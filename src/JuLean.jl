# JuLean.jl - Formal Verification & Contract-Driven Synthesis Bridge for Julia & Lean 4

module JuLean

using MacroTools
using z3_jll

# Include core subsystems
include("types.jl")
include("contracts.jl")
include("lean_bridge.jl")

# Lean 4 AST & transpiler
include("transpiler/types.jl")
include("transpiler/julia_to_lean.jl")
include("transpiler/printer.jl")

# SMT / Z3 backend
include("smt/smt_printer.jl")
include("smt/z3_bridge.jl")
include("smt/bmc.jl")

# Lean 4 & certified artifact export
include("export.jl")

# Global specification registry for formalized functions
"""
    SPEC_REGISTRY

Global registry mapping function names (`Symbol`) to their extracted `FormalSpecification`.
Every function annotated with `@formalize` registers its specification here,
making it available to `verify`, `export_lean_file`, and `verification_summary`.
"""
const SPEC_REGISTRY = Dict{Symbol, FormalSpecification}()

"""
    simplify_expr(expr) -> Expr

Simplifies an algebraic expression. When `Metatheory.jl` is loaded,
the `JuLeanMetatheoryExt` extension performs equality saturation and term rewriting.
"""
function simplify_expr(expr)
    return expr
end

"""
    INLINE_REGISTRY

Global registry mapping function identifiers (`Symbol` or `Expr`) to inlining templates
`(args::Vector{Symbol}, body::Expr)`. Functions registered here are transparently
inlined by JuLean's SMT and Lean 4 engines whenever called within `@formalize` specifications.
"""
const INLINE_REGISTRY = Dict{Any, Tuple{Vector{Symbol}, Any}}()

"""
    register_inline!(fn_name, args::Vector{Symbol}, body)
    register_inline!(fn_name, fdef::Expr)

Registers a function or method AST to be automatically inlined inside formal specifications.
"""
function register_inline!(fn_name, args::Vector{Symbol}, body)
    clean_b = body
    if clean_b isa Expr && clean_b.head == :block
        stmts = filter(a -> !(a isa LineNumberNode), clean_b.args)
        clean_b = length(stmts) == 1 ? stmts[1] : clean_b
    end
    if clean_b isa Expr && clean_b.head == :return && length(clean_b.args) == 1
        clean_b = clean_b.args[1]
    end
    INLINE_REGISTRY[fn_name] = (args, clean_b)
end

function register_inline!(fn_name, fdef::Expr)
    dict = MacroTools.splitdef(fdef)
    args = Symbol[a isa Symbol ? a : (a isa Expr && a.head == :(::) ? a.args[1] : Symbol(string(a))) for a in dict[:args]]
    register_inline!(fn_name, args, dict[:body])
end

"""
    auto_extract_method_ast(func::Function, nargs::Int) -> Union{Tuple{Vector{Symbol}, Expr}, Nothing}

Inspects `func` methods with arity `nargs`, uses `InteractiveUtils.functionloc` to locate
the source file and line, parses the function AST from the original source file, and returns
`(param_names, clean_body_expr)`.
"""
function auto_extract_method_ast(func::Function, nargs::Int)
    ms = collect(methods(func))
    matching = filter(m -> m.nargs == nargs + 1 && nameof(m.module) ∉ (:Base, :Core), ms)
    isempty(matching) && return nothing
    m = first(matching)

    file, line = Base.functionloc(m)
    if file === nothing || !isa(file, AbstractString) || !isfile(file)
        return nothing
    end

    lines = readlines(file)
    chunk = join(lines[line:min(line + 100, length(lines))], "\n")
    fdef, _ = Meta.parse(chunk, 1)

    while fdef isa Expr && fdef.head == :macrocall
        clean_args = filter(a -> !(a isa LineNumberNode), fdef.args[2:end])
        fdef = clean_args[end]
    end

    if fdef isa Expr && fdef.head in (:function, :(=))
        dict = MacroTools.splitdef(fdef)
        args = Symbol[a isa Symbol ? a : (a isa Expr && a.head == :(::) ? a.args[1] : Symbol(string(a))) for a in dict[:args]]
        body = dict[:body]
        clean_b = body
        if clean_b isa Expr && clean_b.head == :block
            stmts = filter(a -> !(a isa LineNumberNode), clean_b.args)
            clean_b = length(stmts) == 1 ? stmts[1] : clean_b
        end
        if clean_b isa Expr && clean_b.head == :return && length(clean_b.args) == 1
            clean_b = clean_b.args[1]
        end
        return (args, clean_b)
    end
    return nothing
end

"""
    expand_inlines(ex) -> Expr

Recursively expands calls to functions registered in `INLINE_REGISTRY` (or dynamically
inspected from enclosing Julia packages) by substituting actual arguments into the
registered parameter template.
"""
function expand_inlines(ex)
    !(ex isa Expr) && return ex

    if ex.head == :call && length(ex.args) >= 1
        fn = ex.args[1]
        call_args = [expand_inlines(a) for a in ex.args[2:end]]

        # Match symbol, Expr(:., ...), or function name
        match_key = nothing
        if haskey(INLINE_REGISTRY, fn)
            match_key = fn
        elseif fn isa Expr && fn.head == :. && length(fn.args) == 2
            sym = fn.args[2] isa QuoteNode ? fn.args[2].value : fn.args[2]
            if haskey(INLINE_REGISTRY, fn)
                match_key = fn
            elseif haskey(INLINE_REGISTRY, sym)
                match_key = sym
            end
        end

        # If not yet registered, attempt automatic reflection and source extraction
        if match_key === nothing
            func_obj = nothing
            # Only inspect qualified calls Module.func (e.g. Sirocco.reduced_cost)
            if fn isa Expr && fn.head == :. && length(fn.args) == 2
                mod_sym = fn.args[1]
                func_sym = fn.args[2] isa QuoteNode ? fn.args[2].value : fn.args[2]
                if mod_sym ∉ (:Base, :Core)
                    for (pkg, m) in Base.loaded_modules
                        if nameof(m) == mod_sym && isdefined(m, func_sym)
                            val = getfield(m, func_sym)
                            if val isa Function
                                func_obj = val
                                break
                            end
                        end
                    end
                end
            end

            if func_obj !== nothing
                extracted = auto_extract_method_ast(func_obj, length(call_args))
                if extracted !== nothing
                    tmpl_args, tmpl_body = extracted
                    INLINE_REGISTRY[fn] = (tmpl_args, tmpl_body)
                    match_key = fn
                end
            end
        end

        if match_key !== nothing
            tmpl_args, tmpl_body = INLINE_REGISTRY[match_key]
            if length(tmpl_args) == length(call_args)
                substs = Dict{Symbol, Any}(zip(tmpl_args, call_args))
                replace_syms(e) = e isa Symbol ? get(substs, e, e) : (e isa Expr ? Expr(e.head, map(replace_syms, e.args)...) : e)
                return expand_inlines(replace_syms(tmpl_body))
            end
        end

        return Expr(:call, fn, call_args...)
    else
        return Expr(ex.head, [expand_inlines(a) for a in ex.args]...)
    end
end

"""
    @inline_formal function foo(args...) ... end

Defines a Julia function and registers its AST with `JuLean` so that any call
to `foo(...)` inside a `@formalize` kernel is automatically inlined during SMT and Lean 4
transpilation.
"""
macro inline_formal(fdef)
    dict = MacroTools.splitdef(fdef)
    fn_name = dict[:name]
    args = Symbol[a isa Symbol ? a : (a isa Expr && a.head == :(::) ? a.args[1] : Symbol(string(a))) for a in dict[:args]]
    clean_b = dict[:body]
    if clean_b isa Expr && clean_b.head == :block
        stmts = filter(a -> !(a isa LineNumberNode), clean_b.args)
        clean_b = length(stmts) == 1 ? stmts[1] : clean_b
    end
    if clean_b isa Expr && clean_b.head == :return && length(clean_b.args) == 1
        clean_b = clean_b.args[1]
    end

    return quote
        $(esc(fdef))
        $(@__MODULE__).register_inline!($(QuoteNode(fn_name)), $(QuoteNode(args)), $(QuoteNode(clean_b)))
        $(esc(fn_name))
    end
end

"""
    get_method_docstring(m::Method) -> String

Retrieves the raw docstring associated with method `m` by querying Julia's doc metadata
or reading the source comments immediately preceding the method definition.
"""
function get_method_docstring(m::Method)::String
    mod = m.module
    b = Base.Docs.Binding(mod, m.name)
    meta = Base.Docs.meta(mod)
    if haskey(meta, b)
        md = meta[b]
        if md isa Base.Docs.MultiDoc
            for (sig, docstr) in md.docs
                if sig == m.sig || (m.sig <: sig)
                    return join(docstr.text, "\n")
                end
            end
            return join([join(d.text, "\n") for d in values(md.docs)], "\n")
        elseif haskey(md, :text)
            return join(md.text, "\n")
        end
    end

    file, line = Base.functionloc(m)
    if file !== nothing && isfile(file)
        lines = readlines(file)
        doc_lines = String[]
        idx = line - 1
        in_doc = false
        while idx >= 1
            l = lines[idx]
            if occursin("\"\"\"", l)
                if in_doc
                    pushfirst!(doc_lines, l)
                    break
                else
                    in_doc = true
                    pushfirst!(doc_lines, l)
                end
            elseif in_doc
                pushfirst!(doc_lines, l)
            elseif !isempty(strip(l)) && !startswith(strip(l), "#")
                break
            end
            idx -= 1
        end
        if !isempty(doc_lines)
            return join(doc_lines, "\n")
        end
    end
    return ""
end

"""
    parse_doc_contracts(doc::AbstractString) -> Tuple{Vector{Expr}, Vector{Expr}, Vector{Expr}}

Extracts formal contracts from a Markdown docstring:
- Lines matching `@requires <expr>`
- Lines matching `@ensures <expr>`
- Lines matching `@invariant <expr>`
"""
function parse_doc_contracts(doc::AbstractString)
    pre = Expr[]
    post = Expr[]
    inv = Expr[]
    for line in split(doc, "\n")
        m_req = match(r"^\s*[-*]?\s*`?@requires\s+(.*?)(?:`|\s*$)", line)
        if m_req !== nothing
            push!(pre, Meta.parse(m_req.captures[1]))
        end
        m_ens = match(r"^\s*[-*]?\s*`?@ensures\s+(.*?)(?:`|\s*$)", line)
        if m_ens !== nothing
            push!(post, Meta.parse(m_ens.captures[1]))
        end
        m_inv = match(r"^\s*[-*]?\s*`?@invariant\s+(.*?)(?:`|\s*$)", line)
        if m_inv !== nothing
            push!(inv, Meta.parse(m_inv.captures[1]))
        end
    end
    return pre, post, inv
end

"""
    extract_formal_spec(func::Function, argtypes::Tuple=()) -> FormalSpecification

Extracts a formal specification directly from a Julia function:
- Body is parsed from source code using `Base.functionloc`.
- Contracts (@requires, @ensures) are extracted from the function's docstring.
"""
function extract_formal_spec(func::Function, argtypes::Tuple=())::FormalSpecification
    ms = collect(methods(func))
    matching = isempty(argtypes) ? filter(m -> nameof(m.module) ∉ (:Base, :Core), ms) : [which(func, argtypes)]
    if isempty(matching)
        error("No user methods found for function `$func`")
    end
    m = first(matching)

    file, line = Base.functionloc(m)
    if file === nothing || !isa(file, AbstractString) || !isfile(file)
        error("Source file not found for method $m")
    end

    lines = readlines(file)
    chunk = join(lines[line:min(line + 100, length(lines))], "\n")
    fdef, _ = Meta.parse(chunk, 1)

    while fdef isa Expr && fdef.head == :macrocall
        clean_args = filter(a -> !(a isa LineNumberNode), fdef.args[2:end])
        fdef = clean_args[end]
    end

    if !(fdef isa Expr && fdef.head in (:function, :(=)))
        error("Could not parse method definition for $m")
    end

    dict = MacroTools.splitdef(fdef)
    fn_name = dict[:name]
    args = Symbol[]
    arg_types = Dict{Symbol, Any}()

    for a in dict[:args]
        if a isa Symbol
            push!(args, a)
            arg_types[a] = Real
        elseif a isa Expr && a.head == :(::)
            sym = a.args[1]
            typ = a.args[2]
            push!(args, sym)
            arg_types[sym] = typ
        else
            push!(args, Symbol(string(a)))
            arg_types[Symbol(string(a))] = Real
        end
    end

    ret_type = get(dict, :rtype, Real)
    if ret_type === nothing
        ret_type = Real
    end

    # Extract contracts from docstring
    doc = get_method_docstring(m)
    pre, post, inv = parse_doc_contracts(doc)

    clean_body = dict[:body]
    if clean_body isa Expr && clean_body.head == :block
        stmts = filter(a -> !(a isa LineNumberNode), clean_body.args)
        clean_body = length(stmts) == 1 ? stmts[1] : clean_body
    end
    if clean_body isa Expr && clean_body.head == :return && length(clean_body.args) == 1
        clean_body = clean_body.args[1]
    end

    clean_body = expand_inlines(clean_body)
    pre = [expand_inlines(p) for p in pre]
    post = [expand_inlines(p) for p in post]
    inv = [expand_inlines(p) for p in inv]

    return FormalSpecification(
        fn_name,
        args,
        arg_types,
        ret_type,
        pre,
        post,
        inv,
        clean_body,
        fdef,
        doc
    )
end

"""
    extract_formal_spec(fdef::Expr) -> FormalSpecification

Analyzes a Julia function definition expression, parses arguments, type annotations,
return type, docstring, and extracts all `@requires` and `@ensures` contracts.
"""
function extract_formal_spec(fdef::Expr)::FormalSpecification
    dict = MacroTools.splitdef(fdef)
    fn_name = dict[:name]
    args = Symbol[]
    arg_types = Dict{Symbol, Any}()

    for a in dict[:args]
        if a isa Symbol
            push!(args, a)
            arg_types[a] = Real
        elseif a isa Expr && a.head == :(::)
            sym = a.args[1]
            typ = a.args[2]
            push!(args, sym)
            arg_types[sym] = typ
        else
            push!(args, Symbol(string(a)))
            arg_types[Symbol(string(a))] = Real
        end
    end

    ret_type = get(dict, :rtype, Real)
    if ret_type === nothing
        ret_type = Real
    end

    pre, post, inv, clean_body = extract_contracts(dict[:body])

    # Transparently expand registered inline functions in formal contracts and body
    clean_body = expand_inlines(clean_body)
    pre = [expand_inlines(p) for p in pre]
    post = [expand_inlines(p) for p in post]
    inv = [expand_inlines(p) for p in inv]

    return FormalSpecification(
        fn_name,
        args,
        arg_types,
        ret_type,
        pre,
        post,
        inv,
        clean_body,
        fdef,
        ""
    )
end

"""
    verify(spec::FormalSpecification; backend=:Z3, timeout=30.0, tactic="") -> VerificationResult

Verifies a `FormalSpecification` using the designated backend:
- `:Z3`: Rapid automated falsification and counterexample check via Z3 SMT solver.
- `:Lean4`: Mechanized proof verification using Lean 4 and Mathlib.
"""
function verify(spec::FormalSpecification; backend::Symbol=:Z3, timeout::Float64=30.0, tactic::String="", logic::String="", depth::Int=3)::VerificationResult
    if backend == :Z3
        return verify_with_z3(spec; logic=logic, timeout=timeout)
    elseif backend == :BMC
        return verify_bmc(spec; depth=depth, logic=(isempty(logic) ? "ALL" : logic), timeout=timeout)
    elseif backend == :Lean4
        lean_def, lean_thm = transpile_to_lean_decl(spec; tactic=tactic)
        struct_decls = [to_lean(s) for s in values(STRUCT_REGISTRY)]
        struct_header = isempty(struct_decls) ? "" : join(struct_decls, "\n\n") * "\n\n"
        code = struct_header * to_lean(lean_def) * "\n\n" * to_lean(lean_thm)
        run_res = run_lean(code; timeout=timeout)
        # Soundness: a proof that relies on `sorry` is NOT verified.
        # Lean reports `sorry` as a warning, so exit code 0 alone is not sufficient.
        uses_sorry = any(w -> occursin("sorry", lowercase(w)), run_res.warnings)
        status = (run_res.success && !uses_sorry) ? StatusVerified : StatusError
        if !run_res.success
            msg = isempty(run_res.errors) ? "Lean 4 exited with code $(run_res.exit_code)" : join(run_res.errors, "\n")
        elseif uses_sorry
            msg = "Proof relies on `sorry`; the theorem is not fully verified"
        else
            msg = "Verified by Lean 4"
        end
        return VerificationResult(
            spec.name,
            status,
            :Lean4;
            message=msg,
            lean_code=code,
            elapsed_time=run_res.elapsed_time
        )
    else
        error("Unsupported verification backend: $backend (choose :Z3 or :Lean4)")
    end
end

"""
    verify(func::Function, argtypes::Tuple=(); kwargs...) -> VerificationResult

Verifies a Julia function directly by extracting its implementation and docstring contracts.
"""
function verify(func::Function, argtypes::Tuple=(); kwargs...)
    spec = extract_formal_spec(func, argtypes)
    return verify(spec; kwargs...)
end

"""
    verify(fn_name::Symbol; backend=:Z3, kwargs...) -> VerificationResult

Verifies a registered function previously annotated with `@formalize`.
"""
function verify(fn_name::Symbol; kwargs...)
    if !haskey(SPEC_REGISTRY, fn_name)
        error("No formal specification found for `$fn_name`. Ensure it is annotated with `@formalize`.")
    end
    return verify(SPEC_REGISTRY[fn_name]; kwargs...)
end

"""
    @formalize function ... end
    @formalize struct ... end
    @formalize Module.func

Annotates a Julia function or struct definition with formal contracts:
- For `struct`: extracts the `LeanStructure`, registers it in `STRUCT_REGISTRY` & `CUSTOM_TYPE_REGISTRY`.
- For `function`: extracts `FormalSpecification`, instruments runtime contracts, and enables formal verification.
- For function reference (`Module.func` or `func`): automatically extracts contracts from the function's Markdown docstrings!
"""
macro formalize(def_expr)
    if def_expr isa Expr && def_expr.head == :struct
        lean_struct = extract_struct_decl(def_expr)
        sname = Symbol(lean_struct.name)
        return quote
            $(esc(def_expr))
            $(@__MODULE__).STRUCT_REGISTRY[$(QuoteNode(sname))] = $(esc(QuoteNode(lean_struct)))
            $(esc(QuoteNode(sname)))
        end
    end

    if def_expr isa Symbol || (def_expr isa Expr && def_expr.head == :. && length(def_expr.args) == 2)
        # Function reference passed! E.g. @formalize Sirocco.reduced_cost
        return quote
            func_val = $(esc(def_expr))
            spec = $(@__MODULE__).extract_formal_spec(func_val)
            $(@__MODULE__).SPEC_REGISTRY[spec.name] = spec
            $(@__MODULE__).register_inline!(spec.name, spec.args, spec.body)
            $(@__MODULE__).register_inline!(func_val, spec.args, spec.body)
            spec.name
        end
    end

    spec = extract_formal_spec(def_expr)
    dict = MacroTools.splitdef(def_expr)
    fn_name = dict[:name]
    pre, post, inv, clean_body = extract_contracts(dict[:body])

    dict[:body] = instrument_contract_body(fn_name, pre, post, clean_body)
    exec_expr = MacroTools.combinedef(dict)

    spec_quote = QuoteNode(spec)

    return quote
        $(esc(exec_expr))
        $(@__MODULE__).SPEC_REGISTRY[$(QuoteNode(fn_name))] = $(esc(spec_quote))
        $(@__MODULE__).register_inline!($(QuoteNode(fn_name)), $(QuoteNode(spec.args)), $(QuoteNode(spec.body)))
        $(esc(fn_name))
    end
end

# Exports
export
    # Contracts & DbC
    @contract,
    @formalize,
    @inline_formal,
    register_inline!,
    expand_inlines,
    @requires,
    @ensures,
    @invariant,
    @forall,
    @exists,
    implies,
    ⟹,
    -->,
    enable_contracts!,
    disable_contracts!,
    ContractViolationError,

    # Specifications & Verification
    FormalSpecification,
    VerificationStatus,
    StatusVerified,
    StatusCounterexample,
    StatusUnverified,
    StatusError,
    StatusSyntaxChecked,
    VerificationResult,
    is_verified,
    verify,
    SPEC_REGISTRY,

    # Lean 4 Transpiler & Bridge
    LeanType,
    LeanNat,
    LeanInt,
    LeanRat,
    LeanFloat,
    LeanBool,
    LeanString,
    LeanProp,
    LeanArray,
    LeanList,
    LeanFinset,
    LeanNamedType,
    LeanExpr,
    LeanVar,
    LeanLitInt,
    LeanLitRat,
    LeanLitFloat,
    LeanLitBool,
    LeanLitString,
    LeanApp,
    LeanBinOp,
    LeanUnaryOp,
    LeanIf,
    LeanLet,
    LeanFieldAccess,
    LeanIndexAccess,
    LeanDecl,
    LeanDef,
    LeanTheorem,
    LeanStructure,
    LeanInductive,
    to_lean,
    transpile_to_lean_decl,
    synthesize_tactic,
    julia_to_lean_type,
    julia_to_lean_expr,
    register_lean_type!,
    CUSTOM_TYPE_REGISTRY,
    STRUCT_REGISTRY,
    extract_struct_decl,
    set_lean_project_dir!,
    find_lean_project_dir,
    run_lean,
    LeanRunResult,
    LeanConfig,

    # SMT & Z3 Backend
    generate_smtlib_query,
    verify_with_z3,
    verify_bmc,
    LoopDescriptor,
    extract_loop_descriptor,
    run_z3,

    # Export & Artifacts
    export_lean_file,
    verification_summary,
    simplify_expr

end # module JuLean
