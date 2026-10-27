# JuLean.jl - Lean 4 Code Generator & Pretty Printer

"""
    to_lean(t::LeanType) -> String

Renders a `LeanType` into Lean 4 type syntax.
"""
function to_lean(t::LeanType)::String
    if t isa LeanNat
        return "Nat"
    elseif t isa LeanInt
        return "Int"
    elseif t isa LeanRat
        return "ℚ"
    elseif t isa LeanFloat
        return "Float"
    elseif t isa LeanBool
        return "Bool"
    elseif t isa LeanString
        return "String"
    elseif t isa LeanProp
        return "Prop"
    elseif t isa LeanArray
        return "Array ($(to_lean(t.elem_type)))"
    elseif t isa LeanList
        return "List ($(to_lean(t.elem_type)))"
    elseif t isa LeanFinset
        return "Finset ($(to_lean(t.elem_type)))"
    elseif t isa LeanArrow
        return "$(to_lean(t.from)) → $(to_lean(t.to))"
    elseif t isa LeanNamedType
        if isempty(t.type_args)
            return t.name
        else
            args_str = join([to_lean(a) for a in t.type_args], " ")
            return "$(t.name) $args_str"
        end
    else
        return "Any"
    end
end

"""
    to_lean(e::LeanExpr; precedence=0) -> String

Renders a `LeanExpr` into Lean 4 expression syntax with appropriate parenthesization.
"""
function to_lean(e::LeanExpr; precedence::Int=0)::String
    if e isa LeanVar
        return e.name
    elseif e isa LeanLitInt
        return string(e.val)
    elseif e isa LeanLitRat
        if e.den == 1
            return "($(e.num) : ℚ)"
        else
            return "($(e.num) : ℚ) / ($(e.den) : ℚ)"
        end
    elseif e isa LeanLitFloat
        return string(e.val)
    elseif e isa LeanLitBool
        return e.val ? "true" : "false"
    elseif e isa LeanLitString
        return "\"$(escape_string(e.val))\""
    elseif e isa LeanRawExpr
        return e.code
    elseif e isa LeanFieldAccess
        return "$(to_lean(e.obj; precedence=100)).$(e.field)"
    elseif e isa LeanIndexAccess
        return "$(to_lean(e.collection; precedence=100))[$(to_lean(e.index))]!"
    elseif e isa LeanApp
        args_str = join([to_lean(a; precedence=100) for a in e.args], " ")
        res = "$(to_lean(e.fn; precedence=100)) $args_str"
        return precedence > 50 ? "($res)" : res
    elseif e isa LeanUnaryOp
        op_sym = if e.op in (:¬, :!)
            "¬"
        elseif e.op == :-
            "-"
        else
            string(e.op)
        end
        res = "$op_sym$(to_lean(e.arg; precedence=90))"
        return precedence > 80 ? "($res)" : res
    elseif e isa LeanBinOp
        op_str, my_prec = binop_info(e.op)
        left_str = to_lean(e.left; precedence=my_prec)
        right_str = to_lean(e.right; precedence=my_prec + 1)
        res = "$left_str $op_str $right_str"
        return precedence > my_prec ? "($res)" : res
    elseif e isa LeanIf
        res = "if $(to_lean(e.cond)) then $(to_lean(e.then_expr)) else $(to_lean(e.else_expr))"
        return precedence > 10 ? "($res)" : res
    elseif e isa LeanLet
        res = "let $(e.var) := $(to_lean(e.val)); $(to_lean(e.body))"
        return precedence > 5 ? "($res)" : res
    elseif e isa LeanMatch
        lines = String["match $(to_lean(e.scrutinee)) with"]
        for arm in e.arms
            push!(lines, "  | $(arm.pattern) => $(to_lean(arm.body))")
        end
        return join(lines, "\n")
    elseif e isa LeanForall
        res = "∀ ($(e.var) : $(to_lean(e.type))), $(to_lean(e.body))"
        return precedence > 5 ? "($res)" : res
    elseif e isa LeanExists
        res = "∃ ($(e.var) : $(to_lean(e.type))), $(to_lean(e.body))"
        return precedence > 5 ? "($res)" : res
    elseif e isa LeanSum
        res = "∑ $(e.var) ∈ $(to_lean(e.domain)), $(to_lean(e.body))"
        return precedence > 5 ? "($res)" : res
    else
        return string(e)
    end
end

function binop_info(op::Symbol)
    if op in (:(==), :eq)
        return ("=", 50)
    elseif op in (:!=, :≠)
        return ("≠", 50)
    elseif op in (:<, :lt)
        return ("<", 50)
    elseif op in (:<=, :≤, :le)
        return ("≤", 50)
    elseif op in (:>, :gt)
        return (">", 50)
    elseif op in (:>=, :≥, :ge)
        return ("≥", 50)
    elseif op in (:+, :plus)
        return ("+", 60)
    elseif op in (:-, :minus)
        return ("-", 60)
    elseif op in (:*, :mult)
        return ("*", 70)
    elseif op in (:/, :div)
        return ("/", 70)
    elseif op in (:∧, :&&, :and)
        return ("∧", 35)
    elseif op in (:∨, :||, :or)
        return ("∨", 30)
    elseif op in (:→, :-->, :⟹, :implies)
        return ("→", 25)
    elseif op in (:↔, :iff)
        return ("↔", 20)
    else
        return (string(op), 50)
    end
end

"""
    to_lean(decl::LeanDecl) -> String

Renders a `LeanDecl` into Lean 4 declaration syntax.
"""
function to_lean(decl::LeanDecl)::String
    if decl isa LeanDef
        doc_str = isempty(decl.doc) ? "" : "/-- $(decl.doc) -/\n"
        args_str = join(["($(a[1]) : $(to_lean(a[2])))" for a in decl.args], " ")
        header = isempty(args_str) ? "def $(decl.name) : $(to_lean(decl.ret_type)) :=" : "def $(decl.name) $args_str : $(to_lean(decl.ret_type)) :="
        body_str = to_lean(decl.body)
        return "$(doc_str)$(header)\n  $(body_str)"
    elseif decl isa LeanTheorem
        doc_str = isempty(decl.doc) ? "" : "/-- $(decl.doc) -/\n"
        params_str = join(["($(p[1]) : $(to_lean(p[2])))" for p in decl.params], " ")
        hyps_str = join(["($(h[1]) : $(to_lean(h[2])))" for h in decl.hypotheses], " ")
        all_binders = filter(!isempty, [params_str, hyps_str])
        binders_str = isempty(all_binders) ? "" : " " * join(all_binders, " ")
        stmt_str = to_lean(decl.statement)
        proof_str = isempty(decl.proof) ? "by sorry" : decl.proof
        return "$(doc_str)theorem $(decl.name)$(binders_str) : $(stmt_str) := $(proof_str)"
    elseif decl isa LeanStructure
        doc_str = isempty(decl.doc) ? "" : "/-- $(decl.doc) -/\n"
        tparams = isempty(decl.type_params) ? "" : " " * join(decl.type_params, " ")
        lines = String["$(doc_str)structure $(decl.name)$(tparams) where"]
        for f in decl.fields
            push!(lines, "  $(f[1]) : $(to_lean(f[2]))")
        end
        return join(lines, "\n")
    elseif decl isa LeanInductive
        doc_str = isempty(decl.doc) ? "" : "/-- $(decl.doc) -/\n"
        tparams = isempty(decl.type_params) ? "" : " " * join(decl.type_params, " ")
        lines = String["$(doc_str)inductive $(decl.name)$(tparams) where"]
        for c in decl.constructors
            if isempty(c[2])
                push!(lines, "  | $(c[1])")
            else
                types_str = join([to_lean(t) for t in c[2]], " → ")
                push!(lines, "  | $(c[1]) : $(types_str) → $(decl.name)")
            end
        end
        return join(lines, "\n")
    else
        return string(decl)
    end
end
