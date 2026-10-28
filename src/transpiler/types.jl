# JuLean.jl - Lean 4 AST Types

"""
Abstract base type for Lean 4 types.
"""
abstract type LeanType end

struct LeanNat <: LeanType end
struct LeanPNat <: LeanType end
struct LeanInt <: LeanType end
struct LeanRat <: LeanType end
struct LeanFloat <: LeanType end
struct LeanBool <: LeanType end
struct LeanString <: LeanType end
struct LeanProp <: LeanType end

struct LeanArray <: LeanType
    elem_type::LeanType
end

struct LeanList <: LeanType
    elem_type::LeanType
end

struct LeanFinset <: LeanType
    elem_type::LeanType
end

struct LeanArrow <: LeanType
    from::LeanType
    to::LeanType
end

struct LeanNamedType <: LeanType
    name::String
    type_args::Vector{LeanType}
end
LeanNamedType(name::String) = LeanNamedType(name, LeanType[])

"""
Abstract base type for Lean 4 expressions.
"""
abstract type LeanExpr end

struct LeanVar <: LeanExpr
    name::String
end

struct LeanLitInt <: LeanExpr
    val::Int
end

struct LeanLitRat <: LeanExpr
    num::BigInt
    den::BigInt
end

struct LeanLitFloat <: LeanExpr
    val::Float64
end

struct LeanLitBool <: LeanExpr
    val::Bool
end

struct LeanLitString <: LeanExpr
    val::String
end

struct LeanApp <: LeanExpr
    fn::LeanExpr
    args::Vector{LeanExpr}
end
LeanApp(fn_name::String, args::Vector{<:LeanExpr}) = LeanApp(LeanVar(fn_name), collect(LeanExpr, args))

struct LeanBinOp <: LeanExpr
    op::Symbol # :+, :-, :*, :/, :==, :!=, :<, :<=, :>, :>=, :∧, :∨, :→, :↔
    left::LeanExpr
    right::LeanExpr
end

struct LeanUnaryOp <: LeanExpr
    op::Symbol # :-, :¬, :!
    arg::LeanExpr
end

struct LeanIf <: LeanExpr
    cond::LeanExpr
    then_expr::LeanExpr
    else_expr::LeanExpr
end

struct LeanLet <: LeanExpr
    var::String
    val::LeanExpr
    body::LeanExpr
end

struct LeanFieldAccess <: LeanExpr
    obj::LeanExpr
    field::String
end

struct LeanIndexAccess <: LeanExpr
    collection::LeanExpr
    index::LeanExpr
end

struct LeanMatchArm
    pattern::String
    body::LeanExpr
end

struct LeanMatch <: LeanExpr
    scrutinee::LeanExpr
    arms::Vector{LeanMatchArm}
end

struct LeanForall <: LeanExpr
    var::String
    type::LeanType
    body::LeanExpr
end

struct LeanExists <: LeanExpr
    var::String
    type::LeanType
    body::LeanExpr
end

struct LeanSum <: LeanExpr
    var::String
    domain::LeanExpr
    body::LeanExpr
end

struct LeanRawExpr <: LeanExpr
    code::String
end

"""
Abstract base type for Lean 4 imperative statements inside a `do` block.
"""
abstract type LeanDoStmt end

struct LeanDoLetMut <: LeanDoStmt
    var::String
    val::LeanExpr
end

struct LeanDoLet <: LeanDoStmt
    var::String
    val::LeanExpr
end

struct LeanDoAssign <: LeanDoStmt
    var::String
    val::LeanExpr
end

struct LeanDoArraySet <: LeanDoStmt
    collection::String
    index::LeanExpr
    val::LeanExpr
end

struct LeanDoForRange <: LeanDoStmt
    var::String
    start_expr::LeanExpr
    stop_expr::LeanExpr
    body::Vector{LeanDoStmt}
end

struct LeanDoForIn <: LeanDoStmt
    var::String
    collection::LeanExpr
    body::Vector{LeanDoStmt}
end

struct LeanDoWhile <: LeanDoStmt
    cond::LeanExpr
    body::Vector{LeanDoStmt}
end

struct LeanDoIf <: LeanDoStmt
    cond::LeanExpr
    then_body::Vector{LeanDoStmt}
    else_body::Vector{LeanDoStmt}
end

struct LeanDoExpr <: LeanDoStmt
    expr::LeanExpr
end

struct LeanDoReturn <: LeanDoStmt
    expr::LeanExpr
end

struct LeanDoBlock <: LeanExpr
    stmts::Vector{LeanDoStmt}
    return_expr::LeanExpr
end

struct LeanIdRun <: LeanExpr
    block::LeanDoBlock
end

struct LeanArrayLit <: LeanExpr
    elements::Vector{LeanExpr}
end

"""
Abstract base type for Lean 4 declarations.
"""
abstract type LeanDecl end

struct LeanDef <: LeanDecl
    name::String
    args::Vector{Tuple{String, LeanType}}
    ret_type::LeanType
    body::LeanExpr
    doc::String
end

struct LeanTheorem <: LeanDecl
    name::String
    params::Vector{Tuple{String, LeanType}}
    hypotheses::Vector{Tuple{String, LeanExpr}}
    statement::LeanExpr
    proof::String # e.g. "by unfold reduced_cost; linarith"
    doc::String
end

struct LeanStructure <: LeanDecl
    name::String
    type_params::Vector{String}
    fields::Vector{Tuple{String, LeanType}}
    doc::String
end

struct LeanInductive <: LeanDecl
    name::String
    type_params::Vector{String}
    constructors::Vector{Tuple{String, Vector{LeanType}}}
    doc::String
end
