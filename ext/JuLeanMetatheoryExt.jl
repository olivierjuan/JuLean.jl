# JuLean.jl - Metatheory Package Extension for E-Graph Simplification

module JuLeanMetatheoryExt

using JuLean
using Metatheory
using Metatheory.EGraphs

"""
Algebraic simplification theory using Metatheory.jl equality saturation.
"""
const ALGEBRAIC_THEORY = @theory a b c begin
    a + 0 --> a
    0 + a --> a
    a * 1 --> a
    1 * a --> a
    a * 0 --> 0
    0 * a --> 0
    a - a --> 0
    a + b == b + a
    a * b == b * a
    (a + b) + c == a + (b + c)
    (a * b) * c == a * (b * c)
    a * (b + c) == (a * b) + (a * c)
end

"""
    JuLean.simplify_expr(expr::Expr)

Applies equality saturation over `ALGEBRAIC_THEORY` using E-graphs to simplify expressions.
"""
function JuLean.simplify_expr(expr::Expr)
    try
        g = EGraph(expr)
        saturate!(g, ALGEBRAIC_THEORY)
        return extract!(g, astsize)
    catch
        return expr
    end
end

end # module JuLeanMetatheoryExt
