import Convex
using LinearAlgebra, Plots
include("z3_utility.jl")
include("smc.jl")

# a problem where x has to be in a circle of radius √2 but outside a square of length 1
x = Variable(2, :Real)
constraints = NodeType[
    Convex.sumsquares(x) <= 2.0,
    (x[1] >= 1.0) ∨ (x[1] <= -1.0),
    (x[2] >= 1.0) ∨ (x[2] <= -1.0),
]
problem = SmcProblem(constraints)
solve!(problem)

plot([-1,1,1,-1,-1], [-1,-1,1,1,-1], color=:red, aspect_ratio=:equal, legend=:topleft)
plot!(cos.(π.*(0:0.1:2)).*√2, sin.(π.*(0:0.1:2)).*√2, color=:green)
scatter!([x.value[1],], [x.value[2],], color=:orange, markersize=5)