include("smc.jl")
push!(LOAD_PATH, "../../../../research/BooleanSatisfiability.jl/src/")
import BooleanSatisfiability as SAT
println("self test")
import Convex

x = Convex.Variable(2) 
y = Convex.Variable(2)

z1 = SAT.Bool("z1")
z2 = SAT.Bool("z2")
constraints1 = NodeType[x>=0.0, x<= 2.0, z1, z2]
constraints2 = NodeType[y>=1.0, y[0]<=2.0, y[1]<=3.0]

problem = SmcProblem([or(constraints1), or(constraints2)])

smc_solve!(problem)
println("z1 = $(SAT.value(z1)), z2=$(SAT.value(z2))")
println("x = $(x.value), y = $(y.value)")