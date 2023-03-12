# Original interface

using Z3

ctx = Context()
z1 = bool_const(ctx, "z1")
z2 = bool_const(ctx, "z2")

s = Solver(ctx)
add(s, or(z1, z2))
add(s, or(not(z1), z2))
add(s, or(not(z1), not(z2)))

res = check(s)
println(res)
# can also check res == Z3.sat

m = get_model(s)
# can only get strings "true" and "false" back from C++ API, not Bool
for (k, v) in consts(m)
    println("$k = $v")
end

# Result is
#= 
CheckResult(0x00000001)
z1 = false
z2 = true
=#







# New interface
include("utility.jl")

z1 = Var(:Bool, "z1")
z2 = Var(:Bool, "z2")

predicates = [z1 ∨ z2, ~z1 ∨ z2, ~z1 ∨ ~z2]
prob = Problem(predicates)
solve!(prob)

println(prob.status)
println("z1 = $(z1.value)")
println("z2 = $(z2.value)")
# Result is
#=
SAT
z1 = Bool[0]
z2 = Bool[1]
=#

# Notes from meeting
# C functions are easy to wrap in Julia
# Look at how the C++ wrapping is done
# If there are functions that are missing we can add them
# TO DO: Add the missing functions

# Thoughts on JuliaZ3.jl
#=
Convex.jl takes a parse tree and puts it to a solver
If you have to go through the convex tree construction then
You write a language which is compatible with Convex.jl where if the problem is convex then it calls Convex.jl
and if the problem is not convex it calls Convex.jl to create the convex expr tree and appends the tree to the nonconvex part
and feeds the whole thing to z3
If it's completely convex 

# TO DO Talk to Kochenderfer about who is really good at Julia and can help advise
# "This could turn into something that is both a nice paper and something people actually use, which is very rare" ~Lall
=#



# Desired interface
# x <= 1 ∨ y <= 1
# convex.jl
# x <= 1, y <= 1

#=
x = Variable(2, :Real)
z = Variable(1, :Bool, "z")

expr1 = ~z
# Satisfying one OR the other constraint
expr2 = (x >= 1.0) ∨ (x <= -1.0)
expr3 = ~expr1 # this would just be z

problem = SmcProblem([expr1, expr2 ∧ expr3])

# this is the part I'm still working on
solve!(problem)

# get the solution
println("x = $(x.value)")
println("z = $(z.value)")
=#