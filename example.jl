# Unsightly interface
#=
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
=#
#=
CheckResult(0x00000001)
z1 = false
z2 = true

=#

# non unsightly
include("utility.jl")

z1 = Var(:Bool, "z1")
z2 = Var(:Bool, "z2")

predicates = [z1 ∨ z2, ~z1 ∨ z2, ~z1 ∨ ~z2]
prob = Problem(predicates)
solve!(prob)

println(prob.status)
println("z1 = $(z1.value)")
println("z2 = $(z2.value)")

#=
SAT
z1 = Bool[0]
z2 = Bool[1]
=#