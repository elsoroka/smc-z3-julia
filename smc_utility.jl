
import Convex.Constraint as CvxExpr
import Convex.Variable as CvxVar

include("z3_utility.jl")

# Base type of variable
VarType = Union{BoolExpr, CvxVar}

# Use these to initialize a variable
function Var(n::Int, t::Symbol, name="")
	if t == :Real
		return CvxVar(n)
	elseif t == :Bool
		if length(name) == 0
			error("Must provide a name to initialize a Bool var")
		end
		return BoolExpr(n, name)
	else
		error("Unrecognized variable type $t")
	end
end
function Var(m::Int, n::Int, t::Symbol, name="")
	if t == :Real
		return CvxVar(m,n)
	elseif t == :Bool
		if length(name) == 0
			error("Must provide a name to initialize a Bool var")
		end
		return BoolExpr(m,n, name)
	else
		error("Unrecognized variable type $t")
	end
end
Var(t::Symbol, name="") = Var(1, t, name)


# SELF TEST
#=
x = Var(2, :Real)
z1 = Var(2, :Bool, "z1")
z2 = Var(2,3, :Bool, "z2")

expr = (z1∧z2)⟹z1
println(expr)
initialize!(expr)

prob = Problem(expr)
solve!(prob)
println(z1.value)
println(z2.value)
=#