
import Convex.Constraint as CvxExpr
import Convex.Variable as CvxVar

include("z3_utility.jl") # TODO fix this import so we only import the useful parts

# Base type of variable and expr (constraint)
VarType  = Union{BoolExpr, CvxVar}
ExprType = Union{BoolExpr, CvxExpr}

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


### SOLVING AND REPRESENTING THE SOLUTION

#=
struct Solution
contains members:
	status: SAT, UNSAT, IN_PROGRESS, FAILED
	bool_vars: dict mapping Boolean var names to true/false if SAT
	real_vars: dict mapping real var names to real values if SAT
=#
struct Solution
	status::SmcStatus
	bool_vars::Dict{String, Bool}
	real_vars::Dict{String, AbstractFloat}
end

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