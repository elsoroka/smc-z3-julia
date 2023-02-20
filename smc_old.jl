
import Convex.Constraint as CvxConstraint
import Convex.Variable as CvxVar

include("z3_utility.jl") # TODO fix this import so we only import the useful parts

# trying to fix this so z3 and cvx can interoperate
mutable struct CvxExpr <: AbstractExpr
	constraint :: CvxConstraint
	shape      :: Tuple
	op         :: Symbol
	name       :: String
	z3_expr  :: Array{_Z3Expr}
	# iff context is unitialized, z3_expr is empty
	context  :: Union{Nothing, _Z3Context}
	value    :: Union{Nothing, Bool, Array{Bool}} # z3 expr value
end
CvxExpr(constraint::CvxConstraint) = CvxExpr(constraint, constraint.size, :Identity, "cvx", Array{_Z3Expr}[], nothing, nothing)

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



#=
We will also define operations
And(...)
Or(...)
which operate on a splatted list of Literals
And and Or return type ConstraintSet
=#
#=
struct Conjunction <: Expr
	exprs::Array{Expr}
end

struct Disjunction <: Expr
	exprs::Array{Expr}
end

# convenience functions
# TODO there is a better way to do this typing
And(constraints::Union{Array{Expr}, Array{Disjunction},Array{ConvexExpr}}) = Conjunction(constraints)
Or(constraints::Union{Array{Expr}, Array{Disjunction},Array{ConvexExpr}}) = Disjunction(constraints)
Not(a::BoolExpr) = BoolExpr(Z3.Not(a.expr), "!"+a.name)
Implies(a::Expr, b::Expr) = Or([Negate(a),b])
=#
### SOLVING AND REPRESENTING THE SOLUTION

#=
struct Solution
contains members:
	status: SAT, UNSAT, IN_PROGRESS, FAILED
	bool_vars: Boolean variables where z.value is set if SAT
	real_vars: cvx variables where x.value is set if SAT
=#
struct Solution
	status::Symbol # SAT, UNSAT, UNKNOWN, IN_PROGRESS
	bool_vars::Array{BoolExpr}
	real_vars::Array{CvxVar}
end

#=
dict Mapping has keys name:str, values selection:Selection
What do we do here
First we make the abstraction -> ADD [variable] = (convex_constraint, none)
Then we solve it -> ADD [variable] = (convex, assignment)
or variable -> assignment and list the vars with assignment = True
Then we pick out the convex constraints: READ [variable] -> (convex, assignment)

Problem has members:
	constraints: And(...) and Or(...) combinations of literals
	predicates: formulae over Boolean variables only (z3)
	_constraint_predicates: abstract constraints,initialize as [] and fill by abstract!
	_mapping: Mapping
	solution: Solution object or none if not solved
	status: SAT, UNSAT, IN_PROGRESS, FAILED
=#
mutable struct SmcProblem
	constraints::Array{AbstractExpr}
	predicates::Array{BoolExpr}
	_constraint_predicates::Array{BoolExpr}
	mapping::Dict{String, Tuple{BoolExpr, Bool}} # 
	solution::Union{Solution, Nothing}
	status::Symbol
	# wow, an inner constructor
	# https://docs.julialang.org/en/v1/manual/constructors/
	function SmcProblem(constraints, predicates)
		
		return new(constraints, predicates, _Z3Expr[],
					   Dict{String,Tuple{_Z3Expr, Bool}}(), nothing, :UNSAT)
	end
end



# Define a solve() procedure
# solve() has steps
# 1. abstract!(Formula) Generates the abstraction, adds abstracted constraints to _constraint_predicates and adds the Mapping
# 2. sat_solve!(Formula): Solves the predicates, placing the solution in Formula.solution
# 3. convex_solve!(Formula): Solves the constraints enabled in the mapping, placing the solution in 
# 4. convex_cert!(Formula): Generates the IIS and adds it to Formula.predicates
# solve! updates Formula.solution and Formula.status

# helper function for abstract
function _assign!(constraint::AbstractExpr, name="a")
	counter = 0
	_constraint_predicates = _Z3Expr[]
	mapping = Dict{String, Tuple{_Z3Expr, Bool}}()
	# TODO define iteration correctly
	# this is only true if it's a bool constraint, which may contain convex constraints inside
	if constraint.op == :And || constraint.op || :Or
		constraint_list = constraint.children
	else
		constraint_list = [constraint,]
	end
	for c in constraint_list
		if c.op == :Or
			p, m = _assign!(c.exprs, "$name$counter")
			push!(_constraint_predicates, Z3.Or(p))
			for k in keys(m)
				mapping[k] = m[k]
			end
			counter += 1

		elseif c.op == :And
			p, m = _assign!(c.exprs, "$name$counter")
			push!(_constraint_predicates, Z3.And(p))
			for k in keys(m)
				mapping[k] = m[k]
			end
			counter += 1

		elseif typeof(c) == CvxExpr
			varname = "$name$counter"
			global _ctx
			var = Z3.bool_const(_ctx, varname)
			push!(_constraint_predicates, var)
			mapping[varname] = c
			counter += 1

		elseif typeof(c) == BoolExpr
			push!(_constraint_predicates, c.expr)

		else
			throw("Unrecognized type $(typeof(c))")
		end
	end
	return _constraint_predicates, mapping
end

function abstract!(problem::SmcProblem)
	problem._constraint_predicates, problem.mapping = _assign!(problem.constraints)
	# now we have all the z3 predicates associated with items in problem.constraints
	println("Generated\n"+str(problem._constraint_predicates))
end

function sat_solve!(problem::SmcProblem)
	global _ctx
	s = Z3.Solver(_ctx)
	add(s, problem._constraint_predicates)
	add(s, problem.predicates)
	status = check(s)
	println("SAT status: "+str(status))
	return status
end

function convex_solve!(problem::SmcProblem)
	println("Unimplemented")
end

function convex_cert!(problem::SmcProblem)
	println("Unimplemented")
end

function smc_solve!(problem::SmcProblem)
	abstract!(problem)
	status = sat_solve!(problem)

end

# self test
x = Var(2, :Real)
y = Var(2, :Real)
z = Var(1, :Bool, "z")

constraints = [CvxExpr(x >= 0.0), CvxExpr(y >= -1.0),
			   CvxExpr(x <= 5.0) ∨ CvxExpr(y <= 5.0),
			   z ∨ CvxExpr(x >= 10.0)]
predicates = [~z,]
prob = SmcProblem(constraints, predicates)
abstract!(prob)
