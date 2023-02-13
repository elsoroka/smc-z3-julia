
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
	constraints::Expr
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
function _assign!(constraints::Union{Expr, Array{Expr}}, name="a")
	counter = 0
	_constraint_predicates = _Z3Expr[]
	mapping = Dict{String, Tuple{_Z3Expr, Bool}}()
	# TODO define iteration correctly
	if (typeof(constraints) == Conjunction) || (typeof(constraints) == Disjunction)
		constraint_list = constraints.exprs
	else
		constraint_list = [constraints,]
	end
	for c in constraint_list
		if typeof(c) == Disjunction
			p, m = _assign!(c.exprs, "$name$counter")
			push!(_constraint_predicates, Z3.Or(p))
			for k in keys(m)
				mapping[k] = m[k]
			end
			counter += 1

		elseif typeof(c) == Conjunction
			p, m = _assign!(c.exprs, "$name$counter")
			push!(_constraint_predicates, Z3.And(p))
			for k in keys(m)
				mapping[k] = m[k]
			end
			counter += 1

		elseif typeof(c) == ConvexExpr
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

constraints = [x >= 0.0, y >= -1.0, x <= 5.0 ∨ y <= 5.0, z ∨ x >= 10.0]
predicates = [~z,]
prob = Problem(constraints, predicates)
abstract!(prob)
