# Code layout
# Long-term code goals
# Convex.jl

import Convex.Constraint as _CvxExpr
import Z3
import Z3.ExprAllocated    as _Z3Expr
import Z3.ContextAllocated as _Z3Context
import Z3.SolverAllocated  as _Z3Solver
# https://github.com/ahumenberger/Z3.jl

# What the code should do:
# Define an abstract type for a literal
# Literal has fields "name" and "expr".
# This type should subtype as:
# Boolean
#   where expr is a (z3) Boolean variable, True or False
# Convex
#   Adds a field for a Convex.jl expression
#   expr returns the low-level representation given by Convex.conic_form

# this is horrible but z3 causes it
global _ctx = nothing

abstract type Expr end

struct BoolExpr <: Expr
	expr::Union{_Z3Expr, Nothing}
	name::String
	# constructor
	function BoolExpr(name)
		global ctx
		if ctx == nothing
			ctx = Z3.Context()
		end
		return BoolExpr(Z3.bool_const(ctx,  name), name)
	end
end


struct ConvexExpr <: Expr
	expr_cvx::_CvxExpr
	expr::Any # conic form of expr_cvx
	name::String
end
#constructor
ConvexExpr(expr_cvx, name) = ConvexExpr(expr_cvx, conic_form(expr_cvx), name)


@enum SmcStatus SAT=0 UNSAT=1 IN_PROGRESS=2 SOLVER_NOT_CALLED=3 FAILED=4

#=
We will also define operations
And(...)
Or(...)
which operate on a splatted list of Literals
And and Or return type ConstraintSet
=#

abstract type ConstraintSet end

struct Conjunction <: ConstraintSet
	exprs::Array{Expr}
end

struct Disjunction <: ConstraintSet
	exprs::Array{Expr}
end

# convenience functions
And(constraints::Array{Expr}) = Conjunction(constraints)
Or(constraints::Array{Expr}) = Disjunction(constraints)
function Not(a::Expr)
	if typeof(a) == BoolExpr
		return BoolExpr(z3.Not(a.expr), "!"+a.name)
	elseif typeof(a) == ConvexExpr
		throw("ERROR: Cannot negate a convex expression")
	else
		throw("ERROR: Unrecognized type $(typeof(a))")
	end
end
Implies(a::Expr, b::Expr) = Or([Not(a),b])

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
mutable struct Problem
	constraints::ConstraintSet
	predicates::Array{_Z3Expr}
	_constraint_predicates::Array{_Z3Expr}
	mapping::Dict{String, Tuple{_Z3Expr, Bool}}
	solution::Union{Solution, Nothing}
	status::SmcStatus
	# wow, an inner constructor
	# https://docs.julialang.org/en/v1/manual/constructors/
	function Problem(constraints, predicates)
		
		return Problem(constraints, predicates, _Z3Expr[],
					   Dict{String,Selection}(), nothing, SOLVER_NOT_CALLED)
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
function _assign!(constraints::ConstraintSet, name="a")
	counter = 0
	_constraint_predicates = _Z3Expr[]
	mapping = Dict{String, Selection}()

	for c in constraints
		if typeof(c) == Disjunction
			p, m = _assign!(c.exprs, name+str(counter))
			push!(_constraint_predicates, Z3.Or(p))
			for k in keys(m)
				mapping[k] = m[k]
			end
			counter += 1

		elseif typeof(c) == Conjunction
			p, m = _assign!(c.exprs, name+str(counter))
			push!(_constraint_predicates, Z3.And(p))
			for k in keys(m)
				mapping[k] = m[k]
			end
			counter += 1

		elseif typeof(c) == ConvexExpr
			varname = name+str(counter)
			global ctx
			var = Z3.bool_const(ctx, varname)
			push!(_constraint_predicates, var)
			mapping[varname] = c
			counter += 1

		elseif typeof(c) == BoolExpr
			push!(_constraint_predicates, c)

		else
			raise("Unrecognized type "+typeof(c))
end
function abstract!(problem::Problem)

end

function sat_solve!(problem::Problem)
end

function convex_solve!(problem::Problem)
end

function convex_cert!(problem::Problem)
end