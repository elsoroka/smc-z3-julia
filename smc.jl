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

abstract type Expr end

struct BoolExpr <: Expr
	expr::Union{_Z3Expr, Nothing}
	name::String
end
# constructor
BoolExpr(name) = BoolExpr(nothing, name)

struct ConvexExpr <: Expr
	expr_cvx::_CvxExpr
	expr::Any # conic form of expr_cvx
	name::String
end
#constructor
ConvexExpr(expr_cvx, name) = ConvexExpr(expr_cvx, conic_form(expr_cvx), name)


@enum SmcStatus SAT=0 UNSAT=1 IN_PROGRESS=2 FAILED=3

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

### SOLVING AND REPRESENTING THE SOLUTION

# struct Selection has fields constraint:Literal, assignment: True or False
struct Selection
	expr::_Z3Expr
	value::Bool
end

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

Formula has members:
	constraints: And(...) and Or(...) combinations of literals
	predicates: formulae over Boolean variables only (z3)
	_constraint_predicates: abstract constraints,initialize as [] and fill by abstract!
	_mapping: Mapping
	solution: Solution object or none if not solved
	status: SAT, UNSAT, IN_PROGRESS, FAILED
=#
mutable struct Formula
	constraints::ConstraintSet
	predicates::Array{_Z3Expr}
	constraint_predicates::Array{_Z3Expr}
	mapping::Dict{String, Selection}
	solution::Solution
	status::SmcStatus
end


# Define a solve() procedure
# solve() has steps
# 1. abstract!(Formula) Generates the abstraction, adds abstracted constraints to _constraint_predicates and adds the Mapping
# 2. sat_solve!(Formula): Solves the predicates, placing the solution in Formula.solution
# 3. convex_solve!(Formula): Solves the constraints enabled in the mapping, placing the solution in 
# 4. convex_cert!(Formula): Generates the IIS and adds it to Formula.predicates
# solve! updates Formula.solution and Formula.status
