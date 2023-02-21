# New file since we now have the typing down
import Convex
import Convex.Constraint as CvxConstraint
import Convex.Variable as CvxVar

include("z3_utility.jl") # TODO fix this import so we only import the useful parts

LeafType = Union{CvxConstraint, BoolExpr}

struct SmcExpr
	op       :: Symbol # :And, :Or, :Not (be careful)
	children :: Array{Union{LeafType, SmcExpr}}
	shape    :: Tuple
	
	# returns True if there is a child of type t
	function check_exists(t::Type, children::Array{T}) where T <: Union{LeafType, SmcExpr}
		result = false
		for c in children
			result |= (isa(c, LeafType) ? isa(c, t) : check_exists(t, c.children))
			if result
				break
			end	
		end
		return result
	end
	
	# Default constructor - defining it here prevents there from being a constructor without this correctness check.
	function SmcExpr(op::Symbol, children::Array{T}, shape::Tuple) where T <: Union{LeafType, SmcExpr}
		if op == :Not && length(children) >= 1 && check_exists(CvxConstraint, children)
			error("Cannot construct a negated convex constraint.")
		end
		return new(op, children, shape)
	end
end

NodeType = Union{CvxConstraint, BoolExpr, SmcExpr}


# Define better constructors
SmcExpr(expr::Array{T})             where T <: NodeType = SmcExpr(:Identity, expr, size(expr))
SmcExpr(op::Symbol, expr::Array{T}) where T <: NodeType = SmcExpr(op, expr, size(expr))

~(e ::NodeType)               = SmcExpr(:Not, [e,])
∧(e1::NodeType, e2::NodeType) = SmcExpr(:And, [e1, e2])
∨(e1::NodeType, e2::NodeType) = SmcExpr(:Or, [e1, e2])
⟹(e1::NodeType, e2::NodeType) = (~e1) ∨ e2

# TODO Can we define advanced STL operations (always, eventually, etc)


# SMC ALGORITHM IMPLEMENTATION

# Problem struct
mutable struct SmcProblem
	constraints :: Array{SmcExpr}
	abstract_constraints :: Array{BoolExpr}
	status::Symbol # :OPTIMAL, :UNSAT, :UNKNOWN
end

SmcProblem(constraints::Array{SmcExpr}) = SmcProblem(constraints, Array{BoolExpr}[], :UNSAT)

# abstract! constructs a matching expr tree in abstract_constraints where all cvx constraints
# are replaced by BoolExprs
# recursion by multiple dispatch!
# base cases
_assign(expr::BoolExpr, name="a") = expr
_assign(expr::CvxConstraint, name="a") = BoolExpr(1, name)
# recursive case
function _assign(expr::SmcExpr, name="a")
	if expr.op == :Identity
		return _assign(expr.children[1])
		
	elseif expr.op == :Not
		return _assign(expr.children[1])

	elseif expr.op == :And
		return and(map( (c::Tuple{Int, NodeType}) -> _assign(c[2], "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	elseif expr.op == :Or
		return or(map(  (c::Tuple{Int, NodeType}) -> _assign(c[2], "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	else
		error("Unrecognized operation $(expr.op)")
	end
end
function abstraction!(prob::SmcProblem)
	prob.abstract_constraints = map(_assign, prob.constraints)
end

#=
function solve!(prob::SmcProblem, δ=1e-3)
	abstraction!(prob)
	# this is a call to JuliaZ3
	solve!(Problem(prob.abstract_constraints))
	# c_construct generates a convex problem
	c_prob = c_construct(prob, δ)
	# this is a call to Convex.jl # TODO eventually we will cache conic_form! and use that instead
	solve!(c_prob)
	# generate IIS certificate
	cc = iis(prob, c_prob, δ)
	prob.abstract_constraints += cc
end
=#

# SELF TEST
x = CvxVar(1)

expr1 = SmcExpr(:Not, [BoolExpr(1, "z1")], (1,))
expr2 = (x >= 1.0) ∨ (x <= 10.0)
expr3 = ~expr1
println(expr2)

problem = SmcProblem([expr1, expr2 ∧ expr3])
abstraction!(problem)
println(problem.abstract_constraints)