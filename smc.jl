# New file since we now have the typing down
import Convex, SCS
import Convex.Constraint as CvxConstraint
import Convex.Variable as CvxVar
import Base.show, Base.string, Base.~, Base.length, Base.size

include("z3_utility.jl") # TODO fix this import so we only import the useful parts

LeafType = Union{CvxConstraint, BoolExpr}

# SmcExpr is a tree-like structure that can have a mirrored BoolExpr tree
#= EXAMPLE:

          SmcExpr (∧)  -------------- BoolExpr (∧)
          /     \     .-------------- / --- \ -.
    CvxExpr1   SmcExpr (∨)    BoolExpr (a1)  BoolExpr (∨)
                /   \                        /    \
      BoolExpr (z1)  CvxExpr2      BoolExpr(z1)   BoolExpr(a21)

In this example, SmcExpr(∧).abstraction points to BoolExpr(∧)
and SmcExpr(∨).abstraction points to BoolExpr(∨).
=#
mutable struct SmcExpr
	op          :: Symbol # :And, :Or, :Not (be careful)
	children    :: Array{Union{LeafType, SmcExpr}}
	abstraction :: Union{Nothing, BoolExpr}
	shape       :: Tuple
	
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
	function SmcExpr(op::Symbol, children::Array{T}, abstraction::Union{Nothing, BoolExpr}, shape::Tuple) where T <: Union{LeafType, SmcExpr}
		if op == :Not && length(children) >= 1 && check_exists(CvxConstraint, children)
			error("Cannot construct a negated convex constraint.")
		end
		return new(op, children, abstraction, shape)
	end
end

NodeType = Union{CvxConstraint, BoolExpr, SmcExpr}


# Define better constructors
SmcExpr(expr::Array{T})             where T <: NodeType = SmcExpr(:Identity, expr, nothing, size(expr))
SmcExpr(op::Symbol, expr::Array{T}) where T <: NodeType = SmcExpr(op, expr, nothing, size(expr))

Base.show(io::IO, expr::SmcExpr) = print(io, string(expr))

function Base.string(expr::SmcExpr, indent=0)
	if expr.op == :Identity	
		return "$(repeat(" | ", indent))$(expr.op) $(expr.shape) -> $(!isnothing(expr.abstraction) ? expr.abstraction : "")\n"
	else
		res = "$(repeat(" | ", indent))$(expr.op)\n"
		for e in expr.children
			res *= string(e, indent+1)
		end
		return res
	end
end

# this prevents double negations
~(e ::NodeType)               = e.op == :Not ? SmcExpr(:Identity, e.children) : SmcExpr(:Not, [e,])
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

# abstraction! constructs a matching expr tree in abstract_constraints where all cvx constraints
# are replaced by BoolExprs
# recursion by multiple dispatch!
# base cases
_assign!(expr::BoolExpr,      name="a") = expr
_assign!(expr::CvxConstraint, name="a") = BoolExpr(1, name)
# recursive case
function _assign!(expr::SmcExpr, name="a")
	bool_expr = nothing
	if expr.op == :Identity
		bool_expr = _assign!(expr.children[1])

	elseif expr.op == :Not
		bool_expr = ~(_assign!(expr.children[1]))

	elseif expr.op == :And
		bool_expr = and(map( (c::Tuple{Int, NodeType}) -> _assign!(c[2], "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	elseif expr.op == :Or
		bool_expr = or(map(  (c::Tuple{Int, NodeType}) -> _assign!(c[2], "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	else
		error("Unrecognized operation $(expr.op)")
	end
	expr.abstraction = bool_expr
	return bool_expr
end
function abstraction!(prob::SmcProblem)
	prob.abstract_constraints = map(_assign!, prob.constraints)
end


#=
c_construct generates a convex problem
from a tree-like SmcExpr structure, we want to select the convex constraints corresponding to 
=#
# TODO eventually this will handle caching conic_form! from Convex.jl to speed up

# base case - both SmcExpr and BoolExpr trees have a BoolExpr leaf
c_construct!(c_expr::BoolExpr, b_expr::BoolExpr, C::Array{CvxConstraint}) = nothing

# base case - SmcExpr tree has a Convex leaf and matching BoolExpr tree has a BoolExpr leaf
c_construct!(c_expr::CvxConstraint, b_expr::BoolExpr, C::Array{CvxConstraint}) = all(b_expr.value) ? push!(C, c_expr) : nothing

# recursive case, pass through
c_construct!(c_expr::SmcExpr, b_expr::BoolExpr, C::Array) =
	map( (c) -> c_construct!(c[1], c[2], C), zip(c_expr.children, b_expr.children) )

# top level
function c_construct(prob::SmcProblem)
	# the (c) -> c_construct(c[1], c[2], C) arises because zip makes tuples
	C = Array{CvxConstraint}(undef, 0)
	map( (c) -> c_construct!(c[1], c[2], C), zip(prob.constraints, prob.abstract_constraints) )
	return Convex.minimize(0.0, C)
end


function solve!(prob::SmcProblem, δ=1e-3, cvx_solver=SCS.Optimizer())
	abstraction!(prob)
	# this is a call to JuliaZ3
	sat_prob = Problem(prob.abstract_constraints)
	solve!(sat_prob)
	# check for exit conditions
	if sat_prob.status == :UNKNOWN
		error("SAT problem failed")
	elseif sat_prob.status == :UNSAT
		println("Problem has no solution")
		prob.status == :UNSAT
		return
	end
	# c_construct generates a convex problem
	cvx_prob = c_construct(prob)
	# this is a call to Convex.jl # TODO eventually we will cache conic_form! and use that instead
	Convex.solve!(cvx_prob, cvx_solver)
	# generate IIS certificate
#	cc = iis(prob, c_prob, δ)
#	prob.abstract_constraints += cc
end


# SELF TEST
using SCS
x = CvxVar(1)

expr1 = SmcExpr(:Not, [BoolExpr(1, "z1")], nothing, (1,))
expr2 = (x >= 1.0) ∨ (x <= 10.0)
expr3 = ~expr1
println(expr2)

problem = SmcProblem([expr1, expr2 ∨ expr3])
abstraction!(problem)
z3_prob = Problem(problem.abstract_constraints)
solve!(z3_prob)
println("Z3 result $(z3_prob.status)")

c_prob = c_construct(problem)

println(c_prob)
Convex.solve!(c_prob, SCS.Optimizer())