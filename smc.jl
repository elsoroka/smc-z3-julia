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

# TODO add return types where appropriate

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

# This object associates a Boolean abstraction variable with a convex constraint
# It stores references so it shouldn't be inefficient
# An array of SmcMapping objects corresponds to the M object in the paper.
mutable struct SmcMapping
	abstract_expr :: BoolExpr
	cvx_expr      :: CvxConstraint
end

# Problem struct
mutable struct SmcProblem
	constraints          :: Array{SmcExpr}
	abstract_constraints :: Array{BoolExpr}
	mapping              :: Array{SmcMapping}
	status               :: Symbol # :OPTIMAL, :UNSAT, :UNKNOWN
end

SmcProblem(constraints::Array{SmcExpr}) = SmcProblem(constraints, Array{BoolExpr}[], Array{SmcMapping}[], :UNSAT)

# abstraction! constructs a matching expr tree in abstract_constraints where all cvx constraints
# are replaced by BoolExprs
# recursion by multiple dispatch!
# base cases
_assign!(expr::BoolExpr, mapping::Array{SmcMapping}, name="a") = expr
function _assign!(expr::CvxConstraint, mapping::Array{SmcMapping}, name="a")
	b = BoolExpr(1, name)
	push!(mapping, SmcMapping(b, expr))
	return b
end
# recursive case
function _assign!(expr::SmcExpr, mapping::Array{SmcMapping}, name="a")
	bool_expr = nothing
	if expr.op == :Identity
		bool_expr = _assign!(expr.children[1], mapping)

	elseif expr.op == :Not
		bool_expr = ~(_assign!(expr.children[1], mapping))

	elseif expr.op == :And
		bool_expr = and(map( (c::Tuple{Int, NodeType}) -> _assign!(c[2], mapping, "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	elseif expr.op == :Or
		bool_expr = or(map(  (c::Tuple{Int, NodeType}) -> _assign!(c[2], mapping, "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	else
		error("Unrecognized operation $(expr.op)")
	end
	expr.abstraction = bool_expr
end

function abstraction!(prob::SmcProblem)
	prob.mapping = SmcMapping[]
	prob.abstract_constraints = map( (c) -> _assign!(c, prob.mapping), prob.constraints )
end


#=
c_construct generates a convex problem
from a tree-like SmcExpr structure, we want to select the convex constraints corresponding to 
=#
# TODO eventually this will handle caching conic_form! from Convex.jl to speed up

# base case - both SmcExpr and BoolExpr trees have a BoolExpr leaf
c_construct!(c_expr::BoolExpr, b_expr::BoolExpr, C::Array{CvxConstraint}) = nothing
#c_construct!(mapping::SmcMapping{BoolExpr}, C::Array{CvxConstraint}) = nothing

# base case - SmcExpr tree has a Convex leaf and matching BoolExpr tree has a BoolExpr leaf
c_construct!(c_expr::CvxConstraint, b_expr::BoolExpr, C::Array{CvxConstraint}) = all(b_expr.value) ? push!(C, c_expr) : nothing
#c_construct!(mapping::SmcMapping{CvxConstraint}, C::Array{CvxConstraint}) = all(mapping.abstract_expr.value) ? push!(C, mapping.cvx_expr) : nothing

# recursive case, pass through
c_construct!(c_expr::SmcExpr, b_expr::BoolExpr, C::Array) =
	map( (c) -> c_construct!(c[1], c[2], C), zip(c_expr.children, b_expr.children) )
#c_construct!(mapping::SmcMapping{SmcExpr}, C::Array) =
#	map( (c) -> c_construct!(c[1], c[2], C), zip(mapping.cvx_expr.children, mapping.abstract_expr.children) )

# top level
function c_construct(prob::SmcProblem)
	# the (c) -> c_construct(c[1], c[2], C) arises because zip makes tuples
	C = Array{CvxConstraint}(undef, 0)
	map( (c) -> c_construct!(c[1], c[2], C), zip(prob.constraints, prob.abstract_constraints) )
	return Convex.minimize(0.0, C)
end

# solve sum-of-slack problem which is equivalent to original when all slack vars are 0
# returns a new, solved convex problem and list of slack variables
# TODO Problem area - doesn't work.
function c_solve_ssf(c_prob, δ=1e-3, cvx_solver=SCS.Optimizer())
	s = Convex.Variable(length(c_prob.constraints))
	# Add the slack variable to the appropriate side of the constraint
	function add_s(a::Tuple) :: Convex.Constraint
		a[1].head == :<= ? a[1].rhs += a[2] : a[1].lhs += a[2]
		return a[1]
	end
	C_ssf = map( add_s, zip(c_prob.constraints, s) ) 

	# Generate the sum-of-slack problem
	ssf_prob = Convex.minimize(Convex.sum(Convex.abs(s)))
	ssf_prob.constraints += C_ssf

	Convex.solve!(ssf_prob, cvx_solver)
	return ssf_prob, s
end

# algorithm 2 in Shoukry et al. page 13
function iis(prob::SmcProblem, c_prob, δ=1e-3, cvx_solver=SCS.Optimizer())
	# step 1: get the optimal slack in each constraint
	ssf_prob, s = c_solve_ssf(c_prob, δ)
	iis_cert = Array{BoolExpr}(undef, 0)
	
	# if there's only one constraint in which case do this
	if length(s) == 1
		iis_temp = c_prob.constraints
		return cert(iis_temp)
	end

	# sort the constraint set by slack values, low to high (default order)

	sorted_const = c_prob.constraints[sortperm(reshape(s.value, (length(s),)) )]
	# search linearly for UNSAT certificate
	status = :SAT
	counter = 2
	#iis_temp = [sorted_const[1], sorted_const[counter]]
	#println("iis_temp length $(length(iis_temp))")

	while status == :SAT
		c_prob = Convex.minimize(0.0, sorted_const[1:counter]) # TODO δ should be here
		println(c_prob)
		Convex.solve!(c_prob, cvx_solver)
		println("\nstatus = $(c_prob.status) ", c_prob.status == :OPTIMAL)
		if c_prob.status != :OPTIMAL
			status = :UNSAT
			# retrieve the abstraction variable a corresponding to the constraints in iis_temp
			iis_cert = map( (m) -> ~(m.abstract_expr), filter( (m) -> m.cvx_expr in sorted_const[1:counter], prob.mapping))
			println("counter=$counter, iis_cert =\n$iis_cert")
		else
			counter += 1
			#push!(iis_temp, sorted_const[counter])
		end
	end
	return iis_cert
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
	cc = iis(prob, cvx_prob, δ)
	prob.abstract_constraints = vcat(prob.abstract_constraints, cc)
end


# SELF TEST
using SCS
x = CvxVar(1)
y = CvxVar(2)

expr1 = SmcExpr(:Not, [BoolExpr(1, "z1")], nothing, (1,))
expr2 = (x >= 1.0) ∨ (x <= 10.0)
expr3 = ~expr1

problem = SmcProblem([expr1, expr2 ∨ expr3, (y <= 5.0)∧(y >= 10.0), (y >= 1.0) ∨ (y + x <= 1.0)])
solve!(problem)
println("x = $(x.value), y = $(y.value)")
println("expr1 = $(expr1.value)")