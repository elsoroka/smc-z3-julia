# New file since we now have the typing down
import SCS
import Convex as CVX
import Base.show, Base.string, Base.~, Base.length, Base.size
include("cvx_prettyprint.jl")

# include("z3_utility.jl") # TODO fix this import so we only import the useful parts
push!(LOAD_PATH, "../../../../research/BooleanSatisfiability.jl/src/")
import BooleanSatisfiability as SAT

LeafType = Union{CVX.Constraint, SAT.BoolExpr}

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
	abstraction :: Union{Nothing, SAT.BoolExpr}
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
	function SmcExpr(op::Symbol, children::Array{T}, abstraction::Union{Nothing, SAT.BoolExpr}, shape::Tuple) where T <: Union{LeafType, SmcExpr}
		if op == :Not && length(children) >= 1 && check_exists(CVX.Constraint, children)
			@error "Cannot construct a negated convex constraint."
		end
		return new(op, children, abstraction, shape)
	end
end

NodeType = Union{CVX.Constraint, SAT.BoolExpr, SmcExpr}


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
#~(e ::NodeType)               = e.op == :Not ? SmcExpr(:Identity, e.children) : SmcExpr(:Not, [e,])
∧(e1::NodeType, e2::NodeType) = SmcExpr(:And, NodeType[e1, e2])
∨(e1::NodeType, e2::NodeType) = SmcExpr(:Or, NodeType[e1, e2])
⟹(e1::NodeType, e2::NodeType) = (~e1) ∨ e2

and(es::Array{T}) where T <: NodeType = SmcExpr(:And, es)
or(es::Array{T}) where T <: NodeType = SmcExpr(:Or, es)

# TODO Can we define advanced STL operations (always, eventually, etc)


# SMC ALGORITHM IMPLEMENTATION

# This object associates a Boolean abstraction variable with a convex constraint
# It stores references so it shouldn't be inefficient
# An array of SmcMapping objects corresponds to the M object in the paper.
mutable struct SmcMapping
	abstract_expr :: SAT.BoolExpr
	cvx_expr      :: CVX.Constraint
end

# Problem struct
mutable struct SmcProblem
	objective            :: Union{Convex.AbstractExpr, AbstractFloat}
	constraints          :: Array{NodeType}
	abstract_constraints :: Array{SAT.BoolExpr}
	mapping              :: Array{SmcMapping}
	status               :: Symbol # :OPTIMAL, :UNSAT, :UNKNOWN
end

SmcProblem(constraints::Array{T}) where T <: NodeType = SmcProblem(0.0, constraints, SAT.BoolExpr[], SmcMapping[], :UNSAT)
SmcProblem(obj, constraints::Array{T}) where T <: NodeType = SmcProblem(obj, constraints, SAT.BoolExpr[], SmcMapping[], :UNSAT)

# abstraction! constructs a matching expr tree in abstract_constraints where all cvx constraints
# are replaced by BoolExprs
# recursion by multiple dispatch!
# base cases
_assign!(expr::SAT.BoolExpr, mapping::Array{SmcMapping}, name="a") = expr
function _assign!(expr::CVX.Constraint, mapping::Array{SmcMapping}, name="a")
	b = SAT.Bool(name)
	push!(mapping, SmcMapping(b, expr))
	return b
end
# recursive case
function _assign!(expr::SmcExpr, mapping::Array{SmcMapping}, name="a")
	bool_expr = nothing
	if expr.op == :Identity
		bool_expr = _assign!(expr.children[1], mapping)

	elseif expr.op == :Not
		bool_expr = SAT.not(_assign!(expr.children[1], mapping))

	elseif expr.op == :And
		bool_expr = SAT.and(map( (c::Tuple{Int, NodeType}) -> _assign!(c[2], mapping, "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	elseif expr.op == :Or
		bool_expr = SAT.or(map(  (c::Tuple{Int, NodeType}) -> _assign!(c[2], mapping, "$(name)_$(c[1])"),
			            enumerate(expr.children) ))
	else
		@error "Unrecognized operation $(expr.op)"
	end
	expr.abstraction = bool_expr
end

function abstraction!(prob::SmcProblem)
	prob.mapping = SmcMapping[]
	prob.abstract_constraints = map( (tp) -> _assign!(tp[2], prob.mapping, "a$(tp[1])"), enumerate(prob.constraints) )
end


#=
c_construct generates a convex problem
from a tree-like SmcExpr structure, we want to select the convex constraints corresponding to 
=#
# TODO eventually this will handle caching conic_form! from Convex.jl to speed up

# base case - both SmcExpr and BoolExpr trees have a BoolExpr leaf
c_construct!(c_expr::SAT.BoolExpr, b_expr::SAT.BoolExpr, C::Array{CVX.Constraint}) = nothing

# base case - SmcExpr tree has a Convex leaf and matching BoolExpr tree has a BoolExpr leaf
c_construct!(c_expr::CVX.Constraint, b_expr::SAT.BoolExpr, C::Array{CVX.Constraint}) = all(b_expr.value) ? push!(C, c_expr) : nothing

# recursive case, pass through
c_construct!(c_expr::SmcExpr, b_expr::SAT.BoolExpr, C::Array) =
	map( (c) -> c_construct!(c[1], c[2], C), zip(c_expr.children, b_expr.children) )

# top level
function c_construct(prob::SmcProblem)
	# the (c) -> c_construct(c[1], c[2], C) arises because zip makes tuples
	C = Array{CVX.Constraint}(undef, 0)
	map( (c) -> c_construct!(c[1], c[2], C), zip(prob.constraints, prob.abstract_constraints) )
	return C
end

# Add the slack variable to the appropriate side of the constraint
# This constructs a new constraint, otherwise we get multiple slack variables added to the same constraint because it would be modified in place.
function add_s(a::Tuple) :: CVX.Constraint
	cons = a[1]
	if cons.head == :<=
		return cons.lhs <= cons.rhs + a[2]
	elseif cons.head == :(==)
		return cons.lhs == cons.rhs + a[2]
	else # >=
		return cons.lhs + a[2] >= cons.rhs
	end
end

# solve sum-of-slack problem which is equivalent to original when all slack vars are 0
# returns a new, solved convex problem and list of slack variables
function c_solve_ssf(constraints, obj, δ=1e-3, cvx_solver=SCS.Optimizer)
	# TODO URGENT - 4/10/23 - this is the culprit.
	# We shouldn't make NEW slack variables.
	# We should attach them to the Problem and reuse the same ones.
	#s = Convex.Variable(length(constraints))

	L = length(constraints)
	s = Convex.Variable(L)

	C_ssf = Convex.Constraint[]
	for pair in zip(constraints, s)
		push!(C_ssf, add_s(pair))
	end

	# Generate the sum-of-slack problem
	ssf_prob = Convex.minimize(Convex.maximum(Convex.abs(s)) + obj)
	ssf_prob.constraints += C_ssf

	Convex.solve!(ssf_prob, cvx_solver; silent_solver=true)
	return ssf_prob, s.value
end

# algorithm 2 in Shoukry et al. page 13
# TODO THERE IS STILL A BUG IN HERE
function iis(prob::SmcProblem, constraints, δ=1e-3, cvx_solver=SCS.Optimizer)
	# step 1: get the optimal slack in each constraint
	ssf_prob, s_value = c_solve_ssf(constraints, 0.0, δ, cvx_solver)
	iis_cert = Array{SAT.Expr}(undef, 0)
		# sort the constraint set by slack values, low to high (default order)
	# the sorting is wrong! be more careful
	sorted_idx = sortperm(vec(s_value))

	@debug "iis_optval $(ssf_prob.optval)"
	

	# search linearly for UNSAT certificate
	status = :SAT
	counter = length(sorted_idx)
	iis_temp_idx = [sorted_idx[1], sorted_idx[counter]]
	#println("iis_temp length $(length(iis_temp))")
	while status == :SAT
		ssf_prob, s_value = c_solve_ssf(constraints[iis_temp_idx], 0.0, δ, cvx_solver)

		@debug "iis_status in iis() = $(ssf_prob.status) $(ssf_prob.optval)"

		if maximum(abs.(s_value)) > δ #string(c_prob.status) != "OPTIMAL"
			status = :UNSAT
			#@debug "iis contains constraints"
			#global varnames
			#for c in iis_temp
			#	@debug prettyprint(c, varnames)
			#end
			# retrieve the abstraction variable a corresponding to the constraints in iis_temp
			iis_temp = constraints[iis_temp_idx]
			negations = reduce(vcat, map( (m) -> SAT.not(m.abstract_expr), filter( (m) -> m.cvx_expr in iis_temp, prob.mapping)))
			iis_cert = SAT.or(negations)

		else
			counter -= 1
			push!(iis_temp_idx, sorted_idx[counter])
		end
	end
	return iis_cert
end

# TODO the current issue is the IIS function is broken
# it is NOT learning the IIS set
# so all iterations have the same IIS set


function smc_solve!(prob::SmcProblem, δ=1e-3, cvx_solver=SCS.Optimizer, max_iters=100)
	abstraction!(prob)
	i=0
	while i < max_iters
		# this is a call to Z3
		status = SAT.sat!(SAT.and(prob.abstract_constraints))
		# check for exit conditions
		if status == :UNKNOWN
			@error "solve! SAT problem failed"
		elseif status == :UNSAT
			@info "Problem has no solution"
			prob.status == :UNSAT
			return
		end
		# c_construct generates the list of convex constraints
		constraints = c_construct(prob)
		#global varnames
		#varnames[s.id_hash] = "s_iter_$i"

		# this is a call to Convex.jl # TODO eventually we will cache conic_form! and use that instead
		_, s_value = c_solve_ssf(constraints, prob.objective, δ, cvx_solver)
		@debug "solve! slack $(maximum(abs.(s_value)))"
		#@debug "Convex problem:"
		#for c in ssf_prob.constraints
		#	@debug "$(prettyprint(c, varnames))"
		#end

		if maximum(abs.(s_value)) < δ
			prob.status = :SAT
			@debug "status is SAT"
			return
		else
			# generate IIS certificate
			cc = iis(prob, constraints, δ, cvx_solver)
			prob.abstract_constraints = vcat(prob.abstract_constraints, cc)
		end
		i += 1
	end
	@warn "Reached max_iters $max_iters"
end
