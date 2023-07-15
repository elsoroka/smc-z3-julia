import Convex
export prettyprint, @varname

macro varname(var)
    name = string(var)
		return :($name)
end

function prettyprint(c::Convex.Constraint, varnames::Dict)
    lhs = isa(c.lhs,Convex.Constant) ? string(c.lhs) : prettyprint(c.lhs, varnames)
    rhs = isa(c.rhs, Convex.Constant) ? string(c.rhs) : prettyprint(c.rhs, varnames)
    return "$lhs $(c.head) $rhs"
end

function prettyprint(a::Convex.AbstractExpr, varnames::Dict)
    childnames = map(c -> isa(c, Convex.Constant) ? string(c) : prettyprint(c, varnames), a.children)
    if length(childnames) == 2 && a.head ∈ [:+, :-, :*, :/]
        return "$(childnames[1]) $(a.head) $(childnames[2])"
    elseif a.head == :index
        return "$(childnames[1])[$(a.inds)]"
    else
        return "$(a.head)($(join(childnames, " ")))"
    end
end

function prettyprint(c::Convex.Variable, varnames::Dict)
    return varnames[c.id_hash]
end
