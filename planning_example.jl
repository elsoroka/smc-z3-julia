include("smc.jl")
push!(LOAD_PATH, "../../../../research/BooleanSatisfiability.jl/src/")
ENV["JULIA_DEBUG"] = Main
import BooleanSatisfiability as SAT
println("self test")
import Convex

# In this problem we want to plan a 2D trajectory x,y over N steps
# TODO we may complicate it later by adding a quadratic approximation to nonlinear dynamics

N = 5
x = Convex.Variable(N)
y = Convex.Variable(N)
global varnames = Dict(x.id_hash => "x", y.id_hash => "y")


x_world = [0.,10.]
y_world = [0.,5.]
bounds = [0.,0.,10.,5.]
start   = [0.25,0.25]
goal    = [9.75, 2.]

# obstacles are represented by two corners (x1, y1, x2, y2)
obs_1 = [2.,0.,4.,3.]
obs_2 = [7.,1.,9.,3.5]
obs_3 = [7.,4.,9.,5.]

plot_rect(obs) = (obs[[1,3,3,1,1]], obs[[2,2,4,4,2]])

function plot_env()
    plot(plot_rect(bounds)..., color=:green, xlim=x_world, ylim=y_world, primary=false)
    plot!(plot_rect(obs_1)..., color=:red, primary=false)
    plot!(plot_rect(obs_2)..., color=:red, primary=false)
    plot!(plot_rect(obs_3)..., color=:red, primary=false)
    scatter!(start[1:1], start[2:2], markersize=5, color=:blue)
    scatter!(goal[1:1], goal[2:2], markersize=5, color=:orange, marker=:star)
end

function outside_box_at_step(xi, yi, box::Array{Float64}) :: Array{NodeType}
    x1, y1, x2, y2 = box
    return [(xi <= x1) ∨ (xi >= x2) ∨ (yi <= y1) ∨ (yi >= y2)]
end
function outside_box_in_interval(x, y, box, N1=1, N2=Inf)
    if length(x) != length(y)
        println("Warning: x and y are different lengths")
    end
    if isinf(N2)
        N2 = min(length(x), length(y))
    end
    xys = Any[(x[i], y[i]) for i=N1:N2]
    append!(xys, [(0.5*(x[i]+x[i+1]), 0.5*(y[i] + y[i+1])) for i=N1:N2-1])
    return reduce(vcat, map( xy -> outside_box_at_step(xy[1], xy[2], box), xys ))
end

umax = 10.0
#control_bounds = map( (i) -> Convex.square(x[i]-x[i-1]) + Convex.square(y[i]-y[i-1]) <= umax, 2:N )
control_bounds_x = map( (i) -> Convex.abs(x[i]-x[i-1]) <= umax, 2:N )
control_bounds_y = map( (i) -> Convex.abs(y[i]-y[i-1]) <= umax, 2:N )

constraints = vcat(
    [x >= bounds[1], y >= bounds[2], x <= bounds[3], y <= bounds[4],
     x[1] == start[1], y[1] == start[2], x[end] == goal[1], y[end] == goal[2]],
                   control_bounds_x, control_bounds_y,
                   outside_box_in_interval(x, y, obs_1),
                   #outside_box_in_interval(x, y, obs_2),
                   #outside_box_in_interval(x, y, obs_3),
                  )

obj = Convex.sumsquares(x[2:end]-x[1:end-1]) + Convex.sumsquares(y[2:end]-y[1:end-1])
prob = SmcProblem(constraints)
smc_solve!(prob, 1e-2, SCS.Optimizer, 500)

println("all true:")
println(round.(x.value .- bounds[1], digits=3))
println(round.(-x.value .+ bounds[3], digits=3))
println(round.(y.value .- bounds[2], digits=3))
println(round.(-y.value .+ bounds[4], digits=3))
println("$(x.value[1]) = $(start[1])\n$(y.value[1]) = $(start[2])
$(x.value[end]) = $(goal[1])\n$(y.value[end]) = $(goal[2])")
println(round.(x.value, digits=2))
println(round.(y.value, digits=2))