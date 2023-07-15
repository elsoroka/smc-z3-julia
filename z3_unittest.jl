using Test, LinearAlgebra
include("z3_utility.jl")

# https://docs.julialang.org/en/v1/stdlib/Test/
# Example of a unittest
# @test π ≈ 3.14 atol=0.01

# BASIC FUNCTIONALITY (TODO)

z = BoolExpr("z")
z1 = BoolExpr(1, "z1")
z12 = BoolExpr(1,2,"z12")
z32 = BoolExpr(3,2,"z32")
z23 = BoolExpr(2,3, "z23")

@testset "Multidimensional behavior" begin
# Sizes are correct
@test all(size(z) .== size(z1))
@test all(size(z1) .== (1,))
@test all(size(z32) .== (3,2))

# Sizes are broadcastable
# (1,) broadcasts with (1,2)
@test all(size(z ∧ z12) .== (1,2))
@test all(size(z1 ∨ z12) .== (1,2))
# (1,) broadcasts with (2,3)
@test all(size(z1 ∨ z32) .== (3,2))
# (1,2) broadcasts with (3,2)
@test all(size(z12 ∧ z32) .== (3,2))

# Wrong sizes aren't broadcastable
# (1,2) doesn't broadcast with (2,3)
@test_throws DimensionMismatch z12 ∧ z23
# (2,3) doesn't broadcast with (3,2)
@test_throws DimensionMismatch z32 ∨ z23

# Nested wrong sizes also aren't broadcastable
@test_throws DimensionMismatch (z1∨z23) ∨ z32
end

@testset "Logical operations" begin
    # and(z) = z and or(z) = z
    @test and(z1) == z1
    @test or(z23) == z23
    
	# Can construct with 2 exprs
    @test all((z1 ∧ z32).children .== [z1, z32]) && (z1 ∧ z32).op == :And
    @test  (z1 ∧ z32).name == "and_z1...z32"
    @test all((z1 ∨ z32).children .== [z1, z32]) && (z1 ∨ z32).op == :Or
    @test  (z1 ∨ z32).name == "or_z1...z32"

    # Can construct with N>2 exprs
    or_N = or([z1, z12, z32])
    and_N = and([z1, z12, z32])

    @test all(or_N.children .== [z1, z12, z32]) 
    @test  and_N.name == "and_z1...z32"

    @test all(or_N.children .== [z1, z12, z32]) 
	@test  or_N.name == "or_z1...z32"
    
    # Can construct negation
    @test (~z32).op == :Not && (~z32).children == [z32,]
    @test (~z32).name == "~z32"

    # Can construct Implies
    @test z1→z23 == z23∨~z1

 
end

@testset "Problem solving" begin

end