# test/runtests.jl
using Test

# immer relativ zum Testordner laden
include(joinpath(@__DIR__, "tests.jl"))   # falls du bei .ji bleiben willst
# oder: include(joinpath(@__DIR__, "tests.jl"))
