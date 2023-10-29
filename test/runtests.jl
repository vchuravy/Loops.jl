import Loops
using Test

function f1(A, x)
    acc = zero(eltype(A))
    for a in A
        acc += sin(x) * a
    end
    return acc
end

let (ir, rt) = only(Base.code_ircode(f1, (Vector{Float64}, Float64), optimize_until = "compact 1"))
    domtree = Core.Compiler.construct_domtree(ir.cfg.blocks)
    loops = Loops.construct_loopinfo(ir, domtree)
    header, LI = only(collect(loops))

    @test header == LI.header 
    @test header ∈ LI.blocks
    @test length(LI.latches) == 1
    @test all(BB -> BB ∈ LI.blocks, LI.latches) 
end

@testset "CFG" begin
    include("ir.jl")
end