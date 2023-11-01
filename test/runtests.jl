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

# Move sin(x) to pre-header
function single_loop_with_sin(A, x)
    acc = zero(eltype(A))
    for a in A
        acc += sin(x) * a
    end
    return acc
end

@testset "Single-loop w sin" begin
    (ir0, rt) = only(Base.code_ircode(single_loop_with_sin, (Vector{Float64}, Float64),
                                     optimize_until = "compact 1"))

    domtree = Core.Compiler.construct_domtree(ir0.cfg.blocks)
    loops = Loops.construct_loopinfo(ir0, domtree)

    (h, LI) = only(loops)
    @test h == LI.header
    @test h ∈ LI.blocks
    @test all(BB->BB ∈ LI.blocks, LI.latches)

    ir = Core.Compiler.copy(ir0)
    ir = Loops.licm_pass!(ir)

    # Old header is pre-header
    stmts = ir.cfg.blocks[h].stmts
    @test length(stmts) == 2
    call = ir.stmts[stmts[1]][:inst]
    @test call isa Expr
    @test call.head == :call
    callee = call.args[1]
    @test callee.name == :sin
    @test ir.stmts[stmts[2]][:inst] isa Core.Compiler.GotoNode
end
