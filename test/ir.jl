import Core.Compiler
import Loops: split_positions, inserted_blocks, allocate_goto_sequence!
import Core.Compiler: BasicBlock, CFG, GotoNode, GotoIfNot, NewNodeInfo

function verify_ircode(ir)
    Compiler.verify_ir(ir)
    Compiler.verify_linetable(ir.linetable)
end

###
### CFG manipulation tools
###

function allocate_branches!(ir::Compiler.IRCode, positions_nbranches)
    blocks = allocate_goto_sequence!(
        ir,
        [p => 2n for (p, n) in positions_nbranches],
    )
    for sp in split_positions(blocks)
        for (n, block) in enumerate(inserted_blocks(sp))
            if isodd(n)
                ibb1 = block.newbb
                ibb3 = ibb1 + 2
                b1 = ir.cfg.blocks[ibb1]
                ir.stmts.inst[last(b1.stmts)] = GotoIfNot(false, ibb3)
                Core.Compiler.cfg_insert_edge!(ir.cfg, ibb1, ibb3)
            end
        end
    end
    return blocks
end

inserted_block_ranges(info) = [sp.prebb:sp.postbb for sp in split_positions(info)]



"""
    inlineinfo(ir::IRCode, line::Integer)
Extract inlining information at `line` that does not depend on `ir.linetable`.
"""
inlineinfo(ir, line) =
    map(Base.IRShow.compute_loc_stack(ir.linetable, Int32(line))) do i
        node = ir.linetable[i]
        (; node.method, node.file, node.line)
    end

"""
    check_linetable(ir, ir0, info)
Test `ir.linetable` invariances of `allocate_new_blocks!` where the arguments are used as in
```julia
ir = copy(ir0)
info = Compiler.allocate_new_blocks!(ir, ...)
```
or some equivalent code.
"""
function check_linetable(ir, ir0, info)
    (; positions_nblocks) = info
    function splabel((; index))
        origpos, _ = positions_nblocks[index]
        "Statement $origpos (= first(positions_nblocks[$index]))"
    end
    iblabel((; nth)) = "$nth-th inserted block at this split point"
    @testset "Goto nodes reflect original statement lines" begin
        @testset "$(splabel(sp))" for sp in split_positions(info)
            origpos, _ = positions_nblocks[sp.index]
            moved = ir.stmts[first(ir.cfg.blocks[sp.postbb].stmts)]

            @testset "Moved statement has the same inline info stack" begin
                orig = ir0.stmts[origpos][:line]
                @test inlineinfo(ir, moved[:line]) == inlineinfo(ir0, orig)
            end

            @testset "Pre-split block" begin
                goto = ir.stmts[last(ir.cfg.blocks[sp.prebb].stmts)]
                @test goto[:line] == moved[:line]
            end

            @testset "$(iblabel(ib))" for ib in inserted_blocks(sp)
                goto = ir.stmts[last(ir.cfg.blocks[ib.newbb].stmts)]
                @test goto[:line] == moved[:line]
            end
        end
    end
end

function single_block(x)
    x+2x 
end

#=
Input:
    #1
        %1 = $inst1     _
        %2 = $inst2      `-- split before %2
        return %2
Output:
    #1
        %1 = $inst1
        goto #2
    #2
        %3 = $inst2
        return %3
=#
@testset "Split a block in two" begin
    ir0, rt = only(Base.code_ircode(single_block, (Float64,), optimize_until = "compact 1"))
    @test length(ir0.stmts) == 3

    ir = Compiler.copy(ir0)
    info = allocate_goto_sequence!(ir, [2=>0])
    verify_ircode(ir)

    @test inserted_block_ranges(info) == [1:2]
    @test ir.cfg == CFG(
        [
            BasicBlock(Compiler.StmtRange(1, 2), Int[], [2]),
            BasicBlock(Compiler.StmtRange(3, 4), [1], Int[]),
        ],
        [3],
    )

    b1, _ = ir.cfg.blocks
    @test ir.stmts[last(b1.stmts)][:inst] == GotoNode(2)
    check_linetable(ir, ir0, info)
end

#=
Input:
    #1
        %1 = $inst1    _
        %2 = $inst2     `-- split before %2 and insert two blocks
        return %2
Output:
    #1
        %1 = $inst1
        goto #2
    #2
        goto #4 if not false
    #3
        goto #4
    #4
        %5 = $inst2
        return %5
=#
@testset "Add one branch (two new blocks) to a single-block IR" begin
    ir0, rt = only(Base.code_ircode(single_block, (Float64,), optimize_until = "compact 1"))
    @test length(ir0.stmts) == 3
    ir = Compiler.copy(ir0)
    info = allocate_branches!(ir, [2 => 1])
    # FIXME: Linetable undef
    # verify_ircode(ir)
    @test inserted_block_ranges(info) == [1:4]
    @test ir.cfg == CFG(
        [
            BasicBlock(Compiler.StmtRange(1, 2), Int[], [2])
            BasicBlock(Compiler.StmtRange(3, 3), [1], [3, 4])
            BasicBlock(Compiler.StmtRange(4, 4), [2], [4])
            BasicBlock(Compiler.StmtRange(5, 6), [3, 2], Int[])
        ],
        [3, 4, 5],
    )
    (b1, b2, b3, _) = ir.cfg.blocks
    @test ir.stmts.inst[last(b1.stmts)] == GotoNode(2)
    @test ir.stmts.inst[last(b2.stmts)] == GotoIfNot(false, 4)
    @test ir.stmts.inst[last(b3.stmts)] == GotoNode(4)
    check_linetable(ir, ir0, info)
end

#=
Input:
    #1                 _
        %1 = $inst1     `-- split before %1 and insert one block
        goto #2
    #2
        %3 = $inst2    _
        return %3       `-- split before %4 (`return %3`) and insert one block
Output:
    #1
        goto #2
    #2
        goto #3
    #3
        %1 = $inst1
        goto #4
    #4
        %5 = $inst2
        goto #5
    #5
        goto #6
    #6
        return %5
This transformation is testing inserting multiple basic blocks at once.  It also tests that
inserting at boundary locations work.
=#
@testset "Insert two more blocks to a two-block IR" begin
    ir0, rt = only(Base.code_ircode(single_block, (Float64,), optimize_until = "compact 1"))
    @test length(ir0.stmts) == 3
    @testset "Split a block in two" begin
        info = allocate_goto_sequence!(ir0, [2 => 0])
        verify_ircode(ir0)
        @test inserted_block_ranges(info) == [1:2]
    end

    ir = Compiler.copy(ir0)
    info = allocate_goto_sequence!(ir, [1 => 1, 4 => 1])
    @test length(ir.stmts) == 8
    @test inserted_block_ranges(info) == [1:3, 4:6]
    verify_ircode(ir)
    @test ir.cfg == CFG(
        [
            BasicBlock(Compiler.StmtRange(1, 1), Int[], [2])
            BasicBlock(Compiler.StmtRange(2, 2), [1], [3])
            BasicBlock(Compiler.StmtRange(3, 4), [2], [4])
            BasicBlock(Compiler.StmtRange(5, 6), [3], [5])
            BasicBlock(Compiler.StmtRange(7, 7), [4], [6])
            BasicBlock(Compiler.StmtRange(8, 8), [5], Int[])
        ],
        [2, 3, 5, 7, 8],
    )
    @test [ir.stmts.inst[last(b.stmts)] for b in ir.cfg.blocks[1:end-1]] == GotoNode.(2:6)
    check_linetable(ir, ir0, info)
end

#=
Input:
    #1
        %1 = $inst1
        %3 = new_instruction()   _
        %2 = $inst2               `-- split before %2
        return %2
Output:
    #1
        %1 = $inst1
        %2 = new_instruction()     # in the pre-split-point BB
        goto #2
    #2
        %4 = $inst2
        return %4
=#
@testset "Split a block of a pre-compact IR (attach before)" begin
    ir0, rt = only(Base.code_ircode(single_block, (Float64,), optimize_until = "compact 1"))
    @test length(ir0.stmts) == 3
    st = Expr(:call, :new_instruction)
    Compiler.insert_node!(ir0, 2, Compiler.NewInstruction(st, Any))

    ir = Compiler.copy(ir0)
    info = allocate_branches!(ir, [2 => 0])
    @test inserted_block_ranges(info) == [1:2]
    verify_ircode(ir)
    check_linetable(ir, ir0, info)

    ir = Core.Compiler.compact!(ir)
    verify_ircode(ir)
    @test ir.cfg == CFG(
        [
            BasicBlock(Compiler.StmtRange(1, 3), Int[], [2])
            BasicBlock(Compiler.StmtRange(4, 5), [1], Int[])
        ],
        [4],
    )
    @test ir.stmts[2][:inst] == st
end

#=
Input:
    #1
        %1 = $inst1              _
        %2 = $inst2               `-- split before %2
        %3 = new_instruction()
        return %2
Output:
    #1
        %1 = $inst1
        goto #2
    #2
        %3 = $inst2
        %4 = new_instruction()     # in the post-split-point BB
        return %3
=#
@testset "Split a block of a pre-compact IR (attach after)" begin
    ir0, rt = only(Base.code_ircode(single_block, (Float64,), optimize_until = "compact 1"))
    @test length(ir0.stmts) == 3
    st = Expr(:call, :new_instruction)
    Compiler.insert_node!(ir0, 2, Compiler.NewInstruction(st, Any), true)

    ir = Compiler.copy(ir0)
    info = allocate_branches!(ir, [2 => 0])
    @test inserted_block_ranges(info) == [1:2]
    verify_ircode(ir)
    check_linetable(ir, ir0, info)

    ir = Core.Compiler.compact!(ir)
    verify_ircode(ir)
    @test ir.cfg == CFG(
        [
            BasicBlock(Compiler.StmtRange(1, 2), Int[], [2])
            BasicBlock(Compiler.StmtRange(3, 5), [1], Int[])
        ],
        [3],
    )
    @test ir.stmts[4][:inst] == st
end
