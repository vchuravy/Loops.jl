# Based off TKF: https://github.com/JuliaLang/julia/pull/45305

###
### CFG manipulation tools
###

import Core: Compiler

##
# basicblock.jl
##

==(a::BasicBlock, b::BasicBlock) =
    a.stmts === b.stmts && a.preds == b.preds && a.succs == b.succs

##
# utilities.jl
##

function _cumsum!(ys)
    isempty(ys) && return ys
    acc = ys[1]
    for i in 2:length(ys)
        acc += ys[i]
        ys[i] = acc
    end
    return ys
end

function isincreasing(xs; by = identity)
    y = iterate(xs)
    y === nothing && return true
    x1, state = y
    while true
        y = iterate(xs, state)
        y === nothing && return true
        x2, state = y
        isless(by(x1), by(x2)) || return false
        x1 = x2
    end
end

##
# ir.jl
##

==(a::CFG, b::CFG) = a.blocks == b.blocks && a.index == b.index

function cfg_reindex!(cfg::CFG)
    resize!(cfg.index, length(cfg.blocks) - 1)
    for ibb in 2:length(cfg.blocks)
        cfg.index[ibb-1] = first(cfg.blocks[ibb].stmts)
    end
    return cfg
end

"""
    NewBlocksInfo
Information on basic blocks newly allocated in `allocate_new_blocks!`.  See
[`allocate_new_blocks!`](@ref) for explanation on the properties.
"""
struct NewBlocksInfo
    positions_nblocks::Vector{Pair{Int,Int}}
    block_to_range::IdDict{Int,UnitRange{Int}}
    ssachangemap::Vector{Int}
    bbchangemap::Vector{Int}
end

"""
    allocate_new_blocks!(
        ir::IRCode,
        positions_nblocks::Vector{Pair{Int,Int}},
    ) -> info::NewBlocksInfo
For each `position => nblocks` in `positions_nblocks`, add new "singleton" `nblocks` blocks
(i.e., each BB contains a single dummy instruction) before the statement `position`.
The caller must ensure that:
    statement_positions = map(first, positions_nblocks)
    @assert all(>(0), diff(statement_positions))
    @assert all(1 <= p <= length(ir.stmts) for p in statement_positions)
    @assert all(nblocks > 0 for (_, nblocks) in positions_nblocks)
Note that this function does not wire up the CFG for newly created BBs. It just
inserts the dummy `GotoNode(0)` at the end of the new singleton BBs and the BB
_before_ (in terms of `ir.cfg.bocks`) it.  The predecessors of the BB just
before the newly added singleton BB and the successors of the BB just after the
newly added singleton BB are re-wired.  See `allocate_goto_sequence!` for
an example for creating a valid CFG.
For example, given an `ir` containing:
    #bb
        %1 = instruction_1
        %2 = instruction_2
`allocate_new_blocks!(ir, [2 => 1])` produces
    #bb′
        %1 = instruction_1
        goto #0               # dummy
    #new_bb_1
        goto #0               # dummy
    #new_bb_2
        %2 = instruction_2
The predecessors of `#bb′` are equivalent to the predecessors of `#bb`.  The successors of
`#new_bb_2` are equivalent to the successors of `#bb`.
The returned object `info::NewBlocksInfo` has the following properties:
* `positions_nblocks`: The second argument.
* `block_to_range`: A mapping from an old basic block index to the indices of
  `positions_nblocks` that contains the statements of the old basic block.
* `ssachangemap`: Given an original statement position `iold`, the new statement position is
  `ssachangemap[iold]`.
* `bbchangemap`: Given an original basic block id `iold`, the new basic block ID is
  `bbchangemap[iold]`.
Functions [`split_blocks`](@ref), [`split_positions`](@ref), and
[`inserted_blocks`](@ref) can be used to iterate over the newly added basic blocks.  These
functions support the following access patterns:
```julia
blocks::NewBlocksInfo
for sb in split_blocks(blocks)  # iterate over split BBs
    sb.oldbb::Int
    sb.indices::UnitRange{Int}
    for sp in split_positions(sb)  # iterate over split positions
        sp.oldbb::Int;   @assert sp.oldbb == sb.oldbb
        sp.prebb::Int    # BB before the split position (exclusive)
        sp.postbb::Int   # BB after the split position (inclusive)
        sp.index::Int;   @assert sp.index ∈ sb.indices
        position, nblocks = blocks.positions_nblocks[sp.index]
        for ib in inserted_blocks(sp)  # iterate over newly added BBs
            ib.oldbb::Int;  @assert ib.oldbb == sb.oldbb
            ib.newbb::Int;  @assert sp.prebb < ib.newbb < sp.postbb
            ib.index::Int;  @assert ib.index == ib.index
            ib.nth::Int;    @assert ib.nth ∈ 1:nblocks
        end
    end
end
```
"""
function allocate_new_blocks!(ir::IRCode, positions_nblocks::Vector{Pair{Int,Int}})
    @assert isincreasing(positions_nblocks; by = first)
    ssachangemap = Vector{Int}(undef, length(ir.stmts) + length(ir.new_nodes.stmts))
    let iold = 1, inew = 1
        for (pos, nblocks) in positions_nblocks
            @assert 1 <= pos <= length(ir.stmts)
            @assert nblocks >= 0
            for i in iold:pos-1
                ssachangemap[i] = inew
                inew += 1
            end
            inew += 1 + nblocks
            iold = pos
        end
        for i in iold:length(ssachangemap)
            ssachangemap[i] = inew
            inew += 1
        end
    end

    # For the original basic block index `ibb`, the pairs of position and the number of
    # blocks to be inserted can be obtained by:
    #     indices = block_to_range[ibb]::UnitRange
    #     positions_nblocks[indices]
    block_to_range = IdDict{Int,UnitRange{Int}}()

    # Two maps are used for relabeling BBs:
    # * `bbchangemap` maps each old BB index to the index of the BB that includes the *last*
    #   statement in the old BB.
    # * `gotolabelchangemap` maps each old BB index to the index of the BB that includes
    #   *first* statement in the old BB; i.e., it is used for fixing the labels in the
    #   goto-like nodes.
    bbchangemap = ones(Int, length(ir.cfg.blocks))
    gotolabelchangemap = ones(Int, length(ir.cfg.blocks) + 1)  # "+ 1" simplifies the code
    newblocks = 0

    let pre_index = 0, pre_ibb = 0
        for (i, (ipos, nblocks)) in pairs(positions_nblocks)
            ibb = block_for_inst(ir.cfg, ipos)

            if pre_ibb != ibb
                if pre_ibb != 0
                    block_to_range[pre_ibb] = pre_index:i-1
                end
                pre_index = i
                pre_ibb = ibb
            end

            bbchangemap[ibb] += 1 + nblocks
            gotolabelchangemap[ibb+1] += 1 + nblocks
            newblocks += 1 + nblocks
        end
        block_to_range[pre_ibb] = pre_index:length(positions_nblocks)
    end
    _cumsum!(bbchangemap)
    _cumsum!(gotolabelchangemap)

    # Insert `newblocks` new blocks:
    oldnblocks = length(ir.cfg.blocks)
    resize!(ir.cfg.blocks, oldnblocks + newblocks)
    # Copy pre-existing blocks:
    for iold in oldnblocks:-1:1
        bb = ir.cfg.blocks[iold]
        for labels in (bb.preds, bb.succs)
            for (i, l) in pairs(labels)
                labels[i] = bbchangemap[l]
            end
            # Note: Some labels that are referring to the split BBs are still incorrect
            # at this point.  These are copied to the new BBs in the next phase (and thus
            # relabeling here is still required).
        end
        start = ssachangemap[bb.stmts.start]
        stop = ssachangemap[bb.stmts.stop]
        ir.cfg.blocks[bbchangemap[iold]] = BasicBlock(bb, StmtRange(start, stop))
    end
    # Insert new blocks:
    for (iold, indices) in block_to_range
        ilst = bbchangemap[iold]  # using bbchangemap as it's already moved
        bblst = ir.cfg.blocks[ilst]

        # Assign `StmtRange`s to the new BBs (edges are handled later)
        prefirst = bblst.stmts.start  # already moved
        inew = get(bbchangemap, iold - 1, 0) + 1
        local oldpos
        for i in indices
            oldpos, nblocks = positions_nblocks[i]
            p = get(ssachangemap, oldpos - 1, 0) + 1
            ir.cfg.blocks[inew] = BasicBlock(StmtRange(min(prefirst, p), p))
            inew += 1
            p += 1
            for _ in 1:nblocks
                ir.cfg.blocks[inew] = BasicBlock(StmtRange(p, p))
                inew += 1
                p += 1
            end
            @assert p == ssachangemap[oldpos]
            prefirst = p
        end

        # Handle edges of the "head" and "tail" BBs
        ifst = get(bbchangemap, iold - 1, 0) + 1
        bbfst = ir.cfg.blocks[ifst]
        for p in bblst.preds
            k = findfirst(==(ilst), ir.cfg.blocks[p].succs)
            @assert k !== nothing
            ir.cfg.blocks[p].succs[k] = ifst
        end
        copy!(bbfst.preds, bblst.preds)
        empty!(bblst.preds)
        stmts = StmtRange(ssachangemap[oldpos], last(bblst.stmts))
        ir.cfg.blocks[bbchangemap[iold]] = BasicBlock(bblst, stmts)
        @assert !isempty(stmts)
    end
    for bb in ir.cfg.blocks
        @assert !isempty(bb.stmts)
    end
    cfg_reindex!(ir.cfg)

    on_ssavalue(v) = SSAValue(ssachangemap[v.id])
    on_phi_label(l) = bbchangemap[l]
    on_goto_label(l) = gotolabelchangemap[l]
    for stmts in (ir.stmts, ir.new_nodes.stmts)
        for i in 1:length(stmts)
            st = stmts[i]
            inst = ssamap(on_ssavalue, st[:inst])
            if inst isa PhiNode
                edges = inst.edges::Vector{Int32}
                for i in 1:length(edges)
                    edges[i] = on_phi_label(edges[i])
                end
            elseif inst isa GotoNode
                inst = GotoNode(on_goto_label(inst.label))
            elseif inst isa GotoIfNot
                inst = GotoIfNot(inst.cond, on_goto_label(inst.dest))
            elseif isexpr(inst, :enter)
                inst.args[1] = on_goto_label(inst.args[1]::Int)
            end
            Core.Compiler.setindex!(st, inst, :inst)
            # st[:inst] = inst
        end
    end
    minpos, _ = positions_nblocks[1]  # it's sorted
    for (i, info) in pairs(ir.new_nodes.info)
        if info.pos >= minpos
            ir.new_nodes.info[i] = if info.attach_after
                NewNodeInfo(ssachangemap[info.pos], info.attach_after)
            else
                NewNodeInfo(get(ssachangemap, info.pos - 1, 0) + 1, info.attach_after)
            end
        end
    end

    # Fixup `ir.linetable` before mutating `ir.stmts.lines`:
    linetablechangemap = Vector{Int32}(undef, length(ir.linetable))
    fill!(linetablechangemap, 1)
    let lines = ir.stmts.line
        # Allocate spaces for newly inserted statements
        for (pos, nblocks) in positions_nblocks
            linetablechangemap[lines[pos]] += 1 + nblocks
        end
    end
    _cumsum!(linetablechangemap)
    let newlength = linetablechangemap[end], ilast = newlength + 1
        @assert newlength == length(ir.linetable) + newblocks
        resize!(ir.linetable, newlength)
        for iold in length(linetablechangemap):-1:1
            inew = linetablechangemap[iold]
            oldinfo = ir.linetable[iold]
            inlined_at = oldinfo.inlined_at
            if inlined_at != 0
                inlined_at = linetablechangemap[inlined_at]
            end
            newinfo = LineInfoNode(
                oldinfo.module,
                oldinfo.method,
                oldinfo.file,
                oldinfo.line,
                inlined_at,
            )
            for i in inew:ilast-1
                ir.linetable[i] = newinfo
            end
            ilast = inew
        end
    end

    # Fixup `ir.stmts.line`
    let lines = ir.stmts.line, iold = length(lines), inew = iold + newblocks

        resize!(lines, inew)
        for i in length(positions_nblocks):-1:1
            pos, nblocks = positions_nblocks[i]
            while pos <= iold
                lines[inew] = linetablechangemap[lines[iold]]
                iold -= 1
                inew -= 1
            end
            for _ in 1:1+nblocks
                lines[inew] = linetablechangemap[lines[iold+1]]
                inew -= 1
            end
        end
        @assert inew == iold
    end

    # Fixup `ir.new_nodes.stmts.line`
    let lines = ir.new_nodes.stmts.line
        for i in 1:length(lines)
            lines[i] = linetablechangemap[lines[i]]
        end
    end

    function allocate_stmts!(xs, filler)
        n = length(xs)
        resize!(xs, length(xs) + newblocks)
        for i in n:-1:1
            xs[ssachangemap[i]] = xs[i]
        end
        for i in 2:n
            for j in ssachangemap[i-1]+1:ssachangemap[i]-1
                xs[j] = filler
            end
        end
        for js in (1:ssachangemap[1]-1, ssachangemap[end]+1:length(xs))
            for j in js
                xs[j] = filler
            end
        end
    end

    allocate_stmts!(ir.stmts.inst, GotoNode(0))  # dummy
    allocate_stmts!(ir.stmts.type, Any)
    allocate_stmts!(ir.stmts.info, NoCallInfo())
    allocate_stmts!(ir.stmts.flag, 0)

    return NewBlocksInfo(positions_nblocks, block_to_range, ssachangemap, bbchangemap)
end

"""
    split_blocks(blocks::NewBlocksInfo)
Iterate over old basic blocks that are split.
Each element `sb::SplitBlock` of the iterable returned from `split_blocks` has the following
properties:
* `blocks::NewBlocksInfo`
* `oldbb::Int`: Old index of a BB that is split.
* `indices`: For each `i` in `indices`, `blocks.positions_nblocks[i]` is the pair
  `position => nblocks` that specifies that `nblocks` new blocks are inserted at statement
  `position`.
Use `split_positions(sb::SplitBlock)` to iterate over the statement positions at which
the old basic blocks are split.
"""
function split_blocks end

"""
    split_positions(sb::SplitBlock)
    split_positions(blocks::NewBlocksInfo)
Iterate over the statement positions at which the old basic blocks are split.
Each element `sp::SplitPosition` of the iterable returned from `split_positions` has the
following properties:
* `blocks::NewBlocksInfo`
* `index`: `blocks.positions_nblocks[index]` is the pair `position => nblocks` that
  specifies that `nblocks` new blocks are inserted at statement `position`.
* `oldbb::Int`: Old index of a BB that is split.
* `prebb::Int`: New index of the BB before the split position (exclusive).
* `postbb::Int`: New index of the BB after the split position (inclusive).
Use `inserted_blocks(sp::SplitPosition)` to iterate over the newly added "singleton"
basic blocks.
"""
function split_positions end

"""
    inserted_blocks(sp::SplitPosition)
    inserted_blocks(sb::SplitBlock)
    inserted_blocks(blocks::NewBlocksInfo)
Iterate over the newly added basic blocks.
Each element `ib::InsertedBlock` of the iterable returned from `inserted_blocks` has the
following properties:
* `blocks::NewBlocksInfo`
* `index`: `blocks.positions_nblocks[index]` is the pair `position => nblocks` that
  specifies that `nblocks` new blocks are inserted at statement `position`.
* `oldbb::Int`: Old index of a BB that is split.
* `newbb::Int`: New index of this BB.
* `nth::Int`: This BB is the `nth` BB at this split position.
"""
function inserted_blocks end

struct SplitBlock
    blocks::NewBlocksInfo
    oldbb::Int
    indices::UnitRange{Int}
end

struct SplitPosition
    blocks::NewBlocksInfo
    oldbb::Int
    prebb::Int
    postbb::Int
    index::Int
end

struct InsertedBlock
    blocks::NewBlocksInfo
    oldbb::Int
    newbb::Int
    index::Int
    nth::Int
end

new_head_bb(sb::SplitBlock) = get(sb.blocks.bbchangemap, sb.oldbb - 1, 0) + 1
new_tail_bb(sb::SplitBlock) = sb.blocks.bbchangemap[sb.oldbb]

function split_blocks(blocks::NewBlocksInfo)
    oldblocks = sort!(collect(Int, keys(blocks.block_to_range)))
    Iterators.map(oldblocks) do oldbb
        indices = blocks.block_to_range[oldbb]
        SplitBlock(blocks, oldbb, indices)
    end
end

struct SplitPositionIterator
    split::SplitBlock
end

function iterate(
    it::SplitPositionIterator,
    (index, prevbb) = (first(it.split.indices), new_head_bb(it.split)),
)
    (; blocks, oldbb, indices) = it.split
    index > last(indices) && return nothing
    _pos, nblocks = blocks.positions_nblocks[index]
    postbb = prevbb + 1 + nblocks
    sp = SplitPosition(blocks, oldbb, prevbb, postbb, index)
    return (sp, (index + 1, postbb))
end

split_positions(sb::SplitBlock) = SplitPositionIterator(sb)
split_positions(blocks::NewBlocksInfo) =
    Iterators.flatmap(split_positions, split_blocks(blocks))

function inserted_blocks(sp::SplitPosition)
    (; blocks, index) = sp
    _pos, nblocks = blocks.positions_nblocks[index]
    Iterators.map(1:nblocks) do nth
        InsertedBlock(sp.blocks, sp.oldbb, sp.prebb + nth, sp.index, nth)
    end
end

inserted_blocks(x) = Iterators.flatmap(inserted_blocks, split_positions(x))

"""
    allocate_goto_sequence!(ir::IRCode, positions_nblocks) -> info::NewBlocksInfo
Add new BBs using `allocate_new_blocks!(ir, positions_nblocks)` and then connect them by
"no-op" `GotoNode` that jumps to the next BB.  Unlike `allocate_new_blocks!`, this function
results in an IR with valid CFG.
Read `allocate_new_blocks!` on the preconditions on `positions_nblocks`.
For example, given an `ir` containing:
    #bb
        %1 = instruction_1
        %2 = instruction_2
`allocate_new_blocks!(ir, [2 => 1])` produces
    #bb′
        %1 = instruction_1
        goto #new_bb_1
    #new_bb_1
        goto #new_bb_2
    #new_bb_2
        %2 = instruction_2
"""
function allocate_goto_sequence!(ir::IRCode, positions_nblocks)
    blocks = allocate_new_blocks!(ir, positions_nblocks)
    function set_goto(ibb1::Int)
        ibb2 = ibb1 + 1
        b1 = ir.cfg.blocks[ibb1]
        @assert ir.stmts.inst[last(b1.stmts)] === GotoNode(0)
        ir.stmts.inst[last(b1.stmts)] = GotoNode(ibb2)
        cfg_insert_edge!(ir.cfg, ibb1, ibb2)
    end
    for sp in split_positions(blocks)
        set_goto(sp.prebb)
        for block in inserted_blocks(sp)
            set_goto(block.newbb)
        end
    end
    return blocks
end