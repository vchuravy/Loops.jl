baremodule Loops

const _TOP_MOD = ccall(:jl_base_relative_to, Any, (Any,), Loops)::Module

# imports
import ._TOP_MOD: ==, getindex, setindex!

import ._TOP_MOD:     # Base definitions
    @__MODULE__, @eval, @assert, @specialize, @nospecialize, @inbounds, @inline, @noinline,
    @label, @goto, !, !==, !=, ≠, +, -, *, ≤, <, ≥, >, &, |, <<, error, missing, copy,
    Vector, BitSet, IdDict, IdSet, UnitRange, Csize_t, Callable, ∪, ⊆, ∩, :, ∈, ∉, =>,
    in, length, get, first, last, haskey, keys, get!, isempty, isassigned,
    pop!, push!, pushfirst!, empty!, delete!, max, min, enumerate, unwrap_unionall,
    ismutabletype, collect

import Core.Compiler: # Core.Compiler specific definitions
    IRCode, construct_domtree, dominates

include(x) = _TOP_MOD.include(@__MODULE__, x)

struct LoopInfo
    header::Int
    latches::Vector{Int}
    blocks::Vector{Int}
end

function construct_loopinfo(ir::IRCode, domtree=construct_domtree(ir.cfg.blocks))
    cfg = ir.cfg

    # 1. find backedges
    # Edge n -> h, where h dominates n
    backedges = Pair{Int, Int}[]
    for (n, bb) in enumerate(cfg.blocks)
        for succ in bb.succs
            if dominates(domtree, succ, n)
                push!(backedges, n => succ)
            end
        end
    end
    isempty(backedges) && return nothing

    loops = IdDict{Int, LoopInfo}()
    for (n, h) in backedges
        # merge loops that have the same header
        if haskey(loops, h)
            visited = BitSet(loops[h].blocks)
            latches = loops[h].latches
        else
            visited = BitSet((h,))
            latches = Int[]
        end
        push!(visited, n)
        push!(latches, n)

        # Create {n′ | n is reachable from n′ in CFG \ {h}} ∪ {h}
        worklist = copy(cfg.blocks[n].preds)
        while !isempty(worklist)
            idx = pop!(worklist)
            idx ∈ visited && continue

            push!(visited, idx)
            append!(worklist, cfg.blocks[idx].preds)
        end

        blocks = collect(visited)
        # Assume sorted in CFG order
        loops[h] = LoopInfo(h, latches, blocks)
    end

    # Find exiting and exit blocks 
    # LLVM calculates this on the fly
    # for loop in values(loops)
    #     for bb in loop.blocks
    #         for succ in cfg.blocks[bb].succs
    #             succ ∈ loop.blocks && continue
    #             push!(loop.exiting, bb)
    #             push!(loop.exits, succ)
    #         end
    #     end
    # end

    # TODO: Loop nesting/Control tree
    return loops 
end

end # module Loops
