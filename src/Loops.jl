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
    ismutabletype, collect, iterate, <=, >=, ones, pairs, 
    resize!, copy!, @show, fill!,
    sort!, Iterators, isless, findfirst, filter, map!, map

import Core.Compiler: # Core.Compiler specific definitions
    IRCode, construct_domtree, dominates, block_for_inst, StmtRange, BasicBlock, CFG, ssamap,
    PhiNode, GotoNode, GotoIfNot, isexpr, SSAValue, LineInfoNode, NoCallInfo, cfg_insert_edge!,
    NewNodeInfo, cfg_delete_edge!, IR_FLAG_EFFECT_FREE, Argument, userefs, InsertBefore, NewInstruction

include(x) = _TOP_MOD.include(@__MODULE__, x)

include("ir.jl")

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

function invariant(ir, LI, invariant_stmts, stmt)
    if stmt isa Argument || stmt isa GlobalRef || stmt isa QuoteNode || stmt isa Bool
        return true
    elseif stmt isa SSAValue
        id = stmt.id
        bb = block_for_inst(ir.cfg, id)
        if bb ∉ LI.blocks
            return true
        end
        return id ∈ invariant_stmts 
    end
    return false
end

function invariant_expr(ir, LI, invariant_stmts, stmt)
    invar = true
    # for useref in userefs(stmt)
    #     invar &= invariant(ir, LI, invariant_stmts, useref[])
    # end
    state = Core.Compiler.iterate(Core.Compiler.userefs(stmt))
	while state !== nothing
		useref, next  = state

		invar &= invariant(ir, LI, invariant_stmts, Core.Compiler.getindex(useref))
		
		state = Core.Compiler.iterate(Core.Compiler.userefs(stmt), next)
	end
    return invar
end

function invariant_stmt(ir, loop, invariant_stmts, stmt)
    if stmt isa Expr
        return invariant_expr(ir, loop, invariant_stmts, stmt)
    end
    return invariant(ir, loop, invariant_stmts, stmt)
end

function find_invariant_stmts(ir, LI)
	stmts = Int[]
	for BB in LI.blocks
		for stmt in ir.cfg.blocks[BB].stmts
			# Okay to throw
			if (ir.stmts[stmt][:flag] & IR_FLAG_EFFECT_FREE) != 0
				# Check if stmt is invariant
				if invariant_stmt(ir, LI, stmts, ir.stmts[stmt][:inst])
					push!(stmts, stmt)
				end
			end
		end
	end
	return stmts
end

function insert_preheader!(ir, LI)
	header = LI.header
	preds = ir.cfg.blocks[header].preds
	entering = filter(BB->BB ∉ LI.blocks, preds)

	# split the header
	split = first(ir.cfg.blocks[header].stmts)
	info = allocate_goto_sequence!(ir, [split => 0])

	map!(BB->info.bbchangemap[BB], entering, entering)

	preheader = header
	header = info.bbchangemap[header]

	on_phi_label(i) = i ∈ entering ? preheader : i

	for stmt in ir.cfg.blocks[header].stmts
		inst = ir.stmts[stmt][:inst]
		if inst isa PhiNode
            edges = inst.edges::Vector{Int32}
            for i in 1:length(edges)
                edges[i] = on_phi_label(edges[i])
            end
		else
			continue
		end
	end

	# TODO: should we mutate LI instead?
	blocks = map(BB->info.bbchangemap[BB], LI.blocks)
	latches = map(BB->info.bbchangemap[BB], LI.latches)

	for latch in latches
		cfg_delete_edge!(ir.cfg, latch, preheader)
		cfg_insert_edge!(ir.cfg, latch, header)
		stmt = ir.stmts[last(ir.cfg.blocks[4].stmts)]
		# stmt[:inst] = GotoNode(header)
        Compiler.setindex!(stmt, Compiler.GotoNode(header), :inst)
	end

	Compiler.verify_ir(ir)

	return preheader, LoopInfo(header, latches, blocks)
end

function move_invariant!(ir, preheader, LI)
	insertion_point = last(ir.cfg.blocks[preheader].stmts)
	stmts = find_invariant_stmts(ir, LI)
	inserter = InsertBefore(ir, SSAValue(insertion_point))
	for stmt in stmts
		new_stmt = inserter(NewInstruction(ir.stmts[stmt]))
		# ir.stmts[stmt] = new_stmt
        Core.Compiler.setindex!(
			ir.stmts, new_stmt, stmt)
	end

end

function licm_pass!(ir::IRCode, loops=construct_loopinfo(ir, construct_domtree(ir.cfg.blocks)))
    # TODO: Check for benefit
    # TODO: More than one Loop in the function. `LI` become stale and would need to be recalculated
    # TODO: Processing order, we should proceess innermost to outermost loops,
    for (h, LI) in loops
        # Find stmts that are invariant w.r.t this loop
        preheader, LI = insert_preheader!(ir, LI)
        move_invariant!(ir, preheader, LI)
    end
    ir = Compiler.compact!(ir)
end

# TODO: 
# - https://nbviewer.org/gist/tkf/d4734be24d2694a3afd669f8f50e6b0f/00_notebook.ipynb


end # module Loops
