module

public import MinCostFlow.HierPaths.BuildProgTags

/-!
# Calling the core in a game round

The scan of active children calls the core on each child's current game graph. The call
leaves the reply at the old heap pointer and reads its tag into a register so the caller
can save the expanding set or use the cut.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Call the core with the level, graph address, ambient size, recursion depth and heap pointer
in registers 0 through 4. Read the new heap pointer into register 5 and the tag into register 6. -/
def buildCoreCall (f : ℕ) : Stmt :=
  .seq (.call 5 f [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4])
    (.assign 6 (.load (.bin .add (.reg 4) (.const 3))))

theorem buildCoreCall_noRand (f : ℕ) : (buildCoreCall f).NoRand := ⟨trivial, trivial⟩

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The core call reads a tag from its reply, retaining the input registers and the
heap guarantees of the core contract. -/
theorem buildCoreCall_triple
    {w K M r q g h saved : ℕ} {G : Graph} {p : Program} {f : ℕ}
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ}
    {mem : ℕ → ℕ}
    (hCore : ProvidesExactCore w K M r core coreCost sC p f)
    (hPre : (CoreExactProcContract w K M r core coreCost sC q G).pre [q, g, M, r, h] mem)
    (hWords : ∀ i ∈ [q, g, M, r, h], i < 2 ^ w) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = q ∧ st.regs 1 = g ∧ st.regs 2 = M ∧
        st.regs 3 = r ∧ st.regs 4 = h ∧ st.regs 12 = saved)
      (buildCoreCall f)
      (normalPost fun st => st.regs 6 = coreTag (core q G) ∧
        st.regs 0 = q ∧ st.regs 1 = g ∧ st.regs 2 = M ∧
        st.regs 3 = r ∧ st.regs 4 = h ∧ st.regs 12 = saved ∧
        (CoreExactProcContract w K M r core coreCost sC q G).post [q, g, M, r, h] mem (st.regs 5) st.mem)
      (fun _ => K * (coreCost q G + G.encode.length + 1) + 12) := by
  intro st ω ⟨hm, hq, hg, hM, hr, hh, hs⟩
  have hSpace : h + sC G.encode.length < 2 ^ w := hPre.2.2
  refine runs_start_le ?_
  unfold buildCoreCall
  refine runs_seq_call_le (hCore q G) (vs := [q, g, M, r, h])
    (by simp [evalArgs, Expr.eval, hq, hg, hM, hr, hh]) hWords (hm ▸ hPre) ?_
  intro v mem' pos' hPost
  obtain ⟨⟨hv₁, hv₂, hf, hz, htriv⟩, _, _, hArgs, hAt, hv⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hArgs
  obtain ⟨rfl, rfl⟩ := hArgs
  have hvw : v < 2 ^ w := hv₂.trans_lt hSpace
  refine runs_assign_le (eval_coreTag (by simpa using hh) hAt (hv ▸ hvw)) ?_ ?_
  · refine ⟨by simp, by simpa using hq, by simpa using hg, by simpa using hM,
      by simpa using hr, by simpa using hh, by simpa using hs, ?_⟩
    simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), Function.update_self]
    exact ⟨⟨hv₁, hv₂, fun i hi => (hf i hi).trans (congrFun hm i), hz, htriv⟩,
      g, h, rfl, hAt, hv⟩
  · simp [CoreExactProcContract, coreHeapContract, heapContract, argsSize, Expr.size]; omega

end MinCostFlow.HierPaths
