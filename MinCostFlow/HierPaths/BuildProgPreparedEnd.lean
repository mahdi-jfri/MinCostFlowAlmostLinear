module

public import MinCostFlow.HierPaths.BuildProgRoundMemory

/-!
# Recovering the core reply area end

The last active reply determines where the new cut index list starts.
Its offsets give the end of the core result. A cut reply adds a mask
and two child-sized output areas.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Args are `[replies, count, childSize]`. Return `mem[replies + count]`, the end of the
prepared child block recorded by `buildGameScanProc`. -/
def buildPreparedEndProc : Stmt :=
  .ret (.load (.bin .add (.reg 0) (.reg 1)))

theorem buildPreparedEndProc_noRand : buildPreparedEndProc.NoRand := by
  simp [buildPreparedEndProc, Stmt.NoRand]

/-- The last child exists, and fits in the same word as its prepared reply. -/
def buildPreparedEndContract (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs) : Contract where
  pre args mem :=
    args = [A.replies,B.jobs.count,B.childSize] ∧ 0 < B.jobs.count ∧
    GameRepliesAt B.jobs B.core B.q A.heap A.replies mem ∧ 3 < 2 ^ w ∧
    A.replies + B.jobs.count + 1 ≤ A.heap ∧ B.prepared A < 2 ^ w ∧
    (B.jobs.graph (B.jobs.count - 1)).n = B.childSize
  post _ mem v mem' := v = B.prepared A ∧ mem' = mem
  cost _ _ := 44

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The prepared-block end is read directly from `replies[count]` in `O(1)` word steps. -/
theorem buildPreparedEndProc_meetsContract {w f : ℕ} {p : Program} {B : BuildRoundData}
    {A : BuildRoundAddrs} (hf : p.procs[f]? = some buildPreparedEndProc) :
    MeetsContract w p f (buildPreparedEndContract w B A) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨rfl,_,hReplies,_,hTable,hEnd,_⟩ := hPre
  have hHeap : A.heap ≤ B.prepared A := B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hOff : A.replies + B.jobs.count < 2 ^ w := by omega
  have hVal : mem (A.replies + B.jobs.count) = B.prepared A := hReplies.1
  refine runs_start_le ?_
  unfold buildPreparedEndProc
  refine runs_ret_le (v := B.prepared A) ?_ ⟨rfl, rfl⟩ ?_
  · simp [Expr.eval, startState, hOff, hVal]
  · simp [buildPreparedEndContract, Expr.size]

end MinCostFlow.HierPaths
