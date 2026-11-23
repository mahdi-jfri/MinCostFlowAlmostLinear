module

public import MinCostFlow.MinRatio.SolverLevelLayout
public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopDefs
import Mathlib.Tactic

/-!
# The meta-disjointness clause after Branch B (`WireChainCoreBranchBMetaDisjKFBL`)

The post of the chain core states `SolverLevelMetaDisjAt vCap eCap tok' out.mem`: the graph and
length blocks of the `d` plain levels do not overlap. Branch B keeps the levels below `firstReb`
in place and rebuilds the levels from `firstReb` on, in fresh memory at or above a heap pointer.

The kept levels are disjoint by the same fact at the start, and their blocks lie below the heap
pointer. The rebuilt levels need the order in which the rebuild allocates its blocks: the graph
block of each level comes before its length block, and the length block of a level comes before
the graph block of every later level. This order is the proposition `BranchBRebuiltOrdKFBL`.
The theorem `ordRebuildSuffixProgramKFBLStore_runs_ord` gives it. The result used later is
`branchB_metaDisj` (with the layout of Branch B).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program SparseCore.Program

/-- The order of the blocks that the rebuild of Branch B allocates in `mem`:
for each rebuilt level `fr ≤ j < d`, the graph block starts at or above `heap` and ends before
the length block of `j`, and the length block of a rebuilt level `j₁` ends before the graph
block of each later level `j₂`. The pointers are in the `levelMeta` table at `lm`. -/
@[expose] def BranchBRebuiltOrdKFBL (lm d fr heap vCap eCap L : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ j, fr ≤ j → j < d →
    heap ≤ mem (lm + d + j) ∧ mem (lm + d + j) + dynGraphSize vCap eCap ≤ mem (lm + j)) ∧
  (∀ j₁ j₂, fr ≤ j₁ → j₁ < j₂ → j₂ < d →
    mem (lm + j₁) + eCap * L ≤ mem (lm + d + j₂))

/-- The kept levels `j < fr` have the pointers of `mem0`, whose blocks end at or below `heap`,
and the rebuilt levels are in the order `BranchBRebuiltOrdKFBL`. Then the blocks of `mem'` are
pairwise disjoint. With `fr = 0` every level is rebuilt, and the order alone gives the claim
(`SolverLevelMetaDisjAt.of_monotone_blocks`). Otherwise the cut is at `fr - 1`
(`SolverLevelMetaDisjAt.of_prefix_and_suffix`). -/
theorem solverLevelMetaDisjAt_of_kept_rebuilt {cfg : Alg2Config} {L vCap eCap fr heap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem0 mem' : ℕ → ℕ}
    (hOld : SolverLevelMetaDisjAt vCap eCap tok mem0)
    (htab : tok'.table = tok.table)
    (hKeep : ∀ j < fr, j < cfg.P.d →
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) ∧
      mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (hLow : ∀ j < fr, j < cfg.P.d →
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L ≤ heap ∧
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        heap)
    (hOrd : BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d fr heap vCap
      eCap L mem') :
    SolverLevelMetaDisjAt vCap eCap tok' mem' := by
  rcases Nat.eq_zero_or_pos fr with h0 | hpos
  · subst h0
    have h := SolverLevelMetaDisjAt.of_monotone_blocks (tok := tok) (L := L)
      (fun j hj => (hOrd.1 j (Nat.zero_le j) hj).2)
      (fun j₁ _ j₂ hj₂ hlt => hOrd.2 j₁ j₂ (Nat.zero_le j₁) hlt hj₂)
    exact h.of_agree htab (fun _ _ => rfl)
  · exact SolverLevelMetaDisjAt.of_prefix_and_suffix (cut := fr - 1) (heap := heap) hOld htab
      (fun j hj hjd => hKeep j (by omega) hjd) (fun j hj hjd => hLow j (by omega) hjd)
      (fun j hj hjd => hOrd.1 j (by omega) hjd)
      (fun j₁ j₂ hj₁ hlt hj₂ => hOrd.2 j₁ j₂ (by omega) hlt hj₂)

/-- **The meta-disjointness clause after Branch B.** In the layout of Branch B (`BranchBStatic` with
the graph and length blocks of the start state at `levelMeta`), the old blocks end at or below the
select base `A.selBase`. The levels `j < fr` keep their pointers, and the rebuilt levels are in the
order `BranchBRebuiltOrdKFBL` at or above `A.selBase`. Then the exit memory `mem'` meets
`SolverLevelMetaDisjAt` for the new token `tok'`, which has the table of `tok`. -/
theorem branchB_metaDisj {cfg : Alg2Config} {L vCap eCap fr : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem0 mem' : ℕ → ℕ}
    {handle table handleBase branchBase lvlMTable rcBase ucBase selBase : ℕ}
    {coreH : ℕ → ℕ}
    (S : BranchBStatic cfg.P.d L handle table handleBase branchBase lvlMTable
      (solverLevelMetaAddr tok.table cfg.P.d) rcBase ucBase selBase (fun _ => vCap)
      (fun _ => eCap) (fun j => mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
      (fun j => mem0 (solverLevelMetaAddr tok.table cfg.P.d + j)) coreH)
    (hOld : SolverLevelMetaDisjAt vCap eCap tok mem0)
    (htab : tok'.table = tok.table)
    (hKeep : ∀ j < fr, j < cfg.P.d →
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) ∧
      mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (hOrd : BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d fr selBase
      vCap eCap L mem') :
    SolverLevelMetaDisjAt vCap eCap tok' mem' :=
  solverLevelMetaDisjAt_of_kept_rebuilt hOld htab hKeep
    (fun j _ hjd => ⟨S.lLt j hjd, S.gLt j hjd⟩) hOrd

end MinCostFlow.MinRatio
