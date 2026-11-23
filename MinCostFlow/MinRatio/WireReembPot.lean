module

public import MinCostFlow.MinRatio.WireReembModel
public import MinCostFlow.MinRatio.WireSelectUpdate
import Mathlib.Tactic

/-!
# The potential that pays the re-embedded lists of the sparse-core program (`WireReembPot`)

The list of re-embedded edges of one step can be much longer than the growth of the tool cost in
that step (`WireReembModel.lean`). So `ReembCostBound` is amortized: a potential of the tool state
pays what the growth of the tool cost does not. For the tool of the sparse-core program,
`sparseCoreProgTool`, the potential is the slack of the machine cost over the model cost, summed
over the branches:
`progReembPot st = Σ_{j < k} (machCost_j - cost_j)`.

The model cost of a branch grows by at least the length of its list (`progReemb_length_le_cost`),
and the machine cost of every branch grows by its share of the growth of the tool cost. So the list
and the new slack are paid by the growth of the tool cost and the old slack.

* `progReembPot_le_cost`: the potential is at most the tool cost. So a fresh tool state (a rebuilt
  level) brings a potential that the growth of `totalRuntime` pays.
* `progReembPot_restart`: a restart raises the potential by at most the growth of the tool cost.
* `reembCostBound_of_progTool`: `ReembCostBound` with `cReemb = 1` for the list of the branch `b`
  of an update, given two model facts for branch `b`: `BranchLazyCovers` of the step and
  `BranchCostLeMach` after the step. `WireReembFacts.lean` proves both on reached states
  (`progTool_branchLazyCovers`, `progTool_branchCostLeMach`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- The potential of a state of the sparse-core program: over the branches, the slack of the
machine cost over the model cost (and `0` on an empty state, whose tool cost is `0`). -/
noncomputable def progReembPot {depth : ℕ} (st : SparseCoreBundleState depth) : ℕ :=
  if st.isNonempty then (Finset.range st.k).sum fun j => (st.trees j).machCost - (st.trees j).cost
  else 0

section Tool

variable {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}

/-- The potential is at most the tool cost: each branch's slack is at most its machine cost. -/
theorem progReembPot_le_cost (st : SparseCoreBundleState depth) :
    progReembPot st ≤ (sparseCoreProgTool lsfInit C_lsst depth impl).cost st := by
  rw [sparseCoreBundleRestartToolMachWith_cost_eq]
  unfold progReembPot
  split_ifs
  · exact Finset.sum_le_sum fun j _ => Nat.sub_le _ _
  · exact le_rfl

/-- Termwise step of the slack: if the machine cost and the model cost both grow, the new slack is
at most the old slack plus the growth of the machine cost. -/
private theorem slack_step {mach cost mach' cost' : ℕ} (hm : mach ≤ mach') (hc : cost ≤ cost') :
    (mach' - cost') + mach ≤ (mach - cost) + mach' := by
  omega

/-- **The restart.** A restart of branch `b` adds `singleBundleRestartCost` to the model cost and
`singleBundleRestartMachCost` to the machine cost of the branch. So the potential grows by at most
the growth of the tool cost. -/
theorem progReembPot_restart (st : SparseCoreBundleState depth) (b : ℕ) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    progReembPot (T.restart st b) + T.cost st ≤ progReembPot st + T.cost (T.restart st b) := by
  intro T
  have hR : T.restart st b =
      if st.isNonempty = true then
        { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
          trees := Function.update st.trees b
            (restartBundleTree depth (fun _ => canonicalSparsify impl) (st.trees b) st.ord) }
      else st :=
    sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst depth _ st b
  by_cases hne : st.isNonempty = true
  · rw [ite_eq_left hne] at hR
    rw [hR]
    change (if st.isNonempty then _ else 0) + T.cost st ≤
      (if st.isNonempty then _ else 0) + T.cost _
    rw [sparseCoreBundleRestartToolMachWith_cost_eq, sparseCoreBundleRestartToolMachWith_cost_eq]
    dsimp only
    simp only [hne, ↓reduceIte]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => slack_step ?_ ?_
    · by_cases hj : j = b
      · subst hj; simp only [Function.update_self]
        change _ ≤ _ + _
        exact Nat.le_add_right _ _
      · simp only [Function.update_of_ne hj, le_refl]
    · by_cases hj : j = b
      · subst hj; simp only [Function.update_self]
        change _ ≤ _ + _
        exact Nat.le_add_right _ _
      · simp only [Function.update_of_ne hj, le_refl]
  · rw [ite_eq_right hne] at hR
    rw [hR, Nat.add_comm]

/-- **`ReembCostBound` for the list of the program.** Let `st'` be the update of a nonempty state
`st`, and `b < k` a branch. Given `BranchLazyCovers` of the step of branch `b` and
`BranchCostLeMach` of branch `b` after the step, the list of branch `b` meets the amortized bound
with `cReemb = 1` and the potential `progReembPot`. The other branches need no hypothesis: their
model and machine costs only grow (`stepBundleTree_cost`, `stepBundleTree_machCost`). -/
theorem reembCostBound_of_progTool (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) {b : ℕ}
    (hb : b < st.k)
    (hLazy : BranchLazyCovers (fun _ => canonicalSparsify impl) (st.trees b) U st.ord ord')
    (hle' : BranchCostLeMach
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.trees b)) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let st' := (T.updateOrd st U ℓ g ord').1
    ReembCostBound (progReemb lsfInit C_lsst depth impl st U ord' b) (T.cost st' - T.cost st) 1
      (progReembPot st) (progReembPot st') := by
  intro T st'
  have hlen := progReemb_length_le_cost (lsfInit := lsfInit) (C_lsst := C_lsst) st hne U ℓ g
    ord' b hLazy
  have hup := progTool_updateOrd_of_nonempty (lsfInit := lsfInit) (C_lsst := C_lsst)
    (impl := impl) st hne U ℓ g ord'
  have hne' : st'.isNonempty = true := by
    change ((T.updateOrd st U ℓ g ord').1).isNonempty = true
    rw [hup]; exact hne
  have hk' : st'.k = st.k := by
    change ((T.updateOrd st U ℓ g ord').1).k = st.k
    rw [hup]
  have htr' : ∀ i, st'.trees i =
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees i) U st.ord ord').state := by
    intro i
    change ((T.updateOrd st U ℓ g ord').1).trees i = _
    rw [hup]
  have hmach : ∀ i, (st.trees i).machCost ≤ (st'.trees i).machCost := by
    intro i
    rw [htr' i, MinCostFlow.SparseCore.stepBundleTree_machCost]
    exact Nat.le_add_right _ _
  have hcost : ∀ i, (st.trees i).cost ≤ (st'.trees i).cost := by
    intro i
    rw [htr' i, MinCostFlow.SparseCore.stepBundleTree_cost]
    exact Nat.le_add_right _ _
  change (st.trees b).cost + _ ≤ (st'.trees b).cost at hlen
  unfold BranchCostLeMach at hle'
  change (st'.trees b).cost ≤ (st'.trees b).machCost at hle'
  -- The sums over the branches.
  have hT : T.cost st = (Finset.range st.k).sum fun j => (st.trees j).machCost :=
    progTool_cost_of_nonempty st hne
  have hT' : T.cost st' = (Finset.range st.k).sum fun j => (st'.trees j).machCost := by
    rw [← hk']; exact progTool_cost_of_nonempty st' hne'
  have hP : progReembPot st =
      (Finset.range st.k).sum fun j => (st.trees j).machCost - (st.trees j).cost := by
    unfold progReembPot; simp [hne]
  have hP' : progReembPot st' =
      (Finset.range st.k).sum fun j => (st'.trees j).machCost - (st'.trees j).cost := by
    unfold progReembPot; simp [hne', hk']
  have hbmem : b ∈ Finset.range st.k := Finset.mem_range.mpr hb
  -- The branch `b` and the rest.
  set len := (progReemb lsfInit C_lsst depth impl st U ord' b).length
  have hrest : ((Finset.range st.k).erase b).sum
        (fun j => ((st'.trees j).machCost - (st'.trees j).cost) + (st.trees j).machCost) ≤
      ((Finset.range st.k).erase b).sum
        (fun j => ((st.trees j).machCost - (st.trees j).cost) + (st'.trees j).machCost) :=
    Finset.sum_le_sum fun j _ => slack_step (hmach j) (hcost j)
  have hbstep : ((st'.trees b).machCost - (st'.trees b).cost) + len + (st.trees b).machCost ≤
      ((st.trees b).machCost - (st.trees b).cost) + (st'.trees b).machCost := by
    have := hmach b
    omega
  have hsum : ((Finset.range st.k).sum fun j =>
        ((st'.trees j).machCost - (st'.trees j).cost) + (st.trees j).machCost) + len ≤
      (Finset.range st.k).sum fun j =>
        ((st.trees j).machCost - (st.trees j).cost) + (st'.trees j).machCost := by
    rw [← Finset.add_sum_erase _ _ hbmem, ← Finset.add_sum_erase _ _ hbmem]
    omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hTle : T.cost st ≤ T.cost st' := by
    rw [hT, hT']; exact Finset.sum_le_sum fun j _ => hmach j
  unfold ReembCostBound
  rw [hP, hP']
  rw [hT, hT'] at hTle ⊢
  omega

end Tool

end MinCostFlow.MinRatio
