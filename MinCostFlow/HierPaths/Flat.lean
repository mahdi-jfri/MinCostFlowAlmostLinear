module

public import MinCostFlow.HierPaths.FlatLoad
public import MinCostFlow.HierPaths.Project
public import MinCostFlow.HierPaths.Params
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lengths and loads of the stored connector walks

The connectors of every depth above the leaves are flattened to the root host
(`HierPaths/FlatWalk.lean`) and then projected to the input graph (`projectWalk`,
`HierPaths/Project.lean`). This file proves the two bounds of flattening:

1. `length_flat_connector_le`: the flattened walk of a connector at depth `t` has at most
   `∏_{k ≤ t} d k` edges, and so does its projection;
2. `walkLoad_flatConnFam_le`: each edge of the input graph occurs at most
   `∑_{t < leafDepth} B² · κ t · ∏_{k < t} ρ k` times in total in all projected connector walks,
   with `B = 2 ^ b`. Only the last family (the connectors of depth `t`) contributes `B²`.

Then `lemma_5_length` and `lemma_5_load` specialize them to the numbers of the hierarchy: every
local bound is `U`, except `H · U` at the root. The length becomes at most `H · U ^ h` and the load
at most `h · B² · H · U ^ h`, for `h ≥ leafDepth`. With the numbers of `HierPaths/Params.lean`
these are `λ = lamOf` and `ξ = xiOf` (`length_le_lamOf`, `load_le_xiOf`).
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

theorem one_lt_groupSize_of_lt_leafDepth (hb : 0 < b) {t : ℕ} (ht : t < leafDepth x b) :
    1 < groupSize x b t := by
  unfold groupSize
  unfold leafDepth at ht
  have h1 : (t + 1) * b ≤ x + b - 1 := (Nat.le_div_iff_mul_le hb).mp ht
  rw [Nat.succ_mul] at h1
  have h2 : t * b < x := by omega
  rw [min_eq_right h2.le]
  exact Nat.one_lt_two_pow (by omega)

theorem branching_le {t : ℕ} (hs : 1 < groupSize x b t) : branching x b t ≤ 2 ^ b := by
  rw [branching_eq hs]; exact min_le_left _ _

/-- **Flattened walks, length.** The flattened walk of a connector at depth `t` has at most
`∏_{k ≤ t} d k` edges. -/
theorem length_flat_connector_le (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ} (hB : H.Bounds x b d ρ κ)
    {t g : ℕ} (hs : 1 < groupSize x b t) (hg : g < numGroups x b t) {c c' : ℕ}
    (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g) (hcc : c < c')
    {q : ℕ × ℕ × List ℕ} (hq : q ∈ H.conn t c c') :
    (flatWalk H x b t g q.1 q.2.2).length ≤ ∏ k ∈ Finset.range (t + 1), d k := by
  have hW := hH.conn_walk t g hs hg c hc c' hc' hcc q hq
  calc _ ≤ q.2.2.length * ∏ k ∈ Finset.range t, d k := length_flatWalk_le hH hB hs hg hW
    _ ≤ d t * ∏ k ∈ Finset.range t, d k :=
        Nat.mul_le_mul_right _ (hB.conn_length t g hs hg c hc c' hc' hcc q hq)
    _ = ∏ k ∈ Finset.range (t + 1), d k := by rw [Finset.prod_range_succ, Nat.mul_comm]

/-- The root walk of a connector is a walk of the root host between its two terminals. -/
theorem flat_connector_isEdgeWalk (hH : H.IsValid x b) {t g : ℕ} (hs : 1 < groupSize x b t)
    (hg : g < numGroups x b t) {c c' : ℕ} (hc : c ∈ childGroups x b t g)
    (hc' : c' ∈ childGroups x b t g) (hcc : c < c') {q : ℕ × ℕ × List ℕ}
    (hq : q ∈ H.conn t c c') :
    IsEdgeWalk (H.host 0 0).edges q.1 q.2.1 (flatWalk H x b t g q.1 q.2.2) :=
  flatWalk_isEdgeWalk hH hs hg (hH.conn_walk t g hs hg c hc c' hc' hcc q hq)

theorem occLoad_flatMap {α : Type*} (l : List α) (f : α → List (ℕ × List ℕ)) (i : ℕ) :
    occLoad (l.flatMap f) i = (l.map fun a => occLoad (f a) i).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    unfold occLoad
    rw [List.map_append, List.sum_append]

/-- The load on the root host of the flattened connectors of one depth `t`. -/
theorem occLoad_flatFam_connFam_le (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ}
    (hB : H.Bounds x b d ρ κ) {t : ℕ} (hs : 1 < groupSize x b t) (i : ℕ) :
    occLoad (flatFam H x b t (connFam H x b t)) i ≤
      (2 ^ b) ^ 2 * κ t * ∏ k ∈ Finset.range t, ρ k := by
  refine (occLoad_flatFam_le hH hB hs (famOK_connFam hH hs)
    (fun a ha i hi => groupLoad_connFam_le hB hs ha hi) i).trans ?_
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  rw [pow_two]
  exact Nat.mul_le_mul (branching_le hs) (branching_le hs)

/-- The load on the root host of all flattened connectors. -/
theorem occLoad_flatConnFam_le (hb : 0 < b) (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ}
    (hB : H.Bounds x b d ρ κ) (i : ℕ) :
    occLoad (flatConnFam H x b) i ≤
      ∑ t ∈ Finset.range (leafDepth x b), (2 ^ b) ^ 2 * κ t * ∏ k ∈ Finset.range t, ρ k := by
  unfold flatConnFam
  rw [occLoad_flatMap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  exact Finset.sum_le_sum fun t ht =>
    occLoad_flatFam_connFam_le hH hB
      (one_lt_groupSize_of_lt_leafDepth hb (Finset.mem_range.mp ht)) i

/-- **Flattened walks, occurrence load.** Each edge of the input graph occurs at most
`∑_{t < leafDepth} B² · κ t · ∏_{k < t} ρ k` times in total in the projected connector walks, when
distinct root host edges carry distinct labels. -/
theorem walkLoad_flatConnFam_le (hb : 0 < b) (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ}
    (hB : H.Bounds x b d ρ κ) {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    (hinj : ∀ j j' e, label j = some e → label j' = some e → j = j') (e : ℕ) :
    walkLoad (projectFamily (H.host 0 0).edges owner label (flatConnFam H x b)) e ≤
      ∑ t ∈ Finset.range (leafDepth x b), (2 ^ b) ^ 2 * κ t * ∏ k ∈ Finset.range t, ρ k :=
  walkLoad_projectFamily_le hinj (occLoad_flatConnFam_le hb hH hB) e

/-! ### The numbers of the hierarchy -/

/-- The local bound at depth `k`: `H · U` at the root and `U` below. -/
def lvlBound (Hc U k : ℕ) : ℕ := if k = 0 then Hc * U else U

theorem one_le_lvlBound {Hc U : ℕ} (hHc : 1 ≤ Hc) (hU : 1 ≤ U) (k : ℕ) :
    1 ≤ lvlBound Hc U k := by
  unfold lvlBound; split_ifs
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact hU

theorem prod_lvlBound (Hc U t : ℕ) :
    ∏ k ∈ Finset.range (t + 1), lvlBound Hc U k = Hc * U ^ (t + 1) := by
  induction t with
  | zero => simp [lvlBound]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih, lvlBound]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [pow_succ _ (t + 1), Nat.mul_assoc]

theorem lvlBound_mul_prod (Hc U t : ℕ) :
    lvlBound Hc U t * ∏ k ∈ Finset.range t, lvlBound Hc U k = Hc * U ^ (t + 1) := by
  rw [Nat.mul_comm, ← Finset.prod_range_succ, prod_lvlBound]

/-- **Flattening length, with the numbers of the hierarchy.** If every local bound is `U ≥ 1`, and
`Hc · U` at the root, a connector at depth `t < h` flattens to at most `Hc · U ^ h` edges. -/
theorem lemma_5_length (hH : H.IsValid x b) {Hc U h : ℕ} (hU : 1 ≤ U)
    (hB : H.Bounds x b (lvlBound Hc U) (lvlBound Hc U) (lvlBound Hc U))
    {t g : ℕ} (ht : t < h) (hs : 1 < groupSize x b t) (hg : g < numGroups x b t) {c c' : ℕ}
    (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g) (hcc : c < c')
    {q : ℕ × ℕ × List ℕ} (hq : q ∈ H.conn t c c') :
    (flatWalk H x b t g q.1 q.2.2).length ≤ Hc * U ^ h := by
  refine (length_flat_connector_le hH hB hs hg hc hc' hcc hq).trans ?_
  rw [prod_lvlBound]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hU ht)

/-- **Flattening load, with the numbers of the hierarchy.** With the same numbers, `h ≥ leafDepth`
and `2 ^ b ≤ B`, each input edge occurs at most `h · B² · Hc · U ^ h` times in total in the
projected connector walks. -/
theorem lemma_5_load (hb : 0 < b) (hH : H.IsValid x b) {Hc U h B : ℕ} (hU : 1 ≤ U)
    (hB : H.Bounds x b (lvlBound Hc U) (lvlBound Hc U) (lvlBound Hc U))
    (hh : leafDepth x b ≤ h) (hBb : 2 ^ b ≤ B) {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    (hinj : ∀ j j' e, label j = some e → label j' = some e → j = j') (e : ℕ) :
    walkLoad (projectFamily (H.host 0 0).edges owner label (flatConnFam H x b)) e ≤
      h * B ^ 2 * (Hc * U ^ h) := by
  refine (walkLoad_flatConnFam_le hb hH hB hinj e).trans ?_
  calc ∑ t ∈ Finset.range (leafDepth x b),
        (2 ^ b) ^ 2 * lvlBound Hc U t * ∏ k ∈ Finset.range t, lvlBound Hc U k
      ≤ ∑ _t ∈ Finset.range (leafDepth x b), B ^ 2 * (Hc * U ^ h) := by
        refine Finset.sum_le_sum fun t ht => ?_
        rw [Nat.mul_assoc, lvlBound_mul_prod]
        exact Nat.mul_le_mul (Nat.pow_le_pow_left hBb 2) (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hU (by have := Finset.mem_range.mp ht; omega)))
    _ = leafDepth x b * (B ^ 2 * (Hc * U ^ h)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ h * B ^ 2 * (Hc * U ^ h) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hh

/-- **The length bound `lemma_5_length`** with `λ = lamOf a d m` of `HierPaths/Params.lean`: local bounds `uOf a m`,
and `hOf d · uOf a m` at the root. -/
theorem length_le_lamOf (hH : H.IsValid x b) {a dd m : ℕ}
    (hB : H.Bounds x b (lvlBound (hOf dd) (uOf a m)) (lvlBound (hOf dd) (uOf a m))
      (lvlBound (hOf dd) (uOf a m)))
    {t g : ℕ} (ht : t < depthOf m) (hs : 1 < groupSize x b t) (hg : g < numGroups x b t)
    {c c' : ℕ} (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g) (hcc : c < c')
    {q : ℕ × ℕ × List ℕ} (hq : q ∈ H.conn t c c') :
    (flatWalk H x b t g q.1 q.2.2).length ≤ lamOf a dd m :=
  lemma_5_length hH (one_le_uOf a m) hB ht hs hg hc hc' hcc hq

/-- **The load bound `lemma_5_load`** with `ξ = xiOf a d m` of `HierPaths/Params.lean`, when
`leafDepth x b ≤ depthOf m` and `2 ^ b ≤ branchOf m`. -/
theorem load_le_xiOf (hb : 0 < b) (hH : H.IsValid x b) {a dd m : ℕ}
    (hB : H.Bounds x b (lvlBound (hOf dd) (uOf a m)) (lvlBound (hOf dd) (uOf a m))
      (lvlBound (hOf dd) (uOf a m)))
    (hh : leafDepth x b ≤ depthOf m) (hBb : 2 ^ b ≤ branchOf m) {owner : ℕ → ℕ}
    {label : ℕ → Option ℕ} (hinj : ∀ j j' e, label j = some e → label j' = some e → j = j')
    (e : ℕ) :
    walkLoad (projectFamily (H.host 0 0).edges owner label (flatConnFam H x b)) e ≤
      xiOf a dd m := by
  refine (lemma_5_load hb hH (one_le_uOf a m) hB hh hBb hinj e).trans (le_of_eq ?_)
  simp only [xiOf, lamOf, vOf, Nat.mul_assoc]

end MinCostFlow.HierPaths
