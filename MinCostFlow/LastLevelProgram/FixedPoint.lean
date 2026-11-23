module

public import MinCostFlow.LastLevelProgram.Choices
public import MinCostFlow.LastLevelProgram.IntegerScale
public import MinCostFlow.LastLevelProgram.Iteration
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Fixed-point stretch bounds for the last level

Use one round per representative edge, within the linear count of
Definition 5.8 (pages 19–20). The weighted stretch bound of Theorem 2.2 (page 7)
controls the weight sum in the rounded form of Lemma 5.5 (page 18).
-/

open MinCostFlow.LSF MinCostFlow.SparseCore

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open scoped BigOperators

/-- The exact round count used by the fixed-point tool is between one
and two rounds per representative edge. Definition 5.8 (pages 19–20)
requires a collection of order the last graph's edge count. -/
theorem lastMWUK_ge_edges (G : MGraph) : G.m ≤ lastMWUK G := by
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    simpa using half_lt_log_add_two 0
  have hm : (0 : ℝ) ≤ (G.m : ℝ) := Nat.cast_nonneg _
  unfold lastMWUK
  apply Nat.le_floor
  nlinarith only [mul_nonneg hm (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]

/-- Use a grid with spacing at most the inverse of twice the update scale. -/
noncomputable def weightPrecision (C : ℝ) (G : MGraph) : ℕ :=
  (2 * integerScale ⌈max 1 C⌉₊ G).size

/-- The integer bit count is the bit count of twice the real scale. -/
theorem weightPrecision_eq_ceil (C : ℝ) (G : MGraph) :
    weightPrecision C G = (⌈2 * roundedScale C G⌉₊ : ℕ).size := by
  unfold weightPrecision roundedScale
  norm_cast
  rw [Nat.ceil_natCast]

/-- Query the tree with the supplied weights and round its stretch estimates. -/
noncomputable def stretchQuery (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (ℓ : ℕ → ℝ) (P : ℕ) (v : ℕ → ℝ) (e : ℕ) : ℝ :=
  roundStretch P (treeStretch G (oracle G (safeLen G ℓ) v) (safeLen G ℓ) e)

/-- Keep the shortest non-loop edge for each endpoint pair, with ties ordered
by edge name. The vertex set consists of the ends of the retained edges. -/
noncomputable def representativeGraph (G : MGraph) (ℓ : ℕ → ℝ) : MGraph :=
  let E := ((nonLoopEdges G).image (edgePairKey G)).image (shortestEdge G ℓ)
  { V := E.biUnion (fun e => {G.tail e, G.head e}), E := E, tail := G.tail, head := G.head }

/-- The rounded last-level collection of Definition 5.8 (pages 19–20).
Restrict each returned tree to the representative edges, then restore
isolated vertices and read each parallel edge through its representative. -/
noncomputable def fixedPointLastLevelTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) : Chain.LastLevelTool where
  build G ℓ := open Classical in
    if (nonLoopEdges G).Nonempty then
      let H := representativeGraph G ℓ
      let P := weightPrecision C H
      let query := stretchQuery oracle H ℓ P
      let v := weights P (roundedScale C H) query
      (H.m, fun j =>
        let T := oracle H (safeLen H ℓ) (v j)
        let F : MGraph := { V := G.V, E := T.E ∩ H.E, tail := G.tail, head := G.head }
        { T := F
          F := { F := F, R := componentRoots G }
          wstr := fun e =>
            if e ∈ nonLoopEdges G then query (v j) (shortestEdge G ℓ (edgePairKey G e))
            else 1 })
    else
      let F : MGraph := { V := G.V, E := ∅, tail := G.tail, head := G.head }
      (1, fun _ => { T := F, F := { F := F, R := G.V }, wstr := fun _ => 1 })
  cost G :=
    if (nonLoopEdges G).Nonempty then
      lastMWUK (representativeGraph G (fun _ => 1)) * (G.m + 1) + 1
    else 1

/-- On a graph with only loops, Definition 5.8 uses one empty forest,
all vertices as roots, and unit stretch on each edge. -/
theorem fixedPointLastLevelTool_loopOnly
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (h : ¬ (nonLoopEdges G).Nonempty) :
    let F : MGraph := { V := G.V, E := ∅, tail := G.tail, head := G.head }
    (fixedPointLastLevelTool oracle C).build G ℓ =
      (1, fun _ => { T := F, F := { F := F, R := G.V }, wstr := fun _ => 1 }) ∧
    (fixedPointLastLevelTool oracle C).cost G = 1 := by
  simp [fixedPointLastLevelTool,h]

/-- The fixed-point iteration on the simple representative subgraph. The LSST
guarantee is used only on the actual rounded weight vectors. -/
theorem stretchQuery_bounds (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (hm : 1 ≤ G.m)
    (hlen : ∀ e ∈ G.E, 0 < ℓ e)
    (hLSST : ∀ j < lastMWUK G,
      let v := weights (weightPrecision C G) (roundedScale C G)
        (stretchQuery oracle G ℓ (weightPrecision C G)) j
      (∀ e ∈ G.E, 1 ≤ v e) →
      (∑ e ∈ G.E, v e) ≤ 2 * G.m →
      IsLSST G (safeLen G ℓ) v (C * (Real.log ((G.n : ℝ) + 2)) ^ 2)
        (oracle G (safeLen G ℓ) v)) :
    let query := stretchQuery oracle G ℓ (weightPrecision C G)
    let v := weights (weightPrecision C G) (roundedScale C G) query
    (∀ j ≤ lastMWUK G, (∀ e ∈ G.E, 1 ≤ v j e) ∧ (∑ e ∈ G.E, v j e) ≤ 2 * G.m) ∧
    (∀ j < lastMWUK G, ∀ e ∈ G.E, query (v j) e ≤ roundedScale C G) ∧
    ∀ e ∈ G.E, ∑ j ∈ Finset.range (lastMWUK G), query (v j) e ≤
      4 * roundedScale C G * Real.log (2 * G.m) := by
  let W := lastW C G
  let ρ := roundedScale C G
  let P := weightPrecision C G
  let query := stretchQuery oracle G ℓ P
  have hscale := (roundedScale_bounds C G).1
  have href : 0 < 2 * lastRho C G := mul_pos zero_lt_two (lastRho_pos hm)
  have hρ : 0 < ρ := href.trans_le hscale
  have hW : 0 < W := lastW_pos C G
  have hm' : (0 : ℝ) < G.m := by exact_mod_cast hm
  have hP : 2 * ρ ≤ (2 : ℝ)^P := by
    have hsize : (⌈2 * ρ⌉₊ : ℕ) < 2 ^ P := by
      rw [show P = weightPrecision C G from rfl, weightPrecision_eq_ceil]
      exact Nat.lt_size_self _
    exact (Nat.le_ceil _).trans (by exact_mod_cast hsize.le)
  have hgrid : 1 / (2 : ℝ)^P ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hraw (v : ℕ → ℝ) (e : ℕ) : 1 ≤
      treeStretch G (oracle G (safeLen G ℓ) v) (safeLen G ℓ) e := by
    unfold treeStretch walkLength
    apply le_add_of_nonneg_right
    exact div_nonneg (Finset.sum_nonneg fun f _ =>
      mul_nonneg (safeLen_nonneg hlen f) (abs_nonneg _)) (safeLen_nonneg hlen e)
  have hK : (lastMWUK G : ℝ) * (2 * W / ρ) ≤ Real.log 2 := by
    calc
      _ ≤ (2 * (G.m : ℝ) * Real.log 2) * (2 * W / ρ) :=
        mul_le_mul_of_nonneg_right (lastMWUK_bounds hm).2.2.1 (by positivity)
      _ ≤ (2 * (G.m : ℝ) * Real.log 2) * (2 * W / (2 * lastRho C G)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) href hscale)
          (by positivity)
      _ = _ := by
        dsimp only [lastRho]
        change 2 * (G.m : ℝ) * Real.log 2 * (2 * W / (2 * (2 * W * G.m))) = _
        field_simp [hW.ne', hm'.ne']
  refine iteration_bounds G.E P (lastMWUK G) query hρ hP hK
    (fun j _ e _ => (hraw _ e).trans (roundStretch_bounds P _).1) ?_ ?_ (by positivity)
  · intro j hj hv hmass
    let v := weights P ρ query j
    let raw := treeStretch G (oracle G (safeLen G ℓ) v) (safeLen G ℓ)
    have hsum := (hLSST j hj hv hmass).2.2.2
    have hnorm : G.norm1 v = ∑ e ∈ G.E, v e := by
      exact Finset.sum_congr rfl fun e he => abs_of_nonneg (zero_le_one.trans (hv e he))
    have hγ : C * (Real.log ((G.n : ℝ) + 2)) ^ 2 ≤ W :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    change (∑ e ∈ G.E, v e * query v e) ≤ _
    calc
      _ ≤ ∑ e ∈ G.E, 2 * (v e * raw e) := by
        apply Finset.sum_le_sum
        intro e he
        have hbounds := (roundStretch_bounds P (raw e)).2
        have hraw' := hraw v e
        have hq : query v e ≤ 2 * raw e := by
          change roundStretch P (raw e) ≤ _
          linarith
        calc
          _ ≤ v e * (2 * raw e) := mul_le_mul_of_nonneg_left hq (zero_le_one.trans (hv e he))
          _ = _ := by ring
      _ = 2 * (∑ e ∈ G.E, v e * raw e) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * (C * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v) :=
        mul_le_mul_of_nonneg_left hsum zero_le_two
      _ ≤ 2 * W * ∑ e ∈ G.E, v e := by
        rw [hnorm, mul_assoc (2 : ℝ) W]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hγ
          (Finset.sum_nonneg fun e he => zero_le_one.trans (hv e he))) zero_le_two
  · refine le_trans ?_ hscale
    change 2 * W * (2 * (G.m : ℝ)) ≤ 2 * (2 * W * G.m)
    ring_nf
    exact le_rfl

/-- A nonnegative stretch sequence of the length used by the current
model can be restricted to one round per representative edge. Its
average then increases by at most a factor of two. -/
theorem lastMWUK_prefix_average (G : MGraph) (hm : 1 ≤ G.m)
    (s : ℕ → ℝ) (hs : ∀ j < lastMWUK G, 0 ≤ s j) :
    (∑ j ∈ Finset.range G.m, s j) / (G.m : ℝ) ≤
      2 * ((∑ j ∈ Finset.range (lastMWUK G), s j) / (lastMWUK G : ℝ)) := by
  have hsub : Finset.range G.m ⊆ Finset.range (lastMWUK G) :=
    Finset.range_mono (lastMWUK_ge_edges G)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i hi _ => hs i (Finset.mem_range.mp hi))
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range (lastMWUK G), s j :=
    Finset.sum_nonneg fun j hj => hs j (Finset.mem_range.mp hj)
  have hm' : (0 : ℝ) < (G.m : ℝ) := by exact_mod_cast hm
  have hk' : (0 : ℝ) < (lastMWUK G : ℝ) := by
    exact_mod_cast (show 0 < lastMWUK G from hm.trans (lastMWUK_ge_edges G))
  have hk : (lastMWUK G : ℝ) ≤ 2 * (G.m : ℝ) := by
    exact_mod_cast (lastMWUK_bounds hm).2.2.2
  calc
    _ ≤ (∑ j ∈ Finset.range (lastMWUK G), s j) / (G.m : ℝ) :=
      div_le_div_of_nonneg_right hsum hm'.le
    _ = (2 * ∑ j ∈ Finset.range (lastMWUK G), s j) / (2 * (G.m : ℝ)) := by ring
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_left (mul_nonneg zero_le_two hnonneg) hk' hk

end MinCostFlow.LastLevelProgram
