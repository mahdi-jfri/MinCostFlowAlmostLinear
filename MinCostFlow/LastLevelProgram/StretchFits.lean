module

public import MinCostFlow.LastLevelProgram.StretchFromLength
public import MinCostFlow.LastLevelProgram.RootDistanceModel
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic

/-!
# Signed bounds for rounded stretch arithmetic

An integral positive denominator is at least one. The fixed-point
scale times the largest path-plus-edge numerator therefore bounds the
magnitude of the quotient even after rounding.
-/

public section

namespace MinCostFlow.LastLevelProgram

open Num

/-- A symmetric integer interval fits if its doubled radius is below
the capacity of the block. -/
theorem fits_of_symmetric_bound {h L : ℕ} {x B : ℤ}
    (hl : -B ≤ x) (hu : x ≤ B) (hb : 2*B < (capacity h L : ℤ)) :
    Fits h L x := by
  unfold Fits
  omega

/-- A bound on the sum of path and edge numerators supplies all four
signed bounds required by the upward-rounded stretch computation. -/
theorem stretchArithmeticFits_of_bound {h L P : ℕ} {a d B : ℤ}
    (hd : 0 < d) (hlo : 0 ≤ a+d) (hhi : a+d ≤ B)
    (hcap : 2*(B*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    stretchArithmeticFits h L P a d := by
  let scale := (2 : ℤ)^P
  let q := floorDiv (-(a+d)*scale) d
  have hs : 1 ≤ scale := by
    have hh : 0 < scale := by dsimp [scale]; positivity
    omega
  have hB : 0 ≤ B := hlo.trans hhi
  have hBB : B ≤ B*scale := by
    simpa using mul_le_mul_of_nonneg_left hs hB
  have hx : -(B*scale) ≤ -(a+d)*scale := by
    rw [neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_right hhi (by omega))
  have hx0 : -(a+d)*scale ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
  have hq : -(B*scale) ≤ q ∧ q ≤ 0 := by
    unfold q
    rw [floorDiv_eq_floor]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    constructor
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hdR).2
      have hmult : -(B*scale) * d ≤ -(a+d)*scale := by
        calc
          -(B*scale) * d ≤ -(B*scale) * 1 :=
            mul_le_mul_of_nonpos_left (by omega : 1 ≤ d) (neg_nonpos.mpr (mul_nonneg hB (by omega)))
          _ = -(B*scale) := mul_one _
          _ ≤ _ := hx
      exact_mod_cast hmult
    · apply Int.floor_le_iff.mpr
      have hn : ((-(a+d)*scale : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hx0
      have hz : ((-(a+d)*scale : ℤ) : ℝ) / (d : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hn hdR.le
      simpa using hz.trans_lt (by norm_num : (0 : ℝ) < 1)
  change 2*(B*scale) < (capacity h L : ℤ) at hcap
  change Fits h L (a+d) ∧ Fits h L (-(a+d)) ∧ Fits h L q ∧ Fits h L (-q)
  exact ⟨fits_of_symmetric_bound (by omega) (hhi.trans hBB) hcap,
    fits_of_symmetric_bound (by omega) (by omega) hcap,
    fits_of_symmetric_bound hq.1 (by omega) hcap,
    fits_of_symmetric_bound (by omega) (by omega) hcap⟩


open LSF in
/-- A path to an ancestor is a suffix of the root path, so a nonnegative
edge encoding gives a nondecreasing numerator away from the root. -/
theorem rootDistanceNumerator_le_of_ancestor {T : MGraph} {r u a : ℕ}
    (hT : IsRootedTree T r) (hu : u ∈ T.V) (ha : IsAncestor T r a u)
    (len : ℕ → ℤ) (hn : ∀ e ∈ T.E, 0 ≤ len e) :
    rootDistanceNumerator T r len a ≤ rootDistanceNumerator T r len u := by
  obtain ⟨he,hd⟩ := forestPath_eq_of_isAncestor hT hu ha
  have hwalk := (forestPath_isPath hT.isForest (hT.connected hu (isAncestor_mem hT hu ha))).1
  have hnonneg : 0 ≤ ∑ e ∈ walkEdges (T.forestPath u a), len e := by
    apply Finset.sum_nonneg
    intro e hm
    obtain ⟨x,hx,heq⟩ : ∃ x ∈ T.forestPath u a, x.1 = e := by
      simpa [walkEdges] using hm
    exact heq ▸ hn _ (IsWalk_edges_mem hwalk hx)
  unfold rootDistanceNumerator
  rw [he,walkEdges_append,Finset.sum_union hd]
  omega

open LSF in
/-- A single signed-capacity bound covers both endpoint subtractions,
their sum, and the rounded stretch quotient. -/
theorem treeStretchNumerator_fits {T : MGraph} {r u v : ℕ}
    (hT : IsRootedTree T r) (hu : u ∈ T.V) (hv : v ∈ T.V)
    (len : ℕ → ℤ) (B h L P : ℕ) (d : ℤ)
    (hbound : ∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ))
    (hd : 0 < d) (hdB : d ≤ B)
    (hcap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    let a := rootDistanceNumerator T r len u - rootDistanceNumerator T r len (lca T r u v)
    let b := rootDistanceNumerator T r len v - rootDistanceNumerator T r len (lca T r u v)
    Fits h L a ∧ Fits h L b ∧ Fits h L (a+b) ∧ stretchArithmeticFits h L P (a+b) d := by
  intro a b
  let M := (T.V.card : ℤ)*B
  let R := 2*M+B
  have ht (x : ℕ) (hx : x ∈ T.V) :
      0 ≤ rootDistanceNumerator T r len x ∧ rootDistanceNumerator T r len x ≤ M := by
    obtain ⟨h0,h1⟩ := rootDistanceNumerator_bound hT hx len B hbound
    have hdepth : (depth T r x : ℤ) ≤ T.V.card := by
      exact_mod_cast (depth_lt_card_vertices hT hx).le
    exact ⟨h0,h1.trans (mul_le_mul_of_nonneg_right hdepth (by positivity))⟩
  have hnl : ∀ e ∈ T.E, 0 ≤ len e := fun e he => (hbound e he).1
  have ha0 : 0 ≤ a := sub_nonneg.mpr
    (rootDistanceNumerator_le_of_ancestor hT hu (lca_isAncestor_left hT hu hv) len hnl)
  have hb0 : 0 ≤ b := sub_nonneg.mpr
    (rootDistanceNumerator_le_of_ancestor hT hv (lca_isAncestor_right hT hu hv) len hnl)
  have hz := (ht _ (lca_mem hT hu hv)).1
  have haM : a ≤ M := by dsimp [a]; have he := (ht u hu).2; omega
  have hbM : b ≤ M := by dsimp [b]; have he := (ht v hv).2; omega
  have hcap' : 2*(R*(2 : ℤ)^P) < (capacity h L : ℤ) := by
    simpa only [R,M,mul_assoc] using hcap
  have hR : 0 ≤ R := by dsimp [R,M]; positivity
  have hscale : 1 ≤ (2 : ℤ)^P := by
    have hp : 0 < (2 : ℤ)^P := by positivity
    omega
  have hRs : R ≤ R*(2 : ℤ)^P := by simpa using mul_le_mul_of_nonneg_left hscale hR
  have hc : 2*R < (capacity h L : ℤ) := by omega
  have hab : a+b+d ≤ R := by dsimp [R]; omega
  exact ⟨fits_of_symmetric_bound (by omega) (by omega) hc,
    fits_of_symmetric_bound (by omega) (by omega) hc,
    fits_of_symmetric_bound (by omega) (by omega) hc,
    stretchArithmeticFits_of_bound hd (by omega) hab hcap'⟩
end MinCostFlow.LastLevelProgram
