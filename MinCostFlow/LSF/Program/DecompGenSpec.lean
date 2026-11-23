module

public import MinCostFlow.LSF.Program.DecompGenRoot
public import MinCostFlow.LSF.ModelWith
public import MinCostFlow.LSF.Lemma54InitBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# From the properties of Lemma B.7 to `IsTreeDecompSpec`

The data structure asks for `W_T` with `IsTreeDecompSpec` (`LSF/ModelWith.lean`). This is what
`pickDecomp_spec` (`LSF/Lemma54InitBase.lean`) shows for `lemma_B_7` with unit weights and
parameter `k * (hldDepthBound n + 1)`. `isTreeDecompSpec_of_b7Props` does the same step for any
decomposition with `B7Props`, so it applies to the output of a program. When `G₀` has fewer
than two vertices, the empty decomposition works (`isTreeDecompSpec_empty`).
`isTreeDecompSpec_of_good` and `isTreeDecompSpec_zero` put this together with
`b7Props_of_good` and `b7Props_zero`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

/-- The parameter of Lemma B.7 used for `W_T`. -/
noncomputable def decompParam (G₀ : MGraph) (k : ℝ) : ℝ :=
  k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)

lemma decompParam_pos {G₀ : MGraph} {k : ℝ} (hk : 0 < k) : 0 < decompParam G₀ k := by
  have hD1_pos : (0 : ℝ) < ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  exact mul_pos hk hD1_pos

theorem isTreeDecompSpec_of_b7Props {G₀ T₀ : MGraph} {r : ℕ} {k : ℝ} (hk : 0 < k)
    {𝒲 : Finset (Finset ℕ)} (h : B7Props G₀ T₀ r (fun _ => (1 : ℝ)) (decompParam G₀ k) 𝒲) :
    IsTreeDecompSpec G₀ T₀ k 𝒲 := by
  classical
  unfold decompParam at h
  obtain ⟨h1, h2, h3, _, h5, h6, _, h8⟩ := h
  refine ⟨h1, h2, h3, h6, ?_, ?_⟩
  · have h1le : (1 : ℝ) ≤ ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hk_le : k ≤ k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) :=
      le_mul_of_one_le_right (le_of_lt hk) h1le
    have hdiv : 6 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) ≤
        6 * (G₀.E.card : ℝ) / k :=
      div_le_div_of_nonneg_left (by positivity) hk hk_le
    linarith
  · intro W₀ hW₀
    have hv0 := h8 W₀ hW₀
    have hD_le := hldDepthBound_add_one_le G₀.n
    have hlog_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) :=
      by linarith [half_lt_log_add_two G₀.n]
    have hvol_le : (G₀.vol (W₀ \ boundary 𝒲) : ℝ) ≤
        2 * ∑ e ∈ G₀.E.filter (fun e =>
          (G₀.tail e ∈ W₀ ∧ G₀.tail e ∉ boundary 𝒲) ∨
          (G₀.head e ∈ W₀ ∧ G₀.head e ∉ boundary 𝒲)), (1 : ℝ) := by
      have hnat := vol_le_two_mul_filter_card G₀ (W₀ \ boundary 𝒲)
      have hfil : G₀.E.filter (fun e => G₀.tail e ∈ W₀ \ boundary 𝒲 ∨
            G₀.head e ∈ W₀ \ boundary 𝒲) =
          G₀.E.filter (fun e => (G₀.tail e ∈ W₀ ∧ G₀.tail e ∉ boundary 𝒲) ∨
            (G₀.head e ∈ W₀ ∧ G₀.head e ∉ boundary 𝒲)) := by
        apply Finset.filter_congr
        intro e _
        simp only [Finset.mem_sdiff]
      rw [hfil] at hnat
      have hcast : (G₀.vol (W₀ \ boundary 𝒲) : ℝ) ≤
          2 * ((G₀.E.filter (fun e => (G₀.tail e ∈ W₀ ∧ G₀.tail e ∉ boundary 𝒲) ∨
            (G₀.head e ∈ W₀ ∧ G₀.head e ∉ boundary 𝒲))).card : ℝ) := by
        exact_mod_cast hnat
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hcast
    have h40_bound : 2 * (40 * (∑ _e ∈ G₀.E, (1 : ℝ)) * (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) /
        (G₀.E.card : ℝ)) ≤ 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      by_cases hE : G₀.E.card = 0
      · rw [hE, Nat.cast_zero, div_zero, mul_zero]
        positivity
      · have hm_ne : (G₀.E.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hE
        calc 2 * (40 * (G₀.E.card : ℝ) * (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) /
              (G₀.E.card : ℝ))
            = 80 * k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by field_simp [hm_ne]; ring
          _ ≤ 80 * k * (28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
              mul_le_mul_of_nonneg_left hD_le (by positivity)
          _ = 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
    exact hvol_le.trans ((mul_le_mul_of_nonneg_left hv0 zero_le_two).trans h40_bound)

lemma edges_empty_of_card_le_one' {T : MGraph} (hT : T.IsForest) (hV : T.V.card ≤ 1) :
    T.E = ∅ := by
  by_contra hne
  have hne' : T.E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨e, he⟩ := hne'
  have huv := hT.1 e he
  have hne_end := isForest_no_selfLoop hT he
  exact hne_end (Finset.card_le_one.mp hV _ huv.1 _ huv.2)

/-- With fewer than two vertices, the tree has no edges, and the empty decomposition works. -/
theorem isTreeDecompSpec_empty {G₀ T₀ : MGraph} {r : ℕ} (hT₀ : IsRootedTree T₀ r)
    (hTV : T₀.V = G₀.V) (hV2 : ¬ 2 ≤ G₀.V.card) {k : ℝ} (hk : 0 < k) :
    IsTreeDecompSpec G₀ T₀ k ∅ := by
  classical
  have hV1 : T₀.V.card ≤ 1 := by rw [hTV]; omega
  have hTE : T₀.E = ∅ := edges_empty_of_card_le_one' hT₀.isForest hV1
  have hB : boundary (∅ : Finset (Finset ℕ)) = ∅ := by
    ext v
    simp only [mem_boundary_iff, Finset.notMem_empty, false_and, exists_false]
  refine ⟨fun _ h => absurd h (Finset.notMem_empty _),
    fun _ h => absurd h (Finset.notMem_empty _), ?_, ?_, ?_,
    fun _ h => absurd h (Finset.notMem_empty _)⟩
  · simp [hTE]
  · rw [hB, Finset.card_empty, Nat.cast_zero]
    positivity
  · rw [Finset.card_empty, Nat.cast_zero]
    positivity

/-- `W_T` from a decomposition of the root with `GoodDecomp`, for unit weights, when `G₀` has
an edge and at least two vertices. -/
theorem isTreeDecompSpec_of_good {G₀ T₀ : MGraph} {r : ℕ} (hG₀ : G₀.IsValid)
    (hT₀ : IsRootedTree T₀ r) (hTV : T₀.V = G₀.V) (hV2 : 2 ≤ G₀.V.card)
    (hE : G₀.E.Nonempty) {k : ℝ} (hk : 0 < k) {𝒲_r : Finset (Finset ℕ)} {B_r : Finset ℕ}
    (hgood : GoodDecomp T₀ r (decompNu G₀ (fun _ => 1) (decompParam G₀ k))
      (decompTheta G₀ (fun _ => 1) (decompParam G₀ k)) r 𝒲_r B_r) :
    IsTreeDecompSpec G₀ T₀ k
      (finalDecomp G₀ (fun _ => 1) (decompParam G₀ k) T₀ r 𝒲_r B_r) := by
  have hpos : 0 < ∑ e ∈ G₀.E, (fun _ => (1 : ℝ)) e := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_pos.mpr hE
  exact isTreeDecompSpec_of_b7Props hk (b7Props_of_good hG₀ hT₀ hTV hV2 _
    (fun _ _ => zero_le_one) _ (decompParam_pos hk) hpos hgood).1

/-- `W_T = {T₀.V}` works when `G₀` has no edges. -/
theorem isTreeDecompSpec_zero {G₀ T₀ : MGraph} {r : ℕ} (hT₀ : IsRootedTree T₀ r)
    (hE : G₀.E = ∅) {k : ℝ} (hk : 0 < k) :
    IsTreeDecompSpec G₀ T₀ k {T₀.V} :=
  isTreeDecompSpec_of_b7Props hk (b7Props_zero hT₀ _ (fun _ _ => zero_le_one) _
    (decompParam_pos hk) (by simp [hE]))

end MinCostFlow.LSF.Program.DecompGen
