module

public import MinCostFlow.SparseCore.Program.LSFWindowLSST
public import MinCostFlow.LSF.Lemma55With
public import MinCostFlow.LSF.Program.Lemma55Program
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fallback Approximate-MWU Initializer (`LSFWindowFallback`)

Defines `fallbackLSFInit`, a deterministic noncomputable LSF initializer on `(G₀, ℓ₀, k)` built
from `exists_lsst_of_wgraph_spec` (`LSFWindowLSST`) using exact multiplicative weight updates
(`δ = 0`), `thresh = defaultThreshNat K_AN G₀.n k`, and `ρ = lemma55RhoNat K_AN G₀.n k`.

This fallback is used by `canonicalLSFInit` whenever the input graph, edge lengths, or parameters
lie outside the fixed-point format supported by `lemma55Module`. It shares the exact constants
`(C_lsst = 4 * max K_AN 1 + 5, α = 5 / 4, K_σ = defaultK_sigma K_AN, K_ρ = 40960)` with the
relocated Word-RAM execution path, and depends on `ℓ₀` only through its restriction to `G₀.E`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program

/-! ## Edge-length congruence helpers -/

lemma safeLen_eq_of_eq_on_E {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ}
    (h : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    safeLen G₀ ℓ₁ = safeLen G₀ ℓ₂ := by
  classical
  funext e
  unfold safeLen
  by_cases he : e ∈ G₀.E
  · simp [he, h e he]
  · simp [he]

lemma safeLen_idem (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) :
    safeLen G₀ (safeLen G₀ ℓ₀) = safeLen G₀ ℓ₀ :=
  safeLen_eq_of_eq_on_E fun _ he => safeLen_eq_of_mem ℓ₀ he

lemma initLSFWith_congr_len {G₀ : MGraph} {ℓ₁ ℓ₂ v : ℕ → ℝ} {k : ℝ}
    {T_raw : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ} {π : ℕ → ℕ}
    {W_T : Finset (Finset ℕ)} {thresh : ℝ}
    (h : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    initLSFWith G₀ ℓ₁ v k T_raw r₀ C_reps π W_T thresh =
      initLSFWith G₀ ℓ₂ v k T_raw r₀ C_reps π W_T thresh := by
  unfold initLSFWith
  rw [safeLen_eq_of_eq_on_E h]

private lemma treeStretch_congr_on_E {G T : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ}
    (hTp : ∀ e ∈ G.E, walkEdges (T.forestPath (G.tail e) (G.head e)) ⊆ G.E)
    (h : ∀ e ∈ G.E, ℓ₁ e = ℓ₂ e) {e : ℕ} (he : e ∈ G.E) :
    treeStretch G T ℓ₁ e = treeStretch G T ℓ₂ e := by
  unfold treeStretch walkLength
  rw [h e he]
  congr 2
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [h f (hTp e he hf)]

private lemma congestion_congr_on_E {G T : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ}
    (h : ∀ e ∈ G.E, ℓ₁ e = ℓ₂ e) (f : ℕ) :
    congestion G T ℓ₁ f = congestion G T ℓ₂ f := by
  unfold congestion
  refine Finset.sum_congr rfl fun e he => ?_
  rw [h e he]

lemma validLSFParams_congr_len {C_lsst α thresh K_σ : ℝ} {G₀ : MGraph} (_hG₀ : G₀.IsValid)
    {ℓ₁ ℓ₂ v : ℕ → ℝ} {k : ℝ} {T_raw : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ}
    {π : ℕ → ℕ} {W_T : Finset (Finset ℕ)}
    (h : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e)
    (hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₁ v k T_raw r₀ C_reps π W_T) :
    ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₂ v k T_raw r₀ C_reps π W_T := by
  classical
  have hT_raw' : IsLSST
      (if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
      (if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₂ else fun _ => 1)
      (fun _ => 1) (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw := by
    have hT1 := hp.hT_raw
    by_cases hE : G₀.E.Nonempty
    · simp only [hE, ↓reduceIte] at hT1 ⊢
      have hlen_eq : ∀ e' ∈ (weightedCopyGraph G₀ v).E,
          weightedCopyLen G₀ ℓ₁ e' = weightedCopyLen G₀ ℓ₂ e' := fun e' he' => by
        unfold weightedCopyLen
        exact h _ (weightedCopyGraph_origEdge_mem hE he').1
      refine ⟨hT1.1, hT1.2.1, hT1.2.2.1, ?_⟩
      have hsum_eq : ∑ e' ∈ (weightedCopyGraph G₀ v).E,
            (1 : ℝ) * treeStretch (weightedCopyGraph G₀ v) T_raw (weightedCopyLen G₀ ℓ₂) e' =
          ∑ e' ∈ (weightedCopyGraph G₀ v).E,
            (1 : ℝ) * treeStretch (weightedCopyGraph G₀ v) T_raw (weightedCopyLen G₀ ℓ₁) e' := by
        refine Finset.sum_congr rfl fun e' he' => ?_
        congr 1
        exact (treeStretch_congr_on_E hT1.2.2.1 hlen_eq he').symm
      rw [hsum_eq]
      exact hT1.2.2.2
    · simpa only [hE, ↓reduceIte] using hT1
  have hπ' : IsApproxCongOrder
      (if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
      (projectTree G₀ v T_raw)
      (if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₂ else fun _ => 1) α π := by
    have hπ1 := hp.hπ
    by_cases hE : G₀.E.Nonempty
    · simp only [hE, ↓reduceIte] at hπ1 ⊢
      have hlen_eq : ∀ e' ∈ (weightedCopyGraph G₀ v).E,
          weightedCopyLen G₀ ℓ₁ e' = weightedCopyLen G₀ ℓ₂ e' := fun e' he' => by
        unfold weightedCopyLen
        exact h _ (weightedCopyGraph_origEdge_mem hE he').1
      refine ⟨hπ1.1, hπ1.2.1, fun f hf g hg hle => ?_⟩
      rw [← congestion_congr_on_E hlen_eq f, ← congestion_congr_on_E hlen_eq g]
      exact hπ1.2.2 f hf g hg hle
    · simpa only [hE, ↓reduceIte] using hπ1
  exact ⟨hT_raw', hp.hr₀, hp.hC_reps, hπ', hp.hW_T, hp.hthresh⟩

/-! ## Stretch-only LSST oracle and fallback MWU sequence -/

/-- Canonical noncomputable LSST oracle backed by `exists_lsst_of_wgraph_spec`. -/
noncomputable def fallbackOracle (K_AN : ℝ) (G : MGraph) (ℓ v : ℕ → ℝ) : MGraph :=
  open Classical in
  if h : WGraphLSSTSpec K_AN ∧ G.IsValid ∧ G.V.Nonempty ∧
      (∀ e ∈ G.E, 0 < ℓ e) ∧ (∀ e ∈ G.E, 0 < v e) then
    Classical.choose (exists_lsst_of_wgraph_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else G

lemma fallbackOracle_spec {K_AN : ℝ} (hAN : WGraphLSSTSpec K_AN) :
    HasLSSTSpec (fallbackOracle K_AN) (4 * max K_AN 1 + 5) := by
  classical
  intro G ℓ v hG hV hℓ hv
  have hcond : WGraphLSSTSpec K_AN ∧ G.IsValid ∧ G.V.Nonempty ∧
      (∀ e ∈ G.E, 0 < ℓ e) ∧ (∀ e ∈ G.E, 0 < v e) := ⟨hAN, hG, hV, hℓ, hv⟩
  unfold fallbackOracle
  rw [dite_eq_left hcond]
  exact Classical.choose_spec (exists_lsst_of_wgraph_spec hAN hG hV hℓ hv)

/-- One-step fallback LSF state built from a weight vector `v` and `safeLen G₀ ℓ₀`. -/
noncomputable def fallbackStepState (K_AN : ℝ) (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℕ) : LSFState :=
  open Classical in
  let ℓ := safeLen G₀ ℓ₀
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ
  let T_raw := if G₀.E.Nonempty then fallbackOracle K_AN G_v ℓ_v (fun _ => 1)
    else fallbackOracle K_AN G₀ (fun _ => 1) (fun _ => 1)
  let T₀ := projectTree G₀ v T_raw
  let r₀ := pickRoot G₀
  let π :=
    if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
    else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
  initLSFWith G₀ ℓ v (k : ℝ) T_raw r₀ (compReps G₀ r₀) π (pickDecomp G₀ T₀ r₀ (k : ℝ))
    (defaultThreshNat K_AN G₀.n k : ℝ)

/-- Exact MWU weight sequence for the fallback initializer. -/
noncomputable def fallbackV (K_AN : ℝ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | j + 1 =>
    let v_j := fallbackV K_AN G₀ ℓ₀ k j
    let S_j := fallbackStepState K_AN G₀ ℓ₀ v_j k
    fun e => v_j e * Real.exp (S_j.wstr e / (lemma55RhoNat K_AN G₀.n k : ℝ))

/-- Fallback LSF initializer for inputs outside the fixed-point Word-RAM window. -/
noncomputable def fallbackLSFInit (K_AN : ℝ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j : ℕ) : LSFState :=
  fallbackStepState K_AN G₀ ℓ₀ (fallbackV K_AN G₀ ℓ₀ k j) k

lemma fallbackStepState_eq_of_eq_on_E {K_AN : ℝ} {G₀ : MGraph} {ℓ₁ ℓ₂ v : ℕ → ℝ} {k : ℕ}
    (h : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    fallbackStepState K_AN G₀ ℓ₁ v k = fallbackStepState K_AN G₀ ℓ₂ v k := by
  unfold fallbackStepState
  rw [safeLen_eq_of_eq_on_E h]

lemma fallbackV_eq_of_eq_on_E {K_AN : ℝ} {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {k : ℕ}
    (h : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    ∀ j, fallbackV K_AN G₀ ℓ₁ k j = fallbackV K_AN G₀ ℓ₂ k j
  | 0 => rfl
  | j + 1 => by
    simp only [fallbackV, fallbackV_eq_of_eq_on_E h j, fallbackStepState_eq_of_eq_on_E h]

lemma fallbackLSFInit_eq_of_eq_on_E {K_AN : ℝ} {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {k j : ℕ}
    (h : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    fallbackLSFInit K_AN G₀ ℓ₁ k j = fallbackLSFInit K_AN G₀ ℓ₂ k j := by
  unfold fallbackLSFInit
  rw [fallbackV_eq_of_eq_on_E h j, fallbackStepState_eq_of_eq_on_E h]

private lemma isApproxCongOrder_mono {G T : MGraph} {ℓ : ℕ → ℝ} {α₁ α₂ : ℝ} {π : ℕ → ℕ}
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (hα : α₁ ≤ α₂) (hπ : IsApproxCongOrder G T ℓ α₁ π) :
    IsApproxCongOrder G T ℓ α₂ π := by
  refine ⟨hπ.1, hπ.2.1.trans hα, fun f hf g hg hle => ?_⟩
  exact (hπ.2.2 f hf g hg hle).trans
    (mul_le_mul_of_nonneg_right hα (congestion_nonneg G T hℓ g))

/-- The fallback initializer satisfies the full approximate-MWU witness specification
(with `C_lsst = 4 * max K_AN 1 + 5`, `α = 5 / 4`, `K_σ = defaultK_sigma K_AN`, `K_ρ = 40960`,
and exact step error `δ = 0`). -/
theorem fallbackLSFInit_approxMWU {K_AN : ℝ} (hAN : WGraphLSSTSpec K_AN)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ)
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hk : 1 ≤ k) :
    ∃ (thresh ρ δ : ℝ) (v : ℕ → ℕ → ℝ) (T_raw : ℕ → MGraph) (r₀ : ℕ → ℕ)
      (C_reps : ℕ → Finset ℕ) (π : ℕ → ℕ → ℕ) (W_T : ℕ → Finset (Finset ℕ)),
      10 * (max (defaultK_sigma K_AN : ℝ)
            (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ ρ ∧
      ρ ≤ (40960 : ℝ) * (max (defaultK_sigma K_AN : ℝ)
            (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ∧
      0 ≤ δ ∧ δ ≤ 1 / (20 * (k : ℝ)) ∧
      (∀ e ∈ G₀.E, v 0 e = 1) ∧ (∀ j ≤ k, ∀ e ∈ G₀.E, 0 < v j e) ∧
      (∀ j < k, ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4) thresh (defaultK_sigma K_AN : ℝ)
        G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)) ∧
      (∀ j < k, ∀ e ∈ G₀.E,
        (1 - δ) * v j e * Real.exp
            ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)
              thresh).wstr e / ρ) ≤ v (j + 1) e ∧
        v (j + 1) e ≤ (1 + δ) * v j e * Real.exp
            ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)
              thresh).wstr e / ρ)) ∧
      ∀ j < k, fallbackLSFInit K_AN G₀ ℓ₀ k j =
        initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh := by
  classical
  let ℓ := safeLen G₀ ℓ₀
  have hℓ_eq : ∀ e ∈ G₀.E, ℓ e = ℓ₀ e := fun _ he => safeLen_eq_of_mem ℓ₀ he
  have hℓ_pos : ∀ e ∈ G₀.E, 0 < ℓ e := fun e he => by rw [hℓ_eq e he]; exact hℓ₀ e he
  let v := fallbackV K_AN G₀ ℓ₀ k
  let T_raw : ℕ → MGraph := fun j =>
    if G₀.E.Nonempty then fallbackOracle K_AN (weightedCopyGraph G₀ (v j)) (weightedCopyLen G₀ ℓ) (fun _ => 1)
    else fallbackOracle K_AN G₀ (fun _ => 1) (fun _ => 1)
  let r₀ : ℕ → ℕ := fun _ => pickRoot G₀
  let C_reps : ℕ → Finset ℕ := fun _ => compReps G₀ (pickRoot G₀)
  let π : ℕ → ℕ → ℕ := fun j =>
    let T₀ := projectTree G₀ (v j) (T_raw j)
    if G₀.E.Nonempty then congOrder T₀ (congestion (weightedCopyGraph G₀ (v j)) T₀ (weightedCopyLen G₀ ℓ))
    else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
  let W_T : ℕ → Finset (Finset ℕ) := fun j => pickDecomp G₀ (projectTree G₀ (v j) (T_raw j)) (pickRoot G₀) (k : ℝ)
  let thresh : ℝ := (defaultThreshNat K_AN G₀.n k : ℝ)
  let ρ : ℝ := (lemma55RhoNat K_AN G₀.n k : ℝ)
  have hLSST := fallbackOracle_spec hAN
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hv_pos_all : ∀ j e, 0 < v j e := by
    intro j
    induction j with
    | zero => intro _; exact zero_lt_one
    | succ j ih =>
      intro e
      exact mul_pos (ih e) (Real.exp_pos _)
  obtain ⟨_, hρ_lo, hρ_hi⟩ := lemma55Rho_bounds K_AN G₀.n hk
  have hρ_lo' : 10 * (max (defaultK_sigma K_AN : ℝ)
        (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
      (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ ρ := by
    dsimp only [lemma54K0] at hρ_lo
    linarith
  have hρ_hi' : ρ ≤ (40960 : ℝ) * (max (defaultK_sigma K_AN : ℝ)
        (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
      (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := by
    dsimp only [lemma54K0] at hρ_hi
    linarith
  have hS_eq : ∀ j, fallbackLSFInit K_AN G₀ ℓ₀ k j =
      initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh := fun j => by
    unfold fallbackLSFInit fallbackStepState
    exact initLSFWith_congr_len hℓ_eq
  refine ⟨thresh, ρ, 0, v, T_raw, r₀, C_reps, π, W_T, hρ_lo', hρ_hi', le_rfl, by positivity,
    fun _ _ => rfl, fun j _ e _ => hv_pos_all j e, ?_, ?_, fun j _ => hS_eq j⟩
  · intro j _
    have hp_base := validLSFParams_initLSF hLSST hG₀ hV₀ hℓ_pos (fun e _ => hv_pos_all j e) hk_real
    have hπ_54 : IsApproxCongOrder
        (if G₀.E.Nonempty then weightedCopyGraph G₀ (v j) else G₀)
        (projectTree G₀ (v j) (T_raw j))
        (if G₀.E.Nonempty then weightedCopyLen G₀ ℓ else fun _ => 1) (5 / 4) (π j) := by
      have hπ1 := hp_base.hπ
      dsimp only [T_raw, π] at hπ1 ⊢
      by_cases hE : G₀.E.Nonempty
      · simp only [hE, ↓reduceIte] at hπ1 ⊢
        exact isApproxCongOrder_mono (fun _ he' => weightedCopyLen_pos hE hℓ_pos he')
          (by norm_num) hπ1
      · simp only [hE, ↓reduceIte] at hπ1 ⊢
        exact isApproxCongOrder_mono (fun _ _ => zero_lt_one) (by norm_num) hπ1
    have hth : IsWstrThresh (4 * max K_AN 1 + 5) (5 / 4) G₀.n (k : ℝ) thresh (defaultK_sigma K_AN : ℝ) :=
      defaultThreshNat_isWstrThresh hk_real le_rfl (by linarith)
    exact validLSFParams_congr_len hG₀ hℓ_eq
      ⟨hp_base.hT_raw, hp_base.hr₀, hp_base.hC_reps, hπ_54, hp_base.hW_T, hth⟩
  · intro j _ e _
    have hstep : v (j + 1) e = v j e * Real.exp
        ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)
          thresh).wstr e / ρ) := by
      rw [← hS_eq j]
      rfl
    rw [sub_zero, add_zero, one_mul, hstep]
    exact ⟨le_rfl, le_rfl⟩

end MinCostFlow.SparseCore.Program
