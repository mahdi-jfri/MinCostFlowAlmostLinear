module

public import MinCostFlow.SparseCore.MWU
public import MinCostFlow.LSF.Lemma55With
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General LSF initializers (`LSFInit`, `IsApproxMWUInit`, `LSFInvAny`)

Generalizes the fixed online MWU initializer `initLSFOnline oracle C_lsst` to any per-component,
per-branch LSF initializer `lsfInit : LSFInit` meeting `IsApproxMWUInit` (the hypotheses of
`LSF.lemma_5_5_approx`), together with the threshold-existential dynamic invariant `LSFInvAny`
and the single-branch validity predicate `IsValidLSFInitFor`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

@[expose] public section

/-- A general per-component, per-branch LSF initializer taking `(G₀, ℓ₀, k, j)`. -/
abbrev LSFInit := MGraph → (ℕ → ℝ) → ℕ → ℕ → LSFState

/-- `lsfInit` meets the hypotheses of `lemma_5_5_approx` on every input. -/
def IsApproxMWUInit (lsfInit : LSFInit) (C_lsst α K_σ K_ρ : ℝ) : Prop :=
  ∀ (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ), G₀.IsValid → G₀.V.Nonempty →
    (∀ e ∈ G₀.E, 0 < ℓ₀ e) → 1 ≤ k →
    ∃ (thresh ρ δ : ℝ) (v : ℕ → ℕ → ℝ) (T_raw : ℕ → MGraph) (r₀ : ℕ → ℕ)
      (C_reps : ℕ → Finset ℕ) (π : ℕ → ℕ → ℕ) (W_T : ℕ → Finset (Finset ℕ)),
      10 * (max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)) * (k : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ ρ ∧
      ρ ≤ K_ρ * (max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)) * (k : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ∧
      0 ≤ δ ∧ δ ≤ 1 / (20 * (k : ℝ)) ∧
      (∀ e ∈ G₀.E, v 0 e = 1) ∧ (∀ j ≤ k, ∀ e ∈ G₀.E, 0 < v j e) ∧
      (∀ j < k, ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ (v j) (k : ℝ)
        (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)) ∧
      (∀ j < k, ∀ e ∈ G₀.E,
        (1 - δ) * v j e * Real.exp
            ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)
              thresh).wstr e / ρ) ≤ v (j + 1) e ∧
        v (j + 1) e ≤ (1 + δ) * v j e * Real.exp
            ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)
              thresh).wstr e / ρ)) ∧
      ∀ j < k, lsfInit G₀ ℓ₀ k j =
        initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh

/-- Exact online MWU initialization `initLSFOnline` satisfies `IsApproxMWUInit` with
`α = 1`, `K_σ = 6272 * max 1 C_lsst`, and `K_ρ = 10`. -/
theorem initLSFOnline_isApproxMWUInit
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    IsApproxMWUInit (initLSFOnline oracle C_lsst) C_lsst 1 (6272 * max 1 C_lsst) 10 := by
  classical
  intro G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hK₀_eq : max (6272 * max 1 C_lsst) (max (112 * (1 + 1) * max 1 C_lsst) 2240) =
      mwuK0 C_lsst := by
    have h1 : (1 : ℝ) ≤ max 1 C_lsst := le_max_left _ _
    have h2 : 112 * (1 + 1) * max 1 C_lsst ≤ 6272 * max 1 C_lsst := by linarith
    have h3 : (2240 : ℝ) ≤ 6272 * max 1 C_lsst := by linarith
    exact max_eq_left (max_le h2 h3)
  let ρ := mwuRho C_lsst G₀ k
  let v := mwuWeights oracle C_lsst G₀ ℓ₀ k
  let G_v : ℕ → MGraph := fun j => weightedCopyGraph G₀ (v j)
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let T_raw : ℕ → MGraph := fun j =>
    if G₀.E.Nonempty then oracle (G_v j) ℓ_v (fun _ => 1) else oracle G₀ (fun _ => 1) (fun _ => 1)
  let T₀ : ℕ → MGraph := fun j => projectTree G₀ (v j) (T_raw j)
  let r₀ : ℕ → ℕ := fun _ => pickRoot G₀
  let π : ℕ → ℕ → ℕ := fun j =>
    if G₀.E.Nonempty then congOrder (T₀ j) (congestion (G_v j) (T₀ j) ℓ_v)
    else congOrder (T₀ j) (congestion G₀ (T₀ j) (fun _ => 1))
  let W_T : ℕ → Finset (Finset ℕ) := fun j => pickDecomp G₀ (T₀ j) (r₀ j) (k : ℝ)
  let thresh := wstrThresh C_lsst G₀.n (k : ℝ)
  have hS_eq : ∀ j, initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j)
      (compReps G₀ (r₀ j)) (π j) (W_T j) thresh =
      initLSF oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ) := fun j =>
    (initLSF_eq_initLSFWith oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ)).symm
  refine ⟨thresh, ρ, 0, v, T_raw, r₀, fun j => compReps G₀ (r₀ j), π, W_T,
    by rw [hK₀_eq]; dsimp only [ρ, mwuRho, mwuU]; linarith,
    by rw [hK₀_eq]; dsimp only [ρ, mwuRho, mwuU]; linarith, le_rfl, by positivity,
    fun _ _ => rfl, fun j _ e _ => mwuWeights_pos oracle C_lsst G₀ ℓ₀ k j e,
    fun j _ => validLSFParams_initLSF hLSST hG₀ hV₀ hℓ₀
      (fun e _ => mwuWeights_pos oracle C_lsst G₀ ℓ₀ k j e) hk_real,
    fun j _ e _ => ?_, fun j _ => (hS_eq j).symm⟩
  have hv_def : v (j + 1) e =
      v j e * Real.exp ((initLSF oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ)).wstr e / ρ) := rfl
  rw [hS_eq j]
  simp only [sub_zero, add_zero, one_mul, ← hv_def]
  exact ⟨le_rfl, le_rfl⟩

/-- Canonical threshold witness for an `LSFState` satisfying `LSFInvWith` at bound `K_σ`. -/
noncomputable def lsfThresh (K_σ : ℝ) (ℓ₀ : ℕ → ℝ) (S : LSFState) : ℝ :=
  open Classical in
  if h : ∃ t : ℝ, LSFInvWith t K_σ ℓ₀ S then h.choose else 1

/-- `LSFInvWith` at some valid threshold with worst-case stretch constant `K_σ`. -/
abbrev LSFInvAny (K_σ : ℝ) (ℓ₀ : ℕ → ℝ) (S : LSFState) : Prop :=
  LSFInvWith (lsfThresh K_σ ℓ₀ S) K_σ ℓ₀ S

lemma lsfInvAny_of_with {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (h : LSFInvWith thresh K_σ ℓ₀ S) : LSFInvAny K_σ ℓ₀ S := by
  classical
  have hex : ∃ t : ℝ, LSFInvWith t K_σ ℓ₀ S := ⟨thresh, h⟩
  unfold LSFInvAny lsfThresh
  rw [dite_eq_left hex]
  exact hex.choose_spec

lemma lsfInvWith_mono_K {thresh K₁ K₂ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (h : LSFInvWith thresh K₁ ℓ₀ S) (hle : K₁ ≤ K₂) : LSFInvWith thresh K₂ ℓ₀ S := by
  have hlog_nn : 0 ≤ Real.log ((S.G₀.n : ℝ) + 2) := by
    linarith [half_lt_log_add_two S.G₀.n]
  have hk_nn : 0 ≤ S.k := by linarith [h.hk]
  have hfac_nn : 0 ≤ S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6 := by positivity
  have hmul : K₁ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6 ≤
      K₂ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6 := by
    have := mul_le_mul_of_nonneg_right hle hfac_nn
    linarith [show K₁ * (S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6) =
        K₁ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6 by ring,
      show K₂ * (S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6) =
        K₂ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6 by ring]
  exact
    { hG₀_val := h.hG₀_val
      hG_val := h.hG_val
      hV₀ := h.hV₀
      hk := h.hk
      hℓ₀ := h.hℓ₀
      hT₀ := h.hT₀
      hTV := h.hTV
      hr₀_base := h.hr₀_base
      hR₀_sub := h.hR₀_sub
      hord := h.hord
      hTG₀ := h.hTG₀
      hTp₀ := h.hTp₀
      hpi_br := h.hpi_br
      hT_cur_forest := h.hT_cur_forest
      hT_cur_V := h.hT_cur_V
      hT_cur_E := h.hT_cur_E
      hF_sub_G := h.hF_sub_G
      horig_id := h.horig_id
      horig_split := h.horig_split
      horig_T := h.horig_T
      horig_G_nins := h.horig_G_nins
      hunsplit_F := h.hunsplit_F
      hdisj_iso := h.hdisj_iso
      hGV_eq := h.hGV_eq
      hins_sub := h.hins_sub
      hins_wstr := h.hins_wstr
      horig_del := h.horig_del
      hsurv_edge := h.hsurv_edge
      hwstr_bound := fun e he => (h.hwstr_bound e he).trans hmul
      hthresh_bd := ⟨h.hthresh_bd.1, h.hthresh_bd.2.trans hmul⟩
      hdeg_le := h.hdeg_le
      hb_W := h.hb_W
      hW_props := h.hW_props }

open Classical in
/-- Single-branch validity predicate for an arbitrary `lsfInit` at branch `(k, j)` and effective
stretch constant `C_lsst`. -/
def IsValidLSFInitFor (lsfInit : LSFInit) (C_lsst : ℝ) (k j : ℕ) : Prop :=
  ∀ (G₀ : MGraph) (ℓ₀ : ℕ → ℝ), G₀.IsValid → G₀.V.Nonempty →
    (∀ e ∈ G₀.E, 0 < ℓ₀ e) → 1 ≤ k →
    let S₀ := lsfInit G₀ ℓ₀ k j
    LSFInvAny (mwuK0 C_lsst) ℓ₀ S₀ ∧
    S₀.G₀ = G₀ ∧ S₀.G = G₀ ∧ S₀.k = (k : ℝ) ∧
    S₀.isolatedVerts = ∅ ∧ S₀.insertedEdges = ∅ ∧
    S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E ∧
    (S₀.R.card : ℝ) ≤
      (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        4 * (G₀.E.card : ℝ) / (k : ℝ) ∧
    (S₀.W_init.card : ℝ) ≤
      6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        10 * (G₀.E.card : ℝ) / (k : ℝ)

lemma IsApproxMWUInit.toValidLSFInitFor {lsfInit : LSFInit} {C_lsst α K_σ K_ρ : ℝ}
    (h : IsApproxMWUInit lsfInit C_lsst α K_σ K_ρ) {k j : ℕ} (hj : j < k) :
    IsValidLSFInitFor lsfInit (max C_lsst (K_σ / 6272)) k j := by
  intro G₀ ℓ₀ hG₀ hV₀ hℓ₀ hk
  obtain ⟨thresh, _, _, v, T_raw, r₀, C_reps, π, W_T, _, _, _, _, _, hv_pos, hp, _, hEq⟩ :=
    h G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsp := initLSFWith_spec hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
  have hinv := initLSFWith_inv hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
  have hKle : K_σ ≤ mwuK0 (max C_lsst (K_σ / 6272)) := by
    unfold mwuK0
    have h1 : K_σ / 6272 ≤ max C_lsst (K_σ / 6272) := le_max_right _ _
    have h2 : max C_lsst (K_σ / 6272) ≤ max 1 (max C_lsst (K_σ / 6272)) := le_max_right _ _
    linarith
  rw [hEq j hj]
  exact ⟨lsfInvAny_of_with (lsfInvWith_mono_K hinv hKle), hsp.1, hsp.2.1, hsp.2.2.2.1,
    hsp.2.2.2.2.1, hsp.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma initLSFOnline_isValidLSFInitFor {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst) (k j : ℕ) :
    IsValidLSFInitFor (initLSFOnline oracle C_lsst) C_lsst k j := by
  intro G₀ ℓ₀ hG₀ hV₀ hℓ₀ hk
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hw : ∀ e ∈ G₀.E, 0 < mwuWeights oracle C_lsst G₀ ℓ₀ k j e :=
    fun e _ => mwuWeights_pos oracle C_lsst G₀ ℓ₀ k j e
  have hsp := initLSF_spec hLSST hG₀ hV₀ hℓ₀ hw hk_real
  have hinv := initLSF_inv hLSST hG₀ hV₀ hℓ₀ hw hk_real
  exact ⟨lsfInvAny_of_with hinv, hsp.1, hsp.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end

end MinCostFlow.SparseCore
