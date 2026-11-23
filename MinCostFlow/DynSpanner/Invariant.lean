module

public import MinCostFlow.DynSpanner.PrefixWalk

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Invariants of the dynamic spanner algorithm (Lemma 5.6, Claims 5.7 and 5.8)

This file develops the inductive state invariant of Algorithm 6 (`step`, `init`, `update`) over
valid sequences of edge deletions and vertex splits:

* `lenBound` (`3^i * γ_ℓ^{i + 1}`) and `vcongBound` (`3^{(i+1)(i+2)/2} * γ_ℓ^{i(i+1)/2} * γ_c^{i+1} * Δ₀`),
  tightening Claim 5.8 and Claim 5.7 of [chen2022maximum] (Section 5.1) so they hold uniformly for
  all `γ_ℓ, γ_c ≥ 1` and with self-loops counted twice in `MGraph.deg`.
* `diffBatch_spec`: exact validity and spanner state equality for the differential batch
  `uh = uhPref ++ uhDel ++ uhIns` on `st.H`.
* `SnapInv` and `step_inv`: preservation of subgraph invariants, touched-vertex sets `S_level`,
  historical level relationships to `lastRebuild`, valid embeddings (`lemma_5_6`),
  length bounds (`claim_5_8`), and vertex-congestion bounds (`claim_5_7`).
-/

namespace MinCostFlow.DynSpanner

section Bounds

@[expose] public section

/-- Length bound `L_i = 3^i · γ_ℓ^{i + 1}` replacing `2^i · γ_ℓ^{i + 1}` of Claim 5.8
([chen2022maximum] arXiv:2203.00671v2, Section 5.1) so it holds uniformly for all `γ_ℓ ≥ 1`. -/
noncomputable def lenBound (γ_ℓ : ℝ) (i : ℕ) : ℝ :=
  (3 : ℝ) ^ i * γ_ℓ ^ (i + 1)

/-- Vertex-congestion bound `V_i = 3^{(i+1)(i+2)/2} · γ_ℓ^{i(i+1)/2} · γ_c^{i+1} · Δ₀`
replacing Claim 5.7 ([chen2022maximum] arXiv:2203.00671v2, Section 5.1) uniformly for all
`γ_ℓ, γ_c ≥ 1` and handling self-loops in `MGraph.deg`. -/
noncomputable def vcongBound (γ_c γ_ℓ : ℝ) (maxDeg₀ i : ℕ) : ℝ :=
  (3 : ℝ) ^ ((i + 1) * (i + 2) / 2) * γ_ℓ ^ (i * (i + 1) / 2) * γ_c ^ (i + 1) * (maxDeg₀ : ℝ)

theorem one_le_lenBound {γ_ℓ : ℝ} (hγ : 1 ≤ γ_ℓ) (i : ℕ) : 1 ≤ lenBound γ_ℓ i := by
  unfold lenBound
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ γ_ℓ ^ (i + 1) := one_le_pow₀ hγ
  nlinarith

theorem lenBound_nonneg {γ_ℓ : ℝ} (hγ : 0 ≤ γ_ℓ) (i : ℕ) : 0 ≤ lenBound γ_ℓ i := by
  unfold lenBound; positivity

theorem lenBound_mono {γ_ℓ : ℝ} (hγ : 1 ≤ γ_ℓ) {i j : ℕ} (hij : i ≤ j) :
    lenBound γ_ℓ i ≤ lenBound γ_ℓ j := by
  unfold lenBound
  have h1 : (3 : ℝ) ^ i ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hij
  have h2 : γ_ℓ ^ (i + 1) ≤ γ_ℓ ^ (j + 1) := pow_le_pow_right₀ hγ (by omega)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem lenBound_step {γ_ℓ : ℝ} (hγ : 1 ≤ γ_ℓ) (i : ℕ) :
    lenBound γ_ℓ i + γ_ℓ * (lenBound γ_ℓ i + 1) ≤ lenBound γ_ℓ (i + 1) := by
  have h1 : 1 ≤ lenBound γ_ℓ i := one_le_lenBound hγ i
  have hL : lenBound γ_ℓ i ≤ γ_ℓ * lenBound γ_ℓ i :=
    le_mul_of_one_le_left (by linarith) hγ
  have hR : γ_ℓ * (lenBound γ_ℓ i + 1) ≤ 2 * (γ_ℓ * lenBound γ_ℓ i) := by nlinarith
  have h3 : lenBound γ_ℓ i + γ_ℓ * (lenBound γ_ℓ i + 1) ≤ 3 * γ_ℓ * lenBound γ_ℓ i := by
    linarith
  calc lenBound γ_ℓ i + γ_ℓ * (lenBound γ_ℓ i + 1)
      ≤ 3 * γ_ℓ * lenBound γ_ℓ i := h3
    _ = lenBound γ_ℓ (i + 1) := by
        unfold lenBound
        ring

theorem vcongBound_nonneg {γ_c γ_ℓ : ℝ} (hc : 0 ≤ γ_c) (hl : 0 ≤ γ_ℓ) (maxDeg₀ i : ℕ) :
    0 ≤ vcongBound γ_c γ_ℓ maxDeg₀ i := by
  unfold vcongBound; positivity

theorem vcongBound_mono {γ_c γ_ℓ : ℝ} (hc : 1 ≤ γ_c) (hl : 1 ≤ γ_ℓ) (maxDeg₀ : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    vcongBound γ_c γ_ℓ maxDeg₀ i ≤ vcongBound γ_c γ_ℓ maxDeg₀ j := by
  unfold vcongBound
  have htri1 : (i + 1) * (i + 2) / 2 ≤ (j + 1) * (j + 2) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
  have htri2 : i * (i + 1) / 2 ≤ j * (j + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul hij (by omega))
  have h3 : (3 : ℝ) ^ ((i + 1) * (i + 2) / 2) ≤ (3 : ℝ) ^ ((j + 1) * (j + 2) / 2) :=
    pow_le_pow_right₀ (by norm_num) htri1
  have hl' : γ_ℓ ^ (i * (i + 1) / 2) ≤ γ_ℓ ^ (j * (j + 1) / 2) :=
    pow_le_pow_right₀ hl htri2
  have hc' : γ_c ^ (i + 1) ≤ γ_c ^ (j + 1) :=
    pow_le_pow_right₀ hc (by omega)
  have hp1 : (3 : ℝ) ^ ((i + 1) * (i + 2) / 2) * γ_ℓ ^ (i * (i + 1) / 2) ≤
      (3 : ℝ) ^ ((j + 1) * (j + 2) / 2) * γ_ℓ ^ (j * (j + 1) / 2) :=
    mul_le_mul h3 hl' (by positivity) (by positivity)
  have hp2 := mul_le_mul hp1 hc' (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right hp2 (Nat.cast_nonneg _)

theorem vcongBound_zero {γ_c γ_ℓ : ℝ} (hc : 0 ≤ γ_c) (maxDeg₀ : ℕ) :
    2 * γ_c * (maxDeg₀ : ℝ) ≤ vcongBound γ_c γ_ℓ maxDeg₀ 0 := by
  unfold vcongBound
  simp only [Nat.zero_add, mul_one, pow_one, Nat.zero_div, pow_zero]
  nlinarith [show (0 : ℝ) ≤ γ_c * (maxDeg₀ : ℝ) by positivity]

private theorem tri_add (i : ℕ) :
    (i + 1) * (i + 2) / 2 + (i + 2) = (i + 2) * (i + 3) / 2 := by
  have heq : (i + 2) * (i + 3) = (i + 1) * (i + 2) + 2 * (i + 2) := by ring
  rw [heq, Nat.add_mul_div_left _ _ (by norm_num)]

private theorem tri_add_zero (i : ℕ) :
    i * (i + 1) / 2 + (i + 1) = (i + 1) * (i + 2) / 2 := by
  have heq : (i + 1) * (i + 2) = i * (i + 1) + 2 * (i + 1) := by ring
  rw [heq, Nat.add_mul_div_left _ _ (by norm_num)]

theorem vcongBound_step {γ_c γ_ℓ : ℝ} (hc : 1 ≤ γ_c) (hl : 1 ≤ γ_ℓ) (maxDeg₀ i : ℕ) :
    vcongBound γ_c γ_ℓ maxDeg₀ i +
      γ_c * (lenBound γ_ℓ i + 1) *
        (vcongBound γ_c γ_ℓ maxDeg₀ i + 2 * vcongBound γ_c γ_ℓ maxDeg₀ i) ≤
      vcongBound γ_c γ_ℓ maxDeg₀ (i + 1) := by
  have h1 : 1 ≤ lenBound γ_ℓ i := one_le_lenBound hl i
  have hV : 0 ≤ vcongBound γ_c γ_ℓ maxDeg₀ i := vcongBound_nonneg (by linarith) (by linarith) _ _
  have hlen2 : lenBound γ_ℓ i + 1 ≤ 2 * lenBound γ_ℓ i := by linarith
  have hcl : 1 ≤ γ_c * lenBound γ_ℓ i := one_le_mul_of_one_le_of_one_le hc h1
  have h7 : vcongBound γ_c γ_ℓ maxDeg₀ i +
      γ_c * (lenBound γ_ℓ i + 1) * (vcongBound γ_c γ_ℓ maxDeg₀ i + 2 * vcongBound γ_c γ_ℓ maxDeg₀ i) ≤
      9 * γ_c * lenBound γ_ℓ i * vcongBound γ_c γ_ℓ maxDeg₀ i := by
    have ha : vcongBound γ_c γ_ℓ maxDeg₀ i ≤ γ_c * lenBound γ_ℓ i * vcongBound γ_c γ_ℓ maxDeg₀ i :=
      le_mul_of_one_le_left hV hcl
    have hb : γ_c * (lenBound γ_ℓ i + 1) * (3 * vcongBound γ_c γ_ℓ maxDeg₀ i) ≤
        γ_c * (2 * lenBound γ_ℓ i) * (3 * vcongBound γ_c γ_ℓ maxDeg₀ i) := by
      gcongr
    linarith
  calc vcongBound γ_c γ_ℓ maxDeg₀ i +
        γ_c * (lenBound γ_ℓ i + 1) *
          (vcongBound γ_c γ_ℓ maxDeg₀ i + 2 * vcongBound γ_c γ_ℓ maxDeg₀ i)
      ≤ 9 * γ_c * lenBound γ_ℓ i * vcongBound γ_c γ_ℓ maxDeg₀ i := h7
    _ = vcongBound γ_c γ_ℓ maxDeg₀ (i + 1) := by
        unfold vcongBound lenBound
        have he1 : (3 : ℝ) ^ ((i + 1) * (i + 2) / 2) * (3 : ℝ) ^ (i + 2) =
            (3 : ℝ) ^ ((i + 2) * (i + 3) / 2) := by
          rw [← pow_add, tri_add i]
        have he2 : γ_ℓ ^ (i * (i + 1) / 2) * γ_ℓ ^ (i + 1) =
            γ_ℓ ^ ((i + 1) * (i + 2) / 2) := by
          rw [← pow_add, tri_add_zero i]
        have he3 : γ_c ^ (i + 1) * γ_c = γ_c ^ (i + 2) := by
          rw [← pow_succ]
        calc 9 * γ_c * ((3 : ℝ) ^ i * γ_ℓ ^ (i + 1)) *
              ((3 : ℝ) ^ ((i + 1) * (i + 2) / 2) * γ_ℓ ^ (i * (i + 1) / 2) * γ_c ^ (i + 1) * (maxDeg₀ : ℝ))
            = ((3 : ℝ) ^ ((i + 1) * (i + 2) / 2) * (3 : ℝ) ^ (i + 2)) *
              (γ_ℓ ^ (i * (i + 1) / 2) * γ_ℓ ^ (i + 1)) *
              (γ_c ^ (i + 1) * γ_c) * (maxDeg₀ : ℝ) := by ring
          _ = (3 : ℝ) ^ ((i + 2) * (i + 3) / 2) * γ_ℓ ^ ((i + 1) * (i + 2) / 2) *
              γ_c ^ (i + 2) * (maxDeg₀ : ℝ) := by rw [he1, he2, he3]

end

end Bounds

section TraceHelpers

@[expose] public section

/-- State produced by running `init` and then `step` over the first `k` updates of `us`. -/
def runState {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) : ℕ → DynSpannerState L
  | 0 => (init G₀ L q sparsify).state
  | k + 1 =>
    match us[k]? with
    | some u => (step (runState G₀ q sparsify us k) u sparsify).state
    | none => runState G₀ q sparsify us k

/-- Step output produced at the `(k + 1)`-st update (`us[k]`) starting from `runState ... k`. -/
def runStepOut {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) (k : ℕ) : StepOut L :=
  match us[k]? with
  | some u => step (runState G₀ q sparsify us k) u sparsify
  | none => ⟨runState G₀ q sparsify us k, [], ∅, 0⟩

theorem take_succ_of_getElem? {α : Type*} {xs : List α} {k : ℕ} {x : α} (h : xs[k]? = some x) :
    xs.take (k + 1) = xs.take k ++ [x] := by
  rw [List.take_add_one, h]
  rfl

theorem lastRebuild_eq_of_not_dvd {q L i k : ℕ} (hnd : ¬ phasePeriod q L i ∣ (k + 1)) :
    lastRebuild q L i (k + 1) = lastRebuild q L i k := by
  unfold lastRebuild
  set B := phasePeriod q L i
  have hdiv : (k + 1) / B = k / B := by
    by_cases hB0 : B = 0
    · simp [hB0]
    · have hB : 0 < B := Nat.pos_of_ne_zero hB0
      have hmod : k % B + 1 < B := by
        have hlt := Nat.mod_lt k hB
        by_contra hge
        have heq : k % B + 1 = B := by omega
        apply hnd
        refine ⟨k / B + 1, ?_⟩
        have hdm := Nat.div_add_mod k B
        nlinarith [hdm, heq]
      have hdm := Nat.div_add_mod k B
      have hk1 : k + 1 = B * (k / B) + (k % B + 1) := by omega
      rw [hk1, Nat.mul_add_div hB, Nat.div_eq_of_lt hmod, add_zero]
  rw [hdiv]

theorem lastRebuild_eq_self_of_dvd {q L i t : ℕ} (hdvd : phasePeriod q L i ∣ t) :
    lastRebuild q L i t = t := by
  unfold lastRebuild
  rw [mul_comm]
  exact Nat.mul_div_cancel' hdvd

theorem lastRebuild_mono_level {q L i j k : ℕ} (hq : 1 ≤ q) (hij : i ≤ j) (hj : j ≤ L) :
    lastRebuild q L i k ≤ lastRebuild q L j k := by
  have hdvd_B : phasePeriod q L j ∣ phasePeriod q L i := phasePeriod_dvd_of_le hij hj
  have hdvd_r : phasePeriod q L j ∣ lastRebuild q L i k := dvd_trans hdvd_B (lastRebuild_dvd q L i k)
  obtain ⟨m, hm⟩ := hdvd_r
  have hle : lastRebuild q L i k ≤ k := lastRebuild_le q L i k
  have hBpos : 0 < phasePeriod q L j := phasePeriod_pos hq L j
  have hm_le : m ≤ k / phasePeriod q L j := by
    rw [Nat.le_div_iff_mul_le hBpos]
    linarith [hm, hle]
  calc lastRebuild q L i k = m * phasePeriod q L j := by linarith [hm]
    _ ≤ (k / phasePeriod q L j) * phasePeriod q L j := Nat.mul_le_mul_right _ hm_le

theorem lastRebuild_idempotent_le {q L i r k : ℕ} (hq : 1 ≤ q) (h1 : lastRebuild q L i k ≤ r)
    (h2 : r ≤ k) : lastRebuild q L i r = lastRebuild q L i k := by
  apply le_antisymm
  · exact Nat.mul_le_mul_right _ (Nat.div_le_div_right h2)
  · have hdvd : phasePeriod q L i ∣ lastRebuild q L i k := lastRebuild_dvd q L i k
    obtain ⟨m, hm⟩ := hdvd
    have hBpos : 0 < phasePeriod q L i := phasePeriod_pos hq L i
    have hm_le : m ≤ r / phasePeriod q L i := by
      rw [Nat.le_div_iff_mul_le hBpos]
      linarith [hm, h1]
    calc lastRebuild q L i k = m * phasePeriod q L i := by linarith [hm]
      _ ≤ (r / phasePeriod q L i) * phasePeriod q L i := Nat.mul_le_mul_right _ hm_le

theorem allTouched_append :
    ∀ (us₁ us₂ : List Update) (G₀ : MGraph),
      allTouched G₀ (us₁ ++ us₂) = allTouched G₀ us₁ ∪ allTouched (G₀.applyBatch us₁) us₂
  | [], us₂, G₀ => by simp [allTouched, MGraph.applyBatch]
  | u :: us₁, us₂, G₀ => by
    simp only [List.cons_append, allTouched]
    rw [allTouched_append us₁ us₂ (G₀.applyUpdate u), Finset.union_assoc]
    rfl

theorem batch_endpoints_mem_V :
    ∀ (us : List Update) (G₀ : MGraph),
      G₀.IsValid → G₀.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      ∀ e₀ ∈ G₀.E,
        (G₀.applyBatch us).tail e₀ ∈ (G₀.applyBatch us).V ∧
        (G₀.applyBatch us).head e₀ ∈ (G₀.applyBatch us).V
  | [], G₀, hV, _, _, e₀, he₀ => by
    simp only [MGraph.applyBatch, List.foldl_nil]
    exact hV e₀ he₀
  | u :: us, G₀, hV, hBV, hds, e₀, he₀ => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ us, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have hV1 := isValid_applyUpdate_of_delOrSplit hV hu hdu
    have he1_ends : (G₀.applyUpdate u).tail e₀ ∈ (G₀.applyUpdate u).V ∧
        (G₀.applyUpdate u).head e₀ ∈ (G₀.applyUpdate u).V := by
      cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => simpa [MGraph.applyUpdate] using hV e₀ he₀
      | split v v' _ _ =>
        simp only [MGraph.applyUpdate, Finset.mem_insert]
        constructor
        · split_ifs
          · left; rfl
          · right; exact (hV e₀ he₀).1
        · split_ifs
          · left; rfl
          · right; exact (hV e₀ he₀).2
    have hV_sub := (batch_delOrSplit_invariants us (G₀.applyUpdate u) hV1 hBV' hds').2.2.1
    simp only [MGraph.applyBatch, List.foldl_cons]
    by_cases he1 : e₀ ∈ (G₀.applyUpdate u).E
    · exact batch_endpoints_mem_V us (G₀.applyUpdate u) hV1 hBV' hds' e₀ he1
    · cases u with
      | insert _ _ _ => exact hdu.elim
      | split _ _ _ _ => exact absurd he₀ (by simpa [MGraph.applyUpdate] using he1)
      | delete d =>
        have hstay : ∀ (us' : List Update) (G' : MGraph),
            G'.BatchIsValid us' → (∀ u' ∈ us', isDelOrSplit u') → e₀ ∉ G'.E →
            (G'.applyBatch us').tail e₀ = G'.tail e₀ ∧
            (G'.applyBatch us').head e₀ = G'.head e₀ := by
          intro us' G' hBV'' hds'' he'
          induction us' generalizing G' with
          | nil => simp [MGraph.applyBatch]
          | cons u' rest ih' =>
            obtain ⟨hu', hrest⟩ := hBV''
            have hdu' := hds'' u' List.mem_cons_self
            have he'' : e₀ ∉ (G'.applyUpdate u').E := fun h => he' (E_applyUpdate_subset hdu' h)
            obtain ⟨ht_r, hh_r⟩ := ih' (G'.applyUpdate u') hrest
              (fun x hx => hds'' x (List.mem_cons_of_mem _ hx)) he''
            simp only [MGraph.applyBatch, List.foldl_cons] at ht_r hh_r ⊢
            rw [ht_r, hh_r]
            cases u' with
            | insert _ _ _ => exact hdu'.elim
            | delete _ => simp [MGraph.applyUpdate]
            | split _ _ St' Sh' =>
              have heSt' : e₀ ∉ St' := fun h => he' (hu'.2.2.1 (Finset.mem_union_left _ h))
              have heSh' : e₀ ∉ Sh' := fun h => he' (hu'.2.2.1 (Finset.mem_union_right _ h))
              simp [MGraph.applyUpdate, heSt', heSh']
        obtain ⟨ht_eq, hh_eq⟩ := hstay us (G₀.applyUpdate (.delete d)) hBV' hds' he1
        simp only [MGraph.applyBatch] at ht_eq hh_eq
        rw [ht_eq, hh_eq]
        exact ⟨hV_sub he1_ends.1, hV_sub he1_ends.2⟩

theorem walkVertices_subset_V_of_batch {us : List Update} {G₀ H₀ Hk : MGraph}
    (hV : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hSub₀ : G₀.IsSubgraph H₀)
    (hEnds : ∀ e ∈ H₀.E, Hk.tail e = (G₀.applyBatch us).tail e ∧
      Hk.head e = (G₀.applyBatch us).head e)
    {w : List (ℕ × Bool)} {a : ℕ}
    (hw : ∀ x ∈ w, x.1 ∈ H₀.E) (ha : a ∈ (G₀.applyBatch us).V) :
    ∀ z ∈ Hk.walkVertices a w, z ∈ (G₀.applyBatch us).V := by
  intro z hz
  simp only [MGraph.walkVertices, List.mem_cons, List.mem_map] at hz
  rcases hz with rfl | ⟨x, hx, rfl⟩
  · exact ha
  · have hxG := hSub₀.2.1 (hw x hx)
    obtain ⟨htHk, hhHk⟩ := hEnds x.1 (hw x hx)
    obtain ⟨htV, hhV⟩ := batch_endpoints_mem_V us G₀ hV hBV hds x.1 hxG
    cases xb : x.2
    · simpa [MGraph.dst, xb, htHk] using htV
    · simpa [MGraph.dst, xb, hhHk] using hhV

end

end TraceHelpers

section DiffBatch

@[expose] public section

private theorem batchIsValid_deletes :
    ∀ (l : List ℕ) (H : MGraph),
      H.IsValid → l.Nodup → (∀ e ∈ l, e ∈ H.E) →
      let H' := H.applyBatch (l.map Update.delete)
      H.BatchIsValid (l.map Update.delete) ∧
      H'.IsValid ∧
      H'.V = H.V ∧
      H'.E = H.E \ l.toFinset ∧
      H'.tail = H.tail ∧
      H'.head = H.head
  | [], H, hV, _, _ => by
    simp [MGraph.BatchIsValid, MGraph.applyBatch, hV]
  | a :: l, H, hV, hnod, hmem => by
    simp only [List.nodup_cons] at hnod
    have haE : a ∈ H.E := hmem a List.mem_cons_self
    have hV1 : (H.applyUpdate (.delete a)).IsValid :=
      isValid_applyUpdate_of_delOrSplit hV haE (by simp [isDelOrSplit])
    have hmem1 : ∀ e ∈ l, e ∈ (H.applyUpdate (.delete a)).E := fun e he => by
      have hne : e ≠ a := fun h => hnod.1 (h ▸ he)
      simp [MGraph.applyUpdate, hne, hmem e (List.mem_cons_of_mem _ he)]
    have ih := batchIsValid_deletes l (H.applyUpdate (.delete a)) hV1 hnod.2 hmem1
    rcases ih with ⟨hBV1, hV', hV_eq, hE_eq, ht_eq, hh_eq⟩
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, MGraph.BatchIsValid] at hV_eq hE_eq ht_eq hh_eq ⊢
    refine ⟨⟨haE, hBV1⟩, hV', by simpa [MGraph.applyUpdate] using hV_eq, ?_,
      by simpa [MGraph.applyUpdate] using ht_eq, by simpa [MGraph.applyUpdate] using hh_eq⟩
    rw [hE_eq]
    simp only [MGraph.applyUpdate, List.toFinset_cons]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
    tauto

private theorem batchIsValid_inserts (G' : MGraph) (hVG' : G'.IsValid) :
    ∀ (l : List ℕ) (H : MGraph),
      H.IsValid → H.V = G'.V → l.Nodup → (∀ e ∈ l, e ∈ G'.E ∧ e ∉ H.E) →
      let bat := l.map fun e => Update.insert e (G'.tail e) (G'.head e)
      let H' := H.applyBatch bat
      H.BatchIsValid bat ∧
      H'.IsValid ∧
      H'.V = H.V ∧
      H'.E = H.E ∪ l.toFinset ∧
      (∀ e ∈ H.E, H'.tail e = H.tail e ∧ H'.head e = H.head e) ∧
      (∀ e ∈ l, H'.tail e = G'.tail e ∧ H'.head e = G'.head e)
  | [], H, hV, _, _, _ => by
    simp [MGraph.BatchIsValid, MGraph.applyBatch, hV]
  | a :: l, H, hV, hHV, hnod, hmem => by
    simp only [List.nodup_cons] at hnod
    obtain ⟨haG', haH⟩ := hmem a List.mem_cons_self
    obtain ⟨hat, hah⟩ := hVG' a haG'
    let u := Update.insert a (G'.tail a) (G'.head a)
    have hu : H.UpdateIsValid u := ⟨haH, hHV ▸ hat, hHV ▸ hah⟩
    have hV1 : (H.applyUpdate u).IsValid := isValid_applyUpdate_any hV hu
    have hHV1 : (H.applyUpdate u).V = G'.V := by simpa [u, MGraph.applyUpdate] using hHV
    have hmem1 : ∀ e ∈ l, e ∈ G'.E ∧ e ∉ (H.applyUpdate u).E := fun e he => by
      have hne : e ≠ a := fun h => hnod.1 (h ▸ he)
      obtain ⟨heG', heH⟩ := hmem e (List.mem_cons_of_mem _ he)
      exact ⟨heG', by simpa [u, MGraph.applyUpdate, Finset.mem_insert, hne] using heH⟩
    have ih := batchIsValid_inserts G' hVG' l (H.applyUpdate u) hV1 hHV1 hnod.2 hmem1
    rcases ih with ⟨hBV1, hV', hV_eq, hE_eq, hend_prev, hend_l⟩
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, MGraph.BatchIsValid] at hV_eq hE_eq hend_prev hend_l ⊢
    refine ⟨⟨hu, hBV1⟩, hV', by simpa [u, MGraph.applyUpdate] using hV_eq, ?_, ?_, ?_⟩
    · rw [hE_eq]
      simp only [u, MGraph.applyUpdate, List.toFinset_cons]
      ext e
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · intro e he
      have hne : e ≠ a := fun h => haH (h ▸ he)
      have he1 : e ∈ (H.applyUpdate u).E := by simp [u, MGraph.applyUpdate, he]
      obtain ⟨ht1, hh1⟩ := hend_prev e he1
      rw [ht1, hh1]
      simp [u, MGraph.applyUpdate, Function.update, hne]
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with heeq | hel
      · subst heeq
        have he1 : e ∈ (H.applyUpdate u).E := by simp [u, MGraph.applyUpdate]
        obtain ⟨ht1, hh1⟩ := hend_prev e he1
        rw [ht1, hh1]
        simp [u, MGraph.applyUpdate]
      · exact hend_l e hel

theorem batchIsValid_append :
    ∀ (H : MGraph) (U₁ U₂ : List Update),
      H.BatchIsValid (U₁ ++ U₂) ↔ H.BatchIsValid U₁ ∧ (H.applyBatch U₁).BatchIsValid U₂
  | _, [], _ => by simp [MGraph.BatchIsValid, MGraph.applyBatch]
  | H, u :: U₁, U₂ => by
    simp only [List.cons_append, MGraph.BatchIsValid]
    rw [batchIsValid_append (H.applyUpdate u) U₁ U₂, and_assoc]
    rfl

theorem applyBatch_append :
    ∀ (H : MGraph) (U₁ U₂ : List Update),
      H.applyBatch (U₁ ++ U₂) = (H.applyBatch U₁).applyBatch U₂
  | H, U₁, U₂ => by simp [MGraph.applyBatch, List.foldl_append]

/-- The differential batch `uh = uhPref ++ uhDel ++ uhIns` on `H` validly transforms `H` into a
graph `H'` on `G'.V` with edge set `H_new_E` agreeing with `G'` on endpoints. -/
theorem diffBatch_spec {G H : MGraph} (hVG : G.IsValid) (hSub : G.IsSubgraph H)
    (hVH_eq : H.V = G.V) {u : Update} (hu : G.UpdateIsValid u) (hds : isDelOrSplit u)
    {H_new_E : Finset ℕ} (hNewSub : H_new_E ⊆ (G.applyUpdate u).E) :
    let G' := G.applyUpdate u
    let uhPref := restrictUpdate u H
    let H_mid := H.applyBatch uhPref
    let uhDel := ((H_mid.E \ H_new_E).sort (· ≤ ·)).map Update.delete
    let uhIns := ((H_new_E \ H_mid.E).sort (· ≤ ·)).map
      fun e => Update.insert e (G'.tail e) (G'.head e)
    let uh := uhPref ++ uhDel ++ uhIns
    let H' := H.applyBatch uh
    H.BatchIsValid uh ∧
    H'.IsValid ∧
    G'.IsSubgraph H' ∧
    H'.V = G'.V ∧
    H'.E = H_new_E ∧
    uhDel.length = (H_mid.E \ H_new_E).card ∧
    uhIns.length = (H_new_E \ H_mid.E).card ∧
    uhPref.length ≤ G.updateEnc u := by
  intro G' uhPref H_mid uhDel uhIns uh H'
  have hVG' : G'.IsValid := isValid_applyUpdate_of_delOrSplit hVG hu hds
  obtain ⟨hBV_pref, hSub_mid, hV_mid, _hE_mid, _hEnds_mid, hLen_pref⟩ :=
    isSubgraph_restrictUpdate hSub hVH_eq hu hds
  have hVH_mid : H_mid.IsValid := by
    intro e he
    obtain ⟨ht, hh⟩ := hSub_mid.2.2 e he
    obtain ⟨htG, hhG⟩ := hVG' e (hSub_mid.2.1 he)
    exact ⟨hV_mid ▸ ht ▸ htG, hV_mid ▸ hh ▸ hhG⟩
  set lDel := (H_mid.E \ H_new_E).sort (· ≤ ·)
  have hDel := batchIsValid_deletes lDel H_mid hVH_mid ((H_mid.E \ H_new_E).sort_nodup _)
    fun e he => (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp he)).1
  set H_del := H_mid.applyBatch uhDel
  rcases hDel with ⟨hBV_del, hVH_del, hV_del, hE_del, ht_del, hh_del⟩
  have hlDel_fin : lDel.toFinset = H_mid.E \ H_new_E := by
    ext e; simp [lDel]
  have hE_del' : H_del.E = H_mid.E ∩ H_new_E := by
    rw [hE_del, hlDel_fin]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  set lIns := (H_new_E \ H_mid.E).sort (· ≤ ·)
  have hlIns_mem : ∀ e ∈ lIns, e ∈ G'.E ∧ e ∉ H_del.E := fun e he => by
    have hes : e ∈ H_new_E \ H_mid.E := (Finset.mem_sort _).mp he
    rw [Finset.mem_sdiff] at hes
    refine ⟨hNewSub hes.1, ?_⟩
    rw [hE_del']
    simp [hes.2]
  have hIns := batchIsValid_inserts G' hVG' lIns H_del hVH_del (hV_del.trans hV_mid)
    ((H_new_E \ H_mid.E).sort_nodup _) hlIns_mem
  rcases hIns with ⟨hBV_ins, hVH_ins, hV_ins, hE_ins, hend_prev, hend_ins⟩
  have hlIns_fin : lIns.toFinset = H_new_E \ H_mid.E := by
    ext e; simp [lIns]
  have hBV_1 : H.BatchIsValid (uhPref ++ uhDel) :=
    (batchIsValid_append H uhPref uhDel).mpr ⟨hBV_pref, hBV_del⟩
  have hApp_1 : H.applyBatch (uhPref ++ uhDel) = H_del := applyBatch_append H uhPref uhDel
  have hBV_all : H.BatchIsValid uh := by
    simpa [uh, List.append_assoc] using
      (batchIsValid_append H (uhPref ++ uhDel) uhIns).mpr ⟨hBV_1, hApp_1 ▸ hBV_ins⟩
  have hApp_all : H' = H_del.applyBatch uhIns := by
    simp only [H', uh, applyBatch_append, H_del, H_mid]
  have hE_final : H'.E = H_new_E := by
    rw [hApp_all, hE_ins, hE_del', hlIns_fin]
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hSub_final : G'.IsSubgraph H' := by
    refine ⟨?_, ?_, fun e he => ?_⟩
    · rw [hApp_all, hV_ins, hV_del, hV_mid]
    · rw [hE_final]; exact hNewSub
    · rw [hE_final] at he
      rw [hApp_all]
      by_cases heM : e ∈ H_mid.E
      · have heD : e ∈ H_del.E := by rw [hE_del']; exact Finset.mem_inter.mpr ⟨heM, he⟩
        obtain ⟨ht1, hh1⟩ := hend_prev e heD
        rw [ht1, hh1, ht_del, hh_del]
        exact hSub_mid.2.2 e heM
      · have heL : e ∈ lIns := (Finset.mem_sort _).mpr (Finset.mem_sdiff.mpr ⟨he, heM⟩)
        exact hend_ins e heL
  have hEnc : uhPref.length ≤ G.updateEnc u :=
    le_trans hLen_pref (updateEnc_pos G u)
  exact ⟨hBV_all, hApp_all ▸ hVH_ins, hSub_final,
    hSub_final.1.antisymm (by rw [hApp_all, hV_ins, hV_del, hV_mid]),
    hE_final, by simp [uhDel], by simp [uhIns], hEnc⟩

end

end DiffBatch

end MinCostFlow.DynSpanner
