module

public import MinCostFlow.SparseCore.Program.LSFWindowCanonMem
import MinCostFlow.DynSpanner.Program.CanonicalSparsify
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Canonical LSF Initializer `canonicalLSFInit` (`LSFWindowCanon`)

Defines `CanonicalLSFValid`, `CanonicalLSFGuestRun`, `canonicalLSFInitWithH`, and
`canonicalLSFInit` (`h = 4`), and proves `canonicalLSFInitWithH_approxMWU` and
`canonicalLSFInit_approxMWU` under the stretch-only `[AN19]` hypothesis.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.WideWord MinCostFlow.Num

/-! ## Canonical validity, witnessed guest run, and `canonicalLSFInit` -/

/-- Exact validity predicate under which `canonicalLSFInitWithH` uses the canonical guest run of
`lemma55Module`. -/
def CanonicalLSFValid (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h L_in P_fp : ℕ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) : Prop :=
  FullAN19Spec Q_AN c_AN K_AN ∧
  1 ≤ h ∧ 1 ≤ L_in ∧ h ∣ P_fp ∧ P_fp + 6 ≤ h * L_in ∧ 1 ≤ k ∧
  (∃ q, q + 11 ≤ P_fp ∧ 40 * k ≤ 2 ^ q) ∧
  32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1) ∧
  G₀.IsValid ∧ G₀.V.Nonempty ∧
  (∀ e ∈ G₀.E, ∃ m : ℕ → ℕ, Valid m 0 h L_in ∧ fixVal m 0 h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)

lemma canonicalLSFValid_iff_of_eq_on_E {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {h L_in P_fp : ℕ}
    {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {k : ℕ} (hℓ : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ ℓ₁ k ↔
      CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ ℓ₂ k := by
  unfold CanonicalLSFValid
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun e he => by rw [← hℓ e he]; exact h11 e he⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun e he => by rw [hℓ e he]; exact h11 e he⟩

/-- Bundled witness of the canonical guest run of `lemma55Module` at word size `canonWordBits`. -/
structure CanonicalLSFGuestRun (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h L_in P_fp : ℕ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) where
  endHeap : ℕ
  st' : State
  c : ℕ
  v' : ℕ → ℕ → ℝ
  S₀ : ℕ → LSFState
  x₀ : ℕ → LSFConcrete
  hs : ℕ → ℕ
  T_raw : ℕ → MGraph
  C_reps : ℕ → Finset ℕ
  W_T : ℕ → Finset (Finset ℕ)
  hrun : ∀ ω, Runs (canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k)
    (lemma55Module Q_AN c_AN K_AN h) ω
    (lemma55InitProc 3 (lemma55BaseLsf 0 + lsfIdxInit) 1 h)
    (startState (canonGuestArgs K_AN L_in P_fp G₀ k) (canonGuestMem G₀ ℓ₀ h L_in P_fp) 0)
    (.returned endHeap) st' c
  hheap_ge : canonHeap G₀ L_in k ≤ endHeap
  hheap_le : endHeap ≤ canonHeap G₀ L_in k +
    lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k
      (canonVCap G₀) (canonECap G₀) G₀.n G₀.m
  hz' : ZeroFrom st'.mem endHeap
  hframe : ∀ z < canonHeap G₀ L_in k,
    (z < canonHandlesOut G₀ L_in ∨ canonHandlesOut G₀ L_in + k ≤ z) →
      st'.mem z = canonGuestMem G₀ ℓ₀ h L_in P_fp z
  hv0 : ∀ e ∈ G₀.E, v' 0 e = 1
  hv_pos : ∀ i ≤ k, ∀ e ∈ G₀.E, 0 < v' i e
  hinit : ∀ i < k,
    ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
      (defaultThreshNat K_AN G₀.n k : ℝ) (defaultK_sigma K_AN : ℝ)
      G₀ ℓ₀ (v' i) (k : ℝ) (T_raw i) (S₀ i).r₀ (C_reps i) (S₀ i).π (W_T i) ∧
    S₀ i = initLSFWith G₀ ℓ₀ (v' i) (k : ℝ) (T_raw i) (S₀ i).r₀ (C_reps i) (S₀ i).π (W_T i)
      (defaultThreshNat K_AN G₀.n k : ℝ)
  hv_step : ∀ i < k, ∀ e ∈ G₀.E,
    (1 - 1 / (20 * (k : ℝ))) * v' i e *
        Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k : ℝ)) ≤ v' (i + 1) e ∧
    v' (i + 1) e ≤
      (1 + 1 / (20 * (k : ℝ))) * v' i e *
        Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k : ℝ))
  hrep : ∀ j < k, st'.mem (canonHandlesOut G₀ L_in + j) = hs j ∧
    (LSFRep h).rep (hs j) (S₀ j) (x₀ j) st'.mem ∧
    (x₀ j).vCap = canonVCap G₀ ∧ (x₀ j).eCap = canonECap G₀ ∧
    (x₀ j).L_w = canonLw K_AN L_in G₀.n k ∧
    (x₀ j).n0 = G₀.n ∧ (x₀ j).m0 = G₀.E.card ∧
    ∀ a, (LSFRep h).foot (hs j) (x₀ j) a → canonHeap G₀ L_in k ≤ a ∧ a < endHeap
  hdisj : ∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ →
    ∀ a, (LSFRep h).foot (hs j₁) (x₀ j₁) a → ¬ (LSFRep h).foot (hs j₂) (x₀ j₂) a
  hcost : c ≤ lemma55Cost Q_AN c_AN K_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k G₀.n G₀.m

lemma canonicalLSFGuestRun_exists {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {h L_in P_fp : ℕ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {k : ℕ}
    (hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ ℓ₀ k) :
    Nonempty (CanonicalLSFGuestRun Q_AN c_AN K_AN h L_in P_fp G₀ ℓ₀ k) := by
  rcases hV with ⟨⟨hc, hQ⟩, hh, hLin1, hdiv, hP_Lin, hk, ⟨q, hq_P, hk_q⟩, hm_Lin, hG₀, hV₀, hℓ_rep⟩
  set w' := canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k
  obtain ⟨hw_h, hB_lt, _⟩ := canonWordBits_bounds Q_AN c_AN K_AN h L_in P_fp G₀ k
  have hp0 : (lemma55Module Q_AN c_AN K_AN h).HasAt 0 (lemma55ModuleProcs Q_AN c_AN K_AN 0 h) := by
    intro i hi
    simp only [lemma55Module, Nat.zero_add, List.getElem?_eq_getElem hi]
  have h2P_lt : 2 * P_fp + 9 < 2 ^ w' :=
    lt_trans (Nat.lt_succ_of_le (le_trans (le_max_left _ _) (le_max_right _ _))) hB_lt
  have hHld_lt : 3 * (4 * k * (hldDepthBound G₀.n + 1)) < 2 ^ w' :=
    lt_trans (Nat.lt_succ_of_le (le_trans (le_max_right _ _) (le_max_right _ _))) hB_lt
  have hsp_lt : canonHeap G₀ L_in k +
      lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k
        (canonVCap G₀) (canonECap G₀) G₀.n G₀.m < 2 ^ w' :=
    lt_trans (Nat.lt_succ_of_le (le_max_left _ _)) hB_lt
  obtain ⟨body, hbody, endHeap, st', c, v', S₀, x₀, hs, T_raw, C_reps, W_T,
    hrun0, hge, hle, hz', hfr', hv0', hv_pos', hinit', hv_step', hhnd', hdisj', hc'⟩ :=
    lemma55Init_runs_with_witness (p := lemma55Module Q_AN c_AN K_AN h) (w := w') (q := q)
      (g0Ptr := 0) (lenArr := canonLenArr G₀) (L_in := L_in) (P_fp := P_fp) (k_nat := k)
      (L_w := canonLw K_AN L_in G₀.n k) (vCap := canonVCap G₀) (eCap := canonECap G₀)
      (handlesOut := canonHandlesOut G₀ L_in) (heap := canonHeap G₀ L_in k)
      (vCap0 := canonVCap G₀) (eCap0 := canonECap G₀)
      (G₀ := G₀) (ℓ₀ := ℓ₀) (mem := canonGuestMem G₀ ℓ₀ h L_in P_fp) 0 (fun _ => false)
      hp0 hQ hc hh hw_h hLin1 (canonLw_ge_Lin K_AN L_in G₀.n k) hk hdiv hq_P hk_q hP_Lin hm_Lin
      h2P_lt hHld_lt (canonLw_rho_cap K_AN hh L_in G₀.n k) hG₀ hV₀
      (canonGuestMem_dynGraphAt hG₀ ℓ₀ h L_in P_fp) le_rfl le_rfl (canonECap_pos G₀)
      (canonGuestMem_lengths hLin1 hℓ_rep)
      (by unfold canonHeap canonHandlesOut canonLenArr; omega)
      (by unfold canonHeap canonHandlesOut; omega)
      (by unfold canonHeap; omega)
      (Or.inr (by unfold canonHandlesOut canonLenArr; omega))
      (Or.inr (by unfold canonHandlesOut; omega))
      (canonGuestMem_zeroFrom G₀ ℓ₀ h L_in P_fp k) hsp_lt
  have hbody_eq : body = lemma55InitProc 3 (lemma55BaseLsf 0 + lsfIdxInit) 1 h := by
    have h0 := (lemma55HasAt_split hp0).1
    exact Option.some.inj (hbody.symm.trans h0)
  subst hbody_eq
  have hdet := lemma55Module_isDeterministic Q_AN c_AN K_AN h
  have hnoRand : (lemma55InitProc 3 (lemma55BaseLsf 0 + lsfIdxInit) 1 h).NoRand :=
    lemma55InitProc_noRand _ _ _ _
  refine ⟨⟨endHeap, st', c, v', S₀, x₀, hs, T_raw, C_reps, W_T, ?_,
    hge, hle, hz', hfr', hv0', hv_pos', hinit', hv_step', hhnd', hdisj', hc'⟩⟩
  intro ω
  rcases hrun0 with ⟨fuel, hfuel⟩
  exact ⟨fuel, (exec_noRand hdet fuel hnoRand (ω₂ := fun _ => false)).trans hfuel⟩

/-- Chosen canonical guest run when `CanonicalLSFValid` holds. -/
noncomputable def chosenGuestRun {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {h L_in P_fp : ℕ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {k : ℕ}
    (hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ ℓ₀ k) :
    CanonicalLSFGuestRun Q_AN c_AN K_AN h L_in P_fp G₀ ℓ₀ k :=
  Classical.choice (canonicalLSFGuestRun_exists hV)

/-- General-`h` canonical LSF initializer: uses the witnessed canonical guest run of `lemma55Module`
on valid fixed-point inputs (normalizing `ℓ₀` via `safeLen G₀ ℓ₀` so it depends only on `ℓ₀|_{G₀.E}`),
and falls back to `fallbackLSFInit` otherwise. -/
noncomputable def canonicalLSFInitWithH (h : ℕ) (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (L_in P_fp : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j : ℕ) : LSFState :=
  open Classical in
  let ℓ := safeLen G₀ ℓ₀
  if hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ ℓ k then
    (chosenGuestRun hV).S₀ j
  else
    fallbackLSFInit K_AN G₀ ℓ k j

/-- Canonical LSF initializer at the paper's IPM limb width `h = 4`. -/
noncomputable def canonicalLSFInit (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (L_in P_fp : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j : ℕ) : LSFState :=
  canonicalLSFInitWithH 4 Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j

lemma canonicalLSFInitWithH_eq_of_eq_on_E {h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {L_in P_fp : ℕ} {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {k j : ℕ}
    (hℓ : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₁ k j =
      canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₂ k j := by
  unfold canonicalLSFInitWithH
  rw [safeLen_eq_of_eq_on_E hℓ]

lemma canonicalLSFInitWithH_eq_chosen {h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {L_in P_fp : ℕ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {k j : ℕ}
    (hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ (safeLen G₀ ℓ₀) k) :
    canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j = (chosenGuestRun hV).S₀ j := by
  unfold canonicalLSFInitWithH
  exact dite_eq_left hV

/-- Approximate-MWU specification for `canonicalLSFInitWithH` under stretch-only `[AN19]`:
matches the body of `IsApproxMWUInit` with constants
`(C_lsst = 4 * max K_AN 1 + 5, α = 5 / 4, K_σ = defaultK_sigma K_AN, K_ρ = 40960)`. -/
theorem canonicalLSFInitWithH_approxMWU (h : ℕ) (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (L_in P_fp : ℕ) (hQ : StretchOnlyAN19Spec Q_AN c_AN K_AN) :
    ∀ (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ), G₀.IsValid → G₀.V.Nonempty →
      (∀ e ∈ G₀.E, 0 < ℓ₀ e) → 1 ≤ k →
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
        ∀ j < k, canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j =
          initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh := by
  classical
  intro G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk
  set ℓ := safeLen G₀ ℓ₀
  have hℓ_eq : ∀ e ∈ G₀.E, ℓ e = ℓ₀ e := fun _ he => safeLen_eq_of_mem ℓ₀ he
  by_cases hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ ℓ k
  · set r := chosenGuestRun hV
    obtain ⟨_, hρ_lo, hρ_hi⟩ := lemma55Rho_bounds K_AN G₀.n hk
    have hρ_lo' : 10 * (max (defaultK_sigma K_AN : ℝ)
          (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ (lemma55RhoNat K_AN G₀.n k : ℝ) := by
      dsimp only [lemma54K0] at hρ_lo; linarith
    have hρ_hi' : (lemma55RhoNat K_AN G₀.n k : ℝ) ≤
        (40960 : ℝ) * (max (defaultK_sigma K_AN : ℝ)
          (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := by
      dsimp only [lemma54K0] at hρ_hi; linarith
    refine ⟨(defaultThreshNat K_AN G₀.n k : ℝ), (lemma55RhoNat K_AN G₀.n k : ℝ),
      1 / (20 * (k : ℝ)), r.v', r.T_raw, fun j => (r.S₀ j).r₀, r.C_reps, fun j => (r.S₀ j).π,
      r.W_T, hρ_lo', hρ_hi', by positivity, le_rfl, r.hv0, r.hv_pos, ?_, ?_, ?_⟩
    · intro j hj
      exact validLSFParams_congr_len hG₀ hℓ_eq (r.hinit j hj).1
    · intro j hj e he
      have hSe : r.S₀ j = initLSFWith G₀ ℓ₀ (r.v' j) (k : ℝ) (r.T_raw j) (r.S₀ j).r₀
          (r.C_reps j) (r.S₀ j).π (r.W_T j) (defaultThreshNat K_AN G₀.n k : ℝ) :=
        (r.hinit j hj).2.trans (initLSFWith_congr_len hℓ_eq)
      rw [← hSe]
      exact r.hv_step j hj e he
    · intro j hj
      rw [canonicalLSFInitWithH_eq_chosen hV]
      exact (r.hinit j hj).2.trans (initLSFWith_congr_len hℓ_eq)
  · have hfb := fallbackLSFInit_approxMWU (stretchOnlyAN19_to_wgraphLSST hQ) G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk
    rcases hfb with ⟨thresh, ρ, δ, v, T_raw, r₀, C_reps, π, W_T, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨thresh, ρ, δ, v, T_raw, r₀, C_reps, π, W_T, h1, h2, h3, h4, h5, h6, h7, h8, fun j hj => ?_⟩
    unfold canonicalLSFInitWithH
    rw [dite_eq_right hV, fallbackLSFInit_eq_of_eq_on_E hℓ_eq]
    exact h9 j hj

/-- Expanded approximate-MWU specification for `canonicalLSFInit` (`h = 4`), with
`K_ρ = 40960`. -/
theorem canonicalLSFInit_approxMWU (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (L_in P_fp : ℕ) (hQ : StretchOnlyAN19Spec Q_AN c_AN K_AN) :
    ∃ K_ρ : ℝ, 1 ≤ K_ρ ∧
      ∀ (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ), G₀.IsValid → G₀.V.Nonempty →
        (∀ e ∈ G₀.E, 0 < ℓ₀ e) → 1 ≤ k →
        ∃ (thresh ρ δ : ℝ) (v : ℕ → ℕ → ℝ) (T_raw : ℕ → MGraph) (r₀ : ℕ → ℕ)
          (C_reps : ℕ → Finset ℕ) (π : ℕ → ℕ → ℕ) (W_T : ℕ → Finset (Finset ℕ)),
          10 * (max (defaultK_sigma K_AN : ℝ)
                (max (112 * (1 + (5 / 4 : ℝ)) * max 1 (4 * max K_AN 1 + 5)) 2240)) * (k : ℝ) *
              (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ ρ ∧
          ρ ≤ K_ρ * (max (defaultK_sigma K_AN : ℝ)
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
          ∀ j < k, canonicalLSFInit Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j =
            initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh :=
  ⟨40960, by norm_num, canonicalLSFInitWithH_approxMWU 4 Q_AN c_AN K_AN L_in P_fp hQ⟩

end MinCostFlow.SparseCore.Program
