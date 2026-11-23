module

public import MinCostFlow.SparseCore.LSFInit
public import MinCostFlow.SparseCore.Program.LSFWindowCanon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `IsApproxMWUInit` Specifications for `canonicalLSFInit` and `canonicalLSFInitAuto` (`LSFWindowSpec`)

Connects `canonicalLSFInit` (`LSFWindowCanon`) to `MinCostFlow.SparseCore.IsApproxMWUInit` with
format-independent constant `K_ρ = 40960` (Lemma 5.5, pages 17–18 of `arXiv:2309.16629v1`):

* `canonicalLSFInit_spec`: for any `[AN19]` program meeting the stretch-only hypothesis, there is a
  single constant `K_ρ ≥ 1` such that `canonicalLSFInit Q_AN c_AN K_AN L_in P_fp` satisfies
  `IsApproxMWUInit` for every `(L_in, P_fp)`.
* `autoLimbCount`: the least limb count `L` (at `h = 4`) satisfying the fixed-point capacity
  requirements and holding every input length `ℓ₀ e` (`e ∈ G₀.E`) without overflow, bounded in
  terms of `P_fp`, `log₂(|E| + 1)`, and the bit size of the largest length (`autoLimbCount_le`,
  `autoLimbCount_le_of_maxLen`).
* `canonicalLSFInitAuto`: runs `canonicalLSFInit` at `L_in = autoLimbCount G₀ ℓ₀ P_fp`.
* `canonicalLSFInitAuto_eq_guestRun`: whenever every edge length is a positive multiple of
  `2 ^ (-P_fp)` (and the precision holds `k`), `canonicalLSFInitAuto` equals the canonical guest
  run, never the fallback.
* `canonicalLSFInitAuto_spec`: `∃ K_ρ ≥ 1, ∀ P_fp, IsApproxMWUInit (canonicalLSFInitAuto … P_fp) …`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.Num

/-! ## Specification of `canonicalLSFInit` (format-independent `K_ρ`) -/

/-- Approximate-MWU specification for `canonicalLSFInit` (`h = 4`), matching Lemma 5.5 (pages 17–18
of `arXiv:2309.16629v1`) with format-independent constant `K_ρ = 40960`. -/
theorem canonicalLSFInit_spec :
    ∀ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      (∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
        (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
        ∃ out cost,
          RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
            G_a.IsSpanningTree out ∧
            G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n) →
      ∃ K_ρ : ℝ, 1 ≤ K_ρ ∧ ∀ (L_in P_fp : ℕ),
        IsApproxMWUInit (canonicalLSFInit Q_AN c_AN K_AN L_in P_fp)
          (4 * max K_AN 1 + 5) (5 / 4)
          (MinCostFlow.LSF.Program.defaultK_sigma K_AN) K_ρ :=
  fun Q_AN c_AN K_AN hQ =>
    ⟨40960, by norm_num, fun L_in P_fp =>
      canonicalLSFInitWithH_approxMWU 4 Q_AN c_AN K_AN L_in P_fp hQ⟩

/-! ## Automatic least limb count `autoLimbCount` and `canonicalLSFInitAuto` -/

/-- Format capacity condition for `L` four-bit limbs (`h = 4`) at precision `P_fp` on `(G₀, ℓ₀)`. -/
def autoLimbPred (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (P_fp L : ℕ) : Prop :=
  1 ≤ L ∧ P_fp + 6 ≤ 4 * L ∧
  32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (4 * L - 1) ∧
  ∀ e ∈ G₀.E, canonLenInt ℓ₀ P_fp e < 2 ^ (4 * L - 1)

private lemma autoLimbPred_of_cand (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (P_fp : ℕ) :
    let U_max := G₀.E.sup (canonLenInt ℓ₀ P_fp)
    let B_bit := max (P_fp + 6)
      (max (P_fp + Nat.log 2 (G₀.E.card + 1) + 7) (Nat.log 2 (U_max + 1) + 2))
    autoLimbPred G₀ ℓ₀ P_fp ((B_bit + 3) / 4) := by
  intro U_max B_bit
  set L₀ := (B_bit + 3) / 4
  have h4L : B_bit ≤ 4 * L₀ := by dsimp only [L₀]; omega
  have hB_ge6 : 6 ≤ B_bit := le_trans (by omega) (le_max_left _ _)
  have h1L : 1 ≤ L₀ := by omega
  have hP6 : P_fp + 6 ≤ 4 * L₀ := le_trans (le_max_left _ _) h4L
  have hm_lt : 32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (4 * L₀ - 1) := by
    have h1 : G₀.E.card + 1 < 2 ^ (Nat.log 2 (G₀.E.card + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by decide) _
    have h2 : 32 * (G₀.E.card + 1) * 2 ^ P_fp <
        2 ^ (P_fp + Nat.log 2 (G₀.E.card + 1) + 6) := by
      have hpow : 2 ^ (P_fp + Nat.log 2 (G₀.E.card + 1) + 6) =
          32 * 2 ^ (Nat.log 2 (G₀.E.card + 1) + 1) * 2 ^ P_fp := by
        rw [show P_fp + Nat.log 2 (G₀.E.card + 1) + 6 =
            5 + (Nat.log 2 (G₀.E.card + 1) + 1) + P_fp by omega, pow_add, pow_add]
        norm_num
      rw [hpow]
      have h3 : 32 * (G₀.E.card + 1) < 32 * 2 ^ (Nat.log 2 (G₀.E.card + 1) + 1) :=
        Nat.mul_lt_mul_of_pos_left h1 (by decide)
      exact Nat.mul_lt_mul_of_pos_right h3 (Nat.pow_pos (by decide))
    have hexp : P_fp + Nat.log 2 (G₀.E.card + 1) + 6 ≤ 4 * L₀ - 1 := by
      have hle : P_fp + Nat.log 2 (G₀.E.card + 1) + 7 ≤ B_bit :=
        le_trans (le_max_left _ _) (le_max_right (P_fp + 6) _)
      omega
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hexp)
  have hu_lt : ∀ e ∈ G₀.E, canonLenInt ℓ₀ P_fp e < 2 ^ (4 * L₀ - 1) := by
    intro e he
    have hle : canonLenInt ℓ₀ P_fp e ≤ U_max := Finset.le_sup (f := canonLenInt ℓ₀ P_fp) he
    have h1 : U_max + 1 < 2 ^ (Nat.log 2 (U_max + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by decide) _
    have hexp : Nat.log 2 (U_max + 1) + 1 ≤ 4 * L₀ - 1 := by
      have hleB : Nat.log 2 (U_max + 1) + 2 ≤ B_bit :=
        le_trans (le_max_right _ _) (le_max_right (P_fp + 6) _)
      omega
    exact lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hexp)
  exact ⟨h1L, hP6, hm_lt, hu_lt⟩

lemma autoLimbPred_exists (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (P_fp : ℕ) :
    ∃ L, autoLimbPred G₀ ℓ₀ P_fp L :=
  ⟨_, autoLimbPred_of_cand G₀ ℓ₀ P_fp⟩

/-- The least four-bit limb count `L` that holds all scaled lengths `⌊ℓ₀(e) · 2^{P_fp}⌋`
(`e ∈ G₀.E`) and satisfies the capacity inequalities of `CanonicalLSFValid`. -/
noncomputable def autoLimbCount (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (P_fp : ℕ) : ℕ :=
  open Classical in Nat.find (autoLimbPred_exists G₀ ℓ₀ P_fp)

lemma autoLimbCount_spec (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (P_fp : ℕ) :
    autoLimbPred G₀ ℓ₀ P_fp (autoLimbCount G₀ ℓ₀ P_fp) := by
  classical exact Nat.find_spec (autoLimbPred_exists G₀ ℓ₀ P_fp)

lemma autoLimbCount_min {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {P_fp L : ℕ}
    (hL : autoLimbPred G₀ ℓ₀ P_fp L) : autoLimbCount G₀ ℓ₀ P_fp ≤ L := by
  classical exact Nat.find_min' (autoLimbPred_exists G₀ ℓ₀ P_fp) hL

lemma autoLimbCount_eq_of_eq_on_E {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {P_fp : ℕ}
    (hℓ : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    autoLimbCount G₀ ℓ₁ P_fp = autoLimbCount G₀ ℓ₂ P_fp := by
  have hpred : ∀ L, autoLimbPred G₀ ℓ₁ P_fp L ↔ autoLimbPred G₀ ℓ₂ P_fp L := fun L => by
    unfold autoLimbPred
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, h3, fun e he => ?_⟩
    · have : canonLenInt ℓ₂ P_fp e = canonLenInt ℓ₁ P_fp e := by
        unfold canonLenInt; rw [hℓ e he]
      rw [this]; exact h4 e he
    · have : canonLenInt ℓ₁ P_fp e = canonLenInt ℓ₂ P_fp e := by
        unfold canonLenInt; rw [hℓ e he]
      rw [this]; exact h4 e he
  exact le_antisymm
    (autoLimbCount_min ((hpred _).mpr (autoLimbCount_spec G₀ ℓ₂ P_fp)))
    (autoLimbCount_min ((hpred _).mp (autoLimbCount_spec G₀ ℓ₁ P_fp)))

/-- Upper bound on `autoLimbCount` in terms of `P_fp`, `log₂(|E| + 1)`, and the bit size of the
largest scaled length `sup_{e ∈ E} ⌊ℓ₀(e) · 2^{P_fp}⌋`. -/
lemma autoLimbCount_le (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (P_fp : ℕ) :
    autoLimbCount G₀ ℓ₀ P_fp ≤
      (max (P_fp + Nat.log 2 (G₀.E.card + 1) + 7)
        (Nat.log 2 (G₀.E.sup (canonLenInt ℓ₀ P_fp) + 1) + 2) + 3) / 4 := by
  have h1 := autoLimbCount_min (autoLimbPred_of_cand G₀ ℓ₀ P_fp)
  have hmax : max (P_fp + 6)
      (max (P_fp + Nat.log 2 (G₀.E.card + 1) + 7)
        (Nat.log 2 (G₀.E.sup (canonLenInt ℓ₀ P_fp) + 1) + 2)) =
      max (P_fp + Nat.log 2 (G₀.E.card + 1) + 7)
        (Nat.log 2 (G₀.E.sup (canonLenInt ℓ₀ P_fp) + 1) + 2) :=
    max_eq_right (le_trans (by omega) (le_max_left _ _))
  simpa only [hmax] using h1

/-- Upper bound on `autoLimbCount` when every edge length satisfies `ℓ₀ e ≤ M_len`:
bounded by `(P_fp + max (log₂(|E| + 1)) (log₂(M_len + 1))) / 4 + 3`. -/
lemma autoLimbCount_le_of_maxLen {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {P_fp M_len : ℕ}
    (hM : ∀ e ∈ G₀.E, ℓ₀ e ≤ (M_len : ℝ)) :
    autoLimbCount G₀ ℓ₀ P_fp ≤
      (P_fp + max (Nat.log 2 (G₀.E.card + 1)) (Nat.log 2 (M_len + 1))) / 4 + 3 := by
  have hsup_le : G₀.E.sup (canonLenInt ℓ₀ P_fp) ≤ M_len * 2 ^ P_fp := by
    refine Finset.sup_le fun e he => ?_
    unfold canonLenInt
    refine Nat.floor_le_of_le ?_
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ P_fp := by positivity
    have hmul := mul_le_mul_of_nonneg_right (hM e he) h2
    exact_mod_cast hmul
  have hlog_le : Nat.log 2 (G₀.E.sup (canonLenInt ℓ₀ P_fp) + 1) ≤
      P_fp + Nat.log 2 (M_len + 1) := by
    have hlt : G₀.E.sup (canonLenInt ℓ₀ P_fp) + 1 < 2 ^ (P_fp + Nat.log 2 (M_len + 1) + 1) := by
      have h1 : M_len + 1 < 2 ^ (Nat.log 2 (M_len + 1) + 1) :=
        Nat.lt_pow_succ_log_self (by decide) _
      have h2 : M_len * 2 ^ P_fp + 1 ≤ (M_len + 1) * 2 ^ P_fp := by
        rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left (Nat.one_le_two_pow) _
      have h3 : (M_len + 1) * 2 ^ P_fp < 2 ^ (Nat.log 2 (M_len + 1) + 1) * 2 ^ P_fp :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by decide))
      have hpow : 2 ^ (Nat.log 2 (M_len + 1) + 1) * 2 ^ P_fp =
          2 ^ (P_fp + Nat.log 2 (M_len + 1) + 1) := by
        rw [← pow_add]; congr 1; omega
      omega
    have := Nat.log_lt_of_lt_pow (by omega) hlt
    omega
  have hbase := autoLimbCount_le G₀ ℓ₀ P_fp
  omega

/-- Limb-count-independent canonical LSF initializer at precision `P_fp`: invokes
`canonicalLSFInit` at the least limb count `autoLimbCount G₀ ℓ₀ P_fp` holding all input lengths. -/
noncomputable def canonicalLSFInitAuto (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (P_fp : ℕ) : LSFInit :=
  fun G₀ ℓ₀ k j =>
    canonicalLSFInit Q_AN c_AN K_AN (autoLimbCount G₀ ℓ₀ P_fp) P_fp G₀ ℓ₀ k j

/-- Whenever every edge length is a positive multiple of `2 ^ (-P_fp)` (and `P_fp` has enough
precision for `k`), `CanonicalLSFValid` holds at `L_in = autoLimbCount G₀ ℓ₀ P_fp`. -/
lemma canonicalLSFInitAuto_valid_of_dyadic {Q_AN : Program} {c_AN P_fp k : ℕ} {K_AN : ℝ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hdiv : 4 ∣ P_fp) (hk : 1 ≤ k) (hq : ∃ q, q + 11 ≤ P_fp ∧ 40 * k ≤ 2 ^ q)
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hdyad : ∀ e ∈ G₀.E, ∃ u : ℕ, 1 ≤ u ∧ ℓ₀ e = (u : ℝ) / (2 : ℝ) ^ P_fp) :
    CanonicalLSFValid Q_AN c_AN K_AN 4 (autoLimbCount G₀ ℓ₀ P_fp) P_fp G₀ (safeLen G₀ ℓ₀) k := by
  obtain ⟨hL1, hP6, hm_lt, hu_lt⟩ := autoLimbCount_spec G₀ ℓ₀ P_fp
  set L := autoLimbCount G₀ ℓ₀ P_fp
  refine ⟨hQ, by decide, hL1, hdiv, hP6, hk, hq, hm_lt, hG₀, hV₀, fun e he => ?_⟩
  obtain ⟨u, hu1, hℓu⟩ := hdyad e he
  have h2P_pos : (0 : ℝ) < (2 : ℝ) ^ P_fp := by positivity
  have hci : canonLenInt ℓ₀ P_fp e = u := by
    unfold canonLenInt
    rw [hℓu, div_mul_cancel₀ _ h2P_pos.ne', Nat.floor_natCast]
  have hu_cap_half : u < 2 ^ (4 * L - 1) := hci ▸ hu_lt e he
  have hcap_eq : capacity 4 L = 2 * 2 ^ (4 * L - 1) := by
    unfold capacity base
    rw [← pow_mul, ← pow_succ']
    congr 1; omega
  have hu_cap : u < capacity 4 L := by omega
  have hnot_neg : ¬ capacity 4 L ≤ 2 * u := by omega
  refine ⟨fun i => natLimb u 4 i, valid_of_natLimb (u := u) (fun i _ => by simp), ?_, ?_⟩
  · rw [safeLen_eq_of_mem ℓ₀ he, hℓu]
    unfold fixVal intVal signedVal
    have huns : unsignedVal (fun i => natLimb u 4 i) 0 4 L = u :=
      unsignedVal_natLimb (fun i _ => by simp) hu_cap
    rw [huns, ite_eq_right hnot_neg, sub_zero]
    simp
  · rw [safeLen_eq_of_mem ℓ₀ he, hℓu]
    have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu1
    exact div_pos hu_pos h2P_pos

/-- Whenever every edge length is a positive multiple of `2 ^ (-P_fp)` (and `P_fp` holds `k`),
`canonicalLSFInitAuto` equals the canonical guest run at `L_in = autoLimbCount G₀ ℓ₀ P_fp`,
never the fallback. -/
theorem canonicalLSFInitAuto_eq_guestRun {Q_AN : Program} {c_AN P_fp k : ℕ} {K_AN : ℝ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hdiv : 4 ∣ P_fp) (hk : 1 ≤ k) (hq : ∃ q, q + 11 ≤ P_fp ∧ 40 * k ≤ 2 ^ q)
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hdyad : ∀ e ∈ G₀.E, ∃ u : ℕ, 1 ≤ u ∧ ℓ₀ e = (u : ℝ) / (2 : ℝ) ^ P_fp) (j : ℕ) :
    canonicalLSFInitAuto Q_AN c_AN K_AN P_fp G₀ ℓ₀ k j =
      (chosenGuestRun (canonicalLSFInitAuto_valid_of_dyadic hQ hdiv hk hq hG₀ hV₀ hdyad)).S₀ j := by
  unfold canonicalLSFInitAuto canonicalLSFInit
  exact canonicalLSFInitWithH_eq_chosen
    (canonicalLSFInitAuto_valid_of_dyadic hQ hdiv hk hq hG₀ hV₀ hdyad)

/-- Approximate-MWU specification for `canonicalLSFInitAuto` (Lemma 5.5, pages 17–18 of
`arXiv:2309.16629v1`) with precision-independent constant `K_ρ = 40960`. -/
theorem canonicalLSFInitAuto_spec :
    ∀ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      (∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
        (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
        ∃ out cost,
          RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
            G_a.IsSpanningTree out ∧
            G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n) →
      ∃ K_ρ : ℝ, 1 ≤ K_ρ ∧ ∀ (P_fp : ℕ),
        IsApproxMWUInit (canonicalLSFInitAuto Q_AN c_AN K_AN P_fp)
          (4 * max K_AN 1 + 5) (5 / 4)
          (MinCostFlow.LSF.Program.defaultK_sigma K_AN) K_ρ :=
  fun Q_AN c_AN K_AN hQ =>
    ⟨40960, by norm_num, fun P_fp G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk =>
      canonicalLSFInitWithH_approxMWU 4 Q_AN c_AN K_AN
        (autoLimbCount G₀ ℓ₀ P_fp) P_fp hQ G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk⟩

end MinCostFlow.SparseCore.Program
