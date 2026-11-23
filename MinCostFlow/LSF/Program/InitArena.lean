module

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import MinCostFlow.LSF.Program.Spec
public import MinCostFlow.LSF.Program.BridgeLemmas
public import MinCostFlow.Num.IntegerDivide
public import MinCostFlow.Num.SignFacts
import MinCostFlow.Num.WordBounds

/-!
# Scratch Arena and Limb-Width Arithmetic for `InitTree`

Defines the `InitArena` scratch layout inside `[lsfEndAddr, b + lsfInitSpace]` and proves
pure `Num` representation and integer arithmetic bounds needed by `InitTreeWeights` and
`InitTree`:
- `unsignedVal_split`, `unsignedVal_pad_zero`, `unsignedVal_zero_lo_hi`,
  `low_limbs_of_mul_lt`, and `pos_intVal_toNat_eq`.
- `kWidthOf` / `K_q` bounds (`7 ≤ L_sim`, `K_w ≤ L_sim`, `K_q ≤ 2 * L_sim`),
  `edgeMult_bounds`, `qNat_bounds`.
- `ia_end_le_lsstHeap`, `lsfInitSpace_ge_arena_add_lsst`, and `div_arena_le_lsstSpace`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM

/-! ## `InitArena` Scratch Layout -/

/-- Scratch layout placed immediately after the static LSF blocks for `Init`.
All arrays strictly precede `iaLsstHeap`, leaving `[iaLsstHeap, iaLsstHeap + lsstSpace)`
free for `lsstFrontierProc` (and temporarily reused for integer divisions after `memFill`). -/
structure InitArena where
  b : ℕ
  vCap : ℕ
  eCap : ℕ
  n0 : ℕ
  m0 : ℕ
  L_in : ℕ
  L_w : ℕ
  L_sim : ℕ
  h : ℕ

namespace InitArena

/-- Static end address using `tM = n0 - 1`. -/
def base (A : InitArena) : ℕ :=
  lsfEndAddr A.b A.vCap A.eCap A.n0 (A.n0 - 1) A.L_w

/-- Limb width for computing `S_v = ∑_{e ∈ G₀.E} v_int(e)` and `edgeMult`. -/
def K_w (A : InitArena) : ℕ :=
  WideWord.kWidthOf A.m0 A.L_in

/-- Limb width for `q_nat(e) = ⌊edgeMult * 2^(h*(L_in+4)) / ℓ_int(e)⌋`. -/
def K_q (A : InitArena) : ℕ :=
  A.K_w + 6

/-- Persistent `q_nat` array (`m0 * K_q` words), retained through `InitCong`. -/
def qNatPtr (A : InitArena) : ℕ := A.base

/-- Base of the reusable phase scratch area `[workPtr, lsstHeap)`. -/
def workPtr (A : InitArena) : ℕ := A.qNatPtr + A.m0 * A.K_q

def multPtr (A : InitArena) : ℕ := A.workPtr
def svPtr (A : InitArena) : ℕ := A.multPtr + A.m0
def svMinusOnePtr (A : InitArena) : ℕ := A.svPtr + A.K_w
def m0LimbsPtr (A : InitArena) : ℕ := A.svMinusOnePtr + A.K_w
def oneLimbsPtr (A : InitArena) : ℕ := A.m0LimbsPtr + A.K_w
def edgeLimbsPtr (A : InitArena) : ℕ := A.oneLimbsPtr + A.K_w
def numerPtr (A : InitArena) : ℕ := A.edgeLimbsPtr + A.K_w
def lenQPtr (A : InitArena) : ℕ := A.numerPtr + A.K_q
def copyTailPtr (A : InitArena) : ℕ := A.lenQPtr + A.K_q
def copyHeadPtr (A : InitArena) : ℕ := A.copyTailPtr + 2 * A.m0
def copyLenPtr (A : InitArena) : ℕ := A.copyHeadPtr + 2 * A.m0
def copyWtPtr (A : InitArena) : ℕ := A.copyLenPtr + 2 * A.m0 * A.L_in
def copyOrigIdxPtr (A : InitArena) : ℕ := A.copyWtPtr + 2 * A.m0 * A.L_in
def copySubIdxPtr (A : InitArena) : ℕ := A.copyOrigIdxPtr + 2 * A.m0
def outOrigPtr (A : InitArena) : ℕ := A.copySubIdxPtr + 2 * A.m0
def outBridgePtr (A : InitArena) : ℕ := A.outOrigPtr + A.n0
def outHdrPtr (A : InitArena) : ℕ := A.outBridgePtr + 2 * A.n0
def usedBridgePtr (A : InitArena) : ℕ := A.outHdrPtr + 2
def bfsScratchPtr (A : InitArena) : ℕ := A.usedBridgePtr + (2 * A.m0 + A.n0)
def treeWorkEnd (A : InitArena) : ℕ := A.bfsScratchPtr + 8 * A.n0

/-- Heap passed to `lsstFrontierProc` (and cleared beforehand via `memFill`). -/
def lsstHeap (A : InitArena) : ℕ :=
  A.base + 50 * (A.n0 + A.m0 + 1) * (A.L_w + A.L_sim + auxLogCap A.n0 + 20) + 200

end InitArena

/-! ## `Num` Padding and Word Decoding Lemmas -/

lemma unsignedVal_split (mem : ℕ → ℕ) (a h L K : ℕ) :
    Num.unsignedVal mem a h (L + K) =
      Num.unsignedVal mem a h L + Num.capacity h L * Num.unsignedVal mem (a + L) h K := by
  induction L generalizing a with
  | zero => simp [Num.unsignedVal, Num.capacity]
  | succ L ih =>
    rw [Nat.succ_add, Num.unsignedVal, Num.unsignedVal, Num.capacity_succ]
    have hih := ih (a + 1)
    rw [show a + 1 + L = a + (L + 1) by omega] at hih
    rw [hih]
    ring

lemma unsignedVal_pad_zero {mem : ℕ → ℕ} {a h L K : ℕ} (hLK : L ≤ K)
    (hz : ∀ i, L ≤ i → i < K → mem (a + i) = 0) :
    Num.unsignedVal mem a h K = Num.unsignedVal mem a h L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLK
  rw [unsignedVal_split]
  have hzero : Num.unsignedVal mem (a + L) h d = 0 :=
    Num.unsignedVal_zero fun i hi => by
      rw [Nat.add_assoc]
      exact hz (L + i) (by omega) (by omega)
  rw [hzero, mul_zero, add_zero]

lemma valid_pad_zero {mem : ℕ → ℕ} {a h L K : ℕ}
    (hv : Num.Valid mem a h L) (hz : ∀ i, L ≤ i → i < K → mem (a + i) = 0) :
    Num.Valid mem a h K := by
  intro i hi
  by_cases hiL : i < L
  · exact hv i hiL
  · rw [hz i (Nat.not_lt.mp hiL) hi]
    exact Num.base_pos h

lemma unsignedVal_zero_lo_hi {mem : ℕ → ℕ} {a h L K : ℕ} (hLK : L ≤ K)
    (hz : ∀ i < L, mem (a + i) = 0) :
    Num.unsignedVal mem a h K = Num.capacity h L * Num.unsignedVal mem (a + L) h (K - L) := by
  have heq : K = L + (K - L) := (Nat.add_sub_cancel' hLK).symm
  conv_lhs => rw [heq, unsignedVal_split, Num.unsignedVal_zero hz, zero_add]

lemma pos_intVal_toNat_eq {mem : ℕ → ℕ} {a h L : ℕ}
    (hv : Num.Valid mem a h L) (hpos : 0 < Num.intVal mem a h L) :
    Num.unsignedVal mem a h L = (Num.intVal mem a h L).toNat ∧
      2 * Num.unsignedVal mem a h L < Num.capacity h L := by
  have hnot_neg : ¬ Num.intVal mem a h L < 0 := by omega
  have hlt : 2 * Num.unsignedVal mem a h L < Num.capacity h L :=
    Nat.not_le.mp ((Num.intVal_neg_iff hv).not.mp hnot_neg)
  have heq : Num.intVal mem a h L = (Num.unsignedVal mem a h L : ℤ) := by
    dsimp only [Num.intVal, Num.signedVal]
    split_ifs <;> omega
  exact ⟨by rw [heq]; rfl, hlt⟩

lemma intVal_eq_of_unsignedVal_lt {mem : ℕ → ℕ} {a h L : ℕ}
    (h2 : 2 * Num.unsignedVal mem a h L < Num.capacity h L) :
    Num.intVal mem a h L = (Num.unsignedVal mem a h L : ℤ) := by
  dsimp only [Num.intVal, Num.signedVal]
  split_ifs <;> omega

lemma wrap_of_nat_lt {h L n : ℕ} (h2 : 2 * n < Num.capacity h L) :
    Num.wrap h L (n : ℤ) = (n : ℤ) := by
  have hn_lt : n < Num.capacity h L := by omega
  have hres : Num.residue h L (n : ℤ) = n := by
    dsimp only [Num.residue]
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg n) (by exact_mod_cast hn_lt)]
    rfl
  dsimp only [Num.wrap, Num.signedVal]
  rw [hres]
  split_ifs <;> omega

lemma low_limbs_of_mul_lt {mem : ℕ → ℕ} {a h L n : ℕ}
    (hv : Num.Valid mem a h (2 * L))
    (hint : Num.intVal mem a h (2 * L) = (n : ℤ))
    (hn : 2 * n < Num.capacity h L) :
    Num.Valid mem a h L ∧
      Num.unsignedVal mem a h L = n ∧
      Num.intVal mem a h L = (n : ℤ) := by
  have hvL : Num.Valid mem a h L := fun i hi => hv i (by omega)
  have h2L : Num.unsignedVal mem a h (L + L) = n := by
    have hpos : 0 ≤ Num.intVal mem a h (2 * L) := by omega
    have hnot_neg : ¬ Num.intVal mem a h (2 * L) < 0 := by omega
    have hlt2 : 2 * Num.unsignedVal mem a h (2 * L) < Num.capacity h (2 * L) :=
      Nat.not_le.mp ((Num.intVal_neg_iff hv).not.mp hnot_neg)
    have hEq : Num.intVal mem a h (2 * L) = (Num.unsignedVal mem a h (2 * L) : ℤ) :=
      intVal_eq_of_unsignedVal_lt hlt2
    rw [hint] at hEq
    have hu : Num.unsignedVal mem a h (2 * L) = n := Int.ofNat.inj hEq.symm
    simpa [Nat.two_mul] using hu
  rw [unsignedVal_split] at h2L
  have hcap : n < Num.capacity h L := by omega
  have hhi0 : Num.unsignedVal mem (a + L) h L = 0 := by
    by_contra hne
    have hpos := Nat.pos_of_ne_zero hne
    have hge : Num.capacity h L ≤ Num.capacity h L * Num.unsignedVal mem (a + L) h L :=
      Nat.le_mul_of_pos_right _ hpos
    linarith [h2L, hcap, hge]
  rw [hhi0, mul_zero, add_zero] at h2L
  exact ⟨hvL, h2L, (intVal_eq_of_unsignedVal_lt (h2L.symm ▸ hn)).trans (congrArg Nat.cast h2L)⟩

/-! ## Width, Multiplicity, and Arena Containment Bounds -/

lemma kWidth_le_lsstLSimMin {c_AN n0 m0 L_in h : ℕ} (hm0 : 1 ≤ m0) :
    WideWord.kWidthOf m0 L_in ≤ WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h := by
  refine le_trans ?_ (le_max_left _ _)
  dsimp only [WideWord.kWidthOf]
  have hlog : Nat.log 2 (4 * m0 + 2) ≤ Nat.log 2 (4 * (2 * m0) + 2) :=
    Nat.log_mono_right (by omega)
  omega

lemma seven_le_lsstLSimMin {c_AN n0 m0 L_in h : ℕ} (hm0 : 1 ≤ m0) (hL : 1 ≤ L_in) :
    7 ≤ WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h := by
  refine le_trans ?_ (le_max_left _ _)
  dsimp only [WideWord.kWidthOf]
  have hge10 : 8 ≤ 4 * (2 * m0) + 2 := by omega
  have hlog3 : 3 ≤ Nat.log 2 (4 * (2 * m0) + 2) := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    exact hge10
  omega

lemma kq_le_two_lsim {c_AN : ℕ} {A : InitArena} (hm0 : 1 ≤ A.m0) (hL : 1 ≤ A.L_in)
    (hLsim : WideWord.lsstLSimMin c_AN A.n0 (2 * A.m0) A.L_in A.h ≤ A.L_sim) :
    A.K_q ≤ 2 * A.L_sim := by
  have hKw : A.K_w ≤ A.L_sim := le_trans (kWidth_le_lsstLSimMin hm0) hLsim
  have h7 : 7 ≤ A.L_sim := le_trans (seven_le_lsstLSimMin hm0 hL) hLsim
  dsimp only [InitArena.K_q, InitArena.K_w] at hKw ⊢
  omega

lemma cap_kWidth_bounds {m0 L_in h : ℕ} (_hm0 : 1 ≤ m0) (hh : 1 ≤ h) :
    4 * m0 + 2 < 2 ^ (Nat.log 2 (4 * m0 + 2) + 1) ∧
      2 ^ (Nat.log 2 (4 * m0 + 2) + 1) ≤ Num.capacity h (Nat.log 2 (4 * m0 + 2) + 1) ∧
      4 * m0 * Num.capacity h L_in < Num.capacity h (WideWord.kWidthOf m0 L_in) / 2 := by
  have hlt1 : 4 * m0 + 2 < 2 ^ (Nat.log 2 (4 * m0 + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hpow_le : 2 ^ (Nat.log 2 (4 * m0 + 2) + 1) ≤ Num.capacity h (Nat.log 2 (4 * m0 + 2) + 1) := by
    rw [Num.capacity_eq_two_pow]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hh)
  have hcap_lt : 4 * m0 * Num.capacity h L_in < Num.capacity h (WideWord.kWidthOf m0 L_in) / 2 := by
    dsimp only [WideWord.kWidthOf]
    rw [Num.capacity_eq_two_pow, Num.capacity_eq_two_pow]
    rw [Num.capacity_eq_two_pow] at hpow_le
    set k := Nat.log 2 (4 * m0 + 2) + 1
    have hmul_lt : 4 * m0 * 2 ^ (h * L_in) < 2 ^ (h * k + h * L_in) := by
      have h4m : 4 * m0 < 2 ^ (h * k) := lt_of_lt_of_le (by omega) hpow_le
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right h4m (Nat.two_pow_pos _)
    have hexp : h * (L_in + k + 2) = (h * k + h * L_in) + 2 * h := by ring
    rw [hexp, Nat.pow_add]
    have h2h : 4 ≤ 2 ^ (2 * h) :=
      le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4mul : 2 ^ (h * k + h * L_in) * 2 ≤ 2 ^ (h * k + h * L_in) * 2 ^ (2 * h) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have : 4 ≤ 2 ^ (2 * h) := h2h
      nlinarith [Nat.two_pow_pos (h * k + h * L_in)]
    omega
  exact ⟨hlt1, hpow_le, hcap_lt⟩

lemma ceil_div_eq_edgeMult {m0 v_int S_v : ℕ} {v : ℕ → ℝ} {G₀ : MGraph} {e : ℕ}
    (hm0 : 1 ≤ m0) (hm_card : G₀.E.card = m0) (hSv_pos : 0 < S_v)
    (hc : ∃ c > 0, G₀.norm1 v = c * (S_v : ℝ) ∧ v e = c * (v_int : ℝ)) :
    (m0 * v_int + S_v - 1) / S_v = edgeMult G₀ v e := by
  rcases hc with ⟨c, hc_pos, hnorm, hve⟩
  dsimp only [edgeMult]
  rw [hm_card, hnorm, hve]
  have hfrac : (m0 : ℝ) * (c * (v_int : ℝ)) / (c * (S_v : ℝ)) =
      ((m0 * v_int : ℕ) : ℝ) / (S_v : ℝ) := by
    push_cast
    field_simp [ne_of_gt hc_pos]
  rw [hfrac]
  by_cases hv0 : v_int = 0
  · subst hv0
    simp only [mul_zero, zero_add, Nat.cast_zero, zero_div, Nat.ceil_zero]
    exact Nat.div_eq_of_lt (by omega)
  · have hv_pos : 1 ≤ v_int := Nat.pos_of_ne_zero hv0
    have hnum_ge : S_v ≤ m0 * v_int + S_v - 1 := by
      have : 1 ≤ m0 * v_int := Nat.mul_pos hm0 hv_pos
      omega
    have hq_pos : 1 ≤ (m0 * v_int + S_v - 1) / S_v := Nat.div_pos hnum_ge hSv_pos
    symm
    rw [Nat.ceil_eq_iff (Nat.ne_of_gt hq_pos)]
    constructor
    · have hdiv_le : ((m0 * v_int + S_v - 1) / S_v) * S_v ≤ m0 * v_int + S_v - 1 :=
        Nat.div_mul_le_self _ _
      have hle_nat : ((m0 * v_int + S_v - 1) / S_v - 1) * S_v < m0 * v_int := by
        rw [Nat.sub_mul, one_mul]
        omega
      have : (((m0 * v_int + S_v - 1) / S_v - 1 : ℕ) : ℝ) < (m0 * v_int : ℝ) / S_v := by
        rw [lt_div_iff₀ (Nat.cast_pos.mpr hSv_pos)]
        exact_mod_cast hle_nat
      simpa [Nat.cast_sub hq_pos] using this
    · rw [div_le_iff₀ (Nat.cast_pos.mpr hSv_pos)]
      have hlt := Nat.lt_div_mul_add hSv_pos (a := m0 * v_int + S_v - 1)
      have hle : m0 * v_int ≤ ((m0 * v_int + S_v - 1) / S_v) * S_v := by omega
      exact_mod_cast hle

lemma sum_edgeMult_le {G₀ : MGraph} {v : ℕ → ℝ} (hv : ∀ e ∈ G₀.E, 0 < v e) :
    (∀ e ∈ G₀.E, 1 ≤ edgeMult G₀ v e ∧ edgeMult G₀ v e ≤ G₀.E.card) ∧
      ∑ e ∈ G₀.E, edgeMult G₀ v e ≤ 2 * G₀.E.card := by
  by_cases hE : G₀.E.Nonempty
  · have hnorm_pos : 0 < G₀.norm1 v := by
      obtain ⟨e0, he0⟩ := hE
      dsimp only [MGraph.norm1]
      have hle : |v e0| ≤ ∑ e ∈ G₀.E, |v e| :=
        Finset.single_le_sum (f := fun e => |v e|) (fun _ _ => abs_nonneg _) he0
      have : 0 < |v e0| := abs_pos.mpr (ne_of_gt (hv e0 he0))
      linarith
    have hb : ∀ e ∈ G₀.E, 1 ≤ edgeMult G₀ v e ∧ edgeMult G₀ v e ≤ G₀.E.card := by
      intro e he
      have hpos_arg : 0 < (G₀.E.card : ℝ) * v e / G₀.norm1 v :=
        div_pos (mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hE)) (hv e he)) hnorm_pos
      have h1 : 1 ≤ edgeMult G₀ v e := Nat.succ_le_of_lt (Nat.ceil_pos.mpr hpos_arg)
      have hve_le : v e ≤ G₀.norm1 v := by
        dsimp only [MGraph.norm1]
        have hle : |v e| ≤ ∑ f ∈ G₀.E, |v f| :=
          Finset.single_le_sum (f := fun f => |v f|) (fun _ _ => abs_nonneg _) he
        simpa [abs_of_pos (hv e he)] using hle
      have hdiv_le : (G₀.E.card : ℝ) * v e / G₀.norm1 v ≤ G₀.E.card := by
        rw [div_le_iff₀ hnorm_pos]
        exact mul_le_mul_of_nonneg_left hve_le (Nat.cast_nonneg _)
      exact ⟨h1, Nat.ceil_le.mpr hdiv_le⟩
    have hsum : (∑ e ∈ G₀.E, edgeMult G₀ v e : ℝ) ≤ 2 * G₀.E.card := by
      have hterm : ∀ e ∈ G₀.E, (edgeMult G₀ v e : ℝ) ≤ (G₀.E.card : ℝ) * v e / G₀.norm1 v + 1 := by
        intro e he
        dsimp only [edgeMult]
        exact le_of_lt (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (le_of_lt (hv e he))) (le_of_lt hnorm_pos)))
      calc (∑ e ∈ G₀.E, (edgeMult G₀ v e : ℝ))
          ≤ ∑ e ∈ G₀.E, ((G₀.E.card : ℝ) * v e / G₀.norm1 v + 1) := Finset.sum_le_sum hterm
        _ = (G₀.E.card : ℝ) * (∑ e ∈ G₀.E, v e) / G₀.norm1 v + G₀.E.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
              ← Finset.sum_div, ← Finset.mul_sum]
        _ = 2 * G₀.E.card := by
            have hnorm_eq : ∑ e ∈ G₀.E, v e = G₀.norm1 v := by
              dsimp only [MGraph.norm1]
              refine Finset.sum_congr rfl fun e he => (abs_of_pos (hv e he)).symm
            rw [hnorm_eq]
            field_simp [ne_of_gt hnorm_pos]
            ring
    exact ⟨hb, by exact_mod_cast hsum⟩
  · have h0 := Finset.not_nonempty_iff_eq_empty.mp hE
    simp [h0]

lemma qNat_cap_bounds {A : InitArena} (hm0 : 1 ≤ A.m0) (hh : 1 ≤ A.h)
    {ℓ_int : ℕ → ℕ} (hℓ_lt : ∀ e, 2 * ℓ_int e < Num.capacity A.h A.L_in) :
    (∀ e, 16 * ℓ_int e ≤ 2 ^ (A.h * (A.L_in + 4))) ∧
      4 * (2 * A.m0) * 2 ^ (A.h * (A.L_in + 4)) < Num.capacity A.h A.K_q / 2 := by
  have h16 : ∀ e, 16 * ℓ_int e ≤ 2 ^ (A.h * (A.L_in + 4)) := by
    intro e
    have hlt := hℓ_lt e
    rw [Num.capacity_eq_two_pow] at hlt
    have hexp : 3 + A.h * A.L_in ≤ A.h * (A.L_in + 4) := by nlinarith
    calc 16 * ℓ_int e = 8 * (2 * ℓ_int e) := by ring
      _ ≤ 8 * 2 ^ (A.h * A.L_in) := Nat.mul_le_mul_left 8 (le_of_lt hlt)
      _ = 2 ^ 3 * 2 ^ (A.h * A.L_in) := by norm_num
      _ = 2 ^ (3 + A.h * A.L_in) := (Nat.pow_add 2 3 (A.h * A.L_in)).symm
      _ ≤ 2 ^ (A.h * (A.L_in + 4)) := Nat.pow_le_pow_right (by norm_num) hexp
  have hcap : 4 * (2 * A.m0) * 2 ^ (A.h * (A.L_in + 4)) < Num.capacity A.h A.K_q / 2 := by
    obtain ⟨hlt1, hpow_le, _⟩ := cap_kWidth_bounds hm0 hh (L_in := A.L_in)
    rw [Num.capacity_eq_two_pow] at hpow_le
    set k := Nat.log 2 (4 * A.m0 + 2) + 1
    have h8m : 4 * (2 * A.m0) < 2 ^ (A.h * (k + 1)) := by
      have hk1 : 4 * (2 * A.m0) < 2 * 2 ^ k := by omega
      have hk2 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_add]; ring
      have h2le : 2 ^ (k + 1) ≤ 2 ^ (A.h * (k + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hh)
      omega
    have hKq_eq : A.K_q = (A.L_in + 4) + (k + 1) + 3 := by
      dsimp only [InitArena.K_q, InitArena.K_w, WideWord.kWidthOf, k]
      omega
    rw [Num.capacity_eq_two_pow, hKq_eq]
    have hmul : 4 * (2 * A.m0) * 2 ^ (A.h * (A.L_in + 4)) <
        2 ^ (A.h * (k + 1) + A.h * (A.L_in + 4)) := by
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right h8m (Nat.two_pow_pos _)
    have hexp : A.h * ((A.L_in + 4) + (k + 1) + 3) =
        (A.h * (k + 1) + A.h * (A.L_in + 4)) + 3 * A.h := by ring
    rw [hexp, Nat.pow_add]
    have h23h : 8 ≤ 2 ^ (3 * A.h) :=
      le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hle4 : 2 ^ (A.h * (k + 1) + A.h * (A.L_in + 4)) * 2 ≤
        2 ^ (A.h * (k + 1) + A.h * (A.L_in + 4)) * 2 ^ (3 * A.h) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith [Nat.two_pow_pos (A.h * (k + 1) + A.h * (A.L_in + 4))]
    omega
  exact ⟨h16, hcap⟩

lemma lsfStaticSize_tM_le (vCap eCap n0 L_w : ℕ) :
    lsfStaticSize vCap eCap n0 (n0 - 1) L_w ≤ lsfStaticSize vCap eCap n0 n0 L_w := by
  dsimp only [lsfStaticSize, tBlockSize, DynSpanner.Program.dynGraphSize]
  have hn : n0 - 1 ≤ n0 := Nat.sub_le n0 1
  omega

lemma treeWorkEnd_le_lsstHeap {c_AN : ℕ} (A : InitArena) (hm0 : 1 ≤ A.m0) (hn0 : 1 ≤ A.n0)
    (hLin : 1 ≤ A.L_in) (hLinW : A.L_in ≤ A.L_w)
    (hLsim : WideWord.lsstLSimMin c_AN A.n0 (2 * A.m0) A.L_in A.h ≤ A.L_sim) :
    A.treeWorkEnd ≤ A.lsstHeap := by
  have hKw : A.K_w ≤ A.L_sim := le_trans (kWidth_le_lsstLSimMin hm0) hLsim
  have hKq : A.K_q ≤ 2 * A.L_sim := kq_le_two_lsim hm0 hLin hLsim
  dsimp only [InitArena.treeWorkEnd, InitArena.bfsScratchPtr, InitArena.usedBridgePtr,
    InitArena.outHdrPtr, InitArena.outBridgePtr, InitArena.outOrigPtr, InitArena.copySubIdxPtr,
    InitArena.copyOrigIdxPtr, InitArena.copyWtPtr, InitArena.copyLenPtr, InitArena.copyHeadPtr,
    InitArena.copyTailPtr, InitArena.lenQPtr, InitArena.numerPtr, InitArena.edgeLimbsPtr,
    InitArena.oneLimbsPtr, InitArena.m0LimbsPtr, InitArena.svMinusOnePtr, InitArena.svPtr,
    InitArena.multPtr, InitArena.workPtr, InitArena.qNatPtr, InitArena.lsstHeap]
  have hm_Kq : A.m0 * A.K_q ≤ 2 * A.m0 * A.L_sim := by nlinarith
  have hm_Lin : A.m0 * A.L_in ≤ A.m0 * A.L_w := Nat.mul_le_mul_left A.m0 hLinW
  have hr1 : 2 * A.m0 * A.L_in + 2 * A.m0 * A.L_in ≤ 4 * A.m0 * A.L_w := by nlinarith [hm_Lin]
  have hr2 : (2 * A.m0) * A.L_sim = 2 * A.m0 * A.L_sim := by ring
  have hr3 : (4 * A.m0) * A.L_w = 4 * A.m0 * A.L_w := by ring
  have hprod : 2 * A.m0 * A.L_sim + 4 * A.m0 * A.L_w + 15 * A.m0 + 12 * A.n0 + 9 * A.L_sim + 2 ≤
      50 * (A.n0 + A.m0 + 1) * (A.L_w + A.L_sim + auxLogCap A.n0 + 20) + 200 := by
    nlinarith [hm_Kq, hm_Lin, hn0, hm0]
  omega

lemma div_arena_le_lsstSpace (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (A : InitArena)
    (hm0 : 1 ≤ A.m0) (hn0 : 1 ≤ A.n0) (hL : 1 ≤ A.L_in)
    (hLsim : WideWord.lsstLSimMin c_AN A.n0 (2 * A.m0) A.L_in A.h ≤ A.L_sim) :
    50 * A.K_w + A.m0 * (6 * A.K_w + Num.integerDivideSpace A.K_w +
        Num.integerDivideSpace A.K_q + 20) ≤
      WideWord.lsstSpace Q_AN K_AN A.n0 (2 * A.m0) A.L_sim A.h := by
  have hKw1 : A.K_w ≤ A.L_sim := le_trans (kWidth_le_lsstLSimMin hm0) hLsim
  have hKw_le : A.K_w ≤ 2 * A.L_sim := by omega
  have hKq_le : A.K_q ≤ 2 * A.L_sim := kq_le_two_lsim hm0 hL hLsim
  have h7 : 7 ≤ A.L_sim := le_trans (seven_le_lsstLSimMin hm0 hL) hLsim
  have hid_mono : ∀ {a b : ℕ}, a ≤ b → Num.integerDivideSpace a ≤ Num.integerDivideSpace b := by
    intro a b hab
    dsimp only [Num.integerDivideSpace, Num.unsignedDivideSpace]
    nlinarith
  have hKw_id := hid_mono hKw_le
  have hKq_id := hid_mono hKq_le
  have hid_ge : 50 * A.L_sim ≤ Num.integerDivideSpace (2 * A.L_sim) := by
    dsimp only [Num.integerDivideSpace, Num.unsignedDivideSpace]
    nlinarith
  dsimp only [WideWord.lsstSpace, WideWord.weightsSpace]
  nlinarith

lemma lsstHeap_add_lsstSpace_le_lsfInitSpace (Q_AN : Program) (K_AN : ℝ)
    (A : InitArena) :
    A.lsstHeap + WideWord.lsstSpace Q_AN K_AN A.n0 (2 * A.m0) A.L_sim A.h ≤
      A.b + lsfStaticSize A.vCap A.eCap A.n0 A.n0 A.L_w +
        WideWord.lsstSpace Q_AN K_AN A.n0 (2 * A.m0) A.L_sim A.h +
        200 * (A.n0 + A.m0 + 1) * (A.L_w + A.L_sim + auxLogCap A.n0 + 20) + 1000 := by
  have hst := lsfStaticSize_tM_le A.vCap A.eCap A.n0 A.L_w
  dsimp only [InitArena.lsstHeap, InitArena.base, lsfEndAddr]
  nlinarith

end MinCostFlow.LSF.Program
