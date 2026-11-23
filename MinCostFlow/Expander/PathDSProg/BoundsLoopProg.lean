module

public import WordRAM.Logic
public import MinCostFlow.Expander.DecomposePhiProg
public import MinCostFlow.Expander.PathDSProg.Params

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared Word-RAM Loop Subroutines and Word Bounds for `BoundsProg`

Provides:
1. Word-size and logarithm helper lemmas (`bounds_word_le`, `fourthRoot_iff`, `eighthRoot_iff`).
2. `kthRootLoop` and `kthRootLoop_triple`: shared linear root finder used for both 4th roots
   (`csGammaExp`) and 8th roots (`qRoot`).
3. `csGammaExpBlock` and `csGammaExpBlock_triple`: computes `csGammaExp Kγ rIn`.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Arithmetic & Word-Size Helper Lemmas -/

lemma log2_three_mul_le (d M : ℕ) (hd : 1 ≤ d) :
    Nat.log 2 (3 * M) ≤ Nat.log 2 (d + M + 2) + 2 := by
  have hle : 3 * M ≤ (d + M + 2) * 2 * 2 := by omega
  have hlog : Nat.log 2 (3 * M) ≤ Nat.log 2 ((d + M + 2) * 2 * 2) := Nat.log_mono_right hle
  have hpos : d + M + 2 ≠ 0 := by omega
  have hpow : Nat.log 2 ((d + M + 2) * 2 * 2) = Nat.log 2 (d + M + 2) + 2 := by
    rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) hpos]
  omega

lemma log2_four_mul_le (d M : ℕ) (hd : 1 ≤ d) :
    Nat.log 2 (4 * M) ≤ Nat.log 2 (d + M + 2) + 2 := by
  have hle : 4 * M ≤ (d + M + 2) * 2 * 2 := by omega
  have hlog : Nat.log 2 (4 * M) ≤ Nat.log 2 ((d + M + 2) * 2 * 2) := Nat.log_mono_right hle
  have hpos : d + M + 2 ≠ 0 := by omega
  have hpow : Nat.log 2 ((d + M + 2) * 2 * 2) = Nat.log 2 (d + M + 2) + 2 := by
    rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) hpos]
  omega

lemma nat_log_lt_self_pos {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 n < n := by
  have h1 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_pow_self (by decide : 1 < 2)
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  omega

lemma fourthRoot_iff {s t : ℕ} :
    s = Nat.sqrt (Nat.sqrt t) ↔ s ^ 4 ≤ t ∧ t < (s + 1) ^ 4 := by
  constructor
  · rintro rfl
    have h1 : (Nat.sqrt (Nat.sqrt t)) ^ 2 ≤ Nat.sqrt t := by rw [sq]; exact Nat.sqrt_le _
    have h2 : Nat.sqrt t < (Nat.sqrt (Nat.sqrt t) + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt _
    have h3 : (Nat.sqrt t) ^ 2 ≤ t := by rw [sq]; exact Nat.sqrt_le _
    have h4 : t < (Nat.sqrt t + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt _
    rw [show (Nat.sqrt (Nat.sqrt t)) ^ 4 = ((Nat.sqrt (Nat.sqrt t)) ^ 2) ^ 2 by ring,
      show (Nat.sqrt (Nat.sqrt t) + 1) ^ 4 = ((Nat.sqrt (Nat.sqrt t) + 1) ^ 2) ^ 2 by ring]
    exact ⟨le_trans (Nat.pow_le_pow_left h1 2) h3, lt_of_lt_of_le h4 (Nat.pow_le_pow_left h2 2)⟩
  · rintro ⟨hle, hlt⟩
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring] at hle
    rw [show (s + 1) ^ 4 = ((s + 1) ^ 2) ^ 2 by ring] at hlt
    have hs1 : s ^ 2 ≤ Nat.sqrt t := (Nat.le_sqrt).mpr (by simpa [sq] using hle)
    have hs2 : Nat.sqrt t < (s + 1) ^ 2 := by
      by_contra hge
      have hge' : (s + 1) ^ 2 ≤ Nat.sqrt t := by omega
      have : ((s + 1) ^ 2) ^ 2 ≤ t := le_trans (Nat.pow_le_pow_left hge' 2) (by rw [sq]; exact Nat.sqrt_le _)
      omega
    have hlo : s ≤ Nat.sqrt (Nat.sqrt t) := (Nat.le_sqrt).mpr (by simpa [sq] using hs1)
    have hhi : Nat.sqrt (Nat.sqrt t) < s + 1 := by
      by_contra hge
      have hge' : s + 1 ≤ Nat.sqrt (Nat.sqrt t) := by omega
      have : (s + 1) ^ 2 ≤ Nat.sqrt t := le_trans (Nat.pow_le_pow_left hge' 2) (by rw [sq]; exact Nat.sqrt_le _)
      omega
    omega

lemma eighthRoot_iff {s t : ℕ} :
    s = Nat.sqrt (Nat.sqrt (Nat.sqrt t)) ↔ s ^ 8 ≤ t ∧ t < (s + 1) ^ 8 := by
  constructor
  · rintro rfl
    have ⟨h1, h2⟩ : (Nat.sqrt (Nat.sqrt (Nat.sqrt t))) ^ 4 ≤ Nat.sqrt t ∧
        Nat.sqrt t < (Nat.sqrt (Nat.sqrt (Nat.sqrt t)) + 1) ^ 4 :=
      fourthRoot_iff.mp rfl
    have h3 : (Nat.sqrt t) ^ 2 ≤ t := by rw [sq]; exact Nat.sqrt_le _
    have h4 : t < (Nat.sqrt t + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt _
    rw [show (Nat.sqrt (Nat.sqrt (Nat.sqrt t))) ^ 8 =
        ((Nat.sqrt (Nat.sqrt (Nat.sqrt t))) ^ 4) ^ 2 by ring,
      show (Nat.sqrt (Nat.sqrt (Nat.sqrt t)) + 1) ^ 8 =
        ((Nat.sqrt (Nat.sqrt (Nat.sqrt t)) + 1) ^ 4) ^ 2 by ring]
    exact ⟨le_trans (Nat.pow_le_pow_left h1 2) h3, lt_of_lt_of_le h4 (Nat.pow_le_pow_left h2 2)⟩
  · rintro ⟨hle, hlt⟩
    rw [show s ^ 8 = (s ^ 4) ^ 2 by ring] at hle
    rw [show (s + 1) ^ 8 = ((s + 1) ^ 4) ^ 2 by ring] at hlt
    have hs1 : s ^ 4 ≤ Nat.sqrt t := (Nat.le_sqrt).mpr (by simpa [sq] using hle)
    have hs2 : Nat.sqrt t < (s + 1) ^ 4 := by
      by_contra hge
      have : ((s + 1) ^ 4) ^ 2 ≤ t :=
        le_trans (Nat.pow_le_pow_left (by omega : (s + 1) ^ 4 ≤ Nat.sqrt t) 2) (by rw [sq]; exact Nat.sqrt_le _)
      omega
    exact fourthRoot_iff.mpr ⟨hs1, hs2⟩

lemma eighthRoot_succ_pow_le {M : ℕ} :
    (qRoot M + 1) ^ 8 ≤ 256 * (Nat.log 2 (M + 2) + 1) := by
  have hle : (qRoot M) ^ 8 ≤ Nat.log 2 (M + 2) := qRoot_pow_eight_le M
  rcases eq_or_ne (qRoot M) 0 with h0 | hne
  · rw [h0]; omega
  · have h2 : qRoot M + 1 ≤ 2 * qRoot M := by omega
    have hpow : (qRoot M + 1) ^ 8 ≤ (2 * qRoot M) ^ 8 := Nat.pow_le_pow_left h2 8
    have h256 : (2 * qRoot M) ^ 8 = 256 * (qRoot M) ^ 8 := by ring
    nlinarith

lemma bounds_word_le {Kγ c K_int cw_cs d M w : ℕ}
    (hd : 1 ≤ d)
    (hcw : max 24 (4 * cw_cs + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2) + 1) ≤ w) :
    let X := d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2
    600 ≤ X ∧ X ^ 24 < 2 ^ w ∧
      (1 ≤ c → Kγ < phiOutDenImpl Kγ c d M) ∧
      (1 ≤ K_int → Kγ < csExpFactor Kγ K_int M) ∧
      c < X ∧ K_int < X ∧ 190 ≤ gDelImpl K_int d M ∧ gDelImpl K_int d M < X ∧
      (Nat.log 2 (3 * M) + 2) ^ 4 < X ^ 8 ∧
      (Nat.log 2 (4 * M) + 2) ^ 4 < X ^ 8 ∧
      (qRoot M + 1) ^ 8 < X ^ 8 ∧
      ((Nat.log 2 (10 * d) + 2) ^ 2 + 1) ^ 3 < X ^ 8 := by
  intro X
  have hgexp : 480 ≤ gExpImpl Kγ c K_int d M := by
    have h2 : 2 ≤ phiOutDenImpl Kγ c d M := by unfold phiOutDenImpl; omega
    have h240 := two_hundred_forty_le_lenFactor M
    have hmul : 2 * 240 ≤ phiOutDenImpl Kγ c d M * lenFactor M := Nat.mul_le_mul h2 h240
    unfold gExpImpl; omega
  have hgdel190 : 190 ≤ gDelImpl K_int d M := by
    unfold gDelImpl; omega
  have hX_ge : 600 ≤ X := by dsimp [X]; omega
  have hX24 : X ^ 24 < 2 ^ w := by
    have hX_lt : X < 2 ^ (Nat.log 2 X + 1) := Nat.lt_pow_succ_log_self (by decide) X
    have h24 : 24 * (Nat.log 2 X + 1) ≤ w :=
      le_trans (Nat.mul_le_mul_right _ (le_max_left _ _)) hcw
    have hpow : X ^ 24 < (2 ^ (Nat.log 2 X + 1)) ^ 24 := Nat.pow_lt_pow_left hX_lt (by decide)
    have h2pow : (2 ^ (Nat.log 2 X + 1)) ^ 24 = 2 ^ (24 * (Nat.log 2 X + 1)) := by
      rw [← pow_mul]; ring_nf
    exact lt_of_lt_of_le (by rw [← h2pow]; exact hpow) (Nat.pow_le_pow_right (by decide) h24)
  have hc_lt : c < X := by
    have hgam1 : 1 ≤ Cited.csGamma Kγ (3 * M) := by
      unfold Cited.csGamma; exact Nat.one_le_pow _ _ (by decide)
    have hcm : c ≤ c * Cited.csGamma Kγ (3 * M) := Nat.le_mul_of_pos_right c hgam1
    have hphi : c ≤ phiOutDenImpl Kγ c d M := by
      unfold phiOutDenImpl; exact le_trans hcm (le_trans (le_max_right _ _) (le_max_right _ _))
    have hg := phiOutDenImpl_le_gExpImpl Kγ c K_int d M
    dsimp [X]; omega
  have hKint_lt : K_int < X := by
    have : K_int ≤ gDelImpl K_int d M := by unfold gDelImpl; omega
    dsimp [X]; omega
  have hgdel_lt : gDelImpl K_int d M < X := by dsimp [X]; omega
  have hKγ_c : 1 ≤ c → Kγ < phiOutDenImpl Kγ c d M := by
    intro hc1
    have h1 : Kγ ≤ csGammaExp Kγ (3 * M) := by
      unfold csGammaExp; exact Nat.le_mul_of_pos_right Kγ (Nat.succ_pos _)
    have h2 : csGammaExp Kγ (3 * M) < Cited.csGamma Kγ (3 * M) :=
      Nat.lt_pow_self (by decide : 1 < 2)
    have h3 : Cited.csGamma Kγ (3 * M) ≤ c * Cited.csGamma Kγ (3 * M) :=
      Nat.le_mul_of_pos_left _ hc1
    unfold phiOutDenImpl
    exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) (le_trans h3 (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hKγ_Kint : 1 ≤ K_int → Kγ < csExpFactor Kγ K_int M := by
    intro hk1
    have h1 : Kγ ≤ csGammaExp Kγ (4 * M) := by
      unfold csGammaExp; exact Nat.le_mul_of_pos_right Kγ (Nat.succ_pos _)
    have hq2 : 2 ≤ qOf M := qOf_ge_two M
    have h2 : csGammaExp Kγ (4 * M) ≤ csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M := by
      have hm1 : csGammaExp Kγ (4 * M) ≤ csGammaExp Kγ (4 * M) * (K_int * qOf M) :=
        Nat.le_mul_of_pos_right _ (by nlinarith)
      nlinarith
    have h3 : csGammaExp Kγ (4 * M) < 2 ^ (csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M) :=
      lt_of_le_of_lt h2 (Nat.lt_pow_self (by decide : 1 < 2))
    unfold csExpFactor
    omega
  have hlogX : Nat.log 2 X < X := nat_log_lt_self_pos (by omega)
  have hlog3 : (Nat.log 2 (3 * M) + 2) ^ 4 < X ^ 8 := by
    have h3x : 3 * M ≤ X * 2 * 2 := by dsimp [X]; omega
    have hl : Nat.log 2 (3 * M) ≤ Nat.log 2 X + 2 := by
      have h1 : Nat.log 2 (3 * M) ≤ Nat.log 2 (X * 2 * 2) := Nat.log_mono_right h3x
      have h2 : Nat.log 2 (X * 2 * 2) = Nat.log 2 X + 2 := by
        rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega)]
      omega
    have hbase : Nat.log 2 (3 * M) + 2 ≤ 2 * X := by omega
    have hpow : (Nat.log 2 (3 * M) + 2) ^ 4 ≤ (2 * X) ^ 4 := Nat.pow_le_pow_left hbase 4
    have h24 : (2 * X) ^ 4 = 16 * X ^ 4 := by ring
    have h16x : 16 * X ^ 4 < X ^ 5 := by nlinarith [Nat.one_le_pow 4 X (by omega)]
    have hx58 : X ^ 5 ≤ X ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hlog4 : (Nat.log 2 (4 * M) + 2) ^ 4 < X ^ 8 := by
    have h4x : 4 * M ≤ X * 2 * 2 := by dsimp [X]; omega
    have hl : Nat.log 2 (4 * M) ≤ Nat.log 2 X + 2 := by
      have h1 : Nat.log 2 (4 * M) ≤ Nat.log 2 (X * 2 * 2) := Nat.log_mono_right h4x
      have h2 : Nat.log 2 (X * 2 * 2) = Nat.log 2 X + 2 := by
        rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega)]
      omega
    have hbase : Nat.log 2 (4 * M) + 2 ≤ 2 * X := by omega
    have hpow : (Nat.log 2 (4 * M) + 2) ^ 4 ≤ (2 * X) ^ 4 := Nat.pow_le_pow_left hbase 4
    have h24 : (2 * X) ^ 4 = 16 * X ^ 4 := by ring
    have h16x : 16 * X ^ 4 < X ^ 5 := by nlinarith [Nat.one_le_pow 4 X (by omega)]
    have hx58 : X ^ 5 ≤ X ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hlog8 : (qRoot M + 1) ^ 8 < X ^ 8 := by
    have hm2 : Nat.log 2 (M + 2) ≤ X := by
      have : Nat.log 2 (M + 2) ≤ M + 2 := le_of_lt (nat_log_lt_self_pos (by omega))
      dsimp [X]; omega
    have hbd := eighthRoot_succ_pow_le (M := M)
    have h1 : 256 * (Nat.log 2 (M + 2) + 1) ≤ 512 * X := by nlinarith
    have hx2 : 512 * X < X ^ 2 := by nlinarith
    have hx28 : X ^ 2 ≤ X ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hlog10 : ((Nat.log 2 (10 * d) + 2) ^ 2 + 1) ^ 3 < X ^ 8 := by
    have h10x : 10 * d ≤ X * 2 * 2 * 2 * 2 := by dsimp [X]; omega
    have hl : Nat.log 2 (10 * d) ≤ Nat.log 2 X + 4 := by
      have h1 : Nat.log 2 (10 * d) ≤ Nat.log 2 (X * 2 * 2 * 2 * 2) := Nat.log_mono_right h10x
      have h2 : Nat.log 2 (X * 2 * 2 * 2 * 2) = Nat.log 2 X + 4 := by
        rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega),
          Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega)]
      omega
    have hbase : Nat.log 2 (10 * d) + 2 ≤ 2 * X := by omega
    have hsq : (Nat.log 2 (10 * d) + 2) ^ 2 + 1 ≤ 5 * X ^ 2 := by
      have := Nat.pow_le_pow_left hbase 2
      nlinarith
    have hcube : ((Nat.log 2 (10 * d) + 2) ^ 2 + 1) ^ 3 ≤ (5 * X ^ 2) ^ 3 :=
      Nat.pow_le_pow_left hsq 3
    have h53 : (5 * X ^ 2) ^ 3 = 125 * X ^ 6 := by ring
    have hlt7 : 125 * X ^ 6 < X ^ 7 := by nlinarith [Nat.one_le_pow 6 X (by omega)]
    have hx78 : X ^ 7 ≤ X ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  exact ⟨hX_ge, hX24, hKγ_c, hKγ_Kint, hc_lt, hKint_lt, hgdel190, hgdel_lt,
    hlog3, hlog4, hlog8, hlog10⟩

/-! ## 2. Shared Loop Subroutines (`kthRootLoop`, `csGammaExpBlock`) -/

/-- Fourth-power expression `((reg r)^2) * ((reg r)^2)` (`size = 7`). -/
def pow4Expr (r : ℕ) : Expr :=
  .bin .mul (.bin .mul (.reg r) (.reg r)) (.bin .mul (.reg r) (.reg r))

/-- Eighth-power expression `pow4Expr r * pow4Expr r` (`size = 15`). -/
def pow8Expr (r : ℕ) : Expr :=
  .bin .mul (pow4Expr r) (pow4Expr r)

@[simp] lemma pow4Expr_size (r : ℕ) : (pow4Expr r).size = 7 := by simp [pow4Expr]
@[simp] lemma pow8Expr_size (r : ℕ) : (pow8Expr r).size = 15 := by simp [pow8Expr, pow4Expr]

lemma pow4Expr_eval {w r x : ℕ} {st : State} (hr : st.regs r = x) (hx4 : x ^ 4 < 2 ^ w) :
    (pow4Expr r).eval w st = some (x ^ 4) := by
  have hx2 : x * x < 2 ^ w := by
    have : x * x ≤ x ^ 4 := by
      rcases x with _ | x'
      · omega
      · nlinarith [show (x' + 1) ^ 4 = ((x' + 1) * (x' + 1)) * ((x' + 1) * (x' + 1)) by ring]
    omega
  have hx4' : (x * x) * (x * x) = x ^ 4 := by ring
  simpa only [pow4Expr, hx4'] using
    Expr.eval_mul (Expr.eval_mul (Expr.eval_reg_of_eq hr) (Expr.eval_reg_of_eq hr) hx2)
      (Expr.eval_mul (Expr.eval_reg_of_eq hr) (Expr.eval_reg_of_eq hr) hx2) (by rw [hx4']; exact hx4)

lemma pow8Expr_eval {w r x : ℕ} {st : State} (hr : st.regs r = x) (hx8 : x ^ 8 < 2 ^ w) :
    (pow8Expr r).eval w st = some (x ^ 8) := by
  have hx4 : x ^ 4 < 2 ^ w := by
    have : x ^ 4 ≤ x ^ 8 := by
      rcases x with _ | x'
      · omega
      · have : 1 ≤ (x' + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
        nlinarith [show (x' + 1) ^ 8 = (x' + 1) ^ 4 * (x' + 1) ^ 4 by ring]
    omega
  have hx8' : x ^ 4 * x ^ 4 = x ^ 8 := by ring
  simpa only [pow8Expr, hx8'] using
    Expr.eval_mul (pow4Expr_eval hr hx4) (pow4Expr_eval hr hx4) (by rw [hx8']; exact hx8)

/-- Linear root-finding loop: increments `rRoot` while `powE < rT + 1`, maintaining `rCur = rRoot + 1`. -/
def kthRootLoop (rRoot rCur rT : ℕ) (powE : Expr) : Stmt :=
  .loop (.bin .lt powE (.bin .add (.reg rT) (.const 1)))
    (.assign rRoot (.bin .add (.reg rRoot) (.const 1)) ;;
     .assign rCur (.bin .add (.reg rRoot) (.const 1)))

lemma kthRootLoop_noRand (rRoot rCur rT : ℕ) (powE : Expr) :
    (kthRootLoop rRoot rCur rT powE).NoRand := by
  simp [kthRootLoop, Stmt.NoRand]

/-- Generic `Triple` for `kthRootLoop` parameterized by exponent `k ≥ 1` and power expression `powE`. -/
theorem kthRootLoop_triple {w : ℕ} {p : Program}
    (rRoot rCur rT k target ans : ℕ) (powE : Expr)
    (hnd : [rRoot, rCur, rT].Nodup)
    (hk : 1 ≤ k)
    (hans : ans ^ k ≤ target ∧ target < (ans + 1) ^ k)
    (hpow_eval : ∀ st, st.regs rCur ≤ ans + 1 → powE.eval w st = some (st.regs rCur ^ k))
    (ht2w : target + 1 < 2 ^ w) (hpow2w : (ans + 1) ^ k < 2 ^ w)
    (st₀ : State) (hrr₀ : st₀.regs rRoot = 0) (hrc₀ : st₀.regs rCur = 1) (hrt₀ : st₀.regs rT = target) :
    Triple w p (fun st => st = st₀) (kthRootLoop rRoot rCur rT powE)
      (normalPost fun st' => st'.regs rRoot = ans ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        ∀ r, r ≠ rRoot → r ≠ rCur → st'.regs r = st₀.regs r)
      (fun _ => (powE.size + 14) * ans + (powE.size + 5)) := by
  have hrc_ne : rRoot ≠ rCur := fun h => by subst h; simp at hnd
  have hrt_ne : rRoot ≠ rT := fun h => by subst h; simp at hnd
  have hct_ne : rCur ≠ rT := fun h => by subst h; simp at hnd
  have h1w : 1 < 2 ^ w := by omega
  have hans_lt_2w : ans + 1 < 2 ^ w := by
    have : ans + 1 ≤ (ans + 1) ^ k := Nat.le_self_pow (by omega) _
    omega
  let Inv : State → Prop := fun st =>
    st.regs rT = target ∧ st.regs rCur = st.regs rRoot + 1 ∧ st.regs rRoot ≤ ans ∧
      st.mem = st₀.mem ∧ st.pos = st₀.pos ∧ (∀ r, r ≠ rRoot → r ≠ rCur → st.regs r = st₀.regs r)
  have hloop := Triple.loop_const_normal (p := p) (w := w)
    (e := .bin .lt powE (.bin .add (.reg rT) (.const 1)))
    (body := .assign rRoot (.bin .add (.reg rRoot) (.const 1)) ;;
      .assign rCur (.bin .add (.reg rRoot) (.const 1)))
    (Inv := Inv)
    (Q := fun st' => st'.regs rRoot = ans ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
      ∀ r, r ≠ rRoot → r ≠ rCur → st'.regs r = st₀.regs r)
    (m := fun st => ans - st.regs rRoot)
    (condVal := fun st => if st.regs rCur ^ k < target + 1 then 1 else 0)
    (bodyBound := 9)
    (hcond := fun st hInv => by
      rcases hInv with ⟨hrt, hrc, hle, _, _, _⟩
      have he1 : powE.eval w st = some (st.regs rCur ^ k) := hpow_eval st (by omega)
      have he2 : (Expr.bin .add (.reg rT) (.const 1)).eval w st = some (target + 1) :=
        Expr.eval_add (Expr.eval_reg_of_eq hrt) (Expr.eval_const h1w) ht2w
      exact Expr.eval_lt_op he1 he2 h1w)
    (hexit := fun st hInv hv => by
      rcases hInv with ⟨hrt, hrc, hle, hm, hp, hf⟩
      have hge : target + 1 ≤ (st.regs rRoot + 1) ^ k := by
        by_contra hlt
        simp [hrc, show (st.regs rRoot + 1) ^ k < target + 1 by omega] at hv
      have heq : st.regs rRoot = ans := by
        by_contra hne
        have hlt1 : st.regs rRoot + 1 ≤ ans := by omega
        have hpow_le : (st.regs rRoot + 1) ^ k ≤ ans ^ k := Nat.pow_le_pow_left hlt1 k
        omega
      exact ⟨heq, hm, hp, hf⟩)
    (hstep := fun st hInv hv => by
      rcases hInv with ⟨hrt, hrc, hle, hm, hp, hf⟩
      have hlt_pow : (st.regs rRoot + 1) ^ k < target + 1 := by
        by_contra hge
        have : ¬ st.regs rCur ^ k < target + 1 := by rw [hrc]; exact hge
        simp [this] at hv
      have hlt_ans : st.regs rRoot < ans := by
        by_contra hge
        have heq : st.regs rRoot = ans := by omega
        rw [heq] at hlt_pow
        omega
      have ha1 : st.regs rRoot + 1 < 2 ^ w := by omega
      have ha2 : st.regs rRoot + 2 < 2 ^ w := by omega
      intro s ω' hs; subst s
      let st₁ : State := { st with regs := Function.update st.regs rRoot (st.regs rRoot + 1) }
      let st₂ : State := { st₁ with regs := Function.update st₁.regs rCur (st.regs rRoot + 2) }
      have hr1 : Runs w p ω' (.assign rRoot (.bin .add (.reg rRoot) (.const 1))) st .normal st₁ 4 :=
        runs_assign_iff.mpr ⟨st.regs rRoot + 1,
          Expr.eval_add (Expr.eval_reg _ _ _) (Expr.eval_const h1w) ha1, rfl, rfl, by simp⟩
      have hr2 : Runs w p ω' (.assign rCur (.bin .add (.reg rRoot) (.const 1))) st₁ .normal st₂ 4 :=
        runs_assign_iff.mpr ⟨st.regs rRoot + 2,
          Expr.eval_eq_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp [st₁]; rw [Function.update_self]))
              (Expr.eval_const h1w) ha2) (by omega), rfl, rfl, by simp⟩
      refine ⟨.normal, st₂, 9, runs_seq_iff.mpr (Or.inr ⟨st₁, 4, 4, hr1, hr2, rfl⟩), ?_, le_rfl⟩
      refine ⟨⟨?_, ?_, ?_, hm, hp, ?_⟩, ?_⟩
      · dsimp [st₂, st₁]
        rw [Function.update_of_ne hct_ne.symm, Function.update_of_ne hrt_ne.symm, hrt]
      · dsimp [st₂, st₁]
        rw [Function.update_self, Function.update_of_ne hrc_ne, Function.update_self]
      · dsimp [st₂, st₁]
        rw [Function.update_of_ne hrc_ne, Function.update_self]
        omega
      · intro r hr1' hr2'
        dsimp [st₂, st₁]
        rw [Function.update_of_ne hr2', Function.update_of_ne hr1']
        exact hf r hr1' hr2'
      · dsimp [st₂, st₁]
        rw [Function.update_of_ne hrc_ne, Function.update_self]
        omega)
  refine hloop.conseq (by
      intro s hs; subst s
      dsimp only [Inv]
      rw [hrr₀, hrc₀]
      exact ⟨hrt₀, by omega, Nat.zero_le _, rfl, rfl, fun _ _ _ => rfl⟩)
    (fun o s' hq => hq)
    (by
      intro s hs; subst s
      rw [hrr₀, Nat.sub_zero]
      have hsz : (Expr.bin .lt powE (.bin .add (.reg rT) (.const 1))).size = powE.size + 4 := by
        simp
      rw [hsz, show powE.size + 4 + 9 + 1 = powE.size + 14 by omega]
      omega)

/-- `Triple` wrapper around `DecomposePhiProg.log2_loop_runs`. -/
lemma log2Loop_triple {w : ℕ} {p : Program}
    (rCur rCnt x : ℕ) (hne : rCur ≠ rCnt) (hx : x < 2 ^ w) (h4 : 4 ≤ 2 ^ w)
    (hk2w : Nat.log 2 x < 2 ^ w) (st₀ : State) (hrc : st₀.regs rCur = x) (hrk : st₀.regs rCnt = 0) :
    Triple w p (fun st => st = st₀)
      (.loop (.bin .lt (.const 1) (.reg rCur))
        (.assign rCur (.bin .div (.reg rCur) (.const 2)) ;;
         .assign rCnt (.bin .add (.reg rCnt) (.const 1))))
      (normalPost fun st' => st'.regs rCnt = Nat.log 2 x ∧ st'.mem = st₀.mem ∧
        st'.pos = st₀.pos ∧ ∀ r, r ≠ rCur → r ≠ rCnt → st'.regs r = st₀.regs r)
      (fun _ => 13 * (Nat.log 2 x + 1)) := by
  intro s ω hs; subst s
  obtain ⟨st', c, hr, hrCnt, hm, hp, hf, hc⟩ :=
    log2_loop_runs (w := w) (p := p) (ω := ω) rCur rCnt hne x hx h4 st₀ hrc hrk hk2w
  exact ⟨.normal, st', c, by simpa only [seqStmts] using hr, ⟨hrCnt, hm, hp, hf⟩, hc⟩

/-- Block computing `rOut := csGammaExp Kγ (st.regs rIn)` using scratch regs `{rCur, rCnt, rT, rRoot}`. -/
def csGammaExpBlock (Kγ rIn rOut rCur rCnt rT rRoot : ℕ) : Stmt :=
  .assign rCur (.reg rIn) ;;
  .assign rCnt (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg rCur))
    (.assign rCur (.bin .div (.reg rCur) (.const 2)) ;;
     .assign rCnt (.bin .add (.reg rCnt) (.const 1))) ;;
  .assign rT (.bin .mul (.bin .mul (.bin .add (.reg rCnt) (.const 1)) (.bin .add (.reg rCnt) (.const 1)))
    (.bin .add (.reg rCnt) (.const 1))) ;;
  .assign rRoot (.const 0) ;;
  .assign rCur (.const 1) ;;
  kthRootLoop rRoot rCur rT (pow4Expr rCur) ;;
  .assign rOut (.bin .mul (.const Kγ) (.bin .add (.reg rRoot) (.const 1)))

lemma csGammaExpBlock_noRand (Kγ rIn rOut rCur rCnt rT rRoot : ℕ) :
    (csGammaExpBlock Kγ rIn rOut rCur rCnt rT rRoot).NoRand := by
  simp [csGammaExpBlock, kthRootLoop_noRand, Stmt.NoRand]

theorem csGammaExpBlock_triple {w : ℕ} {p : Program}
    (Kγ rIn rOut rCur rCnt rT rRoot x : ℕ)
    (hnd : [rOut, rCur, rCnt, rT, rRoot].Nodup) (hin : rIn ≠ rCur ∧ rIn ≠ rCnt)
    (hK_lt : Kγ < 2 ^ w) (hx_lt : x < 2 ^ w) (hcube_lt : (Nat.log 2 x + 2) ^ 4 < 2 ^ w)
    (hcs_lt : csGammaExp Kγ x < 2 ^ w) (h4 : 4 ≤ 2 ^ w) (st₀ : State) (hrIn : st₀.regs rIn = x) :
    Triple w p (fun st => st = st₀) (csGammaExpBlock Kγ rIn rOut rCur rCnt rT rRoot)
      (normalPost fun st' => st'.regs rOut = csGammaExp Kγ x ∧ st'.mem = st₀.mem ∧
        st'.pos = st₀.pos ∧
        ∀ r, r ≠ rOut → r ≠ rCur → r ≠ rCnt → r ≠ rT → r ≠ rRoot → st'.regs r = st₀.regs r)
      (fun _ => 35 * (Nat.log 2 x + 1) + 60) := by
  have ho_c : rOut ≠ rCur := fun h => by subst h; simp at hnd
  have ho_k : rOut ≠ rCnt := fun h => by subst h; simp at hnd
  have ho_t : rOut ≠ rT := fun h => by subst h; simp at hnd
  have ho_r : rOut ≠ rRoot := fun h => by subst h; simp at hnd
  have hc_k : rCur ≠ rCnt := fun h => by subst h; simp at hnd
  have hc_t : rCur ≠ rT := fun h => by subst h; simp at hnd
  have hc_r : rCur ≠ rRoot := fun h => by subst h; simp at hnd
  have hk_t : rCnt ≠ rT := fun h => by subst h; simp at hnd
  have hk_r : rCnt ≠ rRoot := fun h => by subst h; simp at hnd
  have ht_r : rT ≠ rRoot := fun h => by subst h; simp at hnd
  set l := Nat.log 2 x
  set tgt := (l + 1) ^ 3
  set ans := Nat.sqrt (Nat.sqrt tgt)
  have h1w : 1 < 2 ^ w := by omega
  have hl_lt : l < 2 ^ w := by
    have : l ≤ (l + 2) ^ 4 := by
      have h41 : l + 2 ≤ (l + 2) ^ 4 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ l + 2) (by decide : 1 ≤ 4)
      omega
    omega
  have hl1_lt : l + 1 < 2 ^ w := by
    have : l + 1 ≤ (l + 2) ^ 4 := by
      have h41 : l + 2 ≤ (l + 2) ^ 4 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ l + 2) (by decide : 1 ≤ 4)
      omega
    omega
  have hl2_lt : (l + 1) * (l + 1) < 2 ^ w := by
    have : (l + 1) * (l + 1) ≤ (l + 2) ^ 4 := by nlinarith
    omega
  have ht_lt : tgt < 2 ^ w := by
    have : tgt ≤ (l + 2) ^ 4 := by
      dsimp [tgt]
      have : (l + 1) ^ 3 ≤ (l + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      nlinarith
    omega
  have hans_bounds : ans ^ 4 ≤ tgt ∧ tgt < (ans + 1) ^ 4 := fourthRoot_iff.mp rfl
  have hans_le_l1 : ans ≤ l + 1 := by
    by_contra hgt
    have hge : l + 2 ≤ ans := by omega
    have h1 : (l + 2) ^ 4 ≤ ans ^ 4 := Nat.pow_le_pow_left hge 4
    have h2 : tgt < (l + 2) ^ 4 := by
      dsimp [tgt]
      nlinarith [show (l + 1) ^ 3 ≤ (l + 2) ^ 3 from Nat.pow_le_pow_left (by omega) 3]
    omega
  have hans4_lt : (ans + 1) ^ 4 < 2 ^ w := by
    have h1 : ans + 1 ≤ l + 2 := by omega
    exact lt_of_le_of_lt (Nat.pow_le_pow_left h1 4) hcube_lt
  have ht1_lt : tgt + 1 < 2 ^ w := by
    have : tgt + 1 ≤ (l + 2) ^ 4 := by
      dsimp [tgt]; nlinarith [show (l + 1) ^ 3 < (l + 2) ^ 3 by nlinarith]
    omega
  have hans1_lt : ans + 1 < 2 ^ w := by
    have : ans + 1 ≤ (ans + 1) ^ 4 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ ans + 1) (by decide : 1 ≤ 4)
    omega
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  let st1 : State := { st with regs := Function.update st.regs rCur x }
  refine runs_seq_assign_le (v := x) (Expr.eval_reg_of_eq hrIn) ?_
  let st2 : State := { st1 with regs := Function.update st1.regs rCnt 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hr3_tr := log2Loop_triple (w := w) (p := p) rCur rCnt x hc_k hx_lt h4 hl_lt st2
    (by dsimp [st2, st1]; rw [Function.update_of_ne hc_k, Function.update_self])
    (by simp [st2])
  refine runs_seq_triple_le hr3_tr rfl ?_
  intro st3 ⟨hrc3, hm3, hp3, hreg3⟩
  let st4 : State := { st3 with regs := Function.update st3.regs rT tgt }
  have he4 : (Expr.bin .mul
      (.bin .mul (.bin .add (.reg rCnt) (.const 1)) (.bin .add (.reg rCnt) (.const 1)))
      (.bin .add (.reg rCnt) (.const 1))).eval w st3 = some tgt := by
    have ha := Expr.eval_add (Expr.eval_reg_of_eq hrc3) (Expr.eval_const h1w) hl1_lt
    have hm1 := Expr.eval_mul ha ha hl2_lt
    have hm2 := Expr.eval_mul hm1 ha (by
      simpa [tgt, l, pow_three, mul_assoc] using ht_lt)
    simpa [tgt, l, pow_three, mul_assoc] using hm2
  refine runs_seq_assign_le (v := tgt) he4 ?_
  let st5 : State := { st4 with regs := Function.update st4.regs rRoot 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st6 : State := { st5 with regs := Function.update st5.regs rCur 1 }
  refine runs_seq_assign_le (v := 1) (Expr.eval_const h1w) ?_
  have hr7_tr := kthRootLoop_triple (w := w) (p := p) rRoot rCur rT 4 tgt ans (pow4Expr rCur)
    (by simp [List.nodup_cons, hc_r.symm, ht_r.symm, hc_t]) (by decide) hans_bounds
    (fun s hs => pow4Expr_eval rfl (lt_of_le_of_lt (Nat.pow_le_pow_left hs 4) hans4_lt))
    ht1_lt hans4_lt st6
    (by dsimp [st6, st5]; rw [Function.update_of_ne hc_r.symm, Function.update_self])
    (by simp [st6])
    (by dsimp [st6, st5, st4]
        rw [Function.update_of_ne hc_t.symm, Function.update_of_ne ht_r, Function.update_self])
  refine runs_seq_triple_le hr7_tr rfl ?_
  intro st7 hst7
  rcases hst7 with ⟨hr7_ans, hm7, hp7, hf7⟩
  have he_out : (Expr.bin .mul (.const Kγ) (.bin .add (.reg rRoot) (.const 1))).eval w st7 =
      some (csGammaExp Kγ x) := by
    have ha := Expr.eval_add (Expr.eval_reg_of_eq hr7_ans) (Expr.eval_const h1w) hans1_lt
    have hmul := Expr.eval_mul (Expr.eval_const hK_lt) ha (by simpa [csGammaExp, ans, tgt, l] using hcs_lt)
    simpa [csGammaExp, ans, tgt, l] using hmul
  refine runs_assign_le (v := csGammaExp Kγ x) he_out ?_ ?_
  · refine ⟨Function.update_self _ _ _, ?_, ?_, ?_⟩
    · rw [hm7, hm3]
    · rw [hp7, hp3]
    · intro r hrO hrC hrK hrT hrR
      dsimp only
      rw [Function.update_of_ne hrO, hf7 r hrR hrC]
      dsimp [st6, st5, st4]
      rw [Function.update_of_ne hrC, Function.update_of_ne hrR, Function.update_of_ne hrT,
        hreg3 r hrC hrK]
      dsimp [st2, st1]
      rw [Function.update_of_ne hrK, Function.update_of_ne hrC]
  · simp only [pow4Expr_size, Expr.size]
    omega

end MinCostFlow.Expander.PathDSProg
