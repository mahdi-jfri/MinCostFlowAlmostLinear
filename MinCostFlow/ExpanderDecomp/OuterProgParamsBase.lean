module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.Params
public import MinCostFlow.ExpanderDecomp.OuterCorePlayer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM Parameter Computation Procedures (`OuterProgParams`)

Implements and verifies two deterministic (`NoRand`) Word-RAM procedures that compute all integer
parameters of `Params.lean` and `coreLevel` (`OuterCorePlayer.lean`) from the runtime input
`(n, M, r)` without hardcoding any input-dependent constants:

1. `computeParamsProc cfg`: given `args = [n, M, r, pAddr]` with `1 ≤ r ≤ ell M`, writes the
   12-word parameter block `OuterParamBlockAt mem' pAddr cfg n M r` containing
   `[n, M, r, ell M, LParam M, NOf M r, tParam M, bOut cfg M, Lambda cfg M r, DOut cfg M r, QOut cfg M r, 49 * LParam M + 1]`
   in `O(ell M + r + 1)` steps, preserving all memory outside `[pAddr, pAddr + 12)`.
2. `coreLevelProc`: given `args = [N, p]` with `2 ≤ N` and `1 ≤ p`, computes `Nat.clog N p`
   (which equals `coreLevel M r p` when `N = NOf M r`) in `O(Nat.clog N p + 1)` steps without
   modifying memory.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM

/-! ## 1. Parameter Block Layout -/

/-- Twelve-word read-only parameter block stored at `pAddr` for the outer decomposition. -/
def OuterParamBlockAt (mem : ℕ → ℕ) (pAddr : ℕ) (cfg : ParamConfig) (n M r : ℕ) : Prop :=
  mem (pAddr + 0) = n ∧
  mem (pAddr + 1) = M ∧
  mem (pAddr + 2) = r ∧
  mem (pAddr + 3) = ell M ∧
  mem (pAddr + 4) = LParam M ∧
  mem (pAddr + 5) = NOf M r ∧
  mem (pAddr + 6) = tParam M ∧
  mem (pAddr + 7) = bOut cfg M ∧
  mem (pAddr + 8) = Lambda cfg M r ∧
  mem (pAddr + 9) = DOut cfg M r ∧
  mem (pAddr + 10) = QOut cfg M r ∧
  mem (pAddr + 11) = 49 * LParam M + 1

/-! ## 2. `coreLevelProc`: Computing `Nat.clog N p` -/

/-- Deterministic Word-RAM procedure computing `Nat.clog N p` from `args = [N, p]`. -/
def coreLevelProc : Stmt :=
  .assign 2 (.const 0) ;;
  .assign 3 (.const 1) ;;
  .loop (.bin .lt (.reg 3) (.reg 1))
    (.assign 3 (.bin .mul (.reg 3) (.reg 0)) ;;
     .assign 2 (.bin .add (.reg 2) (.const 1))) ;;
  .ret (.reg 2)

/-- Explicit step bound for `coreLevelProc`. -/
def coreLevelProcCost (N p : ℕ) : ℕ :=
  25 * (Nat.clog N p + 1) + 20

/-- Contract for `coreLevelProc`: returns `Nat.clog N p` without modifying memory. -/
def coreLevelContract (w : ℕ) : Contract where
  pre args _mem :=
    ∃ N p, args = [N, p] ∧ 2 ≤ N ∧ 1 ≤ p ∧ N * p + 16 < 2 ^ w
  post args mem v mem' :=
    v = Nat.clog (args.getD 0 0) (args.getD 1 0) ∧ mem' = mem
  cost args _mem :=
    coreLevelProcCost (args.getD 0 0) (args.getD 1 0)

/-! ## 3. `computeParamsProc`: Computing the Outer Parameter Block -/

/-- Word-size bound ensuring every intermediate value of `computeParamsProc` fits `< 2 ^ w`. -/
def ComputeParamsWordBound (w : ℕ) (cfg : ParamConfig) (n M r pAddr : ℕ) : Prop :=
  pAddr + 12 < 2 ^ w ∧
  n < 2 ^ w ∧
  4 * M + 32 < 2 ^ w ∧
  QOut cfg M r + 16 < 2 ^ w ∧
  1920 * cfg.a₀ + 16 < 2 ^ w ∧
  16 * cfg.kappa * cfg.E + 16 < 2 ^ w ∧
  16 * cfg.A + 16 < 2 ^ w

/-- Stage A of `computeParamsProc`: compute `t, dCore, RCore, F` into `r11..r14` and `r15 := 1`. -/
def computeCoreFStmt (cfg : ParamConfig) : Stmt :=
  (.assign 11 (.bin .mul (.const 1024) (.reg 7)) ;;
   .assign 12 (.bin .mul (.const 3200) (.reg 11)) ;;
   .assign 12 (.bin .mul (.reg 12) (.reg 7))) ;;
  (.assign 13 (.bin .mul (.const 1600) (.reg 11)) ;;
   .assign 13 (.bin .mul (.reg 13) (.bin .add (.reg 12) (.const 1))) ;;
   .assign 13 (.bin .mul (.reg 13) (.reg 7))) ;;
  (.assign 14 (.bin .mul (.const (1920 * cfg.a₀)) (.reg 11)) ;;
   .assign 14 (.bin .mul (.reg 14) (.reg 11)) ;;
   .assign 14 (.bin .mul (.reg 14) (.reg 13)) ;;
   .assign 15 (.const 1))

/-- Stage B of `computeParamsProc`: compute `bOut, dOut, ROut, Lambda, DOut, QOut, 49*L+1` into
`r16..r22`. -/
def computeOuterQStmt (cfg : ParamConfig) : Stmt :=
  (.assign 16 (.bin .mul (.const (16 * cfg.kappa)) (.bin .add (.reg 7) (.const 1))) ;;
   .assign 16 (.bin .mul (.reg 16) (.const cfg.E)) ;;
   .assign 17 (.bin .mul (.const 320) (.reg 16)) ;;
   .assign 17 (.bin .mul (.reg 17) (.reg 7))) ;;
  (.assign 18 (.bin .mul (.const 160) (.reg 16)) ;;
   .assign 18 (.bin .mul (.reg 18) (.bin .add (.reg 17) (.const 1))) ;;
   .assign 18 (.bin .mul (.reg 18) (.reg 7))) ;;
  (.assign 19 (.bin .mul (.const 2) (.reg 15)) ;;
   .assign 19 (.bin .mul (.reg 19) (.reg 11)) ;;
   .assign 19 (.bin .mul (.reg 19) (.reg 18)) ;;
   .assign 19 (.bin .mul (.reg 19) (.bin .add (.reg 11) (.const 1)))) ;;
  (.assign 20 (.bin .mul (.const (16 * cfg.A)) (.reg 11)) ;;
   .assign 20 (.bin .mul (.reg 20) (.reg 19)) ;;
   .assign 20 (.bin .mul (.reg 20) (.reg 16)) ;;
   .assign 21 (.bin .add (.bin .mul (.const 2) (.reg 20)) (.const 2)) ;;
   .assign 22 (.bin .add (.bin .mul (.const 49) (.reg 7)) (.const 1)))

/-- Stage C of `computeParamsProc`: store all 12 parameter words at `pAddr + 0 .. pAddr + 11`. -/
def storeParamsStmt : Stmt :=
  (.store (.bin .add (.reg 3) (.const 0)) (.reg 0) ;;
   .store (.bin .add (.reg 3) (.const 1)) (.reg 1) ;;
   .store (.bin .add (.reg 3) (.const 2)) (.reg 2) ;;
   .store (.bin .add (.reg 3) (.const 3)) (.reg 5)) ;;
  (.store (.bin .add (.reg 3) (.const 4)) (.reg 7) ;;
   .store (.bin .add (.reg 3) (.const 5)) (.reg 9) ;;
   .store (.bin .add (.reg 3) (.const 6)) (.reg 11) ;;
   .store (.bin .add (.reg 3) (.const 7)) (.reg 16)) ;;
  (.store (.bin .add (.reg 3) (.const 8)) (.reg 19) ;;
   .store (.bin .add (.reg 3) (.const 9)) (.reg 20) ;;
   .store (.bin .add (.reg 3) (.const 10)) (.reg 21) ;;
   .store (.bin .add (.reg 3) (.const 11)) (.reg 22))

/-- Deterministic Word-RAM procedure computing all 12 words of `OuterParamBlockAt` at `pAddr` from
`args = [n, M, r, pAddr]`. Only the fixed configuration constants of `cfg` appear in the body. -/
def computeParamsProc (cfg : ParamConfig) : Stmt :=
  .assign 4 (.bin .add (.bin .mul (.const 2) (.reg 1)) (.const 2)) ;;
  .assign 5 (.const 0) ;;
  .assign 6 (.const 1) ;;
  .loop (.bin .lt (.reg 6) (.reg 4))
    (.assign 6 (.bin .mul (.const 2) (.reg 6)) ;;
     .assign 5 (.bin .add (.reg 5) (.const 1))) ;;
  .assign 7 (.bin .mul (.const 4) (.reg 5)) ;;
  .assign 8 (.bin .div (.bin .sub (.bin .add (.reg 5) (.reg 2)) (.const 1)) (.reg 2)) ;;
  .cond (.bin .lt (.reg 8) (.const 2)) (.assign 8 (.const 2)) .nop ;;
  .assign 9 (.const 1) ;;
  forRange 10 (.const 0) (.reg 8) (.assign 9 (.bin .mul (.const 2) (.reg 9))) ;;
  computeCoreFStmt cfg ;;
  forRange 10 (.const 0) (.reg 2) (.assign 15 (.bin .mul (.reg 15) (.reg 14))) ;;
  computeOuterQStmt cfg ;;
  storeParamsStmt ;;
  .ret (.const 0)

/-- Explicit step bound for `computeParamsProc`. -/
def computeParamsCost (M r : ℕ) : ℕ :=
  60 * (ell M + r + 1) + 500

/-- Contract for `computeParamsProc cfg`: writes `OuterParamBlockAt mem' pAddr cfg n M r` and
preserves all memory outside `[pAddr, pAddr + 12)`. -/
def computeParamsContract (cfg : ParamConfig) (w : ℕ) : Contract where
  pre args _mem :=
    ∃ n M r pAddr,
      args = [n, M, r, pAddr] ∧
      1 ≤ r ∧ r ≤ ell M ∧
      ComputeParamsWordBound w cfg n M r pAddr
  post args mem v mem' :=
    let n := args.getD 0 0
    let M := args.getD 1 0
    let r := args.getD 2 0
    let pAddr := args.getD 3 0
    v = 0 ∧
    OuterParamBlockAt mem' pAddr cfg n M r ∧
    (∀ a, a < pAddr ∨ pAddr + 12 ≤ a → mem' a = mem a)
  cost args _mem :=
    computeParamsCost (args.getD 1 0) (args.getD 2 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM

lemma coreLevelProc_noRand : coreLevelProc.NoRand := by
  simp [coreLevelProc, Stmt.NoRand]

lemma computeParamsProc_noRand (cfg : ParamConfig) : (computeParamsProc cfg).NoRand := by
  simp [computeParamsProc, computeCoreFStmt, computeOuterQStmt, storeParamsStmt,
    forRange, forUp, Stmt.NoRand]

/-! ## 4. Verification of `coreLevelProc` -/

private lemma pow_lt_of_lt_clog {N p q : ℕ} (_hN : 2 ≤ N) (hq : q < Nat.clog N p) :
    N ^ q < p := by
  by_contra h
  have hle : p ≤ N ^ q := Nat.le_of_not_lt h
  have := Nat.clog_le_of_le_pow hle
  omega

private lemma coreLevelLoop_triple {w N p : ℕ} (pProg : Program) (mem₀ : ℕ → ℕ)
    (hN : 2 ≤ N) (_hp : 1 ≤ p) (hw : N * p + 16 < 2 ^ w) :
    Triple w pProg
      (fun st => st.regs 0 = N ∧ st.regs 1 = p ∧ st.regs 2 = 0 ∧ st.regs 3 = 1 ∧ st.mem = mem₀)
      (.loop (.bin .lt (.reg 3) (.reg 1))
        (.assign 3 (.bin .mul (.reg 3) (.reg 0)) ;;
         .assign 2 (.bin .add (.reg 2) (.const 1))))
      (normalPost fun st' =>
        st'.regs 2 = Nat.clog N p ∧ st'.regs 3 = N ^ Nat.clog N p ∧ st'.mem = mem₀)
      (fun _ => 25 * (Nat.clog N p + 1)) := by
  set Q := Nat.clog N p
  have hlt1 : 1 < 2 ^ w := by omega
  have hloop := Triple.loop_const_normal (w := w) (p := pProg)
    (e := .bin .lt (.reg 3) (.reg 1))
    (body := .assign 3 (.bin .mul (.reg 3) (.reg 0)) ;;
      .assign 2 (.bin .add (.reg 2) (.const 1)))
    (Inv := fun st => st.regs 0 = N ∧ st.regs 1 = p ∧ st.regs 2 ≤ Q ∧
      st.regs 3 = N ^ st.regs 2 ∧ st.mem = mem₀)
    (Q := fun st' => st'.regs 2 = Q ∧ st'.regs 3 = N ^ Q ∧ st'.mem = mem₀)
    (fun st => Q - st.regs 2)
    (fun st => if N ^ st.regs 2 < p then 1 else 0)
    10
    (fun st ⟨_, h1, _, h3, _⟩ => by
      by_cases hlt : N ^ st.regs 2 < p
      · simp [Expr.eval, BinOp.eval, h3, h1, hlt, hlt1]
      · simp [Expr.eval, BinOp.eval, h3, h1, hlt])
    (fun st ⟨_, _, hqle, h3, hmem⟩ hcond => by
      have hge : p ≤ N ^ st.regs 2 := by
        by_contra hlt
        have hlt' : N ^ st.regs 2 < p := Nat.lt_of_not_le hlt
        simp [hlt'] at hcond
      have hclog_le : Q ≤ st.regs 2 := Nat.clog_le_of_le_pow hge
      have hqeq : st.regs 2 = Q := by omega
      exact ⟨hqeq, by rw [hqeq] at h3; exact h3, hmem⟩)
    (fun st ⟨h0, h1, hqle, h3, hmem⟩ hcond => by
      have hpow_lt : N ^ st.regs 2 < p := by
        by_contra h
        simp [h] at hcond
      have hlt : st.regs 2 < Q := by
        by_contra hge
        have hqeq : st.regs 2 = Q := by omega
        have hpow_ge : p ≤ N ^ Q := Nat.le_pow_clog (by omega) p
        rw [hqeq] at hpow_lt
        omega
      have hmul_lt : N ^ st.regs 2 * N < 2 ^ w := by
        have : N ^ st.regs 2 * N ≤ p * N := Nat.mul_le_mul_right N (le_of_lt hpow_lt)
        rw [Nat.mul_comm p N] at this
        omega
      have hq_lt : st.regs 2 + 1 < 2 ^ w := by
        have hpow1 : st.regs 2 < N ^ st.regs 2 := Nat.lt_pow_self (by omega)
        have hp_le : p ≤ N * p := Nat.le_mul_of_pos_left p (by omega)
        omega
      intro s ω hs
      subst s
      set st1 : State := { st with regs := Function.update st.regs 3 (N ^ st.regs 2 * N) }
      set st2 : State := { st1 with regs := Function.update st1.regs 2 (st.regs 2 + 1) }
      have hs1 : Runs w pProg ω (.assign 3 (.bin .mul (.reg 3) (.reg 0))) st .normal st1 4 := by
        rw [runs_assign_iff]
        exact ⟨N ^ st.regs 2 * N, by simp [Expr.eval, BinOp.eval, h3, h0, hmul_lt],
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w pProg ω (.assign 2 (.bin .add (.reg 2) (.const 1))) st1 .normal st2 4 := by
        rw [runs_assign_iff]
        have h2' : st1.regs 2 = st.regs 2 := by simp [st1]
        exact ⟨st.regs 2 + 1, by simp [Expr.eval, BinOp.eval, h2', hq_lt, hlt1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, st2, 9, runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hs1, hs2, rfl⟩), ?_, Nat.le_succ 9⟩
      exact ⟨⟨by simp [st2, st1, h0], by simp [st2, st1, h1], by simp [st2]; omega,
        by simp [st2, st1, Nat.pow_succ], by simp [st2, st1, hmem]⟩, by simp [st2]; omega⟩)
  refine hloop.conseq
    (fun st ⟨h0, h1, h2, h3, hmem⟩ => ⟨h0, h1, by rw [h2]; exact Nat.zero_le Q, by simp [h2, h3], hmem⟩)
    (fun _ _ h => h)
    (fun st ⟨_, _, h2, _, _⟩ => by simp [Expr.size, h2]; omega)

/-- Specification of `coreLevelProc`: computes `Nat.clog N p` without modifying memory. -/
theorem coreLevelProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [coreLevelProc]) :
    MeetsContract w pProg b (coreLevelContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨N, p, rfl, hN, hpp, hw⟩
  have hlt1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [coreLevelProc]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le (coreLevelLoop_triple pProg mem hN hpp hw)
    ⟨by simp [startState], by simp [startState], by simp, by simp, rfl⟩ ?_
  intro st₁ ⟨h2, _, hmem⟩
  refine runs_ret_le (by eval_expr) ?_ ?_
  · simp only [coreLevelContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    exact ⟨trivial, hmem⟩
  · simp only [coreLevelContract, coreLevelProcCost, Expr.size, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    omega

/-! ## 5. Arithmetic Bounds and Staged Triples for `computeParamsProc` -/

lemma ceilDiv_le_self {a b : ℕ} (hb : 1 ≤ b) : ceilDiv a b ≤ a := by
  unfold ceilDiv
  have h1 : a + b ≤ (a + 1) * b := by nlinarith
  have hlt : a + b - 1 < (a + 1) * b := by omega
  have hdiv : (a + b - 1) / b < a + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt
  omega

lemma NOf_le_four_mul (M r : ℕ) (hr1 : 1 ≤ r) : NOf M r ≤ 4 * M + 4 := by
  unfold NOf
  have hell1 : 1 ≤ ell M := one_le_ell M
  have hdiv : ceilDiv (ell M) r ≤ ell M := ceilDiv_le_self hr1
  have hpow : 2 ^ max 2 (ceilDiv (ell M) r) ≤ 2 ^ max 2 (ell M) :=
    Nat.pow_le_pow_right (by decide) (max_le_max_left 2 hdiv)
  have h2ell : 2 ^ ell M ≤ 4 * M + 4 := by
    have hpred : 2 ^ (ell M - 1) < 2 * M + 2 :=
      pow_lt_of_lt_clog (by decide) (by omega : ell M - 1 < ell M)
    have heq : 2 ^ ell M = 2 * 2 ^ (ell M - 1) := by
      conv_lhs => rw [show ell M = (ell M - 1) + 1 by omega, Nat.pow_succ']
    omega
  rcases le_or_gt (ell M) 2 with hle2 | hgt2
  · rw [max_eq_left hle2] at hpow
    have : 2 ^ 2 = 4 := by decide
    omega
  · rw [max_eq_right (by omega : 2 ≤ ell M)] at hpow
    omega

lemma param_le_QOut (cfg : ParamConfig) (M : ℕ) {r : ℕ} (hr1 : 1 ≤ r) :
    1 ≤ FParam cfg M ∧
    FParam cfg M ≤ PParam cfg M r ∧
    PParam cfg M r ≤ Lambda cfg M r ∧
    ROut cfg M ≤ Lambda cfg M r ∧
    dOut cfg M + 1 ≤ ROut cfg M ∧
    bOut cfg M ≤ dOut cfg M ∧
    RCore M ≤ FParam cfg M ∧
    dCore M + 1 ≤ RCore M ∧
    tParam M ≤ dCore M ∧
    LParam M ≤ tParam M ∧
    Lambda cfg M r ≤ DOut cfg M r ∧
    DOut cfg M r ≤ QOut cfg M r ∧
    49 * LParam M + 1 ≤ QOut cfg M r := by
  have hL : 4 ≤ LParam M := four_le_LParam M
  have ht : 4096 ≤ tParam M := by unfold tParam; omega
  have hLt : LParam M ≤ tParam M := by unfold tParam; omega
  have hdC : tParam M ≤ dCore M := by unfold dCore deltaParam; nlinarith
  have hRC : dCore M + 1 ≤ RCore M := by
    unfold RCore deltaParam
    have h1 : 1 ≤ 1600 * tParam M * LParam M := by nlinarith
    calc dCore M + 1 = (dCore M + 1) * 1 := (mul_one _).symm
      _ ≤ (dCore M + 1) * (1600 * tParam M * LParam M) := Nat.mul_le_mul_left _ h1
      _ = 1600 * tParam M * (dCore M + 1) * LParam M := by ring
  have hF : RCore M ≤ FParam cfg M := by
    unfold FParam deltaParam
    have ha0 := cfg.ha₀
    have h1 : 1 ≤ 1920 * cfg.a₀ * (tParam M) ^ 2 := by nlinarith
    calc RCore M = 1 * RCore M := (one_mul _).symm
      _ ≤ (1920 * cfg.a₀ * (tParam M) ^ 2) * RCore M := Nat.mul_le_mul_right _ h1
  have hF1 : 1 ≤ FParam cfg M := by omega
  have hFP : FParam cfg M ≤ PParam cfg M r := by
    unfold PParam; simpa [pow_one] using Nat.pow_le_pow_right hF1 hr1
  have hb1 : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have hdO : bOut cfg M ≤ dOut cfg M := by unfold dOut; nlinarith
  have hRO : dOut cfg M + 1 ≤ ROut cfg M := by
    unfold ROut
    have h1 : 1 ≤ 160 * bOut cfg M * LParam M := by nlinarith
    calc dOut cfg M + 1 = (dOut cfg M + 1) * 1 := (mul_one _).symm
      _ ≤ (dOut cfg M + 1) * (160 * bOut cfg M * LParam M) := Nat.mul_le_mul_left _ h1
      _ = 160 * bOut cfg M * (dOut cfg M + 1) * LParam M := by ring
  have hP1 : 1 ≤ PParam cfg M r := le_trans hF1 hFP
  have hRO1 : 1 ≤ ROut cfg M := by omega
  have hPLam : PParam cfg M r ≤ Lambda cfg M r := by
    unfold Lambda
    have h1 : 1 ≤ 2 * tParam M * ROut cfg M * (tParam M + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) hRO1) (by omega)
    calc PParam cfg M r = PParam cfg M r * 1 := (mul_one _).symm
      _ ≤ PParam cfg M r * (2 * tParam M * ROut cfg M * (tParam M + 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1) := by ring
  have hROLam : ROut cfg M ≤ Lambda cfg M r := by
    unfold Lambda
    have h1 : 1 ≤ 2 * PParam cfg M r * tParam M * (tParam M + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    calc ROut cfg M = ROut cfg M * 1 := (mul_one _).symm
      _ ≤ ROut cfg M * (2 * PParam cfg M r * tParam M * (tParam M + 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1) := by ring
  have hLamD : Lambda cfg M r ≤ DOut cfg M r := by
    unfold DOut
    have hA := cfg.A_pos
    have h1 : 1 ≤ 16 * cfg.A * tParam M * bOut cfg M :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb1
    calc Lambda cfg M r = Lambda cfg M r * 1 := (mul_one _).symm
      _ ≤ Lambda cfg M r * (16 * cfg.A * tParam M * bOut cfg M) := Nat.mul_le_mul_left _ h1
      _ = 16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M := by ring
  have hDQ : DOut cfg M r ≤ QOut cfg M r := by unfold QOut; omega
  have h49 : 49 * LParam M + 1 ≤ QOut cfg M r := by
    have : tParam M ≤ QOut cfg M r := by omega
    unfold tParam at this; omega
  exact ⟨hF1, hFP, hPLam, hROLam, hRO, hdO, hF, hRC, hdC, hLt, hLamD, hDQ, h49⟩

lemma pow2_loop_triple {w expN : ℕ} (pProg : Program)
    (P : State → Prop) (rKeep : ℕ → Prop)
    (h8 : ∀ st, P st → st.regs 8 = expN)
    (h9 : ∀ st, P st → st.regs 9 = 1)
    (hkeep : ∀ r, rKeep r → r ≠ 9 ∧ r ≠ 10)
    (hw : 2 ^ expN + 16 < 2 ^ w) :
    Triple w pProg P
      (forRange 10 (.const 0) (.reg 8) (.assign 9 (.bin .mul (.const 2) (.reg 9))))
      (normalPost fun st' =>
        st'.regs 9 = 2 ^ expN ∧
        ∃ st₀, P st₀ ∧ st'.mem = st₀.mem ∧ (∀ r, rKeep r → st'.regs r = st₀.regs r))
      (fun _ => 20 * (expN + 1)) := by
  have h2pow_pos : 1 ≤ 2 ^ expN := Nat.two_pow_pos expN
  have hlt1 : 1 < 2 ^ w := by omega
  have hlt2 : 2 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := pProg) (r := 10) (lo := .const 0) (hi := .reg 8)
    (body := .assign 9 (.bin .mul (.const 2) (.reg 9)))
    (P := P)
    (Inv := fun i st => st.regs 8 = expN ∧ st.regs 9 = 2 ^ i ∧ st.regs 10 = i ∧
      ∃ st₀, P st₀ ∧ st.mem = st₀.mem ∧ ∀ r, rKeep r → st.regs r = st₀.regs r)
    5 0 expN (Nat.zero_le expN) hlt1
    (fun _ => by
      have : expN < 2 ^ expN := Nat.lt_pow_self one_lt_two
      omega)
    (fun st hP => by
      refine ⟨by eval_expr, ?_, ?_, ?_, st, hP, rfl, fun r hr => ?_⟩
      · simp [h8 st hP]
      · simp [h9 st hP]
      · simp
      · have hne := (hkeep r hr).2; simp [hne])
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => by have hr8 : st.regs 8 = expN := hi.1; eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨hr8, hr9, hr10, st₀, hP₀, hmem, hkr⟩
      have hpow_lt : 2 * 2 ^ i < 2 ^ w := by
        have h1 : 2 ^ (i + 1) ≤ 2 ^ expN := Nat.pow_le_pow_right (by decide) hilt
        rw [Nat.pow_succ'] at h1; omega
      set st' : State := { st with regs := Function.update st.regs 9 (2 * 2 ^ i) }
      refine ⟨.normal, st', 4, ?_, ?_, Nat.le_succ 4⟩
      · rw [runs_assign_iff]
        exact ⟨2 * 2 ^ i, by simp [Expr.eval, BinOp.eval, hr9, hpow_lt, hlt2],
          rfl, rfl, by simp [Expr.size]⟩
      · refine ⟨⟨by simp [st', hr8], by simp [st', Nat.pow_succ'], by simp [st'],
          st₀, hP₀, hmem, fun r hr => ?_⟩, by simp [st', hr10]⟩
        rcases hkeep r hr with ⟨hne1, hne2⟩
        simp [st', Function.update_of_ne hne2, Function.update_of_ne hne1, hkr r hr])
  refine hloop.conseq (fun _ h => h)
    (fun o st' h => by cases o with | returned _ => exact False.elim h | normal => exact ⟨h.2.1, h.2.2.2⟩)
    (fun _ _ => by simp [Expr.size]; omega)

lemma powF_loop_triple {w r F : ℕ} (pProg : Program)
    (P : State → Prop) (rKeep : ℕ → Prop)
    (h2 : ∀ st, P st → st.regs 2 = r)
    (h14 : ∀ st, P st → st.regs 14 = F)
    (h15 : ∀ st, P st → st.regs 15 = 1)
    (hkeep : ∀ j, rKeep j → j ≠ 15 ∧ j ≠ 10)
    (hF1 : 1 ≤ F) (hw : F ^ r + 16 < 2 ^ w) (hrw : r + 1 < 2 ^ w) :
    Triple w pProg P
      (forRange 10 (.const 0) (.reg 2) (.assign 15 (.bin .mul (.reg 15) (.reg 14))))
      (normalPost fun st' =>
        st'.regs 15 = F ^ r ∧
        ∃ st₀, P st₀ ∧ st'.mem = st₀.mem ∧ (∀ j, rKeep j → st'.regs j = st₀.regs j))
      (fun _ => 20 * (r + 1)) := by
  have hlt1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := pProg) (r := 10) (lo := .const 0) (hi := .reg 2)
    (body := .assign 15 (.bin .mul (.reg 15) (.reg 14)))
    (P := P)
    (Inv := fun i st => st.regs 2 = r ∧ st.regs 14 = F ∧ st.regs 15 = F ^ i ∧ st.regs 10 = i ∧
      ∃ st₀, P st₀ ∧ st.mem = st₀.mem ∧ ∀ j, rKeep j → st.regs j = st₀.regs j)
    5 0 r (Nat.zero_le r) hlt1
    (fun _ => by omega)
    (fun st hP => by
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, st, hP, rfl, fun j hj => ?_⟩
      · simp [h2 st hP]
      · simp [h14 st hP]
      · simp [h15 st hP]
      · simp
      · have hne := (hkeep j hj).2; simp [hne])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have hr2 : st.regs 2 = r := hi.1; eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨hr2, hr14, hr15, hr10, st₀, hP₀, hmem, hkr⟩
      have hpow_lt : F ^ i * F < 2 ^ w := by
        have h1 : F ^ (i + 1) ≤ F ^ r := Nat.pow_le_pow_right hF1 hilt
        rw [Nat.pow_succ] at h1; omega
      set st' : State := { st with regs := Function.update st.regs 15 (F ^ i * F) }
      refine ⟨.normal, st', 4, ?_, ?_, Nat.le_succ 4⟩
      · rw [runs_assign_iff]
        exact ⟨F ^ i * F, by simp [Expr.eval, BinOp.eval, hr15, hr14, hpow_lt],
          rfl, rfl, by simp [Expr.size]⟩
      · refine ⟨⟨by simp [st', hr2], by simp [st', hr14], by simp [st', Nat.pow_succ],
          by simp [st'], st₀, hP₀, hmem, fun j hj => ?_⟩, by simp [st', hr10]⟩
        rcases hkeep j hj with ⟨hne1, hne2⟩
        simp [st', Function.update_of_ne hne2, Function.update_of_ne hne1, hkr j hj])
  refine hloop.conseq (fun _ h => h)
    (fun o st' h => by cases o with | returned _ => exact False.elim h | normal => exact ⟨h.2.2.1, h.2.2.2.2⟩)
    (fun _ _ => by simp [Expr.size]; omega)

lemma ell_loop_triple {w n M r pAddr : ℕ} (pProg : Program) (mem₀ : ℕ → ℕ)
    (hw : 4 * M + 16 < 2 ^ w) :
    Triple w pProg
      (fun st => st.regs 0 = n ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = pAddr ∧
        st.regs 4 = 2 * M + 2 ∧ st.regs 5 = 0 ∧ st.regs 6 = 1 ∧ st.mem = mem₀)
      (.loop (.bin .lt (.reg 6) (.reg 4))
        (.assign 6 (.bin .mul (.const 2) (.reg 6)) ;;
         .assign 5 (.bin .add (.reg 5) (.const 1))))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 1 = M ∧ st'.regs 2 = r ∧ st'.regs 3 = pAddr ∧
        st'.regs 5 = ell M ∧ st'.mem = mem₀)
      (fun _ => 25 * (ell M + 1)) := by
  set E := ell M
  have hlt1 : 1 < 2 ^ w := by omega
  have hlt2 : 2 < 2 ^ w := by omega
  have hloop := Triple.loop_const_normal (w := w) (p := pProg)
    (e := .bin .lt (.reg 6) (.reg 4))
    (body := .assign 6 (.bin .mul (.const 2) (.reg 6)) ;;
      .assign 5 (.bin .add (.reg 5) (.const 1)))
    (Inv := fun st => st.regs 0 = n ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = pAddr ∧
      st.regs 4 = 2 * M + 2 ∧ st.regs 5 ≤ E ∧ st.regs 6 = 2 ^ st.regs 5 ∧ st.mem = mem₀)
    (Q := fun st' => st'.regs 0 = n ∧ st'.regs 1 = M ∧ st'.regs 2 = r ∧ st'.regs 3 = pAddr ∧
      st'.regs 5 = E ∧ st'.mem = mem₀)
    (fun st => E - st.regs 5)
    (fun st => if 2 ^ st.regs 5 < 2 * M + 2 then 1 else 0)
    10
    (fun st ⟨_, _, _, _, h4, _, h6, _⟩ => by
      by_cases hlt : 2 ^ st.regs 5 < 2 * M + 2
      · simp [Expr.eval, BinOp.eval, h6, h4, hlt, hlt1]
      · simp [Expr.eval, BinOp.eval, h6, h4, hlt])
    (fun st ⟨h0, h1, h2, h3, _, h5le, _, hmem⟩ hcond => by
      have hge : 2 * M + 2 ≤ 2 ^ st.regs 5 := by
        by_contra hlt
        have hlt' : 2 ^ st.regs 5 < 2 * M + 2 := Nat.lt_of_not_le hlt
        simp [hlt'] at hcond
      have hclog_le : E ≤ st.regs 5 := Nat.clog_le_of_le_pow hge
      exact ⟨h0, h1, h2, h3, by omega, hmem⟩)
    (fun st ⟨h0, h1, h2, h3, h4, h5le, h6, hmem⟩ hcond => by
      have hpow_lt : 2 ^ st.regs 5 < 2 * M + 2 := by
        by_contra h; simp [h] at hcond
      have hlt : st.regs 5 < E := by
        by_contra hge
        have h5eq : st.regs 5 = E := by omega
        have hpow_ge : 2 * M + 2 ≤ 2 ^ E := Nat.le_pow_clog (by decide) (2 * M + 2)
        rw [h5eq] at hpow_lt; omega
      have hmul_lt : 2 * 2 ^ st.regs 5 < 2 ^ w := by omega
      have h5_lt : st.regs 5 + 1 < 2 ^ w := by
        have : st.regs 5 < 2 ^ st.regs 5 := Nat.lt_pow_self one_lt_two; omega
      intro s ω hs; subst s
      set st1 : State := { st with regs := Function.update st.regs 6 (2 * 2 ^ st.regs 5) }
      set st2 : State := { st1 with regs := Function.update st1.regs 5 (st.regs 5 + 1) }
      have hs1 : Runs w pProg ω (.assign 6 (.bin .mul (.const 2) (.reg 6))) st .normal st1 4 := by
        rw [runs_assign_iff]
        exact ⟨2 * 2 ^ st.regs 5, by simp [Expr.eval, BinOp.eval, h6, hlt2, hmul_lt],
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w pProg ω (.assign 5 (.bin .add (.reg 5) (.const 1))) st1 .normal st2 4 := by
        rw [runs_assign_iff]
        have h5' : st1.regs 5 = st.regs 5 := by simp [st1]
        exact ⟨st.regs 5 + 1, by simp [Expr.eval, BinOp.eval, h5', h5_lt, hlt1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, st2, 9, runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hs1, hs2, rfl⟩), ?_, Nat.le_succ 9⟩
      exact ⟨⟨by simp [st2, st1, h0], by simp [st2, st1, h1], by simp [st2, st1, h2],
        by simp [st2, st1, h3], by simp [st2, st1, h4], by simp [st2]; omega,
        by simp [st2, st1, Nat.pow_succ'], by simp [st2, st1, hmem]⟩, by simp [st2]; omega⟩)
  refine hloop.conseq
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, hmem⟩ =>
      ⟨h0, h1, h2, h3, h4, by rw [h5]; exact Nat.zero_le E, by simp [h5, h6], hmem⟩)
    (fun _ _ h => h)
    (fun st ⟨_, _, _, _, _, h5, _, _⟩ => by simp [Expr.size, h5]; omega)

lemma computeCoreF_triple {w M : ℕ} (cfg : ParamConfig) (pProg : Program) (st₀ : State)
    (h7 : st₀.regs 7 = LParam M)
    (hFw : FParam cfg M + 16 < 2 ^ w) (ha0w : 1920 * cfg.a₀ + 16 < 2 ^ w) :
    Triple w pProg
      (fun st => st = st₀)
      (computeCoreFStmt cfg)
      (normalPost fun st' =>
        st'.regs 11 = tParam M ∧ st'.regs 14 = FParam cfg M ∧ st'.regs 15 = 1 ∧
        st'.mem = st₀.mem ∧ ∀ j, j ≤ 9 → st'.regs j = st₀.regs j)
      (fun _ => 80) := by
  have hL : 4 ≤ LParam M := four_le_LParam M
  have ht : 4096 ≤ tParam M := by unfold tParam; omega
  have hLt : LParam M ≤ tParam M := by unfold tParam; omega
  have hdC : tParam M ≤ dCore M := by unfold dCore deltaParam; nlinarith
  have hRC : dCore M + 1 ≤ RCore M := by
    unfold RCore deltaParam
    have h1 : 1 ≤ 1600 * tParam M * LParam M := by nlinarith
    calc dCore M + 1 = (dCore M + 1) * 1 := (mul_one _).symm
      _ ≤ (dCore M + 1) * (1600 * tParam M * LParam M) := Nat.mul_le_mul_left _ h1
      _ = 1600 * tParam M * (dCore M + 1) * LParam M := by ring
  have hF : RCore M ≤ FParam cfg M := by
    unfold FParam deltaParam
    have ha0 := cfg.ha₀
    have h1 : 1 ≤ 1920 * cfg.a₀ * (tParam M) ^ 2 := by nlinarith
    calc RCore M = 1 * RCore M := (one_mul _).symm
      _ ≤ (1920 * cfg.a₀ * (tParam M) ^ 2) * RCore M := Nat.mul_le_mul_right _ h1
  have h3200t : 3200 * tParam M ≤ dCore M := by
    unfold dCore deltaParam
    calc 3200 * tParam M = 3200 * tParam M * 1 := (mul_one _).symm
      _ ≤ 3200 * tParam M * LParam M := Nat.mul_le_mul_left _ (by omega)
  have h1600t : 1600 * tParam M ≤ RCore M := by
    unfold RCore deltaParam
    have h1 : 1 ≤ (dCore M + 1) * LParam M := by nlinarith
    calc 1600 * tParam M = 1600 * tParam M * 1 := (mul_one _).symm
      _ ≤ 1600 * tParam M * ((dCore M + 1) * LParam M) := Nat.mul_le_mul_left _ h1
      _ = 1600 * tParam M * (dCore M + 1) * LParam M := by ring
  have h1600td : 1600 * tParam M * (dCore M + 1) ≤ RCore M := by
    unfold RCore deltaParam
    calc 1600 * tParam M * (dCore M + 1) = (1600 * tParam M * (dCore M + 1)) * 1 := (mul_one _).symm
      _ ≤ (1600 * tParam M * (dCore M + 1)) * LParam M := Nat.mul_le_mul_left _ (by omega)
  have h1920t : 1920 * cfg.a₀ * tParam M ≤ FParam cfg M := by
    unfold FParam deltaParam
    have h1 : 1 ≤ tParam M * RCore M := Nat.mul_pos (by omega) (by omega)
    calc 1920 * cfg.a₀ * tParam M = (1920 * cfg.a₀ * tParam M) * 1 := (mul_one _).symm
      _ ≤ (1920 * cfg.a₀ * tParam M) * (tParam M * RCore M) := Nat.mul_le_mul_left _ h1
      _ = 1920 * cfg.a₀ * (tParam M) ^ 2 * RCore M := by ring
  have h1920tt : 1920 * cfg.a₀ * tParam M * tParam M ≤ FParam cfg M := by
    unfold FParam deltaParam
    calc 1920 * cfg.a₀ * tParam M * tParam M = (1920 * cfg.a₀ * (tParam M) ^ 2) * 1 := by ring
      _ ≤ (1920 * cfg.a₀ * (tParam M) ^ 2) * RCore M := Nat.mul_le_mul_left _ (by omega)
  have h1w : 1 < 2 ^ w := by omega
  have h1024w : 1024 < 2 ^ w := by omega
  have h3200w : 3200 < 2 ^ w := by omega
  have h1600w : 1600 < 2 ^ w := by omega
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [computeCoreFStmt]
  have hp1 : Triple w pProg (fun s => s = st)
      (.assign 11 (.bin .mul (.const 1024) (.reg 7)) ;;
       .assign 12 (.bin .mul (.const 3200) (.reg 11)) ;;
       .assign 12 (.bin .mul (.reg 12) (.reg 7)))
      (normalPost fun s' => s'.regs 7 = LParam M ∧ s'.regs 11 = tParam M ∧ s'.regs 12 = dCore M ∧
        s'.mem = st.mem ∧ ∀ j, j ≤ 9 → s'.regs j = st.regs j)
      (fun _ => 25) := by
    intro s _ hs; subst hs
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := tParam M)
      (by simp [Expr.eval, BinOp.eval, h7, h1024w,
            (by change tParam M < 2 ^ w; omega : 1024 * LParam M < 2 ^ w), tParam]) ?_
    refine runs_seq_assign_le (v := 3200 * tParam M)
      (by simp [Expr.eval, BinOp.eval, h3200w, (by omega : 3200 * tParam M < 2 ^ w)]) ?_
    refine runs_assign_le (v := dCore M)
      (by simp [Expr.eval, BinOp.eval, h7,
            (by change dCore M < 2 ^ w; omega : 3200 * tParam M * LParam M < 2 ^ w),
            dCore, deltaParam])
      ⟨by simp [h7], by simp, by simp, rfl, fun j hj => by
        simp (disch := omega) only [Function.update_of_ne]⟩
      (by simp [Expr.size])
  refine runs_seq_triple_le hp1 rfl ?_
  intro st1 ⟨h1_7, h1_11, h1_12, h1_mem, h1_keep⟩
  have hp2 : Triple w pProg (fun s => s = st1)
      (.assign 13 (.bin .mul (.const 1600) (.reg 11)) ;;
       .assign 13 (.bin .mul (.reg 13) (.bin .add (.reg 12) (.const 1))) ;;
       .assign 13 (.bin .mul (.reg 13) (.reg 7)))
      (normalPost fun s' => s'.regs 11 = tParam M ∧ s'.regs 13 = RCore M ∧
        s'.mem = st1.mem ∧ ∀ j, j ≤ 9 → s'.regs j = st1.regs j)
      (fun _ => 25) := by
    intro s _ hs; subst hs
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := 1600 * tParam M)
      (by simp [Expr.eval, BinOp.eval, h1_11, h1600w, (by omega : 1600 * tParam M < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := 1600 * tParam M * (dCore M + 1))
      (by simp [Expr.eval, BinOp.eval, h1_12, h1w, (by omega : dCore M + 1 < 2 ^ w),
        (by omega : 1600 * tParam M * (dCore M + 1) < 2 ^ w)]) ?_
    refine runs_assign_le (v := RCore M)
      (by simp [Expr.eval, BinOp.eval, h1_7,
            (by change RCore M < 2 ^ w; omega : 1600 * tParam M * (dCore M + 1) * LParam M < 2 ^ w),
            RCore, deltaParam])
      ⟨by simp [h1_11], by simp, rfl, fun j hj => by
        simp (disch := omega) only [Function.update_of_ne]⟩
      (by simp [Expr.size])
  refine runs_seq_triple_le hp2 rfl ?_
  intro st2 ⟨h2_11, h2_13, h2_mem, h2_keep⟩
  refine runs_seq_assign_le (v := 1920 * cfg.a₀ * tParam M)
    (by simp [Expr.eval, BinOp.eval, h2_11, (by omega : 1920 * cfg.a₀ < 2 ^ w),
      (by omega : 1920 * cfg.a₀ * tParam M < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 1920 * cfg.a₀ * tParam M * tParam M)
    (by simp [Expr.eval, BinOp.eval, h2_11, (by omega : 1920 * cfg.a₀ * tParam M * tParam M < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := FParam cfg M)
    (by simp only [Expr.eval, BinOp.eval, Function.update_self,
          Function.update_of_ne (by decide : (13 : ℕ) ≠ 14), h2_13,
          show 1920 * cfg.a₀ * tParam M * tParam M * RCore M = FParam cfg M by
            unfold FParam deltaParam; ring,
          (by omega : FParam cfg M < 2 ^ w), ↓reduceIte]) ?_
  refine runs_assign_le (v := 1) (by simp [Expr.eval, h1w]) ?_ (by simp [Expr.size])
  exact ⟨by simp [h2_11], by simp, by simp, by rw [h2_mem, h1_mem], fun j hj => by
    simp (disch := omega) only [Function.update_of_ne]
    rw [h2_keep j hj, h1_keep j hj]⟩


end MinCostFlow.ExpanderDecomp
