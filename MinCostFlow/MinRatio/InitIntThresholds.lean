module

public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.MinRatio.InitConcretePostTail
public import MinCostFlow.Scaling.ClogTwoProgram
import WordRAM.Tactic

/-!
# Exact integer rebuild threshold table writer for Algorithm 1

Computes `intRebuildThreshold P (4 * M₀) j = M₀ / (k^(j + 1) * Nat.clog 2 (4 * M₀ + 2)^2)`
for all `0 ≤ j ≤ d` in `O(log M₀ + d)` deterministic Word-RAM steps with zero heap allocation,
using the exact iterative division recurrences `intRebuildThreshold_zero_eq` and
`intRebuildThreshold_succ_eq`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- Deterministic inline statement computing `intRebuildThreshold P (4 * M₀) j` for `0 ≤ j ≤ d`
into `mem[tableDst + j]`.
Expects `reg 0 = M₀`, `reg 1 = k`, `reg 2 = d`, `reg 3 = tableDst`.
Uses `clog` (`Scaling.Machine.clogTwoContract w`) and writes only registers `4..8` and memory
`[tableDst, tableDst + d]`. -/
@[expose] def fillIntRebuildThresholdsStmt (clog : ℕ) : Stmt :=
  .assign 4 (.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 2)) ;;
  .call 5 clog [.reg 4] ;;
  .assign 6 (.bin .div (.bin .div (.reg 0) (.bin .mul (.reg 5) (.reg 5))) (.reg 1)) ;;
  .assign 7 (.const 0) ;;
  .assign 8 (.bin .add (.reg 2) (.const 1)) ;;
  .loop (.bin .lt (.reg 7) (.reg 8))
    (.store (.bin .add (.reg 3) (.reg 7)) (.reg 6) ;;
     .assign 6 (.bin .div (.reg 6) (.reg 1)) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1)))

theorem fillIntRebuildThresholdsStmt_noRand (clog : ℕ) :
    (fillIntRebuildThresholdsStmt clog).NoRand := by
  simp [fillIntRebuildThresholdsStmt, Stmt.NoRand]

/-- Deterministic procedure taking `[root]` that overwrites the solver's rebuild-threshold table
`table[0..d]` in-place with the exact integer thresholds `intRebuildThreshold P (4 * max m threshold) j`
while preserving all other memory cells, and returns the final internal-table capacity
`max m threshold + intRebuildThreshold P (4 * max m threshold) 0 + 2 * m`. -/
@[expose] def initOverwriteIntThresholdsBody (clog threshold : ℕ) : Stmt :=
  .assign 10 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.const 9))) ;;
  .assign 2 (.load (.bin .add (.reg 10) (.const 11))) ;;
  .assign 1 (.load (.bin .add (.reg 10) (.const 12))) ;;
  .cond (.bin .lt (.reg 11) (.const threshold))
    (.assign 0 (.const threshold))
    (.assign 0 (.reg 11)) ;;
  fillIntRebuildThresholdsStmt clog ;;
  .assign 4 (.load (.reg 3)) ;;
  .ret (.bin .add (.bin .add (.reg 0) (.reg 4)) (.bin .mul (.const 2) (.reg 11)))

theorem initOverwriteIntThresholdsBody_noRand (clog threshold : ℕ) :
    (initOverwriteIntThresholdsBody clog threshold).NoRand := by
  simp [initOverwriteIntThresholdsBody, fillIntRebuildThresholdsStmt_noRand, Stmt.NoRand]

/-- Helper: `w * w < 2 ^ w` for every `w ≥ 5`. -/
private theorem sq_lt_two_pow {w : ℕ} (hw : 5 ≤ w) : w * w < 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    have hlin : 2 * n + 1 ≤ n * n := by nlinarith
    rw [hpow]
    nlinarith

/-- Helper: for `5 ≤ w` and `n ≤ 2 ^ w`, `(Nat.clog 2 n) * (Nat.clog 2 n) < 2 ^ w`. -/
private theorem clog_sq_lt_two_pow {w n : ℕ} (hw : 5 ≤ w) (hn : n ≤ 2 ^ w) :
    Nat.clog 2 n * Nat.clog 2 n < 2 ^ w := by
  have hcl : Nat.clog 2 n ≤ w := (Nat.clog_le_iff_le_pow (by decide)).mpr hn
  exact lt_of_le_of_lt (Nat.mul_le_mul hcl hcl) (sq_lt_two_pow hw)

/-- Helper: inductive execution of the table-filling loop inside `fillIntRebuildThresholdsStmt`. -/
private theorem fillIntRebuildThresholdsLoop_runs
    {w tableDst : ℕ} {P : ChainParams} {p : Program} {ω : ℕ → Bool}
    (hM₀W : P.M₀ < 2 ^ w)
    (hd1W : P.d + 1 < 2 ^ w) (htabW : tableDst + P.d < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∀ (rem : ℕ) (st : State),
      let j := P.d + 1 - rem
      rem ≤ P.d + 1 →
      st.regs 1 = P.k → st.regs 3 = tableDst →
      st.regs 6 = intRebuildThreshold P (4 * P.M₀) j →
      st.regs 7 = j → st.regs 8 = P.d + 1 →
      (∀ t < j, st.mem (tableDst + t) = intRebuildThreshold P (4 * P.M₀) t) →
      ∃ out cost,
        Runs w p ω
          (.loop (.bin .lt (.reg 7) (.reg 8))
            (.store (.bin .add (.reg 3) (.reg 7)) (.reg 6) ;;
             .assign 6 (.bin .div (.reg 6) (.reg 1)) ;;
             .assign 7 (.bin .add (.reg 7) (.const 1))))
          st .normal out cost ∧
        cost ≤ 22 * rem + 4 ∧
        (∀ t ≤ P.d, out.mem (tableDst + t) = intRebuildThreshold P (4 * P.M₀) t) ∧
        (∀ a, a < tableDst ∨ tableDst + P.d < a → out.mem a = st.mem a) ∧
        (∀ r, r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) := by
  intro rem
  induction rem with
  | zero =>
    intro st j hrem hr1 hr3 hr6 hr7 hr8 hprev
    have hjEq : j = P.d + 1 := by dsimp only [j]; omega
    have hcond0 : (Expr.bin .lt (.reg 7) (.reg 8)).eval w st = some 0 := by
      simp [Expr.eval, BinOp.eval, hr7, hr8, hjEq, show 0 < 2 ^ w by omega]
    refine ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
      by omega, fun t ht => hprev t (by omega), fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    intro st j hrem hr1 hr3 hr6 hr7 hr8 hprev
    have hjLt : j < P.d + 1 := by dsimp only [j]; omega
    have hjNext : P.d + 1 - rem = j + 1 := by dsimp only [j]; omega
    have hcurW : intRebuildThreshold P (4 * P.M₀) j < 2 ^ w :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hM₀W
    have hnextW : intRebuildThreshold P (4 * P.M₀) (j + 1) < 2 ^ w :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hM₀W
    have hcond1 : (Expr.bin .lt (.reg 7) (.reg 8)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hr7, hr8, hjLt, hw1]
    let s1 : State := { st with mem := Function.update st.mem (tableDst + j) (intRebuildThreshold P (4 * P.M₀) j) }
    let s2 : State := { s1 with regs := Function.update s1.regs 6 (intRebuildThreshold P (4 * P.M₀) (j + 1)) }
    let s3 : State := { s2 with regs := Function.update s2.regs 7 (j + 1) }
    have r1 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 7)) (.reg 6)) st .normal s1 5 :=
      runs_store_iff.mpr ⟨tableDst + j, intRebuildThreshold P (4 * P.M₀) j,
        by simp [Expr.eval, BinOp.eval, hr3, hr7, show tableDst + j < 2 ^ w by omega],
        by simp [Expr.eval, hr6], rfl, rfl, rfl⟩
    have hdivEq : intRebuildThreshold P (4 * P.M₀) j / P.k = intRebuildThreshold P (4 * P.M₀) (j + 1) :=
      (intRebuildThreshold_succ_eq P (4 * P.M₀) j).symm
    have r2 : Runs w p ω (.assign 6 (.bin .div (.reg 6) (.reg 1))) s1 .normal s2 4 :=
      runs_assign_iff.mpr ⟨intRebuildThreshold P (4 * P.M₀) (j + 1), by
        simp [Expr.eval, BinOp.eval, s1, hr6, hr1, hdivEq, hnextW],
        rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) s2 .normal s3 4 :=
      runs_assign_iff.mpr ⟨j + 1, by
        simp [Expr.eval, BinOp.eval, s2, s1, hr7, hw1, show j + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have hbody : Runs w p ω
        (.store (.bin .add (.reg 3) (.reg 7)) (.reg 6) ;;
         .assign 6 (.bin .div (.reg 6) (.reg 1)) ;;
         .assign 7 (.bin .add (.reg 7) (.const 1))) st .normal s3 15 :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, 9, r1, runs_seq_iff.mpr (Or.inr ⟨s2, 4, 4, r2, r3, rfl⟩), rfl⟩)
    obtain ⟨out, cRest, hrest, hcRest, htabOut, hfrOut, hregOut⟩ :=
      ih s3 (by omega)
        (by simp [s3, s2, s1, hr1]) (by simp [s3, s2, s1, hr3])
        (by simp [s3, s2, hjNext]) (by simp [s3, hjNext]) (by simp [s3, s2, s1, hr8])
        (fun t ht => by
          rw [hjNext] at ht
          by_cases htj : t = j
          · subst htj; simp [s3, s2, s1]
          · simp only [s3, s2, s1, Function.update_of_ne (show tableDst + t ≠ tableDst + j by omega)]
            exact hprev t (by omega))
    refine ⟨out, 3 + 15 + cRest + 1,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, 15, cRest, hcond1, by decide, hbody, hrest, by simp [Expr.size]⟩)),
      by omega, htabOut, ?_, ?_⟩
    · intro a ha
      rw [hfrOut a ha]
      simp only [s3, s2, s1]
      rw [Function.update_of_ne (by omega)]
    · intro r hr6' hr7'
      rw [hregOut r hr6' hr7']
      simp [s3, s2, s1, Function.update_of_ne hr7', Function.update_of_ne hr6']

/-- Execution of `fillIntRebuildThresholdsStmt clog`: writes `intRebuildThreshold P (4 * P.M₀) j`
at `tableDst + j` for every `j ≤ P.d`, leaving all memory outside `[tableDst, tableDst + P.d]`
unchanged and using `O(log M₀ + d)` steps. -/
theorem fillIntRebuildThresholdsStmt_runs
    {w clog tableDst : ℕ} {P : ChainParams} {p : Program} {ω : ℕ → Bool} {st : State}
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hw5 : 5 ≤ w)
    (hr0 : st.regs 0 = P.M₀) (hr1 : st.regs 1 = P.k)
    (hr2 : st.regs 2 = P.d) (hr3 : st.regs 3 = tableDst)
    (h4M3W : 4 * P.M₀ + 3 < 2 ^ w)
    (hd1W : P.d + 1 < 2 ^ w) (htabW : tableDst + P.d < 2 ^ w) :
    ∃ out cost,
      Runs w p ω (fillIntRebuildThresholdsStmt clog) st .normal out cost ∧
      cost ≤ 40 * Nat.clog 2 (4 * P.M₀ + 2) + 22 * (P.d + 1) + 70 ∧
      (∀ t ≤ P.d, out.mem (tableDst + t) = intRebuildThreshold P (4 * P.M₀) t) ∧
      (∀ a, a < tableDst ∨ tableDst + P.d < a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → out.regs r = st.regs r) := by
  have hw4 : 4 < 2 ^ w := lt_of_lt_of_le (by decide : 4 < 2 ^ 5) (Nat.pow_le_pow_right (by decide) hw5)
  have hw2 : 2 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hM₀W : P.M₀ < 2 ^ w := by omega
  let b := Nat.clog 2 (4 * P.M₀ + 2)
  have hb2W : b * b < 2 ^ w := clog_sq_lt_two_pow hw5 (by omega)
  have hdiv1W : P.M₀ / (b * b) < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hM₀W
  have ht0Eq : (P.M₀ / (b * b)) / P.k = intRebuildThreshold P (4 * P.M₀) 0 := by
    rw [intRebuildThreshold_zero_eq, sq]
  have ht0W : intRebuildThreshold P (4 * P.M₀) 0 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hM₀W
  let s1 : State := { st with regs := Function.update st.regs 4 (4 * P.M₀ + 2) }
  have r1 : Runs w p ω (.assign 4 (.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 2))) st .normal s1 6 :=
    runs_assign_iff.mpr ⟨4 * P.M₀ + 2, by
      simp [Expr.eval, BinOp.eval, hr0, hw4, hw2, show 4 * P.M₀ < 2 ^ w by omega,
        show 4 * P.M₀ + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hargClog : evalArgs w s1 [.reg 4] = some [4 * P.M₀ + 2] := by
    simp [evalArgs, Expr.eval, s1]
  obtain ⟨s2, cClog, vClog, r2, ⟨hmem2, hvClog⟩, hr5_2, hkeep2, hcClog⟩ :=
    runs_call_of_meetsContract (r := 5) (hclog (4 * P.M₀ + 2))
      hargClog (by simp; omega)
      ⟨rfl, h4M3W, hw2⟩ ω
  have h5Eq : s2.regs 5 = b := hr5_2.trans hvClog
  have hcClog' : cClog ≤ 40 * b + 30 := by
    simp only [argsSize, Expr.size, Scaling.Machine.clogTwoContract] at hcClog
    dsimp only [b]; omega
  let s3 : State := { s2 with regs := Function.update s2.regs 6 (intRebuildThreshold P (4 * P.M₀) 0) }
  let s4 : State := { s3 with regs := Function.update s3.regs 7 0 }
  let s5 : State := { s4 with regs := Function.update s4.regs 8 (P.d + 1) }
  have hr0_2 : s2.regs 0 = P.M₀ := (hkeep2 0 (by decide)).trans (by simp [s1, hr0])
  have hr1_2 : s2.regs 1 = P.k := (hkeep2 1 (by decide)).trans (by simp [s1, hr1])
  have hr2_2 : s2.regs 2 = P.d := (hkeep2 2 (by decide)).trans (by simp [s1, hr2])
  have hr3_2 : s2.regs 3 = tableDst := (hkeep2 3 (by decide)).trans (by simp [s1, hr3])
  have r3 : Runs w p ω (.assign 6 (.bin .div (.bin .div (.reg 0) (.bin .mul (.reg 5) (.reg 5))) (.reg 1)))
      s2 .normal s3 8 :=
    runs_assign_iff.mpr ⟨intRebuildThreshold P (4 * P.M₀) 0, by
      simp [Expr.eval, BinOp.eval, hr0_2, hr1_2, h5Eq, hb2W,
        hdiv1W, ht0Eq, ht0W], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 7 (.const 0)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 8 (.bin .add (.reg 2) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨P.d + 1, by
      simp [Expr.eval, BinOp.eval, s4, s3, hr2_2, hw1, hd1W], rfl, rfl, rfl⟩
  obtain ⟨out, cLoop, rLoop, hcLoop, htabOut, hfrOut, hregOut⟩ :=
    fillIntRebuildThresholdsLoop_runs (w := w) (tableDst := tableDst) (P := P) (p := p) (ω := ω)
      hM₀W hd1W htabW hw1 (P.d + 1) s5 le_rfl
      (by simp [s5, s4, s3, hr1_2]) (by simp [s5, s4, s3, hr3_2])
      (by simp [s5, s4, s3]) (by simp [s5, s4]) (by simp [s5])
      (fun t ht => by omega)
  refine ⟨out, 6 + (cClog + (8 + (2 + (4 + cLoop + 1) + 1) + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, 6, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, cClog, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 8, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 2, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 4, cLoop, r5, rLoop, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, htabOut,
    fun a ha => (hfrOut a ha).trans (by simp [s5, s4, s3, hmem2, s1]),
    fun r h4 h5 h6 h7 h8 => by
      rw [hregOut r h6 h7]
      simp [s5, s4, s3, Function.update_of_ne h8, Function.update_of_ne h7,
        Function.update_of_ne h6, hkeep2 r h5, s1, Function.update_of_ne h4]⟩

/-- Execution of `initOverwriteIntThresholdsBody clog threshold`: given a root directory and
chain header with `(m, d, k)` stored, overwrites `table[0..d]` in-place with
`intRebuildThreshold P (4 * P.M₀) j` (where `P.M₀ = max m threshold`), preserving every other
memory cell. -/
theorem initOverwriteIntThresholdsBody_runs
    {w clog threshold root handle table m V psi alphaPtr qual epsExp pos : ℕ}
    {P : ChainParams} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hw14 : 14 ≤ w)
    (hM₀Eq : P.M₀ = max m threshold)
    (hroot0 : mem root = handle) (hroot1 : mem (root + 1) = table)
    (hchain : ChainInitParametersAt mem handle m V P.d P.k psi alphaPtr qual epsExp)
    (hroot1W : root + 1 < 2 ^ w) (hhandle12W : handle + 12 < 2 ^ w)
    (h4M3W : 4 * P.M₀ + 3 < 2 ^ w)
    (hd1W : P.d + 1 < 2 ^ w) (htabW : table + P.d < 2 ^ w) :
    ∃ out cost,
      Runs w p ω (initOverwriteIntThresholdsBody clog threshold)
        (startState [root] mem pos) (.returned (P.M₀ + intRebuildThreshold P (4 * P.M₀) 0 + 2 * m)) out cost ∧
      cost ≤ 40 * Nat.clog 2 (4 * P.M₀ + 2) + 22 * (P.d + 1) + 140 ∧
      (∀ t ≤ P.d, out.mem (table + t) = intRebuildThreshold P (4 * P.M₀) t) ∧
      (∀ a, a < table ∨ table + P.d < a → out.mem a = mem a) := by
  have hw12 : 12 < 2 ^ w := lt_of_lt_of_le (by decide : 12 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hthrW : threshold < 2 ^ w := by omega
  have hmW : m < 2 ^ w := by omega
  have hm9 : mem (handle + 9) = m := by simpa [Nat.add_assoc] using hchain 0 (by simp)
  have hm11 : mem (handle + 11) = P.d := by simpa [Nat.add_assoc] using hchain 2 (by simp)
  have hm12 : mem (handle + 12) = P.k := by simpa [Nat.add_assoc] using hchain 3 (by simp)
  let s0 := startState [root] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 10 handle }
  let s2 : State := { s1 with regs := Function.update s1.regs 3 table }
  let s3 : State := { s2 with regs := Function.update s2.regs 11 m }
  let s4 : State := { s3 with regs := Function.update s3.regs 2 P.d }
  let s5 : State := { s4 with regs := Function.update s4.regs 1 P.k }
  let s6 : State := { s5 with regs := Function.update s5.regs 0 P.M₀ }
  have r1 : Runs w p ω (.assign 10 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, hroot0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨table, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, show 1 < 2 ^ w by omega, hroot1W, hroot1],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 10) (.const 9)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨m, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 9 < 2 ^ w by omega, show handle + 9 < 2 ^ w by omega, hm9],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 10) (.const 11)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨P.d, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 11 < 2 ^ w by omega, show handle + 11 < 2 ^ w by omega, hm11],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 1 (.load (.bin .add (.reg 10) (.const 12)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨P.k, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, hw12, hhandle12W, hm12], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.cond (.bin .lt (.reg 11) (.const threshold))
      (.assign 0 (.const threshold)) (.assign 0 (.reg 11))) s5 .normal s6 6 := by
    by_cases hlt : m < threshold
    · have hmax : P.M₀ = threshold := by omega
      refine runs_cond_iff.mpr ⟨1, 2, by
        simp [Expr.eval, BinOp.eval, s5, s4, s3, hthrW, hlt, show 1 < 2 ^ w by omega],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
           exact runs_assign_iff.mpr ⟨P.M₀, by simp [Expr.eval, hmax, hthrW], rfl, rfl, rfl⟩,
        by simp [Expr.size]⟩
    · have hmax : P.M₀ = m := by omega
      refine runs_cond_iff.mpr ⟨0, 2, by
        simp [Expr.eval, BinOp.eval, s5, s4, s3, hthrW, hlt, show 0 < 2 ^ w by omega],
        by simp only [↓reduceIte]
           exact runs_assign_iff.mpr ⟨P.M₀, by simp [Expr.eval, s5, s4, s3, hmax], rfl, rfl, rfl⟩,
        by simp [Expr.size]⟩
  obtain ⟨out, cFill, rFill, hcFill, htabOut, hfrOut, hregOut⟩ :=
    fillIntRebuildThresholdsStmt_runs (w := w) (clog := clog) (tableDst := table) (P := P)
      (p := p) (ω := ω) (st := s6) hclog (by omega)
      (by simp [s6]) (by simp [s6, s5]) (by simp [s6, s5, s4]) (by simp [s6, s5, s4, s3, s2])
      h4M3W hd1W htabW
  have hr0Out : out.regs 0 = P.M₀ := (hregOut 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s6])
  have hr3Out : out.regs 3 = table := (hregOut 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s6, s5, s4, s3, s2])
  have hr11Out : out.regs 11 = m := (hregOut 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s6, s5, s4, s3])
  have ht0Val : out.mem table = intRebuildThreshold P (4 * P.M₀) 0 := by
    simpa using htabOut 0 (Nat.zero_le P.d)
  have ht0Le : intRebuildThreshold P (4 * P.M₀) 0 ≤ P.M₀ := Nat.div_le_self _ _
  have hmLeM0 : m ≤ P.M₀ := by omega
  let out1 : State := { out with regs := Function.update out.regs 4 (intRebuildThreshold P (4 * P.M₀) 0) }
  have rLoad0 : Runs w p ω (.assign 4 (.load (.reg 3))) out .normal out1 3 :=
    runs_assign_iff.mpr ⟨intRebuildThreshold P (4 * P.M₀) 0,
      by simp [Expr.eval, hr3Out, ht0Val], rfl, rfl, rfl⟩
  have rRet : Runs w p ω (.ret (.bin .add (.bin .add (.reg 0) (.reg 4)) (.bin .mul (.const 2) (.reg 11))))
      out1 (.returned (P.M₀ + intRebuildThreshold P (4 * P.M₀) 0 + 2 * m)) out1 8 :=
    runs_ret_iff.mpr ⟨P.M₀ + intRebuildThreshold P (4 * P.M₀) 0 + 2 * m, by
      simp [Expr.eval, BinOp.eval, out1, hr0Out, hr11Out, show 2 < 2 ^ w by omega,
        show P.M₀ + intRebuildThreshold P (4 * P.M₀) 0 < 2 ^ w by omega,
        show 2 * m < 2 ^ w by omega,
        show P.M₀ + intRebuildThreshold P (4 * P.M₀) 0 + 2 * m < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  refine ⟨out1, 3 + (5 + (5 + (5 + (5 + (6 + (cFill + (3 + 8 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 6, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨out, cFill, _, rFill,
      runs_seq_iff.mpr (Or.inr ⟨out1, 3, 8, rLoad0, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, htabOut, fun a ha => (hfrOut a ha).trans rfl⟩

end MinCostFlow.MinRatio
