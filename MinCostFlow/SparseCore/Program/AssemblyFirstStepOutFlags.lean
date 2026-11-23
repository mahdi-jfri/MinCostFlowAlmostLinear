module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEmbModel
public import MinCostFlow.SparseCore.Program.ReadSpec
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Phase 4 edge-flag precomputation (`AssemblyFirstStepOutFlags`)

Implements and verifies the deterministic Word-RAM procedure `asmFirstPrepFlagsStmt`
(`[batch, chg, eCap, h]`):
* allocates three zero-initialized `eCap`-word arrays at `[h, h + 3 * eCap)`:
  1. `lastOpPtr = h`: `mem[h + e] = batchLastOp U e` (`1` if last batch op on `e` is insert,
     `2` if delete, `0` otherwise);
  2. `inDelBatPtr = h + eCap`: `mem[h + eCap + e] = if e ∈ batchDeletes U then 1 else 0`;
  3. `inFDelPtr = h + 2 * eCap`: `mem[h + 2 * eCap + e] = if e ∈ c.fDel then 1 else 0`.
* returns `h + 3 * eCap`, preserves all memory below `h`, preserves `ZeroFrom` from `h + 3 * eCap`,
  and runs in `≤ 45 * (U.length + c.fDel.length) + 80` steps (`asmFirstPrepFlags_runs`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- Body of the batch-scanning loop in `asmFirstPrepFlagsStmt`:
registers `0 = batch`, `1 = chg`, `2 = eCap`, `3 = h`, `4 = inDelBatPtr (= h + eCap)`,
`5 = inFDelPtr (= h + 2 * eCap)`, `6 = cur`, `7 = nU`, `8 = i`, `9..12` scratch. -/
def asmFirstPrepFlagsBatchBody : Stmt :=
  .assign 9 (.load (.reg 6)) ;;
  .cond (.bin .eq (.reg 9) (.const 0))
    (.assign 10 (.load (.bin .add (.reg 6) (.const 1))) ;;
     .store (.bin .add (.reg 3) (.reg 10)) (.const 1) ;;
     .assign 6 (.bin .add (.reg 6) (.const 4)))
    (.cond (.bin .eq (.reg 9) (.const 1))
      (.assign 10 (.load (.bin .add (.reg 6) (.const 1))) ;;
       .store (.bin .add (.reg 3) (.reg 10)) (.const 2) ;;
       .store (.bin .add (.reg 4) (.reg 10)) (.const 1) ;;
       .assign 6 (.bin .add (.reg 6) (.const 2)))
      (.assign 10 (.load (.bin .add (.reg 6) (.const 3))) ;;
       .assign 11 (.load (.bin .add (.reg 6) (.const 4))) ;;
       .assign 6 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 10)) (.reg 11))))

/-- Body of the `c.fDel`-scanning loop in `asmFirstPrepFlagsStmt`:
registers `5 = inFDelPtr`, `6 = fDelBase`, `7 = nFDel`, `8 = i`, `9` scratch. -/
def asmFirstPrepFlagsFDelBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 6) (.reg 8))) ;;
  .store (.bin .add (.reg 5) (.reg 9)) (.const 1)

/-- **Phase 4 flag precomputation**, `[batch, chg, eCap, h]`.
Populates `lastOpPtr = h`, `inDelBatPtr = h + eCap`, and `inFDelPtr = h + 2 * eCap` and returns
`h + 3 * eCap`. -/
def asmFirstPrepFlagsStmt : Stmt :=
  .assign 4 (.bin .add (.reg 3) (.reg 2)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 2)) ;;
  .assign 12 (.bin .add (.reg 5) (.reg 2)) ;;
  .assign 7 (.load (.reg 0)) ;;
  .assign 6 (.bin .add (.reg 0) (.const 1)) ;;
  forRange 8 (.const 0) (.reg 7) asmFirstPrepFlagsBatchBody ;;
  .assign 9 (.load (.reg 1)) ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 9))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 1) (.const 2)) (.reg 9)) ;;
  forRange 8 (.const 0) (.reg 7) asmFirstPrepFlagsFDelBody ;;
  .ret (.reg 12)

end

public section

theorem asmFirstPrepFlagsStmt_noRand : asmFirstPrepFlagsStmt.NoRand := by
  simp [asmFirstPrepFlagsStmt, asmFirstPrepFlagsBatchBody, asmFirstPrepFlagsFDelBody,
    forRange, forUp, Stmt.NoRand]

private lemma batchLastOp_append_singleton (U : List Update) (u : Update) (e : ℕ) :
    batchLastOp (U ++ [u]) e =
      match u with
      | .insert e' _ _ => if e = e' then 1 else batchLastOp U e
      | .delete e' => if e = e' then 2 else batchLastOp U e
      | .split _ _ _ _ => batchLastOp U e := by
  induction U with
  | nil =>
    cases u <;> simp [batchLastOp, eq_comm]
  | cons a rest ih =>
    simp only [List.cons_append, batchLastOp_cons, ih]
    cases u with
    | insert e' _ _ =>
      by_cases hee : e = e'
      · simp [hee]
      · simp [hee]
    | delete e' =>
      by_cases hee : e = e'
      · simp [hee]
      · simp [hee]
    | split _ _ _ _ => rfl

private lemma mem_batchDeletes_append_singleton (U : List Update) (u : Update) (e : ℕ) :
    e ∈ batchDeletes (U ++ [u]) ↔
      e ∈ batchDeletes U ∨ u = .delete e := by
  simp only [mem_batchDeletes_iff, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨u', hu' | rfl, rfl⟩
    · exact Or.inl ⟨.delete e, hu', rfl⟩
    · exact Or.inr rfl
  · rintro (⟨u', hu', rfl⟩ | rfl)
    · exact ⟨.delete e, Or.inl hu', rfl⟩
    · exact ⟨.delete e, Or.inr rfl, rfl⟩

/-- **Verification of `asmFirstPrepFlagsStmt`**: populates `[h, h + 3 * eCap)` with `batchLastOp U`,
`batchDeletes U`, and `c.fDel` indicator arrays in `≤ 45 * (U.length + c.fDel.length) + 80` steps. -/
theorem asmFirstPrepFlags_runs {w batch chg eCap h words pos : ℕ} {p : Program}
    {G₀ : MGraph} {U : List Update} {c : LSFChange} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hBat : BatchAt mem₀ batch G₀ U words) (hBat_le : batch + words ≤ h)
    (hCaps : ∀ u ∈ U, match u with | .insert e _ _ => e < eCap | .delete e => e < eCap | .split _ _ _ _ => True)
    (hChg : LSFChangeAt mem₀ chg c) (hChg_le : chg + c.words ≤ h)
    (hfDel_cap : ∀ e ∈ c.fDel, e < eCap)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 3 * eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω asmFirstPrepFlagsStmt (startState [batch, chg, eCap, h] mem₀ pos)
        (.returned (h + 3 * eCap)) st' cost ∧
      (∀ e < eCap, st'.mem (h + e) = batchLastOp U e) ∧
      (∀ e < eCap, st'.mem (h + eCap + e) = if e ∈ batchDeletes U then 1 else 0) ∧
      (∀ e < eCap, st'.mem (h + 2 * eCap + e) = if e ∈ c.fDel then 1 else 0) ∧
      ZeroFrom st'.mem (h + 3 * eCap) ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      cost ≤ 45 * (U.length + c.fDel.length) + 80 := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h5w : 5 < 2 ^ w := by omega
  have hUL : U.length < 2 ^ w := by
    have := batchBodyAt_len_le hBat.2.2; have := hBat.1; omega
  have hFL : c.fDel.length < 2 ^ w := by
    dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega
  set s0 := startState [batch, chg, eCap, h] mem₀ pos
  -- Step 1: setup registers for batch loop
  set r1 := Function.update s0.regs 4 (h + eCap)
  set r2 := Function.update r1 5 (h + 2 * eCap)
  set r3 := Function.update r2 12 (h + 3 * eCap)
  set r4 := Function.update r3 7 U.length
  set r5 := Function.update r4 6 (batch + 1)
  have hsetup : ∃ c0, Runs w p ω
      (.assign 4 (.bin .add (.reg 3) (.reg 2)) ;;
       .assign 5 (.bin .add (.reg 4) (.reg 2)) ;;
       .assign 12 (.bin .add (.reg 5) (.reg 2)) ;;
       .assign 7 (.load (.reg 0)) ;;
       .assign 6 (.bin .add (.reg 0) (.const 1)))
      s0 .normal ⟨mem₀, r5, pos⟩ c0 ∧ c0 ≤ 25 := by
    have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.reg 2))) s0 .normal ⟨mem₀, r1, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨h + eCap,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
          (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega), rfl, rfl, rfl⟩
    have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.reg 2))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨h + 2 * eCap, by
        have h4r : r1 4 = h + eCap := by simp [r1]
        have h2r : r1 2 = eCap := by simp [r1, s0, startState]
        have he5 : (Expr.bin .add (.reg 4) (.reg 2)).eval w ⟨mem₀, r1, pos⟩ = some (h + eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h4r) (Expr.eval_reg_of_eq h2r) (by omega)
        simpa [show h + eCap + eCap = h + 2 * eCap by omega] using he5, rfl, rfl, rfl⟩
    have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 5) (.reg 2))) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨h + 3 * eCap, by
        have h5r : r2 5 = h + 2 * eCap := by simp [r2]
        have h2r : r2 2 = eCap := by simp [r2, r1, s0, startState]
        have he12 : (Expr.bin .add (.reg 5) (.reg 2)).eval w ⟨mem₀, r2, pos⟩ = some (h + 2 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h5r) (Expr.eval_reg_of_eq h2r) (by omega)
        simpa [show h + 2 * eCap + eCap = h + 3 * eCap by omega] using he12, rfl, rfl, rfl⟩
    have ha7 : Runs w p ω (.assign 7 (.load (.reg 0))) ⟨mem₀, r3, pos⟩ .normal ⟨mem₀, r4, pos⟩ 3 :=
      runs_assign_iff.mpr ⟨U.length,
        Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [r3, r2, r1, s0, startState])) hBat.2.1, rfl, rfl, rfl⟩
    have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 0) (.const 1))) ⟨mem₀, r4, pos⟩ .normal ⟨mem₀, r5, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨batch + 1,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1, s0, startState]))
          (Expr.eval_const h1w) (by have := hBat.1; omega), rfl, rfl, rfl⟩
    exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha4,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha5,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha12,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha7, ha6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
  obtain ⟨c0, hr0, hc0⟩ := hsetup
  -- Step 2: batch loop by induction on remaining updates `U.length - k`
  have hBloop : ∀ (k : ℕ) (hk : k ≤ U.length) (cur W : ℕ) (stK : State),
      batch < cur → cur + W ≤ batch + words →
      BatchBodyAt mem₀ cur (G₀.applyBatch (U.take k)) (U.drop k) W →
      stK.regs 1 = chg → stK.regs 3 = h → stK.regs 4 = h + eCap →
      stK.regs 5 = h + 2 * eCap → stK.regs 6 = cur → stK.regs 7 = U.length →
      stK.regs 8 = k → stK.regs 12 = h + 3 * eCap →
      (∀ e < eCap, stK.mem (h + e) = batchLastOp (U.take k) e) →
      (∀ e < eCap, stK.mem (h + eCap + e) = if e ∈ batchDeletes (U.take k) then 1 else 0) →
      (∀ a < h, stK.mem a = mem₀ a) →
      ZeroFrom stK.mem (h + 2 * eCap) →
      ∃ st1 c1,
        Runs w p ω (forUp 8 (.reg 7) asmFirstPrepFlagsBatchBody) stK .normal st1 c1 ∧
        st1.regs 1 = chg ∧ st1.regs 5 = h + 2 * eCap ∧ st1.regs 12 = h + 3 * eCap ∧
        (∀ e < eCap, st1.mem (h + e) = batchLastOp U e) ∧
        (∀ e < eCap, st1.mem (h + eCap + e) = if e ∈ batchDeletes U then 1 else 0) ∧
        (∀ a < h, st1.mem a = mem₀ a) ∧
        ZeroFrom st1.mem (h + 2 * eCap) ∧
        c1 ≤ 45 * (U.length - k) + 6 := by
    intro k
    induction hrem : U.length - k generalizing k with
    | zero =>
      intro hk cur W stK _ _ _ r1k r3k r4k r5k _ r7k r8k r12k hlo hdb hfr hz2
      have hkEq : k = U.length := by omega
      subst hkEq
      rw [List.take_length] at hlo hdb
      have hcond : (Expr.bin .lt (.reg 8) (.reg 7)).eval w stK = some 0 := by
        simp [Expr.eval, r7k, r8k, BinOp.eval, (by omega : 0 < 2 ^ w)]
      exact ⟨stK, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        r1k, r5k, r12k, hlo, hdb, hfr, hz2, by omega⟩
    | succ d ih =>
      intro hk cur W stK hclo hchi hBB r1k r3k r4k r5k r6k r7k r8k r12k hlo hdb hfr hz2
      have hklt : k < U.length := by omega
      obtain ⟨u, hu_eq⟩ : ∃ u, U[k]'hklt = u := ⟨_, rfl⟩
      have hdrop : U.drop k = u :: U.drop (k + 1) := by rw [← hu_eq]; exact List.drop_eq_getElem_cons hklt
      have htake : U.take (k + 1) = U.take k ++ [u] := by rw [← hu_eq]; exact List.take_succ_eq_append_getElem hklt
      rw [hdrop] at hBB
      obtain ⟨len, hlenW, huAt, hBBrest⟩ := hBB
      have huc := hCaps u (hu_eq ▸ List.getElem_mem hklt)
      have hbodyStep : ∃ stA cA,
          Runs w p ω asmFirstPrepFlagsBatchBody stK .normal stA cA ∧
          stA.regs 1 = chg ∧ stA.regs 3 = h ∧ stA.regs 4 = h + eCap ∧
          stA.regs 5 = h + 2 * eCap ∧ stA.regs 6 = cur + len ∧ stA.regs 7 = U.length ∧
          stA.regs 8 = k ∧ stA.regs 12 = h + 3 * eCap ∧
          (∀ e < eCap, stA.mem (h + e) = batchLastOp (U.take (k + 1)) e) ∧
          (∀ e < eCap, stA.mem (h + eCap + e) = if e ∈ batchDeletes (U.take (k + 1)) then 1 else 0) ∧
          (∀ a < h, stA.mem a = mem₀ a) ∧ ZeroFrom stA.mem (h + 2 * eCap) ∧ cA ≤ 34 := by
        cases u with
        | insert e0 a0 b0 =>
          rcases huAt with ⟨rfl, hL⟩
          have hm0 : stK.mem cur = 0 := (hfr cur (by omega)).trans (by simpa using hL 0 (by simp))
          have hm1 : stK.mem (cur + 1) = e0 := (hfr (cur + 1) (by omega)).trans (by simpa using hL 1 (by simp))
          set rA := Function.update stK.regs 9 0
          set rB := Function.update rA 10 e0
          set mA := Function.update stK.mem (h + e0) 1
          set rC := Function.update rB 6 (cur + 4)
          have h9 : Runs w p ω (.assign 9 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
          have heC : (Expr.bin .eq (.reg 9) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, BinOp.eval, h1w, (by omega : 0 < 2 ^ w)]
          have h10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.const 1))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨e0, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h1w) (by omega)) hm1,
              rfl, rfl, rfl⟩
          have hst : Runs w p ω (.store (.bin .add (.reg 3) (.reg 10)) (.const 1))
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨mA, rB, stK.pos⟩ 5 :=
            runs_store_iff.mpr ⟨h + e0, 1,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r3k]))
                (Expr.eval_reg_of_eq (by simp [rB])) (by omega),
              Expr.eval_const h1w, rfl, rfl, rfl⟩
          have h6 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 4)))
              ⟨mA, rB, stK.pos⟩ .normal ⟨mA, rC, stK.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 4,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r6k])) (Expr.eval_const h4w) (by omega),
              rfl, rfl, rfl⟩
          refine ⟨⟨mA, rC, stK.pos⟩, 24, runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
            runs_cond_iff.mpr ⟨1, 16, heC, by
              simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst, h6, rfl⟩), rfl⟩), rfl⟩, rfl⟩),
            by simp [rC, rB, rA, r1k], by simp [rC, rB, rA, r3k], by simp [rC, rB, rA, r4k],
            by simp [rC, rB, rA, r5k], by simp [rC], by simp [rC, rB, rA, r7k],
            by simp [rC, rB, rA, r8k], by simp [rC, rB, rA, r12k], ?_, ?_, ?_, ?_, by omega⟩
          · intro e he; rw [htake, batchLastOp_append_singleton]
            by_cases hee : e = e0
            · subst hee; simp [mA]
            · simp only [mA, Function.update_of_ne (by omega : h + e ≠ h + e0), hee, ↓reduceIte]; exact hlo e he
          · intro e he; simp only [htake, mem_batchDeletes_append_singleton,
              mA, Function.update_of_ne (by omega : h + eCap + e ≠ h + e0), reduceCtorEq, or_false]
            exact hdb e he
          · intro a ha; simp only [mA, Function.update_of_ne (by omega : a ≠ h + e0)]; exact hfr a ha
          · intro a ha; simp only [mA, Function.update_of_ne (by omega : a ≠ h + e0)]; exact hz2 a ha
        | delete e0 =>
          rcases huAt with ⟨rfl, hL⟩
          have hm0 : stK.mem cur = 1 := (hfr cur (by omega)).trans (by simpa using hL 0 (by simp))
          have hm1 : stK.mem (cur + 1) = e0 := (hfr (cur + 1) (by omega)).trans (by simpa using hL 1 (by simp))
          set rA := Function.update stK.regs 9 1
          set rB := Function.update rA 10 e0
          set mA := Function.update stK.mem (h + e0) 2
          set mB := Function.update mA (h + eCap + e0) 1
          set rC := Function.update rB 6 (cur + 2)
          have h9 : Runs w p ω (.assign 9 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
          have heC0 : (Expr.bin .eq (.reg 9) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            simp [Expr.eval, rA, BinOp.eval, (by omega : 0 < 2 ^ w)]
          have heC1 : (Expr.bin .eq (.reg 9) (.const 1)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, BinOp.eval, h1w]
          have h10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.const 1))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨e0, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h1w) (by omega)) hm1,
              rfl, rfl, rfl⟩
          have hst1 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 10)) (.const 2))
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨mA, rB, stK.pos⟩ 5 :=
            runs_store_iff.mpr ⟨h + e0, 2,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r3k]))
                (Expr.eval_reg_of_eq (by simp [rB])) (by omega),
              Expr.eval_const h2w, rfl, rfl, rfl⟩
          have hst2 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 10)) (.const 1))
              ⟨mA, rB, stK.pos⟩ .normal ⟨mB, rB, stK.pos⟩ 5 :=
            runs_store_iff.mpr ⟨h + eCap + e0, 1,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r4k]))
                (Expr.eval_reg_of_eq (by simp [rB])) (by omega),
              Expr.eval_const h1w, rfl, rfl, rfl⟩
          have h6 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 2)))
              ⟨mB, rB, stK.pos⟩ .normal ⟨mB, rC, stK.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 2,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r6k])) (Expr.eval_const h2w) (by omega),
              rfl, rfl, rfl⟩
          refine ⟨⟨mB, rC, stK.pos⟩, 34, runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
            runs_cond_iff.mpr ⟨0, 26, heC0, by
              simpa using runs_cond_iff.mpr ⟨1, 22, heC1, by
                simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst1,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst2, h6, rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩, rfl⟩),
            by simp [rC, rB, rA, r1k], by simp [rC, rB, rA, r3k], by simp [rC, rB, rA, r4k],
            by simp [rC, rB, rA, r5k], by simp [rC], by simp [rC, rB, rA, r7k],
            by simp [rC, rB, rA, r8k], by simp [rC, rB, rA, r12k], ?_, ?_, ?_, ?_, ?_⟩
          · intro e he; rw [htake, batchLastOp_append_singleton]
            simp only [mB, Function.update_of_ne (by omega : h + e ≠ h + eCap + e0)]
            by_cases hee : e = e0
            · subst hee; simp [mA]
            · simp only [mA, Function.update_of_ne (by omega : h + e ≠ h + e0), hee, ↓reduceIte]; exact hlo e he
          · intro e he
            have hiff : e ∈ batchDeletes (U.take (k + 1)) ↔ e ∈ batchDeletes (U.take k) ∨ e0 = e := by
              rw [htake, mem_batchDeletes_append_singleton]; simp
            by_cases hee : e = e0
            · subst hee; simp [mB, hiff]
            · simp only [hiff, show e0 ≠ e from Ne.symm hee, or_false,
                mB, Function.update_of_ne (by omega : h + eCap + e ≠ h + eCap + e0),
                mA, Function.update_of_ne (by omega : h + eCap + e ≠ h + e0)]
              exact hdb e he
          · intro a ha
            simp only [mB, Function.update_of_ne (by omega : a ≠ h + eCap + e0),
              mA, Function.update_of_ne (by omega : a ≠ h + e0)]
            exact hfr a ha
          · intro a ha
            simp only [mB, Function.update_of_ne (by omega : a ≠ h + eCap + e0),
              mA, Function.update_of_ne (by omega : a ≠ h + e0)]
            exact hz2 a ha
          · omega
        | split v v' St Sh =>
          obtain ⟨tag, Lt, Lh, htag, hlen, hL⟩ :
              ∃ tag Lt Lh, (tag = 2 ∨ tag = 3) ∧ len = 5 + Lt.length + Lh.length ∧
                ListAt mem₀ cur ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
            rcases huAt with ⟨Lt, Lh, _, _, _, _, hlen, hL⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hL⟩
            · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hL⟩
            · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hL⟩
          have hm0 : stK.mem cur = tag := (hfr cur (by omega)).trans (by simpa using hL 0 (by simp))
          have hm3 : stK.mem (cur + 3) = Lt.length := (hfr (cur + 3) (by omega)).trans (by simpa using hL 3 (by simp))
          have hm4 : stK.mem (cur + 4) = Lh.length := (hfr (cur + 4) (by omega)).trans (by simpa using hL 4 (by simp))
          set rA := Function.update stK.regs 9 tag
          set rB := Function.update rA 10 Lt.length
          set rC := Function.update rB 11 Lh.length
          set rD := Function.update rC 6 (cur + len)
          have h9 : Runs w p ω (.assign 9 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
          have heC0 : (Expr.bin .eq (.reg 9) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            rcases htag with rfl | rfl <;> simp [Expr.eval, rA, BinOp.eval, (by omega : 0 < 2 ^ w)]
          have heC1 : (Expr.bin .eq (.reg 9) (.const 1)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            rcases htag with rfl | rfl <;> simp [Expr.eval, rA, BinOp.eval, h1w, (by omega : 0 < 2 ^ w)]
          have h10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.const 3))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨Lt.length, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h3w) (by omega)) hm3,
              rfl, rfl, rfl⟩
          have h11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 6) (.const 4))))
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stK.mem, rC, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨Lh.length, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r6k])) (Expr.eval_const h4w) (by omega)) hm4,
              rfl, rfl, rfl⟩
          have h6 : Runs w p ω (.assign 6 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 10)) (.reg 11)))
              ⟨stK.mem, rC, stK.pos⟩ .normal ⟨stK.mem, rD, stK.pos⟩ 8 := by
            have hrC6 : rC 6 = cur := by simp [rC, rB, rA, r6k]
            have hrC10 : rC 10 = Lt.length := by simp [rC, rB]
            have hrC11 : rC 11 = Lh.length := by simp [rC]
            have he1 : (Expr.bin .add (.reg 6) (.const 5)).eval w ⟨stK.mem, rC, stK.pos⟩ = some (cur + 5) :=
              Expr.eval_add (Expr.eval_reg_of_eq hrC6) (Expr.eval_const h5w) (by omega)
            have he2 : (Expr.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 10)).eval w ⟨stK.mem, rC, stK.pos⟩ =
                some (cur + 5 + Lt.length) :=
              Expr.eval_add he1 (Expr.eval_reg_of_eq hrC10) (by omega)
            have he : (Expr.bin .add (.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 10)) (.reg 11)).eval w
                ⟨stK.mem, rC, stK.pos⟩ = some (cur + 5 + Lt.length + Lh.length) :=
              Expr.eval_add he2 (Expr.eval_reg_of_eq hrC11) (by omega)
            rw [show cur + 5 + Lt.length + Lh.length = cur + len by omega] at he
            exact runs_assign_iff.mpr ⟨cur + len, he, rfl, rfl, rfl⟩
          refine ⟨⟨stK.mem, rD, stK.pos⟩, 32, runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
            runs_cond_iff.mpr ⟨0, 24, heC0, by
              simpa using runs_cond_iff.mpr ⟨0, 20, heC1, by
                simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, h11, h6, rfl⟩), rfl⟩), rfl⟩, rfl⟩, rfl⟩),
            by simp [rD, rC, rB, rA, r1k], by simp [rD, rC, rB, rA, r3k], by simp [rD, rC, rB, rA, r4k],
            by simp [rD, rC, rB, rA, r5k], by simp [rD], by simp [rD, rC, rB, rA, r7k],
            by simp [rD, rC, rB, rA, r8k], by simp [rD, rC, rB, rA, r12k], ?_, ?_, hfr, hz2, by omega⟩
          · intro e he; rw [htake, batchLastOp_append_singleton]; exact hlo e he
          · intro e he; simp only [htake, mem_batchDeletes_append_singleton, reduceCtorEq, or_false]
            exact hdb e he
      -- Note: in `delete` branch `cA = 34`, so let's handle both `≤ 34` cleanly below!
      obtain ⟨stA, cA, hrA, r1A, r3A, r4A, r5A, r6A, r7A, r8A, r12A, hloA, hdbA, hfrA, hzA, hcA⟩ := hbodyStep
      set stB : State := ⟨stA.mem, Function.update stA.regs 8 (k + 1), stA.pos⟩
      have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) stA .normal stB 4 :=
        runs_assign_iff.mpr ⟨k + 1, Expr.eval_add (Expr.eval_reg_of_eq r8A) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
      have hGnext : G₀.applyBatch (U.take (k + 1)) = (G₀.applyBatch (U.take k)).applyUpdate u := by
        rw [htake, applyBatch_append]; rfl
      obtain ⟨st1, c1, hr1, r1f, r5f, r12f, hlo1, hdb1, hfr1, hz1, hc1⟩ :=
        ih (k + 1) (by omega) (by omega) (cur + len) (W - len) stB (by omega) (by omega)
          (hGnext.symm ▸ hBBrest)
          (by simp [stB, r1A]) (by simp [stB, r3A]) (by simp [stB, r4A]) (by simp [stB, r5A])
          (by simp [stB, r6A]) (by simp [stB, r7A]) (by simp [stB]) (by simp [stB, r12A])
          hloA hdbA hfrA hzA
      have hcond : (Expr.bin .lt (.reg 8) (.reg 7)).eval w stK = some 1 := by
        simp [Expr.eval, r7k, r8k, BinOp.eval, hklt, h1w]
      exact ⟨st1, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stB, _, c1, hcond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨stA, cA, 4, hrA, ha8, rfl⟩), hr1, rfl⟩)),
        r1f, r5f, r12f, hlo1, hdb1, hfr1, hz1, by simp only [Expr.size]; omega⟩
  -- Run batch loop
  set stB0 : State := ⟨mem₀, Function.update r5 8 0, pos⟩
  have ha8_0 : Runs w p ω (.assign 8 (.const 0)) ⟨mem₀, r5, pos⟩ .normal stB0 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  obtain ⟨st1, c1, hrB, r1_1, r5_1, r12_1, hlo1, hdb1, hfr1, hz1, hc1⟩ :=
    hBloop 0 (Nat.zero_le _) (batch + 1) (words - 1) stB0 (by omega) (by have := hBat.1; omega)
      hBat.2.2 (by simp [stB0, r5, r4, r3, r2, r1, s0, startState])
      (by simp [stB0, r5, r4, r3, r2, r1, s0, startState])
      (by simp [stB0, r5, r4, r3, r2, r1]) (by simp [stB0, r5, r4, r3, r2])
      (by simp [stB0, r5]) (by simp [stB0, r5, r4]) (by simp [stB0])
      (by simp [stB0, r5, r4, r3])
      (fun e _ => by simp [stB0, hz (h + e) (by omega)])
      (fun e _ => by simp [stB0, hz (h + eCap + e) (by omega), batchDeletes])
      (fun _ _ => rfl) (fun a ha => hz a (by omega))
  -- Step 3: setup & run `c.fDel` loop
  have hchg0 : st1.mem chg = c.roots.length :=
    (hfr1 chg (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega)).trans hChg.1
  have hchg1 : st1.mem (chg + 1 + c.roots.length) = c.fDel.length :=
    (hfr1 (chg + 1 + c.roots.length) (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega)).trans hChg.2.2.1
  set rF1 := Function.update st1.regs 9 c.roots.length
  set rF2 := Function.update rF1 7 c.fDel.length
  set rF3 := Function.update rF2 6 (chg + 2 + c.roots.length)
  have hsetupF : ∃ cF0, Runs w p ω
      (.assign 9 (.load (.reg 1)) ;;
       .assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 9))) ;;
       .assign 6 (.bin .add (.bin .add (.reg 1) (.const 2)) (.reg 9)))
      st1 .normal ⟨st1.mem, rF3, st1.pos⟩ cF0 ∧ cF0 ≤ 20 := by
    have h9 : Runs w p ω (.assign 9 (.load (.reg 1))) st1 .normal ⟨st1.mem, rF1, st1.pos⟩ 3 :=
      runs_assign_iff.mpr ⟨c.roots.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r1_1) hchg0, rfl, rfl, rfl⟩
    have h7 : Runs w p ω (.assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 9))))
        ⟨st1.mem, rF1, st1.pos⟩ .normal ⟨st1.mem, rF2, st1.pos⟩ 7 :=
      runs_assign_iff.mpr ⟨c.fDel.length, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rF1, r1_1]))
          (Expr.eval_const h1w) (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega))
          (Expr.eval_reg_of_eq (by simp [rF1])) (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega))
        hchg1, rfl, rfl, rfl⟩
    have h6 : Runs w p ω (.assign 6 (.bin .add (.bin .add (.reg 1) (.const 2)) (.reg 9)))
        ⟨st1.mem, rF2, st1.pos⟩ .normal ⟨st1.mem, rF3, st1.pos⟩ 6 :=
      runs_assign_iff.mpr ⟨chg + 2 + c.roots.length,
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rF2, rF1, r1_1]))
          (Expr.eval_const h2w) (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega))
          (Expr.eval_reg_of_eq (by simp [rF2, rF1])) (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega),
        rfl, rfl, rfl⟩
    exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9, runs_seq_iff.mpr (Or.inr ⟨_, _, _, h7, h6, rfl⟩), rfl⟩), by omega⟩
  obtain ⟨cF0, hrF0, hcF0⟩ := hsetupF
  let fInv : ℕ → State → Prop := fun i st =>
    st.regs 5 = h + 2 * eCap ∧ st.regs 6 = chg + 2 + c.roots.length ∧
    st.regs 7 = c.fDel.length ∧ st.regs 8 = i ∧ st.regs 12 = h + 3 * eCap ∧
    (∀ e < eCap, st.mem (h + 2 * eCap + e) = if e ∈ c.fDel.take i then 1 else 0) ∧
    (∀ a, a < h + 2 * eCap ∨ h + 3 * eCap ≤ a → st.mem a = st1.mem a)
  have hFloop := Triple.forRange_le (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := asmFirstPrepFlagsFDelBody)
    (P := fun st => fInv 0 { st with regs := Function.update st.regs 8 0 })
    (Inv := fInv) (fun _ => 15) 0 c.fDel.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun i _ hi st ω' ⟨hr5, hr6, hr7, hr8, hr12, hfd, hfrF⟩ => by
      set e := c.fDel[i]'hi
      have heCap : e < eCap := hfDel_cap e (List.getElem_mem hi)
      have hme : st.mem (chg + 2 + c.roots.length + i) = e := by
        rw [hfrF _ (Or.inl (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega)),
          hfr1 _ (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega)]
        exact hChg.2.2.2 i hi
      set rA := Function.update st.regs 9 e
      set mA := Function.update st.mem (h + 2 * eCap + e) 1
      have h9 : Runs w p ω' (.assign 9 (.load (.bin .add (.reg 6) (.reg 8)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr6) (Expr.eval_reg_of_eq hr8)
            (by dsimp only [LSFChange.words, LSFChange.size] at hChg_le; omega)) hme, rfl, rfl, rfl⟩
      have hst : Runs w p ω' (.store (.bin .add (.reg 5) (.reg 9)) (.const 1))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨mA, rA, st.pos⟩ 5 :=
        runs_store_iff.mpr ⟨h + 2 * eCap + e, 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr5])) (Expr.eval_reg_of_eq (by simp [rA])) (by omega),
          Expr.eval_const h1w, rfl, rfl, rfl⟩
      refine ⟨.normal, ⟨mA, rA, st.pos⟩, 11, runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9, hst, rfl⟩),
        ⟨⟨by simp [rA, hr5], by simp [rA, hr6], by simp [rA, hr7], by simp, by simp [rA, hr12], ?_, ?_⟩,
         by simp [rA, hr8]⟩, show 11 ≤ 15 by omega⟩
      · intro e' he'
        change mA (h + 2 * eCap + e') = if e' ∈ c.fDel.take (i + 1) then 1 else 0
        simp only [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
        by_cases hee : e' = e
        · subst hee; simp [mA, e]
        · have hne : h + 2 * eCap + e' ≠ h + 2 * eCap + e := by omega
          simp only [mA, Function.update_of_ne hne, show e' ≠ c.fDel[i] from hee, or_false]
          exact hfd e' he'
      · intro a ha
        dsimp only [mA]
        rw [Function.update_of_ne (show a ≠ h + 2 * eCap + e by rcases ha with h1 | h2 <;> omega)]
        exact hfrF a ha)
  obtain ⟨oF, st2, cF, hrF, hpostF, hcF⟩ := hFloop ⟨st1.mem, rF3, st1.pos⟩ ω
    ⟨by simp [rF3, rF2, rF1, r5_1], by simp [rF3], by simp [rF3, rF2], by simp,
     by simp [rF3, rF2, rF1, r12_1],
     fun e he => by simp [hz1 (h + 2 * eCap + e) (by omega)], fun _ _ => rfl⟩
  cases oF with
  | returned _ => cases hpostF
  | normal =>
  obtain ⟨-, -, -, -, hr12_2, hfd2, hfr2⟩ := hpostF
  rw [List.take_length] at hfd2
  have hrRet : Runs w p ω (.ret (.reg 12)) st2 (.returned (h + 3 * eCap)) st2 2 :=
    runs_ret_iff.mpr ⟨h + 3 * eCap, Expr.eval_reg_of_eq hr12_2, rfl, rfl, rfl⟩
  have hrFull' : ∃ cTot, Runs w p ω asmFirstPrepFlagsStmt s0 (.returned (h + 3 * eCap)) st2 cTot ∧
      cTot ≤ 45 * (U.length + c.fDel.length) + 80 := by
    have hrc : rangeCost (fun _ => 15) 0 c.fDel.length = 15 * c.fDel.length := by
      simp [rangeCost, Nat.mul_comm]
    dsimp only at hcF; simp only [hrc, Nat.sub_zero, Expr.size] at hcF
    have hseqB : Runs w p ω (forRange 8 (.const 0) (.reg 7) asmFirstPrepFlagsBatchBody)
        ⟨mem₀, r5, pos⟩ .normal st1 (2 + c1 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨stB0, 2, c1, ha8_0, hrB, rfl⟩)
    -- Re-associate `asmFirstPrepFlagsStmt` directly via `runs_seq_iff`
    rcases (runs_seq_iff.mp hr0).resolve_left (by simp) with ⟨sA1, cA1, cA1r, ha4, hrA1, rfl⟩
    rcases (runs_seq_iff.mp hrA1).resolve_left (by simp) with ⟨sA2, cA2, cA2r, ha5, hrA2, rfl⟩
    rcases (runs_seq_iff.mp hrA2).resolve_left (by simp) with ⟨sA3, cA3, cA3r, ha12, hrA3, rfl⟩
    rcases (runs_seq_iff.mp hrA3).resolve_left (by simp) with ⟨sA4, cA4, cA4r, ha7, ha6, rfl⟩
    rcases (runs_seq_iff.mp hrF0).resolve_left (by simp) with ⟨sF1, cF1, cF1r, hf9, hrF1, rfl⟩
    rcases (runs_seq_iff.mp hrF1).resolve_left (by simp) with ⟨sF2, cF2, cF2r, hf7, hf6, rfl⟩
    refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha4,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha5,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha12,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha7,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hseqB,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hf9,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, hf7,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hf6,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrF, hrRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
    omega
  obtain ⟨cTot, hrTot, hcTot⟩ := hrFull'
  exact ⟨st2, cTot, hrTot,
    fun e he => (hfr2 (h + e) (Or.inl (by omega))).trans (hlo1 e he),
    fun e he => (hfr2 (h + eCap + e) (Or.inl (by omega))).trans (hdb1 e he),
    hfd2,
    fun a ha => (hfr2 a (Or.inr ha)).trans (hz1 a (by omega)),
    fun a ha => (hfr2 a (Or.inl (by omega))).trans (hfr1 a ha),
    hcTot⟩

end

end MinCostFlow.SparseCore.Program
