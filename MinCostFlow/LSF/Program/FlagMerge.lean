module

public import MinCostFlow.LSF.Program.FROwn

/-!
# The flags of the first root set

The first root set of the data structure is `C_reps ∪ boundary W_T ∪ ends of the high edges`
(`initLSFWith`). Each part comes from a different pass, in a different form: the boundary as
flags on the vertex indices, the component representatives as a list of vertices, and the high
edges as flags on the edge positions, with the vertex indices of their ends in two arrays.

`flagMergeProc` writes one flag per vertex index for the union. It first copies the boundary
flags, then sets the flag of the index of each representative (read through the table `vIdx`,
which stores index plus one), then sets the flags of both ends of each high edge. The cost is
`O(n + cnt + m0)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- Args: `[n, cnt, m0, bndPtr, repPtr, vIdxPtr, highPtr, euPtr, evPtr, outPtr]`. -/
def flagMergeProc : Stmt :=
  forRange 10 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 9) (.reg 10)) (.load (.bin .add (.reg 3) (.reg 10)))) ;;
  forRange 11 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 9)
      (.bin .sub (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4) (.reg 11))))) (.const 1)))
      (.const 1)) ;;
  forRange 12 (.const 0) (.reg 2)
    (.cond (.load (.bin .add (.reg 6) (.reg 12)))
      (.store (.bin .add (.reg 9) (.load (.bin .add (.reg 7) (.reg 12)))) (.const 1) ;;
       .store (.bin .add (.reg 9) (.load (.bin .add (.reg 8) (.reg 12)))) (.const 1))
      .nop) ;;
  .ret (.const 0)

lemma flagMergeProc_noRand : flagMergeProc.NoRand := by
  simp [flagMergeProc, forRange, forUp, Stmt.NoRand]

/-- The index of representative `j`. -/
def repIdx (mem : ℕ → ℕ) (repPtr vIdxPtr j : ℕ) : ℕ := mem (vIdxPtr + mem (repPtr + j)) - 1

/-- The merged flag condition of index `y`. -/
def MergedFlag (mem : ℕ → ℕ) (cnt m0 bndPtr repPtr vIdxPtr highPtr euPtr evPtr y : ℕ) : Prop :=
  mem (bndPtr + y) = 1 ∨ (∃ j < cnt, repIdx mem repPtr vIdxPtr j = y) ∨
    ∃ t < m0, mem (highPtr + t) = 1 ∧ (mem (euPtr + t) = y ∨ mem (evPtr + t) = y)

open Classical in
/-- The contract of `flagMergeProc`. All inputs lie below the output flags. -/
def flagMergeContract (w : ℕ) : Contract where
  pre args mem := ∃ (n cnt m0 bndPtr repPtr vIdxPtr highPtr euPtr evPtr outPtr : ℕ),
    args = [n, cnt, m0, bndPtr, repPtr, vIdxPtr, highPtr, euPtr, evPtr, outPtr] ∧
    16 ≤ 2 ^ w ∧ bndPtr + n ≤ outPtr ∧ repPtr + cnt ≤ outPtr ∧ highPtr + m0 ≤ outPtr ∧
    euPtr + m0 ≤ outPtr ∧ evPtr + m0 ≤ outPtr ∧ outPtr + n < 2 ^ w ∧
    (∀ y < n, mem (bndPtr + y) ≤ 1) ∧
    (∀ j < cnt, vIdxPtr + mem (repPtr + j) < outPtr ∧ repIdx mem repPtr vIdxPtr j < n) ∧
    (∀ t < m0, mem (highPtr + t) ≤ 1 ∧ mem (euPtr + t) < n ∧ mem (evPtr + t) < n)
  post args mem ret mem' := ∃ (n cnt m0 bndPtr repPtr vIdxPtr highPtr euPtr evPtr outPtr : ℕ),
    args = [n, cnt, m0, bndPtr, repPtr, vIdxPtr, highPtr, euPtr, evPtr, outPtr] ∧ ret = 0 ∧
    (∀ a, a < outPtr ∨ outPtr + n ≤ a → mem' a = mem a) ∧
    ∀ y < n, mem' (outPtr + y) =
      if MergedFlag mem cnt m0 bndPtr repPtr vIdxPtr highPtr euPtr evPtr y then 1 else 0
  cost args _ := 40 * args.getD 0 0 + 40 * args.getD 1 0 + 60 * args.getD 2 0 + 100

lemma exists_lt_succ_iff' {P : ℕ → Prop} {k : ℕ} :
    (∃ j < k + 1, P j) ↔ (∃ j < k, P j) ∨ P k := by
  constructor
  · rintro ⟨j, hj, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · exact Or.inl ⟨j, h, hp⟩
    · exact Or.inr hp
  · rintro (⟨j, hj, hp⟩ | hp)
    · exact ⟨j, by omega, hp⟩
    · exact ⟨k, by omega, hp⟩

theorem flagMerge_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some flagMergeProc) :
    MeetsContract w p b (flagMergeContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, cnt, m0, bndPtr, repPtr, vIdxPtr, highPtr, euPtr, evPtr, outPtr, rfl, hw16, hb, hr,
    hh, heu, hev, how, hb1, hrep, hedge⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, cnt, m0, bndPtr, repPtr, vIdxPtr, highPtr, euPtr, evPtr, outPtr] with hargs
  have hR0 : ∀ i < 10, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 10, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hnw : n < 2 ^ w := hwa 0 (by omega)
  have hcw : cnt < 2 ^ w := hwa 1 (by omega)
  have hmw : m0 < 2 ^ w := hwa 2 (by omega)
  -- the predicates after each loop
  let PB : ℕ → Prop := fun y => mem (bndPtr + y) = 1
  let PA : ℕ → ℕ → Prop := fun k y => PB y ∨ ∃ j < k, repIdx mem repPtr vIdxPtr j = y
  let PC : ℕ → ℕ → Prop := fun k y => PA cnt y ∨
    ∃ t < k, mem (highPtr + t) = 1 ∧ (mem (euPtr + t) = y ∨ mem (evPtr + t) = y)
  -- 1. copy the boundary flags
  let Inv1 : ℕ → State → Prop := fun k st =>
    (∀ i < 10, st.regs i = args.getD i 0) ∧ st.regs 10 = k ∧
    (∀ a, a < outPtr ∨ outPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ y < k, st.mem (outPtr + y) = mem (bndPtr + y)
  have hloop1 : Triple w p (fun st => st = startState args mem pos)
      (forRange 10 (.const 0) (.reg 0)
        (.store (.bin .add (.reg 9) (.reg 10)) (.load (.bin .add (.reg 3) (.reg 10)))))
      (normalPost (Inv1 n))
      (fun _ => (n - 0) * (20 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 20 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl,
        fun y hy => absurd hy (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 10 by omega)]
      exact hR0 i hi
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro k _ hk st ω' hI
      obtain ⟨hR, h10, hfr, hc⟩ := hI
      have r3 : st.regs 3 = bndPtr := hR 3 (by omega)
      have r9 : st.regs 9 = outPtr := hR 9 (by omega)
      have hmb : st.mem (bndPtr + k) = mem (bndPtr + k) := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      refine runs_store_le (x := outPtr + k) (v := mem (bndPtr + k)) (by eval_expr)
        (by rw [← hmb]; eval_expr)
        ⟨⟨fun i hi => ?_, by simpa using h10, fun a ha => ?_, fun y hy => ?_⟩, by simpa using h10⟩
        (by simp [Expr.size])
      · simp only [Function.update_of_ne (show i ≠ 10 by omega)]; exact hR i hi
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
        · rw [Function.update_of_ne (by omega)]; exact hc y hy
        · rw [Function.update_self]
  -- 2. the representatives
  let Inv2 : ℕ → State → Prop := fun k st =>
    (∀ i < 10, st.regs i = args.getD i 0) ∧ st.regs 11 = k ∧
    (∀ a, a < outPtr ∨ outPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ y < n, st.mem (outPtr + y) = if PA k y then 1 else 0
  have hloop2 : ∀ st₀ : State, Inv1 n st₀ → Triple w p (fun st => st = st₀)
      (forRange 11 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 9)
          (.bin .sub (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4) (.reg 11)))))
            (.const 1)))
          (.const 1)))
      (normalPost (Inv2 cnt))
      (fun _ => (cnt - 0) * (30 + (Expr.reg 1).size + 8) +
        ((Expr.const 0).size + (Expr.reg 1).size + 5)) := by
    intro st₀ hI1
    refine Triple.forRange_const 30 0 cnt (by omega) hw1 (fun _ => hcw) ?_ ?_ ?_ ?_
    · rintro st rfl
      obtain ⟨hR, -, hfr, hc⟩ := hI1
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hfr, fun y hy => ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 11 by omega)]
        exact hR i hi
      · rw [hc y hy]
        have hb' := hb1 y hy
        by_cases h : mem (bndPtr + y) = 1
        · rw [if_pos (Or.inl h), h]
        · rw [if_neg (by rintro (h' | ⟨j, hj, -⟩); exact h h'; omega)]
          omega
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r1 : st.regs 1 = cnt := hI.1 1 (by omega)
      eval_expr
    · intro k _ hk st ω' hI
      obtain ⟨hR, h11, hfr, hc⟩ := hI
      have r4 : st.regs 4 = repPtr := hR 4 (by omega)
      have r5 : st.regs 5 = vIdxPtr := hR 5 (by omega)
      have r9 : st.regs 9 = outPtr := hR 9 (by omega)
      obtain ⟨hvl, hidx⟩ := hrep k hk
      have hm1 : st.mem (repPtr + k) = mem (repPtr + k) := hfr _ (Or.inl (by omega))
      have hm2 : st.mem (vIdxPtr + mem (repPtr + k)) = mem (vIdxPtr + mem (repPtr + k)) :=
        hfr _ (Or.inl hvl)
      have hidx' : mem (vIdxPtr + mem (repPtr + k)) - 1 < n := hidx
      refine runs_start_le ?_
      refine runs_store_le (x := outPtr + repIdx mem repPtr vIdxPtr k) (v := 1)
        (by
          unfold repIdx
          rw [← hm2, ← hm1] at hidx' ⊢
          eval_expr <;> omega)
        (by eval_expr)
        ⟨⟨fun i hi => ?_, by simpa using h11, fun a ha => ?_, fun y hy => ?_⟩, by simpa using h11⟩
        (by simp [Expr.size])
      · simp only [Function.update_of_ne (show i ≠ 11 by omega)]; exact hR i hi
      · dsimp only; rw [Function.update_of_ne (by unfold repIdx; omega)]; exact hfr a ha
      · dsimp only
        by_cases hyz : y = repIdx mem repPtr vIdxPtr k
        · rw [hyz, Function.update_self, if_pos (Or.inr ⟨k, by omega, rfl⟩)]
        · rw [Function.update_of_ne (by omega), hc y hy]
          have : ¬ repIdx mem repPtr vIdxPtr k = y := fun h => hyz h.symm
          simp only [PA, PB, exists_lt_succ_iff', this, or_false]
  -- 3. the ends of the high edges
  let Inv3 : ℕ → State → Prop := fun k st =>
    (∀ i < 10, st.regs i = args.getD i 0) ∧ st.regs 12 = k ∧
    (∀ a, a < outPtr ∨ outPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ y < n, st.mem (outPtr + y) = if PC k y then 1 else 0
  have hloop3 : ∀ st₀ : State, Inv2 cnt st₀ → Triple w p (fun st => st = st₀)
      (forRange 12 (.const 0) (.reg 2)
        (.cond (.load (.bin .add (.reg 6) (.reg 12)))
          (.store (.bin .add (.reg 9) (.load (.bin .add (.reg 7) (.reg 12)))) (.const 1) ;;
           .store (.bin .add (.reg 9) (.load (.bin .add (.reg 8) (.reg 12)))) (.const 1))
          .nop))
      (normalPost (Inv3 m0))
      (fun _ => (m0 - 0) * (50 + (Expr.reg 2).size + 8) +
        ((Expr.const 0).size + (Expr.reg 2).size + 5)) := by
    intro st₀ hI2
    refine Triple.forRange_const 50 0 m0 (by omega) hw1 (fun _ => hmw) ?_ ?_ ?_ ?_
    · rintro st rfl
      obtain ⟨hR, -, hfr, hc⟩ := hI2
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hfr, fun y hy => ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 12 by omega)]
        exact hR i hi
      · rw [hc y hy]
        simp only [PC, Nat.not_lt_zero, false_and, exists_false, or_false]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r2 : st.regs 2 = m0 := hI.1 2 (by omega)
      eval_expr
    · intro k _ hk st ω' hI
      obtain ⟨hR, h12, hfr, hc⟩ := hI
      have r6 : st.regs 6 = highPtr := hR 6 (by omega)
      have r7 : st.regs 7 = euPtr := hR 7 (by omega)
      have r8 : st.regs 8 = evPtr := hR 8 (by omega)
      have r9 : st.regs 9 = outPtr := hR 9 (by omega)
      obtain ⟨hh1, heun, hevn⟩ := hedge k hk
      have hmh : st.mem (highPtr + k) = mem (highPtr + k) := hfr _ (Or.inl (by omega))
      have hmu : st.mem (euPtr + k) = mem (euPtr + k) := hfr _ (Or.inl (by omega))
      have hmv : st.mem (evPtr + k) = mem (evPtr + k) := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      refine WordRAM.runs_cond_le (v := mem (highPtr + k)) (by rw [← hmh]; eval_expr) ?_ ?_
      · intro hne
        have hk1 : mem (highPtr + k) = 1 := by omega
        set u := mem (euPtr + k) with hu
        set v := mem (evPtr + k) with hv
        refine runs_seq_store_le (x := outPtr + u) (v := 1) (by rw [← hmu]; eval_expr)
          (by eval_expr) ?_
        refine runs_store_le (x := outPtr + v) (v := 1)
          (by
            have : Function.update st.mem (outPtr + u) 1 (evPtr + k) = v := by
              rw [Function.update_of_ne (by omega), hmv]
            eval_expr)
          (by eval_expr)
          ⟨⟨fun i hi => ?_, by simpa using h12, fun a ha => ?_, fun y hy => ?_⟩,
            by simpa using h12⟩ (by simp [Expr.size])
        · simp only [Function.update_of_ne (show i ≠ 12 by omega)]; exact hR i hi
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a ha
        · dsimp only
          by_cases hyv : y = v
          · rw [hyv, Function.update_self, if_pos (Or.inr ⟨k, by omega, hk1, Or.inr rfl⟩)]
          · rw [Function.update_of_ne (by omega)]
            by_cases hyu : y = u
            · rw [hyu, Function.update_self, if_pos (Or.inr ⟨k, by omega, hk1, Or.inl rfl⟩)]
            · rw [Function.update_of_ne (by omega), hc y hy]
              have : ¬ (mem (highPtr + k) = 1 ∧ (u = y ∨ v = y)) := by
                rintro ⟨-, h | h⟩
                · exact hyu h.symm
                · exact hyv h.symm
              have hQ : ¬ (mem (highPtr + k) = 1 ∧
                  (mem (euPtr + k) = y ∨ mem (evPtr + k) = y)) := this
              simp only [PC, exists_lt_succ_iff', hQ, or_false]
      · intro hz
        refine runs_nop_le ⟨⟨fun i hi => ?_, by simpa using h12, fun a ha => hfr a ha,
          fun y hy => ?_⟩, by simpa using h12⟩ (by simp [Expr.size])
        · simp only [Function.update_of_ne (show i ≠ 12 by omega)]; exact hR i hi
        · rw [hc y hy]
          have : ¬ (mem (highPtr + k) = 1 ∧
              (mem (euPtr + k) = y ∨ mem (evPtr + k) = y)) := by
            rintro ⟨h, -⟩
            omega
          simp only [PC, exists_lt_succ_iff', this, or_false]
  refine runs_start_le ?_
  unfold flagMergeProc
  refine runs_seq_triple_le hloop1 rfl ?_
  rintro st₁ hI1
  refine runs_seq_triple_le (hloop2 st₁ hI1) rfl ?_
  rintro st₂ hI2
  refine runs_seq_triple_le (hloop3 st₂ hI2) rfl ?_
  rintro st ⟨-, -, hfr, hc⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨n, cnt, m0, bndPtr, repPtr, vIdxPtr, highPtr, euPtr, evPtr, outPtr, rfl, rfl, hfr,
      fun y hy => ?_⟩ ?_
  · rw [hc y hy]
    refine if_congr ?_ rfl rfl
    dsimp only [PC, PA, PB, MergedFlag]
    exact or_assoc
  · simp only [flagMergeContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
