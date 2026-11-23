module

public import MinCostFlow.LSF.Program.THPlaceMath
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The block starts and the chain array

`thOffProc` walks `t = 0, …, n - 1` with a running sum: it stores `off t` and then adds
`cnt t` when `t` is its own top. So `off t = offSum top cnt t` (`THPlaceMath.lean`).

`thPlaceProc` walks `x = 0, …, n - 1` and writes `x` at the slot
`off (top x) + (dep x - dep (top x))`. When the slots are distinct (`thSlot_inj`), every `x` is
found at its slot at the end. Both passes cost `O(n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step of the offset pass (register `4` is `t`, register `5` the running sum). -/
def thOffBody : Stmt :=
  .store (.bin .add (.reg 3) (.reg 4)) (.reg 5) ;;
  .assign 5 (.bin .add (.reg 5) (.bin .mul (.bin .eq (.load (.bin .add (.reg 1) (.reg 4))) (.reg 4))
    (.load (.bin .add (.reg 2) (.reg 4)))))

/-- Args: `[n, topPtr, cntPtr, offPtr]`. -/
def thOffProc : Stmt :=
  .assign 5 (.const 0) ;;
  forRange 4 (.const 0) (.reg 0) thOffBody ;;
  .ret (.const 0)

lemma thOffProc_noRand : thOffProc.NoRand := by
  simp [thOffProc, thOffBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `thOffProc`. The running sums are at most `n`. -/
def thOffContract (w : ℕ) : Contract where
  pre args mem := ∃ (n topPtr cntPtr offPtr : ℕ),
    args = [n, topPtr, cntPtr, offPtr] ∧ 0 < n ∧
    topPtr + n ≤ offPtr ∧ cntPtr + n ≤ offPtr ∧ offPtr + n < 2 ^ w ∧
    ∀ t ≤ n, offSum (fun x => mem (topPtr + x)) (fun x => mem (cntPtr + x)) t ≤ n
  post args mem ret mem' := ∃ (n topPtr cntPtr offPtr : ℕ),
    args = [n, topPtr, cntPtr, offPtr] ∧ ret = 0 ∧
    (∀ a, a < offPtr ∨ offPtr + n ≤ a → mem' a = mem a) ∧
    ∀ t < n, mem' (offPtr + t) = offSum (fun x => mem (topPtr + x)) (fun x => mem (cntPtr + x)) t
  cost args _ := 60 * args.getD 0 0 + 30

theorem thOff_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some thOffProc) :
    MeetsContract w p b (thOffContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, topPtr, cntPtr, offPtr, rfl, hn, hta, hca, hoa, hle⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, topPtr, cntPtr, offPtr] with hargs
  set top : ℕ → ℕ := fun x => mem (topPtr + x) with htop
  set cnt : ℕ → ℕ := fun x => mem (cntPtr + x) with hcnt
  have hnw : n < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 4, st.regs i = args.getD i 0) ∧ st.regs 4 = j ∧ st.regs 5 = offSum top cnt j ∧
    (∀ a, a < offPtr ∨ offPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ t < j, st.mem (offPtr + t) = offSum top cnt t
  have hR0 : ∀ i < 4, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hloop : Triple w p (fun st => st = {startState args mem pos with
        regs := Function.update (startState args mem pos).regs 5 0})
      (forRange 4 (.const 0) (.reg 0) thOffBody) (normalPost (Inv n))
      (fun _ => (n - 0) * (40 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 40 0 n (by omega) (by omega) (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, by simp [offSum], fun a _ => rfl,
        fun t ht => absurd ht (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 4 by omega), Function.update_of_ne (show i ≠ 5 by omega)]
      exact hR0 i hi
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j _ hjn st ω' hI
      obtain ⟨hR, h4, h5, hfr, hdone⟩ := hI
      have r1 : st.regs 1 = topPtr := hR 1 (by omega)
      have r2 : st.regs 2 = cntPtr := hR 2 (by omega)
      have r3 : st.regs 3 = offPtr := hR 3 (by omega)
      have hmt : st.mem (topPtr + j) = top j := hfr _ (Or.inl (by omega))
      have hmc : st.mem (cntPtr + j) = cnt j := hfr _ (Or.inl (by omega))
      have hs1 := hle (j + 1) (by omega)
      rw [offSum_succ] at hs1
      set cc := (if top j = j then 1 else 0) with hcc
      have hsel : offSum top cnt j + cc * cnt j = offSum top cnt (j + 1) := by
        rw [offSum_succ, hcc]; split_ifs <;> simp
      have hv : offSum top cnt j + cc * cnt j ≤ n := by rw [hsel, offSum_succ]; exact hs1
      refine runs_start_le ?_
      unfold thOffBody
      refine runs_seq_store_le (x := offPtr + j) (v := offSum top cnt j) (by eval_expr)
        (by have : offSum top cnt j < 2 ^ w := by omega
            eval_expr) ?_
      have hm1t : Function.update st.mem (offPtr + j) (offSum top cnt j) (topPtr + j) = top j := by
        rw [Function.update_of_ne (by omega), hmt]
      have hm1c : Function.update st.mem (offPtr + j) (offSum top cnt j) (cntPtr + j) = cnt j := by
        rw [Function.update_of_ne (by omega), hmc]
      refine runs_assign_le (v := offSum top cnt (j + 1)) (by
        rw [← hsel, hcc, ← hm1t, ← hm1c]
        have : (if Function.update st.mem (offPtr + j) (offSum top cnt j) (topPtr + j) = j then 1
          else 0) * Function.update st.mem (offPtr + j) (offSum top cnt j) (cntPtr + j) ≤ n := by
          rw [hm1t, hm1c]; rw [← hcc]; omega
        eval_expr) ⟨⟨fun i hi => ?_, by simpa using h4, by simp, ?_, ?_⟩, by simpa using h4⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 4 by omega),
          Function.update_of_ne (show i ≠ 5 by omega)]; exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]; exact hfr a ha
      · intro t ht
        dsimp only
        by_cases htj : t = j
        · rw [htj, Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hdone t (by omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold thOffProc
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, topPtr, cntPtr, offPtr, rfl, rfl, hfr, hdone⟩ ?_
  simp only [thOffContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg]
  omega

/-- One step of the placing pass (register `5` is `x`, register `10` is `top x`). -/
def thPlaceBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 5))) ;;
  .store (.bin .add (.reg 4) (.bin .add (.load (.bin .add (.reg 3) (.reg 10)))
    (.bin .sub (.load (.bin .add (.reg 2) (.reg 5))) (.load (.bin .add (.reg 2) (.reg 10))))))
    (.reg 5)

/-- Args: `[n, topPtr, depPtr, offPtr, arrPtr]`. -/
def thPlaceProc : Stmt :=
  forRange 5 (.const 0) (.reg 0) thPlaceBody ;;
  .ret (.const 0)

lemma thPlaceProc_noRand : thPlaceProc.NoRand := by
  simp [thPlaceProc, thPlaceBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `thPlaceProc`. The slots are below `n` and distinct. -/
def thPlaceContract (w : ℕ) : Contract where
  pre args mem := ∃ (n topPtr depPtr offPtr arrPtr : ℕ),
    args = [n, topPtr, depPtr, offPtr, arrPtr] ∧ 0 < n ∧
    topPtr + n ≤ arrPtr ∧ depPtr + n ≤ arrPtr ∧ offPtr + n ≤ arrPtr ∧ arrPtr + n < 2 ^ w ∧
    (∀ x < n, mem (topPtr + x) < n) ∧ (∀ x < n, mem (depPtr + x) < n) ∧
    (∀ x < n, thSlot (fun t => mem (offPtr + t)) (fun t => mem (topPtr + t))
      (fun t => mem (depPtr + t)) x < n) ∧
    (∀ x < n, ∀ y < n, thSlot (fun t => mem (offPtr + t)) (fun t => mem (topPtr + t))
      (fun t => mem (depPtr + t)) x = thSlot (fun t => mem (offPtr + t))
        (fun t => mem (topPtr + t)) (fun t => mem (depPtr + t)) y → x = y)
  post args mem ret mem' := ∃ (n topPtr depPtr offPtr arrPtr : ℕ),
    args = [n, topPtr, depPtr, offPtr, arrPtr] ∧ ret = 0 ∧
    (∀ a, a < arrPtr ∨ arrPtr + n ≤ a → mem' a = mem a) ∧
    ∀ x < n, mem' (arrPtr + thSlot (fun t => mem (offPtr + t)) (fun t => mem (topPtr + t))
      (fun t => mem (depPtr + t)) x) = x
  cost args _ := 60 * args.getD 0 0 + 30

theorem thPlace_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some thPlaceProc) :
    MeetsContract w p b (thPlaceContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, topPtr, depPtr, offPtr, arrPtr, rfl, hn, hta, hda, hoa, haa, htn, hdn, hsl, hinj⟩ := hpre
  set args := [n, topPtr, depPtr, offPtr, arrPtr] with hargs
  set top : ℕ → ℕ := fun x => mem (topPtr + x) with htop
  set dep : ℕ → ℕ := fun x => mem (depPtr + x) with hdep
  set off : ℕ → ℕ := fun x => mem (offPtr + x) with hoff
  have hnw : n < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 5, st.regs i = args.getD i 0) ∧ st.regs 5 = j ∧
    (∀ a, a < arrPtr ∨ arrPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ x < j, st.mem (arrPtr + thSlot off top dep x) = x
  have hR0 : ∀ i < 5, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 5 (.const 0) (.reg 0) thPlaceBody) (normalPost (Inv n))
      (fun _ => (n - 0) * (40 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 40 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl, fun x hx => absurd hx (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 5 by omega)]; exact hR0 i hi
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j _ hjn st ω' hI
      obtain ⟨hR, h5, hfr, hdone⟩ := hI
      have r1 : st.regs 1 = topPtr := hR 1 (by omega)
      have r2 : st.regs 2 = depPtr := hR 2 (by omega)
      have r3 : st.regs 3 = offPtr := hR 3 (by omega)
      have r4 : st.regs 4 = arrPtr := hR 4 (by omega)
      have hjt : top j < n := htn j hjn
      have hmt : st.mem (topPtr + j) = top j := hfr _ (Or.inl (by omega))
      have hmo : st.mem (offPtr + top j) = off (top j) := by
        have : offPtr + top j < arrPtr := by omega
        exact hfr _ (Or.inl this)
      have hmd : st.mem (depPtr + j) = dep j := hfr _ (Or.inl (by omega))
      have hmdt : st.mem (depPtr + top j) = dep (top j) := by
        have : depPtr + top j < arrPtr := by omega
        exact hfr _ (Or.inl this)
      have hs := hsl j hjn
      have hslot : thSlot off top dep j = off (top j) + (dep j - dep (top j)) := rfl
      refine runs_start_le ?_
      unfold thPlaceBody
      refine runs_seq_assign_le (v := top j) (by rw [← hmt]; eval_expr) ?_
      refine runs_store_le (x := arrPtr + thSlot off top dep j) (v := j) (by
        rw [hslot, ← hmo, ← hmd, ← hmdt]
        have : st.mem (offPtr + top j) + (st.mem (depPtr + j) - st.mem (depPtr + top j)) < n := by
          rw [hmo, hmd, hmdt]; exact hs
        have : st.mem (depPtr + j) < n := by rw [hmd]; exact hdn j hjn
        have : st.mem (depPtr + top j) < n := by rw [hmdt]; exact hdn _ hjt
        have : st.mem (offPtr + top j) < n := by
          rw [hmo]; unfold thSlot at hs; omega
        eval_expr) (by eval_expr) ⟨⟨fun i hi => ?_, by simpa using h5, ?_, ?_⟩, by simpa using h5⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 5 by omega)]; exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]; exact hfr a ha
      · intro x hx
        dsimp only
        by_cases hxj : x = j
        · rw [hxj, Function.update_self]
        · have hne : thSlot off top dep x ≠ thSlot off top dep j :=
            fun h => hxj (hinj x (by omega) j hjn h)
          rw [Function.update_of_ne (by omega)]; exact hdone x (by omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold thPlaceProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, topPtr, depPtr, offPtr, arrPtr, rfl, rfl, hfr,
    hdone⟩ ?_
  simp only [thPlaceContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg]
  omega

end

end MinCostFlow.LSF.Program
