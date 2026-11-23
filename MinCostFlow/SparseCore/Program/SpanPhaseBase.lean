module

public import MinCostFlow.SparseCore.Program.SpanBridge
public import WordRAM.Logic

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import WordRAM.Tactic

/-!
# Exact Bucket-Spanner Parameter Procedures (`SpanPhaseBase`)

Deterministic Word-RAM procedures computing the exact integer parameters of `bucketDSParams` and
`DSInitPre` without floating-point arithmetic or word overflow:

* `powGeStmt` (`[base, L, target]`): returns `1` if `target ≤ base ^ L` and `0` otherwise, using
  the overflow-free comparison `(target - 1) / base < acc` (`le_mul_iff_div_lt`), in at most
  `45 * L + 30` steps.
* `phaseBaseStmt bPowGe` (`[nCap, L]`): returns `phaseBase nCap L` exactly via binary search over
  `[2, max 2 nCap]` calling `powGeStmt`, in at most
  `(45 * L + 80) * (Nat.log 2 (nCap + 2) + 2) + 80` steps.
* `bundleSplitBudgetStmt` (`[k, M]`): returns `bundleSplitBudget k M = 2 * ((56 * M + k - 1) / k)`
  in at most `20` steps.
* `spanParamProcs`: relocatable 3-procedure bundle `[powGeStmt, phaseBaseStmt b,
  bundleSplitBudgetStmt]`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.SparseCore

/-! ## Procedure definitions and contracts -/

@[expose] public section

def spanParamIdxPowGe : ℕ := 0
def spanParamIdxPhaseBase : ℕ := 1
def spanParamIdxSplitBudget : ℕ := 2

/-- `args = [base, L, target]`: returns `1` iff `target ≤ base ^ L`, for `1 ≤ base`, `1 ≤ L`,
`1 ≤ target`, `target < 2 ^ w`. Never overflows `2 ^ w`. -/
def powGeStmt : Stmt :=
  .assign 3 (.bin .div (.bin .sub (.reg 2) (.const 1)) (.reg 0)) ;;
  .assign 4 (.const 1) ;;
  .assign 5 (.const 0) ;;
  forRange 6 (.const 0) (.reg 1)
    (.cond (.reg 5)
      .nop
      (.cond (.bin .lt (.reg 3) (.reg 4))
        (.assign 5 (.const 1))
        (.assign 4 (.bin .mul (.reg 4) (.reg 0))))) ;;
  .ret (.reg 5)

/-- `args = [nCap, L]`: returns `phaseBase nCap L` exactly via binary search over `[2, nCap]`
using `powGeStmt` at index `bPowGe`. -/
def phaseBaseStmt (bPowGe : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 0) (.const 2))
    (.ret (.const 2))
    (.call 2 bPowGe [.const 2, .reg 1, .reg 0] ;;
     .cond (.reg 2)
       (.ret (.const 2))
       (.assign 3 (.const 2) ;;
        .assign 4 (.reg 0) ;;
        .loop (.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4))
          (.assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))) ;;
           .call 6 bPowGe [.reg 5, .reg 1, .reg 0] ;;
           .cond (.reg 6)
             (.assign 4 (.reg 5))
             (.assign 3 (.reg 5))) ;;
        .ret (.reg 4)))

/-- `args = [k, M]`: returns `bundleSplitBudget k M = 2 * ((56 * M + k - 1) / k)` for `1 ≤ k`. -/
def bundleSplitBudgetStmt : Stmt :=
  .ret (.bin .mul (.const 2)
    (.bin .div (.bin .sub (.bin .add (.bin .mul (.const 56) (.reg 1)) (.reg 0)) (.const 1))
      (.reg 0)))

/-- Relocatable parameter procedure bundle (`3` deterministic procedures). -/
def spanParamProcs (b : ℕ) : List Stmt :=
  [powGeStmt, phaseBaseStmt (b + spanParamIdxPowGe), bundleSplitBudgetStmt]

lemma spanParamProcs_length (b : ℕ) : (spanParamProcs b).length = 3 := rfl

lemma spanParamProcs_noRand (b : ℕ) : ∀ s ∈ spanParamProcs b, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Cost bound of `powGeStmt`: `45 * L + 30`. -/
def powGeCost (L : ℕ) : ℕ := 45 * L + 30

/-- Cost bound of `phaseBaseStmt`: `(45 * L + 80) * (Nat.log 2 (nCap + 2) + 2) + 80`. -/
def phaseBaseCost (nCap L : ℕ) : ℕ := (45 * L + 80) * (Nat.log 2 (nCap + 2) + 2) + 80

/-- Contract of `powGeStmt` (`[base, L, target]`). -/
def powGeContract (w base L target : ℕ) : Contract where
  pre args _ :=
    args = [base, L, target] ∧ 1 ≤ base ∧ 1 ≤ L ∧ 1 ≤ target ∧ 16 ≤ 2 ^ w ∧ target < 2 ^ w
  post _ mem ret mem' :=
    mem' = mem ∧ ret = if target ≤ base ^ L then 1 else 0
  cost _ _ := powGeCost L

/-- Contract of `phaseBaseStmt` (`[nCap, L]`). -/
def phaseBaseContract (w nCap L : ℕ) : Contract where
  pre args _ :=
    args = [nCap, L] ∧ 1 ≤ L ∧ 16 ≤ 2 ^ w ∧ nCap + 2 < 2 ^ w ∧ L < 2 ^ w
  post _ mem ret mem' :=
    mem' = mem ∧ ret = phaseBase nCap L
  cost _ _ := phaseBaseCost nCap L

/-- Contract of `bundleSplitBudgetStmt` (`[k, M]`). -/
def bundleSplitBudgetContract (w k M : ℕ) : Contract where
  pre args _ :=
    args = [k, M] ∧ 1 ≤ k ∧ 64 ≤ 2 ^ w ∧ 56 * M + k < 2 ^ w ∧ 2 * (56 * M + 1) < 2 ^ w
  post _ mem ret mem' :=
    mem' = mem ∧ ret = bundleSplitBudget k M
  cost _ _ := 20

end

/-! ## Private invariants and arithmetic helpers -/

private lemma runs_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h : ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, hq, by omega⟩

private lemma runs_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h : ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩, hq, by omega⟩

private def PowGeInv (base L target : ℕ) (mem0 : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.mem = mem0 ∧
  st.regs 0 = base ∧ st.regs 1 = L ∧ st.regs 2 = target ∧
  st.regs 3 = (target - 1) / base ∧ st.regs 6 = i ∧
  (if st.regs 5 = 0 then
    st.regs 4 = base ^ i ∧ (i = 0 ∨ base ^ i < target)
   else
    st.regs 5 = 1 ∧ target ≤ base ^ i)

private def PhaseBSInv (nCap L : ℕ) (mem0 : ℕ → ℕ) (st : State) : Prop :=
  st.mem = mem0 ∧
  st.regs 0 = nCap ∧ st.regs 1 = L ∧
  2 ≤ st.regs 3 ∧ st.regs 3 < st.regs 4 ∧ st.regs 4 ≤ nCap ∧
  (st.regs 3) ^ L < nCap ∧ nCap ≤ (st.regs 4) ^ L

private lemma clog2_halve_lt {d : ℕ} (hd : 2 ≤ d) {d' : ℕ} (hle : d' ≤ (d + 1) / 2) :
    Nat.clog 2 d' < Nat.clog 2 d := by
  have h1 : Nat.clog 2 d = Nat.clog 2 ((d + 1) / 2) + 1 := by
    have := Nat.clog_of_one_lt (b := 2) (by decide) (by omega : 1 < d)
    simpa [show d + 2 - 1 = d + 1 by omega] using this
  have h2 : Nat.clog 2 d' ≤ Nat.clog 2 ((d + 1) / 2) := Nat.clog_mono_right 2 hle
  omega

private lemma clog2_le_log2_add_one (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 (n + 2) + 1 := by
  have h1 : Nat.clog 2 n ≤ Nat.clog 2 (n + 2) := Nat.clog_mono_right 2 (by omega)
  have h2 : Nat.clog 2 (n + 2) ≤ Nat.log 2 (n + 2) + 1 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) (n + 2)))
  omega

private lemma phaseBase_cost_arith (L nCap m : ℕ) (hm : m ≤ Nat.log 2 (nCap + 2) + 1) :
    (45 * L + 30) + (45 * L + 80) * m + 75 ≤
      (45 * L + 80) * (Nat.log 2 (nCap + 2) + 2) + 80 := by
  have h1 : (45 * L + 80) * m ≤ (45 * L + 80) * (Nat.log 2 (nCap + 2) + 1) :=
    Nat.mul_le_mul_left _ hm
  have h2 : (45 * L + 80) * (Nat.log 2 (nCap + 2) + 2) =
      (45 * L + 80) * (Nat.log 2 (nCap + 2) + 1) + (45 * L + 80) := by
    rw [show Nat.log 2 (nCap + 2) + 2 = (Nat.log 2 (nCap + 2) + 1) + 1 by omega, Nat.mul_succ]
  omega

/-! ## Contract verification -/

public section

/-- `powGeStmt` meets `powGeContract`. -/
theorem powGe_meetsContract {w base L target : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (spanParamProcs b)) :
    MeetsContract w p (b + spanParamIdxPowGe) (powGeContract w base L target) := by
  refine meetsContract_of_runs
    (hp.get (i := spanParamIdxPowGe) (by simp [spanParamProcs, spanParamIdxPowGe])) ?_
  rintro args mem pos ω hW ⟨rfl, hb1, hL1, ht1, hw16, htW⟩
  simp only [spanParamProcs, spanParamIdxPowGe, List.getElem_cons_zero]
  have hbW : base < 2 ^ w := hW base (by simp)
  have hLW : L < 2 ^ w := hW L (by simp)
  have hqW : (target - 1) / base < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  dsimp only [powGeStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := (target - 1) / base)
    (Expr.eval_div
      (Expr.eval_sub (Expr.eval_reg_of_eq (v := target) (by simp [startState]))
        (Expr.eval_const (by omega)) htW)
      (Expr.eval_reg_of_eq (v := base) (by simp [startState])) (by omega)) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hloop : Triple w p
      (fun st => PowGeInv base L target mem 0 { st with regs := Function.update st.regs 6 0 })
      (forRange 6 (.const 0) (.reg 1)
        (.cond (.reg 5) .nop
          (.cond (.bin .lt (.reg 3) (.reg 4)) (.assign 5 (.const 1))
            (.assign 4 (.bin .mul (.reg 4) (.reg 0))))))
      (normalPost (PowGeInv base L target mem L))
      (fun _ => L * (20 + (Expr.reg 1).size + 8) + ((Expr.const 0).size + (Expr.reg 1).size + 5)) := by
    refine Triple.forRange_const (Inv := PowGeInv base L target mem) 20 0 L (Nat.zero_le L)
      (by omega) (fun _ => by omega)
      (fun st hst => ⟨Expr.eval_const (by omega), hst⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.1)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
      (fun i _ hiL => ?_)
    intro st ω' hI
    obtain ⟨hm, hr0, hr1, hr2, hr3, hr6, h5⟩ := hI
    refine runs_start_le ?_
    by_cases hf : st.regs 5 = 0
    · rw [ite_eq_left hf] at h5
      obtain ⟨hr4, hi0_or_lt⟩ := h5
      refine runs_cond_false_le (Expr.eval_reg_of_eq hf) ?_
      by_cases hlt : (target - 1) / base < base ^ i
      · have hcond : ((Expr.bin .lt (.reg 3) (.reg 4)).eval w st) = some 1 :=
          Expr.eval_lt_true (Expr.eval_reg_of_eq hr3) (Expr.eval_reg_of_eq hr4) hlt (by omega)
        refine runs_cond_true_le (v := 1) hcond (by decide) ?_
        refine runs_assign_le (v := 1) (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
        have hge : target ≤ base ^ (i + 1) := by
          rw [pow_succ]; exact (le_mul_iff_div_lt ht1 hb1).mpr hlt
        refine ⟨⟨hm, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp, ?_⟩,
          by simp [hr6]⟩
        simp [hge]
      · have hcond : ((Expr.bin .lt (.reg 3) (.reg 4)).eval w st) = some 0 :=
          Expr.eval_lt_false (Expr.eval_reg_of_eq hr3) (Expr.eval_reg_of_eq hr4) (by omega) (by omega)
        refine runs_cond_false_le hcond ?_
        have hlt_next : base ^ (i + 1) < target := by
          rw [pow_succ]
          by_contra hge
          exact hlt ((le_mul_iff_div_lt ht1 hb1).mp (by omega))
        have hmulW : base ^ i * base < 2 ^ w := by
          rw [← pow_succ]; exact lt_trans hlt_next htW
        have hmulEval : (Expr.bin .mul (.reg 4) (.reg 0)).eval w st = some (base ^ (i + 1)) := by
          rw [pow_succ]
          exact Expr.eval_mul (Expr.eval_reg_of_eq hr4) (Expr.eval_reg_of_eq hr0) hmulW
        refine runs_assign_le (v := base ^ (i + 1)) hmulEval ?_ (by simp [Expr.size])
        refine ⟨⟨hm, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp, ?_⟩,
          by simp [hr6]⟩
        simp [hf, hlt_next]
    · rw [ite_eq_right hf] at h5
      obtain ⟨hr5, hge⟩ := h5
      refine runs_cond_true_le (v := 1) (Expr.eval_reg_of_eq hr5) (by decide) ?_
      refine runs_nop_le ?_ (by simp [Expr.size])
      have hge' : target ≤ base ^ (i + 1) := by
        rw [pow_succ]
        exact le_trans hge (Nat.le_mul_of_pos_right _ (by omega))
      exact ⟨⟨hm, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp,
        by simp [hr5, hge']⟩, hr6⟩
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨rfl, by simp [startState], by simp [startState], by simp [startState], by simp,
      by simp, ?_⟩
    simp
  · intro st₁ ⟨hm, _, _, _, _, _, h5⟩
    have hval : st₁.regs 5 = if target ≤ base ^ L then 1 else 0 := by
      by_cases hf : st₁.regs 5 = 0
      · rw [ite_eq_left hf] at h5
        have hlt : base ^ L < target := by
          rcases h5.2 with h0 | hlt
          · omega
          · exact hlt
        simp [hf, show ¬ target ≤ base ^ L by omega]
      · rw [ite_eq_right hf] at h5
        simp [h5.1, h5.2]
    refine runs_ret_le (v := if target ≤ base ^ L then 1 else 0)
      (Expr.eval_reg_of_eq hval) ⟨hm, rfl⟩ ?_
    simp only [Expr.size, powGeContract, powGeCost]
    omega

/-- `phaseBaseStmt` meets `phaseBaseContract`. -/
theorem phaseBase_meetsContract {w nCap L : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (spanParamProcs b)) :
    MeetsContract w p (b + spanParamIdxPhaseBase) (phaseBaseContract w nCap L) := by
  refine meetsContract_of_runs
    (hp.get (i := spanParamIdxPhaseBase) (by simp [spanParamProcs, spanParamIdxPhaseBase])) ?_
  rintro args mem pos ω _ ⟨rfl, hL1, hw16, hnW, hLW⟩
  simp only [spanParamProcs, spanParamIdxPhaseBase, List.getElem_cons_succ, List.getElem_cons_zero]
  have hnW0 : nCap < 2 ^ w := by omega
  have h2W : 2 < 2 ^ w := by omega
  dsimp only [phaseBaseStmt]
  refine runs_start_le ?_
  by_cases hn2 : nCap < 2
  · have hcond : ((Expr.bin .lt (.reg 0) (.const 2)).eval w (startState [nCap, L] mem pos)) = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq (v := nCap) (by simp [startState])) (Expr.eval_const h2W) hn2 (by omega)
    refine runs_cond_true_le (v := 1) hcond (by decide) ?_
    refine runs_ret_le (v := 2) (Expr.eval_const h2W)
      ⟨rfl, (phaseBase_of_le_one (by omega)).symm⟩ ?_
    simp only [Expr.size, phaseBaseContract, phaseBaseCost]
    omega
  · have hcond : ((Expr.bin .lt (.reg 0) (.const 2)).eval w (startState [nCap, L] mem pos)) = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq (v := nCap) (by simp [startState])) (Expr.eval_const h2W)
        (by omega) (by omega)
    refine runs_cond_false_le hcond ?_
    have hn1 : 1 ≤ nCap := by omega
    refine runs_seq_call_le (vs := [2, L, nCap]) (powGe_meetsContract (w := w) hp)
      (evalArgs_cons (Expr.eval_const h2W) <|
        evalArgs_cons (Expr.eval_reg_of_eq (v := L) (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (v := nCap) (by simp [startState])) <| evalArgs_nil _ _)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨rfl, by omega, hL1, hn1, hw16, hnW0⟩ ?_
    rintro ret1 mem1 pos1 ⟨hm1, hret1⟩
    subst mem1
    by_cases h2pow : nCap ≤ 2 ^ L
    · have hr2 : ret1 = 1 := by simp [hret1, h2pow]
      refine runs_cond_true_le (v := 1) (Expr.eval_reg_of_eq (by simp [hr2])) (by decide) ?_
      refine runs_ret_le (v := 2) (Expr.eval_const h2W)
        ⟨rfl, (phaseBase_eq_two_of_le_pow hL1 h2pow).symm⟩ ?_
      simp only [Expr.size, argsSize_cons, argsSize_nil, powGeContract, powGeCost,
        phaseBaseContract, phaseBaseCost]
      have := phaseBase_cost_arith L nCap 0 (Nat.zero_le _)
      omega
    · have hr2 : ret1 = 0 := by simp [hret1, h2pow]
      have h2lt : 2 < nCap := by
        have h2le : 2 ≤ 2 ^ L := by
          calc 2 = 2 ^ 1 := by decide
            _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL1
        omega
      refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [hr2])) ?_
      refine runs_seq_assign_le (v := 2) (Expr.eval_const h2W) ?_
      refine runs_seq_assign_le (v := nCap) (Expr.eval_reg_of_eq (by simp [startState])) ?_
      have hloop : Triple w p (PhaseBSInv nCap L mem)
          (.loop (.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4))
            (.assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))) ;;
             .call 6 (b + spanParamIdxPowGe) [.reg 5, .reg 1, .reg 0] ;;
             .cond (.reg 6) (.assign 4 (.reg 5)) (.assign 3 (.reg 5))))
          (normalPost fun st => PhaseBSInv nCap L mem st ∧ st.regs 4 = st.regs 3 + 1)
          (fun st => ((Expr.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4)).size +
              (45 * L + 65) + 1) * Nat.clog 2 (st.regs 4 - st.regs 3) +
            (Expr.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4)).size + 1) := by
        refine Triple.loop_const_normal
          (m := fun st => Nat.clog 2 (st.regs 4 - st.regs 3))
          (condVal := fun st => if st.regs 3 + 1 < st.regs 4 then 1 else 0)
          (45 * L + 65)
          (fun st hI => by
            obtain ⟨_, _, _, _, hlt, hle, _, _⟩ := hI
            by_cases hc : st.regs 3 + 1 < st.regs 4
            · rw [ite_eq_left hc]
              exact Expr.eval_lt_true
                (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
                (Expr.eval_reg_of_eq rfl) hc (by omega)
            · rw [ite_eq_right hc]
              exact Expr.eval_lt_false
                (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
                (Expr.eval_reg_of_eq rfl) (by omega) (by omega))
          (fun st hI h0 => by
            have hnot : ¬ st.regs 3 + 1 < st.regs 4 := by
              intro hc; rw [ite_eq_left hc] at h0; exact Nat.one_ne_zero h0
            have hlt := hI.2.2.2.2.1
            exact ⟨hI, by omega⟩)
          (fun st hI hne => by
            have hc : st.regs 3 + 1 < st.regs 4 := by
              by_contra hnot; rw [ite_eq_right hnot] at hne; exact hne rfl
            intro s ω' hs
            subst s
            obtain ⟨hm, hr0, hr1, hlo2, hlt, hhi_le, hlo_pow, hhi_pow⟩ := hI
            set lo := st.regs 3
            set hi := st.regs 4
            set mid := lo + (hi - lo) / 2
            have hmid_gt : lo < mid := by dsimp only [mid]; omega
            have hmid_lt : mid < hi := by dsimp only [mid]; omega
            have hmidW : mid < 2 ^ w := by omega
            refine runs_start_le ?_
            refine runs_seq_assign_le (v := mid)
              (Expr.eval_add (Expr.eval_reg_of_eq (v := lo) rfl)
                (Expr.eval_div
                  (Expr.eval_sub (Expr.eval_reg_of_eq (v := hi) rfl)
                    (Expr.eval_reg_of_eq (v := lo) rfl) (by omega))
                  (Expr.eval_const h2W) (by omega))
                hmidW) ?_
            refine runs_seq_call_le (vs := [mid, L, nCap]) (powGe_meetsContract (w := w) hp)
              (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
                evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr1])) <|
                evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr0])) <| evalArgs_nil _ _)
              (fun v hv => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                rcases hv with rfl | rfl | rfl <;> omega)
              ⟨rfl, by omega, hL1, hn1, hw16, hnW0⟩ ?_
            rintro ret2 mem2 pos2 ⟨hm2, hret2⟩
            have hm2' : mem2 = mem := hm2.trans hm
            by_cases hmp : nCap ≤ mid ^ L
            · have hr6 : ret2 = 1 := by simp [hret2, hmp]
              refine runs_cond_true_le (v := 1) (Expr.eval_reg_of_eq (by simp [hr6])) (by decide) ?_
              refine runs_assign_le (v := mid) (Expr.eval_reg_of_eq (by simp)) ?_ (by
                simp only [Expr.size, argsSize_cons, argsSize_nil, powGeContract, powGeCost]
                omega)
              refine ⟨⟨hm2', by simp [hr0], by simp [hr1], by simp [lo, hlo2],
                by simp [lo, hmid_gt], by simp [mid]; omega, by simp [lo, hlo_pow],
                by simp [hmp]⟩, ?_⟩
              simp only [Function.update_self, Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide),
                Function.update_of_ne (show (3 : ℕ) ≠ 6 by decide),
                Function.update_of_ne (show (3 : ℕ) ≠ 5 by decide)]
              exact clog2_halve_lt (by omega : 2 ≤ hi - lo) (by dsimp only [mid]; omega)
            · have hr6 : ret2 = 0 := by simp [hret2, hmp]
              refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [hr6])) ?_
              refine runs_assign_le (v := mid) (Expr.eval_reg_of_eq (by simp)) ?_ (by
                simp only [Expr.size, argsSize_cons, argsSize_nil, powGeContract, powGeCost]
                omega)
              refine ⟨⟨hm2', by simp [hr0], by simp [hr1], by simp [mid]; omega,
                by simp [hi, hmid_lt], by simp [hi, hhi_le], by simp; omega,
                by simp [hi, hhi_pow]⟩, ?_⟩
              simp only [Function.update_self, Function.update_of_ne (show (4 : ℕ) ≠ 3 by decide),
                Function.update_of_ne (show (4 : ℕ) ≠ 6 by decide),
                Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide)]
              exact clog2_halve_lt (by omega : 2 ≤ hi - lo) (by dsimp only [mid]; omega))
      have hnpow : nCap ≤ nCap ^ L := by
        calc nCap = nCap ^ 1 := (pow_one nCap).symm
          _ ≤ nCap ^ L := Nat.pow_le_pow_right (by omega) hL1
      refine runs_seq_triple_le hloop
        ⟨rfl, by simp [startState], by simp [startState], by simp, by simp [h2lt], by simp,
          by simp; omega, by simp [hnpow]⟩ ?_
      intro st₂ ⟨⟨hm₂, _, _, hlo2, _, _, hlo_pow, hhi_pow⟩, hhi_eq⟩
      refine runs_ret_le (v := st₂.regs 4) (Expr.eval_reg_of_eq rfl)
        ⟨hm₂, ?_⟩ ?_
      · rw [hhi_eq] at hhi_pow ⊢
        exact (phaseBase_eq_of_bracket hL1 hlo2 hlo_pow hhi_pow).symm
      · simp only [Expr.size, argsSize_cons, argsSize_nil, powGeContract, powGeCost,
          phaseBaseContract, phaseBaseCost, Function.update_self,
          Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide)]
        have hm_le : Nat.clog 2 (nCap - 2) ≤ Nat.log 2 (nCap + 2) + 1 :=
          le_trans (Nat.clog_mono_right 2 (by omega)) (clog2_le_log2_add_one nCap)
        have hstep_le : (1 + 1 + 1 + 1 + 1 + (45 * L + 65) + 1) * Nat.clog 2 (nCap - 2) ≤
            (45 * L + 80) * Nat.clog 2 (nCap - 2) :=
          Nat.mul_le_mul_right _ (by omega)
        have harith := phaseBase_cost_arith L nCap (Nat.clog 2 (nCap - 2)) hm_le
        omega

/-- `bundleSplitBudgetStmt` meets `bundleSplitBudgetContract`. -/
theorem bundleSplitBudget_meetsContract {w k M : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (spanParamProcs b)) :
    MeetsContract w p (b + spanParamIdxSplitBudget) (bundleSplitBudgetContract w k M) := by
  refine meetsContract_of_runs
    (hp.get (i := spanParamIdxSplitBudget) (by simp [spanParamProcs, spanParamIdxSplitBudget])) ?_
  rintro args mem pos ω _ ⟨rfl, hk1, hw64, h56k, h2W⟩
  simp only [spanParamProcs, spanParamIdxSplitBudget, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [bundleSplitBudgetStmt]
  have hdiv_le : (56 * M + k - 1) / k ≤ 56 * M + 1 := by
    have h1 : 56 * M + k - 1 ≤ k * (56 * M + 1) := by
      have : 56 * M ≤ 56 * M * k := Nat.le_mul_of_pos_right _ (by omega)
      rw [Nat.mul_add_one, mul_comm k (56 * M)]
      omega
    exact Nat.div_le_of_le_mul h1
  have hretW : 2 * ((56 * M + k - 1) / k) < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_ret_le (v := 2 * ((56 * M + k - 1) / k))
    (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_div
        (Expr.eval_sub
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := M) (by simp [startState])) (by omega))
            (Expr.eval_reg_of_eq (v := k) (by simp [startState])) h56k)
          (Expr.eval_const (by omega)) h56k)
        (Expr.eval_reg_of_eq (v := k) (by simp [startState])) (by omega))
      hretW)
    ⟨rfl, (bundleSplitBudget_eq_div k M hk1).symm⟩ ?_
  simp only [Expr.size, bundleSplitBudgetContract]
  omega

end

end MinCostFlow.SparseCore.Program
