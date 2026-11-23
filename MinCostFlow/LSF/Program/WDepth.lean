module

public import MinCostFlow.LSF.Program.UArith
public import MinCostFlow.LSF.Program.TopDownPass
public import MinCostFlow.LSF.Program.DecompGreedy
public import MinCostFlow.LSF.Program.THHeavyMath

/-!
# Weighted depths

`wDepthProc` gives every vertex index `x` a block `Ld x` of `LB` limbs that holds the length of
the tree path from `x` to the root. The blocks start at zero. The procedure walks the top-down
order `Q` over the positions `1, …, n - 1` and, at `x = Q[j]`, adds the block of the parent and
the block of the parent edge `LT (pe x)` into the block of `x` (two calls of `uAccProc`). The
parent comes first in `Q`, so its block is final. The result is the rule
`Ld x = Ld (par x) + LT (pe x)` modulo the capacity, at cost `O(n LB)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-- One step (register `8` is `j`). Registers: `10 = x`, `11 = par x`, `12 = pe x`. -/
def wDepthBody (bAcc : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 3) (.reg 10))) ;;
  .call 13 bAcc [.bin .add (.reg 5) (.bin .mul (.reg 10) (.reg 6)),
    .bin .add (.reg 5) (.bin .mul (.reg 11) (.reg 6)), .reg 6, .const 1, .const 0] ;;
  .call 13 bAcc [.bin .add (.reg 5) (.bin .mul (.reg 10) (.reg 6)),
    .bin .add (.reg 4) (.bin .mul (.reg 12) (.reg 6)), .reg 6, .const 1, .const 0]

/-- Args: `[n, qPtr, parPtr, pePtr, ltBase, ldBase, LB]`. -/
def wDepthProc (bAcc : ℕ) : Stmt :=
  forRange 8 (.const 1) (.reg 0) (wDepthBody bAcc) ;;
  .ret (.const 0)

lemma wDepthProc_noRand (bAcc : ℕ) : (wDepthProc bAcc).NoRand := by
  simp [wDepthProc, wDepthBody, forRange, forUp, Stmt.NoRand]

/-- The rule of the weighted depths at an index `x` other than the root. -/
def LdRule (h LB : ℕ) (par pe lt Ld : ℕ → ℕ) (x : ℕ) : Prop :=
  Ld x = (Ld (par x) + lt (pe x)) % capacity h LB

/-- The contract of `wDepthProc`. The blocks of the weighted depths start at zero and lie above
everything that is read. -/
def wDepthContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr pePtr ltBase ldBase LB tM r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, pePtr, ltBase, ldBase, LB] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    (∀ x < n, x ≠ r → mem (pePtr + x) < tM) ∧
    (∀ i < tM, Valid mem (ltBase + i * LB) h LB) ∧
    (∀ a, ldBase ≤ a → a < ldBase + n * LB → mem a = 0) ∧
    qPtr + n ≤ ldBase ∧ parPtr + n ≤ ldBase ∧ pePtr + n ≤ ldBase ∧ ltBase + tM * LB ≤ ldBase ∧
    ldBase + n * LB < 2 ^ w
  post args mem ret mem' := ∃ (n qPtr parPtr pePtr ltBase ldBase LB : ℕ),
    args = [n, qPtr, parPtr, pePtr, ltBase, ldBase, LB] ∧ ret = 0 ∧
    (∀ a, a < ldBase ∨ ldBase + n * LB ≤ a → mem' a = mem a) ∧
    (∀ x < n, Valid mem' (ldBase + x * LB) h LB) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      unsignedVal mem' (ldBase + r * LB) h LB = 0 ∧
      ∀ x < n, x ≠ r → LdRule h LB (fun y => mem (parPtr + y)) (fun y => mem (pePtr + y))
        (fun i => unsignedVal mem (ltBase + i * LB) h LB)
        (fun y => unsignedVal mem' (ldBase + y * LB) h LB) x)
  cost args _ := args.getD 0 0 * (150 * args.getD 6 0 + 120) + 20

theorem wDepth_meetsContract {w h : ℕ} {p : Program} {b bAcc : ℕ}
    (hAcc : MeetsContract w p bAcc (uAccContract w h)) (hh : 1 ≤ h) (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (wDepthProc bAcc)) :
    MeetsContract w p b (wDepthContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, pePtr, ltBase, ldBase, LB, tM, r, Q, rfl, hn, hQ, hQat, hpe, hlt,
    hzero, hq, hpa, hpea, hlta, hldw⟩ := hpre
  have hB2 : 2 ≤ base h := by
    rw [base]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, qPtr, parPtr, pePtr, ltBase, ldBase, LB] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set pe : ℕ → ℕ := fun x => mem (pePtr + x) with hpe_def
  set lt : ℕ → ℕ := fun i => unsignedVal mem (ltBase + i * LB) h LB with hlt_def
  set rule : (ℕ → ℕ) → ℕ → Prop := fun f y => LdRule h LB par pe lt f y with hrule
  have hloc : TDLocal par rule := by
    intro f f' y h1 h2 hr
    unfold rule LdRule at hr ⊢
    rw [← h1, ← h2]; exact hr
  have hnw : n < 2 ^ w := by
    have := blk_end LB (show 0 < n from hn); omega
  have hlenQ : Q.length = n := hQ.len
  have hrQ : r = Q[0] := (hQ.head_eq hn).symm
  have hrn : r < n := hQ.lt r (by rw [hrQ]; exact List.getElem_mem _)
  have hzv : ∀ y < n, ∀ i < LB, mem (ldBase + y * LB + i) = 0 := fun y hy i hi =>
    hzero _ (by omega) (by have := blk_end LB hy; omega)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 7, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < ldBase ∨ ldBase + n * LB ≤ a → st.mem a = mem a) ∧
    (∀ y < n, Valid st.mem (ldBase + y * LB) h LB) ∧
    (∀ y < n, (y ∉ Q.take j ∨ y = r) → ∀ i < LB, st.mem (ldBase + y * LB + i) = 0) ∧
    ∀ y ∈ Q.take j, y ≠ r → rule (fun z => unsignedVal st.mem (ldBase + z * LB) h LB) y
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 8 (.const 1) (.reg 0) (wDepthBody bAcc)) (normalPost (Inv n))
      (fun _ => (n - 1) * ((150 * LB + 100) + (Expr.reg 0).size + 8) +
        ((Expr.const 1).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (150 * LB + 100) 1 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl, fun y hy i hi => ?_,
        fun y hy _ i hi => hzv y hy i hi, fun y hy hyr => ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 8 by omega)]
        interval_cases i <;> simp [startState, hargs]
      · show mem _ < _; rw [hzv y hy i hi]; omega
      · rw [hQ.take_one hn] at hy; exact absurd (List.mem_singleton.mp hy) hyr
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j hj1 hjn st ω' hI
      obtain ⟨hR, h8, hfr, hval, hz, hS⟩ := hI
      have r1 : st.regs 1 = qPtr := hR 1 (by omega)
      have r2 : st.regs 2 = parPtr := hR 2 (by omega)
      have r3 : st.regs 3 = pePtr := hR 3 (by omega)
      have r4 : st.regs 4 = ltBase := hR 4 (by omega)
      have r5 : st.regs 5 = ldBase := hR 5 (by omega)
      have r6 : st.regs 6 = LB := hR 6 (by omega)
      have hjQ : j < Q.length := by omega
      set x := Q[j] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := hQ.ne_root hj1 hjQ
      have hxt : x ∉ Q.take j := hQ.not_mem_take hjQ
      have hpQ := hQ.after j hjQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      have hpx : par x ≠ x := fun h => hxt (by rw [← h]; exact hpQ)
      set pp := par x with hpp
      set e := pe x with he
      have het : e < tM := hpe x hxn hxr
      have hmx : st.mem (qPtr + j) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hjQ
      have hmp_ : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      have hme : st.mem (pePtr + x) = e := hfr _ (Or.inl (by omega))
      have hbx := blk_end LB hxn
      have hbp := blk_end LB hpn
      have hbe := blk_end LB het
      have hdxp := blk_disj LB hpx
      have hltv : Valid st.mem (ltBase + e * LB) h LB := fun i hi => by
        rw [hfr _ (Or.inl (by omega))]; exact hlt e het i hi
      have hltU : unsignedVal st.mem (ltBase + e * LB) h LB = lt e :=
        unsignedVal_congr fun i hi => hfr _ (Or.inl (by omega))
      have hm1 : x * LB < 2 ^ w := by omega
      have hm2 : pp * LB < 2 ^ w := by omega
      have hm3 : e * LB < 2 ^ w := by omega
      refine runs_start_le ?_
      unfold wDepthBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp_]; eval_expr) ?_
      refine runs_seq_assign_le (v := e) (by rw [← hme]; eval_expr) ?_
      refine runs_seq_call_le (vs := [ldBase + x * LB, ldBase + pp * LB, LB, 1, 0]) hAcc
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨_, _, _, _, _, rfl, by omega, by omega, hval x hxn, hval pp hpn, by omega, by omega,
          by omega⟩ ?_
      rintro v₁ mem₁ pos₁ ⟨d₁, a₁, L₁, k₁, n₁, heq₁, -, hfr₁, hv₁, hu₁⟩
      simp only [List.cons.injEq, and_true] at heq₁
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₁
      have hltv₁ : Valid mem₁ (ltBase + e * LB) h LB := fun i hi => by
        rw [hfr₁ _ (Or.inl (by omega))]; exact hltv i hi
      refine runs_call_le (vs := [ldBase + x * LB, ltBase + e * LB, LB, 1, 0]) hAcc
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨_, _, _, _, _, rfl, by omega, by omega, hv₁, hltv₁, by omega, by omega, by omega⟩ ?_
      rintro v₂ mem₂ pos₂ ⟨d₂, a₂, L₂, k₂, n₂, heq₂, -, hfr₂, hv₂, hu₂⟩
      simp only [List.cons.injEq, and_true] at heq₂
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₂
      -- the memory changed only in the block of `x`
      have hout : ∀ a, a < ldBase + x * LB ∨ ldBase + x * LB + LB ≤ a → mem₂ a = st.mem a :=
        fun a ha => (hfr₂ a ha).trans (hfr₁ a ha)
      have hother : ∀ y < n, y ≠ x → ∀ i < LB,
          mem₂ (ldBase + y * LB + i) = st.mem (ldBase + y * LB + i) := fun y hy hyx i hi => by
        have := blk_disj LB hyx; have := blk_end LB hy
        exact hout _ (by omega)
      set f : ℕ → ℕ := fun z => unsignedVal st.mem (ldBase + z * LB) h LB with hf
      have hx0 : f x = 0 := unsignedVal_zero fun i hi => hz x hxn (Or.inl hxt) i hi
      have hnewx : unsignedVal mem₂ (ldBase + x * LB) h LB = (f pp + lt e) % capacity h LB := by
        rw [hu₂, hu₁, accTerm, accTerm, if_neg (by omega), if_neg (by omega), one_mul, one_mul]
        have hU1 : unsignedVal mem₁ (ltBase + e * LB) h LB = lt e := by
          rw [← hltU]; exact unsignedVal_congr fun i hi => hfr₁ _ (Or.inl (by omega))
        rw [hU1]
        have hfx : unsignedVal st.mem (ldBase + x * LB) h LB = 0 := hx0
        rw [hfx, zero_add, Nat.mod_eq_of_lt (unsignedVal_lt (hval pp hpn))]
      have hfeq : ∀ z < n, unsignedVal mem₂ (ldBase + z * LB) h LB =
          Function.update f x ((f pp + lt e) % capacity h LB) z := fun z hz => by
        by_cases hzx : z = x
        · rw [hzx, Function.update_self, hnewx]
        · rw [Function.update_of_ne hzx]
          exact unsignedVal_congr fun i hi => hother z hz hzx i hi
      refine ⟨⟨⟨fun i hi => ?_, ?_, fun a ha => ?_, fun y hy => ?_, fun y hy hy' i hi => ?_,
        fun y hy hyr => ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        simp only [Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 12 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 10 by omega)]
        exact hR i hi
      · simp
      · dsimp only
        rw [hout a (by rcases ha with ha | ha <;> omega)]; exact hfr a ha
      · dsimp only
        by_cases hyx : y = x
        · rw [hyx]; exact hv₂
        · intro i hi; rw [hother y hy hyx i hi]; exact hval y hy i hi
      · dsimp only
        have hyx : y ≠ x := by
          rintro rfl
          rcases hy' with hy' | hy'
          · exact hy' (by
              rw [list_take_succ_eq hjQ]; exact List.mem_append_right _ (List.mem_singleton_self _))
          · exact hxr hy'
        rw [hother y hy hyx i hi]
        refine hz y hy ?_ i hi
        rcases hy' with hy' | hy'
        · left; intro hm; exact hy' (by
            rw [list_take_succ_eq hjQ]; exact List.mem_append_left _ hm)
        · right; exact hy'
      · dsimp only
        have hyn : y < n := hQ.lt y (List.mem_of_mem_take hy)
        have hpyn : y ≠ r → par y < n := fun h => by
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
          rw [List.length_take] at hk
          rw [List.getElem_take] at h ⊢
          exact hQ.lt _ (List.mem_of_mem_take (hQ.after k (by omega) h))
        have := td_step hQ hloc (f := f) (v := (f pp + lt e) % capacity h LB) hjQ hS
          (fun _ => by
            show LdRule h LB par pe lt _ _
            unfold LdRule
            rw [← hx, Function.update_self, Function.update_of_ne hpx]) y hy hyr
        unfold rule LdRule at this ⊢
        beta_reduce
        rw [hfeq y hyn, hfeq _ (hpyn hyr)]
        exact this
      · simp only [Function.update_of_ne (show (8 : ℕ) ≠ 13 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 12 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 11 by omega),
          Function.update_of_ne (show (8 : ℕ) ≠ 10 by omega)]
        exact h8
      · simp only [uAccContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega
  refine runs_start_le ?_
  unfold wDepthProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hval, hz, hS⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, pePtr, ltBase, ldBase, LB,
    rfl, rfl, hfr, hval, fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    rw [hr']
    refine ⟨unsignedVal_zero fun i hi => hz r hrn (Or.inr rfl) i hi, fun x hx hxr => ?_⟩
    rw [List.take_of_length_le (by omega)] at hS
    exact hS x (hQ.cover x hx) hxr
  · simp only [wDepthContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
      Expr.size_reg, Expr.size_bin, Expr.size_load]
    have h1 : (n - 1) * (150 * LB + 100 + 1 + 8) ≤ n * (150 * LB + 109) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : n * (150 * LB + 109) + 11 ≤ n * (150 * LB + 120) := by
      have := Nat.mul_le_mul_left n (show 150 * LB + 109 + 11 ≤ 150 * LB + 120 by omega)
      rw [Nat.mul_add] at this
      nlinarith
    omega

end

end MinCostFlow.LSF.Program
