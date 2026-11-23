module

public import MinCostFlow.LSF.Program.THHeavyMath
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The heavy pass

`thHeavyProc` first stores `top r = r` and `cnt r = 1` for the root `r = Q[0]`. Then it walks the
top-down order `Q` forward, over the positions `1, …, n - 1`. At `x = Q[j]` with parent `p` it
stores `top x = top p` when `sz p < sz x + sz x` (a heavy child) and `top x = x` otherwise, with
no branch, and adds one to `cnt (top x)`. The parent comes before `x` in `Q`, so its top is
already stored. The result is `HeavyState … n` (`THHeavyMath.lean`), at cost `O(n)`. The array
`cnt` starts at `0`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `6` is `j`). Registers: `10 = x`, `11 = p`, `12 = [heavy]`, `13 = top x`. -/
def thHeavyBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 6))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .assign 12 (.bin .lt (.load (.bin .add (.reg 3) (.reg 11)))
    (.bin .add (.load (.bin .add (.reg 3) (.reg 10))) (.load (.bin .add (.reg 3) (.reg 10))))) ;;
  .assign 13 (.bin .add (.bin .mul (.reg 12) (.load (.bin .add (.reg 4) (.reg 11))))
    (.bin .mul (.bin .sub (.const 1) (.reg 12)) (.reg 10))) ;;
  .store (.bin .add (.reg 4) (.reg 10)) (.reg 13) ;;
  .store (.bin .add (.reg 5) (.reg 13)) (.bin .add (.load (.bin .add (.reg 5) (.reg 13))) (.const 1))

/-- Args: `[n, qPtr, parPtr, szPtr, topPtr, cntPtr]`. The first three statements are the root
step. -/
def thHeavyProc : Stmt :=
  .assign 10 (.load (.reg 1)) ;;
  .store (.bin .add (.reg 4) (.reg 10)) (.reg 10) ;;
  .store (.bin .add (.reg 5) (.reg 10)) (.const 1) ;;
  forRange 6 (.const 1) (.reg 0) thHeavyBody ;;
  .ret (.const 0)

lemma thHeavyProc_noRand : thHeavyProc.NoRand := by
  simp [thHeavyProc, thHeavyBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `thHeavyProc`. The sizes are at most `n` and `cnt` starts at `0`. -/
def thHeavyContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr szPtr topPtr cntPtr r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, szPtr, topPtr, cntPtr] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    qPtr + n ≤ topPtr ∧ parPtr + n ≤ topPtr ∧ szPtr + n ≤ topPtr ∧ topPtr + n ≤ cntPtr ∧
    cntPtr + n < 2 ^ w ∧ (∀ x < n, mem (szPtr + x) ≤ n) ∧ (∀ t < n, mem (cntPtr + t) = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr szPtr topPtr cntPtr : ℕ),
    args = [n, qPtr, parPtr, szPtr, topPtr, cntPtr] ∧ ret = 0 ∧
    (∀ a, a < topPtr ∨ cntPtr + n ≤ a → mem' a = mem a) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      HeavyState Q (fun x => mem (parPtr + x)) n r (fun x => mem (szPtr + x))
        (fun x => mem' (topPtr + x)) (fun t => mem' (cntPtr + t)) n)
  cost args _ := 100 * args.getD 0 0 + 60

private lemma sel_eq' {c a a' : ℕ} (P : Prop) [Decidable P] (hc : c = if P then 1 else 0) :
    c * a + (1 - c) * a' = if P then a else a' := by
  subst hc; split_ifs <;> simp

private lemma cnt_le {Q : List ℕ} {par : ℕ → ℕ} {n r : ℕ} {sz top cnt : ℕ → ℕ} {j : ℕ}
    (h : HeavyState Q par n r sz top cnt j) {t : ℕ} (ht : t < n) : cnt t ≤ j := by
  rw [h.2.2.2 t ht]
  exact (List.length_filter_le _ _).trans (by rw [List.length_take]; omega)

theorem thHeavy_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some thHeavyProc) :
    MeetsContract w p b (thHeavyContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, szPtr, topPtr, cntPtr, r, Q, rfl, hn, hQ, hQat, hq, hpa, hsa, hta,
    hca, hszle, hzero⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, qPtr, parPtr, szPtr, topPtr, cntPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set sz : ℕ → ℕ := fun x => mem (szPtr + x) with hsz
  have hnw : n < 2 ^ w := by omega
  have hlenQ : Q.length = n := hQ.len
  have hlen0 : 0 < Q.length := by omega
  have hrQ : r = Q[0] := (hQ.head_eq hn).symm
  have hrn : r < n := hQ.lt r (by rw [hrQ]; exact List.getElem_mem _)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 6, st.regs i = args.getD i 0) ∧ st.regs 6 = j ∧
    (∀ a, a < topPtr ∨ cntPtr + n ≤ a → st.mem a = mem a) ∧
    HeavyState Q par n r sz (fun x => st.mem (topPtr + x)) (fun t => st.mem (cntPtr + t)) j
  have hloop : ∀ st₀ : State, Inv 1 {st₀ with regs := Function.update st₀.regs 6 1} →
      Triple w p (fun st => st = st₀)
      (forRange 6 (.const 1) (.reg 0) thHeavyBody) (normalPost (Inv n))
      (fun _ => (n - 1) * (90 + (Expr.reg 0).size + 8) +
        ((Expr.const 1).size + (Expr.reg 0).size + 5)) := by
    intro st₀ hI1
    refine Triple.forRange_const 90 1 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl; exact ⟨by eval_expr, hI1⟩
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j hj1 hjn st ω' hI
      obtain ⟨hR, h6, hfr, hH⟩ := hI
      have r1 : st.regs 1 = qPtr := hR 1 (by omega)
      have r2 : st.regs 2 = parPtr := hR 2 (by omega)
      have r3 : st.regs 3 = szPtr := hR 3 (by omega)
      have r4 : st.regs 4 = topPtr := hR 4 (by omega)
      have r5 : st.regs 5 = cntPtr := hR 5 (by omega)
      have hjQ : j < Q.length := by omega
      set x := Q[j] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := by
        intro h
        rw [hrQ, hx] at h
        have := (hQ.nodup.getElem_inj_iff).mp h
        omega
      have hpQ := hQ.after j hjQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set pp := par x with hpp
      have hmx : st.mem (qPtr + j) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hjQ
      have hmp : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      have hmsx : st.mem (szPtr + x) = sz x := hfr _ (Or.inl (by omega))
      have hmsp : st.mem (szPtr + pp) = sz pp := hfr _ (Or.inl (by omega))
      have hsx := hszle x hxn
      have hsp := hszle pp hpn
      set top : ℕ → ℕ := fun y => st.mem (topPtr + y) with htop
      set cnt : ℕ → ℕ := fun t => st.mem (cntPtr + t) with hcnt
      have htp : top pp < n := hH.2.1 pp hpQ
      set cc := (if sz pp < sz x + sz x then 1 else 0) with hcc
      have hcc1 : cc ≤ 1 := by rw [hcc]; split_ifs <;> omega
      set v := heavyTop sz par top x with hv
      have hvsel : cc * top pp + (1 - cc) * x = v := by
        rw [sel_eq' _ hcc, hv, heavyTop, show 2 * sz x = sz x + sz x by omega]
      have hvn : v < n := by rw [hv, heavyTop]; split_ifs <;> omega
      have hcv := cnt_le hH hvn
      have hstep := heavyState_step hQ hj1 hjQ hH
      rw [← hx, ← hv] at hstep
      refine runs_start_le ?_
      unfold thHeavyBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp]; eval_expr) ?_
      refine runs_seq_assign_le (v := cc) (by
        rw [hcc, ← hmsx, ← hmsp]
        have : st.mem (szPtr + x) + st.mem (szPtr + x) < 2 ^ w := by rw [hmsx]; change mem (szPtr + x) + mem (szPtr + x) < 2 ^ w; omega
        eval_expr) ?_
      refine runs_seq_assign_le (v := v) (by
        rw [← hvsel]
        have hmt : st.mem (topPtr + pp) = top pp := rfl
        have : cc * top pp ≤ n := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;> simp [h] <;> omega
        have : (1 - cc) * x ≤ n := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;> simp [h] <;> omega
        rw [← hmt] at *
        eval_expr) ?_
      refine runs_seq_store_le (x := topPtr + x) (v := v) (by eval_expr) (by eval_expr) ?_
      have hm1 : Function.update st.mem (topPtr + x) v (cntPtr + v) = cnt v := by
        rw [Function.update_of_ne (by omega)]
      refine runs_store_le (x := cntPtr + v) (v := cnt v + 1) (by eval_expr)
        (by
          rw [← hm1]
          have : Function.update st.mem (topPtr + x) v (cntPtr + v) + 1 < 2 ^ w := by
            rw [hm1]; omega
          eval_expr) ⟨⟨fun i hi => ?_, by simpa using h6, ?_, ?_⟩, by simpa using h6⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 12 by omega),
          Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 6 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · dsimp only
        refine heavyState_congr hQ hrn (fun y hy => ?_) (fun t ht => ?_) hstep
        · by_cases hyx : y = x
          · rw [hyx, Function.update_of_ne (by omega), Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne hyx]
        · by_cases htv : t = v
          · rw [htv, Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne htv]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- the root step, then the loop
  have hR0 : ∀ i < 6, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hmr : mem qPtr = r := by rw [hrQ]; simpa using hQat 0 hlen0
  refine runs_start_le ?_
  unfold thHeavyProc
  refine runs_seq_assign_le (v := r) (by
    have := hR0 1 (by omega); rw [← hmr]; eval_expr) ?_
  refine runs_seq_store_le (x := topPtr + r) (v := r) (by
    have := hR0 4 (by omega); eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cntPtr + r) (v := 1) (by
    have := hR0 5 (by omega); eval_expr) (by eval_expr) ?_
  set m1 := Function.update (Function.update mem (topPtr + r) r) (cntPtr + r) 1 with hm1
  refine runs_seq_triple_le (hloop _ ⟨fun i hi => ?_, by simp, fun a ha => ?_, ?_⟩) rfl ?_
  · simp only [Function.update_of_ne (show i ≠ 6 by omega),
      Function.update_of_ne (show i ≠ 10 by omega)]
    exact hR0 i hi
  · show m1 a = mem a
    rw [hm1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · refine heavyState_init hQ hn hrn ?_ ?_ (fun t ht htr => ?_)
    · show m1 (topPtr + r) = r
      rw [hm1, Function.update_of_ne (by omega), Function.update_self]
    · show m1 (cntPtr + r) = 1
      rw [hm1, Function.update_self]
    · show m1 (cntPtr + t) = 0
      rw [hm1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzero t ht
  rintro st ⟨-, -, hfr, hH⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, szPtr, topPtr, cntPtr,
    rfl, rfl, hfr, fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    exact hH
  · simp only [thHeavyContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
