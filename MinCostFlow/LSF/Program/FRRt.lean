module

public import MinCostFlow.LSF.Program.FRIdx
public import MinCostFlow.LSF.Program.TopDownPass
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The third part of the roots pass: the roots

`frRtProc` first stores `rt r = r` for the root `r = Q[0]`. Then it walks the top-down order `Q`
over the positions `1, …, n - 1`. At `x = Q[j]` it stores `rt x = x` when `x` is in `R`;
otherwise `own (pe x) - 1` when the parent edge of `x` has an owner, and `rt (par x)` when it has
none, with no branch. This is `RtRule` (`FRIdx.lean`), and `rt_bridge` turns it into the root of
`x` in `F_T(R, π)`. The cost is `O(n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `8` is `j`). Registers: `10 = x`, `11 = inR x`, `12 = own (pe x)`,
`13 = [own (pe x) ≠ 0]`. -/
def frRtBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 11 (.load (.bin .add (.reg 4) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 3) (.reg 10))))) ;;
  .assign 13 (.bin .sub (.const 1) (.bin .eq (.reg 12) (.const 0))) ;;
  .store (.bin .add (.reg 6) (.reg 10))
    (.bin .add (.bin .mul (.reg 11) (.reg 10))
      (.bin .mul (.bin .sub (.const 1) (.reg 11))
        (.bin .add (.bin .mul (.reg 13) (.bin .sub (.reg 12) (.const 1)))
          (.bin .mul (.bin .sub (.const 1) (.reg 13))
            (.load (.bin .add (.reg 6) (.load (.bin .add (.reg 2) (.reg 10)))))))))

/-- Args: `[n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr]`. -/
def frRtProc : Stmt :=
  .assign 10 (.load (.reg 1)) ;;
  .store (.bin .add (.reg 6) (.reg 10)) (.reg 10) ;;
  forRange 8 (.const 1) (.reg 0) frRtBody ;;
  .ret (.const 0)

lemma frRtProc_noRand : frRtProc.NoRand := by
  simp [frRtProc, frRtBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `frRtProc`. The output array lies above everything that is read. -/
def frRtContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr pePtr inRPtr ownPtr rtPtr tM r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    (∀ x < n, x ≠ r → mem (pePtr + x) < tM) ∧ (∀ x < n, mem (inRPtr + x) ≤ 1) ∧
    (∀ i < tM, mem (ownPtr + i) ≤ n) ∧
    qPtr + n ≤ rtPtr ∧ parPtr + n ≤ rtPtr ∧ pePtr + n ≤ rtPtr ∧ inRPtr + n ≤ rtPtr ∧
    ownPtr + tM ≤ rtPtr ∧ rtPtr + n < 2 ^ w
  post args mem ret mem' := ∃ (n qPtr parPtr pePtr inRPtr ownPtr rtPtr : ℕ),
    args = [n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr] ∧ ret = 0 ∧
    (∀ a, a < rtPtr ∨ rtPtr + n ≤ a → mem' a = mem a) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      mem' (rtPtr + r) = r ∧
      ∀ x < n, x ≠ r → RtRule (fun y => mem (inRPtr + y)) (fun y => mem (parPtr + y))
          (fun y => mem (pePtr + y)) (fun i => mem (ownPtr + i)) (fun y => mem' (rtPtr + y)) x)
  cost args _ := 150 * args.getD 0 0 + 60

theorem frRt_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some frRtProc) :
    MeetsContract w p b (frRtContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr, tM, r, Q, rfl, hn, hQ, hQat, hpe,
    hinR1, hown, hq, hpa, hpea, hia, hoa, hra⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set inR : ℕ → ℕ := fun x => mem (inRPtr + x) with hinR
  set pe : ℕ → ℕ := fun x => mem (pePtr + x) with hpe_def
  set own : ℕ → ℕ := fun i => mem (ownPtr + i) with hown_def
  set rule : (ℕ → ℕ) → ℕ → Prop := fun f y => f y < n ∧ RtRule inR par pe own f y with hrule
  have hloc : TDLocal par rule := by
    intro f f' y h1 h2 ⟨hlt, hr⟩
    refine ⟨h1 ▸ hlt, ?_⟩
    unfold RtRule at hr ⊢
    rw [← h1, ← h2]; exact hr
  have hnw : n < 2 ^ w := by omega
  have hlenQ : Q.length = n := hQ.len
  have hlen0 : 0 < Q.length := by omega
  have hrQ : r = Q[0] := (hQ.head_eq hn).symm
  have hrn : r < n := hQ.lt r (by rw [hrQ]; exact List.getElem_mem _)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 7, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < rtPtr ∨ rtPtr + n ≤ a → st.mem a = mem a) ∧
    st.mem (rtPtr + r) = r ∧
    ∀ y ∈ Q.take j, y ≠ r → rule (fun z => st.mem (rtPtr + z)) y
  have hloop : ∀ st₀ : State, Inv 1 {st₀ with regs := Function.update st₀.regs 8 1} →
      Triple w p (fun st => st = st₀)
      (forRange 8 (.const 1) (.reg 0) frRtBody) (normalPost (Inv n))
      (fun _ => (n - 1) * (120 + (Expr.reg 0).size + 8) +
        ((Expr.const 1).size + (Expr.reg 0).size + 5)) := by
    intro st₀ hI1
    refine Triple.forRange_const 120 1 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl; exact ⟨by eval_expr, hI1⟩
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j hj1 hjn st ω' hI
      obtain ⟨hR, h8, hfr, hmr, hS⟩ := hI
      have r1 : st.regs 1 = qPtr := hR 1 (by omega)
      have r2 : st.regs 2 = parPtr := hR 2 (by omega)
      have r3 : st.regs 3 = pePtr := hR 3 (by omega)
      have r4 : st.regs 4 = inRPtr := hR 4 (by omega)
      have r5 : st.regs 5 = ownPtr := hR 5 (by omega)
      have r6 : st.regs 6 = rtPtr := hR 6 (by omega)
      have hjQ : j < Q.length := by omega
      set x := Q[j] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := hQ.ne_root hj1 hjQ
      have hpQ := hQ.after j hjQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set pp := par x with hpp
      set e := pe x with he
      have hetM : e < tM := hpe x hxn hxr
      set rt : ℕ → ℕ := fun z => st.mem (rtPtr + z) with hrt
      have hrtp : rt pp < n := by
        by_cases hpr : pp = r
        · rw [hpr]; show st.mem (rtPtr + r) < n; rw [hmr]; exact hrn
        · exact (hS pp hpQ hpr).1
      set o := own e with ho
      have hon : o ≤ n := hown e hetM
      have hmx : st.mem (qPtr + j) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hjQ
      have hmp_ : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      have hme : st.mem (pePtr + x) = e := hfr _ (Or.inl (by omega))
      have hmi : st.mem (inRPtr + x) = inR x := hfr _ (Or.inl (by omega))
      have hmo : st.mem (ownPtr + e) = o := hfr _ (Or.inl (by omega))
      have hmrt : st.mem (rtPtr + pp) = rt pp := rfl
      have hc1 : inR x ≤ 1 := hinR1 x hxn
      set c2 := 1 - (if o = 0 then 1 else 0) with hc2
      have hc21 : c2 ≤ 1 := by omega
      have hc2' : c2 = if o ≠ 0 then 1 else 0 := by rw [hc2]; split_ifs <;> simp_all
      set v := (if inR x = 1 then x else if o ≠ 0 then o - 1 else rt pp) with hv
      have hc1' : inR x = if inR x = 1 then 1 else 0 := by split_ifs with h <;> omega
      have hvsel : inR x * x + (1 - inR x) * (c2 * (o - 1) + (1 - c2) * rt pp) = v := by
        rw [sel_eq _ hc2', sel_eq _ hc1']
      have hvt : v < n := by
        rw [hv]
        split_ifs with h1 h2
        · exact hxn
        · omega
        · exact hrtp
      have hinner : c2 * (o - 1) + (1 - c2) * rt pp ≤ n := sel_le hc21 (by omega) (by omega)
      have h1 : c2 * (o - 1) ≤ n := (mul_le_self_of_le_one hc21).trans (by omega)
      have h2 : (1 - c2) * rt pp ≤ n := (mul_le_self_of_le_one (by omega)).trans (by omega)
      have h3 : inR x * x ≤ n := (mul_le_self_of_le_one hc1).trans (by omega)
      have h4 : (1 - inR x) * (c2 * (o - 1) + (1 - c2) * rt pp) ≤ n :=
        (mul_le_self_of_le_one (by omega)).trans hinner
      have h5 : inR x * x + (1 - inR x) * (c2 * (o - 1) + (1 - c2) * rt pp) ≤ n :=
        sel_le hc1 (by omega) hinner
      have b2 : (1 - c2) * st.mem (rtPtr + st.mem (parPtr + x)) ≤ n := by rw [hmp_]; exact h2
      have b4 : (1 - inR x) * (c2 * (o - 1) + (1 - c2) * st.mem (rtPtr + st.mem (parPtr + x)))
          ≤ n := by rw [hmp_]; exact h4
      have b5 : inR x * x + (1 - inR x) * (c2 * (o - 1) +
          (1 - c2) * st.mem (rtPtr + st.mem (parPtr + x))) ≤ n := by rw [hmp_]; exact h5
      have b6 : ownPtr + st.mem (pePtr + x) < 2 ^ w := by rw [hme]; omega
      have b7 : rtPtr + st.mem (parPtr + Q[j]) < 2 ^ w := by
        rw [← hx, hmp_]; omega
      refine runs_start_le ?_
      unfold frRtBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := inR x) (by rw [← hmi]; eval_expr) ?_
      refine runs_seq_assign_le (v := o) (by rw [← hmo, ← hme]; eval_expr) ?_
      refine runs_seq_assign_le (v := c2) (by rw [hc2]; eval_expr) ?_
      refine runs_store_le (x := rtPtr + x) (v := v) (by eval_expr)
        (by rw [← hvsel, ← hmrt, ← hmp_]; eval_expr)
        ⟨⟨fun i hi => ?_, by simpa using h8, ?_, ?_, ?_⟩, by simpa using h8⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 12 by omega),
          Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 8 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hmr
      · dsimp only
        rw [update_shift]
        refine td_step hQ hloc hjQ hS (fun _ => ?_)
        rw [← hx]
        refine ⟨by rw [Function.update_self]; exact hvt, ?_⟩
        unfold RtRule
        rw [Function.update_self, Function.update_of_ne (show par x ≠ x from
          fun h => hQ.not_mem_take hjQ (by rw [← hx, ← h]; exact hpQ))]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- the root step, then the loop
  have hR0 : ∀ i < 7, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hmr : mem qPtr = r := by rw [hrQ]; simpa using hQat 0 hlen0
  refine runs_start_le ?_
  unfold frRtProc
  refine runs_seq_assign_le (v := r) (by
    have := hR0 1 (by omega); rw [← hmr]; eval_expr) ?_
  refine runs_seq_store_le (x := rtPtr + r) (v := r) (by
    have := hR0 6 (by omega); eval_expr) (by eval_expr) ?_
  set m1 := Function.update mem (rtPtr + r) r with hm1
  refine runs_seq_triple_le (hloop _ ⟨fun i hi => ?_, by simp, fun a ha => ?_, ?_, ?_⟩) rfl ?_
  · simp only [Function.update_of_ne (show i ≠ 8 by omega),
      Function.update_of_ne (show i ≠ 10 by omega)]
    exact hR0 i hi
  · show m1 a = mem a
    rw [hm1, Function.update_of_ne (by omega)]
  · show m1 (rtPtr + r) = r
    rw [hm1, Function.update_self]
  · intro y hy hyr
    rw [hQ.take_one hn] at hy
    exact absurd (List.mem_singleton.mp hy) hyr
  rintro st ⟨-, -, hfr, hmr', hS⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr,
    rfl, rfl, hfr, fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    refine ⟨hmr', fun x hx hxr => ?_⟩
    rw [List.take_of_length_le (by omega)] at hS
    exact (hS x (hQ.cover x hx) hxr).2
  · simp only [frRtContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
