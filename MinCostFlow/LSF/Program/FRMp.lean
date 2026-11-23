module

public import MinCostFlow.LSF.Program.FRIdx
public import MinCostFlow.LSF.Program.TopDownPass
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The first part of the roots pass: smallest edges going up

`frMpProc` first stores `mp r = 0` for the root `r = Q[0]`. Then it walks the top-down order `Q`
over the positions `1, …, n - 1`. At `x = Q[j]` with parent `p` and parent edge index `e`, it
stores `mp x = e` when `p` is in `R`, and otherwise the one of `e` and `mp p` with the smaller
`piv`, with no branch. This is `MpRule` (`FRIdx.lean`), and `mp_bridge` turns it into the
`π`-smallest edge up to the nearest proper ancestor in `R`. The cost is `O(n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `8` is `j`). Registers: `10 = x`, `11 = p`, `12 = e`, `13 = mp p`,
`14 = inR p`, `15 = [piv e < piv (mp p)]`. -/
def frMpBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 3) (.reg 10))) ;;
  .assign 13 (.load (.bin .add (.reg 6) (.reg 11))) ;;
  .assign 14 (.load (.bin .add (.reg 5) (.reg 11))) ;;
  .assign 15 (.bin .lt (.load (.bin .add (.reg 4) (.reg 12)))
    (.load (.bin .add (.reg 4) (.reg 13)))) ;;
  .store (.bin .add (.reg 6) (.reg 10))
    (.bin .add (.bin .mul (.reg 14) (.reg 12))
      (.bin .mul (.bin .sub (.const 1) (.reg 14))
        (.bin .add (.bin .mul (.reg 15) (.reg 12))
          (.bin .mul (.bin .sub (.const 1) (.reg 15)) (.reg 13)))))

/-- Args: `[n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM]`. -/
def frMpProc : Stmt :=
  .store (.bin .add (.reg 6) (.load (.reg 1))) (.const 0) ;;
  forRange 8 (.const 1) (.reg 0) frMpBody ;;
  .ret (.const 0)

lemma frMpProc_noRand : frMpProc.NoRand := by
  simp [frMpProc, frMpBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `frMpProc`. The output array lies above everything that is read. -/
def frMpContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr pePtr piPtr inRPtr mpPtr tM r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    (∀ x < n, x ≠ r → mem (pePtr + x) < tM) ∧ (∀ x < n, mem (inRPtr + x) ≤ 1) ∧
    mem (inRPtr + r) = 1 ∧
    qPtr + n ≤ mpPtr ∧ parPtr + n ≤ mpPtr ∧ pePtr + n ≤ mpPtr ∧ piPtr + tM ≤ mpPtr ∧
    inRPtr + n ≤ mpPtr ∧ mpPtr + n < 2 ^ w
  post args mem ret mem' := ∃ (n qPtr parPtr pePtr piPtr inRPtr mpPtr tM : ℕ),
    args = [n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM] ∧ ret = 0 ∧
    (∀ a, a < mpPtr ∨ mpPtr + n ≤ a → mem' a = mem a) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      mem' (mpPtr + r) = 0 ∧
      ∀ x < n, x ≠ r → mem' (mpPtr + x) < tM ∧
        MpRule (fun y => mem (inRPtr + y)) (fun y => mem (parPtr + y))
          (fun y => mem (pePtr + y)) (fun i => mem (piPtr + i)) (fun y => mem' (mpPtr + y)) x)
  cost args _ := 150 * args.getD 0 0 + 60

theorem frMp_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some frMpProc) :
    MeetsContract w p b (frMpContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM, r, Q, rfl, hn, hQ, hQat, hpe,
    hinR1, hinRr, hq, hpa, hpea, hpia, hia, hma⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set inR : ℕ → ℕ := fun x => mem (inRPtr + x) with hinR
  set pe : ℕ → ℕ := fun x => mem (pePtr + x) with hpe_def
  set piv : ℕ → ℕ := fun i => mem (piPtr + i) with hpiv
  set rule : (ℕ → ℕ) → ℕ → Prop := fun f y => f y < tM ∧ MpRule inR par pe piv f y with hrule
  have hloc : TDLocal par rule := by
    intro f f' y h1 h2 ⟨hlt, hr⟩
    refine ⟨h1 ▸ hlt, ?_⟩
    unfold MpRule at hr ⊢
    rw [← h1, ← h2]; exact hr
  have hnw : n < 2 ^ w := by omega
  have hlenQ : Q.length = n := hQ.len
  have hlen0 : 0 < Q.length := by omega
  have hrQ : r = Q[0] := (hQ.head_eq hn).symm
  have hrn : r < n := hQ.lt r (by rw [hrQ]; exact List.getElem_mem _)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 8, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < mpPtr ∨ mpPtr + n ≤ a → st.mem a = mem a) ∧
    st.mem (mpPtr + r) = 0 ∧
    ∀ y ∈ Q.take j, y ≠ r → rule (fun z => st.mem (mpPtr + z)) y
  have hloop : ∀ st₀ : State, Inv 1 {st₀ with regs := Function.update st₀.regs 8 1} →
      Triple w p (fun st => st = st₀)
      (forRange 8 (.const 1) (.reg 0) frMpBody) (normalPost (Inv n))
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
      have r4 : st.regs 4 = piPtr := hR 4 (by omega)
      have r5 : st.regs 5 = inRPtr := hR 5 (by omega)
      have r6 : st.regs 6 = mpPtr := hR 6 (by omega)
      have hjQ : j < Q.length := by omega
      set x := Q[j] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := hQ.ne_root hj1 hjQ
      have hpQ := hQ.after j hjQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set pp := par x with hpp
      set e := pe x with he
      have hetM : e < tM := hpe x hxn hxr
      set mp : ℕ → ℕ := fun z => st.mem (mpPtr + z) with hmp
      have hmpp : mp pp < tM ∨ pp = r := by
        by_cases hpr : pp = r
        · exact Or.inr hpr
        · exact Or.inl (hS pp hpQ hpr).1
      have hmpp' : mp pp < tM := by
        rcases hmpp with h | h
        · exact h
        · rw [h]; show st.mem (mpPtr + r) < tM; rw [hmr]; omega
      have hmx : st.mem (qPtr + j) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hjQ
      have hmp_ : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      have hme : st.mem (pePtr + x) = e := hfr _ (Or.inl (by omega))
      have hmm : st.mem (mpPtr + pp) = mp pp := rfl
      have hmi : st.mem (inRPtr + pp) = inR pp := hfr _ (Or.inl (by omega))
      have hpe1 : st.mem (piPtr + e) = piv e := hfr _ (Or.inl (by omega))
      have hpe2 : st.mem (piPtr + mp pp) = piv (mp pp) := hfr _ (Or.inl (by omega))
      have hc1 : inR pp ≤ 1 := hinR1 pp hpn
      set c2 := (if piv e < piv (mp pp) then 1 else 0) with hc2
      have hc21 : c2 ≤ 1 := by rw [hc2]; split_ifs <;> omega
      have hinner : c2 * e + (1 - c2) * mp pp ≤ tM := sel_le hc21 (by omega) (by omega)
      set v := (if inR pp = 1 then e else if piv e < piv (mp pp) then e else mp pp) with hv
      have hc1' : inR pp = if inR pp = 1 then 1 else 0 := by split_ifs with h <;> omega
      have hvsel : inR pp * e + (1 - inR pp) * (c2 * e + (1 - c2) * mp pp) = v := by
        rw [sel_eq _ hc2, sel_eq _ hc1']
      have hvt : v < tM := by
        rw [hv]
        split_ifs with h1 h2
        · exact hetM
        · exact hetM
        · exact hmpp'
      have h1 : c2 * e ≤ tM := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc21 with h | h <;> simp [h] <;> omega
      have h2 : (1 - c2) * mp pp ≤ tM := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc21 with h | h <;> simp [h] <;> omega
      have h3 : inR pp * e ≤ tM := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h | h <;> simp [h] <;> omega
      have h4 : (1 - inR pp) * (c2 * e + (1 - c2) * mp pp) ≤ tM := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h | h <;> simp [h] <;> omega
      have h5 : inR pp * e + (1 - inR pp) * (c2 * e + (1 - c2) * mp pp) ≤ tM := by omega
      refine runs_start_le ?_
      unfold frMpBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp_]; eval_expr) ?_
      refine runs_seq_assign_le (v := e) (by rw [← hme]; eval_expr) ?_
      refine runs_seq_assign_le (v := mp pp) (by rw [← hmm]; eval_expr) ?_
      refine runs_seq_assign_le (v := inR pp) (by rw [← hmi]; eval_expr) ?_
      refine runs_seq_assign_le (v := c2) (by
        rw [hc2, ← hpe1, ← hpe2]
        eval_expr) ?_
      refine runs_store_le (x := mpPtr + x) (v := v) (by eval_expr)
        (by rw [← hvsel]; eval_expr) ⟨⟨fun i hi => ?_, by simpa using h8, ?_, ?_, ?_⟩,
          by simpa using h8⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 12 by omega),
          Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 14 by omega),
          Function.update_of_ne (show i ≠ 15 by omega), Function.update_of_ne (show i ≠ 8 by omega)]
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
        unfold MpRule
        rw [Function.update_self, Function.update_of_ne (show par x ≠ x from
          fun h => hQ.not_mem_take hjQ (by rw [← hx, ← h]; exact hpQ))]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- the root step, then the loop
  have hR0 : ∀ i < 8, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hmr : mem qPtr = r := by rw [hrQ]; simpa using hQat 0 hlen0
  refine runs_start_le ?_
  unfold frMpProc
  refine runs_seq_store_le (x := mpPtr + r) (v := 0) (by
    have := hR0 1 (by omega); have := hR0 6 (by omega); rw [← hmr]; eval_expr) (by eval_expr) ?_
  set m1 := Function.update mem (mpPtr + r) 0 with hm1
  refine runs_seq_triple_le (hloop _ ⟨fun i hi => ?_, by simp, fun a ha => ?_, ?_, ?_⟩) rfl ?_
  · simp only [Function.update_of_ne (show i ≠ 8 by omega)]
    exact hR0 i hi
  · show m1 a = mem a
    rw [hm1, Function.update_of_ne (by omega)]
  · show m1 (mpPtr + r) = 0
    rw [hm1, Function.update_self]
  · intro y hy hyr
    rw [hQ.take_one hn] at hy
    exact absurd (List.mem_singleton.mp hy) hyr
  rintro st ⟨-, -, hfr, hmr', hS⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM,
    rfl, rfl, hfr, fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    refine ⟨hmr', fun x hx hxr => ?_⟩
    rw [List.take_of_length_le (by omega)] at hS
    exact hS x (hQ.cover x hx) hxr
  · simp only [frMpContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
