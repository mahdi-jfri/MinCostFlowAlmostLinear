module

public import MinCostFlow.LSF.Program.DecompGreedyMath
public import MinCostFlow.LSF.Program.Utils

/-!
# The label pass of the tree decomposition

`decompLabelProc` walks the top-down order `Q` forward, over the positions `1, …, n - 1`. At
`x = Q[j]` with parent `p` it writes the label `(labY x, labB x)` of the parent edge of `x`
(`DecompGenLabel.lean`): `(p, bidx x)` when `x` is in a closed batch of `p` or `p` is the root,
and the label of `p` otherwise. The parent comes before `x` in `Q`, so its label is already
written. The test is `c = [0 < [bidx x < nb p] + [p = r]]`, and the label is
`c (p, bidx x) + (1 - c) (label of p)`, with no branch. The cost is `O(n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `8` is `j`). Registers: `9 = x`, `10 = p`, `11 = bidx x`, `12 = c`. -/
def decompLabelBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 2) (.reg 9))) ;;
  .assign 11 (.load (.bin .add (.reg 5) (.reg 9))) ;;
  .assign 12 (.bin .lt (.const 0) (.bin .add (.bin .lt (.reg 11) (.load (.bin .add (.reg 4) (.reg 10))))
    (.bin .eq (.reg 10) (.reg 3)))) ;;
  .store (.bin .add (.reg 6) (.reg 9)) (.bin .add (.bin .mul (.reg 12) (.reg 10))
    (.bin .mul (.bin .sub (.const 1) (.reg 12)) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
  .store (.bin .add (.reg 7) (.reg 9)) (.bin .add (.bin .mul (.reg 12) (.reg 11))
    (.bin .mul (.bin .sub (.const 1) (.reg 12)) (.load (.bin .add (.reg 7) (.reg 10)))))

/-- Args: `[n, qPtr, parPtr, r, nbPtr, bidxPtr, labYPtr, labBPtr]`. -/
def decompLabelProc : Stmt :=
  forRange 8 (.const 1) (.reg 0) decompLabelBody ;;
  .ret (.const 0)

lemma decompLabelProc_noRand : decompLabelProc.NoRand := by
  simp [decompLabelProc, decompLabelBody, forRange, forUp, Stmt.NoRand]

/-- The label rule at index `x`, read from the arrays. -/
def LabelRule (par nb bidx labY labB : ℕ → ℕ) (r x : ℕ) : Prop :=
  (labY x, labB x) = if bidx x < nb (par x) ∨ par x = r then (par x, bidx x)
    else (labY (par x), labB (par x))

/-- The contract of `decompLabelProc`. The label arrays start at `0`. -/
def decompLabelContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr r nbPtr bidxPtr labYPtr labBPtr : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, r, nbPtr, bidxPtr, labYPtr, labBPtr] ∧ 0 < n ∧ 16 ≤ 2 ^ w ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    qPtr + n ≤ labYPtr ∧ parPtr + n ≤ labYPtr ∧ nbPtr + n ≤ labYPtr ∧ bidxPtr + n ≤ labYPtr ∧
    labYPtr + n ≤ labBPtr ∧ labBPtr + n < 2 ^ w ∧
    (∀ x < n, x ≠ r → mem (bidxPtr + x) < n) ∧ (∀ x < n, mem (labYPtr + x) = 0 ∧ mem (labBPtr + x) = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr r nbPtr bidxPtr labYPtr labBPtr : ℕ),
    args = [n, qPtr, parPtr, r, nbPtr, bidxPtr, labYPtr, labBPtr] ∧ ret = 0 ∧
    (∀ a, a < labYPtr ∨ labBPtr + n ≤ a → mem' a = mem a) ∧
    (∀ x < n, x ≠ r → LabelRule (fun x => mem (parPtr + x)) (fun x => mem (nbPtr + x))
        (fun x => mem (bidxPtr + x)) (fun x => mem' (labYPtr + x)) (fun x => mem' (labBPtr + x)) r x) ∧
    (∀ x < n, mem' (labYPtr + x) < n ∧ mem' (labBPtr + x) < n)
  cost args _ := 80 * args.getD 0 0 + 20

private lemma test_eq (b nbp pp r : ℕ) :
    (if 0 < (if b < nbp then 1 else 0) + (if pp = r then 1 else 0) then 1 else 0) =
      (if b < nbp ∨ pp = r then 1 else 0) := by
  by_cases h1 : b < nbp <;> by_cases h2 : pp = r <;> simp [h1, h2]

private lemma sel_eq {c a a' : ℕ} (P : Prop) [Decidable P] (hc : c = if P then 1 else 0) :
    c * a + (1 - c) * a' = if P then a else a' := by
  subst hc; split_ifs <;> simp

theorem decompLabel_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some decompLabelProc) :
    MeetsContract w p b (decompLabelContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, r, nbPtr, bidxPtr, labYPtr, labBPtr, Q, rfl, hn, hw, hQ, hQat, hq, hpa,
    hnb, hbi, hly, hlb, hbid, hzero⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, qPtr, parPtr, r, nbPtr, bidxPtr, labYPtr, labBPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set nb : ℕ → ℕ := fun x => mem (nbPtr + x) with hnbf
  set bidx : ℕ → ℕ := fun x => mem (bidxPtr + x) with hbidx
  have hnw : n < 2 ^ w := hwords n (by simp [hargs])
  have hlenQ : Q.length = n := hQ.len
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 8, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < labYPtr ∨ labBPtr + n ≤ a → st.mem a = mem a) ∧
    (∀ x < n, st.mem (labYPtr + x) < n ∧ st.mem (labBPtr + x) < n) ∧
    ∀ i (hi : i < Q.length), 1 ≤ i → i < j →
      LabelRule par nb bidx (fun x => st.mem (labYPtr + x)) (fun x => st.mem (labBPtr + x)) r Q[i]
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 8 (.const 1) (.reg 0) decompLabelBody) (normalPost (Inv n))
      (fun _ => (n - 1) * (70 + (Expr.reg 0).size + 8) +
        ((Expr.const 1).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 70 1 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl, fun x hx => ?_,
        fun i _ h1 h2 => absurd h2 (by omega)⟩
      · simp only [Function.update_of_ne (show i ≠ 8 by omega)]
        interval_cases i <;> simp [startState, hargs]
      · simp only [startState]; rw [(hzero x hx).1, (hzero x hx).2]; exact ⟨hn, hn⟩
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j hj1 hjn st ω' hI
      obtain ⟨hR, h8, hfr, hbd, hdone⟩ := hI
      have r1 : st.regs 1 = qPtr := hR 1 (by omega)
      have r2 : st.regs 2 = parPtr := hR 2 (by omega)
      have r3 : st.regs 3 = r := hR 3 (by omega)
      have r4 : st.regs 4 = nbPtr := hR 4 (by omega)
      have r5 : st.regs 5 = bidxPtr := hR 5 (by omega)
      have r6 : st.regs 6 = labYPtr := hR 6 (by omega)
      have r7 : st.regs 7 = labBPtr := hR 7 (by omega)
      have hjQ : j < Q.length := by omega
      set x := Q[j] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := by
        intro h
        have h0 := hQ.head_eq hn
        rw [← h0, hx] at h
        have := (hQ.nodup.getElem_inj_iff).mp h
        omega
      have hpQ := hQ.after j hjQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set pp := par x with hpp
      have hpx : pp ≠ x := by
        have hnt := hQ.not_mem_take hjQ
        rw [← hx] at hnt
        exact fun h => hnt (h ▸ hpQ)
      have hmx : st.mem (qPtr + j) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hjQ
      have hmp : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      have hmb : st.mem (bidxPtr + x) = bidx x := hfr _ (Or.inl (by omega))
      have hmnb : st.mem (nbPtr + pp) = nb pp := hfr _ (Or.inl (by omega))
      have hbx : bidx x < n := hbid x hxn hxr
      set bb := bidx x with hbb
      set cc := (if bb < nb pp ∨ pp = r then 1 else 0) with hcc
      have hcc1 : cc ≤ 1 := by rw [hcc]; split_ifs <;> omega
      obtain ⟨hy, hb⟩ := hbd pp hpn
      set ly := st.mem (labYPtr + pp) with hly'
      set lb := st.mem (labBPtr + pp) with hlb'
      have hvy : cc * pp + (1 - cc) * ly = if bb < nb pp ∨ pp = r then pp else ly :=
        sel_eq _ hcc
      have hvb : cc * bb + (1 - cc) * lb = if bb < nb pp ∨ pp = r then bb else lb :=
        sel_eq _ hcc
      have hvy_lt : cc * pp + (1 - cc) * ly < n := by rw [hvy]; split_ifs <;> omega
      have hvb_lt : cc * bb + (1 - cc) * lb < n := by rw [hvb]; split_ifs <;> omega
      have hm1 : Function.update st.mem (labYPtr + x) (cc * pp + (1 - cc) * ly) (labBPtr + pp) = lb := by
        rw [Function.update_of_ne (by omega)]
      refine runs_start_le ?_
      unfold decompLabelBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp]; eval_expr) ?_
      refine runs_seq_assign_le (v := bb) (by rw [← hmb]; eval_expr) ?_
      refine runs_seq_assign_le (v := cc) (by
        rw [hcc, ← test_eq, ← hmnb]
        have : (if bb < st.mem (nbPtr + pp) then 1 else 0) + (if pp = r then 1 else 0) ≤ 2 := by
          split_ifs <;> omega
        eval_expr) ?_
      refine runs_seq_store_le (x := labYPtr + x) (v := cc * pp + (1 - cc) * ly) (by eval_expr)
        (by
          have : cc * pp ≤ n := by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;>
            simp [h] <;> omega
          have : (1 - cc) * ly ≤ n := by
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;> simp [h] <;> omega
          eval_expr) ?_
      refine runs_store_le (x := labBPtr + x) (v := cc * bb + (1 - cc) * lb) (by eval_expr)
        (by
          have : cc * bb ≤ n := by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;>
            simp [h] <;> omega
          have : (1 - cc) * lb ≤ n := by
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;> simp [h] <;> omega
          eval_expr) ⟨⟨fun i hi => ?_, by simp, ?_, ?_, ?_⟩, by simpa using h8⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 9 by omega), Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 12 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro y hy'
        dsimp only
        by_cases hyx : y = x
        · subst hyx
          rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
          exact ⟨hvy_lt, hvb_lt⟩
        · constructor
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hbd y hy').1
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hbd y hy').2
      · intro i hi h1 h2
        dsimp only
        have hstab : ∀ z, z < n → z ≠ x →
            Function.update (Function.update st.mem (labYPtr + x) (cc * pp + (1 - cc) * ly))
              (labBPtr + x) (cc * bb + (1 - cc) * lb) (labYPtr + z) = st.mem (labYPtr + z) ∧
            Function.update (Function.update st.mem (labYPtr + x) (cc * pp + (1 - cc) * ly))
              (labBPtr + x) (cc * bb + (1 - cc) * lb) (labBPtr + z) = st.mem (labBPtr + z) := by
          intro z hzn hz
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
            by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]⟩
        by_cases hij : i = j
        · subst hij
          unfold LabelRule
          dsimp only
          rw [(hstab pp hpn hpx).1, (hstab pp hpn hpx).2]
          have hxi : Q[i] = x := rfl
          rw [hxi, Function.update_of_ne (show labYPtr + x ≠ labBPtr + x by omega),
            Function.update_self, Function.update_self, hvy, hvb]
          split_ifs <;> rfl
        · have hiQ : Q[i] ≠ x := by
            intro h
            exact hij ((hQ.nodup.getElem_inj_iff).mp h)
          have hQi_r : Q[i] ≠ r := by
            intro h
            have h0 := hQ.head_eq hn
            have := (hQ.nodup.getElem_inj_iff (hi := hi) (hj := by omega)).mp (h.trans h0.symm)
            omega
          have hpi := hQ.after i hi hQi_r
          have hpix : par Q[i] ≠ x := by
            intro h
            have hmem : x ∈ Q.take i := h ▸ hpi
            exact hQ.not_mem_take hjQ (List.take_subset_take_left _ (by omega) hmem)
          have hold := hdone i hi h1 (by omega)
          have hQin : Q[i] < n := hQ.lt _ (List.getElem_mem _)
          have hpin : par Q[i] < n := hQ.lt _ (List.mem_of_mem_take hpi)
          unfold LabelRule at hold ⊢
          dsimp only at hold ⊢
          rw [(hstab _ hQin hiQ).1, (hstab _ hQin hiQ).2, (hstab _ hpin hpix).1,
            (hstab _ hpin hpix).2]
          exact hold
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold decompLabelProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hlt, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, r, nbPtr, bidxPtr, labYPtr, labBPtr,
    rfl, rfl, hfr, fun x hxn hxr => ?_, hlt⟩ ?_
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hQ.cover x hxn)
    have hi1 : 1 ≤ i := by
      by_contra h0
      have : i = 0 := by omega
      subst this
      exact hxr (hQ.head_eq hn)
    exact hdone i hi hi1 (by omega)
  · simp only [decompLabelContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg]
    omega

end

end MinCostFlow.LSF.Program
