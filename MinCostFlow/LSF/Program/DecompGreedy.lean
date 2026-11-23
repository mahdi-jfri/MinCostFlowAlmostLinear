module

public import MinCostFlow.LSF.Program.DecompGreedyMath
public import MinCostFlow.LSF.Program.Utils

/-!
# The greedy pass of the tree decomposition

`decompGreedyProc` walks the top-down order `Q` from the back, over the positions
`n - 1, …, 1`. At `x = Q[k]` with parent `p` it
* stores the weight `s x = ν x + cur x` of the open bag of `x`;
* stores the batch number `bidx x = nb p`;
* adds `s x` to the open batch of `p`: if the new sum `c'` is below `θ` it is kept as `cur p`,
  and otherwise the batch is closed (`nb p` goes up by one and `cur p` becomes `0`).

The last step has no branch: with `b = [c' < θ]` it stores `cur p = b c'` and
`nb p = nb p + (1 - b)`. The result is `GreedyState … 1` (`DecompGreedyMath.lean`), at cost
`O(n)`. The arrays `cur` and `nb` start at `0`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `9` is `k`). Registers: `10 = x`, `11 = p`, `12 = s x`, `13 = c'`,
`14 = [c' < θ]`. -/
def decompGreedyBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 9))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .assign 12 (.bin .add (.load (.bin .add (.reg 3) (.reg 10)))
    (.load (.bin .add (.reg 5) (.reg 10)))) ;;
  .store (.bin .add (.reg 8) (.reg 10)) (.reg 12) ;;
  .assign 13 (.bin .add (.load (.bin .add (.reg 5) (.reg 11))) (.reg 12)) ;;
  .store (.bin .add (.reg 7) (.reg 10)) (.load (.bin .add (.reg 6) (.reg 11))) ;;
  .assign 14 (.bin .lt (.reg 13) (.reg 4)) ;;
  .store (.bin .add (.reg 5) (.reg 11)) (.bin .mul (.reg 14) (.reg 13)) ;;
  .store (.bin .add (.reg 6) (.reg 11))
    (.bin .add (.load (.bin .add (.reg 6) (.reg 11))) (.bin .sub (.const 1) (.reg 14))) ;;
  .assign 9 (.bin .sub (.reg 9) (.const 1))

/-- Args: `[n, qPtr, parPtr, nuPtr, θ, curPtr, nbPtr, bidxPtr, sPtr]`. -/
def decompGreedyProc : Stmt :=
  .assign 9 (.bin .sub (.reg 0) (.const 1)) ;;
  .loop (.reg 9) decompGreedyBody ;;
  .ret (.const 0)

lemma decompGreedyProc_noRand : decompGreedyProc.NoRand := by
  simp [decompGreedyProc, decompGreedyBody, Stmt.NoRand]

/-- Two top-down orders stored at the same address are equal. -/
lemma topDownOrder_eq_of_listAt {mem : ℕ → ℕ} {a n r r' : ℕ} {par par' : ℕ → ℕ}
    {Q Q' : List ℕ} (hQ : TopDownOrder n r par Q) (hQ' : TopDownOrder n r' par' Q')
    (h : ListAt mem a Q) (h' : ListAt mem a Q') : Q' = Q :=
  List.ext_getElem (by rw [hQ.len, hQ'.len]) (fun i h1 h2 => by rw [← h' i h1, ← h i h2])

/-- The contract of `decompGreedyProc`. The four output arrays lie above everything that is
read. -/
def decompGreedyContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr nuPtr θ curPtr nbPtr bidxPtr sPtr r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, nuPtr, θ, curPtr, nbPtr, bidxPtr, sPtr] ∧ 0 < n ∧ 0 < θ ∧
    3 * θ < 2 ^ w ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    qPtr + n ≤ curPtr ∧ parPtr + n ≤ curPtr ∧ nuPtr + n ≤ curPtr ∧ curPtr + n ≤ nbPtr ∧
    nbPtr + n ≤ bidxPtr ∧ bidxPtr + n ≤ sPtr ∧ sPtr + n < 2 ^ w ∧
    (∀ x < n, mem (nuPtr + x) ≤ θ) ∧ (∀ u < n, mem (curPtr + u) = 0 ∧ mem (nbPtr + u) = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr nuPtr θ curPtr nbPtr bidxPtr sPtr : ℕ),
    args = [n, qPtr, parPtr, nuPtr, θ, curPtr, nbPtr, bidxPtr, sPtr] ∧ ret = 0 ∧
    (∀ a, a < curPtr ∨ sPtr + n ≤ a → mem' a = mem a) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      GreedyState Q (fun x => mem (parPtr + x)) n θ (fun x => mem (nuPtr + x))
        (fun u => mem' (curPtr + u)) (fun u => mem' (nbPtr + u)) (fun x => mem' (bidxPtr + x))
        (fun x => mem' (sPtr + x)) 1)
  cost args _ := 80 * args.getD 0 0 + 20

theorem decompGreedy_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some decompGreedyProc) :
    MeetsContract w p b (decompGreedyContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, nuPtr, θ, curPtr, nbPtr, bidxPtr, sPtr, r, Q, rfl, hn, hθ, h3θ,
    hQ, hQat, hq, hpa, hnu, hc, hnbl, hbl, hsl, hνθ, hzero⟩ := hpre
  set args := [n, qPtr, parPtr, nuPtr, θ, curPtr, nbPtr, bidxPtr, sPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set ν : ℕ → ℕ := fun x => mem (nuPtr + x) with hν
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := hwords n (by simp [hargs])
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ i < 9, st.regs i = args.getD i 0) ∧ st.regs 9 = k ∧ k < n ∧
    (∀ a, a < curPtr ∨ sPtr + n ≤ a → st.mem a = mem a) ∧
    GreedyState Q par n θ ν (fun u => st.mem (curPtr + u)) (fun u => st.mem (nbPtr + u))
      (fun x => st.mem (bidxPtr + x)) (fun x => st.mem (sPtr + x)) (k + 1)
  have hloop : ∀ k₀, Triple w p (Inv k₀) (.loop (.reg 9) decompGreedyBody)
      (normalPost (Inv 0)) (fun _ => 80 * k₀ + 3) := by
    intro k₀
    refine Triple.loop_inv (Inv := Inv) (condVal := fun st => st.regs 9) (fun k => k)
      (fun k => 80 * k + 3) ?_ ?_ ?_ k₀
    · intro k st _; eval_expr
    · rintro k st hI h0
      rw [hI.2.1] at h0; subst h0
      exact ⟨hI, by simp⟩
    · rintro k st ⟨hregs, h9, hkn, hfr, hG⟩ hne
      rw [h9] at hne
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨78, ?_⟩
      intro s ω' hs; subst s
      have r1 : st.regs 1 = qPtr := hregs 1 (by omega)
      have r2 : st.regs 2 = parPtr := hregs 2 (by omega)
      have r3 : st.regs 3 = nuPtr := hregs 3 (by omega)
      have r4 : st.regs 4 = θ := hregs 4 (by omega)
      have r5 : st.regs 5 = curPtr := hregs 5 (by omega)
      have r6 : st.regs 6 = nbPtr := hregs 6 (by omega)
      have r7 : st.regs 7 = bidxPtr := hregs 7 (by omega)
      have r8 : st.regs 8 = sPtr := hregs 8 (by omega)
      have hkQ : k' + 1 < Q.length := by rw [hQ.len]; exact hkn
      set x := Q[k' + 1] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := by
        intro h
        have h0 := hQ.head_eq hn
        rw [← h0, hx] at h
        have := (hQ.nodup.getElem_inj_iff).mp h
        omega
      have hpQ := hQ.after (k' + 1) hkQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set pp := par x with hpp
      have hmx : st.mem (qPtr + (k' + 1)) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hkQ
      have hmp : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      have hmnu : st.mem (nuPtr + x) = ν x := hfr _ (Or.inl (by omega))
      set curx := st.mem (curPtr + x) with hcurx
      set curp := st.mem (curPtr + pp) with hcurp
      set nbp := st.mem (nbPtr + pp) with hnbp
      have hcx_lt : curx < θ := hG.2.2 x hxn
      have hcp_lt : curp < θ := hG.2.2 pp hpn
      have hνx : ν x ≤ θ := hνθ x hxn
      have hnbp_lt : nbp < n := by
        have h1 := onlineRun_nb_le _ _ _ _ _ (hG.1 pp hpn)
        have h2 := procChildren_length_lt hQ pp (k' + 1 + 1) (by omega) hn
        simp only at h1; omega
      set sx := ν x + curx with hsx
      set c' := curp + sx with hc'
      set bb := if c' < θ then 1 else 0 with hbb
      have hbb_le : bb ≤ 1 := by rw [hbb]; split_ifs <;> omega
      have hm1c : Function.update st.mem (sPtr + x) sx (curPtr + pp) = curp := by
        rw [Function.update_of_ne (by omega)]
      have hm1n : Function.update st.mem (sPtr + x) sx (nbPtr + pp) = nbp := by
        rw [Function.update_of_ne (by omega)]
      have hm3n : Function.update (Function.update (Function.update st.mem (sPtr + x) sx)
          (bidxPtr + x) nbp) (curPtr + pp) (bb * c') (nbPtr + pp) = nbp := by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm1n]
      refine runs_start_le ?_
      unfold decompGreedyBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp]; eval_expr) ?_
      refine runs_seq_assign_le (v := sx) (by
        rw [hsx, ← hmnu, hcurx]; eval_expr) ?_
      refine runs_seq_store_le (x := sPtr + x) (v := sx) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_assign_le (v := c') (by rw [hc']; eval_expr) ?_
      refine runs_seq_store_le (x := bidxPtr + x) (v := nbp) (by eval_expr)
        (by eval_expr) ?_
      refine runs_seq_assign_le (v := bb) (by rw [hbb]; eval_expr) ?_
      refine runs_seq_store_le (x := curPtr + pp) (v := bb * c') (by eval_expr) (by
        have : bb * c' ≤ c' := by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbb_le with h | h <;>
          simp [h]
        eval_expr) ?_
      refine runs_seq_store_le (x := nbPtr + pp) (v := nbp + (1 - bb)) (by eval_expr)
        (by eval_expr) ?_
      set m4 := Function.update (Function.update (Function.update (Function.update st.mem
        (sPtr + x) sx) (bidxPtr + x) nbp) (curPtr + pp) (bb * c')) (nbPtr + pp)
        (nbp + (1 - bb)) with hm4
      refine runs_assign_le (v := k') (by show _ = some (k' + 1 - 1); eval_expr) ⟨k', ⟨?_, by simp,
        by omega, ?_, ?_⟩, by omega, ?_⟩ ?_
      · intro i hi
        simp only [Function.update_of_ne (show i ≠ 9 by omega),
          Function.update_of_ne (show i ≠ 14 by omega), Function.update_of_ne (show i ≠ 13 by omega),
          Function.update_of_ne (show i ≠ 12 by omega), Function.update_of_ne (show i ≠ 11 by omega),
          Function.update_of_ne (show i ≠ 10 by omega)]
        exact hregs i hi
      · intro a ha
        show m4 a = mem a
        rw [hm4, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · have hstep := greedyState_step hQ (j := k' + 1 + 1) (by omega) (by omega) hG
        simp only [show k' + 1 + 1 - 1 = k' + 1 by omega] at hstep
        refine greedyState_congr hQ (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_)
          (fun u hu => ?_) hstep
        · dsimp only
          by_cases hu' : u = pp
          · rw [hu', Function.update_self, hm4, Function.update_of_ne (by omega),
              Function.update_self, hbb]
            split_ifs <;> simp <;> rfl
          · rw [Function.update_of_ne hu', hm4, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
        · dsimp only
          by_cases hu' : u = pp
          · rw [hu', Function.update_self, hm4, Function.update_self, hbb]
            split_ifs <;> simp <;> rfl
          · rw [Function.update_of_ne hu', hm4, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
        · dsimp only
          by_cases hu' : u = x
          · rw [hu', Function.update_self, hm4, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_of_ne hu', hm4, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
        · dsimp only
          by_cases hu' : u = x
          · rw [hu', Function.update_self, hm4, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · rw [Function.update_of_ne hu', hm4, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
      · simp only [Expr.size_reg]; omega
      · simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]
        omega
  -- the whole procedure
  have hR0 : ∀ i < 9, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  refine runs_start_le ?_
  unfold decompGreedyProc
  refine runs_seq_assign_le (v := n - 1) (by
    have := hR0 0 (by omega); eval_expr) ?_
  refine runs_seq_triple_le (hloop (n - 1)) ⟨fun i hi => ?_, by simp, by omega,
    fun a _ => rfl, ?_⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 9 by omega)]; exact hR0 i hi
  · rw [show n - 1 + 1 = n by omega]
    refine greedyState_congr hQ (cur := fun _ => 0) (nb := fun _ => 0)
      (fun u hu => (hzero u hu).1.symm) (fun u hu => (hzero u hu).2.symm) (fun _ _ => rfl)
      (fun _ _ => rfl) (greedyState_init hQ hθ ν _ _)
  rintro st ⟨-, -, -, hfr, hG⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, nuPtr, θ, curPtr, nbPtr, bidxPtr,
    sPtr, rfl, rfl, hfr, fun Q' r' hQ' hQat' => by
      rw [topDownOrder_eq_of_listAt hQ hQ' hQat hQat']; simpa using hG⟩ ?_
  simp only [decompGreedyContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
    Expr.size_bin]
  omega

end

end MinCostFlow.LSF.Program
