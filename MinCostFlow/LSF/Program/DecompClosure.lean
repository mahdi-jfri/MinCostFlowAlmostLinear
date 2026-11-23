module

public import MinCostFlow.LSF.Program.DecompClosureMath
public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The closure pass of the tree decomposition

`decompClosureProc` walks the top-down order `Q` from the back, over the positions
`n - 1, …, 1`. At `x = Q[k]` with parent `p` it stores `has x = [0 < S x + cnt x]` and
`inR x = [0 < S x + [1 < cnt x]]`, and adds `has x` to `cnt p`. After the loop it stores
`inR r` for the root `r = Q[0]` by the same rule. The result is `ClosureState … 1`
(`DecompClosureMath.lean`), at cost `O(n)`. The array `cnt` starts at `0`, and the marks
`S x` are `0` or `1`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `7` is `k`). Registers: `10 = x`, `11 = p`, `12 = cnt x`, `13 = S x`. -/
def decompClosureBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 7))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 4) (.reg 10))) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.reg 10))) ;;
  .store (.bin .add (.reg 5) (.reg 10)) (.bin .lt (.const 0) (.bin .add (.reg 13) (.reg 12))) ;;
  .store (.bin .add (.reg 6) (.reg 10))
    (.bin .lt (.const 0) (.bin .add (.reg 13) (.bin .lt (.const 1) (.reg 12)))) ;;
  .store (.bin .add (.reg 4) (.reg 11))
    (.bin .add (.load (.bin .add (.reg 4) (.reg 11))) (.load (.bin .add (.reg 5) (.reg 10)))) ;;
  .assign 7 (.bin .sub (.reg 7) (.const 1))

/-- Args: `[n, qPtr, parPtr, sPtr, cntPtr, hasPtr, inPtr]`. The last four statements are the
root step. -/
def decompClosureProc : Stmt :=
  .assign 7 (.bin .sub (.reg 0) (.const 1)) ;;
  .loop (.reg 7) decompClosureBody ;;
  .assign 10 (.load (.reg 1)) ;;
  .assign 12 (.load (.bin .add (.reg 4) (.reg 10))) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.reg 10))) ;;
  .store (.bin .add (.reg 6) (.reg 10))
    (.bin .lt (.const 0) (.bin .add (.reg 13) (.bin .lt (.const 1) (.reg 12)))) ;;
  .ret (.const 0)

lemma decompClosureProc_noRand : decompClosureProc.NoRand := by
  simp [decompClosureProc, decompClosureBody, Stmt.NoRand]

/-- The contract of `decompClosureProc`. The three output arrays lie above everything that is
read. -/
def decompClosureContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr sPtr cntPtr hasPtr inPtr r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, sPtr, cntPtr, hasPtr, inPtr] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    qPtr + n ≤ cntPtr ∧ parPtr + n ≤ cntPtr ∧ sPtr + n ≤ cntPtr ∧ cntPtr + n ≤ hasPtr ∧
    hasPtr + n ≤ inPtr ∧ inPtr + n < 2 ^ w ∧
    (∀ x < n, mem (sPtr + x) ≤ 1) ∧ (∀ u < n, mem (cntPtr + u) = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr sPtr cntPtr hasPtr inPtr : ℕ),
    args = [n, qPtr, parPtr, sPtr, cntPtr, hasPtr, inPtr] ∧ ret = 0 ∧
    (∀ a, a < cntPtr ∨ inPtr + n ≤ a → mem' a = mem a) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      ClosureState Q (fun x => mem (parPtr + x)) n (fun x => mem (sPtr + x))
        (fun u => mem' (cntPtr + u)) (fun x => mem' (hasPtr + x)) (fun x => mem' (inPtr + x)) 1 ∧
      mem' (inPtr + r) = closureIn (mem (sPtr + r)) (mem' (cntPtr + r)))
  cost args _ := 80 * args.getD 0 0 + 60

theorem decompClosure_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some decompClosureProc) :
    MeetsContract w p b (decompClosureContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, sPtr, cntPtr, hasPtr, inPtr, r, Q, rfl, hn, hQ, hQat, hq, hpa, hsl,
    hcl, hhl, hil, hS1, hzero⟩ := hpre
  set args := [n, qPtr, parPtr, sPtr, cntPtr, hasPtr, inPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set S : ℕ → ℕ := fun x => mem (sPtr + x) with hS
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := hwords n (by simp [hargs])
  have hcnt_le : ∀ (cnt has inR : ℕ → ℕ) j, ClosureState Q par n S cnt has inR j →
      ∀ u < n, cnt u ≤ n := by
    intro cnt has inR j hC u hu
    rw [hC.1 u hu]
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_drop, hQ.len]; omega
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ i < 7, st.regs i = args.getD i 0) ∧ st.regs 7 = k ∧ k < n ∧
    (∀ a, a < cntPtr ∨ inPtr + n ≤ a → st.mem a = mem a) ∧
    ClosureState Q par n S (fun u => st.mem (cntPtr + u)) (fun x => st.mem (hasPtr + x))
      (fun x => st.mem (inPtr + x)) (k + 1)
  have hloop : ∀ k₀, Triple w p (Inv k₀) (.loop (.reg 7) decompClosureBody)
      (normalPost (Inv 0)) (fun _ => 80 * k₀ + 3) := by
    intro k₀
    refine Triple.loop_inv (Inv := Inv) (condVal := fun st => st.regs 7) (fun k => k)
      (fun k => 80 * k + 3) ?_ ?_ ?_ k₀
    · intro k st _; eval_expr
    · rintro k st hI h0
      rw [hI.2.1] at h0; subst h0
      exact ⟨hI, by simp⟩
    · rintro k st ⟨hregs, h7, hkn, hfr, hC⟩ hne
      rw [h7] at hne
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨78, ?_⟩
      intro s ω' hs; subst s
      have r1 : st.regs 1 = qPtr := hregs 1 (by omega)
      have r2 : st.regs 2 = parPtr := hregs 2 (by omega)
      have r3 : st.regs 3 = sPtr := hregs 3 (by omega)
      have r4 : st.regs 4 = cntPtr := hregs 4 (by omega)
      have r5 : st.regs 5 = hasPtr := hregs 5 (by omega)
      have r6 : st.regs 6 = inPtr := hregs 6 (by omega)
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
      have hms : st.mem (sPtr + x) = S x := hfr _ (Or.inl (by omega))
      set cx := st.mem (cntPtr + x) with hcx
      set cp := st.mem (cntPtr + pp) with hcp
      have hcx_le : cx ≤ n := hcnt_le _ _ _ _ hC x hxn
      have hcp_le : cp ≤ n := hcnt_le _ _ _ _ hC pp hpn
      have hSx : S x ≤ 1 := hS1 x hxn
      set hv := closureHas (S x) cx with hhv
      set iv := closureIn (S x) cx with hiv
      have hhv_le : hv ≤ 1 := closureHas_le _ _
      have hiv_le : iv ≤ 1 := by rw [hiv]; unfold closureIn; split_ifs <;> omega
      have hm2c : Function.update (Function.update st.mem (hasPtr + x) hv) (inPtr + x) iv
          (cntPtr + pp) = cp := by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hm2h : Function.update (Function.update st.mem (hasPtr + x) hv) (inPtr + x) iv
          (hasPtr + x) = hv := by
        rw [Function.update_of_ne (by omega), Function.update_self]
      refine runs_start_le ?_
      unfold decompClosureBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp]; eval_expr) ?_
      refine runs_seq_assign_le (v := cx) (by rw [hcx]; eval_expr) ?_
      refine runs_seq_assign_le (v := S x) (by rw [← hms]; eval_expr) ?_
      refine runs_seq_store_le (x := hasPtr + x) (v := hv) (by eval_expr) (by
        rw [hhv, closureHas]
        have : S x + cx < 2 ^ w := by omega
        eval_expr) ?_
      refine runs_seq_store_le (x := inPtr + x) (v := iv) (by eval_expr) (by
        rw [hiv, closureIn]
        have : S x + (if 1 < cx then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        eval_expr) ?_
      refine runs_seq_store_le (x := cntPtr + pp) (v := cp + hv) (by eval_expr) (by
        have : cp + hv < 2 ^ w := by omega
        eval_expr) ?_
      set m3 := Function.update (Function.update (Function.update st.mem (hasPtr + x) hv)
        (inPtr + x) iv) (cntPtr + pp) (cp + hv) with hm3
      refine runs_assign_le (v := k') (by show _ = some (k' + 1 - 1); eval_expr) ⟨k', ⟨?_, by simp,
        by omega, ?_, ?_⟩, by omega, ?_⟩ ?_
      · intro i hi
        simp only [Function.update_of_ne (show i ≠ 7 by omega),
          Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 12 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 10 by omega)]
        exact hregs i hi
      · intro a ha
        show m3 a = mem a
        rw [hm3, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hfr a ha
      · have hstep := closureState_step hQ (j := k' + 1 + 1) (by omega) (by omega) hC
        simp only [show k' + 1 + 1 - 1 = k' + 1 by omega] at hstep
        refine closureState_congr hQ (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_) hstep
        · dsimp only
          by_cases hu' : u = pp
          · rw [hu', Function.update_self, hm3, Function.update_self]
          · rw [Function.update_of_ne hu', hm3, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · dsimp only
          by_cases hu' : u = x
          · rw [hu', Function.update_self, hm3, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_of_ne hu', hm3, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · dsimp only
          by_cases hu' : u = x
          · rw [hu', Function.update_self, hm3, Function.update_of_ne (by omega),
              Function.update_self]
          · rw [Function.update_of_ne hu', hm3, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simp only [Expr.size_reg]; omega
      · simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]
        omega
  -- the whole procedure
  have hR0 : ∀ i < 7, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  refine runs_start_le ?_
  unfold decompClosureProc
  refine runs_seq_assign_le (v := n - 1) (by
    have := hR0 0 (by omega); eval_expr) ?_
  refine runs_seq_triple_le (hloop (n - 1)) ⟨fun i hi => ?_, by simp, by omega,
    fun a _ => rfl, ?_⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 7 by omega)]; exact hR0 i hi
  · rw [show n - 1 + 1 = n by omega]
    exact closureState_congr hQ (cnt := fun _ => 0) (fun u hu => (hzero u hu).symm)
      (fun _ _ => rfl) (fun _ _ => rfl) (closureState_init hQ S _ _)
  rintro st ⟨hregs, -, -, hfr, hC⟩
  have r1 : st.regs 1 = qPtr := hregs 1 (by omega)
  have r3 : st.regs 3 = sPtr := hregs 3 (by omega)
  have r4 : st.regs 4 = cntPtr := hregs 4 (by omega)
  have r6 : st.regs 6 = inPtr := hregs 6 (by omega)
  have hlen : 0 < Q.length := by rw [hQ.len]; exact hn
  have hmr : st.mem qPtr = r := by
    rw [hfr _ (Or.inl (by omega)), ← hQ.head_eq hn]
    simpa using hQat 0 hlen
  have hrn : r < n := hQ.lt r (hQ.head_eq hn ▸ List.getElem_mem hlen)
  have hms : st.mem (sPtr + r) = S r := hfr _ (Or.inl (by omega))
  set cr := st.mem (cntPtr + r) with hcr
  have hcr_le : cr ≤ n := hcnt_le _ _ _ _ hC r hrn
  have hSr : S r ≤ 1 := hS1 r hrn
  set iv := closureIn (S r) cr with hiv
  have hiv_le : iv ≤ 1 := by rw [hiv]; unfold closureIn; split_ifs <;> omega
  refine runs_seq_assign_le (v := r) (by rw [← hmr]; eval_expr) ?_
  refine runs_seq_assign_le (v := cr) (by rw [hcr]; eval_expr) ?_
  refine runs_seq_assign_le (v := S r) (by rw [← hms]; eval_expr) ?_
  refine runs_seq_store_le (x := inPtr + r) (v := iv) (by eval_expr) (by
    rw [hiv, closureIn]
    have : S r + (if 1 < cr then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    eval_expr) ?_
  have hfr' : ∀ a, a < cntPtr ∨ inPtr + n ≤ a → Function.update st.mem (inPtr + r) iv a = mem a := by
    intro a ha
    rw [Function.update_of_ne (by omega)]; exact hfr a ha
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, sPtr, cntPtr, hasPtr, inPtr, rfl,
    rfl, hfr', fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    have hrQ : r' ∉ Q.drop 1 := fun h => ((hQ.mem_drop_one hn).mp h).2 rfl
    have hC' := closureState_congr hQ (cnt' := fun u => Function.update st.mem (inPtr + r') iv
      (cntPtr + u)) (has' := fun u => Function.update st.mem (inPtr + r') iv (hasPtr + u))
      (fun u _ => (Function.update_of_ne (by omega) _ _).symm)
      (fun u _ => (Function.update_of_ne (by omega) _ _).symm) (fun _ _ => rfl) hC
    refine ⟨⟨hC'.1, fun x hx => ?_⟩, ?_⟩
    · have hxr : x ≠ r' := fun h => hrQ (h ▸ hx)
      have e3 : Function.update st.mem (inPtr + r') iv (inPtr + x) = st.mem (inPtr + x) :=
        Function.update_of_ne (by omega) _ _
      dsimp only
      rw [e3]
      exact hC'.2 x hx
    · dsimp only
      rw [Function.update_self, Function.update_of_ne (by omega)]
  · simp only [decompClosureContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
