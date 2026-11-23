module

public import MinCostFlow.MinRatio.FreshTables
import WordRAM.Tactic

/-!
# Dispatching a fixed-graph refresh record

The IPM graph refresh uses deletions and insertions. Each record starts
with its tag. The dispatcher reads that tag and calls the verified name
translation for the corresponding record. Both cases preserve the record
width, which lets a batch loop advance its two cursors by the same amount.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are the source record, two map bases, counter address and heap. -/
def freshRecordBody (ins del : ℕ) : Stmt :=
  .cond (.load (.reg 0))
    (.call 8 del [.reg 0, .reg 1, .reg 4] ;; .ret (.reg 8))
    (.assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
      .assign 6 (.load (.bin .add (.reg 0) (.const 2))) ;;
      .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
      .call 8 ins [.reg 5, .reg 6, .reg 7, .reg 1, .reg 2, .reg 3, .reg 4] ;;
      .ret (.reg 8))

/-- The dispatcher inherits the appropriate translated record and the
corresponding memory effect. The fixed-graph refresh never uses Split. -/
def freshRecordContract (w : ℕ) (record : Update) (internal : ℕ) : Contract where
  pre args mem := ∃ src fwd inv counter heap,
    args = [src, fwd, inv, counter, heap] ∧
    match record with
    | .insert e u v =>
      src + 4 ≤ heap ∧ ListAt mem src (updateWords record) ∧
      e < 2 ^ w ∧ u < 2 ^ w ∧ v < 2 ^ w ∧
      (freshInsertContract w e u v internal).pre [e, u, v, fwd, inv, counter, heap] mem
    | .delete e =>
      (freshDeleteContract w e internal).pre [src, fwd, heap] mem
    | .split .. => False
  post args mem ret mem' := match record with
    | .insert e u v => (freshInsertContract w e u v internal).post
        [e, u, v, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0] mem ret mem'
    | .delete e => (freshDeleteContract w e internal).post
        [args.getD 0 0, args.getD 1 0, args.getD 4 0] mem ret mem'
    | .split .. => False
  cost _ _ := 128

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- The record dispatcher is deterministic when linked to its deterministic callees. -/
theorem freshRecordBody_noRand (ins del : ℕ) : (freshRecordBody ins del).NoRand := by
  simp [freshRecordBody, Stmt.NoRand]

/-- Dispatch and translation of either refresh record costs at most 128 steps. -/
theorem freshRecord_meetsContract {w base ins del internal : ℕ} {p : Program} (record : Update)
    (hp : p.HasAt base [freshRecordBody ins del])
    (hi : ∀ e u v, MeetsContract w p ins (freshInsertContract w e u v internal))
    (hd : ∀ e, MeetsContract w p del (freshDeleteContract w e internal)) :
    MeetsContract w p base (freshRecordContract w record internal) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨src, fwd, inv, counter, heap, rfl, hpre⟩ := hpre
  cases record with
  | split _ _ _ => cases hpre
  | delete e =>
    have hp' : (freshDeleteContract w e internal).pre [src, fwd, heap] mem := hpre
    obtain ⟨⟨src', fwd', heap', hargs, _, _, _, hrecord, _⟩, _, _⟩ := hp'
    simp only [List.cons.injEq, and_true] at hargs
    rcases hargs with ⟨rfl, rfl, rfl⟩
    have htag : mem src = 1 := by
      simpa [updateWords] using hrecord 0 (by simp [updateWords])
    have hws : ∀ x ∈ [src, fwd, heap], x < 2 ^ w := by
      intro x hx
      apply hwords x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    let st := startState [src, fwd, inv, counter, heap] mem pos
    let Q : Outcome → State → Prop := fun o sf =>
      (freshDeleteContract w e internal).post [src, fwd, heap] mem o.value sf.mem
    have ht : Triple w p (fun sf => sf = st ∧ (1 : ℕ) ≠ 0)
        (.call 8 del [.reg 0, .reg 1, .reg 4] ;; .ret (.reg 8)) Q (fun _ => 124) := by
      intro sf tape ⟨hs, _⟩
      subst sf
      apply runs_start_le
      refine runs_seq_call_le (hd e) (vs := [src, fwd, heap]) (by rfl) hws hpre ?_
      intro v mem' pos' hout
      refine runs_ret_le (v := v) (by eval_expr) hout ?_
      change 0 + 3 + 32 + 2 + 2 ≤ 124
      decide
    have hf : Triple w p (fun sf => sf = st ∧ (1 : ℕ) = 0)
        (.assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
          .assign 6 (.load (.bin .add (.reg 0) (.const 2))) ;;
          .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
          .call 8 ins [.reg 5, .reg 6, .reg 7, .reg 1, .reg 2, .reg 3, .reg 4] ;;
          .ret (.reg 8)) Q (fun _ => 124) := by
      intro _ _ hs
      exact False.elim (Nat.one_ne_zero hs.2)
    have htest : ∀ sf, sf = st → (Expr.load (.reg 0)).eval w sf = some 1 := by
      intro sf hs
      subst sf
      exact congrArg some htag
    obtain ⟨o, sf, c, hr, hpost, hcost⟩ :=
      (Triple.cond_const (val := fun _ => 1) htest ht hf) st ω rfl
    refine ⟨o, sf, c, hr, hpost, ?_⟩
    simp only [Expr.size_load, Expr.size_reg, max_self] at hcost
    change c ≤ 128
    omega
  | insert e u v =>
    obtain ⟨hs, hrecord, he, hu, hv, hcall⟩ := hpre
    have hroom : heap + 4 < 2 ^ w := by
      obtain ⟨_, _, _, _, heq, _, _, hh, _⟩ := hcall
      simp only [List.cons.injEq, and_true, true_and] at heq
      rcases heq with ⟨_, _, _, _, _, _, rfl⟩
      exact hh
    have haddr1 : src + 1 < 2 ^ w := by omega
    have haddr2 : src + 2 < 2 ^ w := by omega
    have haddr3 : src + 3 < 2 ^ w := by omega
    have htag : mem src = 0 := by simpa [updateWords] using hrecord 0 (by simp [updateWords])
    have he' : mem (src + 1) = e := hrecord 1 (by simp [updateWords])
    have hu' : mem (src + 2) = u := hrecord 2 (by simp [updateWords])
    have hv' : mem (src + 3) = v := hrecord 3 (by simp [updateWords])
    have hfwd := hwords fwd (by simp)
    have hinv := hwords inv (by simp)
    have hcounter := hwords counter (by simp)
    have hheap := hwords heap (by simp)
    have hws : ∀ x ∈ [e, u, v, fwd, inv, counter, heap], x < 2 ^ w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨he, hu, hv, hfwd, hinv, hcounter, hheap⟩
    let st := startState [src, fwd, inv, counter, heap] mem pos
    let Q : Outcome → State → Prop := fun o sf =>
      (freshInsertContract w e u v internal).post [e, u, v, fwd, inv, counter, heap] mem o.value sf.mem
    have ht : Triple w p (fun sf => sf = st ∧ (0 : ℕ) ≠ 0)
        (.call 8 del [.reg 0, .reg 1, .reg 4] ;; .ret (.reg 8)) Q (fun _ => 124) := by
      intro _ _ hs
      exact False.elim (hs.2 rfl)
    have hf : Triple w p (fun sf => sf = st ∧ (0 : ℕ) = 0)
        (.assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
          .assign 6 (.load (.bin .add (.reg 0) (.const 2))) ;;
          .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
          .call 8 ins [.reg 5, .reg 6, .reg 7, .reg 1, .reg 2, .reg 3, .reg 4] ;;
          .ret (.reg 8)) Q (fun _ => 124) := by
      intro sf tape ⟨heq, _⟩
      subst sf
      apply runs_start_le
      refine runs_seq_assign_le (v := e) (by eval_expr) ?_
      refine runs_seq_assign_le (v := u) (by eval_expr) ?_
      refine runs_seq_assign_le (v := v) (by eval_expr) ?_
      refine runs_seq_call_le (hi e u v) (vs := [e, u, v, fwd, inv, counter, heap])
        (by eval_expr) hws hcall ?_
      intro ret mem' pos' hout
      refine runs_ret_le (v := ret) (by eval_expr) hout ?_
      change 0 + 4 + 2 + 4 + 2 + 4 + 2 + 7 + 64 + 2 + 2 ≤ 124
      decide
    have htest : ∀ sf, sf = st → (Expr.load (.reg 0)).eval w sf = some 0 := by
      intro sf hh
      subst sf
      exact congrArg some htag
    obtain ⟨o, sf, c, hr, hpost, hcost⟩ :=
      (Triple.cond_const (val := fun _ => 0) htest ht hf) st ω rfl
    refine ⟨o, sf, c, hr, hpost, ?_⟩
    simp only [Expr.size_load, Expr.size_reg, max_self] at hcost
    change c ≤ 128
    omega

end MinCostFlow.MinRatio
