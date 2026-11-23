module

public import MinCostFlow.Scaling.LabelPopProgram
public import MinCostFlow.Scaling.LabelVisitProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The complete conditional label-propagation step

An empty pending list stops the step. Otherwise a reached head causes a
pending pop, and an unseen head causes the proved visit operation. This
procedure computes exactly `LabelState.step.1`. Its cost is bounded by
one hundred times the model's step counter plus 1000. Copied outgoing
entries are paid for by their removal from adjacency storage, giving an
amortized allocation bound for the traversal loop.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,stateBase,heap]`. -/
def labelStepBody (pop visit : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 1) (.const 1))) (.const 0)) (.ret (.reg 2))
    (.assign 3 (.load (.reg 1)) ;;
     .assign 4 (.load (.reg 3)) ;;
     .assign 5 (.load (.reg 0)) ;;
     .assign 6 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 5) (.reg 4))) ;;
     .assign 7 (.load (.bin .add (.reg 6) (.const 1))) ;;
     .assign 8 (.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 2) (.reg 5))) ;;
     .cond (.load (.bin .add (.reg 8) (.reg 7)))
       (.call 9 pop [.reg 1, .reg 2] ;; .ret (.reg 9))
       (.call 9 visit [.reg 0, .reg 1, .reg 4, .reg 2] ;; .ret (.reg 9)))

/-- Conditional dispatch, pending pop, and new-vertex visit. -/
def labelStepModule (b : ℕ) : List Stmt :=
  labelStepBody (b+1) (b+3) :: (labelPopModule (b+1) ++ labelVisitModule (b+3))

/-- Local numeric budgets cover all possible pending edges and loaded lists.
The allocation postcondition credits removed adjacency entries. -/
def labelStepContract (w : ℕ) {J : Circulation} (s : Circulation.LabelState J) : Contract where
  pre args mem := ∃ a base heap, args = [a, base, heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length ≤ base ∧ LabelStateAt mem base heap s ∧ labelNodes J.n base ≤ heap ∧
    J.m < 2 ^ w ∧ s.pending.length+J.adjacencyMass s.outgoing+1 < 2 ^ w ∧
    (∀ e ∈ s.pending, (s.labels (J.tail e)).natAbs+(J.cost e).natAbs < 2 ^ w) ∧
    ZeroFrom mem heap ∧ heap+2+2*J.adjacencyMass s.outgoing < 2 ^ w
  post args mem ret mem' := heapArg args ≤ ret ∧
    ret+2*J.adjacencyMass s.step.1.outgoing ≤ heapArg args+2*J.adjacencyMass s.outgoing+2 ∧
    LabelStateAt mem' (args.getD 1 0) ret s.step.1 ∧ ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x < args.getD 1 0 ∨ labelNodes J.n (args.getD 1 0) ≤ x → mem' x = mem x
  cost _ _ := 100*s.step.2+1000

private theorem flag_true_of_nonzero (flag : Bool) (h : flag.toNat ≠ 0) : flag = true := by
  cases flag <;> simp_all

private theorem flag_false_of_zero (flag : Bool) (h : flag.toNat = 0) : flag = false := by
  cases flag <;> simp_all

/-- Every branch and called procedure has no random instruction. -/
theorem labelStepModule_noRand (b : ℕ) : ∀ body ∈ labelStepModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [labelStepBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact labelPopModule_noRand _ body hb
    · exact labelVisitModule_noRand _ body hb

/-- The machine computes the complete model step, with a cost bound paid
by its model counter and an amortized bound on fresh node allocation. -/
theorem labelStep_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (labelStepModule b)) {J : Circulation} (s : Circulation.LabelState J) :
    MeetsContract w p b (labelStepContract w s) := by
  have htail := hasAt_tail hp
  have hpop := hasAt_append_left htail
  have hvisit : p.HasAt (b+3) (labelVisitModule (b+3)) := by
    have h := hasAt_append_right htail
    simpa only [labelPopModule, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, base, heap, rfl, hat, hend, hstate, hnodesEnd, hm, hlengths, hlabelsBudget, hzero, hspace⟩ := hpre
  have hstate0 := hstate
  obtain ⟨ptr, hheader, hpending, _, hseenTable, _⟩ := hstate
  have hnodeBound : base+3+5*J.n ≤ heap := hnodesEnd
  have hheap : heap < 2 ^ w := by omega
  have hbase : base < 2 ^ w := by omega
  have hbase1 : base+1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hlength : s.pending.length < 2 ^ w := by omega
  have hlenMem : mem (base+1) = s.pending.length := hheader 1 (by change 1 < 2; decide)
  cases hpend : s.pending with
  | nil =>
    have hlenZero : mem (base+1) = 0 := by simpa only [hpend, List.length_nil] using hlenMem
    apply runs_start_le
    unfold labelStepBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change heap ≤ heap ∧ heap+2*J.adjacencyMass s.step.1.outgoing ≤ heap+2*J.adjacencyMass s.outgoing+2 ∧
          LabelStateAt mem base heap s.step.1 ∧ ZeroFrom mem heap ∧
          ∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → mem x = mem x
        simp only [Circulation.LabelState.step, hpend]
        exact ⟨le_rfl, by omega, hstate0, hzero, fun _ _ _ => True.intro⟩
      · simp only [labelStepContract, Circulation.LabelState.step, hpend,
          Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]; omega
    · simp [startState, hlenZero] at hcond
  | cons e rest =>
    have hkP := labelPop_meetsContract (w := w) hpop s e rest
    have hkV := labelVisit_meetsContract (w := w) hvisit s e rest
    have heMem : e ∈ s.pending := by rw [hpend]; exact List.mem_cons_self
    have hsum := hlabelsBudget e heMem
    let record := a+2+5*e.val
    let seen := labelSeen J.n base
    let entries := s.outgoing (J.head e)
    have hentriesMass : entries.length ≤ J.adjacencyMass s.outgoing :=
      Finset.single_le_sum (fun v _ => Nat.zero_le (s.outgoing v).length) (Finset.mem_univ (J.head e))
    have hrecordEnd : record+5 ≤ base := by
      have he := e.isLt
      rw [J.solverWords_length] at hend
      dsimp [record]
      omega
    have hNMem := (solver_header_at J hat).1
    have hrecordAt := solver_edge_at J hat e
    have hheadMem : mem (record+1) = (J.head e).val := by
      simpa only [Circulation.solverEdgeWords, List.getElem_cons_succ, List.getElem_cons_zero] using
        hrecordAt 1 (by change 1 < 5; decide)
    have hptrMem : mem base = ptr := by
      have h := hheader 0 (by change 0 < 2; decide)
      change mem (base+0) = ptr at h
      simpa only [Nat.add_zero] using h
    have hpending' : IndexListAt mem (labelNodes J.n base) heap ptr (e :: rest) := by rwa [hpend] at hpending
    obtain ⟨_, _, hptrEnd, hedgeMem, _, _, _⟩ := indexListAt_cons_iff.mp hpending'
    have hflagMem : mem (seen+(J.head e).val) = (s.seen (J.head e)).toNat := hseenTable (J.head e)
    have hhead := (J.head e).isLt
    have hn : J.n < 2 ^ w := by omega
    have heWord : e.val < 2 ^ w := e.isLt.trans hm
    have hheadWord : (J.head e).val < 2 ^ w := by omega
    have hptr : ptr < 2 ^ w := by omega
    have hrecord : record < 2 ^ w := by omega
    have hrecord1 : record+1 < 2 ^ w := by omega
    have ha : a < 2 ^ w := by rw [J.solverWords_length] at hend; omega
    have ha2 : a+2 < 2 ^ w := by rw [J.solverWords_length] at hend; omega
    have h5e : 5*e.val < 2 ^ w := by dsimp [record] at hrecordEnd; omega
    have hbase2 : base+2 < 2 ^ w := by omega
    have h2n : 2*J.n < 2 ^ w := by omega
    have hseen : seen < 2 ^ w := by dsimp [seen, labelSeen]; omega
    have hseenCalc : base+2+2*J.n < 2 ^ w := hseen
    have hflag : seen+(J.head e).val < 2 ^ w := by dsimp [seen, labelSeen]; omega
    have htwo : 2 < 2 ^ w := by omega
    have hfive : 5 < 2 ^ w := by omega
    apply runs_start_le
    unfold labelStepBody
    wram_step
    · simp [startState, hlenMem, hpend] at hcond
    · refine runs_seq_assign_le (v := ptr) (by eval_expr) ?_
      refine runs_seq_assign_le (v := e.val) (by eval_expr) ?_
      refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
      refine runs_seq_assign_le (v := record) (by eval_expr) ?_
      refine runs_seq_assign_le (v := (J.head e).val) (by eval_expr) ?_
      refine runs_seq_assign_le (v := seen) (by change _ = some (base+2+2*J.n); eval_expr) ?_
      wram_step
      · have hnonzero : (s.seen (J.head e)).toNat ≠ 0 := by simpa [startState, hflagMem] using hcond
        have hseenTrue := flag_true_of_nonzero _ hnonzero
        refine runs_seq_call_le hkP (vs := [base, heap]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨base, heap, rfl, hstate0, hpend, hnodesEnd, hlength, hzero, hheap⟩
        · intro ret memP posP hpostP
          obtain ⟨hret, hstateP, hzeroP, hframeP⟩ := hpostP
          change ret = heap at hret
          change LabelStateAt memP base ret { s with pending := rest } at hstateP
          change (∀ x, x < base ∨ base+2 ≤ x → memP x = mem x) at hframeP
          have hretWord : ret < 2 ^ w := by omega
          have hmass : J.adjacencyMass s.step.1.outgoing = J.adjacencyMass s.outgoing := by
            simp only [Circulation.LabelState.step, hpend, hseenTrue, ↓reduceIte]
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change heap ≤ ret ∧ ret+2*J.adjacencyMass s.step.1.outgoing ≤ heap+2*J.adjacencyMass s.outgoing+2 ∧
              LabelStateAt memP base ret s.step.1 ∧ ZeroFrom memP ret ∧
              ∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → memP x = mem x
            refine ⟨by omega, by rw [hmass]; omega, ?_, hzeroP, ?_⟩
            · simpa only [Circulation.LabelState.step, hpend, hseenTrue, ↓reduceIte] using hstateP
            · intro x _ hxout
              apply hframeP
              rcases hxout with hxout | hxout
              · exact Or.inl hxout
              · exact Or.inr (by dsimp [labelNodes] at hxout; omega)
          · simp only [labelStepContract, labelPopContract, Circulation.LabelState.step,
              hpend, hseenTrue, ↓reduceIte, argsSize_cons, argsSize_nil, Expr.size_bin,
              Expr.size_load, Expr.size_reg, Expr.size_const]; omega
      · have hzeroFlag : (s.seen (J.head e)).toNat = 0 := by simpa [startState, hflagMem] using hcond
        have hseenFalse := flag_false_of_zero _ hzeroFlag
        have hentryBudget : entries.length+s.pending.length < 2 ^ w := by omega
        have hentrySpace : heap+2+2*entries.length < 2 ^ w := by omega
        refine runs_seq_call_le hkV (vs := [a, base, e.val, heap]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨a, base, heap, rfl, hat, hend, hstate0, hpend, hseenFalse, hnodesEnd,
            hm, hsum, hentryBudget, hzero, hentrySpace⟩
        · intro ret memV posV hpostV
          obtain ⟨hret, hstateV, hzeroV, hframeV⟩ := hpostV
          change ret = heap+2+2*entries.length at hret
          change LabelStateAt memV base ret s.step.1 at hstateV
          change (∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → memV x = mem x) at hframeV
          have hretWord : ret < 2 ^ w := by omega
          have hmass : J.adjacencyMass s.step.1.outgoing+entries.length = J.adjacencyMass s.outgoing := by
            have h := J.adjacencyMass_update s.outgoing (J.head e) []
            simpa only [Circulation.LabelState.step, hpend, hseenFalse, Bool.false_eq_true,
              ↓reduceIte, List.length_nil, Nat.add_zero] using h
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change heap ≤ ret ∧ ret+2*J.adjacencyMass s.step.1.outgoing ≤ heap+2*J.adjacencyMass s.outgoing+2 ∧
              LabelStateAt memV base ret s.step.1 ∧ ZeroFrom memV ret ∧
              ∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → memV x = mem x
            exact ⟨by omega, by omega, hstateV, hzeroV, hframeV⟩
          · simp only [labelStepContract, labelVisitContract, Circulation.LabelState.step,
              hpend, hseenFalse, Bool.false_eq_true, ↓reduceIte, argsSize_cons, argsSize_nil,
              Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]
            change _ ≤ 100*(12+2*entries.length)+1000
            have hentries : (s.outgoing (J.head e)).length = entries.length := rfl
            omega

end MinCostFlow.Scaling.Machine
