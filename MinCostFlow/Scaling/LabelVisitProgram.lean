module

public import MinCostFlow.Scaling.LabelAssignProgram
public import MinCostFlow.Scaling.LabelLoadOutgoingProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# The newly reached vertex branch of label propagation

For a pending edge whose head is unseen, the model assigns its label,
marks it reached, loads its outgoing entries before the pending tail, and
clears its outgoing head. This procedure composes the two proved state
updates. Its result is exactly `LabelState.step.1` in that branch, at cost
at most `100*loadedCount+800` and with `2+2*loadedCount` fresh words.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,stateBase,edgeIndex,heap]`. -/
def labelVisitBody (assign load : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 5) (.reg 2))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .call 7 assign [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 8 load [.reg 1, .reg 4, .reg 6, .reg 7] ;; .ret (.reg 8)

/-- Label assignment followed by pending-list loading and outgoing clearing. -/
def labelVisitModule (b : ℕ) : List Stmt :=
  labelVisitBody (b+1) (b+7) :: (labelAssignModule (b+1) ++ labelLoadOutgoingModule (b+7))

/-- The branch's pending edge has an unseen head. Local numeric budgets
cover its label difference, lengths, and copied immutable nodes. -/
def labelVisitContract (w : ℕ) {J : Circulation} (s : Circulation.LabelState J)
    (e : Fin J.m) (rest : List (Fin J.m)) : Contract where
  pre args mem := ∃ a base heap, args = [a, base, e.val, heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length ≤ base ∧ LabelStateAt mem base heap s ∧
    s.pending = e :: rest ∧ s.seen (J.head e) = false ∧ labelNodes J.n base ≤ heap ∧ J.m < 2 ^ w ∧
    (s.labels (J.tail e)).natAbs+(J.cost e).natAbs < 2 ^ w ∧
    (s.outgoing (J.head e)).length+s.pending.length < 2 ^ w ∧ ZeroFrom mem heap ∧
    heap+2+2*(s.outgoing (J.head e)).length < 2 ^ w
  post args mem ret mem' := ret = heapArg args+2+2*(s.outgoing (J.head e)).length ∧
    LabelStateAt mem' (args.getD 1 0) ret s.step.1 ∧ ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x < args.getD 1 0 ∨ labelNodes J.n (args.getD 1 0) ≤ x → mem' x = mem x
  cost _ _ := 100*(s.outgoing (J.head e)).length+800

/-- A newly reached vertex is processed without random instructions. -/
theorem labelVisitModule_noRand (b : ℕ) : ∀ body ∈ labelVisitModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [labelVisitBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact labelAssignModule_noRand _ body hb
    · exact labelLoadOutgoingModule_noRand _ body hb

/-- The composed machine procedure computes precisely the new-vertex
branch of the model step, with exact allocation and a linear load cost. -/
theorem labelVisit_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (labelVisitModule b)) {J : Circulation} (s : Circulation.LabelState J)
    (e : Fin J.m) (rest : List (Fin J.m)) : MeetsContract w p b (labelVisitContract w s e rest) := by
  have htail := hasAt_tail hp
  have hassign := hasAt_append_left htail
  have hload : p.HasAt (b+7) (labelLoadOutgoingModule (b+7)) := by
    have h := hasAt_append_right htail
    simpa only [labelAssignModule, signedSubtractModule, signedAddModule, wordPairModule,
      boolTableSetModule, List.length_cons, List.length_nil, List.length_append,
      Nat.reduceAdd, Nat.add_assoc] using h
  let assigned : Circulation.LabelState J :=
    { s with labels := Function.update s.labels (J.head e) (s.labels (J.tail e)-J.cost e)
             seen := Function.update s.seen (J.head e) true }
  let entries := s.outgoing (J.head e)
  have hentries : (assigned.outgoing (J.head e)).length = entries.length := rfl
  have hkA := labelAssign_meetsContract (w := w) hassign s e
  have hkL := labelLoadOutgoing_meetsContract (w := w) hload assigned e rest (J.head e)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, base, heap, rfl, hat, hend, hstate, hnonempty, hunseen, hnodesEnd, hm,
    hsum, hbudget, hzero, hspace⟩ := hpre
  change heap+2+2*entries.length < 2 ^ w at hspace
  let record := a+2+5*e.val
  let nodes := labelNodes J.n base
  let heads := labelHeads J.n base
  let labels := labelLabels base
  let seen := labelSeen J.n base
  have hnodeBound : base+3+5*J.n ≤ heap := hnodesEnd
  have hheadEnd : heads+2*J.n+1 = nodes := by dsimp [heads, nodes, labelHeads, labelNodes]; omega
  have hseenEnd : seen+J.n = heads := by dsimp [seen, heads, labelSeen, labelHeads]; omega
  have hlabelEnd : labels+2*J.n = seen := rfl
  have hh := (J.head e).isLt
  have he := e.isLt
  have hrecordEnd : record+5 ≤ base := by
    rw [J.solverWords_length] at hend
    dsimp [record]
    omega
  have hnMem := (solver_header_at J hat).1
  have hheadRecord := solver_edge_at J hat e
  have hheadMem : mem (record+1) = (J.head e).val := by
    simpa only [Circulation.solverEdgeWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hheadRecord 1 (by change 1 < 5; decide)
  have hheap : heap < 2 ^ w := by omega
  have hheap2 : heap+2 < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := by omega
  have heWord : e.val < 2 ^ w := he.trans hm
  have hhWord : (J.head e).val < 2 ^ w := by omega
  have hbase : base < 2 ^ w := by omega
  have ha : a < 2 ^ w := by rw [J.solverWords_length] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [J.solverWords_length] at hend; omega
  have h5e : 5*e.val < 2 ^ w := by dsimp [record] at hrecordEnd; omega
  have hrecord : record < 2 ^ w := by omega
  have hrecord1 : record+1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by omega
  apply runs_start_le
  unfold labelVisitBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := record) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (J.head e).val) (by eval_expr) ?_
  refine runs_seq_call_le hkA (vs := [a, base, e.val, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a, base, heap, rfl, hat, hend, hstate, hnodesEnd, hsum, hzero, hheap2⟩
  · intro next memA posA hpostA
    obtain ⟨hnext, hstateA, hzeroA, hframeA⟩ := hpostA
    change next = heap+2 at hnext
    change LabelStateAt memA base next assigned at hstateA
    change (∀ x < heap, x ≠ labels+2*(J.head e).val → x ≠ labels+2*(J.head e).val+1 →
      x ≠ seen+(J.head e).val → memA x = mem x) at hframeA
    have hnextWord : next < 2 ^ w := by omega
    refine runs_seq_call_le hkL (vs := [base, J.n, (J.head e).val, next]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨base, next, rfl, hstateA, hnonempty, by omega, hm, hbudget, hzeroA, ?_⟩
      change next+2*entries.length < 2 ^ w
      omega
    · intro ret memL posL hpostL
      obtain ⟨hret, hstateL, hzeroL, hframeL⟩ := hpostL
      change ret = next+2*entries.length at hret
      change LabelStateAt memL base ret
        { assigned with outgoing := Function.update s.outgoing (J.head e) [], pending := entries ++ rest } at hstateL
      change (∀ x < next, (x < base ∨ base+2 ≤ x) →
        (x < heads+2*(J.head e).val ∨ heads+2*(J.head e).val+2 ≤ x) → memL x = memA x) at hframeL
      have hretWord : ret < 2 ^ w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change ret = heap+2+2*entries.length ∧ LabelStateAt memL base ret s.step.1 ∧
          ZeroFrom memL ret ∧ ∀ x < heap, x < base ∨ nodes ≤ x → memL x = mem x
        refine ⟨by omega, ?_, hzeroL, ?_⟩
        · simpa only [Circulation.LabelState.step, hnonempty, hunseen, Bool.false_eq_true, ↓reduceIte] using hstateL
        · intro x hx hxout
          apply (hframeL x (by omega) ?_ ?_).trans (hframeA x hx ?_ ?_ ?_)
          all_goals
            rcases hxout with hxout | hxout
            · dsimp [heads, labelHeads, labels, labelLabels, seen, labelSeen] at *
              omega
            · change nodes ≤ x at hxout
              dsimp [nodes, labelNodes, heads, labelHeads, labels, labelLabels, seen, labelSeen] at *
              omega
      · simp only [labelVisitContract, labelAssignContract, labelLoadOutgoingContract,
          argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]
        change _ ≤ 100*entries.length+800
        omega

end MinCostFlow.Scaling.Machine
