module

public import MinCostFlow.Scaling.LabelStateLayout
public import MinCostFlow.Scaling.CirculationLayout
public import MinCostFlow.Scaling.SignedSubtractProgram
public import MinCostFlow.Scaling.BoolTableSetProgram
public import MinCostFlow.Scaling.WordPairStoreProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Assigning a reached vertex's label

The new-vertex branch of label propagation assigns the parent's label
minus the traversed edge cost, then marks the child as reached. This
procedure reads the indexed graph record and signed parent label, computes
that exact difference, updates the child label and flag, and preserves the
pending and outgoing lists. It uses two scratch words and costs at most 400.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,stateBase,edgeIndex,heap]`. -/
def labelAssignBody (subtract pair flags : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 5) (.reg 2))) ;;
  .assign 6 (.load (.reg 5)) ;;
  .assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .assign 8 (.bin .add (.reg 1) (.const 2)) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 4))) ;;
  .assign 10 (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 7))) ;;
  .call 11 subtract [.load (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 6))),
    .load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 6))) (.const 1)),
    .load (.bin .add (.reg 5) (.const 3)), .load (.bin .add (.reg 5) (.const 4)), .reg 3] ;;
  .call 12 pair [.load (.reg 3), .load (.bin .add (.reg 3) (.const 1)), .reg 10] ;;
  .call 13 flags [.reg 9, .reg 7, .const 1] ;;
  .ret (.reg 11)

/-- Signed subtraction, in-place pair writing, and one visited-flag store. -/
def labelAssignModule (b : ℕ) : List Stmt :=
  labelAssignBody (b+1) (b+4) (b+5) ::
    (signedSubtractModule (b+1) ++ wordPairModule ++ boolTableSetModule)

/-- The original graph precedes the state. The only arithmetic budget is
the sum of the parent-label and edge-cost magnitudes. -/
def labelAssignContract (w : ℕ) {J : Circulation} (s : Circulation.LabelState J) (e : Fin J.m) : Contract where
  pre args mem := ∃ a base heap, args = [a, base, e.val, heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length ≤ base ∧ LabelStateAt mem base heap s ∧ labelNodes J.n base ≤ heap ∧
    (s.labels (J.tail e)).natAbs+(J.cost e).natAbs < 2 ^ w ∧ ZeroFrom mem heap ∧ heap+2 < 2 ^ w
  post args mem ret mem' := ret = heapArg args+2 ∧
    LabelStateAt mem' (args.getD 1 0) ret
      { s with labels := Function.update s.labels (J.head e) (s.labels (J.tail e)-J.cost e)
               seen := Function.update s.seen (J.head e) true } ∧ ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x ≠ labelLabels (args.getD 1 0)+2*(J.head e).val →
      x ≠ labelLabels (args.getD 1 0)+2*(J.head e).val+1 →
      x ≠ labelSeen J.n (args.getD 1 0)+(J.head e).val → mem' x = mem x
  cost _ _ := 400

/-- Label assignment and every called procedure are deterministic. -/
theorem labelAssignModule_noRand (b : ℕ) : ∀ body ∈ labelAssignModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [labelAssignBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact signedSubtractModule_noRand _ body hb
      · have he : body = wordPairBody := by simpa only [wordPairModule, List.mem_singleton] using hb
        subst body
        exact wordPairBody_noRand
    · have he : body = boolTableSetBody := by simpa only [boolTableSetModule, List.mem_singleton] using hb
      subst body
      exact boolTableSetBody_noRand

/-- The machine assigns the exact child label and reached flag while
preserving all other fields of the traversal state. -/
theorem labelAssign_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (labelAssignModule b)) {J : Circulation} (s : Circulation.LabelState J) (e : Fin J.m) :
    MeetsContract w p b (labelAssignContract w s e) := by
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hsub := hasAt_append_left hleft
  have hpair : p.HasAt (b+4) wordPairModule := by
    have h := hasAt_append_right hleft
    simpa only [signedSubtractModule, signedAddModule, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.add_assoc] using h
  have hflags : p.HasAt (b+5) boolTableSetModule := by
    have h := hasAt_append_right htail
    simpa only [List.length_append, signedSubtractModule, signedAddModule, wordPairModule,
      List.length_cons, List.length_nil, Nat.reduceAdd, ← Nat.add_assoc] using h
  have hkS := signedSubtract_meetsContract (w := w) hsub (s.labels (J.tail e)) (J.cost e)
  have hkP := wordPairStore_meetsContract (w := w) hpair
  have hkF := boolTableSet_meetsContract (w := w) hflags s.seen (J.head e) true
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, base, heap, rfl, hat, hend, hstate, hnodesEnd, hsum, hzero, hspace⟩ := hpre
  have hstate0 := hstate
  obtain ⟨_, _, _, hlabels, hseen, _⟩ := hstate
  let labels := labelLabels base
  let seen := labelSeen J.n base
  let heads := labelHeads J.n base
  let nodes := labelNodes J.n base
  let record := a+2+5*e.val
  let child := labels+2*(J.head e).val
  let value := s.labels (J.tail e)-J.cost e
  have hnodeBound : base+3+5*J.n ≤ heap := hnodesEnd
  change nodes ≤ heap at hnodesEnd
  have hlabelEnd : labels+2*J.n = seen := rfl
  have hseenEnd : seen+J.n = heads := by dsimp [seen, heads, labelSeen, labelHeads]; omega
  have hheadEnd : heads+2*J.n+1 = nodes := by dsimp [heads, nodes, labelHeads, labelNodes]; omega
  have ht := (J.tail e).isLt
  have hh := (J.head e).isLt
  have he := e.isLt
  have hchildEnd : child+2 ≤ seen := by dsimp [child]; omega
  have hflagEnd : seen+(J.head e).val < heads := by omega
  have hrecordEnd : record+5 ≤ base := by
    rw [J.solverWords_length] at hend
    dsimp [record]
    omega
  have hedge := solver_edge_at J hat e
  have hfields : ∀ j : Fin 5, mem (record+j.val) = (J.solverEdgeWords e).getD j.val 0 := by
    intro j
    rw [List.getD_eq_getElem _ _ (show j.val < (J.solverEdgeWords e).length from j.isLt)]
    exact hedge _ j.isLt
  have htailMem := hfields ⟨0, by decide⟩
  have hheadMem := hfields ⟨1, by decide⟩
  have hcostSign := hfields ⟨3, by decide⟩
  have hcostMag := hfields ⟨4, by decide⟩
  simp only [Circulation.solverEdgeWords, List.getD_cons_succ, List.getD_cons_zero,
    Nat.add_zero] at htailMem hheadMem hcostSign hcostMag
  have hnMem := (solver_header_at J hat).1
  have hparent := hlabels (J.tail e)
  have hparentSign : mem (labels+2*(J.tail e).val) = if s.labels (J.tail e) < 0 then 1 else 0 := by
    simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hparent 0 (by change 0 < 2; decide)
  have hparentMag : mem (labels+2*(J.tail e).val+1) = (s.labels (J.tail e)).natAbs := by
    simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using hparent 1 (by change 1 < 2; decide)
  have hheap : heap < 2 ^ w := by omega
  have hheap1 : heap+1 < 2 ^ w := by omega
  have hbase : base < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := by omega
  have heWord : e.val < 2 ^ w := hwords _ (by simp)
  have hrecord : record < 2 ^ w := by omega
  have hrecord1 : record+1 < 2 ^ w := by omega
  have hrecord3 : record+3 < 2 ^ w := by omega
  have hrecord4 : record+4 < 2 ^ w := by omega
  have ha : a < 2 ^ w := by rw [J.solverWords_length] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [J.solverWords_length] at hend; omega
  have h5e : 5*e.val < 2 ^ w := by dsimp [record] at hrecord; omega
  have hlabelsWord : labels < 2 ^ w := by change base+2 < 2 ^ w; omega
  have hbase2 : base+2 < 2 ^ w := hlabelsWord
  have hseenWord : seen < 2 ^ w := by change base+2+2*J.n < 2 ^ w; omega
  have h2n : 2*J.n < 2 ^ w := by omega
  have htWord : (J.tail e).val < 2 ^ w := by omega
  have hhWord : (J.head e).val < 2 ^ w := by omega
  have ht2 : 2*(J.tail e).val < 2 ^ w := by omega
  have hh2 : 2*(J.head e).val < 2 ^ w := by omega
  have hparentAddr : labels+2*(J.tail e).val < 2 ^ w := by omega
  have hparentAddr1 : labels+2*(J.tail e).val+1 < 2 ^ w := by omega
  have hchild : child < 2 ^ w := by omega
  have hchild2 : child+2 < 2 ^ w := by omega
  have hparentWord : (s.labels (J.tail e)).natAbs < 2 ^ w := by omega
  have hcostWord : (J.cost e).natAbs < 2 ^ w := by omega
  have hparentSignWord : (if s.labels (J.tail e) < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hcostSignWord : (if J.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hvalueWord : value.natAbs < 2 ^ w := (Int.natAbs_sub_le _ _).trans_lt hsum
  have hvalueSign : (if value < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hthree : 3 < 2 ^ w := by omega
  have hfour : 4 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by omega
  have hseenCalc : labels+2*J.n < 2 ^ w := by rw [hlabelEnd]; exact hseenWord
  apply runs_start_le
  unfold labelAssignBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := record) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (J.tail e).val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (J.head e).val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := labels) (by change _ = some (base+2); eval_expr) ?_
  refine runs_seq_assign_le (v := seen) (by change _ = some (labels+2*J.n); eval_expr) ?_
  refine runs_seq_assign_le (v := child) (by eval_expr) ?_
  refine runs_seq_call_le hkS
    (vs := [if s.labels (J.tail e) < 0 then 1 else 0, (s.labels (J.tail e)).natAbs,
      if J.cost e < 0 then 1 else 0, (J.cost e).natAbs, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hsum⟩, hzero, hspace⟩
  · intro next memS posS hpostS
    obtain ⟨⟨_, _, hframeS, hzeroS, hvalueS⟩, hnext⟩ := hpostS
    change next = heap+2 at hnext
    change (∀ x < heap, memS x = mem x) at hframeS
    change ZeroFrom memS next at hzeroS
    change ListAt memS heap (encodeInt value) at hvalueS
    have hsignMem : memS heap = if value < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hvalueS 0 (by change 0 < 2; decide)
    have hmagMem : memS (heap+1) = value.natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using hvalueS 1 (by change 1 < 2; decide)
    have hnextWord : next < 2 ^ w := by omega
    have hlabelsS : SignedTableAt memS labels s.labels := hlabels.of_agree_below (by omega) hframeS
    have hseenS : BoolTableAt memS seen s.seen := hseen.of_agree_below (by omega) hframeS
    refine runs_seq_call_le hkP (vs := [if value < 0 then 1 else 0, value.natAbs, child]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨_, _, _, rfl, hchild2⟩
    · intro _ memP posP hpostP
      obtain ⟨_, hpairP, hframeP⟩ := hpostP
      change ListAt memP child (encodeInt value) at hpairP
      change (∀ x, x < child ∨ child+2 ≤ x → memP x = memS x) at hframeP
      have hlabelsP : SignedTableAt memP labels (Function.update s.labels (J.head e) value) := by
        apply hlabelsS.update (J.head e) value (heap := heap) (by omega) hpairP
        intro x _ hx0 hx1
        apply hframeP
        omega
      have hseenP : BoolTableAt memP seen s.seen := by
        apply hseenS.of_agree
        intro x hx _
        exact hframeP x (Or.inr (by omega))
      have hseenSpace : seen+J.n < 2 ^ w := by omega
      refine runs_seq_call_le hkF (vs := [seen, (J.head e).val, 1]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨seen, rfl, hseenP, hseenSpace⟩
      · intro _ memF posF hpostF
        obtain ⟨_, hseenF, hframeF⟩ := hpostF
        change BoolTableAt memF seen (Function.update s.seen (J.head e) true) at hseenF
        change (∀ x, x ≠ seen+(J.head e).val → memF x = memP x) at hframeF
        have hlabelsF : SignedTableAt memF labels (Function.update s.labels (J.head e) value) := by
          apply hlabelsP.of_agree
          intro x _ hx
          exact hframeF x (by omega)
        have hframe : ∀ x < heap, x ≠ child → x ≠ child+1 →
            x ≠ seen+(J.head e).val → memF x = mem x := by
          intro x hx hx0 hx1 hxflag
          apply (hframeF x hxflag).trans
          apply (hframeP x ?_).trans (hframeS x hx)
          omega
        have hstateF : LabelStateAt memF base next
            { s with labels := Function.update s.labels (J.head e) value
                     seen := Function.update s.seen (J.head e) true } := by
          refine hstate0.with_labels_seen _ _ (by omega) hlabelsF hseenF ?_ ?_ ?_
          · intro x hx hxend
            apply hframe x (by omega)
            all_goals dsimp [child, labels, labelLabels, seen, labelSeen]; omega
          · intro x hx hxend
            apply hframe x (by rw [← hheadEnd] at hnodesEnd; omega)
            all_goals change heads ≤ x at hx; omega
          · intro x hx hxend
            apply hframe x hxend
            all_goals change nodes ≤ x at hx; omega
        refine runs_ret_le (v := next) (by eval_expr) ?_ ?_
        · change next = heap+2 ∧ LabelStateAt memF base next
            { s with labels := Function.update s.labels (J.head e) value
                     seen := Function.update s.seen (J.head e) true } ∧ ZeroFrom memF next ∧
            ∀ x < heap, x ≠ labels+2*(J.head e).val → x ≠ labels+2*(J.head e).val+1 →
              x ≠ seen+(J.head e).val → memF x = mem x
          refine ⟨hnext, hstateF, ?_, hframe⟩
          intro x hx
          apply (hframeF x (by omega)).trans
          exact (hframeP x (Or.inr (by omega))).trans (hzeroS x hx)
        · simp only [labelAssignContract, signedSubtractContract, heapContract, wordPairStoreContract,
            boolTableSetContract, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load,
            Expr.size_reg, Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
