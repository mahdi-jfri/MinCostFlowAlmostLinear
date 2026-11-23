module

public import MinCostFlow.Scaling.LabelStateLayout
public import MinCostFlow.Scaling.IndexListAppendProgram
public import MinCostFlow.Scaling.AdjacencyClearProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.LabelStateWitness
import WordRAM.Tactic

/-!
# Loading a reached vertex's outgoing edges

After a new vertex receives its label, the model replaces pending by its
outgoing list followed by the unprocessed pending tail, then clears that
outgoing head. This procedure copies exactly those outgoing entries,
updates the pending header, and clears the head. Labels and flags remain
unchanged. It allocates two words per loaded entry and has a linear cost.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Write a chosen new pending pointer and length, clear the outgoing head,
and return the heap produced by prefix copying. -/
def labelLoadOutgoingFinish (writer : ℕ) (ptr : Expr) : Stmt :=
  .call 12 writer [ptr, .bin .add (.reg 10) (.bin .sub (.reg 8) (.const 1)), .reg 0] ;;
  .call 13 writer [.const 0, .const 0, .reg 5] ;; .ret (.reg 11)

/-- Arguments `[stateBase,n,vertex,heap]`, for a nonempty pending list. -/
def labelLoadOutgoingBody (append writer : ℕ) : Stmt :=
  .assign 4 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 3) (.reg 1))) ;;
  .assign 5 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 2))) ;;
  .assign 6 (.load (.reg 0)) ;;
  .assign 7 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 9 (.load (.reg 5)) ;;
  .assign 10 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .call 11 append [.reg 9, .reg 7, .reg 10, .reg 3] ;;
  .cond (.bin .eq (.reg 10) (.const 0))
    (labelLoadOutgoingFinish writer (.reg 7)) (labelLoadOutgoingFinish writer (.reg 3))

/-- Loading outgoing entries, immutable prefix copying, and the shared writer. -/
def labelLoadOutgoingModule (b : ℕ) : List Stmt :=
  labelLoadOutgoingBody (b+1) (b+3) :: (indexListAppendModule (b+1) ++ wordPairModule)

/-- Pending is nonempty. The stored lengths' sum and copied prefix fit,
and every saved edge index is a word. -/
def labelLoadOutgoingContract (w : ℕ) {J : Circulation} (s : Circulation.LabelState J)
    (e : Fin J.m) (rest : List (Fin J.m)) (v : Fin J.n) : Contract where
  pre args mem := ∃ base heap, args = [base, J.n, v.val, heap] ∧ LabelStateAt mem base heap s ∧
    s.pending = e :: rest ∧ labelNodes J.n base ≤ heap ∧ J.m < 2 ^ w ∧
    (s.outgoing v).length+s.pending.length < 2 ^ w ∧ ZeroFrom mem heap ∧
    heap+2*(s.outgoing v).length < 2 ^ w
  post args mem ret mem' := ret = heapArg args+2*(s.outgoing v).length ∧
    LabelStateAt mem' (args.getD 0 0) ret
      { s with outgoing := Function.update s.outgoing v [], pending := s.outgoing v ++ rest } ∧
    ZeroFrom mem' ret ∧
    ∀ x < heapArg args, (x < args.getD 0 0 ∨ args.getD 0 0+2 ≤ x) →
      (x < labelHeads J.n (args.getD 0 0)+2*v.val ∨ labelHeads J.n (args.getD 0 0)+2*v.val+2 ≤ x) →
      mem' x = mem x
  cost _ _ := 100*(s.outgoing v).length+240

/-- Loading outgoing entries and all helpers use no random instructions. -/
theorem labelLoadOutgoingModule_noRand (b : ℕ) :
    ∀ body ∈ labelLoadOutgoingModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [labelLoadOutgoingBody, labelLoadOutgoingFinish, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact indexListAppendModule_noRand _ body hb
    · have he : body = wordPairBody := by simpa only [wordPairModule, List.mem_singleton] using hb
      subst body
      exact wordPairBody_noRand

/-- The machine implements exactly the pending append and outgoing clear
of the model's new-vertex branch, preserving its labels and flags. -/
theorem labelLoadOutgoing_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (labelLoadOutgoingModule b)) {J : Circulation} (s : Circulation.LabelState J)
    (e : Fin J.m) (rest : List (Fin J.m)) (v : Fin J.n) :
    MeetsContract w p b (labelLoadOutgoingContract w s e rest v) := by
  have htail := hasAt_tail hp
  have happend := hasAt_append_left htail
  have hpair : p.HasAt (b+3) wordPairModule := by
    have h := hasAt_append_right htail
    simpa only [indexListAppendModule, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  have hkW := wordPairStore_meetsContract (w := w) hpair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, heap, rfl, hstate, hnonempty, hnodesEnd, hm, hbudget, hzero, hspace⟩ := hpre
  obtain ⟨pending, hheader, hpending, hlabels, hseen, hout⟩ := hstate
  rw [hnonempty] at hheader hpending hbudget
  let entries := s.outgoing v
  change heap+2*entries.length < 2 ^ w at hspace
  let heads := labelHeads J.n base
  let seen := labelSeen J.n base
  let nodes := labelNodes J.n base
  let cell := heads+2*v.val
  have hnodeBound : base+3+5*J.n ≤ heap := hnodesEnd
  change nodes ≤ heap at hnodesEnd
  have hheadEnd : heads+2*J.n+1 = nodes := by dsimp [heads, nodes, labelHeads, labelNodes]; omega
  have hseenEnd : seen+J.n = heads := by dsimp [seen, heads, labelSeen, labelHeads]; omega
  have hlabelEnd : labelLabels base+2*J.n = seen := rfl
  obtain ⟨_, _, hpendingEnd, _, tail, htailMem, htail⟩ := indexListAt_cons_iff.mp hpending
  obtain ⟨prefixPtr, hentryHeader, hentries⟩ := hout v
  change ListAt mem cell [prefixPtr, entries.length] at hentryHeader
  have hptrMem : mem base = pending := by
    have h := hheader 0 (by change 0 < 2; decide)
    change mem (base+0) = pending at h
    simpa only [Nat.add_zero] using h
  have hlenMem : mem (base+1) = (e :: rest).length := hheader 1 (by change 1 < 2; decide)
  have hentryMem : mem cell = prefixPtr := by
    have h := hentryHeader 0 (by change 0 < 2; decide)
    change mem (cell+0) = prefixPtr at h
    simpa only [Nat.add_zero] using h
  have hentryLenMem : mem (cell+1) = entries.length := hentryHeader 1 (by change 1 < 2; decide)
  have hv := v.isLt
  have hcellEnd : cell+2 ≤ heads+2*J.n := by dsimp [cell]; omega
  have hheap : heap < 2 ^ w := by omega
  have hbase : base < 2 ^ w := by omega
  have hbase1 : base+1 < 2 ^ w := by omega
  have hbase2 : base+2 < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := by omega
  have hvWord : v.val < 2 ^ w := by omega
  have h2v : 2*v.val < 2 ^ w := by omega
  have h3n : 3*J.n < 2 ^ w := by omega
  have hheads : heads < 2 ^ w := by dsimp [heads, labelHeads]; omega
  have hheadsCalc : base+2+3*J.n < 2 ^ w := hheads
  have hcell : cell < 2 ^ w := by omega
  have hcell1 : cell+1 < 2 ^ w := by omega
  have hcell2 : cell+2 < 2 ^ w := by omega
  have hpendingWord : pending < 2 ^ w := by omega
  have hpending1 : pending+1 < 2 ^ w := by omega
  have htailWord : tail < 2 ^ w := htail.pointer_le.trans_lt hheap
  have hprefixWord : prefixPtr < 2 ^ w := hentries.pointer_le.trans_lt hheap
  have hentryLen : entries.length < 2 ^ w := by change entries.length+(e :: rest).length < 2 ^ w at hbudget; omega
  have hpendingLen : (e :: rest).length < 2 ^ w := by change entries.length+(e :: rest).length < 2 ^ w at hbudget; omega
  have hrestLen : rest.length < 2 ^ w := by simp only [List.length_cons] at hpendingLen; omega
  have hnewLen : entries.length+rest.length < 2 ^ w := by
    change entries.length+(e :: rest).length < 2 ^ w at hbudget
    simp only [List.length_cons] at hbudget
    omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hthree : 3 < 2 ^ w := by omega
  let newPtr := if entries = [] then tail else heap
  have hnewPtr : newPtr < 2 ^ w := by dsimp [newPtr]; split <;> assumption
  have hkA := indexListAppend_meetsContract (w := w) (lo := nodes) happend entries rest
  apply runs_start_le
  unfold labelLoadOutgoingBody
  refine runs_seq_assign_le (v := heads) (by change _ = some (base+2+3*J.n); eval_expr) ?_
  refine runs_seq_assign_le (v := cell) (by eval_expr) ?_
  refine runs_seq_assign_le (v := pending) (by eval_expr) ?_
  refine runs_seq_assign_le (v := tail) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (e :: rest).length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := prefixPtr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := entries.length) (by eval_expr) ?_
  refine runs_seq_call_le hkA (vs := [prefixPtr, tail, entries.length, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · refine ⟨⟨prefixPtr, tail, heap, rfl, hentries, htail, by omega, hnodesEnd, ?_, htwo⟩, hzero, hspace⟩
    intro k _
    exact k.isLt.trans hm
  · intro next memA posA hpostA
    obtain ⟨⟨_, _, hframeA, hzeroA, hpendingA⟩, hnext⟩ := hpostA
    change next = heap+2*entries.length at hnext
    change (∀ x < heap, memA x = mem x) at hframeA
    change ZeroFrom memA next at hzeroA
    change IndexListAt memA nodes (heap+2*entries.length) newPtr (entries ++ rest) at hpendingA
    rw [← hnext] at hpendingA
    have hnextWord : next < 2 ^ w := by omega
    have hlabelsA : SignedTableAt memA (labelLabels base) s.labels := hlabels.of_agree_below (by omega) hframeA
    have hseenA : BoolTableAt memA seen s.seen := hseen.of_agree_below (by omega) hframeA
    have houtA : AdjacencyAt memA heads nodes next s.outgoing :=
      hout.of_agree_below (by omega) (by omega) hframeA
    wram_step
    all_goals
      unfold labelLoadOutgoingFinish
      refine runs_seq_call_le hkW (vs := [newPtr, entries.length+rest.length, base]) ?_ ?_ ?_ ?_
      · have heq : (e :: rest).length-1 = rest.length := rfl
        rw [← heq]
        by_cases hnil : entries = []
        · simp [hnil] at hcond
          all_goals
            dsimp only [newPtr]
            rw [ite_eq_left hnil]
            eval_expr
        · simp [hnil] at hcond
          all_goals
            dsimp only [newPtr]
            rw [ite_eq_right hnil]
            eval_expr
      · wram_words
      · exact ⟨_, _, _, rfl, hbase2⟩
      · intro _ memH posH hpostH
        obtain ⟨_, hheaderH, hframeH⟩ := hpostH
        change ListAt memH base [newPtr, entries.length+rest.length] at hheaderH
        change (∀ x, x < base ∨ base+2 ≤ x → memH x = memA x) at hframeH
        have hlabelsH : SignedTableAt memH (labelLabels base) s.labels := by
          apply hlabelsA.of_agree
          intro x hx _
          exact hframeH x (Or.inr hx)
        have hseenH : BoolTableAt memH seen s.seen := by
          apply hseenA.of_agree
          intro x hx _
          exact hframeH x (Or.inr (by dsimp [seen, labelSeen] at hx; omega))
        have houtH : AdjacencyAt memH heads nodes next s.outgoing := by
          apply houtA.of_agree le_rfl
          · intro x hx _
            exact hframeH x (Or.inr (by dsimp [heads, labelHeads] at hx; omega))
          · intro x hx _
            exact hframeH x (Or.inr (by dsimp [nodes, labelNodes] at hx; omega))
        have hpendingH : IndexListAt memH nodes next newPtr (entries ++ rest) := by
          apply hpendingA.of_agree
          intro x hx _
          exact hframeH x (Or.inr (by dsimp [nodes, labelNodes] at hx; omega))
        have hkC := adjacencyClear_meetsContract (w := w) (heads := heads) (lo := nodes)
          (bound := next) hpair s.outgoing v
        refine runs_seq_call_le hkC (vs := [0, 0, cell]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨rfl, houtH, by omega, by omega⟩
        · intro _ memC posC hpostC
          obtain ⟨_, houtC, hframeC⟩ := hpostC
          change AdjacencyAt memC heads nodes next (Function.update s.outgoing v []) at houtC
          change (∀ x, x < cell ∨ cell+2 ≤ x → memC x = memH x) at hframeC
          have hlabelsC : SignedTableAt memC (labelLabels base) s.labels := by
            apply hlabelsH.of_agree
            intro x _ hx
            exact hframeC x (Or.inl (by rw [hlabelEnd] at hx; dsimp [cell]; omega))
          have hseenC : BoolTableAt memC seen s.seen := by
            apply hseenH.of_agree
            intro x _ hx
            exact hframeC x (Or.inl (by dsimp [cell]; omega))
          have hheaderC : ListAt memC base [newPtr, (entries ++ rest).length] := by
            rw [List.length_append]
            intro i hi
            have hi' : i < 2 := hi
            rw [hframeC _ (Or.inl (by dsimp [cell, heads, labelHeads]; omega))]
            exact hheaderH i hi
          have hpendingC : IndexListAt memC nodes next newPtr (entries ++ rest) := by
            apply hpendingH.of_agree
            intro x hx _
            exact hframeC x (Or.inr (by omega))
          refine runs_ret_le (v := next) (by eval_expr) ?_ ?_
          · change next = heap+2*entries.length ∧ LabelStateAt memC base next
              { s with outgoing := Function.update s.outgoing v [], pending := entries ++ rest } ∧
              ZeroFrom memC next ∧ ∀ x < heap, (x < base ∨ base+2 ≤ x) →
                (x < cell ∨ cell+2 ≤ x) → memC x = mem x
            refine ⟨hnext, ⟨newPtr, hheaderC, hpendingC, hlabelsC, hseenC, houtC⟩, ?_, ?_⟩
            · intro x hx
              apply (hframeC x (Or.inr (by omega))).trans
              exact (hframeH x (Or.inr (by dsimp [nodes, labelNodes] at hnodesEnd; omega))).trans (hzeroA x hx)
            · intro x hx hxheader hxhead
              exact (hframeC x hxhead).trans ((hframeH x hxheader).trans (hframeA x hx))
          · simp only [labelLoadOutgoingContract, indexListAppendContract, heapContract,
              wordPairStoreContract, adjacencyClearContract, argsSize_cons, argsSize_nil,
              Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]
            change _ ≤ 100*entries.length+240
            omega

/-- Arbitrary nonempty pending lists have simultaneous load/clear premises
on a concrete state with empty outgoing lists and a sufficiently large width. -/
theorem exists_labelLoadOutgoing_pre (J : Circulation) (e : Fin J.m)
    (rest : List (Fin J.m)) (v : Fin J.n) :
    ∃ w mem heap, (∀ x ∈ [0, J.n, v.val, heap], x < 2 ^ w) ∧
      (labelLoadOutgoingContract w
        { labels := fun _ => 0, seen := fun _ => false, outgoing := fun _ => [], pending := e :: rest :
          Circulation.LabelState J } e rest v).pre [0, J.n, v.val, heap] mem := by
  obtain ⟨mem, heap, hnodes, hzero, hat⟩ := exists_labelStatePendingAt J (e :: rest)
  let w := heap+J.n+J.m+(e :: rest).length+5
  have hw : heap+J.n+J.m+(e :: rest).length+5 < 2 ^ w := Nat.lt_two_pow_self
  have hv := v.isLt
  refine ⟨w, mem, heap, ?_, 0, heap, rfl, hat, rfl, hnodes, by omega,
    by change 0+(e :: rest).length < 2 ^ w; omega, hzero, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · change heap+2*0 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
