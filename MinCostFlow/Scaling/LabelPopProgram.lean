module

public import MinCostFlow.Scaling.LabelStateLayout
public import MinCostFlow.Scaling.WordPairStoreProgram
import MinCostFlow.Scaling.LabelStateWitness
import WordRAM.Tactic

/-!
# Removing a processed pending edge

If the next edge's head was already reached, label propagation drops that
edge from pending and changes no other state field. This procedure reads
the immutable head's tail pointer and decreases the stored pending length.
The shared pair writer updates the header. It allocates no memory,
preserves every other cell, and costs at most 70 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[stateBase,heap]`, for a nonempty pending list. -/
def labelPopBody (writer : ℕ) : Stmt :=
  .call 2 writer [.load (.bin .add (.load (.reg 0)) (.const 1)),
    .bin .sub (.load (.bin .add (.reg 0) (.const 1))) (.const 1), .reg 0] ;;
  .ret (.reg 1)

/-- Pending-header update followed by the existing pair writer. -/
def labelPopModule (b : ℕ) : List Stmt := [labelPopBody (b+1), wordPairBody]

/-- A nonempty stored pending list and its fitting length suffice for pop. -/
def labelPopContract (w : ℕ) {J : Circulation} (s : Circulation.LabelState J)
    (e : Fin J.m) (rest : List (Fin J.m)) : Contract where
  pre args mem := ∃ base heap, args = [base, heap] ∧ LabelStateAt mem base heap s ∧
    s.pending = e :: rest ∧ labelNodes J.n base ≤ heap ∧
    s.pending.length < 2 ^ w ∧ ZeroFrom mem heap ∧ heap < 2 ^ w
  post args mem ret mem' := ret = heapArg args ∧
    LabelStateAt mem' (args.getD 0 0) ret { s with pending := rest } ∧ ZeroFrom mem' ret ∧
    ∀ x, x < args.getD 0 0 ∨ args.getD 0 0+2 ≤ x → mem' x = mem x
  cost _ _ := 70

/-- Pending pop and its shared writer use no random instructions. -/
theorem labelPopModule_noRand (b : ℕ) : ∀ body ∈ labelPopModule b, body.NoRand := by
  intro body hb
  simp only [labelPopModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [labelPopBody, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- The procedure drops exactly the pending head, preserves the remaining
label state and every other memory cell, and allocates no new words. -/
theorem labelPop_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (labelPopModule b)) {J : Circulation} (s : Circulation.LabelState J)
    (e : Fin J.m) (rest : List (Fin J.m)) : MeetsContract w p b (labelPopContract w s e rest) := by
  have hpair : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [labelPopModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [labelPopModule])
  have hkW := wordPairStore_meetsContract (w := w) hpair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, heap, rfl, hstate, hnonempty, hnodesEnd, hlength, hzero, hheap⟩ := hpre
  obtain ⟨ptr, hheader, hpending, hlabels, hseen, hout⟩ := hstate
  rw [hnonempty] at hheader hpending hlength
  obtain ⟨_, _, hptrEnd, _, tail, htailMem, htail⟩ := indexListAt_cons_iff.mp hpending
  have hptrMem : mem base = ptr := by
    have h := hheader 0 (by change 0 < 2; decide)
    change mem (base+0) = ptr at h
    simpa only [Nat.add_zero] using h
  have hlenMem : mem (base+1) = (e :: rest).length := hheader 1 (by change 1 < 2; decide)
  have hbase : base < 2 ^ w := by dsimp [labelNodes] at hnodesEnd; omega
  have hbase1 : base+1 < 2 ^ w := by dsimp [labelNodes] at hnodesEnd; omega
  have hbase2 : base+2 < 2 ^ w := by dsimp [labelNodes] at hnodesEnd; omega
  have hptr : ptr < 2 ^ w := by omega
  have hptr1 : ptr+1 < 2 ^ w := by omega
  have htailWord : tail < 2 ^ w := htail.pointer_le.trans_lt hheap
  have hrestLen : rest.length < 2 ^ w := by simp only [List.length_cons] at hlength; omega
  have hone : 1 < 2 ^ w := by dsimp [labelNodes] at hnodesEnd; omega
  apply runs_start_le
  unfold labelPopBody
  refine runs_seq_call_le hkW (vs := [tail, rest.length, base]) ?_ ?_ ?_ ?_
  · have heq : (e :: rest).length-1 = rest.length := rfl
    rw [← heq]
    eval_expr
    all_goals
      simp only [Expr.MemAt, startState, hptrMem]
      first | exact hptr1 | exact htailMem
  · wram_words
  · exact ⟨tail, rest.length, base, rfl, hbase2⟩
  · intro _ memW posW hpostW
    obtain ⟨_, hheaderW, hframeW⟩ := hpostW
    change ListAt memW base [tail, rest.length] at hheaderW
    change (∀ x, x < base ∨ base+2 ≤ x → memW x = mem x) at hframeW
    have htailW : IndexListAt memW (labelNodes J.n base) heap tail rest := by
      apply htail.of_agree
      intro x hx _
      exact hframeW x (Or.inr (by dsimp [labelNodes] at hx; omega))
    have hlabelsW : SignedTableAt memW (labelLabels base) s.labels := by
      apply hlabels.of_agree
      intro x hx _
      exact hframeW x (Or.inr hx)
    have hseenW : BoolTableAt memW (labelSeen J.n base) s.seen := by
      apply hseen.of_agree
      intro x hx _
      exact hframeW x (Or.inr (by dsimp [labelSeen] at hx; omega))
    have houtW : AdjacencyAt memW (labelHeads J.n base) (labelNodes J.n base) heap s.outgoing := by
      apply hout.of_agree le_rfl
      · intro x hx _
        exact hframeW x (Or.inr (by dsimp [labelHeads] at hx; omega))
      · intro x hx _
        exact hframeW x (Or.inr (by dsimp [labelNodes] at hx; omega))
    refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
    · change heap = heap ∧ LabelStateAt memW base heap { s with pending := rest } ∧
        ZeroFrom memW heap ∧ ∀ x, x < base ∨ base+2 ≤ x → memW x = mem x
      refine ⟨rfl, ⟨tail, hheaderW, htailW, hlabelsW, hseenW, houtW⟩, ?_, hframeW⟩
      intro x hx
      exact (hframeW x (Or.inr (by dsimp [labelNodes] at hnodesEnd; omega))).trans (hzero x hx)
    · simp only [labelPopContract, wordPairStoreContract, argsSize_cons, argsSize_nil,
        Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]; omega

/-- Arbitrary pending tails have simultaneous layout, word, and allocation
premises for pop in a concrete nonempty label state. -/
theorem exists_labelPop_pre (J : Circulation) (e : Fin J.m) (rest : List (Fin J.m)) :
    ∃ w mem heap, (∀ x ∈ [0, heap], x < 2 ^ w) ∧
      (labelPopContract w
        { labels := fun _ => 0, seen := fun _ => false, outgoing := fun _ => [], pending := e :: rest :
          Circulation.LabelState J } e rest).pre [0, heap] mem := by
  obtain ⟨mem, heap, hnodes, hzero, hat⟩ := exists_labelStatePendingAt J (e :: rest)
  let w := heap+(e :: rest).length+3
  have hw : heap+(e :: rest).length+3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, mem, heap, ?_, 0, heap, rfl, hat, rfl, hnodes, by change (e :: rest).length < 2 ^ w; omega, hzero, by omega⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
