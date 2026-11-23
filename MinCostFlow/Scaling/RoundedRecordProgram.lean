module

public import MinCostFlow.Scaling.RoundedCostProgram
public import MinCostFlow.Scaling.SignedTableLayout
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.WordFiveStoreProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Writing one rounded residual record

A rounded residual instance keeps each edge's endpoints and capacity and
replaces its cost by the rounded reduced cost. This procedure reads an
existing five-word residual record and the two endpoint potentials, computes
the model's rounded cost, and writes the new record into a reserved array.
It uses twelve fresh scratch cells, costs at most 1500 steps, and changes
no other old cells.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[edge,potentials,B^8,B^9,power,C+1,destination,heap]`. -/
def roundedRecordBody (cost writer : ℕ) : Stmt :=
  .call 8 cost [.load (.bin .add (.reg 0) (.const 3)), .load (.bin .add (.reg 0) (.const 4)),
    .load (.bin .add (.reg 1) (.bin .mul (.const 2) (.load (.reg 0)))),
    .load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.load (.reg 0)))) (.const 1)),
    .load (.bin .add (.reg 1) (.bin .mul (.const 2) (.load (.bin .add (.reg 0) (.const 1))))),
    .load (.bin .add (.bin .add (.reg 1)
      (.bin .mul (.const 2) (.load (.bin .add (.reg 0) (.const 1))))) (.const 1)),
    .reg 2, .reg 3, .reg 4, .reg 5, .reg 7] ;;
  .call 9 writer [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
    .load (.bin .add (.reg 0) (.const 2)),
    .load (.bin .add (.reg 7) (.const 10)), .load (.bin .add (.reg 7) (.const 11)), .reg 6] ;;
  .ret (.reg 8)

/-- The record entry, rounded-cost module, and in-place record writer. -/
def roundedRecordModule (b : ℕ) : List Stmt :=
  roundedRecordBody (b + 1) (b + 20) :: (roundedCostModule (b + 1) ++ wordFiveModule)

/-- The scalar call's arguments, before reading them from a stored edge. -/
def roundedCostArguments {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m+I.m)) (heap : ℕ) : List ℕ :=
  let R := I.residual s.flow
  let x := s.potential (R.tail e)
  let y := s.potential (R.head e)
  [if R.cost e < 0 then 1 else 0, (R.cost e).natAbs,
    if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs,
    (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, heap]

/-- Sources precede the reserved destination, which precedes fresh scratch.
The scalar arithmetic precondition contains only local word budgets. -/
def roundedRecordContract (w : ℕ) {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m+I.m)) : Contract where
  pre args mem := ∃ a pot dst heap,
    args = [a, pot, (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, dst, heap] ∧
    ListAt mem a ((I.residual s.flow).solverEdgeWords e) ∧ SignedTableAt mem pot s.potential ∧
    a+5 ≤ dst ∧ pot+2*I.n ≤ dst ∧ dst+5 ≤ heap ∧
    (∀ x ∈ (I.residual s.flow).solverEdgeWords e, x < 2 ^ w) ∧
    (roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem
  post args mem out mem' := out = heapArg args+12 ∧
    ListAt mem' (args.getD 6 0) ((s.roundedInstance C).solverEdgeWords e) ∧
    ZeroFrom mem' out ∧
    ∀ x < heapArg args, x < args.getD 6 0 ∨ args.getD 6 0+5 ≤ x → mem' x = mem x
  cost _ _ := 1500

/-- The record transformation uses no random instructions. -/
theorem roundedRecordModule_noRand (b : ℕ) :
    ∀ body ∈ roundedRecordModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [roundedRecordBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact roundedCostModule_noRand _ body hb
    · have hh : body = wordFiveBody := by simpa only [wordFiveModule, List.mem_singleton] using hb
      subst body
      exact wordFiveBody_noRand

/-- Reading a residual record and its stored endpoint potentials produces
exactly the corresponding rounded-instance record. -/
theorem roundedRecord_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (roundedRecordModule b)) {I : Circulation} (s : CostState I)
    (C : ℕ) (e : Fin (I.m+I.m)) :
    MeetsContract w p b (roundedRecordContract w s C e) := by
  have htail := hasAt_tail hp
  have hcost := hasAt_append_left htail
  have hwriter : p.HasAt (b+20) wordFiveModule := by
    have h := hasAt_append_right htail
    simpa only [roundedCostModule, costNumeratorModule, reducedNumeratorModule,
      signedScaleModule, scaledDifferenceModule, signedSubtractModule, signedAddModule,
      roundClipModule, nearestQuotientModule, costClipModule, List.length_cons,
      List.length_nil, List.length_append, Nat.reduceAdd, Nat.add_assoc] using h
  have hkC := roundedCost_meetsContract (w := w) hcost s C e
  have hkW := wordFiveStore_meetsContract (w := w) hwriter
  let R := I.residual s.flow
  let x := s.potential (R.tail e)
  let y := s.potential (R.head e)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, pot, dst, heap, rfl, hrecord, htable, habefore, hpbefore, hbefore, hrecordWords, hscalar⟩ := hpre
  have hbudget := hscalar
  obtain ⟨⟨heap', heq, _, _, hxy, _, _, _⟩, hzero, hspace⟩ := hbudget
  have heaph : heap' = heap := by
    have h := congrArg (fun xs : List ℕ => xs.getD 10 0) heq
    simpa only [roundedCostArguments, List.getD_cons_succ, List.getD_cons_zero] using h.symm
  subst heap'
  change ZeroFrom mem heap at hzero
  change heap+12 < 2 ^ w at hspace
  change x.natAbs+y.natAbs < 2 ^ w at hxy
  have htailIdx := (R.tail e).isLt
  have hheadIdx := (R.head e).isLt
  change (R.tail e).val < I.n at htailIdx
  change (R.head e).val < I.n at hheadIdx
  have htailPair := htable (R.tail e)
  have hheadPair := htable (R.head e)
  have hfields : ∀ j : Fin 5, mem (a+j.val) = (R.solverEdgeWords e).getD j.val 0 := by
    intro j
    have hj : j.val < (R.solverEdgeWords e).length := j.isLt
    rw [List.getD_eq_getElem _ _ hj]
    exact hrecord _ hj
  have ht := hfields ⟨0, by decide⟩
  have hh := hfields ⟨1, by decide⟩
  have hu := hfields ⟨2, by decide⟩
  have hcs := hfields ⟨3, by decide⟩
  have hcm := hfields ⟨4, by decide⟩
  simp only [Circulation.solverEdgeWords, List.getD_cons_succ, List.getD_cons_zero,
    Nat.add_zero] at ht hh hu hcs hcm
  have hxs : mem (pot+2*(R.tail e).val) = if x < 0 then 1 else 0 := by
    simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using
      htailPair 0 (by change 0 < 2; decide)
  have hxm : mem (pot+2*(R.tail e).val+1) = x.natAbs := by
    simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using
      htailPair 1 (by change 1 < 2; decide)
  have hys : mem (pot+2*(R.head e).val) = if y < 0 then 1 else 0 := by
    simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using
      hheadPair 0 (by change 0 < 2; decide)
  have hym : mem (pot+2*(R.head e).val+1) = y.natAbs := by
    simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using
      hheadPair 1 (by change 1 < 2; decide)
  have hB8 : (I.m+I.m)^8 < 2 ^ w := hwords _ (by simp)
  have hB9 : (I.m+I.m)^9 < 2 ^ w := hwords _ (by simp)
  have hpower : s.power < 2 ^ w := hwords _ (by simp)
  have hd : C+1 < 2 ^ w := hwords _ (by simp)
  have hheap : heap < 2 ^ w := by omega
  have hheap10 : heap+10 < 2 ^ w := by omega
  have hheap11 : heap+11 < 2 ^ w := by omega
  have hdst : dst < 2 ^ w := by omega
  have hdst5 : dst+5 < 2 ^ w := by omega
  have ha : a < 2 ^ w := by omega
  have ha1 : a+1 < 2 ^ w := by omega
  have ha2 : a+2 < 2 ^ w := by omega
  have ha3 : a+3 < 2 ^ w := by omega
  have ha4 : a+4 < 2 ^ w := by omega
  have htval : (R.tail e).val < 2 ^ w := by omega
  have hhval : (R.head e).val < 2 ^ w := by omega
  have ht2 : 2*(R.tail e).val < 2 ^ w := by omega
  have hh2 : 2*(R.head e).val < 2 ^ w := by omega
  have hpt : pot+2*(R.tail e).val < 2 ^ w := by omega
  have hpt1 : pot+2*(R.tail e).val+1 < 2 ^ w := by omega
  have hph : pot+2*(R.head e).val < 2 ^ w := by omega
  have hph1 : pot+2*(R.head e).val+1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hthree : 3 < 2 ^ w := by omega
  have hfour : 4 < 2 ^ w := by omega
  have hten : 10 < 2 ^ w := by omega
  have heleven : 11 < 2 ^ w := by omega
  have hcostMag : (R.cost e).natAbs < 2 ^ w := hrecordWords _ (by simp [Circulation.solverEdgeWords, R])
  have hcap : R.capacity e < 2 ^ w := hrecordWords _ (by simp [Circulation.solverEdgeWords, R])
  have hcostSign : (if R.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hx : x.natAbs < 2 ^ w := by omega
  have hy : y.natAbs < 2 ^ w := by omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold roundedRecordBody
  refine runs_seq_call_le hkC (vs := roundedCostArguments s C e heap) ?_ ?_ hscalar ?_
  · change _ = some [if R.cost e < 0 then 1 else 0, (R.cost e).natAbs,
      if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs,
      (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, heap]
    eval_expr
    all_goals
      simp only [Expr.MemAt, startState, ht, hh]
      assumption
  · change ∀ a ∈ [if R.cost e < 0 then 1 else 0, (R.cost e).natAbs,
      if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs,
      (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, heap], a < 2 ^ w
    wram_words
  · intro next memC posC hpostC
    obtain ⟨⟨_, _, hframeC, hzeroC, hpairC⟩, hnext⟩ := hpostC
    change next = heap+12 at hnext
    change (∀ a < heap, memC a = mem a) at hframeC
    change ZeroFrom memC next at hzeroC
    change ListAt memC (heap+10) (encodeInt ((s.roundedInstance C).cost e)) at hpairC
    have htC : memC a = (R.tail e).val := (hframeC _ (by omega)).trans ht
    have hhC : memC (a+1) = (R.head e).val := (hframeC _ (by omega)).trans hh
    have huC : memC (a+2) = R.capacity e := (hframeC _ (by omega)).trans hu
    have hsC : memC (heap+10) = if (s.roundedInstance C).cost e < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hpairC 0 (by change 0 < 2; decide)
    have hmC : memC (heap+11) = ((s.roundedInstance C).cost e).natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero,
        show heap+10+1 = heap+11 by omega] using hpairC 1 (by change 1 < 2; decide)
    have hnextWord : next < 2 ^ w := by omega
    have hresultSign : (if (s.roundedInstance C).cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hresultMag : ((s.roundedInstance C).cost e).natAbs < 2 ^ w := by
      have hencoding := encodeInt_clip (s.roundedCost C e) ((I.m+I.m)^8) ((I.m+I.m)^9)
      have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hencoding
      change ((s.roundedInstance C).cost e).natAbs =
        min (s.roundedCost C e).natAbs (if s.roundedCost C e < 0 then (I.m+I.m)^8 else (I.m+I.m)^9) at hh
      rw [hh]
      apply lt_of_le_of_lt (Nat.min_le_right _ _)
      split <;> assumption
    refine runs_seq_call_le hkW
      (vs := [(R.tail e).val, (R.head e).val, R.capacity e,
        if (s.roundedInstance C).cost e < 0 then 1 else 0, ((s.roundedInstance C).cost e).natAbs, dst])
      (by eval_expr) ?_ ?_ ?_
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · exact ⟨_, _, _, _, _, _, rfl, hdst5⟩
    · intro _ memW posW hpostW
      obtain ⟨_, hstored, hframeW⟩ := hpostW
      change ListAt memW dst ((s.roundedInstance C).solverEdgeWords e) at hstored
      change (∀ x, x < dst ∨ dst+5 ≤ x → memW x = memC x) at hframeW
      refine runs_ret_le (v := next) (by eval_expr) ?_ ?_
      · change next = heap+12 ∧ ListAt memW dst ((s.roundedInstance C).solverEdgeWords e) ∧
          ZeroFrom memW next ∧ ∀ x < heap, x < dst ∨ dst+5 ≤ x → memW x = mem x
        refine ⟨hnext, hstored, ?_, ?_⟩
        · intro x hx
          exact (hframeW x (Or.inr (by omega))).trans (hzeroC x hx)
        · intro x hx hxout
          exact (hframeW x hxout).trans (hframeC x hx)
      · simp only [roundedRecordContract, roundedCostContract, heapContract, wordFiveStoreContract,
          argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg,
          Expr.size_const]; omega

/-- Any represented cost state and residual edge have simultaneous source,
table, arithmetic, and scratch-allocation premises at a large enough width. -/
theorem exists_roundedRecord_pre {I : Circulation} (s : CostState I) (C : ℕ)
    (e : Fin (I.m+I.m)) :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧
      (roundedRecordContract w s C e).pre args mem := by
  let R := I.residual s.flow
  let c := R.cost e
  let x := s.potential (R.tail e)
  let y := s.potential (R.head e)
  let B := I.m+I.m
  let factor := B^8*s.power
  let d := C+1
  let z := s.costNumerator C e
  let dst := 5+2*I.n
  let heap := dst+5
  let record := R.solverEdgeWords e
  let table := (List.ofFn s.potential).flatMap encodeInt
  let mem := initMem (record ++ table)
  have hrecordlen : record.length = 5 := rfl
  have htablelen : table.length = 2*I.n := by
    simp only [table, integers_encode_length, List.length_ofFn]
  have hat := listAt_append.mp (listAt_initMem (record ++ table))
  have htable : SignedTableAt mem 5 s.potential := by
    apply signedTableAt_of_listAt
    simpa only [hrecordlen, Nat.zero_add] using hat.2
  have hzero : ZeroFrom mem heap := by
    have hz := zeroFrom_initMem (record ++ table)
    change ZeroFrom mem (record ++ table).length at hz
    rw [List.length_append, hrecordlen, htablelen] at hz
    intro a ha
    exact hz a (by change dst+5 ≤ a at ha; dsimp [dst] at ha; omega)
  let w := c.natAbs+x.natAbs+y.natAbs+B^8+B^9+s.power+factor+c.natAbs*factor+
    (x-y).natAbs*d+d+z.natAbs+R.capacity e+2*I.n+30
  have hw : c.natAbs+x.natAbs+y.natAbs+B^8+B^9+s.power+factor+c.natAbs*factor+
      (x-y).natAbs*d+d+z.natAbs+R.capacity e+2*I.n+30 < 2 ^ w := Nat.lt_two_pow_self
  have ht : (R.tail e).val < I.n := (R.tail e).isLt
  have hh : (R.head e).val < I.n := (R.head e).isLt
  have hhalf := Nat.div_le_self d 2
  refine ⟨w, [0, 5, B^8, B^9, s.power, d, dst, heap], mem, ?_,
    0, 5, dst, heap, rfl, hat.1, htable, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try dsimp [heap, dst]) <;> omega
  · dsimp [dst]; omega
  · dsimp [dst]; omega
  · exact le_rfl
  · change ∀ a ∈ [(R.tail e).val, (R.head e).val, R.capacity e,
      if c < 0 then 1 else 0, c.natAbs], a < 2 ^ w
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · split <;> omega
    · omega
  · refine ⟨⟨heap, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, hzero, ?_⟩
    · change factor < 2 ^ w; omega
    · change c.natAbs*factor < 2 ^ w; omega
    · change x.natAbs+y.natAbs < 2 ^ w; omega
    · change (x-y).natAbs*d < 2 ^ w; omega
    · change (c*(factor : ℤ)).natAbs+((x-y)*(d : ℤ)).natAbs < 2 ^ w
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      omega
    · change z.natAbs+d/2 < 2 ^ w; omega
    · change heap+12 < 2 ^ w
      dsimp [heap, dst]
      omega

end MinCostFlow.Scaling.Machine
