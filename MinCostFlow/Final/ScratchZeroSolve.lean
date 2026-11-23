module

public import MinCostFlow.Final.ScratchSolve
public import MinCostFlow.Scaling.ZeroCapacitySolveProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Solving circulations with inactive edges

The scaling reduction on page 15 retains zero-capacity edge slots.
The adapter builds a positive-capacity circulation, solves it in a
guest region sized for polynomial scratch, and erases the dummy flows.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The entry, positive graph construction, canonical solve, and erasure. -/
def scratchZeroSolveModule (Q : Program) (f b c d : ℕ) : List Stmt :=
  let solveBase := b+5
  let eraseBase := solveBase+(scratchSolveModule Q f solveBase c d).length
  zeroCapacitySolveBody (b+1) solveBase eraseBase ::
    (positiveInstanceModule (b+1) ++ scratchSolveModule Q f solveBase c d ++ eraseZeroFlowModule eraseBase)

/-- The outer layout reserves the positive graph, one complete canonical
guest region, and one unsigned result word per original edge. -/
def scratchZeroSolveContract (w : ℕ) (Q : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (solverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) : Contract :=
  let guest := wordSize (scratchWordMultiplier c d) J.positiveInstance.solverWords
  let H := heapContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      2 ^ (guest+1)+2 ≤ 2 ^ w)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args+3+5*J.m+2^guest) =
      Circulation.solveWithZeroCapacities ((fun K : Circulation => scratchCanonicalSolverAt
        (wordSize (scratchWordMultiplier c d) K.solverWords) Q f T S (hproc K) K)) J)
    (fun _ _ => (Q.regBound+6)*T (J.n+1) J.m+
      80*J.positiveInstance.solverWords.length+40*guest+Q.regBound+400*J.m+900)
    (fun _ _ => 3+6*J.m+2^guest)
  { H with post := fun args mem out mem' => H.post args mem out mem' ∧
      out = heapArg args+3+6*J.m+2^guest }

/-- The complete adapter is deterministic whenever its supplied solver is. -/
theorem scratchZeroSolveModule_noRand (Q : Program) (f b c d : ℕ) (hdet : Q.IsDeterministic) :
    ∀ body ∈ scratchZeroSolveModule Q f b c d, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [zeroCapacitySolveBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact positiveInstanceModule_noRand _ body hb
      · exact scratchSolveModule_noRand Q f _ c d hdet body hb
    · have he : body = eraseZeroFlowBody (b+5+(scratchSolveModule Q f (b+5) c d).length) := by
        simpa only [eraseZeroFlowModule, List.mem_singleton] using hb
      subst body
      exact eraseZeroFlowBody_noRand _

/-- Under exactly the bounded-circulation solver specification, the complete
adapter computes the model's exact zero-capacity solve with counted setup,
solver, and erasure work. -/
theorem scratchZeroSolve_meetsContract {w b : ℕ} {Q P : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (solverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (hdet : Q.IsDeterministic)
    (J : Circulation) (hc : J.CostsBounded (J.m^10)) (hu : ∀ e, J.capacity e ≤ J.m^40)
    (hS : S J.positiveInstance.n J.positiveInstance.m ≤
      c * (J.positiveInstance.n + J.positiveInstance.m + 2)^d)
    (hp : P.HasAt b (scratchZeroSolveModule Q f b c d)) :
    MeetsContract w P b (scratchZeroSolveContract w Q f T S c d hproc J) := by
  let guest := wordSize (scratchWordMultiplier c d) J.positiveInstance.solverWords
  let solve := (fun K : Circulation => scratchCanonicalSolverAt
        (wordSize (scratchWordMultiplier c d) K.solverWords) Q f T S (hproc K) K)
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hpositive := hasAt_append_left hleft
  have hsolve : P.HasAt (b+5) (scratchSolveModule Q f (b+5) c d) := by
    have h := hasAt_append_right hleft
    simpa only [positiveInstanceModule, positiveInstanceEdgesModule, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  have herase : P.HasAt (b+5+(scratchSolveModule Q f (b+5) c d).length)
      (eraseZeroFlowModule (b+5+(scratchSolveModule Q f (b+5) c d).length)) := by
    have h := hasAt_append_right htail
    have hlen : (positiveInstanceModule (b+1)).length = 4 := rfl
    rw [List.length_append] at h
    change P.HasAt (b+1+((positiveInstanceModule (b+1)).length+(scratchSolveModule Q f (b+5) c d).length))
      (eraseZeroFlowModule (b+5+(scratchSolveModule Q f (b+5) c d).length)) at h
    rw [hlen, show b+1+(4+(scratchSolveModule Q f (b+5) c d).length) =
      b+5+(scratchSolveModule Q f (b+5) c d).length by omega] at h
    exact h
  have hcPositive : J.positiveInstance.CostsBounded (J.positiveInstance.m^10) :=
    J.positiveInstance_costsBounded _ hc
  have huPositive : ∀ e, 1 ≤ J.positiveInstance.capacity e ∧
      J.positiveInstance.capacity e ≤ J.positiveInstance.m^40 := by
    intro e
    have hmpos : 0 < J.m := by have h : e.val < J.m := e.isLt; omega
    have hU : 1 ≤ J.m^40 := Nat.pow_pos hmpos
    exact J.positiveInstance_capacitiesBounded (J.m^40) hU hu e
  have hkP := positiveInstance_meetsContract (w := w) hpositive J
  have hkS := scratchSolveModule_meetsContract (w := w) hproc hdet J.positiveInstance hS hcPositive huPositive hsolve
  have hkE := eraseZeroFlow_meetsContract (w := w) herase J
    (fun e => (solve J.positiveInstance e).toNat) (List.finRange J.m)
  have hopt := scratchCanonicalSolverAt_optimal guest Q f T S (hproc J.positiveInstance) J.positiveInstance
  have hnonneg : ∀ e, 0 ≤ solve J.positiveInstance e := by
    intro e
    exact Int.cast_nonneg_iff.mp (hopt.1.2 e).1
  have hflowLe : ∀ e, (solve J.positiveInstance e).toNat ≤ J.positiveInstance.capacity e := by
    intro e
    have hi : solve J.positiveInstance e ≤ (J.positiveInstance.capacity e : ℤ) := by
      have hr : ((solve J.positiveInstance e : ℤ) : ℝ) ≤ (J.positiveInstance.capacity e : ℝ) :=
        (hopt.1.2 e).2
      rw [← Int.cast_natCast] at hr
      exact Int.cast_le.mp hr
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hi
  have hmult : 1 ≤ scratchWordMultiplier c d := by unfold scratchWordMultiplier; omega
  have hlenGuest := length_lt_two_pow_wordSize hmult J.positiveInstance.solverWords
  change J.positiveInstance.solverWords.length < 2 ^ guest at hlenGuest
  have hsize := J.solverWords_length
  have hsizePositive : J.positiveInstance.solverWords.length = 2+5*J.m := J.positiveInstance.solverWords_length
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hdoubled⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(3+6*J.m+2^guest) < 2 ^ w at hspace
  change 2^(guest+1)+2 ≤ 2 ^ w at hdoubled
  have hguestHost : 2^guest < 2 ^ w := by rw [Nat.pow_succ] at hdoubled; omega
  have hnGuest : J.n+1 < 2^guest :=
    lt_two_pow_wordSize_of_mem hmult List.mem_cons_self
  have hn1 : J.n+1 < 2 ^ w := hnGuest.trans hguestHost
  have hw : 8 < 2 ^ w := by rw [hsizePositive] at hlenGuest; omega
  have hm : J.m < 2 ^ w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha : a < 2 ^ w := by rw [hsize] at hend; omega
  have ha1 : a+1 < 2 ^ w := by rw [hsize] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [hsize] at hend; omega
  have hh : heap < 2 ^ w := by omega
  have hhGraph : heap+(2+5*J.m) < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hmcell : mem (a+1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hat 1 (by rw [hsize]; omega)
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hinputCapacity : ∀ e, J.capacity e < 2 ^ w := by
    intro e
    exact hinput _ (Circulation.solverEdgeWord_mem J e (by simp [Circulation.solverEdgeWords]))
  have hflowWord : ∀ e, (solve J.positiveInstance e).toNat < 2 ^ w := by
    intro e
    apply (hflowLe e).trans_lt
    by_cases hz : J.capacity e = 0
    · simpa only [Circulation.positiveInstance, hz, ↓reduceIte] using hone
    · simpa only [Circulation.positiveInstance, hz, ↓reduceIte] using hinputCapacity e
  apply runs_start_le
  unfold zeroCapacitySolveBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [a, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a, heap, rfl, hat, hend, hinput, hn1, hw⟩, hzero, hhGraph⟩
  · intro graphEnd memP posP hpostP
    obtain ⟨⟨_, _, hframeP, hzeroP, hgraphP⟩, hgraphEnd⟩ := hpostP
    change graphEnd = heap+2+5*J.m at hgraphEnd
    change (∀ x < heap, memP x = mem x) at hframeP
    change ZeroFrom memP graphEnd at hzeroP
    change ListAt memP heap J.positiveInstance.solverWords at hgraphP
    have hgraphEndWord : graphEnd < 2 ^ w := by omega
    refine runs_seq_call_le hkS (vs := [heap, graphEnd]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨heap, graphEnd, rfl, hgraphP, by rw [hsizePositive]; omega, hdoubled⟩, hzeroP, ?_⟩
      change graphEnd+(1+2^guest) < 2 ^ w
      omega
    · intro solveEnd memS posS hpostS
      obtain ⟨⟨_, _, hframeS, hzeroS, hreadS⟩, hsolveEnd⟩ := hpostS
      change solveEnd = graphEnd+1+2^guest at hsolveEnd
      change (∀ x < graphEnd, memS x = memP x) at hframeS
      change ZeroFrom memS solveEnd at hzeroS
      change J.positiveInstance.readSolverFlow memS graphEnd = solve J.positiveInstance at hreadS
      have hflowS := solverOutput_listAt J.positiveInstance hreadS
      have hedgeS : ListAt memS (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
        apply (hedge.of_agree_below (h₀ := heap) ?_ hframeP).of_agree_below (h₀ := graphEnd) ?_ hframeS
        all_goals rw [Circulation.solverEdgeRecords_length, List.length_finRange]; rw [hsize] at hend; omega
      have hflowS' : ListAt memS graphEnd ((List.finRange J.m).map (fun e => (solve J.positiveInstance e).toNat)) := by
        rwa [← List.ofFn_eq_map]
      have hsolveEndWord : solveEnd < 2 ^ w := by omega
      refine runs_seq_call_le hkE (vs := [a+2, graphEnd, J.m, solveEnd]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨a+2, graphEnd, solveEnd, by simp only [List.length_finRange], hedgeS, hflowS',
          ?_, ?_, fun e _ => ⟨hinputCapacity e, hflowWord e⟩, hw⟩, hzeroS, ?_⟩
        · rw [List.length_finRange]
          have hend' : a+(2+5*J.m) ≤ heap := by rw [← hsize]; exact hend
          omega
        · rw [List.length_finRange]
          have hlen' := hlenGuest
          rw [hsizePositive] at hlen'
          omega
        · change solveEnd+(List.finRange J.m).length < 2 ^ w
          rw [List.length_finRange]
          omega
      · intro out memE posE hpostE
        obtain ⟨⟨_, _, hframeE, hzeroE, harrayE⟩, hout⟩ := hpostE
        change out = solveEnd+(List.finRange J.m).length at hout
        rw [List.length_finRange] at hout
        change (∀ x < solveEnd, memE x = memS x) at hframeE
        change ZeroFrom memE out at hzeroE
        change ListAt memE solveEnd ((List.finRange J.m).map
          (fun e => if J.capacity e = 0 then 0 else (solve J.positiveInstance e).toNat)) at harrayE
        have hanswer : J.readSolverFlow memE solveEnd = Circulation.solveWithZeroCapacities solve J := by
          have htable : ListAt memE solveEnd (List.ofFn
              (fun e => if J.capacity e = 0 then 0 else (solve J.positiveInstance e).toNat)) := by
            rwa [List.ofFn_eq_map]
          rw [← eraseZeroFlow_unsigned_eq solve J hnonneg]
          funext e
          have h := htable e.val (by simpa only [List.length_ofFn] using e.isLt)
          simp only [List.getElem_ofFn] at h
          change (memE (solveEnd+e.val) : ℤ) = _
          rw [h]
        have houtWord : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap+(3+6*J.m+2^guest) ∧
            (∀ x < heap, memE x = mem x) ∧ ZeroFrom memE out ∧
            J.readSolverFlow memE (heap+3+5*J.m+2^guest) =
              Circulation.solveWithZeroCapacities solve J) ∧ out = heap+3+6*J.m+2^guest
          refine ⟨⟨by omega, by omega, ?_, hzeroE, ?_⟩, by omega⟩
          · intro x hx
            exact (hframeE x (by omega)).trans ((hframeS x (by omega)).trans (hframeP x hx))
          · have heq : heap+3+5*J.m+2^guest = solveEnd := by omega
            rwa [heq]
        · simp only [scratchZeroSolveContract, heapContract, positiveInstanceContract,
            scratchSolveContract, eraseZeroFlowContract, List.length_finRange, argsSize_cons,
            argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]
          change _ ≤ (Q.regBound+6)*T (J.n+1) J.m+
            80*J.positiveInstance.solverWords.length+40*guest+Q.regBound+400*J.m+900
          omega


/-- The outer layout reserves the positive graph, one complete canonical
guest region, and one unsigned result word per original edge. -/
def compressedZeroSolveContract (w : ℕ) (Q : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) : Contract :=
  let guest := wordSize (scratchWordMultiplier c d) J.positiveInstance.solverWords
  let H := heapContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      2 ^ (guest+1)+2 ≤ 2 ^ w)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args+3+5*J.m+2^guest) =
      Circulation.solveWithZeroCapacities ((fun K : Circulation => compressedCanonicalSolverAt
        (wordSize (scratchWordMultiplier c d) K.solverWords) Q f T S (hproc K) K)) J)
    (fun _ _ => (Q.regBound+6)*T (J.n+1) J.m+
      80*J.positiveInstance.solverWords.length+40*guest+Q.regBound+400*J.m+900)
    (fun _ _ => 3+6*J.m+2^guest)
  { H with post := fun args mem out mem' => H.post args mem out mem' ∧
      out = heapArg args+3+6*J.m+2^guest }

/-- Under exactly the bounded-circulation solver specification, the complete
adapter computes the model's exact zero-capacity solve with counted setup,
solver, and erasure work. -/
theorem compressedZeroSolve_meetsContract {w b : ℕ} {Q P : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      Q f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (hdet : Q.IsDeterministic)
    (J : Circulation) (hn : J.n ≤ 2*J.m) (hc : J.CostsBounded (J.m^10)) (hu : ∀ e, J.capacity e ≤ J.m^40)
    (hS : S J.positiveInstance.n J.positiveInstance.m ≤
      c * (J.positiveInstance.n + J.positiveInstance.m + 2)^d)
    (hp : P.HasAt b (scratchZeroSolveModule Q f b c d)) :
    MeetsContract w P b (compressedZeroSolveContract w Q f T S c d hproc J) := by
  let guest := wordSize (scratchWordMultiplier c d) J.positiveInstance.solverWords
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
        (wordSize (scratchWordMultiplier c d) K.solverWords) Q f T S (hproc K) K)
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hpositive := hasAt_append_left hleft
  have hsolve : P.HasAt (b+5) (scratchSolveModule Q f (b+5) c d) := by
    have h := hasAt_append_right hleft
    simpa only [positiveInstanceModule, positiveInstanceEdgesModule, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  have herase : P.HasAt (b+5+(scratchSolveModule Q f (b+5) c d).length)
      (eraseZeroFlowModule (b+5+(scratchSolveModule Q f (b+5) c d).length)) := by
    have h := hasAt_append_right htail
    have hlen : (positiveInstanceModule (b+1)).length = 4 := rfl
    rw [List.length_append] at h
    change P.HasAt (b+1+((positiveInstanceModule (b+1)).length+(scratchSolveModule Q f (b+5) c d).length))
      (eraseZeroFlowModule (b+5+(scratchSolveModule Q f (b+5) c d).length)) at h
    rw [hlen, show b+1+(4+(scratchSolveModule Q f (b+5) c d).length) =
      b+5+(scratchSolveModule Q f (b+5) c d).length by omega] at h
    exact h
  have hcPositive : J.positiveInstance.CostsBounded (J.positiveInstance.m^10) :=
    J.positiveInstance_costsBounded _ hc
  have huPositive : ∀ e, 1 ≤ J.positiveInstance.capacity e ∧
      J.positiveInstance.capacity e ≤ J.positiveInstance.m^40 := by
    intro e
    have hmpos : 0 < J.m := by have h : e.val < J.m := e.isLt; omega
    have hU : 1 ≤ J.m^40 := Nat.pow_pos hmpos
    exact J.positiveInstance_capacitiesBounded (J.m^40) hU hu e
  have hkP := positiveInstance_meetsContract (w := w) hpositive J
  have hkS := compressedSolveModule_meetsContract (w := w) hproc hdet J.positiveInstance (Nat.succ_le_succ hn) hS hcPositive huPositive hsolve
  have hkE := eraseZeroFlow_meetsContract (w := w) herase J
    (fun e => (solve J.positiveInstance e).toNat) (List.finRange J.m)
  have hopt := compressedCanonicalSolverAt_optimal guest Q f T S (hproc J.positiveInstance) J.positiveInstance
  have hnonneg : ∀ e, 0 ≤ solve J.positiveInstance e := by
    intro e
    exact Int.cast_nonneg_iff.mp (hopt.1.2 e).1
  have hflowLe : ∀ e, (solve J.positiveInstance e).toNat ≤ J.positiveInstance.capacity e := by
    intro e
    have hi : solve J.positiveInstance e ≤ (J.positiveInstance.capacity e : ℤ) := by
      have hr : ((solve J.positiveInstance e : ℤ) : ℝ) ≤ (J.positiveInstance.capacity e : ℝ) :=
        (hopt.1.2 e).2
      rw [← Int.cast_natCast] at hr
      exact Int.cast_le.mp hr
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hi
  have hmult : 1 ≤ scratchWordMultiplier c d := by unfold scratchWordMultiplier; omega
  have hlenGuest := length_lt_two_pow_wordSize hmult J.positiveInstance.solverWords
  change J.positiveInstance.solverWords.length < 2 ^ guest at hlenGuest
  have hsize := J.solverWords_length
  have hsizePositive : J.positiveInstance.solverWords.length = 2+5*J.m := J.positiveInstance.solverWords_length
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hdoubled⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(3+6*J.m+2^guest) < 2 ^ w at hspace
  change 2^(guest+1)+2 ≤ 2 ^ w at hdoubled
  have hguestHost : 2^guest < 2 ^ w := by rw [Nat.pow_succ] at hdoubled; omega
  have hnGuest : J.n+1 < 2^guest :=
    lt_two_pow_wordSize_of_mem hmult List.mem_cons_self
  have hn1 : J.n+1 < 2 ^ w := hnGuest.trans hguestHost
  have hw : 8 < 2 ^ w := by rw [hsizePositive] at hlenGuest; omega
  have hm : J.m < 2 ^ w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha : a < 2 ^ w := by rw [hsize] at hend; omega
  have ha1 : a+1 < 2 ^ w := by rw [hsize] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [hsize] at hend; omega
  have hh : heap < 2 ^ w := by omega
  have hhGraph : heap+(2+5*J.m) < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hmcell : mem (a+1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hat 1 (by rw [hsize]; omega)
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hinputCapacity : ∀ e, J.capacity e < 2 ^ w := by
    intro e
    exact hinput _ (Circulation.solverEdgeWord_mem J e (by simp [Circulation.solverEdgeWords]))
  have hflowWord : ∀ e, (solve J.positiveInstance e).toNat < 2 ^ w := by
    intro e
    apply (hflowLe e).trans_lt
    by_cases hz : J.capacity e = 0
    · simpa only [Circulation.positiveInstance, hz, ↓reduceIte] using hone
    · simpa only [Circulation.positiveInstance, hz, ↓reduceIte] using hinputCapacity e
  apply runs_start_le
  unfold zeroCapacitySolveBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [a, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a, heap, rfl, hat, hend, hinput, hn1, hw⟩, hzero, hhGraph⟩
  · intro graphEnd memP posP hpostP
    obtain ⟨⟨_, _, hframeP, hzeroP, hgraphP⟩, hgraphEnd⟩ := hpostP
    change graphEnd = heap+2+5*J.m at hgraphEnd
    change (∀ x < heap, memP x = mem x) at hframeP
    change ZeroFrom memP graphEnd at hzeroP
    change ListAt memP heap J.positiveInstance.solverWords at hgraphP
    have hgraphEndWord : graphEnd < 2 ^ w := by omega
    refine runs_seq_call_le hkS (vs := [heap, graphEnd]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨heap, graphEnd, rfl, hgraphP, by rw [hsizePositive]; omega, hdoubled⟩, hzeroP, ?_⟩
      change graphEnd+(1+2^guest) < 2 ^ w
      omega
    · intro solveEnd memS posS hpostS
      obtain ⟨⟨_, _, hframeS, hzeroS, hreadS⟩, hsolveEnd⟩ := hpostS
      change solveEnd = graphEnd+1+2^guest at hsolveEnd
      change (∀ x < graphEnd, memS x = memP x) at hframeS
      change ZeroFrom memS solveEnd at hzeroS
      change J.positiveInstance.readSolverFlow memS graphEnd = solve J.positiveInstance at hreadS
      have hflowS := solverOutput_listAt J.positiveInstance hreadS
      have hedgeS : ListAt memS (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
        apply (hedge.of_agree_below (h₀ := heap) ?_ hframeP).of_agree_below (h₀ := graphEnd) ?_ hframeS
        all_goals rw [Circulation.solverEdgeRecords_length, List.length_finRange]; rw [hsize] at hend; omega
      have hflowS' : ListAt memS graphEnd ((List.finRange J.m).map (fun e => (solve J.positiveInstance e).toNat)) := by
        rwa [← List.ofFn_eq_map]
      have hsolveEndWord : solveEnd < 2 ^ w := by omega
      refine runs_seq_call_le hkE (vs := [a+2, graphEnd, J.m, solveEnd]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨a+2, graphEnd, solveEnd, by simp only [List.length_finRange], hedgeS, hflowS',
          ?_, ?_, fun e _ => ⟨hinputCapacity e, hflowWord e⟩, hw⟩, hzeroS, ?_⟩
        · rw [List.length_finRange]
          have hend' : a+(2+5*J.m) ≤ heap := by rw [← hsize]; exact hend
          omega
        · rw [List.length_finRange]
          have hlen' := hlenGuest
          rw [hsizePositive] at hlen'
          omega
        · change solveEnd+(List.finRange J.m).length < 2 ^ w
          rw [List.length_finRange]
          omega
      · intro out memE posE hpostE
        obtain ⟨⟨_, _, hframeE, hzeroE, harrayE⟩, hout⟩ := hpostE
        change out = solveEnd+(List.finRange J.m).length at hout
        rw [List.length_finRange] at hout
        change (∀ x < solveEnd, memE x = memS x) at hframeE
        change ZeroFrom memE out at hzeroE
        change ListAt memE solveEnd ((List.finRange J.m).map
          (fun e => if J.capacity e = 0 then 0 else (solve J.positiveInstance e).toNat)) at harrayE
        have hanswer : J.readSolverFlow memE solveEnd = Circulation.solveWithZeroCapacities solve J := by
          have htable : ListAt memE solveEnd (List.ofFn
              (fun e => if J.capacity e = 0 then 0 else (solve J.positiveInstance e).toNat)) := by
            rwa [List.ofFn_eq_map]
          rw [← eraseZeroFlow_unsigned_eq solve J hnonneg]
          funext e
          have h := htable e.val (by simpa only [List.length_ofFn] using e.isLt)
          simp only [List.getElem_ofFn] at h
          change (memE (solveEnd+e.val) : ℤ) = _
          rw [h]
        have houtWord : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap+(3+6*J.m+2^guest) ∧
            (∀ x < heap, memE x = mem x) ∧ ZeroFrom memE out ∧
            J.readSolverFlow memE (heap+3+5*J.m+2^guest) =
              Circulation.solveWithZeroCapacities solve J) ∧ out = heap+3+6*J.m+2^guest
          refine ⟨⟨by omega, by omega, ?_, hzeroE, ?_⟩, by omega⟩
          · intro x hx
            exact (hframeE x (by omega)).trans ((hframeS x (by omega)).trans (hframeP x hx))
          · have heq : heap+3+5*J.m+2^guest = solveEnd := by omega
            rwa [heq]
        · simp only [compressedZeroSolveContract, heapContract, positiveInstanceContract,
            compressedSolveContract, eraseZeroFlowContract, List.length_finRange, argsSize_cons,
            argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]
          change _ ≤ (Q.regBound+6)*T (J.n+1) J.m+
            80*J.positiveInstance.solverWords.length+40*guest+Q.regBound+400*J.m+900
          omega

end MinCostFlow.Final
