module

public import MinCostFlow.Scaling.DemandOldEdgesProgram
public import MinCostFlow.Scaling.DemandArcsProgram
public import MinCostFlow.Scaling.SignedTableLayout
public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Building the complete feasibility circulation

The demand-to-circulation reduction of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, adds a root and two ordered artificial arc blocks.
This procedure writes the new header, copies the old edges with zero costs,
and writes the positive and negative demand arcs. It computes exactly
`Circulation.demandInstance`, including zero-capacity slots, and has linear
cost in the input vertices and edges.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[circulationAddress,demandTable,heap]`. -/
def demandInstanceBody (header old positive negative : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 header [.bin .add (.reg 3) (.const 1),
    .bin .add (.reg 4) (.bin .add (.reg 3) (.reg 3)), .reg 2] ;;
  .call 6 old [.bin .add (.reg 0) (.const 2), .reg 4, .reg 5] ;;
  .call 7 positive [.reg 1, .reg 3, .const 0, .reg 3, .reg 6] ;;
  .call 8 negative [.reg 1, .reg 3, .const 0, .reg 3, .reg 7] ;;
  .ret (.reg 8)

/-- The feasibility constructor and the four proved writing modules. -/
def demandInstanceModule (b : ℕ) : List Stmt :=
  demandInstanceBody (b + 1) (b + 2) (b + 4) (b + 7) :: wordPairBody ::
    (demandOldEdgesModule (b + 2) ++
      (demandArcsModule false (b + 4) ++ demandArcsModule true (b + 7)))

/-- Both inputs precede the fresh output. The postcondition is exactly the
common solver encoding of the model's demand instance. -/
def demandInstanceContract (w : ℕ) (J : Circulation) (d : Fin J.n → ℤ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a table heap, args = [a, table, heap] ∧
      ListAt mem a J.solverWords ∧ SignedTableAt mem table d ∧
      a + J.solverWords.length ≤ heap ∧ table + 2 * J.n ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ (∀ v, (d v).natAbs < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (J.demandInstance d).solverWords)
    (fun _ _ => 200 * J.m + 500 * J.n + 200)
    (fun _ _ => 2 + 5 * J.m + 10 * J.n)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 + 5 * J.m + 10 * J.n }

/-- The complete feasibility constructor has no random instructions. -/
theorem demandInstanceModule_noRand (b : ℕ) :
    ∀ body ∈ demandInstanceModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [demandInstanceBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · rcases List.mem_append.mp hb with hb | hb
      · exact demandOldEdgesModule_noRand _ body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact demandArcsModule_noRand _ _ body hb
        · exact demandArcsModule_noRand _ _ body hb

/-- The machine writes the exact feasibility circulation, in the model's
edge order, with exact space, heap framing, and explicit linear cost. -/
theorem demandInstance_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (demandInstanceModule b)) (J : Circulation) (d : Fin J.n → ℤ) :
    MeetsContract w p b (demandInstanceContract w J d) := by
  have htail := hasAt_tail hp
  have hheader : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, Nat.add_zero, List.getElem_cons_zero] using htail.head
  have hparts : p.HasAt (b + 2)
      (demandOldEdgesModule (b + 2) ++
        (demandArcsModule false (b + 4) ++ demandArcsModule true (b + 7))) := by
    simpa only [Nat.add_assoc] using hasAt_tail htail
  have hold := hasAt_append_left hparts
  have harcs : p.HasAt (b + 4)
      (demandArcsModule false (b + 4) ++ demandArcsModule true (b + 7)) := by
    simpa only [demandOldEdgesModule, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.add_assoc] using hasAt_append_right hparts
  have hpositive := hasAt_append_left harcs
  have hnegative : p.HasAt (b + 7) (demandArcsModule true (b + 7)) := by
    simpa only [demandArcsModule, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.add_assoc] using hasAt_append_right harcs
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkO := demandOldEdges_meetsContract (w := w) hold J (List.finRange J.m)
  have hkP := demandArcs_meetsContract (w := w) false hpositive J.n 0 (List.ofFn d)
  have hkN := demandArcs_meetsContract (w := w) true hnegative J.n 0 (List.ofFn d)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, table, heap, rfl, hat, htable, hend, htableend, hinput, hdemands, hw⟩,
    hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (2 + 5 * J.m + 10 * J.n) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have hN : mem a = J.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using hat 0 (by rw [hsize]; omega)
  have hM : mem (a + 1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using hat 1 (by rw [hsize]; omega)
  have holdinput : ListAt mem (a + 2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have hh := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using hh
  have htableinput := htable.listAt
  have ha : a < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have htableword : table < 2 ^ w := by omega
  have hheap : heap < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := by omega
  have hn1 : J.n + 1 < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have h2n : J.n + J.n < 2 ^ w := by omega
  have hnewm : J.m + (J.n + J.n) < 2 ^ w := by omega
  have hheap2 : heap + 2 < 2 ^ w := by omega
  have hvertices : J.n + 0 + (List.ofFn d).length + 2 < 2 ^ w := by
    simp only [List.length_ofFn]
    omega
  have hmags : ∀ z ∈ List.ofFn d, z.natAbs < 2 ^ w := by
    intro z hz
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hz
    exact hdemands v
  apply runs_start_le
  unfold demandInstanceBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [J.n + 1, J.m + (J.n + J.n), heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_, _, heap, rfl⟩, hzero, hheap2⟩
  · intro heapH memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hptrH⟩ := hpostH
    change heapH = heap + 2 at hptrH
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH heapH at hzeroH
    change ListAt memH heap [J.n + 1, J.m + (J.n + J.n)] at hheaderH
    have hheapH : heapH < 2 ^ w := by omega
    have holdH : ListAt memH (a + 2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
      apply holdinput.of_agree_below (h₀ := heap)
      · rw [J.solverEdgeRecords_length, List.length_finRange]
        omega
      · exact hframeH
    have htableH := htableinput.of_agree_below (h₀ := heap)
      (by simpa only [integers_encode_length, List.length_ofFn] using htableend) hframeH
    refine runs_seq_call_le hkO (vs := [a + 2, J.m, heapH]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨a + 2, heapH, ?_, holdH, ?_, ?_, hw⟩, hzeroH, ?_⟩
      · simp only [List.length_finRange]
      · simp only [List.length_finRange]
        omega
      · intro e _ x hx
        exact hinput x (J.solverEdgeWord_mem e hx)
      · change heapH + 5 * (List.finRange J.m).length < 2 ^ w
        simp only [List.length_finRange]
        omega
    · intro heapO memO posO hpostO
      obtain ⟨⟨_, _, hframeO, hzeroO, holdO⟩, hptrO⟩ := hpostO
      change heapO = heapH + 5 * (List.finRange J.m).length at hptrO
      rw [List.length_finRange] at hptrO
      change (∀ x < heapH, memO x = memH x) at hframeO
      change ZeroFrom memO heapO at hzeroO
      change ListAt memO heapH ((List.finRange J.m).flatMap (demandOldEdgeWords J)) at holdO
      have hheapO : heapO < 2 ^ w := by omega
      have htableO := htableH.of_agree_below (h₀ := heapH)
        (by simp only [integers_encode_length, List.length_ofFn]; omega) hframeO
      refine runs_seq_call_le hkP (vs := [table, J.n, 0, J.n, heapO]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨table, heapO, ?_, htableO, ?_, hvertices, hmags, hw⟩, hzeroO, ?_⟩
        · simp only [List.length_ofFn]
        · simp only [List.length_ofFn]
          omega
        · change heapO + 5 * (List.ofFn d).length < 2 ^ w
          simp only [List.length_ofFn]
          omega
      · intro heapP memP posP hpostP
        obtain ⟨⟨_, _, hframeP, hzeroP, hpositiveP⟩, hptrP⟩ := hpostP
        change heapP = heapO + 5 * (List.ofFn d).length at hptrP
        rw [List.length_ofFn] at hptrP
        change (∀ x < heapO, memP x = memO x) at hframeP
        change ZeroFrom memP heapP at hzeroP
        change ListAt memP heapO (demandArcRecords J.n false 0 (List.ofFn d)) at hpositiveP
        have hheapP : heapP < 2 ^ w := by omega
        have htableP := htableO.of_agree_below (h₀ := heapO)
          (by simp only [integers_encode_length, List.length_ofFn]; omega) hframeP
        refine runs_seq_call_le hkN (vs := [table, J.n, 0, J.n, heapP]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · refine ⟨⟨table, heapP, ?_, htableP, ?_, hvertices, hmags, hw⟩, hzeroP, ?_⟩
          · simp only [List.length_ofFn]
          · simp only [List.length_ofFn]
            omega
          · change heapP + 5 * (List.ofFn d).length < 2 ^ w
            simp only [List.length_ofFn]
            omega
        · intro out memN posN hpostN
          obtain ⟨⟨_, _, hframeN, hzeroN, hnegativeN⟩, hout⟩ := hpostN
          change out = heapP + 5 * (List.ofFn d).length at hout
          rw [List.length_ofFn] at hout
          change (∀ x < heapP, memN x = memP x) at hframeN
          change ZeroFrom memN out at hzeroN
          change ListAt memN heapP (demandArcRecords J.n true 0 (List.ofFn d)) at hnegativeN
          have houtword : out < 2 ^ w := by omega
          have hheaderN : ListAt memN heap [J.n + 1, J.m + (J.n + J.n)] := by
            apply hheaderH.of_agree_below (h₀ := heapH) (by change heap + 2 ≤ heapH; omega)
            intro x hx
            exact (hframeN x (by omega)).trans ((hframeP x (by omega)).trans (hframeO x hx))
          have holdN : ListAt memN heapH ((List.finRange J.m).flatMap (demandOldEdgeWords J)) := by
            apply holdO.of_agree_below (h₀ := heapO)
            · rw [demandOldRecords_length, List.length_finRange]
              omega
            · intro x hx
              exact (hframeN x (by omega)).trans (hframeP x hx)
          have hpositiveN : ListAt memN heapO (demandArcRecords J.n false 0 (List.ofFn d)) :=
            hpositiveP.of_agree_below (h₀ := heapP)
              (by rw [demandArcRecords_length, List.length_ofFn]; omega) hframeN
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + (2 + 5 * J.m + 10 * J.n) ∧
              (∀ x < heap, memN x = mem x) ∧ ZeroFrom memN out ∧
              ListAt memN heap (J.demandInstance d).solverWords) ∧
              out = heap + 2 + 5 * J.m + 10 * J.n
            refine ⟨⟨by omega, by omega, ?_, hzeroN, ?_⟩, by omega⟩
            · intro x hx
              exact (hframeN x (by omega)).trans
                ((hframeP x (by omega)).trans ((hframeO x (by omega)).trans (hframeH x hx)))
            · rw [demandInstance_solverWords]
              have holdEq : (List.ofFn (demandOldEdgeWords J)).flatten =
                  (List.finRange J.m).flatMap (demandOldEdgeWords J) := by
                rw [List.flatMap, ← List.ofFn_eq_map]
              rw [holdEq]
              apply (listAt_append (l₁ := [J.n + 1, J.m + (J.n + J.n)])).mpr
              refine ⟨hheaderN, ?_⟩
              have hstart : heap + [J.n + 1, J.m + (J.n + J.n)].length = heapH := by
                change heap + 2 = heapH
                omega
              rw [hstart]
              apply listAt_append.mpr
              refine ⟨holdN, ?_⟩
              rw [demandOldRecords_length, List.length_finRange]
              have hstartO : heapH + 5 * J.m = heapO := by omega
              rw [hstartO]
              apply listAt_append.mpr
              refine ⟨hpositiveN, ?_⟩
              rw [demandArcRecords_length, List.length_ofFn]
              have hstartP : heapO + 5 * J.n = heapP := by omega
              rwa [hstartP]
          · simp only [demandInstanceContract, heapContract, wordPairContract,
              demandOldEdgesContract, demandArcsContract, List.length_finRange, List.length_ofFn,
              argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega

/-- Every circulation and signed demand vector have a concrete joint input
memory and width satisfying the feasibility constructor's full precondition. -/
theorem exists_demandInstance_pre (J : Circulation) (d : Fin J.n → ℤ) :
    ∃ w mem, (∀ x ∈ [0, J.solverWords.length, J.solverWords.length + 2 * J.n], x < 2 ^ w) ∧
      (demandInstanceContract w J d).pre
        [0, J.solverWords.length, J.solverWords.length + 2 * J.n] mem := by
  let demands := (List.ofFn d).flatMap encodeInt
  let mem := initMem (J.solverWords ++ demands)
  let input := J.solverWords ++
    (((List.ofFn d).map Int.natAbs) ++ [J.solverWords.length + 5 * J.m + 12 * J.n + 20])
  let w := wordSize 1 input
  have hlarge : J.solverWords.length + 5 * J.m + 12 * J.n + 20 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self)))
  have hstored := listAt_append.mp (listAt_initMem (J.solverWords ++ demands))
  have htable : SignedTableAt mem J.solverWords.length d := by
    apply signedTableAt_of_listAt
    simpa only [Nat.zero_add] using hstored.2
  have hzero : ZeroFrom mem (J.solverWords.length + 2 * J.n) := by
    simpa only [List.length_append, demands, integers_encode_length, List.length_ofFn] using
      zeroFrom_initMem (J.solverWords ++ demands)
  refine ⟨w, mem, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · refine ⟨⟨0, J.solverWords.length, J.solverWords.length + 2 * J.n, rfl,
      hstored.1, htable, by omega, le_rfl, ?_, ?_, by omega⟩, hzero, ?_⟩
    · intro x hx
      exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
    · intro v
      exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map.mpr ⟨d v, List.mem_ofFn.mpr ⟨v, rfl⟩, rfl⟩)))
    · change J.solverWords.length + 2 * J.n + (2 + 5 * J.m + 10 * J.n) < 2 ^ w
      omega

/-- The complete module occupies exactly 10 procedure slots. -/
theorem demandInstanceModule_length (b : ℕ) : (demandInstanceModule b).length = 10 := rfl

end MinCostFlow.Scaling.Machine
