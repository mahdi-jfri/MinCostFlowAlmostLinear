module

public import MinCostFlow.Scaling.ShiftedEdgesProgram
public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Building the graph after removing lower capacities

The first graph transformation in the general-flow reduction of Lemma C.1
of Chen et al., arXiv:2203.00671v2, retains the input dimensions and endpoints
and subtracts lower capacities. This procedure reads `Instance.encode`,
writes the two-word circulation header, and runs the shifted-edge scan.
Its output is exactly `shiftedGraph.solverWords`, in linear edge time.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[inputAddress,heap]`. -/
def shiftedGraphBody (header scan : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 header [.reg 2, .reg 3, .reg 1] ;;
  .call 5 scan [.bin .add (.reg 0) (.const 2), .reg 3, .reg 4] ;;
  .ret (.reg 5)

/-- The graph entry, header writer, and shifted-edge scan. -/
def shiftedGraphModule (b : ℕ) : List Stmt :=
  shiftedGraphBody (b + 1) (b + 2) :: wordPairBody :: shiftedEdgesModule (b + 2)

/-- The exact solver-layout encoding of the graph after subtracting lower
capacities, with no change to the stored original input. -/
def shiftedGraphContract (w : ℕ) (I : Instance) (hv : I.IsValid) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a I.encode ∧
      a + I.encode.length ≤ h ∧ (∀ e ∈ I.edges, e.lower ≤ e.upper) ∧
      (∀ e ∈ I.edges, e.lower.natAbs + e.upper.natAbs < 2 ^ w) ∧
      (∀ x ∈ I.encode, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (FlowReduction.shiftedGraph I hv).solverWords)
    (fun _ _ => 400 * I.m + 200) (fun _ _ => 2 + 5 * I.m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 + 5 * I.m }

/-- All procedures of the graph transformation have no random instructions. -/
theorem shiftedGraphModule_noRand (b : ℕ) :
    ∀ body ∈ shiftedGraphModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [shiftedGraphBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · exact shiftedEdgesModule_noRand _ body hb

/-- The graph-building procedure computes exactly `shiftedGraph`, preserves
the heap frame, and takes at most `400*m+200` steps. -/
theorem shiftedGraph_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (shiftedGraphModule b)) (I : Instance) (hv : I.IsValid) :
    MeetsContract w p b (shiftedGraphContract w I hv) := by
  have hheader : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [shiftedGraphModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [shiftedGraphModule])
  have hscan : p.HasAt (b + 2) (shiftedEdgesModule (b + 2)) := by
    intro i hi
    have h := hp (i + 1 + 1) (by simp only [shiftedGraphModule, List.length_cons]; omega)
    have hidx : b + (i + 1 + 1) = b + 2 + i := by omega
    rw [hidx] at h
    simpa only [shiftedGraphModule, List.getElem_cons_succ] using h
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkS := shiftedEdges_meetsContract (w := w) hscan I.edges
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, horder, hsum, hinput, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (2 + 5 * I.m) < 2 ^ w at hspace
  have hlength := instance_encode_length I hv
  have hhead := instance_header_at I mem a hat
  have hN := hhead.1
  have hM := hhead.2
  have hedges := instance_edges_at I mem a hat
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hn : I.n < 2 ^ w := hinput _ (List.mem_cons_self)
  have hm : I.m < 2 ^ w := hinput _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have hheap2 : heap + 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold shiftedGraphBody
  refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [I.n, I.m, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨I.n, I.m, heap, rfl⟩, hzero, hheap2⟩
  · intro edgeHeap memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hptr⟩ := hpostH
    change edgeHeap = heap + 2 at hptr
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH edgeHeap at hzeroH
    change ListAt memH heap [I.n, I.m] at hheaderH
    have hedgeH : ListAt memH (a + 2) (I.edges.flatMap Edge.encode) := by
      apply hedges.of_agree_below (h₀ := heap)
      · rw [edges_encode_length]
        change a + 2 + 8 * I.m ≤ heap
        omega
      · exact hframeH
    have hedgeheap : edgeHeap < 2 ^ w := by omega
    refine runs_seq_call_le hkS (vs := [a + 2, I.edges.length, edgeHeap]) (by eval_expr) ?_ ?_ ?_
    · change ∀ x ∈ [a + 2, I.m, edgeHeap], x < 2 ^ w
      wram_words
    · refine ⟨⟨a + 2, edgeHeap, rfl, hedgeH, ?_, horder, hsum, ?_, hw⟩, hzeroH, ?_⟩
      · change a + 2 + 8 * I.m ≤ edgeHeap
        omega
      · intro x hx
        exact hinput x (instance_edges_word_mem I hx)
      · change edgeHeap + 5 * I.m < 2 ^ w
        omega
    · intro out memS posS hpostS
      obtain ⟨⟨_, _, hframeS, hzeroS, hrecords⟩, hout⟩ := hpostS
      change (∀ x < edgeHeap, memS x = memH x) at hframeS
      change ZeroFrom memS out at hzeroS
      change ListAt memS edgeHeap (I.edges.flatMap shiftedEdgeWords) at hrecords
      change out = edgeHeap + 5 * I.m at hout
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + (2 + 5 * I.m) ∧
          (∀ x < heap, memS x = mem x) ∧ ZeroFrom memS out ∧
          ListAt memS heap (FlowReduction.shiftedGraph I hv).solverWords) ∧
          out = heap + 2 + 5 * I.m
        refine ⟨⟨by omega, by omega, ?_, hzeroS, ?_⟩, by omega⟩
        · intro x hx
          exact (hframeS x (by omega)).trans (hframeH x hx)
        · rw [shiftedGraph_solverWords]
          have hheaderS : ListAt memS heap [I.n, I.m] := by
            apply hheaderH.of_agree_below (h₀ := edgeHeap)
            · change heap + 2 ≤ edgeHeap
              omega
            · exact hframeS
          exact listAt_append.mpr ⟨hheaderS, by simpa only [List.flatMap, List.length_cons, List.length_nil, Nat.reduceAdd, hptr] using hrecords⟩
      · simp only [shiftedGraphContract, heapContract, shiftedEdgesContract,
          wordPairContract, argsSize_cons, argsSize_nil, Expr.size_load,
          Expr.size_bin, Expr.size_reg, Expr.size_const]
        change _ ≤ 400 * I.edges.length + 200
        omega

/-- Every valid input with consistent capacities has a concrete memory
satisfying all graph-building premises at one sufficiently large width. -/
theorem exists_shiftedGraph_pre (I : Instance) (hv : I.IsValid)
    (horder : ∀ e ∈ I.edges, e.lower ≤ e.upper) :
    ∃ w, (∀ x ∈ [0, I.encode.length], x < 2 ^ w) ∧
      (shiftedGraphContract w I hv).pre [0, I.encode.length] (initMem I.encode) := by
  let input := I.encode ++
    ((I.edges.map fun e => e.lower.natAbs + e.upper.natAbs) ++
      [I.encode.length + 2 + 5 * I.m + 10])
  let w := wordSize 1 input
  have hlarge : I.encode.length + 2 + 5 * I.m + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self)))
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · refine ⟨⟨0, I.encode.length, rfl, listAt_initMem _, by omega, horder,
      ?_, ?_, by omega⟩, zeroFrom_initMem _, ?_⟩
    · intro e he
      exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
    · intro x hx
      exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
    · change I.encode.length + (2 + 5 * I.m) < 2 ^ w
      omega

/-- The complete module occupies exactly 5 procedure slots. -/
theorem shiftedGraphModule_length (b : ℕ) : (shiftedGraphModule b).length = 5 := rfl

end MinCostFlow.Scaling.Machine
