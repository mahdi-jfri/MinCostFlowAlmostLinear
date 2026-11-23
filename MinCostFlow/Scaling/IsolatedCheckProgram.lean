module

public import MinCostFlow.Scaling.IsolatedScanProgram
public import MinCostFlow.Scaling.EndpointLabelsProgram
public import MinCostFlow.Scaling.IsolatedDemands
public import MinCostFlow.Scaling.InputMagnitudeBounds
public import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Checking isolated demands from encoded reduction inputs

The general-flow reduction in Lemma C.1 of Chen et al., arXiv:2203.00671v2,
rejects a nonzero demand at an isolated vertex before making a solver call.
This procedure computes endpoint labels from the shifted graph and compares
them with the original encoded demand magnitudes. It computes exactly
`isolatedCheck`, preserving the original input and storing the result in
the padding cell of the new label table. The graph is an explicit stored
input, not a hypothesis about an algorithm's output.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The two stored fields tested per vertex express exactly the model check. -/
theorem isolatedCheck_rows_iff (I : Instance) (hv : I.IsValid) :
    (∀ r ∈ (List.ofFn fun v : Fin I.n =>
      ((FlowReduction.shiftedGraph I hv).endpointLabels.table v, (I.d v).natAbs)),
      0 < r.1 ∨ r.2 = 0) ↔ FlowReduction.isolatedCheck I hv = true := by
  rw [FlowReduction.isolatedCheck_iff]
  constructor
  · intro h v
    have hh := h _ (List.mem_ofFn.mpr ⟨v, rfl⟩)
    rcases hh with hp | hz
    · exact Or.inl hp
    · exact Or.inr (by omega)
  · intro h r hr
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hr
    rcases h v with hp | hz
    · exact Or.inl hp
    · exact Or.inr (by rw [hz]; rfl)

/-- Arguments `[originalInput,shiftedGraph,heap]`. -/
def isolatedCheckBody (labels scan : ℕ) : Stmt :=
  .call 3 labels [.reg 1, .reg 2] ;;
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 6 scan [.bin .add (.reg 2) (.const 2),
    .bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 8) (.reg 5)), .reg 4] ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 6) ;;
  .ret (.reg 3)

/-- Entry, endpoint labeling, and the read-only isolated-demand scan. -/
def isolatedCheckModule (b : ℕ) : List Stmt :=
  isolatedCheckBody (b + 1) (b + 4) ::
    (endpointLabelsModule (b + 1) ++ isolatedScanModule (b + 4))

/-- The flag is at `heap+1`, the label count at `heap`, and labels at
`heap+2`. The return value is the exact end of this allocated label block. -/
def isolatedCheckContract (w : ℕ) (I : Instance) (hv : I.IsValid) : Contract :=
  let J := FlowReduction.shiftedGraph I hv
  let C := heapContract w
    (fun args mem => ∃ a graph heap, args = [a, graph, heap] ∧
      ListAt mem a I.encode ∧ ListAt mem graph J.solverWords ∧
      a + I.encode.length ≤ heap ∧ graph + J.solverWords.length ≤ heap ∧
      (∀ x ∈ I.encode, x < 2 ^ w) ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' =>
      mem' (heapArg args + 1) = (if FlowReduction.isolatedCheck I hv then 1 else 0) ∧
      mem' (heapArg args) = J.endpointLabels.count ∧
      LabelsAt mem' (heapArg args + 2) J.endpointLabels)
    (fun _ _ => 160 * I.m + 100 * I.n + 400) (fun _ _ => I.n + 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 + I.n }

/-- Neither the entry nor any helper uses random instructions. -/
theorem isolatedCheckModule_noRand (b : ℕ) :
    ∀ body ∈ isolatedCheckModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [isolatedCheckBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact endpointLabelsModule_noRand _ body hb
    · have he := List.mem_singleton.mp hb
      subst body
      exact isolatedScanBody_noRand _

/-- The machine computes precisely the model's isolated-demand rejection
flag and retains the computed labels, in linear time and exact space. -/
theorem isolatedCheck_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (isolatedCheckModule b)) (I : Instance) (hv : I.IsValid) :
    MeetsContract w p b (isolatedCheckContract w I hv) := by
  have hparts := hasAt_tail hp
  have hlabels := hasAt_append_left hparts
  have hscan : p.HasAt (b + 4) (isolatedScanModule (b + 4)) := by
    simpa only [endpointLabelsModule, vertexScanModule, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.add_assoc] using hasAt_append_right hparts
  let J := FlowReduction.shiftedGraph I hv
  let rows := List.ofFn fun v : Fin I.n => (J.endpointLabels.table v, (I.d v).natAbs)
  have hkS := isolatedScan_meetsContract (w := w) hscan rows
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, graph, heap, rfl, hat, hgraph, hend, hgraphend, hinput, hgraphwords, hw⟩,
    hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (I.n + 2) < 2 ^ w at hspace
  have hkL := endpointLabels_meetsContract hw hlabels J
  have hlength := instance_encode_length I hv
  have ha : a < 2 ^ w := by omega
  have hg : graph < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hh : heap < 2 ^ w := by omega
  have hn : I.n < 2 ^ w := by omega
  have hm : I.m < 2 ^ w := hinput _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have h2m : 2 * I.m < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha3 : a + 3 < 2 ^ w := by omega
  have h8m : 8 * I.m < 2 ^ w := by omega
  have hmagbase : a + 3 + 8 * I.m < 2 ^ w := by omega
  have hlabelbase : heap + 2 < 2 ^ w := by omega
  have hflagbase : heap + 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold isolatedCheckBody
  refine runs_seq_call_le hkL (vs := [graph, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨graph, heap, rfl, hgraph, hgraphend, hgraphwords⟩, hzero, hspace⟩
  · intro out memL posL hpostL
    obtain ⟨⟨_, _, hframeL, hzeroL, hcountL, htableL⟩, hptr⟩ := hpostL
    change out = heap + 2 + I.n at hptr
    change (∀ x < heap, memL x = mem x) at hframeL
    change ZeroFrom memL out at hzeroL
    change memL heap = J.endpointLabels.count at hcountL
    change LabelsAt memL (heap + 2) J.endpointLabels at htableL
    have houtword : out < 2 ^ w := by omega
    have hatL := hat.of_agree_below hend hframeL
    have hheader := instance_header_at I memL a hatL
    have hN := hheader.1
    have hM := hheader.2
    have hlabelval : ∀ v, J.endpointLabels.table v < 2 ^ w := by
      intro v
      have h1 := J.endpointLabels_valid.1 v
      have h2 := J.endpointLabels_count_le
      change J.endpointLabels.count ≤ 2 * I.m at h2
      omega
    have hrowslabel : ∀ i (hi : i < rows.length), memL (heap + 2 + i) = (rows[i]'hi).1 := by
      intro i hi
      have hi' : i < I.n := by simpa only [rows, List.length_ofFn] using hi
      have he : (rows[i]'hi) = (J.endpointLabels.table ⟨i, hi'⟩, (I.d i).natAbs) := by
        simp only [rows, List.getElem_ofFn]
      rw [he]
      exact htableL ⟨i, hi'⟩
    have hrowsmag : ∀ i (hi : i < rows.length), memL (a + 3 + 8 * I.m + 2 * i) = (rows[i]'hi).2 := by
      intro i hi
      have hi' : i < I.n := by simpa only [rows, List.length_ofFn] using hi
      have he : (rows[i]'hi) = (J.endpointLabels.table ⟨i, hi'⟩, (I.d i).natAbs) := by
        simp only [rows, List.getElem_ofFn]
      rw [he]
      have hh := demand_magnitude_at I hv memL a hatL ⟨i, hi'⟩
      have haddr : a + 3 + 8 * I.m + 2 * i = a + (2 + 8 * I.m + 2 * i + 1) := by omega
      rwa [haddr]
    have hrowsword : ∀ r ∈ rows, r.1 < 2 ^ w ∧ r.2 < 2 ^ w := by
      intro r hr
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hr
      exact ⟨hlabelval v, hinput _ (demand_natAbs_word_mem I hv v)⟩
    refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
    refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
    refine runs_seq_call_le hkS (vs := [heap + 2, a + 3 + 8 * I.m, I.n]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨heap + 2, a + 3 + 8 * I.m, ?_, hrowslabel, hrowsmag, ?_, ?_, hrowsword, by omega⟩
      · simp only [rows, List.length_ofFn]
      · simp only [rows, List.length_ofFn]
        omega
      · simp only [rows, List.length_ofFn]
        omega
    · intro flag memS posS hpostS
      obtain ⟨hmemS, hflag⟩ := hpostS
      change memS = memL at hmemS
      subst memS
      change flag = if ∀ r ∈ rows, 0 < r.1 ∨ r.2 = 0 then 1 else 0 at hflag
      have hiff := isolatedCheck_rows_iff I hv
      change (∀ r ∈ rows, 0 < r.1 ∨ r.2 = 0) ↔ FlowReduction.isolatedCheck I hv = true at hiff
      simp only [hiff] at hflag
      have hflagword : flag < 2 ^ w := by split_ifs at hflag <;> omega
      refine runs_seq_store_le (by eval_expr) (v := flag) (by eval_expr) ?_
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + (I.n + 2) ∧
          (∀ x < heap, Function.update memL (heap + 1) flag x = mem x) ∧
          ZeroFrom (Function.update memL (heap + 1) flag) out ∧
          (Function.update memL (heap + 1) flag (heap + 1) =
            (if FlowReduction.isolatedCheck I hv then 1 else 0) ∧
            Function.update memL (heap + 1) flag heap = J.endpointLabels.count ∧
            LabelsAt (Function.update memL (heap + 1) flag) (heap + 2) J.endpointLabels)) ∧
          out = heap + 2 + I.n
        refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, hptr⟩
        · intro x hx
          rw [Function.update_of_ne (by omega : x ≠ heap + 1)]
          exact hframeL x hx
        · intro x hx
          rw [Function.update_of_ne (by omega : x ≠ heap + 1)]
          exact hzeroL x hx
        · refine ⟨by simpa only [Function.update_self] using hflag,
            by simpa only [Function.update_of_ne (by omega : heap ≠ heap + 1)] using hcountL, ?_⟩
          intro v
          rw [Function.update_of_ne (by omega : heap + 2 + v.val ≠ heap + 1)]
          exact htableL v
      · simp only [isolatedCheckContract, heapContract, endpointLabelsContract,
          isolatedScanContract, rows, List.length_ofFn, argsSize_cons, argsSize_nil,
          Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
        have hJm : J.m = I.m := rfl
        omega

/-- Every valid original instance and its exact shifted graph can satisfy
all input, word, and fresh-heap premises together on a concrete memory. -/
theorem exists_isolatedCheck_pre (I : Instance) (hv : I.IsValid) :
    ∃ w mem, (∀ x ∈ [0, I.encode.length,
        I.encode.length + (FlowReduction.shiftedGraph I hv).solverWords.length], x < 2 ^ w) ∧
      (isolatedCheckContract w I hv).pre
        [0, I.encode.length, I.encode.length + (FlowReduction.shiftedGraph I hv).solverWords.length] mem := by
  let J := FlowReduction.shiftedGraph I hv
  let words := I.encode ++ J.solverWords
  let mem := initMem words
  let input := words ++ [words.length + I.n + 12]
  let w := wordSize 1 input
  have hlarge : words.length + I.n + 12 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ (List.mem_cons_self))
  have hlen : words.length = I.encode.length + J.solverWords.length := List.length_append
  have hstored := listAt_append.mp (listAt_initMem words)
  have hgraph : ListAt mem I.encode.length J.solverWords := by
    simpa only [Nat.zero_add] using hstored.2
  refine ⟨w, mem, ?_, ?_⟩
  · change ∀ x ∈ [0, I.encode.length, I.encode.length + J.solverWords.length], x < 2 ^ w
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · refine ⟨⟨0, I.encode.length, I.encode.length + J.solverWords.length,
      rfl, hstored.1, hgraph, by omega, le_rfl, ?_, ?_, by omega⟩, ?_, ?_⟩
    · intro x hx
      exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_left _ (List.mem_append_left _ hx))
    · intro x hx
      exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_left _ (List.mem_append_right _ hx))
    · change ZeroFrom mem (I.encode.length + J.solverWords.length)
      rw [← hlen]
      exact zeroFrom_initMem words
    · change I.encode.length + J.solverWords.length + (I.n + 2) < 2 ^ w
      omega

/-- The isolated-demand check occupies five procedure slots. -/
theorem isolatedCheckModule_length (b : ℕ) : (isolatedCheckModule b).length = 5 := rfl

end MinCostFlow.Scaling.Machine
