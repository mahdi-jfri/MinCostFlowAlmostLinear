module

public import MinCostFlow.Scaling.DemandStepProgram
public import MinCostFlow.Scaling.DemandScanBounds
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# The lower-capacity demand scan

The general-flow reduction of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
scans the input edges and applies their lower-capacity contributions in
order. This procedure computes exactly `scanDemands` on a stored signed
table. A bound `B` on current magnitudes grows by at most `2*L` per edge,
where `L` bounds the lower capacities. It allocates six scratch words per
edge and takes at most `700*edgeCount+20` machine steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[firstEdge,edgeCount,table,heap]`. -/
def demandScanBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 3))
    (.call 4 step [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
      .load (.bin .add (.reg 0) (.const 2)), .load (.bin .add (.reg 0) (.const 3)),
      .reg 2, .reg 3] ;;
    .call 5 self [.bin .add (.reg 0) (.const 8),
      .bin .sub (.reg 1) (.const 1), .reg 2, .reg 4] ;;
    .ret (.reg 5))

/-- Recursive edge scanning and the proved one-edge demand step. -/
def demandScanModule (b : ℕ) : List Stmt :=
  demandScanBody b (b + 1) :: demandStepModule (b + 1)

/-- Arithmetic bounds count the remaining contributions, rather than asking
for correctness of any future table. The source lies before the demand table. -/
def demandScanContract (w : ℕ) (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (es : List (Fin I.m)) (B L : ℕ) : Contract where
  pre args mem := ∃ a table heap, args = [a, es.length, table, heap] ∧
    ListAt mem a ((es.map I.edge).flatMap Edge.encode) ∧ SignedTableAt mem table s ∧
    a + 8 * es.length ≤ table ∧ table + 2 * I.n ≤ heap ∧
    (∀ v, (s v).natAbs ≤ B) ∧ (∀ e ∈ es, (I.edge e).lower.natAbs ≤ L) ∧
    B + 2 * es.length * L < 2 ^ w ∧ ZeroFrom mem heap ∧
    heap + 6 * es.length < 2 ^ w ∧ 8 < 2 ^ w
  post args mem out mem' := out = heapArg args + 6 * es.length ∧
    SignedTableAt mem' (args.getD 2 0) (FlowReduction.scanDemands I hv s es) ∧
    ZeroFrom mem' out ∧
    ∀ x < heapArg args, x < args.getD 2 0 ∨ args.getD 2 0 + 2 * I.n ≤ x → mem' x = mem x
  cost _ _ := 700 * es.length + 20

/-- The demand scan and all of its helpers use no random instructions. -/
theorem demandScanModule_noRand (b : ℕ) :
    ∀ body ∈ demandScanModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [demandScanBody, Stmt.NoRand, and_self]
  · exact demandStepModule_noRand _ body hb

/-- The machine executes the model's edge fold in its original order,
with exact scratch use, table values, frame, and a linear cost bound. -/
theorem demandScan_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (demandScanModule b)) (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (es : List (Fin I.m)) (B L : ℕ) :
    MeetsContract w p b (demandScanContract w I hv s es B L) := by
  have hstep : p.HasAt (b + 1) (demandStepModule (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by simp only [demandScanModule, List.length_cons]; omega)
    have hidx : b + (i + 1) = (b + 1) + i := by omega
    rw [hidx] at h
    simpa only [demandScanModule, List.getElem_cons_succ] using h
  induction es generalizing s B with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, table, heap, rfl, _, htable, _, _, _, _, _, hzero, hspace, hw⟩ := hpre
    have hh : heap < 2 ^ w := by simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using hspace
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold demandScanBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change heap = heap + 6 * 0 ∧ SignedTableAt mem table s ∧ ZeroFrom mem heap ∧
          ∀ x < heap, x < table ∨ table + 2 * I.n ≤ x → mem x = mem x
        exact ⟨by omega, htable, hzero, fun _ _ _ => rfl⟩
      · simp only [demandScanContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons e es ih =>
    have hkS := demandStep_meetsContract (w := w) hstep I hv s e
    have hkR := ih (FlowReduction.demandStep I hv s e) (B + 2 * L)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, table, heap, rfl, hat, htable, hsourceend, htableend, hs, hl,
      hbudget, hzero, hspace, hw⟩ := hpre
    have hsplit := listAt_append.mp hat
    change ListAt mem a (I.edge e).encode ∧
      ListAt mem (a + (I.edge e).encode.length) ((es.map I.edge).flatMap Edge.encode) at hsplit
    have htail : ListAt mem (a + 8) ((es.map I.edge).flatMap Edge.encode) := by
      simpa only [edge_encode_length] using hsplit.2
    have hfields : ∀ j : Fin 4, mem (a + j.val) = (I.edge e).encode.getD j.val 0 := by
      intro j
      have hj : j.val < (I.edge e).encode.length := by rw [edge_encode_length]; have hh := j.isLt; omega
      rw [List.getD_eq_getElem _ _ hj]
      exact hsplit.1 _ hj
    have htcell := hfields ⟨0, by decide⟩
    have hhcell := hfields ⟨1, by decide⟩
    have hsigncell := hfields ⟨2, by decide⟩
    have hmagcell := hfields ⟨3, by decide⟩
    simp only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero] at htcell hhcell hsigncell hmagcell
    have heL := hl e (List.mem_cons_self)
    have hbudget' : B + 2 * L + 2 * es.length * L < 2 ^ w := by
      simpa only [List.length_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbudget
    have hlocal : B + 2 * L < 2 ^ w := by omega
    have hsumT : (s ((FlowReduction.shiftedGraph I hv).tail e)).natAbs + (I.edge e).lower.natAbs < 2 ^ w := by
      have hval := hs ((FlowReduction.shiftedGraph I hv).tail e)
      omega
    have hsumH := lt_of_le_of_lt (demandStep_head_bound I hv s e B L hs heL) hlocal
    have hnew := demandStep_natAbs_le I hv s e B L hs heL
    have ht : (I.edge e).tail < I.n := ((FlowReduction.shiftedGraph I hv).tail e).isLt
    have hh : (I.edge e).head < I.n := ((FlowReduction.shiftedGraph I hv).head e).isLt
    have htword : (I.edge e).tail < 2 ^ w := by omega
    have hhword : (I.edge e).head < 2 ^ w := by omega
    have hsignword : (if (I.edge e).lower < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hmagword : (I.edge e).lower.natAbs < 2 ^ w := by omega
    have hbefore : a + 8 + 8 * es.length ≤ table := by
      simp only [List.length_cons, Nat.mul_succ] at hsourceend
      omega
    have hheap6 : heap + 6 < 2 ^ w := by
      simp only [List.length_cons, Nat.mul_succ] at hspace
      omega
    have ha : a < 2 ^ w := by omega
    have ha1 : a + 1 < 2 ^ w := by omega
    have ha2 : a + 2 < 2 ^ w := by omega
    have ha3 : a + 3 < 2 ^ w := by omega
    have ha8 : a + 8 < 2 ^ w := by omega
    have htableword : table < 2 ^ w := by omega
    have hheap : heap < 2 ^ w := by omega
    have hlen : (e :: es).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold demandScanBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkS
        (vs := [(I.edge e).tail, (I.edge e).head, if (I.edge e).lower < 0 then 1 else 0,
          (I.edge e).lower.natAbs, table, heap]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨table, heap, rfl, htable, htableend, hsumT, hsumH, hzero, hheap6⟩
      · intro nextHeap memS posS hpostS
        obtain ⟨hptr, htableS, hzeroS, hframeS⟩ := hpostS
        change nextHeap = heap + 6 at hptr
        change SignedTableAt memS table (FlowReduction.demandStep I hv s e) at htableS
        change (∀ x < heap, x < table ∨ table + 2 * I.n ≤ x → memS x = mem x) at hframeS
        have htailS : ListAt memS (a + 8) ((es.map I.edge).flatMap Edge.encode) := by
          apply htail.of_agree_below (h₀ := table)
          · simpa only [edges_encode_length, List.length_map] using hbefore
          · intro x hx
            exact hframeS x (by omega) (Or.inl hx)
        have hnextword : nextHeap < 2 ^ w := by omega
        refine runs_seq_call_le hkR (vs := [a + 8, es.length, table, nextHeap]) ?_ ?_ ?_ ?_
        · have heq : (e :: es).length - 1 = es.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨a + 8, table, nextHeap, rfl, htailS, htableS, hbefore, by omega,
            hnew, (fun e' he' => hl e' (List.mem_cons_of_mem e he')), hbudget', hzeroS, ?_, hw⟩
          simp only [List.length_cons, Nat.mul_succ] at hspace
          omega
        · intro out memR posR hpostR
          obtain ⟨hout, htableR, hzeroR, hframeR⟩ := hpostR
          change out = nextHeap + 6 * es.length at hout
          change SignedTableAt memR table (FlowReduction.scanDemands I hv (FlowReduction.demandStep I hv s e) es) at htableR
          change (∀ x < nextHeap, x < table ∨ table + 2 * I.n ≤ x → memR x = memS x) at hframeR
          have houtword : out < 2 ^ w := by
            simp only [List.length_cons, Nat.mul_succ] at hspace
            omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change out = heap + 6 * (e :: es).length ∧
              SignedTableAt memR table (FlowReduction.scanDemands I hv s (e :: es)) ∧
              ZeroFrom memR out ∧
              ∀ x < heap, x < table ∨ table + 2 * I.n ≤ x → memR x = mem x
            refine ⟨by simp only [List.length_cons, Nat.mul_succ]; omega, htableR, hzeroR, ?_⟩
            intro x hx hxout
            exact (hframeR x (by omega) hxout).trans (hframeS x hx hxout)
          · simp only [demandScanContract, demandStepContract, List.length_cons,
              argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega

/-- A concrete concatenation of input records and a signed table satisfies
all scan premises simultaneously, for every vector and finite edge list. -/
theorem exists_demandScan_pre (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (es : List (Fin I.m)) :
    ∃ w B L mem, (∀ x ∈ [0, es.length, 8 * es.length, 8 * es.length + 2 * I.n], x < 2 ^ w) ∧
      (demandScanContract w I hv s es B L).pre
        [0, es.length, 8 * es.length, 8 * es.length + 2 * I.n] mem := by
  let B := ((List.ofFn s).map Int.natAbs).foldr max 0
  let L := (es.map fun e => (I.edge e).lower.natAbs).foldr max 0
  have hs : ∀ v, (s v).natAbs ≤ B := by
    intro v
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨s v, List.mem_ofFn.mpr ⟨v, rfl⟩, rfl⟩)
  have hl : ∀ e ∈ es, (I.edge e).lower.natAbs ≤ L := by
    intro e he
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨e, he, rfl⟩)
  let w := wordSize 1 [B + 2 * es.length * L + 20 * es.length + 2 * I.n + 10]
  have hlarge : B + 2 * es.length * L + 20 * es.length + 2 * I.n + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  let records := (es.map I.edge).flatMap Edge.encode
  let tableWords := (List.ofFn s).flatMap encodeInt
  let mem := initMem (records ++ tableWords)
  have hrecordslen : records.length = 8 * es.length := by
    simp only [records, edges_encode_length, List.length_map]
  have htablelen : tableWords.length = 2 * I.n := by
    simp only [tableWords, integers_encode_length, List.length_ofFn]
  have hstored := listAt_append.mp (listAt_initMem (records ++ tableWords))
  have htable : SignedTableAt mem (8 * es.length) s := by
    apply signedTableAt_of_listAt
    simpa only [hrecordslen, Nat.zero_add] using hstored.2
  have hzero : ZeroFrom mem (8 * es.length + 2 * I.n) := by
    simpa only [List.length_append, hrecordslen, htablelen] using zeroFrom_initMem (records ++ tableWords)
  refine ⟨w, B, L, mem, ?_, 0, 8 * es.length, 8 * es.length + 2 * I.n,
    rfl, hstored.1, htable, by omega, by omega, hs, hl, by omega, hzero, by omega, by omega⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
