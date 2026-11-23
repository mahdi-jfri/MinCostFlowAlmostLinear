module

public import MinCostFlow.Scaling.AdjacencyStepProgram
public import MinCostFlow.Scaling.SolverContract
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Scanning positive-flow adjacency entries

The model builds adjacency lists by scanning edge indices in order. This
procedure reads the corresponding graph records and unsigned flow values,
then invokes the proved conditional adjacency step. A length bound grows
by at most one per edge. The scan computes exactly the model fold, allocates
at most two words per edge, and costs at most `300*count+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[records,flow,count,firstIndex,heads,heap]`. -/
def adjacencyEdgesBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 5))
    (.call 6 step [.load (.reg 0), .reg 3, .load (.reg 1), .reg 4, .reg 5] ;;
     .call 7 self [.bin .add (.reg 0) (.const 5), .bin .add (.reg 1) (.const 1),
       .bin .sub (.reg 2) (.const 1), .bin .add (.reg 3) (.const 1), .reg 4, .reg 6] ;;
     .ret (.reg 7))

/-- The recursive edge scan and the conditional adjacency update. -/
def adjacencyEdgesModule (b : ℕ) : List Stmt :=
  adjacencyEdgesBody b (b+1) :: adjacencyStepModule (b+1)

/-- Source arrays precede the head table. Its lists have lengths at most
`B`; the remaining scan reserves one length increment and two cells per edge. -/
def adjacencyEdgesContract (w lo : ℕ) (J : Circulation) (f : Fin J.m → ℤ)
    (out : Fin J.n → List (Fin J.m)) (es : List (Fin J.m)) (B index : ℕ) : Contract where
  pre args mem := ∃ a flow heads heap, args = [a, flow, es.length, index, heads, heap] ∧
    ListAt mem a (es.flatMap J.solverEdgeWords) ∧ ListAt mem flow (es.map (fun e => (f e).toNat)) ∧
    AdjacencyAt mem heads lo heap out ∧ a+5*es.length ≤ heads ∧ flow+es.length ≤ heads ∧
    heads+2*J.n ≤ lo ∧ lo ≤ heap ∧ 0 < heap ∧
    (∀ v, (out v).length ≤ B) ∧ B+es.length < 2 ^ w ∧ index+es.length < 2 ^ w ∧
    (∀ i (hi : i < es.length), (es[i]'hi).val = index+i) ∧
    (∀ e ∈ es, 0 ≤ f e ∧ (f e).toNat < 2 ^ w) ∧
    ZeroFrom mem heap ∧ heap+2*es.length < 2 ^ w ∧ 8 < 2 ^ w
  post args mem ret mem' := heapArg args ≤ ret ∧ ret ≤ heapArg args+2*es.length ∧
    AdjacencyAt mem' (args.getD 4 0) lo ret (es.foldl (J.adjacencyStep f) out) ∧ ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x < args.getD 4 0 ∨ args.getD 4 0+2*J.n ≤ x → mem' x = mem x
  cost _ _ := 300*es.length+20

private theorem adjacencyStep_lengths (J : Circulation) (f : Fin J.m → ℤ)
    (out : Fin J.n → List (Fin J.m)) (e : Fin J.m) (B : ℕ)
    (h : ∀ v, (out v).length ≤ B) : ∀ v, (J.adjacencyStep f out e v).length ≤ B+1 := by
  intro v
  unfold Circulation.adjacencyStep
  split
  · by_cases hv : v = J.tail e
    · subst v
      simpa only [Function.update_self, List.length_cons] using Nat.add_le_add_right (h (J.tail e)) 1
    · rw [Function.update_of_ne hv]
      exact (h v).trans (Nat.le_succ _)
  · exact (h v).trans (Nat.le_succ _)

/-- The complete adjacency scan uses no random instructions. -/
theorem adjacencyEdgesModule_noRand (b : ℕ) : ∀ body ∈ adjacencyEdgesModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [adjacencyEdgesBody, Stmt.NoRand, and_self]
  · exact adjacencyStepModule_noRand _ body hb

/-- Scanning stored edges computes exactly the model adjacency fold with a
linear cost, bounded fresh allocation, and a frame outside the vertex table. -/
theorem adjacencyEdges_meetsContract {w b lo : ℕ} {p : Program}
    (hp : p.HasAt b (adjacencyEdgesModule b)) (J : Circulation) (f : Fin J.m → ℤ)
    (out : Fin J.n → List (Fin J.m)) (es : List (Fin J.m)) (B index : ℕ) :
    MeetsContract w p b (adjacencyEdgesContract w lo J f out es B index) := by
  have hstep := hasAt_tail hp
  induction es generalizing out B index with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, flow, heads, heap, rfl, _, _, hat, _, _, _, _, _, _, _, _, _, _, hzero, hspace, hw⟩ := hpre
    have hh : heap < 2 ^ w := by simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using hspace
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold adjacencyEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change heap ≤ heap ∧ heap ≤ heap+2*0 ∧ AdjacencyAt mem heads lo heap out ∧
          ZeroFrom mem heap ∧ ∀ x < heap, x < heads ∨ heads+2*J.n ≤ x → mem x = mem x
        exact ⟨le_rfl, by omega, hat, hzero, fun _ _ _ => rfl⟩
      · simp only [adjacencyEdgesContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    have hkE := adjacencyStep_meetsContract (w := w) (lo := lo) hstep J f out e
    have hkR := ih (J.adjacencyStep f out e) (B+1) (index+1)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, flow, heads, heap, rfl, hat, hflow, htable, haend, hfend, hheadsEnd, hlo,
      hpositive, hsizes, hbudget, hindexBudget, hseq, hvalues, hzero, hspace, hw⟩ := hpre
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    obtain ⟨hflowHead, hflowTail⟩ := listAt_cons.mp hflow
    change mem flow = (f e).toNat at hflowHead
    have htailIndex : mem a = (J.tail e).val := by
      simpa only [Circulation.solverEdgeWords, Nat.add_zero, List.getElem_cons_zero] using
        hhead 0 (by change 0 < 5; decide)
    have heIndex : e.val = index := by
      have h := hseq 0 (by simp)
      change e.val = index+0 at h
      simpa only [Nat.add_zero] using h
    have hseqTail : ∀ i (hi : i < es.length), (es[i]'hi).val = (index+1)+i := by
      intro i hi
      have h := hseq (i+1) (by simp only [List.length_cons]; omega)
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    obtain ⟨hf, hfWord⟩ := hvalues e List.mem_cons_self
    have ht := (J.tail e).isLt
    have hlen : (e :: es).length < 2 ^ w := hwords _ (by simp)
    have hheap : heap < 2 ^ w := by omega
    have ha : a < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have ha5 : a+5 < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have hflow : flow < 2 ^ w := by simp only [List.length_cons] at hfend; omega
    have hflow1 : flow+1 < 2 ^ w := by simp only [List.length_cons] at hfend; omega
    have hheads : heads < 2 ^ w := by omega
    have htWord : (J.tail e).val < 2 ^ w := by omega
    have heWord : e.val < 2 ^ w := by rw [heIndex]; omega
    have hindex1 : index+1 < 2 ^ w := by simp only [List.length_cons] at hindexBudget; omega
    have hheap2 : heap+2 < 2 ^ w := by simp only [List.length_cons] at hspace; omega
    have hlength : (out (J.tail e)).length+1 < 2 ^ w := by
      have h := hsizes (J.tail e)
      simp only [List.length_cons] at hbudget
      omega
    have hone : 1 < 2 ^ w := by omega
    have hfive : 5 < 2 ^ w := by omega
    apply runs_start_le
    unfold adjacencyEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkE
        (vs := [(J.tail e).val, e.val, (f e).toNat, heads, heap]) ?_ ?_ ?_ ?_
      · rw [heIndex]; eval_expr
      · wram_words
      · exact ⟨heads, heap, rfl, hf, htable, hheadsEnd, hlo, hpositive, hlength, hzero, hheap2⟩
      · intro next memE posE hpostE
        obtain ⟨hnextLower, hnextUpper, htableE, hzeroE, hframeE⟩ := hpostE
        change heap ≤ next at hnextLower
        change next ≤ heap+2 at hnextUpper
        change AdjacencyAt memE heads lo next (J.adjacencyStep f out e) at htableE
        change (∀ x < heap, x ≠ heads+2*(J.tail e).val → x ≠ heads+2*(J.tail e).val+1 → memE x = mem x) at hframeE
        have hsourceTail : a+5+5*es.length ≤ heads := by simp only [List.length_cons] at haend; omega
        have hflowTailEnd : flow+1+es.length ≤ heads := by simp only [List.length_cons] at hfend; omega
        have htailE : ListAt memE (a+5) (es.flatMap J.solverEdgeWords) := by
          apply htail.of_agree_below (h₀ := heads)
          · rwa [Circulation.solverEdgeRecords_length]
          · intro x hx
            exact hframeE x (by omega) (by omega) (by omega)
        have hflowE : ListAt memE (flow+1) (es.map (fun e => (f e).toNat)) := by
          apply hflowTail.of_agree_below (h₀ := heads)
          · rwa [List.length_map]
          · intro x hx
            exact hframeE x (by omega) (by omega) (by omega)
        have hnextWord : next < 2 ^ w := by omega
        have hlenTail : es.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
        refine runs_seq_call_le hkR (vs := [a+5, flow+1, es.length, index+1, heads, next]) ?_ ?_ ?_ ?_
        · have heq : (e :: es).length-1 = es.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨a+5, flow+1, heads, next, rfl, htailE, hflowE, htableE,
            hsourceTail, hflowTailEnd, hheadsEnd, by omega, by omega,
            adjacencyStep_lengths J f out e B hsizes, ?_, ?_, hseqTail,
            fun e' he' => hvalues e' (List.mem_cons_of_mem e he'), hzeroE, ?_, hw⟩
          · simp only [List.length_cons] at hbudget; omega
          · simp only [List.length_cons] at hindexBudget; omega
          · simp only [List.length_cons] at hspace; omega
        · intro ret memR posR hpostR
          obtain ⟨hretLower, hretUpper, htableR, hzeroR, hframeR⟩ := hpostR
          change next ≤ ret at hretLower
          change ret ≤ next+2*es.length at hretUpper
          change AdjacencyAt memR heads lo ret (es.foldl (J.adjacencyStep f) (J.adjacencyStep f out e)) at htableR
          change (∀ x < next, x < heads ∨ heads+2*J.n ≤ x → memR x = memE x) at hframeR
          have hretWord : ret < 2 ^ w := by simp only [List.length_cons] at hspace; omega
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change heap ≤ ret ∧ ret ≤ heap+2*(e :: es).length ∧
              AdjacencyAt memR heads lo ret ((e :: es).foldl (J.adjacencyStep f) out) ∧
              ZeroFrom memR ret ∧ ∀ x < heap, x < heads ∨ heads+2*J.n ≤ x → memR x = mem x
            refine ⟨by omega, by simp only [List.length_cons]; omega, htableR, hzeroR, ?_⟩
            intro x hx hxout
            apply (hframeR x (by omega) hxout).trans (hframeE x hx ?_ ?_)
            all_goals rcases hxout with hxout | hxout <;> omega
          · simp only [adjacencyEdgesContract, adjacencyStepContract, List.length_cons,
              argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg,
              Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
