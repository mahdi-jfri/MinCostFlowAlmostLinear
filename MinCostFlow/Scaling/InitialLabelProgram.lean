module

public import MinCostFlow.Scaling.LabelStateLayout
public import MinCostFlow.Scaling.BuildAdjacencyProgram
public import MinCostFlow.Scaling.BoolTableSetProgram
public import MinCostFlow.Scaling.AdjacencyClearProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Initializing label propagation

The model starts with zero labels, marks its root, builds positive-flow
adjacency, moves the root's outgoing entries to pending, and clears that
head. This procedure performs those operations in the fixed label-state
layout. It preserves the graph and flow inputs, uses at most `3+5*n+2*m`
fresh words, and costs at most `300*m+400` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,root,stateHeap]`. -/
def initialLabelBody (adjacency pair flags : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.bin .add (.bin .add (.reg 3) (.const 2)) (.bin .mul (.const 3) (.reg 4))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 3) (.const 2)) (.bin .mul (.const 2) (.reg 4))) ;;
  .call 7 adjacency [.reg 0, .reg 1, .reg 5] ;;
  .assign 8 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 2))) ;;
  .call 9 pair [.load (.reg 8), .load (.bin .add (.reg 8) (.const 1)), .reg 3] ;;
  .call 10 flags [.reg 6, .reg 2, .const 1] ;;
  .call 11 pair [.const 0, .const 0, .reg 8] ;;
  .ret (.reg 7)

/-- The initializer, adjacency constructor, shared pair writer, and flag store. -/
def initialLabelModule (b : ℕ) : List Stmt :=
  initialLabelBody (b+1) (b+6) (b+7) ::
    (buildAdjacencyModule (b+1) ++ wordPairModule ++ boolTableSetModule)

/-- The graph and unsigned nonnegative flow lie below fresh state storage. -/
def initialLabelContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℤ) (root : Fin J.n) : Contract where
  pre args mem := ∃ a flow base, args = [a, flow, root.val, base] ∧
    ListAt mem a J.solverWords ∧ ListAt mem flow (List.ofFn (fun e => (f e).toNat)) ∧
    a+J.solverWords.length ≤ base ∧ flow+J.m ≤ base ∧
    (∀ e, 0 ≤ f e ∧ (f e).toNat < 2 ^ w) ∧ ZeroFrom mem base ∧
    base+3+5*J.n+2*J.m < 2 ^ w ∧ 8 < 2 ^ w
  post args mem ret mem' := labelNodes J.n (heapArg args) ≤ ret ∧
    ret ≤ labelNodes J.n (heapArg args)+2*J.m ∧
    LabelStateAt mem' (heapArg args) ret (J.initialLabelState f root) ∧
    ZeroFrom mem' ret ∧ ∀ x < heapArg args, mem' x = mem x
  cost _ _ := 300*J.m+400

/-- Initialization and all its helpers use no random instructions. -/
theorem initialLabelModule_noRand (b : ℕ) : ∀ body ∈ initialLabelModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [initialLabelBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact buildAdjacencyModule_noRand _ body hb
      · have he : body = wordPairBody := by simpa only [wordPairModule, List.mem_singleton] using hb
        subst body
        exact wordPairBody_noRand
    · have he : body = boolTableSetBody := by simpa only [boolTableSetModule, List.mem_singleton] using hb
      subst body
      exact boolTableSetBody_noRand

/-- The root flag update agrees with the model's equality test. -/
theorem rootFlags_eq {n : ℕ} (root : Fin n) :
    Function.update (fun _ : Fin n => false) root true = (fun v => decide (v = root)) := by
  funext v
  by_cases hv : v = root <;> simp only [Function.update_apply, hv, ↓reduceIte, decide_true, decide_false]

/-- The initializer computes every field of the model's initial label state
with explicit cost, allocation, and input framing. -/
theorem initialLabel_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (initialLabelModule b)) (J : Circulation) (f : Fin J.m → ℤ) (root : Fin J.n) :
    MeetsContract w p b (initialLabelContract w J f root) := by
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hadjacency := hasAt_append_left hleft
  have hpair : p.HasAt (b+6) wordPairModule := by
    have h := hasAt_append_right hleft
    simpa only [buildAdjacencyModule, adjacencyEdgesModule, adjacencyStepModule, adjacencyPushModule,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  have hflags : p.HasAt (b+7) boolTableSetModule := by
    have h := hasAt_append_right htail
    simpa only [List.length_append, buildAdjacencyModule, adjacencyEdgesModule, adjacencyStepModule,
      adjacencyPushModule, wordPairModule, List.length_cons, List.length_nil, Nat.reduceAdd,
      ← Nat.add_assoc] using h
  have hkA := buildAdjacency_meetsContract (w := w) hadjacency J f
  have hkH := wordPairStore_meetsContract (w := w) hpair
  have hkF := boolTableSet_meetsContract (w := w) hflags (fun _ : Fin J.n => false) root true
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, flow, base, rfl, hat, hflow, hend, hflowend, hvalues, hzero, hspace, hw⟩ := hpre
  let heads := labelHeads J.n base
  let seen := labelSeen J.n base
  let nodes := labelNodes J.n base
  let out := J.buildAdjacency f
  let cell := heads+2*root.val
  have hnodesEq : heads+2*J.n+1 = nodes := by dsimp [heads, nodes, labelHeads, labelNodes]; omega
  have hseenEnd : seen+J.n = heads := by dsimp [seen, heads, labelSeen, labelHeads]; omega
  have hlabelEnd : labelLabels base+2*J.n = seen := rfl
  have hcellEnd : cell+2 ≤ heads+2*J.n := by have hr := root.isLt; dsimp [cell]; omega
  have hN : mem a = J.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using
      hat 0 (by rw [J.solverWords_length]; omega)
  have hn : J.n < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have hroot : root.val < 2 ^ w := by have hr := root.isLt; omega
  have hbase : base < 2 ^ w := by omega
  have hbase2 : base+2 < 2 ^ w := by omega
  have h2n : 2*J.n < 2 ^ w := by omega
  have h3n : 3*J.n < 2 ^ w := by omega
  have hheads : heads < 2 ^ w := by dsimp [heads, labelHeads]; omega
  have hseen : seen < 2 ^ w := by dsimp [seen, labelSeen]; omega
  have hheadsCalc : base+2+3*J.n < 2 ^ w := hheads
  have hseenCalc : base+2+2*J.n < 2 ^ w := hseen
  have hnodes : nodes < 2 ^ w := by dsimp [nodes, labelNodes]; omega
  have hcell : cell < 2 ^ w := by rw [← hnodesEq] at hnodes; omega
  have hcell1 : cell+1 < 2 ^ w := by rw [← hnodesEq] at hnodes; omega
  have h2root : 2*root.val < 2 ^ w := by dsimp [cell] at hcell; omega
  have ha : a < 2 ^ w := by rw [J.solverWords_length] at hend; omega
  have hflowWord : flow < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hthree : 3 < 2 ^ w := by omega
  have hzeroHeads : ZeroFrom mem heads := by
    intro x hx
    exact hzero x (by dsimp [heads, labelHeads] at hx; omega)
  obtain ⟨_, _, _, hlabels0, hseen0, _⟩ := labelStateAt_empty J (bound := nodes) hzero
  apply runs_start_le
  unfold initialLabelBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heads) (by change _ = some (base+2+3*J.n); eval_expr) ?_
  refine runs_seq_assign_le (v := seen) (by change _ = some (base+2+2*J.n); eval_expr) ?_
  refine runs_seq_call_le hkA (vs := [a, flow, heads]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · refine ⟨a, flow, heads, rfl, hat, hflow, ?_, ?_, hvalues, hzeroHeads, ?_, hw⟩
    · dsimp [heads, labelHeads]; omega
    · dsimp [heads, labelHeads]; omega
    · rw [hnodesEq]
      exact hspace
  · intro ret memA posA hpostA
    obtain ⟨hretLower, hretUpper, houtA, hzeroA, hframeA⟩ := hpostA
    change heads+2*J.n+1 ≤ ret at hretLower
    change ret ≤ heads+2*J.n+1+2*J.m at hretUpper
    change AdjacencyAt memA heads (heads+2*J.n+1) ret out at houtA
    change (∀ x < heads, memA x = mem x) at hframeA
    rw [hnodesEq] at hretLower hretUpper houtA
    have hretWord : ret < 2 ^ w := by dsimp [nodes, labelNodes] at hretUpper; omega
    have hlabelsA : SignedTableAt memA (labelLabels base) (fun _ : Fin J.n => 0) := by
      apply hlabels0.of_agree
      intro x hx hxend
      exact hframeA x (by dsimp [labelLabels, heads, labelHeads] at *; omega)
    have hseenA : BoolTableAt memA seen (fun _ : Fin J.n => false) := by
      apply hseen0.of_agree
      intro x hx hxend
      exact hframeA x (by change x < seen+J.n at hxend; omega)
    obtain ⟨ptr, hrootRecord, hpendingA⟩ := houtA root
    have hptr : ptr < 2 ^ w := hpendingA.pointer_le.trans_lt hretWord
    have hrootLen : (out root).length ≤ J.m := by
      have hsingle : (out root).length ≤ J.adjacencyMass out :=
        Finset.single_le_sum (fun v _ => Nat.zero_le (out v).length) (Finset.mem_univ root)
      exact hsingle.trans (J.buildAdjacency_mass f)
    have hrootLenWord : (out root).length < 2 ^ w := hrootLen.trans_lt hm
    have hptrMem : memA cell = ptr := by
      have h := hrootRecord 0 (by change 0 < 2; decide)
      change memA (cell+0) = ptr at h
      simpa only [Nat.add_zero] using h
    have hlenMem : memA (cell+1) = (out root).length := hrootRecord 1 (by change 1 < 2; decide)
    refine runs_seq_assign_le (v := cell) (by eval_expr) ?_
    refine runs_seq_call_le hkH (vs := [ptr, (out root).length, base]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨ptr, (out root).length, base, rfl, hbase2⟩
    · intro _ memH posH hpostH
      obtain ⟨_, hheaderH, hframeH⟩ := hpostH
      change ListAt memH base [ptr, (out root).length] at hheaderH
      change (∀ x, x < base ∨ base+2 ≤ x → memH x = memA x) at hframeH
      have hlabelsH : SignedTableAt memH (labelLabels base) (fun _ : Fin J.n => 0) := by
        apply hlabelsA.of_agree
        intro x hx _
        exact hframeH x (Or.inr hx)
      have hseenH : BoolTableAt memH seen (fun _ : Fin J.n => false) := by
        apply hseenA.of_agree
        intro x hx _
        exact hframeH x (Or.inr (by dsimp [seen, labelSeen] at hx; omega))
      have houtH : AdjacencyAt memH heads nodes ret out := by
        apply houtA.of_agree le_rfl
        · intro x hx _
          exact hframeH x (Or.inr (by dsimp [heads, labelHeads] at hx; omega))
        · intro x hx _
          exact hframeH x (Or.inr (by dsimp [nodes, labelNodes] at hx; omega))
      have hpendingH : IndexListAt memH nodes ret ptr (out root) := by
        apply hpendingA.of_agree
        intro x hx _
        exact hframeH x (Or.inr (by dsimp [nodes, labelNodes] at hx; omega))
      have hseenSpace : seen+J.n < 2 ^ w := by rw [hseenEnd]; exact hheads
      refine runs_seq_call_le hkF (vs := [seen, root.val, 1]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨seen, rfl, hseenH, hseenSpace⟩
      · intro _ memF posF hpostF
        obtain ⟨_, hseenF, hframeF⟩ := hpostF
        change BoolTableAt memF seen (Function.update (fun _ : Fin J.n => false) root true) at hseenF
        rw [rootFlags_eq] at hseenF
        change (∀ x, x ≠ seen+root.val → memF x = memH x) at hframeF
        have hflagEnd : seen+root.val < heads := by have hr := root.isLt; omega
        have hlabelsF : SignedTableAt memF (labelLabels base) (fun _ : Fin J.n => 0) := by
          apply hlabelsH.of_agree
          intro x _ hx
          exact hframeF x (by rw [hlabelEnd] at hx; omega)
        have hheaderF : ListAt memF base [ptr, (out root).length] := by
          intro i hi
          have hi' : i < 2 := hi
          rw [hframeF _ (by dsimp [seen, labelSeen]; omega)]
          exact hheaderH i hi
        have houtF : AdjacencyAt memF heads nodes ret out := by
          apply houtH.of_agree le_rfl
          · intro x hx _
            exact hframeF x (by omega)
          · intro x hx _
            exact hframeF x (by dsimp [nodes, labelNodes, heads, labelHeads] at *; omega)
        have hpendingF : IndexListAt memF nodes ret ptr (out root) := by
          apply hpendingH.of_agree
          intro x hx _
          exact hframeF x (by dsimp [nodes, labelNodes, heads, labelHeads] at *; omega)
        have hkC := adjacencyClear_meetsContract (w := w) (heads := heads) (lo := nodes)
          (bound := ret) hpair out root
        have hheadsEnd : heads+2*J.n ≤ nodes := by omega
        have hheadsSpace : heads+2*J.n < 2 ^ w := by omega
        refine runs_seq_call_le hkC (vs := [0, 0, cell]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨rfl, houtF, hheadsEnd, hheadsSpace⟩
        · intro _ memC posC hpostC
          obtain ⟨_, houtC, hframeC⟩ := hpostC
          change AdjacencyAt memC heads nodes ret (Function.update out root []) at houtC
          change (∀ x, x < cell ∨ cell+2 ≤ x → memC x = memF x) at hframeC
          have hlabelsC : SignedTableAt memC (labelLabels base) (fun _ : Fin J.n => 0) := by
            apply hlabelsF.of_agree
            intro x _ hx
            exact hframeC x (Or.inl (by rw [hlabelEnd] at hx; dsimp [cell]; omega))
          have hseenC : BoolTableAt memC seen (fun v : Fin J.n => decide (v = root)) := by
            apply hseenF.of_agree
            intro x _ hx
            exact hframeC x (Or.inl (by dsimp [cell]; omega))
          have hheaderC : ListAt memC base [ptr, (out root).length] := by
            intro i hi
            have hi' : i < 2 := hi
            rw [hframeC _ (Or.inl (by dsimp [cell, heads, labelHeads]; omega))]
            exact hheaderF i hi
          have hpendingC : IndexListAt memC nodes ret ptr (out root) := by
            apply hpendingF.of_agree
            intro x hx _
            exact hframeC x (Or.inr (by omega))
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change nodes ≤ ret ∧ ret ≤ nodes+2*J.m ∧ LabelStateAt memC base ret (J.initialLabelState f root) ∧
              ZeroFrom memC ret ∧ ∀ x < base, memC x = mem x
            refine ⟨hretLower, hretUpper, ⟨ptr, hheaderC, hpendingC, hlabelsC, hseenC, houtC⟩, ?_, ?_⟩
            · intro x hx
              apply (hframeC x (Or.inr (by omega))).trans
              apply (hframeF x (by omega)).trans
              exact (hframeH x (Or.inr (by dsimp [nodes, labelNodes] at hretLower; omega))).trans (hzeroA x hx)
            · intro x hx
              apply (hframeC x (Or.inl (by dsimp [cell, heads, labelHeads]; omega))).trans
              apply (hframeF x (by dsimp [seen, labelSeen]; omega)).trans
              exact (hframeH x (Or.inl hx)).trans (hframeA x (by dsimp [heads, labelHeads]; omega))
          · simp only [initialLabelContract, buildAdjacencyContract, wordPairStoreContract,
              boolTableSetContract, adjacencyClearContract, argsSize_cons, argsSize_nil,
              Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
