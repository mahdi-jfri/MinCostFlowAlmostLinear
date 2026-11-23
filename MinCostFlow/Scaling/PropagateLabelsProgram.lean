module

public import MinCostFlow.Scaling.InitialLabelProgram
public import MinCostFlow.Scaling.LabelRunProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Complete machine label propagation

Build the positive-flow adjacency lists, initialize the root, and run the
counted traversal for the graph's edge count. The model's remaining-edge
bound supplies the traversal's length budget and bounds its work. The
procedure returns the exact model state in the shared label-state layout.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,root,stateHeap]`. -/
def propagateLabelsBody (initial run : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 initial [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 6 run [.reg 0, .reg 3, .reg 4, .reg 5] ;;
  .ret (.reg 6)

/-- The propagation entry, initialization module, and bounded traversal. -/
def propagateLabelsModule (b : ℕ) : List Stmt :=
  propagateLabelsBody (b+1) (b+9) :: (initialLabelModule (b+1) ++ labelRunModule (b+9))

/-- Local word budgets for complete propagation, including every label
subtraction and every fresh copied list node. -/
def propagateLabelsContract (w C : ℕ) (J : Circulation) (f : Fin J.m → ℤ)
    (root : Fin J.n) : Contract where
  pre args mem := ∃ a flow base, args = [a, flow, root.val, base] ∧
    ListAt mem a J.solverWords ∧ ListAt mem flow (List.ofFn (fun e => (f e).toNat)) ∧
    a+J.solverWords.length ≤ base ∧ flow+J.m ≤ base ∧
    (∀ e, 0 ≤ f e ∧ (f e).toNat < 2^w) ∧ (∀ e, (J.cost e).natAbs ≤ C) ∧
    (J.m+1)*C < 2^w ∧ ZeroFrom mem base ∧ base+5+5*J.n+6*J.m < 2^w ∧ 8 < 2^w
  post args mem ret mem' := labelNodes J.n (heapArg args) ≤ ret ∧
    ret ≤ labelNodes J.n (heapArg args)+6*J.m ∧
    LabelStateAt mem' (heapArg args) ret (J.propagateLabels f root).1 ∧
    ZeroFrom mem' ret ∧ ∀ x < heapArg args, mem' x = mem x
  cost _ _ := 3000*J.m+800

/-- All installed propagation procedures have no random instruction. -/
theorem propagateLabelsModule_noRand (b : ℕ) :
    ∀ body ∈ propagateLabelsModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [propagateLabelsBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact initialLabelModule_noRand _ body hb
    · exact labelRunModule_noRand _ body hb

/-- Initialization followed by the bounded traversal computes the complete
integer label-propagation model in linear machine time and fresh space. -/
theorem propagateLabels_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (propagateLabelsModule b)) (C : ℕ) (J : Circulation)
    (f : Fin J.m → ℤ) (root : Fin J.n) :
    MeetsContract w p b (propagateLabelsContract w C J f root) := by
  have htail := hasAt_tail hp
  have hinit := hasAt_append_left htail
  have hrun : p.HasAt (b+9) (labelRunModule (b+9)) := by
    have hh := hasAt_append_right htail
    have hlen : (initialLabelModule (b+1)).length = 8 := rfl
    simpa only [hlen, Nat.add_assoc] using hh
  let s := J.initialLabelState f root
  have hremaining := J.initialLabelState_remaining f root
  change s.remaining ≤ J.m at hremaining
  have hmass : J.adjacencyMass s.outgoing ≤ J.m := by
    dsimp only [Circulation.LabelState.remaining] at hremaining
    omega
  have hwork := Circulation.LabelState.run_work J.m s
  have hkI := initialLabel_meetsContract (w := w) hinit J f root
  have hkR := labelRun_meetsContract (w := w) hrun J.m 0 C s
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, flow, base, rfl, hat, hflow, hend, hflowEnd, hvalues, hcosts,
    hbudget, hzero, hspace, hw⟩ := hpre
  have haWord := hwords a (List.mem_cons_self)
  have hbase : base < 2^w := by omega
  have hm : J.m < 2^w := by omega
  have hremainingWord : s.remaining+1 < 2^w := by omega
  have hone : 1 < 2^w := by omega
  have ha1 : a+1 < 2^w := by rw [J.solverWords_length] at hend; omega
  have hM : mem (a+1) = J.m := (solver_header_at J hat).2
  apply runs_start_le
  unfold propagateLabelsBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkI (vs := [a, flow, root.val, base]) (by eval_expr) hwords ?_ ?_
  · exact ⟨a, flow, base, rfl, hat, hflow, hend, hflowEnd, hvalues, hzero, by omega, hw⟩
  · intro initialHeap memI posI hpostI
    obtain ⟨hlo, hhi, hstate, hzeroI, hframeI⟩ := hpostI
    change labelNodes J.n base ≤ initialHeap at hlo
    change initialHeap ≤ labelNodes J.n base+2*J.m at hhi
    change LabelStateAt memI base initialHeap s at hstate
    change (∀ x < base, memI x = mem x) at hframeI
    have hnode : labelNodes J.n base = base+3+5*J.n := rfl
    have hheapWord : initialHeap < 2^w := by rw [hnode] at hhi; omega
    have hrecSpace : initialHeap+2*J.adjacencyMass s.outgoing+2*J.m+2 < 2^w := by
      rw [hnode] at hhi
      omega
    have hgraph : ListAt memI a J.solverWords := by
      intro i hi
      rw [hframeI (a+i) (by omega)]
      exact hat i hi
    refine runs_seq_call_le hkR (vs := [a, base, J.m, initialHeap]) (by eval_expr) ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact haWord
      · exact hbase
      · exact hm
      · exact hheapWord
    · refine ⟨a, base, initialHeap, rfl, hgraph, hend, hstate, hlo, hm, ?_, hcosts,
        ?_, hremainingWord, hzeroI, hrecSpace⟩
      · intro v
        exact le_rfl
      · simpa only [Nat.zero_add] using hbudget
    · intro ret memR posR hpostR
      obtain ⟨hretlo, halloc, hstateR, hzeroR, hframeR⟩ := hpostR
      change initialHeap ≤ ret at hretlo
      change ret+2*J.adjacencyMass (Circulation.LabelState.run J.m s).1.outgoing ≤
        initialHeap+2*J.adjacencyMass s.outgoing+2*J.m at halloc
      change LabelStateAt memR base ret (Circulation.LabelState.run J.m s).1 at hstateR
      change (∀ x < initialHeap, x < base ∨ labelNodes J.n base ≤ x → memR x = memI x) at hframeR
      have hretWord : ret < 2^w := by rw [hnode] at hhi; omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change labelNodes J.n base ≤ ret ∧ ret ≤ labelNodes J.n base+6*J.m ∧
          LabelStateAt memR base ret (J.propagateLabels f root).1 ∧ ZeroFrom memR ret ∧
          ∀ x < base, memR x = mem x
        refine ⟨hlo.trans hretlo, by omega, hstateR, hzeroR, ?_⟩
        intro x hx
        have hbaseHeap : base ≤ initialHeap := by rw [hnode] at hlo; omega
        exact (hframeR x (by omega) (Or.inl hx)).trans (hframeI x hx)
      · simp only [propagateLabelsContract, initialLabelContract, labelRunContract,
          argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega

end MinCostFlow.Scaling.Machine
