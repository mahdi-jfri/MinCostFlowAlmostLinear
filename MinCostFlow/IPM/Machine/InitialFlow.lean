module

public import MinCostFlow.IPM.Machine.InitialFlowHalf
public import MinCostFlow.IPM.Machine.InitialLayoutRead
public import MinCostFlow.IPM.Machine.InitialMidpointVector
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Loading the prescribed initial flow of the augmented instance

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) specifies the augmented graph and its initial
flow. This entry reads the actual augmented graph header and capacity
words and loads the verified dense fixed-point midpoint array. Its
postcondition names `initialFlow`, not an unspecified feasible flow.
The format and numeric fits are supplied by the precision selection.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Arguments `[augmentedGraph,L,P,heap]`. -/
def initialFlowBody (load : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 load [.bin .add (.reg 0) (.const 4),.reg 4,.reg 1,.reg 2,.reg 3] ;;
  .ret (.reg 5)

/-- Header reader and dense fixed-point loader. -/
def initialFlowModule (b h : ℕ) : List Stmt :=
  [initialFlowBody (b+1)] ++ initialMidpointVectorModule (b+1) h

/-- Load a zero-lower graph's specified midpoint flow. -/
def midpointFlowContract (w h : ℕ) (I : Instance) (f : Fin I.m → ℝ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L P heap, args = [a,L,P,heap] ∧
      1 ≤ P ∧ ZeroLowerAt mem a I ∧ a+(zeroLowerWords I).length ≤ heap ∧
      ∀ e : Fin I.m, (I.edge e).upper.toNat < 2^w ∧
        Num.Fits h L ((I.edge e).upper.toNat : ℤ) ∧
        Num.Fits h L (((I.edge e).upper.toNat : ℤ)*(2 : ℤ)^(P-1)))
    (fun args _ mem' => ∀ e : Fin I.m,
      ScalarAt mem' (heapArg args+e.val*args.getD 1 0) h (args.getD 1 0) (args.getD 2 0) (f e))
    (fun args _ => I.m*(200*args.getD 1 0+600)+200)
    (fun args _ => 4*(I.m*args.getD 1 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+4*(I.m*args.getD 1 0) }

/-- The actual initialized flow is written into consecutive `L`-limb
blocks at heap. Space is `4ML`, including numerical scratch; return is
`heap+4ML`, cost at most `M(200L+600)+200`. No rationality or feasibility
oracle appears in the precondition. -/
def initialFlowContract (w h : ℕ) (J : Circulation) (penalty : ℤ) : Contract :=
  let I := initialInstance J.toInstance penalty
  let C := heapContract w
    (fun args mem => ∃ a L P heap, args = [a,L,P,heap] ∧ 0 < J.m ∧
      (∀ e, 1 ≤ J.capacity e) ∧ 1 ≤ P ∧ ZeroLowerAt mem a I ∧
      a+(zeroLowerWords I).length ≤ heap ∧
      ∀ e : Fin I.m, (I.edge e).upper.toNat < 2^w ∧
        Num.Fits h L ((I.edge e).upper.toNat : ℤ) ∧
        Num.Fits h L (((I.edge e).upper.toNat : ℤ)*(2 : ℤ)^(P-1)))
    (fun args _ mem' => ∀ e : Fin I.m,
      ScalarAt mem' (heapArg args+e.val*args.getD 1 0) h (args.getD 1 0) (args.getD 2 0)
        (IPM.initialFlow J.toInstance penalty e))
    (fun args _ => I.m*(200*args.getD 1 0+600)+200)
    (fun args _ => 4*(I.m*args.getD 1 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+4*(I.m*args.getD 1 0) }

/-- The full initial flow loader is deterministic. -/
theorem initialFlowModule_noRand (b h : ℕ) : ∀ body ∈ initialFlowModule b h, body.NoRand := by
  intro body hb
  simp only [initialFlowModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [initialFlowBody,Stmt.NoRand]
  · exact initialMidpointVectorModule_noRand _ _ body hb

/-- The loader writes the midpoint of every positive-size zero-lower graph. -/
theorem midpointFlow_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hconst : 5 < 2^w)
    (hp : p.HasAt b (initialFlowModule b h)) (I : Instance) (hI : I.IsValid)
    (hMpos : 0 < I.m) (f : Fin I.m → ℝ)
    (hhalf : ∀ e, ((I.edge e).upper.toNat : ℝ)/2 = f e) :
    MeetsContract w p b (midpointFlowContract w h I f) := by
  have hload : p.HasAt (b+1) (initialMidpointVectorModule (b+1) h) := Num.hasAt_append_right hp
  have hloadSpec := initialMidpointVector_meetsContract hh hw hconst hload
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,L,P,heap,rfl,hprec,hencoded,hend,hfits⟩,hzero,hspace⟩ := hpre
  change heap+4*(I.m*L) < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hlen := zeroLowerWords_length I hI
  rw [hlen] at hend
  have hM := (zeroLower_header_at I hI mem a hencoded.2.2).2
  have hMw : I.m < 2^w := by omega
  have hL : L < 2^w := hwords _ (by simp)
  have hP : P < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have ha1 : a+1 < 2^w := by omega
  have ha4 : a+4 < 2^w := by omega
  have hsource : ∀ i < I.m, a+4+5*i < heap ∧ mem (a+4+5*i) < 2^w ∧
      Num.Fits h L (mem (a+4+5*i) : ℤ) ∧
      Num.Fits h L ((mem (a+4+5*i) : ℤ)*(2 : ℤ)^(P-1)) := by
    intro i hi
    rw [zeroLower_capacity_at I hI mem a hencoded.2.2 ⟨i,hi⟩]
    exact ⟨by omega,hfits ⟨i,hi⟩⟩
  apply runs_start_le
  unfold initialFlowBody
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_call_le hloadSpec (vs := [a+4,I.m,L,P,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_,_,_,_,_,rfl,hprec,hsource⟩,hzero,hspace⟩
  · intro value mem' pos' hout
    obtain ⟨⟨hlo,hhi,hframe,hfresh,htable⟩,hv⟩ := hout
    change value = heap+4*(I.m*L) at hv
    have hvw : value < 2^w := by omega
    refine runs_ret_le (v := value) (by eval_expr) ?_ ?_
    · change (heap ≤ value ∧ value ≤ heap+4*(I.m*L) ∧ (∀ x < heap, mem' x = mem x) ∧
        ZeroFrom mem' value ∧ _) ∧ value = heap+4*(I.m*L)
      refine ⟨⟨hlo,hhi,hframe,hfresh,?_⟩,hv⟩
      intro e
      have he := htable e.val e.isLt
      change ScalarAt mem' (heap+e.val*L) h L P ((mem (a+4+5*e.val) : ℝ)/2) at he
      rw [zeroLower_capacity_at I hI mem a hencoded.2.2 e,hhalf e] at he
      exact he
    · simp only [midpointFlowContract,initialMidpointVectorContract,heapContract,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil,
        List.getD_cons_zero,List.getD_cons_succ]
      omega

/-- The fixed-point initialization output is exactly `initialFlow` on
the graph produced by `initialGraph`, at every edge index. -/
theorem initialFlow_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hconst : 5 < 2^w)
    (hp : p.HasAt b (initialFlowModule b h)) (J : Circulation) (penalty : ℤ) :
    MeetsContract w p b (initialFlowContract w h J penalty) := by
  intro args mem pos tape hwords hpre
  obtain ⟨⟨a,L,P,heap,rfl,hm,hpositive,hprec,hencoded,hend,hfits⟩,hzero,hspace⟩ := hpre
  let I := initialInstance J.toInstance penalty
  have hI := initialInstance_valid J.toInstance penalty J.toInstance_valid
  have hMpos : 0 < I.m := by
    have hfree : (freeEdges J.toInstance).card = J.m := by
      rw [freeEdges_circulation J hpositive,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
    change 0 < (initialInstance J.toInstance penalty).m
    rw [initialInstance_m,hfree]
    omega
  exact midpointFlow_meetsContract hh hw hconst hp I hI hMpos _
    (initialFlow_half_encoded J hpositive penalty) _ _ _ _ hwords
    ⟨⟨a,L,P,heap,rfl,hprec,hencoded,hend,hfits⟩,hzero,hspace⟩

end MinCostFlow.IPM.Machine
