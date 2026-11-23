module

public import MinCostFlow.Scaling.CapacityCollectProgram
public import MinCostFlow.Scaling.SortCapacitiesProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic

/-!
# Sorted candidates for the bottleneck search

Collect the capacities in edge order and apply the model's stable sort.
The source graph is preserved. The final candidate array occupies the
last `m` words before the returned heap, ready for indexed threshold tests.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,heap]`. -/
def capacityCandidatesBody (collect sort : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 collect [.reg 0,.reg 1] ;;
  .call 4 sort [.reg 1,.reg 2,.reg 3] ;;
  .ret (.reg 4)

/-- Collection and sorting occupy disjoint consecutive procedure indices. -/
def capacityCandidatesModule (b : ℕ) : List Stmt :=
  capacityCandidatesBody (b+1) (b+1+(capacityCollectModule (b+1)).length) ::
    (capacityCollectModule (b+1) ++
      sortCapacitiesModule (b+1+(capacityCollectModule (b+1)).length))

/-- Sorted capacity candidates, with linear-logarithmic space and cost. -/
def capacityCandidatesContract (w : ℕ) (J : Circulation) : Contract :=
  let fuel := Nat.clog 2 (J.m+1)
  let H := heapContract w
    (fun args mem => ∃ a heap,args=[a,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x<2^w) ∧
      J.m+2<2^w ∧ 8<2^w)
    (fun _ _ _ => True)
    (fun _ _ => 80*J.m+200*(sortCapacities (List.ofFn J.capacity)).2+40*fuel+900)
    (fun _ _ => J.m+(fuel+1)*J.m)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
    heapArg args+J.m ≤ ret ∧
      ListAt mem' (ret-J.m) (sortCapacities (List.ofFn J.capacity)).1 }

/-- Neither collection nor sorting uses random instructions. -/
theorem capacityCandidatesModule_noRand (b : ℕ) :
    ∀ body ∈ capacityCandidatesModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityCandidatesBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hc | hs
    · exact capacityCollectModule_noRand _ body hc
    · exact sortCapacitiesModule_noRand _ body hs

/-- Collection followed by sorting computes exactly the candidate list
used by `bottleneckSearch`, with every call and instruction charged. -/
theorem capacityCandidates_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityCandidatesModule b)) (J : Circulation) :
    MeetsContract w p b (capacityCandidatesContract w J) := by
  have htail := hasAt_tail hp
  have hc := capacityCollect_meetsContract (w := w) (hasAt_append_left htail) J
  have hsrt := sortCapacities_meetsContract (w := w) (hasAt_append_right htail) (List.ofFn J.capacity)
  let fuel := Nat.clog 2 (J.m+1)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hm,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(J.m+(fuel+1)*J.m)<2^w at hs
  have hh : heap<2^w := by omega
  have ha : a<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hend; omega
  have hm0 : J.m<2^w := by omega
  have hcap : ∀ x ∈ List.ofFn J.capacity,x<2^w := by
    intro x hx
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
    exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  have hM := (solver_header_at J hat).2
  apply runs_start_le
  unfold capacityCandidatesBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hc (vs := [a,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,heap,rfl,hat,hend,hinput,hw⟩,hz,by change heap+J.m<2^w; omega⟩
  · intro mid memC posC hpostC
    obtain ⟨⟨_,_,hframeC,hzC,harray⟩,hmid⟩ := hpostC
    change mid=heap+J.m at hmid
    change (∀ x<heap,memC x=mem x) at hframeC
    change ZeroFrom memC mid at hzC
    change ListAt memC heap (List.ofFn J.capacity) at harray
    have hmidword : mid<2^w := by omega
    refine runs_seq_call_le hsrt (vs := [heap,J.m,mid]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨heap,mid,by simp only [List.length_ofFn],harray,?_,hcap,?_,by omega⟩,hzC,?_⟩
      · simp only [List.length_ofFn]; omega
      · simpa only [List.length_ofFn] using hm
      · change mid+(Nat.clog 2 ((List.ofFn J.capacity).length+1)+1)*(List.ofFn J.capacity).length<2^w
        simpa only [List.length_ofFn,hmid,Nat.add_assoc] using hs
    · intro ret memS posS hpostS
      obtain ⟨⟨hlo,hhi,hframeS,hzS,_⟩,hlower,hout⟩ := hpostS
      change mid ≤ ret at hlo
      change ret ≤ mid+(Nat.clog 2 ((List.ofFn J.capacity).length+1)+1)*(List.ofFn J.capacity).length at hhi
      simp only [List.length_ofFn] at hhi hlower hout
      change ret ≤ mid+(fuel+1)*J.m at hhi
      change mid+J.m ≤ ret at hlower
      change (∀ x<mid,memS x=memC x) at hframeS
      change ZeroFrom memS ret at hzS
      have hr : ret<2^w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change (heap≤ret ∧ ret≤heap+(J.m+(fuel+1)*J.m) ∧ (∀ x<heap,memS x=mem x) ∧
          ZeroFrom memS ret ∧ True) ∧ heap+J.m≤ret ∧ _
        refine ⟨⟨by omega,by omega,?_,hzS,True.intro⟩,by omega,hout⟩
        intro x hx
        exact (hframeS x (by omega)).trans (hframeC x hx)
      · simp only [capacityCandidatesContract,capacityCollectContract,sortCapacitiesContract,
          heapContract,List.length_ofFn,argsSize_cons,argsSize_nil,Expr.size_bin,
          Expr.size_load,Expr.size_reg,Expr.size_const]
        omega

/-- Candidate preparation takes linear time times the binary logarithm
of the edge count, including the empty graph's constant overhead. -/
theorem capacityCandidates_cost_le (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (J : Circulation) :
    (capacityCandidatesContract w J).cost args mem ≤
      2520*(Nat.clog 2 (J.m+1)+1)*(J.m+1)+1100 := by
  have h := sortCapacities_cost_le w args mem (List.ofFn J.capacity)
  change 80*J.m+200*(sortCapacities (List.ofFn J.capacity)).2+
    40*Nat.clog 2 (J.m+1)+900 ≤ _
  change 200*(sortCapacities (List.ofFn J.capacity)).2+
    40*Nat.clog 2 ((List.ofFn J.capacity).length+1)+700 ≤ _ at h
  simp only [List.length_ofFn,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one] at h ⊢
  omega

end MinCostFlow.Scaling.Machine
