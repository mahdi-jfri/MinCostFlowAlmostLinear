module

public import MinCostFlow.Scaling.CostStateLayout
public import MinCostFlow.Scaling.CapacityFlowCopyProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CostStateMemory
import WordRAM.Tactic

/-!
# Returning a cost state's flow as a solver array

The repeated cost algorithm returns a three-word state header. Read its exact
unsigned flow pointer and copy the referenced coordinates into fresh
memory. Returning the new heap places the flow in its final `m` words,
as required by the surrounding circulation-solving procedures.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The common first-pointer header reader and flow-copy module. -/
abbrev costFlowCopyModule (b : ℕ) : List Stmt := capacityFlowCopyModule b

/-- Fresh exact unsigned flow output, with the shared heap frame and zero tail. -/
def costFlowCopyContract (w : ℕ) (J : Circulation) (s : CostState J) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ state heap,args=[state,J.m,heap] ∧ state+3≤heap ∧
      CostStateAt mem state heap s ∧ 1<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (List.ofFn (fun e => (s.flow e).toNat)))
    (fun _ _ => 17*J.m+60) (fun _ _ => J.m)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+J.m }

/-- Reading the flow pointer and copying coordinates is deterministic. -/
theorem costFlowCopyModule_noRand (b : ℕ) : ∀ body ∈ costFlowCopyModule b,body.NoRand :=
  capacityFlowCopyModule_noRand b

/-- Copying a represented cost-state flow returns its exact unsigned array
with linear cost, exact allocation, and preserved old memory. -/
theorem costFlowCopy_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (costFlowCopyModule b)) (J : Circulation) (s : CostState J) :
    MeetsContract w p b (costFlowCopyContract w J s) := by
  have hk := copyWords_meetsContract (w := w) (hasAt_tail hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨state,heap,rfl,hstateEnd,hstate,hw⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+J.m<2^w at hspace
  obtain ⟨ptr,pp,hheader,hptrEnd,hppEnd,hread,hpot⟩ := hstate
  have hs : state<2^w := by omega
  have hpWord : ptr<2^w := by omega
  have hh : heap<2^w := by omega
  have hm : J.m<2^w := by omega
  have hptrCell : mem state=ptr := by
    have h : mem (state+0)=ptr := hheader 0 (by change 0<3; decide)
    simpa only [Nat.add_zero] using h
  have hflow := solverOutput_listAt J hread
  apply runs_start_le
  unfold capacityFlowCopyBody
  refine runs_seq_assign_le (v := ptr) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [ptr,heap,J.m]) (by eval_expr) (by wram_words)
    ⟨ptr,heap,J.m,rfl,hw,by omega,hspace.le,Or.inr hptrEnd⟩ ?_
  intro ignored memC posC hpostC
  obtain ⟨src,dst,len,hargs,_,hcopied,hframe⟩ := hpostC
  have heq : ptr=src ∧ heap=dst ∧ J.m=len := by simpa only [List.cons.injEq,and_true] using hargs
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have houtput := copyWords_listAt hflow (List.length_ofFn) hcopied
  refine runs_ret_le (v := heap+J.m) (by eval_expr) ?_ ?_
  · change (heap≤heap+J.m ∧ heap+J.m≤heap+J.m ∧ (∀ x<heap,memC x=mem x) ∧
      ZeroFrom memC (heap+J.m) ∧ ListAt memC heap (List.ofFn (fun e => (s.flow e).toNat))) ∧
      heap+J.m=heap+J.m
    refine ⟨⟨by omega,le_rfl,fun x hx => hframe x (Or.inl hx),?_,houtput⟩,rfl⟩
    intro x hx
    exact (hframe x (Or.inr hx)).trans (hz x (by omega))
  · simp only [costFlowCopyContract,heapContract,copyWordsContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg]
    omega

/-- Every graph has simultaneous flow-copy entry premises represented
by its initial zero-flow, zero-potential, power-one cost state. -/
theorem exists_costFlowCopy_pre (J : Circulation) :
    ∃ w args mem,(∀ x∈args,x<2^w) ∧
      (costFlowCopyContract w J (CostState.initial J)).pre args mem := by
  obtain ⟨mem,state,heap,_,_,hstateEnd,hstate,hzero⟩ :=
    exists_costState_memory (CostState.initial J) (fun _ => le_rfl)
  let w := heap+J.m+2
  have hw : heap+J.m+2<2^w := Nat.lt_two_pow_self
  refine ⟨w,[state,J.m,heap],mem,?_,⟨state,heap,rfl,by omega,hstate,by omega⟩,hzero,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · change heap+J.m<2^w
    omega

end MinCostFlow.Scaling.Machine
