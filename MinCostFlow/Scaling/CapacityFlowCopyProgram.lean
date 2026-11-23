module

public import MinCostFlow.Scaling.CapacityStateLayout
public import WordRAM.CopyWords
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Returning a capacity state's flow as a solver array

The repeated capacity algorithm returns a state header. Read its exact
unsigned flow pointer and copy the referenced coordinates into fresh
memory. Returning the new heap places the flow in its final `m` words,
as required by the surrounding circulation-solving procedures.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[state,edgeCount,heap]`. -/
def capacityFlowCopyBody (copy : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .call 4 copy [.reg 3,.reg 2,.reg 1] ;;
  .ret (.bin .add (.reg 2) (.reg 1))

/-- Header reader followed by the shared word-copy procedure. -/
def capacityFlowCopyModule (b : ℕ) : List Stmt := [capacityFlowCopyBody (b+1),copyWords]

/-- Fresh exact unsigned flow output, with the shared heap frame and zero tail. -/
def capacityFlowCopyContract (w : ℕ) (J : Circulation) (s : CapacityState J) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ state heap,args=[state,J.m,heap] ∧ state+2≤heap ∧
      CapacityStateAt mem state heap s ∧ 1<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (List.ofFn (fun e => (s.flow e).toNat)))
    (fun _ _ => 17*J.m+60) (fun _ _ => J.m)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+J.m }

/-- Header reading and word copying have no random instruction. -/
theorem capacityFlowCopyModule_noRand (b : ℕ) : ∀ body ∈ capacityFlowCopyModule b,body.NoRand := by
  intro body hb
  simp only [capacityFlowCopyModule,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · simp only [capacityFlowCopyBody,Stmt.NoRand,and_self]
  · simp only [copyWords,forRange,forUp,Stmt.NoRand,and_self]

/-- Copying a represented capacity flow returns its exact unsigned array
with linear cost, exact allocation, and preserved old memory. -/
theorem capacityFlowCopy_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityFlowCopyModule b)) (J : Circulation) (s : CapacityState J) :
    MeetsContract w p b (capacityFlowCopyContract w J s) := by
  have hk := copyWords_meetsContract (w := w) (hasAt_tail hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨state,heap,rfl,hstateEnd,hstate,hw⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+J.m<2^w at hspace
  obtain ⟨ptr,hheader,hptrEnd,hread⟩ := hstate
  have hs : state<2^w := by omega
  have hpWord : ptr<2^w := by omega
  have hh : heap<2^w := by omega
  have hm : J.m<2^w := by omega
  have hptrCell : mem state=ptr := by
    have h : mem (state+0)=ptr := hheader 0 (by change 0<2; decide)
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
  · simp only [capacityFlowCopyContract,heapContract,copyWordsContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg]
    omega

/-- Every edge count has joint flow-copy premises, represented by the
initial zero flow and a concrete all-zero memory. -/
theorem exists_capacityFlowCopy_pre (J : Circulation) :
    ∃ w,(∀ x∈[J.m,J.m,J.m+2],x<2^w) ∧
      (capacityFlowCopyContract w J (CapacityState.initial J)).pre [J.m,J.m,J.m+2] (fun _ => 0) := by
  let w := 2*J.m+5
  have hw : 2*J.m+5<2^w := Nat.lt_two_pow_self
  have hstate : CapacityStateAt (fun _ => 0) J.m (J.m+2) (CapacityState.initial J) := by
    refine ⟨0,?_,by omega,?_⟩
    · intro i hi
      have hi' : i=0 ∨ i=1 := by change i<2 at hi; omega
      rcases hi' with rfl | rfl <;> rfl
    · funext e
      rfl
  refine ⟨w,?_,⟨J.m,J.m+2,rfl,le_rfl,hstate,by omega⟩,(fun _ _ => rfl),?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · change J.m+2+J.m<2^w
    omega

end MinCostFlow.Scaling.Machine
