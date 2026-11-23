module

public import MinCostFlow.IPM.Machine.ReportStatus
public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.IPM.Machine.ReportedEdgesContract
import MinCostFlow.IPM.Machine.ReportedCacheCongr
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Fresh budget metadata between epoch iterations

The guarded target test caps the total reported names per epoch, as in
the Query-budget guard of its failure-aware model. Store the remaining
budget, this iteration's report size and its success bit in three fresh
words. The next iteration reads its budget at incoming heap minus three.
No old caller table or DS representation word is changed.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[remaining,count,status,heap]`; write those three words
and return heap plus three. The last two use the existing status writer. -/
def epochBudgetRecordBody (record : ℕ) : Stmt :=
  .store (.reg 3) (.reg 0) ;;
  .call 4 record [.reg 1,.reg 2,.bin .add (.reg 3) (.const 1)] ;;
  .ret (.reg 4)

/-- Exact three-word fresh metadata and complete old-prefix frame. -/
def epochBudgetRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ remaining count bit heap,args=[remaining,count,bit,heap] ∧ bit≤1)
    (fun args _ mem' => mem' (heapArg args)=args.getD 0 0 ∧
      mem' (heapArg args+1)=args.getD 1 0 ∧ mem' (heapArg args+2)=args.getD 2 0)
    (fun _ _ => 60) (fun _ _ => 3)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+3}

/-- The budget metadata writer has no random caller instruction. -/
theorem epochBudgetRecordBody_noRand (record : ℕ) : (epochBudgetRecordBody record).NoRand := by
  simp [epochBudgetRecordBody,Stmt.NoRand]

/-- The actual store and status call construct all three metadata words
with their complete frame, exact allocation and counted operations. -/
theorem epochBudgetRecord_meetsContract {w record entry : ℕ} {p : Program}
    (hp : p.procs[entry]?=some (epochBudgetRecordBody record))
    (hrecord : MeetsContract w p record (reportStatusContract w)) :
    MeetsContract w p entry (epochBudgetRecordContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨⟨remaining,count,bit,heap,rfl,hbit⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+3<2^w at hspace
  have hremaining : remaining<2^w := hwords _ (by simp)
  have hcount : count<2^w := hwords _ (by simp)
  have hbitWord : bit<2^w := hwords _ (by simp)
  have hheap : heap<2^w := by omega
  have hOne : 1<2^w := by omega
  have hnext : heap+1<2^w := by omega
  apply runs_start_le
  unfold epochBudgetRecordBody
  wram_step
  refine runs_seq_call_le hrecord (vs:=[count,bit,heap+1]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨⟨count,bit,heap+1,rfl,hbit⟩,?_,?_⟩
    · change ZeroFrom (Function.update mem heap remaining) (heap+1)
      intro z hz'
      rw [Function.update_of_ne (by omega : z≠heap)]
      exact hz z (by omega)
    · change (heap+1)+2<2^w
      omega
  intro v final pos' hout
  have hv : v=heap+3 := by have hh := hout.2; change v=heap+1+2 at hh; omega
  have hvWord : v<2^w := by omega
  have hf : ∀ z<heap+1,final z=Function.update mem heap remaining z := hout.1.2.2.1
  have hd := hout.1.2.2.2.2
  change final (heap+1)=count ∧ final (heap+1+1)=bit at hd
  refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
  · change (heap≤v ∧ v≤heap+3 ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧
      final heap=remaining ∧ final (heap+1)=count ∧ final (heap+2)=bit) ∧ v=heap+3
    refine ⟨⟨by omega,by omega,?_,hout.1.2.2.2.1,?_,hd.1,by simpa only [Nat.add_assoc] using hd.2⟩,hv⟩
    · intro z hz'
      exact (hf z (by omega)).trans (Function.update_of_ne (by omega : z≠heap) _ _)
    · simpa using hf heap (by omega)
  · simp only [epochBudgetRecordContract,reportStatusContract,boundedStatusRecordContract,heapContract,Expr.size_reg,Expr.size_bin,
      Expr.size_const,argsSize_cons,argsSize_nil]
    omega

/-- The next iteration decodes remaining budget, report count and bit
at fixed offsets from the actual returned allocation endpoint. -/
theorem epochBudgetRecord_output {w remaining count bit heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochBudgetRecordContract w).post [remaining,count,bit,heap] mem v mem') :
    mem' (v-3)=remaining ∧ mem' (v-2)=count ∧ mem' (v-1)=bit := by
  have hv : v=heap+3 := hout.2
  have hd := hout.1.2.2.2.2
  change mem' heap=remaining ∧ mem' (heap+1)=count ∧ mem' (heap+2)=bit at hd
  have h0 : v-3=heap := by omega
  have h1 : v-2=heap+1 := by omega
  have h2 : v-1=heap+2 := by omega
  simpa only [h0,h1,h2] using hd

/-- The fresh metadata preserves the exact concrete state and credit
that the completed iteration returned. -/
theorem epochBudgetRecord_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w remaining count bit heap v b : ℕ} {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (epochBudgetRecordContract w).post [remaining,count,bit,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  have hframe : ∀ z<heap,mem' z=mem z := hout.1.2.2.1
  have hh := hlocal b s x mem mem' (fun z hz => (hframe z (hfoot z hz)).symm)
  exact ⟨hh.1 hrep,hh.2⟩

/-- All earlier doubled-width Update answers survive the budget record,
so the actual effective normalization and transition remain decodable. -/
theorem epochBudgetRecord_scalar {w remaining count bit heap v a h L P : ℕ}
    {mem mem' : ℕ → ℕ} {scalar : ℝ}
    (hout : (epochBudgetRecordContract w).post [remaining,count,bit,heap] mem v mem')
    (hend : a+L≤heap) (hscalar : ScalarAt mem a h L P scalar) : ScalarAt mem' a h L P scalar := by
  have hframe : ∀ z<heap,mem' z=mem z := hout.1.2.2.1
  exact ⟨Num.IPM.valid_frozen hframe hend hscalar.1,
    (Num.IPM.fixVal_frozen hframe hend).trans hscalar.2⟩

/-- Fresh budget metadata preserves a cached edge's exact recovery,
coefficient accuracy, valid words and strict slacks at its held state. -/
theorem epochBudgetRecord_cache {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (s : A.State)
    {remaining count bit heap v m q base lo up f c r a ld gd e : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochBudgetRecordContract w).post [remaining,count,bit,heap] mem v mem')
    (hends : ∀ p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,f+e*F.limbs,
      up+e*F.limbs,a,ld+e*F.limbs,gd+e*F.limbs],p+F.limbs≤heap)
    (hcache : reportedCachePost F A s m q base lo up f c r a ld gd e mem) :
    reportedCachePost F A s m q base lo up f c r a ld gd e mem' := by
  apply reportedCachePost_congr F A s (mem:=mem) (mem':=mem') _ hcache
  intro p hp i hi
  have hend := hends p hp
  have hframe := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  exact hframe _ (by omega)

end MinCostFlow.IPM.Machine
