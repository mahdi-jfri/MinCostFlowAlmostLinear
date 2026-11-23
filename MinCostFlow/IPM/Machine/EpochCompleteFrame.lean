module

public import MinCostFlow.IPM.Machine.EpochCompleteRun
public import MinCostFlow.IPM.Machine.BudgetedIterationFrame
import MinCostFlow.IPM.Machine.EpochMaterializationOutput
import MinCostFlow.IPM.Machine.BudgetedIterationOutput

/-!
# Memory after a completed or rejected epoch

Either return preserves the immutable source arrays. The new endpoint
has a zero suffix and its last word records acceptance.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The input packet places the mutable flow below the heap and outside the DS footprint. -/
theorem epoch_detect_source_geometry {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K h : ℕ) {mem : ℕ → ℕ} {s : A.State} {x : R.τ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I h).take 20) mem) :
    L.flow≤h ∧ (∀ z<L.flow,¬R.foot L.handle x z) := by
  obtain ⟨names,base,lo,up,f,cur,c,r,a,one,mn,mx,E,ld,gd,heq,hfull,_⟩ := hpre
  change [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,h,L.cost,L.residual,
    L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m]=_ at heq
  simp only [List.cons.injEq,true_and,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
    s x q K L.sourceEnd L.tableEnd).pre
    [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,h,L.cost,L.residual,
      L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem at hfull
  obtain ⟨names,count,base,lo,up,f,old,c,r,a,one,mn,mx,E,ld,gd,es,heq,
    _,_,_,_,_,_,_,havoid,_,hs,ht,hn,hends,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hf := hends L.flow (by simp)
  exact ⟨by omega,fun z hz => havoid z (by omega)⟩

/-- The geometry of the old Detect input gives the source frame even
when an attempted iteration returns failure. -/
theorem epoch_stopped_output {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish i : ℕ) (mem : ℕ → ℕ)
    {P : EpochPoint R.τ} {v : ℕ} {st : State} {credit : R.τ}
    (hcond : EpochConditions F A I κ α rate allocation R L q K mem heap space finish i P)
    (hstop : EpochStoppedStep F A I κ α rate allocation R L q K i P v st credit) :
    L.flow≤v ∧ st.mem (v-1)=0 ∧ ZeroFrom st.mem v ∧ (∀ z<L.flow,st.mem z=mem z) := by
  obtain ⟨_,_,_,_,_,_,hframe,_,_,hpre,_⟩ := hcond
  obtain ⟨hbit,_,_,hout,_,_,_⟩ := hstop
  obtain ⟨hf,havoid⟩ := epoch_detect_source_geometry F A I κ α rate allocation R L q K _ hpre
  have hlocal := budgetedIteration_source_frame F A I κ α rate allocation R hpre hout
    hf havoid
  have hEnd := budgetedIteration_end_ge F A I κ α rate allocation R hout
  exact ⟨by omega,hbit,(budgetedIteration_status hout).2.2,fun z hz => (hlocal z hz).trans (hframe z hz)⟩

/-- The complete epoch returns a boolean word, a zero suffix and an
unchanged prefix below the mutable flow block on either branch. -/
theorem epochComplete_output_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ α rate allocation R L q K heap space finish mem loopEnd loopState
      loopCredit certified v final credit)
    (hstopped : loopState.mem (loopEnd-1)≠1 →
      ∃ j<finish, ∃ Q : EpochPoint R.τ,
        EpochConditions F A I κ α rate allocation R L q K mem heap space finish j Q ∧
        EpochStoppedStep F A I κ α rate allocation R L q K j Q loopEnd loopState loopCredit)
    :
    L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) := by
  unfold EpochCompletePost at hpost
  split at hpost
  · obtain ⟨Q,hcond,_,_,hrecord,hpre,_,hout,_⟩ := hpost
    have hf := epoch_materialization_frame F A I rate allocation R L q K loopEnd v _ _ _ _ hpre hout
    have hframe := hcond.2.2.2.2.2.2.1
    have hflow := (epoch_detect_source_geometry F A I κ α rate allocation R L q K _
      hcond.2.2.2.2.2.2.2.2.2.1).1
    have hflag := hrecord.1.2.2.1
    have hflagEnd : loopEnd=Q.machine.regs 8+1 := hrecord.2
    obtain ⟨_,_,_,hEnd,_,hzero,hbit,_⟩ := hout
    change loopEnd≤v at hEnd
    exact ⟨by omega,hbit,hzero,fun z hz => (hf z hz).trans
      ((hflag z (hz.trans_le hflow)).trans (hframe z hz))⟩
  · rename_i hbit
    obtain ⟨j,_,Q,hcond,hstop⟩ := hstopped hbit
    obtain ⟨hEnd,_,hz,hf⟩ := epoch_stopped_output F A I κ α rate allocation R L q K heap space finish j mem hcond hstop
    obtain ⟨rfl,hm,_,hzero⟩ := hpost
    exact ⟨hEnd,by omega,hm ▸ hz,hm ▸ hf⟩

end MinCostFlow.IPM.Machine
