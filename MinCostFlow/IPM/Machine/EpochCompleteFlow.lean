module

public import MinCostFlow.IPM.Machine.EpochCompleteFrame
public import MinCostFlow.IPM.Machine.EpochMaterializationOutput
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# The explicit flow returned by a complete epoch

A successful return has performed the full read. The stored coordinates
are feasible, coincide with the final history and have the strict
slack ranges needed to start another epoch.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful complete epoch under `P` returns an exact fixed-point flow with
the machine's checked slack bounds, including on unpromised targets. -/
theorem epochComplete_output_flow_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ} {a r : ℝ}
    (hpost : EpochCompletePost F A I κ α rate allocation R L q K heap space finish mem loopEnd loopState
      loopCredit certified v final credit)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L a r mem)
    (hbase : I.Routes (epochVector F I mem L.base))
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hbit : final.mem (v-1)=1) :
    ∃ Q : EpochPoint R.τ, certified Q ∧ L.flow+I.m*F.limbs≤v ∧ I.IsFeasible (epochVector F I final.mem L.flow) ∧
      epochVector F I final.mem L.flow=
        epochHistoryFlow I A Q.history Q.eta Q.op (2*finish) (epochVector F I mem L.base) ∧
      ∀ e : Fin I.m,Num.Valid final.mem (L.flow+e.val*F.limbs) F.fmt.limbBits F.limbs ∧
        (1/(2:ℝ)^L.exponent<(I.edge e).upper-epochVector F I final.mem L.flow e ∧
          (I.edge e).upper-epochVector F I final.mem L.flow e<(2:ℝ)^L.exponent) ∧
        (1/(2:ℝ)^L.exponent<epochVector F I final.mem L.flow e-(I.edge e).lower ∧
          epochVector F I final.mem L.flow e-(I.edge e).lower<(2:ℝ)^L.exponent) := by
  unfold EpochCompletePost at hpost
  split at hpost
  · obtain ⟨Q,hcond,_,hcert,_,hpre,hcover,hout,_⟩ := hpost
    have hPD := hcond.stages hP
    obtain ⟨_,_,_,_,_,_,_,hvalid,hgraph,_⟩ := hcond
    have hbaseEnd := harrays L.base (by simp)
    have hbaseSame : epochVector F I final.mem L.base=epochVector F I mem L.base := by
      funext e
      exact Num.IPM.fixVal_frozen hframe
        ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans hbaseEnd)
    have hs := hsource.frozen hframe harrays hscalars
    obtain ⟨hfeas,heq,hvalidFlow⟩ := epoch_materialization_flow_upTo_on F A I κ α Ψ eps hA
      rate allocation R L q K loopEnd v (2*finish) Q.credit a r loopState.mem final.mem Q.history
      Q.eta Q.op hvalid hgraph hPD hs (hbaseSame.symm ▸ hbase) hpre hcover hout hbit
    have hreadFrame := epoch_materialization_frame F A I rate allocation R L q K loopEnd v _ _
      loopState.mem final.mem hpre hout
    have hreadSource := hs.frozen (fun z hz => (hreadFrame z hz).symm) harrays hscalars
    have hslacks := epoch_materialization_slacks F A I rate allocation R L q K loopEnd v _ _
      a r loopState.mem final.mem hreadSource hbaseEnd hpre hcover hout hbit
    rw [hbaseSame] at heq
    have hpre' := hpre
    change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) Q.credit q K L.sourceEnd L.tableEnd).pre
      [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,loopEnd,L.cost,L.residual,L.alpha,
        L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] loopState.mem at hpre'
    obtain ⟨names,count,base,lo,up,f,old,c,r',a',one,mn,mx,E,ld,gd,es,hpacket,
      _,_,_,_,_,_,_,_,_,hs,ht,hn,hends,_⟩ := hpre'
    simp only [List.cons.injEq,and_true,true_and] at hpacket
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := hpacket
    have hfEnd := hends L.flow (by simp)
    obtain ⟨_,_,_,hEnd,_⟩ := hout
    change loopEnd≤v at hEnd
    exact ⟨Q,hcert,by omega,hfeas,heq,fun e => ⟨hvalidFlow e,hslacks e⟩⟩
  · have hz := hpost.2.2.2
    omega

/-- A successful complete epoch returns an exact fixed-point flow with
the machine's checked slack bounds, including on unpromised targets. -/
theorem epochComplete_output_flow_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ} {a r : ℝ}
    (hpost : EpochCompletePost F A I κ α rate allocation R L q K heap space finish mem loopEnd loopState
      loopCredit certified v final credit)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L a r mem)
    (hbase : I.Routes (epochVector F I mem L.base))
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hbit : final.mem (v-1)=1) :
    ∃ Q : EpochPoint R.τ, certified Q ∧ L.flow+I.m*F.limbs≤v ∧ I.IsFeasible (epochVector F I final.mem L.flow) ∧
      epochVector F I final.mem L.flow=
        epochHistoryFlow I A Q.history Q.eta Q.op (2*finish) (epochVector F I mem L.base) ∧
      ∀ e : Fin I.m,Num.Valid final.mem (L.flow+e.val*F.limbs) F.fmt.limbBits F.limbs ∧
        (1/(2:ℝ)^L.exponent<(I.edge e).upper-epochVector F I final.mem L.flow e ∧
          (I.edge e).upper-epochVector F I final.mem L.flow e<(2:ℝ)^L.exponent) ∧
        (1/(2:ℝ)^L.exponent<epochVector F I final.mem L.flow e-(I.edge e).lower ∧
          epochVector F I final.mem L.flow e-(I.edge e).lower<(2:ℝ)^L.exponent) :=
  epochComplete_output_flow_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _)

    rate allocation R L q K heap space finish loopEnd mem loopState loopCredit certified
    hpost hframe hsource hbase harrays hscalars hbit

/-- A successful complete epoch returns an exact fixed-point flow with
the machine's checked slack bounds, including on unpromised targets. -/
theorem epochComplete_output_flow {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ} {a r : ℝ}
    (hpost : EpochCompletePost F A I κ α rate allocation R L q K heap space finish mem loopEnd loopState
      loopCredit certified v final credit)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L a r mem)
    (hbase : I.Routes (epochVector F I mem L.base))
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hbit : final.mem (v-1)=1) :
    ∃ Q : EpochPoint R.τ, certified Q ∧ L.flow+I.m*F.limbs≤v ∧ I.IsFeasible (epochVector F I final.mem L.flow) ∧
      epochVector F I final.mem L.flow=
        epochHistoryFlow I A Q.history Q.eta Q.op (2*finish) (epochVector F I mem L.base) ∧
      ∀ e : Fin I.m,Num.Valid final.mem (L.flow+e.val*F.limbs) F.fmt.limbBits F.limbs ∧
        (1/(2:ℝ)^L.exponent<(I.edge e).upper-epochVector F I final.mem L.flow e ∧
          (I.edge e).upper-epochVector F I final.mem L.flow e<(2:ℝ)^L.exponent) ∧
        (1/(2:ℝ)^L.exponent<epochVector F I final.mem L.flow e-(I.edge e).lower ∧
          epochVector F I final.mem L.flow e-(I.edge e).lower<(2:ℝ)^L.exponent) :=
  epochComplete_output_flow_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) rate allocation R L q K heap
    space finish loopEnd mem loopState loopCredit certified hpost hframe hsource hbase harrays
    hscalars hbit

end MinCostFlow.IPM.Machine
