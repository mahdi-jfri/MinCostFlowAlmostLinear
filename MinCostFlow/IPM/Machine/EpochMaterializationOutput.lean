module

public import MinCostFlow.IPM.Machine.EpochMaterializationFeasible
public import MinCostFlow.IPM.Machine.EpochCacheMovement
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

import MinCostFlow.IPM.Machine.MinRatioBridge

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# Decoding a complete read of the current epoch flow

A full pass over the edge names leaves the immutable sources intact.
If the capacity and slack guards accept, the resulting array contains
the exact base-plus-implicit flow and is feasible. In a promised epoch
the potential supplies the strict slacks for these same guards.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Full coordinate materialization preserves the prefix preceding
the mutable cached-flow table. -/
theorem epoch_materialization_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v : ℕ) (s : A.State) (x : R.τ) (mem final : ℕ → ℕ)
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
      q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
      q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) mem v final) :
    ∀ z<L.flow,final z=mem z := by
  change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
    q K L.sourceEnd L.tableEnd).pre
    [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,L.alpha,
      L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem at hpre
  obtain ⟨names,count,base,lo,up,f,old,c,r,a,one,mn,mx,E,ld,gd,es,heq,
    hlen,_,hlist,_,_,_,_,havoid,_,hsEnd,htEnd,hnEnd,hends,_,_,_,hsL,hsG,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hf := hends L.flow (by simp)
  change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
    q K L.sourceEnd L.tableEnd).post
    [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,L.alpha,
      L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem v final at hout
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨_,_,_,_,_,_,_,hframe,_,_⟩ := hout
  intro z hz
  have hn := havoid z (by omega)
  exact hframe es hlist hlen z (by omega) hn
    (fun e _ => ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩)

/-- The full read under `P` cannot fail when the current historical flow
satisfies the strict machine slack ranges. -/
theorem epoch_materialization_accepts_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (hG : D.G T=namedInstance I)
    (hsource : epochSourcesAt F I L a r mem)
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v final)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-f ∧ (I.edge e).upper-f<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<f-(I.edge e).lower ∧ f-(I.edge e).lower<(2:ℝ)^L.exponent)) :
    final (v-1)=1 := by
  change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
    (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre
    [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,L.alpha,
      L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem at hpre
  obtain ⟨names,count,base,lo,up,f,old,c,r',a',one,mn,mx,E,ld,gd,es,heq,hlen,_,hlist,hgraph,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,_,_,haccept⟩ := hout
  apply (haccept es hlist hlen).mpr
  intro e he
  let idx : Fin I.m := ⟨e,(hgraph e he).2⟩
  have heG : e∈(D.G T).E := hG ▸ (hgraph e he).1
  have hQuery := (hA D eta op T hv hsize hP).1.1 T le_rfl e heG
  let candidate := epochVector F I mem L.base idx+A.query (minRatioState A.eraseFailure D eta op T) e
  have hEq : candidate=epochHistoryFlow I A D eta op T (epochVector F I mem L.base) idx :=
    congrArg (epochVector F I mem L.base idx+·) hQuery
  change (1/(2:ℝ)^L.exponent<epochVector F I mem L.upper idx-candidate ∧
      epochVector F I mem L.upper idx-candidate<(2:ℝ)^L.exponent) ∧
    (1/(2:ℝ)^L.exponent<candidate-epochVector F I mem L.lower idx ∧
      candidate-epochVector F I mem L.lower idx<(2:ℝ)^L.exponent)
  rw [hEq,(hsource.2.2 idx).1,(hsource.2.2 idx).2.1]
  exact hslacks idx

/-- The full read cannot fail when the current historical flow
satisfies the strict machine slack ranges. -/
theorem epoch_materialization_accepts_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (hG : D.G T=namedInstance I)
    (hsource : epochSourcesAt F I L a r mem)
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v final)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-f ∧ (I.edge e).upper-f<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<f-(I.edge e).lower ∧ f-(I.edge e).lower<(2:ℝ)^L.exponent)) :
    final (v-1)=1 :=
  epoch_materialization_accepts_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    rate allocation R L q K heap v T x a r mem final D eta op hv hsize (fun _ _ => trivial) hG
    hsource hpre hout hslacks

/-- The full read cannot fail when the current historical flow
satisfies the strict machine slack ranges. -/
theorem epoch_materialization_accepts {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    (hsource : epochSourcesAt F I L a r mem)
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v final)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-f ∧ (I.edge e).upper-f<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<f-(I.edge e).lower ∧ f-(I.edge e).lower<(2:ℝ)^L.exponent)) :
    final (v-1)=1 := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact epoch_materialization_accepts_upTo F A I κ α Ψ eps (hA.upTo M N) rate allocation R L q K
    heap v T x a r mem final D eta op hv hsize hG hsource hpre hout hslacks

/-- Each successful materialization under `P` is exactly the current historical
flow, in the fixed-point format and satisfying the original routing
and capacity conditions. -/
theorem epoch_materialization_flow_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j))
    (hSource : epochSourcesAt F I L a r final)
    (hBase : I.Routes (epochVector F I final L.base))
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hcover : ∀ e∈(namedInstance I).E,∃ j<I.m,mem (L.names+j)=e)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v final) (hbit : final (v-1)=1) :
    I.IsFeasible (epochVector F I final L.flow) ∧
    epochVector F I final L.flow=epochHistoryFlow I A D eta op T (epochVector F I final L.base) ∧
    ∀ e : Fin I.m,Num.Valid final (L.flow+e.val*F.limbs) F.fmt.limbBits F.limbs := by
  have hCache := (reportedEdges_materializes_all F A (namedInstance I) I.m rate allocation R hpre hcover hout).2 hbit
  have hMem (e : Fin I.m) : e.val∈(namedInstance I).E := Finset.mem_range.mpr e.isLt
  refine ⟨epoch_materialized_feasible_upTo_on F I A κ α Ψ eps hA D eta op T T hv hG hPD le_rfl hBase
    (fun e => (hSource.2.2 e).1) (fun e => (hSource.2.2 e).2.1) hCache,?_ ,
    fun e => (hCache e.val (hMem e)).1⟩
  funext e
  exact reportedCachePost_history_flow_upTo_on F A κ α Ψ eps hA D eta op T T hv
    (namedHistory_bounded hG) hPD le_rfl
    (by rw [hG T le_rfl]; exact hMem e) (hCache e.val (hMem e))

/-- Each successful materialization is exactly the current historical
flow, in the fixed-point format and satisfying the original routing
and capacity conditions. -/
theorem epoch_materialization_flow_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hSource : epochSourcesAt F I L a r final)
    (hBase : I.Routes (epochVector F I final L.base))
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hcover : ∀ e∈(namedInstance I).E,∃ j<I.m,mem (L.names+j)=e)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v final) (hbit : final (v-1)=1) :
    I.IsFeasible (epochVector F I final L.flow) ∧
    epochVector F I final L.flow=epochHistoryFlow I A D eta op T (epochVector F I final L.base) ∧
    ∀ e : Fin I.m,Num.Valid final (L.flow+e.val*F.limbs) F.fmt.limbBits F.limbs :=
  epoch_materialization_flow_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    rate allocation R L q K heap v T x a r mem final D eta op hv hG (fun _ _ => trivial) hSource hBase hpre hcover hout hbit

/-- Each successful materialization is exactly the current historical
flow, in the fixed-point format and satisfying the original routing
and capacity conditions. -/
theorem epoch_materialization_flow {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hSource : epochSourcesAt F I L a r final)
    (hBase : I.Routes (epochVector F I final L.base))
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hcover : ∀ e∈(namedInstance I).E,∃ j<I.m,mem (L.names+j)=e)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v final) (hbit : final (v-1)=1) :
    I.IsFeasible (epochVector F I final L.flow) ∧
    epochVector F I final L.flow=epochHistoryFlow I A D eta op T (epochVector F I final L.base) ∧
    ∀ e : Fin I.m,Num.Valid final (L.flow+e.val*F.limbs) F.fmt.limbBits F.limbs :=
  epoch_materialization_flow_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) rate allocation R L q K heap
    v T x a r mem final D eta op hv hG hSource hBase hpre hcover hout hbit


/-- A successful full read certifies the strict numerical slack range.
The two guards checked that range against the exact recovered
coordinate and the same immutable base and capacities. -/
theorem epoch_materialization_slacks {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap v : ℕ) (s : A.State) (x : R.τ) (a r : ℝ) (mem final : ℕ → ℕ)
    (hSource : epochSourcesAt F I L a r mem) (hbase : L.base+I.m*F.limbs≤L.flow)
    (hpre : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
      q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) mem)
    (hcover : ∀ e∈(namedInstance I).E,∃ j<I.m,mem (L.names+j)=e)
    (hout : (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
      q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) mem v final)
    (hbit : final (v-1)=1) :
    ∀ e : Fin I.m,
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-epochVector F I final L.flow e ∧
        (I.edge e).upper-epochVector F I final L.flow e<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<epochVector F I final L.flow e-(I.edge e).lower ∧
        epochVector F I final L.flow e-(I.edge e).lower<(2:ℝ)^L.exponent) := by
  have hcache := (reportedEdges_materializes_all F A (namedInstance I) I.m rate allocation R hpre hcover hout).2 hbit
  have hframe := epoch_materialization_frame F A I rate allocation R L q K heap v s x mem final hpre hout
  have hpre' := hpre
  change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s x
    q K L.sourceEnd L.tableEnd).pre
    [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,L.alpha,
      L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem at hpre'
  obtain ⟨names,count,base,lo,up,f,old,c,r',a',one,mn,mx,E,ld,gd,es,heq,hlen,_,hlist,_⟩ := hpre'
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,_,_,hsafe⟩ := hout
  intro e
  have heG : e.val∈(namedInstance I).E := Finset.mem_range.mpr e.isLt
  obtain ⟨j,hj,hread⟩ := hcover e.val heG
  have he : e.val∈es := List.mem_iff_getElem.mpr ⟨j,by omega,(hlist j (by omega)).symm.trans hread⟩
  have hs := (hsafe es hlist hlen).mp hbit e.val he
  let f := epochVector F I mem L.base e+A.query s e.val
  change
    (1/(2:ℝ)^L.exponent<epochVector F I mem L.upper e-f ∧
      epochVector F I mem L.upper e-f<(2:ℝ)^L.exponent) ∧
    (1/(2:ℝ)^L.exponent<f-epochVector F I mem L.lower e ∧
      f-epochVector F I mem L.lower e<(2:ℝ)^L.exponent) at hs
  rw [(hSource.2.2 e).1,(hSource.2.2 e).2.1] at hs
  have hbaseSame : epochVector F I final L.base e=epochVector F I mem L.base e :=
    Num.IPM.fixVal_frozen hframe
      ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans hbase)
  have hf : epochVector F I final L.flow e=epochVector F I final L.base e+A.query s e.val :=
    (hcache e.val heG).2.1
  rw [hbaseSame] at hf
  rw [hf]
  exact hs

end MinCostFlow.IPM.Machine
