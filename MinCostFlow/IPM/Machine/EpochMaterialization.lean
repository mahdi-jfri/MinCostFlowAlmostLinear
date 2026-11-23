module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract

import MinCostFlow.IPM.Machine.HistoryAppend

import MinCostFlow.IPM.Machine.MinRatioBridge

/-!
# Materializing all coordinates at an epoch boundary

The checked reported-list procedure also handles a caller-owned list
of all graph edges. A successful run then recovers every coordinate,
not only the most recent Detect report. Its fresh status still stops
at the first rejected coordinate. Distinct complete names make the
number of Query calls exactly the graph's edge count.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A complete name list makes the existing checked refresh a full flow
materialization. Every stored coordinate is exact and strictly feasible;
its associated numerical coefficient guarantees also hold. -/
theorem reportedEdges_materializes_all {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hcover : ∀ e∈G.E,∃ i<count,mem (names+i)=e)
    (hout : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    count=G.E.card ∧
    (mem' (v-1)=1 → ∀ e∈G.E,reportedCachePost F A s m q base lo up f c r a ld gd e mem') := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,
    heq,hlen,hnd,hlist,hgraph,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hmem (e : ℕ) (he : e∈G.E) : e∈es := by
    obtain ⟨i,hi,hread⟩ := hcover e he
    have hi' : i<es.length := by omega
    exact List.mem_iff_getElem.mpr ⟨i,hi',(hlist i hi').symm.trans hread⟩
  have hset : es.toFinset=G.E := by
    ext e
    constructor
    · intro he
      exact (hgraph e (List.mem_toFinset.mp he)).1
    · intro he
      exact List.mem_toFinset.mpr (hmem e he)
  have hcount : count=G.E.card := by
    rw [← hset,List.toFinset_card_of_nodup hnd,hlen]
  refine ⟨hcount,?_⟩
  intro haccept e he
  obtain ⟨_,_,_,_,_,_,_,_,hcache,_⟩ := hout
  exact hcache haccept es hlist hlen e (hmem e he)

/-- After full materialization under `P`, the stored coordinates agree with the
actual accumulated flow of the parameter's valid history. -/
theorem reportedCachePost_history_flow_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (ht : t≤T)
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} (he : e∈(D.G t).E)
    (hcache : reportedCachePost F A (minRatioState A.eraseFailure D eta op t)
      m q base lo up f c r a ld gd e mem) :
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op t e := by
  exact hcache.2.1.trans (congrArg
    (fun z => Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+z)
    ((hA D eta op T hvalid hsize hP).1.1 t ht e he))

/-- After full materialization, the stored coordinates agree with the
actual accumulated flow of the parameter's valid history. -/
theorem reportedCachePost_history_flow_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t≤T)
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} (he : e∈(D.G t).E)
    (hcache : reportedCachePost F A (minRatioState A.eraseFailure D eta op t)
      m q base lo up f c r a ld gd e mem) :
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op t e :=
  reportedCachePost_history_flow_upTo_on F A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    D eta op T t hvalid hsize (fun _ _ => trivial) ht he hcache

/-- After full materialization, the stored coordinates agree with the
actual accumulated flow of the parameter's valid history. -/
theorem reportedCachePost_history_flow {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t≤T)
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} (he : e∈(D.G t).E)
    (hcache : reportedCachePost F A (minRatioState A.eraseFailure D eta op t)
      m q base lo up f c r a ld gd e mem) :
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op t e := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact reportedCachePost_history_flow_upTo F A κ α Ψ eps (hA.upTo M N)
    D eta op T t hvalid hsize ht he hcache

/-- A coordinate refreshed after the actual Detect under `P` caches the old
accumulated flow. Detect itself adds no increment. -/
theorem reportedCachePost_detect_flow_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s))
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} (he : e∈(D.G T).E)
    (hcache : reportedCachePost F A (A.detect (minRatioState A.eraseFailure D eta op T)).2
      m q base lo up f c r a ld gd e mem) :
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op T e := by
  let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  let eta' := Function.update eta (T+1) 0
  let op' := Function.update op (T+1) false
  have hv : MinRatioHistoryValid D' op' (T+1) := appendHistoryStage_valid_detect D op T hvalid
  have hP' := appendHistoryStage_stage_on (D:=D) (T:=T) [] (D.g T) (D.ℓ T) hP (hP T le_rfl)
  have he' : e∈(D'.G (T+1)).E := by
    simpa only [D',appendHistoryStage,Function.update_self] using he
  have hq := ((hA D' eta' op' (T+1) hv (appendHistoryStage_bounded [] (D.g T) (D.ℓ T) hsize) hP').1.1
    (T+1) le_rfl e he')
  dsimp only [D',eta',op'] at hq
  rw [appendHistoryStage_detect_state,appendHistoryStage_detect_flow] at hq
  exact hcache.2.1.trans (congrArg
    (fun z => Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+z) hq)

/-- A coordinate refreshed after the actual Detect caches the old
accumulated flow. Detect itself adds no increment. This holds on lower
guesses too, since Query correctness only needs a valid history. -/
theorem reportedCachePost_detect_flow_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} (he : e∈(D.G T).E)
    (hcache : reportedCachePost F A (A.detect (minRatioState A.eraseFailure D eta op T)).2
      m q base lo up f c r a ld gd e mem) :
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op T e :=
  reportedCachePost_detect_flow_upTo_on F A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    D eta op T hvalid hsize (fun _ _ => trivial) he hcache

/-- A coordinate refreshed after the actual Detect caches the old
accumulated flow. Detect itself adds no increment. This holds on lower
guesses too, since Query correctness only needs a valid history. -/
theorem reportedCachePost_detect_flow {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T)
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} (he : e∈(D.G T).E)
    (hcache : reportedCachePost F A (A.detect (minRatioState A.eraseFailure D eta op T)).2
      m q base lo up f c r a ld gd e mem) :
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op T e := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact reportedCachePost_detect_flow_upTo F A κ α Ψ eps (hA.upTo M N)
    D eta op T hvalid hsize he hcache

end MinCostFlow.IPM.Machine
