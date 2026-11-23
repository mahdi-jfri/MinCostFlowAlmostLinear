module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract

/-!
# Packaging a reported-list postcondition for its actual name order

The contract quantifies over every list stored at the original name
address with the given length. Such a list is unique. It therefore
suffices to prove the frame and cache conditions for the actual Detect
order, while retaining the concrete DS state and allocation bounds.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual stored name list determines all list-quantified clauses
of the complete reported-list postcondition. -/
theorem reportedEdges_post_of_list {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x x' : R.τ} {mem mem' : ℕ → ℕ} (es : List ℕ)
    (hlist : ListAt mem names es) (hlen : es.length=count)
    (hrep : R.rep b s x' mem')
    (hmeta : ∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (hlo : heap≤v) (hhi : v≤heap+count*reportedEdgesScratch F m b E allocation+1)
    (hzero : ZeroFrom mem' v) (hbit : mem' (v-1)≤1)
    (hframe : ∀ z<heap,¬ R.foot b x z →
      (∀ e∈es,(z<f+e*F.limbs ∨ f+e*F.limbs+F.limbs≤z) ∧
        (z<ld+e*F.limbs ∨ ld+e*F.limbs+F.limbs≤z) ∧
        (z<gd+e*F.limbs ∨ gd+e*F.limbs+F.limbs≤z)) → mem' z=mem z)
    (hcache : mem' (v-1)=1 → ∀ e∈es,reportedCachePost F A s m q base lo up f c r a ld gd e mem')
    (hsafe : mem' (v-1)=1 ↔
      ∀ e∈es,ReportedCandidateSafe F A s mem e (base+e*F.limbs) (lo+e*F.limbs) (up+e*F.limbs) E) :
    (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem' := by
  have unique (other : List ℕ) (ho : ListAt mem names other) (hl : other.length=count) : other=es :=
    List.ext_getElem (hl.trans hlen.symm) (fun i hi hj => (ho i hi).symm.trans (hlist i hj))
  refine ⟨x',hrep,hmeta,hlo,hhi,hzero,hbit,?_,?_,?_⟩
  · intro other ho hl
    rw [unique other ho hl]
    exact hframe
  · intro hb other ho hl
    rw [unique other ho hl]
    exact hcache hb
  · intro other ho hl
    rw [unique other ho hl]
    exact hsafe

end MinCostFlow.IPM.Machine
