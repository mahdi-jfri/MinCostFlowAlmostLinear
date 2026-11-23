module

public import MinCostFlow.IPM.Machine.GuardedCoefficientRefresh

/-!
# Memory and allocation facts for guarded coefficient refresh

The relational postcondition exposes the guard's actual intermediate
state. Its two branches imply a common allocation bound and frame for
all caller cells outside the two coefficient entries. A rejection keeps
the entire old prefix. A disjoint data structure and its amortized
potential survive either branch, which permits the reported-edge loop
to compose the numerical work with parameter operations.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Either guard branch respects the same scratch bound, preserves the
fresh suffix, and changes only the two old coefficient entries. -/
theorem guardedCoefficientRefresh_frame
    {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (guardedCoefficientRefreshContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem') :
    heap≤v ∧ v≤heap+(4*L+1)+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1 ∧
      ZeroFrom mem' v ∧
      (∀ z<heap,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem' z=mem z) ∧
      mem' (heap+4*L)≤1 := by
  obtain ⟨guardEnd,guardMem,hguard,hflag,hbranch⟩ := hout
  have he := hguard.2
  change guardEnd=heap+(4*L+1) at he
  have hframe := hguard.1.2.2.1
  change ∀ z<heap,guardMem z=mem z at hframe
  have hbit := hguard.1.2.2.2.2.1
  change guardMem (heap+4*L)≤1 at hbit
  change mem' (heap+4*L)=guardMem (heap+4*L) at hflag
  have hbit' : mem' (heap+4*L)≤1 := hflag ▸ hbit
  change (if guardMem (heap+4*L)=1 then _ else _) at hbranch
  split_ifs at hbranch with haccept
  · obtain ⟨hlo,hhi,hz,hfr,_,_,_,_⟩ := hbranch
    change guardEnd≤v at hlo
    change v≤guardEnd+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1 at hhi
    change ∀ z<guardEnd,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem' z=guardMem z at hfr
    refine ⟨by omega,by omega,hz,?_,hbit'⟩
    intro z hz h0 h1
    exact (hfr z (by omega) h0 h1).trans (hframe z hz)
  · obtain ⟨hv,hm⟩ := hbranch
    change v=guardEnd at hv
    change mem'=guardMem at hm
    have hz := hguard.1.2.2.2.1
    change ZeroFrom guardMem guardEnd at hz
    refine ⟨by omega,by omega,hm ▸ hv ▸ hz,?_,hbit'⟩
    intro z hz _ _
    rw [hm]
    exact hframe z hz

/-- Rejection returns at the guard endpoint and preserves every old cell. -/
theorem guardedCoefficientRefresh_reject
    {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (guardedCoefficientRefreshContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem')
    (hreject : mem' (heap+4*L)=0) :
    v=heap+(4*L+1) ∧ ∀ z<heap,mem' z=mem z := by
  obtain ⟨guardEnd,guardMem,hguard,hflag,hbranch⟩ := hout
  change mem' (heap+4*L)=guardMem (heap+4*L) at hflag
  have hz : guardMem (heap+4*L)=0 := hflag.symm.trans hreject
  change (if guardMem (heap+4*L)=1 then _ else _) at hbranch
  simp only [hz,zero_ne_one,ite_false] at hbranch
  obtain ⟨hv,hm⟩ := hbranch
  have he := hguard.2
  change guardEnd=heap+(4*L+1) at he
  have hf := hguard.1.2.2.1
  change ∀ z<heap,guardMem z=mem z at hf
  change v=guardEnd at hv
  change mem'=guardMem at hm
  exact ⟨hv.trans he,fun z hz => (congrFun hm z).trans (hf z hz)⟩

/-- The reported-edge numerical work preserves a disjoint data structure
and its potential on both acceptance and rejection. -/
theorem guardedCoefficientRefresh_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w h q K m c r lo f up a one mn mx L P E ld gd heap v b : ℕ}
    {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (guardedCoefficientRefreshContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem')
    (hrep : R.rep b s x mem)
    (hfoot : ∀ z,R.foot b x z → z<heap ∧ (z<ld ∨ ld+L≤z) ∧ (z<gd ∨ gd+L≤z)) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  have hf := (guardedCoefficientRefresh_frame hout).2.2.2.1
  have hsame : ∀ z,R.foot b x z → mem z=mem' z := by
    intro z hz
    exact (hf z (hfoot z hz).1 (hfoot z hz).2.1 (hfoot z hz).2.2).symm
  have hh := hlocal b s x mem mem' hsame
  exact ⟨hh.1 hrep,hh.2⟩

/-- Two distinct entries of the same dense table occupy disjoint blocks,
including when the limb count is zero. -/
theorem reported_blocks_disjoint (base L e j : ℕ) (hne : e≠j) :
    base+e*L+L≤base+j*L ∨ base+j*L+L≤base+e*L := by
  rcases Nat.lt_or_gt_of_ne hne with he | hj
  · have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
    simp only [Nat.succ_mul] at hh
    exact Or.inl (by omega)
  · have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hj)
    simp only [Nat.succ_mul] at hh
    exact Or.inr (by omega)

/-- Every represented block disjoint from the two destination entries
retains its validity and exact decoded value. This includes coefficients
of other reported edges that the loop has already refreshed. -/
theorem guardedCoefficientRefresh_preserves_block
    {w h q K m c r lo f up a one mn mx L P E ld gd heap v p N precision : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (guardedCoefficientRefreshContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem')
    (hp : p+N≤heap) (hpl : p+N≤ld ∨ ld+L≤p) (hpg : p+N≤gd ∨ gd+L≤p)
    (hvalid : Num.Valid mem p h N) :
    Num.Valid mem' p h N ∧ Num.fixVal mem' p h N precision=Num.fixVal mem p h N precision := by
  have hf := (guardedCoefficientRefresh_frame hout).2.2.2.1
  have hsame : ∀ i<N,mem' (p+i)=mem (p+i) := by
    intro i hi
    apply hf (p+i) (by omega)
    · rcases hpl with hh | hh <;> omega
    · rcases hpg with hh | hh <;> omega
  refine ⟨?_,?_⟩
  · intro i hi
    rw [hsame i hi]
    exact hvalid i hi
  · unfold Num.fixVal
    rw [Num.intVal_congr hsame]

end MinCostFlow.IPM.Machine
