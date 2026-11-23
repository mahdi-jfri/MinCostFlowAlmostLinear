module

public import MinCostFlow.Scaling.UnsignedFlowProgram

/-!
# Reading converted unsigned flows as signed tables

The pruned circulation solver returns unsigned magnitudes. The existing
conversion loop writes their canonical signed pairs. This interface reads
that same output as a vertex-indexed signed table so that the original
edge indices can be restored by the signed scatter program.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Convert a nonnegative integer vector from one word per coordinate to
its canonical two-word signed table. -/
def unsignedFlowTableContract (w : ℕ) {n : ℕ} (f : Fin n → ℤ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ src heap,args=[src,n,heap] ∧
      ListAt mem src (List.ofFn (fun e => (f e).toNat)) ∧ src+n≤heap ∧
      (∀ e,0≤f e ∧ (f e).natAbs<2^w) ∧ 1<2^w)
    (fun args _ mem' => SignedTableAt mem' (heapArg args) f)
    (fun _ _ => 100*n+20) (fun _ _ => 2*n)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+2*n }

/-- The unsigned conversion loop gives the exact signed-table interface
with unchanged instructions, allocation, and linear cost. -/
theorem unsignedFlowTable_meetsContract {w b n : ℕ} {p : Program}
    (hp : p.HasAt b (unsignedFlowModule b)) (f : Fin n → ℤ) :
    MeetsContract w p b (unsignedFlowTableContract w f) := by
  let xs := List.ofFn (fun e => (f e).toNat)
  have hlen : xs.length=n := List.length_ofFn
  have hk := unsignedFlow_meetsContract (w := w) hp xs
  intro args mem pos ω hwords hpre
  obtain ⟨⟨src,heap,rfl,hat,hend,hvalues,h1⟩,hz,hs⟩ := hpre
  have heapEq : heapArg [src,n,heap]=heap := by simp [heapArg]
  have hpreS : (unsignedFlowContract w xs).pre [src,n,heap] mem := by
    refine ⟨⟨src,heap,by rw [hlen],hat,by rwa [hlen],?_,h1⟩,hz,?_⟩
    · intro x hx
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
      have heq := congrArg Int.natAbs (Int.toNat_of_nonneg (hvalues e).1)
      have habs : (f e).toNat=(f e).natAbs := by simpa only [Int.natAbs_natCast] using heq
      rw [habs]
      exact (hvalues e).2
    · change heap+2*xs.length<2^w
      simpa only [hlen,heapEq] using hs
  obtain ⟨body,hbody,o,st',c,hrun,hpost,hcost⟩ := hk _ _ pos ω hwords hpreS
  obtain ⟨⟨hlo,hhi,hframe,hz',houtput⟩,hret⟩ := hpost
  rw [heapEq] at hlo hhi hframe houtput hret
  have hcast : (fun e => ((f e).toNat : ℤ))=f := by
    funext e
    exact Int.toNat_of_nonneg (hvalues e).1
  have hout : ListAt st'.mem heap ((List.ofFn f).flatMap encodeInt) := by
    simpa only [xs,←List.flatMap_map,List.map_ofFn,Function.comp_def,hcast] using houtput
  refine ⟨body,hbody,o,st',c,hrun,?_,?_⟩
  · change (heap≤o.value ∧ o.value≤heap+2*n ∧ (∀ x<heap,st'.mem x=mem x) ∧
      ZeroFrom st'.mem o.value ∧ SignedTableAt st'.mem heap f) ∧ o.value=heap+2*n
    exact ⟨⟨hlo,by simpa only [hlen] using hhi,hframe,hz',signedTableAt_of_listAt _ _ _ hout⟩,
      by simpa only [hlen] using hret⟩
  · simpa only [unsignedFlowContract,unsignedFlowTableContract,heapContract,hlen] using hcost

/-- Every nonnegative integer vector has simultaneous conversion premises
in canonical unsigned source memory at some finite width. -/
theorem exists_unsignedFlowTable_pre {n : ℕ} (f : Fin n → ℤ) (hf : ∀ e,0≤f e) :
    ∃ w,(∀ x∈[0,n,n],x<2^w) ∧
      (unsignedFlowTableContract w f).pre [0,n,n]
        (initMem (List.ofFn (fun e => (f e).toNat))) := by
  let xs := List.ofFn (fun e => (f e).toNat)
  have hlen : xs.length=n := List.length_ofFn
  obtain ⟨w,hwords,hpre⟩ := exists_unsignedFlow_pre xs
  obtain ⟨⟨src,heap,hargs,hat,hend,hvalues,h1⟩,hz,hs⟩ := hpre
  have heq : src=0 ∧ heap=n := by
    have ha := congrArg (fun ys : List ℕ => ys.getD 0 0) hargs
    have hh := congrArg (fun ys : List ℕ => ys.getD 2 0) hargs
    exact ⟨by simpa using ha.symm,by simpa only [hlen,List.getD_cons_succ,List.getD_cons_zero] using hh.symm⟩
  obtain ⟨hsrc,hheap⟩ := heq
  subst src
  subst heap
  refine ⟨w,by simpa only [hlen] using hwords,⟨0,n,rfl,hat,by omega,?_,h1⟩,?_,?_⟩
  · intro e
    have hv := hvalues _ (List.mem_ofFn.mpr ⟨e,rfl⟩)
    have he := congrArg Int.natAbs (Int.toNat_of_nonneg (hf e))
    simp only [Int.natAbs_natCast] at he
    exact ⟨hf e,he ▸ hv⟩
  · simpa only [hlen] using hz
  · change n+2*n<2^w
    simpa [heapArg,hlen] using hs

end MinCostFlow.Scaling.Machine
