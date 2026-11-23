module

public import MinCostFlow.Scaling.PotentialUpdateScanProgram
public import MinCostFlow.Scaling.SignedTableLayout
import MinCostFlow.Scaling.PotentialUpdateScanWitness

/-!
# The cost-state potential-table update

View the two vertex-indexed signed tables as the paired coordinate list
scanned by the machine. The list scan's exact doubled sums give the new
vertex-indexed potential table. This changes only the interface, with no
additional instructions, allocation, or cost.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Exact vertex-indexed potential update on the shared signed tables. -/
def potentialUpdateContract (w : ℕ) {n : ℕ} (f g : Fin n → ℤ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ a b heap,args=[a,b,n,heap] ∧ SignedTableAt mem a f ∧ SignedTableAt mem b g ∧
      a+2*n≤heap ∧ b+2*n≤heap ∧ (∀ v,2*((f v).natAbs+(g v).natAbs)<2^w) ∧ 2<2^w)
    (fun args _ mem' => SignedTableAt mem' (heapArg args) (fun v => 2*(f v+g v)))
    (fun _ _ => 300*n+20) (fun _ _ => 2*n)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+2*n }

/-- The existing scan computes exactly the new cost-state potential vector,
with `300*n+20` cost and exactly `2*n` fresh words. -/
theorem potentialUpdate_meetsContract {w b n : ℕ} {p : Program}
    (hp : p.HasAt b (potentialUpdateScanModule b)) (f g : Fin n → ℤ) :
    MeetsContract w p b (potentialUpdateContract w f g) := by
  let xs := List.ofFn (fun v => (f v,g v))
  have hlen : xs.length=n := List.length_ofFn
  have hk := potentialUpdateScan_meetsContract (w := w) hp xs
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,bp,heap,rfl,hleft,hright,haEnd,hbEnd,hvalues,h2⟩,hz,hs⟩ := hpre
  have heapEq : heapArg [a,bp,n,heap]=heap := by simp [heapArg]
  have hpreS : (potentialUpdateScanContract w xs).pre [a,bp,n,heap] mem := by
    refine ⟨⟨a,bp,heap,by rw [hlen],?_,?_,by rwa [hlen],by rwa [hlen],?_,h2⟩,hz,?_⟩
    · simpa only [xs,List.map_ofFn,Function.comp_def] using hleft.listAt
    · simpa only [xs,List.map_ofFn,Function.comp_def] using hright.listAt
    · intro x hx
      obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hx
      exact hvalues v
    · change heap+2*xs.length<2^w
      simpa only [hlen,heapEq] using hs
  obtain ⟨body,hbody,o,st',c,hrun,hpost,hcost⟩ := hk _ _ pos ω hwords hpreS
  obtain ⟨⟨hlo,hhi,hframe,hz',houtput⟩,hret⟩ := hpost
  rw [heapEq] at hlo hhi hframe houtput hret
  have houtput' : ListAt st'.mem heap ((List.ofFn (fun v => 2*(f v+g v))).flatMap encodeInt) := by
    simpa only [xs,List.map_ofFn,Function.comp_def] using houtput
  refine ⟨body,hbody,o,st',c,hrun,?_,?_⟩
  · change (heap≤o.value ∧ o.value≤heap+2*n ∧ (∀ x<heap,st'.mem x=mem x) ∧
      ZeroFrom st'.mem o.value ∧ SignedTableAt st'.mem heap (fun v => 2*(f v+g v))) ∧ o.value=heap+2*n
    exact ⟨⟨hlo,by simpa only [hlen] using hhi,hframe,hz',signedTableAt_of_listAt _ _ _ houtput'⟩,
      by simpa only [hlen] using hret⟩
  · simpa only [potentialUpdateScanContract,potentialUpdateContract,heapContract,hlen] using hcost

/-- Every pair of potential tables has simultaneous entry premises at some
finite width, with both sources stored in canonical consecutive arrays. -/
theorem exists_potentialUpdate_pre {n : ℕ} (f g : Fin n → ℤ) :
    ∃ w mem,(∀ a∈[0,2*n,n,4*n],a<2^w) ∧
      (potentialUpdateContract w f g).pre [0,2*n,n,4*n] mem := by
  let xs := List.ofFn (fun v => (f v,g v))
  have hlen : xs.length=n := List.length_ofFn
  obtain ⟨w,hwords,hpre⟩ := exists_potentialUpdateScan_pre xs
  obtain ⟨⟨a,bp,heap,hargs,hleft,hright,haEnd,hbEnd,hvalues,h2⟩,hz,hs⟩ := hpre
  have heq : a=0 ∧ bp=2*n ∧ heap=4*n := by
    have ha := congrArg (fun ys : List ℕ => ys.getD 0 0) hargs
    have hb := congrArg (fun ys : List ℕ => ys.getD 1 0) hargs
    have hh := congrArg (fun ys : List ℕ => ys.getD 3 0) hargs
    exact ⟨by simpa using ha.symm,by simpa [hlen] using hb.symm,by simpa [hlen] using hh.symm⟩
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hz' : ZeroFrom (initMem (((xs.map Prod.fst).flatMap encodeInt)++((xs.map Prod.snd).flatMap encodeInt))) (4*n) := by simpa [heapArg,hlen] using hz
  refine ⟨w,_,by simpa only [hlen] using hwords,
    ⟨0,2*n,4*n,rfl,?_,?_,by simpa only [hlen] using haEnd,
      by simpa only [hlen] using hbEnd,?_,h2⟩,hz',?_⟩
  · apply signedTableAt_of_listAt
    simpa only [xs,List.map_ofFn,Function.comp_def] using hleft
  · apply signedTableAt_of_listAt
    simpa only [xs,List.map_ofFn,Function.comp_def] using hright
  · intro v
    exact hvalues (f v,g v) (List.mem_ofFn.mpr ⟨v,rfl⟩)
  · change 4*n+2*n<2^w
    simpa [heapArg,hlen] using hs

end MinCostFlow.Scaling.Machine
