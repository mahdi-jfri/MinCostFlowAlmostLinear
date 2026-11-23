module

public import MinCostFlow.IPM.Machine.CoefficientRangeList
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Building the reported coefficient-check input

A stable Detect answer supplies exactly the names to check. Valid
coefficient blocks for those names and fitting table extents give all
read and comparison bounds. No bound on the coefficient values is
assumed: deciding those bounds is the guard's job.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A stable report and valid refreshed blocks supply the list guard's
complete input. The endpoint blocks are only required to be valid. -/
theorem coefficientRangeList_pre_of_detect {w h report heap g l neg mx mn L m : ℕ}
    {S : Finset ℕ} {mem : ℕ → ℕ}
    (hreport : DetectAt mem report S) (hend : report+1+S.card≤heap)
    (hheap : heap<2^w) (hw : 1<2^w) (hm : m<2^w)
    (hsubset : ∀ e∈S,e<m)
    (hgEnd : g+m*L<2^w) (hlEnd : l+m*L<2^w)
    (hnEnd : neg+L<2^w) (hxEnd : mx+L<2^w) (hmEnd : mn+L<2^w)
    (hnValid : Num.Valid mem neg h L) (hxValid : Num.Valid mem mx h L)
    (hmValid : Num.Valid mem mn h L)
    (hvalid : ∀ e∈S,Num.Valid mem (g+e*L) h L ∧ Num.Valid mem (l+e*L) h L) :
    (coefficientRangeListContract w h).pre [report+1,S.card,g,l,neg,mx,mn,L] mem := by
  refine ⟨report+1,S.card,g,l,neg,mx,mn,L,rfl,hw,?_⟩
  obtain ⟨es,hnd,hset,hheader,hnames⟩ := hreport
  have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  intro i hi
  have hiList : i<es.length := by omega
  have hread := hnames i hiList
  have he : es[i]∈S := by rw [← hset]; exact List.mem_toFinset.mpr (List.getElem_mem hiList)
  have heM := hsubset _ he
  have heWord := heM.trans hm
  have hgEntry := (reported_entry_end g L es[i] m heM).trans_lt hgEnd
  have hlEntry := (reported_entry_end l L es[i] m heM).trans_lt hlEnd
  have hv := hvalid _ he
  refine ⟨by omega,?_,?_⟩
  · rw [hread]
    exact heWord
  · rw [hread]
    exact ⟨neg,g+es[i]*L,mx,mn,l+es[i]*L,L,rfl,
      ⟨neg,g+es[i]*L,mx,L,rfl,hnEnd,hgEntry,hxEnd,hnValid,hv.1,hxValid⟩,
      ⟨mn,l+es[i]*L,mx,L,rfl,hmEnd,hlEntry,hxEnd,hmValid,hv.2,hxValid⟩⟩

end MinCostFlow.IPM.Machine
