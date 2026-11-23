module

public import MinCostFlow.IPM.Machine.CoefficientRangeListOutput
import MinCostFlow.IPM.Machine.ReportedTableLayout
import Mathlib.Tactic.Positivity

/-!
# Range scan of the fresh coefficient arrays

At epoch startup every name appears in order. The same signed
comparisons used after a Detect report therefore check every array
entry before the finite loop reads the coefficients.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A complete consecutive name list and fitting scalar blocks
supply the read-only scan's precondition. -/
theorem coefficientRangeList_full_pre {w h names m g l neg mx mn L : ℕ}
    {mem : ℕ → ℕ} (hlist : ListAt mem names (List.range m))
    (hOne : 1<2^w) (hn : names+m≤2^w) (hm : m≤2^w)
    (hg : g+m*L<2^w) (hl : l+m*L<2^w)
    (hneg : neg+L<2^w) (hmax : mx+L<2^w) (hmin : mn+L<2^w)
    (hvneg : Num.Valid mem neg h L) (hvmax : Num.Valid mem mx h L)
    (hvmin : Num.Valid mem mn h L)
    (hvalid : ∀ e<m,Num.Valid mem (g+e*L) h L ∧ Num.Valid mem (l+e*L) h L) :
    (coefficientRangeListContract w h).pre [names,m,g,l,neg,mx,mn,L] mem := by
  refine ⟨names,m,g,l,neg,mx,mn,L,rfl,hOne,?_⟩
  intro i hi
  have hread : mem (names+i)=i := by
    exact (hlist i (by simpa only [List.length_range] using hi)).trans (List.getElem_range _)
  rw [hread]
  exact ⟨by omega,by omega,neg,g+i*L,mx,mn,l+i*L,L,rfl,
    ⟨neg,g+i*L,mx,L,rfl,hneg,(reported_entry_end g L i m hi).trans_lt hg,hmax,hvneg,(hvalid i hi).1,hvmax⟩,
    ⟨mn,l+i*L,mx,L,rfl,hmin,(reported_entry_end l L i m hi).trans_lt hl,hmax,hvmin,(hvalid i hi).2,hvmax⟩⟩

/-- Decode the same full scan's bit in the common fixed-point scale. -/
theorem coefficientRangeList_full_output {w h names m g l neg mx mn L P v : ℕ}
    {mem final : ℕ → ℕ} {maximum minimum : ℝ}
    (hlist : ListAt mem names (List.range m))
    (hn : ScalarAt mem neg h L P (-maximum)) (hx : ScalarAt mem mx h L P maximum)
    (hm : ScalarAt mem mn h L P minimum)
    (hout : (coefficientRangeListContract w h).post [names,m,g,l,neg,mx,mn,L] mem v final) :
    v=1 ↔ ∀ e<m,|Num.fixVal mem (g+e*L) h L P|<maximum ∧
      minimum<Num.fixVal mem (l+e*L) h L P ∧ Num.fixVal mem (l+e*L) h L P<maximum := by
  have htest := hout.2.2
  change (v=1 ↔ ∀ i<m,coefficientsInRange mem h neg (g+mem (names+i)*L) mx mn
    (l+mem (names+i)*L) L) at htest
  rw [htest]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have hread : mem (names+e)=e := by
    exact (hlist e (by simpa only [List.length_range] using he)).trans (List.getElem_range _)
  rw [hread,abs_lt,← hn.2,← hx.2,← hm.2]
  simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<2^P)]
  norm_cast
  tauto

end MinCostFlow.IPM.Machine
