module

public import MinCostFlow.IPM.Machine.CoefficientRangeList
public import MinCostFlow.IPM.Machine.CoefficientRangeOutput
import Mathlib.Tactic.Positivity

/-!
# Bounds certified for every reported coefficient

The read-only scan's final bit certifies its entire actual Detect list.
Use the report's set equality to find each reported edge in that list,
then decode that entry's signed comparisons at the common fixed-point
scale. This supplies the real bounds required by the next Update.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- An accepted complete report scan certifies the real coefficient
bounds for every member, independently of its position in the list. -/
theorem coefficientRangeList_accepted {w h report g l neg mx mn L P v : ℕ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ} {maximum minimum : ℝ}
    (hreport : DetectAt mem report S)
    (hout : (coefficientRangeListContract w h).post [report+1,S.card,g,l,neg,mx,mn,L] mem v mem')
    (hn : ScalarAt mem neg h L P (-maximum))
    (hx : ScalarAt mem mx h L P maximum) (hm : ScalarAt mem mn h L P minimum)
    (hvalid : ∀ e∈S,Num.Valid mem (g+e*L) h L ∧ Num.Valid mem (l+e*L) h L)
    (haccept : v=1) (hmin : 0<minimum) :
    ∀ e∈S,|Num.fixVal mem (g+e*L) h L P|≤maximum ∧
      minimum≤Num.fixVal mem (l+e*L) h L P ∧
      Num.fixVal mem (l+e*L) h L P≤maximum ∧ 0<Num.fixVal mem (l+e*L) h L P := by
  obtain ⟨es,hnd,hset,_,hnames⟩ := hreport
  have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  intro e he
  have heList : e∈es := List.mem_toFinset.mp (by rw [hset]; exact he)
  obtain ⟨i,hi,hiEq⟩ := List.mem_iff_getElem.mp heList
  have hread : mem (report+1+i)=e := (hnames i hi).trans hiEq
  have hcheck := hout.2.2.mp haccept i (by change i<S.card; omega)
  change coefficientsInRange mem h neg (g+mem (report+1+i)*L) mx mn (l+mem (report+1+i)*L) L at hcheck
  rw [hread] at hcheck
  have hsingle : (coefficientRangeGuardContract w h).post [neg,g+e*L,mx,mn,l+e*L,L] mem 1 mem := by
    change mem=mem ∧ 1=if coefficientsInRange mem h neg (g+e*L) mx mn (l+e*L) L then 1 else 0
    exact ⟨rfl,(ite_eq_left hcheck).symm⟩
  exact coefficientRangeGuard_accepted hsingle hn ⟨(hvalid e he).1,rfl⟩ hx hm
    ⟨(hvalid e he).2,rfl⟩ rfl hmin

/-- A report scan accepts whenever its represented coefficients lie
strictly inside the exact represented endpoints. This is the reverse
direction used with the potential-derived coefficient margin. -/
theorem coefficientRangeList_accepts {w h report g l neg mx mn L P v : ℕ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ} {maximum minimum : ℝ}
    (hreport : DetectAt mem report S)
    (hout : (coefficientRangeListContract w h).post [report+1,S.card,g,l,neg,mx,mn,L] mem v mem')
    (hn : ScalarAt mem neg h L P (-maximum))
    (hx : ScalarAt mem mx h L P maximum) (hm : ScalarAt mem mn h L P minimum)
    (hstrict : ∀ e∈S,|Num.fixVal mem (g+e*L) h L P|<maximum ∧
      minimum<Num.fixVal mem (l+e*L) h L P ∧ Num.fixVal mem (l+e*L) h L P<maximum) : v=1 := by
  apply hout.2.2.mpr
  obtain ⟨es,hnd,hset,_,hnames⟩ := hreport
  have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  intro i hi
  change i<S.card at hi
  have hiList : i<es.length := by omega
  have he : es[i]∈S := by rw [← hset]; exact List.mem_toFinset.mpr (List.getElem_mem hiList)
  have hread := hnames i hiList
  change coefficientsInRange mem h neg (g+mem (report+1+i)*L) mx mn (l+mem (report+1+i)*L) L
  rw [hread]
  have hgood := hstrict _ he
  rw [abs_lt,← hn.2,← hx.2,← hm.2] at hgood
  simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<2^P)] at hgood
  norm_cast at hgood
  exact ⟨hgood.1.1,hgood.1.2,hgood.2.1,hgood.2.2⟩

end MinCostFlow.IPM.Machine
