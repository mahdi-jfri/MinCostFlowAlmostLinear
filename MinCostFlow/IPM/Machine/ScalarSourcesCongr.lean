module

public import MinCostFlow.IPM.Machine.GuardedRefreshInput

/-!
# Preserving the numeric sources of a remaining reported edge

A successful refresh changes only its own three table entries and the DS
footprint. Other reported names have disjoint table entries. The numeric
preconditions for such an edge therefore survive whenever its nine source
blocks are unchanged. Prove this from block equality, without requiring
all intervening memory to stay fixed or assuming a minimum slack.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Equality on the nine scalar source blocks preserves every numeric
source condition. The allocation endpoint may advance independently. -/
theorem scalarCoefficientSourceConditions_congr
    {w h q K m c r lo f up a one mn mx L P E heap next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E heap mem)
    (hadvance : heap≤next)
    (hblocks : ∀ p∈[c,r,lo,f,up,a,one,mn,mx],∀ i<L,mem' (p+i)=mem (p+i)) :
    scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E next mem' := by
  obtain ⟨hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,
    hvc,hvr,hvl,hvf,hvu,hva,hvo,hone,hrl,hrh,ha0,ha1,hmin,hmax⟩ := hs
  have valid_of_same (p : ℕ) (hp : p∈[c,r,lo,f,up,a,one,mn,mx])
      (hv : Num.Valid mem p h L) : Num.Valid mem' p h L := by
    intro i hi
    rw [hblocks p hp i hi]
    exact hv i hi
  have int_of_same (p : ℕ) (hp : p∈[c,r,lo,f,up,a,one,mn,mx]) :
      Num.intVal mem' p h L=Num.intVal mem p h L :=
    Num.intVal_congr (hblocks p hp)
  have fix_of_same (p : ℕ) (hp : p∈[c,r,lo,f,up,a,one,mn,mx]) :
      Num.fixVal mem' p h L P=Num.fixVal mem p h L P := by
    unfold Num.fixVal
    rw [int_of_same p hp]
  refine ⟨hP,hprec,hwidth,hPw,hmw,hmB,?_,
    hc.trans hadvance,hr.trans hadvance,hlo.trans hadvance,hf.trans hadvance,
    hup.trans hadvance,ha.trans hadvance,ho.trans hadvance,
    valid_of_same c (by simp) hvc,valid_of_same r (by simp) hvr,
    valid_of_same lo (by simp) hvl,valid_of_same f (by simp) hvf,
    valid_of_same up (by simp) hvu,valid_of_same a (by simp) hva,
    valid_of_same one (by simp) hvo,(int_of_same one (by simp)).trans hone,?_,?_,?_,?_,?_,?_⟩
  · rw [int_of_same c (by simp)]; exact hcB
  · rw [fix_of_same r (by simp)]; exact hrl
  · rw [fix_of_same r (by simp)]; exact hrh
  · rw [fix_of_same a (by simp)]; exact ha0
  · rw [fix_of_same a (by simp)]; exact ha1
  · exact ⟨valid_of_same mn (by simp) hmin.1,(fix_of_same mn (by simp)).trans hmin.2⟩
  · exact ⟨valid_of_same mx (by simp) hmax.1,(fix_of_same mx (by simp)).trans hmax.2⟩

/-- Replacing only the stored flow requires valid new words, but no bound
on the old slack: the next program guard checks its candidate slacks.
Every other scalar source is preserved by its actual word frame. -/
theorem scalarCoefficientSourceConditions_replace_flow
    {w h q K m c r lo f up a one mn mx L P E heap next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E heap mem)
    (hadvance : heap≤next)
    (hflow : Num.Valid mem' f h L)
    (hblocks : ∀ p∈[c,r,lo,up,a,one,mn,mx],∀ i<L,mem' (p+i)=mem (p+i)) :
    scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E next mem' := by
  obtain ⟨hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,
    hvc,hvr,hvl,_,hvu,hva,hvo,hone,hrl,hrh,ha0,ha1,hmin,hmax⟩ := hs
  have valid_of_same (p : ℕ) (hp : p∈[c,r,lo,up,a,one,mn,mx])
      (hv : Num.Valid mem p h L) : Num.Valid mem' p h L := by
    intro i hi
    rw [hblocks p hp i hi]
    exact hv i hi
  have int_of_same (p : ℕ) (hp : p∈[c,r,lo,up,a,one,mn,mx]) :
      Num.intVal mem' p h L=Num.intVal mem p h L :=
    Num.intVal_congr (hblocks p hp)
  have fix_of_same (p : ℕ) (hp : p∈[c,r,lo,up,a,one,mn,mx]) :
      Num.fixVal mem' p h L P=Num.fixVal mem p h L P := by
    unfold Num.fixVal
    rw [int_of_same p hp]
  refine ⟨hP,hprec,hwidth,hPw,hmw,hmB,?_,
    hc.trans hadvance,hr.trans hadvance,hlo.trans hadvance,hf.trans hadvance,
    hup.trans hadvance,ha.trans hadvance,ho.trans hadvance,
    valid_of_same c (by simp) hvc,valid_of_same r (by simp) hvr,
    valid_of_same lo (by simp) hvl,hflow,
    valid_of_same up (by simp) hvu,valid_of_same a (by simp) hva,
    valid_of_same one (by simp) hvo,(int_of_same one (by simp)).trans hone,?_,?_,?_,?_,?_,?_⟩
  · rw [int_of_same c (by simp)]; exact hcB
  · rw [fix_of_same r (by simp)]; exact hrl
  · rw [fix_of_same r (by simp)]; exact hrh
  · rw [fix_of_same a (by simp)]; exact ha0
  · rw [fix_of_same a (by simp)]; exact ha1
  · exact ⟨valid_of_same mn (by simp) hmin.1,(fix_of_same mn (by simp)).trans hmin.2⟩
  · exact ⟨valid_of_same mx (by simp) hmax.1,(fix_of_same mx (by simp)).trans hmax.2⟩

end MinCostFlow.IPM.Machine
