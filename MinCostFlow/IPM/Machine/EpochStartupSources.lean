module

public import MinCostFlow.IPM.Machine.EpochCoefficientPre
public import MinCostFlow.IPM.Machine.GuardedRefreshInput
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Scalar refresh inputs from the complete epoch's numerical arrays

The initial gradient pass already checks the common arithmetic and
each source block. Keeping the same scalar formats and guard words
makes these facts the source conditions of every subsequent local
coefficient refresh.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Recover the numerical source conditions for an individual edge
directly from the original gradient-array input. -/
theorem scalarCoefficientSourceConditions_of_gradientArray
    {w h q K m c r lo f up a one mn mx L P E heap : ℕ} {mem : ℕ → ℕ}
    (hgrad : (Num.IPM.gradientArrayContract w h q K).pre [m,c,r,lo,f,up,a,one,L,P,E,heap] mem)
    (hmin : ScalarAt mem mn h L P (1/(2:ℝ)^E))
    (hmax : ScalarAt mem mx h L P ((2:ℝ)^E)) (e : ℕ) (he : e<m) :
    scalarCoefficientSourceConditions w h q K m (c+e*L) r (lo+e*L) (f+e*L) (up+e*L)
      a one mn mx L P E heap mem := by
  obtain ⟨⟨m',c',r',lo',f',up',a',one',L',P',E',heap',heq,hP,hprec,hwidth,hPw,hmw,hmB,
    hca,hra,hla,hfa,hua,haa,hoa,hvr,hrlo,hrhi,hdata⟩,_,_⟩ := hgrad
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨⟨hl,hf,hu,ha,ho,hone,_,_,_,_,ha0,ha1⟩,hc,hBound⟩ := hdata e he
  have hend (p : ℕ) (hp : p+m*L≤heap) : p+e*L+L≤heap :=
    (reported_entry_end p L e m he).trans hp
  exact ⟨hP,hprec,hwidth,hPw,hmw,hmB,hBound,hend c hca,hra,hend lo hla,hend f hfa,hend up hua,
    haa,hoa,hc,hvr,hl,hf,hu,ha,ho,hone,hrlo,hrhi,ha0,ha1,hmin,hmax⟩

/-- The startup coefficient wrapper carries the same gradient-array
precondition, so it establishes the full source family. -/
theorem scalarCoefficientSourceConditions_of_coefficientRefresh
    {w h q K m c r lo f up a one mn mx L P E heap : ℕ} {mem : ℕ → ℕ}
    (hpre : (coefficientRefreshContract w h q K).pre
      [m,c,r,lo,f,up,a,one,L,P,E,Num.IPM.lengthArraySpace m L P E,Num.IPM.gradientArraySpace m L P E,heap] mem)
    (hmin : ScalarAt mem mn h L P (1/(2:ℝ)^E))
    (hmax : ScalarAt mem mx h L P ((2:ℝ)^E)) (e : ℕ) (he : e<m) :
    scalarCoefficientSourceConditions w h q K m (c+e*L) r (lo+e*L) (f+e*L) (up+e*L)
      a one mn mx L P E heap mem := by
  obtain ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,heq,_,_,_,hG⟩,_,_⟩ := hpre
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  exact scalarCoefficientSourceConditions_of_gradientArray hG hmin hmax e he

end MinCostFlow.IPM.Machine
