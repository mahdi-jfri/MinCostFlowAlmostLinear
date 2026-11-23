module

public import MinCostFlow.IPM.Machine.GuardedRefreshSourceFrame

/-!
# Reusing numeric sources after replacing a stored flow coordinate

Coordinate recovery writes the flow block before the slack checks. The
remaining scalar sources occupy disjoint blocks. Their values and all
arithmetic margins survive, while acceptance supplies validity of the new
flow block. The source conditions contain no slack-range conclusion, so
this preservation does not bypass the following machine guard.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem same_block {mem mem' : ℕ → ℕ} {p f L sourceEnd : ℕ}
    (hframe : ∀ z<sourceEnd,(z<f ∨ f+L≤z) → mem' z=mem z)
    (hend : p+L≤sourceEnd) (hdis : p+L≤f ∨ f+L≤p) :
    ∀ i<L,mem' (p+i)=mem (p+i) := by
  intro i hi
  apply hframe _ (by omega)
  rcases hdis with hh | hh <;> omega

/-- Replacing just the stored flow block preserves the raw scalar numeric
conditions when all other inputs are disjoint and the new block is valid. -/
theorem scalarCoefficientSourceConditions_after_flow_write
    {w h q K m c r lo f up a one mn mx L P E sourceEnd next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E sourceEnd mem)
    (hframe : ∀ z<sourceEnd,(z<f ∨ f+L≤z) → mem' z=mem z)
    (hadvance : sourceEnd≤next) (hmn : mn+L≤sourceEnd) (hmx : mx+L≤sourceEnd)
    (hseparate : ∀ p∈[c,r,lo,up,a,one,mn,mx],p+L≤f ∨ f+L≤p)
    (hflow : Num.Valid mem' f h L) :
    scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E next mem' := by
  obtain ⟨hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,
    hvc,hvr,hvl,_,hvu,hva,hvo,hone,hrl,hrh,ha0,ha1,hmin,hmax⟩ := hs
  have hcSame := same_block hframe hc (hseparate c (by simp))
  have hrSame := same_block hframe hr (hseparate r (by simp))
  have hloSame := same_block hframe hlo (hseparate lo (by simp))
  have hupSame := same_block hframe hup (hseparate up (by simp))
  have haSame := same_block hframe ha (hseparate a (by simp))
  have hoSame := same_block hframe ho (hseparate one (by simp))
  have hmnSame := same_block hframe hmn (hseparate mn (by simp))
  have hmxSame := same_block hframe hmx (hseparate mx (by simp))
  have valid_of_same (p : ℕ) (hv : Num.Valid mem p h L)
      (hh : ∀ i<L,mem' (p+i)=mem (p+i)) : Num.Valid mem' p h L := by
    intro i hi
    rw [hh i hi]
    exact hv i hi
  have fix_of_same (p : ℕ) (hh : ∀ i<L,mem' (p+i)=mem (p+i)) :
      Num.fixVal mem' p h L P=Num.fixVal mem p h L P := by
    unfold Num.fixVal
    rw [Num.intVal_congr hh]
  refine ⟨hP,hprec,hwidth,hPw,hmw,hmB,?_,
    hc.trans hadvance,hr.trans hadvance,hlo.trans hadvance,hf.trans hadvance,
    hup.trans hadvance,ha.trans hadvance,ho.trans hadvance,
    valid_of_same c hvc hcSame,valid_of_same r hvr hrSame,valid_of_same lo hvl hloSame,
    hflow,valid_of_same up hvu hupSame,valid_of_same a hva haSame,
    valid_of_same one hvo hoSame,(Num.intVal_congr hoSame).trans hone,?_,?_,?_,?_,?_,?_⟩
  · rw [Num.intVal_congr hcSame]; exact hcB
  · rw [fix_of_same r hrSame]; exact hrl
  · rw [fix_of_same r hrSame]; exact hrh
  · rw [fix_of_same a haSame]; exact ha0
  · rw [fix_of_same a haSame]; exact ha1
  · exact ⟨valid_of_same mn hmin.1 hmnSame,(fix_of_same mn hmnSame).trans hmin.2⟩
  · exact ⟨valid_of_same mx hmax.1 hmxSame,(fix_of_same mx hmxSame).trans hmax.2⟩

/-- An accepted capacity interval gives the absolute upper bounds needed
for exact slack subtraction. It does not assert the minimum slack that
the next machine guard checks. -/
theorem slack_subtraction_bounds_of_inside {lower flow upper bound : ℝ}
    (hlo : lower<flow) (hup : flow<upper) (hwidth : upper-lower≤bound) :
    |upper-flow|≤bound ∧ |flow-lower|≤bound := by
  rw [abs_of_nonneg (by linarith only [hup]),abs_of_nonneg (by linarith only [hlo])]
  constructor <;> linarith only [hlo,hup,hwidth]

end MinCostFlow.IPM.Machine
