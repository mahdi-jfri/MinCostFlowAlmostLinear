module

public import MinCostFlow.Num.IPM.GradientArray
import WordRAM.Memory

/-!
# Preserving gradient inputs across a length refresh

The length procedure preserves every source cell below its incoming
heap. The following gradient procedure reads those same cells from the
new memory. Its numerical premises therefore stay true when the heap
advances, provided its own workspace fits at that new heap.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Freezing the old input prefix preserves the entire numerical
gradient precondition, with fresh space at an advanced heap. -/
theorem gradientArray_pre_frozen {w h q K m cp rp lo fp up ap one L P E heap next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hp : (Num.IPM.gradientArrayContract w h q K).pre
      [m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem)
    (hframe : ∀ x < heap,mem' x=mem x) (hadvance : heap ≤ next)
    (hz : ZeroFrom mem' next)
    (hspace : next+Num.IPM.gradientArraySpace m L P E < 2^w) :
    (Num.IPM.gradientArrayContract w h q K).pre
      [m,cp,rp,lo,fp,up,ap,one,L,P,E,next] mem' := by
  obtain ⟨⟨m',cp',rp',lo',fp',up',ap',one',L',P',E',heap',heq,
    hP,hprec,hwidth,hPw,hmw,hmB,hc,hr,hlo,hf,hup,ha,ho,hvr,hrl,hrh,hdata⟩,_,_⟩ := hp
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  refine ⟨⟨m,cp,rp,lo,fp,up,ap,one,L,P,E,next,rfl,hP,hprec,hwidth,hPw,hmw,hmB,
    hc.trans hadvance,hr.trans hadvance,hlo.trans hadvance,hf.trans hadvance,
    hup.trans hadvance,ha.trans hadvance,ho.trans hadvance,
    Num.IPM.valid_frozen hframe hr hvr,?_,?_,?_⟩,hz,hspace⟩
  · rw [Num.IPM.fixVal_frozen hframe hr]
    exact hrl
  · rw [Num.IPM.fixVal_frozen hframe hr]
    exact hrh
  · intro i hi
    have hblock : i*L+L ≤ m*L := by
      have hh := Nat.mul_le_mul_right L (show i+1 ≤ m by omega)
      simpa only [Nat.add_mul,one_mul] using hh
    have hcend : cp+i*L+L ≤ heap := by omega
    have hloend : lo+i*L+L ≤ heap := by omega
    have hfend : fp+i*L+L ≤ heap := by omega
    have hupend : up+i*L+L ≤ heap := by omega
    have hd := hdata i hi
    refine ⟨Num.IPM.edgeData_frozen hframe hloend hfend hupend ha ho hd.1,
      Num.IPM.valid_frozen hframe hcend hd.2.1,?_⟩
    rw [Num.IPM.value_frozen (h:=h) hframe hcend]
    exact hd.2.2

end MinCostFlow.IPM.Machine
