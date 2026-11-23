module

public import MinCostFlow.IPM.Machine.GuardedCoefficientRefresh
import WordRAM.Memory

/-!
# Reusing stored coefficient inputs across reported-edge refreshes

The cost, flow, capacities, alpha, residual and guard constants live before
the coefficient tables. Each refresh preserves that source prefix even
when it writes a table entry. The input arithmetic conditions and the
upper bounds needed for exact slack subtraction therefore survive for
the next reported edge, at its advanced scratch heap.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The numeric source conditions depend only on their represented blocks.
They survive table writes outside that prefix and an advancing heap. -/
theorem scalarCoefficientSourceConditions_frozen
    {w h q K m c r lo f up a one mn mx L P E sourceEnd next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E sourceEnd mem)
    (hframe : ∀ z<sourceEnd,mem' z=mem z) (hadvance : sourceEnd≤next)
    (hmn : mn+L≤sourceEnd) (hmx : mx+L≤sourceEnd) :
    scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E next mem' := by
  obtain ⟨hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,
    hvc,hvr,hvl,hvf,hvu,hva,hvo,hone,hrl,hrh,ha0,ha1,hmin,hmax⟩ := hs
  have hcval := Num.IPM.value_frozen (h:=h) hframe hc
  have hoval := Num.IPM.value_frozen (h:=h) hframe ho
  have hrval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hr
  have haval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe ha
  refine ⟨hP,hprec,hwidth,hPw,hmw,hmB,?_,
    hc.trans hadvance,hr.trans hadvance,hlo.trans hadvance,hf.trans hadvance,
    hup.trans hadvance,ha.trans hadvance,ho.trans hadvance,
    Num.IPM.valid_frozen hframe hc hvc,Num.IPM.valid_frozen hframe hr hvr,
    Num.IPM.valid_frozen hframe hlo hvl,Num.IPM.valid_frozen hframe hf hvf,
    Num.IPM.valid_frozen hframe hup hvu,Num.IPM.valid_frozen hframe ha hva,
    Num.IPM.valid_frozen hframe ho hvo,hoval.trans hone,?_,?_,?_,?_,?_,?_⟩
  · rw [hcval]; exact hcB
  · rw [hrval]; exact hrl
  · rw [hrval]; exact hrh
  · rw [haval]; exact ha0
  · rw [haval]; exact ha1
  · exact ⟨Num.IPM.valid_frozen hframe hmn hmin.1,(Num.IPM.fixVal_frozen hframe hmn).trans hmin.2⟩
  · exact ⟨Num.IPM.valid_frozen hframe hmx hmax.1,(Num.IPM.fixVal_frozen hframe hmx).trans hmax.2⟩

/-- Upper bounds suffice to subtract slacks exactly before their strict
range check. They do not assert the positive lower bounds being tested.
Thus the loop can construct each real call's full precondition from raw
stored-source conditions and available scratch space. -/
theorem guardedCoefficient_pre_of_source_conditions
    {w h q K m c r lo f up a one mn mx L P E ld gd heap : ℕ} {mem : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E heap mem)
    (hmn : mn+L≤heap) (hmx : mx+L≤heap)
    (hul : |Num.fixVal mem up h L P-Num.fixVal mem f h L P|≤(2:ℝ)^E)
    (hdl : |Num.fixVal mem f h L P-Num.fixVal mem lo h L P|≤(2:ℝ)^E)
    (hld : ld+L≤heap) (hgd : gd+L≤heap) (hdis : ld+L≤gd ∨ gd+L≤ld)
    (hz : ZeroFrom mem heap)
    (hspace : heap+(4*L+1)+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1<2^w) :
    (guardedCoefficientRefreshContract w h q K).pre
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem := by
  have hsCopy := hs
  obtain ⟨_,_,hwidth,_,_,_,_,_,_,hlo,hf,hup,_,_,_,_,hvl,hvf,hvu,_,_,_,_,_,_,_,hmin,hmax⟩ := hs
  have hslack : (Num.IPM.slacksContract w h).pre [lo,f,up,L,P,heap] mem := by
    exact ⟨⟨lo,f,up,L,P,E,heap,rfl,by omega,hlo,hf,hup,hvl,hvf,hvu,hul,hdl⟩,hz,
      by change heap+4*L<2^w; omega⟩
  have hguard : (guardedSlacksContract w h).pre [lo,f,up,mn,mx,L,P,heap] mem := by
    exact ⟨⟨lo,f,up,mn,mx,L,P,heap,rfl,hslack,hmn,hmx,hmin.1,hmax.1⟩,hz,
      by change heap+(4*L+1)<2^w; omega⟩
  exact ⟨⟨m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap,rfl,hsCopy,hguard,hld,hgd,hdis⟩,hspace⟩

end MinCostFlow.IPM.Machine
