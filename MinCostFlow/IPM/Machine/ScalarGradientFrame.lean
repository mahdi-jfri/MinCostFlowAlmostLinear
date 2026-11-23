module

public import MinCostFlow.Num.IPM.Gradient
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Memory

/-!
# Preserving scalar gradient inputs

After computing a reported edge's length, the scalar gradient procedure
reads the same stored edge data and held residual. Preserving the old
memory prefix preserves its numerical premises at the advanced heap.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A length calculation can precede a scalar gradient calculation without
changing its input conditions, provided the remaining workspace fits. -/
theorem gradient_pre_frozen {w h q K m c r lo f up a one L P E heap next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hp : (Num.IPM.gradientContract w h q K).pre
      [m,c,r,lo,f,up,a,one,L,P,E,heap] mem)
    (hframe : ∀ x < heap, mem' x = mem x) (hadvance : heap ≤ next)
    (hz : ZeroFrom mem' next)
    (hspace : next + Num.IPM.gradientSpace L P E < 2^w) :
    (Num.IPM.gradientContract w h q K).pre
      [m,c,r,lo,f,up,a,one,L,P,E,next] mem' := by
  obtain ⟨⟨m',c',r',lo',f',up',a',one',L',P',E',heap',heq,
    hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,
    hvc,hvr,hvlo,hvf,hvup,hva,hvo,hone,hrl,hrh,hul,huh,hdl,hdh,ha0,ha1⟩,_,_⟩ := hp
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hcval := Num.IPM.value_frozen (h:=h) hframe hc
  have hoval := Num.IPM.value_frozen (h:=h) hframe ho
  have hrval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hr
  have hloval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hlo
  have hfval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hf
  have hupval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hup
  have haval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe ha
  refine ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,next,rfl,hP,hprec,hwidth,hPw,hmw,hmB,?_,
    hc.trans hadvance,hr.trans hadvance,hlo.trans hadvance,hf.trans hadvance,
    hup.trans hadvance,ha.trans hadvance,ho.trans hadvance,
    Num.IPM.valid_frozen hframe hc hvc,Num.IPM.valid_frozen hframe hr hvr,
    Num.IPM.valid_frozen hframe hlo hvlo,Num.IPM.valid_frozen hframe hf hvf,
    Num.IPM.valid_frozen hframe hup hvup,Num.IPM.valid_frozen hframe ha hva,
    Num.IPM.valid_frozen hframe ho hvo,hoval.trans hone,?_,?_,?_,?_,?_,?_,?_,?_⟩,
    hz,hspace⟩
  · rw [hcval]; exact hcB
  · rw [hrval]; exact hrl
  · rw [hrval]; exact hrh
  · rw [hupval,hfval]; exact hul
  · rw [hupval,hfval]; exact huh
  · rw [hfval,hloval]; exact hdl
  · rw [hfval,hloval]; exact hdh
  · rw [haval]; exact ha0
  · rw [haval]; exact ha1

end MinCostFlow.IPM.Machine
