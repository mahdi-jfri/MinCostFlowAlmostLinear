module

public import MinCostFlow.Num.IPM.Length
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Memory

/-!
# Moving the scalar length workspace

The caller reserves a block before scratch memory so computed outputs
cannot overlap its coefficient tables. Advancing the heap preserves the
length input premises when the old source prefix is unchanged.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Preserving the source prefix and providing fresh workspace at the new
heap preserves every premise of the scalar length call. -/
theorem length_pre_frozen {w h q lo f up a one L P E heap next : ℕ}
    {mem mem' : ℕ → ℕ}
    (hp : (Num.IPM.lengthContract w h q).pre [lo,f,up,a,one,L,P,E,heap] mem)
    (hframe : ∀ x<heap,mem' x=mem x) (hadvance : heap≤next)
    (hz : ZeroFrom mem' next)
    (hspace : next+Num.IPM.lengthSpace L P E<2^w) :
    (Num.IPM.lengthContract w h q).pre [lo,f,up,a,one,L,P,E,next] mem' := by
  obtain ⟨⟨lo',f',up',a',one',L',P',E',heap',heq,hP,hprec,hwidth,hPw,
    hlo,hf,hup,ha,ho,hvl,hvf,hvu,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩,_,_⟩ := hp
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hloval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hlo
  have hfval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hf
  have hupval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe hup
  have haval := Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe ha
  refine ⟨⟨lo,f,up,a,one,L,P,E,next,rfl,hP,hprec,hwidth,hPw,
    hlo.trans hadvance,hf.trans hadvance,hup.trans hadvance,
    ha.trans hadvance,ho.trans hadvance,
    Num.IPM.valid_frozen hframe hlo hvl,Num.IPM.valid_frozen hframe hf hvf,
    Num.IPM.valid_frozen hframe hup hvu,Num.IPM.valid_frozen hframe ha hva,
    Num.IPM.valid_frozen hframe ho hvo,
    (Num.IPM.value_frozen (h:=h) hframe ho).trans hone,?_,?_,?_,?_,?_,?_⟩,hz,hspace⟩
  · rw [hupval,hfval]; exact hul
  · rw [hupval,hfval]; exact huh
  · rw [hfval,hloval]; exact hdl
  · rw [hfval,hloval]; exact hdh
  · rw [haval]; exact ha0
  · rw [haval]; exact ha1

end MinCostFlow.IPM.Machine
