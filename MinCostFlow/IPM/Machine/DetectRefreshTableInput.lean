module

public import MinCostFlow.IPM.Machine.DetectRefreshOutput
public import MinCostFlow.IPM.Machine.DetectRefreshUnreported

/-!
# Dense coefficient-table inputs immediately after refresh

Success gives valid new blocks for every reported edge. Unreported
blocks retain their exact words, so their old validity and vector
values survive. This supplies the checked driver's inputs before its
range scan runs. No range assertion about a newly reported value is
needed in this transfer.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Successful actual refresh preserves full dense-table validity and
leaves unreported vector coordinates exactly unchanged. -/
theorem detectRefresh_table_input {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hvalid : ∀ e<m,Num.Valid mem (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (ld+e*F.limbs) F.fmt.limbBits F.limbs) :
    (∀ e<m,Num.Valid mem' (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem' (ld+e*F.limbs) F.fmt.limbBits F.limbs) ∧
    ∀ e<m,e∉(A.detect s).1 →
      readVector mem' gd F.fmt.limbBits F.limbs F.fmt.precision m e=
        readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision m e ∧
      readVector mem' ld F.fmt.limbBits F.limbs F.fmt.precision m e=
        readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision m e := by
  have hd := detectRefresh_output F A G m κ α rate allocation R hpre hout
  have hs (e : ℕ) (he : e<m) (hne : e∉(A.detect s).1) :=
    detectRefresh_unreported_coefficients F A G m κ α rate allocation R hpre hout he hne
  constructor
  · intro e he
    by_cases hin : e∈(A.detect s).1
    · have hc := hd.2.2.2.2 haccept e hin
      exact ⟨hc.2.2.2.2.1,hc.2.2.1⟩
    · have hf := hs e he hin
      constructor
      · intro i hi
        rw [hf gd (by simp) i hi]
        exact (hvalid e he).1 i hi
      · intro i hi
        rw [hf ld (by simp) i hi]
        exact (hvalid e he).2 i hi
  · intro e he hne
    have hf := hs e he hne
    simp only [readVector,he,↓reduceIte]
    constructor
    · unfold Num.fixVal
      rw [Num.intVal_congr (hf gd (by simp))]
    · unfold Num.fixVal
      rw [Num.intVal_congr (hf ld (by simp))]

end MinCostFlow.IPM.Machine
