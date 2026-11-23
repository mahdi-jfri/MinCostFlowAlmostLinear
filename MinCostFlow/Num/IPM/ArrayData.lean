module

public import MinCostFlow.Num.IPM.FixedPointFacts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Input ranges for arrays of IPM edge data

Each array uses consecutive blocks of `L` limbs. The scalar edge data
below contains only validity, exact decoding of one, slack ranges, and the
alpha interval. These are the input conditions of the per-edge procedures.
Framing lemmas let array scans reuse those conditions after each call.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM

/-- Numeric input conditions for one edge of Definition 4.2 (page 24). -/
def EdgeData (mem : ℕ→ℕ) (lo f up a one h L P E : ℕ) : Prop :=
  Valid mem lo h L ∧ Valid mem f h L ∧ Valid mem up h L ∧ Valid mem a h L ∧ Valid mem one h L ∧
  intVal mem one h L=(2:ℤ)^P ∧
  1/(2:ℝ)^E≤fixVal mem up h L P-fixVal mem f h L P ∧
  fixVal mem up h L P-fixVal mem f h L P≤(2:ℝ)^E ∧
  1/(2:ℝ)^E≤fixVal mem f h L P-fixVal mem lo h L P ∧
  fixVal mem f h L P-fixVal mem lo h L P≤(2:ℝ)^E ∧
  0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1

/-- Exact edge length read from arrays of capacities and flows. -/
noncomputable def arrayLength (mem : ℕ→ℕ) (lo f up a h L P i : ℕ) : ℝ :=
  Real.rpow (fixVal mem (up+i*L) h L P-fixVal mem (f+i*L) h L P) (-1-fixVal mem a h L P)+
  Real.rpow (fixVal mem (f+i*L) h L P-fixVal mem (lo+i*L) h L P) (-1-fixVal mem a h L P)

/-- Exact edge gradient read from the arrays and shared residual. -/
noncomputable def arrayGradient (mem : ℕ→ℕ) (m c r lo f up a h L P i : ℕ) : ℝ :=
  20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem (c+i*L) h L:ℝ)+
  fixVal mem a h L P*(Real.rpow (fixVal mem (up+i*L) h L P-fixVal mem (f+i*L) h L P) (-1-fixVal mem a h L P)-
    Real.rpow (fixVal mem (f+i*L) h L P-fixVal mem (lo+i*L) h L P) (-1-fixVal mem a h L P))

/-- An edge's numeric input conditions are unchanged below a preserved prefix. -/
theorem edgeData_frozen {mem mem' : ℕ→ℕ} {lo f up a one h L P E heap : ℕ}
    (hframe : ∀z<heap,mem' z=mem z) (hlo : lo+L≤heap) (hf : f+L≤heap)
    (hup : up+L≤heap) (ha : a+L≤heap) (ho : one+L≤heap)
    (hd : EdgeData mem lo f up a one h L P E) : EdgeData mem' lo f up a one h L P E := by
  rcases hd with ⟨hvl,hvf,hvu,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩
  refine ⟨valid_frozen hframe hlo hvl,valid_frozen hframe hf hvf,valid_frozen hframe hup hvu,
    valid_frozen hframe ha hva,valid_frozen hframe ho hvo,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [value_frozen (h:=h) hframe ho]; exact hone
  all_goals simp only [fixVal_frozen (P:=P) hframe hlo,fixVal_frozen (P:=P) hframe hf,
    fixVal_frozen (P:=P) hframe hup,fixVal_frozen (P:=P) hframe ha]
  all_goals assumption

/-- Preserving the four source blocks preserves the exact length. -/
theorem arrayLength_frozen {mem mem' : ℕ→ℕ} {lo f up a h L P i heap : ℕ}
    (hframe : ∀z<heap,mem' z=mem z) (hlo : lo+i*L+L≤heap) (hf : f+i*L+L≤heap)
    (hup : up+i*L+L≤heap) (ha : a+L≤heap) :
    arrayLength mem' lo f up a h L P i=arrayLength mem lo f up a h L P i := by
  simp only [arrayLength,fixVal_frozen (P:=P) hframe hlo,fixVal_frozen (P:=P) hframe hf,
    fixVal_frozen (P:=P) hframe hup,fixVal_frozen (P:=P) hframe ha]

/-- Moving array pointers by one block advances the exact length index. -/
theorem arrayLength_shift (mem : ℕ→ℕ) (lo f up a h L P i : ℕ) :
    arrayLength mem (lo+L) (f+L) (up+L) a h L P i=arrayLength mem lo f up a h L P (i+1) := by
  have hl : lo+L+i*L=lo+(i+1)*L := by ring
  have hf : f+L+i*L=f+(i+1)*L := by ring
  have hu : up+L+i*L=up+(i+1)*L := by ring
  simp only [arrayLength,hl,hf,hu]

/-- Prefix preservation also preserves the exact gradient formula. -/
theorem arrayGradient_frozen {mem mem' : ℕ→ℕ} {m c r lo f up a h L P i heap : ℕ}
    (hframe : ∀z<heap,mem' z=mem z) (hc : c+i*L+L≤heap) (hr : r+L≤heap)
    (hlo : lo+i*L+L≤heap) (hf : f+i*L+L≤heap) (hup : up+i*L+L≤heap) (ha : a+L≤heap) :
    arrayGradient mem' m c r lo f up a h L P i=arrayGradient mem m c r lo f up a h L P i := by
  simp only [arrayGradient,value_frozen (h:=h) hframe hc,fixVal_frozen (P:=P) hframe hr,
    fixVal_frozen (P:=P) hframe hlo,fixVal_frozen (P:=P) hframe hf,
    fixVal_frozen (P:=P) hframe hup,fixVal_frozen (P:=P) hframe ha]

/-- Moving all edge-array pointers advances the exact gradient index. -/
theorem arrayGradient_shift (mem : ℕ→ℕ) (m c r lo f up a h L P i : ℕ) :
    arrayGradient mem m (c+L) r (lo+L) (f+L) (up+L) a h L P i=
      arrayGradient mem m c r lo f up a h L P (i+1) := by
  have hc : c+L+i*L=c+(i+1)*L := by ring
  have hl : lo+L+i*L=lo+(i+1)*L := by ring
  have hf : f+L+i*L=f+(i+1)*L := by ring
  have hu : up+L+i*L=up+(i+1)*L := by ring
  simp only [arrayGradient,hc,hl,hf,hu]

end MinCostFlow.Num.IPM
