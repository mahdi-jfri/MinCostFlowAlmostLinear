module

public import MinCostFlow.IPM.Machine.EpochStart
import MinCostFlow.IPM.Machine.VectorFrame

/-!
# The initialized epoch's stored coefficient arrays

Initialization writes above the numerical workspace. Its prefix frame
therefore preserves both refreshed arrays. The abstract state is
initialized from exactly the arrays decoded from the final memory,
with their coordinatewise numerical error guarantees intact.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the actual epoch-start output: refreshed valid arrays, exact
initialization at their stored values, and a fitting concrete DS state. -/
theorem epochStart_output {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem v mem') :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
    let handle := heap+(la+ga)
    (∀ i<I.m,Num.Valid mem' (heap+i*F.limbs) F.fmt.limbBits F.limbs ∧
      ScalarApprox (1+1/(2:ℝ)^q)
        (Num.fixVal mem' (heap+i*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
        (Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i)) ∧
    (∀ i<I.m,Num.Valid mem' (heap+la+i*F.limbs) F.fmt.limbBits F.limbs ∧
      |Num.fixVal mem' (heap+la+i*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
        Num.IPM.arrayGradient mem I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i|≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i) ∧
    ∃ x,R.rep handle (A.init (namedInstance I)
      (readVector mem' (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) x mem' ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision
        (A.init (namedInstance I)
          (readVector mem' (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) ∧
      (∀ z,R.foot handle x z → handle≤z) ∧ handle≤v ∧
      v≤handle+allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,handle] ∧ ZeroFrom mem' v := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  let handle := heap+(la+ga)
  obtain ⟨coefficients,hcoeff,hinit⟩ := hout
  change (coefficientRefreshContract w F.fmt.limbBits q K).post
    [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap] mem handle coefficients at hcoeff
  change (minRatioInitContract w R
    (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation)).post
    [graph,heap+la,heap,F.limbs,F.fmt.precision,handle] coefficients v mem' at hinit
  obtain ⟨hlo,hhi,hframe,hzero,s,x,hrep,hmodel,hfoot⟩ := hinit
  change ∀ z<handle,mem' z=coefficients z at hframe
  change s=A.init (namedInstance I)
    (readVector coefficients (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector coefficients heap F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧ _ at hmodel
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hlEnd : heap+I.m*F.limbs≤handle := by dsimp only [handle]; omega
  have hgEnd : heap+la+I.m*F.limbs≤handle := by dsimp only [handle]; omega
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
  have hstate : s=A.init (namedInstance I)
      (readVector mem' (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
    rw [hgSame,hlSame]
    exact hmodel.1
  have hlength := hcoeff.1.2.2.2.2.1
  have hgradient := hcoeff.1.2.2.2.2.2
  refine ⟨?_,?_,x,hstate ▸ hrep,hstate ▸ hmodel.2,hfoot,hlo,hhi,hzero⟩
  · intro i hi
    have hend : heap+i*F.limbs+F.limbs≤handle := by
      have hh := Nat.mul_le_mul_right F.limbs (Nat.succ_le_of_lt hi)
      simp only [Nat.succ_mul] at hh
      omega
    exact ⟨Num.IPM.valid_frozen hframe hend (hlength i hi).1,
      by rw [Num.IPM.fixVal_frozen hframe hend]; exact (hlength i hi).2⟩
  · intro i hi
    have hend : heap+la+i*F.limbs+F.limbs≤handle := by
      have hh := Nat.mul_le_mul_right F.limbs (Nat.succ_le_of_lt hi)
      simp only [Nat.succ_mul] at hh
      omega
    exact ⟨Num.IPM.valid_frozen hframe hend (hgradient i hi).1,
      by rw [Num.IPM.fixVal_frozen hframe hend]; exact (hgradient i hi).2⟩

/-- Initializing the epoch's numerical tables and data structure preserves
every earlier source word, including the explicit base and cached flow. -/
theorem epochStart_frame {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem v mem') :
    ∀ z<heap,mem' z=mem z := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  obtain ⟨coefficients,hcoeff,hinit⟩ := hout
  have hcf := hcoeff.1.2.2.1
  change ∀ z<heap,coefficients z=mem z at hcf
  have hif := hinit.2.2.1
  change ∀ z<heap+(la+ga),mem' z=coefficients z at hif
  intro z hz
  exact (hif z (by omega)).trans (hcf z hz)

end MinCostFlow.IPM.Machine
