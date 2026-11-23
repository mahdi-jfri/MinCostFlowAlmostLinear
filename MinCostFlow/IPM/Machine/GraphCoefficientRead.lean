module

public import MinCostFlow.IPM.Machine.InitialLayoutRead
public import MinCostFlow.IPM.Machine.FixedIntegerVector
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Memory

/-!
# Reading numeric coefficients from the fixed graph

The target test uses the existing five-word circulation encoding.
Its sign/magnitude pair is at edge offsets three and four; upper
capacity is at offset two. These lookup lemmas connect the dense
integer-table loader to the actual graph, keeping the original edge
indices and signed cost convention.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The two endpoint words preserve the original graph indices. -/
theorem zeroLower_endpoints_at (I : Instance) (hI : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (zeroLowerWords I)) (e : Fin I.m) :
    mem (a+2+5*e.val)=(I.edge e).tail ∧ mem (a+3+5*e.val)=(I.edge e).head := by
  rw [← zeroLowerCirculation_words I hI] at hat
  have hh := ((Scaling.Machine.solverWords_at_iff (zeroLowerCirculation I hI) mem a).mp hat).2.2
  have ht := hh e ⟨0,by decide⟩
  have hu := hh e ⟨1,by decide⟩
  change mem (a+(2+5*e.val+0))=(I.edge e).tail at ht
  change mem (a+(2+5*e.val+1))=(I.edge e).head at hu
  exact ⟨by simpa only [Nat.add_zero,← Nat.add_assoc] using ht,
    by simpa only [show a+(2+5*e.val+1)=a+3+5*e.val by omega] using hu⟩

/-- The two cost words are exactly the shared canonical integer encoding. -/
theorem zeroLower_cost_at (I : Instance) (hI : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (zeroLowerWords I)) (e : Fin I.m) :
    [mem (a+5+5*e.val),mem (a+6+5*e.val)]=encodeInt (I.edge e).cost := by
  rw [← zeroLowerCirculation_words I hI] at hat
  have hh := ((Scaling.Machine.solverWords_at_iff (zeroLowerCirculation I hI) mem a).mp hat).2.2
  have hsign := hh e ⟨3,by decide⟩
  have hmag := hh e ⟨4,by decide⟩
  change mem (a+(2+5*e.val+3))=(if (I.edge e).cost < 0 then 1 else 0) at hsign
  change mem (a+(2+5*e.val+4))=(I.edge e).cost.natAbs at hmag
  have hsign' : mem (a+5+5*e.val)=(if (I.edge e).cost < 0 then 1 else 0) := by
    simpa only [show a+(2+5*e.val+3)=a+5+5*e.val by omega] using hsign
  have hmag' : mem (a+6+5*e.val)=(I.edge e).cost.natAbs := by
    simpa only [show a+(2+5*e.val+4)=a+6+5*e.val by omega] using hmag
  rw [hsign',hmag']
  rfl

/-- Signed stride-five decoding is the actual source edge cost. -/
theorem zeroLower_strided_cost (I : Instance) (hI : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (zeroLowerWords I)) (e : Fin I.m) :
    stridedInteger true mem (a+5) e.val=(I.edge e).cost := by
  have hh := zeroLower_cost_at I hI mem a hat e
  have hd := congrArg (fun xs : List ℕ => Num.decodeIntWords (xs.getD 0 0) (xs.getD 1 0)) hh
  simpa only [stridedInteger,↓reduceIte,show a+5+1+5*e.val=a+6+5*e.val by omega,
    List.getD_cons_zero,List.getD_cons_succ,encodeInt,Num.decodeIntWords_encodeInt] using hd

/-- Unsigned stride-five decoding is lossless on the graph's upper capacity. -/
theorem zeroLower_strided_capacity (I : Instance) (hI : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ZeroLowerAt mem a I) (e : Fin I.m) :
    stridedInteger false mem (a+3) e.val=(I.edge e).upper := by
  have hh := zeroLower_capacity_at I hI mem a hat.2.2 e
  unfold stridedInteger
  simp only [Bool.false_eq_true,↓reduceIte,show a+3+1+5*e.val=a+4+5*e.val by omega,
    hh,Num.decodeIntWords]
  exact Int.toNat_of_nonneg (hat.1 e).2

end MinCostFlow.IPM.Machine
