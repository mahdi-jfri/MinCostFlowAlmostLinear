module

public import MinCostFlow.IPM.Machine.NamedGraphLayout
public import MinCostFlow.IPM.Machine.NamedEdgeScan
public import MinCostFlow.IPM.Machine.GraphCoefficientRead

/-!
# Identifying serialized endpoint words with the named IPM graph

The endpoint scanner keeps edge indices in increasing order. The shared
circulation-record lookup proves that each scanned triple is exactly the
same named edge used by the mathematical IPM model. This binds the machine
serialization to its graph-level data-structure contract.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The endpoint scan's exact output is the named graph's indexed edge
list. Its source is the actual shared encoded instance. -/
theorem edgeTripleWords_namedInstance (I : Instance) (hI : I.IsValid)
    (mem : ℕ → ℕ) (a : ℕ) (hat : ListAt mem a (zeroLowerWords I)) :
    edgeTripleWords mem (a+2) I.m =
      (List.range I.m).flatMap (fun e => [e,(namedInstance I).tail e,(namedInstance I).head e]) := by
  unfold edgeTripleWords
  apply List.flatMap_congr
  intro i hi
  have hm : i < I.m := List.mem_range.mp hi
  have hh := zeroLower_endpoints_at I hI mem a hat ⟨i,hm⟩
  simp only [namedInstance,hm,↓reduceDIte]
  rw [show a+2+1+5*i=a+3+5*i by omega]
  exact congrArg₂ (fun t u => [i,t,u]) hh.1 hh.2

end MinCostFlow.IPM.Machine
