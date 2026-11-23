module

public import MinCostFlow.Scaling.CostStateLayout
import WordRAM.Entry

/-!
# Concrete source memory for integer cost states

Store a circulation, its unsigned flow, its signed potentials, and the
three-word state header consecutively. A nonnegative integral flow has
exactly the shared unsigned representation. The memory after the header
is zero, so the state can be passed to an allocating cost-round procedure.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every nonnegative integral cost state has a concrete representation
with its original graph and a fresh zero tail after the state header. -/
theorem exists_costState_memory {J : Circulation} (s : CostState J) (hf : ∀ e,0≤s.flow e) :
    ∃ mem state heap,ListAt mem 0 J.solverWords ∧ J.solverWords.length≤heap ∧
      state+3=heap ∧ CostStateAt mem state heap s ∧ ZeroFrom mem heap := by
  let flowWords := List.ofFn (fun e => (s.flow e).toNat)
  let potWords := (List.ofFn s.potential).flatMap encodeInt
  let flow := J.solverWords.length
  let pot := flow+J.m
  let state := pot+2*J.n
  let heap := state+3
  let input := J.solverWords++(flowWords++(potWords++[flow,pot,s.power]))
  let mem := initMem input
  have hflowLen : flowWords.length=J.m := List.length_ofFn
  have hpotLen : potWords.length=2*J.n := by rw [integers_encode_length,List.length_ofFn]
  have hstored := listAt_append.mp (listAt_initMem input)
  have hafterGraph : ListAt mem flow (flowWords++(potWords++[flow,pot,s.power])) := by
    simpa only [Nat.zero_add] using hstored.2
  obtain ⟨hflow,hafterFlow⟩ := listAt_append.mp hafterGraph
  have hafterFlow' : ListAt mem pot (potWords++[flow,pot,s.power]) := by
    simpa only [hflowLen] using hafterFlow
  obtain ⟨hpot,hheader⟩ := listAt_append.mp hafterFlow'
  have hheader' : ListAt mem state [flow,pot,s.power] := by
    simpa only [hpotLen] using hheader
  have hinputLen : input.length=heap := by
    simp only [input,List.length_append,hflowLen,hpotLen,List.length_cons,List.length_nil]
    dsimp only [heap,state,pot,flow]
    omega
  refine ⟨mem,state,heap,hstored.1,by dsimp only [heap,state,pot,flow]; omega,rfl,?_,?_⟩
  · exact costStateAt_of_arrays hheader' (by dsimp only [heap,state,pot]; omega)
      (by dsimp only [heap,state]; omega) hflow hf (signedTableAt_of_listAt s.potential _ _ hpot)
  · simpa only [hinputLen] using zeroFrom_initMem input

end MinCostFlow.Scaling.Machine
