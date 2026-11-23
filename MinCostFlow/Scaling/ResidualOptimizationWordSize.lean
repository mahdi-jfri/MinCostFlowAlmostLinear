module

public import MinCostFlow.Scaling.ResidualOptimizationContract
import MinCostFlow.Scaling.ScalingSpacePolynomial
import MinCostFlow.Scaling.ResidualWordBounds
import WordRAM.Entry
import WordRAM.LinkDefs
import Mathlib.Tactic.Ring

/-!
# Fixed source width for residual optimization

The original instance with its supplied bounds determines the width,
independently of the chosen bounded starting flow. The shifted and residual
graph words fit from the original cost and capacity bounds. The static
capacity budget is bounded by source-base power four, and the uniform
nested-space theorem gives power 11008 for the pruned solve. Multiplier
16384 therefore covers all sources, arithmetic budgets, and phase space.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 32768 in
set_option maxRecDepth 65536 in
/-- Every edgewise bounded starting flow has simultaneous residual-phase
premises at multiplier 16384 on the original instance plus supplied bounds.
The source memory contains the original instance, shifted graph, and flow. -/
theorem residualOptimization_pre_wordSize (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    let source := I.encode++[C,U]
    ∃ mem heap,
      (∀ x∈[0,I.encode.length,I.encode.length+(FlowReduction.shiftedGraph I hv).solverWords.length,C,U,heap],
        x<2^wordSize 16384 source) ∧
      (residualOptimizationContract (wordSize 16384 source) solver entry T hproc I hv f C U).pre
        [0,I.encode.length,I.encode.length+(FlowReduction.shiftedGraph I hv).solverWords.length,C,U,heap] mem := by
  let source := I.encode++[C,U]
  let M := source.foldr max 0
  let b := source.length+M+2
  let J := FlowReduction.shiftedGraph I hv
  let R := J.residual f
  let B := FlowReduction.scalingCapacityBudget I U
  let flow := List.ofFn (fun e => (f e).toNat)
  let input := I.encode++(J.solverWords++flow)
  let mem := initMem input
  let heap := input.length
  let w := wordSize 16384 source
  have hlen : source.length=4+8*I.m+2*I.n := by
    simp only [source,List.length_append,instance_encode_length I hv,List.length_cons,List.length_nil]
    omega
  have hb6 : 6≤b := by omega
  have hbpos : 0<b := by omega
  have hCmax : C≤M := Link.elem_le_foldr_max (List.mem_append_right _ List.mem_cons_self)
  have hUmax : U≤M := Link.elem_le_foldr_max
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hm : I.m≤b := by omega
  have hn : I.n≤b := by omega
  have hRm : R.m≤b := by change I.m+I.m≤b; omega
  have hRn : R.n≤b := hn
  have hbfour : b≤b^16384 := Nat.le_pow (by decide)
  have hb2 : 36≤b^2 := Nat.pow_le_pow_left hb6 2
  have h4b : 4*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 4≤b by omega)
  have h18b : 18*b≤b^3 :=
    (Nat.mul_le_mul_right b (show 18≤b^2 by omega)).trans_eq (pow_succ b 2).symm
  have hfactor : 2*(I.m+1)≤b^2 := by omega
  have hproduct : 2*(I.m+1)*U≤b^3 := by
    simpa only [←pow_succ] using Nat.mul_le_mul hfactor (show U≤b by omega)
  have hB : B≤b^4 := by
    have hp : 1≤b^3 := Nat.one_le_pow _ _ hbpos
    have hh : 2*b^3≤b^4 :=
      (Nat.mul_le_mul_right (b^3) (show 2≤b by omega)).trans_eq (pow_succ' b 3).symm
    change 2*(I.m+1)*U+1≤b^4
    omega
  have hprune := prunedScalingSpace_le_pow R C B b hb6 hRn hRm (show C≤b by omega) hB
  have hheap : heap=I.encode.length+J.solverWords.length+I.m := by
    simp only [heap,input,List.length_append,flow,List.length_ofFn]; omega
  have hlin : heap+2+15*I.m≤18*b := by
    rw [J.solverWords_length] at hheap
    change heap=I.encode.length+(2+5*I.m)+I.m at hheap
    have hi := instance_encode_length I hv
    omega
  have hspace : heap+residualOptimizationSpace I hv f C U≤b^16384 := by
    have h3 : b^3≤b^11008 := Nat.pow_le_pow_right hbpos (by decide)
    have hh : 2*b^11008≤b^11009 :=
      (Nat.mul_le_mul_right (b^11008) (show 2≤b by omega)).trans_eq (pow_succ' b 11008).symm
    have hx : b^11009≤b^16384 := Nat.pow_le_pow_right hbpos (by decide)
    change heap+(2+15*I.m+prunedScalingSpace R C B)≤b^16384
    omega
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤16384) source
  change b^16384<2^w at hp
  have hspaceWord := hspace.trans_lt hp
  have h2full : b^2≤b^16384 := Nat.pow_le_pow_right hbpos (by decide)
  have h4full : b^4≤b^16384 := Nat.pow_le_pow_right hbpos (by decide)
  have hJcap := FlowReduction.shiftedGraph_capacity_le I hv U hl hu
  have hJwords : ∀ x∈J.solverWords,x<2^w := by
    apply solverWords_fit_of_bounds J w (hn.trans_lt (hbfour.trans_lt hp))
      (hm.trans_lt (hbfour.trans_lt hp)) (by omega)
    · intro e
      exact (hJcap e).trans_lt (show 2*U<2^w by omega)
    · intro e
      exact (hC e).trans_lt (show C<2^w by omega)
  have hRwords := residual_words_fit J f w hf hJwords
    (hRm.trans_lt (hbfour.trans_lt hp)) (by omega)
  have hat := listAt_append.mp (listAt_initMem input)
  have hrest := listAt_append.mp hat.2
  change ∃ mem heap,(∀ x∈[0,I.encode.length,I.encode.length+J.solverWords.length,C,U,heap],x<2^w) ∧
    (residualOptimizationContract w solver entry T hproc I hv f C U).pre
      [0,I.encode.length,I.encode.length+J.solverWords.length,C,U,heap] mem
  refine ⟨mem,heap,?_,0,I.encode.length,I.encode.length+J.solverWords.length,heap,rfl,
    hat.1,?_,?_,by omega,(by change I.encode.length+J.solverWords.length≤heap; omega),by omega,hf,hC,hl,hu,?_,hJwords,hRwords,
    by omega,(hB.trans h4full).trans_lt hp,by omega,zeroFrom_initMem _,hspaceWord⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · simpa only [Nat.zero_add] using hrest.1
  · simpa only [Nat.zero_add] using hrest.2
  · intro x hx
    exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)

end MinCostFlow.Scaling.Machine
