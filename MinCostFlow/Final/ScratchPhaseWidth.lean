module

public import MinCostFlow.Final.ScratchResidualOptimization
import MinCostFlow.Scaling.FeasibilityPhaseFacts
import MinCostFlow.Scaling.ResidualOptimizationWordSize
import MinCostFlow.Scaling.ResidualWordBounds
import WordRAM.Entry
import WordRAM.LinkDefs
import Mathlib.Tactic.Ring

/-!
# Source widths for the two outer scaling phases

The source encoding controls all numerical premises of feasibility and
residual optimization. Its widened word multiplier also covers the
nested pruned cost-scaling call, so each phase can run in a fresh region.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- One phase region uses the original multiplier times the guest-width factor. -/
def scratchPhaseMultiplier (c d : ℕ) : ℕ := 16384*scratchWidthFactor c d

theorem scratchPhaseMultiplier_pos (c d : ℕ) : 1 ≤ scratchPhaseMultiplier c d :=
  Nat.mul_pos (by decide) (scratchWidthFactor_pos c d)

/-- Dimensions and cost at most `b`, and capacity budget at most `b^4`,
give a uniform `b^(11008*scratchWidthFactor c d)` reserve for the complete pruned scaling program. -/
theorem scratchPrunedScalingSpace_le_pow (c d : ℕ) (J : Circulation) (C U b : ℕ) (hb6 : 6≤b)
    (hn : J.n≤b) (hm : J.m≤b) (hC : C≤b) (hU : U≤b^4) :
    scratchPrunedScalingSpace c d J C U≤b^(11008*scratchWidthFactor c d) := by
  have hfactor := scratchWidthFactor_pos c d
  let V := max U (2*J.m+1)
  let D := costStepNumberBase J C V
  let fuel := costRounds J.n C
  have hbpos : 0<b := by omega
  have hb2 : 36≤b^2 := Nat.pow_le_pow_left hb6 2
  have h14b : 14*b≤b^3 :=
    (Nat.mul_le_mul_right b (show 14≤b^2 by omega)).trans_eq (pow_succ b 2).symm
  have h2_4 : b^2≤b^4 := Nat.pow_le_pow_right hbpos (by omega)
  have hb_4 : b≤b^4 := Nat.le_pow (by decide)
  have h3b : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
  have hV : V≤b^4 := max_le hU (by omega)
  have hdouble : J.m+J.m≤b^2 := by
    have hh : 2*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 2≤b by omega)
    omega
  have hten : (J.m+J.m)^10≤b^20 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hdouble 10
  have hlinear : J.n+4*J.m+C+8≤14*b := by omega
  have hlinear' : J.n+4*J.m+C+V+8≤b^5 := by
    have h3_4 : b^3≤b^4 := Nat.pow_le_pow_right hbpos (by omega)
    have h4_5 : 2*b^4≤b^5 :=
      (Nat.mul_le_mul_right (b^4) (show 2≤b by omega)).trans_eq (pow_succ' b 4).symm
    omega
  have h5_20 : b^5≤b^20 := Nat.pow_le_pow_right hbpos (by omega)
  have hD : D≤b^21 := by
    have hh : 2*b^20≤b^21 :=
      (Nat.mul_le_mul_right (b^20) (show 2≤b by omega)).trans_eq (pow_succ' b 20).symm
    change J.n+4*J.m+(J.m+J.m)^10+C+V+8≤b^21
    omega
  have hN : D^(524*scratchWidthFactor c d)≤b^(11004*scratchWidthFactor c d) := by
    rw [show 11004*scratchWidthFactor c d = 21*(524*scratchWidthFactor c d) by omega, pow_mul b 21]
    exact Nat.pow_le_pow_left hD _
  have hCLog : Nat.clog 2 (C+1)≤C+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hnLog : Nat.clog 2 (J.n+1)≤J.n+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuel : fuel+2≤b^2 := by
    have hh : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
    change 1+Nat.clog 2 (C+1)+Nat.clog 2 (J.n+1)+2≤b^2
    omega
  have hcells : (fuel+2)*D^(524*scratchWidthFactor c d)≤b^(11006*scratchWidthFactor c d) := by
    have hh := Nat.mul_le_mul hfuel hN
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right hbpos (by omega))
  have hlinS : J.solverWords.length+J.n+2+J.m+2*J.n+3+J.m+3≤14*b := by
    rw [J.solverWords_length]
    omega
  have h3_11006 : b^3≤b^(11006*scratchWidthFactor c d) := Nat.pow_le_pow_right hbpos (by omega)
  have hS : scratchCostScalingSpace c d J C V≤b^(11007*scratchWidthFactor c d) := by
    have hh : 2*b^(11006*scratchWidthFactor c d)≤b^(11007*scratchWidthFactor c d) :=
      (Nat.mul_le_mul_right (b^(11006*scratchWidthFactor c d)) (show 2≤b by omega)).trans ((pow_succ' b (11006*scratchWidthFactor c d)).symm.le.trans
          (Nat.pow_le_pow_right hbpos (by omega)))
    change J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*D^(524*scratchWidthFactor c d)+J.m+3≤b^(11007*scratchWidthFactor c d)
    omega
  have hprune : scratchPrunedScalingSpace c d J C U≤b^(11008*scratchWidthFactor c d) := by
    have hs := scratchPrunedScalingSpace_le c d J C U
    change scratchPrunedScalingSpace c d J C U≤2+10*J.m+scratchCostScalingSpace c d J C V at hs
    have hlin : 2+10*J.m≤14*b := by omega
    have h3 : b^3≤b^(11007*scratchWidthFactor c d) := Nat.pow_le_pow_right hbpos (by omega)
    have hh : 2*b^(11007*scratchWidthFactor c d)≤b^(11008*scratchWidthFactor c d) :=
      (Nat.mul_le_mul_right (b^(11007*scratchWidthFactor c d)) (show 2≤b by omega)).trans ((pow_succ' b (11007*scratchWidthFactor c d)).symm.le.trans
          (Nat.pow_le_pow_right hbpos (by omega)))
    omega
  exact hprune

/-- Multiplier 16384 on the original instance plus supplied bounds
satisfies all full feasibility-phase entry premises jointly. -/
theorem scratchFeasibilityPhase_pre_wordSize (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hC : 1≤C)
    (horder : ∀ e∈I.edges,e.lower≤e.upper)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e∈I.edges,e.lower.natAbs≤U) (hu : ∀ e∈I.edges,e.upper.natAbs≤U) :
    let input := I.encode++[C,U]
    (∀ x∈[0,C,U,input.length],x<2^wordSize (scratchPhaseMultiplier c d) input) ∧
      (scratchFeasibilityPhaseContract (wordSize (scratchPhaseMultiplier c d) input) solver entry T S c d hproc I hv C U).pre
        [0,C,U,input.length] (initMem input) := by
  have hfactor := scratchWidthFactor_pos c d
  have hphase : scratchPhaseMultiplier c d = 16384*scratchWidthFactor c d := rfl
  let input := I.encode++[C,U]
  let M := input.foldr max 0
  let b := input.length+M+2
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  let V := max B (2*P.m+1)
  let D := costStepNumberBase P C V
  let fuel := costRounds P.n C
  let w := wordSize (scratchPhaseMultiplier c d) input
  change (∀ x∈[0,C,U,input.length],x<2^w) ∧
    (scratchFeasibilityPhaseContract w solver entry T S c d hproc I hv C U).pre [0,C,U,input.length] (initMem input)
  have hlen : input.length=4+8*I.m+2*I.n := by
    simp only [input,List.length_append,instance_encode_length I hv,List.length_cons,List.length_nil]
    omega
  have hb6 : 6≤b := by omega
  have hbpos : 0<b := by omega
  have hCmax : C≤M := Link.elem_le_foldr_max (List.mem_append_right _ List.mem_cons_self)
  have hUmax : U≤M := Link.elem_le_foldr_max
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hm : I.m≤b := by omega
  have hn : I.n≤b := by omega
  have hPm : P.m≤b := by change I.m+(I.n+I.n)≤b; omega
  have hPn : P.n≤b := by change I.n+1≤b; omega
  have hb2 : 36≤b^2 := Nat.pow_le_pow_left hb6 2
  have hb3 : 216≤b^3 := Nat.pow_le_pow_left hb6 3
  have h14b : 14*b≤b^3 :=
    (Nat.mul_le_mul_right b (show 14≤b^2 by omega)).trans_eq (pow_succ b 2).symm
  have h40b : 40*b≤b^4 :=
    (Nat.mul_le_mul_right b (show 40≤b^3 by omega)).trans_eq (pow_succ b 3).symm
  have h2_4 : b^2≤b^4 := Nat.pow_le_pow_right hbpos (by omega)
  have hb_4 : b≤b^4 := Nat.le_pow (by decide)
  have hbudgetFactor : 2*(I.m+1)≤b^2 := by
    have hh : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
    omega
  have hbudgetProduct : 2*(I.m+1)*U≤b^3 := by
    simpa only [←pow_succ] using Nat.mul_le_mul hbudgetFactor (show U≤b by omega)
  have hB : B≤b^4 := by
    have hh : 2*b^3≤b^4 :=
      (Nat.mul_le_mul_right (b^3) (show 2≤b by omega)).trans_eq (pow_succ' b 3).symm
    have hp : 1≤b^3 := Nat.one_le_pow _ _ hbpos
    change 2*(I.m+1)*U+1≤b^4
    omega
  have hV : V≤b^4 := max_le hB (by omega)
  have hdouble : P.m+P.m≤b^2 := by
    have hh : 2*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 2≤b by omega)
    omega
  have hten : (P.m+P.m)^10≤b^20 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hdouble 10
  have hlinear : P.n+4*P.m+C+8≤14*b := by omega
  have hlinear' : P.n+4*P.m+C+V+8≤b^5 := by
    have h3_4 : b^3≤b^4 := Nat.pow_le_pow_right hbpos (by omega)
    have h4_5 : 2*b^4≤b^5 :=
      (Nat.mul_le_mul_right (b^4) (show 2≤b by omega)).trans_eq (pow_succ' b 4).symm
    omega
  have h5_20 : b^5≤b^20 := Nat.pow_le_pow_right hbpos (by omega)
  have hD : D≤b^21 := by
    have hh : 2*b^20≤b^21 :=
      (Nat.mul_le_mul_right (b^20) (show 2≤b by omega)).trans_eq (pow_succ' b 20).symm
    change P.n+4*P.m+(P.m+P.m)^10+C+V+8≤b^21
    omega
  have hN : D^(524*scratchWidthFactor c d)≤b^(11004*scratchWidthFactor c d) := by
    rw [show 11004*scratchWidthFactor c d = 21*(524*scratchWidthFactor c d) by omega, pow_mul b 21]
    exact Nat.pow_le_pow_left hD _
  have hCLog : Nat.clog 2 (C+1)≤C+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hnLog : Nat.clog 2 (P.n+1)≤P.n+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuel : fuel+2≤b^2 := by
    have hh : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
    change 1+Nat.clog 2 (C+1)+Nat.clog 2 (P.n+1)+2≤b^2
    omega
  have hcells : (fuel+2)*D^(524*scratchWidthFactor c d)≤b^(11006*scratchWidthFactor c d) := by
    have hh := Nat.mul_le_mul hfuel hN
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right hbpos (by omega))
  have hlinS : P.solverWords.length+P.n+2+P.m+2*P.n+3+P.m+3≤14*b := by
    rw [P.solverWords_length]
    omega
  have h3_11006 : b^3≤b^(11006*scratchWidthFactor c d) := Nat.pow_le_pow_right hbpos (by omega)
  have hS : scratchCostScalingSpace c d P C V≤b^(11007*scratchWidthFactor c d) := by
    have hh : 2*b^(11006*scratchWidthFactor c d)≤b^(11007*scratchWidthFactor c d) :=
      (Nat.mul_le_mul_right (b^(11006*scratchWidthFactor c d)) (show 2≤b by omega)).trans ((pow_succ' b (11006*scratchWidthFactor c d)).symm.le.trans
          (Nat.pow_le_pow_right hbpos (by omega)))
    change P.solverWords.length+P.n+2+P.m+2*P.n+3+(fuel+2)*D^(524*scratchWidthFactor c d)+P.m+3≤b^(11007*scratchWidthFactor c d)
    omega
  have hprune : scratchPrunedScalingSpace c d P C B≤b^(11008*scratchWidthFactor c d) := by
    have hs := scratchPrunedScalingSpace_le c d P C B
    change scratchPrunedScalingSpace c d P C B≤2+10*P.m+scratchCostScalingSpace c d P C V at hs
    have hlin : 2+10*P.m≤14*b := by omega
    have h3 : b^3≤b^(11007*scratchWidthFactor c d) := Nat.pow_le_pow_right hbpos (by omega)
    have hh : 2*b^(11007*scratchWidthFactor c d)≤b^(11008*scratchWidthFactor c d) :=
      (Nat.mul_le_mul_right (b^(11007*scratchWidthFactor c d)) (show 2≤b by omega)).trans ((pow_succ' b (11007*scratchWidthFactor c d)).symm.le.trans
          (Nat.pow_le_pow_right hbpos (by omega)))
    omega
  have hlinOuter : input.length+4+16*I.m+12*I.n+P.m+4*P.m+2+3≤40*b := by omega
  have h4 : b^4≤b^(11008*scratchWidthFactor c d) := Nat.pow_le_pow_right hbpos (by omega)
  have hspace : input.length+scratchFeasibilityPhaseSpace c d I hv C U≤b^(scratchPhaseMultiplier c d) := by
    have hh : 2*b^(11008*scratchWidthFactor c d)≤b^(11009*scratchWidthFactor c d) :=
      (Nat.mul_le_mul_right (b^(11008*scratchWidthFactor c d)) (show 2≤b by omega)).trans ((pow_succ' b (11008*scratchWidthFactor c d)).symm.le.trans
          (Nat.pow_le_pow_right hbpos (by omega)))
    have hx : b^(11009*scratchWidthFactor c d)≤b^(scratchPhaseMultiplier c d) := Nat.pow_le_pow_right hbpos (by omega)
    change input.length+(4+16*I.m+12*I.n+scratchPrunedScalingSpace c d P C B+P.m+4*P.m+2+3)≤b^(scratchPhaseMultiplier c d)
    omega
  have hp := pow_lt_two_pow_wordSize (by omega : 1≤scratchPhaseMultiplier c d) input
  change b^(scratchPhaseMultiplier c d)<2^w at hp
  have h4full : b^4≤b^(scratchPhaseMultiplier c d) := Nat.pow_le_pow_right hbpos (by omega)
  have h5full : b^5≤b^(scratchPhaseMultiplier c d) := Nat.pow_le_pow_right hbpos (by omega)
  have h5 : I.n*B≤b^5 :=
    (Nat.mul_le_mul hn hB).trans_eq (pow_succ' b 4).symm
  have hP5 : P.m*B≤b^5 :=
    (Nat.mul_le_mul hPm hB).trans_eq (pow_succ' b 4).symm
  have hgraph := (listAt_append.mp (listAt_initMem input)).1
  have hcap := FlowReduction.buildFeasibilityInstance_capacity_le I hv U hd
    (fun e => hl _ (List.getElem_mem e.isLt)) (fun e => hu _ (List.getElem_mem e.isLt))
  have hPwords : ∀ x∈P.solverWords,x≤b^4 := by
    intro x hx
    simp only [Circulation.solverWords,List.mem_cons,List.mem_flatMap,List.mem_finRange] at hx
    rcases hx with rfl | rfl | ⟨e,_,hx⟩
    · omega
    · omega
    · simp only [Circulation.solverEdgeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
      have ht := (P.tail e).isLt
      have hh := (P.head e).isLt
      have hc := (hcap e).trans hB
      have hcost := buildFeasibility_costs_le_one I hv e
      change (P.cost e).natAbs≤1 at hcost
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals (try split) <;> omega
  refine ⟨?_,0,input.length,rfl,hgraph,?_,horder,hd,hl,hu,?_,?_,hC,by omega,?_,?_,?_,?_,zeroFrom_initMem _,hspace.trans_lt hp⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · simp only [input,List.length_append,List.length_cons,List.length_nil]; omega
  · intro x hx
    exact lt_two_pow_wordSize_of_mem (by have h := scratchPhaseMultiplier_pos c d; omega) (List.mem_append_left _ hx)
  · intro x hx
    exact ((hPwords x hx).trans h4full).trans_lt hp
  · have he : (2*I.m+2)*U=2*(I.m+1)*U := by ring
    rw [he]
    exact ((hbudgetProduct.trans (Nat.pow_le_pow_right hbpos (by omega : 3≤scratchPhaseMultiplier c d)))).trans_lt hp
  · exact (hB.trans h4full).trans_lt hp
  · exact (h5.trans h5full).trans_lt hp
  · exact (hP5.trans h5full).trans_lt hp

/-- Every edgewise bounded starting flow has simultaneous residual-phase
premises at multiplier 16384 on the original instance plus supplied bounds.
The source memory contains the original instance, shifted graph, and flow. -/
theorem scratchResidualOptimization_pre_wordSize (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    let source := I.encode++[C,U]
    ∃ mem heap,
      (∀ x∈[0,I.encode.length,I.encode.length+(FlowReduction.shiftedGraph I hv).solverWords.length,C,U,heap],
        x<2^wordSize (scratchPhaseMultiplier c d) source) ∧
      (scratchResidualOptimizationContract (wordSize (scratchPhaseMultiplier c d) source) solver entry T S c d hproc I hv f C U).pre
        [0,I.encode.length,I.encode.length+(FlowReduction.shiftedGraph I hv).solverWords.length,C,U,heap] mem := by
  have hwidth := scratchWidthFactor_pos c d
  have hphase : scratchPhaseMultiplier c d = 16384*scratchWidthFactor c d := rfl
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
  let w := wordSize (scratchPhaseMultiplier c d) source
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
  have hbfour : b≤b^(scratchPhaseMultiplier c d) := Nat.le_pow (by omega)
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
  have hprune := scratchPrunedScalingSpace_le_pow c d R C B b hb6 hRn hRm (show C≤b by omega) hB
  have hheap : heap=I.encode.length+J.solverWords.length+I.m := by
    simp only [heap,input,List.length_append,flow,List.length_ofFn]; omega
  have hlin : heap+2+15*I.m≤18*b := by
    rw [J.solverWords_length] at hheap
    change heap=I.encode.length+(2+5*I.m)+I.m at hheap
    have hi := instance_encode_length I hv
    omega
  have hspace : heap+scratchResidualOptimizationSpace c d I hv f C U≤b^(scratchPhaseMultiplier c d) := by
    have h3 : b^3≤b^(11008*scratchWidthFactor c d) := Nat.pow_le_pow_right hbpos (by omega)
    have hlinear := hlin.trans (h18b.trans h3)
    have hh : 2*b^(11008*scratchWidthFactor c d)≤b^(11009*scratchWidthFactor c d) :=
      (Nat.mul_le_mul_right (b^(11008*scratchWidthFactor c d)) (show 2≤b by omega)).trans ((pow_succ' b (11008*scratchWidthFactor c d)).symm.le.trans
          (Nat.pow_le_pow_right hbpos (by omega)))
    have hx : b^(11009*scratchWidthFactor c d)≤b^(scratchPhaseMultiplier c d) := Nat.pow_le_pow_right hbpos (by omega)
    change heap+(2+15*I.m+scratchPrunedScalingSpace c d R C B)≤b^(scratchPhaseMultiplier c d)
    omega
  have hp := pow_lt_two_pow_wordSize (by omega : 1≤scratchPhaseMultiplier c d) source
  change b^(scratchPhaseMultiplier c d)<2^w at hp
  have hspaceWord := hspace.trans_lt hp
  have h2full : b^2≤b^(scratchPhaseMultiplier c d) := Nat.pow_le_pow_right hbpos (by omega)
  have h4full : b^4≤b^(scratchPhaseMultiplier c d) := Nat.pow_le_pow_right hbpos (by omega)
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
    (scratchResidualOptimizationContract w solver entry T S c d hproc I hv f C U).pre
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
    exact lt_two_pow_wordSize_of_mem (by have h := scratchPhaseMultiplier_pos c d; omega) (List.mem_append_left _ hx)

/-- The first phase's complete reserve is bounded by its fixed source
width's address space, independently of its source placement. -/
theorem scratchFeasibilityPhaseSpace_le_source_capacity (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hC : 1≤C)
    (horder : ∀ e∈I.edges,e.lower≤e.upper)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e∈I.edges,e.lower.natAbs≤U) (hu : ∀ e∈I.edges,e.upper.natAbs≤U) :
    scratchFeasibilityPhaseSpace c d I hv C U≤2^wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U]) := by
  obtain ⟨_,hpre⟩ := scratchFeasibilityPhase_pre_wordSize solver entry T S c d hproc I hv C U hC horder hd hl hu
  obtain ⟨a,heap,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hs⟩ := hpre
  change heap+scratchFeasibilityPhaseSpace c d I hv C U<2^wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U]) at hs
  omega

/-- Every bounded starting flow has the same fixed source-width upper
bound on the complete residual optimization reserve. -/
theorem scratchResidualOptimizationSpace_le_source_capacity (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    scratchResidualOptimizationSpace c d I hv f C U≤2^wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U]) := by
  obtain ⟨_,_,_,hpre⟩ := scratchResidualOptimization_pre_wordSize solver entry T S c d hproc I hv f C U hf hC hl hu
  obtain ⟨a,graph,flow,heap,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hs⟩ := hpre
  change heap+scratchResidualOptimizationSpace c d I hv f C U<2^wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U]) at hs
  omega

/-- A fresh region covering one complete source-width address space
supplies all first-phase numeric conditions at any valid source placement. -/
theorem scratchFeasibilityPhase_pre_of_source_space {w : ℕ} (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (C U a heap : ℕ) (mem : ℕ → ℕ) (hC : 1≤C)
    (horder : ∀ e∈I.edges,e.lower≤e.upper)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e∈I.edges,e.lower.natAbs≤U) (hu : ∀ e∈I.edges,e.upper.natAbs≤U)
    (hat : ListAt mem a I.encode) (hend : a+I.encode.length≤heap) (hz : ZeroFrom mem heap)
    (hs : heap+2^wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U])<2^w) :
    (∀ x∈[a,C,U,heap],x<2^w) ∧
      (scratchFeasibilityPhaseContract w solver entry T S c d hproc I hv C U).pre [a,C,U,heap] mem := by
  let guest := wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U])
  change heap+2^guest<2^w at hs
  obtain ⟨hargs,hpre⟩ := scratchFeasibilityPhase_pre_wordSize solver entry T S c d hproc I hv C U hC horder hd hl hu
  obtain ⟨a0,heap0,_,_,_,_,_,_,_,hIwords,hPwords,_,h8,hbudget,hB,hMass,hObj,_,hspace⟩ := hpre
  have hguest : 2^guest<2^w := by omega
  have hS : scratchFeasibilityPhaseSpace c d I hv C U≤2^guest := by
    change heap0+scratchFeasibilityPhaseSpace c d I hv C U<2^guest at hspace
    omega
  refine ⟨?_,a,heap,rfl,hat,hend,horder,hd,hl,hu,
    (fun x hx => (hIwords x hx).trans hguest),(fun x hx => (hPwords x hx).trans hguest),hC,
    h8.trans hguest,hbudget.trans hguest,hB.trans hguest,hMass.trans hguest,hObj.trans hguest,hz,?_⟩
  · have hcw := (hargs C (by simp)).trans hguest
    have huw := (hargs U (by simp)).trans hguest
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · exact (Nat.add_le_add_left hS heap).trans_lt hs

/-- The same source-width region supplies every second-phase numeric
condition for any edgewise bounded starting flow and stored source arrays. -/
theorem scratchResidualOptimization_pre_of_source_space {w : ℕ} (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U a graph flow heap : ℕ) (mem : ℕ → ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U)
    (hat : ListAt mem a I.encode) (hgraph : ListAt mem graph (FlowReduction.shiftedGraph I hv).solverWords)
    (hflow : ListAt mem flow (List.ofFn (fun e => (f e).toNat)))
    (hend : a+I.encode.length≤heap) (hgraphEnd : graph+(FlowReduction.shiftedGraph I hv).solverWords.length≤heap)
    (hflowEnd : flow+I.m≤heap) (hz : ZeroFrom mem heap)
    (hs : heap+2^wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U])<2^w) :
    (∀ x∈[a,graph,flow,C,U,heap],x<2^w) ∧
      (scratchResidualOptimizationContract w solver entry T S c d hproc I hv f C U).pre
        [a,graph,flow,C,U,heap] mem := by
  let guest := wordSize (scratchPhaseMultiplier c d) (I.encode++[C,U])
  change heap+2^guest<2^w at hs
  obtain ⟨mem0,heap0,hargs,hpre⟩ := scratchResidualOptimization_pre_wordSize solver entry T S c d hproc I hv f C U hf hC hl hu
  obtain ⟨a0,graph0,flow0,h0,_,_,_,_,_,_,_,_,_,_,_,hIwords,hJwords,hRwords,h8,hB,h4U,_,hspace⟩ := hpre
  have hguest : 2^guest<2^w := by omega
  have hS : scratchResidualOptimizationSpace c d I hv f C U≤2^guest := by
    change h0+scratchResidualOptimizationSpace c d I hv f C U<2^guest at hspace
    omega
  refine ⟨?_,a,graph,flow,heap,rfl,hat,hgraph,hflow,hend,hgraphEnd,hflowEnd,hf,hC,hl,hu,
    (fun x hx => (hIwords x hx).trans hguest),(fun x hx => (hJwords x hx).trans hguest),
    (fun x hx => (hRwords x hx).trans hguest),h8.trans hguest,hB.trans hguest,h4U.trans hguest,hz,?_⟩
  · have hcw := (hargs C (by simp)).trans hguest
    have huw := (hargs U (by simp)).trans hguest
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact (Nat.add_le_add_left hS heap).trans_lt hs

end MinCostFlow.Final
