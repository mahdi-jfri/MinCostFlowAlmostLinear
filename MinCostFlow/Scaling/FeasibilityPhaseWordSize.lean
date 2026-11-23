module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
import MinCostFlow.Scaling.FeasibilityPhaseFacts
import MinCostFlow.Scaling.PrunedScalingSpace
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# A fixed source width for the complete feasibility phase

Use the original instance encoding with its supplied cost and capacity
bounds. Its size base bounds the auxiliary capacity budget by power four
and the cost-round number base by power twenty-one. The complete nested
reserve then fits power 11009. Multiplier 16384 covers all arguments,
both source encodings, all scan budgets, and the complete first-solve phase.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 32768 in
set_option maxRecDepth 65536 in
/-- Multiplier 16384 on the original instance plus supplied bounds
satisfies all full feasibility-phase entry premises jointly. -/
theorem feasibilityPhase_pre_wordSize (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hC : 1≤C)
    (horder : ∀ e∈I.edges,e.lower≤e.upper)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e∈I.edges,e.lower.natAbs≤U) (hu : ∀ e∈I.edges,e.upper.natAbs≤U) :
    let input := I.encode++[C,U]
    (∀ x∈[0,C,U,input.length],x<2^wordSize 16384 input) ∧
      (feasibilityPhaseContract (wordSize 16384 input) solver entry T hproc I hv C U).pre
        [0,C,U,input.length] (initMem input) := by
  let input := I.encode++[C,U]
  let M := input.foldr max 0
  let b := input.length+M+2
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  let V := max B (2*P.m+1)
  let D := costStepNumberBase P C V
  let fuel := costRounds P.n C
  let w := wordSize 16384 input
  change (∀ x∈[0,C,U,input.length],x<2^w) ∧
    (feasibilityPhaseContract w solver entry T hproc I hv C U).pre [0,C,U,input.length] (initMem input)
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
  have h2_4 : b^2≤b^4 := Nat.pow_le_pow_right hbpos (by decide)
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
    have h3_4 : b^3≤b^4 := Nat.pow_le_pow_right hbpos (by decide)
    have h4_5 : 2*b^4≤b^5 :=
      (Nat.mul_le_mul_right (b^4) (show 2≤b by omega)).trans_eq (pow_succ' b 4).symm
    omega
  have h5_20 : b^5≤b^20 := Nat.pow_le_pow_right hbpos (by decide)
  have hD : D≤b^21 := by
    have hh : 2*b^20≤b^21 :=
      (Nat.mul_le_mul_right (b^20) (show 2≤b by omega)).trans_eq (pow_succ' b 20).symm
    change P.n+4*P.m+(P.m+P.m)^10+C+V+8≤b^21
    omega
  have hN : D^524≤b^11004 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hD 524
  have hCLog : Nat.clog 2 (C+1)≤C+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hnLog : Nat.clog 2 (P.n+1)≤P.n+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuel : fuel+2≤b^2 := by
    have hh : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
    change 1+Nat.clog 2 (C+1)+Nat.clog 2 (P.n+1)+2≤b^2
    omega
  have hcells : (fuel+2)*D^524≤b^11006 := by
    simpa only [←pow_add] using Nat.mul_le_mul hfuel hN
  have hlinS : P.solverWords.length+P.n+2+P.m+2*P.n+3+P.m+3≤14*b := by
    rw [P.solverWords_length]
    omega
  have h3_11006 : b^3≤b^11006 := Nat.pow_le_pow_right hbpos (by decide)
  have hS : costScalingSpace P C V≤b^11007 := by
    have hh : 2*b^11006≤b^11007 :=
      (Nat.mul_le_mul_right (b^11006) (show 2≤b by omega)).trans_eq (pow_succ' b 11006).symm
    change P.solverWords.length+P.n+2+P.m+2*P.n+3+(fuel+2)*D^524+P.m+3≤b^11007
    omega
  have hprune : prunedScalingSpace P C B≤b^11008 := by
    have hs := prunedScalingSpace_le P C B
    change prunedScalingSpace P C B≤2+10*P.m+costScalingSpace P C V at hs
    have hlin : 2+10*P.m≤14*b := by omega
    have h3 : b^3≤b^11007 := Nat.pow_le_pow_right hbpos (by decide)
    have hh : 2*b^11007≤b^11008 :=
      (Nat.mul_le_mul_right (b^11007) (show 2≤b by omega)).trans_eq (pow_succ' b 11007).symm
    omega
  have hlinOuter : input.length+4+16*I.m+12*I.n+P.m+4*P.m+2+3≤40*b := by omega
  have h4 : b^4≤b^11008 := Nat.pow_le_pow_right hbpos (by decide)
  have hspace : input.length+feasibilityPhaseSpace I hv C U≤b^16384 := by
    have hh : 2*b^11008≤b^11009 :=
      (Nat.mul_le_mul_right (b^11008) (show 2≤b by omega)).trans_eq (pow_succ' b 11008).symm
    have hx : b^11009≤b^16384 := Nat.pow_le_pow_right hbpos (by decide)
    change input.length+(4+16*I.m+12*I.n+prunedScalingSpace P C B+P.m+4*P.m+2+3)≤b^16384
    omega
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤16384) input
  change b^16384<2^w at hp
  have h4full : b^4≤b^16384 := Nat.pow_le_pow_right hbpos (by decide)
  have h5full : b^5≤b^16384 := Nat.pow_le_pow_right hbpos (by decide)
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
    exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
  · intro x hx
    exact ((hPwords x hx).trans h4full).trans_lt hp
  · have he : (2*I.m+2)*U=2*(I.m+1)*U := by ring
    rw [he]
    exact ((hbudgetProduct.trans (Nat.pow_le_pow_right hbpos (by decide : 3≤16384)))).trans_lt hp
  · exact (hB.trans h4full).trans_lt hp
  · exact (h5.trans h5full).trans_lt hp
  · exact (hP5.trans h5full).trans_lt hp

end MinCostFlow.Scaling.Machine
