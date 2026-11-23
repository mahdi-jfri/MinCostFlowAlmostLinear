module

public import MinCostFlow.Final.ScratchCapacitySpace
import MinCostFlow.Scaling.ApproximationWorkLower
import MinCostFlow.Scaling.BottleneckGuestBounds
import MinCostFlow.Scaling.CapacityRoundedGuestBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cost of a capacity step with polynomial scratch

A larger guest width increases the linear setup charge by a constant
factor. The solver calls still use the same rates and dimensions.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The work multiplier includes the relocation registers and the guest-width factor. -/
def scratchWorkFactor (solver : Program) (c d : ℕ) : ℕ :=
  (solver.regBound+1)*scratchWidthFactor c d

theorem scratchWorkFactor_pos (solver : Program) (c d : ℕ) :
    1 ≤ scratchWorkFactor solver c d :=
  Nat.mul_pos (by omega) (scratchWidthFactor_pos c d)

theorem scratchWorkFactor_succ (solver : Program) (c d : ℕ) :
    (scratchWorkFactor solver c d - 1)+1 = scratchWorkFactor solver c d := by
  have h := scratchWorkFactor_pos solver c d
  omega

private theorem guest_overhead (m reg guest : ℕ) (hg : 40*guest≤9000*(m+1)) :
    40*guest+reg≤10000*(reg+1)*(m+1) := by
  have hr : reg≤reg*(m+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left reg (show 1≤m+1 by omega)
  have htop : 10000*(reg+1)*(m+1)=10000*(reg*(m+1))+10000*(m+1) := by ring
  rw [htop]
  omega

private theorem rest_cost {m sw mw : ℕ} (hs : sw+1≤mw) (hm : m+1≤mw) :
    200*sw+1500+9000*(m+1)+100≤10800*mw := by omega

private theorem finish_cost {base charge rest weight : ℕ}
    (hc : charge≤10000*weight) (hr : rest≤10800*weight) :
    base+charge+rest≤base+30000*weight := by omega

private theorem counted_cost (calls solveCost guest reg weightReg searchWork modelWork m : ℕ)
    (hwork : calls*(m+1)≤searchWork) (hs : searchWork+1≤modelWork) (hm : m+1≤modelWork)
    (hg : 40*guest+reg≤10000*(weightReg+1)*(m+1)) :
    calls*(solveCost+40*guest+reg)+200*searchWork+1500+9000*(m+1)+100≤
      calls*solveCost+30000*(weightReg+1)*modelWork := by
  have hcharge : calls*(40*guest+reg)≤10000*(weightReg+1)*modelWork := by
    calc
      _ ≤ calls*(10000*(weightReg+1)*(m+1)) := Nat.mul_le_mul_left calls hg
      _ = 10000*(weightReg+1)*(calls*(m+1)) := by ring
      _ ≤ 10000*(weightReg+1)*modelWork := Nat.mul_le_mul_left _ (hwork.trans (by omega))
  have hrest := rest_cost hs hm
  have hweight : modelWork≤(weightReg+1)*modelWork := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right modelWork (show 1≤weightReg+1 by omega)
  have hrest' : 200*searchWork+1500+9000*(m+1)+100≤10800*(weightReg+1)*modelWork :=
    hrest.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10800 hweight)
  have heq : calls*(solveCost+40*guest+reg)=calls*solveCost+calls*(40*guest+reg) := by ring
  rw [heq]
  have hcharge' : calls*(40*guest+reg)≤10000*((weightReg+1)*modelWork) := by
    simpa only [Nat.mul_assoc] using hcharge
  have hfinal := finish_cost (base := calls*solveCost) hcharge'
    (by simpa only [Nat.mul_assoc] using hrest')
  simpa only [Nat.add_assoc,Nat.mul_assoc] using hfinal

/-- The complete approximation execution is bounded directly by its actual
solver-call count and work counter, with an explicit coefficient. -/
theorem scratchPolyApprox_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    let r := polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J
    (scratchPolyApproxContract w solver entry T S c d hproc J C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+1) J.m)+30000*scratchWorkFactor solver c d*r.work := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let xs := (sortCapacities (List.ofFn J.capacity)).1
  let G := scratchBottleneckGuestBound c d J xs
  let old := bottleneckGuestBound J xs
  let f := scratchWidthFactor c d
  let reg := scratchWorkFactor solver c d - 1
  have heff : reg+1 = scratchWorkFactor solver c d := scratchWorkFactor_succ solver c d
  have hG : old ≤ 75*(Nat.clog 2 (J.m+2)+1) := bottleneckGuestBound_le J xs hn hc
  have hlog : Nat.clog 2 (J.m+2)≤J.m+2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hgOld : 40*old≤9000*(J.m+1) := by omega
  have hg : 40*G+solver.regBound≤10000*(reg+1)*(J.m+1) := by
    have hwidth : G ≤ old*f := scratchBottleneckGuestBound_le c d J xs
    have h := Nat.mul_le_mul_right f (guest_overhead J.m solver.regBound old hgOld)
    rw [heff]
    unfold scratchWorkFactor
    nlinarith only [h, Nat.mul_le_mul_left 40 hwidth, Nat.mul_le_mul_left solver.regBound
      (scratchWidthFactor_pos c d)]
  have hwork := bottleneckSearch_calls_mul_le_work solve J
  have hmodel := polyApproxModel_work_lower solve J
  have hbound := counted_cost (bottleneckSearch solve J).calls.length
    ((solver.regBound+6)*T (J.n+1) J.m) G solver.regBound reg
    (bottleneckSearch solve J).work (polyApproxModel solve J).work J.m
    hwork hmodel.1 hmodel.2 hg
  change (bottleneckSearch solve J).calls.length*
    ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound)+
    200*(bottleneckSearch solve J).work+1500+9000*(J.m+1)+100≤_
  simpa only [polyApproxModel_call_trace, heff] using hbound

private theorem rounded_overhead (m reg g : ℕ) (hg : 40*g≤27000*(m+1)) :
    80*(2+5*m)+40*g+reg+680*m+1600≤40000*(reg+1)*(m+1) := by
  have hr : reg≤reg*(m+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left reg (show 1≤m+1 by omega)
  have heq : 40000*(reg+1)*(m+1)=40000*(reg*(m+1))+40000*(m+1) := by ring
  rw [heq]
  omega

/-- A positive rounded solve has one solver term and linear overhead,
including canonical guest execution and all input/output conversions. -/
theorem scratchCapacityRoundedSolve_cost_positive (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (B : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hm : 0<J.m) (hB : 0<B) (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    (scratchCapacityRoundedSolveContract w solver entry T S c d hproc J B).cost args mem≤
      (solver.regBound+6)*T (J.n+1) J.m+40000*scratchWorkFactor solver c d*(J.m+1) := by
  let K := (J.scaledRoundedInstance B).positiveInstance
  let g := wordSize (scratchWordMultiplier c d) K.solverWords
  let old := wordSize 5 K.solverWords
  let f := scratchWidthFactor c d
  have hguest : old≤225*(Nat.clog 2 (J.m+2)+1) := capacityRoundedGuest_width_le J B hm hB hn hc
  have hlog : Nat.clog 2 (J.m+2)≤J.m+2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hg : 40*old≤27000*(J.m+1) := by omega
  have hover := rounded_overhead J.m solver.regBound old hg
  have hwidth : g≤old*f := scratchWordSize_le c d _
  have hfactor : 1≤f := scratchWidthFactor_pos c d
  have hother : 80*(2+5*J.m)+solver.regBound+680*J.m+1600 ≤
      (80*(2+5*J.m)+solver.regBound+680*J.m+1600)*f :=
    Nat.le_mul_of_pos_right _ hfactor
  have hcharge : 80*(2+5*J.m)+40*g+solver.regBound+680*J.m+1600 ≤
      40000*scratchWorkFactor solver c d*(J.m+1) := by
    unfold scratchWorkFactor
    nlinarith only [Nat.mul_le_mul_right f hover, Nat.mul_le_mul_left 40 hwidth, hother]
  have hlen : K.solverWords.length=2+5*J.m := K.solverWords_length
  simp only [scratchCapacityRoundedSolveContract,heapContract,Nat.ne_of_gt hB,↓reduceIte]
  have h := Nat.add_le_add_left hcharge ((solver.regBound+6)*T (J.n+1) J.m)
  simpa only [←hlen,Nat.add_assoc] using h

private theorem zero_cost (m n reg calls base work pCost : ℕ)
    (hp : pCost≤calls*base+30000*(reg+1)*work) :
    600*m+200+pCost+400≤calls*base+100000*(reg+1)*(20*(m+n+1)+work) := by
  nlinarith only [hp,Nat.zero_le (reg*m),Nat.zero_le (reg*n),Nat.zero_le (reg*work),
    Nat.zero_le m,Nat.zero_le n,Nat.zero_le reg,Nat.zero_le work]

private theorem positive_cost (m n reg calls base work pCost qCost : ℕ)
    (hp : pCost≤calls*base+30000*(reg+1)*work)
    (hq : qCost≤base+40000*(reg+1)*(m+m+1)) :
    600*m+200+pCost+(qCost+100*m+100+400)≤
      (calls+1)*base+100000*(reg+1)*(20*(m+n+1)+work+40*(m+m+1)) := by
  nlinarith only [hp,hq,Nat.zero_le (reg*m),Nat.zero_le (reg*n),Nat.zero_le (reg*work),
    Nat.zero_le m,Nat.zero_le n,Nat.zero_le reg,Nat.zero_le work]

/-- Every capacity iteration is charged to its actual solver-call trace
and other-work counter, with one uniform explicit coefficient. -/
theorem scratchCapacityStep_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hm : 0<J.m) (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    let r := s.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K))
    (scratchCapacityStepContract w solver entry T S c d hproc J s C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+1) (J.m+J.m))+
        100000*scratchWorkFactor solver c d*r.work := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let R := J.residual s.flow
  let B := (polyApproxModel solve R).value.magnitude
  have hpolyR := J.residual_polynomialCosts s.flow hc
  have hRm : R.m=J.m+J.m := rfl
  have hnR : R.n≤2*R.m := by change J.n≤2*(J.m+J.m); omega
  have hmR : 0<R.m := by rw [hRm]; omega
  have hp := scratchPolyApprox_cost_counted w solver entry T S c d hproc R C U [] mem hnR hpolyR
  let reg := scratchWorkFactor solver c d - 1
  have heff : reg+1 = scratchWorkFactor solver c d := scratchWorkFactor_succ solver c d
  cases hs : s.stopped with
  | true =>
    simp only [scratchCapacityStepContract,CapacityState.step,hs,↓reduceIte,List.length_nil,Nat.zero_mul,Nat.mul_one]
    have hw : 1 ≤ scratchWorkFactor solver c d := scratchWorkFactor_pos solver c d
    omega
  | false =>
    by_cases hB : B=0
    · have hBraw : (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) (J.residual s.flow)).value.magnitude=0 := hB
      simp only [scratchCapacityStepContract,CapacityState.step,hs,Bool.false_eq_true,↓reduceIte,hBraw]
      simpa only [heff] using zero_cost J.m J.n reg (polyApproxModel solve R).calls.length
        ((solver.regBound+6)*T (J.n+1) (J.m+J.m)) (polyApproxModel solve R).work _ (by simpa only [heff] using hp)
    · have hBraw : (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) (J.residual s.flow)).value.magnitude≠0 := hB
      have hq := scratchCapacityRoundedSolve_cost_positive w solver entry T S c d hproc R B [] mem hmR
        (Nat.pos_of_ne_zero hB) hnR hpolyR
      simp only [scratchCapacityStepContract,CapacityState.step,hs,Bool.false_eq_true,↓reduceIte,hBraw,
        Circulation.solveCapacityRoundedModel,List.length_append,List.length_singleton]
      simpa only [heff] using positive_cost J.m J.n reg (polyApproxModel solve R).calls.length
        ((solver.regBound+6)*T (J.n+1) (J.m+J.m)) (polyApproxModel solve R).work _ _ (by simpa only [heff] using hp) (by simpa only [heff] using hq)

end MinCostFlow.Final
