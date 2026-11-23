module

public import MinCostFlow.Scaling.ArbitraryDemandContract
import MinCostFlow.Scaling.ArbitraryDemandCountedCost
import MinCostFlow.Scaling.EmptyOuterCounters
import MinCostFlow.Scaling.SolverTimePositive
import MinCostFlow.Scaling.GeneralScalingLogs
import Mathlib.Tactic.Ring

/-!
# The outer procedure's paper-form running time

Substitute the proved arbitrary-demand call and work counts into the
actual machine budget. Monotonicity raises the uniform solver dimensions
to a single explicit constant times the original dimensions. The three
padded logarithmic factors multiply solver time plus edge work, and the
vertex scan remains additive. Empty edge sets use the exact zero-call
counters and the positive time of a solver on the empty circulation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- An explicit constant covering outer machine costs and solver dimensions. -/
def outerScalingConstant (solver : Program) : ℕ := 1000000000000000000*(solver.regBound+1)

private theorem outer_paper_budget (calls work m n reg A B L time : ℕ)
    (hc : calls≤345600*A*B*L) (hw : work≤210000000000*m*A*B*L+85*n) :
    calls*((reg+6)*time)+2000000*(reg+1)*work≤
      1000000000000000000*(reg+1)*A*B*L*(time+m)+1000000000000000000*(reg+1)*n := by
  have hcoef : 345600*(reg+6)≤1000000000000000000*(reg+1) := by omega
  have hcalls : calls*((reg+6)*time)≤1000000000000000000*(reg+1)*A*B*L*time := by
    calc
      _ ≤ (345600*A*B*L)*((reg+6)*time) := Nat.mul_le_mul_right _ hc
      _ = 345600*(reg+6)*(A*B*L*time) := by ring
      _ ≤ 1000000000000000000*(reg+1)*(A*B*L*time) := Nat.mul_le_mul_right _ hcoef
      _ = _ := by ring
  have hwork : 2000000*(reg+1)*work≤
      1000000000000000000*(reg+1)*A*B*L*m+1000000000000000000*(reg+1)*n := by
    calc
      _ ≤ 2000000*(reg+1)*(210000000000*m*A*B*L+85*n) := Nat.mul_le_mul_left _ hw
      _ = 420000000000000000*((reg+1)*(A*B*L*m))+170000000*((reg+1)*n) := by ring
      _ ≤ 1000000000000000000*((reg+1)*(A*B*L*m))+
          1000000000000000000*((reg+1)*n) := Nat.add_le_add
        (Nat.mul_le_mul_right _ (by decide)) (Nat.mul_le_mul_right _ (by decide))
      _ = _ := by ring
  exact (Nat.add_le_add hcalls hwork).trans_eq (by ring)

/-- The complete outer procedure costs at most
`K*(actualCalls*T(K*n,K*m)+actualWork)` for the explicit constant `K`,
including every rejection and empty-input branch. -/
theorem arbitraryDemand_cost_model (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv C U
    (arbitraryDemandContract w solver entry T hproc I hv C U).cost args mem≤
      outerScalingConstant solver*(r.calls.length*
        T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m)+r.work) := by
  let r := FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv C U
  let K := outerScalingConstant solver
  have hb := arbitraryDemand_cost_counted w solver entry T hproc hmono I hv C U args mem
  change (arbitraryDemandContract w solver entry T hproc I hv C U).cost args mem≤
    r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+2000000*(solver.regBound+1)*r.work at hb
  have hreg : solver.regBound+6≤K := by dsimp only [K,outerScalingConstant]; omega
  have hwork : 2000000*(solver.regBound+1)≤K := by dsimp only [K,outerScalingConstant]; omega
  have h8 : 8≤K := by dsimp only [K,outerScalingConstant]; omega
  have h72 : 72≤K := by dsimp only [K,outerScalingConstant]; omega
  have ht := hmono (8*I.n) (K*I.n) (72*I.m) (K*I.m)
    (Nat.mul_le_mul_right I.n h8) (Nat.mul_le_mul_right I.m h72)
  have hc : r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))≤
      K*(r.calls.length*T (K*I.n) (K*I.m)) :=
    (Nat.mul_le_mul_left r.calls.length (Nat.mul_le_mul hreg ht)).trans_eq (by ring)
  exact hb.trans ((Nat.add_le_add hc (Nat.mul_le_mul_right r.work hwork)).trans_eq (by ring))

/-- The complete outer procedure has the explicit paper-form bound
`K*log(m)*log(mU)*log(C)*(T(K*n,K*m)+m)+K*n`, with padded binary logs
and `K=10^18*(regBound+1)`, on every nonempty valid input. -/
theorem arbitraryDemand_cost_paper_nonempty (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) (hm : 0<I.m) :
    (arbitraryDemandContract w solver entry T hproc I hv C U).cost args mem≤
      outerScalingConstant solver*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)*
          (T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m)+I.m)+
        outerScalingConstant solver*I.n := by
  let r := FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv C U
  have hc := FlowReduction.arbitraryDemandScalingModel_calls (canonicalSolver solver entry T hproc) I hv C U
  have hw := FlowReduction.arbitraryDemandScalingModel_work (canonicalSolver solver entry T hproc) I hv C U hm
  have hb := arbitraryDemand_cost_counted w solver entry T hproc hmono I hv C U args mem
  change (arbitraryDemandContract w solver entry T hproc I hv C U).cost args mem≤
    r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+2000000*(solver.regBound+1)*r.work at hb
  have h8 : 8≤outerScalingConstant solver := by unfold outerScalingConstant; omega
  have h72 : 72≤outerScalingConstant solver := by unfold outerScalingConstant; omega
  have ht := hmono (8*I.n) (outerScalingConstant solver*I.n) (72*I.m)
    (outerScalingConstant solver*I.m) (Nat.mul_le_mul_right I.n h8) (Nat.mul_le_mul_right I.m h72)
  have hbudget := outer_paper_budget r.calls.length r.work I.m I.n solver.regBound
    (Nat.clog 2 (I.m+1)+1) (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1) (Nat.clog 2 (C+2))
    (T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m)) hc hw
  exact hb.trans ((Nat.add_le_add_right (Nat.mul_le_mul_left r.calls.length
    (Nat.mul_le_mul_left (solver.regBound+6) ht)) _).trans hbudget)

/-- The explicit logarithmic outer cost bound holds on all valid inputs,
including graphs with no edges or vertices. -/
theorem arbitraryDemand_cost_paper (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (arbitraryDemandContract w solver entry T hproc I hv C U).cost args mem≤
      outerScalingConstant solver*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)*
          (T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m)+I.m)+
        outerScalingConstant solver*I.n := by
  by_cases hm : 0<I.m
  · exact arbitraryDemand_cost_paper_nonempty w solver entry T hproc hmono I hv C U args mem hm
  have hz : I.m=0 := by omega
  obtain ⟨hc,hw⟩ := arbitraryDemandScalingModel_empty_counters
    (canonicalSolver solver entry T hproc) I hv C U hz
  have hb := arbitraryDemand_cost_counted w solver entry T hproc hmono I hv C U args mem
  dsimp only at hb
  rw [hc,zero_mul,zero_add] at hb
  have hcost := hb.trans (Nat.mul_le_mul_left (2000000*(solver.regBound+1)) hw)
  have ht : 1≤T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m) :=
    (solverTime_zero_pos solver entry T hproc).trans (hmono 0 _ 0 _ (Nat.zero_le _) (Nat.zero_le _))
  have hl : 1≤Nat.clog 2 (C+2) := Nat.clog_pos (by decide) (by omega)
  have hfactor : outerScalingConstant solver≤
      outerScalingConstant solver*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)*
          (T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m)+I.m) := by
    calc
      _ ≤ _*(Nat.clog 2 (I.m+1)+1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _*(Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _*Nat.clog 2 (C+2) := Nat.le_mul_of_pos_right _ hl
      _ ≤ _*(T (outerScalingConstant solver*I.n) (outerScalingConstant solver*I.m)+I.m) :=
        Nat.le_mul_of_pos_right _ (by omega)
  have hsmall : 2000000*(solver.regBound+1)*(83*I.n+2)≤
      outerScalingConstant solver+outerScalingConstant solver*I.n := by
    unfold outerScalingConstant
    calc
      _ = 166000000*((solver.regBound+1)*I.n)+4000000*(solver.regBound+1) := by ring
      _ ≤ 1000000000000000000*((solver.regBound+1)*I.n)+1000000000000000000*(solver.regBound+1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by decide)) (Nat.mul_le_mul_right _ (by decide))
      _ = _ := by ring
  exact hcost.trans (hsmall.trans (Nat.add_le_add_right hfactor _))

end MinCostFlow.Scaling.Machine
