module

public import MinCostFlow.IPM.Machine.EpochConditions
public import MinCostFlow.IPM.Machine.EpochLayoutArgs
import MinCostFlow.IPM.Machine.HistoryExtension

/-!
# Entering the finite epoch loop

Initialize the actual caller counter to zero. Its DS history starts at
the arrays in the same memory, with zero accumulated flow and report
time zero. The first complete refresh input and numerical cache proved
from startup establish the loop condition at this actual machine state.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual counter initialization enters a successful-prefix epoch
condition at stage zero, using the cache and first-call input from startup. -/
theorem epochConditions_initial_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ)
    (p : Program) (ω : ℕ → Bool)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    ∃ P : EpochPoint R.τ,
      Runs w p ω (.assign 26 (.const 0)) (startState (L.packet F I heap++[finish]) mem pos)
        .normal P.machine 2 ∧ EpochConditions F A I κ α rate allocation R L q K mem heap space finish 0 P ∧
      P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x := by
  let caller := startState (L.packet F I heap++[finish]) mem pos
  let P : EpochPoint R.τ :=
    {history := ⟨fun _ => namedInstance I,fun _ => [],
        fun _ => readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m,
        fun _ => readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m⟩
     eta := fun _ => 0
     op := fun _ => false
     credit := x
     machine := {caller with regs:=Function.update caller.regs 26 0}}
  have hheap : P.machine.regs 8=heap := by
    dsimp only [P]
    rw [Function.update_of_ne (by decide : 8≠26)]
    exact (L.packet_start_regs F I heap finish mem pos 8 (by decide)).trans (L.packet_heap F I heap)
  have hcount : P.machine.regs 25=finish := by
    dsimp only [P]
    rw [Function.update_of_ne (by decide : 25≠26)]
    exact L.packet_start_count F I heap finish mem pos
  have hcounter : P.machine.regs 26=0 := by simp [P]
  have hlength : ∀ e∈(namedInstance I).E,
      0<readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e := by
    intro e he
    have heM : e<I.m := Finset.mem_range.mp he
    simpa only [readVector,heM,ite_true] using (hcache e heM).2.2.2.1.1
  have hvalid : MinRatioHistoryValid P.history P.op 0 :=
    minRatioHistoryValid_constant _ _ _ (namedInstance_valid I hI) hlength _ _
  refine ⟨P,epochIterationsInit_runs p caller ω,?_,rfl,hheap,rfl⟩
  refine ⟨Nat.zero_le _,hcount,hcounter,?_,?_,?_,?_,hvalid,?_,?_,?_,?_,?_,hranges,
    fun _ _ e he => ⟨(hranges e (Finset.mem_range.mp he)).2.2.2.1,
      (hranges e (Finset.mem_range.mp he)).2.2.2.2⟩⟩

  · intro j hj
    rw [hheap]
    dsimp only [P]
    rw [Function.update_of_ne (by omega : j≠26)]
    exact L.packet_start_regs F I heap finish mem pos j hj
  · rw [hheap]
    simp
  · change mem (P.machine.regs 8-3)≤5*I.m
    rw [hheap,hbudget]
  · intro _ _
    rfl
  · intro _ _
    rfl
  · rw [hheap]
    exact hpre
  · rfl
  · rfl
  · exact hcache

end MinCostFlow.IPM.Machine
