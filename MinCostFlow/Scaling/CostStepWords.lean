module

public import MinCostFlow.Scaling.CostStepSpace
import MinCostFlow.Scaling.CostRoundedScalarWords
import MinCostFlow.Scaling.BottleneckGuestSpace

/-!
# Complete cost-round word premises from uniform bounds

The original graph fields fit the common cost-round numerical base.
Its cube bounds the current power and its sixth power the potentials.
These bounds supply every scalar rounding, augmentation, dual-label, and
potential-update word premise. The same power-524 reserve covers all
fresh allocation and fixed constants, leaving no extra numeric promise
about the called solver's future output.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- Current data, uniform power and potential bounds, and the single
polynomial space reserve supply the full measured cost-round precondition. -/
theorem costStep_pre_of_space {w : ℕ} (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    {J : Circulation} (s : CostState J) (C U a state heap : ℕ) (mem : ℕ → ℕ)
    (hgraph : ListAt mem a J.solverWords) (hgraphEnd : a+J.solverWords.length≤heap)
    (hstateEnd : state+3=heap) (hstate : CostStateAt mem state heap s)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) (hm : 0<J.m) (hnU : J.n+1≤U)
    (hpower : s.power≤(costStepNumberBase J C U)^3)
    (hpot : ∀ v,(s.potential v).natAbs≤(costStepNumberBase J C U)^6)
    (hz : ZeroFrom mem heap) (hs : heap+(costStepNumberBase J C U)^524<2^w) :
    (costStepContract w solver entry T hproc s C U).pre [a,state,C,U,heap] mem := by
  let D := costStepNumberBase J C U
  let B := J.m+J.m
  let N := D^524
  let Q := (4*J.m+J.n)*B^10
  have hD : J.n+4*J.m+B^10+C+U+8=D := rfl
  have hB : B=J.m+J.m := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have h1N : D≤N := Nat.le_pow (by decide)
  have h2N : D^2≤N := Nat.pow_le_pow_right hDpos (by decide)
  have h4N : D^4≤N := Nat.pow_le_pow_right hDpos (by decide)
  have h7N : D^7≤N := Nat.pow_le_pow_right hDpos (by decide)
  have hNword : N<2^w := by change heap+N<2^w at hs; omega
  have hmax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D (by omega) (by omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hfields : J.n+B+U+B^10+2≤D := by omega
  have hC1 : C+1≤D := by omega
  have hU2 : 2*U≤D^2 := by
    have huD : U≤D := by omega
    exact (Nat.mul_le_mul_left 2 huD).trans
      (by simpa only [pow_two] using Nat.mul_le_mul_right D (show 2≤D by omega))
  have hpower2 : 2*s.power≤D^4 := by
    have hp : s.power≤D^3 := hpower
    exact (Nat.mul_le_mul_left 2 hp).trans
      ((Nat.mul_le_mul_right (D^3) (show 2≤D by omega)).trans_eq (pow_succ' D 3).symm)
  have hlabel : (4*J.m+J.n+1)*B^10≤D^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show 4*J.m+J.n+1≤D by omega) (show B^10≤D by omega)
  have hQ : Q≤D^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show 4*J.m+J.n≤D by omega) (show B^10≤D by omega)
  have h2_6 : D^2≤D^6 := Nat.pow_le_pow_right hDpos (by decide)
  have hpotBudget : ∀ v,2*((s.potential v).natAbs+Q)≤D^7 := by
    intro v
    have hp : (s.potential v).natAbs≤D^6 := hpot v
    have hlast : 4*D^6≤D^7 :=
      (Nat.mul_le_mul_right (D^6) (show 4≤D by omega)).trans_eq (pow_succ' D 6).symm
    omega
  have hscalar := roundedCost_pre_of_cost_bounds s C U heap mem hC hpower hpot hz hs
  have hspace := costStepSpace_le solver entry T hproc s C U
  refine ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hf,hC,hu,hm,hnU,?_,
    (hfields.trans h1N).trans_lt hNword,(hC1.trans h1N).trans_lt hNword,
    (hpower2.trans h4N).trans_lt hNword,(hU2.trans h2N).trans_lt hNword,
    (hlabel.trans h2N).trans_lt hNword,(fun v => ((hpotBudget v).trans h7N).trans_lt hNword),hscalar,hz,?_⟩
  · intro x hx
    exact ((Link.elem_le_foldr_max hx).trans hmax |>.trans h1N).trans_lt hNword
  · exact (Nat.add_le_add_left hspace heap).trans_lt hs

end MinCostFlow.Scaling.Machine
