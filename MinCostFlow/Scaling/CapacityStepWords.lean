module

public import MinCostFlow.Scaling.CapacityStepSpace
import MinCostFlow.Scaling.CapacityRoundedSpace
import MinCostFlow.Scaling.BottleneckGuestSpace
import MinCostFlow.Scaling.CapacityNumericFacts

/-!
# Deriving every capacity-step word premise from one reserve

A common base bounds the current and residual coordinates, candidate
objective, clipping products, and both kinds of canonical guest. The
power-256 reserve exceeds every such number and the entire step's fresh
workspace. Hence the next iteration needs only this uniform reserve and
the represented bounded flow, rather than separate intermediate bounds.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- All numerical and workspace premises of a capacity step follow from
one uniform reserve and the original graph's coordinate bounds. -/
theorem capacityStep_pre_of_space {w : ℕ} (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hm : 0<J.m) (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e)
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U)
    (a state heap : ℕ) (mem : ℕ → ℕ) (hgraph : ListAt mem a J.solverWords)
    (hgraphEnd : a+J.solverWords.length≤heap) (hstateEnd : state+2=heap)
    (hstate : CapacityStateAt mem state heap s) (hz : ZeroFrom mem heap)
    (hspace : heap+(capacityStepNumberBase J C U)^256<2^w) :
    (capacityStepContract w solver entry T hproc J s C U).pre [a,state,heap] mem := by
  let D := capacityStepNumberBase J C U
  let R := J.residual s.flow
  let B := (polyApproxModel (canonicalSolver solver entry T hproc) R).value.magnitude
  let G := bottleneckGuestBound R (sortCapacities (List.ofFn R.capacity)).1
  let g := wordSize 5 (R.scaledRoundedInstance B).positiveInstance.solverWords
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have hpower : D^256<2^w := by change heap+D^256<2^w at hspace; omega
  have h2 : 16≤D^2 := Nat.pow_le_pow_left hD4 2
  have hlinear : 4*D≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul_right D hD4
  have hD256 : D≤D^256 := by simpa only [pow_one] using Nat.pow_le_pow_right hDpos (by decide : 1≤256)
  have h2_256 : D^2≤D^256 := Nat.pow_le_pow_right hDpos (by decide)
  have h3_256 : D^3≤D^256 := Nat.pow_le_pow_right hDpos (by decide)
  have h4_256 : D^4≤D^256 := Nat.pow_le_pow_right hDpos (by decide)
  have h23_256 : D^23≤D^256 := Nat.pow_le_pow_right hDpos (by decide)
  have h41_256 : D^41≤D^256 := Nat.pow_le_pow_right hDpos (by decide)
  have h216_256 : D^216≤D^256 := Nat.pow_le_pow_right hDpos (by decide)
  have hRn : R.n=J.n := rfl
  have hRm : R.m=J.m+J.m := rfl
  have hRmD : R.m≤D := by rw [hRm]; omega
  have hCD : C≤D := by omega
  have hUD : U≤D := by omega
  have hC_R := J.residual_costsBounded s.flow C hC
  have hRcap := J.residual_capacities_le s.flow (integral_capacity_bounds_cast J s.flow hf) U hu
  have hpolyR := J.residual_polynomialCosts s.flow hc
  have hsourceMax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D
    (by omega) (by omega) (fun e => (hu e).trans hUD) (fun e => (hC e).trans hCD) (by omega)
  have hresidual := capacityResidual_encoding_bounds J s C U hf hC hu
  have hresMax : R.solverWords.foldr max 0≤D^2 := hresidual.1
  have hresBase : R.solverWords.length+R.solverWords.foldr max 0+2≤D^4 := hresidual.2
  have hsourceWords : ∀ x∈J.solverWords,x<2^w := fun x hx =>
    ((Link.elem_le_foldr_max hx).trans hsourceMax).trans_lt (hD256.trans_lt hpower)
  have hresWords : ∀ x∈R.solverWords,x<2^w := fun x hx =>
    ((Link.elem_le_foldr_max hx).trans hresMax).trans_lt (h2_256.trans_lt hpower)
  have hmass : R.m*C≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul hRmD hCD
  have hbudget : (6*R.m+2)*C≤D^4 := by
    have hfactor : 6*R.m+2≤8*D := by omega
    have hmul : (6*R.m+2)*C≤8*D^2 := by
      simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul hfactor hCD
    have h4 : 16*D^2≤D^4 := by
      have h := Nat.mul_le_mul_right (D^2) h2
      simpa only [←pow_add] using h
    omega
  have hproduct : R.m*(C*U)≤D^3 := by
    simpa only [pow_succ',pow_two,pow_zero,Nat.mul_one] using Nat.mul_le_mul hRmD (Nat.mul_le_mul hCD hUD)
  have hB : B≤D^3 :=
    (polyApprox_magnitude_le solver entry T hproc R C U hpolyR hC_R hRcap).trans hproduct
  have hround : B*R.m^20≤D^23 := by
    have h := Nat.mul_le_mul hB (Nat.pow_le_pow_left hRmD 20)
    simpa only [←pow_add] using h
  have hguest : 2^G≤D^40 := by
    have h := Nat.pow_le_pow_left hresBase 10
    rw [←pow_mul] at h
    exact (bottleneckGuestBound_space_le R _).trans h
  have h40positive : 1≤D^40 := Nat.one_le_pow 40 _ (by omega)
  have h41 : 4*D^40≤D^41 :=
    (Nat.mul_le_mul_right (D^40) hD4).trans_eq (pow_succ' D 40).symm
  have hguestMargin : 2^(G+1)+2≤D^41 := by rw [pow_succ]; omega
  have hroundMargin : B=0 ∨ 2^(g+1)+2≤2^w := by
    by_cases hb : B=0
    · exact Or.inl hb
    · right
      have hcost : R.CostsBounded D := fun e => (hC_R e).trans hCD
      have hmargin : 2^(g+1)+2≤D^216 := capacityRoundedGuest_margin_le R B D hD4
        (by rw [hRn]; omega) hRmD hcost (by rw [hRm]; omega) (Nat.pos_of_ne_zero hb)
      exact (hmargin.trans h216_256).trans hpower.le
  have hreserve := capacityStepSpace_le solver entry T hproc J s C U hm hf hC hu
  refine ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hsourceWords,hresWords,hf,hC,hu,hm,hz,
    (Nat.add_le_add_left hreserve heap).trans_lt hspace,?_,hmass.trans_lt (h2_256.trans_lt hpower),
    (hguestMargin.trans h41_256).trans hpower.le,hbudget.trans_lt (h4_256.trans_lt hpower),
    hproduct.trans_lt (h3_256.trans_lt hpower),hround.trans_lt (h23_256.trans_lt hpower),hroundMargin,?_,?_⟩
  · have hsmall : R.m+2≤D^2 := by omega
    exact (hsmall.trans h2_256).trans_lt hpower
  · have hadd : 2*U≤D^2 := by omega
    exact (hadd.trans h2_256).trans_lt hpower
  · omega

end MinCostFlow.Scaling.Machine
