module

public import MinCostFlow.Scaling.CostStepSpace
import MinCostFlow.Scaling.RoundedCostCalls

/-!
# Scalar rounding words from uniform cost-state bounds

Bound the denominator power by the cube of the common numerical base and
potential magnitudes by its sixth power. Residual costs, the eighth-power
scale, and `C+1` are at most the base. Products, differences, and rounding
adjustments then use at most ten powers. The full power-524 space reserve
therefore also covers every scalar operand and intermediate operation.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- The uniform reached-state power and potential bounds supply every
scalar rounded-cost arithmetic premise at a fitting fresh heap. -/
theorem roundedCost_pre_of_cost_bounds {w : ℕ} {J : Circulation} (s : CostState J) (C U heap : ℕ)
    (mem : ℕ → ℕ) (hC : J.CostsBounded C)
    (hpower : s.power≤(costStepNumberBase J C U)^3)
    (hpot : ∀ v,(s.potential v).natAbs≤(costStepNumberBase J C U)^6)
    (hz : ZeroFrom mem heap) (hs : heap+(costStepNumberBase J C U)^524<2^w) :
    ∀ e,(roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem := by
  let D := costStepNumberBase J C U
  let B := J.m+J.m
  have hD : J.n+4*J.m+B^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have h10_524 : D^10≤D^524 := Nat.pow_le_pow_right hDpos (by decide)
  have h10Word : D^10<2^w := by change heap+D^524<2^w at hs; omega
  have h1_10 : D≤D^10 := Nat.le_pow (by decide)
  have h2_10 : D^2≤D^10 := Nat.pow_le_pow_right hDpos (by decide)
  have h4_10 : D^4≤D^10 := Nat.pow_le_pow_right hDpos (by decide)
  have h5_10 : D^5≤D^10 := Nat.pow_le_pow_right hDpos (by decide)
  have h7_10 : D^7≤D^10 := Nat.pow_le_pow_right hDpos (by decide)
  have h8_10 : D^8≤D^10 := Nat.pow_le_pow_right hDpos (by decide)
  have h9_10 : D^9≤D^10 := Nat.pow_le_pow_right hDpos (by decide)
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have h12 : heap+12<2^w := by change heap+D^524<2^w at hs; omega
  have hresCost := J.residual_costsBounded s.flow C hC
  intro e
  let R := J.residual s.flow
  let c := R.cost e
  let x := s.potential (R.tail e)
  let y := s.potential (R.head e)
  let factor := B^8*s.power
  let d := C+1
  have hBpos : 0<B := by have he := e.isLt; change e.val<B at he; omega
  have hB8 : B^8≤D := (Nat.pow_le_pow_right hBpos (by decide : 8≤10)).trans (by omega)
  have hc : c.natAbs≤D := (hresCost e).trans (by omega)
  have hd : d≤D := by dsimp only [d]; omega
  have hx : x.natAbs≤D^6 := hpot _
  have hy : y.natAbs≤D^6 := hpot _
  have hfactor : factor≤D^4 := by
    have hp : s.power≤D^3 := hpower
    exact (Nat.mul_le_mul hB8 hp).trans_eq (pow_succ' D 3).symm
  have hcfactor : c.natAbs*factor≤D^5 := by
    exact (Nat.mul_le_mul hc hfactor).trans_eq (pow_succ' D 4).symm
  have hxy : x.natAbs+y.natAbs≤D^7 := by
    have hlast : 2*D^6≤D^7 :=
      (Nat.mul_le_mul_right (D^6) (show 2≤D by omega)).trans_eq (pow_succ' D 6).symm
    omega
  have hdiff : (x-y).natAbs≤D^7 := (Int.natAbs_sub_le _ _).trans hxy
  have hscaled : (x-y).natAbs*d≤D^8 := by
    exact (Nat.mul_le_mul hdiff hd).trans_eq (pow_succ D 7).symm
  have hcostAbs : (c*(factor : ℤ)).natAbs≤D^5 := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hcfactor
  have hpotAbs : ((x-y)*(d : ℤ)).natAbs≤D^8 := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hscaled
  have h5_8 : D^5≤D^8 := Nat.pow_le_pow_right hDpos (by decide)
  have hsum : (c*(factor : ℤ)).natAbs+((x-y)*(d : ℤ)).natAbs≤D^9 := by
    have hlast : 2*D^8≤D^9 :=
      (Nat.mul_le_mul_right (D^8) (show 2≤D by omega)).trans_eq (pow_succ' D 8).symm
    omega
  have hnum : (s.costNumerator C e).natAbs≤D^9 := by
    rw [costNumerator_eq_reduced]
    exact (Int.natAbs_sub_le _ _).trans hsum
  have h1_9 : D≤D^9 := Nat.le_pow (by decide)
  have hd2 : d/2≤D := (Nat.div_le_self _ _).trans hd
  have hadjust : (s.costNumerator C e).natAbs+d/2≤D^10 := by
    have hlast : 2*D^9≤D^10 :=
      (Nat.mul_le_mul_right (D^9) (show 2≤D by omega)).trans_eq (pow_succ' D 9).symm
    omega
  refine ⟨⟨heap,rfl,(hfactor.trans h4_10).trans_lt h10Word,(hcfactor.trans h5_10).trans_lt h10Word,
    (hxy.trans h7_10).trans_lt h10Word,(hscaled.trans h8_10).trans_lt h10Word,
    (hsum.trans h9_10).trans_lt h10Word,hadjust.trans_lt h10Word⟩,hz,h12⟩

end MinCostFlow.Scaling.Machine
