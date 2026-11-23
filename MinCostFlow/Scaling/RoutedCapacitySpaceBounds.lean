module

public import MinCostFlow.Scaling.CapacityExtractDualContract
public import MinCostFlow.Scaling.CapacityGraphSpaceBounds

/-!
# Uniform space for capacity-backed routing and dual extraction

A source-routing residual has only a constant factor more edge slots and
one more vertex. Its capacity-call numerical base is at most five times
the original base. Squaring absorbs that factor. Power 522 then covers
its full positive capacity call, routing arrays, labels, and primal
residual construction. The bound is independent of flow coordinates.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
private theorem routed_reserve_bound (D base reserve extra : ℕ) (hD8 : 8≤D)
    (hbase : base≤5*D) (hreserve : reserve≤base^260) (hextra : extra≤28*D) :
    extra+reserve≤D^522 := by
  have hDpos : 0<D := by omega
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have hbase2 : base≤D^2 := hbase.trans
    (by simpa only [pow_two] using Nat.mul_le_mul_right D (show 5≤D by omega))
  have hN : reserve≤D^520 := hreserve.trans (by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hbase2 260)
  have hsmall : 28*D≤D^3 :=
    (Nat.mul_le_mul_right D (show 28≤D^2 by omega)).trans_eq (pow_succ D 2).symm
  have h3_520 : D^3≤D^520 := Nat.pow_le_pow_right hDpos (by decide)
  have hlast : 2*D^520≤D^521 :=
    (Nat.mul_le_mul_right (D^520) (show 2≤D by omega)).trans_eq (pow_succ' D 520).symm
  have h521_522 : D^521≤D^522 := Nat.pow_le_pow_right hDpos (by decide)
  omega

set_option exponentiation.threshold 1024 in
/-- Full capacity-backed source-routing label production has a uniform
polynomial reserve in the input dimensions and supplied bounds. -/
theorem capacityRoutingLabelsSpace_le (J : Circulation) (C U : ℕ) :
    capacityRoutingLabelsSpace J C U≤(capacityGraphSpaceBase J C U)^522 := by
  let D := capacityGraphSpaceBase J C U
  let M := J.m+J.n
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  let extra := 4+16*M+M+5+5*(J.n+1)+6*M+2
  have hD : J.n+2*J.m+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hbase : capacityGraphSpaceBase Q C U≤5*D := by
    change (J.n+1)+2*((J.m+J.n)+(J.m+J.n))+C+U+8≤5*D
    omega
  have he : extra≤28*D := by dsimp only [extra,M]; omega
  have hres := routed_reserve_bound D _ _ extra hD8 hbase (capacityPositiveSpace_le Q C U) he
  calc
    _ = extra+capacityPositiveSpace Q C U := by
      change 4+16*M+capacityPositiveSpace Q C U+M+5+5*(J.n+1)+6*M+2=extra+capacityPositiveSpace Q C U
      dsimp only [extra]
      omega
    _ ≤ _ := hres

set_option exponentiation.threshold 1024 in
/-- Including the primal residual does not increase the fixed power-522
bound for measured dual extraction, for every integral source flow. -/
theorem capacityExtractDualSpace_le (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) :
    capacityExtractDualSpace J flow C U≤(capacityGraphSpaceBase J C U)^522 := by
  let D := capacityGraphSpaceBase J C U
  let R := J.residual flow
  let M := R.m+R.n
  let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
  let extra := 2+10*J.m+(4+16*M+M+5+5*(J.n+1)+6*M+2)
  have hD : J.n+2*J.m+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hbase : capacityGraphSpaceBase Q C U≤5*D := by
    change (J.n+1)+2*(((J.m+J.m)+J.n)+((J.m+J.m)+J.n))+C+U+8≤5*D
    omega
  have he : extra≤28*D := by
    change 2+10*J.m+(4+16*(J.m+J.m+J.n)+(J.m+J.m+J.n)+5+5*(J.n+1)+6*(J.m+J.m+J.n)+2)≤28*D
    omega
  have hres := routed_reserve_bound D _ _ extra hD8 hbase (capacityPositiveSpace_le Q C U) he
  calc
    _ = extra+capacityPositiveSpace Q C U := by
      change 2+10*J.m+(4+16*M+capacityPositiveSpace Q C U+M+5+5*(J.n+1)+6*M+2)=extra+capacityPositiveSpace Q C U
      dsimp only [extra]
      omega
    _ ≤ _ := hres

end MinCostFlow.Scaling.Machine
