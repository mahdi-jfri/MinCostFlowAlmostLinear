module

public import MinCostFlow.Scaling.MeasuredCostScaling
public import MinCostFlow.Scaling.CapacityScalingModel
public import MinCostFlow.Scaling.CostCallGeometry
public import MinCostFlow.Scaling.CompositionLogs
import Mathlib.Tactic.Ring

/-!
# Composing cost and capacity scaling

Lemma C.1 of Chen et al., arXiv:2203.00671v2, first reduces costs and then
implements each bounded-cost call by capacity scaling. The function below
executes that composition with integer state and explicit nested traces.
Every primitive solver input satisfies its own polynomial cost and capacity
bounds. Optimality is a separate property of the two reductions.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Cost scaling with each invocation implemented by capacity scaling. -/
def costCapacityModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C U : ℕ) : CallResult (Fin I.m → ℤ) :=
  costScalingMeasured (fun J => capacityScalingModel solve J (max U (2 * I.m + 1))) I C

/-- Every primitive input has at most `24*m` edges. -/
theorem costCapacityModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C U : ℕ) :
    ∀ J ∈ (costCapacityModel solve I C U).calls, J.m ≤ 24 * I.m := by
  unfold costCapacityModel
  rw [costScalingMeasured_calls]
  apply CallResult.expand_instances
  intro J hJ K hK
  have he := capacityScalingModel_edges solve J (max U (2 * I.m + 1)) K hK
  have hb := costScalingModel_edges
    (fun J => (capacityScalingModel solve J (max U (2 * I.m + 1))).value) I C J hJ
  omega

/-- All primitive calls meet the exact bounded solver's input specification. -/
theorem costCapacityModel_inputs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C U : ℕ) (hc : I.CostsBounded C) :
    ∀ J ∈ (costCapacityModel solve I C U).calls,
      J.CostsBounded (J.m ^ 10) ∧ ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
  unfold costCapacityModel
  rw [costScalingMeasured_calls]
  apply CallResult.expand_instances
  intro J hJ K hK
  have hj := costScalingModel_polynomialCosts
    (fun J => (capacityScalingModel solve J (max U (2 * I.m + 1))).value) I C hc J hJ
  exact ⟨capacityScalingModel_costs solve J _ hj K hK,
    capacityScalingModel_capacities solve J _ K hK⟩

private theorem inner_calls_bound (solve : (J : Circulation) → Fin J.m → ℤ)
    (m U : ℕ) (J : Circulation) (hj : J.m ≤ 12 * m) :
    (capacityScalingModel solve J (max U (2 * m + 1))).calls.length ≤
      720 * (Nat.clog 2 (m + 1) + 1) *
        (Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) + 1) := by
  have he := composition_edge_log m J.m hj
  have hu := composition_capacity_log m U
  have h1 : Nat.clog 2 (J.m + 1) + 1 ≤ 5 * (Nat.clog 2 (m + 1) + 1) := by omega
  have h2 : Nat.clog 2 (J.m + 1) + Nat.clog 2 (max U (2 * m + 1) + 1) + 1 ≤
      6 * (Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) + 1) := by omega
  calc
    _ ≤ 24 * (Nat.clog 2 (J.m + 1) + 1) *
        (Nat.clog 2 (J.m + 1) + Nat.clog 2 (max U (2 * m + 1) + 1) + 1) :=
      capacityScalingModel_calls solve J _
    _ ≤ 24 * (5 * (Nat.clog 2 (m + 1) + 1)) *
        (6 * (Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 24 h1) h2
    _ = _ := by ring

/-- The composed function makes at most `5760` times the three padded
binary logarithmic factors many primitive calls. -/
theorem costCapacityModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C U : ℕ) :
    (costCapacityModel solve I C U).calls.length ≤
      5760 * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) * Nat.clog 2 (C + 2) := by
  unfold costCapacityModel
  rw [costScalingMeasured_calls]
  let inner := fun J => capacityScalingModel solve J (max U (2 * I.m + 1))
  let outer := costScalingModel (fun J => (inner J).value) I C
  have hi : ∀ J ∈ outer.calls, (inner J).calls.length ≤
      720 * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by
    intro J hJ
    exact inner_calls_bound solve I.m U J (costScalingModel_edges _ I C J hJ)
  have h := CallResult.expand_calls inner outer _ hi
  have ho := costScalingModel_calls (fun J => (inner J).value) I C
  calc
    _ ≤ outer.calls.length * _ := h
    _ ≤ (8 * Nat.clog 2 (C + 2)) * _ := Nat.mul_le_mul_right _ ho
    _ = _ := by ring

private theorem inner_work_bound (solve : (J : Circulation) → Fin J.m → ℤ)
    (m U : ℕ) (J : Circulation) (hm : 0 < m)
    (hj : m ≤ J.m ∧ J.m ≤ 12 * m ∧ J.n ≤ 2 * m + 2) :
    (capacityScalingModel solve J (max U (2 * m + 1))).work ≤
      108000004 * m * (Nat.clog 2 (m + 1) + 1) *
        (Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) + 1) := by
  let B := Nat.clog 2 (m + 1) + 1
  let S := Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) + 1
  have he := composition_edge_log m J.m hj.2.1
  have hu := composition_capacity_log m U
  have h1 : Nat.clog 2 (J.m + 1) + 1 ≤ 5 * B := by dsimp [B]; omega
  have h2 : Nat.clog 2 (J.m + 1) + Nat.clog 2 (max U (2 * m + 1) + 1) + 1 ≤
      6 * S := by dsimp [S]; omega
  have hp := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left 300000 hj.2.1) h1) h2
  have hw := capacityScalingModel_work solve J (max U (2 * m + 1)) (by omega)
  have hb : 1 ≤ B := by dsimp [B]; omega
  have hs : 1 ≤ S := by dsimp [S]; omega
  have hmb := Nat.mul_le_mul_left m hb
  have hms := Nat.mul_le_mul_left (m * B) hs
  have hp' : 300000 * (12 * m) * (5 * B) * (6 * S) = 108000000 * (m * B * S) := by ring
  rw [hp'] at hp
  change (capacityScalingModel solve J (max U (2 * m + 1))).work ≤
    108000004 * m * B * S
  simp only [Nat.mul_one] at hmb hms
  simp only [Nat.mul_assoc] at hw hp hmb hms ⊢
  omega

/-- The local-work counter has the three logarithmic factors, with one
initial scan of the original vertex table. -/
theorem costCapacityModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C U : ℕ) (hm : 0 < I.m) :
    (costCapacityModel solve I C U).work ≤
      1000000000 * I.m * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) * Nat.clog 2 (C + 2) + I.n := by
  unfold costCapacityModel
  rw [costScalingMeasured_work]
  let inner := fun J => capacityScalingModel solve J (max U (2 * I.m + 1))
  let outer := costScalingModel (fun J => (inner J).value) I C
  let B := Nat.clog 2 (I.m + 1) + 1
  let S := Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1
  let L := Nat.clog 2 (C + 2)
  have hi : ∀ J ∈ outer.calls, (inner J).work ≤ 108000004 * I.m * B * S := by
    intro J hJ
    exact inner_work_bound solve I.m U J hm (costScalingModel_geometry _ I C J hJ)
  have hw := CallResult.expand_work inner outer _ hi
  have ho := costScalingModel_work (fun J => (inner J).value) I C hm
  have hc := costScalingModel_calls (fun J => (inner J).value) I C
  have hp := Nat.mul_le_mul_right (108000004 * I.m * B * S) hc
  have hb : 1 ≤ B := by dsimp [B]; omega
  have hs : 1 ≤ S := by dsimp [S]; omega
  have hmb := Nat.mul_le_mul_left I.m hb
  have hms := Nat.mul_le_mul_left (I.m * B) hs
  simp only [Nat.mul_one] at hmb hms
  have hpad := Nat.mul_le_mul_right L (le_trans hmb hms)
  change (CallResult.expand inner outer).work ≤ 1000000000 * I.m * B * S * L + I.n
  have he : (8 * L) * (108000004 * I.m * B * S) = 864000032 * (I.m * B * S * L) := by ring
  change outer.calls.length * (108000004 * I.m * B * S) ≤ (8 * L) * _ at hp
  rw [he] at hp
  change outer.work ≤ 12000 * I.m * L + I.n at ho
  simp only [Nat.mul_assoc] at hpad ho hw hp ⊢
  omega

end MinCostFlow.Scaling
