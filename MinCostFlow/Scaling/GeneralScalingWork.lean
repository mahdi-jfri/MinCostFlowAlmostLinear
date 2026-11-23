module

public import MinCostFlow.Scaling.GeneralScalingModel
import Mathlib.Tactic.Ring

/-!
# Work of the general-flow scaling composition

The reduction of Lemma C.1 in Appendix C of Chen et al.,
arXiv:2203.00671v2, makes at most two circulation calls. Each compresses its
vertices once. Consequently the vertex-table scans add to the work rather
than multiplying its logarithmic factors. The counter here counts integer
and table operations of the models, prior to the machine implementation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- Each pruned circulation call retains at most one extra vertex. -/
theorem checkedReduction_vertices (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    ∀ J ∈ (checkedReduction solve I hv).calls, J.n ≤ I.n + 1 := by
  unfold checkedReduction
  split
  · intro J hJ
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hJ
    change K.n ≤ I.n + 1
    unfold reduceWithTrace at hK
    split at hK
    · dsimp only at hK
      split at hK
      · rcases List.mem_cons.mp hK with h | h
        · subst K; exact le_rfl
        · have he := List.mem_singleton.mp h
          subst K
          exact Nat.le_succ _
      · have he := List.mem_singleton.mp hK
        subst K; exact le_rfl
    · cases hK
  · simp

private theorem costCapacityModel_work_empty
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C U : ℕ)
    (hm : I.m = 0) : (costCapacityModel solve I C U).work = 1 := by
  simp only [costCapacityModel, costScalingMeasured, hm, ↓reduceIte]

/-- The full integer model has the three logarithmic factors in its other
work, with an additive vertex scan. Constants include both circulation calls. -/
theorem generalScalingModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hm : 0 < I.m) :
    (generalScalingModel solve I hv C U).work ≤
      7000000000 * I.m * (Nat.clog 2 (3 * I.m + 1) + 1) *
        (Nat.clog 2 (3 * I.m + 1) + Nat.clog 2 (scalingCapacityBudget I U + 1) + 1) *
        Nat.clog 2 (max C 1 + 2) + 82 * I.n := by
  let B := Nat.clog 2 (3 * I.m + 1) + 1
  let S := Nat.clog 2 (3 * I.m + 1) + Nat.clog 2 (scalingCapacityBudget I U + 1) + 1
  let L := Nat.clog 2 (max C 1 + 2)
  have hb : 1 ≤ B := by dsimp [B]; omega
  have hs : 1 ≤ S := by dsimp [S]; omega
  have hl : 1 ≤ L := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (max C 1 + 2)
    by_contra hh
    have he : L = 0 := by omega
    change max C 1 + 2 ≤ 2 ^ L at h
    rw [he] at h
    omega
  have hmb := Nat.mul_le_mul_left I.m hb
  have hms := Nat.mul_le_mul_left (I.m * B) hs
  have hml := Nat.mul_le_mul_left (I.m * B * S) hl
  simp only [Nat.mul_one, Nat.mul_assoc] at hmb hms hml
  have hpad : I.m ≤ I.m * (B * (S * L)) := le_trans (le_trans hmb hms) hml
  let inner := fun J => costCapacityModel solve J (max C 1) (scalingCapacityBudget I U)
  let r := checkedReduction (fun J => (inner J).value) I hv
  have hi : ∀ J ∈ r.calls, (inner J).work ≤ 3000000000 * I.m * B * S * L + I.n + 1 := by
    intro J hJ
    have hj := checkedReduction_edges (fun J => (inner J).value) I hv J hJ
    have hn := checkedReduction_vertices (fun J => (inner J).value) I hv J hJ
    by_cases hz : J.m = 0
    · rw [costCapacityModel_work_empty solve J _ _ hz]
      omega
    · have hw := costCapacityModel_work solve J (max C 1) (scalingCapacityBudget I U)
        (Nat.pos_of_ne_zero hz)
      have he := Nat.clog_mono_right (b := 2) (Nat.add_le_add_right hj 1)
      have hp := Nat.mul_le_mul_right L
        (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul_left 1000000000 hj)
            (Nat.add_le_add_right he 1))
          (Nat.add_le_add_right (Nat.add_le_add_right he (Nat.clog 2 (scalingCapacityBudget I U + 1))) 1))
      have hEq : 1000000000 * (3 * I.m) * B * S * L = 3000000000 * I.m * B * S * L := by ring
      change _ ≤ 1000000000 * (3 * I.m) * B * S * L at hp
      rw [hEq] at hp
      change (inner J).work ≤ 1000000000 * J.m * (Nat.clog 2 (J.m + 1) + 1) *
        (Nat.clog 2 (J.m + 1) + Nat.clog 2 (scalingCapacityBudget I U + 1) + 1) * L + J.n at hw
      exact le_trans hw (by omega)
  have hw := CallResult.expand_work inner r _ hi
  have hr := checkedReduction_work (fun J => (inner J).value) I hv
  have hc := checkedReduction_calls (fun J => (inner J).value) I hv
  have hp := Nat.mul_le_mul_right (3000000000 * I.m * B * S * L + I.n + 1) hc
  unfold generalScalingModel
  rw [checkedMeasured_work]
  change (CallResult.expand inner r).work ≤ 7000000000 * I.m * B * S * L + 82 * I.n
  change r.work ≤ 80 * (I.m + I.n) at hr
  change r.calls.length * _ ≤ _ at hp
  simp only [Nat.mul_assoc, Nat.mul_add] at hw hp ⊢
  omega

end MinCostFlow.Scaling.FlowReduction
