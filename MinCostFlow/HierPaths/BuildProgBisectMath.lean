module

public import MinCostFlow.HierPaths.BuildChild
import Mathlib.Data.List.Sort

/-!
# Padding a cut by scanning its vertices

To pad the smaller side to half the child size, keep all vertices on that side and
take the first missing vertices in order until the quota is spent. A left-to-right
scan needs only the remaining quota.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- Number of vertices inspected before `i` that were outside the smaller side. -/
def cutMissing (C : Finset ℕ) (i : ℕ) : ℕ :=
  ((List.range i).filter fun v => decide (v ∉ C)).length

/-- The number of padding vertices still needed when the scan reaches `i`. -/
def cutQuota (s : ℕ) (C : Finset ℕ) (i : ℕ) : ℕ :=
  (s / 2 - C.card) - cutMissing C i

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

private theorem sort_compl_eq_filter (s : ℕ) (C : Finset ℕ) :
    (Finset.range s \ C).sort (· ≤ ·) = (List.range s).filter (fun v => decide (v ∉ C)) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Finset.pairwise_sort ..
  · exact (List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h)).filter _
  · apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup ..) (List.nodup_range.filter _)).mpr
    intro v
    simp

/-- The initial padding quota is half the child size minus the smaller side size. -/
theorem cutQuota_zero (s : ℕ) (C : Finset ℕ) : cutQuota s C 0 = s / 2 - C.card := rfl

/-- Each vertex outside the smaller side consumes one unit of quota, up to saturation. -/
theorem cutQuota_succ (s : ℕ) (C : Finset ℕ) (i : ℕ) :
    cutQuota s C (i + 1) = cutQuota s C i - (if i ∈ C then 0 else 1) := by
  by_cases hi : i ∈ C <;>
    simp [cutQuota, cutMissing, List.range_succ, List.filter_append, hi, Nat.sub_sub, Nat.add_assoc]

/-- The bit written by the scan is exactly membership in the padded side. -/
theorem mem_padHalf_iff_quota {s i : ℕ} {C : Finset ℕ} (hi : i < s) :
    i ∈ padHalf s C ↔ i ∈ C ∨ 0 < cutQuota s C i := by
  by_cases hC : i ∈ C
  · simp [hC, subset_padHalf s C hC]
  simp only [padHalf, Finset.mem_union, hC, false_or, List.mem_toFinset]
  rw [sort_compl_eq_filter]
  have hm : i ∈ (List.range s).filter (fun v => decide (v ∉ C)) := by simp [hi, hC]
  rw [List.mem_take_iff_idxOf_lt hm]
  have he : s = i + 1 + (s - (i + 1)) := by omega
  have hIndex : ((List.range s).filter (fun v => decide (v ∉ C))).idxOf i = cutMissing C i := by
    conv_lhs => rw [he, List.range_add, List.range_succ, List.filter_append, List.filter_append]
    rw [List.idxOf_append_of_mem (by simp [hC]), List.idxOf_append_of_notMem (by simp)]
    simp [cutMissing, hC]
  rw [hIndex]
  unfold cutQuota
  omega

end MinCostFlow.HierPaths
