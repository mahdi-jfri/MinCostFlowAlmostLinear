module

public import MinCostFlow.HierPaths.BuildTopDriverRun
import MinCostFlow.HierPaths.BuildTopSums

/-! # Cost of scanning all hierarchy depths

At each depth the groups partition the padded terminals. This pays for the
parent scan and the child directory together with the calls to the level procedure.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM

private theorem rangeCost_finset (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ∑ i ∈ Finset.range n, f i := by
  rw [rangeCost_zero_eq_range]
  rfl

/-- One depth costs at most its per-terminal work plus 311 steps per terminal. -/
theorem buildTopDriverStepCost_le (x b i K : ℕ) (D : BuildTopDepthInput) (factor : ℕ)
    (hcount : D.count = numGroups x b i) (hbranch : D.branch ≤ groupSize x b i)
    (hwork : ∀ g < D.count, D.work K g ≤ groupSize x b i * factor) :
    rangeCost (fun g => D.work K g + 60) 0 D.count + 9 * D.count + 20 +
        100 * (D.count * D.branch) + 122 ≤ 2 ^ x * (factor + 311) := by
  have hsize : 0 < groupSize x b i := groupSize_pos
  have htotal : D.count * groupSize x b i = 2 ^ x := by rw [hcount, numGroups_mul_groupSize]
  have hcnt : D.count ≤ 2 ^ x := by
    rw [← htotal]
    exact Nat.le_mul_of_pos_right _ hsize
  have hs : rangeCost (fun j => D.work K j + 60) 0 D.count ≤
      2 ^ x * (factor + 60) := by
    rw [rangeCost_finset]
    calc
      _ ≤ ∑ _j ∈ Finset.range D.count, groupSize x b i * (factor + 60) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Nat.mul_add]
        exact Nat.add_le_add (hwork j (Finset.mem_range.mp hj))
          (Nat.le_mul_of_pos_left _ hsize)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Nat.mul_assoc]; exact congrArg (· * (factor + 60)) htotal
  have hc := Nat.mul_le_mul_left 9 hcnt
  have hb : 100 * (D.count * D.branch) ≤ 100 * 2 ^ x :=
    Nat.mul_le_mul_left _ (htotal ▸ Nat.mul_le_mul_left _ (hbranch))
  have hp := Nat.two_pow_pos x
  rw [Nat.mul_add, show 311 = 60 + 251 by decide, Nat.mul_add]
  rw [Nat.mul_add] at hs
  have hx : 20 + 122 ≤ 2 ^ x * 142 := Nat.le_mul_of_pos_left _ hp
  rw [show 251 = 9 + 100 + 142 by decide, Nat.mul_add, Nat.mul_add]
  omega

/-- Sum the driver's machine charges using the number of terminals at each depth. -/
theorem buildTopDriverCost_le (x b n K : ℕ) (D : ℕ → BuildTopDepthInput)
    (factor : ℕ → ℕ)
    (hcount : ∀ i < n, (D i).count = numGroups x b i)
    (hbranch : ∀ i < n, (D i).branch ≤ groupSize x b i)
    (hwork : ∀ i < n, ∀ j < (D i).count,
      (D i).work K j ≤ groupSize x b i * factor i) :
    rangeCost (fun i =>
      rangeCost (fun j => (D i).work K j + 60) 0 (D i).count + 9 * (D i).count + 20 +
      100 * ((D i).count * (D i).branch) + 122) 0 n + 9 * n + 12 ≤
      2 ^ x * (∑ i ∈ Finset.range n, (factor i + 311)) + 9 * n + 12 := by
  rw [rangeCost_finset, Finset.mul_sum]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  have h := Finset.mem_range.mp hi
  exact buildTopDriverStepCost_le x b i K (D i) (factor i) (hcount i h) (hbranch i h) (hwork i h)

end MinCostFlow.HierPaths

end
