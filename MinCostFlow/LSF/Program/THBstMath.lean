module

public import MinCostFlow.LSF.AuxiliaryTree

/-!
# The balanced search tree of a chain, on array positions

Inside a heavy chain, `T_H` hangs the chain below its top as a balanced binary search tree
(`bstParentWith`, `bstDepth`). The program stores the chain in an array `A` and searches by
positions: the segment `[lo, lo + len)` has its middle at `lo + len / 2`. `bstIdx` is this search,
and `bstIdx_spec` shows that it gives the same parent and depth as `bstParentWith` and
`bstDepth` on the list `bstSeg A lo len` of the stored vertices, when `A` takes distinct values
on the segment.
-/

@[expose] public section

namespace MinCostFlow.LSF

/-- The stored vertices `A lo, …, A (lo + len - 1)`. -/
def bstSeg (A : ℕ → ℕ) (lo len : ℕ) : List ℕ := (List.range' lo len).map A

/-- The search for position `lo + j` in the segment `[lo, lo + len)`: the parent vertex and the
depth. -/
def bstIdx (above : ℕ) (A : ℕ → ℕ) (lo len j : ℕ) : ℕ × ℕ :=
  if h : len = 0 then (above, 0)
  else if j = len / 2 then (above, 0)
  else if j < len / 2 then
    ((bstIdx (A (lo + len / 2)) A lo (len / 2) j).1,
      (bstIdx (A (lo + len / 2)) A lo (len / 2) j).2 + 1)
  else
    ((bstIdx (A (lo + len / 2)) A (lo + len / 2 + 1) (len - len / 2 - 1) (j - len / 2 - 1)).1,
      (bstIdx (A (lo + len / 2)) A (lo + len / 2 + 1) (len - len / 2 - 1) (j - len / 2 - 1)).2 + 1)
termination_by len
decreasing_by
  · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
  · omega

lemma bstSeg_length (A : ℕ → ℕ) (lo len : ℕ) : (bstSeg A lo len).length = len := by
  simp [bstSeg]

lemma bstSeg_getElem (A : ℕ → ℕ) (lo len k : ℕ) (hk : k < (bstSeg A lo len).length) :
    (bstSeg A lo len)[k] = A (lo + k) := by
  simp [bstSeg, List.getElem_range']

lemma bstSeg_take (A : ℕ → ℕ) (lo len m : ℕ) (hm : m ≤ len) :
    (bstSeg A lo len).take m = bstSeg A lo m := by
  unfold bstSeg
  rw [← List.map_take, List.take_range'_of_length_ge hm]

lemma bstSeg_drop (A : ℕ → ℕ) (lo len m : ℕ) :
    (bstSeg A lo len).drop m = bstSeg A (lo + m) (len - m) := by
  unfold bstSeg
  rw [← List.map_drop]
  simp [List.drop_range']

lemma mem_bstSeg {A : ℕ → ℕ} {lo len u : ℕ} :
    u ∈ bstSeg A lo len ↔ ∃ k < len, A (lo + k) = u := by
  unfold bstSeg
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [List.mem_range'_1] at ha
    exact ⟨a - lo, by omega, by rw [show lo + (a - lo) = a by omega]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨lo + k, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩

/-- `bstIdx` is `bstParentWith` and `bstDepth` on positions. -/
theorem bstIdx_spec (A : ℕ → ℕ) :
    ∀ len above lo j, j < len →
      (∀ a < len, ∀ b < len, A (lo + a) = A (lo + b) → a = b) →
      bstParentWith above (bstSeg A lo len) (A (lo + j)) = (bstIdx above A lo len j).1 ∧
      bstDepth (bstSeg A lo len) (A (lo + j)) = (bstIdx above A lo len j).2 := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
    intro above lo j hj hinj
    have hlen0 : len ≠ 0 := by omega
    have hL : (bstSeg A lo len).length ≠ 0 := by rw [bstSeg_length]; exact hlen0
    have hm : len / 2 < len := Nat.div_lt_self (by omega) (by decide)
    have hrt : (bstSeg A lo len)[(bstSeg A lo len).length / 2]'(Nat.div_lt_self
        (Nat.pos_of_ne_zero hL) (by decide)) = A (lo + len / 2) := by
      rw [bstSeg_getElem]; simp [bstSeg_length]
    rw [bstParentWith, bstDepth, bstIdx]
    simp only [hL, hlen0, dite_false, hrt]
    by_cases hjm : j = len / 2
    · subst hjm
      simp
    · have hne : A (lo + j) ≠ A (lo + len / 2) := fun h => hjm (hinj _ hj _ hm h)
      simp only [hne, hjm, ite_false]
      have hlenm : (bstSeg A lo len).length / 2 = len / 2 := by rw [bstSeg_length]
      rw [hlenm]
      by_cases hjlt : j < len / 2
      · have hmem : A (lo + j) ∈ (bstSeg A lo len).take (len / 2) := by
          rw [bstSeg_take _ _ _ _ (by omega), mem_bstSeg]
          exact ⟨j, hjlt, rfl⟩
        simp only [hmem, ite_true, hjlt]
        rw [bstSeg_take _ _ _ _ (by omega)]
        obtain ⟨h1, h2⟩ := ih (len / 2) hm (A (lo + len / 2)) lo j hjlt
          (fun a ha b hb hab => hinj a (by omega) b (by omega) hab)
        exact ⟨h1, by rw [h2]; omega⟩
      · have hnmem : A (lo + j) ∉ (bstSeg A lo len).take (len / 2) := by
          rw [bstSeg_take _ _ _ _ (by omega), mem_bstSeg]
          rintro ⟨k, hk, hkj⟩
          have := hinj k (by omega) j hj hkj
          omega
        simp only [hnmem, ite_false, hjlt]
        rw [bstSeg_drop]
        have hj' : A (lo + j) = A (lo + (len / 2 + 1) + (j - len / 2 - 1)) := by
          congr 1; omega
        rw [hj']
        obtain ⟨h1, h2⟩ := ih (len - (len / 2 + 1)) (by omega) (A (lo + len / 2))
          (lo + (len / 2 + 1)) (j - len / 2 - 1) (by omega)
          (fun a ha b hb hab => by
            have := hinj (len / 2 + 1 + a) (by omega) (len / 2 + 1 + b) (by omega)
              (by
                rw [show lo + (len / 2 + 1 + a) = lo + (len / 2 + 1) + a by omega,
                  show lo + (len / 2 + 1 + b) = lo + (len / 2 + 1) + b by omega]
                exact hab)
            omega)
        refine ⟨?_, ?_⟩
        · rw [h1, show len - (len / 2 + 1) = len - len / 2 - 1 by omega,
            show lo + (len / 2 + 1) = lo + len / 2 + 1 by omega]
        · rw [h2, show len - (len / 2 + 1) = len - len / 2 - 1 by omega,
            show lo + (len / 2 + 1) = lo + len / 2 + 1 by omega]
          omega

/-- `bstIdx` commutes with a map applied to the stored values. -/
theorem bstIdx_map (g : ℕ → ℕ) (A : ℕ → ℕ) :
    ∀ len above lo j, bstIdx (g above) (g ∘ A) lo len j =
      (g (bstIdx above A lo len j).1, (bstIdx above A lo len j).2) := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
    intro above lo j
    rw [bstIdx.eq_def (g above) (g ∘ A) lo len j, bstIdx.eq_def above A lo len j]
    by_cases h0 : len = 0
    · simp [h0]
    · simp only [h0, dite_false]
      split_ifs with h1 h2
      · rfl
      · have := ih (len / 2) (Nat.div_lt_self (by omega) (by decide)) (A (lo + len / 2)) lo j
        simp only [Function.comp] at this ⊢
        rw [this]
      · have := ih (len - len / 2 - 1) (by omega) (A (lo + len / 2)) (lo + len / 2 + 1)
          (j - len / 2 - 1)
        simp only [Function.comp] at this ⊢
        rw [this]

end MinCostFlow.LSF

end
