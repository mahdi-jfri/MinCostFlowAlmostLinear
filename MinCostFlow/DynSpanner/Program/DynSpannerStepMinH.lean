module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepUH
public import MinCostFlow.DynSpanner.Program.DynSpannerDelAll

/-!
# The words `minH` after a rebuild of level `j`

The state invariant (`DynSpannerStateAt`) asks that `minH[e]` is one plus the smallest level that
contains `e`, and `0` for an edge outside `H`. A rebuild of level `j` changes these words in two
passes: `dsClearBucketsStmt` sets `minH[e] := 0` for the edges whose smallest level is at least
`j` (the words with `minH[e] ≥ j + 1`), and then `dsFillLevelStmt` sets `minH[e] := j + 1` for
each edge of `J̃` whose word is now `0`. This file shows that the result is again one plus the
smallest level, now for the levels `rebuildLevels H_mid H_j G' j` (`minHRebuild_spec`).
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

@[expose] public section

/-- The words after the clearing pass. -/
def minHClear (j : ℕ) (m : ℕ → ℕ) (e : ℕ) : ℕ := if j + 1 ≤ m e then 0 else m e

/-- The words after the filling pass with the edges `Jt`. -/
def minHRebuild (j : ℕ) (Jt : Finset ℕ) (m : ℕ → ℕ) (e : ℕ) : ℕ :=
  if e ∈ Jt ∧ minHClear j m e = 0 then j + 1 else minHClear j m e

/-- Under the old invariant for the levels `H_mid` and the edge set `E` of `H`, the words after the
two passes are one plus the smallest level of `rebuildLevels H_mid H_j G' j` that contains the
edge, and `0` for the edges outside the new edge set `unionEdgesLt H_mid j ∪ E(H_j)`. -/
theorem minHRebuild_spec {L j : ℕ} (hj : j ≤ L) (H_mid : Fin (L + 1) → MGraph) (Hj G' : MGraph)
    (E : Finset ℕ) (m : ℕ → ℕ) (hm0 : ∀ e, m e = 0 ↔ e ∉ E)
    (hmin : ∀ e ∈ E, ∃ i : Fin (L + 1), m e = i.1 + 1 ∧ e ∈ (H_mid i).E ∧
      ∀ k : Fin (L + 1), k.1 < i.1 → e ∉ (H_mid k).E)
    (hsub : unionEdgesLt H_mid j ⊆ E) :
    (∀ e, minHRebuild j Hj.E m e = 0 ↔ e ∉ unionEdgesLt H_mid j ∪ Hj.E) ∧
    ∀ e ∈ unionEdgesLt H_mid j ∪ Hj.E, ∃ i : Fin (L + 1),
      minHRebuild j Hj.E m e = i.1 + 1 ∧ e ∈ (rebuildLevels H_mid Hj G' j i).E ∧
      ∀ k : Fin (L + 1), k.1 < i.1 → e ∉ (rebuildLevels H_mid Hj G' j k).E := by
  -- An edge is in a level below `j` exactly when it is in `H` with `minH ≤ j`.
  have hlow : ∀ e, e ∈ unionEdgesLt H_mid j ↔ e ∈ E ∧ m e ≤ j ∧ m e ≠ 0 := by
    intro e
    constructor
    · intro he
      have heE := hsub he
      obtain ⟨i, hi, hiE, hfirst⟩ := hmin e heE
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and] at he
      obtain ⟨k, hk, hkE⟩ := he
      have : i.1 ≤ k.1 := by
        by_contra h
        exact hfirst k (by omega) hkE
      exact ⟨heE, by omega, by omega⟩
    · rintro ⟨heE, hle, _⟩
      obtain ⟨i, hi, hiE, _⟩ := hmin e heE
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, by omega, hiE⟩
  -- The value after the two passes.
  have hval : ∀ e, minHRebuild j Hj.E m e =
      if e ∈ unionEdgesLt H_mid j then m e else if e ∈ Hj.E then j + 1 else 0 := by
    intro e
    by_cases hl : e ∈ unionEdgesLt H_mid j
    · obtain ⟨_, hle, hne⟩ := (hlow e).mp hl
      have hc : minHClear j m e = m e := by simp only [minHClear]; split_ifs <;> omega
      simp only [minHRebuild, hc, hl, ite_true]
      split_ifs with h
      · omega
      · rfl
    · have hc : minHClear j m e = 0 := by
        simp only [minHClear]
        split_ifs with h
        · rfl
        · by_contra hne
          exact hl ((hlow e).mpr ⟨(by
            by_contra hE; exact hne ((hm0 e).mpr hE)), by omega, hne⟩)
      simp only [minHRebuild, hc, hl, ite_false, and_true]
  refine ⟨fun e => ?_, fun e he => ?_⟩
  · rw [hval e, Finset.mem_union]
    by_cases hl : e ∈ unionEdgesLt H_mid j
    · obtain ⟨_, _, hne⟩ := (hlow e).mp hl
      simp only [hl, ite_true, true_or, not_true_eq_false, iff_false]
      exact hne
    · by_cases hJ : e ∈ Hj.E
      · simp [hl, hJ]
      · simp [hl, hJ]
  · rw [hval e]
    by_cases hl : e ∈ unionEdgesLt H_mid j
    · obtain ⟨heE, hle, hne⟩ := (hlow e).mp hl
      obtain ⟨i, hi, hiE, hfirst⟩ := hmin e heE
      have hij : i.1 < j := by omega
      refine ⟨i, by simp only [hl, ite_true]; exact hi, ?_, fun k hk => ?_⟩
      · simp only [rebuildLevels, hij, ite_true]; exact hiE
      · simp only [rebuildLevels, show k.1 < j by omega, ite_true]; exact hfirst k hk
    · have hJ : e ∈ Hj.E := by
        rcases Finset.mem_union.mp he with h | h
        · exact absurd h hl
        · exact h
      refine ⟨⟨j, by omega⟩, by simp [hl, hJ], ?_, fun k hk => ?_⟩
      · simp only [rebuildLevels, lt_irrefl, ite_false, ite_true]; exact hJ
      · simp only [rebuildLevels, show k.1 < j from hk, ite_true]
        intro hk'
        apply hl
        simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨k, hk, hk'⟩


/-- The two passes in memory compute `minHRebuild`. Here `mem₀` is the memory before the passes,
`mem₁` after `dsClearBucketsStmt` on the levels `j ≤ i ≤ L`, and `mem₂` after `dsFillLevelStmt`
on the list `es` of the edges of `J̃`. The bucket `B i` holds the edges with `minH[e] = i + 1`. -/
theorem minH_after_passes {eCap j L minH : ℕ} {mem₀ mem₁ mem₂ : ℕ → ℕ} (B : ℕ → List ℕ)
    (es : List ℕ)
    (hB : ∀ i e, j ≤ i → i ≤ L → (e ∈ B i ↔ e < eCap ∧ mem₀ (minH + e) = i + 1))
    (hbig : ∀ e < eCap, mem₀ (minH + e) ≤ L + 1)
    (h1z : ∀ x ∈ bucketsCat B j (L + 1 - j), mem₁ (minH + x) = 0)
    (h1fr : ∀ e < eCap, e ∉ bucketsCat B j (L + 1 - j) → mem₁ (minH + e) = mem₀ (minH + e))
    (h2set : ∀ e ∈ es.filter (fun e => decide (mem₁ (minH + e) = 0)), mem₂ (minH + e) = j + 1)
    (h2fr : ∀ e < eCap, e ∉ es.filter (fun e => decide (mem₁ (minH + e) = 0)) →
      mem₂ (minH + e) = mem₁ (minH + e)) :
    ∀ e < eCap, mem₂ (minH + e) = minHRebuild j es.toFinset (fun e => mem₀ (minH + e)) e := by
  intro e heC
  have hcat : e ∈ bucketsCat B j (L + 1 - j) ↔ j + 1 ≤ mem₀ (minH + e) := by
    simp only [bucketsCat, List.mem_flatMap, List.mem_range']
    constructor
    · rintro ⟨i, ⟨k, hk, rfl⟩, hi⟩
      have := ((hB (j + 1 * k) e (by omega) (by omega)).mp hi).2
      omega
    · intro h
      have := hbig e heC
      refine ⟨mem₀ (minH + e) - 1, ⟨mem₀ (minH + e) - 1 - j, by omega, by omega⟩, ?_⟩
      exact (hB _ e (by omega) (by omega)).mpr ⟨heC, by omega⟩
  have h1 : mem₁ (minH + e) = minHClear j (fun e => mem₀ (minH + e)) e := by
    simp only [minHClear]
    split_ifs with h
    · exact h1z e (hcat.mpr h)
    · exact h1fr e heC (fun h' => h (hcat.mp h'))
  simp only [minHRebuild]
  by_cases hA : e ∈ es.filter (fun e => decide (mem₁ (minH + e) = 0))
  · have hA' := List.mem_filter.mp hA
    simp only [decide_eq_true_eq] at hA'
    rw [h2set e hA]
    split_ifs with h
    · rfl
    · exact absurd ⟨List.mem_toFinset.mpr hA'.1, h1 ▸ hA'.2⟩ h
  · rw [h2fr e heC hA, h1]
    split_ifs with h
    · exfalso
      exact hA (List.mem_filter.mpr ⟨List.mem_toFinset.mp h.1, by simp [h1, h.2]⟩)
    · rfl


/-- The buckets after the two passes: the buckets below `j` stay, bucket `j` holds the edges of
`es` (the edges of `J̃`) whose word was `0` after the clearing pass (`dsFillLevelStmt` puts them
in reverse order), and the buckets above `j` are empty. Each bucket `i` then holds the edges of the
new edge set whose new word is `i + 1`. -/
theorem bucketRebuild_spec {L j : ℕ} (hj : j ≤ L) (H_mid : Fin (L + 1) → MGraph)
    (E : Finset ℕ) (m : ℕ → ℕ) (hm0 : ∀ e, m e = 0 ↔ e ∉ E)
    (hmin : ∀ e ∈ E, ∃ i : Fin (L + 1), m e = i.1 + 1 ∧ e ∈ (H_mid i).E ∧
      ∀ k : Fin (L + 1), k.1 < i.1 → e ∉ (H_mid k).E)
    (hsub : unionEdgesLt H_mid j ⊆ E) (B : ℕ → List ℕ)
    (hB : ∀ i ≤ L, ∀ e, e ∈ B i ↔ e ∈ E ∧ m e = i + 1) (es : List ℕ) :
    ∀ i ≤ L, ∀ e,
      e ∈ (if i < j then B i
        else if i = j then (es.filter fun e => decide (minHClear j m e = 0)).reverse else []) ↔
      e ∈ unionEdgesLt H_mid j ∪ es.toFinset ∧ minHRebuild j es.toFinset m e = i + 1 := by
  have hlow : ∀ e, e ∈ unionEdgesLt H_mid j ↔ e ∈ E ∧ m e ≤ j ∧ m e ≠ 0 := by
    intro e
    constructor
    · intro he
      have heE := hsub he
      obtain ⟨i, hi, hiE, hfirst⟩ := hmin e heE
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and] at he
      obtain ⟨k, hk, hkE⟩ := he
      have : i.1 ≤ k.1 := by
        by_contra h
        exact hfirst k (by omega) hkE
      exact ⟨heE, by omega, by omega⟩
    · rintro ⟨heE, hle, _⟩
      obtain ⟨i, hi, hiE, _⟩ := hmin e heE
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, by omega, hiE⟩
  have hclear : ∀ e, minHClear j m e = if e ∈ unionEdgesLt H_mid j then m e else 0 := by
    intro e
    by_cases hl : e ∈ unionEdgesLt H_mid j
    · obtain ⟨_, hle, hne⟩ := (hlow e).mp hl
      simp only [minHClear, hl, ite_true]; split_ifs <;> omega
    · simp only [minHClear, hl, ite_false]
      split_ifs with h
      · rfl
      · by_contra hne
        exact hl ((hlow e).mpr ⟨(by by_contra hE; exact hne ((hm0 e).mpr hE)), by omega, hne⟩)
  intro i hi e
  by_cases hl : e ∈ unionEdgesLt H_mid j
  · obtain ⟨heE, hle, hne⟩ := (hlow e).mp hl
    have hv : minHRebuild j es.toFinset m e = m e := by
      simp only [minHRebuild, hclear e, hl, ite_true]
      by_cases h : e ∈ es.toFinset ∧ m e = 0
      · exact absurd h.2 hne
      · simp only [h, ite_false]
    rw [hv]
    by_cases h1 : i < j
    · simp only [h1, ite_true, hB i hi, Finset.mem_union, hl, true_or, true_and]
      exact ⟨fun h => h.2, fun h => ⟨heE, h⟩⟩
    · by_cases h2 : i = j
      · subst h2
        simp only [h1, ite_false, ite_true, List.mem_reverse, List.mem_filter, hclear e, hl,
          decide_eq_true_eq]
        constructor
        · rintro ⟨_, h⟩; exact absurd h hne
        · rintro ⟨_, h⟩; omega
      · simp only [h1, h2, ite_false, List.not_mem_nil, false_iff, not_and]
        intro _; omega
  · have hv : minHRebuild j es.toFinset m e = if e ∈ es.toFinset then j + 1 else 0 := by
      simp only [minHRebuild, hclear e, hl, ite_false, and_true]
    rw [hv]
    by_cases h1 : i < j
    · simp only [h1, ite_true, hB i hi]
      constructor
      · rintro ⟨heE, hme⟩
        exact absurd ((hlow e).mpr ⟨heE, by omega, by omega⟩) hl
      · rintro ⟨_, h⟩
        by_cases hes : e ∈ es.toFinset
        · simp only [hes, ite_true] at h; omega
        · simp only [hes, ite_false] at h; omega
    · by_cases h2 : i = j
      · subst h2
        by_cases hes : e ∈ es
        · simp [List.mem_reverse, List.mem_filter, hclear e, hl, hes]
        · simp [List.mem_reverse, List.mem_filter, hclear e, hl, hes]
      · simp only [h1, h2, ite_false, List.not_mem_nil, false_iff, not_and]
        intro _
        by_cases hes : e ∈ es.toFinset
        · simp only [hes, ite_true]; omega
        · simp only [hes, ite_false]; omega
end

end MinCostFlow.DynSpanner.Program
