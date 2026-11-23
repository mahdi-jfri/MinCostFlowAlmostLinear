module

public import MinCostFlow.Chain.Ordered.Algorithm2Facts
public import MinCostFlow.Chain.Ordered.Lemma5_11

/-!
# The renaming of internal names at a rebuild of level `0`

A rebuild of level `0` renames the edges of the new level-`0` graph `G₀'` to `0, …, |E| - 1`
(`Ordered.updateLoop`), and Algorithm 2 renames its maps between external and internal names with
it (`level0E2I`, `level0I2E`, `level0NF`). This file proves what the proofs about Algorithm 2 use:

* `firstRebuiltLevel_eq_some_zero_iff`, `update_rebuildCount_zero`, `level0Rebuilt_update_iff`:
  Algorithm 2 sees a rebuild of level `0` exactly when level `0` passed its threshold.
* `FreshInv.compact`: the fresh-name invariant moves to the renamed graph and maps.
* `update_freshInv_renamed`: after `algorithm1_update`, the level-`0` graph, lengths and gradients
  of the chain match the external ones through the renamed maps.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section Rebuilt

/-- The first rebuilt level is `0` exactly when the rebuild count of level `0` grew. -/
lemma firstRebuiltLevel_eq_some_zero_iff {d : ℕ} (hd : 0 < d) (oldReb newReb : ℕ → ℕ) :
    firstRebuiltLevel d oldReb newReb = some 0 ↔ oldReb 0 < newReb 0 := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_lt hd
  unfold firstRebuiltLevel
  rw [show 0 + d' + 1 = d' + 1 by omega, List.range_succ_eq_map, List.find?_cons]
  by_cases h : oldReb 0 < newReb 0
  · simp [h]
  · simp only [h, decide_false, iff_false]
    intro hfind
    have hmem := List.mem_of_find?_eq_some hfind
    simp at hmem

private lemma updateLoop_rebuildCount_zero (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.rebuildCount 0 =
        (if idx = 0 ∧ intRebuildThreshold P N₀ 0 < st.updCount 0 + curU.length then
          st.rebuildCount 0 + 1 else st.rebuildCount 0)
  | 0, idx, st, curG, curU, _, hsum => by
    have hne0 : idx ≠ 0 := by have := P.hd; omega
    dsimp only [updateLoop]
    by_cases hU : curU = []
    · simp [hU, hne0]
    · simp [hU, hne0]
  | rem + 1, idx, st, curG, curU, curEncAcc, hsum => by
    dsimp only [updateLoop]
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · simp only [hOver, ↓reduceIte]
      have hlt : idx < P.d := by omega
      dsimp only [algorithm1_rebuild]
      simp only [hlt, ↓reduceDIte]
      by_cases h0 : idx = 0
      · subst h0; simp [hOver]
      · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
        simp [h0, hne0]
    · simp only [hOver, ↓reduceIte]
      rw [updateLoop_rebuildCount_zero T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ _ (by omega)]
      have hOver0 : ¬ (idx = 0 ∧ intRebuildThreshold P N₀ 0 < st.updCount 0 + curU.length) := by
        rintro ⟨rfl, h⟩; exact hOver h
      simp [hOver0]

/-- The rebuild count of level `0` after `algorithm1_update` grows by one exactly when level `0`
passed its threshold. -/
lemma update_rebuildCount_zero (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (st : ChainState T P) (U : List Update) (g' ℓ' : ℕ → ℝ) :
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount 0 =
      (if intRebuildThreshold P N₀ 0 < st.updCount 0 + U.length then st.rebuildCount 0 + 1
       else st.rebuildCount 0) := by
  dsimp only [algorithm1_update]
  have h := updateLoop_rebuildCount_zero T L TP P N₀ ℓ' g' P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U) (Nat.zero_add P.d)
  simpa using h

/-- Algorithm 2 renames its internal names (`level0Rebuilt`) exactly when level `0` of the chain
passed its threshold in `algorithm1_update`. -/
lemma level0Rebuilt_update_iff (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (st : ChainState T P) (U : List Update) (g' ℓ' : ℕ → ℝ) :
    level0Rebuilt P.d st.rebuildCount (algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount =
      decide (intRebuildThreshold P N₀ 0 < st.updCount 0 + U.length) := by
  unfold level0Rebuilt
  congr 1
  rw [firstRebuiltLevel_eq_some_zero_iff P.hd, update_rebuildCount_zero]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- If `algorithm1_update` leaves the rebuild count of level `0` unchanged, level `0` stayed below
its threshold, so no renaming happened. -/
lemma update_not_over_of_rebuildCount_eq (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (st : ChainState T P) (U : List Update) (g' ℓ' : ℕ → ℝ)
    (h : (algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount 0 = st.rebuildCount 0) :
    ¬ intRebuildThreshold P N₀ 0 < st.updCount 0 + U.length := by
  intro hOver
  rw [update_rebuildCount_zero, ite_eq_left hOver] at h
  omega

/-- If level `0` is not the first rebuilt level, Algorithm 2 does not rename. -/
lemma level0Rebuilt_eq_false {d : ℕ} {oldReb newReb : ℕ → ℕ}
    (h : firstRebuiltLevel d oldReb newReb ≠ some 0) : level0Rebuilt d oldReb newReb = false := by
  unfold level0Rebuilt
  simp [h]

end Rebuilt

section Fresh

/-- The fresh-name invariant moves to the renamed graph `int.compact`: external edge `e` gets the
internal name `compactRank int.E (e2i e)`, internal name `j` belongs to the external edge
`i2e (compactUnrank int.E j)`, and the next fresh name is `|E(int)|`. -/
lemma _root_.MinCostFlow.Chain.FreshInv.compact {ext int : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv ext int e2i i2e nf) :
    FreshInv ext int.compact (fun e => compactRank int.E (e2i e))
      (fun j => i2e (compactUnrank int.E j)) int.m where
  hV := hF.hV
  hE := by
    rw [compact_E, ← image_compactRank, hF.hE, Finset.image_image]
    rfl
  hLeft := fun e he => by
    have hmem : e2i e ∈ int.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i he
    simp only [compactUnrank_rank hmem]
    exact hF.hLeft e he
  hRight := fun j hj => by
    have hmem := compactUnrank_mem_of_mem_compact hj
    obtain ⟨h1, h2⟩ := hF.hRight _ hmem
    refine ⟨?_, h2⟩
    simp only [h1]
    exact compactRank_unrank (by simpa using hj)
  hTail := fun e he => by
    have hmem : e2i e ∈ int.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i he
    rw [compact_tail, compactUnrank_rank hmem]
    exact hF.hTail e he
  hHead := fun e he => by
    have hmem : e2i e ∈ int.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i he
    rw [compact_head, compactUnrank_rank hmem]
    exact hF.hHead e he
  hLtFresh := fun j hj => (mem_compact_E int).mp hj

/-- After `translateBatch` and `algorithm1_update`, the level-`0` graph of the chain matches the
external graph through the maps of Algorithm 2 after the renaming (`level0E2I`, `level0I2E`,
`level0NF`), and the chain's lengths and gradients are the external ones read through
`level0I2E`. -/
lemma update_freshInv_renamed (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    {extG' : MGraph} {e2i' i2e' : ℕ → ℕ} {nf' : ℕ} {U_int : List Update} (g ℓ : ℕ → ℝ)
    (hF : FreshInv extG' ((st.G 0).applyBatch U_int) e2i' i2e' nf') :
    let ch1 := (algorithm1_update T L TP P N₀ st U_int (fun e' => g (i2e' e'))
      (fun e' => ℓ (i2e' e'))).1
    let ren := level0Rebuilt P.d st.rebuildCount ch1.rebuildCount
    let G₀' := (st.G 0).applyBatch U_int
    FreshInv extG' (ch1.G 0) (level0E2I ren G₀' e2i') (level0I2E ren G₀' i2e')
        (level0NF ren G₀' nf') ∧
      ch1.ℓ = (fun e' => ℓ (level0I2E ren G₀' i2e' e')) ∧
      ch1.g = (fun e' => g (level0I2E ren G₀' i2e' e')) := by
  intro ch1 ren G₀'
  have hren : ren = decide (intRebuildThreshold P N₀ 0 < st.updCount 0 + U_int.length) :=
    level0Rebuilt_update_iff T L TP P N₀ st U_int _ _
  have hG := update_G0_ℓ T L TP P N₀ st U_int (fun e' => g (i2e' e')) (fun e' => ℓ (i2e' e'))
  rw [hG.1, hG.2.1, hG.2.2.1, hren]
  unfold level0E2I level0I2E level0NF
  by_cases hOver : intRebuildThreshold P N₀ 0 < st.updCount 0 + U_int.length
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [hOver, ↓reduceIte, decide_true]
    · exact hF.compact
    all_goals rfl
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [hOver, ↓reduceIte, decide_false, Bool.false_eq_true]
    exact hF

/-- After `algorithm1_update`, the level-`0` lengths of the chain lie in `[e^{-Λ}, e^Λ]` if the new
lengths do on `(st.G 0).applyBatch U`: the renaming only permutes the edges. -/
lemma update_lenInRange (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) {Λ : ℝ} (h : LenInRange Λ ((st.G 0).applyBatch U) ℓ') :
    LenInRange Λ ((algorithm1_update T L TP P N₀ st U g' ℓ').1.G 0)
      (algorithm1_update T L TP P N₀ st U g' ℓ').1.ℓ := by
  have hG := update_G0_ℓ T L TP P N₀ st U g' ℓ'
  rw [hG.1, hG.2.1]
  split_ifs
  · exact h.compact
  · exact h

end Fresh

end MinCostFlow.Chain.Ordered
