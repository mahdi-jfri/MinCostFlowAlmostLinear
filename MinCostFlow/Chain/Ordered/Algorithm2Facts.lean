module

public import MinCostFlow.Chain.Ordered.Traces

/-!
# Helper lemmas for Algorithm 2 with orders

This file proves structural helper lemmas for Algorithm 2 with orders
(`MinCostFlow.Chain.Ordered.Algorithm2`) and Algorithm 1 with orders
(`MinCostFlow.Chain.Ordered.Algorithm1`):

1. `translateUpdate_isEdgeUpdate` and `translateBatch_isEdgeUpdate`: fresh-ID edge translation
   preserves edge-only updates (insertions and deletions, `Bundle.IsEdgeUpdate`), so a
   `HistoryEdgeOnly` external history yields edge-only internal batches at level `0`.
2. `HistoryEdgeOnly.of_le`: restriction of `HistoryEdgeOnly` to shorter prefixes.
3. `updateLoop_rebuildCount_cases`: structural characterization of `rebuildCount` after
   `Ordered.updateLoop` (unchanged, or incremented by `1` at a unique level `iStar < P.d`).
4. `algorithm2_updateWith_eq_of_loop`: case split of `Ordered.algorithm2_updateWith` on the
   optional circulation returned by `Ordered.algorithm2_loopWith`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section EdgeOnlyTranslation

/-- Fresh-ID translation of a single update preserves `IsEdgeUpdate` (insertions and deletions). -/
lemma translateUpdate_isEdgeUpdate (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ)
    {u : Update} (hEdge : IsEdgeUpdate u) :
    IsEdgeUpdate (translateUpdate curExt e2i i2e nf u).2.2.2.2 := by
  cases u with
  | delete e => trivial
  | insert e a b => trivial
  | split v v' St Sh => exact False.elim hEdge

/-- Fresh-ID translation of a batch preserves `IsEdgeUpdate` on every update in the batch. -/
lemma translateBatch_isEdgeUpdate (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) :
    ∀ (U : List Update),
      (∀ u ∈ U, IsEdgeUpdate u) →
      ∀ u' ∈ (translateBatch curExt e2i i2e nf U).2.2.2.2, IsEdgeUpdate u'
  | [], _, u', hu' => by simp [translateBatch] at hu'
  | u :: rest, hEdge, u', hu' => by
    simp only [translateBatch, List.mem_cons] at hu'
    rcases hu' with rfl | hu'_rest
    · exact translateUpdate_isEdgeUpdate curExt e2i i2e nf (hEdge u List.mem_cons_self)
    · exact translateBatch_isEdgeUpdate _ _ _ _ rest
        (fun v hv => hEdge v (List.mem_cons_of_mem u hv)) u' hu'_rest

/-- `HistoryEdgeOnly` restricts to any prefix `T' ≤ T`. -/
lemma HistoryEdgeOnly.of_le {D : DynamicInstance} {T T' : ℕ}
    (hEdge : HistoryEdgeOnly D T) (hT' : T' ≤ T) :
    HistoryEdgeOnly D T' :=
  fun t ht1 ht2 u hu => hEdge t ht1 (le_trans ht2 hT') u hu

end EdgeOnlyTranslation

section UpdateLoopAndUpdateWith

/-- Structural property of `Ordered.updateLoop`: either `rebuildCount` is unchanged, or a unique
level `iStar < P.d` has its rebuild count incremented by `1`. -/
lemma updateLoop_rebuildCount_cases (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      idx + rem = P.d →
      let st' := (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1
      st'.rebuildCount = st.rebuildCount ∨
      ∃ iStar, idx ≤ iStar ∧ iStar < P.d ∧
        st'.rebuildCount = fun j => if j = iStar then st.rebuildCount iStar + 1 else st.rebuildCount j := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEnc _
    left
    dsimp only [updateLoop]
    split_ifs <;> rfl
  | succ rem' ih =>
    intro idx st curG curU curEnc hsum
    dsimp only [updateLoop]
    split_ifs with hTh
    · right
      refine ⟨idx, le_refl _, by omega, ?_⟩
      dsimp only [algorithm1_rebuild]
      split_ifs
      · rfl
      · omega
    · dsimp only
      rcases ih (idx + 1) _ _ _ _ (by omega) with heq | ⟨iStar, h1, h2, h3⟩
      · exact Or.inl heq
      · exact Or.inr ⟨iStar, Nat.le_of_succ_le h1, h2, h3⟩

/-- Case split of `Ordered.algorithm2_updateWith` according to whether `Ordered.algorithm2_loopWith`
returns `none` or `some Δ`. -/
lemma algorithm2_updateWith_eq_of_loop {cfg : Alg2Config} (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e'))).1
    let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    let G₀' := (st.chain.G 0).applyBatch tb.2.2.2.2
    let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let lp := algorithm2_loopWith cfg κ tb.1 (level0E2I ren G₀' tb.2.1) g' ℓ' ch1 bp1.1 bp1.2 (st.lctUpdateOps + U_ext.length)
    (lp.2.2.2.2 = none →
      algorithm2_updateWith cfg κ st U_ext g' ℓ' η =
        ({ st with
           chain := lp.1
           branD := lp.2.1
           passes := lp.2.2.1
           extG := tb.1
           extToInt := level0E2I ren G₀' tb.2.1
           intToExt := level0I2E ren G₀' tb.2.2.1
           nextFresh := level0NF ren G₀' tb.2.2.2.1
           extℓ := ℓ'
           extg := g'
           lctUpdateOps := lp.2.2.2.1
           largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2
           updateCount := st.updateCount + 1 }, none)) ∧
    (∀ Δ, lp.2.2.2.2 = some Δ →
      algorithm2_updateWith cfg κ st U_ext g' ℓ' η =
        (let inc : ℕ → ℝ := fun e => if e ∈ tb.1.E then -(η / tb.1.inner g' Δ) * Δ e else 0
         { chain := lp.1
           branD := lp.2.1
           passes := lp.2.2.1
           extG := tb.1
           extToInt := level0E2I ren G₀' tb.2.1
           intToExt := level0I2E ren G₀' tb.2.2.1
           nextFresh := level0NF ren G₀' tb.2.2.2.1
           extℓ := ℓ'
           extg := g'
           flow := fun e => st.flow e + inc e
           detectAccum := fun e => st.detectAccum e + |inc e|
           lctUpdateOps := lp.2.2.2.1
           lctDetectOps := st.lctDetectOps
           largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2
           updateCount := st.updateCount + 1 }, some Δ)) := by
  refine ⟨?_, ?_⟩
  · intro hnone
    dsimp only [algorithm2_updateWith] at hnone ⊢
    split
    · rfl
    · next opt heq => exact absurd (hnone.symm.trans heq) (by simp)
  · intro Δ hsome
    dsimp only [algorithm2_updateWith] at hsome ⊢
    split
    · next heq => exact absurd (hsome.symm.trans heq) (by simp)
    · next Δ' heq =>
      have hΔ : Δ = Δ' := Option.some.inj (hsome.symm.trans heq)
      subst hΔ
      rfl

end UpdateLoopAndUpdateWith

end MinCostFlow.Chain.Ordered
