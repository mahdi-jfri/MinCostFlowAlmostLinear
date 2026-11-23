module

public import MinCostFlow.Chain.Ordered.Algorithm2Uncond
public import MinCostFlow.Chain.Ordered.RebuildCollapse
public import MinCostFlow.Chain.Ordered.RenameFacts

/-!
# A bound on the internal names of Algorithm 2

Algorithm 2 gives each inserted edge a fresh internal name `nextFresh`, and `nextFresh` grows by
one per insertion. A rebuild of level `0` renames the live internal edges to `0, …, |E| - 1` and
sets `nextFresh` to `|E|` (`level0NF`). Level `0` is rebuilt as soon as it has absorbed more than
`intRebuildThreshold P N₀ 0` updates since its last rebuild. So `nextFresh` never exceeds its
start value, or `M₀`, by more than that threshold.

* `translateBatch_nf_le`: translating a batch `U` raises `nextFresh` by at most `|U|`.
* `alg2_nextFresh_inv_with`: on every reached state, `nextFresh` is at most
  `max (sup E(G₀) + 1) M₀` plus the update count of level `0`, and that count is at most the
  threshold.
* `alg2_nextFresh_le_with`: the bound on reached states.
* `alg2_translate_nextFresh_le_with`: during an update with a batch of length at most `2 * m`,
  every internal name in use (they are all below the `nextFresh` after `translateBatch`) is below
  that bound plus `2 * m`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- Translating a batch `U` raises the next fresh name by at most `|U|`: only insertions use a
new name, one each. -/
lemma translateBatch_nf_le :
    ∀ (U : List Update) (ext : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      (translateBatch ext e2i i2e nf U).2.2.2.1 ≤ nf + U.length
  | [], _, _, _, _ => by simp [translateBatch]
  | u :: rest, ext, e2i, i2e, nf => by
    have h1 : (translateUpdate ext e2i i2e nf u).2.2.2.1 ≤ nf + 1 := by
      cases u <;> simp [translateUpdate]
    rcases h : translateUpdate ext e2i i2e nf u with ⟨ext1, e2i1, i2e1, nf1, u'⟩
    rw [h] at h1
    have ih := translateBatch_nf_le rest ext1 e2i1 i2e1 nf1
    rcases h' : translateBatch ext1 e2i1 i2e1 nf1 rest with ⟨extF, e2iF, i2eF, nfF, rest'⟩
    rw [h'] at ih
    simp only [translateBatch, h, h', List.length_cons]
    dsimp only at h1 ih
    omega

/-- The bound that `nextFresh` keeps: the larger of the first fresh name and `M₀`. -/
def alg2NameBase (cfg : Alg2Config) (G₀ : MGraph) : ℕ :=
  max (G₀.E.sup id + 1) cfg.P.M₀

/-- On every reached state of Algorithm 2, `nextFresh` is at most `alg2NameBase` plus the update
count of level `0`, and that count is at most `intRebuildThreshold P N₀ 0`. The hypotheses are
those of `algorithm2_uncond_preserves_with`, which give the fresh-name invariant and the bound
`m ≤ M₀` used at a rebuild of level `0`. -/
theorem alg2_nextFresh_inv_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t ≤ T,
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).nextFresh ≤
          alg2NameBase cfg (D.G 0) +
            (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).chain.updCount 0 ∧
        (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).chain.updCount 0 ≤
          intRebuildThreshold cfg.P cfg.N₀ 0 := by
  have hMain := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdge hLen hmBound
    hnBound).1
  intro t
  induction t with
  | zero =>
    intro _
    have h0 := initialize_updCount_zero cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.G 0)
      (D.ℓ 0) (D.g 0)
    simp only [minRatioFailState, algorithm2_dsWith, algorithm2_init, h0, add_zero, zero_le,
      and_true, alg2NameBase]
    exact le_max_left _ _
  | succ t ih =>
    intro ht
    have ht_le : t ≤ T := Nat.le_of_succ_le ht
    obtain ⟨ihF, ihU⟩ := ih ht_le
    set st : Alg2State cfg := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    by_cases hupd : isUpdate (t + 1) = true
    · obtain ⟨_, _, _, _, hFresh, hExtG, _⟩ := hMain t ht_le
      have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht
      simp only [Nat.add_sub_cancel] at hD
      have hTB := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
        st.extToInt st.intToExt st.nextFresh hFresh (hExtG ▸ hD.1)
      have hNF := translateBatch_nf_le (D.U (t + 1)) st.extG st.extToInt st.intToExt st.nextFresh
      set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      rcases hTB with ⟨hExt', hFresh', _, _, hLenEq, _⟩
      have hStStep : minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) =
          (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1))
            (η (t + 1))).1 := by
        rw [minRatioFailState.eq_2]
        simp only [hupd, ↓reduceIte]
        rfl
      have hF := algorithm2_updateWith_fields cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1))
        (η (t + 1))
      dsimp only at hF
      set ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1
      set bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
        | none => (st.branD, st.passes)
        | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
      have hL := alg2_loopWith_preserves_counters cfg κ tb.1
        (level0E2I (level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount)
          ((st.chain.G 0).applyBatch tb.2.2.2.2) tb.2.1) (D.g (t + 1)) (D.ℓ (t + 1))
        (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1)
        ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length) le_rfl
      have hUpd0 := update_updCount_zero cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
      have hRen := level0Rebuilt_update_iff cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
      have hNext : (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)).nextFresh =
            level0NF (level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount)
              ((st.chain.G 0).applyBatch tb.2.2.2.2) tb.2.2.2.1 ∧
          (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)).chain.updCount 0 =
            ch1.updCount 0 :=
        ⟨by rw [hStStep]; exact hF.2.2.2.2, by rw [hStStep, hF.1]; exact hL.2.2⟩
      rw [hNext.1, hNext.2]
      change ch1.updCount 0 = _ at hUpd0
      change level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount = _ at hRen
      rw [hRen, hUpd0]
      unfold level0NF
      by_cases hOver : intRebuildThreshold cfg.P cfg.N₀ 0 < st.chain.updCount 0 + tb.2.2.2.2.length
      · -- A rebuild of level `0`: the new next fresh name is `|E|`, at most `M₀`.
        simp only [hOver, decide_true, ↓reduceIte, add_zero, zero_le, and_true]
        have hm : ((st.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
          rw [hFresh'.m_eq, hExt', hExtG, ← hD.2]
          exact hmBound (t + 1) ht
        exact hm.trans (le_max_right _ _)
      · -- No rebuild of level `0`: the next fresh name grew by at most `|U|`, and so did the
        -- update count of level `0`.
        simp only [hOver, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, by omega⟩
        rw [hLenEq] at hOver ⊢
        omega
    · have hdet : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
      have hEq : minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) =
          (algorithm2_detect cfg st).2 := by
        rw [minRatioFailState.eq_2]
        simp only [hdet, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [hEq]
      exact ⟨ihF, ihU⟩

/-- **The bound on `nextFresh`.** On every state that Algorithm 2 reaches in a valid history of
length `T`, the next fresh internal name is at most
`max (sup E(G₀) + 1) M₀ + intRebuildThreshold P N₀ 0`. The bound depends only on the first graph,
`M₀` and the parameters, not on `T`. -/
theorem alg2_nextFresh_le_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) (t : ℕ) (ht : t ≤ T) :
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).nextFresh ≤
      alg2NameBase cfg (D.G 0) + intRebuildThreshold cfg.P cfg.N₀ 0 := by
  obtain ⟨h1, h2⟩ := alg2_nextFresh_inv_with (η := η) κ hV hHist hEdge hLen hmBound hnBound t ht
  omega

/-- **The bound on internal names during an update.** If the batch at step `t + 1` has length at
most `2 * m`, the next fresh name after `translateBatch`, which bounds every internal name that
the update uses before the renaming, is at most the bound of `alg2_nextFresh_le_with` plus
`2 * m`. -/
theorem alg2_translate_nextFresh_le_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) (m : ℕ) (t : ℕ) (ht : t ≤ T)
    (hU : (D.U (t + 1)).length ≤ 2 * m) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    (translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))).2.2.2.1 ≤
      alg2NameBase cfg (D.G 0) + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * m := by
  intro st
  have h1 := alg2_nextFresh_le_with (η := η) κ hV hHist hEdge hLen hmBound hnBound t ht
  have h2 := translateBatch_nf_le (D.U (t + 1)) st.extG st.extToInt st.intToExt st.nextFresh
  change st.nextFresh ≤ _ at h1
  have h3 : st.nextFresh + (D.U (t + 1)).length ≤
      alg2NameBase cfg (D.G 0) + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * m := by omega
  exact h2.trans h3

end MinCostFlow.Chain.Ordered
