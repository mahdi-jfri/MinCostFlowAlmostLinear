module

public import MinCostFlow.MinRatio.QueryDetectPost
public import MinCostFlow.MinRatio.DetectorThreshold

/-!
# Sequential reporting and resets implement the Detect model

The proof of Theorem 5.1 (pages 29–30) searches for edges with a
nonnegative residual and resets each reported edge. The model resets
the whole reported set at once. These lemmas show that after resetting
a prefix, the ready set is exactly the original ready set minus that
prefix. Thus any order of reporting gives the same result.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Reset precisely those accounts whose names have been reported. -/
noncomputable def resetReported (account : ℕ → ℝ) (reported : Finset ℕ) (edge : ℕ) : ℝ :=
  if edge ∈ reported then 0 else account edge

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open Chain

/-- A further point reset extends the set of reset accounts. -/
theorem resetReported_insert (account : ℕ → ℝ) (reported : Finset ℕ) (edge : ℕ) :
    Function.update (resetReported account reported) edge 0 =
      resetReported account (insert edge reported) := by
  funext x
  by_cases hx : x = edge
  · subst x
    simp [resetReported]
  · simp [resetReported, hx]

/-- An edge is still ready exactly when it was ready initially and has
not been reported. The positive threshold rules out a second report
immediately after a point reset. -/
theorem detect_ready_after_report {cfg : Alg2Config} (st : Alg2State cfg)
    (hε : 0 < cfg.ε) (reported : Finset ℕ) (e : ℕ) :
    (e ∈ st.extG.E ∧ cfg.ε ≤ st.extℓ e * resetReported st.detectAccum reported e) ↔
      e ∈ (algorithm2_detect cfg st).1 \ reported := by
  by_cases hrep : e ∈ reported
  · simp only [resetReported, hrep, ↓reduceIte, mul_zero, Finset.mem_sdiff, not_true_eq_false,
      and_false]
    exact ⟨fun h => (not_le_of_gt hε h.2).elim, False.elim⟩
  · simp [resetReported, hrep, algorithm2_detect, Finset.mem_sdiff]

/-- Interpreting the current numerator as a reset account makes the
tree residual test exact for the remaining model reports. -/
theorem detect_residual_pending {cfg : Alg2Config} (st : Alg2State cfg)
    {P e : ℕ} {account residual : ℤ} {reported : Finset ℕ}
    (he : e ∈ st.extG.E) (hε : 0 < cfg.ε) (hl : 0 < st.extℓ e)
    (haccount : (account : ℝ) / (2 : ℝ) ^ P = resetReported st.detectAccum reported e)
    (hresidual : residual = account - detectorThreshold P cfg.ε (st.extℓ e)) :
    0 ≤ residual ↔ e ∈ (algorithm2_detect cfg st).1 \ reported := by
  rw [hresidual, ← detectorThreshold_test P cfg.ε (st.extℓ e) account hl, haccount]
  exact (and_iff_right he).symm.trans (detect_ready_after_report st hε reported e)

/-- An exhausted scan that reported only ready edges has completed the
model report and performed exactly the model's account resets. -/
theorem detect_exhausted {cfg : Alg2Config} (st : Alg2State cfg) (hε : 0 < cfg.ε)
    {reported : Finset ℕ} (hsub : reported ⊆ (algorithm2_detect cfg st).1)
    (hstop : ∀ e ∈ st.extG.E, ¬ cfg.ε ≤ st.extℓ e * resetReported st.detectAccum reported e) :
    reported = (algorithm2_detect cfg st).1 ∧
      resetReported st.detectAccum reported = (algorithm2_detect cfg st).2.detectAccum := by
  have heq : reported = (algorithm2_detect cfg st).1 := by
    apply Finset.Subset.antisymm hsub
    intro e he
    by_contra hn
    have hs : e ∈ (algorithm2_detect cfg st).1 \ reported := Finset.mem_sdiff.mpr ⟨he, hn⟩
    obtain ⟨hG, hready⟩ := (detect_ready_after_report st hε reported e).mpr hs
    exact hstop e hG hready
  exact ⟨heq, congrArg (resetReported st.detectAccum) heq⟩

end MinCostFlow.MinRatio
