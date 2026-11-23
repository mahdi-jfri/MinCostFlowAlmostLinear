module

public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.IPM.Machine.MinRatioContract

/-!
# The stored gradients and lengths follow the history

The precondition of `Update` in `minRatioMachineContractWithV` says that the state is the output
of a `Detect` on a state reached by a valid history, and that the caller's gradient and length
arrays agree with that history outside the edges that the batch inserts
(`MinRatioDetectedWith`). The solver keeps its own copy of the gradient and the length of each
live edge. To read only the inserted entries of the caller's arrays, it must know that its copy
is the history's current vector.

For ordered Algorithm 2 this holds because `Init` and `Update` store the vectors they are given,
and `Detect` keeps them (`algorithm2_detect`). A valid history does not change the vectors at a
`Detect` stage (`MinRatioHistoryValid`, third conjunct). So the stored `extg` and `extℓ` after
stage `T` are `D.g T` and `D.ℓ T` (`ordAlg2_minRatioState_ext`). With `MinRatioDetectedWith`
this gives `ordAlg2_detectedWith_agree`: outside the changed edges, the caller's arrays equal the
stored vectors. Only `ordAlg2_detectedWith_agree` is used later.
-/

public section

namespace MinCostFlow.MinRatio

open Chain IPM IPM.Machine

/-- `Update` of ordered Algorithm 2 stores the gradient and length vectors it is given, in both
outcomes of the cycle loop. -/
theorem ordAlg2_update_ext (cfg : Alg2Config) (κ : ℝ) (model : Alg2State cfg)
    (U : List Update) (g l : ℕ → ℝ) (η : ℝ) :
    ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U g l η).1.extg = g ∧
      ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U g l η).1.extℓ = l := by
  change ((Chain.Ordered.algorithm2_updateWith cfg κ model U g l η).1).extg = _ ∧
    ((Chain.Ordered.algorithm2_updateWith cfg κ model U g l η).1).extℓ = _
  unfold Chain.Ordered.algorithm2_updateWith
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- After stage `T` of a valid history, the state of ordered Algorithm 2 stores the history's
current gradients `D.g T` and lengths `D.ℓ T`. The proof is by induction on `T`. `Init` stores
`D.g 0` and `D.ℓ 0`. An `Update` at stage `t + 1` stores `D.g (t + 1)` and `D.ℓ (t + 1)`
(`ordAlg2_update_ext`). A `Detect` keeps the stored vectors, and the validity of the history
gives `D.g (t + 1) = D.g t` and `D.ℓ (t + 1) = D.ℓ t` at such a stage. -/
theorem ordAlg2_minRatioState_ext (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (hV : MinRatioHistoryValid D op T) :
    (minRatioState (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).eraseFailure D η op T).extg =
        D.g T ∧
      (minRatioState (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).eraseFailure D η op
        T).extℓ = D.ℓ T := by
  induction T with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    have ih' := ih (MinRatioHistoryValid.mono D op (t + 1) t hV (Nat.le_succ t))
    simp only [minRatioState]
    split
    · exact ordAlg2_update_ext cfg κ _ _ _ _ _
    · rename_i hop
      have hstep := hV.2.2.1 (t + 1) (Nat.le_add_left 1 t) le_rfl (by simpa using hop)
      simp only [Nat.add_sub_cancel] at hstep
      rw [hstep.2.1, hstep.2.2]
      exact ih'

/-- Under the `Update` precondition `MinRatioDetectedWith`, the caller's gradient and length
vectors equal the vectors stored in the state at every edge of `G` that is not changed. The
state is `Detect` of a state `s₀` reached by a valid history, and the caller's vectors agree
with that history's current vectors outside the changed edges (both by the definition of
`MinRatioDetectedWith`). The stored vectors of `s₀` are the history's current vectors
(`ordAlg2_minRatioState_ext`), and `Detect` keeps them. -/
theorem ordAlg2_detectedWith_agree {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {s : Alg2State cfg} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (h : MinRatioDetectedWith (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G s changed g l) :
    ∀ e ∈ G.E, ¬ changed e → g e = s.extg e ∧ l e = s.extℓ e := by
  obtain ⟨s₀, g₀, l₀, ⟨D, η, op, T, hV, _, hs₀, hagree₀, _⟩, hs, hagree⟩ := h
  intro e he hn
  have hext := ordAlg2_minRatioState_ext cfg κ D η op T hV
  have hdet : s.extg = s₀.extg ∧ s.extℓ = s₀.extℓ := by
    rw [hs]
    exact ⟨rfl, rfl⟩
  rw [hdet.1, hdet.2, hs₀, hext.1, hext.2, (hagree e he hn).1, (hagree e he hn).2]
  exact hagree₀ e he

end MinCostFlow.MinRatio

end
