module

public import MinCostFlow.HierPaths.PotentialBound

/-!
# The event count bound with the numbers of `HierPaths/Params.lean`

`delCoef_le_gamma`: when the leaf depth is at most `h`, each terminal has at most `h B`
connectors, the reverse lists have at most `ξ` entries and the connector walks at most `λ`
edges, the coefficient `delCoef` of `events_le` is at most the coefficient `delCoeff` of
`HierPaths/Params.lean`, hence at most `Γ`. So `events_le_gamma`: after `t` deletions the event
count is at most `12 Γ t`.

`exists_spec` shows that the hypotheses on the static arrays can hold together.
-/

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

public section

/-- The coefficient `delCoef` is at most the coefficient `delCoeff`, and so at most `Γ`. -/
theorem delCoef_le_gamma {a d m M lam : ℕ} (hmM : m ≤ M) (hL : leafDepth A.x A.b ≤ depthOf m)
    (hκ : κ ≤ depthOf m * branchOf m) (hξ : ξ ≤ xiOf a d m) (hlam : lam ≤ lamOf a d m) :
    A.delCoef ξ κ lam ≤ gammaHP a d M := by
  refine le_trans ?_ (delCoeff_le_gamma a d hmM)
  rw [delCoef_eq]
  unfold delCoeff
  gcongr

/-- After `t` deletions the event count is at most `12 Γ t`. -/
theorem events_le_gamma {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) {lam : ℕ}
    (hlamw : ∀ c < A.C.numConn, (A.C.walk c).edges.length ≤ lam) {a d m M : ℕ} (hmM : m ≤ M)
    (hL : leafDepth A.x A.b ≤ depthOf m) (hκ : κ ≤ depthOf m * branchOf m)
    (hξ : ξ ≤ xiOf a d m) (hlam : lam ≤ lamOf a d m) :
    A.events G.n st ≤ 12 * gammaHP a d M * st.deleted.card :=
  (A.events_le hA hinv hlamw).trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ (A.delCoef_le_gamma hmM hL hκ hξ hlam)))

end

end StaticArrays

public section

/-- The hypotheses on the static arrays can hold together: one vertex, one terminal, no
connector, empty reverse lists. -/
theorem StaticArrays.exists_spec : ∃ (G : Graph) (A : StaticArrays), G.IsValid ∧ A.Spec G 0 0 ∧
    ∀ w < G.n, G.deg w ≤ (A.C.ownedBy w).card := by
  refine ⟨⟨1, []⟩, ⟨⟨1, fun _ => 0, 0, fun _ => 0, fun _ => 0, fun _ => false,
    fun _ => Walk.empty⟩, 0, 1, fun _ => [], fun _ => [], 0, fun _ => [], fun _ => 0⟩,
    ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he; simp at he
  · rfl
  · norm_num
  · exact ⟨fun t ht => by simp, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  · intro e t ht; simp at ht
  · intro c hc; exact absurd hc (Nat.not_lt_zero _)
  · intro e; simp
  · intro t _ c; simp
  · intro t; simp
  · intro t; simp
  · intro p; simp
  · intro p c hc; simp at hc
  · intro c hc; exact absurd hc (Nat.not_lt_zero _)
  · intro w hw
    have : w = 0 := by simpa using hw
    subst this
    decide

end

end MinCostFlow.HierPaths
