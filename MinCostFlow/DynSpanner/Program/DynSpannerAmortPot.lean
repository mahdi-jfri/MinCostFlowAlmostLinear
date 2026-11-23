module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs

/-!
# The potential that pays for clearing levels

A step of Algorithm 6 at level `j > 0` rebuilds `H_j` and empties the levels above `j`. The program
clears these levels edge by edge, so its cost has a term `Σ_{i ≥ j} |E(H_i)|` (`modelOldSum`),
which the model's cost of the step does not count. A restart (`j = 0`) clears the old spanner
`H`, with cost `|E(H)|`. Both are paid by the builds of those levels: each edge of a level was
written once when the level was built.

We use the potential `levelPot st = Σ_i |E(H_i)|`. The main facts:
* `oldSum_add_levelPot_le` (`0 < j`): `Σ_{i ≥ j} |E(H_i)| + Φ(after) ≤ Φ(before) + |E(H_j')|`,
  where `H_j'` is the new level `j`. So the clearing cost is the drop of the potential plus the
  size of the new level, which the model's step pays (`|E(J̃)|`).
* `card_H_le_levelPot`: `|E(H)| ≤ Φ`, since `H` is the union of the levels.
* `levelPot_step_zero` (`j = 0`): after a restart the potential is `|E(H_0)|` of the new level `0`.
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

public section

/-- The potential `Σ_{i ≤ L} |E(H_i)|` of a state. -/
noncomputable def levelPot {L : ℕ} (st : DynSpannerState L) : ℕ :=
  ∑ i : Fin (L + 1), (st.H_level i).m

/-- A deletion or split restricted to `H` does not add edges to `H`. -/
lemma applyBatch_restrictUpdate_E_subset (u : Update) (H : MGraph) :
    (H.applyBatch (restrictUpdate u H)).E ⊆ H.E := by
  cases u with
  | insert _ _ _ => simp [restrictUpdate, MGraph.applyBatch]
  | delete e =>
    by_cases he : e ∈ H.E
    · simp [restrictUpdate, he, MGraph.applyBatch, MGraph.applyUpdate, Finset.erase_subset]
    · simp [restrictUpdate, he, MGraph.applyBatch]
  | split _ _ _ _ => simp [restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]

/-- The union of the levels below `n` has at most `Σ_i |E(H_i)|` edges. -/
lemma card_unionEdgesLt_le {L : ℕ} (H_level : Fin (L + 1) → MGraph) (n : ℕ) :
    (unionEdgesLt H_level n).card ≤ ∑ i : Fin (L + 1), (H_level i).m := by
  unfold unionEdgesLt
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

namespace StepPosModel

variable (m : StepPosModel)

/-- The levels of the state after a step with `0 < j`: below `j` they are `H_mid`, above `j`
they are empty. -/
lemma res_H_level_lt (hq : m.st.q = m.q) (ht : m.st.t = m.k) (hj : 0 < m.j)
    (i : Fin (m.L + 1)) (hi : i.1 < m.j) : m.res.state.H_level i = m.H_mid i := by
  have hj0 : chooseLevel m.L m.st.q (m.st.t + 1) ≠ 0 := by rw [hq, ht]; exact Nat.ne_of_gt hj
  simp only [StepPosModel.res, step]
  rw [dif_neg hj0]
  simp only [hq, ht]
  exact if_pos hi

lemma res_H_level_gt (hq : m.st.q = m.q) (ht : m.st.t = m.k) (hj : 0 < m.j)
    (i : Fin (m.L + 1)) (hi : m.j < i.1) : (m.res.state.H_level i).m = 0 := by
  have hj0 : chooseLevel m.L m.st.q (m.st.t + 1) ≠ 0 := by rw [hq, ht]; exact Nat.ne_of_gt hj
  simp only [StepPosModel.res, step]
  rw [dif_neg hj0]
  have hjj : chooseLevel m.L m.st.q (m.st.t + 1) = m.j := by rw [hq, ht]
  have hjf : m.j = chooseLevel m.L m.q (m.k + 1) := rfl
  have h1 : ¬ i.1 < chooseLevel m.L m.st.q (m.st.t + 1) := by omega
  have h2 : ¬ i.1 = chooseLevel m.L m.st.q (m.st.t + 1) := by omega
  simp only [h1, h2, ↓reduceIte, emptyGraphOn, MGraph.m, Finset.card_empty]

end StepPosModel

/-- **The clearing of the levels `≥ j` is paid by the potential** (step with `0 < j`): the old
levels `j, …, L` together with the potential after the step weigh at most the potential before
the step plus the new level `j`. -/
theorem oldSum_add_levelPot_le (m : StepPosModel) (hq : m.st.q = m.q) (ht : m.st.t = m.k)
    (hj : 0 < m.j) (hjL : m.j < m.L + 1) :
    modelOldSum m + levelPot m.res.state ≤
      levelPot m.st + (m.res.state.H_level ⟨m.j, hjL⟩).m := by
  have hpt : ∀ i : Fin (m.L + 1),
      (if m.j ≤ i.1 then (m.st.H_level i).m else 0) + (m.res.state.H_level i).m ≤
        (m.st.H_level i).m + (if i = ⟨m.j, hjL⟩ then (m.res.state.H_level i).m else 0) := by
    intro i
    rcases lt_trichotomy i.1 m.j with hi | hi | hi
    · rw [if_neg (by omega), if_neg (fun h => by rw [h] at hi; exact lt_irrefl _ hi),
        m.res_H_level_lt hq ht hj i hi]
      simp only [zero_add, add_zero]
      exact Finset.card_le_card (applyBatch_restrictUpdate_E_subset m.u (m.st.H_level i))
    · have hi' : i = ⟨m.j, hjL⟩ := Fin.ext hi
      rw [if_pos (le_of_eq hi.symm), if_pos hi']
    · rw [if_pos (le_of_lt hi), m.res_H_level_gt hq ht hj i hi]
      omega
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
  simpa [modelOldSum, levelPot] using hsum

/-- The spanner `H = ⋃_i H_i` has at most `levelPot st` edges. -/
theorem card_H_le_levelPot {L : ℕ} {st : DynSpannerState L}
    (hH : st.H.E = unionEdgesLt st.H_level (L + 1)) : st.H.m ≤ levelPot st := by
  unfold MGraph.m levelPot
  rw [hH]
  exact card_unionEdgesLt_le st.H_level (L + 1)

/-- After a restart (`j = 0`) the potential is the size of the new level `0`,
`H_0 = (initCore G').1`. -/
theorem levelPot_step_zero {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (hj0 : chooseLevel L st.q (st.t + 1) = 0) :
    levelPot (step st u sparsify).state = (initCore (st.G.applyUpdate u) sparsify).1.m := by
  simp only [step]
  rw [dif_pos hj0]
  simp only [levelPot, initAt]
  rw [Fintype.sum_eq_single ⟨0, Nat.zero_lt_succ L⟩]
  · simp
  · intro i hi
    have hi0 : i.1 ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi0, emptyGraphOn, MGraph.m]

/-- After `init`, the potential is the size of level `0`, `H_0 = (initCore G sparsify).1`. -/
theorem levelPot_init {L : ℕ} (G : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    levelPot (init G L q sparsify).state = (initCore G sparsify).1.m := by
  simp only [levelPot, init, initAt]
  rw [Fintype.sum_eq_single ⟨0, Nat.zero_lt_succ L⟩]
  · simp
  · intro i hi
    have hi0 : i.1 ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi0, emptyGraphOn, MGraph.m]

end

end MinCostFlow.DynSpanner.Program
