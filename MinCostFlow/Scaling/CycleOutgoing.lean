module

public import MinCostFlow.Scaling.CycleExtractionModel
public import MinCostFlow.Scaling.AdjacencyMembership

/-!
# Unused adjacency lists only lose entries

The extraction in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, consumes positive-flow adjacency entries and never introduces
new ones. This file proves that each final outgoing list is a sublist of
its initial list. Every remaining entry therefore still lies at its tail
and belongs to the original positive-flow support.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation}

private theorem update_sublist (out : Fin I.n → List (Fin I.m)) (v : Fin I.n)
    (e : Fin I.m) (rest : List (Fin I.m)) (ho : out v = e :: rest) (w : Fin I.n) :
    (Function.update out v rest w).Sublist (out w) := by
  classical
  by_cases hw : w = v
  · subst w
    rw [Function.update_self, ho]
    exact List.sublist_cons_self _ _
  · rw [Function.update_of_ne hw]

/-- Every step only removes entries from outgoing lists. -/
theorem step_outgoing_sublist (s : CycleState I) (v : Fin I.n) :
    (s.step.outgoing v).Sublist (s.outgoing v) := by
  cases s with
  | mk mode out candidates stack onPath edges cost result =>
    cases mode with
    | done => exact List.Sublist.refl _
    | choose =>
      cases candidates with
      | nil => exact List.Sublist.refl _
      | cons e rest =>
        simp only [step]
        split <;> exact List.Sublist.refl _
    | walk w =>
      cases ho : out w with
      | nil => simpa only [step, ho] using List.Sublist.refl (out v)
      | cons e rest =>
        simp only [step, ho]
        split <;> exact update_sublist out w e rest ho v
    | peel target =>
      cases stack with
      | nil => exact List.Sublist.refl _
      | cons e rest =>
        simp only [step]
        split
        · split <;> exact List.Sublist.refl _
        · exact List.Sublist.refl _

/-- A finite extraction run only removes outgoing entries. -/
theorem run_outgoing_sublist (fuel : ℕ) (s : CycleState I) (v : Fin I.n) :
    ((run fuel s).1.outgoing v).Sublist (s.outgoing v) := by
  induction fuel generalizing s with
  | zero => exact List.Sublist.refl _
  | succ fuel ih =>
    rw [run]
    split
    · exact List.Sublist.refl _
    · exact (ih s.step).trans (s.step_outgoing_sublist v)

end MinCostFlow.Scaling.Circulation.CycleState

namespace MinCostFlow.Scaling.Circulation

/-- Every unconsumed arc after extraction is still a positive original-flow
arc stored at its original tail. -/
theorem extractCycleModel_outgoing (I : Circulation) (flow : Fin I.m → ℤ)
    (v : Fin I.n) (e : Fin I.m) (he : e ∈ (I.extractCycleModel flow).1.outgoing v) :
    I.tail e = v ∧ 0 < flow e := by
  have hh := CycleState.run_outgoing_sublist (6 * I.m + 1) (I.cycleInitial flow) v
  have hm : e ∈ I.buildAdjacency flow v := hh.subset he
  have hp := (I.buildAdjacency_mem flow e v).mp hm
  exact ⟨hp.2.symm, hp.1⟩

end MinCostFlow.Scaling.Circulation
