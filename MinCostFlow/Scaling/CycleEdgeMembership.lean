module

public import MinCostFlow.Scaling.CycleOutgoing

/-!
# Every extracted edge comes from the original positive support

The negative-cycle extraction of Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, moves edges from adjacency lists to the path
stack, from the stack to a closed part, and from that closed part to its
result. The concrete step preserves any property of all stored edges.
Applying this to positive original flow proves support membership of results.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation}

/-- A step preserves any property of every stored and returned edge. -/
theorem step_edges (s : CycleState I) (P : Fin I.m → Prop)
    (hout : ∀ v e, e ∈ s.outgoing v → P e)
    (hstack : ∀ e ∈ s.stack, P e) (hsaved : ∀ e ∈ s.cycleEdges, P e)
    (hresult : ∀ es, s.result = some es → ∀ e ∈ es, P e) :
    (∀ v e, e ∈ s.step.outgoing v → P e) ∧
    (∀ e ∈ s.step.stack, P e) ∧ (∀ e ∈ s.step.cycleEdges, P e) ∧
    (∀ es, s.step.result = some es → ∀ e ∈ es, P e) := by
  refine ⟨fun v e he => hout v e ((s.step_outgoing_sublist v).subset he), ?_⟩
  cases s with
  | mk mode out candidates stack onPath edges cost result =>
    cases mode with
    | done => exact ⟨hstack, hsaved, hresult⟩
    | choose =>
      cases candidates with
      | nil => exact ⟨hstack, hsaved, fun _ h => by cases h⟩
      | cons e rest =>
        simp only [step]
        split
        · exact ⟨by simp, hsaved, hresult⟩
        · exact ⟨by simp, by simp, hresult⟩
    | walk v =>
      cases ho : out v with
      | nil =>
        simp only [step, ho]
        exact ⟨by simp, hsaved, hresult⟩
      | cons e rest =>
        have he := hout v e (by change e ∈ out v; rw [ho]; exact List.mem_cons_self)
        have hnew : ∀ a ∈ e :: stack, P a := by
          intro a ha
          rcases List.mem_cons.mp ha with ha | ha
          · exact ha ▸ he
          · exact hstack a ha
        simp only [step, ho]
        split
        · exact ⟨hnew, by simp, hresult⟩
        · exact ⟨hnew, hsaved, hresult⟩
    | peel target =>
      cases stack with
      | nil => exact ⟨hstack, hsaved, fun _ h => by cases h⟩
      | cons e rest =>
        have he := hstack e List.mem_cons_self
        have hrest : ∀ a ∈ rest, P a := fun a ha => hstack a (List.mem_cons_of_mem _ ha)
        have hnew : ∀ a ∈ e :: edges, P a := by
          intro a ha
          rcases List.mem_cons.mp ha with ha | ha
          · exact ha ▸ he
          · exact hsaved a ha
        simp only [step]
        split
        · split
          · refine ⟨hrest, hnew, ?_⟩
            intro es hes
            cases Option.some.inj hes
            exact hnew
          · exact ⟨hrest, by simp, hresult⟩
        · exact ⟨hrest, hnew, hresult⟩

/-- Every finite run preserves the same stored-edge property. -/
theorem run_edges (fuel : ℕ) (s : CycleState I) (P : Fin I.m → Prop)
    (hout : ∀ v e, e ∈ s.outgoing v → P e)
    (hstack : ∀ e ∈ s.stack, P e) (hsaved : ∀ e ∈ s.cycleEdges, P e)
    (hresult : ∀ es, s.result = some es → ∀ e ∈ es, P e) :
    ∀ es, (run fuel s).1.result = some es → ∀ e ∈ es, P e := by
  induction fuel generalizing s with
  | zero => exact hresult
  | succ fuel ih =>
    rw [run]
    split
    · exact hresult
    · have hs := s.step_edges P hout hstack hsaved hresult
      exact ih s.step hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

end MinCostFlow.Scaling.Circulation.CycleState

namespace MinCostFlow.Scaling.Circulation

/-- Every returned edge has positive original input flow. -/
theorem extractCycleModel_positive (I : Circulation) (flow : Fin I.m → ℤ)
    (es : List (Fin I.m)) (he : (I.extractCycleModel flow).1.result = some es) :
    ∀ e ∈ es, 0 < flow e := by
  apply CycleState.run_edges (6 * I.m + 1) (I.cycleInitial flow) (fun e => 0 < flow e) _
    (by simp [cycleInitial]) (by simp [cycleInitial]) (fun _ h => by cases h) es he
  intro v e hm
  exact ((I.buildAdjacency_mem flow e v).mp hm).1

end MinCostFlow.Scaling.Circulation
