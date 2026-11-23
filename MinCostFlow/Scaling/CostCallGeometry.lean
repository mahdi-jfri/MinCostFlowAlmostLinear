module

public import MinCostFlow.Scaling.CostScalingModel

/-!
# Sizes of the calls made by cost scaling

The composition of Lemmas C.3 and C.9 in Appendix C of Chen et al.,
arXiv:2203.00671v2, needs both edge and vertex bounds for the intermediate
instances. Vertex compression is done once before the cost loop. Dual
extraction adds two vertices. Every intermediate call retains at least the
original number of edge slots.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Dual extraction adds a source and the zero-capacity adapter's vertex. -/
theorem Circulation.extractDualModel_vertices
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (f : Fin I.m → ℤ) :
    ∀ J ∈ (I.extractDualModel solve f).calls, J.n = I.n + 2 := by
  intro J hJ
  have he := List.mem_singleton.mp hJ
  subst J
  rfl

/-- The two calls of one round retain the original edges and add at most two vertices. -/
theorem CostState.step_geometry
    (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ)
    {I : Circulation} (s : CostState I) :
    ∀ J ∈ (s.step solve C).calls, I.m ≤ J.m ∧ J.n ≤ I.n + 2 := by
  intro J hJ
  rcases List.mem_cons.mp hJ with hJ | hJ
  · subst J
    change I.m ≤ I.m + I.m ∧ I.n + 1 ≤ I.n + 2
    omega
  · have he := (s.roundedInstance C).extractDualModel_edges solve _ J hJ
    have hn := (s.roundedInstance C).extractDualModel_vertices solve _ J hJ
    change J.m = 4 * (I.m + I.m) + 2 * I.n at he
    change J.n = I.n + 2 at hn
    omega

/-- The loop preserves the same call geometry at every state. -/
theorem costLoop_geometry (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    ∀ J ∈ (costLoop solve I C).calls, I.m ≤ J.m ∧ J.n ≤ I.n + 2 :=
  CallResult.forRounds_instances _ _ (fun s => CostState.step_geometry solve C s) _ _

/-- All intermediate instances have between `m` and `12*m` edges and at most
`2*m+2` vertices, independently of the original number of isolated vertices. -/
theorem costScalingModel_geometry (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    ∀ J ∈ (costScalingModel solve I C).calls,
      I.m ≤ J.m ∧ J.m ≤ 12 * I.m ∧ J.n ≤ 2 * I.m + 2 := by
  intro J hJ
  have he := costScalingModel_edges solve I C J hJ
  refine ⟨?_, he, ?_⟩
  all_goals
    unfold costScalingModel at hJ
    split at hJ
    · simp at hJ
    · dsimp only at hJ
      split at hJ
      · have hj := List.mem_singleton.mp hJ
        subst J
        first | exact le_rfl | exact Nat.add_le_add (I.endpointLabels_count_le) (by decide)
      · have h := costLoop_geometry solve I.compress C J hJ
        first | exact h.1 | exact le_trans h.2 (Nat.add_le_add_right I.endpointLabels_count_le 2)

end MinCostFlow.Scaling
