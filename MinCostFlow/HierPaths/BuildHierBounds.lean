module

public import MinCostFlow.HierPaths.BuildHierValid

/-!
# The whole static construction: the bounds

`hier_bounds`: the output of the construction meets `HierData.Bounds` with, at every depth,
- `d = routePathLen Δ b̂ L` edges per walk (`lemma_1`);
- load `(49 L' + 2) · R` for the child embeddings of a group, with `R = routeCong Δ b̂ L`
  (`lemma_3`: `T + 1` router calls, `T = 49 L' + 1`);
- load `R` for the connectors of one pair of children (one router call).

Loads count occurrences. The walks of the router may repeat edges; the construction shortcuts
every walk to one that repeats no edge (`erase`), so a walk through an edge uses it once.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

namespace BuildParams

variable {B : BuildParams}

/-- Two different children of group `g`, by their indices. -/
theorem child_indices {j g c c' : ℕ} (hc : c ∈ childGroups B.x B.b j g)
    (hc' : c' ∈ childGroups B.x B.b j g) (hcc' : c < c') :
    parentGroup B.x B.b j c = g ∧ c % branching B.x B.b j < branching B.x B.b j ∧
      c' % branching B.x B.b j < branching B.x B.b j ∧
      c % branching B.x B.b j ≠ c' % branching B.x B.b j := by
  have hpc := mem_childGroups_iff.mp hc
  have hpc' := mem_childGroups_iff.mp hc'
  have hce := child_eq B.x B.b j c
  have hce' := child_eq B.x B.b j c'
  rw [hpc] at hce
  rw [hpc'] at hce'
  refine ⟨hpc, Nat.mod_lt c branching_pos, Nat.mod_lt c' branching_pos, fun h => ?_⟩
  omega

/-- **The bounds of the construction.** -/
theorem hier_bounds {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) :
    (B.hier H0).Bounds B.x B.b (fun j => routePathLen B.Δ (bh j) B.L)
      (fun j => (49 * B.L' + 2) * routeCong B.Δ (bh j) B.L)
      (fun j => routeCong B.Δ (bh j) B.L) := by
  have hall := hostOK_all hrouter hcore hyp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j c hs hc e he
    have hp := parentGroup_lt hc
    have hs' : 1 < groupSize B.x B.b j := lt_of_lt_of_le hs (groupSize_succ_le _ _ _)
    have h := emb_child hrouter hcore hyp hs (hall j _ hs' hp) (Nat.mod_lt c branching_pos)
    rw [child_eq] at h
    exact (h e he).2.2
  · intro j g hs hg c hc c' hc' hcc' q hq
    obtain ⟨hpc, ha, ha', hne⟩ := child_indices hc hc' hcc'
    have hok := hall j g hs hg
    have hw := siblingConns_walk hrouter hok.1 isChildren_members (hyp.β_pos _) hok.2.1 (hyp.bh_ge _) ha ha'
      hne
    change q ∈ B.conn H0 j c c' at hq
    unfold conn at hq
    rw [hpc] at hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact (hw q0 hq0).2.2
  · intro j g hs hg i hi
    have hs' : 1 < groupSize B.x B.b j := lt_of_lt_of_le hs (groupSize_succ_le _ _ _)
    have hok := hall j g hs' hg
    obtain ⟨hl3, hload⟩ := lemma3_at hrouter hcore hyp hs hok
    show ∑ c ∈ childGroups B.x B.b j g, ∑ e ∈ Finset.range (B.host H0 (j + 1) c).m,
      (B.emb H0 j c e).count i ≤ _
    unfold childGroups
    rw [Finset.sum_Ico_eq_sum_range]
    have hbr : (g + 1) * branching B.x B.b j - g * branching B.x B.b j = branching B.x B.b j := by
      rw [add_mul, one_mul]
      omega
    rw [hbr]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a ha => ?_)) (hload i hi)
    have ha' := Finset.mem_range.mp ha
    obtain ⟨_, _, _, _, hfam, _⟩ := hl3 a ha'
    rw [host_child H0 ha']
    have hemb : ∀ e, B.emb H0 j (g * branching B.x B.b j + a) e =
        ((B.localFamily (B.host H0 j g) j g a).getD e ((0, 0), [])).2 := by
      intro e
      simp only [emb, parentGroup_child g ha', child_mod ha']
    simp only [hemb]
    have hlen : (Graph.mk (2 ^ B.x) (shiftEdges (B.off j g a)
        (B.localEdges (B.host H0 j g) j g a))).m = (B.localFamily (B.host H0 j g) j g a).length := by
      simp [Graph.m, shiftEdges, ← hfam]
    rw [hlen]
    unfold occLoad walkFamily
    rw [List.map_map, sum_map_eq_sum_range_getD _ _ ((0, 0), [])]
    rfl
  · intro j g hs hg c hc c' hc' hcc' i hi
    obtain ⟨hpc, ha, ha', hne⟩ := child_indices hc hc' hcc'
    have hok := hall j g hs hg
    have h := (occLoad_siblingConns_le_cong hrouter hok.1 isChildren_members (hyp.β_pos _) hok.2.1 (hyp.bh_ge _)
      ha ha' hne hi)
    show ((B.conn H0 j c c').map fun q => q.2.2.count i).sum ≤ _
    unfold conn
    rw [hpc]
    unfold occLoad at h
    simp only [List.map_map] at h ⊢
    exact h

end BuildParams

end MinCostFlow.HierPaths
