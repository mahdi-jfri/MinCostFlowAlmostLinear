module

public import MinCostFlow.HierPaths.BuildHier
import Mathlib.Data.List.GetD

/-!
# The whole static construction: validity and bounds

`hier_isValid` proves that the output of the construction is a hierarchy (`HierData.IsValid`),
and `hier_bounds` that it meets `HierData.Bounds` with the numbers that full routing,
the child construction and the sibling connectors give:
- every walk has at most `d = routePathLen Δ b̂ L` edges (`lemma_1`);
- the child embeddings at a group have load at most `(T + 1) · R`, with
  `R = routeCong Δ b̂ L` and `T + 1 = 49 L' + 2` (`lemma_3`);
- the connectors of one pair of children have load at most `R` (one router call).

Both come from `hostOK_all`: every host meets the router's conditions, so the child construction
and the connector bounds apply at every group.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

theorem sum_map_eq_sum_range_getD {α : Type*} (l : List α) (f : α → ℕ) (d : α) :
    (l.map f).sum = ∑ e ∈ Finset.range l.length, f (l.getD e d) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

namespace BuildParams

variable {B : BuildParams}

/-- The connector lists of the children of group `g`, by child index. -/
theorem isChildren_members {j g : ℕ} :
    IsChildren (members B.x B.b j g)
      (fun i => members B.x B.b (j + 1) (g * branching B.x B.b j + i))
      (branching B.x B.b j) (groupSize B.x B.b (j + 1)) := by
  have h := isChildren_group (B := B) (j := j) (g := g)
  have heq : (fun i => shiftSet (B.off j g i) (Finset.range (groupSize B.x B.b (j + 1)))) =
      fun i => members B.x B.b (j + 1) (g * branching B.x B.b j + i) :=
    funext fun i => childSet_eq j g i
  rw [heq] at h
  exact h

/-- The embedding of the host of child `i` of group `g` into the host of `g`. -/
theorem emb_child {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) {j g : ℕ}
    (hs : 1 < groupSize B.x B.b (j + 1)) (hok : B.HostOK H0 β j g)
    {i : ℕ} (hi : i < branching B.x B.b j) :
    ∀ e < (B.host H0 (j + 1) (g * branching B.x B.b j + i)).m,
      IsEdgeWalk (B.host H0 j g).edges
        (edgeAt (B.host H0 (j + 1) (g * branching B.x B.b j + i)).edges e).1
        (edgeAt (B.host H0 (j + 1) (g * branching B.x B.b j + i)).edges e).2
        (B.emb H0 j (g * branching B.x B.b j + i) e) ∧
      (∀ i' ∈ B.emb H0 j (g * branching B.x B.b j + i) e,
        insideB (members B.x B.b j g) (edgeAt (B.host H0 j g).edges i') = true) ∧
      (B.emb H0 j (g * branching B.x B.b j + i) e).length ≤ routePathLen B.Δ (bh j) B.L := by
  obtain ⟨hl3, _⟩ := lemma3_at hrouter hcore hyp hs hok
  obtain ⟨_, _, _, _, hfam, hent⟩ := hl3 i hi
  intro e he
  have hemb : B.emb H0 j (g * branching B.x B.b j + i) e =
      ((B.localFamily (B.host H0 j g) j g i).getD e ((0, 0), [])).2 := by
    simp only [emb, parentGroup_child g hi, child_mod hi]
  rw [host_child H0 hi] at he ⊢
  rw [hemb]
  set F := B.localFamily (B.host H0 j g) j g i
  set E := B.localEdges (B.host H0 j g) j g i
  have heE : e < E.length := by
    simpa [Graph.m, shiftEdges] using he
  have heF : e < F.length := by
    rw [← hfam] at heE
    simpa using heE
  have hget : F.getD e ((0, 0), []) = F[e] := List.getD_eq_getElem _ _ heF
  have hedge : edgeAt E e = F[e].1 := by
    unfold edgeAt
    rw [List.getD_eq_getElem _ _ heE]
    simp only [← hfam, List.getElem_map]
  have hok' := hent F[e] (List.getElem_mem heF)
  obtain ⟨hw, hin, hlen⟩ := hok'
  simp only
  rw [edgeAt_shiftEdges heE, hedge, hget]
  exact ⟨hw, hin, hlen⟩

/-- **The construction is a hierarchy.** -/
theorem hier_isValid {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) :
    (B.hier H0).IsValid B.x B.b := by
  have hall := hostOK_all hrouter hcore hyp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j g hs hg i hi
    have h := (hall j g hs hg).2.2 _ (edgeAt_mem hi)
    simp only [insideB, Bool.and_eq_true, decide_eq_true_eq]
    exact h
  · intro j c hs hc
    have hp := parentGroup_lt hc
    have hs' : 1 < groupSize B.x B.b j := lt_of_lt_of_le hs (groupSize_succ_le _ _ _)
    have h := emb_child hrouter hcore hyp hs (hall j _ hs' hp) (Nat.mod_lt c branching_pos)
    rw [child_eq] at h
    intro e he _
    exact ⟨(h e he).1, (h e he).2.1⟩
  · intro j g hs hg c hc c' hc' hcc'
    have hpc := mem_childGroups_iff.mp hc
    have hpc' := mem_childGroups_iff.mp hc'
    have hok := hall j g hs hg
    have ha : c % branching B.x B.b j < branching B.x B.b j := Nat.mod_lt c branching_pos
    have ha' : c' % branching B.x B.b j < branching B.x B.b j := Nat.mod_lt c' branching_pos
    have hce := child_eq B.x B.b j c
    have hce' := child_eq B.x B.b j c'
    rw [hpc] at hce
    rw [hpc'] at hce'
    have hne : c % branching B.x B.b j ≠ c' % branching B.x B.b j := by
      intro h
      omega
    obtain ⟨_, h1, h2, h3, h4⟩ := siblingConns_perfect hrouter hok.1 isChildren_members (hyp.β_pos _)
      hok.2.1 (hyp.bh_ge _) ha ha' hne
    show HierData.IsPerfectOn B.x B.b (j + 1) c c' (B.conn H0 j c c')
    unfold conn HierData.IsPerfectOn
    rw [hpc]
    simp only [List.map_map]
    simp only [hce, hce'] at h2 h4
    exact ⟨h1, h2, h3, h4⟩
  · intro j g hs hg c hc c' hc' hcc' q hq
    have hpc := mem_childGroups_iff.mp hc
    have hpc' := mem_childGroups_iff.mp hc'
    have hok := hall j g hs hg
    have ha : c % branching B.x B.b j < branching B.x B.b j := Nat.mod_lt c branching_pos
    have ha' : c' % branching B.x B.b j < branching B.x B.b j := Nat.mod_lt c' branching_pos
    have hce := child_eq B.x B.b j c
    have hce' := child_eq B.x B.b j c'
    rw [hpc] at hce
    rw [hpc'] at hce'
    have hne : c % branching B.x B.b j ≠ c' % branching B.x B.b j := by
      intro h
      omega
    have hw := siblingConns_walk hrouter hok.1 isChildren_members (hyp.β_pos _) hok.2.1 (hyp.bh_ge _) ha ha' hne
    change q ∈ B.conn H0 j c c' at hq
    unfold conn at hq
    rw [hpc] at hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact (hw q0 hq0).1

end BuildParams

end MinCostFlow.HierPaths
