module

public import MinCostFlow.Basic.Forest
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.MinRatio.PathCancellation
import MinCostFlow.MinRatio.TerminalCutCount
import MinCostFlow.LSF.Walks
import Mathlib.Tactic.Linarith

/-!
# Recovering tree path usage from a terminal cut

When routing flow in Algorithm 2 (page 29), an edge's representative
must be traversed by the same terminal pairs. Root the component.
The paths from the root determine the two sides of each edge. The
absolute coefficient of a path is one when its endpoints lie on
different sides and zero otherwise.
-/

public section

namespace MinCostFlow.MinRatio

private theorem rootedPath_abs {F : MGraph} (hF : F.IsForest) {r u : ℕ}
    (hu : F.Connected r u) (e : ℕ) :
    |walkFlow (F.forestPath r u) e| =
      if e ∈ walkEdges (F.forestPath r u) then 1 else 0 :=
  LSF.walkFlow_abs_of_nodup (LSF.isPath_nodup_edges (LSF.forestPath_isPath hF hu)) e

/-- Membership in the two root paths determines the traversal count
of the terminal-to-terminal path. -/
theorem terminalCut_usage {F : MGraph} (hF : F.IsForest) {r u v : ℕ}
    (hu : F.Connected r u) (hv : F.Connected r v) (e : ℕ) :
    |walkFlow (F.forestPath u v) e| =
      if (e ∈ walkEdges (F.forestPath r u)) ↔ (e ∈ walkEdges (F.forestPath r v))
      then 0 else 1 := by
  classical
  have huv := MGraph.connected_trans (MGraph.connected_symm hu) hv
  let a := walkFlow (F.forestPath r u) e
  let b := walkFlow (F.forestPath r v) e
  let c := walkFlow (F.forestPath u v) e
  have hsum : a + c = b := walkFlow_forestPath_add hF hu huv e
  have hc : |c| ≤ 1 := by
    dsimp only [c]
    rw [rootedPath_abs hF huv]
    split <;> norm_num
  have ha := rootedPath_abs hF hu e
  have hb := rootedPath_abs hF hv e
  change |a| = _ at ha
  change |b| = _ at hb
  change |c| = _
  by_cases hU : e ∈ walkEdges (F.forestPath r u) <;>
    by_cases hV : e ∈ walkEdges (F.forestPath r v) <;> simp [hU,hV] at ha hb ⊢
  · have he : a = b := by
      rcases abs_eq (show (0 : ℝ) ≤ 1 by norm_num) |>.mp ha with h₁ | h₁ <;>
        rcases abs_eq (show (0 : ℝ) ≤ 1 by norm_num) |>.mp hb with h₂ | h₂
      all_goals
        have hpos := le_abs_self c
        have hneg := neg_le_abs c
        linarith only [h₁, h₂, hsum, hc, hpos, hneg]
    exact sub_eq_zero.mp (by linarith only [hsum, he] : c - 0 = 0)
  · have he : c = -a := by linarith only [hsum, hb]
    rw [he, abs_neg, ha]
  · have he : c = b := by linarith only [hsum, ha]
    rw [he, hb]
  · linarith only [hsum, ha, hb]

/-- Two edges defining the same cut on the terminals have the same
absolute coefficient on every path between terminals in the component. -/
theorem terminalCut_same_usage {F : MGraph} (hF : F.IsForest) {r u v e f : ℕ}
    (terminals : Finset ℕ) (hu : u ∈ terminals) (hv : v ∈ terminals)
    (hc : ∀ t ∈ terminals, F.Connected r t)
    (hs : terminals.filter (fun t => e ∈ walkEdges (F.forestPath r t)) =
      terminals.filter (fun t => f ∈ walkEdges (F.forestPath r t))) :
    |walkFlow (F.forestPath u v) e| = |walkFlow (F.forestPath u v) f| := by
  classical
  have hmem (t : ℕ) (ht : t ∈ terminals) :
      (e ∈ walkEdges (F.forestPath r t)) ↔ (f ∈ walkEdges (F.forestPath r t)) := by
    have he := Finset.mem_filter (s := terminals)
      (p := fun t => e ∈ walkEdges (F.forestPath r t)) (a := t)
    have hf := Finset.mem_filter (s := terminals)
      (p := fun t => f ∈ walkEdges (F.forestPath r t)) (a := t)
    rw [hs] at he
    exact ((and_iff_right ht).symm.trans he.symm).trans (hf.trans (and_iff_right ht))
  rw [terminalCut_usage hF (hc u hu) (hc v hv), terminalCut_usage hF (hc u hu) (hc v hv)]
  simp only [hmem u hu, hmem v hv]

private theorem rootPath_prefix_at_edge {F : MGraph} (hF : F.IsForest)
    {r v : ℕ} (hv : F.Connected r v) {x : ℕ × Bool} (hx : x ∈ F.forestPath r v) :
    x ∈ F.forestPath r (F.dst x) ∧ F.forestPath r (F.dst x) <+: F.forestPath r v := by
  have hPath := LSF.forestPath_isPath hF hv
  obtain ⟨p, q, heq, hp, _⟩ := LSF.IsWalk_mem_split_edge hPath.1 hx
  have hprefix := MGraph.isWalk_append hp
    (.cons (MGraph.isWalk_edges_mem hPath.1 x hx) rfl (.nil (F.dst x)))
  have hPathPrefix : F.IsPath r (F.dst x) (p ++ [x]) :=
    LSF.IsPath_append_left (Q := q) (by simpa only [heq, List.append_assoc, List.singleton_append] using hPath)
      hprefix
  rw [LSF.forestPath_eq_of_isPath hF hPathPrefix]
  exact ⟨by simp, ⟨q, by simpa only [List.append_assoc, List.singleton_append] using heq.symm⟩⟩

private theorem rootPath_same_orientation {F : MGraph} (hF : F.IsForest)
    {r u v : ℕ} (hu : F.Connected r u) (hv : F.Connected r v)
    {x y : ℕ × Bool} (hx : x ∈ F.forestPath r u) (hy : y ∈ F.forestPath r v)
    (he : y.1 = x.1) : y = x := by
  have hrev : (x.1, !x.2) ∉ F.forestPath r v := by
    intro hr
    have hlt := (pathCancel_swap hF hu hv hx hr).2.2
    omega
  rcases x with ⟨e, dx⟩
  rcases y with ⟨f, dy⟩
  change f = e at he
  subst f
  cases dx <;> cases dy <;> first | rfl | exact (hrev hy).elim

/-- The sets of terminals whose root paths cross two given forest
edges are nested or disjoint. If a root path crosses both edges,
their prefixes to the farther endpoints are comparable. -/
theorem terminalCut_nested_or_disjoint {F : MGraph} (hF : F.IsForest) {r : ℕ}
    (terminals : Finset ℕ) (hc : ∀ t ∈ terminals, F.Connected r t) (e f : ℕ) :
    let A := terminals.filter (fun t => e ∈ walkEdges (F.forestPath r t))
    let B := terminals.filter (fun t => f ∈ walkEdges (F.forestPath r t))
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  classical
  dsimp only
  by_cases hd : Disjoint (terminals.filter fun t => e ∈ walkEdges (F.forestPath r t))
      (terminals.filter fun t => f ∈ walkEdges (F.forestPath r t))
  · exact Or.inr (Or.inr hd)
  rw [Finset.disjoint_left] at hd
  push Not at hd
  obtain ⟨w, hw₁, hw₂⟩ := hd
  obtain ⟨hw, he⟩ := Finset.mem_filter.mp hw₁
  have hf := (Finset.mem_filter.mp hw₂).2
  have extract {j v : ℕ} (h : j ∈ walkEdges (F.forestPath r v)) :
      ∃ x ∈ F.forestPath r v, x.1 = j := by
    simpa only [walkEdges, List.mem_toFinset, List.mem_map] using h
  obtain ⟨x, hx, rfl⟩ := extract he
  obtain ⟨y, hy, rfl⟩ := extract hf
  obtain ⟨hxEnd, hxPre⟩ := rootPath_prefix_at_edge hF (hc w hw) hx
  obtain ⟨hyEnd, hyPre⟩ := rootPath_prefix_at_edge hF (hc w hw) hy
  have hsub (x y : ℕ × Bool) (hx : x ∈ F.forestPath r w) (hy : y ∈ F.forestPath r w)
      (hxEnd : x ∈ F.forestPath r (F.dst x))
      (hpref : F.forestPath r (F.dst x) <+: F.forestPath r (F.dst y)) :
      (terminals.filter fun t => y.1 ∈ walkEdges (F.forestPath r t)) ⊆
        (terminals.filter fun t => x.1 ∈ walkEdges (F.forestPath r t)) := by
    intro t ht
    obtain ⟨ht, hyt⟩ := Finset.mem_filter.mp ht
    obtain ⟨z, hzt, hz⟩ := extract hyt
    have hz' := rootPath_same_orientation hF (hc w hw) (hc t ht) hy hzt hz
    subst z
    have hpre := (rootPath_prefix_at_edge hF (hc t ht) hzt).2
    have hmem := (hpref.trans hpre).sublist.subset hxEnd
    exact Finset.mem_filter.mpr ⟨ht, by
      unfold walkEdges
      exact List.mem_toFinset.mpr (List.mem_map_of_mem hmem)⟩
  rcases List.prefix_or_prefix_of_prefix hxPre hyPre with hxy | hyx
  · exact Or.inr (Or.inl (hsub x y hx hy hxEnd hxy))
  · exact Or.inl (hsub y x hy hx hyEnd hyx)

/-- One representative per nonempty terminal cut gives a sample of
size at most the square of the terminal count. Every edge on a path
between terminals has a representative with the same path usage. -/
theorem terminalCut_representatives {F : MGraph} (hF : F.IsForest) {r : ℕ}
    (terminals : Finset ℕ) (hc : ∀ t ∈ terminals, F.Connected r t) :
    ∃ sample : Finset ℕ, sample ⊆ F.E ∧ sample.card ≤ terminals.card * terminals.card ∧
      ∀ e ∈ F.E, (∃ t ∈ terminals, e ∈ walkEdges (F.forestPath r t)) →
        ∃ f ∈ sample, ∀ u ∈ terminals, ∀ v ∈ terminals,
          |walkFlow (F.forestPath u v) f| = |walkFlow (F.forestPath u v) e| := by
  classical
  let cut := fun e => terminals.filter fun t => e ∈ walkEdges (F.forestPath r t)
  let used := F.E.filter fun e => (cut e).Nonempty
  let cuts := used.image cut
  have hcut (s : Finset ℕ) (hs : s ∈ cuts) : ∃ e ∈ used, cut e = s := Finset.mem_image.mp hs
  have hbound : cuts.card ≤ terminals.card * terminals.card := by
    apply terminalCutCount_le terminals cuts
    · intro s hs
      obtain ⟨e, _, rfl⟩ := hcut s hs
      exact Finset.filter_subset _ _
    · intro s hs
      obtain ⟨e, he, rfl⟩ := hcut s hs
      exact (Finset.mem_filter.mp he).2
    · intro s hs t ht
      obtain ⟨e, _, rfl⟩ := hcut s hs
      obtain ⟨f, _, rfl⟩ := hcut t ht
      exact terminalCut_nested_or_disjoint hF terminals hc e f
  let chooseEdge := fun s : {s // s ∈ cuts} => (hcut s.val s.property).choose
  let sample := cuts.attach.image chooseEdge
  refine ⟨sample, ?_, Finset.card_image_le.trans ((Finset.card_attach (s := cuts)).le.trans hbound), ?_⟩
  · intro e he
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp (hcut s.val s.property).choose_spec.1).1
  · intro e he hused
    obtain ⟨t, ht, hcross⟩ := hused
    have hmem : cut e ∈ cuts :=
      Finset.mem_image_of_mem cut (Finset.mem_filter.mpr ⟨he, ⟨t, Finset.mem_filter.mpr ⟨ht, hcross⟩⟩⟩)
    let s : {s // s ∈ cuts} := ⟨cut e, hmem⟩
    refine ⟨chooseEdge s, Finset.mem_image_of_mem chooseEdge (Finset.mem_attach _ _), ?_⟩
    intro u hu v hv
    exact terminalCut_same_usage hF terminals hu hv hc (hcut s.val s.property).choose_spec.2

end MinCostFlow.MinRatio
