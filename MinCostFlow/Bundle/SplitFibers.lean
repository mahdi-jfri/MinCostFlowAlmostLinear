module

public import MinCostFlow.Bundle.SplitValid

/-!
# Contents of bundles after splitting into runs

The old name keeps the first run. A fresh name has exactly the ends of
its named run. All other old names retain their ends and core parents.
-/

public section

namespace MinCostFlow.Bundle

private theorem bundle_fresh {B : BundleState} {c : ℕ} (hc : c ∈ B.vertices) :
    c < B.vertices.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hc)

/-- The result of processing one bundle has the exact run fibers named by the
split step. -/
theorem bundleSplitFoldStep_fibers (v v' b : ℕ) (moved : End → Bool) (B : BundleState)
    (ops : List Update) (runs : List (List End)) (hb : b ∈ B.vertices)
    (hfiber_live : ∀ x : End, x.1 ∈ B.edges → B.bundleOf x ∈ B.vertices)
    (hn : runs.flatten.Nodup)
    (hcover : ∀ x, x ∈ runs.flatten ↔ x.1 ∈ B.edges ∧ B.bundleOf x = b) :
    let next := B.vertices.sup id + 1
    let B' := (bundleSplitFoldStep v v' moved (ops, B) (b, runs)).2
    B'.edges = B.edges ∧
    (∀ c, c ∈ B'.vertices ↔ c ∈ B.vertices ∨ ∃ i < (runs.drop 1).length, c = next + i) ∧
    (∀ c ∈ B.vertices, c ≠ b → B'.ends c = B.ends c ∧ B'.parent c = B.parent c) ∧
    B'.ends b = (runs.head?.getD []).toFinset ∧
    B'.parent b = (match runs.head? with
      | none => B.parent b
      | some r => if r.head?.any moved then v' else v) ∧
    ∀ i (hi : i < (runs.drop 1).length),
      B'.ends (next + i) = (runs.drop 1)[i].toFinset ∧
      B'.parent (next + i) = if (runs.drop 1)[i].head?.any moved then v' else v := by
  intro next B'
  let U := bundleRunUpdates b next runs
  have hE : B'.edges = B.edges := bundleRunUpdates_edges B.graph b next runs
  have hV : ∀ c, c ∈ B'.vertices ↔ c ∈ B.vertices ∨ ∃ i < (runs.drop 1).length, c = next + i :=
    bundleRunUpdates_V_mem B.graph b next runs
  refine ⟨hE, hV, ?_, ?_, ?_, ?_⟩
  · intro c hc hcne
    have hcLt : c < next := bundle_fresh hc
    refine ⟨?_, ?_⟩
    · ext x
      rw [BundleState.mem_ends, BundleState.mem_ends, hE]
      constructor
      · rintro ⟨he, ha⟩
        refine ⟨he, ?_⟩
        by_cases hx : B.bundleOf x = b
        · by_cases hm : x ∈ (runs.drop 1).flatten
          · obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hm
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
            have hDrop : (runs.drop 1).flatten.Nodup := by
              rw [List.flatten_eq_flatMap] at hn ⊢
              exact List.Nodup.sublist ((List.drop_sublist _ _).flatMap _) hn
            have heq : B'.bundleOf x = next + i :=
              bundleRunUpdates_src_member B.graph b next runs x ((BundleState.graph_src B x).trans hx)
                (bundle_fresh hb) hDrop i hi hxr
            omega
          · have heq : B'.bundleOf x = b :=
              (bundleRunUpdates_src_unchanged B.graph b next runs x (Or.inl hm)).trans
                ((BundleState.graph_src B x).trans hx)
            exact (hcne (ha.symm.trans heq)).elim
        · have heq : B'.bundleOf x = B.bundleOf x :=
            (bundleRunUpdates_src_unchanged B.graph b next runs x (Or.inr (by rwa [BundleState.graph_src]))).trans
              (BundleState.graph_src B x)
          exact heq.symm.trans ha
      · rintro ⟨he, rfl⟩
        refine ⟨he, ?_⟩
        exact (bundleRunUpdates_src_unchanged B.graph b next runs x (Or.inr (by rwa [BundleState.graph_src]))).trans
          (BundleState.graph_src B x)
    · change (match (if c = b then runs.head? else if next ≤ c then runs[c - next + 1]? else none) with
        | none => B.parent c | some r => if r.head?.any moved then v' else v) = _
      simp [hcne, Nat.not_le_of_lt hcLt]
  · cases runs with
    | nil =>
      ext x
      rw [BundleState.mem_ends, hE]
      change (x.1 ∈ B.edges ∧ B.graph.src x = b) ↔ x ∈ ([] : List End).toFinset
      rw [BundleState.graph_src]
      rw [← hcover]
      simp
    | cons r rs =>
      have hnd := List.nodup_append.mp hn
      ext x
      rw [BundleState.mem_ends, hE]
      change (x.1 ∈ B.edges ∧ B'.bundleOf x = b) ↔ x ∈ r.toFinset
      rw [List.mem_toFinset]
      constructor
      · rintro ⟨he, ha⟩
        have hb₀ : B.bundleOf x = b := by
          by_contra hx
          have hfix : B'.bundleOf x = B.bundleOf x :=
            (bundleRunUpdates_src_unchanged B.graph b next (r :: rs) x
              (Or.inr (by rwa [BundleState.graph_src]))).trans (BundleState.graph_src B x)
          exact hx (hfix.symm.trans ha)
        rcases List.mem_append.mp ((hcover x).mpr ⟨he, hb₀⟩) with hr | hrs
        · exact hr
        · obtain ⟨s, hs, hxs⟩ := List.mem_flatten.mp hrs
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
          have heq : B'.bundleOf x = next + i :=
            bundleRunUpdates_src_member B.graph b next (r :: rs) x ((BundleState.graph_src B x).trans hb₀)
              (bundle_fresh hb) hnd.2.1 i hi hxs
          have hlt : b < next := bundle_fresh hb
          omega
      · intro hr
        have he := (hcover x).mp (List.mem_append_left rs.flatten hr)
        have hnot : x ∉ rs.flatten := fun hh => hnd.2.2 x hr x hh rfl
        exact ⟨he.1, (bundleRunUpdates_src_unchanged B.graph b next (r :: rs) x
          (Or.inl hnot)).trans ((BundleState.graph_src B x).trans he.2)⟩
  · change (match (if b = b then runs.head? else if next ≤ b then runs[b - next + 1]? else none) with
      | none => B.parent b | some r => if r.head?.any moved then v' else v) = _
    simp
  · cases runs with
    | nil => intro i hi; simp at hi
    | cons r rs =>
      intro i hi
      change i < rs.length at hi
      have hn' := List.nodup_append.mp hn
      have hlt : b < next := bundle_fresh hb
      have hne : next + i ≠ b := by omega
      refine ⟨?_, ?_⟩
      · ext x
        rw [BundleState.mem_ends, hE]
        change (x.1 ∈ B.edges ∧ B'.bundleOf x = next + i) ↔ x ∈ rs[i].toFinset
        rw [List.mem_toFinset]
        constructor
        · rintro ⟨he, ha⟩
          have hx : B.bundleOf x = b := by
            by_contra hnot
            have hfix : B'.bundleOf x = B.bundleOf x :=
              (bundleRunUpdates_src_unchanged B.graph b next (r :: rs) x
                (Or.inr (by rwa [BundleState.graph_src]))).trans (BundleState.graph_src B x)
            have hlive := (show ∀ w ∈ B.vertices, w < next from fun _ hw => bundle_fresh hw)
            have hsource : B.bundleOf x ∈ B.vertices := by
              -- A fresh destination can be reached only from the split source.
              -- The live source is provided by validity of the bundle graph.
              exact hfiber_live x he
            have hlt' := hlive _ hsource
            omega
          rcases List.mem_append.mp ((hcover x).mpr ⟨he, hx⟩) with hr | hrs
          · have hnot : x ∉ rs.flatten := fun hh => hn'.2.2 x hr x hh rfl
            have hfix : B'.bundleOf x = b :=
              (bundleRunUpdates_src_unchanged B.graph b next (r :: rs) x
                (Or.inl hnot)).trans ((BundleState.graph_src B x).trans hx)
            exact (hne (ha.symm.trans hfix)).elim
          · obtain ⟨s, hs, hxs⟩ := List.mem_flatten.mp hrs
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
            have heq : B'.bundleOf x = next + j :=
              bundleRunUpdates_src_member B.graph b next (r :: rs) x ((BundleState.graph_src B x).trans hx)
                hlt hn'.2.1 j hj hxs
            have hij : i = j := by omega
            subst j
            exact hxs
        · intro hr
          have hm := List.mem_flatten_of_mem (List.getElem_mem hi) hr
          have he := (hcover x).mp (List.mem_append_right r hm)
          exact ⟨he.1, bundleRunUpdates_src_member B.graph b next (r :: rs) x
            ((BundleState.graph_src B x).trans he.2) hlt hn'.2.1 i hi hr⟩
      · change (match (if next + i = b then (r :: rs).head? else
            if next ≤ next + i then (r :: rs)[next + i - next + 1]? else none) with
          | none => B.parent (next + i)
          | some s => if s.head?.any moved then v' else v) = _
        have hi' : next + i - next = i := by omega
        simp [hne, hi', List.getElem?_eq_getElem hi]

end MinCostFlow.Bundle
