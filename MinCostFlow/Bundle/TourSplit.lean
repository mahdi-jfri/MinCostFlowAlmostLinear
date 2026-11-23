module

public import MinCostFlow.Bundle.Ordered
import MinCostFlow.LSF.Lemma54Split

/-!
# Splitting a vertex in a tour

The branch behind an incident forest end is unchanged by a split at its
source. Both versions of the branch can use the forest with all edges
incident to the source omitted.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.LSF

private theorem src_agree {F G : MGraph} (h : G.IsSubgraph F) {x : End}
    (hx : x.1 ∈ F.E) : F.src x = G.src x := by
  obtain ⟨e, b⟩ := x
  have hh := h.2.2 e hx
  cases b
  · exact hh.2
  · exact hh.1

private theorem not_connected_isolated {F : MGraph} {d w : ℕ} (hne : d ≠ w)
    (hiso : ∀ e ∈ F.E, F.tail e ≠ w ∧ F.head e ≠ w) :
    ¬ F.Connected d w := by
  intro h
  obtain ⟨P, hp⟩ := connected_symm h
  cases hp with
  | nil => exact hne rfl
  | @cons _ _ x _ he hs _ =>
    obtain ⟨e, b⟩ := x
    cases b
    · exact (hiso e he).2 hs
    · exact (hiso e he).1 hs

private theorem reaches_incident {F : MGraph} {d v : ℕ} {y : End} (hy : y.1 ∈ F.E)
    (hc : F.Connected d (F.src y)) (hend : F.tail y.1 = v ∨ F.head y.1 = v) :
    F.Connected d v := by
  have hstep : F.Connected (F.src y) (F.dst y) := ⟨[y], .cons hy rfl (.nil _)⟩
  obtain ⟨e, b⟩ := y
  cases b <;> rcases hend with h | h
  · exact h ▸ connected_trans hc hstep
  · exact h ▸ hc
  · exact h ▸ hc
  · exact h ▸ connected_trans hc hstep

private theorem proj_split_walk_edges {F : MGraph} (hF : F.IsValid) {v v' : ℕ}
    (hv' : v' ∉ F.V) (St Sh : Finset ℕ) {e : ℕ} (he : e ∈ F.E) :
    let P := fun w => if w = v' then v else w
    let F' := F.applyUpdate (.split v v' St Sh)
    P (F'.tail e) = F.tail e ∧ P (F'.head e) = F.head e := by
  have ht : F.tail e ≠ v' := fun h => hv' (h ▸ (hF e he).1)
  have hh : F.head e ≠ v' := fun h => hv' (h ▸ (hF e he).2)
  constructor
  · by_cases h : e ∈ St ∧ F.tail e = v <;> simp [MGraph.applyUpdate, h, ht]
  · by_cases h : e ∈ Sh ∧ F.head e = v <;> simp [MGraph.applyUpdate, h, hh]

private theorem dst_ne_of_source {F : MGraph} (hF : F.IsForest) {x : End}
    (hx : x.1 ∈ F.E) {v : ℕ} (hs : F.src x = v) : F.dst x ≠ v := by
  have hn := isForest_no_selfLoop hF hx
  obtain ⟨e, b⟩ := x
  cases b
  · exact fun hd => hn (hd.trans hs.symm)
  · exact fun hd => hn (hs.trans hd.symm)

/-- Splitting the source of a forest end leaves its branch block unchanged. -/
theorem branch_applySplit_eq {G F : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' St Sh)))
    (hF : F.IsForest) (hF' : (F.applyUpdate (.split v v' St Sh)).IsForest)
    (hG : G.IsSubgraph F)
    (hG' : (G.applyUpdate (.split v v' St Sh)).IsSubgraph (F.applyUpdate (.split v v' St Sh)))
    (hv' : v' ∉ G.V)
    (horder : ∀ w, w ≠ v → w ≠ v' → (σ.order w).IsRotated (ρ.order w))
    {x : End} (hx : x.1 ∈ F.E) (hsrc : F.src x = v) :
    branch ρ hF x = branch σ hF' x := by
  let F' := F.applyUpdate (.split v v' St Sh)
  let J : MGraph := { F with E := F.E.filter fun e => F.tail e ≠ v ∧ F.head e ≠ v }
  have hdv := dst_ne_of_source hF hx hsrc
  have hdxv' : F.dst x ≠ v' := by
    obtain ⟨e, b⟩ := x
    have he := hF.1 e hx
    cases b
    · exact fun h => hv' (h ▸ hG.1 he.1)
    · exact fun h => hv' (h ▸ hG.1 he.2)
  have hd : F'.dst x = F.dst x := by
    obtain ⟨e, b⟩ := x
    cases b <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hdv <;>
      simp [F', MGraph.dst, MGraph.applyUpdate, hdv]
  have hJmem {e : ℕ} : e ∈ J.E ↔ e ∈ F.E ∧ F.tail e ≠ v ∧ F.head e ≠ v :=
    Finset.mem_filter
  have hJsub : F.IsSubgraph J :=
    ⟨Finset.Subset.rfl, fun _ he => (hJmem.mp he).1, fun _ _ => ⟨rfl, rfl⟩⟩
  have hJsub' : F'.IsSubgraph J := by
    refine ⟨fun _ hw => Finset.mem_insert_of_mem hw, hJsub.2.1, ?_⟩
    intro e he
    have ⟨_, ht, hh⟩ := hJmem.mp he
    simp [J, F', MGraph.applyUpdate, ht, hh]
  have hxJ : x.1 ∉ J.E := by
    intro hm
    obtain ⟨_, ht, hh⟩ := hJmem.mp hm
    obtain ⟨e, b⟩ := x
    cases b
    · exact hh hsrc
    · exact ht hsrc
  have hsub : (eraseForestEdge F x.1).IsSubgraph J :=
    ⟨hJsub.1, fun _ he => Finset.mem_erase.mpr ⟨fun eq => hxJ (eq ▸ he), hJsub.2.1 he⟩, hJsub.2.2⟩
  have hsub' : (eraseForestEdge F' x.1).IsSubgraph J :=
    ⟨hJsub'.1, fun _ he => Finset.mem_erase.mpr ⟨fun eq => hxJ (eq ▸ he), hJsub'.2.1 he⟩, hJsub'.2.2⟩
  have hJvalid : J.IsValid := fun e he => hF.1 e (hJsub.2.1 he)
  have hJ := isForest_subgraph hF hJsub hJvalid
  have hGJ : G.IsSubgraph J :=
    ⟨hG.1, fun _ he => hG.2.1 (hJsub.2.1 he), fun e he => hG.2.2 e (hJsub.2.1 he)⟩
  have hGJ' : (G.applyUpdate (.split v v' St Sh)).IsSubgraph J := by
    refine ⟨fun _ hw => Finset.mem_insert_of_mem (hG.1 hw), fun _ he => hG.2.1 (hJsub.2.1 he), ?_⟩
    intro e he
    have hh := hJsub'.2.2 e he
    have hg := hG'.2.2 e (hJsub'.2.1 he)
    exact ⟨hh.1.trans hg.1, hh.2.trans hg.2⟩
  have hkeep : ∀ y : End, y.1 ∈ (eraseForestEdge F x.1).E →
      (eraseForestEdge F x.1).Connected (F.dst x) (F.src y) → y.1 ∈ J.E := by
    intro y hy hc
    apply hJmem.mpr
    refine ⟨(Finset.mem_erase.mp hy).2, ?_⟩
    have hn : ¬ (eraseForestEdge F x.1).Connected (F.dst x) v :=
      fun h => not_connected_eraseForestEdge hF hx (hsrc ▸ connected_symm h)
    exact ⟨fun h => hn (reaches_incident (F := eraseForestEdge F x.1) hy hc (Or.inl h)),
      fun h => hn (reaches_incident (F := eraseForestEdge F x.1) hy hc (Or.inr h))⟩
  have hkeep' : ∀ y : End, y.1 ∈ (eraseForestEdge F' x.1).E →
      (eraseForestEdge F' x.1).Connected (F'.dst x) (F'.src y) → y.1 ∈ J.E := by
    intro y hy hc
    let P : ℕ → ℕ := fun w => if w = v' then v else w
    have hp : ∀ e ∈ (eraseForestEdge F' x.1).E,
        e ∈ (eraseForestEdge F x.1).E ∧ P (F'.tail e) = F.tail e ∧ P (F'.head e) = F.head e :=
      fun e he => ⟨he, proj_split_walk_edges hF.1 (fun h => hv' (hG.1 h)) St Sh
        (Finset.mem_erase.mp he).2⟩
    obtain ⟨Q, hQ⟩ := hc
    have hpQ := proj_isWalk (proj := P) (H := eraseForestEdge F' x.1)
      (K := eraseForestEdge F x.1) hp hQ
    have h₁ : P (F'.dst x) = F.dst x := by simp [P, hd, hdxv']
    have h₂ : P (F'.src y) = F.src y := by
      obtain ⟨e, b⟩ := y
      have h := (hp e hy).2
      cases b
      · exact h.2
      · exact h.1
    rw [h₁, h₂] at hpQ
    exact hkeep y hy ⟨Q, hpQ⟩
  apply branch_eq_of_common ρ σ hF hF' hJ hG hG' hGJ hGJ' hx rfl hd hsub hsub' hkeep hkeep'
  intro w hw
  have hn : w ≠ v := by
    intro h
    subst w
    exact not_connected_isolated hdv (fun e he => (hJmem.mp he).2) hw
  have hn' : w ≠ v' := by
    intro h
    subst w
    apply not_connected_isolated hdxv' _ hw
    intro e he
    have hh := hJvalid e he
    exact ⟨fun h => hv' (h ▸ hGJ.1 hh.1), fun h => hv' (h ▸ hGJ.1 hh.2)⟩
  exact (horder w hn hn').symm

/-- After a vertex split, the tour on each side is the old tour restricted to
the corresponding blocks. -/
theorem tour_applySplit_restrict {G F : MGraph} {v v' β : ℕ} {St Sh : Finset ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' St Sh)))
    (hGval : G.IsValid) (hF : F.IsForest)
    (hF' : (F.applyUpdate (.split v v' St Sh)).IsForest)
    (hG : G.IsSubgraph F) (hV : F.V = G.V)
    (hG' : (G.applyUpdate (.split v v' St Sh)).IsSubgraph (F.applyUpdate (.split v v' St Sh)))
    (hv' : v' ∉ G.V) (hs : RotationStep β (.split v v' St Sh) ρ σ) :
    (tour σ hF' v').IsRotated ((tour ρ hF v).filter
      fun x => (movedTourEnds ρ hF v (splitEnds St Sh)).contains x) ∧
    (tour σ hF' v).IsRotated ((tour ρ hF v).filter
      fun x => (movedTourEnds ρ hF v (fun y => !splitEnds St Sh y)).contains x) := by
  obtain ⟨hk, hm, _, hother⟩ := hs
  have hblocks : ∀ p : End → Bool,
      ((ρ.order v).filter p).flatMap (tourBlock σ hF') =
      ((ρ.order v).filter p).flatMap (tourBlock ρ hF) := by
    intro p
    apply List.flatMap_congr
    intro x hx
    by_cases he : x.1 ∈ F.E
    · have hsrc := (src_agree hG he).trans ((ρ.mem_order _ _).mp (List.mem_of_mem_filter hx)).2
      have hb := branch_applySplit_eq ρ σ hF hF' hG hG' hv' hother he hsrc
      have he' : x.1 ∈ (F.applyUpdate (.split v v' St Sh)).E := he
      simp only [tourBlock, he, he', ↓reduceIte]
      exact hb.symm
    · have he' : x.1 ∉ (F.applyUpdate (.split v v' St Sh)).E := he
      simp only [tourBlock, he, he', ↓reduceIte]
  constructor
  · rw [tour_split_filter ρ hGval hF hG hV, tour_eq_flatMap σ hF' hG', movedTourEnds, ← hblocks]
    exact isRotated_flatMap hm _
  · rw [tour_split_filter ρ hGval hF hG hV, tour_eq_flatMap σ hF' hG', movedTourEnds, ← hblocks]
    exact isRotated_flatMap hk _


/-- Splitting a spanning forest in parallel with its graph keeps the
forest edges and their endpoints in the graph. -/
theorem applySplit_subgraph {G F : MGraph} (h : G.IsSubgraph F)
    (v v' : ℕ) (St Sh : Finset ℕ) :
    (G.applyUpdate (.split v v' St Sh)).IsSubgraph (F.applyUpdate (.split v v' St Sh)) := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (h.1 hx)
  · intro e he
    have ⟨ht, hh⟩ := h.2.2 e he
    simp [MGraph.applyUpdate, ht, hh]

/-- The two vertices of a forest split lie in distinct components. -/
theorem applySplit_separates {F : MGraph} (hF : F.IsForest) {v v' : ℕ}
    (hv : v ∈ F.V) (hv' : v' ∉ F.V) (St Sh : Finset ℕ) :
    ¬ (F.applyUpdate (.split v v' St Sh)).Connected v v' := by
  intro h
  obtain ⟨Q, hQ⟩ := connected_isPath h
  have hne : v ≠ v' := fun he => hv' (he ▸ hv)
  have hQne : Q ≠ [] := by
    intro he
    subst Q
    cases hQ.1
    exact hne rfl
  let P : ℕ → ℕ := fun w => if w = v' then v else w
  have hp : ∀ e ∈ (F.applyUpdate (.split v v' St Sh)).E,
      e ∈ F.E ∧ P ((F.applyUpdate (.split v v' St Sh)).tail e) = F.tail e ∧
        P ((F.applyUpdate (.split v v' St Sh)).head e) = F.head e :=
    fun _ he => ⟨he, proj_split_walk_edges hF.1 hv' St Sh he⟩
  have hclosed := proj_isWalk (proj := P) hp hQ.1
  have hw : F.IsWalk v v Q := by simpa [P, hne] using hclosed
  exact hF.2 Q ⟨hQne, isPath_nodup_edges hQ, v, hw⟩


/-- A vertex split leaves the tours of all other components unchanged. -/
theorem tour_applySplit_untouched {G F : MGraph} {v v' w β : ℕ} {St Sh : Finset ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' St Sh)))
    (hF : F.IsForest) (hF' : (F.applyUpdate (.split v v' St Sh)).IsForest)
    (hG : G.IsSubgraph F) (hw : w ∈ F.V) (hv' : v' ∉ G.V)
    (hs : RotationStep β (.split v v' St Sh) ρ σ) (hn : ¬ F.Connected w v) :
    (tour ρ hF w).IsRotated (tour σ hF' w) := by
  let F' := F.applyUpdate (.split v v' St Sh)
  let H := G.applyUpdate (.split v v' St Sh)
  let J : MGraph := { F with E := F.E.filter fun e => F.tail e ≠ v ∧ F.head e ≠ v }
  have hJmem {e : ℕ} : e ∈ J.E ↔ e ∈ F.E ∧ F.tail e ≠ v ∧ F.head e ≠ v := Finset.mem_filter
  have hJsub : F.IsSubgraph J :=
    ⟨Finset.Subset.rfl, fun _ he => (hJmem.mp he).1, fun _ _ => ⟨rfl, rfl⟩⟩
  have hJsub' : F'.IsSubgraph J := by
    refine ⟨fun _ hw => Finset.mem_insert_of_mem hw, hJsub.2.1, ?_⟩
    intro e he
    have ⟨_, ht, hh⟩ := hJmem.mp he
    simp [J, F', MGraph.applyUpdate, ht, hh]
  have hGJ : G.IsSubgraph J :=
    ⟨hG.1, fun _ he => hG.2.1 (hJsub.2.1 he), fun e he => hG.2.2 e (hJsub.2.1 he)⟩
  have hHJ : H.IsSubgraph J := by
    have hH := applySplit_subgraph hG v v' St Sh
    refine ⟨fun _ h => Finset.mem_insert_of_mem (hG.1 h),
      fun _ he => hG.2.1 (hJsub.2.1 he), ?_⟩
    intro e he
    have he' := hJsub'.2.2 e he
    have he'' := hH.2.2 e (hJsub'.2.1 he)
    exact ⟨he'.1.trans he''.1, he'.2.trans he''.2⟩
  have hJval : J.IsValid := fun e he => hF.1 e (hJsub.2.1 he)
  have hJ := isForest_subgraph hF hJsub hJval
  have hf : v' ∉ F.V := fun hv => hv' (hG.1 hv)
  have hW : w ≠ v' := fun h => hf (h ▸ hw)
  have hkeep (y : End) (hy : y.1 ∈ F.E) (hc : F.Connected w (F.src y)) : y.1 ∈ J.E :=
    hJmem.mpr ⟨hy, fun h => hn (reaches_incident hy hc (Or.inl h)),
      fun h => hn (reaches_incident hy hc (Or.inr h))⟩
  have hkeep' (y : End) (hy : y.1 ∈ F'.E) (hc : F'.Connected w (F'.src y)) : y.1 ∈ J.E := by
    let P : ℕ → ℕ := fun t => if t = v' then v else t
    have hp : ∀ e ∈ F'.E, e ∈ F.E ∧ P (F'.tail e) = F.tail e ∧ P (F'.head e) = F.head e :=
      fun _ he => ⟨he, proj_split_walk_edges hF.1 hf St Sh he⟩
    obtain ⟨Q, hQ⟩ := hc
    have hpQ := proj_isWalk (proj := P) hp hQ
    have hPw : P w = w := by simp [P, hW]
    have hPy : P (F'.src y) = F.src y := by
      obtain ⟨e, b⟩ := y
      have h := (hp e hy).2
      cases b
      · exact h.2
      · exact h.1
    rw [hPw, hPy] at hpQ
    exact hkeep y hy ⟨Q, hpQ⟩
  apply tour_isRotated_of_common ρ σ hF hF' hJ hGJ hHJ rfl hJsub hJsub' w hkeep hkeep'
  intro z hz
  have hne : z ≠ v := fun h => hn (h ▸ connected_of_subgraph hJsub hz)
  have hne' : z ≠ v' := by
    intro h
    subst z
    apply not_connected_isolated hW _ hz
    intro e he
    have ht := hJval e he
    exact ⟨fun he => hf (he ▸ ht.1), fun he => hf (he ▸ ht.2)⟩
  exact (hs.2.2.2 z hne hne').symm


/-- A connection in the split forest projects to a connection in the old
forest when the two copies of the split vertex are identified. -/
theorem connected_applySplit_proj {F : MGraph} (hF : F.IsValid) {v v' : ℕ}
    (hv' : v' ∉ F.V) (St Sh : Finset ℕ) {a b : ℕ}
    (h : (F.applyUpdate (.split v v' St Sh)).Connected a b) :
    F.Connected (if a = v' then v else a) (if b = v' then v else b) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, proj_isWalk (H := F.applyUpdate (.split v v' St Sh)) (K := F)
    (proj := fun w => if w = v' then v else w)
    (fun _ he => ⟨he, proj_split_walk_edges hF hv' St Sh he⟩) hQ⟩

end MinCostFlow.Bundle
