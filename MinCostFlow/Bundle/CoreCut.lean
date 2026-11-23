module

public import MinCostFlow.Bundle.CoreOpenStep
import MinCostFlow.LSF.Walks

/-!
# Core splits from forest cuts

A forest cut detaches one branch of the old tour. Name one side by its
old root and the other by its new root. On the old core edges this is one
ordered split. A released edge can then be inserted as an open edge.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-- A forest cut gives an ordered core split on the old core edges. The cut edge is
omitted from the second graph for the split. If it is released, its insertion follows the split. -/
theorem coreRotation_cut {G : MGraph} {L L' : LSF} {x : End}
    {r fresh β : ℕ} (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.delete x.1)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.delete x.1)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.delete x.1)))
    (hx : x.1 ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F x.1)
    (hRoots : L'.F.R = insert fresh L.F.R) (hr : r ∈ L.F.R) (hf : fresh ∉ L.F.R)
    (hKeep : L'.F.F.Connected (L.F.F.src x) r)
    (hMove : L'.F.F.Connected (L.F.F.dst x) fresh)
    (hσ : RotationStep β (.delete x.1) ρ σ) (hβ : 2 ≤ β) :
    let C := coreGraph G L
    let C' := coreGraph (G.applyUpdate (.delete x.1)) L'
    let St := C.E.filter fun e => C'.tail e = fresh
    let Sh := C.E.filter fun e => C'.head e = fresh
    let op := Update.split r fresh St Sh
    C.UpdateIsValid op ∧ ∃ h : GraphEq C' (C.applyUpdate op),
      RotationStep β op (coreRotation ρ hG hF) ((coreRotation σ hH hF').congrGraph h) := by
  intro C C' St Sh op
  let H := G.applyUpdate (.delete x.1)
  let F := L.F.F
  have hsub : F.IsSubgraph L'.F.F := by
    rw [hCut]
    exact eraseForestEdge_subgraph F _
  have hstep : F.Connected (F.src x) (F.dst x) := ⟨[x], .cons hx rfl (.nil _)⟩
  have hKeep₀ := connected_of_subgraph hsub hKeep
  have hMove₀ := connected_of_subgraph hsub hMove
  have hsV : F.src x ∈ G.V := by
    obtain ⟨e, b⟩ := x
    have he := hF.1.1 e hx
    rw [hF.2.1] at he
    cases b
    · exact he.2
    · exact he.1
  have hFresh' : fresh ∈ L'.F.R := hRoots ▸ Finset.mem_insert_self _ _
  have hFreshV : fresh ∈ G.V := hF'.2.2.1 hFresh'
  have hrV : r ∈ G.V := hF.2.2.1 hr
  have hr₀ : L.F.root (F.src x) = r :=
    (root_eq_of_connected hF hsV hrV hKeep₀).trans (root_eq_of_mem_R hF hr)
  have hFresh₀ : L.F.root fresh = r :=
    (root_eq_of_connected hF hFreshV hsV (connected_symm (connected_trans hstep hMove₀))).trans hr₀
  have hOldConn : F.Connected r (F.src x) := connected_symm hKeep₀
  have hRoot (y : ℕ) (hy : y ∈ G.V) :
      L'.F.root y = if L'.F.root y = fresh ∧ L.F.root y = r then fresh else L.F.root y := by
    have ⟨hRt, hConn⟩ := root_mem_R hF' (v := y) hy
    have hRV : L'.F.root y ∈ G.V := hF'.2.2.1 hRt
    have hEq := root_eq_of_connected hF hy hRV (connected_of_subgraph hsub hConn)
    by_cases hh : L'.F.root y = fresh
    · simp [hh, hEq, hFresh₀]
    · have ho : L'.F.root y ∈ L.F.R := by
        rw [hRoots] at hRt
        exact (Finset.mem_insert.mp hRt).resolve_left hh
      simp [hh, hEq, root_eq_of_mem_R hF ho]
  have hCE : C'.E = C.E := by
    change G.E.erase x.1 \ L'.F.F.E = G.E \ F.E
    rw [hCut]
    ext e
    by_cases he : e = x.1
    · subst e; simp [hx, F]
    · simp [he, F]
  have hEnd (e : ℕ) (he : e ∈ C.E) :
      (C.applyUpdate op).tail e = C'.tail e ∧ (C.applyUpdate op).head e = C'.head e := by
    have hyp := hG e (Finset.mem_sdiff.mp he).1
    have heCore := Finset.mem_sdiff.mp he
    have ht := hRoot (G.tail e) hyp.1
    have hh := hRoot (G.head e) hyp.2
    exact ⟨by simpa [C, C', op, St, coreGraph, MGraph.applyUpdate, heCore.1, heCore.2] using ht.symm,
      by simpa [C, C', op, Sh, coreGraph, MGraph.applyUpdate, heCore.1, heCore.2] using hh.symm⟩
  have hgEq : GraphEq C' (C.applyUpdate op) :=
    ⟨hRoots, hCE, fun e he => let hd := hEnd e (hCE ▸ he); ⟨hd.1.symm, hd.2.symm⟩⟩
  refine ⟨⟨hr, hf, Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_⟩,
    hgEq, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with ht | hh
    · obtain ⟨he, htail⟩ := Finset.mem_filter.mp ht
      have heV := (hG e (Finset.mem_sdiff.mp he).1).1
      change L'.F.root (G.tail e) = fresh at htail
      have hEq' := root_eq_of_connected hF heV hFreshV
        (connected_of_subgraph hsub (htail ▸ (root_mem_R hF' heV).2))
      exact Or.inl (hEq'.trans hFresh₀)
    · obtain ⟨he, hhead⟩ := Finset.mem_filter.mp hh
      have heV := (hG e (Finset.mem_sdiff.mp he).1).2
      change L'.F.root (G.head e) = fresh at hhead
      have hEq' := root_eq_of_connected hF heV hFreshV
        (connected_of_subgraph hsub (hhead ▸ (root_mem_R hF' heV).2))
      exact Or.inr (hEq'.trans hFresh₀)
  let old := coreRotation ρ hG hF
  let new := coreRotation σ hH hF'
  let p : End → Bool := fun z => (branch ρ hF.1 x).contains z
  have hoRoot (w : ℕ) (hw : w ∈ L.F.R) : old.order w = tour ρ hF.1 w := by
    simp [old, coreRotation, hw]
  have hnRoot (w : ℕ) (hw : w ∈ L'.F.R) : new.order w = tour σ hF'.1 w := by
    simp [new, coreRotation, hw]
  have hfilter (w : ℕ) : ((tour σ hF'.1 w).filter fun z => z.1 != x.1) = tour σ hF'.1 w := by
    apply List.filter_eq_self.mpr
    intro z hz
    have he := ((tour_spec σ hH hF'.1 hF'.2.2.2.2 hF'.2.1 w).2 z |>.mp hz).1
    exact bne_iff_ne.mpr fun eq => (Finset.mem_erase.mp he).1 eq
  have hsubCut : H.IsSubgraph (eraseForestEdge F x.1) := hCut ▸ hF'.2.2.2.2
  have hTour (w : ℕ) (e : End) (he : e.1 = x.1) :
      ((tour σ (isForest_eraseEdge hF.1 e.1) w).filter fun z => z.1 != e.1) = tour σ hF'.1 w := by
    have hEq : eraseForestEdge F e.1 = L'.F.F := by rw [he, hCut]
    rw [tour_congr_forest σ _ hF'.1 hEq w, he]
    exact hfilter w
  have hord : ∀ w, ((ρ.order w).filter fun z => z.1 != x.1).IsRotated
      ((σ.order w).filter fun z => z.1 != x.1) := by
    intro w
    have hσw := hσ w
    have hs : ((σ.order w).filter fun z => z.1 != x.1) = σ.order w := by
      apply List.filter_eq_self.mpr
      intro z hz
      exact bne_iff_ne.mpr (Finset.mem_erase.mp ((σ.mem_order _ _).mp hz).1).1
    rw [hs]
    exact hσw.symm
  change RotationStep β op old (new.congrGraph hgEq)
  apply rotationStep_split_of_parts (ρ := old) (σ := new.congrGraph hgEq)
    (fun eq => hf (eq ▸ hr)) p
  · change (new.order r).IsRotated ((old.order r).filter fun z => !(p z))
    rw [hoRoot _ hr, hnRoot _ (hRoots ▸ Finset.mem_insert_of_mem hr)]
    have hfSrc : F.src x.flip = F.dst x := by cases x with | mk e b => cases b <;> rfl
    have hfDst : F.dst x.flip = F.src x := by cases x with | mk e b => cases b <;> rfl
    have hOld' : F.Connected r (F.src x.flip) := hfSrc ▸ connected_trans hOldConn hstep
    have hcut := tour_cut_restrict ρ σ hG hF.1 hF.2.2.2.2 hF.2.1
      (x := x.flip) hx hOld' hsubCut hord
    rw [hfDst] at hcut
    change ((tour σ (isForest_eraseEdge hF.1 x.1) (F.src x)).filter fun z => z.1 != x.1).IsRotated
      ((tour ρ hF.1 r).filter fun z => (branch ρ hF.1 x.flip).contains z) at hcut
    rw [hTour (F.src x) x rfl,
      List.filter_congr (fun z hz => cut_branch_complement ρ hG hF.1 hF.2.2.2.2 hF.2.1 hx hOldConn hz)] at hcut
    exact (tour_isRotated_of_connected σ hF'.1 hF'.2.2.2.2 (connected_symm hKeep)).trans hcut
  · change (new.order fresh).IsRotated ((old.order r).filter p)
    rw [hoRoot _ hr, hnRoot _ hFresh']
    have hh := tour_cut_restrict ρ σ hG hF.1 hF.2.2.2.2 hF.2.1 hx hOldConn hsubCut hord
    rw [hTour _ _ rfl] at hh
    exact (tour_isRotated_of_connected σ hF'.1 hF'.2.2.2.2 (connected_symm hMove)).trans hh
  · rw [hoRoot _ hr]
    exact (cut_old_arc ρ hG hF.1 hF.2.2.2.2 hF.2.1 hx hOldConn).cycBdry_le.trans hβ
  · intro w hwr hwf
    change (new.order w).IsRotated (old.order w)
    by_cases hw : w ∈ L.F.R
    · rw [hoRoot _ hw, hnRoot _ (hRoots ▸ Finset.mem_insert_of_mem hw)]
      have hn : ¬ F.Connected w (F.src x) := by
        intro hc
        have he := root_eq_of_connected hF (hF.2.2.1 hw) hsV hc
        rw [root_eq_of_mem_R hF hw, hr₀] at he
        exact hwr he
      have hh := tour_cut_untouched ρ σ hG hF.1 hF.2.2.2.2 hF.2.1 hx hn hsubCut hord
      rwa [hTour _ _ rfl] at hh
    · have hw' : w ∉ L'.F.R := by rw [hRoots, Finset.mem_insert]; exact not_or.mpr ⟨hwf, hw⟩
      simp only [old, new, coreRotation, hw, hw', ↓reduceIte]
      exact List.IsRotated.refl []

end MinCostFlow.Bundle
