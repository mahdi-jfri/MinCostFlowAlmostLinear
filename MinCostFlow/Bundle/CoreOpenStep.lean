module

public import MinCostFlow.Bundle.CoreRotation
public import MinCostFlow.SparseCore.GraphHelpers

/-!
# Open-edge steps of an ordered core graph

The forest stays fixed during an open-edge edit. The core has the same
roots and its rotations keep the order of all surviving open ends.
-/

@[expose] public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.SparseCore

/-- A rotation depends only on the endpoints of present edges. -/
def Rotation.congrGraph {G H : MGraph} (ρ : Rotation G) (h : GraphEq G H) : Rotation H where
  order := ρ.order
  nodup := ρ.nodup
  mem_order v x := by
    rw [ρ.mem_order]
    have hm : x.1 ∈ G.E ↔ x.1 ∈ H.E := by rw [h.2.1]
    have hs (he : x.1 ∈ G.E) : G.src x = H.src x := by
      obtain ⟨e, side⟩ := x
      have heq := h.2.2 e he
      cases side
      · exact heq.2
      · exact heq.1
    exact ⟨fun ⟨he, hv⟩ => ⟨hm.mp he, (hs he).symm.trans hv⟩,
      fun ⟨he, hv⟩ => ⟨hm.mpr he, (hs (hm.mpr he)).trans hv⟩⟩

/-- Filtering out an absent edge does not change a rotation. -/
theorem filter_avoid_edge {G : MGraph} (ρ : Rotation G) {e : ℕ}
    (he : e ∉ G.E) (v : ℕ) :
    ((ρ.order v).filter fun x => x.1 != e) = ρ.order v := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact bne_iff_ne.mpr fun h => he (h ▸ ((ρ.mem_order _ _).mp hx).1)

/-- Open-edge edits keep the common open ends in core tour order. -/
theorem core_filter_open {G H : MGraph} {L : LSF} {e : ℕ}
    (ρ : Rotation G) (σ : Rotation H) (hG : G.IsValid) (hH : H.IsValid)
    (hF : L.F.IsRootedSpanningForestOf G) (hF' : L.F.IsRootedSpanningForestOf H)
    (he : e ∉ L.F.F.E)
    (hord : ∀ v, ((ρ.order v).filter fun x => x.1 != e).IsRotated
      ((σ.order v).filter fun x => x.1 != e)) :
    ∀ v, (((coreRotation ρ hG hF).order v).filter fun x => x.1 != e).IsRotated
      (((coreRotation σ hH hF').order v).filter fun x => x.1 != e) := by
  intro v
  unfold coreRotation
  by_cases hv : v ∈ L.F.R
  · simp only [hv, ↓reduceIte]
    exact tour_filter_isRotated ρ σ hF.1 hF.2.2.2.2 hF'.2.2.2.2 (fun x => x.1 != e)
      (fun x hx => bne_iff_ne.mpr fun hh => he (hh ▸ hx)) hord v
  · simp only [hv, ↓reduceIte, List.filter_nil]
    exact List.IsRotated.refl []

/-- Inserting an open edge gives an ordered insertion on the core. -/
theorem coreRotation_insert {G : MGraph} {L : LSF} {β e a b : ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.insert e a b)))
    (hG : G.IsValid) (hG' : (G.applyUpdate (.insert e a b)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L.F.IsRootedSpanningForestOf (G.applyUpdate (.insert e a b)))
    (hu : G.UpdateIsValid (.insert e a b))
    (hs : RotationStep β (.insert e a b) ρ σ) :
    let C := coreGraph G L
    let op := Update.insert e (L.F.root a) (L.F.root b)
    ∃ h : GraphEq (coreGraph (G.applyUpdate (.insert e a b)) L) (C.applyUpdate op),
      RotationStep β op (coreRotation ρ hG hF) ((coreRotation σ hG' hF').congrGraph h) := by
  intro C op
  have he : e ∉ L.F.F.E := fun he => hu.1 (hF.2.2.2.2.2.1 he)
  have hh : GraphEq (coreGraph (G.applyUpdate (.insert e a b)) L) (C.applyUpdate op) := by
    refine ⟨rfl, ?_, ?_⟩
    · change insert e G.E \ L.F.F.E = insert e (G.E \ L.F.F.E)
      ext f
      by_cases hfe : f = e
      · subst f; simp [he]
      · simp [hfe]
    · intro f _
      by_cases hfe : f = e
      · subst f; simp [C, op, coreGraph, MGraph.applyUpdate]
      · simp [C, op, coreGraph, MGraph.applyUpdate, Function.update_of_ne hfe]
  refine ⟨hh, ?_⟩
  intro v
  have hor : ∀ w, ((ρ.order w).filter fun x => x.1 != e).IsRotated
      ((σ.order w).filter fun x => x.1 != e) := by
    intro w
    rw [filter_avoid_edge ρ hu.1]
    exact (hs w).symm
  have hcore := (core_filter_open ρ σ hG hG' hF hF' he hor v).symm
  have hnot : e ∉ C.E := fun h => hu.1 (Finset.mem_sdiff.mp h).1
  rw [filter_avoid_edge (coreRotation ρ hG hF) hnot] at hcore
  exact hcore

/-- Deleting an open edge gives an ordered deletion on the core. -/
theorem coreRotation_delete {G : MGraph} {L : LSF} {β e : ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.delete e)))
    (hG : G.IsValid) (hG' : (G.applyUpdate (.delete e)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)))
    (he : e ∉ L.F.F.E) (hs : RotationStep β (.delete e) ρ σ) :
    ∃ h : GraphEq (coreGraph (G.applyUpdate (.delete e)) L)
        ((coreGraph G L).applyUpdate (.delete e)),
      RotationStep β (.delete e) (coreRotation ρ hG hF) ((coreRotation σ hG' hF').congrGraph h) := by
  have hh : GraphEq (coreGraph (G.applyUpdate (.delete e)) L)
      ((coreGraph G L).applyUpdate (.delete e)) := by
    refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    change G.E.erase e \ L.F.F.E = (G.E \ L.F.F.E).erase e
    ext f
    simp [and_assoc]
  refine ⟨hh, ?_⟩
  intro v
  have hnot : e ∉ (G.applyUpdate (.delete e)).E := by simp [MGraph.applyUpdate]
  have hor : ∀ w, ((ρ.order w).filter fun x => x.1 != e).IsRotated
      ((σ.order w).filter fun x => x.1 != e) := by
    intro w
    rw [filter_avoid_edge σ hnot]
    exact (hs w).symm
  have hcore := (core_filter_open ρ σ hG hG' hF hF' he hor v).symm
  have hnot' : e ∉ (coreGraph (G.applyUpdate (.delete e)) L).E :=
    fun h => hnot (Finset.mem_sdiff.mp h).1
  rw [filter_avoid_edge (coreRotation σ hG' hF') hnot'] at hcore
  exact hcore


/-- Reindexing endpoint maps outside the live edge set preserves a
primitive ordered update. -/
theorem RotationStep.congrGraph {G H : MGraph} {β : ℕ} {u : Update} {ρ : Rotation G}
    {σ : Rotation (G.applyUpdate u)} (h : GraphEq G H) (hs : RotationStep β u ρ σ) :
    RotationStep β u (ρ.congrGraph h) (σ.congrGraph (graphEq_applyUpdate h u)) := by
  cases u <;> exact hs

/-- Ordered batches depend only on the live endpoint maps. -/
theorem RotationBatch.congrGraph {G : MGraph} {β : ℕ} {U : List Update}
    {ρ : Rotation G} {σ : Rotation (G.applyBatch U)} (hr : RotationBatch β U ρ σ)
    {H : MGraph} (h : GraphEq G H) :
    RotationBatch β U (ρ.congrGraph h) (σ.congrGraph (graphEq_applyBatch h U)) := by
  induction hr generalizing H with
  | nil hr => exact .nil hr
  | @cons G u U ρ ρ' σ hs _ ih =>
    exact .cons (RotationStep.congrGraph h hs) (ih (graphEq_applyUpdate h u))

/-- Transport along exact graph equality agrees with reindexing on live edges. -/
theorem rotation_cast_congrGraph {G H J : MGraph} (ρ : Rotation G)
    (h : GraphEq G H) (he : H = J) :
    (he ▸ ρ.congrGraph h : Rotation J) = ρ.congrGraph (he ▸ h) := by
  cases he
  rfl

/-- An ordered sequence specified on the literal contractions gives a
`RotInstance` on representatives whose endpoint maps agree on live edges.
This permits the same update batches to be folded without changing their
rotation proofs. -/
theorem rotInstance_of_live_batches (D D' : DynamicInstance) (β : ℕ)
    (hD : ∀ T, D.IsValid T)
    (hG : ∀ t, GraphEq (D'.G t) (D.G t))
    (ρ : ∀ t, Rotation (D'.G t))
    (hBatch : ∀ t, ∃ h : GraphEq (D'.G (t + 1)) ((D'.G t).applyBatch (D.U (t + 1))),
      RotationBatch β (D.U (t + 1)) (ρ t) ((ρ (t + 1)).congrGraph h)) :
    RotInstance D β := by
  refine ⟨fun t => (ρ t).congrGraph (hG t), fun t => ?_⟩
  obtain ⟨_, he⟩ := hD (t + 1) (t + 1) (Nat.succ_pos _) (Nat.le_refl _)
  rw [Nat.add_sub_cancel] at he
  obtain ⟨h, hrot⟩ := hBatch t
  have hr := RotationBatch.congrGraph hrot (hG t)
  refine ⟨he, ?_⟩
  rw [rotation_cast_congrGraph]
  exact hr

end MinCostFlow.Bundle
