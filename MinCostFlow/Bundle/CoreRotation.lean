module

public import MinCostFlow.Bundle.Ordered
public import MinCostFlow.Chain.CoreGraph

/-!
# Rotations on the core graph

The forest tour over a root lists precisely the ends whose endpoints contract
to that root. Subgraph rotations keep the order of the retained ends.
-/

@[expose] public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain

private theorem core_src (G : MGraph) (L : LSF) (x : End) :
    (coreGraph G L).src x = L.F.root (G.src x) := by
  obtain ⟨e, b⟩ := x
  cases b <;> rfl

private theorem src_mem {G : MGraph} (hG : G.IsValid) {x : End} (hx : x.1 ∈ G.E) :
    G.src x ∈ G.V := by
  obtain ⟨e, b⟩ := x
  have h := hG e hx
  cases b
  · exact h.2
  · exact h.1

/-- Give each vertex of the core graph the tour of its forest component. -/
noncomputable def coreRotation {G : MGraph} {L : LSF} (ρ : Rotation G) (hG : G.IsValid)
    (hF : L.F.IsRootedSpanningForestOf G) : Rotation (coreGraph G L) where
  order := fun v => if v ∈ L.F.R then tour ρ hF.1 v else []
  nodup v := by
    split
    · exact (tour_spec ρ hG hF.1 hF.2.2.2.2 hF.2.1 v).1
    · exact List.nodup_nil
  mem_order v x := by
    have he : x.1 ∈ (coreGraph G L).E ↔ x.1 ∈ G.E ∧ x.1 ∉ L.F.F.E := Finset.mem_sdiff
    rw [he, core_src]
    by_cases hv : v ∈ L.F.R
    · have hvG := hF.2.2.1 hv
      rw [show (if v ∈ L.F.R then tour ρ hF.1 v else []) = tour ρ hF.1 v from by simp [hv], (tour_spec ρ hG hF.1 hF.2.2.2.2 hF.2.1 v).2]
      constructor
      · rintro ⟨hx, hn, hc⟩
        exact ⟨⟨hx, hn⟩, (root_eq_of_connected hF hvG (src_mem hG hx) hc).symm.trans
          (root_eq_of_mem_R hF hv)⟩
      · rintro ⟨⟨hx, hn⟩, hr⟩
        exact ⟨hx, hn, connected_of_root_eq hF hvG (src_mem hG hx)
          ((root_eq_of_mem_R hF hv).trans hr.symm)⟩
    · simp only [hv, ↓reduceIte]
      simp only [List.not_mem_nil, false_iff, not_and]
      rintro ⟨hx, _⟩ hr
      exact hv (hr ▸ (root_mem_R hF (src_mem hG hx)).1)

/-- Order the ends of a subgraph by restricting the larger graph's rotations. -/
def Rotation.restrict {C H : MGraph} (ρ : Rotation C) (hH : C.IsSubgraph H) : Rotation H where
  order := fun v => (ρ.order v).filter (fun x => decide (x.1 ∈ H.E))
  nodup v := (ρ.nodup v).filter _
  mem_order v x := by
    rw [List.mem_filter, ρ.mem_order, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨_, hs⟩, hx⟩
      have hh := hH.2.2 x.1 hx
      cases x with
      | mk e b => cases b <;> exact ⟨hx, (by first | exact hh.1.trans hs | exact hh.2.trans hs)⟩
    · rintro ⟨hx, hs⟩
      have hh := hH.2.2 x.1 hx
      refine ⟨⟨hH.2.1 hx, ?_⟩, hx⟩
      cases x with
      | mk e b => cases b <;> first | exact hh.1.symm.trans hs | exact hh.2.symm.trans hs

/-- Restriction to a subgraph preserves the upper bound for a moved set. -/
theorem Rotation.restrict_cycBdry_le {C H : MGraph} (ρ : Rotation C) (hH : C.IsSubgraph H)
    (v : ℕ) (moved : End → Bool) :
    cycBdry moved ((ρ.restrict hH).order v) ≤ cycBdry moved (ρ.order v) :=
  cycBdry_filter_le moved _ _


/-- A core split passes to a subgraph using the same test on its surviving
ends. -/
theorem Rotation.restrict_split {C H : MGraph} {β v v' : ℕ} {St Sh : Finset ℕ}
    {ρ : Rotation C} {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (hH : C.IsSubgraph H)
    (hH' : (C.applyUpdate (.split v v' St Sh)).IsSubgraph
      (H.applyUpdate (.split v v' St Sh)))
    (hs : RotationStep β (.split v v' St Sh) ρ σ) :
    RotationStep β (.split v v' St Sh) (ρ.restrict hH) (σ.restrict hH') := by
  obtain ⟨hkeep, hmove, hbd, hother⟩ := hs
  let q : End → Bool := fun x => decide (x.1 ∈ H.E)
  have hfilter (p : End → Bool) (xs : List End) :
      (xs.filter p).filter q = (xs.filter q).filter p := by
    simp only [List.filter_filter, Bool.and_comm]
  refine ⟨?_, ?_, (cycBdry_filter_le _ q _).trans hbd, ?_⟩
  · have h := isRotated_filter q hkeep
    rw [hfilter] at h
    exact h
  · have h := isRotated_filter q hmove
    rw [hfilter] at h
    exact h
  · intro w hw hw'
    exact isRotated_filter q (hother w hw hw')


/-- Restricting the named split ends to subgraph edges gives the ordered split
of that subgraph. -/
theorem Rotation.restrict_split_inter {C H : MGraph} {β v v' : ℕ} {St Sh : Finset ℕ}
    {ρ : Rotation C} {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (hH : C.IsSubgraph H)
    (hH' : (C.applyUpdate (.split v v' St Sh)).IsSubgraph
      (H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))))
    (hs : RotationStep β (.split v v' St Sh) ρ σ) :
    RotationStep β (.split v v' (St ∩ H.E) (Sh ∩ H.E)) (ρ.restrict hH) (σ.restrict hH') := by
  obtain ⟨hkeep, hmove, hbd, hother⟩ := hs
  let q : End → Bool := fun x => decide (x.1 ∈ H.E)
  let xs := (ρ.order v).filter q
  let p := splitEnds St Sh
  let p' := splitEnds (St ∩ H.E) (Sh ∩ H.E)
  have hm : ∀ x ∈ xs, p x = p' x := by
    intro x hx
    have he : x.1 ∈ H.E := of_decide_eq_true (List.mem_filter.mp hx).2
    obtain ⟨e, b⟩ := x
    cases b <;> simp [p, p', splitEnds, he]
  have hfilter (r : End → Bool) (ys : List End) :
      (ys.filter r).filter q = (ys.filter q).filter r := by
    simp only [List.filter_filter, Bool.and_comm]
  have hb : cycBdry p' xs = cycBdry p xs :=
    cycBdry_congr_on (fun x hx => (hm x hx).symm)
  refine ⟨?_, ?_, hb.le.trans ((cycBdry_filter_le p q _).trans hbd), ?_⟩
  · have hh := isRotated_filter q hkeep
    rw [hfilter, List.filter_congr (fun x hx => congrArg Bool.not (hm x hx))] at hh
    exact hh
  · have hh := isRotated_filter q hmove
    rw [hfilter, List.filter_congr hm] at hh
    exact hh
  · intro w hw hw'
    exact isRotated_filter q (hother w hw hw')

/-- When the core keeps the order of common ends, inserting one subgraph
edge preserves the order of the old subgraph ends. -/
theorem Rotation.restrict_insert {C C' H : MGraph} {β e u v : ℕ}
    (ρ : Rotation C) (σ : Rotation C') (hH : C.IsSubgraph H)
    (hH' : C'.IsSubgraph (H.applyUpdate (.insert e u v))) (he : e ∉ H.E)
    (hor : ∀ w, ((σ.order w).filter fun x => x.1 != e).IsRotated
      ((ρ.order w).filter fun x => x.1 != e)) :
    RotationStep β (.insert e u v) (ρ.restrict hH) (σ.restrict hH') := by
  intro w
  let q : End → Bool := fun x => decide (x.1 ∈ H.E)
  let p : End → Bool := fun x => x.1 != e
  let q' : End → Bool := fun x => decide (x.1 ∈ insert e H.E)
  have hy := isRotated_filter q (hor w)
  have hq : (fun x => q x && p x) = q := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [p, q, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨fun h => h.1, fun hx => ⟨hx, fun eq => he (eq ▸ hx)⟩⟩
  have hq' : (fun x => p x && q' x) = q := by
    funext x
    rw [← congrFun hq x]
    apply Bool.eq_iff_iff.mpr
    simp only [p, q, q', Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Finset.mem_insert]
    exact ⟨fun ⟨hn, hor⟩ => ⟨hor.resolve_left hn, hn⟩,
      fun ⟨hmem, hn⟩ => ⟨hn, Or.inr hmem⟩⟩
  change (((σ.order w).filter q').filter p).IsRotated ((ρ.order w).filter q)
  rw [List.filter_filter, hq']
  change (((σ.order w).filter p).filter q).IsRotated (((ρ.order w).filter p).filter q) at hy
  rw [List.filter_filter, List.filter_filter, hq] at hy
  exact hy

/-- When the core keeps the order of common ends, deleting a subgraph edge
restricts that subgraph's order. -/
theorem Rotation.restrict_delete {C C' H : MGraph} {β e : ℕ}
    (ρ : Rotation C) (σ : Rotation C') (hH : C.IsSubgraph H)
    (hH' : C'.IsSubgraph (H.applyUpdate (.delete e)))
    (hor : ∀ w, ((σ.order w).filter fun x => x.1 != e).IsRotated
      ((ρ.order w).filter fun x => x.1 != e)) :
    RotationStep β (.delete e) (ρ.restrict hH) (σ.restrict hH') := by
  intro w
  let p : End → Bool := fun x => x.1 != e
  let q : End → Bool := fun x => decide (x.1 ∈ H.E)
  let q' : End → Bool := fun x => decide (x.1 ∈ H.E.erase e)
  have hy := isRotated_filter q (hor w)
  have eq₁ : (fun x => p x && q x) = q' := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [p, q, q', Finset.mem_erase]
  have eq₂ : (fun x => q x && p x) = q' := by
    simpa only [Bool.and_comm] using eq₁
  change ((σ.order w).filter q').IsRotated (((ρ.order w).filter q).filter p)
  rw [List.filter_filter, eq₁]
  change (((σ.order w).filter p).filter q).IsRotated (((ρ.order w).filter p).filter q) at hy
  rw [List.filter_filter, List.filter_filter, eq₂] at hy
  exact hy


/-- A split is ordered if its tours restrict to the kept and moved parts
and the moved part satisfies the stated boundary bound. The live
endpoints identify which test is given by the split's encoding. -/
theorem rotationStep_split_of_parts {C : MGraph} {v v' β : ℕ} {St Sh : Finset ℕ}
    {ρ : Rotation C} {σ : Rotation (C.applyUpdate (.split v v' St Sh))}
    (hne : v ≠ v') (p : End → Bool)
    (hk : (σ.order v).IsRotated ((ρ.order v).filter fun x => !(p x)))
    (hm : (σ.order v').IsRotated ((ρ.order v).filter p))
    (hb : cycBdry p (ρ.order v) ≤ β)
    (ho : ∀ w, w ≠ v → w ≠ v' → (σ.order w).IsRotated (ρ.order w)) :
    RotationStep β (.split v v' St Sh) ρ σ := by
  have htest : ∀ x ∈ ρ.order v, p x = splitEnds St Sh x := by
    intro x hx
    have ⟨he, hv⟩ := (ρ.mem_order _ _).mp hx
    have hsrc : x ∈ σ.order v' ↔ splitEnds St Sh x = true := by
      rw [σ.mem_order, src_applySplit, hv]
      by_cases hp : splitEnds St Sh x = true <;> simp [hp, hne, he, MGraph.applyUpdate]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hp
      exact hsrc.mp (hm.perm.mem_iff.mpr (List.mem_filter.mpr ⟨hx, hp⟩))
    · intro hp
      exact (List.mem_filter.mp (hm.perm.mem_iff.mp (hsrc.mpr hp))).2
  refine ⟨?_, ?_, ?_, ho⟩
  · rw [List.filter_congr (fun x hx => congrArg Bool.not (htest x hx))] at hk
    exact hk
  · rw [List.filter_congr htest] at hm
    exact hm
  · exact (cycBdry_congr_on htest).symm.le.trans hb

end MinCostFlow.Bundle
