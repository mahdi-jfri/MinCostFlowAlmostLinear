module

public import MinCostFlow.Bundle.CoreOpenStep

/-!
# Ordered dynamic subgraphs of a core

A subgraph inherits its core rotation at every primitive step. Insertions
and deletions keep surviving ends in order, and splits restrict the core's
moved sets to the live edges of the subgraph.
-/

@[expose] public section

namespace MinCostFlow.Bundle

open MinCostFlow.SparseCore

/-- The ambient core of a subgraph at an intermediate stage. -/
structure CoreView (H : MGraph) where
  /-- The core graph. -/
  graph : MGraph
  /-- The rotation of that core graph. -/
  rotation : Rotation graph
  /-- The graph at this stage is a subgraph of the core. -/
  subgraph : graph.IsSubgraph H

/-- The inherited rotation of the subgraph. -/
def CoreView.inherited {H : MGraph} (view : CoreView H) : Rotation H :=
  view.rotation.restrict view.subgraph

/-- A subgraph batch with a core view at each intermediate stage (repair
note, Result 5.2). A core may stay fixed during a subgraph edge edit, or
change by an edit outside the subgraph that leaves the inherited cyclic
order unchanged up to rotation. A subgraph split follows the core split
with the end sets restricted to its own edges. -/
inductive CoreSubgraphBatch (β : ℕ) :
    {H : MGraph} → (U : List Update) → CoreView H → CoreView (H.applyBatch U) → Prop
  | nil {H : MGraph} (a : CoreView H) : CoreSubgraphBatch β [] a a
  | skip {H : MGraph} {U : List Update} {a b : CoreView H}
      {c : CoreView (H.applyBatch U)} :
      (∀ w, (b.inherited.order w).IsRotated (a.inherited.order w)) →
      CoreSubgraphBatch β U b c → CoreSubgraphBatch β U a c
  | insert {H : MGraph} {U : List Update} {e u v : ℕ} {a : CoreView H}
      {b : CoreView (H.applyUpdate (.insert e u v))}
      {c : CoreView ((H.applyUpdate (.insert e u v)).applyBatch U)} :
      (∀ w, ((b.rotation.order w).filter fun x => x.1 != e).IsRotated
        ((a.rotation.order w).filter fun x => x.1 != e)) →
      CoreSubgraphBatch β U b c → CoreSubgraphBatch β (.insert e u v :: U) a c
  | delete {H : MGraph} {U : List Update} {e : ℕ} {a : CoreView H}
      {b : CoreView (H.applyUpdate (.delete e))}
      {c : CoreView ((H.applyUpdate (.delete e)).applyBatch U)} :
      (∀ w, ((b.rotation.order w).filter fun x => x.1 != e).IsRotated
        ((a.rotation.order w).filter fun x => x.1 != e)) →
      CoreSubgraphBatch β U b c → CoreSubgraphBatch β (.delete e :: U) a c
  | split {H : MGraph} {U : List Update} {v v' : ℕ} {St Sh : Finset ℕ} {a : CoreView H}
      {b : CoreView (H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E)))}
      {c : CoreView ((H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))).applyBatch U)} :
      (he : GraphEq b.graph (a.graph.applyUpdate (.split v v' St Sh))) →
      RotationStep β (.split v v' St Sh) a.rotation (b.rotation.congrGraph he) →
      CoreSubgraphBatch β U b c →
      CoreSubgraphBatch β (.split v v' (St ∩ H.E) (Sh ∩ H.E) :: U) a c

private theorem subgraph_congr_ambient {C C' H : MGraph}
    (h : GraphEq C C') (hH : C.IsSubgraph H) : C'.IsSubgraph H := by
  refine ⟨h.1 ▸ hH.1, h.2.1 ▸ hH.2.1, ?_⟩
  intro e he
  have hEq := h.2.2 e (hH.2.1 he)
  have hEnd := hH.2.2 e he
  exact ⟨hEnd.1.trans hEq.1, hEnd.2.trans hEq.2⟩

/-- A core edge insertion outside `H.E` preserves the inherited rotation of `H` up to rotation. -/
theorem CoreSubgraphBatch.coreInsert {H : MGraph} {U : List Update} {β e u v : ℕ}
    {a b : CoreView H} {c : CoreView (H.applyBatch U)}
    (heNot : e ∉ H.E)
    (he : GraphEq b.graph (a.graph.applyUpdate (.insert e u v)))
    (hs : RotationStep β (.insert e u v) a.rotation (b.rotation.congrGraph he))
    (hrest : CoreSubgraphBatch β U b c) : CoreSubgraphBatch β U a c := by
  refine .skip (fun w => ?_) hrest
  let q : End → Bool := fun x => decide (x.1 ∈ H.E)
  let p : End → Bool := fun x => x.1 != e
  have hq : (fun x => q x && p x) = q := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [p, q, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨fun h => h.1, fun hx => ⟨hx, fun eq => heNot (eq ▸ hx)⟩⟩
  have hrot := isRotated_filter q (hs w)
  change (((b.rotation.order w).filter p).filter q).IsRotated ((a.rotation.order w).filter q) at hrot
  rw [List.filter_filter, hq] at hrot
  exact hrot

/-- A core edge deletion outside `H.E` preserves the inherited rotation of `H` up to rotation. -/
theorem CoreSubgraphBatch.coreDelete {H : MGraph} {U : List Update} {β e : ℕ}
    {a b : CoreView H} {c : CoreView (H.applyBatch U)}
    (heNot : e ∉ H.E)
    (he : GraphEq b.graph (a.graph.applyUpdate (.delete e)))
    (hs : RotationStep β (.delete e) a.rotation (b.rotation.congrGraph he))
    (hrest : CoreSubgraphBatch β U b c) : CoreSubgraphBatch β U a c := by
  refine .skip (fun w => ?_) hrest
  let q : End → Bool := fun x => decide (x.1 ∈ H.E)
  let p : End → Bool := fun x => x.1 != e
  have hq : (fun x => q x && p x) = q := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [p, q, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨fun h => h.1, fun hx => ⟨hx, fun eq => heNot (eq ▸ hx)⟩⟩
  have hrot := isRotated_filter q (hs w)
  change ((b.rotation.order w).filter q).IsRotated (((a.rotation.order w).filter p).filter q) at hrot
  rw [List.filter_filter, hq] at hrot
  exact hrot

/-- Replacing the core view by one with rotated orders preserves `CoreSubgraphBatch`. -/
theorem CoreSubgraphBatch.congrCore {H : MGraph} {U : List Update} {β : ℕ}
    {a b : CoreView H} {c : CoreView (H.applyBatch U)}
    (hor : ∀ w, (b.rotation.order w).IsRotated (a.rotation.order w))
    (hrest : CoreSubgraphBatch β U b c) : CoreSubgraphBatch β U a c :=
  .skip (fun w => isRotated_filter _ (hor w)) hrest

/-- Concatenate two `CoreSubgraphBatch` derivations along consecutive batches. -/
theorem CoreSubgraphBatch.append {H : MGraph} {U₁ U₂ : List Update} {β : ℕ}
    {a : CoreView H} {b : CoreView (H.applyBatch U₁)}
    {c : CoreView ((H.applyBatch U₁).applyBatch U₂)}
    (h₁ : CoreSubgraphBatch β U₁ a b) (h₂ : CoreSubgraphBatch β U₂ b c) :
    CoreSubgraphBatch β (U₁ ++ U₂) a ((applyBatch_append H U₁ U₂).symm ▸ c) := by
  induction h₁ with
  | nil _ => exact h₂
  | skip hrot _ ih => exact .skip hrot (ih h₂)
  | insert hor _ ih => exact .insert hor (ih h₂)
  | delete hor _ ih => exact .delete hor (ih h₂)
  | split he hs _ ih => exact .split he hs (ih h₂)

/-- Pre-composing a primitive `RotationStep` with vertex-wise cyclic rotations preserves it. -/
theorem RotationStep.pre_isRotated {G : MGraph} {β : ℕ} {u : Update}
    {ρ ρ' : Rotation G} {σ : Rotation (G.applyUpdate u)}
    (hrot : ∀ w, (ρ'.order w).IsRotated (ρ.order w))
    (hs : RotationStep β u ρ' σ) : RotationStep β u ρ σ := by
  cases u with
  | insert e a b =>
    intro w
    exact (hs w).trans (hrot w)
  | delete e =>
    intro w
    exact (hs w).trans (isRotated_filter _ (hrot w))
  | split v v' St Sh =>
    refine ⟨(hs.1).trans (isRotated_filter _ (hrot v)),
      (hs.2.1).trans (isRotated_filter _ (hrot v)), ?_,
      fun w hv hv' => (hs.2.2.2 w hv hv').trans (hrot w)⟩
    rw [← cycBdry_isRotated _ (hrot v)]
    exact hs.2.2.1

/-- Post-composing a primitive `RotationStep` with vertex-wise cyclic rotations preserves it. -/
theorem RotationStep.post_isRotated {G : MGraph} {β : ℕ} {u : Update}
    {ρ : Rotation G} {σ σ' : Rotation (G.applyUpdate u)}
    (hs : RotationStep β u ρ σ)
    (hrot : ∀ w, (σ'.order w).IsRotated (σ.order w)) : RotationStep β u ρ σ' := by
  cases u with
  | insert e a b =>
    intro w
    exact (isRotated_filter _ (hrot w)).trans (hs w)
  | delete e =>
    intro w
    exact (hrot w).trans (hs w)
  | split v v' St Sh =>
    exact ⟨(hrot v).trans hs.1, (hrot v').trans hs.2.1, hs.2.2.1,
      fun w hv hv' => (hrot w).trans (hs.2.2.2 w hv hv')⟩

/-- Pre-composing a nonempty `RotationBatch` with vertex-wise cyclic rotations preserves it. -/
theorem RotationBatch.pre_isRotated_of_ne_nil {G : MGraph} {β : ℕ} {U : List Update}
    {ρ ρ' : Rotation G} {σ : Rotation (G.applyBatch U)}
    (hne : U ≠ []) (hrot : ∀ w, (ρ'.order w).IsRotated (ρ.order w))
    (h : RotationBatch β U ρ' σ) : RotationBatch β U ρ σ := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hs hrest => exact .cons (RotationStep.pre_isRotated hrot hs) hrest

/-- Restriction gives an ordered batch from a rotation equivalent to `a.inherited`
at every vertex. -/
theorem CoreSubgraphBatch.ordered_exists {H : MGraph} {U : List Update} {β : ℕ}
    {a : CoreView H} {b : CoreView (H.applyBatch U)} (h : CoreSubgraphBatch β U a b)
    (hU : H.BatchIsValid U) :
    ∃ ρ' : Rotation H, (∀ w, (ρ'.order w).IsRotated (a.inherited.order w)) ∧
      RotationBatch β U ρ' b.inherited := by
  induction h with
  | nil a => exact ⟨a.inherited, fun _ => .refl _, .refl _⟩
  | skip hrot _ ih =>
    obtain ⟨ρ', hrot', hrb⟩ := ih hU
    exact ⟨ρ', fun w => (hrot' w).trans (hrot w), hrb⟩
  | insert hor _ ih =>
    obtain ⟨ρ', hrot', hrb⟩ := ih hU.2
    exact ⟨_, fun _ => .refl _,
      .cons (RotationStep.post_isRotated (Rotation.restrict_insert _ _ _ _ hU.1.1 hor) hrot') hrb⟩
  | delete hor _ ih =>
    obtain ⟨ρ', hrot', hrb⟩ := ih hU.2
    exact ⟨_, fun _ => .refl _,
      .cons (RotationStep.post_isRotated (Rotation.restrict_delete _ _ _ _ hor) hrot') hrb⟩
  | @split H U v v' St Sh a b c he hs _ ih =>
    obtain ⟨ρ', hrot', hrb⟩ := ih hU.2
    exact ⟨_, fun _ => .refl _,
      .cons (RotationStep.post_isRotated
        (Rotation.restrict_split_inter a.subgraph (subgraph_congr_ambient he b.subgraph) hs) hrot')
        hrb⟩

/-- Restriction gives ordered rotations for every nonempty batch. -/
theorem CoreSubgraphBatch.ordered_of_ne_nil {H : MGraph} {U : List Update} {β : ℕ}
    {a : CoreView H} {b : CoreView (H.applyBatch U)} (h : CoreSubgraphBatch β U a b)
    (hU : H.BatchIsValid U) (hne : U ≠ []) : RotationBatch β U a.inherited b.inherited := by
  obtain ⟨ρ', hrot', hrb⟩ := h.ordered_exists hU
  exact RotationBatch.pre_isRotated_of_ne_nil hne hrot' hrb

/-- Restriction gives ordered rotations for every batch, including the empty one, whose orders
agree up to rotation. -/
theorem CoreSubgraphBatch.ordered {H : MGraph} {U : List Update} {β : ℕ}
    {a : CoreView H} {b : CoreView (H.applyBatch U)} (h : CoreSubgraphBatch β U a b)
    (hU : H.BatchIsValid U) : RotationBatch β U a.inherited b.inherited := by
  obtain ⟨ρ', hrot', hrb⟩ := h.ordered_exists hU
  exact hrb.rotate_before hrot'

/-- For an empty batch, `CoreSubgraphBatch` preserves the inherited order up to cyclic rotation. -/
theorem CoreSubgraphBatch.ordered_nil {H : MGraph} {β : ℕ}
    {a b : CoreView H} (h : CoreSubgraphBatch β [] a b) :
    ∀ w, (b.inherited.order w).IsRotated (a.inherited.order w) := by
  obtain ⟨ρ', hrot', hrb⟩ := h.ordered_exists trivial
  cases hrb with
  | nil hr => exact fun w => (hr w).trans (hrot' w)

private theorem inherited_transport {A B : MGraph} (h : A = B) (a : CoreView A) :
    (h ▸ a.inherited : Rotation B) = (h ▸ a : CoreView B).inherited := by
  cases h
  rfl

private theorem rotation_cast_order {A B : MGraph} (h : A = B) (ρ : Rotation A) (w : ℕ) :
    ((h ▸ ρ : Rotation B).order w) = ρ.order w := by
  cases h
  rfl

private theorem rotationBatch_nil_cast {β : ℕ} {A B : MGraph} {U : List Update}
    (hU : U = []) (he : A = B.applyBatch U) (he' : A = B) (ρ : Rotation B) :
    RotationBatch β U ρ (he ▸ (he'.symm ▸ ρ : Rotation A)) := by
  subst hU
  cases he'
  exact .refl ρ

private theorem coreSubgraphBatch_nil_order {β : ℕ} {A B : MGraph} {U : List Update}
    (hU : U = []) (he : A = B.applyBatch U) (a : CoreView B) (b : CoreView A)
    (ht : CoreSubgraphBatch β U a (he ▸ b)) (w : ℕ) :
    (b.inherited.order w).IsRotated (a.inherited.order w) := by
  subst hU
  have he' : A = B := he
  cases he'
  exact ht.ordered_nil w

private noncomputable def buildRotOfView {D : DynamicInstance} {β : ℕ}
    (view : ∀ t, CoreView (D.G t))
    (h : ∀ t, ∃ he : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)),
      CoreSubgraphBatch β (D.U (t + 1)) (view t) (he ▸ view (t + 1))) :
    (t : ℕ) → { ρ : Rotation (D.G t) // ∀ w, (ρ.order w).IsRotated ((view t).inherited.order w) }
  | 0 => ⟨(view 0).inherited, fun _ => .refl _⟩
  | t + 1 =>
    open Classical in
    let prev := buildRotOfView view h t
    if hnil : D.U (t + 1) = [] then
      let he0 := (h t).choose
      have he : D.G (t + 1) = D.G t := by simpa [hnil, MGraph.applyBatch] using he0
      ⟨he.symm ▸ prev.1, fun w => by
        have hrot := coreSubgraphBatch_nil_order hnil he0 (view t) (view (t + 1))
          (h t).choose_spec w
        rw [rotation_cast_order he.symm prev.1 w]
        exact (prev.2 w).trans hrot.symm⟩
    else
      ⟨(view (t + 1)).inherited, fun _ => .refl _⟩

/-- A dynamic subgraph aligned with an ordered core is ordered with the
same split bound. -/
theorem rotInstance_of_core_subgraph {D : DynamicInstance} {β : ℕ}
    (hD : ∀ T, D.IsValid T) (view : ∀ t, CoreView (D.G t))
    (h : ∀ t, ∃ he : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)),
      CoreSubgraphBatch β (D.U (t + 1)) (view t) (he ▸ view (t + 1))) :
    RotInstance D β := by
  refine ⟨fun t => (buildRotOfView view h t).1, fun t => ?_⟩
  obtain ⟨he, ht⟩ := h t
  have hv := (hD (t + 1) (t + 1) (Nat.succ_pos _) (Nat.le_refl _)).1
  rw [Nat.add_sub_cancel] at hv
  refine ⟨he, ?_⟩
  dsimp only
  by_cases hnil : D.U (t + 1) = []
  · have hdef : buildRotOfView view h (t + 1) =
        (let prev := buildRotOfView view h t
         if hnil' : D.U (t + 1) = [] then
           let he0 := (h t).choose
           have he' : D.G (t + 1) = D.G t := by simpa [hnil', MGraph.applyBatch] using he0
           ⟨he'.symm ▸ prev.1, fun w => by
             have hrot := coreSubgraphBatch_nil_order hnil' he0 (view t) (view (t + 1))
               (h t).choose_spec w
             rw [rotation_cast_order he'.symm prev.1 w]
             exact (prev.2 w).trans hrot.symm⟩
         else
           ⟨(view (t + 1)).inherited, fun _ => .refl _⟩) := rfl
    have he' : D.G (t + 1) = D.G t := by simpa [hnil, MGraph.applyBatch] using he
    have hstep : (buildRotOfView view h (t + 1)).1 =
        (he'.symm ▸ (buildRotOfView view h t).1) := by
      rw [hdef]
      simp only [hnil, ↓reduceDIte]
    rw [hstep]
    exact rotationBatch_nil_cast hnil he he' (buildRotOfView view h t).1
  · have hdef : buildRotOfView view h (t + 1) =
        (let prev := buildRotOfView view h t
         if hnil' : D.U (t + 1) = [] then
           let he0 := (h t).choose
           have he' : D.G (t + 1) = D.G t := by simpa [hnil', MGraph.applyBatch] using he0
           ⟨he'.symm ▸ prev.1, fun w => by
             have hrot := coreSubgraphBatch_nil_order hnil' he0 (view t) (view (t + 1))
               (h t).choose_spec w
             rw [rotation_cast_order he'.symm prev.1 w]
             exact (prev.2 w).trans hrot.symm⟩
         else
           ⟨(view (t + 1)).inherited, fun _ => .refl _⟩) := rfl
    have hstep : (buildRotOfView view h (t + 1)).1 = (view (t + 1)).inherited := by
      rw [hdef]
      simp only [hnil, ↓reduceDIte]
    rw [hstep, inherited_transport]
    exact RotationBatch.pre_isRotated_of_ne_nil hnil
      (fun w => ((buildRotOfView view h t).2 w).symm)
      (ht.ordered_of_ne_nil hv hnil)

end MinCostFlow.Bundle
