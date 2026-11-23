module

public import MinCostFlow.Bundle.Tour
public import MinCostFlow.Basic.Hidden
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

/-!
# Ordered dynamic graphs

Carry rotations through each primitive update, including the intermediate
graphs of a batch. Sorting gives compatible rotations for edge-only updates.
-/

@[expose] public section

namespace MinCostFlow.Bundle

/-- The sides named by a split. At the old vertex only the specified tail
and head ends move, as in `MGraph.applyUpdate`. -/
def splitEnds (St Sh : Finset ℕ) (x : End) : Bool :=
  if x.2 then decide (x.1 ∈ St) else decide (x.1 ∈ Sh)

/-- A core split changes the source of exactly the named ends at the split vertex. -/
theorem src_applySplit (C : MGraph) (v v' : ℕ) (St Sh : Finset ℕ) (x : End) :
    (C.applyUpdate (.split v v' St Sh)).src x =
      if C.src x = v ∧ splitEnds St Sh x = true then v' else C.src x := by
  obtain ⟨e, side⟩ := x
  cases side <;> simp [MGraph.applyUpdate, MGraph.src, splitEnds, and_comm]

/-- How one primitive update preserves order. -/
def RotationStep {G : MGraph} (β : ℕ) (u : Update) (before : Rotation G)
    (after : Rotation (G.applyUpdate u)) : Prop :=
  match u with
  | .insert e _ _ =>
    ∀ v, ((after.order v).filter fun x => x.1 != e).IsRotated (before.order v)
  | .delete e =>
    ∀ v, (after.order v).IsRotated ((before.order v).filter fun x => x.1 != e)
  | .split v v' St Sh =>
    let moved := splitEnds St Sh
    (after.order v).IsRotated ((before.order v).filter fun x => !(moved x)) ∧
    (after.order v').IsRotated ((before.order v).filter moved) ∧
    cycBdry moved (before.order v) ≤ β ∧
    ∀ w, w ≠ v → w ≠ v' → (after.order w).IsRotated (before.order w)

/-- Rotations through all primitive updates in a batch. The empty batch allows each vertex's
order to rotate: an order of ends around a vertex is cyclic, so the
two rotations are the same rotation system. -/
inductive RotationBatch (β : ℕ) :
    {G : MGraph} → (U : List Update) → Rotation G → Rotation (G.applyBatch U) → Prop
  | nil {G : MGraph} {ρ σ : Rotation G} (h : ∀ v, (σ.order v).IsRotated (ρ.order v)) :
      RotationBatch β [] ρ σ
  | cons {G : MGraph} {u : Update} {U : List Update} {ρ : Rotation G}
      {ρ' : Rotation (G.applyUpdate u)} {σ : Rotation ((G.applyUpdate u).applyBatch U)} :
      RotationStep β u ρ ρ' → RotationBatch β U ρ' σ → RotationBatch β (u :: U) ρ σ

/-- The empty batch from a rotation to itself. -/
theorem RotationBatch.refl {β : ℕ} {G : MGraph} (ρ : Rotation G) : RotationBatch β [] ρ ρ :=
  .nil fun v => List.IsRotated.refl (ρ.order v)

/-- The rotations at successive stages are connected by ordered primitive
updates. -/
def RotInstance (D : DynamicInstance) (β : ℕ) : Prop :=
  ∃ ρ : ∀ t, Rotation (D.G t), ∀ t,
    ∃ h : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)),
      RotationBatch β (D.U (t + 1)) (ρ t) (h ▸ ρ (t + 1))

/-- The given orders `ord t` are the rotations of the graphs `D.G t` up to stage `τ`, and each
batch up to `τ` is ordered with split bound `β`. This is
`RotInstance` with named orders and a finite horizon: a level receives the orders of its input
from the level below, so they are data of the run. -/
def OrderedUpTo (D : DynamicInstance) (τ β : ℕ) (ord : ℕ → ℕ → List End) : Prop :=
  ∃ ρ : ∀ t, Rotation (D.G t), (∀ t ≤ τ, (ρ t).order = ord t) ∧
    ∀ t < τ, ∃ h : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)),
      RotationBatch β (D.U (t + 1)) (ρ t) (h ▸ ρ (t + 1))

/-- True for insertions and deletions. -/
def IsEdgeUpdate : Update → Prop
  | .insert .. | .delete .. => True
  | .split .. => False

/-- True for an edge deletion. -/
def deleteTag : Update → Bool
  | .delete _ => true
  | _ => false

/-- The tail precedes the head at a fixed edge name. -/
def endKey (x : End) : ℕ := 2 * x.1 + if x.2 then 0 else 1

theorem endKey_injective : Function.Injective endKey := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  cases b <;> cases c <;> simp [endKey] at h ⊢ <;> omega

/-- Compare ends by their sorting keys. -/
def endLE (a b : End) : Prop := endKey a ≤ endKey b

instance : DecidableRel endLE := fun a b => inferInstanceAs (Decidable (endKey a ≤ endKey b))
instance : IsTrans End endLE := ⟨fun _ _ _ => Nat.le_trans⟩
instance : Std.Antisymm endLE := ⟨fun _ _ h₁ h₂ => endKey_injective (Nat.le_antisymm h₁ h₂)⟩
instance : Std.Total endLE := ⟨fun a b => Nat.le_total (endKey a) (endKey b)⟩

/-- The ends at a vertex, sorted by edge name with tail before head. -/
def sortedEnds (G : MGraph) (v : ℕ) : List End :=
  let ends := (G.E ×ˢ ({true, false} : Finset Bool)).filter fun x => G.src x = v
  ends.sort endLE

theorem mem_sortedEnds (G : MGraph) (v : ℕ) (x : End) :
    x ∈ sortedEnds G v ↔ x.1 ∈ G.E ∧ G.src x = v := by
  cases x with
  | mk e b => cases b <;> simp [sortedEnds]

/-- The rotation system obtained by sorting at each vertex. -/
def sortedRotation (G : MGraph) : Rotation G where
  order := sortedEnds G
  nodup _v := Finset.sort_nodup _ _
  mem_order := mem_sortedEnds G

private theorem pairwise_sortedEnds (G : MGraph) (v : ℕ) :
    (sortedEnds G v).Pairwise endLE :=
  Finset.pairwise_sort _ _

private theorem sortedEnds_eq {xs ys : List End} (hx : xs.Nodup) (hy : ys.Nodup)
    (hsx : xs.Pairwise endLE)
    (hsy : ys.Pairwise endLE)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys := by
  exact (List.perm_ext_iff_of_nodup hx hy |>.mpr hm).eq_of_pairwise' hsx hsy

private theorem rotated_of_eq {α : Type*} {xs ys : List α} (h : xs = ys) :
    xs.IsRotated ys := h ▸ List.IsRotated.refl xs

private theorem sortedRotation_step {G : MGraph} {u : Update}
    (hu : G.UpdateIsValid u) (he : IsEdgeUpdate u) :
    RotationStep 0 u (sortedRotation G) (sortedRotation (G.applyUpdate u)) := by
  cases u with
  | split => exact he.elim
  | insert e a b =>
    intro v
    change ((sortedEnds (G.applyUpdate (.insert e a b)) v).filter
      (fun x => x.1 != e)).IsRotated (sortedEnds G v)
    apply rotated_of_eq
    refine sortedEnds_eq
      ((sortedRotation _).nodup v |>.filter _) ((sortedRotation G).nodup v)
      ((pairwise_sortedEnds _ v).filter _) (pairwise_sortedEnds G v) ?_
    intro x
    have he' := hu.1
    by_cases h : x.1 = e
    · simp [List.mem_filter, mem_sortedEnds, h, he']
    · cases x with
      | mk i b => cases b <;>
          simp [List.mem_filter, mem_sortedEnds, MGraph.applyUpdate, MGraph.src, h,
            Function.update_of_ne]
  | delete e =>
    intro v
    change (sortedEnds (G.applyUpdate (.delete e)) v).IsRotated
      ((sortedEnds G v).filter (fun x => x.1 != e))
    apply rotated_of_eq
    refine sortedEnds_eq
      ((sortedRotation _).nodup v) ((sortedRotation G).nodup v |>.filter _)
      (pairwise_sortedEnds _ v) ((pairwise_sortedEnds G v).filter _) ?_
    intro x
    simp only [List.mem_filter, mem_sortedEnds, MGraph.applyUpdate, MGraph.src,
      Finset.mem_erase, bne_iff_ne]
    exact ⟨fun ⟨⟨hn, he⟩, hs⟩ => ⟨⟨he, hs⟩, hn⟩, fun ⟨⟨he, hs⟩, hn⟩ => ⟨⟨hn, he⟩, hs⟩⟩

/-- Sorting gives compatible rotations through a batch of edge updates. -/
theorem sortedRotation_batch {G : MGraph} {U : List Update}
    (hv : G.BatchIsValid U) (he : ∀ u ∈ U, IsEdgeUpdate u) :
    RotationBatch 0 U (sortedRotation G) (sortedRotation (G.applyBatch U)) := by
  induction U generalizing G with
  | nil => exact .refl _
  | cons u U ih =>
    exact .cons (sortedRotation_step hv.1 (he u (by simp)))
      (ih hv.2 (fun op hop => he op (by simp [hop])))

/-- A valid dynamic graph with edge updates only is ordered with bound zero. -/
theorem rotInstance_of_edgeUpdates (D : DynamicInstance)
    (hv : ∀ T, D.IsValid T) (he : ∀ t u, u ∈ D.U (t + 1) → IsEdgeUpdate u) :
    RotInstance D 0 := by
  refine ⟨fun t => sortedRotation (D.G t), fun t => ?_⟩
  obtain ⟨hb, hg⟩ := hv (t + 1) (t + 1) (Nat.succ_pos _) (Nat.le_refl _)
  rw [Nat.add_sub_cancel] at hb hg
  refine ⟨hg, ?_⟩
  have hs : ∀ (H : MGraph) (h : H = (D.G t).applyBatch (D.U (t + 1))),
      RotationBatch 0 (D.U (t + 1)) (sortedRotation (D.G t)) (h ▸ sortedRotation H) := by
    intro H h
    subst H
    exact sortedRotation_batch hb (he t)
  exact hs _ hg


/-- Increasing the split bound keeps a primitive ordered. -/
theorem RotationStep.mono {G : MGraph} {u : Update} {β β' : ℕ} {ρ : Rotation G}
    {σ : Rotation (G.applyUpdate u)} (h : RotationStep β u ρ σ) (hle : β ≤ β') :
    RotationStep β' u ρ σ := by
  cases u with
  | insert => exact h
  | delete => exact h
  | split => exact ⟨h.1, h.2.1, h.2.2.1.trans hle, h.2.2.2⟩

/-- Increasing the split bound keeps an ordered batch. -/
theorem RotationBatch.mono {G : MGraph} {U : List Update} {β β' : ℕ} {ρ : Rotation G}
    {σ : Rotation (G.applyBatch U)} (h : RotationBatch β U ρ σ) (hle : β ≤ β') :
    RotationBatch β' U ρ σ := by
  induction h with
  | nil h => exact .nil h
  | cons hs _ ih => exact .cons (RotationStep.mono hs hle) ih

/-- A primitive update stays ordered when each order before it is rotated. -/
theorem RotationStep.rotate_before {G : MGraph} {u : Update} {β : ℕ} {ρ ρ' : Rotation G}
    {σ : Rotation (G.applyUpdate u)} (hs : RotationStep β u ρ σ)
    (h : ∀ v, (ρ.order v).IsRotated (ρ'.order v)) : RotationStep β u ρ' σ := by
  cases u with
  | insert e a b => exact fun v => (hs v).trans (h v)
  | delete e => exact fun v => (hs v).trans (isRotated_filter _ (h v))
  | split v v' St Sh =>
    refine ⟨hs.1.trans (isRotated_filter _ (h v)), hs.2.1.trans (isRotated_filter _ (h v)), ?_,
      fun w hw hw' => (hs.2.2.2 w hw hw').trans (h w)⟩
    rw [cycBdry_isRotated _ (h v).symm]
    exact hs.2.2.1

/-- An ordered batch stays ordered when each order before it is rotated. -/
theorem RotationBatch.rotate_before {G : MGraph} {U : List Update} {β : ℕ} {ρ ρ' : Rotation G}
    {σ : Rotation (G.applyBatch U)} (hb : RotationBatch β U ρ σ)
    (h : ∀ v, (ρ.order v).IsRotated (ρ'.order v)) : RotationBatch β U ρ' σ := by
  cases hb with
  | nil h' => exact .nil fun v => (h' v).trans (h v)
  | cons hs hr => exact .cons (hs.rotate_before h) hr

end MinCostFlow.Bundle
