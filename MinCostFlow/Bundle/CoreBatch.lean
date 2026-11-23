module

public import MinCostFlow.Bundle.CoreCut
public import MinCostFlow.Bundle.CoreSplit
public import MinCostFlow.Bundle.RootRefinement

/-!
# Ordered core batches

Batch graphs agree with the canonical contraction on live edges. The
batch representative keeps endpoint values at absent names when it can.
-/

@[expose] public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-- A valid ordered batch from one core rotation to the next, with live-edge
agreement at its end. -/
def OrderedCoreBatch {G H : MGraph} (β : ℕ) (ρ : Rotation G) (σ : Rotation H)
    (U : List Update) : Prop :=
  G.BatchIsValid U ∧ ∃ he : GraphEq H (G.applyBatch U), RotationBatch β U ρ (σ.congrGraph he)

/-- One ordered primitive gives an ordered core batch of length one. -/
theorem OrderedCoreBatch.singleton {G H : MGraph} {β : ℕ} {ρ : Rotation G} {σ : Rotation H}
    {u : Update} (hu : G.UpdateIsValid u) (he : GraphEq H (G.applyUpdate u))
    (hs : RotationStep β u ρ (σ.congrGraph he)) : OrderedCoreBatch β ρ σ [u] :=
  ⟨⟨hu, trivial⟩, he, .cons hs (.refl _)⟩

/-- Rotating the order at each vertex of the input rotates the order at each core vertex: the
tours depend only on the cyclic orders. -/
theorem coreRotation_isRotated {G : MGraph} {L : LSF} {ρ σ : Rotation G} (hG : G.IsValid)
    (hF : L.F.IsRootedSpanningForestOf G) (h : ∀ v, (σ.order v).IsRotated (ρ.order v)) (v : ℕ) :
    ((coreRotation σ hG hF).order v).IsRotated ((coreRotation ρ hG hF).order v) := by
  change (if v ∈ L.F.R then tour σ hF.1 v else []).IsRotated
    (if v ∈ L.F.R then tour ρ hF.1 v else [])
  split
  · have ht := tour_filter_isRotated σ ρ hF.1 hF.2.2.2.2 hF.2.2.2.2 (fun _ => true)
      (fun _ _ => rfl) (fun w => by simpa using h w) v
    simpa using ht
  · exact List.IsRotated.refl _

/-- The empty core batch joins the core rotations of two input rotations that differ by a
rotation at each vertex. -/
theorem OrderedCoreBatch.of_isRotated {G : MGraph} {L : LSF} {β : ℕ} {ρ σ : Rotation G}
    (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G)
    (h : ∀ v, (σ.order v).IsRotated (ρ.order v)) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hG hF) [] :=
  ⟨trivial, graphEq_refl _, .nil (coreRotation_isRotated hG hF h)⟩

private theorem rotationBatch_append {β : ℕ} {G : MGraph} {U : List Update}
    {ρ : Rotation G} {σ : Rotation (G.applyBatch U)} (h : RotationBatch β U ρ σ)
    {W : List Update} {τ : Rotation ((G.applyBatch U).applyBatch W)}
    (hW : RotationBatch β W σ τ) :
    RotationBatch β (U ++ W) ρ ((applyBatch_append G U W).symm ▸ τ) := by
  induction h with
  | nil hρ => exact hW.rotate_before hρ
  | cons hs _ ih => exact .cons hs (ih hW)

/-- Ordered core batches concatenate by transporting the second batch across
live-edge agreement at the first batch's endpoint. -/
theorem OrderedCoreBatch.append {G H J : MGraph} {β : ℕ} {ρ : Rotation G} {σ : Rotation H}
    {τ : Rotation J} {U W : List Update}
    (hU : OrderedCoreBatch β ρ σ U) (hW : OrderedCoreBatch β σ τ W) :
    OrderedCoreBatch β ρ τ (U ++ W) := by
  obtain ⟨hvU, heU, hrU⟩ := hU
  obtain ⟨hvW, heW, hrW⟩ := hW
  have hh := graphEq_applyBatch heU W
  have hAll : GraphEq J (G.applyBatch (U ++ W)) := by
    rw [applyBatch_append]
    exact graphEq_trans heW hh
  refine ⟨batchIsValid_append.mpr ⟨hvU, (graphEq_batchIsValid heU W).mp hvW⟩, hAll, ?_⟩
  have hR := rotationBatch_append hrU (RotationBatch.congrGraph hrW heU)
  have hT : (τ.congrGraph heW).congrGraph hh = τ.congrGraph (graphEq_trans heW hh) := by
    rfl
  rw [hT] at hR
  rw [rotation_cast_congrGraph] at hR
  exact hR

end MinCostFlow.Bundle
