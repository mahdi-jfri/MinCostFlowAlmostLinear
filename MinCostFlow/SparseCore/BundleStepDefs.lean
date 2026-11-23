module

public import MinCostFlow.SparseCore.CompLSFOrderedCore
public import MinCostFlow.SparseCore.CompLSFCoreLocal
public import MinCostFlow.Bundle.Bounds
import MinCostFlow.Bundle.SplitValid
import MinCostFlow.SparseCore.CoreModel

/-!
# The specification of the bundle step of one component

The spanner of a component of the initial graph runs on the bundle graph of that component. Its
bundles are arcs of the tours of the global core graph, with the input rotation. A batch of the
component-wise LSF changes the global core graph by an ordered core batch
(`orderedCore_compLSFBatch`). Running the bundle step through that batch gives the new bundles and
the batch for the bundle graph (`bundleBatch_spec`).

The core batch and the bundle batch exist (`bundleStepSpec_exists`). The
specification counts at most two bundle splits per new root and at most one deletion per input
update. No degree enters. The step itself, which computes its
result from the core rotation after the batch, is in `BundleCompStep.lean`. Its proof uses the
pair that exists here only to compare counts.

The count is also local (`BundleStepLocalSpec`). The bundles of one component have their parents
among the roots of that component. A core split never moves ends between components
(`orderedCore_compLSFBatch_local`), so these bundles split at most twice per new root of their
own component, and they lose only their own edges, at deletions of the input batch.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- The hypotheses of the bundle step: the component-wise LSF satisfies its invariant, the given
orders are rotations of the graph before and after the batch with split bound two, the batch is
valid, and the bundles form a partition for the core rotation before the batch. -/
@[expose] def BundleStepReady (cs : CompLSFState) (B : BundleState) (k : ℕ)
    (ord ord' : ℕ → List End) (U : List Update) : Prop :=
  ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (hI : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G)
    (σ : Rotation (cs.G.applyBatch U)),
    ρ.order = ord ∧ σ.order = ord' ∧ RotationBatch 2 U ρ σ ∧ cs.G.BatchIsValid U ∧
    B.IsPartition (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) k

/-- The specification of the bundle step: the new bundles form
a partition for the core rotation after the batch, the bundle batch is valid and has only
deletions and splits, with at most two splits per new root and one deletion per update. -/
@[expose] def BundleStepSpec (cs : CompLSFState) (B : BundleState) (k : ℕ) (ord' : ℕ → List End)
    (U : List Update) (UB : List Update) (B' : BundleState) : Prop :=
  (∀ (σ : Rotation (compLSFBatch cs U).G) (hG : (compLSFBatch cs U).G.IsValid)
      (hF : (compLSFBatch cs U).RF.IsRootedSpanningForestOf (compLSFBatch cs U).G),
      σ.order = ord' →
      B'.IsPartition (coreRotation (L := (compLSFBatch cs U).lsf) σ hG hF) k) ∧
  B.graph.BatchIsValid UB ∧ B'.graph = B.graph.applyBatch UB ∧
  (∀ op ∈ UB, isDelOrSplit op) ∧
  batchSplitCount UB ≤ 2 * ((compLSFBatch cs U).RF.R \ cs.RF.R).card ∧
  UB.countP deleteTag ≤ U.length ∧
  B'.vertices.card = B.vertices.card + batchSplitCount UB

/-- The local part of the specification of the bundle step. If the bundles have their parents among
the roots of a component `C`, then they split at most twice per new root of `C`, and afterwards
their parents are roots of `C` again. Every bundle deletion deletes an old bundle edge that the
input batch deletes, and the bundle edges only shrink: they lose exactly the edges that the input
batch deletes. A component without new roots and without deletions of bundle edges leaves the
bundles unchanged. -/
@[expose] def BundleStepLocalSpec (cs : CompLSFState) (B : BundleState) (U : List Update)
    (UB : List Update) (B' : BundleState) : Prop :=
  (∀ C ∈ components cs.G₀, (∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R) →
    batchSplitCount UB ≤ 2 * (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card ∧
    ∀ b ∈ B'.vertices, B'.parent b ∈ ((compLSFBatch cs U).compSt C).R) ∧
  (∀ op ∈ UB, deleteTag op = true → ∃ e ∈ B.edges, op = .delete e ∧ e ∈ batchDeletes U) ∧
  B'.edges ⊆ B.edges ∧ B'.edges = B.edges \ batchDeletes U ∧
  (∀ C ∈ components cs.G₀, (∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R) →
    ((compLSFBatch cs U).compSt C).R = (cs.compSt C).R → Disjoint B.edges (batchDeletes U) →
    UB = [] ∧ B' = B)

private theorem partition_of_congrGraph' {G H : MGraph} {ρ : Rotation G} {B : BundleState}
    {k : ℕ} (he : GraphEq G H) (h : B.IsPartition (ρ.congrGraph he) k) :
    B.IsPartition ρ k := by
  have hE : B.edges ⊆ G.E := by simpa only [he.2.1] using h.1
  refine ⟨hE, ?_, ?_, h.2.2.2⟩
  · simpa only [he.1] using h.2.1
  · intro x hx
    obtain ⟨hb, hp⟩ := h.2.2.1 x hx
    obtain ⟨ht, hh⟩ := he.2.2 x.1 (hE ((mem_edgeEnds _ _).mp hx))
    refine ⟨hb, hp.trans ?_⟩
    rcases x with ⟨e, side⟩
    cases side
    · exact hh.symm
    · exact ht.symm

private theorem cast_order {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h
  rfl

/-- New roots in the vertex set of a component state are new roots of that component. -/
private theorem newRoots_inter_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs cs' : CompLSFState}
    (hI' : CompLSFInv C_lsst ℓ₀ cs') (hG₀ : cs'.G₀ = cs.G₀) {C : Finset ℕ}
    (hC : C ∈ components cs.G₀) :
    (cs'.RF.R \ cs.RF.R) ∩ (cs'.compSt C).G.V ⊆ (cs'.compSt C).R \ (cs.compSt C).R := by
  intro w hw
  obtain ⟨hw₁, hwV⟩ := Finset.mem_inter.mp hw
  obtain ⟨hwR, hwR₀⟩ := Finset.mem_sdiff.mp hw₁
  change w ∈ (components cs'.G₀).biUnion (fun D => (cs'.compSt D).R) at hwR
  obtain ⟨D, hD, hwD⟩ := Finset.mem_biUnion.mp hwR
  have hC' : C ∈ components cs'.G₀ := hG₀ ▸ hC
  have hDC : D = C := by
    by_contra hne
    exact Finset.disjoint_left.mp (hI'.hV_disj D hD C hC' hne)
      (lsfInv_R_sub_V (hI'.hCompLSF D hD).1 hwD) hwV
  subst hDC
  refine Finset.mem_sdiff.mpr ⟨hwD, fun h => hwR₀ ?_⟩
  change w ∈ (components cs.G₀).biUnion (fun D => (cs.compSt D).R)
  exact Finset.mem_biUnion.mpr ⟨D, hC, h⟩

/-- Under its hypotheses the bundle step has a result that meets its specification, with the
local count. -/
theorem bundleStepSpec_exists {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    ∃ p : List Update × BundleState,
      BundleStepSpec cs B k ord' U p.1 p.2 ∧ BundleStepLocalSpec cs B U p.1 p.2 := by
  obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, _, hσ, hrot, hU, hB⟩ := h
  obtain ⟨he, hI', UC, ⟨hv, hge, hrb⟩, hc, hd, hl, hdel, hin⟩ :=
    orderedCore_compLSFBatch_local (C_lsst := C_lsst) (ℓ₀ := ℓ₀) hrot (Nat.le_refl 2) hU cs rfl hI
  obtain ⟨UB, B', hp, hvalid, hgraph, htypes, hsplits, hdels, hgrowth, hE, hD, hR, hK, hL⟩ :=
    bundleBatch_spec_local hrb B hB hv
  have hG₀ : (compLSFBatch cs U).G₀ = cs.G₀ := compLSFBatch_G₀ cs U
  have hC' : ∀ C ∈ components cs.G₀, C ∈ components (compLSFBatch cs U).G₀ :=
    fun C hC => hG₀ ▸ hC
  have hX : ∀ C ∈ components cs.G₀, (∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R) →
      ∀ b ∈ B.vertices, B.parent b ∈ ((compLSFBatch cs U).compSt C).G.V :=
    fun C hC hpar b hb =>
      compLSFBatch_compSt_V_subset hI hU hC (lsfInv_R_sub_V (hI.hCompLSF C hC).1 (hpar b hb))
  have hcl : ∀ C ∈ components cs.G₀, ∀ op ∈ UC, ∀ v v' St Sh, op = .split v v' St Sh →
      v ∈ ((compLSFBatch cs U).compSt C).G.V → v' ∈ ((compLSFBatch cs U).compSt C).G.V := by
    intro C hC op hop v v' St Sh hop' hvX
    obtain ⟨D, hD, hvD, hv'D⟩ := hl op hop v v' St Sh hop'
    have hDC : D = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI'.hV_disj D hD C (hC' C hC) hne) hvD hvX
    subst hDC
    exact hv'D
  have hVfin : ∀ C ∈ components cs.G₀,
      (((coreGraph cs.G cs.lsf).applyBatch UC).V \ (coreGraph cs.G cs.lsf).V) ∩
        ((compLSFBatch cs U).compSt C).G.V ⊆
        ((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R := by
    intro C hC
    rw [← hge.1]
    exact newRoots_inter_le hI' hG₀ hC
  refine ⟨(UB, B'), ⟨?_, hvalid, hgraph, htypes, ?_, ?_, hgrowth⟩, ?_, ?_, hE, ?_, ?_⟩
  · intro σ' hG hF hσ'
    have hP := partition_of_congrGraph' hge hp
    have hrot' : σ' = he.symm ▸ σ := Rotation.ext_order (by rw [cast_order, hσ, hσ'])
    subst hrot'
    exact hP
  · exact hsplits.trans (Nat.le_of_eq (by rw [hc]))
  · exact hdels.trans (hd.trans (Nat.le_refl _))
  · intro C hC hpar
    let X := ((compLSFBatch cs U).compSt C).G.V
    obtain ⟨hpar', hcount, -⟩ := hL X (hX C hC hpar) (hcl C hC)
    refine ⟨hcount.trans (Nat.mul_le_mul_left 2 ((countP_splitNewIn_le hv X).trans
      (Finset.card_le_card (hVfin C hC)))), ?_⟩
    intro b hb
    have hbR : B'.parent b ∈ (compLSFBatch cs U).RF.R := by
      have h1 := hp.2.1 b hb
      rw [← hge.1] at h1
      exact h1
    have hbX := hpar' b hb
    change B'.parent b ∈ (components (compLSFBatch cs U).G₀).biUnion
      (fun D => ((compLSFBatch cs U).compSt D).R) at hbR
    obtain ⟨D, hD, hbD⟩ := Finset.mem_biUnion.mp hbR
    have hDC : D = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI'.hV_disj D hD C (hC' C hC) hne)
        (lsfInv_R_sub_V (hI'.hCompLSF D hD).1 hbD) hbX
    subst hDC
    exact hbD
  · intro op hop hdt
    obtain ⟨e, heB, rfl, hmem⟩ := hD op hop hdt
    exact ⟨e, heB, rfl, hdel _ hmem e rfl⟩
  · ext e
    simp only [Finset.mem_sdiff]
    constructor
    · intro he'
      refine ⟨hE he', fun hd => hK e (hin e hd (hB.1 (hE he'))) he'⟩
    · rintro ⟨he, hnd⟩
      by_contra hn
      exact hnd (hdel _ (hR e he hn) e rfl)
  · intro C hC hpar hRC hdisj
    let X := ((compLSFBatch cs U).compSt C).G.V
    obtain ⟨-, -, hun⟩ := hL X (hX C hC hpar) (hcl C hC)
    refine hun (fun op hop => ?_) (fun e he hmem => ?_)
    · have hle := (countP_splitNewIn_le hv X).trans (Finset.card_le_card (hVfin C hC))
      rw [hRC, Finset.sdiff_self, Finset.card_empty, Nat.le_zero, List.countP_eq_zero] at hle
      simpa using hle op hop
    · exact Finset.disjoint_left.mp hdisj he (hdel _ hmem e rfl)

end MinCostFlow.SparseCore
