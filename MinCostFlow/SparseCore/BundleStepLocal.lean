module

public import MinCostFlow.SparseCore.BundleCompStep

/-!
# The local count of the bundle step

The bundle state of a component `C` of the initial graph changes by `bundleCompStep` along the
global ordered core batch. The specification `BundleStepSpec` counts the bundle splits against
all new roots and the deletions against the whole batch. Summed over the components this would
lose a factor of the number of components. The step is local, however: its bundles have their
parents among the roots of `C`, a core split never moves ends between components, and a bundle
deletion deletes a bundle edge. So the bundles of `C` split at most twice per new root of `C`, and
they delete only their own edges, at deletions of the input batch.

The proof is `BundleStepLocalSpec`, which `bundleCompStep` meets by its choice
(`bundleCompStep_localSpec`).
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- The local count of the bundle step. If every bundle of `B` has its
parent among the roots of the component `C`, then the bundle batch has at most two splits per new
root of `C`, and every deletion of the bundle batch deletes an edge of `B` that the input batch
deletes. -/
theorem bundleCompStep_local {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U)
    (C : Finset ℕ) (hCmem : C ∈ components cs.G₀)
    (hC : ∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R) :
    let out := bundleCompStep cs B k ord ord' U
    batchSplitCount out.1 ≤ 2 * (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card ∧
    (∀ op ∈ out.1, deleteTag op = true → ∃ e ∈ B.edges, op = .delete e ∧ e ∈ batchDeletes U) :=
  let hs := bundleCompStep_localSpec h
  ⟨(hs.1 C hCmem hC).1, hs.2.1⟩

/-- After the bundle step the bundles of `C` have their parents among the roots of `C` again, and
the bundle edges only shrink. -/
theorem bundleCompStep_local_state {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U)
    (C : Finset ℕ) (hCmem : C ∈ components cs.G₀)
    (hC : ∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R) :
    let out := bundleCompStep cs B k ord ord' U
    (∀ b ∈ out.2.vertices, out.2.parent b ∈ ((compLSFBatch cs U).compSt C).R) ∧
    out.2.edges ⊆ B.edges :=
  let hs := bundleCompStep_localSpec h
  ⟨(hs.1 C hCmem hC).2, hs.2.2.1⟩

/-- The bundle step removes exactly the bundle edges that the input batch deletes. -/
theorem bundleCompStep_edges_eq {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    (bundleCompStep cs B k ord ord' U).2.edges = B.edges \ batchDeletes U :=
  (bundleCompStep_localSpec h).2.2.2.1

/-- A component without new roots, whose bundle edges the input batch does not delete, keeps its
bundles. -/
theorem bundleCompStep_unchanged {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U)
    (C : Finset ℕ) (hCmem : C ∈ components cs.G₀)
    (hC : ∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R)
    (hR : ((compLSFBatch cs U).compSt C).R = (cs.compSt C).R)
    (hdisj : Disjoint B.edges (batchDeletes U)) :
    bundleCompStep cs B k ord ord' U = ([], B) := by
  obtain ⟨h1, h2⟩ := (bundleCompStep_localSpec h).2.2.2.2 C hCmem hC hR hdisj
  exact Prod.ext h1 h2

/-- A batch of deletions and splits never adds an edge. -/
private theorem applyBatch_E_subset_of_delOrSplit {G : MGraph} {V : List Update}
    (hV : ∀ op ∈ V, isDelOrSplit op) : (G.applyBatch V).E ⊆ G.E := by
  induction V generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u V ih =>
    refine (ih (fun op hop => hV op (List.mem_cons_of_mem _ hop))).trans ?_
    have hu := hV u List.mem_cons_self
    cases u with
    | insert => exact hu.elim
    | delete e => exact Finset.erase_subset _ _
    | split => exact Finset.Subset.rfl

/-- A valid batch of deletions and splits deletes every edge at most once. -/
theorem nodup_deletes_of_delOrSplit {G : MGraph} {V : List Update} (hv : G.BatchIsValid V)
    (hV : ∀ op ∈ V, isDelOrSplit op) : (V.filter fun op => deleteTag op).Nodup := by
  induction V generalizing G with
  | nil => simp
  | cons u V ih =>
    have hV' : ∀ op ∈ V, isDelOrSplit op := fun op hop => hV op (List.mem_cons_of_mem _ hop)
    have hrest := ih hv.2 hV'
    cases u with
    | insert => simpa [deleteTag] using hrest
    | split => simpa [deleteTag] using hrest
    | delete e =>
      simp only [List.filter_cons, deleteTag, ↓reduceIte, List.nodup_cons]
      refine ⟨fun hmem => ?_, hrest⟩
      have hmem' := (List.mem_filter.mp hmem).1
      obtain ⟨V₁, V₂, rfl⟩ := List.append_of_mem hmem'
      have hv₂ := (batchIsValid_append.mp hv.2).2
      have hsub := applyBatch_E_subset_of_delOrSplit (G := G.applyUpdate (.delete e))
        (V := V₁) (fun op hop => hV' op (List.mem_append_left _ hop))
      have he := hsub hv₂.1
      exact (Finset.notMem_erase e G.E) he

/-- The number of deletions of the bundle batch is at most the number of edges of `B` that the
input batch deletes. -/
theorem bundleCompStep_deletes_le {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    (bundleCompStep cs B k ord ord' U).1.countP deleteTag ≤ (B.edges ∩ batchDeletes U).card := by
  classical
  have hspec := bundleCompStep_spec h
  have hloc := (bundleCompStep_localSpec h).2.1
  have hnd := nodup_deletes_of_delOrSplit hspec.2.1 hspec.2.2.2.1
  let f : Update → ℕ := fun op => match op with | .delete e => e | _ => 0
  have hinj : ∀ a ∈ ((bundleCompStep cs B k ord ord' U).1.filter fun op => deleteTag op).toFinset,
      ∀ b ∈ ((bundleCompStep cs B k ord ord' U).1.filter fun op => deleteTag op).toFinset,
      f a = f b → a = b := by
    intro a ha b hb hab
    have ha' := List.mem_filter.mp (List.mem_toFinset.mp ha)
    have hb' := List.mem_filter.mp (List.mem_toFinset.mp hb)
    obtain ⟨e, -, rfl, -⟩ := hloc a ha'.1 ha'.2
    obtain ⟨e', -, rfl, -⟩ := hloc b hb'.1 hb'.2
    simp only [f] at hab
    rw [hab]
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnd,
    ← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨op, hop, rfl⟩ := Finset.mem_image.mp hx
  have hop' := List.mem_filter.mp (List.mem_toFinset.mp hop)
  obtain ⟨e, he, rfl, hdel⟩ := hloc op hop'.1 hop'.2
  exact Finset.mem_inter.mpr ⟨he, hdel⟩

end MinCostFlow.SparseCore
