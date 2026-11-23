module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue11

import Mathlib.Tactic

/-!
# Vertex-cap bounds for Phase 4 (`AssemblyFsOpenVerts`)

Proves the premise `hVerts` of `asmFirstStep_hP4` (`AssemblyFirstStepHP4.lean`),
showing from `AsmFsPre` that:
1. every vertex named by the input batch `A.U` (`batchVerts A.U`) lies below `A.x.vCap`,
2. every vertex named by the order edits `A.ed` (`ordEditVerts A.ed`) lies below `A.x.vCap`, and
3. every vertex in the Phase 4 rotation candidate set `asmFirstRotRawSet` lies below `A.x.vCap`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

private lemma applyBatch_V_sub (G : MGraph) (U : List Update) : G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u rest ih =>
    have h1 : G.V ⊆ (G.applyUpdate u).V := by cases u <;> simp [MGraph.applyUpdate]
    exact h1.trans (ih (G.applyUpdate u))

private lemma batchVerts_subset_applyBatch_V :
    ∀ (G : MGraph) (U : List Update), G.BatchIsValid U → batchVerts U ⊆ (G.applyBatch U).V
  | _, [], _ => Finset.empty_subset _
  | G, u :: rest, ⟨hu, hrest⟩ => by
    have hsub : (G.applyUpdate u).V ⊆ ((G.applyUpdate u).applyBatch rest).V :=
      applyBatch_V_sub _ _
    have hsub0 : G.V ⊆ (G.applyUpdate u).V := by cases u <;> simp [MGraph.applyUpdate]
    have h1 : updVerts u ⊆ ((G.applyUpdate u).applyBatch rest).V := by
      cases u with
      | insert e a b =>
        intro v hv
        simp only [updVerts, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hsub (hsub0 hu.2.1)
        · exact hsub (hsub0 hu.2.2)
      | delete e => exact Finset.empty_subset _
      | split v v' St Sh =>
        intro x hx
        simp only [updVerts, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hsub (hsub0 hu.1)
        · exact hsub (by simp [MGraph.applyUpdate])
    have h2 : batchVerts rest ⊆ ((G.applyUpdate u).applyBatch rest).V :=
      batchVerts_subset_applyBatch_V (G.applyUpdate u) rest hrest
    exact Finset.union_subset h1 h2

private lemma ordEditVerts_lt_of_within {vCap eCap : ℕ} :
    ∀ {ed : List OrdEdit}, OrdEditsWithin vCap eCap ed → ∀ v ∈ ordEditVerts ed, v < vCap
  | [], _, _, hv => by simp [ordEditVerts] at hv
  | d :: ds, hw, v, hv => by
    have hd := hw d List.mem_cons_self
    have hds : OrdEditsWithin vCap eCap ds := fun x hx => hw x (List.mem_cons_of_mem d hx)
    rcases Finset.mem_union.mp hv with h1 | h2
    · cases d with
      | dropEdge _ => simp [OrdEdit.verts] at h1
      | moveEnds a b _ _ =>
        simp only [OrdEdit.verts, Finset.mem_insert, Finset.mem_singleton] at h1
        rcases h1 with rfl | rfl
        · exact hd.1
        · exact hd.2.1
      | insertBefore a _ _ =>
        simp only [OrdEdit.verts, Finset.mem_singleton] at h1
        subst h1; exact hd.1
      | rotateTo a _ =>
        simp only [OrdEdit.verts, Finset.mem_singleton] at h1
        subst h1; exact hd.1
    · exact ordEditVerts_lt_of_within hds v h2

private lemma coreBatchSplitPairs_mem_applyBatch_V :
    ∀ (G : MGraph) (U : List Update), G.BatchIsValid U →
      ∀ p ∈ coreBatchSplitPairs U, p.1 ∈ (G.applyBatch U).V ∧ p.2 ∈ (G.applyBatch U).V
  | _, [], _, _, hp => by simp [coreBatchSplitPairs] at hp
  | G, u :: rest, ⟨hu, hrest⟩, p, hp => by
    have hsub : (G.applyUpdate u).V ⊆ ((G.applyUpdate u).applyBatch rest).V :=
      applyBatch_V_sub _ _
    have hsub0 : G.V ⊆ (G.applyUpdate u).V := by cases u <;> simp [MGraph.applyUpdate]
    cases u with
    | insert e a b =>
      exact coreBatchSplitPairs_mem_applyBatch_V (G.applyUpdate (.insert e a b)) rest hrest p hp
    | delete e =>
      exact coreBatchSplitPairs_mem_applyBatch_V (G.applyUpdate (.delete e)) rest hrest p hp
    | split v v' St Sh =>
      simp only [coreBatchSplitPairs, List.filterMap] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨hsub (hsub0 hu.1), hsub (by simp [MGraph.applyUpdate])⟩
      · exact coreBatchSplitPairs_mem_applyBatch_V (G.applyUpdate (.split v v' St Sh)) rest hrest
          p hp'

private lemma rootedForest_root_lt {vCap : ℕ} {RF : RootedForest}
    (hR : ∀ r ∈ RF.R, r < vCap) {u : ℕ} (hu : u < vCap) : RF.root u < vCap := by
  unfold RootedForest.root
  split_ifs with h
  · exact hR _ (Classical.choose_spec h).1
  · exact hu

public section

/-- **Proof of the premise `hVerts` of `asmFirstStep_hP4`**
(`AssemblyFirstStepHP4.lean`): under `AsmFsPre`, every vertex in `batchVerts A.U`,
`ordEditVerts A.ed`, and `asmFirstRotRawSet` lies below `A.x.vCap`. -/
theorem asmFirstStep_hVerts {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {space : ℕ → ℕ} :
    ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      (∀ v ∈ batchVerts A.U, v < A.x.vCap) ∧ (∀ v ∈ ordEditVerts A.ed, v < A.x.vCap) ∧
      ∀ v ∈ asmFirstRotRawSet (fun _ => canonicalSparsify impl) A.tr A.U A.ord A.ed,
        v < A.x.vCap := by
  intro A hA
  unfold AsmFsPre AsmFsPreRaw at hA
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, hFacts, -, hU, -, -, -, hOVF, -⟩ := hA
  have hOld := asmBrModelFacts_of_rep hR
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -, -⟩, -⟩ := hOld
  have hGV' : ∀ v ∈ (compLSFBatch A.tr.cs A.U).G.V, v < A.x.vCap :=
    hFacts.2.2.2.2.2.2.2.1
  have hRoots' : ∀ r ∈ (compLSFBatch A.tr.cs A.U).RF.R, r < A.x.vCap :=
    asmBr_newRoots_lt (fun _ => canonicalSparsify impl) hFacts
  have hVU : ∀ v ∈ batchVerts A.U, v < A.x.vCap := by
    intro v hv
    have hvG : v ∈ (A.tr.cs.G.applyBatch A.U).V := batchVerts_subset_applyBatch_V A.tr.cs.G A.U hU hv
    rw [← compLSFBatch_G A.tr.cs A.U] at hvG
    exact hGV' v hvG
  have hVE : ∀ v ∈ ordEditVerts A.ed, v < A.x.vCap :=
    ordEditVerts_lt_of_within hOVF.1
  refine ⟨hVU, hVE, ?_⟩
  intro v hv
  unfold asmFirstRotRawSet at hv
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset,
    List.mem_map, Finset.mem_insert, Finset.mem_singleton] at hv
  have hSplits : ∀ s ∈ canonSplitList A.tr.cs A.U,
      s.kept ∈ (compLSFBatch A.tr.cs A.U).RF.R ∧ s.fresh ∈ (compLSFBatch A.tr.cs A.U).RF.R := by
    intro s hs
    obtain ⟨hUC_val, hGEq, -⟩ := canonCoreBatch_valid_and_graphEq hI hU
    have hp_mem : (s.kept, s.fresh) ∈ coreBatchSplitPairs (canonCoreBatch A.tr.cs A.U) := by
      rw [canonSplitList_eq_coreSplits A.tr.cs A.U]
      exact List.mem_map.mpr ⟨s, hs, rfl⟩
    have hV := coreBatchSplitPairs_mem_applyBatch_V
      (coreGraph A.tr.cs.G A.tr.cs.lsf) (canonCoreBatch A.tr.cs A.U) hUC_val (s.kept, s.fresh) hp_mem
    have hR_eq : ((coreGraph A.tr.cs.G A.tr.cs.lsf).applyBatch (canonCoreBatch A.tr.cs A.U)).V =
        (compLSFBatch A.tr.cs A.U).RF.R := hGEq.1.symm
    rw [hR_eq] at hV
    exact hV
  rcases hv with (((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨e, he, rfl | rfl⟩) | ⟨u, hu, rfl⟩)
  · exact hRoots' _ (hSplits s hs).1
  · exact hRoots' _ (hSplits s hs).2
  · have heG : e ∈ (compLSFBatch A.tr.cs A.U).G.E :=
      outInsSet_subset_G (fun _ => canonicalSparsify impl) A.tr A.U A.ord (applyOrdEdits A.ord A.ed)
        hFacts.2.2.1 e he
    obtain ⟨C', ℓ', hI', -, -⟩ := hFacts.2.1
    exact rootedForest_root_lt hRoots' (hGV' _ (hI'.hG_val e heG).1)
  · have heG : e ∈ (compLSFBatch A.tr.cs A.U).G.E :=
      outInsSet_subset_G (fun _ => canonicalSparsify impl) A.tr A.U A.ord (applyOrdEdits A.ord A.ed)
        hFacts.2.2.1 e he
    obtain ⟨C', ℓ', hI', -, -⟩ := hFacts.2.1
    exact rootedForest_root_lt hRoots' (hGV' _ (hI'.hG_val e heG).2)
  · rcases hu with hu | hu
    · exact rootedForest_root_lt hRoots' (hVU u hu)
    · exact rootedForest_root_lt hRoots' (hVE u hu)

end

end MinCostFlow.SparseCore.Program
