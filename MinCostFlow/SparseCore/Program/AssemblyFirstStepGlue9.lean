module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue7

import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.SparseCore.CoreModel
import MinCostFlow.SparseCore.SparseCoreHelpers
import Mathlib.Tactic

/-!
# The non-forest edges of an inactive component lie in its bundles (`AssemblyFirstStepGlue9`)

Phase 4 asks (`hInactiveBkts` of `asmFirstP4Sel_runs`) that for every inactive component `C`,
every edge of the graph of its forest state that is not a forest edge lies in the bundle of one
of the active buckets of `C`. At the start this is `initBundleTreeWith_extraEdges`. For a later
state we follow the same route. The edge is a core edge (`compLSF_comp_sdiff_sub`). Its core tail
is the root of its tail, and this root lies in `C` (`asmFirstInactive_root_mem`). So the bucket
of the edge is an active bucket of `C`, and the bundle of that bucket is the start bundle of the
core edges of the bucket (`AsmFirstInactiveCompInv`, `initBundleFor_edges`).

Why the root lies in `C`. The invariant of the inactive components says that the forest state
of `C` has one root. A forest state has the root `r₀` of its first tree among its roots, and its
roots are the roots inside the first graph together with the vertices that splits made
(`LSFState.R`). With one root, every vertex made by a split would be `r₀`, which lies in the
first graph, and the two sets are disjoint. So no split made a vertex, and the vertices of the
graph are those of the first graph, which is `C` (`asmFirstInactive_V_sub`). Hence the side
model already gives this fact, and no new field is needed.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart

public section

/-- **A forest state with one root has no vertex made by a split**: its vertices are those of
its first tree. The root `r₀` of the first tree is a root (it is in the seed `R₀_base`, whose
upward closure is `R_orig`). A vertex made by a split is a root too (`LSFState.R`), so with one
root it is `r₀`, which lies in the first tree. But the vertices made by splits are apart from
the first tree (`hdisj_iso`). -/
theorem lsfState_V_sub_of_card_R {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hR : S.R.card = 1) : S.G.V ⊆ S.T₀.V := by
  intro v hv
  rw [hI.hGV_eq] at hv
  rcases Finset.mem_union.mp hv with hT | hiso
  · exact hT
  · exfalso
    have hr₀ : S.r₀ ∈ S.R := Finset.mem_union_left _ (subset_upClosure hI.hr₀_base)
    have hvR : v ∈ S.R := Finset.mem_union_right _ hiso
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hR
    rw [ha, Finset.mem_singleton] at hr₀ hvR
    have hvT : v ∈ S.T₀.V := by
      rw [hvR, ← hr₀]
      exact hI.hR₀_sub hI.hr₀_base
    exact Finset.disjoint_left.mp hI.hdisj_iso hvT hiso

/-- **The vertices of an inactive component stay in it.** The forest state of `C` has one root
(`AsmFirstInactiveCompInv`), so its vertices are those of its first tree
(`lsfState_V_sub_of_card_R`), which are the vertices of its first graph (`hTV`), the graph of
`G₀` on `C` (`CompLSFInv.hCompLSF`). -/
theorem asmFirstInactive_V_sub
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (hCa : C ∉ tr.activeComps) :
    (tr.cs.compSt C).G.V ⊆ C := by
  obtain ⟨hIC, hG₀C, -⟩ := hI.hCompLSF C hC
  have hsub := lsfState_V_sub_of_card_R hIC (hInact C hC hCa).1
  rw [hIC.hTV, hG₀C] at hsub
  exact hsub

/-- **The root of a vertex of an inactive component lies in the component.** The root in the
whole forest is the root in the forest of `C` (`compLSF_RF_root_eq`), which is a root of that
forest (`rootedForest_root_spec`), hence a vertex of its graph (`lsfInv_R_sub_V`), hence in `C`
(`asmFirstInactive_V_sub`). -/
theorem asmFirstInactive_root_mem
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (hCa : C ∉ tr.activeComps)
    {v : ℕ} (hv : v ∈ (tr.cs.compSt C).G.V) : tr.cs.RF.root v ∈ C := by
  have hIC := (hI.hCompLSF C hC).1
  rw [compLSF_RF_root_eq hI hC hv]
  exact asmFirstInactive_V_sub hI hInact hC hCa
    (lsfInv_R_sub_V hIC (rootedForest_root_spec (lsfInv_to_RS hIC) hv).1)

/-- **`hInactiveBkts` of Phase 4.** For an inactive component `C`, an edge of the graph of its
forest state that is not a forest edge is a core edge (`compLSF_comp_sdiff_sub`) whose core tail
lies in `C`: its tail in the whole graph is its tail in the graph of `C`
(`CompLSFInv.compEnds_eq`), a vertex of that graph, whose root lies in `C`
(`asmFirstInactive_root_mem`). So its bucket is an active bucket of `C`, and the bundle of that
bucket has the core edges of the bucket (`AsmFirstInactiveCompInv`, `initBundleFor_edges`). -/
theorem asmFirstStep_inactiveBkts
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) {ρ : Rotation tr.cs.G} (hρ : ρ.order = ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y) :
    ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ e ∈ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E,
        ∃ b ∈ tr.activeBuckets C, e ∈ (tr.bun (C, b)).edges := by
  intro C hC hCa e he
  obtain ⟨-, hAB, -, -, hB⟩ := hInact C hC hCa
  have heCore : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E := compLSF_comp_sdiff_sub hI hC he
  have heG : e ∈ (tr.cs.compSt C).G.E := (Finset.mem_sdiff.mp he).1
  have hIC := (hI.hCompLSF C hC).1
  have hv : (tr.cs.compSt C).G.tail e ∈ (tr.cs.compSt C).G.V := (hIC.hG_val e heG).1
  rw [(hI.compEnds_eq hC heG).1] at hv
  have htail : (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C :=
    asmFirstInactive_root_mem hI hInact hC hCa hv
  have hb : tr.origBucket e ∈ tr.activeBuckets C := by
    rw [hAB]
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heCore, htail⟩, rfl⟩
  refine ⟨tr.origBucket e, hb, ?_⟩
  rw [← (hB _ hb).1.2.1, initBundleFor_edges hI hρ]
  unfold bucketCoreEdges
  exact Finset.mem_filter.mpr ⟨heCore, htail, rfl⟩

end

end MinCostFlow.SparseCore.Program
