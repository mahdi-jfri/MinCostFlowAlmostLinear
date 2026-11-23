module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSideInv
public import MinCostFlow.SparseCore.Program.ContractOrder
public import MinCostFlow.SparseCore.BundleStageBase

import MinCostFlow.SparseCore.Program.BundleModelBridgeStep
import MinCostFlow.SparseCore.SplitSpannerBase
import MinCostFlow.SparseCore.LSFInit

/-!
# Three bundle-side invariants: init, restart, step, `GraphEq` bridges, and a counterexample

Establishes three invariants of `AsmBrSideModel` (`AssemblyBranchSideInv.lean`,
`AssemblyBranchSide.lean`):
* **The inactive invariant** (`AsmFirstInactiveDynInv`): for every still-inactive component `C` and active bucket
  `b`, `tr.dyn (C, b) = DSHist.state (asmBrSP impl w depth y) ⟨tr.initBunG (C, b), []⟩`.
* **The partition invariant** (`AsmFirstActiveBunPartInv`): for every active `(C, b)`, `tr.bun (C, b)` is a
  `tr.k`-bundle partition for the core rotation of every rotation of `tr.cs.G` with order `ord`.
* **The graph invariant** (`AsmFirstActiveDynGraphInv`, stated with `GraphEq`, not with `=`): for
  every active
  `(C, b)`, `GraphEq (tr.dyn (C, b)).G (tr.bun (C, b)).graph`.

Proves:
1. Init (`asmFirstInactiveDynInv_init`, `asmFirstActiveBunPartInv_init`,
   `asmFirstActiveDynGraphInv_init`),
2. Restart (`asmFirstInactiveDynInv_restart`, `asmFirstActiveBunPartInv_restart`,
   `asmFirstActiveDynGraphInv_restart`),
3. Step preservation across `stepBundleTree` (`asmFirstInactiveDynInv_step`,
   `asmFirstActiveBunPartInv_step`, `asmFirstActiveDynGraphInv_step`),
4. `GraphEq` congruence lemmas for `BunAgree`, `UpdateAt`, `BatchBodyAt`, `BatchAt`, and
   `SmallBatchAt` (`bunAgree_graphEq`, `updateAt_of_graphEq`, `batchBodyAt_of_graphEq`,
   `batchAt_of_graphEq`, `smallBatchAt_of_graphEq`), plus `asmFirstActiveDynGraphInv_E` and
   `asmFirstActiveDynGraphInv_normEq`,
5. A formal counterexample (`raw_s8c_counterexample_exists`) proving that raw record equality
   `(tr.dyn (C, b)).G = normGraph (tr.bun (C, b)).graph` fails after a single valid ordered
   `stepBundleTree` edge deletion from `initBundleTreeWithParams` (because
   `MGraph.applyUpdate (.delete e)` leaves `tail e`/`head e` unchanged outside `E`, whereas
   `normGraph` zeros them).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

public section

/-! ## 1. Helper lemmas for `initBundleFor` and inactive components -/

/-- `initBundleFor cs ord E k` is a `k`-bundle partition for the core rotation of every rotation
`ρ` of `cs.G` with order `ord`, whenever `E ⊆ (coreGraph cs.G cs.lsf).E` and `0 < k`. -/
theorem initBundleFor_isPartition {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {ord : ℕ → List End} {E : Finset ℕ} {k : ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G) (hρ : ρ.order = ord)
    (hE : E ⊆ (coreGraph cs.G cs.lsf).E) (hk : 0 < k) :
    (initBundleFor cs ord E k).IsPartition
      (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) k := by
  rw [initBundleFor_eq hI hρ E k]
  exact initBundleState_inv _ (coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)) hE hk

/-- For a still-inactive component `C` satisfying `AsmFirstInactiveCompInv` and
`AsmFirstCrossInactiveInv`, every bucket core-edge set `bucketCoreEdges ... C b` lies in
`(tr.cs.compSt C).G.E` and avoids `tr.cs.crossEdges`. -/
private theorem inactive_bucketCoreEdges_sub_compE {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} {C : Finset ℕ} {b : ℤ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hC : C ∈ components tr.cs.G₀) (hNotAct : C ∉ tr.activeComps)
    (hCross : AsmFirstCrossInactiveInv tr) :
    let Eq := bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b
    Eq ⊆ (tr.cs.compSt C).G.E ∧ ∀ e ∈ Eq, e ∉ tr.cs.crossEdges := by
  classical
  intro Eq
  have hC_sub_V : C ⊆ (tr.cs.compSt C).G.V := by
    have hLC := (hI.hCompLSF C hC).1
    have hG0C : (tr.cs.compSt C).G₀ = compGraph tr.cs.G₀ C := (hI.hCompLSF C hC).2.1
    intro u hu
    have hu0 : u ∈ (tr.cs.compSt C).G₀.V := by rw [hG0C]; exact hu
    rw [hLC.hGV_eq]
    exact Finset.mem_union_left _ (hLC.hTV.symm ▸ hu0)
  have hCr := hCross C hC hNotAct
  have hsub : ∀ e ∈ Eq, e ∈ (tr.cs.compSt C).G.E ∧ e ∉ tr.cs.crossEdges := by
    intro e he
    obtain ⟨heCore, htC, -⟩ := Finset.mem_filter.mp he
    have heG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp heCore).1
    have ht_root : tr.cs.RF.root (tr.cs.G.tail e) ∈ (tr.cs.compSt C).G.V := hC_sub_V htC
    have htV : tr.cs.G.tail e ∈ (tr.cs.compSt C).G.V :=
      compLSF_mem_V_of_root hI hC (hI.hG_val e heG).1 ht_root
    have hnc : e ∉ tr.cs.crossEdges := fun hcr => (hCr.2 e hcr).1 htV
    obtain ⟨C', hC', heC'⟩ := hI.hEdge_cover e heG hnc
    have hends := hI.hNonCross_ends C' hC' e heC' hnc
    have hvC' := (hI.hCompLSF C' hC').1.hG_val e heC'
    have hEqC : C' = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj C' hC' C hC hne) (hends.1 ▸ hvC'.1) htV
    subst hEqC
    exact ⟨heC', hnc⟩
  exact ⟨fun e he => (hsub e he).1, fun e he => (hsub e he).2⟩

/-- Every pair `(C, b)` of a still-inactive component `C` satisfies `BundleCompReady` under
`AsmFirstInactiveCompInv`, `AsmFirstCrossInactiveInv`, `CompLSFInv`, and `1 ≤ tr.k`. -/
theorem inactive_bundleCompReady
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {y : AsmBrSide B5 depth}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hk : 1 ≤ tr.k)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hCross : AsmFirstCrossInactiveInv tr)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (hNotAct : C ∉ tr.activeComps)
    {b : ℤ} (hb : b ∈ tr.activeBuckets C) :
    BundleCompReady tr.cs C (tr.bun (C, b)) tr.k ord := by
  classical
  set Eq := bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b with hEq_def
  have hEcore : Eq ⊆ (coreGraph tr.cs.G tr.cs.lsf).E := Finset.filter_subset _ _
  obtain ⟨hEC, hNotCr⟩ := inactive_bucketCoreEdges_sub_compE (b := b) hI hC hNotAct hCross
  have hAg : BunAgree (initBundleFor tr.cs ord Eq tr.k) (tr.bun (C, b)) :=
    ((hInact C hC hNotAct).2.2.2.2 b hb).1
  refine ⟨?_, ?_, ?_⟩
  · intro ρ _ _ hρ
    exact (bunAgree_isPartition_iff hAg).mp (initBundleFor_isPartition hI ρ hρ hEcore hk)
  · intro v hv
    have hv0 : v ∈ (initBundleFor tr.cs ord Eq tr.k).vertices := hAg.1.symm ▸ hv
    rw [← hAg.2.2.1]
    by_cases hex : ∃ (C' : ℝ) (ℓ' : ℕ → ℝ) (_ : CompLSFInv C' ℓ' tr.cs) (ρ : Rotation tr.cs.G),
        ρ.order = ord
    · obtain ⟨_, _, _, ρ, hρ⟩ := hex
      rw [initBundleFor_eq hI hρ Eq tr.k] at hv0 ⊢
      exact initBundleState_parent_mem hI hC _ hEcore hEC hNotCr tr.k v hv0
    · unfold initBundleFor at hv0
      rw [dite_eq_right hex] at hv0
      cases hv0
  · rw [← hAg.2.1]
    have hSub : (initBundleFor tr.cs ord Eq tr.k).edges ⊆ Eq := by
      unfold initBundleFor
      split_ifs
      · exact Finset.Subset.refl _
      · exact Finset.empty_subset _
    exact hSub.trans hEC

/-! ## 2. Init lemmas (the three invariants) -/

/-- **The inactive invariant at init**: `initBundleTreeWithParams` satisfies `AsmFirstInactiveDynInv` whenever
`y.splitB = bundleSplitBudget k M`. -/
theorem asmFirstInactiveDynInv_init
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w : ℕ) (lsfInit : LSFInit) (depth : ℕ)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) (y : AsmBrSide B5 depth)
    (hSB : y.splitB = bundleSplitBudget k M) :
    AsmFirstInactiveDynInv impl w depth
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl) params spanConst
        k M N G₀ ℓ₀ ord j) y := by
  intro C _ _ b _
  unfold initBundleTreeWithParams DSHist.state DSHist.q asmBrSP
  simp only [hSB, DSHist.flat, List.flatten_nil, List.length_nil]
  rfl

/-- **The partition invariant at init**: `initBundleTreeWithParams` satisfies `AsmFirstActiveBunPartInv` for `k ≥ 1`. -/
theorem asmFirstActiveBunPartInv_init (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) (hk : 1 ≤ k) :
    AsmFirstActiveBunPartInv
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord j) ord := by
  intro C _ b _ C_lsst ℓ' hI ρ hρ
  exact initBundleFor_isPartition hI ρ hρ (Finset.filter_subset _ _) hk

/-- **The graph invariant at init**: `initBundleTreeWithParams` satisfies `AsmFirstActiveDynGraphInv`. -/
theorem asmFirstActiveDynGraphInv_init (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) :
    AsmFirstActiveDynGraphInv
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord j) := by
  intro C _ b _
  exact normGraph_graphEq _

/-! ## 3. Restart lemmas (the three invariants) -/

/-- **The inactive invariant at restart**: `restartBundleTree` preserves `AsmFirstInactiveDynInv`. -/
theorem asmFirstInactiveDynInv_restart
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord : ℕ → List End} {wp : ℕ} {y : AsmBrSide B5 depth}
    {S' : Fin y.slotCap → Option BundleState} {x' : (B5 y.kB y.slotCap y.vCap5 y.eCap5).τ}
    {S6' : BucketSpannerState y.cap} {x6' : BucketSpannerMeta depth y.cap}
    (hInv : AsmFirstInactiveDynInv impl w depth tr y) :
    AsmFirstInactiveDynInv impl w depth (restartBundleTree depth sparsify tr ord)
      { y with bunS := S', xBun := x', spanS := S6', xSpan := x6', walkPot := wp } := by
  intro C hC hnotA b hb
  have hC' : C ∉ tr.activeComps := hnotA
  have hdyn : (restartBundleTree depth sparsify tr ord).dyn (C, b) = tr.dyn (C, b) := by
    simp only [restartBundleTree, hC', ↓reduceIte]
  have hinit : (restartBundleTree depth sparsify tr ord).initBunG (C, b) = tr.initBunG (C, b) := by
    simp only [restartBundleTree, hC', ↓reduceIte]
  rw [hdyn, hinit]
  exact hInv C hC hnotA b hb

/-- **The partition invariant at restart**: `restartBundleTree` preserves `AsmFirstActiveBunPartInv`. -/
theorem asmFirstActiveBunPartInv_restart (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hk : 1 ≤ tr.k) (hInv : AsmFirstActiveBunPartInv tr ord) :
    AsmFirstActiveBunPartInv (restartBundleTree depth sparsify tr ord) ord := by
  intro C hC b hb C_lsst ℓ₀ hI ρ hρ
  have hC' : C ∈ tr.activeComps := hC
  have hbun : (restartBundleTree depth sparsify tr ord).bun (C, b) =
      initBundleFor tr.cs ord (tr.bun (C, b)).edges tr.k := by
    simp only [restartBundleTree, hC', ↓reduceIte, restartBucketBundle]
  rw [hbun]
  exact initBundleFor_isPartition hI ρ hρ (hInv C hC b hb C_lsst ℓ₀ hI ρ hρ).1 hk

/-- **The graph invariant at restart**: `restartBundleTree` preserves `AsmFirstActiveDynGraphInv`. -/
theorem asmFirstActiveDynGraphInv_restart (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord : ℕ → List End} :
    AsmFirstActiveDynGraphInv (restartBundleTree depth sparsify tr ord) := by
  intro C hC b _
  have hC' : C ∈ tr.activeComps := hC
  simp only [restartBundleTree, hC', ↓reduceIte]
  exact normGraph_graphEq _

/-! ## 4. Step preservation across `stepBundleTree` (the three invariants) -/

/-- **The inactive invariant across `stepBundleTree`**: every component that remains inactive after a valid ordered
step keeps its untouched initial spanner state. -/
theorem asmFirstInactiveDynInv_step
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {y y' : AsmBrSide B5 depth}
    (hSP : asmBrSP impl w depth y' = asmBrSP impl w depth y)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord') (hk : 1 ≤ tr.k)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hCross : AsmFirstCrossInactiveInv tr)
    (hInv : AsmFirstInactiveDynInv impl w depth tr y) :
    AsmFirstInactiveDynInv impl w depth (stepBundleTree sparsify tr U ord ord').state y' := by
  intro C hC hnotA' b hb
  have hC0 : C ∈ components tr.cs.G₀ := by simpa [stepBundleTree, compLSFBatch_G₀] using hC
  obtain ⟨ρ, σ, hρ, hσ, hRB⟩ := hOB
  have hnotA : C ∉ tr.activeComps := fun hA =>
    hnotA' (Finset.mem_union_left _ hA)
  have hnotT : C ∉ touchedCompsBatch tr.cs U := fun hT =>
    hnotA' (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hT, hnotA⟩))
  have hReady := inactive_bundleCompReady hI hk hInact hCross hC0 hnotA hb
  have hStage := bundleCompStep_stage hI hBU hρ hσ hRB hC0 hReady
  have hNil : (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord ord' U).1 = [] := by
    rw [hStage.2.2.2.2.2.2.2.2 hnotT]
  change (DynSpanner.update (tr.dyn (C, b))
      (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord ord' U).1 (sparsify tr.m₀)).state = _
  rw [hNil, update_nil]
  have hSB : y'.splitB = y.splitB := congrArg DSParams.splitBound hSP
  have hst := hInv C hC0 hnotA b hb
  dsimp only [DSHist.state, DSHist.q, asmBrSP] at hst ⊢
  rw [hSB]
  exact hst

/-- **The partition invariant across `stepBundleTree`**: every active (old or newly activated) pair satisfies
`IsPartition` for the new core rotation after a valid ordered step. -/
theorem asmFirstActiveBunPartInv_step
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {y : AsmBrSide B5 depth}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord') (hk : 1 ≤ tr.k)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hPart : AsmFirstActiveBunPartInv tr ord) :
    AsmFirstActiveBunPartInv (stepBundleTree sparsify tr U ord ord').state ord' := by
  intro C hC' b hb C' ℓ' hI' σ' hσ'
  obtain ⟨ρ, σ, hρ, hσ, hRB⟩ := hOB
  have hPartOld : (tr.bun (C, b)).IsPartition
      (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) tr.k := by
    rcases Finset.mem_union.mp hC' with hOld | hNew
    · exact hPart C hOld b hb C_lsst ℓ₀ hI ρ hρ
    · obtain ⟨hT, hNotA⟩ := Finset.mem_sdiff.mp hNew
      have hC0 : C ∈ components tr.cs.G₀ := (Finset.mem_filter.mp hT).1
      have hAg := ((hInact C hC0 hNotA).2.2.2.2 b hb).1
      exact (bunAgree_isPartition_iff hAg).mp
        (initBundleFor_isPartition hI ρ hρ (Finset.filter_subset _ _) hk)
  have hReady : BundleStepReady tr.cs (tr.bun (C, b)) tr.k ord ord' U :=
    ⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hRB, hBU, hPartOld⟩
  exact (bundleCompStep_spec hReady).1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'

/-- **The graph invariant across `stepBundleTree`**: every active (old or newly activated) pair satisfies
`GraphEq (tr'.dyn (C, b)).G (tr'.bun (C, b)).graph` after a valid ordered step. -/
theorem asmFirstActiveDynGraphInv_step
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {y : AsmBrSide B5 depth}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord') (hk : 1 ≤ tr.k)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hInactDyn : AsmFirstInactiveDynInv impl w depth tr y)
    (hPart : AsmFirstActiveBunPartInv tr ord)
    (hDynG : AsmFirstActiveDynGraphInv tr) :
    AsmFirstActiveDynGraphInv (stepBundleTree sparsify tr U ord ord').state := by
  intro C hC' b hb
  obtain ⟨ρ, σ, hρ, hσ, hRB⟩ := hOB
  have hPair : BundleStepReady tr.cs (tr.bun (C, b)) tr.k ord ord' U ∧
      GraphEq (tr.dyn (C, b)).G (tr.bun (C, b)).graph := by
    rcases Finset.mem_union.mp hC' with hOld | hNew
    · exact ⟨⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hRB, hBU, hPart C hOld b hb C_lsst ℓ₀ hI ρ hρ⟩,
        hDynG C hOld b hb⟩
    · obtain ⟨hT, hNotA⟩ := Finset.mem_sdiff.mp hNew
      have hC0 : C ∈ components tr.cs.G₀ := (Finset.mem_filter.mp hT).1
      obtain ⟨hAg, hInitG, -⟩ := (hInact C hC0 hNotA).2.2.2.2 b hb
      have hP : (tr.bun (C, b)).IsPartition
          (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) tr.k :=
        (bunAgree_isPartition_iff hAg).mp
          (initBundleFor_isPartition hI ρ hρ (Finset.filter_subset _ _) hk)
      have hG : GraphEq (tr.dyn (C, b)).G (tr.bun (C, b)).graph := by
        rw [hInactDyn C hC0 hNotA b hb, dsHist_init_G_eq, hInitG]
        exact normGraph_graphEq _
      exact ⟨⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hRB, hBU, hP⟩, hG⟩
  have hSpec := bundleCompStep_spec hPair.1
  change GraphEq
    (DynSpanner.update (tr.dyn (C, b))
      (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord ord' U).1 (sparsify tr.m₀)).state.G
    (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord ord' U).2.graph
  rw [update_G_eq, hSpec.2.2.1]
  exact graphEq_applyBatch hPair.2 _

/-! ## 5. `GraphEq` bridge lemmas for Phase 4 (`SmallBatchAt`, `BatchAt`, `BunAgree`) -/

/-- `BunAgree` implies `GraphEq` on the bundle graphs. -/
theorem bunAgree_graphEq {B₁ B₂ : BundleState} (h : BunAgree B₁ B₂) :
    GraphEq B₁.graph B₂.graph :=
  ⟨h.1, h.2.1, fun e he => ⟨h.2.2.2 (e, true) he, h.2.2.2 (e, false) he⟩⟩

/-- `UpdateAt` is invariant under `GraphEq`. -/
theorem updateAt_of_graphEq {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : MGraph} {u : Update} {len : ℕ}
    (hG : GraphEq G₁ G₂) (h : UpdateAt mem a G₁ u len) : UpdateAt mem a G₂ u len := by
  cases u with
  | insert e x y => exact h
  | delete e => exact h
  | split v v' St Sh =>
    rcases h with ⟨Lt, Lh, hndT, hndH, hLt, hLh, hlen, hAt⟩ |
      ⟨Lt, Lh, hndT, hndH, hLt, hLh, hlen, hAt⟩
    · left
      refine ⟨Lt, Lh, hndT, hndH, fun e => ?_, fun e => ?_, hlen, hAt⟩
      · rw [hLt e, ← hG.2.1]
        exact ⟨fun ⟨he, ht, hs⟩ => ⟨he, (hG.2.2 e he).1 ▸ ht, hs⟩,
          fun ⟨he, ht, hs⟩ => ⟨he, (hG.2.2 e he).1.symm ▸ ht, hs⟩⟩
      · rw [hLh e, ← hG.2.1]
        exact ⟨fun ⟨he, hh, hs⟩ => ⟨he, (hG.2.2 e he).2 ▸ hh, hs⟩,
          fun ⟨he, hh, hs⟩ => ⟨he, (hG.2.2 e he).2.symm ▸ hh, hs⟩⟩
    · right
      refine ⟨Lt, Lh, hndT, hndH, fun e => ?_, fun e => ?_, hlen, hAt⟩
      · rw [hLt e, ← hG.2.1]
        exact ⟨fun ⟨he, ht, hs⟩ => ⟨he, (hG.2.2 e he).1 ▸ ht, hs⟩,
          fun ⟨he, ht, hs⟩ => ⟨he, (hG.2.2 e he).1.symm ▸ ht, hs⟩⟩
      · rw [hLh e, ← hG.2.1]
        exact ⟨fun ⟨he, hh, hs⟩ => ⟨he, (hG.2.2 e he).2 ▸ hh, hs⟩,
          fun ⟨he, hh, hs⟩ => ⟨he, (hG.2.2 e he).2.symm ▸ hh, hs⟩⟩

/-- `BatchBodyAt` is invariant under `GraphEq`. -/
theorem batchBodyAt_of_graphEq {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : MGraph} {U : List Update} {W : ℕ}
    (hG : GraphEq G₁ G₂) (h : BatchBodyAt mem a G₁ U W) : BatchBodyAt mem a G₂ U W := by
  induction U generalizing a G₁ G₂ W with
  | nil => exact h
  | cons u us ih =>
    obtain ⟨len, hle, hu, hrest⟩ := h
    exact ⟨len, hle, updateAt_of_graphEq hG hu, ih (graphEq_applyUpdate hG u) hrest⟩

/-- `BatchAt` is invariant under `GraphEq`. -/
theorem batchAt_of_graphEq {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : MGraph} {U : List Update} {W : ℕ}
    (hG : GraphEq G₁ G₂) (h : BatchAt mem a G₁ U W) : BatchAt mem a G₂ U W :=
  ⟨h.1, h.2.1, batchBodyAt_of_graphEq hG h.2.2⟩

/-- `SmallBatchAt` is invariant under `GraphEq`. -/
theorem smallBatchAt_of_graphEq {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : MGraph} {U : List Update} {W : ℕ}
    (hG : GraphEq G₁ G₂) (h : SmallBatchAt mem a G₁ U W) : SmallBatchAt mem a G₂ U W :=
  ⟨batchAt_of_graphEq hG h.1, by rw [← graphEq_batchEnc hG U]; exact h.2⟩

/-- Edge-set equality extracted from `AsmFirstActiveDynGraphInv`. -/
theorem asmFirstActiveDynGraphInv_E {depth : ℕ} {tr : BundleTreeState depth}
    (h : AsmFirstActiveDynGraphInv tr) {C : Finset ℕ} (hC : C ∈ tr.activeComps)
    {b : ℤ} (hb : b ∈ tr.activeBuckets C) :
    (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges :=
  (h C hC b hb).2.1

/-- Normalized-graph equality extracted from `AsmFirstActiveDynGraphInv`. -/
theorem asmFirstActiveDynGraphInv_normEq {depth : ℕ} {tr : BundleTreeState depth}
    (h : AsmFirstActiveDynGraphInv tr) {C : Finset ℕ} (hC : C ∈ tr.activeComps)
    {b : ℤ} (hb : b ∈ tr.activeBuckets C) :
    SparseCore.normGraph (tr.dyn (C, b)).G = SparseCore.normGraph (tr.bun (C, b)).graph :=
  normGraph_eq_of_graphEq (h C hC b hb)

/-! ## 6. Formal counterexample to the graph invariant with `=` (`(tr.dyn (C, b)).G = normGraph (tr.bun (C, b)).graph`) -/

/-- The 2-vertex, 2-parallel-edge graph used to witness that raw record equality
`(tr.dyn (C, b)).G = normGraph (tr.bun (C, b)).graph` fails after a single `stepBundleTree` edge
deletion. -/
def s8cWitnessGraph : MGraph where
  V := {0, 1}
  E := {0, 1}
  tail := fun _ => 0
  head := fun _ => 1

private theorem s8cWitnessGraph_isValid : s8cWitnessGraph.IsValid := by
  intro e _
  simp [s8cWitnessGraph]

private theorem s8cWitnessGraph_comp :
    ({0, 1} : Finset ℕ) ∈ components s8cWitnessGraph := by
  have hconn : s8cWitnessGraph.Connected 0 1 :=
    ⟨[(0, true)], MGraph.IsWalk.cons (by simp [s8cWitnessGraph]) rfl (.nil 1)⟩
  have hcomp0 : compOf s8cWitnessGraph 0 = {0, 1} := by
    ext v
    rw [mem_compOf_iff]
    simp only [s8cWitnessGraph, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, ⟨[], .nil 0⟩⟩
      · exact ⟨Or.inr rfl, hconn⟩
  rw [← hcomp0]
  exact Finset.mem_image.mpr ⟨0, by simp [s8cWitnessGraph], rfl⟩

/-- Explicit rotation system on `s8cWitnessGraph`. -/
def s8cWitnessRot : Rotation s8cWitnessGraph where
  order v :=
    if v = 0 then [(0, true), (1, true)]
    else if v = 1 then [(0, false), (1, false)]
    else []
  nodup v := by
    split_ifs <;> decide
  mem_order v x := by
    rcases x with ⟨e, side⟩
    cases side <;> split_ifs <;> simp [s8cWitnessGraph, MGraph.src] <;> omega

private def s8cDeleteRot (e₀ : ℕ) : Rotation (s8cWitnessGraph.applyUpdate (.delete e₀)) where
  order v := (s8cWitnessRot.order v).filter (fun x => x.1 != e₀)
  nodup v := (s8cWitnessRot.nodup v).filter _
  mem_order v x := by
    rw [List.mem_filter, s8cWitnessRot.mem_order]
    simp only [MGraph.applyUpdate, MGraph.src, Finset.mem_erase, bne_iff_ne, ne_eq]
    tauto

private theorem applyBatch_delOrSplit_nonzero_end {G : MGraph} {U : List Update} {e : ℕ}
    (h0 : 0 ∈ G.V) (hBV : G.BatchIsValid U) (hds : ∀ u ∈ U, isDelOrSplit u)
    (hnz : G.tail e ≠ 0 ∨ G.head e ≠ 0) :
    (G.applyBatch U).tail e ≠ 0 ∨ (G.applyBatch U).head e ≠ 0 := by
  induction U generalizing G with
  | nil => exact hnz
  | cons u us ih =>
    have hu := hds u (List.mem_cons_self ..)
    have hus := fun u' hu' => hds u' (List.mem_cons_of_mem _ hu')
    cases u with
    | insert _ _ _ => cases hu
    | delete _ => exact ih h0 hBV.2 hus hnz
    | split v v' St Sh =>
      have hv'_ne : v' ≠ 0 := fun h => hBV.1.2.1 (h ▸ h0)
      have h0' : 0 ∈ (G.applyUpdate (.split v v' St Sh)).V := Finset.mem_insert_of_mem h0
      refine ih h0' hBV.2 hus ?_
      rcases hnz with ht | hh
      · left; simp only [MGraph.applyUpdate]; split_ifs <;> assumption
      · right; simp only [MGraph.applyUpdate]; split_ifs <;> assumption

/-- **Formal counterexample to the graph invariant with `=`**: for any valid LSF initializer `lsfInit` at `k = 1`, any
depth `L`, any sparsifier `sparsify`, and any parameters, starting from
`tr₀ := initBundleTreeWithParams lsfInit L sparsify params spanConst 1 M N s8cWitnessGraph (fun _ => 1) s8cWitnessRot.order 0`,
there is a single valid ordered edge deletion `U = [.delete e₀]` after which
`tr₁ := (stepBundleTree sparsify tr₀ U ord ord').state` has an active pair `(C, b)` with
`(tr₁.dyn (C, b)).G ≠ SparseCore.normGraph (tr₁.bun (C, b)).graph`. -/
theorem raw_s8c_counterexample_exists {C_lsst : ℝ} (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst M N : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst 1 0) :
    let G₀ := s8cWitnessGraph
    let ℓ₀ : ℕ → ℝ := fun _ => 1
    let ord := s8cWitnessRot.order
    let tr₀ := initBundleTreeWithParams lsfInit L sparsify params spanConst 1 M N G₀ ℓ₀ ord 0
    ∃ (U : List Update) (ord' : ℕ → List End) (C : Finset ℕ) (b : ℤ),
      tr₀.cs.G.BatchIsValid U ∧
      OrderedBatch tr₀.cs.G U ord ord' ∧
      let tr₁ := (stepBundleTree sparsify tr₀ U ord ord').state
      C ∈ tr₁.activeComps ∧ b ∈ tr₁.activeBuckets C ∧
      (tr₁.dyn (C, b)).G ≠ SparseCore.normGraph (tr₁.bun (C, b)).graph := by
  classical
  intro G₀ ℓ₀ ord tr₀
  have hI₀ : CompLSFInv C_lsst ℓ₀ tr₀.cs :=
    compLSFInv_initWith hInit s8cWitnessGraph_isValid ⟨0, by simp [s8cWitnessGraph]⟩
      (fun _ _ => by norm_num [ℓ₀]) le_rfl
  have hF₀ := compLSF_RF_isRSF hI₀
  -- Any spanning forest on 2 vertices has at most 1 edge, so at least one of `{0, 1}` is a core edge.
  have hCoreNe : ((coreGraph G₀ tr₀.cs.lsf).E).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hEsub : G₀.E ⊆ tr₀.cs.RF.F.E := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have h0F : 0 ∈ tr₀.cs.RF.F.E := hEsub (by simp [G₀, s8cWitnessGraph])
    have h1F : 1 ∈ tr₀.cs.RF.F.E := hEsub (by simp [G₀, s8cWitnessGraph])
    have hsubG := hF₀.2.2.2.2
    have hcyc : tr₀.cs.RF.F.IsWalk 0 0 [(0, true), (1, false)] := by
      have ht0 : tr₀.cs.RF.F.tail 0 = 0 := (hsubG.2.2 0 h0F).1
      have hh0 : tr₀.cs.RF.F.head 0 = 1 := (hsubG.2.2 0 h0F).2
      have ht1 : tr₀.cs.RF.F.tail 1 = 0 := (hsubG.2.2 1 h1F).1
      have hh1 : tr₀.cs.RF.F.head 1 = 1 := (hsubG.2.2 1 h1F).2
      refine MGraph.IsWalk.cons h0F (by simp [MGraph.src, ht0]) ?_
      rw [show tr₀.cs.RF.F.dst (0, true) = 1 by simp [MGraph.dst, hh0]]
      refine MGraph.IsWalk.cons h1F (by simp [MGraph.src, hh1]) ?_
      rw [show tr₀.cs.RF.F.dst (1, false) = 0 by simp [MGraph.dst, ht1]]
      exact .nil 0
    have hnd : ([(0, true), (1, false)] : List End).map Prod.fst |>.Nodup := by decide
    exact hF₀.1.2 [(0, true), (1, false)] ⟨by simp, hnd, 0, hcyc⟩
  obtain ⟨e₀, he₀_core⟩ := hCoreNe
  have he₀_G : e₀ ∈ G₀.E := (Finset.mem_sdiff.mp he₀_core).1
  set C : Finset ℕ := {0, 1}
  set b : ℤ := tr₀.origBucket e₀
  have hC_comp : C ∈ components G₀ := s8cWitnessGraph_comp
  have hC_act : C ∈ tr₀.activeComps := by
    refine Finset.mem_filter.mpr ⟨hC_comp, ?_, ?_⟩
    · have hm : (compGraph G₀ C).m = 2 := by
        show (G₀.E.filter fun e => G₀.tail e ∈ C).card = 2
        have hflt : (G₀.E.filter fun e => G₀.tail e ∈ C) = {0, 1} := by
          ext e; simp [G₀, s8cWitnessGraph, C]
        rw [hflt]; decide
      omega
    · have hm : (compGraph G₀ C).m = 2 := by
        show (G₀.E.filter fun e => G₀.tail e ∈ C).card = 2
        have hflt : (G₀.E.filter fun e => G₀.tail e ∈ C) = {0, 1} := by
          ext e; simp [G₀, s8cWitnessGraph, C]
        rw [hflt]; decide
      omega
  have ht_in_C : (coreGraph G₀ tr₀.cs.lsf).tail e₀ ∈ C := by
    have hV := (coreGraph_isValid hI₀.hG_val hF₀ e₀ he₀_core).1
    exact hF₀.2.2.1 hV
  have hb_act : b ∈ tr₀.activeBuckets C :=
    Finset.mem_image.mpr ⟨e₀, Finset.mem_filter.mpr ⟨he₀_core, ht_in_C⟩, rfl⟩
  set U : List Update := [.delete e₀]
  set σ := s8cDeleteRot e₀
  set ord' := σ.order
  have hBU : tr₀.cs.G.BatchIsValid U := ⟨he₀_G, trivial⟩
  have hRB : RotationBatch 2 U s8cWitnessRot σ :=
    .cons (fun v => List.IsRotated.refl _) (.nil fun v => List.IsRotated.refl _)
  have hOB : OrderedBatch tr₀.cs.G U ord ord' := ⟨s8cWitnessRot, σ, rfl, rfl, hRB⟩
  refine ⟨U, ord', C, b, hBU, hOB, Finset.mem_union_left _ hC_act, hb_act, ?_⟩
  -- In `tr₀.bun (C, b)`, `k = 1` prevents `e₀` from being a self-loop at bundle `0`.
  have hPart₀ : (tr₀.bun (C, b)).IsPartition
      (coreRotation (L := tr₀.cs.lsf) s8cWitnessRot hI₀.hG_val hF₀) 1 :=
    asmFirstActiveBunPartInv_init lsfInit L sparsify params spanConst 1 M N G₀ ℓ₀ ord 0 le_rfl
      C hC_act b hb_act C_lsst ℓ₀ hI₀ s8cWitnessRot rfl
  have he₀_bun : e₀ ∈ (tr₀.bun (C, b)).edges := by
    show e₀ ∈ (initBundleFor tr₀.cs ord
      (bucketCoreEdges (coreGraph G₀ tr₀.cs.lsf) tr₀.origBucket C b) 1).edges
    rw [initBundleFor_eq hI₀ (rfl : s8cWitnessRot.order = ord)]
    exact Finset.mem_filter.mpr ⟨he₀_core, ht_in_C, rfl⟩
  have h0V : 0 ∈ (tr₀.dyn (C, b)).G.V := by
    show 0 ∈ (tr₀.bun (C, b)).vertices
    have hEq := initBundleFor_eq hI₀ (rfl : s8cWitnessRot.order = ord)
      (bucketCoreEdges (coreGraph G₀ tr₀.cs.lsf) tr₀.origBucket C b) 1
    have hVne : (tr₀.bun (C, b)).vertices.Nonempty :=
      ⟨(tr₀.bun (C, b)).bundleOf (e₀, true),
        (hPart₀.2.2.1 (e₀, true) ((mem_edgeEnds _ _).mpr he₀_bun)).1⟩
    change 0 ∈ (initBundleFor tr₀.cs ord
      (bucketCoreEdges (coreGraph G₀ tr₀.cs.lsf) tr₀.origBucket C b) 1).vertices
    change (initBundleFor tr₀.cs ord
      (bucketCoreEdges (coreGraph G₀ tr₀.cs.lsf) tr₀.origBucket C b) 1).vertices.Nonempty at hVne
    rw [hEq] at hVne ⊢
    obtain ⟨v, hv⟩ := hVne
    have hpos : 0 < (initialSlots (coreRotation (L := tr₀.cs.lsf) s8cWitnessRot hI₀.hG_val hF₀)
        (bucketCoreEdges (coreGraph G₀ tr₀.cs.lsf) tr₀.origBucket C b) 1).length :=
      Nat.lt_of_le_of_lt (Nat.zero_le v) (Finset.mem_range.mp hv)
    exact Finset.mem_range.mpr hpos
  have hnz : (tr₀.bun (C, b)).graph.tail e₀ ≠ 0 ∨ (tr₀.bun (C, b)).graph.head e₀ ≠ 0 := by
    by_contra hboth
    push Not at hboth
    obtain ⟨ht0, hh0⟩ := hboth
    have hv0 : 0 ∈ (tr₀.bun (C, b)).vertices := by
      rw [← ht0]
      exact (hPart₀.2.2.1 (e₀, true) ((mem_edgeEnds _ _).mpr he₀_bun)).1
    have hdeg1 : (tr₀.bun (C, b)).graph.deg 0 ≤ 1 := BundleState.deg_le hPart₀ hv0
    rw [BundleState.deg_eq] at hdeg1
    have h2 : ({(e₀, true), (e₀, false)} : Finset End) ⊆ (tr₀.bun (C, b)).ends 0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨(mem_edgeEnds _ _).mpr he₀_bun, ht0⟩
      · exact Finset.mem_filter.mpr ⟨(mem_edgeEnds _ _).mpr he₀_bun, hh0⟩
    have hcard : 2 ≤ ((tr₀.bun (C, b)).ends 0).card := by
      have hle := Finset.card_le_card h2
      have hc2 : ({(e₀, true), (e₀, false)} : Finset End).card = 2 := by
        rw [Finset.card_pair]
        intro h
        exact Bool.noConfusion (Prod.mk.inj h).2
      omega
    omega
  -- Every update in `U_B` is a valid delete or split, and `0 ∈ V`, so `e₀` keeps a nonzero endpoint.
  have hReady : BundleStepReady tr₀.cs (tr₀.bun (C, b)) 1 ord ord' U :=
    ⟨C_lsst, ℓ₀, hI₀, s8cWitnessRot, σ, rfl, rfl, hRB, hBU, hPart₀⟩
  have hSpec := bundleCompStep_spec hReady
  have hDyn0_BV : (tr₀.dyn (C, b)).G.BatchIsValid
      (bundleCompStep tr₀.cs (tr₀.bun (C, b)) 1 ord ord' U).1 :=
    (graphEq_batchIsValid (normGraph_graphEq _) _).mpr hSpec.2.1
  have hDyn0_nz : (tr₀.dyn (C, b)).G.tail e₀ ≠ 0 ∨ (tr₀.dyn (C, b)).G.head e₀ ≠ 0 := by
    have hEq0 : GraphEq (tr₀.dyn (C, b)).G (tr₀.bun (C, b)).graph := normGraph_graphEq _
    have hEnds := hEq0.2.2 e₀ he₀_bun
    rw [hEnds.1, hEnds.2]
    exact hnz
  have hDyn1_G : ((stepBundleTree sparsify tr₀ U ord ord').state.dyn (C, b)).G =
      (tr₀.dyn (C, b)).G.applyBatch (bundleCompStep tr₀.cs (tr₀.bun (C, b)) 1 ord ord' U).1 :=
    update_G_eq _ _ _
  have hDyn1_nz :
      ((stepBundleTree sparsify tr₀ U ord ord').state.dyn (C, b)).G.tail e₀ ≠ 0 ∨
      ((stepBundleTree sparsify tr₀ U ord ord').state.dyn (C, b)).G.head e₀ ≠ 0 := by
    rw [hDyn1_G]
    exact applyBatch_delOrSplit_nonzero_end h0V hDyn0_BV hSpec.2.2.2.1 hDyn0_nz
  -- In `tr₁.bun`, `e₀` is deleted, so `normGraph` sets both `tail e₀ = 0` and `head e₀ = 0`.
  have he₀_notBun1 : e₀ ∉ ((stepBundleTree sparsify tr₀ U ord ord').state.bun (C, b)).edges := by
    have hEq := bundleCompStep_edges_eq hReady
    change e₀ ∉ (bundleCompStep tr₀.cs (tr₀.bun (C, b)) 1 ord ord' U).2.edges
    rw [hEq]
    simp [batchDeletes, addDel, U]
  intro hEqG
  rcases hDyn1_nz with hnt | hnh
  · have h2 : (SparseCore.normGraph
        ((stepBundleTree sparsify tr₀ U ord ord').state.bun (C, b)).graph).tail e₀ = 0 := by
      simp [SparseCore.normGraph, BundleState.graph, he₀_notBun1]
    exact hnt (by rw [hEqG]; exact h2)
  · have h2 : (SparseCore.normGraph
        ((stepBundleTree sparsify tr₀ U ord ord').state.bun (C, b)).graph).head e₀ = 0 := by
      simp [SparseCore.normGraph, BundleState.graph, he₀_notBun1]
    exact hnh (by rw [hEqG]; exact h2)

end

end MinCostFlow.SparseCore.Program
