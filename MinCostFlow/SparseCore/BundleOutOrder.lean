module

public import MinCostFlow.SparseCore.BundleTool
public import MinCostFlow.SparseCore.BundleOutBatchOrder
public import MinCostFlow.SparseCore.BundleRunInv

/-!
# Output order of the bundle-graph sparse core

For every branch `j < k` of `sparseCoreBundleTool`, the output graphs `S_cur` with the restricted
core rotations `BundleTreeState.outOrder` (exported as `sparseCoreBundleTool.rot`) change by
ordered batches with split bound two.

This file proves:
- `BundleTreeState.outOrder_eq_restrict`: `st.outOrder ord` equals the restricted core rotation;
- `stepBundleTree_outOrder`: one-step output order (`CoreSubgraphBatch 2` and `RotationBatch 2`)
  for `stepBundleTree` (from `buildUSOrd_coreSubgraphBatch` and `CoreSubgraphBatch.ordered`,
  reusable across restarts);
- `bundleSeq_orderedUpTo`: trajectory-level output order (`OrderedUpTo`) for any sequence of
  `stepBundleTree` transitions (applicable to both fresh runs and post-restart epochs);
- `sparseCoreBundleTool_orderedUpTo_of_sub` and `sparseCoreBundleTool_orderedUpTo`: the
  output-order clause of `IsSpecOrdUpTo` for `sparseCoreBundleTool` on both nonempty and empty
  initial graphs.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-! ## 1. `BundleTreeState.outOrder` and one-step output order for `stepBundleTree` -/

private theorem applyBatch_delete_list_E (G : MGraph) (L : List ℕ) :
    (G.applyBatch (L.map Update.delete)).E = G.E \ L.toFinset := by
  induction L generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons e L ih =>
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, List.toFinset_cons]
    change ((G.applyUpdate (.delete e)).applyBatch (L.map Update.delete)).E = _
    rw [ih]
    ext x
    simp only [MGraph.applyUpdate, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    tauto

private theorem applyBatch_restrictSplits_E (G : MGraph) (keep : Finset ℕ) (UC : List Update) :
    (G.applyBatch (restrictSplits keep UC)).E = G.E := by
  induction UC generalizing G with
  | nil => rfl
  | cons u UC ih =>
    cases u with
    | insert _ _ _ => exact ih G
    | delete _ => exact ih G
    | split v v' St Sh =>
      simp only [restrictSplits, MGraph.applyBatch, List.foldl_cons]
      exact ih (G.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep)))

private theorem applyBatch_insert_list_E (G : MGraph) (L : List ℕ) (t h : ℕ → ℕ) :
    (G.applyBatch (L.map fun e => Update.insert e (t e) (h e))).E = G.E ∪ L.toFinset := by
  induction L generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons e L ih =>
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, List.toFinset_cons]
    change ((G.applyUpdate (.insert e (t e) (h e))).applyBatch
      (L.map fun e => Update.insert e (t e) (h e))).E = _
    rw [ih]
    ext x
    simp only [MGraph.applyUpdate, Finset.mem_union, Finset.mem_insert]
    tauto

/-- Applying `buildUSOrd` always produces edge set `targetE`. -/
theorem applyBatch_buildUSOrd_E (UC U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) :
    (S_prev.applyBatch (buildUSOrd UC U cs_new S_prev targetE D_reins)).E = targetE := by
  unfold buildUSOrd
  rw [applyBatch_append, applyBatch_append, applyBatch_insert_list_E,
    applyBatch_restrictSplits_E, applyBatch_delete_list_E,
    Finset.sort_toFinset, Finset.sort_toFinset]
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- The output batch emitted by `stepBundleTree` is `buildUSOrd` targeting `info.state.S_cur.E`. -/
theorem stepBundleTree_U_S_eq {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify st U ord ord'
    info.U_S = buildUSOrd (coreBatchOf st.cs ord ord' U) U (compLSFBatch st.cs U)
      st.S_cur info.state.S_cur.E info.D_total := by
  dsimp only [stepBundleTree]
  rw [applyBatch_buildUSOrd_E]

/-- When the LSF satisfies `CompLSFInv` and `ord` is the order of a rotation `ρ` of `st.cs.G`,
`st.outOrder ord` equals the restricted core rotation of `ρ` on `st.S_cur`. -/
theorem BundleTreeState.outOrder_eq_restrict {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (st : BundleTreeState L) (ord : ℕ → List End)
    (hI : CompLSFInv C_lsst ℓ₀ st.cs) (ρ : Rotation st.cs.G) (hρ : ρ.order = ord)
    (hS_sub : (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur) :
    st.outOrder ord =
      ((coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).restrict hS_sub).order := by
  classical
  have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ st.cs) (ρ' : Rotation st.cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold BundleTreeState.outOrder
  rw [dite_eq_left hex]
  have hρ_eq : hex.choose_spec.choose_spec.choose_spec.choose = ρ :=
    Rotation.ext_order (hex.choose_spec.choose_spec.choose_spec.choose_spec.trans hρ.symm)
  funext v
  change (((coreRotation (L := st.cs.lsf) hex.choose_spec.choose_spec.choose_spec.choose
      hex.choose_spec.choose_spec.choose.hG_val
      (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).order v).filter
      fun x => decide (x.1 ∈ st.S_cur.E)) = _
  rw [hρ_eq]; rfl

/-- One-step `CoreSubgraphBatch 2` and `RotationBatch 2` for `stepBundleTree`
(reusable across restarts). -/
theorem stepBundleTree_outOrder {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hI : CompLSFInv C_lsst ℓ₀ st.cs) (hBU : st.cs.G.BatchIsValid U)
    (ρ : Rotation st.cs.G) (σ : Rotation (st.cs.G.applyBatch U))
    (hρ : ρ.order = ord) (hσ : σ.order = ord') (hrot : RotationBatch 2 U ρ σ)
    (hS_val : st.S_cur.IsValid) (hS_V : st.S_cur.V = st.cs.RF.R)
    (hS_sub : (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur)
    (hS_sub' : (coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf).IsSubgraph
      (stepBundleTree sparsify st U ord ord').state.S_cur) :
    let info := stepBundleTree sparsify st U ord ord'
    let hI' := compLSFBatch_inv hI hBU
    let hG_eq := compLSFBatch_G st.cs U
    CoreSubgraphBatch 2 info.U_S
      ⟨coreGraph st.cs.G st.cs.lsf,
        coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI), hS_sub⟩
      ⟨coreGraph info.state.cs.G info.state.cs.lsf,
        coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σ) hI'.hG_val
          (compLSF_RF_isRSF hI'), hS_sub'⟩ ∧
    RotationBatch 2 info.U_S
      ((coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).restrict hS_sub)
      ((coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σ) hI'.hG_val
        (compLSF_RF_isRSF hI')).restrict hS_sub') := by
  intro info hI' hG_eq
  have hUS_eq : info.U_S = buildUSOrd (coreBatchOf st.cs ord ord' U) U (compLSFBatch st.cs U)
      st.S_cur info.state.S_cur.E info.D_total :=
    stepBundleTree_U_S_eq sparsify st U ord ord'
  have hSpec := buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hS_sub'.2.1 info.D_total
  have hCSB_raw := buildUSOrd_coreSubgraphBatch hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub
    hS_sub'.2.1 info.D_total
  have hCSB : CoreSubgraphBatch 2 info.U_S
      ⟨coreGraph st.cs.G st.cs.lsf,
        coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI), hS_sub⟩
      ⟨coreGraph info.state.cs.G info.state.cs.lsf,
        coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σ) hI'.hG_val
          (compLSF_RF_isRSF hI'), hS_sub'⟩ := by
    have aux : ∀ (W : List Update) (hW : W = info.U_S)
        (hsub : (coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf).IsSubgraph
          (st.S_cur.applyBatch W)),
        CoreSubgraphBatch 2 W
          ⟨coreGraph st.cs.G st.cs.lsf,
            coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI), hS_sub⟩
          ⟨coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf,
            coreRotation (L := (compLSFBatch st.cs U).lsf) (hG_eq.symm ▸ σ) hI'.hG_val
              (compLSF_RF_isRSF hI'), hsub⟩ →
        CoreSubgraphBatch 2 info.U_S
          ⟨coreGraph st.cs.G st.cs.lsf,
            coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI), hS_sub⟩
          ⟨coreGraph info.state.cs.G info.state.cs.lsf,
            coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σ) hI'.hG_val
              (compLSF_RF_isRSF hI'), hS_sub'⟩ := by
      intro W hW hsub h; subst hW; exact h
    exact aux _ hUS_eq.symm _ hCSB_raw
  have hBV : st.S_cur.BatchIsValid info.U_S := hUS_eq.symm ▸ hSpec.1
  exact ⟨hCSB, CoreSubgraphBatch.ordered hCSB hBV⟩

/-! ## 2. Trajectory-level output order (reusable for post-restart epochs) -/

/-- General trajectory-level output order (`OrderedUpTo`) for any sequence of `stepBundleTree`
transitions (applicable to both fresh runs and post-restart epochs). -/
theorem bundleSeq_orderedUpTo {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (D : DynamicInstance) (τ : ℕ) (ord : ℕ → ℕ → List End)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (bt : ℕ → BundleTreeState L) (D_out : DynamicInstance)
    (hOut_G : ∀ t ≤ τ, D_out.G t = (bt t).S_cur)
    (hOut_U : ∀ t < τ, D_out.U (t + 1) =
      (stepBundleTree sparsify (bt t) (D.U (t + 1)) (ord t) (ord (t + 1))).U_S)
    (hStep_st : ∀ t < τ, bt (t + 1) =
      (stepBundleTree sparsify (bt t) (D.U (t + 1)) (ord t) (ord (t + 1))).state)
    (hCs_inv : ∀ t ≤ τ, CompLSFInv C_lsst ℓ₀ (bt t).cs ∧ (bt t).cs.G = D.G t)
    (hS_val : ∀ t ≤ τ, (bt t).S_cur.IsValid)
    (hS_V : ∀ t ≤ τ, (bt t).S_cur.V = (bt t).cs.RF.R)
    (hS_sub : ∀ t ≤ τ, (coreGraph (bt t).cs.G (bt t).cs.lsf).IsSubgraph (bt t).S_cur) :
    OrderedUpTo D_out τ 2 (fun t => (bt t).outOrder (ord t)) := by
  have ⟨ρIn, hρOrd, _⟩ := hOrd
  let rotAt : ∀ t, t ≤ τ → Rotation (bt t).S_cur := fun t ht =>
    (coreRotation (L := (bt t).cs.lsf) ((hCs_inv t ht).2.symm ▸ ρIn t)
      (hCs_inv t ht).1.hG_val (compLSF_RF_isRSF (hCs_inv t ht).1)).restrict (hS_sub t ht)
  let ρOut : ∀ t, Rotation (D_out.G t) := fun t =>
    if ht : t ≤ τ then (hOut_G t ht).symm ▸ rotAt t ht else sortedRotation (D_out.G t)
  refine ⟨ρOut, fun t ht => ?_, fun t ht => ?_⟩
  · rw [show ρOut t = (hOut_G t ht).symm ▸ rotAt t ht from dite_eq_left ht, rotation_cast_order]
    exact (BundleTreeState.outOrder_eq_restrict (bt t) (ord t) (hCs_inv t ht).1 _
      (by rw [rotation_cast_order, hρOrd t ht]) (hS_sub t ht)).symm
  · have ht_le : t ≤ τ := Nat.le_of_lt ht
    have hDstep := hD (t + 1) (Nat.succ_pos t) ht
    rw [Nat.add_sub_cancel] at hDstep
    have hBU : (bt t).cs.G.BatchIsValid (D.U (t + 1)) := (hCs_inv t ht_le).2.symm ▸ hDstep.1
    have hG_step : D_out.G (t + 1) = (D_out.G t).applyBatch (D_out.U (t + 1)) := by
      rw [hOut_G (t + 1) ht, hOut_G t ht_le, hOut_U t ht, hStep_st t ht]; rfl
    refine ⟨hG_step, ?_⟩
    obtain ⟨ρt, σt, hρt, hσt, hrot_t⟩ := orderedUpTo_rot_step hOrd ht (hCs_inv t ht_le).2
    let info := stepBundleTree sparsify (bt t) (D.U (t + 1)) (ord t) (ord (t + 1))
    have hEqNext : bt (t + 1) = info.state := hStep_st t ht
    have hS_sub_next : (coreGraph (compLSFBatch (bt t).cs (D.U (t + 1))).G
        (compLSFBatch (bt t).cs (D.U (t + 1))).lsf).IsSubgraph info.state.S_cur := by
      have h1 := hS_sub (t + 1) ht
      rw [hEqNext] at h1
      exact h1
    have hstep := (stepBundleTree_outOrder sparsify (bt t) (D.U (t + 1)) (ord t) (ord (t + 1))
      (hCs_inv t ht_le).1 hBU ρt σt hρt hσt hrot_t (hS_val t ht_le) (hS_V t ht_le)
      (hS_sub t ht_le) hS_sub_next).2
    let hG_eq := compLSFBatch_G (bt t).cs (D.U (t + 1))
    let rotPrev : Rotation (bt t).S_cur :=
      (coreRotation (L := (bt t).cs.lsf) ρt (hCs_inv t ht_le).1.hG_val
        (compLSF_RF_isRSF (hCs_inv t ht_le).1)).restrict (hS_sub t ht_le)
    let rotNext : Rotation info.state.S_cur :=
      (coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σt)
        (compLSFBatch_inv (hCs_inv t ht_le).1 hBU).hG_val
        (compLSF_RF_isRSF (compLSFBatch_inv (hCs_inv t ht_le).1 hBU))).restrict hS_sub_next
    have hcast_step : ∀ (A B : MGraph) (W : List Update) (hA : A = (bt t).S_cur)
        (hB : B = info.state.S_cur) (hW : W = info.U_S)
        (hG' : B = A.applyBatch W) (σA : Rotation A) (σB : Rotation B),
        σA.order = rotPrev.order → σB.order = rotNext.order →
        RotationBatch 2 W σA (hG' ▸ σB) := by
      intro A B W hA hB hW hG' σA σB hσA hσB
      subst hA hB hW
      have h1 : σA = rotPrev := Rotation.ext_order hσA
      have h2 : (hG' ▸ σB : Rotation ((bt t).S_cur.applyBatch info.U_S)) = rotNext :=
        Rotation.ext_order ((rotation_cast_order hG' σB).trans hσB)
      rw [h1, h2]
      exact hstep
    apply hcast_step (D_out.G t) (D_out.G (t + 1)) (D_out.U (t + 1))
      (hOut_G t ht_le) ((hOut_G (t + 1) ht).trans (by rw [hEqNext]))
      (hOut_U t ht) hG_step (ρOut t) (ρOut (t + 1))
    · rw [show ρOut t = (hOut_G t ht_le).symm ▸ rotAt t ht_le from dite_eq_left ht_le,
        rotation_cast_order]
      have h1 := BundleTreeState.outOrder_eq_restrict (bt t) (ord t) (hCs_inv t ht_le).1
        ((hCs_inv t ht_le).2.symm ▸ ρIn t) (by rw [rotation_cast_order, hρOrd t ht_le])
        (hS_sub t ht_le)
      have h2 := BundleTreeState.outOrder_eq_restrict (bt t) (ord t) (hCs_inv t ht_le).1
        ρt hρt (hS_sub t ht_le)
      exact h1.symm.trans h2
    · rw [show ρOut (t + 1) = (hOut_G (t + 1) ht).symm ▸ rotAt (t + 1) ht from dite_eq_left ht,
        rotation_cast_order]
      have h1 := BundleTreeState.outOrder_eq_restrict (bt (t + 1)) (ord (t + 1))
        (hCs_inv (t + 1) ht).1 ((hCs_inv (t + 1) ht).2.symm ▸ ρIn (t + 1))
        (by rw [rotation_cast_order, hρOrd (t + 1) ht]) (hS_sub (t + 1) ht)
      have h2 := BundleTreeState.outOrder_eq_restrict info.state (ord (t + 1))
        (compLSFBatch_inv (hCs_inv t ht_le).1 hBU) (hG_eq.symm ▸ σt)
        (by rw [rotation_cast_order, hσt]) hS_sub_next
      exact h1.symm.trans ((congrArg (fun s => s.outOrder (ord (t + 1))) hEqNext).trans h2)

/-! ## 3. Output order for `bundleRunSeq` and `sparseCoreBundleTool` -/

/-- The component-wise LSF invariant and graph agreement along `bundleRunSeq`. -/
theorem bundleRunSeq_cs_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (ord : ℕ → ℕ → List End) (j : ℕ) :
    ∀ t ≤ τ,
      let st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1
      CompLSFInv C_lsst (D.ℓ 0) st.cs ∧ st.cs.G = D.G t := by
  intro t
  induction t with
  | zero => exact fun _ => ⟨compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j, rfl⟩
  | succ t ih =>
    intro ht1
    obtain ⟨hI, hG⟩ := ih (Nat.le_of_succ_le ht1)
    have hstep := hD (t + 1) (Nat.succ_pos t) ht1
    rw [Nat.add_sub_cancel] at hstep
    have hBU : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs.G.BatchIsValid
        (D.U (t + 1)) := hG.symm ▸ hstep.1
    dsimp only
    rw [bundleRunSeq_cs]
    exact ⟨compLSFBatch_inv hI hBU, by rw [compLSFBatch_G, hG, hstep.2]⟩

/-- On an empty initial graph, `sparseCoreBundleTool.runOrdAt` stays empty and emits empty
batches. -/
private theorem bundleOutOrder_runOrdAt_empty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t
      r.1.isNonempty = false ∧ r.2 = fun _ => [] := by
  intro t
  induction t with
  | zero =>
    exact ⟨by simp [SparseCoreTool.runOrdAt, sparseCoreBundleTool, sparseCoreBundleToolWith,
      initBundleCoreWith, initBundleCoreWithParams, hV₀], rfl⟩
  | succ t ih =>
    obtain ⟨hfalse, _⟩ := ih
    change (updateBundleCore sparsify _ (D.U (t + 1)) (ord (t + 1))).1.isNonempty = false ∧
      (updateBundleCore sparsify _ (D.U (t + 1)) (ord (t + 1))).2 = fun _ => []
    simp only [updateBundleCore, hfalse, Bool.false_eq_true, ↓reduceIte, and_self]

/-- Output order (`OrderedUpTo`) for `sparseCoreBundleTool` on a nonempty initial graph,
taking only the minimal `S_cur` invariant fields. -/
theorem sparseCoreBundleTool_orderedUpTo_of_sub
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    (hS_val : ∀ t ≤ τ,
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.S_cur.IsValid)
    (hS_V : ∀ t ≤ τ,
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.S_cur.V =
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs.RF.R)
    (hS_sub : ∀ t ≤ τ,
      let st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let st := fun t => (T.runOrdAt k M N D ord t).1
    OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j) := by
  intro T st
  have hrun := sparseCoreBundleTool_runOrdAt oracle C_lsst L sparsify k M N D ord hV₀
  have hCs := bundleRunSeq_cs_inv oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD ord j
  let bt := fun t => (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1
  have hrot_eq : ∀ t ≤ τ, T.rot (st t) j = (bt t).outOrder (ord t) := fun t _ => by
    have hne : ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty =
        true := (hrun t).1
    change (if ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty = true
      then (((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.trees j).outOrder
        ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.ord
      else fun _ => []) = _
    simp only [hne, ↓reduceIte, (hrun t).2.2.1, (hrun t).2.2.2.1 j]
    rfl
  have hMain := bundleSeq_orderedUpTo sparsify D τ ord hD hOrd bt
    (T.coreInstanceOrdAt k M N D ord j)
    (fun t _ => by
      have hne : ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty =
          true := (hrun t).1
      change (if ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty = true
        then (((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.trees j).S_cur
        else emptyGraph) = _
      simp only [hne, ↓reduceIte, (hrun t).2.2.2.1 j]
      rfl)
    (fun t _ => (hrun (t + 1)).2.2.2.2 (Nat.succ_pos t) j)
    (fun _ _ => rfl) hCs hS_val hS_V hS_sub
  obtain ⟨ρOut, hOutOrd, hOutStep⟩ := hMain
  exact ⟨ρOut, fun t ht => (hOutOrd t ht).trans (hrot_eq t ht).symm, hOutStep⟩

/-- Output order (`OrderedUpTo`) for `sparseCoreBundleTool` on any valid dynamic graph (both
nonempty and empty `(D.G 0).V`; the output-order clause of
`IsSpecOrdUpTo`). -/
theorem sparseCoreBundleTool_orderedUpTo
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let st := fun t => (T.runOrdAt k M N D ord t).1
    OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j) := by
  intro T st
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hInv := (bundleRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀
      hℓ₀ hD hM hN hThresh hSp ord hOrd j hj).1
    exact sparseCoreBundleTool_orderedUpTo_of_sub oracle C_lsst L sparsify hLSST
      k M N τ hk D hG₀ hV₀ hℓ₀ hD ord hOrd j
      (fun t ht => (hInv t ht).1) (fun t ht => (hInv t ht).2.1) (fun t ht => (hInv t ht).2.2.2.1)
  · have hrunE := bundleOutOrder_runOrdAt_empty oracle C_lsst L sparsify k M N D ord hV₀
    have hG_eq : ∀ t, (T.coreInstanceOrdAt k M N D ord j).G t = emptyGraph := fun t => by
      have hne : ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty =
          false := (hrunE t).1
      change (if ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty = true
        then (((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.trees j).S_cur
        else emptyGraph) = emptyGraph
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hU_eq : ∀ t, (T.coreInstanceOrdAt k M N D ord j).U t = [] := fun t => by
      change (T.runOrdAt k M N D ord t).2 j = []
      rw [(hrunE t).2]
    have hRot_eq : ∀ t, T.rot (st t) j = fun _ => [] := fun t => by
      have hne : ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty =
          false := (hrunE t).1
      change (if ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty = true
        then (((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.trees j).outOrder
          ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.ord
        else fun _ => []) = fun _ => []
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
    let ρEmpty : Rotation emptyGraph :=
      ⟨fun _ => [], fun _ => List.nodup_nil, fun _ _ => by simp [emptyGraph]⟩
    refine ⟨fun t => (hG_eq t).symm ▸ ρEmpty,
      fun t _ => by dsimp only; rw [rotation_cast_order, hRot_eq t], fun t _ => ?_⟩
    have hStepG : (T.coreInstanceOrdAt k M N D ord j).G (t + 1) =
        ((T.coreInstanceOrdAt k M N D ord j).G t).applyBatch
          ((T.coreInstanceOrdAt k M N D ord j).U (t + 1)) := by
      rw [hG_eq (t + 1), hG_eq t, hU_eq (t + 1)]; rfl
    refine ⟨hStepG, ?_⟩
    have aux : ∀ (W : List Update) (hW : W = [])
        (hS : (T.coreInstanceOrdAt k M N D ord j).G (t + 1) =
          ((T.coreInstanceOrdAt k M N D ord j).G t).applyBatch W),
        RotationBatch 2 W ((hG_eq t).symm ▸ ρEmpty) (hS ▸ (hG_eq (t + 1)).symm ▸ ρEmpty) := by
      intro W hW hS; subst hW
      exact .nil fun _ => by rw [rotation_cast_order, rotation_cast_order, rotation_cast_order]
    exact aux _ (hU_eq (t + 1)) hStepG

end MinCostFlow.SparseCore
