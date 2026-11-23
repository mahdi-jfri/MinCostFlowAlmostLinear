module

public import MinCostFlow.SparseCore.Program.RestartModelCost
public import MinCostFlow.Chain.BundleRestartSCur

/-!
# Invariants and non-vacuity for the model-linked restart (`RestartModelInv`)

Shows that the model hypotheses of `restartBranch_model_runs` (`RestartModelCost.lean`) are
simultaneously satisfiable and hold along every run of `sparseCoreBundleRestartToolWith`:

* `exists_slotMapOK`: any branch state `tr` whose active `(component, bucket)` pairs fit in
  `slotCap` and `cap` admits a bijective slot assignment `SlotMapOK`.
* `bunAgree_refl` and `exists_bunTableMatches`: given `SlotMapOK`, the canonical table storing
  `tr.bun p` at `slotOf p` satisfies `BunTableMatches`.
* `restartScurModelInv_of_restartBundleTree`: `RestartScurModelInv` is preserved by
  `restartBundleTree` (whenever the rebuilt bucket spanners have `H.E ⊆ edges`).
* `restartScurModelInv_of_runOrdAfterUpdate`: every pre-restart branch state
  `(T.runOrdAfterUpdate k M N D ord restarts t).1.trees j` along a valid run satisfies
  `RestartScurModelInv`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-- `BunAgree` is reflexive. -/
theorem bunAgree_refl (B : BundleState) : BunAgree B B :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Any branch state whose active `(component, bucket)` pairs fit in `slotCap` and `cap` admits a
slot list and bijective slot assignment `SlotMapOK`. -/
theorem exists_slotMapOK {L slotCap cap : ℕ} (tr : BundleTreeState L)
    (h1 : (activePairs tr).card ≤ slotCap) (h2 : (activePairs tr).card ≤ cap) :
    ∃ (slots : List ℕ) (slotOf : Finset ℕ × ℤ → ℕ), SlotMapOK tr slotCap cap slots slotOf := by
  classical
  let xs := (activePairs tr).toList
  have hnd : xs.Nodup := (activePairs tr).nodup_toList
  have hlen : xs.length = (activePairs tr).card := Finset.length_toList _
  refine ⟨List.range xs.length, fun p => xs.idxOf p, List.nodup_range, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [List.mem_range]
    exact List.idxOf_lt_length_iff.mpr ((Finset.mem_toList (s := activePairs tr)).mpr hp)
  · intro s hs
    rw [List.mem_range] at hs
    have hi : xs.idxOf (xs[s]'hs) < xs.length := List.idxOf_lt_length_iff.mpr (List.getElem_mem hs)
    refine ⟨xs[s]'hs, (Finset.mem_toList (s := activePairs tr)).mp (List.getElem_mem hs), ?_⟩
    exact (List.Nodup.getElem_inj_iff hnd (hi := hi) (hj := hs)).mp (List.getElem_idxOf hi)
  · intro p₁ hp₁ p₂ hp₂ heq
    have h1' : p₁ ∈ xs := (Finset.mem_toList (s := activePairs tr)).mpr hp₁
    have h2' : p₂ ∈ xs := (Finset.mem_toList (s := activePairs tr)).mpr hp₂
    have hi₁ : xs.idxOf p₁ < xs.length := List.idxOf_lt_length_iff.mpr h1'
    have hi₂ : xs.idxOf p₂ < xs.length := List.idxOf_lt_length_iff.mpr h2'
    have hg₁ : xs[xs.idxOf p₁]'hi₁ = p₁ := List.getElem_idxOf hi₁
    have hg₂ : xs[xs.idxOf p₂]'hi₂ = p₂ := List.getElem_idxOf hi₂
    rw [← hg₁, ← hg₂]
    congr 1
  · intro s hs
    rw [List.mem_range] at hs
    omega

/-- Given `SlotMapOK`, the canonical bundle table storing `some (tr.bun p)` at `slotOf p` satisfies
`BunTableMatches`. -/
theorem exists_bunTableMatches {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} (hMap : SlotMapOK tr slotCap cap slots slotOf) :
    ∃ S : Fin slotCap → Option BundleState, BunTableMatches tr slotOf S := by
  classical
  let S : Fin slotCap → Option BundleState := fun i =>
    if h : ∃ p ∈ activePairs tr, slotOf p = i.1 then some (tr.bun h.choose) else none
  refine ⟨S, fun p hp => ?_⟩
  have hmem : slotOf p ∈ slots := hMap.2.1 p hp
  have hs : slotOf p < slotCap := (hMap.2.2.2.2 _ hmem).1
  have hex : ∃ q ∈ activePairs tr, slotOf q = slotOf p := ⟨p, hp, rfl⟩
  have hch : hex.choose = p :=
    hMap.2.2.2.1 hex.choose hex.choose_spec.1 p hp hex.choose_spec.2
  refine ⟨hs, tr.bun p, ?_, bunAgree_refl _⟩
  show (if h : ∃ q ∈ activePairs tr, slotOf q = slotOf p then some (tr.bun h.choose) else none) = _
  rw [dite_eq_left_of_eq_true (eq_true hex), hch]

/-- `RestartScurModelInv` is preserved by `restartBundleTree` when `CoreCordOf` holds and each
rebuilt bucket spanner has its edges inside the rebuilt bundle edges. -/
theorem restartScurModelInv_of_restartBundleTree {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState L} {ord cord : ℕ → List End}
    (hcord : CoreCordOf tr.cs ord cord) (hMod : RestartScurModelInv tr)
    (hInitSub : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      ((restartBundleTree L sparsify tr ord).dyn (C, b)).H.E ⊆
        (restartBucketBundle tr ord C b).edges) :
    RestartScurModelInv (restartBundleTree L sparsify tr ord) := by
  have ⟨_, _, hI, _, _, _⟩ := hcord
  obtain ⟨hAct, _, _, _, hBunInv⟩ := hMod
  set tr' := restartBundleTree L sparsify tr ord
  have hEdgesEq : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr'.bun (C, b)).edges = (tr.bun (C, b)).edges := by
    intro C hC b _
    simp only [tr', restartBundleTree, hC, ↓reduceIte]
    exact restartBucketBundle_edges_of_coreCord hcord C b
  have hDynEq : (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (tr'.dyn (C, b)).H.E) =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        (DynSpanner.init (SparseCore.normGraph (restartBucketBundle tr ord C b).graph) L
          (phaseBase ((SparseCore.normGraph (restartBucketBundle tr ord C b).graph).n +
            tr.splitBound) L) (sparsify tr.m₀)).state.H.E := by
    refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b _ => ?_
    simp only [tr', restartBundleTree, hC, ↓reduceIte]
  have hSE' : tr'.S_cur.E =
      (tr'.activeComps.biUnion fun C => (tr'.activeBuckets C).biUnion fun b => (tr'.dyn (C, b)).H.E) ∪
        (tr'.activeComps.biUnion fun C => tr'.extraEdges C) ∪ tr'.cs.crossEdges := by
    change _ = (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
      (tr'.dyn (C, b)).H.E) ∪ _ ∪ tr.cs.crossEdges
    rw [hDynEq]
    rfl
  have hTgtSub : tr'.S_cur.E ⊆ tr.cs.G.E \ tr.cs.RF.F.E := by
    rw [hSE']
    intro e he
    rcases Finset.mem_union.mp he with he12 | heX
    · rcases Finset.mem_union.mp he12 with heD | heEx
      · rw [Finset.mem_biUnion] at heD
        obtain ⟨C, hC, heB⟩ := heD
        rw [Finset.mem_biUnion] at heB
        obtain ⟨b, hb, heb⟩ := heB
        have h1 : e ∈ (restartBucketBundle tr ord C b).edges := hInitSub C hC b hb heb
        rw [restartBucketBundle_edges_of_coreCord hcord C b] at h1
        exact (hBunInv C hC b hb).1 h1
      · rw [Finset.mem_biUnion] at heEx
        obtain ⟨C, hC, heExC⟩ := heEx
        exact compLSF_comp_sdiff_sub hI (hAct hC) (Finset.mem_sdiff.mp heExC).1
    · exact compLSF_crossEdges_sub hI heX
  refine ⟨hAct, rfl, hSE', ⟨Finset.Subset.rfl, hTgtSub, fun _ _ => ⟨rfl, rfl⟩⟩, ?_⟩
  intro C hC b hb
  have hE := hEdgesEq C hC b hb
  have hOld := hBunInv C hC b hb
  refine ⟨hE ▸ hOld.1, hE ▸ hOld.2.1, hE ▸ hOld.2.2.1, ?_⟩
  have h1 := hInitSub C hC b hb
  rwa [restartBucketBundle_edges_of_coreCord hcord C b, ← hE] at h1

/-- Every pre-restart branch state `(T.runOrdAfterUpdate k M N D ord restarts t).1.trees j` along
any valid run of `sparseCoreBundleRestartToolWith` satisfies `RestartScurModelInv`. -/
theorem restartScurModelInv_of_runOrdAfterUpdate
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (t : ℕ) (ht : t ≤ τ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    RestartScurModelInv ((T.runOrdAfterUpdate k M N D ord restarts t).1.trees j) := by
  intro T
  set pre := (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit t ht
  have hSc := (runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit t ht).1
  have hG₀_eq : pre.cs.G₀ = D.G 0 := by
    rw [hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hAct : pre.activeComps ⊆ components pre.cs.G₀ := by
    rw [hG₀_eq]; exact hBun.2.2.2.2.2.2.2.2.2.1.2
  have hI : CompLSFInv C_lsst (D.ℓ 0) pre.cs := hBun.2.2.2.2.2.2.2.1
  have hcsG : pre.cs.G = D.G t := hBun.2.2.2.2.2.2.2.2.1
  obtain ⟨ρ_t, hρ_t⟩ := orderedUpTo_rot_at hOrd ht hcsG
  have hab : pre.activeBuckets =
      (initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets :=
    hBun.2.2.2.2.1
  -- Extract `(pre.dyn (C, b)).H.E ⊆ (pre.bun (C, b)).edges` via the last restart `s₀`.
  set s₀ := bundleLastRestart restarts j (t - 1)
  have hs₀_spec := bundleLastRestart_spec restarts j (t - 1)
  have hdyn_H_sub : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (pre.dyn (C, b)).H.E ⊆ (pre.bun (C, b)).edges := by
    intro C hC b
    by_cases ht0 : t = 0
    · subst ht0
      have hcb := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b)
      have hPart := hcb.1.1 ρ_t hI.hG_val (compLSF_RF_isRSF hI) hρ_t
      have hVal : (SparseCore.normGraph (pre.bun (C, b)).graph).IsValid :=
        SparseCore.normGraph_isValid (BundleState.graph_isValid hPart)
      have hm : (SparseCore.normGraph (pre.bun (C, b)).graph).m ≤ M := by
        rw [SparseCore.normGraph_m]
        have hsub : (pre.bun (C, b)).edges ⊆ (D.G 0).E := by
          rw [← hcsG]
          exact hPart.1.trans Finset.sdiff_subset
        exact le_trans (Finset.card_le_card hsub) hM
      have hq1 : 1 ≤ phaseBase ((SparseCore.normGraph (pre.bun (C, b)).graph).n +
          bundleSplitBudget k M) L := le_trans (by omega) (two_le_phaseBase _ L)
      have hinv0 := (DynSpanner.runInv_all hVal hL hq1 hm hSp (us := [])
        (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
      exact hinv0.H_sub.2.1
    · have hst : s₀ ≤ t := by omega
      have hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r h1 h2 =>
        hs₀_spec.2.2 r h1 (by omega)
      have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
        k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst ht
        hs₀_spec.2.1 hNoRest C hC b
      have hEp := (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j hst).2.2
      have hlt : s₀ < t := by omega
      have heq_t : epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j (t - s₀) = pre :=
        hEp hlt
      have hsub := (hDyn.2.2.2.2.2.2.2.2.2.1 (t - s₀) le_rfl).2.2.2.1
      have hge := (hDyn.2.2.2.2.2.2.2.2.2.1 (t - s₀) le_rfl).2.1
      rw [heq_t] at hsub hge
      exact hsub.2.1.trans (hge.2.1 ▸ Finset.Subset.rfl)
  refine ⟨hAct, hSc.2.1, hab ▸ hSc.2.2.1, hSc.2.2.2, ?_⟩
  intro C hC b _
  have hC0 : C ∈ components (D.G 0) := hG₀_eq ▸ hAct hC
  have hcb := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b)
  refine ⟨(hcb.1.1 ρ_t hI.hG_val (compLSF_RF_isRSF hI) hρ_t).1, hcb.1.2.2, hcb.2.2.2.2.1,
    hdyn_H_sub C hC0 b⟩

end

end MinCostFlow.SparseCore.Program.Restart
