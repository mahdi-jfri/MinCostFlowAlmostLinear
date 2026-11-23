module

public import MinCostFlow.Chain.BundleRestartMachCost
public import MinCostFlow.Chain.Ordered.ConcreteDefs
public import MinCostFlow.SparseCore.BundleSpanCharge
public import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleRunsSpec
import MinCostFlow.SparseCore.BundleCoreParams
import MinCostFlow.DynSpanner.Walks
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Terms 2, 4, and 6 of `stepBundleTree_machCost` (`AssemblyDryRunSCToolStepTerms`)

Proves the single-step bounds for the bundle-batch, spanner-charge, and lazy-initialization terms
of `stepBundleTree_machCost` (`branchStepCharge`) on any reached branch of
`sparseCoreBundleRestartToolWith` / `sparseCoreBundleRestartToolMachWith`, with no input rotation
requirement on the step batch `U`:

* **Term 2 (`stepBundleTree_bunEnc_sum_le`)**:
  `∑_{C ∈ active', b ∈ actB C} (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b)) ≤ 3 * (k + 1) * M`.
  Uses `bundleRunsStep_core` to map every new bundle injectively into `edgeEnds R.2.edges`
  (`batchSplitCount ≤ 2 * B.edges.card`), `countP_deleteTag_le_card_of_delOrSplit`, and the
  `delOrSplit` degree monotonicity `G.batchEnc U ≤ (G.maxDeg + 1) * U.length`.
* **Envelope (`concreteEnv_gamma_r_bounds`)**: extracts the parameter inequalities from
  `Γ = ⌈(bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2)⌉₊` for `E = concreteEnv …`.
* **Term 4 (`stepBundleTreeMach_dynMach_sum_le`)**:
  `∑ spanBatchChargeWith … ≤ 1080 * spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M`.
* **Term 6 (`stepBundleTreeMach_lazyMach_sum_le`)**:
  `info.newlyActive.sum tr.lazyMachInitCost ≤ spanConst * (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M`.
-/

public section

namespace MinCostFlow.Final.DryRun

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.Bundle

/-! ## 1. Term 2: `b`-free bound on bundle-batch encodings -/

private lemma deg_split_le_old {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (hv : v ∈ G.V) (hv' : v' ∉ G.V) :
    (G.applyUpdate (.split v v' St Sh)).deg v ≤ G.deg v := by
  have hne : v ≠ v' := fun h => hv' (h ▸ hv)
  let G' := G.applyUpdate (.split v v' St Sh)
  have hpart : ∀ (S : Finset ℕ) (f f' : ℕ → ℕ),
      (∀ e, f' e = if e ∈ S ∧ f e = v then v' else f e) →
      (G'.E.filter fun e => f' e = v).card ≤ (G.E.filter fun e => f e = v).card := by
    intro S f f' hf'
    refine Finset.card_le_card fun e he => ?_
    simp only [Finset.mem_filter, hf'] at he ⊢
    change e ∈ G.E ∧ (if e ∈ S ∧ f e = v then v' else f e) = v at he
    split_ifs at he
    · exact absurd he.2.symm hne
    · exact he
  exact Nat.add_le_add (hpart St G.tail G'.tail (fun _ => rfl))
    (hpart Sh G.head G'.head (fun _ => rfl))

private lemma delSplit_updateEnc_le_maxDeg {G : MGraph} {u : Update}
    (hu : G.UpdateIsValid u) (hds : isDelOrSplit u) :
    G.updateEnc u ≤ G.maxDeg + 1 := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete _ => simp [MGraph.updateEnc]
  | split v v' St Sh =>
    rcases hu with ⟨hv, hv', _, _⟩
    have h1 : (G.applyUpdate (.split v v' St Sh)).deg v ≤ G.deg v :=
      deg_split_le_old hv hv'
    have h2 : G.deg v ≤ G.maxDeg := Finset.le_sup (f := G.deg) hv
    simp only [MGraph.updateEnc]
    have hmin : min ((G.applyUpdate (.split v v' St Sh)).deg v)
        ((G.applyUpdate (.split v v' St Sh)).deg v') ≤ G.maxDeg :=
      (min_le_left _ _).trans (h1.trans h2)
    omega

private lemma delSplit_batchEnc_le_maxDeg {G : MGraph} (hG : G.IsValid) {U : List Update}
    (hU : G.BatchIsValid U) (hds : ∀ u ∈ U, isDelOrSplit u) :
    G.batchEnc U ≤ (G.maxDeg + 1) * U.length := by
  induction U generalizing G with
  | nil => simp [MGraph.batchEnc]
  | cons u rest ih =>
    have hu_ds := hds u List.mem_cons_self
    have hrest_ds := fun op hop => hds op (List.mem_cons_of_mem _ hop)
    have h1 := delSplit_updateEnc_le_maxDeg hU.1 hu_ds
    have hG1 : (G.applyUpdate u).IsValid := DynSpanner.isValid_applyUpdate_of_delOrSplit hG hU.1 hu_ds
    have hdeg1 : (G.applyUpdate u).maxDeg ≤ G.maxDeg := maxDeg_applyUpdate_le hG hU.1 hu_ds
    have h2 := ih hG1 hU.2 hrest_ds
    have h3 : ((G.applyUpdate u).maxDeg + 1) * rest.length ≤ (G.maxDeg + 1) * rest.length :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [MGraph.batchEnc, List.length_cons]
    have hmul : (G.maxDeg + 1) * (rest.length + 1) = (G.maxDeg + 1) + (G.maxDeg + 1) * rest.length := by
      ring
    omega

private lemma bundleRunsStep_splitCount_le_two_mul_edges {cs : CompLSFState} {B : BundleState}
    {k : ℕ} {ord ord' : ℕ → List End} {U : List Update}
    (h : BundleStepReady cs B k ord ord' U) :
    batchSplitCount (bundleRunsStep cs B k ord' U).1 ≤ 2 * B.edges.card := by
  classical
  obtain ⟨⟨UBw, Bw⟩, hS, hL⟩ := bundleStepSpec_exists h
  obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, -, hσ, -, hU, hB⟩ := h
  have hI' := compLSFBatch_inv hI hU
  let σ' : Rotation (compLSFBatch cs U).G := (compLSFBatch_G cs U).symm ▸ σ
  have hσ' : σ'.order = ord' := by
    have hcast : ∀ {G H : MGraph} (he : G = H) (r : Rotation G), (he ▸ r : Rotation H).order = r.order := by
      intro G H he r; cases he; rfl
    exact (hcast _ σ).trans hσ
  obtain ⟨hwP, hwv, hwg, hwt, -, -, -⟩ := hS
  obtain ⟨-, -, -, hwE, -⟩ := hL
  dsimp only at hwP hwv hwg hwt hwE
  have hpar0 : ∀ b ∈ B.vertices, B.parent b ∈ (compLSFBatch cs U).RF.R :=
    fun b hb => (compLSFBatch_decremental hI hU).2 (hB.2.1 b hb)
  have core := bundleRunsStep_core (k := k) (fun x hx => (hB.2.2.1 x hx).1)
    (fun b hb => (hB.2.2.2 b hb).1) hpar0 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    (hwP σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ') hwv hwg hwt hwE
  set R := bundleRunsStep cs B k ord' U
  obtain ⟨-, -, c3, -, -, -, -, -, -, c10, c11, c12⟩ := core
  have hnew : ∀ c ∈ R.2.vertices \ B.vertices, ∃ x ∈ R.2.ends c, True := by
    intro c hc
    obtain ⟨hcR, hcNotB⟩ := Finset.mem_sdiff.mp hc
    rcases c3 c hcR with ⟨x, hx, _⟩ | ⟨hcB, _⟩
    · exact ⟨x, hx, trivial⟩
    · exact absurd hcB hcNotB
  let f : ℕ → End := fun c => if hc : c ∈ R.2.vertices \ B.vertices then (hnew c hc).choose else (0, true)
  have hf_maps : ∀ c ∈ R.2.vertices \ B.vertices, f c ∈ edgeEnds R.2.edges := by
    intro c hc
    have hx : (hnew c hc).choose ∈ R.2.ends c := (hnew c hc).choose_spec.1
    have hfx : f c = (hnew c hc).choose := dite_eq_left hc
    rw [hfx]
    exact (mem_edgeEnds _ _).mpr ((BundleState.mem_ends _ _ _).mp hx).1
  have hf_inj : Set.InjOn f ↑(R.2.vertices \ B.vertices) := by
    intro c₁ hc₁ c₂ hc₂ hEq
    have hc₁' : c₁ ∈ R.2.vertices \ B.vertices := Finset.mem_coe.mp hc₁
    have hc₂' : c₂ ∈ R.2.vertices \ B.vertices := Finset.mem_coe.mp hc₂
    have hx₁ : f c₁ ∈ R.2.ends c₁ := by
      have hfx : f c₁ = (hnew c₁ hc₁').choose := dite_eq_left hc₁'
      rw [hfx]; exact (hnew c₁ hc₁').choose_spec.1
    have hx₂ : f c₂ ∈ R.2.ends c₂ := by
      have hfx : f c₂ = (hnew c₂ hc₂').choose := dite_eq_left hc₂'
      rw [hfx]; exact (hnew c₂ hc₂').choose_spec.1
    rw [← hEq] at hx₂
    exact ((BundleState.mem_ends _ _ _).mp hx₁).2.symm.trans ((BundleState.mem_ends _ _ _).mp hx₂).2
  have hcard_le : (R.2.vertices \ B.vertices).card ≤ (edgeEnds R.2.edges).card :=
    Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hsdiff_eq : (R.2.vertices \ B.vertices).card = batchSplitCount R.1 := by
    have hadd := Finset.card_sdiff_add_card_eq_card c12
    omega
  rw [← hsdiff_eq]
  refine hcard_le.trans ?_
  rw [card_edgeEnds, c11]
  exact Nat.mul_le_mul_left 2 (Finset.card_le_card Finset.sdiff_subset)

/-- Term 2 single-step bound (`b`-free): on any reached branch `tr` of
`sparseCoreBundleRestartToolWith`, the sum of bundle-batch encodings across all active buckets
is at most `3 * (k + 1) * M`. -/
theorem stepBundleTree_bunEnc_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (t r : ℕ) (ht : t ≤ τ) (hInit : IsValidLSFInitFor lsfInit C_lsst k r)
    (U : List Update) (ord_in ord' : ℕ → List End) :
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let tr := (Tb.runOrdAfterRestarts k M N D ord restarts t).trees r
    let info := stepBundleTree sparsify tr U ord_in ord'
    (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))) ≤ 3 * (k + 1) * M := by
  classical
  intro Tb tr info
  set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) r
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd r hInit t ht
  have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
    (Tb.runOrdAfterUpdate k M N D ord restarts t).1 (restarts t)).2.2.2.2.1 r
  have hcs_eq : tr.cs = ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).cs := hbf.cs
  have hact_eq : tr.activeComps =
      ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).activeComps := hbf.activeComps
  have hactB_eq : tr.activeBuckets = st₀.activeBuckets :=
    hbf.activeBuckets.trans hBun.2.2.2.2.1
  have hk_eq : tr.k = k := hbf.k.trans hBun.1
  have hG0_cs : tr.cs.G₀ = D.G 0 := by
    rw [hcs_eq, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hact'_sub : info.state.activeComps ⊆ components (D.G 0) := by
    intro C hCact
    change C ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps) at hCact
    rcases Finset.mem_union.mp hCact with h1 | h2
    · exact hBun.2.2.2.2.2.2.2.2.2.1.2 (hact_eq ▸ h1)
    · rw [← hG0_cs]
      exact Finset.filter_subset _ _ (Finset.mem_sdiff.mp h2).1
  let s₀ := bundleLastRestart restarts r t
  obtain ⟨hs₀_le, hs₀_rest, hNoRest_le⟩ := bundleLastRestart_spec restarts r t
  have hNoRest : ∀ s, s₀ < s → s < t → r ∉ restarts s :=
    fun s h1 h2 => hNoRest_le s h1 (Nat.le_of_lt h2)
  have hEp_eq : epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r (t - s₀) = tr := by
    have hnor : r ∉ restarts t ∨ s₀ = t := by
      by_cases heq : s₀ = t
      · exact Or.inr heq
      · exact Or.inl (hNoRest_le t (by omega) le_rfl)
    exact (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r hs₀_le).2.1 hnor
  have hper_bucket : ∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
      (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b)) ≤ 3 * (k + 1) * ((st₀.bun (C, b)).graph).m := by
    intro C hC b _hb
    have hDynSpec := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify k M N τ hk D ord
      restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t r hInit hs₀_le ht hs₀_rest hNoRest C hC b
    set st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r
    set Hb := ((st 0).bun (C, b)).graph
    set Us_ep : List (List Update) :=
      (List.range (t - s₀)).map fun δ =>
        (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))).U_B (C, b)
    have hδ_end := hDynSpec.2.2.2.2.2.2.2.2.2.1 (t - s₀) le_rfl
    have htr_Geq : GraphEq (tr.dyn (C, b)).G (tr.bun (C, b)).graph := by
      rw [← hEp_eq]; exact hδ_end.2.1
    have htr_Gval : (tr.dyn (C, b)).G.IsValid := by
      rw [← hEp_eq]; exact hδ_end.2.2.1
    by_cases hReady : BundleStepReady tr.cs (tr.bun (C, b)) tr.k ord_in ord' U
    · have hSpecB := bundleCompStep_spec hReady
      have hLocB := bundleCompStep_localSpec hReady
      have hUB_eq : info.U_B (C, b) = (bundleRunsStep tr.cs (tr.bun (C, b)) tr.k ord' U).1 := by
        change (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord_in ord' U).1 = _
        rw [bundleCompStep_eq hReady]
      have hUB_val : (tr.dyn (C, b)).G.BatchIsValid (info.U_B (C, b)) :=
        (graphEq_batchIsValid htr_Geq _).mpr hSpecB.2.1
      have hUB_ds : ∀ op ∈ info.U_B (C, b), isDelOrSplit op := hSpecB.2.2.2.1
      have hdeg_le_k : (tr.dyn (C, b)).G.maxDeg ≤ k := by
        have hNormEq : GraphEq (normGraph Hb) Hb := normGraph_graphEq Hb
        have hNormVal : (normGraph Hb).IsValid :=
          graphEq_isValid (graphEq_symm hNormEq) hDynSpec.1
        have hNormM : (normGraph Hb).m ≤ M := (graphEq_m hNormEq).trans_le (hDynSpec.2.1.trans hM)
        have hUs_val : (normGraph Hb).BatchIsValid Us_ep.flatten :=
          (graphEq_batchIsValid hNormEq _).mpr hDynSpec.2.2.2.2.2.1
        have hUs_ds : ∀ op ∈ Us_ep.flatten, isDelOrSplit op := hDynSpec.2.2.2.2.2.2.1
        have hq1 : 1 ≤ phaseBase (Hb.n + bundleSplitBudget k M) L :=
          le_trans (by decide : 1 ≤ 2) (two_le_phaseBase _ _)
        have hSpecPrev := DynSpanner.batchTrace_spec hNormVal hL hq1 hNormM hSp hUs_val hUs_ds
        have hUs_len : Us_ep.length = t - s₀ := by simp [Us_ep]
        have hPrevG : (tr.dyn (C, b)).G = (normGraph Hb).applyBatch Us_ep.flatten := by
          have hdyn_eq : tr.dyn (C, b) =
              DynSpanner.runBatchState (L := L) (normGraph Hb) (phaseBase (Hb.n + bundleSplitBudget k M) L)
                (sparsify M) Us_ep (t - s₀) := by rw [← hEp_eq]; exact hδ_end.1
          rw [hdyn_eq]
          have h1 := (hSpecPrev.1 (t - s₀) (by omega)).2.1
          have htake : Us_ep.flatten.take (batchPrefixLen Us_ep (t - s₀)) = Us_ep.flatten := by
            simp [batchPrefixLen, ← hUs_len]
          rw [htake] at h1
          exact h1
        have hinv_deg : ((normGraph Hb).applyBatch Us_ep.flatten).maxDeg ≤ (normGraph Hb).maxDeg :=
          (batch_delOrSplit_invariants Us_ep.flatten (normGraph Hb) hNormVal hUs_val hUs_ds).2.2.2.1
        rw [hPrevG]
        exact hinv_deg.trans ((graphEq_maxDeg hNormEq).trans_le hDynSpec.2.2.2.1)
      have henc_le : (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b)) ≤
          (k + 1) * (info.U_B (C, b)).length := by
        refine (delSplit_batchEnc_le_maxDeg htr_Gval hUB_val hUB_ds).trans ?_
        exact Nat.mul_le_mul_right _ (by omega)
      have hlen_eq := length_eq_delete_add_split_of_delOrSplit hUB_ds
      have hdel_le : (info.U_B (C, b)).countP deleteTag ≤ (tr.bun (C, b)).edges.card := by
        have hsub_del : ∀ op ∈ info.U_B (C, b), deleteTag op = true →
            ∃ e ∈ (tr.bun (C, b)).edges, op = .delete e := by
          intro op hop hd
          obtain ⟨e, he, hEq, _⟩ := hLocB.2.1 op hop hd
          exact ⟨e, he, hEq⟩
        have h1 := countP_deleteTag_le_card_of_delOrSplit hSpecB.2.1 hUB_ds hsub_del
        exact h1.trans (Finset.card_le_card Finset.inter_subset_right)
      have hsp_le : batchSplitCount (info.U_B (C, b)) ≤ 2 * (tr.bun (C, b)).edges.card := by
        rw [hUB_eq]
        exact bundleRunsStep_splitCount_le_two_mul_edges hReady
      have hedges_le : (tr.bun (C, b)).edges.card ≤ ((st₀.bun (C, b)).graph).m := by
        have h1 := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1
        have h2 := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1
        change (tr.bun (C, b)).edges.card ≤ (st₀.bun (C, b)).edges.card
        rw [h2, h1]
        exact Finset.card_le_card Finset.sdiff_subset
      have hlen_le : (info.U_B (C, b)).length ≤ 3 * ((st₀.bun (C, b)).graph).m := by omega
      calc (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))
          ≤ (k + 1) * (info.U_B (C, b)).length := henc_le
        _ ≤ (k + 1) * (3 * ((st₀.bun (C, b)).graph).m) := Nat.mul_le_mul_left _ hlen_le
        _ = 3 * (k + 1) * ((st₀.bun (C, b)).graph).m := by ring
    · have hUB_nil : info.U_B (C, b) = [] := by
        change (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord_in ord' U).1 = []
        rw [bundleCompStep_of_not hReady]
      rw [hUB_nil]; simp [MGraph.batchEnc]
  have hsum_m := (initBundleTreeWith_buckets_sum_le lsfInit L sparsify (M := M) (N := N) (G₀ := D.G 0) hk (D.ℓ 0) (ord 0) r).2.1
  calc (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
          (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b)))
      ≤ (components (D.G 0)).sum (fun C => (st₀.activeBuckets C).sum fun b =>
          (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))) := by
        rw [hactB_eq]
        exact Finset.sum_le_sum_of_subset hact'_sub
    _ ≤ (components (D.G 0)).sum (fun C => (st₀.activeBuckets C).sum fun b =>
          3 * (k + 1) * ((st₀.bun (C, b)).graph).m) :=
        Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => hper_bucket C hC b hb
    _ = 3 * (k + 1) * ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          ((st₀.bun (C, b)).graph).m) := by
        simp only [← Finset.mul_sum]
    _ ≤ 3 * (k + 1) * (D.G 0).m := Nat.mul_le_mul_left _ hsum_m
    _ ≤ 3 * (k + 1) * M := Nat.mul_le_mul_left _ hM

/-! ## 2. Parameter envelope inequalities from `Γ = ⌈γ_r(M₀²)⌉` -/

private lemma coreE_L_ge_gamma_l (L : ℕ) (P : SparsifyParams) :
    P.γ_ℓ ≤ coreE_L L P := by
  unfold coreE_L
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) := one_le_pow₀ (by norm_num)
  have hgc : (1 : ℝ) ≤ P.γ_c ^ (L + 1) := one_le_pow₀ P.hγ_c
  have hgl_ge1 : (1 : ℝ) ≤ P.γ_ℓ := P.hγ_ℓ
  have hexp : 1 ≤ (L + 1) * (L + 2) / 2 + 2 := by omega
  have hgl_pow : P.γ_ℓ ≤ P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by
    calc P.γ_ℓ = P.γ_ℓ ^ 1 := (pow_one _).symm
      _ ≤ P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := pow_le_pow_right₀ hgl_ge1 hexp
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) :=
    one_le_mul_of_one_le_of_one_le h3 hgc
  nlinarith

/-- Extracts all real-analysis inequalities needed for Terms 4 and 6 from
`Γ := ⌈(bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2)⌉₊` at `E = concreteEnv …`. -/
theorem concreteEnv_gamma_r_bounds (C_lsst : ℝ) (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ B_cap spanConst M : ℕ) (hM : M ≤ M₀ ^ 2) :
    let E := Chain.Ordered.concreteEnv C_lsst params hp_s hp_t M₀ B_cap
    let P_hi := monoSparsifyParamsEnvelope params (M₀ ^ 2)
    let Γ : ℕ := ⌈(bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2)⌉₊
    coreE_L E.L P_hi * (P_hi.K_t + P_hi.K_s + 1) * ((E.L : ℝ) * bundleNRoot E.L M) ≤ 2 * (Γ : ℝ) ∧
    P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) ≤ (Γ : ℝ) ∧
    2 * P_hi.K_s * P_hi.γ_ℓ ≤ (Γ : ℝ) ∧
    P_hi.γ_ℓ ≤ (Γ : ℝ) ∧
    1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) ≤ 115 * (M : ℝ) + 4 ∧
    bundleLambda P_hi M ≤ 115 * (M : ℝ) + 4 := by
  intro E P_hi Γ
  have hγr_eq : (bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2) =
      bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2) := rfl
  have hΓ_ge : bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2) ≤ (Γ : ℝ) := by
    rw [← hγr_eq]; exact Nat.le_ceil _
  have hRec_ge4 : (4 : ℝ) ≤ bundleRecBase E (M₀ ^ 2) :=
    (bundleRecEnv_ge_four E (M₀ ^ 2)).trans (le_max_left _ _)
  have hCM_ge1 : (1 : ℝ) ≤ bundleCostMult E (M₀ ^ 2) := le_max_left _ _
  have hCM_le_Γ : bundleCostMult E (M₀ ^ 2) ≤ (Γ : ℝ) := by nlinarith
  have hRec_le_Γ : bundleRecBase E (M₀ ^ 2) ≤ (Γ : ℝ) := by nlinarith
  have hcoreE_ge1 : (1 : ℝ) ≤ coreE_L E.L P_hi :=
    P_hi.hγ_ℓ.trans (coreE_L_ge_gamma_l E.L P_hi)
  have hKt_nn : 0 ≤ P_hi.K_t := P_hi.hK_t
  have hKs_nn : 0 ≤ P_hi.K_s := P_hi.hK_s
  have hγl_ge1 : 1 ≤ P_hi.γ_ℓ := P_hi.hγ_ℓ
  have hL_ge1 : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
  have hNR_ge1 : 1 ≤ bundleNRoot E.L (M₀ ^ 2) := bundleParams_nRoot_ge_one E.L (M₀ ^ 2)
  have hNR_mono : bundleNRoot E.L M ≤ bundleNRoot E.L (M₀ ^ 2) :=
    bundleParams_nRoot_mono (L := E.L) hM
  have hLNR_le : (E.L : ℝ) * bundleNRoot E.L M ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) :=
    (mul_le_mul_of_nonneg_left hNR_mono (by positivity)).trans (le_max_right _ _)
  have hmaxLNR_ge1 : 1 ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) := le_max_left _ _
  have hCM_body : coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
      max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) * ((E.L : ℝ) + 1) ≤
      bundleCostMult E (M₀ ^ 2) := le_max_right _ _
  have hB_ge1 : (1 : ℝ) ≤ (E.B_fn (M₀ ^ 2) : ℝ) := by exact_mod_cast E.hB_pos (M₀ ^ 2)
  have hLamS_ge1 : 1 ≤ bundleLambdaS P_hi (M₀ ^ 2) := by
    unfold bundleLambdaS
    exact one_le_pow₀ (by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax (M₀ ^ 2) : ℝ) + ((M₀ ^ 2 : ℕ) : ℝ) + 2 by linarith)])
  have hRec_Ks : 22 * (E.B_fn (M₀ ^ 2) : ℝ) * ((E.L : ℝ) + 1) * P_hi.K_s * P_hi.γ_ℓ *
      bundleLambdaS P_hi (M₀ ^ 2) ≤ bundleRecEnv E (M₀ ^ 2) := by
    have hP_eq : E.P_fn (M₀ ^ 2) = P_hi := rfl
    unfold bundleRecEnv
    rw [hP_eq]
    have hcp := bundleParams_bucketRec_pos E.L P_hi (M₀ ^ 2)
    have huc : 0 ≤ bundleUCRatioHi E (M₀ ^ 2) := by linarith [bundleUCRatioHi_ge_one E (M₀ ^ 2)]
    have ht1 : 0 ≤ (E.B_fn (M₀ ^ 2) : ℝ) *
        ((3 + 2 * coreE82Len E.L P_hi) * bundleBucketRecUH E.L P_hi (M₀ ^ 2) +
          2 * bundleBucketRecD E.L P_hi (M₀ ^ 2)) * (2 * bundleUCRatioHi E (M₀ ^ 2)) := by
      have := hcp.1; have := hcp.2.1; have := hcp.2.2; positivity
    have ht3 : 0 ≤ 224 * (Real.log (E.c_n * (((M₀ ^ 2 : ℕ) : ℝ) + 1) + 2)) ^ 2 := by positivity
    linarith
  have h2Ks_le_Rec : 2 * P_hi.K_s * P_hi.γ_ℓ ≤ bundleRecBase E (M₀ ^ 2) := by
    have h1 : 2 * P_hi.K_s * P_hi.γ_ℓ ≤
        22 * (E.B_fn (M₀ ^ 2) : ℝ) * ((E.L : ℝ) + 1) * P_hi.K_s * P_hi.γ_ℓ *
          bundleLambdaS P_hi (M₀ ^ 2) := by
      have hfac : (2 : ℝ) ≤ 22 * (E.B_fn (M₀ ^ 2) : ℝ) * ((E.L : ℝ) + 1) *
          bundleLambdaS P_hi (M₀ ^ 2) := by
        have hBL : 1 ≤ (E.B_fn (M₀ ^ 2) : ℝ) * ((E.L : ℝ) + 1) :=
          one_le_mul_of_one_le_of_one_le hB_ge1 (by linarith)
        have hBLlam : 1 ≤ (E.B_fn (M₀ ^ 2) : ℝ) * ((E.L : ℝ) + 1) * bundleLambdaS P_hi (M₀ ^ 2) :=
          one_le_mul_of_one_le_of_one_le hBL hLamS_ge1
        linarith
      have hmul := mul_le_mul_of_nonneg_right hfac (show 0 ≤ P_hi.K_s * P_hi.γ_ℓ by positivity)
      linarith
    exact h1.trans (hRec_Ks.trans (le_max_left _ _))
  have hKs_le_Rec : P_hi.K_s ≤ bundleRecBase E (M₀ ^ 2) := by nlinarith
  have hKt_piece : P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) ≤ bundleCostMult E (M₀ ^ 2) := by
    have h1 : P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) ≤ P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1 := by linarith
    have hfac : 1 ≤ coreE_L E.L P_hi * max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) * ((E.L : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hcoreE_ge1 hmaxLNR_ge1) (by linarith)
    have h2 : P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1 ≤
        coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) * ((E.L : ℝ) + 1) := by
      have hnn : 0 ≤ P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1 := by positivity
      have := mul_le_mul_of_nonneg_left hfac hnn
      linarith
    exact h1.trans (h2.trans hCM_body)
  have hγl_le_CM : P_hi.γ_ℓ ≤ bundleCostMult E (M₀ ^ 2) := by
    have hKt1 : (1 : ℝ) ≤ P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1 := by nlinarith
    have hfac : 1 ≤ (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
        max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) * ((E.L : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hKt1 hmaxLNR_ge1) (by linarith)
    have h1 : coreE_L E.L P_hi ≤
        coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) * ((E.L : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left hfac (by linarith : 0 ≤ coreE_L E.L P_hi)
      linarith
    exact (coreE_L_ge_gamma_l E.L P_hi).trans (h1.trans hCM_body)
  have hLNR_nn : 0 ≤ (E.L : ℝ) * bundleNRoot E.L M :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [bundleParams_nRoot_ge_one E.L M])
  have hPart1a : coreE_L E.L P_hi * (P_hi.K_t + 1) * ((E.L : ℝ) * bundleNRoot E.L M) ≤
      bundleCostMult E (M₀ ^ 2) := by
    have hKt1 : P_hi.K_t + 1 ≤ P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1 := by nlinarith
    have h1 : coreE_L E.L P_hi * (P_hi.K_t + 1) * ((E.L : ℝ) * bundleNRoot E.L M) ≤
        coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) := by
      have hA : coreE_L E.L P_hi * (P_hi.K_t + 1) ≤
          coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) :=
        mul_le_mul_of_nonneg_left hKt1 (by linarith)
      exact mul_le_mul hA hLNR_le hLNR_nn (by positivity)
    have h2 : coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
        max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) ≤
        coreE_L E.L P_hi * (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L (M₀ ^ 2)) * ((E.L : ℝ) + 1) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    exact h1.trans (h2.trans hCM_body)
  have hPart1b : coreE_L E.L P_hi * P_hi.K_s * ((E.L : ℝ) * bundleNRoot E.L M) ≤ (Γ : ℝ) := by
    have hE_LNR : coreE_L E.L P_hi * ((E.L : ℝ) * bundleNRoot E.L M) ≤ bundleCostMult E (M₀ ^ 2) := by
      have h1 : coreE_L E.L P_hi * ((E.L : ℝ) * bundleNRoot E.L M) ≤
          coreE_L E.L P_hi * (P_hi.K_t + 1) * ((E.L : ℝ) * bundleNRoot E.L M) := by
        have := mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by linarith : 0 ≤ coreE_L E.L P_hi) (by linarith : 1 ≤ P_hi.K_t + 1))
          hLNR_nn
        linarith
      exact h1.trans hPart1a
    have hmul : P_hi.K_s * (coreE_L E.L P_hi * ((E.L : ℝ) * bundleNRoot E.L M)) ≤
        bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2) :=
      mul_le_mul hKs_le_Rec hE_LNR (mul_nonneg (by linarith) hLNR_nn) (by linarith)
    linarith
  have hlogN_le : 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) ≤ 115 * (M : ℝ) + 4 := by
    have hval : (bundleNMax M : ℝ) + (M : ℝ) + 2 = 115 * (M : ℝ) + 4 := by
      unfold bundleNMax; push_cast; ring
    rw [hval]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 115 * (M : ℝ) + 4 by positivity)]
  have hLam_le : bundleLambda P_hi M ≤ 115 * (M : ℝ) + 4 := by
    unfold bundleLambda
    have hp_le1 : max P_hi.p_s P_hi.p_t ≤ 1 :=
      max_le (monoSparsifyParamsEnvelope_p_s_le params hp_s (M₀ ^ 2))
        (monoSparsifyParamsEnvelope_p_t_le params hp_t (M₀ ^ 2))
    have hbase_ge1 : (1 : ℝ) ≤ 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) :=
      by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)]
    calc (1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)) ^ max P_hi.p_s P_hi.p_t
        ≤ (1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)) ^ 1 := pow_le_pow_right₀ hbase_ge1 hp_le1
      _ = 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) := pow_one _
      _ ≤ 115 * (M : ℝ) + 4 := hlogN_le
  refine ⟨by linarith, hKt_piece.trans hCM_le_Γ, h2Ks_le_Rec.trans hRec_le_Γ,
    hγl_le_CM.trans hCM_le_Γ, hlogN_le, hLam_le⟩

/-! ## 3. Term 4 (`spanBatchChargeWith`) and Term 6 (`lazyMachInitCost`) -/

/-- Term 4 single-step bound (`b`-free) for `sparseCoreBundleRestartToolMachWith`:
the sum of `spanBatchChargeWith` over active buckets is at most
`1080 * spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M`. -/
theorem stepBundleTreeMach_dynMach_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ B_cap spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (hMsq : M ≤ M₀ ^ 2) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M (params M) (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (t r : ℕ) (ht : t ≤ τ) (hInit : IsValidLSFInitFor lsfInit C_lsst k r)
    (U : List Update) (ord_in ord' : ℕ → List End) :
    let E := Chain.Ordered.concreteEnv C_lsst params hp_s hp_t M₀ B_cap
    let L := E.L
    let Γ : ℕ := ⌈(bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2)⌉₊
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let tr := (Tm.runOrdAfterRestarts k M N D ord restarts t).trees r
    let info := stepBundleTree sparsify tr U ord_in ord'
    (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      spanBatchChargeWith tr.spanConst tr.spanParams L ((tr.initBunG (C, b)).n + tr.splitBound)
        (tr.initBunG (C, b)) (tr.dyn (C, b)).G (info.U_B (C, b))) ≤
      1080 * spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M := by
  classical
  intro E L Γ Tm tr info
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  set trb := (Tb.runOrdAfterRestarts k M N D ord restarts t).trees r
  set infob := stepBundleTree sparsify trb U ord_in ord'
  set P_hi := monoSparsifyParamsEnvelope params (M₀ ^ 2)
  have hL : 1 ≤ L := E.hL
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
    params spanConst k M N D ord restarts t).2.2.trees r
  have hStepNM := BundleNonMachEq.step sparsify hNM U ord_in ord'
  have hParams := (runOrdAfterRestartsMachWith_params lsfInit C_lsst L sparsify params spanConst
    k M N D ord restarts t r).2
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd r hInit t ht
  have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
    (Tb.runOrdAfterUpdate k M N D ord restarts t).1 (restarts t)).2.2.2.2.1 r
  have hcs_eq : trb.cs = ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).cs := hbf.cs
  have hact_eq : trb.activeComps =
      ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).activeComps := hbf.activeComps
  have hG0_cs : trb.cs.G₀ = D.G 0 := by
    rw [hcs_eq, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hact'_sub : infob.state.activeComps ⊆ components (D.G 0) := by
    intro C hCact
    change C ∈ trb.activeComps ∪ (touchedCompsBatch trb.cs U \ trb.activeComps) at hCact
    rcases Finset.mem_union.mp hCact with h1 | h2
    · exact hBun.2.2.2.2.2.2.2.2.2.1.2 (hact_eq ▸ h1)
    · rw [← hG0_cs]
      exact Finset.filter_subset _ _ (Finset.mem_sdiff.mp h2).1
  have hsb_eq : trb.splitBound = bundleSplitBudget k M := hbf.splitBound.trans hBun.2.2.1
  let s₀ := bundleLastRestart restarts r t
  obtain ⟨hs₀_le, hs₀_rest, hNoRest_le⟩ := bundleLastRestart_spec restarts r t
  have hNoRest : ∀ s, s₀ < s → s < t → r ∉ restarts s :=
    fun s h1 h2 => hNoRest_le s h1 (Nat.le_of_lt h2)
  have hEp_eq : epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r (t - s₀) = trb := by
    have hnor : r ∉ restarts t ∨ s₀ = t := by
      by_cases heq : s₀ = t
      · exact Or.inr heq
      · exact Or.inl (hNoRest_le t (by omega) le_rfl)
    exact (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r hs₀_le).2.1 hnor
  have hEnv := concreteEnv_gamma_r_bounds C_lsst params hp_s hp_t M₀ B_cap spanConst M hMsq
  have hΓ_ge1 : (1 : ℝ) ≤ (Γ : ℝ) := by
    have hRec_ge4 : (4 : ℝ) ≤ bundleRecBase E (M₀ ^ 2) :=
      (bundleRecEnv_ge_four E (M₀ ^ 2)).trans (le_max_left _ _)
    have hCM_ge1 : (1 : ℝ) ≤ bundleCostMult E (M₀ ^ 2) := le_max_left _ _
    have hγr_ge1 : (1 : ℝ) ≤ (bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2) := by
      change 1 ≤ bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2); nlinarith
    exact hγr_ge1.trans (Nat.le_ceil _)
  have hrate_bound : ∀ C ∈ infob.state.activeComps, ∀ b ∈ trb.activeBuckets C,
      (spanBatchChargeWith spanConst (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
        (trb.initBunG (C, b)) (trb.dyn (C, b)).G (infob.U_B (C, b)) : ℝ) ≤
        360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
          ((trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℝ) := by
    intro C hCact b _hb
    have hC : C ∈ components (D.G 0) := hact'_sub hCact
    have hDynSpec := epochBundleSeq_dyn_spec lsfInit C_lsst L hL (params M) sparsify k M N τ hk D ord
      restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t r hInit hs₀_le ht hs₀_rest hNoRest C hC b
    have hInitEq := epochBundleSeq_initBunG_eq lsfInit C_lsst L sparsify k M N τ hk D ord restarts
      hG₀ hV₀ hℓ₀ hD hOrd s₀ t r hInit hs₀_le ht hs₀_rest hNoRest (t - s₀) le_rfl C hC b
    rw [hEp_eq] at hInitEq
    set Hb := ((epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r 0).bun (C, b)).graph
    have hNormEq : GraphEq (trb.initBunG (C, b)) Hb := hInitEq ▸ normGraph_graphEq Hb
    have hn_le : (trb.initBunG (C, b)).n + trb.splitBound ≤ bundleNMax M := by
      have hn1 : (trb.initBunG (C, b)).n = Hb.n := graphEq_n hNormEq
      have hn2 : Hb.n ≤ 2 * Hb.m := hDynSpec.2.2.1
      have hm2 : Hb.m ≤ M := hDynSpec.2.1.trans hM
      have hsb_le : bundleSplitBudget k M ≤ 2 * (56 * M + 1) := by
        unfold bundleSplitBudget
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M :=
          Nat.ceil_le.mpr ((div_le_self (by positivity) hk1).trans (by norm_cast))
        omega
      rw [hn1, hsb_eq]
      unfold bundleNMax
      omega
    have hm_le : (trb.initBunG (C, b)).m ≤ M := (graphEq_m hNormEq).trans_le (hDynSpec.2.1.trans hM)
    have hd_le : (trb.initBunG (C, b)).maxDeg ≤ k :=
      (graphEq_maxDeg hNormEq).trans_le hDynSpec.2.2.2.1
    have h2mul := spanBatchChargeWith_le_two_mul hConst (params M) hL
      ((trb.initBunG (C, b)).n + trb.splitBound) (trb.initBunG (C, b)) (trb.dyn (C, b)).G
      (infob.U_B (C, b))
    have hrate := spanBatchRate_le (le_monoSparsifyParamsEnvelope params hMsq) (L := L)
      hn_le hm_le hd_le
    have hrate_sim : spanBatchRate (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
        (trb.initBunG (C, b)) ≤
        180 * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) := by
      have h1 : 90 * (L : ℝ) * bundleNRoot L M * (P_hi.K_t + P_hi.K_s + 1) * coreE_L L P_hi ≤
          180 * (Γ : ℝ) := by
        have hre : 90 * (L : ℝ) * bundleNRoot L M * (P_hi.K_t + P_hi.K_s + 1) * coreE_L L P_hi =
            90 * (coreE_L L P_hi * (P_hi.K_t + P_hi.K_s + 1) * ((L : ℝ) * bundleNRoot L M)) := by ring
        rw [hre]; linarith [hEnv.1]
      have h2 : 90 * (L : ℝ) * bundleNRoot L M * (P_hi.K_t + P_hi.K_s + 1) *
            coreE_L L P_hi * ((k : ℝ) + 1) * bundleLambda P_hi M ≤
          180 * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) := by
        have hA : 90 * (L : ℝ) * bundleNRoot L M * (P_hi.K_t + P_hi.K_s + 1) *
              coreE_L L P_hi * ((k : ℝ) + 1) ≤ 180 * (Γ : ℝ) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have hLam_nn : 0 ≤ bundleLambda P_hi M := by
          unfold bundleLambda
          exact pow_nonneg (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)]) _
        exact mul_le_mul hA hEnv.2.2.2.2.2 hLam_nn (by positivity)
      exact hrate.trans h2
    calc (spanBatchChargeWith spanConst (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
            (trb.initBunG (C, b)) (trb.dyn (C, b)).G (infob.U_B (C, b)) : ℝ)
        ≤ 2 * (spanConst : ℝ) *
            spanBatchRate (params M) L ((trb.initBunG (C, b)).n + trb.splitBound) (trb.initBunG (C, b)) *
            ((trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℝ) := h2mul
      _ ≤ 2 * (spanConst : ℝ) * (180 * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4)) *
            ((trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrate_sim (by positivity))
            (Nat.cast_nonneg _)
      _ = 360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
            ((trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℝ) := by ring
  have hsum_eq :
      (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        spanBatchChargeWith tr.spanConst tr.spanParams L ((tr.initBunG (C, b)).n + tr.splitBound)
          (tr.initBunG (C, b)) (tr.dyn (C, b)).G (info.U_B (C, b))) =
      (infob.state.activeComps.sum fun C => (trb.activeBuckets C).sum fun b =>
        spanBatchChargeWith spanConst (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
          (trb.initBunG (C, b)) (trb.dyn (C, b)).G (infob.U_B (C, b))) := by
    rw [hStepNM.1.activeComps, hNM.activeBuckets, hParams.2.2.2.1, hParams.2.2.1,
      hNM.initBunG, hNM.splitBound, hNM.dyn, hStepNM.2.1]
  rw [hsum_eq]
  have hbunSum := stepBundleTree_bunEnc_sum_le lsfInit C_lsst L hL (params M) sparsify k M N τ hk
    D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd t r ht hInit U ord_in ord'
  have hR : ((infob.state.activeComps.sum fun C => (trb.activeBuckets C).sum fun b =>
        spanBatchChargeWith spanConst (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
          (trb.initBunG (C, b)) (trb.dyn (C, b)).G (infob.U_B (C, b)) : ℕ) : ℝ) ≤
      ((1080 * spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M : ℕ) : ℝ) := by
    have hbunR : ((infob.state.activeComps.sum fun C => (trb.activeBuckets C).sum fun b =>
          (trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℕ) : ℝ) ≤
        3 * ((k : ℝ) + 1) * (M : ℝ) := by
      have hcast : ((3 * (k + 1) * M : ℕ) : ℝ) = 3 * ((k : ℝ) + 1) * (M : ℝ) := by push_cast; ring
      rw [← hcast]
      exact_mod_cast hbunSum
    have h1 : ((infob.state.activeComps.sum fun C => (trb.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
            (trb.initBunG (C, b)) (trb.dyn (C, b)).G (infob.U_B (C, b)) : ℕ) : ℝ) ≤
        360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
          (3 * ((k : ℝ) + 1) * (M : ℝ)) := by
      push_cast
      calc ∑ C ∈ infob.state.activeComps, ∑ b ∈ trb.activeBuckets C,
              (spanBatchChargeWith spanConst (params M) L ((trb.initBunG (C, b)).n + trb.splitBound)
                (trb.initBunG (C, b)) (trb.dyn (C, b)).G (infob.U_B (C, b)) : ℝ)
          ≤ ∑ C ∈ infob.state.activeComps, ∑ b ∈ trb.activeBuckets C,
              (360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
                ((trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℝ)) :=
            Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => hrate_bound C hC b hb
        _ = 360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
              (∑ C ∈ infob.state.activeComps, ∑ b ∈ trb.activeBuckets C,
                ((trb.dyn (C, b)).G.batchEnc (infob.U_B (C, b)) : ℝ)) := by
            simp only [← Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [Nat.cast_sum] using hbunR) (by positivity)
    have hΓ_sq : (Γ : ℝ) ≤ (Γ : ℝ) ^ 2 := by nlinarith
    have h2 : 360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
          (3 * ((k : ℝ) + 1) * (M : ℝ)) ≤
        1080 * (spanConst : ℝ) * (Γ : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * (115 * (M : ℝ) + 4) * (M : ℝ) := by
      have hre1 : 360 * (spanConst : ℝ) * (Γ : ℝ) * ((k : ℝ) + 1) * (115 * (M : ℝ) + 4) *
            (3 * ((k : ℝ) + 1) * (M : ℝ)) =
          (Γ : ℝ) * (1080 * (spanConst : ℝ) * ((k : ℝ) + 1) ^ 2 * (115 * (M : ℝ) + 4) * (M : ℝ)) := by ring
      have hre2 : 1080 * (spanConst : ℝ) * (Γ : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 *
            (115 * (M : ℝ) + 4) * (M : ℝ) =
          (Γ : ℝ) ^ 2 * (1080 * (spanConst : ℝ) * ((k : ℝ) + 1) ^ 2 * (115 * (M : ℝ) + 4) * (M : ℝ)) := by ring
      rw [hre1, hre2]
      exact mul_le_mul_of_nonneg_right hΓ_sq (by positivity)
    calc _ ≤ _ := h1.trans h2
      _ = ((1080 * spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M : ℕ) : ℝ) := by
          push_cast; ring
  exact_mod_cast hR

/-- Term 6 single-step bound (`b`-free) for `sparseCoreBundleRestartToolMachWith`:
the lazy-initialization sum `info.newlyActive.sum tr.lazyMachInitCost` is at most
`spanConst * (4 * Γ * (115 * M + 4) ^ 2 + (E.L + 6) * (115 * M + 4)) * M`. -/
theorem stepBundleTreeMach_lazyMach_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ B_cap spanConst : ℕ)
    (k M N τ : ℕ) (hk : 1 ≤ k) (hMsq : M ≤ M₀ ^ 2) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (t r : ℕ) (ht : t ≤ τ) (hInit : IsValidLSFInitFor lsfInit C_lsst k r)
    (U : List Update) (ord_in ord' : ℕ → List End) :
    let E := Chain.Ordered.concreteEnv C_lsst params hp_s hp_t M₀ B_cap
    let L := E.L
    let Γ : ℕ := ⌈(bundleCoreParamsMachWith E spanConst).γ_r (M₀ ^ 2)⌉₊
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let tr := (Tm.runOrdAfterRestarts k M N D ord restarts t).trees r
    let info := stepBundleTree sparsify tr U ord_in ord'
    info.newlyActive.sum tr.lazyMachInitCost ≤
      spanConst * (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M := by
  classical
  intro E L Γ Tm tr info
  set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) r
  set st₀m := initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0) (D.ℓ 0) (ord 0) r
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  set trb := (Tb.runOrdAfterRestarts k M N D ord restarts t).trees r
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
    params spanConst k M N D ord restarts t).2.2.trees r
  have hParams := (runOrdAfterRestartsMachWith_params lsfInit C_lsst L sparsify params spanConst
    k M N D ord restarts t r).2
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd r hInit t ht
  have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
    (Tb.runOrdAfterUpdate k M N D ord restarts t).1 (restarts t)).2.2.2.2.1 r
  have hcs_eq : trb.cs = ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).cs := hbf.cs
  have hG0_cs : tr.cs.G₀ = D.G 0 := by
    rw [hNM.cs, hcs_eq, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hnew_sub : info.newlyActive ⊆ components (D.G 0) := by
    intro C hC
    change C ∈ touchedCompsBatch tr.cs U \ tr.activeComps at hC
    rw [← hG0_cs]
    exact Finset.filter_subset _ _ (Finset.mem_sdiff.mp hC).1
  have hlazy_eq : tr.lazyMachInitCost = st₀m.lazyMachInitCost := hParams.2.2.2.2
  have hsum_sub : info.newlyActive.sum tr.lazyMachInitCost ≤
      spanConst * ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
        spanInitBound (params M) L (bundleSplitBudget k M) (normGraph (st₀.bun (C, b)).graph)) := by
    rw [hlazy_eq]
    have h1 := Finset.sum_le_sum_of_subset (f := st₀m.lazyMachInitCost) hnew_sub
    refine h1.trans (le_of_eq ?_)
    have hact_eq : st₀m.activeBuckets = st₀.activeBuckets := rfl
    have hbun_eq : st₀m.bun = st₀.bun := rfl
    change ((components (D.G 0)).sum fun C => (st₀m.activeBuckets C).sum fun b =>
        spanConst * spanInitBound (params M) L (bundleSplitBudget k M) (normGraph (st₀m.bun (C, b)).graph)) = _
    rw [hact_eq, hbun_eq]
    simp only [Finset.mul_sum]
  have hBuckets := initBundleTreeWith_buckets_sum_le lsfInit L sparsify (M := M) (N := N) (G₀ := D.G 0) hk (D.ℓ 0) (ord 0) r
  have hcard : (components (D.G 0)).sum (fun C => (st₀.activeBuckets C).card) ≤ M :=
    hBuckets.1.trans hM
  have hm_sum : (components (D.G 0)).sum (fun C => (st₀.activeBuckets C).sum fun b =>
      (normGraph (st₀.bun (C, b)).graph).m) ≤ M := by
    have heq : ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
        (normGraph (st₀.bun (C, b)).graph).m) =
        ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          ((st₀.bun (C, b)).graph).m) :=
      Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun b _ => graphEq_m (normGraph_graphEq _)
    rw [heq]; exact hBuckets.2.1.trans hM
  have hn_le : ∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
      (normGraph (st₀.bun (C, b)).graph).n ≤ 2 * (normGraph (st₀.bun (C, b)).graph).m := by
    intro C _ b _
    rw [graphEq_n (normGraph_graphEq _), graphEq_m (normGraph_graphEq _)]
    exact hBuckets.2.2.1 C b
  have hsb_le : bundleSplitBudget k M ≤ 2 * (56 * M + 1) := by
    unfold bundleSplitBudget
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M :=
      Nat.ceil_le.mpr ((div_le_self (by positivity) hk1).trans (by norm_cast))
    omega
  set P_hi := monoSparsifyParamsEnvelope params (M₀ ^ 2)
  have hspan := spanInitBound_buckets_sum_le (le_monoSparsifyParamsEnvelope params hMsq)
    hsb_le (components (D.G 0)) st₀.activeBuckets
    (fun C b => normGraph (st₀.bun (C, b)).graph) (L := L) hcard hm_sum hn_le
  have hEnv := concreteEnv_gamma_r_bounds C_lsst params hp_s hp_t M₀ B_cap spanConst M hMsq
  have hinner_nat : ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
        spanInitBound (params M) L (bundleSplitBudget k M) (normGraph (st₀.bun (C, b)).graph)) ≤
      (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M := by
    have hR : (((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          spanInitBound (params M) L (bundleSplitBudget k M) (normGraph (st₀.bun (C, b)).graph) : ℕ) : ℝ) ≤
        (((4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M : ℕ) : ℝ) := by
      set logN := 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)
      set Λ := bundleLambda P_hi M
      have hlogN_nn : 0 ≤ logN := by
        dsimp only [logN]
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)]
      have hΛ_nn : 0 ≤ Λ := by dsimp only [Λ, bundleLambda]; exact pow_nonneg hlogN_nn _
      have hY_ge1 : (1 : ℝ) ≤ 115 * (M : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) M]
      have hY_le_sq : 115 * (M : ℝ) + 4 ≤ (115 * (M : ℝ) + 4) ^ 2 := by nlinarith
      have h1_le_sq : (1 : ℝ) ≤ (115 * (M : ℝ) + 4) ^ 2 := hY_ge1.trans hY_le_sq
      have hΛlog_le : Λ * logN ≤ (115 * (M : ℝ) + 4) ^ 2 := by
        have := mul_le_mul hEnv.2.2.2.2.2 hEnv.2.2.2.2.1 hlogN_nn (by positivity)
        linarith
      have hΛ_le_sq : Λ ≤ (115 * (M : ℝ) + 4) ^ 2 := hEnv.2.2.2.2.2.trans hY_le_sq
      have ht1 : P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) ≤ (Γ : ℝ) * (115 * (M : ℝ) + 4) ^ 2 :=
        mul_le_mul hEnv.2.1 hΛlog_le (mul_nonneg hΛ_nn hlogN_nn) (Nat.cast_nonneg _)
      have ht2 : 2 * P_hi.K_s * P_hi.γ_ℓ * Λ ≤ (Γ : ℝ) * (115 * (M : ℝ) + 4) ^ 2 :=
        mul_le_mul hEnv.2.2.1 hΛ_le_sq hΛ_nn (Nat.cast_nonneg _)
      have ht3 : P_hi.γ_ℓ ≤ (Γ : ℝ) * (115 * (M : ℝ) + 4) ^ 2 := by
        have := le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) Γ) h1_le_sq
        linarith [hEnv.2.2.2.1]
      have ht4 : 5 + ((L : ℝ) + 1) * logN ≤ ((L : ℝ) + 6) * (115 * (M : ℝ) + 4) := by
        have hLlog := mul_le_mul_of_nonneg_left hEnv.2.2.2.2.1 (show 0 ≤ (L : ℝ) + 1 by positivity)
        linarith
      have hcoeff : P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) +
            2 * P_hi.K_s * P_hi.γ_ℓ * Λ + 5 + P_hi.γ_ℓ + ((L : ℝ) + 1) * logN ≤
          4 * (Γ : ℝ) * (115 * (M : ℝ) + 4) ^ 2 + ((L : ℝ) + 6) * (115 * (M : ℝ) + 4) := by
        have hΓ_sq_nn : 0 ≤ (Γ : ℝ) * (115 * (M : ℝ) + 4) ^ 2 := by positivity
        linarith
      have hmul := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) M)
      calc _ ≤ _ := hspan.trans hmul
        _ = (((4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M : ℕ) : ℝ) := by
            push_cast; ring
    exact_mod_cast hR
  calc info.newlyActive.sum tr.lazyMachInitCost
      ≤ spanConst * ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          spanInitBound (params M) L (bundleSplitBudget k M) (normGraph (st₀.bun (C, b)).graph)) := hsum_sub
    _ ≤ spanConst * ((4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M) :=
        Nat.mul_le_mul_left _ hinner_nat
    _ = spanConst * (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M := by ring

end MinCostFlow.Final.DryRun
