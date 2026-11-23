module

public import MinCostFlow.Chain.BundleRestartMach
public import MinCostFlow.Chain.BundleRestartSCur
public import MinCostFlow.Final.AssemblyDryRunSCToolStepAux
import MinCostFlow.SparseCore.BundleOutBatchSpec
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.DynSpanner.ComplexitySum
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic

/-!
# Single-step bound on the output batch encoding `S_cur.batchEnc U_S`

Proves the Term 3 single-step bound of `stepBundleTree_machCost` (`branchStepCharge`) on any
valid input batch `U` of length `≤ b` (with no input rotation requirement on `U`):
```
tr.S_cur.batchEnc info.U_S ≤ (5 + 24 * bundleLogFactor M N) * M + (1 + 112 * bundleLogFactor M N) * b
```
for every reached branch `tr` of `sparseCoreBundleRestartToolWith` or
`sparseCoreBundleRestartToolMachWith` whose current graph satisfies `tr.cs.G.m ≤ M`.

Uses `batchEnc_splits_le_real` and `canonCoreBatch_props_of_valid` from
`AssemblyDryRunSCToolStepAux.lean`, together with bucket-spanner edge containment
(`stepBundleTree_dynUnionE_sub_G0`, via `epochBundleSeq_dyn_spec` and
`DynSpanner.Transition.runInv_all`).
-/

public section

namespace MinCostFlow.Final.DryRun

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.Bundle

/-! ## 1. Single-step bucket-spanner edge containment (`dynUnionE' ⊆ G₀.E`) -/

private lemma runBatchState_append_prefix {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) (U : List Update) :
    ∀ k ≤ Us.length,
      DynSpanner.runBatchState (L := L) G₀ q sparsify (Us ++ [U]) k =
        DynSpanner.runBatchState (L := L) G₀ q sparsify Us k
  | 0, _ => rfl
  | k + 1, hk => by
    have hlt : k < Us.length := Nat.lt_of_succ_le hk
    have hget : (Us ++ [U])[k]? = Us[k]? := List.getElem?_append_left hlt
    simp only [DynSpanner.runBatchState, hget,
      runBatchState_append_prefix G₀ q sparsify Us U k (Nat.le_of_lt hlt)]

private lemma runBatchState_append_last {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) (U : List Update) :
    DynSpanner.runBatchState (L := L) G₀ q sparsify (Us ++ [U]) (Us.length + 1) =
      (DynSpanner.update (DynSpanner.runBatchState (L := L) G₀ q sparsify Us Us.length)
        U sparsify).state := by
  have hget : (Us ++ [U])[Us.length]? = some U := by
    rw [List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
  simp only [DynSpanner.runBatchState, hget,
    runBatchState_append_prefix G₀ q sparsify Us U Us.length le_rfl]

private lemma batchIsValid_append_us {G : MGraph} {U₁ U₂ : List Update}
    (h1 : G.BatchIsValid U₁) (h2 : (G.applyBatch U₁).BatchIsValid U₂) :
    G.BatchIsValid (U₁ ++ U₂) := by
  induction U₁ generalizing G with
  | nil => simpa [MGraph.applyBatch] using h2
  | cons u rest ih =>
    exact ⟨h1.1, ih h1.2 h2⟩

/-- For every component `C ∈ active'` and active bucket `b` in a step from a reached branch of
`sparseCoreBundleRestartToolWith`, the updated spanner edges `(spOut (C, b)).state.H.E` stay
inside `(D.G 0).E`. -/
theorem stepBundleTree_dynUnionE_sub_G0
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
    ∀ C ∈ info.state.activeComps, ∀ b ∈ tr.activeBuckets C,
      (info.stepOut (C, b)).state.H.E ⊆ (D.G 0).E := by
  classical
  intro Tb tr info C hCact b _hb
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd r hInit t ht
  have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
    (Tb.runOrdAfterUpdate k M N D ord restarts t).1 (restarts t)).2.2.2.2.1 r
  have hcs_eq : tr.cs = ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).cs := hbf.cs
  have hact_eq : tr.activeComps =
      ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).activeComps := hbf.activeComps
  have hG0_cs : tr.cs.G₀ = D.G 0 := by
    rw [hcs_eq, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hC : C ∈ components (D.G 0) := by
    change C ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps) at hCact
    rcases Finset.mem_union.mp hCact with h1 | h2
    · exact hBun.2.2.2.2.2.2.2.2.2.1.2 (hact_eq ▸ h1)
    · have hmem := (Finset.mem_sdiff.mp h2).1
      rw [← hG0_cs]
      exact Finset.filter_subset _ _ hmem
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
  have hDynSpec := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify k M N τ hk D ord restarts
    hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t r hInit hs₀_le ht hs₀_rest hNoRest C hC b
  set st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t r
  set Hb := ((st 0).bun (C, b)).graph
  set Us_ep : List (List Update) :=
    (List.range (t - s₀)).map fun δ =>
      (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))).U_B (C, b)
  set splitB := bundleSplitBudget k M
  set q := phaseBase (Hb.n + splitB) L
  have hHb_val : Hb.IsValid := hDynSpec.1
  have hHb_m : Hb.m ≤ (D.G 0).m := hDynSpec.2.1
  have hHb_E_sub : Hb.E ⊆ (D.G 0).E := by
    have hB0_eq : st 0 = (Tb.runOrdAfterRestarts k M N D ord restarts s₀).trees r := by
      have hcond : ¬ (s₀ + 0 = t ∧ s₀ < t) := by omega
      dsimp only [st, epochBundleSeq, Tb]
      rw [ite_eq_right hcond, Nat.add_zero]
    have hBun0 := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
      k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd r hInit s₀ (hs₀_le.trans ht)
    have hE0 := ((hBun0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1
    have hE0p := ((hBun0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1
    change ((st 0).bun (C, b)).edges ⊆ (D.G 0).E
    rw [hB0_eq, hE0p, hE0]
    refine Finset.sdiff_subset.trans ?_
    refine (initBundleFor_edges_sub _ _ _ _).trans ?_
    exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have hδ_end := hDynSpec.2.2.2.2.2.2.2.2.2.1 (t - s₀) le_rfl
  have htr_dyn : tr.dyn (C, b) =
      DynSpanner.runBatchState (L := L) (normGraph Hb) q (sparsify M) Us_ep (t - s₀) := by
    rw [← hEp_eq]; exact hδ_end.1
  have htr_Geq : GraphEq (tr.dyn (C, b)).G (tr.bun (C, b)).graph := by
    rw [← hEp_eq]; exact hδ_end.2.1
  have htr_Hsub : (tr.dyn (C, b)).G.IsSubgraph (tr.dyn (C, b)).H := by
    rw [← hEp_eq]; exact hδ_end.2.2.2.1
  have htr_m0 : tr.m₀ = M := hbf.m₀.trans hBun.2.1
  have hspOut_eq : info.stepOut (C, b) =
      DynSpanner.update (tr.dyn (C, b)) (info.U_B (C, b)) (sparsify M) := by
    change DynSpanner.update (tr.dyn (C, b)) (info.U_B (C, b)) (sparsify tr.m₀) = _
    rw [htr_m0]
  rw [hspOut_eq]
  by_cases hReady : BundleStepReady tr.cs (tr.bun (C, b)) tr.k ord_in ord' U
  · have hSpecB := bundleCompStep_spec hReady
    have hUB_val_bun : (tr.bun (C, b)).graph.BatchIsValid (info.U_B (C, b)) := hSpecB.2.1
    have hUB_ds : ∀ op ∈ info.U_B (C, b), isDelOrSplit op := hSpecB.2.2.2.1
    have hNormEq : GraphEq (normGraph Hb) Hb := normGraph_graphEq Hb
    have hNormVal : (normGraph Hb).IsValid := graphEq_isValid (graphEq_symm hNormEq) hHb_val
    have hNormM : (normGraph Hb).m ≤ M := (graphEq_m hNormEq).trans_le (hHb_m.trans hM)
    have hUs_val : (normGraph Hb).BatchIsValid Us_ep.flatten :=
      (graphEq_batchIsValid hNormEq _).mpr hDynSpec.2.2.2.2.2.1
    have hUs_ds : ∀ op ∈ Us_ep.flatten, isDelOrSplit op := hDynSpec.2.2.2.2.2.2.1
    have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 2) (two_le_phaseBase _ _)
    have hSpecPrev := DynSpanner.batchTrace_spec hNormVal hL hq1 hNormM hSp hUs_val hUs_ds
    have hUs_len : Us_ep.length = t - s₀ := by simp [Us_ep]
    have hPrevG : (tr.dyn (C, b)).G = (normGraph Hb).applyBatch Us_ep.flatten := by
      rw [htr_dyn]
      have h1 := (hSpecPrev.1 (t - s₀) (by omega)).2.1
      have htake : Us_ep.flatten.take (batchPrefixLen Us_ep (t - s₀)) = Us_ep.flatten := by
        simp [batchPrefixLen, ← hUs_len]
      rw [htake] at h1
      exact h1
    have hUB_val_dyn : ((normGraph Hb).applyBatch Us_ep.flatten).BatchIsValid (info.U_B (C, b)) := by
      rw [← hPrevG]
      exact (graphEq_batchIsValid htr_Geq _).mpr hUB_val_bun
    let Us' : List (List Update) := Us_ep ++ [info.U_B (C, b)]
    have hUs'_flat : Us'.flatten = Us_ep.flatten ++ info.U_B (C, b) := by simp [Us']
    have hUs'_val : (normGraph Hb).BatchIsValid Us'.flatten := by
      rw [hUs'_flat]
      exact batchIsValid_append_us hUs_val hUB_val_dyn
    have hUs'_ds : ∀ op ∈ Us'.flatten, isDelOrSplit op := by
      rw [hUs'_flat]
      intro op hop
      rcases List.mem_append.mp hop with h1 | h2
      · exact hUs_ds op h1
      · exact hUB_ds op h2
    have hSpecNew := DynSpanner.batchTrace_spec hNormVal hL hq1 hNormM hSp hUs'_val hUs'_ds
    have hInvNew := DynSpanner.runInv_all hNormVal hL hq1 hNormM hSp hUs'_val hUs'_ds
      Us'.flatten.length le_rfl
    have hStateEq : (DynSpanner.update (tr.dyn (C, b)) (info.U_B (C, b)) (sparsify M)).state =
        DynSpanner.runState (L := L) (normGraph Hb) q (sparsify M) Us'.flatten Us'.flatten.length := by
      rw [htr_dyn, ← hUs_len, ← runBatchState_append_last (normGraph Hb) q (sparsify M) Us_ep (info.U_B (C, b))]
      have hLen' : Us_ep.length + 1 = Us'.length := by simp [Us']
      have hbt := (hSpecNew.1 (Us_ep.length + 1) (by omega)).1
      have hbpl : batchPrefixLen Us' (Us_ep.length + 1) = Us'.flatten.length := by
        simp [batchPrefixLen, hLen']
      rw [hbpl] at hbt
      exact hbt
    rw [hStateEq]
    have hHsub := hInvNew.1.H_sub.2.1
    rw [List.take_length] at hHsub
    refine hHsub.trans ((applyBatch_delOrSplit_E_sub hUs'_ds).trans ?_)
    rw [hNormEq.2.1]
    exact hHb_E_sub
  · have hUB_nil : info.U_B (C, b) = [] := by
      change (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord_in ord' U).1 = []
      rw [bundleCompStep_of_not hReady]
    rw [hUB_nil, update_nil]
    have hE_eq : (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges := htr_Geq.2.1
    have hBun_sub : (tr.bun (C, b)).edges ⊆ (D.G 0).E := by
      have h1 := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1
      have h2 := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1
      rw [h2, h1]
      exact Finset.sdiff_subset.trans ((initBundleFor_edges_sub _ _ _ _).trans
        ((Finset.filter_subset _ _).trans Finset.sdiff_subset))
    exact htr_Hsub.2.1.trans (hE_eq ▸ hBun_sub)

/-! ## 2. Term 3 single-step bound (`S_cur.batchEnc U_S`) -/

/-- Full Term 3 single-step bound for `sparseCoreBundleRestartToolWith`: on any valid batch `U`
of length `≤ b` on a reached branch `tr` with `tr.cs.G.m ≤ M`, the output batch encoding satisfies
`tr.S_cur.batchEnc info.U_S ≤ (5 + 24 * bundleLogFactor M N) * M + (1 + 112 * bundleLogFactor M N) * b`. -/
theorem stepBundleTree_US_batchEnc_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (t r : ℕ) (ht : t ≤ τ) (hInit : IsValidLSFInitFor lsfInit C_lsst k r)
    {U : List Update} {b : ℕ} (ord_in ord' : ℕ → List End)
    (hBU : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
      k M N D ord restarts t |>.trees r).cs.G.BatchIsValid U)
    (hGm : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
      k M N D ord restarts t |>.trees r).cs.G.m ≤ M)
    (hb : U.length ≤ b) :
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let tr := (Tb.runOrdAfterRestarts k M N D ord restarts t).trees r
    let info := stepBundleTree sparsify tr U ord_in ord'
    tr.S_cur.batchEnc info.U_S ≤
      (5 + 24 * bundleLogFactor M N) * M + (1 + 112 * bundleLogFactor M N) * b := by
  classical
  intro Tb tr info
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd r hInit t ht
  have hScur := (runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd r hInit t ht).2
  have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
    (Tb.runOrdAfterUpdate k M N D ord restarts t).1 (restarts t)).2.2.2.2.1 r
  have hcs_eq : tr.cs = ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).cs := hbf.cs
  have hact_eq : tr.activeComps =
      ((Tb.runOrdAfterUpdate k M N D ord restarts t).1.trees r).activeComps := hbf.activeComps
  have hI : CompLSFInv C_lsst (D.ℓ 0) tr.cs := by
    rw [hcs_eq]; exact hBun.2.2.2.2.2.2.2.1
  have hG0_cs : tr.cs.G₀ = D.G 0 := by
    rw [hcs_eq, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]
    rfl
  set cs' := compLSFBatch tr.cs U
  set active' := info.state.activeComps
  set dynUnionE' := active'.biUnion fun C =>
    (tr.activeBuckets C).biUnion fun bkt => (info.stepOut (C, bkt)).state.H.E
  set bunE' := active'.biUnion fun C =>
    (tr.activeBuckets C).biUnion fun bkt => (info.state.bun (C, bkt)).edges
  set extraComps' := active'.biUnion fun C =>
    ((cs'.compSt C).G.E \ (cs'.compSt C).RF.F.E) \ bunE'
  set targetE' := dynUnionE' ∪ extraComps' ∪ cs'.crossEdges
  set D_tot := info.D_total
  set UC := coreBatchOf tr.cs ord_in ord' U
  set keepSet := ((tr.S_cur.E ∩ targetE') \ batchDeletes U) \ D_tot
  set delList := ((tr.S_cur.E \ keepSet).sort (· ≤ ·)).map Update.delete
  set splitList := restrictSplits keepSet UC
  set insList := ((targetE' \ keepSet).sort (· ≤ ·)).map fun e =>
    Update.insert e (cs'.RF.root (cs'.G.tail e)) (cs'.RF.root (cs'.G.head e))
  have hUS_eq : info.U_S = delList ++ splitList ++ insList := rfl
  set S₁ := tr.S_cur.applyBatch delList
  have hEnc_split : tr.S_cur.batchEnc info.U_S =
      delList.length + S₁.batchEnc splitList + insList.length := by
    rw [hUS_eq, batchEnc_append, batchEnc_append, DynSpanner.applyBatch_append,
      batchEnc_map_delete, batchEnc_map_insert]
    simp only [delList, insList, List.length_map]
    rfl
  have hScur_m_le : tr.S_cur.m ≤ M := by
    have hsub : tr.S_cur.E ⊆ tr.cs.G.E := hScur.2.2.2.2.1.trans Finset.sdiff_subset
    exact (Finset.card_le_card hsub).trans hGm
  have hDel_le : delList.length ≤ M := by
    have h1 : delList.length = (tr.S_cur.E \ keepSet).card := by simp [delList]
    rw [h1]
    exact (Finset.card_le_card Finset.sdiff_subset).trans hScur_m_le
  have hDyn_sub_G0 : dynUnionE' ⊆ (D.G 0).E := by
    intro e he
    simp only [dynUnionE', Finset.mem_biUnion] at he
    obtain ⟨C, hC, bkt, hbkt, heH⟩ := he
    exact stepBundleTree_dynUnionE_sub_G0 lsfInit C_lsst L hL P_b sparsify k M N τ hk D ord
      restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd t r ht hInit U ord_in ord' C hC bkt hbkt heH
  have hStepProps := compLSFBatch_step_props U hI hBU
  have hI' : CompLSFInv C_lsst (D.ℓ 0) cs' := hStepProps.1
  have hcs'_G : cs'.G = tr.cs.G.applyBatch U := hStepProps.2.1
  have hExtraCross_sub : extraComps' ∪ cs'.crossEdges ⊆ cs'.G.E := by
    intro e he
    rcases Finset.mem_union.mp he with hEx | hCr
    · simp only [extraComps', Finset.mem_biUnion, Finset.mem_sdiff] at hEx
      obtain ⟨C, hCact, ⟨heC, _⟩, _⟩ := hEx
      have hC : C ∈ components cs'.G₀ := by
        have hG0' : cs'.G₀ = D.G 0 := (compLSFBatch_G₀ tr.cs U).trans hG0_cs
        rw [hG0']
        change C ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps) at hCact
        rcases Finset.mem_union.mp hCact with h1 | h2
        · exact hBun.2.2.2.2.2.2.2.2.2.1.2 (hact_eq ▸ h1)
        · rw [← hG0_cs]
          exact Finset.filter_subset _ _ (Finset.mem_sdiff.mp h2).1
      exact hI'.hCE_sub C hC heC
    · exact hI'.hIns_sub (hI'.hCross_sub hCr)
  have hIns_le : insList.length ≤ 2 * M + b := by
    have h1 : insList.length = (targetE' \ keepSet).card := by simp [insList]
    have h2 : (targetE' \ keepSet).card ≤ targetE'.card := Finset.card_le_card Finset.sdiff_subset
    have h3 : targetE'.card ≤ dynUnionE'.card + (extraComps' ∪ cs'.crossEdges).card := by
      have hunion : targetE' = dynUnionE' ∪ (extraComps' ∪ cs'.crossEdges) := by
        simp [targetE', Finset.union_assoc]
      rw [hunion]
      exact Finset.card_union_le _ _
    have h4 : dynUnionE'.card ≤ M := (Finset.card_le_card hDyn_sub_G0).trans hM
    have h5 : (extraComps' ∪ cs'.crossEdges).card ≤ M + b := by
      have hsub := Finset.card_le_card hExtraCross_sub
      have hgm : cs'.G.m ≤ tr.cs.G.m + U.length := by
        rw [hcs'_G]; exact m_applyBatch_le_add_len tr.cs.G U
      have hGm' : tr.cs.G.m ≤ M := hGm
      change (extraComps' ∪ cs'.crossEdges).card ≤ cs'.G.m at hsub
      omega
    omega
  obtain ⟨hUC_val, hUC_splits, hUC_delSub⟩ := canonCoreBatch_props_of_valid hI hBU
  have hS1_props := applyBatch_map_delete_props hScur.1 ((tr.S_cur.E \ keepSet).sort (· ≤ ·))
  have hS1_E : S₁.E = keepSet := by
    have htoF : ((tr.S_cur.E \ keepSet).sort (· ≤ ·)).toFinset = tr.S_cur.E \ keepSet := by
      ext e; simp
    have hkeep_sub : keepSet ⊆ tr.S_cur.E :=
      Finset.sdiff_subset.trans (Finset.sdiff_subset.trans Finset.inter_subset_left)
    rw [hS1_props.2.2.1, htoF, Finset.sdiff_sdiff_eq_self hkeep_sub]
  have hS1_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph S₁ :=
    ⟨hS1_props.2.2.2.1.trans hScur.2.2.2.1,
     hS1_props.2.2.2.2.1.trans hScur.2.2.2.2.1,
     fun e he =>
       let h1 := hS1_props.2.2.2.2.2 e he
       let h2 := hScur.2.2.2.2.2 e (hS1_props.2.2.2.2.1 he)
       ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩⟩
  have hS1_V : S₁.V = (coreGraph tr.cs.G tr.cs.lsf).V := by
    rw [hS1_props.2.1, hScur.2.1]; rfl
  have hKeep_disj : Disjoint keepSet (batchDeletes UC) := by
    rw [Finset.disjoint_left]
    intro e heK heD
    have heDU : e ∈ batchDeletes U := hUC_delSub heD
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).2 heDU
  have hRS := restrictSplits_spec hUC_val hS1_props.1 hS1_sub hS1_V hS1_E hKeep_disj
  have hSp_isSplit : ∀ u ∈ splitList, isSplit u = true := by
    have haux : ∀ (ks : Finset ℕ) (xs : List Update) (u : Update),
        u ∈ restrictSplits ks xs → isSplit u = true := by
      intro ks xs
      induction xs with
      | nil => intro u hu; simp [restrictSplits] at hu
      | cons op rest ih =>
        intro u hu
        cases op with
        | insert _ _ _ => exact ih u hu
        | delete _ => exact ih u hu
        | split v v' St Sh =>
          simp only [restrictSplits, List.mem_cons] at hu
          rcases hu with rfl | hrest
          · rfl
          · exact ih u hrest
    exact haux keepSet UC
  have hSp_encR : (S₁.batchEnc splitList : ℝ) ≤
      4 * (S₁.m : ℝ) * Real.log (2 * (S₁.m : ℝ) + 2) + (splitList.length : ℝ) :=
    batchEnc_splits_le_real hS1_props.1 hRS.1 hSp_isSplit
  have hS1_m_le : S₁.m ≤ M := (Finset.card_le_card hS1_props.2.2.2.2.1).trans hScur_m_le
  have hLogS1 : Real.log (2 * (S₁.m : ℝ) + 2) ≤ 2 * (bundleLogFactor M N : ℝ) :=
    log_two_mul_add_two_le_two_mul_bundleLog S₁.m M N hS1_m_le
  have hS1_term : 4 * (S₁.m : ℝ) * Real.log (2 * (S₁.m : ℝ) + 2) ≤
      8 * (bundleLogFactor M N : ℝ) * (M : ℝ) := by
    have h1 : 4 * (S₁.m : ℝ) ≤ 4 * (M : ℝ) := by
      have : (S₁.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hS1_m_le
      linarith
    have h2 : 0 ≤ Real.log (2 * (S₁.m : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) S₁.m])
    calc 4 * (S₁.m : ℝ) * Real.log (2 * (S₁.m : ℝ) + 2)
        ≤ 4 * (M : ℝ) * (2 * (bundleLogFactor M N : ℝ)) :=
          mul_le_mul h1 hLogS1 h2 (by positivity)
      _ = 8 * (bundleLogFactor M N : ℝ) * (M : ℝ) := by ring
  have hR_sub : tr.cs.RF.R ⊆ cs'.RF.R := hStepProps.2.2.2.2
  have hR_sum := compLSF_R_sum_le hI hBU
  have hR_sdiffR : ((cs'.RF.R \ tr.cs.RF.R).card : ℝ) ≤
      112 * (bundleLogFactor M N : ℝ) * (b : ℝ) := by
    have hcard : (cs'.RF.R \ tr.cs.RF.R).card + tr.cs.RF.R.card = cs'.RF.R.card :=
      Finset.card_sdiff_add_card_eq_card hR_sub
    have hcardR : ((cs'.RF.R \ tr.cs.RF.R).card : ℝ) =
        (cs'.RF.R.card : ℝ) - (tr.cs.RF.R.card : ℝ) := by
      have : ((cs'.RF.R \ tr.cs.RF.R).card : ℝ) + (tr.cs.RF.R.card : ℝ) = (cs'.RF.R.card : ℝ) := by
        exact_mod_cast hcard
      linarith
    have hG0n : tr.cs.G₀.n ≤ M + N := by rw [hG0_cs]; omega
    have hLogN : Real.log ((tr.cs.G₀.n : ℝ) + 2) ≤ ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) :=
      log_add_two_le_natLog tr.cs.G₀.n M N hG0n
    have hLogN_nn : 0 ≤ Real.log ((tr.cs.G₀.n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) tr.cs.G₀.n])
    have hSq : (Real.log ((tr.cs.G₀.n : ℝ) + 2)) ^ 2 ≤ (bundleLogFactor M N : ℝ) := by
      have h1 := pow_le_pow_left₀ hLogN_nn hLogN 2
      have h2 : (((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ)) ^ 2 = (bundleLogFactor M N : ℝ) := by
        unfold bundleLogFactor; push_cast; ring
      linarith
    have hbR : (U.length : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hMul : 56 * ((2 * U.length : ℕ) : ℝ) * (Real.log ((tr.cs.G₀.n : ℝ) + 2)) ^ 2 ≤
        112 * (bundleLogFactor M N : ℝ) * (b : ℝ) := by
      have h2U : 56 * ((2 * U.length : ℕ) : ℝ) = 112 * (U.length : ℝ) := by push_cast; ring
      rw [h2U]
      have hstep1 : 112 * (U.length : ℝ) * (Real.log ((tr.cs.G₀.n : ℝ) + 2)) ^ 2 ≤
          112 * (b : ℝ) * (bundleLogFactor M N : ℝ) :=
        mul_le_mul (by linarith) hSq (sq_nonneg _) (by positivity)
      linarith
    linarith
  have hSp_lenEq : splitList.length = (cs'.RF.R \ tr.cs.RF.R).card := by
    have h1 : splitList.length = batchSplitCount (canonCoreBatch tr.cs U) := hRS.2.2.2.2.2
    exact h1.trans hUC_splits
  have hSp_lenR : (splitList.length : ℝ) ≤ 112 * (bundleLogFactor M N : ℝ) * (b : ℝ) := by
    rw [hSp_lenEq]
    exact hR_sdiffR
  have hSp_encNat : S₁.batchEnc splitList ≤
      8 * bundleLogFactor M N * M + 112 * bundleLogFactor M N * b := by
    have hR : (S₁.batchEnc splitList : ℝ) ≤
        ((8 * bundleLogFactor M N * M + 112 * bundleLogFactor M N * b : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  rw [hEnc_split]
  have h8_le_24 : 8 * bundleLogFactor M N * M ≤ 24 * bundleLogFactor M N * M := by
    have : 8 * bundleLogFactor M N ≤ 24 * bundleLogFactor M N := by omega
    exact Nat.mul_le_mul_right M this
  have hgoal_ring :
      (5 + 24 * bundleLogFactor M N) * M + (1 + 112 * bundleLogFactor M N) * b =
      5 * M + 24 * bundleLogFactor M N * M + b + 112 * bundleLogFactor M N * b := by ring
  rw [hgoal_ring]
  omega

/-- Machine-cost tool corollary of `stepBundleTree_US_batchEnc_le`, transferring via
`sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq`. -/
theorem stepBundleTreeMach_US_batchEnc_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (t r : ℕ) (ht : t ≤ τ) (hInit : IsValidLSFInitFor lsfInit C_lsst k r)
    {U : List Update} {b : ℕ} (ord_in ord' : ℕ → List End)
    (hBU : ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).runOrdAfterRestarts
      k M N D ord restarts t |>.trees r).cs.G.BatchIsValid U)
    (hGm : ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).runOrdAfterRestarts
      k M N D ord restarts t |>.trees r).cs.G.m ≤ M)
    (hb : U.length ≤ b) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let tr := (Tm.runOrdAfterRestarts k M N D ord restarts t).trees r
    let info := stepBundleTree sparsify tr U ord_in ord'
    tr.S_cur.batchEnc info.U_S ≤
      (5 + 24 * bundleLogFactor M N) * M + (1 + 112 * bundleLogFactor M N) * b := by
  intro Tm tr info
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
    params spanConst k M N D ord restarts t).2.2.trees r
  have hStepEq := BundleNonMachEq.step sparsify hNM U ord_in ord'
  have hBU' : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
      k M N D ord restarts t |>.trees r).cs.G.BatchIsValid U := hNM.cs ▸ hBU
  have hGm' : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
      k M N D ord restarts t |>.trees r).cs.G.m ≤ M := hNM.cs ▸ hGm
  have hbase := stepBundleTree_US_batchEnc_le lsfInit C_lsst L hL P_b sparsify k M N τ hk D ord
    restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd t r ht hInit ord_in ord' hBU' hGm' hb
  change tr.S_cur.batchEnc info.U_S ≤ _
  rw [hNM.S_cur, hStepEq.2.2.1]
  exact hbase

end MinCostFlow.Final.DryRun
