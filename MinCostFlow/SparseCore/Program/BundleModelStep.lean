module

public import MinCostFlow.SparseCore.Program.BundleModelBridgeStep
public import MinCostFlow.SparseCore.Program.BundleCapHeadroom

/-!
# Model-level step and single-slot lazy init on `bunTableRep` (`BundleModelStep`)

Connects `bunTable_step_runs` and `bunTable_initSlots_runs` (`BundleUnified.lean`) directly to
`stepBundleTree` (`BundleTreeCore.lean`), `outCoreOrder` (`OutSpec.lean`), `BunTableMatches`
(`RestartModelState.lean`), and `bunRestartInv` (`BunRestartIface.lean`):

1. **Step on `bunTableRep` (`bunTable_step_model_runs_on`, `bunTable_step_model_runs`)**:
   - Starting from `bunRestartInv vCap eCap S₀ cord` and `BunTableMatches tr slotOf S₀` (or any
     tracked set `P` of pairs), running `bundleStepStmt` with `cord' = outCoreOrder info.state ord'`
     (where `info := stepBundleTree sparsify tr U ord ord'`) ends with `S'` such that:
     * `(bunTableRep slotCap vCap eCap tr.k).rep tbl S' m st'.mem` (same `slotCap`, same `tr.k`),
     * `BunAgree B' (info.state.bun q)` for every tracked pair `q` (in particular every old active
       pair `q ∈ activePairs tr`, or every `q ∈ activePairs info.state` when newly active pairs
       were initialized first),
     * `bunRestartInv vCap eCap S' cord'`,
     * `SmallBatchAt` (`W ≤ 6 * Enc`) for every touched slot's emitted `bundleCompStep` batch,
     * amortized cost paying `bunPhiMul` per split-added bundle into `bunTableRep.phi` and
       telescoping smaller-side scan work into `bundleScanPotMul TS eCap * tourPot` via
       `scanNonMaxSum_le_tourPot_drop_with_adds` (allowing edge insertions / released tree edges via
       `addG`, `addR`, `maxLen`).
2. **One-slot lazy init (`bunTable_initOneSlot_runs`, `bunTable_initNewlyActive_runs`)**:
   - Initializes a single empty slot `s < slotCap` via `bundleInitSlotsStmt` (`nSlots = 1`) to a
     bundle state agreeing with `initBundleFor cs ord E k`, preserving `bunTableRep` and
     `bunRestartInv vCap eCap S' cord`, leaving all other slots unchanged, and extending
     `BunTableMatches` to a newly active pair `(C, b)` (`C ∈ info.newlyActive`) before the step.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

public section

/-! ## 1. Main step theorems on `bunTableRep` -/

/-- General model-level step theorem on `bunTableRep slotCap vCap eCap tr.k` for any tracked set
`P` of `(component, bucket)` pairs (e.g. `activePairs tr`, or `activePairs info.state` after
initializing newly active pairs with `bunTable_initNewlyActive_runs`). -/
theorem bunTable_step_model_runs_on {TS : BundleTourSpec} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {w slotCap vCap eCap tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    {slotOf : Finset ℕ × ℤ → ℕ} {P : Finset (Finset ℕ × ℤ)}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)} {R_old R_new : Finset ℕ} {oldRoots : List ℕ}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hD_eq : (dels.map Prod.fst).toFinset = batchDeletes U)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hMatch0 : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
      S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hcord'_bounds : ∀ v x, x ∈ outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v →
      v < vCap ∧ x.1 < eCap)
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, (bunTableRep slotCap vCap eCap tr.k).foot tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') tx₀ mem₀)
    (hrep0 : (bunTableRep slotCap vCap eCap tr.k).rep tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ trD ∈ dels, trD.1 < eCap ∧ trD.2.1 < 2 ^ w ∧ trD.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    {addG : ℕ → ℕ} {addR : ℕ → ℕ} {maxLen : ℕ}
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ v ∈ gs[gi].toFinset, (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v).length) ≤
        (cord (oldRoots[gi]'(by omega))).length + addG gi ∧
      (cord (oldRoots[gi]'(by omega))).length + addG gi ≤ maxLen)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧
        (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' r).length ≤ (cord r).length + addR r ∧
        (cord r).length + addR r ≤ maxLen)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ batchDeletes U)
        (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) bun,
            (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src x ∈ gs[gi].toFinset)
    (hcap_ok : ∀ (maxIdxs : List ℕ) (j : Fin slotCap) (B₀ : BundleState) (ptr bunCap : ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      S₀ j = some B₀ → m.slotBlocks j = some (ptr, bunCap) →
      B₀.vertices.card + slotScannedEnds S₀ (batchDeletes U)
        (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') gs maxIdxs j ≤ bunCap)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let cord' := outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord'
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched < 2 ^ w) :
    let info := stepBundleTree sparsify tr U ord ord'
    let cord' := outCoreOrder info.state ord'
    let S' := tableAfterStepRuns tr.cs tr.k ord' U S₀
    let U_grp := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
    let totalAdded := (∑ gi ∈ Finset.range gs.length, addG gi) + ∑ r ∈ R_new \ U_grp, addR r
    ∃ body, p.procs[b + bundleIdxStep]? = some body ∧ ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      Runs w p ω body
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      (bunTableRep slotCap vCap eCap tr.k).rep tbl S' m st'.mem ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      bunRestartInv vCap eCap S' cord' ∧
      (∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B' : BundleState),
        S' ⟨slotOf q, hs⟩ = some B' ∧ BunAgree B' (info.state.bun q)) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 totalWords) ∧
      (∀ a < h₀, ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + (bunTableRep slotCap vCap eCap tr.k).phi tbl m st'.mem +
          bundleScanPotMul TS eCap * tourPot R_new cord' + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bunPhiMul * (∑ j : Fin slotCap, match S₀ j with
          | none => 0
          | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) +
        (bunTableRep slotCap vCap eCap tr.k).phi tbl m mem₀ +
        bundleScanPotMul TS eCap * (tourPot R_old cord + totalAdded * (Nat.log 2 maxLen + 2)) +
        htour.rep.phi tourH tx₀ mem₀ := by
  intro info cord' S' U_grp totalAdded
  set src' := (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src
  have hcord'_nd : ∀ v, (cord' v).Nodup := fun v => by
    unfold cord' outCoreOrder
    split_ifs with hex
    · exact (coreRotation (L := info.state.cs.lsf)
        hex.choose_spec.choose_spec.choose_spec.choose
        hex.choose_spec.choose_spec.choose.hG_val
        (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).nodup v
    · exact List.nodup_nil
  have hsrc_iff : ∀ j B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ batchDeletes U), ∀ v, x ∈ cord' v ↔ src' x = v := by
    intro j B₀ hS₀ x hx v
    obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, _, hσ, _, hU, _⟩ := hready j B₀ hS₀
    have hI' := compLSFBatch_inv hI hU
    let σ' : Rotation info.state.cs.G := (compLSFBatch_G tr.cs U).symm ▸ σ
    have hσ' : σ'.order = ord' := by
      dsimp only [σ']
      have hcast : ∀ {G H : MGraph} (he : G = H) (τ : Rotation G), (he ▸ τ : Rotation H).order = τ.order := by
        intro G H he τ; cases he; rfl
      exact (hcast _ σ).trans hσ
    have hpart := (bundleRunsStep_spec (hready j B₀ hS₀)).1.1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    have hxE : x.1 ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E := by
      have hsub := hpart.1
      have hEeq := (bundleRunsStep_spec (hready j B₀ hS₀)).2.2.2.2.1
      rw [hEeq] at hsub
      exact hsub ((mem_edgeEnds _ _).mp hx)
    exact outCoreOrder_mem_iff_src hI' σ' hσ' hxE v
  obtain ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hmaxLen, hmaxSpec,
    hndT, hltT, htouchIff, hhLo, hhHi, hzf, htr', htf', hrep', hout0, hdescs, hfr, hc⟩ :=
    bunTable_step_runs (pos := pos) (ω := ω) (cord' := cord') (src' := src') hp htour hw16 htourH_w hpk_w
      htbl_w hblks_w hdel_w hgrp_w hout_w hfoot_lt hdel_lt hgrp_lt hout_lt hdel_disj_foot
      hgrp_disj_foot hout_disj_foot htfoot_lt htfoot_disj_tbl htfoot_disj_grp htfoot_disj_out
      hzero htrep hrep0 hdels_len hdels_mem hdels_lt hdels_par hgs_mem hgs_pos hgs_lt hgs_nd hgs_disj
      (fun _ _ v _ x hx => (hcord'_bounds v x hx).2) (fun _ _ v _ => hcord'_nd v)
      (fun j B₀ hS₀ x hx => (hcord'_bounds (src' x) x ((hsrc_iff j B₀ hS₀ x (hD_eq ▸ hx) (src' x)).mpr rfl)).1)
      (fun j B₀ hS₀ x hx => (hsrc_iff j B₀ hS₀ x (hD_eq ▸ hx) (src' x)).mpr rfl)
      (fun j B₀ hS₀ x hx v' hv' => ((hsrc_iff j B₀ hS₀ x (hD_eq ▸ hx) v').mp hv').symm)
      (by simpa only [hD_eq] using hbundle_in_group)
      (by simpa only [hD_eq] using hcap_ok)
      (by simpa only [hD_eq] using hh_sp)
  simp only [hD_eq] at hhHi hrep' hdescs hc
  set candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
  have hcand_eq : ∀ j B₀, S₀ j = some B₀ →
      candSet j = (exactSplitCands B₀ (B₀.edges \ batchDeletes U) src').toFinset := fun j B₀ hS₀ =>
    scanCands_eq_exactSplitCands hS₀ hgs_nd (fun _ _ v _ => hcord'_nd v)
      (fun gi hgi => (hmaxSpec gi hgi).1) (hsrc_iff j B₀ hS₀) (hbundle_in_group j B₀ hS₀)
  have hrep_runs : BundleTableRepAt slotCap vCap eCap tbl S' m st'.mem :=
    tableAfterStep_congr_runs hrep0.1 hready hcand_eq hrep'.1
  have hinv' : bunRestartInv vCap eCap S' cord' :=
    bunRestartInv_tableAfterStepRuns hinv0 hready hcord'_bounds
  have hMatch' : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B' : BundleState),
      S' ⟨slotOf q, hs⟩ = some B' ∧ BunAgree B' (info.state.bun q) := by
    intro q hq
    obtain ⟨hs, B₀, hS₀, hag⟩ := hMatch0 q hq
    refine ⟨hs, (bundleRunsStep tr.cs B₀ tr.k ord' U).2, by simp [S', tableAfterStepRuns, hS₀], ?_⟩
    have hr := hready ⟨slotOf q, hs⟩ B₀ hS₀
    have hcomp := bunAgree_bundleCompStep_eq hag hr
    simpa only [info, stepBundleTree, bundleCompStep_eq hr] using hcomp.2
  have hbatch_eq : ∀ j B₀, S₀ j = some B₀ →
      slotBatchOf S₀ (batchDeletes U) src' candSet j = (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 := by
    intro j B₀ hS₀
    have hr := hready j B₀ hS₀
    have heq := bundleStepEmitSlot_eq_bundleRunsStep hr (hcand_eq j B₀ hS₀)
    rw [bundleCompStep_eq hr, heq.1]
    simp only [slotBatchOf, hS₀]
    rfl
  have hsum_splits : (∑ j : Fin slotCap, batchSplitCount (slotBatchOf S₀ (batchDeletes U) src' candSet j)) =
      ∑ j : Fin slotCap, match S₀ j with
        | none => 0
        | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    cases hS : S₀ j with
    | none => simp [slotBatchOf, hS, batchSplitCount]
    | some B₀ => rw [hbatch_eq j B₀ hS]
  have hdrop := scanNonMaxSum_le_tourPot_drop_with_adds hold_len hold_nd hold_sub hgs_nd hgs_sub hgs_disj
    hmaxSpec hgroup_sum_le hrest_le
  have hmul := Nat.mul_le_mul_left (bundleScanPotMul TS eCap) hdrop
  rw [Nat.mul_add] at hmul
  refine ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, ⟨hrep_runs, hrep'.2⟩, htr',
    hinv', hMatch', hhLo, hhHi, hzf, htf', hout0, ?_, hfr, ?_⟩
  · intro i hi
    obtain ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, hbat⟩ := hdescs i hi
    refine ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, fun B₀ hS₀ => ?_⟩
    rw [← hbatch_eq ⟨touched[i]'hi, hs⟩ B₀ hS₀]
    exact (hbat B₀ hS₀).1
  · rw [hsum_splits] at hc
    change c + 70 * touched.length + (bunTableRep slotCap vCap eCap tr.k).phi tbl m st'.mem +
        bundleScanPotMul TS eCap * tourPot R_new cord' + htour.rep.phi tourH tx' st'.mem ≤
      bundleStepCost TS eCap delCount gs +
      bunPhiMul * (∑ j : Fin slotCap, match S₀ j with
        | none => 0
        | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) +
      (bunTableRep slotCap vCap eCap tr.k).phi tbl m mem₀ +
      bundleScanPotMul TS eCap * (tourPot R_old cord + totalAdded * (Nat.log 2 maxLen + 2)) +
      htour.rep.phi tourH tx₀ mem₀
    dsimp only [totalAdded, U_grp]
    omega

/-- Specialization of `bunTable_step_model_runs_on` to `P = activePairs tr` (`BunTableMatches tr slotOf S₀`). -/
theorem bunTable_step_model_runs {TS : BundleTourSpec} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {w slotCap vCap eCap tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    {slotOf : Finset ℕ × ℤ → ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)} {R_old R_new : Finset ℕ} {oldRoots : List ℕ}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hD_eq : (dels.map Prod.fst).toFinset = batchDeletes U)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hMatch0 : BunTableMatches tr slotOf S₀)
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hcord'_bounds : ∀ v x, x ∈ outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v →
      v < vCap ∧ x.1 < eCap)
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, (bunTableRep slotCap vCap eCap tr.k).foot tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') tx₀ mem₀)
    (hrep0 : (bunTableRep slotCap vCap eCap tr.k).rep tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ trD ∈ dels, trD.1 < eCap ∧ trD.2.1 < 2 ^ w ∧ trD.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    {addG : ℕ → ℕ} {addR : ℕ → ℕ} {maxLen : ℕ}
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ v ∈ gs[gi].toFinset, (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v).length) ≤
        (cord (oldRoots[gi]'(by omega))).length + addG gi ∧
      (cord (oldRoots[gi]'(by omega))).length + addG gi ≤ maxLen)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧
        (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' r).length ≤ (cord r).length + addR r ∧
        (cord r).length + addR r ≤ maxLen)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ batchDeletes U)
        (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) bun,
            (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src x ∈ gs[gi].toFinset)
    (hcap_ok : ∀ (maxIdxs : List ℕ) (j : Fin slotCap) (B₀ : BundleState) (ptr bunCap : ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      S₀ j = some B₀ → m.slotBlocks j = some (ptr, bunCap) →
      B₀.vertices.card + slotScannedEnds S₀ (batchDeletes U)
        (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') gs maxIdxs j ≤ bunCap)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let cord' := outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord'
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched < 2 ^ w) :
    let info := stepBundleTree sparsify tr U ord ord'
    let cord' := outCoreOrder info.state ord'
    let S' := tableAfterStepRuns tr.cs tr.k ord' U S₀
    let U_grp := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
    let totalAdded := (∑ gi ∈ Finset.range gs.length, addG gi) + ∑ r ∈ R_new \ U_grp, addR r
    ∃ body, p.procs[b + bundleIdxStep]? = some body ∧ ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      Runs w p ω body
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      (bunTableRep slotCap vCap eCap tr.k).rep tbl S' m st'.mem ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      bunRestartInv vCap eCap S' cord' ∧
      (∀ q ∈ activePairs tr, ∃ (hs : slotOf q < slotCap) (B' : BundleState),
        S' ⟨slotOf q, hs⟩ = some B' ∧ BunAgree B' (info.state.bun q)) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 totalWords) ∧
      (∀ a < h₀, ¬ (bunTableRep slotCap vCap eCap tr.k).foot tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + (bunTableRep slotCap vCap eCap tr.k).phi tbl m st'.mem +
          bundleScanPotMul TS eCap * tourPot R_new cord' + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bunPhiMul * (∑ j : Fin slotCap, match S₀ j with
          | none => 0
          | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) +
        (bunTableRep slotCap vCap eCap tr.k).phi tbl m mem₀ +
        bundleScanPotMul TS eCap * (tourPot R_old cord + totalAdded * (Nat.log 2 maxLen + 2)) +
        htour.rep.phi tourH tx₀ mem₀ :=
  bunTable_step_model_runs_on (P := activePairs tr) hp htour hD_eq hinv0 hMatch0 hready
    hcord'_bounds hw16 htourH_w hpk_w htbl_w hblks_w hdel_w hgrp_w hout_w
    hfoot_lt hdel_lt hgrp_lt hout_lt hdel_disj_foot hgrp_disj_foot hout_disj_foot
    htfoot_lt htfoot_disj_tbl htfoot_disj_grp htfoot_disj_out hzero htrep hrep0
    hdels_len hdels_mem hdels_lt hdels_par hgs_mem hgs_pos hgs_lt hgs_nd hgs_sub hgs_disj
    hold_len hold_nd hold_sub hgroup_sum_le hrest_le hbundle_in_group hcap_ok hh_sp

/-! ## 2. One-slot lazy init for a newly active pair (`newlyActive`) -/

/-- Initializes one empty slot `s < slotCap` via `bundleInitSlotsStmt` (`nSlots = 1`) to a
`BundleState` agreeing with `initBundleFor cs ord E k`, preserving `bunTableRep` and
`bunRestartInv vCap eCap S' cord` and leaving every other slot unchanged. -/
theorem bunTable_initOneSlot_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k s cap
    slotSpecPtr edgeAssignPtr rPtr h : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {cs : CompLSFState} {ord cord : ℕ → List End} {E : Finset ℕ}
    {edges : List ℕ} {rList : List ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    (hs_lt : s < slotCap) (hs_empty : S₀ ⟨s, hs_lt⟩ = none)
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k) (hcore : CoreCordOf cs ord cord)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * edges.length ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * edges.length ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + rList.length ≤ h)
    (hrPtr_disj_tbl : rPtr + rList.length ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS [(s, cap)] cord rList < 2 ^ w)
    (hrep0 : (bunTableRep slotCap vCap eCap k).rep tbl S₀ m₀ mem₀)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ ptr c, m₀.slotBlocks j = some (ptr, c) →
        a < ptr ∨ ptr + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + rList.length ≤ a)
    (hspec_mem : mem₀ slotSpecPtr = s ∧ mem₀ (slotSpecPtr + 1) = cap)
    (hcap_ok : 4 * E.card ≤ cap)
    (hedges_nd : edges.Nodup) (hedges_eq : edges.toFinset = E)
    (hE_sub : E ⊆ (coreGraph cs.G cs.lsf).E)
    (hE_lt : ∀ e ∈ E, e < eCap)
    (hE_fresh : ∀ e ∈ E, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → e ∉ B.edges)
    (hedges_w : edges.length < 2 ^ w)
    (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr edges.length = edges.map (·, s))
    (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w)
    (hrList_pw : rList.Pairwise (· < ·))
    (hrList_sub : ∀ v ∈ rList, v ∈ (coreGraph cs.G cs.lsf).V)
    (hcov : ∀ v x, x ∈ cord v → x.1 ∈ E → v ∈ rList) :
    let m' := allocSlotBlocksMeta m₀ [(s, cap)] h
    let args := [tbl, tourH, 1, slotSpecPtr, edges.length, edgeAssignPtr, rList.length, rPtr, h]
    ∃ body, p.procs[b + bundleIdxInitSlots]? = some body ∧ ∃ st' c hEnd tx' B',
      let S' : BundleTableState slotCap := Function.update S₀ ⟨s, hs_lt⟩ (some B')
      Runs w p ω body (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      (bunTableRep slotCap vCap eCap k).rep tbl S' m' st'.mem ∧
      bunCapHeadroomInv B' cap ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      BunAgree B' (initBundleFor cs ord E k) ∧
      (∀ j : Fin slotCap, j ≠ ⟨s, hs_lt⟩ → S' j = S₀ j) ∧
      h + bundleSlotBlockSize cap ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS [(s, cap)] cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m' a →
        (bunTableRep slotCap vCap eCap k).foot tbl m₀ a ∨ (h ≤ a ∧ a < h + bundleSlotBlockSize cap)) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + bundleSlotBlockSize cap ≤ a ∧ a < hEnd)) ∧
      (∀ a, a < h → ¬ (bunTableRep slotCap vCap eCap k).foot tbl m₀ a →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + (bunTableRep slotCap vCap eCap k).phi tbl m' st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap 1 edges.length cord rList + bunPhiMul * (2 * edges.length) +
        (bunTableRep slotCap vCap eCap k).phi tbl m₀ mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro m' args
  set assigns := edges.map (·, s)
  have hrList_nd : rList.Nodup := hrList_pw.imp ne_of_lt
  have hcord_nd : ∀ v ∈ rList, (cord v).Nodup := fun v _ => by
    obtain ⟨C_lsst, ℓ₀, hI, ρG, _, hcord⟩ := hcore
    rw [hcord]
    exact (coreRotation (L := cs.lsf) ρG hI.hG_val (compLSF_RF_isRSF hI)).nodup v
  have hslotE : slotEdgesOf assigns s = E := by
    ext e
    simp only [slotEdgesOf, assigns, List.mem_toFinset, List.mem_map, List.mem_filter,
      beq_iff_eq, ← hedges_eq]
    constructor
    · rintro ⟨⟨e', s'⟩, ⟨⟨e'', he'', heq⟩, _⟩, rfl⟩
      injection heq with h1 _; exact h1 ▸ he''
    · intro he
      exact ⟨(e, s), ⟨⟨e, he, rfl⟩, rfl⟩, rfl⟩
  have hcov_es : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v := by
    intro es hes side
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hes
    have heE : e ∈ E := hedges_eq ▸ List.mem_toFinset.mpr he
    obtain ⟨C_lsst, ℓ₀, hI, ρG, _, hcord⟩ := hcore
    set ρc := coreRotation (L := cs.lsf) ρG hI.hG_val (compLSF_RF_isRSF hI)
    have hx_mem : (e, side) ∈ cord ((coreGraph cs.G cs.lsf).src (e, side)) := by
      rw [hcord, ρc.mem_order]
      exact ⟨hE_sub heE, rfl⟩
    exact ⟨_, hcov _ (e, side) hx_mem heE, hx_mem⟩
  have hspecs_mem : bundleReadPairs mem₀ slotSpecPtr 1 = [(s, cap)] := by
    simp [bundleReadPairs, hspec_mem.1, hspec_mem.2]
  have hcap_len : (initPrefixSlots cord rList (slotEdgesOf assigns s) k).length ≤ cap := by
    rw [hslotE]
    exact (initPrefixSlots_length_le hk1 hrList_nd hcord_nd hinv0.1.1).trans (by omega)
  obtain ⟨body, hbody, st', c, hEnd, tx', hrun, hhLo, hhHi, hzf, hrep', hinv', htr',
    hfootB', hfootT', hfr, hc⟩ :=
    bunTable_initSlots_runs (specs := [(s, cap)]) (assigns := assigns) (nSlots := 1)
      (nEdges := edges.length) (nR := rList.length)
      hp htour hw16 hk1 htourH_w htbl_h hfoot0_lt hspec_h hspec_disj_tbl hassign_h hassign_disj_tbl
      hrPtr_h hrPtr_disj_tbl hspace_w hrep0 hinv0 hzero0 htour_rep htour_foot_lt
      htour_foot_disj_tbl htour_foot_disj_blocks htour_foot_disj_spec htour_foot_disj_r
      rfl hspecs_mem (fun sb hsb => by simp at hsb; rcases hsb with rfl; exact hs_lt)
      (by simp) (fun sb hsb _ => by simp at hsb; rcases hsb with rfl; exact hs_empty)
      (fun sb hsb => by simp at hsb; rcases hsb with rfl; exact hcap_len)
      (by simp [assigns]) hassigns_mem
      (fun es hes => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hes
        exact ⟨hE_lt e (hedges_eq ▸ List.mem_toFinset.mpr he), by simp⟩)
      (by simpa [assigns, Function.comp_def] using hedges_nd)
      (fun es hes => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hes
        exact hE_fresh e (hedges_eq ▸ List.mem_toFinset.mpr he))
      hedges_w rfl hrList_mem hrList_lt hrList_nd hcord_nd hcov_es
  obtain ⟨B', hB'_eq, hB'_agree⟩ :=
    tableAfterInitSlots_bunAgree (S₀ := S₀) (specs := [(s, cap)]) (assigns := assigns)
      (rList := rList) (j := ⟨s, hs_lt⟩) hk1 hcore (by simp) (by rw [hslotE]; exact hE_sub)
      hrList_pw hrList_sub (fun v x hx hxE => hcov v x hx (hslotE ▸ hxE))
  rw [hslotE] at hB'_agree
  have hS'_eq : tableAfterInitSlots S₀ [(s, cap)] assigns cord rList k =
      Function.update S₀ ⟨s, hs_lt⟩ (some B') := by
    funext j
    by_cases hj : j = ⟨s, hs_lt⟩
    · subst hj; simpa [Function.update_self] using hB'_eq
    · have hne : j.1 ≠ s := fun h => hj (Fin.ext h)
      simp [tableAfterInitSlots, Function.update_of_ne hj, hne]
  rw [hS'_eq] at hrep' hinv'
  have hblk_sp : slotBlocksSpace [(s, cap)] = bundleSlotBlockSize cap := by
    simp [slotBlocksSpace]
  have hB'_headroom : bunCapHeadroomInv B' cap := by
    have hBeq : B' = bundleStateOfSlots (initPrefixSlots cord rList E k) E := by
      have h1 : tableAfterInitSlots S₀ [(s, cap)] assigns cord rList k ⟨s, hs_lt⟩ =
          some (bundleStateOfSlots (initPrefixSlots cord rList E k) E) := by
        simp [tableAfterInitSlots, hslotE]
      exact Option.some.inj (hB'_eq.symm.trans h1)
    rw [hBeq]
    refine bunCapHeadroomInv_of_bundleStateOfSlots hk1 hrList_nd hcord_nd hinv0.1.1 ?_ hcap_ok
    intro x hx
    have hmem : x.1 ∈ edges := List.mem_toFinset.mp (hedges_eq ▸ hx)
    have hes : (x.1, s) ∈ assigns := List.mem_map.mpr ⟨x.1, hmem, rfl⟩
    obtain ⟨v, hv, hxv⟩ := hcov_es (x.1, s) hes x.2
    exact ⟨v, hv, by simpa [Prod.mk.eta] using hxv⟩
  rw [hblk_sp] at hhLo hfootB' hfootT'
  exact ⟨body, hbody, st', c, hEnd, tx', B', hrun, hrep', hB'_headroom, hinv', htr', hB'_agree,
    fun j hj => Function.update_of_ne hj _ _, hhLo, hhHi, hzf, hfootB', hfootT', hfr, hc⟩

/-- Pre-step lazy initialization of one empty slot `s = slotOf qNew` for a newly active pair
`qNew = (C, b)` (`C ∈ info.newlyActive`) to the model's lazy bundle `tr.bun qNew`, extending
agreement on `P` to `insert qNew P` while preserving `bunTableRep` and `bunRestartInv`.

In `stepBundleTree` (`BundleTreeCore.lean`), `info.state.bun q = (bundleCompStep tr.cs (tr.bun q) tr.k ord ord' U).2`
for every `q` (including `C ∈ info.newlyActive`). Calling `bunTable_initNewlyActive_runs` before
`bunTable_step_model_runs_on` installs `tr.bun qNew` into slot `slotOf qNew`, after which the step
advances both old active pairs and newly active pairs together to `BunTableMatches info.state slotOf S'`. -/
theorem bunTable_initNewlyActive_runs {TS : BundleTourSpec} {L : ℕ}
    {w slotCap vCap eCap tbl tourH cap slotSpecPtr edgeAssignPtr rPtr h : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tr : BundleTreeState L} {ord : ℕ → List End}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    {slotOf : Finset ℕ × ℤ → ℕ} {P : Finset (Finset ℕ × ℤ)} {qNew : Finset ℕ × ℤ}
    {E : Finset ℕ} {edges : List ℕ} {rList : List ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    (hLazy : BunAgree (initBundleFor tr.cs ord E tr.k) (tr.bun qNew))
    (hs_lt : slotOf qNew < slotCap) (hs_empty : S₀ ⟨slotOf qNew, hs_lt⟩ = none)
    (hMatch0 : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
      S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hDisjNew : ∀ q ∈ P, slotOf q ≠ slotOf qNew)
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ tr.k)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, (bunTableRep slotCap vCap eCap tr.k).foot tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * edges.length ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * edges.length ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + rList.length ≤ h)
    (hrPtr_disj_tbl : rPtr + rList.length ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS [(slotOf qNew, cap)] (outCoreOrder tr ord) rList < 2 ^ w)
    (hrep0 : (bunTableRep slotCap vCap eCap tr.k).rep tbl S₀ m₀ mem₀)
    (hinv0 : bunRestartInv vCap eCap S₀ (outCoreOrder tr ord))
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH (outCoreOrder tr ord) tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ ptr c, m₀.slotBlocks j = some (ptr, c) →
        a < ptr ∨ ptr + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + rList.length ≤ a)
    (hspec_mem : mem₀ slotSpecPtr = slotOf qNew ∧ mem₀ (slotSpecPtr + 1) = cap)
    (hcap_ok : 4 * E.card ≤ cap)
    (hedges_nd : edges.Nodup) (hedges_eq : edges.toFinset = E)
    (hE_sub : E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E)
    (hE_lt : ∀ e ∈ E, e < eCap)
    (hE_fresh : ∀ e ∈ E, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → e ∉ B.edges)
    (hedges_w : edges.length < 2 ^ w)
    (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr edges.length = edges.map (·, slotOf qNew))
    (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w)
    (hrList_pw : rList.Pairwise (· < ·))
    (hrList_sub : ∀ v ∈ rList, v ∈ (coreGraph tr.cs.G tr.cs.lsf).V)
    (hcov : ∀ v x, x ∈ outCoreOrder tr ord v → x.1 ∈ E → v ∈ rList) :
    let cord := outCoreOrder tr ord
    let m' := allocSlotBlocksMeta m₀ [(slotOf qNew, cap)] h
    let args := [tbl, tourH, 1, slotSpecPtr, edges.length, edgeAssignPtr, rList.length, rPtr, h]
    ∃ body, p.procs[b + bundleIdxInitSlots]? = some body ∧ ∃ st' c hEnd tx' B',
      let S' : BundleTableState slotCap := Function.update S₀ ⟨slotOf qNew, hs_lt⟩ (some B')
      Runs w p ω body (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      (bunTableRep slotCap vCap eCap tr.k).rep tbl S' m' st'.mem ∧
      bunCapHeadroomInv B' cap ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ q ∈ insert qNew P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
        S' ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q)) ∧
      h + bundleSlotBlockSize cap ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS [(slotOf qNew, cap)] cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      c + (bunTableRep slotCap vCap eCap tr.k).phi tbl m' st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap 1 edges.length cord rList + bunPhiMul * (2 * edges.length) +
        (bunTableRep slotCap vCap eCap tr.k).phi tbl m₀ mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro cord m' args
  obtain ⟨body, hbody, st', c, hEnd, tx', B', hrun, hrep', hB'_headroom, hinv', htr', hag, hother,
    hhLo, hhHi, hzf, _, _, _, hc⟩ :=
    bunTable_initOneSlot_runs hp htour hs_lt hs_empty hw16 hk1 (outCoreOrder_coreCordOf hI ρ hρ)
      htourH_w htbl_h hfoot0_lt hspec_h hspec_disj_tbl hassign_h hassign_disj_tbl hrPtr_h
      hrPtr_disj_tbl hspace_w hrep0 hinv0 hzero0 htour_rep htour_foot_lt htour_foot_disj_tbl
      htour_foot_disj_blocks htour_foot_disj_spec htour_foot_disj_r hspec_mem hcap_ok
      hedges_nd hedges_eq hE_sub hE_lt hE_fresh hedges_w hassigns_mem hrList_mem hrList_lt
      hrList_pw hrList_sub hcov
  refine ⟨body, hbody, st', c, hEnd, tx', B', hrun, hrep', hB'_headroom, hinv', htr', ?_, hhLo, hhHi, hzf, hc⟩
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hqP
  · refine ⟨hs_lt, B', Function.update_self _ _ _, ?_⟩
    exact ⟨hag.1.trans hLazy.1, hag.2.1.trans hLazy.2.1, hag.2.2.1.trans hLazy.2.2.1,
      fun x hx => (hag.2.2.2 x hx).trans (hLazy.2.2.2 x (hag.2.1 ▸ hx))⟩
  · obtain ⟨hs, B, hSB, hB⟩ := hMatch0 q hqP
    have hne : (⟨slotOf q, hs⟩ : Fin slotCap) ≠ ⟨slotOf qNew, hs_lt⟩ :=
      fun h => hDisjNew q hqP (congrArg Fin.val h)
    exact ⟨hs, B, (hother _ hne).trans hSB, hB⟩

end

end MinCostFlow.SparseCore.Program
