module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEmbModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchSideGapS8
public import MinCostFlow.SparseCore.SplitTrace
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSideInv
import MinCostFlow.SparseCore.Program.CompSplitListCut

import Mathlib.Tactic

/-!
# Phase 4 rotation-cover, spanner count-bank, and side-model step theorems (`AssemblyFirstStepOutEmbRotModel`)

Completes the pure mathematical backbone for Phase 4 and Phase 5:
1. **`T₀` coverage without `c.fDel` endpoints** (`cutVerts_image_root_subset`,
   `asmFirstRotSet_subset_raw`, `asmFirstRotRaw_card_le`): proves that `asmFirstRotSet` is covered
   by `(s.kept, s.fresh)` from `canonSplitList`, `(tl e, hd e)` from `outInsSet`, and
   `cs'.RF.root` on `batchVerts U ∪ ordEditVerts ed`.
2. **Per-slot spanner count-bank bound** (`dsHist_step_counts_add_bank_le`): proves
   `90 * |D| + 90 * |R| + 240 * |UH| + bankAfter ≤ bankBefore + dsBatchCharge` directly from
   `dsStepAmortCost`.
3. **Cumulative split-count extraction** (`batchSplitCount_le_of_branchUpdatesBelow`): extracts
   `batchSplitCount d.flat ≤ y.splitB` from `BranchUpdatesBelow` and `AsmBrSideModel`.
4. **Full post-step `AsmBrSideModel` preservation** (`asmBrSideModel_step`), using the step
   lemmas of the side invariants (`asmFirstInactiveDynInv_step`, `asmFirstActiveBunPartInv_step`,
   `asmFirstActiveDynGraphInv_step`) and `AsmBrModelFacts info.state ord'`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

/-! ## 1. `T₀` coverage from `spPtr`, `insPtr`, `batch`, and `edits` -/

@[expose] public section

/-- Candidate vertex finset for `T₀` computable directly from `spPtr`, `insPtr`, `batch`, and `edits`. -/
noncomputable def asmFirstRotRawSet {L : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit) : Finset ℕ :=
  let cs' := compLSFBatch tr.cs U
  let splits := canonSplitList tr.cs U
  let insS := outInsSet sp tr U ord (applyOrdEdits ord ed)
  (splits.map CompSplitEntry.kept).toFinset ∪ (splits.map CompSplitEntry.fresh).toFinset ∪
    insS.biUnion (fun e => {cs'.RF.root (cs'.G.tail e), cs'.RF.root (cs'.G.head e)}) ∪
    (batchVerts U ∪ ordEditVerts ed).image cs'.RF.root

end

public section

private lemma mem_canonSplitList_fresh_of_sdiff {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (cs : CompLSFState)
    (U : List Update) (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    {r : ℕ} (hr : r ∈ (compLSFBatch cs U).RF.R \ cs.RF.R) :
    r ∈ ((canonSplitList cs U).map CompSplitEntry.fresh).toFinset := by
  set G₀ := coreGraph cs.G cs.lsf
  set UC := canonCoreBatch cs U
  have hG₀_val : G₀.IsValid := coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)
  obtain ⟨hUC_val, hGEq, _⟩ := canonCoreBatch_valid_and_graphEq hI hU
  have hpairs := canonSplitList_eq_coreSplits cs U
  have hAnc := applyBatch_anc_spec G₀ UC hG₀_val hUC_val
  rw [hpairs] at hAnc
  obtain ⟨_, _, _, hAnc_diff, _, _, _, _⟩ := hAnc
  have hr_diff : r ∈ (G₀.applyBatch UC).V \ G₀.V := by
    have h1 : (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).V = (compLSFBatch cs U).RF.R := rfl
    rw [← hGEq.1, h1]; exact hr
  have hmem : r ∈ ((canonSplitList cs U).map fun s => (s.kept, s.fresh)).map Prod.snd :=
    (hAnc_diff r).mp hr_diff
  rw [List.map_map] at hmem
  exact List.mem_toFinset.mpr hmem

private lemma applyBatch_V_sub_local (G : MGraph) (U : List Update) : G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u rest ih =>
    have h1 : G.V ⊆ (G.applyUpdate u).V := by cases u <;> simp [MGraph.applyUpdate]
    exact h1.trans (ih (G.applyUpdate u))

private lemma connected_of_graphEq_local {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) {a b : ℕ}
    (hc : G₁.Connected a b) : G₂.Connected a b :=
  connected_of_subgraph ⟨h.1.le, h.2.1.le, fun e he => h.2.2 e he⟩ hc

private lemma isWalk_of_subgraph_local {G₁ G₂ : MGraph} (hsub : G₂.IsSubgraph G₁)
    {x y : ℕ} {W : List End} (hw : G₁.IsWalk x y W) : G₂.IsWalk x y W := by
  induction hw with
  | nil z => exact MGraph.IsWalk.nil z
  | @cons a b z rest hzE hzsrc _ ih =>
    have hth := hsub.2.2 z.1 hzE
    have hsrc : G₂.src z = a := by
      rw [← hzsrc]; cases z.2 <;> simp [MGraph.src, hth.1, hth.2]
    have hdst : G₂.dst z = G₁.dst z := by
      cases z.2 <;> simp [MGraph.dst, hth.1, hth.2]
    exact MGraph.IsWalk.cons (hsub.2.1 hzE) hsrc (hdst.symm ▸ ih)

private lemma walk_lift_compLSFBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ {U : List Update} {cs : CompLSFState}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      ∀ {x y : ℕ} {W : List End}, x ∈ cs.G.V → y ∈ cs.G.V →
        (compLSFBatch cs U).RF.F.IsWalk x y W → cs.RF.F.IsWalk x y W
  | [], _, _, _, _, _, _, _, _, hw => hw
  | u :: rest, cs, hI, hU, x, y, W, hx, hy, hw => by
    have hI1 := compLSFBatch_inv hI (U := [u]) ⟨hU.1, trivial⟩
    have hG1 : (compLSFStepSingle cs u).G = cs.G.applyUpdate u := rfl
    have hV1 : cs.G.V ⊆ (compLSFStepSingle cs u).G.V := by
      rw [hG1]; cases u <;> simp [MGraph.applyUpdate]
    have hw1 := walk_lift_compLSFBatch hI1 (hG1 ▸ hU.2) (hV1 hx) (hV1 hy) hw
    have hRFa := compLSF_RF_isRSF hI
    have hRFb := compLSF_RF_isRSF hI1
    have hEb := (compLSFBatch_decremental hI (U := [u]) ⟨hU.1, trivial⟩).1
    cases u with
    | insert e' _ _ =>
      refine isWalk_of_subgraph_local ⟨?_, hEb, fun f hf => ?_⟩ hw1
      · rw [hRFb.2.1, hRFa.2.1]; exact Finset.Subset.rfl
      · have hne : f ≠ e' := fun h => hU.1.1 (h ▸ hRFa.2.2.2.2.2.1 (hEb hf))
        have h1 := hRFb.2.2.2.2.2.2 f hf
        have h2 := hRFa.2.2.2.2.2.2 f (hEb hf)
        exact ⟨by rw [h1.1, h2.1]; change (cs.G.applyUpdate (Update.insert e' _ _)).tail f = _; simp [MGraph.applyUpdate, Function.update_of_ne hne],
          by rw [h1.2, h2.2]; change (cs.G.applyUpdate (Update.insert e' _ _)).head f = _; simp [MGraph.applyUpdate, Function.update_of_ne hne]⟩
    | delete _ =>
      refine isWalk_of_subgraph_local ⟨?_, hEb, fun f hf => ?_⟩ hw1
      · rw [hRFb.2.1, hRFa.2.1]; exact Finset.Subset.rfl
      · have h1 := hRFb.2.2.2.2.2.2 f hf
        have h2 := hRFa.2.2.2.2.2.2 f (hEb hf)
        exact ⟨by rw [h1.1, h2.1]; rfl, by rw [h1.2, h2.2]; rfl⟩
    | split v1 v1' St Sh =>
      let P : ℕ → ℕ := fun w => if w = v1' then v1 else w
      have hPx : P x = x := by simp [P, show x ≠ v1' from fun h => hU.1.2.1 (h ▸ hx)]
      have hPy : P y = y := by simp [P, show y ≠ v1' from fun h => hU.1.2.1 (h ▸ hy)]
      have hP : ∀ {x1 y1 : ℕ} {W1 : List End},
          (compLSFStepSingle cs (.split v1 v1' St Sh)).RF.F.IsWalk x1 y1 W1 →
          cs.RF.F.IsWalk (P x1) (P y1) W1 := by
        intro x1 y1 W1 hw'
        induction hw' with
        | nil u1 => exact MGraph.IsWalk.nil (P u1)
        | @cons u1 _ z1 r1 hzE hzsrc _ ih1 =>
          have hz0 := hEb hzE
          have h1 := hRFb.2.2.2.2.2.2 z1.1 hzE
          have h2 := hRFa.2.2.2.2.2.2 z1.1 hz0
          have hPt : P ((compLSFStepSingle cs (.split v1 v1' St Sh)).RF.F.tail z1.1) = cs.RF.F.tail z1.1 := by
            change P ((compLSFBatch cs [.split v1 v1' St Sh]).RF.F.tail z1.1) = _
            rw [h1.1, h2.1]
            change P ((cs.G.applyUpdate (.split v1 v1' St Sh)).tail z1.1) = _
            have hne : cs.G.tail z1.1 ≠ v1' := fun h => hU.1.2.1 (h ▸ (hI.hG_val z1.1 (hRFa.2.2.2.2.2.1 hz0)).1)
            by_cases hst : z1.1 ∈ St ∧ cs.G.tail z1.1 = v1
            · simp [P, MGraph.applyUpdate, hst]
            · simp [P, MGraph.applyUpdate, hst, hne]
          have hPh : P ((compLSFStepSingle cs (.split v1 v1' St Sh)).RF.F.head z1.1) = cs.RF.F.head z1.1 := by
            change P ((compLSFBatch cs [.split v1 v1' St Sh]).RF.F.head z1.1) = _
            rw [h1.2, h2.2]
            change P ((cs.G.applyUpdate (.split v1 v1' St Sh)).head z1.1) = _
            have hne : cs.G.head z1.1 ≠ v1' := fun h => hU.1.2.1 (h ▸ (hI.hG_val z1.1 (hRFa.2.2.2.2.2.1 hz0)).2)
            by_cases hsh : z1.1 ∈ Sh ∧ cs.G.head z1.1 = v1
            · simp [P, MGraph.applyUpdate, hsh]
            · simp [P, MGraph.applyUpdate, hsh, hne]
          have hPsrc : cs.RF.F.src z1 = P u1 := by
            rw [← hzsrc]; cases hz2 : z1.2 <;> simp [MGraph.src, hz2, hPt, hPh]
          have hPdst : P ((compLSFStepSingle cs (.split v1 v1' St Sh)).RF.F.dst z1) = cs.RF.F.dst z1 := by
            cases hz2 : z1.2 <;> simp [MGraph.dst, hz2, hPt, hPh]
          exact MGraph.IsWalk.cons hz0 hPsrc (hPdst ▸ ih1)
      exact hPx ▸ hPy ▸ hP hw1

private lemma releasesSplitEntries_kept_of_root_ne {G : MGraph} {final : RootedForest}
    (hfinal : final.IsRootedSpanningForestOf G) :
    ∀ (cuts : List ℕ) (L : LSF),
      L.F.IsRootedSpanningForestOf G →
      L.F.F.IsSubgraph final.F → L.F.R ⊆ final.R →
      cuts.Nodup → (∀ e ∈ cuts, e ∈ L.F.F.E) →
      (cuts.foldl eraseForestEdge L.F.F).E = final.F.E →
      ∀ w ∈ G.V, final.root w ≠ L.F.root w →
        L.F.root w ∈ ((releasesSplitEntries final.R L cuts).map CompSplitEntry.kept).toFinset
  | [], L, hLF, hsub, hRsub, _, _, hEeq, w, hw, hne => by
    exfalso; apply hne
    have hEqF : GraphEq L.F.F final.F :=
      ⟨hLF.2.1.trans hfinal.2.1.symm, hEeq, fun e he =>
        let ⟨h1, h2⟩ := hsub.2.2 e (hEeq ▸ he); ⟨h1.symm, h2.symm⟩⟩
    have hReq : L.F.R = final.R := by
      refine Finset.Subset.antisymm hRsub fun r hr => ?_
      have hrG : r ∈ G.V := hfinal.2.2.1 hr
      obtain ⟨r', ⟨hr'R, hc'⟩, _⟩ := hLF.2.2.2.1 r hrG
      have hcf : final.F.Connected r r' := connected_of_graphEq_local hEqF hc'
      have h1 := root_eq_of_connected hfinal hrG (hfinal.2.2.1 (hRsub hr'R)) hcf
      rw [root_eq_of_mem_R hfinal hr, root_eq_of_mem_R hfinal (hRsub hr'R)] at h1
      exact h1 ▸ hr'R
    exact (graphEq_root_eq hEqF hReq).symm
  | e :: rest, L, hLF, hsub, hRsub, hnd, hcutsE, hEeq, w, hw, hne => by
    rcases List.nodup_cons.mp hnd with ⟨he_nmem, hnd_r⟩
    have heL : e ∈ L.F.F.E := hcutsE e List.mem_cons_self
    set K := eraseForestEdge L.F.F e
    have hK_for : K.IsForest := isForest_eraseEdge hLF.1 e
    have hKV : K.V = G.V := hLF.2.1
    have hKG : G.IsSubgraph K :=
      ⟨hLF.2.2.2.2.1, (Finset.erase_subset e L.F.F.E).trans hLF.2.2.2.2.2.1,
        fun f hf => hLF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hKsub : K.IsSubgraph final.F := by
      have hEsub : final.F.E ⊆ K.E := by
        rw [← hEeq, List.foldl_cons]
        have hfl : (rest.foldl eraseForestEdge K).E = K.E \ rest.toFinset := by
          simp [foldl_eraseForestEdge]
        rw [hfl]; exact Finset.sdiff_subset
      exact ⟨hsub.1, hEsub, fun f hf => hsub.2.2 f hf⟩
    have hSep : ∀ r ∈ L.F.R, ∀ s ∈ L.F.R, K.Connected r s → r = s := fun r hr s hs hc => by
      have hc0 := connected_of_subgraph (eraseForestEdge_subgraph L.F.F e) hc
      have h1 := root_eq_of_connected hLF (hLF.2.2.1 hr) (hLF.2.2.1 hs) hc0
      rwa [root_eq_of_mem_R hLF hr, root_eq_of_mem_R hLF hs] at h1
    obtain ⟨hOld1, hSub1, hRF1⟩ := canonRoots_spec hK_for hKV hKG hfinal hKsub hRsub hSep
    let L1 : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R final.R⟩, L.wstr⟩
    have hRcard : L1.F.R.card = L.F.R.card + 1 := by
      have hComp := forest_eraseEdge_components_card hLF.1 heL
      change (components K).card = _ at hComp
      rw [← rootedForest_components_card hRF1, ← rootedForest_components_card hLF]
      exact hComp
    obtain ⟨fresh, hfnm, hRins⟩ := roots_insert_of_card hOld1 hRcard
    simp only [releasesSplitEntries, List.map_cons, List.toFinset_cons, Finset.mem_insert]
    rcases eraseForestEdge_root_eq_or_fresh (L := L) (L' := L1) hLF hRF1 rfl heL rfl hRins hfnm hw with hsame | ⟨hkept, _⟩
    · right
      rw [← hsame]
      refine releasesSplitEntries_kept_of_root_ne hfinal rest L1 hRF1 hKsub hSub1 hnd_r
        (fun f hf => Finset.mem_erase.mpr ⟨fun h => he_nmem (h ▸ hf), hcutsE f (List.mem_cons_of_mem _ hf)⟩)
        (by simpa [List.foldl_cons, L1, K] using hEeq) w hw (by rwa [hsame])
    · exact Or.inl hkept

private lemma canonStepSplits_kept_of_root_ne {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u)
    {w : ℕ} (hw : w ∈ cs.G.V) (hne : (compLSFStepSingle cs u).RF.root w ≠ cs.RF.root w) :
    cs.RF.root w ∈ ((canonStepSplits cs u).map CompSplitEntry.kept).toFinset := by
  set cs' := compLSFStepSingle cs u
  have hI' := compLSFBatch_inv hI (U := [u]) ⟨hu, trivial⟩
  have hF0 := compLSF_RF_isRSF hI
  have hF1 := compLSF_RF_isRSF hI'
  have hG1 : cs'.G = cs.G.applyUpdate u := rfl
  have hRsub : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  set K := forestAfterInput cs.RF.F u
  have hFV := hF0.2.1; have hFV' := hF1.2.1
  have hFG := hF0.2.2.2.2.2.1; have hFG' := hF1.2.2.2.2.2.1
  have hFE := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).1
  have hK : K.IsForest := by
    cases u with
    | insert => exact hF0.1
    | delete e => exact isForest_eraseEdge hF0.1 e
    | split v v' St Sh => exact applyUpdate_split_isForest hF0.1 (hFV ▸ hu.1) (hFV ▸ hu.2.1) St Sh
  have hKV : K.V = cs'.RF.F.V := by
    change K.V = (compLSFBatch cs [u]).RF.F.V
    rw [hFV']
    change K.V = cs'.G.V
    rw [hG1]
    cases u with
    | insert => exact hFV
    | delete => exact hFV
    | split v v' St Sh => change insert v' cs.RF.F.V = insert v' cs.G.V; rw [hFV]
  have hKG : cs'.G.IsSubgraph K := by
    rw [hG1]
    cases u with
    | insert e a b =>
      refine ⟨hFV.le, hFG.trans (Finset.subset_insert _ _), fun f hf => ?_⟩
      have hfe : f ≠ e := fun h => hu.1 (h ▸ hFG hf)
      have h0 := hF0.2.2.2.2.2.2 f hf
      exact ⟨by simp [K, forestAfterInput, MGraph.applyUpdate, Function.update_of_ne hfe, h0.1],
        by simp [K, forestAfterInput, MGraph.applyUpdate, Function.update_of_ne hfe, h0.2]⟩
    | delete e =>
      exact ⟨hFV.le, Finset.erase_subset_erase e hFG, fun f hf =>
        hF0.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    | split v v' St Sh =>
      refine ⟨by change insert v' cs.RF.F.V ⊆ insert v' cs.G.V; rw [hFV], hFG, fun f hf => ?_⟩
      have h0 := hF0.2.2.2.2.2.2 f hf
      exact ⟨by simp [K, forestAfterInput, MGraph.applyUpdate, h0.1],
        by simp [K, forestAfterInput, MGraph.applyUpdate, h0.2]⟩
  have hsub : K.IsSubgraph cs'.RF.F := by
    have hKE : cs'.RF.F.E ⊆ K.E := by
      cases u with
      | insert => exact hFE
      | split => exact hFE
      | delete e =>
        intro f hf; refine Finset.mem_erase.mpr ⟨?_, hFE hf⟩
        rintro rfl
        have hfg : f ∈ cs'.G.E := hFG' hf
        rw [hG1] at hfg; simp [MGraph.applyUpdate] at hfg
    refine ⟨hKV.symm.le, hKE, fun f hf => ?_⟩
    have h1 := hKG.2.2 f (hKE hf); have h2 := hF1.2.2.2.2.2.2 f hf
    exact ⟨h2.1.trans h1.1.symm, h2.2.trans h1.2.symm⟩
  set M := inputMid cs u
  have hSep : ∀ r ∈ cs.RF.R, ∀ s ∈ cs.RF.R, K.Connected r s → r = s := fun r hr s hs hc => by
    have hV_r := hF0.2.2.1 hr; have hV_s := hF0.2.2.1 hs
    have hV_r' : r ∈ cs.G.V := hV_r; have hV_s' : s ∈ cs.G.V := hV_s
    cases u with
    | insert _ _ _ =>
      have h1 := root_eq_of_connected hF0 hV_r' hV_s' hc
      rwa [root_eq_of_mem_R hF0 hr, root_eq_of_mem_R hF0 hs] at h1
    | delete e =>
      have hc0 := connected_of_subgraph (eraseForestEdge_subgraph cs.RF.F e) hc
      have h1 := root_eq_of_connected hF0 hV_r' hV_s' hc0
      rwa [root_eq_of_mem_R hF0 hr, root_eq_of_mem_R hF0 hs] at h1
    | split v v' St Sh =>
      obtain ⟨W, hW⟩ := hc
      let P : ℕ → ℕ := fun z => if z = v' then v else z
      have hPr : P r = r := by simp [P, show r ≠ v' from fun h => hu.2.1 (h ▸ hV_r')]
      have hPs : P s = s := by simp [P, show s ≠ v' from fun h => hu.2.1 (h ▸ hV_s')]
      have hP : ∀ {x y : ℕ} {W1 : List End}, K.IsWalk x y W1 → cs.RF.F.IsWalk (P x) (P y) W1 := by
        intro x y W1 hw'; induction hw' with
        | nil z => exact MGraph.IsWalk.nil (P z)
        | @cons x0 _ z1 _ hzE hzsrc _ ih =>
          have hPt : P (K.tail z1.1) = cs.RF.F.tail z1.1 := by
            have hne : cs.RF.F.tail z1.1 ≠ v' := fun h => hu.2.1 (h ▸ hF0.2.1 ▸ (hF0.1.1 z1.1 hzE).1)
            by_cases h1 : z1.1 ∈ St ∧ cs.RF.F.tail z1.1 = v
            · simp [P, K, forestAfterInput, MGraph.applyUpdate, h1]
            · simp [P, K, forestAfterInput, MGraph.applyUpdate, h1, hne]
          have hPh : P (K.head z1.1) = cs.RF.F.head z1.1 := by
            have hne : cs.RF.F.head z1.1 ≠ v' := fun h => hu.2.1 (h ▸ hF0.2.1 ▸ (hF0.1.1 z1.1 hzE).2)
            by_cases h1 : z1.1 ∈ Sh ∧ cs.RF.F.head z1.1 = v
            · simp [P, K, forestAfterInput, MGraph.applyUpdate, h1]
            · simp [P, K, forestAfterInput, MGraph.applyUpdate, h1, hne]
          have hPsrc : cs.RF.F.src z1 = P x0 := by
            rw [← hzsrc]; cases hz2 : z1.2 <;> simp [MGraph.src, hz2, hPt, hPh]
          have hPdst : P (K.dst z1) = cs.RF.F.dst z1 := by
            cases hz2 : z1.2 <;> simp [MGraph.dst, hz2, hPt, hPh]
          exact MGraph.IsWalk.cons hzE hPsrc (hPdst ▸ ih)
      have h1 := root_eq_of_connected hF0 hV_r' hV_s' ⟨W, hPr ▸ hPs ▸ hP hW⟩
      rwa [root_eq_of_mem_R hF0 hr, root_eq_of_mem_R hF0 hs] at h1
  obtain ⟨hOldM, hSubM, hRFM⟩ := canonRoots_spec hK (hKV.trans hF1.2.1) hKG hF1 hsub hRsub hSep
  have hMF_F : M.F.F = K := by
    cases u with
    | insert _ _ _ => rfl
    | delete e =>
      by_cases he : e ∈ cs.RF.F.E
      · simp [M, inputMid, K, forestAfterInput, he]
      · simp only [M, inputMid, K, forestAfterInput, he]
        change cs.RF.F = eraseForestEdge cs.RF.F e
        cases hF : cs.RF.F; simp [eraseForestEdge, Finset.erase_eq_of_notMem (hF ▸ he)]
    | split _ _ _ _ => rfl
  have hMF_RF : M.F.IsRootedSpanningForestOf cs'.G := by
    have hRFM_cs' : RootedForest.IsRootedSpanningForestOf
        { F := K, R := canonRoots K cs.RF.R cs'.RF.R } cs'.G := hRFM
    cases u with
    | insert e0 u0 v0 =>
      have hVeq : cs'.G.V = cs.G.V := by rw [hG1]; rfl
      refine ⟨hF0.1, hF0.2.1.trans hVeq.symm, fun r hr => hVeq.symm ▸ hF0.2.2.1 hr,
        fun v hv => hF0.2.2.2.1 v (hVeq ▸ hv), hVeq.symm ▸ hF0.2.2.2.2.1, ?_, ?_⟩
      · intro e he; rw [hG1]; exact Finset.mem_insert_of_mem (hF0.2.2.2.2.2.1 he)
      · intro e he
        have heG := hF0.2.2.2.2.2.1 he
        have hne : e ≠ e0 := fun h => hu.1 (h ▸ heG)
        have hth := hF0.2.2.2.2.2.2 e he
        rw [hG1]; simp only [MGraph.applyUpdate, Function.update_of_ne hne]; exact hth
    | delete e =>
      by_cases he : e ∈ cs.RF.F.E
      · simpa [M, inputMid, K, forestAfterInput, cs', he] using hRFM_cs'
      · have hVeq : cs'.G.V = cs.G.V := by rw [hG1]; rfl
        have hMF0 : M.F = cs.RF := by simp [M, inputMid, he]; rfl
        rw [hMF0]
        refine ⟨hF0.1, hF0.2.1.trans hVeq.symm, fun r hr => hVeq.symm ▸ hF0.2.2.1 hr,
          fun v hv => hF0.2.2.2.1 v (hVeq ▸ hv), hVeq.symm ▸ hF0.2.2.2.2.1, ?_, ?_⟩
        · intro e' he'; rw [hG1]; exact Finset.mem_erase.mpr ⟨fun h => he (h ▸ he'), hF0.2.2.2.2.2.1 he'⟩
        · intro e' he'; rw [hG1]; exact hF0.2.2.2.2.2.2 e' he'
    | split _ _ _ _ => simpa [M, inputMid, K, forestAfterInput, cs'] using hRFM_cs'
  have hMF_subR : M.F.R ⊆ cs'.RF.R := by
    have hSubM_cs' : canonRoots K cs.RF.R cs'.RF.R ⊆ cs'.RF.R := hSubM
    cases u with
    | insert _ _ _ => exact hRsub
    | delete e =>
      by_cases he : e ∈ cs.RF.F.E
      · simpa [M, inputMid, K, forestAfterInput, cs', he] using hSubM_cs'
      · simp [M, inputMid, he]; exact hRsub
    | split _ _ _ _ => simpa [M, inputMid, K, forestAfterInput, cs'] using hSubM_cs'
  have hw' : w ∈ cs'.G.V := by rw [hG1]; cases u <;> simp [MGraph.applyUpdate, hw]
  simp only [canonStepSplits, List.map_append, List.toFinset_append, Finset.mem_union]
  by_cases hM : M.F.root w = cs.RF.root w
  · right; rw [← hM]
    set cuts := (K.E \ cs'.RF.F.E).sort (· ≤ ·)
    have hEeq : (cuts.foldl eraseForestEdge M.F.F).E = cs'.RF.F.E := by
      rw [hMF_F]
      simp only [cuts, foldl_eraseForestEdge, Finset.sort_toFinset]
      exact Finset.sdiff_sdiff_eq_self hsub.2.1
    exact releasesSplitEntries_kept_of_root_ne hF1 cuts M hMF_RF (hMF_F ▸ hsub) hMF_subR
      (Finset.sort_nodup _ _) (fun e he => hMF_F ▸ (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp he)).1)
      hEeq w hw' (by rwa [hM])
  · left
    cases u with
    | insert e0 u0 v0 =>
      exact absurd rfl hM
    | delete e =>
      by_cases heF : e ∈ cs.RF.F.E
      · have hMF : M.F = ⟨K, canonRoots K cs.RF.R cs'.RF.R⟩ := by
          simp [M, inputMid, K, forestAfterInput, cs', heF]
        have hRcard : (canonRoots K cs.RF.R cs'.RF.R).card = cs.RF.R.card + 1 := by
          have hComp : (components K).card = (components cs.RF.F).card + 1 :=
            forest_eraseEdge_components_card hF0.1 heF
          have h1 : (components K).card = (canonRoots K cs.RF.R cs'.RF.R).card :=
            rootedForest_components_card hRFM
          have h2 : (components cs.RF.F).card = cs.RF.R.card :=
            rootedForest_components_card hF0
          omega
        obtain ⟨fresh, hfnm, hRins⟩ := roots_insert_of_card hOldM hRcard
        have hRFM' : M.F.IsRootedSpanningForestOf cs'.G := hMF ▸ hRFM
        have hMF_F' : M.F.F = eraseForestEdge cs.RF.F e := by simp [hMF, K, forestAfterInput]
        have hMF_R : M.F.R = insert fresh cs.RF.R := by rw [hMF]; exact hRins
        rcases eraseForestEdge_root_eq_or_fresh (L := cs.lsf) (L' := M) hF0 hRFM' rfl heF hMF_F' hMF_R hfnm hw with
          hsame | ⟨hkept, _⟩
        · exact absurd hsame hM
        · simp [inputSplitEntries, heF]; exact hkept
      · exact absurd (by simp [M, inputMid, heF]; rfl) hM
    | split v v' St Sh =>
      have hMF : M.F = ⟨K, canonRoots K cs.RF.R cs'.RF.R⟩ := by
        simp [M, inputMid, K, forestAfterInput, cs']
      have hRcard : (canonRoots K cs.RF.R cs'.RF.R).card = cs.RF.R.card + 1 := by
        have ho := rootedForest_R_add_edges hF0
        have hn := rootedForest_R_add_edges hRFM
        have hv : (cs.G.applyUpdate (.split v v' St Sh)).V.card = cs.G.V.card + 1 :=
          Finset.card_insert_of_notMem hu.2.1
        change (canonRoots K cs.RF.R cs'.RF.R).card + cs.RF.F.E.card =
          (cs.G.applyUpdate (.split v v' St Sh)).V.card at hn
        omega
      obtain ⟨fresh, hfnm, hRins⟩ := roots_insert_of_card hOldM hRcard
      have hRFM' : M.F.IsRootedSpanningForestOf cs'.G := hMF ▸ hRFM
      have hMF_F : M.F.F = cs.RF.F.applyUpdate (.split v v' St Sh) := by simp [hMF, K, forestAfterInput]
      have hMF_R : M.F.R = insert fresh cs.RF.R := by rw [hMF]; exact hRins
      rcases applySplit_root_eq_or_fresh (L := cs.lsf) (L' := M) hF0 hRFM' hMF_F hMF_R hfnm hu hw (Or.inl rfl) with
        hsame | ⟨hkept, _⟩
      · exact absurd hsame hM
      · simp [inputSplitEntries]; exact hkept

/-- Every forest edge removed during `compLSFBatch cs U` has both endpoints' final roots among
the `kept` and `fresh` roots of `canonSplitList cs U`. -/
theorem cutVerts_image_root_subset {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (cs : CompLSFState) (U : List Update)
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    (cutVerts cs U).image (compLSFBatch cs U).RF.root ⊆
      ((canonSplitList cs U).map CompSplitEntry.kept).toFinset ∪
        ((canonSplitList cs U).map CompSplitEntry.fresh).toFinset := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨e, he, hv_end⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨heF0, hneF'⟩ := Finset.mem_sdiff.mp he
  have hI' := compLSFBatch_inv hI hU
  have hRF0 := compLSF_RF_isRSF hI
  have hRF' := compLSF_RF_isRSF hI'
  have hV_e := hI.hG_val e (hRF0.2.2.2.2.2.1 heF0)
  have hvV : v ∈ cs.G.V := by
    rcases Finset.mem_insert.mp hv_end with rfl | h'
    · exact hV_e.1
    · rw [Finset.mem_singleton.mp h']; exact hV_e.2
  have hvV' : v ∈ (compLSFBatch cs U).G.V := compLSFBatch_G cs U ▸ applyBatch_V_sub_local cs.G U hvV
  by_cases hr0 : (compLSFBatch cs U).RF.root v ∈ cs.RF.R
  · apply Finset.mem_union_left
    have haV' : cs.G.tail e ∈ (compLSFBatch cs U).G.V := compLSFBatch_G cs U ▸ applyBatch_V_sub_local cs.G U hV_e.1
    have hbV' : cs.G.head e ∈ (compLSFBatch cs U).G.V := compLSFBatch_G cs U ▸ applyBatch_V_sub_local cs.G U hV_e.2
    have hFt := (hRF0.2.2.2.2.2.2 e heF0).1
    have hFh := (hRF0.2.2.2.2.2.2 e heF0).2
    have hr_v_eq : (compLSFBatch cs U).RF.root v = cs.RF.root v := by
      have ⟨W, hW⟩ := (root_mem_R hRF' hvV').2
      have h1 := root_eq_of_connected hRF0 hvV (hRF0.2.2.1 hr0)
        ⟨W, walk_lift_compLSFBatch hI hU hvV (hRF0.2.2.1 hr0) hW⟩
      rw [root_eq_of_mem_R hRF0 hr0] at h1; exact h1.symm
    have hr_ab : cs.RF.root (cs.G.tail e) = cs.RF.root (cs.G.head e) :=
      root_eq_of_connected hRF0 hV_e.1 hV_e.2
        ⟨[(e, true)], .cons (x := (e, true)) heF0 hFt (hFh ▸ .nil _)⟩
    have hr_eq_a : (compLSFBatch cs U).RF.root v = cs.RF.root (cs.G.tail e) := by
      rw [hr_v_eq]; rcases Finset.mem_insert.mp hv_end with rfl | h'
      · rfl
      · rw [Finset.mem_singleton.mp h']; exact hr_ab.symm
    have hne_fin : (compLSFBatch cs U).RF.root (cs.G.tail e) ≠ (compLSFBatch cs U).RF.root (cs.G.head e) := by
      intro heq
      obtain ⟨W, hW⟩ := connected_trans (root_mem_R hRF' haV').2 (heq ▸ connected_symm (root_mem_R hRF' hbV').2)
      have hW_ne : ∀ x ∈ W, x.1 ≠ e := by
        intro x hx hxe
        have hxE : ∀ {u1 u2 : ℕ} {P : List (ℕ × Bool)},
            (compLSFBatch cs U).RF.F.IsWalk u1 u2 P → ∀ y ∈ P, y.1 ∈ (compLSFBatch cs U).RF.F.E := by
          intro u1 u2 P hP
          induction hP with
          | nil _ => intro _ hy; cases hy
          | cons heP _ _ ih =>
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact heP
            · exact ih y hy'
        exact hneF' (hxe ▸ hxE hW x hx)
      have hW0 := walk_lift_compLSFBatch hI hU hV_e.1 hV_e.2 hW
      have hW_e : (eraseForestEdge cs.RF.F e).IsWalk (cs.RF.F.src (e, true)) (cs.RF.F.dst (e, true)) W := by
        change (eraseForestEdge cs.RF.F e).IsWalk (cs.RF.F.tail e) (cs.RF.F.head e) W
        rw [hFt, hFh]
        exact isWalk_eraseForestEdge_of_notMem hW0 hW_ne
      exact (not_connected_eraseForestEdge hRF0.1 (x := (e, true)) heF0) ⟨W, hW_e⟩
    obtain ⟨w, hwV, hrw0, hrw_ne⟩ : ∃ w ∈ cs.G.V, cs.RF.root w = (compLSFBatch cs U).RF.root v ∧
        (compLSFBatch cs U).RF.root w ≠ cs.RF.root w := by
      by_cases ha : (compLSFBatch cs U).RF.root (cs.G.tail e) = (compLSFBatch cs U).RF.root v
      · exact ⟨cs.G.head e, hV_e.2, hr_ab.symm.trans hr_eq_a.symm,
          fun h => hne_fin (ha.trans (hr_eq_a.trans (hr_ab.trans h.symm)))⟩
      · exact ⟨cs.G.tail e, hV_e.1, hr_eq_a.symm, fun h => ha (h.trans hr_eq_a.symm)⟩
    have hkept_ind : ∀ (U' : List Update) (cs0 : CompLSFState),
        CompLSFInv C_lsst ℓ₀ cs0 → cs0.G.BatchIsValid U' →
        ∀ w0 ∈ cs0.G.V, (compLSFBatch cs0 U').RF.root w0 ≠ cs0.RF.root w0 →
          cs0.RF.root w0 ∈ ((canonSplitList cs0 U').map CompSplitEntry.kept).toFinset := by
      intro U'; induction U' with
      | nil => intro _ _ _ _ _ h; exact absurd rfl h
      | cons u0 r0 ih0 =>
        intro cs0 hI0 hU0 w0 hw0 hne0
        have hI1 := compLSFBatch_inv hI0 (U := [u0]) ⟨hU0.1, trivial⟩
        have hG1 : (compLSFStepSingle cs0 u0).G = cs0.G.applyUpdate u0 := rfl
        have hw1 : w0 ∈ (compLSFStepSingle cs0 u0).G.V := by rw [hG1]; cases u0 <;> simp [MGraph.applyUpdate, hw0]
        simp only [canonSplitList, List.map_append, List.toFinset_append, Finset.mem_union]
        by_cases hstep : (compLSFStepSingle cs0 u0).RF.root w0 = cs0.RF.root w0
        · right; rw [← hstep]
          exact ih0 (compLSFStepSingle cs0 u0) hI1 (hG1 ▸ hU0.2) w0 hw1
            (by change (compLSFBatch cs0 (u0 :: r0)).RF.root w0 ≠ (compLSFStepSingle cs0 u0).RF.root w0; rwa [hstep])
        · left; exact canonStepSplits_kept_of_root_ne hI0 hU0.1 hw0 hstep
    rw [← hrw0]; exact hkept_ind U cs hI hU w hwV hrw_ne
  · apply Finset.mem_union_right
    exact mem_canonSplitList_fresh_of_sdiff cs U hI hU
      (Finset.mem_sdiff.mpr ⟨(root_mem_R hRF' hvV').1, hr0⟩)

private lemma ordEditVerts_outPrefixEdits_sub : ∀ (P : List Update),
    ordEditVerts (outPrefixEdits P) ⊆ batchVerts P
  | [] => Finset.Subset.refl _
  | u :: rest => by
    have ih := ordEditVerts_outPrefixEdits_sub rest
    cases u with
    | insert _ _ _ => exact ih.trans Finset.subset_union_right
    | delete _ => simp only [outPrefixEdits, ordEditVerts, OrdEdit.verts, Finset.empty_union, batchVerts, updVerts]; exact ih
    | split v v' _ _ =>
      simp only [outPrefixEdits, ordEditVerts, OrdEdit.verts, batchVerts, updVerts]
      exact Finset.union_subset_union_right ih

private lemma ordEditVerts_outInsertEdits_sub (t : ℕ → List End) (G : MGraph) :
    ∀ (I : List Update),
      (∀ e a b, Update.insert e a b ∈ I → G.tail e = a ∧ G.head e = b) →
      ordEditVerts (outInsertEdits t G.src I) ⊆ batchVerts I
  | [], _ => Finset.Subset.refl _
  | u :: rest, hI => by
    have ih := ordEditVerts_outInsertEdits_sub t G rest (fun e a b h => hI e a b (List.mem_cons_of_mem _ h))
    cases u with
    | insert e a b =>
      obtain ⟨ht, hh⟩ := hI e a b List.mem_cons_self
      simp only [outInsertEdits, ordEditVerts, OrdEdit.verts, batchVerts, updVerts, MGraph.src, ht, hh]
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | rfl | hr
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (ih hr)
    | delete _ => exact ih.trans Finset.subset_union_right
    | split _ _ _ _ => exact ih.trans Finset.subset_union_right

private lemma batchVerts_restrictSplits_sub (keep : Finset ℕ) (U : List Update) :
    batchVerts (restrictSplits keep U) ⊆
      ((coreBatchSplitPairs U).map Prod.fst).toFinset ∪ ((coreBatchSplitPairs U).map Prod.snd).toFinset := by
  induction U with
  | nil => simp [restrictSplits, batchVerts]
  | cons u rest ih =>
    cases u with
    | insert _ _ _ => exact ih
    | delete _ => exact ih
    | split v v' _ _ =>
      simp only [restrictSplits, batchVerts, updVerts, coreBatchSplitPairs, List.filterMap_cons,
        List.map_cons, List.toFinset_cons]
      intro x hx
      rcases Finset.mem_union.mp hx with hvv | hr
      · rcases Finset.mem_insert.mp hvv with rfl | h'
        · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · rw [Finset.mem_singleton.mp h']; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · rcases Finset.mem_union.mp (ih hr) with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h1)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h2)

/-- **`T₀` coverage theorem**: `asmFirstRotSet` is contained in `asmFirstRotRawSet`, which needs
only `canonSplitList`, `outInsSet` endpoints, and `rootOf` on `batchVerts U ∪ ordEditVerts ed`. -/
theorem asmFirstRotSet_subset_raw {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hScur_ends : ∀ e ∈ outInsSet sp tr U ord (applyOrdEdits ord ed),
      (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state.S_cur.tail e =
        (compLSFBatch tr.cs U).RF.root ((compLSFBatch tr.cs U).G.tail e) ∧
      (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state.S_cur.head e =
        (compLSFBatch tr.cs U).RF.root ((compLSFBatch tr.cs U).G.head e)) :
    asmFirstRotSet sp tr U ord ed ⊆ asmFirstRotRawSet sp tr U ord ed := by
  set ord' := applyOrdEdits ord ed
  set info := stepBundleTree sp tr U ord ord'
  set cs' := compLSFBatch tr.cs U
  have hUC : info.U_core = canonCoreBatch tr.cs U := by rw [← coreBatchOf_eq tr.cs ord ord' U]; rfl
  have hUS_sub : batchVerts info.U_S ⊆
      ((canonSplitList tr.cs U).map CompSplitEntry.kept).toFinset ∪
        ((canonSplitList tr.cs U).map CompSplitEntry.fresh).toFinset ∪
        (outInsSet sp tr U ord ord').biUnion (fun e => {cs'.RF.root (cs'.G.tail e), cs'.RF.root (cs'.G.head e)}) := by
    have hbv_app : ∀ A B : List Update, batchVerts (A ++ B) = batchVerts A ∪ batchVerts B := by
      intro A B; induction A with
      | nil => simp [batchVerts]
      | cons a as ih => simp [batchVerts, ih, Finset.union_assoc]
    have hbv_del : ∀ L : List ℕ, batchVerts (L.map Update.delete) = ∅ := by
      intro L; induction L with
      | nil => rfl
      | cons e es ih => simp [batchVerts, updVerts, ih]
    have hbv_ins : ∀ L : List ℕ,
        batchVerts (L.map fun e => Update.insert e (cs'.RF.root (cs'.G.tail e)) (cs'.RF.root (cs'.G.head e))) =
          L.toFinset.biUnion fun e => {cs'.RF.root (cs'.G.tail e), cs'.RF.root (cs'.G.head e)} := by
      intro L; induction L with
      | nil => simp [batchVerts]
      | cons e es ih => simp [batchVerts, updVerts, ih]
    rw [stepBundleTree_U_S_split, outPrefixBatch, hbv_app, hbv_app, hbv_del, Finset.empty_union,
      outInsBatch]
    change batchVerts (restrictSplits (outKeep sp tr U ord ord') info.U_core) ∪
      batchVerts ((outInsList sp tr U ord ord').map fun e =>
        Update.insert e (cs'.RF.root (cs'.G.tail e)) (cs'.RF.root (cs'.G.head e))) ⊆ _
    rw [hbv_ins, outInsList, Finset.sort_toFinset]
    refine Finset.union_subset_union_left ?_
    rw [hUC]
    have h1 := batchVerts_restrictSplits_sub (outKeep sp tr U ord ord') (canonCoreBatch tr.cs U)
    rw [canonSplitList_eq_coreSplits, List.map_map, List.map_map] at h1
    exact h1
  have hBase_sub : ordEditVerts (outBaseEdits sp tr U ord ord') ⊆ batchVerts info.U_S := by
    rw [outBaseEdits, ordEditVerts_append, stepBundleTree_U_S_split]
    have hbv_app : ∀ A B : List Update, batchVerts (A ++ B) = batchVerts A ∪ batchVerts B := by
      intro A B; induction A with
      | nil => simp [batchVerts]
      | cons a as ih => simp [batchVerts, ih, Finset.union_assoc]
    rw [hbv_app]
    refine Finset.union_subset_union (ordEditVerts_outPrefixEdits_sub _)
      (ordEditVerts_outInsertEdits_sub _ _ _ fun e a b hm => ?_)
    rw [outInsBatch, List.mem_map] at hm
    obtain ⟨e0, he0, heq⟩ := hm; cases heq
    exact hScur_ends e ((Finset.mem_sort (· ≤ ·)).mp he0)
  have hT_sub : (asmFirstTouched tr.cs U ed).image cs'.RF.root ⊆ asmFirstRotRawSet sp tr U ord ed := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    simp only [asmFirstTouched, Finset.mem_union] at hv
    rcases hv with (hvU | hvC) | hvE
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hvU))
    · have hcut := cutVerts_image_root_subset tr.cs U hI hU (Finset.mem_image_of_mem _ hvC)
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hcut)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_right _ hvE))
  intro r hr
  simp only [asmFirstRotSet, Finset.mem_union] at hr
  rcases hr with (h1 | h2) | h3
  · exact Finset.mem_union_left _ (hUS_sub (hBase_sub h1))
  · exact Finset.mem_union_left _ (hUS_sub h2)
  · exact hT_sub h3

/-! ## 2. Per-slot spanner count-bank bound and split-count extraction -/

/-- Along any run slice, `90 * |D| + 90 * |R| + 240 * |UH|` for a batch `U` is bounded by the
sum of `dsStepAmortCost` over the steps of `U`. -/
theorem dsHist_step_counts_add_bank_le (P : DSParams) (s : DSHist) (U : List Update)
    (hVG₀ : s.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : s.G₀.m ≤ P.mMax)
    (hBV : s.G₀.BatchIsValid (s.flat ++ U)) (hds : ∀ u ∈ s.flat ++ U, isDelOrSplit u)
    (hsplit : batchSplitCount (s.flat ++ U) ≤ P.splitBound)
    (hp : 1 ≤ max P.impl.p_s P.impl.p_t) :
    let out := DynSpanner.update (s.state P) U (canonicalSparsify P.impl)
    let R := updateReembSet (s.state P) U (canonicalSparsify P.impl)
    90 * out.D.card + 90 * R.card + 240 * out.UH.length +
      (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).bank P ≤
      s.bank P + dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀
        (s.G₀.applyBatch s.flat) U := by
  intro out R
  have hmatch : ∀ (i : ℕ) (hi : i < U.length),
      (s.flat ++ U)[s.flat.length + i]? = some (U[i]'hi) := by
    intro i hi
    simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hi
  have hst : s.state P = runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) s.flat.length := by
    rw [runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl]; rfl
  have hgo := updateGo_run_eq (L := P.L) (q := s.q P) (sparsify := canonicalSparsify P.impl)
    s.G₀ (s.flat ++ U) U s.flat.length [] ∅ 0 (by simp) hmatch
  have hre := updateReembSet_run_eq (L := P.L) (q := s.q P) (sparsify := canonicalSparsify P.impl)
    s.G₀ (s.flat ++ U) U s.flat.length hmatch
  have hD_le : out.D.card ≤ ∑ i ∈ Finset.range U.length,
      (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).D.card := by
    dsimp only [out, DynSpanner.update]
    rw [hst, hgo]
    refine (Finset.card_le_card (Finset.inter_subset_left.trans (by simp))).trans (Finset.card_biUnion_le)
  have hR_le : R.card ≤ ∑ i ∈ Finset.range U.length,
      (runStepReembSet (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).card := by
    dsimp only [R]; rw [hst, hre]
    exact (Finset.card_le_card Finset.inter_subset_left).trans Finset.card_biUnion_le
  have hUH_eq : out.UH.length = ∑ i ∈ Finset.range U.length,
      (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).UH.length := by
    dsimp only [out, DynSpanner.update]
    rw [hst, hgo]
    simp only [List.nil_append, List.length_flatMap]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have hcnt : 90 * out.D.card + 90 * R.card + 240 * out.UH.length ≤
      ∑ i ∈ Finset.range U.length, dsStepAmortCost s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap
        (s.flat ++ U) (s.flat.length + i) := by
    calc 90 * out.D.card + 90 * R.card + 240 * out.UH.length
        ≤ 90 * (∑ i ∈ Finset.range U.length,
            (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).D.card) +
          90 * (∑ i ∈ Finset.range U.length,
            (runStepReembSet (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).card) +
          240 * (∑ i ∈ Finset.range U.length,
            (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).UH.length) := by
          omega
      _ = ∑ i ∈ Finset.range U.length,
            (90 * (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).D.card +
             90 * (runStepReembSet (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).card +
             240 * (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U) (s.flat.length + i)).UH.length) := by
          simp only [Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ ∑ i ∈ Finset.range U.length, dsStepAmortCost s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap
            (s.flat ++ U) (s.flat.length + i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have ham := dsStepAmortCost_eq s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U) (s.flat.length + i)
          omega
  have hsp := dsSpent_append P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat U
  have hflat : (s.Us ++ [U]).flatten = s.flat ++ U := dsHist_flat_append s U
  have hle := dsSpent_le_bankTotal (vCap := P.vCap) (eCap := P.eCap) (nMax := s.G₀.n + P.splitBound)
    P.impl (Us := s.Us ++ [U]) hVG₀ hL hGm₀ (by rw [hflat]; exact hBV) (by rw [hflat]; exact hds)
    (by rw [hflat]; exact Nat.add_le_add_left hsplit _) hp
  have htot := dsBankTotal_append P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ s.Us U
  simp only [DSHist.bank, dsBank]
  have hq' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).q P = s.q P := rfl
  rw [hq', hflat]; rw [hflat] at hle
  change _ + _ + _ + (dsBankTotal P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ (s.Us ++ [U]) -
      dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ (s.flat ++ U)) ≤
    (dsBankTotal P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ s.Us -
      dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat) + _
  have hq'' : s.q P = phaseBase (s.G₀.n + P.splitBound) P.L := rfl
  rw [hq''] at hcnt hsp htot ⊢
  rw [show s.Us.flatten = s.flat from rfl] at htot
  dsimp only [out, R] at hcnt ⊢
  omega

/-- Extracts `batchSplitCount d.flat ≤ tr.splitBound` from `BranchUpdatesBelow` and `AsmBrSideModel`. -/
theorem batchSplitCount_le_of_branchUpdatesBelow {P : DSParams} {tr : BundleTreeState P.L} {n : ℕ}
    (hBUB : BranchUpdatesBelow P.impl tr n) {q : Finset ℕ × ℤ} {d : DSHist}
    (hC : q.1 ∈ components tr.cs.G₀) (hL : 1 ≤ P.L) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hG₀ : d.G₀ = tr.initBunG q) (hst : d.state P = tr.dyn q)
    (hds : ∀ u ∈ d.flat, isDelOrSplit u) (hBV : d.G₀.BatchIsValid d.flat) :
    batchSplitCount d.flat ≤ tr.splitBound := by
  rcases q with ⟨C, b⟩
  obtain ⟨hVG₀, _, _, _, _, hDiff, _, _, _, _⟩ := hBUB.2 C hC b
  rw [← hG₀] at hVG₀ hDiff
  have hq : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hGeq : (tr.dyn (C, b)).G = d.G₀.applyBatch d.flat := by
    rw [← hst]
    have hI := (runInv_all hVG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
      hBV hds d.flat.length le_rfl).1.G_eq
    simpa [DSHist.state, List.take_length] using hI
  have hn := n_applyBatch_of_delOrSplit d.flat d.G₀ hBV hds
  rw [← hGeq] at hn
  omega

end

end MinCostFlow.SparseCore.Program
