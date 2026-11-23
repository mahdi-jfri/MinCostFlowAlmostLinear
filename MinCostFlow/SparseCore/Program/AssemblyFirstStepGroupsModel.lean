module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepBunPrepProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepProof

/-!
# Split-group model specification and `BundleStepReady` bridge (`AssemblyFirstStepGroupsModel`)

Connects `splitGroupsOf ((canonSplitList tr.cs U).map fun s => (s.kept, s.fresh))` and
`splitOldRoots ...` (`AssemblyFirstStepBunPrepProg.lean`) directly to ALL split-group and
root-partition preconditions of `bunTableHeadroom_step_model_runs_on` (`BundleCapHeadroomStep.lean`),
and provides `bundleStepReady_of_active_slot`.

Main results:
1. `splitGroups_model_spec`: proves `hgs_pos`, `hgs_lt`, `hgs_nd`, `hgs_sub`, `hgs_disj`,
   `hold_len`, `hold_nd`, `hold_sub`, `hgroup_sum_le`, `hrest_le`, `hbundle_in_group`,
   `totalAdded ≤ 2 * (U.length + (canonSplitList tr.cs U).length)`,
   `groupsTotalLen gs ≤ 2 * (canonSplitList tr.cs U).length`, and
   `groupsWords gs ≤ 3 * (canonSplitList tr.cs U).length`.
2. `bundleStepReady_of_active_slot`: proves `BundleStepReady tr.cs B₀ tr.k ord ord' U` for every
   active slot `S₀ j = some B₀` under `SlotMapOK`, `BunTableMatches`, `RestartScurModelInv`,
   `CompLSFInv`, and `OrderedBatch`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Pure helpers -/

private lemma coreGraph_V_eq (cs : CompLSFState) : (coreGraph cs.G cs.lsf).V = cs.RF.R := rfl

private lemma updateEdgeOpt_card_le (U : List Update) :
    (U.filterMap fun
      | .insert e _ _ => some e
      | .delete e => some e
      | .split _ _ _ _ => none).toFinset.card ≤ U.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

private lemma newCoreEdges_subset {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (cs : CompLSFState) (U : List Update)
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    let cs' := compLSFBatch cs U
    let G₀ := coreGraph cs.G cs.lsf
    let G' := coreGraph cs'.G cs'.lsf
    G'.E \ (G₀.E \ batchDeletes U) ⊆
      (U.filterMap fun
        | .insert e _ _ => some e
        | .delete e => some e
        | .split _ _ _ _ => none).toFinset ∪
      ((canonSplitList cs U).map CompSplitEntry.edge).toFinset := by
  induction U generalizing cs with
  | nil =>
    dsimp only [compLSFBatch]
    intro e he
    simp [batchDeletes] at he
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hU
    have hI1 := compLSFInv_step hI hu
    set cs1 := compLSFStepSingle cs u
    set cs' := compLSFBatch cs1 rest
    have hcs'_eq : compLSFBatch cs (u :: rest) = cs' := rfl
    have hih := ih cs1 hI1 hrest
    dsimp only
    intro e he
    rw [hcs'_eq, Finset.mem_sdiff, Finset.mem_sdiff, not_and, not_not] at he
    obtain ⟨heG', hnot⟩ := he
    -- Check if `e ∈ (coreGraph cs1.G cs1.lsf).E \ batchDeletes rest`
    by_cases h1 : e ∈ (coreGraph cs1.G cs1.lsf).E \ batchDeletes rest
    · rw [Finset.mem_sdiff] at h1
      by_cases he0 : e ∈ (coreGraph cs.G cs.lsf).E
      · have hdel : e ∈ batchDeletes (u :: rest) := hnot he0
        obtain ⟨w, hw, rfl⟩ := (mem_batchDeletes_iff _ _).mp hdel
        rcases List.mem_cons.mp hw with rfl | hw_rest
        · exact Finset.mem_union_left _ (List.mem_toFinset.mpr (by simp))
        · exact absurd ((mem_batchDeletes_iff _ _).mpr ⟨.delete e, hw_rest, rfl⟩) h1.2
      · -- `e ∈ (coreGraph cs1.G cs1.lsf).E \ (coreGraph cs.G cs.lsf).E`
        have he_cs1G : e ∈ cs1.G.E := (Finset.mem_sdiff.mp h1.1).1
        have he_notF1 : e ∉ cs1.RF.F.E := (Finset.mem_sdiff.mp h1.1).2
        have hG1_eq : cs1.G = cs.G.applyUpdate u := by
          simpa [cs1, compLSFBatch, MGraph.applyBatch] using compLSFBatch_G cs [u]
        rw [hG1_eq] at he_cs1G
        by_cases heG0 : e ∈ cs.G.E
        · -- `e ∈ cs.G.E` and `e ∉ coreGraph cs` implies `e ∈ cs.RF.F.E`
          have heF0 : e ∈ cs.RF.F.E := by
            by_contra hnf; exact he0 (Finset.mem_sdiff.mpr ⟨heG0, hnf⟩)
          -- Either `u = .delete e` or `e ∈ (forestAfterInput cs.RF.F u).E \ cs1.RF.F.E`
          cases u with
          | delete e' =>
            by_cases hee : e = e'
            · subst hee; exact Finset.mem_union_left _ (List.mem_toFinset.mpr (by simp))
            · have he_fai : e ∈ (forestAfterInput cs.RF.F (.delete e')).E :=
                Finset.mem_erase.mpr ⟨hee, heF0⟩
              have hrel : e ∈ ((canonStepSplits cs (.delete e')).filter CompSplitEntry.isRelease).map CompSplitEntry.edge := by
                rw [canonStepSplits_releases_edges]
                exact (Finset.mem_sort _).mpr (Finset.mem_sdiff.mpr ⟨he_fai, he_notF1⟩)
              rcases List.mem_map.mp hrel with ⟨s, hs, rfl⟩
              exact Finset.mem_union_right _ (List.mem_toFinset.mpr
                (List.mem_map.mpr ⟨s, List.mem_append_left _ (List.mem_of_mem_filter hs), rfl⟩))
          | insert e' a b =>
            have he_fai : e ∈ (forestAfterInput cs.RF.F (.insert e' a b)).E := heF0
            have hrel : e ∈ ((canonStepSplits cs (.insert e' a b)).filter CompSplitEntry.isRelease).map CompSplitEntry.edge := by
              rw [canonStepSplits_releases_edges]
              exact (Finset.mem_sort _).mpr (Finset.mem_sdiff.mpr ⟨he_fai, he_notF1⟩)
            rcases List.mem_map.mp hrel with ⟨s, hs, rfl⟩
            exact Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_map.mpr ⟨s, List.mem_append_left _ (List.mem_of_mem_filter hs), rfl⟩))
          | split v v' St Sh =>
            have he_fai : e ∈ (forestAfterInput cs.RF.F (.split v v' St Sh)).E := heF0
            have hrel : e ∈ ((canonStepSplits cs (.split v v' St Sh)).filter CompSplitEntry.isRelease).map CompSplitEntry.edge := by
              rw [canonStepSplits_releases_edges]
              exact (Finset.mem_sort _).mpr (Finset.mem_sdiff.mpr ⟨he_fai, he_notF1⟩)
            rcases List.mem_map.mp hrel with ⟨s, hs, rfl⟩
            exact Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_map.mpr ⟨s, List.mem_append_left _ (List.mem_of_mem_filter hs), rfl⟩))
        · -- `e ∈ (cs.G.applyUpdate u).E \ cs.G.E` implies `u = .insert e _ _`
          cases u with
          | insert e' a b =>
            have hee : e = e' := (Finset.mem_insert.mp he_cs1G).resolve_right heG0
            subst hee; exact Finset.mem_union_left _ (List.mem_toFinset.mpr (by simp))
          | delete e' => exact absurd (Finset.mem_of_mem_erase he_cs1G) heG0
          | split _ _ _ _ => exact absurd he_cs1G heG0
    · -- `e ∉ (coreGraph cs1.G cs1.lsf).E \ batchDeletes rest`, so `e` is in IH!
      have hmem_ih := hih (Finset.mem_sdiff.mpr ⟨heG', h1⟩)
      rcases Finset.mem_union.mp hmem_ih with hL | hR
      · refine Finset.mem_union_left _ (List.mem_toFinset.mpr ?_)
        rw [List.mem_toFinset] at hL
        cases u <;> simp [hL]
      · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
        rw [List.mem_toFinset] at hR
        rcases List.mem_map.mp hR with ⟨s, hs, rfl⟩
        exact List.mem_map.mpr ⟨s, List.mem_append_right _ hs, rfl⟩

private lemma newCoreEdges_card_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (cs : CompLSFState) (U : List Update)
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    ((coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).E \
      ((coreGraph cs.G cs.lsf).E \ batchDeletes U)).card ≤
      U.length + (canonSplitList cs U).length := by
  have hsub := newCoreEdges_subset cs U hI hU
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := updateEdgeOpt_card_le U
  have h3 : ((canonSplitList cs U).map CompSplitEntry.edge).toFinset.card ≤ (canonSplitList cs U).length :=
    (List.toFinset_card_le _).trans (by simp)
  omega

private lemma outCoreOrder_nodup_and_mem {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord) :
    (∀ v, (outCoreOrder tr ord v).Nodup) ∧
    (∀ v x, x ∈ outCoreOrder tr ord v ↔
      x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E ∧ (coreGraph tr.cs.G tr.cs.lsf).src x = v) := by
  classical
  have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ tr.cs) (ρ' : Rotation tr.cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  have hrot : outCoreOrder tr ord =
      (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).order := by
    funext v
    unfold outCoreOrder
    rw [dite_eq_left hex]
    have hρ_eq : hex.choose_spec.choose_spec.choose_spec.choose = ρ :=
      Rotation.ext_order (hex.choose_spec.choose_spec.choose_spec.choose_spec.trans hρ.symm)
    change (coreRotation (L := tr.cs.lsf) hex.choose_spec.choose_spec.choose_spec.choose
        hex.choose_spec.choose_spec.choose.hG_val
        (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).order v = _
    rw [hρ_eq]
  rw [hrot]
  exact ⟨(coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).nodup,
    (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).mem_order⟩

private lemma list_length_eq_countP_add {α : Type*} (l : List α) (p : α → Bool) :
    l.length = l.countP p + l.countP (fun x => !p x) := by
  induction l with
  | nil => simp
  | cons a tl ih => cases hp : p a <;> simp [hp, ih] <;> omega

private lemma list_countP_eq_card_filter {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    (p : α → Bool) :
    l.countP p = (l.toFinset.filter fun x => p x = true).card := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd_tl⟩
    have hmem : a ∉ tl.toFinset := by simpa using hnot
    rw [List.countP_cons, ih hnd_tl, List.toFinset_cons, Finset.filter_insert]
    cases hp : p a
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    · simp only [↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp [hmem])]

private lemma list_length_le_2eCap {eCap : ℕ} {l : List End} (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, x.1 < eCap) : l.length ≤ 2 * eCap := by
  rw [← List.toFinset_card_of_nodup hnd]
  have hsub : l.toFinset ⊆ Finset.range eCap ×ˢ (Finset.univ : Finset Bool) := fun x hx => by
    rw [Finset.mem_product, Finset.mem_range]
    exact ⟨hlt x (List.mem_toFinset.mp hx), Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool] at hle
  omega

/-! ## Main theorems -/

public section

/-- Every active slot `S₀ j = some B₀` satisfies `BundleStepReady tr.cs B₀ tr.k ord ord' U`. -/
theorem bundleStepReady_of_active_slot {depth slotCap cap : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord ord' : ℕ → List End} {U : List Update}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S₀ : BundleTableState slotCap}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hPartAll : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      ∀ (ρ : Rotation tr.cs.G), ρ.order = ord →
        (tr.bun (C, b)).IsPartition (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) tr.k)
    (hSlotMap : SlotMapOK tr slotCap cap slots slotOf)
    (hBunMatch : BunTableMatches tr slotOf S₀)
    (hFree : ∀ j : Fin slotCap, j.1 ∉ slots → S₀ j = none) :
    ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U := by
  intro j B₀ hSj
  obtain ⟨ρ, σ, hρ, hσ, hRB⟩ := hOB
  have hj_mem : j.1 ∈ slots := by
    by_contra hnot; cases (hFree j hnot).symm.trans hSj
  obtain ⟨q, hq, hsq⟩ := hSlotMap.2.2.1 j.1 hj_mem
  obtain ⟨hs, B', hSB', hAg⟩ := hBunMatch q hq
  have hj_eq : j = ⟨slotOf q, hs⟩ := Fin.ext hsq.symm
  subst hj_eq
  have hB_eq : B₀ = B' := Option.some.inj (hSj.symm.trans hSB')
  subst hB_eq
  rcases Finset.mem_biUnion.mp hq with ⟨C, hC, hb_img⟩
  rcases Finset.mem_image.mp hb_img with ⟨b, hb, rfl⟩
  exact ⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hRB, hBU, (bunAgree_isPartition_iff hAg).mpr (hPartAll C hC b hb ρ hρ)⟩

set_option maxHeartbeats 800000 in
/-- **Complete Phase 3 split-group specification**: for `L = canonSplitList tr.cs U`,
`pairs = L.map fun s => (s.kept, s.fresh)`, `gs = splitGroupsOf pairs`, `oldRoots = splitOldRoots pairs`,
proves every split-group hypothesis of `bunTableHeadroom_step_model_runs_on` together with
`totalAdded ≤ 2 * (U.length + L.length)`, `groupsTotalLen gs ≤ 2 * L.length`, and
`groupsWords gs ≤ 3 * L.length`. -/
theorem splitGroups_model_spec {w depth slotCap vCap eCap : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord : ℕ → List End} {U : List Update} {ord' : ℕ → List End}
    {S₀ : BundleTableState slotCap}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hRlt : ∀ r ∈ (compLSFBatch tr.cs U).RF.R, r < vCap)
    (hVltW : vCap < 2 ^ w)
    (hE_old : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, e < eCap)
    (hE_new : ∀ e ∈ (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).E, e < eCap)
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U) :
    let L := canonSplitList tr.cs U
    let pairs := L.map fun s => (s.kept, s.fresh)
    let gs := splitGroupsOf pairs
    let oldRoots := splitOldRoots pairs
    let info := stepBundleTree sparsify tr U ord ord'
    let cord := outCoreOrder tr ord
    let cord' := outCoreOrder info.state ord'
    let R_old := tr.cs.RF.R
    let R_new := info.state.cs.RF.R
    (∀ s ∈ L, s.kept < vCap ∧ s.fresh < vCap) ∧
    (splitOldList pairs (fun _ => 0) = pairs.map fun p => ancDecode (splitAncFold pairs (fun _ => 0)) p.2) ∧
    (∀ G ∈ gs, 0 < G.length) ∧
    (∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w) ∧
    (∀ G ∈ gs, G.Nodup) ∧
    (∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new) ∧
    (∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint (gs[i]'hi).toFinset (gs[j]'hj).toFinset) ∧
    oldRoots.length = gs.length ∧
    oldRoots.Nodup ∧
    (∀ r ∈ oldRoots, r ∈ R_old) ∧
    groupsTotalLen gs ≤ 2 * L.length ∧
    groupsWords gs ≤ 3 * L.length ∧
    (∃ (addG addR : ℕ → ℕ),
      (∀ gi (hgi : gi < gs.length),
        (∑ v ∈ (gs[gi]'hgi).toFinset, (cord' v).length) ≤
          (cord (oldRoots[gi]'(by simp [gs, splitGroupsOf, oldRoots] at hgi ⊢; exact hgi))).length + addG gi ∧
        (cord (oldRoots[gi]'(by simp [gs, splitGroupsOf, oldRoots] at hgi ⊢; exact hgi))).length + addG gi ≤ 4 * eCap) ∧
      (∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ (gs[gi]'hgi).toFinset) →
        r ∈ R_old ∧ r ∉ oldRoots ∧
          (cord' r).length ≤ (cord r).length + addR r ∧
          (cord r).length + addR r ≤ 4 * eCap) ∧
      (let U_grp := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
       (∑ gi ∈ Finset.range gs.length, addG gi) + ∑ r ∈ R_new \ U_grp, addR r ≤
         2 * (U.length + L.length))) ∧
    (∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ batchDeletes U)
        (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) bun,
            (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src x ∈ (gs[gi]'hgi).toFinset) := by
  intro L pairs gs oldRoots info cord cord' R_old R_new
  obtain ⟨ρ, σ, hρ, hσ, _⟩ := hOB
  have hI' : CompLSFInv C_lsst ℓ₀ (compLSFBatch tr.cs U) := compLSFBatch_inv hI hBU
  have hcs'_eq : info.state.cs = compLSFBatch tr.cs U := rfl
  have hR_sub : R_old ⊆ R_new := (compLSFBatch_decremental hI hBU).2
  set G₀ := coreGraph tr.cs.G tr.cs.lsf
  set UC := canonCoreBatch tr.cs U
  set G' := coreGraph info.state.cs.G info.state.cs.lsf
  have hG₀_val : G₀.IsValid := coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)
  obtain ⟨hUC_val, hGEq, hDel_sub⟩ := canonCoreBatch_valid_and_graphEq hI hBU
  have hpairs_eq : coreBatchSplitPairs UC = pairs := canonSplitList_eq_coreSplits tr.cs U
  have hAnc := applyBatch_anc_spec G₀ UC hG₀_val hUC_val
  rw [hpairs_eq] at hAnc
  set anc := splitAncFold pairs (fun _ => 0)
  obtain ⟨hAnc_old, hAnc_out, hAnc_in, hAnc_diff, hSnd_nd, hAnc_src, hOldList_eq, hPairs_old⟩ := hAnc
  have hG'V : G'.V = (G₀.applyBatch UC).V := hGEq.1
  have hG'E : G'.E = (G₀.applyBatch UC).E := hGEq.2.1
  have hRold_V : R_old = G₀.V := rfl
  have hRnew_V : R_new = (G₀.applyBatch UC).V := hG'V
  -- 1. Bound every `(kept, fresh)` in `L` by `vCap`
  have hL_vCap : ∀ s ∈ L, s.kept < vCap ∧ s.fresh < vCap := by
    have haux : ∀ (G : MGraph) (B : List Update), G.BatchIsValid B →
        (∀ v ∈ (G.applyBatch B).V, v < vCap) →
        ∀ p ∈ coreBatchSplitPairs B, p.1 < vCap ∧ p.2 < vCap := by
      intro G B; induction B generalizing G with
      | nil => intro _ _ _ h; cases h
      | cons u rest ih =>
        intro ⟨hu, hrest⟩ hVlt p hp
        have hVsub : ∀ (G₁ : MGraph) (B₁ : List Update), G₁.BatchIsValid B₁ → G₁.V ⊆ (G₁.applyBatch B₁).V := by
          intro G₁ B₁; induction B₁ generalizing G₁ with
          | nil => intro _; exact Finset.Subset.rfl
          | cons u₁ r₁ ih₁ =>
            intro ⟨hu₁, hr₁⟩
            have h1 : G₁.V ⊆ (G₁.applyUpdate u₁).V := by cases u₁ <;> simp [MGraph.applyUpdate]
            exact h1.trans (ih₁ _ hr₁)
        cases u with
        | insert _ _ _ => exact ih _ hrest hVlt p hp
        | delete _ => exact ih _ hrest hVlt p hp
        | split v v' St Sh =>
          simp only [coreBatchSplitPairs, List.filterMap_cons, List.mem_cons] at hp
          rcases hp with rfl | hp'
          · have hsub1 := hVsub (G.applyUpdate (.split v v' St Sh)) rest hrest
            exact ⟨hVlt v (hsub1 (Finset.mem_insert_of_mem hu.1)),
              hVlt v' (hsub1 (Finset.mem_insert_self v' G.V))⟩
          · exact ih _ hrest hVlt p hp'
    intro s hs
    have hp : (s.kept, s.fresh) ∈ coreBatchSplitPairs UC := by
      rw [hpairs_eq]; exact List.mem_map.mpr ⟨s, hs, rfl⟩
    exact haux G₀ UC hUC_val (fun v hv => by rw [← hRnew_V] at hv; exact hRlt v hv) (s.kept, s.fresh) hp
  -- 2. Basic properties of `oldRoots` and `gs`
  have hold_nd : oldRoots.Nodup := Finset.sort_nodup _ _
  have hold_mem_iff : ∀ r, r ∈ oldRoots ↔ r ∈ splitOldList pairs (fun _ => 0) := fun r => by
    simp [oldRoots, splitOldRoots]
  have hold_sub : ∀ r ∈ oldRoots, r ∈ R_old := fun r hr => by
    rw [hold_mem_iff, hOldList_eq, List.mem_map] at hr
    rcases hr with ⟨p, hp, rfl⟩; exact hPairs_old p hp
  have hold_len : oldRoots.length = gs.length := by simp [gs, splitGroupsOf, oldRoots]
  have hgs_pos : ∀ G ∈ gs, 0 < G.length := fun G hG => by
    rcases List.mem_map.mp hG with ⟨r, _, rfl⟩; simp
  have hgs_mem_iff : ∀ gi (hgi : gi < gs.length) v,
      v ∈ (gs[gi]'hgi) ↔ v = oldRoots[gi]'(by omega) ∨ (v ∈ R_new \ R_old ∧ ancDecode anc v = oldRoots[gi]'(by omega)) := by
    intro gi hgi v
    have hget : gs[gi]'hgi = oldRoots[gi]'(by omega) :: (pairs.filter fun p => decide (ancDecode anc p.2 = oldRoots[gi]'(by omega))).map Prod.snd := by
      simp [gs, splitGroupsOf, oldRoots, anc]
    rw [hget, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨p, hp, rfl⟩)
      · exact Or.inl rfl
      · rw [List.mem_filter, decide_eq_true_eq] at hp
        right; refine ⟨?_, hp.2⟩
        rw [hRnew_V, hRold_V, hAnc_diff]; exact List.mem_map.mpr ⟨p, hp.1, rfl⟩
    · rintro (rfl | ⟨hv_diff, hanc_v⟩)
      · exact Or.inl rfl
      · right
        rw [hRnew_V, hRold_V, hAnc_diff, List.mem_map] at hv_diff
        rcases hv_diff with ⟨p, hp, rfl⟩
        exact ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr hanc_v⟩, rfl⟩
  have hgs_sub : ∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new := fun G hG v hv => by
    rw [List.mem_iff_getElem] at hG; rcases hG with ⟨gi, hgi, rfl⟩
    rcases (hgs_mem_iff gi hgi v).mp hv with rfl | ⟨hdiff, _⟩
    · exact hR_sub (hold_sub _ (List.getElem_mem _))
    · exact (Finset.mem_sdiff.mp hdiff).1
  have hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w := fun G hG v hv =>
    ⟨hRlt v (hgs_sub G hG v hv), lt_trans (hRlt v (hgs_sub G hG v hv)) hVltW⟩
  have hgs_nd : ∀ G ∈ gs, G.Nodup := fun G hG => by
    rcases List.mem_map.mp hG with ⟨r, hr, rfl⟩
    rw [List.nodup_cons]
    refine ⟨fun hm => ?_, ?_⟩
    · rcases List.mem_map.mp hm with ⟨p, hp, hp_eq⟩
      have hv_diff : r ∈ (G₀.applyBatch UC).V \ G₀.V :=
        (hAnc_diff r).mpr (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, hp_eq⟩)
      exact (Finset.mem_sdiff.mp hv_diff).2 (hold_sub r hr)
    · have hsub : List.Sublist ((pairs.filter fun p => decide (ancDecode anc p.2 = r)).map Prod.snd) (pairs.map Prod.snd) :=
        (List.filter_sublist).map Prod.snd
      exact hSnd_nd.sublist hsub
  have hgs_anc : ∀ gi (hgi : gi < gs.length) v, v ∈ (gs[gi]'hgi) → ancDecode anc v = oldRoots[gi]'(by omega) := by
    intro gi hgi v hv
    rcases (hgs_mem_iff gi hgi v).mp hv with rfl | ⟨_, hanc_v⟩
    · have h0 := hAnc_old (oldRoots[gi]'(by omega)) (hold_sub _ (List.getElem_mem (by omega)))
      dsimp only [anc]; simp [ancDecode, h0]
    · exact hanc_v
  have hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint (gs[i]'hi).toFinset (gs[j]'hj).toFinset := fun i hi j hj hne =>
    Finset.disjoint_left.mpr fun v hvi hvj => by
      have h1 := hgs_anc i hi v (List.mem_toFinset.mp hvi)
      have h2 := hgs_anc j hj v (List.mem_toFinset.mp hvj)
      have heq := (List.nodup_iff_injective_getElem.mp hold_nd)
        (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) (h1.symm.trans h2)
      exact hne (congrArg Fin.val heq)
  -- 3. `groupsTotalLen gs ≤ 2 * L.length` and `groupsWords gs ≤ 3 * L.length`
  have hold_len_le : oldRoots.length ≤ L.length := by
    rw [← List.toFinset_card_of_nodup hold_nd]
    have hsub : oldRoots.toFinset ⊆ (splitOldList pairs (fun _ => 0)).toFinset := fun r hr =>
      List.mem_toFinset.mpr ((hold_mem_iff r).mp (List.mem_toFinset.mp hr))
    have hlen_ol : ∀ (ps : List (ℕ × ℕ)) (a : ℕ → ℕ), (splitOldList ps a).length = ps.length := by
      intro ps; induction ps with | nil => intro _; rfl | cons _ _ ih => intro _; simp [splitOldList, ih]
    calc oldRoots.toFinset.card ≤ (splitOldList pairs (fun _ => 0)).toFinset.card := Finset.card_le_card hsub
      _ ≤ (splitOldList pairs (fun _ => 0)).length := List.toFinset_card_le _
      _ = pairs.length := hlen_ol pairs (fun _ => 0)
      _ = L.length := List.length_map _
  have htot_le : groupsTotalLen gs ≤ 2 * L.length := by
    have h1 : groupsTotalLen gs = ((Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset).card := by
      rw [Finset.card_biUnion]
      · unfold groupsTotalLen
        have hsum : ∀ (l : List (List ℕ)), (∀ g ∈ l, g.Nodup) →
            (l.map List.length).sum = ∑ i ∈ Finset.range l.length, (l.getD i []).toFinset.card := by
          intro l; induction l using List.reverseRecOn with
          | nil => intro _; simp
          | append_singleton xs x ih =>
            intro hnd'
            rw [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
              List.length_append, List.length_singleton, Finset.sum_range_succ, ih (fun g hg => hnd' g (List.mem_append_left _ hg))]
            congr 1
            · refine Finset.sum_congr rfl fun i hi => ?_
              have hilt := Finset.mem_range.mp hi
              rw [List.getD_eq_getElem (xs ++ [x]) [] (by rw [List.length_append]; omega), List.getElem_append_left hilt,
                List.getD_eq_getElem xs [] hilt]
            · rw [List.getD_eq_getElem (xs ++ [x]) [] (by simp only [List.length_append, List.length_singleton]; omega),
                List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [List.toFinset_card_of_nodup (hnd' x (List.mem_append.mpr (Or.inr List.mem_cons_self)))]
        exact hsum gs hgs_nd
      · intro i hi j hj hne
        have hi' := Finset.mem_range.mp hi; have hj' := Finset.mem_range.mp hj
        dsimp only [Function.onFun]
        rw [List.getD_eq_getElem gs [] hi', List.getD_eq_getElem gs [] hj']
        exact hgs_disj i hi' j hj' hne
    rw [h1]
    have hsub : ((Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset) ⊆
        oldRoots.toFinset ∪ (pairs.map Prod.snd).toFinset := fun v hv => by
      rcases Finset.mem_biUnion.mp hv with ⟨gi, hgi, hvg⟩
      have hgi' := Finset.mem_range.mp hgi
      rw [List.getD_eq_getElem gs [] hgi', List.mem_toFinset] at hvg
      rcases (hgs_mem_iff gi hgi' v).mp hvg with rfl | ⟨hdiff, _⟩
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.getElem_mem _))
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr ((hAnc_diff v).mp (by rwa [← hRnew_V, ← hRold_V])))
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : oldRoots.toFinset.card ≤ L.length := (List.toFinset_card_le _).trans hold_len_le
    have h3 : (pairs.map Prod.snd).toFinset.card ≤ L.length :=
      (List.toFinset_card_le _).trans (by simp [pairs])
    omega
  have hwords_le : groupsWords gs ≤ 3 * L.length := by
    have hgw : groupsWords gs = gs.length + groupsTotalLen gs := by
      clear htot_le; induction gs with
      | nil => simp [groupsWords, groupsTotalLen]
      | cons g rest ih => simp [groupsWords, groupsTotalLen] at ih ⊢; omega
    omega
  -- 4. Surviving/new ends split for `hgroup_sum_le`, `hrest_le`, and `totalAdded`
  obtain ⟨hcord_nd, hcord_iff⟩ := outCoreOrder_nodup_and_mem hI ρ hρ
  let σ' : Rotation info.state.cs.G := (compLSFBatch_G tr.cs U).symm ▸ σ
  have hσ' : σ'.order = ord' := by
    dsimp only [σ']
    have hcast : ∀ {G H : MGraph} (he : G = H) (τ : Rotation G), (he ▸ τ : Rotation H).order = τ.order := by
      intro G H he τ; cases he; rfl
    exact (hcast _ σ).trans hσ
  obtain ⟨hcord'_nd, hcord'_iff⟩ := outCoreOrder_nodup_and_mem hI' σ' hσ'
  set survE : Finset ℕ := G₀.E \ batchDeletes U
  let isNew : End → Bool := fun x => !decide (x.1 ∈ survE)
  let addR : ℕ → ℕ := fun v => (cord' v).countP isNew
  let addG : ℕ → ℕ := fun gi => ∑ v ∈ (gs.getD gi []).toFinset, addR v
  have hsurv_anc : ∀ x : End, x.1 ∈ survE → ∀ v, x ∈ cord' v → ancDecode anc v = G₀.src x ∧ x ∈ cord (G₀.src x) := by
    intro x hx v hxv
    obtain ⟨hxE', hsrc'⟩ := (hcord'_iff v x).mp hxv
    have hx_sub : x.1 ∈ G₀.E \ batchDeletes UC :=
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, fun hd => (Finset.mem_sdiff.mp hx).2 (hDel_sub hd)⟩
    have hsrc_eq : (G₀.applyBatch UC).src x = v := by
      rw [← hsrc']
      rcases x with ⟨e, side⟩
      cases side with
      | true => exact (hGEq.2.2 e hxE').1.symm
      | false => exact (hGEq.2.2 e hxE').2.symm
    have hanc_eq := hAnc_src x.1 hx_sub x.2
    rw [hsrc_eq] at hanc_eq
    exact ⟨hanc_eq, (hcord_iff (G₀.src x) x).mpr ⟨(Finset.mem_sdiff.mp hx).1, rfl⟩⟩
  have hcord_le_2e : ∀ v, (cord v).length ≤ 2 * eCap := fun v =>
    list_length_le_2eCap (hcord_nd v) fun x hx => hE_old x.1 ((hcord_iff v x).mp hx).1
  have haddR_sum_le : (∑ v ∈ R_new, addR v) ≤ 2 * (U.length + L.length) := by
    have hcard_eq : ∀ v ∈ R_new, addR v = ((cord' v).toFinset.filter fun x => x.1 ∈ G'.E \ survE).card := fun v _ => by
      unfold addR
      rw [list_countP_eq_card_filter (hcord'_nd v)]
      congr 1; ext x
      simp only [Finset.mem_filter, List.mem_toFinset, isNew, Bool.not_eq_true', decide_eq_false_iff_not, Finset.mem_sdiff]
      exact ⟨fun ⟨hx, hns⟩ => ⟨hx, ((hcord'_iff v x).mp hx).1, hns⟩, fun ⟨hx, _, hns⟩ => ⟨hx, hns⟩⟩
    rw [Finset.sum_congr rfl hcard_eq, ← Finset.card_biUnion]
    · have hsub : (R_new.biUnion fun v => (cord' v).toFinset.filter fun x => x.1 ∈ G'.E \ survE) ⊆
          (G'.E \ survE) ×ˢ (Finset.univ : Finset Bool) := fun x hx => by
        rcases Finset.mem_biUnion.mp hx with ⟨v, _, hxv⟩
        rw [Finset.mem_product]; exact ⟨(Finset.mem_filter.mp hxv).2, Finset.mem_univ _⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h1
      have h2 := newCoreEdges_card_le tr.cs U hI hBU
      have hG'_eq : (G'.E \ survE).card =
          ((coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).E \
            ((coreGraph tr.cs.G tr.cs.lsf).E \ batchDeletes U)).card := by
        dsimp only [G', survE, G₀]; rw [hcs'_eq]
      have hL_len_eq : (canonSplitList tr.cs U).length = L.length := rfl
      omega
    · intro u _ v _ huv
      refine Finset.disjoint_left.mpr fun x hxu hxv => huv ?_
      have h1 := ((hcord'_iff u x).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hxu).1)).2
      have h2 := ((hcord'_iff v x).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hxv).1)).2
      exact h1.symm.trans h2
  have haddR_sum_2e : (∑ v ∈ R_new, addR v) ≤ 2 * eCap := by
    have hcard_eq : ∀ v ∈ R_new, addR v ≤ ((cord' v).toFinset).card := fun v _ => by
      unfold addR; rw [list_countP_eq_card_filter (hcord'_nd v)]; exact Finset.card_filter_le _ _
    have hle1 : (∑ v ∈ R_new, addR v) ≤ (R_new.biUnion fun v => (cord' v).toFinset).card := by
      rw [Finset.card_biUnion]
      · exact Finset.sum_le_sum hcard_eq
      · intro u _ v _ huv
        refine Finset.disjoint_left.mpr fun x hxu hxv => huv ?_
        exact ((hcord'_iff u x).mp (List.mem_toFinset.mp hxu)).2.symm.trans
          ((hcord'_iff v x).mp (List.mem_toFinset.mp hxv)).2
    have hsub : (R_new.biUnion fun v => (cord' v).toFinset) ⊆ Finset.range eCap ×ˢ (Finset.univ : Finset Bool) := fun x hx => by
      rcases Finset.mem_biUnion.mp hx with ⟨v, _, hxv⟩
      rw [Finset.mem_product, Finset.mem_range]
      exact ⟨hE_new x.1 ((hcord'_iff v x).mp (List.mem_toFinset.mp hxv)).1, Finset.mem_univ _⟩
    exact hle1.trans ((Finset.card_le_card hsub).trans (by simp [Finset.card_product]; omega))
  -- 5. Combine everything!
  refine ⟨hL_vCap, hOldList_eq, hgs_pos, hgs_lt, hgs_nd, hgs_sub, hgs_disj, hold_len, hold_nd, hold_sub,
    htot_le, hwords_le, ⟨addG, addR, ?_, ?_, ?_⟩, ?_⟩
  · -- `hgroup_sum_le`
    intro gi hgi
    set r := oldRoots[gi]'(by omega)
    have hsplit : ∀ v ∈ (gs[gi]'hgi).toFinset,
        (cord' v).length = ((cord' v).toFinset.filter fun x => x.1 ∈ survE).card + addR v := fun v _ => by
      have h1 := list_length_eq_countP_add (cord' v) (fun x => decide (x.1 ∈ survE))
      rw [list_countP_eq_card_filter (hcord'_nd v)] at h1
      simp only [decide_eq_true_eq] at h1
      exact h1
    have hsum_eq : ∑ v ∈ (gs[gi]'hgi).toFinset, (cord' v).length =
        (∑ v ∈ (gs[gi]'hgi).toFinset, ((cord' v).toFinset.filter fun x => x.1 ∈ survE).card) + addG gi := by
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      congr 1; simp only [addG, List.getD_eq_getElem, hgi]
    have hsurv_le : (∑ v ∈ (gs[gi]'hgi).toFinset, ((cord' v).toFinset.filter fun x => x.1 ∈ survE).card) ≤
        (cord r).length := by
      rw [← Finset.card_biUnion]
      · rw [← List.toFinset_card_of_nodup (hcord_nd r)]
        refine Finset.card_le_card fun x hx => ?_
        rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
        rw [Finset.mem_filter, List.mem_toFinset] at hxv
        have ⟨hanc_v, hxin⟩ := hsurv_anc x hxv.2 v hxv.1
        have hv_r : ancDecode anc v = r := hgs_anc gi hgi v (List.mem_toFinset.mp hv)
        rw [← hanc_v, hv_r] at hxin
        exact List.mem_toFinset.mpr hxin
      · intro u _ v _ huv
        refine Finset.disjoint_left.mpr fun x hxu hxv => huv ?_
        exact ((hcord'_iff u x).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hxu).1)).2.symm.trans
          ((hcord'_iff v x).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hxv).1)).2
    have haddG_le : addG gi ≤ 2 * eCap := by
      have hsub : (gs[gi]'hgi).toFinset ⊆ R_new := fun v hv => hgs_sub _ (List.getElem_mem hgi) v (List.mem_toFinset.mp hv)
      calc addG gi = ∑ v ∈ (gs[gi]'hgi).toFinset, addR v := by simp only [addG, List.getD_eq_getElem, hgi]
        _ ≤ ∑ v ∈ R_new, addR v := Finset.sum_le_sum_of_subset hsub
        _ ≤ 2 * eCap := haddR_sum_2e
    have hcord_r := hcord_le_2e r
    omega
  · -- `hrest_le`
    intro r hr hnot_gs
    have hr_old : r ∈ R_old := by
      by_contra hno
      have hdiff : r ∈ (G₀.applyBatch UC).V \ G₀.V := Finset.mem_sdiff.mpr ⟨hRnew_V ▸ hr, hno⟩
      rcases List.mem_map.mp ((hAnc_diff r).mp hdiff) with ⟨p, hp, rfl⟩
      have ha_in : ancDecode anc p.2 ∈ oldRoots :=
        (hold_mem_iff _).mpr (by rw [hOldList_eq]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
      rw [List.mem_iff_getElem] at ha_in; rcases ha_in with ⟨gi, hgi, hgi_eq⟩
      have hgi' : gi < gs.length := by omega
      have hmem : p.2 ∈ (gs[gi]'hgi').toFinset :=
        List.mem_toFinset.mpr ((hgs_mem_iff gi hgi' p.2).mpr (Or.inr ⟨by rwa [hRnew_V, hRold_V], hgi_eq.symm⟩))
      exact hnot_gs gi hgi' hmem
    have hr_not_oldRoots : r ∉ oldRoots := fun hm => by
      rw [List.mem_iff_getElem] at hm; rcases hm with ⟨gi, hgi, rfl⟩
      have hgi' : gi < gs.length := by omega
      exact hnot_gs gi hgi' (List.mem_toFinset.mpr ((hgs_mem_iff gi hgi' _).mpr (Or.inl rfl)))
    have hsplit : (cord' r).length = ((cord' r).toFinset.filter fun x => x.1 ∈ survE).card + addR r := by
      have h1 := list_length_eq_countP_add (cord' r) (fun x => decide (x.1 ∈ survE))
      rw [list_countP_eq_card_filter (hcord'_nd r)] at h1
      simp only [decide_eq_true_eq] at h1
      exact h1
    have hsurv_le : ((cord' r).toFinset.filter fun x => x.1 ∈ survE).card ≤ (cord r).length := by
      rw [← List.toFinset_card_of_nodup (hcord_nd r)]
      refine Finset.card_le_card fun x hx => ?_
      rw [Finset.mem_filter, List.mem_toFinset] at hx
      have ⟨hanc_r, hxin⟩ := hsurv_anc x hx.2 r hx.1
      have h0 : ancDecode anc r = r := by dsimp only [anc]; simp [ancDecode, hAnc_old r hr_old]
      rw [← hanc_r, h0] at hxin
      exact List.mem_toFinset.mpr hxin
    have haddR_le : addR r ≤ 2 * eCap :=
      (Finset.single_le_sum (f := addR) (fun _ _ => Nat.zero_le _) hr).trans haddR_sum_2e
    have hcord_r := hcord_le_2e r
    exact ⟨hr_old, hr_not_oldRoots, by omega, by omega⟩
  · -- `totalAdded ≤ 2 * (U.length + L.length)`
    dsimp only
    set U_grp := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
    have hUsub : U_grp ⊆ R_new := fun v hv => by
      rcases Finset.mem_biUnion.mp hv with ⟨gi, hgi, hvg⟩
      have hgi' := Finset.mem_range.mp hgi
      rw [List.getD_eq_getElem gs [] hgi', List.mem_toFinset] at hvg
      exact hgs_sub _ (List.getElem_mem hgi') v hvg
    have hsum_grp : ∑ gi ∈ Finset.range gs.length, addG gi = ∑ v ∈ U_grp, addR v := by
      rw [Finset.sum_biUnion]
      intro i hi j hj hne
      have hi' := Finset.mem_range.mp hi; have hj' := Finset.mem_range.mp hj
      dsimp only [Function.onFun]
      rw [List.getD_eq_getElem gs [] hi', List.getD_eq_getElem gs [] hj']
      exact hgs_disj i hi' j hj' hne
    rw [hsum_grp, add_comm, Finset.sum_sdiff hUsub]
    exact haddR_sum_le
  · -- `hbundle_in_group`
    intro j B₀ hSj bun hbun hcard2
    obtain ⟨_, _, hI_j, ρ_j, _, hρ_j, _, _, _, hPart⟩ := hready j B₀ hSj
    have hρ_eq : ρ_j = ρ := Rotation.ext_order (hρ_j.trans hρ.symm)
    have hPart_ρ : B₀.IsPartition (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) tr.k := by
      subst hρ_eq; exact hPart
    have hsrc_anc : ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) bun,
        G'.src x ∈ R_new ∧ ancDecode anc (G'.src x) = B₀.parent bun := by
      intro x hx
      rw [survivingEnds, Finset.mem_filter] at hx
      obtain ⟨hx_ends, hx_surv⟩ := hx
      have hx_eB : x.1 ∈ B₀.edges := (Finset.mem_sdiff.mp hx_surv).1
      have hx_G0 : x.1 ∈ G₀.E := hPart_ρ.1 hx_eB
      have hx_survE : x.1 ∈ survE := Finset.mem_sdiff.mpr ⟨hx_G0, (Finset.mem_sdiff.mp hx_surv).2⟩
      have hx_in_G' : x.1 ∈ G'.E := by
        rw [hG'E]
        have hx_sub : x.1 ∈ G₀.E \ batchDeletes UC :=
          Finset.mem_sdiff.mpr ⟨hx_G0, fun hd => (Finset.mem_sdiff.mp hx_surv).2 (hDel_sub hd)⟩
        have hkeep : ∀ (G : MGraph) (B : List Update) (e : ℕ),
            e ∈ G.E \ batchDeletes B → e ∈ (G.applyBatch B).E := by
          intro G B; induction B generalizing G with
          | nil => intro e he; exact (Finset.mem_sdiff.mp he).1
          | cons u r ih =>
            intro e he; rw [Finset.mem_sdiff] at he
            have hnot_r : e ∉ batchDeletes r := fun hr => he.2 (by
              obtain ⟨w, hw, rfl⟩ := (mem_batchDeletes_iff _ _).mp hr
              exact (mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_cons_of_mem u hw, rfl⟩)
            apply ih
            refine Finset.mem_sdiff.mpr ⟨?_, hnot_r⟩
            cases u with
            | insert e' _ _ => exact Finset.mem_insert_of_mem he.1
            | delete e' =>
              have hne : e ≠ e' := fun h => he.2 (by subst h; exact (mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_cons_self, rfl⟩)
              exact Finset.mem_erase.mpr ⟨hne, he.1⟩
            | split _ _ _ _ => exact he.1
        exact hkeep G₀ UC x.1 hx_sub
      have hsrc'_mem : G'.src x ∈ R_new := by
        have hv := coreGraph_isValid hI'.hG_val (compLSF_RF_isRSF hI') x.1 hx_in_G'
        rcases x with ⟨e, side⟩
        cases side <;> [exact hv.2; exact hv.1]
      have hx_cord' : x ∈ cord' (G'.src x) := (hcord'_iff _ _).mpr ⟨hx_in_G', rfl⟩
      have ⟨hanc_x, _⟩ := hsurv_anc x hx_survE (G'.src x) hx_cord'
      have hsrc0 : G₀.src x = B₀.parent bun := by
        have hx_edgeEnds : x ∈ Bundle.edgeEnds B₀.edges := by simp [Bundle.mem_edgeEnds, hx_eB]
        have hmem_core := hPart_ρ.2.2.1 x hx_edgeEnds
        have hbeq : B₀.bundleOf x = bun := (Finset.mem_filter.mp hx_ends).2
        rw [hbeq] at hmem_core
        exact hmem_core.2.symm
      exact ⟨hsrc'_mem, hanc_x.trans hsrc0⟩
    obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_succ_le hcard2)
    rcases Finset.mem_image.mp hw₁ with ⟨x₁, hx₁, rfl⟩
    rcases Finset.mem_image.mp hw₂ with ⟨x₂, hx₂, rfl⟩
    obtain ⟨hw₁_new, hw₁_anc⟩ := hsrc_anc x₁ hx₁
    obtain ⟨hw₂_new, hw₂_anc⟩ := hsrc_anc x₂ hx₂
    set r := B₀.parent bun
    have hex_diff : ∃ w ∈ R_new \ R_old, ancDecode anc w = r := by
      by_cases h1 : G'.src x₁ = r
      · have h2 : G'.src x₂ ≠ r := fun h => hne (h1.trans h.symm)
        refine ⟨G'.src x₂, Finset.mem_sdiff.mpr ⟨hw₂_new, fun hro => h2 ?_⟩, hw₂_anc⟩
        have h0 := hAnc_old (G'.src x₂) hro; dsimp only [anc] at hw₂_anc; rw [ancDecode, h0] at hw₂_anc; simpa using hw₂_anc
      · refine ⟨G'.src x₁, Finset.mem_sdiff.mpr ⟨hw₁_new, fun hro => h1 ?_⟩, hw₁_anc⟩
        have h0 := hAnc_old (G'.src x₁) hro; dsimp only [anc] at hw₁_anc; rw [ancDecode, h0] at hw₁_anc; simpa using hw₁_anc
    obtain ⟨w, hw_diff, hw_anc⟩ := hex_diff
    rcases List.mem_map.mp ((hAnc_diff w).mp (by rwa [← hRnew_V, ← hRold_V])) with ⟨p, hp, rfl⟩
    have hr_in : r ∈ oldRoots :=
      (hold_mem_iff r).mpr (by rw [hOldList_eq]; exact List.mem_map.mpr ⟨p, hp, hw_anc⟩)
    rw [List.mem_iff_getElem] at hr_in; rcases hr_in with ⟨gi, hgi, hgi_eq⟩
    have hgi' : gi < gs.length := by omega
    refine ⟨gi, hgi', fun x hx => ?_⟩
    obtain ⟨hx_new, hx_anc⟩ := hsrc_anc x hx
    rw [List.mem_toFinset, hgs_mem_iff gi hgi']
    by_cases hxr : G'.src x = r
    · exact Or.inl (hxr.trans hgi_eq.symm)
    · right
      refine ⟨Finset.mem_sdiff.mpr ⟨hx_new, fun hro => hxr ?_⟩, hx_anc.trans hgi_eq.symm⟩
      have h0 := hAnc_old (G'.src x) hro; dsimp only [anc] at hx_anc; rw [ancDecode, h0] at hx_anc; simpa using hx_anc

end

end MinCostFlow.SparseCore.Program
