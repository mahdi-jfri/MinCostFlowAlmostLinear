module

public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkCharge

/-!
# Branch-level walk potential change and total step bound (`AssemblyFirstWalkBound`)

Combines the per-pair `walkPot` step lemmas (`AssemblyFirstWalkPot.lean`), the spanner bank bound
(`AssemblyFirstWalkBank.lean`), the spanner charge bound (`AssemblyFirstWalkCharge.lean`), and the
newly-active pair init walk and bank bounds (`AssemblyFirstNewPairs.lean`) into the branch-level
step bounds:

* `walkPot_step_le`: `stepNewWalks + walkPot tr' ≤ walkPot tr + (reemb walks of all active' pairs)
  + (init walks of newlyActive pairs)`.
* `stepNewWalks_total_bound`: `stepNewWalks + walkPot tr' + bankAfter ≤ walkPot tr + bankBefore +
  branchStepCharge + 2 * (lazy init charge of newlyActive pairs)`.
* `stepNewWalks_total_bound_charge`: when `tr.lazyMachInitCost` equals the lazy init charge on each
  newly active component, `stepNewWalks + walkPot tr' + bankAfter ≤ walkPot tr + bankBefore +
  3 * branchStepCharge`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

/-- **Branch-level change of `walkPot`.** All new off-spanner walks of a step (`stepNewWalks`)
plus `walkPot tr'` are at most `walkPot tr`, plus the re-embedded walks of all active pairs of
`tr'`, plus the init walks of all newly active pairs. -/
theorem walkPot_step_le (P : DSParams) (tr : BundleTreeState P.L) (U : List Update)
    (ord ord' : ℕ → List End)
    (hL : 1 ≤ P.L)
    (hI : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ), CompLSFInv C_lsst ℓ₀ tr.cs)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hDynG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges)
    (hI' : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ),
      CompLSFInv C_lsst ℓ₀ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.cs)
    (hMod' : RestartScurModelInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG' : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.activeComps,
      ∀ b ∈ tr.activeBuckets C,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn (C, b)).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun (C, b)).edges)
    (d : Finset ℕ × ℤ → DSHist)
    (hOld : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (d (C, b)).state P = tr.dyn (C, b) ∧
      (d (C, b)).G₀.IsValid ∧ (d (C, b)).G₀.m ≤ P.mMax ∧
      (d (C, b)).G₀.BatchIsValid ((d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ∧
      (∀ u ∈ (d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b),
        isDelOrSplit u))
    (hNew : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').newlyActive,
      ∀ b ∈ tr.activeBuckets C,
      tr.dyn (C, b) = DSHist.state P ⟨tr.initBunG (C, b), []⟩ ∧
      (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P.mMax ∧
      (tr.initBunG (C, b)).BatchIsValid
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ∧
      (∀ u ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b),
        isDelOrSplit u)) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let tr' := info.state
    stepNewWalks sp tr U ord ord' + walkPot tr' ≤
      walkPot tr +
      (tr'.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)).sum fun e =>
          (piTotal (tr'.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) := by
  classical
  intro sp info tr'
  obtain ⟨C_lsst, ℓ₀, hI0⟩ := hI
  obtain ⟨C_lsst', ℓ₀', hI1⟩ := hI'
  have hDisj : Disjoint tr.activeComps info.newlyActive := Finset.disjoint_sdiff
  have hAct' : tr'.activeComps = tr.activeComps ∪ info.newlyActive := rfl
  have hActB' : tr'.activeBuckets = tr.activeBuckets := rfl
  rw [walkPot_eq_H_sum hI0 hMod hBD hDynG, walkPot_eq_H_sum hI1 hMod' hBD' hDynG', hAct', hActB',
    Finset.sum_union hDisj, Finset.sum_union hDisj]
  -- Old active pairs
  have hOldSum :
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        let p := (C, b)
        let R := updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)
        let L_p := (tr.S_cur.E \ tr'.S_cur.E) ∩ (tr'.dyn p).G.E
        ((R \ tr'.S_cur.E) ∪ L_p).sum fun e => (piTotal (tr'.dyn p) e).length) +
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr'.dyn (C, b)).H.E.sum fun e => (piTotal (tr'.dyn (C, b)) e).length) ≤
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.dyn (C, b)).H.E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) +
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)).sum fun e =>
          (piTotal (tr'.dyn (C, b)) e).length) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨hst, hVG₀, hGm₀, hBV, hds⟩ := hOld C hC b hb
    set p := (C, b)
    have hC' : C ∈ tr'.activeComps := Finset.mem_union_left _ hC
    have hH_eq := scur_inter_dynG_eq_dynH hI0 hMod hBD hC hb (hDynG C hC b hb)
    have hH'_eq := scur_inter_dynG_eq_dynH hI1 hMod' hBD' hC' hb (hDynG' C hC' b hb)
    have hst' : tr'.dyn p = (⟨(d p).G₀, (d p).Us ++ [info.U_B p]⟩ : DSHist).state P := by
      show (DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)).state = _
      rw [← hst, dsHist_append_state_eq_update]
    have hEnter : (tr'.dyn p).H.E \ (tr.dyn p).H.E ⊆
        updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
      rw [hst', ← hst]
      exact dsHist_H_sdiff_sub_updateReembSet P (d p) (info.U_B p) hVG₀ hL hGm₀ hBV hds
    have hSame : ∀ e ∈ (tr'.dyn p).G.E,
        e ∉ updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) →
        (piTotal (tr'.dyn p) e).length = (piTotal (tr.dyn p) e).length := by
      intro e he hnr
      rw [hst'] at he ⊢
      rw [← hst] at hnr ⊢
      rw [dsHist_piTotal_eq_of_not_mem_updateReembSet P (d p) (info.U_B p) hVG₀ hL hGm₀ hBV hds
        e he hnr]
    have hH'_sub : (tr'.dyn p).H.E ⊆ (tr'.dyn p).G.E := by
      rw [← hH'_eq]; exact Finset.inter_subset_right
    have hG'_sub : (tr'.dyn p).G.E ⊆ (tr.dyn p).G.E := by
      have hq1 : 1 ≤ (d p).q P := le_trans (by decide) (two_le_phaseBase _ _)
      have hInv1 := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
        hBV hds (d p).flat.length (by simp)).1.G_eq
      have hInv2 := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
        hBV hds ((d p).flat ++ info.U_B p).length le_rfl).1.G_eq
      rw [List.take_length] at hInv2
      have hG1 : (tr.dyn p).G = (d p).G₀.applyBatch (d p).flat := by
        rw [← hst]; unfold DSHist.state
        rw [runState_append (d p).G₀ ((d p).q P) (canonicalSparsify P.impl) (d p).flat (info.U_B p)
          (d p).flat.length le_rfl] at hInv1
        simpa [List.take_left] using hInv1
      have hG2 : (tr'.dyn p).G = (d p).G₀.applyBatch ((d p).flat ++ info.U_B p) := by
        rw [hst']
        change (runState (L := P.L) (d p).G₀ ((d p).q P) (canonicalSparsify P.impl)
            ((d p).Us ++ [info.U_B p]).flatten ((d p).Us ++ [info.U_B p]).flatten.length).G = _
        have hfl : ((d p).Us ++ [info.U_B p]).flatten = (d p).flat ++ info.U_B p :=
          dsHist_flat_append (d p) (info.U_B p)
        rw [hfl]
        exact hInv2
      rw [hG1, hG2, applyBatch_append]
      exact applyBatch_E_subset_of_delOrSplit _ _ fun u hu => hds u (List.mem_append_right _ hu)
    have hRsub : updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) ⊆
        (tr'.dyn p).G.E := by
      have hmatch : ∀ (i : ℕ) (hi : i < (info.U_B p).length),
          ((d p).flat ++ info.U_B p)[(d p).flat.length + i]? = some ((info.U_B p)[i]'hi) := by
        intro i hi
        simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem hi
      have hst_eq : tr.dyn p = runState (L := P.L) (d p).G₀ ((d p).q P) (canonicalSparsify P.impl)
          ((d p).flat ++ info.U_B p) (d p).flat.length := by
        rw [← hst, runState_append (d p).G₀ ((d p).q P) (canonicalSparsify P.impl)
          (d p).flat (info.U_B p) (d p).flat.length le_rfl]; rfl
      have hst'_eq : tr'.dyn p = runState (L := P.L) (d p).G₀ ((d p).q P) (canonicalSparsify P.impl)
          ((d p).flat ++ info.U_B p) ((d p).flat.length + (info.U_B p).length) := by
        rw [hst']; simp only [DSHist.state, dsHist_flat_append, List.length_append]; rfl
      rw [hst_eq, hst'_eq, updateReembSet_run_eq (d p).G₀ ((d p).flat ++ info.U_B p)
        (info.U_B p) (d p).flat.length hmatch]
      exact Finset.inter_subset_right
    have hSetEq :
        ((updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) \ tr'.S_cur.E) ∪
          ((tr.S_cur.E \ tr'.S_cur.E) ∩ (tr'.dyn p).G.E)) =
        ((updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) \ (tr'.dyn p).H.E) ∪
          (((tr.dyn p).H.E \ (tr'.dyn p).H.E) ∩ (tr'.dyn p).G.E)) := by
      ext e
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      have hiff1 : e ∈ (tr'.dyn p).G.E → (e ∈ tr'.S_cur.E ↔ e ∈ (tr'.dyn p).H.E) := fun heG' =>
        ⟨fun h => hH'_eq ▸ Finset.mem_inter.mpr ⟨h, heG'⟩,
         fun h => (Finset.mem_inter.mp (hH'_eq.symm ▸ h)).1⟩
      have hiff0 : e ∈ (tr'.dyn p).G.E → (e ∈ tr.S_cur.E ↔ e ∈ (tr.dyn p).H.E) := fun heG' =>
        ⟨fun h => hH_eq ▸ Finset.mem_inter.mpr ⟨h, hG'_sub heG'⟩,
         fun h => (Finset.mem_inter.mp (hH_eq.symm ▸ h)).1⟩
      constructor
      · rintro (⟨hR, hnS'⟩ | ⟨⟨hS, hnS'⟩, hG'⟩)
        · exact Or.inl ⟨hR, fun hH' => hnS' ((hiff1 (hRsub hR)).mpr hH')⟩
        · exact Or.inr ⟨⟨(hiff0 hG').mp hS, fun hH' => hnS' ((hiff1 hG').mpr hH')⟩, hG'⟩
      · rintro (⟨hR, hnH'⟩ | ⟨⟨hH, hnH'⟩, hG'⟩)
        · exact Or.inl ⟨hR, fun hS' => hnH' ((hiff1 (hRsub hR)).mp hS')⟩
        · exact Or.inr ⟨⟨(hiff0 hG').mpr hH, fun hS' => hnH' ((hiff1 hG').mp hS')⟩, hG'⟩
    dsimp only
    rw [hSetEq]
    exact walkPot_old_pair_step hH'_sub hEnter hSame
  -- Newly active pairs
  have hNewSum :
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        ((tr'.dyn (C, b)).G.E \ tr'.S_cur.E).sum fun e => (piTotal (tr'.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr'.dyn (C, b)).H.E.sum fun e => (piTotal (tr'.dyn (C, b)) e).length) ≤
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)).sum fun e =>
          (piTotal (tr'.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨hst0, hVG₀, hGm₀, hBV, hds⟩ := hNew C hC b hb
    set p := (C, b)
    set d0 : DSHist := ⟨tr.initBunG p, []⟩
    have hC' : C ∈ tr'.activeComps := Finset.mem_union_right _ hC
    have hH'_eq := scur_inter_dynG_eq_dynH hI1 hMod' hBD' hC' hb (hDynG' C hC' b hb)
    have hH'_sub : (tr'.dyn p).H.E ⊆ (tr'.dyn p).G.E := by
      rw [← hH'_eq]; exact Finset.inter_subset_right
    have hst' : tr'.dyn p = (⟨tr.initBunG p, [info.U_B p]⟩ : DSHist).state P := by
      show (DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)).state = _
      rw [hst0]
      exact (dsHist_append_state_eq_update P d0 (info.U_B p)).symm
    have hG'_sub : (tr'.dyn p).G.E ⊆ (tr.initBunG p).E := by
      have hq1 : 1 ≤ d0.q P := le_trans (by decide) (two_le_phaseBase _ _)
      have hInv2 := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
        hBV hds (info.U_B p).length le_rfl).1.G_eq
      have hG2 : (tr'.dyn p).G = (tr.initBunG p).applyBatch (info.U_B p) := by
        rw [hst']; simp only [DSHist.state, DSHist.flat, List.flatten_cons, List.flatten_nil,
          List.append_nil]
        rw [List.take_length] at hInv2
        exact hInv2
      rw [hG2]
      exact applyBatch_E_subset_of_delOrSplit _ _ hds
    have hSame : ∀ e ∈ (tr'.dyn p).G.E,
        e ∉ updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) →
        (piTotal (tr'.dyn p) e).length = (piTotal (tr.dyn p) e).length := by
      intro e he hnr
      have hflat0 : d0.flat ++ info.U_B p = info.U_B p := by simp [d0, DSHist.flat]
      have h1 := dsHist_piTotal_eq_of_not_mem_updateReembSet P d0 (info.U_B p) hVG₀ hL hGm₀
        (by rwa [hflat0]) (by rwa [hflat0])
      rw [hst'] at he ⊢
      rw [hst0] at hnr ⊢
      exact congrArg List.length (h1 e he hnr)
    have hSetEq : (tr'.dyn p).G.E \ tr'.S_cur.E = (tr'.dyn p).G.E \ (tr'.dyn p).H.E := by
      ext e
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨heG', hnS'⟩
        exact ⟨heG', fun heH' => hnS' (Finset.mem_inter.mp (hH'_eq ▸ heH')).1⟩
      · rintro ⟨heG', hnH'⟩
        exact ⟨heG', fun heS' => hnH' (hH'_eq ▸ Finset.mem_inter.mpr ⟨heS', heG'⟩)⟩
    rw [hSetEq]
    exact walkPot_new_pair_step hG'_sub hH'_sub hSame
  dsimp only [stepNewWalks, tr', info, sp] at hOldSum hNewSum ⊢
  omega

/-- **Total walk and potential bound of one branch step.** All new off-spanner walks of the step,
plus `walkPot tr'` and the new spanner banks, are at most `walkPot tr`, plus the old spanner banks,
plus `branchStepCharge`, plus twice the lazy init charge of the newly active pairs. -/
theorem stepNewWalks_total_bound (P : DSParams) (tr : BundleTreeState P.L) (U : List Update)
    (ord ord' : ℕ → List End)
    (hL : 1 ≤ P.L) (hp : 1 ≤ max P.impl.p_s P.impl.p_t)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hConst : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound)
    (hI : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ), CompLSFInv C_lsst ℓ₀ tr.cs)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hDynG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges)
    (hI' : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ),
      CompLSFInv C_lsst ℓ₀ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.cs)
    (hMod' : RestartScurModelInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG' : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.activeComps,
      ∀ b ∈ tr.activeBuckets C,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn (C, b)).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun (C, b)).edges)
    (d : Finset ℕ × ℤ → DSHist)
    (hOld : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (d (C, b)).G₀ = tr.initBunG (C, b) ∧
      (d (C, b)).state P = tr.dyn (C, b) ∧
      (d (C, b)).G₀.IsValid ∧ (d (C, b)).G₀.m ≤ P.mMax ∧
      (d (C, b)).G₀.BatchIsValid ((d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ∧
      (∀ u ∈ (d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b),
        isDelOrSplit u) ∧
      batchSplitCount ((d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ≤
        P.splitBound)
    (hNew : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').newlyActive,
      ∀ b ∈ tr.activeBuckets C,
      tr.dyn (C, b) = DSHist.state P ⟨tr.initBunG (C, b), []⟩ ∧
      (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P.mMax ∧
      (tr.initBunG (C, b)).BatchIsValid
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ∧
      (∀ u ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b),
        isDelOrSplit u) ∧
      batchSplitCount
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ≤
        P.splitBound) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let tr' := info.state
    let bankBefore := tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b => (d (C, b)).bank P
    let bankAfter :=
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (⟨(d (C, b)).G₀, (d (C, b)).Us ++ [info.U_B (C, b)]⟩ : DSHist).bank P) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (⟨tr.initBunG (C, b), [info.U_B (C, b)]⟩ : DSHist).bank P)
    stepNewWalks sp tr U ord ord' + walkPot tr' + bankAfter ≤
      walkPot tr + bankBefore + branchStepCharge sp tr U ord ord' +
      2 * (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) := by
  classical
  intro sp info tr' bankBefore bankAfter
  have hc1 : 1 ≤ tr.spanConst := le_trans (one_le_dsAmortConst P.impl) hConst
  have hstep := walkPot_step_le P tr U ord ord' hL hI hMod hBD hDynG hI' hMod' hBD' hDynG' d
    (fun C hC b hb => by obtain ⟨-, h2, h3, h4, h5, h6, -⟩ := hOld C hC b hb; exact ⟨h2, h3, h4, h5, h6⟩)
    (fun C hC b hb => by obtain ⟨h1, h2, h3, h4, h5, -⟩ := hNew C hC b hb; exact ⟨h1, h2, h3, h4, h5⟩)
  dsimp only at hstep
  have hDisj : Disjoint tr.activeComps info.newlyActive := Finset.disjoint_sdiff
  have hAct' : tr'.activeComps = tr.activeComps ∪ info.newlyActive := rfl
  have hBankOld :
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)).sum fun e =>
          (piTotal (tr'.dyn (C, b)) e).length) +
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (⟨(d (C, b)).G₀, (d (C, b)).Us ++ [info.U_B (C, b)]⟩ : DSHist).bank P) ≤
      bankBefore +
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        spanBatchChargeWith tr.spanConst tr.spanParams P.L
          ((tr.initBunG (C, b)).n + tr.splitBound) (tr.initBunG (C, b)) (tr.dyn (C, b)).G
          (info.U_B (C, b))) := by
    dsimp only [bankBefore]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨hG₀eq, hst, hVG₀, hGm₀, hBV, hds, hspl⟩ := hOld C hC b hb
    set p := (C, b)
    have hst' : tr'.dyn p = (⟨(d p).G₀, (d p).Us ++ [info.U_B p]⟩ : DSHist).state P := by
      show (DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)).state = _
      rw [← hst, dsHist_append_state_eq_update]
    have hGeq : (d p).G₀.applyBatch (d p).flat = (tr.dyn p).G := by
      have hq1 : 1 ≤ (d p).q P := le_trans (by decide) (two_le_phaseBase _ _)
      have hI0 := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
        hBV hds (d p).flat.length (by simp)).1.G_eq
      rw [← hst]; unfold DSHist.state
      rw [runState_append (d p).G₀ ((d p).q P) (canonicalSparsify P.impl) (d p).flat (info.U_B p)
        (d p).flat.length le_rfl] at hI0
      simpa [List.take_left] using hI0.symm
    have hwb := dsHist_reemb_walks_add_bank_le P (d p) (info.U_B p) hVG₀ hL hGm₀ hBV hds hspl hp
    have hch := dsBatchCharge_le_spanBatchChargeWith P.impl P.mMax P.L
      ((d p).G₀.n + P.splitBound) (d p).G₀ ((d p).G₀.applyBatch (d p).flat) (info.U_B p) hConst hP
    have h1 := le_trans hwb (Nat.add_le_add_left hch _)
    rw [hst, ← hst', hGeq, hG₀eq, hSB] at h1
    simpa only [hG₀eq] using h1
  have hBankNew :
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)).sum fun e =>
          (piTotal (tr'.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (⟨tr.initBunG (C, b), [info.U_B (C, b)]⟩ : DSHist).bank P) ≤
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        spanBatchChargeWith tr.spanConst tr.spanParams P.L
          ((tr.initBunG (C, b)).n + tr.splitBound) (tr.initBunG (C, b)) (tr.dyn (C, b)).G
          (info.U_B (C, b))) +
      2 * (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨hst0, hVG₀, hGm₀, hBV, hds, hspl⟩ := hNew C hC b hb
    set p := (C, b)
    set Hb := tr.initBunG p
    set d0 : DSHist := ⟨Hb, []⟩
    have hflat0 : d0.flat ++ info.U_B p = info.U_B p := by simp [d0, DSHist.flat]
    have hst' : tr'.dyn p = (⟨Hb, [info.U_B p]⟩ : DSHist).state P := by
      show (DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)).state = _
      rw [hst0]
      exact (dsHist_append_state_eq_update P d0 (info.U_B p)).symm
    have hGeq : Hb.applyBatch d0.flat = (tr.dyn p).G := by
      rw [hst0, dsHist_state_nil]; rfl
    have hwb := dsHist_reemb_walks_add_bank_le P d0 (info.U_B p) hVG₀ hL hGm₀
      (by rwa [hflat0]) (by rwa [hflat0]) (by rwa [hflat0]) hp
    have hbank0 : d0.bank P = dsInitBank P Hb := dsHist_nil_bank_eq_dsInitBank P Hb
    have hbank0_le : dsInitBank P Hb ≤
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound Hb :=
      le_trans (dsInitBank_le_mul_spanInitBound P hVG₀ hGm₀)
        (Nat.mul_le_mul hConst (spanInitBound_mono (L := P.L) hP (le_of_eq hSB) Hb))
    have hinit_le : Hb.E.sum (fun e => (piTotal (tr.dyn p) e).length) ≤
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound Hb := by
      rw [hst0]
      exact le_trans (init_walks_le_spanInitBound P hVG₀ hGm₀)
        (le_trans (spanInitBound_mono (L := P.L) hP (le_of_eq hSB) Hb)
          (Nat.le_mul_of_pos_left _ hc1))
    have hch := dsBatchCharge_le_spanBatchChargeWith P.impl P.mMax P.L
      (Hb.n + P.splitBound) Hb (Hb.applyBatch d0.flat) (info.U_B p) hConst hP
    have hwb' := le_trans hwb (Nat.add_le_add_left hch _)
    rw [hbank0, ← hst0, hSB, hGeq] at hwb'
    change (updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)).sum
          (fun e => (piTotal ((⟨Hb, [info.U_B p]⟩ : DSHist).state P) e).length) +
        (⟨Hb, [info.U_B p]⟩ : DSHist).bank P ≤
        dsInitBank P Hb + spanBatchChargeWith tr.spanConst tr.spanParams P.L
          (Hb.n + tr.splitBound) Hb (tr.dyn p).G (info.U_B p) at hwb'
    rw [← hst'] at hwb'
    omega
  have hSpanCh := spanCharges_le_branchStepCharge sp tr U ord ord'
  rw [hAct', Finset.sum_union hDisj] at hSpanCh
  change stepNewWalks sp tr U ord ord' + walkPot tr' ≤
      walkPot tr +
      (tr'.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)).sum fun e =>
          (piTotal (tr'.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) at hstep
  rw [hAct', Finset.sum_union hDisj] at hstep
  dsimp only [bankAfter, bankBefore, tr', info, sp] at hstep hBankOld hBankNew hSpanCh ⊢
  omega

/-- **Total bound against `3 * branchStepCharge` alone**, when `tr.lazyMachInitCost` equals the
lazy init charge on each newly active component (as holds along every run). -/
theorem stepNewWalks_total_bound_charge (P : DSParams) (tr : BundleTreeState P.L) (U : List Update)
    (ord ord' : ℕ → List End)
    (hL : 1 ≤ P.L) (hp : 1 ≤ max P.impl.p_s P.impl.p_t)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound)
    (hI : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ), CompLSFInv C_lsst ℓ₀ tr.cs)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hDynG : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges)
    (hI' : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ),
      CompLSFInv C_lsst ℓ₀ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.cs)
    (hMod' : RestartScurModelInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG' : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.activeComps,
      ∀ b ∈ tr.activeBuckets C,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn (C, b)).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun (C, b)).edges)
    (hLazy : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').newlyActive,
      ((tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) ≤
          tr.lazyMachInitCost C)
    (d : Finset ℕ × ℤ → DSHist)
    (hOld : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (d (C, b)).G₀ = tr.initBunG (C, b) ∧
      (d (C, b)).state P = tr.dyn (C, b) ∧
      (d (C, b)).G₀.IsValid ∧ (d (C, b)).G₀.m ≤ P.mMax ∧
      (d (C, b)).G₀.BatchIsValid ((d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ∧
      (∀ u ∈ (d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b),
        isDelOrSplit u) ∧
      batchSplitCount ((d (C, b)).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ≤
        P.splitBound)
    (hNew : ∀ C ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').newlyActive,
      ∀ b ∈ tr.activeBuckets C,
      tr.dyn (C, b) = DSHist.state P ⟨tr.initBunG (C, b), []⟩ ∧
      (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P.mMax ∧
      (tr.initBunG (C, b)).BatchIsValid
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ∧
      (∀ u ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b),
        isDelOrSplit u) ∧
      batchSplitCount
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B (C, b)) ≤
        P.splitBound) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let tr' := info.state
    let bankBefore := tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b => (d (C, b)).bank P
    let bankAfter :=
      (tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (⟨(d (C, b)).G₀, (d (C, b)).Us ++ [info.U_B (C, b)]⟩ : DSHist).bank P) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (⟨tr.initBunG (C, b), [info.U_B (C, b)]⟩ : DSHist).bank P)
    stepNewWalks sp tr U ord ord' + walkPot tr' + bankAfter ≤
      walkPot tr + bankBefore + 3 * branchStepCharge sp tr U ord ord' := by
  intro sp info tr' bankBefore bankAfter
  have h1 := stepNewWalks_total_bound P tr U ord ord' hL hp hP hC hSB hI hMod hBD hDynG
    hI' hMod' hBD' hDynG' d hOld hNew
  dsimp only at h1
  have h2 : (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) ≤
      info.newlyActive.sum fun C => tr.lazyMachInitCost C :=
    Finset.sum_le_sum fun C hC => hLazy C hC
  have h3 := lazyMachInitCost_sum_le_branchStepCharge sp tr U ord ord'
  dsimp only [bankBefore, bankAfter, tr', info, sp] at h1 h2 h3 ⊢
  omega

end

end MinCostFlow.SparseCore.Program
