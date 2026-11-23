module

public import MinCostFlow.SparseCore.Program.AssemblyInputRun

import MinCostFlow.Chain.BundleRestartInv
import MinCostFlow.SparseCore.Program.RestartModelInv
import MinCostFlow.SparseCore.Program.SpanBridge
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.DynSpanner.Program.CanonicalSparsify

/-!
# Branch model invariants and update-count bounds from `SparseCoreOrdInput` (`AssemblyInputInv`)

Proves `asm_input_model_inv`: every nonempty state reachable under `SparseCoreOrdInput` for
`sparseCoreBundleRestartToolMachWith` (with `1 ≤ depth`, `impl.γ_t M = 1`, vertex/edge bounds
`< vCap, < eCap`, and `IsValidLSFInitFor lsfInit C_lsst k j`) satisfies both
`AsmBrModelFacts impl vCap eCap tr ord` (`AssemblyBranchFacts.lean`) and
`BranchUpdatesBelow impl tr n`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.LSF
open MinCostFlow.SparseCore.Program.Restart

private lemma updateGo_state_eq_runState {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us : List Update) :
    ∀ (U : List Update) (k₀ : ℕ) (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      (∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      (DynSpanner.updateGo sparsify (DynSpanner.runState (L := L) G₀ q sparsify us k₀) U uhAcc dAcc cAcc).state =
        DynSpanner.runState (L := L) G₀ q sparsify us (k₀ + U.length)
  | [], k₀, _, _, _, _ => by simp [DynSpanner.updateGo]
  | u :: U, k₀, uhAcc, dAcc, cAcc, hget => by
    have h0 : us[k₀]? = some u := by simpa using hget 0 (Nat.succ_pos _)
    have hstep : (DynSpanner.step (DynSpanner.runState (L := L) G₀ q sparsify us k₀) u sparsify).state =
        DynSpanner.runState (L := L) G₀ q sparsify us (k₀ + 1) := by
      simp [DynSpanner.runState, h0]
    simp only [DynSpanner.updateGo, hstep]
    rw [updateGo_state_eq_runState G₀ q sparsify us U (k₀ + 1) _ _ _ (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hget (i + 1) (Nat.succ_lt_succ hi))]
    simp [Nat.add_assoc, Nat.add_comm 1 U.length]

private lemma runBatchState_eq_runState {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (Us : List (List Update)) :
    ∀ t ≤ Us.length,
      DynSpanner.runBatchState (L := L) G₀ q sparsify Us t =
        DynSpanner.runState (L := L) G₀ q sparsify Us.flatten (Us.take t).flatten.length
  | 0, _ => by simp [DynSpanner.runBatchState, DynSpanner.runState]
  | t + 1, ht => by
    have hlt : t < Us.length := Nat.lt_of_succ_le ht
    have hsome : Us[t]? = some (Us[t]'hlt) := List.getElem?_eq_getElem hlt
    have htake : Us.take (t + 1) = Us.take t ++ [Us[t]'hlt] :=
      List.take_add_one.trans (by simp [hsome])
    have hflat_split : Us.flatten = (Us.take t).flatten ++ (Us[t]'hlt ++ (Us.drop (t + 1)).flatten) := by
      have h1 : Us.flatten = (Us.take (t + 1) ++ Us.drop (t + 1)).flatten :=
        congrArg List.flatten (List.take_append_drop (t + 1) Us).symm
      rw [h1, htake, List.flatten_append, List.flatten_append, List.flatten_singleton, List.append_assoc]
    simp only [DynSpanner.runBatchState, hsome, runBatchState_eq_runState G₀ q sparsify Us t (Nat.le_of_lt hlt),
      DynSpanner.update]
    rw [updateGo_state_eq_runState G₀ q sparsify Us.flatten (Us[t]'hlt) (Us.take t).flatten.length _ _ _
      (fun i hi => by
        rw [hflat_split, List.getElem?_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi])]
    rw [htake, List.flatten_append, List.flatten_singleton, List.length_append]

private lemma foldl_restart_initBunG_inactive {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {j : ℕ} {C : Finset ℕ} {b : ℤ} :
    ∀ (xs : List ℕ) (st : SparseCoreBundleState depth),
      C ∉ (st.trees j).activeComps →
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl)).restart st).trees j).initBunG (C, b) =
        (st.trees j).initBunG (C, b)
  | [], _, _ => rfl
  | x :: xs, st, hna => by
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    have hf1 := (foldl_bundleRestart_props lsfInit C_lsst depth
      (fun _ => canonicalSparsify impl) st [x]).2.2.2.2.1 j
    dsimp only [List.foldl] at hf1 ⊢
    rw [foldl_restart_initBunG_inactive xs (Tb.restart st x) (by rw [hf1.activeComps]; exact hna)]
    dsimp only [Tb]; rw [sparseCoreBundleRestartTool_restart_eq]
    split_ifs with hne'
    · by_cases hjx : j = x
      · subst hjx; simp [Function.update_self, restartBundleTree, hna]
      · simp [Function.update_of_ne hjx]
    · rfl

private lemma foldl_restart_initBunG_eq {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {j : ℕ} {C : Finset ℕ} {b : ℤ} :
    ∀ (xs : List ℕ) (st : SparseCoreBundleState depth),
      st.isNonempty = true →
      (st.trees j).initBunG (C, b) = normGraph ((st.trees j).bun (C, b)).graph →
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl)).restart st).trees j).initBunG (C, b) =
        normGraph (((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl)).restart st).trees j).bun (C, b)).graph
  | [], _, _, h => h
  | x :: xs, st, hst_ne, hst_ig => by
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    refine foldl_restart_initBunG_eq xs (Tb.restart st x) ?_ ?_
    · dsimp only [Tb]; rw [sparseCoreBundleRestartTool_restart_eq]; simp [hst_ne]
    · dsimp only [Tb]; rw [sparseCoreBundleRestartTool_restart_eq]; simp only [hst_ne, ↓reduceIte]
      by_cases hjx : j = x
      · subst hjx; simp only [Function.update_self, restartBundleTree]
        split_ifs <;> [rfl; exact hst_ig]
      · simp only [Function.update_of_ne hjx]; exact hst_ig

private lemma foldl_restart_initBunG_active {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {j : ℕ} {C : Finset ℕ} {b : ℤ} :
    ∀ (xs : List ℕ) (st : SparseCoreBundleState depth),
      st.isNonempty = true → C ∈ (st.trees j).activeComps → j ∈ xs →
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl)).restart st).trees j).initBunG (C, b) =
        normGraph (((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl)).restart st).trees j).bun (C, b)).graph
  | [], _, _, _, h => by cases h
  | x :: xs, st, hst_ne, hst_act, hmem => by
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    have hx_ne : (Tb.restart st x).isNonempty = true := by
      dsimp only [Tb]; rw [sparseCoreBundleRestartTool_restart_eq]; simp [hst_ne]
    have hf1 := (foldl_bundleRestart_props lsfInit C_lsst depth
      (fun _ => canonicalSparsify impl) st [x]).2.2.2.2.1 j
    dsimp only [List.foldl] at hf1 ⊢
    have hx_act : C ∈ ((Tb.restart st x).trees j).activeComps := by
      rw [hf1.activeComps]; exact hst_act
    rcases List.mem_cons.mp hmem with rfl | htail
    · have hbase : ((Tb.restart st j).trees j).initBunG (C, b) =
          normGraph (((Tb.restart st j).trees j).bun (C, b)).graph := by
        dsimp only [Tb]; rw [sparseCoreBundleRestartTool_restart_eq]
        simp only [hst_ne, ↓reduceIte, Function.update_self, restartBundleTree, hst_act, ↓reduceIte]
      exact foldl_restart_initBunG_eq xs (Tb.restart st j) hx_ne hbase
    · exact foldl_restart_initBunG_active xs (Tb.restart st x) hx_ne hx_act htail

/-- For every branch `j < k` of a nonempty state reachable by `SparseCoreOrdInput` (with
`1 ≤ depth`, `impl.γ_t M = 1`, vertex/edge bounds `< vCap, < eCap`, and
`IsValidLSFInitFor lsfInit C_lsst k j`), both `AsmBrModelFacts impl vCap eCap tr ord` and
`BranchUpdatesBelow impl tr n` hold. -/
theorem asm_input_model_inv
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {k M N vCap eCap : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth
      (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k) (hdepth : 1 ≤ depth) (hγt : impl.γ_t M = 1)
    (hvCap : ∀ x ∈ G.V, x < vCap) (heCap : ∀ e ∈ G.E, e < eCap)
    (hinp : SparseCoreOrdInput (sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth
      (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl))
      k M N s G ord n)
    (hne : SparseCoreBundleState.isNonempty (L := depth) s = true)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let tr := SparseCoreBundleState.trees (L := depth) s j
    AsmBrModelFacts impl vCap eCap tr ord ∧ BranchUpdatesBelow impl tr n := by
  classical
  intro tr
  set Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
  obtain ⟨_, _, hmn⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  obtain ⟨τ, D, ordSeq, restarts, hG₀, hM, hN, hℓ₀, hD, hOrd, hGτ, hordτ, hsum, hThr, hrun⟩ :=
    sparseCoreOrdInput_exists_run Tm hinp
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst depth
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
    k M N D ordSeq restarts τ).2.2
  rw [hrun] at hNM
  have hV₀ : (D.G 0).V.Nonempty := by
    have h1 := (runOrdAfterRestarts_isNonempty lsfInit C_lsst depth
      (fun _ => canonicalSparsify impl) k M N D ordSeq restarts τ).2.1
    rw [← hNM.isNonempty, hne] at h1
    exact of_decide_eq_true h1.symm
  have hSp : SparsifySpec M (canonicalSparsifyParams impl M).absorbTime (canonicalSparsify impl) :=
    canonicalSparsify_spec_absorb impl M
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit τ le_rfl
  have hSc := (runOrdAfterRestarts_S_cur_inv lsfInit C_lsst depth hdepth
    (canonicalSparsifyParams impl M).absorbTime (fun _ => canonicalSparsify impl)
    k M N τ hk D ordSeq restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit τ le_rfl).2
  set post := (Tb.runOrdAfterRestarts k M N D ordSeq restarts τ).trees j
  set pre := (Tb.runOrdAfterUpdate k M N D ordSeq restarts τ).1.trees j
  have hbf : BundleBaseFieldsEq post pre :=
    (foldl_bundleRestart_props lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (Tb.runOrdAfterUpdate k M N D ordSeq restarts τ).1 (restarts τ)).2.2.2.2.1 j
  have hEq : BundleNonMachEq tr post := hNM.trees j
  -- Align `post` with the last-restart epoch `s₀ := bundleLastRestart restarts j τ`.
  set s₀ := bundleLastRestart restarts j τ
  have hs₀ := bundleLastRestart_spec restarts j τ
  have hNoRest_lt : ∀ r, s₀ < r → r < τ → j ∉ restarts r := fun r h1 h2 => hs₀.2.2 r h1 h2.le
  set stEp := epochBundleSeq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    k M N D ordSeq restarts s₀ τ j
  have hpost_eq_ep : post = stEp (τ - s₀) := by
    have hEp := epochBundleSeq_eq_post lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      k M N D ordSeq restarts s₀ τ j hs₀.1
    by_cases hlt : s₀ < τ
    · exact (hEp.2.1 (Or.inl (hs₀.2.2 τ hlt le_rfl))).symm
    · exact (hEp.2.1 (Or.inr (by omega))).symm
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst depth hdepth
    (canonicalSparsifyParams impl M).absorbTime (fun _ => canonicalSparsify impl)
    k M N τ hk D ordSeq restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ τ j hInit hs₀.1 le_rfl
    hs₀.2.1 hNoRest_lt
  have hSplit := fun C (hC : C ∈ components (D.G 0)) (b : ℤ) =>
    epochBundleSeq_batchSplitCount_le_splitB lsfInit C_lsst depth hdepth
      (canonicalSparsifyParams impl M).absorbTime (fun _ => canonicalSparsify impl)
      k M N τ hk D ordSeq restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd (hsum.symm ▸ hThr)
      s₀ τ j hInit hs₀.1 le_rfl hs₀.2.1 hNoRest_lt hC b
  -- `initBunG` equals `normGraph ((stEp 0).bun (C, b)).graph` along the epoch.
  have hinitBunG_eq : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      post.initBunG (C, b) = normGraph ((stEp 0).bun (C, b)).graph := by
    intro C hC b
    have hstep_initG : ∀ δ ≤ τ - s₀, (stEp δ).initBunG (C, b) = (stEp 0).initBunG (C, b) := by
      intro δ hδ
      induction δ with
      | zero => rfl
      | succ d ih =>
        have hst := (epochBundleSeq_steps lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          k M N D ordSeq restarts hV₀ s₀ τ j hs₀.1 hNoRest_lt).2 d (by omega)
        dsimp only [stEp]
        rw [hst.1]
        exact ih (by omega)
    rw [hpost_eq_ep, hstep_initG (τ - s₀) le_rfl]
    have hst0 : stEp 0 = (Tb.runOrdAfterRestarts k M N D ordSeq restarts s₀).trees j := by
      have hne0 : ¬ (s₀ = τ ∧ s₀ < τ) := fun h => absurd h.1 (ne_of_lt h.2)
      simp [stEp, epochBundleSeq, Tb, hne0]
    rw [hst0]
    rcases hs₀.2.1 with hs0 | hj_mem
    · dsimp only [s₀]
      rw [hs0]
      exact foldl_restart_initBunG_eq (restarts 0) (Tb.runOrdAfterUpdate k M N D ordSeq restarts 0).1
        ((runOrdAfterRestarts_isNonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          k M N D ordSeq restarts 0).1.trans (decide_eq_true hV₀)) rfl
    · have hB0 := runOrdAfterRestarts_bun_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit s₀ hs₀.1
      by_cases hact : C ∈ ((Tb.runOrdAfterUpdate k M N D ordSeq restarts s₀).1.trees j).activeComps
      · exact foldl_restart_initBunG_active (restarts s₀)
          (Tb.runOrdAfterUpdate k M N D ordSeq restarts s₀).1
          ((runOrdAfterRestarts_isNonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
            k M N D ordSeq restarts s₀).1.trans (decide_eq_true hV₀)) hact hj_mem
      · have hbun_s0 : ((Tb.runOrdAfterRestarts k M N D ordSeq restarts s₀).trees j).bun (C, b) =
            (initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0) (D.ℓ 0)
              (ordSeq 0) j).bun (C, b) := (hB0.2.2.2.2.2.2.2.2.2.2.1 C hC hact).2 b |>.2.2.1
        have hinitG_inact : ∀ s, C ∉ ((Tb.runOrdAfterUpdate k M N D ordSeq restarts s).1.trees j).activeComps →
            ((Tb.runOrdAfterUpdate k M N D ordSeq restarts s).1.trees j).initBunG (C, b) =
              (initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0) (D.ℓ 0)
                (ordSeq 0) j).initBunG (C, b) ∧
            ((Tb.runOrdAfterRestarts k M N D ordSeq restarts s).trees j).initBunG (C, b) =
              (initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0) (D.ℓ 0)
                (ordSeq 0) j).initBunG (C, b) := by
          intro s
          induction s with
          | zero =>
            intro hna0
            exact ⟨rfl, foldl_restart_initBunG_inactive (restarts 0) _ hna0⟩
          | succ s ihs =>
            intro hna1
            have hne_s : (Tb.runOrdAfterRestarts k M N D ordSeq restarts s).isNonempty = true :=
              (runOrdAfterRestarts_isNonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
                k M N D ordSeq restarts s).2.1.trans (decide_eq_true hV₀)
            have hupd_eq : ((Tb.runOrdAfterUpdate k M N D ordSeq restarts (s + 1)).1.trees j) =
                (stepBundleTree (fun _ => canonicalSparsify impl)
                  ((Tb.runOrdAfterRestarts k M N D ordSeq restarts s).trees j)
                  (D.U (s + 1)) (Tb.runOrdAfterRestarts k M N D ordSeq restarts s).ord
                  (ordSeq (s + 1))).state := by
              rw [SparseCoreRestartTool.runOrdAfterUpdate_succ]
              dsimp only [Tb]
              rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_s]
            have hbf_s := (foldl_bundleRestart_props lsfInit C_lsst depth
              (fun _ => canonicalSparsify impl)
              (Tb.runOrdAfterUpdate k M N D ordSeq restarts s).1 (restarts s)).2.2.2.2.1 j
            have hna_s : C ∉ ((Tb.runOrdAfterUpdate k M N D ordSeq restarts s).1.trees j).activeComps := by
              intro hc
              apply hna1
              rw [hupd_eq]
              exact Finset.mem_union_left _ (hbf_s.activeComps.symm ▸ hc)
            have hpre_eq : ((Tb.runOrdAfterUpdate k M N D ordSeq restarts (s + 1)).1.trees j).initBunG (C, b) =
                (initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0) (D.ℓ 0)
                  (ordSeq 0) j).initBunG (C, b) := by
              rw [hupd_eq]; exact (ihs hna_s).2
            exact ⟨hpre_eq, (foldl_restart_initBunG_inactive (restarts (s + 1)) _ hna1).trans hpre_eq⟩
        rw [(hinitG_inact s₀ hact).2, hbun_s0]
        rfl
  -- Basic field equalities for `tr` and `post`.
  have hG₀_post : post.cs.G₀ = D.G 0 := by
    rw [hbf.cs, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hI_post : CompLSFInv C_lsst (D.ℓ 0) post.cs := hbf.cs.symm ▸ hBun.2.2.2.2.2.2.2.1
  have hG_post : post.cs.G = D.G τ := by rw [hbf.cs, hBun.2.2.2.2.2.2.2.2.1]
  obtain ⟨ρ_τ, hρ_τ⟩ := orderedUpTo_rot_at hOrd le_rfl hG_post
  have hρ_ord : ρ_τ.order = ord := hρ_τ.trans hordτ
  have hAct_sub : post.activeComps ⊆ components (D.G 0) :=
    hbf.activeComps ▸ hBun.2.2.2.2.2.2.2.2.2.1.2
  have hLarge_sub : largeComps k (D.G 0) ⊆ post.activeComps :=
    hbf.activeComps ▸ hBun.2.2.2.2.2.2.2.2.2.1.1
  have hst0_disj := (initBundleTreeWith_buckets_sum_le lsfInit depth (fun _ => canonicalSparsify impl)
    (M := M) (N := N) hk (G₀ := D.G 0) (D.ℓ 0) (ordSeq 0) j).2.2.2
  have hab_post : post.activeBuckets =
      (initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0) (D.ℓ 0)
        (ordSeq 0) j).activeBuckets := hbf.activeBuckets.trans hBun.2.2.2.2.1
  -- Prove `RestartScurModelInv post` and `AsmBunDisjointInv post`.
  have hRSMI_post : RestartScurModelInv post := by
    refine ⟨hG₀_post.symm ▸ hAct_sub, hSc.2.1, hab_post ▸ hSc.2.2.1, hSc.2.2.2, ?_⟩
    intro C hC b _
    have hC0 : C ∈ components (D.G 0) := hAct_sub hC
    have hcb := (hBun.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b
    have hE_eq : (post.bun (C, b)).edges = (pre.bun (C, b)).edges := hcb.2.2.2.1
    have hPart := hcb.2.1.1 ρ_τ hI_post.hG_val (compLSF_RF_isRSF hI_post) hρ_τ
    have hDynC := (hDyn C hC0 b).2.2.2.2.2.2.2.2.2.1 (τ - s₀) le_rfl
    have hpost_raw : epochBundleSeq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        k M N D ordSeq restarts s₀ τ j (τ - s₀) = post := hpost_eq_ep.symm
    rw [hpost_raw] at hDynC
    refine ⟨hPart.1, hcb.2.1.2.2, by rw [hbf.cs, hE_eq]; exact hcb.2.2.2.2.1,
      hDynC.2.2.2.1.2.1.trans (hDynC.2.1.2.1 ▸ Finset.Subset.rfl)⟩
  have hBD_post : BunDisjointInv post := by
    refine ⟨fun p₁ hp₁ p₂ hp₂ hne_p => ?_, fun p hp => ?_⟩
    · have hC₁ : p₁.1 ∈ components (D.G 0) := hAct_sub (mem_activePairs.mp hp₁).1
      have hC₂ : p₂.1 ∈ components (D.G 0) := hAct_sub (mem_activePairs.mp hp₂).1
      have hsub₁ : (post.bun p₁).edges ⊆
          ((initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0)
            (D.ℓ 0) (ordSeq 0) j).bun p₁).edges := by
        rw [((hBun.2.2.2.2.2.2.2.2.2.2.2 p₁.1 hC₁).2 p₁.2).2.2.2.1,
          ((hBun.2.2.2.2.2.2.2.2.2.2.2 p₁.1 hC₁).2 p₁.2).2.2.1]
        exact Finset.sdiff_subset
      have hsub₂ : (post.bun p₂).edges ⊆
          ((initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl) k M N (D.G 0)
            (D.ℓ 0) (ordSeq 0) j).bun p₂).edges := by
        rw [((hBun.2.2.2.2.2.2.2.2.2.2.2 p₂.1 hC₂).2 p₂.2).2.2.2.1,
          ((hBun.2.2.2.2.2.2.2.2.2.2.2 p₂.1 hC₂).2 p₂.2).2.2.1]
        exact Finset.sdiff_subset
      exact Disjoint.mono hsub₁ hsub₂ (hst0_disj p₁.1 hC₁ p₂.1 hC₂ p₁.2 p₂.2 hne_p)
    · have hC : p.1 ∈ components (D.G 0) := hAct_sub (mem_activePairs.mp hp).1
      have hcb := (hBun.2.2.2.2.2.2.2.2.2.2.2 p.1 hC).2 p.2
      have hdisj_ins : Disjoint (post.bun p).edges post.cs.insertedGlobal := by
        rw [hbf.cs, hcb.2.2.2.1]; exact hcb.2.2.2.2.1
      exact Disjoint.mono_right hI_post.hCross_sub hdisj_ins
  -- Transport `AsmBrModelFacts` from `post` to `tr` via `hEq : BundleNonMachEq tr post`.
  have htr_k : tr.k = k := hEq.k.trans (hbf.k.trans hBun.1)
  have htr_m₀ : tr.m₀ = M := (hmn j).1
  have htr_n₀ : tr.n₀ = N := (hmn j).2.1
  have htr_extra : tr.extraEdges = post.extraEdges := by
    funext C
    unfold BundleTreeState.extraEdges
    rw [hEq.cs, hEq.bun, hEq.activeBuckets]
  have hScur_sub_G : post.S_cur.E ⊆ post.cs.G.E := by
    intro e he
    rw [hRSMI_post.2.2.1] at he
    rcases Finset.mem_union.mp he with h1 | hcross
    · rcases Finset.mem_union.mp h1 with hH | hEx
      · rcases Finset.mem_biUnion.mp hH with ⟨C, hC, hbE⟩
        rcases Finset.mem_biUnion.mp hbE with ⟨b, hb, heH⟩
        have hcb := hRSMI_post.2.2.2.2 C hC b hb
        exact Finset.sdiff_subset (hcb.1 (hcb.2.2.2 heH))
      · rcases Finset.mem_biUnion.mp hEx with ⟨C, hC, heEx⟩
        unfold BundleTreeState.extraEdges at heEx
        exact hI_post.hCE_sub C (hG₀_post.symm ▸ hAct_sub hC) (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heEx).1).1
    · exact hI_post.hIns_sub (hI_post.hCross_sub hcross)
  have htr_G : tr.cs.G = G := by rw [hEq.cs, hG_post, hGτ]
  have hFacts : AsmBrModelFacts impl vCap eCap tr ord := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hcsG : post.cs.G = tr.cs.G := congrArg CompLSFState.G hEq.cs.symm
      have hord_cast : ∀ {G₁ G₂ : MGraph} (h : G₁ = G₂) (ρ : Rotation G₁),
          (h ▸ ρ : Rotation G₂).order = ρ.order := fun h ρ => by cases h; rfl
      exact ⟨C_lsst, D.ℓ 0, hEq.cs.symm ▸ hI_post, hcsG ▸ ρ_τ, (hord_cast hcsG ρ_τ).trans hρ_ord⟩
    · unfold RestartScurModelInv at hRSMI_post ⊢
      rw [hEq.activeComps, hEq.cs, hEq.S_cur, hEq.activeBuckets, hEq.dyn, hEq.bun, htr_extra]
      exact hRSMI_post
    · unfold BunDisjointInv activePairs at hBD_post ⊢
      rw [hEq.activeComps, hEq.activeBuckets, hEq.bun, hEq.cs]
      exact hBD_post
    · rw [hEq.S_cur]; exact hSc.1
    · rw [htr_m₀, (hmn j).2.2.2.1, canonicalSparsifyParams_absorbTime_eq_of_unit impl M hγt]
      exact sparsifyParamsLe_refl _
    · rw [(hmn j).2.2.2.2]
    · intro x hx; rw [htr_G] at hx; exact hvCap x hx
    · intro e he; rw [htr_G] at he; exact heCap e he
    · intro e he
      rw [hEq.S_cur] at he
      exact heCap e (hGτ ▸ hG_post ▸ hScur_sub_G he)
  -- Prove `BranchUpdatesBelow impl tr n`.
  have hUpd : BranchUpdatesBelow impl tr n := by
    refine ⟨by rw [htr_k, htr_m₀, htr_n₀]; exact hThr, fun C hC b => ?_⟩
    have hC0 : C ∈ components (D.G 0) := by rwa [hEq.cs, hG₀_post] at hC
    have hDC := hDyn C hC0 b
    set Hb := ((stEp 0).bun (C, b)).graph
    set Us_ep : List (List Update) := (List.range (τ - s₀)).map fun r =>
      (stepBundleTree (fun _ => canonicalSparsify impl) (stEp r) (D.U (s₀ + r + 1))
        (ordSeq (s₀ + r)) (ordSeq (s₀ + r + 1))).U_B (C, b)
    set us := Us_ep.flatten
    have hG₀_eq : tr.initBunG (C, b) = normGraph Hb := hEq.initBunG ▸ hinitBunG_eq C hC0 b
    have hst_eq : tr.dyn (C, b) =
        DynSpanner.runState (L := depth) (normGraph Hb) (phaseBase (Hb.n + bundleSplitBudget k M) depth)
          (canonicalSparsify impl) us us.length := by
      have h1 := (hDC.2.2.2.2.2.2.2.2.2.1 (τ - s₀) le_rfl).1
      have hpost_raw : epochBundleSeq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          k M N D ordSeq restarts s₀ τ j (τ - s₀) = post := hpost_eq_ep.symm
      rw [hpost_raw] at h1
      rw [hEq.dyn, h1]
      have hlen : Us_ep.length = τ - s₀ := by simp [Us_ep]
      have hrb := runBatchState_eq_runState (L := depth) (normGraph Hb)
        (phaseBase (Hb.n + bundleSplitBudget k M) depth) (canonicalSparsify impl) Us_ep (τ - s₀) hlen.ge
      rw [← hlen, List.take_length] at hrb
      change DynSpanner.runBatchState (L := depth) (normGraph Hb)
        (phaseBase (Hb.n + bundleSplitBudget k M) depth) (canonicalSparsify impl) Us_ep (τ - s₀) = _
      rw [← hlen]
      exact hrb
    have hBV_norm : (normGraph Hb).BatchIsValid us :=
      batchIsValid_of_graphEq (graphEq_symm (normGraph_graphEq Hb)) hDC.2.2.2.2.2.1
    have hds_us : ∀ u ∈ us, isDelOrSplit u := hDC.2.2.2.2.2.2.1
    obtain ⟨ht_eq, hG_eq⟩ := runState_t_and_G (L := depth) (normGraph Hb)
      (phaseBase (Hb.n + bundleSplitBudget k M) depth) (canonicalSparsify impl) us us.length le_rfl
    rw [List.take_length] at hG_eq
    obtain ⟨hn_le, hm_le, hsp_eq, hdl_eq, hlen_eq⟩ := delOrSplit_counts (normGraph Hb) us hBV_norm hds_us
    have hsp_le_sb : batchSplitCount us ≤ bundleSplitBudget k M := hSplit C hC0 b
    have hdel_le_n : us.countP deleteTag ≤ n := by
      have hsum_del : ∀ d ≤ τ - s₀,
          (((List.range d).map fun r =>
            (stepBundleTree (fun _ => canonicalSparsify impl) (stEp r) (D.U (s₀ + r + 1))
              (ordSeq (s₀ + r)) (ordSeq (s₀ + r + 1))).U_B (C, b)).flatten).countP deleteTag ≤
          (Finset.Icc (s₀ + 1) (s₀ + d)).sum (fun r => (D.U r).length) := by
        intro d
        induction d with
        | zero => intro _; simp
        | succ d ihd =>
          intro hd
          rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
            List.flatten_cons, List.flatten_nil, List.append_nil, List.countP_append]
          have hIcc : Finset.Icc (s₀ + 1) (s₀ + (d + 1)) =
              insert (s₀ + d + 1) (Finset.Icc (s₀ + 1) (s₀ + d)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
          have hstep_del : ((stepBundleTree (fun _ => canonicalSparsify impl) (stEp d)
              (D.U (s₀ + d + 1)) (ordSeq (s₀ + d)) (ordSeq (s₀ + d + 1))).U_B (C, b)).countP deleteTag ≤
              (D.U (s₀ + d + 1)).length := by
            have h1 := ((hDC.2.2.2.2.2.2.2.2.2.2 d (by omega)).2.2.2.2.1)
            exact le_trans h1 (le_trans (Finset.card_le_card Finset.inter_subset_right)
              (batchDeletes_card_le _))
          have hih := ihd (by omega)
          omega
      have hsub : Finset.Icc (s₀ + 1) (s₀ + (τ - s₀)) ⊆ Finset.Icc 1 τ := by
        intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
      calc us.countP deleteTag
          ≤ (Finset.Icc (s₀ + 1) (s₀ + (τ - s₀))).sum (fun r => (D.U r).length) := hsum_del (τ - s₀) le_rfl
        _ ≤ (Finset.Icc 1 τ).sum (fun r => (D.U r).length) :=
            Finset.sum_le_sum_of_subset hsub
        _ = n := hsum
    have hsp_le_112 : ((batchSplitCount us : ℕ) : ℝ) ≤
        112 * (n : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2 := by
      have hsc_R : batchSplitCount us ≤
          2 * (((stEp (τ - s₀)).cs.compSt C).R \ ((stEp 0).cs.compSt C).R).card :=
        hDC.2.2.2.2.2.2.2.1
      set cs₀ := (initBundleTreeWith lsfInit depth (fun _ => canonicalSparsify impl)
        k M N (D.G 0) (D.ℓ 0) (ordSeq 0) j).cs
      have hSt_base := (epochBundleSeq_steps lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        k M N D ordSeq restarts hV₀ s₀ τ j hs₀.1 hNoRest_lt).1
      have hR_le : ∀ r ≤ τ,
          ((((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl) k M N D ordSeq j r).1.cs.compSt C).R \
            (cs₀.compSt C).R).card : ℝ) ≤
          56 * ((∑ s ∈ Finset.Icc 1 r, (D.U s).length : ℕ) : ℝ) *
            (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by
        intro r
        induction r with
        | zero => intro _; dsimp only [bundleRunSeqWith, cs₀]; simp
        | succ m ih =>
          intro hm_le
          have hBm := runOrdAfterRestarts_bun_inv lsfInit C_lsst depth
            (fun _ => canonicalSparsify impl) k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j
            hInit m (by omega)
          have hbase_m := (runOrdAfterRestarts_base_proj lsfInit C_lsst depth
            (fun _ => canonicalSparsify impl) k M N D ordSeq restarts hV₀ j m).1
          have hI_m : CompLSFInv C_lsst (D.ℓ 0)
              (bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl) k M N D ordSeq j m).1.cs :=
            hbase_m.cs ▸ hBm.2.2.2.2.2.2.2.1
          have hG_m : (bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
              k M N D ordSeq j m).1.cs.G = D.G m := by
            rw [← hbase_m.cs, hBm.2.2.2.2.2.2.2.2.1]
          have hG₀_m : (bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
              k M N D ordSeq j m).1.cs.G₀ = D.G 0 := by
            rw [← hbase_m.cs, hBm.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
          have hDt := hD (m + 1) (Nat.succ_pos m) hm_le
          simp only [Nat.add_sub_cancel] at hDt
          have hBV : (bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
              k M N D ordSeq j m).1.cs.G.BatchIsValid (D.U (m + 1)) := by rw [hG_m]; exact hDt.1
          have hgrow := compLSFBatch_compSt_R_card_le hI_m hBV (hG₀_m ▸ hC0)
          rw [hG₀_m, ← bundleRunSeqWith_cs] at hgrow
          have hS0 : (cs₀.compSt C).R ⊆
              ((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
                k M N D ordSeq j m).1.cs.compSt C).R := by
            rw [← hbase_m.cs]; exact (hBm.2.2.2.2.2.2.2.2.2.2.2 C hC0).1.hR_sub
          have hss : ((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
              k M N D ordSeq j m).1.cs.compSt C).R ⊆
              ((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
                k M N D ordSeq j (m + 1)).1.cs.compSt C).R :=
            (compLSFBatch_compSt hI_m hBV (hG₀_m ▸ hC0)).2.2.2.1
          have hdiff : ((((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
                k M N D ordSeq j (m + 1)).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) ≤
              ((((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
                k M N D ordSeq j m).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) +
              ((((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
                k M N D ordSeq j (m + 1)).1.cs.compSt C).R.card : ℝ) -
                (((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
                  k M N D ordSeq j m).1.cs.compSt C).R.card : ℝ)) := by
            have c1 := Finset.card_le_card hS0
            have c2 := Finset.card_le_card hss
            rw [Finset.card_sdiff_of_subset hS0, Finset.card_sdiff_of_subset (hS0.trans hss),
              Nat.cast_sub c1, Nat.cast_sub (c1.trans c2)]
            linarith
          have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext x; simp [Finset.mem_Icc]; omega
          rw [hIcc, Finset.sum_insert (by simp), Nat.cast_add]
          have hring : 56 * (((D.U (m + 1)).length : ℝ) +
              ((∑ x ∈ Finset.Icc 1 m, (D.U x).length : ℕ) : ℝ)) *
                (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 =
              56 * ((D.U (m + 1)).length : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 +
              56 * ((∑ x ∈ Finset.Icc 1 m, (D.U x).length : ℕ) : ℝ) *
                (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by ring
          linarith [hgrow, ih (by omega), hdiff, hring]
      have hRsub0 : (cs₀.compSt C).R ⊆ ((stEp 0).cs.compSt C).R := by
        have h0 := hSt_base 0 (Nat.zero_le _)
        have hB0 := runOrdAfterRestarts_bun_inv lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl) k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j
          hInit s₀ hs₀.1
        have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst depth
          (fun _ => canonicalSparsify impl) k M N D ordSeq restarts hV₀ j s₀).1.cs
        rw [h0.cs, Nat.add_zero, ← hbp]
        exact (hB0.2.2.2.2.2.2.2.2.2.2.2 C hC0).1.hR_sub
      have hRdiff_le : (((stEp (τ - s₀)).cs.compSt C).R \ ((stEp 0).cs.compSt C).R).card ≤
          (((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
            k M N D ordSeq j τ).1.cs.compSt C).R \ (cs₀.compSt C).R).card := by
        have ht_eq := (hSt_base (τ - s₀) le_rfl).cs
        rw [show s₀ + (τ - s₀) = τ by omega] at ht_eq
        rw [ht_eq]
        exact Finset.card_le_card (Finset.sdiff_subset_sdiff Finset.Subset.rfl hRsub0)
      have hlog_sq_le : (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [half_lt_log_add_two (D.G 0).n])
          (Real.log_le_log (by positivity)
            (by linarith [show ((D.G 0).n : ℝ) ≤ (N : ℝ) from by exact_mod_cast hN])) 2
      have hR_τ := le_trans (hR_le τ le_rfl) (mul_le_mul_of_nonneg_left hlog_sq_le (by positivity))
      rw [hsum] at hR_τ
      have hsc_cast : ((batchSplitCount us : ℕ) : ℝ) ≤
          2 * ((((bundleRunSeqWith lsfInit depth (fun _ => canonicalSparsify impl)
            k M N D ordSeq j τ).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) := by
        exact_mod_cast le_trans hsc_R (Nat.mul_le_mul_left 2 hRdiff_le)
      linarith
    have hnorm_n : (normGraph Hb).n = Hb.n := rfl
    have hnorm_m : (normGraph Hb).m = Hb.m := rfl
    have hG₀_val : (normGraph Hb).IsValid := SparseCore.normGraph_isValid hDC.1
    have hG₀_m : (normGraph Hb).m ≤ tr.m₀ := by rw [htr_m₀, hnorm_m]; exact le_trans hDC.2.1 hM
    have hG₀_n : (normGraph Hb).n ≤ 2 * (normGraph Hb).m := by rw [hnorm_n, hnorm_m]; exact hDC.2.2.1
    dsimp only
    rw [hG₀_eq, hst_eq, ht_eq, hG_eq]
    refine ⟨hG₀_val, hG₀_m, hG₀_n, hn_le, hm_le,
      by rw [← hsp_eq, (hmn j).2.2.1]; exact hsp_le_sb,
      by rw [← hsp_eq, htr_n₀]; exact hsp_le_112,
      by omega,
      by rw [htr_m₀, (hmn j).2.2.1]; omega,
      us, hBV_norm, hds_us, rfl, hsp_eq, hdl_eq, hdel_le_n, by
        rw [(hmn j).2.2.1, hnorm_n]⟩
  exact ⟨hFacts, hUpd⟩

end MinCostFlow.SparseCore.Program
