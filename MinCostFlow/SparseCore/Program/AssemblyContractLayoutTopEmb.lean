module

public import MinCostFlow.SparseCore.Program.AssemblyTopOps
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout

import MinCostFlow.Chain.BundleRestartInv
import MinCostFlow.DynSpanner.Correctness
import MinCostFlow.DynSpanner.Program.CanonicalSparsify
import MinCostFlow.SparseCore.Program.AssemblyInputRun

/-!
# Top-layer embedding readout (`op 4`) with layout, word, and footprint bounds (`AssemblyContractLayoutTopEmb`)

Proves `asmTop_op4_runs` for `asmTopReadEmbBody` with both the layout/word-bound postconditions of
`sparseCoreOrdMachineContractKFBL` and the companion per-run `R.foot` / `o.value` clauses of
`SparseCoreReadoutFootAt.op4_runs`:
* `asm_input_emb_edges_in_S_cur`: along any nonempty `SparseCoreOrdInput` history (with `1 ≤ depth`
  and `IsValidLSFInitFor`), every edge occurring in any embedding walk `(s.trees j).emb e` belongs
  to `(s.trees j).S_cur.E` and `G.E`;
* `mWalkAt_words_lt`: every word of `MWalkAt mem ptr P` (length, edge IDs, direction bits) fits
  below `2 ^ w` once `ptr + (mWalkEncode P).length ≤ cur`, `cur + 2 < 2 ^ w`, and every edge ID
  in `P` fits below `2 ^ w`;
* `asmTop_op4_runs`: full `op 4` execution proof for both the empty (`x.ne = none`) and nonempty
  (`x.ne = some ne`) branches of `asmTopReadEmbBody`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Edge membership and word bounds for embedding walks -/

private lemma updateGo_state_eq_runState_emb {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us : List Update) :
    ∀ (U : List Update) (k₀ : ℕ) (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      (∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      (DynSpanner.updateGo sparsify (DynSpanner.runState (L := L) G₀ q sparsify us k₀) U uhAcc dAcc cAcc).state =
        DynSpanner.runState (L := L) G₀ q sparsify us (k₀ + U.length)
  | [], _, _, _, _, _ => by simp [DynSpanner.updateGo]
  | u :: U, k₀, uhAcc, dAcc, cAcc, hget => by
    have h0 : us[k₀]? = some u := by simpa using hget 0 (Nat.succ_pos _)
    have hstep : (DynSpanner.step (DynSpanner.runState (L := L) G₀ q sparsify us k₀) u sparsify).state =
        DynSpanner.runState (L := L) G₀ q sparsify us (k₀ + 1) := by
      simp [DynSpanner.runState, h0]
    simp only [DynSpanner.updateGo, hstep]
    rw [updateGo_state_eq_runState_emb G₀ q sparsify us U (k₀ + 1) _ _ _ (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hget (i + 1) (Nat.succ_lt_succ hi))]
    simp [Nat.add_assoc, Nat.add_comm 1 U.length]

private lemma runBatchState_eq_runState_emb {L : ℕ} (G₀ : MGraph) (q : ℕ)
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
    simp only [DynSpanner.runBatchState, hsome, runBatchState_eq_runState_emb G₀ q sparsify Us t (Nat.le_of_lt hlt),
      DynSpanner.update]
    rw [updateGo_state_eq_runState_emb G₀ q sparsify Us.flatten (Us[t]'hlt) (Us.take t).flatten.length _ _ _
      (fun i hi => by
        rw [hflat_split, List.getElem?_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi])]
    rw [htake, List.flatten_append, List.flatten_singleton, List.length_append]

/-- Along any nonempty `SparseCoreOrdInput` history (with `0 < k`, `1 ≤ depth`, and
`IsValidLSFInitFor`), every edge in any embedding walk `(s.trees j).emb e` belongs to `G.E`. -/
theorem asm_input_emb_edges_in_G
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl} {k M N : ℕ}
    {s : (sparseCoreProgTool lsfInit C_lsst depth impl).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k) (hdepth : 1 ≤ depth)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N s G ord n)
    (hne : SparseCoreBundleState.isNonempty (L := depth) s = true)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    ∀ e : ℕ, ∀ step ∈ (SparseCoreBundleState.trees (L := depth) s j).emb e, step.1 ∈ G.E := by
  classical
  let Tm := sparseCoreProgTool lsfInit C_lsst depth impl
  obtain ⟨τ, D, ordSeq, restarts, hG₀, hM, hN, hℓ₀, hD, hOrd, hGτ, _, _, _, hrun⟩ :=
    sparseCoreOrdInput_exists_run Tm hinp
  let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
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
  have hEq : BundleNonMachEq (SparseCoreBundleState.trees (L := depth) s j) post := hNM.trees j
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
  have hG₀_post : post.cs.G₀ = D.G 0 := by rw [hbf.cs, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hI_post : CompLSFInv C_lsst (D.ℓ 0) post.cs := hbf.cs.symm ▸ hBun.2.2.2.2.2.2.2.1
  have hG_post : post.cs.G = G := by rw [hbf.cs, hBun.2.2.2.2.2.2.2.2.1, hGτ]
  have hAct_sub : post.activeComps ⊆ components (D.G 0) :=
    hbf.activeComps ▸ hBun.2.2.2.2.2.2.2.2.2.1.2
  have hpost_raw : epochBundleSeq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      k M N D ordSeq restarts s₀ τ j (τ - s₀) = post := hpost_eq_ep.symm
  have hScur_sub_G : post.S_cur.E ⊆ G.E := fun e he => by
    rw [← hG_post]
    rw [hSc.2.2.1] at he
    rcases Finset.mem_union.mp he with h1 | hcross
    · rcases Finset.mem_union.mp h1 with hH | hEx
      · rcases Finset.mem_biUnion.mp hH with ⟨C, hC, hbE⟩
        rcases Finset.mem_biUnion.mp hbE with ⟨b, _, heH⟩
        have hC0 : C ∈ components (D.G 0) := hAct_sub hC
        have hDynC := (hDyn C hC0 b).2.2.2.2.2.2.2.2.2.1 (τ - s₀) le_rfl
        rw [hpost_raw] at hDynC
        have heB : e ∈ (post.bun (C, b)).edges := by
          change e ∈ (post.bun (C, b)).graph.E
          rw [← hDynC.2.1.2.1]
          exact hDynC.2.2.2.1.2.1 heH
        have hcb := (hBun.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b
        exact hI_post.hCE_sub C (hG₀_post.symm ▸ hC0) (hcb.2.1.2.2 heB)
      · rcases Finset.mem_biUnion.mp hEx with ⟨C, hC, heEx⟩
        unfold BundleTreeState.extraEdges at heEx
        exact hI_post.hCE_sub C (hG₀_post.symm ▸ hAct_sub hC)
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heEx).1).1
    · exact hI_post.hIns_sub (hI_post.hCross_sub hcross)
  have hemb_eq : (SparseCoreBundleState.trees (L := depth) s j).emb = post.emb := by
    funext e
    unfold BundleTreeState.emb
    rw [hEq.S_cur, hEq.activeComps, hEq.activeBuckets, hEq.bun, hEq.dyn]
  intro e step hstep
  rw [hemb_eq] at hstep
  unfold BundleTreeState.emb at hstep
  split_ifs at hstep with heS hp
  · simp only [List.mem_singleton] at hstep
    subst hstep
    exact hScur_sub_G heS
  · set p := hp.choose
    have hpA : p.1 ∈ post.activeComps := hp.choose_spec.1
    have hpC : p.1 ∈ components (D.G 0) := hAct_sub hpA
    have hep : e ∈ (post.bun p).edges := hp.choose_spec.2.2
    have hDC := hDyn p.1 hpC p.2
    set Hb := ((stEp 0).bun p).graph
    set Us_ep : List (List Update) := (List.range (τ - s₀)).map fun r =>
      (stepBundleTree (fun _ => canonicalSparsify impl) (stEp r) (D.U (s₀ + r + 1))
        (ordSeq (s₀ + r)) (ordSeq (s₀ + r + 1))).U_B p
    set us := Us_ep.flatten
    have hDynP := hDC.2.2.2.2.2.2.2.2.2.1 (τ - s₀) le_rfl
    rw [hpost_raw] at hDynP
    have hst_eq : post.dyn p =
        DynSpanner.runState (L := depth) (normGraph Hb) (phaseBase (Hb.n + bundleSplitBudget k M) depth)
          (canonicalSparsify impl) us us.length := by
      rw [hDynP.1]
      have hlen : Us_ep.length = τ - s₀ := by simp [Us_ep]
      have hrb := runBatchState_eq_runState_emb (L := depth) (normGraph Hb)
        (phaseBase (Hb.n + bundleSplitBudget k M) depth) (canonicalSparsify impl) Us_ep (τ - s₀) hlen.ge
      rw [← hlen, List.take_length] at hrb
      change DynSpanner.runBatchState (L := depth) (normGraph Hb)
        (phaseBase (Hb.n + bundleSplitBudget k M) depth) (canonicalSparsify impl) Us_ep (τ - s₀) = _
      rw [← hlen]
      exact hrb
    have hBV_norm : (normGraph Hb).BatchIsValid us :=
      batchIsValid_of_graphEq (graphEq_symm (normGraph_graphEq Hb)) hDC.2.2.2.2.2.1
    have hds_us : ∀ u ∈ us, isDelOrSplit u := hDC.2.2.2.2.2.2.1
    have hEmb := (DynSpanner.lemma_5_6 (normGraph_isValid hDC.1) hdepth
      (le_trans (by decide) (two_le_phaseBase (Hb.n + bundleSplitBudget k M) depth))
      (le_trans hDC.2.1 hM)
      hSp hBV_norm hds_us (k := us.length) le_rfl).2
    rw [List.take_length] at hEmb
    obtain ⟨_, hG_run⟩ := runState_t_and_G (L := depth) (normGraph Hb)
      (phaseBase (Hb.n + bundleSplitBudget k M) depth) (canonicalSparsify impl) us us.length le_rfl
    rw [List.take_length] at hG_run
    rw [← hG_run, ← hst_eq] at hEmb
    have heGp : e ∈ (post.dyn p).G.E := hDynP.2.1.2.1.symm ▸ hep
    have hWalk := hEmb.2 e heGp
    have hstepH : step.1 ∈ (post.dyn p).H.E := MGraph.isWalk_edges_mem hWalk step hstep
    have hstepG : step.1 ∈ (post.dyn p).G.E := hDynP.2.2.2.1.2.1 hstepH
    have hstepB : step.1 ∈ (post.bun p).edges := by
      change step.1 ∈ (post.bun (p.1, p.2)).graph.E
      rw [← hDynP.2.1.2.1]
      exact hstepG
    have hcb := (hBun.2.2.2.2.2.2.2.2.2.2.2 p.1 hpC).2 p.2
    have hstepComp : step.1 ∈ (post.cs.compSt p.1).G.E := hcb.2.1.2.2 hstepB
    rw [← hG_post]
    exact hI_post.hCE_sub p.1 (hG₀_post.symm ▸ hpC) hstepComp
  · simp at hstep

/-- Every word of `MWalkAt mem ptr P` fits below `2 ^ w` when the encoded walk ends at or below
`cur` (`cur + 2 < 2 ^ w`) and every edge ID occurring in `P` fits below `2 ^ w`. -/
theorem mWalkAt_words_lt {w ptr cur : ℕ} {mem : ℕ → ℕ} {P : List (ℕ × Bool)}
    (hW : MWalkAt mem ptr P) (hEnd : ptr + (mWalkEncode P).length ≤ cur)
    (hcurW : cur + 2 < 2 ^ w) (hEdges : ∀ step ∈ P, step.1 < 2 ^ w) :
    ∀ t < (mWalkEncode P).length, mem (ptr + t) < 2 ^ w := by
  have hlen : (mWalkEncode P).length = 1 + 2 * P.length := mWalkEncode_length P
  intro t ht
  rw [hlen] at ht hEnd
  cases t with
  | zero =>
    rw [Nat.add_zero, MWalkAt_head hW]
    omega
  | succ t' =>
    have hi : t' / 2 < P.length := by omega
    by_cases hev : t' % 2 = 0
    · have ht_eq : ptr + (t' + 1) = ptr + 1 + 2 * (t' / 2) := by omega
      rw [ht_eq, MWalkAt_step_edge hW hi]
      exact hEdges _ (List.getElem_mem hi)
    · have ht_eq : ptr + (t' + 1) = ptr + 1 + 2 * (t' / 2) + 1 := by omega
      rw [ht_eq, MWalkAt_step_dir hW hi]
      split_ifs <;> omega

/-! ## Top-layer `op 4` (`asmTopReadEmbBody`) with layout, word, and footprint bounds -/

theorem asmTop_op4_runs
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hdepth : 1 ≤ depth) (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFBL fmt L depth T G k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    ∀ (hndl : ℕ) (a : SparseCoreOrdAbs T) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some hndl →
      R.rep hndl a x mem → D.pre 4 a args mem →
      (∀ addr, R.foot hndl x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 4 a args mem < 2 ^ w →
      ∃ body, p.procs[asmTopOpIdx b 4]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep hndl a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         let embTable := st'.mem cur
         let embCap := st'.mem (cur + 1)
         let coreE := (coreGraph a.G (T.lsfs a.st br)).E
         EmbeddingReadoutAt st'.mem cur embCap a.G (T.lsfs a.st br) (T.emb a.st br) ∧
         MEmbBounded st'.mem embTable coreE embCap (T.emb a.st br) 0 cur ∧
         embCap ≤ eCap ∧
         (∀ e ∈ coreE, ∀ t < (mWalkEncode (T.emb a.st br e)).length,
           st'.mem (st'.mem (embTable + e) + t) < 2 ^ w) ∧
         (∀ addr, embTable ≤ addr → addr < embTable + embCap →
           R.foot hndl x' addr ∨ (cur ≤ addr ∧ addr < o.value)) ∧
         (∀ e ∈ coreE, ∀ addr,
           st'.mem (embTable + e) ≤ addr →
           addr < st'.mem (embTable + e) + (mWalkEncode (T.emb a.st br e)).length →
           R.foot hndl x' addr ∨ (cur ≤ addr ∧ addr < o.value))) ∧
        R.Respects (R.foot hndl x) (heapArg args) (D.space 4 a args mem) mem o.value hndl x' st'.mem ∧
        c + R.phi hndl x' st'.mem ≤ D.cost 4 a args mem + R.phi hndl x mem := by
  intro T P alloc D R hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  refine ⟨_, hp.at_op4, ?_⟩
  rcases hpre with ⟨hinp, h0', branch, graph, heap, rfl, hbr_lt, _, _⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst h0'
  have hheapArg : heapArg [hndl, branch, graph, heap] = heap := rfl
  rw [hheapArg] at hfoot hz hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hhndlW, hbrW, hgrW, hheapW⟩
  have hrep_orig := hrep
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, h0, _, _, _, _, _, _, _, _, _, _, _, hnonempty⟩, _, _, hxvCap, hxeCap, _, _, _⟩, _, hCaps⟩
  obtain ⟨hinp_k, _, _⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hresHi_le : x.resHi ≤ heap := by have := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by
    have := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by unfold ASM_HDR_SIZE; omega, by unfold ASM_HDR_SIZE; omega⟩)
    unfold ASM_HDR_SIZE at *; omega
  have hw16 : 16 < 2 ^ w := by unfold ASM_HDR_SIZE at hxres; omega
  set st0 := startState [hndl, branch, graph, heap] mem pos
  have hload4 : Runs w p ω (.assign 4 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 4 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, startState]))
        (by simpa [st0, startState, ASM_HDR_NE] using h0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 4 (if x.ne.isSome then 1 else 0) }
  cases hxne_b : x.ne with
  | none =>
    have hst_em : a.st.isNonempty = false := by simpa [hxne_b] using hxne.symm
    obtain ⟨_, hE_em⟩ := asmEmpty_inv hinp hst_em
    have hret : Runs w p ω (.ret (.bin .add (.reg 3) (.const 2))) st1 (.returned (heap + 2)) st1 _ :=
      runs_ret_iff.mpr ⟨heap + 2,
        Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st1, st0, startState]))
          (Expr.eval_const (by omega)) (by change heap + 2 < 2 ^ w at hsp; exact hsp), rfl, rfl, rfl⟩
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadEmbBody bp.fReadEmb) st0 (.returned (heap + 2)) st1 cF ∧ cF ≤ 50 := by
      unfold asmTopReadEmbBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload4,
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq (v := 0) (by simp [st1, hxne_b]),
          by simp only [↓reduceIte]; exact hret, rfl⟩, rfl⟩), ?_⟩
      simp only [Expr.size]; omega
    have hlsf_em : T.lsfs a.st branch = emptyLSF := by
      change (if a.st.isNonempty then _ else emptyLSF) = _; simp [hst_em]
    have hemb_em : T.emb a.st branch = fun _ => [] := by
      funext e; change (if a.st.isNonempty then _ else fun _ => []) e = _; simp [hst_em]
    have hcoreE_em : (coreGraph a.G (T.lsfs a.st branch)).E = ∅ := by
      ext e; simp only [coreGraph, Finset.mem_sdiff, hE_em, Finset.notMem_empty, false_and]
    have h0z : mem heap = 0 := hz heap le_rfl
    have h1z : mem (heap + 1) = 0 := hz (heap + 1) (by omega)
    refine ⟨.returned (heap + 2), st1, cF, x, hfull, hrep_orig, ?_,
      ⟨by simp [Outcome.value], by change heap + 2 ≤ heap + 2; exact le_rfl,
        fun addr ha => hz addr (by simp only [Outcome.value] at ha; omega),
        fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · change EmbeddingReadoutAt mem heap (mem (heap + 1)) a.G (T.lsfs a.st branch) (T.emb a.st branch)
        rw [hlsf_em, hemb_em, h1z]; exact embReadoutAt_empty hE_em
      · change MEmbBounded mem (mem heap) (coreGraph a.G (T.lsfs a.st branch)).E (mem (heap + 1))
          (T.emb a.st branch) 0 heap
        rw [hcoreE_em, h0z, h1z]
        exact ⟨Nat.zero_le _, Nat.zero_le _, fun _ he => absurd he (Finset.notMem_empty _)⟩
      · change mem (heap + 1) ≤ eCap; rw [h1z]; exact Nat.zero_le _
      · intro e he; change e ∈ (coreGraph a.G (T.lsfs a.st branch)).E at he
        rw [hcoreE_em] at he; exact absurd he (Finset.notMem_empty _)
      · intro addr ha1 ha2; change mem heap ≤ addr at ha1; change addr < mem heap + mem (heap + 1) at ha2
        rw [h0z] at ha1 ha2; rw [h1z] at ha2; omega
      · intro e he; change e ∈ (coreGraph a.G (T.lsfs a.st branch)).E at he
        rw [hcoreE_em] at he; exact absurd he (Finset.notMem_empty _)
    · have hphi0 : R.phi hndl x st1.mem = 0 ∧ R.phi hndl x mem = 0 := by simp [R, asmTopRepEq, asmTopPhi, hxne_b]
      rw [hphi0.1, hphi0.2]; change cF + 0 ≤ P.readout + 0; simp only [P, asmTopParams]; omega
  | some ne =>
    have hst_ne : a.st.isNonempty = true := by simpa [hxne_b] using hxne.symm
    obtain ⟨_, _, h10, _, htblLt, hbrLt, _, heG, hG_br, _, _, hTbl, hBRRep, _, _, _, _, _⟩ := hnonempty ne hxne_b
    have hload5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL)))) st1 .normal
        { st1 with regs := Function.update st1.regs 5 ne.tbl } _ :=
      runs_assign_iff.mpr ⟨ne.tbl, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_TBL; omega)) (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)) h10,
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 5 ne.tbl }
    have hload6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.reg 1)))) st2 .normal
        { st2 with regs := Function.update st2.regs 6 (ne.brH branch) } _ :=
      runs_assign_iff.mpr ⟨ne.brH branch, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := ne.tbl) (by simp [st2]))
          (Expr.eval_reg_of_eq (v := branch) (by simp [st2, st1, st0, startState])) (by omega))
        (hTbl branch (by omega)), rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 6 (ne.brH branch) }
    have hsp2 : heap + 2 < 2 ^ w := by change heap + 2 < 2 ^ w at hsp; exact hsp
    obtain ⟨bodyBR, hbodyBR, oBR, stBR, cBR, xBr', hrunBR, hBRRep',
        ⟨hEmbRd, hBd, hCapLe, hTabIn, hWalkIn⟩, hRespBR, hCostBR⟩ :=
      hLay.readEmb_layout_runs (ne.brH branch) heap vCap eCap (a.st.trees branch) a.st.ord (ne.xBR branch)
        st3.mem st3.pos ω (by rw [← hxvCap, ← hxeCap]; exact hBRRep branch (by omega))
        (fun addr ha => hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, by omega, ha⟩))))
        (by have := hbrLt branch (by omega); omega) hheapW hz hsp2
    have hcallBR : Runs w p ω (.call 7 bp.fReadEmb [.reg 6, .reg 3]) st3 .normal
        { stBR with regs := Function.update st3.regs 7 oBR.value }
        (argsSize [.reg 6, .reg 3] + cBR + 1) := by
      refine (runs_call_iff (r := 7) (f := bp.fReadEmb) (st := st3) (o := .normal)
        (st' := { stBR with regs := Function.update st3.regs 7 oBR.value })).mpr
        ⟨[ne.brH branch, heap], bodyBR, oBR, stBR, cBR, ?_, hbodyBR, hrunBR, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st3, st2, st1, st0, startState]
    set st4 : State := { stBR with regs := Function.update st3.regs 7 oBR.value }
    have hret : Runs w p ω (.ret (.reg 7)) st4 (.returned oBR.value) st4 _ :=
      runs_ret_iff.mpr ⟨oBR.value, Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
    have hthen := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload5,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hload6,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcallBR, hret, rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadEmbBody bp.fReadEmb) st0 (.returned oBR.value) st4 cF ∧ cF ≤ cBR + 50 := by
      unfold asmTopReadEmbBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload4,
        runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (v := 1) (by simp [st1, hxne_b]),
          by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩), ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
    obtain ⟨hrep', hresp', hphi'⟩ := asmTop_branch_readout_frame hxne_b (by omega) hrep_orig.1 hfoot hBRRep' hRespBR
    have hlsf_eq : T.lsfs a.st branch = (a.st.trees branch).cs.lsf := by
      change (if a.st.isNonempty then _ else emptyLSF) = _; simp [hst_ne]
    have hemb_eq : T.emb a.st branch = (a.st.trees branch).emb := by
      change (if a.st.isNonempty then _ else fun _ => []) = _; simp [hst_ne]
    have hG_eq : (a.st.trees branch).cs.G = a.G := (hG_br branch (by omega)).1
    have hEmbInG := asm_input_emb_edges_in_G (by omega) hdepth hinp hst_ne (hInit branch hbr_lt)
    have hEdgeW : ∀ e, ∀ step ∈ (a.st.trees branch).emb e, step.1 < 2 ^ w := fun e step hstep => by
      have hlt : step.1 < x.eCap := heG step.1 (hEmbInG e step hstep)
      unfold ASM_HDR_SIZE at hxres
      omega
    refine ⟨.returned oBR.value, st4, cF, _, hfull,
      ⟨hrep', fun h => by simp at h, fun ne₁ hne₁ => by cases Option.some.inj hne₁.symm; exact hCaps ne hxne_b⟩, ?_, hresp', ?_⟩
    · refine ⟨?_, ?_, hCapLe, ?_, ?_, ?_⟩
      · change EmbeddingReadoutAt stBR.mem heap (stBR.mem (heap + 1)) a.G (T.lsfs a.st branch) (T.emb a.st branch)
        rw [hlsf_eq, hemb_eq, ← hG_eq]; exact hEmbRd
      · change MEmbBounded stBR.mem (stBR.mem heap) (coreGraph a.G (T.lsfs a.st branch)).E
          (stBR.mem (heap + 1)) (T.emb a.st branch) 0 heap
        rw [hlsf_eq, hemb_eq, ← hG_eq]; exact hBd
      · intro e he
        change e ∈ (coreGraph a.G (T.lsfs a.st branch)).E at he
        rw [hlsf_eq, ← hG_eq] at he
        obtain ⟨_, _, hwEnd, hW⟩ := hBd.2.2 e he
        change ∀ t < (mWalkEncode (T.emb a.st branch e)).length,
          stBR.mem (stBR.mem (stBR.mem heap + e) + t) < 2 ^ w
        rw [hemb_eq]
        exact mWalkAt_words_lt hW hwEnd hsp2 (hEdgeW e)
      · intro addr ha1 ha2
        rcases hTabIn addr ha1 ha2 with hbf | hnew
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨branch, by dsimp only; omega, by simpa using hbf⟩)))))
        · exact Or.inr hnew
      · intro e he addr ha1 ha2
        change e ∈ (coreGraph a.G (T.lsfs a.st branch)).E at he
        rw [hlsf_eq, ← hG_eq] at he
        change stBR.mem (stBR.mem heap + e) ≤ addr at ha1
        change addr < stBR.mem (stBR.mem heap + e) + (mWalkEncode (T.emb a.st branch e)).length at ha2
        rw [hemb_eq] at ha2
        rcases hWalkIn e he addr ha1 ha2 with hbf | hnew
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨branch, by dsimp only; omega, by simpa using hbf⟩)))))
        · exact Or.inr hnew
    · change cF + R.phi hndl _ stBR.mem ≤ P.readout + R.phi hndl x mem
      change cBR + BR.rep.phi (ne.brH branch) xBr' stBR.mem ≤ BRS.readout capExp + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem at hCostBR
      change R.phi hndl _ stBR.mem + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem =
        R.phi hndl x mem + BR.rep.phi (ne.brH branch) xBr' stBR.mem at hphi'
      simp only [P, asmTopParams]; omega

end MinCostFlow.SparseCore.Program
