module

public import MinCostFlow.MinRatio.UpdateAssemblyBase
public import MinCostFlow.MinRatio.OrdBatchEdits
public import MinCostFlow.MinRatio.PassReset
import WordRAM.Tactic

/-!
# Wired ordered chain refresh: entry body, sub-specifications and helpers

The first half of the wired `ChainRefresh` (`MinRatio/OrdChainRefreshWired.lean`): the entry
procedure `ordChainRefreshWiredBody`, the sub-specifications `OrdChainUpdateCoreSpec` and
`ShiftQuotaWriterSpec`, the scan and snapshot loops, and the lemma
`solverStateRep_update_passes_branD` for the pass reset.

The wired procedure as a whole:

Implements the deterministic Word-RAM entry `ordChainRefreshWiredBody` for Algorithm 2's
`ChainRefresh` step (`[root, uIntBuf, g, l, quotaBase, heap]`, pages 20 and 29, with the rotation
orders of the bundle repair of Lemma 5.17):
1. Snapshots `rebuildCount[0..d-1]` onto the fresh heap `[heap, heap + d)`.
2. Calls `level0BatchToOrdEditsBody` (`OrdBatchEdits.lean`) at `editsPtr := heap + d` to emit
   `OrdEditsAt` for `batchToOrdEdits tr.2.2.2.2` and advance `afterEdits := editsPtr + editWords`.
3. Invokes `ordChainCoreProc` (`OrdChainUpdateCoreSpec`), which runs the ordered Algorithm 1
   level update / periodic rebuild loop (`ordCoreUpdateStmt`, `ordLoadBranchOutStmt`,
   `rebuildGuard`, `buildSortedEndsBody` / `ordCoreReadOrdStmt`, `ordRebuildSuffixProgram`),
   terminal update, LCT tree-edit fold, and detector threshold refresh.
4. Deterministically scans `[heap, heap + d)` against the updated `rebuildCount[0..d-1]` to
   compute `firstRebuiltLevel cfg.P.d oldRC newRC`; on `some iStar`, clears `passes[iStar..d]`
   via `resetPassSuffix` (`PassReset.lean`) and sets `branD := 0`.
5. Invokes `shiftQuotaWriterProc` (`ShiftQuotaWriterSpec`) to populate `quotaBase[0..d+1]`.
6. Proves `chainRefreshStepSpec_wired`, discharging `ChainRefreshStepSpec`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program MinCostFlow.Bundle

/-- Intermediate `Alg2State` produced right after `Chain.Ordered.algorithm1_update` and before
the `firstRebuiltLevel` pass-counter reset of `alg2PreLoopState`. After a rebuild of level `0` its
name maps are the renamed ones (`Chain.Ordered.level0E2I`). -/
@[expose] noncomputable def alg2PreResetState (cfg : Alg2Config) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) : Alg2State cfg :=
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let ch1 := (Chain.Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
    tr.2.2.2.2 (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))).1
  let ren := Chain.Ordered.level0Rebuilt cfg.P.d model.chain.rebuildCount ch1.rebuildCount
  let G₀' := (model.chain.G 0).applyBatch tr.2.2.2.2
  { model with
    chain := ch1
    extG := tr.1
    extToInt := Chain.Ordered.level0E2I ren G₀' tr.2.1
    intToExt := Chain.Ordered.level0I2E ren G₀' tr.2.2.1
    nextFresh := Chain.Ordered.level0NF ren G₀' tr.2.2.2.1
    extℓ := lVec
    extg := gVec
    lctUpdateOps := model.lctUpdateOps + U.length
    largeBatchEnc := model.largeBatchEnc + largeBatchEncCap cfg.P tr.2.2.2.2
    updateCount := model.updateCount + 1 }

/-- Modular contract for the ordered Algorithm 1 chain-update, periodic rebuild, LCT tree-edit
fold, and detector threshold refresh subroutine
`ordChainCoreProc [root, uIntBuf, editsPtr, editWords, g, l, heap]`.
Consumes `OrdEditsAt` for `batchToOrdEdits tr.2.2.2.2` at `editsPtr`, updates levels `0..d`
to `Chain.Ordered.algorithm1_update` (producing `alg2PreResetState`), and preserves everything
below `heap` outside `Rrep.foot root tok` (including the old `rebuildCount` snapshot). -/
@[expose] def OrdChainUpdateCoreSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (ordChainCoreProc : ℕ) (coreSpace coreBudget : ℕ → ℕ) (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[ordChainCoreProc]? = some body ∧
    ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
      (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 →
      tr.2.2.2.1 ≤ tok.intCap →
      BatchAt mem uIntBuf tr.2.2.2.2 →
      DynSpanner.Program.SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
      OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
      (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
      editsPtr + editWords = heap →
      RefreshBatch model.extG U →
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      uIntBuf + cfg.P.d ≤ editsPtr →
      ZeroFrom mem heap →
      heap + coreSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R',
        Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root modelPre tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv modelPre L out.mem tok'.edgeRecords B' ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ coreBudget U.length + Rrep.phi root tok mem0

/-- Modular contract for the shift-quota writer `shiftQuotaWriterProc [root, quotaBase]`
(isolating `Real.log` in `alg2PsiGame`). Writes `shiftQuotaWord` at `quotaBase[0..d]` and
`⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊` at `quotaBase[d + 1]`, leaving all other memory unchanged. -/
@[expose] def ShiftQuotaWriterSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftQuotaWriterProc quotaBudget : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftQuotaWriterProc]? = some body ∧
    ∀ (root quotaBase pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore),
      Rrep.rep root model tok mem →
      (∀ a, Rrep.foot root tok a → a < 2 ^ w) →
      (∀ i ≤ cfg.P.d, shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i < 2 ^ w) →
      (∀ i ≤ cfg.P.d + 1, ¬ Rrep.foot root tok (quotaBase + i)) →
      quotaBase + cfg.P.d + 1 < 2 ^ w →
      ∃ cost out,
        Runs w p ω body (startState [root, quotaBase] mem pos) (.returned 0) out cost ∧
        cost ≤ quotaBudget ∧
        (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i) ∧
        out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
        (∀ a, a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a → out.mem a = mem a)

/-- Deterministic wired `ChainRefresh` entry procedure taking
`[root, uIntBuf, g, l, quotaBase, heap]` (`reg 0..5`) and returning `nextHeap`. -/
@[expose] def ordChainRefreshWiredBody
    (ordEditsProc ordChainCoreProc shiftQuotaWriterProc : ℕ) : Stmt :=
  .assign 20 (.reg 0) ;;
  .assign 21 (.reg 1) ;;
  .assign 22 (.reg 2) ;;
  .assign 23 (.reg 3) ;;
  .assign 24 (.reg 4) ;;
  .assign 25 (.reg 5) ;;
  .assign 26 (.load (.reg 20)) ;;
  .assign 27 (.load (.bin .add (.reg 20) (.const 2))) ;;
  .assign 28 (.load (.bin .add (.reg 26) (.const 11))) ;;
  .assign 29 (.bin .add (.reg 28) (.const 1)) ;;
  .assign 30 (.bin .add (.reg 27) (.bin .mul (.const 2) (.reg 29))) ;;
  forRange 19 (.const 0) (.reg 28)
    (.store (.bin .add (.reg 25) (.reg 19)) (.load (.bin .add (.reg 30) (.reg 19)))) ;;
  .assign 36 (.bin .add (.reg 25) (.reg 28)) ;;
  .call 31 ordEditsProc [.reg 21, .reg 36] ;;
  .assign 32 (.bin .add (.reg 36) (.reg 31)) ;;
  .call 33 ordChainCoreProc [.reg 20, .reg 21, .reg 36, .reg 31, .reg 22, .reg 23, .reg 32] ;;
  .assign 27 (.load (.bin .add (.reg 20) (.const 2))) ;;
  .assign 30 (.bin .add (.reg 27) (.bin .mul (.const 2) (.reg 29))) ;;
  .assign 34 (.reg 28) ;;
  forRange 19 (.const 0) (.reg 28)
    (.cond (.bin .eq (.reg 34) (.reg 28))
      (.cond (.bin .lt (.load (.bin .add (.reg 25) (.reg 19))) (.load (.bin .add (.reg 30) (.reg 19))))
        (.assign 34 (.reg 19))
        .nop)
      .nop) ;;
  .cond (.bin .lt (.reg 34) (.reg 28))
    (.assign 0 (.reg 27) ;;
     .assign 1 (.reg 34) ;;
     .assign 2 (.reg 29) ;;
     resetPassSuffix ;;
     .store (.bin .add (.reg 27) (.bin .mul (.const 4) (.reg 29))) (.const 0))
    .nop ;;
  .call 35 shiftQuotaWriterProc [.reg 20, .reg 24] ;;
  .ret (.reg 33)

theorem ordChainRefreshWiredBody_noRand
    (ordEditsProc ordChainCoreProc shiftQuotaWriterProc : ℕ) :
    (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc).NoRand := by
  simp [ordChainRefreshWiredBody, forRange, forUp, resetPassSuffix_noRand, Stmt.NoRand]

theorem batchBodyAt_len_eq_of_edgeOnly {mem : ℕ → ℕ} {a : ℕ} {G : MGraph}
    {U : List Update} {totalWords : ℕ}
    (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hb : DynSpanner.Program.BatchBodyAt mem a G U totalWords) :
    totalWords = (U.flatMap IPM.Machine.updateWords).length := by
  induction U generalizing a G totalWords with
  | nil => simpa [DynSpanner.Program.BatchBodyAt] using hb
  | cons u rest ih =>
    obtain ⟨len, hle, huAt, hrest⟩ := hb
    have huE := hedge u List.mem_cons_self
    have hrestE := fun v hv => hedge v (List.mem_cons_of_mem u hv)
    have hrestLen := ih hrestE hrest
    cases u with
    | split _ _ _ _ => exact huE.elim
    | insert e x y =>
      have hlen : len = 4 := huAt.1
      simp only [List.flatMap_cons, List.length_append, IPM.Machine.updateWords, List.length_cons,
        List.length_nil]
      omega
    | delete e =>
      have hlen : len = 2 := huAt.1
      simp only [List.flatMap_cons, List.length_append, IPM.Machine.updateWords, List.length_cons,
        List.length_nil]
      omega

theorem smallBatchAt_len_eq_of_edgeOnly {mem : ℕ → ℕ} {a : ℕ} {G : MGraph}
    {U : List Update} {totalWords : ℕ}
    (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hsb : DynSpanner.Program.SmallBatchAt mem a G U totalWords) :
    totalWords = (IPM.Machine.batchWords U).length := by
  obtain ⟨⟨h1, _, hbody⟩, _⟩ := hsb
  have hlen := batchBodyAt_len_eq_of_edgeOnly hedge hbody
  simp only [IPM.Machine.batchWords, List.length_cons]
  omega

theorem refreshBatch_isEdgeUpdate {G : MGraph} {U : List Update}
    (h : RefreshBatch G U) : ∀ u ∈ U, IsEdgeUpdate u := by
  intro u hu
  have hspec := h.2.2 u hu
  cases u with
  | insert _ _ _ => trivial
  | delete _ => trivial
  | split _ _ _ _ => exact hspec.elim

theorem translateBatch_words_lt {w : ℕ} {extG intG : MGraph}
    {e2i i2e : ℕ → ℕ} {nf : ℕ} {U : List Update}
    (hfresh : FreshInv extG intG e2i i2e nf)
    (hvalid : extG.BatchIsValid U)
    (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hwordsU : ∀ x ∈ batchWords U, x < 2 ^ w)
    (hnfW : 2 * (nf + U.length) + 1 < 2 ^ w)
    (hw1 : 1 < 2 ^ w) :
    let U_int := (translateBatch extG e2i i2e nf U).2.2.2.2
    (∀ x ∈ batchWords U_int, x < 2 ^ w) ∧
    (∀ u ∈ U_int, match u with | .insert e _ _ => 2 * e + 1 < 2 ^ w | _ => True) := by
  have hlenEq : (translateBatch extG e2i i2e nf U).2.2.2.2.length = U.length :=
    (translateBatch_preserves U extG intG e2i i2e nf hfresh hvalid).2.2.2.2.1
  have hstep : ∀ (extG intG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (U : List Update),
      FreshInv extG intG e2i i2e nf → extG.BatchIsValid U → (∀ u ∈ U, IsEdgeUpdate u) →
      (∀ x ∈ U.flatMap updateWords, x < 2 ^ w) → 2 * (nf + U.length) + 1 < 2 ^ w →
      let U_int := (translateBatch extG e2i i2e nf U).2.2.2.2
      (∀ x ∈ U_int.flatMap updateWords, x < 2 ^ w) ∧
      (∀ u ∈ U_int, match u with | .insert e _ _ => 2 * e + 1 < 2 ^ w | _ => True) := by
    intro extG intG e2i i2e nf U
    induction U generalizing extG intG e2i i2e nf with
    | nil => intro _ _ _ _ _; simp [translateBatch]
    | cons u rest ih =>
      intro hfr hval hed hwu hnw
      have huE := hed u List.mem_cons_self
      have hrestE := fun v hv => hed v (List.mem_cons_of_mem u hv)
      have htr := translateUpdate_preserves hfr hval.1
      have hwu_u : ∀ x ∈ updateWords u, x < 2 ^ w := fun x hx =>
        hwu x (List.mem_flatMap.mpr ⟨u, List.mem_cons_self, hx⟩)
      have hwu_r : ∀ x ∈ rest.flatMap updateWords, x < 2 ^ w := fun x hx => by
        obtain ⟨v, hv, hxv⟩ := List.mem_flatMap.mp hx
        exact hwu x (List.mem_flatMap.mpr ⟨v, List.mem_cons_of_mem u hv, hxv⟩)
      cases u with
      | split _ _ _ _ => exact huE.elim
      | delete e =>
        dsimp only [translateBatch, translateUpdate] at htr ⊢
        obtain ⟨hwr, hkr⟩ := ih _ _ _ _ _ htr.1 hval.2 hrestE hwu_r (by simp at hnw; omega)
        have heLt : e2i e < nf := hfr.hLtFresh _ (hfr.hE ▸ Finset.mem_image_of_mem _ hval.1)
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · simp only [List.flatMap_cons, List.mem_append, updateWords, List.mem_cons,
            List.not_mem_nil, or_false] at hx
          rcases hx with (rfl | rfl) | hx
          · exact hw1
          · omega
          · exact hwr x hx
        · rcases List.mem_cons.mp hv with rfl | hv
          · trivial
          · exact hkr v hv
      | insert e x y =>
        dsimp only [translateBatch, translateUpdate] at htr ⊢
        obtain ⟨hwr, hkr⟩ := ih _ _ _ _ _ htr.1 hval.2 hrestE hwu_r (by simp at hnw; omega)
        have hxW : x < 2 ^ w := hwu_u x (by simp [updateWords])
        have hyW : y < 2 ^ w := hwu_u y (by simp [updateWords])
        refine ⟨fun z hz => ?_, fun v hv => ?_⟩
        · simp only [List.flatMap_cons, List.mem_append, updateWords, List.mem_cons,
            List.not_mem_nil, or_false] at hz
          rcases hz with (rfl | rfl | rfl | rfl) | hz
          · omega
          · omega
          · exact hxW
          · exact hyW
          · exact hwr z hz
        · rcases List.mem_cons.mp hv with rfl | hv
          · simp at hnw; omega
          · exact hkr v hv
  obtain ⟨hflat, hkeys⟩ := hstep extG intG e2i i2e nf U hfresh hvalid hedge
    (fun x hx => hwordsU x (List.mem_cons_of_mem _ hx)) hnfW
  refine ⟨fun x hx => ?_, hkeys⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · rw [hlenEq]; exact hwordsU U.length List.mem_cons_self
  · exact hflat x hx

theorem smallBatchAt_congr {mem mem' : ℕ → ℕ} {a : ℕ} {G : MGraph}
    {U : List Update} {totalWords : ℕ}
    (hsb : DynSpanner.Program.SmallBatchAt mem a G U totalWords)
    (hag : ∀ x, a ≤ x → x < a + totalWords → mem' x = mem x) :
    DynSpanner.Program.SmallBatchAt mem' a G U totalWords := by
  have hbody : ∀ (a : ℕ) (G : MGraph) (U : List Update) (tw : ℕ),
      DynSpanner.Program.BatchBodyAt mem a G U tw →
      (∀ x, a ≤ x → x < a + tw → mem' x = mem x) →
      DynSpanner.Program.BatchBodyAt mem' a G U tw := by
    intro a G U
    induction U generalizing a G with
    | nil => intro tw hb _; exact hb
    | cons u rest ih =>
      intro tw ⟨len, hle, huAt, hrest⟩ hag'
      refine ⟨len, hle, ?_, ih (a + len) (G.applyUpdate u) (tw - len) hrest
        (fun x h1 h2 => hag' x (by omega) (by omega))⟩
      have hlist : ∀ (xs : List ℕ), xs.length = len → ListAt mem a xs → ListAt mem' a xs :=
        fun xs hxs hl j hj => (hag' (a + j) (by omega) (by omega)).trans (hl j hj)
      cases u with
      | insert e x y => exact ⟨huAt.1, hlist _ (by have := huAt.1; simp [this]) huAt.2⟩
      | delete e => exact ⟨huAt.1, hlist _ (by have := huAt.1; simp [this]) huAt.2⟩
      | split v v' St Sh =>
        rcases huAt with ⟨Lt, Lh, h1, h2, h3, h4, h5, h6⟩ | ⟨Lt, Lh, h1, h2, h3, h4, h5, h6⟩
        · exact Or.inl ⟨Lt, Lh, h1, h2, h3, h4, h5, hlist _ (by simp; omega) h6⟩
        · exact Or.inr ⟨Lt, Lh, h1, h2, h3, h4, h5, hlist _ (by simp; omega) h6⟩
  have h1 := hsb.1.1
  exact ⟨⟨h1, (hag a le_rfl (by omega)).trans hsb.1.2.1,
    hbody (a + 1) G U (totalWords - 1) hsb.1.2.2 (fun x hx1 hx2 => hag x (by omega) (by omega))⟩, hsb.2⟩

theorem snapshotRebuildCounts_runs {w dstBase srcBase d : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (hr25 : st.regs 25 = dstBase) (hr28 : st.regs 28 = d) (hr30 : st.regs 30 = srcBase)
    (hdisj : srcBase + d ≤ dstBase)
    (hdstW : dstBase + d < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω
        (forRange 19 (.const 0) (.reg 28)
          (.store (.bin .add (.reg 25) (.reg 19)) (.load (.bin .add (.reg 30) (.reg 19)))))
        st .normal out cost ∧
      cost ≤ 18 * d + 10 ∧
      (∀ j < d, out.mem (dstBase + j) = st.mem (srcBase + j)) ∧
      (∀ a, a < dstBase ∨ dstBase + d ≤ a → out.mem a = st.mem a) ∧
      (∀ r ≠ 19, out.regs r = st.regs r) := by
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ d ∧ s.regs 19 = j ∧ (∀ r ≠ 19, s.regs r = st.regs r) ∧
    (∀ k < j, s.mem (dstBase + k) = st.mem (srcBase + k)) ∧
    (∀ a, a < dstBase ∨ dstBase + j ≤ a → s.mem a = st.mem a)
  have hstep : ∀ j, 0 ≤ j → j < d →
      Triple w p (Inv j)
        (.store (.bin .add (.reg 25) (.reg 19)) (.load (.bin .add (.reg 30) (.reg 19))))
        (normalPost fun s' => Inv (j + 1) { s' with regs := Function.update s'.regs 19 (j + 1) } ∧
          s'.regs 19 = j) (fun _ => 8) := by
    intro j _ hj s bits ⟨_, hjr, hregs, hprev, hfr⟩
    have hsrcEq : s.mem (srcBase + j) = st.mem (srcBase + j) := hfr (srcBase + j) (Or.inl (by omega))
    let out := { s with mem := Function.update s.mem (dstBase + j) (st.mem (srcBase + j)) }
    have hr : Runs w p bits
        (.store (.bin .add (.reg 25) (.reg 19)) (.load (.bin .add (.reg 30) (.reg 19))))
        s .normal out 8 :=
      runs_store_iff.mpr ⟨dstBase + j, st.mem (srcBase + j),
        by simp [Expr.eval, BinOp.eval, (hregs 25 (by decide)).trans hr25, hjr, show dstBase + j < 2 ^ w by omega],
        by simp [Expr.eval, BinOp.eval, (hregs 30 (by decide)).trans hr30, hjr, show srcBase + j < 2 ^ w by omega, hsrcEq],
        rfl, rfl, rfl⟩
    refine ⟨.normal, out, 8, hr, ⟨⟨by omega, by simp, fun r hr' => by simpa [out, Function.update_of_ne hr'] using hregs r hr',
      fun k hk => by
        by_cases hkj : k = j
        · subst hkj; simp [out]
        · simp only [out, Function.update_of_ne (show dstBase + k ≠ dstBase + j by omega)]
          exact hprev k (by omega),
      fun a ha => by
        simp only [out, Function.update_of_ne (show a ≠ dstBase + j by omega)]
        exact hfr a (by omega)⟩, hjr⟩, le_rfl⟩
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 19) (lo := .const 0) (hi := .reg 28) 8 0 d (Nat.zero_le _) hw1 (fun _ => by omega)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r hr => by simp [Function.update_of_ne hr], fun k hk => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 28 (by decide)).trans hr28])
    hstep
  obtain ⟨o, out, cost, hr, hInv, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv
  | normal =>
    exact ⟨out, cost, hr, by simp [Expr.size] at hc; omega, hInv.2.2.2.1, hInv.2.2.2.2, hInv.2.2.1⟩

theorem scanFirstRebuiltLevel_runs {w oldBase newBase d : ℕ} {oldRC newRC : ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hr25 : st.regs 25 = oldBase) (hr28 : st.regs 28 = d)
    (hr30 : st.regs 30 = newBase) (hr34 : st.regs 34 = d)
    (hold : ∀ j < d, st.mem (oldBase + j) = oldRC j)
    (hnew : ∀ j < d, st.mem (newBase + j) = newRC j)
    (holdW : oldBase + d < 2 ^ w) (hnewW : newBase + d < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω
        (forRange 19 (.const 0) (.reg 28)
          (.cond (.bin .eq (.reg 34) (.reg 28))
            (.cond (.bin .lt (.load (.bin .add (.reg 25) (.reg 19))) (.load (.bin .add (.reg 30) (.reg 19))))
              (.assign 34 (.reg 19)) .nop)
            .nop))
        st .normal out cost ∧
      cost ≤ 30 * d + 10 ∧
      out.regs 34 = (firstRebuiltLevel d oldRC newRC).getD d ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 19 → r ≠ 34 → out.regs r = st.regs r) := by
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ d ∧ s.regs 19 = j ∧ s.mem = st.mem ∧
    (∀ r, r ≠ 19 → r ≠ 34 → s.regs r = st.regs r) ∧
    s.regs 34 = ((List.range j).find? fun k => decide (oldRC k < newRC k)).getD d
  have hfindLt : ∀ j ≤ d, ∀ k, ((List.range j).find? fun t => decide (oldRC t < newRC t)) = some k → k < d := by
    intro j hj k hk
    have := List.mem_range.mp (List.mem_of_find?_eq_some hk); omega
  let stepBody : Stmt :=
    .cond (.bin .eq (.reg 34) (.reg 28))
      (.cond (.bin .lt (.load (.bin .add (.reg 25) (.reg 19))) (.load (.bin .add (.reg 30) (.reg 19))))
        (.assign 34 (.reg 19)) .nop)
      .nop
  have hstep : ∀ j, 0 ≤ j → j < d →
      Triple w p (Inv j) stepBody
        (normalPost fun s' => Inv (j + 1) { s' with regs := Function.update s'.regs 19 (j + 1) } ∧
          s'.regs 19 = j) (fun _ => 18) := by
    intro j _ hj s bits ⟨_, hjr, hmem, hregs, h34⟩
    have h25 : s.regs 25 = oldBase := (hregs 25 (by decide) (by decide)).trans hr25
    have h28 : s.regs 28 = d := (hregs 28 (by decide) (by decide)).trans hr28
    have h30 : s.regs 30 = newBase := (hregs 30 (by decide) (by decide)).trans hr30
    cases hf : (List.range j).find? (fun k => decide (oldRC k < newRC k)) with
    | some k =>
      have hkLt : k < d := hfindLt j (by omega) k hf
      have h34k : s.regs 34 = k := by simpa [hf] using h34
      have hcond0 : (Expr.bin .eq (.reg 34) (.reg 28)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, h34k, h28, show k ≠ d by omega, show 0 < 2 ^ w by omega]
      have hr : Runs w p bits stepBody s .normal s 5 :=
        runs_cond_iff.mpr ⟨0, 1, hcond0, by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
          by simp [Expr.size]⟩
      have hfSucc : (List.range (j + 1)).find? (fun t => decide (oldRC t < newRC t)) = some k := by
        rw [List.range_succ, List.find?_append, hf]; rfl
      refine ⟨.normal, s, 5, hr, ⟨⟨by omega, by simp, hmem,
        fun r h1 h2 => by simpa [Function.update_of_ne h1] using hregs r h1 h2,
        by simp [h34k, hfSucc]⟩, hjr⟩, by dsimp; omega⟩
    | none =>
      have h34d : s.regs 34 = d := by simpa [hf] using h34
      have hcond1 : (Expr.bin .eq (.reg 34) (.reg 28)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, h34d, h28, hw1]
      have hltEval : (Expr.bin .lt (.load (.bin .add (.reg 25) (.reg 19)))
          (.load (.bin .add (.reg 30) (.reg 19)))).eval w s =
          some (if oldRC j < newRC j then 1 else 0) := by
        by_cases hlt' : oldRC j < newRC j
        · simp [Expr.eval, BinOp.eval, h25, h30, hjr, hmem, show oldBase + j < 2 ^ w by omega,
            show newBase + j < 2 ^ w by omega, hold j hj, hnew j hj, hlt', hw1]
        · simp [Expr.eval, BinOp.eval, h25, h30, hjr, hmem, show oldBase + j < 2 ^ w by omega,
            show newBase + j < 2 ^ w by omega, hold j hj, hnew j hj, hlt', show 0 < 2 ^ w by omega]
      by_cases hlt : oldRC j < newRC j
      · let s' : State := { s with regs := Function.update s.regs 34 j }
        have hrAsgn : Runs w p bits (.assign 34 (.reg 19)) s .normal s' 2 :=
          runs_assign_iff.mpr ⟨j, by simp [Expr.eval, hjr], rfl, rfl, rfl⟩
        have hrIn : Runs w p bits
            (.cond (.bin .lt (.load (.bin .add (.reg 25) (.reg 19))) (.load (.bin .add (.reg 30) (.reg 19))))
              (.assign 34 (.reg 19)) .nop) s .normal s' 12 :=
          runs_cond_iff.mpr ⟨1, 2, by simpa [hlt] using hltEval,
            by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrAsgn, by simp [Expr.size]⟩
        have hr : Runs w p bits stepBody s .normal s' 16 :=
          runs_cond_iff.mpr ⟨1, 12, hcond1,
            by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrIn, by simp [Expr.size]⟩
        have hfSucc : (List.range (j + 1)).find? (fun t => decide (oldRC t < newRC t)) = some j := by
          rw [List.range_succ, List.find?_append, hf]; simp [hlt]
        refine ⟨.normal, s', 16, hr, ⟨⟨by omega, by simp, hmem,
          fun r h1 h2 => by simpa [s', Function.update_of_ne h1, Function.update_of_ne h2] using hregs r h1 h2,
          by simp [s', hfSucc]⟩,
          by simp [s', hjr]⟩, by dsimp; omega⟩
      · have hrIn : Runs w p bits
            (.cond (.bin .lt (.load (.bin .add (.reg 25) (.reg 19))) (.load (.bin .add (.reg 30) (.reg 19))))
              (.assign 34 (.reg 19)) .nop) s .normal s 11 :=
          runs_cond_iff.mpr ⟨0, 1, by simpa [hlt] using hltEval,
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
        have hr : Runs w p bits stepBody s .normal s 15 :=
          runs_cond_iff.mpr ⟨1, 11, hcond1,
            by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrIn, by simp [Expr.size]⟩
        have hfSucc : (List.range (j + 1)).find? (fun t => decide (oldRC t < newRC t)) = none := by
          rw [List.range_succ, List.find?_append, hf]; simp [hlt]
        refine ⟨.normal, s, 15, hr, ⟨⟨by omega, by simp, hmem,
          fun r h1 h2 => by simpa [Function.update_of_ne h1] using hregs r h1 h2,
          by simp [h34d, hfSucc]⟩, hjr⟩, by dsimp; omega⟩
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 19) (lo := .const 0) (hi := .reg 28) 18 0 d (Nat.zero_le _) hw1 (fun _ => by omega)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp, rfl,
        fun r h1 _ => by simp [Function.update_of_ne h1],
        by simp [hr34]⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.2.1 28 (by decide) (by decide)).trans hr28])
    hstep
  obtain ⟨o, out, cost, hr, hInv, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv
  | normal =>
    exact ⟨out, cost, hr, by simp [Expr.size] at hc; omega, hInv.2.2.2.2, hInv.2.2.1, hInv.2.2.2.1⟩

theorem solverStateRep_update_passes_branD
    {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocal : Rcore.Local)
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} {branD' : ℕ} {passes' : Fin (cfg.P.d + 1) → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hsched' : SolverScheduleAt mem' tok.levelsEnd { model with branD := branD', passes := passes' })
    (hframe : ∀ a, tok.tag a ≠ 5 → mem' a = mem a) :
    let model' := { model with branD := branD', passes := passes' }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model' tok mem' ∧
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem' =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem := by
  dsimp only
  obtain ⟨hroot, hdet, hnum, hchP, hfrI, hfrT, hextM, hG0M, _, hoffR, hsn, hlct, htreeRep,
    hedgeAcc, hcores, htermH, htermB, htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hne5 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 5) : mem' a = mem a :=
    hframe a (fun h => hv (ht.symm.trans h))
  have htreeLoc := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  have htermLoc := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have htreeEq : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a →
      mem a = mem' a := fun a ha => (hne5 (t16 a ha) (by decide)).symm
  have hcoreEq : ∀ i (hi : i < cfg.P.d) a, Rcore.foot (tok.coreHandle i) (tok.coreTok i) a →
      mem a = mem' a := fun i hi a ha => (hne5 (t21 i hi a ha) (by omega)).symm
  refine ⟨⟨
    fun j hj => (hne5 (t1 j (by simpa [List.length] using hj)) (by decide)).trans (hroot j hj),
    fun j hj => (hne5 (t2 j (by simp [List.length] at hj; omega)) (by decide)).trans (hdet j hj),
    fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact (hne5 (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide)).trans (by rw [← h1]; exact hnum j hj),
    fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      rw [h1]; exact (hne5 (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide)).trans (by rw [← h1]; exact hchP j hj),
    hfrI,
    ⟨(hne5 t6 (by decide)).trans hfrT.1,
     fun e he => (hne5 (t7 e he) (by decide)).trans (hfrT.2.1 e he),
     fun e he => (hne5 (t8 e he) (by decide)).trans (hfrT.2.2 e he)⟩,
    hextM, hG0M, hsched',
    ⟨hoffR.1,
     fun j hj => by
       have h1 := hne5 (t14 j (lt_of_lt_of_le hj hoffR.1)) (by decide)
       rw [h1]; exact ⟨(hoffR.2.1 j hj).1, (hne5 (t15 _ (hoffR.2.1 j hj).1) (by decide)).trans (hoffR.2.1 j hj).2⟩,
     fun j₁ hj₁ j₂ hj₂ hne => by
       rw [hne5 (t14 j₁ (lt_of_lt_of_le hj₁ hoffR.1)) (by decide),
           hne5 (t14 j₂ (lt_of_lt_of_le hj₂ hoffR.1)) (by decide)]
       exact hoffR.2.2.1 j₁ hj₁ j₂ hj₂ hne,
     fun e he => by rw [hne5 (t15 e he) (by decide)]; exact hoffR.2.2.2.1 e he,
     fun e he h1 => by
       rw [hne5 (t15 e he) (by decide)] at h1
       obtain ⟨j, hj, hje⟩ := hoffR.2.2.2.2 e he h1
       exact ⟨j, hj, (hne5 (t14 j (lt_of_lt_of_le hj hoffR.1)) (by decide)).trans hje⟩⟩,
    hsn, hlct, (htreeLoc tok.treeHeap tok.tree tok.treeTok mem mem' htreeEq).1 htreeRep,
    ?_,
    fun i hi => ⟨(hne5 (t4 i (by omega)) (by decide)).trans (hcores i hi).1,
      by
        have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hne5 (t4 _ (by omega)) (by decide)).trans (by rw [← h1]; exact (hcores i hi).2.1),
      (hlocal (tok.coreHandle i) _ (tok.coreTok i) mem mem' (hcoreEq i hi)).1 (hcores i hi).2.2⟩,
    (hne5 (t4 cfg.P.d (by omega)) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1]; exact (hne5 (t4 _ (by omega)) (by decide)).trans (by rw [← h1]; exact htermB),
    (htermLoc tok.termHandle _ tok.termTok mem mem' (fun a ha =>
      (hne5 (t19 a ((lastLevelRepresentation_foot_indep_P tok.vcLast tok.ecLast 4 L P 0 _ _ _ _).mp ha))
        (by decide)).symm)).1 htermRep,
    ?_,
    ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16,
     fun e he => by
       have hcap := (hedgeAcc.1 e he).1
       dsimp only
       rw [hne5 (t12 _ hcap) (by decide), hne5 (t13 _ hcap) (by decide)]
       exact t1718 e he,
     t19, t20, t21⟩⟩, ?_⟩
  · refine ⟨fun e he => ?_, fun slot val hslot hpair => ?_⟩
    · obtain ⟨heiCap, hthr, hbr⟩ := hedgeAcc.1 e he
      refine ⟨heiCap, ?_, ?_⟩
      · rw [hne5 (t12 _ heiCap) (by decide)]
        exact hthr.congr (fun j hj => hne5 ((t1718 e he).1 j hj) (by decide))
      · dsimp only at hbr ⊢
        split_ifs at hbr ⊢ with hin
        · obtain ⟨hsnz, his, hnm, hst, hval⟩ := hbr
          have hslEq := hne5 (t9 _ heiCap) (by decide)
          have hslotLt : mem (tok.slots + model.extToInt e) < 2 * tok.tree.n := his.2
          rw [hslEq, hne5 (t12 _ heiCap) (by decide)]
          exact ⟨hsnz, his, (hne5 (t10 _ hslotLt) (by decide)).trans hnm,
            (hne5 (t11 _ hslotLt) (by decide)).trans hst, hval⟩
        · obtain ⟨hs0, val, acc, hrec, hfl, hac, hdet', hpush⟩ := hbr
          rw [hne5 (t9 _ heiCap) (by decide), hne5 (t13 _ heiCap) (by decide)]
          refine ⟨hs0, val, acc, hrec.congr (fun x hlo hhi => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) + (x - mem (tok.edgeRecords + model.extToInt e)) :=
              (Nat.add_sub_of_le hlo).symm
            rw [hx]; exact hne5 ((t1718 e he).2 hin _ (by omega)) (by decide)),
            hfl, hac, hdet', fun hnn => (hne5 (t15 _ heiCap) (by decide)).trans (hpush hnn)⟩
    · have hslotLt : slot < 2 * tok.tree.n := hslot.2
      obtain ⟨heiCap, hin, hsl, heE, he2i⟩ := hedgeAcc.2 slot val hslot hpair
      dsimp only at heiCap hin hsl heE he2i ⊢
      rw [hne5 (t10 slot hslotLt) (by decide)]
      exact ⟨heiCap, hin, (hne5 (t9 _ heiCap) (by decide)).trans hsl, heE, he2i⟩
  · refine ⟨fun j hj => (hne5 (t3 j hj) (by decide)).trans (hwire.1 j hj),
      hwire.2.1.of_agree (fun a h1 h2 => hne5 (t20 a h1 h2) (by decide)),
      hwire.2.2.1,
      ⟨fun ei hei => by
          have hc := (hwire.2.2.1.2 ei hei).1
          rw [hne5 (t9 ei hc) (by decide)]
          have hf := hwire.2.2.2.1.forward ei hei
          exact ⟨hf.1, hf.2.1, (hne5 (t10 _ hf.2.1.2) (by decide)).trans hf.2.2⟩,
       fun k hk hks => by
          rw [hne5 (t10 k hks.2) (by decide)]
          obtain ⟨hmemF, hsl⟩ := hwire.2.2.2.1.inverse k hk hks
          exact ⟨hmemF, (hne5 (t9 _ (hwire.2.2.1.2 _ hmemF).1) (by decide)).trans hsl⟩,
       fun ei hei => by
          rw [hne5 (t9 ei (hwire.2.2.1.2 ei hei).1) (by decide)]
          exact hwire.2.2.2.1.endpoints ei hei⟩,
      fun e he => by
        have hor := hwire.2.2.2.2 e he
        have heiCap := (hedgeAcc.1 e he).1
        dsimp only at hor ⊢
        split_ifs at hor ⊢ with hin
        · intro val hpair
          rw [hne5 (t9 _ heiCap) (by decide)] at hpair ⊢
          exact hor val hpair
        · intro val hpa
          rw [hne5 (t13 _ heiCap) (by decide)] at hpa
          exact hor val (hpa.congr fun x hlo hhi => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) + (x - mem (tok.edgeRecords + model.extToInt e)) :=
              (Nat.add_sub_of_le hlo).symm
            rw [hx]; exact (hne5 ((t1718 e he).2 hin _ (by omega)) (by decide)).symm)⟩
  · change (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem' +
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem') +
        tok.offReadyCount * drainUnit =
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem +
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) +
        tok.offReadyCount * drainUnit
    have hpt := (htreeLoc tok.treeHeap tok.tree tok.treeTok mem mem' htreeEq).2.symm
    have hpc : (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem') =
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) :=
      Finset.sum_congr rfl fun i _ => (hlocal (tok.coreHandle i.val)
        (chainLevelOrdAbs model.chain i.val) (tok.coreTok i.val) mem mem'
        (hcoreEq i.val i.isLt)).2.symm
    rw [hpt, hpc]

end MinCostFlow.MinRatio

end
