module

public import MinCostFlow.MinRatio.WireTreeSyncDelete
import MinCostFlow.LinkCut.PathProg.Implements
import WordRAM.Tactic

/-!
# Shared path-tree synchronization: insertion step and full loop (`WireTreeSyncLoop`)

Verifies the insertion branch (`wireTreeSyncInsert_step_runs`) and the full loop
(`wireTreeSyncLoop_runs`) of `wireTreeSyncLoop`, applying any packed
`TreeEditDifference oldF.E newF.E edits` to the solver's path tree and edge tables.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

private theorem lctLink_n (s : PathTreeState) (u v : ℕ) (val : Option PathEdgeValue) :
    (lctLink pathPayload s u v val).n = s.n := by
  unfold lctLink lctLinkCost
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Execute one insertion iteration of `wireTreeSyncStep`. -/
theorem wireTreeSyncInsert_step_runs {w L drainUnit : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {fmt : Num.Format w}
    {initTree : ℕ} {opTree : ℕ → ℕ} {bind canonCopy isNeg : ℕ}
    {root editPtr heap0 : ℕ} {memStart : ℕ → ℕ}
    {G0 oldF newF : MGraph} {edits done rem : List TreeChange} {e : ℕ}
    {tok : SolverToken cfg L Rcore} {canonVal : ℕ → PathEdgeValue} {B R : ℤ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {curHeap curOffCnt : ℕ} {st : State}
    (ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R)
    (hinv : WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
      done (.insert e :: rem) curTree curTreeTok curHeap curOffCnt st) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    ∃ st' cost curTree' curTreeTok' curHeap' curOffCnt',
      Runs w p ω (wireTreeSyncStep (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
        st .normal st' cost ∧
      WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
        (done ++ [.insert e]) rem curTree' curTreeTok' curHeap' curOffCnt' st' ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' st'.mem + curOffCnt' * drainUnit) ≤
        wireTreeSyncEditCost L drainUnit +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + curOffCnt * drainUnit) := by
  intro Rtree
  have hinv0 := hinv
  obtain ⟨happ, hr0, hr1, hr2, hr3, hr6, hr18, hr9, hr10, hr11, hr19, hr20, hr22, hr23, hr24,
    hr25, hr26, hHeapLo, hHeapHi, hz, hTreeFoot, hFrame, hTreeN,
    ⟨curTrees, curFree, curDepth, hLct, hNum, hNamed, hLive⟩, hTreeRep,
    hSlotThr, hOffSlot0, hOffRec, hOffPush, hOffWhere, hOffDisj,
    hOffCntMem, hOffInv⟩ := hinv
  have hlenEq : done.length + (rem.length + 1) = edits.length := by
    have := congrArg List.length happ; simp at this; omega
  have hHeapRoom : curHeap + wireTreeSyncEditSpace L < 2 ^ w := by
    have hmul : (done.length + 1) * wireTreeSyncEditSpace L ≤ edits.length * wireTreeSyncEditSpace L :=
      Nat.mul_le_mul_right _ (by omega)
    have hadd : done.length * wireTreeSyncEditSpace L + wireTreeSyncEditSpace L =
        (done.length + 1) * wireTreeSyncEditSpace L := by rw [Nat.add_mul, Nat.one_mul]
    have := ctx.room; omega
  have hHeapW : curHeap < 2 ^ w := by omega
  have htagLt {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap0 := ctx.tags.1 a (ht ▸ hv)
  have htagLtCur {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < curHeap :=
    lt_of_lt_of_le (htagLt ht hv) hHeapLo
  have hTreeFootLt : ∀ a, Rtree.foot tok.treeHeap curTreeTok a → a < curHeap := by
    intro a ha; rcases hTreeFoot a ha with h0 | ⟨_, hhi⟩
    · exact htagLtCur (ctx.tags.2.2.2.2.2.2.2.2.2.1 a h0) (by decide)
    · exact hhi
  have hnotF0 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) :
      ¬ Rtree.foot tok.treeHeap curTreeTok a := by
    intro hft; rcases hTreeFoot a hft with h0 | ⟨hlo, _⟩
    · have h16 := ctx.tags.2.2.2.2.2.2.2.2.2.1 a h0; rw [ht] at h16; exact hv16 h16
    · exact Nat.not_lt_of_ge hlo (htagLt ht hv)
  have hneTag {a b va vb : ℕ} (ha : tok.tag a = va) (hb : tok.tag b = vb) (hne : va ≠ vb) : a ≠ b :=
    fun h => hne (ha.symm.trans (h ▸ hb))
  have heSdiff : e ∈ newF.E \ oldF.E :=
    ctx.diff.insert_mem_sdiff (happ ▸ List.mem_append_right _ List.mem_cons_self)
  have heNew : e ∈ newF.E := (Finset.mem_sdiff.mp heSdiff).1
  have heNotOld : e ∉ oldF.E := (Finset.mem_sdiff.mp heSdiff).2
  have heG : e ∈ G0.E := ctx.newSub heNew
  have heCap : e < tok.intCap := ctx.capE e heG
  obtain ⟨hcurSubNew, heNotCur, _⟩ := ctx.diff.insert_cursor happ.symm
  have hcurSubG0 := wireSync_curE_sub_G0 ctx.diff happ ctx.oldSub ctx.newSub
  have hsetEq : applyTreeChanges oldF.E (done ++ [.insert e]) =
      insert e (applyTreeChanges oldF.E done) := by
    unfold applyTreeChanges; rw [List.foldl_append]; rfl
  let s1 := { st with regs := Function.update st.regs 7 1 }
  let s2 := { s1 with regs := Function.update s1.regs 8 e }
  let s3 := { s2 with regs := Function.update s2.regs 12 (G0.tail e + 1) }
  let s4 := { s3 with regs := Function.update s3.regs 13 (G0.head e + 1) }
  let recPtr := st.mem (tok.edgeRecords + e)
  have hrecEqStart : recPtr = memStart (tok.edgeRecords + e) := (hOffWhere e heG heNotCur).2 heNotOld
  have hrecEnd : recPtr + (2 + 4 * L) ≤ curHeap := by
    have ht18 := ctx.tags.2.2.2.2.2.2.2.2.2.2.1 e heG heNotOld (2 + 4 * L - 1) (by omega)
    have := htagLtCur ht18 (by decide); omega
  have hrecAt : PathEdgeAt st.mem recPtr 4 L (some (canonVal e)) := hOffRec e heG heNotCur
  have hfwdE : (canonVal e).forward = true := (ctx.canonProp e heG).1
  have hcurFits : pathTreeFits 4 L curTree := hNum.fits hLct (by rw [hTreeN]; exact ctx.capT)
  have hBudgetLe := pathTreeBudget_le_of_log (n := curTree.n) (hTreeN ▸ ctx.logW)
  -- Establish disconnection and numeric invariant for `lctLink`
  have hNamedPref : TreeEditNamedPrefix curTree oldF newF G0 (.insert e :: rem)
      (fun ei => st.mem (tok.slots + ei)) (fun sl => st.mem (tok.names + sl)) :=
    ⟨done, curTrees, curFree, curDepth, happ.symm ▸ ctx.diff, hLct, hNamed,
      fun f hf => hTreeN.symm ▸ ctx.vtxE f (hcurSubG0 hf)⟩
  have hTailLt : G0.tail e < curTree.n := hTreeN.symm ▸ (ctx.vtxE e heG).1
  have hHeadLt : G0.head e < curTree.n := hTreeN.symm ▸ (ctx.vtxE e heG).2
  have hTailEq : newF.tail e = G0.tail e := (ctx.newEnds e heNew).1.symm
  have hHeadEq : newF.head e = G0.head e := (ctx.newEnds e heNew).2.symm
  have hDisc : ¬ pathTreeConnected curTree (vid (G0.tail e)) (vid (G0.head e)) := by
    rw [← hTailEq, ← hHeadEq]
    exact hNamedPref.insert_disconnected ctx.newForest ctx.newEnds
      (hTailEq.symm ▸ hTailLt) (hHeadEq.symm ▸ hHeadLt)
  have hFreeNZ : curTree.freeHead ≠ 0 :=
    treeEdit_freeHead_of_disconnected ⟨_, _, _, hLct⟩ hTailLt hHeadLt hDisc
  have hneCur : ∀ f ∈ applyTreeChanges oldF.E done, G0.tail f ≠ G0.head f := fun f hf =>
    named_account_endpoints_ne
      (G := { V := G0.V, E := applyTreeChanges oldF.E done, tail := G0.tail, head := G0.head })
      hLct hNamed hf (hTreeN.symm ▸ (ctx.vtxE f (hcurSubG0 hf)).1)
  have hvCur : ∀ f ∈ applyTreeChanges oldF.E done, G0.tail f < curTree.n ∧ G0.head f < curTree.n :=
    fun f hf => hTreeN.symm ▸ ctx.vtxE f (hcurSubG0 hf)
  obtain ⟨linkTrees, linkFree, linkDepth, hLctLink, hNamedLink, hLiveLink⟩ :=
    hLive.link hNamed hLct hvCur hneCur heNotCur hTailLt hHeadLt hDisc (canonVal e)
  simp only [hfwdE, ↓reduceIte, Function.update_eq_self] at hLctLink hNamedLink hLiveLink
  -- Also prove `PathTreeNumericInv` after `lctLink`
  have hDiscRoot : subRoot (inducedSubPar pathPayload curTree.splay curTrees)
      (curTrees.flatMap AuxTree.toList).length (vid (G0.tail e)) ≠
      subRoot (inducedSubPar pathPayload curTree.splay curTrees)
      (curTrees.flatMap AuxTree.toList).length (vid (G0.head e)) :=
    fun h => hDisc ((pathTreeConnected_iff_induced_roots hLct hTailLt hHeadLt).mpr h)
  have hFreeNonempty : curFree ≠ [] := fun hnil => by
    have hinvF := hLct.freeListInv; rw [hnil] at hinvF; exact hFreeNZ hinvF
  obtain ⟨freshSlot, restFree, hFreeEq⟩ := List.exists_cons_of_ne_nil hFreeNonempty
  have hFreshEq : curTree.freeHead = freshSlot := by
    have hinvF := hLct.freeListInv; rw [hFreeEq] at hinvF; exact hinvF.2.1
  have huV : isVertex curTree.n (vid (G0.tail e)) := by unfold isVertex vid; omega
  have hvV : isVertex curTree.n (vid (G0.head e)) := by unfold isVertex vid; omega
  obtain ⟨linkTrees', linkDepth', hLctLink', hNumLink'⟩ :=
    pathTreeNumericInv_link (hFreeEq ▸ hLct) hNum huV hvV hDiscRoot
      (value := some (canonVal e)) (fun v hv => by
        cases Option.some.inj hv
        exact (ctx.canonProp e heG).2)
  have hFreeLinkEq : linkFree = restFree :=
    freeListInv_unique hLctLink.freeListInv hLctLink'.freeListInv
  subst hFreeLinkEq
  have hNumLink : PathTreeNumericInv (lctLink pathPayload curTree (vid (G0.tail e)) (vid (G0.head e))
      (some (canonVal e))) linkTrees B R := hNumLink'.relabel hLctLink' hLctLink
  have hLinkN : (lctLink pathPayload curTree (vid (G0.tail e)) (vid (G0.head e))
      (some (canonVal e))).n = G0.n := (lctLink_n _ _ _ _).trans hTreeN
  have hLinkFits : pathTreeFits 4 L (lctLink pathPayload curTree (vid (G0.tail e)) (vid (G0.head e))
      (some (canonVal e))) := hNumLink.fits hLctLink (by rw [hLinkN]; exact ctx.capT)
  -- I1-I2: `reg 17 := curHeap`, `reg 14 := edgeRecords[e]`
  let i1 := { s4 with regs := Function.update s4.regs 17 curHeap }
  let i2 := { i1 with regs := Function.update i1.regs 14 recPtr }
  have ri1 : Runs w p ω (.assign 17 (.reg 3)) s4 .normal i1 2 :=
    runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, s4, s3, s2, s1, hr3], rfl, rfl, rfl⟩
  have hrecE_lt : tok.edgeRecords + e < curHeap := htagLtCur (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide)
  have ri2 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 22) (.reg 8)))) i1 .normal i2 5 :=
    runs_assign_iff.mpr ⟨recPtr, by
      simp [Expr.eval, BinOp.eval, i1, s4, s3, s2, s1, hr22, show tok.edgeRecords + e < 2 ^ w by omega, recPtr],
      rfl, rfl, rfl⟩
  -- I3: `opTree 0` (`linkTree`) on `[tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap]`
  have hreadEq : readPathEdge st.mem recPtr 4 L = some (canonVal e) := readPathEdge_eq hrecAt
  have hpre0 : (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)).pre
      0 curTree [tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap] st.mem := by
    refine ⟨⟨_, _, _, hLct⟩, ctx.fmtBits.symm ▸ hcurFits, hTreeN.symm ▸ ctx.nW,
      ctx.fmtBits.symm ▸ hTreeN.symm ▸ ctx.logW,
      tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap, rfl, huV, hvV, hDisc, hFreeNZ,
      hrecEnd, ?_, ?_, ?_⟩
    · rw [ctx.fmtBits, hreadEq]; exact hrecAt
    · rw [ctx.fmtBits, hreadEq]; rfl
    · rw [ctx.fmtBits, hreadEq]; exact hLinkFits
  have hroom0 : curHeap + (pathTreeMachineContract fmt L LinkCut.PathProg.pathC
      (LinkCut.PathProg.pathAlloc L)).space 0 curTree
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap] st.mem < 2 ^ w := by
    change curHeap + LinkCut.PathProg.pathAlloc L 0 curTree.n
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap] < 2 ^ w
    simp only [LinkCut.PathProg.pathAlloc, show (0 : ℕ) ≠ 7 by decide, ↓reduceIte]
    unfold wireTreeSyncEditSpace at hHeapRoom; omega
  have hu1W : G0.tail e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).1; have := ctx.nW; omega
  have hv1W : G0.head e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).2; have := ctx.nW; omega
  obtain ⟨b0, hb0, o0, out0, c0, hr0_op, linkSt, tok1, hRep1, hPost0, hResp0, hc0⟩ :=
    ctx.treeImpl.2.2 0 tok.treeHeap curTree curTreeTok
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap] st.mem i2.pos ω
      (by simp [ctx.treeHeapLt, hu1W, hv1W, show recPtr < 2 ^ w by omega, hHeapW]) rfl
      hTreeRep hpre0 hTreeFootLt hz hroom0
  obtain ⟨hLinkStEq, hSlotWritten⟩ := hPost0
  change linkSt = lctLink pathPayload curTree (G0.tail e + 1) (G0.head e + 1)
    (readPathEdge st.mem recPtr fmt.limbBits L) at hLinkStEq
  rw [ctx.fmtBits, hreadEq] at hLinkStEq
  subst hLinkStEq
  have hSlotAtHeap : out0.mem curHeap = curTree.freeHead := by simpa [heapArg] using hSlotWritten
  let h1 := o0.value
  have hh1Lo : curHeap ≤ h1 := hResp0.1
  have hh1Hi : h1 ≤ curHeap + (20 * LinkCut.PathProg.treeLimbs L + 100) := by
    have := hResp0.2.1; change h1 ≤ curHeap + LinkCut.PathProg.pathAlloc L 0 curTree.n
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap] at this
    simpa [LinkCut.PathProg.pathAlloc] using this
  have hResp0_foot : ∀ a, Rtree.foot tok.treeHeap tok1 a →
      Rtree.foot tok.treeHeap curTreeTok a ∨ (curHeap ≤ a ∧ a < h1) := hResp0.2.2.2.2
  have hResp0_frame : ∀ a < curHeap, ¬ Rtree.foot tok.treeHeap curTreeTok a →
      out0.mem a = st.mem a := hResp0.2.2.2.1
  let i3 : State := { regs := Function.update i2.regs 3 h1, mem := out0.mem, pos := out0.pos }
  have ri3 : Runs w p ω (.call 3 (opTree 0) [.reg 0, .reg 12, .reg 13, .reg 14, .reg 17])
      i2 .normal i3 (c0 + 6) :=
    runs_call_iff.mpr ⟨[tok.treeHeap, G0.tail e + 1, G0.head e + 1, recPtr, curHeap], b0, o0, out0, c0, by
      simp [evalArgs, Expr.eval, i2, i1, s4, s3, s2, s1, hr0], hb0, hr0_op, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  -- I4-I5: `reg 15 := mem[curHeap]`, `bind [slots, names, e, slot, h1]`
  let newSlot := curTree.freeHead
  have hNewSlotIs : isEdgeSlot curTree.n newSlot := by
    have hfv := hLct.freeValid freshSlot (by rw [hFreeEq]; exact List.mem_cons_self)
    rwa [← hFreshEq] at hfv
  have hNewSlotLt : newSlot < 2 * G0.n := by unfold isEdgeSlot at hNewSlotIs; omega
  let i4 := { i3 with regs := Function.update i3.regs 15 newSlot }
  have ri4 : Runs w p ω (.assign 15 (.load (.reg 17))) i3 .normal i4 3 :=
    runs_assign_iff.mpr ⟨newSlot, by simp [Expr.eval, i3, i2, i1, hSlotAtHeap, newSlot], rfl, rfl, rfl⟩
  have hslotsE_lt : tok.slots + e < curHeap := htagLtCur (ctx.tags.2.2.1 e heCap) (by decide)
  have hnamesS_lt : tok.names + newSlot < curHeap := htagLtCur (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide)
  have hslotThrS_lt : tok.slotThresholds + newSlot < curHeap :=
    htagLtCur (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide)
  have hedgeThrE_lt : tok.edgeThresholds + e < curHeap :=
    htagLtCur (ctx.tags.2.2.2.2.2.1 e heCap) (by decide)
  have hh1W : h1 < 2 ^ w := by unfold wireTreeSyncEditSpace at hHeapRoom; omega
  obtain ⟨i5, cBind, retBind, ri5, hpBind, hr5Bind, hi5Regs, hcBind⟩ :=
    runs_call_of_meetsContract (r := 3) (args := [.reg 19, .reg 20, .reg 8, .reg 15, .reg 3])
      ctx.bindOk (st := i4) (vs := [tok.slots, tok.names, e, newSlot, h1])
      (by simp [evalArgs, Expr.eval, i4, i3, i2, i1, s4, s3, s2, s1, hr19, hr20])
      (by simp [show tok.slots < 2 ^ w by omega, show tok.names < 2 ^ w by omega,
        show e < 2 ^ w by omega, show newSlot < 2 ^ w by omega, hh1W])
      ⟨tok.slots, tok.names, e, newSlot, h1, rfl, by omega, by omega,
        hneTag (ctx.tags.2.2.1 e heCap) (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide),
        hh1W, hResp0.2.2.1⟩ ω
  obtain ⟨hretBindEq, hmemBind, hzBind⟩ := hpBind
  change retBind = h1 at hretBindEq; subst hretBindEq
  change i5.mem = Function.update (Function.update out0.mem (tok.slots + e) newSlot)
    (tok.names + newSlot) e at hmemBind
  have hbindCost : cBind ≤ 24 := by
    simp only [pathSlotBindContract, argsSize, Expr.size] at hcBind
    exact Nat.le_trans hcBind (by norm_num)
  -- I6: `slotThresholds[newSlot] := edgeThresholds[e]`
  have hedgeThrEq : i5.mem (tok.edgeThresholds + e) = st.mem (tok.edgeThresholds + e) := by
    rw [hmemBind,
      Function.update_of_ne (hneTag (ctx.tags.2.2.2.2.2.1 e heCap) (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide)),
      Function.update_of_ne (hneTag (ctx.tags.2.2.2.2.2.1 e heCap) (ctx.tags.2.2.1 e heCap) (by decide))]
    exact hResp0_frame _ hedgeThrE_lt (hnotF0 (ctx.tags.2.2.2.2.2.1 e heCap) (by decide) (by decide))
  let i6 := { i5 with mem := Function.update i5.mem (tok.slotThresholds + newSlot) (st.mem (tok.edgeThresholds + e)) }
  have hslotThrSW : tok.slotThresholds + newSlot < 2 ^ w := by omega
  have hedgeThrEW : tok.edgeThresholds + e < 2 ^ w := by omega
  have ri6 : Runs w p ω (.store (.bin .add (.reg 24) (.reg 15)) (.load (.bin .add (.reg 23) (.reg 8))))
      i5 .normal i6 8 :=
    runs_store_iff.mpr ⟨tok.slotThresholds + newSlot, st.mem (tok.edgeThresholds + e), by
      simp [Expr.eval, BinOp.eval, hi5Regs 24 (by decide), hi5Regs 15 (by decide), i4, i3, i2, i1,
        s4, s3, s2, s1, hr24, hslotThrSW],
      by simp [Expr.eval, BinOp.eval, hi5Regs 23 (by decide), hi5Regs 8 (by decide), i4, i3, i2, i1,
        s4, s3, s2, s1, hr23, hedgeThrEW, hedgeThrEq],
      rfl, rfl, rfl⟩
  have rIns : Runs w p ω (wireTreeSyncInsert (opTree 0) bind) s4 .normal i6
      (2 + (5 + ((c0 + 6) + (3 + (cBind + 8 + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨i1, 2, _, ri1,
    runs_seq_iff.mpr (Or.inr ⟨i2, 5, _, ri2,
    runs_seq_iff.mpr (Or.inr ⟨i3, c0 + 6, _, ri3,
    runs_seq_iff.mpr (Or.inr ⟨i4, 3, _, ri4,
    runs_seq_iff.mpr (Or.inr ⟨i5, cBind, 8, ri5, ri6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hi6_keep (r : ℕ) (h3 : r ≠ 3) (h7 : r ≠ 7) (h8 : r ≠ 8) (h12 : r ≠ 12) (h13 : r ≠ 13)
      (h14 : r ≠ 14) (h15 : r ≠ 15) (h17 : r ≠ 17) : i6.regs r = st.regs r := by
    change i5.regs r = st.regs r; rw [hi5Regs r h3]
    simp [i4, i3, i2, i1, s4, s3, s2, s1, Function.update_of_ne, h3, h7, h8, h12, h13, h14, h15, h17]
  let out := { i6 with regs := Function.update (Function.update i6.regs 6
    (editPtr + 2 * (done.length + 1))) 18 rem.length }
  have rStep := wireSync_step_wrap ctx hinv0 (tagVal := 1) (e := e) rfl heG rIns
    ((hi6_keep 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr6)
    ((hi6_keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr18)
  -- Helper: relate `i6.mem` to `out0.mem` and `st.mem`
  have hnotF1 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) :
      ¬ Rtree.foot tok.treeHeap tok1 a := by
    intro hft; rcases hResp0_foot a hft with h0 | ⟨hlo, _⟩
    · exact hnotF0 ht hv hv16 h0
    · exact Nat.not_lt_of_ge hlo (htagLtCur ht hv)
  have hi6_foot1 : ∀ a, Rtree.foot tok.treeHeap tok1 a → out0.mem a = i6.mem a := fun a ha => by
    symm; dsimp only [i6]; rw [hmemBind]
    rw [Function.update_of_ne (by intro h; subst h; exact hnotF1 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide) (by decide) ha),
      Function.update_of_ne (by intro h; subst h; exact hnotF1 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide) (by decide) ha),
      Function.update_of_ne (by intro h; subst h; exact hnotF1 (ctx.tags.2.2.1 e heCap) (by decide) (by decide) ha)]
  obtain ⟨hRep1_iff, hPhi1_eq⟩ := ctx.treeImpl.1 tok.treeHeap _ tok1 out0.mem i6.mem hi6_foot1
  have hRep1_i6 := hRep1_iff hRep1
  have hi6_eq_st (a : ℕ) (hlt : a < curHeap) (hne9 : a ≠ tok.slots + e)
      (hne10 : a ≠ tok.names + newSlot) (hne11 : a ≠ tok.slotThresholds + newSlot)
      (hnf0 : ¬ Rtree.foot tok.treeHeap curTreeTok a) : i6.mem a = st.mem a := by
    dsimp only [i6]; rw [hmemBind]
    rw [Function.update_of_ne hne11, Function.update_of_ne hne10, Function.update_of_ne hne9]
    exact hResp0_frame a hlt hnf0
  have hSlotUpd (ei : ℕ) (hei : ei ∈ insert e (applyTreeChanges oldF.E done)) :
      i6.mem (tok.slots + ei) = Function.update (fun x => st.mem (tok.slots + x)) e newSlot ei := by
    have heiG : ei ∈ G0.E := by
      rcases Finset.mem_insert.mp hei with rfl | hm; exact heG; exact hcurSubG0 hm
    have ht9 := ctx.tags.2.2.1 ei (ctx.capE ei heiG)
    dsimp only [i6]; rw [hmemBind]
    rw [Function.update_of_ne (hneTag ht9 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide)),
      Function.update_of_ne (hneTag ht9 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))]
    by_cases heq : ei = e
    · subst heq; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne heq]
      exact hResp0_frame _ (htagLtCur ht9 (by decide)) (hnotF0 ht9 (by decide) (by decide))
  have hNameUpd (sl : ℕ) (his : isEdgeSlot (lctLink pathPayload curTree (vid (G0.tail e))
      (vid (G0.head e)) (some (canonVal e))).n sl) :
      i6.mem (tok.names + sl) = Function.update (fun x => st.mem (tok.names + x)) newSlot e sl := by
    have hslLt : sl < 2 * G0.n := by unfold isEdgeSlot at his; omega
    have ht10 := ctx.tags.2.2.2.1 sl hslLt
    dsimp only [i6]; rw [hmemBind]
    rw [Function.update_of_ne (hneTag ht10 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))]
    by_cases heq : sl = newSlot
    · subst heq; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne heq,
        Function.update_of_ne (hneTag ht10 (ctx.tags.2.2.1 e heCap) (by decide))]
      exact hResp0_frame _ (htagLtCur ht10 (by decide)) (hnotF0 ht10 (by decide) (by decide))
  have hRecEq_all (ei : ℕ) (heiG : ei ∈ G0.E) : i6.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) := by
    have ht13 := ctx.tags.2.2.2.2.2.2.1 ei (ctx.capE ei heiG)
    exact hi6_eq_st _ (htagLtCur ht13 (by decide))
      (hneTag ht13 (ctx.tags.2.2.1 e heCap) (by decide))
      (hneTag ht13 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
      (hneTag ht13 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
      (hnotF0 ht13 (by decide) (by decide))
  -- Assemble `WireSyncInv` and amortized cost
  refine ⟨out, _, lctLink pathPayload curTree (vid (G0.tail e)) (vid (G0.head e))
      (some (canonVal e)), tok1, h1, curOffCnt, rStep, ?_, ?_⟩
  · refine ⟨by simpa [List.append_assoc] using happ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, ?_, ?_, ?_, ?_, hLinkN,
      ⟨linkTrees, linkFree, linkDepth, hLctLink, hNumLink,
        by rw [hsetEq]; exact namedSlots_congr_slot hNamedLink hSlotUpd (fun sl _ his => hNameUpd sl his),
        by rw [hsetEq]; exact liveAccounts_congr_slot hLiveLink hSlotUpd⟩,
      hRep1_i6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [out, hi6_keep 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0]
    · simp [out, hi6_keep 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1]
    · simp [out, hi6_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr2]
    · simp [out, i6, hr5Bind]
    · simp [out, List.length_append]
    · simp [out]
    · simp [out, hi6_keep 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr9]
    · simp [out, hi6_keep 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr10]
    · simp [out, hi6_keep 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr11]
    · simp [out, hi6_keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr19]
    · simp [out, hi6_keep 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20]
    · simp [out, hi6_keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22]
    · simp [out, hi6_keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr23]
    · simp [out, hi6_keep 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr24]
    · simp [out, hi6_keep 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr25]
    · simp [out, hi6_keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr26]
    · rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
      have hstepLe : h1 ≤ curHeap + wireTreeSyncEditSpace L := by unfold wireTreeSyncEditSpace; omega
      omega
    · intro a ha; dsimp only [out, i6]; rw [Function.update_of_ne (by omega)]; exact hzBind a ha
    · intro a ha
      rcases hResp0_foot a ha with h0' | ⟨hlo, hhi⟩
      · rcases hTreeFoot a h0' with hbase | ⟨hlo, hhi⟩
        · exact Or.inl hbase
        · exact Or.inr ⟨hlo, by omega⟩
      · exact Or.inr ⟨by omega, hhi⟩
    · intro a ha hne11 h9 h10 h11 h13 h14 h15 h16
      have hnf0 : ¬ Rtree.foot tok.treeHeap curTreeTok a := fun hft => by
        rcases hTreeFoot a hft with h0 | ⟨hlo, _⟩
        · exact h16 (ctx.tags.2.2.2.2.2.2.2.2.2.1 a h0)
        · omega
      exact (hi6_eq_st a (by omega)
        (fun h => h9 (h ▸ ctx.tags.2.2.1 e heCap))
        (fun h => h10 (h ▸ ctx.tags.2.2.2.1 newSlot hNewSlotLt))
        (fun h => h11 (h ▸ ctx.tags.2.2.2.2.1 newSlot hNewSlotLt)) hnf0).trans
        (hFrame a ha hne11 h9 h10 h11 h13 h14 h15 h16)
    · intro ei hei; rw [hsetEq] at hei
      rw [hSlotUpd ei hei]
      rcases Finset.mem_insert.mp hei with rfl | hm
      · simp only [Function.update_self]
        have hL1 : i6.mem (tok.slotThresholds + newSlot) = st.mem (tok.edgeThresholds + ei) := by simp [i6]
        have hR1 : i6.mem (tok.edgeThresholds + ei) = st.mem (tok.edgeThresholds + ei) :=
          hi6_eq_st _ hedgeThrE_lt
            (hneTag (ctx.tags.2.2.2.2.2.1 ei heCap) (ctx.tags.2.2.1 ei heCap) (by decide))
            (hneTag (ctx.tags.2.2.2.2.2.1 ei heCap) (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
            (hneTag (ctx.tags.2.2.2.2.2.1 ei heCap) (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
            (hnotF0 (ctx.tags.2.2.2.2.2.1 ei heCap) (by decide) (by decide))
        rw [hL1, hR1]
      · have hne : ei ≠ e := fun h => heNotCur (h ▸ hm)
        rw [Function.update_of_ne hne]
        have hslotNe : st.mem (tok.slots + ei) ≠ newSlot := fun hEq => by
          have hact := (hNamed.forward ei hm).1
          have his := (hNamed.forward ei hm).2.1
          exact (hLct.partitionSlots _ his).mp hact (by
            rw [hEq]; dsimp only [newSlot]; rw [hFreshEq, hFreeEq]; exact List.mem_cons_self)
        have hslLt : st.mem (tok.slots + ei) < 2 * G0.n := by
          have := (hNamed.forward ei hm).2.1; unfold isEdgeSlot at this; omega
        have ht11 := ctx.tags.2.2.2.2.1 _ hslLt
        have ht12 := ctx.tags.2.2.2.2.2.1 ei (ctx.capE ei (hcurSubG0 hm))
        have hL1 := hi6_eq_st _ (htagLtCur ht11 (by decide))
          (hneTag ht11 (ctx.tags.2.2.1 e heCap) (by decide))
          (hneTag ht11 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide)) (by omega)
          (hnotF0 ht11 (by decide) (by decide))
        have hR1 := hi6_eq_st _ (htagLtCur ht12 (by decide))
          (hneTag ht12 (ctx.tags.2.2.1 e heCap) (by decide))
          (hneTag ht12 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hneTag ht12 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hnotF0 ht12 (by decide) (by decide))
        rw [hL1, hR1]; exact hSlotThr ei hm
    · intro ei heiG hnot; rw [hsetEq] at hnot
      have hne : ei ≠ e := fun h => hnot (h ▸ Finset.mem_insert_self _ _)
      have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_insert_of_mem hm)
      have ht9 := ctx.tags.2.2.1 ei (ctx.capE ei heiG)
      exact (hi6_eq_st _ (htagLtCur ht9 (by decide)) (by omega)
        (hneTag ht9 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
        (hneTag ht9 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
        (hnotF0 ht9 (by decide) (by decide))).trans (hOffSlot0 ei heiG hnot')
    · intro ei heiG hnot; rw [hsetEq] at hnot
      have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_insert_of_mem hm)
      rw [hRecEq_all ei heiG]
      refine (hOffRec ei heiG hnot').congr fun a ha1 ha2 => ?_
      by_cases hOld : ei ∈ oldF.E
      · obtain ⟨hlo, hhi, hnf⟩ := (hOffWhere ei heiG hnot').1 hOld
        exact hi6_eq_st a (by omega)
          (by have := htagLt (ctx.tags.2.2.1 e heCap) (by decide); omega)
          (by have := htagLt (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide); omega)
          (by have := htagLt (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide); omega)
          (hnf a ha1 (by omega))
      · have hrecEq := (hOffWhere ei heiG hnot').2 hOld
        have ht18 := ctx.tags.2.2.2.2.2.2.2.2.2.2.1 ei heiG hOld (a - st.mem (tok.edgeRecords + ei)) (by omega)
        have hsub : memStart (tok.edgeRecords + ei) + (a - st.mem (tok.edgeRecords + ei)) = a := by omega
        rw [hsub] at ht18
        exact hi6_eq_st a (htagLtCur ht18 (by decide))
          (hneTag ht18 (ctx.tags.2.2.1 e heCap) (by decide))
          (hneTag ht18 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hneTag ht18 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hnotF0 ht18 (by decide) (by decide))
    · intro ei heiG hnot hdet; rw [hsetEq] at hnot
      have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_insert_of_mem hm)
      have ht15 := ctx.tags.2.2.2.2.2.2.2.2.1 ei (ctx.capE ei heiG)
      exact (hi6_eq_st _ (htagLtCur ht15 (by decide))
        (hneTag ht15 (ctx.tags.2.2.1 e heCap) (by decide))
        (hneTag ht15 (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
        (hneTag ht15 (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
        (hnotF0 ht15 (by decide) (by decide))).trans (hOffPush ei heiG hnot' hdet)
    · intro ei heiG hnot; rw [hsetEq] at hnot
      have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_insert_of_mem hm)
      rw [hRecEq_all ei heiG]
      refine ⟨fun hOld => ?_, (hOffWhere ei heiG hnot').2⟩
      obtain ⟨hlo, hhi, hnf⟩ := (hOffWhere ei heiG hnot').1 hOld
      refine ⟨hlo, by omega, fun a ha1 ha2 hft => ?_⟩
      rcases hResp0_foot a hft with h0' | ⟨hlo0, _⟩
      · exact hnf a ha1 ha2 h0'
      · omega
    · intro e1 he1 e2 he2 hne hnot1 hnot2; rw [hsetEq] at hnot1 hnot2
      rw [hRecEq_all e1 he1, hRecEq_all e2 he2]
      exact hOffDisj e1 he1 e2 he2 hne
        (fun hm => hnot1 (Finset.mem_insert_of_mem hm))
        (fun hm => hnot2 (Finset.mem_insert_of_mem hm))
    · exact (hi6_eq_st _ (htagLtCur (ctx.tags.2.1 11 (by omega)) (by decide))
        (hneTag (ctx.tags.2.1 11 (by omega)) (ctx.tags.2.2.1 e heCap) (by decide))
        (hneTag (ctx.tags.2.1 11 (by omega)) (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
        (hneTag (ctx.tags.2.1 11 (by omega)) (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
        (hnotF0 (ctx.tags.2.1 11 (by omega)) (by decide) (by decide))).trans hOffCntMem
    · have hagreeL : ∀ j < tok.intCap, i6.mem (tok.offReadyList + j) = st.mem (tok.offReadyList + j) :=
        fun j hj => hi6_eq_st _ (htagLtCur (ctx.tags.2.2.2.2.2.2.2.1 j hj) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.1 e heCap) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hnotF0 (ctx.tags.2.2.2.2.2.2.2.1 j hj) (by decide) (by decide))
      have hagreeI : ∀ j < tok.intCap, i6.mem (tok.inOffReady + j) = st.mem (tok.inOffReady + j) :=
        fun j hj => hi6_eq_st _ (htagLtCur (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.1 e heCap) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.2.2.1 newSlot hNewSlotLt) (by decide))
          (hnotF0 (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (by decide) (by decide))
      obtain ⟨hc, h1', h2', h3', h4'⟩ := hOffInv
      refine ⟨hc, fun j hj => ?_, fun j1 hj1 j2 hj2 hne => ?_, fun k hk => ?_, fun k hk h1'' => ?_⟩
      · rw [hagreeL j (by omega)]; exact ⟨(h1' j hj).1, (hagreeI _ (h1' j hj).1).trans (h1' j hj).2⟩
      · rw [hagreeL j1 (by omega), hagreeL j2 (by omega)]; exact h2' j1 hj1 j2 hj2 hne
      · rw [hagreeI k hk]; exact h3' k hk
      · rw [hagreeI k hk] at h1''; obtain ⟨j, hj, hje⟩ := h4' k hk h1''
        exact ⟨j, hj, (hagreeL j (by omega)).trans hje⟩
  · -- Amortized cost bound
    change _ + (Rtree.phi tok.treeHeap tok1 i6.mem + curOffCnt * drainUnit) ≤ _
    rw [← hPhi1_eq]
    have hBudLe : pathTreeBudget LinkCut.PathProg.pathC L curTree.n ≤
        25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) :=
      pathTreeBudget_le_of_log (hTreeN.symm ▸ ctx.logW)
    have hc0' : c0 + Rtree.phi tok.treeHeap tok1 out0.mem ≤
        25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + Rtree.phi tok.treeHeap curTreeTok st.mem :=
      le_trans hc0 (Nat.add_le_add_right hBudLe _)
    unfold wireTreeSyncEditCost
    linarith [hc0', hbindCost]

/-- Execute the full `wireTreeSyncLoop` over all remaining `rem` edits. -/
theorem wireTreeSyncLoop_runs {w L drainUnit : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {fmt : Num.Format w}
    {initTree : ℕ} {opTree : ℕ → ℕ} {bind canonCopy isNeg : ℕ}
    {root editPtr heap0 : ℕ} {memStart : ℕ → ℕ}
    {G0 oldF newF : MGraph} {edits done rem : List TreeChange}
    {tok : SolverToken cfg L Rcore} {canonVal : ℕ → PathEdgeValue} {B R : ℤ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {curHeap curOffCnt : ℕ} {st : State}
    (ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R)
    (hinv : WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
      done rem curTree curTreeTok curHeap curOffCnt st) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    ∃ st' cost curTree' curTreeTok' curHeap' curOffCnt',
      Runs w p ω (wireTreeSyncLoop (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
        st .normal st' cost ∧
      WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
        edits [] curTree' curTreeTok' curHeap' curOffCnt' st' ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' st'.mem + curOffCnt' * drainUnit) ≤
        rem.length * (wireTreeSyncEditCost L drainUnit + 2) + 2 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + curOffCnt * drainUnit) := by
  intro Rtree
  induction rem generalizing done curTree curTreeTok curHeap curOffCnt st with
  | nil =>
    have hdoneEq : done = edits := by simpa using hinv.1
    subst hdoneEq
    have h18 : st.regs 18 = 0 := hinv.2.2.2.2.2.2.1
    exact ⟨st, 2, curTree, curTreeTok, curHeap, curOffCnt,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, h18], rfl, rfl, rfl⟩), hinv, by omega⟩
  | cons ch rest ih =>
    have h18 : st.regs 18 = rest.length + 1 := hinv.2.2.2.2.2.2.1
    have hstep : ∃ mid cStep t1 tok1 h1 off1,
        Runs w p ω (wireTreeSyncStep (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
          st .normal mid cStep ∧
        WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
          (done ++ [ch]) rest t1 tok1 h1 off1 mid ∧
        cStep + (Rtree.phi tok.treeHeap tok1 mid.mem + off1 * drainUnit) ≤
          wireTreeSyncEditCost L drainUnit +
            (Rtree.phi tok.treeHeap curTreeTok st.mem + curOffCnt * drainUnit) := by
      cases ch with
      | delete e => exact wireTreeSyncDelete_step_runs ctx hinv
      | insert e => exact wireTreeSyncInsert_step_runs ctx hinv
    obtain ⟨mid, cStep, t1, tok1, h1, off1, rStep, hinv1, hcStep⟩ := hstep
    obtain ⟨out, cRest, t2, tok2, h2, off2, rRest, hinv2, hcRest⟩ := ih hinv1
    refine ⟨out, cStep + cRest + 2, t2, tok2, h2, off2,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨rest.length + 1, mid, cStep, cRest,
        by simp [Expr.eval, h18], Nat.succ_ne_zero _, rStep, rRest, by simp [Expr.size]; omega⟩)),
      hinv2, ?_⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end MinCostFlow.MinRatio
