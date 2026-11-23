module

public import MinCostFlow.MinRatio.WireTreeSync
import MinCostFlow.LinkCut.PathProg.Implements
import WordRAM.Tactic

/-!
# Shared path-tree synchronization: deletion step (`WireTreeSyncDelete`)

Verifies the deletion branch (`wireTreeSyncDelete_step_runs`) of `wireTreeSyncStep`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

private theorem lctExpose_n (s : PathTreeState) (x : ℕ) :
    (lctExpose pathPayload s x).n = s.n := rfl

/-- Execute one deletion iteration of `wireTreeSyncStep`. -/
theorem wireTreeSyncDelete_step_runs {w L drainUnit : ℕ} {cfg : Alg2Config}
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
      done (.delete e :: rem) curTree curTreeTok curHeap curOffCnt st) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    ∃ st' cost curTree' curTreeTok' curHeap' curOffCnt',
      Runs w p ω (wireTreeSyncStep (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
        st .normal st' cost ∧
      WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
        (done ++ [.delete e]) rem curTree' curTreeTok' curHeap' curOffCnt' st' ∧
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
  have hw1 : 1 < 2 ^ w := by have := ctx.hw11; omega
  have hw2 : 2 < 2 ^ w := by have := ctx.hw11; omega
  have hw3 : 3 < 2 ^ w := by have := ctx.hw11; omega
  have hw4 : 4 < 2 ^ w := by have := ctx.hw11; omega
  have hL4 : 2 + 4 * L < 2 ^ w := by unfold wireTreeSyncEditSpace at hHeapRoom; omega
  have hLW : L < 2 ^ w := by omega
  have htagLt {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap0 := ctx.tags.1 a (ht ▸ hv)
  have htagLtCur {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < curHeap :=
    lt_of_lt_of_le (htagLt ht hv) hHeapLo
  have hTreeFootLt : ∀ a, Rtree.foot tok.treeHeap curTreeTok a → a < curHeap := by
    intro a ha; rcases hTreeFoot a ha with h0 | ⟨_, hhi⟩
    · exact htagLtCur (ctx.tags.2.2.2.2.2.2.2.2.2.1 a h0) (by decide)
    · exact hhi
  have heSdiff : e ∈ oldF.E \ newF.E :=
    ctx.diff.delete_mem_sdiff (happ ▸ List.mem_append_right _ List.mem_cons_self)
  have heOld : e ∈ oldF.E := (Finset.mem_sdiff.mp heSdiff).1
  have heNotNew : e ∉ newF.E := (Finset.mem_sdiff.mp heSdiff).2
  have heG : e ∈ G0.E := ctx.oldSub heOld
  have heCap : e < tok.intCap := ctx.capE e heG
  have heCur : e ∈ applyTreeChanges oldF.E done := ctx.diff.delete_live happ.symm
  have hcurSubG0 := wireSync_curE_sub_G0 ctx.diff happ ctx.oldSub ctx.newSub
  have hsetEq : applyTreeChanges oldF.E (done ++ [.delete e]) =
      (applyTreeChanges oldF.E done).erase e := by
    unfold applyTreeChanges; rw [List.foldl_append]; rfl
  let s1 := { st with regs := Function.update st.regs 7 0 }
  let s2 := { s1 with regs := Function.update s1.regs 8 e }
  let s3 := { s2 with regs := Function.update s2.regs 12 (G0.tail e + 1) }
  let s4 := { s3 with regs := Function.update s3.regs 13 (G0.head e + 1) }
  let slot := st.mem (tok.slots + e)
  obtain ⟨hslotAct, hslotIs, hslotNm⟩ := hNamed.forward e heCur
  have hslotW : slot < 2 ^ w := by unfold isEdgeSlot at hslotIs; have := ctx.nW; omega
  have hslotsE_lt : tok.slots + e < curHeap := htagLtCur (ctx.tags.2.2.1 e heCap) (by decide)
  have hrecE_lt : tok.edgeRecords + e < curHeap := htagLtCur (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide)
  have hroot11_lt : root + 11 < curHeap := htagLtCur (ctx.tags.2.1 11 (by omega)) (by decide)
  have hinOffE_lt : tok.inOffReady + e < curHeap := htagLtCur (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (by decide)
  have hcurFits : pathTreeFits 4 L curTree := hNum.fits hLct (by rw [hTreeN]; exact ctx.capT)
  have h2B_lt_cap : 2 * B < (Num.capacity 4 L : ℤ) := by
    have hB0 := hNum.1; have hR0 := hNum.2.1; have hcap := ctx.capT
    rw [mul_assoc] at hcap
    have h1 : B + R ≤ ((2 * G0.n + 1 : ℕ) : ℤ) * (B + R) :=
      le_mul_of_one_le_left (add_nonneg hB0 hR0) (by omega)
    omega
  have hBudgetLe := pathTreeBudget_le_of_log (n := curTree.n) (hTreeN ▸ ctx.logW)
  -- D1-D2: `reg 17 := curHeap`, `reg 15 := slots[e]`
  let d1 := { s4 with regs := Function.update s4.regs 17 curHeap }
  let d2 := { d1 with regs := Function.update d1.regs 15 slot }
  have rd1 : Runs w p ω (.assign 17 (.reg 3)) s4 .normal d1 2 :=
    runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, s4, s3, s2, s1, hr3], rfl, rfl, rfl⟩
  have rd2 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 19) (.reg 8)))) d1 .normal d2 5 :=
    runs_assign_iff.mpr ⟨slot, by
      simp [Expr.eval, BinOp.eval, d1, s4, s3, s2, s1, hr19, show tok.slots + e < 2 ^ w by omega, slot],
      rfl, rfl, rfl⟩
  -- D3: `opTree 4` (`readTree`) on `[tok.treeHeap, slot, curHeap]`
  obtain ⟨t0, ht0, hslotT0⟩ := List.mem_flatMap.mp hslotAct
  obtain ⟨expTrees, hLctExp, hNumExp⟩ := pathTreeNumericInv_expose hLct hNum ht0 hslotT0
  have hexpFits : pathTreeFits 4 L (lctExpose pathPayload curTree slot) :=
    hNumExp.fits hLctExp (by rw [lctExpose_n, hTreeN]; exact ctx.capT)
  have hpre4 : (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)).pre
      4 curTree [tok.treeHeap, slot, curHeap] st.mem :=
    ⟨⟨_, _, _, hLct⟩, ctx.fmtBits.symm ▸ hcurFits, hTreeN.symm ▸ ctx.nW,
      ctx.fmtBits.symm ▸ hTreeN.symm ▸ ctx.logW, tok.treeHeap, slot, curHeap, rfl,
      ⟨_, _, _, hLct, hslotAct⟩, ctx.fmtBits.symm ▸ hexpFits⟩
  have hroom4 : curHeap + (pathTreeMachineContract fmt L LinkCut.PathProg.pathC
      (LinkCut.PathProg.pathAlloc L)).space 4 curTree [tok.treeHeap, slot, curHeap] st.mem < 2 ^ w := by
    change curHeap + LinkCut.PathProg.pathAlloc L 4 curTree.n [tok.treeHeap, slot, curHeap] < 2 ^ w
    simp only [LinkCut.PathProg.pathAlloc, show (4 : ℕ) ≠ 7 by decide, ↓reduceIte]
    unfold wireTreeSyncEditSpace at hHeapRoom; omega
  obtain ⟨b4, hb4, o4, out4, c4, hr4, expSt, tok1, hRep1, hPost4, hResp4, hc4⟩ :=
    ctx.treeImpl.2.2 4 tok.treeHeap curTree curTreeTok [tok.treeHeap, slot, curHeap] st.mem d2.pos ω
      (by simp [ctx.treeHeapLt, hslotW, hHeapW]) rfl hTreeRep hpre4 hTreeFootLt hz hroom4
  obtain ⟨hExpEq, hExpEdge⟩ := hPost4
  change expSt = lctExpose pathPayload curTree slot at hExpEq; subst hExpEq
  have hExpEdge4 : PathEdgeAt out4.mem curHeap 4 L ((lctExpose pathPayload curTree slot).splay.nodes slot).val := by
    simpa [ctx.fmtBits, heapArg] using hExpEdge
  obtain ⟨val, hValEq, hValCases, _⟩ := (hLive e heCur).expose_value hLct
  rw [hValEq] at hExpEdge4
  have hCanonValEq : canonPathEdgeValue val = canonVal e := by
    rcases hValCases with rfl | rfl
    · exact canonPathEdgeValue_eq_self_of_forward (ctx.canonProp e heG).1
    · rw [canonPathEdgeValue_reverse]; exact canonPathEdgeValue_eq_self_of_forward (ctx.canonProp e heG).1
  have hValBd : |val.gradient| ≤ B ∧ |val.flow| ≤ B := by
    obtain ⟨_, hgB, _, hfB, _⟩ := ctx.canonProp e heG
    rcases hValCases with rfl | rfl
    · exact ⟨hgB, hfB⟩
    · simpa [PathEdgeValue.reverse] using ⟨hgB, hfB⟩
  let h1 := o4.value
  have hh1Lo : curHeap ≤ h1 := hResp4.1
  have hh1Hi : h1 ≤ curHeap + (20 * LinkCut.PathProg.treeLimbs L + 100) := by
    have := hResp4.2.1; change h1 ≤ curHeap + LinkCut.PathProg.pathAlloc L 4 curTree.n [tok.treeHeap, slot, curHeap] at this
    simpa [LinkCut.PathProg.pathAlloc] using this
  have hResp4_foot : ∀ a, Rtree.foot tok.treeHeap tok1 a →
      Rtree.foot tok.treeHeap curTreeTok a ∨ (curHeap ≤ a ∧ a < h1) := hResp4.2.2.2.2
  have hResp4_frame : ∀ a < curHeap, ¬ Rtree.foot tok.treeHeap curTreeTok a →
      out4.mem a = st.mem a := hResp4.2.2.2.1
  let d3 : State := { regs := Function.update d2.regs 3 h1, mem := out4.mem, pos := out4.pos }
  have rd3 : Runs w p ω (.call 3 (opTree 4) [.reg 0, .reg 15, .reg 17]) d2 .normal d3 (c4 + 4) :=
    runs_call_iff.mpr ⟨[tok.treeHeap, slot, curHeap], b4, o4, out4, c4, by
      simp [evalArgs, Expr.eval, d2, d1, s4, s3, s2, s1, hr0], hb4, hr4, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hFoot1Lt : ∀ a, Rtree.foot tok.treeHeap tok1 a → a < h1 := by
    intro a ha; rcases hResp4_foot a ha with h0 | ⟨_, hhi⟩
    · exact (hTreeFootLt a h0).trans_le hh1Lo
    · exact hhi
  -- D4-D6: `dst := h1 + (2 + 4*L)`, `workHeap := dst + (2 + 4*L)`, call `canonCopy`
  let dst := h1 + (2 + 4 * L)
  let workHeap := dst + (2 + 4 * L)
  have hworkRoom : workHeap + 2 * L < 2 ^ w := by unfold wireTreeSyncEditSpace at hHeapRoom; omega
  let d4 := { d3 with regs := Function.update d3.regs 14 dst }
  let d5 := { d4 with regs := Function.update d4.regs 15 workHeap }
  have rd4 : Runs w p ω (.assign 14 (.bin .add (.reg 3) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 2)))))
      d3 .normal d4 8 :=
    runs_assign_iff.mpr ⟨dst, by
      simp [Expr.eval, BinOp.eval, d3, d2, d1, s4, s3, s2, s1, hr2, hw2, hw4,
        show 4 * L < 2 ^ w by omega, hL4, show dst < 2 ^ w by omega, dst], rfl, rfl, rfl⟩
  have rd5 : Runs w p ω (.assign 15 (.bin .add (.reg 14) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 2)))))
      d4 .normal d5 8 :=
    runs_assign_iff.mpr ⟨workHeap, by
      simp [Expr.eval, BinOp.eval, d4, d3, d2, d1, s4, s3, s2, s1, hr2, hw2, hw4,
        show 4 * L < 2 ^ w by omega, hL4, show workHeap < 2 ^ w by omega, workHeap], rfl, rfl, rfl⟩
  have hpreCC : (wireCanonCopyContract w val).pre [curHeap, dst, L, workHeap] out4.mem :=
    ⟨curHeap, dst, L, workHeap, rfl, hw4, Or.inr (by omega), by omega, le_rfl, hworkRoom,
      hExpEdge4, wire_fits_of_two_mul_abs_lt (by rw [abs_neg]; linarith [hValBd.1]),
      wire_fits_of_two_mul_abs_lt (by rw [abs_neg]; linarith [hValBd.2]),
      fun a ha => hResp4.2.2.1 a (by omega)⟩
  obtain ⟨d6, cCC, h2, rd6, hpCC, hr6CC, hd6Regs, hcCC⟩ :=
    runs_call_of_meetsContract (r := 3) (args := [.reg 17, .reg 14, .reg 2, .reg 15])
      (ctx.canonOk val) (st := d5) (vs := [curHeap, dst, L, workHeap])
      (by simp [evalArgs, Expr.eval, d5, d4, d3, d2, d1, s4, s3, s2, s1, hr2])
      (by simp [hHeapW, show dst < 2 ^ w by omega, hLW, show workHeap < 2 ^ w by omega])
      hpreCC ω
  obtain ⟨_, _, _, _, hargsCC, hh2Lo, hh2Hi, hDstEdge, hz2, hFrCC⟩ := hpCC
  simp only [List.cons.injEq, and_true] at hargsCC
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargsCC
  rw [hCanonValEq] at hDstEdge
  have hccBound : cCC ≤ 160 * L + 286 := by
    have hsz : argsSize [.reg 17, .reg 14, .reg 2, .reg 15] = 4 := rfl
    have hcs : (wireCanonCopyContract w val).cost [curHeap, dst, L, workHeap] d5.mem = 160 * L + 280 := rfl
    rw [hsz, hcs] at hcCC
    exact Nat.le_trans hcCC (by omega)
  -- D7-D8: store `edgeRecords[e] := dst`, `slots[e] := 0`
  let m2a := Function.update d6.mem (tok.edgeRecords + e) dst
  let m2b := Function.update m2a (tok.slots + e) 0
  let d7 := { d6 with mem := m2a }
  let d8 := { d7 with mem := m2b }
  have hrecEW : tok.edgeRecords + e < 2 ^ w := by omega
  have hslotsEW : tok.slots + e < 2 ^ w := by omega
  have rd7 : Runs w p ω (.store (.bin .add (.reg 22) (.reg 8)) (.reg 14)) d6 .normal d7 5 :=
    runs_store_iff.mpr ⟨tok.edgeRecords + e, dst, by
      simp [Expr.eval, BinOp.eval, hd6Regs 22 (by decide), hd6Regs 8 (by decide), d5, d4, d3, d2,
        d1, s4, s3, s2, s1, hr22, hrecEW],
      by simp [Expr.eval, hd6Regs 14 (by decide), d5, d4], rfl, rfl, rfl⟩
  have rd8 : Runs w p ω (.store (.bin .add (.reg 19) (.reg 8)) (.const 0)) d7 .normal d8 5 :=
    runs_store_iff.mpr ⟨tok.slots + e, 0, by
      simp [Expr.eval, BinOp.eval, d7, hd6Regs 19 (by decide), hd6Regs 8 (by decide), d5, d4, d3, d2,
        d1, s4, s3, s2, s1, hr19, hslotsEW],
      by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hm2b_foot : ∀ a, Rtree.foot tok.treeHeap tok1 a → out4.mem a = m2b a := by
    intro a ha
    have hlt1 := hFoot1Lt a ha
    have hne9 : a ≠ tok.slots + e := by
      intro heq; subst heq; rcases hResp4_foot _ ha with h0 | ⟨hlo, _⟩
      · have h16 := ctx.tags.2.2.2.2.2.2.2.2.2.1 _ (hTreeFoot _ h0 |>.elim id (fun h => by
          have := htagLt (ctx.tags.2.2.1 e heCap) (by decide); omega))
        rw [ctx.tags.2.2.1 e heCap] at h16; omega
      · exact Nat.not_lt_of_ge hlo hslotsE_lt
    have hne13 : a ≠ tok.edgeRecords + e := by
      intro heq; subst heq; rcases hResp4_foot _ ha with h0 | ⟨hlo, _⟩
      · have h16 := ctx.tags.2.2.2.2.2.2.2.2.2.1 _ (hTreeFoot _ h0 |>.elim id (fun h => by
          have := htagLt (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide); omega))
        rw [ctx.tags.2.2.2.2.2.2.1 e heCap] at h16; omega
      · exact Nat.not_lt_of_ge hlo hrecE_lt
    symm; dsimp only [m2b, m2a]
    rw [Function.update_of_ne hne9, Function.update_of_ne hne13]
    exact hFrCC a (by omega) (Or.inl (by omega))
  obtain ⟨hRep1_iff, hPhi1_eq⟩ := ctx.treeImpl.1 tok.treeHeap _ tok1 out4.mem m2b hm2b_foot
  have hRep1_m2b := hRep1_iff hRep1
  -- D9: `opTree 1` (`cutTree`) on `[tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2]`
  have hneCur : ∀ f ∈ applyTreeChanges oldF.E done, G0.tail f ≠ G0.head f := fun f hf =>
    named_account_endpoints_ne
      (G := { V := G0.V, E := applyTreeChanges oldF.E done, tail := G0.tail, head := G0.head })
      hLct hNamed hf (hTreeN.symm ▸ (ctx.vtxE f (hcurSubG0 hf)).1)
  have hvCur : ∀ f ∈ applyTreeChanges oldF.E done, G0.tail f < curTree.n ∧ G0.head f < curTree.n :=
    fun f hf => hTreeN.symm ▸ ctx.vtxE f (hcurSubG0 hf)
  obtain ⟨cutTrees, cutDepth, hLctCut, hNamedCut, hLiveCut⟩ :=
    hLive.cut_exposed hNamed hLct hvCur hneCur heCur
  have hNamedExp := treeEditNamedSlots_expose_witness hNamed hLct hslotAct hLctExp
  have huV : isVertex (lctExpose pathPayload curTree slot).n (vid (G0.tail e)) := by
    rw [lctExpose_n]; unfold isVertex vid; have := (ctx.vtxE e heG).1; omega
  have hvV : isVertex (lctExpose pathPayload curTree slot).n (vid (G0.head e)) := by
    rw [lctExpose_n]; unfold isVertex vid; have := (ctx.vtxE e heG).2; omega
  have huvNe : vid (G0.tail e) ≠ vid (G0.head e) := fun h => hneCur e heCur (Nat.add_right_cancel h)
  obtain ⟨edgeCut, cutTrees', cutDepth', hLctCut', hNumCut'⟩ :=
    pathTreeNumericInv_cut hLctExp hNumExp huV hvV huvNe
      ⟨slot, (hNamedExp.forward e heCur).1, (hNamedExp.endpoints e heCur).symm⟩
  have hEdgeCutEq : edgeCut = slot :=
    hLctCut'.freeListInv.2.1.symm.trans hLctCut.freeListInv.2.1
  subst hEdgeCutEq
  have hNumCut : PathTreeNumericInv (lctCut pathPayload (lctExpose pathPayload curTree slot)
      (G0.tail e + 1) (G0.head e + 1)) cutTrees B R := hNumCut'.relabel hLctCut' hLctCut
  have hCutN : (lctCut pathPayload (lctExpose pathPayload curTree slot)
      (G0.tail e + 1) (G0.head e + 1)).n = G0.n := (treeEditCut_n _ _ _).trans hTreeN
  have hCutFits : pathTreeFits 4 L (lctCut pathPayload (lctExpose pathPayload curTree slot)
      (G0.tail e + 1) (G0.head e + 1)) := hNumCut.fits hLctCut (by rw [hCutN]; exact ctx.capT)
  have hpre1 : (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)).pre
      1 (lctExpose pathPayload curTree slot)
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2] m2b :=
    ⟨⟨_, _, _, hLctExp⟩, ctx.fmtBits.symm ▸ hexpFits,
      by rw [lctExpose_n, hTreeN]; exact ctx.nW,
      by rw [lctExpose_n, ctx.fmtBits, hTreeN]; exact ctx.logW,
      tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2, rfl, huV, hvV, ctx.fmtBits.symm ▸ hCutFits⟩
  have hz2b : ZeroFrom m2b h2 := fun a ha => by
    dsimp only [m2b, m2a]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz2 a ha
  have hroom1 : h2 + (pathTreeMachineContract fmt L LinkCut.PathProg.pathC
      (LinkCut.PathProg.pathAlloc L)).space 1 (lctExpose pathPayload curTree slot)
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2] m2b < 2 ^ w := by
    change h2 + LinkCut.PathProg.pathAlloc L 1 (lctExpose pathPayload curTree slot).n
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2] < 2 ^ w
    simp only [LinkCut.PathProg.pathAlloc, show (1 : ℕ) ≠ 7 by decide, ↓reduceIte]
    unfold wireTreeSyncEditSpace at hHeapRoom; omega
  have hu1W : G0.tail e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).1; have := ctx.nW; omega
  have hv1W : G0.head e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).2; have := ctx.nW; omega
  obtain ⟨b1, hb1, o1, out1, c1, hr1_op, cutSt, tok2, hRep2, hPost1, hResp1, hc1⟩ :=
    ctx.treeImpl.2.2 1 tok.treeHeap (lctExpose pathPayload curTree slot) tok1
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2] m2b d8.pos ω
      (by simp [ctx.treeHeapLt, hu1W, hv1W, show h2 < 2 ^ w by omega]) rfl
      hRep1_m2b hpre1 (fun a ha => lt_of_lt_of_le (hFoot1Lt a ha) (by change h1 ≤ h2; omega)) hz2b hroom1
  change cutSt = lctCut pathPayload (lctExpose pathPayload curTree slot) (G0.tail e + 1) (G0.head e + 1) at hPost1
  subst hPost1
  let h3 := o1.value
  have hh3Lo : h2 ≤ h3 := hResp1.1
  have hh3Hi : h3 ≤ h2 + (20 * LinkCut.PathProg.treeLimbs L + 100) := by
    have := hResp1.2.1; change h3 ≤ h2 + LinkCut.PathProg.pathAlloc L 1 (lctExpose pathPayload curTree slot).n
      [tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2] at this
    simpa [LinkCut.PathProg.pathAlloc] using this
  have hResp1_foot : ∀ a, Rtree.foot tok.treeHeap tok2 a →
      Rtree.foot tok.treeHeap tok1 a ∨ (h2 ≤ a ∧ a < h3) := hResp1.2.2.2.2
  have hResp1_frame : ∀ a < h2, ¬ Rtree.foot tok.treeHeap tok1 a →
      out1.mem a = m2b a := hResp1.2.2.2.1
  let d9 : State := { regs := Function.update d8.regs 3 h3, mem := out1.mem, pos := out1.pos }
  have rd9 : Runs w p ω (.call 3 (opTree 1) [.reg 0, .reg 12, .reg 13, .reg 3]) d8 .normal d9 (c1 + 5) :=
    runs_call_iff.mpr ⟨[tok.treeHeap, G0.tail e + 1, G0.head e + 1, h2], b1, o1, out1, c1, by
      simp [evalArgs, Expr.eval, d8, d7, hr6CC, hd6Regs 0 (by decide), hd6Regs 12 (by decide),
        hd6Regs 13 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1, hr0],
      hb1, hr1_op, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have hDstEdge3 : PathEdgeAt out1.mem dst 4 L (some (canonVal e)) := by
    refine hDstEdge.congr fun a ha1 ha2 => ?_
    have hnot1 : ¬ Rtree.foot tok.treeHeap tok1 a := fun hft => by have := hFoot1Lt a hft; omega
    have h1eq := hResp1_frame a (by omega) hnot1
    have h2eq : m2b a = d6.mem a := by
      dsimp only [m2b, m2a]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h1eq.trans h2eq
  -- D10: `isNeg [dst + 2 + 3 * L, L]`
  obtain ⟨d10, cNeg, negRet, rd10, hpNeg, hr10Neg, hd10Regs, hcNeg⟩ :=
    runs_call_of_meetsContract (r := 15)
      (args := [.bin .add (.bin .add (.reg 14) (.const 2)) (.bin .mul (.const 3) (.reg 2)), .reg 2])
      ctx.isNegOk (st := d9) (vs := [dst + 2 + 3 * L, L])
      (by simp [evalArgs, Expr.eval, BinOp.eval, d9, d8, d7, hd6Regs 14 (by decide),
        hd6Regs 2 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1, hr2, hw2, hw3,
        show dst + 2 < 2 ^ w by omega, show 3 * L < 2 ^ w by omega, show dst + 2 + 3 * L < 2 ^ w by omega])
      (by simp [show dst + 2 + 3 * L < 2 ^ w by omega, hLW])
      ⟨dst + 2 + 3 * L, L, rfl, by omega, hDstEdge3.2.2.2.2.2.1⟩ ω
  obtain ⟨hmem10, hnegVal⟩ := hpNeg
  change negRet = if Num.intVal out1.mem (dst + 2 + 3 * L) 4 L < 0 then 1 else 0 at hnegVal
  rw [hDstEdge3.2.2.2.2.2.2] at hnegVal
  have hnegBound : cNeg ≤ 22 := by
    simp only [Num.isNegativeContract, argsSize, Expr.size] at hcNeg
    exact Nat.le_trans hcNeg (by norm_num)
  have hout1_eq_m2b (a : ℕ) (hlt : a < h2) (hnf : ¬ Rtree.foot tok.treeHeap tok1 a) :
      out1.mem a = m2b a := hResp1_frame a hlt hnf
  have hm2a_eq_st (a : ℕ) (hlt : a < curHeap) (hne13 : a ≠ tok.edgeRecords + e)
      (hne9 : a ≠ tok.slots + e) (hnf0 : ¬ Rtree.foot tok.treeHeap curTreeTok a) :
      m2b a = st.mem a := by
    dsimp only [m2b, m2a]
    rw [Function.update_of_ne hne9, Function.update_of_ne hne13, hFrCC a (by omega) (Or.inl (by omega)),
      hResp4_frame a hlt hnf0]
  have hout1_eq_st (a : ℕ) (hlt : a < curHeap) (hne13 : a ≠ tok.edgeRecords + e)
      (hne9 : a ≠ tok.slots + e) (hnf0 : ¬ Rtree.foot tok.treeHeap curTreeTok a) :
      out1.mem a = st.mem a := by
    have hnf1 : ¬ Rtree.foot tok.treeHeap tok1 a := fun hft => by
      rcases hResp4_foot a hft with h0 | ⟨hlo, _⟩; exact hnf0 h0; omega
    exact (hout1_eq_m2b a (by omega) hnf1).trans (hm2a_eq_st a hlt hne13 hne9 hnf0)
  have hnotF0 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) :
      ¬ Rtree.foot tok.treeHeap curTreeTok a := by
    intro hft; rcases hTreeFoot a hft with h0 | ⟨hlo, _⟩
    · have h16 := ctx.tags.2.2.2.2.2.2.2.2.2.1 a h0; rw [ht] at h16; exact hv16 h16
    · exact Nat.not_lt_of_ge hlo (htagLt ht hv)
  have hnotF2 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) :
      ¬ Rtree.foot tok.treeHeap tok2 a := by
    intro hft; rcases hResp1_foot a hft with h1' | ⟨hlo, _⟩
    · rcases hResp4_foot a h1' with h0 | ⟨hlo, _⟩
      · exact hnotF0 ht hv hv16 h0
      · exact Nat.not_lt_of_ge hlo (htagLtCur ht hv)
    · have := htagLtCur ht hv; omega
  have hneTag {a b va vb : ℕ} (ha : tok.tag a = va) (hb : tok.tag b = vb) (hne : va ≠ vb) : a ≠ b :=
    fun h => hne (ha.symm.trans (h ▸ hb))
  -- D11: conditional push onto `offReadyList`
  have hPushStmt : ∃ d11 cPush curOffCnt',
      Runs w p ω
        (.cond (.reg 15) .nop
          (.cond (.load (.bin .add (.reg 26) (.reg 8))) .nop
            (.store (.bin .add (.reg 26) (.reg 8)) (.const 1) ;;
             .assign 16 (.load (.bin .add (.reg 1) (.const 11))) ;;
             .store (.bin .add (.reg 25) (.reg 16)) (.reg 8) ;;
             .store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1)))))
        d10 .normal d11 cPush ∧
      cPush ≤ 40 ∧
      (∀ r, r ≠ 16 → d11.regs r = d10.regs r) ∧
      d11.mem (root + 11) = curOffCnt' ∧
      (curOffCnt' = curOffCnt ∨ curOffCnt' = curOffCnt + 1) ∧
      OffReadyInv d11.mem curOffCnt' tok.offReadyList tok.inOffReady tok.intCap ∧
      (0 ≤ (canonVal e).detector → d11.mem (tok.inOffReady + e) = 1) ∧
      (∀ a, (curOffCnt' = curOffCnt + 1 →
        a ≠ tok.inOffReady + e ∧ a ≠ tok.offReadyList + curOffCnt ∧ a ≠ root + 11) →
        d11.mem a = out1.mem a) ∧
      (curOffCnt' = curOffCnt + 1 → curOffCnt < tok.intCap) := by
    have hoffInv3 : OffReadyInv out1.mem curOffCnt tok.offReadyList tok.inOffReady tok.intCap := by
      have hagreeL : ∀ j < tok.intCap, out1.mem (tok.offReadyList + j) = st.mem (tok.offReadyList + j) :=
        fun j hj => hout1_eq_st _ (htagLtCur (ctx.tags.2.2.2.2.2.2.2.1 j hj) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.1 e heCap) (by decide))
          (hnotF0 (ctx.tags.2.2.2.2.2.2.2.1 j hj) (by decide) (by decide))
      have hagreeI : ∀ j < tok.intCap, out1.mem (tok.inOffReady + j) = st.mem (tok.inOffReady + j) :=
        fun j hj => hout1_eq_st _ (htagLtCur (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.2.1 e heCap) (by decide))
          (hnotF0 (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (by decide) (by decide))
      obtain ⟨hc, h1', h2', h3', h4'⟩ := hOffInv
      refine ⟨hc, fun j hj => ?_, fun j1 hj1 j2 hj2 hne => ?_, fun k hk => ?_, fun k hk h1'' => ?_⟩
      · rw [hagreeL j (by omega)]; exact ⟨(h1' j hj).1, (hagreeI _ (h1' j hj).1).trans (h1' j hj).2⟩
      · rw [hagreeL j1 (by omega), hagreeL j2 (by omega)]; exact h2' j1 hj1 j2 hj2 hne
      · rw [hagreeI k hk]; exact h3' k hk
      · rw [hagreeI k hk] at h1''; obtain ⟨j, hj, hje⟩ := h4' k hk h1''
        exact ⟨j, hj, (hagreeL j (by omega)).trans hje⟩
    have hroot11_3 : out1.mem (root + 11) = curOffCnt :=
      (hout1_eq_st _ hroot11_lt
        (hneTag (ctx.tags.2.1 11 (by omega)) (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
        (hneTag (ctx.tags.2.1 11 (by omega)) (ctx.tags.2.2.1 e heCap) (by decide))
        (hnotF0 (ctx.tags.2.1 11 (by omega)) (by decide) (by decide))).trans hOffCntMem
    by_cases hneg : (canonVal e).detector < 0
    · have hnr : negRet = 1 := by simp [hnegVal, hneg]
      refine ⟨d10, 3, curOffCnt, runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, hr10Neg, hnr],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
        by simp [Expr.size]⟩, by omega, fun _ _ => rfl, hmem10.symm ▸ hroot11_3, Or.inl rfl,
        hmem10.symm ▸ hoffInv3, fun hge => (not_lt_of_ge hge hneg).elim,
        fun a _ => congrFun hmem10 a, fun h => by omega⟩
    · have hnr : negRet = 0 := by simp [hnegVal, hneg]
      have hinE_val : d10.mem (tok.inOffReady + e) = st.mem (tok.inOffReady + e) :=
        hmem10.symm ▸ (hout1_eq_st _ hinOffE_lt
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
          (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (ctx.tags.2.2.1 e heCap) (by decide))
          (hnotF0 (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (by decide) (by decide)))
      have hinOffEW : tok.inOffReady + e < 2 ^ w := by omega
      rcases hOffInv.2.2.2.1 e heCap with hst0 | hst1
      · have hin0 : d10.mem (tok.inOffReady + e) = 0 := hinE_val.trans hst0
        obtain ⟨hcntLt, hoffPush'⟩ := offReadyInv_push hoffInv3 heCap (hmem10 ▸ hin0)
          (fun j hj k hk => hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj)
            (ctx.tags.2.2.2.2.2.2.2.2.1 k hk) (by decide))
        have hcnt1W : curOffCnt + 1 < 2 ^ w := by
          have := htagLtCur (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt hcntLt) (by decide); omega
        have hlistW : tok.offReadyList + curOffCnt < 2 ^ w := by
          have := htagLtCur (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt hcntLt) (by decide); omega
        let p1 := { d10 with mem := Function.update d10.mem (tok.inOffReady + e) 1 }
        let p2 := { p1 with regs := Function.update p1.regs 16 curOffCnt }
        let p3 := { p2 with mem := Function.update p2.mem (tok.offReadyList + curOffCnt) e }
        let p4 := { p3 with mem := Function.update p3.mem (root + 11) (curOffCnt + 1) }
        have hp1_r11 : p1.mem (root + 11) = curOffCnt := by
          dsimp only [p1]; rw [Function.update_of_ne (hneTag (ctx.tags.2.1 11 (by omega))
            (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (by decide)), hmem10]; exact hroot11_3
        have hroot11W : root + 11 < 2 ^ w := by omega
        have rp1 : Runs w p ω (.store (.bin .add (.reg 26) (.reg 8)) (.const 1)) d10 .normal p1 5 :=
          runs_store_iff.mpr ⟨tok.inOffReady + e, 1, by
            simp [Expr.eval, BinOp.eval, hd10Regs 26 (by decide), hd10Regs 8 (by decide), d9, d8, d7,
              hd6Regs 26 (by decide), hd6Regs 8 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1,
              hr26, hinOffEW],
            by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
        have hp1_reg1 : p1.regs 1 = root := by
          change d10.regs 1 = root
          simp [hd10Regs 1 (by decide), d9, d8, d7, hd6Regs 1 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1, hr1]
        have rp2 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 1) (.const 11)))) p1 .normal p2 5 :=
          runs_assign_iff.mpr ⟨curOffCnt, by
            simp [Expr.eval, BinOp.eval, hp1_reg1, ctx.hw11, hroot11W, hp1_r11], rfl, rfl, rfl⟩
        have rp3 : Runs w p ω (.store (.bin .add (.reg 25) (.reg 16)) (.reg 8)) p2 .normal p3 5 :=
          runs_store_iff.mpr ⟨tok.offReadyList + curOffCnt, e, by
            simp [Expr.eval, BinOp.eval, p2, p1, hd10Regs 25 (by decide), d9, d8, d7,
              hd6Regs 25 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1, hr25, hlistW],
            by simp [Expr.eval, p2, p1, hd10Regs 8 (by decide), d9, d8, d7, hd6Regs 8 (by decide),
              d5, d4, d3, d2, d1, s4, s3, s2, s1], rfl, rfl, rfl⟩
        have rp4 : Runs w p ω (.store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1)))
            p3 .normal p4 7 :=
          runs_store_iff.mpr ⟨root + 11, curOffCnt + 1, by
            simp [Expr.eval, BinOp.eval, p3, p2, p1, hd10Regs 1 (by decide), d9, d8, d7,
              hd6Regs 1 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1, hr1, ctx.hw11,
              hroot11W],
            by simp [Expr.eval, BinOp.eval, p3, p2, hw1, hcnt1W], rfl, rfl, rfl⟩
        have rInner : Runs w p ω
            (.store (.bin .add (.reg 26) (.reg 8)) (.const 1) ;;
             .assign 16 (.load (.bin .add (.reg 1) (.const 11))) ;;
             .store (.bin .add (.reg 25) (.reg 16)) (.reg 8) ;;
             .store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1))) d10 .normal p4 25 :=
          runs_seq_iff.mpr (Or.inr ⟨p1, 5, 19, rp1,
            runs_seq_iff.mpr (Or.inr ⟨p2, 5, 13, rp2,
              runs_seq_iff.mpr (Or.inr ⟨p3, 5, 7, rp3, rp4, rfl⟩), rfl⟩), rfl⟩)
        have rCond2 : Runs w p ω
            (.cond (.load (.bin .add (.reg 26) (.reg 8))) .nop
              (.store (.bin .add (.reg 26) (.reg 8)) (.const 1) ;;
               .assign 16 (.load (.bin .add (.reg 1) (.const 11))) ;;
               .store (.bin .add (.reg 25) (.reg 16)) (.reg 8) ;;
               .store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1))))
            d10 .normal p4 30 :=
          runs_cond_iff.mpr ⟨0, 25, by
            simp [Expr.eval, BinOp.eval, hd10Regs 26 (by decide), hd10Regs 8 (by decide), d9, d8, d7,
              hd6Regs 26 (by decide), hd6Regs 8 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1,
              hr26, hinOffEW, hin0],
            by simp only [↓reduceIte]; exact rInner, by simp [Expr.size]⟩
        have rCond1 : Runs w p ω
            (.cond (.reg 15) .nop
              (.cond (.load (.bin .add (.reg 26) (.reg 8))) .nop
                (.store (.bin .add (.reg 26) (.reg 8)) (.const 1) ;;
                 .assign 16 (.load (.bin .add (.reg 1) (.const 11))) ;;
                 .store (.bin .add (.reg 25) (.reg 16)) (.reg 8) ;;
                 .store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1)))))
            d10 .normal p4 32 :=
          runs_cond_iff.mpr ⟨0, 30, by simp [Expr.eval, hr10Neg, hnr],
            by simp only [↓reduceIte]; exact rCond2, by simp [Expr.size]⟩
        have hp4_offInv : OffReadyInv p4.mem (curOffCnt + 1) tok.offReadyList tok.inOffReady tok.intCap := by
          have hEqL (j : ℕ) (hj : j < tok.intCap) : p4.mem (tok.offReadyList + j) = p3.mem (tok.offReadyList + j) :=
            Function.update_of_ne (hneTag (ctx.tags.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.1 11 (by omega)) (by decide)) _ _
          have hEqI (j : ℕ) (hj : j < tok.intCap) : p4.mem (tok.inOffReady + j) = p3.mem (tok.inOffReady + j) :=
            Function.update_of_ne (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 j hj) (ctx.tags.2.1 11 (by omega)) (by decide)) _ _
          have hp3_eq : p3.mem = Function.update (Function.update out1.mem (tok.inOffReady + e) 1)
              (tok.offReadyList + curOffCnt) e := by simp [p3, p2, p1, hmem10, d9]
          rw [hp3_eq] at hEqL hEqI
          obtain ⟨hc, h1', h2', h3', h4'⟩ := hoffPush'
          refine ⟨hc, fun j hj => ?_, fun j1 hj1 j2 hj2 hne => ?_, fun k hk => ?_, fun k hk h1'' => ?_⟩
          · rw [hEqL j (by omega)]; exact ⟨(h1' j hj).1, (hEqI _ (h1' j hj).1).trans (h1' j hj).2⟩
          · rw [hEqL j1 (by omega), hEqL j2 (by omega)]; exact h2' j1 hj1 j2 hj2 hne
          · rw [hEqI k hk]; exact h3' k hk
          · rw [hEqI k hk] at h1''; obtain ⟨j, hj, hje⟩ := h4' k hk h1''
            exact ⟨j, hj, (hEqL j (by omega)).trans hje⟩
        refine ⟨p4, 32, curOffCnt + 1, rCond1, by omega,
          fun r hr => by simp [p4, p3, p2, p1, Function.update_of_ne hr],
          by simp [p4], Or.inr rfl, hp4_offInv, fun _ => by
            dsimp only [p4, p3, p2, p1]
            rw [Function.update_of_ne (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (ctx.tags.2.1 11 (by omega)) (by decide)),
              Function.update_of_ne (hneTag (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt hcntLt) (by decide)),
              Function.update_self],
          fun a ha => by
            obtain ⟨ha1, ha2, ha3⟩ := ha rfl
            dsimp only [p4, p3, p2, p1]
            rw [Function.update_of_ne ha3, Function.update_of_ne ha2, Function.update_of_ne ha1, hmem10],
          fun _ => hcntLt⟩
      · have hin1 : d10.mem (tok.inOffReady + e) = 1 := hinE_val.trans hst1
        have rCond1 : Runs w p ω
            (.cond (.reg 15) .nop
              (.cond (.load (.bin .add (.reg 26) (.reg 8))) .nop
                (.store (.bin .add (.reg 26) (.reg 8)) (.const 1) ;;
                 .assign 16 (.load (.bin .add (.reg 1) (.const 11))) ;;
                 .store (.bin .add (.reg 25) (.reg 16)) (.reg 8) ;;
                 .store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1)))))
            d10 .normal d10 8 :=
          runs_cond_iff.mpr ⟨0, 6, by simp [Expr.eval, hr10Neg, hnr],
            by simp only [↓reduceIte]; exact runs_cond_iff.mpr ⟨1, 1, by
                simp [Expr.eval, BinOp.eval, hd10Regs 26 (by decide), hd10Regs 8 (by decide), d9, d8, d7,
                  hd6Regs 26 (by decide), hd6Regs 8 (by decide), d5, d4, d3, d2, d1, s4, s3, s2, s1,
                  hr26, hinOffEW, hin1],
                by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
                by simp [Expr.size]⟩,
            by simp [Expr.size]⟩
        exact ⟨d10, 8, curOffCnt, rCond1, by omega, fun _ _ => rfl, hmem10.symm ▸ hroot11_3,
          Or.inl rfl, hmem10.symm ▸ hoffInv3, fun _ => hin1, fun a _ => congrFun hmem10 a,
          fun h => by omega⟩
  obtain ⟨d11, cPush, curOffCnt', rd11, hcPush, hd11Regs, hd11Cnt, hCntCases, hd11OffInv,
    hd11InE, hd11Frame, hd11PushLt⟩ := hPushStmt
  have rDel : Runs w p ω (wireTreeSyncDelete (opTree 4) (opTree 1) canonCopy isNeg) s4 .normal d11
      (2 + (5 + ((c4 + 4) + (8 + (8 + (cCC + (5 + (5 + ((c1 + 5) + (cNeg + cPush + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨d1, 2, _, rd1,
    runs_seq_iff.mpr (Or.inr ⟨d2, 5, _, rd2,
    runs_seq_iff.mpr (Or.inr ⟨d3, c4 + 4, _, rd3,
    runs_seq_iff.mpr (Or.inr ⟨d4, 8, _, rd4,
    runs_seq_iff.mpr (Or.inr ⟨d5, 8, _, rd5,
    runs_seq_iff.mpr (Or.inr ⟨d6, cCC, _, rd6,
    runs_seq_iff.mpr (Or.inr ⟨d7, 5, _, rd7,
    runs_seq_iff.mpr (Or.inr ⟨d8, 5, _, rd8,
    runs_seq_iff.mpr (Or.inr ⟨d9, c1 + 5, _, rd9,
    runs_seq_iff.mpr (Or.inr ⟨d10, cNeg, cPush, rd10, rd11, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hd11_keep (r : ℕ) (hr3_ne : r ≠ 3) (h7 : r ≠ 7) (h8 : r ≠ 8) (h12 : r ≠ 12) (h13 : r ≠ 13)
      (h14 : r ≠ 14) (h15 : r ≠ 15) (h16 : r ≠ 16) (h17 : r ≠ 17) : d11.regs r = st.regs r := by
    rw [hd11Regs r h16, hd10Regs r h15]
    change (Function.update d8.regs 3 h3) r = st.regs r
    rw [Function.update_of_ne hr3_ne]; change d6.regs r = st.regs r
    rw [hd6Regs r hr3_ne]
    simp [d5, d4, d3, d2, d1, s4, s3, s2, s1, Function.update_of_ne, hr3_ne, h7, h8, h12, h13, h14, h15, h17]
  let out := { d11 with regs := Function.update (Function.update d11.regs 6
    (editPtr + 2 * (done.length + 1))) 18 rem.length }
  have rStep := wireSync_step_wrap ctx hinv0 (tagVal := 0) (e := e) rfl heG rDel
    ((hd11_keep 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr6)
    ((hd11_keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr18)
  have h11_eq_out1 (a : ℕ) (h15 : tok.tag a ≠ 15) (h14 : tok.tag a ≠ 14) (h1 : a ≠ root + 11) :
      d11.mem a = out1.mem a :=
    hd11Frame a fun hpush => ⟨fun h => h15 (h ▸ ctx.tags.2.2.2.2.2.2.2.2.1 e heCap),
      fun h => h14 (h ▸ ctx.tags.2.2.2.2.2.2.2.1 curOffCnt (hd11PushLt hpush)), h1⟩
  have h11_foot2 : ∀ a, Rtree.foot tok.treeHeap tok2 a → out1.mem a = d11.mem a := fun a ha => by
    symm; refine hd11Frame a fun hpush => ⟨?_, ?_, ?_⟩
    · intro h; exact hnotF2 (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (by decide) (by decide) (h ▸ ha)
    · intro h; exact hnotF2 (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt (hd11PushLt hpush)) (by decide) (by decide) (h ▸ ha)
    · intro h; exact hnotF2 (ctx.tags.2.1 11 (by omega)) (by decide) (by decide) (h ▸ ha)
  obtain ⟨hRep2_iff, hPhi2_eq⟩ := ctx.treeImpl.1 tok.treeHeap _ tok2 out1.mem d11.mem h11_foot2
  have hRep2_d11 := hRep2_iff hRep2
  have hSlotEq (ei : ℕ) (hei : ei ∈ (applyTreeChanges oldF.E done).erase e) :
      d11.mem (tok.slots + ei) = st.mem (tok.slots + ei) := by
    have heiG : ei ∈ G0.E := hcurSubG0 (Finset.mem_erase.mp hei).2
    have hne : ei ≠ e := (Finset.mem_erase.mp hei).1
    have ht9 := ctx.tags.2.2.1 ei (ctx.capE ei heiG)
    exact (h11_eq_out1 _ (by rw [ht9]; decide) (by rw [ht9]; decide)
      (hneTag ht9 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
      (hout1_eq_st _ (htagLtCur ht9 (by decide))
        (hneTag ht9 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide)) (by omega)
        (hnotF0 ht9 (by decide) (by decide)))
  have hNameEq (sl : ℕ) (his : isEdgeSlot (lctCut pathPayload (lctExpose pathPayload curTree slot)
      (G0.tail e + 1) (G0.head e + 1)).n sl) :
      d11.mem (tok.names + sl) = st.mem (tok.names + sl) := by
    have hslLt : sl < 2 * G0.n := by unfold isEdgeSlot at his; omega
    have ht10 := ctx.tags.2.2.2.1 sl hslLt
    exact (h11_eq_out1 _ (by rw [ht10]; decide) (by rw [ht10]; decide)
      (hneTag ht10 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
      (hout1_eq_st _ (htagLtCur ht10 (by decide))
        (hneTag ht10 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
        (hneTag ht10 (ctx.tags.2.2.1 e heCap) (by decide))
        (hnotF0 ht10 (by decide) (by decide)))
  have hRecEq_e : d11.mem (tok.edgeRecords + e) = dst := by
    have ht13 := ctx.tags.2.2.2.2.2.2.1 e heCap
    have h1 := h11_eq_out1 _ (by rw [ht13]; decide) (by rw [ht13]; decide)
      (hneTag ht13 (ctx.tags.2.1 11 (by omega)) (by decide))
    have hnf1 : ¬ Rtree.foot tok.treeHeap tok1 (tok.edgeRecords + e) := fun hft => by
      rcases hResp4_foot _ hft with h0 | ⟨hlo, _⟩
      · exact hnotF0 ht13 (by decide) (by decide) h0
      · exact Nat.not_lt_of_ge hlo hrecE_lt
    rw [h1, hout1_eq_m2b _ (by omega) hnf1]
    dsimp only [m2b, m2a]
    rw [Function.update_of_ne (hneTag ht13 (ctx.tags.2.2.1 e heCap) (by decide)), Function.update_self]
  have hRecEq_ne (ei : ℕ) (heiG : ei ∈ G0.E) (hne : ei ≠ e) :
      d11.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) := by
    have ht13 := ctx.tags.2.2.2.2.2.2.1 ei (ctx.capE ei heiG)
    exact (h11_eq_out1 _ (by rw [ht13]; decide) (by rw [ht13]; decide)
      (hneTag ht13 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
      (hout1_eq_st _ (htagLtCur ht13 (by decide)) (by omega)
        (hneTag ht13 (ctx.tags.2.2.1 e heCap) (by decide))
        (hnotF0 ht13 (by decide) (by decide)))
  refine ⟨out, _, lctCut pathPayload (lctExpose pathPayload curTree slot)
      (G0.tail e + 1) (G0.head e + 1), tok2, h3, curOffCnt', rStep, ?_, ?_⟩
  · refine ⟨by simpa [List.append_assoc] using happ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, ?_, ?_, ?_, ?_, hCutN,
      ⟨cutTrees, slot :: curFree, cutDepth, hLctCut, hNumCut,
        by rw [hsetEq]; exact namedSlots_congr_slot hNamedCut hSlotEq (fun sl _ his => hNameEq sl his),
        by rw [hsetEq]; exact liveAccounts_congr_slot hLiveCut hSlotEq⟩,
      hRep2_d11, ?_, ?_, ?_, ?_, ?_, ?_, hd11Cnt, hd11OffInv⟩
    · simp [out, hd11_keep 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0]
    · simp [out, hd11_keep 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1]
    · simp [out, hd11_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr2]
    · simp [out, hd11Regs 3 (by decide), hd10Regs 3 (by decide), d9]
    · simp [out, List.length_append]
    · simp [out]
    · simp [out, hd11_keep 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr9]
    · simp [out, hd11_keep 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr10]
    · simp [out, hd11_keep 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr11]
    · simp [out, hd11_keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr19]
    · simp [out, hd11_keep 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20]
    · simp [out, hd11_keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22]
    · simp [out, hd11_keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr23]
    · simp [out, hd11_keep 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr24]
    · simp [out, hd11_keep 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr25]
    · simp [out, hd11_keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr26]
    · rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
      have hstepLe : h3 ≤ curHeap + wireTreeSyncEditSpace L := by unfold wireTreeSyncEditSpace; omega
      omega
    · intro a ha
      exact (hd11Frame a fun hpush => ⟨by have := hinOffE_lt; omega,
        by have := htagLtCur (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt (hd11PushLt hpush)) (by decide); omega,
        by omega⟩).trans (hResp1.2.2.1 a ha)
    · intro a ha
      rcases hResp1_foot a ha with h1' | ⟨hlo, hhi⟩
      · rcases hResp4_foot a h1' with h0' | ⟨hlo, hhi⟩
        · rcases hTreeFoot a h0' with hbase | ⟨hlo, hhi⟩
          · exact Or.inl hbase
          · exact Or.inr ⟨hlo, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, hhi⟩
    · intro a ha hne11 h9 h10 h11 h13 h14 h15 h16
      have hnf0 : ¬ Rtree.foot tok.treeHeap curTreeTok a := fun hft => by
        rcases hTreeFoot a hft with h0 | ⟨hlo, _⟩
        · exact h16 (ctx.tags.2.2.2.2.2.2.2.2.2.1 a h0)
        · omega
      exact (h11_eq_out1 a h15 h14 hne11).trans
        ((hout1_eq_st a (by omega)
          (fun h => h13 (h ▸ ctx.tags.2.2.2.2.2.2.1 e heCap))
          (fun h => h9 (h ▸ ctx.tags.2.2.1 e heCap)) hnf0).trans
          (hFrame a ha hne11 h9 h10 h11 h13 h14 h15 h16))
    · intro ei hei; rw [hsetEq] at hei
      have heiCur := (Finset.mem_erase.mp hei).2
      rw [hSlotEq ei hei]
      have hslLt : st.mem (tok.slots + ei) < 2 * G0.n := by
        have := (hNamed.forward ei heiCur).2.1; unfold isEdgeSlot at this; omega
      have ht11 := ctx.tags.2.2.2.2.1 _ hslLt
      have ht12 := ctx.tags.2.2.2.2.2.1 ei (ctx.capE ei (hcurSubG0 heiCur))
      have hL1 := (h11_eq_out1 _ (by rw [ht11]; decide) (by rw [ht11]; decide)
        (hneTag ht11 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
        (hout1_eq_st _ (htagLtCur ht11 (by decide))
          (hneTag ht11 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
          (hneTag ht11 (ctx.tags.2.2.1 e heCap) (by decide)) (hnotF0 ht11 (by decide) (by decide)))
      have hR1 := (h11_eq_out1 _ (by rw [ht12]; decide) (by rw [ht12]; decide)
        (hneTag ht12 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
        (hout1_eq_st _ (htagLtCur ht12 (by decide))
          (hneTag ht12 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
          (hneTag ht12 (ctx.tags.2.2.1 e heCap) (by decide)) (hnotF0 ht12 (by decide) (by decide)))
      rw [hL1, hR1]; exact hSlotThr ei heiCur
    · intro ei heiG hnot; rw [hsetEq] at hnot
      have ht9 := ctx.tags.2.2.1 ei (ctx.capE ei heiG)
      by_cases heq : ei = e
      · subst heq
        have hnf1 : ¬ Rtree.foot tok.treeHeap tok1 (tok.slots + ei) := fun hft => by
          rcases hResp4_foot _ hft with h0 | ⟨hlo, _⟩
          · exact hnotF0 ht9 (by decide) (by decide) h0
          · exact Nat.not_lt_of_ge hlo hslotsE_lt
        rw [h11_eq_out1 _ (by rw [ht9]; decide) (by rw [ht9]; decide)
          (hneTag ht9 (ctx.tags.2.1 11 (by omega)) (by decide)), hout1_eq_m2b _ (by omega) hnf1]
        simp [m2b]
      · have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_erase.mpr ⟨heq, hm⟩)
        exact (h11_eq_out1 _ (by rw [ht9]; decide) (by rw [ht9]; decide)
          (hneTag ht9 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
          ((hout1_eq_st _ (htagLtCur ht9 (by decide))
            (hneTag ht9 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide)) (by omega)
            (hnotF0 ht9 (by decide) (by decide))).trans (hOffSlot0 ei heiG hnot'))
    · intro ei heiG hnot; rw [hsetEq] at hnot
      by_cases heq : ei = e
      · subst heq; rw [hRecEq_e]
        exact hDstEdge3.congr fun a ha1 ha2 =>
          hd11Frame a fun hpush => ⟨by have := hinOffE_lt; omega,
            by have := htagLtCur (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt (hd11PushLt hpush)) (by decide); omega,
            by omega⟩
      · have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_erase.mpr ⟨heq, hm⟩)
        rw [hRecEq_ne ei heiG heq]
        refine (hOffRec ei heiG hnot').congr fun a ha1 ha2 => ?_
        by_cases hOld : ei ∈ oldF.E
        · obtain ⟨hlo, hhi, hnf⟩ := (hOffWhere ei heiG hnot').1 hOld
          exact (hd11Frame a fun hpush => ⟨by have := htagLt (ctx.tags.2.2.2.2.2.2.2.2.1 e heCap) (by decide); omega,
            by have := htagLt (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt (hd11PushLt hpush)) (by decide); omega,
            by have := htagLt (ctx.tags.2.1 11 (by omega)) (by decide); omega⟩).trans
            (hout1_eq_st a (by omega)
              (by have := htagLt (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide); omega)
              (by have := htagLt (ctx.tags.2.2.1 e heCap) (by decide); omega)
              (hnf a ha1 (by omega)))
        · have hrecEq := (hOffWhere ei heiG hnot').2 hOld
          have ht18 := ctx.tags.2.2.2.2.2.2.2.2.2.2.1 ei heiG hOld (a - st.mem (tok.edgeRecords + ei)) (by omega)
          have hsub : memStart (tok.edgeRecords + ei) + (a - st.mem (tok.edgeRecords + ei)) = a := by omega
          rw [hsub] at ht18
          exact (h11_eq_out1 a (by rw [ht18]; decide) (by rw [ht18]; decide)
            (hneTag ht18 (ctx.tags.2.1 11 (by omega)) (by decide))).trans
            (hout1_eq_st a (htagLtCur ht18 (by decide))
              (hneTag ht18 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
              (hneTag ht18 (ctx.tags.2.2.1 e heCap) (by decide)) (hnotF0 ht18 (by decide) (by decide)))
    · intro ei heiG hnot hdet; rw [hsetEq] at hnot
      by_cases heq : ei = e
      · subst heq; exact hd11InE hdet
      · have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_erase.mpr ⟨heq, hm⟩)
        have ht15 := ctx.tags.2.2.2.2.2.2.2.2.1 ei (ctx.capE ei heiG)
        exact (hd11Frame _ fun hpush => ⟨by omega,
          hneTag ht15 (ctx.tags.2.2.2.2.2.2.2.1 curOffCnt (hd11PushLt hpush)) (by decide),
          hneTag ht15 (ctx.tags.2.1 11 (by omega)) (by decide)⟩).trans
          ((hout1_eq_st _ (htagLtCur ht15 (by decide))
            (hneTag ht15 (ctx.tags.2.2.2.2.2.2.1 e heCap) (by decide))
            (hneTag ht15 (ctx.tags.2.2.1 e heCap) (by decide)) (hnotF0 ht15 (by decide) (by decide))).trans
            (hOffPush ei heiG hnot' hdet))
    · intro ei heiG hnot; rw [hsetEq] at hnot
      by_cases heq : ei = e
      · subst heq; rw [hRecEq_e]
        refine ⟨fun _ => ⟨by omega, by omega, fun a ha1 ha2 hft => ?_⟩, fun hno => (hno heOld).elim⟩
        rcases hResp1_foot a hft with h1' | ⟨hlo, _⟩
        · have := hFoot1Lt a h1'; omega
        · omega
      · have hnot' : ei ∉ applyTreeChanges oldF.E done := fun hm => hnot (Finset.mem_erase.mpr ⟨heq, hm⟩)
        rw [hRecEq_ne ei heiG heq]
        refine ⟨fun hOld => ?_, (hOffWhere ei heiG hnot').2⟩
        obtain ⟨hlo, hhi, hnf⟩ := (hOffWhere ei heiG hnot').1 hOld
        refine ⟨hlo, by omega, fun a ha1 ha2 hft => ?_⟩
        rcases hResp1_foot a hft with h1' | ⟨hlo2, _⟩
        · rcases hResp4_foot a h1' with h0' | ⟨hlo1, _⟩
          · exact hnf a ha1 ha2 h0'
          · omega
        · omega
    · intro e1 he1 e2 he2 hne hnot1 hnot2; rw [hsetEq] at hnot1 hnot2
      have hRecBound (f : ℕ) (hfG : f ∈ G0.E) (hfnot : f ∉ applyTreeChanges oldF.E done) :
          st.mem (tok.edgeRecords + f) + (2 + 4 * L) ≤ curHeap := by
        by_cases hOld : f ∈ oldF.E
        · exact ((hOffWhere f hfG hfnot).1 hOld).2.1
        · have hrecEq := (hOffWhere f hfG hfnot).2 hOld
          have ht18 := ctx.tags.2.2.2.2.2.2.2.2.2.2.1 f hfG hOld (2 + 4 * L - 1) (by omega)
          have := htagLtCur ht18 (by decide); omega
      by_cases h1e : e1 = e
      · subst h1e; have hnot2' : e2 ∉ applyTreeChanges oldF.E done := fun hm => hnot2 (Finset.mem_erase.mpr ⟨hne.symm, hm⟩)
        rw [hRecEq_e, hRecEq_ne e2 he2 hne.symm]
        exact Or.inr (by have := hRecBound e2 he2 hnot2'; omega)
      · by_cases h2e : e2 = e
        · subst h2e; have hnot1' : e1 ∉ applyTreeChanges oldF.E done := fun hm => hnot1 (Finset.mem_erase.mpr ⟨h1e, hm⟩)
          rw [hRecEq_e, hRecEq_ne e1 he1 h1e]
          exact Or.inl (by have := hRecBound e1 he1 hnot1'; omega)
        · have hnot1' : e1 ∉ applyTreeChanges oldF.E done := fun hm => hnot1 (Finset.mem_erase.mpr ⟨h1e, hm⟩)
          have hnot2' : e2 ∉ applyTreeChanges oldF.E done := fun hm => hnot2 (Finset.mem_erase.mpr ⟨h2e, hm⟩)
          rw [hRecEq_ne e1 he1 h1e, hRecEq_ne e2 he2 h2e]
          exact hOffDisj e1 he1 e2 he2 hne hnot1' hnot2'
  · change _ + (Rtree.phi tok.treeHeap tok2 d11.mem + curOffCnt' * drainUnit) ≤ _
    rw [← hPhi2_eq]
    have hBudLe : pathTreeBudget LinkCut.PathProg.pathC L curTree.n ≤
        25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) :=
      pathTreeBudget_le_of_log (hTreeN.symm ▸ ctx.logW)
    have hc4' : c4 + Rtree.phi tok.treeHeap tok1 out4.mem ≤
        25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + Rtree.phi tok.treeHeap curTreeTok st.mem :=
      le_trans hc4 (Nat.add_le_add_right hBudLe _)
    have hc1' : c1 + Rtree.phi tok.treeHeap tok2 out1.mem ≤
        25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + Rtree.phi tok.treeHeap tok1 m2b := by
      have h1 := hc1
      change c1 + Rtree.phi tok.treeHeap tok2 out1.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC L (lctExpose pathPayload curTree slot).n +
          Rtree.phi tok.treeHeap tok1 m2b at h1
      rw [lctExpose_n] at h1
      exact le_trans h1 (Nat.add_le_add_right hBudLe _)
    rw [← hPhi1_eq] at hc1'
    have hcntMul : curOffCnt' * drainUnit ≤ curOffCnt * drainUnit + drainUnit := by
      rcases hCntCases with rfl | rfl
      · omega
      · rw [Nat.add_mul, Nat.one_mul]
    unfold wireTreeSyncEditCost
    linarith [hc4', hc1', hccBound, hnegBound, hcPush, hcntMul]

end MinCostFlow.MinRatio
