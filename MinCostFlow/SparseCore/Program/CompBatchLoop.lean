module

public import MinCostFlow.SparseCore.Program.CompBatchLoopBase
import WordRAM.Tactic

/-!
# Batch-Update Main Loop Verification (`CompBatchLoop`)

Proves `compBatchLoop_runs`: running `compBatchLoopStmt bIns bDel bSplit` sequentially on an
encoded batch `U` advances `S` to `compLSFBatchFamily S U`, records touched components, cut logs,
and split vertices, maintains `CompLSFRepDirty`, and bounds amortized cost + potential change.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The 3-way dispatch statement inside `compBatchLoopStmt`. -/
def compBatchDispStmt (bIns bDel bSplit : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 13) (.const 0))
    (.call 11 bIns [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
    (.cond (.bin .eq (.reg 13) (.const 1))
      (.call 11 bDel [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
      (.call 11 bSplit [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9, .bin .add (.reg 8) (.reg 12)] ;;
       .assign 12 (.bin .add (.reg 12) (.const 1))))

set_option maxHeartbeats 1200000 in
open Classical in
/-- Single-update dispatch step inside `compBatchLoopStmt`. -/
lemma compBatchLoopStep_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bErase bApp bMark bDisp bIns bDel bSplit
      uPtr heap cntBase splitBase updBuf nSp uLen : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {touched : List ℕ} {cnts : Fin k → ℕ}
    {u : Update} {st : State}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpCons : p.procs[bCons]? = some ghostConsProc)
    (hpErase : p.procs[bErase]? = some ghostEraseProc)
    (hpApp : p.procs[bApp]? = some ghostAppendProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hpIns : p.procs[bIns]? = some (compStepInsertProc bCons bMark bDisp))
    (hpDel : p.procs[bDel]? = some (compStepDeleteProc bErase bMark bDisp))
    (hpSplit : p.procs[bSplit]? = some (compStepSplitProc bApp bMark bDisp))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched st.mem)
    (hnd : touched.Nodup) (hlt : ∀ c ∈ touched, c < x.numComps)
    (hu_at : UpdateAt st.mem uPtr (S ⟨0, hrep.1⟩).G u uLen)
    (hu_mem_ag : ∀ i < uLen, st.mem (uPtr + i) = mem0 (uPtr + i))
    (hu_words : ∀ i < uLen, st.mem (uPtr + i) < 2 ^ w)
    (hu_out : ∀ i < uLen, (uPtr + i < b ∨ x.endAddr ≤ uPtr + i) ∧ uPtr + i < heap)
    (huLen_eq : dgUpdateMemLen mem0 uPtr = uLen)
    (huLen_ge2 : 2 ≤ uLen)
    (hu_val : (S ⟨0, hrep.1⟩).G.UpdateIsValid u)
    (hCaps1 : UpdateWithinCaps x.vCap x.eCap u)
    (hr0 : st.regs 0 = b) (hr2 : st.regs 2 = heap) (hr7 : st.regs 7 = cntBase)
    (hr8 : st.regs 8 = splitBase) (hr9 : st.regs 9 = updBuf)
    (hr11 : st.regs 11 = uPtr) (hr12 : st.regs 12 = nSp)
    (hend_h : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_sp : cntBase + k + 2 * (k * x.vCap) ≤ splitBase)
    (hsp_buf : splitBase + nSp + 1 ≤ updBuf)
    (hbuf_w : updBuf + 5 + uLen + 2 * x.eCap < 2 ^ w)
    (hu_w : uPtr + uLen < 2 ^ w)
    (hz : ZeroFrom st.mem updBuf)
    (hhp : st.mem heap = touched.length) (hls : ListAt st.mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, st.mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card) :
    let cs0 := S ⟨0, hrep.1⟩
    let S1 : CompLSFFamily k := fun j => compLSFStepSingle (S j) u
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    let stTag : State := { st with regs := Function.update st.regs 13 (st.mem uPtr) }
    ∃ st1 cStep, ∃ (x1 : CompLSFMeta k) (touched1 : List ℕ)
        (cuts1 : Fin k → List (ℕ × ℕ)) (sp1 : List ℕ),
      Runs w p ω (compBatchDispStmt bIns bDel bSplit) stTag .normal st1 cStep ∧
      (∀ r < 11, st1.regs r = st.regs r) ∧
      st1.regs 11 = uPtr + uLen ∧
      st1.regs 12 = nSp + sp1.length ∧
      sp1.length ≤ 1 ∧
      sp1 = (match (generalizing := false) u with | .split _ v' _ _ => [v'] | _ => []) ∧
      x1.vCap = x.vCap ∧ x1.eCap = x.eCap ∧ x1.L_w = x.L_w ∧
      x1.numComps = x.numComps ∧ x1.numEdgeful = x.numEdgeful ∧
      x1.m0Total = x.m0Total ∧ x1.endAddr = x.endAddr ∧ HEq x1.compOf x.compOf ∧
      CompLSFRepDirty W k b S1 x1 touched1 st1.mem ∧
      touched1.Nodup ∧ (∀ c ∈ touched1, c < x.numComps) ∧
      touched1.length ≤ touched.length + 2 ∧
      touched.length ≤ touched1.length ∧
      st1.mem heap = touched1.length ∧
      ListAt st1.mem (heap + 1) touched1 ∧
      (∀ i (hi : i < sp1.length), st1.mem (splitBase + (nSp + i)) = sp1[i]) ∧
      (∀ j : Fin k,
        st1.mem (cntBase + j.1) = cnts j + (cuts1 j).length ∧
        (∀ i (hi : i < (cuts1 j).length),
          st1.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts1 j)[i].2 ∧
          st1.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts1 j)[i].1) ∧
        cnts j + (cuts1 j).length ≤ (S1 j).RF.R.card) ∧
      (∀ (cuts2 : Fin k → List (ℕ × ℕ)) (sp2 : List ℕ) (S2 : CompLSFFamily k),
        (∀ j : Fin k,
          CompForestCutsValid x.vCap (S1 j).RF (cuts2 j) ∧
          ((cuts2 j).map Prod.fst).Nodup ∧
          ((cuts2 j).map Prod.fst).toFinset = (S1 j).RF.F.E \ (S2 j).RF.F.E ∧
          (S2 j).RF.F.E ⊆ (S1 j).RF.F.E ∧
          ((cuts2 j).map Prod.snd).Nodup ∧
          sp2.Nodup ∧
          (∀ r ∈ (cuts2 j).map Prod.snd, r ∉ sp2) ∧
          ((cuts2 j).map Prod.snd).toFinset ∪ sp2.toFinset = (S2 j).RF.R \ (S1 j).RF.R ∧
          (S1 j).RF.R ⊆ (S2 j).RF.R) →
        ∀ j : Fin k,
          let cuts := cuts1 j ++ cuts2 j
          let sp := sp1 ++ sp2
          CompForestCutsValid x.vCap (S j).RF cuts ∧
          (cuts.map Prod.fst).Nodup ∧
          (cuts.map Prod.fst).toFinset = (S j).RF.F.E \ (S2 j).RF.F.E ∧
          (S2 j).RF.F.E ⊆ (S j).RF.F.E ∧
          (cuts.map Prod.snd).Nodup ∧
          sp.Nodup ∧
          (∀ r ∈ cuts.map Prod.snd, r ∉ sp) ∧
          (cuts.map Prod.snd).toFinset ∪ sp.toFinset = (S2 j).RF.R \ (S j).RF.R ∧
          (S j).RF.R ⊆ (S2 j).RF.R) ∧
      (∀ a,
        (a < b ∨ x.endAddr ≤ a) →
        a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + touched.length + 2 ≤ a) →
        (a < splitBase + nSp ∨ splitBase + nSp + sp1.length ≤ a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts1 j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts1 j).length ≤ a) →
        a < updBuf → st1.mem a = st.mem a) ∧
      ZeroFrom st1.mem updBuf ∧
      cStep + 120 * (∑ j : Fin k, (cuts1 j).length) + compPhi b x1 st1.mem ≤
        compPhi b x st.mem + 630 +
          k * ((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
            lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
            lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) := by
  intro cs0 S1 rootsBase fDelBase stTag
  set tag := st.mem uPtr
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  cases u with
  | insert e a bVert =>
    rcases hu_at with ⟨rfl, hLA⟩
    have hu_in : st.mem uPtr = 0 ∧ st.mem (uPtr + 1) = e ∧ st.mem (uPtr + 2) = a ∧ st.mem (uPtr + 3) = bVert :=
      ⟨by simpa using hLA 0 (by simp), by simpa using hLA 1 (by simp),
       by simpa using hLA 2 (by simp), by simpa using hLA 3 (by simp)⟩
    have htag0 : tag = 0 := hu_in.1
    obtain ⟨stI, cI, x1, touched1, cuts1, hrunI, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep1, hnd1, hlt1, hlen1, hlen_ge1, hhp1, hls1, hbr1, hfr1, hz1, hcost1⟩ :=
      compStepInsert_runs (pos := stTag.pos) (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hpCons hpMark hpDisp
        hw16 hrep hnd hlt hu_in hu_val hCaps1 hend_h (by omega) (by omega) (by omega) hu_w
        hz hhp hls hcnts_m hcnts_le
    let st1 : State := { stTag with regs := Function.update stTag.regs 11 (uPtr + 4), mem := stI.mem, pos := stI.pos }
    have hcall : Runs w p ω (.call 11 bIns [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
        stTag .normal st1 (cI + 6) :=
      runs_call_iff.mpr ⟨[b, uPtr, heap, cntBase, updBuf], _, .returned (uPtr + 4), stI, cI,
        by simp [evalArgs, Expr.eval, stTag, hr0, hr11, hr2, hr7, hr9], hpIns, hrunI, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    have hcond : Runs w p ω (compBatchDispStmt bIns bDel bSplit) stTag .normal st1 (cI + 10) := by
      unfold compBatchDispStmt
      exact runs_cond_iff.mpr ⟨1, cI + 6, by simp [Expr.eval, BinOp.eval, stTag, hu_in.1, hw0', hw1],
        by simpa using hcall, by simp [Expr.size]; omega⟩
    have ht_le : touched.length ≤ touched1.length := by
      rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup hnd1]
      exact Finset.card_le_card fun c hc =>
        List.mem_toFinset.mpr ((hlen_ge1 ⟨c, hlt c (List.mem_toFinset.mp hc)⟩).mpr (Or.inl (List.mem_toFinset.mp hc)))
    refine ⟨st1, cI + 10, x1, touched1, cuts1, [], hcond,
      fun r hr => by simp [st1, stTag, show r ≠ 11 by omega, show r ≠ 13 by omega],
      by simp [st1], by simp [st1, stTag, hr12], Nat.zero_le _, rfl,
      hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hrep1, hnd1, hlt1, hlen1, ht_le, hhp1, hls1,
      fun _ hi => by simp at hi,
      fun j => ⟨(hbr1 j).1, (hbr1 j).2.1, (hbr1 j).2.2.2.2.2.2.2.2.2⟩,
      fun cuts2 sp2 S2 h2 j => by
        obtain ⟨_, _, hval1, hndE1, hsE1, hEsub1, hndR1, hsR1, hRsub1, _⟩ := hbr1 j
        obtain ⟨hval2, hndE2, hsE2, hEsub2, hndR2, hndS2, hdisj2, hsR2, hRsub2⟩ := h2 j
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr⟩, _⟩ := hrep
        have hV_ends := compLSFStepSingle_ins_RF_V_ends (hBr j).1 ((hBr j).2.2.1.symm ▸ hu_val)
        exact compBatchStep_cuts_combine_nonSplit hV_ends.1 (fun f hf => hV_ends.2 f hf hEsub1)
          hval1 hndE1 hsE1 hEsub1 hndR1 hsR1 hRsub1 hval2 hndE2 hsE2 hEsub2 hndR2 hndS2 hdisj2 hsR2 hRsub2,
      fun z h1 h2 h3 _ h5 h6 h7 h8 => hfr1 z h1 h2 h3 h5 h6 h7 h8, hz1,
      by dsimp only [st1, cs0, projUpdWords] at hcost1 ⊢; omega⟩
  | delete e =>
    rcases hu_at with ⟨rfl, hLA⟩
    have hu_in : st.mem uPtr = 1 ∧ st.mem (uPtr + 1) = e :=
      ⟨by simpa using hLA 0 (by simp), by simpa using hLA 1 (by simp)⟩
    obtain ⟨stD, cD, x1, touched1, cuts1, hrunD, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep1, hnd1, hlt1, hlen1, hlen_ge1, hhp1, hls1, hbr1, hfr1, hz1, hcost1⟩ :=
      compStepDelete_runs (pos := stTag.pos) (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hpErase hpMark hpDisp
        hw16 hrep hnd hlt hu_in hu_val hend_h (by omega) (by omega) (by omega) hu_w
        hz hhp hls hcnts_m hcnts_le
    let st1 : State := { stTag with regs := Function.update stTag.regs 11 (uPtr + 2), mem := stD.mem, pos := stD.pos }
    have hcall : Runs w p ω (.call 11 bDel [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
        stTag .normal st1 (cD + 6) :=
      runs_call_iff.mpr ⟨[b, uPtr, heap, cntBase, updBuf], _, .returned (uPtr + 2), stD, cD,
        by simp [evalArgs, Expr.eval, stTag, hr0, hr11, hr2, hr7, hr9], hpDel, hrunD, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    have hcond2 : Runs w p ω
        (.cond (.bin .eq (.reg 13) (.const 1))
          (.call 11 bDel [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
          (.call 11 bSplit [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9, .bin .add (.reg 8) (.reg 12)] ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)))) stTag .normal st1 (cD + 10) :=
      runs_cond_iff.mpr ⟨1, cD + 6, by simp [Expr.eval, BinOp.eval, stTag, hu_in.1, hw1],
        by simpa using hcall, by simp [Expr.size]; omega⟩
    have hcond : Runs w p ω (compBatchDispStmt bIns bDel bSplit) stTag .normal st1 (cD + 14) := by
      unfold compBatchDispStmt
      exact runs_cond_iff.mpr ⟨0, cD + 10, by simp [Expr.eval, BinOp.eval, stTag, hu_in.1, hw0'],
        by simpa using hcond2, by simp [Expr.size]; omega⟩
    have ht_le : touched.length ≤ touched1.length := by
      rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup hnd1]
      exact Finset.card_le_card fun c hc =>
        List.mem_toFinset.mpr ((hlen_ge1 ⟨c, hlt c (List.mem_toFinset.mp hc)⟩).mpr (Or.inl (List.mem_toFinset.mp hc)))
    refine ⟨st1, cD + 14, x1, touched1, cuts1, [], hcond,
      fun r hr => by simp [st1, stTag, show r ≠ 11 by omega, show r ≠ 13 by omega],
      by simp [st1], by simp [st1, stTag, hr12], Nat.zero_le _, rfl,
      hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hrep1, hnd1, hlt1, hlen1, ht_le, hhp1, hls1,
      fun _ hi => by simp at hi,
      fun j => ⟨(hbr1 j).1, (hbr1 j).2.1, (hbr1 j).2.2.2.2.2.2.2.2.2⟩,
      fun cuts2 sp2 S2 h2 j => by
        obtain ⟨_, _, hval1, hndE1, hsE1, hEsub1, hndR1, hsR1, hRsub1, _⟩ := hbr1 j
        obtain ⟨hval2, hndE2, hsE2, hEsub2, hndR2, hndS2, hdisj2, hsR2, hRsub2⟩ := h2 j
        have hVd : (S1 j).RF.F.V = (S j).RF.F.V := by
          simp only [S1, CompLSFState.RF, compLSFStepSingle, MGraph.applyUpdate]
        have hendsd : ∀ f ∈ (S1 j).RF.F.E,
            (S1 j).RF.F.tail f = (S j).RF.F.tail f ∧ (S1 j).RF.F.head f = (S j).RF.F.head f := fun _ _ => by
          simp only [S1, CompLSFState.RF, compLSFStepSingle, MGraph.applyUpdate, and_self]
        exact compBatchStep_cuts_combine_nonSplit hVd hendsd
          hval1 hndE1 hsE1 hEsub1 hndR1 hsR1 hRsub1 hval2 hndE2 hsE2 hEsub2 hndR2 hndS2 hdisj2 hsR2 hRsub2,
      fun z h1 h2 h3 _ h5 h6 h7 h8 => hfr1 z h1 h2 h3 h5 h6 h7 h8, hz1,
      by dsimp only [st1, cs0, projUpdWords] at hcost1 ⊢; omega⟩
  | split v v' St Sh =>
    have htag23 : st.mem uPtr = 2 ∨ st.mem uPtr = 3 := by
      rcases hu_at with ⟨_, _, _, _, _, _, _, hLA⟩ | ⟨_, _, _, _, _, _, _, hLA⟩
      · left; exact by simpa using hLA 0 (by simp)
      · right; exact by simpa using hLA 0 (by simp)
    obtain ⟨stS, cS, x1, touched1, cuts1, hrunS, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep1, hnd1, hlt1, hlen1, hlen_ge1, hhp1, hls1, hsp_m1, hbr1, hfr1, hz1, hcost1⟩ :=
      compStepSplit_runs (splitPtr := splitBase + nSp) (pos := stTag.pos) (ω := ω)
        hpZero hpLogAdd hpPreLog hpLsf hpApp hpMark hpDisp
        hw16 hrep hnd hlt hu_at hu_words hu_out hu_val hCaps1 hend_h (by omega) (by omega)
        (by omega) (by omega) hz hhp hls hcnts_m hcnts_le
    let stS1 : State := { stTag with regs := Function.update stTag.regs 11 (uPtr + uLen), mem := stS.mem, pos := stS.pos }
    let st1 : State := { stS1 with regs := Function.update stS1.regs 12 (nSp + 1) }
    have hcall : Runs w p ω (.call 11 bSplit [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9, .bin .add (.reg 8) (.reg 12)])
        stTag .normal stS1 (cS + 9) :=
      runs_call_iff.mpr ⟨[b, uPtr, heap, cntBase, updBuf, splitBase + nSp], _, .returned (uPtr + uLen), stS, cS,
        by simp [evalArgs, Expr.eval, BinOp.eval, stTag, hr0, hr11, hr2, hr7, hr8, hr9, hr12,
          show splitBase + nSp < 2 ^ w by omega], hpSplit, hrunS, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    have hinc : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1))) stS1 .normal st1 4 :=
      runs_assign_iff.mpr ⟨nSp + 1, by simp [Expr.eval, BinOp.eval, stS1, stTag, hr12, hw1,
        show nSp + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    have hseq : Runs w p ω
        (.call 11 bSplit [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9, .bin .add (.reg 8) (.reg 12)] ;;
         .assign 12 (.bin .add (.reg 12) (.const 1))) stTag .normal st1 (cS + 14) :=
      runs_seq_iff.mpr (Or.inr ⟨stS1, cS + 9, 4, hcall, hinc, rfl⟩)
    have hcond2 : Runs w p ω
        (.cond (.bin .eq (.reg 13) (.const 1))
          (.call 11 bDel [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
          (.call 11 bSplit [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9, .bin .add (.reg 8) (.reg 12)] ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)))) stTag .normal st1 (cS + 18) :=
      runs_cond_iff.mpr ⟨0, cS + 14, by simp [Expr.eval, BinOp.eval, stTag, hw1,
        show st.mem uPtr ≠ 1 by rcases htag23 with h | h <;> omega], by simpa using hseq, by simp [Expr.size]; omega⟩
    have hcond : Runs w p ω (compBatchDispStmt bIns bDel bSplit) stTag .normal st1 (cS + 22) := by
      unfold compBatchDispStmt
      exact runs_cond_iff.mpr ⟨0, cS + 18, by simp [Expr.eval, BinOp.eval, stTag, hw0',
        show st.mem uPtr ≠ 0 by rcases htag23 with h | h <;> omega], by simpa using hcond2, by simp [Expr.size]; omega⟩
    have ht_le : touched.length ≤ touched1.length := by
      rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup hnd1]
      exact Finset.card_le_card fun c hc =>
        List.mem_toFinset.mpr ((hlen_ge1 ⟨c, hlt c (List.mem_toFinset.mp hc)⟩).mpr (Or.inl (List.mem_toFinset.mp hc)))
    have hpw_eq : ∀ C, projUpdWords st.mem (S ⟨0, hrep.1⟩) C uPtr (.split v v' St Sh) =
        projUpdWords mem0 (S ⟨0, hrep.1⟩) C uPtr (.split v v' St Sh) := fun C => by
      have hl1 : dgUpdateMemLen st.mem uPtr = uLen := dgUpdateMemLen_eq hu_at
      simp only [projUpdWords, hl1, huLen_eq]
    simp only [hpw_eq] at hcost1
    refine ⟨st1, cS + 22, x1, touched1, cuts1, [v'], hcond,
      fun r hr => by simp [st1, stS1, stTag, show r ≠ 11 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega],
      by simp [st1, stS1], by simp [st1], le_refl 1, rfl,
      hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hrep1, hnd1, hlt1, hlen1, ht_le, hhp1, hls1,
      fun i hi => by
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0; simpa [st1, stS1] using hsp_m1,
      fun j => ⟨(hbr1 j).1, (hbr1 j).2.1, (hbr1 j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
      fun cuts2 sp2 S2 h2 j => by
        obtain ⟨_, _, h1, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, _⟩ := hbr1 j
        obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2 j
        exact compBatchStep_cuts_combine_split h1 h2' h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
          b1 b2 b3 b4 b5 b6 b7 b8 b9,
      fun z h1 h2 h3 hsp_ne h5 h6 h7 h8 => hfr1 z h1 h2 h3 (by simp at hsp_ne; omega) h5 h6 h7 h8, hz1,
      by dsimp only [st1, stS1, cs0]; omega⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compBatchLoopStmt`: processes every update in `U` sequentially from `uPtr`,
advancing `S` to `compLSFBatchFamily S U`, logging ordered cuts and split vertices into the
scratch buffers starting at `(cnts, nSp)`, and bounding cost + potential change. -/
theorem compBatchLoop_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bErase bApp bMark bDisp bIns bDel bSplit
      batchPtr heap numU cntBase splitBase updBuf totalWords : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpCons : p.procs[bCons]? = some ghostConsProc)
    (hpErase : p.procs[bErase]? = some ghostEraseProc)
    (hpApp : p.procs[bApp]? = some ghostAppendProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hpIns : p.procs[bIns]? = some (compStepInsertProc bCons bMark bDisp))
    (hpDel : p.procs[bDel]? = some (compStepDeleteProc bErase bMark bDisp))
    (hpSplit : p.procs[bSplit]? = some (compStepSplitProc bApp bMark bDisp))
    (hw16 : 16 ≤ 2 ^ w)
    (hbatch_words : ∀ i < totalWords, mem0 (batchPtr + i) < 2 ^ w)
    (hbatch_heap : batchPtr + totalWords ≤ heap) :
    ∀ (U : List Update) (idx uPtr nSp remWords : ℕ)
      (S : CompLSFFamily k) (x : CompLSFMeta k)
      (touched : List ℕ) (cnts : Fin k → ℕ) (st : State),
      idx + U.length = numU →
      batchPtr + 1 ≤ uPtr →
      uPtr + remWords ≤ batchPtr + totalWords →
      (∀ i < totalWords, batchPtr + i < b ∨ x.endAddr ≤ batchPtr + i) →
      (∀ i < totalWords, st.mem (batchPtr + i) = mem0 (batchPtr + i)) →
      (hrep : CompLSFRepDirty W k b S x touched st.mem) →
      touched.Nodup → (∀ c ∈ touched, c < x.numComps) →
      touched.length ≤ 2 * idx →
      nSp ≤ idx →
      st.regs 0 = b → st.regs 2 = heap → st.regs 6 = numU →
      st.regs 7 = cntBase → st.regs 8 = splitBase → st.regs 9 = updBuf →
      st.regs 10 = idx → st.regs 11 = uPtr → st.regs 12 = nSp →
      BatchBodyAt mem0 uPtr (S ⟨0, hrep.1⟩).G U remWords →
      (S ⟨0, hrep.1⟩).G.BatchIsValid U →
      BatchWithinCaps x.vCap x.eCap U →
      x.endAddr ≤ heap →
      heap + 1 + 2 * numU ≤ cntBase →
      cntBase + k + 2 * (k * x.vCap) ≤ splitBase →
      splitBase + numU ≤ updBuf →
      updBuf + 5 + totalWords + 2 * x.eCap < 2 ^ w →
      ZeroFrom st.mem updBuf →
      st.mem heap = touched.length →
      ListAt st.mem (heap + 1) touched →
      (∀ j : Fin k, st.mem (cntBase + j.1) = cnts j) →
      (∀ j : Fin k, cnts j ≤ (S j).RF.R.card) →
      let cs0 := S ⟨0, hrep.1⟩
      let S' := compLSFBatchFamily S U
      let rootsBase := cntBase + k
      let fDelBase := cntBase + k + k * x.vCap
      ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ)
          (cuts : Fin k → List (ℕ × ℕ)) (sp : List ℕ),
        Runs w p ω (compBatchLoopStmt bIns bDel bSplit) st .normal st' cost ∧
        (∀ r < 10, st'.regs r = st.regs r) ∧
        st'.regs 12 = nSp + sp.length ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
        x'.numComps = x.numComps ∧ x'.numEdgeful = x.numEdgeful ∧
        x'.m0Total = x.m0Total ∧ x'.endAddr = x.endAddr ∧ HEq x'.compOf x.compOf ∧
        CompLSFRepDirty W k b S' x' touched' st'.mem ∧
        touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
        touched'.length ≤ 2 * numU ∧
        sp.length ≤ U.length ∧
        st'.mem heap = touched'.length ∧
        ListAt st'.mem (heap + 1) touched' ∧
        (∀ i (hi : i < sp.length), st'.mem (splitBase + (nSp + i)) = sp[i]) ∧
        (∀ j : Fin k,
          st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
          (∀ i (hi : i < (cuts j).length),
            st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
            st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
          CompForestCutsValid x.vCap (S j).RF (cuts j) ∧
          ((cuts j).map Prod.fst).Nodup ∧
          ((cuts j).map Prod.fst).toFinset = (S j).RF.F.E \ (S' j).RF.F.E ∧
          (S' j).RF.F.E ⊆ (S j).RF.F.E ∧
          ((cuts j).map Prod.snd).Nodup ∧
          sp.Nodup ∧
          (∀ r ∈ (cuts j).map Prod.snd, r ∉ sp) ∧
          ((cuts j).map Prod.snd).toFinset ∪ sp.toFinset = (S' j).RF.R \ (S j).RF.R ∧
          (S j).RF.R ⊆ (S' j).RF.R) ∧
        (∀ a,
          (a < b ∨ x.endAddr ≤ a) →
          a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + 2 * numU ≤ a) →
          (a < splitBase + nSp ∨ splitBase + nSp + sp.length ≤ a) →
          (∀ j : Fin k, a ≠ cntBase + j.1) →
          (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
            rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
          (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
            fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
          a < updBuf → st'.mem a = st.mem a) ∧
        ZeroFrom st'.mem updBuf ∧
        cost + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' st'.mem ≤
          compPhi b x st.mem + 645 * U.length + 10 +
            k * compBatchStepsCost mem0 x.L_w cs0 uPtr U := by
  intro U
  induction U with
  | nil =>
    intro idx uPtr nSp remWords S x touched cnts st hidx _ _ _ _ hrep hnd hlt hlen_t _
      _ _ hr6 _ _ _ hr10 _ hr12 _ _ _ _ _ _ _ _ hz hhp hls hcnts_m _
    have hidx_eq : idx = numU := by simpa using hidx
    have hrun : Runs w p ω (compBatchLoopStmt bIns bDel bSplit) st .normal st 4 :=
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr10, hr6, hidx_eq], rfl, rfl,
        by simp [Expr.size]⟩)
    refine ⟨st, 4, x, touched, fun _ => [], [], hrun, fun _ _ => rfl, by simpa using hr12,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, hrep, hnd, hlt, by omega, Nat.zero_le _,
      hhp, hls, fun _ hi => by simp at hi,
      fun j => ⟨by simpa using hcnts_m j, fun _ hi => by simp at hi, trivial,
        List.nodup_nil, by simp [compLSFBatchFamily, compLSFBatch], Finset.Subset.rfl,
        List.nodup_nil, List.nodup_nil, fun _ h => by simp at h,
        by simp [compLSFBatchFamily, compLSFBatch], Finset.Subset.rfl⟩,
      fun _ _ _ _ _ _ _ _ _ => rfl, hz, by simp [compBatchStepsCost]; omega⟩
  | cons u us ih =>
    intro idx uPtr nSp remWords S x touched cnts st hidx hu_ge hu_le hout_b hag_b hrep hnd hlt
      hlen_t hnSp hr0 hr2 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hBody hVal hCaps hend_h hheap_cnt
      hcnt_sp hsp_buf hbuf_w hz hhp hls hcnts_m hcnts_le
    set cs0 := S ⟨0, hrep.1⟩
    set S1 : CompLSFFamily k := fun j => compLSFStepSingle (S j) u
    set S' := compLSFBatchFamily S (u :: us)
    have hS'_eq : S' = compLSFBatchFamily S1 us := by funext j; rfl
    set rootsBase := cntBase + k
    set fDelBase := cntBase + k + k * x.vCap
    have hidx_lt : idx < numU := by simp at hidx; omega
    have hw0 : w ≠ 0 := by intro h; subst h; omega
    have hw1 : 1 < 2 ^ w := by omega
    rcases hBody with ⟨uLen, rem2, hu_at0, hBody2⟩
    rcases hVal with ⟨hu_val, hVal2⟩
    have hCaps1 : UpdateWithinCaps x.vCap x.eCap u ∧ BatchWithinCaps x.vCap x.eCap us := by
      simpa [BatchWithinCaps] using hCaps
    have huLen_eq : dgUpdateMemLen mem0 uPtr = uLen := dgUpdateMemLen_eq hu_at0
    have huLen_ge2 : 2 ≤ uLen := updateAt_len_ge_two hu_at0
    have hu_mem_ag : ∀ i < uLen, st.mem (uPtr + i) = mem0 (uPtr + i) := fun i hi => by
      have h := hag_b (uPtr - batchPtr + i) (by omega)
      rwa [show batchPtr + (uPtr - batchPtr + i) = uPtr + i by omega] at h
    have hu_words : ∀ i < uLen, st.mem (uPtr + i) < 2 ^ w := fun i hi => by
      rw [hu_mem_ag i hi]
      have h := hbatch_words (uPtr - batchPtr + i) (by omega)
      rwa [show batchPtr + (uPtr - batchPtr + i) = uPtr + i by omega] at h
    have hu_out : ∀ i < uLen, (uPtr + i < b ∨ x.endAddr ≤ uPtr + i) ∧ uPtr + i < heap := fun i hi => by
      have h1 := hout_b (uPtr - batchPtr + i) (by omega)
      rw [show batchPtr + (uPtr - batchPtr + i) = uPtr + i by omega] at h1
      exact ⟨h1, by omega⟩
    have hu_at : UpdateAt st.mem uPtr cs0.G u uLen := by
      obtain ⟨l', hl'le, hu_at', hrem'⟩ :=
        compBatchBodyAt_of_agree (U := [u]) (tw := uLen) ⟨uLen, le_refl uLen, hu_at0, Nat.sub_self uLen⟩ hu_mem_ag
      have hl'eq : l' = uLen := by dsimp [BatchBodyAt] at hrem'; omega
      exact hl'eq ▸ hu_at'
    have hu_w : uPtr + uLen < 2 ^ w := by omega
    set tag := st.mem uPtr
    let stTag : State := { st with regs := Function.update st.regs 13 tag }
    have hrun_tag : Runs w p ω (.assign 13 (.load (.reg 11))) st .normal stTag 3 :=
      runs_assign_iff.mpr ⟨tag, by simp [Expr.eval, hr11, tag], rfl, rfl, by simp [Expr.size]⟩
    obtain ⟨st1, cStep, x1, touched1, cuts1, sp1, hrun_step, hr1_lt11, hr1_11, hr1_12, hsp1_le, _,
      hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hrep1, hnd1, hlt1, hlen1, hlen_ge1, hhp1, hls1, hsp1_m,
      hbr1, hcomb, hfr1, hz1, hcost1⟩ :=
      compBatchLoopStep_runs hpZero hpLogAdd hpPreLog hpLsf hpCons hpErase hpApp hpMark hpDisp
        hpIns hpDel hpSplit hw16 hrep hnd hlt hu_at hu_mem_ag hu_words hu_out huLen_eq huLen_ge2
        hu_val hCaps1.1 hr0 hr2 hr7 hr8 hr9 hr11 hr12 hend_h (by omega) hcnt_sp (by omega)
        (by omega) hu_w hz hhp hls hcnts_m hcnts_le
    let st2 : State := { st1 with regs := Function.update st1.regs 10 (idx + 1) }
    have hrun_inc : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) st1 .normal st2 4 :=
      runs_assign_iff.mpr ⟨idx + 1, by simp [Expr.eval, BinOp.eval, hr1_lt11 10 (by omega), hr10, hw1,
        show idx + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    have hrun_body : Runs w p ω
        (.assign 13 (.load (.reg 11)) ;;
         compBatchDispStmt bIns bDel bSplit ;;
         .assign 10 (.bin .add (.reg 10) (.const 1))) st .normal st2 (cStep + 9) :=
      runs_seq_iff.mpr (Or.inr ⟨stTag, 3, _, hrun_tag,
        runs_seq_iff.mpr (Or.inr ⟨st1, cStep, 4, hrun_step, hrun_inc, rfl⟩), by omega⟩)
    have hst2_batch : ∀ i < totalWords, st2.mem (batchPtr + i) = mem0 (batchPtr + i) := fun i hi => by
      have hout_i := hout_b i hi
      have hlt_h : batchPtr + i < heap := by omega
      exact (hfr1 (batchPtr + i) hout_i (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans (hag_b i hi)
    have hcnts1_le : ∀ j : Fin k, cnts j + (cuts1 j).length ≤ (S1 j).RF.R.card := fun j => (hbr1 j).2.2
    obtain ⟨st3, cRest, x2, touched2, cuts2, sp2, hrun_rest, hr3_lt10, hr3_12,
      hx2_1, hx2_2, hx2_3, hx2_4, hx2_5, hx2_6, hx2_7, hx2_8, hrep2, hnd2, hlt2, hlen2, hsp2_le,
      hhp2, hls2, hsp2_m, hbr2, hfr2, hz2, hcost2⟩ :=
      ih (idx + 1) (uPtr + uLen) (nSp + sp1.length) (remWords - uLen) S1 x1 touched1
        (fun j => cnts j + (cuts1 j).length) st2 (by simp at hidx; omega) (by omega) (by omega)
        (fun i hi => by rw [hx7]; exact hout_b i hi) hst2_batch hrep1 hnd1
        (fun c hc => hx4.symm ▸ hlt1 c hc) (by omega) (by omega)
        (by simp [st2, hr1_lt11 0 (by omega), hr0]) (by simp [st2, hr1_lt11 2 (by omega), hr2])
        (by simp [st2, hr1_lt11 6 (by omega), hr6]) (by simp [st2, hr1_lt11 7 (by omega), hr7])
        (by simp [st2, hr1_lt11 8 (by omega), hr8]) (by simp [st2, hr1_lt11 9 (by omega), hr9])
        (by simp [st2]) (by simp [st2, hr1_11]) (by simp [st2, hr1_12])
        hBody2 hVal2 (hx1.symm ▸ hx2.symm ▸ hCaps1.2)
        (hx7.symm ▸ hend_h) hheap_cnt (hx1.symm ▸ hcnt_sp) hsp_buf (hx2.symm ▸ hbuf_w)
        hz1 hhp1 hls1 (fun j => (hbr1 j).1) hcnts1_le
    have hrun_loop : Runs w p ω (compBatchLoopStmt bIns bDel bSplit) st .normal st3 (cStep + cRest + 13) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, cStep + 9, cRest,
        by simp [Expr.eval, BinOp.eval, hr10, hr6, hidx_lt, hw0], by decide,
        by simpa [compBatchDispStmt] using hrun_body, hrun_rest, by simp [Expr.size]; omega⟩))
    have hcap12 : ∀ j : Fin k, cnts j + (cuts1 j).length + (cuts2 j).length ≤ x.vCap := fun j => by
      obtain ⟨_, _, _, _, _, _, _, _, _, hsR2, hRsub2⟩ := hbr2 j
      have hcard_le : (cuts2 j).length ≤ ((compLSFBatchFamily S1 us j).RF.R \ (S1 j).RF.R).card := by
        have h1 : (cuts2 j).length = ((cuts2 j).map Prod.snd).toFinset.card := by
          rw [List.toFinset_card_of_nodup (hbr2 j).2.2.2.2.2.2.1, List.length_map]
        rw [h1, ← hsR2]; exact Finset.card_le_card Finset.subset_union_left
      have hcard_sdiff : ((compLSFBatchFamily S1 us j).RF.R \ (S1 j).RF.R).card + (S1 j).RF.R.card =
          (compLSFBatchFamily S1 us j).RF.R.card :=
        Finset.card_sdiff_add_card_eq_card hRsub2
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀', hBr'⟩, _, hT0', _⟩ := hrep2
      have hT' := compEdgeTrack_of_same_graph hT0'
        (hBr' j).2.1 (hBr' j).2.2.1 (hBr' j).2.2.2.2.1 (hBr' j).2.2.2.2.2.2
      have hR_le : (compLSFBatchFamily S1 us j).RF.R.card ≤ x.vCap := by
        rw [← hx1, ← hx2_1]
        exact (Finset.card_le_card fun r hr => Finset.mem_range.mpr
          (hT'.hVlt r ((compLSF_RF_isRSF (hBr' j).1).2.2.1 hr))).trans (by simp)
      have := hcnts1_le j; omega
    refine ⟨st3, cStep + cRest + 13, x2, touched2, fun j => cuts1 j ++ cuts2 j, sp1 ++ sp2,
      hrun_loop, fun r hr => (hr3_lt10 r hr).trans (by simp [st2, show r ≠ 10 by omega]; exact hr1_lt11 r (by omega)),
      by rw [hr3_12]; simp [List.length_append, Nat.add_assoc],
      hx2_1.trans hx1, hx2_2.trans hx2, hx2_3.trans hx3, hx2_4.trans hx4,
      hx2_5.trans hx5, hx2_6.trans hx6, hx2_7.trans hx7, hx2_8.trans hx8,
      hS'_eq.symm ▸ hrep2, hnd2, fun c hc => hx4 ▸ hlt2 c hc, hlen2,
      by simp [List.length_append]; omega, hhp2, hls2, ?_, ?_, ?_, hz2, ?_⟩
    · intro i hi
      by_cases hi1 : i < sp1.length
      · have hfr_sp : st3.mem (splitBase + (nSp + i)) = st2.mem (splitBase + (nSp + i)) :=
          hfr2 _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
            (fun j => by have := j.2; omega)
            (fun j => Or.inr (by
              have hj : (j.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by have := j.2; omega)
              rw [Nat.add_mul, Nat.one_mul] at hj; have := hcap12 j; rw [hx1]; omega))
            (fun j => Or.inr (by
              have hj : (j.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by have := j.2; omega)
              rw [Nat.add_mul, Nat.one_mul] at hj; have := hcap12 j; rw [hx1]; omega))
            (by omega)
        rw [hfr_sp, List.getElem_append_left hi1]; exact hsp1_m i hi1
      · have hi2 : i - sp1.length < sp2.length := by rw [List.length_append] at hi; omega
        rw [List.getElem_append_right (by omega : sp1.length ≤ i)]
        have hidx_eq : splitBase + (nSp + i) = splitBase + (nSp + sp1.length + (i - sp1.length)) := by omega
        rw [hidx_eq]; exact hsp2_m (i - sp1.length) hi2
    · intro j
      have hcomb_j := hcomb cuts2 sp2 S' (fun j' => by
        obtain ⟨_, _, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbr2 j'
        exact ⟨hx1 ▸ b1, b2, b3, b4, b5, b6, b7, b8, b9⟩) j
      refine ⟨by simpa [List.length_append, Nat.add_assoc] using (hbr2 j).1, ?_,
        hcomb_j.1, hcomb_j.2.1, hcomb_j.2.2.1, hcomb_j.2.2.2.1, hcomb_j.2.2.2.2.1,
        hcomb_j.2.2.2.2.2.1, hcomb_j.2.2.2.2.2.2.1, hcomb_j.2.2.2.2.2.2.2.1, hcomb_j.2.2.2.2.2.2.2.2⟩
      intro i hi
      by_cases hi1 : i < (cuts1 j).length
      · have hd := compStep_cutBuf_disj (cntBase := cntBase) hcap12 j hi1
        have hR_fr : st3.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) =
            st2.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) :=
          hfr2 _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
            (fun j0 => (hd.1 j0).1) (fun j0 => by rw [hx1]; exact (hd.2.1 j0).1)
            (fun j0 => by rw [hx1]; exact (hd.2.2.1 j0).1) (by omega)
        have hF_fr : st3.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) =
            st2.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) :=
          hfr2 _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
            (fun j0 => (hd.1 j0).2) (fun j0 => by rw [hx1]; exact (hd.2.1 j0).2)
            (fun j0 => by rw [hx1]; exact (hd.2.2.1 j0).2) (by omega)
        rw [hR_fr, hF_fr, List.getElem_append_left hi1]; exact (hbr1 j).2.1 i hi1
      · have hi2 : i - (cuts1 j).length < (cuts2 j).length := by rw [List.length_append] at hi; omega
        rw [List.getElem_append_right (by omega : (cuts1 j).length ≤ i)]
        have h := (hbr2 j).2.1 (i - (cuts1 j).length) hi2
        rw [hx1] at h
        have hidxR : rootsBase + j.1 * x.vCap + (cnts j + i) =
            rootsBase + j.1 * x.vCap + (cnts j + (cuts1 j).length + (i - (cuts1 j).length)) := by omega
        have hidxF : fDelBase + j.1 * x.vCap + (cnts j + i) =
            fDelBase + j.1 * x.vCap + (cnts j + (cuts1 j).length + (i - (cuts1 j).length)) := by omega
        rw [hidxR, hidxF]; exact h
    · intro z hout hnh hnl hnsp hnc hnrt hnfd hlt_buf
      have h2 := hfr2 z (by rw [hx7]; exact hout) hnh (by omega)
        (by rw [List.length_append] at hnsp; omega) hnc
        (fun j => by have := hnrt j; rw [hx1]; rw [List.length_append] at this; omega)
        (fun j => by have := hnfd j; rw [hx1]; rw [List.length_append] at this; omega) hlt_buf
      have h1 := hfr1 z hout hnh (by omega) (by rw [List.length_append] at hnsp; omega) hnc
        (fun j => by have := hnrt j; rw [List.length_append] at this; omega)
        (fun j => by have := hnfd j; rw [List.length_append] at this; omega) hlt_buf
      exact h2.trans h1
    · have hsum_cuts : (∑ j : Fin k, (cuts1 j ++ cuts2 j).length) =
          (∑ j : Fin k, (cuts1 j).length) + (∑ j : Fin k, (cuts2 j).length) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => List.length_append
      have hsteps_eq : compBatchStepsCost mem0 x.L_w cs0 uPtr (u :: us) =
          ((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
            lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
            lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) +
          compBatchStepsCost mem0 x.L_w (compLSFStepSingle cs0 u) (uPtr + uLen) us := by
        simp only [compBatchStepsCost, huLen_eq]
      rw [hx3] at hcost2
      rw [hsum_cuts, hsteps_eq]
      simp only [List.length_cons]
      have hmul_dist : k * (((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
            lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
            lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) +
          compBatchStepsCost mem0 x.L_w (compLSFStepSingle cs0 u) (uPtr + uLen) us) =
        k * ((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
            lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
            lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) +
        k * compBatchStepsCost mem0 x.L_w (compLSFStepSingle cs0 u) (uPtr + uLen) us := Nat.mul_add _ _ _
      rw [hmul_dist]
      change cStep + cRest + 13 + 120 * ((∑ j : Fin k, (cuts1 j).length) + (∑ j : Fin k, (cuts2 j).length)) +
        compPhi b x2 st3.mem ≤ _
      dsimp only [st2, cs0, S1] at hcost1 hcost2 ⊢
      omega

end

end MinCostFlow.SparseCore.Program
