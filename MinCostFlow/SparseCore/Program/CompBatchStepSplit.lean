module

public import MinCostFlow.SparseCore.Program.CompBatchStepSplitDisp
import WordRAM.Tactic

/-!
# Vertex-Split Step (`CompBatchStepSplit`)

Verifies `compStepSplitProc`: decodes an encoded `.split v v' St Sh` (Tag-2 or Tag-3), records
`vComp[v'] := cv` and `mem[splitPtr] := v'`, marks `cv` touched, dispatches the projected 1-update
split batch across all `k` branches via `compStepSplitDisp_runs`, and lifts the forest cuts to the
global rooted forest.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Full entry point: `compStepSplit_runs` -/

set_option maxHeartbeats 1200000 in
open Classical in
/-- Verification of `compStepSplitProc`: processes an encoded `.split v v' St Sh` (Tag-2 or Tag-3)
at `uPtr`, records `v'` at `splitPtr`, and returns `uPtr + uLen`, maintaining `CompLSFRepDirty`,
cut logs, `ZeroFrom`, frame, `compRF_cuts_lift_split` postconditions, and uniform amortized cost
`≤ 600 + k * ∑_{touched edgeful} (...)`. -/
theorem compStepSplit_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bApp bMark bDisp uPtr heap cntBase splitPtr updBuf v v' uLen : ℕ}
    {St Sh : Finset ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpApp : p.procs[bApp]? = some ghostAppendProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (hu_at : UpdateAt mem uPtr (S ⟨0, hrep.1⟩).G (.split v v' St Sh) uLen)
    (hu_words : ∀ i < uLen, mem (uPtr + i) < 2 ^ w)
    (hu_out : ∀ i < uLen, (uPtr + i < b ∨ x.endAddr ≤ uPtr + i) ∧ uPtr + i < heap)
    (hu_valid : (S ⟨0, hrep.1⟩).G.UpdateIsValid (.split v v' St Sh))
    (hv'Cap : v' < x.vCap)
    (hend_heap : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_sp : cntBase + k + 2 * (k * x.vCap) ≤ splitPtr)
    (hsp_buf : splitPtr + 1 ≤ updBuf)
    (hbuf_w : updBuf + 1 + uLen + 2 * x.eCap < 2 ^ w)
    (hz : ZeroFrom mem updBuf)
    (hcnt_touch : mem heap = touched.length)
    (hlist_touch : ListAt mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card) :
    let cs0 := S ⟨0, hrep.1⟩
    let S' : CompLSFFamily k := fun j => compLSFStepSingle (S j) (.split v v' St Sh)
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compStepSplitProc bApp bMark bDisp)
        (startState [b, uPtr, heap, cntBase, updBuf, splitPtr] mem pos)
        (.returned (uPtr + uLen)) st' cost ∧
      x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
      x'.numComps = x.numComps ∧ x'.numEdgeful = x.numEdgeful ∧
      x'.m0Total = x.m0Total ∧ x'.endAddr = x.endAddr ∧ HEq x'.compOf x.compOf ∧
      CompLSFRepDirty W k b S' x' touched' st'.mem ∧
      touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
      touched'.length ≤ touched.length + 2 ∧
      (∀ c : Fin x.numComps, c.1 ∈ touched' ↔
        c.1 ∈ touched ∨ x.compOf c ∈ touchedComps cs0 (.split v v' St Sh)) ∧
      st'.mem heap = touched'.length ∧
      ListAt st'.mem (heap + 1) touched' ∧
      st'.mem splitPtr = v' ∧
      (∀ j : Fin k,
        let RF_mid := (cuts j).foldl compApplyForestCut (S j).RF
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        CompForestCutsValid x.vCap (S j).RF (cuts j) ∧
        ((cuts j).map Prod.fst).Nodup ∧
        ((cuts j).map Prod.fst).toFinset = (S j).RF.F.E \ (S' j).RF.F.E ∧
        (S' j).RF.F.E ⊆ (S j).RF.F.E ∧
        ((cuts j).map Prod.snd).Nodup ∧
        v' ∉ (S j).RF.R ∧ v' ∈ (S' j).RF.R ∧ v' ∉ (cuts j).map Prod.snd ∧
        ((cuts j).map Prod.snd).toFinset = (S' j).RF.R.erase v' \ (S j).RF.R ∧
        (S j).RF.R ⊆ (S' j).RF.R ∧
        RF_mid.F.IsValid ∧ v ∈ RF_mid.R ∧ v ∈ RF_mid.F.V ∧ v' ∉ RF_mid.F.V ∧
        (S' j).RF.F.V = insert v' RF_mid.F.V ∧
        (S' j).RF.F.E = RF_mid.F.E ∧
        (S' j).RF.R = insert v' RF_mid.R ∧
        (∀ e ∈ RF_mid.F.E, unsplitMap v v' ((S' j).RF.F.tail e) = RF_mid.F.tail e ∧
          unsplitMap v v' ((S' j).RF.F.head e) = RF_mid.F.head e) ∧
        cnts j + (cuts j).length ≤ (S' j).RF.R.card) ∧
      (∀ a,
        (a < b ∨ x.endAddr ≤ a) →
        a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + touched.length + 2 ≤ a) →
        a ≠ splitPtr →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        a < updBuf → st'.mem a = mem a) ∧
      ZeroFrom st'.mem updBuf ∧
      cost + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' st'.mem ≤
        compPhi b x mem + 600 +
        k * ((touchedComps cs0 (.split v v' St Sh)).filter fun C =>
              1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.split v v' St Sh)) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.split v v' St Sh) * x.L_w)) := by
  intro cs0 S' rootsBase fDelBase
  obtain ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩,
    hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩ := hrep
  have hI0 : CompLSFInv W.C_lsst ℓ₀ cs0 := (hBr ⟨0, hk⟩).1
  have hS_G : ∀ j : Fin k, (S j).G = cs0.G := fun j => (hBr j).2.2.1
  obtain ⟨Cv, hCv, hvC⟩ := Finset.mem_biUnion.mp (hI0.hV_eq ▸ hu_valid.1)
  obtain ⟨cv, rfl⟩ := (hT.hBij.2 Cv).mp hCv
  have hv_lt : v < x.vCap := hT.hVlt v hu_valid.1
  have hv_only : ∀ c : Fin x.numComps, v ∈ (cs0.compSt (x.compOf c)).G.V ↔ c = cv := fun c =>
    ⟨fun h => by
      by_contra hne
      exact Finset.disjoint_left.mp (hI0.hV_disj _ (hT.compOf_mem c) _ hCv (fun h' => hne (hT.hBij.1 h'))) h hvC,
     fun h => h ▸ hvC⟩
  have htouch_iff : ∀ c : Fin x.numComps,
      x.compOf c ∈ touchedComps cs0 (.split v v' St Sh) ↔ c = cv := fun c => by
    have hmem : x.compOf c ∈ touchedComps cs0 (.split v v' St Sh) ↔
        x.compOf c ∈ components cs0.G₀ ∧ projCompUpdateG cs0.G (cs0.compSt (x.compOf c)).G (.split v v' St Sh) ≠ [] :=
      Finset.mem_filter
    rw [hmem, and_iff_right (hT.compOf_mem c)]
    dsimp only [projCompUpdateG]; simp only [hv_only c]
    by_cases hc : c = cv <;> simp [hc]
  have hefComp_inj : ∀ ec₁ ec₂ : Fin x.numEdgeful, x.edgefulComp ec₁ = x.edgefulComp ec₂ → ec₁ = ec₂ := by
    intro ec₁ ec₂ heq; have h1 := (hEfMeta ec₁).2; have h2 := (hEfMeta ec₂).2
    rw [heq] at h1; exact Fin.ext (h1.symm.trans h2)
  -- Decode `UpdateAt` into `tag, Lt, Lh`
  have hdec : ∃ (tag : ℕ) (Lt Lh : List ℕ), (tag = 2 ∨ tag = 3) ∧
      uLen = 5 + Lt.length + Lh.length ∧ Lt.Nodup ∧ Lh.Nodup ∧
      (tag = 2 → ∀ e, e ∈ Lt ↔ e ∈ cs0.G.E ∧ cs0.G.tail e = v ∧ e ∈ St) ∧
      (tag = 2 → ∀ e, e ∈ Lh ↔ e ∈ cs0.G.E ∧ cs0.G.head e = v ∧ e ∈ Sh) ∧
      (tag = 3 → ∀ e, e ∈ Lt ↔ e ∈ cs0.G.E ∧ cs0.G.tail e = v ∧ e ∉ St) ∧
      (tag = 3 → ∀ e, e ∈ Lh ↔ e ∈ cs0.G.E ∧ cs0.G.head e = v ∧ e ∉ Sh) ∧
      ListAt mem uPtr ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
    rcases hu_at with ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen, hLA⟩ | ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen, hLA⟩
    · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hnd1, hnd2, fun _ => h1, fun _ => h2, fun h => by omega, fun h => by omega, hLA⟩
    · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hnd1, hnd2, fun h => by omega, fun h => by omega, fun _ => h1, fun _ => h2, hLA⟩
  obtain ⟨tag, Lt, Lh, htag, huLen_eq, hLt_nd, hLh_nd, hLt_m2, hLh_m2, hLt_m3, hLh_m3, hLA_u⟩ := hdec
  have hu_in : mem uPtr = tag ∧ mem (uPtr + 1) = v ∧ mem (uPtr + 2) = v' ∧
      mem (uPtr + 3) = Lt.length ∧ mem (uPtr + 4) = Lh.length :=
    ⟨by simpa using hLA_u 0 (by simp), by simpa using hLA_u 1 (by simp),
     by simpa using hLA_u 2 (by simp), by simpa using hLA_u 3 (by simp), by simpa using hLA_u 4 (by simp)⟩
  have hLt_at : ListAt mem (uPtr + 5) Lt := fun i hi => by
    have h := hLA_u (5 + i) (by simp; omega)
    rw [show uPtr + (5 + i) = uPtr + 5 + i by omega,
        List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)] at h
    simpa using h
  have hLh_at : ListAt mem (uPtr + 5 + Lt.length) Lh := fun i hi => by
    have h := hLA_u (5 + Lt.length + i) (by simp; omega)
    rw [show uPtr + (5 + Lt.length + i) = uPtr + 5 + Lt.length + i by omega,
        List.getElem_append_right (by simp; omega)] at h
    convert h using 2; simp; omega
  have hu_le_heap0 : uPtr + uLen ≤ heap := by
    have := (hu_out (uLen - 1) (by omega)).2; omega
  have hbuf_w' : updBuf + 6 + Lt.length + Lh.length < 2 ^ w := by omega
  -- Step 1: Prefix
  obtain ⟨cP, hrunP, hcP⟩ := compStepSplitPref_runs (p := p) (b := b) (uPtr := uPtr) (heap := heap)
    (cntBase := cntBase) (updBuf := updBuf) (splitPtr := splitPtr) (pos := pos) (ω := ω)
    hw16 hTE (by omega) (by omega) (by omega) (by omega) hhdr hu_in hv_lt hv'Cap (hVComp cv v hvC)
  set st0 := startState [b, uPtr, heap, cntBase, updBuf, splitPtr] mem pos
  set m2 := Function.update (Function.update mem (compVCompBase b + v') cv.1) splitPtr v'
  set regsP :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update
      st0.regs 6 tag) 7 v) 8 v') 9 Lt.length) 10 Lh.length) 11 (compVCompBase b)) 12 cv.1)
      13 (compTouchMarkBase b x.vCap x.eCap)) 14 (heap + 1))
      15 (compEdgefulBase b x.vCap)) 16 (compEdgefulIdxBase b x.vCap))
      17 x.vCap) 18 x.eCap
  set stP : State := { st0 with regs := regsP, mem := m2 }
  have hm2_fr : ∀ z, z ≠ compVCompBase b + v' → z ≠ splitPtr → m2 z = mem z := fun z h1 h2 => by
    simp [m2, Function.update_of_ne h2, Function.update_of_ne h1]
  have htm_lt_end : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ x.endAddr := by
    have : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
        compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
        compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := by omega
  have htm_w : compTouchMarkBase b x.vCap x.eCap + x.vCap < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
      compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
      compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have hm2_ge_ef : ∀ z, compEdgefulBase b x.vCap ≤ z → z ≠ splitPtr → m2 z = mem z := fun z h1 h2 =>
    hm2_fr z (by dsimp only [compEdgefulBase] at h1; omega) h2
  -- Step 2: `compMarkTouchProc` on `cv`
  have hm2_mk : m2 (compTouchMarkBase b x.vCap x.eCap + cv.1) = if cv.1 ∈ touched then 1 else 0 :=
    (hm2_ge_ef _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega) (by have := cv.2; omega)).trans (hTM cv.1 (by have := cv.2; omega))
  obtain ⟨oM, stM, cM, hrunM, _, hmkM, hcntM, hlistM, hfrM, hcM⟩ :=
    compMarkTouch_call (cap := x.vCap) (L := touched) (c := cv.1) (pos := stP.pos) (ω := ω)
      hpMark hw16 (by have := cv.2; omega) htm_w
      (by omega) (by omega) (by omega) (by omega) (by omega) (fun i hi => ⟨by omega, by omega⟩)
      ((hm2_ge_ef heap (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at htm_lt_end; omega) (by omega)).trans hcnt_touch)
      (fun i hi => (hm2_ge_ef (heap + 1 + i) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at htm_lt_end; omega) (by omega)).trans (hlist_touch i hi))
      (by rw [hm2_mk]; split_ifs <;> simp)
  set touched' := if m2 (compTouchMarkBase b x.vCap x.eCap + cv.1) = 0 then touched ++ [cv.1] else touched
  let stC1 : State := { stP with regs := Function.update stP.regs 20 oM.value, mem := stM.mem, pos := stM.pos }
  have hrun_m : Runs w p ω (.call 20 bMark [.reg 13, .reg 14, .reg 2, .reg 12]) stP .normal stC1 (cM + 5) := by
    rw [runs_call_iff]
    refine ⟨[compTouchMarkBase b x.vCap x.eCap, heap + 1, heap, cv.1], compMarkTouchProc,
      oM, stM, cM, ?_, hpMark, hrunM, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, stP, regsP, st0, startState]
  have hM_below_tm : ∀ z < compTouchMarkBase b x.vCap x.eCap, stM.mem z = m2 z := fun z hz' =>
    hfrM z (by omega) (by omega) (by omega)
  have hM_mid : ∀ z, compEdgefulBase b x.vCap ≤ z → z < compTouchMarkBase b x.vCap x.eCap → stM.mem z = mem z := fun z h1 h2 =>
    (hM_below_tm z h2).trans (hm2_ge_ef z h1 (by omega))
  have hM_ge_handles : ∀ z, compHandlesBase b x.vCap x.eCap x.L_w ≤ z → z < heap → stM.mem z = mem z := fun z h1 h2 => by
    have hge_tm : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ z := by
      dsimp only [compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize,
        compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h1 ⊢; omega
    exact (hfrM z (by have := cv.2; omega) (by omega) (by omega)).trans
      (hm2_ge_ef z (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at hge_tm; omega) (by omega))
  have hM_ge_cnt : ∀ z, cntBase ≤ z → z ≠ splitPtr → stM.mem z = mem z := fun z h1 h2 =>
    (hfrM z (by omega) (by omega) (by omega)).trans
      (hm2_ge_ef z (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at htm_lt_end; omega) h2)
  have hM_hdr : ∀ z, b ≤ z → z < b + compHdrSize → stM.mem z = mem z := fun z h1 h2 =>
    (hM_below_tm z (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h2 ⊢; omega)).trans
      (hm2_fr z (by dsimp only [compVCompBase, compHdrSize] at h2 ⊢; omega) (by
        have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
          dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
        omega))
  -- Step 3: Conditional split dispatch on `cv`
  have hM_ef_spec : 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx cv = ec.1 ∧
        stM.mem (compEdgefulIdxBase b x.vCap + cv.1) = ec.1 ∧ x.edgefulComp ec = cv ∧
        CompDispatchWinOk W k b S x ec stM.mem := fun hpos => by
    obtain ⟨ec, hidx, hmem_idx, hcomp⟩ := (hCompMeta cv).2.2.2 hpos
    have hwin_orig : CompDispatchWinOk W k b S x ec mem :=
      ⟨hk, hLw, hnumEf, hTE, hhdr.2.2.1, hhdr.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
       fun j => (hBr j).2.2.2.2.2.2 (x.edgefulComp ec), fun j => hWins ec j,
       fun j₁ j₂ hne => hDisj ec ec j₁ j₂ (Or.inr hne)⟩
    refine ⟨ec, hidx, (hM_mid _ (by dsimp only [compEdgefulIdxBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; have := cv.2; omega)).trans hmem_idx,
      hcomp, hwin_orig.of_agree
      ⟨hM_hdr _ (by dsimp only [compOffK]; omega) (by dsimp only [compOffK, compHdrSize]; omega),
       hM_hdr _ (by dsimp only [compOffVCap]; omega) (by dsimp only [compOffVCap, compHdrSize]; omega),
       hM_hdr _ (by dsimp only [compOffHandlesPtr]; omega) (by dsimp only [compOffHandlesPtr, compHdrSize]; omega)⟩
      (fun j => hM_ge_handles _ (Nat.le_add_right _ _) (by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        dsimp only [compTablesEnd] at hTE; omega))
      (fun j z hz => by
        obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
        have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
          dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz.1)
        exact hM_ge_handles z hge_h (lt_of_lt_of_le hz.2 (le_trans hle hend_heap)))⟩
  have hu_le_heap : uPtr + uLen ≤ heap := by
    have hpos : 0 < uLen := by omega
    have := (hu_out (uLen - 1) (by omega)).2; omega
  have hM_u_ag : ∀ z, uPtr ≤ z → z < uPtr + uLen → stM.mem z = mem z := fun z hz1 hz2 => by
    have hout := (hu_out (z - uPtr) (by omega)).1
    have hlt_h := (hu_out (z - uPtr) (by omega)).2
    have heq_z : uPtr + (z - uPtr) = z := by omega
    rw [heq_z] at hout hlt_h
    have hvc_lt_end : compVCompBase b + v' < x.endAddr := by
      have : compVCompBase b + v' < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize]; omega
      omega
    have hvc_ge_b : b ≤ compVCompBase b + v' := by dsimp only [compVCompBase, compHdrSize]; omega
    have htm_ge_b : b ≤ compTouchMarkBase b x.vCap x.eCap + cv.1 := by
      dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase,
        compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
        compEdgefulBase, compVCompBase, compHdrSize]; omega
    have htm_lt_end' : compTouchMarkBase b x.vCap x.eCap + cv.1 < x.endAddr := by have := cv.2; omega
    rw [hfrM z (by rcases hout with h | h <;> omega) (by omega) (by omega)]
    exact hm2_fr z (by rcases hout with h | h <;> omega) (by omega)
  have hM_cr_ag : ∀ f < x.eCap, stM.mem (compIsCrossBase b x.vCap x.eCap + f) =
      if f ∈ cs0.crossEdges then 1 else 0 := fun f hf =>
    (hM_mid _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)
      (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase]; omega)).trans (hFlags f hf).1
  have hLt_w : ∀ e ∈ Lt, e < 2 ^ w := fun e he => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    rw [← hLt_at i hi]; simpa [Nat.add_assoc] using hu_words (5 + i) (by omega)
  have hLh_w : ∀ e ∈ Lh, e < 2 ^ w := fun e he => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    rw [← hLh_at i hi]; simpa [Nat.add_assoc] using hu_words (5 + Lt.length + i) (by omega)
  obtain ⟨stD, cD, cuts, winConc', hrunD, hregsD, hbrD, hwinD, hfrD, hzD, hcostD⟩ :=
    compStepSplitDisp_runs (uPtr := uPtr) (cntBase := cntBase) (updBuf := updBuf) (tag := tag)
      (v := v) (v' := v') (St := St) (Sh := Sh) (Lt := Lt) (Lh := Lh) (cnts := cnts) (st := stC1) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpApp hpDisp hw16 hk hLw htag cv hefComp_inj (fun ec => (hEfMeta ec).1)
      (by simp [stC1, stP, regsP, st0, startState]) (by simp [stC1, stP, regsP, st0, startState])
      (by simp [stC1, stP, regsP, st0, startState]) (by simp [stC1, stP, regsP, st0, startState])
      (by simp [stC1, stP, regsP]) (by simp [stC1, stP, regsP]) (by simp [stC1, stP, regsP])
      (by simp [stC1, stP, regsP]) (by simp [stC1, stP, regsP]) (by simp [stC1, stP, regsP])
      (by simp [stC1, stP, regsP]) (by simp [stC1, stP, regsP])
      hnumC (by omega) (by omega) (by omega) hbuf_w'
      (fun z hz' => (hM_ge_cnt z (by omega) (by omega)).trans (hz z hz'))
      (fun j => (hM_ge_cnt _ (Nat.le_add_right _ _) (by have := j.2; omega)).trans (hcnts_m j))
      hTE
      ((hM_mid _ (Nat.le_add_right _ _) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; have := cv.2; omega)).trans (hCompMeta cv).1)
      hM_ef_spec ⟨ℓ₀, hI0⟩ hT hu_valid hvC hv_lt hv'Cap
      (fun i hi => (hM_u_ag (uPtr + 5 + i) (by omega) (by omega)).trans (hLt_at i hi))
      (fun i hi => (hM_u_ag (uPtr + 5 + Lt.length + i) (by omega) (by omega)).trans (hLh_at i hi))
      hLt_nd hLh_nd hLt_m2 hLh_m2 hLt_m3 hLh_m3 hLt_w hLh_w
      ((hM_hdr _ (by dsimp only [compOffIsCrossPtr]; omega) (by dsimp only [compOffIsCrossPtr, compHdrSize]; omega)).trans hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      hM_cr_ag
      (fun j => by
        have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
        exact compRootCap_le_vCap (hBr j).1 hTj (hcnts_le j) cv _)
  -- Step 4: Return `uPtr + 5 + Lt.length + Lh.length`
  have hw5 : 5 < 2 ^ w := by omega
  have hrun_ret : Runs w p ω (.ret (.bin .add (.bin .add (.bin .add (.reg 1) (.const 5)) (.reg 9)) (.reg 10)))
      stD (.returned (uPtr + uLen)) stD 8 := by
    rw [runs_ret_iff]
    refine ⟨uPtr + uLen, ?_, rfl, rfl, by simp [Expr.size]⟩
    have hr1 : stD.regs 1 = uPtr := (hregsD 1 (by omega)).trans (by simp [stC1, stP, regsP, st0, startState])
    have hr9 : stD.regs 9 = Lt.length := (hregsD 9 (by omega)).trans (by simp [stC1, stP, regsP])
    have hr10 : stD.regs 10 = Lh.length := (hregsD 10 (by omega)).trans (by simp [stC1, stP, regsP])
    simp [Expr.eval, BinOp.eval, hr1, hr9, hr10, hw5, show uPtr + 5 < 2 ^ w by omega,
      show uPtr + 5 + Lt.length < 2 ^ w by omega, show uPtr + 5 + Lt.length + Lh.length < 2 ^ w by omega, huLen_eq]
    omega
  have hrun_all : Runs w p ω (compStepSplitProc bApp bMark bDisp) st0 (.returned (uPtr + uLen)) stD
      (cP + cM + cD + 16) :=
    runs_seq_iff.mpr (Or.inr ⟨stP, cP, _, hrunP,
      runs_seq_iff.mpr (Or.inr ⟨stC1, cM + 5, _, hrun_m,
      runs_seq_iff.mpr (Or.inr ⟨stD, cD, 8, hrunD, hrun_ret, rfl⟩), rfl⟩), by omega⟩)
  -- Post-step invariants
  have hBr' : ∀ j : Fin k,
      CompLSFInv W.C_lsst ℓ₀ (S' j) ∧ (S' j).G₀ = (S' ⟨0, hk⟩).G₀ ∧
      (S' j).G = (S' ⟨0, hk⟩).G ∧ (S' j).k = k ∧
      (S' j).crossEdges = (S' ⟨0, hk⟩).crossEdges ∧
      (S' j).insertedGlobal = (S' ⟨0, hk⟩).insertedGlobal ∧
      (∀ c : Fin x.numComps, ((S' j).compSt (x.compOf c)).G = ((S' ⟨0, hk⟩).compSt (x.compOf c)).G) := by
    intro j
    have hIj := (hBr j).1; have hu_j := (hS_G j).symm ▸ hu_valid; have hG0j := (hBr j).2.1
    refine ⟨compLSFInv_step hIj hu_j, hG0j, by simp [S', compLSFStepSingle, hS_G j, cs0],
      (hBr j).2.2.2.1, by simp [S', compLSFStepSingle, (hBr j).2.2.2.2.1],
      by simp [S', compLSFStepSingle, (hBr j).2.2.2.2.2.1], ?_⟩
    intro c
    have hG_c := applyLSFBatch_G_of_valid (hIj.hCompLSF _ (hG0j.symm ▸ hT.compOf_mem c)).1
      (projCompUpdateG_valid hIj hu_j (hG0j.symm ▸ hT.compOf_mem c))
    have hG_0 := applyLSFBatch_G_of_valid (hI0.hCompLSF _ (hT.compOf_mem c)).1
      (projCompUpdateG_valid hI0 hu_valid (hT.compOf_mem c))
    change (applyLSFBatch ((S j).compSt (x.compOf c)) _).G = (applyLSFBatch (cs0.compSt (x.compOf c)) _).G
    rw [hG_c, hG_0, hS_G j, (hBr j).2.2.2.2.2.2 c]
  have hT' := compEdgeTrack_step_split hI0 hT hu_valid hv'Cap hvC
  let x' : CompLSFMeta k := { x with winConc := winConc' }
  have hD_below_tables : ∀ z < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k, stD.mem z = stM.mem z := fun z hz' =>
    hfrD z (fun ec j _ ha => by obtain ⟨_, _, _, _, _, hge, _⟩ := hWins ec j; exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hz' hge)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)
  have hD_mid : ∀ z, compEdgefulBase b x.vCap ≤ z → z < compTouchMarkBase b x.vCap x.eCap → stD.mem z = mem z := fun z h1 h2 =>
    (hD_below_tables z (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h2 ⊢; omega)).trans (hM_mid z h1 h2)
  have htouch'_len : touched'.length ≤ touched.length + 2 := by dsimp only [touched']; split_ifs <;> simp
  have hD_heap : stD.mem heap = touched'.length :=
    (hfrD heap (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle hend_heap)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans hcntM
  have hD_list : ListAt stD.mem (heap + 1) touched' := fun i hi =>
    (hfrD (heap + 1 + i) (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans (hlistM i hi)
  have hD_splitPtr : stD.mem splitPtr = v' := by
    have hlen_j : ∀ j : Fin k, cnts j + (cuts j).length ≤ x.vCap := fun j => by
      by_cases hp : 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m
      · set u_c : Update := .split v v'
          ((cs0.compSt (x.compOf cv)).G.E.filter fun e => e ∈ St ∧ (cs0.compSt (x.compOf cv)).G.tail e = v ∧ cs0.G.tail e = v)
          ((cs0.compSt (x.compOf cv)).G.E.filter fun e => e ∈ Sh ∧ (cs0.compSt (x.compOf cv)).G.head e = v ∧ cs0.G.head e = v)
        have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
        have hcap_j := compRootCap_le_vCap (hBr j).1 hTj (hcnts_le j) cv u_c
        have hcard := List.toFinset_card_of_nodup ((hbrD j).2.2.1 hp).2.2.2.2.1
        rw [List.length_map, ((hbrD j).2.2.1 hp).2.2.2.2.2.2.2] at hcard
        have hsub : ((applyLSFUpdate ((S j).compSt (x.compOf cv)) u_c).RF.R.erase v' \ ((S j).compSt (x.compOf cv)).RF.R) ⊆
            ((applyLSFUpdate ((S j).compSt (x.compOf cv)) u_c).R_orig \ ((S j).compSt (x.compOf cv)).R_orig) := fun z hz => by
          dsimp only [u_c] at hz ⊢
          simp only [LSFState.RF, LSFState.R, applyLSFUpdate, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_insert] at hz ⊢
          exact ⟨by rcases hz.1.2 with h1 | (h2 | h3); exact h1; exact absurd h2 hz.1.1; exact absurd (Or.inr h3) hz.2, fun h => hz.2 (Or.inl h)⟩
        have := Finset.card_le_card hsub; omega
      · rw [(hbrD j).2.2.2 (by dsimp only [cs0] at hp; omega)]; simp
        have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
        have hR_le : (S j).RF.R.card ≤ x.vCap :=
          (Finset.card_le_card fun r hr => Finset.mem_range.mpr (hTj.hVlt r ((compLSF_RF_isRSF (hBr j).1).2.2.1 hr))).trans (by simp)
        have := hcnts_le j; omega
    have h1 := hfrD splitPtr
      (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
      (fun j => by have := j.2; omega)
      (fun j => Or.inr (by
        have hjk : (j.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by have := j.2; omega)
        rw [Nat.add_mul, Nat.one_mul] at hjk; have := hlen_j j; omega))
      (fun j => Or.inr (by
        have hjk : (j.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by have := j.2; omega)
        rw [Nat.add_mul, Nat.one_mul] at hjk; have := hlen_j j; omega))
      (by omega)
    rw [h1, hfrM splitPtr (by omega) (by omega) (by omega)]; simp [m2]
  have htouch'_iff : ∀ c : Fin x.numComps, c.1 ∈ touched' ↔ c.1 ∈ touched ∨ c = cv := fun c => by
    dsimp only [touched']; rw [hm2_mk]
    by_cases hcvt : cv.1 ∈ touched
    · simp only [hcvt, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]
      exact ⟨Or.inl, fun h => h.elim id (fun h' => h' ▸ hcvt)⟩
    · simp only [hcvt, ↓reduceIte, List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.elim Or.inl (fun h' => Or.inr (Fin.ext h')),
        fun h => h.elim Or.inl (fun h' => Or.inr (congrArg Fin.val h'))⟩
  have htouch'_nd : touched'.Nodup := by
    dsimp only [touched']; rw [hm2_mk]
    by_cases hcvt : cv.1 ∈ touched
    · simp only [hcvt, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]; exact htouch_nd
    · simp only [hcvt, ↓reduceIte]
      exact List.nodup_append.mpr ⟨htouch_nd, List.nodup_singleton _, fun z hz w hw heq => hcvt (List.mem_singleton.mp hw ▸ heq ▸ hz)⟩
  have htouch'_lt : ∀ c ∈ touched', c < x.numComps := fun c hc => by
    dsimp only [touched'] at hc; rw [hm2_mk] at hc
    by_cases hcvt : cv.1 ∈ touched
    · simp only [hcvt, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega] at hc; exact htouch_lt c hc
    · simp only [hcvt, ↓reduceIte, List.mem_append, List.mem_singleton] at hc
      exact hc.elim (htouch_lt c) (fun h => h ▸ cv.2)
  -- Assemble `CompLSFRepDirty`
  have hrep' : CompLSFRepDirty W k b S' x' touched' stD.mem := by
    refine ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE,
      compHeaderAt_of_agree hhdr (fun z hz1 hz2 => (hD_below_tables z (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hz2 ⊢; omega)).trans (hM_hdr z hz1 hz2)),
      ⟨ℓ₀, hBr'⟩, hm0Tot, by simpa [x'] using hT', ?_, hEfMeta, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c; dsimp only [x']; have hc_lt : c.1 < x.numComps := c.2; obtain ⟨h1, h2, h3, h4⟩ := hCompMeta c
      refine ⟨(hD_mid _ (Nat.le_add_right _ _) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)).trans h1,
        (hD_mid _ (by dsimp only [compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base]; omega)).trans h2,
        (hD_mid _ (by dsimp only [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base]; omega)).trans h3, fun hpos => ?_⟩
      obtain ⟨ec, he1, he2, he3⟩ := h4 hpos
      exact ⟨ec, he1, (hD_mid _ (by dsimp only [compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega)).trans he2, he3⟩
    · intro c u hu; dsimp only [x']
      have hVc : ((S' ⟨0, hk⟩).compSt (x.compOf c)).G.V =
          if c = cv then insert v' (cs0.compSt (x.compOf c)).G.V else (cs0.compSt (x.compOf c)).G.V := by
        have hG := applyLSFBatch_G_of_valid (hI0.hCompLSF _ (hT.compOf_mem c)).1
          (projCompUpdateG_valid hI0 hu_valid (hT.compOf_mem c))
        dsimp only [S', compLSFStepSingle]; rw [hG]; simp only [projCompUpdateG, hv_only c]; split_ifs <;> rfl
      rw [hVc] at hu
      have hu_lt : u < x.vCap := by
        split_ifs at hu
        · rcases Finset.mem_insert.mp hu with rfl | hu0; exact hv'Cap
          exact hT.hVlt u (hI0.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hT.compOf_mem c, hu0⟩)
        · exact hT.hVlt u (hI0.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hT.compOf_mem c, hu⟩)
      rw [hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize]; omega),
          hM_below_tm _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)]
      by_cases huv' : u = v'
      · subst huv'
        have hccv : c = cv := by
          by_contra hne; rw [ite_eq_right hne] at hu
          exact hu_valid.2.1 (hI0.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hT.compOf_mem c, hu⟩)
        subst hccv; dsimp only [m2]
        rw [Function.update_of_ne (by
          have : compVCompBase b + u < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
            dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize]; omega
          omega), Function.update_self]
      · have hu0 : u ∈ (cs0.compSt (x.compOf c)).G.V := by
          split_ifs at hu; exact (Finset.mem_insert.mp hu).resolve_left huv'; exact hu
        rw [hm2_fr _ (by omega) (by
          have : compVCompBase b + u < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
            dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize]; omega
          omega)]
        exact hVComp c u hu0
    · intro f hf; dsimp only [x']
      have hf_lt : f < x.eCap := hT.hElt f hf
      exact ⟨(hD_mid _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)).trans (hEdgeC f hf).1,
        (hD_mid _ (by dsimp only [compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase]; omega)).trans (hEdgeC f hf).2⟩
    · intro f hf; dsimp only [x'] at hf ⊢
      exact ⟨(hD_mid _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase]; omega)).trans (hFlags f hf).1,
        (hD_mid _ (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize]; omega)).trans (hFlags f hf).2⟩
    · dsimp only [x']
      set gPtr := compGhostBase b x.vCap x.eCap
      have hgh_ag : ∀ z, gPtr ≤ z → z < compTouchMarkBase b x.vCap x.eCap → stD.mem z = mem z := fun z h1 h2 =>
        hD_mid z (by dsimp only [gPtr, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at h1; omega) h2
      refine ⟨fun u hu => ?_, fun f hf hcr => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hGhost.1 u hu
        exact ⟨h1.of_agree
            (hgh_ag _ (by dsimp only [ghostTHeadBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTHeadBase, gPtr]; omega))
            (fun f hf => have := (hT.hGT u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostTPrevBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTPrevBase, gPtr]; omega))
            (fun f hf => have := (hT.hGT u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostTNextBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostTCntBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTCntBase, gPtr]; omega)).trans h2,
          h3.of_agree
            (hgh_ag _ (by dsimp only [ghostHHeadBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHHeadBase, gPtr]; omega))
            (fun f hf => have := (hT.hGH u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostHPrevBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHPrevBase, gPtr]; omega))
            (fun f hf => have := (hT.hGH u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostHNextBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostHCntBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHCntBase, gPtr]; omega)).trans h4⟩
      · have hf_lt : f < x.eCap := hT.hElt f hf
        exact ⟨(hgh_ag _ (by dsimp only [ghostTVertBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTVertBase, gPtr]; omega)).trans (hGhost.2 f hf hcr).1,
          (hgh_ag _ (by dsimp only [ghostHVertBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHVertBase, gPtr]; omega)).trans (hGhost.2 f hf hcr).2⟩
    · intro c hc; dsimp only [x'] at hc ⊢
      rw [hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)]
      by_cases hccv : c = cv.1
      · subst hccv; rw [hmkM, ite_eq_left ((htouch'_iff cv).mpr (Or.inr rfl))]
      · rw [hfrM _ (by omega) (by omega) (by omega),
            hm2_ge_ef _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega) (by omega),
            hTM c hc]
        have hiff : c ∈ touched' ↔ c ∈ touched := by dsimp only [touched']; split_ifs <;> simp [hccv]
        simp [hiff]
    · dsimp only [x']
      have hone_ag : ∀ i < x.L_w, stD.mem (compOneLimbBase b x.vCap x.eCap + i) = mem (compOneLimbBase b x.vCap x.eCap + i) := fun i hi => by
        have hge_tm : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compOneLimbBase b x.vCap x.eCap + i := by dsimp only [compOneLimbBase]; omega
        have h1e := compOneLimb_end_eq b x.vCap x.eCap x.L_w
        have hlt_te : compOneLimbBase b x.vCap x.eCap + i < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by dsimp only [compTablesEnd]; omega
        rw [hD_below_tables _ hlt_te, hfrM _ (by have := cv.2; omega) (by omega) (by omega),
            hm2_ge_ef _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at hge_tm; omega) (by omega)]
      exact ⟨(hone_ag 0 hLw).trans hOne.1, fun i h1 h2 => (hone_ag i h2).trans (hOne.2 i h1 h2)⟩
    · intro ec j; dsimp only [x']; have hec_lt : ec.1 < x.numEdgeful := ec.2
      obtain ⟨hslot, hrep_ec, hv, he, hL, hge, hle⟩ := hWins ec j
      have hslot' : stD.mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) = x.winHandle ec j := by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        exact (hD_below_tables _ (by dsimp only [compTablesEnd]; omega)).trans ((hM_ge_handles _ (Nat.le_add_right _ _) (by dsimp only [compTablesEnd] at hTE; omega)).trans hslot)
      by_cases hec : x.edgefulComp ec = cv
      · obtain ⟨hss, hrep_new⟩ := (hwinD ec j).1 hec
        have hSt_eq : (S' j).compSt (x.compOf (x.edgefulComp ec)) =
            applyLSFUpdate ((S j).compSt (x.compOf cv))
              (.split v v' ((cs0.compSt (x.compOf cv)).G.E.filter fun e => e ∈ St ∧ (cs0.compSt (x.compOf cv)).G.tail e = v ∧ cs0.G.tail e = v)
                ((cs0.compSt (x.compOf cv)).G.E.filter fun e => e ∈ Sh ∧ (cs0.compSt (x.compOf cv)).G.head e = v ∧ cs0.G.head e = v)) := by
          rw [hec]
          change applyLSFBatch _ (projCompUpdateG (S j).G ((S j).compSt (x.compOf cv)).G (.split v v' St Sh)) = _
          simp [projCompUpdateG, applyLSFBatch, hS_G j, (hBr j).2.2.2.2.2.2 cv, hvC, cs0]
        exact ⟨hslot', hSt_eq ▸ hrep_new, hss.1.trans hv, hss.2.1.trans he,
          hss.2.2.2.2.2.2.2.2.1.trans hL, hge, (hss.endAddr (x.winHandle ec j)).symm ▸ hle⟩
      · have hwc : winConc' ec j = x.winConc ec j := (hwinD ec j).2 hec
        have hSt_eq : (S' j).compSt (x.compOf (x.edgefulComp ec)) = (S j).compSt (x.compOf (x.edgefulComp ec)) := by
          have hv_not : v ∉ ((S j).compSt (x.compOf (x.edgefulComp ec))).G.V := by
            rw [(hBr j).2.2.2.2.2.2]; exact fun h => hec ((hv_only _).mp h)
          change applyLSFBatch _ (projCompUpdateG (S j).G _ (.split v v' St Sh)) = _
          simp [projCompUpdateG, hv_not, applyLSFBatch]
        have hrep_old' : (LSFRep W.h).rep (x.winHandle ec j) ((S j).compSt (x.compOf (x.edgefulComp ec)))
            (x.winConc ec j) stD.mem := by
          refine (lsfRep_local W.h _ _ _ mem stD.mem fun z hz => ?_).1 hrep_ec
          have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
            dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz.1)
          have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz.2 hle
          symm
          exact (hfrD z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hec (h ▸ h0))) z hz ha0)
            (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
            (hM_ge_handles z hge_h (lt_of_lt_of_le hz.2 (le_trans hle hend_heap)))
        rw [hwc, hSt_eq]; exact ⟨hslot', hrep_old', hv, he, hL, hge, hle⟩
    · intro ec₁ ec₂ j₁ j₂ hne z h1 h2; dsimp only [x'] at h1 h2
      have hsame : ∀ ec j, (LSFRep W.h).foot (x.winHandle ec j) (winConc' ec j) z ↔
          (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) z := fun ec j => by
        by_cases hc : x.edgefulComp ec = cv
        · simp [LSFRep, ((hwinD ec j).1 hc).1.endAddr]
        · rw [(hwinD ec j).2 hc]
      exact hDisj ec₁ ec₂ j₁ j₂ hne z ((hsame ec₁ j₁).mp h1) ((hsame ec₂ j₂).mp h2)
  -- Cost & potential bound
  have hphi_old : compPhi b x mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem :=
    compPhi_eq_sum_dirty ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr,
      ⟨ℓ₀, hBr⟩, hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩
  have hphi_new : compPhi b x' stD.mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem :=
    compPhi_eq_sum_dirty hrep'
  have hpw_eq : projUpdWords mem cs0 (x.compOf cv) uPtr (.split v v' St Sh) =
      5 + Lt.length + Lh.length := by
    have hbase : dgUpdateMemLen mem uPtr = 5 + Lt.length + Lh.length := by
      dsimp only [dgUpdateMemLen]; rw [hu_in.1, hu_in.2.2.2.1, hu_in.2.2.2.2]
      rcases htag with rfl | rfl <;> rfl
    dsimp only [projUpdWords]; rw [ite_eq_left hvC, hbase]
  have hcost_final : (cP + cM + cD + 16) + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' stD.mem ≤
      compPhi b x mem + 600 +
      k * ((touchedComps cs0 (.split v v' St Sh)).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
        lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.split v v' St Sh)) * x.L_w + 1) +
        lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.split v v' St Sh) * x.L_w)) := by
    have hfilt : (touchedComps cs0 (.split v v' St Sh)).filter (fun C => 1 ≤ (compGraph cs0.G₀ C).m) =
        if 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m then {x.compOf cv} else ∅ := by
      ext C; simp only [Finset.mem_filter]
      by_cases hC : C ∈ components cs0.G₀
      · obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
        rw [htouch_iff c]; split_ifs with hp
        · simp only [Finset.mem_singleton, hT.hBij.1.eq_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hp⟩⟩
        · simp only [Finset.notMem_empty, iff_false, not_and]; intro h; subst h; exact hp
      · have hnot : C ∉ touchedComps cs0 (.split v v' St Sh) := fun h => hC (Finset.mem_filter.mp h).1
        have hne : C ≠ x.compOf cv := fun h => hC (h ▸ hCv)
        split_ifs <;> simp [hnot, hne]
    rw [hphi_new, hphi_old, hfilt]
    by_cases hpos : 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m
    · rw [ite_eq_left hpos, Finset.sum_singleton, hpw_eq]; rw [dite_eq_left hpos] at hcostD
      obtain ⟨ec1, hec1, hcostD'⟩ := hcostD
      have hphi_unch : ∀ ec ≠ ec1,
          (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem) =
          (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) := fun ec hne => by
        have hne_c : x.edgefulComp ec ≠ cv := fun h => hne (hefComp_inj ec ec1 (h.trans hec1.symm))
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(hwinD ec j).2 hne_c]
        obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
        refine lsfPhi_congr fun z hz1 hz2 => ?_
        have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
          dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz1)
        have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz2 hle
        exact (hfrD z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hne_c (h ▸ h0))) z ⟨hz1, hz2⟩ ha0)
          (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
          (hM_ge_handles z hge_h (lt_of_lt_of_le hz2 (le_trans hle hend_heap)))
      have hphi_m_ec1 : (∑ j : Fin k, lsfPhi (x.winHandle ec1 j) (x.winConc ec1 j) stM.mem) =
          (∑ j : Fin k, lsfPhi (x.winHandle ec1 j) (x.winConc ec1 j) mem) :=
        Finset.sum_congr rfl fun j _ => by
          obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec1 j
          have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ x.winHandle ec1 j := by
            dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) hge
          exact lsfPhi_congr fun z hz1 hz2 => hM_ge_handles z (le_trans hge_h hz1) (lt_of_lt_of_le hz2 (le_trans hle hend_heap))
      rw [hphi_m_ec1] at hcostD'
      rw [← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem) (Finset.mem_univ ec1),
          ← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) (Finset.mem_univ ec1)]
      rw [Finset.sum_congr rfl fun ec hec => hphi_unch ec (Finset.mem_erase.mp hec).1]
      set len := 5 + Lt.length + Lh.length
      have habs := compSingleDispatch_cost_le (len := len) hk hLw (by omega)
      linarith
    · rw [ite_eq_right hpos, Finset.sum_empty]; rw [dite_eq_right hpos] at hcostD
      obtain ⟨hcD, hmD⟩ := hcostD
      have hcuts0 : ∑ j : Fin k, (cuts j).length = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [(hbrD j).2.2.2 (by dsimp only [cs0] at hpos; omega)]; rfl
      have hphi_eq : (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem) =
          (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) :=
        Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => by
          rw [(hwinD ec j).2 (fun h => hpos (h ▸ (hEfMeta ec).1))]
          obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
          have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ x.winHandle ec j := by
            dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) hge
          exact lsfPhi_congr fun z hz1 hz2 => (hmD z).trans
            (hM_ge_handles z (le_trans hge_h hz1) (lt_of_lt_of_le hz2 (le_trans hle hend_heap)))
      rw [hcuts0, hphi_eq]; omega
  -- Final assembly
  refine ⟨stD, cP + cM + cD + 16, x', touched', cuts, hrun_all,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    hrep', htouch'_nd, htouch'_lt, htouch'_len,
    fun c => by rw [htouch'_iff c, htouch_iff c],
    hD_heap, hD_list, hD_splitPtr, ?_, ?_, hzD, hcost_final⟩
  · intro j
    have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
    have hG0j := (hBr j).2.1
    have hv_j : v ∈ ((S j).compSt (x.compOf cv)).G.V := ((hBr j).2.2.2.2.2.2 cv).symm ▸ hvC
    have hlift := compRF_cuts_lift_split (hBr j).1 hTj ((hS_G j).symm ▸ hu_valid) hv_j
      (fun hp => by
        have h := (hbrD j).2.2.1 (by simpa [hG0j] using hp)
        have hGj := (hBr j).2.2.2.2.2.2 cv
        have hnv' : v' ∉ ((S j).compSt (x.compOf cv)).RF.R ∧ ∀ z, (z, v') ∉ cuts j :=
          ⟨fun hr => h.2.2.2.2.2.2.1 (Finset.mem_union_left _ hr),
           fun z hz => h.2.2.2.2.2.2.1 (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.snd) hz)))⟩
        simpa [hS_G j, hGj, cs0] using ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, hnv', h.2.2.2.2.2.2.2⟩)
      (fun hm => (hbrD j).2.2.2 (by simpa [hG0j] using hm))
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hlift
    exact ⟨(hbrD j).1, (hbrD j).2.1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, compStep_cnts_le_of_lift_split (hcnts_le j) h10 h6 h5 h9⟩
  · intro z hout hnh hnl hnsp hnc hnrt hnfd hlt_buf
    have h1 : stD.mem z = stM.mem z := hfrD z (fun ec j _ ha => by
      obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
      have hb_le : b ≤ x.winHandle ec j := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hge; omega
      rcases hout with hlt | hge'
      · exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hlt hb_le))
      · exact absurd ha.2 (not_lt.mpr (le_trans hle hge'))) hnc hnrt hnfd hlt_buf
    have hne_list : z ≠ heap + 1 + touched.length := by omega
    have hne_tm : z ≠ compTouchMarkBase b x.vCap x.eCap + cv.1 := by
      have : b ≤ compTouchMarkBase b x.vCap x.eCap + cv.1 := by
        dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase,
          compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compHdrSize]; omega
      have : compTouchMarkBase b x.vCap x.eCap + cv.1 < x.endAddr := by have := cv.2; omega
      rcases hout with hlt | hge' <;> omega
    have hne_vc : z ≠ compVCompBase b + v' := by
      have : b ≤ compVCompBase b + v' := by dsimp only [compVCompBase, compHdrSize]; omega
      have : compVCompBase b + v' < x.endAddr := by
        have : compVCompBase b + v' < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
          dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize]; omega
        omega
      rcases hout with hlt | hge' <;> omega
    rw [h1, hfrM z hne_tm hnh hne_list, hm2_fr z hne_vc hnsp]

end

end MinCostFlow.SparseCore.Program

