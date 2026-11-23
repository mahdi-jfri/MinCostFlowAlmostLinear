module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopPassKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSizesKFBL
public import MinCostFlow.MinRatio.OrdSolverToolMono
import MinCostFlow.MinRatio.WireChainCoreAlgebra
import WordRAM.Tactic

/-!
# The plain-step loop of Branch B under `KFBL` (`WireChainCoreBranchBLoopKFBL`)

The loop `wireBranchBLoopKFBL` runs the plain passes at the levels `idx, idx + 1, …` until the
threshold test fires at a level `i₀ < d` or until `i₀ = d`. When the test fires, the body only
stores `i₀` in the end register `reg 99` (`wireBranchBLoopBodyKFBL_runs_over`), and the loop stops.

`wireBranchBLoopKFBL_runs` is the run of the whole loop, by induction on the number `rem` of
levels left. At the exit level `i₀` it gives the invariant `BranchBLoopInvKFBL` and the model
invariant, the tie of `Chain.Ordered.updateLoop` from the start to the exit, the heap used, the
words below the start heap that the loop keeps, the growth of the core footprints, and the cost
of every pass against the potentials of all cores.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- When the threshold test fires at level `idx`, the body loads the three words of the test and
stores `idx` in the end register `reg 99`. -/
theorem wireBranchBLoopBodyKFBL_runs_over {w idx table ucBase curBatch thr uc len : ℕ}
    (updCore readLSF dgApply copyProc updLen slotProc : ℕ) {p : Program} {ω : ℕ → Bool}
    {st : State} (hr10 : st.regs 10 = curBatch) (hLen : st.mem curBatch = len)
    (hr85 : st.regs 85 = ucBase) (hr96 : st.regs 96 = idx) (hr74 : st.regs 74 = table)
    (hUC : st.mem (ucBase + idx) = uc) (hTab : st.mem (table + idx) = thr)
    (hucW : ucBase + idx < 2 ^ w) (htW : table + idx < 2 ^ w) (hSumW : uc + len < 2 ^ w)
    (hOver : thr < uc + len) :
    ∃ sF : State,
      Runs w p ω (wireBranchBLoopBodyKFBL updCore readLSF dgApply copyProc updLen slotProc)
        st .normal sF 24 ∧
      sF.mem = st.mem ∧ (∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → sF.regs r = st.regs r) ∧
      sF.regs 99 = idx := by
  let sa := { st with regs := Function.update st.regs 16 len }
  let sb := { sa with regs := Function.update sa.regs 17 uc }
  let sc := { sb with regs := Function.update sb.regs 18 thr }
  let sd := { sc with regs := Function.update sc.regs 99 idx }
  have ra : Runs w p ω (.assign 16 (.load (.reg 10))) st .normal sa 3 :=
    runs_assign_iff.mpr ⟨len, by simp [Expr.eval, hr10, hLen], rfl, rfl, rfl⟩
  have rb : Runs w p ω (.assign 17 (.load (.bin .add (.reg 85) (.reg 96)))) sa .normal sb 5 :=
    runs_assign_iff.mpr ⟨uc, by simp [Expr.eval, BinOp.eval, sa, hr85, hr96, hucW, hUC],
      rfl, rfl, rfl⟩
  have rc : Runs w p ω (.assign 18 (.load (.bin .add (.reg 74) (.reg 96)))) sb .normal sc 5 :=
    runs_assign_iff.mpr ⟨thr, by simp [Expr.eval, BinOp.eval, sb, sa, hr74, hr96, htW, hTab],
      rfl, rfl, rfl⟩
  have rd : Runs w p ω (.assign 99 (.reg 96)) sc .normal sd 2 :=
    runs_assign_iff.mpr ⟨idx, by simp [Expr.eval, sc, sb, sa, hr96], rfl, rfl, rfl⟩
  refine ⟨sd, ?_, rfl, fun r h1 h2 h3 h4 => by
    simp [sd, sc, sb, sa, Function.update, h1, h2, h3, h4], by simp [sd]⟩
  have hw : 1 < 2 ^ w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; omega
    · exact Nat.one_lt_two_pow (by omega)
  exact runs_seq_iff.mpr (Or.inr ⟨sa, 3, 20, ra,
    runs_seq_iff.mpr (Or.inr ⟨sb, 5, 14, rb,
      runs_seq_iff.mpr (Or.inr ⟨sc, 5, 8, rc,
        runs_cond_iff.mpr ⟨1, 2,
          by simp [Expr.eval, BinOp.eval, sc, sb, sa, hSumW, hOver, hw],
          by simpa using rd, by simp [Expr.size]⟩, rfl⟩), rfl⟩), rfl⟩)

/-- The plain step of the update loop at level `idx < d` raises `totalRuntime` by at least the
change of tool cost at level `idx`, when the tool cost does not drop (`ToolCostMono`). -/
theorem updateLoopNext_totalRuntime_ge {cfg : Alg2Config} (hMono : ToolCostMono cfg.T)
    (ℓ' g' : ℕ → ℝ) {idx : ℕ} (hidx : idx < cfg.P.d) (ch : ChainState cfg.T cfg.P)
    (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    ch.totalRuntime + (cfg.T.cost ((updateLoopNext cfg ℓ' g' idx ch curG curU curEnc).scState idx) -
      cfg.T.cost (ch.scState idx)) ≤
      (updateLoopNext cfg ℓ' g' idx ch curG curU curEnc).totalRuntime := by
  set Cp : TreeChain := { ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j }
  set upd := cfg.T.updateOrd (ch.scState idx) curU (Cp.chainLen ℓ' idx) (Cp.chainGrad g' idx)
    (chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState ch.bran idx)
    with hupd
  have h := updateLoop_step_totalRuntime_eq ch hidx curG upd.1 curU (upd.2 (ch.bran idx)) curEnc
    ((ch.G (idx + 1)).batchEnc (upd.2 (ch.bran idx)))
    (diffTreeChanges (cfg.T.lsfs (ch.scState idx) (ch.bran idx)).F.F.E
      (cfg.T.lsfs upd.1 (ch.bran idx)).F.F.E).length (hMono.1 _ _ _ _ _)
  dsimp only at h
  have hT : (updateLoopNext cfg ℓ' g' idx ch curG curU curEnc).totalRuntime =
      ch.totalRuntime + (cfg.T.cost upd.1 - cfg.T.cost (ch.scState idx)) + curEnc +
        (if idx + 1 < cfg.P.d then (ch.G (idx + 1)).batchEnc (upd.2 (ch.bran idx)) else 0) := h
  have hS : (updateLoopNext cfg ℓ' g' idx ch curG curU curEnc).scState idx = upd.1 := by
    simp only [updateLoopNext, ↓reduceIte]; rfl
  rw [hT, hS]
  omega

set_option maxHeartbeats 4000000 in
/-- The run of the plain-step loop of Branch B from level `idx`, by induction on the number `rem`
of levels left. It stops at the level `i₀`: either `i₀ = d`, or the threshold test fires at
`i₀ < d`. If the test does not fire at the start level `idx < d`, then `idx < i₀`. At the exit it gives the invariant at `i₀` for the state `sE` at the top of the last
pass (the final state `sF` differs from `sE` only in `regs 16, 17, 18, 99`), the tie of
`Chain.Ordered.updateLoop`, the heap used, the frame below the start heap, the growth of the core
footprints and the cost of the passes. -/
theorem wireBranchBLoopKFBL_runs
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy wordExp stretchPrec N0 : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ}
    {BWc EWc ULc stepSpace : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (hRLLoc : RL.Local)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hStepSp : ∀ j < cfg.P.d, ∀ coreH gB bPtr bW ePtr eW lB h nU uL : ℕ, bW ≤ BWc j →
      eW ≤ EWc j → nU ≤ ULc (j + 1) → uL ≤ ULc j →
      3 * alloc 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
        nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) +
        uL + nU ≤ stepSpace j) :
    ∀ (rem idx : ℕ) (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEditsList : List OrdEdit) (curEnc : ℕ) (oldOrd : ℕ → List End) (st : State)
      (tok : ℕ → Rcore.τ) (curBatch curBatchWords curEdits curEditsWords : ℕ)
      (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists),
      idx + rem = cfg.P.d →
      BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
        (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
        EWc ULc ch0 termTok idx ch curG curU curEditsList oldOrd st tok curBatch curBatchWords
        curEdits curEditsWords levelU levelUS D →
      UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
        ℓ' g' rem idx ch curG curU curEnc oldOrd →
      UpdateLoopSizeInv cfg ℓ' g' edMul
        (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) BWc EWc ULc rem
        idx ch curG curU curEnc →
      st.regs 4 + (Finset.Ico idx cfg.P.d).sum stepSpace < 2 ^ w →
      ∃ (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P) (curGE : MGraph)
        (curUE : List Update) (curEditsE : List OrdEdit) (curEncE : ℕ)
        (oldOrdE : ℕ → List End) (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ)
        (levelUE levelUSE : ℕ → List Update) (DE : ℕ → LevelDiffLists),
        Runs w p ω (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
          st .normal sF cost ∧
        idx ≤ i₀ ∧ i₀ ≤ cfg.P.d ∧
        (¬ (intRebuildThreshold cfg.P N0 idx < ch.updCount idx + curU.length) →
          idx < cfg.P.d → idx < i₀) ∧
        BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
          (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
          EWc ULc ch0 termTok i₀ chE curGE curUE curEditsE oldOrdE sE tokE bE bWE eE eWE levelUE
          levelUSE DE ∧
        UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
          ℓ' g' (cfg.P.d - i₀) i₀ chE curGE curUE curEncE oldOrdE ∧
        (i₀ < cfg.P.d → intRebuildThreshold cfg.P N0 i₀ < chE.updCount i₀ + curUE.length) ∧
        (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' rem idx ch curG curU
            curEnc).1 =
          (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' (cfg.P.d - i₀) i₀ chE
            curGE curUE curEncE).1 ∧
        sF.mem = sE.mem ∧
        (∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → sF.regs r = sE.regs r) ∧ sF.regs 99 = i₀ ∧
        st.regs 4 ≤ sE.regs 4 ∧ sE.regs 4 ≤ st.regs 4 + (Finset.Ico idx i₀).sum stepSpace ∧
        (∀ j < idx, chE.scState j = ch.scState j ∧ levelUSE j = levelUS j ∧ DE j = D j) ∧
        (∀ a < st.regs 4, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
          (∀ j < cfg.P.d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
            (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) →
          (∀ j < cfg.P.d, a ≠ A.ucBase + j) →
          (a < A.selBase ∨ A.selBase + 1 + 12 * cfg.P.d ≤ a) → sF.mem a = st.mem a) ∧
        (∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tokE j) a →
          Rcore.foot (A.coreH j) (tok j) a ∨ (st.regs 4 ≤ a ∧ a < sE.regs 4)) ∧
        cost + branchBPhiSum Rcore A tokE sE.mem ≤
          (Finset.Ico idx i₀).sum (fun j =>
            branchBStepCostKFBL L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀ (BWc j)
              (EWc j) (cfg.T.cost (chE.scState j) - cfg.T.cost (ch0.scState j))
              (levelUSE j).length (DE j).fDel.length (DE j).reemb.length + 4) + 32 +
          branchBPhiSum Rcore A tok st.mem ∧
        (∀ j, idx ≤ j → j < i₀ →
          cfg.T.cost (chE.scState j) - cfg.T.cost (ch.scState j) =
            (branchBStepData cfg ℓ' g' rem idx ch curG curU curEnc j).2.1 ∧
          (levelUSE j).length = (branchBStepData cfg ℓ' g' rem idx ch curG curU curEnc j).2.2) ∧
        (ToolCostMono cfg.T → ch.totalRuntime +
          (Finset.Ico idx i₀).sum (fun j => cfg.T.cost (chE.scState j) - cfg.T.cost (ch.scState j)) ≤
          chE.totalRuntime) := by
  have hw0 : w ≠ 0 := by intro h; have := E.w16; subst h; omega
  intro rem
  induction rem with
  | zero =>
    intro idx ch curG curU curEditsList curEnc oldOrd st tok curBatch curBatchWords curEdits
      curEditsWords levelU levelUS D hSum I hM hSz hRoom
    have hIdx : idx = cfg.P.d := by omega
    have hr96 := I.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hr99 := I.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hd0 : cfg.P.d - idx = 0 := by omega
    refine ⟨idx, st, st, 4, ch, curG, curU, curEditsList, curEnc, oldOrd, tok, curBatch,
      curBatchWords, curEdits, curEditsWords, levelU, levelUS, D,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr96, hr99, hIdx], rfl, rfl,
        rfl⟩), le_rfl, by omega, fun _ h => by omega, I, by rw [hd0]; exact hM,
      fun h => by omega,
      by rw [hd0], rfl, fun _ _ _ _ _ => rfl, by rw [hr99, hIdx], le_rfl, by simp,
      fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ _ => rfl, fun _ _ _ ha => Or.inl ha, by simp,
      fun j h1 h2 => absurd h2 (by omega), fun _ => by simp⟩
  | succ rem ih =>
    intro idx ch curG curU curEditsList curEnc oldOrd st tok curBatch curBatchWords curEdits
      curEditsWords levelU levelUS D hSum I hM hSz hRoom
    have hIdxLt : idx < cfg.P.d := by omega
    obtain ⟨hFloor, hr10, _, _, _, _, _, hr74, _, _, _, _, _, _, hr85, _, _, _, hr96, _, _,
      hr99⟩ := I.regs
    have hIco : ∀ (f : ℕ → ℕ) (k : ℕ), idx < k →
        (Finset.Ico idx k).sum f = f idx + (Finset.Ico (idx + 1) k).sum f := fun f k hk => by
      have h1 : Finset.Ico idx k = insert idx (Finset.Ico (idx + 1) k) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
    have hUCW : ch.updCount idx + curU.length < 2 ^ w := hM.1
    by_cases hOver : intRebuildThreshold cfg.P N0 idx < ch.updCount idx + curU.length
    · -- the threshold test fires: the body stores `idx` in `reg 99` and the loop stops
      have hucLt := S.ucLt
      have htabLt := S.tableLt
      obtain ⟨sF, rBody, hsFmem, hsFregs, hsF99⟩ :=
        wireBranchBLoopBodyKFBL_runs_over (opCore 0) (opCore 2) dgApply copyProc updLen slotProc
          (p := p) (ω := ω) hr10 I.batchLen hr85 hr96 hr74 (I.cells idx hIdxLt).2.2.2.2.2.2.2.2.1
          (I.cells idx hIdxLt).1 (by omega) (by omega) hUCW hOver
      have hsF96 : sF.regs 96 = idx := (hsFregs 96 (by decide) (by decide) (by decide)
        (by decide)).trans hr96
      have rLoop : Runs w p ω
          (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
          st .normal sF (3 + 24 + 4 + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, sF, 24, 4,
          by simp [Expr.eval, BinOp.eval, hr96, hr99, hIdxLt, hw0], by decide, rBody,
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hsF96, hsF99], rfl, rfl,
            rfl⟩), rfl⟩))
      have hd1 : cfg.P.d - idx = rem + 1 := by omega
      refine ⟨idx, st, sF, _, ch, curG, curU, curEditsList, curEnc, oldOrd, tok, curBatch,
        curBatchWords, curEdits, curEditsWords, levelU, levelUS, D, rLoop, le_rfl, by omega,
        fun h _ => absurd hOver h, I, by rw [hd1]; exact hM, fun _ => hOver, by rw [hd1], hsFmem, hsFregs, hsF99, le_rfl,
        by simp, fun _ _ => ⟨rfl, rfl, rfl⟩, fun a _ _ _ _ _ => by rw [hsFmem],
        fun _ _ _ ha => Or.inl ha, ?_, fun j h1 h2 => absurd h2 (by omega), fun _ => by simp⟩
      have : branchBPhiSum Rcore A tok st.mem = branchBPhiSum Rcore A tok st.mem := rfl
      simp
    · -- a plain pass, then the rest of the loop from `idx + 1`
      have hRoom1 : st.regs 4 + stepSpace idx < 2 ^ w := by
        rw [hIco stepSpace cfg.P.d hIdxLt] at hRoom; omega
      obtain ⟨out, cB, tok1, nextEdits, c, rBody, hSpace, hOut⟩ :=
        wireBranchBLoopBodyKFBL_runs_plain (ω := ω) E S hSlotLe hN0 hLvlM
          (by omega : idx + (rem + 1) = cfg.P.d) I hM hSz hOver (hStepSp idx hIdxLt) hRoom1
      obtain ⟨I', hM', hSz', hc'⟩ :=
        branchBLoopInvKFBL_pass E.loc hRLLoc S hSlotLe (by omega : idx + (rem + 1) = cfg.P.d) I
          hM hSz hOver hOut
      have hOut' := hOut
      unfold BranchBPassOutKFBL at hOut'
      obtain ⟨hLo, _, _, hReg70, _, hFoot1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hFr, _⟩ := hOut'
      have h4 : Function.update out.regs 96 (idx + 1) 4 = out.regs 4 :=
        Function.update_of_ne (by decide) _ _
      have hRoom' : ({ out with regs := Function.update out.regs 96 (idx + 1) } : State).regs 4 +
          (Finset.Ico (idx + 1) cfg.P.d).sum stepSpace < 2 ^ w := by
        show Function.update out.regs 96 (idx + 1) 4 + _ < _
        rw [h4]
        rw [hIco stepSpace cfg.P.d hIdxLt] at hRoom
        omega
      obtain ⟨i₀, sE, sF, cR, chE, curGE, curUE, curEditsE, curEncE, oldOrdE, tokE, bE, bWE, eE,
          eWE, levelUE, levelUSE, DE, rRest, hi1, hi2, _, IE, hME, hOverE, hUpdE, hsFmem, hsFregs,
          hsF99, hsE4lo, hsE4hi, hFrameE, hFrE, hFootE, hcE, hDataE, hRtE⟩ :=
        ih (idx + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) I' hM' hSz' hRoom'
      change Function.update out.regs 96 (idx + 1) 4 ≤ sE.regs 4 at hsE4lo
      change sE.regs 4 ≤ Function.update out.regs 96 (idx + 1) 4 + _ at hsE4hi
      rw [h4] at hsE4lo hsE4hi
      have rLoop : Runs w p ω
          (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
          st .normal sF (3 + cB + cR + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, cB, cR,
          by simp [Expr.eval, BinOp.eval, hr96, hr99, hIdxLt, hw0], by decide, rBody, rRest,
          rfl⟩))
      have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
      have hUpd : (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' (rem + 1) idx ch
          curG curU curEnc).1 =
          (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' rem (idx + 1)
            (updateLoopNext cfg ℓ' g' idx ch curG curU curEnc)
            (cfg.T.S (cfg.T.updateOrd (ch.scState idx) curU
              (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
                TreeChain).chainLen ℓ' idx)
              (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
                TreeChain).chainGrad g' idx)
              (chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState
                ch.bran idx)).1 (ch.bran idx))
            ((cfg.T.updateOrd (ch.scState idx) curU
              (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
                TreeChain).chainLen ℓ' idx)
              (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
                TreeChain).chainGrad g' idx)
              (chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState
                ch.bran idx)).2 (ch.bran idx)) 0).1 := by
        simp only [Chain.Ordered.updateLoop, hOver, ↓reduceIte]
        rfl
      have hFr0 := hFrameE idx (by omega)
      refine ⟨i₀, sE, sF, _, chE, curGE, curUE, curEditsE, curEncE, oldOrdE, tokE, bE, bWE, eE,
        eWE, levelUE, levelUSE, DE, rLoop, by omega, hi2, fun _ _ => by omega, IE, hME, hOverE,
        hUpd.trans hUpdE,
        hsFmem, hsFregs, hsF99, by omega, ?_, fun j hj => ?_, fun a ha h0 hgl hu hs => ?_,
        fun j hj a ha => ?_, ?_, fun j hj1 hj2 => ?_, fun hMono => ?_⟩
      · rw [hIco stepSpace i₀ (by omega)]; omega
      · obtain ⟨e1, e2, e3⟩ := hFrameE j (by omega)
        refine ⟨e1.trans (ite_eq_right (show j ≠ idx by omega)), e2.trans
          (ite_eq_right (show j ≠ idx by omega)), e3.trans (ite_eq_right (show j ≠ idx by omega))⟩
      · have hst : out.mem a = st.mem a :=
          hFr a ha (h0 idx hIdxLt) (hgl idx hIdxLt).1 (hu idx hIdxLt)
            (fun hlt => (hgl (idx + 1) hlt).2) (by omega)
        have ha' : a < Function.update out.regs 96 (idx + 1) 4 := by rw [h4]; omega
        refine (hFrE a ha' (fun j hj hf => ?_) hgl hu hs).trans hst
        by_cases hje : j = idx
        · simp only [hje, ↓reduceIte] at hf
          rcases hFoot1 a hf with h' | h'
          · exact h0 idx hIdxLt h'
          · omega
        · simp only [hje, ↓reduceIte] at hf
          exact h0 j hj hf
      · rcases hFootE j hj a ha with h' | h'
        · by_cases hje : j = idx
          · simp only [hje, ↓reduceIte] at h'
            rcases hFoot1 a h' with h'' | h''
            · rw [hje]; exact Or.inl h''
            · exact Or.inr ⟨h''.1, by omega⟩
          · simp only [hje, ↓reduceIte] at h'
            exact Or.inl h'
        · have h1 := h'.1
          change Function.update out.regs 96 (idx + 1) 4 ≤ a at h1
          rw [h4] at h1
          exact Or.inr ⟨by omega, h'.2⟩
      · obtain ⟨e1, e2, e3⟩ := hFr0
        rw [hIco _ i₀ (by omega), e1, e2, e3]
        simp only [↓reduceIte] at hc' hcE ⊢
        omega
      · -- the data of the steps: level `idx` is this pass, the levels above come from the rest
        have hD : ∀ j', j' ≠ idx →
            branchBStepData cfg ℓ' g' (rem + 1) idx ch curG curU curEnc j' =
              branchBStepData cfg ℓ' g' rem (idx + 1)
                (updateLoopNext cfg ℓ' g' idx ch curG curU curEnc) _ _ 0 j' := fun j' hj' => by
          simp only [branchBStepData, hN, hOver, ↓reduceIte, hj']
          rfl
        obtain ⟨e1, e2, e3⟩ := hFrameE idx (by omega)
        by_cases hjI : j = idx
        · subst hjI
          simp only [branchBStepData, hN, hOver, ↓reduceIte, branchBStepNext]
          refine ⟨?_, ?_⟩
          · rw [e1]; simp only [updateLoopNext, ↓reduceIte]
          · rw [e2]; simp only [↓reduceIte]
        · obtain ⟨d1, d2⟩ := hDataE j (by omega) hj2
          rw [hD j hjI]
          have hScj : (updateLoopNext cfg ℓ' g' idx ch curG curU curEnc).scState j = ch.scState j :=
            by simp only [updateLoopNext, hjI, ↓reduceIte]
          rw [hScj] at d1
          exact ⟨d1, d2⟩
      · -- the runtime grows by the change of tool cost at each plain level
        have hR := hRtE hMono
        obtain ⟨e1, _, _⟩ := hFrameE idx (by omega)
        have hNextRt := updateLoopNext_totalRuntime_ge hMono ℓ' g' hIdxLt ch curG curU curEnc
        rw [← e1] at hNextRt
        have hSumEq : (Finset.Ico (idx + 1) i₀).sum (fun j =>
              cfg.T.cost (chE.scState j) -
                cfg.T.cost ((updateLoopNext cfg ℓ' g' idx ch curG curU curEnc).scState j)) =
            (Finset.Ico (idx + 1) i₀).sum (fun j =>
              cfg.T.cost (chE.scState j) - cfg.T.cost (ch.scState j)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjne : j ≠ idx := by have := (Finset.mem_Ico.mp hj).1; omega
          simp only [updateLoopNext, hjne, ↓reduceIte]
        rw [hSumEq] at hR
        rw [hIco _ i₀ (by omega)]
        omega
end MinCostFlow.MinRatio
