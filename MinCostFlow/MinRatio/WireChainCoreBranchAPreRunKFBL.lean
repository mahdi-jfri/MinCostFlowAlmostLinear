module

public import MinCostFlow.MinRatio.WireChainCoreBranchAPre
public import MinCostFlow.MinRatio.WireShiftDeepCollectKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# Branch A Steps 0–2 execution under `KFBL` (`WireChainCoreBranchAPreRunKFBL`)

Provides:
1. `branchA_modelPre_chain_eq`: identifies `modelPre.chain` with `algorithm1_rebuild` from level `0`
   on `G0'.compact` and proves `level0Rebuilt = true`.
2. `wireBranchASteps0To2StmtKFBL` and `wireBranchASteps0To2KFBL_runs`: executes Branch A Steps 0–2
   after `updateCoreInitRegsKFBL`:
   - Step 0: writes `firstReb = 0` at `mem[selOut]` (`reg 72`).
   - Step 1: collects old active LSF forest pointers `0 .. d` directly into `oldPtrs` (`reg 80`)
     via `collectLSFForestsLoopKFBL_runs` + `collectTermForestStmt_runs`.
   - Step 2: runs `wireBranchASync1AndPrepStmt` (`oldF → ∅`, zero `slots`, refresh accounts,
     update `rootGraph` to `G0'`, update `levelMeta[0]` to `ℓ'`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Branch A Steps 0–2 statement: store `firstReb = 0`, collect old forests `0 .. d`, and run
Sync 1 + account refresh + level-0 graph/length updates. -/
@[expose] def wireBranchASteps0To2StmtKFBL
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc readLSF : ℕ) : Stmt :=
  .store (.reg 72) (.const 0) ;;
  .assign 20 (.const 0) ;;
  collectLSFForestsLoop readLSF 80 ;;
  collectTermForestStmt 80 ;;
  wireBranchASync1AndPrepStmt packEditsProc readTree cutTree linkTree bind canonCopy isNeg
    refreshAccountsProc dgApply updateLen0Proc

theorem wireBranchASteps0To2StmtKFBL_noRand
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc readLSF : ℕ) :
    (wireBranchASteps0To2StmtKFBL packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc readLSF).NoRand := by
  simp [wireBranchASteps0To2StmtKFBL, collectLSFForestsLoop_noRand, collectTermForestStmt_noRand,
    wireBranchASync1AndPrepStmt_noRand, Stmt.NoRand]

/-- Branch A model identity: when `intRebuildThreshold 0 < updCount 0 + U_int.length`,
`modelPre.chain` equals `algorithm1_rebuild` from level `0` on `G0'.compact`, and
`level0Rebuilt = true`. -/
theorem branchA_modelPre_chain_eq {cfg : Alg2Config} (model : Alg2State cfg) (U : List Update)
    (gVec lVec : ℕ → ℝ)
    (hdPos : 0 < cfg.P.d)
    (hN0 : model.chain.N₀ = cfg.N₀)
    (hOver :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch U_int
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let g' := fun e' => gVec (tr.2.2.1 e')
    let st0 : ChainState cfg.T cfg.P :=
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    let stLG : ChainState cfg.T cfg.P :=
      { st0 with
        ℓ := fun j => ℓ' (compactUnrank G0'.E j)
        g := fun j => g' (compactUnrank G0'.E j) }
    let modelPre := alg2PreResetState cfg model U gVec lVec
    modelPre.chain =
      (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 G0'.compact (G0.batchEnc U_int)).1 ∧
    Chain.Ordered.level0Rebuilt cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount = true := by
  dsimp only
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  let ℓ' := fun e' => lVec (tr.2.2.1 e')
  let g' := fun e' => gVec (tr.2.2.1 e')
  let st0 : ChainState cfg.T cfg.P :=
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
  let stLG : ChainState cfg.T cfg.P :=
    { st0 with
      ℓ := fun j => ℓ' (compactUnrank G0'.E j)
      g := fun j => g' (compactUnrank G0'.E j) }
  have hdEq : cfg.P.d = (cfg.P.d - 1) + 1 := by omega
  have hOver' : intRebuildThreshold cfg.P cfg.N₀ 0 <
      model.chain.updCount 0 +
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length := by
    simpa [hN0] using hOver
  have hChEq : (alg2PreResetState cfg model U gVec lVec).chain =
      (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 G0'.compact (G0.batchEnc U_int)).1 := by
    unfold alg2PreResetState Chain.Ordered.algorithm1_update
    dsimp only
    rw [hdEq]
    dsimp only [Chain.Ordered.updateLoop]
    simp only [hOver', ↓reduceIte]
    rfl
  refine ⟨hChEq, ?_⟩
  unfold alg2PreResetState
  dsimp only
  rw [Chain.Ordered.level0Rebuilt_update_iff]
  simp [hOver']

private theorem branchA02_cost_arith {c01 cSync phiT1 d ro sumOld syncC ic uL refC L
    phiT0 offD phiC0 : ℕ}
    (h1 : c01 ≤ d * (ro + 48) + 68 + phiC0)
    (h3 : cSync + phiT1 ≤ (230 * (d + 1) + 85 * sumOld + 300) + sumOld * (syncC + 2) +
      (15 * ic + 30) + (uL * (refC + 120) + 71 * L + 210) +
      (670 * (4 * uL + 1) + 30) + (uL * (17 * L + 70) + 80) + (phiT0 + offD)) :
    c01 + cSync + 1 + phiT1 ≤
      d * (ro + 48) + (230 * (d + 1) + 85 * sumOld + 300) + sumOld * (syncC + 2) +
      (15 * ic + 30) + (uL * (refC + 120) + 71 * L + 210) +
      (670 * (4 * uL + 1) + 30) + (uL * (17 * L + 70) + 80) + 70 +
      (phiT0 + offD + phiC0) := by
  omega

/-- Execute Branch A Steps 0–1 (store `0` at `mem[heap]`, collect old active LSF forest pointers
`0 .. d` into `arrBase .. arrBase + d`) in a clean context without `translateBatch` / `alg2PreResetState`. -/
private theorem branchA_steps01_runs
    {w L P m V psi k epsExp drainUnit capExp vCap eCap initCore root uIntBuf heap : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hCoreLocal : Rcore.Local)
    (hdPos : 0 < cfg.P.d) (hdW : cfg.P.d < 2 ^ w) (hkW : cfg.P.k < 2 ^ w) (hw18 : 18 < 2 ^ w)
    (hCoreImpl : UpdateCoreCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hSFL0 : ShiftLoopLevelFacts cfg model.chain)
    (hBrLt0 : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hLastBrLt0 : model.chain.lastBran < model.chain.lastK)
    (hOrdIn0 : ∀ j < cfg.P.d,
      SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM j) model.chain.N₀
        (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j) (model.chain.updCount j))
    (hFSub0 : ∀ j < cfg.P.d, (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆ (model.chain.G 0).E)
    (hLastFSub0 : (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆ (model.chain.G 0).E)
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < uIntBuf)
    (hULeHeap : uIntBuf ≤ heap)
    (hStMem : st.mem = mem) (hz0 : ZeroFrom mem heap)
    (hRegs :
      let d := cfg.P.d
      let cnt := d + 1
      let arrBase := heap + 1 + 12 * d
      let handleBase := tok.handle + 18
      let branchBase := handleBase + cnt
      let levelMeta := solverLevelMetaAddr tok.table d
      st.regs 4 = arrBase + 3 * cnt + 4 ∧ st.regs 71 = 0 ∧ st.regs 72 = heap ∧
      st.regs 75 = d ∧ st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧
      st.regs 80 = arrBase ∧ st.regs 83 = levelMeta)
    (hHS5Lt : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 5 * cfg.P.d < 2 ^ w) :
    let d := cfg.P.d
    let cnt := d + 1
    let arrBase := heap + 1 + 12 * d
    let emptyGraphPtr := arrBase + 3 * cnt
    let heapStart := arrBase + 3 * cnt + 4
    ∃ (s1 : State) (c01 heap1 : ℕ),
      Runs w p ω
        (.store (.reg 72) (.const 0) ;; .assign 20 (.const 0) ;;
          collectLSFForestsLoop (opCore 2) 80 ;; collectTermForestStmt 80)
        st .normal s1 c01 ∧
      s1.regs 4 = heap1 ∧ heapStart ≤ heap1 ∧ heap1 ≤ heapStart + 5 * d ∧
      ZeroFrom s1.mem heap1 ∧
      (∀ r, 70 ≤ r → s1.regs r = st.regs r) ∧
      (∀ j < 4, s1.mem (emptyGraphPtr + j) = 0) ∧
      (∀ (j : ℕ) (hj : j < cfg.P.d + 1), ∃ vc ec,
        DynGraphAt s1.mem (s1.mem (arrBase + j)) vc ec
          ((chainSuffixForests model.chain 0)[j]'(by rw [chainSuffixForests_length]; omega)) ∧
        (s1.mem (arrBase + j) + dynGraphSize vc ec ≤ arrBase ∨ heapStart ≤ s1.mem (arrBase + j)) ∧
        s1.mem (arrBase + j) + dynGraphSize vc ec ≤ heap1 ∧
        ∀ e ∈ ((chainSuffixForests model.chain 0)[j]'(by rw [chainSuffixForests_length]; omega)).E,
          e < tok.intCap) ∧
      (∀ a < arrBase, (∀ j < d, ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
        s1.mem a = mem a) ∧
      c01 ≤ d * (Psc.readout + 48) + 68 +
        (Finset.range d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
  dsimp only
  dsimp only at hRegs
  obtain ⟨hr4, hr71, hr72, hr75, hr77, hr78, hr80, hr83⟩ := hRegs
  have hMeta0_keep := hMeta0
  have hM0_le_m : (model.chain.G 0).m ≤ m := by
    obtain ⟨_, _, _, _, hFresh0, _, hExtM0, _⟩ := hRep0
    rw [hFresh0.m_eq]
    exact (Finset.card_le_card fun e he => Finset.mem_range.mpr (hExtM0 e he)).trans_eq
      (Finset.card_range m)
  obtain ⟨_, _, _, _, _, _, _, ⟨hG0Cap, _, _, _⟩, _, _, _, _, _, _, hCores0, hTermH0, hTermB0,
    hTermRep0, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, hT19, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, _, hTagMeta0, _⟩ := hMeta0
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hCapsMeta0 := fun j hj => SolverLevelMetaAt.atCaps hMeta0_keep hCaps0 j hj
  have hMemEqOfTag {a : ℕ} (ht : tok.tag a ≠ 0) (h6 : tok.tag a ≠ 6) (h7 : tok.tag a ≠ 7)
      (h8 : tok.tag a ≠ 8) : mem a = mem0 a := hMemEq a (htagLt ht) h6 h7 h8
  let s0 : State := { st with mem := Function.update st.mem heap 0 }
  have r0 : Runs w p ω (.store (.reg 72) (.const 0)) st .normal s0 3 :=
    runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, hr72],
      by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hs0_mem : s0.mem = mem := by
    ext a
    by_cases ha : a = heap
    · subst ha; simpa [s0] using (hz0 a le_rfl).symm
    · simp [s0, Function.update_of_ne ha, hStMem]
  let s0a : State := { s0 with regs := Function.update s0.regs 20 0 }
  have r0a : Runs w p ω (.assign 20 (.const 0)) s0 .normal s0a 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hs0a_r4 : s0a.regs 4 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 := by
    simp [s0a, s0, hr4]
  obtain ⟨s1a, cColOld, coreTok1, rColOld, hs1a_lo, hs1a_hi, hz1a, hCores1a, _,
      hOldForests1a, hs1a_fr, hs1a_regs, hcColOld⟩ :=
    collectLSFForestsLoopKFBL_runs (w := w) (L := L) (depth := Expander.chosenL (cfg.P.M₀ ^ 2))
      (vCap := vCap) (eCap := eCap) (capExp := capExp) (first := 0) (baseIdx := 0) (dstReg := 80)
      (dstPtrs := heap + 1 + 12 * cfg.P.d) (handleBase := tok.handle + 18)
      (branchBase := tok.handle + 18 + (cfg.P.d + 1))
      (levelMeta := solverLevelMetaAddr tok.table cfg.P.d) (p := p) (ω := ω) (st := s0a)
      model.chain tok.coreHandle tok.coreTok
      hCoreLocal (by decide) le_rfl (Nat.zero_le _) (by simp [s0a]) (by simp [s0a, s0, hr71])
      (by simp [s0a, s0, hr75]) (by simp [s0a, s0, hr77]) (by simp [s0a, s0, hr78])
      (by simp [s0a, s0, hr83]) (by simp [s0a, s0, hr80]) hkW hdW (by omega)
      (by have := htagLt (by rw [hTagMeta0 (2 * cfg.P.d - 1) (by omega)]; omega); rw [hs0a_r4]; omega)
      (by have := htagLt (by rw [hT4 (cfg.P.d - 1) (by omega)]; decide); rw [hs0a_r4]; omega)
      (by have := htagLt (by rw [hT4 ((cfg.P.d + 1) + cfg.P.d - 1) (by omega)]; decide); rw [hs0a_r4]; omega)
      (by rw [hs0a_r4]; omega) (by rw [hs0a_r4]; exact hHS5Lt)
      (fun a ha => by rw [show s0a.mem = mem from hs0_mem]; rw [hs0a_r4] at ha; exact hz0 a (by omega))
      (fun j _ hj => by
        rw [hSFL0.2.1, hSFL0.2.2.1]
        exact (hCoreImpl j hj (model.chain.G j) (hSFL0.1 j (le_of_lt hj))
          ((hSFL0.2.2.2 j (le_of_lt hj)).trans hM0_le_m)).2)
      (fun j _ hj => by
        obtain ⟨hDGj, _, _, _, hTagGj⟩ := hCapsMeta0 j hj
        have hTagH : tok.tag (tok.handle + 18 + j) = 4 := hT4 j (by omega)
        have hTagB : tok.tag (tok.handle + 18 + (cfg.P.d + 1) + j) = 4 := by
          have := hT4 (cfg.P.d + 1 + j) (by omega); simpa [Nat.add_assoc] using this
        have hTagM : tok.tag (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
          have := hTagMeta0 (cfg.P.d + j) (by omega); simpa [Nat.add_assoc] using this
        have hCoreFootLt : ∀ a, Rcore.foot (tok.coreHandle j) (tok.coreTok j) a → a < uIntBuf :=
          fun a ha => htagLt (by rw [hT21 j hj a ha]; omega)
        have hCoreRepM : Rcore.rep (tok.coreHandle j) (chainLevelOrdAbs model.chain j) (tok.coreTok j) mem :=
          (hCoreLocal _ _ _ mem0 mem (fun a ha => (hMemEqOfTag (by rw [hT21 j hj a ha]; omega)
            (by rw [hT21 j hj a ha]; omega) (by rw [hT21 j hj a ha]; omega)
            (by rw [hT21 j hj a ha]; omega)).symm)).1 (hCores0 j hj).2.2
        have hMemM : mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
            mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) :=
          hMemEqOfTag (by rw [hTagM]; omega) (by rw [hTagM]; omega)
            (by rw [hTagM]; omega) (by rw [hTagM]; omega)
        have hDGjM : DynGraphAt mem (mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)) vCap eCap (model.chain.G j) :=
          dynGraphAt_of_agree hDGj (fun a ha1 ha2 => by
            have ht := hTagGj a ha1 ha2
            exact hMemEqOfTag (by rw [ht]; split_ifs <;> omega) (by rw [ht]; split_ifs <;> omega)
              (by rw [ht]; split_ifs <;> omega) (by rw [ht]; split_ifs <;> omega))
        have hDGjEnd : mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤ uIntBuf := by
          have h4 : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
          have ht := hTagGj (mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap - 1)
            (by omega) (by omega)
          have hlt := htagLt (by rw [ht]; split_ifs <;> omega); omega
        rw [show s0a.mem = mem from hs0_mem, hs0a_r4]
        refine ⟨(hMemEqOfTag (by rw [hTagH]; decide) (by rw [hTagH]; decide) (by rw [hTagH]; decide)
            (by rw [hTagH]; decide)).trans (hCores0 j hj).1,
          (hMemEqOfTag (by rw [hTagB]; decide) (by rw [hTagB]; decide) (by rw [hTagB]; decide)
            (by rw [hTagB]; decide)).trans (hCores0 j hj).2.1,
          hBrLt0 j hj,
          by have := hFootLt _ (Or.inl (hMeta0_keep.2.1 j hj)); omega,
          hCoreRepM, hOrdIn0 j hj,
          fun a ha => by have := hCoreFootLt a ha; omega,
          fun r _ hr => ⟨fun hf => by have := hT21 r hr _ hf; rw [hTagH] at this; omega,
            fun hf => by have := hT21 r hr _ hf; rw [hTagB] at this; omega,
            fun hf => by have := hT21 r hr _ hf; rw [hTagM] at this; omega⟩,
          Or.inl (by have := htagLt (by rw [hTagH]; decide); omega),
          Or.inl (by have := htagLt (by rw [hTagB]; decide); omega),
          Or.inl (by have := htagLt (by rw [hTagM]; omega); omega),
          fun t _ _ hf => by have := hCoreFootLt _ hf; omega,
          hMemM.symm ▸ hDGjM, by rw [hMemM]; omega,
          fun a ha1 ha2 => by
            rw [hMemM] at ha1 ha2
            have ht := hTagGj a ha1 ha2
            exact ⟨fun r _ hr hf => by have := hT21 r hr a hf; rw [ht] at this; split_ifs at this <;> omega,
              Or.inl (by have := htagLt (by rw [ht]; split_ifs <;> omega); omega)⟩⟩)
      (fun j₁ j₂ _ h1 _ h2 hne a ha1 ha2 => by
        have ht1 := hT21 j₁ h1 a ha1; have ht2 := hT21 j₂ h2 a ha2; omega)
  obtain ⟨_, _, _, hTBr0⟩ := hTermRep0
  obtain ⟨hTBrHdr0, hTLSF0⟩ := hTBr0 model.chain.lastBran hLastBrLt0
  let termLsfHdr0 := mem0 (tok.termHandle + 1 + model.chain.lastBran)
  let termFPtr0 := mem0 (termLsfHdr0 + 1)
  have hTermFootLt0 : ∀ a, (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a → a < uIntBuf :=
    fun a ha => htagLt (by rw [hT19 a ha]; decide)
  have hs1a_eq_mem0 {a : ℕ} (ht : tok.tag a ≠ 0) (h6 : tok.tag a ≠ 6) (h7 : tok.tag a ≠ 7)
      (h8 : tok.tag a ≠ 8) (hc : ∀ j < cfg.P.d, tok.tag a ≠ 21 + j) : s1a.mem a = mem0 a := by
    have hlt := htagLt ht
    refine (hs1a_fr a (by rw [hs0a_r4]; omega) (fun j _ hj hf => hc j hj (hT21 j hj a hf))
      (Or.inl (by omega))).trans ?_
    rw [show s0a.mem = mem from hs0_mem]
    exact hMemEq a hlt h6 h7 h8
  have hTermH1a : s1a.mem (tok.handle + 18 + cfg.P.d) = tok.termHandle :=
    (hs1a_eq_mem0 (by rw [hT4 cfg.P.d (by omega)]; decide) (by rw [hT4 cfg.P.d (by omega)]; decide)
      (by rw [hT4 cfg.P.d (by omega)]; decide) (by rw [hT4 cfg.P.d (by omega)]; decide)
      (fun _ _ => by rw [hT4 cfg.P.d (by omega)]; omega)).trans hTermH0
  have hTermB1a : s1a.mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) = model.chain.lastBran := by
    have ht : tok.tag (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) = 4 := by
      have := hT4 (cfg.P.d + 1 + cfg.P.d) (by omega); simpa [Nat.add_assoc] using this
    exact (hs1a_eq_mem0 (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) (fun _ _ => by rw [ht]; omega)).trans hTermB0
  have hTermLsf1a : s1a.mem (tok.termHandle + 1 + model.chain.lastBran) = termLsfHdr0 := by
    have ht : tok.tag (tok.termHandle + 1 + model.chain.lastBran) = 19 :=
      hT19 _ ⟨by omega, by have := hTBrHdr0.1; omega⟩
    exact hs1a_eq_mem0 (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) (fun _ _ => by rw [ht]; omega)
  have hTermFPtr1a : s1a.mem (termLsfHdr0 + 1) = termFPtr0 := by
    have ht : tok.tag (termLsfHdr0 + 1) = 19 :=
      hT19 _ ⟨by have := hTBrHdr0.1; omega, by have := hTBrHdr0.2.1; omega⟩
    exact hs1a_eq_mem0 (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) (fun _ _ => by rw [ht]; omega)
  obtain ⟨s1, cTermOld, rTermOld, hcTermOld, hs1Mem, hs1Regs⟩ :=
    collectTermForestStmt_runs (w := w) (dstReg := 80) (dstPtrs := heap + 1 + 12 * cfg.P.d)
      (baseIdx := 0) (d := cfg.P.d) (handleBase := tok.handle + 18)
      (branchBase := tok.handle + 18 + (cfg.P.d + 1)) (termHandle := tok.termHandle)
      (lastBran := model.chain.lastBran) (lsfHdr := termLsfHdr0) (forestPtr := termFPtr0)
      (p := p) (ω := ω) (st := s1a)
      ((hs1a_regs 80 (Or.inl (by decide))).trans (by simp [s0a, s0, hr80]))
      ((hs1a_regs 71 (Or.inl (by decide))).trans (by simp [s0a, s0, hr71]))
      ((hs1a_regs 75 (Or.inl (by decide))).trans (by simp [s0a, s0, hr75]))
      ((hs1a_regs 77 (Or.inl (by decide))).trans (by simp [s0a, s0, hr77]))
      ((hs1a_regs 78 (Or.inl (by decide))).trans (by simp [s0a, s0, hr78]))
      (by decide) (Nat.zero_le _) hTermH1a hTermB1a hTermLsf1a hTermFPtr1a
      (by have := htagLt (by rw [hT4 cfg.P.d (by omega)]; decide); omega)
      (by have := htagLt (by rw [hT4 (cfg.P.d + 1 + cfg.P.d) (by omega)]; decide); omega)
      (by have := hTermFootLt0 (tok.termHandle + 1 + model.chain.lastBran) ⟨by omega, by have := hTBrHdr0.1; omega⟩; omega)
      (by have := hTermFootLt0 (termLsfHdr0 + 1) ⟨by have := hTBrHdr0.1; omega, by have := hTBrHdr0.2.1; omega⟩; omega)
      (by omega) (by omega)
  have hs1_r4 : s1.regs 4 = s1a.regs 4 := hs1Regs 4 (by decide) (by decide) (by decide)
  have hPhiCore0Eq :
      (Finset.Ico 0 cfg.P.d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) s0a.mem) =
      (Finset.range cfg.P.d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
    rw [show Finset.Ico 0 cfg.P.d = Finset.range cfg.P.d by ext x; simp]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    exact (hCoreLocal (tok.coreHandle j) (chainLevelOrdAbs model.chain j) (tok.coreTok j) mem0 s0a.mem (fun a ha => by
      rw [show s0a.mem = mem from hs0_mem]
      exact (hMemEqOfTag (by rw [hT21 j hj' a ha]; omega) (by rw [hT21 j hj' a ha]; omega)
        (by rw [hT21 j hj' a ha]; omega) (by rw [hT21 j hj' a ha]; omega)).symm)).2.symm
  rw [hPhiCore0Eq] at hcColOld; simp only [Nat.sub_zero] at hcColOld
  refine ⟨s1, _, s1.regs 4,
    runs_seq_iff.mpr (Or.inr ⟨s0, 3, _, r0,
    runs_seq_iff.mpr (Or.inr ⟨s0a, 2, _, r0a,
    runs_seq_iff.mpr (Or.inr ⟨s1a, cColOld, cTermOld, rColOld, rTermOld, rfl⟩), rfl⟩), rfl⟩),
    rfl, by rw [hs1_r4]; simpa [hs0a_r4] using hs1a_lo,
    by rw [hs1_r4]; simpa [hs0a_r4] using hs1a_hi,
    fun a ha => by
      rw [hs1Mem, Function.update_of_ne (by rw [hs1_r4] at ha; rw [hs0a_r4] at hs1a_lo; omega)]
      exact hz1a a (hs1_r4 ▸ ha),
    fun r hr => by
      rw [hs1Regs r (by omega) (by omega) (by omega), hs1a_regs r (Or.inl hr)]
      simp [s0a, s0, Function.update_of_ne (by omega : r ≠ 20)],
    fun j hj => by
      rw [hs1Mem, Function.update_of_ne (by omega)]
      exact (hs1a_fr _ (by rw [hs0a_r4]; omega)
        (fun r _ hr hf => by have := htagLt (by rw [hT21 r hr _ hf]; omega); omega)
        (Or.inr (by omega))).trans (by rw [show s0a.mem = mem from hs0_mem]; exact hz0 _ (by omega)),
    fun j hj => ?_,
    fun a ha hnf => by
      rw [hs1Mem, Function.update_of_ne (by omega)]
      exact (hs1a_fr a (by rw [hs0a_r4]; omega) (fun r _ hr => hnf r hr) (Or.inl ha)).trans
        (by rw [show s0a.mem = mem from hs0_mem]),
    by omega⟩
  by_cases hjd : j < cfg.P.d
  · rw [chainSuffixForests_getElem_lt model.chain (by omega : j < cfg.P.d - 0)]
    simp only [Nat.zero_add]
    obtain ⟨vcF, ecF, hDGF, hEndF, hFootF⟩ := hOldForests1a j (Nat.zero_le j) hjd
    simp only [Nat.sub_zero] at hDGF hEndF hFootF
    have hPtr : s1.mem (heap + 1 + 12 * cfg.P.d + j) = s1a.mem (heap + 1 + 12 * cfg.P.d + j) := by
      rw [hs1Mem, Function.update_of_ne (by omega)]
    have hFMem : DynGraphAt s1.mem (s1a.mem (heap + 1 + 12 * cfg.P.d + j)) vcF ecF
        (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F :=
      dynGraphAt_of_agree hDGF (fun a ha1 ha2 => by
        rw [hs1Mem, Function.update_of_ne (by
          intro heq; subst heq
          rcases (hCores1a j (Nat.zero_le j) hjd).2 _ (hFootF _ ha1 ha2) with h0 | ⟨hlo, _⟩
          · have := htagLt (by rw [hT21 j hjd _ h0]; omega); omega
          · rw [hs0a_r4] at hlo; omega)])
    refine ⟨vcF, ecF, hPtr.symm ▸ hFMem, ?_, hPtr.symm ▸ (hs1_r4.symm ▸ hEndF),
      fun e he => hG0Cap e (hFSub0 j hjd he)⟩
    rw [hPtr]
    have h4 : 4 ≤ dynGraphSize vcF ecF := by unfold dynGraphSize; omega
    rcases (hCores1a j (Nat.zero_le j) hjd).2 (s1a.mem (heap + 1 + 12 * cfg.P.d + j))
        (hFootF _ le_rfl (by omega)) with h0 | ⟨hlo, _⟩
    · left
      have hlt := htagLt (by rw [hT21 j hjd _ h0]; omega)
      by_contra hgt; push Not at hgt
      rcases (hCores1a j (Nat.zero_le j) hjd).2 (heap + 1 + 12 * cfg.P.d)
          (hFootF _ (by omega) hgt) with h0' | ⟨hlo', _⟩
      · have := htagLt (by rw [hT21 j hjd _ h0']; omega); omega
      · rw [hs0a_r4] at hlo'; omega
    · right; rw [hs0a_r4] at hlo; exact hlo
  · have hjEq : j = cfg.P.d := by omega
    subst hjEq
    rw [show (chainSuffixForests model.chain 0)[cfg.P.d]'(by rw [chainSuffixForests_length]; omega) =
        (model.chain.lastLSFs model.chain.lastBran).F.F by
      simp [chainSuffixForests, List.getElem_append_right]]
    have hPtr : s1.mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) = termFPtr0 := by
      rw [hs1Mem, show cfg.P.d - 0 = cfg.P.d by omega, Function.update_self]
    have hFP1 : tok.termHandle ≤ termFPtr0 := by
      have := hTBrHdr0.2.2.2.2.1; dsimp only [termFPtr0, termLsfHdr0]; omega
    have hFP2 : termFPtr0 + dynGraphSize tok.vcLast tok.ecLast ≤ tok.termTok := by
      have := hTBrHdr0.2.2.2.2.2.1; dsimp only [termFPtr0, termLsfHdr0]; omega
    have hFEnd : termFPtr0 + dynGraphSize tok.vcLast tok.ecLast ≤ uIntBuf := by
      have h4 : 4 ≤ dynGraphSize tok.vcLast tok.ecLast := by unfold dynGraphSize; omega
      have hlt := hTermFootLt0 (termFPtr0 + dynGraphSize tok.vcLast tok.ecLast - 1) ⟨by omega, by omega⟩
      omega
    refine ⟨tok.vcLast, tok.ecLast, ?_, Or.inl (by rw [hPtr]; omega),
      by rw [hPtr, hs1_r4]; rw [hs0a_r4] at hs1a_lo; omega, fun e he => hG0Cap e (hLastFSub0 he)⟩
    rw [hPtr]
    exact dynGraphAt_of_agree hTLSF0.2.1 (fun a ha1 ha2 => by
      have ht : tok.tag a = 19 := hT19 a ⟨by omega, by omega⟩
      rw [hs1Mem, Function.update_of_ne (by have := htagLt (by rw [ht]; decide); omega)]
      exact hs1a_eq_mem0 (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (fun _ _ => by rw [ht]; omega))

/-- Execute Branch A Steps 0–2 starting from the state right after `updateCoreInitRegsKFBL`. -/
theorem wireBranchASteps0To2KFBL_runs
    {w L P m V psi k epsExp drainUnit capExp capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap
      packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore
      root uIntBuf editsPtr g l heap : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hLpos : 0 < L) (hPWord : P < 2 ^ w)
    (hdW : cfg.P.d < 2 ^ w) (hkW : cfg.P.k < 2 ^ w) (hw18 : 18 < 2 ^ w)
    (hPackProc : p.procs[packEditsProc]? = some wireSuffixPackEditsBody)
    (hRefAccProc : p.procs[refreshAccountsProc]? =
      some (wireRefreshAccountsBody shift negate refreshOneProc))
    (hRefOneProc : p.procs[refreshOneProc]? =
      some (wireRefreshOneAccountBody divide add sub negate copy isNeg))
    (hUpdLen0Proc : p.procs[updateLen0Proc]? = some (wireUpdateLen0FromBatchBody copy))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hDGApplyRoot :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      MeetsContract w p dgApply
        (dgApplyBatchContract w model.extG.n tok.rootECap (model.chain.G 0) (model.chain.G 0)
          tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf)))
    (hCoreImpl : UpdateCoreCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    {stepCap : ℕ → ℕ → ℕ}
    (hOps : UpdateCoreOpsHypKFBL (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (capLimit := capLimit) (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (drainUnit := drainUnit) (edMul := edMul)
      (mThresh := mThresh) (coreSpace := coreSpace) (coreFixed := coreFixed) (toolMul := toolMul)
      (fmt := fmt) (cfg := cfg) (G := G) (Psc := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) levelSpace levelCost updStepSpace lastSpace termUpdSpace stepCap)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hModelInvKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec)
    (hIntCapMax : tok.intCap ≤ intCapMax)
    (hForestCap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFreshMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1)
    (hTrNfLe :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      tr.2.2.2.1 ≤ tok.intCap)
    (hBatchMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      IPM.Machine.BatchAt mem uIntBuf tr.2.2.2.2)
    (hSmallMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf))
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr) (hEdLeHeap : editsPtr ≤ heap)
    (hStMem : st.mem = mem) (hz0 : ZeroFrom mem heap)
    (hRegs :
      let d := cfg.P.d
      let cnt := d + 1
      let arrBase := heap + 1 + 12 * d
      let handleBase := tok.handle + 18
      let branchBase := handleBase + cnt
      let levelMeta := solverLevelMetaAddr tok.table d
      st.regs 4 = arrBase + 3 * cnt + 4 ∧ st.regs 70 = root ∧ st.regs 71 = 0 ∧
      st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧ st.regs 75 = d ∧
      st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧ st.regs 79 = cnt ∧
      st.regs 80 = arrBase ∧ st.regs 83 = levelMeta ∧ st.regs 87 = uIntBuf ∧
      st.regs 90 = g ∧ st.regs 91 = l ∧ st.regs 92 = arrBase + 2 * cnt ∧
      st.regs 93 = arrBase + 3 * cnt ∧ st.regs 94 = L)
    (hRoom : heap + coreSpace U.length < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let d := cfg.P.d
    let cnt := d + 1
    let arrBase := heap + 1 + 12 * d
    let emptyPtrs := arrBase + 2 * cnt
    let emptyGraphPtr := arrBase + 3 * cnt
    let levelMeta := solverLevelMetaAddr tok.table d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch U_int
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
    ∃ (out : State) (cost heap1 heapSync heap2 : ℕ)
      (curTree1 : PathTreeState) (curTrees1 : List AuxTree) (curFree1 : List ℕ)
      (curDepth1 : ℕ → ℕ) (curTreeTok1 : Rtree.τ) (newCanonVal : ℕ → PathEdgeValue),
      Runs w p ω
        (wireBranchASteps0To2StmtKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy
          isNeg refreshAccountsProc dgApply updateLen0Proc (opCore 2))
        st .normal out cost ∧
      vCap = model.extG.n ∧ eCap = tok.rootECap ∧
      arrBase + 3 * cnt + 4 ≤ heap1 ∧ heap1 ≤ arrBase + 3 * cnt + 4 + 5 * d ∧
      heap1 ≤ heapSync ∧ heapSync ≤ heap1 + 3 * tok.intCap + sumOld * (2 + wireTreeSyncEditSpace L) ∧
      heapSync + 3 * L ≤ heap2 ∧ heap2 ≤ heapSync + 3 * L + U.length * wireRefreshOneSpace L ∧
      out.regs 4 = heap2 ∧ ZeroFrom out.mem heap2 ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      out.mem heap = 0 ∧
      (∀ j < cnt, out.mem (emptyPtrs + j) = emptyGraphPtr) ∧
      (∀ j < 4, out.mem (emptyGraphPtr + j) = 0) ∧
      curTree1.n = model.extG.n ∧
      LctInvWith pathPayload curTree1 curTrees1 curFree1 curDepth1 ∧
      PathTreeNumericInv curTree1 curTrees1 B R ∧
      TreeEditNamedSlots curTree1 curTrees1 { G0' with E := ∅ }
        (fun ei => out.mem (tok.slots + ei)) (fun sl => out.mem (tok.names + sl)) ∧
      TreeEditLiveAccounts curTree1 curTrees1 { G0' with E := ∅ }
        (fun ei => out.mem (tok.slots + ei)) newCanonVal ∧
      Rtree.rep tok.treeHeap curTree1 curTreeTok1 out.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok1 a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap1 ≤ a ∧ a < heapSync)) ∧
      (∀ j < tok.intCap, out.mem (tok.slots + j) = 0) ∧
      DynGraphAt out.mem tok.rootGraph model.extG.n tok.rootECap G0' ∧
      EdgeValuesAt out.mem (mem0 levelMeta) 4 L P G0'.E ℓ' ∧
      (∀ a < arrBase, a ≠ root + 11 →
        tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 → tok.tag a ≠ 12 → tok.tag a ≠ 13 →
        tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 → tok.tag a ≠ 20 →
        tok.tag a ≠ 23 + d → (∀ j < d, tok.tag a ≠ 21 + j) → out.mem a = mem a) ∧
      (∀ e ∈ model.extG.E,
        let ei := tr.2.1 e
        let v := newCanonVal ei
        PathIntAt out.mem (out.mem (tok.edgeThresholds + ei)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (ei ∈ G0.E →
          out.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
          ((ei ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ out.mem (tok.edgeRecords + ei) ∧
              out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, out.mem (tok.edgeRecords + ei) ≤ a →
                a < out.mem (tok.edgeRecords + ei) + (2 + 4 * L) →
                ¬ Rtree.foot tok.treeHeap curTreeTok1 a) ∧
           (ei ∉ model.chain.toTreeChain.chainTree.E →
              out.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei)))) ∧
        (ei ∉ G0.E →
          heapSync + 3 * L ≤ out.mem (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeThresholds + ei) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heap2)) ∧
      (∀ ei₁ ∈ G0'.E, ∀ ei₂ ∈ G0'.E, ei₁ ≠ ei₂ →
        out.mem (tok.edgeRecords + ei₁) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₁)) ∧
      (∀ ei₁ ∈ G0'.E, ei₁ ∉ G0.E → ∀ ei₂ ∈ G0'.E, ei₂ ∉ G0.E →
        out.mem (tok.edgeThresholds + ei₁) + L ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeThresholds + ei₁)) ∧
      cost + Rtree.phi tok.treeHeap curTreeTok1 out.mem ≤
        d * (Psc.readout + 48) +
        (230 * (d + 1) + 85 * sumOld + 300) +
        sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
        (15 * tok.intCap + 30) +
        (U.length * (wireRefreshOneCost L + 120) + 71 * L + 210) +
        (670 * (4 * U.length + 1) + 30) +
        (U.length * (17 * L + 70) + 80) + 70 +
        (Rtree.phi tok.treeHeap tok.treeTok mem0 + tok.offReadyCount * drainUnit +
          (Finset.range d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0)) := by
  dsimp only
  let d := cfg.P.d
  let cnt := d + 1
  let arrBase := heap + 1 + 12 * d
  let heapStart := arrBase + 3 * cnt + 4
  let levelMeta := solverLevelMetaAddr tok.table d
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
  have hRep0_keep := hRep0
  have hMeta0_keep := hMeta0
  have hModelInv_keep := hModelInv
  obtain ⟨hOwnOfTag, hT1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hRootG0 := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  obtain ⟨⟨hdPos, _⟩, ⟨_, hExtNLe, hRootCapLe⟩, _, _, _, _, ⟨hLastBrLt0, _⟩, hOrdIn0,
    ⟨hLMd0Eq, _, _, _, _, _⟩, _, hG0'Cap, _, hG0'mLeI, _, _, _, _, hFSub0, hLastFSub0, _⟩ := hModelInv
  obtain ⟨hSFL0, _, _, _, _, _, _, _, _, _, hBrLt0, _, _⟩ := hModelInvKFBL
  have hCapsEq : vCap = model.extG.n ∧ eCap = tok.rootECap := by
    have hCap0 := hCaps0 0 hdPos; rw [hLMd0Eq] at hCap0; exact dynGraphAt_caps_eq hCap0 hRootG0
  obtain ⟨hvCapEq, heCapEq⟩ := hCapsEq
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hSpA := hOps.spaceTotalBranchA model.extG.n tok.rootECap U.length G0'.m hExtNLe
    (hRootCapLe.trans hIntCapMax) (hG0'mLeI.trans hIntCapMax)
  have hSumOldSp : sumOld * (2 + wireTreeSyncEditSpace L) ≤ forestEdgeCap * (2 + wireTreeSyncEditSpace L) :=
    Nat.mul_le_mul_right _ (Nat.le_of_add_right_le hForestCap)
  have hSyncRoom :
      heapStart + 5 * d + (3 * tok.intCap + sumOld * (2 + wireTreeSyncEditSpace L)) +
        (3 * L + U.length * wireRefreshOneSpace L) < 2 ^ w := by
    have h1 : heapStart + 5 * d = heap + ((1 + 12 * d) + 3 * (d + 1) + 4 + d * 5) := by
      dsimp only [heapStart, arrBase, cnt, d]; ring
    have h2 : 3 * tok.intCap ≤ 3 * intCapMax := Nat.mul_le_mul_left 3 hIntCapMax
    have h3 : (1 + 12 * d) + 3 * (d + 1) + 4 + d * 5 +
        (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) +
        (3 * L + U.length * wireRefreshOneSpace L) ≤ coreSpace U.length :=
      le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
        (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
          (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) hSpA)))))))
    have h4 : (1 + 12 * d) + 3 * (d + 1) + 4 + d * 5 +
        (3 * tok.intCap + sumOld * (2 + wireTreeSyncEditSpace L)) +
        (3 * L + U.length * wireRefreshOneSpace L) ≤ coreSpace U.length :=
      le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add h2 hSumOldSp) _) _) h3
    rw [h1]; linarith [hRoom, h4]
  have hHS5Lt : heapStart + 5 * d < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSyncRoom)
  dsimp only at hRegs
  obtain ⟨hr4, hr70, hr71, hr72, hr73, hr75, hr77, hr78, hr79, hr80, hr83, hr87, hr90, hr91,
    hr92, hr93, hr94⟩ := hRegs
  -- Steps 0–1
  obtain ⟨s1, c01, heap1, r01, hs1_r4, hHeap1Lo, hHeap1Hi, hz1, hs1_ge70, hEmptyG1, hOldF1,
      hs1_frame, hc01⟩ :=
    branchA_steps01_runs hCoreLocal hdPos hdW hkW hw18 hCoreImpl hRep0_keep hMeta0_keep hCaps0 hSFL0
      hBrLt0 hLastBrLt0 hOrdIn0 (fun j hj => (hFSub0 j hj).1) hLastFSub0 hMemEq hFootLt
      (le_trans (le_trans (Nat.le_add_right _ _) hULeEd) hEdLeHeap) hStMem hz0
      ⟨hr4, hr71, hr72, hr75, hr77, hr78, hr80, hr83⟩ hHS5Lt
  -- Step 2: `wireBranchASync1AndPrepStmt`
  have hLvl0Meta :
      EdgeValuesAt mem0 (mem0 levelMeta) 4 L P G0.E (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ a, mem0 levelMeta ≤ a → a < mem0 levelMeta + eCap * L → tok.tag a = 23 + d) ∧
      (∀ e ∈ G0.E, e < eCap) ∧ (∀ e ∈ G0'.E, e < eCap) ∧
      (∀ u ∈ U_int, match u with | .insert ei _ _ => ei < eCap | _ => True) := by
    obtain ⟨hDG0, hEV0, _, hTL0, _⟩ := SolverLevelMetaAt.atCaps hMeta0_keep hCaps0 0 hdPos
    refine ⟨hEV0, hTL0, fun e he => hDG0.2.2.1 e he, fun e he => heCapEq.symm ▸ (hG0'Cap e he).1,
      fun u hu => ?_⟩
    cases u with
    | insert ei x y => exact heCapEq.symm ▸ hModelInv_keep.2.2.2.2.2.2.2.2.2.1 _ hu
    | delete _ | split _ _ _ _ => trivial
  obtain ⟨s2, cSync1, heapSync, heap2, curTree1, curTrees1, curFree1, curDepth1, curTreeTok1,
      newCanonVal, rSync1, hcSync1, hs2_r4, hSyncLo, hSyncHi, hH2Lo, hH2Hi, hz2, hs2_ge70,
      hEmptyPtrs2, hEmptyG2, hTreeN1, hLct1, hNum1, hNamed1, hLive1, hTreeRep1, hTreeFoot1,
      hZeroSlots2, hRootG2, hLen0_2, hs2_frame, hCanon2, hOffDisj2, hThrOffDisj2⟩ :=
    wireBranchASync1AndPrep_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (wordExp := wordExp) (stretchPrec := stretchPrec)
      (packEditsProc := packEditsProc) (initTree := initTree) (bind := bind) (canonCopy := canonCopy)
      (isNeg := isNeg) (refreshAccountsProc := refreshAccountsProc) (shift := shift) (negate := negate)
      (refreshOneProc := refreshOneProc) (divide := divide) (add := add) (sub := sub) (copy := copy)
      (dgApply := dgApply) (updateLen0Proc := updateLen0Proc) (root := root) (uIntBuf := uIntBuf)
      (editsPtr := editsPtr) (g := g) (l := l) (heap := arrBase) (heap1 := heap1) (ec0 := eCap)
      (fmt := fmt) (cfg := cfg) (Rcore := Rcore) (p := p) (opTree := opTree) (ω := ω)
      (mem0 := mem0) (mem := mem) (st := s1) (model := model) (tok := tok) (U := U) (B := B) (R := R)
      hPackProc hRefAccProc hRefOneProc hUpdLen0Proc hFour hLpos hPWord hw18 hTreeImpl hBindOk hCanonOk
      hIsNegOk hshift hdiv hadd hsub hneg hcopy hDGApplyRoot hRep0_keep hMeta0_keep hNum0 hOffInv0 hOffBd0
      hModelInv_keep hLogW hCapT hRef hMemEq hFreshMem hTrNfLe hBatchMem hSmallMem hFootLt hGLt hLLt
      hULeEd (le_trans hEdLeHeap (by dsimp only [arrBase]; omega)) hHeap1Lo hLvl0Meta
      ⟨hs1_r4, (hs1_ge70 70 (by decide)).trans hr70, (hs1_ge70 73 (by decide)).trans hr73,
       (hs1_ge70 75 (by decide)).trans hr75, (hs1_ge70 79 (by decide)).trans hr79,
       (hs1_ge70 80 (by decide)).trans hr80, (hs1_ge70 83 (by decide)).trans hr83,
       (hs1_ge70 87 (by decide)).trans hr87, (hs1_ge70 90 (by decide)).trans hr90,
       (hs1_ge70 91 (by decide)).trans hr91, (hs1_ge70 92 (by decide)).trans hr92,
       (hs1_ge70 93 (by decide)).trans hr93, (hs1_ge70 94 (by decide)).trans hr94⟩
      hz1 hEmptyG1 hOldF1 hs1_frame
      (by have hHi : heap1 ≤ heapStart + 5 * d := hHeap1Hi; linarith [hHi, hSyncRoom])
  have r02 : Runs w p ω
      (wireBranchASteps0To2StmtKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy
        isNeg refreshAccountsProc dgApply updateLen0Proc (opCore 2)) st .normal s2 (c01 + cSync1 + 1) := by
    obtain ⟨s0, c0, cr1, h0, h1, hc1⟩ := (runs_seq_iff.mp r01).resolve_left (by simp)
    obtain ⟨s0a, c0a, cr2, h0a, h2, hc2⟩ := (runs_seq_iff.mp h1).resolve_left (by simp)
    obtain ⟨s1a, c1a, c1b, h1a, h1b, hc3⟩ := (runs_seq_iff.mp h2).resolve_left (by simp)
    refine runs_seq_iff.mpr (Or.inr ⟨s0, c0, c0a + (c1a + (c1b + cSync1 + 1) + 1) + 1, h0,
      runs_seq_iff.mpr (Or.inr ⟨s0a, c0a, c1a + (c1b + cSync1 + 1) + 1, h0a,
      runs_seq_iff.mpr (Or.inr ⟨s1a, c1a, c1b + cSync1 + 1, h1a,
      runs_seq_iff.mpr (Or.inr ⟨s1, c1b, cSync1, h1b, rSync1, rfl⟩), rfl⟩), rfl⟩),
      by omega⟩)
  have hs2_frame_arr : ∀ a < arrBase, a ≠ root + 11 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 → tok.tag a ≠ 12 → tok.tag a ≠ 13 →
      tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 → tok.tag a ≠ 20 →
      tok.tag a ≠ 23 + d → (∀ j < d, tok.tag a ≠ 21 + j) → s2.mem a = mem a := by
    intro a ha hne11 h9 h10 h11 h12 h13 h14 h15 h16 h20 h23 hc
    refine (hs2_frame a (lt_of_lt_of_le ha (le_trans (by dsimp only [heapStart, arrBase, cnt]; omega) hHeap1Lo))
      hne11 (Or.inl (lt_of_lt_of_le ha (Nat.le_add_right _ _))) h9 h10 h11 h12 h13 h14 h15 h16 h20
      (by by_contra h; push Not at h; exact h23 (hLvl0Meta.2.1 a h.1 h.2))).trans ?_
    exact hs1_frame a ha (fun j hj hf => hc j hj (hT21 j hj a hf))
  refine ⟨s2, c01 + cSync1 + 1, heap1, heapSync, heap2, curTree1, curTrees1, curFree1, curDepth1,
    curTreeTok1, newCanonVal, r02, hvCapEq, heCapEq, hHeap1Lo, hHeap1Hi, hSyncLo, hSyncHi, hH2Lo,
    hH2Hi, hs2_r4, hz2, fun r hr => (hs2_ge70 r hr).trans (hs1_ge70 r hr), ?_, hEmptyPtrs2,
    hEmptyG2, hTreeN1, hLct1, hNum1, hNamed1, hLive1, hTreeRep1, hTreeFoot1, hZeroSlots2, hRootG2,
    hLen0_2, hs2_frame_arr, hCanon2, hOffDisj2, hThrOffDisj2, branchA02_cost_arith hc01 hcSync1⟩
  have hUIntLeHeap : uIntBuf ≤ heap := le_trans (le_trans (Nat.le_add_right _ _) hULeEd) hEdLeHeap
  have hneH : ∀ v, v ≠ 0 → tok.tag heap ≠ v := fun v hv h =>
    Nat.not_lt_of_ge hUIntLeHeap (htagLt (by rw [h]; exact hv))
  exact (hs2_frame_arr heap (by dsimp only [arrBase]; omega)
    (Nat.ne_of_gt (lt_of_lt_of_le (htagLt (by rw [hT1 11 (by omega)]; decide)) hUIntLeHeap))
    (hneH 9 (by decide)) (hneH 10 (by decide)) (hneH 11 (by decide))
    (hneH 12 (by decide)) (hneH 13 (by decide)) (hneH 14 (by decide))
    (hneH 15 (by decide)) (hneH 16 (by decide)) (hneH 20 (by decide))
    (hneH (23 + d) (by omega)) (fun j _ => hneH (21 + j) (by omega))).trans (hz0 heap le_rfl)

end MinCostFlow.MinRatio
