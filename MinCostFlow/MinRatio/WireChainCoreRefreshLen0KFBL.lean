module

public import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# The account refresh and the lengths of level `0` for Branch B (`WireChainCoreRefreshLen0KFBL`)

Branch A and Branch B both refresh the accounts and write the lengths of level `0` after their
first sync. Branch A also applies the batch to the root graph there
(`wireRefreshAndUpdateRootStmt`, `WireChainCorePreCommon.lean`). Branch B must not: in Branch B
the root graph is the graph of level `0`, and the step of level `0` in the loop applies the batch
to it. So `wireRefreshLen0Stmt` is `wireRefreshAndUpdateRootStmt` without the root `dgApply`, and
`wireRefreshLen0_runs` is `wireRefreshAndUpdateRoot_runs` without that step. The root graph is
left alone, so the frame covers it, and the cost has no term for `dgApply`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Refresh the accounts, then write the lengths of level `0`. The root graph is not touched. -/
@[expose] def wireRefreshLen0Stmt (refreshAccountsProc updateLen0Proc : ℕ) : Stmt :=
  .call 4 refreshAccountsProc [.reg 70, .reg 87, .reg 90, .reg 91, .reg 4] ;;
  .assign 14 (.load (.bin .add (.reg 70) (.const 4))) ;;
  .assign 15 (.load (.reg 83)) ;;
  .call 16 updateLen0Proc [.reg 87, .reg 14, .reg 91, .reg 15, .reg 94]

theorem wireRefreshLen0Stmt_noRand (refreshAccountsProc updateLen0Proc : ℕ) :
    (wireRefreshLen0Stmt refreshAccountsProc updateLen0Proc).NoRand := by
  simp [wireRefreshLen0Stmt, Stmt.NoRand]

set_option maxHeartbeats 1200000 in
/-- The run of `wireRefreshLen0Stmt` after the first sync has saved canonical `PathEdgeAt` records
for every deleted edge of `U_int` and every surviving edge outside `curE`. It is
`wireRefreshAndUpdateRoot_runs` without the step on the root graph. -/
theorem wireRefreshLen0_runs
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec
      refreshAccountsProc shift negate refreshOneProc divide add sub copy isNeg
      updateLen0Proc
      root uIntBuf editsPtr g l heap heapSync ec0 : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    {curE : Finset ℕ} {canonVal : ℕ → PathEdgeValue}
    (hRefAccProc : p.procs[refreshAccountsProc]? =
      some (wireRefreshAccountsBody shift negate refreshOneProc))
    (hRefOneProc : p.procs[refreshOneProc]? =
      some (wireRefreshOneAccountBody divide add sub negate copy isNeg))
    (hUpdLen0Proc : p.procs[updateLen0Proc]? = some (wireUpdateLen0FromBatchBody copy))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hisNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hRef : RefreshBatch model.extG U)
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
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a <
        uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr) (hEdLeHeap : editsPtr ≤ heap)
    (hHeapLe : heap ≤ heapSync)
    (hLpos : 0 < L) (hPword : P < 2 ^ w) (hw18 : 18 < 2 ^ w)
    (hLevel0Meta :
      let lm := solverLevelMetaAddr tok.table cfg.P.d
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      EdgeValuesAt mem0 (mem0 lm) 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ a, mem0 lm ≤ a → a < mem0 lm + ec0 * L → tok.tag a = 23 + cfg.P.d) ∧
      (∀ e ∈ (model.chain.G 0).E, e < ec0) ∧
      (∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < ec0) ∧
      (∀ u ∈ tr.2.2.2.2, match u with | .insert ei _ _ => ei < ec0 | _ => True))
    (hCanonExt : ∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      let v := canonVal ei
      v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
      (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
      (v.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
      (v.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
      ∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        v.detector = acc - detectorThreshold P cfg.ε (model.extℓ e))
    (hRegs :
      st.regs 4 = heapSync ∧ st.regs 70 = root ∧ st.regs 83 =
          solverLevelMetaAddr tok.table cfg.P.d ∧
      st.regs 87 = uIntBuf ∧ st.regs 90 = g ∧ st.regs 91 = l ∧ st.regs 94 = L)
    (hzSync : ZeroFrom st.mem heapSync)
    (hStMem0 : ∀ a < uIntBuf, a ≠ root + 11 →
      tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
      tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
      (∀ j < cfg.P.d, tok.tag a ≠ 21 + j) → st.mem a = mem0 a)
    (hStMemFresh : ∀ a < heap,
      (tok.tag a = 6 ∨ tok.tag a = 7 ∨ tok.tag a = 8 ∨ uIntBuf ≤ a) → st.mem a = mem a)
    (hOffSynced :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let U_int := tr.2.2.2.2
      let G0 := model.chain.G 0
      (∀ ei ∈ G0.E, (Update.delete ei ∈ U_int ∨ ei ∉ curE) →
        PathEdgeAt st.mem (st.mem (tok.edgeRecords + ei)) 4 L (some (canonVal ei)) ∧
        st.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapSync ∧
        (∀ j < 2 + 4 * L, ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap
          (st.mem (tok.edgeRecords + ei) + j) ∧
          (st.mem (tok.edgeRecords + ei) + j < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
            mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L ≤ st.mem (tok.edgeRecords + ei)
                + j))) ∧
      (∀ e₁ ∈ G0.E, ∀ e₂ ∈ G0.E, e₁ ≠ e₂ → e₁ ∉ curE → e₂ ∉ curE →
        st.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ st.mem (tok.edgeRecords + e₂) ∨
        st.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ st.mem (tok.edgeRecords + e₁)))
    (hRoom : heapSync + 3 * L + U.length * wireRefreshOneSpace L < 2 ^ w) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch U_int
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let lm := solverLevelMetaAddr tok.table cfg.P.d
    ∃ (out : State) (cost heap2 : ℕ) (newCanonVal : ℕ → PathEdgeValue),
      Runs w p ω (wireRefreshLen0Stmt refreshAccountsProc updateLen0Proc) st .normal out cost ∧
      cost ≤ (U.length * (wireRefreshOneCost L + 120) + 71 * L + 210) +
        (U.length * (17 * L + 70) + 80) ∧
      out.regs 4 = heap2 ∧
      heapSync + 3 * L ≤ heap2 ∧ heap2 ≤ heapSync + 3 * L + U.length * wireRefreshOneSpace L ∧
      ZeroFrom out.mem heap2 ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      EdgeValuesAt out.mem (mem0 lm) 4 L P G0'.E ℓ' ∧
      (∀ a < heapSync,
        ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap a →
        (a < mem0 lm ∨ mem0 lm + ec0 * L ≤ a) → out.mem a = st.mem a) ∧
      (∀ ei < tok.intCap,
        (¬ ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = ei) →
          out.mem (tok.edgeThresholds + ei) = st.mem (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
      (∀ e ∈ model.extG.E,
        let ei := tr.2.1 e
        let v := newCanonVal ei
        PathIntAt out.mem (out.mem (tok.edgeThresholds + ei))
            4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (ei ∈ G0.E →
          newCanonVal ei = canonVal ei ∧
          out.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) ∧
          (ei ∉ curE → PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some v))) ∧
        (ei ∉ G0.E →
          heapSync + 3 * L ≤ out.mem (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeThresholds + ei) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heap2 ∧
          PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some v))) ∧
      (∀ ei₁ ∈ G0'.E, ∀ ei₂ ∈ G0'.E, ei₁ ≠ ei₂ → ei₁ ∉ curE → ei₂ ∉ curE →
        out.mem (tok.edgeRecords + ei₁) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₁)) ∧
      (∀ ei₁ ∈ G0'.E, ei₁ ∉ G0.E → ∀ ei₂ ∈ G0'.E, ei₂ ∉ G0.E →
        out.mem (tok.edgeThresholds + ei₁) + L ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeThresholds + ei₁)) := by
  classical
  dsimp only
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set U_int := tr.2.2.2.2
  set G0 := model.chain.G 0
  set G0' := G0.applyBatch U_int
  set gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  set lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  set ℓ' := fun e' => lVec (tr.2.2.1 e')
  set d := cfg.P.d
  set lm := solverLevelMetaAddr tok.table d
  set oldLen0 := mem0 lm
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, hFreshInv, _, hExtLtM,
    ⟨hG0Cap, hIntCapPos, _, _⟩, _, _, _, _, _, hAccounts0, _, _, _, _, hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, hT6, hT7, hT8, _, _, _, hT12, hT13, _, _, _,
    hT1718, _, hT20, _⟩ := hTags0
  obtain ⟨_, hRootG0, _, _, _⟩ := hWire0
  obtain ⟨_, _, _, _, hTagMeta0, hMetaLvls0⟩ := hMeta0
  obtain ⟨⟨hdPos, hmPos⟩, _, hEllEq0, ⟨hGDisjRaw, hLDisjRaw⟩, _, ⟨hPdiv, hEpsLe, hFitPos, hEpsEq⟩,
    _, _, _, hBatchCaps, hG0'Cap, _, _, hRefInfo, _⟩ := hModelInv
  have hGDisj : ∀ j < m * L,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (g + j) := by
    intro j hj hf; rcases hf with h | h | ⟨r, hr, h⟩
    · exact (hGDisjRaw j hj).1 h
    · exact (hGDisjRaw j hj).2.1 h
    · exact (hGDisjRaw j hj).2.2 r hr h
  have hLDisj : ∀ j < m * L,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (l + j) := by
    intro j hj hf; rcases hf with h | h | ⟨r, hr, h⟩
    · exact (hLDisjRaw j hj).1 h
    · exact (hLDisjRaw j hj).2.1 h
    · exact (hLDisjRaw j hj).2.2 r hr h
  obtain ⟨hOldLen0, hTagOldLen0, hG0Ec0, hG0'Ec0, hInsEc0⟩ := hLevel0Meta
  obtain ⟨hTr1Eq, hFreshTr, hEdgeInt, hUnchEdge, hRepEdge⟩ :=
      refreshBatch_edge_dichotomy hFreshInv hRef
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    cases u with
    | insert _ _ _ | delete _ => trivial
    | split _ _ _ _ => exact hRef.2.2 _ hu
  have hULenEq : U_int.length = U.length :=
    translateBatch_length_eq U model.extG model.extToInt model.intToExt model.nextFresh hEdgeU
  obtain ⟨hI2EOldAll, hSurvAll, hRangeAll, _, hInsIffAll⟩ :=
    translateBatch_oldId_facts U model.extG G0 model.extToInt model.intToExt model.nextFresh
      hFreshInv hRef.1 hEdgeU
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hNoMutOfTag {a v : ℕ} (ht : tok.tag a = v) (h12 : v ≠ 12) (h13 : v ≠ 13) :
      ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap a := by
    intro hm; rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hT12 (a - tok.edgeThresholds) (by omega)
      rw [show tok.edgeThresholds + (a - tok.edgeThresholds) =
          a by omega, ht] at this; exact h12 this
    · have := hT13 (a - tok.edgeRecords) (by omega)
      rw [show tok.edgeRecords + (a - tok.edgeRecords) = a by omega, ht] at this; exact h13 this
  have hNoMutOfNotFoot {a : ℕ}
      (hnf : ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a) :
      ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap a := by
    intro hm; rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hnf (Or.inl (hOwnOfTag a (by
        have := hT12 (a - tok.edgeThresholds) (by omega)
        rw [show tok.edgeThresholds + (a - tok.edgeThresholds) =
            a by omega] at this; rw [this]; decide)))
    · exact hnf (Or.inl (hOwnOfTag a (by
        have := hT13 (a - tok.edgeRecords) (by omega)
        rw [show tok.edgeRecords + (a - tok.edgeRecords) = a by omega] at this; rw [this]; decide)))
  have hNotLen0OfTag {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 23 + d) :
      a < oldLen0 ∨ oldLen0 + ec0 * L ≤ a := by
    by_contra h; push Not at h
    have := hTagOldLen0 a h.1 h.2; rw [ht] at this; exact hv this
  have hStFixed {a v : ℕ} (ht : tok.tag a = v) (hv : v = 1 ∨ v = 2 ∨ v = 12 ∨ v = 17 ∨ v = 20 ∨ v =
      22 + d ∨ v = 23 + d)
      (hne11 : a ≠ root + 11) : st.mem a = mem0 a :=
    hStMem0 a (htagLt (by rw [ht]; omega)) hne11 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (fun _ _ => by omega)
  have hStNotFoot {a : ℕ} (ha : a < uIntBuf)
      (hnf : ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a) :
      st.mem a = mem0 a := by
    have ht0 : tok.tag a = 0 := by by_contra hne; exact hnf (Or.inl (hOwnOfTag a hne))
    have hne11 : a ≠ root + 11 := fun h => by rw [h, hT1 11 (by omega)] at ht0; omega
    exact hStMem0 a ha hne11 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (fun _ _ => by omega)
  have hStG {a : ℕ} (h1 : g ≤ a) (h2 : a < g + m * L) : st.mem a = mem0 a :=
    hStNotFoot (by omega)
        (by have := hGDisj (a - g) (by omega); rwa [show g + (a - g) = a by omega] at this)
  have hStL {a : ℕ} (h1 : l ≤ a) (h2 : a < l + m * L) : st.mem a = mem0 a :=
    hStNotFoot (by omega)
        (by have := hLDisj (a - l) (by omega); rwa [show l + (a - l) = a by omega] at this)
  have hRootSt : SolverRootDirAt st.mem root tok.handle tok.table tok.levelsEnd tok.forward
      tok.inverse tok.freshCounter tok.slots tok.names tok.slotThresholds tok.edgeThresholds
      tok.edgeRecords (st.mem (root + 11))
          tok.offReadyList tok.inOffReady tok.rootGraph tok.intCap := by
    intro j hj; have hj16 : j < 16 := by simpa using hj
    by_cases h11 : j = 11
    · subst h11; simp
    · rw [hStFixed (hT1 j hj16) (Or.inl rfl) (by omega)]
      have h0 := hRootDir0 j hj
      have : [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse, tok.freshCounter,
          tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds, tok.edgeRecords,
          st.mem (root + 11), tok.offReadyList, tok.inOffReady, tok.rootGraph, tok.intCap][j] =
        [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse, tok.freshCounter,
          tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds, tok.edgeRecords,
          tok.offReadyCount, tok.offReadyList, tok.inOffReady, tok.rootGraph, tok.intCap][j] := by
        interval_cases j <;> first | rfl | contradiction
      exact h0.trans this.symm
  have hDG0St : DynGraphAt st.mem tok.rootGraph model.extG.n tok.rootECap G0 :=
    hRootG0.of_agree fun a ha1 ha2 => hStFixed (hT20 a ha1 ha2) (by omega)
      (fun h => by have := hT20 a ha1 ha2; rw [h, hT1 11 (by omega)] at this; omega)
  have hBatchLenEq : (batchWords U_int).length = editsPtr - d - uIntBuf :=
    smallBatchAt_batchWords_len_eq hSmallMem hEdgeInt
  have hBatchSt : IPM.Machine.BatchAt st.mem uIntBuf U_int := fun j hj => by
    rw [hStMemFresh (uIntBuf + j) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))]
    exact hBatchMem j hj
  have hFreshSt : FreshTablesAt st.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 :=
    ⟨(hStMemFresh tok.freshCounter (lt_trans (htagLt (by rw [hT6]; decide)) (by omega))
        (Or.inl hT6)).trans hFreshMem.1,
     fun j hj => (hStMemFresh (tok.forward + j) (lt_trans (htagLt (by rw [hT7 j hj]; decide))
         (by omega))
        (Or.inr (Or.inl (hT7 j hj)))).trans (hFreshMem.2.1 j hj),
     fun j hj => (hStMemFresh (tok.inverse + j) (lt_trans (htagLt (by rw [hT8 j hj]; decide))
         (by omega))
        (Or.inr (Or.inr (Or.inl (hT8 j hj))))).trans (hFreshMem.2.2 j hj)⟩
  let oldThr : ℕ → ℤ := fun ei => detectorThreshold P cfg.ε (model.extℓ (model.intToExt ei))
  let accFn : ℕ → ℤ := fun ei =>
    if h : model.intToExt ei ∈ model.extG.E ∧ model.extToInt (model.intToExt ei) = ei then
      (hCanonExt (model.intToExt ei) h.1).2.2.2.2.2.2.2.2.choose
    else 0
  let gNew : ℕ → ℤ := fun e => Num.intVal mem0 (g + e * L) 4 L
  let lNew : ℕ → ℕ := fun e => (Num.intVal mem0 (l + e * L) 4 L).toNat
  have hDelInfoSt : ∀ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int →
      let e := tr.2.2.1 ei_old
      let ei_new := tr.2.1 e
      let ε := (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P
      let thrNew := detectorThreshold P ε ((lNew e : ℝ) / (2 : ℝ) ^ P)
      ei_old < tok.intCap ∧ ei_old < tok.rootECap ∧ e < m ∧ ei_new < tok.intCap ∧
      0 < lNew e ∧
      (∀ ei2 ∈ G0.E, Update.delete ei2 ∈ U_int → ei_new ≠ ei2) ∧
      (∀ ei2 ∈ G0.E, Update.delete ei2 ∈ U_int → ei2 ≠ ei_old → tr.2.1 (tr.2.2.1 ei2) ≠ ei_new) ∧
      (canonVal ei_old).forward = true ∧
      PathEdgeAt st.mem (st.mem (tok.edgeRecords + ei_old)) 4 L (some (canonVal ei_old)) ∧
      PathIntAt st.mem (st.mem (tok.edgeThresholds + ei_old)) 4 L (oldThr ei_old) ∧
      (canonVal ei_old).detector = accFn ei_old - oldThr ei_old ∧
      PathIntAt st.mem (g + e * L) 4 L (gNew e) ∧
      PathIntAt st.mem (l + e * L) 4 L (lNew e : ℤ) ∧
      Num.Fits 4 L (-thrNew) ∧ Num.Fits 4 L thrNew ∧
      Num.Fits 4 L (accFn ei_old) ∧ Num.Fits 4 L (accFn ei_old - thrNew) ∧
      st.mem (tok.edgeRecords + ei_old) + (2 + 4 * L) ≤ heapSync ∧
      st.mem (tok.edgeThresholds + ei_old) + L ≤ heapSync ∧
      (∀ j < 2 + 4 * L, ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap
        (st.mem (tok.edgeRecords + ei_old) + j)) ∧
      (∀ j < L, ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap
        (st.mem (tok.edgeThresholds + ei_old) + j)) := by
    intro ei_old hOldG hOldDel
    obtain ⟨hE2I, hExtMem⟩ := hFreshInv.hRight ei_old hOldG
    have heEq : tr.2.2.1 ei_old = model.intToExt ei_old :=
        hI2EOldAll ei_old (hFreshInv.hLtFresh _ hOldG)
    set e := tr.2.2.1 ei_old
    have heExt : e ∈ model.extG.E := heEq ▸ hExtMem
    have hNewG0' : tr.2.1 e ∈ G0'.E := hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 heExt
    obtain ⟨hGV, hLV, _, hLEq, hLPos, _, _, hFitNT, hFitPT, hAccB⟩ := hRefInfo ei_old hOldG hOldDel
    change 0 < Num.intVal mem0 (l + e * L) 4 L at hLPos
    have hlNewEq : (lNew e : ℤ) = Num.intVal mem0 (l + e * L) 4 L := by dsimp only [lNew]; omega
    have hlNewReal : (lNew e : ℝ) / (2 : ℝ) ^ P = lVec e := by
      rw [← Int.cast_natCast, hlNewEq]; exact hLEq
    have hCanon := hCanonExt (model.intToExt ei_old) hExtMem
    rw [hE2I] at hCanon
    have hAccSpec := (hCanonExt (model.intToExt ei_old) hExtMem).2.2.2.2.2.2.2.2.choose_spec
    have hAccFnEq : accFn ei_old = (hCanonExt (model.intToExt ei_old)
        hExtMem).2.2.2.2.2.2.2.2.choose := by
      simp [accFn, hExtMem, hE2I]
    have hOff := hOffSynced.1 ei_old hOldG (Or.inl hOldDel)
    have hThrPtrEq : st.mem (tok.edgeThresholds + ei_old) = mem0 (tok.edgeThresholds + ei_old) :=
      hStFixed (hT12 ei_old (hG0Cap ei_old hOldG)) (by omega)
        (fun h => by
          have := hT12 ei_old (hG0Cap ei_old hOldG); rw [h, hT1 11 (by omega)] at this; omega)
    have hThrTag (j : ℕ) (hj : j < L) : tok.tag (mem0 (tok.edgeThresholds + ei_old) + j) = 17 := by
      have := (hT1718 (model.intToExt ei_old) hExtMem).1 j hj; rwa [hE2I] at this
    have hThrAtSt : PathIntAt st.mem (st.mem (tok.edgeThresholds + ei_old)) 4 L (oldThr ei_old) :=
        by
      rw [hThrPtrEq]; have h0 := (hAccounts0.1 (model.intToExt ei_old) hExtMem).2.1; rw [hE2I] at h0
      exact h0.congr (fun j hj => hStFixed (hThrTag j hj) (by omega)
        (fun h => by have := hThrTag j hj; rw [h, hT1 11 (by omega)] at this; omega))
    have hDetOldEq : (canonVal ei_old).detector = accFn ei_old - oldThr ei_old := by
      rw [hAccFnEq]; simpa [oldThr, hE2I] using hAccSpec.2
    have hAccFits := hAccB (accFn ei_old) (by
      have heEq' :
          (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 ei_old =
          model.intToExt ei_old := heEq
      rw [hAccFnEq, heEq']; exact hAccSpec.1)
    have heLtM : e < m := hExtLtM e heExt
    have heL : e * L + L ≤ m * L := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLtM)
    have hThrEq : detectorThreshold P ((((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P)
        ((lNew e : ℝ) / (2 : ℝ) ^ P) = detectorThreshold P cfg.ε (lVec e) := by
      have hEpsEq' : cfg.ε = (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P := by
        simpa [Int.cast_pow, Int.cast_ofNat] using hEpsEq
      rw [← hEpsEq', hlNewReal]
    refine ⟨hG0Cap ei_old hOldG, hRootG0.2.2.1 ei_old hOldG, heLtM, (hG0'Cap _ hNewG0').2,
      by dsimp only [lNew]; omega,
      fun ei2 h2G h2Del hEq => ((hSurvAll ei2 h2G).mp (hEq ▸ hNewG0')) h2Del,
      fun ei2 h2G h2Del hne hEq => by
        have h2Ext : tr.2.2.1 ei2 ∈ model.extG.E := by
          rw [hI2EOldAll ei2 (hFreshInv.hLtFresh _ h2G)]; exact (hFreshInv.hRight ei2 h2G).2
        have hSame := (hFreshTr.hLeft _ h2Ext).symm.trans (hEq ▸ hFreshTr.hLeft e heExt)
        rw [hI2EOldAll ei2 (hFreshInv.hLtFresh _ h2G), heEq] at hSame
        exact hne ((hFreshInv.hRight ei2 h2G).1.symm.trans (hSame ▸ hE2I)),
      hCanon.1, hOff.1, hThrAtSt, hDetOldEq,
      ⟨fun j hj => by rw [hStG (by omega) (by omega)]; exact hGV j hj,
       by dsimp only [gNew]; exact Num.intVal_congr (fun j hj => hStG (by omega) (by omega))⟩,
      ⟨fun j hj => by rw [hStL (by omega) (by omega)]; exact hLV j hj,
       by rw [hlNewEq]; exact Num.intVal_congr (fun j hj => hStL (by omega) (by omega))⟩,
      hThrEq.symm ▸ hFitNT, hThrEq.symm ▸ hFitPT, hAccFits.2.1, hThrEq.symm ▸ hAccFits.2.2,
      hOff.2.1,
      by rw [hThrPtrEq]; have := htagLt (by rw [hThrTag (L - 1) (by omega)]; decide); omega,
      fun j hj => (hOff.2.2 j hj).1,
      fun j hj => by rw [hThrPtrEq]; exact hNoMutOfTag (hThrTag j hj) (by decide) (by decide)⟩
  have hNe11 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 1) : a ≠ root + 11 :=
    fun h => hv (ht.symm.trans (h ▸ hT1 11 (by omega)))
  have hH5St : st.mem (tok.handle + 5) = L :=
    (hStFixed (hT2 5 (by omega)) (by omega) (hNe11 (hT2 5 (by omega))
        (by decide))).trans (by simpa using hDetHdr0 5 (by simp))
  have hH8St : st.mem (tok.handle + 8) = P :=
    (hStFixed (hT2 8 (by omega)) (by omega) (hNe11 (hT2 8 (by omega))
        (by decide))).trans (by have := hNumHdr0 3 (by simp); simpa [Nat.add_assoc] using this)
  have hH16St : st.mem (tok.handle + 16) = epsExp :=
    (hStFixed (hT2 16 (by omega)) (by omega) (hNe11 (hT2 16 (by omega))
        (by decide))).trans (by have := hInitPar0 7 (by simp); simpa [Nat.add_assoc] using this)
  have hRootLeU : root + 16 ≤ uIntBuf :=
      by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleLeU : tok.handle + 18 ≤ uIntBuf :=
      by have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hRGLeU : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ uIntBuf := by
    have hpos : 0 < dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
    have := htagLt (by rw [hT20 (tok.rootGraph +
        dynGraphSize model.extG.n tok.rootECap - 1) (by omega) (by omega)]; decide); omega
  have hFwdLeU : tok.forward + m ≤ uIntBuf :=
      by have := htagLt (by rw [hT7 (m - 1) (by omega)]; decide); omega
  have hInvLeU : tok.inverse + tok.intCap ≤ uIntBuf :=
      by have := htagLt (by rw [hT8 (tok.intCap - 1) (by omega)]; decide); omega
  have hETLeU : tok.edgeThresholds + tok.intCap ≤ uIntBuf :=
      by have := htagLt (by rw [hT12 (tok.intCap - 1) (by omega)]; decide); omega
  have hERLeU : tok.edgeRecords + tok.intCap ≤ uIntBuf :=
      by have := htagLt (by rw [hT13 (tok.intCap - 1) (by omega)]; decide); omega
  have hOldLenLeU : oldLen0 + ec0 * L ≤ uIntBuf := by
    by_cases h0 : ec0 * L = 0
    · obtain ⟨_, _, _, _, hOwn0, _, _⟩ := hMetaLvls0 0 hdPos
      have hOwn0' : tok.owned oldLen0 := by simpa [oldLen0, lm, d] using hOwn0
      have := hFootLt oldLen0 (Or.inl hOwn0'); omega
    · have := htagLt (by rw [hTagOldLen0 (oldLen0 +
        ec0 * L - 1) (by omega) (by omega)]; omega); omega
  obtain ⟨_, _, hG0Valid, _, _, _, _⟩ :=
    translateBatch_preserves U model.extG G0 model.extToInt model.intToExt model.nextFresh hFreshInv
      hRef.1
  have hMutDisj : tok.edgeThresholds + tok.intCap ≤ tok.edgeRecords ∨
      tok.edgeRecords + tok.intCap ≤ tok.edgeThresholds := by
    by_contra h; push Not at h
    have h1 := hT12 (max tok.edgeThresholds tok.edgeRecords - tok.edgeThresholds) (by omega)
    have h2 := hT13 (max tok.edgeThresholds tok.edgeRecords - tok.edgeRecords) (by omega)
    rw [show tok.edgeThresholds + (max tok.edgeThresholds tok.edgeRecords - tok.edgeThresholds) =
        max tok.edgeThresholds tok.edgeRecords by omega] at h1
    rw [show tok.edgeRecords + (max tok.edgeThresholds tok.edgeRecords - tok.edgeRecords) =
        max tok.edgeThresholds tok.edgeRecords by omega] at h2; omega
  obtain ⟨heap2, outRef, cRef, rRefBody, hH2Lo, hH2Hi, hcRef, hzRef, hFrRef, hUnchRef, hDoneRef,
      hDisjRef⟩ :=
    wireRefreshAccountsBody_runs (w := w) (shift := shift) (negate := negate)
      (refreshOneProc := refreshOneProc) (divide := divide) (add := add) (sub := sub)
      (copy := copy) (isNeg := isNeg) (root := root) (uIntBuf := uIntBuf) (g := g) (l := l)
      (heap := heapSync) (m := m) (L := L) (P := P) (epsExp := epsExp) (pos := st.pos)
      (p := p) (ω := ω) (mem := st.mem) (G0 := G0) (U_int := U_int)
      (e2i' := tr.2.1) (i2e' := tr.2.2.1) (oldVal := canonVal) (oldThr := oldThr)
      (acc := accFn) (gNew := gNew) (lNew := lNew)
      hRefOneProc hshift hdiv hadd hsub hneg hcopy hisNeg
      hRootSt hH5St hH8St hH16St hDG0St hBatchSt hEdgeInt hFreshSt
      hLpos hPdiv hPword hEpsLe hFitPos hDelInfoSt
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hMutDisj
      ⟨fun j hj => hNoMutOfNotFoot (fun hf => by have := hFootLt _ hf; omega),
       fun j hj => hNoMutOfTag (hT20 (tok.rootGraph + j) (by omega) (by omega)) (by decide)
           (by decide),
       fun j hj => hNoMutOfTag (hT7 j hj) (by decide) (by decide),
       fun j hj => hNoMutOfTag (hT8 j hj) (by decide) (by decide),
       fun j hj => hNoMutOfNotFoot (hGDisj j hj),
       fun j hj => hNoMutOfNotFoot (hLDisj j hj)⟩
      (batchIsValid_delete_lt_ecap U_int G0 hG0Valid hBatchCaps hEdgeInt hRootG0.2.2.1)
      hzSync (by rw [hULenEq]; exact hRoom) (by omega)
  let s1 : State := { regs := Function.update st.regs 4 heap2, mem := outRef.mem, pos :=
      outRef.pos }
  have r1 : Runs w p ω (.call 4 refreshAccountsProc [.reg 70, .reg 87, .reg 90, .reg 91, .reg 4])
      st .normal s1 (5 + cRef + 1) :=
    runs_call_iff.mpr ⟨[root, uIntBuf, g, l, heapSync],
        wireRefreshAccountsBody shift negate refreshOneProc,
      .returned heap2, outRef, cRef,
      by simp [evalArgs, Expr.eval, hRegs.1, hRegs.2.1, hRegs.2.2.2.1, hRegs.2.2.2.2.1,
        hRegs.2.2.2.2.2.1],
      hRefAccProc, rRefBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hTagLM0 : tok.tag lm = 22 + d := by
    have := hTagMeta0 0 (by omega); simpa [lm, d] using this
  have hR4_s1 : s1.mem (root + 4) = tok.inverse :=
    (hFrRef (root + 4) (by omega) (hNoMutOfTag (hT1 4 (by omega)) (by decide) (by decide))).trans
      (by simpa using hRootSt 4 (by simp))
  have hLM0_s1 : s1.mem lm = oldLen0 :=
    (hFrRef lm (lt_of_lt_of_le (htagLt (by rw [hTagLM0]; omega)) (by omega))
      (hNoMutOfTag hTagLM0 (by omega) (by omega))).trans
      (hStFixed hTagLM0 (by omega) (hNe11 hTagLM0 (by omega)))
  let s4 := { s1 with regs := Function.update s1.regs 14 tok.inverse }
  let s5 := { s4 with regs := Function.update s4.regs 15 oldLen0 }
  have r4 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 70) (.const 4)))) s1 .normal s4 5 :=
    runs_assign_iff.mpr ⟨tok.inverse, by
      simp [Expr.eval, BinOp.eval, s1, hRegs.2.1, show 4 < 2 ^ w by omega,
        show root + 4 < 2 ^ w by omega]
      exact hR4_s1, rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 15 (.load (.reg 83))) s4 .normal s5 3 :=
    runs_assign_iff.mpr ⟨oldLen0, by
      simp [Expr.eval, s4, s1, hRegs.2.2.1]; exact hLM0_s1, rfl, rfl, rfl⟩
  have hBatch_s5 : IPM.Machine.BatchAt s5.mem uIntBuf U_int := fun j hj =>
    (hFrRef (uIntBuf + j) (by omega)
        (hNoMutOfNotFoot (fun hf => by have := hFootLt _ hf; omega))).trans
      (hBatchSt j hj)
  have hOldLen_s5 : EdgeValuesAt s5.mem oldLen0 4 L P G0.E model.chain.ℓ :=
    hOldLen0.congr fun e he t ht => by
      have heL : e * L + L ≤ ec0 * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hG0Ec0 e he))
      have hTag := hTagOldLen0 (oldLen0 + e * L + t) (by omega) (by omega)
      exact (hFrRef _ (by omega) (hNoMutOfTag hTag (by omega) (by omega))).trans
        (hStFixed hTag (by omega) (fun h => by rw [h, hT1 11 (by omega)] at hTag; omega))
  have hInvU5 : ∀ u ∈ U_int, match u with
      | .insert ei _ _ => ei < tok.intCap ∧ ei < ec0 ∧ s5.mem (tok.inverse + ei) = tr.2.2.1 ei ∧
          tr.2.2.1 ei < m ∧ Num.Valid s5.mem (l + tr.2.2.1 ei * L) 4 L ∧
          Num.fixVal s5.mem (l + tr.2.2.1 ei * L) 4 L P = ℓ' ei
      | _ => True := by
    intro u hu
    cases hU : u with
    | delete _ => trivial
    | split _ _ _ _ => trivial
    | insert ei x y =>
      have hEc := hInsEc0 u hu; rw [hU] at hEc
      have hRan := hRangeAll u hu; rw [hU] at hRan
      have hEiCap : ei < tok.intCap := lt_of_lt_of_le hRan.2 hTrNfLe
      obtain ⟨v, hvU, hvIns⟩ := translateBatch_insert_mem_ext U model.extG G0 model.extToInt
        model.intToExt model.nextFresh hFreshInv hRef.1 hEdgeU ei x y (hU ▸ hu)
      have heExt : tr.2.2.1 ei ∈ model.extG.E := by
        have hvR := hRef.2.2 v hvU
        cases v with
        | insert a _ _ => simp only [Update.Inserts] at hvIns; rw [← hvIns]; exact hvR.1
        | delete _ => simp [Update.Inserts] at hvIns
        | split _ _ _ _ => simp [Update.Inserts] at hvIns
      obtain ⟨hOldG, hOldDel, hOldI2E, _, _⟩ := hRepEdge (tr.2.2.1 ei) heExt ⟨v, hvU, hvIns⟩
      obtain ⟨_, hLV, _, hLEq, _, _, _, _, _, _⟩ := hRefInfo (model.extToInt (tr.2.2.1 ei))
          hOldG hOldDel
      rw [hOldI2E] at hLV hLEq
      have heLtM : tr.2.2.1 ei < m := hExtLtM _ heExt
      have heL : tr.2.2.1 ei * L + L ≤ m * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLtM)
      have hL5 (t : ℕ) (ht : t < L) : s5.mem (l + tr.2.2.1 ei * L + t) = mem0 (l +
          tr.2.2.1 ei * L + t) := by
        have hnf := hLDisj (tr.2.2.1 ei * L + t) (by omega)
        rw [show l + (tr.2.2.1 ei * L + t) = l + tr.2.2.1 ei * L + t by omega] at hnf
        exact (hFrRef _ (by omega) (hNoMutOfNotFoot hnf)).trans (hStL (by omega) (by omega))
      refine ⟨hEiCap, hEc, ?_, heLtM,
        fun t ht => by rw [hL5 t ht]; exact hLV t ht, ?_⟩
      · exact (hFrRef (tok.inverse + ei) (by omega)
          (hNoMutOfTag (hT8 ei hEiCap) (by decide) (by decide))).trans (hFreshSt.2.2 ei hEiCap)
      · unfold Num.fixVal
        rw [Num.intVal_congr hL5]
        exact hLEq
  have hAgreeOld5 : ∀ ei ∈ G0'.E, (¬ ∃ u ∈ U_int, u.Inserts ei) →
      ei ∈ G0.E ∧ model.chain.ℓ ei = ℓ' ei := by
    intro ei hei hNoIns
    have heiG0 : ei ∈ G0.E := mem_applyBatch_of_no_insert U_int G0 ei hei hNoIns
    obtain ⟨hE2I, heExt⟩ := hFreshInv.hRight ei heiG0
    have hI2E : tr.2.2.1 ei = model.intToExt ei := hI2EOldAll ei (hFreshInv.hLtFresh _ heiG0)
    have hNotDel : Update.delete ei ∉ U_int := (hSurvAll ei heiG0).mp hei
    have hNotInsExt : ¬ ∃ u ∈ U, u.Inserts (model.intToExt ei) := by
      have := hInsIffAll (model.intToExt ei) heExt (hTr1Eq.symm ▸ heExt)
      rw [hE2I] at this; exact this.mpr hNotDel
    refine ⟨heiG0, ?_⟩
    dsimp only [ℓ', lVec, updateOverlay]
    rw [hI2E, hEllEq0 ei heiG0]
    simp [heExt, hNotInsExt]
  have hMemIns5 : ∀ ei ∈ G0'.E, (∃ u ∈ U_int, u.Inserts ei) →
      ∃ k, ∃ hk : k < U_int.length, U_int[k].Inserts ei := by
    intro ei _ ⟨u, hu, hui⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
    exact ⟨k, hk, hui⟩
  have hDisjInvLen0 : 0 < ec0 → (tok.inverse + tok.intCap ≤ oldLen0 ∨ oldLen0 + ec0 * L ≤
      tok.inverse) := by
    intro hec0; have h0 : 0 < ec0 * L := Nat.mul_pos hec0 hLpos
    by_contra h; push Not at h
    have h1 := hT8 (max tok.inverse oldLen0 - tok.inverse) (by omega)
    have h2 := hTagOldLen0 (max tok.inverse oldLen0) (by omega) (by omega)
    rw [show tok.inverse + (max tok.inverse oldLen0 - tok.inverse) =
        max tok.inverse oldLen0 by omega] at h1; omega
  have hDisjLLen0 : 0 < ec0 → (l + m * L ≤ oldLen0 ∨ oldLen0 + ec0 * L ≤ l) := by
    intro hec0; have hmLPos : 0 < m * L := Nat.mul_pos hmPos hLpos
    have h0 : 0 < ec0 * L := Nat.mul_pos hec0 hLpos
    by_contra h; push Not at h
    have hnf := hLDisj (max l oldLen0 - l) (by omega)
    rw [show l + (max l oldLen0 - l) = max l oldLen0 by omega] at hnf
    exact hnf (Or.inl (hOwnOfTag _ (by rw [hTagOldLen0 _ (by omega) (by omega)]; omega)))
  obtain ⟨outLen, cLen, rLenBody, hcLen, hLen6, hFrLen⟩ :=
    wireUpdateLen0FromBatchBody_runs (w := w) (copyWords := copy) (uIntBuf := uIntBuf)
      (inverse := tok.inverse) (l := l) (len0Ptr := oldLen0) (L := L) (P := P) (m := m)
      (eCap := ec0) (intCap := tok.intCap) (pos := s5.pos) (p := p) (ω := ω) (mem := s5.mem)
      (G0 := G0) (U_int := U_int) (i2e := tr.2.2.1) (oldℓ := model.chain.ℓ) (newℓ := ℓ')
      hcopy hBatch_s5 hEdgeInt hInvU5 hOldLen_s5 hAgreeOld5 hMemIns5
      (Or.inr (by omega)) hDisjInvLen0 hDisjLLen0
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  let s6 : State := { regs := Function.update s5.regs 16 0, mem := outLen.mem, pos := outLen.pos }
  have r6 : Runs w p ω (.call 16 updateLen0Proc [.reg 87, .reg 14, .reg 91, .reg 15, .reg 94])
      s5 .normal s6 (5 + cLen + 1) :=
    runs_call_iff.mpr ⟨[uIntBuf, tok.inverse, l, oldLen0, L], wireUpdateLen0FromBatchBody copy,
      .returned 0, outLen, cLen,
      by simp [evalArgs, Expr.eval, s5, s4, s1, hRegs.2.2.2.1, hRegs.2.2.2.2.2.1,
        hRegs.2.2.2.2.2.2],
      hUpdLen0Proc, rLenBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have rAll : Runs w p ω (wireRefreshLen0Stmt refreshAccountsProc updateLen0Proc)
      st .normal s6 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5 + cRef + 1, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 3, 5 + cLen + 1, r5, r6, rfl⟩), rfl⟩), rfl⟩)
  let newCanonVal : ℕ → PathEdgeValue := fun ei =>
    if h : ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = ei then
      let ei_old := h.choose
      let e := tr.2.2.1 ei_old
      { forward := true, gradient := gNew e, length := (lNew e : ℤ),
        flow := (canonVal ei_old).flow, detector :=
            accFn ei_old - detectorThreshold P cfg.ε (lVec e) }
    else canonVal ei
  have hS6EqS1 {a : ℕ} (hL0 : a < oldLen0 ∨ oldLen0 + ec0 * L ≤ a) : s6.mem a = s1.mem a :=
    hFrLen a hL0
  have hS6GeSync (a : ℕ) (ha : heapSync ≤ a) : s6.mem a = s1.mem a :=
    hS6EqS1 (Or.inr (by omega))
  have hUnch6 : ∀ ei < tok.intCap,
      (¬ ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = ei) →
        s6.mem (tok.edgeThresholds + ei) = st.mem (tok.edgeThresholds + ei) ∧
        s6.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) := by
    intro ei hei hni
    have hu := hUnchRef ei hei hni
    exact ⟨(hS6EqS1 (hNotLen0OfTag (hT12 ei hei) (by omega))).trans hu.1,
      (hS6EqS1 (hNotLen0OfTag (hT13 ei hei) (by omega))).trans hu.2⟩
  have hNewOf {ei : ℕ} (hei : ei ∈ G0'.E) (hNot : ei ∉ G0.E) :
      ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = ei ∧
      s6.mem (tok.edgeThresholds + ei) = outRef.mem (tok.edgeThresholds + ei) ∧
      s6.mem (tok.edgeRecords + ei) = outRef.mem (tok.edgeRecords + ei) ∧
      heapSync + 3 * L ≤ s6.mem (tok.edgeRecords + ei) := by
    obtain ⟨hE2I, heExt⟩ := hFreshTr.hRight ei hei
    have hCap := (hG0'Cap ei hei).2
    have hIns : ∃ u ∈ U, u.Inserts (tr.2.2.1 ei) := by
      by_contra hni; obtain ⟨_, hEq, _, _, _⟩ := hUnchEdge _ heExt hni
      exact hNot (hE2I.symm.trans hEq ▸ hFreshInv.hE ▸ Finset.mem_image_of_mem _ heExt)
    obtain ⟨hOldG, hOldDel, hOldI2E, _, _⟩ := hRepEdge _ heExt hIns
    have hDone := hDoneRef (model.extToInt (tr.2.2.1 ei)) hOldG hOldDel
    dsimp only at hDone; rw [hOldI2E, hE2I] at hDone
    have hREq : s6.mem (tok.edgeRecords + ei) = outRef.mem (tok.edgeRecords + ei) :=
      hS6EqS1 (hNotLen0OfTag (hT13 ei hCap) (by omega))
    exact ⟨model.extToInt (tr.2.2.1 ei), hOldG, hOldDel, by rw [hOldI2E, hE2I],
      hS6EqS1 (hNotLen0OfTag (hT12 ei hCap) (by omega)),
      hREq, hREq ▸ hDone.2.2.1⟩
  have hOldOf {ei : ℕ} (hei : ei ∈ G0'.E) (hInG0 : ei ∈ G0.E) (hNotC : ei ∉ curE) :
      s6.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) ∧
      s6.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapSync := by
    obtain ⟨hE2I, heExt⟩ := hFreshTr.hRight ei hei
    have hNotIns : ¬ ∃ u ∈ U, u.Inserts (tr.2.2.1 ei) := fun hIns => by
      have hng := (hRepEdge _ heExt hIns).2.2.2.1; rw [hE2I] at hng; exact hng hInG0
    obtain ⟨_, hEq, _, _, hNoRef⟩ := hUnchEdge _ heExt hNotIns
    have hU := hUnch6 ei (hG0'Cap ei hei).2 ((hE2I.symm.trans hEq) ▸ hNoRef)
    exact ⟨hU.2, hU.2 ▸ (hOffSynced.1 ei hInG0 (Or.inr hNotC)).2.1⟩
  refine ⟨s6, _, heap2, newCanonVal, rAll, ?_, by simp [s6, s5, s4, s1], hH2Lo,
    by rw [← hULenEq]; exact hH2Hi, fun a ha => (hS6GeSync a (by omega)).trans (hzRef a ha),
    fun r hr => by simp [s6, s5, s4, s1, Function.update_of_ne (by omega : r ≠ 16),
      Function.update_of_ne (by omega : r ≠ 15), Function.update_of_ne (by omega : r ≠ 14),
      Function.update_of_ne (by omega : r ≠ 4)],
    hLen6, fun a ha hnm hL0 => (hS6EqS1 hL0).trans (hFrRef a ha hnm),
    hUnch6, ?_, ?_, ?_⟩
  · rw [hULenEq] at hcRef hcLen; omega
  · intro e he
    set ei := tr.2.1 e
    by_cases hIns : ∃ u ∈ U, u.Inserts e
    · obtain ⟨hOldG, hOldDel, hOldI2E, hNotG0, _⟩ := hRepEdge e he hIns
      have hEx : ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = ei :=
        ⟨model.extToInt e, hOldG, hOldDel, by rw [hOldI2E]⟩
      have hChEq : hEx.choose = model.extToInt e := by
        obtain ⟨hCG, hCD, hCEq⟩ := hEx.choose_spec
        by_contra hne
        exact (hDelInfoSt (model.extToInt e)
            hOldG hOldDel).2.2.2.2.2.2.1 hEx.choose hCG hCD hne (by rw [hCEq, hOldI2E])
      have hVDef : newCanonVal ei = PathEdgeValue.mk true (gNew e) (lNew e : ℤ)
          (canonVal (model.extToInt e)).flow
          (accFn (model.extToInt e) - detectorThreshold P cfg.ε (lVec e)) := by
        simp only [newCanonVal, hEx, ↓reduceDIte, hChEq]
        have hI : tr.2.2.1 (model.extToInt e) = e := hOldI2E
        rw [hI]
      have hDone := hDoneRef (model.extToInt e) hOldG hOldDel; rw [hOldI2E] at hDone
      obtain ⟨_, _, hGEq, hLEq, hLPos, hgB, hlB, _, _, hAccB⟩ := hRefInfo (model.extToInt e)
          hOldG hOldDel
      rw [hOldI2E] at hGEq hLEq hLPos hgB hlB hAccB
      have hlNewEq : (lNew e : ℤ) = Num.intVal mem0 (l + e * L) 4 L := by dsimp only [lNew]; omega
      have hlNewReal : (lNew e : ℝ) / (2 : ℝ) ^ P = lVec e :=
          by rw [← Int.cast_natCast, hlNewEq]; exact hLEq
      have hCanon := hCanonExt e he
      have hAccSpec := hCanon.2.2.2.2.2.2.2.2.choose_spec
      have hAccFnEq : accFn (model.extToInt e) = hCanon.2.2.2.2.2.2.2.2.choose :=
          by simp [accFn, hFreshInv.hLeft e he, he]
      have hAccDetB := (hAccB (accFn (model.extToInt e)) (by rw [hAccFnEq]; exact hAccSpec.1)).1
      have hEiCap : ei < tok.intCap :=
          (hG0'Cap ei (hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 he)).2
      have hThrPtr6 : s6.mem (tok.edgeThresholds + ei) = outRef.mem (tok.edgeThresholds + ei) :=
        hS6EqS1 (hNotLen0OfTag (hT12 ei hEiCap) (by omega))
      have hRecPtr6 : s6.mem (tok.edgeRecords + ei) = outRef.mem (tok.edgeRecords + ei) :=
        hS6EqS1 (hNotLen0OfTag (hT13 ei hEiCap) (by omega))
      have hEpsEq' : cfg.ε = (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P := by
        simpa [Int.cast_pow, Int.cast_ofNat] using hEpsEq
      have hTLo : heapSync + 3 * L ≤ outRef.mem (tok.edgeThresholds + ei) := hDone.1
      have hRLo : heapSync + 3 * L ≤ outRef.mem (tok.edgeRecords + ei) := hDone.2.2.1
      have hThrAt6 : PathIntAt s6.mem (s6.mem (tok.edgeThresholds + ei))
          4 L (detectorThreshold P cfg.ε (lVec e)) := by
        rw [hThrPtr6, hEpsEq',
            ← hlNewReal]; exact hDone.2.2.2.2.1.congr (fun t ht => hS6GeSync _ (by omega))
      have hRecAt6 : PathEdgeAt s6.mem (s6.mem (tok.edgeRecords + ei))
          4 L (some (newCanonVal ei)) := by
        rw [hRecPtr6, hVDef, hEpsEq', ← hlNewReal]
        exact hDone.2.2.2.2.2.congr (fun a ha1 ha2 => hS6GeSync a (by omega))
      refine ⟨hThrAt6, by rw [hVDef], by rw [hVDef]; exact hgB,
        by rw [hVDef]; dsimp only; rw [hlNewEq]; exact hlB, by rw [hVDef]; exact hCanon.2.2.2.1,
        by rw [hVDef]; exact hAccDetB,
        by rw [hVDef]; simp only [PathEdgeValue.originalFlow, ↓reduceIte]
           simpa [PathEdgeValue.originalFlow, hCanon.1] using hCanon.2.2.2.2.2.1,
        by rw [hVDef]; simp only [PathEdgeValue.originalGradient, ↓reduceIte]; exact hGEq,
        by rw [hVDef]; dsimp only; rw [hlNewEq]; exact hLEq,
        ⟨accFn (model.extToInt e), by rw [hAccFnEq]; exact hAccSpec.1, by rw [hVDef]⟩,
        fun hInG0 => absurd hInG0 hNotG0,
        fun _ => ⟨by rw [hThrPtr6]; exact hDone.1, by rw [hThrPtr6]; exact hDone.2.1,
          by rw [hRecPtr6]; exact hDone.2.2.1, by rw [hRecPtr6]; exact hDone.2.2.2.1, hRecAt6⟩⟩
    · obtain ⟨_, hEiEq, _, _, hNoRef⟩ := hUnchEdge e he hIns
      have hEiEq' : ei = model.extToInt e := hEiEq
      have heiG0 : ei ∈ G0.E := by rw [hEiEq']; exact hFreshInv.hE ▸ Finset.mem_image_of_mem _ he
      have hNotEx : ¬ ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) =
          ei := by
        rw [hEiEq']; exact hNoRef
      have hVDef : newCanonVal ei = canonVal ei := by simp [newCanonVal, hNotEx]
      have hGVecEq : gVec e = model.extg e := by simp [gVec, updateOverlay, he, hIns]
      have hLVecEq : lVec e = model.extℓ e := by simp [lVec, updateOverlay, he, hIns]
      have hCanon := hCanonExt e he; rw [← hEiEq'] at hCanon
      have hEiCap : ei < tok.intCap := hG0Cap ei heiG0
      have hU6 := hUnch6 ei hEiCap hNotEx
      have hThrPtr6 : s6.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) :=
        hU6.1.trans (hStFixed (hT12 ei hEiCap) (by omega) (hNe11 (hT12 ei hEiCap) (by decide)))
      have hThrAt6 : PathIntAt s6.mem (s6.mem (tok.edgeThresholds + ei))
          4 L (detectorThreshold P cfg.ε (lVec e)) := by
        rw [hThrPtr6, hLVecEq]; have h0 := (hAccounts0.1 e he).2.1; rw [← hEiEq'] at h0
        exact h0.congr (fun j hj => by
          have htg : tok.tag (mem0 (tok.edgeThresholds + ei) + j) = 17 := by
            have := (hT1718 e he).1 j hj; rwa [← hEiEq'] at this
          exact (hS6EqS1 (hNotLen0OfTag htg (by omega))).trans
            ((hFrRef _ (lt_of_lt_of_le (htagLt (by rw [htg]; decide)) (by omega))
              (hNoMutOfTag htg (by decide) (by decide))).trans (hStFixed htg (by omega)
                  (hNe11 htg (by decide)))))
      refine ⟨hThrAt6, hVDef ▸ hCanon.1, hVDef ▸ hCanon.2.1, hVDef ▸ hCanon.2.2.1,
        hVDef ▸ hCanon.2.2.2.1, hVDef ▸ hCanon.2.2.2.2.1, hVDef ▸ hCanon.2.2.2.2.2.1,
        by rw [hVDef, hGVecEq]; exact hCanon.2.2.2.2.2.2.1,
        by rw [hVDef, hLVecEq]; exact hCanon.2.2.2.2.2.2.2.1,
        by
          obtain ⟨acc, ha, hd⟩ := hCanon.2.2.2.2.2.2.2.2
          exact ⟨acc, ha, by rw [hVDef, hLVecEq]; exact hd⟩,
        fun _ => ⟨hVDef, hThrPtr6, hU6.2, fun hNotCur => by
          rw [hU6.2, hVDef]; have hOff := hOffSynced.1 ei heiG0 (Or.inr hNotCur)
          exact hOff.1.congr (fun a ha1 ha2 => by
            have hD := hOff.2.2 (a - st.mem (tok.edgeRecords + ei)) (by omega)
            rw [show st.mem (tok.edgeRecords + ei) + (a - st.mem (tok.edgeRecords + ei)) =
                a by omega] at hD
            exact (hS6EqS1 hD.2).trans (hFrRef a (by omega) hD.1))⟩,
        fun hNotG0 => absurd heiG0 hNotG0⟩
  · intro ei₁ h1G' ei₂ h2G' hne h1Not h2Not
    by_cases h1 : ei₁ ∈ G0.E <;> by_cases h2 : ei₂ ∈ G0.E
    · rw [(hOldOf h1G' h1 h1Not).1,
        (hOldOf h2G' h2 h2Not).1]; exact hOffSynced.2 ei₁ h1 ei₂ h2 hne h1Not h2Not
    · have := (hOldOf h1G' h1 h1Not).2; obtain ⟨_, _, _, _, _, _, hGe2⟩ :=
        hNewOf h2G' h2; exact Or.inl (by omega)
    · obtain ⟨_, _, _, _, _, _, hGe1⟩ := hNewOf h1G' h1; have :=
        (hOldOf h2G' h2 h2Not).2; exact Or.inr (by omega)
    · obtain ⟨e1, h1O, h1D, h1M, _, h1Eq, _⟩ := hNewOf h1G' h1
      obtain ⟨e2, h2O, h2D, h2M, _, h2Eq, _⟩ := hNewOf h2G' h2
      have hd := (hDisjRef e1 h1O e2 h2O h1D h2D).1 (fun h => hne (h1M.symm.trans (h ▸ h2M)))
      rw [h1M, h2M] at hd; rw [h1Eq, h2Eq]; exact hd
  · intro ei₁ h1G' h1Not ei₂ h2G' h2Not
    obtain ⟨e1, h1O, h1D, h1M, h1TEq, _, _⟩ := hNewOf h1G' h1Not
    obtain ⟨e2, h2O, h2D, h2M, _, h2REq, _⟩ := hNewOf h2G' h2Not
    have hd := (hDisjRef e1 h1O e2 h2O h1D h2D).2; rw [h1M, h2M] at hd; rw [h1TEq, h2REq]; exact hd

end MinCostFlow.MinRatio

