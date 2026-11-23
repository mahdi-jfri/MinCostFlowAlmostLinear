module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopDefsKFBL
import WordRAM.Tactic

/-!
# One plain pass of the update loop of Branch B under `KFBL` (`WireChainCoreBranchBLoopRunKFBL`)

At the top of the loop at a level `idx < d` whose threshold test does not fire, the body runs the
plain step `wireBranchBStepKFBL` and moves `reg 96` to `idx + 1`. This file derives every
hypothesis of `wireBranchBStepKFBL_runs` from the loop invariant `BranchBLoopInvKFBL`, the model
invariant `UpdateLoopModelInv` and the size caps `UpdateLoopSizeInv`, and runs the body.

* `BranchBLoopEnvKFBL`: the fixed hypotheses on the program (the sparse core at every level, its
  companions, and the helper procedures).
* `branchBStepCostKFBL`: the cost of one pass, at the caps of the input words.
* `wireBranchBLoopBodyKFBL_runs_plain`: the run of one pass, with the post of the step lemma.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The fixed hypotheses on the program that every pass of the loop of Branch B uses. -/
structure BranchBLoopEnvKFBL (w L P depth vCap eCap capExp edMul initCore dgApply copyProc
    updLen slotProc collectProc edgeProc signExt mul intDiv copy : ℕ) (fmt : Num.Format w)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (alloc : ℕ → List ℕ → ℕ)
    (Ginit : ℕ → MGraph) (reembFn : ToolReembFn cfg.T) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (opCore : ℕ → ℕ) : Prop where
  loc : Rcore.Local
  four : fmt.limbBits = 4
  prec : fmt.precision = P
  w16 : 16 ≤ 2 ^ w
  updOrdEq : ToolUpdateOrdEqOnE cfg.T
  impl : ∀ j < cfg.P.d, Rcore.Implements w p initCore opCore
    (sparseCoreOrdMachineContractKFRBL fmt L depth cfg.T reembFn (Ginit j) cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc alloc)
  out : ∀ j < cfg.P.d, SparseCoreUpdateOutFootAt fmt L depth cfg.T (Ginit j) cfg.P.k
    (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc alloc edMul Rcore p opCore
  place : ∀ j < cfg.P.d, SparseCoreReembPlaceAt fmt L depth cfg.T (Ginit j) cfg.P.k
    (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc alloc Rcore p opCore
  footAt : ∀ j < cfg.P.d, SparseCoreReadoutFootAt fmt L depth cfg.T (Ginit j) cfg.P.k
    (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc alloc Rcore p opCore
  dgApplyC : ∀ (G : MGraph) (U : List Update) (bW : ℕ),
    MeetsContract w p dgApply (dgApplyBatchContract w vCap eCap G G U bW)
  copyP : p.procs[copyProc]? = some wireRawCopyBody
  slotP : p.procs[slotProc]? = some (wireSelOutSlotBody collectProc)
  collP : p.procs[collectProc]? = some wireCollectTouchedEdgesBody
  updLenP : p.procs[updLen]? = some (wireUpdateCoreLenFromBatchBody edgeProc)
  edgeP : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy)
  signC : MeetsContract w p signExt (Num.signExtendContract w 4)
  mulC : MeetsContract w p mul (Num.multiplyContract w 4)
  divC : MeetsContract w p intDiv (Num.integerDivideContract w 4)
  copyC : MeetsContract w p copy (copyWordsContract w)
  dW : cfg.P.d < 2 ^ w
  kW : cfg.P.k < 2 ^ w

/-- The cost of one plain pass at a level of sizes `(M, N)`, at the caps `bW`, `eW` of the input
words, with tool cost change `Δc`, `nU` forwarded updates and the lengths of the two copied
lists. -/
@[expose] def branchBStepCostKFBL (L capExp : ℕ) (Psc : SparseCoreOrdParams)
    (k M N bW eW Δc nU fDelLen reembLen : ℕ) : ℕ :=
  Psc.mul * (Δc + (k + 1) * (bW + eW + 1) * SparseCore.bundleLogFactor M N) + 700 * bW +
    20 * (fDelLen + reembLen) + Psc.readout +
    nU * (wireCoreLenEdgeCost (ordLevelLwMax L capExp M N) + 120) + 930

private theorem pass_cost_arith {cS phi1 phi0 X Y bW eW BW EW m F R Z k lg : ℕ}
    (h : cS + phi1 ≤ m * (X + (k + 1) * (bW + eW + 1) * lg) + 700 * bW + F + R + Z + 901 + phi0)
    (hb : bW ≤ BW) (he : eW ≤ EW) (hY : Y = X) :
    cS + 27 + phi1 ≤
      m * (Y + (k + 1) * (BW + EW + 1) * lg) + 700 * BW + F + R + Z + 930 + phi0 := by
  rw [hY]
  have h1 : (k + 1) * (bW + eW + 1) * lg ≤ (k + 1) * (BW + EW + 1) * lg :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h2 : m * (X + (k + 1) * (bW + eW + 1) * lg) ≤ m * (X + (k + 1) * (BW + EW + 1) * lg) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- What one plain pass at level `idx` leaves at the end state `out` of the step, before the move
of `reg 96`. These are the clauses of `wireBranchBStepKFBL_runs` at the addresses of the loop,
with the lengths `ℓi` and gradients `gi` of the level and with the cost at the caps `BWc idx`,
`EWc idx` of the input words. -/
@[expose] def BranchBPassOutKFBL (w L P vCap eCap capExp edMul : ℕ) {cfg : Alg2Config}
    (Psc : SparseCoreOrdParams) (alloc : ℕ → List ℕ → ℕ) {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (reembFn : ToolReembFn cfg.T) (A : BranchBAddrs) (BWc EWc : ℕ → ℕ) (idx : ℕ)
    (ch : ChainState cfg.T cfg.P) (curU : List Update) (ℓi gi : ℕ → ℝ)
    (curBatch curBatchWords curEdits curEditsWords : ℕ) (coreTok0 : Rcore.τ) (st out : State)
    (cost : ℕ) (coreTok' : Rcore.τ) (nextEdits : List OrdEdit) (c : Read.LSFChange) : Prop :=
  let M := levelM cfg.TP cfg.P idx
  let curHeap := st.regs 4
  let coreH := A.coreH idx
  let gPtr := A.gPtr0 idx
  let lPtr := A.lPtr0 idx
  let nextLPtr := A.lPtr0 (idx + 1)
  let curG := (ch.G idx).applyBatch curU
  let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
    ch.scState ch.bran idx
  let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
  let sc' := upd.1
  let nextU := upd.2 (ch.bran idx)
  let aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
  let args := [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap]
  let b := ch.bran idx
  let GS := cfg.T.S (ch.scState idx) b
  let reemb := reembFn (ch.scState idx) curU newOrd b
  let LwMax := ordLevelLwMax L capExp M cfg.N₀
  curHeap ≤ out.regs 4 ∧
  out.regs 4 ≤ curHeap + 3 * alloc 0 args + 7 + nextU.length * wireCoreLenEdgeSpace LwMax +
    curU.length + nextU.length ∧
  ZeroFrom out.mem (out.regs 4) ∧
  (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
  Rcore.rep coreH aNext coreTok' out.mem ∧
  (∀ a, Rcore.foot coreH coreTok' a →
    Rcore.foot coreH coreTok0 a ∨ (curHeap ≤ a ∧ a < out.regs 4)) ∧
  DynGraphAt out.mem gPtr vCap eCap curG ∧
  out.mem (A.ucBase + idx) = ch.updCount idx + curU.length ∧
  SmallBatchAt out.mem (out.regs 10) GS nextU (out.regs 11) ∧
  (decodeBatch out.mem (out.regs 10) GS).1 = nextU ∧
  OrdEditsAt out.mem (out.regs 12) nextEdits (out.regs 13) ∧
  applyOrdEdits (cfg.T.rot (ch.scState idx) b) nextEdits = cfg.T.rot sc' b ∧
  OrdEditsForBatch GS nextU nextEdits ∧
  OrdEditsValidFor vCap eCap (cfg.T.rot (ch.scState idx) b) nextEdits ∧
  curHeap ≤ out.regs 10 ∧ out.regs 10 + out.regs 11 ≤ out.regs 4 ∧
  curHeap ≤ out.regs 12 ∧ out.regs 12 + out.regs 13 ≤ out.regs 4 ∧
  (∀ t < out.regs 11, out.mem (out.regs 10 + t) < 2 ^ w ∧
    ¬ Rcore.foot coreH coreTok' (out.regs 10 + t)) ∧
  (∀ t < out.regs 13, out.mem (out.regs 12 + t) < 2 ^ w ∧
    ¬ Rcore.foot coreH coreTok' (out.regs 12 + t)) ∧
  out.regs 13 ≤ edMul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
    (curBatchWords + curEditsWords + 1) * SparseCore.bundleLogFactor M cfg.N₀) ∧
  (idx + 1 < cfg.P.d →
    EdgeValuesAt out.mem nextLPtr 4 L P (GS.applyBatch nextU).E
      (coreLen (cfg.T.lsfs sc' b) ℓi)) ∧
  (∀ a < curHeap, ¬ Rcore.foot coreH coreTok0 a →
    (a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) → a ≠ A.ucBase + idx →
    (idx + 1 < cfg.P.d → a < nextLPtr ∨ nextLPtr + eCap * L ≤ a) →
    (a < A.selBase + 1 + 12 * idx ∨ A.selBase + 1 + 12 * idx + 12 ≤ a) →
    out.mem a = st.mem a) ∧
  c.Exact (cfg.T.lsfs (ch.scState idx) b) (cfg.T.lsfs sc' b) ∧ (∀ e ∈ c.fDel, e < 2 ^ w) ∧
  SelOutLevelMemAt w P LwMax
    (fun x => (curHeap ≤ x ∧ ¬ Rcore.foot coreH coreTok' x) ∨
      (curBatch ≤ x ∧ x < curBatch + curBatchWords))
    (fun x => Rcore.foot coreH coreTok' x ∨ (curHeap ≤ x ∧ x < out.regs 4))
    curBatch (out.regs 4) out.mem (A.selBase + 1 + 12 * idx)
    ⟨coreBatchTouchedEdges curU, c.fDel, coreBatchTouchedEdges nextU, reemb⟩ (ch.G idx) curU
    curG.E (cfg.T.lsfs sc' b).wstr ∧
  cost + Rcore.phi coreH coreTok' out.mem ≤
    branchBStepCostKFBL L capExp Psc cfg.P.k M cfg.N₀ (BWc idx) (EWc idx)
      (cfg.T.cost sc' - cfg.T.cost (ch.scState idx)) nextU.length c.fDel.length reemb.length +
    Rcore.phi coreH coreTok0 st.mem

set_option maxHeartbeats 3200000 in
/-- One plain pass of the loop at a level `idx < d` whose threshold test does not fire: the body
runs the step `wireBranchBStepKFBL` at the addresses of the invariant and moves `reg 96` to
`idx + 1`. The step leaves the clauses `BranchBPassOutKFBL`, and its heap grows by at most `space`,
the bound `hStepSp` at the caps of the level. -/
theorem wireBranchBLoopBodyKFBL_runs_plain
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy wordExp stretchPrec space idx rem curEnc N0 : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ}
    {BWc EWc ULc : ℕ → ℕ} {ch0 ch : ChainState cfg.T cfg.P} {termTok : RL.τ} {curG : MGraph}
    {curU : List Update} {curEditsList : List OrdEdit} {oldOrd : ℕ → List End} {st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hSum : idx + (rem + 1) = cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok idx ch curG curU curEditsList oldOrd st tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' (rem + 1) idx ch curG curU curEnc oldOrd)
    (hSz : UpdateLoopSizeInv cfg ℓ' g' edMul
      (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) BWc EWc ULc (rem + 1)
      idx ch curG curU curEnc)
    (hNotOver : ¬ intRebuildThreshold cfg.P N0 idx < ch.updCount idx + curU.length)
    (hStepSp : ∀ coreH gB bPtr bW ePtr eW lB h nU uL : ℕ, bW ≤ BWc idx → eW ≤ EWc idx →
      nU ≤ ULc (idx + 1) → uL ≤ ULc idx →
      3 * alloc 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
        nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P idx) cfg.N₀) +
        uL + nU ≤ space)
    (hRoom : st.regs 4 + space < 2 ^ w) :
    ∃ (out : State) (cost : ℕ) (tok1 : Rcore.τ) (nextEdits : List OrdEdit) (c : Read.LSFChange),
      Runs w p ω (wireBranchBLoopBodyKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
        st .normal { out with regs := Function.update out.regs 96 (idx + 1) } cost ∧
      out.regs 4 ≤ st.regs 4 + space ∧
      BranchBPassOutKFBL w L P vCap eCap capExp edMul Psc alloc reembFn A BWc EWc idx ch curU
        (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
          TreeChain).chainLen ℓ' idx)
        (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
          TreeChain).chainGrad g' idx)
        curBatch curBatchWords curEdits curEditsWords (tok idx) st out cost tok1 nextEdits c := by
  have hIdxLt : idx < cfg.P.d := by omega
  obtain ⟨hUCW, hBValid, hBCaps, hCurGEq, hCurGCap, hIfInv⟩ := hM
  subst hCurGEq
  have hNch : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hOver' : ¬ intRebuildThreshold cfg.P ch.N₀ idx <
      ch.updCount idx + curU.length := by rw [hNch]; exact hNotOver
  simp only [hOver', ↓reduceIte] at hIfInv
  obtain ⟨hInIdx, hOrdBatch, hUpdThresh, _, hLenPos, hNextInvM, hRecInv⟩ := hIfInv
  unfold UpdateLoopSizeInv at hSz
  simp only [hOver', ↓reduceIte] at hSz
  obtain ⟨_, _, hULn, _⟩ := hSz
  have hLvlIdx : ch.lvlM idx = levelM cfg.TP cfg.P idx := by
    rw [I.modelFrame.2.2.2.2.2.2.1]; exact hLvlM idx hIdxLt
  have hNcfg : ch.N₀ = cfg.N₀ := hNch.trans hN0
  rw [hLvlIdx, hNcfg] at hInIdx hUpdThresh
  obtain ⟨hFloor, hr10, hr11, hr12, hr13, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr82, hr83,
    hr85, hr86, hr94, hr95, hr96, hr97, hr98, hr99⟩ := I.regs
  obtain ⟨hTab, _, hHC, hBC, hBrLt, hCHW, hGC, hLC, hUCC, _⟩ := I.cells idx hIdxLt
  obtain ⟨hSmall, hDecode, hBatchW, hBatchLo, hBatchHi, hEditsAt, hEditsW, hEditsHi, hNewOrdEq,
    hValid, hBlocks⟩ := I.batch hIdxLt
  obtain ⟨hBW, hEW, hUL⟩ := I.sizes
  have hRep := (I.reps idx hIdxLt).1
  simp only [↓reduceIte] at hRep
  have hgLt : ∀ j < cfg.P.d, A.gPtr0 j + dynGraphSize vCap eCap ≤ A.selBase := S.gLt
  have hlLt : ∀ j < cfg.P.d, A.lPtr0 j + eCap * L ≤ A.selBase := S.lLt
  have hucLt := S.ucLt
  have hmetaLt := S.metaLt
  have htabLt := S.tableLt
  have hhbLt := S.hbLt
  have hbbLt := S.bbLt
  have hCoreSt := I.static idx hIdxLt
  have hOldIdx := I.footOld idx le_rfl hIdxLt
  -- the three loads and the test
  let sa := { st with regs := Function.update st.regs 16 curU.length }
  let sb := { sa with regs := Function.update sa.regs 17 (ch.updCount idx) }
  let sc := { sb with regs := Function.update sb.regs 18 (intRebuildThreshold cfg.P N0 idx) }
  have hsc : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → sc.regs r = st.regs r := fun r h1 h2 h3 => by
    simp [sc, sb, sa, Function.update, h1, h2, h3]
  have ra : Runs w p ω (.assign 16 (.load (.reg 10))) st .normal sa 3 :=
    runs_assign_iff.mpr ⟨curU.length, by simp [Expr.eval, hr10, I.batchLen], rfl, rfl, rfl⟩
  have rb : Runs w p ω (.assign 17 (.load (.bin .add (.reg 85) (.reg 96)))) sa .normal sb 5 :=
    runs_assign_iff.mpr ⟨ch.updCount idx, by
      simp [Expr.eval, BinOp.eval, sa, hr85, hr96,
        show A.ucBase + idx < 2 ^ w by omega, hUCC], rfl, rfl, rfl⟩
  have rc : Runs w p ω (.assign 18 (.load (.bin .add (.reg 74) (.reg 96)))) sb .normal sc 5 :=
    runs_assign_iff.mpr ⟨intRebuildThreshold cfg.P N0 idx, by
      simp [Expr.eval, BinOp.eval, sb, sa, hr74, hr96,
        show A.table + idx < 2 ^ w by omega, hTab], rfl, rfl, rfl⟩
  -- the step
  set ℓi := ({ ch.toTreeChain with
    G := (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j) } :
      TreeChain).chainLen ℓ' idx with hℓi
  set gi := ({ ch.toTreeChain with
    G := (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j) } :
      TreeChain).chainGrad g' idx with hgi
  have hNext : idx + 1 < cfg.P.d →
      let curG := (ch.G idx).applyBatch curU
      let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
        ch.scState ch.bran idx
      let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
      let GS := cfg.T.S (ch.scState idx) (ch.bran idx)
      EdgeValuesAt sc.mem (A.lPtr0 (idx + 1)) 4 L P GS.E (origLen (idx + 1)) ∧
      (∀ e ∈ GS.E, e < eCap) ∧
      (∀ u ∈ upd.2 (ch.bran idx), match u with
        | .insert e _ _ => e ∈ curG.E ∧ e < eCap ∧ e < eCap ∧
            (∃ q : ℤ, Num.Fits 4 L q ∧
              (q : ℝ) / (2 : ℝ) ^ P = coreLen (cfg.T.lsfs upd.1 (ch.bran idx)) ℓi e)
        | _ => True) ∧
      (∀ e ∈ (GS.applyBatch (upd.2 (ch.bran idx))).E,
        (¬ ∃ u ∈ upd.2 (ch.bran idx), u.Inserts e) →
        e ∈ GS.E ∧ origLen (idx + 1) e = coreLen (cfg.T.lsfs upd.1 (ch.bran idx)) ℓi e) := by
    intro hlt
    obtain ⟨hGN, hIns, hOld⟩ := hNextInvM hlt
    have hNG : cfg.T.S (cfg.T.updateOrd (ch.scState idx) curU ℓi gi
        (chainLevelOrd cfg.T (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j)
          ch.scState ch.bran idx)).1 (ch.bran idx) =
        (ch.G (idx + 1)).applyBatch ((cfg.T.updateOrd (ch.scState idx) curU ℓi gi
          (chainLevelOrd cfg.T (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j)
            ch.scState ch.bran idx)).2 (ch.bran idx)) := by
      cases rem with
      | zero => omega
      | succ _ => simpa [show idx + 1 ≠ idx by omega] using hRecInv.2.2.2.1
    dsimp only
    rw [← hGN]
    refine ⟨I.lensGt (idx + 1) (by omega) hlt, fun e he => (I.graphs (idx + 1) hlt).2.2.1 e he,
      hIns, fun e he hni => ?_⟩
    rw [← hNG] at he
    obtain ⟨h1, h2⟩ := hOld e he (fun u hu hins => hni ⟨u, hu, hins⟩)
    exact ⟨h1, h2.symm⟩
  obtain ⟨sStep, cStep, tok1, nextEdits, c, rStep, hStepLo, hStepHi, hzStep, hStepGe70, hRep1,
      _, hFoot1, hDG1, hUC1, hNextSB, hNextDec, hNextOE, hNextRot, hNextFor, hNextValid,
      hNextBLo, hNextBHi, hNextELo, hNextEHi, hNextBW, hNextEW, hNextEWle, hNextLen1, hFr1,
      hEx, hFDelW, hLvl1, hcStep⟩ :=
    wireBranchBStepKFBL_runs (M := levelM cfg.TP cfg.P idx) (N := cfg.N₀) (vCap := vCap)
      (eCap := eCap) (idx := idx) (coreH := A.coreH idx) (gPtr := A.gPtr0 idx)
      (lPtr := A.lPtr0 idx) (nextLPtr := A.lPtr0 (idx + 1)) (curBatch := curBatch)
      (curBatchWords := curBatchWords) (curEdits := curEdits) (curEditsWords := curEditsWords)
      (curHeap := st.regs 4) (handleBase := A.handleBase) (branchBase := A.branchBase)
      (levelMeta := A.levelMeta) (updCountBase := A.ucBase) (selBase := A.selBase)
      (ecNext := eCap) (Ginit := Ginit idx) (ω := ω) (st := sc)
      ch curU curEditsList oldOrd ℓi gi (origLen (idx + 1)) (tok idx) E.loc E.four E.prec
      E.w16 E.updOrdEq (E.impl idx hIdxLt) (E.out idx hIdxLt) (E.place idx hIdxLt)
      (E.footAt idx hIdxLt) (E.dgApplyC _ _ _) E.copyP E.slotP E.collP E.updLenP E.edgeP E.signC
      E.mulC E.divC E.copyC hIdxLt E.dW E.kW
      ⟨hsc 4 (by decide) (by decide) (by decide),
        (hsc 10 (by decide) (by decide) (by decide)).trans hr10,
        (hsc 11 (by decide) (by decide) (by decide)).trans hr11,
        (hsc 12 (by decide) (by decide) (by decide)).trans hr12,
        (hsc 13 (by decide) (by decide) (by decide)).trans hr13,
        (hsc 72 (by decide) (by decide) (by decide)).trans hr72,
        (hsc 75 (by decide) (by decide) (by decide)).trans hr75,
        (hsc 76 (by decide) (by decide) (by decide)).trans hr76,
        (hsc 77 (by decide) (by decide) (by decide)).trans hr77,
        (hsc 78 (by decide) (by decide) (by decide)).trans hr78,
        (hsc 83 (by decide) (by decide) (by decide)).trans hr83,
        (hsc 85 (by decide) (by decide) (by decide)).trans hr85,
        (hsc 94 (by decide) (by decide) (by decide)).trans hr94,
        (hsc 96 (by decide) (by decide) (by decide)).trans hr96⟩
      hHC hBC hBrLt hGC hLC (fun hlt => (I.cells (idx + 1) hlt).2.2.2.2.2.2.2.1) hUCC hUCW hCHW
      hRep hInIdx (I.reps idx hIdxLt).2 (I.graphs idx hIdxLt) hSmall hDecode hBValid hBCaps
      (fun t ht => (hBatchW t ht).1) hEditsAt hEditsW hValid hBlocks hNewOrdEq
      (by rw [hNewOrdEq]; exact hOrdBatch) hUpdThresh (I.lensEq hIdxLt) hCurGCap hLenPos hNext
      ⟨by omega, by omega, by omega, by omega, by have := hgLt idx hIdxLt; omega,
        by have := hlLt idx hIdxLt; omega, hBatchHi, hEditsHi⟩
      ⟨fun a ha1 ha2 =>
        ⟨hCoreSt.2.2.2.2.1 idx hIdxLt a ha1 ha2,
          by rcases (S.gSep idx hIdxLt a ha1 ha2).2.2.2.2.2.2.2.1 with h | h <;> omega,
          by have := hgLt idx hIdxLt; omega⟩,
        (hCoreSt.2.2.2.1 idx hIdxLt).2.2.2.1, by omega,
        fun t ht => (hBatchW t ht).2 idx hIdxLt⟩
      (fun x hx1 hx2 =>
        ⟨hCoreSt.2.2.2.2.2 idx hIdxLt x hx1 hx2,
          by
            by_contra h
            have := ((S.gSep idx hIdxLt x (by omega) (by omega)).2.2.2.2.2.2.2.2 idx hIdxLt).1
            omega,
          by rcases (S.lSep idx hIdxLt x hx1 hx2).2.2.2.2.2.2.2 with h | h <;> omega⟩)
      (fun hlt =>
        ⟨by have := hlLt (idx + 1) hlt; omega, S.lPairSep idx hIdxLt (idx + 1) hlt (by omega),
          fun x hx1 hx2 =>
            ⟨hCoreSt.2.2.2.2.2 (idx + 1) hlt x hx1 hx2,
              by
                by_contra h
                have := ((S.gSep idx hIdxLt x (by omega) (by omega)).2.2.2.2.2.2.2.2 (idx + 1)
                  hlt).1
                omega,
              by rcases (S.lSep (idx + 1) hlt x hx1 hx2).2.2.2.2.2.2.2 with h | h <;> omega⟩,
          (hCoreSt.2.2.2.1 (idx + 1) hlt).2.1,
          by
            by_contra h
            have := (S.gSep idx hIdxLt (A.levelMeta + (idx + 1)) (by omega) (by omega)).2.2.2.2.2.1
            omega,
          by rcases S.sepUCLM with h | h <;> omega,
          fun t ht => by have := hlLt (idx + 1) hlt; omega⟩)
      (by omega)
      (fun i hi => ⟨fun hf => by have := hOldIdx _ hf; omega, by omega,
        fun hlt => by have := hlLt (idx + 1) hlt; omega,
        by have := hgLt idx hIdxLt; omega, by omega⟩)
      I.zero
      (by
        dsimp only
        have := hStepSp (A.coreH idx) (A.gPtr0 idx) curBatch curBatchWords curEdits curEditsWords
          (A.lPtr0 idx) (st.regs 4) _ curU.length hBW hEW hULn hUL
        omega)
  -- the move of `reg 96` and the body
  let sInc := { sStep with regs := Function.update sStep.regs 96 (idx + 1) }
  have h96 : sStep.regs 96 = idx :=
    (hStepGe70 96 (by decide)).trans ((hsc 96 (by decide) (by decide) (by decide)).trans hr96)
  have rInc : Runs w p ω (.assign 96 (.bin .add (.reg 96) (.const 1))) sStep .normal sInc 4 :=
    runs_assign_iff.mpr ⟨idx + 1, by
      simp [Expr.eval, BinOp.eval, h96, show 1 < 2 ^ w by have := E.w16; omega,
        show idx + 1 < 2 ^ w by have := E.dW; omega], rfl, rfl, rfl⟩
  have rBody : Runs w p ω
      (wireBranchBLoopBodyKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
      st .normal sInc (3 + (5 + (5 + (5 + (cStep + 4 + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨sa, 3, _, ra,
      runs_seq_iff.mpr (Or.inr ⟨sb, 5, _, rb,
        runs_seq_iff.mpr (Or.inr ⟨sc, 5, _, rc,
          runs_cond_iff.mpr ⟨0, cStep + 4 + 1,
            by simp [Expr.eval, BinOp.eval, sc, sb, sa, hUCW, hNotOver],
            by simpa using runs_seq_iff.mpr (Or.inr ⟨sStep, cStep, 4, rStep, rInc, rfl⟩),
            by simp [Expr.size]⟩, rfl⟩), rfl⟩), rfl⟩)
  have hSpace : sStep.regs 4 ≤ st.regs 4 + space := by
    have := hStepSp (A.coreH idx) (A.gPtr0 idx) curBatch curBatchWords curEdits curEditsWords
      (A.lPtr0 idx) (st.regs 4) _ curU.length hBW hEW hULn hUL
    omega
  refine ⟨sStep, _, tok1, nextEdits, c, rBody, hSpace, ?_⟩
  have hcS := pass_cost_arith (Y := cfg.T.cost (cfg.T.updateOrd (ch.scState idx) curU ℓi gi
      (chainLevelOrd cfg.T (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j)
        ch.scState ch.bran idx)).1 - cfg.T.cost (ch.scState idx)) hcStep hBW hEW rfl
  unfold BranchBPassOutKFBL
  dsimp only
  refine ⟨hStepLo, hStepHi, hzStep,
    fun r hr => (hStepGe70 r hr).trans (hsc r (by omega) (by omega) (by omega)), hRep1, hFoot1,
    hDG1, hUC1, hNextSB, hNextDec, hNextOE, hNextRot, hNextFor, hNextValid, hNextBLo, hNextBHi,
    hNextELo, hNextEHi, hNextBW, hNextEW, hNextEWle, hNextLen1, hFr1, hEx, hFDelW, hLvl1, ?_⟩
  have hPhi : Rcore.phi (A.coreH idx) (tok idx) sc.mem = Rcore.phi (A.coreH idx) (tok idx) st.mem :=
    rfl
  rw [hPhi] at hcS
  unfold branchBStepCostKFBL
  omega

end MinCostFlow.MinRatio
