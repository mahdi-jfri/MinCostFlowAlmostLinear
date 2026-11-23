module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopInvKFBL
import WordRAM.Tactic

/-!
# The invariant of the Branch B loop at the next level (`WireChainCoreBranchBLoopPassKFBL`)

From the clauses `BranchBPassOutKFBL` that one plain pass at level `idx` leaves, this file
rebuilds the invariant `BranchBLoopInvKFBL` at level `idx + 1` (`branchBLoopInvKFBL_pass`). The
core of level `idx` gets its new token, its slot joins the finished slots, the forwarded batch
and edits become the input of level `idx + 1`, and the frame of the step keeps every other word
that the invariant reads. The cost of the pass is stated against the potentials of all cores.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 4000000 in
/-- The invariant of the loop of Branch B at level `idx + 1` after a plain pass at `idx`, with
the model and size invariants at `idx + 1` and the cost of the pass. -/
theorem branchBLoopInvKFBL_pass
    {w L P depth vCap eCap capExp edMul wordExp stretchPrec idx rem curEnc N0 cost : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))}
    {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ}
    {BWc EWc ULc : ℕ → ℕ} {ch0 ch : ChainState cfg.T cfg.P} {termTok : RL.τ} {curG : MGraph}
    {curU : List Update} {curEditsList : List OrdEdit} {oldOrd : ℕ → List End} {st out : State}
    {tok : ℕ → Rcore.τ} {tok1 : Rcore.τ} {nextEdits : List OrdEdit} {c : Read.LSFChange}
    {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
    (hLoc : Rcore.Local) (hRLLoc : RL.Local)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
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
    (hOut : BranchBPassOutKFBL w L P vCap eCap capExp edMul Psc alloc reembFn A BWc EWc idx ch
      curU
      (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
        TreeChain).chainLen ℓ' idx)
      (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } :
        TreeChain).chainGrad g' idx)
      curBatch curBatchWords curEdits curEditsWords (tok idx) st out cost tok1 nextEdits c) :
    let Cp : TreeChain := { ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j }
    let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState
      ch.bran idx
    let upd := cfg.T.updateOrd (ch.scState idx) curU (Cp.chainLen ℓ' idx) (Cp.chainGrad g' idx)
      newOrd
    let nextU := upd.2 (ch.bran idx)
    let nextG := cfg.T.S upd.1 (ch.bran idx)
    let stN := updateLoopNext cfg ℓ' g' idx ch curG curU curEnc
    let tokN : ℕ → Rcore.τ := fun j => if j = idx then tok1 else tok j
    let DN : ℕ → LevelDiffLists := fun j => if j = idx then
      ⟨coreBatchTouchedEdges curU, c.fDel, coreBatchTouchedEdges nextU,
        reembFn (ch.scState idx) curU newOrd (ch.bran idx)⟩ else D j
    let UN : ℕ → List Update := fun j => if j = idx + 1 then nextU else levelU j
    let USN : ℕ → List Update := fun j => if j = idx then nextU else levelUS j
    BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok (idx + 1) stN nextG nextU nextEdits
      (cfg.T.rot (ch.scState idx) (ch.bran idx))
      { out with regs := Function.update out.regs 96 (idx + 1) } tokN (out.regs 10)
      (out.regs 11) (out.regs 12) (out.regs 13) UN USN DN ∧
    UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen ℓ' g'
      rem (idx + 1) stN nextG nextU 0 (cfg.T.rot (ch.scState idx) (ch.bran idx)) ∧
    UpdateLoopSizeInv cfg ℓ' g' edMul
      (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) BWc EWc ULc rem
      (idx + 1) stN nextG nextU 0 ∧
    cost + branchBPhiSum Rcore A tokN out.mem ≤
      branchBStepCostKFBL L capExp Psc cfg.P.k (levelM cfg.TP cfg.P idx) cfg.N₀ (BWc idx)
        (EWc idx) (cfg.T.cost (stN.scState idx) - cfg.T.cost (ch0.scState idx))
        (USN idx).length (DN idx).fDel.length (DN idx).reemb.length +
      branchBPhiSum Rcore A tok st.mem := by
  have hIdxLt : idx < cfg.P.d := by omega
  obtain ⟨hUCW, hBValid, hBCaps, hCurGEq, hCurGCap, hIfInv⟩ := hM
  subst hCurGEq
  have hNch : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hOver' : ¬ intRebuildThreshold cfg.P ch.N₀ idx < ch.updCount idx + curU.length := by
    rw [hNch]; exact hNotOver
  simp only [hOver', ↓reduceIte] at hIfInv
  obtain ⟨_, _, _, _, _, hNextInvM, hRecInv⟩ := hIfInv
  unfold UpdateLoopSizeInv at hSz
  simp only [hOver', ↓reduceIte] at hSz
  obtain ⟨hBWn, hEWn, hULn, hSzRec⟩ := hSz
  unfold BranchBPassOutKFBL at hOut
  obtain ⟨hLo, _, hz1, hReg70, hRep1, hFoot1, hDG1, hUC1, hNSB, hNDec, hNOE, hNRot, hNFor,
    hNValid, hNBLo, hNBHi, hNELo, hNEHi, hNBW, hNEW, hNEWle, hNLen, hFr, hEx, _, hLvl1,
    hCost⟩ := hOut
  intro Cp newOrd upd nextU nextG stN tokN DN UN USN
  obtain ⟨hFloor, hr10, hr11, hr12, hr13, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr82, hr83,
    hr85, hr86, hr94, hr95, hr96, hr97, hr98, hr99⟩ := I.regs
  obtain ⟨_, _, hBatchW, hBatchLo, hBatchHi, _, _, _, _, _, _⟩ := I.batch hIdxLt
  obtain ⟨hBW, hEW, _⟩ := I.sizes
  have hgLt : ∀ j < cfg.P.d, A.gPtr0 j + dynGraphSize vCap eCap ≤ A.selBase := S.gLt
  have hlLt : ∀ j < cfg.P.d, A.lPtr0 j + eCap * L ≤ A.selBase := S.lLt
  have hucLt := S.ucLt
  have hCoreSt := I.static idx hIdxLt
  beta_reduce at hCoreSt
  have hOldIdx := I.footOld idx le_rfl hIdxLt
  have hG0 : ch0.G idx = ch.G idx := (I.modelFrame.1 idx le_rfl).1.symm
  have hSc0 : ch0.scState idx = ch.scState idx := (I.modelFrame.1 idx le_rfl).2.symm
  have hBr0 : ch0.bran = ch.bran := I.modelFrame.2.1.symm
  -- the words that the step keeps
  have hKeepLow : ∀ a, a < A.selBase → ¬ Rcore.foot (A.coreH idx) (tok idx) a →
      (a < A.gPtr0 idx ∨ A.gPtr0 idx + dynGraphSize vCap eCap ≤ a) → a ≠ A.ucBase + idx →
      (idx + 1 < cfg.P.d → a < A.lPtr0 (idx + 1) ∨ A.lPtr0 (idx + 1) + eCap * L ≤ a) →
      out.mem a = st.mem a := fun a ha h0 hg hu hn =>
    hFr a (by omega) h0 hg hu hn (Or.inl (by omega))
  have hKeepS : ∀ a, BranchBStaticWord cfg.P.d A a → out.mem a = st.mem a := fun a ha => by
    obtain ⟨hlt, hnf, hgl, hnu⟩ := branchBStaticWord_off S I.static ha
    exact hKeepLow a hlt (hnf idx hIdxLt) (hgl idx hIdxLt).1 (hnu idx hIdxLt)
      (fun hlt' => (hgl (idx + 1) hlt').2)
  have hKeepFoot : ∀ j < cfg.P.d, j ≠ idx → ∀ a, Rcore.foot (A.coreH j) (tok j) a →
      out.mem a = st.mem a := fun j hj hne a ha => by
    have hst := I.static j hj
    beta_reduce at hst
    exact hFr a ((I.reps j hj).2 a ha) (fun hf => I.disj j hj idx hIdxLt hne a ha hf)
      (by by_contra h; exact hst.2.2.2.2.1 idx hIdxLt a (by omega) (by omega) ha)
      (fun h => (hst.2.2.2.1 idx hIdxLt).2.2.2.1 (h ▸ ha))
      (fun hlt => by by_contra h; exact hst.2.2.2.2.2 (idx + 1) hlt a (by omega) (by omega) ha)
      (by rcases I.footLoc j hj a ha with h | h <;> omega)
  have hKeepL : ∀ j < cfg.P.d, j ≠ idx + 1 → ∀ e, e < eCap → ∀ t < L,
      out.mem (A.lPtr0 j + e * L + t) = st.mem (A.lPtr0 j + e * L + t) :=
      fun j hj hne e he t ht => by
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
    have := hlLt j hj
    exact hKeepLow _ (by omega) (hCoreSt.2.2.2.2.2 j hj _ (by omega) (by omega))
      (by
        by_contra h
        have := ((S.gSep idx hIdxLt (A.lPtr0 j + e * L + t) (by omega) (by omega)).2.2.2.2.2.2.2.2
          j hj).1
        omega)
      (by
        rcases (S.lSep j hj (A.lPtr0 j + e * L + t) (by omega) (by omega)).2.2.2.2.2.2.2 with
          h | h <;> omega)
      (fun hlt => by rcases S.lPairSep j hj (idx + 1) hlt hne with h | h <;> omega)
  have hu : ∀ r, r ≠ 96 → Function.update out.regs 96 (idx + 1) r = out.regs r :=
    fun r h => Function.update_of_ne h _ _
  have hk : ∀ r, 70 ≤ r → r ≠ 96 → Function.update out.regs 96 (idx + 1) r = st.regs r :=
    fun r h1 h2 => (hu r h2).trans (hReg70 r h1)
  -- the abstract states of the cores in the next model state
  have hLvlOrdIdx : stN.levelOrd idx = newOrd := by
    unfold ChainState.levelOrd chainLevelOrd
    simp only [stN, newOrd, updateLoopNext]
    by_cases h0 : idx = 0
    · subst h0; simp [chainLevelOrd]
    · simp [h0, show idx - 1 ≠ idx by omega, chainLevelOrd]
  have hAbsIdx : chainLevelOrdAbs stN idx =
      ⟨upd.1, (ch.G idx).applyBatch curU, newOrd, ch.updCount idx + curU.length⟩ := by
    unfold chainLevelOrdAbs
    rw [hLvlOrdIdx]
    simp only [stN, updateLoopNext_G, updateLoopNext_scState, updateLoopNext_updCount,
      ↓reduceIte]
    rfl
  have hLvlOrdLt : ∀ j < idx, stN.levelOrd j = ch.levelOrd j := fun j hj => by
    unfold ChainState.levelOrd chainLevelOrd
    by_cases hj0 : j = 0
    · subst hj0; simp [stN, updateLoopNext_G, show (0 : ℕ) ≠ idx by omega]
    · simp [stN, updateLoopNext, hj0, show j - 1 ≠ idx by omega]
  have hStNextAbs : ∀ j < cfg.P.d, j ≠ idx → j ≠ idx + 1 →
      chainLevelOrdAbs stN j = chainLevelOrdAbs ch j := fun j hj hne hne1 => by
    unfold chainLevelOrdAbs ChainState.levelOrd chainLevelOrd
    simp only [stN, updateLoopNext, hne, ↓reduceIte]
    by_cases hj0 : j = 0
    · subst hj0; simp [hne]
    · simp [hj0, show j - 1 ≠ idx by omega]
  have hAbs1 : chainLevelOrdAbs ch (idx + 1) =
      ⟨ch.scState (idx + 1), ch.G (idx + 1), cfg.T.rot (ch.scState idx) (ch.bran idx),
        ch.updCount (idx + 1)⟩ := by
    unfold chainLevelOrdAbs ChainState.levelOrd chainLevelOrd
    simp
  have hLocJ : ∀ j < cfg.P.d, j ≠ idx →
      (Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) st.mem →
        Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) out.mem) ∧
      Rcore.phi (A.coreH j) (tok j) st.mem = Rcore.phi (A.coreH j) (tok j) out.mem :=
    fun j hj hne => hLoc (A.coreH j) (chainLevelOrdAbs ch j) (tok j) st.mem out.mem
      (fun a ha => (hKeepFoot j hj hne a ha).symm)
  have hRepOld : ∀ j < cfg.P.d, j ≠ idx →
      Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) st.mem := fun j hj hne => by
    have h := (I.reps j hj).1
    simp only [hne, ↓reduceIte] at h
    exact h
  have hlt4 : ∀ a, a < out.regs 4 → a < Function.update out.regs 96 (idx + 1) 4 :=
    fun a h => by rw [hu 4 (by decide)]; exact h
  refine ⟨{
      idxLe := (by omega)
      regs := ?_
      hdrCell := ?_
      n0Word := ?_
      cells := ?_
      termCells := ?_
      reps := ?_
      footLoc := ?_
      footOld := ?_
      disj := ?_
      static := ?_
      graphs := ?_
      lensLt := ?_
      lensEq := ?_
      lensGt := ?_
      term := ?_
      batchLen := ?_
      batch := ?_
      sizes := ?_
      slots := ?_
      slotModel := ?_
      curULink := ?_
      modelFrame := ?_
      zero := ?_
      oldOrdEq := ?_
      updFrame := ?_
    }, hRecInv, hSzRec, ?_⟩
  -- regs
  · exact ⟨le_of_le_of_eq (by omega : A.heapFloor ≤ out.regs 4) (hu 4 (by decide)).symm,
      hu 10 (by decide), hu 11 (by decide), hu 12 (by decide), hu 13 (by decide),
      (hk 72 (by decide) (by decide)).trans hr72, (hk 73 (by decide) (by decide)).trans hr73,
      (hk 74 (by decide) (by decide)).trans hr74, (hk 75 (by decide) (by decide)).trans hr75,
      (hk 76 (by decide) (by decide)).trans hr76, (hk 77 (by decide) (by decide)).trans hr77,
      (hk 78 (by decide) (by decide)).trans hr78, (hk 82 (by decide) (by decide)).trans hr82,
      (hk 83 (by decide) (by decide)).trans hr83, (hk 85 (by decide) (by decide)).trans hr85,
      (hk 86 (by decide) (by decide)).trans hr86, (hk 94 (by decide) (by decide)).trans hr94,
      (hk 95 (by decide) (by decide)).trans hr95,
      (by simp : Function.update out.regs 96 (idx + 1) 96 = idx + 1),
      (hk 97 (by decide) (by decide)).trans hr97, (hk 98 (by decide) (by decide)).trans hr98,
      (hk 99 (by decide) (by decide)).trans hr99⟩
  -- hdrCell
  · obtain ⟨_, hN0Foot, hN0Sep⟩ := I.n0Word
    have := S.lvlMLt
    exact (hKeepLow _ (by omega) (hN0Foot idx hIdxLt) (hN0Sep idx hIdxLt).1
      (hN0Sep idx hIdxLt).2.2.1 (fun hlt' => (hN0Sep (idx + 1) hlt').2.1)).trans I.hdrCell
  -- n0Word
  · refine ⟨I.n0Word.1, fun j hj ha => ?_, I.n0Word.2.2⟩
    by_cases hje : j = idx
    · simp only [tokN, hje, ↓reduceIte] at ha
      rcases hFoot1 _ ha with h0 | ⟨h1, _⟩
      · exact I.n0Word.2.1 idx hIdxLt h0
      · have := S.lvlMLt; omega
    · simp only [tokN, hje, ↓reduceIte] at ha
      exact I.n0Word.2.1 j hj ha
  -- cells
  · intro j hj
    obtain ⟨hTab, hLvlMc, hHC, hBC, hBrLt, hCHW, hGC, hLC, hUCC, hRCC⟩ := I.cells j hj
    refine ⟨(hKeepS _ (by unfold BranchBStaticWord; omega)).trans hTab,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans hLvlMc,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans hHC,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans hBC, hBrLt, hCHW,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans hGC,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans hLC, ?_,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans hRCC⟩
    rw [show stN.updCount j = (if j = idx then ch.updCount idx + curU.length else ch.updCount j)
      from rfl]
    by_cases hje : j = idx
    · rw [ite_eq_left hje, hje]; exact hUC1
    · rw [ite_eq_right hje]
      refine (hKeepLow _ (by omega) (hCoreSt.2.2.2.1 j hj).2.2.2.1 ?_ (by omega) ?_).trans hUCC
      · by_contra h
        rcases (S.gSep idx hIdxLt (A.ucBase + j) (by omega) (by omega)).2.2.2.2.2.2.2.1 with
          h' | h' <;> omega
      · intro hlt
        by_contra h
        rcases (S.lSep (idx + 1) hlt (A.ucBase + j) (by omega) (by omega)).2.2.2.2.2.2.2 with
          h' | h' <;> omega
  -- termCells
  · exact ⟨(hKeepS _ (by unfold BranchBStaticWord; omega)).trans I.termCells.1,
      (hKeepS _ (by unfold BranchBStaticWord; omega)).trans I.termCells.2⟩
  -- reps
  · intro j hj
    by_cases hje : j = idx
    · have e1 : tokN j = tok1 := by simp only [tokN, hje, ↓reduceIte]
      rw [e1, ite_eq_right (by omega : ¬ j = idx + 1), hje, hAbsIdx]
      refine ⟨hRep1, fun a ha => hlt4 a ?_⟩
      rcases hFoot1 a ha with h0 | ⟨_, h⟩
      · exact ((I.reps idx hIdxLt).2 a h0).trans_le hLo
      · exact h
    · have e1 : tokN j = tok j := by simp only [tokN, hje, ↓reduceIte]
      rw [e1]
      refine ⟨?_, fun a ha => hlt4 a (((I.reps j hj).2 a ha).trans_le hLo)⟩
      have hR := (hLocJ j hj hje).1 (hRepOld j hj hje)
      by_cases hje1 : j = idx + 1
      · subst hje1
        rw [ite_eq_left rfl]
        rw [hAbs1] at hR
        have eA : (⟨stN.scState (idx + 1), stN.G (idx + 1),
            cfg.T.rot (ch.scState idx) (ch.bran idx), stN.updCount (idx + 1)⟩ :
              SparseCoreOrdAbs cfg.T) =
            ⟨ch.scState (idx + 1), ch.G (idx + 1), cfg.T.rot (ch.scState idx) (ch.bran idx),
              ch.updCount (idx + 1)⟩ := by
          simp [stN, updateLoopNext_G, updateLoopNext_scState, updateLoopNext_updCount]
        rw [eA]; exact hR
      · rw [ite_eq_right hje1, hStNextAbs j hj hje hje1]; exact hR
  -- footLoc
  · intro j hj a ha
    by_cases hje : j = idx
    · simp only [tokN, hje, ↓reduceIte] at ha
      rcases hFoot1 a ha with h0 | ⟨h1, _⟩
      · exact I.footLoc idx hIdxLt a h0
      · exact Or.inr (by omega)
    · simp only [tokN, hje, ↓reduceIte] at ha
      exact I.footLoc j hj a ha
  -- footOld
  · intro j hj1 hj2 a ha
    simp only [tokN, show j ≠ idx by omega, ↓reduceIte] at ha
    exact I.footOld j (by omega) hj2 a ha
  -- disj
  · intro j₁ hj₁ j₂ hj₂ hne a ha1 ha2
    by_cases h1 : j₁ = idx
    · have h2 : j₂ ≠ idx := fun h => hne (h1.trans h.symm)
      simp only [tokN, h1, ↓reduceIte] at ha1
      simp only [tokN, h2, ↓reduceIte] at ha2
      rcases hFoot1 a ha1 with h0 | ⟨hlo, _⟩
      · exact I.disj idx hIdxLt j₂ hj₂ (Ne.symm h2) a h0 ha2
      · have := (I.reps j₂ hj₂).2 a ha2; omega
    · by_cases h2 : j₂ = idx
      · simp only [tokN, h2, ↓reduceIte] at ha2
        simp only [tokN, h1, ↓reduceIte] at ha1
        rcases hFoot1 a ha2 with h0 | ⟨hlo, _⟩
        · exact I.disj j₁ hj₁ idx hIdxLt h1 a ha1 h0
        · have := (I.reps j₁ hj₁).2 a ha1; omega
      · simp only [tokN, h1, h2, ↓reduceIte] at ha1 ha2
        exact I.disj j₁ hj₁ j₂ hj₂ hne a ha1 ha2
  -- static
  · exact branchBCoresDisjStatic_update S (curHeap := st.regs 4) (by omega) I.static
      (fun a ha => (hFoot1 a ha).imp id And.left)
  -- graphs
  · intro j hj
    rw [show stN.G j = (if j = idx then (ch.G idx).applyBatch curU else ch.G j) from rfl]
    by_cases hje : j = idx
    · rw [ite_eq_left hje, hje]; exact hDG1
    · rw [ite_eq_right hje]
      exact dynGraphAt_of_agree (I.graphs j hj) (fun a ha1 ha2 =>
        hKeepLow a (by have := hgLt j hj; omega) (hCoreSt.2.2.2.2.1 j hj a ha1 ha2)
          (((S.gSep j hj a ha1 ha2).2.2.2.2.2.2.2.2 idx hIdxLt).2 (Ne.symm hje))
          (by rcases (S.gSep j hj a ha1 ha2).2.2.2.2.2.2.2.1 with h | h <;> omega)
          (fun hlt => ((S.gSep j hj a ha1 ha2).2.2.2.2.2.2.2.2 (idx + 1) hlt).1))
  -- lensLt
  · intro j hj
    have hLeq : stN.toTreeChain.chainLen ℓ' j =
        (if j = idx then Cp.chainLen ℓ' idx else ch.toTreeChain.chainLen ℓ' j) := by
      by_cases hje : j = idx
      · rw [ite_eq_left hje, hje]
        exact chainLen_congr_lt _ _ ℓ' idx (fun m hm => by
          simp [stN, Cp, updateLoopNext, TreeChain.activeLSF, ChainState.toTreeChain,
            show m < cfg.P.d by omega, show m ≠ idx by omega])
      · rw [ite_eq_right hje]
        exact chainLen_congr_lt _ _ ℓ' j (fun m hm => by
          simp [stN, updateLoopNext, TreeChain.activeLSF, ChainState.toTreeChain,
            show m < cfg.P.d by omega, show m ≠ idx by omega])
    rw [hLeq, show stN.G j = (if j = idx then (ch.G idx).applyBatch curU else ch.G j) from rfl]
    by_cases hje : j = idx
    · rw [ite_eq_left hje, ite_eq_left hje, hje]
      exact (I.lensEq hIdxLt).congr (fun e he t ht =>
        hKeepL idx hIdxLt (by omega) e (hCurGCap e he) t ht)
    · rw [ite_eq_right hje, ite_eq_right hje]
      exact (I.lensLt j (by omega)).congr (fun e he t ht =>
        hKeepL j (by omega) (by omega) e ((I.graphs j (by omega)).2.2.1 e he) t ht)
  -- lensEq
  · intro hlt
    obtain ⟨hGN, _, _⟩ := hNextInvM hlt
    have hNG : nextG = (ch.G (idx + 1)).applyBatch nextU := by
      cases rem with
      | zero => omega
      | succ _ => simpa [show idx + 1 ≠ idx by omega] using hRecInv.2.2.2.1
    have hL1 : ({ stN.toTreeChain with G := fun j => if j = idx + 1 then nextG else stN.G j } :
        TreeChain).chainLen ℓ' (idx + 1) =
        coreLen (cfg.T.lsfs upd.1 (ch.bran idx)) (Cp.chainLen ℓ' idx) := by
      simp only [TreeChain.chainLen, TreeChain.activeLSF, ChainState.toTreeChain, stN,
        updateLoopNext, hIdxLt, ↓reduceIte]
      congr 1
      exact chainLen_congr_lt _ _ ℓ' idx (fun m hm => by
        simp [Cp, TreeChain.activeLSF, ChainState.toTreeChain, show m < cfg.P.d by omega,
          show m ≠ idx by omega])
    have key : EdgeValuesAt out.mem (A.lPtr0 (idx + 1)) 4 L P nextG.E
        (coreLen (cfg.T.lsfs upd.1 (ch.bran idx)) (Cp.chainLen ℓ' idx)) := by
      rw [hNG, hGN]; exact hNLen hlt
    rw [← hL1] at key
    exact key
  -- lensGt
  · intro j hj1 hj2
    rw [show stN.G j = (if j = idx then (ch.G idx).applyBatch curU else ch.G j) from rfl,
      ite_eq_right (by omega)]
    exact (I.lensGt j (by omega) hj2).congr (fun e he t ht =>
      hKeepL j hj2 (by omega) e ((I.graphs j hj2).2.2.1 e he) t ht)
  -- term
  · have hKeepT : ∀ a, RL.foot (A.coreH cfg.P.d) termTok a → st.mem a = out.mem a :=
      fun a ha => by
        obtain ⟨h1, h2, h3, _, _, _, h7, _⟩ := I.term.2 a ha
        exact (hKeepLow a h1 (h2 idx hIdxLt) (h3 idx hIdxLt).1 (by rcases h7 with h | h <;> omega)
          (fun hlt => (h3 (idx + 1) hlt).2)).symm
    refine ⟨(hRLLoc _ (ch.lastK, ch.lastLSFs) _ _ _ hKeepT).1 I.term.1, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := I.term.2 a ha
    refine ⟨h1, fun j hj => ?_, h3, h4⟩
    by_cases hje : j = idx
    · simp only [tokN, hje, ↓reduceIte]
      intro hc
      rcases hFoot1 a hc with h0 | ⟨hlo, _⟩
      · exact h2 idx hIdxLt h0
      · omega
    · simp only [tokN, hje, ↓reduceIte]; exact h2 j hj
  -- batchLen
  · exact hNSB.1.2.1
  -- batch
  · intro hlt
    obtain ⟨hGN, _, _⟩ := hNextInvM hlt
    have hSG : stN.G (idx + 1) = cfg.T.S (ch.scState idx) (ch.bran idx) := by
      rw [show stN.G (idx + 1) = (if idx + 1 = idx then (ch.G idx).applyBatch curU
        else ch.G (idx + 1)) from rfl, ite_eq_right (by omega), hGN]
    rw [hSG]
    refine ⟨hNSB, hNDec, fun t ht => ⟨(hNBW t ht).1, fun j hj => ?_⟩, by omega,
      le_of_le_of_eq hNBHi (hu 4 (by decide)).symm, hNOE, fun t ht => (hNEW t ht).1,
      le_of_le_of_eq hNEHi (hu 4 (by decide)).symm, ?_, hNValid, hNFor⟩
    · by_cases hje : j = idx
      · simp only [tokN, hje, ↓reduceIte]; exact (hNBW t ht).2
      · simp only [tokN, hje, ↓reduceIte]
        intro hf
        have := (I.reps j hj).2 _ hf
        omega
    · unfold chainLevelOrd
      rw [ite_eq_right (by omega)]
      simp only [Nat.add_sub_cancel, stN, updateLoopNext_scState, ↓reduceIte]
      exact hNRot
  -- sizes
  · refine ⟨hNSB.2.trans hBWn, ?_, hULn⟩
    exact hNEWle.trans (le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (by omega)) _)) hEWn)
  -- slots
  · have hS0 : BranchBDoneSlots w P cfg.P.d
        (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
        (fun r => Rcore.foot (A.coreH r) (tok r)) A.heapFloor (st.regs 4) A.selBase st.mem idx DN
        ch0.G UN (fun j => (stN.G j).E)
        (fun j => (cfg.T.lsfs (stN.scState j) (stN.bran j)).wstr) := fun j hj => by
      have h := I.slots j hj
      simp only [DN, UN, stN, updateLoopNext_G, updateLoopNext_scState, show j ≠ idx by omega,
        show j ≠ idx + 1 by omega, ↓reduceIte]
      exact h
    have hnew := hLvl1.transfer
      (Good' := fun x => (st.regs 4 ≤ x ∧ ¬ Rcore.foot (A.coreH idx) (tokN idx) x) ∨
        (curBatch ≤ x ∧ x < curBatch + curBatchWords))
      (InTab' := fun x => Rcore.foot (A.coreH idx) (tokN idx) x ∨
        (st.regs 4 ≤ x ∧ x < out.regs 4))
      (mem' := out.mem) (lo' := curBatch) (hi' := out.regs 4) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a _ _ h => by simpa [tokN] using h) (fun a h => by simpa [tokN] using h) le_rfl le_rfl
    have hnew' : SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P idx) cfg.N₀)
        (fun x => (st.regs 4 ≤ x ∧ ¬ Rcore.foot (A.coreH idx) (tokN idx) x) ∨
          (curBatch ≤ x ∧ x < curBatch + curBatchWords))
        (fun x => Rcore.foot (A.coreH idx) (tokN idx) x ∨ (st.regs 4 ≤ x ∧ x < out.regs 4))
        curBatch (out.regs 4) out.mem (A.selBase + 1 + 12 * idx) (DN idx) (ch0.G idx) (UN idx)
        (stN.G idx).E (cfg.T.lsfs (stN.scState idx) (stN.bran idx)).wstr := by
      simp only [DN, UN, stN, updateLoopNext_G, updateLoopNext_scState, ↓reduceIte,
        show idx ≠ idx + 1 by omega, I.curULink, hG0]
      exact hnew
    have hS1 := BranchBDoneSlots.step (foot' := fun r => Rcore.foot (A.coreH r) (tokN r))
      (K := fun a => (a < A.gPtr0 idx ∨ A.gPtr0 idx + dynGraphSize vCap eCap ≤ a) ∧
        a ≠ A.ucBase + idx ∧
        (idx + 1 < cfg.P.d → a < A.lPtr0 (idx + 1) ∨ A.lPtr0 (idx + 1) + eCap * L ≤ a) ∧
        (a < A.selBase + 1 + 12 * idx ∨ A.selBase + 1 + 12 * idx + 12 ≤ a))
      hS0 hnew' hIdxLt hBatchLo hLo hFloor
      (fun x h1 h2 => ⟨by omega, by
        have := (hBatchW (x - curBatch) (by omega)).2
        rwa [show curBatch + (x - curBatch) = x by omega] at this⟩)
      (fun r hr x => by simp only [tokN, hr, ↓reduceIte])
      (fun x hx => by simp only [tokN, ↓reduceIte] at hx; exact hFoot1 x hx)
      (fun r hr x hx => (I.reps r hr).2 x hx)
      (fun x hx => by have := hOldIdx x hx; omega)
      (fun r hr hne x hx => I.disj r hr idx hIdxLt hne x hx)
      (fun a ha h0 hK => hFr a ha h0 hK.1 hK.2.1 hK.2.2.1 hK.2.2.2)
      (fun x h1 h2 => ⟨Or.inr (by have := hgLt idx hIdxLt; omega), by omega,
        fun hlt => Or.inr (by have := hlLt (idx + 1) hlt; omega), by omega⟩)
      (fun r hr hne x hx => by
        have hst := I.static r hr
        beta_reduce at hst
        exact ⟨by by_contra h; exact hst.2.2.2.2.1 idx hIdxLt x (by omega) (by omega) hx,
          fun h => (hst.2.2.2.1 idx hIdxLt).2.2.2.1 (h ▸ hx),
          fun hlt => by by_contra h; exact hst.2.2.2.2.2 (idx + 1) hlt x (by omega) (by omega) hx,
          by rcases I.footLoc r hr x hx with h | h <;> omega⟩)
      (fun j hj i hi => ⟨by omega, fun hf => by have := hOldIdx _ hf; omega,
        Or.inr (by have := hgLt idx hIdxLt; omega), by omega,
        fun hlt => Or.inr (by have := hlLt (idx + 1) hlt; omega), Or.inl (by omega)⟩)
    exact hS1
  -- slotModel
  · intro j hj
    by_cases hje : j = idx
    · rw [hje]
      have eD : DN idx = ⟨coreBatchTouchedEdges curU, c.fDel, coreBatchTouchedEdges nextU,
          reembFn (ch.scState idx) curU newOrd (ch.bran idx)⟩ := ite_eq_left rfl
      have eU : UN idx = curU := (ite_eq_right (by omega)).trans I.curULink
      have eU1 : UN (idx + 1) = nextU := ite_eq_left rfl
      have eUS : USN idx = nextU := ite_eq_left rfl
      have eSc : stN.scState idx = upd.1 := ite_eq_left rfl
      have eG : stN.G idx = (ch.G idx).applyBatch curU := ite_eq_left rfl
      rw [eD, eU, eU1, eUS, eSc, eG, hLvlOrdIdx, hG0, hSc0, hBr0]
      exact ⟨rfl, rfl, hEx.2.2.1, hEx.2.2.2, rfl, hBCaps, rfl, hBValid, rfl,
        Cp.chainLen ℓ' idx, Cp.chainGrad g' idx, newOrd, rfl, rfl⟩
    · have hjl : j < idx := by omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := I.slotModel j hjl
      have eD : DN j = D j := ite_eq_right hje
      have eU : UN j = levelU j := ite_eq_right (by omega)
      have eU1 : UN (j + 1) = levelU (j + 1) := ite_eq_right (by omega)
      have eUS : USN j = levelUS j := ite_eq_right hje
      have eSc : stN.scState j = ch.scState j := ite_eq_right hje
      have eG : stN.G j = ch.G j := ite_eq_right hje
      rw [eD, eU, eU1, eUS, eSc, eG, hLvlOrdLt j hjl]
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  -- curULink
  · exact ite_eq_left rfl
  -- modelFrame
  · refine ⟨fun j hj => ⟨?_, ?_⟩, I.modelFrame.2.1, I.modelFrame.2.2.1, I.modelFrame.2.2.2.1,
      I.modelFrame.2.2.2.2.1, I.modelFrame.2.2.2.2.2.1, I.modelFrame.2.2.2.2.2.2.1,
      I.modelFrame.2.2.2.2.2.2.2⟩
    · exact (ite_eq_right (show j ≠ idx by omega)).trans (I.modelFrame.1 j (by omega)).1
    · exact (ite_eq_right (show j ≠ idx by omega)).trans (I.modelFrame.1 j (by omega)).2
  -- zero
  · exact hz1
  -- oldOrdEq
  · rw [(I.modelFrame.1 idx le_rfl).2, I.modelFrame.2.1]
    simp [ChainState.levelOrd, chainLevelOrd]
  -- updFrame
  · intro j hj
    rw [show stN.updCount j = (if j = idx then ch.updCount idx + curU.length
      else ch.updCount j) from rfl, ite_eq_right (show j ≠ idx by omega)]
    exact I.updFrame j (by omega)
  -- cost
  · have hmem : idx ∈ Finset.range cfg.P.d := Finset.mem_range.mpr hIdxLt
    have hPhi : branchBPhiSum Rcore A tokN out.mem + Rcore.phi (A.coreH idx) (tok idx) st.mem =
        branchBPhiSum Rcore A tok st.mem + Rcore.phi (A.coreH idx) tok1 out.mem := by
      unfold branchBPhiSum
      rw [← Finset.add_sum_erase _ _ hmem,
        ← Finset.add_sum_erase _ (fun j => Rcore.phi (A.coreH j) (tok j) st.mem) hmem]
      have hRest : ((Finset.range cfg.P.d).erase idx).sum
          (fun j => Rcore.phi (A.coreH j) (tokN j) out.mem) =
          ((Finset.range cfg.P.d).erase idx).sum
            (fun j => Rcore.phi (A.coreH j) (tok j) st.mem) :=
        Finset.sum_congr rfl (fun j hj => by
          obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hj
          simp only [tokN, hne, ↓reduceIte]
          exact (hLocJ j (Finset.mem_range.mp hlt) hne).2.symm)
      rw [hRest]
      simp only [tokN, ↓reduceIte]
      omega
    have eUS : USN idx = nextU := ite_eq_left rfl
    have eDf : (DN idx).fDel = c.fDel := by simp only [DN, ↓reduceIte]
    have eDr : (DN idx).reemb = reembFn (ch.scState idx) curU newOrd (ch.bran idx) := by
      simp only [DN, ↓reduceIte]
    have eSc : stN.scState idx = upd.1 := ite_eq_left rfl
    rw [eUS, eDf, eDr, eSc, hSc0]
    have hC : cost + Rcore.phi (A.coreH idx) tok1 out.mem ≤
        branchBStepCostKFBL L capExp Psc cfg.P.k (levelM cfg.TP cfg.P idx) cfg.N₀ (BWc idx)
          (EWc idx) (cfg.T.cost upd.1 - cfg.T.cost (ch.scState idx)) nextU.length c.fDel.length
          (reembFn (ch.scState idx) curU newOrd (ch.bran idx)).length +
        Rcore.phi (A.coreH idx) (tok idx) st.mem := hCost
    omega

end MinCostFlow.MinRatio
