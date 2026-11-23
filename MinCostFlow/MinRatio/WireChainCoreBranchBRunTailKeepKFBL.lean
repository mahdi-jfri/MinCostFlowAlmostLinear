module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailBaseKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import WordRAM.Tactic

/-!
# The words below the select base across the head of Branch B (`WireChainCoreBranchBRunTailKeepKFBL`)

The suffix of Branch B reads two kinds of words that the head does not write: the word
`root + 15` of the root directory (the size of the name tables) and the internal batch at
`uIntBuf`. Both lie below the select base `heap`.

* `branchBLowWords_keep`: a word below `heap` whose tag is none of `4`, `5`, `20` and below `21`
  (when it lies below `uIntBuf`) keeps its value from the end `sP` of the prefix to the end of
  the exit. The front writes only above the heap floor, and the loop and the exit write only the
  cores (tags `21 + j`), the level arrays (tags `4`, `5`), the graphs and length blocks of the
  levels (tags `20`, `22 + d`, `23 + d`), and the select slots (above `heap`). This is the first
  half of the proof of `branchBMidWords_keep`.
* `BranchBRunHeadKFBL.low_keep`: such a word that is also not the count word `root + 11` and has
  a tag outside `6`, …, `16` keeps its value from the start memory `mem` to `sX`: the prefix
  writes only the tree state, the tag-`6`, `7`, `8` words, the accounts of the new names, the
  length block of level `0` and one word above `heap`.
* `intCap_sX`, `batch_sX`: the two facts that the suffix reads.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1600000 in
/-- The words below the select base `heap` with a tag outside `4`, `5`, `20` and below `21`
(below `uIntBuf`) keep their values from the end `sP` of the prefix to the end `out` of the exit
of Branch B. The premises are those of `branchBMidWords_keep`, without the frame of the exit
above the select slots. -/
theorem branchBLowWords_keep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap root uIntBuf g l heap heap2 : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    {sP s sE out : State} {tokE : ℕ → Rcore.τ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hFront : ∀ a < heap2, s.mem a = sP.mem a)
    (hh : heap ≤ heap2) (hs4 : heap2 ≤ s.regs 4)
    (hLoop : let A := branchBAddrsOf tok mem0 heap heap2
      ∀ a < s.regs 4, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok.coreTok j) a) →
      (∀ j < cfg.P.d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
        (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) →
      (∀ j < cfg.P.d, a ≠ A.ucBase + j) →
      (a < A.selBase ∨ A.selBase + 1 + 12 * cfg.P.d ≤ a) → sE.mem a = s.mem a)
    (hLoopFoot : let A := branchBAddrsOf tok mem0 heap heap2
      ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tokE j) a →
        Rcore.foot (A.coreH j) (tok.coreTok j) a ∨ (s.regs 4 ≤ a ∧ a < sE.regs 4))
    (hExit : let A := branchBAddrsOf tok mem0 heap heap2
      ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tokE j) a) →
      (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) →
      (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) →
      (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) → (a < A.rcBase ∨ A.rcBase + cfg.P.d ≤ a) →
      (∀ j < cfg.P.d, a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) →
      (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) → out.mem a = sE.mem a) :
    ∀ a < heap, (a < uIntBuf → tok.tag a ≠ 4 ∧ tok.tag a ≠ 5 ∧ tok.tag a ≠ 20 ∧ tok.tag a < 21) →
      out.mem a = sP.mem a := by
  intro a hLow hTag
  set A := branchBAddrsOf tok mem0 heap heap2 with hA
  set d := cfg.P.d with hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, _, _, _, hT4, hT5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, _, hMetaTag, _⟩ := hMeta0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := hModelInv
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := hFootLt x (Or.inl (hOwn x h))
  -- a word with a tag of the kinds the loop and the exit write is not `a`
  have hNo {x t : ℕ} (hx : x = a) (ht : tok.tag x = t) (h0 : t ≠ 0)
      (hT : t = 4 ∨ t = 5 ∨ t = 20 ∨ 21 ≤ t) : False := by
    subst hx
    have hl := hLt (by rw [ht]; exact h0)
    have h := hTag hl
    rw [ht] at h
    omega
  have hCapEq (j : ℕ) (hj : j < d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (hCaps0 j hj)
  have eCH (j : ℕ) (hj : j < d) : A.coreH j = tok.coreHandle j := by
    show (if j < d then tok.coreHandle j else tok.termHandle) = _
    simp [hj]
  have hCoreOff (j : ℕ) (hj : j < d) : ¬ Rcore.foot (A.coreH j) (tok.coreTok j) a := fun hf => by
    rw [eCH j hj] at hf
    exact hNo rfl (hT21 j hj a hf) (by omega) (by omega)
  have hGOff (j : ℕ) (hj : j < d) : a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    obtain ⟨hv, he⟩ := hCapEq j hj
    obtain ⟨_, _, _, _, hG⟩ := hLev j hj
    rw [hv, he] at hG
    have htag := (hG a hc.1 hc.2).1
    by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte] at htag; exact hNo rfl htag (by omega) (by omega)
    · simp only [h0, ↓reduceIte] at htag; exact hNo rfl htag (by omega) (by omega)
  have hLOff (j : ℕ) (hj : j < d) : a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    obtain ⟨_, he⟩ := hCapEq j hj
    obtain ⟨_, _, _, hL, _⟩ := hLev j hj
    rw [he] at hL
    exact hNo rfl (hL a hc.1 hc.2) (by omega) (by omega)
  have hUCOff (j : ℕ) (hj : j < d) : a ≠ A.ucBase + j := fun h =>
    hNo (x := tok.levelsEnd + (3 * (d + 1) + j)) (by rw [h]; show _ = tok.levelsEnd + _ + j; omega)
      (hT5 (3 * (d + 1) + j) (by omega)) (by omega) (by omega)
  have hS : s.mem a = sP.mem a := hFront a (by omega)
  have hE : sE.mem a = s.mem a :=
    hLoop a (by omega) hCoreOff (fun j hj => ⟨hGOff j hj, hLOff j hj⟩) hUCOff (Or.inl hLow)
  have hRange {x n t : ℕ} (hx : ∀ j < n, tok.tag (x + j) = t) (h0 : t ≠ 0)
      (hT : t = 4 ∨ t = 5 ∨ t = 20 ∨ 21 ≤ t) : a < x ∨ x + n ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    exact hNo (show x + (a - x) = a by omega) (hx (a - x) (by omega)) h0 hT
  have hHB := hRange (x := tok.handle + 18) (n := 2 * (d + 1)) hT4 (by omega) (by omega)
  have hLMr := hRange (x := A.levelMeta) (n := 2 * d) hMetaTag (by omega) (by omega)
  have hR5 := hRange (x := tok.levelsEnd) (n := 4 * (d + 1) + 1) hT5 (by omega) (by omega)
  have eHB : A.handleBase = tok.handle + 18 := rfl
  have eBB : A.branchBase = tok.handle + 18 + (d + 1) := rfl
  have eRC : A.rcBase = tok.levelsEnd + 2 * (d + 1) := rfl
  have eUC : A.ucBase = tok.levelsEnd + 3 * (d + 1) := rfl
  refine (hExit a hLow (fun j hj hf => ?_) (by omega) (by omega) hLMr (by omega)
    hGOff (by omega)).trans (hE.trans hS)
  rcases hLoopFoot j hj a hf with h | h
  · exact hCoreOff j hj h
  · omega

namespace BranchBRunHeadKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

set_option maxHeartbeats 800000 in
/-- A word below the select base `heap`, other than the count word `root + 11`, whose tag (below
`uIntBuf`) is `1`, `2`, `3`, `17`, `18` or `19`, keeps its value from the start memory `mem` to
the end `sX` of the exit. The prefix keeps it (its two frames: the word is not an account of a
name, not in the length block of level `0` and not the word `heap + 1 + 12 d + d`), and
`branchBLowWords_keep` gives the rest. -/
theorem low_keep {a : ℕ} (ha : a < heap) (h11 : a ≠ root + 11)
    (hT : a < uIntBuf → tok.tag a = 1 ∨ tok.tag a = 2 ∨ tok.tag a = 3 ∨ (17 ≤ tok.tag a ∧
      tok.tag a ≤ 19)) :
    Hd.sX.mem a = mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := Hd.start.rep0
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, hT9, _, _, hT12, hT13, _⟩ := hTags
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf :=
    Hd.start.footLt x (Or.inl (hOwn x h))
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := Hd.start.modelInv
  have hdPos : 0 < cfg.P.d := Hd.start.modelInv.1.1
  obtain ⟨hU, hh0, hS1h, hFl, _⟩ := heap_order Hd
  -- the frames of the prefix
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hMS1, hSP, _⟩ := Hd.pre
  have hTagA (h : a < uIntBuf) : tok.tag a ≠ 0 ∧ tok.tag a < 20 ∧ tok.tag a ≠ 9 ∧
      tok.tag a ≠ 12 ∧ tok.tag a ≠ 13 := by
    rcases hT h with h | h | h | h <;> omega
  have hSlot : ∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E → a ≠ tok.slots + ei ∧
      a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei := by
    intro ei hei _
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have := hT9 ei hei; rw [← he] at this
      have := (hTagA (hLt (by omega))).2.2.1; omega
    · have := hT12 ei hei; rw [← he] at this
      have := (hTagA (hLt (by omega))).2.2.2.1; omega
    · have := hT13 ei hei; rw [← he] at this
      have := (hTagA (hLt (by omega))).2.2.2.2; omega
  have hLM : a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
      mem0 (solverLevelMetaAddr tok.table cfg.P.d) + Hd.ec0 * L ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    have hCap := dynGraphAt_caps_eq (hLev 0 hdPos).1 (Hd.start.caps0 0 hdPos)
    obtain ⟨_, _, _, hL, _⟩ := hLev 0 hdPos
    rw [hCap.2, Nat.add_zero] at hL
    rw [Hd.ec0_eq] at hc
    have htag := hL a hc.1 hc.2
    have hl := hLt (by rw [htag]; omega)
    have := (hTagA hl).2.1
    omega
  have h1 : Hd.sP.mem a = Hd.memS1 a := hSP a (by omega) hSlot hLM
  have h2 : Hd.memS1 a = mem a := by
    rw [hMS1 a (by omega) h11 (fun h => by rcases hT h with h | h | h | h <;> omega)]
    exact Function.update_of_ne (by omega) _ _
  -- the front, the loop and the exit
  obtain ⟨_, _, hF4, hFr, _⟩ := Hd.front
  obtain ⟨_, _, _, _, _, _, _, _, hMem, _, _, _, _, _, hLFr, hLFoot, _⟩ := Hd.loop
  have hExit := Hd.exitOut.frame
  have hA := Hd.A_eq
  rw [hA] at hLFr hLFoot hExit
  have h3 : Hd.sX.mem a = Hd.sP.mem a :=
    branchBLowWords_keep (s := Hd.sF0) (sE := Hd.sE) (tokE := Hd.tokE) (heap2 := Hd.heap2)
      Hd.start.rep0 Hd.start.meta0 Hd.start.caps0 Hd.start.modelInv Hd.start.footLt hFr
      (by omega) (by omega)
      (fun a ha h1 h2 h3 h4 => by rw [← hMem]; exact hLFr a ha h1 h2 h3 h4) hLFoot hExit a ha
      (fun h => by rcases hT h with h | h | h | h <;> omega)
  rw [h3, h1, h2]

/-- The word `root + 15` holds the size of the name tables at the end of the exit (the premise
`hIntCap` of the suffix): it has tag `1`, so `low_keep` moves it from `mem`, where it holds the
value of `mem0` (`memEq`), the size `tok.intCap` in the root directory. -/
theorem intCap_sX : Hd.sX.mem (root + 15) = tok.intCap := by
  have hRep := Hd.start.rep0
  obtain ⟨hDir, _⟩ := hRep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := Hd.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  have ht : tok.tag (root + 15) = 1 := hT1 15 (by omega)
  have hlt : root + 15 < uIntBuf := Hd.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
  have hU := (heap_order Hd).1
  rw [low_keep Hd (by omega) (by omega) (fun _ => Or.inl ht),
    Hd.start.memEq _ hlt (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)]
  simpa using hDir 15 (by simp)

/-- The words of the internal batch at `uIntBuf` keep their values from `mem` to `sX`: they lie
in `[uIntBuf, editsPtr - d)`, below the select base. -/
theorem batch_keep {x : ℕ} (h1 : uIntBuf ≤ x) (h2 : x < uIntBuf + (editsPtr - cfg.P.d - uIntBuf)) :
    Hd.sX.mem x = mem x := by
  have hu := Hd.start.uLe
  have he := Hd.start.edHeap
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := Hd.start.rep0
  obtain ⟨_, hT1, _⟩ := hTags
  have hR : root + 11 < uIntBuf := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := Hd.start.rep0
    exact Hd.start.footLt _ (Or.inl (hTags.1 _ (by rw [hT1 11 (by omega)]; decide)))
  exact low_keep Hd (by omega) (by omega) (fun h => absurd h (by omega))

/-- The batch facts of the suffix at `sX`: the internal batch is at `uIntBuf` in the small
format over the old root graph, and its words fit in a word. -/
theorem batch_sX :
    SmallBatchAt Hd.sX.mem uIntBuf (model.chain.G 0) Hd.Uint (editsPtr - cfg.P.d - uIntBuf) ∧
    ∀ j < editsPtr - cfg.P.d - uIntBuf, Hd.sX.mem (uIntBuf + j) < 2 ^ w := by
  have hS := Hd.start.small
  rw [← Hd.Uint_eq] at hS
  refine ⟨smallBatchAt_congr hS fun x h1 h2 => batch_keep Hd h1 h2, fun j hj => ?_⟩
  rw [batch_keep Hd (by omega) (by omega)]
  have hRoom := Hd.start.room
  have hu := Hd.start.uLe
  have he := Hd.start.edHeap
  have hLen : U.length < 2 ^ w := by
    have := Hd.envA.ops.spaceTotalBranchB U.length
    omega
  exact branchB_batchWords_lt Hd.start.rep0 Hd.start.modelInv Hd.start.refresh Hd.start.trNf
    Hd.start.batch Hd.start.small Hd.start.footLt (by omega) hLen j hj

end BranchBRunHeadKFBL

end MinCostFlow.MinRatio
