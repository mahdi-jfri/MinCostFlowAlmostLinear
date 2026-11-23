module

public import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL
public import MinCostFlow.MinRatio.OrdBatchEditsValid
import WordRAM.Tactic

/-!
# The memory facts of the Branch B front, from the solver rep (`WireChainCoreBranchBFrontRepKFBL`)

The front of the Branch B loop (`wireBranchBFrontKFBL_runs`) reads the cells of the fixed arrays,
the reps of the level cores and of the terminal level, and the graphs and length blocks of the
levels. The solver rep at the start of the chain core gives all of them at `mem0`. Before the
front, Branch B writes only the words of the tree state, the words of the name tables and the
length block of level `0` (`wireBranchBPrefixKFBL_runs`). The words that the front reads have the
tags `3`, `4`, `5` or a tag of at least `19`, and only the length block of level `0` among them
changes.

`branchBFrontMem_of_rep` moves the facts from `mem0` to any memory `mem'` that agrees with `mem0`
on these words. Two blocks or words with different tags do not meet (`tag_point_sep`), and the
graphs and length blocks of the levels `j ≥ 1` lie apart from the length block of level `0` by the
layout part of `UpdateCoreModelInv`.

`branchBOldTermForest_of_rep` gives the cells of the terminal level and its old forest graph,
which the start of Branch B stores in the array of old forests for the exits of the loop.

`branchBLevel0Edits_of_rep` gives the facts on the edits of level `0` that the front needs: the
internal batch has only edge updates, its edits `batchToOrdEdits` take the sorted order of the
old root graph to the sorted order of the new one, they can be sent to the order store, and they
come in one block per update. The caps of the root graph are `(extG.n, rootECap)`.

`branchBPrefix_frontAgree` turns the two frames of `wireBranchBPrefixKFBL_runs` into the
agreement that `branchBFrontMem_of_rep` asks for.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1600000 in
/-- The facts that the front of the Branch B loop reads, at a memory `mem'` that agrees with
`mem0` on the words with tag `3`, `4`, `5` or at least `19`, except on the length block of
level `0` (`hAg`). The addresses are `branchBAddrsOf tok mem0 heap heapFloor`. -/
theorem branchBFrontMem_of_rep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap root uIntBuf g l heap
      heapFloor : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem' : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hLoc : Rcore.Local)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap)
    (hAg : ∀ a, (tok.tag a = 3 ∨ tok.tag a = 4 ∨ tok.tag a = 5 ∨ 19 ≤ tok.tag a) →
      (tok.tag a = 23 + cfg.P.d →
        a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a) →
      mem' a = mem0 a) :
    let A := branchBAddrsOf tok mem0 heap heapFloor
    let d := cfg.P.d
    let ch := model.chain
    mem' (A.lvlMTable - 1) = ch.N₀ ∧
    (∀ j < d,
      mem' (A.table + j) = intRebuildThreshold cfg.P cfg.N₀ j ∧
      mem' (A.lvlMTable + j) = ch.lvlM j ∧
      mem' (A.handleBase + j) = A.coreH j ∧
      mem' (A.branchBase + j) = ch.bran j ∧
      A.coreH j < uIntBuf ∧
      mem' (A.levelMeta + d + j) = A.gPtr0 j ∧
      mem' (A.levelMeta + j) = A.lPtr0 j ∧
      mem' (A.ucBase + j) = ch.updCount j ∧
      mem' (A.rcBase + j) = ch.rebuildCount j) ∧
    (mem' (A.handleBase + d) = A.coreH d ∧ mem' (A.branchBase + d) = ch.lastBran) ∧
    (∀ j < d, Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok.coreTok j) mem' ∧
      ∀ a, Rcore.foot (A.coreH j) (tok.coreTok j) a → a < A.selBase) ∧
    (∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ → ∀ a, Rcore.foot (A.coreH j₁) (tok.coreTok j₁) a →
      ¬ Rcore.foot (A.coreH j₂) (tok.coreTok j₂) a) ∧
    (∀ j < d, DynGraphAt mem' (A.gPtr0 j) vCap eCap (ch.G j)) ∧
    (∀ j, 0 < j → j < d →
      EdgeValuesAt mem' (A.lPtr0 j) 4 L P (ch.G j).E (ch.toTreeChain.chainLen ch.ℓ j)) ∧
    ((LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P (ch.G d).E).rep
        (A.coreH d) (ch.lastK, ch.lastLSFs) tok.termTok mem' ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
          (ch.G d).E).foot (A.coreH d) tok.termTok a →
        a < A.selBase ∧
        (∀ j < d, ¬ Rcore.foot (A.coreH j) (tok.coreTok j) a) ∧
        (∀ j < d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
          (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) ∧
        (a < A.handleBase ∨ A.handleBase + d < a) ∧
        (a < A.branchBase ∨ A.branchBase + d < a) ∧
        (a < A.levelMeta ∨ A.levelMeta + 2 * d ≤ a) ∧
        (a < A.ucBase ∨ A.ucBase + d ≤ a) ∧
        (a < A.rcBase ∨ A.rcBase + d < a))) := by
  intro A d ch
  obtain ⟨_, _, _, _, _, _, _, _, hSched, _, _, _, _, _, hCores, hTermH, hTermBr, hTermRep,
    hWire, hTags0⟩ := hRep0
  obtain ⟨hOwn, _, _, hT3, hT4, hT5, _, _, _, _, _, _, _, _, _, _, _, _, hT19, _, hT21⟩ :=
    hTags0
  obtain ⟨hTab, _⟩ := hWire
  obtain ⟨_, _, hRC, hUC, _⟩ := hSched
  obtain ⟨⟨hN0Val, hN0Tag, _, _⟩, hCoreOwn, hLvlMVal, hLvlMTag, hMetaTag, _⟩ := hMeta0
  obtain ⟨⟨hdPos, _⟩, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, hLPair, _⟩, _⟩ := hModelInv
  -- the addresses
  have eHB : A.handleBase = tok.handle + 18 := rfl
  have eBB : A.branchBase = tok.handle + 18 + (d + 1) := rfl
  have eM : A.lvlMTable = tok.table + (d + 1) + 1 := rfl
  have eLM : A.levelMeta = solverLevelMetaAddr tok.table d := rfl
  have eLM' : A.levelMeta = tok.table + (d + 1) + 1 + d := rfl
  have eRC : A.rcBase = tok.levelsEnd + 2 * (d + 1) := rfl
  have eUC : A.ucBase = tok.levelsEnd + 3 * (d + 1) := rfl
  have eS : A.selBase = heap := rfl
  have eG (j : ℕ) : A.gPtr0 j = mem0 (solverLevelMetaAddr tok.table d + d + j) := rfl
  have eL (j : ℕ) : A.lPtr0 j = mem0 (solverLevelMetaAddr tok.table d + j) := rfl
  have eCH (j : ℕ) (hj : j < d) : A.coreH j = tok.coreHandle j := by
    show (if j < d then tok.coreHandle j else tok.termHandle) = _
    simp [hj]
  have eCHd : A.coreH d = tok.termHandle := by
    show (if d < d then tok.coreHandle d else tok.termHandle) = _
    simp
  -- the tagged blocks
  have R4 : ∀ j < 2 * (d + 1), tok.tag (tok.handle + 18 + j) = 4 := hT4
  have R5 : ∀ j < 4 * (d + 1) + 1, tok.tag (tok.levelsEnd + j) = 5 := hT5
  have RLM : ∀ j < 2 * d, tok.tag (A.levelMeta + j) = 22 + d := hMetaTag
  have hLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwn a h))
  -- the caps of the graphs and length blocks are `vCap`, `eCap`
  have hCapEq (j : ℕ) (hj : j < d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (hCaps0 j hj)
  -- a word with a tag other than `23 + d` lies off the length block of level `0`
  have hAg' {a : ℕ} (h : tok.tag a = 3 ∨ tok.tag a = 4 ∨ tok.tag a = 5 ∨ 19 ≤ tok.tag a)
      (hne : tok.tag a ≠ 23 + d) : mem' a = mem0 a :=
    hAg a h (fun h' => absurd h' hne)
  -- the graph and length blocks of the levels
  have hGr (j : ℕ) (hj : j < d) (a : ℕ) (h1 : A.gPtr0 j ≤ a)
      (h2 : a < A.gPtr0 j + dynGraphSize vCap eCap) :
      tok.tag a = (if j = 0 then 20 else 23 + d) ∧
      (a < A.lPtr0 0 ∨ A.lPtr0 0 + eCap * L ≤ a) := by
    obtain ⟨hv, he⟩ := hCapEq j hj
    obtain ⟨_, _, _, _, hG⟩ := hLev j hj
    rw [hv, he] at hG
    obtain ⟨htag, hsep⟩ := hG a h1 h2
    refine ⟨htag, ?_⟩
    have hs := (hsep 0 hdPos).1
    rw [(hCapEq 0 hdPos).2] at hs
    simpa [eL] using hs
  have hLn (j : ℕ) (hj : j < d) (a : ℕ) (h1 : A.lPtr0 j ≤ a) (h2 : a < A.lPtr0 j + eCap * L) :
      tok.tag a = 23 + d := by
    obtain ⟨_, he⟩ := hCapEq j hj
    obtain ⟨_, _, _, hL, _⟩ := hLev j hj
    rw [he] at hL
    exact hL a h1 h2
  have hLnSep (j : ℕ) (hj0 : 0 < j) (hj : j < d) :
      A.lPtr0 j + eCap * L ≤ A.lPtr0 0 ∨ A.lPtr0 0 + eCap * L ≤ A.lPtr0 j := by
    have h := hLPair j hj 0 hdPos (by omega)
    rw [(hCapEq j hj).2, (hCapEq 0 hdPos).2] at h
    simpa [eL] using h
  -- the core footprints
  have hCore (r : ℕ) (hr : r < d) (a : ℕ) (ha : Rcore.foot (A.coreH r) (tok.coreTok r) a) :
      tok.tag a = 21 + r := by
    rw [eCH r hr] at ha
    exact hT21 r hr a ha
  -- the footprint of the terminal level
  have hTermTag (a : ℕ) (ha : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L
      P (ch.G d).E).foot (A.coreH d) tok.termTok a) : tok.tag a = 19 := by
    rw [eCHd] at ha
    exact hT19 a ha
  have hAgT {a t : ℕ} (ht : tok.tag a = t) (h : t = 3 ∨ t = 4 ∨ t = 5 ∨ 19 ≤ t)
      (hne : t ≠ 23 + d) : mem' a = mem0 a :=
    hAg' (by rw [ht]; exact h) (by rw [ht]; exact hne)
  refine ⟨?_, fun j hj => ?_, ⟨?_, ?_⟩, fun j hj => ⟨?_, fun a ha => ?_⟩,
    fun j₁ hj₁ j₂ hj₂ hne a ha hb => ?_, fun j hj => ?_, fun j hj0 hj => ?_, ?_, ?_⟩
  · -- the cell of `N₀`
    have e : A.lvlMTable - 1 = solverN0Addr tok.table d := by rw [eM]; rfl
    rw [e, hAgT hN0Tag (by omega) (by omega)]
    exact hN0Val
  · -- the cells of level `j`
    have c3 : tok.tag (A.table + j) = 3 := hT3 j (by omega)
    have cM : tok.tag (A.lvlMTable + j) = 21 + d := hLvlMTag j hj
    have c4h : tok.tag (A.handleBase + j) = 4 := R4 j (by omega)
    have c4b : tok.tag (A.branchBase + j) = 4 := by
      have := R4 (d + 1 + j) (by omega); rw [← add_assoc] at this; exact this
    have cLMg : tok.tag (A.levelMeta + d + j) = 22 + d := by
      have := RLM (d + j) (by omega); rw [← add_assoc] at this; exact this
    have cLMl : tok.tag (A.levelMeta + j) = 22 + d := RLM j (by omega)
    have c5u : tok.tag (A.ucBase + j) = 5 := by
      have := R5 (3 * (d + 1) + j) (by omega); rw [← add_assoc] at this; exact this
    have c5r : tok.tag (A.rcBase + j) = 5 := by
      have := R5 (2 * (d + 1) + j) (by omega); rw [← add_assoc] at this; exact this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAgT c3 (by omega) (by omega)]; exact hTab j (by omega)
    · rw [hAgT cM (by omega) (by omega)]; exact hLvlMVal j hj
    · rw [hAgT c4h (by omega) (by omega), eCH j hj]; exact (hCores j hj).1
    · rw [hAgT c4b (by omega) (by omega)]; exact (hCores j hj).2.1
    · rw [eCH j hj]; exact hFootLt _ (Or.inl (hCoreOwn j hj))
    · rw [hAgT cLMg (by omega) (by omega)]; rfl
    · rw [hAgT cLMl (by omega) (by omega)]; rfl
    · rw [hAgT c5u (by omega) (by omega)]; exact hUC j (by omega)
    · rw [hAgT c5r (by omega) (by omega)]; exact hRC j (by omega)
  · -- the cells of the terminal level
    have c4h : tok.tag (A.handleBase + d) = 4 := R4 d (by omega)
    rw [hAgT c4h (by omega) (by omega), eCHd]
    exact hTermH
  · have c4b : tok.tag (A.branchBase + d) = 4 := by
      have := R4 (d + 1 + d) (by omega); rw [← add_assoc] at this; exact this
    rw [hAgT c4b (by omega) (by omega)]
    exact hTermBr
  · -- the reps of the cores
    refine (hLoc _ _ _ _ _ (fun a ha =>
      (hAgT (hCore j hj a ha) (by omega) (by omega)).symm)).1 ?_
    rw [eCH j hj]
    exact (hCores j hj).2.2
  · have h1 := hCore j hj a ha
    have := hLt (a := a) (by omega)
    rw [eS]; omega
  · -- the cores are apart
    have h1 := hCore j₁ hj₁ a ha
    have h2 := hCore j₂ hj₂ a hb
    omega
  · -- the graphs
    have hG := hCaps0 j hj
    refine dynGraphAt_of_agree hG (fun x h1 h2 => ?_)
    obtain ⟨htag, hsep⟩ := hGr j hj x h1 h2
    refine hAg x ?_ (fun _ => by simpa [eL] using hsep)
    split_ifs at htag <;> omega
  · -- the length blocks of the levels `j ≥ 1`
    have hG := hCaps0 j hj
    refine ((hLev j hj).2.1).congr (fun e he t ht => ?_)
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hG.2.2.1 e he))
    have hin1 : A.lPtr0 j ≤ A.lPtr0 j + e * L + t := by omega
    have hin2 : A.lPtr0 j + e * L + t < A.lPtr0 j + eCap * L := by omega
    have htag := hLn j hj _ hin1 hin2
    have hsep := hLnSep j hj0 hj
    have e0 : A.lPtr0 0 = mem0 (solverLevelMetaAddr tok.table cfg.P.d) := by simp [eL]; rfl
    have ej : A.lPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) := rfl
    rw [e0, ej] at hsep
    rw [ej] at hin2 htag
    refine hAg _ (by rw [htag]; omega) (fun _ => ?_)
    omega
  · -- the rep of the terminal level
    refine (LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast 4 L P
      (ch.G d).E _ _ _ _ _ (fun a ha =>
        (hAgT (hTermTag a ha) (by omega) (by omega)).symm)).1 ?_
    rw [eCHd]
    exact hTermRep
  · -- the footprint of the terminal level misses the other blocks
    intro a ha
    have ht := hTermTag a ha
    refine ⟨?_, fun j hj hf => by have := hCore j hj a hf; omega, fun j hj => ⟨?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_⟩
    · have := hLt (a := a) (by omega); rw [eS]; omega
    · by_contra hc
      have := (hGr j hj a (by omega) (by omega)).1
      split_ifs at this <;> omega
    · by_contra hc
      have := hLn j hj a (by omega) (by omega)
      omega
    · rcases tag_point_sep R4 ht (by omega) with h | h <;> omega
    · rcases tag_point_sep R4 ht (by omega) with h | h <;> omega
    · rcases tag_point_sep RLM ht (by omega) with h | h <;> omega
    · rcases tag_point_sep R5 ht (by omega) with h | h <;> omega
    · rcases tag_point_sep R5 ht (by omega) with h | h <;> omega

/-- The old forest of the terminal level, from the solver rep at `mem0`. The handle of the
terminal level is at `handle + 18 + d` and its branch at `handle + 18 + (d + 1) + d`. The word
`termHandle + 1 + lastBran` holds the header `lsfHdr` of the active branch, and the word
`lsfHdr + 1` holds the pointer `forestPtr` to its forest graph. These two words and the graph lie
in the footprint `[termHandle, termTok)` of the terminal level, whose words have tag `19`. The
start of Branch B stores `forestPtr` in the array of old forests, and the exits of the loop read
the graph there. -/
theorem branchBOldTermForest_of_rep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec root g l : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B) :
    let d := cfg.P.d
    let lsfHdr := mem0 (tok.termHandle + 1 + model.chain.lastBran)
    let forestPtr := mem0 (lsfHdr + 1)
    mem0 (tok.handle + 18 + d) = tok.termHandle ∧
    mem0 (tok.handle + 18 + (d + 1) + d) = model.chain.lastBran ∧
    tok.tag (tok.termHandle + 1 + model.chain.lastBran) = 19 ∧
    tok.tag (lsfHdr + 1) = 19 ∧
    DynGraphAt mem0 forestPtr tok.vcLast tok.ecLast
      (model.chain.lastLSFs model.chain.lastBran).F.F ∧
    (∀ a, forestPtr ≤ a → a < forestPtr + dynGraphSize tok.vcLast tok.ecLast →
      tok.termHandle ≤ a ∧ a < tok.termTok ∧ tok.tag a = 19) := by
  intro d lsfHdr forestPtr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTermH, hTermBr, hTermRep, _, hTags0⟩ :=
    hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT19, _, _⟩ := hTags0
  obtain ⟨_, _, _, _, _, _, ⟨hLastLt, _⟩, _⟩ := hModelInv
  obtain ⟨hCnt, _, _, hBranches⟩ := hTermRep
  obtain ⟨hBW, hLSF⟩ := hBranches model.chain.lastBran hLastLt
  obtain ⟨hB1, hB2, _, _, hB5, hB6, _⟩ := hBW
  dsimp only at hCnt hB1 hB2 hB5 hB6
  have hFoot (a : ℕ) (h1 : tok.termHandle ≤ a) (h2 : a < tok.termTok) : tok.tag a = 19 :=
    hT19 a ⟨h1, h2⟩
  have hS1 : tok.termHandle + 1 + model.chain.lastBran < tok.termTok := by omega
  have hB5' : tok.termHandle + 1 + model.chain.lastK ≤ forestPtr := hB5
  have hB6' : forestPtr + dynGraphSize tok.vcLast tok.ecLast ≤ tok.termTok := hB6
  have hS2 : tok.termHandle ≤ lsfHdr + 1 ∧ lsfHdr + 1 < tok.termTok := ⟨by omega, by omega⟩
  refine ⟨hTermH, hTermBr, hFoot _ (by omega) hS1, hFoot _ hS2.1 hS2.2,
    hLSF.2.1, fun a h1 h2 => ⟨by omega, by omega, hFoot a (by omega) (by omega)⟩⟩

/-- The edits of level `0` in Branch B. The internal batch `U_int` of the update has only edge
updates. Its edits `batchToOrdEdits U_int` take the order of level `0` (the sorted ends of the
old root graph) to the sorted ends of the new root graph, they fit the order store at the caps
`(vCap, eCap)`, and they come in one block per update. The caps of level `0` are those of the
root graph in the rep. -/
theorem branchBLevel0Edits_of_rep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap root g l : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hRef : RefreshBatch model.extG U) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    vCap = model.extG.n ∧ eCap = tok.rootECap ∧
    (∀ u ∈ U_int, IsEdgeUpdate u) ∧
    applyOrdEdits (model.chain.levelOrd 0) (batchToOrdEdits U_int) =
      chainLevelOrd cfg.T (fun j => if j = 0 then G0.applyBatch U_int else model.chain.G j)
        model.chain.scState model.chain.bran 0 ∧
    OrdEditsValidFor vCap eCap (model.chain.levelOrd 0) (batchToOrdEdits U_int) ∧
    OrdEditsForBatch G0 U_int (batchToOrdEdits U_int) := by
  intro tr U_int G0
  obtain ⟨_, _, _, _, hFresh, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire, _⟩ := hRep0
  obtain ⟨_, hRootG, _⟩ := hWire
  obtain ⟨⟨hdPos, _⟩, _, _, _, _, _, _, _, ⟨hRootMeta, _⟩, hBatchCaps, _⟩ := hModelInv
  have hG0 : DynGraphAt mem0 tok.rootGraph vCap eCap G0 := by
    have h := hCaps0 0 hdPos
    rw [hRootMeta] at h
    exact h
  obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hG0 hRootG
  have hedgeExt : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have := hRef.2.2 u hu
    cases u with
    | split _ _ _ _ => exact this
    | insert _ _ _ => trivial
    | delete _ => trivial
  have hvalInt : G0.BatchIsValid U_int :=
    (translateBatch_preserves U model.extG G0 model.extToInt model.intToExt model.nextFresh
      hFresh hRef.1).2.2.1
  obtain ⟨hedgeInt, hfreshInt⟩ := translateBatch_freshIdsAlongBatch hFresh hRef.1 hedgeExt
  have hOrd : model.chain.levelOrd 0 = sortedEnds G0 := by
    simp [ChainState.levelOrd, chainLevelOrd, G0]
  have hcaps : BatchWithinCaps vCap eCap U_int := by
    rw [hvc, hec]; exact hBatchCaps
  refine ⟨hvc, hec, hedgeInt, ?_, ?_, ordEditsForBatch_batchToOrdEdits hedgeInt⟩
  · rw [hOrd, applyOrdEdits_sortedEnds_batch hedgeInt hfreshInt]
    simp [chainLevelOrd]
    rfl
  · rw [hOrd]
    exact ordEditsValidFor_batchToOrdEdits hG0.1 hG0.2.1 hG0.2.2.1 hvalInt hedgeInt hfreshInt
      hcaps

/-- The words that the front reads keep their values from `mem0` across the start of Branch B.
`hFr1` and `hFr2` are the two frames of `wireBranchBPrefixKFBL_runs`: below `h0` the start writes
only words with the tags of the tree state and the name tables, the word `root + 11` and the stored
old terminal forest at `heap + 1 + 12 d + d`; below `hS1` the refresh writes only the words of
names off the root graph and the length block of level `0`. Before the core, only words with tags
`6`, `7`, `8` changed (`hMemEq`). A word with tag `3`, `4`, `5` or at least `19` is none of these
(it lies below `uIntBuf`, and its tag differs from all of them), except a word of the length block
of level `0`. -/
theorem branchBPrefix_frontAgree
    {L P m V psi k epsExp drainUnit root uIntBuf heap h0 hS1 eCap forestPtr : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem memS1 memOut : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {G0 : MGraph}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap) (hHh0 : heap ≤ h0) (hh0 : h0 ≤ hS1)
    (hLen0Tag : ∀ a, mem0 (solverLevelMetaAddr tok.table cfg.P.d) ≤ a →
      a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L → tok.tag a = 23 + cfg.P.d)
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFr1 : ∀ a < h0, a ≠ root + 11 →
      (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
        tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
      memS1 a = Function.update mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) forestPtr a)
    (hFr2 : ∀ a < hS1, (∀ ei < tok.intCap, ei ∉ G0.E → a ≠ tok.slots + ei ∧
        a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
      (a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a) →
      memOut a = memS1 a) :
    ∀ a, (tok.tag a = 3 ∨ tok.tag a = 4 ∨ tok.tag a = 5 ∨ 19 ≤ tok.tag a) →
      (tok.tag a = 23 + cfg.P.d →
        a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a) →
      memOut a = mem0 a := by
  intro a ha hLen
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, hT1, _, _, _, _, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, _⟩ := hTags0
  have hne0 : tok.tag a ≠ 0 := by omega
  have haU : a < uIntBuf := hFootLt a (Or.inl (hOwn a hne0))
  have hR11 : a ≠ root + 11 := fun h => by
    have := hT1 11 (by omega); rw [← h] at this; omega
  have hOff0 : a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
      mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a := by
    by_cases h23 : tok.tag a = 23 + cfg.P.d
    · exact hLen h23
    · by_contra hc
      exact h23 (hLen0Tag a (by omega) (by omega))
  rw [hFr2 a (by omega) (fun ei hei _ => ⟨fun h => by
      have := hT9 ei hei; rw [← h] at this; omega, fun h => by
      have := hT12 ei hei; rw [← h] at this; omega, fun h => by
      have := hT13 ei hei; rw [← h] at this; omega⟩) hOff0,
    hFr1 a (by omega) hR11 (fun _ => ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩), Function.update_of_ne (by omega)]
  exact hMemEq a haU (by omega) (by omega) (by omega)

end MinCostFlow.MinRatio
