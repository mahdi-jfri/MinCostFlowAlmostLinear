module

public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import WordRAM.Tactic

/-!
# The words of the tree state across the middle of Branch B (`WireChainCoreBranchBTreeKeepKFBL`)

After Sync 1 and the refresh, Branch B runs the front, the plain-step loop and one exit. Then the
tree state must move to the new root graph (`TreeSyncPhaseAt.change_graph`). That lemma asks that
the words the tree state reads keep their values from the memory `memS1` after Sync 1, except the
words of names off the old root graph. Below `uIntBuf` these words carry the tags `1`, `2`,
`9, …, 16` and `18`. Above `uIntBuf` they lie below the select slots or from the end `h0` of the
fixed part of the heap of Branch B on (the new tree words and the records of the cut edges).

`branchBTreeWords_keep` proves this from the frames of the four steps: the frame of the refresh,
the frame of the front, the frame of the loop and the two frames of the exit. Each step writes
only words of other kinds: the cores, the fixed arrays of the levels, the graphs and the length
blocks of the levels carry other tags (`3`, `4`, `5`, `20` and more), and each word with a tag lies
below `uIntBuf`. The select slots and the arrays of forest pointers lie in `[heap, h0)`, and the
new parts of the core footprints lie above the heap floor.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1600000 in
/-- The words that the tree state reads keep their values from `memS1` (after Sync 1) to the end
`out` of the exit of Branch B. The addresses are `branchBAddrsOf tok mem0 heap heap2`, the fixed
part of the heap ends at `h0`, and the tree state lies below `hS1 ≤ heap2`. The steps are:
the refresh (from `memS1` to `sP`, `hPre`), the front (from `sP` to `s`, `hFront`), the loop
(from `s` to `sE`, `hLoop`, with the core tokens `tokE` at its end) and the exit (from `sE` to
`out`, `hExit` and `hExitHeap`). -/
theorem branchBTreeWords_keep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap root uIntBuf g l heap heap2
      hS1 ec0 oldPtrs newPtrs : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 memS1 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    {sP s sE out : State} {tokE : ℕ → Rcore.τ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap)
    (hh0 : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ hS1) (hS1le : hS1 ≤ heap2)
    (hPtrs : heap + 1 + 12 * cfg.P.d ≤ oldPtrs ∧ oldPtrs + (cfg.P.d + 1) ≤ newPtrs ∧
      newPtrs + (cfg.P.d + 1) ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4)
    (hLm : ∀ a, mem0 (solverLevelMetaAddr tok.table cfg.P.d) ≤ a →
      a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L → tok.tag a = 23 + cfg.P.d)
    (hPre : ∀ a < hS1, (∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E →
        a ≠ tok.slots + ei ∧ a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
      (a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L ≤ a) → sP.mem a = memS1 a)
    (hFront : ∀ a < heap2, s.mem a = sP.mem a)
    (hs4 : heap2 ≤ s.regs 4)
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
      (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) → out.mem a = sE.mem a)
    (hExitHeap : let A := branchBAddrsOf tok mem0 heap heap2
      ∀ a, A.selBase + 1 + 12 * cfg.P.d ≤ a → a < A.heapFloor →
      (a < oldPtrs ∨ oldPtrs + (cfg.P.d + 1) ≤ a) → (a < newPtrs ∨ newPtrs + (cfg.P.d + 1) ≤ a) →
      out.mem a = sE.mem a) :
    ∀ a < hS1,
      (a < uIntBuf → tok.tag a = 1 ∨ tok.tag a = 2 ∨ (9 ≤ tok.tag a ∧ tok.tag a ≤ 16) ∨
        tok.tag a = 18) →
      (uIntBuf ≤ a → a < heap ∨ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a) →
      (∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E → a ≠ tok.slots + ei ∧
        a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
      out.mem a = memS1 a := by
  intro a ha hTag hHigh hNew
  set A := branchBAddrsOf tok mem0 heap heap2 with hA
  set d := cfg.P.d with hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, _, _, _, hT4, hT5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, _, hMetaTag, _⟩ := hMeta0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := hModelInv
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := hFootLt x (Or.inl (hOwn x h))
  -- a word with a tag that is neither `0` nor a tag of the tree state is not `a`
  have hNo {x t : ℕ} (hx : x = a) (ht : tok.tag x = t) (h0 : t ≠ 0)
      (hT : t ≠ 1 ∧ t ≠ 2 ∧ (t < 9 ∨ 16 < t) ∧ t ≠ 18) : False := by
    subst hx
    have hl := hLt (by rw [ht]; exact h0)
    rcases hTag hl with h | h | h | h <;> rw [ht] at h <;> omega
  have hCapEq (j : ℕ) (hj : j < d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (hCaps0 j hj)
  have eCH (j : ℕ) (hj : j < d) : A.coreH j = tok.coreHandle j := by
    show (if j < d then tok.coreHandle j else tok.termHandle) = _
    simp [hj]
  -- the kinds of words the steps write
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
    · rw [if_pos h0] at htag; exact hNo rfl htag (by omega) (by omega)
    · rw [if_neg h0] at htag; exact hNo rfl htag (by omega) (by omega)
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
  -- the frame of the refresh and of the front
  have hLmOff : a < mem0 (solverLevelMetaAddr tok.table d) ∨
      mem0 (solverLevelMetaAddr tok.table d) + ec0 * L ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    exact hNo rfl (hLm a hc.1 hc.2) (by omega) (by omega)
  have hS : s.mem a = memS1 a := (hFront a (by omega)).trans (hPre a ha hNew hLmOff)
  by_cases hLow : a < heap
  · -- below the select base: the frame of the loop and the frame of the exit
    have hE : sE.mem a = s.mem a :=
      hLoop a (by omega) hCoreOff (fun j hj => ⟨hGOff j hj, hLOff j hj⟩) hUCOff (Or.inl hLow)
    have hRange {x n t : ℕ} (hx : ∀ j < n, tok.tag (x + j) = t) (h0 : t ≠ 0)
        (hT : t ≠ 1 ∧ t ≠ 2 ∧ (t < 9 ∨ 16 < t) ∧ t ≠ 18) : a < x ∨ x + n ≤ a := by
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
  · -- above the fixed part of the heap: the second frame of the exit
    have hge : uIntBuf ≤ a := by omega
    have hHi : heap + 1 + 12 * d + 3 * (d + 1) + 4 ≤ a := (hHigh hge).resolve_left hLow
    have hE : sE.mem a = s.mem a :=
      hLoop a (by omega) hCoreOff (fun j hj => ⟨hGOff j hj, hLOff j hj⟩) hUCOff
        (Or.inr (by show heap + 1 + 12 * d ≤ a; omega))
    exact (hExitHeap a (by show heap + 1 + 12 * d ≤ a; omega) (by show a < heap2; omega)
      (Or.inr (by omega)) (Or.inr (by omega))).trans (hE.trans hS)

end MinCostFlow.MinRatio
