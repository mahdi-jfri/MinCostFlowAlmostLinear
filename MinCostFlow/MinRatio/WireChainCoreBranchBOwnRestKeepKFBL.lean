module

public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import WordRAM.Tactic

/-!
# The words of the edge accounts across the middle of Branch B (`WireChainCoreBranchBOwnRestKeepKFBL`)

Between the prefix and the suffix, Branch B runs the front, the plain-step loop and one exit.
The fields of `BranchBSufOutKFBL` on the edge accounts read words that the prefix wrote: the
threshold and record pointers of the edges (tags `12` and `13` below `uIntBuf`), the threshold
and record blocks of the old edges (tags `17` and `18`), and the new blocks of the refresh, which
lie in the heap of the prefix, above the fixed part of the heap of Branch B.

`branchBMidWords_keep` says that such words keep their values from the end `sP` of the prefix to
the end `out` of the exit. The proof is the one of `branchBTreeWords_keep`: each of the three
steps writes only words of other kinds. The cores, the fixed arrays of the levels, the graphs
and the length blocks carry tags outside `9, …, 18` (each word with a tag lies below
`uIntBuf`), the select slots and the arrays of forest pointers lie in the fixed part
`[heap, h0)` of the heap, and the new parts of the core footprints lie above the heap floor.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1600000 in
/-- The words below the heap floor `heap2` with a tag in `9, …, 18` (below `uIntBuf`) or outside
the fixed part `[heap, h0)` of the heap (above `uIntBuf`) keep their values from the end `sP` of
the prefix to the end `out` of the exit of Branch B. The addresses are
`branchBAddrsOf tok mem0 heap heap2`. The steps are the front (from `sP` to `s`, `hFront`), the
loop (from `s` to `sE`, `hLoop`, with the core tokens `tokE` at its end) and the exit (from `sE`
to `out`, `hExit` and `hExitHeap`). -/
theorem branchBMidWords_keep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap root uIntBuf g l heap heap2
      oldPtrs newPtrs : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    {sP s sE out : State} {tokE : ℕ → Rcore.τ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap)
    (hPtrs : heap + 1 + 12 * cfg.P.d ≤ oldPtrs ∧ oldPtrs + (cfg.P.d + 1) ≤ newPtrs ∧
      newPtrs + (cfg.P.d + 1) ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4)
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
    ∀ a < heap2, (a < uIntBuf → 9 ≤ tok.tag a ∧ tok.tag a ≤ 18) →
      (uIntBuf ≤ a → a < heap ∨ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a) →
      out.mem a = sP.mem a := by
  intro a ha hTag hHigh
  set A := branchBAddrsOf tok mem0 heap heap2 with hA
  set d := cfg.P.d with hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, _, _, _, hT4, hT5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, _, hMetaTag, _⟩ := hMeta0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := hModelInv
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := hFootLt x (Or.inl (hOwn x h))
  -- a word with a tag that is neither `0` nor a tag of the tree state is not `a`
  have hNo {x t : ℕ} (hx : x = a) (ht : tok.tag x = t) (h0 : t ≠ 0)
      (hT : t < 9 ∨ 18 < t) : False := by
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
  -- the frame of the front
  have hS : s.mem a = sP.mem a := hFront a ha
  by_cases hLow : a < heap
  · -- below the select base: the frame of the loop and the frame of the exit
    have hE : sE.mem a = s.mem a :=
      hLoop a (by omega) hCoreOff (fun j hj => ⟨hGOff j hj, hLOff j hj⟩) hUCOff (Or.inl hLow)
    have hRange {x n t : ℕ} (hx : ∀ j < n, tok.tag (x + j) = t) (h0 : t ≠ 0)
        (hT : t < 9 ∨ 18 < t) : a < x ∨ x + n ≤ a := by
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
