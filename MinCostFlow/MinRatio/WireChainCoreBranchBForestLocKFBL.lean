module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSuffixKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBExitOutKFBL

/-!
# Where the forests of the suffix of Branch B lie (`WireChainCoreBranchBForestLocKFBL`)

The suffix of Branch B reads two lists of forests (`oldFs` at `oldPtrs + fr`, `newFs` at
`newPtrs + fr`), the select base and the batch at `uIntBuf`, across its two syncs. Its run lemma
`wireBranchBSuffixKFBL_runs` asks that all these words lie in the set `BranchBSuffixKeep`: below
the heap pointer, not the count word `root + 11`, without the tags `9`, …, `16` (but `12`) below
`uIntBuf`, and off the tree above `uIntBuf`.

The exits give the lists (`BranchBExitBaseKFBL.oldF`, `newF`) but not the place of the words of
their graphs. `branchBSuffixLists_of_exit` gives the lists and their lengths in the form of the
suffix. `BranchBExitForestLocKFBL` is this place: each word of a listed graph lies in the
footprint of a core or of the last level at the exit of the loop, or in the heap of Branch B above
its floor. `branchBSuffixKeep_of_forestLoc` gives the premises `hOldK`, `hNewK`, `hSelK` and
`hBatchK` of the suffix from it, from the tags of the footprints, and from the place of the tree.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program

/-- The words of the graphs of the two forest lists after an exit of the loop of Branch B, at the
state `out`: in the footprint of a core `j < d` (at the tokens `tok` of the loop exit) or of the
last level (at `termTok`), or in `[A.heapFloor, out.regs 4)`. -/
structure BranchBExitForestLocKFBL {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {RL : DSRep (ℕ × (ℕ → LSF))} (A : BranchBAddrs) (oldPtrs newPtrs fr : ℕ)
    (oldFs newFs : List MGraph) (tok : ℕ → Rcore.τ) (termTok : RL.τ) (out : State) : Prop where
  old : ∀ (t : ℕ) (ht : t < oldFs.length) (vc ec : ℕ),
    DynGraphAt out.mem (out.mem (oldPtrs + fr + t)) vc ec oldFs[t] →
    ∀ x, out.mem (oldPtrs + fr + t) ≤ x → x < out.mem (oldPtrs + fr + t) + dynGraphSize vc ec →
      (∃ j < cfg.P.d, Rcore.foot (A.coreH j) (tok j) x) ∨ RL.foot (A.coreH cfg.P.d) termTok x ∨
      (A.heapFloor ≤ x ∧ x < out.regs 4)
  new : ∀ (t : ℕ) (ht : t < newFs.length) (vc ec : ℕ),
    DynGraphAt out.mem (out.mem (newPtrs + fr + t)) vc ec newFs[t] →
    ∀ x, out.mem (newPtrs + fr + t) ≤ x → x < out.mem (newPtrs + fr + t) + dynGraphSize vc ec →
      (∃ j < cfg.P.d, Rcore.foot (A.coreH j) (tok j) x) ∨ RL.foot (A.coreH cfg.P.d) termTok x ∨
      (A.heapFloor ≤ x ∧ x < out.regs 4)

/-- A word of a footprint or of the heap above the floor lies in `BranchBSuffixKeep`, given the
tags of the footprints below `uIntBuf`, and the tree footprint below `uIntBuf` or in
`[h0, hS1)` with `hS1` below the floor. -/
private theorem keep_of_loc {L : ℕ} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {RL : DSRep (ℕ × (ℕ → LSF))} {tokS : SolverToken cfg L Rcore} {A : BranchBAddrs}
    {root uIntBuf heapX h0 hS1 hOut x : ℕ} {tok : ℕ → Rcore.τ} {termTok : RL.τ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hCoreTag : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tok j) a →
      (a < uIntBuf ∧ tokS.tag a = 21 + j) ∨ A.heapFloor ≤ a)
    (hLastTag : ∀ a, RL.foot (A.coreH cfg.P.d) termTok a → a < uIntBuf ∧ tokS.tag a = 19)
    (hTree : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tokS.treeHeap
      curTreeTok a → a < uIntBuf ∨ (h0 ≤ a ∧ a < hS1))
    (hRootTag : tokS.tag (root + 11) = 1) (hRootU : root + 16 ≤ uIntBuf) (hS1 : hS1 ≤ A.heapFloor)
    (hU : uIntBuf ≤ A.heapFloor) (hOutX : hOut ≤ heapX)
    (hFootX : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tok j) a → a < heapX)
    (hLastX : uIntBuf ≤ heapX)
    (hx : (∃ j < cfg.P.d, Rcore.foot (A.coreH j) (tok j) x) ∨ RL.foot (A.coreH cfg.P.d) termTok x ∨
      (A.heapFloor ≤ x ∧ x < hOut)) :
    BranchBSuffixKeep L tokS root uIntBuf heapX curTreeTok x := by
  have hTagOk {v : ℕ} (hv : v = 19 ∨ 21 ≤ v) : v ≠ 9 ∧ v ≠ 10 ∧ v ≠ 11 ∧ v ≠ 13 ∧ v ≠ 14 ∧
      v ≠ 15 ∧ v ≠ 16 ∧ v ≠ 1 := by omega
  have hHigh (h1 : A.heapFloor ≤ x) (h2 : x < heapX) :
      BranchBSuffixKeep L tokS root uIntBuf heapX curTreeTok x := by
    refine ⟨h2, fun h => by omega, fun h => absurd h (by omega), fun _ hf => ?_⟩
    · rcases hTree x hf with h | h <;> omega
  have hLow (h1 : x < uIntBuf) (ht : tokS.tag x = 19 ∨ 21 ≤ tokS.tag x) :
      BranchBSuffixKeep L tokS root uIntBuf heapX curTreeTok x := by
    have h := hTagOk ht
    refine ⟨by omega, fun he => h.2.2.2.2.2.2.2 (by rw [he] at *; exact hRootTag), fun _ =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩,
      fun h' => absurd h' (by omega)⟩
  rcases hx with ⟨j, hj, hf⟩ | hf | ⟨h1, h2⟩
  · rcases hCoreTag j hj x hf with ⟨h1, h2⟩ | h1
    · exact hLow h1 (Or.inr (by omega))
    · exact hHigh h1 (hFootX j hj x hf)
  · obtain ⟨h1, h2⟩ := hLastTag x hf
    exact hLow h1 (Or.inl h2)
  · exact hHigh h1 (by omega)


/-- A word in `[uIntBuf, h0)` lies in `BranchBSuffixKeep` when the tree footprint lies below
`uIntBuf` or in `[h0, hS1)` and `h0 ≤ heapX`. -/
private theorem keep_mid {L : ℕ} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tokS : SolverToken cfg L Rcore} {root uIntBuf heapX h0 hS1 x : ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hTree : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tokS.treeHeap
      curTreeTok a → a < uIntBuf ∨ (h0 ≤ a ∧ a < hS1))
    (hRootU : root + 16 ≤ uIntBuf) (hX : h0 ≤ heapX) (h1 : uIntBuf ≤ x) (h2 : x < h0) :
    BranchBSuffixKeep L tokS root uIntBuf heapX curTreeTok x :=
  ⟨by omega, by omega, fun h => absurd h (by omega), fun _ hf => by
    rcases hTree x hf with h | h <;> omega⟩

/-- **The keep premises of the suffix of Branch B.** From the places of the forests after the exit
(`BranchBExitForestLocKFBL`), the tags of the footprints of the cores and of the last level, and
the place of the tree, the words that the suffix reads lie in `BranchBSuffixKeep` at the heap
pointer `out.regs 4`: the pointer cells and the graph words of the two forest lists (the premises
`hOldK` and `hNewK` of `wireBranchBSuffixKFBL_runs`), the select base (`hSelK`) and the batch
(`hBatchK`). The pointer arrays, the select base and the batch lie in `[uIntBuf, h0)`. -/
theorem branchBSuffixKeep_of_forestLoc {L : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))}
    {tokS : SolverToken cfg L Rcore} {A : BranchBAddrs}
    {root uIntBuf h0 hS1 oldPtrs newPtrs fr selBase totalWords : ℕ} {oldFs newFs : List MGraph}
    {tok : ℕ → Rcore.τ} {termTok : RL.τ} {out : State}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hLoc : BranchBExitForestLocKFBL A oldPtrs newPtrs fr oldFs newFs tok termTok out)
    (hCoreTag : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tok j) a →
      (a < uIntBuf ∧ tokS.tag a = 21 + j) ∨ A.heapFloor ≤ a)
    (hFootX : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tok j) a → a < out.regs 4)
    (hLastTag : ∀ a, RL.foot (A.coreH cfg.P.d) termTok a → a < uIntBuf ∧ tokS.tag a = 19)
    (hTree : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tokS.treeHeap
      curTreeTok a → a < uIntBuf ∨ (h0 ≤ a ∧ a < hS1))
    (hRootTag : tokS.tag (root + 11) = 1) (hRootU : root + 16 ≤ uIntBuf)
    (hh0 : h0 ≤ hS1) (hS1 : hS1 ≤ A.heapFloor) (hFloor : A.heapFloor ≤ out.regs 4)
    (hOldLo : uIntBuf ≤ oldPtrs) (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewH0 : newPtrs + (cfg.P.d + 1) ≤ h0)
    (hOldLen : fr + oldFs.length ≤ cfg.P.d + 1) (hNewLen : fr + newFs.length ≤ cfg.P.d + 1)
    (hSel1 : uIntBuf ≤ selBase) (hSel2 : selBase < h0) (hBatch : uIntBuf + totalWords ≤ h0) :
    let K := BranchBSuffixKeep L tokS root uIntBuf (out.regs 4) curTreeTok
    (∀ (t : ℕ) (ht : t < oldFs.length), K (oldPtrs + fr + t) ∧
      ∀ vc ec, DynGraphAt out.mem (out.mem (oldPtrs + fr + t)) vc ec oldFs[t] →
        ∀ x, out.mem (oldPtrs + fr + t) ≤ x →
          x < out.mem (oldPtrs + fr + t) + dynGraphSize vc ec → K x) ∧
    (∀ (t : ℕ) (ht : t < newFs.length), K (newPtrs + fr + t) ∧
      ∀ vc ec, DynGraphAt out.mem (out.mem (newPtrs + fr + t)) vc ec newFs[t] →
        ∀ x, out.mem (newPtrs + fr + t) ≤ x →
          x < out.mem (newPtrs + fr + t) + dynGraphSize vc ec → K x) ∧
    K selBase ∧ (∀ x, uIntBuf ≤ x → x < uIntBuf + totalWords → K x) := by
  intro K
  have hX : h0 ≤ out.regs 4 := by omega
  have hU : uIntBuf ≤ A.heapFloor := by omega
  have hUX : uIntBuf ≤ out.regs 4 := by omega
  refine ⟨fun t ht => ⟨keep_mid hTree hRootU hX (by omega) (by omega), fun vc ec hG x h1 h2 =>
      keep_of_loc hCoreTag hLastTag hTree hRootTag hRootU hS1 hU le_rfl hFootX hUX
        (hLoc.old t ht vc ec hG x h1 h2)⟩,
    fun t ht => ⟨keep_mid hTree hRootU hX (by omega) (by omega), fun vc ec hG x h1 h2 =>
      keep_of_loc hCoreTag hLastTag hTree hRootTag hRootU hS1 hU le_rfl hFootX hUX
        (hLoc.new t ht vc ec hG x h1 h2)⟩,
    keep_mid hTree hRootU hX hSel1 hSel2,
    fun x h1 h2 => keep_mid hTree hRootU hX h1 (by omega)⟩


/-- The length of a suffix forest list from `fr` (none when `fr = d + 1`). -/
private theorem suffixList_length {T : SparseCoreRestartTool} {P : ChainParams}
    (c : ChainState T P) {fr : ℕ} (h : fr ≤ P.d + 1) :
    (if fr ≤ P.d then chainSuffixForests c fr else []).length = P.d + 1 - fr := by
  split_ifs with hf
  · rw [chainSuffixForests_length]; omega
  · simp only [List.length_nil]; omega

/-- **The forest lists of the suffix of Branch B** from the facts after an exit: the old and the
new forests of the levels from `fr` on, at `oldPtrs + fr` and `newPtrs + fr`, with `d + 1 - fr`
entries each (the premises `hi₀`, `hOldLen`, `hNewLen`, `hOld`, `hNew` of
`wireBranchBSuffixKFBL_runs` at `i₀ := fr`, `dd := d` and the heap pointer `out.regs 4`). -/
theorem branchBSuffixLists_of_exit {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {A : BranchBAddrs}
    {vcL ecL oldPtrs newPtrs intCap fr termTokN : ℕ} {ch0 ch X : ChainState cfg.T cfg.P}
    {levelU : ℕ → List Update} {D : ℕ → LevelDiffLists} {sE out : State}
    {tok tokN : ℕ → Rcore.τ}
    (O : BranchBExitBaseKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vcL ecL oldPtrs newPtrs intCap fr ch0 ch X levelU D sE out tok tokN
      termTokN) :
    fr ≤ cfg.P.d + 1 ∧
    (if fr ≤ cfg.P.d then chainSuffixForests ch0 fr else []).length = cfg.P.d + 1 - fr ∧
    (if fr ≤ cfg.P.d then chainSuffixForests X fr else []).length = cfg.P.d + 1 - fr ∧
    ForestPtrListAt out.mem (oldPtrs + fr)
      (if fr ≤ cfg.P.d then chainSuffixForests ch0 fr else []) intCap (out.regs 4) ∧
    ForestPtrListAt out.mem (newPtrs + fr)
      (if fr ≤ cfg.P.d then chainSuffixForests X fr else []) intCap (out.regs 4) :=
  ⟨O.frLe, suffixList_length ch0 O.frLe, suffixList_length X O.frLe, O.oldF, O.newF⟩

end MinCostFlow.MinRatio
