module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopDefsKFBL
public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import WordRAM.Tactic

/-!
# The fixed addresses of the Branch B loop, from the solver rep (`WireChainCoreBranchBStaticKFBL`)

The loop of Branch B (`wireBranchBFrontKFBL_runs` and the lemmas after it) reads a list of fixed
addresses (`BranchBAddrs`) and asks that the fixed arrays, the level graphs and the length blocks
lie apart from each other (`BranchBStatic`) and apart from the core footprints
(`BranchBCoresDisjStatic`). This file gets these facts from the solver rep at the start of the
chain core.

`branchBAddrsOf` lists the addresses: the header, the threshold table, the core handles and
branches (just after the header), the level sizes and the level metadata (just after the table),
the rebuild and update counters, the select base and the graph and length pointers of each level.

Most separations come from the tags of `SolverTagsAt` and `SolverLevelMetaAt`: two blocks whose
words have different tags cannot meet (`tag_block_sep`), and a word with one tag is outside a
block of another tag (`tag_point_sep`). The graphs of the levels `j ≥ 1` and all the length
blocks share the tag `23 + d`, so their separations come from the layout part of
`UpdateCoreModelInv`. The result used later is `branchBStatic_of_rep`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- A word whose tag differs from the tag of every word of a block lies outside the block. -/
theorem tag_point_sep {tag : ℕ → ℕ} {x n a t t' : ℕ} (h : ∀ j < n, tag (x + j) = t)
    (ha : tag a = t') (hne : t' ≠ t) : a < x ∨ x + n ≤ a := by
  by_contra hc
  have hj := h (a - x) (by omega)
  rw [show x + (a - x) = a by omega, ha] at hj
  exact hne hj

/-- Two nonempty blocks whose words have two different tags do not meet. -/
theorem tag_block_sep {tag : ℕ → ℕ} {x n y m t t' : ℕ} (hx : ∀ j < n, tag (x + j) = t)
    (hy : ∀ j < m, tag (y + j) = t') (hne : t ≠ t') (hn : 0 < n) (hm : 0 < m) :
    x + n ≤ y ∨ y + m ≤ x := by
  rcases le_total x y with hxy | hyx
  · rcases tag_point_sep hx (by simpa using hy 0 hm) (Ne.symm hne) with h | h <;> omega
  · rcases tag_point_sep hy (by simpa using hx 0 hn) hne with h | h <;> omega

/-- The fixed addresses of the Branch B loop at the start of the chain core: the ones that
Phase 0 loads into the registers `72`–`86`, the floor `heapFloor` of the heap of the loop, and
the graph and length pointers of each level as stored in `mem0`. The handle of level `d` is the
handle of the terminal level. -/
@[expose] def branchBAddrsOf {cfg : Alg2Config} {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (mem0 : ℕ → ℕ) (heap heapFloor : ℕ) : BranchBAddrs where
  handle := tok.handle
  table := tok.table
  handleBase := tok.handle + 18
  branchBase := tok.handle + 18 + (cfg.P.d + 1)
  lvlMTable := solverLvlMAddr tok.table cfg.P.d
  levelMeta := solverLevelMetaAddr tok.table cfg.P.d
  rcBase := tok.levelsEnd + 2 * (cfg.P.d + 1)
  ucBase := tok.levelsEnd + 3 * (cfg.P.d + 1)
  selBase := heap
  heapFloor := heapFloor
  gPtr0 j := mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)
  lPtr0 j := mem0 (solverLevelMetaAddr tok.table cfg.P.d + j)
  coreH j := if j < cfg.P.d then tok.coreHandle j else tok.termHandle

set_option maxHeartbeats 1600000 in
/-- The layout facts of the Branch B loop from the solver rep at `mem0`, with the select base at
`heap` (above the footprint of the rep): the fixed arrays, the graphs and the length blocks lie
apart and below `heap` (`BranchBStatic`), the core footprints miss all of them
(`BranchBCoresDisjStatic`), and the cell `lvlMTable - 1` of `N₀` lies apart from the core
footprints, the graphs, the length blocks and the counters. -/
theorem branchBStatic_of_rep
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap root uIntBuf g l heap
      heapFloor : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap) :
    let A := branchBAddrsOf tok mem0 heap heapFloor
    BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable A.levelMeta
      A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0 A.coreH ∧
    BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L A.handle A.table A.handleBase
      A.branchBase A.lvlMTable A.levelMeta A.rcBase A.ucBase (fun _ => vCap) (fun _ => eCap)
      A.gPtr0 A.lPtr0 A.coreH tok.coreTok ∧
    (0 < A.lvlMTable ∧
      (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok.coreTok j) (A.lvlMTable - 1)) ∧
      (∀ j < cfg.P.d,
        (A.lvlMTable - 1 < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ A.lvlMTable - 1) ∧
        (A.lvlMTable - 1 < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ A.lvlMTable - 1) ∧
        A.lvlMTable - 1 ≠ A.ucBase + j ∧ A.lvlMTable - 1 ≠ A.rcBase + j)) := by
  intro A
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, _, hT2, hT3, hT4, hT5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ :=
    hTags0
  obtain ⟨⟨_, hN0Tag, _, _⟩, _, _, hLvlMTag, hMetaTag, _⟩ := hMeta0
  obtain ⟨⟨hdPos, _⟩, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, hLPair, _⟩, _⟩ := hModelInv
  set d := cfg.P.d with hd
  -- the addresses
  have eH : A.handle = tok.handle := rfl
  have eT : A.table = tok.table := rfl
  have eHB : A.handleBase = tok.handle + 18 := rfl
  have eBB : A.branchBase = tok.handle + 18 + (d + 1) := rfl
  have eM : A.lvlMTable = tok.table + (d + 1) + 1 := rfl
  have eLM : A.levelMeta = tok.table + (d + 1) + 1 + d := rfl
  have eRC : A.rcBase = tok.levelsEnd + 2 * (d + 1) := rfl
  have eUC : A.ucBase = tok.levelsEnd + 3 * (d + 1) := rfl
  have eS : A.selBase = heap := rfl
  -- the tagged blocks
  have R2 : ∀ j < 18, tok.tag (tok.handle + j) = 2 := hT2
  have R3 : ∀ j < d + 1, tok.tag (tok.table + j) = 3 := fun j hj => hT3 j (by omega)
  have R4 : ∀ j < 2 * (d + 1), tok.tag (tok.handle + 18 + j) = 4 := hT4
  have R5 : ∀ j < 4 * (d + 1) + 1, tok.tag (tok.levelsEnd + j) = 5 := hT5
  have RM : ∀ j < d, tok.tag (A.lvlMTable + j) = 21 + d := hLvlMTag
  have RLM : ∀ j < 2 * d, tok.tag (A.levelMeta + j) = 22 + d := hMetaTag
  have hN0 : tok.tag (A.lvlMTable - 1) = 21 + d := by
    rw [show A.lvlMTable - 1 = solverN0Addr tok.table d by rw [eM]; rfl]; exact hN0Tag
  have hLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwn a h))
  -- a word with a tag outside the fixed tags lies outside every fixed block
  have hOff {a t : ℕ} (ht : tok.tag a = t) (h2 : t ≠ 2) (h3 : t ≠ 3) (h4 : t ≠ 4) (h5 : t ≠ 5)
      (hm : t ≠ 21 + d) (hlm : t ≠ 22 + d) :
      (a < tok.handle ∨ tok.handle + 18 ≤ a) ∧ (a < tok.table ∨ tok.table + (d + 1) ≤ a) ∧
      (a < tok.handle + 18 ∨ tok.handle + 18 + 2 * (d + 1) ≤ a) ∧
      (a < tok.levelsEnd ∨ tok.levelsEnd + (4 * (d + 1) + 1) ≤ a) ∧
      (a < A.lvlMTable ∨ A.lvlMTable + d ≤ a) ∧ (a < A.levelMeta ∨ A.levelMeta + 2 * d ≤ a) :=
    ⟨tag_point_sep R2 ht h2, tag_point_sep R3 ht h3, tag_point_sep R4 ht h4,
      tag_point_sep R5 ht h5, tag_point_sep RM ht hm, tag_point_sep RLM ht hlm⟩
  -- the graphs and the length blocks, at the caps `(vCap, eCap)`
  have hCapEq (j : ℕ) (hj : j < d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (hCaps0 j hj)
  have hGr : ∀ j < d, ∀ a, A.gPtr0 j ≤ a → a < A.gPtr0 j + dynGraphSize vCap eCap →
      (tok.tag a = 20 ∨ tok.tag a = 23 + d) ∧ ∀ r < d,
        (a < A.lPtr0 r ∨ A.lPtr0 r + eCap * L ≤ a) ∧
        (r ≠ j → a < A.gPtr0 r ∨ A.gPtr0 r + dynGraphSize vCap eCap ≤ a) := by
    intro j hj a h1 h2
    obtain ⟨hv, he⟩ := hCapEq j hj
    obtain ⟨_, _, _, _, hG⟩ := hLev j hj
    rw [hv, he] at hG
    obtain ⟨htag, hsep⟩ := hG a h1 h2
    refine ⟨by split_ifs at htag <;> simp [htag], fun r hr => ?_⟩
    obtain ⟨hv', he'⟩ := hCapEq r hr
    have hs := hsep r hr
    rw [hv', he'] at hs
    exact hs
  have hLn : ∀ j < d, ∀ a, A.lPtr0 j ≤ a → a < A.lPtr0 j + eCap * L → tok.tag a = 23 + d := by
    intro j hj a h1 h2
    obtain ⟨_, he⟩ := hCapEq j hj
    obtain ⟨_, _, _, hL, _⟩ := hLev j hj
    rw [he] at hL
    exact hL a h1 h2
  have hLOwn (j : ℕ) (hj : j < d) : A.lPtr0 j < uIntBuf :=
    hFootLt _ (Or.inl (hLev j hj).2.2.1)
  have hLP : ∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
      A.lPtr0 j₁ + eCap * L ≤ A.lPtr0 j₂ ∨ A.lPtr0 j₂ + eCap * L ≤ A.lPtr0 j₁ := by
    intro j₁ hj₁ j₂ hj₂ hne
    have h := hLPair j₁ hj₁ j₂ hj₂ hne
    rw [(hCapEq j₁ hj₁).2, (hCapEq j₂ hj₂).2] at h
    exact h
  have hGTag (j : ℕ) (hj : j < d) (a : ℕ) (h1 : A.gPtr0 j ≤ a)
      (h2 : a < A.gPtr0 j + dynGraphSize vCap eCap) :=
    (hGr j hj a h1 h2).1
  have hpos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
  -- the core footprints
  have hCore (r : ℕ) (hr : r < d) (a : ℕ) (ha : Rcore.foot (A.coreH r) (tok.coreTok r) a) :
      tok.tag a = 21 + r := by
    have hc : A.coreH r = tok.coreHandle r := by
      show (if r < d then tok.coreHandle r else tok.termHandle) = _
      simp [hr]
    rw [hc] at ha
    exact hT21 r hr a ha
  -- the blocks of different tags
  have b4M := tag_block_sep R4 RM (by omega) (by omega) hdPos
  have b4LM := tag_block_sep R4 RLM (by omega) (by omega) (by omega)
  have b52 := tag_block_sep R5 R2 (by omega) (by omega) (by omega)
  have b5M := tag_block_sep R5 RM (by omega) (by omega) hdPos
  have b54 := tag_block_sep R5 R4 (by omega) (by omega) (by omega)
  have b5LM := tag_block_sep R5 RLM (by omega) (by omega) (by omega)
  have b35 := tag_block_sep R3 R5 (by omega) (by omega) (by omega)
  have b34 := tag_block_sep R3 R4 (by omega) (by omega) (by omega)
  refine ⟨{
    handleLt := by have := hLt (a := tok.handle + 17) (by rw [R2 17 (by omega)]; decide); omega
    tableLt := by have := hLt (a := tok.table + d) (by rw [R3 d (by omega)]; decide); omega
    hbLt := by have := hLt (a := tok.handle + 18 + d) (by rw [R4 d (by omega)]; decide); omega
    bbLt := by
      have := hLt (a := tok.handle + 18 + (2 * d + 1)) (by rw [R4 _ (by omega)]; decide); omega
    lvlMLt := by
      have := hLt (a := A.lvlMTable + (d - 1)) (by rw [RM _ (by omega)]; omega); omega
    metaLt := by
      have := hLt (a := A.levelMeta + (2 * d - 1)) (by rw [RLM _ (by omega)]; omega); omega
    rcLt := by
      have := hLt (a := tok.levelsEnd + (2 * (d + 1) + d)) (by rw [R5 _ (by omega)]; decide)
      omega
    ucLt := by
      have := hLt (a := tok.levelsEnd + (3 * (d + 1) + d)) (by rw [R5 _ (by omega)]; decide)
      omega
    gLt := fun j hj => by
      have := hLt (a := A.gPtr0 j + dynGraphSize vCap eCap - 1) (by
        rcases hGTag j hj (A.gPtr0 j + dynGraphSize vCap eCap - 1) (by omega) (by omega)
          with h | h <;> rw [h] <;> omega)
      omega
    lLt := fun j hj => by
      by_cases h0 : eCap * L = 0
      · have := hLOwn j hj; omega
      · have := hLt (a := A.lPtr0 j + eCap * L - 1) (by
          rw [hLn j hj _ (by omega) (by omega)]; omega)
        omega
    sepHB := by omega
    sepHM := by omega
    sepBM := by omega
    sepHL := by omega
    sepBL := by omega
    sepML := by omega
    sepRCH := by omega
    sepRCM := by omega
    sepRCHB := by omega
    sepRCBB := by omega
    sepRCLM := by omega
    sepRCUC := by omega
    sepUCHB := by omega
    sepUCBB := by omega
    sepUCLM := by omega
    sepUCH := by omega
    sepUCM := by omega
    sepTabUC := by omega
    sepTabHB := by omega
    sepTabBB := by omega
    sepTabLM := by omega
    sepTabRC := by omega
    gSep := fun j hj a h1 h2 => by
      obtain ⟨ht, hrest⟩ := hGr j hj a h1 h2
      have hO : (a < tok.handle ∨ tok.handle + 18 ≤ a) ∧
          (a < tok.table ∨ tok.table + (d + 1) ≤ a) ∧
          (a < tok.handle + 18 ∨ tok.handle + 18 + 2 * (d + 1) ≤ a) ∧
          (a < tok.levelsEnd ∨ tok.levelsEnd + (4 * (d + 1) + 1) ≤ a) ∧
          (a < A.lvlMTable ∨ A.lvlMTable + d ≤ a) ∧
          (a < A.levelMeta ∨ A.levelMeta + 2 * d ≤ a) := by
        rcases ht with h | h <;> exact hOff h (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
      obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hO
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        hrest⟩
    lSep := fun j hj a h1 h2 => by
      obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hOff (hLn j hj a h1 h2) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    lPairSep := hLP }, ?_, ?_⟩
  · -- the core footprints miss the fixed blocks, the graphs and the length blocks
    intro r hr
    have hne {a t : ℕ} (ht : tok.tag a = t) (htr : t ≠ 21 + r) :
        ¬ Rcore.foot (A.coreH r) (tok.coreTok r) a := fun hf => htr (ht ▸ hCore r hr a hf)
    refine ⟨fun a h1 h2 => ?_, fun j hj => hne (R3 j (by omega)) (by omega),
      fun j hj => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_, ?_, ?_, ?_⟩,
      fun j hj a h1 h2 => ?_, fun j hj a h1 h2 => ?_⟩
    · have := R2 (a - tok.handle) (by omega)
      rw [show tok.handle + (a - tok.handle) = a by omega] at this
      exact hne this (by omega)
    · exact hne (R4 j (by omega)) (by omega)
    · have := R4 (d + 1 + j) (by omega)
      rw [← add_assoc] at this
      exact hne this (by omega)
    · exact hne (RM j hj) (by omega)
    · exact hne (RLM j (by omega)) (by omega)
    · have := RLM (d + j) (by omega)
      rw [← add_assoc] at this
      exact hne this (by omega)
    · have := R5 (3 * (d + 1) + j) (by omega)
      rw [← add_assoc] at this
      exact hne this (by omega)
    · have := R5 (2 * (d + 1) + j) (by omega)
      rw [← add_assoc] at this
      exact hne this (by omega)
    · beta_reduce at h2
      rcases hGTag j hj a h1 h2 with h | h <;> exact hne h (by omega)
    · beta_reduce at h2
      exact hne (hLn j hj a h1 h2) (by omega)
  · -- the cell of `N₀`
    refine ⟨by omega, fun j hj hf => by have := hCore j hj _ hf; omega, fun j hj => ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hc
      rcases hGTag j hj (A.lvlMTable - 1) (by omega) (by omega) with h | h <;> omega
    · by_contra hc
      have := hLn j hj (A.lvlMTable - 1) (by omega) (by omega); omega
    · intro hc
      have := R5 (3 * (d + 1) + j) (by omega)
      rw [← add_assoc, ← eUC, ← hc] at this; omega
    · intro hc
      have := R5 (2 * (d + 1) + j) (by omega)
      rw [← add_assoc, ← eRC, ← hc] at this; omega

end MinCostFlow.MinRatio
