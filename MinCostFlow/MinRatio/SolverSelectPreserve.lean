module

public import MinCostFlow.MinRatio.SolverLevelCapsInv
public import MinCostFlow.MinRatio.SolverLevelLayout
public import MinCostFlow.MinRatio.SolverSelectState
public import MinCostFlow.MinRatio.MinRatioMachineAssembly
public import MinCostFlow.MinRatio.SolverSelectRegionInv
import Mathlib.Tactic

/-!
# Preservation of level-metadata and select-state regions (`Query`, `Detect`, `Eval`, `Select`, `Find`)

Proves that every non-level-changing solver step preserves **both**:
1. The level-metadata / cap invariant `SolverLevelCapsInv` (`SolverLevelCapsInv.lean`, tags
   `20`, `21 + d`, `22 + d`, `23 + d`).
2. The select-heap invariant `SolverSelectInv` and wrapper `solverStateRepSel`
   (`SolverSelectState.lean`).

This file provides:
* Universal preservation lemmas: `SolverSelectInv.preserve_of_levelMeta` and
  `PreservesLevelMeta.preserve_both`.
* Full `solverStateRepSel` + `SolverLevelCapsInv` + `SolverSelectRegionInv` preservation for
  `Query` (`solverOps_query_preserves_sel`) and `Detect` (`solverOps_detect_preserves_sel`).
* Both-region preservation for `Eval` (`evalCycle_preserves_both`), `Select` / `SelectHeap`
  (`selectRoute_preserves_both`, `selectRouteHeap_preserves_both`), and `Find` / `FindHeap`
  (`findCycle_preserves_both`, `findCycleHeap_preserves_both`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-! ## 1. Universal preservation lemmas -/

theorem SelectStateAt.mono_foot {cfg : Alg2Config} {G : MGraph} {L P m dMul kOff table : ℕ}
    {model model' : Alg2State cfg} {foot₁ foot₂ : ℕ → Prop} {sg : SelectGhost} {mem : ℕ → ℕ}
    (h : SelectStateAt G L P m dMul kOff table model foot₁ sg mem)
    (hsub : ∀ a, foot₁ a → foot₂ a)
    (hChain : model'.chain = model.chain) :
    SelectStateAt G L P m dMul kOff table model' foot₂ sg mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8.imp (hsub _) id, h9, h10, ?_, ?_, ?_⟩
  · simpa [hChain] using h11
  · simpa [hChain] using h12
  · simpa [hChain] using h13

theorem SelectModelInv.of_chain_ext {cfg : Alg2Config} {model model' : Alg2State cfg}
    {G₀ : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (h : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hChain : model'.chain = model.chain)
    (hExtG : model'.extG = model.extG)
    (hExtℓ : model'.extℓ = model.extℓ) :
    SelectModelInv model' G₀ σ σ_mwu γ_ℓ γ_c := by
  simpa [SelectModelInv, hChain, hExtG, hExtℓ] using h

/-- **Universal `SolverSelectInv` preservation lemma.** Any solver step that preserves the
level-metadata region (`PreservesLevelMeta`), preserves off-foot memory below `frameHi`, grows the
solver's footprint only inside `[footLo, nextHeap)` with `frameHi ≤ footLo`, starts with
`sg.owned` strictly below `frameHi`, and leaves `chain`, `extG`, `extℓ` unchanged preserves
`SolverSelectInv`. -/
theorem SolverSelectInv.preserve_of_levelMeta
    {cfg : Alg2Config} {G : MGraph} {L P m V psi k epsExp drainUnit dMul kOff : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {root frameHi footLo nextHeap : ℕ}
    {model model' : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem mem' : ℕ → ℕ}
    (hInv : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hMeta : PreservesLevelMeta tok tok' mem mem')
    (hFrame : ∀ a < frameHi,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      mem' a = mem a)
    (hFoot : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a →
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨
        (footLo ≤ a ∧ a < nextHeap))
    (hBelow : ∀ a, sg.owned a → a < frameHi)
    (hLe : frameHi ≤ footLo)
    (hChain : model'.chain = model.chain)
    (hExtG : model'.extG = model.extG)
    (hExtℓ : model'.extℓ = model.extℓ) :
    SolverSelectInv G L P m dMul kOff tok'.table model'
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok')
      (LevelMetaFoot tok') sg mem' := by
  rw [hMeta.1]
  obtain ⟨hState, hDisj, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod⟩ := hInv
  refine ⟨?_, ?_, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod.of_chain_ext hChain hExtG hExtℓ⟩
  · intro mem₁ hag₁
    have hag₀ : ∀ a, LevelMetaFoot tok a ∨ sg.owned a → mem₁ a = mem a := by
      intro a ha
      rcases ha with hm | ho
      · exact (hag₁ a (Or.inl (hMeta.levelMetaFoot_mono hm))).trans (hMeta.metaEq a hm).2
      · exact (hag₁ a (Or.inr ho)).trans (hFrame a (hBelow a ho) (hDisj a ho))
    exact (hState mem₁ hag₀).mono_foot (fun _ hm => hMeta.levelMetaFoot_mono hm) hChain
  · intro a ho hf'
    rcases hFoot a hf' with hf | ⟨hlo, _⟩
    · exact hDisj a ho hf
    · have := hBelow a ho; omega

/-- **Combined preservation of both regions (`SolverLevelCapsInv` and `SolverSelectInv`)**
across any non-level-changing solver step that exports `PreservesLevelMeta`. -/
theorem PreservesLevelMeta.preserve_both
    {cfg : Alg2Config} {G : MGraph} {L P m V psi k epsExp drainUnit vCap eCap dMul kOff : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {root frameHi footLo nextHeap : ℕ}
    {model model' : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem mem' : ℕ → ℕ}
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hMeta : PreservesLevelMeta tok tok' mem mem')
    (hFrame : ∀ a < frameHi,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      mem' a = mem a)
    (hFoot : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a →
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨
        (footLo ≤ a ∧ a < nextHeap))
    (hBelow : ∀ a, sg.owned a → a < frameHi)
    (hLe : frameHi ≤ footLo)
    (hChain : model'.chain = model.chain)
    (hExtG : model'.extG = model.extG)
    (hExtℓ : model'.extℓ = model.extℓ) :
    SolverLevelCapsInv P V vCap eCap model' tok' mem' ∧
      SolverSelectInv G L P m dMul kOff tok'.table model'
        ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok')
        (LevelMetaFoot tok') sg mem' :=
  ⟨hMeta.to_capsInv hCaps (by rw [hChain]) (fun _ _ => by rw [hChain])
    (fun _ _ => by rw [hChain]) (fun _ _ => by rw [hChain]) (fun _ _ => by rw [hChain])
    (by rw [hChain]),
   hSel.preserve_of_levelMeta hMeta hFrame hFoot hBelow hLe hChain hExtG hExtℓ⟩

/-! ## 2. `Query` and `Detect` preserve both `SolverLevelCapsInv` and `solverStateRepSel` -/

/-- `solverOps_query_runs` preserves `SolverLevelCapsInv`, `SolverSelectRegionInv` and the full
`solverStateRepSel` invariant (including footprint, frame, and potential with unchanged
`K * sg.reembPot`). -/
theorem solverOps_query_preserves_sel
    {w base chainRefreshProc findCycleProc shiftLevelProc m V psi k epsExp
      unit toolMul treeMul dMul kOff vCap eCap K E pLast slot root e heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {κ α : ℝ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {pot : cfg.T.State → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg}
    {tok : (solverStateRepSel cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul dMul kOff Rcore K pot).τ}
    {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hrepSel : (solverStateRepSel cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul dMul kOff Rcore K pot).rep
      root model tok mem)
    (hCaps : SolverLevelCapsInv F.fmt.precision V vCap eCap model tok.1.1.1 mem)
    (hReg : SolverSelectRegionInv G F.limbs F.fmt.precision m E pLast slot vCap eCap model
      ((solverStateRepFull cfg κ G F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul Rcore).foot root tok.1)
      tok.1.1.1 tok.2 mem)
    (hpre : (minRatioMachineContractWithV F
      (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).pre
      1 model [root, e, heap] mem)
    (hbelow : ∀ a, (solverStateRepSel cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul dMul kOff Rcore K pot).foot
      root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (htreeWord : 2 * tok.1.1.1.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.1.1.1.tree.n + 1) ≤ 4 * F.limbs)
    (hroom : heap + max (F.limbs + LinkCut.PathProg.pathAlloc F.limbs 4 tok.1.1.1.tree.n
        [tok.1.1.1.treeHeap, mem (tok.1.1.1.slots + model.extToInt e), heap + F.limbs])
        (2 + 5 * F.limbs) + F.limbs < 2 ^ w) :
    let L := F.limbs
    let P := F.fmt.precision
    let R := solverStateRepSel cfg κ G L P m V psi k epsExp (detectOffTreeDrainUnit L)
      unit toolMul treeMul dMul kOff Rcore K pot
    ∃ body, p.procs[solverOpsDispatch base 1]? = some body ∧
      ∃ ret cost out tok',
        Runs w p ω body (startState [root, e, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F
          (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).post
          1 model [root, e, heap] mem model out.mem ∧
        R.rep root model tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model tok'.1.1.1 out.mem ∧
        (SolverLevelLayoutAt vCap eCap tok.1.1.1 mem →
          SolverLevelLayoutAt vCap eCap tok'.1.1.1 out.mem) ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap model
          ((solverStateRepFull cfg κ G L P m V psi k epsExp (detectOffTreeDrainUnit L) unit
            toolMul treeMul Rcore).foot root tok'.1) tok'.1.1.1 tok'.2 out.mem ∧
        tok'.1.1.1.intCap = tok.1.1.1.intCap ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        ret ≤ heap + max (L + LinkCut.PathProg.pathAlloc L 4 tok.1.1.1.tree.n
          [tok.1.1.1.treeHeap, mem (tok.1.1.1.slots + model.extToInt e), heap + L])
          (2 + 5 * L) + L ∧
        (∀ a < heap, ¬ R.foot root tok a → out.mem a = mem a) ∧
        (∀ a, R.foot root tok' a → R.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        cost + R.phi root tok' out.mem ≤
          pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 53 * L + 160 +
            R.phi root tok mem ∧
        (∀ B R : ℤ, PathTreeNumericInv tok.1.1.1.tree tok.1.1.1.trees B R →
          PathTreeNumericInv tok'.1.1.1.tree tok'.1.1.1.trees B R) ∧
        tok'.1.1.1.edgeRecords = tok.1.1.1.edgeRecords ∧
        (∀ j < tok.1.1.1.intCap,
          out.mem (tok.1.1.1.edgeRecords + j) = mem (tok.1.1.1.edgeRecords + j)) := by
  dsimp only
  obtain ⟨⟨⟨hrep, hfwd, hghost⟩, ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩,
      hrcG, htcG⟩, hSel, hReemb⟩ := hrepSel
  obtain ⟨hfits, hfitsExp⟩ := hnumInv.fits hrep
  obtain ⟨body, hbody, ret, cost, out, tok1', hr, hpost, hrep', hMeta, hcapQ, hz', hretLo, hretHi,
      hframe', hfoot', hcostHi, hkeep, hrecQ, hptrQ⟩ :=
    solverOps_query_runs hlocalCore hw hfmt4 hp hrep hpre hextEq
      (fun a ha => hbelow a (Or.inl ha)) hz htreeWord htreeWidth hfits hfitsExp hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hframe' hfoot'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  have hReg' := hReg.preserve_of_levelMeta hCaps.1 hMeta hframe' hfoot'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  have htn' : tok1'.tree.n = tok.1.1.1.tree.n :=
    (solverStateRep_tree_n hrep').trans (solverStateRep_tree_n hrep).symm
  obtain ⟨B, R0, hnB, hcapB, hthrB, hfitB⟩ := hnumInv
  have hrepS' : (solverStateRepShift cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit Rcore).rep root model (tok1', tok.1.1.2) out.mem :=
    ⟨hrep', hfwd, hghost⟩
  refine ⟨body, hbody, ret, cost, out, (((tok1', tok.1.1.2), tok.1.2), tok.2),
    hr, hpost,
    ⟨⟨hrepS', ⟨⟨⟨hextEq, hlen, hBr⟩, B, R0, hkeep B R0 hnB, htn' ▸ hcapB, hthrB, hfitB⟩,
      hreach, hnfB, hcapQ.trans hintCapB⟩, hrcG, htcG⟩, hSel', hReemb⟩,
    hCaps', fun hL => hMeta.to_levelLayout hCaps.1 hL, hReg', hcapQ, hz', hretLo, hretHi,
    fun a ha hnf => hframe' a ha (fun hf => hnf (Or.inl hf)),
    fun a ha => ha.elim (fun hf => (hfoot' a hf).imp Or.inl id) (fun ho => Or.inl (Or.inr ho)),
    ?_, hkeep, hrecQ, hptrQ⟩
  have hphi0 := solverStateRepFull_phi_eq (κ := κ) (G := G) (unit := unit) (toolMul := toolMul)
    (treeMul := treeMul) (tok := tok.1) ⟨hrep, hfwd, hghost⟩ hrcG htcG
  have hphi1 := solverStateRepFull_phi_eq (κ := κ) (G := G) (unit := unit) (toolMul := toolMul)
    (treeMul := treeMul) (tok := ((tok1', tok.1.1.2), tok.1.2)) hrepS' hrcG htcG
  dsimp only at hphi1
  change cost + ((solverStateRepFull cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul Rcore).phi root
      ((tok1', tok.1.1.2), tok.1.2) out.mem + K * tok.2.reembPot) ≤
    _ + ((solverStateRepFull cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul Rcore).phi root tok.1 mem +
      K * tok.2.reembPot)
  rw [hphi0, hphi1]
  omega

/-- `solverOps_detect_runs` preserves `SolverLevelCapsInv`, `SolverSelectRegionInv` and the full
`solverStateRepSel` invariant (including footprint, frame, and potential with unchanged
`K * sg.reembPot`). -/
theorem solverOps_detect_preserves_sel
    {w base chainRefreshProc findCycleProc shiftLevelProc m V psi k epsExp
      unit toolMul treeMul dMul kOff vCap eCap K E pLast slot root heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {κ α : ℝ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {pot : cfg.T.State → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg}
    {tok : (solverStateRepSel cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul dMul kOff Rcore K pot).τ}
    {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ} {Bb Rb : ℤ}
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hGE : ∀ e < m, e ∈ G.E) (heps : 0 < cfg.ε)
    (hnumB : PathTreeNumericInv tok.1.1.1.tree tok.1.1.1.trees Bb Rb)
    (hcapBB : 2 * ((2 * tok.1.1.1.tree.n + 1 : ℕ) : ℤ) * (Bb + Rb) < (Num.capacity 4 F.limbs : ℤ))
    (hthrBB : ∀ e ∈ model.extG.E,
      |detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)| ≤ Bb)
    (hrepSel : (solverStateRepSel cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul dMul kOff Rcore K pot).rep
      root model tok mem)
    (hCaps : SolverLevelCapsInv F.fmt.precision V vCap eCap model tok.1.1.1 mem)
    (hReg : SolverSelectRegionInv G F.limbs F.fmt.precision m E pLast slot vCap eCap model
      ((solverStateRepFull cfg κ G F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul Rcore).foot root tok.1)
      tok.1.1.1 tok.2 mem)
    (hpre : (minRatioMachineContractWithV F
      (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).pre
      2 model [root, heap] mem)
    (hbelow : ∀ a, (solverStateRepSel cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul dMul kOff Rcore K pot).foot
      root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (htreeWord : 2 * tok.1.1.1.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.1.1.1.tree.n + 1) ≤ 4 * F.limbs)
    (hroom : heap + 1 + m + ((algorithm2_detect cfg model).1.card + 1) *
        detectTreeRoundSpace F.limbs + tok.1.1.1.offReadyCount * (2 + 4 * F.limbs) < 2 ^ w) :
    let L := F.limbs
    let P := F.fmt.precision
    let R := solverStateRepSel cfg κ G L P m V psi k epsExp (detectOffTreeDrainUnit L)
      unit toolMul treeMul dMul kOff Rcore K pot
    let S := (algorithm2_detect cfg model).1
    ∃ body, p.procs[solverOpsDispatch base 2]? = some body ∧
      ∃ ret cost out tok',
        Runs w p ω body (startState [root, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F
          (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).post
          2 model [root, heap] mem (algorithm2_detect cfg model).2 out.mem ∧
        R.rep root (algorithm2_detect cfg model).2 tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap (algorithm2_detect cfg model).2 tok'.1.1.1 out.mem ∧
        (SolverLevelLayoutAt vCap eCap tok.1.1.1 mem →
          SolverLevelLayoutAt vCap eCap tok'.1.1.1 out.mem) ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap (algorithm2_detect cfg model).2
          ((solverStateRepFull cfg κ G L P m V psi k epsExp (detectOffTreeDrainUnit L) unit
            toolMul treeMul Rcore).foot root tok'.1) tok'.1.1.1 tok'.2 out.mem ∧
        tok'.1.1.1.intCap = tok.1.1.1.intCap ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        ret ≤ heap + 1 + m + (S.card + 1) * detectTreeRoundSpace L +
          tok.1.1.1.offReadyCount * (2 + 4 * L) ∧
        (∀ a < heap, ¬ R.foot root tok a → out.mem a = mem a) ∧
        (∀ a, R.foot root tok' a → R.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        cost + R.phi root tok' out.mem ≤
          (S.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 +
            R.phi root tok mem ∧
        PathTreeNumericInv tok'.1.1.1.tree tok'.1.1.1.trees Bb Rb ∧
        (OffTreeRecSep model L mem tok.1.1.1.edgeRecords →
          OffTreeRecSep (algorithm2_detect cfg model).2 L out.mem tok'.1.1.1.edgeRecords) := by
  dsimp only
  obtain ⟨⟨⟨hrep, hfwd, hghost⟩, ⟨⟨⟨hextEq, hlen, hBr⟩, _, _, _, _, _, hfitNeg⟩,
      hreach, hnfB, hintCapB⟩, hrcG, htcG⟩, hSel, hReemb⟩ := hrepSel
  obtain ⟨body, hbody, ret, cost, out, tok1', hr, hpost, hrep', hMeta, hcapD, hnum', hz',
      hretLo, hretHi, hframe', hfoot', hcostHi, hsepD⟩ :=
    solverOps_detect_runs hlocalCore hw hfmt4 hLpos hp (fun e he => hextEq ▸ hGE e he) heps hlen
      hnumB hcapBB hthrBB hfitNeg hrep hpre (fun a ha => hbelow a (Or.inl ha)) hz htreeWord
      htreeWidth hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hframe' hfoot'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  have hReg' := hReg.preserve_of_levelMeta hCaps.1 hMeta hframe' hfoot'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  have htn' : tok1'.tree.n = tok.1.1.1.tree.n :=
    (solverStateRep_tree_n hrep').trans (solverStateRep_tree_n hrep).symm
  have hch : (algorithm2_detect cfg model).2.chain = model.chain := rfl
  have hrcEq : runtimeCredit cfg (algorithm2_detect cfg model).2 = runtimeCredit cfg model := rfl
  have htcEq : treeCredit cfg (algorithm2_detect cfg model).2 = treeCredit cfg model := rfl
  have hrepS' : (solverStateRepShift cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit Rcore).rep root (algorithm2_detect cfg model).2
      (tok1', tok.1.1.2) out.mem := ⟨hrep', hch ▸ hfwd, hch ▸ hghost⟩
  refine ⟨body, hbody, ret, cost, out, (((tok1', tok.1.1.2), tok.1.2), tok.2),
    hr, hpost,
    ⟨⟨hrepS', ⟨⟨ordSolverReachBase_detect ⟨hextEq, hlen, hBr⟩,
      Bb, Rb, hnum', htn' ▸ hcapBB, hthrBB, hfitNeg⟩, ordSolverReached_detect hreach,
      hnfB, hcapD.trans hintCapB⟩, hrcEq ▸ hrcG, htcEq ▸ htcG⟩, hSel', hReemb⟩,
    hCaps', fun hL => hMeta.to_levelLayout hCaps.1 hL, hReg', hcapD, hz', hretLo, hretHi,
    fun a ha hnf => hframe' a ha (fun hf => hnf (Or.inl hf)),
    fun a ha => ha.elim (fun hf => (hfoot' a hf).imp Or.inl id) (fun ho => Or.inl (Or.inr ho)),
    ?_, hnum', hsepD⟩
  have hphi0 := solverStateRepFull_phi_eq (κ := κ) (G := G) (unit := unit) (toolMul := toolMul)
    (treeMul := treeMul) (tok := tok.1) ⟨hrep, hfwd, hghost⟩ hrcG htcG
  have hphi1 := solverStateRepFull_phi_eq (κ := κ) (G := G) (unit := unit) (toolMul := toolMul)
    (treeMul := treeMul) (tok := ((tok1', tok.1.1.2), tok.1.2)) hrepS' (hrcEq ▸ hrcG) (htcEq ▸ htcG)
  dsimp only at hphi1
  change cost + ((solverStateRepFull cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul Rcore).phi root
      ((tok1', tok.1.1.2), tok.1.2) out.mem + K * tok.2.reembPot) ≤
    _ + ((solverStateRepFull cfg κ G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) unit toolMul treeMul Rcore).phi root tok.1 mem +
      K * tok.2.reembPot)
  rw [hphi0, hphi1, hch, hrcEq, htcEq]
  omega

/-! ## 3. `Eval`, `Select` / `SelectHeap`, and `Find` / `FindHeap` preserve both regions -/

/-- Any cycle evaluator meeting `OrdCycleRouteEvalSpecW` (in particular `evalCycleBody_meets_spec`)
preserves both `SolverLevelCapsInv` and `SolverSelectInv`. -/
theorem evalCycle_preserves_both
    {w L P m V psi k epsExp drainUnit vCap eCap dMul kOff evalCycleProc evalSpace evalBudget
      maxEdges maxPaths root edgesBase pathsBase workHeap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {B R : ℤ} {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    (hEval : OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p
      evalCycleProc evalSpace evalBudget maxEdges maxPaths)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hℓNN : ∀ e ∈ model.extG.E, 0 ≤ model.extℓ e)
    (hedMax : edges.length ≤ maxEdges) (hptMax : paths.length ≤ maxPaths)
    (hno : NoOppositePairs edges)
    (hEdAt : ExplicitEdgesAt mem edgesBase edges)
    (hPtAt : PathEndpointsAt mem pathsBase paths)
    (hRoute : CycleRouteAt model edges paths)
    (heHi : edgesBase + 2 * edges.length ≤ workHeap)
    (hpHi : pathsBase + 2 * paths.length ≤ workHeap)
    (hnfEd : ∀ x < 2 * edges.length,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (edgesBase + x))
    (hnfPt : ∀ x < 2 * paths.length,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (pathsBase + x))
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < workHeap)
    (hz : ZeroFrom mem workHeap)
    (hroom : workHeap + evalSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ body, p.procs[evalCycleProc]? = some body ∧
      ∃ nextHeap cost out tok' inner norm,
        Runs w p ω body
          (startState [root, edgesBase, edges.length, pathsBase, paths.length, workHeap] mem pos)
          (.returned nextHeap) out cost ∧
        Rrep.rep root model tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model (Rrep.foot root tok')
          (LevelMetaFoot tok') sg out.mem ∧
        PathIntAt out.mem workHeap 4 L inner ∧
        PathIntAt out.mem (workHeap + L) 4 L norm ∧
        ZeroFrom out.mem nextHeap ∧
        cost + Rrep.phi root tok' out.mem ≤ evalBudget + Rrep.phi root tok mem := by
  obtain ⟨body, hbody, hRun⟩ := hEval
  obtain ⟨nextHeap, cost, out, tok', inner, norm, hr, _, _, _, _, _, hIn, hNm, _, _, _, _, _,
      hrep', hMeta, _, _, _, hz', hfr', hft', hcost⟩ :=
    hRun root edgesBase pathsBase workHeap pos ω mem model tok B R edges paths
      hrep hnum hoff hBd hcapE hcapT hlogW hℓNN hedMax hptMax hno hEdAt hPtAt hRoute
      heHi hpHi hnfEd hnfPt (fun a ha => hbelow a (Or.inl ha)) hz hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hfr' hft'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  exact ⟨body, hbody, nextHeap, cost, out, tok', inner, norm, hr, hrep', hCaps', hSel',
    hIn, hNm, hz', hcost⟩

/-- Any route selector meeting `OrdCycleRouteSelectSpecW` preserves both `SolverLevelCapsInv`
and `SolverSelectInv`. -/
theorem selectRoute_preserves_both
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit vCap eCap dMul kOff
      selectRouteProc selectSpace selectBudget maxEdges maxPaths root descBase workHeap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {B R : ℤ}
    (hSelSpec : OrdCycleRouteSelectSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      cfg Rcore p selectRouteProc selectSpace selectBudget maxEdges maxPaths)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hCapF : WireCapFacts capExp limbMul L capLimit model)
    (hLv : ShiftLoopLevelFacts cfg model.chain)
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < descBase)
    (hwh : descBase + 6 = workHeap)
    (hz : ZeroFrom mem descBase)
    (hroom : workHeap + selectSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ body, p.procs[selectRouteProc]? = some body ∧
      ∃ work1 cost out tok' edges paths,
        Runs w p ω body (startState [root, descBase, workHeap] mem pos) (.returned work1) out cost ∧
        Rrep.rep root model tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model (Rrep.foot root tok')
          (LevelMetaFoot tok') sg out.mem ∧
        CycleRouteAt model edges paths ∧
        ZeroFrom out.mem work1 ∧
        cost + Rrep.phi root tok' out.mem ≤ selectBudget + Rrep.phi root tok mem := by
  obtain ⟨body, hbody, hRun⟩ := hSelSpec
  obtain ⟨work1, cost, out, tok', edges, paths, hr, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hRoute, _, _, _, hrep', hMeta, _, _, _, hz', hfr', hft', hcost⟩ :=
    hRun root descBase workHeap pos ω mem model tok B R hrep hnum hoff hBd hCapF hLv
      (fun a ha => hbelow a (Or.inl ha)) hwh hz hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hfr' hft'
    (fun a ha => hbelow a (Or.inr ha)) (by omega) rfl rfl rfl
  exact ⟨body, hbody, work1, cost, out, tok', edges, paths, hr, hrep', hCaps', hSel',
    hRoute, hz', hcost⟩

/-- Any heap-backed route selector meeting `OrdCycleRouteSelectSpecHeap` (in particular
`ordCycleRouteSelectSpecHeap_proved`) takes its select-heap hypotheses from `SolverSelectInv`
via `solverSelect_findHyps` and preserves both `SolverLevelCapsInv` and `SolverSelectInv`. -/
theorem selectRouteHeap_preserves_both
    {w L P m V psi k epsExp drainUnit dMul kOff vCap eCap
      selectRouteProc selectSpace selectBudget maxEdges maxPaths root descBase workHeap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {B R : ℤ}
    (hSelSpec : OrdCycleRouteSelectSpecHeap w L P m V psi k epsExp drainUnit dMul kOff
      cfg Rcore p selectRouteProc selectSpace selectBudget maxEdges maxPaths)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hEmbBd : ∀ i < cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeCore i).E \
      (model.chain.toTreeChain.activeS i).E,
      (model.chain.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < descBase)
    (hwh : descBase + 6 = workHeap)
    (hz : ZeroFrom mem descBase)
    (hroom : workHeap + selectSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ body, p.procs[selectRouteProc]? = some body ∧
      ∃ work1 cost out tok' edges paths,
        Runs w p ω body (startState [root, descBase, workHeap] mem pos) (.returned work1) out cost ∧
        Rrep.rep root model tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model (Rrep.foot root tok')
          (LevelMetaFoot tok') sg out.mem ∧
        CycleRouteAt model edges paths ∧
        ZeroFrom out.mem work1 ∧
        cost + Rrep.phi root tok' out.mem ≤ selectBudget + Rrep.phi root tok mem := by
  obtain ⟨hLk, hhbRd, hhbLt, hMatch, hMetaE, hlocEnd, hlocDisj, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod⟩ :=
    solverSelect_findHyps hSel (fun _ hm => LevelMetaFoot.mem_foot hrep hm) hbelow
  obtain ⟨body, hbody, hRun⟩ := hSelSpec
  obtain ⟨work1, cost, out, tok', edges, paths, hr, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hRoute, _, _, _, hrep', hMeta, _, _, _, _, hz', hfr', hft', hcost⟩ :=
    hRun root descBase workHeap pos sg.size ω mem model tok sg.loc B R G₀ σ σ_mwu γ_ℓ γ_c
      hrep hnum hoff hBd hMod hlogW hmaxE1 hmaxEP hEmbBd hcapE hcapT hLk hhbRd hhbLt
      hMatch hMetaE hlocEnd hlocDisj (fun a ha => hbelow a (Or.inl ha)) hwh hz hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hfr' hft'
    (fun a ha => hbelow a (Or.inr ha)) (by omega) rfl rfl rfl
  exact ⟨body, hbody, work1, cost, out, tok', edges, paths, hr, hrep', hCaps', hSel',
    hRoute, hz', hcost⟩

/-- Any cycle finder meeting `FindCycleStepSpecW` (in particular `findCycleStepSpecW_wired`)
preserves both `SolverLevelCapsInv` and `SolverSelectInv`. -/
theorem findCycle_preserves_both
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit vCap eCap dMul kOff
      findCycleProc findSpace findBudget maxEdges maxPaths root heap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {B R : ℤ}
    (hFind : FindCycleStepSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      cfg Rcore p findCycleProc findSpace findBudget maxEdges maxPaths)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hCapF : WireCapFacts capExp limbMul L capLimit model)
    (hLv : ShiftLoopLevelFacts cfg model.chain)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hℓNN : ∀ e ∈ model.extG.E, 0 ≤ model.extℓ e)
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < heap)
    (hz : ZeroFrom mem heap)
    (hroom : heap + findSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ body, p.procs[findCycleProc]? = some body ∧
      ∃ nextHeap cost out tok' inner norm edges paths,
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        CycleDescriptorAt model L P out.mem heap nextHeap inner norm edges paths ∧
        Rrep.rep root model tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model (Rrep.foot root tok')
          (LevelMetaFoot tok') sg out.mem ∧
        ZeroFrom out.mem nextHeap ∧
        cost + Rrep.phi root tok' out.mem ≤ findBudget + Rrep.phi root tok mem := by
  obtain ⟨body, hbody, hRun⟩ := hFind
  obtain ⟨nextHeap, cost, out, tok', inner, norm, edges, paths, hr, _, _, _, _, _, _, _, _, _,
      hdesc, hrep', hMeta, _, _, _, hz', hfr', hft', hcost⟩ :=
    hRun root heap pos ω mem model tok B R hrep hnum hoff hBd hCapF hLv hcapE hcapT hlogW hℓNN
      (fun a ha => hbelow a (Or.inl ha)) hz hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hfr' hft'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  exact ⟨body, hbody, nextHeap, cost, out, tok', inner, norm, edges, paths, hr, hdesc,
    hrep', hCaps', hSel', hz', hcost⟩

/-- Any heap-backed cycle finder meeting `FindCycleStepSpecHeap` (in particular
`findCycleStepSpecHeap_proved`) discharges its select-heap hypotheses from `SolverSelectInv`
via `solverSelect_findHyps` and preserves both `SolverLevelCapsInv` and `SolverSelectInv`. -/
theorem findCycleHeap_preserves_both
    {w L P m V psi k epsExp drainUnit dMul kOff vCap eCap
      findCycleProc findSpace findBudget maxEdges maxPaths root heap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {B R : ℤ}
    (hFind : FindCycleStepSpecHeap w L P m V psi k epsExp drainUnit dMul kOff
      cfg Rcore p findCycleProc findSpace findBudget maxEdges maxPaths)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hEmbBd : ∀ i < cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeCore i).E \
      (model.chain.toTreeChain.activeS i).E,
      (model.chain.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < heap)
    (hz : ZeroFrom mem heap)
    (hroom : heap + findSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ body, p.procs[findCycleProc]? = some body ∧
      ∃ nextHeap cost out tok' inner norm edges paths,
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        CycleDescriptorAt model L P out.mem heap nextHeap inner norm edges paths ∧
        Rrep.rep root model tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model (Rrep.foot root tok')
          (LevelMetaFoot tok') sg out.mem ∧
        ZeroFrom out.mem nextHeap ∧
        cost + Rrep.phi root tok' out.mem ≤ findBudget + Rrep.phi root tok mem := by
  obtain ⟨hLk, hhbRd, hhbLt, hMatch, hMetaE, hlocEnd, hlocDisj, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod⟩ :=
    solverSelect_findHyps hSel (fun _ hm => LevelMetaFoot.mem_foot hrep hm) hbelow
  obtain ⟨body, hbody, hRun⟩ := hFind
  obtain ⟨nextHeap, cost, out, tok', inner, norm, edges, paths, hr, _, _, _, _, _, _, _, _, _,
      hdesc, hrep', hMeta, _, _, _, _, hz', hfr', hft', hcost⟩ :=
    hRun root heap pos sg.size ω mem model tok sg.loc B R G₀ σ σ_mwu γ_ℓ γ_c
      hrep hnum hoff hBd hMod hlogW hmaxE1 hmaxEP hEmbBd hcapE hcapT hLk hhbRd hhbLt
      hMatch hMetaE hlocEnd hlocDisj (fun a ha => hbelow a (Or.inl ha)) hz hroom
  obtain ⟨hCaps', hSel'⟩ := hMeta.preserve_both hCaps hSel hfr' hft'
    (fun a ha => hbelow a (Or.inr ha)) le_rfl rfl rfl rfl
  exact ⟨body, hbody, nextHeap, cost, out, tok', inner, norm, edges, paths, hr, hdesc,
    hrep', hCaps', hSel', hz', hcost⟩

end MinCostFlow.MinRatio
