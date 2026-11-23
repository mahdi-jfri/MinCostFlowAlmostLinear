module

public import MinCostFlow.MinRatio.WireChainCoreBranchBStep
public import MinCostFlow.MinRatio.WireChainCoreBranchBTerm
public import MinCostFlow.MinRatio.WireChainCoreBranchBInterior
import WordRAM.Tactic

/-!
# Shared definitions and invariants for the Branch B level-update loop (`WireChainCoreBranchBLoopDefs`)

Provides `wireBranchBLoopBody`, `wireBranchBLoopAndTermStmt`, `BranchBStatic`,
`BranchBPreservedAddr`, `BranchBCoresDisjStatic`, and the unified postcondition `BranchBLoopPost`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- One iteration body of the Branch B level-update loop at `idx = reg 96 < d`. -/
@[expose] def wireBranchBLoopBody
    (updCore readGraph readLSF readOrd initCore coreLenProc dgApply updateCoreLenProc
      lastInit : ℕ) : Stmt :=
  .assign 16 (.load (.reg 10)) ;;
  .assign 17 (.load (.bin .add (.reg 85) (.reg 96))) ;;
  .assign 18 (.load (.bin .add (.reg 74) (.reg 96))) ;;
  .cond (.bin .lt (.reg 18) (.bin .add (.reg 17) (.reg 16)))
    (wireBranchBInteriorRebuildStep dgApply readOrd initCore readGraph readLSF coreLenProc lastInit ;;
     .assign 96 (.reg 75))
    (wireBranchBNoRebuildStep updCore readLSF dgApply updateCoreLenProc ;;
     .assign 96 (.bin .add (.reg 96) (.const 1)))

/-- Branch B `updateLoop` while-loop followed by conditional terminal rebuild when `reg 97 = 0`. -/
@[expose] def wireBranchBLoopAndTermStmt
    (updCore readGraph readLSF readOrd initCore coreLenProc dgApply updateCoreLenProc
      lastInit : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 96) (.reg 75))
    (wireBranchBLoopBody updCore readGraph readLSF readOrd initCore coreLenProc dgApply
      updateCoreLenProc lastInit) ;;
  .cond (.reg 97) .nop
    (wireBranchBTerminalStep readGraph readLSF coreLenProc readOrd lastInit)

theorem wireBranchBLoopBody_noRand
    (updCore readGraph readLSF readOrd initCore coreLenProc dgApply updateCoreLenProc lastInit : ℕ) :
    (wireBranchBLoopBody updCore readGraph readLSF readOrd initCore coreLenProc dgApply
      updateCoreLenProc lastInit).NoRand := by
  simp [wireBranchBLoopBody, wireBranchBInteriorRebuildStep_noRand,
    wireBranchBNoRebuildStep_noRand, Stmt.NoRand]

theorem wireBranchBLoopAndTermStmt_noRand
    (updCore readGraph readLSF readOrd initCore coreLenProc dgApply updateCoreLenProc lastInit : ℕ) :
    (wireBranchBLoopAndTermStmt updCore readGraph readLSF readOrd initCore coreLenProc dgApply
      updateCoreLenProc lastInit).NoRand := by
  simp [wireBranchBLoopAndTermStmt, wireBranchBLoopBody_noRand,
    wireBranchBTerminalStep_noRand, Stmt.NoRand]

theorem chainLen_congr_lt (C₁ C₂ : TreeChain) (ℓ : ℕ → ℝ) (k : ℕ)
    (h : ∀ m < k, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainLen ℓ k = C₂.chainLen ℓ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [TreeChain.chainLen]
    rw [h k (Nat.lt_succ_self k), ih (fun m hm => h m (Nat.lt_succ_of_lt hm))]

/-- Static layout and pairwise disjointness context preserved across all iterations of
`wireBranchBLoopAndTerm_runs`. -/
structure BranchBStatic (d L : ℕ)
    (handle table handleBase branchBase lvlMTable levelMeta rebuildCountBase updCountBase
      heapFloor : ℕ) (vcOf ecOf gPtr0 lPtr0 coreHandle0 : ℕ → ℕ) : Prop where
  handleLt : handle + 18 ≤ heapFloor
  tableLt : table + d ≤ heapFloor
  hbLt : handleBase + d < heapFloor
  bbLt : branchBase + d < heapFloor
  lvlMLt : lvlMTable + d ≤ heapFloor
  metaLt : levelMeta + 2 * d ≤ heapFloor
  rcLt : rebuildCountBase + d < heapFloor
  ucLt : updCountBase + d ≤ heapFloor
  gLt : ∀ j < d, gPtr0 j + dynGraphSize (vcOf j) (ecOf j) ≤ heapFloor
  lLt : ∀ j < d, lPtr0 j + ecOf j * L ≤ heapFloor
  sepHB : handleBase + d < branchBase ∨ branchBase + d < handleBase
  sepHM : handleBase + d < lvlMTable ∨ lvlMTable + d ≤ handleBase
  sepBM : branchBase + d < lvlMTable ∨ lvlMTable + d ≤ branchBase
  sepHL : handleBase + d < levelMeta ∨ levelMeta + 2 * d ≤ handleBase
  sepBL : branchBase + d < levelMeta ∨ levelMeta + 2 * d ≤ branchBase
  sepML : lvlMTable + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ lvlMTable
  sepRCH : rebuildCountBase + d < handle ∨ handle + 18 ≤ rebuildCountBase
  sepRCM : rebuildCountBase + d < lvlMTable ∨ lvlMTable + d ≤ rebuildCountBase
  sepRCHB : rebuildCountBase + d < handleBase ∨ handleBase + d < rebuildCountBase
  sepRCBB : rebuildCountBase + d < branchBase ∨ branchBase + d < rebuildCountBase
  sepRCLM : rebuildCountBase + d < levelMeta ∨ levelMeta + 2 * d ≤ rebuildCountBase
  sepRCUC : rebuildCountBase + d < updCountBase ∨ updCountBase + d ≤ rebuildCountBase
  sepUCHB : updCountBase + d ≤ handleBase ∨ handleBase + d < updCountBase
  sepUCBB : updCountBase + d ≤ branchBase ∨ branchBase + d < updCountBase
  sepUCLM : updCountBase + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ updCountBase
  sepUCH : updCountBase + d ≤ handle ∨ handle + 18 ≤ updCountBase
  sepUCM : updCountBase + d ≤ lvlMTable ∨ lvlMTable + d ≤ updCountBase
  sepTabUC : table + d ≤ updCountBase ∨ updCountBase + d ≤ table
  sepTabHB : table + d ≤ handleBase ∨ handleBase + d < table
  sepTabBB : table + d ≤ branchBase ∨ branchBase + d < table
  sepTabLM : table + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ table
  sepTabRC : table + d ≤ rebuildCountBase ∨ rebuildCountBase + d < table
  gSep : ∀ j < d, ∀ a, gPtr0 j ≤ a → a < gPtr0 j + dynGraphSize (vcOf j) (ecOf j) →
    (a < handle ∨ handle + 18 ≤ a) ∧
    (a < table ∨ table + d ≤ a) ∧
    (a < handleBase ∨ handleBase + d < a) ∧
    (a < branchBase ∨ branchBase + d < a) ∧
    (a < lvlMTable ∨ lvlMTable + d ≤ a) ∧
    (a < levelMeta ∨ levelMeta + 2 * d ≤ a) ∧
    (a < rebuildCountBase ∨ rebuildCountBase + d < a) ∧
    (a < updCountBase ∨ updCountBase + d ≤ a) ∧
    (∀ r < d, (a < lPtr0 r ∨ lPtr0 r + ecOf r * L ≤ a) ∧
      (r ≠ j → a < gPtr0 r ∨ gPtr0 r + dynGraphSize (vcOf r) (ecOf r) ≤ a))
  lSep : ∀ j < d, ∀ a, lPtr0 j ≤ a → a < lPtr0 j + ecOf j * L →
    (a < handle ∨ handle + 18 ≤ a) ∧
    (a < table ∨ table + d ≤ a) ∧
    (a < handleBase ∨ handleBase + d < a) ∧
    (a < branchBase ∨ branchBase + d < a) ∧
    (a < lvlMTable ∨ lvlMTable + d ≤ a) ∧
    (a < levelMeta ∨ levelMeta + 2 * d ≤ a) ∧
    (a < rebuildCountBase ∨ rebuildCountBase + d < a) ∧
    (a < updCountBase ∨ updCountBase + d ≤ a)
  lPairSep : ∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
    lPtr0 j₁ + ecOf j₁ * L ≤ lPtr0 j₂ ∨ lPtr0 j₂ + ecOf j₂ * L ≤ lPtr0 j₁

/-- Addresses below `curHeap` untouched by `wireBranchBLoopAndTermStmt` starting at `idx`. -/
@[expose] def BranchBPreservedAddr {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (L idx handleBase branchBase levelMeta updCountBase rebuildCountBase : ℕ)
    (vcOf ecOf gPtr0 lPtr0 coreHandle0 : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ) (a : ℕ) : Prop :=
  let d := cfg.P.d
  (∀ j < d, ¬ Rcore.foot (coreHandle0 j) (coreTok0 j) a) ∧
  (∀ j, idx ≤ j → j < d →
    (a < gPtr0 j ∨ gPtr0 j + dynGraphSize (vcOf j) (ecOf j) ≤ a) ∧
    (a < lPtr0 j ∨ lPtr0 j + ecOf j * L ≤ a)) ∧
  (a < handleBase + idx ∨ handleBase + d < a) ∧
  (a < branchBase + idx ∨ branchBase + d < a) ∧
  (a < levelMeta + idx ∨ levelMeta + d ≤ a) ∧
  (a < levelMeta + d + idx ∨ levelMeta + 2 * d ≤ a) ∧
  (a < updCountBase + idx ∨ updCountBase + d ≤ a) ∧
  (a < rebuildCountBase + idx ∨ rebuildCountBase + d < a)

/-- Disjointness of all permanent static arrays and graph/length blocks from core footprints. -/
@[expose] def BranchBCoresDisjStatic {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (L handle table handleBase branchBase lvlMTable levelMeta rebuildCountBase updCountBase : ℕ)
    (vcOf ecOf gPtr0 lPtr0 coreHandle0 : ℕ → ℕ) (coreTok : ℕ → Rcore.τ) : Prop :=
  let d := cfg.P.d
  ∀ r < d,
    (∀ a, handle ≤ a → a < handle + 18 → ¬ Rcore.foot (coreHandle0 r) (coreTok r) a) ∧
    (∀ j < d, ¬ Rcore.foot (coreHandle0 r) (coreTok r) (table + j)) ∧
    (∀ j ≤ d, ¬ Rcore.foot (coreHandle0 r) (coreTok r) (handleBase + j) ∧
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) (branchBase + j)) ∧
    (∀ j < d, ¬ Rcore.foot (coreHandle0 r) (coreTok r) (lvlMTable + j) ∧
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) (levelMeta + j) ∧
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) (levelMeta + d + j) ∧
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) (updCountBase + j) ∧
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) (rebuildCountBase + j)) ∧
    (∀ j < d, ∀ a, gPtr0 j ≤ a → a < gPtr0 j + dynGraphSize (vcOf j) (ecOf j) →
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) a) ∧
    (∀ j < d, ∀ a, lPtr0 j ≤ a → a < lPtr0 j + ecOf j * L →
      ¬ Rcore.foot (coreHandle0 r) (coreTok r) a)

theorem branchBCoresDisjStatic_update {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {L handle table handleBase branchBase lvlMTable levelMeta rebuildCountBase updCountBase
      heapFloor curHeap j0 : ℕ}
    {vcOf ecOf gPtr0 lPtr0 coreHandle0 : ℕ → ℕ} {coreTok : ℕ → Rcore.τ} {tokNew : Rcore.τ}
    (S : BranchBStatic cfg.P.d L handle table handleBase branchBase lvlMTable levelMeta
      rebuildCountBase updCountBase heapFloor vcOf ecOf gPtr0 lPtr0 coreHandle0)
    (hFloor : heapFloor ≤ curHeap)
    (hOld : BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L handle table handleBase
      branchBase lvlMTable levelMeta rebuildCountBase updCountBase vcOf ecOf gPtr0 lPtr0
      coreHandle0 coreTok)
    (hFootNew : ∀ a, Rcore.foot (coreHandle0 j0) tokNew a →
      Rcore.foot (coreHandle0 j0) (coreTok j0) a ∨ curHeap ≤ a) :
    BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L handle table handleBase branchBase
      lvlMTable levelMeta rebuildCountBase updCountBase vcOf ecOf gPtr0 lPtr0 coreHandle0
      (fun r => if r = j0 then tokNew else coreTok r) := by
  intro r hr
  by_cases hrj : r = j0
  · subst hrj
    simp only [↓reduceIte]
    have hkill (a : ℕ) (ha : a < heapFloor) (hn : ¬ Rcore.foot (coreHandle0 r) (coreTok r) a) :
        ¬ Rcore.foot (coreHandle0 r) tokNew a := fun hf => (hFootNew a hf).elim hn (by omega)
    obtain ⟨hH, hT, hHB, hM, hG, hL⟩ := hOld r hr
    refine ⟨fun a ha1 ha2 => hkill a (by have := S.handleLt; omega) (hH a ha1 ha2),
      fun j hj => hkill _ (by have := S.tableLt; omega) (hT j hj),
      fun j hj => ⟨hkill _ (by have := S.hbLt; omega) (hHB j hj).1,
        hkill _ (by have := S.bbLt; omega) (hHB j hj).2⟩,
      fun j hj => ⟨hkill _ (by have := S.lvlMLt; omega) (hM j hj).1,
        hkill _ (by have := S.metaLt; omega) (hM j hj).2.1,
        hkill _ (by have := S.metaLt; omega) (hM j hj).2.2.1,
        hkill _ (by have := S.ucLt; omega) (hM j hj).2.2.2.1,
        hkill _ (by have := S.rcLt; omega) (hM j hj).2.2.2.2⟩,
      fun j hj a ha1 ha2 => hkill a (by have := S.gLt j hj; omega) (hG j hj a ha1 ha2),
      fun j hj a ha1 ha2 => hkill a (by have := S.lLt j hj; omega) (hL j hj a ha1 ha2)⟩
  · simp only [hrj, ↓reduceIte]; exact hOld r hr

/-- Unified postcondition of `wireBranchBLoopAndTermStmt` transitioning from `(idx, ch, st)` to
`next`. -/
@[expose] def BranchBLoopPost {w L P lastMul dgCap termUpdSpace termUpdCost
      initCore dgApply coreLenProc updateCoreLenProc lastInit
      handleBase branchBase levelMeta rebuildCountBase updCountBase
      termHandle0 vcLast0 ecLast0 termTok0 : ℕ}
    {levelSpace levelCost updStepSpace updStepCost vcOf ecOf gPtr0 lPtr0 coreHandle0 : ℕ → ℕ}
    {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ} {ω : ℕ → Bool}
    (idx : ℕ) (ch next : ChainState cfg.T cfg.P) (st : State) (coreTok0 : ℕ → Rcore.τ) : Prop :=
  ∃ (out : State) (cost vcLast ecLast termTok : ℕ) (coreTok' : ℕ → Rcore.τ),
    Runs w p ω
      (wireBranchBLoopAndTermStmt (opCore 0) (opCore 3) (opCore 2) (opCore 5) initCore
        coreLenProc dgApply updateCoreLenProc lastInit)
      st .normal out cost ∧
    st.regs 4 ≤ out.regs 4 ∧
    out.regs 4 ≤ st.regs 4 + (Finset.Ico idx cfg.P.d).sum updStepSpace + (1 + dgCap) +
      (Finset.Ico idx cfg.P.d).sum levelSpace + termUpdSpace ∧
    ZeroFrom out.mem (out.regs 4) ∧
    (∀ r, 70 ≤ r → r ≠ 96 → r ≠ 97 → out.regs r = st.regs r) ∧
    ch.totalRuntime ≤ next.totalRuntime ∧
    (∀ j < cfg.P.d,
      out.mem (branchBase + j) = next.bran j ∧
      next.bran j < cfg.P.k ∧ out.mem (handleBase + j) < 2 ^ w ∧
      (out.mem (handleBase + j) = coreHandle0 j ∨
        (st.regs 4 ≤ out.mem (handleBase + j) ∧ out.mem (handleBase + j) ≤ out.regs 4)) ∧
      Rcore.rep (out.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok' j) out.mem ∧
      (∀ a, Rcore.foot (out.mem (handleBase + j)) (coreTok' j) a →
        (j < cfg.P.d ∧ Rcore.foot (coreHandle0 j) (coreTok0 j) a) ∨
          (st.regs 4 ≤ a ∧ a < out.regs 4))) ∧
    (∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
      ∀ a, Rcore.foot (out.mem (handleBase + j₁)) (coreTok' j₁) a →
        ¬ Rcore.foot (out.mem (handleBase + j₂)) (coreTok' j₂) a) ∧
    (∀ j < cfg.P.d, ∃ vc ec,
      DynGraphAt out.mem (out.mem (levelMeta + cfg.P.d + j)) vc ec (next.G j) ∧
      EdgeValuesAt out.mem (out.mem (levelMeta + j)) 4 L P (next.G j).E
        (next.toTreeChain.chainLen next.ℓ j) ∧
      ((out.mem (levelMeta + cfg.P.d + j) = gPtr0 j ∧ vc = vcOf j ∧ ec = ecOf j) ∨
        (st.regs 4 ≤ out.mem (levelMeta + cfg.P.d + j) ∧
          out.mem (levelMeta + cfg.P.d + j) + dynGraphSize vc ec ≤ out.regs 4)) ∧
      ((out.mem (levelMeta + j) = lPtr0 j ∧ ec = ecOf j) ∨
        (st.regs 4 ≤ out.mem (levelMeta + j) ∧
          out.mem (levelMeta + j) + ec * L ≤ out.regs 4)) ∧
      (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + ec * L →
        (∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok' r) a) ∧
        ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G cfg.P.d).E).foot
          (out.mem (handleBase + cfg.P.d)) termTok a) ∧
      (∀ a, out.mem (levelMeta + cfg.P.d + j) ≤ a →
        a < out.mem (levelMeta + cfg.P.d + j) + dynGraphSize vc ec →
        (∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok' r) a) ∧
        ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G cfg.P.d).E).foot
          (out.mem (handleBase + cfg.P.d)) termTok a)) ∧
    out.mem (branchBase + cfg.P.d) = next.lastBran ∧
    (out.mem (handleBase + cfg.P.d) = termHandle0 ∨ st.regs 4 ≤ out.mem (handleBase + cfg.P.d)) ∧
    (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G cfg.P.d).E).rep
      (out.mem (handleBase + cfg.P.d)) (next.lastK, next.lastLSFs) termTok out.mem ∧
    (∀ a, (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G cfg.P.d).E).foot
        (out.mem (handleBase + cfg.P.d)) termTok a →
      ((LastLevelProgram.lastLevelRepresentation vcLast0 ecLast0 4 L P (ch.G cfg.P.d).E).foot
          termHandle0 termTok0 a ∨
        (st.regs 4 ≤ a ∧ a < out.regs 4)) ∧
      (∀ j < cfg.P.d, ¬ Rcore.foot (out.mem (handleBase + j)) (coreTok' j) a)) ∧
    (∀ j < cfg.P.d,
      out.mem (updCountBase + j) = next.updCount j ∧
      out.mem (rebuildCountBase + j) = next.rebuildCount j) ∧
    (∀ a < st.regs 4,
      BranchBPreservedAddr (cfg := cfg) (Rcore := Rcore) L idx handleBase branchBase levelMeta
        updCountBase rebuildCountBase vcOf ecOf gPtr0 lPtr0 coreHandle0 coreTok0 a →
      out.mem a = st.mem a) ∧
    let phiNew := (Finset.range cfg.P.d).sum
      (fun j => Rcore.phi (out.mem (handleBase + j)) (coreTok' j) out.mem)
    let phiOld := (Finset.range cfg.P.d).sum
      (fun j => Rcore.phi (coreHandle0 j) (coreTok0 j) st.mem)
    ((∃ i₀, idx ≤ i₀ ∧ i₀ < cfg.P.d ∧ 0 < i₀ ∧ next.rebuildCount i₀ = ch.rebuildCount i₀ + 1 ∧
        cost + phiNew ≤
          Psc.mul * (next.totalRuntime - ch.totalRuntime) +
            (Finset.Ico idx (i₀ + 1)).sum updStepCost +
            (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost j + 9) +
            lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) +
            20 * cfg.P.d + 45 * (i₀ - idx) + 200 + phiOld) ∨
      (next.curLastRebuilds = ch.curLastRebuilds + 1 ∧
        cost + phiNew ≤
          Psc.mul * (next.totalRuntime - ch.totalRuntime) +
            (Finset.Ico idx cfg.P.d).sum updStepCost + termUpdCost +
            lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) +
            45 * (cfg.P.d - idx) + 30 + phiOld) ∨
      (cost + phiNew ≤
        Psc.mul * (next.totalRuntime - ch.totalRuntime) +
          (Finset.Ico idx cfg.P.d).sum updStepCost + 45 * (cfg.P.d - idx) + 30 + phiOld))

end MinCostFlow.MinRatio
