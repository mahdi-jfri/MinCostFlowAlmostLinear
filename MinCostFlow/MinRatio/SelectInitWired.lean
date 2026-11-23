module

public import MinCostFlow.MinRatio.SelectInitWiredCore
public import MinCostFlow.MinRatio.SolverSelectRegionInv
import WordRAM.Tactic

/-!
# End-to-end wired solver initialization with select region (`SelectInitWired`)

Proves `solverInitWiredSel_runs`: the single fixed deterministic Word-RAM procedure
`solverInitWiredSelBody` (`SelectInitWiredCore.lean`, ABI `[graph, gradient, lengths, L, P, V, root]`)
composes `solverInitWiredBody`, `G_d` extraction (`opCore 3` + `dgInitEmpty` + `dgCopyRefill`),
and `selectInitRegionBody` (`SelectInitBody.lean`) to establish:
* `(solverStateRepSel ... 4 2 Rcore K pot).rep root s0 (tokFull', sg) out.mem`,
* `SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tokFull'.1.1 out.mem`,
* both runtime select-region pointers `out.mem (solverSelectHeapAddr tokFull'.1.1.table d) = sb`
  and `out.mem (solverSelectBlocksAddr tokFull'.1.1.table d) = B.base`,
* `sg.owned = fun a => sb ≤ a ∧ a < B.endAddr` and `sg.reembPot = chainReembPot pot s0.chain`,
* `SolverSelectRegionInv` (the owned blocks layout with slot `slot` and precision `pLast`, the
  potential bound `SelectPhiBoundedAt` with `N = 2 m + 2` and `M_g = 2 ^ E`, and the gradient
  bound), where the potential bound comes from `selectPhiBoundedAt_of_phiFill` at each level,
* `Rsel.Respects (fun _ => False) root totalSpace mem scOut root (tokFull', sg) out.mem`, and
* the amortized cost bound paying `K * sg.reembPot ≤ K * s0.chain.totalRuntime`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

/-- Initial re-embedding potential bound at `Ordered.algorithm2_init` (`chainReembPot_init_le`). -/
theorem selectInitRegion_reembPot_le {cfg : Alg2Config} {pot : cfg.T.State → ℕ}
    (hpot : ToolReembPotFacts cfg.T pot) (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) (K : ℕ) :
    K * chainReembPot pot (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain ≤
      K * (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain.totalRuntime :=
  Nat.mul_le_mul_left K (chainReembPot_init_le hpot cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀ g₀)

set_option maxHeartbeats 1600000 in
/-- **End-to-end wired solver initialization with select region**:
`solverInitWiredSelBody` runs `solverInitWiredBody`, extracts `G_d` via `op 3` + `dgInitEmpty` +
`dgCopyRefill`, and runs `selectInitRegionBody`, establishing `solverStateRepSel.rep`,
`SolverLevelCapsInv`, both `solverSelectHeapAddr` and `solverSelectBlocksAddr`, `Rsel.Respects`,
and the amortized cost bound paying `K * sg.reembPot ≤ K * s0.chain.totalRuntime`. -/
theorem solverInitWiredSel_runs
    {w L P E m V psi k epsExp clog threshold initConcreteProc overwriteProc copyWords
      wiredInitProc dgEmptyProc dgCopyProc selInitProc pLastProc slotProc
      skelProc copyValProc intLoopProc fillIntProc fillLastProc finalizeProc
      coreLenProc filterProc embCopyProc phiLoopProc phiFillProc rebuildSuffixProc rebuildLvlProc
      depth capExp limbMul capLimit wordExp initSpace' initFixed initMul
      unit toolMul treeMul K pLast slot op3Space evalSpace evalCost pLastCost slotCost
      graph gradient lengths root pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {κ : ℝ} {G initialGraph : MGraph}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {pot : cfg.T.State → ℕ}
    {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool} {mem : ℕ → ℕ} {B_tree : ℤ}
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hpot : ToolReembPotFacts cfg.T pot)
    (hpWired : p.procs[wiredInitProc]? = some (solverInitWiredBody initConcreteProc overwriteProc copyWords))
    (hpSelInit : p.procs[selInitProc]? = some (selectInitRegionBody skelProc copyValProc intLoopProc fillLastProc finalizeProc))
    (hInitSpec : OrdInitConcreteSpecW w L P E m V psi k epsExp cfg Rcore G p initConcreteProc B_tree
      capExp limbMul capLimit wordExp initSpace' initFixed initMul)
    (hOverAt : p.procs[overwriteProc]? = some (initOverwriteIntThresholdsBody clog threshold))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hPLast : MeetsContract w p pLastProc (selectPLastContract w m pLast pLastCost))
    (hSlot : MeetsContract w p slotProc (selectSlotContract w m V L P slot slotCost))
    (hw14 : 14 ≤ w) (hLkW : L < 2 ^ w) (hSlotW : slot < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) (hmPos : 0 < m)
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hM₀Eq : cfg.P.M₀ = max m threshold) (hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀)
    (h4M3W : 4 * cfg.P.M₀ + 3 < 2 ^ w) (hd1W : cfg.P.d + 1 < 2 ^ w) (hεPos : 0 < cfg.ε)
    (hGE : G.E = Finset.range m) (hEndsLt : ∀ e ∈ G.E, G.tail e < G.n ∧ G.head e < G.n)
    (hGraph : IPM.Machine.GraphAt mem graph G)
    (hGraphBelow : graph + (IPM.Machine.graphWords G).length ≤ root)
    (hLenEnd : lengths + G.m * L ≤ root) (hGradEnd : gradient + G.m * L ≤ root)
    (hVecValid : ∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧
      0 < Num.intVal mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L)
    (hLenWithin : IPM.LengthsWithin G E (IPM.Machine.readVector mem lengths 4 L P m))
    (hGradWithin : ∀ e ∈ G.E, |IPM.Machine.readVector mem gradient 4 L P m e| ≤ (2 : ℝ) ^ E)
    (hPW : P < 2 ^ w) (hVW : V < 2 ^ w)
    (hWordLvl : ∀ i < cfg.P.d,
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.lvlM i + cfg.N₀ + 2) ^ wordExp *
        (L + 1) < 2 ^ w)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)))
    (hvalBAll : ∀ e < m,
      let v := initialPathEdgeValue P cfg.ε
        (Num.intVal mem (gradient + e * L) 4 L) ((Num.intVal mem (lengths + e * L) 4 L).toNat)
      |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree)
    (hmod : SelectModelInv
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)) G σ σ_mwu γ_ℓ γ_c)
    (hReach : OrdSolverReached cfg κ G
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)))
    (hNumInit : ∀ tok : SolverToken cfg L Rcore,
      PathTreeNumericInv tok.tree tok.trees B_tree 0 →
      SolverTreeNumericInv P
        (Chain.Ordered.algorithm2_init cfg G
          (IPM.Machine.readVector mem gradient 4 L P m)
          (IPM.Machine.readVector mem lengths 4 L P m)) tok)
    (hLastBr :
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.lastBran <
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.lastK)
    (hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.G j).V, v < G.n)
    (hEcap : ∀ j ≤ cfg.P.d, ∀ e ∈
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.G j).E, e < initTargetCap cfg G)
    (hFV : ∀ j ≤ cfg.P.d, ∀ v ∈
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.toTreeChain.activeLSF j).F.F.V, v < G.n)
    (hFE : ∀ j ≤ cfg.P.d, ∀ e ∈
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.toTreeChain.activeLSF j).F.F.E,
      e < initTargetCap cfg G)
    (hLenFitInt :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ j < cfg.P.d, ∀ e ∈ (s0.chain.G j).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ P = s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e)
    (hLenFitLast :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ e ∈ (s0.chain.G cfg.P.d).E,
        (∃ q0 : ℤ, Num.Fits 4 L (q0 * (2 : ℤ) ^ pLast) ∧
          (q0 : ℝ) / (2 : ℝ) ^ P = s0.chain.toTreeChain.chainLen s0.chain.ℓ cfg.P.d e) ∧
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
            s0.chain.toTreeChain.chainLen s0.chain.ℓ (cfg.P.d + 1) e)
    (hEmbSlot :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ j < cfg.P.d, ∀ e ∈ (s0.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (s0.chain.toTreeChain.activeEmb j e)).length ≤ slot)
    (hGn : G.n ≤ 2 * m + 2)
    (hFitPhi :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
        (∀ r < j, SelectPotInvAt s0.chain.toTreeChain s0.chain.g φ' r) →
        (∀ r < j, SelectPhiBoundedAt s0.chain.toTreeChain φ' (2 * m + 2) ((2 : ℝ) ^ E) r) →
        (∀ e ∈ (s0.chain.toTreeChain.activeLSF j).F.F.E,
          PotGradEvalFits 4 L P s0.chain.toTreeChain s0.chain.g φ' j e) ∧
        ForestWalkFits 4 L P (s0.chain.toTreeChain.activeLSF j).F.F
          (potGrad s0.chain.toTreeChain s0.chain.g φ' j))
    (hDgEmpty : MeetsContract w p dgEmptyProc (dgInitEmptyContract w))
    (hSkel : ∀ sb lvlMeta hbCell, MeetsContract w p skelProc
      (selectRegionSkeletonContract w P sb (selectHeapCap cfg G m) cfg.P.d G.n
        (initTargetCap cfg G) L slot lvlMeta pLast hbCell))
    (hCopyVal : ∀ eL : List ℕ, MeetsContract w p copyValProc (selCopyValuesContractSrc w G.m (initTargetCap cfg G) eL))
    (hpIntLoop : p.procs[intLoopProc]? = some (selectInitInteriorLoopBody intLoopProc fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc))
    (hpFillLast : p.procs[fillLastProc]? = some (selectFillLastLevelBody dgCopyProc coreLenProc))
    (hpFinalize : p.procs[finalizeProc]? = some (selectInitFinalizeBody phiLoopProc rebuildSuffixProc))
    (hFootAt :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ j < cfg.P.d,
        SparseCoreReadoutFootAt fmt L depth cfg.T initialGraph cfg.P.k
          (s0.chain.lvlM j) s0.chain.N₀ G.n (initTargetCap cfg G) capExp Psc allocation Rcore p op)
    (hOp3Sp : 1 ≤ op3Space)
    (hDgCopy : ∀ G_new : MGraph, ∀ vcS ecS,
      MeetsContract w p dgCopyProc
        (dgCopyRefillContract w G.n (initTargetCap cfg G) vcS ecS dgEmptyGraph G_new))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P (initTargetCap cfg G) eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ j < cfg.P.d, ∀ eL : List ℕ,
        MeetsContract w p embCopyProc (selEmbCopyContract w eL (s0.chain.toTreeChain.activeEmb j)))
    (hpPhiLoop : p.procs[phiLoopProc]? = some (selectPhiLoopBody phiLoopProc phiFillProc))
    (hPhiFill :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ (mloc : SelectLevelMetaLoc) (φ : ℕ → ℕ → ℝ),
        MeetsContract w p phiFillProc
          (selectPhiFillContract w 4 P mloc s0.chain.toTreeChain G s0.chain.g s0.chain.ℓ
            σ σ_mwu γ_ℓ γ_c φ))
    (hpRebSuf : p.procs[rebuildSuffixProc]? = some (selectRebuildSuffixBody rebuildSuffixProc rebuildLvlProc))
    (hRebLvl :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      ∀ (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc) (φ : ℕ → ℕ → ℝ),
        mloc.pLast = pLast → mloc.Lk = L →
        MeetsContract w p rebuildLvlProc
          (selectRebuildLevelContract w 4 P loc mloc s0.chain.toTreeChain s0.chain.g
            s0.chain.ℓ φ (fun j => s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1))
            evalSpace evalCost))
    (hz : ZeroFrom mem root)
    (hroom :
      let s0 := Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)
      root + (initSpace' + initWiredExtraSpace cfg G +
        solverInitWiredSelSpace s0.chain G.n (initTargetCap cfg G) (selectHeapCap cfg G m)
          L capExp slot op3Space evalSpace) < 2 ^ w) :
    let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
    let len₀ := IPM.Machine.readVector mem lengths 4 L P m
    let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
    let cap := selectHeapCap cfg G m
    let Rfull := solverStateRepFull cfg κ G L P m V psi k epsExp (detectOffTreeDrainUnit L)
      unit toolMul treeMul Rcore
    let Rsel := solverStateRepSel cfg κ G L P m V psi k epsExp (detectOffTreeDrainUnit L)
      unit toolMul treeMul 4 2 Rcore K pot
    let totalSpace := initSpace' + initWiredExtraSpace cfg G +
      solverInitWiredSelSpace s0.chain G.n (initTargetCap cfg G) cap L capExp slot op3Space evalSpace
    ∃ (scOut cost sb : ℕ) (out : State) (tokFull' : Rfull.τ) (sg : SelectGhost),
      let metaBase := sb + selectHeapSize cap cfg.P.d L
      let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize cfg.P.d, cfg.P.d, G.n, initTargetCap cfg G, L, slot⟩
      Runs w p ω (solverInitWiredSelBody wiredInitProc (op 3) dgEmptyProc dgCopyProc selInitProc pLastProc slotProc)
        (startState [graph, gradient, lengths, L, P, V, root] mem pos)
        (.returned scOut) out cost ∧
      MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P s0 ∧
      Rsel.rep root s0 (tokFull', sg) out.mem ∧
      SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tokFull'.1.1 out.mem ∧
      SolverLevelLayoutAt G.n (initTargetCap cfg G) tokFull'.1.1 out.mem ∧
      out.mem (solverSelectHeapAddr tokFull'.1.1.table cfg.P.d) = sb ∧
      out.mem (solverSelectBlocksAddr tokFull'.1.1.table cfg.P.d) = B.base ∧
      sg.owned = (fun a => sb ≤ a ∧ a < B.endAddr) ∧
      sg.reembPot = chainReembPot pot s0.chain ∧
      SolverSelectRegionInv G L P m E pLast slot G.n (initTargetCap cfg G) s0
        (Rfull.foot root tokFull') tokFull'.1.1 sg out.mem ∧
      Rsel.Respects (fun _ => False) root totalSpace mem scOut root (tokFull', sg) out.mem ∧
      cost + Rsel.phi root (tokFull', sg) out.mem ≤
        initFixed + initWiredExtraCost cfg G +
          solverInitWiredSelCost s0.chain Psc.readout cap L capExp slot evalCost pLastCost slotCost +
          unit * ((cfg.P.d + 1) * Nat.floor ((10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1))) +
          toolMul * runtimeCredit cfg s0 + treeMul * treeCredit cfg s0 +
          (initMul + K) * s0.chain.totalRuntime := by
  intro grad₀ len₀ s0 cap Rfull Rsel totalSpace
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hw10 : 10 ≤ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hdPos : 0 < cfg.P.d := cfg.P.hd
  have hd0 : cfg.P.d ≠ 0 := ne_of_gt hdPos
  have hjLt : cfg.P.d - 1 < cfg.P.d := by omega
  have hGm : G.m = m := by unfold MGraph.m; rw [hGE, Finset.card_range]
  have hCapEq : cap = 2 * initTargetCap cfg G := selectHeapCap_eq_two_mul_initTargetCap cfg G m hGm
  have hroom' : root + (initSpace' + initWiredExtraSpace cfg G +
      solverInitWiredSelSpace s0.chain G.n (initTargetCap cfg G) cap L capExp slot op3Space evalSpace) <
      2 ^ w := hroom
  -- Step 1: Run `solverInitWiredBody`
  obtain ⟨cur0, cWired, st0, tok0, hrWired, hfits, hrep0, hcaps0, hlay0, hrecap0, hintCap0, _, _,
      hnum0, _, _, hcur0Lo, hcur0Hi, hz0, hFr0Below, hFoot0, hcWired⟩ :=
    ordSolverInitWired_runs (pos := pos) (ω := ω) hInitSpec hOverAt hCopy hclog hlocalCore hw14 hmPos hM₀Eq hN₀Eq h4M3W
      hd1W hεPos hGE hEndsLt (by omega) hWordLvl hCapFacts
      hGraph hGraphBelow hLenEnd hGradEnd hVecValid hLenWithin hGradWithin hz
      ⟨σ, σ_mwu, γ_ℓ, γ_c, hmod.1⟩ hvalBAll
  have hlPos0 : ∀ e ∈ G.E, 0 < len₀ e := fun e he => lt_of_lt_of_le (by positivity) (hLenWithin e he).1
  obtain ⟨hrepS0, hphiS0Le⟩ := solverStateRepFull_phi_init_le (κ := κ) (G := G)
    (unit := unit) (toolMul := toolMul) (treeMul := treeMul) hrep0
  let tokFull0 : Rfull.τ := ((tok0, 0), (runtimeCredit cfg s0, treeCredit cfg s0))
  have hrepFull0 : Rfull.rep root s0 tokFull0 st0.mem :=
    ⟨hrepS0, ⟨⟨ordSolverReachBase_init cfg G grad₀ len₀ hlPos0, hNumInit tok0 hnum0⟩,
      hReach, hReach.nextFresh_le hV hmG hnG, hintCap0⟩, rfl, rfl⟩
  have hFoot0Lt : ∀ a, Rfull.foot root tokFull0 a → a < cur0 := fun a ha => (hFoot0 a ha).2
  have hFoot0Ge : ∀ a, Rfull.foot root tokFull0 a → root ≤ a := fun a ha => (hFoot0 a ha).1
  have hMeta0 := init_meta_hyps_of_caps hrepFull0 hFoot0Lt hcaps0
  obtain ⟨hRootDir0, _, _, hChainHdr0, _, _, _, _, _, _, _, _, _, _, hCores0, _, _, hTermRep0, hWire0, htags0⟩ := hrep0
  obtain ⟨hOwn0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, t19_0, t20_0, _⟩ := htags0
  have hRootDG : DynGraphAt st0.mem tok0.rootGraph G.n (initTargetCap cfg G) G := by
    have h1 : DynGraphAt st0.mem tok0.rootGraph s0.extG.n tok0.rootECap (s0.chain.G 0) := hWire0.2.1
    have hG0 : s0.chain.G 0 = G := hmod.1.1
    have hEn : s0.extG.n = G.n := by simp [s0, Chain.Ordered.algorithm2_init]
    rw [hrecap0, hG0, hEn] at h1
    exact h1
  -- Step 2: `pLastProc` and `slotProc`
  obtain ⟨bPL, hbPL, oPL, stPL, cPL, hrPL, ⟨hMemPL, hRetPL⟩, hcPL⟩ :=
    hPLast [m] st0.mem st0.pos ω (by simp; omega) ⟨rfl, hpLastW⟩
  obtain ⟨bSl, hbSl, oSl, stSl, cSl, hrSl, ⟨hMemSl, hRetSl⟩, hcSl⟩ :=
    hSlot [m, V, L, P] stPL.mem stPL.pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl) <;> omega)
      ⟨rfl, hSlotW⟩
  have hMemSl0 : stSl.mem = st0.mem := hMemSl.trans hMemPL
  -- Step 3: `op 3` on core `d - 1` + `dgInitEmpty` + `dgCopyRefill`
  have hRoom3 : cur0 + op3Space + dynGraphSize G.n (initTargetCap cfg G) + 3 * (s0.chain.G cfg.P.d).m < 2 ^ w := by
    dsimp only [solverInitWiredSelSpace] at hroom'; omega
  obtain ⟨b3, o3, st1, c3, bE, oE, st2, cE, bC, oC, st3, cC, tokFull1,
      hb3, hr3, hbE, hrE, hbC, hrC, hcur1Lo, hcur1Hi, hoCEq, hrep1Full, htab1, hhnd1, _, htt1, _, _, _, _, _,
      hcaps1, hGd3, hFr30, hft1, hz3, hcBr⟩ :=
    op3_copy_gd_runs (pos := stSl.pos) hlocalCore hw16 hkW hdPos hrepFull0 hFoot0Lt hcaps0 hmod
      (hmod.2.2.2.1 (cfg.P.d - 1) hjLt) (hmod.2.2.1 (cfg.P.d - 1) hjLt)
      (hVcap cfg.P.d (le_refl _)) (hEcap cfg.P.d (le_refl _))
      (hFootAt (cfg.P.d - 1) hjLt) hOp3Sp hDgEmpty (hDgCopy (s0.chain.G cfg.P.d) G.n (initTargetCap cfg G))
      hz0 hRoom3
  set srcGd := o3.value
  set sb := oC.value
  have hFoot1Lt : ∀ a, Rfull.foot root tokFull1 a → a < srcGd := fun a ha => by
    rcases hft1 a ha with h0 | hnew
    · exact lt_of_lt_of_le (hFoot0Lt a h0) hcur1Lo
    · exact hnew.2
  have hFoot1Ge : ∀ a, Rfull.foot root tokFull1 a → root ≤ a := fun a ha => by
    rcases hft1 a ha with h0 | hnew
    · exact hFoot0Ge a h0
    · omega
  have hFoot1Sb : ∀ a, Rfull.foot root tokFull1 a → a < sb := fun a ha =>
    lt_of_lt_of_le (hFoot1Lt a ha) (by omega)
  have hMeta1 := init_meta_hyps_of_caps hrep1Full hFoot1Sb hcaps1
  have hOwn1 : ∀ a, tokFull1.1.1.tag a ≠ 0 → tokFull1.1.1.owned a :=
    hrep1Full.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFr3Root : ∀ a < root, st3.mem a = mem a := fun a ha => by
    have hnc : ¬ Rcore.foot (tok0.coreHandle (cfg.P.d - 1)) (tok0.coreTok (cfg.P.d - 1)) a :=
      fun hc => by have := hFoot0Ge a (Or.inr (Or.inr ⟨cfg.P.d - 1, hjLt, hc⟩)); omega
    exact (hFr30 a (by omega) hnc).trans (hFr0Below a ha)
  have hG0E : (s0.chain.G 0).E = G.E := congrArg MGraph.E hmod.1.1
  have hGrad3 : EdgeValuesAt st3.mem gradient 4 L P (s0.chain.G 0).E s0.chain.g := by
    have hg0Eq : ∀ e ∈ G.E, s0.chain.g e = grad₀ e := fun e _ => by
      simp [s0, Chain.Ordered.algorithm2_init, Chain.Ordered.algorithm1_initialize]
    intro e he
    have heG : e ∈ G.E := hG0E ▸ he
    have hem : e < m := Finset.mem_range.mp (hGE ▸ heG)
    have hAg : ∀ t < L, st3.mem (gradient + e * L + t) = mem (gradient + e * L + t) := fun t ht => by
      have hmul : e * L + L ≤ G.m * L := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (by omega)
      exact hFr3Root _ (by omega)
    refine ⟨fun t ht => by rw [hAg t ht]; exact (hVecValid e hem).2.2 t ht, ?_⟩
    unfold Num.fixVal; rw [Num.intVal_congr hAg, hg0Eq e heG]
    simp [grad₀, IPM.Machine.readVector, hem, Num.fixVal]
  have hTermBelow1 : tokFull1.1.1.termTok ≤ sb := by
    have hTermLt : tok0.termHandle < tok0.termTok := by have := hTermRep0.1; omega
    have hOwnT : tok0.owned (tok0.termTok - 1) :=
      hOwn0 (tok0.termTok - 1) (by
        have htg := t19_0 (tok0.termTok - 1) ⟨by omega, by omega⟩
        omega)
    have hlt := hFoot0Lt _ (Or.inl hOwnT)
    dsimp only [tokFull0] at htt1
    rw [htt1]; omega
  -- The level potentials stay bounded by `3 ^ j (2 m + 2) 2 ^ E` (`selectPhiBoundedAt_of_phiFill`)
  have hgBd : ∀ e ∈ (s0.chain.G 0).E, |s0.chain.g e| ≤ (2 : ℝ) ^ E := fun e he => by
    have heG : e ∈ G.E := hG0E ▸ he
    have hg0Eq : s0.chain.g e = grad₀ e := by
      simp [s0, Chain.Ordered.algorithm2_init, Chain.Ordered.algorithm1_initialize]
    rw [hg0Eq]; exact hGradWithin e heG
  have hN0 : (s0.chain.toTreeChain.G 0).n ≤ 2 * m + 2 := by
    have hG0 : s0.chain.G 0 = G := hmod.1.1
    change (s0.chain.G 0).n ≤ 2 * m + 2
    rw [hG0]; exact hGn
  have hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ r < j, SelectPotInvAt s0.chain.toTreeChain s0.chain.g φ r) →
      (∀ r < j, SelectPhiBoundedAt s0.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) r) →
      (∀ v ∈ (s0.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (s0.chain.toTreeChain.activeLSF j).F.F.V,
          (s0.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad s0.chain.toTreeChain s0.chain.g φ j)
            ((s0.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ r < j + 1, SelectPhiBoundedAt s0.chain.toTreeChain (Function.update φ j φj)
        (2 * m + 2) ((2 : ℝ) ^ E) r := by
    intro j hj φ φj hpot hbd hfill r hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
    · exact selectPhiBoundedAt_update_ne φj (by omega) (hbd r hlt)
    · exact selectPhiBoundedAt_of_phiFill (by positivity) hmod.1 hj hN0 hgBd hpot hbd hfill
  -- Step 4: Call `selectInitRegionBody`
  let metaBase := sb + selectHeapSize cap cfg.P.d L
  let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize cfg.P.d, cfg.P.d, G.n, initTargetCap cfg G, L, slot⟩
  have hBEndEq : B.endAddr = sb + selectHeapSize cap cfg.P.d L + selectLevelMetaSize cfg.P.d +
      (⟨0, cfg.P.d, G.n, initTargetCap cfg G, L, slot⟩ : SelectBlocksLoc).endAddr :=
    blocks_endAddr_eq_base_add _ _ _ _ _ _
  have hRoomSel : B.endAddr + selectInitRegionScratch s0.chain cap L capExp evalSpace < 2 ^ w := by
    rw [hBEndEq]; dsimp only [solverInitWiredSelSpace] at hroom'; omega
  obtain ⟨scOut, cSel, stSel, tokFull', sg, hrSel, hscLo, hscHi, hrepSel, hsgOwn, hsgReemb, _, _, _,
      hCapsSel, hhbOut, hblkOut, hBlkSel, hBdSel, hzSel, hFrSelBelow, hFootSel, hcSel⟩ :=
    selectInitRegion_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := detectOffTreeDrainUnit L) (unit := unit)
      (toolMul := toolMul) (treeMul := treeMul) (dMul := 4) (kOff := 2) (K := K)
      (depth := depth) (capExp := capExp) (vCap := G.n) (eCap := initTargetCap cfg G)
      (sb := sb) (pLast := pLast) (slot := slot) (g0Src := gradient) (g0SrcCap := G.m)
      (srcGd := srcGd) (srcVCap := G.n) (srcECap := initTargetCap cfg G) (l0Ptr := lengths)
      (evalSpace := evalSpace) (evalCost := evalCost) (pos := st3.pos)
      (skelProc := skelProc) (copyValProc := copyValProc) (intLoopProc := intLoopProc)
      (fillIntProc := fillIntProc) (fillLastProc := fillLastProc) (finalizeProc := finalizeProc)
      (dgCopyProc := dgCopyProc) (coreLenProc := coreLenProc) (filterProc := filterProc)
      (embCopyProc := embCopyProc) (phiLoopProc := phiLoopProc) (phiFillProc := phiFillProc)
      (rebuildSuffixProc := rebuildSuffixProc) (rebuildLvlProc := rebuildLvlProc)
      (fmt := fmt) (cfg := cfg) (κ := κ) (G := G) (G₀ := G) (initialGraph := initialGraph)
      (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c) (Psc := Psc) (allocation := allocation)
      (Rcore := Rcore) (pot := pot) (p := p) (op := op) (ω := ω) (root := root) (model := s0)
      (tokFull := tokFull1) (mem := st3.mem)
      hfmt4 hfmtP hlocalCore hw16 hw10 hLkW hSlotW hpLastW hkW hrep1Full hFoot1Sb
      hMeta1.1 hMeta1.2.1 hMeta1.2.2.1 hMeta1.2.2.2.1 hMeta1.2.2.2.2 hcaps1 hmod
      hGrad3 (fun e he => by
        have heG : e ∈ G.E := hG0E ▸ he
        rw [hGm]; exact Finset.mem_range.mp (hGE ▸ heG))
      (by omega) (fun a ha => Or.inr (by
        have hGe : root ≤ a := hFoot1Ge a (Or.inl (hOwn1 a
          (by rcases ha with rfl | rfl
              · exact hMeta1.1.tag_ne_zero
              · rw [show tokFull1.1.1.table + 4 * cfg.P.d + 2 + 1 =
                  solverSelectBlocksAddr tokFull1.1.1.table cfg.P.d by rw [solverSelectBlocksAddr_eq],
                  hcaps1.1.1.2.2.2]; omega)))
        omega))
      hGd3 (by omega)
      (fun a ha => Or.inl (by
        have hLt : a < srcGd := hFoot1Lt a (Or.inl (hOwn1 a
          (by rcases ha with rfl | rfl
              · exact hMeta1.1.tag_ne_zero
              · rw [show tokFull1.1.1.table + 4 * cfg.P.d + 2 + 1 =
                  solverSelectBlocksAddr tokFull1.1.1.table cfg.P.d by rw [solverSelectBlocksAddr_eq],
                  hcaps1.1.1.2.2.2]; omega)))
        omega))
      (fun j hj a ha1 _ hc => by have := hFoot1Lt a (Or.inr (Or.inr ⟨j, hj, hc⟩)); omega)
      (fun h => absurd h hd0)
      (fun j hj => hmod.2.2.2.1 j hj) (fun j hj => hmod.2.2.1 j hj) hLastBr hTermBelow1
      hVcap hEcap hFV hFE hLenFitInt hLenFitLast hEmbSlot
      (fun j hj e he => by
        have h1 := hEcap j hj e he
        change e < cap / 2
        rw [hCapEq]
        omega)
      (PhiBd := fun φ r => SelectPhiBoundedAt s0.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) r)
      hPhiBdStep hFitPhi
      (hSkel sb (solverLevelMetaAddr tokFull1.1.1.table cfg.P.d) (tokFull1.1.1.table + 4 * cfg.P.d + 2))
      hCopyVal hpIntLoop hpFillInt hpFillLast hpFinalize hFootAt hDgCopy hCoreLen hFilter
      hEmbCopy hpPhiLoop
      (fun φ => hPhiFill _ φ) hpRebSuf (fun φ => hRebLvl _ _ φ rfl rfl) hz3 hRoomSel
  -- Step 5: Stitch into `solverInitWiredSelBody`
  let sInit := startState [graph, gradient, lengths, L, P, V, root] mem pos
  have hCoreHnd := (hCores0 (cfg.P.d - 1) hjLt).1
  have hCoreBr : st0.mem (tok0.handle + 18 + (cfg.P.d + 1) + (cfg.P.d - 1)) = s0.chain.bran (cfg.P.d - 1) :=
    (hCores0 (cfg.P.d - 1) hjLt).2.1
  have hDgSz : dynGraphSize G.n (initTargetCap cfg G) = 4 + 7 * G.n + 9 * initTargetCap cfg G := rfl
  have hHb0Lt : tok0.table + 4 * cfg.P.d + 2 + 2 ≤ cur0 := hMeta0.2.2.1
  have hHnd0Lt : tok0.handle + 18 + 2 * (cfg.P.d + 1) ≤ cur0 := hMeta0.2.2.2.2.1
  have hCur0W : cur0 < 2 ^ w := by dsimp only [solverInitWiredSelSpace] at hroom'; omega
  have hRootGraph1Lt : tok0.rootGraph + 1 < cur0 :=
    hFoot0Lt _ (Or.inl (hOwn0 _ (by
      have := t20_0 (tok0.rootGraph + 1) (by omega) (by unfold dynGraphSize; omega)
      omega)))
  have hRD0 : st0.mem root = tok0.handle := by simpa using hRootDir0 0 (by simp)
  have hRD1 : st0.mem (root + 1) = tok0.table := by simpa using hRootDir0 1 (by simp)
  have hRD14 : st0.mem (root + 14) = tok0.rootGraph := by simpa using hRootDir0 14 (by simp)
  have hCH0 : st0.mem (tok0.handle + 9) = m := by simpa using hChainHdr0 0 (by simp)
  have hCH2 : st0.mem (tok0.handle + 11) = cfg.P.d := by simpa using hChainHdr0 2 (by simp)
  have hRootVCap : st0.mem tok0.rootGraph = G.n := by simpa [dgVCapOff] using hRootDG.2.2.2.1
  have hRootECap : st0.mem (tok0.rootGraph + 1) = initTargetCap cfg G := by
    simpa [dgECapOff] using hRootDG.2.2.2.2.1
  have hMainRun : ∃ o out cTot,
      Runs w p ω (solverInitWiredSelBody wiredInitProc (op 3) dgEmptyProc dgCopyProc selInitProc pLastProc slotProc)
        sInit o out cTot ∧ o = .returned scOut ∧ out.mem = stSel.mem ∧
      cTot ≤ cWired + cPL + cSl + c3 + cE + cC + cSel + 240 := by
    unfold solverInitWiredSelBody
    refine runs_seq_call_ex2 (vs := [graph, gradient, lengths, L, P, V, root])
      (by simp [evalArgs, Expr.eval, sInit, startState]) hpWired hrWired <|
      runs_seq_assign_ex2 (v := tok0.handle) (by simp [Expr.eval, sInit, startState, hRD0]) <|
      runs_seq_assign_ex2 (v := tok0.table) (by simp [Expr.eval, BinOp.eval, sInit, startState, hw1,
        show root + 1 < 2 ^ w by omega, hRD1]) <|
      runs_seq_assign_ex2 (v := tok0.rootGraph) (by simp [Expr.eval, BinOp.eval, sInit, startState,
        show 14 < 2 ^ w by omega, show root + 14 < 2 ^ w by omega, hRD14]) <|
      runs_seq_assign_ex2 (v := m) (by simp [Expr.eval, BinOp.eval, sInit, startState,
        show 9 < 2 ^ w by omega, show tok0.handle + 9 < 2 ^ w by omega, hCH0]) <|
      runs_seq_assign_ex2 (v := cfg.P.d) (by simp [Expr.eval, BinOp.eval, sInit, startState,
        show 11 < 2 ^ w by omega, show tok0.handle + 11 < 2 ^ w by omega, hCH2]) <|
      runs_seq_assign_ex2 (v := G.n) (by simp [Expr.eval, sInit, startState, hRootVCap]) <|
      runs_seq_assign_ex2 (v := initTargetCap cfg G) (by simp [Expr.eval, BinOp.eval, sInit, startState, hw1,
        show tok0.rootGraph + 1 < 2 ^ w by omega, hRootECap]) <|
      runs_seq_assign_ex2 (v := cap) (by simp [Expr.eval, BinOp.eval, sInit, startState, hCapEq,
        show 2 < 2 ^ w by omega, show 2 * initTargetCap cfg G < 2 ^ w by omega]) <|
      runs_seq_assign_ex2 (v := tok0.handle + 18) (by simp [Expr.eval, BinOp.eval, sInit, startState,
        show 18 < 2 ^ w by omega, show tok0.handle + 18 < 2 ^ w by omega]) <|
      runs_seq_assign_ex2 (v := solverLevelMetaAddr tok0.table cfg.P.d) (by
        simp [Expr.eval, BinOp.eval, sInit, startState, solverLevelMetaAddr_eq, show 2 < 2 ^ w by omega,
          show 2 * cfg.P.d < 2 ^ w by omega, show tok0.table + 2 * cfg.P.d < 2 ^ w by omega,
          show tok0.table + 2 * cfg.P.d + 2 < 2 ^ w by omega]) <|
      runs_seq_assign_ex2 (v := tok0.table + 4 * cfg.P.d + 2) (by
        simp [Expr.eval, BinOp.eval, sInit, startState, show 2 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
          show 4 * cfg.P.d < 2 ^ w by omega, show tok0.table + 4 * cfg.P.d < 2 ^ w by omega,
          show tok0.table + 4 * cfg.P.d + 2 < 2 ^ w by omega]) <|
      runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, sInit, startState]) hbPL hrPL <|
      runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, sInit, startState]) hbSl hrSl ?_
    have hRest : ∀ {stCur : State},
        stCur.mem = stSl.mem → stCur.pos = stSl.pos →
        stCur.regs 1 = gradient → stCur.regs 2 = lengths → stCur.regs 3 = L →
        stCur.regs 7 = cur0 → stCur.regs 12 = cfg.P.d → stCur.regs 13 = G.n →
        stCur.regs 14 = initTargetCap cfg G → stCur.regs 15 = cap →
        stCur.regs 16 = tok0.handle + 18 →
        stCur.regs 17 = solverLevelMetaAddr tok0.table cfg.P.d →
        stCur.regs 18 = tok0.table + 4 * cfg.P.d + 2 →
        stCur.regs 19 = pLast → stCur.regs 20 = slot →
        ∃ o out cR,
          Runs w p ω
            (.cond (.reg 12)
              (.assign 21 (.load (.bin .add (.reg 16) (.bin .sub (.reg 12) (.const 1)))) ;;
               .assign 22 (.load (.bin .add (.bin .add (.reg 16) (.bin .add (.reg 12) (.const 1)))
                 (.bin .sub (.reg 12) (.const 1)))) ;;
               .call 23 (op 3) [.reg 21, .reg 22, .reg 7] ;;
               .assign 24 (.load (.reg 7)) ;;
               .call 25 dgEmptyProc [.reg 23, .reg 13, .reg 14] ;;
               .assign 26 (.bin .add (.bin .add (.bin .add (.reg 23) (.const 4)) (.bin .mul (.const 7) (.reg 13)))
                 (.bin .mul (.const 9) (.reg 14))) ;;
               .call 27 dgCopyProc [.reg 23, .reg 24, .reg 26] ;;
               .assign 28 (.reg 23) ;; .assign 29 (.reg 27))
              (.assign 28 (.reg 10) ;; .assign 29 (.reg 7)) ;;
             .call 30 selInitProc
               [.reg 29, .reg 15, .reg 12, .reg 13, .reg 14, .reg 3, .reg 20, .reg 16, .reg 17,
                .reg 19, .reg 18, .reg 1, .reg 28, .reg 2] ;;
             .ret (.reg 30))
            stCur o out cR ∧
          o = .returned scOut ∧ out.mem = stSel.mem ∧
          cR ≤ c3 + cE + cC + cSel + 120 := by
      intro stCur hM hP hr1 hr2 hr3r hr7 hr12 hr13 hr14 hr15 hr16 hr17 hr18 hr19 hr20
      have hT : ∃ o outT cT,
          Runs w p ω
            (.assign 21 (.load (.bin .add (.reg 16) (.bin .sub (.reg 12) (.const 1)))) ;;
             .assign 22 (.load (.bin .add (.bin .add (.reg 16) (.bin .add (.reg 12) (.const 1)))
               (.bin .sub (.reg 12) (.const 1)))) ;;
             .call 23 (op 3) [.reg 21, .reg 22, .reg 7] ;;
             .assign 24 (.load (.reg 7)) ;;
             .call 25 dgEmptyProc [.reg 23, .reg 13, .reg 14] ;;
             .assign 26 (.bin .add (.bin .add (.bin .add (.reg 23) (.const 4)) (.bin .mul (.const 7) (.reg 13)))
               (.bin .mul (.const 9) (.reg 14))) ;;
             .call 27 dgCopyProc [.reg 23, .reg 24, .reg 26] ;;
             .assign 28 (.reg 23) ;; .assign 29 (.reg 27))
            stCur o outT cT ∧ o = .normal ∧
          outT.mem = st3.mem ∧ outT.pos = st3.pos ∧
          evalArgs w outT [.reg 29, .reg 15, .reg 12, .reg 13, .reg 14, .reg 3, .reg 20, .reg 16, .reg 17,
            .reg 19, .reg 18, .reg 1, .reg 28, .reg 2] =
            some [sb, cap, cfg.P.d, G.n, initTargetCap cfg G, L, slot, tokFull1.1.1.handle + 18,
              solverLevelMetaAddr tokFull1.1.1.table cfg.P.d, pLast,
              tokFull1.1.1.table + 4 * cfg.P.d + 2, gradient, srcGd, lengths] ∧
          cT ≤ c3 + cE + cC + 90 :=
        runs_seq_assign_ex2 (v := tok0.coreHandle (cfg.P.d - 1))
          (by simp [Expr.eval, BinOp.eval, hM, hMemSl0, hr12, hr16, hw1, show cfg.P.d - 1 < 2 ^ w by omega,
            show tok0.handle + 18 + (cfg.P.d - 1) < 2 ^ w by omega, hCoreHnd]) <|
        runs_seq_assign_ex2 (v := s0.chain.bran (cfg.P.d - 1))
          (by simp [Expr.eval, BinOp.eval, hM, hMemSl0, hr12, hr16, hw1, show cfg.P.d + 1 < 2 ^ w by omega,
            show cfg.P.d - 1 < 2 ^ w by omega, show tok0.handle + 18 + (cfg.P.d + 1) < 2 ^ w by omega,
            show tok0.handle + 18 + (cfg.P.d + 1) + (cfg.P.d - 1) < 2 ^ w by omega, hCoreBr]) <|
        runs_seq_call_ex2 (vs := [tok0.coreHandle (cfg.P.d - 1), s0.chain.bran (cfg.P.d - 1), cur0])
          (by simp [evalArgs, Expr.eval, hr7]) hb3
          (by rw [hM, hP, hMemSl0]; exact hr3) <|
        runs_seq_assign_ex2 (v := st1.mem cur0) (by simp [Expr.eval, hr7]) <|
        runs_seq_call_ex2 (vs := [o3.value, G.n, initTargetCap cfg G])
          (by simp [evalArgs, Expr.eval, hr13, hr14]) hbE hrE <|
        runs_seq_assign_ex2 (v := srcGd + dynGraphSize G.n (initTargetCap cfg G))
          (by simp [Expr.eval, BinOp.eval, hr13, hr14, srcGd, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
            show 9 < 2 ^ w by omega, show o3.value + 4 < 2 ^ w by omega, show 7 * G.n < 2 ^ w by omega,
            show 9 * initTargetCap cfg G < 2 ^ w by omega, show o3.value + 4 + 7 * G.n < 2 ^ w by omega,
            show o3.value + 4 + 7 * G.n + 9 * initTargetCap cfg G = o3.value + dynGraphSize G.n (initTargetCap cfg G) by omega,
            show o3.value + dynGraphSize G.n (initTargetCap cfg G) < 2 ^ w by omega]) <|
        runs_seq_call_ex2 (vs := [o3.value, st1.mem cur0, o3.value + dynGraphSize G.n (initTargetCap cfg G)])
          (by simp [evalArgs, Expr.eval, srcGd]) hbC hrC <|
        runs_seq_assign_ex2 (v := srcGd) (by simp [Expr.eval, srcGd])
          (⟨.normal, _, 2, runs_assign_iff.mpr ⟨sb, by simp [Expr.eval, sb], rfl, rfl, by simp [Expr.size]⟩,
            rfl, rfl, rfl,
            by simp [evalArgs, Expr.eval, hr1, hr2, hr3r, hr12, hr13, hr14, hr15, hr16, hr17, hr18,
              hr19, hr20, htab1, hhnd1, tokFull0, sb, srcGd],
            by simp only [Expr.size, argsSize]; omega⟩)
      obtain ⟨_, outT, cT, hrT, rfl, hmemT, hposT, hargsT, hcT⟩ := hT
      have hrCallSel : Runs w p ω
          (.call 30 selInitProc [.reg 29, .reg 15, .reg 12, .reg 13, .reg 14, .reg 3, .reg 20, .reg 16, .reg 17,
            .reg 19, .reg 18, .reg 1, .reg 28, .reg 2]) outT .normal
          ⟨stSel.mem, Function.update outT.regs 30 scOut, stSel.pos⟩ (14 + cSel + 1) :=
        runs_call_iff.mpr ⟨_, _, .returned scOut, stSel, cSel, hargsT, hpSelInit,
          by rw [hmemT, hposT]; exact hrSel, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hrRet : Runs w p ω (.ret (.reg 30))
          ⟨stSel.mem, Function.update outT.regs 30 scOut, stSel.pos⟩ (.returned scOut) _ 2 :=
        runs_ret_iff.mpr ⟨scOut, by simp [Expr.eval], rfl, rfl, rfl⟩
      exact ⟨.returned scOut, _, _,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨cfg.P.d, cT, by simp [Expr.eval, hr12],
            by simp only [hd0, ↓reduceIte]; exact hrT, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrCallSel, hrRet, rfl⟩), rfl⟩),
        rfl, rfl, by simp only [Expr.size]; omega⟩
    have hMono : ∀ {s : Stmt} {st : State} {f : ℕ → ℕ} {B1 B2 : ℕ},
        (∀ c, c ≤ B1 → f c ≤ B2) →
        (∃ o out c, Runs w p ω s st o out c ∧ o = .returned scOut ∧ out.mem = stSel.mem ∧ c ≤ B1) →
        ∃ o out c, Runs w p ω s st o out c ∧ o = .returned scOut ∧ out.mem = stSel.mem ∧ f c ≤ B2 :=
      fun hf ⟨o, out, c, hr, ho, hm, hc⟩ => ⟨o, out, c, hr, ho, hm, hf c hc⟩
    refine hMono (B1 := c3 + cE + cC + cSel + 120) (fun c hc => by simp [Expr.size, argsSize]; omega) ?_
    exact hRest rfl rfl
      (by simp [sInit, startState]) (by simp [sInit, startState]) (by simp [sInit, startState])
      (by simp [Outcome.value]) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [hRetPL]) (by simp [hRetSl])
  obtain ⟨_, out, cTot, hrMain, rfl, hmemEq, hcTot⟩ := hMainRun
  -- Frame below `root`: `selectInitRegionBody` preserves all `< sb` outside `Rfull.foot`, and `root ≤ a` for `Rfull.foot`
  have hReembLe := selectInitRegion_reembPot_le hpot G grad₀ len₀ K
  have hSbLeSc : sb ≤ scOut := by
    have h1 : B.endAddr ≤ scOut := hscLo
    rw [hBEndEq] at h1; omega
  have hscHi' : scOut ≤ root + totalSpace := by
    have h1 : scOut ≤ B.endAddr + selectInitRegionScratch s0.chain cap L capExp evalSpace := hscHi
    rw [hBEndEq] at h1
    dsimp only [sb] at h1
    change scOut ≤ root + (initSpace' + initWiredExtraSpace cfg G +
      solverInitWiredSelSpace s0.chain G.n (initTargetCap cfg G) cap L capExp slot op3Space evalSpace)
    dsimp only [solverInitWiredSelSpace]
    omega
  have hResp : Rsel.Respects (fun _ => False) root totalSpace mem scOut root (tokFull', sg) out.mem := by
    refine ⟨by omega, hscHi', hmemEq ▸ hzSel, fun a ha _ => ?_, fun a ha => ?_⟩
    · rw [hmemEq]
      have hGeHb : root ≤ tokFull1.1.1.table + 4 * cfg.P.d + 2 :=
        hFoot1Ge _ (LevelMetaFoot.mem_foot hrep1Full.1.1 hMeta1.1)
      have hFrSel : stSel.mem a = st3.mem a :=
        hFrSelBelow a (by omega) (by omega) (by omega)
          (fun ⟨j, hj, hc⟩ => by have := hFoot1Ge a (Or.inr (Or.inr ⟨j, hj, hc⟩)); omega)
      exact hFrSel.trans (hFr3Root a ha)
    · rcases hFootSel a ha with h1 | h2
      · exact Or.inr ⟨hFoot1Ge a h1, lt_of_lt_of_le (hFoot1Sb a h1) hSbLeSc⟩
      · exact Or.inr ⟨by omega, h2.2⟩
  have hLayEnd : SolverLevelLayoutAt G.n (initTargetCap cfg G) tokFull'.1.1 out.mem := by
    have hEqCell : ∀ a, tok0.tag a ≠ 0 → tok0.tag a = 1 ∨ tok0.tag a = 22 + cfg.P.d →
        tokFull1.1.1.tag a = tok0.tag a → out.mem a = st0.mem a := by
      intro a hnz htg hteq
      have hFr3 : st3.mem a = st0.mem a :=
        hFr30 a (hFoot0Lt a (Or.inl (hOwn0 a hnz))) fun hc => by
          have h := solverStateRep_core_tag (tok := tok0) hrepFull0.1.1 hjLt hc
          rcases htg with h1 | h2 <;> omega
      have hne : ∀ b, b = tokFull1.1.1.table + 4 * cfg.P.d + 2 ∨
          b = tokFull1.1.1.table + 4 * cfg.P.d + 3 → a ≠ b := fun b hb hab => by
        rcases htg with h1 | h2
        · exact (hMeta1.2.1 b hb).1 1 (by decide) (by omega) (hab ▸ hteq.trans h1)
        · exact (hMeta1.2.1 b hb).2.1 (hab ▸ hteq.trans h2)
      rw [hmemEq, ← hFr3]
      exact hFrSelBelow a (hFoot1Sb a (Or.inl (hOwn1 a (by omega))))
        (hne _ (Or.inl rfl)) (hne _ (Or.inr (by omega))) fun ⟨j, hj, hc⟩ => by
          have h := solverStateRep_core_tag hrep1Full.1.1 hj hc
          rcases htg with h1 | h2 <;> omega
    have hTabEnd : tokFull'.1.1.table = tok0.table := by
      have h1 : stSel.mem (root + 1) = tokFull'.1.1.table := by simpa using hrepSel.1.1.1.1 1 (by simp)
      have h0 : st0.mem (root + 1) = tok0.table := by simpa using hrepFull0.1.1.1 1 (by simp)
      have ht0 : tok0.tag (root + 1) = 1 := hrepFull0.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1 (by omega)
      have ht1 : tokFull1.1.1.tag (root + 1) = 1 := hrep1Full.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1 (by omega)
      rw [← h1, ← hmemEq, hEqCell (root + 1) (by omega) (Or.inl ht0) (ht1.trans ht0.symm), h0]
    have hRGEnd : tokFull'.1.1.rootGraph = tok0.rootGraph := by
      have h1 : stSel.mem (root + 14) = tokFull'.1.1.rootGraph := by simpa using hrepSel.1.1.1.1 14 (by simp)
      have h0 : st0.mem (root + 14) = tok0.rootGraph := by simpa using hrepFull0.1.1.1 14 (by simp)
      have ht0 : tok0.tag (root + 14) = 1 := hrepFull0.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14 (by omega)
      have ht1 : tokFull1.1.1.tag (root + 14) = 1 := hrep1Full.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14 (by omega)
      rw [← h1, ← hmemEq, hEqCell (root + 14) (by omega) (Or.inl ht0) (ht1.trans ht0.symm), h0]
    refine SolverLevelLayoutAt.of_agree hlay0 cfg.P.hd hTabEnd hRGEnd fun k hk => ?_
    have ht0 : tok0.tag (solverLevelMetaAddr tok0.table cfg.P.d + k) = 22 + cfg.P.d := hcaps0.1.2.2.2.2.1 k hk
    have ht1 : tokFull1.1.1.tag (solverLevelMetaAddr tok0.table cfg.P.d + k) = 22 + cfg.P.d := by
      rw [← htab1]; exact hcaps1.1.2.2.2.2.1 k hk
    exact hEqCell _ (by omega) (Or.inr ht0) (ht1.trans ht0.symm)
  refine ⟨scOut, cTot, sb, out, tokFull', sg, hrMain, hfits, hmemEq ▸ hrepSel, hmemEq ▸ hCapsSel,
    hLayEnd,
    by rw [solverSelectHeapAddr_eq]; exact hmemEq ▸ hhbOut,
    by rw [solverSelectBlocksAddr_eq]; exact hmemEq ▸ hblkOut,
    hsgOwn, hsgReemb, ?_, hResp, ?_⟩
  · rw [hmemEq]
    exact ⟨⟨B, rfl, hBlkSel (by rw [solverSelectHeapAddr_eq]; exact hhbOut)
      (by rw [solverSelectBlocksAddr_eq]; exact hblkOut)⟩, hBdSel, hgBd⟩
  rw [hmemEq]
  change cPL ≤ pLastCost at hcPL
  change cSl ≤ slotCost at hcSl
  have hPhi0Le : Rfull.phi root tokFull0 st0.mem ≤
      (solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore).phi root tok0 st0.mem +
        unit * ((cfg.P.d + 1) * Nat.floor ((10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1))) +
        toolMul * runtimeCredit cfg s0 + treeMul * treeCredit cfg s0 := hphiS0Le
  have hcBr' : c3 + cE + cC + Rfull.phi root tokFull1 st3.mem ≤
      Psc.readout + 40 + dgCopyRefillCost 0 0 (s0.chain.G cfg.P.d).n (s0.chain.G cfg.P.d).m +
        Rfull.phi root tokFull0 st0.mem := hcBr
  have hMulSplit : (initMul + K) * s0.chain.totalRuntime =
      initMul * s0.chain.totalRuntime + K * s0.chain.totalRuntime := Nat.add_mul _ _ _
  have hcSel' : cSel + Rsel.phi root (tokFull', sg) stSel.mem ≤
      selectInitRegionCost s0.chain Psc.readout cap L capExp slot evalCost +
        Rfull.phi root tokFull1 st3.mem + K * chainReembPot pot s0.chain := hcSel
  have hReembLe' : K * chainReembPot pot s0.chain ≤ K * s0.chain.totalRuntime := hReembLe
  have hcWired' : cWired + (solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore).phi root tok0 st0.mem ≤
      initFixed + initWiredExtraCost cfg G + initMul * s0.chain.totalRuntime := hcWired
  dsimp only [solverInitWiredSelCost]
  rw [hMulSplit]
  omega

end MinCostFlow.MinRatio
