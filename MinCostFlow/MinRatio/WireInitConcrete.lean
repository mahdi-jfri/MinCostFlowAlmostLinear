module

public import MinCostFlow.MinRatio.WireInitConcreteCore
public import MinCostFlow.MinRatio.WireInitSpec
public import MinCostFlow.LinkCut.PathProg.Implements
import MinCostFlow.MinRatio.OrdSolverToolMono
import MinCostFlow.MinRatio.OrdSolverImplementsFull
import MinCostFlow.Chain.Ordered.InitPreserves

/-!
# Concrete ordered initializer meets `OrdInitConcreteSpecW` (`WireInitConcrete`)

Bridges `initConcreteBody_runs` (`WireInitConcreteCore`) directly into `OrdInitConcreteSpecW`
(`WireInitSpec`), discharging all chain invariants (`TreeChain.Holds`, `SparseCoreOrdInput`,
per-level graph validity/size/rotation-order bounds, and `ordRotWords`) from
`cfg.ValidOrdNoHidden` + `Chain.Ordered.initialize_preserves_noHidden` + `rebuildSuffix_spec_noHidden`,
and discharging all four `initialPathEdgeValue` bounds and `Num.Fits 4 L (±th)` from
`IPM.LengthsWithin G E len₀` and `∀ e ∈ G.E, |grad₀ e| ≤ (2 : ℝ) ^ E`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LastLevelProgram
open MinCostFlow.Bundle

/-- Derive `TreeChain.Holds`, `SparseCoreOrdInput`, and all structural per-level model bounds
at `Chain.Ordered.algorithm1_initialize` from `cfg.ValidOrdNoHidden` and `IPM.LengthsWithin`. -/
private theorem initModelStructural_of_validOrdNoHidden
    {cfg : Alg2Config} {G : MGraph} {len₀ grad₀ : ℕ → ℝ} {E : ℕ}
    (hV : cfg.ValidOrdNoHidden) (hEq : ToolInitOrdEqOnE cfg.T)
    (hGV : G.IsValid) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hEΨ : (E : ℝ) ≤ cfg.Ψ)
    (hLenWithin : IPM.LengthsWithin G E len₀) :
    let lvlM := levelM cfg.TP cfg.P
    let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P lvlM cfg.N₀ G len₀ grad₀).1
    (∃ σ σ_mwu γ_ℓ γ_c, chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c) ∧
    (∀ i < cfg.P.d,
      SparseCoreOrdInput cfg.T cfg.P.k (lvlM i) cfg.N₀
        (chain.scState i) (chain.G i) (chain.levelOrd i) (chain.updCount i)) ∧
    (∀ i < cfg.P.d,
      (chain.G i).m ≤ lvlM i ∧ (chain.G i).n ≤ cfg.N₀ ∧
      (∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen len₀ i e) ∧
      IsRotationOrder (chain.G i) (chain.levelOrd i) ∧
      (chain.G (i + 1)).E ⊆ (chain.G i).E ∧
      (chain.G (i + 1)).m ≤ lvlM (i + 1) ∧
      ordRotWords (chainLevelOrdAbs chain i) 0 ≤ 1 + 2 * cfg.N₀ + 2 * lvlM (i + 1)) ∧
    (∀ e ∈ (chain.G cfg.P.d).E, 0 < chain.toTreeChain.chainLen len₀ cfg.P.d e) := by
  dsimp only
  set lvlM := levelM cfg.TP cfg.P
  set chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P lvlM cfg.N₀ G len₀ grad₀).1
  have hlPos : ∀ e ∈ G.E, 0 < len₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLenWithin e he).1
  have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G len₀ := by
    intro e he
    have hlog : |Real.log (len₀ e)| ≤ max 0 cfg.Ψ :=
      ((abs_log_le_of_two_pow_bounds (hLenWithin e he).1 (hLenWithin e he).2).trans hEΨ).trans
        (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk G len₀ grad₀ hGV hmG hnG hℓ
  rcases hInit with ⟨hInv, _, hG0, hℓ0, _, _, _, _, _, _⟩
  have hHolds := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  rw [hG0, hℓ0] at hHolds
  have hFacts := ordAlgorithm1_initialize_level_facts hEq cfg.L cfg.P lvlM cfg.N₀ G len₀ grad₀
  -- Replay `rebuildSuffix_spec_noHidden` and `rebuildSuffix_levelOrd_rotation`
  set dummySc := cfg.T.initOrd cfg.P.k (lvlM 0) cfg.N₀ G len₀ grad₀ (Bundle.sortedEnds G)
  have hℓ0' : Chain.Ordered.LevelLenRange cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ) 0 G
      ((Chain.mkPartialChain cfg.T cfg.P (fun _ => G) (fun _ => dummySc) (fun _ => 0) G).chainLen len₀ 0) :=
    hℓ.toLevel cfg.TP cfg.P cfg.N₀
  have hm0_real : (G.m : ℝ) ≤ (lvlM 0 : ℝ) := by
    exact_mod_cast le_trans hmG (Chain.M₀_le_levelM_zero hV.hTP cfg.P)
  have hOrd0 : ∃ ρ : Rotation G,
      ρ.order = Chain.Ordered.chainLevelOrd cfg.T (fun _ => G) (fun _ => dummySc) (fun _ => 0) 0 :=
    ⟨sortedRotation G, rfl⟩
  have hRS := Chain.Ordered.rebuildSuffix_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk len₀ grad₀ cfg.P.d 0
    (fun _ => G) (fun _ => dummySc) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (zero_add cfg.P.d) hGV (Finset.Subset.refl _) hnG hm0_real hℓ0' hOrd0
  have hOrdAll := Chain.Ordered.rebuildSuffix_levelOrd_rotation cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk len₀ grad₀ cfg.P.d 0
    (fun _ => G) (fun _ => dummySc) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (zero_add cfg.P.d) hGV (Finset.Subset.refl _) hnG hm0_real hℓ0' hOrd0
  rcases hRS with ⟨hG0eq, _, hSuf, hGdV, hGdSubV, hGdm, hGdℓ, _, _, _, _, _⟩
  set res := Chain.Ordered.rebuildSuffix cfg.T cfg.L cfg.P lvlM cfg.N₀ len₀ grad₀ cfg.P.d 0
    (fun _ => G) (fun _ => dummySc) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hLenCon : ∀ idx ≤ cfg.P.d,
      chain.toTreeChain.chainLen len₀ idx =
        (Chain.mkPartialChain cfg.T cfg.P res.1 res.2.1 res.2.2.1 (res.1 cfg.P.d)).chainLen len₀ idx := by
    intro idx hidx
    exact Chain.chainLen_congr_params rfl len₀ hidx (fun _ _ => rfl) (fun _ _ => rfl)
  have hGiBasic (i : ℕ) (hi : i < cfg.P.d) :
      (chain.G i).IsValid ∧ (chain.G i).m ≤ lvlM i ∧ (chain.G i).n ≤ cfg.N₀ ∧
      (∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen len₀ i e) ∧
      IsRotationOrder (chain.G i) (chain.levelOrd i) := by
    rcases hSuf i (Nat.zero_le _) hi with ⟨_, _, _, _, _, hGiV, hSubV, hGim, hGiℓ, _, _, _⟩
    have hGmNat : (chain.G i).m ≤ lvlM i := by exact_mod_cast hGim
    have hGnNat : (chain.G i).n ≤ cfg.N₀ := by
      refine le_trans (Finset.card_le_card ?_) hnG
      simpa [chain, Chain.Ordered.algorithm1_initialize, res, hG0eq 0 (le_refl 0)] using hSubV
    have hGiℓ' : ∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen len₀ i e := by
      rw [hLenCon i (Nat.le_of_lt hi)]; exact hGiℓ
    obtain ⟨ρ, hρ⟩ := hOrdAll i (Nat.zero_le _) hi
    exact ⟨hGiV, hGmNat, hGnNat, hGiℓ', ⟨ρ, hρ⟩⟩
  have hSuccBasic (i : ℕ) (hi : i < cfg.P.d) :
      (chain.G (i + 1)).IsValid ∧ (chain.G (i + 1)).m ≤ lvlM (i + 1) ∧
      (chain.G (i + 1)).n ≤ cfg.N₀ ∧ (chain.G (i + 1)).E ⊆ (chain.G i).E ∧
      IsRotationOrder (chain.G (i + 1)) (cfg.T.rot (chain.scState i) 0) := by
    have hSubE : (chain.G (i + 1)).E ⊆ (chain.G i).E := by
      obtain ⟨hbrLt, hLvl, _, hGeq⟩ := hHolds.2.2.2.2.1 i hi
      have hSp := (hLvl (chain.bran i) hbrLt).2.1.2.1
      have hC : (coreGraph (chain.G i) (chain.toTreeChain.lsfs i (chain.bran i))).E ⊆ (chain.G i).E :=
        Finset.sdiff_subset
      have hGeq' : chain.G (i + 1) = chain.toTreeChain.S i (chain.bran i) := hGeq
      rw [hGeq']; exact hSp.trans hC
    have hRotNext : IsRotationOrder (chain.G (i + 1)) (cfg.T.rot (chain.scState i) 0) := by
      by_cases hlt : i + 1 < cfg.P.d
      · have hrot := (hGiBasic (i + 1) hlt).2.2.2.2
        rwa [(hFacts.2.2.2.2 i hi).2.2.2.1] at hrot
      · rcases hSuf i (Nat.zero_le _) hi with ⟨_, _, _, _, _, hGiV, hSubV, hGim, hGiℓ, hsc_i, hGsucc, hOKi⟩
        let ℓi := (Chain.mkPartialChain cfg.T cfg.P res.1 res.2.1 res.2.2.1 (res.1 cfg.P.d)).chainLen len₀ i
        let gi := (Chain.mkPartialChain cfg.T cfg.P res.1 res.2.1 res.2.2.1 (res.1 cfg.P.d)).chainGrad grad₀ i
        let D0 : DynamicInstance := { G := fun _ => chain.G i, U := fun _ => [], ℓ := fun _ => ℓi, g := fun _ => gi }
        have hGin : (chain.G i).n ≤ cfg.N₀ := (hGiBasic i hi).2.2.1
        have hD0Ord : OrderedUpTo D0 0 2 (fun _ => chain.levelOrd i) :=
          Chain.Ordered.orderedUpTo_zero_of_rotation (hOrdAll i (Nat.zero_le _) hi)
        have hSpec0 := hOKi.noHidden cfg.P.k 0 (lvlM i) cfg.N₀ D0 (fun _ => chain.levelOrd i)
          (fun _ => []) cfg.P.hk hGiV (fun _ ht1 ht2 => by omega) (fun _ ht1 ht2 => by omega)
          (fun _ _ e he => hGiℓ e he) hD0Ord (by exact_mod_cast hGim) hGin
          (fun _ _ _ h => by cases h) (by simp only [Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.sum_empty, Nat.cast_zero]; exact Chain.updateThreshold_nonneg _ _ _)
          ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hOut := hSpec0.2.2.2.2.1 0 0 (le_refl 0) (le_refl 0) 0 cfg.P.hk (Or.inl rfl)
          (fun _ h1 h2 => by omega)
        have hRot := Chain.Ordered.rotation_of_orderedUpTo hOut (le_refl 0)
        refine Chain.Ordered.exists_rotation_of_eq ?_ ?_ hRot
        · simp only [SparseCoreRestartTool.coreInstanceOrdFrom,
            SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
            List.foldl_nil, D0]
          exact (congrArg (fun s => cfg.T.S s 0) hsc_i.symm).trans hGsucc.symm
        · simp only [SparseCoreRestartTool.runOrdAfterRestarts,
            SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil, D0]
          exact congrArg (fun s => cfg.T.rot s 0) hsc_i.symm
    by_cases hlt : i + 1 < cfg.P.d
    · obtain ⟨hV1, hm1, hn1, _, _⟩ := hGiBasic (i + 1) hlt
      exact ⟨hV1, hm1, hn1, hSubE, hRotNext⟩
    · have hieq : i + 1 = cfg.P.d := by omega
      rw [hieq]
      have hGdmNat : (chain.G cfg.P.d).m ≤ lvlM cfg.P.d := by exact_mod_cast hGdm
      have hGdnNat : (chain.G cfg.P.d).n ≤ cfg.N₀ := by
        refine le_trans (Finset.card_le_card ?_) hnG
        simpa [chain, Chain.Ordered.algorithm1_initialize, res, hG0eq 0 (le_refl 0)] using hGdSubV
      exact ⟨hGdV, hGdmNat, hGdnNat, hieq ▸ hSubE, hieq ▸ hRotNext⟩
  refine ⟨⟨_, _, _, _, hHolds⟩, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · obtain ⟨hGiV, hGim, hGin, hGiℓ, hGiRot⟩ := hGiBasic i hi
    obtain ⟨_, hUpd, _, _, hScEq⟩ := hFacts.2.2.2.2 i hi
    rw [hUpd, hScEq]
    exact SparseCoreOrdInput.init (chain.G i)
      (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen len₀ i e else 0)
      (fun e => if e ∈ (chain.G i).E then
        (if i = 0 then grad₀ e else chain.toTreeChain.chainLen len₀ i e) else 0)
      (chain.levelOrd i) hGiV hGim hGin
      (fun e he => by simpa [he] using hGiℓ e he) hGiRot
  · obtain ⟨_, hGim, hGin, hGiℓ, hGiRot⟩ := hGiBasic i hi
    obtain ⟨hV1, hm1, hn1, hSubE, hRot1⟩ := hSuccBasic i hi
    have hOrdW : ordRotWords (chainLevelOrdAbs chain i) 0 ≤ 1 + 2 * cfg.N₀ + 2 * lvlM (i + 1) := by
      unfold ordRotWords chainLevelOrdAbs
      dsimp only
      have hGeq : cfg.T.S (chain.scState i) 0 = chain.G (i + 1) := (hFacts.2.2.2.2 i hi).2.2.1.symm
      rw [hGeq]
      rw [ordWordsOn_eq_of_isRotationOrder hV1 hRot1]
      omega
    exact ⟨hGim, hGin, hGiℓ, hGiRot, hSubE, hm1, hOrdW⟩
  · rw [hLenCon cfg.P.d le_rfl]; exact hGdℓ

/-- Every value read from a fixed-point table lies on the `2 ^ (-P)` grid: an entry below `m` is
`Num.intVal / 2 ^ P`, and the entries at or above `m` are `0`. -/
theorem readVector_onGrid (mem : ℕ → ℕ) (a h L P m e : ℕ) :
    ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = IPM.Machine.readVector mem a h L P m e := by
  unfold IPM.Machine.readVector
  split_ifs
  · exact ⟨Num.intVal mem (a + e * L) h L, rfl⟩
  · exact ⟨0, by simp⟩

/-- **Main concrete initializer theorem (`OrdInitConcreteSpecW`)**: `initConcreteBody` satisfies
`OrdInitConcreteSpecW` against any `Rcore` that meets `sparseCoreOrdMachineContractKFBL` and
`SparseCoreReadoutFootAt` at every level of the initial chain, with the depth
`Expander.chosenL (cfg.P.M₀ ^ 2)` stored in the header and the caps `(G.n, m)` of the input graph,
with `lastLevelRuntimeMachineContract` + `LastLevelProgram.readoutBody`, and with the Section 6
path-tree program `LinkCut.PathProg.pathTreeBodies`. Of the old readout layout only the init space
bound `hInitSpaceLe` stays. -/
theorem initConcreteBody_meets_spec
    {w L P E m V psi k epsExp capExp limbMul capLimit
      initConcreteProc graphPack paramSetup sortedEnds coreInit coreLenProc edgeProc
      signExt mul intDiv lastInit treeBase bind shift divide negate copy
      lastMult stretchP lastSpace paramSpace paramCost : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {P_sc : SparseCoreOrdParams}
    {coreAlloc lastAlloc : ℕ → List ℕ → ℕ} {coreInitSpace : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {opCore opLast : ℕ → ℕ}
    {G : MGraph} {p : Program} {B_tree : ℤ}
    (hInitAt : p.procs[initConcreteProc]? = some
      (initConcreteBody graphPack paramSetup sortedEnds coreInit (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit (opLast 0) treeBase (treeBase + 1) bind shift divide negate copy))
    (hFour : fmt.limbBits = 4) (hPeq : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hEq : ToolInitOrdEqOnE cfg.T) (hLastEq : LastLevelBuildEqOnE cfg.L)
    (hlocalCore : Rcore.Local)
    (hV : cfg.ValidOrdNoHidden)
    (hGV : G.IsValid) (hGE : G.E = Finset.range m) (hVlt : ∀ v ∈ G.V, v < G.n)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀) (hcap0 : G.n + initRootECap cfg.N₀ cfg.P.k m + 2 ≤ capLimit)
    (hEΨ : (E : ℝ) ≤ cfg.Ψ)
    (hεEq : cfg.ε = ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P)
    (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ E)
    (hThrB : (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_tree)
    (hCapTree : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * B_tree < (Num.capacity 4 L : ℤ))
    (hdPos : 0 < cfg.P.d)
    (hw14 : 14 ≤ w) (hwk : cfg.P.k < 2 ^ w) (hN3w : cfg.N₀ + 3 < 2 ^ w)
    (hVW : V < 2 ^ w) (hPW : P < 2 ^ w)
    (hDW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w) (hsearchW : 20 * (4 * L + 8) + 100 < 2 ^ w)
    (hPdiv : 4 ∣ P) (hLpos : 0 < L) (hleEps : epsExp ≤ P) (hfitEps : P - epsExp + 1 < 4 * L)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidthN : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hMw : ∀ i < cfg.P.d, levelM cfg.TP cfg.P i < 2 ^ w)
    (hpack : MeetsContract w p graphPack
      (dgInitFromListsContract w G.n (initRootECap cfg.N₀ cfg.P.k m) G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hparam : MeetsContract w p paramSetup
      (initParamSetupContract w m V L P cfg.P.d cfg.P.k psi k epsExp cfg.N₀
        (Expander.chosenL (cfg.P.M₀ ^ 2)) (levelM cfg.TP cfg.P) paramSpace paramCost))
    (hsortAt : p.procs[sortedEnds]? = some buildSortedEndsBody)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hIntDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hTreeAt : p.HasAt treeBase (LinkCut.PathProg.pathTreeBodies 4 treeBase))
    (hCoreImpl : ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G E ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ i < cfg.P.d,
        Rcore.Implements w p coreInit opCore
          (sparseCoreOrdMachineContractKFBL fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T
            (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ G.n
            (initRootECap cfg.N₀ cfg.P.k m) capExp P_sc coreAlloc) ∧
        SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (chain.G i)
          cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initRootECap cfg.N₀ cfg.P.k m) capExp P_sc
          coreAlloc Rcore p opCore)
    (hLastImpl : ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G E ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ vc ec, vc + ec + 2 ≤ capLimit →
        (lastLevelRepresentation vc ec 4 L P (chain.G cfg.P.d).E).Implements w p lastInit opLast
          (lastLevelRuntimeMachineContract fmt L cfg.L (chain.G cfg.P.d) vc ec
            lastMult stretchP lastAlloc))
    (hLastReadout : p.procs[opLast 0]? = some LastLevelProgram.readoutBody)
    (hLastSpaceLe : ∀ args, lastAlloc 1 args ≤ lastSpace)
    (hInitSpaceLe : ∀ i < cfg.P.d, ∀ g l gr o h,
      coreAlloc 6 [g, l, gr, o, cfg.P.k, levelM cfg.TP cfg.P i, cfg.N₀, L, P,
        Expander.chosenL (cfg.P.M₀ ^ 2), h] ≤ coreInitSpace i)
    (hCoreLenFits : ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G E ℓ₀ →
      (∀ e ∈ G.E, ∃ q₀ : ℤ, (q₀ : ℝ) / (2 : ℝ) ^ P = ℓ₀ e) →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ i < cfg.P.d, ∀ e ∈ (chain.G (i + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
          chain.toTreeChain.chainLen ℓ₀ (i + 1) e)
    (hLastStretchFits : ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G E ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ e ∈ (chain.G cfg.P.d).E,
        2 * (2 : ℝ) ^ stretchP *
          lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
        Num.capacity 4 L) :
    OrdInitConcreteSpecW w L P E m V psi k epsExp cfg Rcore G p initConcreteProc B_tree
      capExp limbMul capLimit P_sc.wordExp
      (initConcreteSpace m G.n L cfg.P.d paramSpace capExp capLimit lastSpace
        (LinkCut.PathProg.arenaEnd 0 G.n L) (20 * LinkCut.PathProg.treeLimbs L + 100)
        coreInitSpace (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀)
      (initConcreteFixed m G.n L cfg.P.d paramCost capExp capLimit lastMult
        LinkCut.PathProg.pathC P_sc (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀)
      (max P_sc.mul lastMult) := by
  refine ⟨_, hInitAt, ?_⟩
  intro graph gradient lengths root pos ω mem
  dsimp only
  intro hroom hWord _hCapFacts hGraphAt hGraphBelow hLenBelow hGradBelow hVecValid hLenWithin hGradRange hz
  have hw17 : 17 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 17 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hGm : G.m = m := by unfold MGraph.m; rw [hGE, Finset.card_range]
  have hGmLeM0 : m ≤ levelM cfg.TP cfg.P 0 :=
    hGm ▸ le_trans hmG (Chain.M₀_le_levelM_zero hV.hTP cfg.P)
  have htreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p treeBase
      (fun i => treeBase + 1 + i)
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)) := by
    have h := LinkCut.PathProg.pathTree_implements (w := w) (b0 := treeBase) (p := p) fmt L
      (by omega) (by omega) (hFour.symm ▸ hTreeAt)
    rwa [hFour] at h
  obtain ⟨⟨σ, σ_mwu, γ_ℓ, γ_c, hH⟩, hCoreIn, hModelStruct, hGdPos⟩ :=
    initModelStructural_of_validOrdNoHidden hV hEq hGV hmG hnG hEΨ hLenWithin
  have hValFits := initialPathEdgeValue_bounds_of_ranges hGE hεPos hεLe hThrB hCapTree
    hVecValid hLenWithin hGradRange
  have hBnonneg : 0 ≤ B_tree := le_trans (by positivity) hThrB
  have hRes := initConcreteBody_runs
    (w := w) (graphPack := graphPack) (paramSetup := paramSetup) (sortedEnds := sortedEnds)
    (coreInit := coreInit) (coreLenProc := coreLenProc) (edgeProc := edgeProc)
    (signExt := signExt) (mul := mul) (intDiv := intDiv) (lastInit := lastInit)
    (treeInit := treeBase) (bind := bind) (shift := shift) (divide := divide)
    (negate := negate) (copy := copy)
    (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
    (capExp := capExp) (capLimit := capLimit) (lastMult := lastMult) (stretchP := stretchP)
    (lastSpace := lastSpace) (paramSpace := paramSpace) (paramCost := paramCost)
    (treeConst := LinkCut.PathProg.pathC)
    (treeInitSpace := LinkCut.PathProg.arenaEnd 0 G.n L)
    (linkSpace := 20 * LinkCut.PathProg.treeLimbs L + 100)
    (graph := graph) (gradient := gradient) (lengths := lengths) (root := root) (pos := pos)
    (fmt := fmt) (T := cfg.T) (lastTool := cfg.L) (C := cfg.P) (P_sc := P_sc)
    (coreAlloc := coreAlloc) (lastAlloc := lastAlloc)
    (treeAlloc := LinkCut.PathProg.pathAlloc L)
    (coreInitSpace := coreInitSpace) (lvlM := levelM cfg.TP cfg.P)
    (nextM := fun i => levelM cfg.TP cfg.P (i + 1)) (N₀ := cfg.N₀)
    (Rcore := Rcore) (Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC)
    (opCore := opCore) (opLast := opLast) (opTree := fun i => treeBase + 1 + i)
    (p := p) (ω := ω) (mem := mem) (G := G) (B_tree := B_tree)
    (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c)
    hFour hPeq hWidth hEq hLastEq hlocalCore hpack hparam hsortAt hCoreLenProc hEdgeProc
    hSign hMul hIntDiv hshift hdiv hneg hcopy hbind hLastReadout htreeImpl
    (hCoreImpl _ _ hLenWithin)
    (fun vc ec hcap => hLastImpl _ _ hLenWithin vc ec hcap)
    hLastSpaceLe hInitSpaceLe
    (fun _ => by unfold LinkCut.PathProg.pathAlloc; simp)
    (fun _ => by unfold LinkCut.PathProg.pathAlloc; simp)
    hGE hGV hVlt hnG hGmLeM0 hcap0 hGraphAt hGraphBelow hLenBelow hGradBelow hVecValid hz
    cfg.P.hk hdPos hwk hN3w hVW hPW hDW hsearchW hPdiv hLpos hleEps hfitEps hvw hwidthN hw17
    hMw hWord hH hCoreIn
    ⟨fun i hi =>
      let hms := hModelStruct i hi
      ⟨hms.1, hms.2.1, hms.2.2.1, hms.2.2.2.1, hms.2.2.2.2.1, hms.2.2.2.2.2.1,
       fun _ => le_rfl, hms.2.2.2.2.2.2,
       hCoreLenFits _ _ hLenWithin (fun e _ => readVector_onGrid mem lengths 4 L P m e) i hi⟩,
     hGdPos, hLastStretchFits _ _ hLenWithin⟩
    (hεEq ▸ hValFits) hBnonneg (by simpa using hCapTree) hroom
  simpa only [Chain.Ordered.algorithm2_init, hεEq, OrdInitChainCoresK, OrdInitChainCoresAt] using hRes

/-- Paper-shape asymptotic form of `initConcreteFixed`: linear in `m + n + d * (M_max + N₀ + capLimit)`
times polylogarithmic factors in `L`, `M_max + N₀`, and `n`, plus `paramCost + lastMult`. -/
theorem initConcreteFixed_le_shape
    {m n L d paramCost capExp capLimit lastMult treeConst M_max N₀ : ℕ}
    {P_sc : SparseCoreOrdParams} {lvlM nextM : ℕ → ℕ}
    (hd : 0 < d) (hM : ∀ i < d, lvlM i ≤ M_max) (hNext : ∀ i < d, nextM i ≤ M_max) :
    let LwMax := ordLevelLwMax L capExp M_max N₀
    let logN := Nat.log 2 (2 * n + 1) + 1
    let poly := P_sc.mul * SparseCore.bundleLogFactor M_max N₀ + P_sc.readout +
      treeConst * (L + 1) ^ 2 * logN + (LwMax + 1) ^ 2 + 1
    initConcreteFixed m n L d paramCost capExp capLimit lastMult treeConst P_sc lvlM nextM N₀ ≤
      paramCost + lastMult + 7500 * (m + n + d * (M_max + N₀ + capLimit + 1) + 1) * poly := by
  intro LwMax logN poly
  have hLogMono (M : ℕ) (hMle : M ≤ M_max) :
      SparseCore.bundleLogFactor M N₀ ≤ SparseCore.bundleLogFactor M_max N₀ := by
    unfold SparseCore.bundleLogFactor
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) 2
  have hLwMono (M : ℕ) (hMle : M ≤ M_max) :
      ordLevelLwMax L capExp M N₀ ≤ LwMax := by
    unfold ordLevelLwMax LwMax
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)) _
  have hLvlLe : ∀ i ∈ Finset.range d,
      ordLevelFixedCost L capExp capLimit P_sc (lvlM i) N₀ (nextM i) + 9 ≤
        4500 * (M_max + N₀ + capLimit + 1) * poly := by
    intro i hi
    have hi' : i < d := Finset.mem_range.mp hi
    have hMi : lvlM i ≤ M_max := hM i hi'
    have hNi : nextM i ≤ M_max := hNext i hi'
    have hB1 : 1 ≤ SparseCore.bundleLogFactor M_max N₀ := by
      unfold SparseCore.bundleLogFactor; exact Nat.one_le_pow 2 _ (by omega)
    have hBi := hLogMono (lvlM i) hMi
    have hLwi := hLwMono (lvlM i) hMi
    have hdg : dynGraphSize capLimit capLimit = 4 + 16 * capLimit := by unfold dynGraphSize; omega
    have hEdgeC : wireCoreLenEdgeCost (ordLevelLwMax L capExp (lvlM i) N₀) + 30 ≤
        4500 * (LwMax + 1) ^ 2 := by
      unfold wireCoreLenEdgeCost
      have hsq : ordLevelLwMax L capExp (lvlM i) N₀ ^ 2 ≤ (LwMax + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hlin : ordLevelLwMax L capExp (lvlM i) N₀ ≤ (LwMax + 1) ^ 2 :=
        le_trans (by omega) (Nat.le_self_pow (by decide : 2 ≠ 0) (LwMax + 1))
      have h1 : 1 ≤ (LwMax + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
      nlinarith
    have hMul1 : P_sc.mul * (N₀ + lvlM i + (2 * N₀ + 2 * lvlM i + 1) + 1) ≤
        3 * (M_max + N₀ + capLimit + 1) * (P_sc.mul * SparseCore.bundleLogFactor M_max N₀) := by
      have h1 : N₀ + lvlM i + (2 * N₀ + 2 * lvlM i + 1) + 1 ≤ 3 * (M_max + N₀ + capLimit + 1) := by omega
      calc P_sc.mul * (N₀ + lvlM i + (2 * N₀ + 2 * lvlM i + 1) + 1)
          ≤ P_sc.mul * (3 * (M_max + N₀ + capLimit + 1)) := Nat.mul_le_mul_left _ h1
        _ = 3 * (M_max + N₀ + capLimit + 1) * P_sc.mul := by ring
        _ ≤ 3 * (M_max + N₀ + capLimit + 1) * (P_sc.mul * SparseCore.bundleLogFactor M_max N₀) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have hMul2 : P_sc.mul * (2 * N₀ + 2 * nextM i + 2) * SparseCore.bundleLogFactor (lvlM i) N₀ ≤
        2 * (M_max + N₀ + capLimit + 1) * (P_sc.mul * SparseCore.bundleLogFactor M_max N₀) := by
      have h1 : 2 * N₀ + 2 * nextM i + 2 ≤ 2 * (M_max + N₀ + capLimit + 1) := by omega
      calc P_sc.mul * (2 * N₀ + 2 * nextM i + 2) * SparseCore.bundleLogFactor (lvlM i) N₀
          ≤ P_sc.mul * (2 * (M_max + N₀ + capLimit + 1)) * SparseCore.bundleLogFactor M_max N₀ :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) hBi
        _ = 2 * (M_max + N₀ + capLimit + 1) * (P_sc.mul * SparseCore.bundleLogFactor M_max N₀) := by ring
    have hNextC : nextM i * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (lvlM i) N₀) + 30) ≤
        4500 * M_max * (LwMax + 1) ^ 2 := by
      calc nextM i * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (lvlM i) N₀) + 30)
          ≤ M_max * (4500 * (LwMax + 1) ^ 2) := Nat.mul_le_mul hNi hEdgeC
        _ = 4500 * M_max * (LwMax + 1) ^ 2 := by ring
    unfold ordLevelFixedCost
    rw [hdg]
    have hpoly : P_sc.mul * SparseCore.bundleLogFactor M_max N₀ + P_sc.readout +
        (LwMax + 1) ^ 2 + 1 ≤ poly := by dsimp only [poly]; omega
    nlinarith
  have hSumLe :
      (∑ i ∈ Finset.range d, (ordLevelFixedCost L capExp capLimit P_sc (lvlM i) N₀ (nextM i) + 9)) ≤
        d * (4500 * (M_max + N₀ + capLimit + 1) * poly) := by
    calc (∑ i ∈ Finset.range d, (ordLevelFixedCost L capExp capLimit P_sc (lvlM i) N₀ (nextM i) + 9))
        ≤ ∑ _i ∈ Finset.range d, (4500 * (M_max + N₀ + capLimit + 1) * poly) := Finset.sum_le_sum hLvlLe
      _ = d * (4500 * (M_max + N₀ + capLimit + 1) * poly) := by simp
  have hLLeLw : L + 1 ≤ LwMax + 1 := by unfold LwMax ordLevelLwMax; omega
  have hLsq : (L + 1) ^ 2 ≤ (LwMax + 1) ^ 2 := Nat.pow_le_pow_left hLLeLw 2
  have hLlin : L ≤ (LwMax + 1) ^ 2 :=
    le_trans (by omega) (Nat.le_self_pow (by decide : 2 ≠ 0) (LwMax + 1))
  have hTreeLog : 1 ≤ logN := Nat.succ_pos _
  have hTreeInit : treeConst * (L + 1) ^ 2 * (n + 1) ≤ (n + 1) * poly := by
    have h1 : treeConst * (L + 1) ^ 2 ≤ treeConst * (L + 1) ^ 2 * logN :=
      Nat.le_mul_of_pos_right _ hTreeLog
    have h2 : treeConst * (L + 1) ^ 2 * logN ≤ poly := by dsimp only [poly]; omega
    calc treeConst * (L + 1) ^ 2 * (n + 1) = (n + 1) * (treeConst * (L + 1) ^ 2) := by ring
      _ ≤ (n + 1) * poly := Nat.mul_le_mul_left _ (h1.trans h2)
  have hPathB : pathTreeBudget treeConst L n ≤ 25 * poly := by
    unfold pathTreeBudget; dsimp only [poly, logN]; nlinarith
  unfold initConcreteFixed ordInitLevelsFixed initPostTailCost initLinkChainCost
  have hPolyGe1 : 1 ≤ poly := by dsimp only [poly]; omega
  have hReadLe : P_sc.readout ≤ poly := by dsimp only [poly]; omega
  have hLwSqLe : (LwMax + 1) ^ 2 ≤ poly := by dsimp only [poly]; omega
  have hL2Le : L ^ 2 ≤ poly := le_trans (Nat.pow_le_pow_left (by omega) 2) hLwSqLe
  have hLLe : L ≤ poly := hLlin.trans hLwSqLe
  have hLinkM : m * (pathTreeBudget treeConst L n + 96) ≤ m * (121 * poly) :=
    Nat.mul_le_mul_left m (by omega)
  have hDetectM : m * (2700 * L ^ 2 + 2920 * L + 869) ≤ m * (6489 * poly) :=
    Nat.mul_le_mul_left m (by nlinarith)
  have hLinkD : d * (2 * P_sc.readout + 80) ≤ 82 * (d * (M_max + N₀ + capLimit + 1)) * poly := by
    have h1 : d * (2 * P_sc.readout + 80) ≤ d * (82 * poly) := Nat.mul_le_mul_left d (by omega)
    have h2 : d ≤ d * (M_max + N₀ + capLimit + 1) := Nat.le_mul_of_pos_right d (by omega)
    have h3 : d * (82 * poly) ≤ (d * (M_max + N₀ + capLimit + 1)) * (82 * poly) :=
      Nat.mul_le_mul_right _ h2
    calc d * (2 * P_sc.readout + 80) ≤ (d * (M_max + N₀ + capLimit + 1)) * (82 * poly) := h1.trans h3
      _ = 82 * (d * (M_max + N₀ + capLimit + 1)) * poly := by ring
  have hMetaM : 30 * (m * L) ≤ m * (30 * poly) := by
    calc 30 * (m * L) = m * (30 * L) := by ring
      _ ≤ m * (30 * poly) := Nat.mul_le_mul_left m (Nat.mul_le_mul_left 30 hLLe)
  have hMetaD : 56 * d ≤ 56 * (d * (M_max + N₀ + capLimit + 1)) * poly := by
    have h1 : d ≤ d * (M_max + N₀ + capLimit + 1) := Nat.le_mul_of_pos_right d (by omega)
    have h2 : d * (M_max + N₀ + capLimit + 1) ≤ (d * (M_max + N₀ + capLimit + 1)) * poly :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h3 : 56 * d ≤ 56 * ((d * (M_max + N₀ + capLimit + 1)) * poly) :=
      Nat.mul_le_mul_left 56 (h1.trans h2)
    simpa [Nat.mul_assoc] using h3
  have hClogLe : Nat.clog 2 (N₀ + 2) ≤ N₀ + 2 :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
  have hCapN0 : 150 * capLimit + 22 * Nat.clog 2 (N₀ + 2) ≤
      172 * (d * (M_max + N₀ + capLimit + 1) + 1) * poly := by
    have h1 : 150 * capLimit + 22 * Nat.clog 2 (N₀ + 2) ≤ 172 * (d * (M_max + N₀ + capLimit + 1) + 1) := by
      have hd1 : 1 * (M_max + N₀ + capLimit + 1) ≤ d * (M_max + N₀ + capLimit + 1) :=
        Nat.mul_le_mul_right _ hd
      omega
    have h2 : d * (M_max + N₀ + capLimit + 1) + 1 ≤
        (d * (M_max + N₀ + capLimit + 1) + 1) * poly :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h3 : 172 * (d * (M_max + N₀ + capLimit + 1) + 1) ≤
        172 * ((d * (M_max + N₀ + capLimit + 1) + 1) * poly) :=
      Nat.mul_le_mul_left 172 h2
    exact h1.trans (by simpa [Nat.mul_assoc] using h3)
  have hNPoly : n ≤ n * poly := Nat.le_mul_of_pos_right n hPolyGe1
  have hMPoly : m ≤ m * poly := Nat.le_mul_of_pos_right m hPolyGe1
  clear hM hNext hLwMono hLvlLe hLLeLw hLsq hLlin hTreeLog hPathB hReadLe hLwSqLe hL2Le hClogLe
  linarith [hSumLe, hTreeInit, hLinkM, hDetectM, hLinkD, hMetaM, hMetaD, hCapN0, hNPoly, hMPoly, hLLe, hPolyGe1]

end MinCostFlow.MinRatio
