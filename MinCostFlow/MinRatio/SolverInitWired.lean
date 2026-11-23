module

public import MinCostFlow.MinRatio.SolverInitWiredGrow
public import MinCostFlow.MinRatio.WireInitSpec
public import MinCostFlow.MinRatio.SolverLevelLayout
import MinCostFlow.LSF.Walks

/-!
# Wired ordered Algorithm 2 initialization (`SolverInitStepSpec`)

Runs `solverInitWiredBody` (`MinRatio/SolverInitWiredBase.lean`): the ordered concrete
initializer (`OrdInitConcreteSpec`) followed by `initOverwriteIntThresholdsBody`, which
overwrites `table[0..d]` with the exact integer rebuild thresholds. It builds the initial
`SolverToken` with the region tags `initSolverTag`, proves `solverStateRep.rep` (including
`SolverWireInv` and `SolverEdgeOrientInv`), `PathTreeNumericInv`, `OffTreeRecInv`, and
`MinRatioStateFits` (`ordSolverInitWired_runs`), and discharges `SolverInitStepSpec`
(`solverInitStepSpec_of_wired`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program IPM.Machine SparseCore.Program

/-- Given `InitPathTreeInv`, produce the witness `(ts, fs, ds)` together with
`SolverEdgeAccountsAt`, `TreeEditNamedSlots`, `SolverEdgeOrientInv`, and `OffTreeRecInv`. -/
private theorem init_accounts_orient_offTree {cfg : Alg2Config} {L P m : ℕ}
    {Rtree : DSRep PathTreeState} {treeHeap slots names slotThresholds edgeThresholds
      edgeRecords inOffReady finalHeap : ℕ}
    {G : MGraph} {sFin : PathTreeState} {yTree : Rtree.τ} {slotFin nameFin thPtr recPtr : ℕ → ℕ}
    {lenInt : ℕ → ℕ} {gradInt : ℕ → ℤ} {B_tree : ℤ} {mem : ℕ → ℕ}
    {g₀ ℓ₀ : ℕ → ℝ} {model : Alg2State cfg}
    (hExtG : model.extG = G) (hExtToInt : model.extToInt = id) (hIntToExt : model.intToExt = id)
    (hExtg : model.extg = g₀) (hExtℓ : model.extℓ = ℓ₀)
    (hFlow0 : model.flow = fun _ => 0) (hDet0 : model.detectAccum = fun _ => 0)
    (hGE : G.E = Finset.range m)
    (hSubT : model.chain.toTreeChain.chainTree.E ⊆ G.E)
    (hεPos : 0 < cfg.ε)
    (hlenPos : ∀ e < m, 0 < lenInt e ∧ ((lenInt e : ℝ) / (2 : ℝ) ^ P) = ℓ₀ e)
    (hgradEq : ∀ e < m, ((gradInt e : ℝ) / (2 : ℝ) ^ P) = g₀ e)
    (hdetB : ∀ e < m,
      |(initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)).detector| ≤ B_tree)
    (_hinOff0 : ∀ e < m, mem (inOffReady + e) = 0)
    (hedges : ∀ e < m,
      mem (edgeThresholds + e) = thPtr e ∧
      mem (edgeRecords + e) = recPtr e ∧
      PathIntAt mem (thPtr e) 4 L (detectorThreshold P cfg.ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
      PathEdgeAt mem (recPtr e) 4 L (some (initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e))))
    (hrecDisj : ∀ e₁ < m, ∀ e₂ < m, e₁ ≠ e₂ →
      recPtr e₁ + (2 + 4 * L) ≤ recPtr e₂ ∨ recPtr e₂ + (2 + 4 * L) ≤ recPtr e₁)
    (hinv : InitPathTreeInv Rtree treeHeap G model.chain.toTreeChain.chainTree
      (fun e => initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)) B_tree
      slots names slotThresholds m thPtr model.chain.toTreeChain.chainTree.E
      sFin yTree slotFin nameFin finalHeap mem) :
    ∃ ts fs ds,
      LctInvWith pathPayload sFin ts fs ds ∧
      PathTreeNumericInv sFin ts B_tree 0 ∧
      SolverEdgeAccountsAt model L P mem slots names slotThresholds
        edgeThresholds edgeRecords inOffReady m sFin ts ∧
      TreeEditNamedSlots sFin ts model.chain.toTreeChain.chainTree
        (fun ei => mem (slots + ei)) (fun slot => mem (names + slot)) ∧
      SolverEdgeOrientInv L P model mem slots edgeRecords sFin ts ∧
      OffTreeRecInv model L mem edgeRecords B_tree := by
  obtain ⟨hsn, _, _, _, ⟨hslotsAt, hnamesAt⟩, ⟨ts, fs, ds, hLct, hNum, hNamed0, hLive0⟩,
      hstAt, hoff0⟩ := hinv
  let F := model.chain.toTreeChain.chainTree
  have hNamed : TreeEditNamedSlots sFin ts F slotFin nameFin := hNamed0
  have hLive : TreeEditLiveAccounts sFin ts F slotFin
      (fun e => initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)) := hLive0
  have hnd : (ts.flatMap AuxTree.toList).Nodup := hLct.activeNodup
  have hslotMem (e : ℕ) (he : e < m) : mem (slots + e) = slotFin e := hslotsAt e he
  have hnameMem (k : ℕ) (hk : k < 2 * G.n) : mem (names + k) = nameFin k := hnamesAt k hk
  refine ⟨ts, fs, ds, hLct, hNum, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun e he => ?_, fun slot val hslot hpair => ?_⟩
    · have hem : e < m := by rw [hExtG, hGE] at he; exact Finset.mem_range.mp he
      have hptr := hedges e hem
      have hℓEq := (hlenPos e hem).2
      have hℓPos : 0 < ℓ₀ e := by
        rw [← hℓEq]; exact div_pos (Nat.cast_pos.mpr (hlenPos e hem).1) (pow_pos zero_lt_two P)
      refine ⟨by rw [hExtToInt]; exact hem,
        by rw [hExtToInt, id_eq, hptr.1, hExtℓ, ← hℓEq]; exact hptr.2.2.1, ?_⟩
      dsimp only; rw [hExtToInt, id_eq]
      split_ifs with hin
      · have hfwd := hNamed.forward e hin
        have hsnz : slotFin e ≠ 0 := by unfold isEdgeSlot at hfwd; omega
        have hsLt : slotFin e < 2 * G.n := by unfold isEdgeSlot at hfwd; rw [← hsn]; exact hfwd.2.1.2
        rw [hslotMem e hem, hnameMem _ hsLt, hptr.1]
        refine ⟨hsnz, hfwd.2.1, hfwd.2.2, hstAt e hin, ?_⟩
        rcases hLive e hin with ⟨_, _, hp⟩ | ⟨_, _, hp⟩
        · refine ⟨initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e), 0, hp, ?_, ?_, ?_⟩
          · simp [PathEdgeValue.originalFlow, initialPathEdgeValue, hFlow0]
          · simp [hDet0]
          · simp [initialPathEdgeValue, hExtℓ, ← hℓEq]
        · refine ⟨(initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)).reverse, 0, hp, ?_, ?_, ?_⟩
          · simp [PathEdgeValue.originalFlow, PathEdgeValue.reverse, initialPathEdgeValue, hFlow0]
          · simp [hDet0]
          · simp [PathEdgeValue.reverse, initialPathEdgeValue, hExtℓ, ← hℓEq]
      · rw [hslotMem e hem, hptr.2.1]
        refine ⟨hoff0 e hem hin, initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e), 0,
          hptr.2.2.2, ?_, ?_, ?_, ?_⟩
        · simp [PathEdgeValue.originalFlow, initialPathEdgeValue, hFlow0]
        · simp [hDet0]
        · simp [initialPathEdgeValue, hExtℓ, ← hℓEq]
        · intro hnn
          have hpos := detectorThreshold_pos P cfg.ε (ℓ₀ e) hεPos hℓPos
          simp only [initialPathEdgeValue, hℓEq] at hnn; omega
    · have hslotMemTree : slot ∈ ts.flatMap AuxTree.toList :=
        (init_forestPairs_map_fst_perm sFin.splay ts).mem_iff.mp
          (List.mem_map.mpr ⟨(slot, some val), hpair, rfl⟩)
      have hsLt : slot < 2 * G.n := by unfold isEdgeSlot at hslot; rw [← hsn]; exact hslot.2
      obtain ⟨hmemF, hslotEq⟩ := hNamed.inverse slot hslotMemTree hslot
      have hem : nameFin slot < m := Finset.mem_range.mp (hGE ▸ hSubT hmemF)
      dsimp only
      rw [hnameMem slot hsLt, hIntToExt, id_eq, hslotMem _ hem, hExtG, hExtToInt, id_eq, hGE]
      exact ⟨hem, hmemF, hslotEq, Finset.mem_range.mpr hem, rfl⟩
  · refine ⟨fun ei hei => ?_, fun k hk hks => ?_, fun ei hei => ?_⟩
    · have hem : ei < m := Finset.mem_range.mp (hGE ▸ hSubT hei)
      have hfwd := hNamed.forward ei hei
      have hsLt : slotFin ei < 2 * G.n := by unfold isEdgeSlot at hfwd; rw [← hsn]; exact hfwd.2.1.2
      rw [hslotMem ei hem, hnameMem _ hsLt]; exact hfwd
    · have hkLt : k < 2 * G.n := by unfold isEdgeSlot at hks; rw [← hsn]; exact hks.2
      obtain ⟨hmemF, hslotEq⟩ := hNamed.inverse k hk hks
      have hem : nameFin k < m := Finset.mem_range.mp (hGE ▸ hSubT hmemF)
      rw [hnameMem k hkLt, hslotMem _ hem]; exact ⟨hmemF, hslotEq⟩
    · have hem : ei < m := Finset.mem_range.mp (hGE ▸ hSubT hei)
      rw [hslotMem ei hem]; exact hNamed.endpoints ei hei
  · intro e he
    have hem : e < m := by rw [hExtG, hGE] at he; exact Finset.mem_range.mp he
    dsimp only; rw [hExtToInt, id_eq, hExtg, hExtℓ]
    split_ifs with hin
    · intro val hpair
      rw [hslotMem e hem] at hpair ⊢
      rcases hLive e hin with ⟨h1, h2, hp⟩ | ⟨h1, h2, hp⟩
      · have hvEq : val = initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e) :=
          Option.some.inj (init_forestPairs_snd_unique hnd hpair hp)
        subst hvEq
        refine ⟨by simp [PathEdgeValue.originalGradient, initialPathEdgeValue, hgradEq e hem],
          by simp [initialPathEdgeValue, (hlenPos e hem).2],
          fun _ => ⟨h1, h2⟩, fun h => by simp [initialPathEdgeValue] at h⟩
      · have hvEq : val = (initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)).reverse :=
          Option.some.inj (init_forestPairs_snd_unique hnd hpair hp)
        subst hvEq
        refine ⟨by simp [PathEdgeValue.originalGradient, PathEdgeValue.reverse, initialPathEdgeValue, hgradEq e hem],
          by simp [PathEdgeValue.reverse, initialPathEdgeValue, (hlenPos e hem).2],
          fun h => by simp [PathEdgeValue.reverse, initialPathEdgeValue] at h,
          fun _ => ⟨h1, h2⟩⟩
    · intro val hpa
      rw [(hedges e hem).2.1] at hpa
      have hvEq : val = initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e) :=
        initPathEdgeAt_unique hpa (hedges e hem).2.2.2
      subst hvEq
      exact ⟨rfl, by simp [PathEdgeValue.originalGradient, initialPathEdgeValue, hgradEq e hem],
        by simp [initialPathEdgeValue, (hlenPos e hem).2]⟩
  · refine ⟨fun e he _ val hpa => ?_, fun e₁ he₁ e₂ he₂ hne _ _ => ?_⟩
    · have hem : e < m := by rw [hExtG, hGE] at he; exact Finset.mem_range.mp he
      rw [hExtToInt, id_eq, (hedges e hem).2.1] at hpa
      have hvEq : val = initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e) :=
        initPathEdgeAt_unique hpa (hedges e hem).2.2.2
      subst hvEq; exact hdetB e hem
    · have he₁m : e₁ < m := by rw [hExtG, hGE] at he₁; exact Finset.mem_range.mp he₁
      have he₂m : e₂ < m := by rw [hExtG, hGE] at he₂; exact Finset.mem_range.mp he₂
      rw [hExtToInt, id_eq, id_eq, (hedges e₁ he₁m).2.1, (hedges e₂ he₂m).2.1]
      exact hrecDisj e₁ he₁m e₂ he₂m hne

/-- Core execution of `solverInitWiredBody` needing only the detector-threshold bound `hdetB`
(which follows from `LengthsWithin` alone, without requiring a gradient bound in `Init`
preconditions). Produces `OffTreeRecBound` conditionally when gradient and length bounds also
hold. -/
theorem ordSolverInitWired_runs_core
    {w L P E m V psi k epsExp clog threshold initConcreteProc overwriteProc copyWords
      capExp limbMul capLimit wordExp initSpace' initFixed initMul
      graph gradient lengths root pos : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {G : MGraph}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {B_tree : ℤ}
    (hInitSpec : OrdInitConcreteSpecW w L P E m V psi k epsExp cfg Rcore G p initConcreteProc B_tree
      capExp limbMul capLimit wordExp initSpace' initFixed initMul)
    (hOverAt : p.procs[overwriteProc]? = some (initOverwriteIntThresholdsBody clog threshold))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hlocal : Rcore.Local)
    (hw14 : 14 ≤ w) (hmPos : 0 < m)
    (hM₀Eq : cfg.P.M₀ = max m threshold)
    (hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀)
    (h4M3W : 4 * cfg.P.M₀ + 3 < 2 ^ w) (hd1W : cfg.P.d + 1 < 2 ^ w)
    (hεPos : 0 < cfg.ε)
    (hGE : G.E = Finset.range m)
    (hEndsLt : ∀ e ∈ G.E, G.tail e < G.n ∧ G.head e < G.n)
    (hroom : root + (initSpace' + initWiredExtraSpace cfg G) < 2 ^ w)
    (hWordLvl : ∀ i < cfg.P.d,
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.lvlM i + cfg.N₀ + 2) ^ wordExp *
        (L + 1) < 2 ^ w)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)))
    (hGraph : IPM.Machine.GraphAt mem graph G)
    (hGraphBelow : graph + (IPM.Machine.graphWords G).length ≤ root)
    (hLenEnd : lengths + G.m * L ≤ root)
    (hGradEnd : gradient + G.m * L ≤ root)
    (hVecValid : ∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧
      0 < Num.intVal mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L)
    (hLenWithin : IPM.LengthsWithin G E (IPM.Machine.readVector mem lengths 4 L P m))
    (hGradWithin : ∀ e ∈ G.E, |IPM.Machine.readVector mem gradient 4 L P m e| ≤ (2 : ℝ) ^ E)
    (hz : ZeroFrom mem root)
    (hHoldsEx : ∃ σ σ_mwu' γ_ℓ γ_c,
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.toTreeChain.Holds G
        (IPM.Machine.readVector mem lengths 4 L P m) σ σ_mwu' γ_ℓ γ_c)
    (hdetB : ∀ e < m,
      |(initialPathEdgeValue P cfg.ε
        (Num.intVal mem (gradient + e * L) 4 L)
        ((Num.intVal mem (lengths + e * L) 4 L).toNat)).detector| ≤ B_tree) :
    let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
    let len₀ := IPM.Machine.readVector mem lengths 4 L P m
    let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ (finalHeap cost : ℕ) (out : State) (tok : SolverToken cfg L Rcore),
      Runs w p ω (solverInitWiredBody initConcreteProc overwriteProc copyWords)
        (startState [graph, gradient, lengths, L, P, V, root] mem pos)
        (.returned finalHeap) out cost ∧
      MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P s0 ∧
      Rrep.rep root s0 tok out.mem ∧
      SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tok out.mem ∧
      SolverLevelLayoutAt G.n (initTargetCap cfg G) tok out.mem ∧
      tok.rootECap = initTargetCap cfg G ∧
      tok.intCap = initTargetCap cfg G ∧
      out.mem (solverSelectHeapAddr tok.table cfg.P.d) = 0 ∧
      out.mem (solverSelectBlocksAddr tok.table cfg.P.d) = 0 ∧
      PathTreeNumericInv tok.tree tok.trees B_tree 0 ∧
      OffTreeRecInv s0 L out.mem tok.edgeRecords B_tree ∧
      ((∀ e < m,
        let v := initialPathEdgeValue P cfg.ε
          (Num.intVal mem (gradient + e * L) 4 L) ((Num.intVal mem (lengths + e * L) 4 L).toNat)
        |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree) →
        OffTreeRecBound s0 L out.mem tok.edgeRecords B_tree) ∧
      root ≤ finalHeap ∧ finalHeap ≤ root + (initSpace' + initWiredExtraSpace cfg G) ∧ ZeroFrom out.mem finalHeap ∧
      (∀ a < root, out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok a → root ≤ a ∧ a < finalHeap) ∧
      cost + Rrep.phi root tok out.mem ≤
        initFixed + initWiredExtraCost cfg G +
          initMul * s0.chain.totalRuntime := by
  dsimp only
  let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
  let len₀ := IPM.Machine.readVector mem lengths 4 L P m
  let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
  let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
  let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
  let C := cfg.P
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  obtain ⟨σ, σ_mwu', γ_ℓ, γ_c, hHolds⟩ := hHoldsEx
  have hSub := s0.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  have hTForest : s0.chain.toTreeChain.chainTree.IsForest :=
    s0.chain.toTreeChain.chainTree_isForest hHolds hSub
  have hTSub : s0.chain.toTreeChain.chainTree.E ⊆ G.E := by
    have hs := s0.chain.toTreeChain.chainTree_isSubgraph hHolds hSub
    rw [hHolds.1] at hs; exact hs.2.1
  obtain ⟨bInit, hbInit, hInitRun⟩ := hInitSpec
  obtain ⟨mid, cInit, rootGraph, table, levelsEnd, treeEnd, finalHeap, vcLast, ecLast,
      sFin, yTree, slotFin, nameFin, yCore, yTerm, hrInit,
      hrootDirM, hdetectM, hnumM, hchainM, hfreshM, hschedM, hinOffM,
      hedgesM, hinvM, hzM, hrootLeFin, hcallerM,
      hdgM, hroot16LeRG, hrootGLeLen0, hlen0EqTb, hlevGe, htreeLeEnd, hafterLeFin, hfinLtW,
      hSel0M, hMetaM, hMetaOrdM, htreeDisjM, hcoresAtM, hfinLeSp, hcInitBound⟩ :=
    hInitRun graph gradient lengths root pos ω mem (by omega) hWordLvl hCapFacts
      hGraph hGraphBelow hLenEnd hGradEnd hVecValid hLenWithin hGradWithin hz
  let eCap := initRootECap cfg.N₀ C.k m
  let len0Buf := table - eCap * L
  let levelMeta := solverLevelMetaAddr table C.d
  let handle := solverHandleAddr table C.d
  let levelTable := handle + 18
  let freshCounter := levelsEnd + (4 * (C.d + 1) + 1)
  let forward := freshCounter + 1
  let inverse := forward + m
  let edgeThresholds := inverse + m
  let treeHeap := edgeThresholds + m
  let slots := treeEnd
  let names := treeEnd + m
  let slotThresholds := treeEnd + m + 2 * G.n
  let edgeRecords := treeEnd + m + 2 * G.n + 2 * G.n
  let offReadyList := treeEnd + m + 2 * G.n + 2 * G.n + m
  let inOffReady := treeEnd + m + 2 * G.n + 2 * G.n + m + m
  have hLpos : 0 < L := by
    by_contra h0
    have hL0 : L = 0 := by omega
    have hpos := (hVecValid 0 hmPos).2.1
    rw [hL0] at hpos
    simp [Num.intVal, Num.unsignedVal] at hpos
  have hLayoutW : root + 1 < 2 ^ w ∧ handle + 12 < 2 ^ w ∧ table + C.d < 2 ^ w ∧
      root ≤ table ∧ table + C.d < finalHeap := by
    have hfinW' : finalHeap < 2 ^ w := hfinLtW
    have h1a : root + 16 + (L + 1) + 6 ≤ rootGraph := hroot16LeRG
    have h1 : rootGraph + dynGraphSize G.n eCap ≤ len0Buf := hrootGLeLen0
    have h1b : len0Buf + eCap * L = table := hlen0EqTb
    have h2 : table + (4 * C.d + 4) + 18 + (C.d + 1) + (C.d + 1) ≤ levelsEnd := by
      dsimp only [C]; unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr at hlevGe; omega
    have h3 : levelsEnd + (4 * (C.d + 1) + 1) + 1 + m + m + m ≤ treeEnd := htreeLeEnd
    have h4 : treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L +
        m * initEdgeRecordSpace L ≤ finalHeap := hafterLeFin
    dsimp only [handle, C]
    unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hroot0M : mid.mem root = handle := by simpa using hrootDirM 0 (by simp)
  have hroot1M : mid.mem (root + 1) = table := by simpa using hrootDirM 1 (by simp)
  obtain ⟨out, cOver, hrOver, hcOver, htabExact, hframeOver⟩ :=
    initOverwriteIntThresholdsBody_runs (w := w) (clog := clog) (threshold := threshold)
      (P := C) (p := p) (ω := ω) (mem := mid.mem) (pos := mid.pos)
      hclog hw14 hM₀Eq hroot0M hroot1M hchainM.chain hLayoutW.1 hLayoutW.2.1 h4M3W hd1W hLayoutW.2.2.1
  let newCap := C.M₀ + intRebuildThreshold C (4 * C.M₀) 0 + 2 * m
  have hGm : G.m = m := by unfold MGraph.m; rw [hGE, Finset.card_range]
  have hNewCapEq : newCap = initTargetCap cfg G := by
    unfold initTargetCap Chain.Ordered.alg2NameBase newCap
    have hsup : G.E.sup id + 1 = m := by rw [hGE]; exact range_sup_id_add_one hmPos
    rw [hsup, hGm, hN₀Eq, max_eq_right (by omega : m ≤ cfg.P.M₀)]
  let s0St := startState [graph, gradient, lengths, L, P, V, root] mem pos
  let s1St : State := { s0St with regs := Function.update s0St.regs 8 root }
  let s2St : State := { regs := Function.update s1St.regs 9 finalHeap, mem := mid.mem, pos := mid.pos }
  let s3St : State := { regs := Function.update s2St.regs 7 newCap, mem := out.mem, pos := out.pos }
  have hr1 : Runs w p ω (.assign 8 (.reg 6)) s0St .normal s1St 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0St, startState], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.call 9 initConcreteProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6])
      s1St .normal s2St (cInit + 8) :=
    runs_call_iff.mpr ⟨[graph, gradient, lengths, L, P, V, root], _, .returned finalHeap, mid, cInit,
      by simp [evalArgs, Expr.eval, s1St, s0St, startState], hbInit, hrInit, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hr3 : Runs w p ω (.call 7 overwriteProc [.reg 8]) s2St .normal s3St (cOver + 2) :=
    runs_call_iff.mpr ⟨[root], _, .returned newCap, out, cOver,
      by simp [evalArgs, Expr.eval, s2St, s1St], hOverAt, hrOver, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hlenPos : ∀ e < m, 0 < lenInt e ∧ ((lenInt e : ℝ) / (2 : ℝ) ^ P) = len₀ e := by
    intro e he
    obtain ⟨_, hpos, _⟩ := hVecValid e he
    have htoNat : ((lenInt e : ℕ) : ℤ) = Num.intVal mem (lengths + e * L) 4 L :=
      Int.toNat_of_nonneg (le_of_lt hpos)
    refine ⟨by dsimp only [lenInt]; omega, ?_⟩
    dsimp only [len₀, IPM.Machine.readVector]
    rw [ite_eq_left he, Num.fixVal]
    exact congrArg (fun x : ℝ => x / (2 : ℝ) ^ P) (by exact_mod_cast htoNat)
  have hgradEq : ∀ e < m, ((gradInt e : ℝ) / (2 : ℝ) ^ P) = grad₀ e := by
    intro e he; dsimp only [grad₀, gradInt, IPM.Machine.readVector]; rw [ite_eq_left he, Num.fixVal]
  let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
  have hrecDisj : ∀ e₁ < m, ∀ e₂ < m, e₁ ≠ e₂ →
      (threshHeap + 3 * L + e₁ * initEdgeRecordSpace L + Num.fixedDivideSpace L + L) + (2 + 4 * L) ≤
        threshHeap + 3 * L + e₂ * initEdgeRecordSpace L + Num.fixedDivideSpace L + L ∨
      (threshHeap + 3 * L + e₂ * initEdgeRecordSpace L + Num.fixedDivideSpace L + L) + (2 + 4 * L) ≤
        threshHeap + 3 * L + e₁ * initEdgeRecordSpace L + Num.fixedDivideSpace L + L := by
    intro e₁ _ e₂ _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have hstep : (e₁ + 1) * initEdgeRecordSpace L ≤ e₂ * initEdgeRecordSpace L :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at hstep; unfold initEdgeRecordSpace at hstep ⊢; omega
    · right
      have hstep : (e₂ + 1) * initEdgeRecordSpace L ≤ e₁ * initEdgeRecordSpace L :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hgt)
      rw [Nat.succ_mul] at hstep; unfold initEdgeRecordSpace at hstep ⊢; omega
  obtain ⟨ts, fs, ds, hLctM, hNumM, hedgeAccM, hnamedM, horientM, hoffRecM⟩ :=
    init_accounts_orient_offTree (model := s0) (G := G) (m := m) (L := L) (P := P)
      rfl rfl rfl rfl rfl rfl rfl hGE hTSub hεPos hlenPos hgradEq
      hdetB hinOffM hedgesM hrecDisj hinvM
  let tagFn := initSolverTag (cfg := cfg) (L := L) (Rcore := Rcore)
    root rootGraph len0Buf table levelsEnd treeEnd m G.n eCap vcLast ecLast (s0.chain.G C.d) yTree yTerm
    (fun i => mid.mem (levelTable + i)) yCore (mid.mem (levelTable + C.d))
    (fun j => mid.mem (levelMeta + j)) (fun j => mid.mem (levelMeta + C.d + j))
  let tok : SolverToken cfg L Rcore :=
    { handle := handle, table := table, levelsEnd := levelsEnd,
      forward := forward, inverse := inverse, freshCounter := freshCounter,
      slots := slots, names := names, slotThresholds := slotThresholds,
      edgeThresholds := edgeThresholds, edgeRecords := edgeRecords,
      offReadyCount := 0, offReadyList := offReadyList, inOffReady := inOffReady,
      rootGraph := rootGraph, rootECap := eCap, intCap := m, treeHeap := treeHeap,
      searchSpace := 20 * (4 * L + 8) + 100, readSpace := 20 * (4 * L + 8) + 100,
      alphaPtr := root + 16, tree := sFin, trees := ts, free := fs, depth := ds,
      treeTok := yTree, coreHandle := fun i => mid.mem (levelTable + i), coreTok := yCore,
      termHandle := mid.mem (levelTable + C.d), vcLast := vcLast, ecLast := ecLast, termTok := yTerm,
      owned := fun a => tagFn a ≠ 0 ∨ (∃ j < C.d, a = mid.mem (levelTable + j)), tag := tagFn }
  have hTagAndFoot := initSolverTag_spec (cfg := cfg) (L := L) (P := P) (m := m) (eCap := eCap)
    (V := V) (psi := psi) (k := k) (epsExp := epsExp) (Rcore := Rcore)
    (root := root) (rootGraph := rootGraph) (len0Buf := len0Buf) (table := table) (levelsEnd := levelsEnd)
    (treeEnd := treeEnd) (finalHeap := finalHeap) (vcLast := vcLast) (ecLast := ecLast)
    (G := G) (sFin := sFin) (yTree := yTree) (yCore := yCore) (yTerm := yTerm)
    (mem := mid.mem) (model := s0) rfl rfl hGE hinvM.1 hmPos (initRootECap_ge_m cfg.N₀ C.k m) hLpos
    (by omega) hrootGLeLen0 hlen0EqTb hlevGe htreeLeEnd hafterLeFin
    (by have hG0 : s0.chain.G 0 = G := hHolds.1; rw [hG0]; exact hdgM) hMetaM
    (fun e he => ⟨(hedgesM e he).1, (hedgesM e he).2.1⟩)
    hinvM.2.2.2.1 htreeDisjM hcoresAtM
  have htagsM : SolverTagsAt root m s0 tok mid.mem := hTagAndFoot.1
  have hCapsInvM : SolverLevelCapsInv P V G.n eCap s0 tok mid.mem := hTagAndFoot.2.1
  have hfootBounds : ∀ a, Rrep.foot root tok a → root ≤ a ∧ a < finalHeap := hTagAndFoot.2.2
  have hOutEqOfTag (a : ℕ) (hne3 : tagFn a ≠ 3) : out.mem a = mid.mem a := by
    apply hframeOver a
    by_contra hIn; push Not at hIn
    have hsub : table + (a - table) = a := Nat.add_sub_of_le hIn.1
    have hdiff : a - table ≤ C.d := Nat.sub_le_of_le_add (by rw [Nat.add_comm]; exact hIn.2)
    exact hne3 (by rw [← hsub]; exact htagsM.2.2.2.1 (a - table) hdiff)
  have hOutEqIfNot3 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 3) : out.mem a = mid.mem a :=
    hOutEqOfTag a (fun h => hv (ht.symm.trans h))
  have hrepOut : Rrep.rep root s0 tok s3St.mem := by
    change (solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore).rep
      root s0 tok out.mem
    obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
      t16, t1718, t19, t20, t21⟩ := htagsM
    have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
    have htermLocal := LastLevelProgram.lastLevelRepresentation_local vcLast ecLast
      4 L P (s0.chain.G C.d).E
    have hmem_et (e : ℕ) (he : e ∈ s0.extG.E) :
        out.mem (edgeThresholds + e) = mid.mem (edgeThresholds + e) :=
      hOutEqIfNot3 (t12 e (Finset.mem_range.mp (hGE ▸ he))) (by decide)
    have hmem_er (e : ℕ) (he : e ∈ s0.extG.E) :
        out.mem (edgeRecords + e) = mid.mem (edgeRecords + e) :=
      hOutEqIfNot3 (t13 e (Finset.mem_range.mp (hGE ▸ he))) (by decide)
    have hnextFreshEq : s0.nextFresh = m := by
      change G.E.sup id + 1 = m; rw [hGE]; exact range_sup_id_add_one hmPos
    have hchainG0 : s0.chain.G 0 = G := hHolds.1
    have hschedCell (off : ℕ) (hoff : off < 4 * (C.d + 1) + 1) : out.mem (levelsEnd + off) = 0 :=
      (hOutEqIfNot3 (t5 off hoff) (by decide)).trans
        (hschedM (levelsEnd + off) (Nat.le_add_right _ _) (Nat.add_lt_add_left hoff levelsEnd))
    refine ⟨
      fun j hj => (hOutEqIfNot3 (t1 j (by simpa [List.length] using hj)) (by decide)).trans (hrootDirM j hj),
      fun j hj => (hOutEqIfNot3 (t2 j (by simp [List.length] at hj; omega)) (by decide)).trans (hdetectM j hj),
      fun j hj => by
        have h1 : handle + 5 + j = handle + (5 + j) := by omega
        rw [h1]; exact (hOutEqIfNot3 (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide)).trans (by rw [← h1]; exact hnumM j hj),
      fun j hj => by
        have h1 : handle + 9 + j = handle + (9 + j) := by omega
        rw [h1]; exact (hOutEqIfNot3 (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide)).trans (by rw [← h1]; exact hchainM j hj),
      by rw [hchainG0]; exact freshInv_init G,
      ⟨(hOutEqIfNot3 t6 (by decide)).trans (by rw [hnextFreshEq]; exact hfreshM.1),
       fun e he => (hOutEqIfNot3 (t7 e he) (by decide)).trans (hfreshM.2.1 e he),
       fun e he => (hOutEqIfNot3 (t8 e he) (by decide)).trans (hfreshM.2.2 e he)⟩,
      fun e he => Finset.mem_range.mp (hGE ▸ he),
      ⟨fun e he => by rw [hchainG0] at he; exact Finset.mem_range.mp (hGE ▸ he), hmPos,
        hnextFreshEq.le, fun _ _ => rfl⟩,
      ⟨fun i => hschedCell i.val (lt_of_lt_of_le i.isLt (by change C.d + 1 ≤ 4 * (C.d + 1) + 1; omega)),
       fun i hi => by
         have hi' : i ≤ C.d := hi
         have h1 : levelsEnd + (C.d + 1) + i = levelsEnd + (C.d + 1 + i) := Nat.add_assoc _ _ _
         rw [h1]; exact hschedCell (C.d + 1 + i) (by omega),
       fun i hi => by
         have hi' : i ≤ C.d := hi
         have h1 : levelsEnd + 2 * (C.d + 1) + i = levelsEnd + (2 * (C.d + 1) + i) := Nat.add_assoc _ _ _
         rw [h1]; exact hschedCell (2 * (C.d + 1) + i) (by omega),
       fun i hi => by
         have hi' : i ≤ C.d := hi
         have h1 : levelsEnd + 3 * (C.d + 1) + i = levelsEnd + (3 * (C.d + 1) + i) := Nat.add_assoc _ _ _
         rw [h1]
         exact (hschedCell (3 * (C.d + 1) + i) (by omega)).trans
           (ordRebuildSuffix_updCount_zero cfg.T cfg.L cfg.P (Chain.levelM cfg.TP cfg.P) cfg.N₀
             len₀ grad₀ i cfg.P.d 0 _ _ _ _ _ _).symm,
       hschedCell (4 * (C.d + 1)) (Nat.lt_succ_self _)⟩,
      ⟨Nat.zero_le _, fun _ hj => (Nat.not_lt_zero _ hj).elim, fun _ hj => (Nat.not_lt_zero _ hj).elim,
       fun e he => Or.inl ((hOutEqIfNot3 (t15 e he) (by decide)).trans (hinOffM e he)),
       fun e he h1 => by rw [(hOutEqIfNot3 (t15 e he) (by decide)).trans (hinOffM e he)] at h1; exact (Nat.zero_ne_one h1).elim⟩,
      hinvM.1, hLctM,
      (htreeLocal treeHeap sFin yTree mid.mem out.mem
        (fun a ha => (hOutEqIfNot3 (t16 a ha) (by decide)).symm)).1 hinvM.2.2.1,
      ?_, ?_,
      (hOutEqIfNot3 (t4 C.d (by change C.d < 2 * (C.d + 1); omega)) (by decide)),
      by
        have h1 : levelTable + (C.d + 1) + C.d = levelTable + (2 * C.d + 1) := by omega
        rw [h1]; exact (hOutEqIfNot3 (t4 (2 * C.d + 1) (by change 2 * C.d + 1 < 2 * (C.d + 1); omega)) (by decide)).trans (by rw [← h1]; exact hcoresAtM.2.1),
      (htermLocal (mid.mem (levelTable + C.d)) _ yTerm mid.mem out.mem
        (fun a ha => (hOutEqIfNot3 (t19 a ((lastLevelRepresentation_foot_indep_P vcLast ecLast 4 L P 0 _ _ _ _).mp ha))
          (by decide)).symm)).1 hcoresAtM.2.2.1,
      ?_,
      ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16,
       fun e he => by
         change (∀ j < L, tok.tag (out.mem (edgeThresholds + e) + j) = 17) ∧
           (e ∉ s0.chain.toTreeChain.chainTree.E → ∀ j < 2 + 4 * L, tok.tag (out.mem (edgeRecords + e) + j) = 18)
         rw [hmem_et e he, hmem_er e he]; exact t1718 e he,
       t19, t20, t21⟩⟩
    · refine ⟨fun e he => ?_, fun slot val hslot hpair => ?_⟩
      · obtain ⟨heiCap, hthr, hbranch⟩ := hedgeAccM.1 e he
        change e < m at heiCap
        refine ⟨heiCap, ?_, ?_⟩
        · change PathIntAt out.mem (out.mem (edgeThresholds + e)) 4 L (detectorThreshold P cfg.ε (s0.extℓ e))
          rw [hmem_et e he]
          exact hthr.congr (fun j hj => hOutEqIfNot3 ((t1718 e he).1 j hj) (by decide))
        · change (if e ∈ s0.chain.toTreeChain.chainTree.E then _ else _) at hbranch ⊢
          split_ifs at hbranch ⊢ with hin
          · obtain ⟨hsnz, his, hnm, hst, hval⟩ := hbranch
            have hslotLt : mid.mem (slots + e) < 2 * sFin.n := his.2
            have hslEq : out.mem (slots + e) = mid.mem (slots + e) := hOutEqIfNot3 (t9 e heiCap) (by decide)
            change out.mem (slots + e) ≠ 0 ∧ isEdgeSlot sFin.n (out.mem (slots + e)) ∧
              out.mem (names + out.mem (slots + e)) = e ∧
              out.mem (slotThresholds + out.mem (slots + e)) = out.mem (edgeThresholds + e) ∧
              ∃ (val : PathEdgeValue) (account : ℤ),
                (out.mem (slots + e), some val) ∈ forestPairs pathPayload sFin.splay ts ∧
                (val.originalFlow : ℝ) / (2 : ℝ) ^ P = s0.flow e ∧
                (account : ℝ) / (2 : ℝ) ^ P = s0.detectAccum e ∧
                val.detector = account - detectorThreshold P cfg.ε (s0.extℓ e)
            rw [hslEq, hmem_et e he]
            exact ⟨hsnz, his, (hOutEqIfNot3 (t10 _ hslotLt) (by decide)).trans hnm,
              (hOutEqIfNot3 (t11 _ hslotLt) (by decide)).trans hst, hval⟩
          · obtain ⟨hs0, val, acc, hrec, hfl, hac, hdet, hpush⟩ := hbranch
            have hrecEq : out.mem (edgeRecords + e) = mid.mem (edgeRecords + e) := hmem_er e he
            change out.mem (slots + e) = 0 ∧ ∃ val account,
              PathEdgeAt out.mem (out.mem (edgeRecords + e)) 4 L (some val) ∧ _
            rw [hrecEq]
            refine ⟨(hOutEqIfNot3 (t9 e heiCap) (by decide)).trans hs0, val, acc,
              hrec.congr (fun x hxlo hxhi => by
                have hx : x = mid.mem (edgeRecords + e) + (x - mid.mem (edgeRecords + e)) := (Nat.add_sub_of_le hxlo).symm
                have hxhi' : x < mid.mem (edgeRecords + e) + (2 + 4 * L) := by
                  rw [← Nat.add_assoc]; exact hxhi
                have hxlt : x - mid.mem (edgeRecords + e) < 2 + 4 * L :=
                  Nat.sub_lt_left_of_lt_add hxlo hxhi'
                rw [hx]; exact hOutEqIfNot3 ((t1718 e he).2 hin _ hxlt) (by decide)),
              hfl, hac, hdet, fun hnn => (hOutEqIfNot3 (t15 e heiCap) (by decide)).trans (hpush hnn)⟩
      · have hslotLt : slot < 2 * sFin.n := hslot.2
        obtain ⟨heiCap, hin, hsl, heE, he2i⟩ := hedgeAccM.2 slot val hslot hpair
        have hnmEq : out.mem (names + slot) = mid.mem (names + slot) := hOutEqIfNot3 (t10 slot hslotLt) (by decide)
        dsimp only at heiCap hin hsl heE he2i ⊢
        rw [hnmEq]
        exact ⟨heiCap, hin, (hOutEqIfNot3 (t9 _ heiCap) (by decide)).trans hsl, heE, he2i⟩
    · intro i hi
      have hi' : i < C.d := hi
      refine ⟨hOutEqIfNot3 (t4 i (by change i < 2 * (C.d + 1); omega)) (by decide),
        by
          have h1 : levelTable + (C.d + 1) + i = levelTable + (C.d + 1 + i) := Nat.add_assoc _ _ _
          have hlt : C.d + 1 + i < 2 * (C.d + 1) := by omega
          rw [h1]; exact (hOutEqIfNot3 (t4 _ hlt) (by decide)).trans (by rw [← h1]; exact (hcoresAtM.1 i hi').1),
        (hlocal (mid.mem (levelTable + i)) _ (yCore i) mid.mem out.mem
          (fun a ha => (hOutEqIfNot3 (t21 i hi' a ha) (by omega)).symm)).1 (hcoresAtM.1 i hi').2.1⟩
    · refine ⟨by rw [hN₀Eq]; exact htabExact,
        by rw [hchainG0]; exact hdgM.of_agree (fun a h1 h2 => hOutEqIfNot3 (t20 a h1 h2) (by decide)),
        ⟨hTForest, fun ei hei => by
          have heiG : ei ∈ G.E := hTSub hei
          have hEnds : s0.chain.toTreeChain.chainTree.tail ei = G.tail ei ∧
              s0.chain.toTreeChain.chainTree.head ei = G.head ei := by
            change (s0.chain.G 0).tail ei = G.tail ei ∧ (s0.chain.G 0).head ei = G.head ei
            rw [hchainG0]; exact ⟨rfl, rfl⟩
          exact ⟨Finset.mem_range.mp (hGE ▸ heiG), hEnds.1 ▸ (hEndsLt ei heiG).1,
            hEnds.2 ▸ (hEndsLt ei heiG).2, LSF.isForest_no_selfLoop hTForest hei⟩⟩,
        ⟨fun ei hei => by
            have heiCap : ei < m := Finset.mem_range.mp (hGE ▸ hTSub hei)
            rw [hOutEqIfNot3 (t9 ei heiCap) (by decide)]
            have hfwd := hnamedM.forward ei hei
            have hslotLt : mid.mem (slots + ei) < 2 * sFin.n := hfwd.2.1.2
            exact ⟨hfwd.1, hfwd.2.1, (hOutEqIfNot3 (t10 _ hslotLt) (by decide)).trans hfwd.2.2⟩,
         fun k hk hks => by
            have hkLt : k < 2 * sFin.n := hks.2
            rw [hOutEqIfNot3 (t10 k hkLt) (by decide)]
            obtain ⟨hmemF, hslotEq⟩ := hnamedM.inverse k hk hks
            have heiCap : mid.mem (names + k) < m := Finset.mem_range.mp (hGE ▸ hTSub hmemF)
            exact ⟨hmemF, (hOutEqIfNot3 (t9 _ heiCap) (by decide)).trans hslotEq⟩,
         fun ei hei => by
            have heiCap : ei < m := Finset.mem_range.mp (hGE ▸ hTSub hei)
            rw [hOutEqIfNot3 (t9 ei heiCap) (by decide)]; exact hnamedM.endpoints ei hei⟩,
        fun e he => by
          have hor := horientM e he
          have heiCap : e < m := Finset.mem_range.mp (hGE ▸ he)
          change (if e ∈ s0.chain.toTreeChain.chainTree.E then _ else _) at hor ⊢
          split_ifs at hor ⊢ with hin
          · intro val hpair
            have hslEq : out.mem (slots + e) = mid.mem (slots + e) := hOutEqIfNot3 (t9 e heiCap) (by decide)
            change (out.mem (slots + e), some val) ∈ _ at hpair
            change _ ∧ _ ∧ (val.forward = true →
                inducedSubPar pathPayload sFin.splay ts (vid (s0.chain.toTreeChain.chainTree.head e)) = out.mem (slots + e) ∧
                inducedSubPar pathPayload sFin.splay ts (out.mem (slots + e)) = vid (s0.chain.toTreeChain.chainTree.tail e)) ∧
              (val.forward = false →
                inducedSubPar pathPayload sFin.splay ts (vid (s0.chain.toTreeChain.chainTree.tail e)) = out.mem (slots + e) ∧
                inducedSubPar pathPayload sFin.splay ts (out.mem (slots + e)) = vid (s0.chain.toTreeChain.chainTree.head e))
            rw [hslEq] at hpair ⊢; exact hor val hpair
          · intro val hpa
            have herEq : out.mem (edgeRecords + e) = mid.mem (edgeRecords + e) := hmem_er e he
            change PathEdgeAt out.mem (out.mem (edgeRecords + e)) 4 L (some val) at hpa
            rw [herEq] at hpa
            exact hor val (hpa.congr fun x hlo hhi => by
              have hx : x = mid.mem (edgeRecords + e) + (x - mid.mem (edgeRecords + e)) := (Nat.add_sub_of_le hlo).symm
              rw [hx]; exact (hOutEqIfNot3 ((t1718 e he).2 hin _ (by omega)) (by decide)).symm)⟩
  have hoffRecOut : OffTreeRecInv s0 L s3St.mem tok.edgeRecords B_tree := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, t13, _, _, _, t1718, _⟩ := htagsM
    refine ⟨fun e he hnot val hpa => ?_, fun e₁ he₁ e₂ he₂ hne hn₁ hn₂ => ?_⟩
    · have heiCap : e < m := Finset.mem_range.mp (hGE ▸ he)
      have hmemEr : out.mem (edgeRecords + e) = mid.mem (edgeRecords + e) := hOutEqIfNot3 (t13 e heiCap) (by decide)
      change PathEdgeAt out.mem (out.mem (edgeRecords + e)) 4 L (some val) at hpa; rw [hmemEr] at hpa
      exact hoffRecM.1 e he hnot val (hpa.congr fun x hlo hhi => by
        have hx : x = mid.mem (edgeRecords + e) + (x - mid.mem (edgeRecords + e)) := (Nat.add_sub_of_le hlo).symm
        rw [hx]; exact (hOutEqIfNot3 ((t1718 e he).2 hnot _ (by omega)) (by decide)).symm)
    · have he₁Cap : e₁ < m := Finset.mem_range.mp (hGE ▸ he₁)
      have he₂Cap : e₂ < m := Finset.mem_range.mp (hGE ▸ he₂)
      change out.mem (edgeRecords + e₁) + (2 + 4 * L) ≤ out.mem (edgeRecords + e₂) ∨
        out.mem (edgeRecords + e₂) + (2 + 4 * L) ≤ out.mem (edgeRecords + e₁)
      rw [hOutEqIfNot3 (t13 e₁ he₁Cap) (by decide), hOutEqIfNot3 (t13 e₂ he₂Cap) (by decide)]
      exact hoffRecM.2 e₁ he₁ e₂ he₂ hne hn₁ hn₂
  have hoffBoundOut :
      (∀ e < m,
        let v := initialPathEdgeValue P cfg.ε
          (Num.intVal mem (gradient + e * L) 4 L) ((Num.intVal mem (lengths + e * L) 4 L).toNat)
        |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree) →
      OffTreeRecBound s0 L s3St.mem tok.edgeRecords B_tree := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, t13, _, _, _, t1718, _⟩ := htagsM
    intro hglB e he hnot val hpa
    have heiCap : e < m := Finset.mem_range.mp (hGE ▸ he)
    have hmemEr : out.mem (edgeRecords + e) = mid.mem (edgeRecords + e) := hOutEqIfNot3 (t13 e heiCap) (by decide)
    change PathEdgeAt out.mem (out.mem (edgeRecords + e)) 4 L (some val) at hpa; rw [hmemEr] at hpa
    have hpaM : PathEdgeAt mid.mem (mid.mem (edgeRecords + e)) 4 L (some val) :=
      hpa.congr fun x hlo hhi => by
        have hx : x = mid.mem (edgeRecords + e) + (x - mid.mem (edgeRecords + e)) := (Nat.add_sub_of_le hlo).symm
        rw [hx]; exact (hOutEqIfNot3 ((t1718 e he).2 hnot _ (by omega)) (by decide)).symm
    rw [(hedgesM e heiCap).2.1] at hpaM
    have hvEq := initPathEdgeAt_unique hpaM (hedgesM e heiCap).2.2.2; subst hvEq
    obtain ⟨hg, hl⟩ := hglB e heiCap
    exact ⟨hg, hl, le_trans (by change |(0 : ℤ)| ≤ _; rw [abs_zero]; exact abs_nonneg _) hg⟩
  have hphiOut : Rrep.phi root tok s3St.mem =
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi treeHeap yTree mid.mem +
        ∑ i : Fin C.d, Rcore.phi (mid.mem (levelTable + i.val)) (yCore i.val) mid.mem := by
    change (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi treeHeap yTree out.mem +
        (∑ i : Fin C.d, Rcore.phi (mid.mem (levelTable + i.val)) (yCore i.val) out.mem) +
        0 * detectOffTreeDrainUnit L = _
    have htreePhi : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi treeHeap yTree out.mem =
        (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi treeHeap yTree mid.mem :=
      ((LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC treeHeap sFin yTree mid.mem out.mem
        (fun a ha => (hOutEqIfNot3 (htagsM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a ha) (by decide)).symm)).2).symm
    have hcorePhi : ∑ i : Fin C.d, Rcore.phi (mid.mem (levelTable + i.val)) (yCore i.val) out.mem =
        ∑ i : Fin C.d, Rcore.phi (mid.mem (levelTable + i.val)) (yCore i.val) mid.mem :=
      Finset.sum_congr rfl fun i _ =>
        ((hlocal (mid.mem (levelTable + i.val)) (chainLevelOrdAbs s0.chain i.val) (yCore i.val) mid.mem out.mem
          (fun a ha => (hOutEqIfNot3 (htagsM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i.val i.isLt a ha)
            (by omega)).symm)).2).symm
    rw [htreePhi, hcorePhi, Nat.zero_mul, Nat.add_zero]
  have hCapsInvOut : SolverLevelCapsInv P V G.n eCap s0 tok s3St.mem :=
    hCapsInvM.preserve rfl (fun j hj => Or.inr ⟨j, hj, rfl⟩)
      (fun a ht => ⟨rfl, by rcases ht with h | h | h | h <;> exact hOutEqIfNot3 h (by omega)⟩)
      (fun j hj => (solverLevelCapsInv_iff_metaCaps.mp hCapsInvM).2.2.2.2.2 j hj |>.2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hnextFreshEq0 : s0.nextFresh = m := by change G.E.sup id + 1 = m; rw [hGE]; exact range_sup_id_add_one hmPos
  obtain ⟨cGrow, outG, tok', hrGrow, hrepG, hcapG, hpresG, hNumG, hoffRecG, hoffBoundG, hrootLeG,
      hfinLeG, hzG, hcallerG, hfootG, hphiG, hcGrow⟩ :=
    initGrowTablesTail_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (copyWords := copyWords) (root := root) (finalHeap := finalHeap)
      (initSpace' := initSpace') (newCap := newCap) (st := s3St) (mem := mem) hCopy hlocal hw14 hmPos
      (by simp [s3St, s2St, s1St]) (by simp [s3St, s2St]) (by simp [s3St]) rfl (by dsimp only [newCap]; omega)
      hnextFreshEq0.le (fun e he => Finset.mem_range.mp (hGE ▸ he)) hrepOut hNumM hoffRecOut hoffBoundOut
      hrootLeFin hfinLeSp (by rw [hNewCapEq]; exact hroom)
      (fun a ha => (hframeOver a (Or.inr (lt_of_lt_of_le hLayoutW.2.2.2.2 ha))).trans (hzM a ha))
      (fun a ha => (hframeOver a (Or.inl (lt_of_lt_of_le ha hLayoutW.2.2.2.1))).trans (hcallerM a ha))
      hfootBounds
  have heCapEq : eCap = initTargetCap cfg G :=
    initRootECap_eq_initTargetCap hN₀Eq hmPos hGE (by omega)
  have hCapsInvG : SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tok' outG.mem :=
    heCapEq ▸ hpresG.to_capsInv hCapsInvOut rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl
  have hLayM : SolverLevelLayoutAt G.n eCap tok mid.mem := by
    refine SolverLevelLayoutAt.of_monotone_blocks hMetaM.2.2.2.2.1 (fun j hj => ?_) (fun j₁ _ j₂ hj2 hlt => ?_)
    · by_cases hj0 : j = 0
      · subst hj0
        change mid.mem (levelMeta + C.d + 0) + dynGraphSize G.n eCap ≤ mid.mem (levelMeta + 0)
        rw [hMetaM.2.2.2.2.1, hMetaM.2.2.2.1]; exact hrootGLeLen0
      · exact hMetaOrdM.1 j (by omega) hj
    · by_cases hj0 : j₁ = 0
      · subst hj0
        change mid.mem (levelMeta + 0) + eCap * L ≤ mid.mem (levelMeta + C.d + j₂)
        rw [hMetaM.2.2.2.1, hlen0EqTb]
        have hlo := (hMetaM.2.2.2.2.2.2 j₂ (by omega) hj2).2.2.2.2.1
        dsimp only [levelMeta, C] at hlo ⊢
        unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr at hlo
        unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hlo ⊢
        omega
      · exact hMetaOrdM.2 j₁ j₂ (by omega) hlt hj2
  have hPresOver : PreservesLevelMeta tok tok mid.mem s3St.mem :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ h => h,
     fun a ht => ⟨rfl, by rcases ht with h | h | h | h <;> exact hOutEqIfNot3 h (by omega)⟩⟩
  have hLayG : SolverLevelLayoutAt G.n (initTargetCap cfg G) tok' outG.mem :=
    heCapEq ▸ hpresG.to_levelLayout hCapsInvOut.1 (hPresOver.to_levelLayout hCapsInvM.1 hLayM)
  have hMeta0 := (solverLevelCapsInv_iff_metaCaps.mp hCapsInvOut).1
  have hSel0G : outG.mem (solverSelectHeapAddr tok'.table cfg.P.d) = 0 ∧
      outG.mem (solverSelectBlocksAddr tok'.table cfg.P.d) = 0 := by
    rw [hpresG.tableEq]
    exact ⟨(hpresG.metaEq _ (Or.inr (Or.inl hMeta0.2.2.1))).2.trans ((hOutEqIfNot3 hMeta0.2.2.1 (by omega)).trans hSel0M.1),
      (hpresG.metaEq _ (Or.inr (Or.inl hMeta0.2.2.2))).2.trans ((hOutEqIfNot3 hMeta0.2.2.2 (by omega)).trans hSel0M.2)⟩
  have hrTotal : Runs w p ω (solverInitWiredBody initConcreteProc overwriteProc copyWords)
      s0St (.returned (finalHeap + 6 * newCap)) outG (2 + ((cInit + 8) + ((cOver + 2) + cGrow + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1St, 2, _, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2St, cInit + 8, _, hr2,
        runs_seq_iff.mpr (Or.inr ⟨s3St, cOver + 2, cGrow, hr3, hrGrow, rfl⟩), rfl⟩), rfl⟩)
  refine ⟨finalHeap + 6 * newCap, _, outG, tok', hrTotal, algorithm2_init_stateFits, hrepG,
    hCapsInvG, hLayG, hpresG.rootECapEq.trans heCapEq, hcapG.trans hNewCapEq, hSel0G.1, hSel0G.2,
    hNumG, hoffRecG, hoffBoundG, hrootLeG,
    by unfold initWiredExtraSpace; rw [← hNewCapEq]; exact hfinLeG, hzG, hcallerG, hfootG, ?_⟩
  rw [hphiG, hphiOut]
  unfold initWiredExtraCost
  rw [hGm, ← hNewCapEq]
  dsimp only [C, s0, treeHeap, edgeThresholds, inverse, forward, freshCounter, levelTable, handle] at hcOver hcInitBound hcGrow ⊢
  omega

/-- End-to-end execution of `solverInitWiredBody` on the ordered chain: composes
`OrdInitConcreteSpecW`, `initOverwriteIntThresholdsBody_runs`, and `initGrowTablesTail_runs`,
establishing `solverStateRep.rep`, `tok.intCap = initTargetCap cfg G`, `MinRatioStateFits`,
`PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound`, footprint locality, space, and cost. -/
theorem ordSolverInitWired_runs
    {w L P E m V psi k epsExp clog threshold initConcreteProc overwriteProc copyWords
      capExp limbMul capLimit wordExp initSpace' initFixed initMul
      graph gradient lengths root pos : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {G : MGraph}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {B_tree : ℤ}
    (hInitSpec : OrdInitConcreteSpecW w L P E m V psi k epsExp cfg Rcore G p initConcreteProc B_tree
      capExp limbMul capLimit wordExp initSpace' initFixed initMul)
    (hOverAt : p.procs[overwriteProc]? = some (initOverwriteIntThresholdsBody clog threshold))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hlocal : Rcore.Local)
    (hw14 : 14 ≤ w) (hmPos : 0 < m)
    (hM₀Eq : cfg.P.M₀ = max m threshold)
    (hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀)
    (h4M3W : 4 * cfg.P.M₀ + 3 < 2 ^ w) (hd1W : cfg.P.d + 1 < 2 ^ w)
    (hεPos : 0 < cfg.ε)
    (hGE : G.E = Finset.range m)
    (hEndsLt : ∀ e ∈ G.E, G.tail e < G.n ∧ G.head e < G.n)
    (hroom : root + (initSpace' + initWiredExtraSpace cfg G) < 2 ^ w)
    (hWordLvl : ∀ i < cfg.P.d,
      ((Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.lvlM i + cfg.N₀ + 2) ^ wordExp *
        (L + 1) < 2 ^ w)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)))
    (hGraph : IPM.Machine.GraphAt mem graph G)
    (hGraphBelow : graph + (IPM.Machine.graphWords G).length ≤ root)
    (hLenEnd : lengths + G.m * L ≤ root)
    (hGradEnd : gradient + G.m * L ≤ root)
    (hVecValid : ∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧
      0 < Num.intVal mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L)
    (hLenWithin : IPM.LengthsWithin G E (IPM.Machine.readVector mem lengths 4 L P m))
    (hGradWithin : ∀ e ∈ G.E, |IPM.Machine.readVector mem gradient 4 L P m e| ≤ (2 : ℝ) ^ E)
    (hz : ZeroFrom mem root)
    (hHoldsEx : ∃ σ σ_mwu' γ_ℓ γ_c,
      (Chain.Ordered.algorithm2_init cfg G
        (IPM.Machine.readVector mem gradient 4 L P m)
        (IPM.Machine.readVector mem lengths 4 L P m)).chain.toTreeChain.Holds G
        (IPM.Machine.readVector mem lengths 4 L P m) σ σ_mwu' γ_ℓ γ_c)
    (hvalBAll : ∀ e < m,
      let v := initialPathEdgeValue P cfg.ε
        (Num.intVal mem (gradient + e * L) 4 L) ((Num.intVal mem (lengths + e * L) 4 L).toNat)
      |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree) :
    let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
    let len₀ := IPM.Machine.readVector mem lengths 4 L P m
    let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ (finalHeap cost : ℕ) (out : State) (tok : SolverToken cfg L Rcore),
      Runs w p ω (solverInitWiredBody initConcreteProc overwriteProc copyWords)
        (startState [graph, gradient, lengths, L, P, V, root] mem pos)
        (.returned finalHeap) out cost ∧
      MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P s0 ∧
      Rrep.rep root s0 tok out.mem ∧
      SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tok out.mem ∧
      SolverLevelLayoutAt G.n (initTargetCap cfg G) tok out.mem ∧
      tok.rootECap = initTargetCap cfg G ∧
      tok.intCap = initTargetCap cfg G ∧
      out.mem (solverSelectHeapAddr tok.table cfg.P.d) = 0 ∧
      out.mem (solverSelectBlocksAddr tok.table cfg.P.d) = 0 ∧
      PathTreeNumericInv tok.tree tok.trees B_tree 0 ∧
      OffTreeRecInv s0 L out.mem tok.edgeRecords B_tree ∧
      OffTreeRecBound s0 L out.mem tok.edgeRecords B_tree ∧
      root ≤ finalHeap ∧ finalHeap ≤ root + (initSpace' + initWiredExtraSpace cfg G) ∧ ZeroFrom out.mem finalHeap ∧
      (∀ a < root, out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok a → root ≤ a ∧ a < finalHeap) ∧
      cost + Rrep.phi root tok out.mem ≤
        initFixed + initWiredExtraCost cfg G +
          initMul * s0.chain.totalRuntime := by
  obtain ⟨fh, c, out, tok, hr, hfits, hrep, hcaps, hlay, hrecap, hcap, hsh, hsb, hnum, hrec, hbound, hrest⟩ :=
    ordSolverInitWired_runs_core hInitSpec hOverAt hCopy hclog hlocal hw14 hmPos hM₀Eq hN₀Eq h4M3W hd1W
      hεPos hGE hEndsLt hroom hWordLvl hCapFacts hGraph hGraphBelow hLenEnd hGradEnd hVecValid
      hLenWithin hGradWithin hz hHoldsEx (fun e he => (hvalBAll e he).2.2.2)
  exact ⟨fh, c, out, tok, hr, hfits, hrep, hcaps, hlay, hrecap, hcap, hsh, hsb, hnum, hrec,
    hbound (fun e he => ⟨(hvalBAll e he).1, (hvalBAll e he).2.1⟩), hrest⟩

end MinCostFlow.MinRatio
