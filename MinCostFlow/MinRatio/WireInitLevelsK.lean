module

public import MinCostFlow.MinRatio.WireInitLevelsLoopK
import Mathlib.Tactic.Ring

/-!
# Ordered Init level loop and terminal builder (`WireInitLevelsK`)

Composes `initLevelsLoop_runs` (`WireInitLevelsLoopK.lean`) across levels `0 .. d - 1` and
`rebuildLastLevelRuntime_runs` + `storeRebuiltLevel` at terminal level `d` to execute
`ordRebuildSuffixProgramKFBLStore` for `Chain.Ordered.algorithm1_initialize`, under
`sparseCoreOrdMachineContractKFBL`. Every level has the caps `(vCap, eCap)` of the input graph,
since op `3` returns the caps of the level. Maintains:
1. All `d` ordered sparse-core representations at `mem (levelTable + i)` with
   `mem (branchTable + i) = chain.bran i` and disjoint footprints in `[levelsStart, levelsEnd)`;
2. The terminal `lastLevelRepresentation` at `mem (levelTable + d)`, with footprint in
   `[levelsStart, levelsEnd)` disjoint from all `d` cores;
3. For every `1 ≤ j < d`, the level-`j` length and graph pointers recorded in `levelMeta[j]`
   and `levelMeta[d + j]`, pointing to valid blocks in `[levelsStart, levelsEnd)` disjoint from
   every core and from the terminal level;
4. The space bound `levelsEnd ≤ levelsStart + ordInitLevelsSpace ...`;
5. The bound `cost + ∑ i : Fin d, Rcore.phi … ≤ ordInitLevelsFixed ... + 26 * d +
   max P.mul lastMult * chain.totalRuntime`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.LastLevelProgram

/-- Complete execution of `ordRebuildSuffixProgramKFBLStore` for `Chain.Ordered.algorithm1_initialize`:
builds all `C.d` ordered sparse-core levels (`0 .. C.d - 1`) and the terminal `lastLevelRepresentation`
collection at level `C.d`, records level `1 ≤ j < C.d` length and graph pointers in `levelMeta`,
establishes pairwise-disjoint footprints in `[levelsStart, levelsEnd)`,
`levelsEnd ≤ levelsStart + ordInitLevelsSpace ...`, and the telescoping cost + potential bound. -/
theorem ordRebuildSuffixProgramKFBL_init_runs
    {w L depth capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy lastInit
      rootGraph lenBase gradBase ordBase ordWords vc0 ec0
      levelTable branchTable levelsStart lvlMTable levelMeta lastMult stretchP lastSpace : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {lastTool : LastLevelTool}
    {C : ChainParams} {P : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAllocation : ℕ → List ℕ → ℕ}
    {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    {G₀ : MGraph} {ℓ₀ g₀ : ℕ → ℝ}
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (hEq : ToolInitOrdEqOnE T) (hLastEq : LastLevelBuildEqOnE lastTool)
    (hlocal : Rcore.Local)
    (hCoreImpl : ∀ i < C.d,
      Rcore.Implements w p init opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth T
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1.G i)
          C.k (lvlM i) N₀ vc0 ec0 capExp P allocation) ∧
      SparseCoreReadoutFootAt fmt L depth T
        ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1.G i)
        C.k (lvlM i) N₀ vc0 ec0 capExp P allocation Rcore p opCore)
    (hLastImpl : ∀ vc ec, vc + ec + 2 ≤ capLimit →
      (lastLevelRepresentation vc ec 4 L fmt.precision
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1.G C.d).E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L lastTool
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1.G C.d)
          vc ec lastMult stretchP lastAllocation))
    (hLastSpaceLe : ∀ args, lastAllocation 1 args ≤ lastSpace)
    (hInitSpaceLe : ∀ i < C.d, ∀ g l gr o h,
      allocation 6 [g, l, gr, o, C.k, lvlM i, N₀, L, fmt.precision, depth, h] ≤ coreInitSpace i)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (h1 : st.regs 1 = C.k) (h4 : st.regs 4 = levelsStart)
    (h6 : st.regs 6 = rootGraph) (h7 : st.regs 7 = lenBase)
    (h8 : st.regs 8 = gradBase) (h9 : st.regs 9 = ordBase)
    (h20 : st.regs 20 = 0) (h21 : st.regs 21 = C.d)
    (h51 : st.regs 51 = levelTable) (h52 : st.regs 52 = branchTable)
    (h56 : st.regs 56 = N₀) (h57 : st.regs 57 = lvlMTable) (h58 : st.regs 58 = levelMeta)
    (h67 : st.regs 67 = L) (h68 : st.regs 68 = fmt.precision) (h98 : st.regs 98 = depth)
    (hTableLayout : levelTable + (C.d + 1) = branchTable ∧ branchTable + (C.d + 1) ≤ levelsStart)
    (hMetaLayout : lvlMTable + C.d = levelMeta ∧ levelMeta + 2 * C.d ≤ levelTable)
    (hMTab : ∀ i < C.d, st.mem (lvlMTable + i) = lvlM i)
    (hcap0 : vc0 + ec0 + 2 ≤ capLimit)
    (hG0 : DynGraphAt st.mem rootGraph vc0 ec0 G₀)
    (hG0End : rootGraph + dynGraphSize vc0 ec0 ≤ levelMeta)
    (hLen0 : EdgeValuesAt st.mem lenBase 4 L fmt.precision G₀.E ℓ₀)
    (hLen0End : lenBase + ec0 * L ≤ levelMeta)
    (hGrad0 : EdgeValuesAt st.mem gradBase 4 L fmt.precision G₀.E g₀)
    (hGrad0End : gradBase + ec0 * L ≤ levelTable)
    (hOrd0 : OrdListAt st.mem ordBase (sortedEnds G₀) ordWords)
    (hOrd0Le : 0 < C.d → ordWords ≤ 2 * N₀ + 2 * lvlM 0 + 1)
    (hOrd0End : ordBase + ordWords ≤ levelTable)
    (hOrd0W : ∀ j < ordWords, st.mem (ordBase + j) < 2 ^ w)
    (hz : ZeroFrom st.mem levelsStart)
    (hk : 0 < C.k) (hdPos : 0 < C.d) (hwk : C.k < 2 ^ w) (hNw : N₀ < 2 ^ w) (hdW : C.d < 2 ^ w)
    (hLW : L < 2 ^ w) (hPW : fmt.precision < 2 ^ w) (hDW : depth < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hMw : ∀ i < C.d, lvlM i < 2 ^ w)
    (hWord : ∀ i < C.d, (lvlM i + N₀ + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
    (hModel :
      let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
      (∀ i < C.d,
        (chain.G i).m ≤ lvlM i ∧ (chain.G i).n ≤ N₀ ∧
        (∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen ℓ₀ i e) ∧
        IsRotationOrder (chain.G i) (chain.levelOrd i) ∧
        (chain.G (i + 1)).E ⊆ (chain.G i).E ∧
        (chain.G (i + 1)).m ≤ nextM i ∧
        (i + 1 < C.d → nextM i ≤ lvlM (i + 1)) ∧
        ordRotWords (chainLevelOrdAbs chain i) 0 ≤ 1 + 2 * N₀ + 2 * nextM i ∧
        (∀ e ∈ (chain.G (i + 1)).E,
          ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
            chain.toTreeChain.chainLen ℓ₀ (i + 1) e)) ∧
      (∀ e ∈ (chain.G C.d).E, 0 < chain.toTreeChain.chainLen ℓ₀ C.d e) ∧
      (∀ e ∈ (chain.G C.d).E,
        2 * (2 : ℝ) ^ stretchP *
          lastLevelStretchBound (chain.G C.d) (chain.toTreeChain.chainLen ℓ₀ C.d) e <
        Num.capacity 4 L))
    (hroom : levelsStart +
      ordInitLevelsSpace L capExp capLimit coreInitSpace lvlM nextM N₀ lastSpace C.d < 2 ^ w) :
    let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
    ∃ (out : State) (levelsEnd vcLast ecLast cost : ℕ) (yCore : ℕ → Rcore.τ) (yTerm : ℕ),
      Runs w p ω
        (ordRebuildSuffixProgramKFBLStore init (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        st .normal out cost ∧
      out.regs 4 = levelsEnd ∧
      levelsStart ≤ levelsEnd ∧
      levelsEnd ≤ levelsStart +
        ordInitLevelsSpace L capExp capLimit coreInitSpace lvlM nextM N₀ lastSpace C.d ∧
      vcLast + ecLast + 2 ≤ capLimit ∧
      ZeroFrom out.mem levelsEnd ∧
      (∀ a < levelsStart,
        (a < levelTable ∨ levelTable + (C.d + 1) ≤ a) →
        (a < branchTable ∨ branchTable + (C.d + 1) ≤ a) →
        (a < levelMeta + 1 ∨ levelMeta + C.d ≤ a) →
        (a < levelMeta + C.d + 1 ∨ levelMeta + 2 * C.d ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ i < C.d,
        out.mem (branchTable + i) = chain.bran i ∧
        Rcore.rep (out.mem (levelTable + i)) (chainLevelOrdAbs chain i) (yCore i) out.mem ∧
        (∀ a, Rcore.foot (out.mem (levelTable + i)) (yCore i) a → levelsStart ≤ a ∧ a < levelsEnd) ∧
        (∀ j < C.d, j ≠ i → ∀ a, Rcore.foot (out.mem (levelTable + i)) (yCore i) a →
          ¬ Rcore.foot (out.mem (levelTable + j)) (yCore j) a) ∧
        (∀ a, Rcore.foot (out.mem (levelTable + i)) (yCore i) a →
          ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
              (out.mem (levelTable + C.d)) yTerm a)) ∧
      (∀ j, 1 ≤ j → j < C.d →
        DynGraphAt out.mem (out.mem (levelMeta + C.d + j)) vc0 ec0 (chain.G j) ∧
        levelsStart ≤ out.mem (levelMeta + C.d + j) ∧
        out.mem (levelMeta + C.d + j) + dynGraphSize vc0 ec0 ≤ levelsEnd ∧
        EdgeValuesAt out.mem (out.mem (levelMeta + j)) 4 L fmt.precision (chain.G j).E
          (chain.toTreeChain.chainLen ℓ₀ j) ∧
        levelsStart ≤ out.mem (levelMeta + j) ∧
        out.mem (levelMeta + j) + ec0 * L ≤ levelsEnd ∧
        (∀ r < C.d,
          (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + ec0 * L →
            ¬ Rcore.foot (out.mem (levelTable + r)) (yCore r) a) ∧
          (∀ a, out.mem (levelMeta + C.d + j) ≤ a →
            a < out.mem (levelMeta + C.d + j) + dynGraphSize vc0 ec0 →
            ¬ Rcore.foot (out.mem (levelTable + r)) (yCore r) a)) ∧
        (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + ec0 * L →
          ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
              (out.mem (levelTable + C.d)) yTerm a) ∧
        (∀ a, out.mem (levelMeta + C.d + j) ≤ a →
          a < out.mem (levelMeta + C.d + j) + dynGraphSize vc0 ec0 →
          ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
              (out.mem (levelTable + C.d)) yTerm a)) ∧
      ((∀ j, 1 ≤ j → j < C.d →
          out.mem (levelMeta + C.d + j) + dynGraphSize vc0 ec0 ≤ out.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < C.d →
          out.mem (levelMeta + j₁) + ec0 * L ≤ out.mem (levelMeta + C.d + j₂))) ∧
      out.mem (branchTable + C.d) = chain.lastBran ∧
      (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).rep
        (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) yTerm out.mem ∧
      (∀ a, (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
          (out.mem (levelTable + C.d)) yTerm a → levelsStart ≤ a ∧ a < levelsEnd) ∧
      (∀ i ≤ C.d, levelsStart ≤ out.mem (levelTable + i) ∧ out.mem (levelTable + i) ≤ levelsEnd) ∧
      (∀ r, r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + (∑ i : Fin C.d, Rcore.phi (out.mem (levelTable + i.val)) (yCore i.val) out.mem) ≤
        ordInitLevelsFixed L capExp capLimit P lvlM nextM N₀ lastMult C.d + 26 * C.d +
          max P.mul lastMult * chain.totalRuntime := by
  dsimp only
  set chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
  have hFacts := ordAlgorithm1_initialize_level_facts hEq lastTool C lvlM N₀ G₀ ℓ₀ g₀
  -- Step 0: `.assign 19 (.reg 20)` from `forRange`
  let s0 : State := { st with regs := Function.update st.regs 19 0 }
  have r0 : Runs w p ω (.assign 19 (.reg 20)) st .normal s0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h20], rfl, rfl, rfl⟩
  have hG0Eq : chain.G 0 = G₀ := hFacts.1
  have hOrd0Eq : chain.levelOrd 0 = Bundle.sortedEnds G₀ := hFacts.2.1
  have hInv0 : InitLevelsLoopInv (w := w) Rcore chain L fmt.precision depth vc0 ec0 capExp
      capLimit levelTable branchTable levelsStart lvlMTable levelMeta coreInitSpace lvlM nextM
      N₀ ℓ₀ g₀ st.mem 0 s0 (fun _ h => absurd h (Nat.not_lt_zero _)) := by
    refine ⟨by simp [s0, h1], by simp [s0], by simp [s0, h21], by simp [s0, h51],
      by simp [s0, h52], by simp [s0, h56], by simp [s0, h57], by simp [s0, h58], by simp [s0, h67],
      by simp [s0, h68], by simp [s0, h98], by simp [s0, h4], by simp [s0, h4],
      by simpa [s0, h4] using hz,
      fun _ _ _ _ _ _ => rfl, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h1 h2 _ => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _),
      ⟨fun _ h1 h2 _ => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _),
       fun _ _ h1 hlt h2 _ => absurd (lt_of_lt_of_le (lt_trans h1 hlt) h2) (lt_irrefl _)⟩,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · refine ⟨vc0, ec0, rfl, rfl, hcap0, by rw [hG0Eq]; simpa [s0, h6] using hG0,
        by simp [s0, h6, h4]; omega,
        fun a _ hhi => Or.inl (by simp [s0, h6] at hhi; omega),
        fun a _ hhi => Or.inl (by simp [s0, h6] at hhi; omega),
        fun a _ hhi => Or.inl (by simp [s0, h6] at hhi; omega),
        by rw [hG0Eq]; simpa [s0, h7, TreeChain.chainLen] using hLen0,
        by simp [s0, h7, h4]; omega,
        fun a _ hhi => Or.inl (by simp [s0, h7] at hhi; omega),
        fun a _ hhi => Or.inl (by simp [s0, h7] at hhi; omega),
        fun a _ hhi => Or.inl (by simp [s0, h7] at hhi; omega),
        by rw [hG0Eq]; simpa [s0, h8] using hGrad0,
        by simp [s0, h8, h4]; omega⟩
    · intro hdPos'
      exact ⟨ordWords, by rw [hOrd0Eq]; simpa [s0, h9] using hOrd0, hOrd0Le hdPos',
        by simp [s0, h9, h4]; omega, by simpa [s0, h9] using hOrd0W⟩
  -- Step 1: Run loop over `0 .. C.d - 1`
  obtain ⟨mid, cLoop, yCoreDep, rLoop, hInvD, hMidRegs, hcLoop⟩ :=
    initLevelsLoop_runs (w := w) (L := L) (depth := depth) (vCap := vc0) (eCap := ec0)
      (capExp := capExp) (capLimit := capLimit)
      (init := init) (coreLenProc := coreLenProc) (edgeProc := edgeProc)
      (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy)
      (levelTable := levelTable) (branchTable := branchTable) (levelsStart := levelsStart)
      (lvlMTable := lvlMTable) (levelMeta := levelMeta) (fmt := fmt) (T := T) (lastTool := lastTool)
      (C := C) (P := P) (allocation := allocation) (coreInitSpace := coreInitSpace) (lvlM := lvlM)
      (nextM := nextM) (N₀ := N₀) (Rcore := Rcore) (p := p) (opCore := opCore) (ω := ω)
      (G₀ := G₀) (ℓ₀ := ℓ₀) (g₀ := g₀) (initMem := st.mem)
      hFour hEq hlocal hCoreImpl hcap0 hInitSpaceLe hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      hTableLayout hMetaLayout hMTab hk hwk hNw hdW hw9 hPW hDW hMw hWord hModel.1
      (by dsimp only [ordInitLevelsSpace] at hroom; omega) C.d 0 (Nat.zero_add C.d)
      s0 (fun _ h => absurd h (Nat.not_lt_zero _)) hInv0
  let yCore : ℕ → Rcore.τ := fun i => if h : i < C.d then yCoreDep i h else yCoreDep 0 hdPos
  -- Step 2: Terminal level `C.d` (`rebuildLastLevelRuntime lastInit ;; storeRebuiltLevel`)
  obtain ⟨vcLast, ecLast, _, _, hcapLast, hGLast, hGEndLast, _, _, _, hLenLast, hLenEndLast, _, _,
      _, _, _⟩ := hInvD.curGraph
  let Rterm := lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E
  have hLastRoom :
      mid.regs 4 + lastAllocation 1 [mid.regs 6, mid.regs 7, L, fmt.precision, mid.regs 4] < 2 ^ w := by
    have h1 := hInvD.heapHi
    have h2 := hLastSpaceLe [mid.regs 6, mid.regs 7, L, fmt.precision, mid.regs 4]
    dsimp only [ordInitLevelsSpace] at hroom; omega
  have hLastPre :
      (lastLevelRuntimeMachineContract fmt L lastTool (chain.G C.d) vcLast ecLast lastMult
        stretchP lastAllocation).initPre [mid.regs 6, mid.regs 7, L, fmt.precision, mid.regs 4] mid.mem := by
    refine ⟨mid.regs 6, mid.regs 7, mid.regs 4, rfl, hFour, hWidth,
      ⟨mid.regs 6, mid.regs 7, mid.regs 4, rfl, hGLast, hGEndLast, hLenEndLast,
        fun e he => hFour ▸ (hLenLast e he).1,
        fun e he => by
          rw [hFour, readEdgeValues_eq hLenLast he]
          exact hModel.2.1 e he⟩,
      fun e he => by
        have hstEq :
            lastLevelStretchBound (chain.G C.d)
              (readEdgeValues mid.mem (mid.regs 7) fmt.limbBits L fmt.precision (chain.G C.d).E) e =
            lastLevelStretchBound (chain.G C.d) (chain.toTreeChain.chainLen ℓ₀ C.d) e := by
          unfold lastLevelStretchBound
          rw [hFour, readEdgeValues_eq hLenLast he]
          congr 2
          exact Finset.sum_congr rfl fun f hf => readEdgeValues_eq hLenLast hf
        rw [hstEq, hFour]
        exact hModel.2.2 e he⟩
  have hLastBuildEq :
      lastTool.build (chain.G C.d)
        (readEdgeValues mid.mem (mid.regs 7) fmt.limbBits L fmt.precision (chain.G C.d).E) =
      (chain.lastK, chain.lastLSFs) := by
    rw [hFacts.2.2.2.1]
    exact hLastEq (chain.G C.d) _ _ (fun e he => by rw [hFour, readEdgeValues_eq hLenLast he])
  have hLastWords : ∀ a ∈ [mid.regs 6, mid.regs 7, L, fmt.precision, mid.regs 4], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨sTerm, levelsEnd, cTerm, yTerm, rTerm, hsT2, hsT3, hsT4, hrepTerm0, _, hrespTerm, hcTerm⟩ :=
    rebuildLastLevelRuntime_runs (w := w) (L := L) (init := lastInit)
      (graph := mid.regs 6) (lengths := mid.regs 7) (heap := mid.regs 4)
      (vCap := vcLast) (eCap := ecLast) (multiplier := lastMult) (stretchPrecision := stretchP)
      (fmt := fmt) (tool := lastTool) (G := chain.G C.d) (allocation := lastAllocation)
      (R := Rterm) (p := p) (op := opLast) (st := mid) (ω := ω)
      (hLastImpl vcLast ecLast hcapLast) rfl rfl rfl hInvD.reg67 hInvD.reg68
      hLastWords hLastPre hInvD.zeroFrom hLastRoom
  rw [hLastBuildEq] at hrepTerm0
  have hTermRegs (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : sTerm.regs r = mid.regs r := by
    unfold rebuildLastLevelRuntime at rTerm
    rcases runs_seq_iff.mp rTerm with ⟨_, _, _, hbad, _⟩ | ⟨a1, _, _, ha1, rRest, _⟩; · cases hbad
    rcases runs_seq_iff.mp rRest with ⟨_, _, _, hbad, _⟩ | ⟨a2, _, _, ha2, ha3, _⟩; · cases hbad
    obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha1
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp ha2
    obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha3
    simp [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4]
  have hfootTerm0 (a : ℕ) (ha : Rterm.foot (mid.regs 4) yTerm a) : mid.regs 4 ≤ a ∧ a < levelsEnd :=
    (hrespTerm.2.2.2.2 a ha).resolve_left id
  obtain ⟨out, rStore, houtH, houtB, hrepTermOut, _, houtFrame, houtRegs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) (st := sTerm)
      (lastLevelRepresentation_local vcLast ecLast 4 L fmt.precision (chain.G C.d).E)
      ((hTermRegs 51 (by decide) (by decide) (by decide)).trans hInvD.reg51)
      ((hTermRegs 52 (by decide) (by decide) (by decide)).trans hInvD.reg52)
      (by omega) (by rw [hsT3]; have := hInvD.heapLo; omega)
      (by rw [hsT3]; have := hInvD.heapLo; omega)
      (fun a ha => by rw [hsT3] at ha ⊢; exact (hfootTerm0 a ha).1)
      (by rw [hsT3]; exact hrepTerm0)
  -- Assemble full run of `ordRebuildSuffixProgramKFBLStore`
  have rFull : Runs w p ω
      (ordRebuildSuffixProgramKFBLStore init (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
      st .normal out ((2 + cLoop + 1) + (cTerm + 7 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨mid, 2 + cLoop + 1, cTerm + 7 + 1,
      runs_seq_iff.mpr (Or.inr ⟨s0, 2, cLoop, r0, rLoop, rfl⟩),
      runs_seq_iff.mpr (Or.inr ⟨sTerm, cTerm, 7, rTerm, rStore, rfl⟩), rfl⟩)
  have houtMem_lt (a : ℕ) (hlt : a < mid.regs 4)
      (hh : a ≠ levelTable + C.d) (hb : a ≠ branchTable + C.d) :
      out.mem a = mid.mem a :=
    (houtFrame a hh hb).trans (hrespTerm.2.2.2.1 a hlt id)
  have hCorePres (i : ℕ) (hi : i < C.d) :
      out.mem (levelTable + i) = mid.mem (levelTable + i) ∧
      out.mem (branchTable + i) = chain.bran i ∧
      Rcore.rep (out.mem (levelTable + i)) (chainLevelOrdAbs chain i) (yCore i) out.mem ∧
      Rcore.phi (out.mem (levelTable + i)) (yCore i) out.mem =
        Rcore.phi (mid.mem (levelTable + i)) (yCoreDep i hi) mid.mem := by
    obtain ⟨hbrI, hrepI, hfootI, _⟩ := hInvD.cores i hi
    have hlv : out.mem (levelTable + i) = mid.mem (levelTable + i) :=
      houtMem_lt _ (by have := hInvD.heapLo; omega) (by omega) (by omega)
    have hbr : out.mem (branchTable + i) = chain.bran i :=
      (houtMem_lt _ (by have := hInvD.heapLo; omega) (by omega) (by omega)).trans hbrI
    have hlocI := hlocal (mid.mem (levelTable + i)) (chainLevelOrdAbs chain i) (yCoreDep i hi)
      mid.mem out.mem (fun a ha => by
        obtain ⟨hlo, hhi⟩ := hfootI a ha
        exact (houtMem_lt a hhi (by omega) (by omega)).symm)
    have hyi : yCore i = yCoreDep i hi := by simp [yCore, hi]
    exact ⟨hlv, hbr, by rw [hlv, hyi]; exact hlocI.1 hrepI, by rw [hlv, hyi]; exact hlocI.2.symm⟩
  have hSumFin :
      (∑ i : Fin C.d, Rcore.phi (out.mem (levelTable + i.val)) (yCore i.val) out.mem) =
      (∑ i : Fin C.d, Rcore.phi (mid.mem (levelTable + i.val)) (yCoreDep i.val i.isLt) mid.mem) :=
    Finset.sum_congr rfl fun i _ => (hCorePres i.val i.isLt).2.2.2
  have hTotalRT := algorithm1_initialize_totalRuntime T lastTool C lvlM N₀ G₀ ℓ₀ g₀
  refine ⟨out, levelsEnd, vcLast, ecLast, _, yCore, yTerm, rFull,
    by rw [houtRegs, hsT4], hInvD.heapLo.trans hrespTerm.1, ?_, hcapLast, ?_, ?_, ?_, ?_, ?_,
    by rw [houtB, hFacts.2.2.1],
    by rw [houtH]; exact hrepTermOut,
    fun a ha => by
      rw [houtH, houtRegs, hsT3] at ha
      exact ⟨hInvD.heapLo.trans (hfootTerm0 a ha).1, (hfootTerm0 a ha).2⟩,
    fun i hi => by
      by_cases hlt : i < C.d
      · rw [(hCorePres i hlt).1]
        exact ⟨(hInvD.handlesLe i hlt).1, (hInvD.handlesLe i hlt).2.trans hrespTerm.1⟩
      · have hieq : i = C.d := by omega
        subst hieq; rw [houtH, houtRegs, hsT3]; exact ⟨hInvD.heapLo, hrespTerm.1⟩,
    fun r hr => by
      rw [houtRegs, hTermRegs r (by rcases hr with rfl | rfl | _ <;> omega)
        (by rcases hr with rfl | rfl | _ <;> omega) (by rcases hr with rfl | rfl | _ <;> omega)]
      rcases hr with rfl | rfl | hr70
      · exact hInvD.reg67.trans h67.symm
      · exact hInvD.reg68.trans h68.symm
      · exact (hMidRegs r hr70).trans (by simp [s0, Function.update_of_ne (show r ≠ 19 by omega)]),
    ?_⟩
  · have h1 := hInvD.heapHi
    have h2 := hrespTerm.2.1
    have h3 := hLastSpaceLe [mid.regs 6, mid.regs 7, L, fmt.precision, mid.regs 4]
    dsimp only [ordInitLevelsSpace]; omega
  · intro a ha
    have hlo := hrespTerm.1
    exact (houtFrame a (by have := hInvD.heapLo; omega) (by have := hInvD.heapLo; omega)).trans
      (hrespTerm.2.2.1 a ha)
  · intro a ha hL' hB' hML' hMG'
    rw [houtMem_lt a (ha.trans_le hInvD.heapLo) (by rcases hL' with h | h <;> omega)
      (by rcases hB' with h | h <;> omega)]
    exact hInvD.frameBelow a ha (by rcases hL' with h | h <;> omega)
      (by rcases hB' with h | h <;> omega) hML' hMG'
  · intro i hi
    obtain ⟨hlv, hbr, hrepI, _⟩ := hCorePres i hi
    obtain ⟨_, _, hfootI, hdisjI⟩ := hInvD.cores i hi
    have hyi : yCore i = yCoreDep i hi := by simp [yCore, hi]
    refine ⟨hbr, hrepI,
      fun a ha => by
        rw [hlv, hyi] at ha
        exact ⟨(hfootI a ha).1, (hfootI a ha).2.trans_le hrespTerm.1⟩,
      fun j hj hne a ha hfj => by
        have hyj : yCore j = yCoreDep j hj := by simp [yCore, hj]
        rw [hlv, hyi] at ha
        rw [(hCorePres j hj).1, hyj] at hfj
        exact hdisjI j hj hne a ha hfj,
      fun a ha hft => by
        rw [hlv, hyi] at ha
        rw [houtH, houtRegs, hsT3] at hft
        have h1 := (hfootI a ha).2
        have h2 := (hfootTerm0 a hft).1
        omega⟩
  · intro j hj1 hjLt
    obtain ⟨hDGJ, hGLoJ, hGHiJ, hLenJ, hLLoJ, hLHiJ, hDisjJ⟩ := hInvD.metaLevels j hj1 hjLt.le hjLt
    have hLCell : out.mem (levelMeta + j) = mid.mem (levelMeta + j) :=
      houtMem_lt _ (by have := hInvD.heapLo; omega) (by omega) (by omega)
    have hGCell : out.mem (levelMeta + C.d + j) = mid.mem (levelMeta + C.d + j) :=
      houtMem_lt _ (by have := hInvD.heapLo; omega) (by omega) (by omega)
    refine ⟨by rw [hGCell]; exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 =>
        houtMem_lt a (by omega) (by omega) (by omega)),
      by rw [hGCell]; exact hGLoJ,
      by rw [hGCell]; exact hGHiJ.trans hrespTerm.1,
      by rw [hLCell]; exact hLenJ.congr (fun e he t ht => by
        have heLt := hDGJ.2.2.1 e he
        have hmul : e * L + L ≤ ec0 * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
        exact houtMem_lt _ (by omega) (by omega) (by omega)),
      by rw [hLCell]; exact hLLoJ,
      by rw [hLCell]; exact hLHiJ.trans hrespTerm.1,
      fun r hr => ⟨fun a ha1 ha2 hf => by
          rw [hLCell] at ha1 ha2
          have hyr : yCore r = yCoreDep r hr := by simp [yCore, hr]
          rw [(hCorePres r hr).1, hyr] at hf
          exact (hDisjJ r hr).1 a ha1 ha2 hf,
        fun a ha1 ha2 hf => by
          rw [hGCell] at ha1 ha2
          have hyr : yCore r = yCoreDep r hr := by simp [yCore, hr]
          rw [(hCorePres r hr).1, hyr] at hf
          exact (hDisjJ r hr).2 a ha1 ha2 hf⟩,
      fun a ha1 ha2 hft => by
        rw [hLCell] at ha1 ha2; rw [houtH, houtRegs, hsT3] at hft
        have := (hfootTerm0 a hft).1; omega,
      fun a ha1 ha2 hft => by
        rw [hGCell] at ha1 ha2; rw [houtH, houtRegs, hsT3] at hft
        have := (hfootTerm0 a hft).1; omega⟩
  · refine ⟨fun j hj1 hjLt => ?_, fun j₁ j₂ hj1 hlt hj2Lt => ?_⟩
    · rw [houtMem_lt (levelMeta + C.d + j) (by have := hInvD.heapLo; omega) (by omega) (by omega),
          houtMem_lt (levelMeta + j) (by have := hInvD.heapLo; omega) (by omega) (by omega)]
      exact hInvD.metaOrd.1 j hj1 hjLt.le hjLt
    · rw [houtMem_lt (levelMeta + j₁) (by have := hInvD.heapLo; omega) (by omega) (by omega),
          houtMem_lt (levelMeta + C.d + j₂) (by have := hInvD.heapLo; omega) (by omega) (by omega)]
      exact hInvD.metaOrd.2 j₁ j₂ hj1 hlt hj2Lt.le hj2Lt
  · rw [hSumFin]
    have hLoopBound :
        (∑ j ∈ Finset.range C.d, if 0 ≤ j then
            P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35
          else 0) =
        (∑ j ∈ Finset.range C.d, P.mul * T.cost (chain.scState j)) +
        (∑ j ∈ Finset.range C.d, (ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 9)) +
        26 * C.d := by
      have h1 : (∑ j ∈ Finset.range C.d,
          (P.mul * T.cost (chain.scState j) +
            (ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 9) + 26)) =
          (∑ j ∈ Finset.range C.d, P.mul * T.cost (chain.scState j)) +
          (∑ j ∈ Finset.range C.d, (ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 9)) +
          (∑ _j ∈ Finset.range C.d, 26) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h2 : (∑ _j ∈ Finset.range C.d, 26) = 26 * C.d := by
        simp [Nat.mul_comm]
      rw [← h2, ← h1]
      refine Finset.sum_congr rfl fun j _ => by simp; omega
    have hScaled :
        (∑ j ∈ Finset.range C.d, P.mul * T.cost (chain.scState j)) + lastMult * lastTool.cost (chain.G C.d) ≤
        max P.mul lastMult * chain.totalRuntime := by
      rw [hTotalRT, mul_add]
      refine Nat.add_le_add ?_ (Nat.mul_le_mul_right _ (le_max_right _ _))
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (le_max_left _ _)
    have hTermPhi : Rterm.phi (mid.regs 4) yTerm sTerm.mem = 0 := rfl
    rw [hTermPhi, add_zero] at hcTerm
    have hLastMul : lastMult * (lastTool.cost (chain.G C.d) + 1) =
        lastMult * lastTool.cost (chain.G C.d) + lastMult := by ring
    rw [hLastMul] at hcTerm
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hcLoop
    rw [hLoopBound] at hcLoop
    dsimp only [ordInitLevelsFixed]
    omega

end MinCostFlow.MinRatio
