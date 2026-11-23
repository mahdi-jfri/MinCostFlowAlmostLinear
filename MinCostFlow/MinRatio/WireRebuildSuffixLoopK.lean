module

public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKBase
import WordRAM.Tactic

/-!
# K-contract ordered suffix rebuild loop execution (`WireRebuildSuffixLoopK`)

Proves `ordRebuildSuffixProgramKStore_runs`: iterates `ordRebuildLevelBodyKStore` over
`[first, d)` and `rebuildTerminalRuntimeStep` at level `d`, maintaining rebuilt ordered
sparse-core representations, `levelMeta` (`levelLens` + `levelGraphs`) pointers, disjoint
footprints, and exact `Rcore.phi` potential accounting.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section SuffixLoopK

/-- Full K-contract suffix rebuild loop theorem (`first ≤ d`), tracking:
- rebuilt ordered sparse-core levels `[first, d)` with pairwise-disjoint footprints in `[heapFloor, ret)`
  and exact `Rcore.phi` potential accounting;
- updated `levelLens[first + 1 .. d - 1]` pointers into `[heapFloor, ret)`;
- terminal level `d` installed at `(handleBase + d, branchBase + d)` via `rebuildTerminalRuntimeStep`;
- exact memory frame below `heapFloor` outside the modified descriptor and `levelLens` cells. -/
theorem ordRebuildSuffixProgramKStore_runs
    {w L capExp init coreLenProc edgeProc signExt mul intDiv copy lastInit
      first handleBase branchBase lvlMTable levelLens heapFloor lastMul stretchPrec
      vc0 ec0 ordWords0 : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {LT : LastLevelTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ} {opLast : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (next : ChainState T CP)
    (levelSpace levelCost : ℕ → ℕ) (lastSpace : ℕ)
    (hFirstLe : first ≤ CP.d)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hdW : CP.d < 2 ^ w) (hkPos : 0 < CP.k) (hkW : CP.k < 2 ^ w) (hNW : next.N₀ < 2 ^ w)
    (hw9 : 9 < 2 ^ w)
    (hReg1 : st.regs 1 = CP.k) (hReg4 : heapFloor ≤ st.regs 4)
    (hReg20 : st.regs 20 = first) (hReg21 : st.regs 21 = CP.d)
    (hReg51 : st.regs 51 = handleBase + first) (hReg52 : st.regs 52 = branchBase + first)
    (hReg56 : st.regs 56 = next.N₀) (hReg57 : st.regs 57 = lvlMTable)
    (hReg58 : st.regs 58 = levelLens) (hReg67 : st.regs 67 = L) (hReg68 : st.regs 68 = fmt.precision)
    (hhEnd : handleBase + CP.d < heapFloor) (hbEnd : branchBase + CP.d < heapFloor)
    (hMEnd : lvlMTable + CP.d ≤ heapFloor) (hLEnd : levelLens + 2 * CP.d ≤ heapFloor)
    (hSepHB : handleBase + CP.d < branchBase ∨ branchBase + CP.d < handleBase)
    (hSepHM : handleBase + CP.d < lvlMTable ∨ lvlMTable + CP.d ≤ handleBase)
    (hSepBM : branchBase + CP.d < lvlMTable ∨ lvlMTable + CP.d ≤ branchBase)
    (hSepHL : handleBase + CP.d < levelLens ∨ levelLens + 2 * CP.d ≤ handleBase)
    (hSepBL : branchBase + CP.d < levelLens ∨ levelLens + 2 * CP.d ≤ branchBase)
    (hSepML : lvlMTable + CP.d ≤ levelLens ∨ levelLens + 2 * CP.d ≤ lvlMTable)
    (hLvlM : ∀ j, first ≤ j → j < CP.d → st.mem (lvlMTable + j) = next.lvlM j)
    (hG0 : DynGraphAt st.mem (st.regs 6) vc0 ec0 (next.G first))
    (hLen0 : EdgeValuesAt st.mem (st.regs 7) 4 L fmt.precision (next.G first).E
      (next.toTreeChain.chainLen next.ℓ first))
    (hGrad0 : st.regs 8 = st.regs 7)
    (hOrd0 : first < CP.d →
      OrdListAt st.mem (st.regs 9) (next.levelOrd first) ordWords0 ∧
      (∀ j < ordWords0, st.mem (st.regs 9 + j) < 2 ^ w) ∧
      st.regs 9 + ordWords0 ≤ st.regs 4)
    (hG0End : st.regs 6 + dynGraphSize vc0 ec0 ≤ st.regs 4)
    (hLen0End : st.regs 7 + ec0 * L ≤ st.regs 4)
    (hG0Disj : ∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vc0 ec0 →
      (a < handleBase + first ∨ handleBase + CP.d < a) ∧
      (a < branchBase + first ∨ branchBase + CP.d < a) ∧
      (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))
    (hLen0Disj : ∀ a, st.regs 7 ≤ a → a < st.regs 7 + ec0 * L →
      (a < handleBase + first ∨ handleBase + CP.d < a) ∧
      (a < branchBase + first ∨ branchBase + CP.d < a) ∧
      (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hCoreImpl : ∀ j, first ≤ j → j < CP.d → ∀ vc ec,
      Rcore.Implements w p init op
        (sparseCoreOrdMachineContractK fmt L T (next.G j) CP.k (next.lvlM j) next.N₀
          vc ec capExp P (allocation j)))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hLastImpl : ∀ vc ec,
      (LastLevelProgram.lastLevelRepresentation vc ec 4 L fmt.precision (next.G CP.d).E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L LT (next.G CP.d) vc ec lastMul stretchPrec lastAlloc))
    (hModelLevel : ∀ j, first ≤ j → j < CP.d →
      let Gj := next.G j
      let ℓj := next.toTreeChain.chainLen next.ℓ j
      next.scState j = T.initOrd CP.k (next.lvlM j) next.N₀ Gj
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (next.levelOrd j) ∧
      next.G (j + 1) = T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0 ∧
      (next.G j).m ≤ next.lvlM j ∧ (next.G j).n ≤ next.N₀ ∧
      next.lvlM j < 2 ^ w ∧ (next.lvlM j + next.N₀ + 2) ^ P.wordExp * (L + 1) < 2 ^ w ∧
      IsRotationOrder (next.G j) (next.levelOrd j) ∧
      (∀ e ∈ (next.G j).E, 0 < ℓj e) ∧
      (next.G (j + 1)).E ⊆ (next.G j).E ∧
      (∀ e ∈ (next.G (j + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          next.toTreeChain.chainLen next.ℓ (j + 1) e))
    (hModelLast :
      (next.lastK, next.lastLSFs) = LT.build (next.G CP.d) (next.toTreeChain.chainLen next.ℓ CP.d) ∧
      next.lastBran = 0 ∧
      LT.build (next.G CP.d) (fun e => if e ∈ (next.G CP.d).E then
        next.toTreeChain.chainLen next.ℓ CP.d e else 0) =
        LT.build (next.G CP.d) (next.toTreeChain.chainLen next.ℓ CP.d) ∧
      (∀ e ∈ (next.G CP.d).E, 0 < next.toTreeChain.chainLen next.ℓ CP.d e) ∧
      (∀ e ∈ (next.G CP.d).E,
        2 * (2 : ℝ) ^ stretchPrec *
          lastLevelStretchBound (next.G CP.d) (next.toTreeChain.chainLen next.ℓ CP.d) e <
          Num.capacity 4 L))
    (hLevelRoom : ∀ j, first ≤ j → j < CP.d → ∀ vc ec gBase lBase oBase oWords h,
      gBase + dynGraphSize vc ec ≤ h → lBase + ec * L ≤ h → oBase + oWords ≤ h →
      (j = first → oWords = ordWords0) →
      (first < j → oWords ≤ ordRotWords (chainLevelOrdAbs next (j - 1)) 0) →
      heapFloor ≤ h → h ≤ st.regs 4 + (Finset.Ico first j).sum levelSpace →
      h + allocation j 6 [gBase, lBase, lBase, oBase, CP.k, next.lvlM j, next.N₀, h] + 1 < 2 ^ w ∧
      (∀ ret0, h ≤ ret0 →
        ret0 ≤ h + allocation j 6 [gBase, lBase, lBase, oBase, CP.k, next.lvlM j, next.N₀, h] →
        (∀ m1 h1 rawGraph vcH ecH,
          DynGraphAt m1 rawGraph vcH ecH (next.G (j + 1)) → ret0 ≤ h1 → h1 ≤ ret0 + 1 →
          rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ h1 + dynGraphSize vcH ecH + 5 < 2 ^ w ∧
          allocation j 6 [gBase, lBase, lBase, oBase, CP.k, next.lvlM j, next.N₀, h] +
            7 + dynGraphSize vcH ecH + ecH * L +
            (next.G (j + 1)).m *
              wireCoreLenEdgeSpace (max L (L + (capExp + sparseCoreReadout2LimbConst) *
                (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1))) +
            ordRotWords (chainLevelOrdAbs next j) 0 ≤ levelSpace j) ∧
        (∀ m2 (vcH : ℕ) ecH vcF ecF h2 h3 Lw,
          (∃ m1 rawG, DynGraphAt m1 rawG vcH ecH (next.G (j + 1))) →
          LSFAt m2 h2 vcF ecF 4 Lw fmt.precision (next.G j).E (T.lsfs (next.scState j) 0) →
          Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1) →
          ret0 ≤ h2 → h2 ≤ ret0 + 1 + dynGraphSize vcH ecH → h2 ≤ h3 → h3 ≤ h2 + 5 →
          m2 (h2 + 3) + 2 ≤ h3 ∧
          (∀ e ∈ (next.G (j + 1)).E, m2 (m2 (h2 + 3)) + e * Lw + Lw ≤ h3) ∧
          (∀ e ∈ (next.G (j + 1)).E, m2 (m2 (h2 + 3) + 1) + e * Lw + Lw ≤ h3) ∧
          h3 + ecH * L + (next.G (j + 1)).m * wireCoreLenEdgeSpace (max L Lw) +
            (1 + ordRotWords (chainLevelOrdAbs next j) 0) < 2 ^ w)))
    (hOrd5Bounds : ∀ j, first ≤ j → j + 1 < CP.d → ∀ m oPtr oWords h,
      OrdListAt m oPtr (next.levelOrd (j + 1)) oWords →
      oWords ≤ ordRotWords (chainLevelOrdAbs next j) 0 →
      ZeroFrom m h → heapFloor ≤ h →
      (∀ a, oPtr ≤ a → a < oPtr + oWords →
        a ≠ levelLens + (j + 1) ∧ a ≠ levelLens + CP.d + (j + 1)) ∧
      oPtr + oWords ≤ h ∧ (∀ t < oWords, m (oPtr + t) < 2 ^ w))
    (hLevelCost : ∀ j, first ≤ j → j < CP.d → ∀ m gPtr vcH ecH oWords,
      DynGraphAt m gPtr vcH ecH (next.G (j + 1)) →
      (j = first → oWords = ordWords0) →
      (first < j → oWords ≤ ordRotWords (chainLevelOrdAbs next (j - 1)) 0) →
      P.mul * (T.cost (next.scState j) + (next.G j).n + (next.G j).m + oWords + 1) +
        P.mul * (ordRotWords (chainLevelOrdAbs next j) 0 + 1) *
          SparseCore.bundleLogFactor (next.lvlM j) next.N₀ +
        2 * P.readout + 17 * dynGraphSize vcH ecH +
        (next.G (j + 1)).m *
          (wireCoreLenEdgeCost (max L (L + (capExp + sparseCoreReadout2LimbConst) *
            (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1))) + 30) +
        265 ≤ levelCost j)
    (hLastRoom : ∀ vc ec gBase lBase h,
      gBase + dynGraphSize vc ec ≤ h → lBase + ec * L ≤ h → heapFloor ≤ h →
      h ≤ st.regs 4 + (Finset.Ico first CP.d).sum levelSpace →
      h + lastAlloc 1 [gBase, lBase, L, fmt.precision, h] < 2 ^ w ∧
      lastAlloc 1 [gBase, lBase, L, fmt.precision, h] ≤ lastSpace)
    (hTok0 : Rcore.τ) :
    ∃ (out : State) (cost vcLast ecLast termTok : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (ordRebuildSuffixProgramKStore init (op 3) (op 2) coreLenProc (op 5) lastInit)
        st .normal out cost ∧
      st.regs 4 ≤ out.regs 4 ∧
      out.regs 4 ≤ st.regs 4 + (Finset.Ico first CP.d).sum levelSpace + lastSpace ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ j, first ≤ j → j < CP.d →
        out.mem (branchBase + j) = next.bran j ∧
        heapFloor ≤ out.mem (handleBase + j) ∧ out.mem (handleBase + j) ≤ out.regs 4 ∧
        Rcore.rep (out.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok j) out.mem ∧
        (∀ a, Rcore.foot (out.mem (handleBase + j)) (coreTok j) a → heapFloor ≤ a ∧ a < out.regs 4)) ∧
      (∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (out.mem (handleBase + j₁)) (coreTok j₁) a →
          ¬ Rcore.foot (out.mem (handleBase + j₂)) (coreTok j₂) a) ∧
      (∀ j, first + 1 ≤ j → j < CP.d →
        ∃ vc_j ec_j,
          DynGraphAt out.mem (out.mem (levelLens + CP.d + j)) vc_j ec_j (next.G j) ∧
          heapFloor ≤ out.mem (levelLens + CP.d + j) ∧
          out.mem (levelLens + CP.d + j) + dynGraphSize vc_j ec_j ≤ out.regs 4 ∧
          EdgeValuesAt out.mem (out.mem (levelLens + j)) 4 L fmt.precision (next.G j).E
            (next.toTreeChain.chainLen next.ℓ j) ∧
          heapFloor ≤ out.mem (levelLens + j) ∧
          out.mem (levelLens + j) + ec_j * L ≤ out.regs 4 ∧
          (∀ r, first ≤ r → r < CP.d →
            (∀ a, out.mem (levelLens + j) ≤ a → a < out.mem (levelLens + j) + ec_j * L →
              ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a) ∧
            (∀ a, out.mem (levelLens + CP.d + j) ≤ a →
              a < out.mem (levelLens + CP.d + j) + dynGraphSize vc_j ec_j →
              ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a)) ∧
          (∀ a, out.mem (levelLens + j) ≤ a → a < out.mem (levelLens + j) + ec_j * L →
            ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L fmt.precision (next.G CP.d).E).foot
              (out.mem (handleBase + CP.d)) termTok a) ∧
          (∀ a, out.mem (levelLens + CP.d + j) ≤ a →
            a < out.mem (levelLens + CP.d + j) + dynGraphSize vc_j ec_j →
            ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L fmt.precision (next.G CP.d).E).foot
              (out.mem (handleBase + CP.d)) termTok a)) ∧
      out.mem (branchBase + CP.d) = next.lastBran ∧
      heapFloor ≤ out.mem (handleBase + CP.d) ∧
      (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L fmt.precision (next.G CP.d).E).rep
        (out.mem (handleBase + CP.d)) (next.lastK, next.lastLSFs) termTok out.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L fmt.precision (next.G CP.d).E).foot
        (out.mem (handleBase + CP.d)) termTok a → heapFloor ≤ a ∧ a < out.regs 4) ∧
      (∀ j, first ≤ j → j < CP.d → ∀ a,
        (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L fmt.precision (next.G CP.d).E).foot
          (out.mem (handleBase + CP.d)) termTok a →
        ¬ Rcore.foot (out.mem (handleBase + j)) (coreTok j) a) ∧
      (∀ a < heapFloor,
        (a < handleBase + first ∨ handleBase + CP.d < a) →
        (a < branchBase + first ∨ branchBase + CP.d < a) →
        ((a < levelLens + (first + 1) ∨ levelLens + CP.d ≤ a) ∧
         (a < levelLens + CP.d + (first + 1) ∨ levelLens + 2 * CP.d ≤ a)) →
        out.mem a = st.mem a) ∧
      cost + (Finset.Ico first CP.d).sum
          (fun j => Rcore.phi (out.mem (handleBase + j)) (coreTok j) out.mem) ≤
        (Finset.Ico first CP.d).sum (fun j => levelCost j + 9) +
          lastMul * (LT.cost (next.G CP.d) + 1) + 28 := by
  have hwne0 : w ≠ 0 := by intro h; subst h; omega
  have hSepHB_ne (j₁ j₂ : ℕ) (h1 : j₁ ≤ CP.d) (h2 : j₂ ≤ CP.d) :
      handleBase + j₁ ≠ branchBase + j₂ := by
    rcases hSepHB with h | h <;> omega
  have hSepHL_ne (j₁ j₂ : ℕ) (h1 : j₁ ≤ CP.d) (h2 : j₂ < 2 * CP.d) :
      handleBase + j₁ ≠ levelLens + j₂ := by
    rcases hSepHL with h | h <;> omega
  have hSepBL_ne (j₁ j₂ : ℕ) (h1 : j₁ ≤ CP.d) (h2 : j₂ < 2 * CP.d) :
      branchBase + j₁ ≠ levelLens + j₂ := by
    rcases hSepBL with h | h <;> omega
  have hMDisjH (j : ℕ) (hj : j < CP.d) :
      lvlMTable + j < handleBase + first ∨ handleBase + CP.d < lvlMTable + j := by
    rcases hSepHM with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hMDisjB (j : ℕ) (hj : j < CP.d) :
      lvlMTable + j < branchBase + first ∨ branchBase + CP.d < lvlMTable + j := by
    rcases hSepBM with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hMDisjL (j : ℕ) (hj : j < CP.d) :
      (lvlMTable + j < levelLens + (first + 1) ∨ levelLens + CP.d ≤ lvlMTable + j) ∧
      (lvlMTable + j < levelLens + CP.d + (first + 1) ∨ levelLens + 2 * CP.d ≤ lvlMTable + j) := by
    rcases hSepML with h | h
    · exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
  clear hSepHB hSepHM hSepBM hSepHL hSepBL hSepML
  let Inv := SuffixLoopInv (w := w) (L := L) (first := first) (handleBase := handleBase)
    (branchBase := branchBase) (lvlMTable := lvlMTable) (levelLens := levelLens)
    (heapFloor := heapFloor) (ordWords0 := ordWords0) (fmt := fmt) Rcore next levelSpace st
  have hInv0 : Inv first { st with regs := Function.update st.regs 19 first } 0 :=
    { r19 := by simp, r20 := by simp [hReg20], r21 := by simp [hReg21], r1 := by simp [hReg1],
      r56 := by simp [hReg56], r57 := by simp [hReg57], r58 := by simp [hReg58],
      r67 := by simp [hReg67], r68 := by simp [hReg68], r51 := by simp [hReg51],
      r52 := by simp [hReg52], heapGe := by simp, heapLe := by simp, hz := by simpa using hz0,
      curTables := ⟨vc0, ec0, ordWords0, by simpa using hG0, by simpa using hLen0, by simp [hGrad0],
        fun hlt => by
          obtain ⟨hO, hOW, hOEnd⟩ := hOrd0 hlt
          exact ⟨by simpa using hO, by simpa using hOW, by simpa using hOEnd, fun _ => rfl, fun h => by omega⟩,
        by simpa using hG0End, by simpa using hLen0End,
        fun _ => ⟨by simpa using hG0Disj, by simpa using hLen0Disj⟩, fun h => by omega⟩,
      cores := ⟨fun _ => hTok0, fun _ h1 h2 => by omega, fun _ _ h1 h2 => by omega,
        fun _ h1 h2 => by omega, by simp⟩,
      frame := fun _ _ _ _ _ => rfl }
  obtain ⟨mid, cLoop, potMid, rLoop, hInvMid, hcLoop⟩ :=
    forRange19_runs_with_pot (w := w) (p := p) (ω := ω) (st := st) (Inv := Inv) levelCost 0
      hFirstLe (by omega) hdW hReg20 hInv0
      (fun _ _ _ _ _ h => h.r19) (fun _ _ _ _ _ h => h.r21)
      (fun i s pot hi hlt hInv => by
        obtain ⟨vc, ec, oWords, hGS, hLenS, hGradS, hOrdS, hGEndS, hLenEndS, hFirstDisj, hGtFloor⟩ :=
          hInv.curTables
        obtain ⟨tok, hTokRep, hTokDisj, hLensS, hPotEq⟩ := hInv.cores
        obtain ⟨hO, hOW, hOEnd, hOFirst, hOGt⟩ := hOrdS hlt
        obtain ⟨hScEq, hGSucc, hBrEq, hUpdEq, hmLe, hnLe, hMiW, hWordExp, hRot, hPosI,
          hSubI, hFitsI⟩ := hModelLevel i hi hlt
        have hHeapGe : heapFloor ≤ s.regs 4 := hReg4.trans hInv.heapGe
        have hMCell : s.mem (lvlMTable + i) = next.lvlM i := by
          rw [hInv.frame (lvlMTable + i) (by omega) (hMDisjH i hlt) (hMDisjB i hlt) (hMDisjL i hlt)]
          exact hLvlM i hi hlt
        obtain ⟨hInitRoom, hTailRoomRaw⟩ :=
          hLevelRoom i hi hlt vc ec (s.regs 6) (s.regs 7) (s.regs 9) oWords (s.regs 4)
            hGEndS hLenEndS hOEnd hOFirst hOGt hHeapGe hInv.heapLe
        have hDisjG : ∀ a, s.regs 6 ≤ a → a < s.regs 6 + dynGraphSize vc ec →
            a ≠ handleBase + i ∧ a ≠ branchBase + i := fun a ha1 ha2 => by
          by_cases hif : i = first
          · subst hif; obtain ⟨h1, h2, _⟩ := (hFirstDisj rfl).1 a ha1 ha2; omega
          · have := (hGtFloor (by omega)).1; omega
        have hDisjLen : ∀ a, s.regs 7 ≤ a → a < s.regs 7 + ec * L →
            a ≠ handleBase + i ∧ a ≠ branchBase + i := fun a ha1 ha2 => by
          by_cases hif : i = first
          · subst hif; obtain ⟨h1, h2, _⟩ := (hFirstDisj rfl).2 a ha1 ha2; omega
          · have := (hGtFloor (by omega)).2; omega
        have hAbsEq :
            ({ st := T.initOrd CP.k (next.lvlM i) next.N₀ (next.G i)
                (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
                (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
                (next.levelOrd i),
               G := next.G i, ord := next.levelOrd i, n := 0 } : SparseCoreOrdAbs T) =
            chainLevelOrdAbs next i := by
          unfold chainLevelOrdAbs; congr 1
          · exact hScEq.symm
          · exact hUpdEq.symm
        have hCoreLenFits' : ∀ e ∈ (T.S (T.initOrd CP.k (next.lvlM i) next.N₀ (next.G i)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (next.levelOrd i)) 0).E,
            ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
              coreLen (T.lsfs (T.initOrd CP.k (next.lvlM i) next.N₀ (next.G i)
                (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
                (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
                (next.levelOrd i)) 0) (next.toTreeChain.chainLen next.ℓ i) e := by
          intro e he
          rw [← hScEq, ← hGSucc] at he
          rw [← hScEq]
          have hCL : coreLen (T.lsfs (next.scState i) 0) (next.toTreeChain.chainLen next.ℓ i) e =
              next.toTreeChain.chainLen next.ℓ (i + 1) e := by
            simp only [TreeChain.chainLen, ChainState.toTreeChain, TreeChain.activeLSF, hlt,
              ↓reduceIte, hBrEq]
          rw [hCL]
          exact hFitsI e he
        obtain ⟨s1, vcH, ecH, nextOrdWords, Lw, c1, y1, r1, hLwLe, hs1_h, hs1_b, hs1_19,
            hs1_51, hs1_52, hrep1, hH1, hLen1, hGrad1, hOrd1, hOrdLe1, h6Lo1, hHEnd1, h6Disj1,
            h7Lo1, hLenEnd1, h7Disj1, h4Lo1, h4Hi1, hz1, hs1_frame, hs1_footIn, hs1_regs, hc1⟩ :=
          ordRebuildLevelBodyK_runs (ω := ω) (st := s)
            (next.toTreeChain.chainLen next.ℓ i) (next.toTreeChain.chainLen next.ℓ i)
            (next.levelOrd i) hFour (hCoreImpl i hi hlt vc ec) hCoreLenProc hEdgeProc
            hSign hMul hDiv hCopy rfl rfl hGradS rfl rfl hInv.r1 hInv.r56 hInv.r57 hInv.r19
            hInv.r51 hInv.r52 hInv.r67 hMCell (by omega) hkPos hkW hMiW hNW hw9 hWordExp
            (hSepHB_ne i i (le_of_lt hlt) (le_of_lt hlt)) (by omega) (by omega) (by omega) (by omega)
            hGS hmLe hnLe hGEndS hDisjG
            hLenEndS hLenEndS hDisjLen hO hOEnd hOW hRot hLenS hLenS hPosI hInv.hz hInitRoom
            (by dsimp only; rw [← hScEq, ← hGSucc]; exact hSubI) hCoreLenFits'
            (fun ret0 hlo hhi => by
              obtain ⟨hA, hB⟩ := hTailRoomRaw ret0 hlo hhi
              refine ⟨fun m1 h1 rawGraph vcH ecH hDG hh1 hh2 => ?_,
                fun m2 vcH ecH vcF ecF h2 h3 Lw hDGEx hL hLw hh2 hh2Hi hh3 hh4 => ?_⟩
              · rw [← hScEq, ← hGSucc] at hDG
                obtain ⟨h1', h2', _⟩ := hA m1 h1 rawGraph vcH ecH hDG hh1 hh2
                exact ⟨h1', h2'⟩
              · rw [← hScEq] at hL
                rw [← hScEq, ← hGSucc] at hDGEx
                obtain ⟨h1', h2', h3', h4'⟩ := hB m2 vcH ecH vcF ecF h2 h3 Lw hDGEx hL hLw hh2 hh2Hi hh3 hh4
                refine ⟨h1', ?_, ?_, ?_⟩
                · rw [← hScEq, ← hGSucc]; exact h2'
                · rw [← hScEq, ← hGSucc]; exact h3'
                · have hAbsI :
                      ({ st := next.scState i, G := next.G i, ord := next.levelOrd i, n := 0 } :
                        SparseCoreOrdAbs T) = chainLevelOrdAbs next i := by
                    unfold chainLevelOrdAbs; congr 1; exact hUpdEq.symm
                  rw [← hScEq, ← hGSucc, hAbsI]; exact h4')
        rw [hAbsEq] at hrep1 hOrdLe1 h4Hi1 hc1
        have hHEq : T.S (T.initOrd CP.k (next.lvlM i) next.N₀ (next.G i)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (next.levelOrd i)) 0 = next.G (i + 1) := by rw [← hScEq, ← hGSucc]
        have hLenEq : coreLen (T.lsfs (T.initOrd CP.k (next.lvlM i) next.N₀ (next.G i)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (next.levelOrd i)) 0) (next.toTreeChain.chainLen next.ℓ i) =
            next.toTreeChain.chainLen next.ℓ (i + 1) := by
          rw [← hScEq]; simp only [TreeChain.chainLen, ChainState.toTreeChain, TreeChain.activeLSF,
            hlt, ↓reduceIte, hBrEq]
        have hOrdEq : T.rot (T.initOrd CP.k (next.lvlM i) next.N₀ (next.G i)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (fun e => if e ∈ (next.G i).E then next.toTreeChain.chainLen next.ℓ i e else 0)
            (next.levelOrd i)) 0 = next.levelOrd (i + 1) := by
          rw [← hScEq]
          simp only [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, Nat.add_eq_zero_iff,
            one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, hBrEq]
        rw [hHEq] at hH1 hLen1
        dsimp only [chainLevelOrdAbs] at hc1 h4Hi1
        rw [← hGSucc] at hc1 h4Hi1
        rw [hLenEq] at hLen1
        rw [hOrdEq] at hOrd1
        have hs1_21 : s1.regs 21 = CP.d := (hs1_regs 21 (by omega)).trans hInv.r21
        have hs1_58 : s1.regs 58 = levelLens := (hs1_regs 58 (by omega)).trans hInv.r58
        let condStmt : Stmt :=
          .cond (.bin .lt (.bin .add (.reg 19) (.const 1)) (.reg 21))
            (.store (.bin .add (.reg 58) (.bin .add (.reg 19) (.const 1))) (.reg 7) ;;
             .store (.bin .add (.bin .add (.reg 58) (.reg 21)) (.bin .add (.reg 19) (.const 1))) (.reg 6))
            .nop
        have hCondStep : ∃ s2 c2,
            Runs w p ω condStmt s1 .normal s2 c2 ∧ c2 ≤ 25 ∧
            s2.regs = s1.regs ∧
            (i + 1 < CP.d → s2.mem (levelLens + (i + 1)) = s1.regs 7 ∧
              s2.mem (levelLens + CP.d + (i + 1)) = s1.regs 6) ∧
            (∀ a, (i + 1 < CP.d → a ≠ levelLens + (i + 1) ∧ a ≠ levelLens + CP.d + (i + 1)) →
              s2.mem a = s1.mem a) := by
          by_cases hNextLt : i + 1 < CP.d
          · let s2a := { s1 with mem := Function.update s1.mem (levelLens + (i + 1)) (s1.regs 7) }
            let s2 := { s2a with mem := Function.update s2a.mem (levelLens + CP.d + (i + 1)) (s1.regs 6) }
            have rSt1 : Runs w p ω (.store (.bin .add (.reg 58) (.bin .add (.reg 19) (.const 1))) (.reg 7))
                s1 .normal s2a 7 :=
              runs_store_iff.mpr ⟨levelLens + (i + 1), s1.regs 7,
                by simp [Expr.eval, BinOp.eval, hs1_58, hs1_19, show 1 < 2 ^ w by omega,
                  show i + 1 < 2 ^ w by omega, show levelLens + (i + 1) < 2 ^ w by omega],
                by simp [Expr.eval], rfl, rfl, rfl⟩
            have rSt2 : Runs w p ω
                (.store (.bin .add (.bin .add (.reg 58) (.reg 21)) (.bin .add (.reg 19) (.const 1))) (.reg 6))
                s2a .normal s2 9 :=
              runs_store_iff.mpr ⟨levelLens + CP.d + (i + 1), s1.regs 6,
                by simp [Expr.eval, BinOp.eval, s2a, hs1_58, hs1_21, hs1_19, show 1 < 2 ^ w by omega,
                  show i + 1 < 2 ^ w by omega, show levelLens + CP.d < 2 ^ w by omega,
                  show levelLens + CP.d + (i + 1) < 2 ^ w by omega],
                by simp [Expr.eval, s2a], rfl, rfl, rfl⟩
            have rC : Runs w p ω condStmt s1 .normal s2 23 :=
              runs_cond_iff.mpr ⟨1, 7 + 9 + 1,
                by simp [Expr.eval, BinOp.eval, hs1_19, hs1_21, show 1 < 2 ^ w by omega,
                  show i + 1 < 2 ^ w by omega, hNextLt],
                by simpa using runs_seq_iff.mpr (Or.inr ⟨s2a, 7, 9, rSt1, rSt2, rfl⟩),
                by simp [Expr.size]⟩
            exact ⟨s2, 23, rC, by omega, rfl,
              fun _ => ⟨by simp [s2, s2a, Function.update_of_ne (by omega : levelLens + (i + 1) ≠ levelLens + CP.d + (i + 1))],
                by simp [s2]⟩,
              fun a hne => by
                obtain ⟨h1, h2⟩ := hne hNextLt
                simp [s2, s2a, Function.update_of_ne h1, Function.update_of_ne h2]⟩
          · have rC : Runs w p ω condStmt s1 .normal s1 7 :=
              runs_cond_iff.mpr ⟨0, 1,
                by simp [Expr.eval, BinOp.eval, hs1_19, hs1_21, show 1 < 2 ^ w by omega,
                  show i + 1 < 2 ^ w by omega, hNextLt],
                by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
            exact ⟨s1, 7, rC, by omega, rfl, fun h => absurd h hNextLt, fun _ _ => rfl⟩
        obtain ⟨s2, c2, r2, hc2, hs2_regs, hs2_lenCell, hs2_memNe⟩ := hCondStep
        have hs2_geFloor (a : ℕ) (ha : heapFloor ≤ a) : s2.mem a = s1.mem a :=
          hs2_memNe a (fun _ => ⟨by omega, by omega⟩)
        have hs2_ltFloor (a : ℕ) (ha : a < heapFloor) (h1 : a ≠ handleBase + i)
            (h2 : a ≠ branchBase + i)
            (h3 : i + 1 < CP.d → a ≠ levelLens + (i + 1) ∧ a ≠ levelLens + CP.d + (i + 1)) :
            s2.mem a = s.mem a :=
          (hs2_memNe a h3).trans (hs1_frame a (by omega) h1 h2)
        have hhi_i : s2.mem (handleBase + i) = s.regs 4 :=
          (hs2_memNe _ (fun hlt' => ⟨hSepHL_ne i (i + 1) (le_of_lt hlt) (by omega),
            by rw [Nat.add_assoc]; exact hSepHL_ne i (CP.d + (i + 1)) (le_of_lt hlt) (by omega)⟩)).trans hs1_h
        have hbi_i : s2.mem (branchBase + i) = 0 :=
          (hs2_memNe _ (fun hlt' => ⟨hSepBL_ne i (i + 1) (le_of_lt hlt) (by omega),
            by rw [Nat.add_assoc]; exact hSepBL_ne i (CP.d + (i + 1)) (le_of_lt hlt) (by omega)⟩)).trans hs1_b
        have hlocY1 := hCoreLocal (s.regs 4) (chainLevelOrdAbs next i) y1 s1.mem s2.mem
          (fun a ha => (hs2_geFloor a (hHeapGe.trans (hs1_footIn a ha).1)).symm)
        have hPrevPres (j : ℕ) (hj1 : first ≤ j) (hj2 : j < i) :
            s2.mem (handleBase + j) = s.mem (handleBase + j) ∧
            s2.mem (branchBase + j) = s.mem (branchBase + j) ∧
            Rcore.rep (s.mem (handleBase + j)) (chainLevelOrdAbs next j) (tok j) s2.mem ∧
            Rcore.phi (s.mem (handleBase + j)) (tok j) s2.mem =
              Rcore.phi (s.mem (handleBase + j)) (tok j) s.mem := by
          obtain ⟨_, _, _, hrepJ, hfootJ⟩ := hTokRep j hj1 hj2
          have hlocJ := hCoreLocal (s.mem (handleBase + j)) (chainLevelOrdAbs next j) (tok j)
            s.mem s2.mem (fun a ha => by
              have hfa := hfootJ a ha
              exact ((hs2_geFloor a hfa.1).trans (hs1_frame a hfa.2 (by omega) (by omega))).symm)
          exact ⟨hs2_ltFloor _ (by omega) (by omega) (hSepHB_ne j i (by omega) (by omega))
              (fun hlt' => ⟨hSepHL_ne j (i + 1) (by omega) (by omega),
                by rw [Nat.add_assoc]; exact hSepHL_ne j (CP.d + (i + 1)) (by omega) (by omega)⟩),
            hs2_ltFloor _ (by omega) ((hSepHB_ne i j (by omega) (by omega)).symm) (by omega)
              (fun hlt' => ⟨hSepBL_ne j (i + 1) (by omega) (by omega),
                by rw [Nat.add_assoc]; exact hSepBL_ne j (CP.d + (i + 1)) (by omega) (by omega)⟩),
            hlocJ.1 hrepJ, hlocJ.2.symm⟩
        let tok' : ℕ → Rcore.τ := fun j => if j = i then y1 else tok j
        let pot' := (Finset.Ico first (i + 1)).sum
          (fun j => Rcore.phi (s2.mem (handleBase + j)) (tok' j) s2.mem)
        have hPotSplit : pot' = pot + Rcore.phi (s.regs 4) y1 s1.mem := by
          have hIns : Finset.Ico first (i + 1) = insert i (Finset.Ico first i) := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          dsimp only [pot']
          rw [hIns, Finset.sum_insert (by simp), hPotEq]
          have hTermI : Rcore.phi (s2.mem (handleBase + i)) (tok' i) s2.mem =
              Rcore.phi (s.regs 4) y1 s1.mem := by
            simp only [tok', ↓reduceIte, hhi_i]; exact hlocY1.2.symm
          have hRest : (Finset.Ico first i).sum
              (fun j => Rcore.phi (s2.mem (handleBase + j)) (tok' j) s2.mem) =
              (Finset.Ico first i).sum
              (fun j => Rcore.phi (s.mem (handleBase + j)) (tok j) s.mem) :=
            Finset.sum_congr rfl (fun j hj => by
              obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
              have hne : j ≠ i := by omega
              obtain ⟨hhEq, _, _, hphiEq⟩ := hPrevPres j hj1 hj2
              simp only [tok', hne, ↓reduceIte, hhEq, hphiEq])
          rw [hTermI, hRest, add_comm]
        let s3 := { s2 with regs := Function.update s2.regs 19 (i + 1) }
        have hs3_r (r : ℕ) (hr : r ≠ 19) : s3.regs r = s1.regs r := by
          simp [s3, Function.update_of_ne hr, hs2_regs]
        have hInvNext : Inv (i + 1) s3 pot' :=
          { r19 := by simp [s3],
            r20 := (hs3_r 20 (by decide)).trans ((hs1_regs 20 (by omega)).trans hInv.r20),
            r21 := (hs3_r 21 (by decide)).trans hs1_21,
            r1 := (hs3_r 1 (by decide)).trans ((hs1_regs 1 (by omega)).trans hInv.r1),
            r56 := (hs3_r 56 (by decide)).trans ((hs1_regs 56 (by omega)).trans hInv.r56),
            r57 := (hs3_r 57 (by decide)).trans ((hs1_regs 57 (by omega)).trans hInv.r57),
            r58 := (hs3_r 58 (by decide)).trans hs1_58,
            r67 := (hs3_r 67 (by decide)).trans ((hs1_regs 67 (by omega)).trans hInv.r67),
            r68 := (hs3_r 68 (by decide)).trans ((hs1_regs 68 (by omega)).trans hInv.r68),
            r51 := by rw [hs3_r 51 (by decide), hs1_51]; omega,
            r52 := by rw [hs3_r 52 (by decide), hs1_52]; omega,
            heapGe := by rw [hs3_r 4 (by decide)]; exact hInv.heapGe.trans h4Lo1,
            heapLe := by
              rw [hs3_r 4 (by decide)]
              have hIns : Finset.Ico first (i + 1) = insert i (Finset.Ico first i) := by
                ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
              rw [hIns, Finset.sum_insert (by simp)]
              have hSpDom := ((hTailRoomRaw (s.regs 4) le_rfl (Nat.le_add_right _ _)).1
                s1.mem (s.regs 4) (s1.regs 6) vcH ecH hH1 le_rfl (by omega)).2.2
              dsimp only [chainLevelOrdAbs] at hSpDom
              have hMonoSp : wireCoreLenEdgeSpace (max L Lw) ≤
                  wireCoreLenEdgeSpace (max L (L + (capExp + sparseCoreReadout2LimbConst) *
                    (Nat.log 2 (next.lvlM i + next.N₀ + 2) + 1))) :=
                wireCoreLenEdgeSpace_mono (max_le_max_left L hLwLe)
              have hMulSp := Nat.mul_le_mul_left (next.G (i + 1)).m hMonoSp
              have hInvLe : s.regs 4 ≤ st.regs 4 + ∑ x ∈ Finset.Ico first i, levelSpace x := hInv.heapLe
              omega,
            hz := fun a ha => by
              rw [hs3_r 4 (by decide)] at ha
              exact (hs2_geFloor a (by omega)).trans (hz1 a ha),
            curTables := ⟨vcH, ecH, nextOrdWords,
              by rw [hs3_r 6 (by decide)]
                 exact dynGraphAt_of_agree hH1 (fun a ha1 _ => hs2_geFloor a (hHeapGe.trans (h6Lo1.trans ha1))),
              by rw [hs3_r 7 (by decide)]
                 exact hLen1.congr (fun _ _ _ _ => hs2_geFloor _ (by omega)),
              by rw [hs3_r 8 (by decide), hs3_r 7 (by decide), hGrad1],
              fun hi1Lt => by
                obtain ⟨hDisjO, hEndO, hWO⟩ :=
                  hOrd5Bounds i hi hi1Lt s1.mem (s1.regs 9) nextOrdWords (s1.regs 4)
                    hOrd1 hOrdLe1 hz1 (hHeapGe.trans h4Lo1)
                have hOrdEqMem : ∀ a, s1.regs 9 ≤ a → a < s1.regs 9 + nextOrdWords → s2.mem a = s1.mem a :=
                  fun a ha1 ha2 => hs2_memNe a (fun _ => hDisjO a ha1 ha2)
                refine ⟨by rw [hs3_r 9 (by decide)]
                           exact ordListAt_of_agree hOrd1 (fun j hj => hOrdEqMem (s1.regs 9 + j) (by omega) (by omega)),
                  fun t ht => by
                    rw [hs3_r 9 (by decide), hOrdEqMem (s1.regs 9 + t) (by omega) (by omega)]
                    exact hWO t ht,
                  by rw [hs3_r 9 (by decide), hs3_r 4 (by decide)]; exact hEndO,
                  fun h => by omega,
                  fun _ => by simpa [Nat.add_sub_cancel] using hOrdLe1⟩,
              by rw [hs3_r 6 (by decide), hs3_r 4 (by decide)]; exact hHEnd1,
              by rw [hs3_r 7 (by decide), hs3_r 4 (by decide)]; exact hLenEnd1,
              fun h => by omega,
              fun _ => ⟨by rw [hs3_r 6 (by decide)]; exact hHeapGe.trans h6Lo1,
                by rw [hs3_r 7 (by decide)]; exact hHeapGe.trans h7Lo1⟩⟩,
            cores := ⟨tok',
              fun j hj1 hj2 => by
                by_cases hjeq : j = i
                · subst hjeq
                  simp only [s3, tok', ↓reduceIte, hhi_i, hbi_i, hBrEq]
                  refine ⟨trivial, hHeapGe, by change s.regs 4 ≤ s3.regs 4; rw [hs3_r 4 (by decide)]; exact h4Lo1,
                    hlocY1.1 hrep1, fun a ha => ?_⟩
                  change heapFloor ≤ a ∧ a < s3.regs 4
                  rw [hs3_r 4 (by decide)]
                  obtain ⟨ha1, ha2⟩ := hs1_footIn a ha
                  exact ⟨hHeapGe.trans ha1, ha2⟩
                · have hjlt : j < i := by omega
                  obtain ⟨hbrJ, hhLo, hhHi, _, hfootJ⟩ := hTokRep j hj1 hjlt
                  obtain ⟨hhEq, hbEq, hrepJ2, _⟩ := hPrevPres j hj1 hjlt
                  simp only [s3, tok', hjeq, ↓reduceIte, hhEq, hbEq]
                  refine ⟨hbrJ, hhLo, by change _ ≤ s3.regs 4; rw [hs3_r 4 (by decide)]; exact hhHi.trans h4Lo1,
                    hrepJ2, fun a ha => ⟨(hfootJ a ha).1, by change a < s3.regs 4; rw [hs3_r 4 (by decide)]; exact (hfootJ a ha).2.trans_le h4Lo1⟩⟩,
              fun j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2 => by
                by_cases e1 : j₁ = i <;> by_cases e2 : j₂ = i
                · exact hne (e1.trans e2.symm)
                · subst e1
                  obtain ⟨hh2, _, _, _⟩ := hPrevPres j₂ h3 (by omega)
                  simp only [s3, tok', ↓reduceIte, e2, hhi_i, hh2] at ha1 ha2
                  have h1lo := (hs1_footIn a ha1).1
                  have h2hi := (hTokRep j₂ h3 (by omega)).2.2.2.2 a ha2
                  omega
                · subst e2
                  obtain ⟨hh1, _, _, _⟩ := hPrevPres j₁ h1 (by omega)
                  simp only [s3, tok', ↓reduceIte, e1, hhi_i, hh1] at ha1 ha2
                  have h2lo := (hs1_footIn a ha2).1
                  have h1hi := (hTokRep j₁ h1 (by omega)).2.2.2.2 a ha1
                  omega
                · obtain ⟨hh1, _, _, _⟩ := hPrevPres j₁ h1 (by omega)
                  obtain ⟨hh2, _, _, _⟩ := hPrevPres j₂ h3 (by omega)
                  simp only [s3, tok', e1, e2, ↓reduceIte, hh1, hh2] at ha1 ha2
                  exact hTokDisj j₁ j₂ h1 (by omega) h3 (by omega) hne a ha1 ha2,
              fun j hj1 hj2 hjLt => by
                by_cases hjeq : j = i + 1
                · subst hjeq
                  obtain ⟨hLC, hGC⟩ := hs2_lenCell hjLt
                  refine ⟨vcH, ecH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · rw [hGC]; exact dynGraphAt_of_agree hH1 (fun a ha1 _ => hs2_geFloor a (hHeapGe.trans (h6Lo1.trans ha1)))
                  · rw [hGC]; exact hHeapGe.trans h6Lo1
                  · rw [hGC, hs3_r 4 (by decide)]; exact hHEnd1
                  · rw [hLC]; exact hLen1.congr (fun _ _ _ _ => hs2_geFloor _ (by omega))
                  · rw [hLC]; exact hHeapGe.trans h7Lo1
                  · rw [hLC, hs3_r 4 (by decide)]; exact hLenEnd1
                  · intro r hr1 hr2
                    rw [hLC, hGC]
                    by_cases hri : r = i
                    · subst hri; simp only [s3, tok', ↓reduceIte, hhi_i]; exact ⟨h7Disj1, h6Disj1⟩
                    · obtain ⟨hhR, _, _, _⟩ := hPrevPres r hr1 (by omega)
                      simp only [s3, tok', hri, ↓reduceIte, hhR]
                      exact ⟨fun a ha1 _ hf => by have := (hTokRep r hr1 (by omega)).2.2.2.2 a hf; omega,
                        fun a ha1 _ hf => by have := (hTokRep r hr1 (by omega)).2.2.2.2 a hf; omega⟩
                · obtain ⟨vcJ, ecJ, hDGJ, hGLoJ, hGHiJ, hEvJ, hLoJ, hHiJ, hDisjJ⟩ :=
                    hLensS j hj1 (by omega) hjLt
                  have hPtrEq : s2.mem (levelLens + j) = s.mem (levelLens + j) :=
                    hs2_ltFloor _ (by omega) ((hSepHL_ne i j (by omega) (by omega)).symm)
                      ((hSepBL_ne i j (by omega) (by omega)).symm) (fun _ => ⟨by omega, by omega⟩)
                  have hGPtrEq : s2.mem (levelLens + CP.d + j) = s.mem (levelLens + CP.d + j) :=
                    hs2_ltFloor _ (by omega)
                      (Ne.symm (by rw [Nat.add_assoc]; exact hSepHL_ne i (CP.d + j) (by omega) (by omega)))
                      (Ne.symm (by rw [Nat.add_assoc]; exact hSepBL_ne i (CP.d + j) (by omega) (by omega)))
                      (fun _ => ⟨by omega, by omega⟩)
                  refine ⟨vcJ, ecJ, ?_, hGPtrEq.symm ▸ hGLoJ,
                    by rw [hGPtrEq, hs3_r 4 (by decide)]; exact hGHiJ.trans h4Lo1,
                    ?_, hPtrEq.symm ▸ hLoJ,
                    by rw [hPtrEq, hs3_r 4 (by decide)]; exact hHiJ.trans h4Lo1, ?_⟩
                  · rw [hGPtrEq]
                    exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 =>
                      (hs2_geFloor a (by omega)).trans (hs1_frame a (by omega) (by omega) (by omega)))
                  · rw [hPtrEq]
                    exact hEvJ.congr (fun e he t ht => by
                      have heLt : e < ecJ := hDGJ.2.2.1 e he
                      have hmul : e * L + L ≤ ecJ * L := by
                        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
                      exact (hs2_geFloor _ (by omega)).trans (hs1_frame _ (by omega) (by omega) (by omega)))
                  · intro r hr1 hr2
                    rw [hPtrEq, hGPtrEq]
                    by_cases hri : r = i
                    · subst hri; simp only [s3, tok', ↓reduceIte, hhi_i]
                      exact ⟨fun a _ ha2 hf => by have := (hs1_footIn a hf).1; omega,
                        fun a _ ha2 hf => by have := (hs1_footIn a hf).1; omega⟩
                    · obtain ⟨hhR, _, _, _⟩ := hPrevPres r hr1 (by omega)
                      simp only [s3, tok', hri, ↓reduceIte, hhR]
                      exact hDisjJ r hr1 (by omega),
              rfl⟩,
            frame := fun a ha h1 h2 h3 =>
              (hs2_ltFloor a ha (by omega) (by omega) (fun _ => ⟨by omega, by omega⟩)).trans
                (hInv.frame a ha h1 h2 h3) }
        have hCostI : (c1 + c2 + 1) + pot' ≤ levelCost i + pot := by
          rw [hPotSplit]
          have hDom := hLevelCost i hi hlt s1.mem (s1.regs 6) vcH ecH oWords hH1 hOFirst hOGt
          dsimp only [chainLevelOrdAbs] at hDom
          have hMonoCL : wireCoreLenEdgeCost (max L Lw) ≤
              wireCoreLenEdgeCost (max L (L + (capExp + sparseCoreReadout2LimbConst) *
                (Nat.log 2 (next.lvlM i + next.N₀ + 2) + 1))) :=
            wireCoreLenEdgeCost_mono (max_le_max_left L hLwLe)
          have hMulCL := Nat.mul_le_mul_left (next.G (i + 1)).m (Nat.add_le_add_right hMonoCL 30)
          omega
        exact ⟨s2, c1 + c2 + 1, pot',
          runs_seq_iff.mpr (Or.inr ⟨s1, c1, c2, r1, r2, rfl⟩),
          (congrFun hs2_regs 19).trans hs1_19, hInvNext, hCostI⟩)
  -- Terminal level `d` via `rebuildTerminalRuntimeStep`
  obtain ⟨vcD, ecD, _, hGD, hLenD, _, _, hGDEnd, hLenDEnd, _, _⟩ := hInvMid.curTables
  obtain ⟨tokMid, hTokMidRep, hTokMidDisj, hLensMid, hPotMidEq⟩ := hInvMid.cores
  obtain ⟨hLastMod, hLastBr, hLastAgree, hLastPos, hLastStr⟩ := hModelLast
  have hHeapGeMid : heapFloor ≤ mid.regs 4 := hReg4.trans hInvMid.heapGe
  obtain ⟨hLastRoomW, hLastSpLe⟩ :=
    hLastRoom vcD ecD (mid.regs 6) (mid.regs 7) (mid.regs 4) hGDEnd hLenDEnd hHeapGeMid hInvMid.heapLe
  obtain ⟨out, retLast, cLast, yLast, rLast, houtH, houtB, hout4, hLastRep, hzOut,
      hLastFoot, hLastFrame, hLastGe, hLastLe, hcLast⟩ :=
    wireRebuildTerminalStep_runs (ω := ω) (st := mid) (hLastImpl vcD ecD)
      rfl rfl rfl hInvMid.r67 hInvMid.r68 hLWord hPWord hFour hWidth
      (next.toTreeChain.chainLen next.ℓ CP.d) hGD hGDEnd hLenDEnd (hFour.symm ▸ hLenD)
      (by simpa [hFour] using hLastStr) hLastPos hInvMid.hz hLastRoomW
      hLastAgree hInvMid.r51 hInvMid.r52 (hSepHB_ne CP.d CP.d le_rfl le_rfl) (by omega) (by omega)
  rw [← hLastMod] at hLastRep
  have hMidCorePres (j : ℕ) (hj1 : first ≤ j) (hj2 : j < CP.d) :
      out.mem (handleBase + j) = mid.mem (handleBase + j) ∧
      out.mem (branchBase + j) = mid.mem (branchBase + j) ∧
      Rcore.rep (mid.mem (handleBase + j)) (chainLevelOrdAbs next j) (tokMid j) out.mem ∧
      Rcore.phi (mid.mem (handleBase + j)) (tokMid j) out.mem =
        Rcore.phi (mid.mem (handleBase + j)) (tokMid j) mid.mem := by
    obtain ⟨_, _, _, hrepJ, hfootJ⟩ := hTokMidRep j hj1 hj2
    have hlocJ := hCoreLocal (mid.mem (handleBase + j)) (chainLevelOrdAbs next j) (tokMid j)
      mid.mem out.mem (fun a ha => by
        have hfa := hfootJ a ha
        exact (hLastFrame a hfa.2 (by omega) (by omega)).symm)
    exact ⟨hLastFrame _ (by omega) (by omega) (hSepHB_ne j CP.d (by omega) le_rfl),
      hLastFrame _ (by omega) ((hSepHB_ne CP.d j le_rfl (by omega)).symm) (by omega),
      hlocJ.1 hrepJ, hlocJ.2.symm⟩
  refine ⟨out, cLoop + cLast + 1, vcD, ecD, yLast, tokMid,
    runs_seq_iff.mpr (Or.inr ⟨mid, cLoop, cLast, rLoop, rLast, rfl⟩),
    by rw [hout4]; exact hInvMid.heapGe.trans hLastGe,
    by rw [hout4]; have := hInvMid.heapLe; omega,
    hout4.symm ▸ hzOut, ?_, ?_, ?_, houtB.trans hLastBr.symm, houtH.symm ▸ hHeapGeMid,
    houtH.symm ▸ hLastRep,
    fun a ha => by
      rw [hout4]
      obtain ⟨ha1, ha2⟩ := hLastFoot a (houtH ▸ ha)
      exact ⟨hHeapGeMid.trans ha1, ha2⟩,
    fun j hj1 hj2 a haL haC => by
      obtain ⟨hhEq, _, _, _⟩ := hMidCorePres j hj1 hj2
      have hLlo := (hLastFoot a (houtH ▸ haL)).1
      have hChi := (hTokMidRep j hj1 hj2).2.2.2.2 a (hhEq ▸ haC)
      omega,
    fun a ha h1 h2 h3 =>
      (hLastFrame a (ha.trans_le hHeapGeMid) (by omega) (by omega)).trans (hInvMid.frame a ha h1 h2 h3),
    ?_⟩
  · intro j hj1 hj2
    obtain ⟨hbrJ, hhLo, hhHi, _, hfootJ⟩ := hTokMidRep j hj1 hj2
    obtain ⟨hhEq, hbEq, hrepJ, _⟩ := hMidCorePres j hj1 hj2
    rw [hhEq, hbEq, hout4]
    exact ⟨hbrJ, hhLo, hhHi.trans hLastGe, hrepJ,
      fun a ha => ⟨(hfootJ a ha).1, (hfootJ a ha).2.trans_le hLastGe⟩⟩
  · intro j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2
    obtain ⟨hh1, _, _, _⟩ := hMidCorePres j₁ h1 h2
    obtain ⟨hh2, _, _, _⟩ := hMidCorePres j₂ h3 h4
    exact hTokMidDisj j₁ j₂ h1 h2 h3 h4 hne a (hh1 ▸ ha1) (hh2 ▸ ha2)
  · intro j hj1 hjLt
    obtain ⟨vcJ, ecJ, hDGJ, hGLoJ, hGHiJ, hEvJ, hLoJ, hHiJ, hDisjJ⟩ :=
      hLensMid j hj1 (le_of_lt hjLt) hjLt
    have hPtrEq : out.mem (levelLens + j) = mid.mem (levelLens + j) :=
      hLastFrame _ (by omega) ((hSepHL_ne CP.d j le_rfl (by omega)).symm)
        ((hSepBL_ne CP.d j le_rfl (by omega)).symm)
    have hGPtrEq : out.mem (levelLens + CP.d + j) = mid.mem (levelLens + CP.d + j) :=
      hLastFrame _ (by omega)
        (Ne.symm (by rw [Nat.add_assoc]; exact hSepHL_ne CP.d (CP.d + j) le_rfl (by omega)))
        (Ne.symm (by rw [Nat.add_assoc]; exact hSepBL_ne CP.d (CP.d + j) le_rfl (by omega)))
    refine ⟨vcJ, ecJ, ?_, hGPtrEq.symm ▸ hGLoJ, by rw [hGPtrEq, hout4]; exact hGHiJ.trans hLastGe,
      ?_, hPtrEq.symm ▸ hLoJ, by rw [hPtrEq, hout4]; exact hHiJ.trans hLastGe,
      fun r hr1 hr2 => by
        obtain ⟨hhR, _, _, _⟩ := hMidCorePres r hr1 hr2
        rw [hPtrEq, hGPtrEq, hhR]; exact hDisjJ r hr1 hr2,
      fun a ha1 ha2 hf => by rw [hPtrEq] at ha1 ha2; have := (hLastFoot a (houtH ▸ hf)).1; omega,
      fun a ha1 ha2 hf => by rw [hGPtrEq] at ha1 ha2; have := (hLastFoot a (houtH ▸ hf)).1; omega⟩
    · rw [hGPtrEq]
      exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 => hLastFrame a (by omega) (by omega) (by omega))
    · rw [hPtrEq]
      exact hEvJ.congr (fun e he t ht => by
        have heLt : e < ecJ := hDGJ.2.2.1 e he
        have hmul : e * L + L ≤ ecJ * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
        exact hLastFrame _ (by omega) (by omega) (by omega))
  · have hPhiEq :
        (Finset.Ico first CP.d).sum (fun j => Rcore.phi (out.mem (handleBase + j)) (tokMid j) out.mem) =
        potMid := by
      rw [hPotMidEq]
      exact Finset.sum_congr rfl (fun j hj => by
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        obtain ⟨hhEq, _, _, hphiEq⟩ := hMidCorePres j hj1 hj2
        rw [hhEq, hphiEq])
    rw [hPhiEq]
    have hLastPhi : (LastLevelProgram.lastLevelRepresentation vcD ecD 4 L fmt.precision (next.G CP.d).E).phi
        (mid.regs 4) yLast out.mem = 0 := rfl
    rw [hLastPhi, add_zero] at hcLast
    omega

end SuffixLoopK

end MinCostFlow.MinRatio
