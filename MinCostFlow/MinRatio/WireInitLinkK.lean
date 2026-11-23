module

public import MinCostFlow.MinRatio.WireInitLinkLoopK
import MinCostFlow.MinRatio.InitPathTreeEdges
import Mathlib.Tactic.Ring

/-!
# Chain spanning-forest insertion into the Section 6 path tree (`WireInitLinkK`)

Composes `initLinkChainLoopK_runs` (levels `0 .. C.d - 1`) with `LastLevelProgram.readout_runs`
and `initLinkForestEdges_runs` at terminal level `C.d` to prove `initLinkChainForestsK_runs`
with exact `InitPathTreeInv`, `OrdInitChainCoresK`, space `initLinkChainSpace`, and telescoping
cost + potential bound `initLinkChainCost`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program LastLevelProgram

theorem initLinkChainForestsK_runs
    {w L depth treeConst initCore initTree bind
      treeHandle rootBase levelTable branchTable slots names slotThresholds
      edgeRecords edgeThresholds m ec0 heap linkSpace capExp capLimit vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool}
    {C : ChainParams} {P : SparseCoreOrdParams}
    {coreAlloc : ℕ → List ℕ → ℕ}
    {lvlM : ℕ → ℕ} {treeAlloc : ℕ → ℕ → List ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} {val : ℕ → PathEdgeValue} {B : ℤ}
    {recPtr thPtr : ℕ → ℕ} {extraStatic : ℕ → Prop} {xCore : ℕ → Rcore.τ} {xTerm : ℕ}
    {s0 : PathTreeState} {xTree : Rtree.τ} {slot0 name0 : ℕ → ℕ}
    (hFour : fmt.limbBits = 4)
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hcoreImpl : ∀ i < C.d,
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0
          capExp P coreAlloc) ∧
      SparseCoreReadoutFootAt fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0 capExp P
        coreAlloc Rcore p opCore)
    (hLastReadout : p.procs[opLast 0]? = some LastLevelProgram.readoutBody)
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreInput : ∀ i < C.d,
      SparseCoreOrdInput T C.k (lvlM i) N₀ (chain.scState i) (chain.G i) (chain.levelOrd i) (chain.updCount i))
    (hG : DynGraphAt st.mem rootBase G.n ec0 G) (hELt : ∀ e ∈ G.E, e < m)
    (hrootInStatic : ∀ a, rootBase ≤ a → a < rootBase + dynGraphSize G.n ec0 → extraStatic a)
    (hcap0 : G.n + ec0 + 2 ≤ capLimit)
    (hinv0 : InitPathTreeInv Rtree treeHandle G chain.toTreeChain.chainTree val B
      slots names slotThresholds m thPtr ∅ s0 xTree slot0 name0 heap st.mem)
    (hcores0 : OrdInitChainCoresK Rcore
      (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E) Rtree
      chain treeHandle levelTable branchTable rootBase edgeRecords edgeThresholds
      slots names slotThresholds m L heap G recPtr extraStatic xCore xTerm xTree st.mem)
    (hvalFwd : ∀ e ∈ chain.toTreeChain.chainTree.E, (val e).forward = true)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      |(val e).gradient| ≤ B ∧ |(val e).length| ≤ B ∧ |(val e).flow| ≤ B ∧ |(val e).detector| ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity 4 L : ℤ))
    (h0 : st.regs 0 = treeHandle) (h3 : st.regs 3 = heap)
    (h9 : st.regs 9 = dgETailSlotBase rootBase G.n ec0)
    (h10 : st.regs 10 = dgEHeadSlotBase rootBase G.n ec0)
    (h11 : st.regs 11 = dgIntToExtBase rootBase G.n)
    (h19 : st.regs 19 = slots) (h20 : st.regs 20 = names)
    (h22 : st.regs 22 = edgeRecords) (h23 : st.regs 23 = edgeThresholds)
    (h24 : st.regs 24 = slotThresholds)
    (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h31 : st.regs 31 = C.d) (h34 : st.regs 34 = rootBase)
    (hrecPtr : ∀ e ∈ chain.toTreeChain.chainTree.E, st.mem (edgeRecords + e) = recPtr e)
    (hrecAt : ∀ e ∈ chain.toTreeChain.chainTree.E, PathEdgeAt st.mem (recPtr e) 4 L (some (val e)))
    (hthPtrAt : ∀ e ∈ chain.toTreeChain.chainTree.E, st.mem (edgeThresholds + e) = thPtr e)
    (hthValW : ∀ e ∈ chain.toTreeChain.chainTree.E, thPtr e < 2 ^ w)
    (hstaticBelow : ∀ a, InitChainStaticAddr rootBase levelTable branchTable
      edgeRecords edgeThresholds C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a →
      a < heap ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ Rtree.foot treeHandle xTree a)
    (hslotsBelow : slots + m ≤ heap) (hnamesBelow : names + 2 * G.n ≤ heap)
    (hstBelow : slotThresholds + 2 * G.n ≤ heap)
    (hdisjSN : slots + m ≤ names ∨ names + 2 * G.n ≤ slots)
    (hdisjST : slots + m ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ slots)
    (hdisjNT : names + 2 * G.n ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ names)
    (hfootTreeOut : ∀ a, Rtree.foot treeHandle xTree a →
      OutsideInitSlotTables slots names slotThresholds m G.n a)
    (hhandlesW : ∀ i ≤ C.d, st.mem (levelTable + i) < 2 ^ w ∧ st.mem (branchTable + i) < 2 ^ w)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hhandleW : treeHandle < 2 ^ w) (hdW : C.d < 2 ^ w) (hw7 : 7 < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hlinkAlloc : ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
      heap ≤ cur → cur ≤ heap + initLinkChainSpace C.d m linkSpace →
      treeAlloc 0 G.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, cur] ≤ linkSpace)
    (hroom : heap + initLinkChainSpace C.d m linkSpace < 2 ^ w) :
    let Rterm := lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E
    ∃ (out : State) (ret cost : ℕ) (sFin : PathTreeState) (yTree : Rtree.τ)
      (slotFin nameFin : ℕ → ℕ) (yCore : ℕ → Rcore.τ) (yTerm : ℕ),
      Runs w p ω (initLinkChainForests (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
        st .normal out cost ∧
      out.regs 3 = ret ∧
      (∀ r, 36 ≤ r → out.regs r = st.regs r) ∧
      InitPathTreeInv Rtree treeHandle G chain.toTreeChain.chainTree val B
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin ret out.mem ∧
      (∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a → out.mem a = st.mem a) ∧
      ZeroFrom out.mem ret ∧ heap ≤ ret ∧ ret ≤ heap + initLinkChainSpace C.d m linkSpace ∧
      (∀ a, Rtree.foot treeHandle yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
      OrdInitChainCoresK Rcore Rterm Rtree chain treeHandle levelTable branchTable
        rootBase edgeRecords edgeThresholds slots names slotThresholds m L ret G recPtr extraStatic
        yCore yTerm yTree out.mem ∧
      cost + Rtree.phi treeHandle yTree out.mem +
          (∑ i : Fin C.d, Rcore.phi (out.mem (levelTable + i.val)) (yCore i.val) out.mem) ≤
        initLinkChainCost C.d m treeConst L G.n P.readout +
          Rtree.phi treeHandle xTree st.mem +
          (∑ i : Fin C.d, Rcore.phi (st.mem (levelTable + i.val)) (xCore i.val) st.mem) := by
  dsimp only
  let Rterm := lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E
  have htermLocal := lastLevelRepresentation_local vcLast ecLast 4 L fmt.precision (chain.G C.d).E
  let Ttree := chain.toTreeChain.chainTree
  have hSub := chain.toTreeChain.forestsAreSubgraphs_of_holds hH
  have hTForest : Ttree.IsForest := chain.toTreeChain.chainTree_isForest hH hSub
  have hTG0 : chain.toTreeChain.G 0 = G := hH.1
  have hTG : Ttree.E ⊆ G.E := by
    have hs := chain.toTreeChain.chainTree_isSubgraph hH hSub; rw [hTG0] at hs; exact hs.2.1
  have hTEnds : ∀ f ∈ Ttree.E, Ttree.tail f = G.tail f ∧ Ttree.head f = G.head f := by
    intro f _; change (chain.toTreeChain.G 0).tail f = G.tail f ∧ (chain.toTreeChain.G 0).head f = G.head f
    rw [hTG0]; exact ⟨rfl, rfl⟩
  have hrootStatic (a : ℕ) (hlo : rootBase ≤ a) (hhi : a < rootBase + dynGraphSize G.n ec0) :
      InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hrootInStatic a hlo hhi))))))
  have hrootBelow : rootBase + dynGraphSize G.n ec0 ≤ heap := by
    have hsz : 0 < dynGraphSize G.n ec0 := by unfold dynGraphSize; omega
    have h := (hstaticBelow (rootBase + dynGraphSize G.n ec0 - 1)
      (hrootStatic _ (by omega) (by omega))).1
    omega
  have hSumAllLe : ∑ j ∈ Finset.range (C.d + 1), (chain.toTreeChain.activeLSF j).F.F.m ≤ m :=
    (activeLSF_sum_le_m hH).trans (by
      simpa [MGraph.m] using Finset.card_le_card (fun e he => Finset.mem_range.mpr (hELt e he)))
  let sInit := { st with regs := Function.update st.regs 32 0 }
  have hrInit : Runs w p ω (.assign 32 (.const 0)) st .normal sInit 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hI0 : InitChainLoopInvK Rcore Rterm Rtree chain treeHandle rootBase levelTable branchTable
      slots names slotThresholds edgeRecords edgeThresholds m ec0 L heap linkSpace capLimit
      G val B recPtr thPtr extraStatic st.mem 0 sInit heap s0 xTree slot0 name0 xCore xTerm :=
    ⟨by simp [sInit], by simp [sInit, h31], by simp [sInit, h0], by simp [sInit, h3],
     by simp [sInit, h9], by simp [sInit, h10], by simp [sInit, h11],
     by simp [sInit, h19], by simp [sInit, h20], by simp [sInit, h22], by simp [sInit, h23],
     by simp [sInit, h24], by simp [sInit, h29], by simp [sInit, h30],
     le_rfl, by simp, hz, fun _ _ => rfl,
     ⟨G.n, ec0, rfl, rfl, hcap0, by rw [show chain.G 0 = G from hTG0]; simpa [sInit, h34] using hG,
       by simpa [sInit, h34] using hrootBelow⟩,
     by simpa using hinv0,
     fun a ha => ⟨hfootTreeOut a ha, fun hs => (hstaticBelow a hs).2.2 ha⟩, hcores0⟩
  obtain ⟨mid, midHeap, midS, midXTree, midSlot, midName, midXCore, midXTerm, cLoop,
      hrLoop, hId, hMidRegs, hcLoop⟩ :=
    initLinkChainLoopK_runs hFour hH hcoreImpl htreeImpl hbind hcoreInput hG hELt hrootInStatic
      hvalFwd hvalB hcapB hrecPtr hrecAt hthPtrAt hthValW
      (fun a ha => ⟨(hstaticBelow a ha).1, (hstaticBelow a ha).2.1⟩)
      hslotsBelow hnamesBelow hstBelow hdisjSN hdisjST hdisjNT hhandlesW
      hvw hwidth hhandleW hdW hw7 hlinkAlloc hroom
      C.d 0 (Nat.zero_add C.d) sInit heap s0 xTree slot0 name0 xCore xTerm hI0
  -- Terminal level `C.d`: opLast 0 + `initLinkForestEdges`
  have hlastLvStat : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
      C.d m L G Ttree recPtr extraStatic (levelTable + C.d) := Or.inr (Or.inl ⟨by omega, by omega⟩)
  have hlastBrStat : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
      C.d m L G Ttree recPtr extraStatic (branchTable + C.d) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hlhEq : mid.mem (levelTable + C.d) = st.mem (levelTable + C.d) := hId.staticEq _ hlastLvStat
  have hlbrEq : mid.mem (branchTable + C.d) = chain.lastBran := hId.cores.2.1
  let l1 := { mid with regs := Function.update mid.regs 33 midHeap }
  have hrL1 : Runs w p ω (.assign 33 (.reg 3)) mid .normal l1 2 :=
    runs_assign_iff.mpr ⟨midHeap, by simp [Expr.eval, hId.r3], rfl, rfl, rfl⟩
  have hSumD := hSumAllLe
  rw [Finset.sum_range_succ] at hSumD
  have hMulD : ((∑ j ∈ Finset.range C.d, (chain.toTreeChain.activeLSF j).F.F.m) +
      (chain.toTreeChain.activeLSF C.d).F.F.m) * linkSpace ≤ m * linkSpace :=
    Nat.mul_le_mul_right linkSpace hSumD
  have hlastRoom4 : midHeap + 4 < 2 ^ w := by
    have := hId.heapHi; rw [Nat.add_mul] at hMulD; dsimp only [initLinkChainSpace] at hroom; omega
  have hlbrValW : chain.lastBran < 2 ^ w := by
    have := (hhandlesW C.d le_rfl).2; rw [← hId.staticEq _ hlastBrStat, hlbrEq] at this; exact this
  have hTermRepMid : Rterm.rep (st.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) midXTerm mid.mem :=
    hlhEq ▸ hId.cores.2.2.1
  have hTermLimitLe : midXTerm ≤ midHeap := by
    by_cases hlt : st.mem (levelTable + C.d) < midXTerm
    · have hlt' := (hId.cores.2.2.2 (midXTerm - 1) (by rw [hlhEq]; exact ⟨by omega, by omega⟩)).1
      omega
    · have := hTermRepMid.1; omega
  obtain ⟨hspanLast, _⟩ := hTermRepMid.2.2.2 chain.lastBran hH.2.2.2.2.2.1
  let bLast := st.mem (levelTable + C.d)
  let baseLast := mid.mem (bLast + 1 + chain.lastBran)
  have hLastKLe : bLast + 1 + chain.lastK ≤ midXTerm := hTermRepMid.1
  have hLastBrLt : chain.lastBran < chain.lastK := hH.2.2.2.2.2.1
  have hslotLt : bLast + 1 + chain.lastBran < midHeap := by omega
  obtain ⟨oR, afterR, cLRF, hrReadout, ⟨hoR, hmemR⟩, hcLRF⟩ :=
    LastLevelProgram.readout_runs (w := w) p ω bLast chain.lastBran midHeap l1.pos mid.mem hslotLt
      (by have := hspanLast.2.1; dsimp only [baseLast, bLast] at *; omega) hlastRoom4
      (by
        have h1 := hspanLast.2.2.2.1
        have h2 : 0 < dynGraphSize vcLast ecLast := by unfold dynGraphSize; omega
        dsimp only [baseLast, bLast] at *; omega)
      (by
        have h1 := hspanLast.2.2.2.2.2.1
        have h2 : 0 < dynGraphSize vcLast ecLast := by unfold dynGraphSize; omega
        dsimp only [baseLast, bLast] at *; omega)
      (by have h1 := hspanLast.2.2.2.2.2.2.2.1; dsimp only [baseLast, bLast] at *; omega)
      (by have h1 := hspanLast.2.2.2.2.2.2.2.2.2.1; dsimp only [baseLast, bLast] at *; omega)
  cases oR with
  | normal => simp [Outcome.value] at hoR
  | returned retL1 =>
    change retL1 = midHeap + 4 at hoR
    subst hoR
    let l2 : State := { afterR with regs := Function.update l1.regs 3 (midHeap + 4) }
    have hargsL2 : evalArgs w l1 [.load (.bin .add (.reg 29) (.reg 31)),
        .load (.bin .add (.reg 30) (.reg 31)), .reg 3] =
        some [bLast, chain.lastBran, midHeap] := by
      simp [evalArgs, Expr.eval, BinOp.eval, l1, hId.r29, hId.r30, hId.r31, hId.r3,
        show levelTable + C.d < 2 ^ w by have := (hstaticBelow _ hlastLvStat).1; omega,
        show branchTable + C.d < 2 ^ w by have := (hstaticBelow _ hlastBrStat).1; omega,
        hlhEq, hlbrEq, bLast]
    have hrL2 : Runs w p ω (.call 3 (opLast 0) [.load (.bin .add (.reg 29) (.reg 31)),
        .load (.bin .add (.reg 30) (.reg 31)), .reg 3]) l1 .normal l2 (9 + cLRF + 1) :=
      runs_call_iff.mpr ⟨_, LastLevelProgram.readoutBody, .returned (midHeap + 4), afterR, cLRF,
        hargsL2, hLastReadout, hrReadout, rfl, rfl, rfl⟩
    have hframeLast (a : ℕ) (ha : a < midHeap) : l2.mem a = mid.mem a := by
      change afterR.mem a = mid.mem a
      rw [hmemR]
      simp [Function.update_of_ne (show a ≠ midHeap + 3 by omega),
        Function.update_of_ne (show a ≠ midHeap + 2 by omega),
        Function.update_of_ne (show a ≠ midHeap + 1 by omega),
        Function.update_of_ne (show a ≠ midHeap by omega)]
    have hzL2 : ZeroFrom l2.mem (midHeap + 4) := fun a ha => by
      change afterR.mem a = 0; rw [hmemR]
      simp only [Function.update_of_ne (show a ≠ midHeap + 3 by omega),
        Function.update_of_ne (show a ≠ midHeap + 2 by omega),
        Function.update_of_ne (show a ≠ midHeap + 1 by omega),
        Function.update_of_ne (show a ≠ midHeap by omega)]
      exact hId.zeroFrom a (by omega)
    have hstatL2 (a : ℕ) (ha : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a) : l2.mem a = st.mem a :=
      (hframeLast a ((hstaticBelow a ha).1.trans_le hId.heapLo)).trans (hId.staticEq a ha)
    let fBaseLast := l2.mem (midHeap + 1)
    have hfBaseEq : fBaseLast = mid.mem (baseLast + 1) := by
      change afterR.mem (midHeap + 1) = mid.mem (baseLast + 1)
      rw [hmemR]; simp [baseLast, Function.update_of_ne]
    let Fd := (chain.toTreeChain.activeLSF C.d).F.F
    have hFdEq : (chain.lastLSFs chain.lastBran).F.F = Fd := by
      simp [Fd, TreeChain.activeLSF, ChainState.toTreeChain]
    have hFdMid : DynGraphAt mid.mem (mid.mem (baseLast + 1)) vcLast ecLast Fd :=
      hFdEq ▸ (hTermRepMid.2.2.2 chain.lastBran hH.2.2.2.2.2.1).2.2.1
    have hFdDG : DynGraphAt l2.mem fBaseLast vcLast ecLast Fd := by
      rw [hfBaseEq]
      exact dynGraphAt_of_agree hFdMid (fun a hlo hhi =>
        hframeLast a (lt_of_lt_of_le hhi (hspanLast.2.2.2.2.2.1.trans hTermLimitLe)))
    have hfBaseInTerm (a : ℕ) (hlo : fBaseLast ≤ a) (hhi : a < fBaseLast + dynGraphSize vcLast ecLast) :
        Rterm.foot bLast midXTerm a := by
      rw [hfBaseEq] at hlo hhi
      have h1 := hspanLast.2.2.2.2.1
      have h2 := hspanLast.2.2.2.2.2.1
      dsimp only [bLast, baseLast] at h1 h2 hlo hhi ⊢
      exact ⟨by omega, by omega⟩
    have hfBaseEnd : fBaseLast + dynGraphSize vcLast ecLast ≤ midHeap + 4 := by
      rw [hfBaseEq]; have := hspanLast.2.2.2.2.2.1; dsimp only [baseLast, bLast] at *; omega
    -- Step 2: reg 25 := fBaseLast; link terminal forest Fd
    let l3 := { l2 with regs := Function.update l2.regs 25 fBaseLast }
    have hrL3 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 33) (.const 1)))) l2 .normal l3 5 :=
      runs_assign_iff.mpr ⟨fBaseLast, by
        simp [Expr.eval, BinOp.eval, l2, l1, show 1 < 2 ^ w by omega,
          show midHeap + 1 < 2 ^ w by omega, fBaseLast], rfl, rfl, rfl⟩
    have htreeLocL2 := htreeImpl.1 treeHandle midS midXTree mid.mem l2.mem (fun a ha =>
      (hframeLast a (hId.treeInv.2.2.2.1 a ha)).symm)
    have hinvL3 : InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
        ((Finset.range C.d).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
        midS midXTree midSlot midName (midHeap + 4) l3.mem := by
      obtain ⟨hn, hsub', hrepT, hfootT, ⟨hslotT, hnameT⟩, hwt, hstT, hzrT⟩ := hId.treeInv
      refine ⟨hn, hsub', htreeLocL2.1 hrepT, fun a ha => (hfootT a ha).trans_le (by omega),
        ⟨fun e he => (hframeLast _ (by have := hId.heapLo; omega)).trans (hslotT e he),
         fun k hk => (hframeLast _ (by have := hId.heapLo; omega)).trans (hnameT k hk)⟩,
        hwt, fun e he => by
          have hsLt : midSlot e < 2 * G.n := by
            obtain ⟨ts, _, _, hW, _, hnm, _⟩ := hwt; exact (hn ▸ (hnm.forward e he).2.1).2
          exact (hframeLast _ (by have := hId.heapLo; omega)).trans (hstT e he),
        hzrT⟩
    have hGL3 : DynGraphAt l3.mem rootBase G.n ec0 G :=
      dynGraphAt_of_agree hG (fun a hlo hhi => hstatL2 a (hrootStatic a hlo hhi))
    have hlinkRoomD : midHeap + 4 + Fd.m * linkSpace < 2 ^ w := by
      have := hId.heapHi; rw [Nat.add_mul] at hMulD
      dsimp only [initLinkChainSpace] at hroom; dsimp only [Fd]; omega
    obtain ⟨out, retFin, cLinkD, sFin, yTreeFin, slotFin, nameFin,
        hrL4, hout3, hregsL4, hinvFin, htreeOutFin, hrespFin, hcLinkD⟩ :=
      initLinkForestEdges_runs (edgeRecords := edgeRecords) (edgeThresholds := edgeThresholds)
        (ω := ω) (st := l3) htreeImpl hbind hTForest hTEnds hGL3 hFdDG
        hTG hELt (activeLSF_subset_chainTree le_rfl) (initChain_prefix_disjoint hH le_rfl)
        hinvL3 (fun e he => hvalFwd e (activeLSF_subset_chainTree le_rfl he))
        (fun e he => hvalB e (activeLSF_subset_chainTree le_rfl he)) (hFour ▸ hcapB)
        (by simp [l3, l2, l1, hId.r0]) (by simp [l3, l2])
        (by simp [l3, l2, l1, hId.r9]) (by simp [l3, l2, l1, hId.r10])
        (by simp [l3, l2, l1, hId.r11]) (by simp [l3, l2, l1, hId.r19])
        (by simp [l3, l2, l1, hId.r20]) (by simp [l3, l2, l1, hId.r22])
        (by simp [l3, l2, l1, hId.r23]) (by simp [l3, l2, l1, hId.r24]) (by simp [l3])
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have heM : e < m := hELt e (hTG heT)
          exact (hstatL2 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans (hrecPtr e heT))
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          exact hFour ▸ (hrecAt e heT).congr (fun a hlo hhi =>
            hstatL2 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, hlo, by omega⟩))))))))
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have heM : e < m := hELt e (hTG heT)
          exact (hstatL2 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).trans (hthPtrAt e heT))
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have h := (hstaticBelow (recPtr e + (2 + 4 * L) - 1)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, by omega, by omega⟩))))))).1
          have := hId.heapLo; omega)
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have heM : e < m := hELt e (hTG heT)
          have h := (hstaticBelow (edgeRecords + e) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).1
          have := hId.heapLo; omega)
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have heM : e < m := hELt e (hTG heT)
          have h := (hstaticBelow (edgeThresholds + e) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).1
          have := hId.heapLo; omega)
        (fun e he => hthValW e (activeLSF_subset_chainTree le_rfl he))
        (by have := hId.heapLo; omega) hfBaseEnd
        (by have := hId.heapLo; omega) (by have := hId.heapLo; omega) (by have := hId.heapLo; omega)
        hdisjSN hdisjST hdisjNT (fun a ha => (hId.treeOut a ha).1)
        (fun a hlo hhi => ⟨(hstaticBelow a (hrootStatic a hlo hhi)).2.1,
          fun hft => (hId.treeOut a hft).2 (hrootStatic a hlo hhi)⟩)
        (fun a hlo hhi =>
          have hft := hfBaseInTerm a hlo hhi
          ⟨(hId.cores.2.2.2 a (hlhEq.symm ▸ hft)).2.1, (hId.cores.2.2.2 a (hlhEq.symm ▸ hft)).2.2.2.1⟩)
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have heM : e < m := hELt e (hTG heT)
          exact ⟨(hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).2.1,
            fun hft => (hId.treeOut _ hft).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))⟩)
        (fun e he a hlo hhi => by
          have heT := activeLSF_subset_chainTree le_rfl he
          exact ⟨(hstaticBelow a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, hlo, hhi⟩))))))).2.1,
            fun hft => (hId.treeOut a hft).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, hlo, hhi⟩))))))⟩)
        (fun e he => by
          have heT := activeLSF_subset_chainTree le_rfl he
          have heM : e < m := hELt e (hTG heT)
          exact ⟨(hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).2.1,
            fun hft => (hId.treeOut _ hft).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))⟩)
        hvw (hFour ▸ hwidth) hhandleW hw7 hzL2
        (fun e he cur hlo hhi => hlinkAlloc e (activeLSF_subset_chainTree le_rfl he) cur
          (hId.heapLo.trans (by omega)) (by
            have := hId.heapHi; rw [Nat.add_mul] at hMulD
            dsimp only [initLinkChainSpace, Fd] at hhi ⊢; omega))
        hlinkRoomD
    have hframeFin (a : ℕ) (ha : a < midHeap + 4) (hnt : ¬ Rtree.foot treeHandle midXTree a)
        (hout : OutsideInitSlotTables slots names slotThresholds m G.n a) :
        out.mem a = l2.mem a :=
      hrespFin.2.2.2.1 a ha (fun h => h.elim hnt (fun hno => hno hout))
    have hstatFin (a : ℕ) (ha : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a) : out.mem a = st.mem a :=
      (hframeFin a (lt_of_lt_of_le (hstaticBelow a ha).1 (hId.heapLo.trans (by omega)))
        (fun hft => (hId.treeOut a hft).2 ha) (hstaticBelow a ha).2.1).trans (hstatL2 a ha)
    have hTreeOutFinFull (a : ℕ) (hft : Rtree.foot treeHandle yTreeFin a) :
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic a := by
      refine ⟨htreeOutFin a hft, fun hs => ?_⟩
      rcases hrespFin.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
      · exact hpre.elim (fun h => (hId.treeOut a h).2 hs) (fun hno => hno (hstaticBelow a hs).2.1)
      · have := (hstaticBelow a hs).1; have := hId.heapLo; omega
    have hCorePresFin (j : ℕ) (hj : j < C.d) :
        out.mem (levelTable + j) = mid.mem (levelTable + j) ∧
        out.mem (branchTable + j) = chain.bran j ∧
        Rcore.rep (out.mem (levelTable + j)) (chainLevelOrdAbs chain j) (midXCore j) out.mem ∧
        Rcore.phi (out.mem (levelTable + j)) (midXCore j) out.mem =
          Rcore.phi (mid.mem (levelTable + j)) (midXCore j) mid.mem := by
      have hlvJ : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic (levelTable + j) := Or.inr (Or.inl ⟨by omega, by omega⟩)
      have hbrJ : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic (branchTable + j) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      obtain ⟨hbrOld, hrepOld, hfootOld⟩ := hId.cores.1 j hj
      have hlvEq : out.mem (levelTable + j) = mid.mem (levelTable + j) :=
        (hstatFin _ hlvJ).trans (hId.staticEq _ hlvJ).symm
      have hbrEq' : out.mem (branchTable + j) = chain.bran j :=
        (hstatFin _ hbrJ).trans ((hId.staticEq _ hbrJ).symm.trans hbrOld)
      have hcoreLoc : Rcore.Local := (hcoreImpl j hj).1.1
      have hloc := hcoreLoc (mid.mem (levelTable + j)) (chainLevelOrdAbs chain j) (midXCore j)
        mid.mem out.mem (fun a ha => by
          have hfo := hfootOld a ha
          exact ((hframeFin a (by omega) hfo.2.2.2.1 hfo.2.1).trans (hframeLast a hfo.1)).symm)
      exact ⟨hlvEq, hbrEq', by rw [hlvEq]; exact hloc.1 hrepOld, by rw [hlvEq]; exact hloc.2.symm⟩
    have hTermLocFin := htermLocal bLast (chain.lastK, chain.lastLSFs) midXTerm mid.mem out.mem (fun a ha => by
      have hfo := hId.cores.2.2.2 a (hlhEq.symm ▸ ha)
      exact ((hframeFin a (by omega) hfo.2.2.2.1 hfo.2.1).trans (hframeLast a hfo.1)).symm)
    have hCoresFin : OrdInitChainCoresK Rcore Rterm Rtree chain treeHandle levelTable branchTable
        rootBase edgeRecords edgeThresholds slots names slotThresholds m L retFin G recPtr
        extraStatic midXCore midXTerm yTreeFin out.mem := by
      refine ⟨fun j hj => ?_, (hstatFin _ hlastBrStat).trans ((hId.staticEq _ hlastBrStat).symm.trans hlbrEq),
        by rw [hstatFin _ hlastLvStat]; exact hTermLocFin.1 hTermRepMid, fun a ha => ?_⟩
      · obtain ⟨hlvEq, hbrEq', hrepJ, _⟩ := hCorePresFin j hj
        refine ⟨hbrEq', hrepJ, fun a ha => ?_⟩
        rw [hlvEq] at ha
        have hfo := (hId.cores.1 j hj).2.2 a ha
        refine ⟨hfo.1.trans_le (by have := hrespFin.1; omega), hfo.2.1, hfo.2.2.1, fun hft => ?_,
          fun j' hj' hne hfj' => hfo.2.2.2.2.1 j' hj' hne (by rwa [(hCorePresFin j' hj').1] at hfj'),
          fun hft => hfo.2.2.2.2.2 (by rw [hstatFin _ hlastLvStat] at hft; rwa [hlhEq])⟩
        rcases hrespFin.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
        · exact hpre.elim hfo.2.2.2.1 (fun hno => hno hfo.2.1)
        · omega
      · rw [hstatFin _ hlastLvStat] at ha
        have hfo := hId.cores.2.2.2 a (hlhEq.symm ▸ ha)
        refine ⟨hfo.1.trans_le (by have := hrespFin.1; omega), hfo.2.1, hfo.2.2.1, fun hft => ?_,
          fun j hj hfj => hfo.2.2.2.2 j hj (by rwa [(hCorePresFin j hj).1] at hfj)⟩
        rcases hrespFin.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
        · exact hpre.elim hfo.2.2.2.1 (fun hno => hno hfo.2.1)
        · omega
    have rFull : Runs w p ω (initLinkChainForests (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
        st .normal out (2 + (cLoop + (2 + ((9 + cLRF + 1) + (5 + cLinkD + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨sInit, 2, _, hrInit,
      runs_seq_iff.mpr (Or.inr ⟨mid, cLoop, _, hrLoop,
      runs_seq_iff.mpr (Or.inr ⟨l1, 2, _, hrL1,
      runs_seq_iff.mpr (Or.inr ⟨l2, 9 + cLRF + 1, _, hrL2,
      runs_seq_iff.mpr (Or.inr ⟨l3, 5, cLinkD, hrL3, hrL4, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hUnionFull :
        ((Finset.range C.d).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E) ∪ Fd.E =
          Ttree.E := by
      rw [show Fd.E = (chain.toTreeChain.activeLSF C.d).F.F.E from rfl, initChain_prefix_union C.d]
      rfl
    have hCorePhiFin :
        (∑ j : Fin C.d, Rcore.phi (out.mem (levelTable + j.val)) (midXCore j.val) out.mem) =
        (∑ j : Fin C.d, Rcore.phi (mid.mem (levelTable + j.val)) (midXCore j.val) mid.mem) :=
      Finset.sum_congr rfl fun j _ => (hCorePresFin j.val j.isLt).2.2.2
    have hTreePhiL2 : Rtree.phi treeHandle midXTree l3.mem = Rtree.phi treeHandle midXTree mid.mem :=
      htreeLocL2.2.symm
    have hSumCost :
        (∑ j ∈ Finset.range C.d, if 0 ≤ j then
          (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) +
          Fd.m * (pathTreeBudget treeConst L G.n + 96) ≤
        m * (pathTreeBudget treeConst L G.n + 96) := by
      have h1 : (∑ j ∈ Finset.range C.d, if 0 ≤ j then
          (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) =
          (∑ j ∈ Finset.range C.d, (chain.toTreeChain.activeLSF j).F.F.m) *
            (pathTreeBudget treeConst L G.n + 96) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by simp
      rw [h1, ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ hSumD
    refine ⟨out, retFin, _, sFin, yTreeFin, slotFin, nameFin, midXCore, midXTerm,
      rFull, hout3, fun r hr => by
        rw [hregsL4 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)]
        simp only [l3, l2, l1, Function.update_of_ne (show r ≠ 25 by omega),
          Function.update_of_ne (show r ≠ 3 by omega), Function.update_of_ne (show r ≠ 33 by omega)]
        rw [hMidRegs r hr]
        simp [sInit, Function.update_of_ne (show r ≠ 32 by omega)],
      by rwa [hUnionFull] at hinvFin, hstatFin, hrespFin.2.2.1,
      hId.heapLo.trans (by have := hrespFin.1; omega),
      by have := hId.heapHi; have hF := hrespFin.2.1; rw [Nat.add_mul] at hMulD
         dsimp only [initLinkChainSpace, Fd] at hF ⊢; omega,
      hTreeOutFinFull, hCoresFin, ?_⟩
    rw [hCorePhiFin]
    rw [hTreePhiL2] at hcLinkD
    simp only [Nat.sub_zero] at hcLoop
    dsimp only [initLinkChainCost, sInit] at hcLoop ⊢
    omega

end MinCostFlow.MinRatio
