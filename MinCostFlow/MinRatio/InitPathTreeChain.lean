module

public import MinCostFlow.MinRatio.InitPathTreeChainLoop
import MinCostFlow.MinRatio.ShiftForestScan
import Mathlib.Tactic.Ring

/-!
# Full chain spanning-forest insertion into the Section 6 path tree

Composes `initLinkChainLoop_runs` (for sparse-core levels `0 .. C.d - 1`) with
the terminal `opLast 0` readout and `initLinkForestEdges` for level `C.d`,
populating the Section 6 path tree with `chain.toTreeChain.chainTree`, its
`PathSlotTablesAt`, and its `slotThresholds` pointers while preserving all
sparse-core and last-level representations.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- Run `initLinkChainForests` across all `C.d + 1` levels of an initialized
chain `chain`, inserting every edge of `chain.toTreeChain.chainTree` into the
Section 6 path tree with exact `InitPathTreeInv`, while preserving all core and
terminal data structure representations. -/
theorem initLinkChainForests_runs {w L treeConst initCore initLast initTree bind
    treeHandle rootBase levelTable branchTable slots names slotThresholds
    edgeRecords edgeThresholds m heap levelSpace linkSpace lastMult stretchP vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {lastTool : LastLevelTool}
    {C : ChainParams} {costs : SparseCoreMachineCosts}
    {coreAlloc : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {treeAlloc : ℕ → ℕ → List ℕ → ℕ}
    {Mcap Ncap : ℕ → ℕ} {Rcore : DSRep T.State}
    {Rterm : DSRep (ℕ × (ℕ → LSF))} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} {val : ℕ → PathEdgeValue} {B : ℤ}
    {recPtr thPtr : ℕ → ℕ} {extraStatic : ℕ → Prop} {xCore : ℕ → Rcore.τ} {xTerm : Rterm.τ}
    {s0 : PathTreeState} {xTree : Rtree.τ} {slot0 name0 : ℕ → ℕ}
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hcoreImpl : ∀ i < C.d, ∀ vc ec, Rcore.Implements w p initCore opCore
      (sparseCoreMachineContract fmt L T (chain.G i) C.k (Mcap i) (Ncap i) vc ec costs (coreAlloc i)))
    (htermImpl : Rterm.Implements w p initLast opLast
      (lastLevelRuntimeMachineContract fmt L lastTool (chain.G C.d) vcLast ecLast lastMult stretchP lastAlloc))
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreInput : ∀ i < C.d,
      SparseCoreInput T.toSparseCoreTool T.restart C.k (chain.scState i) (chain.G i))
    (hG : DynGraphAt st.mem rootBase G.n G.m G) (hGm : G.m = m)
    (hinv0 : InitPathTreeInv Rtree treeHandle G chain.toTreeChain.chainTree val B
      slots names slotThresholds m thPtr ∅ s0 xTree slot0 name0 heap st.mem)
    (hcores0 : InitChainCoresAt Rcore Rterm Rtree chain treeHandle levelTable branchTable
      rootBase edgeRecords edgeThresholds slots names slotThresholds m L heap G recPtr extraStatic
      xCore xTerm xTree st.mem)
    (hvalFwd : ∀ e ∈ chain.toTreeChain.chainTree.E, (val e).forward = true)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      |(val e).gradient| ≤ B ∧ |(val e).length| ≤ B ∧ |(val e).flow| ≤ B ∧ |(val e).detector| ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity fmt.limbBits L : ℤ))
    (h0 : st.regs 0 = treeHandle) (h3 : st.regs 3 = heap)
    (h9 : st.regs 9 = dgETailSlotBase rootBase G.n G.m)
    (h10 : st.regs 10 = dgEHeadSlotBase rootBase G.n G.m)
    (h11 : st.regs 11 = dgIntToExtBase rootBase G.n)
    (h19 : st.regs 19 = slots) (h20 : st.regs 20 = names)
    (h22 : st.regs 22 = edgeRecords) (h23 : st.regs 23 = edgeThresholds)
    (h24 : st.regs 24 = slotThresholds)
    (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h31 : st.regs 31 = C.d) (h34 : st.regs 34 = rootBase)
    (hrecPtr : ∀ e ∈ chain.toTreeChain.chainTree.E, st.mem (edgeRecords + e) = recPtr e)
    (hrecAt : ∀ e ∈ chain.toTreeChain.chainTree.E,
      PathEdgeAt st.mem (recPtr e) fmt.limbBits L (some (val e)))
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
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ fmt.limbBits * L)
    (hhandleW : treeHandle < 2 ^ w) (hdW : C.d < 2 ^ w) (hw7 : 7 < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hreadoutBounds : ∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (fv fe : ℕ) (yCore : Rcore.τ),
      heap ≤ cur → cur ≤ ret →
      LSFAt mem' cur fv fe fmt.limbBits L fmt.precision (chain.G i).E (T.lsfs (chain.scState i) (chain.bran i)) →
      let fBase := mem' (cur + 1)
      fBase + dynGraphSize fv fe ≤ ret ∧
      (∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        Rcore.foot (st.mem (levelTable + i)) yCore a ∨ (cur ≤ a ∧ a < ret)))
    (hgraphReadBounds : ∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (gv ge : ℕ) (yCore : Rcore.τ),
      heap ≤ cur → cur ≤ ret →
      DynGraphAt mem' (mem' cur) gv ge (chain.G (i + 1)) →
      mem' cur + dynGraphSize gv ge ≤ ret ∧
      (∀ a, mem' cur ≤ a → a < mem' cur + dynGraphSize gv ge →
        Rcore.foot (st.mem (levelTable + i)) yCore a ∨ (cur ≤ a ∧ a < ret)))
    (hlastReadBounds : ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (fv fe : ℕ) (yTerm : Rterm.τ),
      heap ≤ cur → cur ≤ ret →
      LSFAt mem' cur fv fe fmt.limbBits L fmt.precision (chain.G C.d).E (chain.lastLSFs chain.lastBran) →
      let fBase := mem' (cur + 1)
      fBase + dynGraphSize fv fe ≤ ret ∧
      (∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        Rterm.foot (st.mem (levelTable + C.d)) yTerm a ∨ (cur ≤ a ∧ a < ret)))
    (hlevelCap : ∀ i < C.d, 5 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace ≤ levelSpace)
    (hlastCap : 4 + (chain.toTreeChain.activeLSF C.d).F.F.m * linkSpace ≤ levelSpace)
    (hlinkAlloc : ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
      heap ≤ cur → cur ≤ heap + (C.d + 1) * levelSpace →
      treeAlloc 0 G.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, cur] ≤ linkSpace)
    (hroom : heap + (C.d + 1) * levelSpace < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (sFin : PathTreeState) (yTree : Rtree.τ)
      (slotFin nameFin : ℕ → ℕ) (yCore : ℕ → Rcore.τ) (yTerm : Rterm.τ),
      Runs w p ω (initLinkChainForests (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
        st .normal out cost ∧
      out.regs 3 = ret ∧
      InitPathTreeInv Rtree treeHandle G chain.toTreeChain.chainTree val B
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin ret out.mem ∧
      (∀ a, Rtree.foot treeHandle yTree a → ¬ extraStatic a) ∧
      (∀ i < C.d, Rcore.rep (st.mem (levelTable + i)) (chain.scState i) (yCore i) out.mem ∧
        ∀ a, Rcore.foot (st.mem (levelTable + i)) (yCore i) a → a < ret ∧ ¬ extraStatic a) ∧
      Rterm.rep (st.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) yTerm out.mem ∧
      (∀ a, Rterm.foot (st.mem (levelTable + C.d)) yTerm a → a < ret ∧ ¬ extraStatic a) ∧
      (∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a → out.mem a = st.mem a) ∧
      ZeroFrom out.mem ret ∧ heap ≤ ret ∧ ret ≤ heap + (C.d + 1) * levelSpace ∧
      (∀ a, Rtree.foot treeHandle yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
      InitChainCoresAt Rcore Rterm Rtree chain treeHandle levelTable branchTable
        rootBase edgeRecords edgeThresholds slots names slotThresholds m L ret G recPtr extraStatic
        yCore yTerm yTree out.mem := by
  let Ttree := chain.toTreeChain.chainTree
  have hSub := chain.toTreeChain.forestsAreSubgraphs_of_holds hH
  have hTForest : Ttree.IsForest := chain.toTreeChain.chainTree_isForest hH hSub
  have hTG0 : chain.toTreeChain.G 0 = G := hH.1
  have hTG : Ttree.E ⊆ G.E := by
    have hs := chain.toTreeChain.chainTree_isSubgraph hH hSub
    rw [hTG0] at hs; exact hs.2.1
  have hTEnds : ∀ f ∈ Ttree.E, Ttree.tail f = G.tail f ∧ Ttree.head f = G.head f := by
    intro f _; change (chain.toTreeChain.G 0).tail f = G.tail f ∧ (chain.toTreeChain.G 0).head f = G.head f
    rw [hTG0]; exact ⟨rfl, rfl⟩
  have hrootBelow : rootBase + dynGraphSize G.n G.m ≤ heap := by
    have hsz : 0 < dynGraphSize G.n G.m := by unfold dynGraphSize; omega
    have h := (hstaticBelow (rootBase + dynGraphSize G.n G.m - 1) (Or.inl ⟨by omega, by omega⟩)).1
    omega
  let sInit := { st with regs := Function.update st.regs 32 0 }
  have hrInit : Runs w p ω (.assign 32 (.const 0)) st .normal sInit 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hI0 : InitChainLoopInv Rcore Rterm Rtree chain treeHandle rootBase levelTable branchTable
      slots names slotThresholds edgeRecords edgeThresholds m L heap levelSpace
      G val B recPtr thPtr extraStatic st.mem 0 sInit heap s0 xTree slot0 name0 xCore xTerm :=
    ⟨by simp [sInit], by simp [sInit, h31], by simp [sInit, h0], by simp [sInit, h3],
     by simp [sInit, h9], by simp [sInit, h10], by simp [sInit, h11],
     by simp [sInit, h19], by simp [sInit, h20], by simp [sInit, h22], by simp [sInit, h23],
     by simp [sInit, h24], by simp [sInit, h29], by simp [sInit, h30],
     le_rfl, by simp, hz, fun _ _ => rfl,
     ⟨G.n, G.m, by rw [show chain.G 0 = G from hTG0]; simpa [sInit, h34] using hG,
       by simpa [sInit, h34] using hrootBelow⟩,
     by simpa using hinv0,
     fun a ha => ⟨hfootTreeOut a ha, fun hs => (hstaticBelow a hs).2.2 ha⟩, hcores0⟩
  obtain ⟨mid, midHeap, midS, midXTree, midSlot, midName, midXCore, midXTerm, cLoop, hrLoop, hId⟩ :=
    initLinkChainLoop_runs hH hcoreImpl htermImpl htreeImpl hbind hcoreInput hG hGm
      hvalFwd hvalB hcapB hrecPtr hrecAt hthPtrAt hthValW
      (fun a ha => ⟨(hstaticBelow a ha).1, (hstaticBelow a ha).2.1⟩)
      hslotsBelow hnamesBelow hstBelow hdisjSN hdisjST hdisjNT hhandlesW
      hvw hwidth hhandleW hdW hw7 hreadoutBounds hgraphReadBounds hlevelCap hlinkAlloc hroom
      C.d 0 (Nat.zero_add C.d) sInit heap s0 xTree slot0 name0 xCore xTerm hI0
  obtain ⟨_, h31d, h0d, h3d, h9d, h10d, h11d, h19d, h20d, h22d, h23d, h24d, h29d, h30d,
      hloD, hhiD, hzD, hstatEqD, _, hinvD, htreeOutD, hcoresD⟩ := hId
  have hlastLvStatic : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
      C.d m L G Ttree recPtr extraStatic (levelTable + C.d) := Or.inr (Or.inl ⟨by omega, by omega⟩)
  have hlastBrStatic : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
      C.d m L G Ttree recPtr extraStatic (branchTable + C.d) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hlhEq : mid.mem (levelTable + C.d) = st.mem (levelTable + C.d) := hstatEqD _ hlastLvStatic
  have hlbrEq : mid.mem (branchTable + C.d) = chain.lastBran := hcoresD.2.1
  let l1 := { mid with regs := Function.update mid.regs 33 midHeap }
  have hrL1 : Runs w p ω (.assign 33 (.reg 3)) mid .normal l1 2 :=
    runs_assign_iff.mpr ⟨midHeap, by simp [Expr.eval, h3d], rfl, rfl, rfl⟩
  have hlastRoom4 : midHeap + 4 < 2 ^ w := by
    have : (C.d + 1) * levelSpace = C.d * levelSpace + levelSpace := by ring
    omega
  have hlbrValW : chain.lastBran < 2 ^ w := by
    have := (hhandlesW C.d le_rfl).2
    rw [← hstatEqD _ hlastBrStatic, hlbrEq] at this; exact this
  obtain ⟨l2, retL1, cLRF, yTermFin, hrL2, hretL2, hregsL2, hrepTerm2, hlsfLast, hrespLast, _⟩ :=
    run_last_readForest (ω := ω) (st := l1) htermImpl
      (hlhEq ▸ hcoresD.2.2.1) (fun a ha => (hcoresD.2.2.2 a (hlhEq.symm ▸ ha)).1)
      hH.2.2.2.2.2.1
      (by simp [l1, h3d]) (by simp [l1, h29d]) (by simp [l1, h30d]) (by simp [l1, h31d])
      hlhEq hlbrEq
      (by have := (hstaticBelow _ hlastLvStatic).1; omega)
      (by have := (hstaticBelow _ hlastBrStatic).1; omega)
      (hhandlesW C.d le_rfl).1 hlbrValW hzD hlastRoom4
  have hframeLast (a : ℕ) (ha : a < midHeap) (hnt : ¬ Rterm.foot (st.mem (levelTable + C.d)) midXTerm a) :
      l2.mem a = mid.mem a := hrespLast.2.2.2.1 a ha hnt
  have hstatEqL2 : ∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
      C.d m L G Ttree recPtr extraStatic a → l2.mem a = st.mem a := fun a ha =>
    (hframeLast a ((hstaticBelow a ha).1.trans_le hloD)
      (fun hf => (hcoresD.2.2.2 a (hlhEq.symm ▸ hf)).2.2.1 ha)).trans (hstatEqD a ha)
  have hinvL2 : InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
      ((Finset.range C.d).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
      midS midXTree midSlot midName retL1 l2.mem := by
    obtain ⟨hsn, hinsSub, hrepT, hfootT, htabT, hwitT, hstT, hzT⟩ := hinvD
    have hlocT := htreeImpl.1 treeHandle midS midXTree mid.mem l2.mem (fun a ha =>
      (hframeLast a (hfootT a ha) (fun hf => (hcoresD.2.2.2 a (hlhEq.symm ▸ hf)).2.2.2.1 ha)).symm)
    refine ⟨hsn, hinsSub, hlocT.1 hrepT, fun a ha => (hfootT a ha).trans_le hrespLast.1,
      htabT.congr
        (fun e he => hframeLast _ (by omega) (fun hf => ((hcoresD.2.2.2 _ (hlhEq.symm ▸ hf)).2.1.1).elim (by omega) (by omega)))
        (fun k hk => hframeLast _ (by omega) (fun hf => ((hcoresD.2.2.2 _ (hlhEq.symm ▸ hf)).2.1.2.1).elim (by omega) (by omega))),
      hwitT, fun e he => ?_, hzT⟩
    obtain ⟨ts, fs, ds, hW, _, hnamed, _⟩ := hwitT
    have hsLt : midSlot e < 2 * G.n := (hsn ▸ (hnamed.forward e he).2.1).2
    rw [hframeLast _ (by omega) (fun hf => ((hcoresD.2.2.2 _ (hlhEq.symm ▸ hf)).2.1.2.2).elim (by omega) (by omega))]
    exact hstT e he
  let fBaseLast := l2.mem (midHeap + 1)
  have hactiveLast : chain.toTreeChain.activeLSF C.d = chain.lastLSFs chain.lastBran := by
    simp [ChainState.toTreeChain, TreeChain.activeLSF]
  have hFLast : DynGraphAt l2.mem fBaseLast vcLast ecLast (chain.toTreeChain.activeLSF C.d).F.F := by
    rw [hactiveLast]; exact hlsfLast.2.1
  have hlastB := hlastReadBounds l2.mem midHeap retL1 vcLast ecLast yTermFin hloD hrespLast.1 hlsfLast
  let l3 := { l2 with regs := Function.update l2.regs 25 fBaseLast }
  have hrL3 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 33) (.const 1)))) l2 .normal l3 5 :=
    runs_assign_iff.mpr ⟨fBaseLast, by
      simp [Expr.eval, BinOp.eval, hregsL2 33 (by decide), l1, fBaseLast,
        show 1 < 2 ^ w by omega, show midHeap + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hGLast : DynGraphAt l3.mem rootBase G.n G.m G :=
    DynGraphAt.of_agree hG (fun a haLo haHi => hstatEqL2 a (Or.inl ⟨haLo, haHi⟩))
  have hFdSub : (chain.toTreeChain.activeLSF C.d).F.F.E ⊆ Ttree.E := activeLSF_subset_chainTree le_rfl
  have hretL1Room : retL1 + (chain.toTreeChain.activeLSF C.d).F.F.m * linkSpace < 2 ^ w := by
    have h1 : retL1 ≤ midHeap + 4 := hrespLast.2.1
    have h2 : (C.d + 1) * levelSpace = C.d * levelSpace + levelSpace := by ring
    omega
  have hforestOutLast : ∀ a, fBaseLast ≤ a → a < fBaseLast + dynGraphSize vcLast ecLast →
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ Rtree.foot treeHandle midXTree a := by
    intro a haLo haHi
    rcases hlastB.2 a haLo haHi with hft | ⟨hge, _⟩
    · rcases hrespLast.2.2.2.2 a hft with hold | ⟨hge, _⟩
      · exact ⟨(hcoresD.2.2.2 a (hlhEq.symm ▸ hold)).2.1, (hcoresD.2.2.2 a (hlhEq.symm ▸ hold)).2.2.2.1⟩
      · exact ⟨⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
          fun hf => by have := hinvD.2.2.2.1 a hf; omega⟩
    · exact ⟨⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
        fun hf => by have := hinvD.2.2.2.1 a hf; omega⟩
  obtain ⟨out, retFin, cLinkLast, sFin, yTreeFin, slotFin, nameFin, hrL4, hretFin, _,
      hinvFin, hfootOutFin, hrespFin, _⟩ :=
    initLinkForestEdges_runs (ω := ω) (st := l3) htreeImpl hbind hTForest hTEnds
      hGLast hFLast hTG (fun e he => hGm ▸ hG.2.2.1 e he) hFdSub (initChain_prefix_disjoint hH le_rfl) hinvL2
      (fun e he => hvalFwd e (hFdSub he)) (fun e he => hvalB e (hFdSub he)) hcapB
      (by simp [l3, hregsL2 0 (by decide), l1, h0d])
      (by simp [l3, hretL2])
      (by simp [l3, hregsL2 9 (by decide), l1, h9d])
      (by simp [l3, hregsL2 10 (by decide), l1, h10d])
      (by simp [l3, hregsL2 11 (by decide), l1, h11d])
      (by simp [l3, hregsL2 19 (by decide), l1, h19d])
      (by simp [l3, hregsL2 20 (by decide), l1, h20d])
      (by simp [l3, hregsL2 22 (by decide), l1, h22d])
      (by simp [l3, hregsL2 23 (by decide), l1, h23d])
      (by simp [l3, hregsL2 24 (by decide), l1, h24d])
      (by simp [l3])
      (fun e he => (hstatEqL2 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
        by have := hG.2.2.1 e (hTG (hFdSub he)); omega⟩))))).trans (hrecPtr e (hFdSub he)))
      (fun e he => (hrecAt e (hFdSub he)).congr (fun a hloA hhiA =>
        hstatEqL2 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hFdSub he, hloA, by omega⟩))))))))
      (fun e he => (hstatEqL2 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
        by have := hG.2.2.1 e (hTG (hFdSub he)); omega⟩)))))).trans (hthPtrAt e (hFdSub he)))
      (fun e he => by
        have h1 := (hstaticBelow (recPtr e + (2 + 4 * L) - 1)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hFdSub he, by omega, by omega⟩))))))).1
        have := hrespLast.1; omega)
      (fun e he => ((hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
        by have := hG.2.2.1 e (hTG (hFdSub he)); omega⟩))))).1.trans_le hloD).trans_le hrespLast.1)
      (fun e he => ((hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
        by have := hG.2.2.1 e (hTG (hFdSub he)); omega⟩)))))).1.trans_le hloD).trans_le hrespLast.1)
      (fun e he => hthValW e (hFdSub he))
      (hrootBelow.trans (hloD.trans hrespLast.1)) hlastB.1
      (hslotsBelow.trans (hloD.trans hrespLast.1))
      (hnamesBelow.trans (hloD.trans hrespLast.1))
      (hstBelow.trans (hloD.trans hrespLast.1))
      hdisjSN hdisjST hdisjNT (fun a ha => (htreeOutD a ha).1)
      (fun a haLo haHi => ⟨(hstaticBelow a (Or.inl ⟨haLo, haHi⟩)).2.1,
        fun hf => (htreeOutD a hf).2 (Or.inl ⟨haLo, haHi⟩)⟩)
      hforestOutLast
      (fun e he =>
        let hA : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic (edgeRecords + e) :=
          Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by have := hG.2.2.1 e (hTG (hFdSub he)); omega⟩)))
        ⟨(hstaticBelow _ hA).2.1, fun hf => (htreeOutD _ hf).2 hA⟩)
      (fun e he a hloA hhiA =>
        let hA : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a :=
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hFdSub he, hloA, hhiA⟩)))))
        ⟨(hstaticBelow a hA).2.1, fun hf => (htreeOutD a hf).2 hA⟩)
      (fun e he =>
        let hA : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic (edgeThresholds + e) :=
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by have := hG.2.2.1 e (hTG (hFdSub he)); omega⟩))))
        ⟨(hstaticBelow _ hA).2.1, fun hf => (htreeOutD _ hf).2 hA⟩)
      hvw hwidth hhandleW hw7 hrespLast.2.2.1
      (fun e he cur hlo' hhi' => hlinkAlloc e (hFdSub he) cur (hloD.trans (hrespLast.1.trans hlo'))
        (by
          have h1 : retL1 ≤ midHeap + 4 := hrespLast.2.1
          have h2 : (C.d + 1) * levelSpace = C.d * levelSpace + levelSpace := by ring
          omega))
      hretL1Room
  rw [initChain_prefix_union C.d] at hinvFin
  have hretFinLe : retFin ≤ heap + (C.d + 1) * levelSpace := by
    have h1 : retL1 ≤ midHeap + 4 := hrespLast.2.1
    have h2 : retFin ≤ retL1 + (chain.toTreeChain.activeLSF C.d).F.F.m * linkSpace := hrespFin.2.1
    have h3 : (C.d + 1) * levelSpace = C.d * levelSpace + levelSpace := by ring
    omega
  refine ⟨out, retFin, _, sFin, yTreeFin, slotFin, nameFin, midXCore, yTermFin,
    runs_seq_iff.mpr (Or.inr ⟨sInit, 2, _, hrInit,
      runs_seq_iff.mpr (Or.inr ⟨mid, cLoop, _, hrLoop,
        runs_seq_iff.mpr (Or.inr ⟨l1, 2, _, hrL1,
          runs_seq_iff.mpr (Or.inr ⟨l2, cLRF, _, hrL2,
            runs_seq_iff.mpr (Or.inr ⟨l3, 5, cLinkLast, hrL3, hrL4, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hretFin, hinvFin, ?_, ?_, ?_, ?_, ?_, hrespFin.2.2.1,
    hloD.trans (hrespLast.1.trans hrespFin.1), hretFinLe, ?_, ?_⟩
  · intro a ha hex
    have hst : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hex)))))
    rcases hrespFin.2.2.2.2 a ha with (hold | hnot) | ⟨hge, _⟩
    · exact (htreeOutD a hold).2 hst
    · exact hnot (hstaticBelow a hst).2.1
    · have := (hstaticBelow a hst).1; have := hrespLast.1; omega
  · intro i hi
    have hci := hcoresD.1 i hi
    have hchD : mid.mem (levelTable + i) = st.mem (levelTable + i) :=
      hstatEqD _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hlocC := (hcoreImpl i hi G.n G.m).1 (st.mem (levelTable + i)) (chain.scState i)
      (midXCore i) mid.mem out.mem (fun a ha => by
        have hf := hci.2.2 a (hchD.symm ▸ ha)
        have h1 : l2.mem a = mid.mem a :=
          hframeLast a hf.1 (fun hft => hf.2.2.2.2.2 (hlhEq.symm ▸ hft))
        have h2 : out.mem a = l2.mem a :=
          hrespFin.2.2.2.1 a (hf.1.trans_le hrespLast.1) (fun h => h.elim hf.2.2.2.1 (fun hn => hn hf.2.1))
        exact (h2.trans h1).symm)
    refine ⟨hlocC.1 (hchD ▸ hci.2.1), fun a ha => ?_⟩
    have hf := hci.2.2 a (hchD.symm ▸ ha)
    exact ⟨(hf.1.trans_le hrespLast.1).trans_le hrespFin.1,
      fun hex => hf.2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hex))))))⟩
  · have hlocL := htermImpl.1 (st.mem (levelTable + C.d))
      (chain.lastK, chain.lastLSFs) yTermFin l2.mem out.mem (fun a ha => by
        rcases hrespLast.2.2.2.2 a ha with hold | ⟨hge, hlt⟩
        · have hf := hcoresD.2.2.2 a (hlhEq.symm ▸ hold)
          exact (hrespFin.2.2.2.1 a (hf.1.trans_le hrespLast.1)
            (fun h => h.elim hf.2.2.2.1 (fun hn => hn hf.2.1))).symm
        · exact (hrespFin.2.2.2.1 a hlt (fun h => h.elim
            (fun ht => by have := hinvD.2.2.2.1 a ht; omega)
            (fun hn => hn ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩))).symm)
    exact hlocL.1 hrepTerm2
  · intro a ha
    rcases hrespLast.2.2.2.2 a ha with hold | ⟨hge, hlt⟩
    · have hf := hcoresD.2.2.2 a (hlhEq.symm ▸ hold)
      exact ⟨(hf.1.trans_le hrespLast.1).trans_le hrespFin.1,
        fun hex => hf.2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hex))))))⟩
    · refine ⟨hlt.trans_le hrespFin.1, fun hex => ?_⟩
      have := (hstaticBelow a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hex))))))).1
      omega
  · intro a ha
    have hlt := ((hstaticBelow a ha).1.trans_le hloD).trans_le hrespLast.1
    exact (hrespFin.2.2.2.1 a hlt (fun h => h.elim
      (fun hf => (htreeOutD a hf).2 ha)
      (fun hn => hn (hstaticBelow a ha).2.1))).trans (hstatEqL2 a ha)
  · intro a ha
    refine ⟨hfootOutFin a ha, fun hst => ?_⟩
    rcases hrespFin.2.2.2.2 a ha with (hold | hnot) | ⟨hge, _⟩
    · exact (htreeOutD a hold).2 hst
    · exact hnot (hfootOutFin a ha)
    · have := (hstaticBelow a hst).1; have := hrespLast.1; omega
  · have hstatOut : ∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a → out.mem a = st.mem a := fun a ha => by
      have hlt := ((hstaticBelow a ha).1.trans_le hloD).trans_le hrespLast.1
      exact (hrespFin.2.2.2.1 a hlt (fun h => h.elim
        (fun hf => (htreeOutD a hf).2 ha)
        (fun hn => hn (hstaticBelow a ha).2.1))).trans (hstatEqL2 a ha)
    have hlvOut (i : ℕ) (hi : i ≤ C.d) : out.mem (levelTable + i) = st.mem (levelTable + i) :=
      hstatOut _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hbrOut (i : ℕ) (hi : i ≤ C.d) : out.mem (branchTable + i) = st.mem (branchTable + i) :=
      hstatOut _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
    · have hci := hcoresD.1 i hi
      have hchD : mid.mem (levelTable + i) = st.mem (levelTable + i) :=
        hstatEqD _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
      have hbrD : mid.mem (branchTable + i) = st.mem (branchTable + i) :=
        hstatEqD _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      have hlocC := (hcoreImpl i hi G.n G.m).1 (st.mem (levelTable + i)) (chain.scState i)
        (midXCore i) mid.mem out.mem (fun a ha => by
          have hf := hci.2.2 a (hchD.symm ▸ ha)
          have h1 : l2.mem a = mid.mem a :=
            hframeLast a hf.1 (fun hft => hf.2.2.2.2.2 (hlhEq.symm ▸ hft))
          have h2 : out.mem a = l2.mem a :=
            hrespFin.2.2.2.1 a (hf.1.trans_le hrespLast.1) (fun h => h.elim hf.2.2.2.1 (fun hn => hn hf.2.1))
          exact (h2.trans h1).symm)
      rw [hlvOut i hi.le, hbrOut i hi.le]
      refine ⟨hbrD.symm.trans hci.1, hlocC.1 (hchD ▸ hci.2.1), fun a ha => ?_⟩
      have hf := hci.2.2 a (hchD.symm ▸ ha)
      refine ⟨(hf.1.trans_le hrespLast.1).trans_le hrespFin.1, hf.2.1, hf.2.2.1, ?_, ?_, ?_⟩
      · intro ht
        rcases hrespFin.2.2.2.2 a ht with (hold | hnot) | ⟨hge, _⟩
        · exact hf.2.2.2.1 hold
        · exact hnot hf.2.1
        · have := hrespLast.1; omega
      · intro j hj hne
        rw [hlvOut j hj.le]
        have hcjD : mid.mem (levelTable + j) = st.mem (levelTable + j) :=
          hstatEqD _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
        exact fun hfj => hf.2.2.2.2.1 j hj hne (hcjD.symm ▸ hfj)
      · rw [hlvOut C.d le_rfl]
        intro hft
        rcases hrespLast.2.2.2.2 a hft with hold | ⟨hge, _⟩
        · exact hf.2.2.2.2.2 (hlhEq.symm ▸ hold)
        · omega
    · rw [hbrOut C.d le_rfl]
      exact (hstatEqD _ hlastBrStatic).symm.trans hlbrEq
    · rw [hlvOut C.d le_rfl]
      have hlocL := htermImpl.1 (st.mem (levelTable + C.d))
        (chain.lastK, chain.lastLSFs) yTermFin l2.mem out.mem (fun a ha => by
          rcases hrespLast.2.2.2.2 a ha with hold | ⟨hge, hlt⟩
          · have hf := hcoresD.2.2.2 a (hlhEq.symm ▸ hold)
            exact (hrespFin.2.2.2.1 a (hf.1.trans_le hrespLast.1)
              (fun h => h.elim hf.2.2.2.1 (fun hn => hn hf.2.1))).symm
          · exact (hrespFin.2.2.2.1 a hlt (fun h => h.elim
              (fun ht => by have := hinvD.2.2.2.1 a ht; omega)
              (fun hn => hn ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩))).symm)
      exact hlocL.1 hrepTerm2
    · intro a ha
      rw [hlvOut C.d le_rfl] at ha
      rcases hrespLast.2.2.2.2 a ha with hold | ⟨hge, hlt⟩
      · have hf := hcoresD.2.2.2 a (hlhEq.symm ▸ hold)
        refine ⟨(hf.1.trans_le hrespLast.1).trans_le hrespFin.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
        · intro ht
          rcases hrespFin.2.2.2.2 a ht with (holdT | hnot) | ⟨hgeT, _⟩
          · exact hf.2.2.2.1 holdT
          · exact hnot hf.2.1
          · have := hrespLast.1; omega
        · intro j hj
          rw [hlvOut j hj.le]
          have hcjD : mid.mem (levelTable + j) = st.mem (levelTable + j) :=
            hstatEqD _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
          exact fun hfj => hf.2.2.2.2 j hj (hcjD.symm ▸ hfj)
      · refine ⟨hlt.trans_le hrespFin.1,
          ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
          fun hst => by have := (hstaticBelow a hst).1; omega, ?_, ?_⟩
        · intro ht
          rcases hrespFin.2.2.2.2 a ht with (holdT | hnot) | ⟨hgeT, _⟩
          · have := hinvD.2.2.2.1 a holdT; omega
          · exact hnot ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · omega
        · intro j hj
          rw [hlvOut j hj.le]
          have hcjD : mid.mem (levelTable + j) = st.mem (levelTable + j) :=
            hstatEqD _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
          intro hfj
          have := ((hcoresD.1 j hj).2.2 a (hcjD.symm ▸ hfj)).1
          omega

/-- `initLinkChainForests` only writes registers below `36`. -/
theorem initLinkChainForests_preserves_regs
    {w readCore readGraph readLast linkOp bind r cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State}
    (hr : 36 ≤ r)
    (hrun : Runs w p ω (initLinkChainForests readCore readGraph readLast linkOp bind)
      st .normal out cost) :
    out.regs r = st.regs r :=
  runs_preserves_above hr (by rfl) hrun

end MinCostFlow.MinRatio
