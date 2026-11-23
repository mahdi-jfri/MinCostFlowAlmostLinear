module

public import MinCostFlow.MinRatio.WireInitLinkBaseKFBL
import MinCostFlow.MinRatio.InitPathTreeEdges
import Mathlib.Tactic.Ring

/-!
# Core-level forest linking loop (`WireInitLinkLoopK`)

Executes the `C.d`-iteration loop of `initLinkChainForests` under
`sparseCoreOrdMachineContractKFBL` and `SparseCoreReadoutFootAt` at the caps `(G.n, G.m)` of the
input graph, linking the active forests of levels `0 .. C.d - 1` into the Section 6
path tree with exact space and telescoping cost + potential bounds.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program LastLevelProgram

theorem initLinkChainLoopK_runs
    {w L depth treeConst initCore initTree bind
      treeHandle rootBase levelTable branchTable slots names slotThresholds
      edgeRecords edgeThresholds m ec0 heap linkSpace capExp capLimit vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {C : ChainParams}
    {P : SparseCoreOrdParams} {coreAlloc : ℕ → List ℕ → ℕ} {lvlM : ℕ → ℕ}
    {treeAlloc : ℕ → ℕ → List ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {Rtree : DSRep PathTreeState}
    {opCore opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {initMem : ℕ → ℕ}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} {val : ℕ → PathEdgeValue} {B : ℤ}
    {recPtr thPtr : ℕ → ℕ} {extraStatic : ℕ → Prop}
    (hFour : fmt.limbBits = 4)
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hcoreImpl : ∀ i < C.d,
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0
          capExp P coreAlloc) ∧
      SparseCoreReadoutFootAt fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0 capExp P
        coreAlloc Rcore p opCore)
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreInput : ∀ i < C.d,
      SparseCoreOrdInput T C.k (lvlM i) N₀ (chain.scState i) (chain.G i) (chain.levelOrd i) (chain.updCount i))
    (hG : DynGraphAt initMem rootBase G.n ec0 G) (hELt : ∀ e ∈ G.E, e < m)
    (hrootInStatic : ∀ a, rootBase ≤ a → a < rootBase + dynGraphSize G.n ec0 → extraStatic a)
    (hvalFwd : ∀ e ∈ chain.toTreeChain.chainTree.E, (val e).forward = true)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      |(val e).gradient| ≤ B ∧ |(val e).length| ≤ B ∧ |(val e).flow| ≤ B ∧ |(val e).detector| ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity 4 L : ℤ))
    (hrecPtr : ∀ e ∈ chain.toTreeChain.chainTree.E, initMem (edgeRecords + e) = recPtr e)
    (hrecAt : ∀ e ∈ chain.toTreeChain.chainTree.E, PathEdgeAt initMem (recPtr e) 4 L (some (val e)))
    (hthPtrAt : ∀ e ∈ chain.toTreeChain.chainTree.E, initMem (edgeThresholds + e) = thPtr e)
    (hthValW : ∀ e ∈ chain.toTreeChain.chainTree.E, thPtr e < 2 ^ w)
    (hstaticBelow : ∀ a, InitChainStaticAddr rootBase levelTable branchTable
      edgeRecords edgeThresholds C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a →
      a < heap ∧ OutsideInitSlotTables slots names slotThresholds m G.n a)
    (hslotsBelow : slots + m ≤ heap) (hnamesBelow : names + 2 * G.n ≤ heap)
    (hstBelow : slotThresholds + 2 * G.n ≤ heap)
    (hdisjSN : slots + m ≤ names ∨ names + 2 * G.n ≤ slots)
    (hdisjST : slots + m ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ slots)
    (hdisjNT : names + 2 * G.n ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ names)
    (hhandlesW : ∀ i ≤ C.d, initMem (levelTable + i) < 2 ^ w ∧ initMem (branchTable + i) < 2 ^ w)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hhandleW : treeHandle < 2 ^ w) (hdW : C.d < 2 ^ w) (hw7 : 7 < 2 ^ w)
    (hlinkAlloc : ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
      heap ≤ cur → cur ≤ heap + initLinkChainSpace C.d m linkSpace →
      treeAlloc 0 G.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, cur] ≤ linkSpace)
    (hroom : heap + initLinkChainSpace C.d m linkSpace < 2 ^ w)
    (rem i : ℕ) (hsum : i + rem = C.d)
    (curSt : State) (curHeap : ℕ) (curS : PathTreeState) (curXTree : Rtree.τ)
    (curSlot curName : ℕ → ℕ) (curXCore : ℕ → Rcore.τ) (curXTerm : ℕ)
    (hI : InitChainLoopInvK Rcore (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E)
      Rtree chain treeHandle rootBase levelTable branchTable slots names slotThresholds
      edgeRecords edgeThresholds m ec0 L heap linkSpace capLimit G val B recPtr thPtr extraStatic
      initMem i curSt curHeap curS curXTree curSlot curName curXCore curXTerm) :
    let Rterm := lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E
    ∃ (mid : State) (midHeap : ℕ) (midS : PathTreeState) (midXTree : Rtree.τ)
      (midSlot midName : ℕ → ℕ) (midXCore : ℕ → Rcore.τ) (midXTerm cLoop : ℕ),
      Runs w p ω (.loop (.bin .lt (.reg 32) (.reg 31)) (
        .assign 33 (.reg 3) ;;
        .call 3 (opCore 2) [.load (.bin .add (.reg 29) (.reg 32)),
          .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3] ;;
        .assign 25 (.load (.bin .add (.reg 33) (.const 1))) ;;
        initLinkForestEdges (opTree 0) bind ;;
        .assign 33 (.reg 3) ;;
        .call 3 (opCore 3) [.load (.bin .add (.reg 29) (.reg 32)),
          .load (.bin .add (.reg 30) (.reg 32)), .reg 3] ;;
        .assign 34 (.load (.reg 33)) ;;
        .assign 32 (.bin .add (.reg 32) (.const 1)))) curSt .normal mid cLoop ∧
      InitChainLoopInvK Rcore Rterm Rtree chain treeHandle rootBase levelTable branchTable
        slots names slotThresholds edgeRecords edgeThresholds m ec0 L heap linkSpace capLimit
        G val B recPtr thPtr extraStatic initMem C.d mid midHeap midS midXTree midSlot midName
        midXCore midXTerm ∧
      (∀ r, 36 ≤ r → mid.regs r = curSt.regs r) ∧
      cLoop + Rtree.phi treeHandle midXTree mid.mem +
          (∑ j : Fin C.d, Rcore.phi (mid.mem (levelTable + j.val)) (midXCore j.val) mid.mem) ≤
        (C.d - i) * (2 * P.readout + 80) +
          (∑ j ∈ Finset.range C.d, if i ≤ j then
            (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) +
          Rtree.phi treeHandle curXTree curSt.mem +
          (∑ j : Fin C.d, Rcore.phi (curSt.mem (levelTable + j.val)) (curXCore j.val) curSt.mem) + 5 := by
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
  induction rem generalizing i curSt curHeap curS curXTree curSlot curName curXCore curXTerm with
  | zero =>
    have hieq : i = C.d := by omega
    subst hieq
    refine ⟨curSt, curHeap, curS, curXTree, curSlot, curName, curXCore, curXTerm, 4,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hI.r32, hI.r31], rfl, rfl,
        by simp [Expr.size]⟩),
      hI, fun _ _ => rfl, ?_⟩
    have hzero : (∑ j ∈ Finset.range C.d, if C.d ≤ j then
        (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => by rw [Finset.mem_range] at hj; simp [show ¬ C.d ≤ j by omega]
    omega
  | succ rem ih =>
    have hi : i < C.d := by omega
    obtain ⟨vc, ec, hvc, hec, hcapI, hGi, hGiEnd⟩ := hI.curG
    rw [hvc, hec] at hcapI hGi hGiEnd
    have hcoreLocal : Rcore.Local := (hcoreImpl i hi).1.1
    have hlvStat : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic (levelTable + i) := Or.inr (Or.inl ⟨by omega, by omega⟩)
    have hbrStat : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic (branchTable + i) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hchEq : curSt.mem (levelTable + i) = initMem (levelTable + i) := hI.staticEq _ hlvStat
    have hbrEq : curSt.mem (branchTable + i) = chain.bran i := (hI.cores.1 i hi).1
    have hbrLt : chain.bran i < C.k := (hH.2.2.2.2.1 i hi).1
    have hbrValW : chain.bran i < 2 ^ w := by
      have := (hhandlesW i hi.le).2
      rw [← hI.staticEq _ hbrStat, hbrEq] at this; exact this
    have hSumPrefLe : (∑ j ∈ Finset.range i, (chain.toTreeChain.activeLSF j).F.F.m) +
        (chain.toTreeChain.activeLSF i).F.F.m ≤ m := by
      rw [← Finset.sum_range_succ]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => Nat.zero_le _)).trans hSumAllLe
    have hMulPrefLe : ((∑ j ∈ Finset.range i, (chain.toTreeChain.activeLSF j).F.F.m) +
        (chain.toTreeChain.activeLSF i).F.F.m) * linkSpace ≤ m * linkSpace :=
      Nat.mul_le_mul_right linkSpace hSumPrefLe
    have hCurLo := hI.heapLo
    have hCurHi := hI.heapHi
    -- Step 1: reg 33 := curHeap; call opCore 2
    let s1 := { curSt with regs := Function.update curSt.regs 33 curHeap }
    have hr1 : Runs w p ω (.assign 33 (.reg 3)) curSt .normal s1 2 :=
      runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, hI.r3], rfl, rfl, rfl⟩
    have hroom5 : curHeap + 5 < 2 ^ w := by
      have h1 : (∑ j ∈ Finset.range i, (chain.toTreeChain.activeLSF j).F.F.m) * linkSpace ≤ m * linkSpace :=
        Nat.mul_le_mul_right linkSpace (by omega)
      dsimp only [initLinkChainSpace] at hroom; omega
    obtain ⟨s2, ret1, cRF, yCoreI1, fv, fe, Lw, hr2, hret1, hregs2, hrepI1, hlsf1, hfEnd0, hfIn,
        hresp1, hcRF⟩ :=
      run_core_readForestKFBL (ω := ω) (st := s1) hFour (hcoreImpl i hi).2
        (hchEq ▸ (hI.cores.1 i hi).2.1)
        (fun a ha => ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ ha)).1)
        hbrLt (hcoreInput i hi) hGi hGiEnd
        (by simp [s1, hI.r3]) (by simp [s1, hI.r29]) (by simp [s1, hI.r30])
        (by simp [s1, hI.r32]) (by simp [s1])
        hchEq hbrEq (by have := (hstaticBelow _ hlvStat).1; omega)
        (by have := (hstaticBelow _ hbrStat).1; omega)
        (hhandlesW i hi.le).1 hbrValW
        (by
          have : 0 < dynGraphSize G.n ec0 := by unfold dynGraphSize; omega
          omega)
        hI.zeroFrom hroom5
    have hframe1 (a : ℕ) (ha : a < curHeap) (hnf : ¬ Rcore.foot (initMem (levelTable + i)) (curXCore i) a) :
        s2.mem a = curSt.mem a := hresp1.2.2.2.1 a ha hnf
    have hstat2 (a : ℕ) (ha : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a) : s2.mem a = initMem a :=
      (hframe1 a ((hstaticBelow a ha).1.trans_le hI.heapLo)
        (fun hf => ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hf)).2.2.1 ha)).trans (hI.staticEq a ha)
    let fBase := s2.mem (curHeap + 1)
    let Fi := (chain.toTreeChain.activeLSF i).F.F
    have hFiEq : (T.lsfs (chain.scState i) (chain.bran i)).F.F = Fi := by
      simp [Fi, TreeChain.activeLSF, ChainState.toTreeChain, hi]
    have hFiDG : DynGraphAt s2.mem fBase fv fe Fi := hFiEq ▸ hlsf1.2.1
    have hfEnd : fBase + dynGraphSize fv fe ≤ ret1 := hfEnd0.trans hresp1.1
    -- Step 2: reg 25 := mem[reg 33 + 1] = fBase
    let s3 := { s2 with regs := Function.update s2.regs 25 fBase }
    have hr3 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 33) (.const 1)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨fBase, by
        simp [Expr.eval, BinOp.eval, hregs2 33 (by decide), s1, show 1 < 2 ^ w by omega,
          show curHeap + 1 < 2 ^ w by omega, fBase], rfl, rfl, rfl⟩
    have htreeLoc1 := htreeImpl.1 treeHandle curS curXTree curSt.mem s2.mem (fun a ha =>
      (hframe1 a (hI.treeInv.2.2.2.1 a ha)
        (fun hf => ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hf)).2.2.2.1 ha)).symm)
    have hinv3 : InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
        ((Finset.range i).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
        curS curXTree curSlot curName ret1 s3.mem := by
      obtain ⟨hn, hsub', hrepT, hfootT, ⟨hslotT, hnameT⟩, hwt, hstT, hzrT⟩ := hI.treeInv
      refine ⟨hn, hsub', htreeLoc1.1 hrepT, fun a ha => (hfootT a ha).trans_le hresp1.1,
        ⟨fun e he => (hframe1 _ (by omega) (fun hf =>
            ((hI.cores.1 i hi).2.2 _ (hchEq.symm ▸ hf)).2.1.1.elim (by omega) (by omega))).trans (hslotT e he),
         fun k hk => (hframe1 _ (by omega) (fun hf =>
            ((hI.cores.1 i hi).2.2 _ (hchEq.symm ▸ hf)).2.1.2.1.elim (by omega) (by omega))).trans (hnameT k hk)⟩,
        hwt, fun e he => by
          have hsLt : curSlot e < 2 * G.n := by
            obtain ⟨ts, _, _, hW, _, hnm, _⟩ := hwt
            exact (hn ▸ (hnm.forward e he).2.1).2
          exact (hframe1 _ (by omega) (fun hf =>
            ((hI.cores.1 i hi).2.2 _ (hchEq.symm ▸ hf)).2.1.2.2.elim (by omega) (by omega))).trans (hstT e he),
        hzrT⟩
    have hfOut : ∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ Rtree.foot treeHandle curXTree a := by
      intro a hlo hhi
      rcases hfIn a hlo hhi with hfi | ⟨hloC, _⟩
      · rcases hresp1.2.2.2.2 a hfi with hold | ⟨hloC, _⟩
        · exact ⟨((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hold)).2.1,
            ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hold)).2.2.2.1⟩
        · exact ⟨⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
            fun hft => by have := hI.treeInv.2.2.2.1 a hft; omega⟩
      · exact ⟨⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
          fun hft => by have := hI.treeInv.2.2.2.1 a hft; omega⟩
    have hG3 : DynGraphAt s3.mem rootBase G.n ec0 G :=
      dynGraphAt_of_agree hG (fun a hlo hhi => hstat2 a (hrootStatic a hlo hhi))
    have hlinkRoom : ret1 + Fi.m * linkSpace < 2 ^ w := by
      have h1 := hresp1.2.1
      dsimp only [initLinkChainSpace] at hroom
      rw [Nat.add_mul] at hMulPrefLe
      dsimp only [Fi]
      omega
    -- Step 3: Link all edges of Fi via `initLinkForestEdges_runs`
    obtain ⟨s4, ret2, cLink, nextS, nextXTree, nextSlot, nextName,
        hr4, hs4_3, hregs4, hinv4, htreeOut4, hresp4, hcLink⟩ :=
      initLinkForestEdges_runs (edgeRecords := edgeRecords) (edgeThresholds := edgeThresholds)
        (ω := ω) (st := s3) htreeImpl hbind hTForest hTEnds hG3 hFiDG
        hTG hELt (activeLSF_subset_chainTree hi.le) (initChain_prefix_disjoint hH hi.le)
        hinv3 (fun e he => hvalFwd e (activeLSF_subset_chainTree hi.le he))
        (fun e he => hvalB e (activeLSF_subset_chainTree hi.le he)) (hFour ▸ hcapB)
        (by simp [s3, hregs2 0 (by decide), s1, hI.r0]) (by simp [s3, hret1])
        (by simp [s3, hregs2 9 (by decide), s1, hI.r9])
        (by simp [s3, hregs2 10 (by decide), s1, hI.r10])
        (by simp [s3, hregs2 11 (by decide), s1, hI.r11])
        (by simp [s3, hregs2 19 (by decide), s1, hI.r19])
        (by simp [s3, hregs2 20 (by decide), s1, hI.r20])
        (by simp [s3, hregs2 22 (by decide), s1, hI.r22])
        (by simp [s3, hregs2 23 (by decide), s1, hI.r23])
        (by simp [s3, hregs2 24 (by decide), s1, hI.r24]) (by simp [s3])
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have heM : e < m := hELt e (hTG heT)
          exact (hstat2 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans (hrecPtr e heT))
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          exact hFour ▸ (hrecAt e heT).congr (fun a hlo hhi =>
            hstat2 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, hlo, by omega⟩))))))))
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have heM : e < m := hELt e (hTG heT)
          exact (hstat2 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).trans (hthPtrAt e heT))
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have h := (hstaticBelow (recPtr e + (2 + 4 * L) - 1)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, by omega, by omega⟩))))))).1
          have := hresp1.1; omega)
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have heM : e < m := hELt e (hTG heT)
          have h := (hstaticBelow (edgeRecords + e) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).1
          have := hresp1.1; omega)
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have heM : e < m := hELt e (hTG heT)
          have h := (hstaticBelow (edgeThresholds + e) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).1
          have := hresp1.1; omega)
        (fun e he => hthValW e (activeLSF_subset_chainTree hi.le he))
        (by have := hresp1.1; omega) hfEnd
        (by have := hresp1.1; omega) (by have := hresp1.1; omega) (by have := hresp1.1; omega)
        hdisjSN hdisjST hdisjNT (fun a ha => (hI.treeOut a ha).1)
        (fun a hlo hhi => ⟨(hstaticBelow a (hrootStatic a hlo hhi)).2,
          fun hft => (hI.treeOut a hft).2 (hrootStatic a hlo hhi)⟩)
        hfOut
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have heM : e < m := hELt e (hTG heT)
          exact ⟨(hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).2,
            fun hft => (hI.treeOut _ hft).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))⟩)
        (fun e he a hlo hhi => by
          have heT := activeLSF_subset_chainTree hi.le he
          exact ⟨(hstaticBelow a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, hlo, hhi⟩))))))).2,
            fun hft => (hI.treeOut a hft).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, heT, hlo, hhi⟩))))))⟩)
        (fun e he => by
          have heT := activeLSF_subset_chainTree hi.le he
          have heM : e < m := hELt e (hTG heT)
          exact ⟨(hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).2,
            fun hft => (hI.treeOut _ hft).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))⟩)
        hvw (hFour ▸ hwidth) hhandleW hw7 hresp1.2.2.1
        (fun e he cur hlo hhi => hlinkAlloc e (activeLSF_subset_chainTree hi.le he) cur
          (hCurLo.trans (hresp1.1.trans hlo)) (by
            have h1 := hresp1.2.1; rw [Nat.add_mul] at hMulPrefLe
            dsimp only [initLinkChainSpace, Fi] at hhi ⊢; omega))
        hlinkRoom
    have hframe4 (a : ℕ) (ha : a < ret1) (hnt : ¬ Rtree.foot treeHandle curXTree a)
        (hout : OutsideInitSlotTables slots names slotThresholds m G.n a) :
        s4.mem a = s2.mem a :=
      hresp4.2.2.2.1 a ha (fun h => h.elim hnt (fun hno => hno hout))
    have hstat4 (a : ℕ) (ha : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a) : s4.mem a = initMem a :=
      (hframe4 a (((hstaticBelow a ha).1.trans_le hI.heapLo).trans_le hresp1.1)
        (fun hft => (hI.treeOut a hft).2 ha) (hstaticBelow a ha).2).trans (hstat2 a ha)
    have hfootI1Lt (a : ℕ) (ha : Rcore.foot (initMem (levelTable + i)) yCoreI1 a) : a < ret1 := by
      rcases hresp1.2.2.2.2 a ha with hold | ⟨_, hhi⟩
      · exact ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hold)).1.trans_le hresp1.1
      · exact hhi
    have hfootI1Disj4 (a : ℕ) (ha : Rcore.foot (initMem (levelTable + i)) yCoreI1 a) :
        ¬ Rtree.foot treeHandle curXTree a ∧ OutsideInitSlotTables slots names slotThresholds m G.n a := by
      rcases hresp1.2.2.2.2 a ha with hold | ⟨hlo, _⟩
      · exact ⟨((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hold)).2.2.2.1,
          ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hold)).2.1⟩
      · exact ⟨fun hft => by have := hI.treeInv.2.2.2.1 a hft; omega,
          ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩⟩
    have hcoreI1_loc4 := hcoreLocal (initMem (levelTable + i)) (chainLevelOrdAbs chain i) yCoreI1
      s2.mem s4.mem (fun a ha =>
        (hframe4 a (hfootI1Lt a ha) (hfootI1Disj4 a ha).1 (hfootI1Disj4 a ha).2).symm)
    -- Step 4: reg 33 := ret2; call opCore 3
    let s5 := { s4 with regs := Function.update s4.regs 33 ret2 }
    have hr5 : Runs w p ω (.assign 33 (.reg 3)) s4 .normal s5 2 :=
      runs_assign_iff.mpr ⟨ret2, by simp [Expr.eval, hs4_3], rfl, rfl, rfl⟩
    have hroom1 : ret2 + 1 < 2 ^ w := by
      have h1 := hresp1.2.1; have h2 := hresp4.2.1
      rw [Nat.add_mul] at hMulPrefLe; dsimp only [initLinkChainSpace] at hroom; dsimp only [Fi] at h2; omega
    have hregs4Keep (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) (h8 : r ≠ 8)
        (h21 : r ≠ 21) (h25 : r ≠ 25) (h26 : r ≠ 26) (h27 : r ≠ 27) (h28 : r ≠ 28) (h33 : r ≠ 33) :
        s4.regs r = curSt.regs r := by
      rw [hregs4 r h1 h2 h3 h4 h8 h21 h26 h27 h28]
      simp [s3, Function.update_of_ne h25, hregs2 r h3, s1, Function.update_of_ne h33]
    obtain ⟨s6, ret3, cRG, yCoreI2, gv, ge, hr6, hret3, hregs6, hrepI2, hGNext, hgv, hge,
        hGNextEnd0, -, hresp6, hcRG⟩ :=
      run_core_readGraphKFBL (ω := ω) (st := s5) (hcoreImpl i hi).2
        (hcoreI1_loc4.1 hrepI1) (fun a ha => (hfootI1Lt a ha).trans_le hresp4.1)
        hbrLt (hcoreInput i hi) (by simp [s5, hs4_3])
        (by simp [s5, hregs4Keep 29 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r29])
        (by simp [s5, hregs4Keep 30 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r30])
        (by simp [s5, hregs4Keep 32 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r32])
        (hstat4 _ hlvStat) ((hstat4 _ hbrStat).trans ((hI.staticEq _ hbrStat).symm.trans hbrEq))
        (by have := (hstaticBelow _ hlvStat).1; omega)
        (by have := (hstaticBelow _ hbrStat).1; omega)
        (hhandlesW i hi.le).1 hbrValW hresp4.2.2.1 hroom1
    have hcapNext : gv + ge + 2 ≤ capLimit := by rw [hgv, hge]; exact hcapI
    have hGNextEnd : s6.mem ret2 + dynGraphSize gv ge ≤ ret3 := hGNextEnd0.trans hresp6.1
    -- Step 5: reg 34 := mem[reg 33]; reg 32 := reg 32 + 1
    let s7 := { s6 with regs := Function.update s6.regs 34 (s6.mem ret2) }
    let s8 := { s7 with regs := Function.update s7.regs 32 (i + 1) }
    have hr7 : Runs w p ω (.assign 34 (.load (.reg 33))) s6 .normal s7 3 :=
      runs_assign_iff.mpr ⟨s6.mem ret2, by simp [Expr.eval, hregs6 33 (by decide), s5], rfl, rfl, rfl⟩
    have hr8 : Runs w p ω (.assign 32 (.bin .add (.reg 32) (.const 1))) s7 .normal s8 4 :=
      runs_assign_iff.mpr ⟨i + 1, by
        simp [Expr.eval, BinOp.eval, s7, hregs6 32 (by decide), s5,
          hregs4Keep 32 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hI.r32, show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hframe6 (a : ℕ) (ha : a < ret2) (hnf : ¬ Rcore.foot (initMem (levelTable + i)) yCoreI1 a) :
        s6.mem a = s4.mem a := hresp6.2.2.2.1 a ha hnf
    have hstat6 (a : ℕ) (ha : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a) : s6.mem a = initMem a := by
      have hnf : ¬ Rcore.foot (initMem (levelTable + i)) yCoreI1 a := fun hf => by
        rcases hresp1.2.2.2.2 a hf with hold | ⟨hlo, _⟩
        · exact ((hI.cores.1 i hi).2.2 a (hchEq.symm ▸ hold)).2.2.1 ha
        · have := (hstaticBelow a ha).1; have := hI.heapLo; omega
      exact (hframe6 a ((((hstaticBelow a ha).1.trans_le hI.heapLo).trans_le hresp1.1).trans_le hresp4.1) hnf).trans
        (hstat4 a ha)
    have hfootI1DisjTree4 (a : ℕ) (ha : Rcore.foot (initMem (levelTable + i)) yCoreI1 a) :
        ¬ Rtree.foot treeHandle nextXTree a := by
      intro hft
      rcases hresp4.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
      · exact hpre.elim (hfootI1Disj4 a ha).1 (fun hno => hno (hfootI1Disj4 a ha).2)
      · have := hfootI1Lt a ha; omega
    have htreeLoc6 := htreeImpl.1 treeHandle nextS nextXTree s4.mem s6.mem (fun a ha =>
      (hframe6 a (hinv4.2.2.2.1 a ha) (fun hf => hfootI1DisjTree4 a hf ha)).symm)
    have hinv8 : InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
        ((Finset.range (i + 1)).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
        nextS nextXTree nextSlot nextName ret3 s8.mem := by
      rw [← initChain_prefix_union i]
      obtain ⟨hn, hsub', hrepT, hfootT, ⟨hslotT, hnameT⟩, hwt, hstT, hzrT⟩ := hinv4
      refine ⟨hn, hsub', htreeLoc6.1 hrepT, fun a ha => (hfootT a ha).trans_le hresp6.1,
        ⟨fun e he => (hframe6 _ (by have := hresp1.1; have := hresp4.1; have := hI.heapLo; omega)
            (fun hf => (hfootI1Disj4 _ hf).2.1.elim (by omega) (by omega))).trans (hslotT e he),
         fun k hk => (hframe6 _ (by have := hresp1.1; have := hresp4.1; have := hI.heapLo; omega)
            (fun hf => (hfootI1Disj4 _ hf).2.2.1.elim (by omega) (by omega))).trans (hnameT k hk)⟩,
        hwt, fun e he => by
          have hsLt : nextSlot e < 2 * G.n := by
            obtain ⟨ts, _, _, hW, _, hnm, _⟩ := hwt; exact (hn ▸ (hnm.forward e he).2.1).2
          exact (hframe6 _ (by have := hresp1.1; have := hresp4.1; have := hI.heapLo; omega)
            (fun hf => (hfootI1Disj4 _ hf).2.2.2.elim (by omega) (by omega))).trans (hstT e he),
        hzrT⟩
    -- Build next core token function `nextXCore` and preserve all other cores + terminal
    let nextXCore : ℕ → Rcore.τ := fun j => if j = i then yCoreI2 else curXCore j
    have hfootI2_in (a : ℕ) (ha : Rcore.foot (initMem (levelTable + i)) yCoreI2 a) :
        Rcore.foot (initMem (levelTable + i)) (curXCore i) a ∨
        (curHeap ≤ a ∧ a < ret1) ∨ (ret2 ≤ a ∧ a < ret3) := by
      rcases hresp6.2.2.2.2 a ha with hy1 | ⟨hlo, hhi⟩
      · rcases hresp1.2.2.2.2 a hy1 with hx | ⟨hlo1, hhi1⟩
        · exact Or.inl hx
        · exact Or.inr (Or.inl ⟨hlo1, hhi1⟩)
      · exact Or.inr (Or.inr ⟨hlo, hhi⟩)
    have hOtherCore (j : ℕ) (hj : j < C.d) (hne : j ≠ i) :
        let hJ := initMem (levelTable + j)
        s8.mem (levelTable + j) = hJ ∧
        s8.mem (branchTable + j) = chain.bran j ∧
        Rcore.rep hJ (chainLevelOrdAbs chain j) (curXCore j) s8.mem ∧
        Rcore.phi hJ (curXCore j) s8.mem = Rcore.phi (curSt.mem (levelTable + j)) (curXCore j) curSt.mem ∧
        (∀ a, Rcore.foot hJ (curXCore j) a → a < curHeap ∧
          ¬ Rcore.foot (initMem (levelTable + i)) yCoreI2 a ∧ ¬ Rtree.foot treeHandle nextXTree a) := by
      have hlvJ : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic (levelTable + j) := Or.inr (Or.inl ⟨by omega, by omega⟩)
      have hbrJ : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic (branchTable + j) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      have hJeq : curSt.mem (levelTable + j) = initMem (levelTable + j) := hI.staticEq _ hlvJ
      obtain ⟨hbrOld, hrepOld, hfootOld⟩ := hI.cores.1 j hj
      have hagree (a : ℕ) (ha : Rcore.foot (initMem (levelTable + j)) (curXCore j) a) :
          s6.mem a = curSt.mem a := by
        have hfo := hfootOld a (hJeq.symm ▸ ha)
        have hnfI0 : ¬ Rcore.foot (initMem (levelTable + i)) (curXCore i) a :=
          fun hf => hfo.2.2.2.2.1 i hi hne.symm (hchEq.symm ▸ hf)
        have hnfI1 : ¬ Rcore.foot (initMem (levelTable + i)) yCoreI1 a := fun hf => by
          rcases hresp1.2.2.2.2 a hf with hx | ⟨hlo, _⟩
          · exact hnfI0 hx
          · have := hfo.1; omega
        rw [hframe6 a ((hfo.1.trans_le hresp1.1).trans_le hresp4.1) hnfI1,
          hframe4 a (hfo.1.trans_le hresp1.1) hfo.2.2.2.1 hfo.2.1,
          hframe1 a hfo.1 hnfI0]
      have hlocJ := hcoreLocal (initMem (levelTable + j)) (chainLevelOrdAbs chain j) (curXCore j)
        curSt.mem s6.mem (fun a ha => (hagree a ha).symm)
      refine ⟨hstat6 _ hlvJ, (hstat6 _ hbrJ).trans ((hI.staticEq _ hbrJ).symm.trans hbrOld),
        hlocJ.1 (hJeq ▸ hrepOld), by rw [hJeq]; exact hlocJ.2.symm, fun a ha => ?_⟩
      have hfo := hfootOld a (hJeq.symm ▸ ha)
      refine ⟨hfo.1, fun hf => ?_, fun hft => ?_⟩
      · rcases hfootI2_in a hf with hx | ⟨hlo, _⟩ | ⟨hlo, _⟩
        · exact hfo.2.2.2.2.1 i hi hne.symm (hchEq.symm ▸ hx)
        · have := hfo.1; omega
        · have := hfo.1; have := hresp1.1; have := hresp4.1; omega
      · rcases hresp4.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
        · exact hpre.elim hfo.2.2.2.1 (fun hno => hno hfo.2.1)
        · have := hfo.1; have := hresp1.1; omega
    have hTermPres :
        let hT := initMem (levelTable + C.d)
        s8.mem (levelTable + C.d) = hT ∧
        s8.mem (branchTable + C.d) = chain.lastBran ∧
        Rterm.rep hT (chain.lastK, chain.lastLSFs) curXTerm s8.mem ∧
        (∀ a, Rterm.foot hT curXTerm a → a < curHeap ∧
          ¬ Rcore.foot (initMem (levelTable + i)) yCoreI2 a ∧ ¬ Rtree.foot treeHandle nextXTree a) := by
      have hlvT : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic (levelTable + C.d) := Or.inr (Or.inl ⟨by omega, by omega⟩)
      have hbrT : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic (branchTable + C.d) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      have hTeq : curSt.mem (levelTable + C.d) = initMem (levelTable + C.d) := hI.staticEq _ hlvT
      obtain ⟨hbrOld, hrepOld, hfootOld⟩ := hI.cores.2
      have hagree (a : ℕ) (ha : Rterm.foot (initMem (levelTable + C.d)) curXTerm a) :
          s6.mem a = curSt.mem a := by
        have hfo := hfootOld a (hTeq.symm ▸ ha)
        have hnfI0 : ¬ Rcore.foot (initMem (levelTable + i)) (curXCore i) a :=
          fun hf => hfo.2.2.2.2 i hi (hchEq.symm ▸ hf)
        have hnfI1 : ¬ Rcore.foot (initMem (levelTable + i)) yCoreI1 a := fun hf => by
          rcases hresp1.2.2.2.2 a hf with hx | ⟨hlo, _⟩
          · exact hnfI0 hx
          · have := hfo.1; omega
        rw [hframe6 a ((hfo.1.trans_le hresp1.1).trans_le hresp4.1) hnfI1,
          hframe4 a (hfo.1.trans_le hresp1.1) hfo.2.2.2.1 hfo.2.1,
          hframe1 a hfo.1 hnfI0]
      have hlocT := htermLocal (initMem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) curXTerm
        curSt.mem s6.mem (fun a ha => (hagree a ha).symm)
      refine ⟨hstat6 _ hlvT, (hstat6 _ hbrT).trans ((hI.staticEq _ hbrT).symm.trans hbrOld),
        hlocT.1 (hTeq ▸ hrepOld), fun a ha => ?_⟩
      have hfo := hfootOld a (hTeq.symm ▸ ha)
      refine ⟨hfo.1, fun hf => ?_, fun hft => ?_⟩
      · rcases hfootI2_in a hf with hx | ⟨hlo, _⟩ | ⟨hlo, _⟩
        · exact hfo.2.2.2.2 i hi (hchEq.symm ▸ hx)
        · have := hfo.1; omega
        · have := hfo.1; have := hresp1.1; have := hresp4.1; omega
      · rcases hresp4.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
        · exact hpre.elim hfo.2.2.2.1 (fun hno => hno hfo.2.1)
        · have := hfo.1; have := hresp1.1; omega
    have hNextTreeOut : ∀ a, Rtree.foot treeHandle nextXTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
          C.d m L G Ttree recPtr extraStatic a := fun a hft => by
      refine ⟨htreeOut4 a hft, fun hs => ?_⟩
      rcases hresp4.2.2.2.2 a hft with hpre | ⟨hlo, _⟩
      · exact hpre.elim (fun h => (hI.treeOut a h).2 hs) (fun hno => hno (hstaticBelow a hs).2)
      · have := (hstaticBelow a hs).1; have := hI.heapLo; have := hresp1.1; omega
    have hCoresNext : OrdInitChainCoresK Rcore Rterm Rtree chain treeHandle levelTable branchTable
        rootBase edgeRecords edgeThresholds slots names slotThresholds m L ret3 G recPtr
        extraStatic nextXCore curXTerm nextXTree s8.mem := by
      refine ⟨fun j hj => ?_, hTermPres.2.1, by rw [hTermPres.1]; exact hTermPres.2.2.1, fun a ha => ?_⟩
      · by_cases hji : j = i
        · subst hji
          simp only [nextXCore, ↓reduceIte]
          have hlvS : s8.mem (levelTable + j) = initMem (levelTable + j) := hstat6 _ hlvStat
          have hbrS : s8.mem (branchTable + j) = chain.bran j :=
            (hstat6 _ hbrStat).trans ((hI.staticEq _ hbrStat).symm.trans hbrEq)
          refine ⟨hbrS, by rw [hlvS]; exact hrepI2, fun a ha => ?_⟩
          rw [hlvS] at ha
          have haLt : a < ret3 := by
            rcases hfootI2_in a ha with hx | ⟨_, hhi⟩ | ⟨_, hhi⟩
            · exact (((hI.cores.1 j hj).2.2 a (hchEq.symm ▸ hx)).1.trans_le hresp1.1).trans_le
                (hresp4.1.trans hresp6.1)
            · exact hhi.trans_le (hresp4.1.trans hresp6.1)
            · exact hhi
          refine ⟨haLt, ?_, ?_, ?_, fun j' hj' hne => ?_, fun hft => ?_⟩
          · rcases hfootI2_in a ha with hx | ⟨hlo, _⟩ | ⟨hlo, _⟩
            · exact ((hI.cores.1 j hj).2.2 a (hchEq.symm ▸ hx)).2.1
            · exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
            · have := hresp1.1; have := hresp4.1; exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · intro hs
            rcases hfootI2_in a ha with hx | ⟨hlo, _⟩ | ⟨hlo, _⟩
            · exact ((hI.cores.1 j hj).2.2 a (hchEq.symm ▸ hx)).2.2.1 hs
            · have := (hstaticBelow a hs).1; have := hI.heapLo; omega
            · have := (hstaticBelow a hs).1; have := hI.heapLo; have := hresp1.1; have := hresp4.1; omega
          · intro hft
            rcases hresp4.2.2.2.2 a hft with hpre | ⟨hlo4, hhi4⟩
            · rcases hfootI2_in a ha with hx | ⟨hlo, _⟩ | ⟨hlo, _⟩
              · exact hpre.elim ((hI.cores.1 j hj).2.2 a (hchEq.symm ▸ hx)).2.2.2.1
                  (fun hno => hno ((hI.cores.1 j hj).2.2 a (hchEq.symm ▸ hx)).2.1)
              · exact hpre.elim (fun ht => by have := hI.treeInv.2.2.2.1 a ht; omega)
                  (fun hno => hno ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩)
              · have := hresp1.1; have := hresp4.1
                exact hpre.elim (fun ht => by have := hI.treeInv.2.2.2.1 a ht; omega)
                  (fun hno => hno ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩)
            · rcases hfootI2_in a ha with hx | ⟨_, hhi⟩ | ⟨hlo, _⟩
              · have := ((hI.cores.1 j hj).2.2 a (hchEq.symm ▸ hx)).1; have := hresp1.1; omega
              · omega
              · omega
          · simp only [hne, ↓reduceIte]
            intro hf'
            rw [(hOtherCore j' hj' hne).1] at hf'
            exact ((hOtherCore j' hj' hne).2.2.2.2 a hf').2.1 ha
          · rw [hTermPres.1] at hft
            exact (hTermPres.2.2.2 a hft).2.1 ha
        · simp only [nextXCore, hji, ↓reduceIte]
          obtain ⟨hlvJ, hbrJ, hrepJ, _, hfootJ⟩ := hOtherCore j hj hji
          have hJeq : curSt.mem (levelTable + j) = initMem (levelTable + j) :=
            hI.staticEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
          refine ⟨hbrJ, by rw [hlvJ]; exact hrepJ, fun a ha => ?_⟩
          rw [hlvJ] at ha
          have hfo := (hI.cores.1 j hj).2.2 a (hJeq.symm ▸ ha)
          refine ⟨(hfo.1.trans_le hresp1.1).trans_le (hresp4.1.trans hresp6.1),
            hfo.2.1, hfo.2.2.1, (hfootJ a ha).2.2, fun j' hj' hne hfj' => ?_,
            fun hft => hfo.2.2.2.2.2 (by rw [hTermPres.1] at hft; rw [hI.staticEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hft)⟩
          by_cases hj'i : j' = i
          · subst hj'i
            simp only [↓reduceIte] at hfj'
            rw [hstat6 _ hlvStat] at hfj'
            exact (hfootJ a ha).2.1 hfj'
          · simp only [hj'i, ↓reduceIte] at hfj'
            rw [(hOtherCore j' hj' hj'i).1] at hfj'
            exact hfo.2.2.2.2.1 j' hj' hne (by
              rw [hI.staticEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hfj')
      · rw [hTermPres.1] at ha
        have hTeq : curSt.mem (levelTable + C.d) = initMem (levelTable + C.d) :=
          hI.staticEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
        have hfo := hI.cores.2.2.2 a (hTeq.symm ▸ ha)
        refine ⟨(hfo.1.trans_le hresp1.1).trans_le (hresp4.1.trans hresp6.1),
          hfo.2.1, hfo.2.2.1, (hTermPres.2.2.2 a ha).2.2, fun j hj hfj => ?_⟩
        by_cases hji : j = i
        · subst hji
          simp only [nextXCore, ↓reduceIte] at hfj
          rw [hstat6 _ hlvStat] at hfj
          exact (hTermPres.2.2.2 a ha).2.1 hfj
        · simp only [nextXCore, hji, ↓reduceIte] at hfj
          rw [(hOtherCore j hj hji).1] at hfj
          exact hfo.2.2.2.2 j hj (by
            rw [hI.staticEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hfj)
    have hNextInv : InitChainLoopInvK Rcore Rterm Rtree chain treeHandle rootBase levelTable
        branchTable slots names slotThresholds edgeRecords edgeThresholds m ec0 L heap linkSpace
        capLimit G val B recPtr thPtr extraStatic initMem (i + 1) s8 ret3 nextS nextXTree
        nextSlot nextName nextXCore curXTerm := by
      refine ⟨by simp [s8],
        by simp [s8, s7, hregs6 31 (by decide), s5, hregs4Keep 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r31],
        by simp [s8, s7, hregs6 0 (by decide), s5, hregs4Keep 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r0],
        by simp [s8, s7, hret3],
        by simp [s8, s7, hregs6 9 (by decide), s5, hregs4Keep 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r9],
        by simp [s8, s7, hregs6 10 (by decide), s5, hregs4Keep 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r10],
        by simp [s8, s7, hregs6 11 (by decide), s5, hregs4Keep 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r11],
        by simp [s8, s7, hregs6 19 (by decide), s5, hregs4Keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r19],
        by simp [s8, s7, hregs6 20 (by decide), s5, hregs4Keep 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r20],
        by simp [s8, s7, hregs6 22 (by decide), s5, hregs4Keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r22],
        by simp [s8, s7, hregs6 23 (by decide), s5, hregs4Keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r23],
        by simp [s8, s7, hregs6 24 (by decide), s5, hregs4Keep 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r24],
        by simp [s8, s7, hregs6 29 (by decide), s5, hregs4Keep 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r29],
        by simp [s8, s7, hregs6 30 (by decide), s5, hregs4Keep 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r30],
        hI.heapLo.trans (hresp1.1.trans (hresp4.1.trans hresp6.1)),
        by
          rw [Finset.sum_range_succ, Nat.add_mul]
          have := hresp1.2.1; have h4 := hresp4.2.1; have := hresp6.2.1
          dsimp only [Fi] at h4; omega,
        hresp6.2.2.1, hstat6,
        ⟨gv, ge, hgv, hge, hcapNext, by
          have hGsucc : chain.G (i + 1) = T.S (chain.scState i) (chain.bran i) :=
            (hH.2.2.2.2.1 i hi).2.2.2
          rw [hGsucc]; simpa [s8, s7, chainLevelOrdAbs] using hGNext, by simpa [s8, s7] using hGNextEnd⟩,
        hinv8, hNextTreeOut, hCoresNext⟩
    obtain ⟨mid, midHeap, midS, midXTree, midSlot, midName, midXCore, midXTerm, cRest,
        hrRest, hInvFin, hMidRegs, hcRest⟩ :=
      ih (i + 1) (by omega) s8 ret3 nextS nextXTree nextSlot nextName nextXCore curXTerm hNextInv
    have rBody : Runs w p ω (
        .assign 33 (.reg 3) ;;
        .call 3 (opCore 2) [.load (.bin .add (.reg 29) (.reg 32)),
          .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3] ;;
        .assign 25 (.load (.bin .add (.reg 33) (.const 1))) ;;
        initLinkForestEdges (opTree 0) bind ;;
        .assign 33 (.reg 3) ;;
        .call 3 (opCore 3) [.load (.bin .add (.reg 29) (.reg 32)),
          .load (.bin .add (.reg 30) (.reg 32)), .reg 3] ;;
        .assign 34 (.load (.reg 33)) ;;
        .assign 32 (.bin .add (.reg 32) (.const 1)))
        curSt .normal s8 (2 + (cRF + (5 + (cLink + (2 + (cRG + (3 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, cRF, _, hr2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, hr3,
      runs_seq_iff.mpr (Or.inr ⟨s4, cLink, _, hr4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, hr5,
      runs_seq_iff.mpr (Or.inr ⟨s6, cRG, _, hr6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 3, 4, hr7, hr8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have rLoop : Runs w p ω (.loop (.bin .lt (.reg 32) (.reg 31)) _) curSt .normal mid
        (3 + (2 + (cRF + (5 + (cLink + (2 + (cRG + (3 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + cRest + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s8, _, cRest,
        by simp [Expr.eval, BinOp.eval, hI.r32, hI.r31, hi, show 1 < 2 ^ w by omega],
        by decide, rBody, hrRest, by simp [Expr.size]⟩))
    refine ⟨mid, midHeap, midS, midXTree, midSlot, midName, midXCore, midXTerm, _, rLoop, hInvFin,
      fun r hr => by
        rw [hMidRegs r hr]
        simp only [s8, s7, Function.update_of_ne (show r ≠ 32 by omega),
          Function.update_of_ne (show r ≠ 34 by omega)]
        rw [hregs6 r (by omega)]
        simp only [s5, Function.update_of_ne (show r ≠ 33 by omega)]
        exact hregs4Keep r (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), ?_⟩
    -- Telescope core potential sum and tree potential across iteration `i`
    have hCorePhiSplit :
        (∑ j : Fin C.d, Rcore.phi (s8.mem (levelTable + j.val)) (nextXCore j.val) s8.mem) +
          Rcore.phi (curSt.mem (levelTable + i)) (curXCore i) curSt.mem =
        (∑ j : Fin C.d, Rcore.phi (curSt.mem (levelTable + j.val)) (curXCore j.val) curSt.mem) +
          Rcore.phi (initMem (levelTable + i)) yCoreI2 s6.mem := by
      have hiFin : (⟨i, hi⟩ : Fin C.d) ∈ (Finset.univ : Finset (Fin C.d)) := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ hiFin, ← Finset.add_sum_erase _ _ hiFin]
      have hRestEq :
          ∑ j ∈ (Finset.univ : Finset (Fin C.d)).erase ⟨i, hi⟩,
            Rcore.phi (s8.mem (levelTable + j.val)) (nextXCore j.val) s8.mem =
          ∑ j ∈ (Finset.univ : Finset (Fin C.d)).erase ⟨i, hi⟩,
            Rcore.phi (curSt.mem (levelTable + j.val)) (curXCore j.val) curSt.mem := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j.val ≠ i := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
        simp only [nextXCore, hne, ↓reduceIte]
        rw [(hOtherCore j.val j.isLt hne).1]
        exact (hOtherCore j.val j.isLt hne).2.2.2.1
      rw [hRestEq]
      simp only [nextXCore, ↓reduceIte]
      change Rcore.phi (s6.mem (levelTable + i)) yCoreI2 s6.mem + _ + _ = _
      rw [hstat6 _ hlvStat]; omega
    have hTreePhi1 : Rtree.phi treeHandle curXTree s3.mem = Rtree.phi treeHandle curXTree curSt.mem :=
      htreeLoc1.2.symm
    have hTreePhi6 : Rtree.phi treeHandle nextXTree s8.mem = Rtree.phi treeHandle nextXTree s4.mem :=
      htreeLoc6.2.symm
    have hCorePhi4 : Rcore.phi (initMem (levelTable + i)) yCoreI1 s5.mem =
        Rcore.phi (initMem (levelTable + i)) yCoreI1 s2.mem := hcoreI1_loc4.2.symm
    have hSumEdgeSplit :
        (∑ j ∈ Finset.range C.d, if i ≤ j then
          (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) =
        Fi.m * (pathTreeBudget treeConst L G.n + 96) +
        (∑ j ∈ Finset.range C.d, if i + 1 ≤ j then
          (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) := by
      have hterm : ∀ j ∈ Finset.range C.d,
          (if i ≤ j then (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) =
          (if j = i then (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) +
          (if i + 1 ≤ j then (chain.toTreeChain.activeLSF j).F.F.m * (pathTreeBudget treeConst L G.n + 96) else 0) := by
        intro j _; by_cases h1 : j = i <;> by_cases h2 : i + 1 ≤ j <;> simp [h1, h2] <;> omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [hi, Fi]
    have hDsub : (C.d - i) * (2 * P.readout + 80) =
        (2 * P.readout + 80) + (C.d - (i + 1)) * (2 * P.readout + 80) := by
      have : C.d - i = 1 + (C.d - (i + 1)) := by omega
      rw [this, Nat.add_mul, one_mul]
    rw [hTreePhi1] at hcLink
    rw [hTreePhi6] at hcRest
    rw [hCorePhi4] at hcRG
    rw [hchEq] at hCorePhiSplit
    rw [hSumEdgeSplit, hDsub]
    dsimp only [s1] at hcRF
    omega

end MinCostFlow.MinRatio
