module

public import MinCostFlow.MinRatio.InitPathTreeChainHelpers
import Mathlib.Tactic.Ring

/-!
# Core-level loop of `initLinkChainForests`

Proves `initLinkChainLoop_runs`: running the `C.d`-iteration loop of
`initLinkChainForests` inserts the active forest edges of levels `0 .. C.d - 1`
into the Section 6 path tree while preserving `InitChainLoopInv`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- Run the `C.d`-iteration loop of `initLinkChainForests` from level `0` to `C.d`. -/
theorem initLinkChainLoop_runs {w L treeConst initCore initLast initTree bind
    treeHandle rootBase levelTable branchTable slots names slotThresholds
    edgeRecords edgeThresholds m heap levelSpace linkSpace lastMult stretchP vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {lastTool : LastLevelTool}
    {C : ChainParams} {costs : SparseCoreMachineCosts}
    {coreAlloc : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {treeAlloc : ℕ → ℕ → List ℕ → ℕ}
    {Mcap Ncap : ℕ → ℕ} {Rcore : DSRep T.State}
    {Rterm : DSRep (ℕ × (ℕ → LSF))} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {initMem : ℕ → ℕ}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} {val : ℕ → PathEdgeValue} {B : ℤ}
    {recPtr thPtr : ℕ → ℕ} {extraStatic : ℕ → Prop}
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hcoreImpl : ∀ i < C.d, ∀ vc ec, Rcore.Implements w p initCore opCore
      (sparseCoreMachineContract fmt L T (chain.G i) C.k (Mcap i) (Ncap i) vc ec costs (coreAlloc i)))
    (htermImpl : Rterm.Implements w p initLast opLast
      (lastLevelRuntimeMachineContract fmt L lastTool (chain.G C.d) vcLast ecLast lastMult stretchP lastAlloc))
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreInput : ∀ i < C.d,
      SparseCoreInput T.toSparseCoreTool T.restart C.k (chain.scState i) (chain.G i))
    (hG : DynGraphAt initMem rootBase G.n G.m G) (hGm : G.m = m)
    (hvalFwd : ∀ e ∈ chain.toTreeChain.chainTree.E, (val e).forward = true)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      |(val e).gradient| ≤ B ∧ |(val e).length| ≤ B ∧ |(val e).flow| ≤ B ∧ |(val e).detector| ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity fmt.limbBits L : ℤ))
    (hrecPtr : ∀ e ∈ chain.toTreeChain.chainTree.E, initMem (edgeRecords + e) = recPtr e)
    (hrecAt : ∀ e ∈ chain.toTreeChain.chainTree.E,
      PathEdgeAt initMem (recPtr e) fmt.limbBits L (some (val e)))
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
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ fmt.limbBits * L)
    (hhandleW : treeHandle < 2 ^ w) (hdW : C.d < 2 ^ w) (hw7 : 7 < 2 ^ w)
    (hreadoutBounds : ∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (fv fe : ℕ) (yCore : Rcore.τ),
      heap ≤ cur → cur ≤ ret →
      LSFAt mem' cur fv fe fmt.limbBits L fmt.precision (chain.G i).E (T.lsfs (chain.scState i) (chain.bran i)) →
      let fBase := mem' (cur + 1)
      fBase + dynGraphSize fv fe ≤ ret ∧
      (∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        Rcore.foot (initMem (levelTable + i)) yCore a ∨ (cur ≤ a ∧ a < ret)))
    (hgraphReadBounds : ∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret : ℕ) (gv ge : ℕ) (yCore : Rcore.τ),
      heap ≤ cur → cur ≤ ret →
      DynGraphAt mem' (mem' cur) gv ge (chain.G (i + 1)) →
      mem' cur + dynGraphSize gv ge ≤ ret ∧
      (∀ a, mem' cur ≤ a → a < mem' cur + dynGraphSize gv ge →
        Rcore.foot (initMem (levelTable + i)) yCore a ∨ (cur ≤ a ∧ a < ret)))
    (hlevelCap : ∀ i < C.d, 5 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace ≤ levelSpace)
    (hlinkAlloc : ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
      heap ≤ cur → cur ≤ heap + (C.d + 1) * levelSpace →
      treeAlloc 0 G.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, cur] ≤ linkSpace)
    (hroom : heap + (C.d + 1) * levelSpace < 2 ^ w)
    (rem i : ℕ) (hi : i + rem = C.d)
    (curSt : State) (curHeap : ℕ) (curS : PathTreeState) (curXTree : Rtree.τ)
    (curSlot curName : ℕ → ℕ) (curXCore : ℕ → Rcore.τ) (curXTerm : Rterm.τ)
    (hI : InitChainLoopInv Rcore Rterm Rtree chain treeHandle rootBase levelTable branchTable
      slots names slotThresholds edgeRecords edgeThresholds m L heap levelSpace
      G val B recPtr thPtr extraStatic initMem i curSt curHeap curS curXTree curSlot curName curXCore curXTerm) :
    ∃ (mid : State) (midHeap : ℕ) (midS : PathTreeState) (midXTree : Rtree.τ)
      (midSlot midName : ℕ → ℕ) (midXCore : ℕ → Rcore.τ) (midXTerm : Rterm.τ) (cLoop : ℕ),
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
      InitChainLoopInv Rcore Rterm Rtree chain treeHandle rootBase levelTable branchTable
        slots names slotThresholds edgeRecords edgeThresholds m L heap levelSpace
        G val B recPtr thPtr extraStatic initMem C.d mid midHeap midS midXTree midSlot midName midXCore midXTerm := by
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
  induction rem generalizing i curSt curHeap curS curXTree curSlot curName curXCore curXTerm with
  | zero =>
    have hieq : i = C.d := by omega
    subst hieq
    exact ⟨curSt, curHeap, curS, curXTree, curSlot, curName, curXCore, curXTerm, 4,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hI.1, hI.2.1], rfl, rfl, rfl⟩), hI⟩
  | succ rem ih =>
    have hiLt : i < C.d := by omega
    obtain ⟨h32, h31, h0c, h3c, h9c, h10c, h11c, h19c, h20c, h22c, h23c, h24c, h29c, h30c,
        hlo, hhi, hzc, hstatEq, ⟨vc, ec, hGi, hGiBelow⟩, hinvC, htreeOutC, hcoresC⟩ := hI
    have hcoreI := hcoresC.1 i hiLt
    have hlvStatic : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic (levelTable + i) := Or.inr (Or.inl ⟨by omega, by omega⟩)
    have hbrStatic : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic (branchTable + i) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hchEq : curSt.mem (levelTable + i) = initMem (levelTable + i) := hstatEq _ hlvStatic
    have hbrEq : curSt.mem (branchTable + i) = chain.bran i := hcoreI.1
    have hcurLeTotal : curHeap ≤ heap + (C.d + 1) * levelSpace :=
      hhi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right levelSpace (by omega)) heap)
    have hcapI := hlevelCap i hiLt
    let st1 := { curSt with regs := Function.update curSt.regs 33 curHeap }
    have hr1 : Runs w p ω (.assign 33 (.reg 3)) curSt .normal st1 2 :=
      runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, h3c], rfl, rfl, rfl⟩
    have hbrLtK : chain.bran i < C.k := (hH.2.2.2.2.1 i hiLt).1
    have hcgW : curSt.regs 34 < 2 ^ w := by
      have hlt := hGiBelow.trans hcurLeTotal; omega
    have hchAddrW : levelTable + i < 2 ^ w := by
      have := (hstaticBelow _ hlvStatic).1; omega
    have hbrAddrW : branchTable + i < 2 ^ w := by
      have := (hstaticBelow _ hbrStatic).1; omega
    have hbrValW : chain.bran i < 2 ^ w := by
      have := (hhandlesW i hiLt.le).2
      rw [← hstatEq _ hbrStatic, hbrEq] at this; exact this
    have hrfRoom : curHeap + 4 < 2 ^ w := by
      have h1 : (i + 1) * levelSpace = i * levelSpace + levelSpace := by ring
      have h2 : (i + 1) * levelSpace ≤ (C.d + 1) * levelSpace := Nat.mul_le_mul_right levelSpace (by omega)
      omega
    obtain ⟨st2, ret1, cRF, yCore1, fv, fe, hr2, hret2, hregs2, hrepC1, hlsf2, hrespRF, _⟩ :=
      run_core_readForest (ω := ω) (st := st1) (hcoreImpl i hiLt vc ec)
        (hchEq ▸ hcoreI.2.1) (fun a ha => (hcoreI.2.2 a (hchEq.symm ▸ ha)).1)
        hbrLtK (hcoreInput i hiLt) hGi hGiBelow
        (by simp [st1, h3c]) (by simp [st1, h29c]) (by simp [st1, h30c])
        (by simp [st1, h32]) (by simp [st1])
        hchEq hbrEq hchAddrW hbrAddrW (hhandlesW i hiLt.le).1 hbrValW hcgW
        hzc hrfRoom
    have hframeRF (a : ℕ) (ha : a < curHeap) (hnot : ¬ Rcore.foot (initMem (levelTable + i)) (curXCore i) a) :
        st2.mem a = curSt.mem a := hrespRF.2.2.2.1 a ha hnot
    have hstatEq2 : ∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a → st2.mem a = initMem a := fun a ha =>
      (hframeRF a ((hstaticBelow a ha).1.trans_le hlo)
        (fun hf => (hcoreI.2.2 a (hchEq.symm ▸ hf)).2.2.1 ha)).trans (hstatEq a ha)
    have hinv2 : InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
        ((Finset.range i).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
        curS curXTree curSlot curName ret1 st2.mem := by
      obtain ⟨hsn, hinsSub, hrepT, hfootT, htabT, hwitT, hstT, hzT⟩ := hinvC
      have hlocT := htreeImpl.1 treeHandle curS curXTree curSt.mem st2.mem (fun a ha =>
        (hframeRF a (hfootT a ha) (fun hf => (hcoreI.2.2 a (hchEq.symm ▸ hf)).2.2.2.1 ha)).symm)
      refine ⟨hsn, hinsSub, hlocT.1 hrepT, fun a ha => (hfootT a ha).trans_le hrespRF.1,
        htabT.congr
          (fun e he => hframeRF _ (by omega) (fun hf => ((hcoreI.2.2 _ (hchEq.symm ▸ hf)).2.1.1).elim (by omega) (by omega)))
          (fun k hk => hframeRF _ (by omega) (fun hf => ((hcoreI.2.2 _ (hchEq.symm ▸ hf)).2.1.2.1).elim (by omega) (by omega))),
        hwitT, fun e he => ?_, hzT⟩
      obtain ⟨ts, fs, ds, hW, _, hnamed, _⟩ := hwitT
      have hsLt : curSlot e < 2 * G.n := (hsn ▸ (hnamed.forward e he).2.1).2
      rw [hframeRF _ (by omega) (fun hf => ((hcoreI.2.2 _ (hchEq.symm ▸ hf)).2.1.2.2).elim (by omega) (by omega))]
      exact hstT e he
    let fBase := st2.mem (curHeap + 1)
    have hactiveI : chain.toTreeChain.activeLSF i = T.lsfs (chain.scState i) (chain.bran i) := by
      simp [ChainState.toTreeChain, TreeChain.activeLSF, hiLt]
    have hF2 : DynGraphAt st2.mem fBase fv fe (chain.toTreeChain.activeLSF i).F.F := by
      rw [hactiveI]; exact hlsf2.2.1
    have hreadB := hreadoutBounds i hiLt st2.mem curHeap ret1 fv fe yCore1 hlo hrespRF.1 (by
      have hEeq : (readNamedGraph curSt.mem (curSt.regs 34) vc ec).E = (chain.G i).E :=
        readNamedGraph_edges hGi
      rw [hEeq] at hlsf2; exact hlsf2)
    let st3 := { st2 with regs := Function.update st2.regs 25 fBase }
    have hr3 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 33) (.const 1)))) st2 .normal st3 5 :=
      runs_assign_iff.mpr ⟨fBase, by
        simp [Expr.eval, BinOp.eval, hregs2 33 (by decide), st1, fBase,
          show 1 < 2 ^ w by omega, show curHeap + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hG2 : DynGraphAt st3.mem rootBase G.n G.m G :=
      DynGraphAt.of_agree hG (fun a haLo haHi => hstatEq2 a (Or.inl ⟨haLo, haHi⟩))
    have hFiSub : (chain.toTreeChain.activeLSF i).F.F.E ⊆ Ttree.E := activeLSF_subset_chainTree hiLt.le
    have hret1Room : ret1 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace < 2 ^ w := by
      have h1 : ret1 ≤ curHeap + 4 := hrespRF.2.1
      have h2 : (i + 1) * levelSpace = i * levelSpace + levelSpace := by ring
      have h3 : (i + 1) * levelSpace ≤ (C.d + 1) * levelSpace := Nat.mul_le_mul_right levelSpace (by omega)
      omega
    have hforestOut2 : ∀ a, fBase ≤ a → a < fBase + dynGraphSize fv fe →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ Rtree.foot treeHandle curXTree a := by
      intro a haLo haHi
      rcases hreadB.2 a haLo haHi with hfc | ⟨hge, _⟩
      · rcases hrespRF.2.2.2.2 a hfc with hold | ⟨hge, _⟩
        · exact ⟨(hcoreI.2.2 a (hchEq.symm ▸ hold)).2.1, (hcoreI.2.2 a (hchEq.symm ▸ hold)).2.2.2.1⟩
        · exact ⟨⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
            fun hf => by have := hinvC.2.2.2.1 a hf; omega⟩
      · exact ⟨⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
          fun hf => by have := hinvC.2.2.2.1 a hf; omega⟩
    obtain ⟨st4, ret2, cLink, sNext, yTreeNext, slotNext, nameNext, hr4, hret4, hregs4,
        hinv4, htreeOut4, hresp4, _⟩ :=
      initLinkForestEdges_runs (ω := ω) (st := st3) htreeImpl hbind hTForest hTEnds
        hG2 hF2 hTG (fun e he => hGm ▸ hG.2.2.1 e he) hFiSub (initChain_prefix_disjoint hH hiLt.le) hinv2
        (fun e he => hvalFwd e (hFiSub he)) (fun e he => hvalB e (hFiSub he)) hcapB
        (by simp [st3, hregs2 0 (by decide), st1, h0c])
        (by simp [st3, hret2])
        (by simp [st3, hregs2 9 (by decide), st1, h9c])
        (by simp [st3, hregs2 10 (by decide), st1, h10c])
        (by simp [st3, hregs2 11 (by decide), st1, h11c])
        (by simp [st3, hregs2 19 (by decide), st1, h19c])
        (by simp [st3, hregs2 20 (by decide), st1, h20c])
        (by simp [st3, hregs2 22 (by decide), st1, h22c])
        (by simp [st3, hregs2 23 (by decide), st1, h23c])
        (by simp [st3, hregs2 24 (by decide), st1, h24c])
        (by simp [st3])
        (fun e he => (hstatEq2 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
          by have := hG.2.2.1 e (hTG (hFiSub he)); omega⟩))))).trans (hrecPtr e (hFiSub he)))
        (fun e he => (hrecAt e (hFiSub he)).congr (fun a hloA hhiA =>
          hstatEq2 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hFiSub he, hloA, by omega⟩))))))))
        (fun e he => (hstatEq2 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
          by have := hG.2.2.1 e (hTG (hFiSub he)); omega⟩)))))).trans (hthPtrAt e (hFiSub he)))
        (fun e he => by
          have h1 := (hstaticBelow (recPtr e + (2 + 4 * L) - 1)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hFiSub he, by omega, by omega⟩))))))).1
          have := hrespRF.1; omega)
        (fun e he => ((hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
          by have := hG.2.2.1 e (hTG (hFiSub he)); omega⟩))))).1.trans_le hlo).trans_le hrespRF.1)
        (fun e he => ((hstaticBelow _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
          by have := hG.2.2.1 e (hTG (hFiSub he)); omega⟩)))))).1.trans_le hlo).trans_le hrespRF.1)
        (fun e he => hthValW e (hFiSub he))
        (hrootBelow.trans (hlo.trans hrespRF.1)) hreadB.1
        (hslotsBelow.trans (hlo.trans hrespRF.1))
        (hnamesBelow.trans (hlo.trans hrespRF.1))
        (hstBelow.trans (hlo.trans hrespRF.1))
        hdisjSN hdisjST hdisjNT (fun a ha => (htreeOutC a ha).1)
        (fun a haLo haHi => ⟨(hstaticBelow a (Or.inl ⟨haLo, haHi⟩)).2,
          fun hf => (htreeOutC a hf).2 (Or.inl ⟨haLo, haHi⟩)⟩)
        hforestOut2
        (fun e he =>
          let hA : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic (edgeRecords + e) :=
            Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by have := hG.2.2.1 e (hTG (hFiSub he)); omega⟩)))
          ⟨(hstaticBelow _ hA).2, fun hf => (htreeOutC _ hf).2 hA⟩)
        (fun e he a hloA hhiA =>
          let hA : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a :=
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hFiSub he, hloA, hhiA⟩)))))
          ⟨(hstaticBelow a hA).2, fun hf => (htreeOutC a hf).2 hA⟩)
        (fun e he =>
          let hA : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic (edgeThresholds + e) :=
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by have := hG.2.2.1 e (hTG (hFiSub he)); omega⟩))))
          ⟨(hstaticBelow _ hA).2, fun hf => (htreeOutC _ hf).2 hA⟩)
        hvw hwidth hhandleW hw7 hrespRF.2.2.1
        (fun e he cur hlo' hhi' => hlinkAlloc e (hFiSub he) cur (hlo.trans (hrespRF.1.trans hlo'))
          (by
            have h1 : ret1 ≤ curHeap + 4 := hrespRF.2.1
            have h2 : (i + 1) * levelSpace ≤ (C.d + 1) * levelSpace := Nat.mul_le_mul_right levelSpace (by omega)
            have h3 : (i + 1) * levelSpace = i * levelSpace + levelSpace := by ring
            omega))
        hret1Room
    rw [initChain_prefix_union i] at hinv4
    have hret2Bound : ret2 ≤ heap + (i + 1) * levelSpace := by
      have h1 : ret1 ≤ curHeap + 4 := hrespRF.2.1
      have h2 : ret2 ≤ ret1 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace := hresp4.2.1
      have h3 : (i + 1) * levelSpace = i * levelSpace + levelSpace := by ring
      omega
    have hframeLink (a : ℕ) (ha : a < ret1)
        (hOut : OutsideInitSlotTables slots names slotThresholds m G.n a)
        (hnt : ¬ Rtree.foot treeHandle curXTree a) : st4.mem a = st2.mem a :=
      hresp4.2.2.2.1 a ha (fun h => h.elim hnt (fun hn => hn hOut))
    have hstatEq4 : ∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a → st4.mem a = initMem a := fun a ha =>
      (hframeLink a (((hstaticBelow a ha).1.trans_le hlo).trans_le hrespRF.1)
        (hstaticBelow a ha).2 (fun hf => (htreeOutC a hf).2 ha)).trans (hstatEq2 a ha)
    have hfootCore1 : ∀ a, Rcore.foot (initMem (levelTable + i)) yCore1 a →
        a < ret1 ∧ OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
        ¬ Rtree.foot treeHandle curXTree a := by
      intro a ha
      rcases hrespRF.2.2.2.2 a ha with hold | ⟨hge, hlt⟩
      · have hc := hcoreI.2.2 a (hchEq.symm ▸ hold)
        exact ⟨hc.1.trans_le hrespRF.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      · exact ⟨hlt, ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩,
          fun hs => by have := (hstaticBelow a hs).1; omega,
          fun ht => by have := hinvC.2.2.2.1 a ht; omega⟩
    have hrepC1_4 : Rcore.rep (initMem (levelTable + i)) (chain.scState i) yCore1 st4.mem :=
      ((hcoreImpl i hiLt vc ec).1 _ _ _ st2.mem st4.mem
        (fun a ha => (hframeLink a (hfootCore1 a ha).1 (hfootCore1 a ha).2.1 (hfootCore1 a ha).2.2.2).symm)).1 hrepC1
    let st5 := { st4 with regs := Function.update st4.regs 33 ret2 }
    have hr5 : Runs w p ω (.assign 33 (.reg 3)) st4 .normal st5 2 :=
      runs_assign_iff.mpr ⟨ret2, by simp [Expr.eval, hret4], rfl, rfl, rfl⟩
    have hret2Room : ret2 + 1 < 2 ^ w := by
      have h1 : ret1 ≤ curHeap + 4 := hrespRF.2.1
      have h2 : ret2 ≤ ret1 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace := hresp4.2.1
      have h3 : (i + 1) * levelSpace = i * levelSpace + levelSpace := by ring
      have h4 : (i + 1) * levelSpace ≤ (C.d + 1) * levelSpace := Nat.mul_le_mul_right levelSpace (by omega)
      omega
    have hreg4_29 : st4.regs 29 = levelTable :=
      (hregs4 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simp [st3, hregs2 29 (by decide), st1, h29c])
    have hreg4_30 : st4.regs 30 = branchTable :=
      (hregs4 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simp [st3, hregs2 30 (by decide), st1, h30c])
    have hreg4_32 : st4.regs 32 = i :=
      (hregs4 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simp [st3, hregs2 32 (by decide), st1, h32])
    obtain ⟨st6, ret3, cRG, yCore2, gv, ge, hr6, hret6, hregs6, hrepC2, hdg6, hrespRG, _⟩ :=
      run_core_readGraph (ω := ω) (st := st5) (hcoreImpl i hiLt vc ec)
        hrepC1_4 (fun a ha => (hfootCore1 a ha).1.trans_le hresp4.1)
        hbrLtK (hcoreInput i hiLt)
        (by simp [st5, hret4]) (by simp [st5, hreg4_29]) (by simp [st5, hreg4_30]) (by simp [st5, hreg4_32])
        (hstatEq4 _ hlvStatic) ((hstatEq4 _ hbrStatic).trans ((hstatEq _ hbrStatic).symm.trans hbrEq))
        hchAddrW hbrAddrW (hhandlesW i hiLt.le).1 hbrValW hresp4.2.2.1 hret2Room
    have hGi1Eq : T.S (chain.scState i) (chain.bran i) = chain.G (i + 1) := by
      have h := (hH.2.2.2.2.1 i hiLt).2.2.2
      simpa [ChainState.toTreeChain, hiLt] using h.symm
    rw [hGi1Eq] at hdg6
    have hgb6 := hgraphReadBounds i hiLt st6.mem ret2 ret3 gv ge yCore2
      (hlo.trans (hrespRF.1.trans hresp4.1)) hrespRG.1 hdg6
    let st7 := { st6 with regs := Function.update st6.regs 34 (st6.mem ret2) }
    let st8 := { st7 with regs := Function.update st7.regs 32 (i + 1) }
    have hr7 : Runs w p ω (.assign 34 (.load (.reg 33))) st6 .normal st7 3 :=
      runs_assign_iff.mpr ⟨st6.mem ret2, by simp [Expr.eval, hregs6 33 (by decide), st5], rfl, rfl, rfl⟩
    have hr8 : Runs w p ω (.assign 32 (.bin .add (.reg 32) (.const 1))) st7 .normal st8 4 :=
      runs_assign_iff.mpr ⟨i + 1, by
        simp [Expr.eval, BinOp.eval, st7, hregs6 32 (by decide), st5, hreg4_32,
          show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hret3Bound : ret3 ≤ heap + (i + 1) * levelSpace := by
      have h1 : ret1 ≤ curHeap + 4 := hrespRF.2.1
      have h2 : ret2 ≤ ret1 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace := hresp4.2.1
      have h3 : ret3 ≤ ret2 + 1 := hrespRG.2.1
      have h4 : (i + 1) * levelSpace = i * levelSpace + levelSpace := by ring
      omega
    have hfootTreeOutNext : ∀ a, Rtree.foot treeHandle yTreeNext a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a := by
      intro a ha
      refine ⟨htreeOut4 a ha, fun hs => ?_⟩
      rcases hresp4.2.2.2.2 a ha with h | ⟨hge, _⟩
      · rcases h with hfx | hnot
        · exact (htreeOutC a hfx).2 hs
        · exact hnot (hstaticBelow a hs).2
      · have := (hstaticBelow a hs).1; have := hrespRF.1; omega
    have hfootCore1NotTreeNext : ∀ a, Rcore.foot (initMem (levelTable + i)) yCore1 a →
        ¬ Rtree.foot treeHandle yTreeNext a := by
      intro a ha ht
      have h1 := (hfootCore1 a ha).1
      rcases hresp4.2.2.2.2 a ht with h | ⟨hge, _⟩
      · rcases h with hfx | hnot
        · exact (hfootCore1 a ha).2.2.2 hfx
        · exact hnot (hfootCore1 a ha).2.1
      · omega
    have hinv6 : InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
        ((Finset.range (i + 1)).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
        sNext yTreeNext slotNext nameNext ret3 st8.mem := by
      obtain ⟨hsn, hinsSub, hrepT, hfootT, htabT, hwitT, hstT, hzT⟩ := hinv4
      have hlocT := htreeImpl.1 treeHandle sNext yTreeNext st4.mem st6.mem (fun a ha =>
        (hrespRG.2.2.2.1 a (hfootT a ha) (fun hf => hfootCore1NotTreeNext a hf ha)).symm)
      refine ⟨hsn, hinsSub, hlocT.1 hrepT, fun a ha => (hfootT a ha).trans_le hrespRG.1,
        htabT.congr
          (fun e he => hrespRG.2.2.2.1 _ (by have := hrespRF.1; have := hresp4.1; omega)
            (fun hf => (hfootCore1 _ hf).2.1.1.elim (by omega) (by omega)))
          (fun k hk => hrespRG.2.2.2.1 _ (by have := hrespRF.1; have := hresp4.1; omega)
            (fun hf => (hfootCore1 _ hf).2.1.2.1.elim (by omega) (by omega))),
        hwitT, fun e he => ?_, hzT⟩
      obtain ⟨ts, fs, ds, hW, _, hnamed, _⟩ := hwitT
      have hsLt : slotNext e < 2 * G.n := (hsn ▸ (hnamed.forward e he).2.1).2
      rw [show st8.mem = st6.mem from rfl,
        hrespRG.2.2.2.1 _ (by have := hrespRF.1; have := hresp4.1; omega)
          (fun hf => (hfootCore1 _ hf).2.1.2.2.elim (by omega) (by omega))]
      exact hstT e he
    have hstatEq8 : ∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
        C.d m L G Ttree recPtr extraStatic a → st8.mem a = initMem a := fun a ha =>
      (hrespRG.2.2.2.1 a ((((hstaticBelow a ha).1.trans_le hlo).trans_le hrespRF.1).trans_le hresp4.1)
        (fun hf => (hfootCore1 a hf).2.2.1 ha)).trans (hstatEq4 a ha)
    let nextXCore : ℕ → Rcore.τ := Function.update curXCore i yCore2
    have hcores8 : InitChainCoresAt Rcore Rterm Rtree chain treeHandle levelTable branchTable
        rootBase edgeRecords edgeThresholds slots names slotThresholds m L ret3 G recPtr extraStatic
        nextXCore curXTerm yTreeNext st8.mem := by
      have hstepFrameOther (a : ℕ) (ha : a < curHeap)
          (hOut : OutsideInitSlotTables slots names slotThresholds m G.n a)
          (hnt : ¬ Rtree.foot treeHandle curXTree a)
          (hnc : ¬ Rcore.foot (initMem (levelTable + i)) (curXCore i) a) :
          st6.mem a = curSt.mem a := by
        have h1 : st2.mem a = curSt.mem a := hframeRF a ha hnc
        have h2 : st4.mem a = st2.mem a := hframeLink a (ha.trans_le hrespRF.1) hOut hnt
        have hnc1 : ¬ Rcore.foot (initMem (levelTable + i)) yCore1 a := fun hf =>
          (hrespRF.2.2.2.2 a hf).elim hnc (fun h => by omega)
        exact (hrespRG.2.2.2.1 a ((ha.trans_le hrespRF.1).trans_le hresp4.1) hnc1).trans (h2.trans h1)
      refine ⟨fun j hj => ?_, ?_, ?_, ?_⟩
      · have hjStatic : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
            C.d m L G Ttree recPtr extraStatic (levelTable + j) := Or.inr (Or.inl ⟨by omega, by omega⟩)
        have hbrJStatic : InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
            C.d m L G Ttree recPtr extraStatic (branchTable + j) := Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
        have hjHandle : st8.mem (levelTable + j) = curSt.mem (levelTable + j) :=
          (hstatEq8 _ hjStatic).trans (hstatEq _ hjStatic).symm
        have hjBr : st8.mem (branchTable + j) = chain.bran j :=
          (hstatEq8 _ hbrJStatic).trans ((hstatEq _ hbrJStatic).symm.trans (hcoresC.1 j hj).1)
        by_cases hji : j = i
        · subst hji
          refine ⟨hjBr, by rw [hjHandle, hchEq]; simpa [nextXCore] using hrepC2, fun a ha => ?_⟩
          rw [hjHandle, hchEq] at ha
          simp only [nextXCore, Function.update_self] at ha
          rcases hrespRG.2.2.2.2 a ha with h1 | ⟨hge2, hlt3⟩
          · have hf1 := hfootCore1 a h1
            refine ⟨hf1.1.trans_le (hresp4.1.trans hrespRG.1), hf1.2.1, hf1.2.2.1,
              hfootCore1NotTreeNext a h1, fun k hk hki => ?_, ?_⟩
            · simp only [nextXCore, Function.update_of_ne hki]
              rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
                ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
              rcases hrespRF.2.2.2.2 a h1 with hold | ⟨hge0, _⟩
              · exact (hcoreI.2.2 a (hchEq.symm ▸ hold)).2.2.2.2.1 k hk hki
              · intro hfk; have := ((hcoresC.1 k hk).2.2 a hfk).1; omega
            · rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
                ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
              rcases hrespRF.2.2.2.2 a h1 with hold | ⟨hge0, _⟩
              · exact (hcoreI.2.2 a (hchEq.symm ▸ hold)).2.2.2.2.2
              · intro hft; have := (hcoresC.2.2.2 a hft).1; omega
          · refine ⟨hlt3, ⟨Or.inr (by have := hrespRF.1; have := hresp4.1; omega),
              Or.inr (by have := hrespRF.1; have := hresp4.1; omega),
              Or.inr (by have := hrespRF.1; have := hresp4.1; omega)⟩,
              fun hs => by have := (hstaticBelow a hs).1; have := hrespRF.1; have := hresp4.1; omega,
              fun ht => by have := hinv4.2.2.2.1 a ht; omega,
              fun k hk hki => ?_, ?_⟩
            · simp only [nextXCore, Function.update_of_ne hki]
              rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
                ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
              intro hfk; have := ((hcoresC.1 k hk).2.2 a hfk).1; have := hrespRF.1; have := hresp4.1; omega
            · rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
                ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
              intro hft; have := (hcoresC.2.2.2 a hft).1; have := hrespRF.1; have := hresp4.1; omega
        · have hcj := hcoresC.1 j hj
          have hlocJ := (hcoreImpl j hj vc ec).1 (curSt.mem (levelTable + j)) (chain.scState j)
            (curXCore j) curSt.mem st6.mem (fun a ha => by
              have hf := hcj.2.2 a ha
              exact (hstepFrameOther a hf.1 hf.2.1 hf.2.2.2.1
                (fun hci => hf.2.2.2.2.1 i hiLt (Ne.symm hji) (hchEq.symm ▸ hci))).symm)
          refine ⟨hjBr, by rw [hjHandle]; simpa [nextXCore, Function.update_of_ne hji] using hlocJ.1 hcj.2.1,
            fun a ha => ?_⟩
          rw [hjHandle] at ha; simp only [nextXCore, Function.update_of_ne hji] at ha
          have hf := hcj.2.2 a ha
          refine ⟨hf.1.trans_le (hrespRF.1.trans (hresp4.1.trans hrespRG.1)), hf.2.1, hf.2.2.1, ?_,
            fun k hk hkj => ?_, ?_⟩
          · intro ht
            rcases hresp4.2.2.2.2 a ht with h | ⟨hge1, _⟩
            · exact h.elim hf.2.2.2.1 (fun hn => hn hf.2.1)
            · have := hrespRF.1; omega
          · by_cases hki : k = i
            · subst k
              simp only [nextXCore, Function.update_self]
              rw [hstatEq8 _ hlvStatic]
              intro hci2
              rcases hrespRG.2.2.2.2 a hci2 with hci1 | ⟨hge2, _⟩
              · rcases hrespRF.2.2.2.2 a hci1 with hci0 | ⟨hge0, _⟩
                · exact hf.2.2.2.2.1 i hiLt (Ne.symm hji) (hchEq.symm ▸ hci0)
                · omega
              · have := hrespRF.1; have := hresp4.1; omega
            · simp only [nextXCore, Function.update_of_ne hki]
              rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
                ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
              exact hf.2.2.2.2.1 k hk hkj
          · rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
              ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
            exact hf.2.2.2.2.2
      · exact (hstatEq8 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans
          ((hstatEq _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).symm.trans hcoresC.2.1)
      · have hlhEq : st8.mem (levelTable + C.d) = curSt.mem (levelTable + C.d) :=
          (hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans
            (hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).symm
        rw [hlhEq]
        exact (htermImpl.1 _ _ _ curSt.mem st6.mem (fun a ha => by
          have hf := hcoresC.2.2.2 a ha
          exact (hstepFrameOther a hf.1 hf.2.1 hf.2.2.2.1
            (fun hci => hf.2.2.2.2 i hiLt (hchEq.symm ▸ hci))).symm)).1 hcoresC.2.2.1
      · intro a ha
        have hlhEq : st8.mem (levelTable + C.d) = curSt.mem (levelTable + C.d) :=
          (hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans
            (hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).symm
        rw [hlhEq] at ha
        have hf := hcoresC.2.2.2 a ha
        refine ⟨hf.1.trans_le (hrespRF.1.trans (hresp4.1.trans hrespRG.1)), hf.2.1, hf.2.2.1, ?_, fun k hk => ?_⟩
        · intro ht
          rcases hresp4.2.2.2.2 a ht with h | ⟨hge1, _⟩
          · exact h.elim hf.2.2.2.1 (fun hn => hn hf.2.1)
          · have := hrespRF.1; omega
        · by_cases hki : k = i
          · subst k
            simp only [nextXCore, Function.update_self]
            rw [hstatEq8 _ hlvStatic]
            intro hci2
            rcases hrespRG.2.2.2.2 a hci2 with hci1 | ⟨hge2, _⟩
            · rcases hrespRF.2.2.2.2 a hci1 with hci0 | ⟨hge0, _⟩
              · exact hf.2.2.2.2 i hiLt (hchEq.symm ▸ hci0)
              · omega
            · have := hrespRF.1; have := hresp4.1; omega
          · simp only [nextXCore, Function.update_of_ne hki]
            rw [hstatEq8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)),
              ← hstatEq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
            exact hf.2.2.2.2 k hk
    have hreg8 (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3' : r ≠ 3) (h4 : r ≠ 4) (h8 : r ≠ 8)
        (h21 : r ≠ 21) (h25 : r ≠ 25) (h26 : r ≠ 26) (h27 : r ≠ 27) (h28 : r ≠ 28)
        (h32' : r ≠ 32) (h33 : r ≠ 33) (h34' : r ≠ 34) : st8.regs r = curSt.regs r := by
      simp only [st8, st7, Function.update_of_ne h32', Function.update_of_ne h34']
      rw [hregs6 r h3']
      simp only [st5, Function.update_of_ne h33]
      rw [hregs4 r h1 h2 h3' h4 h8 h21 h26 h27 h28]
      simp only [st3, Function.update_of_ne h25]
      rw [hregs2 r h3']
      simp only [st1, Function.update_of_ne h33]
    have hI' : InitChainLoopInv Rcore Rterm Rtree chain treeHandle rootBase levelTable branchTable
        slots names slotThresholds edgeRecords edgeThresholds m L heap levelSpace
        G val B recPtr thPtr extraStatic initMem (i + 1) st8 ret3 sNext yTreeNext slotNext nameNext nextXCore curXTerm :=
      ⟨by simp [st8],
       (hreg8 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h31,
       (hreg8 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0c,
       by simp [st8, st7, hret6],
       (hreg8 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9c,
       (hreg8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10c,
       (hreg8 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11c,
       (hreg8 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19c,
       (hreg8 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20c,
       (hreg8 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22c,
       (hreg8 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23c,
       (hreg8 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24c,
       (hreg8 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29c,
       (hreg8 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
         (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30c,
       hlo.trans (hrespRF.1.trans (hresp4.1.trans hrespRG.1)), hret3Bound, hrespRG.2.2.1,
       hstatEq8, ⟨gv, ge, by simpa [st8, st7] using hdg6, by simpa [st8, st7] using hgb6.1⟩,
       hinv6, hfootTreeOutNext, hcores8⟩
    obtain ⟨mid, midHeap, midS, midXTree, midSlot, midName, midXCore, midXTerm, cRest, hrRest, hInvFin⟩ :=
      ih (i + 1) (by omega) st8 ret3 sNext yTreeNext slotNext nameNext nextXCore curXTerm hI'
    have hrBody : Runs w p ω _ curSt .normal st8 _ :=
      runs_seq_iff.mpr (Or.inr ⟨st1, 2, _, hr1,
        runs_seq_iff.mpr (Or.inr ⟨st2, cRF, _, hr2,
          runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hr3,
            runs_seq_iff.mpr (Or.inr ⟨st4, cLink, _, hr4,
              runs_seq_iff.mpr (Or.inr ⟨st5, 2, _, hr5,
                runs_seq_iff.mpr (Or.inr ⟨st6, cRG, _, hr6,
                  runs_seq_iff.mpr (Or.inr ⟨st7, 3, 4, hr7, hr8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    exact ⟨mid, midHeap, midS, midXTree, midSlot, midName, midXCore, midXTerm, _,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st8, _, cRest,
        by simp [Expr.eval, BinOp.eval, h32, h31, hiLt, show 1 < 2 ^ w by omega],
        by decide, hrBody, hrRest, rfl⟩)), hInvFin⟩

end MinCostFlow.MinRatio
