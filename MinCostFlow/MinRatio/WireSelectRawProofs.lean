module

public import MinCostFlow.MinRatio.WireSelectRawPrefix
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
import WordRAM.Tactic

/-!
# Verification of `selectRawRouteBody` (`O(log)` + cycle length raw cycle selection)

Proves `selectRawRoute_runs`: `selectRawRouteBody` implements the raw cycle selection of
Algorithm 1 (page 21) and Algorithm 2 (page 29) on the maintained select-heap `SelectHeapLoc`:
- If `size = 0` (`(G_0.E \ chainTree.E) = ∅`), writes empty `edges = []`, `paths = []` in `O(1)`.
- If `size > 0`, reads `eBest = arr[0]` (`O(1)`), determines the sign flip via `Num.isNegative`
  + `Num.isZero` (`O(Lk)`), handles `i = d` directly (`K = 1`) and `i < d` by reading `emb[eBest]`
  directly from the owned embedding table `embPtr[i]` (`O(1)` lookup) followed by `selectFillRev`,
  `selectSplitSteps`, and `selectEmitStitches` (`O(K)`).
- Total step cost is `≤ selectRawRouteCost loc.Lk maxEdges`, i.e., `O(log)` plus the length of
  the returned cycle, preserving `tok`, `solverStateRep`, `SelectHeapMatchesChain`,
  `PathTreeNumericInv`, `OffTreeRecInv`, and `OffTreeRecBound` with zero potential change.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

set_option maxHeartbeats 600000 in
/-- **`selectRawRoute_runs`**: `selectRawRouteBody` computes the exact raw cycle route
`(rawEdgesOfWalk, rawPathsOfWalk)` of `(algorithm1_findCycle model.chain).1` in
`≤ selectRawRouteCost loc.Lk maxEdges` steps (`O(log)` + cycle length), using at most
`selectRawRouteSpace maxEdges` scratch words, with no sparse-core readout and unchanged `tok`. -/
theorem selectRawRoute_runs
    {w L P m V psi k epsExp drainUnit isNegProc isZeroProc
      fillRev splitSteps emitStitches maxEdges maxPaths : ℕ}
    {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    (hw16 : 16 < 2 ^ w)
    (hlocalCore : Rcore.Local)
    (hIsNeg : MeetsContract w p isNegProc (Num.isNegativeContract w 4))
    (hIsZero : MeetsContract w p isZeroProc (Num.isZeroContract w 4))
    (hFillRev : ∀ Q : List (ℕ × Bool), MeetsContract w p fillRev (selectFillRevContract w Q))
    (hSplitSteps : ∀ G0 F W fl, MeetsContract w p splitSteps (selectSplitStepsContract w G0 F W fl))
    (hEmitStitches : ∀ G0 W fl p0, MeetsContract w p emitStitches (selectEmitStitchesContract w G0 W fl p0)) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∀ (root descBase workHeap pos size : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ)
      (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c →
      1 ≤ maxEdges →
      2 * maxEdges ≤ maxPaths →
      (∀ i < cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeCore i).E \
        (model.chain.toTreeChain.activeS i).E,
        (model.chain.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges) →
      SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size →
      SelectMetaEmbsAt mem loc.metaPtr descBase model.chain.toTreeChain →
      loc.endAddr ≤ descBase →
      (∀ a, loc.hb ≤ a → a < loc.endAddr → ¬ Rrep.foot root tok a) →
      (∀ a, Rrep.foot root tok a → a < descBase) →
      descBase + 6 = workHeap →
      ZeroFrom mem descBase →
      workHeap + selectRawRouteSpace maxEdges < 2 ^ w →
      ∃ work1 cost out edges paths,
        Runs w p ω (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches)
          (startState [root, loc.hb, descBase, workHeap] mem pos) (.returned work1) out cost ∧
        workHeap ≤ work1 ∧ work1 ≤ workHeap + selectRawRouteSpace maxEdges ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        workHeap ≤ out.mem (descBase + 2) ∧ out.mem (descBase + 2) + 2 * edges.length ≤ out.mem (descBase + 4) ∧
        out.mem (descBase + 2) + 2 * edges.length ≤ work1 ∧ out.mem (descBase + 3) = edges.length ∧
        workHeap ≤ out.mem (descBase + 4) ∧ out.mem (descBase + 4) + 2 * paths.length ≤ work1 ∧
        out.mem (descBase + 5) = paths.length ∧
        ExplicitEdgesAt out.mem (out.mem (descBase + 2)) edges ∧
        PathEndpointsAt out.mem (out.mem (descBase + 4)) paths ∧
        (∀ x ∈ edges, x.1 ∈ (model.chain.G 0).E \ model.chain.toTreeChain.chainTree.E) ∧
        (∀ p ∈ paths, p.1 < model.extG.n ∧ p.2 < model.extG.n ∧
          model.chain.toTreeChain.chainTree.Connected p.1 p.2) ∧
        (∀ p ∈ paths, ∀ q ∈ paths, model.chain.toTreeChain.chainTree.Connected p.1 q.1) ∧
        (∀ ei : ℕ, (algorithm1_findCycle model.chain).1 ei =
          (edges.map (fun x => walkFlow [x] ei)).sum +
          (paths.map (fun p => walkFlow (model.chain.toTreeChain.chainTree.forestPath p.1 p.2) ei)).sum) ∧
        (∀ x < 2 * edges.length, ¬ Rrep.foot root tok (out.mem (descBase + 2) + x)) ∧
        (∀ x < 2 * paths.length, ¬ Rrep.foot root tok (out.mem (descBase + 4) + x)) ∧
        (∀ a, tok.tag a = 18 → a < descBase) ∧
        Rrep.rep root model tok out.mem ∧
        SelectHeapMatchesChain out.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
        PathTreeNumericInv tok.tree tok.trees B R ∧
        OffTreeRecInv model L out.mem tok.edgeRecords B ∧
        OffTreeRecBound model L out.mem tok.edgeRecords B ∧
        ZeroFrom out.mem work1 ∧
        (∀ a < descBase, out.mem a = mem a) ∧
        Rrep.phi root tok out.mem = Rrep.phi root tok mem ∧
        cost ≤ selectRawRouteCost loc.Lk maxEdges := by
  intro Rrep root descBase workHeap pos size ω mem model tok B R G₀ σ σ_mwu γ_ℓ γ_c
    hrep hnum hoff hBd hMod hmaxE1 hmaxEP hEmbBd hMatch hMetaE hlocEnd _hlocDisj hbelow hwh hz hroom
  set C := model.chain.toTreeChain
  have hrep0 := hrep
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  obtain ⟨hH, hSpan, _hBranLt, _hCoreIn, _hExtPos, hVlt⟩ := hMod
  obtain ⟨hrootDir, _, _, hinitP, hFresh, _, _, hIntB, _, _, _, _, _, hedgeAcc, _, _, _, _, hWire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, _, _, _, _, t9, _, _, _, _, _, _, _, _, _, t20, _⟩ := htags
  obtain ⟨_, hRootDG, _, _, _⟩ := hWire
  have hhdSize : mem loc.hb = size := by simpa using hMatch.1.1 0 (by simp)
  have hCdEq : C.d = cfg.P.d := rfl
  have hrootW : root < 2 ^ w := by
    have hrt0 := t1 0 (by decide); rw [Nat.add_zero] at hrt0
    exact lt_trans (hbelow root (Or.inl (hOwn root (by rw [hrt0]; decide)))) (by omega)
  have hhbW : loc.hb < 2 ^ w := by have := loc.endAddr_eq; unfold selectHeapSize shHdrSize at *; omega
  have hdbW : descBase < 2 ^ w := by omega
  have hwhW : workHeap < 2 ^ w := by omega
  have hsp1 : 4 ≤ selectRawRouteSpace maxEdges := by unfold selectRawRouteSpace; omega
  -- Helper: preserve solver invariants across writes strictly above `descBase`
  have hPresTok : ∀ (memB : ℕ → ℕ),
      (∀ a < descBase, memB a = mem a) →
      Rrep.rep root model tok memB ∧
      Rrep.phi root tok memB = Rrep.phi root tok mem ∧
      SelectHeapMatchesChain memB loc 4 P C model.chain.g model.chain.ℓ size ∧
      OffTreeRecInv model L memB tok.edgeRecords B ∧
      OffTreeRecBound model L memB tok.edgeRecords B := by
    intro memB hagLt
    have hagF : ∀ a, Rrep.foot root tok a → memB a = mem a := fun a ha => hagLt a (hbelow a ha)
    have hagL : ∀ a, loc.hb ≤ a → a < loc.endAddr → memB a = mem a := fun a _ ha2 =>
      hagLt a (lt_of_lt_of_le ha2 hlocEnd)
    have hloc' := hlocR root model tok mem memB (fun a ha => (hagF a ha).symm)
    have htag1318 : ∀ a, (tok.tag a = 13 ∨ tok.tag a = 18) → memB a = mem a := fun a ha =>
      hagF a (Or.inl (hOwn a (by rcases ha with h | h <;> rw [h] <;> decide)))
    exact ⟨hloc'.1 hrep0, hloc'.2.symm, hMatch.of_agree hagL,
      offTreeRecInv_of_agree hrep0 hoff htag1318, offTreeRecBound_of_agree hrep0 hBd htag1318⟩
  have htag18Lt : ∀ a, tok.tag a = 18 → a < descBase :=
    fun a ha => hbelow a (Or.inl (hOwn a (by rw [ha]; decide)))
  -- Branch on `size = 0` vs `size > 0`
  by_cases hsz0 : size = 0
  · -- Empty heap: `(G_0.E \ chainTree.E) = ∅`
    have hEmptyS : ¬ ((model.chain.G 0).E \ C.chainTree.E).Nonempty := by
      rintro ⟨e, he⟩
      obtain ⟨heCap, hnz⟩ := (hMatch.2.2.1 e).mpr he
      rcases hMatch.1.2.1.2.2.2 e heCap with h0 | ⟨hle, _⟩
      · exact hnz h0
      · omega
    have hAlg0 : ∀ ei, (algorithm1_findCycle model.chain).1 ei = 0 := by
      intro ei; unfold algorithm1_findCycle; rw [dite_eq_right hEmptyS]; rfl
    let m1 := Function.update (Function.update (Function.update (Function.update mem
      (descBase + 2) workHeap) (descBase + 3) 0) (descBase + 4) workHeap) (descBase + 5) 0
    have hm1_out (a : ℕ) (h2 : a ≠ descBase + 2) (h3 : a ≠ descBase + 3)
        (h4 : a ≠ descBase + 4) (h5 : a ≠ descBase + 5) : m1 a = mem a := by
      dsimp only [m1]
      rw [Function.update_of_ne h5, Function.update_of_ne h4,
        Function.update_of_ne h3, Function.update_of_ne h2]
    have hrun : ∃ o st' c, Runs w p ω
        (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches)
        (startState [root, loc.hb, descBase, workHeap] mem pos) o st' c ∧
        (o = .returned workHeap ∧ st'.mem = m1) ∧ c ≤ selectRawRouteCost loc.Lk maxEdges := by
      apply runs_start_le (T := selectRawRouteCost loc.Lk maxEdges)
      unfold selectRawRouteBody
      refine runs_seq_assign_flat (v := 0)
        (by simp [Expr.eval, hhdSize, hsz0]) ?_
      refine WordRAM.runs_cond_le (v := 1)
        (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega])
        ?_ (fun h => absurd h (by decide))
      intro _
      refine runs_seq_store_flat (x := descBase + 2) (v := workHeap) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_flat (x := descBase + 3) (v := 0) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_flat (x := descBase + 4) (v := workHeap) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_flat (x := descBase + 5) (v := 0) (by eval_expr) (by eval_expr) ?_
      refine WordRAM.runs_ret_le (v := workHeap) (by eval_expr) ⟨rfl, rfl⟩ ?_
      simp only [selectRawRouteCost, Expr.size]; omega
    obtain ⟨o, st', c, hrun', ⟨rfl, hstMem⟩, hcLe⟩ := hrun
    have hpres := hPresTok m1 fun a ha => hm1_out a (by omega) (by omega) (by omega) (by omega)
    refine ⟨workHeap, c, st', [], [], hrun', le_rfl, Nat.le_add_right _ _,
      Nat.zero_le _, Nat.zero_le _,
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self, Function.update_of_ne (by omega), Function.update_self]; simp,
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]; simp,
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]; rfl,
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_self],
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_self]; simp,
      by rw [hstMem]; dsimp only [m1]; rw [Function.update_self]; rfl,
      (fun i hi => by simp at hi), (fun i hi => by simp at hi),
      (fun _ h => by cases h), (fun _ h => by cases h),
      (fun _ h => by cases h),
      (fun ei => by simp [hAlg0 ei]),
      (fun _ h => by simp at h), (fun _ h => by simp at h),
      htag18Lt,
      hstMem ▸ hpres.1, hstMem ▸ hpres.2.2.1, hnum, hstMem ▸ hpres.2.2.2.1, hstMem ▸ hpres.2.2.2.2,
      (fun a ha => (hstMem ▸ hm1_out a (by omega) (by omega) (by omega) (by omega)).trans (hz a (by omega))),
      (fun a ha => hstMem ▸ hm1_out a (by omega) (by omega) (by omega) (by omega)),
      hstMem ▸ hpres.2.1, hcLe⟩
  · -- Nonempty heap (`0 < size`): read top candidate `eBest = arr[0]`
    have hszPos : 0 < size := Nat.pos_of_ne_zero hsz0
    obtain ⟨hne, heBestEq, hiEq, _⟩ := (selectHeapMatchesChain_root hH hSpan hMatch).2 hszPos
    set eBest := mem loc.arrPtr
    set i := mem (loc.lvlPtr + eBest)
    set W := C.sparsifierCycle i eBest
    set flip := !(decide (walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0))
    have hne' : ((model.chain.G 0).E \ C.chainTree.E).Nonempty := hne
    have heBestEq' : eBest = leastArgmax ((model.chain.G 0).E \ C.chainTree.E)
        (heapCycleRatio C model.chain.g model.chain.ℓ) hne' := heBestEq
    have heBestS : eBest ∈ (model.chain.G 0).E \ C.chainTree.E := by
      rw [heBestEq']; exact (leastArgmax_spec _ _ hne').1
    have hKeyRep : SelectKeyRepresents (loc.readNum mem 4 eBest) (loc.readDen mem 4 eBest)
        (walkInner (C.chainGrad model.chain.g (C.edgeLevel eBest + 1))
          (C.sparsifierCycle (C.edgeLevel eBest) eBest))
        (C.wlen model.chain.ℓ eBest) :=
      (hMatch.2.2.2 eBest heBestS).2
    have heBestCap : eBest < loc.cap := (hMatch.2.2.1 eBest).mpr heBestS |>.1
    have heBestNZ : mem (loc.posPtr + eBest) ≠ 0 := (hMatch.2.2.1 eBest).mpr heBestS |>.2
    have hiLeD : i ≤ C.d := by rw [hiEq]; exact (C.mem_activeCore_diff_edgeLevel hH heBestS).1
    have heBestCore : eBest ∈ (C.activeCore i).E \ (C.activeS i).E := by
      rw [hiEq]; exact (C.mem_activeCore_diff_edgeLevel hH heBestS).2
    have hRawSpec := rawRouteOfWalk_spec model hH hSpan hFresh hVlt hne'
    have hRawSpec' :
        (rawEdgesOfWalk C.chainTree W flip).length ≤ W.length ∧
        (rawPathsOfWalk (model.chain.G 0) C.chainTree W flip).length ≤ 2 * W.length ∧
        (∀ x ∈ rawEdgesOfWalk C.chainTree W flip, x.1 ∈ (model.chain.G 0).E \ C.chainTree.E) ∧
        (∀ p ∈ rawPathsOfWalk (model.chain.G 0) C.chainTree W flip,
          p.1 < model.extG.n ∧ p.2 < model.extG.n ∧ C.chainTree.Connected p.1 p.2) ∧
        (∀ ei : ℕ, (algorithm1_findCycle model.chain).1 ei =
          ((rawEdgesOfWalk C.chainTree W flip).map (fun x => walkFlow [x] ei)).sum +
          ((rawPathsOfWalk (model.chain.G 0) C.chainTree W flip).map
            (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) ei)).sum) := by
      have h1 := hRawSpec
      dsimp only [C] at heBestEq' hiEq h1 ⊢
      rw [← heBestEq'] at h1
      rw [← hiEq] at h1
      exact h1
    have hSameComp : ∀ p ∈ rawPathsOfWalk (model.chain.G 0) C.chainTree W flip,
        ∀ q ∈ rawPathsOfWalk (model.chain.G 0) C.chainTree W flip,
          C.chainTree.Connected p.1 q.1 :=
      rawPathsOfWalk_same_comp hH hSpan
        (fun x hx => C.G_E_subset_of_le hH (Nat.zero_le i) hiLeD
          (Finset.mem_sdiff.mp (MGraph.isWalk_edges_mem (C.sparsifierCycle_isClosedWalk hH hSpan hiLeD heBestCore) x hx)).1)
        (fun q hq => by
          cases hfl : flip
          · exact (hRawSpec'.2.2.2.1 q (by unfold rawPathsOfWalk; rw [List.mem_append]; right; simp [hfl]; exact hq)).2.2
          · exact MGraph.connected_symm (hRawSpec'.2.2.2.1 q.swap (by
              unfold rawPathsOfWalk; rw [List.mem_append]; right; simp [hfl]; exact hq)).2.2)
    have hHdr := hMatch.1.1
    have hLkHdr : mem (loc.hb + shLkOff) = loc.Lk := by simpa [shLkOff] using hHdr 3 (by simp)
    have hArrHdr : mem (loc.hb + shArrOff) = loc.arrPtr := by simpa [shArrOff] using hHdr 4 (by simp)
    have hLvlHdr : mem (loc.hb + shLvlOff) = loc.lvlPtr := by simpa [shLvlOff] using hHdr 6 (by simp)
    have hNumHdr : mem (loc.hb + shNumOff) = loc.numBase := by simpa [shNumOff] using hHdr 7 (by simp)
    have hMetaHdr : mem (loc.hb + shMetaOff) = loc.metaPtr := by simpa [shMetaOff] using hHdr 13 (by simp)
    have hHandle : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
    have hSlots : mem (root + 6) = tok.slots := by simpa using hrootDir 6 (by simp)
    have hRootG : mem (root + 14) = tok.rootGraph := by simpa using hrootDir 14 (by simp)
    have hD11 : mem (tok.handle + 11) = cfg.P.d := by
      have h := hinitP 2 (by simp); simpa [Nat.add_assoc] using h
    have hHandle11W : tok.handle + 11 < 2 ^ w :=
      lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t2 11 (by decide)]; decide)))) (by omega)
    have hLay : loc.Lk < 2 ^ w ∧ loc.arrPtr < 2 ^ w ∧ loc.lvlPtr < 2 ^ w ∧ loc.numBase < 2 ^ w ∧
        loc.metaPtr < 2 ^ w ∧ eBest < 2 ^ w ∧ loc.lvlPtr + eBest < 2 ^ w ∧
        loc.numBase + eBest * loc.Lk + loc.Lk < 2 ^ w ∧ i < 2 ^ w := by
      have hend := loc.endAddr_eq; unfold selectHeapSize shHdrSize at hend
      have heLk : eBest * loc.Lk + loc.Lk ≤ loc.cap * loc.Lk := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right loc.Lk (Nat.succ_le_of_lt heBestCap)
      have hLkLe : loc.Lk ≤ loc.cap * loc.Lk := Nat.le_trans (Nat.le_add_left _ _) heLk
      have hmsz := hMetaE.1; unfold selectLevelMetaSize at hmsz
      unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead
        SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr shHdrSize at *
      omega
    have hNumValid : Num.Valid mem (loc.numBase + eBest * loc.Lk) 4 loc.Lk :=
      (hMatch.1.2.2.1 eBest heBestCap heBestNZ).2.1
    have hFlipBit : (if ((if Num.intVal mem (loc.numBase + eBest * loc.Lk) 4 loc.Lk < 0 then 1 else 0) +
        (if Num.intVal mem (loc.numBase + eBest * loc.Lk) 4 loc.Lk = 0 then 1 else 0)) = 0 then 1 else 0) =
        (if flip then 1 else 0) := by
      have hleIff : walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0 ↔
          Num.intVal mem (loc.numBase + eBest * loc.Lk) 4 loc.Lk ≤ 0 := by
        have h1 := hKeyRep.nonpos_iff
        rw [← hiEq] at h1
        simpa [SelectHeapLoc.readNum, eBest, i, W] using h1.symm
      dsimp only [flip]
      by_cases hneg : Num.intVal mem (loc.numBase + eBest * loc.Lk) 4 loc.Lk < 0
      · have hle : walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0 := hleIff.mpr (le_of_lt hneg)
        simp [hneg, hle]
      · by_cases hz0 : Num.intVal mem (loc.numBase + eBest * loc.Lk) 4 loc.Lk = 0
        · have hle : walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0 := hleIff.mpr (le_of_eq hz0)
          simp [hz0, hle]
        · have hnle : ¬ walkInner (C.chainGrad model.chain.g (i + 1)) W ≤ 0 :=
            fun h => by have := hleIff.mp h; omega
          simp [hneg, hz0, hnle]
    -- Root DynGraphAt bounds
    have hRootGLt : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ descBase := by
      by_contra hgt; push Not at hgt
      have hlo : tok.rootGraph ≤ tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1 := by
        unfold dynGraphSize; omega
      have hlt : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1 < descBase :=
        hbelow _ (Or.inl (hOwn _ (by rw [t20 _ hlo (by omega)]; decide)))
      omega
    have hSlotsLt : tok.slots + tok.intCap ≤ descBase := by
      have hpos : 0 < tok.intCap := hIntB.2.1
      have hlt : tok.slots + (tok.intCap - 1) < descBase :=
        hbelow _ (Or.inl (hOwn _ (by rw [t9 (tok.intCap - 1) (by omega)]; decide)))
      omega
    have hRootVC : mem tok.rootGraph = model.extG.n := by simpa [dgVCapOff] using hRootDG.2.2.2.1
    have hRootEC : mem (tok.rootGraph + 1) = tok.rootECap := by simpa [dgECapOff] using hRootDG.2.2.2.2.1
    have hRootDG_ends : ∀ f ∈ (model.chain.G 0).E,
        mem (dgIntToExtBase tok.rootGraph model.extG.n +
          mem (dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + f)) = (model.chain.G 0).tail f ∧
        mem (dgIntToExtBase tok.rootGraph model.extG.n +
          mem (dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + f)) = (model.chain.G 0).head f ∧
        dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + f < descBase ∧
        dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + f < descBase ∧
        dgIntToExtBase tok.rootGraph model.extG.n +
          mem (dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + f) < descBase ∧
        dgIntToExtBase tok.rootGraph model.extG.n +
          mem (dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + f) < descBase ∧
        (model.chain.G 0).tail f < 2 ^ w ∧ (model.chain.G 0).head f < 2 ^ w := by
      intro f hf
      have hfEC : f < tok.rootECap := hRootDG.2.2.1 f hf
      have hG0Val := hRootDG.1 f hf
      have hTlt : (model.chain.G 0).tail f < model.extG.n := hRootDG.2.1 _ hG0Val.1
      have hHlt : (model.chain.G 0).head f < model.extG.n := hRootDG.2.1 _ hG0Val.2
      obtain ⟨hTsl, hHsl⟩ := hRootDG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hf
      obtain ⟨hTev, hTinv⟩ := hRootDG.2.2.2.2.2.2.2.2.2.1 _ hG0Val.1
      obtain ⟨hHev, hHinv⟩ := hRootDG.2.2.2.2.2.2.2.2.2.1 _ hG0Val.2
      have hTeLt : mem (dgExtToIntBase tok.rootGraph model.extG.n + (model.chain.G 0).tail f) < model.extG.n :=
        hRootDG.2.1 _ hTev
      have hHeLt : mem (dgExtToIntBase tok.rootGraph model.extG.n + (model.chain.G 0).head f) < model.extG.n :=
        hRootDG.2.1 _ hHev
      have hdgsz : dynGraphSize model.extG.n tok.rootECap = 4 + 7 * model.extG.n + 9 * tok.rootECap := rfl
      refine ⟨hTsl ▸ hTinv, hHsl ▸ hHinv, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold dgETailSlotBase; omega
      · unfold dgEHeadSlotBase; omega
      · rw [hTsl]; unfold dgIntToExtBase; omega
      · rw [hHsl]; unfold dgIntToExtBase; omega
      · omega
      · omega
    -- Common prefix execution up to `.cond (.bin .eq (.reg 10) (.reg 16))`
    have hRt14W : root + 14 < 2 ^ w :=
      lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t1 14 (by decide)]; decide)))) (by omega)
    obtain ⟨regsP, posP, kP, hRunP, _hr0, hr1, hr2, hr3, hr9, hr10, hr14, _hr15, hr16, hr17, _hr20,
      hr21, hr22, hr23, hkP⟩ :=
      selectRawRoute_prefix_runs (fillRev := fillRev)
        (splitSteps := splitSteps) (emitStitches := emitStitches) (eBest := eBest) (i := i)
        hw16 hIsNeg hIsZero hsz0 hhdSize hLkHdr hArrHdr hLvlHdr hNumHdr rfl rfl
        hNumValid hFlipBit hHandle hD11 hSlots hRootG hRootVC hRootEC
        ⟨by have := loc.endAddr_eq; unfold selectHeapSize shHdrSize shNumOff at *; omega,
         hLay.2.2.2.2.2.2.1, hLay.2.2.2.2.2.2.2.1, hRt14W, hHandle11W, by omega, hLay.1⟩
    -- Branch on `i = cfg.P.d` vs `i < cfg.P.d`
    by_cases hid : i = cfg.P.d
    · -- `i = d`: cycle length `K = 1`, direct 1-edge + 1-path emission
      have hW1 : W = [(eBest, true)] := by
        dsimp only [W]; rw [hid, TreeChain.sparsifierCycle, TreeChain.activeEmb, ite_eq_right (by omega)]; rfl
      have heG0 : eBest ∈ (model.chain.G 0).E := (Finset.mem_sdiff.mp heBestS).1
      have heNotT : eBest ∉ C.chainTree.E := (Finset.mem_sdiff.mp heBestS).2
      have hEd1 : rawEdgesOfWalk C.chainTree W flip = [(eBest, !flip)] := by
        rw [hW1]; unfold rawEdgesOfWalk orientWalkSteps; cases flip <;> simp [heNotT]
      have hPt1 : rawPathsOfWalk (model.chain.G 0) C.chainTree W flip =
          [if !flip then ((model.chain.G 0).head eBest, (model.chain.G 0).tail eBest)
           else ((model.chain.G 0).tail eBest, (model.chain.G 0).head eBest)] := by
        rw [hW1]; unfold rawPathsOfWalk orientWalkSteps
        cases flip <;> simp [heNotT, cycleSegments, cycleSegmentsAux, MGraph.src, MGraph.dst]
      obtain ⟨hT0, hH0, hts0, hhs0, hi2eT0, hi2eH0, hT0W, hH0W⟩ := hRootDG_ends eBest heG0
      set dirBit : ℕ := if !flip then 1 else 0
      set pU : ℕ := if !flip then (model.chain.G 0).head eBest else (model.chain.G 0).tail eBest
      set pV : ℕ := if !flip then (model.chain.G 0).tail eBest else (model.chain.G 0).head eBest
      let m1 := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update mem
          workHeap eBest) (workHeap + 1) dirBit) (workHeap + 2) pU) (workHeap + 3) pV)
          (descBase + 2) workHeap) (descBase + 3) 1) (descBase + 4) (workHeap + 2)) (descBase + 5) 1
      have hm1_out (a : ℕ) (hlo : a < descBase ∨ a = descBase ∨ a = descBase + 1 ∨ workHeap + 4 ≤ a) :
          m1 a = mem a := by
        dsimp only [m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hrun : ∃ o st' c, Runs w p ω
          (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches)
          (startState [root, loc.hb, descBase, workHeap] mem pos) o st' c ∧
          (o = .returned (workHeap + 4) ∧ st'.mem = m1) ∧
          c ≤ selectRawRouteCost loc.Lk maxEdges := by
        refine hRunP (fun o st' => o = .returned (workHeap + 4) ∧ st'.mem = m1)
          (selectRawRouteCost loc.Lk maxEdges) ?_
        refine WordRAM.runs_cond_le (v := 1)
          (by simp [Expr.eval, BinOp.eval, hr10, hr16, hid, show 1 < 2 ^ w by omega])
          ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assign_flat (v := workHeap) (by simp [Expr.eval, hr3]) ?_
        refine runs_seq_assign_flat (v := workHeap + 2)
          (by simp [Expr.eval, BinOp.eval, hr3, show 2 < 2 ^ w by omega, show workHeap + 2 < 2 ^ w by omega]) ?_
        refine runs_seq_assign_flat (v := dirBit)
          (by cases hfl : flip <;> simp [Expr.eval, BinOp.eval, hr14, show 0 < 2 ^ w by omega,
                show 1 < 2 ^ w by omega, dirBit, hfl]) ?_
        have hts0W : dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + eBest < 2 ^ w := by omega
        have hhs0W : dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + eBest < 2 ^ w := by omega
        have hi2eT0W : dgIntToExtBase tok.rootGraph model.extG.n +
            mem (dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + eBest) < 2 ^ w := by omega
        have hi2eH0W : dgIntToExtBase tok.rootGraph model.extG.n +
            mem (dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + eBest) < 2 ^ w := by omega
        refine runs_seq_assign_flat (v := (model.chain.G 0).tail eBest)
          (by simp [Expr.eval, BinOp.eval, hr21, hr22, hr9, hts0W, hi2eT0W, hT0]) ?_
        refine runs_seq_assign_flat (v := (model.chain.G 0).head eBest)
          (by simp [Expr.eval, BinOp.eval, hr21, hr23, hr9, hhs0W, hi2eH0W, hH0]) ?_
        refine runs_seq_store_flat (x := workHeap) (v := eBest) (by eval_expr) (by simp [Expr.eval, hr9]) ?_
        refine runs_seq_store_flat (x := workHeap + 1) (v := dirBit)
          (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show workHeap + 1 < 2 ^ w by omega])
          (by eval_expr) ?_
        have hPostStore : ∀ (regs2 : ℕ → ℕ) (k2 : ℕ),
            regs2 2 = descBase → regs2 3 = workHeap → regs2 24 = workHeap → regs2 25 = workHeap + 2 →
            k2 + 45 ≤ selectRawRouteCost loc.Lk maxEdges →
            ∃ o st' c, Runs w p ω
              (.store (.bin .add (.reg 2) (.const 2)) (.reg 24) ;;
               .store (.bin .add (.reg 2) (.const 3)) (.const 1) ;;
               .store (.bin .add (.reg 2) (.const 4)) (.reg 25) ;;
               .store (.bin .add (.reg 2) (.const 5)) (.const 1) ;;
               .ret (.bin .add (.reg 3) (.const 4)))
              ⟨Function.update (Function.update (Function.update (Function.update mem
                workHeap eBest) (workHeap + 1) dirBit) (workHeap + 2) pU) (workHeap + 3) pV,
               regs2, posP⟩ o st' c ∧
              (o = .returned (workHeap + 4) ∧ st'.mem = m1) ∧
              k2 + c ≤ selectRawRouteCost loc.Lk maxEdges := by
          intro regs2 k2 r2 r3 r24 r25 hk2
          refine runs_seq_store_flat (x := descBase + 2) (v := workHeap)
            (by simp [Expr.eval, BinOp.eval, r2, show 2 < 2 ^ w by omega, show descBase + 2 < 2 ^ w by omega])
            (by simp [Expr.eval, r24]) ?_
          refine runs_seq_store_flat (x := descBase + 3) (v := 1)
            (by simp [Expr.eval, BinOp.eval, r2, show 3 < 2 ^ w by omega, show descBase + 3 < 2 ^ w by omega])
            (by eval_expr) ?_
          refine runs_seq_store_flat (x := descBase + 4) (v := workHeap + 2)
            (by simp [Expr.eval, BinOp.eval, r2, show 4 < 2 ^ w by omega, show descBase + 4 < 2 ^ w by omega])
            (by simp [Expr.eval, r25]) ?_
          refine runs_seq_store_flat (x := descBase + 5) (v := 1)
            (by simp [Expr.eval, BinOp.eval, r2, show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega])
            (by eval_expr) ?_
          refine WordRAM.runs_ret_le (v := workHeap + 4)
            (by simp [Expr.eval, BinOp.eval, r3, show 4 < 2 ^ w by omega, show workHeap + 4 < 2 ^ w by omega])
            ⟨rfl, rfl⟩ (by simp [Expr.size]; omega)
        by_cases hfl : flip = true
        · refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval, dirBit, hfl])
            (fun h => absurd rfl h) ?_
          intro _
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_flat (x := workHeap + 2) (v := pU) (by eval_expr)
            (by simp [Expr.eval, pU, hfl]) ?_
          refine runs_seq_store_flat (x := workHeap + 3) (v := pV)
            (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show workHeap + 3 < 2 ^ w by omega])
            (by simp [Expr.eval, pV, hfl]) ?_
          apply hPostStore
          all_goals first | (simp [hr2, hr3]; done) | (simp [selectRawRouteCost, Expr.size]; omega)
        · have hflF : flip = false := Bool.eq_false_iff.mpr hfl
          refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval, dirBit, hflF])
            ?_ (fun h => absurd h (by decide))
          intro _
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_flat (x := workHeap + 2) (v := pU) (by eval_expr)
            (by simp [Expr.eval, pU, hflF]) ?_
          refine runs_seq_store_flat (x := workHeap + 3) (v := pV)
            (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show workHeap + 3 < 2 ^ w by omega])
            (by simp [Expr.eval, pV, hflF]) ?_
          apply hPostStore
          all_goals first | (simp [hr2, hr3]; done) | (simp [selectRawRouteCost, Expr.size]; omega)
      obtain ⟨o, st', c, hrun', ⟨rfl, hstMem⟩, hcLe⟩ := hrun
      have hpres := hPresTok m1 fun a ha => hm1_out a (Or.inl ha)
      have hm1_d2 : m1 (descBase + 2) = workHeap := by
        dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      have hm1_d3 : m1 (descBase + 3) = 1 := by
        dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      have hm1_d4 : m1 (descBase + 4) = workHeap + 2 := by
        dsimp only [m1]; rw [Function.update_of_ne (by omega), Function.update_self]
      have hm1_d5 : m1 (descBase + 5) = 1 := by
        dsimp only [m1]; rw [Function.update_self]
      refine ⟨workHeap + 4, c, st',
        rawEdgesOfWalk C.chainTree W flip, rawPathsOfWalk (model.chain.G 0) C.chainTree W flip,
        hrun', by omega, by omega,
        by rw [hEd1]; simp; omega, by rw [hPt1]; simp; omega,
        by rw [hstMem, hm1_d2], by rw [hstMem, hm1_d2, hm1_d4, hEd1]; simp,
        by rw [hstMem, hm1_d2, hEd1]; simp,
        by rw [hstMem, hm1_d3, hEd1]; rfl,
        by rw [hstMem, hm1_d4]; omega,
        by rw [hstMem, hm1_d4, hPt1]; simp,
        by rw [hstMem, hm1_d5, hPt1]; rfl,
        by
          rw [hstMem, hm1_d2, hEd1]
          intro j hj
          have hj0 : j = 0 := by simp at hj; omega
          subst hj0
          simp only [Nat.mul_zero, Nat.add_zero]
          refine ⟨?_, ?_⟩
          · dsimp only [m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]; rfl
          · dsimp only [m1, dirBit]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
            cases flip <;> rfl,
        by
          rw [hstMem, hm1_d4, hPt1]
          intro j hj
          have hj0 : j = 0 := by simp at hj; omega
          subst hj0
          simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
          refine ⟨?_, ?_⟩
          · dsimp only [m1, pU]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
            cases flip <;> rfl
          · dsimp only [m1, pV]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
            cases flip <;> rfl,
        hRawSpec'.2.2.1, hRawSpec'.2.2.2.1, hSameComp, hRawSpec'.2.2.2.2,
        fun x _ hf => by rw [hstMem, hm1_d2] at hf; have := hbelow _ hf; omega,
        fun x _ hf => by rw [hstMem, hm1_d4] at hf; have := hbelow _ hf; omega,
        htag18Lt,
        hstMem ▸ hpres.1, hstMem ▸ hpres.2.2.1, hnum, hstMem ▸ hpres.2.2.2.1, hstMem ▸ hpres.2.2.2.2,
        fun a ha => (hstMem ▸ hm1_out a (Or.inr (Or.inr (Or.inr ha)))).trans (hz a (by omega)),
        fun a ha => hstMem ▸ hm1_out a (Or.inl ha),
        hstMem ▸ hpres.2.1, hcLe⟩
    · -- `i < d`: direct lookup in owned `embPtr[i]`, then `fillRev` + `splitSteps` + `emitStitches`
      have hiLtD : i < cfg.P.d := by omega
      have hWlt : W = (eBest, true) :: walkRev (C.activeEmb i eBest) := rfl
      set embP := C.activeEmb i eBest
      set K := embP.length + 1
      have hWlen : W.length = K := by rw [hWlt]; simp [walkRev, K]
      have hKleMax : K ≤ maxEdges := hEmbBd i hiLtD eBest heBestCore
      obtain ⟨hMetaBd, hMetaEmb⟩ := hMetaE
      obtain ⟨hEmbPtrLt, hwPtrHi, hMW1⟩ := hMetaEmb i hiLtD eBest (Finset.mem_sdiff.mp heBestCore).1
      set embPtr := mem (smEntryAddr loc.metaPtr C.d 5 i)
      have hMWlen : (mWalkEncode embP).length = 1 + 2 * embP.length := mWalkEncode_length embP
      -- Every edge `x ∈ W` is in `(C.G 0).E`, with `x.1 ∈ C.chainTree.E ↔ mem (tok.slots + x.1) ≠ 0`
      have hWE_G0 : ∀ x ∈ W, x.1 ∈ (model.chain.G 0).E := by
        intro x hx
        have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hiLeD heBestCore
        exact C.G_E_subset_of_le hH (Nat.zero_le i) hiLeD
          (Finset.mem_sdiff.mp (MGraph.isWalk_edges_mem hClosed x hx)).1
      have hWE_slot_lt : ∀ x ∈ (eBest, true) :: walkRev embP,
          x.1 ∈ (model.chain.G 0).E ∧ (x.1 ∈ C.chainTree.E ↔ mem (tok.slots + x.1) ≠ 0) ∧
          tok.slots + x.1 < descBase ∧ x.1 < 2 ^ w := by
        intro x hx
        have hxW : x ∈ W := hWlt.symm ▸ hx
        have hxG0 := hWE_G0 x hxW
        have hxIntCap : x.1 < tok.intCap := hIntB.1 x.1 hxG0
        obtain ⟨heFwd, heExt⟩ := hFresh.hRight x.1 hxG0
        have hacc := hedgeAcc.1 (model.intToExt x.1) heExt
        dsimp only at hacc
        rw [heFwd] at hacc
        refine ⟨hxG0, ?_, by omega, by omega⟩
        have hbr := hacc.2.2
        by_cases hxT : x.1 ∈ C.chainTree.E
        · rw [ite_eq_left hxT] at hbr
          exact ⟨fun _ => hbr.1, fun _ => hxT⟩
        · rw [ite_eq_right hxT] at hbr
          exact ⟨fun h => (hxT h).elim, fun hnz => (hnz hbr.1).elim⟩
      have hEmbPw : ∀ j (hj : j < embP.length), embP[j].1 < 2 ^ w := fun j hj => by
        have hmem : (embP[j].1, !embP[j].2) ∈ (eBest, true) :: walkRev embP := by
          apply List.mem_cons_of_mem
          unfold walkRev; rw [List.mem_reverse, List.mem_map]
          exact ⟨embP[j], List.getElem_mem hj, rfl⟩
        exact (hWE_slot_lt _ hmem).2.2.2
      set edgesBase := workHeap + 2 * K
      set pathsBase := workHeap + 4 * K
      set work1 := workHeap + 8 * K
      have hwork1W : work1 < 2 ^ w := by unfold selectRawRouteSpace at hroom; omega
      have hWE_ends_lt : ∀ x ∈ (eBest, true) :: walkRev embP,
          mem (dgIntToExtBase tok.rootGraph model.extG.n +
            mem (dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + x.1)) = (model.chain.G 0).tail x.1 ∧
          mem (dgIntToExtBase tok.rootGraph model.extG.n +
            mem (dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + x.1)) = (model.chain.G 0).head x.1 ∧
          dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + x.1 < descBase ∧
          dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + x.1 < descBase ∧
          dgIntToExtBase tok.rootGraph model.extG.n +
            mem (dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap + x.1) < descBase ∧
          dgIntToExtBase tok.rootGraph model.extG.n +
            mem (dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap + x.1) < descBase ∧
          (model.chain.G 0).tail x.1 < 2 ^ w ∧ (model.chain.G 0).head x.1 < 2 ^ w :=
        fun x hx => hRootDG_ends x.1 (hWE_G0 x (hWlt.symm ▸ hx))
      have hRegW : tok.slots < 2 ^ w ∧ dgIntToExtBase tok.rootGraph model.extG.n < 2 ^ w ∧
          dgETailSlotBase tok.rootGraph model.extG.n tok.rootECap < 2 ^ w ∧
          dgEHeadSlotBase tok.rootGraph model.extG.n tok.rootECap < 2 ^ w := by
        have hdgsz : dynGraphSize model.extG.n tok.rootECap = 4 + 7 * model.extG.n + 9 * tok.rootECap := rfl
        unfold dgIntToExtBase dgETailSlotBase dgEHeadSlotBase; omega
      have hEmbPtrLt' : embPtr + eBest < workHeap := by
        change embPtr + eBest < descBase at hEmbPtrLt; omega
      have hwPtrHi' : mem (embPtr + eBest) + 1 + 2 * embP.length ≤ workHeap := by
        rw [hMWlen] at hwPtrHi
        change mem (embPtr + eBest) + (1 + 2 * embP.length) ≤ descBase at hwPtrHi
        omega
      obtain ⟨stBr, cBr, hrBr, hd2Br, hd3Br, hd4Br, hd5Br, hEdBr, hPtBr, hfrBr, hcBr⟩ :=
        selectRawRoute_branch_lt_runs (G0 := model.chain.G 0) (F := C.chainTree)
          (embPtr := embPtr) (embP := embP)
          hw16 (hFillRev embP) (hSplitSteps (model.chain.G 0) C.chainTree ((eBest, true) :: walkRev embP) flip)
          (hEmitStitches (model.chain.G 0) ((eBest, true) :: walkRev embP) flip _)
          hr1 hr2 hr3 hr9 hr10 hr14 hr16 hr17 hr21 hr22 hr23
          hMetaHdr (by rw [← hCdEq])
          (by have := loc.endAddr_eq; unfold selectHeapSize shHdrSize shMetaOff at *; omega)
          (by rw [← hCdEq]; omega) hiLtD hwh hwork1W hEmbPtrLt' hwPtrHi'
          hMW1 hEmbPw hWE_ends_lt hWE_slot_lt hRegW
      have hrun : ∃ o st' c, Runs w p ω
          (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches)
          (startState [root, loc.hb, descBase, workHeap] mem pos) o st' c ∧
          (o = .returned work1 ∧
           st'.mem (descBase + 2) = edgesBase ∧
           st'.mem (descBase + 3) = (rawEdgesOfWalk C.chainTree W flip).length ∧
           st'.mem (descBase + 4) = pathsBase ∧
           st'.mem (descBase + 5) = (rawPathsOfWalk (model.chain.G 0) C.chainTree W flip).length ∧
           ExplicitEdgesAt st'.mem edgesBase (rawEdgesOfWalk C.chainTree W flip) ∧
           PathEndpointsAt st'.mem pathsBase (rawPathsOfWalk (model.chain.G 0) C.chainTree W flip) ∧
           (∀ a, (a < descBase ∨ work1 ≤ a) → st'.mem a = mem a)) ∧
          c ≤ selectRawRouteCost loc.Lk maxEdges := by
        refine hRunP (fun o st' =>
          o = .returned work1 ∧
          st'.mem (descBase + 2) = edgesBase ∧
          st'.mem (descBase + 3) = (rawEdgesOfWalk C.chainTree W flip).length ∧
          st'.mem (descBase + 4) = pathsBase ∧
          st'.mem (descBase + 5) = (rawPathsOfWalk (model.chain.G 0) C.chainTree W flip).length ∧
          ExplicitEdgesAt st'.mem edgesBase (rawEdgesOfWalk C.chainTree W flip) ∧
          PathEndpointsAt st'.mem pathsBase (rawPathsOfWalk (model.chain.G 0) C.chainTree W flip) ∧
          (∀ a, (a < descBase ∨ work1 ≤ a) → st'.mem a = mem a))
          (selectRawRouteCost loc.Lk maxEdges) ?_
        have hKmul : 350 * K ≤ 350 * maxEdges := Nat.mul_le_mul_left 350 hKleMax
        refine ⟨.returned work1, stBr, cBr + 4, ?_,
          ⟨rfl, hd2Br, hWlt.symm ▸ hd3Br, hd4Br, hWlt.symm ▸ hd5Br,
            hWlt.symm ▸ hEdBr, hWlt.symm ▸ hPtBr, hfrBr⟩, by unfold selectRawRouteCost; omega⟩
        exact runs_cond_iff.mpr ⟨0, cBr,
          by simp [Expr.eval, BinOp.eval, hr10, hr16, hid, show 0 < 2 ^ w by omega],
          hrBr, by simp [Expr.size]; omega⟩
      obtain ⟨o, st', c, hrun', ⟨rfl, hd2, hd3, hd4, hd5, hEdAt, hPtAt, hfrSt⟩, hcLe⟩ := hrun
      have hpres := hPresTok st'.mem fun a ha => hfrSt a (Or.inl ha)
      refine ⟨work1, c, st',
        rawEdgesOfWalk C.chainTree W flip, rawPathsOfWalk (model.chain.G 0) C.chainTree W flip,
        hrun', by omega, by unfold selectRawRouteSpace; omega,
        le_trans hRawSpec'.1 (by omega), le_trans hRawSpec'.2.1 (by omega),
        by rw [hd2]; omega, by rw [hd2, hd4]; have := hRawSpec'.1; omega,
        by rw [hd2]; have := hRawSpec'.1; omega, hd3,
        by rw [hd4]; omega, by rw [hd4]; have := hRawSpec'.2.1; omega, hd5,
        by rw [hd2]; exact hEdAt, by rw [hd4]; exact hPtAt,
        hRawSpec'.2.2.1, hRawSpec'.2.2.2.1, hSameComp, hRawSpec'.2.2.2.2,
        fun x _ hf => by rw [hd2] at hf; have := hbelow _ hf; omega,
        fun x _ hf => by rw [hd4] at hf; have := hbelow _ hf; omega,
        htag18Lt, hpres.1, hpres.2.2.1, hnum, hpres.2.2.2.1, hpres.2.2.2.2,
        fun a ha => (hfrSt a (Or.inr ha)).trans (hz a (by omega)),
        fun a ha => hfrSt a (Or.inl ha),
        hpres.2.1, hcLe⟩

end MinCostFlow.MinRatio
