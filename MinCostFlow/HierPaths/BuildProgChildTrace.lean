module

public import MinCostFlow.HierPaths.BuildProgChildTraceBase
public import MinCostFlow.HierPaths.BuildProgChildTraceRounds
import MinCostFlow.HierPaths.BuildProgGameStepMemory
import MinCostFlow.HierPaths.BuildProgChoiceSaved
import MinCostFlow.HierPaths.InitBlockLen
import MinCostFlow.HierPaths.InitLayout

/-!
# Final injection archive invariant

Extends `TraceRoundsMem` across `buildInjectEndContract` and proves `InjArchive` for the final
injection (`finishedLevelMem_of_inject`).
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- After the final injection `buildInjectEndContract`, both `TraceRoundsMem` and the
injection archive `InjArchive` hold on the resulting memory. -/
theorem finishedLevelMem_of_inject {w tailBudget : ℕ} {D : ChoiceLoopData} {β : ℝ}
    {bh heap₁ slot injEnd runEnd : ℕ} {initial mem₂ mem₃ : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap₁ sts mem₂)
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hInit : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hDirZero : ∀ r < D.limit, initial (D.directory + r) = 0)
    (hRoom : ∀ t' heap' sts' mem', t' < D.limit →
      ChoiceLoopTrace w D initial t' heap' sts' mem' → (D.round sts').jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap' sts')
    (hAffine : ∀ i, D.childAddr i = slot + i * D.geometry.slotWords)
    (hRes : lemma1Route D.base.route D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L = (.matched Ms emb, runEnd))
    (hB : runEnd ≤ bh)
    (hMatch : RouteMatchedSpec D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
      D.base.Δ D.base.L runEnd 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card)
    (hInjPost : (buildInjectEndContract w D heap₁ slot sts Ms emb).post
      (injectEndArgs D heap₁ slot) mem₂ injEnd mem₃) :
    let F := finishedChildFamily D.base.route D.base.host D.base.verts D.base.Δ D.base.L
      D.base.childSize D.count D.offset sts
    TraceRoundsMem D D.limit heap₁ sts mem₃ ∧
    InjArchive D.base.host D.base.childSize D.count D.base.pathBound (roundRouteCap D)
      slot D.geometry.slotWords heap₁ injEnd F (fun c => (sts c).rounds.flatten.map Prod.snd) mem₃ := by
  have hM := hTrace.memory le_rfl h hL hInit hRoom
  have hRounds := hTrace.roundsMem le_rfl h hL hInit hDirZero hRoom
  obtain ⟨top, mid, hTopLo, hTopHi, hRoutePost, hFinPost⟩ := hInjPost
  obtain ⟨_, _, _, _, _, hreq, hMidHeap, hRepMid, _, _, hRouteFrame, _⟩ := hRoutePost
  simp only [List.cons.injEq, and_true, true_and] at hreq
  obtain ⟨rfl, rfl, rfl, rfl, _, rfl⟩ := hreq
  have hPairsLen : (injPairs D.base.childSize D.count D.offset sts).length = D.count := by
    simp [injPairs]
  have hMlen : Ms.length = D.count := by simpa [hPairsLen] using hMatch.1
  have hResFst : (lemma1Route D.base.route D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L).1 = .matched Ms emb :=
    congrArg Prod.fst hRes
  rw [hPairsLen, hResFst] at hRepMid
  obtain ⟨slot', rep', top', midT, hfeq, hTabPost, hBatchPost⟩ := hFinPost
  simp only [injectFinishArgs, List.cons.injEq, and_true, true_and] at hfeq
  obtain ⟨rfl, rfl, rfl⟩ := hfeq
  obtain ⟨_, _, _, _, _, _, _, _, hteq, hTabFrame, _, _, _⟩ := hTabPost
  simp only [List.cons.injEq, and_true] at hteq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hteq
  obtain ⟨_, _, _, _, _, _, _, hbeq, hAppPost⟩ := hBatchPost
  simp only [List.cons.injEq, and_true] at hbeq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, _⟩ := hbeq
  obtain ⟨mt', tb', idx', graphs', offs', tmp', ends', vs', P', dir', out', haeq,
    hInjEndEq, hZeroFinal, hZeroP, hKept, hRowAt⟩ := hAppPost
  simp only [finishBatchApplyArgs, List.cons.injEq, and_true, true_and] at haeq
  obtain ⟨rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := haeq
  let rep := injectReplyBase heap₁ D.count D.base.childSize
  let routedEnd := top
  let walkDir := routedEnd + 4
  let P := walkDir + Ms.flatten.length + D.base.pathBound + 1
  have hDirS : D.directory + D.limit ≤ D.saved := hL.directory
  have hSG : D.saved + D.count ≤ D.addrs.graphs := hL.saved
  have hGO : D.addrs.graphs + D.count ≤ D.addrs.offsets := hL.graphs
  have hOR : D.addrs.offsets + D.count ≤ D.addrs.replies := hL.offsets
  have hRH : D.addrs.replies + D.count ≤ D.addrs.heap := by
    have hr : D.addrs.replies + D.count + 1 ≤ D.addrs.heap := hL.replies; omega
  have hHeapGe : D.addrs.heap ≤ heap₁ := hM.heap
  have hLoRep : heap₁ ≤ rep := by unfold rep injectReplyBase buildBatchEnd; omega
  have hHeapLtRep : heap₁ < rep := by unfold rep injectReplyBase buildBatchEnd; omega
  have hCapSlot : ∀ c < Ms.length, (D.injectionData sts Ms emb).cap c ≤
      D.childAddr c + D.geometry.slotWords := by
    intro c hc
    have h1 := (hTrace.injectRow h hMatch hFull hc).2.1
    simpa [ChoiceLoopData.injection_child D sts Ms emb (hMlen ▸ hc)] using h1
  -- Frame lemma for cells in D.directory or [D.addrs.heap, heap₁)
  have hPres (a : ℕ) (ha : a < D.addrs.graphs ∨ (D.addrs.heap ≤ a ∧ a < heap₁)) :
      mem₃ a = mem₂ a := by
    have hRepLeHeap : D.addrs.replies ≤ D.addrs.heap := (Nat.le_add_right _ _).trans hRH
    have hAppEq : mem₃ a = midT a := by
      refine hKept a ⟨by rcases ha with h1 | ⟨_, h2⟩ <;> omega, fun j hj => ?_⟩
      have hjc : j < D.count := hMlen ▸ hj
      have hAddrEq : (D.injectionData sts Ms emb).addr j = D.childAddr j := by
        change D.childAddr ((D.injectionData sts Ms emb).child j) = _
        rw [D.injection_child sts Ms emb hjc]
      have hSlot : D.addrs.offsets + D.count ≤ D.childAddr j ∧
          D.childAddr j + D.geometry.slotWords ≤ D.addrs.replies := hL.slots j hjc
      have hCap := hCapSlot j hj
      rcases ha with h1 | ⟨h2, _⟩
      · exact Or.inl (by rw [hAddrEq]; omega)
      · exact Or.inr (hCap.trans (hSlot.2.trans (hRepLeHeap.trans h2)))
    have hTabEq : midT a = mid a := by
      rcases ha with h1 | ⟨h2, _⟩
      · exact hTabFrame.2 a (Or.inl h1) (Or.inl (by omega)) (Or.inl (by omega))
      · exact hTabFrame.2 a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    have hRtEq : mid a = mem₂ a := hRouteFrame a (by rcases ha with h1 | ⟨_, h2⟩ <;> omega)
    exact hAppEq.trans (hTabEq.trans hRtEq)
  -- Preservation of [rep, rep + |res|) and heap₁ from mid to mem₃
  have hRepFinal : ListAt mem₃ rep (routeResultWords (.matched Ms emb)) := by
    have hRepLeHeap : D.addrs.replies ≤ D.addrs.heap := (Nat.le_add_right _ _).trans hRH
    refine WordRAM.ListAt.congr hRepMid fun a ha hb => ?_
    have hAppEq : mem₃ a = midT a := by
      refine hKept a ⟨by omega, fun j hj => Or.inr ?_⟩
      have hjc : j < D.count := hMlen ▸ hj
      exact (hCapSlot j hj).trans ((hL.slots j hjc).2.trans (hRepLeHeap.trans (hHeapGe.trans (hLoRep.trans ha))))
    have hTabEq : midT a = mid a :=
      hTabFrame.2 a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    exact hAppEq.trans hTabEq
  have hMemHeapFinal : mem₃ heap₁ = routedEnd := by
    have hRepLeHeap : D.addrs.replies ≤ D.addrs.heap := (Nat.le_add_right _ _).trans hRH
    have hAppEq : mem₃ heap₁ = midT heap₁ := by
      refine hKept heap₁ ⟨by omega, fun j hj => Or.inr ?_⟩
      have hjc : j < D.count := hMlen ▸ hj
      exact (hCapSlot j hj).trans ((hL.slots j hjc).2.trans (hRepLeHeap.trans hHeapGe))
    have hTabEq : midT heap₁ = mid heap₁ :=
      hTabFrame.2 heap₁ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    exact hAppEq.trans (hTabEq.trans hMidHeap)
  constructor
  · obtain ⟨hFut, bounds, walks, holes, hb0, hbt, hbMono, hArch, hWalks⟩ := hRounds
    have hBoundsGe (r : ℕ) (hr : r ≤ D.limit) : D.addrs.heap ≤ bounds r := by
      induction r with
      | zero => rw [hb0]
      | succ r' ih' => exact (ih' (Nat.le_of_succ_le hr)).trans (hbMono r' hr)
    have hBoundsLe (r : ℕ) (hr : r ≤ D.limit) : bounds r ≤ heap₁ := by
      have hgen : ∀ d, r + d ≤ D.limit → bounds r ≤ bounds (r + d) := by
        intro d; induction d with
        | zero => intro _; simp
        | succ d' ihd => intro hle; exact (ihd (by omega)).trans (hbMono (r + d') (by omega))
      have h1 := hgen (D.limit - r) (by omega)
      rw [Nat.add_sub_of_le hr, hbt] at h1; exact h1
    refine ⟨fun r hr1 hr2 => by omega, bounds, walks, holes, hb0, hbt, hbMono, fun r hr => ?_, hWalks⟩
    rw [hPres (D.directory + r) (Or.inl (by omega))]
    exact (hArch r hr).frame fun a ha1 ha2 =>
      hPres a (Or.inr ⟨(hBoundsGe r hr.le).trans ha1, ha2.trans_le (hBoundsLe (r + 1) hr)⟩)
  · -- Prove InjArchive
    have hInjGeP : P + D.base.host.n ≤ injEnd := by
      rw [hInjEndEq]
      exact (D.injectionData sts Ms emb).cursor_mono (P + D.base.host.n) (Nat.zero_le Ms.length)
    have hInjEntries (c : ℕ) (hc : c < D.count) :
        finishedInjEntries D.base.route D.base.host D.base.verts D.base.Δ D.base.L
          D.base.childSize D.count D.offset sts c =
        (List.range (Ms.getD c []).length).map fun e =>
          let row := matchingWalkRow Ms emb c
          ((row.u e - D.offset c, row.v e - D.offset c),
            erase D.base.host.edges (row.u e) (row.raw e)) := by
      unfold finishedInjEntries
      rw [hResFst]
      apply takeEntries_eq_matchingRow (hMlen.symm ▸ hc)
      intro a ha e he
      have ha' : a < D.count := hMlen ▸ ha
      have hEnds := (hTrace.injectRow h hMatch hFull ha).2.2 e
        (by rwa [List.getD_eq_getElem _ _ ha])
      refine ⟨fun hIn => ?_, fun hEq => hEq ▸ hEnds.1⟩
      by_contra hne
      exact Finset.disjoint_left.mp (h.children.2.2 a ha' c hc hne) hEnds.1 hIn
    have hRowLe : ∀ j < Ms.length, (Ms.getD j []).length ≤ D.base.childSize := by
      intro j hj
      have h1 := hFull j (by omega)
      have h2 : ((injPairs D.base.childSize D.count D.offset sts)[j]'(by omega)).1.card ≤
          D.base.childSize := by
        have hjc : j < D.count := hMlen ▸ hj
        obtain ⟨hInv, _⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
          h.denominator h.children h.even (coreLevel_le h.coreSize)
        obtain ⟨S, hS⟩ := CertifiedGame.all_saved h.children.1 h.sizeLog hInv j hjc
        have hpair : (injPairs D.base.childSize D.count D.offset sts)[j]'(by omega) =
            (shiftSet (D.offset j) (Finset.range D.base.childSize \ S), shiftSet (D.offset j) S) := by
          rw [← List.getD_eq_getElem]; exact injPairs_getD hjc hS
        rw [hpair, card_shiftSet]
        exact (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
      omega
    have hFlatLe : Ms.flatten.length ≤ D.count * D.base.childSize :=
      (flatten_length_le_mul hRowLe).trans (Nat.mul_le_mul_right _ (by omega))
    have hEmbLen : ∀ j < Ms.flatten.length, (emb j).length ≤ D.base.pathBound := by
      intro j hj
      have h1 := hMatch.2.2.2.2.1 j hj
      have h2 : routePathLen D.base.Δ runEnd D.base.L ≤ routePathLen D.base.Δ bh D.base.L := by
        unfold routePathLen; gcongr
      exact (h1.trans h2).trans h.path
    have hRepLenLe := routeMatched_length_le hEmbLen
    have hCurLe : (D.injectionData sts Ms emb).cursor (P + D.base.host.n) Ms.length ≤
        P + D.base.host.n + Ms.flatten.length * (D.base.pathBound + 1) :=
      applyBatch_cursor_le (D.injectionData sts Ms emb) (P + D.base.host.n) D.base.pathBound hEmbLen
    have hInjEndEq' : injEnd = (D.injectionData sts Ms emb).cursor (P + D.base.host.n) Ms.length :=
      hInjEndEq
    have hTopLeCap : routedEnd ≤ rep + roundRouteCap D := by
      have hPairsCard : ∀ p ∈ injPairs D.base.childSize D.count D.offset sts,
          p.1.card + p.2.card ≤ D.base.childSize := by
        intro p hp
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
        have hSub : savedSet D.base.childSize (sts c) ⊆ Finset.range D.base.childSize := by
          unfold savedSet
          cases hS : (sts c).saved with
          | none => exact Finset.Subset.rfl
          | some S =>
            obtain ⟨hInv, _⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
              h.denominator h.children h.even (coreLevel_le h.coreSize)
            exact ((hInv c (List.mem_range.mp hc)).2.2.2.1 S hS).1
        rw [card_shiftSet, card_shiftSet, Finset.card_sdiff_of_subset hSub, Finset.card_range]
        have hCard := Finset.card_le_card hSub; simp only [Finset.card_range] at hCard; omega
      have hPWLe : (pairsWords (injPairs D.base.childSize D.count D.offset sts)).length ≤
          2 * D.count + 1 + D.count * D.base.childSize := by
        have h1 := pairsWords_length_le_card hPairsCard
        rw [hPairsLen] at h1; exact h1
      have hSup : routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
            (pairsWords (injPairs D.base.childSize D.count D.offset sts)).length
            (D.base.Δ + D.base.L + max 2 D.base.verts.card) ≤
          (Finset.range (2 * D.count + 1 + D.count * D.base.childSize + 1)).sup
            (fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
              pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card)) :=
        Finset.le_sup
          (f := fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
            pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hPWLe))
      exact hTopHi.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (D.base.verts.card + 1) hSup) rep)
    have hSizeBound : injEnd - heap₁ - D.base.host.n ≤
        roundNonHoleCap D.base.childSize D.count D.base.pathBound + roundRouteCap D := by
      have h1 := round_nonhole_arith (k := D.count) (s := D.base.childSize) (d := D.base.pathBound)
        le_rfl le_rfl hFlatLe (hMlen ▸ hRepLenLe)
      rw [hInjEndEq']
      dsimp [P, walkDir, rep, injectReplyBase, buildBatchEnd] at hCurLe hTopLeCap ⊢
      omega
    have hRoutedLeInj : routedEnd ≤ injEnd := by
      dsimp [P, walkDir] at hInjGeP ⊢; omega
    have hHeapLeP : heap₁ ≤ P := by
      dsimp [P, walkDir] at hLoRep hTopLo ⊢; omega
    refine ⟨Ms, emb, routedEnd, hMlen, fun c hc => hRowLe c (hMlen.symm ▸ hc), hLoRep,
      hMemHeapFinal, hTopLo, hRoutedLeInj, hRepFinal, hHeapLeP, hInjGeP, hZeroP,
      fun c hc => ?_, fun c hc e he => ?_, fun c hc => ?_, hSizeBound, hZeroFinal⟩
    · have hcM : c < Ms.length := hMlen.symm ▸ hc
      have hGr : GraphAt mem₃ ((D.injectionData sts Ms emb).addr c)
          (appendGameMatching ((D.injectionData sts Ms emb).graph c)
            ((D.injectionData sts Ms emb).offset c) (Ms.getD c [])) := (hRowAt c hcM).1
      have hAddrEq : (D.injectionData sts Ms emb).addr c = slot + c * D.geometry.slotWords := by
        change D.childAddr ((D.injectionData sts Ms emb).child c) = _
        rw [D.injection_child sts Ms emb hc, hAffine c]
      have hGraphEq : appendGameMatching ((D.injectionData sts Ms emb).graph c)
          ((D.injectionData sts Ms emb).offset c) (Ms.getD c []) =
          ⟨D.base.childSize, (finishedChildFamily D.base.route D.base.host D.base.verts
            D.base.Δ D.base.L D.base.childSize D.count D.offset sts c).map Prod.fst⟩ := by
        have hch : (D.injectionData sts Ms emb).child c = c := D.injection_child sts Ms emb hc
        change appendGameMatching (gameGraph D.base.childSize (sts ((D.injectionData sts Ms emb).child c)))
          (D.offset ((D.injectionData sts Ms emb).child c)) (Ms.getD c []) = _
        rw [hch]
        unfold appendGameMatching finishedChildFamily gameGraph ChildState.M
        rw [List.map_append, hInjEntries c hc, matchingWalkRow_map_ends, witnessEdges_eq_flatten]
      rwa [hAddrEq, hGraphEq] at hGr
    · have hcM : c < Ms.length := hMlen.symm ▸ hc
      obtain ⟨hDirAt, hSeqAt⟩ := (hRowAt c hcM).2 e he
      set r := (D.injectionData sts Ms emb).row c
      set curC := (D.injectionData sts Ms emb).cursor (P + D.base.host.n) c
      have hAddrEq : mem₃ (walkDir + flatIndex Ms c 0 + e) = r.cursor curC e := hDirAt
      rw [hAddrEq]
      have hCurLo : P + D.base.host.n ≤ r.cursor curC e :=
        ((D.injectionData sts Ms emb).cursor_mono (P + D.base.host.n) (Nat.zero_le c)).trans
          (r.cursor_mono curC (Nat.zero_le e))
      have hCurHi : r.cursor curC e + 1 + (r.raw e).length ≤ injEnd := by
        have hstep : r.cursor curC (e + 1) ≤ (D.injectionData sts Ms emb).cursor (P + D.base.host.n) (c + 1) :=
          r.cursor_mono curC (Nat.succ_le_of_lt he)
        have htop : (D.injectionData sts Ms emb).cursor (P + D.base.host.n) (c + 1) ≤ injEnd := by
          rw [hInjEndEq]
          exact (D.injectionData sts Ms emb).cursor_mono (P + D.base.host.n) (Nat.succ_le_of_lt hcM)
        simp only [BuildWalkRow.cursor] at hstep; omega
      have hEraseLe : (erase D.base.host.edges ((matchingWalkRow Ms emb c).u e)
          ((matchingWalkRow Ms emb c).raw e)).length ≤ (r.raw e).length := by
        have hfl := flatIndex_lt_flatten hcM he
        have hmemM : edgeAt (Ms.getD c []) e ∈ Ms.getD c [] := by
          unfold edgeAt; rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he
        have hEnds := (hTrace.injectRow h hMatch hFull hcM).2.2 (edgeAt (Ms.getD c []) e) hmemM
        have hflEq : edgeAt Ms.flatten (flatIndex Ms c 0 + e) = edgeAt (Ms.getD c []) e := by
          unfold edgeAt; rw [flatIndex_zero_add]
          exact (getD_flatten_flatIndex Ms (0, 0) hcM he).2
        have hins : insideB D.base.verts (edgeAt Ms.flatten (flatIndex Ms c 0 + e)) = true := by
          rw [hflEq]
          simp only [insideB, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨(h.children.2.1 c hc).1 hEnds.1, (h.children.2.1 c hc).1 hEnds.2⟩
        have hwk : IsEdgeWalk D.base.host.edges (r.u e) (r.v e) (r.raw e) := by
          have hw := (hMatch.2.2.2.1 (flatIndex Ms c 0 + e) hfl hins).1
          rw [hflEq] at hw
          exact hw
        exact ((erase_spec (r.raw e).length _ _ _ le_rfl hwk).2.1).length_le
      exact ⟨hHeapLeP.trans (Nat.le_trans (Nat.le_add_right _ _) hCurLo), by omega, hSeqAt⟩
    · unfold finishedChildFamily
      rw [List.map_append, hInjEntries c hc]
      simp [List.map_map, Function.comp_def]


end MinCostFlow.HierPaths
