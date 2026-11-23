module

public import MinCostFlow.HierPaths.BuildProgChildTraceBase
import MinCostFlow.HierPaths.BuildProgGameStepMemory
import MinCostFlow.HierPaths.BuildProgChoiceSaved
import MinCostFlow.HierPaths.InitBlockLen
import MinCostFlow.HierPaths.InitLayout

/-!
# Loop-trace archive invariant across `ChoiceLoopTrace`

Proves `ChoiceLoopTrace.roundsMem`: every executed round in the certified choice loop leaves a
valid `RoundArchive` record inside `[D.addrs.heap, heap)`, preserving earlier rounds and matching
the flattened child walk lists.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Every certified loop trace maintains the complete round archive of all executed rounds. -/
theorem ChoiceLoopTrace.roundsMem {w tailBudget : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {t heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem) (ht : t ≤ D.limit)
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hInit : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hDirZero : ∀ r < D.limit, initial (D.directory + r) = 0)
    (hRoom : ∀ t' heap' sts' mem', t' < D.limit →
      ChoiceLoopTrace w D initial t' heap' sts' mem' → (D.round sts').jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap' sts') :
    TraceRoundsMem D t heap sts mem := by
  induction hTrace with
  | start =>
    refine ⟨fun r _ hr => hDirZero r hr, fun _ => D.addrs.heap, fun _ _ => [], fun _ => none,
      rfl, rfl, fun _ hr => (Nat.not_lt_zero _ hr).elim,
      fun _ hr => (Nat.not_lt_zero _ hr).elim, fun _ _ => by simp [ChildState.init]⟩
  | @skip t heap sts mem tr hEmpty ih =>
    obtain ⟨hFut, bounds, walks, holes, hb0, hbt, hbMono, hArch, hWalks⟩ :=
      ih (Nat.le_of_succ_le ht)
    refine ⟨fun r hr1 hr2 => hFut r (by omega) hr2,
      fun r => if r ≤ t then bounds r else heap,
      fun r => if r < t then walks r else fun _ => [],
      fun r => if r < t then holes r else none,
      by simp [hb0], by simp, ?_, ?_, ?_⟩
    · intro r hr
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | rfl
      · simp only [hlt.le, Nat.succ_le_of_lt hlt, ↓reduceIte]
        exact hbMono r hlt
      · simp [hbt]
    · intro r hr
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | rfl
      · simp only [hlt, hlt.le, Nat.succ_le_of_lt hlt, ↓reduceIte]
        exact hArch r hlt
      · simp only [le_rfl, lt_irrefl, Nat.not_succ_le_self, ↓reduceIte, hbt]
        have hdir0 : mem (D.directory + r) = 0 := hFut r le_rfl (Nat.lt_of_succ_le ht)
        simp [RoundArchive, hdir0]
    · intro c hc
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp only [lt_irrefl, ↓reduceIte, List.append_nil]
      rw [hWalks c hc]
      apply List.flatMap_congr
      intro r hr
      have hrt : r < t := List.mem_range.mp hr
      simp [hrt]
  | @run t heap sts mem v after tr hn ans bump rBump hCert hBump hRBump hPost ih =>
    have htLt : t < D.limit := ht
    obtain ⟨hFut, bounds, walks, holes, hb0, hbt, hbMono, hArch, hWalks⟩ :=
      ih (Nat.le_of_succ_le ht)
    have hM := tr.memory (Nat.le_of_succ_le ht) h hL hInit hRoom
    let B := (D.round sts).withReplies ans bump rBump
    let A := D.atHeap heap
    let out := Function.update after (D.directory + t) v
    have hPre := choiceStep_pre_of_memory h hL hM htLt tr (hRoom t heap sts mem htLt tr hn)
      (Nat.pos_of_ne_zero hn)
    have hFit : BuildRoundFit w B A mem := (hPre.2.1.2.2 ans bump hCert hBump).1 rBump hRBump
    have hLay₀ := hPre.2.2.1
    have hLay : GameStepLayout w B A D.first D.saved (D.active sts) :=
      ⟨hLay₀.active, hLay₀.size, hLay₀.childInj, hLay₀.offsets, hLay₀.offsetWord,
        hLay₀.savedBelow, hLay₀.graphsBelow, hLay₀.offsetsBelow, hLay₀.tableBelow⟩
    have hRows (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ)
        (hne : B.indices.isEmpty = false) (he : B.result.1 = .matched Ms emb) :
        Ms.length = B.indices.length :=
      (D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator h.children h.even hne he).1
    have hPostCopy := hPost
    obtain ⟨hvRec, hRecAt, mid, adv, hRound, hAdv, hAF, _⟩ := hPostCopy
    have hRoundMem := oneRoundMemory_of_post hFit hRows hRound
    have hPrepGe : heap ≤ B.prepared A :=
      B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
    have hPrepEnd : B.prepared A + 1 + B.indices.length ≤ v := hRoundMem.preparedEnd
    have hDirSaved : D.directory + D.limit ≤ D.saved := hL.directory
    have hSavedG : D.saved + D.count ≤ A.graphs := hL.saved
    have hGO : A.graphs + D.count ≤ A.offsets := hL.graphs
    have hOR : A.offsets + D.count ≤ A.replies := hL.offsets
    have hRH : A.replies + D.count + 1 ≤ D.addrs.heap := hL.replies
    have hHeapGe : D.addrs.heap ≤ heap := hM.heap
    have hCountLe : B.jobs.count ≤ D.count := D.active_le sts
    have hSlotLen : ∀ i < (D.round sts).jobs.count,
        ((D.round sts).jobs.graph i).encode.length ≤ D.geometry.slotWords := by
      intro i hi
      obtain ⟨hInv, _⟩ := tr.certified.invariant h.router h.host h.positive h.expansion
        h.denominator h.children h.even (coreLevel_le h.coreSize)
      have hEnc := (gameGraph_bounds_of_inv (hInv (D.active sts i) (D.active_mem hi).1)).2.2.1
      exact hEnc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : t ≤ D.limit + 1)) _)
    have hPBound : B.prepared A ≤ heap + roundCoreCap D :=
      prepPrefix_le_validBump hBump hSlotLen heap
    have hIdxLe : B.indices.length ≤ B.jobs.count := by
      simpa [BuildRoundData.indices, batchJobIndices, cutReplyIndices] using
        List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
          (List.range B.jobs.count)
    have hLimPos : 1 ≤ D.limit := by unfold ChoiceLoopData.limit; omega
    have hvPos : 0 < v := by omega
    -- Preservation of directory entries r ≠ t and arena [D.addrs.heap, heap)
    have hDirPres (r : ℕ) (hr : r < D.limit) (hne : r ≠ t) :
        out (D.directory + r) = mem (D.directory + r) := by
      have hneAddr : D.directory + r ≠ D.directory + t := by omega
      dsimp only [out]; rw [Function.update_of_ne hneAddr]
      have hSafe : B.unchangedBelow (D.directory + r) := by
        by_cases hem : B.indices.isEmpty = true
        · exact Or.inl hem
        · refine Or.inr fun Ms emb hm i hi => Or.inl ?_
          have hIdx := (mem_batchJobIndices.mp (rowIndex_mem (emb := emb) hi
            (hRows Ms emb (Bool.eq_false_iff.mpr hem) hm))).1
          have hs := (hL.slots _ (D.active_mem hIdx).1).1
          change A.offsets + D.count ≤ D.childAddr (D.active sts ((B.applyData Ms emb).child i)) at hs
          change D.directory + r < D.childAddr (D.active sts ((B.applyData Ms emb).child i))
          omega
      exact gameStep_prefix_frame hFit hLay hRows hPost
        (Or.inl ⟨by omega, hSafe⟩) (Or.inl (by omega)) (Or.inl (by omega))
        (fun i _ _ => by omega)
    have hArenaPres (a : ℕ) (ha1 : D.addrs.heap ≤ a) (ha2 : a < heap) : out a = mem a := by
      dsimp only [out]; rw [Function.update_of_ne (by omega)]
      exact gameStep_prefix_frame hFit hLay hRows hPost
        (Or.inr ⟨by omega, ha2⟩) (Or.inr (by omega)) (Or.inr (by omega))
        (fun i hi _ => by have := hLay.savedBelow i hi; omega)
    -- Preservation of [heap, v) from mid to out
    have hMidToOut (a : ℕ) (ha1 : heap ≤ a) (ha2 : a < v) : out a = mid a := by
      obtain ⟨_, _, _, he, _, _, _, _, _, hKeep⟩ := hAdv
      simp only [List.cons.injEq, and_true, true_and] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      dsimp only [out]; rw [Function.update_of_ne (by omega), hAF a (by omega) (by omega)]
      refine hKeep a (Or.inr ?_) (Or.inr ?_) (Or.inl (by omega))
        (fun i hi _ => by have := hLay.savedBelow i hi; omega)
      · change A.graphs + B.indices.length ≤ a; omega
      · change A.offsets + B.indices.length ≤ a; omega
    -- Bounds monotonicity for old rounds
    have hBoundsGe (r : ℕ) (hr : r ≤ t) : D.addrs.heap ≤ bounds r := by
      induction r with
      | zero => rw [hb0]
      | succ r' ih' => exact (ih' (Nat.le_of_succ_le hr)).trans (hbMono r' hr)
    have hBoundsLe (r : ℕ) (hr : r ≤ t) : bounds r ≤ heap := by
      have hgen : ∀ d, r + d ≤ t → bounds r ≤ bounds (r + d) := by
        intro d
        induction d with
        | zero => intro _; simp
        | succ d' ihd =>
          intro hle
          exact (ihd (by omega)).trans (hbMono (r + d') (by omega))
      have h1 := hgen (t - r) (by omega)
      rw [Nat.add_sub_of_le hr, hbt] at h1
      exact h1
    -- Construct the round-t walks and hole
    have hRoundData : ∃ (wt : ℕ → List (List ℕ)) (ht_hole : Option ℕ),
        RoundArchive D.base.host D.first D.base.childSize D.count D.base.pathBound
          (roundCoreCap D + roundRouteCap D) out heap (v + 2 + B.jobs.count) v wt ht_hole ∧
        ∀ c < D.count, (D.next sts ans c).rounds.flatten.map Prod.snd =
          (sts c).rounds.flatten.map Prod.snd ++ wt c := by
      have hOutV : out v = B.prepared A := by
        dsimp only [out]; rw [Function.update_of_ne (by omega)]
        simpa using hRecAt 0 (by simp)
      have hOutV1 : out (v + 1) = B.jobs.count := by
        dsimp only [out]; rw [Function.update_of_ne (by omega)]
        simpa using hRecAt 1 (by simp)
      have hOutOff (i : ℕ) (hi : i < B.jobs.count) :
          out (v + 2 + i) = D.first + D.active sts i * D.base.childSize := by
        obtain ⟨_, _, _, he, _, _, _, hSnap, _, _⟩ := hAdv
        simp only [List.cons.injEq, and_true, true_and] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        dsimp only [out]; rw [Function.update_of_ne (by omega), hAF _ (by omega) (by omega)]
        have hi' : i < (tabList B.jobs.count B.jobs.offset).length := by simpa using hi
        have hS := hSnap i hi'
        simp only [tabList, List.getElem_map, List.getElem_range] at hS
        exact hS
      have hOutPrep : out (B.prepared A) = B.indices.length :=
        (hMidToOut _ hPrepGe (by omega)).trans hRoundMem.count
      have hOutCut (j : ℕ) (hj : j < B.indices.length) :
          out (B.prepared A + 1 + j) = B.indices.getD j 0 := by
        rw [hMidToOut _ (by omega) (by omega), List.getD_eq_getElem _ _ hj]
        exact hRoundMem.indices j hj
      have hCutLt (j : ℕ) (hj : j < B.indices.length) : B.indices.getD j 0 < B.jobs.count := by
        rw [List.getD_eq_getElem _ _ hj]
        exact (mem_batchJobIndices.mp (List.getElem_mem hj)).1
      have hCutInj : ∀ j₁ < B.indices.length, ∀ j₂ < B.indices.length,
          B.indices.getD j₁ 0 = B.indices.getD j₂ 0 → j₁ = j₂ := by
        have hnd : B.indices.Nodup := List.nodup_range.filter _
        intro j₁ hj₁ j₂ hj₂ heq
        rw [List.getD_eq_getElem _ _ hj₁, List.getD_eq_getElem _ _ hj₂] at heq
        exact (hnd.getElem_inj_iff).mp heq
      by_cases hNum : B.indices.length = 0
      · refine ⟨fun _ => [], none, ?_, ?_⟩
        · unfold RoundArchive
          rw [ite_eq_right (Nat.ne_of_gt hvPos)]
          refine ⟨B.prepared A, B.jobs.count, D.active sts, B.indices.length,
            fun j => B.indices.getD j 0, hPrepGe, by omega, rfl, Nat.pos_of_ne_zero hn,
            hCountLe, hOutV, hOutV1, fun i hi => ⟨(D.active_mem hi).1, hOutOff i hi⟩,
            fun i hi j hj => D.active_inj sts hi hj, hOutPrep, hIdxLe,
            fun j hj => ⟨hCutLt j hj, hOutCut j hj⟩, hCutInj, ?_⟩
          rw [ite_eq_left hNum]
          refine ⟨fun _ => rfl, rfl, ?_⟩
          have hempty : B.indices.isEmpty = true := List.isEmpty_iff_length_eq_zero.mpr hNum
          have hvEq : v = B.prepared A + 1 + B.jobs.count := by
            change v = B.record A at hvRec
            rw [hvRec]; unfold BuildRoundData.record; simp [hempty]
          unfold roundNonHoleCap
          omega
        · intro c hc
          rw [List.append_nil]
          have hno : c ∉ choiceRequesting D.base.childSize D.count D.offset sts
              (answerByChild D.count sts ans) := by
            rw [← D.selected_eq sts ans]
            have hnil : ((D.round sts).withReplies ans).indices = [] :=
              List.eq_nil_of_length_eq_zero hNum
            simp [hnil]
          unfold ChoiceLoopData.next choiceGameRound
          simp only [hc, ↓reduceIte]
          cases hS : (sts c).saved with
          | some _ => simp [childStepAnswer, hS]
          | none =>
            cases hA : answerByChild D.count sts ans c with
            | expander _ => simp [childStepAnswer, hS]
            | cut U => exact (hno (mem_choiceRequesting.mpr ⟨hc, hS, U, hA⟩)).elim
      · have hne : B.indices.isEmpty = false :=
          Bool.eq_false_iff.mpr fun he => hNum (List.isEmpty_iff_length_eq_zero.mp he)
        obtain ⟨Ms, emb, hRes, hMatch, hFull, hLastB⟩ := h.matched hCert hne
        obtain ⟨hMlen, hChildRows⟩ := D.matchedRows hCert h.router h.host h.positive h.expansion
          h.denominator h.children h.even hne hRes
        -- Extract round postcondition facts on `mid`
        obtain ⟨A', m₁, m₂, midR, heA, _, hRpost, hFpost⟩ := hRound
        have hAeq : A' = A := by
          cases A'
          simp only [BuildRoundData.args, List.cons.injEq, and_true, true_and] at heA
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heA; rfl
        subst hAeq
        obtain ⟨_, _, _, _, hre, hRAt, _, _, _⟩ := hRpost
        simp only [BuildRoundData.routeArgs, List.cons.injEq, and_true, true_and] at hre
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hre
        have hRAt' : (if B.indices.isEmpty then midR = B.prepared A + 1 + B.jobs.count else
            m₂ (B.prepared A + 1 + B.jobs.count) = midR ∧
            ListAt m₂ (buildBatchEnd (B.prepared A + 1 + B.jobs.count) B.indices.length D.base.childSize)
              (routeResultWords B.result.1) ∧
            buildBatchEnd (B.prepared A + 1 + B.jobs.count) B.indices.length D.base.childSize +
              (routeResultWords B.result.1).length ≤ midR) := hRAt.2.2
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hRAt'
        obtain ⟨hBatchM₂, hRepAt₂, hRepEndLeMidR⟩ := hRAt'
        change B.result.1 = .matched Ms emb at hRes
        rw [hRes] at hRepAt₂ hRepEndLeMidR
        have hneList : ((D.round sts).withReplies ans bump rBump).indices ≠ [] :=
          fun h => hNum (by simpa [B] using congrArg List.length h)
        have hFpost' : midR = B.routedEnd A ∧ ∃ Ms' emb', B.result.1 = .matched Ms' emb' ∧
            (buildFinishBatchContract w (B.applyData Ms' emb')).post
              (B.finishArgs A) m₂ v mid := by
          simpa [roundFinishPost, hneList, B, A] using hFpost
        obtain ⟨hMidREq, Ms', emb', hRes', hFinPost⟩ := hFpost'
        subst hMidREq
        rw [hRes] at hRes'; cases hRes'
        obtain ⟨rep', idx', graphs', offs', ends', cap', heap', hfeq, hAppPost⟩ := hFinPost
        simp only [BuildRoundData.finishArgs, List.cons.injEq, and_true] at hfeq
        obtain ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, _⟩ := hfeq
        obtain ⟨mt', tb', idx'', graphs'', offs'', tmp', ends'', vs', P', dir', out', haeq,
          hvCur, _, hZeroP, hKept, hRowAt⟩ := hAppPost
        simp only [finishBatchApplyArgs, List.cons.injEq, and_true, true_and] at haeq
        obtain ⟨rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := haeq
        let batch := B.prepared A + 1 + B.jobs.count
        let rep := buildBatchEnd batch B.indices.length D.base.childSize
        let routedEnd := B.routedEnd A
        let walkDir := routedEnd + 4
        let P := walkDir + Ms.flatten.length + D.base.pathBound + 1
        have hLoRep : heap ≤ rep := by dsimp [rep, batch, buildBatchEnd]; omega
        have hRoutedEq : B.routedEnd A = routedEnd := rfl
        have hRoutedDef : routedEnd = rep + (routeResultWords (.matched Ms emb)).length + rBump := by
          unfold routedEnd BuildRoundData.routedEnd BuildRoundData.routeReply
          rw [hRes]; rfl
        have hPeq : B.routedEnd A + 4 + (B.applyData Ms emb).matchings.flatten.length +
            B.pathBound + 1 = P := rfl
        have hOutGeP : P + D.base.host.n ≤ v := by
          rw [hvCur, hPeq]
          exact (B.applyData Ms emb).cursor_mono (P + D.base.host.n) (Nat.zero_le Ms.length)
        have hCapLeAll : ∀ j (hj : j < Ms.length),
            (B.applyData Ms emb).cap j ≤ D.addrs.replies := by
          intro j hj
          have hIdx := (mem_batchJobIndices.mp (rowIndex_mem (emb := emb) hj hMlen)).1
          have hc := (D.active_mem hIdx).1
          have hSlot : D.childAddr (D.active sts ((B.applyData Ms emb).child j)) +
              D.geometry.slotWords ≤ D.addrs.replies := (hL.slots _ hc).2
          have hCapLe : (B.applyData Ms emb).cap j ≤
              D.childAddr (D.active sts ((B.applyData Ms emb).child j)) +
              D.geometry.slotWords := by
            rw [applyBatch_cap_eq]
            have hGr : appendGameMatching ((B.applyData Ms emb).graph j)
                ((B.applyData Ms emb).offset j) (Ms.getD j []) =
                gameGraph D.base.childSize (D.next sts ans (D.active sts ((B.applyData Ms emb).child j))) :=
              D.graph_of_row (wk := fun e => erase B.host.edges ((matchingWalkRow Ms emb j).u e)
                ((matchingWalkRow Ms emb j).raw e)) (hChildRows j hj).2.2
            change _ ≤ D.childAddr (D.active sts ((B.applyData Ms emb).child j)) + _
            rw [show (B.applyData Ms emb).addr j = D.childAddr (D.active sts ((B.applyData Ms emb).child j)) from rfl]
            apply Nat.add_le_add_left
            rw [hGr]
            have hTrNext : ChoiceLoopTrace w D initial (t + 1) (v + 2 + B.jobs.count) (D.next sts ans) out :=
              ChoiceLoopTrace.run tr hn ans bump rBump hCert hBump hRBump hPost
            obtain ⟨hInv', _⟩ := hTrNext.certified.invariant h.router h.host h.positive h.expansion
              h.denominator h.children h.even (coreLevel_le h.coreSize)
            have hLen := (gameGraph_bounds_of_inv (hInv' _ (hChildRows j hj).1)).2.2.1
            have hLim : t + 1 ≤ D.limit + 1 := by omega
            exact hLen.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLim) _)
          exact hCapLe.trans hSlot
        have hRepLeHeap : D.addrs.replies ≤ D.addrs.heap := by
          change D.addrs.replies + D.count + 1 ≤ D.addrs.heap at hRH; omega
        have hRepMid : ListAt mid rep (routeResultWords (.matched Ms emb)) := by
          refine WordRAM.ListAt.congr hRepAt₂ fun a ha hb => hKept a ⟨?_, fun j hj => ?_⟩
          · rw [hRoutedEq, hRoutedDef]; omega
          · exact Or.inr ((hCapLeAll j hj).trans (hRepLeHeap.trans (hHeapGe.trans (hLoRep.trans ha))))
        have hBatchMid : mid batch = routedEnd := by
          have hBatchLt : batch < routedEnd := by
            dsimp [batch, rep, buildBatchEnd] at hRoutedDef ⊢; omega
          have hBatchKept : mid batch = m₂ batch :=
            hKept batch ⟨hBatchLt, fun j hj => Or.inr ((hCapLeAll j hj).trans
              (hRepLeHeap.trans (hHeapGe.trans (by dsimp [batch]; omega))))⟩
          exact hBatchKept.trans hBatchM₂
        let rowWalks : ℕ → List (List ℕ) := fun j =>
          (List.range (Ms.getD j []).length).map fun e =>
            let row := matchingWalkRow Ms emb j
            erase D.base.host.edges (row.u e) (row.raw e)
        let wt : ℕ → List (List ℕ) := fun c =>
          match (List.range B.indices.length).find? (fun j => decide (D.active sts (B.indices.getD j 0) = c)) with
          | some j => rowWalks j
          | none => []
        have hActCutInj : ∀ j₁ < B.indices.length, ∀ j₂ < B.indices.length,
            D.active sts (B.indices.getD j₁ 0) = D.active sts (B.indices.getD j₂ 0) → j₁ = j₂ := by
          intro j₁ hj₁ j₂ hj₂ heq
          exact hCutInj j₁ hj₁ j₂ hj₂ (D.active_inj sts (hCutLt j₁ hj₁) (hCutLt j₂ hj₂) heq)
        have hWtAt : ∀ j < B.indices.length, wt (D.active sts (B.indices.getD j 0)) = rowWalks j := by
          intro j hj
          dsimp [wt]
          cases hfind : (List.range B.indices.length).find?
              (fun j' => decide (D.active sts (B.indices.getD j' 0) = D.active sts (B.indices.getD j 0))) with
          | none =>
            have := List.find?_eq_none.mp hfind j (List.mem_range.mpr hj)
            simp at this
          | some j' =>
            have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
            have hpred : D.active sts (B.indices.getD j' 0) = D.active sts (B.indices.getD j 0) :=
              of_decide_eq_true (by simpa using List.find?_some hfind)
            rw [hActCutInj j' hmem j hj hpred]
        have hWtOther : ∀ c < D.count, (∀ j < B.indices.length, D.active sts (B.indices.getD j 0) ≠ c) →
            wt c = [] := by
          intro c _ hneC
          dsimp [wt]
          cases hfind : (List.range B.indices.length).find?
              (fun j' => decide (D.active sts (B.indices.getD j' 0) = c)) with
          | none => rfl
          | some j' =>
            have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
            have hpred : D.active sts (B.indices.getD j' 0) = c :=
              of_decide_eq_true (by simpa using List.find?_some hfind)
            exact (hneC j' hmem hpred).elim
        -- Size bound
        have hRowLe : ∀ j < Ms.length, (Ms.getD j []).length ≤ D.base.childSize := by
          intro j hj
          have hjP : j < B.pairs.length := by
            unfold BuildRoundData.pairs; rw [length_batchJobPairs]; exact hMlen ▸ hj
          have h1 : (Ms.getD j []).length = (B.pairs[j]'hjP).1.card := hFull j hjP
          have h2 : (B.pairs[j]'hjP).1.card ≤ D.base.childSize := by
            have hEqP : B.pairs = choiceRoundPairs D.base.childSize D.count D.offset sts
                (answerByChild D.count sts ans) := D.pairs_eq sts ans
            have hmemP : B.pairs[j]'hjP ∈ choiceRoundPairs D.base.childSize D.count D.offset sts
                (answerByChild D.count sts ans) := hEqP ▸ List.getElem_mem hjP
            obtain ⟨c, hc, hce⟩ := List.mem_map.mp hmemP
            rw [← hce]
            obtain ⟨_, ha, U, hU⟩ := mem_choiceRequesting.mp hc
            simp only [choiceRequest, ha, hU, Option.getD_some, card_shiftSet]
            have hUsub : U ⊆ Finset.range D.base.childSize := by
              have := D.certify_children hCert c (mem_choiceRequesting.mp hc).1 ha
              rw [hU] at this; exact this.1
            exact (Finset.card_le_card (bisectOf_spec hUsub).1).trans (by simp)
          exact h1.le.trans h2
        have hML : Ms.length ≤ D.count := hMlen.le.trans (hIdxLe.trans hCountLe)
        have hFlatLe : Ms.flatten.length ≤ D.count * D.base.childSize :=
          (flatten_length_le_mul hRowLe).trans (Nat.mul_le_mul_right _ hML)
        have hEmbLen : ∀ j < Ms.flatten.length, (emb j).length ≤ D.base.pathBound := by
          intro j hj
          have h1 := hMatch.2.2.2.2.1 j hj
          have h2 : routePathLen D.base.Δ B.result.2 D.base.L ≤ routePathLen D.base.Δ bh D.base.L := by
            unfold routePathLen; gcongr; exact hLastB
          exact (h1.trans h2).trans h.path
        have hRepLenLe := routeMatched_length_le hEmbLen
        have hCurLe : (B.applyData Ms emb).cursor (P + D.base.host.n) Ms.length ≤
            P + D.base.host.n + Ms.flatten.length * (D.base.pathBound + 1) :=
          applyBatch_cursor_le (B.applyData Ms emb) (P + D.base.host.n) D.base.pathBound hEmbLen
        have hvCur' : v = (B.applyData Ms emb).cursor (P + D.base.host.n) Ms.length := by
          rw [hvCur, hPeq]; rfl
        have hRBumpLeCap : rBump ≤ roundRouteCap D := by
          have hPairCard : ∀ p ∈ B.pairs, p.1.card + p.2.card ≤ D.base.childSize := by
            intro p hp
            have hEqP : B.pairs = choiceRoundPairs D.base.childSize D.count D.offset sts
                (answerByChild D.count sts ans) := D.pairs_eq sts ans
            rw [hEqP] at hp
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
            obtain ⟨_, ha, U, hU⟩ := mem_choiceRequesting.mp hc
            simp only [choiceRequest, ha, hU, Option.getD_some, card_shiftSet]
            have hUsub : U ⊆ Finset.range D.base.childSize := by
              have := D.certify_children hCert c (mem_choiceRequesting.mp hc).1 ha
              rw [hU] at this; exact this.1
            have hBsub := (bisectOf_spec hUsub).1
            rw [Finset.card_sdiff_of_subset hBsub, Finset.card_range]
            have := Finset.card_le_card hBsub; simp only [Finset.card_range] at this; omega
          have hPWLe : (pairsWords B.pairs).length ≤ 2 * D.count + 1 + D.count * D.base.childSize := by
            have h1 := pairsWords_length_le_card hPairCard
            have hPL : B.pairs.length ≤ D.count := by
              rw [show B.pairs.length = B.indices.length from length_batchJobPairs ..]; omega
            have hMul := Nat.mul_le_mul_right D.base.childSize hPL
            omega
          have hSup : routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
                (pairsWords B.pairs).length (D.base.Δ + D.base.L + max 2 D.base.verts.card) ≤
              (Finset.range (2 * D.count + 1 + D.count * D.base.childSize + 1)).sup
                (fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
                  pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card)) :=
            Finset.le_sup
              (f := fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
                pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card))
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hPWLe))
          exact hRBump.trans (Nat.mul_le_mul_left (D.base.verts.card + 1) hSup)
        have hSizeBound : v + 2 + B.jobs.count - heap - D.base.host.n ≤
            roundNonHoleCap D.base.childSize D.count D.base.pathBound +
              (roundCoreCap D + roundRouteCap D) := by
          have h1 := round_nonhole_bump_arith (coreCap := roundCoreCap D) hCountLe hIdxLe hFlatLe
            (hMlen ▸ hRepLenLe)
          rw [hvCur']
          dsimp [P, walkDir, rep, batch, buildBatchEnd] at hCurLe hRoutedDef ⊢
          omega
        have hRoutedLeV : routedEnd ≤ v := by
          dsimp [P, walkDir] at hOutGeP ⊢; omega
        have hHeapLeP : heap ≤ P := by
          dsimp [P, walkDir] at hLoRep hRoutedDef ⊢; omega
        have hOutBatch : out batch = routedEnd :=
          (hMidToOut batch (by dsimp [batch]; omega) (by dsimp [batch, rep, buildBatchEnd] at hRoutedDef hRoutedLeV ⊢; omega)).trans hBatchMid
        refine ⟨wt, some P, ?_, ?_⟩
        · unfold RoundArchive
          rw [ite_eq_right (Nat.ne_of_gt hvPos)]
          refine ⟨B.prepared A, B.jobs.count, D.active sts, B.indices.length,
            fun j => B.indices.getD j 0, hPrepGe, by omega, rfl, Nat.pos_of_ne_zero hn,
            hCountLe, hOutV, hOutV1, fun i hi => ⟨(D.active_mem hi).1, hOutOff i hi⟩,
            fun i hi j hj => D.active_inj sts hi hj, hOutPrep, hIdxLe,
            fun j hj => ⟨hCutLt j hj, hOutCut j hj⟩, hCutInj, ?_⟩
          rw [ite_eq_right hNum]
          refine ⟨Ms, emb, routedEnd, hMlen, fun j hj => hRowLe j (hMlen.symm ▸ hj), hLoRep,
            hOutBatch, by rw [hRoutedDef]; omega, hRoutedLeV,
            WordRAM.ListAt.congr hRepMid (fun a ha hb => hMidToOut a (hLoRep.trans ha) (by
              rw [hRoutedDef] at hRoutedLeV; omega)),
            rfl, hHeapLeP, hOutGeP,
            fun a ha => (hMidToOut _ (hHeapLeP.trans (Nat.le_add_right _ _)) (by omega)).trans
              (by simpa only [hPeq] using hZeroP a ha),
            fun j hj e he => ?_, hWtAt, hWtOther, hSizeBound⟩
          have hjM : j < Ms.length := hMlen.symm ▸ hj
          obtain ⟨_, hRowWalk⟩ := hRowAt j hjM
          obtain ⟨hDirAt, hSeqAt⟩ := hRowWalk e he
          have hDirAddr : walkDir + flatIndex Ms j 0 + e < v := by
            have hfl := flatIndex_lt_flatten hjM he
            dsimp [P, walkDir] at hOutGeP ⊢; omega
          have hDirGe : heap ≤ walkDir + flatIndex Ms j 0 + e := by
            dsimp [walkDir] at hLoRep hRoutedDef ⊢; omega
          have hAddrEq : out (walkDir + flatIndex Ms j 0 + e) =
              ((B.applyData Ms emb).row j).cursor ((B.applyData Ms emb).cursor (P + D.base.host.n) j) e := by
            rw [hMidToOut _ hDirGe hDirAddr]
            change mid (B.routedEnd A + 4 + flatIndex Ms j 0 + e) =
              ((B.applyData Ms emb).row j).cursor
                ((B.applyData Ms emb).cursor (B.routedEnd A + 4 +
                  (B.applyData Ms emb).matchings.flatten.length + B.pathBound + 1 + D.base.host.n) j) e at hDirAt
            rw [hRoutedEq] at hDirAt
            exact hDirAt
          rw [hAddrEq]
          set r := (B.applyData Ms emb).row j
          set curJ := (B.applyData Ms emb).cursor (P + D.base.host.n) j
          have hCurLo : P + D.base.host.n ≤ r.cursor curJ e :=
            ((B.applyData Ms emb).cursor_mono (P + D.base.host.n) (Nat.zero_le j)).trans
              (r.cursor_mono curJ (Nat.zero_le e))
          have hCurHi : r.cursor curJ e + 1 + (r.raw e).length ≤ v := by
            have hstep : r.cursor curJ (e + 1) ≤ (B.applyData Ms emb).cursor (P + D.base.host.n) (j + 1) :=
              r.cursor_mono curJ (Nat.succ_le_of_lt he)
            have htop : (B.applyData Ms emb).cursor (P + D.base.host.n) (j + 1) ≤ v := by
              rw [hvCur']
              exact (B.applyData Ms emb).cursor_mono (P + D.base.host.n) (Nat.succ_le_of_lt hjM)
            simp only [BuildWalkRow.cursor] at hstep
            omega
          have hEraseLe : (erase D.base.host.edges ((matchingWalkRow Ms emb j).u e)
              ((matchingWalkRow Ms emb j).raw e)).length ≤ (r.raw e).length := by
            have hfl := flatIndex_lt_flatten hjM he
            have hmemM : edgeAt (Ms.getD j []) e ∈ Ms[j]'hjM := by
              rw [← List.getD_eq_getElem _ [] hjM]
              unfold edgeAt; rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he
            have hEnds := (hChildRows j hjM).2.1 (edgeAt (Ms.getD j []) e) hmemM
            have hflEq : edgeAt Ms.flatten (flatIndex Ms j 0 + e) = edgeAt (Ms.getD j []) e := by
              unfold edgeAt; rw [flatIndex_zero_add]
              exact (getD_flatten_flatIndex Ms (0, 0) hjM he).2
            have hins : insideB D.base.verts (edgeAt Ms.flatten (flatIndex Ms j 0 + e)) = true := by
              rw [hflEq]
              simp only [insideB, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨(h.children.2.1 _ (hChildRows j hjM).1).1 hEnds.1,
                (h.children.2.1 _ (hChildRows j hjM).1).1 hEnds.2⟩
            have hwk : IsEdgeWalk D.base.host.edges (r.u e) (r.v e) (r.raw e) := by
              have hw := (hMatch.2.2.2.1 (flatIndex Ms j 0 + e) hfl hins).1
              rw [hflEq] at hw
              exact hw
            exact ((erase_spec (r.raw e).length _ _ _ le_rfl hwk).2.1).length_le
          refine ⟨hHeapLeP.trans (Nat.le_trans (Nat.le_add_right _ _) hCurLo), by omega, ?_⟩
          have hSeqMid : SeqAt mid (r.cursor curJ e) (erase D.base.host.edges (r.u e) (r.raw e)) := by
            change SeqAt mid (r.cursor ((B.applyData Ms emb).cursor (B.routedEnd A + 4 +
              (B.applyData Ms emb).matchings.flatten.length + B.pathBound + 1 + D.base.host.n) j) e)
              (erase D.base.host.edges (r.u e) (r.raw e)) at hSeqAt
            rw [hRoutedEq] at hSeqAt
            exact hSeqAt
          exact seqAt_frame hSeqMid fun a ha hb =>
            hMidToOut a (hHeapLeP.trans (Nat.le_trans (Nat.le_add_right _ _) (hCurLo.trans ha))) (by omega)
        · intro c hc
          by_cases hIn : ∃ j < B.indices.length, D.active sts (B.indices.getD j 0) = c
          · obtain ⟨j, hj, rfl⟩ := hIn
            have hjM : j < Ms.length := hMlen.symm ▸ hj
            have hRow := (hChildRows j hjM).2.2
            change (D.next sts ans (D.active sts (B.indices.getD j 0))).rounds = _ at hRow
            rw [hRow, List.flatten_append, List.flatten_singleton, List.map_append, hWtAt j hj]
            simp [rowWalks, List.map_map, Function.comp_def]; rfl
          · push Not at hIn
            rw [hWtOther c hc hIn, List.append_nil]
            have hno : c ∉ choiceRequesting D.base.childSize D.count D.offset sts
                (answerByChild D.count sts ans) := by
              rw [← D.selected_eq sts ans]
              intro hm
              obtain ⟨idx, hidx, heq⟩ := List.mem_map.mp hm
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hidx
              exact hIn j hj (by rw [show B.indices = ((D.round sts).withReplies ans).indices from rfl,
                List.getD_eq_getElem _ _ hj]; exact heq)
            unfold ChoiceLoopData.next choiceGameRound
            simp only [hc, ↓reduceIte]
            cases hS : (sts c).saved with
            | some _ => simp [childStepAnswer, hS]
            | none =>
              cases hA : answerByChild D.count sts ans c with
              | expander _ => simp [childStepAnswer, hS]
              | cut U => exact (hno (mem_choiceRequesting.mpr ⟨hc, hS, U, hA⟩)).elim
    obtain ⟨wt, ht_hole, hArchT, hWalksT⟩ := hRoundData
    refine ⟨fun r hr1 hr2 => (hDirPres r hr2 (by omega)).trans (hFut r (by omega) hr2),
      fun r => if r ≤ t then bounds r else v + 2 + B.jobs.count,
      fun r => if r < t then walks r else wt,
      fun r => if r < t then holes r else ht_hole,
      by simp [hb0], by simp [B]; rfl, ?_, ?_, ?_⟩
    · intro r hr
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | heq
      · simp only [hlt.le, Nat.succ_le_of_lt hlt, ↓reduceIte]
        exact hbMono r hlt
      · subst heq
        simp only [le_rfl, Nat.not_succ_le_self, ↓reduceIte, hbt]
        omega
    · intro r hr
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | heq
      · simp only [hlt, hlt.le, Nat.succ_le_of_lt hlt, ↓reduceIte]
        change RoundArchive D.base.host D.first D.base.childSize D.count D.base.pathBound
          (roundCoreCap D + roundRouteCap D) out (bounds r) (bounds (r + 1)) (out (D.directory + r)) (walks r) (holes r)
        rw [hDirPres r (by omega) (by omega)]
        exact (hArch r hlt).frame fun a ha1 ha2 =>
          hArenaPres a ((hBoundsGe r hlt.le).trans ha1) (ha2.trans_le (hBoundsLe (r + 1) hlt))
      · subst heq
        simp only [le_rfl, lt_irrefl, Nat.not_succ_le_self, ↓reduceIte, hbt]
        change RoundArchive D.base.host D.first D.base.childSize D.count D.base.pathBound
          (roundCoreCap D + roundRouteCap D) out heap (v + 2 + B.jobs.count) (out (D.directory + r)) wt ht_hole
        have hdirT : out (D.directory + r) = v := by simp [out]
        rw [hdirT]
        exact hArchT
    · intro c hc
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp only [lt_irrefl, ↓reduceIte]
      rw [hWalksT c hc, hWalks c hc]
      congr 1
      apply List.flatMap_congr
      intro r hr
      have hrt : r < t := List.mem_range.mp hr
      simp [hrt]

end MinCostFlow.HierPaths
