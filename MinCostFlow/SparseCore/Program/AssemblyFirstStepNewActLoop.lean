module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActLoopDefs

import WordRAM.Tactic

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

set_option maxHeartbeats 800000 in
/-- **Verification of the component-activation loop** `forRange 7 (.const 0) (.reg 3)` inside
`asmFirstNewActStmt`, invoking `asmFirstInitOneComp_runs` on each `(c, v)` pair in `newComps`. -/
theorem asmFirstNewAct_loop_runs {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w depth L capExp limbMul bBun fVertRoot fTourList fTourLen fTourOwner fInitOne : ℕ}
    {impl : SparsifyImpl} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun fTourList fTourLen fTourOwner))
    (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (hTB : AsmBrTourBridge TS TR w p fTourList fTourLen fTourOwner)
    (hfOne : p.procs[fInitOne]? = some (asmFirstInitOneCompStmt fVertRoot fTourList
      (bBun + bundleOffSort) (bBun + bundleIdxInitSlots)))
    {restH tourH newCompsPtr h : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {mk : Finset End}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {tx₀ : (TR y.vCap5 y.eCap5).τ} {newComps : List (ℕ × ℕ)} {mem_orig mem₀ : ℕ → ℕ} {st₀ : State}
    (hSide : AsmBrSideAt (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w depth L capExp limbMul Ψ restH ⟨tr, ord, y.vCap5, y.eCap5⟩ y mem_orig)
    (hAgree : ∀ a, asmSdFoot restH y a →
      (∀ c < y.comps.length, a ≠ y.ctH + 3 * c) →
      (∀ v < y.vCap5, a ≠ y.cmpH + v) → mem₀ a = mem_orig a)
    (hrepT : (TR y.vCap5 y.eCap5).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx₀ mem₀)
    (hvCapG : ∀ u ∈ tr.cs.G.V, u < y.vCap5) (heCapG : ∀ e ∈ tr.cs.G.E, e < y.eCap5)
    (hw16 : 16 ≤ 2 ^ w) (hvCapW : y.vCap5 < 2 ^ w) (heCapW : 4 * y.eCap5 < 2 ^ w)
    (htourW : tourH < 2 ^ w)
    (hfootSide : ∀ a, asmSdFoot restH y a → a < h)
    (hfootT : ∀ a, (TR y.vCap5 y.eCap5).foot tourH tx₀ a → a < h)
    (hdisjST : ∀ a, asmSdFoot restH y a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a)
    (hNC_at : ∀ i (hi : i < newComps.length),
      mem₀ (newCompsPtr + 2 * i) = (newComps[i]'hi).1 ∧
      mem₀ (newCompsPtr + 2 * i + 1) = (newComps[i]'hi).2)
    (hNC_lt : newCompsPtr + 2 * newComps.length ≤ h)
    (hNC_disj : ∀ a, newCompsPtr ≤ a → a < newCompsPtr + 2 * newComps.length →
      ¬ asmSdFoot restH y a ∧ ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a)
    (hNC_nd : (newComps.map Prod.fst).Nodup)
    (hNC_ok : ∀ q ∈ newComps, ∃ hc : q.1 < y.comps.length,
      y.comps[q.1]'hc ∉ tr.activeComps ∧ q.2 ∈ (tr.cs.compSt (y.comps[q.1]'hc)).G.V)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + 2 * newComps.length + newActLoopSpace TS hRoot.querySpace tr ord y.comps newComps < 2 ^ w)
    (hst0_mem : st₀.mem = mem₀)
    (hst0_regs : st₀.regs 0 = restH ∧ st₀.regs 1 = tourH ∧ st₀.regs 2 = newCompsPtr ∧
      st₀.regs 3 = newComps.length ∧ st₀.regs 4 = h ∧ st₀.regs 5 = y.slots.length ∧
      st₀.regs 6 = h + 2 * newComps.length) :
    ∃ st' c mt',
      Runs w p ω
        (forRange 7 (.const 0) (.reg 3)
          (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7)))) ;;
           .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))) (.const 1))) ;;
           .call 6 fInitOne [.reg 0, .reg 1, .reg 8, .reg 9,
             .bin .add (.reg 4) (.bin .mul (.const 2) (.reg 7)), .reg 6]))
        st₀ .normal st' c ∧
      NewActLoopInv (TR := TR)
        TS hRoot.querySpace w tr ord mk restH tourH h y tx₀ newComps mem₀ st₀
        newComps.length mt' st' ∧
      c + (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).phi y.bunH mt'.1 st'.mem +
          (TR y.vCap5 y.eCap5).phi tourH mt'.2 st'.mem ≤
        rangeCost (fun i => newActLoopStepCost TS hRoot.mul y.eCap5 tr ord y.comps
          (newComps.getD i (0, 0))) 0 newComps.length +
        newComps.length * 9 + 7 +
        (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).phi y.bunH y.xBun mem₀ +
        (TR y.vCap5 y.eCap5).phi tourH tx₀ mem₀ := by
  -- Unpack `hSide` and lift non-`cmpH`/non-`ctH[3*c]` facts to `mem₀`
  obtain ⟨hRec_eq, hrepB0, _, _, hBktOk, hCtOk, hMapWords⟩ := asmBrSide_lift_agree hSide hAgree
  rcases hSide with ⟨hRecBun0, _, hRecSlots0, hRecNSlots0, _, _, _, _, _, _, _, _, _,
    _, _, _, hSlotsLeCap, hPartDisj, hMaps, hModel⟩
  unfold AsmBrSideModel at hModel; unfold AsmSdMapsAt at hMaps; dsimp only at hModel hMaps
  rcases hMaps with ⟨_, hRecBkt0, hRecCt0, _, hCompsNd, hCompsMem, _, _, _, _, hMapDisj, hMapNotSl⟩
  have hRecBun : mem₀ (restH + ASM_SD_BUN) = y.bunH := (hRec_eq ASM_SD_BUN (by decide)).trans hRecBun0
  have hRecSlots : mem₀ (restH + ASM_SD_SLOTS) = y.slotsPtr := (hRec_eq ASM_SD_SLOTS (by decide)).trans hRecSlots0
  have hRecNSlots : mem₀ (restH + ASM_SD_NSLOTS) = y.slots.length := (hRec_eq ASM_SD_NSLOTS (by decide)).trans hRecNSlots0
  have hRecBkt : mem₀ (restH + ASM_SD_BKT) = y.bktH := (hRec_eq ASM_SD_BKT (by decide)).trans hRecBkt0
  have hRecCt : mem₀ (restH + ASM_SD_CT) = y.ctH := (hRec_eq ASM_SD_CT (by decide)).trans hRecCt0
  rcases hModel with ⟨hSlotMap0, hBunMatch0, _, hScurInv, _, hk1,
    ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, _, _, _, _, _, hInvB0, _, _, _, _, hkB_eq,
    ⟨hTotCap, hSlotsRange, hFreeBun0, _⟩, hInactiveInv, hCrossInv, _⟩
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hfootB0 : ∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a → a < h :=
    fun a ha => hfootSide a ⟨1, by omega, ha⟩
  have hdisjBT0 : ∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a →
      ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a := fun a ha => hdisjST a ⟨1, by omega, ha⟩
  have hrestH_lt : restH + ASM_SD_SIZE ≤ h := by
    by_contra hlt; push Not at hlt
    have : restH + ASM_SD_SIZE - 1 < h := hfootSide _ ⟨0, by omega, by unfold ASM_SD_SIZE; omega, by omega⟩
    unfold ASM_SD_SIZE at *; omega
  have htblFit : y.bunH + bundleTableFixedSize y.slotCap y.eCap5 ≤ h := by
    by_cases h0 : bundleTableFixedSize y.slotCap y.eCap5 = 0
    · unfold bundleTableFixedSize at h0; omega
    · have : y.bunH + bundleTableFixedSize y.slotCap y.eCap5 - 1 < h :=
        hfootB0 _ (Or.inl ⟨by omega, by omega⟩)
      omega
  have hbkt_lt : y.eCap5 = 0 ∨ y.bktH + y.eCap5 ≤ h := by
    rcases Nat.eq_zero_or_pos y.eCap5 with h0 | hpos
    · exact Or.inl h0
    · have := hfootSide (y.bktH + y.eCap5 - 1) ⟨3, by omega, Or.inr ⟨1, by omega, by omega⟩⟩
      exact Or.inr (by omega)
  have hsl_lt : y.slotsPtr + y.slotsCap + 1 ≤ h := by
    have : y.slotsPtr + y.slotsCap < h := hfootSide _ ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩
    omega
  have hTotSlots_le : y.slots.length + newCompsBucketSum tr y.comps newComps ≤
      min (min y.slotCap y.cap) y.slotsCap := by
    have hcard : y.slots.length = (activePairs tr).card := by
      rw [← List.toFinset_card_of_nodup hSlotMap0.1, ← hSlotMap0.image_eq,
        Finset.card_image_of_injOn fun q₁ hq₁ q₂ hq₂ heq => hSlotMap0.2.2.2.1 q₁ hq₁ q₂ hq₂ heq]
    rw [hcard]
    exact (activeBuckets_disj_sum_le tr y.comps hCompsNd hCompsMem hScurInv.1 newComps hNC_nd
      fun q hq => by
        obtain ⟨hc, hnot, _⟩ := hNC_ok q hq
        exact ⟨hc, by rwa [getElem!_pos y.comps q.1 hc]⟩).trans hTotCap
  -- Define potential Φ and invoke `forRange_amort`
  let Inv := NewActLoopInv (TR := TR)
    TS hRoot.querySpace w tr ord mk restH tourH h y tx₀ newComps mem₀ st₀
  let Φ : BundleTableMeta y.slotCap × (TR y.vCap5 y.eCap5).τ → State → ℕ :=
    fun mt st => (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).phi y.bunH mt.1 st.mem +
      (TR y.vCap5 y.eCap5).phi tourH mt.2 st.mem
  have hInitInv : Inv 0 (y.xBun, tx₀) { st₀ with regs := Function.update st₀.regs 7 0 } := by
    refine ⟨h + 2 * newComps.length, y.bunS, y.slotOf, y.cslPtr, y.cslL, fun k => Fin.elim0 k,
      fun r _ hr7 _ _ => Function.update_of_ne hr7 _ _, by simp,
      by simp [hst0_regs.2.2.2.2.2.2], ?_, ?_, fun _ _ => rfl, fun _ _ => rfl,
      hst0_mem ▸ hrepB0, hst0_mem ▸ hrepT, hInvB0, by simp [hst0_mem, hRecNSlots, newCompsBucketSum],
      fun s hs1 hs2 => by simp [newCompsBucketSum] at hs2; omega, ?_, ?_, fun k hk => by omega,
      le_refl _, by simp [newActLoopSpace], fun a ha => hst0_mem ▸ hZero a (by omega),
      fun _ ha => Or.inl ha, fun _ ha => Or.inl ha, hdisjBT0,
      fun a _ _ _ _ _ _ => congrFun hst0_mem a⟩
    · simp only [List.take_zero, List.map_nil, List.toFinset_nil, Finset.union_empty,
        newCompsBucketSum, List.sum_nil, add_zero]
      rw [← hSlotsRange]; exact hSlotMap0
    · simp only [List.take_zero, List.map_nil, List.toFinset_nil, Finset.union_empty]
      exact hBunMatch0
    · intro c hc
      obtain ⟨hct1, hcslW, hct2, hnd, hcsl, hiff⟩ := hCtOk c hc
      refine ⟨hst0_mem ▸ hct1, hcslW, hst0_mem ▸ hct2, hnd, fun bi hbi => ⟨hst0_mem ▸ (hcsl bi hbi).1, hst0_mem ▸ (hcsl bi hbi).2⟩,
        fun b t => by simp only [List.take_zero, List.map_nil, List.toFinset_nil, Finset.union_empty]; exact hiff b t,
        fun _ => ⟨rfl, rfl⟩, ?_⟩
      by_cases h0 : (y.cslL c).length = 0
      · exact Or.inl h0
      · right; refine ⟨fun _ => ?_, fun hmem => by simp at hmem, fun a ha1 ha2 => ⟨?_, ?_, ?_⟩⟩
        · have : y.cslPtr c + 2 * (y.cslL c).length - 1 < h :=
            hfootSide _ ⟨3, by omega, Or.inr ⟨c + 3, hc, by omega, by omega⟩⟩
          omega
        · exact fun hB => hPartDisj 1 (by omega) 3 (by omega) (by decide) a hB (Or.inr ⟨c + 3, hc, ha1, ha2⟩)
        · exact hdisjST a ⟨3, by omega, Or.inr ⟨c + 3, hc, ha1, ha2⟩⟩
        · exact hst0_mem ▸ hMapWords a (Or.inr ⟨c, hc, hc, ha1, ha2⟩)
    · intro c₁ hc₁ c₂ hc₂ hne a ha1 ha2 ⟨hb1, hb2⟩
      exact hMapDisj (c₁ + 3) (c₂ + 3) (by omega) a ⟨hc₁, ha1, ha2⟩ ⟨hc₂, hb1, hb2⟩
  have hStep : ∀ i mt st, i < newComps.length → Inv i mt st →
      ∃ st₁ c₁ mt₁, Runs w p ω
        (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7)))) ;;
         .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))) (.const 1))) ;;
         .call 6 fInitOne [.reg 0, .reg 1, .reg 8, .reg 9,
           .bin .add (.reg 4) (.bin .mul (.const 2) (.reg 7)), .reg 6])
        st .normal st₁ c₁ ∧
        st₁.regs 7 = i ∧
        Inv (i + 1) mt₁ { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
        Φ mt₁ { st₁ with regs := Function.update st₁.regs 7 (i + 1) } = Φ mt₁ st₁ ∧
        c₁ + Φ mt₁ st₁ ≤ newActLoopStepCost TS hRoot.mul y.eCap5 tr ord y.comps (newComps.getD i (0, 0)) + Φ mt st := by
    intro i ⟨m, tx⟩ st hi hInv
    rcases hInv with ⟨hCur, S, slotOf, cslPtr, cslL, lazyE,
      hregs, hr7, hr6, hSlotMap, hBunMatch, hOldSlotOf, hS_out, hrepB, hrepT_i, hInvB,
      hNSl_mem, hSlots_mem, hCt_i, hCslDisj, hLazy_i, hhCur_lo, hhCur_hi, hzCur,
      hftB_i, hftT_i, hdisjBT_i, hfr_i⟩
    set c_i := (newComps[i]'hi).1
    set v_i := (newComps[i]'hi).2
    obtain ⟨hc_i, hNotAct_i, hv_i⟩ := hNC_ok (newComps[i]'hi) (List.getElem_mem hi)
    have hSD_ns : ASM_SD_NSLOTS = 3 := rfl
    have hSD_sz : ASM_SD_SIZE = 16 := rfl
    have hct_lt : y.ctH + 3 * y.comps.length ≤ h := by
      have : y.ctH + 3 * y.comps.length - 1 < h :=
        hfootSide _ ⟨3, by omega, Or.inr ⟨2, by omega, by omega⟩⟩
      omega
    set C_i := y.comps[c_i]'hc_i
    have hC_i_mem : C_i ∈ components tr.cs.G₀ := (hCompsMem C_i).mp (List.getElem_mem hc_i)
    have hc_not_pref : c_i ∉ (newComps.take i).map Prod.fst := by
      intro hmem
      rw [List.mem_map] at hmem; rcases hmem with ⟨q, hq, hq1⟩
      rw [List.mem_take_iff_getElem] at hq; rcases hq with ⟨k, hk, rfl⟩
      have hk_lt : k < newComps.length := by omega
      have hEq := (List.nodup_iff_injective_getElem.mp hNC_nd)
        (a₁ := ⟨k, by simpa using hk_lt⟩) (a₂ := ⟨i, by simpa using hi⟩) (by simpa [c_i] using hq1)
      have : k = i := congrArg Fin.val hEq
      omega
    have hNotAct_pref : C_i ∉ tr.activeComps ∪ ((newComps.take i).map fun p => y.comps.getD p.1 ∅).toFinset := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hA | hP
      · exact hNotAct_i hA
      · rw [List.mem_toFinset, List.mem_map] at hP; rcases hP with ⟨q, hq, hqC⟩
        have hq_mem : q ∈ newComps := List.mem_of_mem_take hq
        obtain ⟨hq_lt, _, _⟩ := hNC_ok q hq_mem
        rw [List.getD_eq_getElem _ _ hq_lt] at hqC
        have hq_eq : q.1 = c_i := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hCompsNd)
          (a₁ := ⟨q.1, hq_lt⟩) (a₂ := ⟨c_i, hc_i⟩) hqC)
        exact hc_not_pref (List.mem_map.mpr ⟨q, hq, hq_eq⟩)
    -- Prefix/suffix bookkeeping
    set pref := newComps.take i
    set nSlots := y.slots.length + newCompsBucketSum tr y.comps pref
    have htake_succ : newComps.take (i + 1) = pref ++ [(c_i, v_i)] := by
      rw [List.take_succ_eq_append_getElem hi]
    have hBktSum_succ : newCompsBucketSum tr y.comps (newComps.take (i + 1)) =
        newCompsBucketSum tr y.comps pref + (tr.activeBuckets C_i).card := by
      unfold newCompsBucketSum
      rw [htake_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [List.getD_eq_getElem y.comps ∅ hc_i]
    have hBktSum_le_tot : newCompsBucketSum tr y.comps (newComps.take (i + 1)) ≤
        newCompsBucketSum tr y.comps newComps := by
      unfold newCompsBucketSum
      conv_rhs => rw [← List.take_append_drop (i + 1) newComps]
      rw [List.map_append, List.sum_append]; omega
    have hnSlots_cap : nSlots + (tr.activeBuckets C_i).card ≤ y.slotCap ∧
        nSlots + (tr.activeBuckets C_i).card ≤ y.cap ∧
        nSlots + (tr.activeBuckets C_i).card ≤ y.slotsCap := by
      have h1 : nSlots + (tr.activeBuckets C_i).card ≤ min (min y.slotCap y.cap) y.slotsCap := by omega
      exact ⟨le_trans h1 (le_trans (min_le_left _ _) (min_le_left _ _)),
        le_trans h1 (le_trans (min_le_left _ _) (min_le_right _ _)),
        le_trans h1 (min_le_right _ _)⟩
    have hSpace_succ : newActLoopSpace TS hRoot.querySpace tr ord y.comps (newComps.take (i + 1)) =
        newActLoopSpace TS hRoot.querySpace tr ord y.comps pref +
        newActOneSpace TS hRoot.querySpace (outCoreOrder tr ord (tr.cs.RF.root v_i)).length
          (compCoreEdges tr C_i).card (tr.activeBuckets C_i).card := by
      unfold newActLoopSpace
      rw [htake_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [List.getD_eq_getElem y.comps ∅ hc_i]
    have hSpace_le_tot : newActLoopSpace TS hRoot.querySpace tr ord y.comps (newComps.take (i + 1)) ≤
        newActLoopSpace TS hRoot.querySpace tr ord y.comps newComps := by
      unfold newActLoopSpace
      conv_rhs => rw [← List.take_append_drop (i + 1) newComps]
      rw [List.map_append, List.sum_append]; omega
    -- Evaluate the 2 loads (`r8 = c_i`, `r9 = v_i`)
    have hnc_read : st.mem (newCompsPtr + 2 * i) = c_i ∧ st.mem (newCompsPtr + 2 * i + 1) = v_i := by
      have hfr_nc : ∀ a, newCompsPtr + 2 * i ≤ a → a ≤ newCompsPtr + 2 * i + 1 → st.mem a = mem₀ a := fun a ha1 ha2 =>
        hfr_i a (by omega) (fun hB => (hNC_disj a (by omega) (by omega)).1 ⟨1, by omega, hB⟩)
          (hNC_disj a (by omega) (by omega)).2
          (fun hEq => (hNC_disj a (by omega) (by omega)).1 ⟨0, by omega, by omega, by omega⟩)
          (fun k hk ⟨h1', h2'⟩ => (hNC_disj a (by omega) (by omega)).1 ⟨3, by omega, Or.inr ⟨2, by omega, by
            have := (hNC_ok _ (List.getElem_mem (by omega : k < newComps.length))).1
            rw [List.getD_eq_getElem newComps (0, 0) (by omega)] at h2'; omega⟩⟩)
          (fun ⟨h1', h2'⟩ => (hNC_disj a (by omega) (by omega)).1 ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩)
      exact ⟨(hfr_nc _ (le_refl _) (by omega)).trans (hNC_at i hi).1,
        (hfr_nc _ (by omega) (le_refl _)).trans (hNC_at i hi).2⟩
    have hr0_i : st.regs 0 = restH := (hregs 0 (by decide) (by decide) (by decide) (by decide)).trans hst0_regs.1; have hr1_i : st.regs 1 = tourH := (hregs 1 (by decide) (by decide) (by decide) (by decide)).trans hst0_regs.2.1
    have hr2_i : st.regs 2 = newCompsPtr := (hregs 2 (by decide) (by decide) (by decide) (by decide)).trans hst0_regs.2.2.1; have hr4_i : st.regs 4 = h := (hregs 4 (by decide) (by decide) (by decide) (by decide)).trans hst0_regs.2.2.2.2.1
    have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))))) st .normal
        { st with regs := Function.update st.regs 8 c_i } _ :=
      runs_assign_iff.mpr ⟨c_i, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hr2_i)
          (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq hr7) (by omega)) (by omega))
        hnc_read.1, rfl, rfl, rfl⟩
    set stA : State := { st with regs := Function.update st.regs 8 c_i }
    have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))) (.const 1))))
        stA .normal { stA with regs := Function.update stA.regs 9 v_i } _ :=
      runs_assign_iff.mpr ⟨v_i, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, hr2_i]))
          (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [stA, hr7])) (by omega)) (by omega))
          (Expr.eval_const h1w) (by omega)) hnc_read.2, rfl, rfl, rfl⟩
    set stB : State := { stA with regs := Function.update stA.regs 9 v_i }
    -- Prepare hypotheses and invoke `asmFirstInitOneComp_runs` on `(c_i, v_i)`
    obtain ⟨hR1_i, hBktsEq_i, hCoreG0_i, _, hLazyBun_i⟩ := hInactiveInv C_i hC_i_mem hNotAct_i
    have hRec_i : st.mem (restH + ASM_SD_BUN) = y.bunH ∧ st.mem (restH + ASM_SD_SLOTS) = y.slotsPtr ∧
        st.mem (restH + ASM_SD_NSLOTS) = nSlots ∧ st.mem (restH + ASM_SD_BKT) = y.bktH ∧
        st.mem (restH + ASM_SD_CT) = y.ctH := by
      have hsd : ∀ off < ASM_SD_SIZE, off ≠ ASM_SD_NSLOTS → st.mem (restH + off) = mem₀ (restH + off) :=
        fun off hoff hne => hfr_i (restH + off) (by omega)
          (fun hB => hPartDisj 0 (by omega) 1 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩ hB)
          (hdisjST (restH + off) ⟨0, by omega, by omega, by omega⟩) (by omega)
          (fun k hk ⟨h1', h2'⟩ => hPartDisj 0 (by omega) 3 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩
            (Or.inr ⟨2, by omega, by
              have := (hNC_ok _ (List.getElem_mem (by omega : k < newComps.length))).1
              rw [List.getD_eq_getElem newComps (0, 0) (by omega)] at h2'; omega⟩))
          (fun ⟨h1', h2'⟩ => hPartDisj 0 (by omega) 3 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩ (Or.inl ⟨by omega, by omega⟩))
      exact ⟨(hsd ASM_SD_BUN (by decide) (by decide)).trans hRecBun,
        (hsd ASM_SD_SLOTS (by decide) (by decide)).trans hRecSlots, hNSl_mem,
        (hsd ASM_SD_BKT (by decide) (by decide)).trans hRecBkt,
        (hsd ASM_SD_CT (by decide) (by decide)).trans hRecCt⟩
    have hbkt_i : ∀ e ∈ tr.cs.G₀.E, e < y.eCap5 ∧ st.mem (y.bktH + e) = bucketCode (tr.origBucket e) ∧
        st.mem (y.bktH + e) < 2 ^ w := fun e he => by
      obtain ⟨hlt, heq⟩ := hBktOk e he
      have hfrB : st.mem (y.bktH + e) = mem₀ (y.bktH + e) :=
        hfr_i (y.bktH + e) (by omega)
          (fun hB => hPartDisj 1 (by omega) 3 (by omega) (by decide) (y.bktH + e) hB (Or.inr ⟨1, by omega, by omega⟩))
          (hdisjST (y.bktH + e) ⟨3, by omega, Or.inr ⟨1, by omega, by omega⟩⟩)
          (fun hEq => hPartDisj 0 (by omega) 3 (by omega) (by decide) (y.bktH + e) ⟨by omega, by omega⟩
            (Or.inr ⟨1, by omega, by omega⟩))
          (fun k hk ⟨h1', h2'⟩ => hMapDisj 1 2 (by decide) (y.bktH + e) ⟨by omega, by omega⟩
            ⟨by omega, by
              have := (hNC_ok _ (List.getElem_mem (by omega : k < newComps.length))).1
              rw [List.getD_eq_getElem newComps (0, 0) (by omega)] at h2'; omega⟩)
          (fun ⟨h1', h2'⟩ => hMapNotSl (y.bktH + e) ⟨1, by omega, by omega⟩ ⟨by omega, by omega⟩)
      exact ⟨hlt, hfrB.trans heq, hfrB.symm ▸ hMapWords (y.bktH + e) (Or.inl ⟨by omega, by omega⟩)⟩
    have hOldDisj_i : ∀ s : Fin y.slotCap, ∀ B, S s = some B →
        ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C_i → e ∉ B.edges := by
      intro s B hSB e heC htail heB
      have hIn : s.1 < nSlots := by
        by_contra hge; push Not at hge
        have := hS_out s (Or.inr hge)
        rw [hFreeBun0 s (by rw [hSlotsRange]; simp; omega)] at this
        rw [this] at hSB; cases hSB
      obtain ⟨q, hq, hsq⟩ := hSlotMap.2.2.1 s.1 (List.mem_range.mpr hIn)
      obtain ⟨hs₀, B₀, hSB₀, hAg⟩ := hBunMatch q hq
      have hB_eq : B = B₀ := by
        have : some B = some B₀ := by
          rw [← hSB]; convert hSB₀ using 2; exact Fin.ext hsq.symm
        exact Option.some.inj this
      subst hB_eq
      have he_tr : e ∈ (tr.bun q).edges := hAg.2.1 ▸ heB
      rcases Finset.mem_biUnion.mp hq with ⟨C', hC'_act, hb'⟩
      have hC'_ne : C' ≠ C_i := fun hEq => hNotAct_pref (hEq ▸ hC'_act)
      obtain ⟨-, -, hCoreInC⟩ := inactive_comp_cord_iff hI ρ hρ hC_i_mem hNotAct_i hR1_i hCrossInv hv_i
      obtain ⟨heCi, hnc⟩ := hCoreInC e (Finset.mem_filter.mpr ⟨heC, htail⟩)
      obtain ⟨b', hb'_m, hqb'⟩ := Finset.mem_image.mp hb'
      rcases Finset.mem_union.mp hC'_act with hOld | hPref
      · exact inactive_comp_edge_disj_active hI hScurInv hC_i_mem hNotAct_i heCi hnc hOld hb'_m (hqb'.symm ▸ he_tr)
      · rw [List.mem_toFinset, List.mem_map] at hPref
        rcases hPref with ⟨p', hp', rfl⟩
        obtain ⟨hp'_lt, hp'_not, _⟩ := hNC_ok p' (List.mem_of_mem_take hp')
        have hC'_eq : y.comps.getD p'.1 ∅ = y.comps[p'.1]'hp'_lt := List.getD_eq_getElem y.comps ∅ hp'_lt
        have hC'_mem : y.comps.getD p'.1 ∅ ∈ components tr.cs.G₀ := by
          rw [hC'_eq]; exact (hCompsMem _).mp (List.getElem_mem hp'_lt)
        obtain ⟨_, _, _, _, hLz'⟩ := hInactiveInv _ hC'_mem (hC'_eq.symm ▸ hp'_not)
        have hAg' := (hLz' b' hb'_m).1
        have he_bkt : e ∈ bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket (y.comps.getD p'.1 ∅) b' := by
          have hEq_e := initBundleFor_edges hI hρ (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket (y.comps.getD p'.1 ∅) b') tr.k
          rw [← hEq_e, hAg'.2.1]; exact hqb'.symm ▸ he_tr
        have ht2 : (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ y.comps.getD p'.1 ∅ := (Finset.mem_filter.mp he_bkt).2.1
        exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint tr.cs.G₀ hC_i_mem hC'_mem hC'_ne.symm) htail ht2
    -- Call `asmFirstInitOneComp_runs`
    have hFree_i : ∀ s, nSlots ≤ s → ∀ hs : s < y.slotCap, S ⟨s, hs⟩ = none := fun s hs hlt =>
      (hS_out ⟨s, hlt⟩ (Or.inr hs)).trans (hFreeBun0 ⟨s, hlt⟩ (by rw [hSlotsRange]; simp; omega))
    have hfootB_i_lt : ∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a → a < hCur := fun a ha => by
      rcases hftB_i a ha with h0 | ⟨_, hhi⟩; have := hfootB0 a h0; omega; exact hhi
    have hfootT_i_lt : ∀ a, (TR y.vCap5 y.eCap5).foot tourH tx a → a < hCur := fun a ha => by
      rcases hftT_i a ha with h0 | ⟨_, hhi⟩; have := hfootT a h0; omega; exact hhi
    have hMutDisj_i :
        (∀ a, restH ≤ a → a < restH + ASM_SD_SIZE →
          ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a ∧
          ¬ (TR y.vCap5 y.eCap5).foot tourH tx a) ∧
        (∀ a, y.bktH ≤ a → a < y.bktH + y.eCap5 → ¬ (TR y.vCap5 y.eCap5).foot tourH tx a) ∧
        (∀ a, y.ctH + 3 * c_i + 1 ≤ a → a < y.ctH + 3 * c_i + 3 →
          ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a ∧
          ¬ (TR y.vCap5 y.eCap5).foot tourH tx a ∧
          ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (y.bktH ≤ a ∧ a < y.bktH + y.eCap5)) ∧
        (∀ a, y.slotsPtr + nSlots ≤ a → a < y.slotsPtr + nSlots + (tr.activeBuckets C_i).card →
          ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a ∧
          ¬ (TR y.vCap5 y.eCap5).foot tourH tx a ∧
          ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (y.bktH ≤ a ∧ a < y.bktH + y.eCap5) ∧
          ¬ (y.ctH + 3 * c_i + 1 ≤ a ∧ a < y.ctH + 3 * c_i + 3)) ∧
        (∀ a, h + 2 * i ≤ a → a < h + 2 * i + 2 →
          ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a ∧
          ¬ (TR y.vCap5 y.eCap5).foot tourH tx a ∧
          ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (y.bktH ≤ a ∧ a < y.bktH + y.eCap5) ∧
          ¬ (y.ctH + 3 * c_i + 1 ≤ a ∧ a < y.ctH + 3 * c_i + 3) ∧
          ¬ (y.slotsPtr + nSlots ≤ a ∧ a < y.slotsPtr + nSlots + (tr.activeBuckets C_i).card)) := by
      refine ⟨fun a h1 h2 => ⟨fun hB => by rcases hftB_i a hB with h0 | ⟨hlo, _⟩; exact hPartDisj 0 (by omega) 1 (by omega) (by decide) a ⟨h1, h2⟩ h0; omega,
          fun hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨0, by omega, h1, h2⟩ h0; omega⟩,
        fun a h1 h2 hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨3, by omega, Or.inr ⟨1, h1, h2⟩⟩ h0; omega,
        fun a h1 h2 => ⟨fun hB => by rcases hftB_i a hB with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 3 (by omega) (by decide) a h0 (Or.inr ⟨2, by omega, by omega⟩); omega,
          fun hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨3, by omega, Or.inr ⟨2, by omega, by omega⟩⟩ h0; omega,
          fun hr => hPartDisj 0 (by omega) 3 (by omega) (by decide) a hr (Or.inr ⟨2, by omega, by omega⟩),
          fun hb => hMapDisj 1 2 (by decide) a hb ⟨by omega, by omega⟩⟩,
        fun a h1 h2 => ⟨fun hB => by rcases hftB_i a hB with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 3 (by omega) (by decide) a h0 (Or.inl ⟨by omega, by omega⟩); omega,
          fun hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩ h0; omega,
          fun hr => hPartDisj 0 (by omega) 3 (by omega) (by decide) a hr (Or.inl ⟨by omega, by omega⟩),
          fun hb => hMapNotSl a ⟨1, hb⟩ ⟨by omega, by omega⟩,
          fun hc' => hMapNotSl a ⟨2, by omega, by omega⟩ ⟨by omega, by omega⟩⟩,
        fun a h1 h2 => ⟨fun hB => by rcases hftB_i a hB with h0 | ⟨hlo, _⟩; have := hfootB0 a h0; omega; omega,
          fun hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; have := hfootT a h0; omega; omega,
          by omega, by omega, by omega, by omega⟩⟩
    rw [hkB_eq] at hrepB hfootB_i_lt hdisjBT_i hMutDisj_i
    have hCard_Ci : (tr.activeBuckets (y.comps[c_i]'hc_i)).card = (tr.activeBuckets C_i).card := rfl
    have hsl_ci_lt : y.slotsPtr + nSlots + (tr.activeBuckets (y.comps[c_i]'hc_i)).card ≤ hCur := by
      rw [hCard_Ci]; omega
    have hCapRoom_i : nSlots + (tr.activeBuckets (y.comps[c_i]'hc_i)).card ≤ y.slotCap := by
      rw [hCard_Ci]; exact hnSlots_cap.1
    have hSpRoom_i : hCur + newActOneSpace TS hRoot.querySpace
        (outCoreOrder tr ord (tr.cs.RF.root v_i)).length
        {e ∈ (coreGraph tr.cs.G tr.cs.lsf).E | (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ y.comps[c_i]'hc_i}.card
        (tr.activeBuckets (y.comps[c_i]'hc_i)).card < 2 ^ w := by
      change hCur + newActOneSpace TS hRoot.querySpace (outCoreOrder tr ord (tr.cs.RF.root v_i)).length
        (compCoreEdges tr C_i).card (tr.activeBuckets C_i).card < 2 ^ w
      omega
    obtain ⟨hEnd, st1, cOne, S', m', tx', uniqE, uniqB, cslPtrNew, hrunOne,
        hE_pw, hE_fin, hB_pw, hB_len, hB_iff, hrepB', hrepT', hInvB', hS'_oth, hBunNew,
        hNSl', hct1', hcsl_le_end, hct2', hcsl_at', hcsl_rg', hsl_at', hlz_at', hlz_len', hlz_lo', hlz_hi', hlz_cells',
        hh_lo', hh_hi', hz', hftB', hftT', hdisjBT', hfr', hcost'⟩ :=
      asmFirstInitOneComp_runs (ω := ω) (pos := stB.pos) (mem₀ := st.mem) (lazySlotPtr := h + 2 * i)
        hpBun hRoot hTB hI ρ hρ hCrossInv hk1 hc_i hC_i_mem hNotAct_i hR1_i hBktsEq_i hCoreG0_i
        (fun b hb => (hLazyBun_i b hb).1) hv_i hvCapG heCapG hw16 hvCapW heCapW (by omega) hRec_i
        hbkt_i (by omega) (by omega) hsl_ci_lt (by omega) hCapRoom_i hFree_i hOldDisj_i
        hrepB hInvB hrepT_i hfootB_i_lt hfootT_i_lt hdisjBT_i hMutDisj_i
        (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
            · omega
            · exact htourW
            · omega
            · exact lt_trans (hvCapG v_i (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨C_i, hC_i_mem, hv_i⟩)) hvCapW
            · omega
            · omega)
        (by omega) hzCur hSpRoom_i
    change uniqB.length = (tr.activeBuckets C_i).card at hB_len
    change st1.mem (restH + ASM_SD_NSLOTS) = nSlots + (tr.activeBuckets C_i).card at hNSl'
    change ∀ bi < (tr.activeBuckets C_i).card, st1.mem (y.slotsPtr + (nSlots + bi)) = nSlots + bi at hsl_at'
    change hEnd ≤ hCur + newActOneSpace TS hRoot.querySpace (outCoreOrder tr ord (tr.cs.RF.root v_i)).length
      (compCoreEdges tr C_i).card (tr.activeBuckets C_i).card at hh_hi'
    change ∀ a < hCur, ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 tr.k).foot y.bunH m a →
      ¬ (TR y.vCap5 y.eCap5).foot tourH tx a → a ≠ restH + ASM_SD_NSLOTS →
      ¬ (y.ctH + 3 * c_i + 1 ≤ a ∧ a < y.ctH + 3 * c_i + 3) →
      ¬ (y.slotsPtr + nSlots ≤ a ∧ a < y.slotsPtr + nSlots + (tr.activeBuckets C_i).card) →
      ¬ (h + 2 * i ≤ a ∧ a < h + 2 * i + 2) → st1.mem a = st.mem a at hfr'
    change cOne + (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 tr.k).phi y.bunH m' st1.mem +
        (TR y.vCap5 y.eCap5).phi tourH tx' st1.mem ≤
      newActOneCost TS hRoot.mul y.eCap5 (outCoreOrder tr ord (tr.cs.RF.root v_i)).length
        (compCoreEdges tr C_i).card (tr.activeBuckets C_i).card (outCoreOrder tr ord) (tr.cs.RF.root v_i) +
      (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 tr.k).phi y.bunH m st.mem +
      (TR y.vCap5 y.eCap5).phi tourH tx st.mem at hcost'
    have hcallOne : Runs w p ω
        (.call 6 fInitOne [.reg 0, .reg 1, .reg 8, .reg 9, .bin .add (.reg 4) (.bin .mul (.const 2) (.reg 7)), .reg 6])
        stB .normal { st1 with regs := Function.update stB.regs 6 hEnd } _ :=
      runs_call_iff.mpr ⟨[restH, tourH, c_i, v_i, h + 2 * i, hCur], _, .returned hEnd, st1, cOne,
        by have h2i : 2 * i < 2 ^ w := by omega
           have hh2i : h + 2 * i < 2 ^ w := by omega
           simp [evalArgs, Expr.eval, BinOp.eval, stB, stA, hr0_i, hr1_i, hr4_i, hr7, hr6, h2w, h2i, hh2i],
        hfOne, hrunOne, rfl, rfl, rfl⟩
    set stC : State := { st1 with regs := Function.update stB.regs 6 hEnd }
    have hbodyRun := runs_seq_iff.mpr (Or.inr ⟨stA, _, _, ha8,
      runs_seq_iff.mpr (Or.inr ⟨stB, _, _, ha9, hcallOne, rfl⟩), rfl⟩)
    -- Build updated `slotOf'`, `cslPtr'`, `cslL'`, `lazyE'`
    let newPairsList : List (ℤ × ℕ) :=
      (List.finRange uniqB.length).map fun bi => (bucketCodeInv (uniqB[bi.1]'bi.2), nSlots + bi.1)
    let slotOf' : Finset ℕ × ℤ → ℕ :=
      fun q => if q.1 = C_i then nSlots + uniqB.idxOf (bucketCode q.2) else slotOf q
    let cslPtr' : ℕ → ℕ := fun c => if c = c_i then cslPtrNew else cslPtr c
    let cslL' : ℕ → List (ℤ × ℕ) := fun c => if c = c_i then newPairsList else cslL c
    let lazyE' : Fin (i + 1) → List ℕ := fun k => if hk : k.1 < i then lazyE ⟨k.1, hk⟩ else uniqE
    have huniqB_nd : uniqB.Nodup := hB_pw.imp fun h => Nat.ne_of_lt h
    have hnPL_len : newPairsList.length = (tr.activeBuckets C_i).card := by
      show ((List.finRange uniqB.length).map _).length = _
      simp only [List.length_map, List.length_finRange]; exact hB_len
    have hnPL_nd : newPairsList.Nodup := by
      refine (List.nodup_finRange uniqB.length).map ?_
      intro a b hab
      have : nSlots + a.1 = nSlots + b.1 := congrArg Prod.snd hab
      exact Fin.ext (by omega)
    have hpref_union : ((newComps.take (i + 1)).map fun p => y.comps.getD p.1 ∅).toFinset =
        ((pref.map fun p => y.comps.getD p.1 ∅).toFinset) ∪ {C_i} := by
      rw [htake_succ, List.map_append, List.toFinset_append]
      ext x; simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_singleton]
      rw [List.getD_eq_getElem y.comps ∅ hc_i]
    have hact_union : activePairs { tr with activeComps := tr.activeComps ∪
          ((newComps.take (i + 1)).map fun p => y.comps.getD p.1 ∅).toFinset } =
        activePairs { tr with activeComps := tr.activeComps ∪
          (pref.map fun p => y.comps.getD p.1 ∅).toFinset } ∪
        (tr.activeBuckets C_i).image (C_i, ·) := by
      ext q; simp only [activePairs, hpref_union, Finset.mem_biUnion, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_image]
      constructor
      · rintro ⟨C', hOld | (hPref | rfl), b, hb, rfl⟩
        · exact Or.inl ⟨C', Or.inl hOld, b, hb, rfl⟩
        · exact Or.inl ⟨C', Or.inr hPref, b, hb, rfl⟩
        · exact Or.inr ⟨b, hb, rfl⟩
      · rintro (⟨C', hOld | hPref, b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
        · exact ⟨C', Or.inl hOld, b, hb, rfl⟩
        · exact ⟨C', Or.inr (Or.inl hPref), b, hb, rfl⟩
        · exact ⟨C_i, Or.inr (Or.inr rfl), b, hb, rfl⟩
    have hSlotMap' : SlotMapOK { tr with activeComps := tr.activeComps ∪
          ((newComps.take (i + 1)).map fun p => y.comps.getD p.1 ∅).toFinset }
        y.slotCap y.cap (List.range (y.slots.length + newCompsBucketSum tr y.comps (newComps.take (i + 1)))) slotOf' := by
      rw [hBktSum_succ]
      refine ⟨List.nodup_range, ?_, ?_, ?_, fun s hs => by have := List.mem_range.mp hs; omega⟩
      · intro q hq
        rw [hact_union, Finset.mem_union] at hq
        rcases hq with hOld | hNew
        · have hne : q.1 ≠ C_i := fun hEq => by
            rcases Finset.mem_biUnion.mp hOld with ⟨C', hC', hb⟩
            rcases Finset.mem_image.mp hb with ⟨b, _, hqb⟩
            rw [← hqb] at hEq; exact hNotAct_pref (hEq ▸ hC')
          have hlt := List.mem_range.mp (hSlotMap.2.1 q hOld)
          simp only [slotOf', hne, ↓reduceIte]
          exact List.mem_range.mpr (by omega)
        · rcases Finset.mem_image.mp hNew with ⟨b, hb, rfl⟩
          simp only [slotOf', ↓reduceIte]
          have hlt : uniqB.idxOf (bucketCode b) < uniqB.length := List.idxOf_lt_length_of_mem ((hB_iff b).mp hb)
          exact List.mem_range.mpr (by omega)
      · intro s hs
        have hslt := List.mem_range.mp hs
        by_cases hlt : s < nSlots
        · obtain ⟨q, hq, hsq⟩ := hSlotMap.2.2.1 s (List.mem_range.mpr hlt)
          have hne : q.1 ≠ C_i := fun hEq => by
            rcases Finset.mem_biUnion.mp hq with ⟨C', hC', hb⟩
            rcases Finset.mem_image.mp hb with ⟨b, _, hqb⟩
            rw [← hqb] at hEq; exact hNotAct_pref (hEq ▸ hC')
          exact ⟨q, hact_union ▸ Finset.mem_union_left _ hq, by simp [slotOf', hne, hsq]⟩
        · have hbi : s - nSlots < uniqB.length := by omega
          set b := bucketCodeInv (uniqB[s - nSlots]'hbi)
          have hb : b ∈ tr.activeBuckets C_i := (hB_iff b).mpr (by rw [bucketCodeInv_right]; exact List.getElem_mem hbi)
          refine ⟨(C_i, b), hact_union ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), ?_⟩
          simp only [slotOf', ↓reduceIte, b, bucketCodeInv_right]
          rw [List.Nodup.idxOf_getElem huniqB_nd (s - nSlots) hbi]; omega
      · intro q₁ hq₁ q₂ hq₂ heq
        rw [hact_union, Finset.mem_union] at hq₁ hq₂
        have hne_of : ∀ q, q ∈ activePairs { tr with activeComps := tr.activeComps ∪
            (pref.map fun p => y.comps.getD p.1 ∅).toFinset } → q.1 ≠ C_i := fun q hq hEq => by
          rcases Finset.mem_biUnion.mp hq with ⟨C', hC', hb⟩
          rcases Finset.mem_image.mp hb with ⟨b, _, hqb⟩
          rw [← hqb] at hEq; exact hNotAct_pref (hEq ▸ hC')
        rcases hq₁ with h1 | h1 <;> rcases hq₂ with h2 | h2
        · simp only [slotOf', hne_of q₁ h1, hne_of q₂ h2, ↓reduceIte] at heq
          exact hSlotMap.2.2.2.1 q₁ h1 q₂ h2 heq
        · rcases Finset.mem_image.mp h2 with ⟨b₂, _, rfl⟩
          simp only [slotOf', hne_of q₁ h1, ↓reduceIte] at heq
          have := List.mem_range.mp (hSlotMap.2.1 q₁ h1); omega
        · rcases Finset.mem_image.mp h1 with ⟨b₁, _, rfl⟩
          simp only [slotOf', hne_of q₂ h2, ↓reduceIte] at heq
          have := List.mem_range.mp (hSlotMap.2.1 q₂ h2); omega
        · rcases Finset.mem_image.mp h1 with ⟨b₁, hb₁, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨b₂, hb₂, rfl⟩
          simp only [slotOf', ↓reduceIte] at heq
          have hidx : uniqB.idxOf (bucketCode b₁) = uniqB.idxOf (bucketCode b₂) := by omega
          have h1' := List.getElem_idxOf (xs := uniqB) (x := bucketCode b₁) (List.idxOf_lt_length_of_mem ((hB_iff b₁).mp hb₁))
          have h2' := List.getElem_idxOf (xs := uniqB) (x := bucketCode b₂) (List.idxOf_lt_length_of_mem ((hB_iff b₂).mp hb₂))
          have hbc : bucketCode b₁ = bucketCode b₂ := by rw [← h1', ← h2']; congr 1
          exact Prod.ext rfl (bucketCode_injective hbc)
    have hBunMatch' : BunTableMatches { tr with activeComps := tr.activeComps ∪
          ((newComps.take (i + 1)).map fun p => y.comps.getD p.1 ∅).toFinset } slotOf' S' := by
      intro q hq
      rw [hact_union, Finset.mem_union] at hq
      rcases hq with hOld | hNew
      · have hne : q.1 ≠ C_i := fun hEq => by
          rcases Finset.mem_biUnion.mp hOld with ⟨C', hC', hb⟩
          rcases Finset.mem_image.mp hb with ⟨b, _, hqb⟩
          rw [← hqb] at hEq; exact hNotAct_pref (hEq ▸ hC')
        obtain ⟨hs₀, B₀, hSB₀, hAg₀⟩ := hBunMatch q hOld
        have hlt := List.mem_range.mp (hSlotMap.2.1 q hOld)
        have hslot : slotOf' q = slotOf q := by simp [slotOf', hne]
        refine ⟨hslot.symm ▸ hs₀, B₀, ?_, hAg₀⟩
        simpa only [hslot] using (hS'_oth ⟨slotOf q, hs₀⟩ (Or.inl hlt)).trans hSB₀
      · rcases Finset.mem_image.mp hNew with ⟨b, hb, rfl⟩
        have hbi : uniqB.idxOf (bucketCode b) < uniqB.length := List.idxOf_lt_length_of_mem ((hB_iff b).mp hb)
        obtain ⟨hs, B', hSB', hAg'⟩ := hBunNew (uniqB.idxOf (bucketCode b)) hbi
        have hbeq : bucketCodeInv (uniqB[uniqB.idxOf (bucketCode b)]'hbi) = b := by
          rw [List.getElem_idxOf hbi, bucketCodeInv_left]
        rw [hbeq] at hAg'
        have hslot : slotOf' (C_i, b) = nSlots + uniqB.idxOf (bucketCode b) := by simp [slotOf']
        refine ⟨hslot.symm ▸ hs, B', ?_, hAg'⟩
        simpa only [hslot] using hSB'
    have hftB_all : ∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m' a →
        (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a ∨
          (h + 2 * newComps.length ≤ a ∧ a < hEnd) := fun a ha => by
      rw [hkB_eq] at ha ⊢
      rcases hftB' a ha with hprev | ⟨hlo, hhi⟩
      · rcases hftB_i a (hkB_eq.symm ▸ hprev) with h0 | ⟨hlo0, hhi0⟩
        · exact Or.inl (hkB_eq ▸ h0)
        · exact Or.inr ⟨hlo0, by omega⟩
      · exact Or.inr ⟨by omega, hhi⟩
    have hftT_all : ∀ a, (TR y.vCap5 y.eCap5).foot tourH tx' a →
        (TR y.vCap5 y.eCap5).foot tourH tx₀ a ∨ (h + 2 * newComps.length ≤ a ∧ a < hEnd) := fun a ha => by
      rcases hftT' a ha with hprev | ⟨hlo, hhi⟩
      · rcases hftT_i a hprev with h0 | ⟨hlo0, hhi0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hlo0, by omega⟩
      · exact Or.inr ⟨by omega, hhi⟩
    refine ⟨stC, _, (m', tx'), hbodyRun, by simp [stC, stB, stA, hr7], ?_, rfl, ?_⟩
    · -- Prove `Inv (i + 1) (m', tx') { stC with regs := Function.update stC.regs 7 (i + 1) }`
      refine ⟨hEnd, S', slotOf', cslPtr', cslL', lazyE',
        fun r hr6' hr7' hr8' hr9' => by simp [stC, stB, stA, Function.update_of_ne hr7', Function.update_of_ne hr6', Function.update_of_ne hr9', Function.update_of_ne hr8', hregs r hr6' hr7' hr8' hr9'],
        by simp, by simp [stC], hSlotMap', hBunMatch', ?_, ?_, hkB_eq.symm ▸ hrepB', hrepT', hInvB',
        by rw [hBktSum_succ]; dsimp only [stC, C_i, nSlots] at hNSl' ⊢; omega, ?_, ?_, ?_, ?_, by omega,
        by rw [hSpace_succ]; dsimp only [compCoreEdges, C_i, v_i] at hh_hi' ⊢; omega,
        hz', hftB_all, hftT_all, hkB_eq.symm ▸ hdisjBT', ?_⟩
      · intro q hq
        have hne : q.1 ≠ C_i := fun hEq => hNotAct_i (by
          rcases Finset.mem_biUnion.mp hq with ⟨C', hC', hb⟩
          rcases Finset.mem_image.mp hb with ⟨b, _, hqb⟩
          rw [← hqb] at hEq; exact hEq ▸ hC')
        simp [slotOf', hne, hOldSlotOf q hq]
      · intro s hs; rw [hBktSum_succ] at hs
        rcases hs with hlt | hge
        · exact (hS'_oth s (Or.inl (by omega))).trans (hS_out s (Or.inl hlt))
        · exact (hS'_oth s (Or.inr (by rw [hCard_Ci]; omega))).trans (hS_out s (Or.inr (by omega)))
      · intro s hs1 hs2; rw [hBktSum_succ] at hs2
        by_cases hlt : s < nSlots
        · have hfr_s : st1.mem (y.slotsPtr + s) = st.mem (y.slotsPtr + s) :=
            hfr' (y.slotsPtr + s) (by omega)
              (fun hB => by rcases hftB_i (y.slotsPtr + s) (hkB_eq.symm ▸ hB) with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 3 (by omega) (by decide) (y.slotsPtr + s) h0 (Or.inl ⟨by omega, by omega⟩); omega)
              (fun hT => by rcases hftT_i (y.slotsPtr + s) hT with h0 | ⟨hlo, _⟩; exact hdisjST (y.slotsPtr + s) ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩ h0; omega)
              (fun hEq => hPartDisj 0 (by omega) 3 (by omega) (by decide) (y.slotsPtr + s) ⟨by omega, by omega⟩ (Or.inl ⟨by omega, by omega⟩))
              (fun ⟨h1', h2'⟩ => hMapNotSl (y.slotsPtr + s) ⟨2, by omega, by omega⟩ ⟨by omega, by omega⟩) (by omega) (by omega)
          exact hfr_s.trans (hSlots_mem s hs1 hlt)
        · have hbi : s - nSlots < (tr.activeBuckets C_i).card := by omega
          have := hsl_at' (s - nSlots) hbi
          rwa [show nSlots + (s - nSlots) = s by omega] at this
      · -- `csl` for every `c < y.comps.length`
        intro c hc
        by_cases hcc : c = c_i
        · subst hcc
          simp only [cslPtr', cslL', ↓reduceIte]
          refine ⟨hct1', by omega, by rw [hnPL_len]; exact hct2', hnPL_nd, ?_, ?_,
            fun hnot => absurd (by rw [htake_succ, List.map_append]; simp) hnot, ?_⟩
          · intro bi hbi
            have hbi' : bi < uniqB.length := by simpa [hnPL_len, hB_len] using hbi
            simp only [newPairsList, List.getElem_map, List.getElem_finRange, bucketCodeInv_right]
            exact hcsl_at' bi hbi'
          · intro b t
            simp only [newPairsList, List.mem_map, List.mem_finRange, true_and, Prod.mk.injEq]
            constructor
            · rintro ⟨bi, rfl, rfl⟩
              have hb : bucketCodeInv (uniqB[bi.1]'bi.2) ∈ tr.activeBuckets C_i :=
                (hB_iff _).mpr (by rw [bucketCodeInv_right]; exact List.getElem_mem bi.2)
              refine ⟨hact_union ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), ?_⟩
              simp only [slotOf', bucketCodeInv_right]
              rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), List.Nodup.idxOf_getElem huniqB_nd bi.1 bi.2]
            · rintro ⟨hq, rfl⟩
              have hb : b ∈ tr.activeBuckets C_i := by
                rw [hact_union, Finset.mem_union] at hq
                rcases hq with hOld | hNew
                · rcases Finset.mem_biUnion.mp hOld with ⟨C', hC', hb'⟩
                  rcases Finset.mem_image.mp hb' with ⟨b', _, hEq⟩
                  have : C' = C_i := congrArg Prod.fst hEq
                  exact absurd (this ▸ hC') hNotAct_pref
                · rcases Finset.mem_image.mp hNew with ⟨b', hb', hEq⟩
                  have : b' = b := congrArg Prod.snd hEq
                  exact this ▸ hb'
              have hbi : uniqB.idxOf (bucketCode b) < uniqB.length := List.idxOf_lt_length_of_mem ((hB_iff b).mp hb)
              refine ⟨⟨uniqB.idxOf (bucketCode b), hbi⟩, ?_, by simp [slotOf', C_i]⟩
              rw [List.getElem_idxOf hbi, bucketCodeInv_left]
          · rcases hcsl_rg' with hr0 | ⟨hlo, hhi, hcells⟩
            · exact Or.inl (by rw [hnPL_len]; exact hr0)
            · right; rw [hnPL_len]
              exact ⟨fun hnot => absurd (by rw [htake_succ, List.map_append]; simp) hnot, fun _ => ⟨by omega, hhi⟩,
                fun a ha1 ha2 => by
                  have hc' := hcells a ha1 ha2
                  exact ⟨hkB_eq.symm ▸ hc'.1, hc'.2.1, hc'.2.2⟩⟩
        · simp only [cslPtr', cslL', hcc, ↓reduceIte]
          obtain ⟨hct1_c, hcslW_c, hct2_c, hnd_c, hcsl_c, hiff_c, hnotP_c, hrg_c⟩ := hCt_i c hc
          have hct_fr : ∀ off, off = 1 ∨ off = 2 → st1.mem (y.ctH + 3 * c + off) = st.mem (y.ctH + 3 * c + off) :=
            fun off hoff => hfr' (y.ctH + 3 * c + off) (by omega)
              (fun hB => by rcases hftB_i (y.ctH + 3 * c + off) (hkB_eq.symm ▸ hB) with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 3 (by omega) (by decide) (y.ctH + 3 * c + off) h0 (Or.inr ⟨2, by omega, by omega⟩); omega)
              (fun hT => by rcases hftT_i (y.ctH + 3 * c + off) hT with h0 | ⟨hlo, _⟩; exact hdisjST (y.ctH + 3 * c + off) ⟨3, by omega, Or.inr ⟨2, by omega, by omega⟩⟩ h0; omega)
              (fun hEq => hPartDisj 0 (by omega) 3 (by omega) (by decide) (y.ctH + 3 * c + off) ⟨by omega, by omega⟩ (Or.inr ⟨2, by omega, by omega⟩))
              (by omega) (fun ⟨h1', h2'⟩ => hMapNotSl (y.ctH + 3 * c + off) ⟨2, by omega, by omega⟩ ⟨by omega, by omega⟩) (by omega)
          have hmem_c : ∀ a, cslPtr c ≤ a → a < cslPtr c + 2 * (cslL c).length → st1.mem a = st.mem a := fun a ha1 ha2 => by
            rcases hrg_c with h0 | ⟨hlo_np, hlo_p, hcells⟩
            · omega
            · by_cases hcp : c ∈ pref.map Prod.fst
              · have ⟨hc1, hc2⟩ := hlo_p hcp
                exact hfr' a (by omega) (hkB_eq ▸ (hcells a ha1 ha2).1) (hcells a ha1 ha2).2.1
                  (by omega) (by omega) (by omega) (by omega)
              · have ⟨hcp_eq, hcl_eq⟩ := hnotP_c hcp
                have ha_lt := hlo_np hcp
                exact hfr' a (by omega) (hkB_eq ▸ (hcells a ha1 ha2).1) (hcells a ha1 ha2).2.1
                  (fun hEq => hPartDisj 0 (by omega) 3 (by omega) (by decide) a
                    ⟨by omega, by omega⟩
                    (Or.inr ⟨c + 3, hc, hcp_eq ▸ ha1, hcp_eq ▸ hcl_eq ▸ ha2⟩))
                  (fun ⟨h1', h2'⟩ => hMapDisj (c + 3) 2 (by omega) a ⟨hc, hcp_eq ▸ ha1, hcp_eq ▸ hcl_eq ▸ ha2⟩ ⟨by omega, by omega⟩)
                  (fun ⟨h1', h2'⟩ => hMapNotSl a ⟨c + 3, hc, hcp_eq ▸ ha1, hcp_eq ▸ hcl_eq ▸ ha2⟩ ⟨by omega, by omega⟩)
                  (by omega)
          refine ⟨(hct_fr 1 (Or.inl rfl)).trans hct1_c, hcslW_c, (hct_fr 2 (Or.inr rfl)).trans hct2_c, hnd_c,
            fun bi hbi => ⟨(hmem_c _ (by omega) (by omega)).trans (hcsl_c bi hbi).1,
              (hmem_c _ (by omega) (by omega)).trans (hcsl_c bi hbi).2⟩,
            fun b t => by
              rw [hiff_c b t, hact_union, Finset.mem_union]
              have hneC : y.comps[c]'hc ≠ C_i := fun hEq => hcc (congrArg Fin.val
                ((List.nodup_iff_injective_getElem.mp hCompsNd) (a₁ := ⟨c, hc⟩) (a₂ := ⟨c_i, hc_i⟩) hEq))
              simp [slotOf', hneC, hneC.symm],
            fun hnot => hnotP_c (fun hm => hnot (by rw [htake_succ]; simp [hm])), ?_⟩
          rcases hrg_c with h0 | ⟨hlo_np, hlo_p, hcells⟩
          · exact Or.inl h0
          · right
            refine ⟨fun hnot => hlo_np (fun hm => hnot (by rw [htake_succ]; simp [hm])),
              fun hmem => by
                have hcp : c ∈ pref.map Prod.fst := by rw [htake_succ] at hmem; simpa [hcc] using hmem
                have ⟨hc1, hc2⟩ := hlo_p hcp; exact ⟨hc1, by omega⟩,
              fun a ha1 ha2 => ?_⟩
            have halt : a < hCur := by
              by_cases hcp : c ∈ pref.map Prod.fst
              · have := (hlo_p hcp).2; omega
              · have := hlo_np hcp; omega
            refine ⟨fun hB => ?_, fun hT => ?_, by rw [hmem_c a ha1 ha2]; exact (hcells a ha1 ha2).2.2⟩
            · rcases hftB' a (hkB_eq ▸ hB) with hprev | ⟨hlo, _⟩
              · exact (hcells a ha1 ha2).1 (hkB_eq.symm ▸ hprev)
              · omega
            · rcases hftT' a hT with hprev | ⟨hlo, _⟩
              · exact (hcells a ha1 ha2).2.1 hprev
              · omega
      · -- `cslDisj`
        intro c₁ hc₁ c₂ hc₂ hne a ha1 ha2 ⟨hb1, hb2⟩
        by_cases h1 : c₁ = c_i
        · subst h1; simp only [cslPtr', cslL', ↓reduceIte, Ne.symm hne] at ha1 ha2 hb1 hb2
          rcases hcsl_rg' with hr0 | ⟨hlo, _, _⟩
          · rw [hnPL_len, show (tr.activeBuckets C_i).card = 0 from hr0] at ha2; omega
          · obtain ⟨_, _, _, _, _, _, _, hrg2⟩ := hCt_i c₂ hc₂
            rcases hrg2 with h0 | ⟨hlo_np, hlo_p, _⟩
            · omega
            · by_cases hcp : c₂ ∈ pref.map Prod.fst
              · have := (hlo_p hcp).2; omega
              · have := hlo_np hcp; omega
        · by_cases h2 : c₂ = c_i
          · subst h2; simp only [cslPtr', cslL', ↓reduceIte, h1] at ha1 ha2 hb1 hb2
            rcases hcsl_rg' with hr0 | ⟨hlo, _, _⟩
            · rw [hnPL_len, show (tr.activeBuckets C_i).card = 0 from hr0] at hb2; omega
            · obtain ⟨_, _, _, _, _, _, _, hrg1⟩ := hCt_i c₁ hc₁
              rcases hrg1 with h0 | ⟨hlo_np, hlo_p, _⟩
              · omega
              · by_cases hcp : c₁ ∈ pref.map Prod.fst
                · have := (hlo_p hcp).2; omega
                · have := hlo_np hcp; omega
          · simp only [cslPtr', cslL', h1, h2, ↓reduceIte] at ha1 ha2 hb1 hb2
            exact hCslDisj c₁ hc₁ c₂ hc₂ hne a ha1 ha2 ⟨hb1, hb2⟩
      · -- `lazyE'`
        intro k hk
        by_cases hki : k < i
        · simp only [lazyE', hki, ↓reduceDIte]
          obtain ⟨hlz_at_k, hlz_len_k, hpw_k, hfin_k, hlo, hhi, hcells⟩ := hLazy_i k hki
          have hslot_eq : st1.mem (h + 2 * k) = st.mem (h + 2 * k) ∧
              st1.mem (h + 2 * k + 1) = st.mem (h + 2 * k + 1) := by
            have hfr_lz : ∀ a, h + 2 * k ≤ a → a ≤ h + 2 * k + 1 → st1.mem a = st.mem a := fun a ha1 ha2 =>
              hfr' a (by omega)
                (fun hB => by rcases hftB_i a (hkB_eq.symm ▸ hB) with h0 | ⟨hlo, _⟩; have := hfootB0 _ h0; omega; omega)
                (fun hT => by rcases hftT_i a hT with h0 | ⟨hlo, _⟩; have := hfootT _ h0; omega; omega)
                (by omega) (by omega) (by omega) (by omega)
            exact ⟨hfr_lz _ (le_refl _) (by omega), hfr_lz _ (by omega) (le_refl _)⟩
          refine ⟨?_, hslot_eq.2.trans hlz_len_k, hpw_k, hfin_k, ?_⟩
          · intro idx hidx
            change st1.mem (st1.mem (h + 2 * k) + idx) = _
            rw [hslot_eq.1, hfr' (st.mem (h + 2 * k) + idx) (by omega)
              (hkB_eq ▸ (hcells (st.mem (h + 2 * k) + idx) (by omega) (by omega)).1)
              (hcells (st.mem (h + 2 * k) + idx) (by omega) (by omega)).2
              (by omega) (by omega) (by omega) (by omega)]
            exact hlz_at_k idx hidx
          · rw [hslot_eq.1]
            refine ⟨hlo, by omega, fun a ha1 ha2 => ⟨fun hB => ?_, fun hT => ?_⟩⟩
            · rcases hftB' a (hkB_eq ▸ hB) with hprev | ⟨hlo', _⟩
              · exact (hcells a ha1 ha2).1 (hkB_eq.symm ▸ hprev)
              · omega
            · rcases hftT' a hT with hprev | ⟨hlo', _⟩
              · exact (hcells a ha1 ha2).2 hprev
              · omega
        · have hkeq : k = i := by omega
          subst hkeq
          simp only [lazyE', lt_irrefl, ↓reduceDIte]
          refine ⟨hlz_at', hlz_len', hE_pw, by rw [List.getD_eq_getElem newComps (0, 0) hi, List.getD_eq_getElem y.comps ∅ hc_i]; exact hE_fin, ?_⟩
          dsimp only [stC]
          exact ⟨by omega, hlz_hi', fun a ha1 ha2 =>
            ⟨hkB_eq.symm ▸ (hlz_cells' a ha1 ha2).1, (hlz_cells' a ha1 ha2).2⟩⟩
      · -- Frame `< h`
        intro a ha hnb hnt hns hct hsl
        rw [hBktSum_succ] at hsl
        have hnb_i : ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 tr.k).foot y.bunH m a := fun hB => by
          rcases hftB_i a (hkB_eq.symm ▸ hB) with h0 | ⟨hlo, _⟩; exact hnb h0; omega
        have hnt_i : ¬ (TR y.vCap5 y.eCap5).foot tourH tx a := fun hT => by
          rcases hftT_i a hT with h0 | ⟨hlo, _⟩; exact hnt h0; omega
        have hct_ci : ¬ (y.ctH + 3 * c_i + 1 ≤ a ∧ a < y.ctH + 3 * c_i + 3) := by
          have := hct i (by omega)
          rwa [List.getD_eq_getElem newComps (0, 0) hi] at this
        have hsl_ci : ¬ (y.slotsPtr + nSlots ≤ a ∧ a < y.slotsPtr + nSlots + (tr.activeBuckets C_i).card) :=
          fun ⟨h1', h2'⟩ => hsl ⟨by omega, by omega⟩
        have hsl_prev : ¬ (y.slotsPtr + y.slots.length ≤ a ∧ a < y.slotsPtr + nSlots) :=
          fun ⟨h1', h2'⟩ => hsl ⟨h1', by omega⟩
        have h1 := hfr' a (by omega) hnb_i hnt_i hns hct_ci hsl_ci (by omega)
        exact h1.trans (hfr_i a ha hnb hnt hns (fun k hk => hct k (by omega)) hsl_prev)
    · -- Amortized cost bound
      have hkB_tr : y.kB = tr.k := hkB_eq
      dsimp only [Φ, newActLoopStepCost, argsSize, Expr.size, stC, stB, stA, compCoreEdges, C_i, v_i, c_i] at hcost' ⊢
      rw [List.getD_eq_getElem newComps (0, 0) hi, List.getD_eq_getElem y.comps ∅ hc_i, hkB_tr]
      omega
  obtain ⟨st', c, mt', hrun, hInvEnd, hcost⟩ :=
    forRange_amort (ω := ω) Inv Φ
      (fun i => newActLoopStepCost TS hRoot.mul y.eCap5 tr ord y.comps (newComps.getD i (0, 0)))
      newComps.length h1w (by omega) hInitInv
      (fun _ _ _ _ ⟨_, _, _, _, _, _, _, hr7, _⟩ => hr7)
      (fun _ _ _ _ ⟨_, _, _, _, _, _, hregs, _⟩ =>
        Expr.eval_reg_of_eq ((hregs 3 (by decide) (by decide) (by decide) (by decide)).trans hst0_regs.2.2.2.1))
      hStep
  refine ⟨st', c, mt', hrun, hInvEnd, ?_⟩
  dsimp only [Φ, Expr.size] at hcost
  rw [hst0_mem] at hcost
  omega

end

end MinCostFlow.SparseCore.Program

