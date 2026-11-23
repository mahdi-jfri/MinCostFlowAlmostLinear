module

public import MinCostFlow.SparseCore.Program.BundleInitInner

import WordRAM.Tactic

/-!
# Outer tour scan and full verification of `bundleInitSlotsStmt` (`BundleInitProofs`)

Verifies:
1. `bundleInitLoop3_runs`: Loop 3 of `bundleInitSlotsStmt` via `runs_forRange_pot`, invoking
   `htour.list_runs` once per core vertex `v ∈ rList` and `bundleInitInner_triple` to chunk every
   initialized slot's incident ends simultaneously.
2. `bundleInitSlots_runs`: full end-to-end correctness, representation invariants
   (`BundleTableRepAt`, `BundleTableCordMatch`), heap/footprint containment, and amortized time
   bound (`bundleInitSlotsCost`) for `bundleInitSlotsStmt`.
3. `bundleInitSlots_eq_initBundleState`: exact agreement of every initialized slot with
   `initBundleState ρ E_s k` and `initBundleFor cs ord E_s k`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Helper lemmas connecting `bundleStateOfSlots` to `InitScanSlotInv` -/

lemma initPrefixSlots_flatMap_nodup {cord : ℕ → List End} {rList : List ℕ} {E : Finset ℕ}
    {k : ℕ} (hk : 1 ≤ k) (hr_nd : rList.Nodup) (hcord_nd : ∀ w ∈ rList, (cord w).Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂) :
    ((initPrefixSlots cord rList E k).flatMap Prod.snd).Nodup := by
  have hflat : (initPrefixSlots cord rList E k).flatMap Prod.snd =
      rList.flatMap fun w => (cord w).filter fun x => decide (x.1 ∈ E) := by
    simp only [initPrefixSlots, List.flatMap_assoc, List.flatMap_map]
    apply List.flatMap_congr; intro w _
    simpa [List.flatten] using (initialChunks_spec hk ((cord w).filter fun x => decide (x.1 ∈ E))).1
  rw [hflat, List.nodup_flatMap]
  refine ⟨fun w hw => (hcord_nd w hw).filter _, ?_⟩
  exact hr_nd.imp fun hne =>
    List.disjoint_left.mpr fun x hx1 hx2 =>
      hne (hcord_disj _ _ x (List.mem_filter.mp hx1).1 (List.mem_filter.mp hx2).1)

lemma bundleStateOfSlots_props {cord : ℕ → List End} {rList : List ℕ} {E : Finset ℕ}
    {k : ℕ} (hk : 1 ≤ k) (hr_nd : rList.Nodup) (hcord_nd : ∀ w ∈ rList, (cord w).Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hcov : ∀ x : End, x.1 ∈ E → ∃ v ∈ rList, x ∈ cord v) :
    let slots := initPrefixSlots cord rList E k
    let B := bundleStateOfSlots slots E
    (∀ b (hb : b < slots.length), slots[b].2 ≠ []) ∧
    (∀ b (hb : b < slots.length), slots[b].1 ∈ rList ∧ ∀ x ∈ slots[b].2, x.1 ∈ E ∧ x ∈ cord slots[b].1) ∧
    (∀ b (hb : b < slots.length), ∀ x ∈ slots[b].2, B.bundleOf x = b) ∧
    (∀ x ∈ edgeEnds E, B.bundleOf x < slots.length) ∧
    (∀ b (hb : b < slots.length), ∀ x, x ∈ B.ends b ↔ x ∈ slots[b].2) := by
  intro slots B
  have hnd := initPrefixSlots_flatMap_nodup (E := E) hk hr_nd hcord_nd hcord_disj
  have hne : ∀ b (hb : b < slots.length), slots[b].2 ≠ [] := by
    intro b hb
    have hmem : slots[b] ∈ slots := List.getElem_mem hb
    simp only [slots, initPrefixSlots, List.mem_flatMap, List.mem_map] at hmem
    rcases hmem with ⟨v, _, ch, hch, heq⟩
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hch
    have hpos : 0 < ((initialChunks k ((cord v).filter fun x => decide (x.1 ∈ E)))[c]'hc).length := by
      rw [initialChunks_getElem_length]
      have hcl : c < (((cord v).filter fun x => decide (x.1 ∈ E)).length + k - 1) / k := by
        simpa [initialChunks_length_eq] using hc
      have hck : c * k < ((cord v).filter fun x => decide (x.1 ∈ E)).length := by
        have h1 : (c + 1) * k ≤ (((cord v).filter fun x => decide (x.1 ∈ E)).length + k - 1) / k * k :=
          Nat.mul_le_mul_right k hcl
        have h2 := Nat.div_mul_le_self (((cord v).filter fun x => decide (x.1 ∈ E)).length + k - 1) k
        have h3 : c * k + k = (c + 1) * k := by ring
        omega
      omega
    have h2 : slots[b].2 = (initialChunks k ((cord v).filter fun x => decide (x.1 ∈ E)))[c]'hc :=
      congrArg Prod.snd heq.symm
    rw [h2]; exact List.ne_nil_of_length_pos hpos
  have hmem_src : ∀ b (hb : b < slots.length),
      slots[b].1 ∈ rList ∧ ∀ x ∈ slots[b].2, x.1 ∈ E ∧ x ∈ cord slots[b].1 := by
    intro b hb
    have hmem : slots[b] ∈ slots := List.getElem_mem hb
    simp only [slots, initPrefixSlots, List.mem_flatMap, List.mem_map] at hmem
    rcases hmem with ⟨v, hv, ch, hch, heq⟩
    have h1 : slots[b].1 = v := congrArg Prod.fst heq.symm
    have h2 : slots[b].2 = ch := congrArg Prod.snd heq.symm
    refine ⟨h1 ▸ hv, fun x hx => ?_⟩
    rw [h2] at hx
    have hfl := (initialChunks_spec hk ((cord v).filter fun y => decide (y.1 ∈ E))).1
    have hxf : x ∈ (cord v).filter fun y => decide (y.1 ∈ E) := by
      rw [← hfl]; exact List.mem_flatten.mpr ⟨ch, hch, hx⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hxf
    exact ⟨hxf.2, h1 ▸ hxf.1⟩
  have hdisj_b : ∀ b₁ b₂ (h₁ : b₁ < slots.length) (h₂ : b₂ < slots.length), b₁ ≠ b₂ →
      ∀ x, x ∈ slots[b₁].2 → x ∉ slots[b₂].2 := by
    intro b₁ b₂ h₁ h₂ hne x hx1 hx2
    have hpw := (List.nodup_flatMap.mp hnd).2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact List.disjoint_left.mp (List.pairwise_iff_getElem.mp hpw b₁ b₂ h₁ h₂ hlt) hx1 hx2
    · exact List.disjoint_left.mp (List.pairwise_iff_getElem.mp hpw b₂ b₁ h₂ h₁ hgt) hx2 hx1
  have hbun : ∀ b (hb : b < slots.length), ∀ x ∈ slots[b].2, B.bundleOf x = b := by
    intro b hb x hx
    change slots.findIdx (fun p => p.2.contains x) = b
    rw [List.findIdx_eq hb]
    refine ⟨List.contains_iff_mem.mpr hx, fun j hj => ?_⟩
    rw [Bool.eq_false_iff]; intro hc
    exact hdisj_b b j hb (Nat.lt_trans hj hb) (by omega) x hx (List.contains_iff_mem.mp hc)
  have hlt_all : ∀ x ∈ edgeEnds E, B.bundleOf x < slots.length := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := hcov x ((mem_edgeEnds E x).mp hx)
    have hxf : x ∈ (cord v).filter fun y => decide (y.1 ∈ E) :=
      List.mem_filter.mpr ⟨hxv, decide_eq_true ((mem_edgeEnds E x).mp hx)⟩
    have hfl := (initialChunks_spec hk ((cord v).filter fun y => decide (y.1 ∈ E))).1
    rw [← hfl] at hxf
    obtain ⟨ch, hch, hxch⟩ := List.mem_flatten.mp hxf
    have hmem : (v, ch) ∈ slots := List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨ch, hch, rfl⟩⟩
    obtain ⟨b, hb, hbeq⟩ := List.getElem_of_mem hmem
    rw [hbun b hb x (by simpa [hbeq] using hxch)]
    exact hb
  refine ⟨hne, hmem_src, hbun, hlt_all, fun b hb x => ?_⟩
  rw [BundleState.mem_ends]
  constructor
  · rintro ⟨hxE, hbx⟩
    obtain ⟨v, hv, hxv⟩ := hcov x hxE
    have hxf : x ∈ (cord v).filter fun y => decide (y.1 ∈ E) :=
      List.mem_filter.mpr ⟨hxv, decide_eq_true hxE⟩
    have hfl := (initialChunks_spec hk ((cord v).filter fun y => decide (y.1 ∈ E))).1
    rw [← hfl] at hxf
    obtain ⟨ch, hch, hxch⟩ := List.mem_flatten.mp hxf
    have hmem : (v, ch) ∈ slots := List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨ch, hch, rfl⟩⟩
    obtain ⟨b', hb', hbeq⟩ := List.getElem_of_mem hmem
    have hx' : x ∈ slots[b'].2 := by simpa [hbeq] using hxch
    have hbb : b' = b := (hbun b' hb' x hx').symm.trans hbx
    exact hbb ▸ hx'
  · intro hx
    exact ⟨(hmem_src b hb).2 x hx |>.1, hbun b hb x hx⟩

/-! ## 2. Outer Loop 3 verification (`bundleInitLoop3_runs`) -/

/-- Verifies Loop 3 of `bundleInitSlotsStmt` using `runs_forRange_pot`: scans `rList` once, calling
`htour.list_runs` once per core vertex and `bundleInitInner_triple` to chunk all initialized slots
simultaneously, threading `hCur` and the tour metadata `tx` with exact potential telescoping. -/
theorem bundleInitLoop3_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k nSlots
    slotSpecPtr nEdges edgeAssignPtr nR rPtr h : ℕ}
    {pProg : Program} {bDllPush bTourList bTourLen bTourOwner : ℕ}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {mem₀ : ℕ → ℕ} {st₀ : State} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hbPush : ∀ prevBase nextBase headAddr key L,
      MeetsContract w pProg bDllPush
        (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hw16 : 16 ≤ 2 ^ w)
    (hk1 : 1 ≤ k)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hrPtr_h : rPtr + nR ≤ h)
    (hrPtr_disj : rPtr + nR ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS specs cord rList < 2 ^ w)
    (hnR : rList.length = nR)
    (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w)
    (hrList_nd : rList.Nodup)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap)
    (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_cap : ∀ sb ∈ specs,
      (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k).length ≤ sb.2)
    (hcord_nd : ∀ w' ∈ rList, (cord w').Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hcord_lt : ∀ v ∈ rList, ∀ x ∈ cord v, x.1 < eCap)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + nR ≤ a)
    (hzero : ZeroFrom mem₀ (h + slotBlocksSpace specs))
    (hslotPtr : ∀ q (hq : q < specs.length),
      mem₀ (btSlotPtrBase tbl + specs[q].1) = h + slotBlocksSpace (specs.take q))
    (htouched_in : ∀ s ∈ specs.map Prod.fst, mem₀ (btSlotTouchedBase tbl slotCap eCap + s) = 1)
    (htouched_out : ∀ s < slotCap, s ∉ specs.map Prod.fst →
      mem₀ (btSlotTouchedBase tbl slotCap eCap + s) = 0)
    (hedgeSlot_in : ∀ e < eCap, ∀ s ∈ specs.map Prod.fst, e ∈ slotEdgesOf assigns s →
      mem₀ (btEdgeSlotBase tbl slotCap + e) = s + 1)
    (hedgeSlot_out : ∀ e < eCap, (∀ s ∈ specs.map Prod.fst, e ∉ slotEdgesOf assigns s) →
      mem₀ (btEdgeSlotBase tbl slotCap + e) = 0 ∨
      ∃ s < slotCap, s ∉ specs.map Prod.fst ∧ mem₀ (btEdgeSlotBase tbl slotCap + e) = s + 1)
    (hinit0 : ∀ q (hq : q < specs.length),
      InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
        (btCurTagBase tbl slotCap eCap) cord rList 0 0 specs[q].1
        (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) mem₀)
    (hst0 : st₀.mem = mem₀ ∧
      BundleInitConstRegs st₀ tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
        slotCap eCap ∧
      st₀.regs 10 = h + slotBlocksSpace specs ∧
      st₀.regs 17 = btCurBunBase tbl slotCap eCap ∧
      st₀.regs 18 = btCurTagBase tbl slotCap eCap) :
    ∃ st' c hEnd tx',
      Runs w pProg ω
        (forRange 19 (.const 0) (.reg 7)
          (.assign 20 (.load (.bin .add (.reg 8) (.reg 19))) ;;
           .call 21 bTourList [.reg 1, .reg 20, .reg 10] ;;
           .assign 22 (.load (.reg 10)) ;;
           forRange 23 (.const 0) (.reg 22) (bundleInitEndBody bDllPush) ;;
           .assign 10 (.reg 21)))
        st₀ .normal st' c ∧
      BundleInitConstRegs st' tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
        slotCap eCap ∧
      st'.regs 10 = hEnd ∧
      st'.regs 17 = btCurBunBase tbl slotCap eCap ∧
      st'.regs 18 = btCurTagBase tbl slotCap eCap ∧
      h + slotBlocksSpace specs ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS specs cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + slotBlocksSpace specs ≤ a ∧ a < hEnd)) ∧
      (∀ q (hq : q < specs.length),
        InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
          (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
          (btCurTagBase tbl slotCap eCap) cord rList nR 0 specs[q].1
          (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) st'.mem) ∧
      (∀ a, a < h → ¬ htour.rep.foot tourH tx₀ a →
        (∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
          a ≠ btEndBundleBase tbl slotCap eCap + endKey x ∧
          a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
          a ≠ btEndNextBase tbl slotCap eCap + endKey x) →
        (∀ s ∈ specs.map Prod.fst,
          a ≠ btCurBunBase tbl slotCap eCap + s ∧
          a ≠ btCurTagBase tbl slotCap eCap + s) →
        st'.mem a = mem₀ a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        45 * nR + (rList.map fun v => (TS.mul * ordStoreLog eCap + 220) * ((cord v).length + 1)).sum + 15 +
          htour.rep.phi tourH tx₀ mem₀ := by
  let h2 := h + slotBlocksSpace specs
  let listSpacePref : ℕ → ℕ := fun i => ((rList.take i).map fun v => TS.listSpace (cord v).length).sum
  let Inv : ℕ → ℕ × htour.rep.τ → State → Prop := fun i ⟨hCur, tx⟩ st =>
    BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
      slotCap eCap ∧
    st.regs 10 = hCur ∧ st.regs 17 = btCurBunBase tbl slotCap eCap ∧
    st.regs 18 = btCurTagBase tbl slotCap eCap ∧ st.regs 19 = i ∧
    h2 ≤ hCur ∧ hCur ≤ h2 + listSpacePref i ∧
    ZeroFrom st.mem hCur ∧
    htour.rep.rep tourH cord tx st.mem ∧
    (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (h2 ≤ a ∧ a < hCur)) ∧
    (∀ q (hq : q < specs.length),
      InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
        (btCurTagBase tbl slotCap eCap) cord rList i 0 specs[q].1
        (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) st.mem) ∧
    (∀ a, a < h → ¬ htour.rep.foot tourH tx₀ a →
      (∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
        a ≠ btEndBundleBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndNextBase tbl slotCap eCap + endKey x) →
      (∀ s ∈ specs.map Prod.fst,
        a ≠ btCurBunBase tbl slotCap eCap + s ∧
        a ≠ btCurTagBase tbl slotCap eCap + s) →
      st.mem a = mem₀ a)
  have htake_sp : ∀ i, listSpacePref i ≤ (rList.map fun v => TS.listSpace (cord v).length).sum := by
    intro i
    change ((rList.take i).map _).sum ≤ _
    conv_rhs => rw [← List.take_append_drop i rList, List.map_append, List.sum_append]
    omega
  have hsp_step : ∀ i (hi : i < rList.length),
      listSpacePref (i + 1) = listSpacePref i + TS.listSpace (cord rList[i]).length := by
    intro i hi
    simp only [listSpacePref, List.take_succ_eq_append_getElem hi, List.map_append,
      List.map_singleton, List.sum_append, List.sum_singleton]
  have hend_lt_2e : ∀ y : End, (∃ s ∈ specs.map Prod.fst, y.1 ∈ slotEdgesOf assigns s) →
      endKey y < 2 * eCap := by
    rintro ⟨ee, side⟩ ⟨s, _, he⟩
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at he
    rcases he with ⟨p, ⟨hp, _⟩, rfl⟩
    have := (hassigns_in p hp).1
    cases side <;> simp [endKey] <;> omega
  have hblk_end : ∀ q (hq : q < specs.length),
      slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 ≤ slotBlocksSpace specs := by
    intro q hq
    have h1 : slotBlocksSpace (specs.take (q + 1)) =
        slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 := by
      simp only [slotBlocksSpace]
      rw [List.take_succ_eq_append_getElem hq, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton]
    rw [← h1]
    have hsp := List.take_append_drop (q + 1) specs
    have : slotBlocksSpace specs = slotBlocksSpace (specs.take (q + 1)) +
        slotBlocksSpace (specs.drop (q + 1)) := by
      conv_lhs => rw [← hsp]
      simp only [slotBlocksSpace, List.map_append, List.sum_append]
    omega
  let stepCost : ℕ → ℕ := fun i =>
    (TS.mul * ordStoreLog eCap + 220) * ((cord (rList.getD i 0)).length + 1) + 35
  obtain ⟨st', c, ⟨hEnd, tx'⟩, hrun, hInvEnd, hcost⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 19) (lo := .const 0) (hi := .reg 7)
      (phi := fun a st => htour.rep.phi tourH a.2 st.mem) (Inv := Inv) (stepCost := stepCost)
      nR (by omega) (fun _ => by unfold bundleInitSlotsSpace at hspace_w; omega)
      (st₀ := st₀) (a₀ := (h2, tx₀))
      (by
        rcases hst0 with ⟨hm, hc, r10, r17, r18⟩
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        refine ⟨hc.upd (by omega), by simp [r10, h2], by simp [r17], by simp [r18], by simp,
          le_rfl, by simp [listSpacePref], by rw [hm]; exact hzero, by rw [hm]; exact htour_rep,
          fun a ha => Or.inl ha, fun q hq => by rw [hm]; exact hinit0 q hq,
          fun a _ _ _ _ => by rw [hm]⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.1)
      (fun _ _ st _ hI => by
        simp [Expr.eval, hI.1.2.2.2.2.2.2.2.1])
      (fun i ⟨hCur, tx⟩ st hi hI => by
        rcases hI with ⟨hc, r10, r17, r18, r19, hh2_le, hCur_le, hzeroCur, htrep, htfoot,
          hslots, hfr⟩
        have hi_len : i < rList.length := by omega
        set v := rList[i]'hi_len
        have hv_lt := hrList_lt v (List.getElem_mem hi_len)
        have hv_getD : rList.getD i 0 = v := List.getD_eq_getElem _ _ hi_len
        have hCur_sp_lt : hCur + TS.listSpace (cord v).length < 2 ^ w := by
          have h1 : listSpacePref (i + 1) = listSpacePref i + TS.listSpace (cord v).length :=
            hsp_step i hi_len
          have h2le := htake_sp (i + 1)
          unfold bundleInitSlotsSpace at hspace_w; omega
        have hmem_v : st.mem (rPtr + i) = v := by
          rw [hfr _ (by omega) (fun hf => by have := htour_foot_disj_r _ hf; omega)
            (fun y hy => by
              have := hend_lt_2e y hy
              unfold btEndBundleBase btEndPrevBase btEndNextBase bundleTableFixedSize at *; omega)
            (fun s hs => by
              obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
              unfold btCurBunBase btCurTagBase bundleTableFixedSize at *; exact ⟨by omega, by omega⟩)]
          exact hrList_mem i hi_len
        have hr8 : st.regs 8 = rPtr := hc.2.2.2.2.2.2.2.2.1
        have hr1 : st.regs 1 = tourH := hc.2.1
        -- Step 1: v := mem (rPtr + i)
        set st1 : State := { st with regs := Function.update st.regs 20 v }
        have hassign_v : Runs w pProg ω (.assign 20 (.load (.bin .add (.reg 8) (.reg 19))))
            st .normal st1 5 := by
          refine runs_assign_iff.mpr ⟨v, ?_, rfl, rfl, rfl⟩
          simp [Expr.eval, BinOp.eval, hr8, r19, hmem_v,
            show rPtr + i < 2 ^ w by unfold bundleInitSlotsSpace at hspace_w; omega]
        -- Step 2: call bTourList [tourH, v, hCur]
        have htfoot_lt : ∀ a, htour.rep.foot tourH tx a → a < hCur := fun a ha => by
          rcases htfoot a ha with h0 | ⟨_, hlt⟩
          · have := htour_foot_lt a h0; omega
          · exact hlt
        obtain ⟨bodyL, hbodyL, oL, stL, cL, tx1, hrunL, htrep1, hendL, hhNext_ge, hrespL, hcostL⟩ :=
          htour.list_runs tourH v hCur cord tx st.mem st1.pos ω htourH_w hv_lt.1 hv_lt.2
            (by omega) htrep htfoot_lt hzeroCur hCur_sp_lt
        set hNext := oL.value
        have hhNext_le : hNext ≤ hCur + TS.listSpace (cord v).length := hrespL.2.1
        have hhNext_w : hNext < 2 ^ w := by omega
        set st2 : State := { mem := stL.mem, regs := Function.update st1.regs 21 hNext, pos := stL.pos }
        have hcall_L : Runs w pProg ω (.call 21 bTourList [.reg 1, .reg 20, .reg 10])
            st1 .normal st2 (cL + 4) := by
          have hargs : evalArgs w st1 [.reg 1, .reg 20, .reg 10] = some [tourH, v, hCur] := by
            simp [evalArgs, Expr.eval, st1, hr1, r10]
          have hcall : Runs w pProg ω (.call 21 bTourList [.reg 1, .reg 20, .reg 10]) st1 .normal
              { mem := stL.mem, regs := Function.update st1.regs 21 oL.value, pos := stL.pos }
              (argsSize [.reg 1, .reg 20, .reg 10] + cL + 1) :=
            runs_call_iff.mpr ⟨[tourH, v, hCur], bodyL, oL, stL, cL, hargs, hbodyL, hrunL, rfl, rfl, rfl⟩
          simpa [argsSize, Expr.size, st2, hNext, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcall
        -- Preserve stL.mem = st.mem outside tour foot and < hCur
        have hstL_eq_st : ∀ a, a < hCur → ¬ htour.rep.foot tourH tx a → stL.mem a = st.mem a :=
          fun a ha hnf => hrespL.2.2.2.1 a ha hnf
        have hstL_eq_st_tbl : ∀ a, tbl ≤ a → a < tbl + bundleTableFixedSize slotCap eCap →
            stL.mem a = st.mem a := fun a ha1 ha2 =>
          hstL_eq_st a (by omega) fun hf => by
            rcases htfoot a hf with h0 | ⟨hge, _⟩
            · have := htour_foot_disj_tbl a h0; omega
            · omega
        have hstL_eq_st_h2 : ∀ a, h ≤ a → a < h2 → stL.mem a = st.mem a := fun a ha1 ha2 =>
          hstL_eq_st a (by omega) fun hf => by
            rcases htfoot a hf with h0 | ⟨hge, _⟩
            · have := htour_foot_lt a h0; omega
            · omega
        have hstL_eq_mem0 : ∀ a, a < h → ¬ htour.rep.foot tourH tx₀ a →
            (∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
              a ≠ btEndBundleBase tbl slotCap eCap + endKey x ∧
              a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
              a ≠ btEndNextBase tbl slotCap eCap + endKey x) →
            (∀ s ∈ specs.map Prod.fst,
              a ≠ btCurBunBase tbl slotCap eCap + s ∧
              a ≠ btCurTagBase tbl slotCap eCap + s) →
            stL.mem a = mem₀ a := fun a ha hnf hne hne_cur => by
          rw [hstL_eq_st a (by omega) (fun hf => by
            rcases htfoot a hf with h0 | ⟨hge, _⟩
            · exact hnf h0
            · omega)]
          exact hfr a ha hnf hne hne_cur
        -- Step 3: len := mem hCur = (cord v).length
        set st3 : State := { st2 with regs := Function.update st2.regs 22 (cord v).length }
        have hassign_len : Runs w pProg ω (.assign 22 (.load (.reg 10))) st2 .normal st3 3 := by
          refine runs_assign_iff.mpr ⟨(cord v).length, ?_, rfl, rfl, rfl⟩
          simp [Expr.eval, st2, st1, r10, hendL.1]
        -- Step 4: inner loop `bundleInitInner_triple`
        have hinner := bundleInitInner_triple (w := w) (slotCap := slotCap) (eCap := eCap)
          (tbl := tbl) (tourH := tourH) (k := k) (nSlots := nSlots) (slotSpecPtr := slotSpecPtr)
          (nEdges := nEdges) (edgeAssignPtr := edgeAssignPtr) (nR := nR) (rPtr := rPtr) (h := h)
          (hCur := hCur) (hNext := hNext) (i := i) (pProg := pProg) (bDllPush := bDllPush)
          (mem₀ := stL.mem) (specs := specs) (assigns := assigns) (cord := cord) (rList := rList)
          hbPush hw16 hk1 htbl_h hh2_le (hv_getD ▸ hhNext_ge) hhNext_w hi_len hrList_nd
          (by unfold bundleInitSlotsSpace at hspace_w; omega) hspecs_lt hspecs_nd hspecs_cap
          hcord_nd hcord_disj (hv_getD ▸ hcord_lt v (List.getElem_mem hi_len)) hassigns_in
          hassigns_nd (hv_getD ▸ hendL)
          (fun q hq => by
            have hs_lt := hspecs_lt specs[q] (List.getElem_mem hq)
            rw [hstL_eq_st_tbl _ (by unfold btSlotPtrBase; omega)
              (by unfold btSlotPtrBase bundleTableFixedSize; omega),
              hfr _ (by unfold btSlotPtrBase bundleTableFixedSize at *; omega)
                (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btSlotPtrBase bundleTableFixedSize at *; omega)
                (fun y hy => by have := hend_lt_2e y hy; unfold btSlotPtrBase btEndBundleBase btEndPrevBase btEndNextBase; omega)
                (fun s hs => by obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb; unfold btSlotPtrBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
            exact hslotPtr q hq)
          (fun s hs => by
            obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs
            have hs_lt := hspecs_lt sb hsb
            rw [hstL_eq_st_tbl _ (by unfold btSlotTouchedBase; omega)
              (by unfold btSlotTouchedBase bundleTableFixedSize; omega),
              hfr _ (by unfold btSlotTouchedBase bundleTableFixedSize at *; omega)
                (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btSlotTouchedBase bundleTableFixedSize at *; omega)
                (fun y hy => by have := hend_lt_2e y hy; unfold btSlotTouchedBase btEndBundleBase btEndPrevBase btEndNextBase; omega)
                (fun s' hs' => by obtain ⟨sb', hsb', rfl⟩ := List.mem_map.mp hs'; have := hspecs_lt sb' hsb'; unfold btSlotTouchedBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
            exact htouched_in sb.1 hs)
          (fun s hs hnot => by
            rw [hstL_eq_st_tbl _ (by unfold btSlotTouchedBase; omega)
              (by unfold btSlotTouchedBase bundleTableFixedSize; omega),
              hfr _ (by unfold btSlotTouchedBase bundleTableFixedSize at *; omega)
                (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btSlotTouchedBase bundleTableFixedSize at *; omega)
                (fun y hy => by have := hend_lt_2e y hy; unfold btSlotTouchedBase btEndBundleBase btEndPrevBase btEndNextBase; omega)
                (fun s' hs' => by obtain ⟨sb', hsb', rfl⟩ := List.mem_map.mp hs'; have := hspecs_lt sb' hsb'; unfold btSlotTouchedBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
            exact htouched_out s hs hnot)
          (fun e he s hs hes => by
            rw [hstL_eq_st_tbl _ (by unfold btEdgeSlotBase; omega)
              (by unfold btEdgeSlotBase bundleTableFixedSize; omega),
              hfr _ (by unfold btEdgeSlotBase bundleTableFixedSize at *; omega)
                (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btEdgeSlotBase bundleTableFixedSize at *; omega)
                (fun y hy => by have := hend_lt_2e y hy; unfold btEdgeSlotBase btEndBundleBase btEndPrevBase btEndNextBase; omega)
                (fun s' hs' => by obtain ⟨sb', hsb', rfl⟩ := List.mem_map.mp hs'; have := hspecs_lt sb' hsb'; unfold btEdgeSlotBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
            exact hedgeSlot_in e he s hs hes)
          (fun e he hnot => by
            rw [hstL_eq_st_tbl _ (by unfold btEdgeSlotBase; omega)
              (by unfold btEdgeSlotBase bundleTableFixedSize; omega),
              hfr _ (by unfold btEdgeSlotBase bundleTableFixedSize at *; omega)
                (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btEdgeSlotBase bundleTableFixedSize at *; omega)
                (fun y hy => by have := hend_lt_2e y hy; unfold btEdgeSlotBase btEndBundleBase btEndPrevBase btEndNextBase; omega)
                (fun s' hs' => by obtain ⟨sb', hsb', rfl⟩ := List.mem_map.mp hs'; have := hspecs_lt sb' hsb'; unfold btEdgeSlotBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
            exact hedgeSlot_out e he hnot)
          (fun q hq => by
            have hq_end := hblk_end q hq
            have hs_lt := hspecs_lt specs[q] (List.getElem_mem hq)
            have hsq_mem : specs[q].1 ∈ specs.map Prod.fst :=
              List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩
            exact (hslots q hq).of_agree hk1
              (fun a ha1 ha2 => (hstL_eq_st_h2 a (by omega) (by omega)).symm)
              (fun key hkey => (hstL_eq_st_tbl _ (by unfold btEndPrevBase; omega) (by
                have := hend_lt_2e (endOfKey key) ⟨specs[q].1, hsq_mem, hkey⟩
                rw [bundle_endKey_endOfKey] at this
                unfold btEndPrevBase bundleTableFixedSize; omega)).symm)
              (fun key hkey => (hstL_eq_st_tbl _ (by unfold btEndNextBase; omega) (by
                have := hend_lt_2e (endOfKey key) ⟨specs[q].1, hsq_mem, hkey⟩
                rw [bundle_endKey_endOfKey] at this
                unfold btEndNextBase bundleTableFixedSize; omega)).symm)
              (fun x hx => (hstL_eq_st_tbl _ (by unfold btEndBundleBase; omega) (by
                have := hend_lt_2e x ⟨specs[q].1, hsq_mem, hx⟩
                unfold btEndBundleBase bundleTableFixedSize; omega)).symm)
              (hstL_eq_st_tbl _ (by unfold btCurBunBase; omega)
                (by unfold btCurBunBase bundleTableFixedSize; omega)).symm
              (hstL_eq_st_tbl _ (by unfold btCurTagBase; omega)
                (by unfold btCurTagBase bundleTableFixedSize; omega)).symm)
        obtain ⟨o4, st4, c4, hrun4, hpost4, hcost4⟩ := hinner st3 ω
          ⟨rfl, ((hc.upd (by omega)).upd (by omega)).upd (by omega), by simp [st3, st2, st1, r10],
            by simp [st3, st2, st1, r17], by simp [st3, st2, st1, r18], by simp [st3, st2, st1, r19],
            by simp [st3, st2], by dsimp only [st3]; rw [Function.update_self, hv_getD]⟩
        cases o4 with
        | returned u => exact False.elim hpost4
        | normal =>
          rcases hpost4 with ⟨hc4, _, r17_4, r18_4, r19_4, r21_4, _, _, hslots4, hfr4⟩
          -- Step 5: r 10 := hNext
          set st5 : State := { st4 with regs := Function.update st4.regs 10 hNext }
          have hassign_h : Runs w pProg ω (.assign 10 (.reg 21)) st4 .normal st5 2 := by
            refine runs_assign_iff.mpr ⟨hNext, ?_, rfl, rfl, rfl⟩
            simp [Expr.eval, r21_4]
          have hrun_body : Runs w pProg ω
              (.assign 20 (.load (.bin .add (.reg 8) (.reg 19))) ;;
               .call 21 bTourList [.reg 1, .reg 20, .reg 10] ;;
               .assign 22 (.load (.reg 10)) ;;
               forRange 23 (.const 0) (.reg 22) (bundleInitEndBody bDllPush) ;;
               .assign 10 (.reg 21)) st .normal st5 (5 + ((cL + 4) + (3 + (c4 + 2 + 1) + 1) + 1) + 1) :=
            bundle_runs_seq_normal hassign_v
              (bundle_runs_seq_normal hcall_L
                (bundle_runs_seq_normal hassign_len
                  (bundle_runs_seq_normal hrun4 hassign_h)))
          have htfoot1 : ∀ a, htour.rep.foot tourH tx1 a →
              htour.rep.foot tourH tx₀ a ∨ (h2 ≤ a ∧ a < hNext) := fun a ha => by
            rcases hrespL.2.2.2.2 a ha with hprev | ⟨hge, hlt⟩
            · rcases htfoot a hprev with h0 | ⟨hge0, hlt0⟩
              · exact Or.inl h0
              · exact Or.inr ⟨hge0, by omega⟩
            · exact Or.inr ⟨by omega, hlt⟩
          have hagree_tour : ∀ a, htour.rep.foot tourH tx1 a → st4.mem a = stL.mem a := fun a ha => by
            rcases htfoot1 a ha with h0 | ⟨hge, _⟩
            · exact hfr4 a (Or.inl (htour_foot_lt a h0)) (fun y hy => by
                have := hend_lt_2e y hy
                have := htour_foot_disj_tbl a h0
                unfold btEndBundleBase btEndPrevBase btEndNextBase bundleTableFixedSize at *; omega)
                (fun s hs => by
                  obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
                  have := htour_foot_disj_tbl a h0
                  unfold btCurBunBase btCurTagBase bundleTableFixedSize at *; exact ⟨by omega, by omega⟩)
            · exact hfr4 a (Or.inr hge) (fun y hy => by
                have := hend_lt_2e y hy
                unfold btEndBundleBase btEndPrevBase btEndNextBase bundleTableFixedSize at *; omega)
                (fun s hs => by
                  obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
                  unfold btCurBunBase btCurTagBase bundleTableFixedSize at *; exact ⟨by omega, by omega⟩)
          have hloc4 := htour.rep_local tourH cord tx1 stL.mem st4.mem
            (fun a ha => (hagree_tour a ha).symm)
          have htrep4 : htour.rep.rep tourH cord tx1 st4.mem := hloc4.1 htrep1
          have hphi4 : htour.rep.phi tourH tx1 st4.mem = htour.rep.phi tourH tx1 stL.mem :=
            hloc4.2.symm
          refine ⟨st5, _, (hNext, tx1), hrun_body, by simp [st5, r19_4], ?_, rfl, ?_⟩
          · refine ⟨(hc4.upd (by omega)).upd (by omega), by simp [st5], by simp [st5, r17_4],
              by simp [st5, r18_4], by simp [st5], by omega,
              by have h1 : listSpacePref (i + 1) = listSpacePref i + TS.listSpace (cord v).length :=
                   hsp_step i hi_len
                 omega,
              fun a ha => by
                rw [hfr4 a (Or.inr (by omega)) (fun y hy => by
                  have := hend_lt_2e y hy
                  unfold btEndBundleBase btEndPrevBase btEndNextBase bundleTableFixedSize at *; omega)
                  (fun s hs => by
                    obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
                    unfold btCurBunBase btCurTagBase bundleTableFixedSize at *; exact ⟨by omega, by omega⟩)]
                exact hrespL.2.2.1 a ha,
              htrep4, htfoot1, ?_, ?_⟩
            · intro q hq
              have hq4 := hslots4 q hq
              have hmid_eq : initMidSlots cord (rList.take i) (rList.getD i 0)
                  (cord (rList.getD i 0)).length (slotEdgesOf assigns specs[q].1) k =
                  initMidSlots cord (rList.take (i + 1)) (rList.getD (i + 1) 0) 0
                    (slotEdgesOf assigns specs[q].1) k := by
                rw [hv_getD, initMidSlots_full cord rList hi_len, initMidSlots_zero]
              rcases hq4 with ⟨c1, c2, c3, c4', c5, c6, c7, c8, c9, c10⟩
              refine ⟨hmid_eq ▸ c1, c2, hmid_eq ▸ c3, c4', hmid_eq ▸ c5, hmid_eq ▸ c6, c7,
                hmid_eq ▸ c8, fun _ => ?_, fun hne => by simp at hne⟩
              dsimp only [st5]
              by_cases hcur0 : (((cord (rList.getD i 0)).take (cord (rList.getD i 0)).length).filter
                  fun x => decide (x.1 ∈ slotEdgesOf assigns specs[q].1)) = []
              · have := c9 hcur0; omega
              · have := (c10 hcur0).1; omega
            · intro a ha hnf hne hne_cur
              rw [hfr4 a (Or.inl ha) hne hne_cur, hstL_eq_mem0 a ha hnf hne hne_cur]
          · dsimp only [st5, stepCost]
            rw [hphi4, hv_getD]
            have hmul : TS.mul * ((cord v).length + 1) * ordStoreLog eCap + 220 * ((cord v).length + 1) =
                (TS.mul * ordStoreLog eCap + 220) * ((cord v).length + 1) := by ring
            have h4 : c4 ≤ (cord v).length * 215 + 15 := by rw [hv_getD] at hcost4; exact hcost4
            omega)
  rcases hInvEnd with ⟨hc', r10', r17', r18', _, hh2_le, hEnd_le, hzero', htrep', htfoot', hslots', hfr'⟩
  have hrc : rangeCost stepCost 0 nR =
      (rList.map fun v => (TS.mul * ordStoreLog eCap + 220) * ((cord v).length + 1)).sum + 35 * nR := by
    rw [rangeCost_zero_eq_range]
    have haux : ∀ (l : List ℕ),
        ((List.range l.length).map fun i => (TS.mul * ordStoreLog eCap + 220) * ((cord (l.getD i 0)).length + 1) + 35).sum =
        (l.map fun v => (TS.mul * ordStoreLog eCap + 220) * ((cord v).length + 1)).sum + 35 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a tl ih =>
        rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
        have htl : ((List.range tl.length).map ((fun i =>
            (TS.mul * ordStoreLog eCap + 220) * ((cord ((a :: tl).getD i 0)).length + 1) + 35) ∘ Nat.succ)).sum =
            ((List.range tl.length).map fun i =>
              (TS.mul * ordStoreLog eCap + 220) * ((cord (tl.getD i 0)).length + 1) + 35).sum := rfl
        rw [htl, ih]; simp [Nat.mul_add]; omega
    simpa [stepCost, hnR] using haux rList
  refine ⟨st', c, hEnd, tx', hrun, hc', r10', r17', r18', hh2_le, ?_, hzero', htrep', htfoot', hslots', hfr', ?_⟩
  · have := htake_sp nR
    unfold bundleInitSlotsSpace; omega
  · rw [hrc, hst0.1] at hcost
    simp only [Expr.size_reg, Expr.size_const] at hcost
    omega

end

end MinCostFlow.SparseCore.Program
