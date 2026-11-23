module

public import MinCostFlow.SparseCore.Program.BundleInitStep

import WordRAM.Tactic

/-!
# Inner tour-end loop verification for bundle initialization (`BundleInitInner`)

Verifies `bundleInitInner_triple`, the inner `forRange 23 (.const 0) (.reg 22)
(bundleInitEndBody bDllPush)` loop of `bundleInitSlotsStmt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Extracts the pre-push doubly linked list `L` for chunk `bun` after `bundleInitChooseBun_triple`. -/
private lemma bundleInitInner_hL_ex {slotCap eCap tbl k h i t s p cap bun key : ℕ}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    {st st1 : State}
    (hk1 : 1 ≤ k) (htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h)
    (hi : i < rList.length) (hv_eq : rList.getD i 0 = rList[i])
    (ht : t < (cord (rList.getD i 0)).length) (ht_r : t < (cord rList[i]).length)
    (hkey_eq : key = endKey ((cord (rList.getD i 0))[t]'ht))
    (hp_blk : p + (3 + 6 * cap) ≤ h + slotBlocksSpace specs) (hp_ge : h ≤ p)
    (hs_lt : s < slotCap)
    (hbun_eq_def : bun =
      if (((cord rList[i]).take t).filter fun y => decide (y.1 ∈ slotEdgesOf assigns s)).length % k = 0
      then (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length
      else (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length - 1)
    (hbun_lt_cap : bun < cap)
    (hpos_of_ne : (((cord rList[i]).take t).filter fun y => decide (y.1 ∈ slotEdgesOf assigns s)) ≠ [] →
      0 < (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length)
    (hfresh : ∀ b (hb : b < (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length),
      (cord rList[i])[t]'ht_r ∉ (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k)[b].2)
    (hIq : InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
      (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
      (btCurTagBase tbl slotCap eCap) cord rList i t s p cap k (slotEdgesOf assigns s) st.mem)
    (hfr1 : ∀ a, a ≠ p + bsOffNB → a ≠ btCurTagBase tbl slotCap eCap + s →
      a ≠ btCurBunBase tbl slotCap eCap + s → st1.mem a = st.mem a) :
    let E_q := slotEdgesOf assigns s
    let curEnds := ((cord rList[i]).take t).filter fun y => decide (y.1 ∈ E_q)
    let oldChunks := initMidSlots cord (rList.take i) rList[i] t E_q k
    ∃ L : List ℕ,
      IsDoublyLinkedList st1.mem (btEndPrevBase tbl slotCap eCap)
        (btEndNextBase tbl slotCap eCap) (bsHeadBase p + bun) (2 * eCap) L ∧
      st1.mem (bsSizeBase p cap + bun) = L.length ∧
      key ∉ L ∧ L.length + 1 ≤ k ∧
      (curEnds.length % k = 0 → L = []) ∧
      (∀ key', key' ∈ L ↔
        ∃ hlt : bun < oldChunks.length, endOfKey key' ∈ oldChunks[bun].2) := by
  intro E_q curEnds oldChunks
  have hx_eq : (cord (rList.getD i 0))[t]'ht = (cord rList[i])[t]'ht_r := by simp only [hv_eq]
  have hIq' : InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (btEndBundleBase tbl slotCap eCap)
      (btCurBunBase tbl slotCap eCap) (btCurTagBase tbl slotCap eCap) cord rList i t s p
      cap k E_q st.mem := hIq
  simp only [InitScanSlotInv, List.getD_eq_getElem _ _ hi] at hIq'
  have hhead_fr : bsHeadBase p + bun ≠ p + bsOffNB ∧
      bsHeadBase p + bun ≠ btCurTagBase tbl slotCap eCap + s ∧
      bsHeadBase p + bun ≠ btCurBunBase tbl slotCap eCap + s := by
    unfold bsHeadBase bsOffNB btCurTagBase btCurBunBase; clear * - htbl_h' hp_ge hs_lt; omega
  have hsz_fr : bsSizeBase p cap + bun ≠ p + bsOffNB ∧
      bsSizeBase p cap + bun ≠ btCurTagBase tbl slotCap eCap + s ∧
      bsSizeBase p cap + bun ≠ btCurBunBase tbl slotCap eCap + s := by
    unfold bsSizeBase bsOffNB btCurTagBase btCurBunBase; clear * - htbl_h' hp_ge hs_lt; omega
  by_cases hmod : curEnds.length % k = 0
  · have hbun_eq : bun = oldChunks.length := by rw [hbun_eq_def]; simp only [E_q, curEnds, oldChunks, hmod, ↓reduceIte]
    have htail_q := hIq'.2.2.2.2.2.1 bun (by rw [hbun_eq]) hbun_lt_cap
    refine ⟨[], ?_, ?_, by simp, by clear * - hk1; omega, fun _ => rfl, fun key' => by simp [hbun_eq]⟩
    · refine ⟨List.nodup_nil, (fun _ h => by simp at h), ?_, (fun _ h => by cases h)⟩
      rw [hfr1 _ hhead_fr.1 hhead_fr.2.1 hhead_fr.2.2]
      exact htail_q.1
    · rw [hfr1 _ hsz_fr.1 hsz_fr.2.1 hsz_fr.2.2]
      exact htail_q.2.1
  · have hbun_eq : bun = oldChunks.length - 1 := by
      rw [hbun_eq_def]; dsimp only [E_q, curEnds, oldChunks] at hmod ⊢; simp only [hmod, ↓reduceIte]
    have hne : curEnds ≠ [] := fun h0 => hmod (by simp [h0])
    have hpos_old := hpos_of_ne hne
    have hbun_lt : bun < oldChunks.length := by
      dsimp only [oldChunks, E_q] at hbun_eq ⊢; clear * - hbun_eq hpos_old; omega
    obtain ⟨L, hL, hsz, hlenL, hmemL⟩ := hIq'.2.2.2.2.1 bun hbun_lt
    have hlast_len_lt : oldChunks[bun].2.length < k := by
      have hch_pos : 0 < (initialChunks k curEnds).length := by
        rw [initialChunks_length_eq]
        exact Nat.div_pos (by have := List.length_pos_of_ne_nil hne; clear * - this hk1; omega) hk1
      have hlast_eq : oldChunks[bun].2 =
          (initialChunks k curEnds)[(initialChunks k curEnds).length - 1]'(by
            clear * - hch_pos; omega) := by
        simp only [oldChunks, initMidSlots, hbun_eq, List.length_append, List.length_map]
        rw [List.getElem_append_right (by dsimp only [curEnds] at hch_pos; clear * - hch_pos; omega),
          List.getElem_map]
        dsimp only; congr 1
        dsimp only [curEnds] at hch_pos ⊢; clear * - hch_pos; omega
      have hle_k : oldChunks[bun].2.length ≤ k := by
        rw [hlast_eq, initialChunks_getElem_length]; exact Nat.min_le_left _ _
      have hne_k : oldChunks[bun].2.length ≠ k := by
        rw [hlast_eq]
        exact fun h => hmod ((last_initialChunk_length_eq_k_iff hk1 hne).mp h)
      clear * - hle_k hne_k; omega
    have hlenL' : L.length = oldChunks[bun].2.length := hlenL
    refine ⟨L, hL.of_agree ?_ ?_ ?_, ?_, ?_, by clear * - hlenL' hlast_len_lt; omega,
        fun h => absurd h hmod, fun key' => ?_⟩
    · exact hfr1 _ hhead_fr.1 hhead_fr.2.1 hhead_fr.2.2
    · intro k' hk'
      have hk'_lt := hL.2.1 k' hk'
      exact hfr1 _
        (by unfold btEndPrevBase bsOffNB; clear * - htbl_h' hp_ge hk'_lt; omega)
        (by unfold btEndPrevBase btCurTagBase; clear * - hk'_lt; omega)
        (by unfold btEndPrevBase btCurBunBase; clear * - hk'_lt; omega)
    · intro k' hk'
      have hk'_lt := hL.2.1 k' hk'
      exact hfr1 _
        (by unfold btEndNextBase bsOffNB; clear * - htbl_h' hp_ge hk'_lt; omega)
        (by unfold btEndNextBase btCurTagBase; clear * - hk'_lt; omega)
        (by unfold btEndNextBase btCurBunBase; clear * - hk'_lt; omega)
    · rw [hfr1 _ hsz_fr.1 hsz_fr.2.1 hsz_fr.2.2]
      exact hsz
    · intro hkin
      have hxin := (hmemL key).mp hkin
      rw [show endOfKey key = (cord rList[i])[t]'ht_r by rw [hkey_eq, bundle_endOfKey_endKey, hx_eq]] at hxin
      exact hfresh bun hbun_lt hxin
    · rw [hmemL key']; exact ⟨fun h => ⟨hbun_lt, h⟩, fun ⟨_, h⟩ => h⟩

/-- Full verification of the inner tour-end scan loop `forRange 23 (.const 0) (.reg 22)
(bundleInitEndBody bDllPush)` at core vertex `v = rList[i]`. -/
theorem bundleInitInner_triple {w slotCap eCap tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr
    nR rPtr h hCur hNext i : ℕ}
    {pProg : Program} {bDllPush : ℕ} {mem₀ : ℕ → ℕ}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hbPush : ∀ prevBase nextBase headAddr key L,
      MeetsContract w pProg bDllPush
        (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hw16 : 16 ≤ 2 ^ w)
    (hk1 : 1 ≤ k)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hh_cur : h + slotBlocksSpace specs ≤ hCur)
    (hh_next : hCur + 1 + (cord (rList.getD i 0)).length ≤ hNext)
    (hh_next_w : hNext < 2 ^ w)
    (hi : i < rList.length)
    (hrList_nd : rList.Nodup)
    (hrList_w : rList.length < 2 ^ w)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap)
    (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_cap : ∀ sb ∈ specs,
      (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k).length ≤ sb.2)
    (hcord_nd : ∀ w' ∈ rList, (cord w').Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hcord_lt : ∀ x ∈ cord (rList.getD i 0), x.1 < eCap)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hendList : EndListAt mem₀ hCur (cord (rList.getD i 0)))
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
        (btCurTagBase tbl slotCap eCap) cord rList i 0 specs[q].1
        (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) mem₀) :
    let v := rList.getD i 0
    let len := (cord v).length
    let Inv : ℕ → State → Prop := fun t st =>
      BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
        slotCap eCap ∧
      st.regs 10 = hCur ∧ st.regs 17 = btCurBunBase tbl slotCap eCap ∧
      st.regs 18 = btCurTagBase tbl slotCap eCap ∧ st.regs 19 = i ∧
      st.regs 21 = hNext ∧ st.regs 22 = len ∧ st.regs 23 = t ∧
      (∀ q (hq : q < specs.length),
        InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
          (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
          (btCurTagBase tbl slotCap eCap) cord rList i t specs[q].1
          (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) st.mem) ∧
      (∀ a,
        (a < h ∨ h + slotBlocksSpace specs ≤ a) →
        (∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
          a ≠ btEndBundleBase tbl slotCap eCap + endKey x ∧
          a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
          a ≠ btEndNextBase tbl slotCap eCap + endKey x) →
        (∀ s ∈ specs.map Prod.fst,
          a ≠ btCurBunBase tbl slotCap eCap + s ∧
          a ≠ btCurTagBase tbl slotCap eCap + s) →
        st.mem a = mem₀ a)
    Triple w pProg
      (fun st => st.mem = mem₀ ∧
        BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
          slotCap eCap ∧
        st.regs 10 = hCur ∧ st.regs 17 = btCurBunBase tbl slotCap eCap ∧
        st.regs 18 = btCurTagBase tbl slotCap eCap ∧ st.regs 19 = i ∧
        st.regs 21 = hNext ∧ st.regs 22 = len)
      (forRange 23 (.const 0) (.reg 22) (bundleInitEndBody bDllPush))
      (normalPost (Inv len))
      (fun _ => len * 215 + 15) := by
  intro v len Inv
  have hv_eq : v = rList[i] := List.getD_eq_getElem _ _ hi
  have htake_le : ∀ q ≤ specs.length, slotBlocksSpace (specs.take q) ≤ slotBlocksSpace specs := by
    intro q _
    have hsp := List.take_append_drop q specs
    have : slotBlocksSpace specs = slotBlocksSpace (specs.take q) + slotBlocksSpace (specs.drop q) := by
      conv_lhs => rw [← hsp]
      simp [slotBlocksSpace]
    omega
  have hblk_end : ∀ q (hq : q < specs.length),
      slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 ≤ slotBlocksSpace specs := by
    intro q hq
    have h1 : slotBlocksSpace (specs.take (q + 1)) =
        slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 := by
      simp only [slotBlocksSpace]
      rw [List.take_succ_eq_append_getElem hq, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton]
    rw [← h1]; exact htake_le (q + 1) (by omega)
  have hblk_disj : ∀ q₁ q₂ (hq₁ : q₁ < specs.length) (hq₂ : q₂ < specs.length), q₁ ≠ q₂ →
      (h + slotBlocksSpace (specs.take q₁)) + bundleSlotBlockSize specs[q₁].2 ≤
        h + slotBlocksSpace (specs.take q₂) ∨
      (h + slotBlocksSpace (specs.take q₂)) + bundleSlotBlockSize specs[q₂].2 ≤
        h + slotBlocksSpace (specs.take q₁) := by
    have hstep : ∀ a b (hab : a < b) (hb : b ≤ specs.length),
        slotBlocksSpace (specs.take a) + bundleSlotBlockSize (specs[a]'(by omega)).2 ≤
          slotBlocksSpace (specs.take b) := by
      intro a b hab hb
      have h1 : slotBlocksSpace (specs.take (a + 1)) =
          slotBlocksSpace (specs.take a) + bundleSlotBlockSize (specs[a]'(by omega)).2 := by
        simp only [slotBlocksSpace]
        rw [List.take_succ_eq_append_getElem (by omega : a < specs.length), List.map_append,
          List.map_singleton, List.sum_append, List.sum_singleton]
      rw [← h1]
      have h2 : specs.take b = specs.take (a + 1) ++ (specs.drop (a + 1)).take (b - (a + 1)) := by
        rw [← List.take_append_drop (a + 1) (specs.take b), List.take_take,
          Nat.min_eq_left (by omega), List.drop_take]
      rw [h2]; simp [slotBlocksSpace, List.map_append, List.sum_append]
    intro q₁ q₂ hq₁ hq₂ hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · left; have := hstep q₁ q₂ hlt (by omega); omega
    · right; have := hstep q₂ q₁ hgt (by omega); omega
  have hdisj_slotE : ∀ s₁ s₂, s₁ ≠ s₂ → ∀ e,
      e ∈ slotEdgesOf assigns s₁ → e ∉ slotEdgesOf assigns s₂ := by
    intro s₁ s₂ hne e h1 h2
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at h1 h2
    rcases h1 with ⟨⟨e₁, s₁'⟩, ⟨hmem1, hs1⟩, rfl⟩
    rcases h2 with ⟨⟨e₂, s₂'⟩, ⟨hmem2, hs2⟩, he2⟩
    dsimp only at hs1 hs2 he2
    obtain ⟨idx1, hidx1, heq1⟩ := List.getElem_of_mem hmem1
    obtain ⟨idx2, hidx2, heq2⟩ := List.getElem_of_mem hmem2
    have hfst : (assigns.map Prod.fst)[idx1]'(by simp [hidx1]) =
        (assigns.map Prod.fst)[idx2]'(by simp [hidx2]) := by simp [heq1, heq2, he2]
    have hidx : idx1 = idx2 := hassigns_nd.getElem_inj_iff.mp hfst
    subst hidx; rw [heq1] at heq2; have := (Prod.mk.inj heq2).2; omega
  have hend_lt_2e : ∀ y : End, (∃ s ∈ specs.map Prod.fst, y.1 ∈ slotEdgesOf assigns s) →
      endKey y < 2 * eCap := by
    rintro ⟨ee, side⟩ ⟨s, _, he⟩
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at he
    rcases he with ⟨p, ⟨hp, _⟩, rfl⟩
    have := (hassigns_in p hp).1
    cases side <;> simp [endKey] <;> omega
  refine (Triple.forRange_const (p := pProg) (w := w) (r := 23) (lo := .const 0) (hi := .reg 22)
    (Inv := Inv) 205 0 len (Nat.zero_le _) (by omega)
    (fun _ => by dsimp only [len, v]; omega)
    (fun st ⟨hm, hc, r10, r17, r18, r19, r21, r22⟩ => by
      refine ⟨by eval_expr, hc.upd (by omega), by simp [r10], by simp [r17], by simp [r18],
        by simp [r19], by simp [r21], by simp [r22], by simp,
        fun q hq => by rw [hm]; exact hinit0 q hq, fun a _ _ _ => by rw [hm]⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.1; eval_expr)
    (fun t _ ht => by
      wram_enter
      rcases hpre with ⟨hc, r10, r17, r18, r19, r21, r22, r23, hslots, hfr⟩
      have ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc35,
        hr11, hr12, hr13, hr14, hr15, hr16⟩ : st.regs 0 = tbl ∧ _ := hc
      set x : End := (cord v)[t]'ht
      set key : ℕ := endKey x
      set e : ℕ := x.1
      have he_lt : e < eCap := hcord_lt x (List.getElem_mem ht)
      have hkey_lt : key < 2 * eCap := by
        rcases x with ⟨ee, side⟩; cases side <;> simp [key, e, endKey] at he_lt ⊢ <;> omega
      have hkey_div : key / 2 = e := by
        rcases x with ⟨ee, side⟩; cases side <;> simp [key, e, endKey]; omega
      have hcur_t_w : hCur + 1 + t < 2 ^ w := by dsimp only [len, v] at ht; omega
      have hmem_key : st.mem (hCur + 1 + t) = key := by
        rw [hfr _ (Or.inr (by omega)) (fun y hy => by
          have := hend_lt_2e y hy
          unfold btEndBundleBase btEndPrevBase btEndNextBase bundleTableFixedSize at *; omega)
          (fun s' hs' => by
            obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs'
            have := hspecs_lt sb hsb
            unfold btCurBunBase btCurTagBase bundleTableFixedSize at *; omega)]
        have h1 := hendList.2 t ht
        change mem₀ (hCur + 1 + t) = endKey ((cord v).getD t (0, true)) at h1
        rw [List.getD_eq_getElem _ _ ht] at h1
        exact h1
      have hmem_es : st.mem (tbl + 12 + slotCap + e) = mem₀ (btEdgeSlotBase tbl slotCap + e) :=
        hfr _ (Or.inl (by unfold bundleTableFixedSize at htbl_h; omega)) (fun y hy => by
          have := hend_lt_2e y hy
          unfold btEndBundleBase btEndPrevBase btEndNextBase at *; omega)
          (fun s' _ => by unfold btCurBunBase btCurTagBase; omega)
      dsimp only [bundleInitEndBody]
      refine runs_seq_assign_le (v := key) (by
        simp [Expr.eval, BinOp.eval, r10, r23, hmem_key, show 1 < 2 ^ w by omega,
          show hCur + 1 < 2 ^ w by omega, hcur_t_w]) ?_
      refine runs_seq_assign_le (v := e) (by
        simp [Expr.eval, BinOp.eval, hkey_div, show 2 < 2 ^ w by omega,
          show e < 2 ^ w by unfold bundleTableFixedSize at htbl_h; omega]) ?_
      refine runs_seq_assign_le (v := mem₀ (btEdgeSlotBase tbl slotCap + e)) (by
        simp [Expr.eval, BinOp.eval, hr12, hmem_es,
          show tbl + 12 + slotCap + e < 2 ^ w by unfold bundleTableFixedSize at htbl_h; omega]) ?_
      by_cases hex : ∃ s ∈ specs.map Prod.fst, e ∈ slotEdgesOf assigns s
      · obtain ⟨s, hs_mem, he_s⟩ := hex
        obtain ⟨q, hq_len, hsq⟩ := List.getElem_of_mem (List.mem_map.mp hs_mem |>.choose_spec.1)
        have hsq_eq : specs[q].1 = s := by
          have := (List.mem_map.mp hs_mem).choose_spec.2
          rw [← hsq] at this; exact this
        have hs_lt : s < slotCap := hsq_eq ▸ hspecs_lt specs[q] (List.getElem_mem hq_len)
        have hes_val : mem₀ (btEdgeSlotBase tbl slotCap + e) = s + 1 :=
          hedgeSlot_in e he_lt s hs_mem he_s
        simp only [hes_val]
        refine runs_cond_true_le (v := s + 1) (by simp [Expr.eval]) (Nat.succ_ne_zero s) ?_
        have hmem_flag : st.mem (tbl + 12 + slotCap + 7 * eCap + s) = 1 := by
          rw [hfr _ (Or.inl (by unfold bundleTableFixedSize at htbl_h; omega)) (fun y hy => by
            have := hend_lt_2e y hy
            unfold btEndBundleBase btEndPrevBase btEndNextBase at *; omega)
            (fun s' _ => by unfold btCurBunBase btCurTagBase; omega)]
          exact htouched_in s hs_mem
        have hs1_w : s + 1 < 2 ^ w := by unfold bundleTableFixedSize at htbl_h; omega
        wram_step; try dsimp only; simp only [Nat.add_sub_cancel]
        refine runs_seq_assign_le (v := 1) (by
          simp [Expr.eval, BinOp.eval, hr16, hmem_flag,
            show tbl + 12 + slotCap + 7 * eCap + s < 2 ^ w by
              unfold bundleTableFixedSize at htbl_h; omega]) ?_
        refine runs_cond_true_le (v := 1) (by simp [Expr.eval]) (by decide) ?_
        set p := h + slotBlocksSpace (specs.take q)
        set cap := specs[q].2
        set E_q := slotEdgesOf assigns s
        have hIq := hslots q hq_len
        rw [hsq_eq] at hIq
        have hp_end : p + bundleSlotBlockSize cap ≤ h + slotBlocksSpace specs := by
          have := hblk_end q hq_len; dsimp only [p, cap]; omega
        have hmem_p : st.mem (tbl + 12 + s) = p := by
          rw [hfr _ (Or.inl (by unfold bundleTableFixedSize at htbl_h; omega)) (fun y hy => by
            have := hend_lt_2e y hy
            unfold btEndBundleBase btEndPrevBase btEndNextBase at *; omega)
            (fun s' _ => by unfold btCurBunBase btCurTagBase; omega)]
          simpa [btSlotPtrBase, hsq_eq] using hslotPtr q hq_len
        have hmem_cap : st.mem p = cap := by simpa [bsOffBunCap] using hIq.2.1
        refine runs_seq_assign_le (v := p) (by
          simp [Expr.eval, BinOp.eval, hr11, hmem_p,
            show tbl + 12 + s < 2 ^ w by unfold bundleTableFixedSize at htbl_h; omega]) ?_
        refine runs_seq_assign_le (v := cap) (by
          simp [Expr.eval, hmem_cap]) ?_
        refine runs_seq_assign_le (v := st.mem (btCurTagBase tbl slotCap eCap + s)) (by
          simp [Expr.eval, BinOp.eval, r18,
            show btCurTagBase tbl slotCap eCap + s < 2 ^ w by
              unfold btCurTagBase bundleTableFixedSize at *; omega]) ?_
        have ht_r : t < (cord rList[i]).length := hv_eq ▸ ht
        have hx_r : ((cord rList[i])[t]'ht_r).1 ∈ E_q := by simpa [hv_eq, e, x] using he_s
        have hcap_next : (initMidSlots cord (rList.take i) rList[i] (t + 1) E_q k).length ≤ cap :=
          le_trans (initMidSlots_le_full cord rList hi (t + 1) E_q k)
            (by simpa [hsq_eq, E_q, cap] using hspecs_cap specs[q] (List.getElem_mem hq_len))
        have hchoose := bundleInitChooseBun_triple (w := w) (pProg := pProg)
          (eCap := eCap) (prevBase := btEndPrevBase tbl slotCap eCap)
          (nextBase := btEndNextBase tbl slotCap eCap) (endBunBase := btEndBundleBase tbl slotCap eCap)
          (curBunBase := btCurBunBase tbl slotCap eCap) (curTagBase := btCurTagBase tbl slotCap eCap)
          (i := i) (t := t) (s := s) (p := p) (cap := cap) (k := k)
          (cord := cord) (rList := rList) (E := E_q) (mem := st.mem)
          (regs0 := Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update st.regs 24 key) 25 e) 26 (s + 1))
            27 s) 28 1) 29 p) 30 cap) 31 (st.mem (btCurTagBase tbl slotCap eCap + s)))
          hw16 hk1 hi (by omega) ht_r hx_r
          (by unfold bundleSlotBlockSize at hp_end ⊢; omega)
          (by unfold btCurBunBase bundleTableFixedSize at *; omega)
          (by unfold btCurTagBase bundleTableFixedSize at *; omega)
          (Or.inr (by unfold btCurBunBase bundleTableFixedSize at *; omega))
          (Or.inr (by unfold btCurTagBase bundleTableFixedSize at *; omega))
          (by unfold btCurBunBase btCurTagBase; omega) hIq hcap_next
        refine runs_seq_triple_le hchoose
          ⟨rfl, rfl, by simp [hc2], by simp [r17], by simp [r18], by simp [r19],
            by simp, by simp, by simp, by simp⟩ ?_
        intro st1 ⟨hregs1, hr32_1, hnb1, htag1, hcurB1, hfr1⟩
        set curEnds := ((cord rList[i]).take t).filter fun y => decide (y.1 ∈ E_q)
        set oldChunks := initMidSlots cord (rList.take i) rList[i] t E_q k
        set newChunks := initMidSlots cord (rList.take i) rList[i] (t + 1) E_q k
        set bun := if curEnds.length % k = 0 then oldChunks.length else oldChunks.length - 1
        have hnew_len : newChunks.length =
            if curEnds.length % k = 0 then oldChunks.length + 1 else oldChunks.length := by
          have hce : ((cord rList[i]).take (t + 1)).filter (fun y => decide (y.1 ∈ E_q)) =
              curEnds ++ [(cord rList[i])[t]'ht_r] := by
            rw [List.take_succ_eq_append_getElem ht_r, List.filter_append]; simp [curEnds, hx_r]
          change (initPrefixSlots cord (rList.take i) E_q k ++
              (initialChunks k (((cord rList[i]).take (t + 1)).filter
                fun y => decide (y.1 ∈ E_q))).map (rList[i], ·)).length = _
          rw [hce, List.length_append, List.length_map, initialChunks_snoc_length hk1]
          have hold_eq : oldChunks.length =
              (initPrefixSlots cord (rList.take i) E_q k).length + (initialChunks k curEnds).length := by
            simp [oldChunks, initMidSlots, curEnds]
          split_ifs <;> omega
        have htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h := htbl_h
        have hp_blk : p + (3 + 6 * cap) ≤ h + slotBlocksSpace specs := hp_end
        have hp_ge : h ≤ p := Nat.le_add_right _ _
        have hh_w : h + slotBlocksSpace specs < 2 ^ w := by
          clear * - hh_cur hh_next hh_next_w; omega
        have hpos_of_ne : curEnds ≠ [] → 0 < oldChunks.length := fun hne => by
          have h1 : 1 ≤ (curEnds.length + k - 1) / k :=
            Nat.div_pos (by have := List.length_pos_of_ne_nil hne; clear * - this hk1; omega) hk1
          have h2 : oldChunks.length =
              (initPrefixSlots cord (rList.take i) E_q k).length + (curEnds.length + k - 1) / k := by
            simp only [oldChunks, initMidSlots, List.length_append, List.length_map,
              initialChunks_length_eq, curEnds]
          clear * - h1 h2; omega
        have hbun_lt_new : bun < newChunks.length := by
          rw [hnew_len]; dsimp only [bun]
          split_ifs with hmod
          · clear * -; omega
          · have hpos_old := hpos_of_ne (fun h0 => hmod (by simp [h0]))
            clear * - hpos_old; omega
        have hbun_lt_cap : bun < cap := lt_of_lt_of_le hbun_lt_new hcap_next
        have hfresh : ∀ b (hb : b < oldChunks.length),
            (cord rList[i])[t]'ht_r ∉ oldChunks[b].2 := by
          intro b hb hmem_x
          have hsrc := (mem_initMidSlots_end hk1 hb hmem_x).2
          rcases hsrc with ⟨w', hw', hxw'⟩ | hxt
          · have hw_eq : w' = rList[i] := hcord_disj w' rList[i] _ hxw' (List.getElem_mem ht_r)
            subst hw_eq
            obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hw'
            have hj_lt : j < i := by simp at hj; omega
            have := hrList_nd.getElem_inj_iff.mp (show rList[j]'(by omega) = rList[i] by
              simpa [List.getElem_take] using hjeq)
            omega
          · obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hxt
            have hj_lt : j < t := by simp at hj; omega
            have := (hcord_nd rList[i] (List.getElem_mem hi)).getElem_inj_iff.mp
              (show (cord rList[i])[j]'(by omega) = (cord rList[i])[t]'ht_r by
                simpa [List.getElem_take] using hjeq)
            omega
        obtain ⟨L, hL1, hsz1, hkey_notL, hLlen_lt, hL_nil, hL_mem⟩ :=
          bundleInitInner_hL_ex (slotCap := slotCap) (eCap := eCap) (tbl := tbl) (k := k) (h := h)
            (i := i) (t := t) (s := s) (p := p) (cap := cap) (bun := bun) (key := key)
            (specs := specs) (assigns := assigns) (cord := cord) (rList := rList)
            (st := st) (st1 := st1)
            hk1 htbl_h' hi hv_eq ht ht_r rfl hp_blk hp_ge hs_lt rfl hbun_lt_cap hpos_of_ne hfresh hIq hfr1
        have htail := bundleInitEndTail_triple (w := w) (pProg := pProg) (bDllPush := bDllPush)
          (eCap := eCap) (prevBase := btEndPrevBase tbl slotCap eCap)
          (nextBase := btEndNextBase tbl slotCap eCap)
          (endBunBase := btEndBundleBase tbl slotCap eCap)
          (p := p) (cap := cap) (bun := bun) (key := key) (sz := L.length) (L := L)
          (mem := st1.mem) (regs0 := st1.regs)
          (hbPush _ _ _ _ _) hw16
          (by unfold btEndPrevBase; clear * - htbl_h' hh_w; omega)
          (by unfold btEndNextBase; clear * - htbl_h' hh_w; omega)
          (Or.inl (by unfold btEndPrevBase btEndNextBase; clear * -; omega))
          (Or.inr (by unfold btEndPrevBase bsHeadBase; clear * - htbl_h' hp_ge; omega))
          (Or.inr (by unfold btEndNextBase bsHeadBase; clear * - htbl_h' hp_ge; omega))
          (by unfold bsSizeBase; clear * - hp_blk hh_w hbun_lt_cap; omega)
          (by unfold btEndBundleBase; clear * - htbl_h' hh_w hkey_lt; omega)
          hkey_lt hkey_notL hL1 hsz1 (by
            have hcard : (key :: L).length ≤ 2 * eCap := by
              have hnd : (key :: L).Nodup := List.nodup_cons.mpr ⟨hkey_notL, hL1.1⟩
              have hsub : (key :: L).toFinset ⊆ Finset.range (2 * eCap) := fun y hy => by
                rw [List.mem_toFinset, List.mem_cons] at hy
                exact Finset.mem_range.mpr (hy.elim (fun he => he ▸ hkey_lt) (hL1.2.1 y))
              have := Finset.card_le_card hsub
              rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
              exact this
            simp only [List.length_cons] at hcard
            clear * - hcard htbl_h' hh_w; omega)
          (by unfold bsSizeBase bsHeadBase; clear * - hbun_lt_cap; omega)
          (Or.inr (by unfold bsSizeBase btEndPrevBase; clear * - htbl_h' hp_ge; omega))
          (Or.inr (by unfold bsSizeBase btEndNextBase; clear * - htbl_h' hp_ge; omega))
          (by unfold btEndBundleBase bsSizeBase; clear * - htbl_h' hp_ge hkey_lt; omega)
          (by unfold btEndBundleBase bsHeadBase; clear * - htbl_h' hp_ge hkey_lt; omega)
          (Or.inl (by unfold btEndBundleBase btEndPrevBase; clear * - hkey_lt; omega))
          (Or.inl (by unfold btEndBundleBase btEndNextBase; clear * - hkey_lt; omega))
        refine runs_triple_le htail
          ⟨rfl, rfl, by rw [hregs1 13 (by decide) (by decide)]; simp [hr13, btEndBundleBase],
            by rw [hregs1 14 (by decide) (by decide)]; simp [hr14, btEndPrevBase],
            by rw [hregs1 15 (by decide) (by decide)]; simp [hr15, btEndNextBase],
            by rw [hregs1 24 (by decide) (by decide)]; simp,
            by rw [hregs1 29 (by decide) (by decide)]; simp,
            by rw [hregs1 30 (by decide) (by decide)]; simp, hr32_1⟩
          (fun o st2 hq2 => by
            cases o with
            | returned _ => exact False.elim hq2
            | normal =>
            rcases hq2 with ⟨hregs2, hdll2, hsz2, hend2, hfr2⟩
            exact bundleInitInner_post (slotCap := slotCap) (eCap := eCap) (tbl := tbl)
              (tourH := tourH) (k := k) (nSlots := nSlots) (slotSpecPtr := slotSpecPtr)
              (nEdges := nEdges) (edgeAssignPtr := edgeAssignPtr) (nR := nR) (rPtr := rPtr)
              (h := h) (hCur := hCur) (hNext := hNext) (i := i) (t := t) (q := q) (s := s)
              (p := p) (cap := cap) (bun := bun) (key := key) (e := e) (st := st) (st1 := st1)
              (st2 := st2) (L := L)
              hk1 htbl_h' hi hrList_nd hspecs_lt hspecs_nd hcord_nd
              hcord_disj hblk_end hblk_disj hdisj_slotE hend_lt_2e hq_len hsq_eq hs_lt hs_mem
              rfl rfl hp_blk hp_ge hv_eq ht ht_r rfl rfl he_s hx_r hkey_lt hcap_next rfl
              hbun_lt_cap hpos_of_ne hfresh hL1 hsz1 hL_nil hL_mem hc r10 r17 r18 r19 r21 r22 r23
              hslots hfr hregs1 hnb1 htag1 hcurB1 hfr1 hregs2 hdll2 hsz2 hend2 hfr2)
          (by simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; decide)
      · push Not at hex
        have htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h := htbl_h
        have hh_w : h + slotBlocksSpace specs < 2 ^ w := by
          clear * - hh_cur hh_next hh_next_w; omega
        rcases hedgeSlot_out e he_lt hex with hzero | ⟨s, hs_lt, hs_not, hes_val⟩
        · simp only [hzero]
          refine runs_cond_false_le (by simp [Expr.eval]) ?_
          refine runs_nop_le ?_ (by simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; decide)
          refine ⟨⟨(((hc.upd (by decide)).upd (by decide)).upd (by decide)).upd (by decide),
              by simp [r10], by simp [r17], by simp [r18], by simp [r19], by simp [r21],
              by simp [r22], by simp, fun q hq => (hslots q hq).step_skip ht
                (hex specs[q].1 (List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)), hfr⟩,
              by simp [r23]⟩
        · simp only [hes_val]
          refine runs_cond_true_le (v := s + 1) (by simp [Expr.eval]) (Nat.succ_ne_zero s) ?_
          have hmem_flag : st.mem (tbl + 12 + slotCap + 7 * eCap + s) = 0 := by
            rw [hfr _ (Or.inl (by clear * - htbl_h' hs_lt; omega)) (fun y hy => by
              have hy_lt := hend_lt_2e y hy
              unfold btEndBundleBase btEndPrevBase btEndNextBase; clear * - hy_lt; omega)
              (fun s' _ => by unfold btCurBunBase btCurTagBase; clear * - hs_lt; omega)]
            exact htouched_out s hs_lt hs_not
          refine runs_seq_assign_le (v := s) (by
            simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by clear * - hw16; omega,
              show s < 2 ^ w by clear * - htbl_h' hh_w hs_lt; omega]) ?_
          refine runs_seq_assign_le (v := 0) (by
            simp [Expr.eval, BinOp.eval, hr16, hmem_flag,
              show tbl + 12 + slotCap + 7 * eCap + s < 2 ^ w by
                clear * - htbl_h' hh_w hs_lt; omega]) ?_
          refine runs_cond_false_le (by simp [Expr.eval]) ?_
          refine runs_nop_le ?_ (by simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; decide)
          refine ⟨⟨(((((hc.upd (by decide)).upd (by decide)).upd (by decide)).upd (by decide)).upd
              (by decide)).upd (by decide),
              by simp [r10], by simp [r17], by simp [r18], by simp [r19], by simp [r21],
              by simp [r22], by simp, fun q hq => (hslots q hq).step_skip ht
                (hex specs[q].1 (List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)), hfr⟩,
              by simp [r23]⟩)).mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; clear * -; omega

end

end MinCostFlow.SparseCore.Program
