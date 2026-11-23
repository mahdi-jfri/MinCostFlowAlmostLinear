module

public import MinCostFlow.SparseCore.Program.BundleInitProofs

/-!
# Postcondition assembly for `bundleInitSlotsStmt` (`BundleInitPost`)

Converts the final `InitScanSlotInv` and memory-frame relations after Loop 4 of
`bundleInitSlotsStmt` into `BundleTableRepAt`, `BundleTableCordMatch`, footprint containment, and
external memory framing (`bundleInitSlots_post`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Abstract bundle table state after installing `bundleStateOfSlots` for every `(s, _)` in
`specs` with edge set `slotEdgesOf assigns s`. -/
def tableAfterInitSlots {slotCap : ℕ} (S₀ : BundleTableState slotCap)
    (specs assigns : List (ℕ × ℕ)) (cord : ℕ → List End) (rList : List ℕ) (k : ℕ) :
    BundleTableState slotCap :=
  fun j =>
    if j.1 ∈ specs.map Prod.fst then
      some (bundleStateOfSlots (initPrefixSlots cord rList (slotEdgesOf assigns j.1) k)
        (slotEdgesOf assigns j.1))
    else S₀ j

end

public section

lemma initScanSlotInv_to_bundleSlotRepAt {eCap prevBase nextBase endBunBase curBunBase
    curTagBase s p cap k : ℕ} {cord : ℕ → List End} {rList : List ℕ} {E : Finset ℕ}
    {mem : ℕ → ℕ}
    (hk1 : 1 ≤ k) (hr_nd : rList.Nodup) (hcord_nd : ∀ v ∈ rList, (cord v).Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hE_lt : ∀ e ∈ E, e < eCap)
    (hcov : ∀ x : End, x.1 ∈ E → ∃ v ∈ rList, x ∈ cord v)
    (hI : InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList rList.length 0 s p cap k E mem) :
    let slots := initPrefixSlots cord rList E k
    let B := bundleStateOfSlots slots E
    BundleSlotRepAt eCap prevBase nextBase p cap B mem ∧
    (∀ x ∈ edgeEnds B.edges, mem (endBunBase + endKey x) = B.bundleOf x) ∧
    (∀ b ∈ B.vertices, (∃ v ∈ rList, B.parent b = v) ∧ ∀ x ∈ B.ends b, x ∈ cord (B.parent b)) := by
  intro slots B
  have hmid : initMidSlots cord (rList.take rList.length) (rList.getD rList.length 0) 0 E k =
      slots := by
    rw [initMidSlots_zero, List.take_length]
  rcases hI with ⟨hlen_cap, h0, h1, h2, hdll, htail, hscr, hbun_mem, _, _⟩
  rw [hmid] at hlen_cap h1 hdll htail hbun_mem
  obtain ⟨hne, hmem_src, hbun, hlt_all, hmem_ends⟩ :=
    bundleStateOfSlots_props hk1 hr_nd hcord_nd hcord_disj hcov
  refine ⟨⟨slots.length, rfl, hlen_cap, hE_lt, hlt_all, ?_, h0, h1, h2, ?_, ?_, htail, hscr⟩,
    ?_, ?_⟩
  · intro b hb
    change (slots[b]?.getD (0, [])).1 = 0
    rw [List.getElem?_eq_none hb]; rfl
  · intro b hb
    obtain ⟨L, hL, hsz, _, hmemL⟩ := hdll b hb
    exact ⟨L, hL, hsz, fun key => (hmemL key).trans (hmem_ends b hb (endOfKey key)).symm⟩
  · intro b hb hem
    exfalso
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne b hb)
    have hxin : x ∈ B.ends b := (hmem_ends b hb x).mpr hx
    rw [hem] at hxin; exact Finset.notMem_empty x hxin
  · intro x hx
    have hblt := hlt_all x hx
    have hxin : x ∈ slots[B.bundleOf x].2 := by
      have hm : x ∈ B.ends (B.bundleOf x) := by
        rw [BundleState.mem_ends]; exact ⟨(mem_edgeEnds E x).mp hx, rfl⟩
      exact (hmem_ends (B.bundleOf x) hblt x).mp hm
    exact hbun_mem (B.bundleOf x) hblt x hxin
  · intro b hb
    have hb_lt : b < slots.length := Finset.mem_range.mp hb
    have hpar : B.parent b = slots[b].1 := by
      change (slots[b]?.getD (0, [])).1 = slots[b].1
      rw [List.getElem?_eq_getElem hb_lt]; rfl
    rw [hpar]
    exact ⟨⟨slots[b].1, (hmem_src b hb_lt).1, rfl⟩,
      fun x hx => ((hmem_src b hb_lt).2 x ((hmem_ends b hb_lt x).mp hx)).2⟩

lemma slotEdgesOf_card_eq {assigns : List (ℕ × ℕ)} {s : ℕ}
    (hnd : (assigns.map Prod.fst).Nodup) :
    (slotEdgesOf assigns s).card = (assigns.filter fun p => p.2 == s).length := by
  unfold slotEdgesOf
  have hnd_f : ((assigns.filter fun p => p.2 == s).map Prod.fst).Nodup := by
    induction assigns with
    | nil => simp
    | cons a tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      simp only [List.filter_cons]
      split_ifs
      · rw [List.map_cons, List.nodup_cons]
        exact ⟨fun hmem => hnd.1 (by
          obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hmem
          exact List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, hpeq⟩), ih hnd.2⟩
      · exact ih hnd.2
  rw [List.toFinset_card_of_nodup hnd_f, List.length_map]

/-- Assembles `BundleTableRepAt`, `BundleTableCordMatch`, footprint containment, and external
memory framing after Loop 4 of `bundleInitSlotsStmt`. -/
lemma bundleInitSlots_post {slotCap vCap eCap tbl k nSlots nR h hEnd : ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ mem2 mem3 mem4 : ℕ → ℕ} {tourFoot₀ : ℕ → Prop}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hk1 : 1 ≤ k)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, bundleTableFoot eCap tbl m₀ a → a < h)
    (hh2_le : h + slotBlocksSpace specs ≤ hEnd)
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m₀ mem₀)
    (hcm0 : BundleTableCordMatch vCap S₀ cord)
    (htour_foot_disj_tbl : ∀ a, tourFoot₀ a → a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, tourFoot₀ a → ∀ j : Fin slotCap, ∀ p c,
      m₀.slotBlocks j = some (p, c) → a < p ∨ p + bundleSlotBlockSize c ≤ a)
    (hnSlots : specs.length = nSlots) (hnR : rList.length = nR)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap)
    (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_empty : ∀ sb ∈ specs, ∀ hlt : sb.1 < slotCap, S₀ ⟨sb.1, hlt⟩ = none)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hassigns_fresh : ∀ es ∈ assigns, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → es.1 ∉ B.edges)
    (hrList_lt : ∀ v ∈ rList, v < vCap)
    (hrList_nd : rList.Nodup) (hcord_nd : ∀ v ∈ rList, (cord v).Nodup)
    (hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v)
    (hblk_end : ∀ q (hq : q < specs.length),
      slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 ≤ slotBlocksSpace specs)
    (hblk_disj : ∀ q₁ q₂ (hq₁ : q₁ < specs.length) (hq₂ : q₂ < specs.length), q₁ ≠ q₂ →
      (h + slotBlocksSpace (specs.take q₁)) + bundleSlotBlockSize specs[q₁].2 ≤
        h + slotBlocksSpace (specs.take q₂) ∨
      (h + slotBlocksSpace (specs.take q₂)) + bundleSlotBlockSize specs[q₂].2 ≤
        h + slotBlocksSpace (specs.take q₁))
    (hst2_eq_mem0 : ∀ a,
      (∀ q (hq : q < specs.length), a ≠ h + slotBlocksSpace (specs.take q) ∧
        a ≠ h + slotBlocksSpace (specs.take q) + 2 ∧
        a ≠ tbl + 12 + specs[q].1 ∧ a ≠ tbl + 12 + slotCap + 7 * eCap + specs[q].1) →
      (∀ q (hq : q < assigns.length), a ≠ tbl + 12 + slotCap + assigns[q].1) →
      mem2 a = mem₀ a)
    (hst2_out_tbl : ∀ a, a < h → (a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a) →
      mem2 a = mem₀ a)
    (hslotPtr2 : ∀ q (hq : q < specs.length),
      mem2 (btSlotPtrBase tbl + specs[q].1) = h + slotBlocksSpace (specs.take q))
    (hedgeSlot_in2 : ∀ e < eCap, ∀ s ∈ specs.map Prod.fst, e ∈ slotEdgesOf assigns s →
      mem2 (btEdgeSlotBase tbl slotCap + e) = s + 1)
    (hzero3 : ZeroFrom mem3 hEnd)
    (hslots3 : ∀ q (hq : q < specs.length),
      InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
        (btCurTagBase tbl slotCap eCap) cord rList nR 0 specs[q].1
        (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) mem3)
    (hfr3 : ∀ a, a < h → ¬ tourFoot₀ a →
      (∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
        a ≠ btEndBundleBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndNextBase tbl slotCap eCap + endKey x) →
      (∀ s ∈ specs.map Prod.fst,
        a ≠ btCurBunBase tbl slotCap eCap + s ∧
        a ≠ btCurTagBase tbl slotCap eCap + s) →
      mem3 a = mem2 a)
    (hdone4 : ∀ q < nSlots, ∀ hql : q < specs.length,
      mem4 (tbl + 12 + slotCap + 7 * eCap + specs[q].1) = 0 ∧
      mem4 (btCurBunBase tbl slotCap eCap + specs[q].1) = 0 ∧
      mem4 (btCurTagBase tbl slotCap eCap + specs[q].1) = 0)
    (hfr4 : ∀ a, (∀ q < nSlots, ∀ hql : q < specs.length,
        a ≠ tbl + 12 + slotCap + 7 * eCap + specs[q].1 ∧
        a ≠ btCurBunBase tbl slotCap eCap + specs[q].1 ∧
        a ≠ btCurTagBase tbl slotCap eCap + specs[q].1) → mem4 a = mem3 a) :
    let S' := tableAfterInitSlots S₀ specs assigns cord rList k
    let m' := allocSlotBlocksMeta m₀ specs h
    ZeroFrom mem4 hEnd ∧
    BundleTableRepAt slotCap vCap eCap tbl S' m' mem4 ∧
    BundleTableCordMatch vCap S' cord ∧
    (∀ a, bundleTableFoot eCap tbl m' a →
      bundleTableFoot eCap tbl m₀ a ∨ (h ≤ a ∧ a < h + slotBlocksSpace specs)) ∧
    (∀ a, a < h → ¬ bundleTableFoot eCap tbl m₀ a → ¬ tourFoot₀ a → mem4 a = mem₀ a) := by
  intro S' m'
  have htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h := htbl_h
  rcases hrep0 with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11,
    hdisjE0, hedgeSlot0, hendBun0, hslots0, hdisjB0, hscrS0, hscrE0, hcur0⟩
  have hend_lt : ∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
      endKey x < 2 * eCap := by
    rintro ⟨ee, side⟩ ⟨s, _, hx⟩
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at hx
    rcases hx with ⟨pp, ⟨hpp, _⟩, rfl⟩
    have := (hassigns_in pp hpp).1
    cases side <;> simp [endKey] <;> omega
  have hst4_eq_st3 : ∀ a, (∀ s ∈ specs.map Prod.fst,
      a ≠ btSlotTouchedBase tbl slotCap eCap + s ∧
      a ≠ btCurBunBase tbl slotCap eCap + s ∧
      a ≠ btCurTagBase tbl slotCap eCap + s) →
      mem4 a = mem3 a := fun a ha =>
    hfr4 a fun q _ hql => ha specs[q].1 (List.mem_map.mpr ⟨specs[q], List.getElem_mem hql, rfl⟩)
  have hslot_cov : ∀ q (hq : q < specs.length), ∀ x : End, x.1 ∈ slotEdgesOf assigns specs[q].1 →
      ∃ v ∈ rList, x ∈ cord v := fun q _ x hx => by
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at hx
    rcases hx with ⟨p, ⟨hp, _⟩, hx1⟩
    rcases x with ⟨ee, side⟩; dsimp only at hx1; subst hx1; exact hcov p hp side
  have hslot_lt : ∀ q (hq : q < specs.length), ∀ e ∈ slotEdgesOf assigns specs[q].1, e < eCap := by
    intro q _ e he
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at he
    rcases he with ⟨p, ⟨hp, _⟩, rfl⟩; exact (hassigns_in p hp).1
  have hdisj_slotE : ∀ s₁ s₂, s₁ ≠ s₂ → ∀ e ∈ slotEdgesOf assigns s₁, e ∉ slotEdgesOf assigns s₂ := by
    intro s₁ s₂ hne e h1 h2
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at h1 h2
    rcases h1 with ⟨⟨e₁, s₁'⟩, ⟨hmem1, hs1⟩, rfl⟩
    rcases h2 with ⟨⟨e₂, s₂'⟩, ⟨hmem2, hs2⟩, he2⟩
    dsimp only at hs1 hs2 he2
    obtain ⟨idx1, hidx1, heq1⟩ := List.getElem_of_mem hmem1
    obtain ⟨idx2, hidx2, heq2⟩ := List.getElem_of_mem hmem2
    have hidx : idx1 = idx2 := hassigns_nd.getElem_inj_iff.mp
      (show (assigns.map Prod.fst)[idx1]'(by simp [hidx1]) = (assigns.map Prod.fst)[idx2]'(by simp [hidx2]) by
        simp [heq1, heq2, he2])
    subst hidx; rw [heq1] at heq2; have := (Prod.mk.inj heq2).2; omega
  have hslot_final : ∀ q (hq : q < specs.length),
      let slots := initPrefixSlots cord rList (slotEdgesOf assigns specs[q].1) k
      let B := bundleStateOfSlots slots (slotEdgesOf assigns specs[q].1)
      BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (h + slotBlocksSpace (specs.take q)) specs[q].2 B mem4 ∧
      (∀ x ∈ edgeEnds B.edges, mem4 (btEndBundleBase tbl slotCap eCap + endKey x) = B.bundleOf x) ∧
      (∀ b ∈ B.vertices, (∃ v ∈ rList, B.parent b = v) ∧ ∀ x ∈ B.ends b, x ∈ cord (B.parent b)) := by
    intro q hq
    have hIq3 := hslots3 q hq; rw [← hnR] at hIq3
    obtain ⟨hrep3, hbun3, hpar3⟩ :=
      initScanSlotInv_to_bundleSlotRepAt hk1 hrList_nd hcord_nd hcm0.1 (hslot_lt q hq)
        (hslot_cov q hq) hIq3
    refine ⟨hrep3.of_agree_slot ?_ ?_ ?_, ?_, hpar3⟩
    · intro a ha1 _
      exact (hst4_eq_st3 a fun s hs => by
        obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
        unfold btSlotTouchedBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega, by omega⟩).symm
    · intro key hkey
      have he_lt := hslot_lt q hq _ hkey
      have hkl : key < 2 * eCap := by
        have hke := bundle_endKey_endOfKey key
        rcases h : endOfKey key with ⟨ee, side⟩
        rw [h] at he_lt hke; cases side <;> simp [endKey] at hke <;> omega
      exact (hst4_eq_st3 _ fun s _ => by
        unfold btEndPrevBase btSlotTouchedBase btCurBunBase btCurTagBase
        exact ⟨by omega, by omega, by omega⟩).symm
    · intro key hkey
      have he_lt := hslot_lt q hq _ hkey
      have hkl : key < 2 * eCap := by
        have hke := bundle_endKey_endOfKey key
        rcases h : endOfKey key with ⟨ee, side⟩
        rw [h] at he_lt hke; cases side <;> simp [endKey] at hke <;> omega
      exact (hst4_eq_st3 _ fun s _ => by
        unfold btEndNextBase btSlotTouchedBase btCurBunBase btCurTagBase
        exact ⟨by omega, by omega, by omega⟩).symm
    · intro x hx
      have he_lt := hslot_lt q hq _ ((mem_edgeEnds _ _).mp hx)
      have hkl : endKey x < 2 * eCap := by
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      rw [hst4_eq_st3 _ fun s _ => by
        unfold btEndBundleBase btSlotTouchedBase btCurBunBase btCurTagBase
        exact ⟨by omega, by omega, by omega⟩]
      exact hbun3 x hx
  have hst4_fixed_eq_m0 : ∀ a, tbl ≤ a → a < tbl + bundleTableFixedSize slotCap eCap →
      (∀ q (hq : q < specs.length), a ≠ btSlotPtrBase tbl + specs[q].1 ∧
        a ≠ btSlotTouchedBase tbl slotCap eCap + specs[q].1 ∧
        a ≠ btCurBunBase tbl slotCap eCap + specs[q].1 ∧
        a ≠ btCurTagBase tbl slotCap eCap + specs[q].1) →
      (∀ q (hq : q < assigns.length), a ≠ btEdgeSlotBase tbl slotCap + assigns[q].1) →
      (∀ x : End, (∃ s ∈ specs.map Prod.fst, x.1 ∈ slotEdgesOf assigns s) →
        a ≠ btEndBundleBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndNextBase tbl slotCap eCap + endKey x) →
      mem4 a = mem₀ a := fun a ha1 ha2 h1 h2 h3 => by
    rw [hst4_eq_st3 a (fun s hs => by
      obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs
      obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
      simpa [hqeq] using (h1 q hq).2),
      hfr3 a (by omega) (fun hf => by have := htour_foot_disj_tbl a hf; omega) h3 (fun s hs => by
        obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs
        obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
        simpa [hqeq] using (h1 q hq).2.2)]
    exact hst2_eq_mem0 a (fun q hq => ⟨by omega, by omega, (h1 q hq).1, (h1 q hq).2.1⟩) h2
  have hst4_hdr : ∀ off < 12, mem4 (tbl + off) = mem₀ (tbl + off) := fun off hoff =>
    hst4_fixed_eq_m0 (tbl + off) (by omega) (by unfold bundleTableFixedSize; omega)
      (fun q hq => by
        unfold btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
        exact ⟨by omega, by omega, by omega, by omega⟩)
      (fun q hq => by unfold btEdgeSlotBase; omega)
      (fun x _ => by unfold btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hst4_eq_st3 a fun s hs => by
      obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
      unfold btSlotTouchedBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega, by omega⟩]
    exact hzero3 a ha
  · refine ⟨(hst4_hdr 0 (by decide)).trans hr0, (hst4_hdr 1 (by decide)).trans hr1,
      (hst4_hdr 2 (by decide)).trans hr2, (hst4_hdr 3 (by decide)).trans hr3,
      (hst4_hdr 4 (by decide)).trans hr4, (hst4_hdr 5 (by decide)).trans hr5,
      (hst4_hdr 6 (by decide)).trans hr6, (hst4_hdr 7 (by decide)).trans hr7,
      (hst4_hdr 8 (by decide)).trans hr8, (hst4_hdr 9 (by decide)).trans hr9,
      (hst4_hdr 10 (by decide)).trans hr10, (hst4_hdr 11 (by decide)).trans hr11,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j₁ j₂ hne B₁ B₂ hB₁ hB₂
      simp only [S', tableAfterInitSlots] at hB₁ hB₂
      split_ifs at hB₁ hB₂ with h1 h2
      · cases hB₁; cases hB₂
        exact Finset.disjoint_left.mpr fun e he1 he2 =>
          hdisj_slotE j₁.1 j₂.1 (fun h => hne (Fin.ext h)) e he1 he2
      · cases hB₁
        refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
        simp only [bundleStateOfSlots, slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter,
          beq_iff_eq] at he1
        rcases he1 with ⟨p, ⟨hp, _⟩, rfl⟩; exact hassigns_fresh p hp j₂ B₂ hB₂ he2
      · cases hB₂
        refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
        simp only [bundleStateOfSlots, slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter,
          beq_iff_eq] at he2
        rcases he2 with ⟨p, ⟨hp, _⟩, rfl⟩; exact hassigns_fresh p hp j₁ B₁ hB₁ he1
      · exact hdisjE0 j₁ j₂ hne B₁ B₂ hB₁ hB₂
    · intro e he
      have hst4_es : mem4 (btEdgeSlotBase tbl slotCap + e) = mem2 (btEdgeSlotBase tbl slotCap + e) := by
        rw [hst4_eq_st3 _ fun s _ => by
            unfold btEdgeSlotBase btSlotTouchedBase btCurBunBase btCurTagBase
            exact ⟨by omega, by omega, by omega⟩,
          hfr3 _ (by unfold btEdgeSlotBase; omega)
            (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btEdgeSlotBase bundleTableFixedSize at *; omega)
            (fun x _ => by unfold btEdgeSlotBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)
            (fun s _ => by unfold btEdgeSlotBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
      rw [hst4_es]
      refine ⟨fun j B hSj heB => ?_, fun hnone => ?_⟩
      · simp only [S', tableAfterInitSlots] at hSj
        split_ifs at hSj with hmem
        · cases hSj; exact hedgeSlot_in2 e he j.1 hmem heB
        · rw [hst2_eq_mem0 _ (fun q hq => by
            have := hspecs_lt _ (List.getElem_mem hq); unfold btEdgeSlotBase
            exact ⟨by omega, by omega, by omega, by omega⟩)
            (fun q hq => by
              have hne_e : assigns[q].1 ≠ e := fun h =>
                hassigns_fresh assigns[q] (List.getElem_mem hq) j B hSj (h ▸ heB)
              unfold btEdgeSlotBase; omega)]
          exact (hedgeSlot0 e he).1 j B hSj heB
      · have hnot_s : ∀ s ∈ specs.map Prod.fst, e ∉ slotEdgesOf assigns s := by
          intro s hs hes
          obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs
          have hs' : sb.1 ∈ specs.map Prod.fst := List.mem_map.mpr ⟨sb, hsb, rfl⟩
          exact hnone ⟨sb.1, hspecs_lt sb hsb⟩
            (bundleStateOfSlots (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k) (slotEdgesOf assigns sb.1))
            (by simp [S', tableAfterInitSlots, hs']) hes
        have hnot_old : ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B → e ∉ B.edges := by
          intro j B hSj
          have hnot_j : j.1 ∉ specs.map Prod.fst := by
            intro hin; obtain ⟨sb, hsb, heq⟩ := List.mem_map.mp hin
            have := hspecs_empty sb hsb (heq ▸ j.2)
            rw [show (⟨sb.1, heq ▸ j.2⟩ : Fin slotCap) = j from Fin.ext heq, hSj] at this; cases this
          exact hnone j B (by simp [S', tableAfterInitSlots, hnot_j, hSj])
        rw [hst2_eq_mem0 _ (fun q hq => by
          have := hspecs_lt _ (List.getElem_mem hq); unfold btEdgeSlotBase
          exact ⟨by omega, by omega, by omega, by omega⟩)
          (fun q hq => by
            have hne_e : assigns[q].1 ≠ e := fun h => by
              have hmem := List.getElem_mem hq
              exact hnot_s assigns[q].2 (hassigns_in _ hmem).2
                (by simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
                    exact ⟨assigns[q], ⟨hmem, rfl⟩, h⟩)
            unfold btEdgeSlotBase; omega)]
        exact (hedgeSlot0 e he).2 hnot_old
    · intro j B hSj x hx
      simp only [S', tableAfterInitSlots] at hSj
      split_ifs at hSj with hmem
      · cases hSj
        obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp hmem
        obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
        have hsq : specs[q].1 = j.1 := by rw [hqeq]; exact hsbeq
        exact hsq ▸ (hslot_final q hq).2.1 x (hsq.symm ▸ hx)
      · have heB : x.1 ∈ B.edges := (mem_edgeEnds _ _).mp hx
        have hkx : endKey x < 2 * eCap := by
          have hslot := hslots0 j; rw [hSj] at hslot
          cases hm0 : m₀.slotBlocks j with
          | none => rw [hm0] at hslot; exact False.elim hslot
          | some pb =>
            rw [hm0] at hslot
            have he_lt := hslot.2.1.choose_spec.2.2.1 x.1 heB
            rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
        rw [hst4_fixed_eq_m0 _ (by unfold btEndBundleBase; omega)
          (by unfold btEndBundleBase bundleTableFixedSize; omega)
          (fun q hq => by
            have := hspecs_lt _ (List.getElem_mem hq)
            unfold btEndBundleBase btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
            exact ⟨by omega, by omega, by omega, by omega⟩)
          (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btEndBundleBase btEdgeSlotBase; omega)
          (fun y ⟨s, hs, hy⟩ => by
            have hne_e : x.1 ≠ y.1 := by
              simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at hy
              rcases hy with ⟨p, ⟨hp, _⟩, hpeq⟩
              exact fun h => hassigns_fresh p hp j B hSj ((hpeq.trans h.symm) ▸ heB)
            have hne_k : endKey x ≠ endKey y := fun h => hne_e (by
              have := congrArg (fun z => (endOfKey z).1) h; simpa [bundle_endOfKey_endKey] using this)
            unfold btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
        exact hendBun0 j B hSj x hx
    · intro j
      by_cases hmem : j.1 ∈ specs.map Prod.fst
      · obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp hmem
        obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
        have hsq : specs[q].1 = j.1 := by rw [hqeq]; exact hsbeq
        simp only [S', tableAfterInitSlots, hmem, ↓reduceIte, m',
          allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq hsq.symm]
        refine ⟨?_, hsq ▸ (hslot_final q hq).1, Or.inr (by omega)⟩
        rw [hst4_eq_st3 _ fun s _ => by
            unfold btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
            exact ⟨by omega, by omega, by omega⟩,
          hfr3 _ (by unfold btSlotPtrBase; omega)
            (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btSlotPtrBase bundleTableFixedSize at *; omega)
            (fun x _ => by unfold btSlotPtrBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)
            (fun s _ => by unfold btSlotPtrBase btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
        simpa [hsq] using hslotPtr2 q hq
      · simp only [S', tableAfterInitSlots, hmem, ↓reduceIte, m',
          allocSlotBlocksMeta_of_not_mem m₀ specs h hmem]
        have hslot := hslots0 j
        cases hS : S₀ j with
        | none =>
          rw [hS] at hslot
          cases hm : m₀.slotBlocks j with
          | none =>
            rw [hm] at hslot
            rw [hst4_fixed_eq_m0 _ (by unfold btSlotPtrBase; omega)
              (by unfold btSlotPtrBase bundleTableFixedSize; omega)
              (fun q hq => by
                have hne : j.1 ≠ specs[q].1 := fun h => hmem (h ▸ List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)
                unfold btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
                exact ⟨by omega, by omega, by omega, by omega⟩)
              (fun q hq => by unfold btSlotPtrBase btEdgeSlotBase; omega)
              (fun x _ => by unfold btSlotPtrBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
            exact hslot
          | some _ => rw [hm] at hslot; exact False.elim hslot
        | some B =>
          rw [hS] at hslot
          cases hm : m₀.slotBlocks j with
          | none => rw [hm] at hslot; exact False.elim hslot
          | some pb =>
            rcases pb with ⟨p, c⟩; rw [hm] at hslot
            refine ⟨?_, ?_, hslot.2.2⟩
            · rw [hst4_fixed_eq_m0 _ (by unfold btSlotPtrBase; omega)
                (by unfold btSlotPtrBase bundleTableFixedSize; omega)
                (fun q hq => by
                  have hne : j.1 ≠ specs[q].1 := fun h => hmem (h ▸ List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)
                  unfold btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
                  exact ⟨by omega, by omega, by omega, by omega⟩)
                (fun q hq => by unfold btSlotPtrBase btEdgeSlotBase; omega)
                (fun x _ => by unfold btSlotPtrBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
              exact hslot.1
            · refine hslot.2.1.of_agree_slot ?_ ?_ ?_
              · intro a ha1 ha2
                have ha_lt : a < h := hfoot0_lt a (Or.inr ⟨j, p, c, hm, ha1, ha2⟩)
                have ha_disj_tbl : a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a := by
                  rcases hslot.2.2 with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
                have ha_nf : ¬ tourFoot₀ a := fun hf => by
                  have := htour_foot_disj_blocks a hf j p c hm; omega
                rw [hst4_eq_st3 a (fun s hs => by
                  obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
                  unfold btSlotTouchedBase btCurBunBase btCurTagBase bundleTableFixedSize at *
                  exact ⟨by omega, by omega, by omega⟩),
                  hfr3 a ha_lt ha_nf (fun x hx => by
                    have hkx := hend_lt x hx
                    unfold bundleTableFixedSize at ha_disj_tbl
                    unfold btEndBundleBase btEndPrevBase btEndNextBase
                    exact ⟨by omega, by omega, by omega⟩)
                    (fun s hs => by
                      obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
                      unfold bundleTableFixedSize at ha_disj_tbl
                      unfold btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
                exact (hst2_out_tbl a ha_lt ha_disj_tbl).symm
              · intro k hk
                have he_lt := hslot.2.1.choose_spec.2.2.1 _ hk
                have hkl : k < 2 * eCap := by
                  have hke := bundle_endKey_endOfKey k
                  rcases h : endOfKey k with ⟨ee, side⟩
                  rw [h] at he_lt hke; cases side <;> simp [endKey] at hke <;> omega
                exact (hst4_fixed_eq_m0 _ (by unfold btEndPrevBase; omega)
                  (by unfold btEndPrevBase bundleTableFixedSize; omega)
                  (fun q hq => by
                    have := hspecs_lt _ (List.getElem_mem hq)
                    unfold btEndPrevBase btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
                    exact ⟨by omega, by omega, by omega, by omega⟩)
                  (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btEndPrevBase btEdgeSlotBase; omega)
                  (fun y hy => by
                    have hyk := hend_lt y hy
                    rcases hy with ⟨_, _, hy'⟩
                    have hne_e : (endOfKey k).1 ≠ y.1 := by
                      simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at hy'
                      rcases hy' with ⟨pp, ⟨hpp, _⟩, hpeq⟩
                      exact fun h => hassigns_fresh pp hpp j B hS ((hpeq.trans h.symm) ▸ hk)
                    have hne_k : k ≠ endKey y := fun h => hne_e (by
                      have := congrArg (fun z => (endOfKey z).1) h; simpa [bundle_endOfKey_endKey] using this)
                    unfold btEndPrevBase btEndBundleBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)).symm
              · intro k hk
                have he_lt := hslot.2.1.choose_spec.2.2.1 _ hk
                have hkl : k < 2 * eCap := by
                  have hke := bundle_endKey_endOfKey k
                  rcases h : endOfKey k with ⟨ee, side⟩
                  rw [h] at he_lt hke; cases side <;> simp [endKey] at hke <;> omega
                exact (hst4_fixed_eq_m0 _ (by unfold btEndNextBase; omega)
                  (by unfold btEndNextBase bundleTableFixedSize; omega)
                  (fun q hq => by
                    have := hspecs_lt _ (List.getElem_mem hq)
                    unfold btEndNextBase btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
                    exact ⟨by omega, by omega, by omega, by omega⟩)
                  (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btEndNextBase btEdgeSlotBase; omega)
                  (fun y hy => by
                    have hyk := hend_lt y hy
                    rcases hy with ⟨_, _, hy'⟩
                    have hne_e : (endOfKey k).1 ≠ y.1 := by
                      simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at hy'
                      rcases hy' with ⟨pp, ⟨hpp, _⟩, hpeq⟩
                      exact fun h => hassigns_fresh pp hpp j B hS ((hpeq.trans h.symm) ▸ hk)
                    have hne_k : k ≠ endKey y := fun h => hne_e (by
                      have := congrArg (fun z => (endOfKey z).1) h; simpa [bundle_endOfKey_endKey] using this)
                    unfold btEndNextBase btEndBundleBase btEndPrevBase; exact ⟨by omega, by omega, by omega⟩)).symm
    · intro j₁ j₂ hne p₁ c₁ p₂ c₂ hm₁ hm₂
      by_cases h1 : j₁.1 ∈ specs.map Prod.fst <;> by_cases h2 : j₂.1 ∈ specs.map Prod.fst
      · obtain ⟨sb₁, hsb₁, heq₁⟩ := List.mem_map.mp h1
        obtain ⟨sb₂, hsb₂, heq₂⟩ := List.mem_map.mp h2
        obtain ⟨q₁, hq₁, hqeq₁⟩ := List.getElem_of_mem hsb₁
        obtain ⟨q₂, hq₂, hqeq₂⟩ := List.getElem_of_mem hsb₂
        have hsq₁ : specs[q₁].1 = j₁.1 := by rw [hqeq₁]; exact heq₁
        have hsq₂ : specs[q₂].1 = j₂.1 := by rw [hqeq₂]; exact heq₂
        rw [allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq₁ hsq₁.symm] at hm₁
        rw [allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq₂ hsq₂.symm] at hm₂
        cases hm₁; cases hm₂
        exact hblk_disj q₁ q₂ hq₁ hq₂ fun hq => hne (Fin.ext (by subst hq; rw [← hsq₁, ← hsq₂]))
      · obtain ⟨sb₁, hsb₁, heq₁⟩ := List.mem_map.mp h1
        obtain ⟨q₁, hq₁, hqeq₁⟩ := List.getElem_of_mem hsb₁
        have hsq₁ : specs[q₁].1 = j₁.1 := by rw [hqeq₁]; exact heq₁
        rw [allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq₁ hsq₁.symm] at hm₁
        rw [allocSlotBlocksMeta_of_not_mem m₀ specs h h2] at hm₂; cases hm₁
        have hp₂ : p₂ + bundleSlotBlockSize c₂ ≤ h := by
          have := hfoot0_lt (p₂ + bundleSlotBlockSize c₂ - 1)
            (Or.inr ⟨j₂, p₂, c₂, hm₂, by unfold bundleSlotBlockSize; omega, by unfold bundleSlotBlockSize; omega⟩)
          unfold bundleSlotBlockSize at *; omega
        exact Or.inr (by omega)
      · obtain ⟨sb₂, hsb₂, heq₂⟩ := List.mem_map.mp h2
        obtain ⟨q₂, hq₂, hqeq₂⟩ := List.getElem_of_mem hsb₂
        have hsq₂ : specs[q₂].1 = j₂.1 := by rw [hqeq₂]; exact heq₂
        rw [allocSlotBlocksMeta_of_not_mem m₀ specs h h1] at hm₁
        rw [allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq₂ hsq₂.symm] at hm₂; cases hm₂
        have hp₁ : p₁ + bundleSlotBlockSize c₁ ≤ h := by
          have := hfoot0_lt (p₁ + bundleSlotBlockSize c₁ - 1)
            (Or.inr ⟨j₁, p₁, c₁, hm₁, by unfold bundleSlotBlockSize; omega, by unfold bundleSlotBlockSize; omega⟩)
          unfold bundleSlotBlockSize at *; omega
        exact Or.inl (by omega)
      · rw [allocSlotBlocksMeta_of_not_mem m₀ specs h h1] at hm₁
        rw [allocSlotBlocksMeta_of_not_mem m₀ specs h h2] at hm₂
        exact hdisjB0 j₁ j₂ hne p₁ c₁ p₂ c₂ hm₁ hm₂
    · intro s hs
      refine ⟨?_, ?_, ?_⟩
      · by_cases hmem : s ∈ specs.map Prod.fst
        · obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hmem
          obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
          simpa [btSlotTouchedBase, hqeq] using (hdone4 q (by omega) hq).1
        · rw [hst4_fixed_eq_m0 _ (by unfold btSlotTouchedBase; omega)
            (by unfold btSlotTouchedBase bundleTableFixedSize; omega)
            (fun q hq => by
              have := hspecs_lt _ (List.getElem_mem hq)
              have hne : s ≠ specs[q].1 := fun h => hmem (h ▸ List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)
              unfold btSlotTouchedBase btSlotPtrBase btCurBunBase btCurTagBase
              exact ⟨by omega, by omega, by omega, by omega⟩)
            (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btSlotTouchedBase btEdgeSlotBase; omega)
            (fun x hx => by have := hend_lt x hx; unfold btSlotTouchedBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
          exact (hscrS0 s hs).1
      · rw [hst4_fixed_eq_m0 _ (by unfold btSlotDelHeadBase; omega)
          (by unfold btSlotDelHeadBase bundleTableFixedSize; omega)
          (fun q hq => by
            have := hspecs_lt _ (List.getElem_mem hq)
            unfold btSlotDelHeadBase btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
            exact ⟨by omega, by omega, by omega, by omega⟩)
          (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btSlotDelHeadBase btEdgeSlotBase; omega)
          (fun x hx => by have := hend_lt x hx; unfold btSlotDelHeadBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
        exact (hscrS0 s hs).2.1
      · rw [hst4_fixed_eq_m0 _ (by unfold btSlotCandHeadBase; omega)
          (by unfold btSlotCandHeadBase bundleTableFixedSize; omega)
          (fun q hq => by
            have := hspecs_lt _ (List.getElem_mem hq)
            unfold btSlotCandHeadBase btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
            exact ⟨by omega, by omega, by omega, by omega⟩)
          (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btSlotCandHeadBase btEdgeSlotBase; omega)
          (fun x hx => by have := hend_lt x hx; unfold btSlotCandHeadBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
        exact (hscrS0 s hs).2.2
    · intro e he
      rw [hst4_fixed_eq_m0 _ (by unfold btSlotDelNextBase; omega)
        (by unfold btSlotDelNextBase bundleTableFixedSize; omega)
        (fun q hq => by
          have := hspecs_lt _ (List.getElem_mem hq)
          unfold btSlotDelNextBase btSlotPtrBase btSlotTouchedBase btCurBunBase btCurTagBase
          exact ⟨by omega, by omega, by omega, by omega⟩)
        (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btSlotDelNextBase btEdgeSlotBase; omega)
        (fun x hx => by have := hend_lt x hx; unfold btSlotDelNextBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
      exact hscrE0 e he
    · intro s hs
      by_cases hmem : s ∈ specs.map Prod.fst
      · obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
        simpa [hqeq] using (hdone4 q (by omega) hq).2
      · refine ⟨?_, ?_⟩
        · rw [hst4_fixed_eq_m0 _ (by unfold btCurBunBase; omega)
            (by unfold btCurBunBase bundleTableFixedSize; omega)
            (fun q hq => by
              have := hspecs_lt _ (List.getElem_mem hq)
              have hne : s ≠ specs[q].1 := fun h => hmem (h ▸ List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)
              unfold btCurBunBase btSlotPtrBase btSlotTouchedBase btCurTagBase
              exact ⟨by omega, by omega, by omega, by omega⟩)
            (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btCurBunBase btEdgeSlotBase; omega)
            (fun x hx => by have := hend_lt x hx; unfold btCurBunBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
          exact (hcur0 s hs).1
        · rw [hst4_fixed_eq_m0 _ (by unfold btCurTagBase; omega)
            (by unfold btCurTagBase bundleTableFixedSize; omega)
            (fun q hq => by
              have := hspecs_lt _ (List.getElem_mem hq)
              have hne : s ≠ specs[q].1 := fun h => hmem (h ▸ List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)
              unfold btCurTagBase btSlotPtrBase btSlotTouchedBase btCurBunBase
              exact ⟨by omega, by omega, by omega, by omega⟩)
            (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btCurTagBase btEdgeSlotBase; omega)
            (fun x hx => by have := hend_lt x hx; unfold btCurTagBase btEndBundleBase btEndPrevBase btEndNextBase; exact ⟨by omega, by omega, by omega⟩)]
          exact (hcur0 s hs).2
  · refine ⟨hcm0.1, fun j B hSj b hb => ?_⟩
    simp only [S', tableAfterInitSlots] at hSj
    split_ifs at hSj with hmem
    · cases hSj
      obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp hmem
      obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
      have hsq : specs[q].1 = j.1 := by rw [hqeq]; exact hsbeq
      rw [← hsq] at hb ⊢
      obtain ⟨⟨v, hv, hpar⟩, hends⟩ := (hslot_final q hq).2.2 b hb
      exact ⟨hpar ▸ hrList_lt v hv, hends⟩
    · exact hcm0.2 j B hSj b hb
  · intro a ha
    rcases ha with hfix | ⟨j, p, c, hm, ha1, ha2⟩
    · exact Or.inl (Or.inl hfix)
    · by_cases hmem : j.1 ∈ specs.map Prod.fst
      · obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp hmem
        obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
        have hsq : specs[q].1 = j.1 := by rw [hqeq]; exact hsbeq
        rw [allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq hsq.symm] at hm
        cases hm; have := hblk_end q hq; exact Or.inr ⟨by omega, by omega⟩
      · rw [allocSlotBlocksMeta_of_not_mem m₀ specs h hmem] at hm
        exact Or.inl (Or.inr ⟨j, p, c, hm, ha1, ha2⟩)
  · intro a ha hnf0 hnt0
    have ha_disj_tbl : a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a := by
      by_contra hcon; push Not at hcon; exact hnf0 (Or.inl hcon)
    rw [hst4_eq_st3 a fun s hs => by
      obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
      unfold btSlotTouchedBase btCurBunBase btCurTagBase bundleTableFixedSize at *
      exact ⟨by omega, by omega, by omega⟩]
    rw [hfr3 a ha hnt0 (fun x hx => by
      have hkx := hend_lt x hx
      unfold bundleTableFixedSize at ha_disj_tbl
      unfold btEndBundleBase btEndPrevBase btEndNextBase
      exact ⟨by omega, by omega, by omega⟩)
      (fun s hs => by
        obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
        unfold bundleTableFixedSize at ha_disj_tbl
        unfold btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
    exact hst2_out_tbl a ha ha_disj_tbl

end

end MinCostFlow.SparseCore.Program
