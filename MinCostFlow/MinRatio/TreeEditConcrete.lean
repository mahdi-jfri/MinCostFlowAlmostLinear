module

public import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.MinRatio.TreeEditPayloadSave

/-!
# Applying packed edits to the dynamic trees

The buffer frame keeps the graph and payload tables available during the edit loop.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut DynSpanner.Program

/-- The packed buffer is separate from both graph allocations, so
endpoint lookups remain available for the emitted edit order. -/
theorem TreeEditGraphs.of_pack_frame {R : DSRep PathTreeState}
    {handle oldBase newBase vc oldCap newCap : ℕ} {x : R.τ} {before after : State}
    {oldG newG : MGraph} {edits : List TreeChange}
    (hd : TreeEditDifference oldG.E newG.E edits)
    (hold : DynGraphAt before.mem oldBase vc oldCap oldG)
    (hnew : DynGraphAt before.mem newBase vc newCap newG)
    (heq : after.regs 3 = before.regs 3)
    (hOldBelow : oldBase + dynGraphSize vc oldCap ≤ before.regs 3)
    (hNewBelow : newBase + dynGraphSize vc newCap ≤ before.regs 3)
    (hOldOutside : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap → ¬ R.foot handle x a)
    (hNewOutside : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap → ¬ R.foot handle x a)
    (hOldSep : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap →
      a < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ a)
    (hNewSep : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap →
      a < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ a)
    (hframe : ∀ a, a < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ a →
      after.mem a = before.mem a) :
    TreeEditGraphs R handle x after oldBase newBase vc oldCap newCap oldG newG edits := by
  refine ⟨?_, heq.symm ▸ hOldBelow, heq.symm ▸ hNewBelow, hOldOutside, hNewOutside⟩
  intro edit hm
  have hlookup := TreeEditEndpointSuffix.of_diff hold hnew edit (hd.perm.mem_iff.mp hm)
  cases edit with
  | delete e => exact hlookup.congr_region (fun a hlo hhi => hframe a (hOldSep a hlo hhi))
  | insert e => exact hlookup.congr_region (fun a hlo hhi => hframe a (hNewSep a hlo hhi))

/-- Repacking the change list leaves every protected payload pointer
and record intact. -/
theorem TreeEditPayloads.of_pack_frame {R : DSRep PathTreeState} {handle h L : ℕ}
    {x : R.τ} {before after : State} {edits : List TreeChange}
    {record : ℕ → ℕ} {value : ℕ → PathEdgeValue}
    (hp : TreeEditPayloads R handle h L x before edits record value)
    (hHeap : after.regs 3 = before.regs 3) (hbase : after.regs 22 = before.regs 22)
    (hPointSep : ∀ e, TreeChange.insert e ∈ edits →
      before.regs 22 + e < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ before.regs 22 + e)
    (hRecordSep : ∀ e, TreeChange.insert e ∈ edits → ∀ a, record e ≤ a →
      a < record e + 2 + 4 * L → a < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ a)
    (hframe : ∀ a, a < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ a →
      after.mem a = before.mem a) :
    TreeEditPayloads R handle h L x after edits record value := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hp.payloadOutside⟩
  · intro e he
    rw [hbase, hframe _ (hPointSep e he)]
    exact hp.pointer e he
  · intro e he
    exact (hp.payload e he).congr fun a hlo hhi => hframe a (hRecordSep e he a hlo hhi)
  · intro e he
    rw [hbase, hHeap]
    exact hp.pointerBelow e he
  · rw [hHeap]
    exact hp.payloadBelow
  · rw [hbase]
    exact hp.pointerOutside

/-- An address lies outside both inverse slot tables. -/
@[expose] def OutsideTreeEditSlots (slots names edgeCap slotCap a : ℕ) : Prop :=
  (a < slots ∨ slots + edgeCap ≤ a) ∧ (a < names ∨ names + slotCap ≤ a)

theorem OutsideTreeEditSlots.ne_words {slots names edgeCap slotCap a e slot : ℕ}
    (h : OutsideTreeEditSlots slots names edgeCap slotCap a) (he : e < edgeCap)
    (hs : slot < slotCap) : a ≠ slots + e ∧ a ≠ names + slot := by
  obtain ⟨hedge, hslot⟩ := h
  exact ⟨fun eq => hedge.elim (by omega) (by omega), fun eq => hslot.elim (by omega) (by omega)⟩

/-- Run the concrete Cut and Link branches over the edit list.
The caller supplies a model invariant closed under the ordered edits
and the allocation and separation bounds for each call. -/
theorem treeEditLoop_concrete_runs {w L constant init cut link bind handle oldBase newBase vc oldCap
    newCap slots names edgeCap slotCap spacePerEdit : ℕ} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool}
    {R : DSRep PathTreeState} {op : ℕ → ℕ} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {st : State} {tree : PathTreeState} {x : R.τ} {changes : List TreeChange}
    {oldG newG ambient : MGraph} {record : ℕ → ℕ} {value : ℕ → PathEdgeValue}
    (Valid : List TreeChange → PathTreeState → Prop)
    (hOldForest : oldG.IsForest) (hforest : newG.IsForest)
    (hOldEnds : ∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f)
    (hNewEnds : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f)
    (hNewBound : ∀ f ∈ newG.E, ambient.tail f < tree.n ∧ ambient.head f < tree.n)
    (hNamedStart : ∃ f g, TreeEditNamedPrefix tree oldG newG ambient changes f g ∧
      PathSlotTablesAt st.mem slots names edgeCap slotCap f g)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hcut : cut = op 1) (hlink : link = op 0)
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hedgeTable : newCap ≤ edgeCap) (hslotTable : 2 * tree.n ≤ slotCap)
    (hvc : vc ≤ tree.n) (hw : 2 * tree.n + 1 < 2 ^ w)
    (hwidth : Nat.log 2 (2 * tree.n + 1) ≤ fmt.limbBits * L) (hhandle : handle < 2 ^ w)
    (h0 : st.regs 0 = handle)
    (h12 : st.regs 12 = dgETailSlotBase oldBase vc oldCap)
    (h13 : st.regs 13 = dgEHeadSlotBase oldBase vc oldCap)
    (h14 : st.regs 14 = dgIntToExtBase oldBase vc)
    (h15 : st.regs 15 = dgETailSlotBase newBase vc newCap)
    (h16 : st.regs 16 = dgEHeadSlotBase newBase vc newCap)
    (h17 : st.regs 17 = dgIntToExtBase newBase vc)
    (h19 : st.regs 19 = slots) (h20 : st.regs 20 = names)
    (hbuf : TreeEditBuffer R handle x st changes)
    (hready : TreeEditFoldReady R handle fmt.limbBits L st oldBase newBase vc oldCap newCap
        slots names edgeCap slotCap
      oldG newG record value changes x st)
    (hbudget : st.regs 3 + changes.length * spacePerEdit < 2 ^ w)
    (hrep : R.rep handle tree x st.mem) (hvalid : Valid changes tree)
    (hfits : ∀ edits t, Valid edits t → pathTreeFits fmt.limbBits L t)
    (hnext : ∀ edit rest t, Valid (edit :: rest) t →
      Valid rest (treeEditApply oldG newG value t edit))
    (hcutRoom : ∀ e rest t x before, Valid (.delete e :: rest) t →
      TreeEditFoldReady R handle fmt.limbBits L st oldBase newBase vc oldCap newCap
        slots names edgeCap slotCap
        oldG newG record value (.delete e :: rest) x before →
      allocation 1 t.n
        [handle, oldG.tail e + 1, oldG.head e + 1, before.regs 3] ≤ spacePerEdit)
    (hOldOutside : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap →
      OutsideTreeEditSlots slots names edgeCap slotCap a)
    (hNewOutside : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap →
      OutsideTreeEditSlots slots names edgeCap slotCap a)
    (hPointerOutside : ∀ f < newCap,
      OutsideTreeEditSlots slots names edgeCap slotCap (st.regs 22 + f))
    (hPayloadOutside : ∀ f < newCap, ∀ a, record f ≤ a → a < record f + 2 + 4 * L →
      OutsideTreeEditSlots slots names edgeCap slotCap a)
    (hBufferOutside : ∀ a, st.regs 6 ≤ a → a < st.regs 6 + 2 * changes.length →
      OutsideTreeEditSlots slots names edgeCap slotCap a)
    (hlinkRoom : ∀ e rest t x before, Valid (.insert e :: rest) t →
      TreeEditFoldReady R handle fmt.limbBits L st oldBase newBase vc oldCap newCap
        slots names edgeCap slotCap oldG newG record value (.insert e :: rest) x before →
      allocation 0 t.n [handle, newG.tail e + 1, newG.head e + 1, record e, before.regs 3] ≤ spacePerEdit) :
    ∃ out cost y,
      Runs w p ω (treeEditLoop link cut bind) st .normal out cost ∧
      TreeEditBuffer R handle y out [] ∧
      R.rep handle (changes.foldl (treeEditApply oldG newG value) tree) y out.mem ∧
      TreeEditFoldReady R handle fmt.limbBits L st oldBase newBase vc oldCap newCap
        slots names edgeCap slotCap
        oldG newG record value [] y out ∧
      out.regs 3 < 2 ^ w ∧
      (∃ ts fs ds f g,
        LctInvWith pathPayload (changes.foldl (treeEditApply oldG newG value) tree) ts fs ds ∧
        TreeEditNamedSlots (changes.foldl (treeEditApply oldG newG value) tree) ts newG f g ∧
        PathSlotTablesAt out.mem slots names edgeCap slotCap f g) ∧
      Valid [] (changes.foldl (treeEditApply oldG newG value) tree) ∧
      cost + R.phi handle y out.mem ≤
        changes.length * (pathTreeBudget constant L tree.n + 102) + R.phi handle x st.mem + 2 := by
  let Ready := fun edits t token before =>
    TreeEditFoldReady R handle fmt.limbBits L st oldBase newBase vc oldCap newCap
        slots names edgeCap slotCap
      oldG newG record value edits token before ∧
      (before.regs 3 + edits.length * spacePerEdit < 2 ^ w) ∧
      (st.regs 6 ≤ before.regs 6 ∧
        before.regs 6 + 2 * edits.length = st.regs 6 + 2 * changes.length) ∧
      (∃ f g, TreeEditNamedPrefix t oldG newG ambient edits f g ∧
        PathSlotTablesAt before.mem slots names edgeCap slotCap f g) ∧ Valid edits t
  obtain ⟨out, cost, y, hr, hb, ht, ⟨hf, hfinalHeap, _, hnamed, hv⟩, hc⟩ :=
    treeEditLoop_fold_runs (constant := constant) (L := L) oldG newG value Ready ⟨hready, hbudget, ⟨le_rfl, rfl⟩, hNamedStart, hvalid⟩ hbuf hrep (by
      intro edit rest current token before hb ht hn hready bits
      obtain ⟨hm, hbudget, hcursor, ⟨f, g, hprefix, htable⟩, hv⟩ := hready
      obtain ⟨hregs, hh, htables, hg, hp⟩ := hm
      have hi := hprefix.lctInv
      have hfit := hfits _ _ hv
      have hv' := hnext edit rest current hv
      have hfit' := hfits _ _ hv'
      have hcvc : vc ≤ current.n := hn.symm ▸ hvc
      have hcw : 2 * current.n + 1 < 2 ^ w := hn.symm ▸ hw
      have hcn : current.n < 2 ^ w := by omega
      have hcwidth : Nat.log 2 (2 * current.n + 1) ≤ fmt.limbBits * L := hn.symm ▸ hwidth
      have hzero := (hregs 0 (Or.inl rfl)).trans h0
      have hspace (n : ℕ) (h : n ≤ spacePerEdit) : before.regs 3 + n < 2 ^ w :=
        (treeEditHeapBudget_step (ret := 0) hbudget h (Nat.zero_le _)).1
      have hremain (ret n : ℕ) (h : n ≤ spacePerEdit) (hr : ret ≤ before.regs 3 + n) :
          ret + rest.length * spacePerEdit < 2 ^ w :=
        (treeEditHeapBudget_step hbudget h hr).2
      have hNewCurrent : ∀ f ∈ newG.E, ambient.tail f < current.n ∧ ambient.head f < current.n := by
        rw [hn]
        exact hNewBound
      have hNamedNext := hprefix.advance (value := value) hOldForest hforest hOldEnds hNewEnds hNewCurrent
      cases edit with
      | delete e =>
        change pathTreeFits fmt.limbBits L
          (lctCut pathPayload current (oldG.tail e + 1) (oldG.head e + 1)) at hfit'
        have ha := hcutRoom e rest current token before hv ⟨hregs, hh, htables, hg, hp⟩
        obtain ⟨after, ret, c, next, hr, hret, hcursorOut, hs, hb', hh', htables', htable', hg', hp', ht', hframe, hc⟩ :=
          treeEditIteration_cut_runs (bind := bind) (link := link) (ω := bits)
            hcut himpl hg hcvc hcn hb hp ((hregs 12 (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans h12)
            ((hregs 13 (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans h13) ((hregs 14 (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans h14)
            hzero rfl hhandle ht hi hfit hcw hcwidth hfit' htables htable hh (hspace _ ha)
        exact ⟨after, c, next, hr, hb', ht',
          ⟨⟨fun r h => (hs r h).trans (hregs r h), hh', hret.symm ▸ htables', hg', hp'⟩, hret.symm ▸ hremain ret _ ha hframe.2.1, ⟨by omega, by
            rw [hcursorOut, ← hcursor.2]
            simp only [List.length_cons]
            omega⟩, ⟨_, _, hNamedNext, htable'⟩, hv'⟩, by omega⟩
      | insert e =>
        change pathTreeFits fmt.limbBits L
          (lctLink pathPayload current (newG.tail e + 1) (newG.head e + 1) (some (value e))) at hfit'
        have ha := hlinkRoom e rest current token before hv ⟨hregs, hh, htables, hg, hp⟩
        have he : TreeEditEndpointAt before.mem newBase vc newCap newG e :=
          hg.lookup (.insert e) List.mem_cons_self
        have hedgeCap := he.edgeBound.trans_le hedgeTable
        have htail := he.tailNameBound.trans_le hcvc
        have hhead := he.headNameBound.trans_le hcvc
        have hconn := hprefix.insert_disconnected hforest hNewEnds htail hhead
        have hfree := treeEdit_freeHead_of_disconnected hi htail hhead hconn
        have hslotCap := (treeEditFreeHead_lt hi hfree).trans_le
          (show 2 * current.n ≤ slotCap by rwa [hn])
        have hbufSep a (hlo : before.regs 6 + 2 ≤ a)
            (hhi : a < before.regs 6 + 2 + (rest.flatMap treeEditWords).length) :=
          (hBufferOutside a (by have := hcursor.1; omega) (by
            rw [treeEditWords_length] at hhi
            rw [← hcursor.2]
            simp only [List.length_cons]
            omega)).ne_words hedgeCap hslotCap
        have hOldSep a hl hh := (hOldOutside a hl hh).ne_words hedgeCap hslotCap
        have hNewSep a hl hh := (hNewOutside a hl hh).ne_words hedgeCap hslotCap
        have hlookup (f : ℕ) (hf : TreeChange.insert f ∈ rest) : f < newCap :=
          (show TreeEditEndpointAt before.mem newBase vc newCap newG f from
            hg.lookup (.insert f) (List.mem_cons_of_mem _ hf)).edgeBound
        have hpSep f (hf : TreeChange.insert f ∈ rest) : before.regs 22 + f ≠ slots + e ∧
            before.regs 22 + f ≠ names + current.freeHead := by
          have heq := hregs 22 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          simpa only [heq] using (hPointerOutside f (hlookup f hf)).ne_words hedgeCap hslotCap
        have hvSep f hf a hl hh :=
          (hPayloadOutside f (hlookup f hf) a hl hh).ne_words hedgeCap hslotCap
        obtain ⟨after, ret, c, next, hr, hret, hcursorOut, hs', hb', hh', htables', htable', hg', hp', ht', hframe, hc⟩ :=
          treeEditIteration_link_runs (deleteBody := treeEditCut cut) (ω := bits) hbind hlink himpl hg hcvc hcn hb
            ((hregs 15 (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans h15) ((hregs 16 (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans h16)
            ((hregs 17 (Or.inr (Or.inl ⟨by decide, by decide⟩))).trans h17) hzero rfl ((hregs 19 (Or.inr (Or.inr (Or.inl rfl)))).trans h19)
            ((hregs 20 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans h20) hedgeCap hslotCap hbufSep hp hOldSep hNewSep
            hpSep hvSep hhandle ht hi hfit hcw hcwidth hconn hfit' htables htable hh (hspace _ ha)
        exact ⟨after, c, next, hr, hb', ht',
          ⟨⟨fun r h => (hs' r h).trans (hregs r h), hh', hret.symm ▸ htables', hg', hp'⟩, hret.symm ▸ hremain ret _ ha hframe.2.1, ⟨by omega, by
            rw [hcursorOut, ← hcursor.2]
            simp only [List.length_cons]
            omega⟩, ⟨_, _, hNamedNext, htable'⟩, hv'⟩, by omega⟩)
  obtain ⟨f, g, hprefix, htable⟩ := hnamed
  obtain ⟨ts, fs, ds, hi, hnames⟩ := hprefix.finish hNewEnds
  exact ⟨out, cost, y, hr, hb, ht, hf, by simpa using hfinalHeap,
    ⟨ts, fs, ds, f, g, hi, hnames, htable⟩, hv, hc⟩

end MinCostFlow.MinRatio
