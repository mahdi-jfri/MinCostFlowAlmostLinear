module

public import MinCostFlow.MinRatio.TreeEditDispatch
import WordRAM.Memory

/-!
# Applying the chain tree's change list

The proof of Theorem 5.1 (pages 29–30) charges link-cut operations
to the edge changes produced by Lemma 5.11 (page 20). The loop
consumes two words per record and telescopes the tree potential.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut DynSpanner.Program

/-- Register 6 is the record cursor and register 18 counts unread edits. -/
@[expose] def treeEditAdvance : Stmt :=
  .assign 6 (.bin .add (.reg 6) (.const 2)) ;;
  .assign 18 (.bin .sub (.reg 18) (.const 1))

/-- Move to the next tree change after applying the current one. -/
theorem treeEditAdvance_runs {w addr remaining : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (ha : st.regs 6 = addr) (hr : st.regs 18 = remaining)
    (hw : addr + 2 < 2 ^ w) (hcounts : remaining < 2 ^ w) :
    ∃ out, Runs w p ω treeEditAdvance st .normal out 9 ∧
      out.regs 6 = addr + 2 ∧ out.regs 18 = remaining - 1 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 6 → r ≠ 18 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 6 (addr + 2) }
  let out := { mid with regs := Function.update mid.regs 18 (remaining - 1) }
  have htwo : 2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hsub : remaining - 1 < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 2))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, ha, htwo, hw], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 18 (.bin .sub (.reg 18) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, Function.update_of_ne, hr, hone, hsub],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], rfl, ?_⟩
  intro r h6 h18
  simp [out, mid, Function.update_of_ne, h6, h18]

/-- A linked cut or link preserves the unread suffix when the edit
buffer is below the heap and outside the tree footprint. Advance the
cursor and remaining count after the edit. -/
theorem treeEditAdvance_after_dispatch {w base heap : ℕ} {p : Program}
    {ω : ℕ → Bool} {before mid : State}
    {edit : TreeChange} {rest : List TreeChange} {foot : ℕ → Prop}
    (hbuf : TreeEditsAt before.mem base (edit :: rest))
    (hframe : ∀ a < heap, ¬ foot a → mid.mem a = before.mem a)
    (hroom : base + 2 + (rest.flatMap treeEditWords).length ≤ heap)
    (hsep : ∀ a, base + 2 ≤ a → a < base + 2 + (rest.flatMap treeEditWords).length → ¬ foot a)
    (hcursor : mid.regs 6 = base) (hcount : mid.regs 18 = (edit :: rest).length)
    (hword : heap < 2 ^ w) (hcountWord : (edit :: rest).length < 2 ^ w) :
    ∃ out, Runs w p ω treeEditAdvance mid .normal out 9 ∧
      out.regs 6 = base + 2 ∧ out.regs 18 = rest.length ∧
      TreeEditsAt out.mem (base + 2) rest ∧ out.mem = mid.mem ∧
      (∀ r, r ≠ 6 → r ≠ 18 → out.regs r = mid.regs r) := by
  have htail : ListAt before.mem (base + 2) (rest.flatMap treeEditWords) :=
    (treeEditsAt_cons hbuf).2
  have htail' := htail.congr (mem' := mid.mem) (fun a hlo hup =>
    hframe a (hup.trans_le hroom) (hsep a hlo hup))
  obtain ⟨out, hr, h6, h18, hmem, hregs⟩ :=
    treeEditAdvance_runs (p := p) (ω := ω) hcursor hcount (by omega) hcountWord
  exact ⟨out, hr, h6, by simpa using h18, by rwa [hmem], hmem, hregs⟩

/-- Fresh tree cells cannot overlap any unread edit cell below the
incoming heap. This supplies the next iteration's separation fact. -/
theorem treeEditSuffix_disjoint {base heap ret space handle : ℕ}
    {R : DSRep PathTreeState} {old new : R.τ} {mem mem' : ℕ → ℕ}
    {rest : List TreeChange}
    (hroom : base + (rest.flatMap treeEditWords).length ≤ heap)
    (hsep : ∀ a, base ≤ a → a < base + (rest.flatMap treeEditWords).length → ¬ R.foot handle old a)
    (hr : R.Respects (R.foot handle old) heap space mem ret handle new mem') :
    base + (rest.flatMap treeEditWords).length ≤ ret ∧
      (∀ a, base ≤ a → a < base + (rest.flatMap treeEditWords).length → ¬ R.foot handle new a) := by
  refine ⟨hroom.trans hr.1, ?_⟩
  intro a hlo hup hf
  rcases hr.2.2.2.2 a hf with hold | ⟨hnew, _⟩
  · exact hsep a hlo hup hold
  · exact (Nat.not_le_of_lt (hup.trans_le hroom)) hnew

/-- The unread tree-edit records lie below the heap and outside
the current link-cut footprint. -/
structure TreeEditBuffer (R : DSRep PathTreeState) (handle : ℕ)
    (token : R.τ) (st : State) (edits : List TreeChange) : Prop where
  count : st.regs 18 = edits.length
  records : TreeEditsAt st.mem (st.regs 6) edits
  bound : st.regs 6 + (edits.flatMap treeEditWords).length ≤ st.regs 3
  disjoint : ∀ a, st.regs 6 ≤ a → a < st.regs 6 + (edits.flatMap treeEditWords).length →
    ¬ R.foot handle token a

/-- Enter the edit loop with the change list from a Shift or Rebuild.
The exact symmetric-difference size determines the buffer bounds. -/
theorem TreeEditBuffer.of_diff {R : DSRep PathTreeState} {handle : ℕ} {x : R.τ}
    {st : State} {oldE newE : Finset ℕ}
    (hcount : st.regs 18 = (oldE \ newE).card + (newE \ oldE).card)
    (hrecords : TreeEditsAt st.mem (st.regs 6) (diffTreeChanges oldE newE))
    (hbound : st.regs 6 + 2 * ((oldE \ newE).card + (newE \ oldE).card) ≤ st.regs 3)
    (hsep : ∀ a, st.regs 6 ≤ a →
      a < st.regs 6 + 2 * ((oldE \ newE).card + (newE \ oldE).card) → ¬ R.foot handle x a) :
    TreeEditBuffer R handle x st (diffTreeChanges oldE newE) := by
  refine ⟨?_, hrecords, ?_, ?_⟩
  · rwa [diffTreeChanges_length]
  · rwa [treeEditDiff_words]
  · rw [treeEditDiff_words]
    exact hsep

/-- The tree call followed by cursor advance leaves a valid buffer
for the remainder of the model's edit list. -/
theorem TreeEditBuffer.advance_with_writes {w handle ret space : ℕ} {p : Program}
    {ω : ℕ → Bool} {st mid : State} {R : DSRep PathTreeState}
    {x y : R.τ} {extra : ℕ → Prop} {edit : TreeChange} {rest : List TreeChange}
    (hbuf : TreeEditBuffer R handle x st (edit :: rest))
    (hframe : R.Respects (fun a => R.foot handle x a ∨ extra a) (st.regs 3) space st.mem ret handle y mid.mem)
    (hextra : ∀ a, st.regs 6 + 2 ≤ a → a < st.regs 6 + 2 +
      (rest.flatMap treeEditWords).length → ¬ extra a)
    (hheap : mid.regs 3 = ret)
    (hcursor : mid.regs 6 = st.regs 6) (hcount : mid.regs 18 = st.regs 18)
    (hword : st.regs 3 < 2 ^ w) :
    ∃ out, Runs w p ω treeEditAdvance mid .normal out 9 ∧
      TreeEditBuffer R handle y out rest ∧ out.mem = mid.mem ∧ out.regs 6 = st.regs 6 + 2 ∧
      (∀ r, r ≠ 6 → r ≠ 18 → out.regs r = mid.regs r) := by
  have hcountWord : (edit :: rest).length < 2 ^ w := by
    have hb := hbuf.bound
    rw [treeEditWords_length] at hb
    omega
  have hlen : (treeEditWords edit).length = 2 := by cases edit <;> rfl
  have hb := hbuf.bound
  have hd := hbuf.disjoint
  simp only [List.flatMap_cons, List.length_append, hlen, ← Nat.add_assoc] at hb hd
  have hsep a (hl : st.regs 6 + 2 ≤ a)
      (hu : a < st.regs 6 + 2 + (rest.flatMap treeEditWords).length) :
      ¬ (R.foot handle x a ∨ extra a) :=
    fun hw => hw.elim (hd a (by omega) hu) (hextra a hl hu)
  obtain ⟨out, hrun, h6, h18, hrecords, hmem, hregs⟩ :=
    treeEditAdvance_after_dispatch (p := p) (ω := ω) hbuf.records hframe.2.2.2.1
      hb hsep hcursor (hcount.trans hbuf.count) hword hcountWord
  have hbound := hb.trans hframe.1
  have h3 := (hregs 3 (by decide) (by decide)).trans hheap
  refine ⟨out, hrun, ⟨h18, ?_, ?_, ?_⟩, hmem, h6, hregs⟩
  · rwa [h6]
  · rwa [h6, h3]
  · rw [h6]
    intro a hlo hhi ha
    rcases hframe.2.2.2.2 a ha with hold | ⟨hnew, _⟩
    · exact hsep a hlo hhi hold
    · exact (Nat.not_le_of_lt (hhi.trans_le hb)) hnew

/-- Advance after an edit whose only writes are to its tree footprint. -/
theorem TreeEditBuffer.advance {w handle ret space : ℕ} {p : Program}
    {ω : ℕ → Bool} {st mid : State} {R : DSRep PathTreeState}
    {x y : R.τ} {edit : TreeChange} {rest : List TreeChange}
    (hbuf : TreeEditBuffer R handle x st (edit :: rest))
    (hframe : R.Respects (R.foot handle x) (st.regs 3) space st.mem ret handle y mid.mem)
    (hheap : mid.regs 3 = ret)
    (hcursor : mid.regs 6 = st.regs 6) (hcount : mid.regs 18 = st.regs 18)
    (hword : st.regs 3 < 2 ^ w) :
    ∃ out, Runs w p ω treeEditAdvance mid .normal out 9 ∧
      TreeEditBuffer R handle y out rest ∧ out.mem = mid.mem ∧ out.regs 6 = st.regs 6 + 2 ∧
      (∀ r, r ≠ 6 → r ≠ 18 → out.regs r = mid.regs r) := by
  exact hbuf.advance_with_writes (extra := fun _ => False)
    (by simpa only [or_false] using hframe) (fun _ _ _ => id) hheap hcursor hcount hword

/-- The unread buffer survives Link followed by slot binding if
neither table cell belongs to the unread suffix. -/
theorem TreeEditBuffer.advance_after_link_bind {w handle ret space slots names edge slot : ℕ}
    {R : DSRep PathTreeState} {x y : R.τ} {p : Program} {ω : ℕ → Bool}
    {st linked bound : State} {rest : List TreeChange}
    (hb : TreeEditBuffer R handle x st (.insert edge :: rest))
    (htree : R.Respects (R.foot handle x) (st.regs 3) space st.mem ret handle y linked.mem)
    (hbind : (pathSlotBindContract w).post [slots, names, edge, slot, ret] linked.mem ret bound.mem)
    (hsep : ∀ a, st.regs 6 + 2 ≤ a →
      a < st.regs 6 + 2 + (rest.flatMap treeEditWords).length →
      a ≠ slots + edge ∧ a ≠ names + slot)
    (hheap : bound.regs 3 = ret)
    (hcursor : bound.regs 6 = st.regs 6) (hcount : bound.regs 18 = st.regs 18)
    (hword : st.regs 3 < 2 ^ w) :
    ∃ out, Runs w p ω treeEditAdvance bound .normal out 9 ∧
      TreeEditBuffer R handle y out rest ∧ out.mem = bound.mem ∧ out.regs 3 = ret ∧ out.regs 6 = st.regs 6 + 2 ∧
      (∀ r, r ≠ 6 → r ≠ 18 → out.regs r = bound.regs r) := by
  have hlimit := hb.bound
  have hdisj := hb.disjoint
  simp only [List.flatMap_cons, List.length_append, treeEditWords, List.length_cons,
    List.length_nil, ← Nat.add_assoc] at hlimit hdisj
  have hwithin a (ha : st.regs 6 + 2 ≤ a)
      (hu : a < st.regs 6 + 2 + (rest.flatMap treeEditWords).length) :
      ¬ R.foot handle x a :=
    hdisj a (by omega) hu
  have hcword : (TreeChange.insert edge :: rest).length < 2 ^ w := by
    have hb' := hb.bound
    rw [treeEditWords_length] at hb'
    omega
  have hf := treeEdit_link_bind_respects htree hbind
  obtain ⟨out, hr, h6, h18, hat, hm, hregs⟩ :=
    treeEditAdvance_after_dispatch (p := p) (ω := ω) hb.records hf.2.2.2.1 hlimit
      (fun a hl hu ha => ha.elim (hwithin a hl hu) (fun he =>
        he.elim (hsep a hl hu).1 (hsep a hl hu).2))
      hcursor (hcount.trans hb.count) hword hcword
  obtain ⟨hlimit', hdisj'⟩ := treeEditSuffix_disjoint hlimit hwithin htree
  have h3 := (hregs 3 (by decide) (by decide)).trans hheap
  refine ⟨out, hr, ⟨h18, ?_, ?_, ?_⟩, hm, h3, h6, hregs⟩
  · rwa [h6]
  · rwa [h6, h3]
  · rw [h6]
    exact hdisj'

/-- A verified dispatch and the buffer advance form one complete
iteration, preserving the resulting tree and its amortized bound. -/
theorem treeEditIteration_runs {w link cut handle ret space cost budget : ℕ}
    {p : Program} {ω : ℕ → Bool} {st mid : State} {R : DSRep PathTreeState}
    {x y : R.τ} {tree : PathTreeState} {edit : TreeChange} {rest : List TreeChange}
    (hbuf : TreeEditBuffer R handle x st (edit :: rest))
    (hdispatch : Runs w p ω (treeEditDispatch link cut) st .normal mid cost)
    (hrep : R.rep handle tree y mid.mem)
    (hframe : R.Respects (R.foot handle x) (st.regs 3) space st.mem ret handle y mid.mem)
    (hheap : mid.regs 3 = ret)
    (hcursor : mid.regs 6 = st.regs 6) (hcount : mid.regs 18 = st.regs 18)
    (hword : st.regs 3 < 2 ^ w)
    (hcost : cost + R.phi handle y mid.mem ≤ budget + R.phi handle x st.mem) :
    ∃ out, Runs w p ω (treeEditDispatch link cut ;; treeEditAdvance) st .normal out (cost + 10) ∧
      TreeEditBuffer R handle y out rest ∧ R.rep handle tree y out.mem ∧
      out.regs 3 = ret ∧ out.mem = mid.mem ∧
      cost + 10 + R.phi handle y out.mem ≤ budget + 10 + R.phi handle x st.mem := by
  obtain ⟨out, ha, hb, hm, _, hregs⟩ :=
    hbuf.advance (p := p) (ω := ω) hframe hheap hcursor hcount hword
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 9, hdispatch, ha, by omega⟩),
    hb, by rwa [hm], (hregs 3 (by decide) (by decide)).trans hheap, hm, ?_⟩
  rw [hm]
  omega

/-- A protected payload table cell stays readable for a later insertion.
The frame excludes both tree storage and any slot bindings written by
the preceding edit. -/
theorem treeEditPayloadAddr_preserved
    {R : DSRep PathTreeState} {st out : State} {old : ℕ → Prop}
    {space ret handle edge record : ℕ} {y : R.τ}
    (hframe : R.Respects old (st.regs 3) space st.mem ret handle y out.mem)
    (hbase : out.regs 22 = st.regs 22)
    (hbelow : st.regs 22 + edge < st.regs 3)
    (hprotected : ¬ old (st.regs 22 + edge))
    (hrecord : st.mem (st.regs 22 + edge) = record) :
    out.mem (out.regs 22 + edge) = record := by
  rw [hbase, hframe.2.2.2.1 _ hbelow hprotected, hrecord]

/-- The handle and all table bases lie in registers unaffected by an edit. -/
@[expose] def TreeEditInputReg (r : ℕ) : Prop :=
  r = 0 ∨ 12 ≤ r ∧ r ≤ 17 ∨ r = 19 ∨ r = 20 ∨ r = 22 ∨ r = 29

theorem TreeEditInputReg.valid {r : ℕ} (hr : TreeEditInputReg r) :
    r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧
      r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 18 ∧ r ≠ 21 := by
  unfold TreeEditInputReg at hr
  omega

/-- The tree occupies only allocated words and the unused heap is zero. -/
structure TreeEditHeap (R : DSRep PathTreeState) (handle : ℕ) (x : R.τ) (st : State) : Prop where
  below : ∀ a, R.foot handle x a → a < st.regs 3
  zero : ZeroFrom st.mem (st.regs 3)

/-- The operation frame keeps the tree inside the allocated heap.
Any writes outside the old tree footprint must also be below the old heap. -/
theorem TreeEditHeap.advance {R : DSRep PathTreeState} {handle space ret : ℕ}
    {x y : R.τ} {st out : State} {extra : ℕ → Prop}
    (hh : TreeEditHeap R handle x st)
    (hf : R.Respects (fun a => R.foot handle x a ∨ extra a) (st.regs 3)
      space st.mem ret handle y out.mem)
    (hheap : out.regs 3 = ret) (hextra : ∀ a, extra a → a < st.regs 3) :
    TreeEditHeap R handle y out := by
  rw [← hheap] at hf
  refine ⟨?_, hf.2.2.1⟩
  intro a ha
  rcases hf.2.2.2.2 a ha with (hold | ⟨_, hnew⟩)
  · exact (hold.elim (hh.below a) (hextra a)).trans_le hf.1
  · exact hnew

/-- The two inverse slot tables occupy separate allocated intervals
outside the tree representation. -/
structure TreeEditSlotStorage (R : DSRep PathTreeState) (handle slots names edgeCap slotCap : ℕ)
    (x : R.τ) (heap : ℕ) : Prop where
  slotsBelow : slots + edgeCap ≤ heap
  namesBelow : names + slotCap ≤ heap
  separate : slots + edgeCap ≤ names ∨ names + slotCap ≤ slots
  slotsOutside : ∀ a, slots ≤ a → a < slots + edgeCap → ¬ R.foot handle x a
  namesOutside : ∀ a, names ≤ a → a < names + slotCap → ¬ R.foot handle x a

/-- The tree's allocation frame keeps the whole slot-table storage
outside the new tree. Binding a slot afterwards keeps the same tree token. -/
theorem TreeEditSlotStorage.advance_with_writes
    {R : DSRep PathTreeState} {handle slots names edgeCap slotCap heap space ret : ℕ}
    {x y : R.τ} {mem mem' : ℕ → ℕ} {extra : ℕ → Prop}
    (ht : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (hf : R.Respects (fun a => R.foot handle x a ∨ extra a) heap space mem ret handle y mem')
    (hslots : ∀ a, slots ≤ a → a < slots + edgeCap → ¬ extra a)
    (hnames : ∀ a, names ≤ a → a < names + slotCap → ¬ extra a) :
    TreeEditSlotStorage R handle slots names edgeCap slotCap y ret := by
  have hkeep a (ha : a < heap) (houtside : ¬ (R.foot handle x a ∨ extra a)) : ¬ R.foot handle y a :=
    fun h => (hf.2.2.2.2 a h).elim houtside (fun hnew => (Nat.not_le_of_lt ha) hnew.1)
  exact ⟨ht.slotsBelow.trans hf.1, ht.namesBelow.trans hf.1, ht.separate,
    fun a hlo hhi => hkeep a (hhi.trans_le ht.slotsBelow) (fun h => h.elim (ht.slotsOutside a hlo hhi) (hslots a hlo hhi)),
    fun a hlo hhi => hkeep a (hhi.trans_le ht.namesBelow) (fun h => h.elim (ht.namesOutside a hlo hhi) (hnames a hlo hhi))⟩

/-- Retain slot storage when the call only writes its own footprint. -/
theorem TreeEditSlotStorage.advance
    {R : DSRep PathTreeState} {handle slots names edgeCap slotCap heap space ret : ℕ}
    {x y : R.τ} {mem mem' : ℕ → ℕ}
    (ht : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (hf : R.Respects (R.foot handle x) heap space mem ret handle y mem') :
    TreeEditSlotStorage R handle slots names edgeCap slotCap y ret :=
  ht.advance_with_writes (extra := fun _ => False) (by simpa only [or_false] using hf)
    (fun _ _ _ => id) (fun _ _ _ => id)

/-- A tree call preserves both table contents before any slot binding. -/
theorem TreeEditSlotStorage.frame_tables_with_writes
    {R : DSRep PathTreeState} {handle slots names edgeCap slotCap heap space ret : ℕ}
    {x y : R.τ} {mem mem' : ℕ → ℕ} {f g : ℕ → ℕ} {extra : ℕ → Prop}
    (ht : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (hf : R.Respects (fun a => R.foot handle x a ∨ extra a) heap space mem ret handle y mem')
    (hslots : ∀ a, slots ≤ a → a < slots + edgeCap → ¬ extra a)
    (hnames : ∀ a, names ≤ a → a < names + slotCap → ¬ extra a)
    (hh : PathSlotTablesAt mem slots names edgeCap slotCap f g) :
    PathSlotTablesAt mem' slots names edgeCap slotCap f g := by
  apply hh.congr
  · intro e he
    have hhi := Nat.add_lt_add_left he slots
    refine hf.2.2.2.1 _ (hhi.trans_le ht.slotsBelow) ?_
    exact fun h => h.elim (ht.slotsOutside _ (by omega) hhi) (hslots _ (by omega) hhi)
  · intro k hk
    have hhi := Nat.add_lt_add_left hk names
    refine hf.2.2.2.1 _ (hhi.trans_le ht.namesBelow) ?_
    exact fun h => h.elim (ht.namesOutside _ (by omega) hhi) (hnames _ (by omega) hhi)

/-- Retain the table cells when the call only writes its tree footprint. -/
theorem TreeEditSlotStorage.frame_tables
    {R : DSRep PathTreeState} {handle slots names edgeCap slotCap heap space ret : ℕ}
    {x y : R.τ} {mem mem' : ℕ → ℕ} {f g : ℕ → ℕ}
    (ht : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (hf : R.Respects (R.foot handle x) heap space mem ret handle y mem')
    (hh : PathSlotTablesAt mem slots names edgeCap slotCap f g) :
    PathSlotTablesAt mem' slots names edgeCap slotCap f g :=
  ht.frame_tables_with_writes (extra := fun _ => False) (by simpa only [or_false] using hf)
    (fun _ _ _ => id) (fun _ _ _ => id) hh

/-- In-range Link indices give two distinct writable words below the
heap and outside the tree. -/
theorem TreeEditSlotStorage.bind_words
    {R : DSRep PathTreeState} {handle slots names edgeCap slotCap heap e slot : ℕ} {x : R.τ}
    (ht : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (he : e < edgeCap) (hs : slot < slotCap) :
    slots + e < heap ∧ names + slot < heap ∧ slots + e ≠ names + slot ∧
      ¬ R.foot handle x (slots + e) ∧ ¬ R.foot handle x (names + slot) := by
  have hEdge : slots + e < slots + edgeCap := Nat.add_lt_add_left he _
  have hSlot : names + slot < names + slotCap := Nat.add_lt_add_left hs _
  refine ⟨hEdge.trans_le ht.slotsBelow, hSlot.trans_le ht.namesBelow, ?_,
    ht.slotsOutside _ (Nat.le_add_right _ _) hEdge, ht.namesOutside _ (Nat.le_add_right _ _) hSlot⟩
  rcases ht.separate with hl | hr <;> omega

/-- Readiness of the endpoint lookups for the unread edit suffix.
A deletion uses the old graph, and an insertion uses the new graph. -/
@[expose] def TreeEditEndpointSuffix (mem : ℕ → ℕ) (oldBase newBase vc oldCap newCap : ℕ)
    (oldG newG : MGraph) (edits : List TreeChange) : Prop :=
  ∀ edit ∈ edits, match edit with
    | .delete e => TreeEditEndpointAt mem oldBase vc oldCap oldG e
    | .insert e => TreeEditEndpointAt mem newBase vc newCap newG e

/-- The two graph layouts supply every lookup in the symmetric
difference used to enter the edit loop. -/
theorem TreeEditEndpointSuffix.of_diff {mem : ℕ → ℕ} {oldBase newBase vc oldCap newCap : ℕ}
    {oldG newG : MGraph}
    (hold : DynGraphAt mem oldBase vc oldCap oldG) (hnew : DynGraphAt mem newBase vc newCap newG) :
    TreeEditEndpointSuffix mem oldBase newBase vc oldCap newCap oldG newG
      (diffTreeChanges oldG.E newG.E) := by
  intro edit he
  cases edit with
  | delete e =>
    exact TreeEditEndpointAt.of_graph hold (Finset.mem_sdiff.mp (treeEdit_delete_mem_diff.mp he)).1
  | insert e =>
    exact TreeEditEndpointAt.of_graph hnew (Finset.mem_sdiff.mp (treeEdit_insert_mem_diff.mp he)).1

/-- A graph region below the incoming heap stays disjoint from the
new tree footprint if it was outside all writable addresses. -/
theorem treeEditGraphRegion_disjoint
    {R : DSRep PathTreeState} {base vc ec heap ret space handle : ℕ}
    {mem mem' : ℕ → ℕ} {write : ℕ → Prop} {y : R.τ}
    (hf : R.Respects write heap space mem ret handle y mem')
    (hbelow : base + dynGraphSize vc ec ≤ heap)
    (hsep : ∀ a, base ≤ a → a < base + dynGraphSize vc ec → ¬ write a) :
    base + dynGraphSize vc ec ≤ ret ∧
      ∀ a, base ≤ a → a < base + dynGraphSize vc ec → ¬ R.foot handle y a := by
  refine ⟨hbelow.trans hf.1, ?_⟩
  intro a hlo hhi hfoot
  rcases hf.2.2.2.2 a hfoot with hw | ⟨hfresh, _⟩
  · exact hsep a hlo hhi hw
  · exact (Nat.not_le_of_lt (hhi.trans_le hbelow)) hfresh

/-- An edit preserves the endpoint lookups on the suffix if both graphs
are below the heap and disjoint from the edit's writable memory. -/
theorem TreeEditEndpointSuffix.advance
    {R : DSRep PathTreeState} {oldBase newBase vc oldCap newCap heap ret space handle : ℕ}
    {mem mem' : ℕ → ℕ} {oldG newG : MGraph} {edit : TreeChange} {rest : List TreeChange}
    {write : ℕ → Prop} {y : R.τ}
    (he : TreeEditEndpointSuffix mem oldBase newBase vc oldCap newCap oldG newG (edit :: rest))
    (hf : R.Respects write heap space mem ret handle y mem')
    (hold : oldBase + dynGraphSize vc oldCap ≤ heap)
    (hnew : newBase + dynGraphSize vc newCap ≤ heap)
    (hOldSep : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap → ¬ write a)
    (hNewSep : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap → ¬ write a) :
    TreeEditEndpointSuffix mem' oldBase newBase vc oldCap newCap oldG newG rest := by
  intro next hn
  have hlookup := he next (List.mem_cons_of_mem edit hn)
  cases next with
  | delete e =>
    exact hlookup.congr_region fun a ha hb => hf.2.2.2.1 a (hb.trans_le hold) (hOldSep a ha hb)
  | insert e =>
    exact hlookup.congr_region fun a ha hb => hf.2.2.2.1 a (hb.trans_le hnew) (hNewSep a ha hb)

/-- The old and new graph regions are available for endpoint lookup
throughout the edit loop. They lie below the heap and outside the tree. -/
structure TreeEditGraphs (R : DSRep PathTreeState) (handle : ℕ)
    (x : R.τ) (st : State) (oldBase newBase vc oldCap newCap : ℕ)
    (oldG newG : MGraph) (edits : List TreeChange) : Prop where
  lookup : TreeEditEndpointSuffix st.mem oldBase newBase vc oldCap newCap oldG newG edits
  oldBelow : oldBase + dynGraphSize vc oldCap ≤ st.regs 3
  newBelow : newBase + dynGraphSize vc newCap ≤ st.regs 3
  oldOutside : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap → ¬ R.foot handle x a
  newOutside : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap → ¬ R.foot handle x a

/-- Set up both graph views from the allocations for a Shift or Rebuild. -/
theorem TreeEditGraphs.of_diff
    {R : DSRep PathTreeState} {handle oldBase newBase vc oldCap newCap : ℕ}
    {x : R.τ} {st : State} {oldG newG : MGraph}
    (hold : DynGraphAt st.mem oldBase vc oldCap oldG)
    (hnew : DynGraphAt st.mem newBase vc newCap newG)
    (hOldBelow : oldBase + dynGraphSize vc oldCap ≤ st.regs 3)
    (hNewBelow : newBase + dynGraphSize vc newCap ≤ st.regs 3)
    (hOldOutside : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap → ¬ R.foot handle x a)
    (hNewOutside : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap → ¬ R.foot handle x a) :
    TreeEditGraphs R handle x st oldBase newBase vc oldCap newCap oldG newG
      (diffTreeChanges oldG.E newG.E) :=
  ⟨TreeEditEndpointSuffix.of_diff hold hnew, hOldBelow, hNewBelow, hOldOutside, hNewOutside⟩

/-- Carry both graph regions and their lookups through an edit, using
the frame of the tree call and any writes to the slot tables. -/
theorem TreeEditGraphs.advance
    {R : DSRep PathTreeState} {handle oldBase newBase vc oldCap newCap ret space : ℕ}
    {x y : R.τ} {st out : State} {oldG newG : MGraph} {edit : TreeChange}
    {rest : List TreeChange} {extra : ℕ → Prop}
    (hg : TreeEditGraphs R handle x st oldBase newBase vc oldCap newCap oldG newG (edit :: rest))
    (hf : R.Respects (fun a => R.foot handle x a ∨ extra a) (st.regs 3)
      space st.mem ret handle y out.mem)
    (hheap : out.regs 3 = ret)
    (hOldExtra : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap → ¬ extra a)
    (hNewExtra : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap → ¬ extra a) :
    TreeEditGraphs R handle y out oldBase newBase vc oldCap newCap oldG newG rest := by
  have hOldSep a hlo hhi := fun ha => Or.elim ha (hg.oldOutside a hlo hhi) (hOldExtra a hlo hhi)
  have hNewSep a hlo hhi := fun ha => Or.elim ha (hg.newOutside a hlo hhi) (hNewExtra a hlo hhi)
  obtain ⟨hOldBelow, hOldOutside⟩ := treeEditGraphRegion_disjoint hf hg.oldBelow hOldSep
  obtain ⟨hNewBelow, hNewOutside⟩ := treeEditGraphRegion_disjoint hf hg.newBelow hNewSep
  exact ⟨hg.lookup.advance hf hg.oldBelow hg.newBelow hOldSep hNewSep,
    hheap.symm ▸ hOldBelow, hheap.symm ▸ hNewBelow, hOldOutside, hNewOutside⟩

/-- Every unread insertion has a payload pointer and fixed-point
record below the heap and outside the tree footprint. -/
structure TreeEditPayloads (R : DSRep PathTreeState) (handle h L : ℕ)
    (x : R.τ) (st : State) (edits : List TreeChange)
    (record : ℕ → ℕ) (value : ℕ → PathEdgeValue) : Prop where
  pointer : ∀ e, TreeChange.insert e ∈ edits → st.mem (st.regs 22 + e) = record e
  payload : ∀ e, TreeChange.insert e ∈ edits → PathEdgeAt st.mem (record e) h L (some (value e))
  pointerBelow : ∀ e, TreeChange.insert e ∈ edits → st.regs 22 + e < st.regs 3
  payloadBelow : ∀ e, TreeChange.insert e ∈ edits → record e + 2 + 4 * L ≤ st.regs 3
  pointerOutside : ∀ e, TreeChange.insert e ∈ edits → ¬ R.foot handle x (st.regs 22 + e)
  payloadOutside : ∀ e, TreeChange.insert e ∈ edits → ∀ a, record e ≤ a →
    a < record e + 2 + 4 * L → ¬ R.foot handle x a

/-- A tree edit retains all unread payloads when its extra writes
avoid their pointers and records. Cut has no extra writes. Link's
extra writes are the two slot bindings. -/
theorem TreeEditPayloads.advance
    {R : DSRep PathTreeState} {handle h L space ret : ℕ} {x y : R.τ} {st out : State}
    {edit : TreeChange} {rest : List TreeChange} {record : ℕ → ℕ} {value : ℕ → PathEdgeValue}
    {extra : ℕ → Prop}
    (hp : TreeEditPayloads R handle h L x st (edit :: rest) record value)
    (hframe : R.Respects (fun a => R.foot handle x a ∨ extra a) (st.regs 3) space
      st.mem ret handle y out.mem)
    (hbase : out.regs 22 = st.regs 22) (hheap : out.regs 3 = ret)
    (hpointer : ∀ e, TreeChange.insert e ∈ rest → ¬ extra (st.regs 22 + e))
    (hpayload : ∀ e, TreeChange.insert e ∈ rest → ∀ a, record e ≤ a →
      a < record e + 2 + 4 * L → ¬ extra a) :
    TreeEditPayloads R handle h L y out rest record value := by
  have hmem {a : ℕ} (ha : a < st.regs 3) (hx : ¬ R.foot handle x a) (he : ¬ extra a) :
      out.mem a = st.mem a :=
    hframe.2.2.2.1 a ha (fun hw => hw.elim hx he)
  have hfresh {a : ℕ} (ha : a < st.regs 3) (hx : ¬ R.foot handle x a) (he : ¬ extra a) :
      ¬ R.foot handle y a := by
    intro hf
    rcases hframe.2.2.2.2 a hf with (hw | ⟨hl, _⟩)
    · exact hw.elim hx he
    · exact (Nat.not_le_of_lt ha) hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hn := List.mem_cons_of_mem edit he
    rw [hbase, hmem (hp.pointerBelow e hn) (hp.pointerOutside e hn) (hpointer e he)]
    exact hp.pointer e hn
  · intro e he
    have hn := List.mem_cons_of_mem edit he
    exact (hp.payload e hn).congr fun a ha hb =>
      hmem (hb.trans_le (hp.payloadBelow e hn)) (hp.payloadOutside e hn a ha hb)
        (hpayload e he a ha hb)
  · intro e he
    rw [hbase, hheap]
    exact (hp.pointerBelow e (List.mem_cons_of_mem edit he)).trans_le hframe.1
  · intro e he
    rw [hheap]
    exact (hp.payloadBelow e (List.mem_cons_of_mem edit he)).trans hframe.1
  · intro e he
    have hn := List.mem_cons_of_mem edit he
    rw [hbase]
    exact hfresh (hp.pointerBelow e hn) (hp.pointerOutside e hn) (hpointer e he)
  · intro e he a ha hb
    have hn := List.mem_cons_of_mem edit he
    exact hfresh (hb.trans_le (hp.payloadBelow e hn)) (hp.payloadOutside e hn a ha hb)
      (hpayload e he a ha hb)

/-- Apply the next deletion and preserve the unread buffer. -/
theorem treeEditIteration_cut_runs {w L constant init link cut bind handle heap base vc ec e slots names edgeCap slotCap : ℕ}
    {G otherG : MGraph} {otherBase otherCap : ℕ} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {rest : List TreeChange}
    {recordOf f g : ℕ → ℕ} {valueOf : ℕ → PathEdgeValue}
    (hentry : cut = op 1)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hg : TreeEditGraphs R handle x st base otherBase vc ec otherCap G otherG
      (.delete e :: rest))
    (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (hbuf : TreeEditBuffer R handle x st (.delete e :: rest))
    (hp : TreeEditPayloads R handle fmt.limbBits L x st (.delete e :: rest) recordOf valueOf)
    (h9 : st.regs 12 = dgETailSlotBase base vc ec)
    (h10 : st.regs 13 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 14 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (hhandle : handle < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hi : LctInv pathPayload s) (hf : pathTreeFits fmt.limbBits L s)
    (hw : 2 * s.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L)
    (hfitNext : pathTreeFits fmt.limbBits L
      (lctCut pathPayload s (G.tail e + 1) (G.head e + 1)))
    (htables : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (htableValues : PathSlotTablesAt st.mem slots names edgeCap slotCap f g)
    (halloc : TreeEditHeap R handle x st)
    (hroom : heap + allocation 1 s.n [handle, G.tail e + 1, G.head e + 1, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditDispatchBound link cut bind ;; treeEditAdvance) st .normal out cost ∧
      out.regs 3 = ret ∧ out.regs 6 = st.regs 6 + 2 ∧
      (∀ r, TreeEditInputReg r → out.regs r = st.regs r) ∧
      TreeEditBuffer R handle y out rest ∧
      TreeEditHeap R handle y out ∧
      TreeEditSlotStorage R handle slots names edgeCap slotCap y ret ∧
      PathSlotTablesAt out.mem slots names edgeCap slotCap f g ∧
      TreeEditGraphs R handle y out base otherBase vc ec otherCap G otherG rest ∧
      TreeEditPayloads R handle fmt.limbBits L y out rest recordOf valueOf ∧
      R.rep handle (lctCut pathPayload s u v) y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 1 s.n [handle, u, v, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 71 := by
  dsimp only
  have hheap : heap < 2 ^ w := by omega
  have hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w :=
    (hg.oldBelow.trans_eq h3).trans hheap.le
  have haddr : st.regs 6 + 1 < 2 ^ w := by
    have hbound := hbuf.bound
    rw [treeEditWords_length] at hbound
    simp only [List.length_cons] at hbound
    rw [h3] at hbound
    omega
  have he : TreeEditEndpointAt st.mem base vc ec G e :=
    hg.lookup (.delete e) List.mem_cons_self
  have htail : G.tail e + 1 < 2 ^ w := (he.tailNameBound.trans_le hvc).succ_le.trans_lt hn
  have hhead : G.head e + 1 < 2 ^ w := (he.headNameBound.trans_le hvc).succ_le.trans_lt hn
  have hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h <;> subst a <;> assumption
  have hpre := treeEditCut_named_pre (constant := constant) (handle := handle)
    (heap := heap) (allocation := allocation) (fmt := fmt) he hvc hi hf hw hwidth hfitNext
  have hfoot := h3 ▸ halloc.below
  have hz := h3 ▸ halloc.zero
  let saved := { st with regs := Function.update st.regs 21 (st.regs 3) }
  obtain ⟨mid, ret, c, y, hd, hret, htag, _, hregs, hrep', hframe, hcost⟩ :=
    treeEditDispatch_cut_runs (st := saved) (ω := ω) hentry himpl he hgraphRoom hvc hn
      rfl (treeEditsAt_cons hbuf.records).1 haddr
      (by simpa [saved] using h9) (by simpa [saved] using h10)
      (by simpa [saved] using h11) (by simpa [saved] using h0) (by simpa [saved] using h3)
      hwords hrep hpre hfoot hz hroom
  have hrun := treeEditDispatchBound_cut (bind := bind) hd htag
  obtain ⟨out, ha, hbuf', hmem, hcursorOut, hsave⟩ :=
    hbuf.advance (p := p) (ω := ω) (by rwa [h3]) hret
      (hregs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
      (hregs 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
      (by rwa [h3])
  change c + R.phi handle y mid.mem ≤
    pathTreeBudget constant L s.n + R.phi handle x st.mem + 54 at hcost
  have hinputs r (hr : TreeEditInputReg r) : out.regs r = st.regs r := by
    obtain ⟨h1, h2, h3', _, h6, h7, h8, h9', h10', h11', h18, h21⟩ := hr.valid
    exact (hsave r h6 h18).trans ((hregs r h1 h2 h3' h7 h8 h9' h10' h11').trans
      (Function.update_of_ne h21 _ _))
  have houtheap := (hsave 3 (by decide) (by decide)).trans hret
  have hfinal : R.Respects (R.foot handle x) heap (allocation 1 s.n
      [handle, G.tail e + 1, G.head e + 1, heap]) st.mem ret handle y out.mem := by
    rwa [hmem]
  have hp' := hp.advance (extra := fun _ => False) (by simpa only [h3, or_false] using hfinal)
    (hinputs 22 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) houtheap (fun _ _ => id) (fun _ _ _ _ _ => id)
  have hg' := hg.advance (extra := fun _ => False) (by simpa only [h3, or_false] using hfinal)
    houtheap (fun _ _ _ => id) (fun _ _ _ => id)
  have halloc' := halloc.advance (extra := fun _ => False)
    (by simpa only [h3, or_false] using hfinal) houtheap (fun _ h => h.elim)
  refine ⟨out, ret, c + 17, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, c + 7, 9, hrun, ha, by omega⟩),
    houtheap, hcursorOut, hinputs, hbuf', halloc', htables.advance hfinal, htables.frame_tables hfinal htableValues, hg', hp', ?_, hfinal, ?_⟩
  · rwa [hmem]
  · rw [hmem]
    omega

/-- After a bound insertion, advance the edit cursor and retain
the linked tree and the slot binding. -/
theorem treeEditBoundIteration_link_runs {w handle ret space slots names edge slot cost : ℕ}
    {dispatch : Stmt} {R : DSRep PathTreeState} {x y : R.τ} {p : Program} {ω : ℕ → Bool}
    {st linked bound : State} {tree : PathTreeState} {rest : List TreeChange}
    (hb : TreeEditBuffer R handle x st (.insert edge :: rest))
    (hr : Runs w p ω (dispatch) st .normal bound cost)
    (htree : R.Respects (R.foot handle x) (st.regs 3) space st.mem ret handle y linked.mem)
    (hbind : (pathSlotBindContract w).post [slots, names, edge, slot, ret] linked.mem ret bound.mem)
    (hrep : R.rep handle tree y bound.mem)
    (hsep : ∀ a, st.regs 6 + 2 ≤ a →
      a < st.regs 6 + 2 + (rest.flatMap treeEditWords).length →
      a ≠ slots + edge ∧ a ≠ names + slot)
    (hheap : bound.regs 3 = ret)
    (hcursor : bound.regs 6 = st.regs 6) (hcount : bound.regs 18 = st.regs 18)
    (hword : st.regs 3 < 2 ^ w) :
    ∃ out, Runs w p ω (dispatch ;; treeEditAdvance) st .normal out
        (cost + 10) ∧
      TreeEditBuffer R handle y out rest ∧ R.rep handle tree y out.mem ∧
      out.mem = bound.mem ∧ out.regs 3 = ret ∧ out.regs 6 = st.regs 6 + 2 ∧
      R.phi handle y out.mem = R.phi handle y bound.mem ∧
      (∀ r, r ≠ 6 → r ≠ 18 → out.regs r = bound.regs r) := by
  obtain ⟨out, ha, hbuf, hm, h3, h6, hregs⟩ :=
    hb.advance_after_link_bind (p := p) (ω := ω) htree hbind hsep hheap hcursor hcount hword
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨bound, cost, 9, hr, ha, by omega⟩),
    hbuf, hm.symm ▸ hrep, hm, h3, h6, by rw [hm], hregs⟩

/-- Apply the next insertion and preserve the unread buffer. -/
theorem treeEditIteration_link_runs {w L constant init link bind slots names handle heap base vc ec e edgeCap slotCap : ℕ}
    {deleteBody : Stmt} {G otherG : MGraph} {otherBase otherCap : ℕ} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {rest : List TreeChange} {recordOf f g : ℕ → ℕ} {valueOf : ℕ → PathEdgeValue}
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hentry : link = op 0)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hg : TreeEditGraphs R handle x st otherBase base vc otherCap ec otherG G
      (.insert e :: rest))
    (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (hbuf : TreeEditBuffer R handle x st (.insert e :: rest))
    (h9 : st.regs 15 = dgETailSlotBase base vc ec)
    (h10 : st.regs 16 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 17 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (h19 : st.regs 19 = slots) (h20 : st.regs 20 = names)
    (hedgeCap : e < edgeCap) (hslotCap : s.freeHead < slotCap)
    (hbufSep : ∀ a, st.regs 6 + 2 ≤ a →
      a < st.regs 6 + 2 + (rest.flatMap treeEditWords).length →
      a ≠ slots + e ∧ a ≠ names + s.freeHead)
    (hp : TreeEditPayloads R handle fmt.limbBits L x st (.insert e :: rest) recordOf valueOf)
    (hOldExtra : ∀ a, otherBase ≤ a → a < otherBase + dynGraphSize vc otherCap →
      a ≠ slots + e ∧ a ≠ names + s.freeHead)
    (hNewExtra : ∀ a, base ≤ a → a < base + dynGraphSize vc ec →
      a ≠ slots + e ∧ a ≠ names + s.freeHead)
    (hpointerSep : ∀ f, TreeChange.insert f ∈ rest →
      st.regs 22 + f ≠ slots + e ∧ st.regs 22 + f ≠ names + s.freeHead)
    (hpayloadSep : ∀ f, TreeChange.insert f ∈ rest → ∀ a, recordOf f ≤ a →
      a < recordOf f + 2 + 4 * L → a ≠ slots + e ∧ a ≠ names + s.freeHead)
    (hhandle : handle < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hi : LctInv pathPayload s) (hf : pathTreeFits fmt.limbBits L s)
    (hw : 2 * s.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L)
    (hconn : ¬ pathTreeConnected s (G.tail e + 1) (G.head e + 1))
    (hfitNext : pathTreeFits fmt.limbBits L
      (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (valueOf e))))
    (htables : TreeEditSlotStorage R handle slots names edgeCap slotCap x heap)
    (htableValues : PathSlotTablesAt st.mem slots names edgeCap slotCap f g)
    (halloc : TreeEditHeap R handle x st)
    (hroom : heap + allocation 0 s.n [handle, G.tail e + 1, G.head e + 1, recordOf e, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditDispatchBoundWithCut link bind deleteBody ;; treeEditAdvance) st .normal out cost ∧
      out.regs 3 = ret ∧ out.regs 6 = st.regs 6 + 2 ∧
      (∀ r, TreeEditInputReg r → out.regs r = st.regs r) ∧
      TreeEditBuffer R handle y out rest ∧
      TreeEditHeap R handle y out ∧
      TreeEditSlotStorage R handle slots names edgeCap slotCap y ret ∧
      PathSlotTablesAt out.mem slots names edgeCap slotCap (Function.update f e s.freeHead) (Function.update g s.freeHead e) ∧
      TreeEditGraphs R handle y out otherBase base vc otherCap ec otherG G rest ∧
      TreeEditPayloads R handle fmt.limbBits L y out rest recordOf valueOf ∧
      R.rep handle (lctLink pathPayload s u v (some (valueOf e))) y out.mem ∧
      R.Respects (fun a => R.foot handle x a ∨ a = slots + e ∨ a = names + s.freeHead) heap (allocation 0 s.n [handle, u, v, recordOf e, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 100 := by
  dsimp only
  have hheap : heap < 2 ^ w := by omega
  have hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w :=
    (hg.newBelow.trans_eq h3).trans hheap.le
  have haddr : st.regs 6 + 1 < 2 ^ w := by
    have hbound := hbuf.bound
    rw [treeEditWords_length] at hbound
    simp only [List.length_cons] at hbound
    rw [h3] at hbound
    omega
  have hhere : TreeChange.insert e ∈ TreeChange.insert e :: rest := List.mem_cons_self
  have hpayloadRoom := (hp.pointerBelow e hhere).trans (show st.regs 3 < 2 ^ w by rwa [h3])
  have hpayload := hp.pointer e hhere
  have hvalue := hp.payload e hhere
  have he : TreeEditEndpointAt st.mem base vc ec G e :=
    hg.lookup (.insert e) List.mem_cons_self
  have htail : G.tail e + 1 < 2 ^ w := (he.tailNameBound.trans_le hvc).succ_le.trans_lt hn
  have hhead : G.head e + 1 < 2 ^ w := (he.headNameBound.trans_le hvc).succ_le.trans_lt hn
  have hrecordWord : recordOf e < 2 ^ w := by
    have hb := (hp.payloadBelow e hhere).trans_eq h3
    omega
  have hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, recordOf e, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h <;> subst a <;> assumption
  have hblock : recordOf e + (2 + 4 * L) ≤ heap := by
    have hb := (hp.payloadBelow e hhere).trans_eq h3
    omega
  have hpre := treeEditLink_named_pre (constant := constant) (handle := handle)
    (heap := heap) (allocation := allocation) (fmt := fmt) he hvc hi hf hw hwidth hconn
    hblock hvalue hfitNext
  have hfoot := h3 ▸ halloc.below
  have hz := h3 ▸ halloc.zero
  obtain ⟨hs, hnames, hsep, hsf, hnf⟩ := htables.bind_words hedgeCap hslotCap
  let saved := { st with regs := Function.update st.regs 21 (st.regs 3) }
  obtain ⟨mid, ret, c, y, hd, hret, htag, hedge, hregs, hrep', hslot, hframe, hcost⟩ :=
    treeEditDispatchWithCut_link_runs (st := saved) (ω := ω) hentry himpl he hgraphRoom hvc hn
      rfl (treeEditsAt_cons hbuf.records).1 haddr
      (by simpa [saved] using h9) (by simpa [saved] using h10)
      (by simpa [saved] using h11) (by simpa [saved] using h0) (by simpa [saved] using h3)
      (by simpa [saved] using hpayloadRoom) (by simpa [saved] using hpayload)
      hvalue hwords hrep hpre hfoot hz hroom
  have regl (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) (h7 : r ≠ 7) (h8 : r ≠ 8)
      (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) := hregs r h1 h2 h3 h4 h7 h8 h9 h10 h11
  have h19' : mid.regs 19 = slots :=
    (regl 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans (by simpa [saved] using h19)
  have h20' : mid.regs 20 = names :=
    (regl 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans (by simpa [saved] using h20)
  have h21' : mid.regs 21 = st.regs 3 :=
    (regl 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans (by simp [saved])
  have hfresh a (ha : a < heap) (ho : ¬ R.foot handle x a) : ¬ R.foot handle y a := by
    intro hy
    rcases hframe.2.2.2.2 a hy with hold | ⟨hnew, _⟩
    · exact ho hold
    · exact (Nat.not_le_of_lt ha) hnew
  have hretWord : ret < 2 ^ w := hframe.2.1.trans_lt hroom
  obtain ⟨bound, cb, hr, hbheap, hsave, hpost, htree, hphi, hcb⟩ :=
    treeEditDispatchBound_link hd htag hbind himpl.1 hrep'
      ⟨h19', h20', hedge, h21', hret⟩ (by rwa [h3])
      (hs.trans_le hframe.1) (hnames.trans_le hframe.1) hsep (hfresh _ hs hsf)
      (hfresh _ hnames hnf) hretWord hframe.2.2.1
  have h6 := (hsave 6 (by decide)).trans
    (regl 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  have h18 := (hsave 18 (by decide)).trans
    (regl 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  obtain ⟨out, hrun, hb', hrep'', houtmem, houtheap, hcursorOut, hpotential, hregisters⟩ :=
    treeEditBoundIteration_link_runs hbuf hr (by rwa [h3]) hpost htree hbufSep hbheap
      (by simpa [saved] using h6) (by simpa [saved] using h18) (by rwa [h3])
  have hframe' := treeEdit_link_bind_respects hframe hpost
  change c + R.phi handle y mid.mem ≤
    pathTreeBudget constant L s.n + R.phi handle x st.mem + 61 at hcost
  have hinputs r (hr : TreeEditInputReg r) : out.regs r = st.regs r := by
    obtain ⟨h1, h2, h3', h4, h6', h7, h8, h9', h10', h11', h18', h21⟩ := hr.valid
    exact (hregisters r h6' h18').trans ((hsave r h3').trans
      ((regl r h1 h2 h3' h4 h7 h8 h9' h10' h11').trans (Function.update_of_ne h21 _ _)))
  have hfinal := show R.Respects
      (fun a => R.foot handle x a ∨ a = slots + e ∨ a = names + s.freeHead) heap
      (allocation 0 s.n [handle, G.tail e + 1, G.head e + 1, recordOf e, heap])
      st.mem ret handle y out.mem by rwa [houtmem]
  have hp' := hp.advance (by rw [h3]; exact hfinal) (hinputs 22 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) houtheap
    (fun f hf he => Or.elim he (hpointerSep f hf).1 (hpointerSep f hf).2)
    (fun f hf a ha hb he => Or.elim he (hpayloadSep f hf a ha hb).1 (hpayloadSep f hf a ha hb).2)
  have hg' := hg.advance (by rw [h3]; exact hfinal) houtheap
    (fun a ha hb h => Or.elim h (hOldExtra a ha hb).1 (hOldExtra a ha hb).2)
    (fun a ha hb h => Or.elim h (hNewExtra a ha hb).1 (hNewExtra a ha hb).2)
  have halloc' := halloc.advance (by rw [h3]; exact hfinal) houtheap (fun a ha => by
    rw [h3]
    exact Or.elim ha (fun he => he.symm ▸ hs) (fun he => he.symm ▸ hnames))
  have htableMid := htables.frame_tables hframe htableValues
  have htableOut := pathSlotBind_tables htableMid hedgeCap hslotCap htables.separate hpost
  rw [← houtmem] at htableOut
  exact ⟨out, ret, cb + 10, y, hrun, houtheap, hcursorOut, hinputs, hb', halloc', htables.advance hframe, htableOut, hg', hp', hrep'', hfinal, by omega⟩

/-- Process records until the unread count reaches zero. -/
@[expose] def treeEditLoop (link cut bind : ℕ) : Stmt :=
  .loop (.reg 18) (treeEditDispatchBound link cut bind ;; treeEditAdvance)

/-- Iterate the named edit dispatch and charge each iteration plus
the decrease in tree potential. The invariant carries the unread list. -/
theorem treeEditLoopWithBody_runs {w : ℕ} {body : Stmt} {p : Program} {ω : ℕ → Bool}
    {Inv : List TreeChange → ℕ → State → Prop} {st : State}
    {changes : List TreeChange} {potential : ℕ} (budget : ℕ)
    (hcount : ∀ xs phi s, Inv xs phi s → s.regs 18 = xs.length)
    (hstep : ∀ edit rest phi s, Inv (edit :: rest) phi s → ∀ bits,
      ∃ out cost phi',
        Runs w p bits body s .normal out cost ∧
        Inv rest phi' out ∧ cost + phi' ≤ budget + phi)
    (hin : Inv changes potential st) :
    ∃ out cost finalPotential,
      Runs w p ω (.loop (.reg 18) body) st .normal out cost ∧ Inv [] finalPotential out ∧
      cost + finalPotential ≤ changes.length * (budget + 2) + potential + 2 := by
  induction changes generalizing st potential with
  | nil =>
    have hzero := hcount [] potential st hin
    have he : (Expr.reg 18).eval w st = some 0 := by simp [Expr.eval, hzero]
    exact ⟨st, 2, potential,
      runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩), hin, by simp [Nat.add_comm]⟩
  | cons edit rest ih =>
    have heq := hcount (edit :: rest) potential st hin
    have he : (Expr.reg 18).eval w st = some (rest.length + 1) := by simp [Expr.eval, heq]
    obtain ⟨next, c, phi, hbody, hnext, hbound⟩ := hstep edit rest potential st hin ω
    obtain ⟨out, d, final, hr, hout, hd⟩ := ih hnext
    refine ⟨out, c + 2 + d, final,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨rest.length + 1, next, c, d, he,
        Nat.succ_ne_zero _, hbody, hr, by simp [Expr.size]; omega⟩)), hout, ?_⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Iterate the tree-only edit dispatcher. -/
theorem treeEditLoop_runs {w link cut bind : ℕ} {p : Program} {ω : ℕ → Bool}
    {Inv : List TreeChange → ℕ → State → Prop} {st : State}
    {changes : List TreeChange} {potential : ℕ} (budget : ℕ)
    (hcount : ∀ xs phi s, Inv xs phi s → s.regs 18 = xs.length)
    (hstep : ∀ edit rest phi s, Inv (edit :: rest) phi s → ∀ bits,
      ∃ out cost phi',
        Runs w p bits (treeEditDispatchBound link cut bind ;; treeEditAdvance) s .normal out cost ∧
        Inv rest phi' out ∧ cost + phi' ≤ budget + phi)
    (hin : Inv changes potential st) :
    ∃ out cost finalPotential,
      Runs w p ω (treeEditLoop link cut bind) st .normal out cost ∧ Inv [] finalPotential out ∧
      cost + finalPotential ≤ changes.length * (budget + 2) + potential + 2 :=
  treeEditLoopWithBody_runs budget hcount hstep hin

/-- Interpret the packed changes as the ordered link-cut edits used
in the proof of Theorem 5.1 (pages 29–30). Insertions use the new
graph and supplied edge payloads, while deletions use the old graph. -/
@[expose] def treeEditApply (oldG newG : MGraph) (value : ℕ → PathEdgeValue)
    (tree : PathTreeState) : TreeChange → PathTreeState
  | .delete e => lctCut pathPayload tree (oldG.tail e + 1) (oldG.head e + 1)
  | .insert e => lctLink pathPayload tree (newG.tail e + 1) (newG.head e + 1) (some (value e))

/-- Cutting an edge leaves the vertex arena size fixed. -/
theorem treeEditCut_n (s : PathTreeState) (u v : ℕ) :
    (lctCut pathPayload s u v).n = s.n := by
  have hn : (lctExposeCost pathPayload (lctRerootCost pathPayload s u).1 v).1.n = s.n := rfl
  unfold lctCut lctCutCost
  split
  · rfl
  · dsimp only
    generalize h : (lctExposeCost pathPayload (lctRerootCost pathPayload s u).1 v).1 = t
    rw [h] at hn
    split
    · exact hn
    · try dsimp only
      split <;> first | exact hn | rfl | (split <;> first | exact hn | rfl)
private theorem treeEditLink_n (s : PathTreeState) (u v : ℕ) (value : PathEdgeValue) :
    (lctLink pathPayload s u v (some value)).n = s.n := by
  have hn : (lctRerootCost pathPayload (lctRerootCost pathPayload s v).1 u).1.n = s.n := rfl
  unfold lctLink lctLinkCost
  split
  · rfl
  · dsimp only
    generalize h : (lctRerootCost pathPayload (lctRerootCost pathPayload s v).1 u).1 = t
    rw [h] at hn
    split <;> exact hn

/-- A tree edit keeps the vertex arena size. This fixes the same
tree budget and vertex-index bounds throughout the loop. -/
theorem treeEditApply_n (oldG newG : MGraph) (value : ℕ → PathEdgeValue)
    (tree : PathTreeState) (change : TreeChange) :
    (treeEditApply oldG newG value tree change).n = tree.n := by
  cases change with
  | delete e => exact treeEditCut_n tree _ _
  | insert e => exact treeEditLink_n tree _ _ (value e)

/-- The packed loop implements the ordered model edits, with the
unread suffix and tree representation in its invariant. Each branch
uses its verified iteration once the remaining machine inputs fit. -/
theorem treeEditLoop_fold_runs {w link cut bind handle constant L : ℕ}
    {p : Program} {ω : ℕ → Bool} {R : DSRep PathTreeState}
    {st : State} {tree : PathTreeState} {x : R.τ} {changes : List TreeChange}
    (oldG newG : MGraph) (value : ℕ → PathEdgeValue)
    (Ready : List TreeChange → PathTreeState → R.τ → State → Prop)
    (hready : Ready changes tree x st)
    (hbuf : TreeEditBuffer R handle x st changes) (hrep : R.rep handle tree x st.mem)
    (hstep : ∀ edit rest current token before,
      TreeEditBuffer R handle token before (edit :: rest) →
      R.rep handle current token before.mem → current.n = tree.n →
      Ready (edit :: rest) current token before → ∀ bits,
      ∃ after cost nextToken,
        Runs w p bits (treeEditDispatchBound link cut bind ;; treeEditAdvance) before .normal after cost ∧
        TreeEditBuffer R handle nextToken after rest ∧
        R.rep handle (treeEditApply oldG newG value current edit) nextToken after.mem ∧
        Ready rest (treeEditApply oldG newG value current edit) nextToken after ∧
        cost + R.phi handle nextToken after.mem ≤ pathTreeBudget constant L current.n + 100 + R.phi handle token before.mem) :
    ∃ out cost y,
      Runs w p ω (treeEditLoop link cut bind) st .normal out cost ∧
      TreeEditBuffer R handle y out [] ∧
      R.rep handle (changes.foldl (treeEditApply oldG newG value) tree) y out.mem ∧
      Ready [] (changes.foldl (treeEditApply oldG newG value) tree) y out ∧
      cost + R.phi handle y out.mem ≤
        changes.length * (pathTreeBudget constant L tree.n + 102) + R.phi handle x st.mem + 2 := by
  let budget := pathTreeBudget constant L tree.n + 100
  let target := changes.foldl (treeEditApply oldG newG value) tree
  let Inv := fun rest phi (current : State) =>
    ∃ t token, TreeEditBuffer R handle token current rest ∧ R.rep handle t token current.mem ∧
      rest.foldl (treeEditApply oldG newG value) t = target ∧ t.n = tree.n ∧
      Ready rest t token current ∧ phi = R.phi handle token current.mem
  obtain ⟨out, c, phi, hr, hf, hc⟩ :=
    treeEditLoop_runs (p := p) (ω := ω) (Inv := Inv) budget
      (fun _ _ _ ⟨_, _, hb, _⟩ => hb.count)
      (fun edit rest phi before ⟨t, token, hb, hrep, ht, hn, hready, hp⟩ bits => by
        obtain ⟨after, cost, nextToken, hr, hb', hrep', hready', hc⟩ :=
          hstep edit rest t token before hb hrep hn hready bits
        rw [hn] at hc
        exact ⟨after, cost, _, hr, ⟨_, nextToken, hb', hrep', ht,
          (treeEditApply_n oldG newG value t edit).trans hn, hready', rfl⟩, hp.symm ▸ hc⟩)
      (show Inv changes (R.phi handle x st.mem) st from ⟨tree, x, hbuf, hrep, rfl, rfl, hready, rfl⟩)
  obtain ⟨t, token, hb, hp, ht, _, hready, hphi⟩ := hf
  change t = target at ht
  rw [ht] at hp hready
  exact ⟨out, c, token, hr, hb, hp, hready,
    by simpa [budget, Nat.add_assoc] using (hphi ▸ hc)⟩

end MinCostFlow.MinRatio
