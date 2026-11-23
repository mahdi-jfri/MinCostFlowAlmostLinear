module

public import MinCostFlow.MinRatio.FreshBatchInvariant
import WordRAM.Memory

/-!
# Advancing the fresh-name scan invariant

A dispatcher call changes the name tables and writes one translated
record. The input suffix and the earlier output survive its writes.
The resulting two cursors, table state, and remaining record count
satisfy the same invariant for the tail of the input.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

private theorem record_width {G : MGraph} {f g : ℕ → ℕ} {next cap : ℕ}
    {record : Update} (hfit : FreshRecordFits cap record) :
    (updateWords (translateUpdate G f g next record).2.2.2.2).length =
      (updateWords record).length := by
  cases record with
  | split _ _ _ => cases hfit
  | insert _ _ _ => rfl
  | delete _ => rfl

private theorem next_le {G : MGraph} {f g : ℕ → ℕ} {next : ℕ} {record : Update} :
    (translateUpdate G f g next record).2.2.2.1 ≤ next + 1 := by
  cases record <;> first | exact Nat.le_succ _ | exact le_rfl

/-- The already written records and unread suffix remain in the
required layout after a verified dispatcher step. -/
def FreshBatchInvariant.advance {w : ℕ} {region : FreshBatchRegions} {target : FreshBatchResult}
    {record : Update} {rest : List Update} {st st' : State} {initial : ℕ → ℕ} (hsep : region.Separated)
    (h : FreshBatchInvariant w region target initial (record :: rest) st)
    (hstep : st'.regs 0 = st.regs 0 + (updateWords record).length ∧
      st'.regs 1 = st.regs 1 ∧ st'.regs 2 = st.regs 2 ∧ st'.regs 3 = st.regs 3 ∧
      st'.regs 4 = st.regs 4 + (updateWords record).length ∧ st'.regs 5 = st.regs 5 - 1 ∧
      (freshRecordContract w record (freshRecordName h.forward h.next record)).post
        [st.regs 0, st.regs 1, st.regs 2, st.regs 3, st.regs 4] st.mem (st'.regs 4) st'.mem) :
    FreshBatchInvariant w region target initial rest st' := by
  rcases hstep with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hpost⟩
  rcases h.registers with ⟨h1, h2, h3, h5⟩
  rcases hsep with ⟨hfo, hin, hco, hdis, hfco, hico⟩
  rw [h1, h2, h3] at hpost
  have hrf := h.recordFits record List.mem_cons_self
  have hname : h.next < region.internalCap := by
    have hs := h.spareNames
    simp only [List.length_cons] at hs
    omega
  have hsrcOut : region.input ≤ region.output :=
    h.inputStart.trans ((Nat.le_add_right _ _).trans h.inputEnd)
  have hbeforeOut : region.output ≤ st.regs 4 := h.outputCursor ▸ Nat.le_add_right _ _
  have hbound : region.input ≤ st.regs 4 := hsrcOut.trans hbeforeOut
  have hmachine := freshRecord_model (G := h.external) h.tables (hfo.trans hbound)
    (hin.trans hbound) (hco.trans_le hbound) hdis hfco hico
    (freshRecordName_model h.forward hrf hname) hpost
  have hframe := freshRecord_frame_interval hfo hin hco
    (freshRecordName_frame h.forward hrf hname) hpost
  let result := translateUpdate h.external h.forward h.inverse h.next record
  have hg := freshRecord_graph_valid h.fresh h.valid.1
  change FreshTablesAt st'.mem region.forward region.inverse region.counter region.externalCap
    region.internalCap result.2.1 result.2.2.1 result.2.2.2.1 ∧
      ListAt st'.mem (st.regs 4) (updateWords result.2.2.2.2) ∧ _ at hmachine
  rcases hmachine with ⟨htables, hwritten, _, hz⟩
  have hwidth : (updateWords result.2.2.2.2).length = (updateWords record).length := record_width hrf
  have hsum : ((record :: rest).flatMap updateWords).length =
      (updateWords record).length + (rest.flatMap updateWords).length := by
    simp [List.flatMap_cons]
  have hnext : result.2.2.2.1 ≤ h.next + 1 := next_le
  have hvalid : result.1.BatchIsValid rest := by
    have hext : result.1 = h.external.applyUpdate record := by cases record <;> rfl
    rw [hext]
    exact h.valid.2
  refine {
    external := result.1
    internal := h.internal.applyUpdate result.2.2.2.2
    forward := result.2.1
    inverse := result.2.2.1
    next := result.2.2.2.1
    written := h.written ++ [result.2.2.2.2]
    fresh := hg.1
    valid := hvalid
    inputFits := ?_
    recordFits := fun u hu => h.recordFits u (List.mem_cons_of_mem _ hu)
    spareNames := ?_
    inputStart := ?_
    inputEnd := ?_
    outputCursor := ?_
    outputEnd := ?_
    leftWord := ?_
    registers := ?_
    tables := htables
    inputWords := ?_
    outputWords := ?_
    zero := hz
    frame := ?_
    targetEq := ?_ }
  · intro x hx
    apply h.inputFits x
    exact List.mem_append_right _ hx
  · have hs := h.spareNames
    simp only [List.length_cons] at hs
    omega
  · exact h.inputStart.trans (hr0 ▸ Nat.le_add_right _ _)
  · have he := h.inputEnd
    rw [hsum] at he
    omega
  · rw [hr4, h.outputCursor, List.flatMap_append, List.flatMap_singleton,
      List.length_append, hwidth, Nat.add_assoc]
  · have he := h.outputEnd
    rw [hsum] at he
    omega
  · exact (Nat.lt_succ_self rest.length).trans h.leftWord
  · exact ⟨hr1.trans h1, hr2.trans h2, hr3.trans h3, by rw [hr5, h5]; simp⟩
  · have hrest := (listAt_append.mp h.inputWords).2
    rw [hr0]
    intro j hj
    have ha := h.inputStart
    have he := h.inputEnd
    rw [hsum] at he
    rw [hframe _ (by omega) (by omega)]
    exact hrest j hj
  · rw [List.flatMap_append, List.flatMap_singleton]
    apply listAt_append.mpr
    refine ⟨?_, ?_⟩
    · intro j hj
      have he := h.outputCursor
      rw [hframe _ (hsrcOut.trans (Nat.le_add_right _ _)) (by omega)]
      exact h.outputWords j hj
    · rw [← h.outputCursor]
      exact hwritten
  · intro a ha hmut
    have hsafe :
        match (motive := Update → Prop) record with
        | .insert e _ _ => a ≠ region.forward + e ∧
            a ≠ region.inverse + freshRecordName h.forward h.next record ∧ a ≠ region.counter
        | .delete _ => True
        | .split .. => False := by
      cases record with
      | split _ _ _ => exact hrf
      | delete e => trivial
      | insert e u v =>
        have he : e < region.externalCap := hrf
        change a ≠ region.forward + e ∧ a ≠ region.inverse + h.next ∧ a ≠ region.counter
        refine ⟨?_, ?_, fun h => hmut (Or.inl h)⟩
        · intro heq
          exact hmut (Or.inr (Or.inl ⟨by omega, by omega⟩))
        · intro heq
          exact hmut (Or.inr (Or.inr ⟨by omega, by omega⟩))
    exact (freshRecord_frame_before (ha.trans_le hbeforeOut) hsafe hpost).trans (h.frame a ha hmut)
  · have ht := h.targetEq
    dsimp only [translateBatch] at ht
    change
      (let suffix := translateBatch result.1 result.2.1 result.2.2.1 result.2.2.2.1 rest
       (suffix.1, suffix.2.1, suffix.2.2.1, suffix.2.2.2.1,
         (h.written ++ [result.2.2.2.2]) ++ suffix.2.2.2.2)) = target
    simp only [List.append_assoc, List.singleton_append]
    exact ht

end MinCostFlow.MinRatio
