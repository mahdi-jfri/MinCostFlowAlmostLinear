module

public import MinCostFlow.MinRatio.FreshBatchAdvance
import WordRAM.Memory

/-!
# The fresh-name scan computes the model batch result

Algorithm 2 (page 29) translates the updates in order. Each iteration of
the machine scan reads the next input record and produces the matching
translated record. The loop proof carries the model's exact suffix
result and the two name maps. The cost is linear in the number of records
of the IPM's fixed-graph refresh, which has no splits.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

private theorem sum_unit_cost (updates : List Update) :
    (updates.map (fun _ => (160 : ℕ))).sum = 160 * updates.length := by
  induction updates with
  | nil => rfl
  | cons u rest ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- The scan loop contains no random instruction. -/
theorem freshBatchLoop_noRand (dispatch : ℕ) : (freshBatchLoop dispatch).NoRand := by
  exact freshBatchStep_noRand dispatch

/-- The scan produces the model's entire translated list and final tables
at cost at most `162 * rest.length + 2`. The count lives in register 5. -/
theorem freshBatchLoop_triple {w dispatch : ℕ} {p : Program}
    {region : FreshBatchRegions} {target : FreshBatchResult} {initial : ℕ → ℕ}
    (hsep : region.Separated) (updates : List Update)
    (hdispatch : ∀ record name, MeetsContract w p dispatch (freshRecordContract w record name)) :
    Triple w p (fun st => Nonempty (FreshBatchInvariant w region target initial updates st))
      (freshBatchLoop dispatch) (normalPost (FreshBatchDone region target initial))
      (fun _ => 162 * updates.length + 2) := by
  unfold freshBatchLoop
  have hn : ∀ st, Nonempty (FreshBatchInvariant w region target initial [] st) →
      (Expr.reg 5).eval w st = some 0 ∧ FreshBatchDone region target initial st := by
    intro st ⟨h⟩
    exact ⟨congrArg some h.registers.2.2.2, h.done⟩
  have hs : ∀ record rest st, Nonempty (FreshBatchInvariant w region target initial (record :: rest) st) →
      ∃ v, (Expr.reg 5).eval w st = some v ∧ v ≠ 0 ∧
        Triple w p (fun s => s = st) (freshBatchStep dispatch)
          (fun o s' => match o with
            | .returned _ => False
            | .normal => Nonempty (FreshBatchInvariant w region target initial rest s'))
          (fun _ => 160) := by
    intro record rest st ⟨h⟩
    rcases h.registers with ⟨h1, h2, h3, h5⟩
    rcases hsep with ⟨hf, hi, hc, hdis, hfc, hic⟩
    have hrem : 0 < st.regs 5 := by rw [h5]; simp
    have hremWord : st.regs 5 < 2 ^ w := h5 ▸ h.leftWord
    have hinput := h.inputEnd
    have houtput := h.outputEnd
    have hsum : ((record :: rest).flatMap updateWords).length =
        (updateWords record).length + (rest.flatMap updateWords).length := by
      simp [List.flatMap_cons]
    rw [hsum] at hinput houtput
    have hbefore : region.output ≤ st.regs 4 := h.outputCursor ▸ Nat.le_add_right _ _
    have hbelow : region.input ≤ st.regs 4 := by have hh := h.inputStart; omega
    have hsrc : st.regs 0 + (updateWords record).length ≤ st.regs 4 := by omega
    have hroom : st.regs 4 + (updateWords record).length < 2 ^ w := by omega
    have hf' : region.forward + region.externalCap ≤ st.regs 4 := hf.trans hbelow
    have hi' : region.inverse + region.internalCap ≤ st.regs 4 := hi.trans hbelow
    have hc' : region.counter < st.regs 4 := hc.trans_le hbelow
    have hrecord : ListAt st.mem (st.regs 0) (updateWords record) :=
      (listAt_append.mp h.inputWords).1
    have hname : h.next < region.internalCap := by
      have hspare := h.spareNames
      simp only [List.length_cons] at hspare
      omega
    have hpre := freshRecord_pre_of_tables h.fresh h.valid.1 h.tables hrecord
      (h.recordFits record List.mem_cons_self) hname
      (fun x hx => h.inputFits x (List.mem_append_left _ hx)) hsrc hroom
      hf' hi' hc' hdis hfc hic h.zero
    rw [← h1, ← h2, ← h3] at hpre
    have hw : ∀ x ∈ [st.regs 0, st.regs 1, st.regs 2, st.regs 3, st.regs 4], x < 2 ^ w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega
    have ht := freshBatchStep_triple record
      (hdispatch record (freshRecordName h.forward h.next record)) hpre hw
      (Nat.lt_of_le_of_lt hsrc (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hroom))
      hroom hrem hremWord
    refine ⟨st.regs 5, rfl, Nat.ne_of_gt hrem, ?_⟩
    refine ht.strengthen_post ?_
    intro o st' hp
    cases o with
    | returned _ => exact hp
    | normal => exact ⟨h.advance ⟨hf, hi, hc, hdis, hfc, hic⟩ hp⟩
  have hloop := Triple.loop_list (w := w) (p := p) (e := .reg 5)
    (Inv := fun rest st => Nonempty (FreshBatchInvariant w region target initial rest st))
    (Q := normalPost (FreshBatchDone region target initial)) (fun _ => 160) hn hs updates
  refine hloop.mono_cost ?_
  intro _ _
  simp only [Expr.size_reg, sum_unit_cost]
  omega

/-- The scan can use the dispatcher, insert, and delete bodies from
the same program, with no additional procedure specification assumed. -/
theorem freshBatchLoop_triple_of_placement {w dispatch ins del : ℕ} {p : Program}
    {region : FreshBatchRegions} {target : FreshBatchResult} {initial : ℕ → ℕ}
    (hsep : region.Separated) (updates : List Update)
    (hd : p.HasAt dispatch [freshRecordBody ins del])
    (hi : p.HasAt ins [freshInsertBody]) (he : p.HasAt del [freshDeleteBody]) :
    Triple w p (fun st => Nonempty (FreshBatchInvariant w region target initial updates st))
      (freshBatchLoop dispatch) (normalPost (FreshBatchDone region target initial))
      (fun _ => 162 * updates.length + 2) :=
  freshBatchLoop_triple hsep updates fun record _ =>
    freshRecord_meetsContract record hd (fun _ _ _ => freshInsert_meetsContract hi)
      (fun _ => freshDelete_meetsContract he)

end MinCostFlow.MinRatio
