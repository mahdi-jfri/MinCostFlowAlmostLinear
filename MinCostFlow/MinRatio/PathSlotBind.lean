module

public import WordRAM.Layout
public import Mathlib.Data.Finset.Insert
import WordRAM.Tactic

/-!
# Recording the association between an edge and a tree slot

Section 6 (pages 29–30) maintains edge values as the spanning tree
changes. When a tree operation returns a slot for an edge, record
both directions of the association. The forward entry supports Query.
The inverse entry lets Detect recover the edge from a returned slot.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The two bounded tables used by the slot lookups. The caller tracks
which entries are live. -/
def PathSlotTablesAt (mem : ℕ → ℕ) (slots names edgeCap slotCap : ℕ)
    (slot name : ℕ → ℕ) : Prop :=
  (∀ e < edgeCap, mem (slots + e) = slot e) ∧
  (∀ s < slotCap, mem (names + s) = name s)

/-- Arguments are the two table bases, internal name, slot, and heap. -/
def pathSlotBindBody : Stmt :=
  .store (.bin .add (.reg 0) (.reg 2)) (.reg 3) ;;
  .store (.bin .add (.reg 1) (.reg 3)) (.reg 2) ;;
  .ret (.reg 4)

/-- Record the association in two distinct cells below the heap. -/
def pathSlotBindContract (w : ℕ) : Contract where
  pre args mem := ∃ slots names edge slot heap, args = [slots, names, edge, slot, heap] ∧
    slots + edge < heap ∧ names + slot < heap ∧ slots + edge ≠ names + slot ∧
    heap < 2 ^ w ∧ ZeroFrom mem heap
  post args mem ret mem' :=
    ret = heapArg args ∧
    mem' = Function.update (Function.update mem (args.getD 0 0 + args.getD 2 0)
      (args.getD 3 0)) (args.getD 1 0 + args.getD 3 0) (args.getD 2 0) ∧ ZeroFrom mem' ret
  cost _ _ := 16

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The binding takes at most 16 steps, writes only the two entries,
and returns the same heap. -/
theorem pathSlotBind_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.HasAt entry [pathSlotBindBody]) :
    MeetsContract w p entry (pathSlotBindContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨slots, names, edge, slot, heap, rfl, hs, hn, hsep, hheap, hz⟩ := hpre
  have hsw : slots + edge < 2 ^ w := hs.trans hheap
  have hnw : names + slot < 2 ^ w := hn.trans hheap
  have hew := hwords edge (by simp)
  have hslw := hwords slot (by simp)
  apply runs_start_le
  unfold pathSlotBindBody
  refine runs_seq_store_le (x := slots + edge) (v := slot) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := names + slot) (v := edge) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := heap) (by eval_expr) ⟨rfl, rfl, ?_⟩ ?_
  · intro x hx
    change heap ≤ x at hx
    change Function.update (Function.update mem (slots + edge) slot) (names + slot) edge x = 0
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz x hx
  · change 14 ≤ 16
    decide

/-- Binding one edge updates precisely the corresponding entries of
the two abstract slot maps. -/
theorem pathSlotBind_tables {w slots names edge slot heap ret edgeCap slotCap : ℕ}
    {f g : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (ht : PathSlotTablesAt mem slots names edgeCap slotCap f g)
    (he : edge < edgeCap) (hs : slot < slotCap)
    (hsep : slots + edgeCap ≤ names ∨ names + slotCap ≤ slots)
    (hout : (pathSlotBindContract w).post [slots, names, edge, slot, heap] mem ret mem') :
    PathSlotTablesAt mem' slots names edgeCap slotCap
      (Function.update f edge slot) (Function.update g slot edge) := by
  have hmem := hout.2.1
  change mem' = Function.update (Function.update mem (slots + edge) slot) (names + slot) edge at hmem
  rw [hmem]
  constructor
  · intro e hcap
    rw [Function.update_of_ne (by omega : slots + e ≠ names + slot)]
    by_cases heq : e = edge
    · subst e
      simp only [Function.update_self]
    · rw [Function.update_of_ne heq, Function.update_of_ne (by omega)]
      exact ht.1 e hcap
  · intro s hcap
    by_cases heq : s = slot
    · subst s
      simp only [Function.update_self]
    · rw [Function.update_of_ne heq, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega : names + s ≠ slots + edge)]
      exact ht.2 s hcap

/-- If the edge is new and the slot is free among live associations,
binding preserves both inverse identities on the enlarged live sets. -/
theorem pathSlotBind_inverse (edges slots : Finset ℕ) (f g : ℕ → ℕ)
    {edge slot : ℕ} (he : edge ∉ edges) (hs : slot ∉ slots)
    (hf : ∀ e ∈ edges, f e ∈ slots ∧ g (f e) = e)
    (hg : ∀ s ∈ slots, g s ∈ edges ∧ f (g s) = s) :
    let f' := Function.update f edge slot
    let g' := Function.update g slot edge
    (∀ e ∈ insert edge edges, f' e ∈ insert slot slots ∧ g' (f' e) = e) ∧
    (∀ s ∈ insert slot slots, g' s ∈ insert edge edges ∧ f' (g' s) = s) := by
  dsimp only
  constructor
  · intro e he'
    rcases Finset.mem_insert.mp he' with rfl | hold
    · simp
    · have hne : e ≠ edge := fun h => he (h ▸ hold)
      obtain ⟨hslot, hback⟩ := hf e hold
      have hnslot : f e ≠ slot := fun h => hs (h ▸ hslot)
      rw [Function.update_of_ne hne, Function.update_of_ne hnslot]
      exact ⟨Finset.mem_insert_of_mem hslot, hback⟩
  · intro s hs'
    rcases Finset.mem_insert.mp hs' with rfl | hold
    · simp
    · have hne : s ≠ slot := fun h => hs (h ▸ hold)
      obtain ⟨hedge, hback⟩ := hg s hold
      have hnedge : g s ≠ edge := fun h => he (h ▸ hedge)
      rw [Function.update_of_ne hne, Function.update_of_ne hnedge]
      exact ⟨Finset.mem_insert_of_mem hedge, hback⟩

/-- Cutting a bound edge removes both live entries. The stored cells
may be reused by the next bind, since queries consult only live entries. -/
theorem pathSlotCut_inverse (edges slots : Finset ℕ) (f g : ℕ → ℕ)
    {edge : ℕ} (he : edge ∈ edges)
    (hf : ∀ e ∈ edges, f e ∈ slots ∧ g (f e) = e)
    (hg : ∀ s ∈ slots, g s ∈ edges ∧ f (g s) = s) :
    (∀ e ∈ edges.erase edge, f e ∈ slots.erase (f edge) ∧ g (f e) = e) ∧
    (∀ s ∈ slots.erase (f edge), g s ∈ edges.erase edge ∧ f (g s) = s) := by
  constructor
  · intro e hem
    obtain ⟨hne, hae⟩ := Finset.mem_erase.mp hem
    obtain ⟨hs, hback⟩ := hf e hae
    have hslot : f e ≠ f edge := by
      intro heq
      apply hne
      exact hback.symm.trans ((congrArg g heq).trans (hf edge he).2)
    exact ⟨Finset.mem_erase.mpr ⟨hslot, hs⟩, hback⟩
  · intro s hsm
    obtain ⟨hne, hst⟩ := Finset.mem_erase.mp hsm
    obtain ⟨hedge, hback⟩ := hg s hst
    have hne' : g s ≠ edge := by
      intro heq
      apply hne
      exact hback.symm.trans (congrArg f heq)
    exact ⟨Finset.mem_erase.mpr ⟨hne', hedge⟩, hback⟩

/-- A tree operation that leaves the two slot tables outside its
footprint preserves all stored associations. -/
theorem PathSlotTablesAt.congr {mem mem' : ℕ → ℕ}
    {slots names edgeCap slotCap : ℕ} {f g : ℕ → ℕ}
    (ht : PathSlotTablesAt mem slots names edgeCap slotCap f g)
    (hf : ∀ e < edgeCap, mem' (slots + e) = mem (slots + e))
    (hg : ∀ s < slotCap, mem' (names + s) = mem (names + s)) :
    PathSlotTablesAt mem' slots names edgeCap slotCap f g :=
  ⟨fun e he => (hf e he).trans (ht.1 e he), fun s hs => (hg s hs).trans (ht.2 s hs)⟩

end MinCostFlow.MinRatio
