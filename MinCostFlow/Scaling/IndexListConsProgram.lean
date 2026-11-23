module

public import MinCostFlow.Scaling.IndexListLayout
public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Entry

/-!
# Allocating an immutable edge-list node

The traversal's list push writes an edge index and the old tail pointer to
two fresh words. The shared pair writer performs exactly those stores.
This file gives that same procedure its linked-list contract: the new head
is the old heap pointer, the new heap is two cells later, and every old
represented list is preserved by the heap frame. The cost remains 14.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The old tail is represented below the heap and the new pointer is
nonzero, so zero continues to denote only an empty list. -/
def indexListConsContract (w lo : ℕ) {m : ℕ} (e : Fin m) (es : List (Fin m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ tail heap, args = [e.val, tail, heap] ∧
      0 < heap ∧ lo ≤ heap ∧ IndexListAt mem lo heap tail es)
    (fun args _ mem' => IndexListAt mem' lo (heapArg args+2) (heapArg args) (e :: es))
    (fun _ _ => 14) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args+2 }

/-- The existing deterministic pair writer also computes a list cons node
with the exact pointer, heap increment, frame, and constant cost. -/
theorem indexListCons_meetsContract {w b lo m : ℕ} {p : Program}
    (hp : p.HasAt b wordPairModule) (e : Fin m) (es : List (Fin m)) :
    MeetsContract w p b (indexListConsContract w lo e es) := by
  intro args mem pos ω hwords hpre
  obtain ⟨⟨tail, heap, rfl, hpositive, hlower, hat⟩, hzero, hspace⟩ := hpre
  obtain ⟨body, hbody, o, st, cost, hrun, hpost, hcost⟩ :=
    wordPair_meetsContract hp [e.val, tail, heap] mem pos ω hwords
      ⟨⟨e.val, tail, heap, rfl⟩, hzero, hspace⟩
  obtain ⟨⟨hstart, hend, hframe, hzero', hpairs⟩, hout⟩ := hpost
  change (∀ x < heap, st.mem x = mem x) at hframe
  change ListAt st.mem heap [e.val, tail] at hpairs
  have htail : IndexListAt st.mem lo (heap+2) tail es := by
    apply (hat.of_agree (fun x _ hx => hframe x hx)).mono le_rfl
    omega
  have hvalue : st.mem heap = e.val := by
    have h := hpairs 0 (by change 0 < 2; decide)
    change st.mem (heap+0) = e.val at h
    simpa only [Nat.add_zero] using h
  have hnext : st.mem (heap+1) = tail := hpairs 1 (by change 1 < 2; decide)
  refine ⟨body, hbody, o, st, cost, hrun, ?_, hcost⟩
  change (heap ≤ o.value ∧ o.value ≤ heap+2 ∧ (∀ x < heap, st.mem x = mem x) ∧
    ZeroFrom st.mem o.value ∧ IndexListAt st.mem lo (heap+2) heap (e :: es)) ∧ o.value = heap+2
  exact ⟨⟨hstart, hend, hframe, hzero', .cons hpositive hlower le_rfl hvalue hnext htail⟩, hout⟩

/-- Arbitrary finite tails and head indices have simultaneous list-layout,
argument, and fresh-allocation premises with nodes above address zero. -/
theorem exists_indexListCons_pre {m : ℕ} (e : Fin m) (es : List (Fin m)) :
    ∃ w mem tail heap, (∀ x ∈ [e.val, tail, heap], x < 2 ^ w) ∧
      (indexListConsContract w 1 e es).pre [e.val, tail, heap] mem := by
  obtain ⟨mem, heap, tail, hheap, hat, hzero⟩ := exists_indexListAt es
  let w := m+heap+3
  have hw : m+heap+3 < 2 ^ w := Nat.lt_two_pow_self
  have he := e.isLt
  have htail := hat.pointer_le
  refine ⟨w, mem, tail, heap, ?_, ⟨tail, heap, rfl, by omega, hheap, hat⟩, hzero, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · change heap+2 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
