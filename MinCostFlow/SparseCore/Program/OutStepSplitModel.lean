module

public import MinCostFlow.SparseCore.Program.OutStepIns
public import MinCostFlow.SparseCore.Program.OutStepBridge

/-!
# What one split of the output step writes

A split round of the output step (`osSplitIter`) reads the split list `Y` of the helper, writes
a first record of the split from the ends of `Y` whose edge is in the graph, applies it, and then
rewrites the record and writes the edit from the incidence list `L` of the vertex of the smaller
side. This file proves, in the model, what these lists give.

* `keyFilterMem_endEdges`: the filter on the keys of `Y` gives the edge lists `endEdges`.
* `DynGraphAt.incList`: the incidence list of a vertex in the stored graph, as keys of its ends.
* `updateAt_split_of_lists`: the edge lists of a side give a record of the split (`UpdateAt`).
* `outSplitEdit_eq_incList`: the edit of the smaller side, read from its incidence list, is
  `outSplitEdit`, and the list has `min (deg v) (deg v')` keys.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

theorem endKey_mod_two (x : End) : endKey x % 2 = if x.2 then 0 else 1 := by
  obtain ⟨e, b⟩ := x
  cases b <;> simp [endKey] <;> omega

theorem endKey_div_two (x : End) : endKey x / 2 = x.1 := by
  obtain ⟨e, b⟩ := x
  cases b <;> simp [endKey] <;> omega

/-- **The filter on the keys of a list of ends** keeps the edges of the ends on one side whose
edge is present. -/
theorem keyFilterMem_endEdges {mem : ℕ → ℕ} {pb eCap : ℕ} {E : Finset ℕ} {Y : List End}
    (hpres : ∀ e < eCap, mem (pb + e) = if e ∈ E then 1 else 0) (hY : ∀ x ∈ Y, x.1 < eCap)
    (b : Bool) :
    keyFilterMem mem pb (Y.map endKey) (if b then 0 else 1) = endEdges Y E b := by
  unfold keyFilterMem endEdges
  rw [List.filter_map, List.map_map]
  have hf : ∀ x ∈ Y, ((fun k => decide (k % 2 = (if b then 0 else 1) ∧ mem (pb + k / 2) = 1)) ∘
      endKey) x = (x.2 == b && decide (x.1 ∈ E)) := by
    intro x hx
    simp only [Function.comp, endKey_mod_two, endKey_div_two, hpres x.1 (hY x hx)]
    obtain ⟨e, c⟩ := x
    cases b <;> cases c <;> by_cases he : e ∈ E <;> simp [he]
  rw [List.filter_congr hf]
  apply List.map_congr_left
  intro x _
  simp [endKey_div_two]

/-- The keys of a list read back as ends give back the keys. -/
theorem map_endKey_endOfKey (L : List ℕ) : (L.map endOfKey).map endKey = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left
  intro k _
  exact endKey_endOfKey k

/-- **The incidence list of a vertex** of the stored graph: a doubly linked list of the keys of
the ends at the vertex. -/
theorem DynGraphAt.incList {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) {x : ℕ} (hx : x ∈ G.V) :
    mem (dgExtToIntBase a vCap + x) < vCap ∧
    ∃ L : List ℕ, IsDoublyLinkedList mem (dgHePrevBase a vCap eCap) (dgHeNextBase a vCap eCap)
      (dgIncHeadBase a vCap + mem (dgExtToIntBase a vCap + x)) (2 * eCap) L ∧
      ∀ k, k ∈ L ↔ k < 2 * eCap ∧ (endOfKey k).1 ∈ G.E ∧ G.src (endOfKey k) = x := by
  obtain ⟨hval, hV, -, -, -, -, -, -, -, hext, -, -, -, hslot, incL, hinc⟩ := hG
  have hsV := (hext x hx).1
  have hs := hV _ hsV
  refine ⟨hs, incL (mem (dgExtToIntBase a vCap + x)), (hinc _ hs).1, fun k => ?_⟩
  rw [(hinc _ hs).2.2 k]
  -- two vertices with the same slot are equal
  have hinj : ∀ y ∈ G.V, mem (dgExtToIntBase a vCap + y) = mem (dgExtToIntBase a vCap + x) →
      y = x := by
    intro y hy hxy
    have h1 := (hext y hy).2
    rw [hxy, (hext x hx).2] at h1
    exact h1.symm
  have hkey : ∀ e ∈ G.E, ((if k % 2 = 0 then mem (dgETailSlotBase a vCap eCap + e)
      else mem (dgEHeadSlotBase a vCap eCap + e)) = mem (dgExtToIntBase a vCap + x) ↔
      G.src (e, decide (k % 2 = 0)) = x) := by
    intro e he
    by_cases hp : k % 2 = 0
    · rw [ite_eq_left hp, (hslot e he).1, show decide (k % 2 = 0) = true from decide_eq_true hp]
      show _ ↔ G.tail e = x
      exact ⟨hinj _ (hval e he).1, fun h => by rw [h]⟩
    · rw [ite_eq_right hp, (hslot e he).2, show decide (k % 2 = 0) = false from decide_eq_false hp]
      show _ ↔ G.head e = x
      exact ⟨hinj _ (hval e he).2, fun h => by rw [h]⟩
  constructor
  · rintro ⟨hk, hkE, hks⟩; exact ⟨hk, hkE, (hkey _ hkE).mp hks⟩
  · rintro ⟨hk, hkE, hks⟩; exact ⟨hk, hkE, (hkey _ hkE).mpr hks⟩

/-- The ends read from a list of keys with the incidence property. -/
theorem mem_map_endOfKey_iff {L : List ℕ} {eCap x : ℕ} {G : MGraph}
    (hL : ∀ k, k ∈ L ↔ k < 2 * eCap ∧ (endOfKey k).1 ∈ G.E ∧ G.src (endOfKey k) = x)
    (y : End) : y ∈ L.map endOfKey ↔ y.1 < eCap ∧ y.1 ∈ G.E ∧ G.src y = x := by
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hk1, hk2, hk3⟩ := (hL k).mp hk
    refine ⟨?_, hk2, hk3⟩
    have := endKey_endOfKey k
    have h := endKey_div_two (endOfKey k)
    rw [this] at h
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨endKey y, (hL _).mpr ⟨endKey_lt_two_mul h1, ?_, ?_⟩, endOfKey_endKey y⟩ <;>
      rw [endOfKey_endKey] <;> assumption

/-- **A record of the split** from the edge lists of the ends of one side. -/
theorem updateAt_split_of_lists {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {v v' : ℕ}
    {St Sh : Finset ℕ} (hG : G.IsValid) (hu : G.UpdateIsValid (.split v v' St Sh))
    {Y : List End} (hY : Y.Nodup) (side : ℕ) (hs : side ≤ 1)
    (hside : ∀ x : End, x.1 ∈ G.E →
      (x ∈ Y ↔ (G.applyUpdate (.split v v' St Sh)).src x = if side = 0 then v else v'))
    (hrec : ListAt mem a ([3 - side, v, v', (endEdges Y G.E true).length,
      (endEdges Y G.E false).length] ++ endEdges Y G.E true ++ endEdges Y G.E false)) :
    UpdateAt mem a G (.split v v' St Sh)
      (5 + (endEdges Y G.E true).length + (endEdges Y G.E false).length) := by
  obtain ⟨h1, h0⟩ := splitLists_spec hG hu side hside
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with rfl | rfl
  · obtain ⟨ht, hh⟩ := h0 rfl
    exact Or.inr ⟨_, _, nodup_endEdges hY _ _, nodup_endEdges hY _ _, ht, hh, rfl, hrec⟩
  · obtain ⟨ht, hh⟩ := h1 one_ne_zero
    exact Or.inl ⟨_, _, nodup_endEdges hY _ _, nodup_endEdges hY _ _, ht, hh, rfl, hrec⟩

/-- A list of distinct keys below `2 eCap` has at most `2 eCap` keys. -/
theorem nodup_length_le_of_lt {L : List ℕ} {m : ℕ} (hnd : L.Nodup) (hlt : ∀ k ∈ L, k < m) :
    L.length ≤ m := by
  rw [← List.toFinset_card_of_nodup hnd]
  calc L.toFinset.card ≤ (Finset.range m).card :=
        Finset.card_le_card fun k hk => Finset.mem_range.mpr (hlt k (List.mem_toFinset.mp hk))
    _ = m := Finset.card_range m

/-- **The edit of the smaller side**, read from the incidence list `L` of its vertex after the
split, is `outSplitEdit`, and `L` has `min (deg v) (deg v')` keys. The vertex is `v` when its
degree is smaller, and `v'` otherwise; the tag of the edit is `2` (the complement) for `v`. -/
theorem outSplitEdit_eq_incList {G : MGraph} {v v' eCap : ℕ} {St Sh : Finset ℕ}
    (hG : G.IsValid) (hu : G.UpdateIsValid (.split v v' St Sh)) (hE : ∀ e ∈ G.E, e < eCap)
    {L : List ℕ} (hnd : L.Nodup) {x : ℕ}
    (hx : x = if (G.applyUpdate (.split v v' St Sh)).deg v <
      (G.applyUpdate (.split v v' St Sh)).deg v' then v else v')
    (hL : ∀ k, k ∈ L ↔ k < 2 * eCap ∧ (endOfKey k).1 ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
      (G.applyUpdate (.split v v' St Sh)).src (endOfKey k) = x) :
    outSplitEdit G v v' St Sh = .moveEnds v v' (L.map endOfKey).toFinset
        (decide ((if (G.applyUpdate (.split v v' St Sh)).deg v <
          (G.applyUpdate (.split v v' St Sh)).deg v' then 2 else 1) = 2)) ∧
      L.length + 1 = G.updateEnc (.split v v' St Sh) := by
  set G' := G.applyUpdate (.split v v' St Sh) with hG'
  obtain ⟨hd', hd⟩ := deg_applySplit hG hu
  rw [← hG'] at hd' hd
  have hcard : (L.map endOfKey).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup (hnd.map endOfKey_injective), List.length_map]
  have hmem : ∀ side, x = (if side = 0 then v else v') →
      (L.map endOfKey).toFinset =
        if side = 0 then splitKeptSel G v St Sh else splitMovedSel G v St Sh := by
    intro side hxs
    ext y
    rw [List.mem_toFinset, mem_map_endOfKey_iff hL, mem_splitSide_iff hG hu side y]
    constructor
    · rintro ⟨-, h2, h3⟩; exact ⟨h2, hxs ▸ h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨hE _ h2, h2, hxs ▸ h3⟩
  have henc : G.updateEnc (.split v v' St Sh) = min (G'.deg v) (G'.deg v') + 1 := rfl
  rw [henc]
  unfold outSplitEdit
  by_cases hlt : G'.deg v < G'.deg v'
  · have hS := hmem 0 (by rw [hx, ite_eq_left hlt]; rfl)
    simp only [if_true] at hS
    rw [ite_eq_right (by omega), ite_eq_left hlt, hS]
    refine ⟨rfl, ?_⟩
    rw [← hcard, hS, ← hd]
    omega
  · have hS := hmem 1 (by rw [hx, ite_eq_right hlt]; rfl)
    simp only [one_ne_zero, if_false] at hS
    rw [ite_eq_left (by omega), ite_eq_right hlt, hS]
    refine ⟨rfl, ?_⟩
    rw [← hcard, hS, ← hd']
    omega

end MinCostFlow.SparseCore.Program
