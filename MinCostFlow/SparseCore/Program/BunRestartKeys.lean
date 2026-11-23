module

public import MinCostFlow.SparseCore.Program.BunRestartProg

/-!
# The restart of the bundles: the keys and the pairs (`BunRestartKeys`)

Loop B of the restart walks the end list of every bundle of every listed slot, and writes the keys
it finds one after the other. This file names what it finds and proves its properties from P5's
representation of the table (`BundleTableRepAt`).

* `slotB S s`, `slotBlk m s`: the bundle state and the block `(p, bunCap)` of slot `s`.
* `bunList … p B b`: the end list of bundle `b` of the block at `p` (`mem_bunList`).
* `bunKeys … p B`: the end lists of all bundles `b < nB` of the block, one after the other. They
  are the keys of the ends of the edges of `B`, each once (`mem_bunKeys`, `bunKeys_nodup`), so
  there are `2 |E|` of them (`bunKeys_length`).
* `allKeys`: the keys of all listed slots; `allPairs`: the pairs `(e, s)` for the even keys `2 e`.
  `slotEdgesOf allPairs s` is the edge set of slot `s` (`slotEdgesOf_allPairs`), the edges of the
  pairs have no repeats (`allPairs_fst_nodup`), and there are `E` pairs (`allPairs_length`).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The empty bundle state. -/
def emptyBun : BundleState := ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

/-- The bundle state of slot `s` (the empty one if the slot is inactive). -/
noncomputable def slotB {slotCap : ℕ} (S : Fin slotCap → Option BundleState) (s : ℕ) :
    BundleState :=
  if hs : s < slotCap then (S ⟨s, hs⟩).getD emptyBun else emptyBun

/-- The block `(p, bunCap)` of slot `s` (`(0, 0)` if the slot has none). -/
def slotBlk {slotCap : ℕ} (m : BundleTableMeta slotCap) (s : ℕ) : ℕ × ℕ :=
  if hs : s < slotCap then (m.slotBlocks ⟨s, hs⟩).getD (0, 0) else (0, 0)

/-- The end list of bundle `b` of the block at `p` of a bundle state `B`: a doubly linked list at
`head[b]` whose keys are those of the ends of bundle `b` (`[]` if there is none). -/
noncomputable def bunList (slotCap eCap tbl : ℕ) (mem : ℕ → ℕ) (p : ℕ) (B : BundleState)
    (b : ℕ) : List ℕ :=
  open Classical in
  if h : ∃ L, IsDoublyLinkedList mem (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase p + b) (2 * eCap) L ∧
      ∀ k, k ∈ L ↔ endOfKey k ∈ B.ends b then h.choose else []

/-- The end lists of all bundles of the block at `p`, one after the other. -/
noncomputable def bunKeys (slotCap eCap tbl : ℕ) (mem : ℕ → ℕ) (p : ℕ) (B : BundleState) :
    List ℕ :=
  (List.range B.vertices.card).flatMap (bunList slotCap eCap tbl mem p B)

/-- The keys of slot `s`. -/
noncomputable def slotKeys {slotCap : ℕ} (eCap tbl : ℕ) (S : Fin slotCap → Option BundleState)
    (m : BundleTableMeta slotCap) (mem : ℕ → ℕ) (s : ℕ) : List ℕ :=
  bunKeys slotCap eCap tbl mem (slotBlk m s).1 (slotB S s)

/-- The keys of all listed slots, one slot after the other. -/
noncomputable def allKeys {slotCap : ℕ} (eCap tbl : ℕ) (S : Fin slotCap → Option BundleState)
    (m : BundleTableMeta slotCap) (mem : ℕ → ℕ) (slots : List ℕ) : List ℕ :=
  slots.flatMap (slotKeys eCap tbl S m mem)

/-- The number of edges of the listed slots. -/
noncomputable def edgeTot {slotCap : ℕ} (S : Fin slotCap → Option BundleState)
    (slots : List ℕ) : ℕ :=
  (slots.map fun s => (slotB S s).edges.card).sum

/-- The pairs `(k / 2, s)` of the even keys `k` of `L`. -/
def evenPairs (s : ℕ) (L : List ℕ) : List (ℕ × ℕ) :=
  (L.filter fun k => k % 2 = 0).map fun k => (k / 2, s)

/-- The pairs `(e, s)` of the edges of the listed slots, one slot after the other. -/
noncomputable def allPairs {slotCap : ℕ} (eCap tbl : ℕ) (S : Fin slotCap → Option BundleState)
    (m : BundleTableMeta slotCap) (mem : ℕ → ℕ) (slots : List ℕ) : List (ℕ × ℕ) :=
  slots.flatMap fun s => evenPairs s (slotKeys eCap tbl S m mem s)

/-- The specs of the new blocks: `(s, 4 |E_s|)` for each listed slot. -/
noncomputable def brSpecs {slotCap : ℕ} (S : Fin slotCap → Option BundleState)
    (slots : List ℕ) : List (ℕ × ℕ) :=
  slots.map fun s => (s, 4 * (slotB S s).edges.card)

end

public section

variable {slotCap vCap eCap tbl : ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}

theorem slotB_eq {s : ℕ} (hs : s < slotCap) {B : BundleState} (hB : S ⟨s, hs⟩ = some B) :
    slotB S s = B := by
  simp [slotB, hs, hB]

/-- The facts of an active slot `s` holding `B`: its block, its slot pointer, and the
representation of `B` in the block. -/
theorem slot_facts (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) {s : ℕ}
    (hs : s < slotCap) {B : BundleState} (hB : S ⟨s, hs⟩ = some B) :
    m.slotBlocks ⟨s, hs⟩ = some (slotBlk m s) ∧
      mem (btSlotPtrBase tbl + s) = (slotBlk m s).1 ∧
      BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (slotBlk m s).1 (slotBlk m s).2 B mem ∧
      ((slotBlk m s).1 + bundleSlotBlockSize (slotBlk m s).2 ≤ tbl ∨
        tbl + bundleTableFixedSize slotCap eCap ≤ (slotBlk m s).1) := by
  rcases hrep with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hslots, -⟩
  have hsl := hslots ⟨s, hs⟩
  rw [hB] at hsl
  rcases hm : m.slotBlocks ⟨s, hs⟩ with _ | ⟨p, c⟩
  · rw [hm] at hsl; exact hsl.elim
  · rw [hm] at hsl
    have hblk : slotBlk m s = (p, c) := by simp [slotBlk, hs, hm]
    rw [hblk]
    exact ⟨rfl, hsl.1, hsl.2.1, hsl.2.2⟩

/-- The edge slot of an edge of an active slot `s` is `s + 1`. -/
theorem edgeSlot_of_mem (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) {s : ℕ}
    (hs : s < slotCap) {B : BundleState} (hB : S ⟨s, hs⟩ = some B) {e : ℕ} (he : e ∈ B.edges)
    (heC : e < eCap) : mem (btEdgeSlotBase tbl slotCap + e) = s + 1 := by
  rcases hrep with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hedge, -⟩
  exact (hedge e heC).1 ⟨s, hs⟩ B hB he

/-- The edge sets of two distinct active slots are disjoint. -/
theorem edges_disjoint (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) {s₁ s₂ : ℕ}
    (hs₁ : s₁ < slotCap) (hs₂ : s₂ < slotCap) (hne : s₁ ≠ s₂) {B₁ B₂ : BundleState}
    (hB₁ : S ⟨s₁, hs₁⟩ = some B₁) (hB₂ : S ⟨s₂, hs₂⟩ = some B₂) : Disjoint B₁.edges B₂.edges := by
  rcases hrep with ⟨-, -, -, -, -, -, -, -, -, -, -, -, hdisj, -⟩
  exact hdisj ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ (fun h => hne (congrArg Fin.val h)) B₁ B₂ hB₁ hB₂

section Block

variable {p c : ℕ} {B : BundleState}

/-- The end list of a bundle of a represented block. -/
theorem bunList_spec
    (hslot : BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) p c B mem) {b : ℕ} (hb : b < B.vertices.card) :
    IsDoublyLinkedList mem (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (bsHeadBase p + b) (2 * eCap) (bunList slotCap eCap tbl mem p B b) ∧
      ∀ k, k ∈ bunList slotCap eCap tbl mem p B b ↔ endOfKey k ∈ B.ends b := by
  obtain ⟨nB, hV, -, -, -, -, -, -, -, hdll, -⟩ := hslot
  have hb' : b < nB := by rw [hV, Finset.card_range] at hb; exact hb
  obtain ⟨L, hL, -, hmem⟩ := hdll b hb'
  have hex : ∃ L, IsDoublyLinkedList mem (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase p + b) (2 * eCap) L ∧
      ∀ k, k ∈ L ↔ endOfKey k ∈ B.ends b := ⟨L, hL, hmem⟩
  unfold bunList
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

private theorem endOfKey_fst (k : ℕ) : (endOfKey k).1 = k / 2 := rfl

/-- A key is in the end lists of a block if and only if its edge is an edge of the block. -/
theorem mem_bunKeys
    (hslot : BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) p c B mem) {k : ℕ} :
    k ∈ bunKeys slotCap eCap tbl mem p B ↔ k / 2 ∈ B.edges := by
  unfold bunKeys
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨b, hb, hk⟩
    have hb' := List.mem_range.mp hb
    have hx := ((bunList_spec hslot hb').2 k).mp hk
    rw [BundleState.mem_ends] at hx
    exact hx.1
  · intro hk
    have hslot' := hslot
    obtain ⟨nB, hV, -, -, hbo, -⟩ := hslot'
    have hx : endOfKey k ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr hk
    have hlt := hbo _ hx
    have hlt' : B.bundleOf (endOfKey k) < B.vertices.card := by
      rw [hV, Finset.card_range]; exact hlt
    refine ⟨B.bundleOf (endOfKey k), List.mem_range.mpr hlt', ?_⟩
    exact ((bunList_spec hslot hlt').2 k).mpr ((BundleState.mem_ends _ _ _).mpr ⟨hk, rfl⟩)

/-- The end lists of a block have no repeated key. -/
theorem bunKeys_nodup
    (hslot : BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) p c B mem) :
    (bunKeys slotCap eCap tbl mem p B).Nodup := by
  unfold bunKeys
  rw [List.nodup_flatMap]
  refine ⟨fun b hb => (bunList_spec hslot (List.mem_range.mp hb)).1.1, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
  intro b₁ b₂ hb₁ hb₂ hne
  refine List.disjoint_left.mpr fun k hk₁ hk₂ => hne ?_
  have h₁ := ((bunList_spec hslot (List.mem_range.mp hb₁)).2 k).mp hk₁
  have h₂ := ((bunList_spec hslot (List.mem_range.mp hb₂)).2 k).mp hk₂
  rw [BundleState.mem_ends] at h₁ h₂
  exact h₁.2.symm.trans h₂.2

/-- Every key of a block is below `2 eCap`. -/
theorem bunKeys_lt
    (hslot : BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) p c B mem) {k : ℕ}
    (hk : k ∈ bunKeys slotCap eCap tbl mem p B) : k < 2 * eCap := by
  unfold bunKeys at hk
  obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.mp hk
  exact (bunList_spec hslot (List.mem_range.mp hb)).1.2.1 k hkb

/-- A block holds `2 |E|` keys. -/
theorem bunKeys_length
    (hslot : BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) p c B mem) :
    (bunKeys slotCap eCap tbl mem p B).length = 2 * B.edges.card := by
  rw [← List.toFinset_card_of_nodup (bunKeys_nodup hslot), ← card_edgeEnds,
    ← Finset.card_image_of_injective _ endKey_injective]
  congr 1
  ext k
  rw [List.mem_toFinset, mem_bunKeys hslot, Finset.mem_image]
  constructor
  · intro hk
    exact ⟨endOfKey k, (mem_edgeEnds _ _).mpr hk, bundle_endKey_endOfKey k⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← endOfKey_fst, bundle_endOfKey_endKey]
    exact (mem_edgeEnds _ _).mp hx

end Block

/-! ## Pairs of even keys -/

theorem mem_evenPairs {s e t : ℕ} {L : List ℕ} : (e, t) ∈ evenPairs s L ↔ t = s ∧ 2 * e ∈ L := by
  unfold evenPairs
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨k, ⟨hk, hev⟩, rfl, rfl⟩
    exact ⟨rfl, by rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hev)]⟩
  · rintro ⟨rfl, h⟩
    exact ⟨2 * e, ⟨h, by omega⟩, by omega, rfl⟩

/-- The edges of the pairs of a list of keys without repeats have no repeats. -/
theorem evenPairs_fst_nodup {s : ℕ} {L : List ℕ} (hL : L.Nodup) :
    ((evenPairs s L).map Prod.fst).Nodup := by
  unfold evenPairs
  rw [List.map_map]
  refine (hL.filter _).map_on fun a ha b hb hab => ?_
  have ha' := (List.mem_filter.mp ha).2
  have hb' := (List.mem_filter.mp hb).2
  simp only [decide_eq_true_eq] at ha' hb'
  simp only [Function.comp_apply] at hab
  omega

/-- If the keys of `L` are those whose edge lies in `E`, then `L` has `|E|` even keys. -/
theorem evenPairs_length {s : ℕ} {L : List ℕ} {E : Finset ℕ} (hL : L.Nodup)
    (hmem : ∀ k, k ∈ L ↔ k / 2 ∈ E) : (evenPairs s L).length = E.card := by
  rw [← List.length_map (f := Prod.fst), ← List.toFinset_card_of_nodup (evenPairs_fst_nodup hL)]
  congr 1
  ext e
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨e', t⟩, hp, rfl⟩
    have := (mem_evenPairs.mp hp).2
    rw [hmem] at this
    simpa using this
  · intro he
    refine ⟨(e, s), mem_evenPairs.mpr ⟨rfl, (hmem _).mpr (by simpa using he)⟩, rfl⟩

/-! ## All listed slots -/

section All

variable (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) {slots : List ℕ}
  (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
include hrep hact

/-- The keys of a listed slot `s`: those whose edge is an edge of `s`, each once. -/
theorem slotKeys_facts {s : ℕ} (hs : s ∈ slots) :
    (∀ k, k ∈ slotKeys eCap tbl S m mem s ↔ k / 2 ∈ (slotB S s).edges) ∧
      (slotKeys eCap tbl S m mem s).Nodup ∧
      (slotKeys eCap tbl S m mem s).length = 2 * (slotB S s).edges.card ∧
      ∀ k ∈ slotKeys eCap tbl S m mem s, k < 2 * eCap := by
  obtain ⟨hsc, B, hB⟩ := hact s hs
  have hslot := (slot_facts hrep hsc hB).2.2.1
  rw [← slotB_eq hsc hB] at hslot
  exact ⟨fun k => mem_bunKeys hslot, bunKeys_nodup hslot, bunKeys_length hslot,
    fun k hk => bunKeys_lt hslot hk⟩

/-- The edge sets of two distinct listed slots are disjoint. -/
theorem slotB_edges_disjoint {s₁ s₂ : ℕ} (hs₁ : s₁ ∈ slots) (hs₂ : s₂ ∈ slots) (hne : s₁ ≠ s₂) :
    Disjoint (slotB S s₁).edges (slotB S s₂).edges := by
  obtain ⟨h₁, B₁, hB₁⟩ := hact s₁ hs₁
  obtain ⟨h₂, B₂, hB₂⟩ := hact s₂ hs₂
  rw [slotB_eq h₁ hB₁, slotB_eq h₂ hB₂]
  exact edges_disjoint hrep h₁ h₂ hne hB₁ hB₂

theorem mem_allKeys {k : ℕ} :
    k ∈ allKeys eCap tbl S m mem slots ↔ ∃ s ∈ slots, k / 2 ∈ (slotB S s).edges := by
  unfold allKeys
  rw [List.mem_flatMap]
  exact exists_congr fun s => and_congr_right fun hs => (slotKeys_facts hrep hact hs).1 k

include hrep hact in
theorem allKeys_nodup (hnd : slots.Nodup) : (allKeys eCap tbl S m mem slots).Nodup := by
  unfold allKeys
  rw [List.nodup_flatMap]
  refine ⟨fun s hs => (slotKeys_facts hrep hact hs).2.1, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro s₁ s₂ hs₁ hs₂ hne
  refine List.disjoint_left.mpr fun k hk₁ hk₂ => ?_
  have h₁ := ((slotKeys_facts hrep hact hs₁).1 k).mp hk₁
  have h₂ := ((slotKeys_facts hrep hact hs₂).1 k).mp hk₂
  exact Finset.disjoint_left.mp (slotB_edges_disjoint hrep hact hs₁ hs₂ hne) h₁ h₂

theorem allKeys_length : (allKeys eCap tbl S m mem slots).length = 2 * edgeTot S slots := by
  unfold allKeys edgeTot
  rw [List.length_flatMap, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun s hs => (slotKeys_facts hrep hact hs).2.2.1

theorem allKeys_lt {k : ℕ} (hk : k ∈ allKeys eCap tbl S m mem slots) : k < 2 * eCap := by
  obtain ⟨s, hs, hks⟩ := List.mem_flatMap.mp hk
  exact (slotKeys_facts hrep hact hs).2.2.2 k hks

theorem mem_allPairs {e t : ℕ} :
    (e, t) ∈ allPairs eCap tbl S m mem slots ↔ t ∈ slots ∧ e ∈ (slotB S t).edges := by
  unfold allPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hp⟩
    obtain ⟨rfl, hk⟩ := mem_evenPairs.mp hp
    refine ⟨hs, ?_⟩
    have := ((slotKeys_facts hrep hact hs).1 _).mp hk
    simpa using this
  · rintro ⟨ht, he⟩
    refine ⟨t, ht, mem_evenPairs.mpr ⟨rfl, ((slotKeys_facts hrep hact ht).1 _).mpr ?_⟩⟩
    simpa using he

theorem slotEdgesOf_allPairs {s : ℕ} (hs : s ∈ slots) :
    slotEdgesOf (allPairs eCap tbl S m mem slots) s = (slotB S s).edges := by
  ext e
  unfold slotEdgesOf
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨e', t⟩, hp, rfl⟩
    rw [List.mem_filter] at hp
    have ht : t = s := by simpa using hp.2
    subst ht
    exact ((mem_allPairs hrep hact).mp hp.1).2
  · intro he
    exact ⟨(e, s), List.mem_filter.mpr ⟨(mem_allPairs hrep hact).mpr ⟨hs, he⟩, by simp⟩, rfl⟩

include hrep hact in
theorem allPairs_fst_nodup (hnd : slots.Nodup) :
    ((allPairs eCap tbl S m mem slots).map Prod.fst).Nodup := by
  unfold allPairs
  rw [List.map_flatMap, List.nodup_flatMap]
  refine ⟨fun s hs => evenPairs_fst_nodup (slotKeys_facts hrep hact hs).2.1, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro s₁ s₂ hs₁ hs₂ hne
  refine List.disjoint_left.mpr fun e he₁ he₂ => ?_
  obtain ⟨⟨e₁, t₁⟩, hp₁, rfl⟩ := List.mem_map.mp he₁
  obtain ⟨⟨e₂, t₂⟩, hp₂, he⟩ := List.mem_map.mp he₂
  simp only at he
  subst he
  obtain ⟨rfl, hk₁⟩ := mem_evenPairs.mp hp₁
  obtain ⟨rfl, hk₂⟩ := mem_evenPairs.mp hp₂
  have h₁ := ((slotKeys_facts hrep hact hs₁).1 _).mp hk₁
  have h₂ := ((slotKeys_facts hrep hact hs₂).1 _).mp hk₂
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at h₁ h₂
  exact Finset.disjoint_left.mp (slotB_edges_disjoint hrep hact hs₁ hs₂ hne) h₁ h₂

theorem allPairs_length : (allPairs eCap tbl S m mem slots).length = edgeTot S slots := by
  unfold allPairs edgeTot
  rw [List.length_flatMap]
  congr 1
  exact List.map_congr_left fun s hs =>
    evenPairs_length (slotKeys_facts hrep hact hs).2.1 (slotKeys_facts hrep hact hs).1

/-- **The pairs the program computes.** For each even key `k` of the listed slots, the pair
`(k / 2, edgeSlot[k / 2] - 1)` is `(e, s)` for the slot `s` of the edge `e = k / 2`. -/
theorem progPairs_eq (heC : ∀ s ∈ slots, ∀ e ∈ (slotB S s).edges, e < eCap) :
    ((allKeys eCap tbl S m mem slots).filter fun k => k % 2 = 0).map
        (fun k => (k / 2, mem (btEdgeSlotBase tbl slotCap + k / 2) - 1)) =
      allPairs eCap tbl S m mem slots := by
  unfold allKeys allPairs evenPairs
  rw [List.filter_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun s hs => List.map_congr_left fun k hk => ?_
  obtain ⟨hsc, B, hB⟩ := hact s hs
  have hkE := ((slotKeys_facts hrep hact hs).1 k).mp (List.mem_filter.mp hk).1
  have hedge := edgeSlot_of_mem hrep hsc hB (by rwa [← slotB_eq hsc hB]) (heC s hs _ hkE)
  rw [hedge, Nat.add_sub_cancel]

end All

end

end MinCostFlow.SparseCore.Program.Restart
