module

public import MinCostFlow.Bundle.State
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card

/-!
# Initial bundles

Make chunks of the restricted rotations and number the chunks by their
positions. The concatenated chunks list each admitted end once, which
identifies the unique bundle of each end.
-/

@[expose] public section

namespace MinCostFlow.Bundle

/-- The ends of the admitted edges in their order at `v`. -/
def restrictedEnds {C : MGraph} (ρ : Rotation C) (E : Finset ℕ) (v : ℕ) : List End :=
  (ρ.order v).filter fun x => decide (x.1 ∈ E)

theorem mem_restrictedEnds {C : MGraph} (ρ : Rotation C) {E : Finset ℕ} (hE : E ⊆ C.E)
    (v : ℕ) (x : End) : x ∈ restrictedEnds ρ E v ↔ x.1 ∈ E ∧ C.src x = v := by
  simp only [restrictedEnds, List.mem_filter, ρ.mem_order, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hE h.1, h.2⟩, h.1⟩⟩

/-- The list of initial bundles with their core vertices. -/
noncomputable def initialSlots {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    (k : ℕ) : List (ℕ × List End) :=
  (C.V.sort (· ≤ ·)).flatMap fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)

/-- Initialize a bundle epoch by cutting each restricted tour into chunks. -/
noncomputable def initBundleState {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    (k : ℕ) : BundleState :=
  let slots := initialSlots ρ E k
  { vertices := Finset.range slots.length
    edges := E
    parent := fun b => (slots[b]?.getD (0, [])).1
    bundleOf := fun x => slots.findIdx (fun p => p.2.contains x) }

private theorem initialSlots_mem {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    (k : ℕ) (s : ℕ × List End) :
    s ∈ initialSlots ρ E k ↔ s.1 ∈ C.V ∧ s.2 ∈ initialChunks k (restrictedEnds ρ E s.1) := by
  obtain ⟨v, ys⟩ := s
  simp only [initialSlots, List.mem_flatMap, Finset.mem_sort, List.mem_map, Prod.mk.injEq]
  exact ⟨by rintro ⟨w, hw, zs, hz, rfl, rfl⟩; exact ⟨hw, hz⟩,
    fun h => ⟨v, h.1, ys, h.2, rfl, rfl⟩⟩

private theorem initialSlots_flatten {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    {k : ℕ} (hk : 0 < k) :
    (initialSlots ρ E k).flatMap Prod.snd =
      (C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E) := by
  rw [initialSlots, List.flatMap_assoc]
  apply List.flatMap_congr
  intro v _
  rw [List.flatMap_map]
  change (initialChunks k (restrictedEnds ρ E v)).flatMap id = _
  rw [← List.flatten_eq_flatMap]
  exact (initialChunks_spec hk _).1

private theorem initialSlots_nodup {C : MGraph} (ρ : Rotation C) {E : Finset ℕ}
    (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) :
    ((initialSlots ρ E k).flatMap Prod.snd).Nodup := by
  rw [initialSlots_flatten ρ E hk, List.nodup_flatMap]
  refine ⟨fun v _ => (ρ.nodup v).filter _, ?_⟩
  apply List.Pairwise.imp_of_mem _ (Finset.sort_nodup C.V (· ≤ ·))
  intro v w _ _ hne
  apply List.disjoint_left.mpr
  intro x hv hw
  exact hne (((mem_restrictedEnds ρ hE v x).mp hv).2.symm.trans
    ((mem_restrictedEnds ρ hE w x).mp hw).2)

private theorem initialSlots_covers {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) {x : End} (hx : x.1 ∈ E) :
    ∃ s ∈ initialSlots ρ E k, x ∈ s.2 := by
  apply List.mem_flatMap.mp
  rw [initialSlots_flatten ρ E hk, List.mem_flatMap]
  have hv : C.src x ∈ C.V := by
    obtain ⟨e, side⟩ := x
    have h := hC e (hE hx)
    cases side
    · exact h.2
    · exact h.1
  exact ⟨C.src x, (Finset.mem_sort (· ≤ ·)).mpr hv, (mem_restrictedEnds ρ hE _ _).mpr ⟨hx, rfl⟩⟩

private theorem initialChunks_arc {k : ℕ} (hk : 0 < k) {xs ys : List End}
    (hxs : xs.Nodup) (hy : ys ∈ initialChunks k xs) :
    IsArc (fun x => ys.contains x) xs := by
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hy
  have hflat := (initialChunks_spec hk xs).1
  rw [hsplit, List.flatten_append, List.flatten_cons] at hflat
  refine ⟨ys, post.flatten ++ pre.flatten, ?_, ?_, ?_⟩
  · rw [← hflat]
    simpa only [List.append_assoc] using
      (List.isRotated_append (l := pre.flatten) (l' := ys ++ post.flatten))
  · exact fun x hx => List.contains_iff_mem.mpr hx
  · intro x hx
    have hn : (ys ++ (post.flatten ++ pre.flatten)).Nodup := by
      rw [← List.append_assoc]
      apply (List.isRotated_append (l := pre.flatten) (l' := ys ++ post.flatten)).perm.nodup_iff.mp
      rwa [hflat]
    exact Bool.eq_false_iff.mpr fun hm =>
      (List.nodup_append.mp hn).2.2 x (List.contains_iff_mem.mp hm) x hx rfl

private theorem slots_index_unique (slots : List (ℕ × List End))
    (hn : (slots.flatMap Prod.snd).Nodup) {i j : ℕ} (hi : i < slots.length)
    (hj : j < slots.length) {x : End} (hxi : x ∈ slots[i].2) (hxj : x ∈ slots[j].2) :
    i = j := by
  have hp := (List.nodup_flatMap.mp hn).2
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact False.elim (List.disjoint_left.mp (List.pairwise_iff_getElem.mp hp i j hi hj h) hxi hxj)
  · exact h
  · exact False.elim (List.disjoint_left.mp (List.pairwise_iff_getElem.mp hp j i hj hi h) hxj hxi)

private theorem slot_end_iff {C : MGraph} (ρ : Rotation C) {E : Finset ℕ}
    (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) {b : ℕ} (hb : b < (initialSlots ρ E k).length)
    (x : End) : x ∈ (initBundleState ρ E k).ends b ↔ x ∈ (initialSlots ρ E k)[b].2 := by
  let slots := initialSlots ρ E k
  let p : (ℕ × List End) → Bool := fun s => s.2.contains x
  change x ∈ (edgeEnds E).filter (fun y => slots.findIdx (fun s => s.2.contains y) = b) ↔
    x ∈ slots[b].2
  rw [Finset.mem_filter, mem_edgeEnds]
  constructor
  · rintro ⟨_, hf⟩
    have hi : slots.findIdx p < slots.length := by
      change slots.findIdx p = b at hf
      rw [hf]
      exact hb
    have hg := List.contains_iff_mem.mp (List.findIdx_getElem (p := p) (w := hi))
    have hget : slots[slots.findIdx p]? = slots[b]? := congrArg (fun j => slots[j]?) hf
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hb] at hget
    exact (Option.some.inj hget) ▸ hg
  · intro hx
    have hc := (initialSlots_mem ρ E k slots[b]).mp (List.getElem_mem hb)
    have hxρ : x ∈ restrictedEnds ρ E slots[b].1 := by
      rw [← (initialChunks_spec hk (restrictedEnds ρ E slots[b].1)).1]
      rw [List.flatten_eq_flatMap]
      exact List.mem_flatMap_of_mem (f := id) hc.2 hx
    have he := (mem_restrictedEnds ρ hE _ _).mp hxρ
    have hi := List.findIdx_lt_length_of_exists (p := p)
      ⟨slots[b], List.getElem_mem hb, List.contains_iff_mem.mpr hx⟩
    exact ⟨he.1, slots_index_unique slots (initialSlots_nodup ρ hE hk) hi hb
      (List.contains_iff_mem.mp (List.findIdx_getElem (p := p) (w := hi))) hx⟩

/-- The initial bundle state partitions all the admitted ends and satisfies
the cap. -/
theorem initBundleState_inv {C : MGraph} (ρ : Rotation C) (hC : C.IsValid) {E : Finset ℕ}
    (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) : (initBundleState ρ E k).IsPartition ρ k := by
  let B := initBundleState ρ E k
  let slots := initialSlots ρ E k
  have hslot : ∀ b (hb : b ∈ B.vertices), ∃ hi : b < slots.length,
      B.parent b = slots[b].1 := by
    intro b hb
    have hi : b < slots.length := Finset.mem_range.mp hb
    exact ⟨hi, by simp [B, initBundleState, slots, List.getElem?_eq_getElem hi]⟩
  refine ⟨hE, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨hi, hp⟩ := hslot b hb
    rw [hp]
    exact ((initialSlots_mem ρ E k _).mp (List.getElem_mem hi)).1
  · intro x hx
    let p : (ℕ × List End) → Bool := fun s => s.2.contains x
    have hi : slots.findIdx p < slots.length := List.findIdx_lt_length_of_exists (p := p) (by
      obtain ⟨s, hs, hxs⟩ := initialSlots_covers ρ hC hE hk ((mem_edgeEnds _ _).mp hx)
      exact ⟨s, hs, List.contains_iff_mem.mpr hxs⟩)
    have hb : B.bundleOf x ∈ B.vertices := Finset.mem_range.mpr hi
    obtain ⟨hj, hp⟩ := hslot (B.bundleOf x) hb
    refine ⟨hb, ?_⟩
    have hc := ((initialSlots_mem ρ E k _).mp (List.getElem_mem hj)).2
    have hxρ : x ∈ restrictedEnds ρ E slots[B.bundleOf x].1 := by
      rw [← (initialChunks_spec hk (restrictedEnds ρ E slots[B.bundleOf x].1)).1]
      have hmem : x ∈ slots[B.bundleOf x].2 :=
        List.contains_iff_mem.mp (List.findIdx_getElem (p := p) (w := hi))
      rw [List.flatten_eq_flatMap]
      exact List.mem_flatMap_of_mem (f := id) hc hmem
    rw [hp]
    exact ((mem_restrictedEnds ρ hE _ _).mp hxρ).2.symm
  · intro b hb
    obtain ⟨hi, hp⟩ := hslot b hb
    have hc := ((initialSlots_mem ρ E k _).mp (List.getElem_mem hi)).2
    have he : B.ends b = slots[b].2.toFinset := by
      ext x
      rw [List.mem_toFinset]
      exact slot_end_iff ρ hE hk hi x
    constructor
    · rw [he]
      exact Nat.le_trans (List.toFinset_card_le _) ((initialChunks_spec hk _).2 _ hc)
    · change IsArc (fun x => decide (x ∈ B.ends b)) (restrictedEnds ρ E (B.parent b))
      rw [hp, he]
      have hpred : (fun x => decide (x ∈ slots[b].2.toFinset)) = fun x => slots[b].2.contains x := by
        funext x
        apply Bool.eq_iff_iff.mpr
        simp
      rw [hpred]
      exact initialChunks_arc hk ((ρ.nodup _).filter _) hc


private theorem ceil_capacity_le (n k : ℕ) (hk : 0 < k) :
    k * (n ⌈/⌉ k) ≤ k + n := by
  have hmod := Nat.mod_lt n hk
  have hdiv := Nat.mod_add_div n k
  have h₁ : n ≤ k * (n / k + 1) := by
    rw [Nat.mul_succ]
    omega
  have h₂ : n ⌈/⌉ k ≤ n / k + 1 := (ceilDiv_le_iff_le_mul hk).2 h₁
  apply (Nat.mul_le_mul_left k h₂).trans
  rw [Nat.mul_succ]
  omega

private theorem initialSlots_count_le {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    (k : ℕ) (hk : 0 < k) (vs : List ℕ) :
    k * (vs.flatMap fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)).length ≤
      k * vs.length + (vs.flatMap (restrictedEnds ρ E)).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
      initialChunks_length, Nat.mul_add, Nat.mul_one]
    have h := ceil_capacity_le (restrictedEnds ρ E v).length k hk
    omega

/-- The initial vertex count is at most the component count plus two
admitted ends per edge divided by the bundle cap. -/
theorem initBundleState_vertex_bound {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) :
    k * (initBundleState ρ E k).vertices.card ≤ k * C.V.card + 2 * E.card := by
  let zs := (initialSlots ρ E k).flatMap Prod.snd
  have hset : zs.toFinset = edgeEnds E := by
    ext x
    rw [List.mem_toFinset, mem_edgeEnds]
    constructor
    · intro hx
      change x ∈ (initialSlots ρ E k).flatMap Prod.snd at hx
      rw [initialSlots_flatten ρ E hk] at hx
      obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hx
      exact ((mem_restrictedEnds ρ hE v x).mp hv).1
    · intro hx
      exact List.mem_flatMap.mpr (initialSlots_covers ρ hC hE hk hx)
  have hlen : zs.length = 2 * E.card := by
    rw [← List.toFinset_card_of_nodup (initialSlots_nodup ρ hE hk), hset, card_edgeEnds]
  have hl := initialSlots_count_le ρ E k hk (C.V.sort (· ≤ ·))
  rw [Finset.length_sort] at hl
  rw [show ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).length = zs.length from
    congrArg List.length (initialSlots_flatten ρ E hk).symm, hlen] at hl
  simpa only [initBundleState, initialSlots, Finset.card_range] using hl

end MinCostFlow.Bundle
