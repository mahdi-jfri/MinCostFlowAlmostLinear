module

public import MinCostFlow.Bundle.Update
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Infix

/-!
# Maximal runs in a cyclic order

The bundle step cuts each bundle into the maximal arcs of its ends in the cyclic order at a core
vertex. This file defines these arcs for a list read cyclically and proves the three facts the
bundle step needs.

For a linear list, `pRuns p l` lists the maximal blocks of consecutive elements with `p`, in
order. For a cyclic list, `cycRuns p xs` first rotates `xs` so that it ends with an element
without `p` (`cycRot`), so that no block wraps around, and then takes the linear blocks. If every
element has `p`, the whole list is one block.

The facts are: the runs are nonempty, have `p`, and list each element with `p` once
(`mem_cycRuns_flatten`, `cycRuns_flatten_nodup`); each run is an arc of the cyclic order
(`cycRuns_isArc`); and an arc whose elements all have `p` lies in one run (`cycRuns_block`).
The last fact is what makes the runs the coarsest cut of `p` into arcs.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Bundle

variable {α : Type*}

/-- Put `a` in front of the first run, or start a run with `a` if there is none. -/
def consRun (a : α) : List (List α) → List (List α)
  | [] => [[a]]
  | r :: rs => (a :: r) :: rs

/-- The maximal blocks of consecutive elements with `p` of a linear list, in order. -/
def pRuns (p : α → Bool) : List α → List (List α)
  | [] => []
  | a :: l =>
    if p a then (if l.head?.any p then consRun a (pRuns p l) else [a] :: pRuns p l)
    else pRuns p l

/-- Rotate a list so that it ends right after its first element without `p`. The list is
unchanged if every element has `p`. -/
def cycRot (p : α → Bool) (xs : List α) : List α :=
  xs.drop (xs.findIdx (fun x => !p x) + 1) ++ xs.take (xs.findIdx (fun x => !p x) + 1)

/-- The maximal arcs of elements with `p` in the cyclic order `xs`. -/
def cycRuns (p : α → Bool) (xs : List α) : List (List α) :=
  pRuns p (cycRot p xs)

private theorem consRun_flatten (a : α) (rs : List (List α)) :
    (consRun a rs).flatten = a :: rs.flatten := by
  cases rs <;> rfl

theorem pRuns_flatten (p : α → Bool) (l : List α) : (pRuns p l).flatten = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a
    · by_cases hh : l.head?.any p
      · simp only [pRuns, ha, hh, ↓reduceIte, consRun_flatten, ih, List.filter_cons]
      · simp only [pRuns, ha, hh, ↓reduceIte, List.flatten_cons, List.singleton_append, ih,
          List.filter_cons, Bool.false_eq_true]
    · simp only [pRuns, ha, ↓reduceIte, ih, List.filter_cons, Bool.false_eq_true]

theorem pRuns_spec (p : α → Bool) (l : List α) :
    ∀ r ∈ pRuns p l, r ≠ [] ∧ ∀ x ∈ r, p x = true := by
  induction l with
  | nil => simp [pRuns]
  | cons a l ih =>
    by_cases ha : p a
    · by_cases hh : l.head?.any p
      · simp only [pRuns, ha, hh, ↓reduceIte]
        cases hr : pRuns p l with
        | nil => simp [consRun, ha]
        | cons r rs =>
          rw [hr] at ih
          intro s hs
          simp only [consRun, List.mem_cons] at hs
          rcases hs with rfl | hs
          · refine ⟨List.cons_ne_nil _ _, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ha
            · exact (ih r List.mem_cons_self).2 x hx
          · exact ih s (List.mem_cons_of_mem _ hs)
      · simp only [pRuns, ha, hh, ↓reduceIte]
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨List.cons_ne_nil _ _, fun x hx => (List.mem_singleton.mp hx) ▸ ha⟩
        · exact ih s hs
    · simp only [pRuns, ha, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- The first run of a list that starts with an element with `p` is a prefix of the list. -/
private theorem pRuns_head (p : α → Bool) (b : α) (l : List α) (hb : p b = true) :
    ∃ r rs, pRuns p (b :: l) = r :: rs ∧ r <+: b :: l := by
  induction l generalizing b with
  | nil => exact ⟨[b], [], by simp [pRuns, hb], List.prefix_refl _⟩
  | cons c l ih =>
    by_cases hc : p c
    · obtain ⟨r, rs, hr, hp⟩ := ih c hc
      refine ⟨b :: r, rs, ?_, List.cons_prefix_cons.mpr ⟨rfl, hp⟩⟩
      simp only [pRuns, hb, List.head?_cons, Option.any_some, hc, ↓reduceIte] at hr ⊢
      rw [hr]
      rfl
    · refine ⟨[b], pRuns p (c :: l), ?_, ?_⟩
      · simp [pRuns, hb, hc]
      · exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩

theorem pRuns_infix (p : α → Bool) (l : List α) : ∀ r ∈ pRuns p l, r <:+: l := by
  induction l with
  | nil => simp [pRuns]
  | cons a l ih =>
    have ht : ∀ r ∈ pRuns p l, r <:+: a :: l :=
      fun r hr => (ih r hr).trans (List.suffix_cons a l).isInfix
    by_cases ha : p a
    · by_cases hh : l.head?.any p
      · cases l with
        | nil => simp at hh
        | cons c l' =>
          have hc : p c = true := by simpa using hh
          obtain ⟨r, rs, hr, hp⟩ := pRuns_head p c l' hc
          rw [pRuns]
          simp only [ha, hh, ↓reduceIte]
          rw [hr] at ih ht ⊢
          intro s hs
          simp only [consRun, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact (List.cons_prefix_cons.mpr ⟨rfl, hp⟩).isInfix
          · exact ht s (List.mem_cons_of_mem _ hs)
      · simp only [pRuns, ha, hh, ↓reduceIte]
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩).isInfix
        · exact ht s hs
    · simp only [pRuns, ha, Bool.false_eq_true, ↓reduceIte]
      exact ht

/-- Every run of the tail lies in a run of the list. -/
private theorem pRuns_cons_extend (p : α → Bool) (a : α) (l : List α) :
    ∀ r ∈ pRuns p l, ∃ r' ∈ pRuns p (a :: l), ∀ x ∈ r, x ∈ r' := by
  intro r hr
  by_cases ha : p a
  · by_cases hh : l.head?.any p
    · simp only [pRuns, ha, hh, ↓reduceIte]
      cases hl : pRuns p l with
      | nil => rw [hl] at hr; simp at hr
      | cons r₀ rs =>
        rw [hl] at hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨a :: r, List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ hx⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, fun x hx => hx⟩
    · simp only [pRuns, ha, hh, ↓reduceIte]
      exact ⟨r, List.mem_cons_of_mem _ hr, fun x hx => hx⟩
  · simp only [pRuns, ha, Bool.false_eq_true, ↓reduceIte]
    exact ⟨r, hr, fun x hx => hx⟩

/-- A nonempty block of elements with `p` at the start of a list lies in its first run. -/
private theorem pRuns_block_prefix (p : α → Bool) (blk post : List α) (hne : blk ≠ [])
    (hp : ∀ x ∈ blk, p x = true) :
    ∃ r rs, pRuns p (blk ++ post) = r :: rs ∧ ∀ x ∈ blk, x ∈ r := by
  induction blk with
  | nil => exact absurd rfl hne
  | cons a blk ih =>
    have ha := hp a List.mem_cons_self
    cases blk with
    | nil =>
      by_cases hh : post.head?.any p
      · cases hl : pRuns p post with
        | nil => exact ⟨[a], [], by simp [pRuns, ha, hh, hl, consRun], by simp⟩
        | cons r rs =>
          exact ⟨a :: r, rs, by simp [pRuns, ha, hh, hl, consRun], by simp⟩
      · exact ⟨[a], pRuns p post, by simp [pRuns, ha, hh], by simp⟩
    | cons b blk' =>
      have hb := hp b (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨r, rs, hr, hm⟩ := ih (List.cons_ne_nil _ _) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      refine ⟨a :: r, rs, ?_, ?_⟩
      · have hh : ((b :: blk') ++ post).head?.any p = true := by simp [hb]
        rw [List.cons_append, pRuns]
        simp only [ha, hh, ↓reduceIte]
        rw [hr]
        rfl
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hm x hx)

/-- A nonempty block of consecutive elements with `p` lies in one run. -/
theorem pRuns_block (p : α → Bool) (pre blk post : List α) (hne : blk ≠ [])
    (hp : ∀ x ∈ blk, p x = true) :
    ∃ r ∈ pRuns p (pre ++ blk ++ post), ∀ x ∈ blk, x ∈ r := by
  induction pre with
  | nil =>
    obtain ⟨r, rs, hr, hm⟩ := pRuns_block_prefix p blk post hne hp
    refine ⟨r, ?_, hm⟩
    rw [List.nil_append, hr]
    exact List.mem_cons_self
  | cons a pre ih =>
    obtain ⟨r, hr, hm⟩ := ih
    obtain ⟨r', hr', hsub⟩ := pRuns_cons_extend p a (pre ++ blk ++ post) r hr
    exact ⟨r', by simpa using hr', fun x hx => hsub x (hm x hx)⟩

theorem cycRot_isRotated (p : α → Bool) (xs : List α) : xs.IsRotated (cycRot p xs) := by
  have h := List.isRotated_append (l := xs.take (xs.findIdx (fun x => !p x) + 1))
    (l' := xs.drop (xs.findIdx (fun x => !p x) + 1))
  rw [List.take_append_drop] at h
  exact h

private theorem cycRot_of_all (p : α → Bool) (xs : List α) (h : ∀ x ∈ xs, p x = true) :
    cycRot p xs = xs := by
  have hi : xs.findIdx (fun x => !p x) = xs.length :=
    List.findIdx_eq_length.mpr (fun x hx => by simp [h x hx])
  simp only [cycRot, hi]
  rw [List.drop_eq_nil_of_le (Nat.le_succ _), List.take_of_length_le (Nat.le_succ _),
    List.nil_append]

private theorem cycRot_last (p : α → Bool) (xs : List α) (h : ∃ x ∈ xs, p x = false) :
    ∃ w z, cycRot p xs = w ++ [z] ∧ p z = false := by
  have hex : ∃ x ∈ xs, (fun x => !p x) x = true := by
    obtain ⟨x, hx, hpx⟩ := h
    exact ⟨x, hx, by simp [hpx]⟩
  have hi := List.findIdx_lt_length_of_exists hex
  have hz := List.findIdx_getElem (w := hi)
  refine ⟨xs.drop (xs.findIdx (fun x => !p x) + 1) ++ xs.take (xs.findIdx (fun x => !p x)),
    xs[xs.findIdx (fun x => !p x)], ?_, by simpa using hz⟩
  rw [List.append_assoc, List.take_concat_get']
  rfl

theorem mem_cycRuns_flatten (p : α → Bool) (xs : List α) (x : α) :
    x ∈ (cycRuns p xs).flatten ↔ x ∈ xs ∧ p x = true := by
  rw [cycRuns, pRuns_flatten, List.mem_filter, (cycRot_isRotated p xs).perm.mem_iff]

theorem cycRuns_flatten_nodup (p : α → Bool) {xs : List α} (hn : xs.Nodup) :
    (cycRuns p xs).flatten.Nodup := by
  rw [cycRuns, pRuns_flatten]
  exact ((cycRot_isRotated p xs).nodup_iff.mp hn).filter _

theorem cycRuns_spec (p : α → Bool) (xs : List α) :
    ∀ r ∈ cycRuns p xs, r ≠ [] ∧ ∀ x ∈ r, x ∈ xs ∧ p x = true := by
  intro r hr
  obtain ⟨hne, hp⟩ := pRuns_spec p _ r hr
  refine ⟨hne, fun x hx => ⟨?_, hp x hx⟩⟩
  have hm := (pRuns_infix p _ r hr).subset hx
  exact (cycRot_isRotated p xs).perm.mem_iff.mpr hm

/-- Each run is an arc of the cyclic order. -/
theorem cycRuns_isArc [DecidableEq α] (p : α → Bool) {xs : List α} (hn : xs.Nodup)
    {r : List α} (hr : r ∈ cycRuns p xs) : IsArc (fun x => decide (x ∈ r)) xs := by
  obtain ⟨s, t, hst⟩ := pRuns_infix p _ r hr
  have hrot : xs.IsRotated (r ++ (t ++ s)) := by
    have h₁ := cycRot_isRotated p xs
    rw [← hst] at h₁
    refine h₁.trans ?_
    have h₂ := List.isRotated_append (l := s) (l' := r ++ t)
    simpa only [List.append_assoc] using h₂
  have hn' := hrot.nodup_iff.mp hn
  refine ⟨r, t ++ s, hrot, fun x hx => by simpa using hx, fun x hx => ?_⟩
  have hd := (List.nodup_append.mp hn').2.2
  simpa using fun hxr => hd x hxr x hx rfl

/-- A rotation of `u ++ v` either puts `u` in one piece or cuts it, with its first part at the
end. -/
private theorem rotated_cases {ys u v : List α} (h : ys.IsRotated (u ++ v)) :
    (∃ s t, ys = t ++ u ++ s ∧ v = s ++ t) ∨
      ∃ u₁ u₂, u = u₁ ++ u₂ ∧ u₁ ≠ [] ∧ ys = u₂ ++ v ++ u₁ := by
  obtain ⟨n, hn, hrot⟩ := List.isRotated_iff_mod.mp h.symm
  rw [List.rotate_eq_drop_append_take hn, List.drop_append, List.take_append] at hrot
  by_cases hu : n ≤ u.length
  · have h0 : n - u.length = 0 := Nat.sub_eq_zero_of_le hu
    rw [h0, List.drop_zero, List.take_zero, List.append_nil] at hrot
    by_cases hz : u.take n = []
    · have hdrop : u.drop n = u := by
        have := List.take_append_drop n u
        rw [hz, List.nil_append] at this
        exact this
      left
      refine ⟨v, [], ?_, by simp⟩
      rw [← hrot, hz, hdrop]
      simp
    · right
      exact ⟨u.take n, u.drop n, (List.take_append_drop n u).symm, hz, hrot.symm⟩
  · have hle : u.length ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hu)
    rw [List.drop_eq_nil_of_le hle, List.take_of_length_le hle, List.nil_append] at hrot
    left
    refine ⟨v.take (n - u.length), v.drop (n - u.length), ?_, (List.take_append_drop _ _).symm⟩
    rw [← hrot, List.append_assoc]

/-- An arc of the cyclic order whose elements all have `p` lies in one run, if it is not
empty. -/
theorem cycRuns_block (p q : α → Bool) {xs : List α} (hq : IsArc q xs)
    (hqp : ∀ x ∈ xs, q x = true → p x = true) (hex : ∃ x ∈ xs, q x = true) :
    ∃ r ∈ cycRuns p xs, ∀ x ∈ xs, q x = true → x ∈ r := by
  by_cases hall : ∀ x ∈ xs, p x = true
  · have hne : xs ≠ [] := by
      obtain ⟨x, hx, _⟩ := hex
      exact List.ne_nil_of_mem hx
    obtain ⟨r, hr, hm⟩ := pRuns_block p [] xs [] hne hall
    refine ⟨r, ?_, fun x hx _ => hm x hx⟩
    rw [cycRuns, cycRot_of_all p xs hall]
    simpa using hr
  · have hnp : ∃ x ∈ xs, p x = false := by
      by_contra hc
      exact hall fun x hx => by
        by_contra hpx
        exact hc ⟨x, hx, by simpa using hpx⟩
    obtain ⟨w, z, hwz, hz⟩ := cycRot_last p xs hnp
    have hrot := cycRot_isRotated p xs
    have hqy : IsArc q (cycRot p xs) := IsArc.of_isRotated hq hrot.symm
    obtain ⟨u, v, huv, hu, hv⟩ := hqy
    have hmem : ∀ x, x ∈ cycRot p xs ↔ x ∈ xs := fun x => hrot.perm.mem_iff.symm
    have hmemuv : ∀ x, x ∈ cycRot p xs ↔ x ∈ u ++ v := fun x => huv.perm.mem_iff
    rcases rotated_cases huv with ⟨s, t, hys, hvst⟩ | ⟨u₁, u₂, hu₁₂, hne, hys⟩
    · have hune : u ≠ [] := by
        rintro rfl
        obtain ⟨x, hx, hqx⟩ := hex
        have hxv : x ∈ v := by simpa using (hmemuv x).mp ((hmem x).mpr hx)
        rw [hv x hxv] at hqx
        exact Bool.false_ne_true hqx
      have hup : ∀ x ∈ u, p x = true := fun x hx =>
        hqp x ((hmem x).mp ((hmemuv x).mpr (List.mem_append_left v hx))) (hu x hx)
      obtain ⟨r, hr, hm⟩ := pRuns_block p t u s hune hup
      refine ⟨r, by rw [cycRuns, hys]; exact hr, fun x hx hqx => hm x ?_⟩
      have hx' := (hmem x).mpr hx
      rw [hys] at hx'
      rcases List.mem_append.mp hx' with hx' | hx'
      · rcases List.mem_append.mp hx' with hx' | hx'
        · have : x ∈ v := hvst ▸ List.mem_append_right s hx'
          rw [hv x this] at hqx
          exact absurd hqx Bool.false_ne_true
        · exact hx'
      · have : x ∈ v := hvst ▸ List.mem_append_left t hx'
        rw [hv x this] at hqx
        exact absurd hqx Bool.false_ne_true
    · exfalso
      have hlast : (cycRot p xs).getLast? = some z := by rw [hwz]; simp
      have hlast' : (cycRot p xs).getLast? = u₁.getLast? := by
        rw [hys, List.getLast?_append, List.getLast?_eq_some_getLast hne]
        simp
      rw [hlast] at hlast'
      have hzu : z ∈ u := hu₁₂ ▸ List.mem_append_left u₂
        (List.mem_of_getLast? hlast'.symm)
      have hzx : z ∈ xs := (hmem z).mp ((hmemuv z).mpr (List.mem_append_left v hzu))
      rw [hqp z hzx (hu z hzu)] at hz
      exact absurd hz (by simp)

end MinCostFlow.SparseCore
