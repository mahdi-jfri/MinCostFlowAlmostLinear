module

public import Mathlib.Data.List.Rotate

/-!
# Cyclic boundary counts

Count changes of membership along a closed list. Filtering the list shortcuts
the deleted entries, and a shortcut cannot add a change.
-/

@[expose] public section

namespace MinCostFlow.Bundle

/-- An edge end. The side is the direction of the dart
whose source is this end: `true` at the tail and `false` at the head. -/
abbrev End := ℕ × Bool

/-- A representative of a cyclic order.
Representatives are compared by `List.IsRotated`. -/
abbrev CyclicOrder (α : Type*) := { xs : List α // xs.Nodup }

/-- Count changes along the path from `a`, through `xs`, to `b`. -/
def pathBdry {α : Type*} (p : α → Bool) (a : α) : List α → α → ℕ
  | [], b => if p a = p b then 0 else 1
  | x :: xs, b => (if p a = p x then 0 else 1) + pathBdry p x xs b

/-- Count changes of membership between cyclic successors. -/
def cycBdry {α : Type*} (p : α → Bool) : List α → ℕ
  | [] => 0
  | x :: xs => pathBdry p x xs x

private theorem pathBdry_join {α : Type*} (p : α → Bool) (a b c : α)
    (xs ys : List α) :
    pathBdry p a (xs ++ b :: ys) c = pathBdry p a xs b + pathBdry p b ys c := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [pathBdry, ih, Nat.add_assoc]

/-- Swapping a prefix and suffix preserves the cyclic count. -/
theorem cycBdry_append_comm {α : Type*} (p : α → Bool) (xs ys : List α) :
    cycBdry p (xs ++ ys) = cycBdry p (ys ++ xs) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.cons_append, cycBdry, pathBdry_join]
      exact Nat.add_comm _ _

/-- The boundary count depends only on the cyclic order. -/
theorem cycBdry_isRotated {α : Type*} (p : α → Bool) {xs ys : List α}
    (h : xs.IsRotated ys) : cycBdry p xs = cycBdry p ys := by
  obtain ⟨n, hn, rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn, cycBdry_append_comm, List.take_append_drop]

private theorem pathBdry_compl {α : Type*} (p : α → Bool) (a b : α) (xs : List α) :
    pathBdry (fun x => !(p x)) a xs b = pathBdry p a xs b := by
  induction xs generalizing a with
  | nil => simp [pathBdry]
  | cons x xs ih => simp [pathBdry, ih]

/-- Complementing membership preserves boundary pairs. -/
theorem cycBdry_compl {α : Type*} (p : α → Bool) (xs : List α) :
    cycBdry (fun x => !(p x)) xs = cycBdry p xs := by
  cases xs <;> simp [cycBdry, pathBdry_compl]

/-- A set is an arc if a representative starts with just its members. -/
def IsArc {α : Type*} (p : α → Bool) (xs : List α) : Prop :=
  ∃ inside outside : List α, xs.IsRotated (inside ++ outside) ∧
    (∀ x ∈ inside, p x = true) ∧ (∀ x ∈ outside, p x = false)

private theorem pathBdry_constant {α : Type*} (p : α → Bool) (a b : α)
    (xs : List α) (h : ∀ x ∈ xs, p x = p a) :
    pathBdry p a xs b = (if p a = p b then 0 else 1) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    rw [pathBdry, ih x (fun y hy => (h y (by simp [hy])).trans hx.symm)]
    simp [hx]

/-- Only the two joins can count for an arc. -/
theorem IsArc.cycBdry_le {α : Type*} {p : α → Bool} {xs : List α}
    (h : IsArc p xs) : cycBdry p xs ≤ 2 := by
  obtain ⟨inside, outside, hr, hi, ho⟩ := h
  rw [cycBdry_isRotated p hr]
  cases inside with
  | nil =>
    cases outside with
    | nil => simp [cycBdry]
    | cons y ys =>
      simp [cycBdry, pathBdry_constant p y y ys
        (fun z hz => (ho z (by simp [hz])).trans (ho y (by simp)).symm)]
  | cons x xs =>
    have hx := hi x (by simp)
    have hxs : ∀ z ∈ xs, p z = p x :=
      fun z hz => (hi z (by simp [hz])).trans hx.symm
    cases outside with
    | nil => simp [cycBdry, pathBdry_constant p x x xs hxs]
    | cons y ys =>
      have hy := ho y (by simp)
      have hys : ∀ z ∈ ys, p z = p y :=
        fun z hz => (ho z (by simp [hz])).trans hy.symm
      simp [cycBdry, pathBdry_join, pathBdry_constant p x y xs hxs,
        pathBdry_constant p y x ys hys, hx, hy]

private def changeCount {α : Type*} (p : α → Bool) (a b : α) : ℕ :=
  if p a = p b then 0 else 1

private theorem changeCount_triangle {α : Type*} (p : α → Bool) (a b c : α) :
    changeCount p a c ≤ changeCount p a b + changeCount p b c := by
  cases ha : p a <;> cases hb : p b <;> cases hc : p c <;>
    simp [changeCount, ha, hb, hc]

private theorem pathBdry_shortcut {α : Type*} (p : α → Bool) (a x b : α)
    (xs : List α) : pathBdry p a xs b ≤ pathBdry p a (x :: xs) b := by
  cases xs with
  | nil => exact changeCount_triangle p a x b
  | cons y ys =>
    have h := Nat.add_le_add_right (changeCount_triangle p a x y) (pathBdry p y ys b)
    simpa only [pathBdry, changeCount, Nat.add_assoc] using h

private theorem pathBdry_filter_le {α : Type*} (p q : α → Bool) (a b : α)
    (xs : List α) : pathBdry p a (xs.filter q) b ≤ pathBdry p a xs b := by
  induction xs generalizing a with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    cases h : q x
    · rw [List.filter_cons_of_neg (by simp [h])]
      exact (ih a).trans (pathBdry_shortcut p a x b xs)
    · rw [List.filter_cons_of_pos h]
      exact Nat.add_le_add_left (ih x) _

private theorem pathBdry_append_singleton_le {α : Type*} (p : α → Bool)
    (a x b : α) (xs : List α) : pathBdry p a xs b ≤ pathBdry p a (xs ++ [x]) b := by
  induction xs generalizing a with
  | nil => exact changeCount_triangle p a x b
  | cons z zs ih => exact Nat.add_le_add_left (ih z) _

/-- Skipping elements cannot add cyclic boundary pairs. -/
theorem cycBdry_filter_le {α : Type*} (p q : α → Bool) (xs : List α) :
    cycBdry p (xs.filter q) ≤ cycBdry p xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    cases h : q x
    · rw [List.filter_cons_of_neg (by simp [h])]
      apply ih.trans
      cases xs with
      | nil => exact Nat.zero_le _
      | cons y ys =>
        rw [cycBdry_isRotated p (List.isRotated_concat x (y :: ys)).symm]
        simp only [List.cons_append, cycBdry]
        exact pathBdry_append_singleton_le p y x y ys
    · rw [List.filter_cons_of_pos h]
      exact pathBdry_filter_le p q x x xs

/-- Filtering both representatives preserves their cyclic order. -/
theorem isRotated_filter {α : Type*} (q : α → Bool) {xs ys : List α}
    (h : xs.IsRotated ys) : (xs.filter q).IsRotated (ys.filter q) := by
  obtain ⟨n, hn, rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn, List.filter_append]
  have he : xs.filter q = (xs.take n).filter q ++ (xs.drop n).filter q := by
    rw [← List.filter_append, List.take_append_drop]
  conv_lhs => rw [he]
  exact List.isRotated_append

/-- An arc stays an arc after restriction. -/
theorem IsArc.filter {α : Type*} {p : α → Bool} {xs : List α}
    (h : IsArc p xs) (q : α → Bool) : IsArc p (xs.filter q) := by
  obtain ⟨inside, outside, hr, hi, ho⟩ := h
  refine ⟨inside.filter q, outside.filter q, ?_, ?_, ?_⟩
  · simpa only [List.filter_append] using isRotated_filter q hr
  · exact fun x hx => hi x (List.mem_of_mem_filter hx)
  · exact fun x hx => ho x (List.mem_of_mem_filter hx)

private theorem pathBdry_skip_same {α : Type*} (p : α → Bool) (a b : α)
    (xs ys : List α) (h : ∀ x ∈ xs, p x = p a) :
    pathBdry p a (xs ++ ys) b = pathBdry p a ys b := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, p y = p x :=
      fun y hy => (h y (by simp [hy])).trans hx.symm
    simp only [List.cons_append, pathBdry, hx, ite_true, Nat.zero_add, ih x hxs]
    cases ys <;> simp [pathBdry, hx]

private theorem pathBdry_blocks {ι α : Type*} (q : ι → Bool) (p : α → Bool)
    (block : ι → List α) (is : List ι) (a b : ι) (x y : α)
    (hx : p x = q a) (hy : p y = q b)
    (hne : ∀ i ∈ is, block i ≠ [])
    (hp : ∀ i ∈ is, ∀ z ∈ block i, p z = q i) :
    pathBdry p x (is.flatMap block) y = pathBdry q a is b := by
  induction is generalizing a x with
  | nil => simp [pathBdry, hx, hy]
  | cons i is ih =>
    cases hi : block i with
    | nil => exact False.elim (hne i (by simp) hi)
    | cons z zs =>
      have hz : p z = q i := hp i (by simp) z (by simp [hi])
      have hzs : ∀ w ∈ zs, p w = p z :=
        fun w hw => (hp i (by simp) w (by simp [hi, hw])).trans hz.symm
      simp only [List.flatMap_cons, hi, List.cons_append, pathBdry]
      rw [pathBdry_skip_same p z y zs _ hzs]
      rw [ih i z hz (fun j hj => hne j (by simp [hj]))
        (fun j hj => hp j (by simp [hj])), hx, hz]

private theorem flatMap_filter_nonempty {ι α : Type*} (block : ι → List α) (is : List ι) :
    (is.filter (fun i => !(block i).isEmpty)).flatMap block = is.flatMap block := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    cases hi : block i <;> simp [hi, ih]

/-- Only joins between nonempty blocks count, and skipping empty blocks cannot add
boundary pairs. -/
theorem cycBdry_blocks {ι α : Type*} (q : ι → Bool) (p : α → Bool)
    (block : ι → List α) (is : List ι)
    (hp : ∀ i ∈ is, ∀ x ∈ block i, p x = q i) :
    cycBdry p (is.flatMap block) ≤ cycBdry q is := by
  let js := is.filter (fun i => !(block i).isEmpty)
  have he : js.flatMap block = is.flatMap block := flatMap_filter_nonempty block is
  have hne : ∀ j ∈ js, block j ≠ [] := by
    intro j hj
    have h := (List.mem_filter.mp hj).2
    intro hnil
    simp [hnil] at h
  have hmem : ∀ j ∈ js, ∀ z ∈ block j, p z = q j :=
    fun j hj => hp j (List.mem_of_mem_filter hj)
  have hle : cycBdry q js ≤ cycBdry q is := cycBdry_filter_le q _ is
  rw [← he]
  apply Nat.le_trans _ hle
  clear he
  clear_value js
  cases js with
  | nil => simp [cycBdry]
  | cons j js =>
    cases hj : block j with
    | nil => exact False.elim (hne j (by simp) hj)
    | cons x xs =>
      have hx := hmem j (by simp) x (by simp [hj])
      have hxs : ∀ z ∈ xs, p z = p x :=
        fun z hz => (hmem j (by simp) z (by simp [hj, hz])).trans hx.symm
      simp only [List.flatMap_cons, hj, List.cons_append, cycBdry]
      rw [pathBdry_skip_same p x x xs _ hxs,
        pathBdry_blocks q p block js j j x x hx hx
          (fun i hi => hne i (by simp [hi])) (fun i hi => hmem i (by simp [hi]))]


/-- Boundary counts depend on the test only at entries of the list. -/
theorem cycBdry_congr_on {α : Type*} {p q : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = q x) : cycBdry p xs = cycBdry q xs := by
  have hmap : xs.map p = xs.map q := List.map_congr_left h
  have he (f : α → Bool) : cycBdry f xs = cycBdry id (xs.map f) := by
    have hp (a z : α) (ys : List α) :
        pathBdry f a ys z = pathBdry id (f a) (ys.map f) (f z) := by
      induction ys generalizing a with
      | nil => rfl
      | cons y ys ih => simp only [pathBdry, List.map_cons, id_eq, ih]
    cases xs
    · rfl
    · exact hp _ _ _
  rw [he p, he q, hmap]

end MinCostFlow.Bundle
