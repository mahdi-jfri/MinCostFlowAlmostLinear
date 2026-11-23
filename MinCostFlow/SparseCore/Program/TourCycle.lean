module

public import MinCostFlow.Bundle.CoreRotation
public import MinCostFlow.SparseCore.Program.ContractOrder

/-!
# Cyclic successor chains and orbit uniqueness

This file develops the elementary combinatorics of cyclic successor maps on `Nodup` lists:
* `cycNext`, `IsSuccChain`, `IsCycleOf`
* `cycNext_isRotated`
* `isRotated_of_cycNext_eq` (orbit uniqueness for two `Nodup` cycles sharing an element and a
  successor map)
* `tour_rotateToList_eq_of_isRotated`
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

/-! ## Cyclic successor and successor chains -/

/-- The cyclic successor of `x` in `xs` (defaulting to `(0, true)` on the empty list). -/
def cycNext (xs : List End) (x : End) : End :=
  xs.getD ((xs.idxOf x + 1) % xs.length) (0, true)

/-- Every adjacent pair `(a, b)` in `xs` satisfies `f a = b`. -/
def IsSuccChain (f : End → End) : List End → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => f a = b ∧ IsSuccChain f (b :: rest)

/-- `xs` is a closed cycle of `f`: adjacent entries follow `f`, and the last entry maps to the
first. -/
def IsCycleOf (f : End → End) (xs : List End) : Prop :=
  IsSuccChain f xs ∧ ∀ a b, xs.head? = some a → xs.getLast? = some b → f b = a

theorem isSuccChain_append {f : End → End} {xs ys : List End}
    (hx : IsSuccChain f xs) (hy : IsSuccChain f ys)
    (hlink : ∀ a b, xs.getLast? = some a → ys.head? = some b → f a = b) :
    IsSuccChain f (xs ++ ys) := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => trivial
      | cons y ys => exact ⟨hlink x y rfl rfl, hy⟩
    | cons x' xs =>
      refine ⟨hx.1, ih hx.2 fun a b ha hb => hlink a b ?_ hb⟩
      simpa [List.getLast?_cons_cons] using ha

theorem isSuccChain_of_append_left {f : End → End} {xs ys : List End}
    (h : IsSuccChain f (xs ++ ys)) : IsSuccChain f xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    cases xs with
    | nil => trivial
    | cons x' xs => exact ⟨h.1, ih h.2⟩

theorem isSuccChain_of_append_right {f : End → End} {xs ys : List End}
    (h : IsSuccChain f (xs ++ ys)) : IsSuccChain f ys := by
  induction xs with
  | nil => simpa using h
  | cons x xs ih =>
    cases hxs : xs ++ ys with
    | nil =>
      have : ys = [] := (List.append_eq_nil_iff.mp hxs).2
      subst this; trivial
    | cons b rest =>
      rw [List.cons_append, hxs] at h
      exact ih (hxs ▸ h.2)

theorem isSuccChain_link_of_append {f : End → End} {xs ys : List End}
    (h : IsSuccChain f (xs ++ ys)) {a b : End}
    (ha : xs.getLast? = some a) (hb : ys.head? = some b) : f a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hxa : x = a := Option.some.inj ha
      subst hxa
      cases ys with
      | nil => simp at hb
      | cons y ys =>
        have hyb : y = b := Option.some.inj hb
        subst hyb
        exact h.1
    | cons x' xs =>
      exact ih h.2 (by simpa [List.getLast?_cons_cons] using ha)

private theorem isSuccChain_getElem {f : End → End} {xs : List End}
    (h : IsSuccChain f xs) :
    ∀ (i : ℕ) (hi : i + 1 < xs.length), f (xs[i]'(by omega)) = xs[i + 1]'hi := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    cases xs with
    | nil => intro i hi; simp at hi
    | cons y ys =>
      intro i hi
      cases i with
      | zero => exact h.1
      | succ j => exact ih h.2 j (by simpa using hi)

private theorem isCycleOf_getElem {f : End → End} {xs : List End} (h : IsCycleOf f xs)
    {i : ℕ} (hi : i < xs.length) :
    f (xs[i]'hi) = xs[(i + 1) % xs.length]'(Nat.mod_lt _ (by omega)) := by
  by_cases hlt : i + 1 < xs.length
  · simp only [Nat.mod_eq_of_lt hlt]
    exact isSuccChain_getElem h.1 i hlt
  · have heq : i + 1 = xs.length := by omega
    simp only [heq, Nat.mod_self]
    have hhead : xs.head? = some (xs[0]'(by omega)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    have hlast : xs.getLast? = some (xs[i]'hi) := by
      rw [List.getLast?_eq_getElem?]
      have hidx : xs.length - 1 = i := by omega
      simp only [hidx, List.getElem?_eq_getElem hi]
    exact h.2 _ _ hhead hlast

theorem cycNext_eq_getElem {xs : List End} {i : ℕ} (hnd : xs.Nodup) (hi : i < xs.length) :
    cycNext xs (xs[i]'hi) = xs[(i + 1) % xs.length]'(Nat.mod_lt _ (by omega)) := by
  have hidx : xs.idxOf (xs[i]'hi) = i := by
    have hlt := List.idxOf_lt_length_of_mem (List.getElem_mem hi)
    exact (hnd.getElem_inj_iff).mp (List.getElem_idxOf hlt)
  unfold cycNext
  rw [hidx, List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega))]

theorem isCycleOf_iff_cycNext {f : End → End} {xs : List End} (hnd : xs.Nodup) :
    IsCycleOf f xs ↔ ∀ z ∈ xs, cycNext xs z = f z := by
  constructor
  · intro hc z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    rw [cycNext_eq_getElem hnd hi]
    exact (isCycleOf_getElem hc hi).symm
  · intro hf
    refine ⟨?_, ?_⟩
    · have hget : ∀ (i : ℕ) (hi : i + 1 < xs.length), f (xs[i]'(by omega)) = xs[i + 1]'hi := by
        intro i hi
        have hi0 : i < xs.length := by omega
        have hstep := (hf (xs[i]'hi0) (List.getElem_mem hi0)).symm
        rw [cycNext_eq_getElem hnd hi0] at hstep
        simpa only [Nat.mod_eq_of_lt hi] using hstep
      clear hf
      induction xs with
      | nil => trivial
      | cons x xs ih =>
        cases xs with
        | nil => trivial
        | cons y ys =>
          refine ⟨hget 0 (by simp), ih (List.nodup_cons.mp hnd).2 fun i hi => ?_⟩
          exact hget (i + 1) (by simpa using hi)
    · intro a b ha hb
      cases xs with
      | nil => simp at ha
      | cons x xs =>
        have hpos : 0 < (x :: xs).length := by simp
        have hlast_lt : (x :: xs).length - 1 < (x :: xs).length := by omega
        have ha' : a = (x :: xs)[0]'hpos := by simpa using ha.symm
        have hb' : b = (x :: xs)[(x :: xs).length - 1]'hlast_lt := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_lt] at hb
          exact (Option.some.inj hb).symm
        rw [hb', ha']
        have hstep := (hf ((x :: xs)[(x :: xs).length - 1]'hlast_lt) (List.getElem_mem hlast_lt)).symm
        rw [cycNext_eq_getElem hnd hlast_lt] at hstep
        have hmod : ((x :: xs).length - 1 + 1) % (x :: xs).length = 0 := by
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
        simpa only [hmod] using hstep

theorem cycNext_isRotated {xs ys : List End} (hnd : xs.Nodup) (hrot : xs.IsRotated ys)
    {z : End} (hz : z ∈ xs) : cycNext ys z = cycNext xs z := by
  obtain ⟨k, hk, rfl⟩ := List.isRotated_iff_mod.mp hrot
  have hnd' : (xs.rotate k).Nodup := (List.rotate_perm xs k).nodup_iff.mpr hnd
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  have hpos : 0 < xs.length := by omega
  let j := (i + xs.length - k) % xs.length
  have hj : j < (xs.rotate k).length := by rw [List.length_rotate]; exact Nat.mod_lt _ hpos
  have hj_eq : (xs.rotate k)[j]'hj = xs[i]'hi := by
    rw [List.getElem_rotate]
    congr 1
    dsimp only [j]
    rw [Nat.mod_add_mod]
    have : i + xs.length - k + k = i + xs.length := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  conv_lhs => rw [← hj_eq, cycNext_eq_getElem hnd' hj]
  rw [cycNext_eq_getElem hnd hi, List.getElem_rotate]
  congr 1
  rw [List.length_rotate]
  dsimp only [j]
  have hstep : (i + xs.length - k) % xs.length + 1 + k ≡ (i + xs.length - k) + 1 + k [MOD xs.length] :=
    ((Nat.mod_modEq _ _).add_right 1).add_right k
  have hstep2 : ((i + xs.length - k) % xs.length + 1) % xs.length + k ≡
      (i + xs.length - k) % xs.length + 1 + k [MOD xs.length] :=
    (Nat.mod_modEq _ _).add_right k
  have hlin : i + xs.length - k + 1 + k = i + 1 + xs.length := by omega
  have hstep3 : i + 1 + xs.length ≡ i + 1 [MOD xs.length] := by simp [Nat.ModEq]
  exact (hstep2.trans hstep).trans (hlin ▸ hstep3)

theorem rotateToList_isRotated {y : End} {xs : List End} : xs.IsRotated (rotateToList y xs) := by
  unfold rotateToList
  split_ifs with h
  · have he := List.take_append_drop (xs.idxOf y) xs
    conv_lhs => rw [← he]
    exact List.isRotated_append
  · exact List.IsRotated.refl xs

theorem rotateToList_head? {y : End} {xs : List End} (h : y ∈ xs) :
    (rotateToList y xs).head? = some y := by
  unfold rotateToList
  rw [ite_eq_left_iff.mpr (fun hn => absurd h hn)]
  have hlt := List.idxOf_lt_length_of_mem h
  have hdrop : xs.drop (xs.idxOf y) ≠ [] := by
    intro he
    have := congrArg List.length he
    simp at this
    omega
  rw [List.head?_append_of_ne_nil _ hdrop, List.head?_drop, List.getElem?_eq_getElem hlt,
    List.getElem_idxOf hlt]

private theorem iter_eq_getElem {f : End → End} {xs : List End}
    (hc : IsCycleOf f xs) {a : End} (hhead : xs.head? = some a) :
    ∀ k, f^[k] a = xs[k % xs.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil
      (by intro h0; rw [h0] at hhead; simp at hhead))) := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.zero_mod]
    cases xs with
    | nil => simp at hhead
    | cons x rest => simpa using hhead.symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, isCycleOf_getElem hc]
    congr 1
    rw [Nat.mod_add_mod]

/-- Orbit uniqueness: two `Nodup` cycles of the same function `f` that share an element `a` are
cyclic rotations of each other. -/
theorem isRotated_of_cycNext_eq {f : End → End} {xs ys : List End}
    (hx : xs.Nodup) (hy : ys.Nodup) {a : End} (hax : a ∈ xs) (hay : a ∈ ys)
    (hfx : ∀ z ∈ xs, cycNext xs z = f z) (hfy : ∀ z ∈ ys, cycNext ys z = f z) :
    xs.IsRotated ys := by
  let xs' := rotateToList a xs
  let ys' := rotateToList a ys
  have hrx : xs.IsRotated xs' := rotateToList_isRotated
  have hry : ys.IsRotated ys' := rotateToList_isRotated
  have hndx' : xs'.Nodup := hrx.perm.nodup_iff.mp hx
  have hndy' : ys'.Nodup := hry.perm.nodup_iff.mp hy
  have hcx : IsCycleOf f xs' := (isCycleOf_iff_cycNext hndx').mpr fun z hz => by
    have hz0 := hrx.perm.mem_iff.mpr hz
    rw [cycNext_isRotated hx hrx hz0, hfx z hz0]
  have hcy : IsCycleOf f ys' := (isCycleOf_iff_cycNext hndy').mpr fun z hz => by
    have hz0 := hry.perm.mem_iff.mpr hz
    rw [cycNext_isRotated hy hry hz0, hfy z hz0]
  have hhx : xs'.head? = some a := rotateToList_head? hax
  have hhy : ys'.head? = some a := rotateToList_head? hay
  have hposx : 0 < xs'.length := List.length_pos_of_ne_nil (by intro h0; rw [h0] at hhx; simp at hhx)
  have hposy : 0 < ys'.length := List.length_pos_of_ne_nil (by intro h0; rw [h0] at hhy; simp at hhy)
  have hitx := iter_eq_getElem hcx hhx
  have hity := iter_eq_getElem hcy hhy
  have hlen : xs'.length = ys'.length := by
    apply le_antisymm
    · by_contra hgt
      have hlt : ys'.length < xs'.length := by omega
      have h1 := hitx ys'.length
      have h2 := hity ys'.length
      simp only [Nat.mod_eq_of_lt hlt] at h1
      simp only [Nat.mod_self] at h2
      have h0 := hitx 0; simp only [Nat.zero_mod] at h0
      have h0y := hity 0; simp only [Nat.zero_mod] at h0y
      have heq : xs'[ys'.length]'hlt = xs'[0]'hposx := by rw [← h1, h2, ← h0y, h0]
      have := (hndx'.getElem_inj_iff).mp heq
      omega
    · by_contra hgt
      have hlt : xs'.length < ys'.length := by omega
      have h1 := hity xs'.length
      have h2 := hitx xs'.length
      simp only [Nat.mod_eq_of_lt hlt] at h1
      simp only [Nat.mod_self] at h2
      have h0 := hity 0; simp only [Nat.zero_mod] at h0
      have h0x := hitx 0; simp only [Nat.zero_mod] at h0x
      have heq : ys'[xs'.length]'hlt = ys'[0]'hposy := by rw [← h1, h2, ← h0x, h0]
      have := (hndy'.getElem_inj_iff).mp heq
      omega
  have heq : xs' = ys' := by
    refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
    have hx_i := hitx i
    have hy_i := hity i
    simp only [Nat.mod_eq_of_lt hi₁] at hx_i
    simp only [Nat.mod_eq_of_lt hi₂] at hy_i
    exact hx_i.symm.trans hy_i
  exact hrx.trans (heq ▸ hry.symm)

/-- Rotating any cyclic rotation of a `Nodup` list to start at its head recovers it identically. -/
theorem tour_rotateToList_eq_of_isRotated {xs ys : List End} {a : End}
    (hnd : xs.Nodup) (hrot : ys.IsRotated xs) (hhead : xs.head? = some a) :
    rotateToList a ys = xs := by
  have ha : a ∈ xs := List.mem_of_head? hhead
  have hay : a ∈ ys := hrot.perm.mem_iff.mpr ha
  let zs := rotateToList a ys
  have hrz : ys.IsRotated zs := rotateToList_isRotated
  have hzx : zs.IsRotated xs := hrz.symm.trans hrot
  have hndz : zs.Nodup := hzx.perm.nodup_iff.mpr hnd
  have hhz : zs.head? = some a := rotateToList_head? hay
  cases xs with
  | nil => simp at hhead
  | cons x rest =>
    have hxa : x = a := Option.some.inj hhead
    subst hxa
    cases hzs : zs with
    | nil => rw [hzs] at hhz; simp at hhz
    | cons z zrest =>
      rw [hzs] at hhz hzx hndz
      have hza : z = x := Option.some.inj hhz
      subst hza
      obtain ⟨k, hrotk⟩ := hzx
      rw [← List.rotate_mod] at hrotk
      let i := k % (z :: zrest).length
      have hi : i < (z :: zrest).length := Nat.mod_lt _ (by simp)
      have hh := congrArg List.head? hrotk
      rw [List.head?_rotate hi, List.getElem?_eq_getElem hi] at hh
      have he : (z :: zrest)[i] = (z :: zrest)[0] := Option.some.inj hh
      have hi0 : i = 0 := hndz.getElem_inj_iff.mp he
      change (z :: zrest).rotate i = z :: rest at hrotk
      rw [hi0, List.rotate_zero] at hrotk
      exact hzs.trans hrotk

end MinCostFlow.SparseCore.Program
