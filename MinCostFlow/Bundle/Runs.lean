module

public import MinCostFlow.Bundle.Initialize

/-!
# Runs of a bundle

Each change of side starts a new run. For a bundle that occupies the whole
cycle, start at a boundary if there is one, so a run does not cross the join.
-/

@[expose] public section

namespace MinCostFlow.Bundle

/-- The run starting at `a`, and the remaining runs, in a linear order. -/
def runsFrom {α : Type*} (p : α → Bool) (a : α) : List α → List α × List (List α)
  | [] => ([a], [])
  | x :: xs =>
    let (first, rest) := runsFrom p x xs
    if p a = p x then (a :: first, rest) else ([a], first :: rest)

/-- Split a linear order into its maximal runs of one side. -/
def linearRuns {α : Type*} (p : α → Bool) : List α → List (List α)
  | [] => []
  | a :: xs => let (first, rest) := runsFrom p a xs; first :: rest

/-- Start immediately after the first run. If there is just one run, this
leaves the order unchanged. -/
def cycleRunStart {α : Type*} (p : α → Bool) : List α → List α
  | [] => []
  | a :: xs => (a :: xs).dropWhile (fun x => p x == p a) ++
      (a :: xs).takeWhile (fun x => p x == p a)

/-- Split a bundle into maximal runs.
For a proper arc the given order starts at its first end. For a whole
cycle there is no distinguished first end. -/
def bundleRuns {α : Type*} (p : α → Bool) (whole : Bool) (xs : List α) : List (List α) :=
  linearRuns p (if whole then cycleRunStart p xs else xs)

private theorem runsFrom_flatten {α : Type*} (p : α → Bool) (a : α) (xs : List α) :
    (runsFrom p a xs).1 ++ (runsFrom p a xs).2.flatten = a :: xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [runsFrom]
    cases hr : runsFrom p x xs with
    | mk first rest =>
      have ihx := ih x
      simp only [hr] at ihx
      by_cases hp : p a = p x <;> simp [hp, ihx]

/-- The runs partition the input and preserve its order. -/
theorem linearRuns_flatten {α : Type*} (p : α → Bool) (xs : List α) :
    (linearRuns p xs).flatten = xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simpa only [linearRuns, List.flatten_cons] using runsFrom_flatten p a xs

private theorem runsFrom_nonempty {α : Type*} (p : α → Bool) (a : α) (xs : List α) :
    (runsFrom p a xs).1 ≠ [] ∧ ∀ ys ∈ (runsFrom p a xs).2, ys ≠ [] := by
  induction xs generalizing a with
  | nil => simp [runsFrom]
  | cons x xs ih =>
    rw [runsFrom]
    cases hr : runsFrom p x xs with
    | mk first rest =>
      have ihx := ih x
      simp only [hr] at ihx
      by_cases hp : p a = p x
      · simpa [hp] using ihx.2
      · simpa [hp, ihx.1] using ihx.2

private theorem runsFrom_first_side {α : Type*} (p : α → Bool) (a : α) (xs : List α) :
    ∀ y ∈ (runsFrom p a xs).1, p y = p a := by
  induction xs generalizing a with
  | nil => simp [runsFrom]
  | cons x xs ih =>
    rw [runsFrom]
    cases hr : runsFrom p x xs with
    | mk first rest =>
      have ihx := ih x
      simp only [hr] at ihx
      by_cases hp : p a = p x
      · simpa [hp] using ihx
      · simp [hp]

private theorem runsFrom_sides {α : Type*} (p : α → Bool) (a : α) (xs : List α) :
    ∀ ys ∈ (runsFrom p a xs).2, ∃ side : Bool, ∀ y ∈ ys, p y = side := by
  induction xs generalizing a with
  | nil => simp [runsFrom]
  | cons x xs ih =>
    rw [runsFrom]
    cases hr : runsFrom p x xs with
    | mk first rest =>
      have hf := runsFrom_first_side p x xs
      have ihx := ih x
      simp only [hr] at ihx hf
      by_cases hp : p a = p x
      · simpa [hp] using ihx
      · intro ys hy
        simp only [hp, ↓reduceIte, List.mem_cons] at hy
        rcases hy with rfl | h
        · exact ⟨p x, hf⟩
        · exact ihx ys h

/-- Every run is nonempty and lies on one side of the split. -/
theorem linearRuns_spec {α : Type*} (p : α → Bool) (xs : List α) :
    ∀ ys ∈ linearRuns p xs, ys ≠ [] ∧ ∃ side : Bool, ∀ y ∈ ys, p y = side := by
  cases xs with
  | nil => simp [linearRuns]
  | cons a xs =>
    intro ys hy
    change ys ∈ (runsFrom p a xs).1 :: (runsFrom p a xs).2 at hy
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨(runsFrom_nonempty p a xs).1, p a, runsFrom_first_side p a xs⟩
    · exact ⟨(runsFrom_nonempty p a xs).2 _ hm, runsFrom_sides p a xs _ hm⟩

/-- The number of internal boundaries of a linear order. -/
def linearBdry {α : Type*} (p : α → Bool) : List α → ℕ
  | [] | [_] => 0
  | a :: x :: xs => (if p a = p x then 0 else 1) + linearBdry p (x :: xs)

private theorem runsFrom_count {α : Type*} (p : α → Bool) (a : α) (xs : List α) :
    (runsFrom p a xs).2.length = linearBdry p (a :: xs) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [runsFrom, linearBdry]
    cases hr : runsFrom p x xs with
    | mk first rest =>
      have h := ih x
      rw [hr] at h
      by_cases hp : p a = p x <;> simp [hp, ← h, Nat.add_comm]

/-- The number of fresh vertices for the linear runs equals the number of
internal boundary pairs. -/
theorem linearRuns_count {α : Type*} (p : α → Bool) (xs : List α) :
    (linearRuns p xs).length - 1 = linearBdry p xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    change ((runsFrom p a xs).2.length + 1) - 1 = _
    rw [Nat.add_sub_cancel, runsFrom_count]

private theorem linearBdry_le_path {α : Type*} (p : α → Bool) (a b : α) (xs : List α) :
    linearBdry p (a :: xs) ≤ pathBdry p a xs b := by
  induction xs generalizing a with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    rw [linearBdry, pathBdry]
    exact Nat.add_le_add_left (ih x) _

theorem cycleRunStart_isRotated {α : Type*} (p : α → Bool) (xs : List α) :
    xs.IsRotated (cycleRunStart p xs) := by
  cases xs with
  | nil => exact List.IsRotated.refl _
  | cons a xs =>
    let q : α → Bool := fun x => p x == p a
    change (a :: xs).IsRotated ((a :: xs).dropWhile q ++ (a :: xs).takeWhile q)
    have he := List.takeWhile_append_dropWhile (l := a :: xs) (p := q)
    conv_lhs => rw [← he]
    exact List.isRotated_append

/-- A bundle occupying the whole cycle creates at most the cyclic boundary
count of fresh vertices. -/
theorem bundleRuns_full_count_le {α : Type*} (p : α → Bool) (xs : List α) :
    (bundleRuns p true xs).length - 1 ≤ cycBdry p xs := by
  rw [cycBdry_isRotated p (cycleRunStart_isRotated p xs)]
  change (linearRuns p (cycleRunStart p xs)).length - 1 ≤ cycBdry p (cycleRunStart p xs)
  rw [linearRuns_count]
  cases cycleRunStart p xs with
  | nil => exact Nat.le_refl _
  | cons a xs => exact linearBdry_le_path p a a xs

/-- Splitting the two ends of a loop gives two singleton bundle runs. -/
example : bundleRuns (fun x : End => x.2) true [(0, true), (0, false)] =
    [[(0, false)], [(0, true)]] := by decide


private theorem linearBdry_append_le {α : Type*} (p : α → Bool) (xs ys : List α) :
    linearBdry p xs + linearBdry p ys ≤ linearBdry p (xs ++ ys) := by
  induction xs with
  | nil => simp [linearBdry]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [linearBdry]
      | cons y ys =>
        simp only [linearBdry, Nat.zero_add, List.cons_append, List.nil_append]
        exact Nat.le_add_left _ _
    | cons x xs =>
      simp only [linearBdry, List.cons_append, Nat.add_assoc]
      exact Nat.add_le_add_left ih _

/-- For consecutive proper bundle blocks, the total number of new runs
is bounded by the cyclic boundary count. -/
theorem linearRuns_blocks_count_le {α : Type*} (p : α → Bool) (blocks : List (List α)) :
    (blocks.map fun xs => (linearRuns p xs).length - 1).sum ≤ cycBdry p blocks.flatten := by
  have h : (blocks.map (linearBdry p)).sum ≤ linearBdry p blocks.flatten := by
    induction blocks with
    | nil => exact Nat.le_refl _
    | cons xs rest ih =>
      rw [List.map_cons, List.sum_cons, List.flatten_cons]
      exact (Nat.add_le_add_left ih _).trans (linearBdry_append_le p xs rest.flatten)
  simp only [linearRuns_count]
  apply h.trans
  cases blocks.flatten with
  | nil => exact Nat.le_refl _
  | cons a xs => exact linearBdry_le_path p a a xs


private theorem run_arc_of_flatten {α : Type*} [BEq α] [LawfulBEq α]
    {xs : List α} {runs : List (List α)} {out run : List α}
    (hn : xs.Nodup) (hr : xs.IsRotated (runs.flatten ++ out)) (hm : run ∈ runs) :
    IsArc (fun x => run.contains x) xs := by
  obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp hm
  rw [he, List.flatten_append, List.flatten_cons] at hr
  have hh := (List.isRotated_append (l := pre.flatten) (l' := run ++ post.flatten ++ out))
  have hr' : xs.IsRotated (run ++ ((post.flatten ++ out) ++ pre.flatten)) := by
    exact hr.trans (by simpa only [List.append_assoc] using hh)
  have hn' := hr'.perm.nodup_iff.mp hn
  refine ⟨run, (post.flatten ++ out) ++ pre.flatten, hr', ?_, ?_⟩
  · intro x hx
    exact List.contains_iff_mem.mpr hx
  · intro x hx
    exact Bool.eq_false_iff.mpr fun h =>
      (List.nodup_append.mp hn').2.2 x (List.contains_iff_mem.mp h) x hx rfl

/-- A run of a proper bundle lies on one side, has size at most that of
the bundle, and is an arc in the order restricted to its side. -/
theorem linearRun_restrict_arc {α : Type*} [BEq α] [LawfulBEq α] (p : α → Bool)
    {xs bundle out run : List α} (hn : xs.Nodup) (hr : xs.IsRotated (bundle ++ out))
    (hm : run ∈ linearRuns p bundle) :
    run.length ≤ bundle.length ∧ ∃ side : Bool, (∀ x ∈ run, p x = side) ∧
      IsArc (fun x => run.contains x) (xs.filter fun x => p x == side) := by
  have hrot : xs.IsRotated ((linearRuns p bundle).flatten ++ out) := by
    rwa [linearRuns_flatten]
  have harc := run_arc_of_flatten hn hrot hm
  obtain ⟨_, side, hs⟩ := linearRuns_spec p bundle run hm
  refine ⟨?_, side, hs, harc.filter _⟩
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hm
  have hflat := linearRuns_flatten p bundle
  rw [hsplit, List.flatten_append, List.flatten_cons] at hflat
  rw [← hflat]
  simp only [List.length_append]
  omega

/-- The same run bound holds for a bundle that occupies the whole cycle. -/
theorem fullBundleRun_restrict_arc {α : Type*} [BEq α] [LawfulBEq α] (p : α → Bool)
    {xs run : List α} (hn : xs.Nodup) (hm : run ∈ bundleRuns p true xs) :
    run.length ≤ xs.length ∧ ∃ side : Bool, (∀ x ∈ run, p x = side) ∧
      IsArc (fun x => run.contains x) (xs.filter fun x => p x == side) := by
  have hr : xs.IsRotated (cycleRunStart p xs ++ []) := by
    simpa only [List.append_nil] using cycleRunStart_isRotated p xs
  obtain ⟨hs, hv⟩ := linearRun_restrict_arc p hn hr hm
  rw [← (cycleRunStart_isRotated p xs).perm.length_eq] at hs
  exact ⟨hs, hv⟩

end MinCostFlow.Bundle
