module

public import MinCostFlow.HierPaths.BuildProgWalkRow
public import MinCostFlow.HierPaths.BuildProgRoundRoute

/-!
# Matching rows and their corresponding walk rows

The router stores one list of endpoint words per request and one walk per edge
of the flattened matching. The endpoint offset is twice the first walk index.
That equality lets the builder append the endpoints and find the corresponding
walks without scanning the other matching rows.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The endpoint words of one matching row. -/
def matchingRowWords (Ms : List (List (ℕ × ℕ))) (i : ℕ) : List ℕ :=
  (Ms.getD i []).flatMap fun e => [e.1, e.2]

/-- The walk row aligned with the matching row `i`. -/
def matchingWalkRow (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) (i : ℕ) : BuildWalkRow :=
  ⟨(Ms.getD i []).length, Ms.flatten.length, flatIndex Ms i 0,
      fun j => (edgeAt (Ms.getD i []) j).1, fun j => (edgeAt (Ms.getD i []) j).2, emb⟩

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The matching row stores two words per edge. -/
theorem length_matchingRowWords (Ms : List (List (ℕ × ℕ))) (i : ℕ) :
    (matchingRowWords Ms i).length = 2 * (Ms.getD i []).length := by
  simp [matchingRowWords, List.length_flatMap, Nat.mul_comm]

private theorem matchRow_prefix (Ms : List (List (ℕ × ℕ))) :
    ∀ i ≤ Ms.length, ((List.range i).map fun j => (matchingRowWords Ms j).length).sum =
      2 * flatIndex Ms i 0 := by
  intro i hi
  induction i with
  | zero => simp [flatIndex]
  | succ i ih =>
    have hi' : i < Ms.length := by omega
    have ht := List.take_succ_eq_append_getElem hi'
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      length_matchingRowWords, flatIndex, ht, List.getD_eq_getElem _ _ hi',
      List.map_append, List.sum_append]
    omega

private theorem flatIndex_last (Ms : List (List (ℕ × ℕ))) :
    flatIndex Ms Ms.length 0 = Ms.flatten.length := by
  simp [flatIndex, List.length_flatten]

/-- The router's matching offsets identify exactly the row and its first walk. -/
theorem matchingRow_view {mem : ℕ → ℕ} {tb i : ℕ} {Ms : List (List (ℕ × ℕ))}
    (hi : i < Ms.length) (hAt : ListAt mem tb (csrList Ms.length (matchingRowWords Ms))) :
    mem (tb + i) = 2 * flatIndex Ms i 0 ∧
    mem (tb + i + 1) = 2 * (flatIndex Ms i 0 + (Ms.getD i []).length) ∧
    mem (tb + Ms.length) = 2 * Ms.flatten.length ∧
    ListAt mem (tb + (Ms.length + 1) + 2 * flatIndex Ms i 0) (matchingRowWords Ms i) := by
  have h0 := csrList_offset hAt hi.le
  have h1 := csrList_offset hAt (show i + 1 ≤ Ms.length by omega)
  have h2 := csrList_offset hAt (le_refl Ms.length)
  have h3 := listAt_csrList_get hAt hi
  rw [matchRow_prefix Ms _ hi.le] at h0 h3
  rw [matchRow_prefix Ms _ (le_refl _), flatIndex_last] at h2
  rw [List.range_succ, List.map_append, List.sum_append, matchRow_prefix Ms _ hi.le] at h1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    length_matchingRowWords] at h1
  exact ⟨h0, by rw [Nat.add_assoc]; omega, h2, h3⟩

/-- The next row starts just after the current matching's last edge. -/
theorem matchingRow_first_succ {Ms : List (List (ℕ × ℕ))} {i : ℕ} (hi : i < Ms.length) :
    flatIndex Ms (i + 1) 0 = flatIndex Ms i 0 + (Ms.getD i []).length := by
  unfold flatIndex
  rw [List.take_succ_eq_append_getElem hi, List.getD_eq_getElem _ _ hi]
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Earlier matching rows occupy disjoint intervals of the flattened matching. -/
theorem matchingRow_first_mono (Ms : List (List (ℕ × ℕ))) : Monotone (fun i => flatIndex Ms i 0) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < Ms.length
  · rw [matchingRow_first_succ hi]
    exact Nat.le_add_right _ _
  · simp [flatIndex, List.take_of_length_le (show Ms.length ≤ i by omega),
      List.take_of_length_le (show Ms.length ≤ i + 1 by omega)]

/-- The last edge of a row lies before the end of the flattened matching. -/
theorem matchingRow_end_le {Ms : List (List (ℕ × ℕ))} {i : ℕ} (hi : i < Ms.length) :
    flatIndex Ms i 0 + (Ms.getD i []).length ≤ Ms.flatten.length := by
  rw [← matchingRow_first_succ hi, ← flatIndex_last]
  exact matchingRow_first_mono Ms (by omega)

/-- An edge's source in the matching row is stored before its target. -/
theorem matchingRow_source {mem : ℕ → ℕ} {a i j : ℕ} {Ms : List (List (ℕ × ℕ))}
    (hAt : ListAt mem a (matchingRowWords Ms i)) (hj : j < (Ms.getD i []).length) :
    mem (a + 2 * j) = (edgeAt (Ms.getD i []) j).1 := by
  unfold matchingRowWords at hAt
  generalize Ms.getD i [] = row at hAt hj ⊢
  change ListAt mem a (row.flatMap fun e => [e.1, e.2]) at hAt
  induction row generalizing a j with
  | nil => simp at hj
  | cons e row ih =>
    change ListAt mem a ([e.1, e.2] ++ row.flatMap fun e => [e.1, e.2]) at hAt
    obtain ⟨h0, h1⟩ := listAt_append.mp hAt
    cases j with
    | zero => exact h0 0 (by simp)
    | succ j =>
      have ht := ih (by simpa using hj) h1
      have hh : a + 2 * (j + 1) = a + 2 + 2 * j := by omega
      simpa only [hh, edgeAt, List.getD_cons_succ, List.length_cons, List.length_nil] using ht

/-- The raw walk in the row joins the endpoints in that row. -/
theorem matchingWalkRow_correct {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {Δ L b z i j : ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : RouteMatchedSpec G X pairs Δ L b z Ms emb) (hX : X ⊆ Finset.range G.n)
    (hPairs : ValidTerminalPairs X pairs) (hi : i < Ms.length) (hj : j < (Ms.getD i []).length) :
    let R := matchingWalkRow Ms emb i
    R.u j < G.n ∧ IsEdgeWalk G.edges (R.u j) (R.v j) (R.raw j) := by
  obtain ⟨hj', hIndex⟩ := getD_flatten_flatIndex Ms (0, 0) hi hj
  have hx : i < pairs.length := by rwa [← h.1]
  let e := edgeAt (Ms.getD i []) j
  have he : e ∈ Ms.getD i [] := by
    dsimp [e, edgeAt]
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨ha, hb⟩ := (h.2.1 i hx).1 e he
  obtain ⟨hl, hr, _⟩ := hPairs.1 (pairs[i]'hx) (List.getElem_mem hx)
  have hEnds : edgeAt Ms.flatten (flatIndex Ms i j) = e := hIndex
  have hin : insideB X (edgeAt Ms.flatten (flatIndex Ms i j)) = true := by
    rw [hEnds]
    simp [insideB, hl ha, hr hb]
  have hRaw := (h.2.2.2.1 _ hj' hin).1
  rw [hEnds] at hRaw
  refine ⟨Finset.mem_range.mp (hX (hl ha)), ?_⟩
  exact hRaw

end MinCostFlow.HierPaths
