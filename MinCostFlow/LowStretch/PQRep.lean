module

public import MinCostFlow.LowStretch.ProgTT

/-!
# The class queues in memory

A run of Dijkstra keeps its queue as `J` lists, one per weight class. Each list is sorted by key,
because all arcs of a class have the same cost and the keys of the settled vertices only grow.
This file fixes how the lists sit in memory, starting at a base `D`:
* `D`, `D + 1`, `D + 2` hold `J`, the capacity `A` of a list, and the bound `INF` on keys;
* the tournament tree over the classes is at `D + 3` (cells `D + 4, …, D + 2 + 2J`);
* the first and last-plus-one positions of list `c` are at `D + 3 + 2J + c` and `D + 3 + 3J + c`;
* entry `i` of list `c` has its key at `D + 3 + 4J + 2(cA + i)` and its vertex one cell later.
Leaf `c` of the tree holds `key · J + c` for the first key of list `c`, or `INF · J + c` if the
list is empty. So the root decides the class of a least entry (`PQRep.root_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The value of leaf `c` for list `l`. -/
def leafv (INF J c : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => INF * J + c
  | e :: _ => e.1 * J + c

/-- Address of the first position of list `c`. -/
def pqH (D J c : ℕ) : ℕ := D + 3 + 2 * J + c

/-- Address of the last-plus-one position of list `c`. -/
def pqT (D J c : ℕ) : ℕ := D + 3 + 3 * J + c

/-- Address of the key of entry `i` of list `c`. -/
def pqE (D J A c i : ℕ) : ℕ := D + 3 + 4 * J + 2 * (c * A + i)

/-- The size of the whole layout. -/
def pqSize (J A : ℕ) : ℕ := 3 + 4 * J + 2 * J * A

/-- The entries of list `c` as they sit in memory. -/
def pqList (mem : ℕ → ℕ) (D J A c : ℕ) : List (ℕ × ℕ) :=
  (List.range (mem (pqT D J c) - mem (pqH D J c))).map fun i =>
    (mem (pqE D J A c (mem (pqH D J c) + i)), mem (pqE D J A c (mem (pqH D J c) + i) + 1))

/-- The memory at `D` holds the lists `qs`. -/
structure PQRep (mem : ℕ → ℕ) (D J A INF : ℕ) (qs : ℕ → List (ℕ × ℕ)) : Prop where
  hJ : mem D = J
  hA : mem (D + 1) = A
  hINF : mem (D + 2) = INF
  J_pos : 1 ≤ J
  bounds : ∀ c < J, mem (pqH D J c) ≤ mem (pqT D J c) ∧ mem (pqT D J c) ≤ A
  list : ∀ c < J, qs c = pqList mem D J A c
  none : ∀ c, J ≤ c → qs c = []
  sorted : ∀ c, (qs c).Pairwise (fun a b => a.1 ≤ b.1)
  lt : ∀ c, ∀ e ∈ qs c, e.1 < INF
  tt : TTOk mem (D + 3) J
  leaf : ∀ c < J, mem (D + 3 + J + c) = leafv INF J c (qs c)

/-- All entries. -/
def pqAll (J : ℕ) (qs : ℕ → List (ℕ × ℕ)) : List (ℕ × ℕ) := (List.range J).flatMap qs

theorem mem_pqAll {J : ℕ} {qs : ℕ → List (ℕ × ℕ)} {e : ℕ × ℕ} :
    e ∈ pqAll J qs ↔ ∃ c < J, e ∈ qs c := by
  simp [pqAll]

theorem pack_div {k J c : ℕ} (hc : c < J) : (k * J + c) / J = k :=
  Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

theorem pack_mod {k J c : ℕ} (hc : c < J) : (k * J + c) % J = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem leafv_div {INF J c : ℕ} (hc : c < J) (l : List (ℕ × ℕ)) :
    leafv INF J c l / J = (match l with | [] => INF | e :: _ => e.1) ∧ leafv INF J c l % J = c := by
  cases l with
  | nil => exact ⟨pack_div hc, pack_mod hc⟩
  | cons e l => exact ⟨pack_div hc, pack_mod hc⟩

/-- **What the root says.** If the root key is below `INF`, the root's class has a first entry
whose key is at most every key; otherwise every list is empty. -/
theorem PQRep.root_spec {mem : ℕ → ℕ} {D J A INF : ℕ} {qs : ℕ → List (ℕ × ℕ)}
    (h : PQRep mem D J A INF qs) :
    (mem (D + 3 + 1) / J < INF →
      ∃ e rest, qs (mem (D + 3 + 1) % J) = e :: rest ∧ e.1 = mem (D + 3 + 1) / J ∧
        mem (D + 3 + 1) % J < J ∧ ∀ e' ∈ pqAll J qs, e.1 ≤ e'.1) ∧
    (INF ≤ mem (D + 3 + 1) / J → ∀ c, qs c = []) := by
  have hJ := h.J_pos
  obtain ⟨c0, hc0, hroot⟩ := h.tt.root_mem hJ
  rw [h.leaf c0 hc0] at hroot
  have hd := leafv_div (INF := INF) hc0 (qs c0)
  rw [← hroot] at hd
  -- every class has a first key at least the root key
  have hle : ∀ c < J, ∀ e ∈ qs c, mem (D + 3 + 1) / J ≤ e.1 := by
    intro c hc e he
    have hr := h.tt.root_le hc
    rw [h.leaf c hc] at hr
    cases hq : qs c with
    | nil => rw [hq] at he; simp at he
    | cons f rest =>
      rw [hq] at hr he
      simp only [leafv] at hr
      have h1 : mem (D + 3 + 1) / J ≤ (f.1 * J + c) / J := Nat.div_le_div_right hr
      rw [pack_div hc] at h1
      have hs := h.sorted c
      rw [hq] at hs
      rcases List.mem_cons.mp he with rfl | he'
      · exact h1
      · exact h1.trans (List.rel_of_pairwise_cons hs he')
  constructor
  · intro hlt
    cases hq : qs c0 with
    | nil =>
      rw [hq] at hd
      simp only at hd
      omega
    | cons e rest =>
      rw [hq] at hd
      simp only at hd
      refine ⟨e, rest, by rw [hd.2, hq], hd.1.symm, by rw [hd.2]; exact hc0, fun e' he' => ?_⟩
      obtain ⟨c, hc, he'⟩ := mem_pqAll.mp he'
      rw [← hd.1]
      exact hle c hc e' he'
  · intro hge c
    by_cases hc : c < J
    · cases hq : qs c with
      | nil => rfl
      | cons e rest =>
        have := hle c hc e (by rw [hq]; exact List.mem_cons_self)
        have := h.lt c e (by rw [hq]; exact List.mem_cons_self)
        omega
    · exact h.none c (by omega)

end MinCostFlow.LowStretch
