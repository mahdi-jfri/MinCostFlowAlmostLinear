module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

/-!
# Assigning consecutive labels to encountered vertices

The instance-size bounds for Appendix C of Chen et al., arXiv:2203.00671v2,
can discard isolated vertices of a circulation. Scan the two endpoints of
each edge and give a new label only on the first encounter. Zero means that
a vertex has not been encountered. Each encounter performs one table lookup
and, only for a new vertex, one increment and one table update. There is no
search through the already assigned labels.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- A table of assigned positive labels and the number of labels in use. -/
structure VertexLabels (n : ℕ) where
  count : ℕ
  table : Fin n → ℕ

namespace VertexLabels

/-- Initially no vertex has a positive label. -/
def empty (n : ℕ) : VertexLabels n := ⟨0, fun _ => 0⟩

/-- Encounter one endpoint, assigning the next positive label if needed. -/
def encounter {n : ℕ} (s : VertexLabels n) (v : Fin n) : VertexLabels n :=
  if s.table v = 0 then
    ⟨s.count + 1, Function.update s.table v (s.count + 1)⟩
  else s

/-- Scan a list of endpoints in order. -/
def scan {n : ℕ} : VertexLabels n → List (Fin n) → VertexLabels n
  | s, [] => s
  | s, v :: vs => scan (s.encounter v) vs

/-- The table invariants: labels are in range and positive labels are unique. -/
def Valid {n : ℕ} (s : VertexLabels n) : Prop :=
  (∀ v, s.table v ≤ s.count) ∧
    ∀ v w, s.table v ≠ 0 → s.table v = s.table w → v = w

/-- The initial table satisfies all invariants. -/
theorem empty_valid (n : ℕ) : (empty n).Valid := by
  constructor
  · intro v
    exact le_rfl
  · intro v w h
    exact False.elim (h rfl)

/-- Each encounter adds at most one label. -/
theorem encounter_count_le {n : ℕ} (s : VertexLabels n) (v : Fin n) :
    (s.encounter v).count ≤ s.count + 1 := by
  unfold encounter
  split
  · exact le_rfl
  · exact Nat.le_succ _

/-- Encountering a vertex gives it a positive label. -/
theorem encounter_self_pos {n : ℕ} (s : VertexLabels n) (v : Fin n) :
    0 < (s.encounter v).table v := by
  unfold encounter
  split
  · simp only [Function.update_self]
    exact Nat.zero_lt_succ _
  · exact Nat.pos_of_ne_zero ‹_›

/-- An already positive label is never changed by an encounter. -/
theorem encounter_preserves {n : ℕ} (s : VertexLabels n) (v w : Fin n)
    (hw : s.table w ≠ 0) : (s.encounter v).table w = s.table w := by
  by_cases h : s.table v = 0
  · have hne : w ≠ v := by intro he; exact hw (he ▸ h)
    simp only [encounter, h, ↓reduceIte, Function.update_of_ne hne]
  · simp only [encounter, h, ↓reduceIte]

/-- Fresh labels preserve the table's range and uniqueness invariants. -/
theorem encounter_valid {n : ℕ} (s : VertexLabels n) (hs : s.Valid) (v : Fin n) :
    (s.encounter v).Valid := by
  by_cases h : s.table v = 0
  · simp only [encounter, h, ↓reduceIte]
    dsimp only [Valid]
    constructor
    · intro w
      by_cases hw : w = v
      · subst w
        simp only [Function.update_self, le_refl]
      · rw [Function.update_of_ne hw]
        exact le_trans (hs.1 w) (Nat.le_succ _)
    · intro a b ha hab
      by_cases hav : a = v
      · subst a
        rw [Function.update_self] at hab
        by_cases hb : b = v
        · exact hb.symm
        · rw [Function.update_of_ne hb] at hab
          have := hs.1 b
          omega
      · rw [Function.update_of_ne hav] at ha hab
        by_cases hb : b = v
        · subst b
          rw [Function.update_self] at hab
          have := hs.1 a
          omega
        · rw [Function.update_of_ne hb] at hab
          exact hs.2 a b ha hab
  · simpa only [encounter, h, ↓reduceIte] using hs

/-- Scanning endpoints preserves the table invariants. -/
theorem scan_valid {n : ℕ} (s : VertexLabels n) (hs : s.Valid) (vs : List (Fin n)) :
    (s.scan vs).Valid := by
  induction vs generalizing s with
  | nil => exact hs
  | cons v vs ih => exact ih (s.encounter v) (s.encounter_valid hs v)

/-- The number of labels is bounded by the initial number plus endpoints scanned. -/
theorem scan_count_le {n : ℕ} (s : VertexLabels n) (vs : List (Fin n)) :
    (s.scan vs).count ≤ s.count + vs.length := by
  induction vs generalizing s with
  | nil => exact le_rfl
  | cons v vs ih =>
    have ht := ih (s.encounter v)
    have he := s.encounter_count_le v
    simp only [scan, List.length_cons]
    omega

/-- Every old positive label stays unchanged throughout a scan. -/
theorem scan_preserves {n : ℕ} (s : VertexLabels n) (vs : List (Fin n))
    (v : Fin n) (hv : s.table v ≠ 0) : (s.scan vs).table v = s.table v := by
  induction vs generalizing s with
  | nil => rfl
  | cons w vs ih =>
    have he := s.encounter_preserves w v hv
    have hp : (s.encounter w).table v ≠ 0 := he ▸ hv
    exact (ih (s.encounter w) hp).trans he

/-- Every scanned endpoint has a positive label at the end. -/
theorem scan_mem_pos {n : ℕ} (s : VertexLabels n) (vs : List (Fin n))
    (v : Fin n) (hv : v ∈ vs) : 0 < (s.scan vs).table v := by
  induction vs generalizing s with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons w vs ih =>
    rcases List.mem_cons.mp hv with he | he
    · subst v
      have hp := s.encounter_self_pos w
      rw [scan, scan_preserves _ _ _ (Nat.ne_of_gt hp)]
      exact hp
    · exact ih (s.encounter w) he

/-- The endpoint scan with a counter for table operations and loop control.
A new label uses a lookup, test, increment, update, and loop step. An old label
uses only the lookup, test, and loop step. -/
def scanWithWork {n : ℕ} : VertexLabels n → List (Fin n) → VertexLabels n × ℕ
  | s, [] => (s, 0)
  | s, v :: vs =>
      let r := scanWithWork (s.encounter v) vs
      (r.1, (if s.table v = 0 then 5 else 3) + r.2)

/-- Instrumenting the scan leaves its returned labels unchanged. -/
theorem scanWithWork_value {n : ℕ} (s : VertexLabels n) (vs : List (Fin n)) :
    (s.scanWithWork vs).1 = s.scan vs := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact ih (s.encounter v)

/-- At most five table/control operations are charged per endpoint. -/
theorem scanWithWork_bound {n : ℕ} (s : VertexLabels n) (vs : List (Fin n)) :
    (s.scanWithWork vs).2 ≤ 5 * vs.length := by
  induction vs generalizing s with
  | nil => exact le_rfl
  | cons v vs ih =>
    have h := ih (s.encounter v)
    change (if s.table v = 0 then 5 else 3) +
      (scanWithWork (s.encounter v) vs).2 ≤ 5 * (vs.length + 1)
    split <;> omega

end VertexLabels
end MinCostFlow.Scaling
