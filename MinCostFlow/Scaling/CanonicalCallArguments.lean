module

public import MinCostFlow.Scaling.CanonicalRelocation
import Mathlib.Data.List.Range

/-!
# Arguments of a relocated circulation solver

A canonical circulation solve uses arguments `[0,inputLength]` in the guest.
Relocation adds the host base and guest word bound after the registers used
by the guest. This file gives the finite argument list that initializes
exactly the state used by `canonical_relocated_run`, including programs
whose register bound is one.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Guest arguments padded or truncated to the program's register bound,
followed by the two relocation parameters. -/
def canonicalCallArgs (Q : Program) (J : Circulation) (guestWidth h : ℕ) : List ℕ :=
  ((List.range Q.regBound).map fun r => [0, J.solverWords.length].getD r 0) ++
    [h + 1, 2 ^ guestWidth]

/-- The call has one argument for each guest register and two relocation words. -/
theorem canonicalCallArgs_length (Q : Program) (J : Circulation) (guestWidth h : ℕ) :
    (canonicalCallArgs Q J guestWidth h).length = Q.regBound + 2 := by
  simp only [canonicalCallArgs, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil]

/-- Reading the finite argument list gives exactly the canonical host registers. -/
theorem canonicalCallArgs_getD (Q : Program) (J : Circulation) (guestWidth h r : ℕ) :
    (canonicalCallArgs Q J guestWidth h).getD r 0 =
      if r = Q.regBound then h + 1 else if r = Q.regBound + 1 then 2 ^ guestWidth
      else [0, J.solverWords.length].getD r 0 := by
  have hR := Link.one_le_regBound Q
  unfold canonicalCallArgs
  by_cases hr : r < Q.regBound
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hr)]
    simp only [List.getElem?_map, List.getElem?_range hr, Option.map_some,
      Option.getD_some, ite_eq_right (by omega : r ≠ Q.regBound),
      ite_eq_right (by omega : r ≠ Q.regBound + 1)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using Nat.le_of_not_gt hr)]
    simp only [List.length_map, List.length_range]
    by_cases he : r = Q.regBound
    · subst r
      simp
    · by_cases he' : r = Q.regBound + 1
      · subst r
        simp
      · have hsub : 2 ≤ r - Q.regBound := by omega
        have hout : [h + 1, 2 ^ guestWidth][r - Q.regBound]? = none :=
          List.getElem?_eq_none (by simpa using hsub)
        have hpair : [0, J.solverWords.length].getD r 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          rfl
        simp only [hout, Option.getD_none, he, he', ↓reduceIte, hpair]

/-- Passing these arguments through an ordinary machine call initializes
exactly the state in the relocation theorem. -/
theorem startState_canonicalCallArgs (Q : Program) (J : Circulation)
    (guestWidth h pos : ℕ) (mem : ℕ → ℕ) :
    startState (canonicalCallArgs Q J guestWidth h) mem pos =
      canonicalHostState Q J guestWidth h pos mem := by
  unfold startState canonicalHostState
  congr 1
  funext r
  exact canonicalCallArgs_getD Q J guestWidth h r

/-- All call arguments fit when the canonical guest input fits and the
fresh guest region ends strictly inside host memory. -/
theorem canonicalCallArgs_words {Q : Program} {J : Circulation}
    {guestWidth hostWidth h : ℕ} {T : ℕ → ℕ → ℕ}
    (hin : CanonicalInput guestWidth T J) (hw : guestWidth ≤ hostWidth)
    (hspace : h + 1 + 2 ^ guestWidth < 2 ^ hostWidth) :
    ∀ a ∈ canonicalCallArgs Q J guestWidth h, a < 2 ^ hostWidth := by
  intro a ha
  have hpositive : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    have hlen : J.solverWords.length < 2 ^ hostWidth :=
      lt_of_lt_of_le (hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
        (Nat.pow_le_pow_right (by decide) hw)
    rcases r with _ | r
    · simp only [List.getD_cons_zero]; omega
    · rcases r with _ | r
      · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hlen
      · simp only [List.getD_cons_succ, List.getD_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
