module

public import MinCostFlow.MinRatio.PathCancellation
import MinCostFlow.LSF.Walks
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Find

/-!
# Cancellation-free tree routes of bounded size

Algorithm 2 (page 29) needs the absolute change on each edge of the
circulation. Destinations can be swapped to cancel opposite traversals
while keeping the same number of paths, given by their endpoints.
A shortest equivalent route thus has no opposite traversals. This is an
existence and correctness statement for the route decomposition.
-/

public section

namespace MinCostFlow.MinRatio

private theorem forestPath_no_reverse {F : MGraph} (hF : F.IsForest) {a b : ℕ}
    (hab : F.Connected a b) {x : ℕ × Bool} (hx : x ∈ F.forestPath a b) :
    (x.1, !x.2) ∉ F.forestPath a b := by
  intro hrev
  have hnd := LSF.isPath_nodup_edges (LSF.forestPath_isPath hF hab)
  have heq := List.inj_on_of_nodup_map hnd hx hrev rfl
  have hb := congrArg Prod.snd heq
  cases hbit : x.2 <;> simp [hbit] at hb

/-- Tree paths can be rerouted to have no opposite traversals while
preserving the signed flow and the number of endpoint pairs. -/
theorem pathCancel_route {F : MGraph} (hF : F.IsForest) (paths : List (ℕ × ℕ))
    (hconn : ∀ p ∈ paths, F.Connected p.1 p.2) :
    ∃ Q : List (ℕ × ℕ), Q.length = paths.length ∧ (∀ p ∈ Q, F.Connected p.1 p.2) ∧
      (∀ e, (Q.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
        (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum) ∧
      ∀ (x : ℕ × Bool) p q, p ∈ Q → q ∈ Q → x ∈ F.forestPath p.1 p.2 →
        (x.1, !x.2) ∉ F.forestPath q.1 q.2 := by
  classical
  let steps := fun Q : List (ℕ × ℕ) => (Q.map (fun p => (F.forestPath p.1 p.2).length)).sum
  let flow := fun Q : List (ℕ × ℕ) => fun e : ℕ =>
    (Q.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum
  let admissible := fun Q : List (ℕ × ℕ) =>
    Q.length = paths.length ∧ (∀ p ∈ Q, F.Connected p.1 p.2) ∧ ∀ e, flow Q e = flow paths e
  have hex : ∃ n, ∃ Q, admissible Q ∧ steps Q = n :=
    ⟨steps paths, paths, ⟨rfl, hconn, fun _ => rfl⟩, rfl⟩
  obtain ⟨Q, ⟨hlen, hc, hflow⟩, hsteps⟩ := Nat.find_spec hex
  refine ⟨Q, hlen, hc, hflow, ?_⟩
  intro x p q hp hq hx hy
  have hne : q ≠ p := by
    intro he
    subst q
    exact forestPath_no_reverse hF (hc p hp) hx hy
  let rest := (Q.erase p).erase q
  have hpq : Q.Perm (p :: q :: rest) :=
    (List.perm_cons_erase hp).trans
      ((List.perm_cons_erase ((List.mem_erase_of_ne hne).mpr hq)).cons p)
  have hrest : ∀ y ∈ rest, F.Connected y.1 y.2 := fun y hy =>
    hc y ((hpq.mem_iff).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)))
  obtain ⟨h₁, h₂, hswap, hshort⟩ := pathCancel_swap hF (hc p hp) (hc q hq) hx hy
  let R := (p.1, q.2) :: (q.1, p.2) :: rest
  have hRlen : R.length = paths.length := by
    rw [← hlen, hpq.length_eq]
    rfl
  have hRc : ∀ y ∈ R, F.Connected y.1 y.2 := by
    intro y hy
    simp only [R, List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact h₁
    · exact h₂
    · exact hrest y hy
  have hRf : ∀ e, flow R e = flow paths e := by
    intro e
    rw [← hflow e]
    have hs := (hpq.map (fun t => walkFlow (F.forestPath t.1 t.2) e)).sum_eq
    unfold flow R
    rw [hs]
    simp only [List.map_cons, List.sum_cons, ← add_assoc, hswap e]
  have hRs : steps R < steps Q := by
    have hs := (hpq.map (fun t => (F.forestPath t.1 t.2).length)).sum_eq
    unfold steps R
    rw [hs]
    simp only [List.map_cons, List.sum_cons]
    omega
  have hmin := Nat.find_min' hex ⟨R, ⟨hRlen, hRc, hRf⟩, rfl⟩
  omega

end MinCostFlow.MinRatio
