module

public import MinCostFlow.Narrow.OuterDefs
import MinCostFlow.Narrow.Stage1Model
import Mathlib.Tactic.Ring

/-!
# Compressed circulation solver using Stage 1 and Stage 2 (Item 1)

This file proves the correctness, bounded-solver input bounds, and explicit
round/phase/call-count bounds for `narrowCircModel`, which removes isolated
vertices (`Circulation.compress`), handles the zero-edge case, and runs
Stage 1 (`narrowCostSolve`).
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- Every bounded-solver call produced by `narrowCircModel solve J` satisfies
the compressed-solver geometry, `m ^ 40` capacity, and `m ^ 10` cost bounds. -/
theorem narrowCircModel_calls_bounds (solve : (K : Circulation) → Fin K.m → ℤ)
    (J : Circulation) :
    ∀ K ∈ (narrowCircModel solve J).calls,
      K.n ≤ 2 * K.m + 1 ∧
      K.n ≤ 2 * J.m + 2 ∧
      K.m ≤ 12 * J.m ∧
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) ∧
      K.CostsBounded (K.m ^ 10) := by
  unfold narrowCircModel
  split
  · simp
  · rename_i hm0
    have hm : 0 < J.compress.m := Nat.pos_of_ne_zero hm0
    have hn : J.compress.n ≤ 2 * J.compress.m := J.endpointLabels_count_le
    intro K hK
    have hb := narrowCostSolverCalls_bounds solve J.compress hm hn K hK
    have hKn : K.n ≤ J.compress.n + 2 := hb.1
    have hKm : K.m ≤ 8 * J.m + 2 * J.compress.n := hb.2.2.1
    have hcn : J.compress.n ≤ 2 * J.m := hn
    exact ⟨hb.2.1, by omega, by omega, hb.2.2.2.1, hb.2.2.2.2.2⟩

/-- `narrowCircModel` returns an exact integral optimum of `J` whenever `solve`
is optimal on every recorded call in `(narrowCircModel solve J).calls`. -/
theorem narrowCircModel_optimal_of_calls (solve : (K : Circulation) → Fin K.m → ℤ)
    (J : Circulation)
    (hsolve : ∀ K ∈ (narrowCircModel solve J).calls, K.Optimal (fun a => (solve K a : ℝ))) :
    J.Optimal (fun e => ((narrowCircModel solve J).value e : ℝ)) := by
  unfold narrowCircModel at hsolve ⊢
  split at hsolve
  · rename_i hm0
    simp only [hm0, ↓reduceIte, Int.cast_zero]
    refine ⟨J.zero_feasible, fun g _ => ?_⟩
    have hg0 : g = fun _ => 0 := by
      funext e
      exact False.elim (by have := e.isLt; omega)
    rw [hg0]
  · rename_i hm0
    simp only [hm0, ↓reduceIte]
    have hm : 0 < J.compress.m := Nat.pos_of_ne_zero hm0
    have hn : J.compress.n ≤ 2 * J.compress.m := J.endpointLabels_count_le
    exact (J.compress_optimal_iff _).mp
      (narrowCostSolve_optimal_of_calls solve J.compress hm hn hsolve)

/-- `narrowCircModel` returns an exact integral optimum of every circulation `J`
under the compressed bounded-solver hypothesis (`compressedSolverContract`). -/
theorem narrowCircModel_optimal (solve : (K : Circulation) → Fin K.m → ℤ)
    (hsolve : ∀ K : Circulation, K.n ≤ 2 * K.m + 1 → K.CostsBounded (K.m ^ 10) →
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) →
      K.Optimal (fun a => (solve K a : ℝ)))
    (J : Circulation) :
    J.Optimal (fun e => ((narrowCircModel solve J).value e : ℝ)) := by
  apply narrowCircModel_optimal_of_calls solve J
  intro K hK
  have hb := narrowCircModel_calls_bounds solve J K hK
  exact hsolve K hb.1 hb.2.2.2.2 hb.2.2.2.1

private lemma list_flatMap_length_le {α β : Type} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have : (l.length + 1) * B = B + l.length * B := by ring
    omega

/-- Under the compressed bounded-solver hypothesis, every Stage 1 round keeps
a feasible flow, so `narrowCircModel solve J` makes at most
`narrowCostRounds J.compress * (bitScalingPhases J.compress + 1)` solver calls. -/
theorem narrowCircModel_calls_length (solve : (K : Circulation) → Fin K.m → ℤ)
    (hsolve : ∀ K : Circulation, K.n ≤ 2 * K.m + 1 → K.CostsBounded (K.m ^ 10) →
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) →
      K.Optimal (fun a => (solve K a : ℝ)))
    (J : Circulation) :
    (narrowCircModel solve J).calls.length ≤
      narrowCostRounds J.compress * (bitScalingPhases J.compress + 1) := by
  unfold narrowCircModel
  split
  · simp
  · rename_i hm0
    have hm : 0 < J.compress.m := Nat.pos_of_ne_zero hm0
    have hn : J.compress.n ≤ 2 * J.compress.m := J.endpointLabels_count_le
    have hcalls : ∀ K ∈ narrowCostSolverCalls solve J.compress,
        K.Optimal (fun a => (solve K a : ℝ)) := by
      intro K hK
      have hb := narrowCostSolverCalls_bounds solve J.compress hm hn K hK
      exact hsolve K hb.2.1 hb.2.2.2.2.2 hb.2.2.2.1
    have hinv := narrowCostStateAt_invariant solve J.compress hm hn hcalls
    unfold narrowCostSolverCalls
    have hlen := list_flatMap_length_le (List.range (narrowCostRounds J.compress))
      (fun j => narrowRoundSolverCalls solve J.compress
        (narrowCostStateAt solve J.compress (costScaleBits J.compress) j))
      (bitScalingPhases J.compress + 1)
      (fun j hj => by
        have hjlt : j < narrowCostRounds J.compress := List.mem_range.mp hj
        have hfeas := (hinv j (Nat.le_of_lt hjlt)).1.2.1
        apply narrowRoundSolverCalls_length_le
        intro e
        have h1 : 0 ≤ (narrowCostStateAt solve J.compress (costScaleBits J.compress) j).flow e :=
          (Int.cast_nonneg_iff (R := ℝ)).mp (hfeas.2 e).1
        have h2 : (narrowCostStateAt solve J.compress (costScaleBits J.compress) j).flow e ≤
            (J.compress.capacity e : ℤ) := by
          apply (Int.cast_le (R := ℝ)).mp
          simpa only [Int.cast_natCast] using (hfeas.2 e).2
        exact ⟨h1, h2⟩)
    simpa only [List.length_range] using hlen

/-- `Nat.size x ≤ Nat.clog 2 (x + 1)` for every natural number `x`. -/
theorem size_le_clog_succ (x : ℕ) : Nat.size x ≤ Nat.clog 2 (x + 1) :=
  Nat.size_le.mpr (lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_pow_clog (by decide) (x + 1)))

/-- Explicit Stage 1 round-count bound in terms of `Nat.clog 2`. -/
theorem narrowCircModel_rounds_le (J : Circulation) (m C : ℕ)
    (hm : J.m ≤ 3 * m) (hc : J.CostsBounded (max C 1)) :
    narrowCostRounds J.compress ≤
      28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) := by
  unfold narrowCostRounds
  have hL : costScaleBits J.compress ≤ Nat.clog 2 (C + 2) := by
    unfold costScaleBits
    have hmax : circMaxCost J.compress ≤ max C 1 := by
      unfold circMaxCost
      apply Finset.sup_le
      intro e _
      exact hc e
    have h1 := Nat.size_le_size hmax
    have h2 := size_le_clog_succ (max C 1)
    have h3 : Nat.clog 2 (max C 1 + 1) ≤ Nat.clog 2 (C + 2) :=
      Nat.clog_mono_right 2 (by omega)
    exact le_trans (le_trans h1 h2) h3
  have hp : costPrecisionExp J.compress.m ≤ 24 + 8 * Nat.clog 2 (m + 1) := by
    unfold costPrecisionExp
    apply Nat.clog_le_of_le_pow
    have h2m : 2 * J.compress.m ≤ 8 * (m + 1) := by change 2 * J.m ≤ 8 * (m + 1); omega
    have hpow := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
    calc
      (2 * J.compress.m) ^ 8 ≤ (8 * (m + 1)) ^ 8 := Nat.pow_le_pow_left h2m 8
      _ ≤ (8 * 2 ^ Nat.clog 2 (m + 1)) ^ 8 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hpow) 8
      _ = 2 ^ (24 + 8 * Nat.clog 2 (m + 1)) := by
        rw [Nat.mul_pow, Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm 8]
  have hn : Nat.size (J.compress.n + 1) ≤ 3 + Nat.clog 2 (m + 1) := by
    have h1 := size_le_clog_succ (J.compress.n + 1)
    have hnle : J.compress.n + 1 + 1 ≤ 8 * (m + 1) := by
      have hcnt : J.compress.n ≤ 2 * J.m := J.endpointLabels_count_le
      omega
    have h2 : Nat.clog 2 (J.compress.n + 1 + 1) ≤ 3 + Nat.clog 2 (m + 1) := by
      apply Nat.clog_le_of_le_pow
      have hpow := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
      calc
        J.compress.n + 1 + 1 ≤ 8 * (m + 1) := hnle
        _ ≤ 8 * 2 ^ Nat.clog 2 (m + 1) := Nat.mul_le_mul_left 8 hpow
        _ = 2 ^ (3 + Nat.clog 2 (m + 1)) := by rw [Nat.pow_add]
    exact le_trans h1 h2
  omega

/-- Explicit Stage 2 phase-count bound in terms of `Nat.clog 2`. -/
theorem narrowCircModel_phases_le (J : Circulation) (B : ℕ)
    (hu : ∀ e, J.capacity e ≤ B) :
    bitScalingPhases J.compress + 1 ≤ Nat.clog 2 (B + 1) + 1 := by
  have hmax : circMaxCapacity J.compress ≤ B := by
    unfold circMaxCapacity
    apply Finset.sup_le
    intro e _
    exact hu e
  exact Nat.add_le_add_right (le_trans (Nat.size_le_size hmax) (size_le_clog_succ B)) 1

end MinCostFlow.Narrow
