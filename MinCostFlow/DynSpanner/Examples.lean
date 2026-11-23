module

public import MinCostFlow.DynSpanner.Complexity

import MinCostFlow.DynSpanner.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Examples and non-vacuity witnesses for `DynSpanner`

This file proves that all hypotheses of `SparsifySpec` and `theorem_8_2` are jointly satisfiable:
* `idSparsify` and `idSparsifyParams`: a concrete `SparsifySpec`-compliant static sparsifier
  (returning `(J, idEmb, |V(J)| + |E(J)|)` with `γ_c = 1`, `γ_ℓ = 1`, `K_s = mMax`, `K_t = 1`).
* `exGraph` and `exBatches`: a concrete valid multigraph and valid sequence of deletion and
  vertex-split batches.
* `ex_theorem_8_2`: a full instantiation of `theorem_8_2` on `(exGraph, idSparsify, exBatches)`,
  confirming non-vacuity of all invariants, recourse bounds, and runtime bounds.
-/

namespace MinCostFlow.DynSpanner

@[expose] public section

/-- Concrete identity static sparsifier: returns `J` itself with the identity embedding and
cost `|V(J)| + |E(J)|`. -/
def idSparsify (_H' J : MGraph) (_embJH : Embedding) : SparsifyOut :=
  { Jtilde := J, emb := idEmb, cost := J.n + J.m }

/-- Parameters under which `idSparsify` satisfies `SparsifySpec mMax`. -/
def idSparsifyParams (mMax : ℕ) : SparsifyParams :=
  { γ_c := 1
    γ_ℓ := 1
    K_s := (mMax : ℝ)
    p_s := 0
    K_t := 1
    p_t := 0
    hγ_c := le_rfl
    hγ_ℓ := le_rfl
    hK_s := Nat.cast_nonneg mMax
    hK_t := zero_le_one }

/-- `idSparsify` satisfies `SparsifySpec mMax (idSparsifyParams mMax)` for every `mMax : ℕ`,
showing that the static sparsifier contract of Theorem 8.1 is non-vacuous. -/
theorem idSparsify_spec (mMax : ℕ) :
    SparsifySpec mMax (idSparsifyParams mMax) idSparsify := by
  intro H' J embJH _ hVJ hJm hLen _
  dsimp only [idSparsify, idSparsifyParams]
  refine ⟨?_, idEmb_isEmbedding J, ?_, ?_, ?_, ?_⟩
  · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  · rw [comp_idEmb]
    by_cases hE : J.E.Nonempty
    · have h1 : (1 : ℝ) ≤ (embJH.length J : ℝ) := by exact_mod_cast hLen hE
      have hvc : 0 ≤ embJH.vcong J H' (fun _ => 1) := vcong_nonneg embJH J H'
      have hmd : 0 ≤ (J.maxDeg : ℝ) := Nat.cast_nonneg _
      have hsum_nn : 0 ≤ embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ) := add_nonneg hvc hmd
      calc embJH.vcong J H' (fun _ => 1)
          ≤ embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ) := le_add_of_nonneg_right hmd
        _ = 1 * 1 * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) := by ring
        _ ≤ 1 * (embJH.length J : ℝ) * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 zero_le_one) hsum_nn
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      have hvc0 : embJH.vcong J H' (fun _ => 1) = 0 := by
        have hAt : ∀ v, embJH.vcongAt J H' (fun _ => 1) v = 0 := fun v => by
          simp [Embedding.vcongAt, hE]
        dsimp only [Embedding.vcong]
        split_ifs with hV
        · have hle : H'.V.sup' hV (embJH.vcongAt J H' (fun _ => 1)) ≤ 0 :=
            Finset.sup'_le hV _ fun v _ => le_of_eq (hAt v)
          have hge : 0 ≤ H'.V.sup' hV (embJH.vcongAt J H' (fun _ => 1)) := by
            have h := Finset.le_sup' (embJH.vcongAt J H' (fun _ => 1)) hV.choose_spec
            rwa [hAt] at h
          linarith
        · rfl
      rw [hvc0]
      positivity
  · rw [comp_idEmb, one_mul]
  · by_cases hE : J.E.Nonempty
    · obtain ⟨e, he⟩ := hE
      have hn : 1 ≤ J.n := Finset.card_pos.mpr ⟨J.tail e, (hVJ e he).1⟩
      have hmn : (J.m : ℝ) ≤ (mMax : ℝ) * (J.n : ℝ) := by
        exact_mod_cast le_trans hJm (Nat.le_mul_of_pos_right mMax hn)
      simpa using hmn
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      have hm0 : J.m = 0 := by simp [MGraph.m, hE]
      simp only [hm0, Nat.cast_zero, pow_zero, mul_one]
      positivity
  · by_cases hE : J.E.Nonempty
    · have h1 : (1 : ℝ) ≤ (embJH.length J : ℝ) := by exact_mod_cast hLen hE
      have hm : (J.m : ℝ) ≤ (J.m : ℝ) * (embJH.length J : ℝ) :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) h1
      simp only [Nat.cast_add, one_pow, mul_one, one_mul, pow_zero]
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      have hm0 : J.m = 0 := by simp [MGraph.m, hE]
      simp [hm0]

/-- Concrete 3-vertex path graph `(0 —edge 0→ 1 —edge 1→ 2)`. -/
def exGraph : MGraph where
  V := {0, 1, 2}
  E := {0, 1}
  tail := fun e => if e = 0 then 0 else 1
  head := fun e => if e = 0 then 1 else 2

/-- `exGraph` is a valid multigraph. -/
theorem exGraph_valid : exGraph.IsValid := by
  intro e he
  simp only [exGraph, Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases he with rfl | rfl <;> simp

/-- Concrete sequence of valid update batches: delete edge `1`, then split vertex `1` into `1` and `3`
moving incident edge `0` to `3`. -/
def exBatches : List (List Update) :=
  [[.delete 1], [.split 1 3 {0} {0}]]

/-- `exBatches` is a valid deletion-and-split sequence on `exGraph` with `batchSplitCount = 1`. -/
theorem exBatches_valid :
    exGraph.BatchIsValid exBatches.flatten ∧
    (∀ u ∈ exBatches.flatten, isDelOrSplit u) ∧
    batchSplitCount exBatches.flatten ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, trivial⟩
    · simp [exGraph, MGraph.UpdateIsValid]
    · simp only [exGraph, MGraph.UpdateIsValid, MGraph.applyUpdate]
      refine ⟨by decide, by decide, ?_, ?_⟩
      · intro e he
        simp only [Finset.union_self, Finset.mem_singleton] at he
        subst he
        decide
      · intro e he
        simp only [Finset.union_self, Finset.mem_singleton] at he
        subst he
        right
        simp
  · intro u hu
    simp only [exBatches, List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact trivial
  · simp [exBatches, batchSplitCount, isSplit]

/-- Concrete non-vacuity instantiation of `theorem_8_2` on `(exGraph, idSparsify, exBatches)` with
`L = 1`, `splitBound = 1`: all hypotheses hold simultaneously and yield all stage invariants,
recourse bounds, Item 1–3 guarantees, and amortized update-time bounds. -/
theorem ex_theorem_8_2 :
    let L := 1
    let nMax := exGraph.n + 1
    let q := phaseBase nMax L
    let initOut := init exGraph L q idSparsify
    let st := fun t => runBatchState (L := L) exGraph q idSparsify exBatches t
    let res := fun t => runBatchStepOut (L := L) exGraph q idSparsify exBatches t
    let P := idSparsifyParams exGraph.m
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (exGraph.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (exGraph.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let nRoot : ℝ := ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
    let batchTotal := fun t => ((exBatches.take t).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t, match exBatches[t']? with
      | some U => ((st t').G.batchEnc U : ℝ)
      | none => 0
    ((initOut.state.H.m : ℝ) ≤ P.K_s * (exGraph.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((exGraph.n : ℝ) + (exGraph.m : ℝ) + 2)) ^ P.p_s) ∧
    (∀ t ≤ exBatches.length,
      (st t).G = exGraph.applyBatch (exBatches.flatten.take (batchPrefixLen exBatches t)) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s ∧
      Embedding.IsEmbedding (piTotal (st t)) (st t).G (st t).H ∧
      (Embedding.length (piTotal (st t)) (st t).G : ℝ) ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P.γ_ℓ ^ (L * (L + 1) / 2) * P.γ_c ^ (L + 1) *
          (exGraph.maxDeg : ℝ)) ∧
    (∀ t ≤ exBatches.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + 2 * (6 + 3 * degΛ) * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s *
          batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        90 * (L : ℝ) * nRoot * (P.K_t + P.K_s + 1) * E_L * ((exGraph.maxDeg : ℝ) + 1) * Λ *
          encTotal t)) := by
  have h := theorem_8_2 (G₀ := exGraph) (L := 1) (mMax := exGraph.m) (splitBound := 1)
    exGraph_valid le_rfl le_rfl (idSparsify_spec exGraph.m)
    exBatches_valid.1 exBatches_valid.2.1 exBatches_valid.2.2
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

end

end MinCostFlow.DynSpanner
