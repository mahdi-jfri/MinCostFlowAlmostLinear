module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitDefs
import Mathlib.Tactic.Ring

/-!
# The cost of the sparsifier call against the model's `out.cost`

The model step charges `out.cost`, the cost of the run of the guest program of `Sparsify`
(Theorem 8.1, page 39) on the canonical input (`canonicalSparsify`). The program calls the guest
through `sparsifyDynStmt`, whose contract (`sparsifyDynContract`) charges the guest at its time
bound `cQ = ⌈K_t γ_t (1 + |V(J)| + |E(J)| γ_ℓ² length(Π_{J→H'})) log^{p_t}⌉`, times the
relocation factor `R + 6` (`R` is the register bound of the guest program, a constant of the
implementation), plus the translation to and from the cited graph format.

So the program's cost is not bounded by `out.cost` itself, which can be much smaller than its
bound, but both are bounded by the same `cQ`:
* `canonicalSparsify_cost_le`: `out.cost ≤ cQ` (the guest run meets the time bound of
  Theorem 8.1);
* `sparsifyDynCost_eq`: the program's cost is `(R + 6) · cQ + sparsifyTransCost`, where
  `sparsifyTransCost` is the cost of the translation and of the word-size computation;
* `sparsifyTransCost_le`: the translation costs at most
  `10000 · (|V(J)| + |E(J)| · (length(Π_{J→H'}) + 1) + |x| + w' + R + 1) · (log₂ ℓ + 1)` with
  `ℓ = |V(J)| + 2 |E(J)| length(Π_{J→H'}) + |E(J)| + 2`, `x` the canonical input and `w'` its word
  size, plus `250 · |E(J)| · ⌈γ_ℓ⌉` for the output walks.

Hence an amortized analysis of the program must bound the sparsifier by the time bound of
Theorem 8.1, as the model's `StepCostRecord` does (`rebuild_bounds`, `restart_bounds`), and not by
`out.cost`. The translation has a factor `log₂ ℓ`, which the bound of Theorem 8.2 absorbs only
when the polylogarithmic exponent of the sparsifier is positive.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner
open MinCostFlow.Spanner

public section

/-- The time bound of Theorem 8.1 for the guest, as the natural number `cQ` that
`sparsifyDynContract` charges. -/
noncomputable def sparsifyGuestBound (impl : SparsifyImpl) (mMax : ℕ) (J : MGraph)
    (emb : MinCostFlow.Embedding) : ℕ :=
  ⌈impl.K_t * (impl.γ_t mMax) *
      (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (emb.length J : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊

/-- The definition of `sparsifyGuestBound`, for use in other files. -/
theorem sparsifyGuestBound_def (impl : SparsifyImpl) (mMax : ℕ) (J : MGraph)
    (emb : MinCostFlow.Embedding) :
    sparsifyGuestBound impl mMax J emb =
      ⌈impl.K_t * (impl.γ_t mMax) *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (emb.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊ := by
  unfold sparsifyGuestBound; rfl

/-- The part of the cost of `sparsifyDynStmt` that is not the guest: the translation of the
graphs and walks to and from the cited format, and the word-size computation. -/
noncomputable def sparsifyTransCost (impl : SparsifyImpl) (mMax : ℕ) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) : ℕ :=
  let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
  let lArg := J.n + 2 * rawEsLen + J.m + 2
  let x := canonSparsifyInput H' J emb
  let R := impl.program.regBound
  1430 * (J.n + J.m + rawEsLen) * (Nat.log 2 lArg + 1) + 1250 * (J.n + J.m + rawEsLen) + 1500 +
    40 * (x.length + wordSize impl.cw x + 1) + R +
    250 * J.n * (Nat.log 2 (J.n + 1) + 1) + 250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
    430 * J.n + 1065 * J.m + 250 * (J.m * Nat.ceil (impl.γ_ℓ mMax)) + 1200

/-- The cost of `sparsifyDynStmt` is the guest's time bound times `R + 6`, plus the
translation. -/
theorem sparsifyDynCost_eq (impl : SparsifyImpl) (mMax : ℕ) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) :
    sparsifyDynCost impl mMax H' J emb =
      (impl.program.regBound + 6) * sparsifyGuestBound impl mMax J emb +
        sparsifyTransCost impl mMax H' J emb := by
  simp only [sparsifyDynCost, sparsifyDynContract, sparsifyGuestBound, sparsifyTransCost]
  ring

/-- The translation is nearly linear in the size of `J` with its walks, and in the canonical
input. -/
theorem sparsifyTransCost_le (impl : SparsifyImpl) (mMax : ℕ) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) :
    let x := canonSparsifyInput H' J emb
    sparsifyTransCost impl mMax H' J emb ≤
      10000 * (J.n + J.m * (emb.length J + 1) + x.length + wordSize impl.cw x +
          impl.program.regBound + 1) *
        (Nat.log 2 (J.n + 2 * (J.m * emb.length J) + J.m + 2) + 1) +
      250 * (J.m * Nat.ceil (impl.γ_ℓ mMax)) := by
  intro x
  have hraw := collectRawEsFun_length_le (J := J) (emb := emb)
  set raw := (collectRawEsFun (vertsOf J.E) emb).length
  set Λ := Nat.log 2 (J.n + 2 * (J.m * emb.length J) + J.m + 2) + 1
  set N := J.n + J.m * (emb.length J + 1) + x.length + wordSize impl.cw x +
    impl.program.regBound + 1
  have hlog1 : Nat.log 2 (J.n + 2 * raw + J.m + 2) + 1 ≤ Λ :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have hlog2 : Nat.log 2 (J.n + 1) + 1 ≤ Λ :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have hlog3 : Nat.log 2 (J.m + 1) + 1 ≤ Λ :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have hΛ1 : 1 ≤ Λ := Nat.le_add_left _ _
  have hmul : J.m * (emb.length J + 1) = J.m * emb.length J + J.m := by ring
  have hX : J.n + J.m + raw ≤ N := by omega
  have hn : J.n ≤ N := by omega
  have hm : J.m ≤ N := by omega
  have hx : x.length + wordSize impl.cw x + 1 ≤ N := by omega
  have hR : impl.program.regBound ≤ N := by omega
  have h1 : (J.n + J.m + raw) * (Nat.log 2 (J.n + 2 * raw + J.m + 2) + 1) ≤ N * Λ :=
    Nat.mul_le_mul hX hlog1
  have h2 : J.n * (Nat.log 2 (J.n + 1) + 1) ≤ N * Λ := Nat.mul_le_mul hn hlog2
  have h3 : J.m * (Nat.log 2 (J.m + 1) + 1) ≤ N * Λ := Nat.mul_le_mul hm hlog3
  have h4 : N ≤ N * Λ := Nat.le_mul_of_pos_right N hΛ1
  have h5 : 1 ≤ N := by omega
  simp only [sparsifyTransCost]
  rw [Nat.mul_assoc 1430, Nat.mul_assoc 250 J.n, Nat.mul_assoc 250 J.m, Nat.mul_assoc 10000]
  simp only [raw, x, N, Λ] at h1 h2 h3 h4 h5 hx hR hn hm ⊢
  omega

/-- The model's sparsifier cost is at most the time bound of Theorem 8.1. -/
theorem canonicalSparsify_cost_le (impl : SparsifyImpl) (mMax : ℕ)
    {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ emb.length J) (hemb : emb.IsEmbedding J H') :
    (canonicalSparsify impl H' J emb).cost ≤ sparsifyGuestBound impl mMax J emb := by
  by_cases hJn : 1 ≤ J.n
  · have hV : CanonicalSparsifyValid impl H' J emb := ⟨hJn, hH', hJ, hLen, hemb⟩
    obtain ⟨body, o, st', cost, cJtilde, kept, embJJtilde,
      hp, hr, _, _, _, _, hOut, hCost_le⟩ :=
      canonicalGuestRun_exists impl mMax hH' hJ hJm hLen hemb
    rw [canonicalSparsify_eq_of_run hV hp hr hOut]
    exact hCost_le
  · have hnV : ¬ CanonicalSparsifyValid impl H' J emb := fun h => hJn h.1
    simp only [canonicalSparsify, dif_neg hnV]
    exact Nat.zero_le _

end

end MinCostFlow.DynSpanner.Program
