module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortBudget
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPot
public import MinCostFlow.DynSpanner.Program.DynSpannerInitCost
public import MinCostFlow.DynSpanner.Complexity

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The amortized cost of a restart

A step at level `j = 0` (a restart, Algorithm 6) rebuilds level `0` on the whole graph `G'`: the
program runs `dsInitCoreStmt` on `G'` and clears the old spanner `H`. Its cost bound
`dsStepZeroCost` is the cost of the initialization on `G'` (`dsInitCoreCost`), plus
`675 |E(H_old)|` for clearing `H`, plus terms linear in `|E(H_0)|`, `n` and `L`.

We compare it with the budget of a restart in the sum of Lemma 5.9
(`lemma_5_9_sum_of_step_bounds`):
* the initialization is at most `F` times the initialization bound of Theorem 8.2 on `G'`
  (`dsInitCore_initCostBound`, `F = dsInitCostFactor impl`);
* clearing the old spanner is paid by the potential `Φ = Σ_i |E(H_i)|` (`levelPot`): `|E(H_old)| ≤ Φ`
  before the step (`card_H_le_levelPot`), and `Φ = |E(H_0)|` after it (`levelPot_step_zero`);
* the rest is the arithmetic of `restart_extra_of_le`, with `n ≤ N₁`, `m ≤ N₁ Δ₀` and the sizes of
  the spanners from Lemma 5.9.

The polylogarithmic factor of the initialization is `log^{max p_t 1}`, which is at most `Λ` when
`1 ≤ max p_s p_t`. This is the hypothesis `hp` (the sparsifier we use has `p_s = 1`).

The main result is `stepZero_budget`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- Every update has encoding size at least `1`. -/
lemma one_le_updateEnc (G : MGraph) (u : Update) : 1 ≤ G.updateEnc u := by
  cases u <;> simp [MGraph.updateEnc]

/-- The log factor `(1 + log a)^p` grows with `a` and with `p`. -/
lemma logPow_mono {a b : ℝ} {p p' : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hp : p ≤ p') :
    (1 + Real.log a) ^ p ≤ (1 + Real.log b) ^ p' := by
  have h0 : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  calc (1 + Real.log a) ^ p ≤ (1 + Real.log b) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
    _ ≤ (1 + Real.log b) ^ p' := pow_le_pow_right₀ (by linarith) hp

/-- **The amortized cost of a restart** (a step with `j = 0`). The cost bound of the program for
the step, with the per-step overhead of the batch loop (`35 L + 420 + 90 |D| + 240 |U_H| + 160`),
is at most `C = dsInitCostFactor impl + 3000` times the budget of a restart in the sum of
Lemma 5.9, plus `1440` times the drop of the potential `levelPot`. -/
theorem stepZero_budget {G₀ : MGraph} (impl : SparsifyImpl) {mMax L q vCap eCap nMax : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj0 : chooseLevel L q (k + 1) = 0)
    (hn : ∀ k' ≤ k + 1, (G₀.applyBatch (us.take k')).n ≤ nMax)
    (hp : 1 ≤ max impl.p_s impl.p_t) :
    let P := (canonicalSparsifyParams impl mMax).absorbTime
    let res := runStepOut (L := L) G₀ q (canonicalSparsify impl) us k
    ((dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 + 35 * L + 520 + 90 * res.D.card +
        90 * (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k).card +
        240 * res.UH.length + 240 : ℕ) : ℝ) ≤
      ((dsInitCostFactor impl : ℝ) + 3000) *
        (((L : ℝ) + 1) * ((G₀.applyBatch (us.take k)).updateEnc (us[k]'hk) : ℝ) +
          (res.UH.length : ℝ) + (res.D.card : ℝ) +
          ((max nMax 1 : ℕ) : ℝ) * (12 * ((L : ℝ) * (q : ℝ)) * (P.K_t + P.K_s + 1) *
            (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
              P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
            (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t))) +
      1440 * ((levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us k) : ℝ) -
        (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) : ℝ)) := by
  intro P res
  set sp := canonicalSparsify impl
  set u := us[k]'hk with hu_def
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  have hq1 : 1 ≤ q := by omega
  have hSpec : SparsifySpec mMax P sp := canonicalSparsify_spec_absorb impl mMax
  obtain ⟨hInvk, -⟩ := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds k hk.le
  obtain ⟨-, hRecs⟩ := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) hk
  have hRec := hRecs k (Nat.lt_succ_self k) u hu
  set st := runState (L := L) G₀ q sp us k with hst
  have hres : res = step st u sp := by simp [res, runStepOut, hu, st, sp]
  have hst1 : runState (L := L) G₀ q sp us (k + 1) = (step st u sp).state := by
    simp [runState, hu, st, sp]
  -- The graph after the update.
  set G' := st.G.applyUpdate u with hG'
  have hG'eq : G' = G₀.applyBatch (us.take (k + 1)) := by
    rw [hG', hInvk.G_eq, take_succ_of_getElem? hu, applyBatch_append]
    rfl
  obtain ⟨hBVk1, hdsk1, -⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
  obtain ⟨hVG'0, hEsub, -⟩ := batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀ hBVk1 hdsk1
  have hVG' : G'.IsValid := hG'eq ▸ hVG'0
  have hG'm0 : G'.m ≤ G₀.m := hG'eq ▸ Finset.card_le_card hEsub
  have hG'm : G'.m ≤ mMax := le_trans hG'm0 hGm₀
  have hG'n : G'.n ≤ nMax := hG'eq ▸ hn (k + 1) le_rfl
  have hG0n : G₀.n ≤ nMax := by simpa [MGraph.applyBatch] using hn 0 (Nat.zero_le _)
  -- The cost of the program.
  set H₀ := (initCore G' sp).1 with hH₀
  have hcost : dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 =
      dsStepZeroCost impl mMax L G' st.H H₀ 0 := by
    simp only [dsStepCostAt, hu, hj0, ↓reduceIte]
    rfl
  have hInitB := dsInitCore_initCostBound impl mMax L q hVG' hG'm
  dsimp only at hInitB
  have hinitH : (init G' L q sp).state.H.m = H₀.m := rfl
  rw [hinitH] at hInitB
  -- The potential.
  have hcl : chooseLevel L st.q (st.t + 1) = 0 := by rw [hInvk.q_eq, hInvk.t_eq]; exact hj0
  have hΦ1 : levelPot (runState (L := L) G₀ q sp us (k + 1)) = H₀.m := by
    rw [hst1]; exact levelPot_step_zero st u sp hcl
  have hΦ0 : st.H.m ≤ levelPot st := card_H_le_levelPot hInvk.H_E
  -- Sizes.
  set N₁ : ℝ := ((max nMax 1 : ℕ) : ℝ)
  set Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
  set Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
  set nact : ℕ := (activeSubgraph G').n
  set X := (1 + Real.log ((nact : ℝ) + (G'.m : ℝ) + 2)) ^ max P.p_t 1
  have h1N : (1 : ℝ) ≤ N₁ := by simp only [N₁]; exact_mod_cast le_max_right nMax 1
  have hnN : (nMax : ℝ) ≤ N₁ := by simp only [N₁]; exact_mod_cast le_max_left nMax 1
  have hnact_le : nact ≤ nMax := le_trans (activeSubgraph_n_le G') hG'n
  have hnact : (nact : ℝ) ≤ N₁ := le_trans (by exact_mod_cast hnact_le) hnN
  have hn' : (G'.n : ℝ) ≤ N₁ := le_trans (by exact_mod_cast hG'n) hnN
  have hm' : (G'.m : ℝ) ≤ N₁ * (G₀.maxDeg : ℝ) := by
    have h2 : (2 : ℝ) * (G₀.m : ℝ) ≤ (G₀.n : ℝ) * (G₀.maxDeg : ℝ) := by
      exact_mod_cast two_mul_m_le_n_mul_maxDeg hVG₀
    have h3 : (G₀.n : ℝ) ≤ N₁ := le_trans (by exact_mod_cast hG0n) hnN
    have h4 : (G'.m : ℝ) ≤ (G₀.m : ℝ) := by exact_mod_cast hG'm0
    nlinarith [Nat.cast_nonneg (α := ℝ) G₀.maxDeg, Nat.cast_nonneg (α := ℝ) G'.m]
  have harg1 : (1 : ℝ) ≤ (nact : ℝ) + (G'.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nact, Nat.cast_nonneg (α := ℝ) G'.m]
  have harg_le : (nact : ℝ) + (G'.m : ℝ) + 2 ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    have : (nact : ℝ) ≤ nMax := by exact_mod_cast hnact_le
    have : (G'.m : ℝ) ≤ G₀.m := by exact_mod_cast hG'm0
    linarith
  have hX0 : 0 ≤ X := pow_nonneg (by linarith [Real.log_nonneg harg1]) _
  have hpp : max P.p_t 1 ≤ max P.p_s P.p_t := max_le (le_max_right _ _) hp
  have hXΛ : X ≤ Λ := logPow_mono harg1 harg_le hpp
  have hbig1 : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hΛs1 : 1 ≤ Λ_s := one_le_pow₀ (by linarith [Real.log_nonneg hbig1])
  have hΛsΛ : Λ_s ≤ Λ := logPow_mono hbig1 le_rfl (le_max_left _ _)
  -- The new level `0` and the old spanner.
  have hHnew : (H₀.m : ℝ) ≤ N₁ * P.K_s * P.γ_ℓ * Λ_s := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlev, -⟩ :=
      initAt_state_props (L := L) (q := q) (t := 0) hSpec hVG' hG'm le_rfl
    have h0 := hlev ⟨0, Nat.zero_lt_succ L⟩
    simp only [initAt, ↓reduceIte] at h0
    have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
    have hl : (1 + Real.log ((nact : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s ≤ Λ_s :=
      logPow_mono harg1 harg_le le_rfl
    have hl0 : 0 ≤ (1 + Real.log ((nact : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
      pow_nonneg (by linarith [Real.log_nonneg harg1]) _
    calc (H₀.m : ℝ) ≤ P.K_s * (nact : ℝ) * P.γ_ℓ *
          (1 + Real.log ((nact : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s := h0
      _ ≤ P.K_s * N₁ * P.γ_ℓ * Λ_s :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnact P.hK_s) hγl) hl hl0
          (mul_nonneg (mul_nonneg P.hK_s (by linarith)) hγl)
      _ = N₁ * P.K_s * P.γ_ℓ * Λ_s := by ring
  have hHold : (st.H.m : ℝ) ≤ N₁ * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by
    have h0 := (sparsity_H hVG₀ hL hq1 hGm₀ hSpec hBV hds).2 k hk.le
    dsimp only at h0
    have hkn : (G₀.applyBatch (us.take k)).n ≤ nMax := hn k (Nat.le_succ k)
    have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
    have harg1' : (1 : ℝ) ≤ ((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (G₀.applyBatch (us.take k)).n,
        Nat.cast_nonneg (α := ℝ) G₀.m]
    have hknr : ((G₀.applyBatch (us.take k)).n : ℝ) ≤ nMax := by exact_mod_cast hkn
    have hl : (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
        Λ_s := logPow_mono harg1' (by linarith) le_rfl
    have hl0 : 0 ≤ (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
      pow_nonneg (by linarith [Real.log_nonneg harg1']) _
    have hkn' : ((G₀.applyBatch (us.take k)).n : ℝ) ≤ N₁ := le_trans hknr hnN
    have hLK : 0 ≤ (L + 1 : ℝ) * P.K_s := mul_nonneg (by positivity) P.hK_s
    calc (st.H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * ((G₀.applyBatch (us.take k)).n : ℝ) * P.γ_ℓ *
          (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := h0
      _ ≤ (L + 1 : ℝ) * P.K_s * N₁ * P.γ_ℓ * Λ_s :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn' hLK) hγl) hl hl0
          (mul_nonneg (mul_nonneg hLK (by linarith)) hγl)
      _ = N₁ * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by ring
  -- The bound on the cost, in the form of `restart_extra_of_le`.
  set F : ℝ := (dsInitCostFactor impl : ℝ) with hFdef
  have hF : (30000 : ℝ) ≤ F := by
    rw [hFdef]; exact_mod_cast le_dsInitCostFactor impl
  have hencst : st.G.updateEnc u = (G₀.applyBatch (us.take k)).updateEnc u := by
    rw [hInvk.G_eq]
  set enc : ℝ := ((G₀.applyBatch (us.take k)).updateEnc u : ℝ) with henc
  have henc1 : (1 : ℝ) ≤ enc := by rw [henc]; exact_mod_cast one_le_updateEnc _ u
  set A : ℝ := P.K_t * ((nact : ℝ) + (G'.m : ℝ) * P.γ_ℓ ^ 2) * X with hA
  have hA0 : 0 ≤ A := by
    have := P.hK_t
    have : 0 ≤ (nact : ℝ) + (G'.m : ℝ) * P.γ_ℓ ^ 2 := by positivity
    positivity
  have hγ0 : 0 ≤ (G'.m : ℝ) * P.γ_ℓ := mul_nonneg (Nat.cast_nonneg _) (by linarith [P.hγ_ℓ])
  set S : ℝ := A + (G'.n : ℝ) + (G'.m : ℝ) + (H₀.m : ℝ) + (G'.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1
    with hS
  have hInitB' : ((dsInitCoreCost impl mMax G' : ℕ) : ℝ) + 140 * (G'.n : ℝ) +
      500 * (G'.m : ℝ) + 420 ≤ F * S := by
    have h := hInitB
    push_cast at h
    rw [hS, hA]
    exact h
  -- The cost of the step and of the loop overhead.
  have hreemb_card : (runStepReembSet (L := L) G₀ q sp us k).card = G'.m := by
    simp only [runStepReembSet, hu, ← hst]
    rw [stepReembSet_eq_zero st u hcl]
    rfl
  set g : ℝ := ((dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 + 35 * L + 520 +
    90 * res.D.card + 90 * (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k).card +
    240 * res.UH.length + 240 : ℕ) : ℝ) with hg_def
  have hg_eq : g = ((dsInitCoreCost impl mMax G' : ℕ) : ℝ) + 675 * (st.H.m : ℝ) +
      250 * (H₀.m : ℝ) + 30 * (G'.n : ℝ) + 90 * ((L : ℝ) + 1) + 1500 + 35 * (L : ℝ) + 520 +
      90 * (res.D.card : ℝ) + 90 * (G'.m : ℝ) + 240 * (res.UH.length : ℝ) + 240 := by
    rw [hg_def, hcost, hreemb_card]
    simp only [dsStepZeroCost]
    push_cast
    ring
  have hΦ0r : (st.H.m : ℝ) ≤ (levelPot st : ℝ) := by exact_mod_cast hΦ0
  set T : ℝ := A + (G'.n : ℝ) + (G'.m : ℝ) + 2 * (H₀.m : ℝ) + (G'.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1 +
      ((L : ℝ) + 1) * enc + 2 * (st.H.m : ℝ) + (res.UH.length : ℝ) + (res.D.card : ℝ) with hT
  have hST : S ≤ T := by
    rw [hS, hT]
    have : 0 ≤ ((L : ℝ) + 1) * enc := by positivity
    linarith [Nat.cast_nonneg (α := ℝ) H₀.m, Nat.cast_nonneg (α := ℝ) st.H.m,
      Nat.cast_nonneg (α := ℝ) res.UH.length, Nat.cast_nonneg (α := ℝ) res.D.card]
  have hFST : F * S ≤ F * T := mul_le_mul_of_nonneg_left hST (by linarith)
  have hC : 0 < F + 3000 := by linarith
  have hL1enc : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) * enc := le_mul_of_one_le_right (by positivity) henc1
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hstep : g - 1440 * ((levelPot st : ℝ) - (H₀.m : ℝ)) ≤ (F + 3000) * T := by
    have hexp : (F + 3000) * T = F * T + 3000 * T := by ring
    rw [hexp, hg_eq]
    have hT' : 3000 * T = 3000 * A + 3000 * (G'.n : ℝ) + 3000 * (G'.m : ℝ) +
        6000 * (H₀.m : ℝ) + 3000 * ((G'.m : ℝ) * P.γ_ℓ) + 3000 * ((L : ℝ) + 1) +
        3000 * (((L : ℝ) + 1) * enc) + 6000 * (st.H.m : ℝ) + 3000 * (res.UH.length : ℝ) +
        3000 * (res.D.card : ℝ) := by rw [hT]; ring
    rw [hT']
    linarith [hInitB', hFST, hΦ0r, hA0, hγ0, hL1enc, Nat.cast_nonneg (α := ℝ) G'.m,
      Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) H₀.m,
      Nat.cast_nonneg (α := ℝ) st.H.m, Nat.cast_nonneg (α := ℝ) res.UH.length,
      Nat.cast_nonneg (α := ℝ) res.D.card]
  have hf : (g - 1440 * ((levelPot st : ℝ) - (H₀.m : ℝ))) / (F + 3000) ≤
      A + (G'.n : ℝ) + (G'.m : ℝ) + 2 * (H₀.m : ℝ) + (G'.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1 +
      ((L : ℝ) + 1) * enc + 2 * (st.H.m : ℝ) + (res.UH.length : ℝ) + (res.D.card : ℝ) := by
    rw [div_le_iff₀ hC]
    linarith only [hstep]
  have hmain := restart_extra_of_le P hL hq h1N hnact (Nat.cast_nonneg _) hn' hm'
    (Nat.cast_nonneg _) hHnew hHold hX0 hXΛ hΛs1 hΛsΛ hf
  have hf2 := (div_le_iff₀ hC).mp (sub_le_iff_le_add.mp (sub_le_iff_le_add.mp
    (sub_le_iff_le_add.mp hmain)))
  rw [hΦ1]
  linarith only [hf2]

end

end MinCostFlow.DynSpanner.Program
