module

public import MinCostFlow.Chain.SparseCoreRestart
public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.SparseCore.SparseCoreCostEnv
import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.SparseCore.SparseCoreBounds
import MinCostFlow.SparseCore.SparseCoreCost
import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.SparseCore.SparseCoreMetrics
import MinCostFlow.SparseCore.SparseCoreRunBounds
import MinCostFlow.SparseCore.SparseCoreSpannerMetrics
import MinCostFlow.SparseCore.SparseCoreStability
import MinCostFlow.DynSpanner.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Helper lemmas for the restart specification of `sparseCoreRestartTool`

This file collects small facts used by `SparseCoreRestartSpec.lean`. The first two compare the
parameters of `sparseCoreParams`: the length bound `gammaLEnv` is at most the recourse bound
`recEnv`, and the cost multiplier is at least four. The others unfold one step of
`sparseCoreRestartTool` (update, restart, and the fields `lsfs`, `S`, `emb`, `cost`) on the
nonempty and the empty instance.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-! ## 1. Parameter & tool helper lemmas -/

/-- The real inequality behind `gammaLEnv_le_recEnv`, with the parameters as plain numbers. -/
lemma gammaLEnv_le_recEnv_aux {B d Lr Ks γ Λs nr len RD lg : ℝ}
    (hB : 1 ≤ B) (hd : 0 ≤ d) (hLr : 1 ≤ Lr) (hKs : 0 ≤ Ks) (hγ : 1 ≤ γ) (hΛs : 1 ≤ Λs)
    (hnr : 1 ≤ nr) (hlen : 3 ≤ len) (hRD : 0 ≤ RD) (hlg : 1 ≤ lg) :
    max len (11 * ((Lr + 1) * Ks * γ * Λs * B * (2 * d + 190) + 115)) ≤
      B * ((3 + 2 * len) * (2 + 12 * Lr * nr * Ks * γ * Λs) + 2 * RD) *
          (2 * (d + 1 + 56 * lg)) +
        22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg := by
  have hP : 0 ≤ Ks * γ * Λs := by positivity
  have hK : 0 ≤ (Lr + 1) * (Ks * γ * Λs) * B := by positivity
  have hdK : 0 ≤ d * ((Lr + 1) * (Ks * γ * Λs) * B) := mul_nonneg hd hK
  -- The part of the recourse bound with `2` in place of `2 + 12 Lr nr Ks γ Λs`.
  have hT1 : 9 * 2 * (2 * (d + 57)) ≤ B * (3 + 2 * len) * 2 * (2 * (d + 1 + 56 * lg)) := by
    have h9 : (9 : ℝ) ≤ B * (3 + 2 * len) := by nlinarith
    have hu : 2 * (d + 57) ≤ 2 * (d + 1 + 56 * lg) := by linarith
    have := mul_le_mul (mul_le_mul_of_nonneg_right h9 (by norm_num : (0 : ℝ) ≤ 2)) hu
      (by positivity) (by positivity)
    linarith
  have hT1' : len ≤ B * (3 + 2 * len) * 2 * (2 * (d + 1 + 56 * lg)) := by
    have h1 : len ≤ B * (3 + 2 * len) := by nlinarith
    have h2 : (1 : ℝ) ≤ 2 * (2 * (d + 1 + 56 * lg)) := by linarith
    have := mul_le_mul h1 h2 (by norm_num) (by positivity)
    nlinarith
  -- The part with `12 Lr nr Ks γ Λs`, which dominates the `(2 d + 190)` term.
  have hX : 6 * ((Lr + 1) * (Ks * γ * Λs)) ≤ 12 * Lr * nr * Ks * γ * Λs := by
    have h1 : 6 * (Lr + 1) ≤ 12 * Lr * nr := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hP
    nlinarith
  have hT2 : 9 * (6 * ((Lr + 1) * (Ks * γ * Λs) * B)) * (2 * (d + 57)) ≤
      B * (3 + 2 * len) * (12 * Lr * nr * Ks * γ * Λs) * (2 * (d + 1 + 56 * lg)) := by
    have h9 : (9 : ℝ) ≤ 3 + 2 * len := by linarith
    have hBX : 6 * ((Lr + 1) * (Ks * γ * Λs) * B) ≤ B * (12 * Lr * nr * Ks * γ * Λs) := by
      have := mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ B)
      linarith
    have hu : 2 * (d + 57) ≤ 2 * (d + 1 + 56 * lg) := by linarith
    have h1 := mul_le_mul h9 hBX (by positivity) (by linarith)
    have h2 := mul_le_mul h1 hu (by positivity) (by positivity)
    linarith
  have hRest : 0 ≤ B * (2 * RD) * (2 * (d + 1 + 56 * lg)) +
      22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg := by positivity
  have hsplit : B * ((3 + 2 * len) * (2 + 12 * Lr * nr * Ks * γ * Λs) + 2 * RD) *
        (2 * (d + 1 + 56 * lg)) +
      22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg =
      B * (3 + 2 * len) * 2 * (2 * (d + 1 + 56 * lg)) +
      B * (3 + 2 * len) * (12 * Lr * nr * Ks * γ * Λs) * (2 * (d + 1 + 56 * lg)) +
      (B * (2 * RD) * (2 * (d + 1 + 56 * lg)) +
        22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg) := by ring
  have hT2nn : 0 ≤ B * (3 + 2 * len) * (12 * Lr * nr * Ks * γ * Λs) * (2 * (d + 1 + 56 * lg)) := by
    have : 0 ≤ len := by linarith
    have : 0 ≤ Lr := by linarith
    have : 0 ≤ nr := by linarith
    positivity
  rw [hsplit]
  refine max_le ?_ ?_
  · linarith
  · have hE : 11 * ((Lr + 1) * Ks * γ * Λs * B * (2 * d + 190) + 115) =
        22 * (d * ((Lr + 1) * (Ks * γ * Λs) * B)) + 2090 * ((Lr + 1) * (Ks * γ * Λs) * B) + 1265 := by
      ring
    have hE2 : 9 * (6 * ((Lr + 1) * (Ks * γ * Λs) * B)) * (2 * (d + 57)) =
        108 * (d * ((Lr + 1) * (Ks * γ * Λs) * B)) + 6156 * ((Lr + 1) * (Ks * γ * Λs) * B) := by
      ring
    rw [hE]
    linarith

/-- The length factor `gammaLEnv` of `sparseCoreParams` is at most the recourse factor `recEnv`. -/
lemma gammaLEnv_le_recEnv (E : SparseCoreEnv) (m : ℕ) :
    gammaLEnv E m ≤ recEnv E m := by
  have hlog : 1 ≤ Real.log (E.c_n * ((m : ℝ) + 1) + 2) := by
    have harg : (3 : ℝ) ≤ E.c_n * ((m : ℝ) + 1) + 2 := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [E.hc_n]
    exact le_trans (by linarith [real_log_three_gt]) (Real.log_le_log (by norm_num) harg)
  have hlg : 1 ≤ (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2 := one_le_pow₀ hlog
  have h := gammaLEnv_le_recEnv_aux (B := (E.B_fn m : ℝ)) (d := (E.d_fn m : ℝ)) (Lr := (E.L : ℝ))
    (Ks := (E.P_fn m).K_s) (γ := (E.P_fn m).γ_ℓ) (Λs := coreLambdaS (E.P_fn m) m)
    (nr := coreNRoot E.L m) (len := coreE82Len E.L (E.P_fn m))
    (RD := coreBucketRecD E.L (E.P_fn m) m) (lg := (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2)
    (by exact_mod_cast E.hB_pos m) (Nat.cast_nonneg _) (by exact_mod_cast E.hL)
    (E.P_fn m).hK_s (E.P_fn m).hγ_ℓ (coreLambdaS_ge_one _ _) (coreNRoot_ge_one _ _)
    (coreE82Len_ge_three E.L E.hL _) (coreBucketRec_pos E.L (E.P_fn m) m).2.1 hlg
  unfold gammaLEnv recEnv ucRatioHi
  unfold coreBucketRecUH
  exact h

lemma costMult_ge_four (E : SparseCoreEnv) (m : ℕ) : 4 ≤ costMult E m := by
  set P_b := E.P_fn m
  have h1 : (3 : ℝ) ≤ (3 : ℝ) ^ ((E.L + 1) * (E.L + 2) / 2 + E.L + 2) := by
    have hexp : 1 ≤ (E.L + 1) * (E.L + 2) / 2 + E.L + 2 := by omega
    calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (3 : ℝ) ^ ((E.L + 1) * (E.L + 2) / 2 + E.L + 2) := pow_le_pow_right₀ (by norm_num) hexp
  have h2 : 1 ≤ P_b.γ_c ^ (E.L + 1) := one_le_pow₀ P_b.hγ_c
  have h3 : 1 ≤ P_b.γ_ℓ ^ ((E.L + 1) * (E.L + 2) / 2 + 2) := one_le_pow₀ P_b.hγ_ℓ
  have hE : 3 ≤ coreE_L E.L P_b := by
    dsimp only [coreE_L]
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
  have hd : (1 : ℝ) ≤ (E.d_fn m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (E.d_fn m)]
  have hkt : 1 ≤ P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1 := by
    have := P_b.hK_t; have := P_b.hγ_ℓ
    nlinarith [sq_nonneg P_b.γ_ℓ]
  have hmx : (1 : ℝ) ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m) := le_max_left _ _
  have hL1 : (2 : ℝ) ≤ (E.L : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
    linarith
  have hprod : 4 ≤ coreE_L E.L P_b * ((E.d_fn m : ℝ) + 1) *
      (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) * max 1 ((E.L : ℝ) * coreNRoot E.L m) * ((E.L : ℝ) + 1) := by
    have ha : 3 ≤ coreE_L E.L P_b * ((E.d_fn m : ℝ) + 1) := by nlinarith
    have hb : 3 ≤ coreE_L E.L P_b * ((E.d_fn m : ℝ) + 1) *
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) := by nlinarith
    have hc : 3 ≤ coreE_L E.L P_b * ((E.d_fn m : ℝ) + 1) *
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) * max 1 ((E.L : ℝ) * coreNRoot E.L m) := by nlinarith
    nlinarith
  exact le_trans hprod (le_max_right _ _)

lemma stepTreeCoreAux_U_C_eq_of_cs_ts {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {st₁ st₂ : TreeCoreState L} (hcs : st₁.cs = st₂.cs) (hts : st₁.ts = st₂.ts)
    (U : List Update) :
    (stepTreeCoreAux sparsify st₁ U).U_C = (stepTreeCoreAux sparsify st₂ U).U_C := by
  dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith]
  rw [hcs, hts]

lemma stepTreeCoreAux_newlyActive_eq_of_cs_act {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {st₁ st₂ : TreeCoreState L} (hcs : st₁.cs = st₂.cs) (hact : st₁.activeComps = st₂.activeComps)
    (U : List Update) :
    (stepTreeCoreAux sparsify st₁ U).newlyActive =
      (stepTreeCoreAux sparsify st₂ U).newlyActive := by
  dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith]
  rw [hcs, hact]

lemma batchPrefixLen_le_flatten (Us : List (List Update)) (t : ℕ) :
    batchPrefixLen Us t ≤ Us.flatten.length := by
  change (Us.take t).flatten.length ≤ Us.flatten.length
  conv_rhs => rw [← List.take_append_drop t Us, List.flatten_append, List.length_append]
  exact Nat.le_add_right _ _

lemma list_sum_count_eq_length (xs : List ℕ) (k : ℕ) (hx : ∀ x ∈ xs, x < k) :
    xs.length = ∑ j ∈ Finset.range k, xs.count j := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : a < k := hx a List.mem_cons_self
    have hxs := ih (fun x hmem => hx x (List.mem_cons_of_mem a hmem))
    simp only [List.length_cons, hxs, List.count_cons]
    have hsplit : ∑ j ∈ Finset.range k, (xs.count j + if a == j then 1 else 0) =
        (∑ j ∈ Finset.range k, xs.count j) +
          ∑ j ∈ Finset.range k, (if a == j then 1 else 0) :=
      Finset.sum_add_distrib
    have h1 : ∑ j ∈ Finset.range k, (if a == j then 1 else 0) = 1 := by
      have : (fun j => if a == j then (1 : ℕ) else 0) = (fun j => if a = j then 1 else 0) := by
        funext j; simp [beq_iff_eq]
      rw [this, Finset.sum_ite_eq]
      simp [Finset.mem_range.mpr ha]
    omega

lemma sRT_update_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).update st U ℓ g =
      ({ isNonempty := true, k := st.k,
         trees := fun j => (stepTreeCoreAux sparsify (st.trees j) U).state },
       fun j => (stepTreeCoreAux sparsify (st.trees j) U).U_S) := by
  dsimp only [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith]
  simp only [hne, ↓reduceIte]

lemma sRT_lsfs_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hne : st.isNonempty = true) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).lsfs st j = (st.trees j).cs.lsf := by
  change (if st.isNonempty = true then (st.trees j).cs.lsf else emptyLSF) = _
  simp only [hne, ↓reduceIte]

lemma sRT_lsfs_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hem : st.isNonempty = false) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).lsfs st j = emptyLSF := by
  change (if st.isNonempty = true then (st.trees j).cs.lsf else emptyLSF) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sRT_S_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hne : st.isNonempty = true) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).S st j = (st.trees j).S_cur := by
  change (if st.isNonempty = true then (st.trees j).S_cur else emptyGraph) = _
  simp only [hne, ↓reduceIte]

lemma sRT_S_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hem : st.isNonempty = false) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).S st j = emptyGraph := by
  change (if st.isNonempty = true then (st.trees j).S_cur else emptyGraph) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sRT_emb_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hne : st.isNonempty = true) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).emb st j = (st.trees j).emb := by
  change (if st.isNonempty = true then (st.trees j).emb else fun _ => []) = _
  simp only [hne, ↓reduceIte]

lemma sRT_emb_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hem : st.isNonempty = false) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).emb st j = fun _ => [] := by
  change (if st.isNonempty = true then (st.trees j).emb else fun _ => []) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sRT_cost_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreState L} (hem : st.isNonempty = false) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).cost st = 0 := by
  change (if st.isNonempty = true then _ else 0) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sRT_foldl_restart_empty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (hem : st.isNonempty = false) (p : List ℕ) :
    List.foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart
      (st : (sparseCoreRestartTool oracle C_lsst L sparsify).State) p = st := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    have hx : (sparseCoreRestartTool oracle C_lsst L sparsify).restart st x = st := by
      change (if st.isNonempty then _ else st) = st
      simp only [hem, Bool.false_eq_true, ↓reduceIte]
    change List.foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart
      ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x) xs = st
    rw [hx]
    exact ih

end MinCostFlow.Chain

end
