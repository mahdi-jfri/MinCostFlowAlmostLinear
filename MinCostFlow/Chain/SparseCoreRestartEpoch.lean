module

public import MinCostFlow.Chain.SparseCoreRestartAux
public import MinCostFlow.Chain.SparseCoreRestart
public import MinCostFlow.Chain.SparseCoreRestartDyn
public import MinCostFlow.Chain.SparseCoreRestartInv
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
import MinCostFlow.DynSpanner.WalkCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Epoch invariants of `sparseCoreRestartTool`

An epoch of branch `j` is the run of its tree state from the last restart `s₀` of `j` (or from
`s₀ = 0`) up to a stage `t`, with no restart of `j` in between. This file proves that along an
epoch the tree states, read through `epochTreeSeq`, satisfy the same invariants as a run of
`sparseCoreTool` without restarts: the bucket spanners of Theorem 8.2 are valid and small, each
step is a valid batch on the spanner `S`, and the per-bucket recourse and cost obey the bounds of
Theorem 8.2. The proof applies the epoch lemmas of `SparseCoreRestart.lean`
(`epochTreeSeq_dyn_spec`, `runAfterRestarts_S_cur_inv`) at each step.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-! ## 2. Epoch `Theorem 8.2`, stage, and step invariants -/

lemma epochTreeSeq_eq_post
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (s₀ t j : ℕ) (hst : s₀ ≤ t) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let ep := epochTreeSeq oracle C_lsst L sparsify k M N D restarts s₀ t j
    (∀ r < t - s₀, ep r = (T.runAfterRestarts k M N D restarts (s₀ + r)).trees j) ∧
    (j ∉ restarts t ∨ s₀ = t →
      ep (t - s₀) = (T.runAfterRestarts k M N D restarts t).trees j) ∧
    (s₀ < t → ep (t - s₀) = (T.runAfterUpdate k M N D restarts t).1.trees j) := by
  intro T ep
  refine ⟨fun r hr => ?_, fun hnor => ?_, fun hlt => ?_⟩
  · have hcond : ¬ (s₀ + r = t ∧ s₀ < t) := by omega
    dsimp only [ep, epochTreeSeq, T]
    simp only [hcond, ↓reduceIte]
  · rcases hnor with hni | rfl
    · by_cases heq : s₀ = t
      · subst heq
        simp only [Nat.sub_self, Nat.add_zero]
        dsimp only [ep, epochTreeSeq, T]
        simp [Nat.lt_irrefl]
      · have hlt : s₀ < t := by omega
        have hcond : s₀ + (t - s₀) = t ∧ s₀ < t := ⟨by omega, hlt⟩
        dsimp only [ep, epochTreeSeq, T]
        simp only [hcond, ↓reduceIte]
        have hf := (foldl_restart_props oracle C_lsst L sparsify
          (T.runAfterUpdate k M N D restarts t).1 (restarts t)).2.2.2.2 j hni
        exact hf.symm
    · simp only [Nat.sub_self, Nat.add_zero]
      dsimp only [ep, epochTreeSeq, T]
      simp [Nat.lt_irrefl]
  · have hcond : s₀ + (t - s₀) = t ∧ s₀ < t := ⟨by omega, hlt⟩
    dsimp only [ep, epochTreeSeq, T]
    simp only [hcond, and_self, ↓reduceIte]

lemma epoch_UC_batchSplitCount_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) (C : Finset ℕ) (hC : C ∈ components (D.G 0)) :
    let G₀ := D.G 0
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    ∑ r ∈ Finset.range τ,
      batchSplitCount ((stepTreeCoreAux sparsify
        (treeRunSeq oracle C_lsst L sparsify k M N D j r).1 (D.U (r + 1))).U_C C) ≤ splitB := by
  intro G₀ splitB
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  set cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
  have hS_step : ∀ r < τ,
      batchSplitCount ((stepTreeCoreAux sparsify
        (treeRunSeq oracle C_lsst L sparsify k M N D j r).1 (D.U (r + 1))).U_C C) ≤
        (D.U (r + 1)).length * (G₀.maxDeg + 1) +
          (((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.cs.compSt C).R \
            ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).R).card := by
    intro r hr
    have h1 := ((hStep r hr).2.2.2 C hC).2.2.1
    have h2 := projCompBatchWeight_le_length (D.U (r + 1))
      (treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.G
      ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).G
    exact le_trans h1 (Nat.add_le_add_right (Nat.mul_le_mul_right _ h2) _)
  have hsum_step :
      ∑ r ∈ Finset.range τ, batchSplitCount ((stepTreeCoreAux sparsify
        (treeRunSeq oracle C_lsst L sparsify k M N D j r).1 (D.U (r + 1))).U_C C) ≤
      (∑ r ∈ Finset.range τ, (D.U (r + 1)).length) * (G₀.maxDeg + 1) +
        ∑ r ∈ Finset.range τ,
          (((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.cs.compSt C).R \
            ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).R).card := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r hr => hS_step r (Finset.mem_range.mp hr)
  have hU_len_sum : ∑ r ∈ Finset.range τ, (D.U (r + 1)).length =
      ∑ s ∈ Finset.Icc 1 τ, (D.U s).length :=
    sum_range_nat_eq_sum_Icc_succ (fun s => (D.U s).length) τ
  have hR_sum_le : ∀ t ≤ τ,
      (∑ r ∈ Finset.range t,
        (((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.cs.compSt C).R \
          ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).R).card : ℝ) ≤
        56 * ((∑ s ∈ Finset.Icc 1 t, (D.U s).length : ℕ) : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ s ih =>
      intro hs1
      have hs_lt : s < τ := hs1
      have hs_le : s ≤ τ := Nat.le_of_lt hs_lt
      have hb_s := hBase s hs_le
      have hStep_s := hStep s hs_lt
      set st_s := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
      set st_s1 := (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1
      have hG₀_s : st_s.cs.G₀ = G₀ := by rw [hb_s.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
      have hC' : C ∈ components st_s.cs.G₀ := by rw [hG₀_s]; exact hC
      have hI_sC := (hb_s.2.2.2.2.2.2.2.2.1.hCompLSF C hC').1
      have hcomp_sp := compLSFBatch_compSt hb_s.2.2.2.2.2.2.2.2.1 hStep_s.1 hC'
      have hstepR := compLSFBatch_compSt_R_le_compN hb_s.2.2.2.2.2.2.2.2.1 hStep_s.1 hC'
      have hcomp_step : st_s1.cs.compSt C = (compLSFBatch st_s.cs (D.U (s + 1))).compSt C := rfl
      rw [← hcomp_step, hG₀_s] at hstepR
      have hsq : (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 2 ≤ (Real.log ((G₀.n : ℝ) + 2)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [half_lt_log_add_two (compGraph G₀ C).n])
          (Real.log_le_log (by positivity)
            (by linarith [show ((compGraph G₀ C).n : ℝ) ≤ G₀.n from
              by exact_mod_cast compGraph_n_le hC])) 2
      have hR_sub : (st_s.cs.compSt C).R ⊆ (st_s1.cs.compSt C).R := hcomp_step ▸ hcomp_sp.2.2.2.1
      have hcard_diff : (((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card : ℝ) ≤
          56 * ((D.U (s + 1)).length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
        rw [Finset.card_sdiff_of_subset hR_sub, Nat.cast_sub (Finset.card_le_card hR_sub)]
        have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 56 * ((D.U (s + 1)).length : ℝ))
        linarith
      have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
        ext x; simp [Finset.mem_Icc]; omega
      rw [Finset.sum_range_succ, hIcc, Finset.sum_insert (by simp), Nat.cast_add]
      linarith [ih hs_le, hcard_diff]
  have hR_le : (∑ r ∈ Finset.range τ,
      (((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.cs.compSt C).R \
        ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).R).card : ℝ) ≤
      56 * (M : ℝ) / (k : ℝ) := by
    have hr := hR_sum_le τ le_rfl
    have hlogG_pos : (0 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := by linarith [half_lt_log_add_two G₀.n]
    have hlogN_pos : (0 : ℝ) < Real.log ((N : ℝ) + 2) := by linarith [half_lt_log_add_two N]
    have hlogN2_pos : (0 : ℝ) < (Real.log ((N : ℝ) + 2)) ^ 2 := sq_pos_of_pos hlogN_pos
    have hlog_sq : (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 :=
      pow_le_pow_left₀ hlogG_pos.le
        (Real.log_le_log (by positivity) (by linarith [show (G₀.n : ℝ) ≤ N from by exact_mod_cast hN])) 2
    have hrN : (∑ r ∈ Finset.range τ,
        (((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.cs.compSt C).R \
          ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).R).card : ℝ) ≤
        56 * ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) *
          (Real.log ((N : ℝ) + 2)) ^ 2 :=
      le_trans hr (mul_le_mul_of_nonneg_left hlog_sq (by positivity))
    have h1 : 56 * ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) ≤
        56 * SparseCoreTool.updateThreshold k M N := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hlogN2_pos.le
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have heq : 56 * SparseCoreTool.updateThreshold k M N *
        (Real.log ((N : ℝ) + 2)) ^ 2 = 56 * (M : ℝ) / (k : ℝ) := by
      rw [SparseCoreTool.updateThreshold]
      field_simp [hlogN2_pos.ne', hk_pos.ne']
    exact le_trans hrN (heq ▸ h2)
  have hfloor : ∑ s ∈ Finset.Icc 1 τ, (D.U s).length ≤
      Nat.floor (SparseCoreTool.updateThreshold k M N) := Nat.le_floor hThresh
  have hceil : ∑ r ∈ Finset.range τ,
      (((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.cs.compSt C).R \
        ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C).R).card ≤
      Nat.ceil (56 * (M : ℝ) / (k : ℝ)) := by
    exact_mod_cast le_trans hR_le (Nat.le_ceil _)
  rw [hU_len_sum] at hsum_step
  exact le_trans hsum_step (Nat.add_le_add (Nat.mul_le_mul_right _ hfloor) hceil)

lemma epochTreeSeq_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let G₀ := D.G 0
    let cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let actB := fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    let Δ := t - s₀
    let st := epochTreeSeq oracle C_lsst L sparsify k M N D restarts s₀ t j
    let Hb := fun C b => restartBucketGraph (st 0) C b
    let Us_ep : Finset ℕ → ℤ → List (List Update) := fun C b =>
      (List.range Δ).map fun r => (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)
    (∀ C ∈ components G₀, ∀ b : ℤ,
      (Hb C b).IsValid ∧ (Hb C b).m ≤ G₀.m ∧ (Hb C b).n ≤ 2 * (Hb C b).m ∧
      (Hb C b).maxDeg ≤ (ts₀ C).C.maxDeg ∧
      batchSplitCount (Us_ep C b).flatten ≤ splitB) ∧
    ((components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ G₀.m) ∧
    (∀ r ≤ Δ,
      (st r).S_cur.IsValid ∧ (st r).activeComps ⊆ components G₀ ∧
      ∀ C ∈ components G₀, ∀ b : ℤ,
        ((st r).dyn (C, b)).G.IsValid ∧
        ((st r).ts C).C.IsSubgraph ((st r).dyn (C, b)).G ∧
        ((st r).dyn (C, b)).G.E = ((st r).ts C).C.E.filter (fun e => (st r).origBucket e = b) ∧
        ((st r).dyn (C, b)).G.n ≤ coreNMax M ∧
        ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) *
          P_b.γ_ℓ * (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) *
          P_b.γ_ℓ * coreLambdaS P_b M ∧
        (piTotal ((st r).dyn (C, b))).IsEmbedding ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H ∧
        ((piTotal ((st r).dyn (C, b))).length ((st r).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b ∧
        (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H (fun _ => 1) ≤
          coreE82Cong L P_b * ((ts₀ C).C.maxDeg : ℝ) ∧
        (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H (fun _ => 1) ≤
          coreE82Cong L P_b * (2 * (M : ℝ))) ∧
    (∀ r < Δ,
      let info := stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))
      (st r).S_cur.BatchIsValid info.U_S ∧
      (st (r + 1)).S_cur = (st r).S_cur.applyBatch info.U_S ∧
      (D.U (s₀ + r + 1) = [] → info.U_S = []) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update ((st r).dyn (C, b)) (info.U_b (C, b)) (sparsify (st r).m₀) ∧
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H ∧
        (info.U_b (C, b)).length ≤ (info.U_C C).length ∧
        (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ eH ∈ walkEdges (piTotal ((st (r + 1)).dyn (C, b)) eG),
          eH ∉ (info.stepOut (C, b)).D → eH ∈ walkEdges (piTotal ((st r).dyn (C, b)) eG)) ∧
        (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ e' : ℕ, e' ∉ (info.stepOut (C, b)).D →
          walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) e' ≤
            walkCount (piTotal ((st r).dyn (C, b)) eG) e')) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧
      info.newlyActive.card ≤ 2 * (D.U (s₀ + r + 1)).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (st (r + 1)).activeComps.sum (fun C => (st r).activeBuckets C |>.sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        info.newlyActive.sum (fun C => (st r).activeBuckets C |>.sum fun b =>
          ((st r).dyn (C, b)).H.E.card) +
        7 * (D.U (s₀ + r + 1)).length +
        2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card +
        2 * info.D_total.card) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ,
      let nMax_b := (Hb C b).n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length : ℝ)
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
            (Us_ep C b) r).G.batchEnc
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ)
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
          (Us_ep C b) r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) := by
  intro G₀ cs₀ ts₀ actB splitB Δ st Hb Us_ep
  have hDyn := epochTreeSeq_dyn_spec oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D restarts hM hN hSp hG₀ hV₀ hℓ₀ hD s₀ t j hst htτ hs₀ hNoRest
  dsimp only at hDyn
  obtain ⟨hSt_base, hSt_step⟩ := epochTreeSeq_steps oracle C_lsst L sparsify
    k M N D restarts hV₀ s₀ t j hst hNoRest
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  obtain ⟨hSmall, _, _, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hSc := runAfterRestarts_S_cur_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D restarts hM hN hSp hG₀ hV₀ hℓ₀ hD j
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E :=
    fun C hC => initLSF_cov0 oracle C_lsst hk hG₀ hℓ₀ hC hLSST
  have hm₀_eq : ∀ r ≤ Δ, (st r).m₀ = M := fun r hr =>
    (hSt_base r hr).m₀.trans (hBase (s₀ + r) (by omega)).1
  -- 1. Bucket split counts ≤ splitB
  have hSplit_b : ∀ C ∈ components G₀, ∀ b : ℤ, batchSplitCount (Us_ep C b).flatten ≤ splitB := by
    intro C hC b
    have hflat_eq : batchSplitCount (Us_ep C b).flatten =
        ∑ r ∈ Finset.range Δ, batchSplitCount
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) := by
      have hlen_u : (Us_ep C b).length = Δ := by simp [Us_ep]
      clear hDyn hSc hSmall
      have hgen : ∀ n ≤ Δ, batchSplitCount ((Us_ep C b).take n).flatten =
          ∑ r ∈ Finset.range n, batchSplitCount
            ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) := by
        intro n
        induction n with
        | zero => intro _; simp [batchSplitCount]
        | succ m ih =>
          intro hm
          have hm_lt : m < Δ := hm
          have hget : (Us_ep C b)[m]? =
              some ((stepTreeCoreAux sparsify (st m) (D.U (s₀ + m + 1))).U_b (C, b)) := by
            dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hm_lt]; rfl
          rw [take_succ_of_getElem? hget, List.flatten_append, List.flatten_singleton,
            SparseCore.batchSplitCount_append, ih (Nat.le_of_lt hm_lt), Finset.sum_range_succ]
      have h := hgen Δ le_rfl
      rwa [List.take_of_length_le (by omega)] at h
    have hle_sum : ∑ r ∈ Finset.range Δ, batchSplitCount
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) ≤
        ∑ r ∈ Finset.range Δ, batchSplitCount
          ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1
            (D.U (s₀ + r + 1))).U_C C) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hr_lt : r < Δ := Finset.mem_range.mp hr
      have hT_r : TildeInv (cs₀.compSt C) ((st r).cs.compSt C) ((st r).ts C) := by
        rw [(hSt_base r hr_lt.le).cs, (hSt_base r hr_lt.le).ts]
        exact (hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2 C hC |>.2.1
      have hG_r := (hDyn C hC b).2.2.2.2.2.2.2.1 r hr_lt.le
      have hUC_sp := (hStep (s₀ + r) (by omega)).2.2.2 C hC
      have hUC_eq : (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C =
          (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1
            (D.U (s₀ + r + 1))).U_C C :=
        congrFun (stepTreeCoreAux_U_C_eq_of_cs_ts sparsify
          (hSt_base r hr_lt.le).cs (hSt_base r hr_lt.le).ts (D.U (s₀ + r + 1))) C
      have htd : ((st r).ts C).C.BatchIsValid
            ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C) ∧
          (∀ op ∈ (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C, isDelOrSplit op) := by
        rw [hUC_eq, (hSt_base r hr_lt.le).ts]
        have htr := tildeStepBatch_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
          ((hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.1.hCompLSF C
            (by rw [(hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.1, compLSFBatch_G₀]; exact hC)).1
          ((hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2 C hC).1
          ((hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
          (compLSFBatch_compSt (hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.1
            (hStep (s₀ + r) (by omega)).1
            (by rw [(hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.1, compLSFBatch_G₀]; exact hC)).2.2.1
        dsimp only at htr
        exact ⟨hUC_sp.1 ▸ htr.2.2.2.2.2.1, hUC_sp.2.1⟩
      have hfb := filterBucketBatch_spec hT_r.hC_val hG_r.2.1 hG_r.2.2.2.2 hG_r.2.2.2.1 htd.1 htd.2
      change batchSplitCount
          (filterBucketBatch ((st r).dyn (C, b)).G
            ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C)).2 ≤ _
      rw [← hUC_eq]
      exact hfb.2.2.2.2.2.2.2
    have hshift : ∑ r ∈ Finset.range Δ, batchSplitCount
          ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1
            (D.U (s₀ + r + 1))).U_C C) ≤
        ∑ s ∈ Finset.range τ, batchSplitCount
          ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C) := by
      let f : ℕ → ℕ := fun s => batchSplitCount
        ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
          (D.U (s + 1))).U_C C)
      change ∑ r ∈ Finset.range Δ, f (s₀ + r) ≤ ∑ s ∈ Finset.range τ, f s
      rw [← Finset.sum_image (f := f) (s := Finset.range Δ) (g := fun r => s₀ + r)
        (fun a _ b _ h => Nat.add_left_cancel h)]
      exact Finset.sum_le_sum_of_subset fun x hx => by
        rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega)
    rw [hflat_eq]
    exact le_trans hle_sum (le_trans hshift (epoch_UC_batchSplitCount_sum_le oracle C_lsst L sparsify
      hLSST k M N τ hk D hM hN hG₀ hV₀ hℓ₀ hD hThresh j C hC))
  -- 2. Theorem 8.2 per `(C, b)`
  have hT82 : ∀ C ∈ components G₀, ∀ b : ℤ,
      let nMax_b := (Hb C b).n + splitB
      let q_b := phaseBase nMax_b L
      let st_b := fun r => DynSpanner.runBatchState (L := L) (Hb C b) q_b (sparsify M) (Us_ep C b) r
      let res_b := fun r => DynSpanner.runBatchStepOut (L := L) (Hb C b) q_b (sparsify M) (Us_ep C b) r
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length : ℝ)
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((st_b r).G.batchEnc ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ)
      (∀ r ≤ Δ,
        (st_b r).G.IsSubgraph (st_b r).H ∧
        ((st_b r).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st_b r).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st_b r).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        (piTotal (st_b r)).IsEmbedding (st_b r).G (st_b r).H ∧
        ((piTotal (st_b r)).length (st_b r).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        (piTotal (st_b r)).vcong (st_b r).G (st_b r).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
            ((Hb C b).maxDeg : ℝ)) ∧
      (∀ r < Δ, ∀ U, (Us_ep C b)[r]? = some U →
        res_b r = DynSpanner.update
          (DynSpanner.runState (L := L) (Hb C b) q_b (sparsify M) (Us_ep C b).flatten
            (batchPrefixLen (Us_ep C b) r)) U (sparsify M) ∧
        (res_b r).state = st_b (r + 1) ∧
        (st_b r).H.BatchIsValid (res_b r).UH ∧
        (st_b r).H.applyBatch (res_b r).UH = (st_b (r + 1)).H ∧
        (res_b r).D ⊆ (st_b (r + 1)).H.E ∧
        (∀ eG ∈ (st_b (r + 1)).G.E, ∀ eH ∈ walkEdges (piTotal (st_b (r + 1)) eG),
          eH ∉ (res_b r).D → eH ∈ walkEdges (piTotal (st_b r) eG))) ∧
      ((∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b ∧
      (∑ r ∈ Finset.range Δ, ((res_b r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) := by
    intro C hC b nMax_b q_b st_b res_b Λ_s_b Λ_b E_L_b nRoot_b batchTot_b encTot_b
    have hdC := hDyn C hC b
    have hHb_mM : (Hb C b).m ≤ M := le_trans hdC.2.1 hM
    have hBV := hdC.2.2.2.2.1
    have hds := hdC.2.2.2.2.2.1
    have hsc := hSplit_b C hC b
    have hlen_Us : (Us_ep C b).length = Δ := by simp [Us_ep]
    have hthm := DynSpanner.theorem_8_2 hdC.1 hL hHb_mM hSp hBV hds hsc
    rcases hthm with ⟨_, _, hStage, hStep82, hCum⟩
    have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase _ L)
    have hSpars := DynSpanner.sparsity_H hdC.1 hL hq1 hHb_mM hSp hBV hds
    have hTrace := DynSpanner.batchTrace_spec hdC.1 hL hq1 hHb_mM hSp hBV hds
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have hs := hStage r (le_trans hr hlen_Us.symm.le)
      have hbp_le : batchPrefixLen (Us_ep C b) r ≤ (Us_ep C b).flatten.length :=
        batchPrefixLen_le_flatten (Us_ep C b) r
      have htr := hTrace.1 r (le_trans hr hlen_Us.symm.le)
      have hsp_r := hSpars.2 (batchPrefixLen (Us_ep C b) r) hbp_le
      dsimp only at hsp_r
      rw [← htr.1, ← htr.2.1] at hsp_r
      exact ⟨hs.2.1, hsp_r, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
    · intro r hr U hU
      exact hStep82 r (lt_of_lt_of_le hr hlen_Us.symm.le) U hU
    · have hc := hCum Δ (le_trans le_rfl hlen_Us.symm.le)
      have hstep_eq : ∀ r ∈ Finset.range Δ,
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)) = res_b r := by
        intro r hr
        exact (hDyn C hC b).2.2.2.2.2.2.2.2 r (Finset.mem_range.mp hr) |>.1
      have hbt_eq : ((Us_ep C b).take Δ).flatten.length =
          ∑ r ∈ Finset.range Δ,
            ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length := by
        have hlen_u : (Us_ep C b).length = Δ := by simp [Us_ep]
        have hgen : ∀ n ≤ Δ, ((Us_ep C b).take n).flatten.length =
            ∑ r ∈ Finset.range n,
              ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length := by
          intro n
          induction n with
          | zero => intro _; simp
          | succ m ih =>
            intro hm
            have hm_lt : m < Δ := hm
            have hget : (Us_ep C b)[m]? =
                some ((stepTreeCoreAux sparsify (st m) (D.U (s₀ + m + 1))).U_b (C, b)) := by
              dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hm_lt]; rfl
            rw [take_succ_of_getElem? hget, List.flatten_append, List.flatten_singleton,
              List.length_append, ih (Nat.le_of_lt hm_lt), Finset.sum_range_succ]
        simpa [hlen_u] using hgen Δ le_rfl
      have hbtR : (((Us_ep C b).take Δ).flatten.length : ℝ) = batchTot_b := by
        dsimp only [batchTot_b]; rw [hbt_eq, Nat.cast_sum]
      have henc_eq : (∑ t' ∈ Finset.range Δ, match (Us_ep C b)[t']? with
            | some U => ((st_b t').G.batchEnc U : ℝ)
            | none => 0) = encTot_b := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr_lt : r < Δ := Finset.mem_range.mp hr
        have hget : (Us_ep C b)[r]? =
            some ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) := by
          dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hr_lt]; rfl
        rw [hget]
      refine ⟨?_, ?_, ?_⟩
      · have h1 := hc.1
        dsimp only at h1
        rw [hbtR] at h1
        refine le_trans ?_ h1
        exact le_of_eq (Finset.sum_congr rfl fun r hr => by rw [hstep_eq r hr])
      · have h2 := hc.2.2.1
        dsimp only at h2
        rw [hbtR] at h2
        refine le_trans ?_ h2
        exact le_of_eq (Finset.sum_congr rfl fun r hr => by rw [hstep_eq r hr])
      · have h3 := hc.2.2.2
        exact h3.trans_eq (by rw [← henc_eq] <;> rfl)
  -- 3. Edge-count bounds and bucket `hm_sum`
  have hm_sum : (components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ G₀.m := by
    obtain ⟨_, hm0_sum, _⟩ := all_buckets_sum_le oracle hLSST hk hG₀ hV₀ hℓ₀ j
    refine le_trans (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => ?_) hm0_sum
    have hE_sub : (Hb C b).E ⊆ (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).E := by
      intro e he
      have hts_sub := ((hBase s₀ (le_trans hst htτ)).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1
      have hOB := (hBase s₀ (le_trans hst htτ)).2.2.2.2.1
      have hst0 := hSt_base 0 (Nat.zero_le Δ)
      rw [Nat.add_zero] at hst0
      change e ∈ ((st 0).ts C).C.E.filter (fun e => (st 0).origBucket e = b) at he
      rw [hst0.ts, hst0.origBucket, hOB, Finset.mem_filter] at he
      beta_reduce at he
      change e ∈ (initTildeState (cs₀.compSt C)).C.E.filter
        (fun e => bucketOf (coreLen (cs₀.compSt C).lsf (D.ℓ 0) e) = b)
      rw [Finset.mem_filter]
      refine ⟨hts_sub he.1, ?_⟩
      rw [← initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC e (hts_sub he.1),
        ← initCompLSF_safeLen_origBucket_eq oracle C_lsst hk hG₀ hV₀ hℓ₀ hC hLSST (hts_sub he.1)]
      exact he.2
    exact Finset.card_le_card hE_sub
  -- Package all outputs cleanly
  refine ⟨fun C hC b => ?_, hm_sum, ?_, ?_, ?_⟩
  · have hdC := hDyn C hC b
    exact ⟨hdC.1, hdC.2.1, hdC.2.2.1, hdC.2.2.2.1, hSplit_b C hC b⟩
  · -- Stage invariants (`r ≤ Δ`)
    intro r hr
    have hSc_r : (st r).S_cur.IsValid ∧ (st r).S_cur.V = (st r).cs.RF.R ∧
        (st r).S_cur.E =
          ((st r).activeComps.biUnion fun C => (actB C).biUnion fun b => ((st r).dyn (C, b)).H.E) ∪
            ((st r).activeComps.biUnion fun C => extraSet ((st r).cs.compSt C) ((st r).ts C)) ∪
            (st r).cs.crossEdges ∧
        (coreGraph (st r).cs.G (st r).cs.lsf).IsSubgraph (st r).S_cur := by
      dsimp only [st, epochTreeSeq]
      split_ifs with hcond
      · exact hcond.1 ▸ (hSc t htτ).1
      · exact (hSc (s₀ + r) (by omega)).2
    have hAct_r : (st r).activeComps ⊆ components G₀ := by
      rw [(hSt_base r hr).activeComps]
      exact (hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.2.2.1.2
    refine ⟨hSc_r.1, hAct_r, fun C hC b => ?_⟩
    have hdC := hDyn C hC b
    have hdr := hdC.2.2.2.2.2.2.2.1 r hr
    have ht82 := (hT82 C hC b).1 r hr
    have hm_b : (Hb C b).m ≤ M := le_trans hdC.2.1 hM
    have hn_b : (Hb C b).n ≤ 2 * M := le_trans hdC.2.2.1 (Nat.mul_le_mul_left 2 hm_b)
    have hSplitB : splitB ≤ coreSplitMax M :=
      splitB_le_coreSplitMax_at hk (le_trans (Finset.card_pos.mpr hV₀) hN) hM
    have hGn_le_nMax : ((st r).dyn (C, b)).G.n ≤ coreNMax M := by
      have hn_le_Hb : ((st r).dyn (C, b)).G.n ≤ (Hb C b).n + splitB := by
        have hv : ((st r).dyn (C, b)).G.n ≤ (Hb C b).n +
            batchSplitCount ((Us_ep C b).take r).flatten := by
          have hPref : (Hb C b).BatchIsValid ((Us_ep C b).take r).flatten ∧
              (Hb C b).applyBatch ((Us_ep C b).take r).flatten = ((st r).dyn (C, b)).G := by
            have hT82_r := ht82
            have htrace_r := DynSpanner.batchTrace_spec (q := phaseBase ((Hb C b).n + splitB) L)
              hdC.1 hL (le_trans (by omega) (two_le_phaseBase _ L)) hm_b hSp hdC.2.2.2.2.1
              hdC.2.2.2.2.2.1
            have htake_len : ((Us_ep C b).take r).flatten.length = batchPrefixLen (Us_ep C b) r := rfl
            have hBV_take : (Hb C b).BatchIsValid ((Us_ep C b).take r).flatten := by
              have h := hdC.2.2.2.2.1
              change (Hb C b).BatchIsValid (Us_ep C b).flatten at h
              rw [show (Us_ep C b).flatten =
                  ((Us_ep C b).take r).flatten ++ ((Us_ep C b).drop r).flatten by
                rw [← List.flatten_append, List.take_append_drop],
                SparseCore.batchIsValid_append] at h
              exact h.1
            refine ⟨hBV_take, ?_⟩
            rw [hdr.1]
            have hlen_Us : (Us_ep C b).length = Δ := by simp [Us_ep]
            have htr1 := (htrace_r.1 r (le_trans hr hlen_Us.symm.le)).2.1
            rw [htr1]
            congr 1
            change ((Us_ep C b).take r).flatten =
              (Us_ep C b).flatten.take ((Us_ep C b).take r).flatten.length
            rw [show (Us_ep C b).flatten = ((Us_ep C b).take r).flatten ++ ((Us_ep C b).drop r).flatten by
              rw [← List.flatten_append, List.take_append_drop]]
            simp
          have hds_take : ∀ op ∈ ((Us_ep C b).take r).flatten, isDelOrSplit op := fun op hop =>
            hdC.2.2.2.2.2.1 op (by
              change op ∈ (Us_ep C b).flatten
              rw [show (Us_ep C b).flatten =
                  ((Us_ep C b).take r).flatten ++ ((Us_ep C b).drop r).flatten by
                rw [← List.flatten_append, List.take_append_drop]]
              exact List.mem_append_left _ hop)
          unfold MGraph.n
          rw [← hPref.2]
          exact (applyBatch_V_card_eq_of_isDelOrSplit hPref.1 hds_take).le
        have hsc_take : batchSplitCount ((Us_ep C b).take r).flatten ≤ splitB := by
          have h1 : batchSplitCount ((Us_ep C b).take r).flatten ≤
              batchSplitCount (Us_ep C b).flatten := by
            conv_rhs =>
              rw [← List.take_append_drop r (Us_ep C b), List.flatten_append, SparseCore.batchSplitCount_append]
            exact Nat.le_add_right _ _
          exact le_trans h1 (hSplit_b C hC b)
        exact le_trans hv (Nat.add_le_add_left hsc_take _)
      dsimp only [coreNMax]
      omega
    have hΛ_le : (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
        coreLambdaS P_b M := by
      have harg1 : (1 : ℝ) ≤ (((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) ((st r).dyn (C, b)).G.n, Nat.cast_nonneg (α := ℝ) (Hb C b).m]
      have harg_le : (((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2 ≤
          (coreNMax M : ℝ) + (M : ℝ) + 2 := by
        have h1 : (((st r).dyn (C, b)).G.n : ℝ) ≤ (coreNMax M : ℝ) := by exact_mod_cast hGn_le_nMax
        have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_b
        linarith
      have hbase1 : 0 ≤ 1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2) := by
        linarith [Real.log_nonneg harg1]
      exact pow_le_pow_left₀ hbase1 (add_le_add le_rfl (Real.log_le_log (by linarith) harg_le)) P_b.p_s
    have hHm_le1 : (((st r).dyn (C, b)).H.m : ℝ) ≤
        (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s := by
      rw [hdr.1]; exact ht82.2.1
    have hHm_le2 : (((st r).dyn (C, b)).H.m : ℝ) ≤
        (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ * coreLambdaS P_b M := by
      have hK_s := P_b.hK_s
      have hγℓ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
      have hfac : 0 ≤ (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ := by positivity
      exact le_trans hHm_le1 (mul_le_mul_of_nonneg_left hΛ_le hfac)
    have hvc1 : (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H
        (fun _ => 1) ≤ coreE82Cong L P_b * ((ts₀ C).C.maxDeg : ℝ) := by
      have h1 : (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H
          (fun _ => 1) ≤ coreE82Cong L P_b * ((Hb C b).maxDeg : ℝ) := by
        rw [hdr.1]; exact ht82.2.2.2.2
      have hd_le : ((Hb C b).maxDeg : ℝ) ≤ ((ts₀ C).C.maxDeg : ℝ) := by
        exact_mod_cast hdC.2.2.2.1
      exact le_trans h1 (mul_le_mul_of_nonneg_left hd_le (coreE82Cong_nonneg L P_b))
    have hvc2 : (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H
        (fun _ => 1) ≤ coreE82Cong L P_b * (2 * (M : ℝ)) := by
      have hdeg_le : (ts₀ C).C.maxDeg ≤ 2 * (ts₀ C).C.m := maxDeg_le_two_m (ts₀ C).C
      have hm_ts0 : (ts₀ C).C.m ≤ G₀.m := by
        have hT₀ := initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
        have hsub1 : (ts₀ C).C.E ⊆ (cs₀.compSt C).G.E := by
          intro e he; exact (Finset.mem_sdiff.mp (hT₀.hCE_sub he)).1
        have hm_G : (cs₀.compSt C).G.m ≤ G₀.m := by
          rw [(initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2.1]
          exact compGraph_m_le
        exact le_trans (Finset.card_le_card hsub1) hm_G
      have hm_ts0_M : (ts₀ C).C.m ≤ M := le_trans hm_ts0 hM
      have hdegR : ((ts₀ C).C.maxDeg : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast le_trans hdeg_le (by omega)
      exact le_trans hvc1 (mul_le_mul_of_nonneg_left hdegR (coreE82Cong_nonneg L P_b))
    refine ⟨hdr.2.1, hdr.2.2.2.2, hdr.2.2.2.1, hGn_le_nMax, ?_, hHm_le1, hHm_le2, ?_, ?_, hvc1, hvc2⟩
    · rw [hdr.1]; exact ht82.1
    · rw [hdr.1]; exact ht82.2.2.1
    · rw [hdr.1]; exact ht82.2.2.2.1
  · -- Step invariants (`r < Δ`)
    intro r hr info
    have hr_lt : s₀ + r < τ := by omega
    have hBase_r := hBase (s₀ + r) (by omega)
    have hBase_r1 := hBase (s₀ + r + 1) (by omega)
    have hSt_r := hSt_base r hr.le
    have hSt_r1 := hSt_base (r + 1) hr
    have hStep_orig := hStep (s₀ + r) hr_lt
    have hStep_st : (st (r + 1)) = info.state := (hSt_step r hr).1
    have hm₀_r : (st r).m₀ = M := hm₀_eq r hr.le
    have hSc_r : (st r).S_cur.IsValid ∧ (st r).S_cur.V = (st r).cs.RF.R ∧
        (st r).S_cur.E =
          ((st r).activeComps.biUnion fun C => (actB C).biUnion fun b => ((st r).dyn (C, b)).H.E) ∪
            ((st r).activeComps.biUnion fun C => extraSet ((st r).cs.compSt C) ((st r).ts C)) ∪
            (st r).cs.crossEdges ∧
        (coreGraph (st r).cs.G (st r).cs.lsf).IsSubgraph (st r).S_cur := by
      have hr_ne : ¬ (s₀ + r = t ∧ s₀ < t) := by omega
      dsimp only [st, epochTreeSeq]
      simp only [hr_ne, ↓reduceIte]
      exact (hSc (s₀ + r) (by omega)).2
    have hSc_r1 : (st (r + 1)).S_cur.IsValid ∧ (st (r + 1)).S_cur.V = (st (r + 1)).cs.RF.R ∧
        (st (r + 1)).S_cur.E =
          ((st (r + 1)).activeComps.biUnion fun C => (actB C).biUnion fun b => ((st (r + 1)).dyn (C, b)).H.E) ∪
            ((st (r + 1)).activeComps.biUnion fun C => extraSet ((st (r + 1)).cs.compSt C) ((st (r + 1)).ts C)) ∪
            (st (r + 1)).cs.crossEdges ∧
        (coreGraph (st (r + 1)).cs.G (st (r + 1)).cs.lsf).IsSubgraph (st (r + 1)).S_cur := by
      dsimp only [st, epochTreeSeq]
      split_ifs with hcond
      · exact hcond.1 ▸ (hSc t htτ).1
      · exact (hSc (s₀ + (r + 1)) (by omega)).2
    have hAct_r : (st r).activeComps ⊆ components G₀ := by
      rw [hSt_r.activeComps]; exact hBase_r.2.2.2.2.2.2.2.2.2.2.1.2
    have hAct_r1 : (st (r + 1)).activeComps ⊆ components G₀ := by
      rw [hSt_r1.activeComps, show s₀ + (r + 1) = s₀ + r + 1 by omega]
      exact hBase_r1.2.2.2.2.2.2.2.2.2.2.1.2
    have hG₀_r : (st r).cs.G₀ = G₀ := by
      rw [hSt_r.cs, hBase_r.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hI_r : CompLSFInv C_lsst (D.ℓ 0) (st r).cs := by
      rw [hSt_r.cs]; exact hBase_r.2.2.2.2.2.2.2.2.1
    have hUnt_r : ∀ C ∈ components G₀, C ∉ (st r).activeComps →
        (st r).cs.compSt C = cs₀.compSt C ∧ (st r).ts C = ts₀ C := by
      intro C hC hna
      rw [hSt_r.cs, hSt_r.ts]
      exact hBase_r.2.2.2.2.2.2.2.2.2.2.2.1 C hC (hSt_r.activeComps ▸ hna)
    have hHist_r : ∀ C ∈ components G₀, LSFDerivedFrom (cs₀.compSt C) ((st r).cs.compSt C) := by
      intro C hC; rw [hSt_r.cs]; exact (hBase_r.2.2.2.2.2.2.2.2.2.2.2.2 C hC).1
    have hT_r : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) ((st r).cs.compSt C) ((st r).ts C) := by
      intro C hC; rw [hSt_r.cs, hSt_r.ts]; exact (hBase_r.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
    have hU_r : (st r).cs.G.BatchIsValid (D.U (s₀ + r + 1)) := by
      rw [hSt_r.cs]; exact hStep_orig.1
    have hDynB_r1 : ∀ C ∈ components G₀, ∀ b : ℤ,
        ((st (r + 1)).dyn (C, b)).G.IsSubgraph ((st (r + 1)).dyn (C, b)).H ∧
        ((st (r + 1)).dyn (C, b)).G.E ⊆ ((st (r + 1)).ts C).C.E := by
      intro C hC b
      have hd := (hDyn C hC b).2.2.2.2.2.2.2.1 (r + 1) hr
      have ht := (hT82 C hC b).1 (r + 1) hr
      have hsub : ((st (r + 1)).dyn (C, b)).G.IsSubgraph ((st (r + 1)).dyn (C, b)).H := by
        rw [hd.1]; exact ht.1
      have hge : ((st (r + 1)).dyn (C, b)).G.E ⊆ ((st (r + 1)).ts C).C.E := by
        rw [hd.2.2.2.1]; exact Finset.filter_subset _ _
      exact ⟨hsub, hge⟩
    have hAB_r : (st r).activeBuckets = actB := hSt_r.activeBuckets.trans hBase_r.2.2.2.2.2.1
    have hsp_stage := stepTreeCoreAux_stage_stepWith true sparsify hI₀ rfl hCov₀ (st r)
      (D.U (s₀ + r + 1)) actB hAB_r hG₀_r hI_r hAct_r hUnt_r hHist_r hT_r hU_r
      hSc_r.1 hSc_r.2.1 hSc_r.2.2.1 hSc_r.2.2.2
      (fun C hC b _ => by rw [← hStep_st]; exact (hDynB_r1 C hC b).1.2.1)
      (fun C hC b _ => by rw [← hStep_st]; exact (hDynB_r1 C hC b).2)
      (fun hUnil C _ b => by
        have hUb : (stepTreeCoreAuxWith true sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b) = [] := by
          dsimp only [stepTreeCoreAuxWith]; rw [hUnil]; rfl
        change DynSpanner.update ((st r).dyn (C, b))
          ((stepTreeCoreAuxWith true sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b))
          (sparsify (st r).m₀) = _
        rw [hUb, update_nil])
    dsimp only at hsp_stage
    have hCB_step : ∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update ((st r).dyn (C, b)) (info.U_b (C, b)) (sparsify (st r).m₀) ∧
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H ∧
        (info.U_b (C, b)).length ≤ (info.U_C C).length ∧
        (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ eH ∈ walkEdges (piTotal ((st (r + 1)).dyn (C, b)) eG),
          eH ∉ (info.stepOut (C, b)).D → eH ∈ walkEdges (piTotal ((st r).dyn (C, b)) eG)) ∧
        (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ e' : ℕ, e' ∉ (info.stepOut (C, b)).D →
          walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) e' ≤
            walkCount (piTotal ((st r).dyn (C, b)) eG) e') := by
      intro C hC b
      have hget : (Us_ep C b)[r]? = some (info.U_b (C, b)) := by
        dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hr]; rfl
      have hs82 := (hT82 C hC b).2.1 r hr _ hget
      have hd_prev := (hDyn C hC b).2.2.2.2.2.2.2.1 r hr.le
      have hd_cur := (hDyn C hC b).2.2.2.2.2.2.2.1 (r + 1) hr
      have hstep_dyn := (hDyn C hC b).2.2.2.2.2.2.2.2 r hr
      have hres_eq : DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
          (sparsify M) (Us_ep C b) r = info.stepOut (C, b) := hstep_dyn.1.symm
      beta_reduce at hs82
      rw [hres_eq] at hs82
      have hup_eq : info.stepOut (C, b) =
          DynSpanner.update ((st r).dyn (C, b)) (info.U_b (C, b)) (sparsify (st r).m₀) := by
        change DynSpanner.update ((st r).dyn (C, b)) (info.U_b (C, b)) (sparsify (st r).m₀) = _
        rfl
      have hwc : ∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ e' : ℕ, e' ∉ (info.stepOut (C, b)).D →
          walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) e' ≤
            walkCount (piTotal ((st r).dyn (C, b)) eG) e' := by
        have hlen_Us : (Us_ep C b).length = Δ := by simp [Us_ep]
        have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L :=
          le_trans (by omega) (two_le_phaseBase _ L)
        have hdC := hDyn C hC b
        have hbt := DynSpanner.batchTrace_walkCount_le (q := phaseBase ((Hb C b).n + splitB) L)
          hdC.1 hL hq1 (le_trans hdC.2.1 hM) hSp hdC.2.2.2.2.1 hdC.2.2.2.2.2.1 r (hlen_Us.symm ▸ hr) _ hget
        dsimp only at hbt
        rw [hres_eq] at hbt
        have hst1 : (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) := by
          rw [hStep_st]; rfl
        rw [hst1, ← hd_prev.1] at hbt
        intro eG heG e' hnD
        unfold walkCount
        exact Nat.cast_le.mpr (hbt eG heG e' hnD)
      refine ⟨hup_eq, by rw [hStep_st]; rfl, ?_, hstep_dyn.2.2, ?_, hwc⟩
      · rw [hd_prev.1, hd_cur.1]; exact hs82.2.2.2.1
      · intro eG heG eH heH hnD
        rw [hd_cur.1] at heG heH
        rw [hd_prev.1]
        exact hs82.2.2.2.2.2 eG heG eH heH hnD
    have hNew_eq := stepTreeCoreAux_newlyActive_eq_of_cs_act sparsify hSt_r.cs hSt_r.activeComps
      (D.U (s₀ + r + 1))
    have hNew_sub : info.newlyActive ⊆ components G₀ \ largeComps k G₀ := by
      intro C hC_mem
      rw [hNew_eq] at hC_mem
      have hC1 : C ∈ (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r + 1)).1.activeComps := by
        rw [hStep_orig.2.1.2.2.1]; exact Finset.mem_union_right _ hC_mem
      have hna : C ∉ (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.activeComps := by
        rw [hStep_orig.2.1.1, Finset.mem_sdiff] at hC_mem; exact hC_mem.2
      have hAct_orig1 := hBase_r1.2.2.2.2.2.2.2.2.2.2.1.2
      have hAct_orig0 := hBase_r.2.2.2.2.2.2.2.2.2.2.1.1
      exact Finset.mem_sdiff.mpr ⟨hAct_orig1 hC1, fun hL => hna (hAct_orig0 hL)⟩
    have hNew_card : info.newlyActive.card ≤ 2 * (D.U (s₀ + r + 1)).length := by
      rw [hNew_eq]; exact hStep_orig.2.1.2.2.2
    have hNew_n : ∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11 := by
      intro C hC_mem b
      have hC_comp := (Finset.mem_sdiff.mp (hNew_sub hC_mem)).1
      have hNL := (Finset.mem_sdiff.mp (hNew_sub hC_mem)).2
      rw [hNew_eq] at hC_mem
      have hna : C ∉ (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.activeComps := by
        rw [hStep_orig.2.1.1, Finset.mem_sdiff] at hC_mem; exact hC_mem.2
      have hts_orig : (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts C = ts₀ C :=
        (hBase_r.2.2.2.2.2.2.2.2.2.2.2.1 C hC_comp hna).2
      have hsub := ((hDyn C hC_comp b).2.2.2.2.2.2.2.1 r hr.le).2.2.2.2.1
      rw [hSt_r.ts, hts_orig] at hsub
      exact le_trans (Finset.card_le_card hsub) (hSmall C hC_comp hNL)
    have hLen_US := stepTreeCoreAux_US_lenWith true sparsify hI₀ rfl hCov₀ (st r)
      (D.U (s₀ + r + 1)) actB hG₀_r hI_r hAct_r (hStep_st ▸ hAct_r1) hUnt_r hHist_r hT_r hU_r
      hSc_r.2.2.1 (by rw [← hStep_st]; exact hSc_r1.2.2.1)
      hsp_stage.2.2.2.2.2.2.2.2
      (fun C hC b _ => by rw [← hStep_st]; exact (hCB_step C (hAct_r1 (hStep_st ▸ hC)) b).2.2.1)
    simp only [↓reduceIte] at hLen_US
    have hStep_st' : st (r + 1) =
        (stepTreeCoreAuxWith true sparsify (st r) (D.U (s₀ + r + 1))).state := hStep_st
    rw [← hStep_st'] at hsp_stage hLen_US
    rw [← hAB_r] at hLen_US
    exact ⟨hsp_stage.2.2.2.2.1, hsp_stage.2.2.2.2.2.1, fun hn => (hsp_stage.2.2.2.2.2.2.1 hn).1,
      hCB_step, hNew_sub, hNew_card, hNew_n, hLen_US⟩
  · intro C hC b
    exact (hT82 C hC b).2.2

end MinCostFlow.Chain

end
