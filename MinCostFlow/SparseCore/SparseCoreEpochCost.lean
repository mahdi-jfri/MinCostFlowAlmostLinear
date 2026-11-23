module

public import MinCostFlow.SparseCore.SparseCoreRecourse

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime bound for `sparseCoreTool` (`treeRunSeq_cost_le`)

Bounds `(treeRunSeq oracle C_lsst L sparsify k D j τ).1.cost` unconditionally in terms of
`(m₀, n₀, Δ₀, dC, B_bound)` and `P_b : SparsifyParams`:
- Initialization + all lazy component initializations (`∑_C ∑_b initB.cost ≤ Õ(L m₀ + ... m₀)`
  via `all_buckets_sum_le` and `(hT82_cum ...).1, .2.1`, with no `splitB` blowup),
- Input batch cost (`q_τ`), quotient step cost (`∑_C |U_C| ≤ 2 coreUCRatio q_τ`), and spanner
  output recourse (`coreRecoursePerQ * q_τ`, with no `broken` term),
- Dynamic spanner update work (`90 * L * nRoot * ... * 20 * (m₀ + B_bound * ucBound) * log(...)`
  via Theorem 8.2's encoding bound and Lemma 2.1).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma initCB_cost_le
    {L : ℕ} {P_b : SparsifyParams} {m₀ : ℕ}
    {Hb : MGraph} {initB : DynSpanner.InitOut L}
    (hm_le_m0 : Hb.m ≤ m₀) (hn_le_2m : Hb.n ≤ 2 * Hb.m)
    (h82_Hm : (initB.state.H.m : ℝ) ≤
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ * (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s)
    (h82_cost : (initB.cost : ℝ) ≤
      P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t +
        (Hb.n : ℝ) + (Hb.m : ℝ) + (initB.state.H.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
        (L : ℝ) + 1) :
    (initB.cost : ℝ) ≤
      ((L : ℝ) + 1) +
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * coreLambda P_b m₀ + 3 + P_b.γ_ℓ +
          2 * P_b.K_s * P_b.γ_ℓ * coreLambda P_b m₀) * (Hb.m : ℝ) := by
  set Λ := coreLambda P_b m₀
  have hK_s := P_b.hK_s
  have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hn_le_2m₀ : Hb.n ≤ 2 * m₀ := le_trans hn_le_2m (Nat.mul_le_mul_left 2 hm_le_m0)
  have hn_le_core : Hb.n ≤ coreNMax m₀ := by unfold coreNMax; omega
  have hact_le_n : (activeSubgraph Hb).n ≤ Hb.n := by
    unfold MGraph.n activeSubgraph
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h1_n : (1 : ℝ) ≤ (Hb.n : ℝ) + (Hb.m : ℝ) + 2 := by linarith
  have hbase_n : 0 ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg h1_n]
  have hlog_n_le : (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s ≤ Λ := by
    have hsub : 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) ≤
        1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      refine add_le_add le_rfl (Real.log_le_log (by linarith) ?_)
      have h1 : (Hb.n : ℝ) ≤ (coreNMax m₀ : ℝ) := by exact_mod_cast hn_le_core
      have h2 : (Hb.m : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm_le_m0
      linarith
    calc (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s
        ≤ (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ P_b.p_s :=
            pow_le_pow_left₀ hbase_n hsub _
      _ ≤ Λ :=
            pow_le_pow_right₀
              (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)])
              (le_max_left _ _)
  have hnR : (Hb.n : ℝ) ≤ 2 * (Hb.m : ℝ) := by exact_mod_cast hn_le_2m
  have hinitH : (initB.state.H.m : ℝ) ≤ 2 * P_b.K_s * P_b.γ_ℓ * Λ * (Hb.m : ℝ) := by
    calc (initB.state.H.m : ℝ)
        ≤ P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ * (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s :=
            h82_Hm
      _ ≤ P_b.K_s * (2 * (Hb.m : ℝ)) * P_b.γ_ℓ * Λ := by
            have h1 : P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ ≤ P_b.K_s * (2 * (Hb.m : ℝ)) * P_b.γ_ℓ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnR hK_s) hγℓ_nn
            exact mul_le_mul h1 hlog_n_le (pow_nonneg hbase_n _) (by positivity)
      _ = 2 * P_b.K_s * P_b.γ_ℓ * Λ * (Hb.m : ℝ) := by ring
  have h1_act : (1 : ℝ) ≤ ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 := by linarith
  have hbase_act : 0 ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg h1_act]
  have hlog_act_le : (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t ≤ Λ := by
    have hsub : 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) ≤
        1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      refine add_le_add le_rfl (Real.log_le_log (by linarith) ?_)
      have h1 : ((activeSubgraph Hb).n : ℝ) ≤ (coreNMax m₀ : ℝ) := by
        exact_mod_cast le_trans hact_le_n hn_le_core
      have h2 : (Hb.m : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm_le_m0
      linarith
    calc (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t
        ≤ (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ P_b.p_t :=
            pow_le_pow_left₀ hbase_act hsub _
      _ ≤ Λ :=
            pow_le_pow_right₀
              (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)])
              (le_max_right _ _)
  have hactR : ((activeSubgraph Hb).n : ℝ) ≤ 2 * (Hb.m : ℝ) := by
    exact_mod_cast le_trans hact_le_n hn_le_2m
  have hpart1 :
      P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t ≤
        P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ * (Hb.m : ℝ) := by
    have hm_part : ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2 ≤
        (2 + P_b.γ_ℓ ^ 2) * (Hb.m : ℝ) := by linarith
    calc P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
            (1 + Real.log _) ^ P_b.p_t
        ≤ P_b.K_t * ((2 + P_b.γ_ℓ ^ 2) * (Hb.m : ℝ)) * Λ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm_part hK_t) hlog_act_le
              (pow_nonneg hbase_act _) (by positivity)
      _ = P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ * (Hb.m : ℝ) := by ring
  linarith [h82_cost, hpart1, hinitH]

lemma initBuckets_cost_sum_le
    {L : ℕ} {P_b : SparsifyParams} {m₀ : ℕ} {G₀ : MGraph}
    (actComps : Finset (Finset ℕ)) (hact_sub : actComps ⊆ components G₀)
    (actB : Finset ℕ → Finset ℤ)
    (Hb : Finset ℕ → ℤ → MGraph)
    (initCB : Finset ℕ → ℤ → DynSpanner.InitOut L)
    (hact_card : (components G₀).sum (fun C => (actB C).card) ≤ m₀)
    (hm_sum : (components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ m₀)
    (hn_2m : ∀ C ∈ components G₀, ∀ b ∈ actB C, (Hb C b).n ≤ 2 * (Hb C b).m)
    (h82_init : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((initCB C b).state.H.m : ℝ) ≤
        P_b.K_s * ((Hb C b).n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((Hb C b).n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
      ((initCB C b).cost : ℝ) ≤
        P_b.K_t * (((activeSubgraph (Hb C b)).n : ℝ) + ((Hb C b).m : ℝ) * P_b.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph (Hb C b)).n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_t +
          ((Hb C b).n : ℝ) + ((Hb C b).m : ℝ) + ((initCB C b).state.H.m : ℝ) +
          ((Hb C b).m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) :
    (actComps.sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ))) ≤
      ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * coreLambda P_b m₀ + 3 + P_b.γ_ℓ +
        2 * P_b.K_s * P_b.γ_ℓ * coreLambda P_b m₀) * (m₀ : ℝ) := by
  set Λ := coreLambda P_b m₀
  have hK_s := P_b.hK_s
  have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hΛ_ge1 : 1 ≤ Λ := coreLambda_ge_one P_b m₀
  have hΛ_nn : 0 ≤ Λ := by linarith
  have hC1 : 0 ≤ P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
      2 * P_b.K_s * P_b.γ_ℓ * Λ := by positivity
  have hsub : actComps.sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) ≤
      (components G₀).sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hact_sub
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hcb_le :
      ((components G₀).sum fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) ≤
      (components G₀).sum fun C => (actB C).sum fun b =>
        (((L : ℝ) + 1) +
          (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) *
            ((Hb C b).m : ℝ)) := by
    refine Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => ?_
    have hm_cb : (Hb C b).m ≤ m₀ := by
      calc (Hb C b).m ≤ (actB C).sum (fun b' => (Hb C b').m) :=
              Finset.single_le_sum (f := fun b' => (Hb C b').m) (fun _ _ => Nat.zero_le _) hb
        _ ≤ (components G₀).sum (fun C' => (actB C').sum fun b' => (Hb C' b').m) :=
              Finset.single_le_sum (f := fun C' => (actB C').sum fun b' => (Hb C' b').m)
                (fun _ _ => Nat.zero_le _) hC
        _ ≤ m₀ := hm_sum
    have hspec := h82_init C hC b hb
    exact initCB_cost_le hm_cb (hn_2m C hC b hb) hspec.1 hspec.2
  have hsum_eq :
      ((components G₀).sum fun C => (actB C).sum fun b =>
        (((L : ℝ) + 1) +
          (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) *
            ((Hb C b).m : ℝ))) =
      ((components G₀).sum fun C => ((actB C).card : ℝ)) * ((L : ℝ) + 1) +
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) *
          ((components G₀).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  have hcard_r : ((components G₀).sum fun C => ((actB C).card : ℝ)) ≤ (m₀ : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hact_card
  have hm_r : ((components G₀).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) ≤ (m₀ : ℝ) := by
    simp only [← Nat.cast_sum]
    exact_mod_cast hm_sum
  calc actComps.sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ))
      ≤ (components G₀).sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) := hsub
    _ ≤ _ := hcb_le
    _ = _ := hsum_eq
    _ ≤ (m₀ : ℝ) * ((L : ℝ) + 1) +
          (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) * (m₀ : ℝ) := by
          gcongr
    _ = _ := by ring

private lemma stepTreeCoreAux_U_C_eq_of_cs_ts {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {st₁ st₂ : TreeCoreState L} (hcs : st₁.cs = st₂.cs) (hts : st₁.ts = st₂.ts)
    (U : List Update) (C : Finset ℕ) :
    (stepTreeCoreAux sparsify st₁ U).U_C C = (stepTreeCoreAux sparsify st₂ U).U_C C := by
  dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith]
  rw [hcs, hts]

lemma epoch_U_C_sum_le_min
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j s₀ Δ : ℕ) (hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → TreeCoreState L)
    (hcs_s : ∀ r ≤ Δ, (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs)
    (hts_s : ∀ r ≤ Δ, (st r).ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts) :
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    ((components (D.G 0)).sum fun C => ∑ r ∈ Finset.range Δ,
      (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) ≤
      2 * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg * (q_ep : ℝ) := by
  intro q_ep
  obtain ⟨_, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hq_nat : q_ep = ∑ r ∈ Finset.range Δ, (D.U (s₀ + r + 1)).length := by
    have hshift : ∀ d, ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + d), (D.U s).length =
        ∑ r ∈ Finset.range d, (D.U (s₀ + r + 1)).length := fun d => by
      induction d with
      | zero => simp
      | succ d ih =>
        have hs1 : s₀ + (d + 1) = s₀ + d + 1 := by omega
        rw [hs1, Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    exact hshift Δ
  have hq_eq : ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) = (q_ep : ℝ) := by
    rw [hq_nat, Nat.cast_sum]
  rw [Finset.sum_comm]
  calc (∑ r ∈ Finset.range Δ, (components (D.G 0)).sum fun C =>
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))
      ≤ ∑ r ∈ Finset.range Δ, (2 * ((D.U (s₀ + r + 1)).length : ℝ) *
          coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hr_lt : r < Δ := Finset.mem_range.mp hr
          have hr_τ : s₀ + r < τ := by omega
          have hst_r := hStep (s₀ + r) hr_τ
          have hcs_r := hcs_s r (Nat.le_of_lt hr_lt)
          have hts_r := hts_s r (Nat.le_of_lt hr_lt)
          calc (components (D.G 0)).sum (fun C =>
                  (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))
              = (components (D.G 0)).sum (fun C =>
                  (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1
                    (D.U (s₀ + r + 1))).U_C C).length : ℝ)) := by
                  refine Finset.sum_congr rfl fun C _ => ?_
                  rw [stepTreeCoreAux_U_C_eq_of_cs_ts sparsify hcs_r hts_r]
            _ ≤ (components (D.G 0)).sum (fun C =>
                  (projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.G
                    ((treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.compSt C).G
                    (D.U (s₀ + r + 1)) : ℝ) * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg) :=
                  Finset.sum_le_sum fun C hC => by
                    dsimp only [coreUCRatio]
                    exact treeRunSeq_U_C_len_le_min oracle C_lsst L sparsify hLSST k M N τ hk D
                      hG₀ hV₀ hℓ₀ hD j (s₀ + r) hr_τ C hC
            _ = ((components (D.G 0)).sum fun C =>
                  (projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.G
                    ((treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.compSt C).G
                    (D.U (s₀ + r + 1)) : ℝ)) * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg := by
                  rw [← Finset.sum_mul]
            _ ≤ (2 * ((D.U (s₀ + r + 1)).length : ℝ)) * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg := by
                  refine mul_le_mul_of_nonneg_right ?_ (coreUCRatio_pos _ _)
                  exact_mod_cast hst_r.2.2.1
    _ = 2 * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg * (q_ep : ℝ) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hq_eq]; ring

lemma epoch_U_C_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j s₀ Δ : ℕ) (hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → TreeCoreState L)
    (hcs_s : ∀ r ≤ Δ, (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs)
    (hts_s : ∀ r ≤ Δ, (st r).ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts) :
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    ((components (D.G 0)).sum fun C => ∑ r ∈ Finset.range Δ,
      (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) ≤
      2 * coreUCRatio N (D.G 0).maxDeg * (q_ep : ℝ) := by
  intro q_ep
  have h := epoch_U_C_sum_le_min oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh
    j s₀ Δ hsΔ st hcs_s hts_s
  have hm := coreUCRatio_mono (le_trans (min_le_left (D.G 0).n ((D.G 0).m + 1)) hN) (D.G 0).maxDeg
  exact le_trans h (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

lemma epoch_dyn_cost_le_min
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j B_bound : ℕ)
    (hB_bound :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound)
    (s₀ Δ : ℕ) (hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → TreeCoreState L)
    (Hb : Finset ℕ → ℤ → MGraph)
    (Us_ep : Finset ℕ → ℤ → List (List Update))
    (hm_sum :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      (components (D.G 0)).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ M)
    (hHb_2m : ∀ C ∈ components (D.G 0), ∀ b : ℤ, (Hb C b).n ≤ 2 * (Hb C b).m)
    (hHb_deg :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let ts₀ := fun C => initTildeState (cs₀.compSt C)
      ∀ C ∈ components (D.G 0), ∀ b : ℤ, (Hb C b).maxDeg ≤ (ts₀ C).C.maxDeg)
    (hact_sub : ∀ r ≤ Δ, (st r).activeComps ⊆ components (D.G 0))
    (hcs_s : ∀ r ≤ Δ, (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs)
    (hts_s : ∀ r ≤ Δ, (st r).ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts)
    (hDyn_G_val0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ, ((st 0).dyn (C, b)).G.IsValid)
    (hDyn_G_m0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ, ((st 0).dyn (C, b)).G.m = (Hb C b).m)
    (hStep_ep : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let info := stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))
      ((st r).dyn (C, b)).G.BatchIsValid (info.U_b (C, b)) ∧
      ((st (r + 1)).dyn (C, b)).G = ((st r).dyn (C, b)).G.applyBatch (info.U_b (C, b)) ∧
      (info.U_b (C, b)).length ≤ (info.U_C C).length)
    (hRun_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      ∀ r ≤ Δ, ((st r).dyn (C, b)).G =
        (DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
          (sparsify M) (Us_ep C b) r).G)
    (hStepOut_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      ∀ r < Δ,
        (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b) =
          DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) (Us_ep C b) r)
    (hT82_cost : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      let nMax_b := (Hb C b).n + splitB
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
            (Us_ep C b) r).G.batchEnc
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ)
      (∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
          (Us_ep C b) r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let actB := fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
    let Δ₀ := (D.G 0).maxDeg
    let dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := coreLambda P_b M
    let uc_ep := 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_ep : ℝ)
    let ucBound := 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ)
    (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
      (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ))) ≤
      90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((dC : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * uc_ep) * Real.log ((M : ℝ) + ucBound + 2)) := by
  classical
  intro cs₀ ts₀ actB Δ₀ dC q_ep q_τ Λ uc_ep ucBound
  have hK_s := P_b.hK_s
  have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hγc_nn := P_b.hγ_c
  have hΛ_ge1 : 1 ≤ Λ := coreLambda_ge_one P_b M
  have hΛ_nn : 0 ≤ Λ := by linarith
  have hSplitB : Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ coreSplitMax M :=
    splitB_le_coreSplitMax_at hk (le_trans (Finset.card_pos.mpr hV₀) hN) hM
  have hUC_C : ∀ C ∈ components (D.G 0),
      0 ≤ ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hUC_comps :
      ((components (D.G 0)).sum fun C => ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) ≤ uc_ep := by
    have h1 := epoch_U_C_sum_le_min oracle C_lsst L sparsify hLSST k M N τ hk D
      hG₀ hV₀ hℓ₀ hD hN hThresh j s₀ Δ hsΔ st hcs_s hts_s
    have hmin : min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1) :=
      le_min (le_trans (min_le_left _ _) hN) (le_trans (min_le_right _ _) (Nat.succ_le_succ hM))
    have hmono := coreUCRatio_mono hmin Δ₀
    exact le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  have hq_le : q_ep ≤ q_τ := Finset.sum_le_sum_of_subset
    (fun s hs => Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hs).1; omega,
      by have := (Finset.mem_Icc.mp hs).2; omega⟩)
  have huc_le_ucBound : uc_ep ≤ ucBound :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hq_le)
      (mul_nonneg zero_le_two (coreUCRatio_pos (min N (M + 1)) Δ₀))
  have hcoeff_nn :
      0 ≤ 90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((dC : ℝ) + 1) * Λ := by
    unfold coreNRoot coreE_L
    positivity
  have hb_cost : ∀ C ∈ components (D.G 0), ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ)) ≤
        90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
          ((dC : ℝ) + 1) * Λ *
          (20 * (((Hb C b).m : ℝ) +
            (∑ r ∈ Finset.range Δ,
              (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))) *
            Real.log ((M : ℝ) + ucBound + 2)) := by
    intro C hC b hb
    set splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    set ucC := ∑ r ∈ Finset.range Δ,
      (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)
    have htb := hT82_cost C hC b
    dsimp only at htb
    have hm_le_m0 : (Hb C b).m ≤ M := by
      calc (Hb C b).m ≤ (actB C).sum (fun b' => (Hb C b').m) :=
              Finset.single_le_sum (f := fun b' => (Hb C b').m) (fun _ _ => Nat.zero_le _) hb
        _ ≤ (components (D.G 0)).sum (fun C' => (actB C').sum fun b' => (Hb C' b').m) :=
              Finset.single_le_sum (f := fun C' => (actB C').sum fun b' => (Hb C' b').m)
                (fun _ _ => Nat.zero_le _) hC
        _ ≤ M := hm_sum
    have hn_le_2m0 : (Hb C b).n ≤ 2 * M :=
      le_trans (hHb_2m C hC b) (Nat.mul_le_mul_left 2 hm_le_m0)
    have hnMax_le : (Hb C b).n + splitB ≤ coreNMax M := by
      unfold coreNMax
      exact Nat.add_le_add hn_le_2m0 hSplitB
    have hnRoot_le : ((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) ≤ coreNRoot L M := by
      unfold coreNRoot
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by positivity)
      exact_mod_cast max_le_max_right 1 hnMax_le
    have h1_b : (1 : ℝ) ≤ (((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2 := by linarith
    have hbase_b : 0 ≤ 1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) := by
      linarith [Real.log_nonneg h1_b]
    have hlog_sub_b : 1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) ≤
        1 + Real.log ((coreNMax M : ℝ) + (M : ℝ) + 2) := by
      refine add_le_add le_rfl (Real.log_le_log (by linarith) ?_)
      have h1 : (((Hb C b).n + splitB : ℕ) : ℝ) ≤ (coreNMax M : ℝ) := by exact_mod_cast hnMax_le
      have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_le_m0
      linarith
    have hΛ_le : (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^
        max P_b.p_s P_b.p_t ≤ Λ :=
      pow_le_pow_left₀ hbase_b hlog_sub_b _
    have hdeg_le : ((Hb C b).maxDeg : ℝ) + 1 ≤ (dC : ℝ) + 1 := by
      have hle : (Hb C b).maxDeg ≤ dC :=
        le_trans (hHb_deg C hC b) (Finset.le_sup (f := fun C => (ts₀ C).C.maxDeg) hC)
      exact_mod_cast Nat.succ_le_succ hle
    have hucC_le_uc : ucC ≤ ucBound :=
      le_trans (le_trans (Finset.single_le_sum (f := fun C => ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))
        (fun C' hC' => hUC_C C' hC') hC) hUC_comps) huc_le_ucBound
    have henc_b :
        (∑ r ∈ Finset.range Δ,
          ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L) (sparsify M)
            (Us_ep C b) r).G.batchEnc
            ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ)) ≤
          20 * (((Hb C b).m : ℝ) + ucC) * Real.log ((M : ℝ) + ucBound + 2) := by
      let Gb : ℕ → MGraph := fun r =>
        (DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L) (sparsify M)
          (Us_ep C b) r).G
      let Ub : ℕ → List Update := fun r =>
        if r = 0 then [] else
          (stepTreeCoreAux sparsify (st (r - 1)) (D.U (s₀ + (r - 1) + 1))).U_b (C, b)
      have hG0_b : (Gb 0).IsValid := by
        dsimp only [Gb]
        rw [← hRun_ep C hC b 0 (Nat.zero_le _)]
        exact hDyn_G_val0 C hC b
      have hG0_m : (Gb 0).m = (Hb C b).m := by
        dsimp only [Gb]
        rw [← hRun_ep C hC b 0 (Nat.zero_le _)]
        exact hDyn_G_m0 C hC b
      have hval_b : ∀ r, 1 ≤ r → r ≤ Δ →
          (Gb (r - 1)).BatchIsValid (Ub r) ∧ Gb r = (Gb (r - 1)).applyBatch (Ub r) := by
        intro r hr1 hrΔ
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
        have hUb_eq : Ub s.succ = (stepTreeCoreAux sparsify
            (st s) (D.U (s₀ + s + 1))).U_b (C, b) := by
          simp only [Ub, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
        rw [hUb_eq]
        have hs_step := hStep_ep s hrΔ C hC b
        have hdyn_s := hRun_ep C hC b s (Nat.le_of_lt hrΔ)
        have hdyn_s1 := hRun_ep C hC b (s + 1) hrΔ
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        dsimp only [Gb]
        rw [← hdyn_s, ← hdyn_s1]
        exact ⟨hs_step.1, hs_step.2.1⟩
      have hL21 := MinCostFlow.Chain.lemma_2_1 (G := Gb) (U := Ub) (τ := Δ) hG0_b hval_b
      have hsum_enc : ∑ r ∈ Finset.Icc 1 Δ, (Gb (r - 1)).batchEnc (Ub r) =
          ∑ r ∈ Finset.range Δ, (Gb r).batchEnc (Ub (r + 1)) := by
        rw [← sum_range_nat_eq_sum_Icc_succ (fun r => (Gb (r - 1)).batchEnc (Ub r)) Δ]
        simp only [Nat.add_sub_cancel]
      have hsum_len : ∑ r ∈ Finset.Icc 1 Δ, (Ub r).length =
          ∑ r ∈ Finset.range Δ, (Ub (r + 1)).length := by
        rw [← sum_range_nat_eq_sum_Icc_succ (fun r => (Ub r).length) Δ]
      have hlen_le : ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) ≤ ucC := by
        rw [hsum_len, Nat.cast_sum]
        refine Finset.sum_le_sum fun r hr => ?_
        have hUb_eq : Ub (r + 1) = (stepTreeCoreAux sparsify
            (st r) (D.U (s₀ + r + 1))).U_b (C, b) := by
          simp only [Ub, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Nat.add_sub_cancel]
        rw [hUb_eq]
        exact_mod_cast (hStep_ep r (Finset.mem_range.mp hr) C hC b).2.2
      rw [hG0_m, hsum_enc] at hL21
      have henc_eq : (∑ r ∈ Finset.range Δ, ((Gb r).batchEnc (Ub (r + 1)) : ℝ)) =
          ∑ r ∈ Finset.range Δ,
            ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L) (sparsify M)
              (Us_ep C b) r).G.batchEnc
              ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [Gb, Ub]
      rw [← henc_eq]
      rw [Nat.cast_sum] at hL21
      refine le_trans hL21 ?_
      have h1 : ((Hb C b).m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) ≤
          ((Hb C b).m : ℝ) + ucC := by linarith [hlen_le]
      have h2 : ((Hb C b).m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) + 2 ≤
          (M : ℝ) + ucBound + 2 := by
        have hmR : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_le_m0
        linarith [hlen_le, hucC_le_uc]
      have hlen_nn : 0 ≤ ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) := Nat.cast_nonneg _
      have hlog1 : 0 ≤ Real.log (((Hb C b).m : ℝ) +
          ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) + 2) :=
        Real.log_nonneg (by linarith)
      have hlog_le : Real.log (((Hb C b).m : ℝ) +
          ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) + 2) ≤
          Real.log ((M : ℝ) + ucBound + 2) :=
        Real.log_le_log (by linarith) h2
      have hm_nn : (0 : ℝ) ≤ ((Hb C b).m : ℝ) := Nat.cast_nonneg _
      refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hlog_le hlog1 (by linarith)
    have hcost_eq : ∀ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ) =
          ((DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L) (sparsify M)
            (Us_ep C b) r).cost : ℝ) := by
      intro r hr
      rw [hStepOut_ep C hC b r (Finset.mem_range.mp hr)]
    rw [Finset.sum_congr rfl hcost_eq]
    refine le_trans htb ?_
    have henc_nn : 0 ≤ ∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L) (sparsify M)
          (Us_ep C b) r).G.batchEnc
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hpart1 :
        90 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) *
            (P_b.K_t + P_b.K_s + 1) *
            (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
              P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
            (((Hb C b).maxDeg : ℝ) + 1) *
            (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^
              max P_b.p_s P_b.p_t ≤
          90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
            ((dC : ℝ) + 1) * Λ := by
      have hγc_nn' : 0 ≤ P_b.γ_c := by linarith
      have hNR_nn : 0 ≤ coreNRoot L M := Real.rpow_nonneg (Nat.cast_nonneg _) _
      unfold coreE_L
      refine mul_le_mul ?_ hΛ_le (pow_nonneg hbase_b _) (by positivity)
      refine mul_le_mul ?_ hdeg_le (by positivity) (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hnRoot_le (by positivity)
    exact mul_le_mul hpart1 henc_b henc_nn hcoeff_nn
  have hstep_sub :
      (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ))) ≤
      ∑ r ∈ Finset.range Δ, (components (D.G 0)).sum fun C => (actB C).sum fun b =>
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ) :=
    Finset.sum_le_sum fun r hr =>
      Finset.sum_le_sum_of_subset_of_nonneg (hact_sub (r + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hr)))
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hcomm :
      (∑ r ∈ Finset.range Δ, (components (D.G 0)).sum fun C => (actB C).sum fun b =>
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ)) =
      (components (D.G 0)).sum fun C => (actB C).sum fun b =>
        ∑ r ∈ Finset.range Δ,
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
  have hinner_sum :
      ((components (D.G 0)).sum fun C => (actB C).sum fun b =>
        (((Hb C b).m : ℝ) +
          ∑ r ∈ Finset.range Δ,
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))) ≤
        (M : ℝ) + (B_bound : ℝ) * uc_ep := by
    have hm_r : ((components (D.G 0)).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) ≤
        (M : ℝ) := by exact_mod_cast hm_sum
    have huc_B :
        ((components (D.G 0)).sum fun C => ((actB C).card : ℝ) * ∑ r ∈ Finset.range Δ,
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) ≤
        (B_bound : ℝ) * uc_ep := by
      calc _ ≤ (components (D.G 0)).sum (fun C => (B_bound : ℝ) * ∑ r ∈ Finset.range Δ,
              (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) :=
            Finset.sum_le_sum fun C hC =>
              mul_le_mul_of_nonneg_right (by exact_mod_cast hB_bound C hC) (hUC_C C hC)
        _ = (B_bound : ℝ) * (components (D.G 0)).sum (fun C => ∑ r ∈ Finset.range Δ,
              (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) := by
            rw [← Finset.mul_sum]
        _ ≤ (B_bound : ℝ) * uc_ep :=
            mul_le_mul_of_nonneg_left hUC_comps (Nat.cast_nonneg _)
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith [hm_r, huc_B]
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + ucBound + 2) := by
    refine Real.log_nonneg ?_
    have huc_nn : 0 ≤ ucBound := mul_nonneg (mul_nonneg zero_le_two (coreUCRatio_pos (min N (M + 1)) Δ₀))
      (Nat.cast_nonneg _)
    linarith [Nat.cast_nonneg (α := ℝ) M]
  calc _ ≤ _ := hstep_sub
    _ = _ := hcomm
    _ ≤ (components (D.G 0)).sum fun C => (actB C).sum fun b =>
          90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
            ((dC : ℝ) + 1) * Λ *
            (20 * (((Hb C b).m : ℝ) +
              ∑ r ∈ Finset.range Δ,
                (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) *
              Real.log ((M : ℝ) + ucBound + 2)) :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => hb_cost C hC b hb
    _ = 90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
          ((dC : ℝ) + 1) * Λ *
          (20 * ((components (D.G 0)).sum fun C => (actB C).sum fun b =>
            (((Hb C b).m : ℝ) +
              ∑ r ∈ Finset.range Δ,
                (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))) *
            Real.log ((M : ℝ) + ucBound + 2)) := by
          simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ _ := by
          gcongr


end

end MinCostFlow.SparseCore
