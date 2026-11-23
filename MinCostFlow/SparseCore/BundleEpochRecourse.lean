module

public import MinCostFlow.SparseCore.BundleRecourseBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-epoch recourse and encoding-size bound for bundle graphs

Proves `bundleEpoch_recourse_and_enc_min` and `bundleEpoch_recourse_and_enc`: cumulative
recourse `∑ |U_S|` (with degree-free factor `bundleRecoursePerQ`), Lemma 2.1 batch encoding
size `∑ S.batchEnc U_S`, and exact vanishing when `q_ep = 0` over an arbitrary valid suffix
epoch `s₀ .. s₀ + Δ` of `BundleTreeState`.

This is the bundle-graph analogue of `SparseCoreEpochRecourse.lean`. It takes abstract epoch
invariants and a per-step bound on the total bundle-batch length, so it applies both to a fresh run
(`BundleRecourse.lean`) and to a restarted epoch.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

private lemma mem_batchDeletes_of_sdiff_applyBatch' (H : MGraph) (U : List Update) {e : ℕ}
    (he : e ∈ H.E) (he' : e ∉ (H.applyBatch U).E) : e ∈ batchDeletes U := by
  rw [mem_batchDeletes_iff]
  induction U generalizing H with
  | nil => exact absurd he he'
  | cons u rest ih =>
    by_cases hdel : u = .delete e
    · exact ⟨u, List.mem_cons_self, hdel⟩
    · have he1 : e ∈ (H.applyUpdate u).E := by
        cases u with
        | delete e' =>
          have hne : e ≠ e' := fun h => hdel (congrArg Update.delete h.symm)
          simpa [MGraph.applyUpdate, hne] using he
        | insert _ _ _ => simp [MGraph.applyUpdate, he]
        | split _ _ _ _ => exact he
      obtain ⟨u', hu', heq⟩ := ih (H.applyUpdate u) he1 he'
      exact ⟨u', List.mem_cons_of_mem _ hu', heq⟩

private lemma sum_Icc_shift_eq_sum_range' (s₀ Δ : ℕ) (f : ℕ → ℕ) :
    ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), f s = ∑ r ∈ Finset.range Δ, f (s₀ + r + 1) := by
  induction Δ with
  | zero => simp
  | succ d ih =>
    have hs1 : s₀ + (d + 1) = s₀ + d + 1 := by omega
    rw [hs1, Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Cumulative recourse `∑ |U_S|` and Lemma 2.1 encoding size over an arbitrary valid suffix
epoch `s₀ .. s₀ + Δ` (with `s₀ + Δ ≤ τ`) for a `BundleTreeState` sequence stepping via
`stepBundleTree`, using `n_eff = min (D.G 0).n ((D.G 0).m + 1)`. -/
lemma bundleEpoch_recourse_and_enc_min
    {C_lsst : ℝ} {L : ℕ} (_hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M τ : ℕ} (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End)
    (actB : Finset ℕ → Finset ℤ) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound)
    (hM_of_actB : ∀ C ∈ components (D.G 0), (actB C).Nonempty → 1 ≤ M)
    (s₀ Δ : ℕ) (_hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → BundleTreeState L) (U_S : ℕ → List Update)
    (Hb : Finset ℕ → ℤ → MGraph)
    (hHb_bounds : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (Hb C b).m ≤ M ∧ (Hb C b).n ≤ 2 * (Hb C b).m)
    (hst_step : ∀ r < Δ,
      st (r + 1) = (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).state)
    (hUS_step : ∀ r < Δ,
      U_S (r + 1) = (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).U_S)
    (hcs_inv : ∀ r ≤ Δ, CompLSFInv C_lsst (D.ℓ 0) (st r).cs ∧ (st r).cs.G₀ = D.G 0)
    (hBV_ep : ∀ r < Δ, (st r).cs.G.BatchIsValid (D.U (s₀ + r + 1)))
    (hactB_ep : ∀ r ≤ Δ, (st r).activeBuckets = actB)
    (hUB_sum_ep : ∀ r < Δ,
      ((components (D.G 0)).sum fun C => (actB C).sum fun b =>
        ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length) ≤
        B_bound * ((D.U (s₀ + r + 1)).length + 2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card))
    (hStage_ep : ∀ r ≤ Δ,
      (st r).S_cur.IsValid ∧
      (st r).activeComps ⊆ components (D.G 0) ∧
      ∀ C ∈ components (D.G 0), ∀ b : ℤ,
        ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤
          ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
            (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        ((piTotal ((st r).dyn (C, b))).length ((st r).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b)
    (hStep_ep : ∀ r < Δ,
      let info := stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))
      (st r).S_cur.BatchIsValid info.U_S ∧
      (st (r + 1)).S_cur = (st r).S_cur.applyBatch info.U_S ∧
      (D.U (s₀ + r + 1) = [] → info.U_S = []) ∧
      (∀ C ∈ components (D.G 0), ∀ b : ℤ,
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H) ∧
      info.newlyActive ⊆ components (D.G 0) \ largeComps k (D.G 0) ∧
      info.newlyActive.card ≤ 2 * (D.U (s₀ + r + 1)).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (st (r + 1)).activeComps.sum (fun C => (actB C).sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        info.newlyActive.sum (fun C => (actB C).sum fun b =>
          ((st r).dyn (C, b)).H.E.card) +
        7 * (D.U (s₀ + r + 1)).length +
        2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card +
        2 * info.D_total.card)
    (hT82_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := bundleSplitBudget k M
      let nMax_b := (Hb C b).n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let nRoot_b := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length : ℝ)
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b) :
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) ≤
      bundleRecoursePerQ L P_b M (min (D.G 0).n ((D.G 0).m + 1)) B_bound * (q_ep : ℝ) ∧
    ((∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) : ℕ) : ℝ) ≤
      20 * (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ)) *
        Real.log (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) + 2) ∧
    (q_ep = 0 →
      ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length = 0 ∧
      ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) = 0) := by
  classical
  intro q_ep
  set G₀ := D.G 0
  set n_eff := min G₀.n (G₀.m + 1)
  let stepI : ℕ → BundleTreeStepInfo L := fun r =>
    stepBundleTree sparsify (st r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))
  have hsum_step_eq : (∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) =
      ∑ r ∈ Finset.range Δ, (stepI r).U_S.length := by
    rw [← sum_range_nat_eq_sum_Icc_succ (fun r => (U_S r).length) Δ]
    refine Finset.sum_congr rfl fun r hr =>
      congrArg List.length (hUS_step r (Finset.mem_range.mp hr))
  have hq_nat : q_ep = ∑ r ∈ Finset.range Δ, (D.U (s₀ + r + 1)).length :=
    sum_Icc_shift_eq_sum_range' s₀ Δ (fun s => (D.U s).length)
  have hq_eq : ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) = (q_ep : ℝ) := by
    rw [hq_nat, Nat.cast_sum]
  have hR_step : ∀ r ∈ Finset.range Δ,
      (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) ≤
        112 * ((D.U (s₀ + r + 1)).length : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
    intro r hr
    have hr_lt : r < Δ := Finset.mem_range.mp hr
    have hI_r := (hcs_inv r (Nat.le_of_lt hr_lt)).1
    have hG0_r := (hcs_inv r (Nat.le_of_lt hr_lt)).2
    have hBV_r := hBV_ep r hr_lt
    have hcs1_eq : (st (r + 1)).cs = compLSFBatch (st r).cs (D.U (s₀ + r + 1)) := by
      rw [hst_step r hr_lt]; rfl
    have hsub_R : (st r).cs.RF.R ⊆ (st (r + 1)).cs.RF.R := by
      rw [hcs1_eq]; exact (compLSFBatch_decremental hI_r hBV_r).2
    have hcard_eq := Finset.card_sdiff_add_card_inter (st (r + 1)).cs.RF.R (st r).cs.RF.R
    rw [Finset.inter_eq_right.mpr hsub_R] at hcard_eq
    have hR_le := compLSF_R_sum_le_min hI_r hBV_r
    rw [← hcs1_eq, hG0_r] at hR_le
    have hdiff_R : (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) =
        ((st (r + 1)).cs.RF.R.card : ℝ) - ((st r).cs.RF.R.card : ℝ) := by
      have : (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) + ((st r).cs.RF.R.card : ℝ) =
          ((st (r + 1)).cs.RF.R.card : ℝ) := by exact_mod_cast hcard_eq
      linarith
    rw [hdiff_R]
    have hpush2 : ((2 * (D.U (s₀ + r + 1)).length : ℕ) : ℝ) =
        2 * ((D.U (s₀ + r + 1)).length : ℝ) := by
      push_cast; rfl
    rw [hpush2] at hR_le
    linarith
  have hR_sum : (∑ r ∈ Finset.range Δ,
      (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)) ≤
      112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
    calc ∑ r ∈ Finset.range Δ, (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)
        ≤ ∑ r ∈ Finset.range Δ,
            (112 * ((D.U (s₀ + r + 1)).length : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2) :=
            Finset.sum_le_sum hR_step
      _ = 112 * (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) *
            (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = 112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by rw [hq_eq]
  have hsum_UB :
      (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
        (((stepI r).U_B (C, b)).length : ℝ))) ≤
        (B_bound : ℝ) * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) := by
    have hstep_b : ∀ r ∈ Finset.range Δ,
        ((components G₀).sum fun C => (actB C).sum fun b =>
          (((stepI r).U_B (C, b)).length : ℝ)) ≤
        (B_bound : ℝ) * (((D.U (s₀ + r + 1)).length : ℝ) +
          2 * (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)) := fun r hr => by
      have h1 := hUB_sum_ep r (Finset.mem_range.mp hr)
      have h1r : (((components G₀).sum fun C => (actB C).sum fun b =>
          ((stepI r).U_B (C, b)).length : ℕ) : ℝ) ≤
          ((B_bound * ((D.U (s₀ + r + 1)).length +
            2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card) : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at h1r
      exact h1r
    calc ∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
            (((stepI r).U_B (C, b)).length : ℝ))
        ≤ ∑ r ∈ Finset.range Δ,
            ((B_bound : ℝ) * (((D.U (s₀ + r + 1)).length : ℝ) +
              2 * (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ))) :=
            Finset.sum_le_sum hstep_b
      _ = (B_bound : ℝ) * ((∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) +
            2 * (∑ r ∈ Finset.range Δ, (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ))) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (B_bound : ℝ) * ((q_ep : ℝ) +
            2 * (112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2)) := by
            rw [hq_eq]
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            linarith [hR_sum]
      _ ≤ (B_bound : ℝ) * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            unfold bundleUCRatio
            have hq_nn : (0 : ℝ) ≤ (q_ep : ℝ) := Nat.cast_nonneg _
            linarith
  have hSplitB : bundleSplitBudget k M ≤ 2 * (56 * M + 1) := bundleRec_splitBudget_le hk
  have hUH_D_cb : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ, (((stepI r).stepOut (C, b)).UH.length : ℝ)) ≤
        bundleBucketRecUH L P_b M *
          (∑ r ∈ Finset.range Δ, (((stepI r).U_B (C, b)).length : ℝ)) ∧
      (∑ r ∈ Finset.range Δ, (((stepI r).stepOut (C, b)).D.card : ℝ)) ≤
        bundleBucketRecD L P_b M *
          (∑ r ∈ Finset.range Δ, (((stepI r).U_B (C, b)).length : ℝ)) := by
    intro C hC b _
    set splitB := bundleSplitBudget k M
    have htb := hT82_ep C hC b
    have hnMax_le : (Hb C b).n + splitB ≤ bundleNMax M := by
      have hbm := (hHb_bounds C hC b).1
      have hbn := (hHb_bounds C hC b).2
      dsimp only [splitB] at hbm hbn ⊢
      unfold bundleNMax
      omega
    have hnr_le : ((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) ≤ bundleNRoot L M := by
      unfold bundleNRoot
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by positivity)
      exact_mod_cast (max_le_max_right 1 hnMax_le)
    have hbase_ge1 : (1 : ℝ) ≤ (((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2 := by
      linarith
    have hbase_nn : 0 ≤ 1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) := by
      linarith [Real.log_nonneg hbase_ge1]
    have hlog_le : Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) ≤
        Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) := by
      refine Real.log_le_log (by linarith) ?_
      have h1 : (((Hb C b).n + splitB : ℕ) : ℝ) ≤ (bundleNMax M : ℝ) := by exact_mod_cast hnMax_le
      have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hHb_bounds C hC b).1
      linarith
    have hlam_le : (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
        bundleLambdaS P_b M := by
      unfold bundleLambdaS
      exact pow_le_pow_left₀ hbase_nn (by linarith [hlog_le]) _
    have hK_nn := P_b.hK_s
    have hγ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
    have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hnr_nn : 0 ≤ ((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by positivity
    have hnr2_nn : 0 ≤ bundleNRoot L M := by unfold bundleNRoot; positivity
    have hbatch_nn : 0 ≤ ∑ r ∈ Finset.range Δ, (((stepI r).U_B (C, b)).length : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hcoeff_uh :
        2 + 12 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ *
            (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
          bundleBucketRecUH L P_b M := by
      unfold bundleBucketRecUH
      have h1 : 12 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ ≤
          12 * (L : ℝ) * bundleNRoot L M * P_b.K_s * P_b.γ_ℓ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnr_le (by positivity)) hK_nn) hγ_nn
      have h2 := mul_le_mul h1 hlam_le (pow_nonneg hbase_nn _) (by positivity)
      linarith
    have hcoeff_d :
        6 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ *
            (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) *
            (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
          bundleBucketRecD L P_b M := by
      unfold bundleBucketRecD
      have h3g : (0 : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1 := by positivity
      have h1 : 6 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ *
            (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) ≤
          6 * (L : ℝ) * bundleNRoot L M * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnr_le (by positivity)) hK_nn) hγ_nn) h3g
      exact mul_le_mul h1 hlam_le (pow_nonneg hbase_nn _) (by positivity)
    exact ⟨le_trans htb.1 (mul_le_mul_of_nonneg_right hcoeff_uh hbatch_nn),
      le_trans htb.2 (mul_le_mul_of_nonneg_right hcoeff_d hbatch_nn)⟩
  have hsum_buckets : ∀ (g : StepOut L → ℝ) (B_per : ℝ), 0 ≤ B_per →
      (∀ o : StepOut L, 0 ≤ g o) →
      (∀ C ∈ components G₀, ∀ b ∈ actB C,
        ∑ r ∈ Finset.range Δ, g ((stepI r).stepOut (C, b)) ≤
          B_per * ∑ r ∈ Finset.range Δ, (((stepI r).U_B (C, b)).length : ℝ)) →
      (∑ r ∈ Finset.range Δ, (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        g ((stepI r).stepOut (C, b))) ≤
        (B_bound : ℝ) * B_per * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) := by
    intro g B_per hB_nn hg_nn hg_cb
    have hAct_sub : ∀ r ∈ Finset.range Δ, (st (r + 1)).activeComps ⊆ components G₀ := fun r hr =>
      (hStage_ep (r + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hr))).2.1
    have hstep_sub :
        (∑ r ∈ Finset.range Δ, (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          g ((stepI r).stepOut (C, b))) ≤
        ∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
          g ((stepI r).stepOut (C, b))) :=
      Finset.sum_le_sum fun r hr =>
        Finset.sum_le_sum_of_subset_of_nonneg (hAct_sub r hr)
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => hg_nn _)
    have hcomm :
        (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
          g ((stepI r).stepOut (C, b)))) =
        (components G₀).sum fun C => (actB C).sum fun b =>
          ∑ r ∈ Finset.range Δ, g ((stepI r).stepOut (C, b)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
    have hC_sum :
        ((components G₀).sum fun C => (actB C).sum fun b =>
          ∑ r ∈ Finset.range Δ, g ((stepI r).stepOut (C, b))) ≤
        B_per * (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
          (((stepI r).U_B (C, b)).length : ℝ))) := by
      have hcomm2 :
          (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
            (((stepI r).U_B (C, b)).length : ℝ))) =
          (components G₀).sum fun C => (actB C).sum fun b =>
            ∑ r ∈ Finset.range Δ, (((stepI r).U_B (C, b)).length : ℝ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
      rw [hcomm2, Finset.mul_sum]
      refine Finset.sum_le_sum fun C hC => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b hb => hg_cb C hC b hb
    calc (∑ r ∈ Finset.range Δ, (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            g ((stepI r).stepOut (C, b)))
        ≤ B_per * (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
            (((stepI r).U_B (C, b)).length : ℝ))) :=
            le_trans hstep_sub (le_trans (le_of_eq hcomm) hC_sum)
      _ ≤ B_per * ((B_bound : ℝ) * (2 * bundleUCRatio n_eff * (q_ep : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum_UB hB_nn
      _ = (B_bound : ℝ) * B_per * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) := by ring
  have hUH_total :
      (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        (((stepI r).stepOut (C, b)).UH.length : ℝ))) ≤
        (B_bound : ℝ) * bundleBucketRecUH L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) :=
    hsum_buckets (fun o => (o.UH.length : ℝ)) (bundleBucketRecUH L P_b M)
      (bundleRec_BucketRec_nonneg L P_b M).1 (fun o => Nat.cast_nonneg _)
      fun C hC b hb => (hUH_D_cb C hC b hb).1
  have hD_total :
      (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        (((stepI r).stepOut (C, b)).D.card : ℝ))) ≤
        (B_bound : ℝ) * bundleBucketRecD L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) :=
    hsum_buckets (fun o => (o.D.card : ℝ)) (bundleBucketRecD L P_b M)
      (bundleRec_BucketRec_nonneg L P_b M).2.1 (fun o => Nat.cast_nonneg _)
      fun C hC b hb => (hUH_D_cb C hC b hb).2
  have hNew_total :
      (∑ r ∈ Finset.range Δ,
        ((stepI r).newlyActive.sum fun C => (actB C).sum fun b =>
          ((st r).dyn (C, b)).H.E.card : ℝ)) ≤
        22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (q_ep : ℝ) := by
    have hK_nn := P_b.hK_s
    have hγ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
    have hlam_nn := bundleRec_LambdaS_nonneg P_b M
    have hterm : ∀ r ∈ Finset.range Δ,
        ((stepI r).newlyActive.sum fun C => (actB C).sum fun b =>
          (((st r).dyn (C, b)).H.E.card : ℝ)) ≤
        22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M *
          ((D.U (s₀ + r + 1)).length : ℝ) := by
      intro r hr
      have hr_lt : r < Δ := Finset.mem_range.mp hr
      have hSt := hStep_ep r hr_lt
      have hSa := hStage_ep r (Nat.le_of_lt hr_lt)
      have hC_sum : ∀ C ∈ (stepI r).newlyActive,
          ((actB C).sum fun b => (((st r).dyn (C, b)).H.E.card : ℝ)) ≤
            11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M := by
        intro C hCN
        have hC : C ∈ components G₀ := (Finset.mem_sdiff.mp (hSt.2.2.2.2.1 hCN)).1
        have hb_le : ∀ b ∈ actB C,
            (((st r).dyn (C, b)).H.E.card : ℝ) ≤
              11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M := by
          intro b hb
          have hsp := hSa.2.2 C hC b
          have hgn11 : ((st r).dyn (C, b)).G.n ≤ 11 := hSt.2.2.2.2.2.2.1 C hCN b
          have hM_pos : 1 ≤ M := hM_of_actB C hC ⟨b, hb⟩
          have hgn_core : ((st r).dyn (C, b)).G.n ≤ bundleNMax M := by
            unfold bundleNMax; omega
          have harg_ge1 : (1 : ℝ) ≤ (((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2 := by
            linarith
          have harg_le : (((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2 ≤
              (bundleNMax M : ℝ) + (M : ℝ) + 2 := by
            have h1 : (((st r).dyn (C, b)).G.n : ℝ) ≤ (bundleNMax M : ℝ) := by exact_mod_cast hgn_core
            have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hHb_bounds C hC b).1
            linarith
          have hlog_nn : 0 ≤ 1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2) := by
            linarith [Real.log_nonneg harg_ge1]
          have hlam_le : (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
              bundleLambdaS P_b M := by
            unfold bundleLambdaS
            exact pow_le_pow_left₀ hlog_nn
              (add_le_add le_rfl (Real.log_le_log (by linarith) harg_le)) _
          have hgn_r : (((st r).dyn (C, b)).G.n : ℝ) ≤ 11 := by exact_mod_cast hgn11
          have hpre_le : ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ ≤
              11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ := by
            calc ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ
                ≤ ((L : ℝ) + 1) * P_b.K_s * 11 * P_b.γ_ℓ := by
                    refine mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hgn_r (by positivity)) hγ_nn
              _ = 11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ := by ring
          have hm_e : (((st r).dyn (C, b)).H.E.card : ℝ) = (((st r).dyn (C, b)).H.m : ℝ) := rfl
          rw [hm_e]
          exact le_trans hsp.2.1 (mul_le_mul hpre_le hlam_le (pow_nonneg hlog_nn _) (by positivity))
        calc (actB C).sum (fun b => (((st r).dyn (C, b)).H.E.card : ℝ))
            ≤ (actB C).sum (fun _ => 11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M) :=
                Finset.sum_le_sum hb_le
          _ = ((actB C).card : ℝ) * (11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M) := by
                simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (B_bound : ℝ) * (11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hB_bound C hC) (by positivity)
          _ = 11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M := by ring
      have hN_card : (((stepI r).newlyActive.card : ℝ)) ≤
          2 * ((D.U (s₀ + r + 1)).length : ℝ) := by exact_mod_cast hSt.2.2.2.2.2.1
      calc ((stepI r).newlyActive.sum _)
          ≤ (stepI r).newlyActive.sum
              (fun _ => 11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M) :=
              Finset.sum_le_sum hC_sum
        _ = ((stepI r).newlyActive.card : ℝ) *
              (11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * ((D.U (s₀ + r + 1)).length : ℝ)) *
              (11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M) :=
              mul_le_mul_of_nonneg_right hN_card (by positivity)
        _ = 22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M *
              ((D.U (s₀ + r + 1)).length : ℝ) := by ring
    calc ∑ r ∈ Finset.range Δ, _
        ≤ ∑ r ∈ Finset.range Δ,
            (22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M *
              ((D.U (s₀ + r + 1)).length : ℝ)) := Finset.sum_le_sum hterm
      _ = 22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M *
            ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) := by rw [← Finset.mul_sum]
      _ = 22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (q_ep : ℝ) := by
            rw [hq_eq]
  have hrec : ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) ≤
      bundleRecoursePerQ L P_b M n_eff B_bound * (q_ep : ℝ) := by
    rw [hsum_step_eq, Nat.cast_sum]
    have hD_tot_step : ∀ r ∈ Finset.range Δ,
        ((stepI r).D_total.card : ℝ) ≤
          ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            (((stepI r).stepOut (C, b)).D.card : ℝ)) +
          coreE82Len L P_b *
            ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
              (((stepI r).stepOut (C, b)).UH.length : ℝ)) := by
      intro r hr
      have hr_lt : r < Δ := Finset.mem_range.mp hr
      have hSt := hStep_ep r hr_lt
      have hSa1 := hStage_ep (r + 1) (Nat.succ_le_of_lt hr_lt)
      have hAB_r : (st r).activeBuckets = actB := hactB_ep r (Nat.le_of_lt hr_lt)
      let D_sp := (stepI r).state.activeComps.biUnion fun C =>
        ((st r).activeBuckets C).biUnion fun b => ((stepI r).stepOut (C, b)).D
      let A : Finset ℕ → ℤ → Finset ℕ := fun C b =>
        (((st r).dyn (C, b)).H.E ∩ ((stepI r).stepOut (C, b)).state.G.E) \
          ((stepI r).stepOut (C, b)).state.H.E
      let D_left := (stepI r).state.activeComps.biUnion fun C =>
        ((st r).activeBuckets C).biUnion fun b =>
          (A C b).biUnion fun e => walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)
      have hU_card : ((stepI r).D_total.card : ℝ) ≤ (D_sp.card : ℝ) + (D_left.card : ℝ) := by
        have hEq := bundleRec_stepBundleTree_D_total_eq sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))
        change ((stepI r).D_total.card : ℝ) ≤ _
        rw [hEq]
        exact_mod_cast Finset.card_union_le D_sp D_left
      have hDs_le : (D_sp.card : ℝ) ≤
          (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            (((stepI r).stepOut (C, b)).D.card : ℝ) := by
        have hbi : D_sp.card ≤
            (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
              ((stepI r).stepOut (C, b)).D.card := by
          dsimp only [D_sp]
          rw [hAB_r, ← hst_step r hr_lt]
          exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
        exact_mod_cast hbi
      have hDl_cb : ∀ C ∈ (st (r + 1)).activeComps, ∀ b ∈ actB C,
          (((A C b).biUnion fun e => walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ) ≤
            coreE82Len L P_b * (((stepI r).stepOut (C, b)).UH.length : ℝ) := by
        intro C hCA b _
        have hC : C ∈ components G₀ := hSa1.2.1 hCA
        have hCb := hSt.2.2.2.1 C hC b
        have hEmb := hSa1.2.2 C hC b
        have hA_sub : A C b ⊆ batchDeletes ((stepI r).stepOut (C, b)).UH := by
          intro e he
          rcases Finset.mem_sdiff.mp he with ⟨he1, heNot⟩
          have heHprev : e ∈ ((st r).dyn (C, b)).H.E := (Finset.mem_inter.mp he1).1
          rw [hCb.1, ← hCb.2] at heNot
          exact mem_batchDeletes_of_sdiff_applyBatch' _ _ heHprev heNot
        have hA_card : (A C b).card ≤ ((stepI r).stepOut (C, b)).UH.length :=
          le_trans (Finset.card_le_card hA_sub) (batchDeletes_card_le _)
        have hWalk_le : ∀ e ∈ A C b,
            ((walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ) ≤ coreE82Len L P_b := by
          intro e he
          have heG : e ∈ ((st (r + 1)).dyn (C, b)).G.E := by
            rw [← hCb.1]; exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).2
          have hlen1 : (walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card ≤
              (piTotal ((st (r + 1)).dyn (C, b)) e).length := by
            rw [hCb.1]
            simpa [walkEdges] using
              ((piTotal ((st (r + 1)).dyn (C, b)) e).map Prod.fst).toFinset_card_le
          have hlen2 : (piTotal ((st (r + 1)).dyn (C, b)) e).length ≤
              Embedding.length (piTotal ((st (r + 1)).dyn (C, b))) ((st (r + 1)).dyn (C, b)).G := by
            unfold Embedding.length
            exact Finset.le_sup (f := fun x => (piTotal ((st (r + 1)).dyn (C, b)) x).length) heG
          have hlen3 : (Embedding.length (piTotal ((st (r + 1)).dyn (C, b)))
              ((st (r + 1)).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b := hEmb.2.2
          exact le_trans (by exact_mod_cast le_trans hlen1 hlen2) hlen3
        have hbi : (((A C b).biUnion fun e => walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ) ≤
            ∑ e ∈ A C b, ((walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        calc (((A C b).biUnion fun e => walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ)
            ≤ ∑ e ∈ A C b, ((walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ) := hbi
          _ ≤ ∑ _ ∈ A C b, coreE82Len L P_b := Finset.sum_le_sum hWalk_le
          _ = ((A C b).card : ℝ) * coreE82Len L P_b := by simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (((stepI r).stepOut (C, b)).UH.length : ℝ) * coreE82Len L P_b :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hA_card)
                (bundleRec_BucketRec_nonneg L P_b M).2.2
          _ = coreE82Len L P_b * (((stepI r).stepOut (C, b)).UH.length : ℝ) := mul_comm _ _
      have hDl_le : (D_left.card : ℝ) ≤ coreE82Len L P_b *
          ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            (((stepI r).stepOut (C, b)).UH.length : ℝ)) := by
        have hbi0 : D_left.card ≤ (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            ((A C b).biUnion fun e => walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card := by
          dsimp only [D_left]
          rw [hAB_r, ← hst_step r hr_lt]
          exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
        calc (D_left.card : ℝ)
            ≤ (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                (((A C b).biUnion fun e =>
                  walkEdges (piTotal ((stepI r).stepOut (C, b)).state e)).card : ℝ) := by
                exact_mod_cast hbi0
          _ ≤ (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                coreE82Len L P_b * (((stepI r).stepOut (C, b)).UH.length : ℝ) :=
              Finset.sum_le_sum fun C hCA => Finset.sum_le_sum fun b hb => hDl_cb C hCA b hb
          _ = coreE82Len L P_b * ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                (((stepI r).stepOut (C, b)).UH.length : ℝ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun C _ => (Finset.mul_sum _ _ _).symm
      linarith
    have hD_tot_sum : (∑ r ∈ Finset.range Δ, ((stepI r).D_total.card : ℝ)) ≤
        (B_bound : ℝ) * bundleBucketRecD L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) +
        coreE82Len L P_b *
          ((B_bound : ℝ) * bundleBucketRecUH L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ))) := by
      have hs := Finset.sum_le_sum hD_tot_step
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
      exact le_trans hs (add_le_add hD_total
        (mul_le_mul_of_nonneg_left hUH_total (bundleRec_BucketRec_nonneg L P_b M).2.2))
    have hstep_b : ∑ r ∈ Finset.range Δ, ((stepI r).U_S.length : ℝ) ≤
        (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          (((stepI r).stepOut (C, b)).UH.length : ℝ))) +
        (∑ r ∈ Finset.range Δ,
          ((stepI r).newlyActive.sum fun C => (actB C).sum fun b =>
            ((st r).dyn (C, b)).H.E.card : ℝ)) +
        7 * (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) +
        2 * (∑ r ∈ Finset.range Δ, (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)) +
        2 * (∑ r ∈ Finset.range Δ, ((stepI r).D_total.card : ℝ)) := by
      calc ∑ r ∈ Finset.range Δ, ((stepI r).U_S.length : ℝ)
          ≤ ∑ r ∈ Finset.range Δ,
              (((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                (((stepI r).stepOut (C, b)).UH.length : ℝ)) +
              ((stepI r).newlyActive.sum fun C => (actB C).sum fun b =>
                ((st r).dyn (C, b)).H.E.card : ℝ) +
              7 * ((D.U (s₀ + r + 1)).length : ℝ) +
              2 * (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) +
              2 * ((stepI r).D_total.card : ℝ)) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have h1 := (hStep_ep r (Finset.mem_range.mp hr)).2.2.2.2.2.2.2
            exact_mod_cast h1
        _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcomb_rec :
        (B_bound : ℝ) * bundleBucketRecUH L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) +
          2 * ((B_bound : ℝ) * bundleBucketRecD L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) +
            coreE82Len L P_b *
              ((B_bound : ℝ) * bundleBucketRecUH L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)))) ≤
        (B_bound : ℝ) * ((3 + 2 * coreE82Len L P_b) * bundleBucketRecUH L P_b M +
          2 * bundleBucketRecD L P_b M) * (2 * bundleUCRatio n_eff) * (q_ep : ℝ) := by
      have hUH_nn := (bundleRec_BucketRec_nonneg L P_b M).1
      have huc := bundleRec_UCRatio_nonneg n_eff
      have hterm_nn : 0 ≤ (B_bound : ℝ) * bundleBucketRecUH L P_b M *
          (2 * bundleUCRatio n_eff * (q_ep : ℝ)) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hUH_nn)
          (mul_nonneg (mul_nonneg zero_le_two huc) (Nat.cast_nonneg _))
      nlinarith
    calc ∑ r ∈ Finset.range Δ, ((stepI r).U_S.length : ℝ)
        ≤ _ := hstep_b
      _ ≤ (B_bound : ℝ) * bundleBucketRecUH L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) +
            22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (q_ep : ℝ) +
            7 * (q_ep : ℝ) + 2 * (112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2) +
            2 * ((B_bound : ℝ) * bundleBucketRecD L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)) +
              coreE82Len L P_b *
                ((B_bound : ℝ) * bundleBucketRecUH L P_b M * (2 * bundleUCRatio n_eff * (q_ep : ℝ)))) := by
          rw [hq_eq]
          gcongr
      _ ≤ (B_bound : ℝ) * ((3 + 2 * coreE82Len L P_b) * bundleBucketRecUH L P_b M +
            2 * bundleBucketRecD L P_b M) * (2 * bundleUCRatio n_eff) * (q_ep : ℝ) +
            22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (q_ep : ℝ) +
            7 * (q_ep : ℝ) + 2 * (112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2) := by
          linarith [hcomb_rec]
      _ = bundleRecoursePerQ L P_b M n_eff B_bound * (q_ep : ℝ) := by
          unfold bundleRecoursePerQ; ring
  have hEnc : ((∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) : ℕ) : ℝ) ≤
      20 * (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ)) *
        Real.log (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) + 2) := by
    let U' : ℕ → List Update := fun r => if r = 0 then [] else U_S r
    have hval0 : (st 0).S_cur.IsValid := (hStage_ep 0 (Nat.zero_le Δ)).1
    have hval : ∀ r, 1 ≤ r → r ≤ Δ →
        (st (r - 1)).S_cur.BatchIsValid (U' r) ∧ (st r).S_cur = (st (r - 1)).S_cur.applyBatch (U' r) := by
      intro r hr1 hrΔ
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hn' := hStep_ep m (by omega)
      simp only at hn' ⊢
      have hU' : U' (m + 1) = (stepI m).U_S := by
        simp only [U', Nat.succ_ne_zero, ↓reduceIte]
        exact hUS_step m (by omega)
      rw [hU']
      exact ⟨hn'.1, hn'.2.1⟩
    have hL21 := MinCostFlow.Chain.lemma_2_1 (G := fun r => (st r).S_cur) (U := U') (τ := Δ) hval0 hval
    have hsum1 : ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U' r) =
        ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
      simp [U', hne0]
    have hsum2 : ∑ r ∈ Finset.Icc 1 Δ, (U' r).length = ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
      simp [U', hne0]
    rwa [hsum1, hsum2] at hL21
  have hZero : q_ep = 0 →
      ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length = 0 ∧
      ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) = 0 := by
    intro hq0
    rw [hq_nat] at hq0
    have hUS_nil : ∀ r, 1 ≤ r → r ≤ Δ → U_S r = [] := by
      intro r hr1 hrΔ
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hm_lt : m < Δ := by omega
      have hU0 : (D.U (s₀ + m + 1)).length = 0 :=
        Finset.sum_eq_zero_iff.mp hq0 m (Finset.mem_range.mpr hm_lt)
      have hnil := (hStep_ep m hm_lt).2.2.1 (List.eq_nil_of_length_eq_zero hU0)
      exact (hUS_step m hm_lt).trans hnil
    refine ⟨Finset.sum_eq_zero fun r hr => ?_, Finset.sum_eq_zero fun r hr => ?_⟩
    · rw [hUS_nil r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]; rfl
    · rw [hUS_nil r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]; rfl
  exact ⟨hrec, hEnc, hZero⟩

/-- Epoch recourse and encoding-size bound with `N` in place of `min (D.G 0).n ((D.G 0).m + 1)`. -/
lemma bundleEpoch_recourse_and_enc
    {C_lsst : ℝ} {L : ℕ} (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N τ : ℕ} (hk : 1 ≤ k) (D : DynamicInstance)
    (hN : (D.G 0).n ≤ N)
    (ord : ℕ → ℕ → List End)
    (actB : Finset ℕ → Finset ℤ) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound)
    (hM_of_actB : ∀ C ∈ components (D.G 0), (actB C).Nonempty → 1 ≤ M)
    (s₀ Δ : ℕ) (hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → BundleTreeState L) (U_S : ℕ → List Update)
    (Hb : Finset ℕ → ℤ → MGraph)
    (hHb_bounds : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (Hb C b).m ≤ M ∧ (Hb C b).n ≤ 2 * (Hb C b).m)
    (hst_step : ∀ r < Δ,
      st (r + 1) = (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).state)
    (hUS_step : ∀ r < Δ,
      U_S (r + 1) = (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).U_S)
    (hcs_inv : ∀ r ≤ Δ, CompLSFInv C_lsst (D.ℓ 0) (st r).cs ∧ (st r).cs.G₀ = D.G 0)
    (hBV_ep : ∀ r < Δ, (st r).cs.G.BatchIsValid (D.U (s₀ + r + 1)))
    (hactB_ep : ∀ r ≤ Δ, (st r).activeBuckets = actB)
    (hUB_sum_ep : ∀ r < Δ,
      ((components (D.G 0)).sum fun C => (actB C).sum fun b =>
        ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length) ≤
        B_bound * ((D.U (s₀ + r + 1)).length + 2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card))
    (hStage_ep : ∀ r ≤ Δ,
      (st r).S_cur.IsValid ∧
      (st r).activeComps ⊆ components (D.G 0) ∧
      ∀ C ∈ components (D.G 0), ∀ b : ℤ,
        ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤
          ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
            (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        ((piTotal ((st r).dyn (C, b))).length ((st r).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b)
    (hStep_ep : ∀ r < Δ,
      let info := stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))
      (st r).S_cur.BatchIsValid info.U_S ∧
      (st (r + 1)).S_cur = (st r).S_cur.applyBatch info.U_S ∧
      (D.U (s₀ + r + 1) = [] → info.U_S = []) ∧
      (∀ C ∈ components (D.G 0), ∀ b : ℤ,
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H) ∧
      info.newlyActive ⊆ components (D.G 0) \ largeComps k (D.G 0) ∧
      info.newlyActive.card ≤ 2 * (D.U (s₀ + r + 1)).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (st (r + 1)).activeComps.sum (fun C => (actB C).sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        info.newlyActive.sum (fun C => (actB C).sum fun b =>
          ((st r).dyn (C, b)).H.E.card) +
        7 * (D.U (s₀ + r + 1)).length +
        2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card +
        2 * info.D_total.card)
    (hT82_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := bundleSplitBudget k M
      let nMax_b := (Hb C b).n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let nRoot_b := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length : ℝ)
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b) :
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) ≤
      bundleRecoursePerQ L P_b M N B_bound * (q_ep : ℝ) ∧
    ((∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) : ℕ) : ℝ) ≤
      20 * (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ)) *
        Real.log (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) + 2) ∧
    (q_ep = 0 →
      ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length = 0 ∧
      ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) = 0) := by
  intro q_ep
  have h := bundleEpoch_recourse_and_enc_min hL P_b sparsify hk D ord actB B_bound hB_bound
    hM_of_actB s₀ Δ hsΔ st U_S Hb hHb_bounds hst_step hUS_step hcs_inv hBV_ep hactB_ep hUB_sum_ep
    hStage_ep hStep_ep hT82_ep
  exact ⟨le_trans h.1 (mul_le_mul_of_nonneg_right
    (bundleRec_PerQ_mono_n L P_b M (le_trans (min_le_left _ _) hN) B_bound)
    (Nat.cast_nonneg _)), h.2.1, h.2.2⟩

end

end MinCostFlow.SparseCore
