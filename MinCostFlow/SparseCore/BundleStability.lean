module

public import MinCostFlow.SparseCore.BundleStabilityItems124
import MinCostFlow.DynSpanner.WalkCount
import MinCostFlow.SparseCore.BundleStage
import MinCostFlow.SparseCore.BundleRunInv
import MinCostFlow.SparseCore.BundleSpannerMetrics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional full `WeakHiddenStable`, surviving embeddings, and no-reinsert for bundle graphs

Proves the bundle-graph analogues of `SparseCoreStability.lean` (paper Lemma 5.17, item 2, pages
23–24):
1. `bundleTreeState_seq_weakHiddenStable` and `bundleRunSeq_weakHiddenStable`: unconditional full
   `WeakHiddenStable` (all 4 clauses, with `Ψ_S` using `k` in place of `2 M`) using `buildUSOrd`'s
   `D_total` reinsertion together with `DynSpanner.batchTrace_walkCount_le`.
2. `bundleCore_embedsSurviving_at` and `bundleCore_embedsSurviving`: surviving edges in `S_cur`
   always embed as `[(e, true)]`.
3. `bundleCore_noReinsert_step_at` and `bundleCore_noReinsert_step`: unconditional surviving-edge
   insertion propagation for `sparseCoreBundleTool`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Unconditional full `WeakHiddenStable` over an arbitrary suffix epoch -/

private lemma bundle_passCoreW_sum_filter (lsf : LSF) (emb : Embedding) (G : MGraph)
    (w : ℕ → ℝ) (e' : ℕ) :
    ∑ e ∈ (coreGraph G lsf).E, lsf.wstr e * w e * walkCount (emb e) e' =
      ∑ e ∈ (coreGraph G lsf).E.filter (fun e => e' ∈ walkEdges (emb e)),
        lsf.wstr e * w e * walkCount (emb e) e' := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with hew
  · rfl
  · rw [walkCount_eq_zero_of_not_mem hew, mul_zero]

/-- Unconditional full `WeakHiddenStable` (all 4 clauses) over an arbitrary suffix epoch
`s₀ .. s₀ + Δ` (with `s₀ + Δ ≤ τ`) for any state sequence `st : ℕ → BundleTreeState L` whose
`.cs` agrees with `bundleRunSeqWith`, whose steps evolve via `stepBundleTree`, and whose `bun`/`dyn`
buckets satisfy single-step backward `walkEdges`/`walkCount` preservation. -/
theorem bundleTreeState_seq_weakHiddenStable_with
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (s₀ Δ : ℕ) (hsτ : s₀ + Δ ≤ τ)
    (st : ℕ → BundleTreeState L)
    (D' : DynamicInstance) (c' w' : ℕ → ℕ → ℝ)
    (hD'_G : ∀ r ≤ Δ, D'.G r = (st r).S_cur)
    (hD'_U : ∀ r < Δ, D'.U (r + 1) =
      (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).U_S)
    (hD'_ℓ : ∀ r ≤ Δ, D'.ℓ r = coreLen (st r).cs.lsf (D.ℓ (s₀ + r)))
    (hc' : ∀ r ≤ Δ, c' r = passSparseCoreC (coreGraph (D.G (s₀ + r)) (st r).cs.lsf)
      (st r).emb (passCoreC (c (s₀ + r))))
    (hw' : ∀ r ≤ Δ, w' r = passSparseCoreW (coreGraph (D.G (s₀ + r)) (st r).cs.lsf)
      (st r).emb (passCoreW (st r).cs.lsf (w (s₀ + r))))
    (hst_step : ∀ r < Δ, st (r + 1) =
      (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).state)
    (hcs_s : ∀ r ≤ Δ, (st r).cs =
      (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s₀ + r)).1.cs)
    (hI_s : ∀ r ≤ Δ, CompLSFInv C_lsst (D.ℓ 0) (st r).cs)
    (hG₀_s : ∀ r ≤ Δ, (st r).cs.G₀ = D.G 0)
    (hG_s : ∀ r ≤ Δ, (st r).cs.G = D.G (s₀ + r))
    (hAct_s : ∀ r ≤ Δ, (st r).activeComps ⊆ components (D.G 0))
    (hS_E : ∀ r ≤ Δ, (st r).S_cur.E =
      ((st r).activeComps.biUnion fun C => ((st r).activeBuckets C).biUnion fun b =>
          ((st r).dyn (C, b)).H.E) ∪
        ((st r).activeComps.biUnion fun C => (st r).extraEdges C) ∪
        (st r).cs.crossEdges)
    (hSp_metrics : ∀ r ≤ Δ,
      (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).IsSubgraph (st r).S_cur ∧
      (st r).emb.IsEmbedding (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) (st r).S_cur ∧
      (∀ e ∈ (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).E, ∀ e' ∈ walkEdges ((st r).emb e),
        approx2 (coreLen (st r).cs.lsf (D.ℓ (s₀ + r)) e)
          (coreLen (st r).cs.lsf (D.ℓ (s₀ + r)) e')) ∧
      ((st r).emb.length (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
      (st r).emb.econg (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) (st r).S_cur
        (fun _ => 1) (fun _ => 1) ≤ 1 + coreE82Cong L P_b * (k : ℝ))
    (hBun_s : ∀ r (hr : r ≤ Δ), ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (∀ (ρ : Rotation (st r).cs.G), ρ.order = ord (s₀ + r) →
        ((st r).bun (C, b)).IsPartition
          (coreRotation (L := (st r).cs.lsf) ρ (hI_s r hr).hG_val
            (compLSF_RF_isRSF (hI_s r hr))) (st r).k) ∧
      (∀ x ∈ ((st r).bun (C, b)).vertices,
        ((st r).bun (C, b)).parent x ∈ ((st r).cs.compSt C).R) ∧
      Disjoint ((st r).bun (C, b)).edges (st r).cs.crossEdges ∧
      GraphEq ((st r).dyn (C, b)).G ((st r).bun (C, b)).graph ∧
      ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
      (piTotal ((st r).dyn (C, b))).IsEmbedding ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H)
    (hBun_disj : ∀ r ≤ Δ, ∀ C₁ ∈ components (D.G 0), ∀ C₂ ∈ components (D.G 0), ∀ b₁ b₂ : ℤ,
      ∀ x, x ∈ ((st r).bun (C₁, b₁)).edges → x ∈ ((st r).bun (C₂, b₂)).edges →
        C₁ = C₂ ∧ b₁ = b₂)
    (hBun_step : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((st (r + 1)).bun (C, b)).edges ⊆ ((st r).bun (C, b)).edges ∧
      Disjoint ((st (r + 1)).bun (C, b)).edges (batchDeletes (D.U (s₀ + r + 1))))
    (hDyn_step : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let stepOut := (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)
      stepOut = update ((st r).dyn (C, b))
        ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b))
        (sparsify (st r).m₀) ∧
      stepOut.state = (st (r + 1)).dyn (C, b) ∧
      (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E,
        ∀ eH ∈ walkEdges (piTotal ((st (r + 1)).dyn (C, b)) eG),
          eH ∉ stepOut.D → eH ∈ walkEdges (piTotal ((st r).dyn (C, b)) eG)) ∧
      (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ x : ℕ,
        x ∉ stepOut.D →
        walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) x ≤
          walkCount (piTotal ((st r).dyn (C, b)) eG) x)) :
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (k : ℝ)) * coreE82Len L P_b * σ_top + 2)
    WeakHiddenStable D' Δ Ψ_S c' w' := by
  intro σ_top Ψ_S t ht
  have hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e := fun s hs e he =>
    ((hWeak s hs).2.2.2 e he).2.2.1
  have hG_lsf := bundleRunSeqWith_lsf_guarantees_branch lsfInit C_lsst L sparsify
    k M N τ hk D hG₀ hV₀ hD hℓ hLen ord hInit
  obtain ⟨ρ_all, hρ_all, _⟩ := hOrd
  have hL_holds : ∀ r (hr : r ≤ Δ),
      (st r).cs.lsf.Holds (D.G (s₀ + r)) (D.ℓ (s₀ + r))
        (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G (s₀ + r)).n : ℝ) + 2)) ^ 6) := by
    intro r hr
    rw [hcs_s r hr]
    exact (hG_lsf.1 (s₀ + r) (by omega)).1
  have hRF_sub : ∀ r (hr : r ≤ Δ), (D.G (s₀ + r)).IsSubgraph (st r).cs.RF.F := by
    intro r hr
    rw [hcs_s r hr]
    exact (hG_lsf.1 (s₀ + r) (by omega)).2
  have hSpM := hSp_metrics t ht
  have h124 := bundleTreeState_weakHidden_items124 C_lsst L hL P_b k τ hk D hG₀ hD Ψ c w hWeak
    (s₀ + t) (by omega) (st t) (hRF_sub t ht) (hL_holds t ht) hSpM.1 hSpM.2.1 hSpM.2.2.1
    hSpM.2.2.2.1 hSpM.2.2.2.2
  dsimp only [WeakHiddenStableAt]
  rw [hD'_G t ht, hD'_ℓ t ht, hc' t ht, hw' t ht]
  refine ⟨h124.1, h124.2.1, fun e' he' t' ht't hNotIns => ?_, h124.2.2⟩
  let A : ℕ → Finset ℕ := fun r =>
    (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).E.filter (fun e => e' ∈ walkEdges ((st r).emb e))
  have hBack : ∀ m ≤ t - t',
      let r := t - m
      e' ∈ (st r).S_cur.E ∧
      A t ⊆ A r ∧
      (∀ e ∈ A t,
        (st t).cs.lsf.wstr e = (st r).cs.lsf.wstr e ∧
        walkCount ((st t).emb e) e' ≤ walkCount ((st r).emb e) e' ∧
        ∀ q, s₀ + r < q → q ≤ s₀ + t → ∀ u ∈ D.U q, ¬ u.Inserts e) := by
    intro m
    induction m with
    | zero =>
      intro _
      dsimp only [Nat.sub_zero]
      exact ⟨he', Finset.Subset.rfl, fun _ _ => ⟨rfl, le_rfl, fun _ h1 _ => absurd h1 (by omega)⟩⟩
    | succ m ih =>
      intro hm1
      have hm : m ≤ t - t' := Nat.le_of_succ_le hm1
      obtain ⟨he'_r1, hSub_r1, hw_r1⟩ := ih hm
      set s := t - (m + 1)
      have hs1_eq : t - m = s + 1 := by omega
      rw [hs1_eq] at he'_r1 hSub_r1 hw_r1
      have hs_lt_Δ : s < Δ := by omega
      have hs1_le_Δ : s + 1 ≤ Δ := by omega
      have hs_le_Δ : s ≤ Δ := Nat.le_of_lt hs_lt_Δ
      have hs_lt : s₀ + s < τ := by omega
      have hNoIns_s1 : ∀ u ∈ (stepBundleTree sparsify (st s) (D.U (s₀ + s + 1))
          (ord (s₀ + s)) (ord (s₀ + s + 1))).U_S, ¬ u.Inserts e' := by
        have h := hNotIns (s + 1) (by omega) (by omega)
        rwa [hD'_U s hs_lt_Δ] at h
      have hBV_U : (D.G (s₀ + s)).BatchIsValid (D.U (s₀ + s + 1)) := by
        have hDs := (hD (s₀ + s + 1) (Nat.succ_pos _) (by omega)).1
        simpa [Nat.add_sub_cancel] using hDs
      have hSp_sub_s : (coreGraph (st s).cs.G (st s).cs.lsf).IsSubgraph (st s).S_cur := by
        rw [hG_s s hs_le_Δ]; exact (hSp_metrics s hs_le_Δ).1
      let ρ_s : Rotation (st s).cs.G := (hG_s s hs_le_Δ).symm ▸ ρ_all (s₀ + s)
      have hρ_s : ρ_s.order = ord (s₀ + s) := by
        have hcast : ∀ {G₁ G₂ : MGraph} (heq : G₁ = G₂) (ρ : Rotation G₁),
            (heq ▸ ρ : Rotation G₂).order = ρ.order := fun heq _ => by cases heq; rfl
        exact (hcast (hG_s s hs_le_Δ).symm (ρ_all (s₀ + s))).trans (hρ_all (s₀ + s) (by omega))
      let ρ_s1 : Rotation (st (s + 1)).cs.G :=
        (hG_s (s + 1) hs1_le_Δ).symm ▸ ρ_all (s₀ + (s + 1))
      have hρ_s1 : ρ_s1.order = ord (s₀ + s + 1) := by
        have hcast : ∀ {G₁ G₂ : MGraph} (heq : G₁ = G₂) (ρ : Rotation G₁),
            (heq ▸ ρ : Rotation G₂).order = ρ.order := fun heq _ => by cases heq; rfl
        have h1 := (hcast (hG_s (s + 1) hs1_le_Δ).symm (ρ_all (s₀ + (s + 1)))).trans
          (hρ_all (s₀ + (s + 1)) (by omega))
        simpa [Nat.add_assoc] using h1
      obtain ⟨he'_s, _, hback_e⟩ := bundleWeakHidden_step_backward_core sparsify D ord
        (s := s₀ + s) (st s) (st (s + 1)) (hst_step s hs_lt_Δ)
        (hI_s s hs_le_Δ) (hI_s (s + 1) hs1_le_Δ)
        (hG₀_s s hs_le_Δ) (hG₀_s (s + 1) hs1_le_Δ)
        (hG_s s hs_le_Δ) hBV_U ρ_s hρ_s ρ_s1 hρ_s1
        (hAct_s s hs_le_Δ) (hAct_s (s + 1) hs1_le_Δ)
        hSp_sub_s (hS_E s hs_le_Δ) (hS_E (s + 1) hs1_le_Δ)
        (fun C hC b =>
          let hb := hBun_s s hs_le_Δ C hC b
          ⟨hb.1 ρ_s hρ_s, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1⟩)
        (fun C hC b =>
          let hb := hBun_s (s + 1) hs1_le_Δ C hC b
          ⟨hb.1 ρ_s1 (by simpa [Nat.add_assoc] using hρ_s1), hb.2.1, hb.2.2.1,
            hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2⟩)
        (hBun_disj s hs_le_Δ) (hBun_step s hs_lt_Δ) (hDyn_step s hs_lt_Δ)
        he'_r1 hNoIns_s1
      refine ⟨he'_s, fun e heAt => ?_, fun e heAt => ?_⟩
      · have he_s1 := hSub_r1 heAt
        rw [Finset.mem_filter] at he_s1 ⊢
        have hb := hback_e e (by simpa [Nat.add_assoc] using he_s1.1) he_s1.2
        exact ⟨hb.1, hb.2.1⟩
      · have he_s1 := hSub_r1 heAt
        rw [Finset.mem_filter] at he_s1
        have heC1' : e ∈ (coreGraph (D.G (s₀ + s + 1)) (st (s + 1)).cs.lsf).E := by
          simpa [Nat.add_assoc] using he_s1.1
        have hb := hback_e e heC1' he_s1.2
        have hw_eq := (hG_lsf.2 (s₀ + s + 1) (Nat.succ_pos _) (by omega)).2 e
          (Finset.mem_sdiff.mp heC1').1 (Finset.mem_sdiff.mp hb.1).1 hb.2.2.2
        rw [Nat.add_sub_cancel] at hw_eq
        have hw_eq' : (st (s + 1)).cs.lsf.wstr e = (st s).cs.lsf.wstr e := by
          rw [hcs_s (s + 1) hs1_le_Δ, hcs_s s hs_le_Δ]
          simpa [Nat.add_assoc] using hw_eq
        obtain ⟨hw_t, hwc_t, hni_t⟩ := hw_r1 e heAt
        refine ⟨hw_t.trans hw_eq', le_trans hwc_t hb.2.2.1, fun q hq1 hqt u hu => ?_⟩
        rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hq1) with rfl | hgt
        · exact hb.2.2.2 u hu
        · exact hni_t q (by omega) hqt u hu
  obtain ⟨_, hSub_t', hEdge_t'⟩ := hBack (t - t') le_rfl
  have hrr : t - (t - t') = t' := by omega
  rw [hrr] at hSub_t' hEdge_t'
  set st_t := st t
  set st_t' := st t'
  have hGt_W : w' t e' =
      2 * ∑ e ∈ A t, st_t.cs.lsf.wstr e * w (s₀ + t) e * walkCount (st_t.emb e) e' := by
    rw [hw' t ht]; dsimp only [passSparseCoreW, passCoreW]
    exact congrArg (2 * ·)
      (bundle_passCoreW_sum_filter st_t.cs.lsf st_t.emb (D.G (s₀ + t)) (w (s₀ + t)) e')
  have hGt'_W : w' t' e' =
      2 * ∑ e ∈ A t', st_t'.cs.lsf.wstr e * w (s₀ + t') e * walkCount (st_t'.emb e) e' := by
    rw [hw' t' (le_trans ht't ht)]; dsimp only [passSparseCoreW, passCoreW]
    exact congrArg (2 * ·)
      (bundle_passCoreW_sum_filter st_t'.cs.lsf st_t'.emb (D.G (s₀ + t')) (w (s₀ + t')) e')
  have hwstr_nn : ∀ e ∈ A t', 0 ≤ st_t'.cs.lsf.wstr e := by
    intro e he
    have heGt' : e ∈ (D.G (s₀ + t')).E := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
    have h1 := one_le_stretch (hRF_sub t' (le_trans ht't ht))
      (fun y hy => le_of_lt (hℓ (s₀ + t') (by omega) y hy)) heGt'
    have hH := ((hL_holds t' (le_trans ht't ht)).2.2.2 e heGt').1
    change st_t'.cs.RF.stretch (D.G (s₀ + t')) (D.ℓ (s₀ + t')) e ≤ _ at hH; linarith
  have hsub_A :
      ∑ e ∈ A t, st_t.cs.lsf.wstr e * w (s₀ + t) e * walkCount (st_t.emb e) e' ≤
        2 * ∑ e ∈ A t', st_t'.cs.lsf.wstr e * w (s₀ + t') e * walkCount (st_t'.emb e) e' := by
    rw [Finset.mul_sum]
    calc ∑ e ∈ A t, st_t.cs.lsf.wstr e * w (s₀ + t) e * walkCount (st_t.emb e) e'
        ≤ ∑ e ∈ A t, 2 * (st_t'.cs.lsf.wstr e * w (s₀ + t') e * walkCount (st_t'.emb e) e') := by
          refine Finset.sum_le_sum fun e he => ?_
          obtain ⟨hw_eq, hwc_le, hnotIns_e⟩ := hEdge_t' e he
          have heGt : e ∈ (D.G (s₀ + t)).E := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
          have hw_bound : w (s₀ + t) e ≤ 2 * w (s₀ + t') e :=
            (hWeak (s₀ + t) (by omega)).2.2.1 e heGt (s₀ + t') (by omega) hnotIns_e
          have hw_nn := hwstr_nn e (hSub_t' he)
          have hwt'_pos : 0 ≤ w (s₀ + t') e := by
            have heGt' : e ∈ (D.G (s₀ + t')).E :=
              (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hSub_t' he)).1).1
            exact le_of_lt ((hWeak (s₀ + t') (by omega)).2.2.2 e heGt').1
          have hwc_nn : 0 ≤ walkCount (st_t.emb e) e' := walkCount_nonneg _ _
          have hwe : st_t.cs.lsf.wstr e = st_t'.cs.lsf.wstr e := hw_eq
          rw [hwe]
          calc st_t'.cs.lsf.wstr e * w (s₀ + t) e * walkCount (st_t.emb e) e'
              ≤ st_t'.cs.lsf.wstr e * (2 * w (s₀ + t') e) * walkCount (st_t.emb e) e' :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hw_bound hw_nn) hwc_nn
            _ ≤ st_t'.cs.lsf.wstr e * (2 * w (s₀ + t') e) * walkCount (st_t'.emb e) e' :=
                  mul_le_mul_of_nonneg_left hwc_le (by positivity)
            _ = 2 * (st_t'.cs.lsf.wstr e * w (s₀ + t') e * walkCount (st_t'.emb e) e') := by ring
      _ ≤ ∑ e ∈ A t', 2 * (st_t'.cs.lsf.wstr e * w (s₀ + t') e * walkCount (st_t'.emb e) e') := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hSub_t' fun e he _ => ?_
          have heGt' : e ∈ (D.G (s₀ + t')).E := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
          have h1 := hwstr_nn e he
          have h2 : 0 ≤ w (s₀ + t') e := le_of_lt ((hWeak (s₀ + t') (by omega)).2.2.2 e heGt').1
          have h3 := walkCount_nonneg (st_t'.emb e) e'
          positivity
  rw [← hw' t ht, hGt_W, hGt'_W]; linarith

/-- Unconditional full `WeakHiddenStable` (all 4 clauses) over an arbitrary suffix epoch
`s₀ .. s₀ + Δ` (with `s₀ + Δ ≤ τ`) for any state sequence `st : ℕ → BundleTreeState L` whose
`.cs` agrees with `bundleRunSeq`, whose steps evolve via `stepBundleTree`, and whose `bun`/`dyn`
buckets satisfy single-step backward `walkEdges`/`walkCount` preservation (paper Lemma 5.17, item 2,
pages 23–24). -/
theorem bundleTreeState_seq_weakHiddenStable
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (_hj : j < k) (s₀ Δ : ℕ) (hsτ : s₀ + Δ ≤ τ)
    (st : ℕ → BundleTreeState L)
    (D' : DynamicInstance) (c' w' : ℕ → ℕ → ℝ)
    (hD'_G : ∀ r ≤ Δ, D'.G r = (st r).S_cur)
    (hD'_U : ∀ r < Δ, D'.U (r + 1) =
      (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).U_S)
    (hD'_ℓ : ∀ r ≤ Δ, D'.ℓ r = coreLen (st r).cs.lsf (D.ℓ (s₀ + r)))
    (hc' : ∀ r ≤ Δ, c' r = passSparseCoreC (coreGraph (D.G (s₀ + r)) (st r).cs.lsf)
      (st r).emb (passCoreC (c (s₀ + r))))
    (hw' : ∀ r ≤ Δ, w' r = passSparseCoreW (coreGraph (D.G (s₀ + r)) (st r).cs.lsf)
      (st r).emb (passCoreW (st r).cs.lsf (w (s₀ + r))))
    (hst_step : ∀ r < Δ, st (r + 1) =
      (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).state)
    (hcs_s : ∀ r ≤ Δ, (st r).cs =
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s₀ + r)).1.cs)
    (hI_s : ∀ r ≤ Δ, CompLSFInv C_lsst (D.ℓ 0) (st r).cs)
    (hG₀_s : ∀ r ≤ Δ, (st r).cs.G₀ = D.G 0)
    (hG_s : ∀ r ≤ Δ, (st r).cs.G = D.G (s₀ + r))
    (hAct_s : ∀ r ≤ Δ, (st r).activeComps ⊆ components (D.G 0))
    (hS_E : ∀ r ≤ Δ, (st r).S_cur.E =
      ((st r).activeComps.biUnion fun C => ((st r).activeBuckets C).biUnion fun b =>
          ((st r).dyn (C, b)).H.E) ∪
        ((st r).activeComps.biUnion fun C => (st r).extraEdges C) ∪
        (st r).cs.crossEdges)
    (hSp_metrics : ∀ r ≤ Δ,
      (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).IsSubgraph (st r).S_cur ∧
      (st r).emb.IsEmbedding (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) (st r).S_cur ∧
      (∀ e ∈ (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).E, ∀ e' ∈ walkEdges ((st r).emb e),
        approx2 (coreLen (st r).cs.lsf (D.ℓ (s₀ + r)) e)
          (coreLen (st r).cs.lsf (D.ℓ (s₀ + r)) e')) ∧
      ((st r).emb.length (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
      (st r).emb.econg (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) (st r).S_cur
        (fun _ => 1) (fun _ => 1) ≤ 1 + coreE82Cong L P_b * (k : ℝ))
    (hBun_s : ∀ r (hr : r ≤ Δ), ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (∀ (ρ : Rotation (st r).cs.G), ρ.order = ord (s₀ + r) →
        ((st r).bun (C, b)).IsPartition
          (coreRotation (L := (st r).cs.lsf) ρ (hI_s r hr).hG_val
            (compLSF_RF_isRSF (hI_s r hr))) (st r).k) ∧
      (∀ x ∈ ((st r).bun (C, b)).vertices,
        ((st r).bun (C, b)).parent x ∈ ((st r).cs.compSt C).R) ∧
      Disjoint ((st r).bun (C, b)).edges (st r).cs.crossEdges ∧
      GraphEq ((st r).dyn (C, b)).G ((st r).bun (C, b)).graph ∧
      ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
      (piTotal ((st r).dyn (C, b))).IsEmbedding ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H)
    (hBun_disj : ∀ r ≤ Δ, ∀ C₁ ∈ components (D.G 0), ∀ C₂ ∈ components (D.G 0), ∀ b₁ b₂ : ℤ,
      ∀ x, x ∈ ((st r).bun (C₁, b₁)).edges → x ∈ ((st r).bun (C₂, b₂)).edges →
        C₁ = C₂ ∧ b₁ = b₂)
    (hBun_step : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((st (r + 1)).bun (C, b)).edges ⊆ ((st r).bun (C, b)).edges ∧
      Disjoint ((st (r + 1)).bun (C, b)).edges (batchDeletes (D.U (s₀ + r + 1))))
    (hDyn_step : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let stepOut := (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)
      stepOut = update ((st r).dyn (C, b))
        ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b))
        (sparsify (st r).m₀) ∧
      stepOut.state = (st (r + 1)).dyn (C, b) ∧
      (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E,
        ∀ eH ∈ walkEdges (piTotal ((st (r + 1)).dyn (C, b)) eG),
          eH ∉ stepOut.D → eH ∈ walkEdges (piTotal ((st r).dyn (C, b)) eG)) ∧
      (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ x : ℕ,
        x ∉ stepOut.D →
        walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) x ≤
          walkCount (piTotal ((st r).dyn (C, b)) eG) x)) :
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (k : ℝ)) * coreE82Len L P_b * σ_top + 2)
    WeakHiddenStable D' Δ Ψ_S c' w' :=
  bundleTreeState_seq_weakHiddenStable_with (initLSFOnline oracle C_lsst) C_lsst L hL P_b sparsify
    k M N τ hk D hG₀ hV₀ hD hLen ord hOrd Ψ c w hWeak j (initLSFOnline_isValidLSFInitFor hLSST k j)
    s₀ Δ hsτ st D' c' w' hD'_G hD'_U hD'_ℓ hc' hw' hst_step hcs_s hI_s hG₀_s hG_s hAct_s hS_E
    hSp_metrics hBun_s hBun_disj hBun_step hDyn_step

/-! ## 2. `bundleRunSeq_weakHiddenStable` -/

/-- Full `WeakHiddenStable` for `sparseCoreBundleTool` along an ordered dynamic instance
(paper Lemma 5.17, item 2, pages 23–24). The congestion
factor in `Ψ_S` uses `k` in place of `2 M` because every bundle vertex has degree at most `k`. -/
theorem bundleRunSeq_weakHiddenStable
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (k : ℝ)) * coreE82Len L P_b * σ_top + 2)
    WeakHiddenStable (T.coreInstanceOrdAt k M N D ord j) τ Ψ_S (T.coreCOrdAt k M N D ord c j)
      (T.coreWOrdAt k M N D ord w j) := by
  intro T σ_top Ψ_S
  have hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e := fun s hs e he =>
    ((hWeak s hs).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hrun := sparseCoreBundleTool_runOrdAt oracle C_lsst L sparsify k M N D ord hV₀
  have hS_eq := bundleTool_S_eq_at oracle C_lsst L sparsify k M N D ord hV₀ j
  have hL_eq := bundleTool_lsfs_eq_at oracle C_lsst L sparsify k M N D ord hV₀ j
  have hEmb_eq := bundleTool_emb_eq_at oracle C_lsst L sparsify k M N D ord hV₀ j
  obtain ⟨hBase, hStep_st, hFlat⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  obtain ⟨hStage_all, hStep_full, _⟩ := bundleRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj
  have hSpCore := bundleRunSeq_isSparsifiedCoreGraph oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hD hℓ hLen hM hN hThresh hSp ord hOrd j hj
  set run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
  set st₀ := (run 0).1
  set cs₀ := st₀.cs
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have ⟨ρ_all, hρ_all, _⟩ := hOrd
  have hBun0_edges : ∀ C b, (st₀.bun (C, b)).edges =
      bucketCoreEdges (coreGraph (D.G 0) cs₀.lsf) st₀.origBucket C b := fun C b =>
    initBundleFor_edges_eq hI₀ (ρ_all 0) (hρ_all 0 (Nat.zero_le τ)) _ k
  have hStep_bun_sub : ∀ s < τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((run (s + 1)).1.bun (C, b)).edges ⊆ ((run s).1.bun (C, b)).edges := by
    intro s hs C hC b
    have hGs := ((hBase s (Nat.le_of_lt hs)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
    have hGs1 := ((hBase (s + 1) hs).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
    have hSt := (hStep_st s hs).2.2.2.2 C hC b
    have hEsub := bun_edges_sub_of_delOrSplit_batch (G := ((run s).1.dyn (C, b)).G) hSt.2.2.1
    rw [← hSt.2.1, hGs1.2.2.2.1.2.1, hGs.2.2.2.1.2.1] at hEsub
    exact hEsub
  have hE_sub_G : ∀ t ≤ τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((run t).1.bun (C, b)).edges ⊆ (D.G t).E := by
    intro t ht C hC b
    have hb := hBase t ht
    have hPart := ((hb.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1
    let ρt : Rotation (run t).1.cs.G := hb.2.2.2.2.2.2.2.2.1.symm ▸ ρ_all t
    have hρt : ρt.order = ord t := by
      have hcast : ∀ {G₁ G₂ : MGraph} (heq : G₁ = G₂) (ρ : Rotation G₁),
          (heq ▸ ρ : Rotation G₂).order = ρ.order := fun heq _ => by cases heq; rfl
      exact (hcast hb.2.2.2.2.2.2.2.2.1.symm (ρ_all t)).trans (hρ_all t ht)
    have hsub := (hPart ρt hb.2.2.2.2.2.2.2.1.hG_val (compLSF_RF_isRSF hb.2.2.2.2.2.2.2.1) hρt).1
    rw [hb.2.2.2.2.2.2.2.2.1] at hsub
    exact Finset.Subset.trans hsub Finset.sdiff_subset
  have hBunDisj : ∀ t < τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      Disjoint ((run (t + 1)).1.bun (C, b)).edges (batchDeletes (D.U (t + 1))) :=
    fun t ht C hC b => ((hStep_st t ht).2.2.2.2 C hC b).2.2.2.2.2
  have hDisjCross : ∀ t ≤ τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      Disjoint ((run t).1.bun (C, b)).edges (run t).1.cs.crossEdges := by
    have hAll := bun_edges_disjoint_insertedGlobal (C_lsst := C_lsst) (ℓ₀ := D.ℓ 0) hD
      (cs₀ := cs₀) rfl (fun t => (run t).1)
      (fun t ht => (hBase t ht).2.2.2.2.2.2.1)
      (fun t ht => (hBase t ht).2.2.2.2.2.2.2.1)
      hE_sub_G hStep_bun_sub hBunDisj
    exact fun t ht C hC b => (hAll t ht C hC b).2
  refine bundleTreeState_seq_weakHiddenStable oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hD hLen ord hOrd Ψ c w hWeak j hj 0 τ (by omega)
    (fun r => (run r).1)
    (T.coreInstanceOrdAt k M N D ord j) (T.coreCOrdAt k M N D ord c j)
    (T.coreWOrdAt k M N D ord w j)
    (fun r _ => hS_eq r)
    (fun r _ => by
      change (T.runOrdAt k M N D ord (r + 1)).2 j = _
      rw [(hrun (r + 1)).2.2.2.2 (Nat.succ_pos r) j, Nat.zero_add]; rfl)
    (fun r _ => by dsimp only [SparseCoreTool.coreInstanceOrdAt]; rw [hL_eq r, Nat.zero_add])
    (fun r _ => by dsimp only [SparseCoreTool.coreCOrdAt]; rw [hL_eq r, hEmb_eq r, Nat.zero_add])
    (fun r _ => by dsimp only [SparseCoreTool.coreWOrdAt]; rw [hL_eq r, hEmb_eq r, Nat.zero_add])
    (fun r _ => by rw [Nat.zero_add]; rfl)
    (fun r _ => by rw [Nat.zero_add])
    (fun r hr => (hBase r hr).2.2.2.2.2.2.2.1)
    (fun r hr => by rw [(hBase r hr).2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl)
    (fun r hr => by rw [Nat.zero_add]; exact (hBase r hr).2.2.2.2.2.2.2.2.1)
    (fun r hr => (hBase r hr).2.2.2.2.2.2.2.2.2.1.2)
    (fun r hr => by simpa [(hBase r hr).2.2.2.2.1] using (hStage_all r hr).2.2.1)
    (fun r hr => by
      rcases hSpCore r hr with ⟨h1, h2, h3, h4, h5, _⟩
      rw [Nat.zero_add]; exact ⟨h1, h2, h3, h4, h5⟩)
    (fun r hr C hC b => by
      have hb := ((hBase r hr).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
      have hst := (hStage_all r hr).2.2.2.2.2.2.2 C hC b
      refine ⟨fun ρ hρ => ?_, hb.2.2.1, hDisjCross r hr C hC b, hb.2.2.2.1, hst.1, hst.2.2.2.1⟩
      have hk_r : (run r).1.k = k := (hBase r hr).1
      exact Eq.mpr (congrArg (BundleState.IsPartition ((run r).1.bun (C, b)) _) hk_r)
        (hb.1 ρ _ _ (by simpa [Nat.zero_add] using hρ)))
    (fun r hr C₁ hC₁ C₂ hC₂ b₁ b₂ x hx₁ hx₂ => by
      have hsub₁ := ((hBase r hr).2.2.2.2.2.2.2.2.2.2.2 C₁ hC₁).2 b₁ |>.2.1 hx₁
      have hsub₂ := ((hBase r hr).2.2.2.2.2.2.2.2.2.2.2 C₂ hC₂).2 b₂ |>.2.1 hx₂
      rw [hBun0_edges C₁ b₁] at hsub₁
      rw [hBun0_edges C₂ b₂] at hsub₂
      exact bucketCoreEdges_pairwiseDisjoint hC₁ hC₂ hsub₁ hsub₂)
    (fun r hr C hC b => by
      rw [Nat.zero_add]
      exact ⟨hStep_bun_sub r hr C hC b, hBunDisj r hr C hC b⟩)
    (fun r hr C hC b => by
      have hSt := (hStep_full (r + 1) (Nat.succ_pos r) hr).2.2.2.1 C hC b
      simp only [Nat.add_sub_cancel] at hSt
      dsimp only [bundleRunInfo, bundleRunInfoWith] at hSt
      have hrun_eq : bundleRunSeqWith (initLSFOnline oracle C_lsst) L sparsify k M N D ord j r = run r := rfl
      rw [hrun_eq] at hSt
      refine ⟨?_, ?_, ?_, fun eG heG1 x hnotD => ?_⟩
      · rw [(hBase r (Nat.le_of_lt hr)).2.1]; simpa [Nat.zero_add] using hSt.1
      · simpa [Nat.zero_add] using hSt.2.1
      · simpa [Nat.zero_add] using hSt.2.2.2.2.2
      · set Hb₀ := normGraph (st₀.bun (C, b)).graph
        set splitB := bundleSplitBudget k M
        set Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
        set q_b := phaseBase (Hb₀.n + splitB) L
        have hHb_val : Hb₀.IsValid := by
          have hb0 := ((hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
          exact hb0.2.2.2.2.1
        have hHb_m : Hb₀.m ≤ M := by
          change (st₀.bun (C, b)).edges.card ≤ M
          rw [hBun0_edges C b]
          have hsub : bucketCoreEdges (coreGraph (D.G 0) cs₀.lsf) st₀.origBucket C b ⊆ (D.G 0).E :=
            Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset
          exact le_trans (Finset.card_le_card hsub) hM
        have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase (Hb₀.n + splitB) L)
        have hfb := hFlat C hC b
        have hUs_len : Us_b.length = τ := by simp [Us_b, bundleBatchList, bundleBatchListWith]
        have hget : Us_b[r]? = some ((stepBundleTree sparsify (run r).1
            (D.U (0 + r + 1)) (ord (0 + r)) (ord (0 + r + 1))).U_B (C, b)) := by
          simp only [Nat.zero_add]
          exact bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hr
        have hdyn_s : runBatchState Hb₀ q_b (sparsify M) Us_b r = (run r).1.dyn (C, b) :=
          (((hBase r (Nat.le_of_lt hr)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.2.symm
        have hSt2 : ((stepBundleTree sparsify (run r).1 (D.U (0 + r + 1))
            (ord (0 + r)) (ord (0 + r + 1))).stepOut (C, b)).state = (run (r + 1)).1.dyn (C, b) := by
          simpa [Nat.zero_add] using hSt.2.1
        have hres_eq : runBatchStepOut Hb₀ q_b (sparsify M) Us_b r =
            (stepBundleTree sparsify (run r).1 (D.U (0 + r + 1))
              (ord (0 + r)) (ord (0 + r + 1))).stepOut (C, b) := by
          dsimp only [DynSpanner.runBatchStepOut]
          rw [hget, hdyn_s]
          simpa [Nat.zero_add] using hSt.1.symm
        have hbt := DynSpanner.batchTrace_walkCount_le hHb_val hL hq1 hHb_m hSp
          ((graphEq_batchIsValid (normGraph_graphEq _) _).mpr hfb.1) hfb.2.1 r
          (hUs_len.symm ▸ hr) _ hget
        dsimp only at hbt
        rw [hres_eq, hdyn_s, hSt2] at hbt
        exact Nat.cast_le (α := ℝ).mpr (hbt eG heG1 x hnotD))

/-! ## 3. Unconditional surviving self-embeddings and unconditional no-reinsert -/

/-- On an empty initial graph, `sparseCoreBundleTool.runOrdAt` keeps `isNonempty = false` and emits
empty output batches at every stage. -/
lemma sparseCoreBundleTool_runOrdAt_empty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t
      r.1.isNonempty = false ∧ ∀ j, r.2 j = [] := by
  intro t
  induction t with
  | zero =>
    exact ⟨by simp [SparseCoreTool.runOrdAt, sparseCoreBundleTool, sparseCoreBundleToolWith,
        initBundleCoreWith, initBundleCoreWithParams, hV₀],
      fun _ => rfl⟩
  | succ s ih =>
    obtain ⟨hfalse, _⟩ := ih
    change (updateBundleCore sparsify _ (D.U (s + 1)) (ord (s + 1))).1.isNonempty = false ∧
      ∀ j, (updateBundleCore sparsify _ (D.U (s + 1)) (ord (s + 1))).2 j = []
    simp only [updateBundleCore, hfalse, Bool.false_eq_true, ↓reduceIte, implies_true, and_self]

/-- Surviving edges in the maintained sparsified core of `sparseCoreBundleTool` always embed as
themselves `[(e, true)]`. -/
lemma bundleCore_embedsSurviving_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    ∀ t j, ∀ e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E,
      T.emb (T.runOrdAt k M N D ord t).1 j e = [(e, true)] := by
  intro T t j e he
  have hrun := sparseCoreBundleTool_runOrdAt oracle C_lsst L sparsify k M N D ord hV₀ t
  dsimp only [T] at he ⊢
  change e ∈ (if ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty = true then
    (((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.trees j).S_cur
    else emptyGraph).E at he
  change (if ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.isNonempty = true then
    (((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1.trees j).emb
    else fun _ => []) e = _
  simp only [hrun.1, ↓reduceIte] at he ⊢
  rw [hrun.2.2.2.1 j] at he ⊢
  dsimp only [BundleTreeState.emb]
  simp only [he, ↓reduceIte]

lemma bundleCore_embedsSurviving
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    ∀ t j, ∀ e ∈ (T.S (T.runOrdAt k (D.G 0).m (D.G 0).n D ord t).1 j).E,
      T.emb (T.runOrdAt k (D.G 0).m (D.G 0).n D ord t).1 j e = [(e, true)] :=
  bundleCore_embedsSurviving_at oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D ord hV₀

/-- Unconditional surviving-edge insertion propagation for `sparseCoreBundleTool`: any edge `e`
surviving in `T.S _ j` from `t - 1` to `t` without insertion in `(T.runOrdAt ... t).2 j` cannot be
inserted in `D.U t`. -/
lemma bundleCore_noReinsert_step_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    ∀ e ∈ (T.S (T.runOrdAt k M N D ord (t - 1)).1 j).E,
      e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E →
      (∀ u ∈ (T.runOrdAt k M N D ord t).2 j, ¬ u.Inserts e) →
      ∀ u ∈ D.U t, ¬ u.Inserts e := by
  intro T e hePrev heCur hNoIns
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hePrev ⊢
  have hrun_cur := sparseCoreBundleTool_runOrdAt oracle C_lsst L sparsify k M N D ord hV₀ (s + 1)
  obtain ⟨_, hStep_full, _⟩ := bundleRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj
  have hS_prev_eq : T.S (T.runOrdAt k M N D ord s).1 j =
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.S_cur :=
    bundleTool_S_eq_at oracle C_lsst L sparsify k M N D ord hV₀ j s
  have hS_cur_eq : T.S (T.runOrdAt k M N D ord (s + 1)).1 j =
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.S_cur :=
    bundleTool_S_eq_at oracle C_lsst L sparsify k M N D ord hV₀ j (s + 1)
  have hU_eq : (T.runOrdAt k M N D ord (s + 1)).2 j =
      (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_S := by
    rw [hrun_cur.2.2.2.2 (Nat.succ_pos s) j]; rfl
  rw [hS_prev_eq] at hePrev
  rw [hS_cur_eq] at heCur
  rw [hU_eq] at hNoIns
  have hSt := (hStep_full (s + 1) (Nat.succ_pos s) htτ).2.2.2.2.1
  simp only [Nat.add_sub_cancel] at hSt
  exact (hSt e hePrev heCur hNoIns).2

lemma bundleCore_noReinsert_step
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hSp : SparsifySpec (D.G 0).m P_b (sparsify (D.G 0).m))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    ∀ e ∈ (T.S (T.runOrdAt k (D.G 0).m (D.G 0).n D ord (t - 1)).1 j).E,
      e ∈ (T.S (T.runOrdAt k (D.G 0).m (D.G 0).n D ord t).1 j).E →
      (∀ u ∈ (T.runOrdAt k (D.G 0).m (D.G 0).n D ord t).2 j, ¬ u.Inserts e) →
      ∀ u ∈ D.U t, ¬ u.Inserts e :=
  bundleCore_noReinsert_step_at oracle C_lsst L hL P_b sparsify hLSST
    k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hSp ord hOrd
    t ht1 htτ j hj

end

end MinCostFlow.SparseCore
