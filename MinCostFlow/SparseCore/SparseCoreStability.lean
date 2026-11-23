module

public import MinCostFlow.SparseCore.SparseCoreStabilityItems124
import MinCostFlow.DynSpanner.WalkCount

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional full `WeakHiddenStable`, surviving embeddings, and no-reinsert

Proves:
1. `treeCoreState_seq_weakHiddenStable` and `treeRunSeq_weakHiddenStable`: unconditional full
   `WeakHiddenStable` (including clause 3 `w^S_t(e') ≤ 2 * w^S_{t'}(e')`) using `buildUSReinsert`'s
   `D_total` reinsertion together with `DynSpanner.batchTrace_walkCount_le`.
2. `sparseCore_embedsSurviving`: surviving edges in `S_cur` always embed as `[(e, true)]`.
3. `sparseCore_noReinsert_step` and `sparseCore_noReinsert_step_strict`: unconditional surviving-edge
   insertion propagation for `sparseCoreTool` and strict `NoBatchReinsert` propagation for
   `sparseCoreToolKeep`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 3. Unconditional full `WeakHiddenStable` -/

private lemma passCoreW_sum_filter (lsf : LSF) (emb : Embedding) (G : MGraph)
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
`s₀ .. s₀ + Δ` (with `s₀ + Δ ≤ τ`) for any state sequence `st : ℕ → TreeCoreState L` whose
`.cs, .ts, .activeComps, .origBucket, .activeBuckets, .m₀` agree with `treeRunSeq`, whose steps
evolve via `stepTreeCoreAux`, and whose `dyn` buckets satisfy single-step backward
`walkEdges`/`walkCount` preservation. -/
theorem treeCoreState_seq_weakHiddenStable
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hj : j < k) (s₀ Δ : ℕ) (hsτ : s₀ + Δ ≤ τ)
    (st : ℕ → TreeCoreState L)
    (D' : DynamicInstance) (c' w' : ℕ → ℕ → ℝ)
    (hD'_G : ∀ r ≤ Δ, D'.G r = (st r).S_cur)
    (hD'_U : ∀ r < Δ, D'.U (r + 1) = (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_S)
    (hD'_ℓ : ∀ r ≤ Δ, D'.ℓ r = coreLen (st r).cs.lsf (D.ℓ (s₀ + r)))
    (hc' : ∀ r ≤ Δ, c' r = passSparseCoreC (coreGraph (D.G (s₀ + r)) (st r).cs.lsf)
      (st r).emb (passCoreC (c (s₀ + r))))
    (hw' : ∀ r ≤ Δ, w' r = passSparseCoreW (coreGraph (D.G (s₀ + r)) (st r).cs.lsf)
      (st r).emb (passCoreW (st r).cs.lsf (w (s₀ + r))))
    (hst_step : ∀ r < Δ, st (r + 1) = (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).state)
    (hm₀_s : ∀ r ≤ Δ, (st r).m₀ = M)
    (hcs_s : ∀ r ≤ Δ, (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs)
    (hts_s : ∀ r ≤ Δ, (st r).ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts)
    (hact_s : ∀ r ≤ Δ, (st r).activeComps =
      (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.activeComps)
    (horig_s : ∀ r ≤ Δ, (st r).origBucket =
      (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.origBucket)
    (hactB_s : ∀ r ≤ Δ, (st r).activeBuckets =
      (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.activeBuckets)
    (hS_E : ∀ r ≤ Δ, (st r).S_cur.E =
      ((st r).activeComps.biUnion fun C => ((st r).activeBuckets C).biUnion fun b => ((st r).dyn (C, b)).H.E) ∪
        ((st r).activeComps.biUnion fun C => extraSet ((st r).cs.compSt C) ((st r).ts C)) ∪
        (st r).cs.crossEdges)
    (hSp_metrics : ∀ r ≤ Δ,
      (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).IsSubgraph (st r).S_cur ∧
      (st r).emb.IsEmbedding (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) (st r).S_cur ∧
      (∀ e ∈ (coreGraph (D.G (s₀ + r)) (st r).cs.lsf).E, ∀ e' ∈ walkEdges ((st r).emb e),
        approx2 (coreLen (st r).cs.lsf (D.ℓ (s₀ + r)) e) (coreLen (st r).cs.lsf (D.ℓ (s₀ + r)) e')) ∧
      ((st r).emb.length (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
      (st r).emb.econg (coreGraph (D.G (s₀ + r)) (st r).cs.lsf) (st r).S_cur (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong L P_b * (2 * (M : ℝ)))
    (hDyn_G : ∀ r ≤ Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((st r).ts C).C.IsSubgraph ((st r).dyn (C, b)).G ∧
      ((st r).dyn (C, b)).G.E = ((st r).ts C).C.E.filter (fun e => (st r).origBucket e = b) ∧
      ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
      (piTotal ((st r).dyn (C, b))).IsEmbedding ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H)
    (hDyn_step : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let stepOut := (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)
      stepOut = update ((st r).dyn (C, b)) ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b))
        (sparsify (st r).m₀) ∧
      stepOut.state = (st (r + 1)).dyn (C, b) ∧
      (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E,
        ∀ eH ∈ walkEdges (piTotal ((st (r + 1)).dyn (C, b)) eG),
          eH ∉ stepOut.D → eH ∈ walkEdges (piTotal ((st r).dyn (C, b)) eG)) ∧
      (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ e' : ℕ,
        e' ∉ stepOut.D →
        walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) e' ≤ walkCount (piTotal ((st r).dyn (C, b)) eG) e')) :
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top + 2)
    WeakHiddenStable D' Δ Ψ_S c' w' := by
  intro σ_top Ψ_S t ht
  have hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e := fun s hs e he =>
    ((hWeak s hs).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hL_eq := tool_lsfs_eq_at oracle C_lsst L sparsify k M N D hV₀ j
  have hG_lsf := sparseCore_lsf_guarantees_at oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hD hℓ hLen
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hL_holds : ∀ r (hr : r ≤ Δ),
      (st r).cs.lsf.Holds (D.G (s₀ + r)) (D.ℓ (s₀ + r))
        (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G (s₀ + r)).n : ℝ) + 2)) ^ 6) := by
    intro r hr
    have h0 := (hG_lsf.1 (s₀ + r) (by omega) j hj).1
    rw [hL_eq (s₀ + r)] at h0
    rw [hcs_s r hr]
    exact h0
  have hRF_sub : ∀ r (hr : r ≤ Δ), (D.G (s₀ + r)).IsSubgraph (st r).cs.RF.F := by
    intro r hr
    rw [hcs_s r hr, ← (hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.2.1]
    exact (compLSF_RF_isRSF (hBase (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.1).2.2.2.2
  have hSpM := hSp_metrics t ht
  have h124 := treeCoreState_weakHidden_items124 C_lsst L hL P_b k M τ hk D hG₀ hD Ψ c w hWeak
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
      have hNoIns_s1 : ∀ u ∈ (stepTreeCoreAux sparsify (st s) (D.U (s₀ + s + 1))).U_S, ¬ u.Inserts e' := by
        have h := hNotIns (s + 1) (by omega) (by omega)
        rwa [hD'_U s hs_lt_Δ] at h
      have hG_cs_s : (st s).cs.G = D.G (s₀ + s) := by
        rw [hcs_s s hs_le_Δ]; exact (hBase (s₀ + s) (by omega)).2.2.2.2.2.2.2.2.2.1
      have hSp_sub_s : (coreGraph (st s).cs.G (st s).cs.lsf).IsSubgraph (st s).S_cur := by
        rw [hG_cs_s]; exact (hSp_metrics s hs_le_Δ).1
      obtain ⟨he'_s, _, hback_e⟩ := weakHidden_step_backward_core oracle C_lsst L sparsify hLSST
        k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j hs_lt (st s) (st (s + 1)) (hst_step s hs_lt_Δ)
        (hm₀_s s hs_le_Δ) (hcs_s s hs_le_Δ) (hcs_s (s + 1) hs1_le_Δ)
        (hts_s s hs_le_Δ) (hts_s (s + 1) hs1_le_Δ) (hact_s s hs_le_Δ) (hact_s (s + 1) hs1_le_Δ)
        (horig_s s hs_le_Δ) (horig_s (s + 1) hs1_le_Δ) (hactB_s s hs_le_Δ)
        hSp_sub_s (hS_E s hs_le_Δ) (hS_E (s + 1) hs1_le_Δ)
        (fun C hC b => ⟨(hDyn_G s hs_le_Δ C hC b).1, (hDyn_G s hs_le_Δ C hC b).2.1,
          (hDyn_G s hs_le_Δ C hC b).2.2.1⟩)
        (fun C hC b => ⟨(hDyn_G (s + 1) hs1_le_Δ C hC b).2.1,
          (hDyn_G (s + 1) hs1_le_Δ C hC b).2.2.1, (hDyn_G (s + 1) hs1_le_Δ C hC b).2.2.2⟩)
        (hDyn_step s hs_lt_Δ) he'_r1 hNoIns_s1
      refine ⟨he'_s, fun e heAt => ?_, fun e heAt => ?_⟩
      · have he_s1 := hSub_r1 heAt
        rw [Finset.mem_filter] at he_s1 ⊢
        have hb := hback_e e he_s1.1 he_s1.2
        exact ⟨hb.1, hb.2.1⟩
      · have he_s1 := hSub_r1 heAt
        rw [Finset.mem_filter] at he_s1
        have hb := hback_e e he_s1.1 he_s1.2
        have hw_eq := (hG_lsf.2.1 (s₀ + s + 1) (Nat.succ_pos _) (by omega) j hj).2.1 e
          (Finset.mem_sdiff.mp he_s1.1).1 (Finset.mem_sdiff.mp hb.1).1 hb.2.2.2
        dsimp only at hw_eq
        rw [Nat.add_sub_cancel, hL_eq (s₀ + s + 1), hL_eq (s₀ + s)] at hw_eq
        change (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + (s + 1))).1.cs.lsf.wstr e =
          (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + s)).1.cs.lsf.wstr e at hw_eq
        rw [← hcs_s (s + 1) hs1_le_Δ, ← hcs_s s hs_le_Δ] at hw_eq
        obtain ⟨hw_t, hwc_t, hni_t⟩ := hw_r1 e heAt
        refine ⟨hw_t.trans hw_eq, le_trans hwc_t hb.2.2.1, fun q hq1 hqt u hu => ?_⟩
        rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hq1) with rfl | hgt
        · exact hb.2.2.2 u hu
        · exact hni_t q (by omega) hqt u hu
  obtain ⟨_, hSub_t', hEdge_t'⟩ := hBack (t - t') le_rfl
  have hrr : t - (t - t') = t' := by omega
  rw [hrr] at hSub_t' hEdge_t'
  set st_t := st t
  set st_t' := st t'
  have hGt_W : w' t e' = 2 * ∑ e ∈ A t, st_t.cs.lsf.wstr e * w (s₀ + t) e * walkCount (st_t.emb e) e' := by
    rw [hw' t ht]; dsimp only [passSparseCoreW, passCoreW]
    exact congrArg (2 * ·) (passCoreW_sum_filter st_t.cs.lsf st_t.emb (D.G (s₀ + t)) (w (s₀ + t)) e')
  have hGt'_W : w' t' e' =
      2 * ∑ e ∈ A t', st_t'.cs.lsf.wstr e * w (s₀ + t') e * walkCount (st_t'.emb e) e' := by
    rw [hw' t' (le_trans ht't ht)]; dsimp only [passSparseCoreW, passCoreW]
    exact congrArg (2 * ·) (passCoreW_sum_filter st_t'.cs.lsf st_t'.emb (D.G (s₀ + t')) (w (s₀ + t')) e')
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

theorem treeRunSeq_weakHiddenStable_at
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
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top + 2)
    WeakHiddenStable (T.coreInstanceAt k M N D j) τ Ψ_S (T.coreCAt k M N D c j)
      (T.coreWAt k M N D w j) := by
  intro T σ_top Ψ_S
  have hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e := fun s hs e he =>
    ((hWeak s hs).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hrun := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀
  have hS_eq := tool_S_eq_at oracle C_lsst L sparsify k M N D hV₀ j
  have hL_eq := tool_lsfs_eq_at oracle C_lsst L sparsify k M N D hV₀ j
  have hEmb_eq := tool_emb_eq_at oracle C_lsst L sparsify k M N D hV₀ j
  have hSpCore := treeRunSeq_isSparsifiedCoreGraph oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hD hℓ hLen hM hN hThresh hSp j hj
  obtain ⟨hBase, _, hFlat⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, hStep_full, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  refine treeCoreState_seq_weakHiddenStable oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hD hLen hN hThresh Ψ c w hWeak j hj 0 τ (by omega)
    (fun r => (treeRunSeq oracle C_lsst L sparsify k M N D j r).1)
    (T.coreInstanceAt k M N D j) (T.coreCAt k M N D c j) (T.coreWAt k M N D w j)
    (fun r _ => hS_eq r)
    (fun r hr => by
      change (T.runAt k M N D (r + 1)).2 j = _
      rw [(hrun (r + 1)).2.2.2 (r + 1) (Nat.succ_pos r) j, Nat.zero_add]; rfl)
    (fun r _ => by dsimp only [SparseCoreTool.coreInstanceAt]; rw [hL_eq r, Nat.zero_add])
    (fun r _ => by dsimp only [SparseCoreTool.coreCAt]; rw [hL_eq r, hEmb_eq r, Nat.zero_add])
    (fun r _ => by dsimp only [SparseCoreTool.coreWAt]; rw [hL_eq r, hEmb_eq r, Nat.zero_add])
    (fun r _ => by rw [Nat.zero_add]; rfl)
    (fun r hr => (hBase r hr).1)
    (fun r _ => by rw [Nat.zero_add]) (fun r _ => by rw [Nat.zero_add])
    (fun r _ => by rw [Nat.zero_add]) (fun r _ => by rw [Nat.zero_add]) (fun r _ => by rw [Nat.zero_add])
    (fun r hr => by simpa [(hBase r hr).2.2.2.2.2.1] using (hStage_all r hr).2.2.1)
    (fun r hr => by
      rcases hSpCore r hr with ⟨h1, h2, h3, h4, _, h6, _⟩
      rw [Nat.zero_add]; exact ⟨h1, h2, h3, h4, h6⟩)
    (fun r hr C hC b => ⟨((hBase r hr).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b |>.2.1,
      (((hBase r hr).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b).2.2.1.trans
        (Finset.filter_congr fun x hx => by
          have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
          have hT0 := initTildeState_inv (hI₀.hCompLSF C hC).1 (initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC).2
          have hxG₀ : x ∈ (D.G 0).E :=
            (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
              (hT0.hCE_sub (((hBase r hr).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1 hx)))).1
          rw [(hBase r hr).2.2.2.2.1]; simp [coreLen, safeLen, hxG₀]),
      (hStage_all r hr).2.2.2.2.2.2.2 C hC b |>.1,
      (hStage_all r hr).2.2.2.2.2.2.2 C hC b |>.2.2.2.1⟩)
    (fun r hr C hC b => by
      have hSt := (hStep_full (r + 1) (Nat.succ_pos r) hr).2.2.2.1 C hC b
      refine ⟨?_, ?_, ?_, fun eG heG1 e' hnotD => ?_⟩
      · rw [(hBase r (Nat.le_of_lt hr)).1]; simpa [Nat.zero_add] using hSt.1
      · simpa [Nat.zero_add] using hSt.2.1
      · simpa [Nat.zero_add] using hSt.2.2.2.2.2
      · set cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
        set Hb₀ := initBucketGraph (cs₀.compSt C) (D.ℓ 0) b
        set splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
          ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
        set Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
        set q_b := phaseBase (Hb₀.n + splitB) L
        have hS₀C_spec := initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC
        have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
        have hHb := initBucketGraph_spec (hI₀.hCompLSF C hC).1 hS₀C_spec.2 b
        have hHb_m : Hb₀.m ≤ M := le_trans (le_trans hHb.2.2.2.2.2.2.2.1
          (by rw [hS₀C_spec.1]; exact compGraph_m_le)) hM
        have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase (Hb₀.n + splitB) L)
        have hfb := hFlat C hC b
        have hUs_len : Us_b.length = τ := by simp [Us_b, bucketBatchList]
        have hget : Us_b[r]? = some ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
            (D.U (0 + r + 1))).U_b (C, b)) := by
          rw [Nat.zero_add]
          exact bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hr
        have hdyn_s : runBatchState Hb₀ q_b (sparsify M) Us_b r =
            (treeRunSeq oracle C_lsst L sparsify k M N D j r).1.dyn (C, b) :=
          (((hBase r (Nat.le_of_lt hr)).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b).2.2.2.symm
        have hSt2 : ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
            (D.U (0 + r + 1))).stepOut (C, b)).state =
            (treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.dyn (C, b) := by
          simpa [Nat.zero_add] using hSt.2.1
        have hres_eq : runBatchStepOut Hb₀ q_b (sparsify M) Us_b r =
            (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
              (D.U (0 + r + 1))).stepOut (C, b) := by
          dsimp only [DynSpanner.runBatchStepOut]
          rw [hget, hdyn_s]
          exact (by simpa [Nat.zero_add] using hSt.1.symm)
        have hbt := DynSpanner.batchTrace_walkCount_le hHb.1 hL hq1 hHb_m hSp hfb.1 hfb.2.1 r
          (hUs_len.symm ▸ hr) _ hget
        dsimp only at hbt
        rw [hres_eq, hdyn_s, hSt2] at hbt
        exact Nat.cast_le (α := ℝ).mpr (hbt eG heG1 e' hnotD))

theorem treeRunSeq_weakHiddenStable
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hSp : SparsifySpec (D.G 0).m P_b (sparsify (D.G 0).m))
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (2 * ((D.G 0).m : ℝ))) * coreE82Len L P_b * σ_top + 2)
    WeakHiddenStable (T.coreInstance k D j) τ Ψ_S (T.coreC k D c j) (T.coreW k D w j) :=
  treeRunSeq_weakHiddenStable_at oracle C_lsst L hL P_b sparsify hLSST
    k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hD hLen le_rfl le_rfl hThresh hSp Ψ c w hWeak j hj

/-! ## 4. Unconditional surviving self-embeddings and unconditional no-reinsert -/

lemma sparseCore_embedsSurviving_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    ∀ t j, ∀ e ∈ (T.S (T.runAt k M N D t).1 j).E, T.emb (T.runAt k M N D t).1 j e = [(e, true)] := by
  intro T t j e he
  have hrun := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀ t
  dsimp only [T] at he ⊢
  change e ∈ (if ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1.isNonempty = true then
    (((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1.trees j).S_cur else emptyGraph).E at he
  change (if ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1.isNonempty = true then
    (((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1.trees j).emb else fun _ => []) e = _
  simp only [hrun.1, ↓reduceIte] at he ⊢
  rw [hrun.2.2.1 j] at he ⊢
  dsimp only [TreeCoreState.emb]
  simp only [he, ↓reduceIte]

lemma sparseCore_embedsSurviving
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    ∀ t j, ∀ e ∈ (T.S (T.run k D t).1 j).E, T.emb (T.run k D t).1 j e = [(e, true)] :=
  sparseCore_embedsSurviving_at oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D hV₀

/-- Legacy strict `NoBatchReinsert` propagation for `sparseCoreToolKeep`: `buildUS` never
deletes and reinserts surviving edges when the input batch is non-reinserting. -/
lemma sparseCore_noReinsert_step_strict_at
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
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k)
    (hNoReins_in : NoBatchReinsert (D.G (t - 1)) (D.U t)) :
    let T := sparseCoreToolKeep oracle C_lsst L sparsify
    NoBatchReinsert (T.S (T.runAt k M N D (t - 1)).1 j) ((T.runAt k M N D t).2 j) := by
  intro T
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hNoReins_in ⊢
  have hs_lt : s + 1 ≤ τ := htτ
  have hrun_prev := sparseCoreToolWith_runAt_eq_treeRunSeqWith false oracle C_lsst L sparsify k M N D hV₀ s
  have hrun_cur := sparseCoreToolWith_runAt_eq_treeRunSeqWith false oracle C_lsst L sparsify k M N D hV₀ (s + 1)
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, _, hStep_full, _⟩ := treeRunSeq_invWith false oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hcs_eq := (treeRunSeqWith_fields_eq false oracle C_lsst L sparsify k M N D j s).2.2.2.2.2.2.2.1
  have hG_prev : (treeRunSeqKeep oracle C_lsst L sparsify k M N D j s).1.cs.G = D.G s := by
    rw [hcs_eq]
    exact (hBase s (Nat.le_of_lt htτ)).2.2.2.2.2.2.2.2.2.1
  have hNR := (hStep_full (s + 1) (Nat.succ_pos s) hs_lt).2.2.2.2.1.1 rfl
  simp only [Nat.add_sub_cancel] at hNR
  have hNR' := hNR (hG_prev ▸ hNoReins_in)
  have hS_prev_eq : T.S (T.runAt k M N D s).1 j =
      (treeRunSeqKeep oracle C_lsst L sparsify k M N D j s).1.S_cur := by
    dsimp only [T, sparseCoreToolKeep, SparseCoreTool.S]
    change (if ((sparseCoreToolWith false oracle C_lsst L sparsify).runAt k M N D s).1.isNonempty = true then
      (((sparseCoreToolWith false oracle C_lsst L sparsify).runAt k M N D s).1.trees j).S_cur else emptyGraph) = _
    simp only [hrun_prev.1, ↓reduceIte, hrun_prev.2.2.1 j]
  have hU_eq : (T.runAt k M N D (s + 1)).2 j = (treeRunSeqKeep oracle C_lsst L sparsify k M N D j (s + 1)).2 :=
    hrun_cur.2.2.2 (s + 1) (Nat.succ_pos s) j
  rw [hS_prev_eq, hU_eq]
  exact hNR'

lemma sparseCore_noReinsert_step_strict
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
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k)
    (hNoReins_in : NoBatchReinsert (D.G (t - 1)) (D.U t)) :
    let T := sparseCoreToolKeep oracle C_lsst L sparsify
    NoBatchReinsert (T.S (T.run k D (t - 1)).1 j) ((T.run k D t).2 j) :=
  sparseCore_noReinsert_step_strict_at oracle C_lsst L hL P_b sparsify hLSST
    k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hSp t ht1 htτ j hj hNoReins_in

/-- Unconditional surviving-edge insertion propagation for `sparseCoreTool`:
any edge `e` surviving in `T.S _ j` from `t - 1` to `t` without insertion in `U_{\mathcal{S}, j}^{(t)}`
cannot be inserted in `D.U t`. -/
lemma sparseCore_noReinsert_step_at
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
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    ∀ e ∈ (T.S (T.runAt k M N D (t - 1)).1 j).E,
      e ∈ (T.S (T.runAt k M N D t).1 j).E →
      (∀ u ∈ (T.runAt k M N D t).2 j, ¬ u.Inserts e) →
      ∀ u ∈ D.U t, ¬ u.Inserts e := by
  intro T e hePrev heCur hNoIns
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hePrev ⊢
  have hs_lt : s < τ := htτ
  have hrun_cur := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀ (s + 1)
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, _, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  set stPrev := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
  set stCur := (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1
  have hS_prev_eq : T.S (T.runAt k M N D s).1 j = stPrev.S_cur :=
    tool_S_eq_at oracle C_lsst L sparsify k M N D hV₀ j s
  have hS_cur_eq : T.S (T.runAt k M N D (s + 1)).1 j = stCur.S_cur :=
    tool_S_eq_at oracle C_lsst L sparsify k M N D hV₀ j (s + 1)
  have hU_eq : (T.runAt k M N D (s + 1)).2 j =
      (stepTreeCoreAux sparsify stPrev (D.U (s + 1))).U_S := by
    rw [hrun_cur.2.2.2 (s + 1) (Nat.succ_pos s) j]; rfl
  rw [hS_prev_eq] at hePrev
  rw [hS_cur_eq] at heCur
  rw [hU_eq] at hNoIns
  have hS_prev_sub : (coreGraph stPrev.cs.G stPrev.cs.lsf).IsSubgraph stPrev.S_cur :=
    (hStage_all s (Nat.le_of_lt htτ)).2.2.2.1
  have hS_cur_E := (hStage_all (s + 1) htτ).2.2.1
  have hAB_s := (hBase s (Nat.le_of_lt htτ)).2.2.2.2.2.1
  have hSte : (stepTreeCoreAux sparsify stPrev (D.U (s + 1))).state = stCur := rfl
  exact (stepTreeCoreAux_noReinsertPropagates sparsify stPrev (D.U (s + 1)) (hStep s hs_lt).1
    hS_prev_sub hAB_s (hSte ▸ hS_cur_E) e hePrev (hSte ▸ heCur) hNoIns).2

lemma sparseCore_noReinsert_step
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
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    ∀ e ∈ (T.S (T.run k D (t - 1)).1 j).E,
      e ∈ (T.S (T.run k D t).1 j).E →
      (∀ u ∈ (T.run k D t).2 j, ¬ u.Inserts e) →
      ∀ u ∈ D.U t, ¬ u.Inserts e :=
  sparseCore_noReinsert_step_at oracle C_lsst L hL P_b sparsify hLSST
    k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hSp t ht1 htτ j hj

end

end MinCostFlow.SparseCore
