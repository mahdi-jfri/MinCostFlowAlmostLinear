module

public import MinCostFlow.Spanner.Claim87Base

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Task 2 Completion: Claim 8.7, Corollary 8.8, and Task 2 Bounds

Proves `claim_8_7` (Claim 8.7, pages 43–44), `task2_spec`, `corollary_8_8`
(Corollary 8.8, page 44), and `task2_stats`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Claim 8.7 (`claim_8_7`) -/

/-- **Claim 8.7** (`spanner.tex`, pages 43–44):
In one round `s' = task2Round wd s` starting from `hs : Task2RoundEntryInv ... s`:
1. The unembedded `W`-volume at `s'` is at most `2 c_deg` times the `W`-volume of newly embedded
   edges `newlyEmbeddedSet1 wd s s'`.
2. Consequently, `volWRem wd s' ≤ (2 c_deg / (2 c_deg + 1)) * volWRem wd s`.
3. `s'.deleteCountJ - s.deleteCountJ ≤ J.m`.
4. `s'.innerIters1 - s.innerIters1 ≤ H'.n`, and when `0 < wd.τ₁`,
   `(s'.innerIters1 - s.innerIters1 : ℝ) ≤ (newlyEmbeddedSet1 wd s s').card * (wd.γ_ExpPath * (length J embJH + 1))`. -/
theorem claim_8_7 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s : Task2State tools.pathDS.State}
    (hs : Task2RoundEntryInv tools.pathDS.State H' J embJH (buildWitness tools H' J embJH) s) :
    let wd := buildWitness tools H' J embJH
    let s' := task2Round tools.pathDS H' J embJH wd s
    let E_embed := newlyEmbeddedSet1 wd s s'
    volWRem wd s' ≤ (2 * wd.c_deg) * (∑ eW ∈ E_embed, wd.wW eW) ∧
    volWRem wd s' ≤ ((2 * wd.c_deg) / (2 * wd.c_deg + 1)) * volWRem wd s ∧
    s'.deleteCountJ - s.deleteCountJ ≤ J.m ∧
    s'.innerIters1 - s.innerIters1 ≤ H'.n ∧
    (0 < wd.τ₁ → ((s'.innerIters1 - s.innerIters1 : ℕ) : ℝ) ≤
      (E_embed.card : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))) := by
  intro wd s' E_embed
  obtain ⟨hη_eq, hloop', hrel', hmid, _⟩ := invariant_1 tools H' J embJH hJ hembJH hw hs
  let dsDef := tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
  have hpart := unembeddedSet1_partition wd s s' hrel'.emb_mono
  have hvol_mid := volWRem_le_of_mid_done tools H' J embJH hw hloop'.toTask2CoreInv hmid
  obtain ⟨hdel_m, hdel_proc⟩ := sum_deleted_bounds tools H' J embJH hw hloop'.toTask2CoreInv
  have hdel_diff : s'.deleteCountJ - s.deleteCountJ =
      ∑ ci ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card := by
    have hdeq := hrel'.del_eq
    change s'.deleteCountJ = s.deleteCountJ +
        ∑ ci ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card at hdeq
    omega
  have hdel_le : s'.deleteCountJ - s.deleteCountJ ≤ J.m := by
    rw [hdel_diff]
    exact hdel_m
  have hinner_diff : s'.innerIters1 - s.innerIters1 = s'.processedVerts.card := by
    have hieq := hrel'.inner_eq
    change s'.innerIters1 = s.innerIters1 + s'.processedVerts.card at hieq
    omega
  have hinner_H : s'.innerIters1 - s.innerIters1 ≤ H'.n := by
    rw [hinner_diff]
    have hsub : s'.processedVerts ⊆ Finset.range H'.n := fun x hx =>
      Finset.mem_range.mpr (hloop'.processed_sub x hx).1
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range H'.n)
  -- Per processed vertex x ∈ s'.processedVerts, vcong increased by at least τ₁ / 2.
  have hvcong_inc : ∀ x ∈ s'.processedVerts,
      wd.τ₁ / 2 ≤ ∑ eW ∈ E_embed,
        if x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts then wd.wW eW else 0 := by
    intro x hx
    have hx_sub := hloop'.processed_sub x hx
    have hhigh : (s'.η₁ : ℝ) * wd.τ₁ ≤
        vcongAt wd.W wd.wW (compose J embJH (partialToWalk s'.embWJ)) x := hx_sub.2
    have hlow : vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x ≤
        ((s.η₁ : ℝ) + 1 / 2) * wd.τ₁ := hs.vcong_half x hx_sub.1
    have hdiff : wd.τ₁ / 2 ≤
        vcongAt wd.W wd.wW (compose J embJH (partialToWalk s'.embWJ)) x -
          vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x := by
      have hη_s' : s'.η₁ = s.η₁ + 1 := hη_eq
      have hη_r : (s'.η₁ : ℝ) = (s.η₁ : ℝ) + 1 := by exact_mod_cast hη_s'
      rw [hη_r] at hhigh
      have hexp1 : ((s.η₁ : ℝ) + 1) * wd.τ₁ = (s.η₁ : ℝ) * wd.τ₁ + wd.τ₁ := by ring
      have hexp2 : ((s.η₁ : ℝ) + 1 / 2) * wd.τ₁ = (s.η₁ : ℝ) * wd.τ₁ + wd.τ₁ / 2 := by ring
      linarith
    have hmono_diff := vcongAt_mono_diff wd.W J wd.wW embJH s.embWJ s'.embWJ
      (fun e0 he0 => hrel'.emb_mono e0 he0) x
    have hsum_eq : (∑ eW ∈ (Finset.range wd.W.m).filter (fun eW =>
          (s.embWJ eW).isNone = true ∧ (s'.embWJ eW).isSome = true ∧
            x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts), wd.wW eW) =
        ∑ eW ∈ E_embed,
          if x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts then wd.wW eW else 0 := by
      rw [Finset.sum_filter]
      dsimp only [E_embed, newlyEmbeddedSet1]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun eW _ => ?_
      by_cases h1 : (s.embWJ eW).isNone = true <;>
        by_cases h2 : (s'.embWJ eW).isSome = true <;>
        by_cases h3 : x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts <;>
        simp [h1, h2, h3]
    rw [hsum_eq] at hmono_diff
    linarith
  have hverts_le : ∀ eW ∈ E_embed,
      ((compose J embJH (partialToWalk s'.embWJ) eW).verts.toFinset.card : ℝ) ≤
        wd.γ_ExpPath * ((length J embJH : ℝ) + 1) := by
    intro eW heW
    rw [mem_newlyEmbeddedSet1] at heW
    have hwalk : Walk.IsWalk J (wd.W.edges[eW]'heW.1).1 (wd.W.edges[eW]'heW.1).2
        (partialToWalk s'.embWJ eW) := by
      rcases Option.isSome_iff_exists.mp heW.2.2 with ⟨P, hP⟩
      have hpw : partialToWalk s'.embWJ eW = P := by simp [partialToWalk, hP]
      rw [hpw]
      exact hloop'.partial_emb.2 eW heW.1 P hP
    have hPedges : ∀ j ∈ (partialToWalk s'.embWJ eW).edges, j < J.m :=
      hwalk.2.2.elim (fun h => by simp [h.2.1]) (fun h => h.2.2.2.2.1)
    have hcard := verts_toFinset_compose_card_le hembJH hPedges
    have hlen := hloop'.emb_len eW heW.1
    change ((composeAux J embJH (partialToWalk s'.embWJ eW).verts (partialToWalk s'.embWJ eW).edges).verts.toFinset.card : ℝ) ≤ _
    exact le_trans hcard (mul_le_mul_of_nonneg_right hlen (by positivity))
  have hsum_proc_tau : (s'.processedVerts.card : ℝ) * (wd.τ₁ / 2) ≤
      ∑ eW ∈ E_embed, wd.wW eW * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by
    calc (s'.processedVerts.card : ℝ) * (wd.τ₁ / 2)
        = ∑ _x ∈ s'.processedVerts, (wd.τ₁ / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ s'.processedVerts, ∑ eW ∈ E_embed,
            if x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts then wd.wW eW else 0 :=
          Finset.sum_le_sum hvcong_inc
      _ = ∑ eW ∈ E_embed, ∑ x ∈ s'.processedVerts,
            if x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts then wd.wW eW else 0 :=
          Finset.sum_comm
      _ ≤ ∑ eW ∈ E_embed, wd.wW eW * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun eW heW => ?_
          have hm : eW < wd.W.m := ((mem_newlyEmbeddedSet1 wd s s').mp heW).1
          have hw_pos := (wW_pos tools H' J embJH hw hm).le
          have hsub : s'.processedVerts.filter (fun x =>
                x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts) ⊆
              (compose J embJH (partialToWalk s'.embWJ) eW).verts.toFinset := by
            intro x hx
            exact List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          rw [mul_comm _ (wd.wW eW)]
          have hcard_le : ((s'.processedVerts.filter fun x =>
                x ∈ (compose J embJH (partialToWalk s'.embWJ) eW).verts).card : ℝ) ≤
              ((compose J embJH (partialToWalk s'.embWJ) eW).verts.toFinset.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          exact mul_le_mul_of_nonneg_left (le_trans hcard_le (hverts_le eW heW)) hw_pos
  have hinner_tau : 0 < wd.τ₁ →
      ((s'.innerIters1 - s.innerIters1 : ℕ) : ℝ) ≤
        (E_embed.card : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by
    intro hτpos
    have hhalf_pos : 0 < wd.τ₁ / 2 := div_pos hτpos (by norm_num)
    have hlen_JH : 1 ≤ length J embJH := by
      by_contra h0
      have h0' : length J embJH = 0 := by omega
      have hτ0 : wd.τ₁ / 2 = 0 := by
        rw [tau_half_eq, h0', Nat.cast_zero, mul_zero, zero_mul, zero_mul, zero_div]
      linarith
    have hdeg_le_half : (maxDeg J : ℝ) ≤ wd.τ₁ / 2 :=
      maxDeg_le_tau_half tools H' J embJH hw hlen_JH
    have hγE_nn : 0 ≤ wd.γ_ExpPath * ((length J embJH : ℝ) + 1) := by
      have h1 : (0 : ℝ) ≤ 1 / wd.φ_ds := div_nonneg zero_le_one hw.φ_ds_pos.le
      have hge : 0 ≤ wd.γ_ExpPath := le_trans h1 hw.γ_ExpPath_ge
      exact mul_nonneg hge (add_nonneg (Nat.cast_nonneg _) zero_le_one)
    have hprod_le : (s'.processedVerts.card : ℝ) * (wd.τ₁ / 2) ≤
        ((E_embed.card : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))) * (wd.τ₁ / 2) := by
      refine le_trans hsum_proc_tau ?_
      calc ∑ eW ∈ E_embed, wd.wW eW * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))
          ≤ ∑ _eW ∈ E_embed, (wd.τ₁ / 2) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by
            refine Finset.sum_le_sum fun eW heW => ?_
            have hm : eW < wd.W.m := ((mem_newlyEmbeddedSet1 wd s s').mp heW).1
            have hw_deg := wW_le_maxDeg tools H' J embJH hJ hw hm
            exact mul_le_mul_of_nonneg_right (le_trans hw_deg hdeg_le_half) hγE_nn
        _ = ((E_embed.card : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))) * (wd.τ₁ / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm (wd.τ₁ / 2), ← mul_assoc]
    rw [hinner_diff]
    exact le_of_mul_le_mul_right hprod_le hhalf_pos
  have hvol_embed : volWRem wd s' ≤ (2 * wd.c_deg) * (∑ eW ∈ E_embed, wd.wW eW) := by
    by_cases hcomp0 : wd.comps.length = 0
    · have hsum_nn : 0 ≤ ∑ eW ∈ E_embed, wd.wW eW := Finset.sum_nonneg fun eW heW =>
        (wW_pos tools H' J embJH hw ((mem_newlyEmbeddedSet1 wd s s').mp heW).1).le
      have hcdeg_nn : 0 ≤ 2 * wd.c_deg := by linarith [hw.c_deg_ge]
      have hm' : volWRem wd s' ≤ (wd.c_deg * wd.γ_del / wd.φ_ds) *
          ((∑ ci ∈ Finset.range wd.comps.length,
            (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card : ℕ) : ℝ) := hvol_mid
      rw [hcomp0, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero] at hm'
      exact le_trans hm' (mul_nonneg hcdeg_nn hsum_nn)
    · have hcomp_pos : 0 < wd.comps.length := Nat.pos_of_ne_zero hcomp0
      obtain ⟨hmaxDeg, hlenJH⟩ := nonloop_edge_witness_bounds tools H' J embJH hJ hembJH hw hcomp_pos
      have hvcong_nn : 0 ≤ vcong J H' (fun _ => 1) embJH := vcong_nonneg J H' (fun _ => 1) embJH
      have hmax_pos : (0 : ℝ) < (maxDeg J : ℝ) := by exact_mod_cast hmaxDeg
      have hlen_pos : (0 : ℝ) < (length J embJH : ℝ) := by exact_mod_cast hlenJH
      have hφ_pos : 0 < wd.φ_ds := hw.φ_ds_pos
      have hγE_pos : 0 < wd.γ_ExpPath :=
        lt_of_lt_of_le (div_pos zero_lt_one hφ_pos) hw.γ_ExpPath_ge
      have hγdel_pos : 0 < wd.γ_del := lt_of_lt_of_le zero_lt_one hw.γ_del_ge
      have hτ₁_half := tau_half_eq tools H' J embJH
      have hhalf_pos : 0 < wd.τ₁ / 2 := by
        rw [hτ₁_half]
        exact div_pos (mul_pos (mul_pos (mul_pos hγE_pos hlen_pos) hγdel_pos)
          (add_pos_of_nonneg_of_pos hvcong_nn hmax_pos)) hφ_pos
      have hlen_one : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hlenJH
      have hlen_two : (length J embJH : ℝ) + 1 ≤ 2 * (length J embJH : ℝ) := by linarith [hlen_one]
      have hsum_two : (s'.processedVerts.card : ℝ) * (wd.τ₁ / 2) ≤
          (2 * wd.γ_ExpPath * (length J embJH : ℝ)) * (∑ eW ∈ E_embed, wd.wW eW) := by
        refine le_trans hsum_proc_tau ?_
        calc ∑ eW ∈ E_embed, wd.wW eW * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))
            ≤ ∑ eW ∈ E_embed, wd.wW eW * (wd.γ_ExpPath * (2 * (length J embJH : ℝ))) := by
              refine Finset.sum_le_sum fun eW heW => ?_
              have hm := ((mem_newlyEmbeddedSet1 wd s s').mp heW).1
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlen_two hγE_pos.le)
                (wW_pos tools H' J embJH hw hm).le
          _ = (2 * wd.γ_ExpPath * (length J embJH : ℝ)) * (∑ eW ∈ E_embed, wd.wW eW) := by
              rw [← Finset.sum_mul, mul_comm, two_mul_swap]
      have hcdeg_nn : 0 ≤ wd.c_deg := by linarith [hw.c_deg_ge]
      have hA : volWRem wd s' ≤
          (wd.c_deg * wd.γ_del * vcong J H' (fun _ => 1) embJH / wd.φ_ds) *
            (s'.processedVerts.card : ℝ) := by
        have h1 : (wd.c_deg * wd.γ_del / wd.φ_ds) *
              ((∑ ci ∈ Finset.range wd.comps.length,
                (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card : ℕ) : ℝ) ≤
            (wd.c_deg * wd.γ_del / wd.φ_ds) *
              ((s'.processedVerts.card : ℝ) * vcong J H' (fun _ => 1) embJH) :=
          mul_le_mul_of_nonneg_left hdel_proc
            (div_nonneg (mul_nonneg hcdeg_nn hγdel_pos.le) hφ_pos.le)
        have h_re := div_mul_assoc_swap wd.c_deg wd.γ_del wd.φ_ds
          (s'.processedVerts.card : ℝ) (vcong J H' (fun _ => 1) embJH)
        exact le_trans hvol_mid (le_trans h1 (le_of_eq h_re))
      have hsum_nn : 0 ≤ ∑ eW ∈ E_embed, wd.wW eW := Finset.sum_nonneg fun eW heW =>
        (wW_pos tools H' J embJH hw ((mem_newlyEmbeddedSet1 wd s s').mp heW).1).le
      exact claim_8_7_algebra hcdeg_nn hγdel_pos hφ_pos hlen_pos hγE_pos hvcong_nn
        hmax_pos hsum_nn hτ₁_half hA hsum_two
  have hvol_shrink : volWRem wd s' ≤ ((2 * wd.c_deg) / (2 * wd.c_deg + 1)) * volWRem wd s := by
    have hden_pos : 0 < 2 * wd.c_deg + 1 := by linarith [hw.c_deg_ge]
    have hpart_sum : volWRem wd s = volWRem wd s' + ∑ eW ∈ E_embed, wd.wW eW := hpart.2.2.2.1
    have hmul : volWRem wd s' * (2 * wd.c_deg + 1) ≤ (2 * wd.c_deg) * volWRem wd s := by
      rw [hpart_sum]
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hden_pos]
    exact hmul
  exact ⟨hvol_embed, hvol_shrink, hdel_le, hinner_H, hinner_tau⟩

/-! ## Task 2 termination, round bound (`eta1Bound`), Corollary 8.8, and stats -/

private theorem volWRem_task2Init_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    volWRem wd (task2Init J wd (DSState := tools.pathDS.State)) ≤ wd.c_deg * (J.m : ℝ) := by
  intro wd
  unfold volWRem
  have hsub : unembeddedSet1 wd (task2Init J wd (DSState := tools.pathDS.State)) ⊆
      Finset.Ico wd.j0Edges.length wd.W.m := by
    intro eW heW
    simp only [unembeddedSet1, Finset.mem_filter, Finset.mem_range,
      Option.isNone_iff_eq_none] at heW
    refine Finset.mem_Ico.mpr ⟨?_, heW.1⟩
    by_contra hlt
    have hj0 := (task2Init_entryInv tools H' J embJH hJ hembJH hw).j0_embedded eW (Nat.lt_of_not_ge hlt)
    rw [heW.2] at hj0
    simp at hj0
  have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub fun eW heW _ =>
    (wW_pos tools H' J embJH hw (Finset.mem_Ico.mp heW).2).le
  exact le_trans hsum_le (sum_wW_comp_le tools H' J embJH hw)

/-- Complete Task 2 specification (`spanner.tex`, pages 42–44):
`task2` terminates with `task2OuterCond = false`, satisfies `Task2LoopInv`, completes within
`1 ≤ s_final.η₁ ≤ eta1Bound wd J` rounds, and bounds all Task 2 counters. -/
theorem task2_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s_final := task2 tools.pathDS H' J embJH wd
    task2OuterCond wd s_final = false ∧
    Task2LoopInv tools.pathDS H' J embJH wd s_final ∧
    1 ≤ s_final.η₁ ∧
    s_final.η₁ ≤ eta1Bound wd J ∧
    s_final.deleteCountJ ≤ s_final.η₁ * J.m ∧
    s_final.innerIters1 ≤ s_final.η₁ * H'.n ∧
    (s_final.innerIters1 : ℝ) ≤
      (s_final.getPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by
  intro wd s_final
  let V₀ : ℝ := wd.c_deg * (J.m : ℝ)
  let M : ℝ := wd.γ_ExpPath * ((length J embJH : ℝ) + 1)
  let r : ℝ := (2 * wd.c_deg) / (2 * wd.c_deg + 1)
  let K : ℕ := Nat.ceil (2 * wd.c_deg)
  let B : ℕ := Nat.log 2 (Nat.ceil (V₀ / (2 * wd.φ_dec)) + 1) + 1
  have hcdeg_pos : 0 < 2 * wd.c_deg := by linarith [hw.c_deg_ge]
  have hr_nn : 0 ≤ r := by positivity
  have hr_lt_one : r < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hV₀_nn : 0 ≤ V₀ := by
    have : 0 ≤ wd.c_deg := by linarith [hw.c_deg_ge]
    positivity
  have h2φ_pos : 0 < 2 * wd.φ_dec := by linarith [hw.φ_dec_pos]
  have hbern : r ^ (K * B) * V₀ < 2 * wd.φ_dec :=
    bernoulli_round_lt hcdeg_pos hV₀_nn h2φ_pos
  have hKB_ge : ∀ (st : Task2State tools.pathDS.State),
      (∀ eW < wd.j0Edges.length, (st.embWJ eW).isSome = true) →
      volWRem wd st ≤ r ^ st.η₁ * V₀ → task2OuterCond wd st = true → st.η₁ < K * B := by
    intro st hj0 hvol hcond
    unfold task2OuterCond at hcond
    rw [List.any_eq_true] at hcond
    rcases hcond with ⟨eW, heW_range, hnone⟩
    have heW_m : eW < wd.W.m := List.mem_range.mp heW_range
    have hnone' : st.embWJ eW = none := Option.isNone_iff_eq_none.mp hnone
    have hj0_le : wd.j0Edges.length ≤ eW := by
      by_contra hlt
      have hs := hj0 eW (Nat.lt_of_not_ge hlt)
      rw [hnone'] at hs
      simp at hs
    have h2φ_le_w : 2 * wd.φ_dec ≤ wd.wW eW := wW_ge_two_phi_comp tools H' J embJH hw hj0_le heW_m
    have heW_mem : eW ∈ unembeddedSet1 wd st := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr heW_m, hnone⟩
    have hw_le_vol : wd.wW eW ≤ volWRem wd st := by
      unfold volWRem
      exact Finset.single_le_sum
        (fun e' he' => (wW_pos tools H' J embJH hw (Finset.mem_range.mp (Finset.mem_filter.mp he').1)).le)
        heW_mem
    by_contra hge
    have hle_KB : K * B ≤ st.η₁ := Nat.le_of_not_lt hge
    have hpow : r ^ st.η₁ ≤ r ^ (K * B) := pow_le_pow_of_le_one hr_nn hr_lt_one.le hle_KB
    have hcontr : 2 * wd.φ_dec ≤ r ^ (K * B) * V₀ :=
      le_trans h2φ_le_w (le_trans hw_le_vol (le_trans hvol (mul_le_mul_of_nonneg_right hpow hV₀_nn)))
    linarith
  let P : Task2State tools.pathDS.State → Prop := fun st =>
    Task2LoopInv tools.pathDS H' J embJH wd st ∧
    1 ≤ st.η₁ ∧
    st.η₁ ≤ eta1Bound wd J ∧
    volWRem wd st ≤ r ^ st.η₁ * V₀ ∧
    st.deleteCountJ ≤ st.η₁ * J.m ∧
    st.innerIters1 ≤ st.η₁ * H'.n ∧
    (0 < wd.τ₁ → (st.innerIters1 : ℝ) ≤ (st.getPathCountJ : ℝ) * M) ∧
    (wd.τ₁ = 0 → st.innerIters1 = 0)
  let s₀ : Task2State tools.pathDS.State := task2Init J wd
  let s₁ := task2Round tools.pathDS H' J embJH wd s₀
  have hP₁ : P s₁ := by
    have hs₀ := task2Init_entryInv tools H' J embJH hJ hembJH hw
    obtain ⟨hη₁, hloop₁, hrel₁, _, _⟩ := invariant_1 tools H' J embJH hJ hembJH hw hs₀
    obtain ⟨_, hvol₁, hdel₁, hinnerH₁, hinnerτ₁⟩ := claim_8_7 tools H' J embJH hJ hembJH hw hs₀
    have hs₀_η : s₀.η₁ = 0 := rfl
    have hs₀_del : s₀.deleteCountJ = 0 := rfl
    have hs₀_inn : s₀.innerIters1 = 0 := rfl
    have hs₀_gp : s₀.getPathCountJ = 0 := rfl
    have hη_one : s₁.η₁ = 1 := by rw [hη₁, hs₀_η]
    have hvol₁' : volWRem wd s₁ ≤ r ^ s₁.η₁ * V₀ := by
      have hinit_vol := volWRem_task2Init_le tools H' J embJH hJ hembJH hw
      have hle : r * volWRem wd s₀ ≤ r * V₀ := mul_le_mul_of_nonneg_left hinit_vol hr_nn
      rw [hη_one, pow_one]
      exact le_trans hvol₁ hle
    have hemb_card : (newlyEmbeddedSet1 wd s₀ s₁).card = s₁.getPathCountJ := by
      have hp := (unembeddedSet1_partition wd s₀ s₁ hrel₁.emb_mono).2.2.2.2
      have h0 : unembeddedCount1 wd s₀ = wd.W.m - wd.j0Edges.length := by
        have hu := hs₀.unemb_eq
        change s₀.getPathCountJ + unembeddedCount1 wd s₀ = wd.W.m - wd.j0Edges.length at hu
        rw [hs₀_gp, Nat.zero_add] at hu
        exact hu
      have h1 : s₁.getPathCountJ + unembeddedCount1 wd s₁ = wd.W.m - wd.j0Edges.length :=
        hloop₁.unemb_eq
      omega
    refine ⟨hloop₁, by omega, ?_, hvol₁', ?_, ?_, ?_, ?_⟩
    · rw [hη_one]
      dsimp only [eta1Bound]
      omega
    · rw [hη_one, one_mul]
      change s₁.deleteCountJ - s₀.deleteCountJ ≤ J.m at hdel₁
      rw [hs₀_del] at hdel₁
      omega
    · rw [hη_one, one_mul]
      change s₁.innerIters1 - s₀.innerIters1 ≤ H'.n at hinnerH₁
      rw [hs₀_inn] at hinnerH₁
      omega
    · intro hτ
      have h := hinnerτ₁ hτ
      change ((s₁.innerIters1 - s₀.innerIters1 : ℕ) : ℝ) ≤
        ((newlyEmbeddedSet1 wd s₀ s₁).card : ℝ) * M at h
      rw [hs₀_inn, Nat.sub_zero, hemb_card] at h
      exact h
    · intro hτ0
      have hcomps0 : wd.comps = [] := by
        rw [← List.length_eq_zero_iff]
        by_contra hne
        have hcomp_pos : 0 < wd.comps.length := Nat.pos_of_ne_zero hne
        obtain ⟨hmaxD, hlenJ⟩ := nonloop_edge_witness_bounds tools H' J embJH hJ hembJH hw hcomp_pos
        have hτ₁_eq : wd.τ₁ = 2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := rfl
        have h1 : (0 : ℝ) < (length J embJH : ℝ) := by exact_mod_cast hlenJ
        have h2 : (0 : ℝ) < (maxDeg J : ℝ) := by exact_mod_cast hmaxD
        have h3 : 0 ≤ vcong J H' (fun _ => 1) embJH := vcong_nonneg J H' (fun _ => 1) embJH
        have h4 : 0 < wd.φ_ds := hw.φ_ds_pos
        have h5 : 0 < wd.γ_ExpPath := lt_of_lt_of_le (by positivity) hw.γ_ExpPath_ge
        have h6 : 0 < wd.γ_del := lt_of_lt_of_le (by norm_num) hw.γ_del_ge
        have hpos : 0 < wd.τ₁ := by rw [hτ₁_eq]; positivity
        linarith
      have hWm_eq : wd.W.m = wd.j0Edges.length := by
        have hwW := hw.W_m_eq
        simpa [wd, hcomps0] using hwW
      let dsInit := wd.comps.map fun c => tools.pathDS.init wd.φ_dec wd.J0_strip.m c.J_sub
      let s1 : Task2State tools.pathDS.State :=
        { s₀ with
          η₁ := s₀.η₁ + 1
          dsJ := dsInit
          processedVerts := ∅
          initCountJ := s₀.initCountJ + wd.comps.length
          initEdgesJ := s₀.initEdgesJ + (wd.comps.map fun c => c.J_sub.m).sum }
      have hcond_false : task2MiddleCond tools.pathDS wd s1 = false := by
        unfold task2MiddleCond findReadyWEdge
        have hnil : ∀ f : ℕ → Option (ℕ × ℕ × ℕ),
            (∀ eW < wd.W.m, f eW = none) →
            ((List.range wd.W.m).filterMap f).head?.isSome = false := by
          intro f hf
          have h0 : (List.range wd.W.m).filterMap f = [] := by
            rw [List.filterMap_eq_nil_iff]
            intro eW heW
            exact hf eW (List.mem_range.mp heW)
          rw [h0]
          rfl
        apply hnil
        intro eW heW
        have heW_j0 : eW < wd.j0Edges.length := hWm_eq ▸ heW
        have hsome : (s1.embWJ eW).isSome = true := hs₀.j0_embedded eW heW_j0
        have hnone_f : (s1.embWJ eW).isNone = false := by
          cases h : s1.embWJ eW <;> simp [h] at hsome ⊢
        simp [s1, hnone_f]
      have hs₁_eq : s₁ = s1 := by
        change whileFuel wd.W.m (task2MiddleCond tools.pathDS wd)
          (task2MiddleStep tools.pathDS H' J embJH wd) s1 = s1
        cases wd.W.m with
        | zero => rfl
        | succ k => simp [whileFuel, hcond_false]
      rw [hs₁_eq]
      exact hs₀_inn
  have hstep : ∀ st, P st → task2OuterCond wd st = true →
      P (task2Round tools.pathDS H' J embJH wd st) ∧
      unembeddedCount1 wd (task2Round tools.pathDS H' J embJH wd st) < unembeddedCount1 wd st := by
    intro st ⟨hloop, hη_ge, _, hvol, hdel, hinnerH, hinnerτ, _⟩ hcond
    obtain ⟨hη', hloop', hrel', _, _⟩ := invariant_1 tools H' J embJH hJ hembJH hw hloop.toEntryInv
    obtain ⟨_, hvol', hdel', hinnerH', hinnerτ'⟩ := claim_8_7 tools H' J embJH hJ hembJH hw hloop.toEntryInv
    let st' := task2Round tools.pathDS H' J embJH wd st
    have hη_st' : st'.η₁ = st.η₁ + 1 := hη'
    have hvol_st' : volWRem wd st' ≤ r * volWRem wd st := hvol'
    have hdel_st' : st'.deleteCountJ - st.deleteCountJ ≤ J.m := hdel'
    have hinnerH_st' : st'.innerIters1 - st.innerIters1 ≤ H'.n := hinnerH'
    -- Since task2OuterCond wd st = true, there is a component edge, hence wd.comps.length ≥ 1 and 0 < wd.τ₁
    have hτpos : 0 < wd.τ₁ := by
      have hcond' := hcond
      unfold task2OuterCond at hcond'
      rw [List.any_eq_true] at hcond'
      rcases hcond' with ⟨eW, heW_r, hnone⟩
      have heWm : eW < wd.W.m := List.mem_range.mp heW_r
      have hnone' : st.embWJ eW = none := Option.isNone_iff_eq_none.mp hnone
      have hj0_ge : wd.j0Edges.length ≤ eW := by
        by_contra hlt
        exact hlt (Nat.le_of_not_lt fun h => by
          have hs := hloop.j0_embedded eW h
          rw [hnone'] at hs; simp at hs)
      rcases W_edge_cases tools H' J embJH heWm with hlt0 | ⟨ci, hci, _, _, _⟩
      · exact absurd hlt0 (Nat.not_lt_of_ge hj0_ge)
      · obtain ⟨hmaxD, hlenJ⟩ := nonloop_edge_witness_bounds tools H' J embJH hJ hembJH hw hci
        have hτ₁_eq : wd.τ₁ = 2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := rfl
        rw [hτ₁_eq]
        have h1 : (0 : ℝ) < (length J embJH : ℝ) := by exact_mod_cast hlenJ
        have h2 : (0 : ℝ) < (maxDeg J : ℝ) := by exact_mod_cast hmaxD
        have h3 : 0 ≤ vcong J H' (fun _ => 1) embJH := vcong_nonneg J H' (fun _ => 1) embJH
        have h4 : 0 < wd.φ_ds := hw.φ_ds_pos
        have h5 : 0 < wd.γ_ExpPath := lt_of_lt_of_le (by positivity) hw.γ_ExpPath_ge
        have h6 : 0 < wd.γ_del := lt_of_lt_of_le (by norm_num) hw.γ_del_ge
        positivity
    have hlt_KB : st.η₁ < K * B := hKB_ge st hloop.j0_embedded hvol hcond
    have hη_bound' : st'.η₁ ≤ eta1Bound wd J := by
      have hle_kb : st'.η₁ ≤ K * B := by omega
      have heta : eta1Bound wd J = 1 + K * B := rfl
      omega
    have hvol_pow' : volWRem wd st' ≤ r ^ st'.η₁ * V₀ := by
      rw [hη_st', pow_succ']
      calc volWRem wd st' ≤ r * volWRem wd st := hvol_st'
        _ ≤ r * (r ^ st.η₁ * V₀) := mul_le_mul_of_nonneg_left hvol hr_nn
        _ = r * r ^ st.η₁ * V₀ := by ring
    have hdel_le_prev : st.deleteCountJ ≤ st'.deleteCountJ := by
      have hdeq := hrel'.del_eq
      change st'.deleteCountJ = st.deleteCountJ + _ at hdeq
      omega
    have hdel_tot' : st'.deleteCountJ ≤ st'.η₁ * J.m := by
      rw [hη_st', Nat.add_mul, one_mul]
      omega
    have hinner_le_prev : st.innerIters1 ≤ st'.innerIters1 := by
      have hieq := hrel'.inner_eq
      change st'.innerIters1 = st.innerIters1 + _ at hieq
      omega
    have hinnerH_tot' : st'.innerIters1 ≤ st'.η₁ * H'.n := by
      rw [hη_st', Nat.add_mul, one_mul]
      omega
    have hinner_tau' : (st'.innerIters1 : ℝ) ≤ (st'.getPathCountJ : ℝ) * M := by
      have hprev := hinnerτ hτpos
      have hinc := hinnerτ' hτpos
      have hemb_card : (newlyEmbeddedSet1 wd st st').card = st'.getPathCountJ - st.getPathCountJ := by
        have hp := (unembeddedSet1_partition wd st st' hrel'.emb_mono).2.2.2.2
        have h0 : st.getPathCountJ + unembeddedCount1 wd st = wd.W.m - wd.j0Edges.length :=
          hloop.unemb_eq
        have h1 : st'.getPathCountJ + unembeddedCount1 wd st' = wd.W.m - wd.j0Edges.length :=
          hloop'.unemb_eq
        omega
      have hgp_le : st.getPathCountJ ≤ st'.getPathCountJ := by
        have h0 : st.getPathCountJ + unembeddedCount1 wd st = wd.W.m - wd.j0Edges.length :=
          hloop.unemb_eq
        have h1 : st'.getPathCountJ + unembeddedCount1 wd st' = wd.W.m - wd.j0Edges.length :=
          hloop'.unemb_eq
        have hsub := (unembeddedSet1_partition wd st st' hrel'.emb_mono).1
        have hc : unembeddedCount1 wd st' ≤ unembeddedCount1 wd st := Finset.card_le_card hsub
        omega
      rw [hemb_card] at hinc
      have hsplit_inn : (st'.innerIters1 : ℝ) = (st.innerIters1 : ℝ) + ((st'.innerIters1 - st.innerIters1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.add_sub_of_le hinner_le_prev).symm
      have hsplit_gp : (st'.getPathCountJ : ℝ) = (st.getPathCountJ : ℝ) + ((st'.getPathCountJ - st.getPathCountJ : ℕ) : ℝ) := by
        exact_mod_cast (Nat.add_sub_of_le hgp_le).symm
      rw [hsplit_inn, hsplit_gp]
      linarith
    have hvol_pos : 0 < volWRem wd st := by
      unfold task2OuterCond at hcond
      rw [List.any_eq_true] at hcond
      rcases hcond with ⟨eW, heW_r, hnone⟩
      have heWm := List.mem_range.mp heW_r
      have hw_pos := wW_pos tools H' J embJH hw heWm
      have heW_mem : eW ∈ unembeddedSet1 wd st := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr heWm, hnone⟩
      unfold volWRem
      exact lt_of_lt_of_le hw_pos (Finset.single_le_sum
        (fun e' he' => (wW_pos tools H' J embJH hw (Finset.mem_range.mp (Finset.mem_filter.mp he').1)).le)
        heW_mem)
    have hvol_lt : volWRem wd st' < volWRem wd st :=
      lt_of_le_of_lt hvol_st' (mul_lt_of_lt_one_left hvol_pos hr_lt_one)
    have hssub : unembeddedSet1 wd st' ⊂ unembeddedSet1 wd st := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨(unembeddedSet1_partition wd st st' hrel'.emb_mono).1, ?_⟩
      intro heq
      have hveq : volWRem wd st' = volWRem wd st := by simp [volWRem, heq]
      linarith
    exact ⟨⟨hloop', by dsimp only [st'] at hη_st'; rw [hη_st']; omega,
      hη_bound', hvol_pow', hdel_tot', hinnerH_tot', fun _ => hinner_tau',
      fun h0 => absurd h0 hτpos.ne'⟩, Finset.card_lt_card hssub⟩
  have hs_final_eq : s_final = whileFuel wd.W.m (task2OuterCond wd)
      (task2Round tools.pathDS H' J embJH wd) s₁ := rfl
  have hP_final : P s_final :=
    whileFuel_inv P (task2OuterCond wd) (task2Round tools.pathDS H' J embJH wd)
      (fun st hp hc => (hstep st hp hc).1) wd.W.m s₁ hP₁
  have hdone : task2OuterCond wd s_final = false :=
    whileFuel_done P (unembeddedCount1 wd) (task2OuterCond wd)
      (task2Round tools.pathDS H' J embJH wd) hstep wd.W.m s₁ hP₁
      (by simp only [unembeddedCount1, unembeddedSet1]; exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _))
  rcases hP_final with ⟨hloop_f, hη_ge_f, hη_le_f, _, hdel_f, hinnerH_f, hinnerτ_f, hinner0_f⟩
  have hinner_all : (s_final.innerIters1 : ℝ) ≤ (s_final.getPathCountJ : ℝ) * M := by
    rcases lt_or_eq_of_le hw.τ₁_nonneg with hpos | hzero
    · exact hinnerτ_f hpos
    · have h1 : s_final.innerIters1 = 0 := hinner0_f hzero.symm
      rw [h1, Nat.cast_zero]
      have hM_nn : 0 ≤ M := by
        have hφ_pos : 0 < wd.φ_ds := hw.φ_ds_pos
        have hγ_nn : 0 ≤ wd.γ_ExpPath := le_trans (by positivity) hw.γ_ExpPath_ge
        positivity
      exact mul_nonneg (Nat.cast_nonneg _) hM_nn
  exact ⟨hdone, hloop_f, hη_ge_f, hη_le_f, hdel_f, hinnerH_f, hinner_all⟩

/-- **Corollary 8.8** (`spanner.tex`, page 44):
At the end of Task 2, `embWJ := partialToWalk s_final.embWJ` is a complete valid embedding of
`wd.W` into `J` with length at most `γ_ExpPath` and composed vertex congestion at most
`(s_final.η₁ + 1 / 2) * wd.τ₁ ≤ (eta1Bound wd J + 1 / 2) * wd.τ₁`. -/
theorem corollary_8_8 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s_final := task2 tools.pathDS H' J embJH wd
    let embWJ := partialToWalk s_final.embWJ
    IsEmbedding wd.W J embWJ ∧
    vcong wd.W H' wd.wW (compose J embJH embWJ) ≤ (s_final.η₁ + 1 / 2 : ℝ) * wd.τ₁ ∧
    vcong wd.W H' wd.wW (compose J embJH embWJ) ≤ ((eta1Bound wd J : ℝ) + 1 / 2) * wd.τ₁ ∧
    (length wd.W embWJ : ℝ) ≤ wd.γ_ExpPath := by
  intro wd s_final embWJ
  obtain ⟨hdone, hloop, _, hη_le, _, _, _⟩ := task2_spec tools H' J embJH hJ hembJH hw
  have hall : ∀ eW < wd.W.m, (s_final.embWJ eW).isSome = true :=
    (task2OuterCond_false_iff wd s_final).mp hdone
  have hemb : IsEmbedding wd.W J embWJ := by
    refine ⟨hloop.partial_emb.1, fun j hj => ?_⟩
    rcases Option.isSome_iff_exists.mp (hall j hj) with ⟨P, hP⟩
    have hpw : embWJ j = P := by simp [embWJ, partialToWalk, hP]
    rw [hpw]
    exact hloop.partial_emb.2 j hj P hP
  have hvcong : vcong wd.W H' wd.wW (compose J embJH embWJ) ≤ (s_final.η₁ + 1 / 2 : ℝ) * wd.τ₁ := by
    rw [vcong_le_iff]
    refine ⟨by have := hw.τ₁_nonneg; positivity, fun x hx => hloop.vcong_half x hx⟩
  have hvcong_eta :
      vcong wd.W H' wd.wW (compose J embJH embWJ) ≤ ((eta1Bound wd J : ℝ) + 1 / 2) * wd.τ₁ := by
    have hη_r : (s_final.η₁ : ℝ) ≤ (eta1Bound wd J : ℝ) := by exact_mod_cast hη_le
    have hτ := hw.τ₁_nonneg
    calc vcong wd.W H' wd.wW (compose J embJH embWJ)
        ≤ (s_final.η₁ + 1 / 2 : ℝ) * wd.τ₁ := hvcong
      _ ≤ ((eta1Bound wd J : ℝ) + 1 / 2) * wd.τ₁ := by nlinarith
  have hlen : (length wd.W embWJ : ℝ) ≤ wd.γ_ExpPath := by
    have hγ_nn : 0 ≤ wd.γ_ExpPath := le_trans (by have := hw.φ_ds_pos; positivity) hw.γ_ExpPath_ge
    have hnat : length wd.W embWJ ≤ Nat.floor wd.γ_ExpPath := by
      rw [length_le_iff]
      intro j hj
      exact Nat.le_floor (hloop.emb_len j hj)
    exact le_trans (by exact_mod_cast hnat) (Nat.floor_le hγ_nn)
  exact ⟨hemb, hvcong, hvcong_eta, hlen⟩

/-- Task 2 counter and work bounds on `s_final = task2 tools.pathDS H' J embJH wd`. -/
theorem task2_stats {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s_final := task2 tools.pathDS H' J embJH wd
    1 ≤ s_final.η₁ ∧
    s_final.η₁ ≤ eta1Bound wd J ∧
    wd.comps.length ≤ J.m ∧
    s_final.initCountJ = s_final.η₁ * wd.comps.length ∧
    s_final.initEdgesJ = s_final.η₁ * (wd.comps.map fun c => c.J_sub.m).sum ∧
    s_final.initEdgesJ ≤ s_final.η₁ * J.m ∧
    s_final.getPathCountJ = wd.W.m - wd.j0Edges.length ∧
    s_final.getPathCountJ ≤ wd.W.m ∧
    s_final.middleIters1 = s_final.getPathCountJ ∧
    s_final.deleteCountJ ≤ s_final.η₁ * J.m ∧
    (s_final.vcongUpdates : ℝ) ≤
      (s_final.getPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) ∧
    s_final.innerIters1 ≤ s_final.η₁ * H'.n ∧
    (s_final.innerIters1 : ℝ) ≤
      (s_final.getPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by
  intro wd s_final
  obtain ⟨hdone, hloop, hη_ge, hη_le, hdel, hinnerH, hinner_all⟩ :=
    task2_spec tools H' J embJH hJ hembJH hw
  have hunemb0 : unembeddedCount1 wd s_final = 0 := by
    unfold unembeddedCount1
    rw [(task2OuterCond_false_iff_unemb wd s_final).mp hdone, Finset.card_empty]
  have hgp : s_final.getPathCountJ = wd.W.m - wd.j0Edges.length := by
    have h := hloop.unemb_eq
    rw [hunemb0, Nat.add_zero] at h
    exact h
  have hJ0_le : wd.J0_strip.m ≤ J.m := by
    simp only [wd, buildWitness, stripLoops, Graph.m, List.length_map]
    exact (List.length_filter_le _ _).trans_eq List.length_range
  have hsum_Jm : (wd.comps.map fun c => c.J_sub.m).sum ≤ J.m := by
    have h1 := sum_comp_j_m_le tools H' J embJH hw
    change wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m at h1
    exact le_trans (Nat.le_add_left _ _) (le_trans h1 hJ0_le)
  have hcomps_le_Jm : wd.comps.length ≤ J.m := by
    have hlen_le_sum : ∀ cs : List CompInfo, (∀ c ∈ cs, 1 ≤ c.J_sub.m) →
        cs.length ≤ (cs.map fun c => c.J_sub.m).sum := by
      intro cs
      induction cs with
      | nil => intro _; simp
      | cons c rest ih =>
        intro hcs
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have h1 := hcs c List.mem_cons_self
        have h2 := ih fun x hx => hcs x (List.mem_cons_of_mem c hx)
        omega
    have hall_pos : ∀ c ∈ wd.comps, 1 ≤ c.J_sub.m := by
      intro c hc
      obtain ⟨ci, hci, hc_eq⟩ := List.mem_iff_getElem.mp hc
      exact hc_eq ▸ (hw.comp_props ci hci).2.2.2.2.2.2.2.1
    exact le_trans (hlen_le_sum wd.comps hall_pos) hsum_Jm
  have hinitE_le : s_final.initEdgesJ ≤ s_final.η₁ * J.m := by
    rw [hloop.initEdges_eq]
    exact Nat.mul_le_mul_left _ hsum_Jm
  exact ⟨hη_ge, hη_le, hcomps_le_Jm, hloop.initCount_eq, hloop.initEdges_eq, hinitE_le,
    hgp, by omega, hloop.middle_eq, hdel, hloop.vcongUpdates_le, hinnerH, hinner_all⟩

end MinCostFlow.Spanner


