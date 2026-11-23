module

public import MinCostFlow.Spanner.Analysis2Base

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Task 3 Analysis: Claim 8.9, Task 3 Spec, and Corollary 8.10

Proves `claim_8_9` (Claim 8.9, page 44), `task3_spec`, `corollary_8_10`
(Corollary 8.10, page 44), and `task3_stats`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-- **Claim 8.9** (`spanner.tex`, page 44):
In one round `s → s'` (`s'.η₂ = s.η₂ + 1`) ending with `task3MiddleCond = false`:
1. `unembeddedCount2 J s' ≤ 2 * E_embed.card`, and therefore `3 * unembeddedCount2 J s' ≤ 2 * unembeddedCount2 J s`.
2. Deletions and inner-loop iterations are bounded by `E_embed.card * γ_ExpPath` and by `W.m`. -/
theorem claim_8_9 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s s' : Task3State tools.pathDS.State}
    (hs : Task3RoundEntryInv J (buildWitness tools H' J embJH) s)
    (hs' : Task3LoopInv tools.pathDS J (buildWitness tools H' J embJH) s')
    (hrel : Task3RoundRel tools.pathDS J (buildWitness tools H' J embJH) s s')
    (hmid : task3MiddleCond tools.pathDS J (buildWitness tools H' J embJH) s' = false)
    (heta : s'.η₂ = s.η₂ + 1) :
    let wd := buildWitness tools H' J embJH
    let E_embed := (Finset.range J.m).filter fun eJ =>
      (s.embJW eJ).isNone = true ∧ (s'.embJW eJ).isSome = true
    unembeddedCount2 J s' ≤ 2 * E_embed.card ∧
    3 * unembeddedCount2 J s' ≤ 2 * unembeddedCount2 J s ∧
    ((s'.innerIters2 - s.innerIters2 : ℕ) : ℝ) ≤ (E_embed.card : ℝ) * wd.γ_ExpPath ∧
    s'.innerIters2 - s.innerIters2 ≤ wd.W.m := by
  intro wd E_embed
  let dsDef := tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
  let E_del_W : Finset ℕ := (Finset.range wd.comps.length).biUnion (delWSet tools.pathDS wd s' hs'.ds_len)
  have hdel_disj : Set.PairwiseDisjoint (Finset.range wd.comps.length : Set ℕ)
      (delWSet tools.pathDS wd s' hs'.ds_len) := by
    intro ci₁ h1 ci₂ h2 hne S hS₁ hS₂ eW heW
    have hci₁ := Finset.mem_range.mp h1
    have hci₂ := Finset.mem_range.mp h2
    have hm1 := (delWSet_spec tools H' J embJH hw hs'.toTask3CoreInv hci₁).2 eW (hS₁ heW)
    have hm2 := (delWSet_spec tools H' J embJH hw hs'.toTask3CoreInv hci₂).2 eW (hS₂ heW)
    rcases hm1 with ⟨hw1_le, hw1_lt, _⟩
    rcases hm2 with ⟨hw2_le, hw2_lt, _⟩
    rcases Nat.lt_trichotomy ci₁ ci₂ with hlt | heq | hgt
    · have hadj := compsAligned_adjacent hw.aligned ci₁ ci₂ hci₁ hci₂ hlt
      omega
    · exact False.elim (hne heq)
    · have hadj := compsAligned_adjacent hw.aligned ci₂ ci₁ hci₂ hci₁ hgt
      omega
  have hE_del_sub : E_del_W ⊆ Finset.range wd.W.m := by
    intro eW heW
    rcases Finset.mem_biUnion.mp heW with ⟨ci, hci_r, heW_ci⟩
    have hci := Finset.mem_range.mp hci_r
    exact Finset.mem_range.mpr ((delWSet_spec tools H' J embJH hw hs'.toTask3CoreInv hci).2 eW heW_ci).2.2.1
  have hE_del_card : E_del_W.card = s'.innerIters2 - s.innerIters2 := by
    have h1 : E_del_W.card =
        ∑ ci ∈ Finset.range wd.comps.length, (delWSet tools.pathDS wd s' hs'.ds_len ci).card :=
      Finset.card_biUnion hdel_disj
    have h2 : ∑ ci ∈ Finset.range wd.comps.length, (delWSet tools.pathDS wd s' hs'.ds_len ci).card =
        ∑ ci ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card := by
      refine Finset.sum_congr rfl fun ci hci_r => ?_
      have hci := Finset.mem_range.mp hci_r
      have hci_ds : ci < s'.dsW.length := by rw [hs'.ds_len]; exact hci
      rw [List.getD_eq_getElem _ _ hci_ds]
      exact (delWSet_spec tools H' J embJH hw hs'.toTask3CoreInv hci).1
    have h3 : s'.innerIters2 = s.innerIters2 +
        ∑ ci ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card :=
      hrel.inner_eq
    omega
  have hdel_le_Wm : s'.innerIters2 - s.innerIters2 ≤ wd.W.m := by
    rw [← hE_del_card]
    simpa [Finset.card_range] using Finset.card_le_card hE_del_sub
  have hwSum_eq :
      ∑ ci ∈ Finset.range wd.comps.length,
        ((tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card : ℝ) *
          (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) =
      ∑ eW ∈ E_del_W, wd.wW eW := by
    symm
    rw [Finset.sum_biUnion hdel_disj]
    refine Finset.sum_congr rfl fun ci hci_r => ?_
    have hci := Finset.mem_range.mp hci_r
    have hsp := delWSet_spec tools H' J embJH hw hs'.toTask3CoreInv hci
    have hconst : ∑ eW ∈ delWSet tools.pathDS wd s' hs'.ds_len ci, wd.wW eW =
        ∑ _eW ∈ delWSet tools.pathDS wd s' hs'.ds_len ci,
          (wd.φ_dec * (2 ^ (wd.comps[ci]'hci).level : ℝ)) :=
      Finset.sum_congr rfl fun eW heW => (hsp.2 eW heW).2.2.2.1
    have hci_ds : ci < s'.dsW.length := by rw [hs'.ds_len]; exact hci
    rw [hconst, Finset.sum_const, nsmul_eq_mul, hsp.1,
      List.getD_eq_getElem _ _ hci, List.getD_eq_getElem _ _ hci_ds]
  have hU_le : (unembeddedCount2 J s' : ℝ) ≤ (wd.γ_del / wd.φ_ds) * ∑ eW ∈ E_del_W, wd.wW eW := by
    rw [← hwSum_eq]
    exact unembeddedSet2_le_sum_comp tools H' J embJH hJ hw hs'.toTask3CoreInv hmid
  have heW_gap : ∀ eW ∈ E_del_W,
      wd.τ₂ / 2 ≤ econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) eW -
        econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW := by
    intro eW heW
    rcases Finset.mem_biUnion.mp heW with ⟨ci, hci_r, heW_ci⟩
    have hci := Finset.mem_range.mp hci_r
    have hsp := (delWSet_spec tools H' J embJH hw hs'.toTask3CoreInv hci).2 eW heW_ci
    rcases hsp with ⟨_, _, heWm, _, eL, heL_del, rfl⟩
    have hhi : (s'.η₂ : ℝ) * wd.τ₂ ≤
        econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) ((wd.comps[ci]'hci).wStart + eL) :=
      (hs'.deleted_spec ci hci eL heL_del).2
    have hlo : econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) ((wd.comps[ci]'hci).wStart + eL) ≤
        (s.η₂ + 1 / 2 : ℝ) * wd.τ₂ :=
      hs.econg_half _ heWm
    have heta_r : (s'.η₂ : ℝ) = (s.η₂ : ℝ) + 1 := by
      rw [heta]; push_cast; rfl
    dsimp only [wd] at hlo ⊢
    rw [heta_r] at hhi
    linarith
  have hW_gap_sum : (wd.τ₂ / 2) * (∑ eW ∈ E_del_W, wd.wW eW) ≤
      (E_embed.card : ℝ) * wd.γ_ExpPath := by
    have hstep1 : (wd.τ₂ / 2) * (∑ eW ∈ E_del_W, wd.wW eW) ≤
        ∑ eW ∈ E_del_W,
          wd.wW eW * (econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) eW -
            econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun eW heW => ?_
      have heWm := Finset.mem_range.mp (hE_del_sub heW)
      have hw_nn := (wW_pos tools H' J embJH hw heWm).le
      rw [mul_comm (wd.τ₂ / 2)]
      exact mul_le_mul_of_nonneg_left (heW_gap eW heW) hw_nn
    have hstep2 :
        ∑ eW ∈ E_del_W,
          wd.wW eW * (econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) eW -
            econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW) ≤
        ∑ eW ∈ Finset.range wd.W.m,
          wd.wW eW * (econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) eW -
            econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hE_del_sub fun eW heWm_r _ => ?_
      have heWm := Finset.mem_range.mp heWm_r
      have hw_pos := wW_pos tools H' J embJH hw heWm
      rw [econgAt_mono_diff J wd.wW s.embJW s'.embJW hrel.emb_mono eW, mul_div_cancel₀ _ hw_pos.ne']
      exact Nat.cast_nonneg _
    have hstep3 :
        ∑ eW ∈ Finset.range wd.W.m,
          wd.wW eW * (econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) eW -
            econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW) =
        ∑ eJ ∈ E_embed,
          (((Finset.range wd.W.m).filter fun eW => eW ∈ (partialToWalk s'.embJW eJ).edges).card : ℝ) := by
      have hcongr : ∀ eW ∈ Finset.range wd.W.m,
          wd.wW eW * (econgAt J (fun _ => 1) wd.wW (partialToWalk s'.embJW) eW -
            econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW) =
          ∑ eJ ∈ E_embed, if eW ∈ (partialToWalk s'.embJW eJ).edges then (1 : ℝ) else 0 := by
        intro eW heWm_r
        have hw_pos := wW_pos tools H' J embJH hw (Finset.mem_range.mp heWm_r)
        rw [econgAt_mono_diff J wd.wW s.embJW s'.embJW hrel.emb_mono eW, mul_div_cancel₀ _ hw_pos.ne']
        have hfilt : (Finset.range J.m).filter (fun eJ =>
            (s.embJW eJ).isNone = true ∧ (s'.embJW eJ).isSome = true ∧
              eW ∈ (partialToWalk s'.embJW eJ).edges) =
            E_embed.filter (fun eJ => eW ∈ (partialToWalk s'.embJW eJ).edges) := by
          ext eJ
          simp only [E_embed, Finset.mem_filter, Finset.mem_range]
          tauto
        rw [hfilt, ← mul_one ((E_embed.filter _).card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const,
          Finset.sum_filter]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_comm]
      refine Finset.sum_congr rfl fun eJ _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hstep4 :
        ∑ eJ ∈ E_embed,
          (((Finset.range wd.W.m).filter fun eW => eW ∈ (partialToWalk s'.embJW eJ).edges).card : ℝ) ≤
        (E_embed.card : ℝ) * wd.γ_ExpPath := by
      calc ∑ eJ ∈ E_embed,
            (((Finset.range wd.W.m).filter fun eW => eW ∈ (partialToWalk s'.embJW eJ).edges).card : ℝ)
          ≤ ∑ eJ ∈ E_embed, ((partialToWalk s'.embJW eJ).edges.length : ℝ) := by
            refine Finset.sum_le_sum fun eJ _ => ?_
            exact_mod_cast le_trans (Finset.card_le_card fun eW heW => by
              rw [Finset.mem_filter] at heW
              exact List.mem_toFinset.mpr heW.2) (List.toFinset_card_le _)
        _ ≤ ∑ _eJ ∈ E_embed, wd.γ_ExpPath := by
            refine Finset.sum_le_sum fun eJ heJ => ?_
            have heJm := Finset.mem_range.mp (Finset.mem_filter.mp heJ).1
            exact hs'.emb_len eJ heJm
        _ = (E_embed.card : ℝ) * wd.γ_ExpPath := by rw [Finset.sum_const, nsmul_eq_mul]
    exact le_trans hstep1 (le_trans hstep2 (le_trans (le_of_eq hstep3) hstep4))
  have hγE_pos : 0 < wd.γ_ExpPath :=
    lt_of_lt_of_le (div_pos one_pos hw.φ_ds_pos) hw.γ_ExpPath_ge
  have hU_card_le : unembeddedCount2 J s' ≤ 2 * E_embed.card := by
    have hreal : (unembeddedCount2 J s' : ℝ) ≤ 2 * (E_embed.card : ℝ) :=
      claim_8_9_algebra hγE_pos hU_le rfl hW_gap_sum
    exact_mod_cast hreal
  have hpart : unembeddedCount2 J s' + E_embed.card = unembeddedCount2 J s := by
    have hdisj : Disjoint (unembeddedSet2 J s') E_embed := by
      rw [Finset.disjoint_left]
      intro eJ h1 h2
      simp only [unembeddedSet2, E_embed, Finset.mem_filter, Option.isNone_iff_eq_none,
        Option.isSome_iff_ne_none] at h1 h2
      exact h2.2.2 h1.2
    have hunion : unembeddedSet2 J s' ∪ E_embed = unembeddedSet2 J s := by
      ext eJ
      simp only [Finset.mem_union, unembeddedSet2, E_embed, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hm, h1⟩ | ⟨hm, h0, _⟩)
        · refine ⟨hm, ?_⟩
          rcases hrel.emb_mono eJ hm with h0 | h01
          · exact Option.isNone_iff_eq_none.mpr h0
          · rw [← h01]; exact h1
        · exact ⟨hm, h0⟩
      · rintro ⟨hm, h0⟩
        by_cases h1 : (s'.embJW eJ).isNone = true
        · exact Or.inl ⟨hm, h1⟩
        · have hsome : (s'.embJW eJ).isSome = true := by
            cases h : s'.embJW eJ with
            | none => simp [h] at h1
            | some _ => rfl
          exact Or.inr ⟨hm, h0, hsome⟩
    unfold unembeddedCount2
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have h32 : 3 * unembeddedCount2 J s' ≤ 2 * unembeddedCount2 J s := by omega
  have htau2_half := one_div_phi_dec_le_tau2_half tools H' J embJH hw
  have hcard_del_le : ((s'.innerIters2 - s.innerIters2 : ℕ) : ℝ) ≤
      (E_embed.card : ℝ) * wd.γ_ExpPath := by
    have h1 : (E_del_W.card : ℝ) ≤ (wd.τ₂ / 2) * (∑ eW ∈ E_del_W, wd.wW eW) := by
      rw [Finset.mul_sum]
      rw [← mul_one (E_del_W.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun eW heW => ?_
      have heWm := Finset.mem_range.mp (hE_del_sub heW)
      have hphi := wW_ge_phi tools H' J embJH hw heWm
      have h1 : 1 ≤ (wd.τ₂ / 2) * wd.φ_dec :=
        (div_le_iff₀ hw.φ_dec_pos).mp htau2_half
      have htau_nn : 0 ≤ wd.τ₂ / 2 := div_nonneg (tau2_pos tools H' J embJH hw).le two_pos.le
      exact le_trans h1 (mul_le_mul_of_nonneg_left hphi htau_nn)
    rw [← hE_del_card]
    exact le_trans h1 hW_gap_sum
  exact ⟨hU_card_le, h32, hcard_del_le, hdel_le_Wm⟩

/-! ## Task 3 termination, Corollary 8.10, and work statistics -/

private theorem eta2_round_contra {m η₂ k : ℕ} (hk : 1 ≤ k) (hm : m + 1 < 2 ^ k)
    (_hu : 1 ≤ m) :
    ¬ (η₂ = 2 * k ∧ 3 ^ η₂ ≤ 2 ^ η₂ * m) := by
  rintro ⟨rfl, hle⟩
  have h94 : 3 ^ (2 * k) = 9 ^ k := by
    have h32 : 3 ^ 2 = 9 := rfl
    rw [pow_mul, h32]
  have h42 : 2 ^ (2 * k) = 4 ^ k := by
    have h22 : 2 ^ 2 = 4 := rfl
    rw [pow_mul, h22]
  rw [h94, h42] at hle
  have h8lt9 : 8 ^ k < 9 ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
  have h4m : 4 ^ k * m < 4 ^ k * 2 ^ k := Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have h42_8 : 4 ^ k * 2 ^ k = 8 ^ k := by
    have h42' : 4 * 2 = 8 := rfl
    rw [← Nat.mul_pow, h42']
  omega

/-- Complete Task 3 specification (`spanner.tex`, pages 42, 44):
`task3` terminates with `task3OuterCond = false`, `Task3LoopInv`, `1 ≤ s_final.η₂ ≤ eta2Bound J`,
and exact inner-loop / deletion bounds. -/
theorem task3_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s_final := task3 tools.pathDS J wd
    task3OuterCond J s_final = false ∧
    Task3LoopInv tools.pathDS J wd s_final ∧
    1 ≤ s_final.η₂ ∧
    s_final.η₂ ≤ eta2Bound J ∧
    s_final.deleteCountW = s_final.innerIters2 ∧
    s_final.innerIters2 ≤ s_final.η₂ * wd.W.m ∧
    (s_final.innerIters2 : ℝ) ≤ (s_final.getPathCountW : ℝ) * wd.γ_ExpPath := by
  intro wd s_final
  let k := Nat.log 2 (J.m + 1) + 1
  have hk_pos : 1 ≤ k := by omega
  have hm_lt : J.m + 1 < 2 ^ k := Nat.lt_pow_succ_log_self (by omega) (J.m + 1)
  let s₀ := task3Init (DSState := tools.pathDS.State) J wd
  have hs₀_entry : Task3RoundEntryInv J wd s₀ := task3Init_entryInv tools H' J embJH hJ hw
  have hstep_entry : ∀ st, Task3RoundEntryInv J wd st →
      let st' := task3Round tools.pathDS J wd st
      Task3RoundEntryInv J wd st' ∧
      Task3LoopInv tools.pathDS J wd st' ∧
      Task3RoundRel tools.pathDS J wd st st' ∧
      task3MiddleCond tools.pathDS J wd st' = false ∧
      st'.η₂ = st.η₂ + 1 ∧
      3 * unembeddedCount2 J st' ≤ 2 * unembeddedCount2 J st := by
    intro st hst
    obtain ⟨hloop', hrel', hdone', heta', hic', hie'⟩ :=
      invariant_2 tools H' J embJH hJ hw hst
    have hc89 := claim_8_9 tools H' J embJH hJ hw hst hloop' hrel' hdone' heta'
    rcases hc89 with ⟨_, h32, hinner_E, hinner_W⟩
    have hE_diff : ((Finset.range J.m).filter fun eJ =>
        (st.embJW eJ).isNone = true ∧ ((task3Round tools.pathDS J wd st).embJW eJ).isSome = true).card =
        (task3Round tools.pathDS J wd st).getPathCountW - st.getPathCountW := by
      have hdisj : Disjoint (unembeddedSet2 J (task3Round tools.pathDS J wd st))
          ((Finset.range J.m).filter fun eJ =>
            (st.embJW eJ).isNone = true ∧ ((task3Round tools.pathDS J wd st).embJW eJ).isSome = true) := by
        rw [Finset.disjoint_left]
        intro eJ h1 h2
        simp only [unembeddedSet2, Finset.mem_filter, Option.isNone_iff_eq_none,
          Option.isSome_iff_ne_none] at h1 h2
        exact h2.2.2 h1.2
      have hunion : unembeddedSet2 J (task3Round tools.pathDS J wd st) ∪
          ((Finset.range J.m).filter fun eJ =>
            (st.embJW eJ).isNone = true ∧ ((task3Round tools.pathDS J wd st).embJW eJ).isSome = true) =
          unembeddedSet2 J st := by
        ext eJ
        simp only [Finset.mem_union, unembeddedSet2, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro (⟨hm, h1⟩ | ⟨hm, h0, _⟩)
          · refine ⟨hm, ?_⟩
            rcases hrel'.emb_mono eJ hm with h0 | h01
            · exact Option.isNone_iff_eq_none.mpr h0
            · rw [← h01]; exact h1
          · exact ⟨hm, h0⟩
        · rintro ⟨hm, h0⟩
          by_cases h1 : ((task3Round tools.pathDS J wd st).embJW eJ).isNone = true
          · exact Or.inl ⟨hm, h1⟩
          · have hsome : ((task3Round tools.pathDS J wd st).embJW eJ).isSome = true := by
              cases h : (task3Round tools.pathDS J wd st).embJW eJ with
              | none => simp [h] at h1
              | some _ => rfl
            exact Or.inr ⟨hm, h0, hsome⟩
      have hcard_u : unembeddedCount2 J (task3Round tools.pathDS J wd st) +
          ((Finset.range J.m).filter fun eJ =>
            (st.embJW eJ).isNone = true ∧ ((task3Round tools.pathDS J wd st).embJW eJ).isSome = true).card =
          unembeddedCount2 J st := by
        unfold unembeddedCount2
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hgp : (task3Round tools.pathDS J wd st).getPathCountW +
            unembeddedCount2 J (task3Round tools.pathDS J wd st) =
          st.getPathCountW + unembeddedCount2 J st := hrel'.getPath_eq
      omega
    have hinner_le_new : (task3Round tools.pathDS J wd st).innerIters2 ≤
        (task3Round tools.pathDS J wd st).η₂ * wd.W.m := by
      have hi1 := hst.inner_le
      have hin_mono : st.innerIters2 ≤ (task3Round tools.pathDS J wd st).innerIters2 := by
        rw [hrel'.inner_eq]; exact Nat.le_add_right _ _
      have hi_diff : (task3Round tools.pathDS J wd st).innerIters2 - st.innerIters2 ≤ wd.W.m :=
        hinner_W
      rw [heta', Nat.add_mul, Nat.one_mul]
      omega
    have hdel_eq_new : (task3Round tools.pathDS J wd st).deleteCountW =
        (task3Round tools.pathDS J wd st).innerIters2 := by
      have hde : (task3Round tools.pathDS J wd st).deleteCountW =
          (task3Round tools.pathDS J wd st).innerIters2 - st.innerIters2 + st.deleteCountW :=
        hrel'.del_eq
      have hde0 := hst.del_eq_inner
      have hin_mono : st.innerIters2 ≤ (task3Round tools.pathDS J wd st).innerIters2 := by
        rw [hrel'.inner_eq]; exact Nat.le_add_right _ _
      omega
    have hinner_gp_new : ((task3Round tools.pathDS J wd st).innerIters2 : ℝ) ≤
        ((task3Round tools.pathDS J wd st).getPathCountW : ℝ) * wd.γ_ExpPath := by
      have hin_mono : st.innerIters2 ≤ (task3Round tools.pathDS J wd st).innerIters2 := by
        rw [hrel'.inner_eq]; exact Nat.le_add_right _ _
      have hgp_mono : st.getPathCountW ≤ (task3Round tools.pathDS J wd st).getPathCountW := by
        have hgp : (task3Round tools.pathDS J wd st).getPathCountW +
              unembeddedCount2 J (task3Round tools.pathDS J wd st) =
            st.getPathCountW + unembeddedCount2 J st := hrel'.getPath_eq
        have h32' : 3 * unembeddedCount2 J (task3Round tools.pathDS J wd st) ≤
            2 * unembeddedCount2 J st := h32
        omega
      rw [hE_diff] at hinner_E
      have h1 : ((task3Round tools.pathDS J wd st).innerIters2 : ℝ) =
          (st.innerIters2 : ℝ) + (((task3Round tools.pathDS J wd st).innerIters2 - st.innerIters2 : ℕ) : ℝ) := by
        rw [← Nat.cast_add, Nat.add_sub_of_le hin_mono]
      have h2 : (((task3Round tools.pathDS J wd st).getPathCountW : ℝ) - (st.getPathCountW : ℝ)) * wd.γ_ExpPath =
          (((task3Round tools.pathDS J wd st).getPathCountW - st.getPathCountW : ℕ) : ℝ) * wd.γ_ExpPath := by
        congr 1
        rw [← Nat.cast_sub hgp_mono]
      calc ((task3Round tools.pathDS J wd st).innerIters2 : ℝ)
          = (st.innerIters2 : ℝ) + _ := h1
        _ ≤ (st.getPathCountW : ℝ) * wd.γ_ExpPath +
              (((task3Round tools.pathDS J wd st).getPathCountW - st.getPathCountW : ℕ) : ℝ) * wd.γ_ExpPath :=
            add_le_add hst.inner_le_getPath hinner_E
        _ = (st.getPathCountW : ℝ) * wd.γ_ExpPath +
              (((task3Round tools.pathDS J wd st).getPathCountW : ℝ) - (st.getPathCountW : ℝ)) * wd.γ_ExpPath := by
            rw [← h2]
        _ = ((task3Round tools.pathDS J wd st).getPathCountW : ℝ) * wd.γ_ExpPath := by ring
    refine ⟨?_, hloop', hrel', hdone', heta', h32⟩
    exact
      { partial_emb := hloop'.partial_emb
        j0_and_loops_embedded := hloop'.j0_and_loops_embedded
        emb_len := hloop'.emb_len
        econg_half := hloop'.econg_half
        j0_econg := hloop'.j0_econg
        initCount_eq := hic'
        initEdges_eq := hie'
        middle_eq := hloop'.middle_eq
        unemb_eq := hloop'.unemb_eq
        econgUpdates_le := hloop'.econgUpdates_le
        del_eq_inner := hdel_eq_new
        inner_le := hinner_le_new
        inner_le_getPath := hinner_gp_new }
  let s₁ := task3Round tools.pathDS J wd s₀
  obtain ⟨hs₁_entry, hs₁_loop, _, _, hs₁_eta, hs₁_32⟩ := hstep_entry s₀ hs₀_entry
  have hs₁_eta_eq : s₁.η₂ = 1 := hs₁_eta
  have hs₁_pow : 3 ^ s₁.η₂ * unembeddedCount2 J s₁ ≤ 2 ^ s₁.η₂ * J.m := by
    rw [hs₁_eta_eq, pow_one, pow_one]
    have hgp0 : s₀.getPathCountW = 0 := rfl
    have hu0 : unembeddedCount2 J s₀ ≤ J.m := by
      have := hs₀_entry.unemb_eq
      omega
    have h32_1 : 3 * unembeddedCount2 J s₁ ≤ 2 * unembeddedCount2 J s₀ := hs₁_32
    omega
  let P : Task3State tools.pathDS.State → Prop := fun st =>
    Task3RoundEntryInv J wd st ∧
    Task3LoopInv tools.pathDS J wd st ∧
    1 ≤ st.η₂ ∧
    st.η₂ ≤ 2 * k ∧
    3 ^ st.η₂ * unembeddedCount2 J st ≤ 2 ^ st.η₂ * J.m
  let meas : Task3State tools.pathDS.State → ℕ := fun st => unembeddedCount2 J st
  have hP₁ : P s₁ := ⟨hs₁_entry, hs₁_loop, by rw [hs₁_eta_eq], by omega, hs₁_pow⟩
  have hstep : ∀ st, P st → task3OuterCond J st = true →
      P (task3Round tools.pathDS J wd st) ∧
        meas (task3Round tools.pathDS J wd st) < meas st := by
    intro st ⟨hst_entry, _, hge1, hle2k, hpow⟩ hcond
    have hu_pos : 1 ≤ unembeddedCount2 J st := by
      by_contra hlt
      have hu0 : unembeddedCount2 J st = 0 := by omega
      have hempty : unembeddedSet2 J st = ∅ := Finset.card_eq_zero.mp hu0
      have hfalse := (task3OuterCond_false_iff_unemb J st).mpr hempty
      rw [hfalse] at hcond
      simp at hcond
    have hm_pos : 1 ≤ J.m := by
      have := hst_entry.unemb_eq
      omega
    have hlt_2k : st.η₂ < 2 * k := by
      by_contra hge
      have heq : st.η₂ = 2 * k := by omega
      have h3pow : 3 ^ st.η₂ ≤ 2 ^ st.η₂ * J.m := by
        calc 3 ^ st.η₂ = 3 ^ st.η₂ * 1 := (Nat.mul_one _).symm
          _ ≤ 3 ^ st.η₂ * unembeddedCount2 J st := Nat.mul_le_mul_left _ hu_pos
          _ ≤ 2 ^ st.η₂ * J.m := hpow
      exact eta2_round_contra hk_pos hm_lt hm_pos ⟨heq, h3pow⟩
    obtain ⟨hst'_entry, hst'_loop, _, _, heta', h32⟩ := hstep_entry st hst_entry
    have hpow' : 3 ^ (task3Round tools.pathDS J wd st).η₂ *
        unembeddedCount2 J (task3Round tools.pathDS J wd st) ≤
        2 ^ (task3Round tools.pathDS J wd st).η₂ * J.m := by
      rw [heta', pow_succ, pow_succ]
      calc 3 ^ st.η₂ * 3 * unembeddedCount2 J (task3Round tools.pathDS J wd st)
          = 3 ^ st.η₂ * (3 * unembeddedCount2 J (task3Round tools.pathDS J wd st)) := by ring
        _ ≤ 3 ^ st.η₂ * (2 * unembeddedCount2 J st) := Nat.mul_le_mul_left _ h32
        _ = 2 * (3 ^ st.η₂ * unembeddedCount2 J st) := by ring
        _ ≤ 2 * (2 ^ st.η₂ * J.m) := Nat.mul_le_mul_left _ hpow
        _ = 2 ^ st.η₂ * 2 * J.m := by ring
    have hlt_meas : meas (task3Round tools.pathDS J wd st) < meas st := by
      dsimp only [meas]
      have h32' : 3 * unembeddedCount2 J (task3Round tools.pathDS J wd st) ≤ 2 * unembeddedCount2 J st :=
        h32
      omega
    exact ⟨⟨hst'_entry, hst'_loop, by omega, by omega, hpow'⟩, hlt_meas⟩
  have hmeas_le : meas s₁ ≤ J.m := by
    dsimp only [meas]
    exact Nat.le_trans (Nat.le_add_left _ _) hs₁_entry.unemb_eq
  have hs_final_eq : s_final = whileFuel J.m (task3OuterCond J)
      (task3Round tools.pathDS J wd) s₁ := rfl
  have hinv_final : P s_final := by
    rw [hs_final_eq]
    exact whileFuel_inv P (task3OuterCond J) (task3Round tools.pathDS J wd)
      (fun st h c => (hstep st h c).1) J.m s₁ hP₁
  have hdone_final : task3OuterCond J s_final = false := by
    rw [hs_final_eq]
    exact whileFuel_done P meas (task3OuterCond J) (task3Round tools.pathDS J wd)
      hstep J.m s₁ hP₁ hmeas_le
  rcases hinv_final with ⟨hf_entry, hf_loop, hge1, hle2k, _⟩
  exact ⟨hdone_final, hf_loop, hge1, by simp only [eta2Bound]; omega,
         hf_entry.del_eq_inner, hf_entry.inner_le, hf_entry.inner_le_getPath⟩

/-- **Corollary 8.10** (`spanner.tex`, page 44):
Upon termination of Task 3, `embJW := partialToWalk s_final.embJW` is a valid `J → W` embedding
with `econg(Π_{J → W}) ≤ (η₂ + 1/2) τ₂ ≤ (eta2Bound J + 1/2) τ₂` and `length(Π_{J → W}) ≤ γ_ExpPath`. -/
theorem corollary_8_10 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s_final := task3 tools.pathDS J wd
    let embJW := partialToWalk s_final.embJW
    IsEmbedding J wd.W embJW ∧
    econg J wd.W (fun _ => 1) wd.wW embJW ≤ ((s_final.η₂ : ℝ) + 1 / 2) * wd.τ₂ ∧
    econg J wd.W (fun _ => 1) wd.wW embJW ≤ ((eta2Bound J : ℝ) + 1 / 2) * wd.τ₂ ∧
    (length J embJW : ℝ) ≤ wd.γ_ExpPath := by
  intro wd s_final embJW
  obtain ⟨hdone, hloop, _, heta_le, _, _, _⟩ := task3_spec tools H' J embJH hJ hw
  have hτ₂_pos := tau2_pos tools H' J embJH hw
  have hemb : IsEmbedding J wd.W embJW := by
    refine ⟨hloop.partial_emb.1, fun eJ heJ => ?_⟩
    have hsome := (task3OuterCond_false_iff J s_final).mp hdone eJ heJ
    rcases Option.isSome_iff_exists.mp hsome with ⟨P, hP⟩
    have hwalk := hloop.partial_emb.2 eJ heJ P hP
    dsimp only [embJW, partialToWalk]
    rw [hP]
    exact hwalk
  have hec1 : econg J wd.W (fun _ => 1) wd.wW embJW ≤ ((s_final.η₂ : ℝ) + 1 / 2) * wd.τ₂ := by
    rw [econg_le_iff]
    refine ⟨by positivity, fun eW heWm => ?_⟩
    exact hloop.econg_half eW heWm
  have hec2 : econg J wd.W (fun _ => 1) wd.wW embJW ≤ ((eta2Bound J : ℝ) + 1 / 2) * wd.τ₂ := by
    have heta_r : (s_final.η₂ : ℝ) ≤ (eta2Bound J : ℝ) := by exact_mod_cast heta_le
    exact le_trans hec1 (by nlinarith)
  have hlen : (length J embJW : ℝ) ≤ wd.γ_ExpPath := by
    have hγE_nn : 0 ≤ wd.γ_ExpPath :=
      (le_trans (by norm_num) (one_le_gamma_ExpPath tools H' J embJH hw))
    by_cases hm0 : J.m = 0
    · have hlen0 : length J embJW = 0 := by
        unfold length
        rw [hm0, Finset.range_zero, Finset.fold_empty]
      rw [hlen0]
      simpa using hγE_nn
    · have hm_pos : 0 < J.m := Nat.pos_of_ne_zero hm0
      have he : ∃ eJ < J.m, length J embJW = (embJW eJ).edges.length := by
        unfold length
        have hne : (Finset.range J.m).Nonempty := ⟨0, Finset.mem_range.mpr hm_pos⟩
        obtain ⟨eJ, heJ_r, heq⟩ :=
          Finset.exists_max_image (Finset.range J.m) (fun j => (embJW j).edges.length) hne
        have hle1 : (Finset.range J.m).fold max 0 (fun j => (embJW j).edges.length) ≤
            (embJW eJ).edges.length := by
          rw [Finset.fold_max_le]
          exact ⟨Nat.zero_le _, heq⟩
        have hle2 : (embJW eJ).edges.length ≤
            (Finset.range J.m).fold max 0 (fun j => (embJW j).edges.length) :=
          (Finset.le_fold_max _).mpr (Or.inr ⟨eJ, heJ_r, le_rfl⟩)
        exact ⟨eJ, Finset.mem_range.mp heJ_r, le_antisymm hle1 hle2⟩
      rcases he with ⟨eJ, heJm, heq⟩
      rw [heq]
      exact hloop.emb_len eJ heJm
  exact ⟨hemb, hec1, hec2, hlen⟩

/-- Exact Task 3 counter and work bounds upon termination of `task3`. -/
theorem task3_stats {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s_final := task3 tools.pathDS J wd
    1 ≤ s_final.η₂ ∧
    s_final.η₂ ≤ eta2Bound J ∧
    s_final.initCountW = s_final.η₂ * wd.comps.length ∧
    s_final.initEdgesW = s_final.η₂ * (wd.comps.map fun c => c.W_sub.m).sum ∧
    s_final.initEdgesW ≤ s_final.η₂ * wd.W.m ∧
    s_final.getPathCountW ≤ J.m ∧
    s_final.middleIters2 = s_final.getPathCountW ∧
    s_final.deleteCountW = s_final.innerIters2 ∧
    s_final.innerIters2 ≤ s_final.η₂ * wd.W.m ∧
    (s_final.innerIters2 : ℝ) ≤ (s_final.getPathCountW : ℝ) * wd.γ_ExpPath ∧
    (s_final.econgUpdates : ℝ) ≤ (s_final.getPathCountW : ℝ) * wd.γ_ExpPath := by
  intro wd s_final
  obtain ⟨_, hloop, hge1, hle, hdel, hin_W, hin_gp⟩ := task3_spec tools H' J embJH hJ hw
  have hsum_le_Wm : (wd.comps.map fun c => c.W_sub.m).sum ≤ wd.W.m := by
    dsimp only [wd]
    rw [hw.W_m_eq]
    exact Nat.le_add_left _ _
  refine ⟨hge1, hle, hloop.initCount_eq, hloop.initEdges_eq, ?_, ?_, hloop.middle_eq,
    hdel, hin_W, hin_gp, hloop.econgUpdates_le⟩
  · rw [hloop.initEdges_eq]
    exact Nat.mul_le_mul_left _ hsum_le_Wm
  · exact Nat.le_trans (Nat.le_add_right _ _) hloop.unemb_eq

end MinCostFlow.Spanner
