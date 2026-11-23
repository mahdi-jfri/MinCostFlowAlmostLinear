module

public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Expander.PathDSBounds
public import MinCostFlow.Expander.PathDSProg.FallbackCost
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import MinCostFlow.Expander.DecrementalPaths
import MinCostFlow.Expander.FallbackPruning
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import MinCostFlow.Expander.PathDSBase

/-!
# Theorem 8.6 as a `PathDSTool` Data Structure

Constructs a `MinCostFlow.Spanner.PathDSTool` from `Cited.DecrementalExpanderPaths`
([CS21] Theorem 3.9, `MinCostFlow/Statement/Cited/ChuzhoySaranurak.lean`):

* When `10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in` and deletion count stays within the
  `[CS21]` budget `t ≤ csPhi Kγ c (3 * G.m) * (3 * G.m) / 10`, transitions and path queries execute
  `R.Implements` for `Cited.prunedExpanderDS` on the 2-subdivision `subdivGraph G` with
  `q := qOf M = Θ(log^{1/8}(M + 2))` and project `S_s, P_s` back to `G` via `projSet, projWalk`.
* When `[CS21]` budget is exceeded, `overBudget` sets `V̂ := G.verts`, keeping `vol(V̂) = 2 * G.m`
  below `γ_del * t / φ_out` (using `γ_del ≥ 7`).
* When a small component has `φ_in < 10 * Cited.csPhi Kγ c (3 * G.m)` (for instance when `G.m ≪ M`),
  greedy strong-expander pruning + BFS (`FallbackPruning.lean`) maintains `vol(V̂) ≤ 7 * t / φ_in`
  and simple walks of length `≤ 25 * (log(2M + 2) + 1) / φ_in ≤ γ_ExpPath φ_in M`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

section

private lemma csOverBudget_spec {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (R : DSRep Cited.PrunedExpander) (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) (w h₀ h : ℕ)
    (s_cs : Cited.PrunedExpander) (x : R.τ) (mem : ℕ → ℕ) (delList : List ℕ)
    (overBudget : Bool) (VhatSet : Finset ℕ) (e : ℕ)
    (hinv : CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList overBudget VhatSet)
    (he_lt : e < G.m) (he_nd : e ∉ delList)
    (hover : overBudget = true ∨
      Cited.csPhi Kγ c (3 * G.m) * ((3 * G.m : ℕ) : ℝ) / 10 < ((delList.length + 1 : ℕ) : ℝ)) :
    let delList' := delList ++ [e]
    let st' : PDSState R.τ := .cs φ_in M G w h₀ h s_cs x mem delList' true G.verts
    PDSInv Kγ c K cw R φ_in M G st' ∧
    pdsDeleted st' = insert e delList.toFinset ∧
    VhatSet ⊆ pdsVhat st' ∧
    pdsVhat st' ⊆ G.verts ∧
    G.verts \ VhatSet = pdsVhat st' \ VhatSet ∧
    (G.vol (pdsVhat st') : ℝ) ≤
      csGammaDel K * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M := by
  rcases hinv with ⟨hφ, hV, hm1, hmM, hcs, hsG, hsq, hdel_nd, hdel_lt, hw_eq, hh₀_eq, hzf,
    hfoot, hh_le, hrep, hgood, hbranch⟩
  set delList' := delList ++ [e]
  have hdel'_nd : delList'.Nodup := by
    rw [List.nodup_append]
    exact ⟨hdel_nd, List.nodup_singleton e, fun x hx y hy hxy => by
      simp only [List.mem_singleton] at hy
      subst hxy hy
      exact he_nd hx⟩
  have hdel'_lt : ∀ j ∈ delList', j < G.m := by
    intro j hj
    rw [List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact hdel_lt j hj
    · exact he_lt
  have hdel'_fin : delList'.toFinset = insert e delList.toFinset := by
    ext j; simp [delList']
  have hVhat_sub : VhatSet ⊆ G.verts := by
    cases overBudget
    · simp only [Bool.false_eq_true, ↓reduceIte] at hbranch
      rw [hbranch.2.2]
      exact (projSet_spec hV s_cs.S).1
    · simp only [↓reduceIte] at hbranch
      rw [hbranch.2]
  have hover' : Cited.csPhi Kγ c (3 * G.m) * ((3 * G.m : ℕ) : ℝ) / 10 < (delList'.length : ℝ) := by
    have hlen' : delList'.length = delList.length + 1 := by simp [delList']
    rw [hlen']
    rcases hover with rfl | hgt
    · simp only [↓reduceIte] at hbranch
      have h1 : (delList.length : ℝ) < ((delList.length + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact lt_trans hbranch.1 h1
    · exact hgt
  have hh'_le : h ≤ h₀ + (delList'.length + 1) * Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q := by
    have h1 : delList.length + 1 ≤ delList'.length + 1 := by simp [delList']
    have h2 : (delList.length + 1) * Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q ≤
        (delList'.length + 1) * Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q :=
      Nat.mul_le_mul_right _ h1
    omega
  have hvol_le : (G.vol G.verts : ℝ) ≤
      csGammaDel K * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M := by
    have hcard_eq : (insert e delList.toFinset).card = delList'.length := by
      rw [← hdel'_fin, List.toFinset_card_of_nodup hdel'_nd]
    have hvol_eq : (G.vol G.verts : ℝ) = (2 * G.m : ℝ) := by
      rw [vol_verts_of_isValid hV]
      push_cast; ring
    have hφout_pos : 0 < csPhiOut Kγ c φ_in M := csPhiOut_pos Kγ c hc hφ M
    have hφout_le : csPhiOut Kγ c φ_in M ≤ Cited.csPhi Kγ c (3 * G.m) :=
      csPhiOut_le_csPhi_m hc φ_in hmM
    have hratio : Cited.csPhi Kγ c (3 * G.m) / csPhiOut Kγ c φ_in M ≥ 1 :=
      (one_le_div hφout_pos).mpr hφout_le
    have hlow : (21 / 10 : ℝ) * (G.m : ℝ) < 7 * (delList'.length : ℝ) / csPhiOut Kγ c φ_in M := by
      have hmul := mul_lt_mul_of_pos_left hover' (by norm_num : (0 : ℝ) < 7)
      have hdiv : 7 * (Cited.csPhi Kγ c (3 * G.m) * ((3 * G.m : ℕ) : ℝ) / 10) / csPhiOut Kγ c φ_in M <
          7 * (delList'.length : ℝ) / csPhiOut Kγ c φ_in M :=
        div_lt_div_of_pos_right hmul hφout_pos
      have hlhs : 7 * (Cited.csPhi Kγ c (3 * G.m) * ((3 * G.m : ℕ) : ℝ) / 10) / csPhiOut Kγ c φ_in M =
          (21 / 10 : ℝ) * (G.m : ℝ) * (Cited.csPhi Kγ c (3 * G.m) / csPhiOut Kγ c φ_in M) := by
        push_cast; ring
      have hgm_nn : (0 : ℝ) ≤ (21 / 10 : ℝ) * (G.m : ℝ) := by positivity
      have h1 : (21 / 10 : ℝ) * (G.m : ℝ) ≤
          (21 / 10 : ℝ) * (G.m : ℝ) * (Cited.csPhi Kγ c (3 * G.m) / csPhiOut Kγ c φ_in M) := by
        calc (21 / 10 : ℝ) * (G.m : ℝ) = (21 / 10 : ℝ) * (G.m : ℝ) * 1 := by ring
          _ ≤ (21 / 10 : ℝ) * (G.m : ℝ) * (Cited.csPhi Kγ c (3 * G.m) / csPhiOut Kγ c φ_in M) :=
              mul_le_mul_of_nonneg_left hratio hgm_nn
      linarith
    have h7_le : 7 ≤ csGammaDel K := le_max_right _ 7
    have hcard_nn : 0 ≤ ((insert e delList.toFinset).card : ℝ) := Nat.cast_nonneg _
    have hdiv_le : 7 * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M ≤
        csGammaDel K * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h7_le hcard_nn) hφout_pos.le
    rw [hvol_eq]
    rw [← hcard_eq] at hlow
    linarith
  refine ⟨⟨rfl, rfl, rfl, hφ, hV, hm1, hmM, hcs, hsG, hsq, hdel'_nd, hdel'_lt, hw_eq, hh₀_eq,
      hzf, hfoot, hh'_le, hrep, hgood, ?_⟩, hdel'_fin, hVhat_sub, Finset.Subset.rfl, rfl, hvol_le⟩
  simp only [↓reduceIte]
  refine ⟨?_, trivial⟩
  push_cast at hover' ⊢
  exact hover'

private noncomputable def csGetPathWalk {Kγ c : ℕ} (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w))
    (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) (w h₀ h : ℕ) (s_cs : Cited.PrunedExpander)
    (x : R.τ) (mem : ℕ → ℕ) (delList : List ℕ) (VhatSet : Finset ℕ) (u v : ℕ)
    (hinv : CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet)
    (hu : u ∈ G.verts \ VhatSet) (hv : v ∈ G.verts \ VhatSet) :
    { P : Spanner.Walk //
      P.IsWalk G u v ∧ P.verts.Nodup ∧ (∀ e ∈ P.edges, e ∉ delList.toFinset) ∧
      (∀ x ∈ P.verts, x ∉ VhatSet) ∧ (P.edges.length : ℝ) ≤ csGammaExpPath Kγ c K φ_in M } := by
  classical
  rcases hinv with ⟨hφ, hV, hm1, hmM, hcs, hsG, hsq, hdel_nd, hdel_lt, hw_eq, hh₀_eq, hzf,
    hfoot, hh_le, hrep, hgood, hbranch⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hbranch
  rcases hbranch with ⟨hsdel, _, hVhat_eq⟩
  have hu_lt : u < G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hu).1
  have hv_lt : v < G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hv).1
  have hu_notS : u ∉ s_cs.S := by
    intro huS
    apply (Finset.mem_sdiff.mp hu).2
    rw [hVhat_eq, projSet, Finset.mem_filter]
    exact ⟨huS, hu_lt⟩
  have hv_notS : v ∉ s_cs.S := by
    intro hvS
    apply (Finset.mem_sdiff.mp hv).2
    rw [hVhat_eq, projSet, Finset.mem_filter]
    exact ⟨hvS, hv_lt⟩
  have hlen_le : delList.length ≤ G.m := nodup_subset_range_length_le hdel_nd hdel_lt
  set G_s := subdivGraph G
  have hH_lt : G_s.encode.length +
      (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) +
      Cited.csQuery Kγ K G_s.m (qOf M) + G_s.n + 3 * G.m + qOf M + 4 < 2 ^ w := by
    rw [hw_eq]
    exact lt_two_pow_csWordSize Kγ cw K M G
  have hw_cw : cw * (Nat.log 2 (G_s.n + G_s.m + 2) + 1) ≤ w := by
    rw [hw_eq]
    exact csWordSize_ge_cw Kγ cw K M G
  set args := [h₀, u, v, h]
  have hh_bound : h ≤ G_s.encode.length + (G.m + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by
    have hmul : (delList.length + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
        (G.m + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hh₀_eq, hsG, hsq] at hh_le
    omega
  have hm_le : (G.m + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
      (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
    Nat.mul_le_mul_right _ (by omega)
  have hpre : (Cited.prunedExpanderDS Kγ c K cw w).pre 1 s_cs args mem := by
    refine ⟨rfl, ?_, ?_, ?_, hu_notS, hv_notS⟩
    · rw [hsG]; exact hw_cw
    · change u < s_cs.G.n
      rw [hsG, show G_s.n = G.n + 2 * G.m from subdivGraph_n G]; omega
    · change v < s_cs.G.n
      rw [hsG, show G_s.n = G.n + 2 * G.m from subdivGraph_n G]; omega
  have hargs_w : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    have hSn : G.n ≤ G_s.n := by rw [show G_s.n = G.n + 2 * G.m from subdivGraph_n G]; omega
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hspace_w : heapArg args + (Cited.prunedExpanderDS Kγ c K cw w).space 1 s_cs args mem < 2 ^ w := by
    change h + Cited.csQuery Kγ K s_cs.G.m s_cs.q < 2 ^ w
    rw [hsG, hsq]
    omega
  have hR := (hImpl w 0 (csProgram mk) (csProgram_hasAt mk)).2.2 1 h₀ s_cs x args mem 0
    (fun _ => false) hargs_w rfl hrep hpre hfoot hzf hspace_w
  let body := Classical.choose hR
  have hbody := Classical.choose_spec hR
  let o := Classical.choose hbody.2
  have ho := Classical.choose_spec hbody.2
  let st' := Classical.choose ho
  have hst' := Classical.choose_spec ho
  let cost := Classical.choose hst'
  have hcost := Classical.choose_spec hst'
  let s' := Classical.choose hcost.2
  have hs' := Classical.choose_spec hcost.2
  let x' := Classical.choose hs'
  have hx' := Classical.choose_spec hs'
  rcases hx' with ⟨_, hpost', _, _⟩
  set P_s := Classical.choose hpost'.2
  have hP_spec : WordRAM.SeqAt st'.mem (heapArg args) P_s ∧ P_s.Nodup ∧ (∀ x ∈ P_s, x ∉ s_cs.S) ∧
      Cited.IsPathAlong s_cs.currentEdges u v P_s ∧
      (P_s.length : ℝ) - 1 ≤ (Cited.csGamma Kγ s_cs.G.m : ℝ) ^ (K * (s_cs.q : ℝ)) := by
    have hs := Classical.choose_spec hpost'.2
    change WordRAM.SeqAt st'.mem (heapArg args) P_s ∧ P_s.Nodup ∧ (∀ x ∈ P_s, x ∉ s_cs.S) ∧
        Cited.IsPathAlong s_cs.currentEdges (args.getD 1 0) (args.getD 2 0) P_s ∧
        (P_s.length : ℝ) - 1 ≤ (Cited.csGamma Kγ s_cs.G.m : ℝ) ^ (K * (s_cs.q : ℝ)) at hs
    exact hs
  rcases hP_spec with ⟨_, hP_nd, hP_notS, hP_along, hP_len⟩
  have hs_eq : s_cs = ⟨subdivGraph G, qOf M, subdivDel delList, s_cs.S⟩ := by
    cases s_cs
    simp only at hsG hsq hsdel
    subst hsG hsq hsdel
    rfl
  have hP_along' : Cited.IsPathAlong
      (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, qOf M, subdivDel delList, s_cs.S⟩) u v P_s := by
    rw [← hs_eq]
    exact hP_along
  have hW := projWalk_spec hV delList s_cs.S hu_lt hv_lt hP_nd hP_notS hP_along'
  set W := projWalk G u v P_s
  refine ⟨W, hW.1, hW.2.1, ?_, ?_, ?_⟩
  · intro e he hmem
    rw [List.mem_toFinset] at hmem
    exact (hW.2.2.2.1 e he).2 hmem
  · intro z hz
    rw [hVhat_eq]
    exact hW.2.2.1 z hz
  · have hP_pos : 1 ≤ P_s.length := by
      cases hPs : P_s with
      | nil => rw [hPs] at hP_along; simp [Cited.IsPathAlong] at hP_along
      | cons _ _ => simp
    have hW3 : 3 * W.edges.length ≤ P_s.length - 1 := hW.2.2.2.2
    have hW_len : (W.edges.length : ℝ) ≤ (P_s.length : ℝ) - 1 := by
      have h1 : (W.edges.length : ℝ) ≤ ((P_s.length - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : W.edges.length ≤ P_s.length - 1)
      rw [Nat.cast_sub hP_pos] at h1
      simpa using h1
    have hγ_ge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ s_cs.G.m : ℝ) := by
      unfold Cited.csGamma
      exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
    have hγ_mono : (Cited.csGamma Kγ s_cs.G.m : ℝ) ≤ (Cited.csGamma Kγ (3 * M) : ℝ) := by
      rw [hsG, subdivGraph_m]
      exact_mod_cast csGamma_mono (by omega : 3 * G.m ≤ 3 * M)
    have hexp_le : K * (s_cs.q : ℝ) ≤ max K 1 * (qOf M : ℝ) := by
      rw [hsq]
      exact mul_le_mul_of_nonneg_right (le_max_left K 1) (Nat.cast_nonneg _)
    have hpow1 : (Cited.csGamma Kγ s_cs.G.m : ℝ) ^ (K * (s_cs.q : ℝ)) ≤
        (Cited.csGamma Kγ s_cs.G.m : ℝ) ^ (max K 1 * (qOf M : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hγ_ge1 hexp_le
    have hpow2 : (Cited.csGamma Kγ s_cs.G.m : ℝ) ^ (max K 1 * (qOf M : ℝ)) ≤
        (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (qOf M : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hγ_mono (by positivity)
    exact le_trans (le_trans hW_len hP_len) (le_trans (le_trans hpow1 hpow2) (le_max_left _ _))

open Classical in
private noncomputable def rawPathDS {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    Spanner.PathDSTool where
  State := PDSState R.τ
  φ_out := csPhiOut Kγ c
  γ_ExpPath := csGammaExpPath Kγ c K
  γ_query := csGammaQuery Kγ c K
  γ_del _ _ := csGammaDel K
  init φ_in M G :=
    if h : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
        (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
        10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in then
      (csInitState K cw mk R hImpl φ_in M G h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
        h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2).1
    else .fb φ_in M G ∅ ∅
  Vhat := pdsVhat
  deleted := pdsDeleted
  delete s e :=
    match s with
    | .cs φ_in M G w h₀ h s_cs x mem delList overBudget VhatSet =>
      if hover : overBudget = true then
        (.cs φ_in M G w h₀ h s_cs x mem (delList ++ [e]) true G.verts, G.verts \ VhatSet)
      else
        if hpre : CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet ∧
            e < G.m ∧ e ∉ delList ∧
            ((delList.length + 1 : ℕ) : ℝ) ≤ Cited.csPhi Kγ c s_cs.G.m * (s_cs.G.m : ℝ) / 10 then
          (csDeleteState hc K cw mk R hImpl φ_in M G w h₀ h s_cs x mem delList VhatSet e
            hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2).1
        else (.cs φ_in M G w h₀ h s_cs x mem (delList ++ [e]) true G.verts, G.verts \ VhatSet)
    | .fb φ_in M G del S =>
      let del' := insert e del
      let S' := fbPruneStep G del' φ_in S
      (.fb φ_in M G del' S', S' \ S)
  getPath s u v :=
    match s with
    | .cs φ_in M G w h₀ h s_cs x mem delList overBudget VhatSet =>
      if hpre : overBudget = false ∧
          CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet ∧
          u ∈ G.verts \ VhatSet ∧ v ∈ G.verts \ VhatSet then
        (csGetPathWalk K cw mk R hImpl φ_in M G w h₀ h s_cs x mem delList VhatSet u v
          hpre.2.1 hpre.2.2.1 hpre.2.2.2).1
      else Walk.empty
    | .fb φ_in M G del S => fallbackGetPath G del S φ_in M u v
  Inv := PDSInv Kγ c K cw R
  hφ_pos _ M hφ := csPhiOut_pos Kγ c hc hφ M
  hφ_le _ _ _ := min_le_left _ _
  hφ_half _ _ _ := le_trans (min_le_right _ _) (min_le_left _ _)
  hγ_ExpPath_ge φ_in M hφ := by
    have hlog : 1 ≤ Real.log (2 * (M : ℝ) + 2) + 1 := by
      have : 0 ≤ Real.log (2 * (M : ℝ) + 2) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
      linarith
    have hφout_pos : 0 < csPhiOut Kγ c φ_in M := csPhiOut_pos Kγ c hc hφ M
    have hdiv : 1 / csPhiOut Kγ c φ_in M ≤
        25 * (Real.log (2 * (M : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M :=
      div_le_div_of_nonneg_right (by linarith) hφout_pos.le
    exact le_trans hdiv (le_max_right _ _)
  hγ_query_ge _ _ _ := le_add_of_nonneg_right (Nat.cast_nonneg _)
  hγ_del_ge _ _ _ := le_trans (by norm_num : (1 : ℝ) ≤ 7) (le_max_right _ 7)
  init_inv φ_in M G hφ hφ1 hV hm hmM hiso hexp := by
    by_cases h10 : 10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in
    · have hall : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
          (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
          10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in :=
        ⟨hφ, hφ1, hV, hm, hmM, hiso, hexp, h10⟩
      rw [dite_eq_left_of_eq_true (eq_true hall)]
      exact (csInitState K cw mk R hImpl φ_in M G hφ hφ1 hV hm hmM hiso hexp h10).2.1
    · have hnot : ¬ (0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
          (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
          10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in) := fun h => h10 h.2.2.2.2.2.2.2
      rw [dite_eq_right_of_eq_false (eq_false hnot)]
      exact ⟨rfl, rfl, rfl, lt_of_not_ge h10, fbPruneStep_init G φ_in hφ hV hm hexp, Finset.empty_subset _⟩
  init_Vhat φ_in M G hφ hφ1 hV hm hmM hiso hexp := by
    by_cases h10 : 10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in
    · have hall : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
          (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
          10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in :=
        ⟨hφ, hφ1, hV, hm, hmM, hiso, hexp, h10⟩
      rw [dite_eq_left_of_eq_true (eq_true hall)]
      exact (csInitState K cw mk R hImpl φ_in M G hφ hφ1 hV hm hmM hiso hexp h10).2.2.1
    · have hnot : ¬ (0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
          (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
          10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in) := fun h => h10 h.2.2.2.2.2.2.2
      rw [dite_eq_right_of_eq_false (eq_false hnot)]
      rfl
  init_deleted φ_in M G hφ hφ1 hV hm hmM hiso hexp := by
    by_cases h10 : 10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in
    · have hall : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
          (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
          10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in :=
        ⟨hφ, hφ1, hV, hm, hmM, hiso, hexp, h10⟩
      rw [dite_eq_left_of_eq_true (eq_true hall)]
      exact (csInitState K cw mk R hImpl φ_in M G hφ hφ1 hV hm hmM hiso hexp h10).2.2.2
    · have hnot : ¬ (0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
          (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in ∧
          10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in) := fun h => h10 h.2.2.2.2.2.2.2
      rw [dite_eq_right_of_eq_false (eq_false hnot)]
      rfl
  delete_spec φ_in M G s e hφ hφ1 hV hm _hmM hiso hexp hinv he_lt he_nd := by
    cases s with
    | cs φ_in' M' G' w h₀ h s_cs x mem delList overBudget VhatSet =>
      rcases hinv with ⟨hφ_eq, hM_eq, hG_eq, hcsInv⟩
      subst φ_in' M' G'
      have he_nd' : e ∉ delList := fun hm_list => he_nd (List.mem_toFinset.mpr hm_list)
      cases overBudget
      · dsimp only
        rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)]
        by_cases hbud : ((delList.length + 1 : ℕ) : ℝ) ≤
            Cited.csPhi Kγ c s_cs.G.m * (s_cs.G.m : ℝ) / 10
        · have hall : CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet ∧
              e < G.m ∧ e ∉ delList ∧
              ((delList.length + 1 : ℕ) : ℝ) ≤ Cited.csPhi Kγ c s_cs.G.m * (s_cs.G.m : ℝ) / 10 :=
            ⟨hcsInv, he_lt, he_nd', hbud⟩
          rw [dite_eq_left_of_eq_true (eq_true hall)]
          rcases (csDeleteState hc K cw mk R hImpl φ_in M G w h₀ h s_cs x mem delList VhatSet e
            hcsInv he_lt he_nd' hbud).2 with ⟨h1, h2, h3, h4, h5, h6⟩
          exact ⟨h1, h2, h3, h4, h5, le_of_le_of_eq h6
            (congrArg (fun S : Finset ℕ => csGammaDel K * (S.card : ℝ) / csPhiOut Kγ c φ_in M) h2.symm)⟩
        · have hnot : ¬ (CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet ∧
              e < G.m ∧ e ∉ delList ∧
              ((delList.length + 1 : ℕ) : ℝ) ≤ Cited.csPhi Kγ c s_cs.G.m * (s_cs.G.m : ℝ) / 10) :=
            fun h => hbud h.2.2.2
          rw [dite_eq_right_of_eq_false (eq_false hnot)]
          have hsGm : s_cs.G.m = 3 * G.m := by
            rw [hcsInv.2.2.2.2.2.1, subdivGraph_m]
          have hover_gt : Cited.csPhi Kγ c (3 * G.m) * ((3 * G.m : ℕ) : ℝ) / 10 <
              ((delList.length + 1 : ℕ) : ℝ) := by
            rw [← hsGm]; exact lt_of_not_ge hbud
          rcases csOverBudget_spec hc K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet e
            hcsInv he_lt he_nd' (Or.inr hover_gt) with ⟨h1, h2, h3, h4, h5, h6⟩
          rw [← h2] at h6
          exact ⟨h1, h2, h3, h4, h5, h6⟩
      · dsimp only
        rw [dite_eq_left_of_eq_true (eq_true rfl)]
        rcases csOverBudget_spec hc K cw R φ_in M G w h₀ h s_cs x mem delList true VhatSet e
          hcsInv he_lt he_nd' (Or.inl rfl) with ⟨h1, h2, h3, h4, h5, h6⟩
        rw [← h2] at h6
        exact ⟨h1, h2, h3, h4, h5, h6⟩
    | fb φ_in' M' G' del S =>
      rcases hinv with ⟨hφ_eq, hM_eq, hG_eq, hfb10, hfbInv, hdel_sub⟩
      subst φ_in' M' G'
      dsimp only
      set del' := insert e del
      set S' := fbPruneStep G del' φ_in S
      have hpr := fbPruneStep_spec G del del' φ_in hφ hφ1 hV hm hexp (Finset.subset_insert _ _) hfbInv
      rcases hpr with ⟨hSS', hfbInv'⟩
      have hdel'_sub : del' ⊆ Finset.range G.m :=
        Finset.insert_subset_iff.mpr ⟨Finset.mem_range.mpr he_lt, hdel_sub⟩
      refine ⟨⟨rfl, rfl, rfl, hfb10, hfbInv', hdel'_sub⟩, rfl, hSS', hfbInv'.1, rfl, ?_⟩
      have hvol1 : (G.vol S' : ℝ) ≤ 7 * (del'.card : ℝ) / φ_in := hfbInv'.2.1
      have h7_le : 7 ≤ csGammaDel K := le_max_right _ 7
      have hcard_nn : (0 : ℝ) ≤ (del'.card : ℝ) := Nat.cast_nonneg _
      have hφout_pos : 0 < csPhiOut Kγ c φ_in M := csPhiOut_pos Kγ c hc hφ M
      have hφout_le : csPhiOut Kγ c φ_in M ≤ φ_in := min_le_left _ _
      have hdiv1 : 7 * (del'.card : ℝ) / φ_in ≤ csGammaDel K * (del'.card : ℝ) / φ_in :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h7_le hcard_nn) hφ.le
      have hdiv2 : csGammaDel K * (del'.card : ℝ) / φ_in ≤
          csGammaDel K * (del'.card : ℝ) / csPhiOut Kγ c φ_in M := by
        have hγ_nn : 0 ≤ csGammaDel K * (del'.card : ℝ) := by
          have : 0 ≤ csGammaDel K := le_trans (by norm_num) (le_max_right _ 7)
          exact mul_nonneg this hcard_nn
        exact div_le_div_of_nonneg_left hγ_nn hφout_pos hφout_le
      exact le_trans hvol1 (le_trans hdiv1 hdiv2)
  getPath_spec φ_in M G s u v hφ hφ1 hV _hm hmM hiso _hexp hinv hu hv := by
    cases s with
    | cs φ_in' M' G' w h₀ h s_cs x mem delList overBudget VhatSet =>
      rcases hinv with ⟨hφ_eq, hM_eq, hG_eq, hcsInv⟩
      subst φ_in' M' G'
      cases overBudget
      · dsimp only
        have hall : false = false ∧
            CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet ∧
            u ∈ G.verts \ VhatSet ∧ v ∈ G.verts \ VhatSet :=
          ⟨rfl, hcsInv, hu, hv⟩
        rw [dite_eq_left_of_eq_true (eq_true hall)]
        exact (csGetPathWalk K cw mk R hImpl φ_in M G w h₀ h s_cs x mem delList VhatSet u v
          hcsInv hu hv).2
      · exfalso
        rcases hcsInv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩
        simp only [↓reduceIte] at hb
        have hVeq : VhatSet = G.verts := hb.2
        have h_emp : u ∈ G.verts \ G.verts := hVeq ▸ hu
        simp at h_emp
    | fb φ_in' M' G' del S =>
      rcases hinv with ⟨hφ_eq, hM_eq, hG_eq, _, hfbInv, _⟩
      subst φ_in' M' G'
      dsimp only
      have hgp := fallbackGetPath_spec hV hmM hiso hφ hφ1 hfbInv.2.2.1 hu hv
      refine ⟨hgp.1, hgp.2.1, hgp.2.2.1, hgp.2.2.2.1, ?_⟩
      have hnum_nn : 0 ≤ 25 * (Real.log (2 * (M : ℝ) + 2) + 1) := by
        have : 0 ≤ Real.log (2 * (M : ℝ) + 2) :=
          Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
        linarith
      have hdiv : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / φ_in ≤
          25 * (Real.log (2 * (M : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M :=
        div_le_div_of_nonneg_left hnum_nn (csPhiOut_pos Kγ c hc hφ M) (min_le_left _ _)
      exact le_trans hgp.2.2.2.2 (le_trans hdiv (le_max_right _ _))

end

public section

/-- Bundled `PathDSTool` together with its parameter equalities. -/
noncomputable def pathDSOfCSBundle {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    { ds : Spanner.PathDSTool //
      ds.φ_out = csPhiOut Kγ c ∧
      ds.γ_ExpPath = csGammaExpPath Kγ c K ∧
      ds.γ_del = (fun _ _ => csGammaDel K) ∧
      ds.γ_query = csGammaQuery Kγ c K } :=
  ⟨rawPathDS hc K cw mk R hImpl, rfl, rfl, rfl, rfl⟩

/-- Construct `Spanner.PathDSTool` from the concrete `[CS21]` implementation of
`DecrementalExpanderPaths`, bridging small components (`φ_in < 10 * csPhi Kγ c (3*G.m)`) and
post-budget deletions via `FallbackPruning` and `V̂ := G.verts`. -/
noncomputable def pathDSOfCS {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    Spanner.PathDSTool :=
  (pathDSOfCSBundle hc K cw mk R hImpl).1

@[simp] lemma pathDSOfCS_φ_out {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    (pathDSOfCS hc K cw mk R hImpl).φ_out = csPhiOut Kγ c :=
  (pathDSOfCSBundle hc K cw mk R hImpl).2.1

@[simp] lemma pathDSOfCS_γ_ExpPath {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    (pathDSOfCS hc K cw mk R hImpl).γ_ExpPath = csGammaExpPath Kγ c K :=
  (pathDSOfCSBundle hc K cw mk R hImpl).2.2.1

@[simp] lemma pathDSOfCS_γ_del {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    (pathDSOfCS hc K cw mk R hImpl).γ_del = fun _ _ => csGammaDel K :=
  (pathDSOfCSBundle hc K cw mk R hImpl).2.2.2.1

@[simp] lemma pathDSOfCS_γ_query {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) :
    (pathDSOfCS hc K cw mk R hImpl).γ_query = csGammaQuery Kγ c K :=
  (pathDSOfCSBundle hc K cw mk R hImpl).2.2.2.2

end

end MinCostFlow.Expander
