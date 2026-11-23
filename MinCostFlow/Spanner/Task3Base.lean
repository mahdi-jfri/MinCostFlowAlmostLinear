module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.WitnessLift

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Task 3 Base Invariants and Loops

This file contains the helper lemmas, invariants (`Task3CoreInv`, `Task3LoopInv`, `Task3RoundRel`),
and inner/middle loop specifications (`task3InnerLoop_spec`, `task3MiddleStep_inv`,
`task3MiddleLoop_spec`) for Task 3 of Algorithm 4 (`Sparsify`, `spanner.tex`, lines 105–121,
page 44). These support `invariant_2`, `claim_8_9`, and `corollary_8_10` in
`MinCostFlow.Spanner.Analysis2`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## General list, `zipIdx`, and edge-congestion update lemmas -/

private theorem head?_some_mem2 {α : Type*} {l : List α} {a : α} (h : l.head? = some a) :
    a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

private theorem mem_zipIdx_spec {α : Type*} :
    ∀ (l : List α) (k : ℕ) (p : α × ℕ),
      p ∈ l.zipIdx k → k ≤ p.2 ∧ ∃ h : p.2 - k < l.length, l[p.2 - k]'h = p.1 := by
  intro l
  induction l with
  | nil => intro k p hp; simp at hp
  | cons x xs ih =>
    intro k p hp
    simp only [List.zipIdx_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨le_rfl, by simp, by simp⟩
    · obtain ⟨hk, hlt, heq⟩ := ih (k + 1) p hp
      have hsub : p.2 - k = (p.2 - (k + 1)) + 1 := by omega
      refine ⟨by omega, by simp; omega, ?_⟩
      simp_rw [hsub, List.getElem_cons_succ]
      exact heq

private theorem getElem_mem_zipIdx {α : Type*} :
    ∀ (l : List α) (k i : ℕ) (hi : i < l.length),
      (l[i]'hi, k + i) ∈ l.zipIdx k := by
  intro l
  induction l with
  | nil => intro _ _ hi; simp at hi
  | cons x xs ih =>
    intro k i hi
    cases i with
    | zero => simp [List.zipIdx_cons]
    | succ j =>
      have hj : j < xs.length := Nat.succ_lt_succ_iff.mp hi
      simp only [List.zipIdx_cons, List.getElem_cons_succ, List.mem_cons]
      right
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih (k + 1) j hj

theorem econgAt_update_none (J : Graph) (wW : ℕ → ℝ)
    (emb? : ℕ → Option Walk) {eJ₀ : ℕ} (heJ₀ : eJ₀ < J.m) (hnone : emb? eJ₀ = none)
    (P : Walk) (eW : ℕ) :
    econgAt J (fun _ => 1) wW (partialToWalk (Function.update emb? eJ₀ (some P))) eW =
      econgAt J (fun _ => 1) wW (partialToWalk emb?) eW +
        if eW ∈ P.edges then 1 / wW eW else 0 := by
  unfold econgAt
  rw [Finset.sum_filter, Finset.sum_filter]
  have hzero : (if eW ∈ (partialToWalk emb? eJ₀).edges then (1 : ℝ) else 0) = 0 := by
    simp [partialToWalk, hnone, Walk.empty]
  have heJ_mem : eJ₀ ∈ Finset.range J.m := Finset.mem_range.mpr heJ₀
  rw [← Finset.add_sum_erase (Finset.range J.m) _ heJ_mem,
      ← Finset.add_sum_erase (Finset.range J.m) _ heJ_mem]
  have hsum_eq : ∑ j ∈ (Finset.range J.m).erase eJ₀,
        (if eW ∈ (partialToWalk (Function.update emb? eJ₀ (some P)) j).edges then (1 : ℝ) else 0) =
      ∑ j ∈ (Finset.range J.m).erase eJ₀,
        (if eW ∈ (partialToWalk emb? j).edges then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjne := Finset.ne_of_mem_erase hj
    rw [partialToWalk, Function.update_of_ne hjne]
    rfl
  rw [hsum_eq, hzero, zero_add]
  have hself : partialToWalk (Function.update emb? eJ₀ (some P)) eJ₀ = P := by
    simp [partialToWalk, Function.update_self]
  rw [hself, add_comm]
  split_ifs with hp
  · simp [add_div]
  · simp

theorem econgAt_update_none_le (J : Graph) (wW : ℕ → ℝ)
    (emb? : ℕ → Option Walk) {eJ₀ : ℕ} (heJ₀ : eJ₀ < J.m) (hnone : emb? eJ₀ = none)
    (P : Walk) {eW : ℕ} (hwW : 0 < wW eW) :
    econgAt J (fun _ => 1) wW (partialToWalk (Function.update emb? eJ₀ (some P))) eW ≤
      econgAt J (fun _ => 1) wW (partialToWalk emb?) eW + 1 / wW eW := by
  rw [econgAt_update_none J wW emb? heJ₀ hnone P eW]
  split_ifs
  · exact le_rfl
  · linarith [one_div_nonneg.mpr hwW.le]

theorem econgAt_mono_diff (J : Graph) (wW : ℕ → ℝ)
    (emb₀ emb₁ : ℕ → Option Walk)
    (hmono : ∀ eJ < J.m, emb₀ eJ = none ∨ emb₁ eJ = emb₀ eJ) (eW : ℕ) :
    econgAt J (fun _ => 1) wW (partialToWalk emb₁) eW -
      econgAt J (fun _ => 1) wW (partialToWalk emb₀) eW =
      (((Finset.range J.m).filter (fun eJ =>
        (emb₀ eJ).isNone = true ∧ (emb₁ eJ).isSome = true ∧
          eW ∈ (partialToWalk emb₁ eJ).edges)).card : ℝ) / wW eW := by
  unfold econgAt
  rw [← sub_div]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib,
      ← mul_one (((Finset.range J.m).filter _).card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const,
      Finset.sum_filter]
  refine Finset.sum_congr rfl fun eJ heJ => ?_
  have heJm : eJ < J.m := Finset.mem_range.mp heJ
  rcases hmono eJ heJm with h0 | h01
  · have hnotin : eW ∉ (partialToWalk emb₀ eJ).edges := by
      simp [partialToWalk, h0, Walk.empty]
    simp only [hnotin, ↓reduceIte, sub_zero]
    cases h1 : emb₁ eJ with
    | none =>
      have hnotin1 : eW ∉ (partialToWalk emb₁ eJ).edges := by
        simp [partialToWalk, h1, Walk.empty]
      simp [h0, hnotin1]
    | some P₁ =>
      by_cases he : eW ∈ (partialToWalk emb₁ eJ).edges <;> simp [h0, he]
  · have hed : (partialToWalk emb₁ eJ).edges = (partialToWalk emb₀ eJ).edges := by
      simp [partialToWalk, h01]
    rw [hed, sub_self]
    cases h0 : emb₀ eJ with
    | none =>
      rw [h0] at h01
      simp [h01]
    | some P₀ => simp

/-! ## Task 3 measures, invariants, and round bound -/

/-- Set of unembedded `J`-edge indices (`< J.m`) in Task 3 state `s`. -/
def unembeddedSet2 {DSState : Type} (J : Graph) (s : Task3State DSState) : Finset ℕ :=
  (Finset.range J.m).filter fun eJ => (s.embJW eJ).isNone

/-- Number of unembedded `J`-edges in Task 3 state `s`. -/
def unembeddedCount2 {DSState : Type} (J : Graph) (s : Task3State DSState) : ℕ :=
  (unembeddedSet2 J s).card

/-- Explicit `O(log m)` upper bound on the number of rounds `η₂` in Task 3 (`Claim 8.9`, p. 44). -/
def eta2Bound (J : Graph) : ℕ :=
  1 + 2 * (Nat.log 2 (J.m + 1) + 1)

theorem task3OuterCond_false_iff {DSState : Type} (J : Graph) (s : Task3State DSState) :
    task3OuterCond J s = false ↔ ∀ eJ < J.m, (s.embJW eJ).isSome = true := by
  unfold task3OuterCond
  rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
  push Not
  simp only [List.mem_range, Bool.not_eq_true, Option.isNone_eq_false_iff]

theorem task3OuterCond_false_iff_unemb {DSState : Type} (J : Graph) (s : Task3State DSState) :
    task3OuterCond J s = false ↔ unembeddedSet2 J s = ∅ := by
  rw [task3OuterCond_false_iff]
  simp only [unembeddedSet2, Finset.filter_eq_empty_iff, Finset.mem_range,
    Option.isNone_iff_eq_none, Option.isSome_iff_ne_none, ne_eq]

theorem unembeddedCount2_update_none {DSState : Type} (J : Graph) (s : Task3State DSState)
    {eJ : ℕ} (heJ : eJ < J.m) (hnone : s.embJW eJ = none) (P : Walk) :
    unembeddedSet2 J { s with embJW := Function.update s.embJW eJ (some P) } =
      (unembeddedSet2 J s).erase eJ ∧
    unembeddedCount2 J { s with embJW := Function.update s.embJW eJ (some P) } + 1 =
      unembeddedCount2 J s := by
  have hmem : eJ ∈ unembeddedSet2 J s := by simp [unembeddedSet2, heJ, hnone]
  have hset : unembeddedSet2 J { s with embJW := Function.update s.embJW eJ (some P) } =
      (unembeddedSet2 J s).erase eJ := by
    ext j
    simp only [unembeddedSet2, Finset.mem_filter, Finset.mem_range, Finset.mem_erase,
      Option.isNone_iff_eq_none]
    by_cases hj : j = eJ
    · subst hj; simp [Function.update_self]
    · simp [hj]
  refine ⟨hset, ?_⟩
  unfold unembeddedCount2
  rw [hset]
  exact Finset.card_erase_add_one hmem

theorem one_div_phi_dec_le_tau2_half {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    1 / wd.φ_dec ≤ wd.τ₂ / 2 := by
  intro wd
  have h1 : 1 / wd.φ_dec ≤ 1 / wd.φ_ds :=
    one_div_le_one_div_of_le hw.φ_ds_pos hw.φ_ds_le_dec
  have h2 : 1 / wd.φ_ds ≤ wd.γ_ExpPath := hw.γ_ExpPath_ge
  have h3 : (1 : ℝ) ≤ wd.γ_del / (2 * wd.φ_ds) := by
    rw [one_le_div (mul_pos two_pos hw.φ_ds_pos)]
    have h4 : 2 * wd.φ_ds ≤ 1 := by linarith [hw.φ_ds_half]
    linarith [hw.γ_del_ge]
  have hγE : 0 ≤ wd.γ_ExpPath :=
    le_trans (div_nonneg zero_le_one hw.φ_dec_pos.le) (le_trans h1 h2)
  have hτ : wd.τ₂ / 2 = wd.γ_ExpPath * (wd.γ_del / (2 * wd.φ_ds)) := by
    change (wd.γ_ExpPath * wd.γ_del / wd.φ_ds) / 2 = _
    ring
  rw [hτ]
  calc 1 / wd.φ_dec ≤ wd.γ_ExpPath := le_trans h1 h2
    _ = wd.γ_ExpPath * 1 := (mul_one _).symm
    _ ≤ wd.γ_ExpPath * (wd.γ_del / (2 * wd.φ_ds)) :=
        mul_le_mul_of_nonneg_left h3 hγE

/-- Core Task 3 invariant maintained inside `task3InnerLoop`, `task3MiddleLoop`, and `task3Round`. -/
structure Task3CoreInv (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Prop where
  ds_len : s.dsW.length = wd.comps.length
  ds_inv : ∀ ci (hci : ci < wd.comps.length),
    pathDS.Inv wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
      (s.dsW[ci]'(by rw [ds_len]; exact hci))
  Vhat_sub : ∀ ci (hci : ci < wd.comps.length),
    pathDS.Vhat (s.dsW[ci]'(by rw [ds_len]; exact hci)) ⊆ (wd.comps[ci]'hci).W_sub.verts
  Vhat_vol : ∀ ci (hci : ci < wd.comps.length),
    ((wd.comps[ci]'hci).W_sub.vol (pathDS.Vhat (s.dsW[ci]'(by rw [ds_len]; exact hci))) : ℝ) ≤
      wd.γ_del * ((pathDS.deleted (s.dsW[ci]'(by rw [ds_len]; exact hci))).card : ℝ) / wd.φ_ds
  partial_emb : IsPartialEmbedding J wd.W s.embJW
  j0_and_loops_embedded : ∀ eJ < J.m,
    (wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
     ∃ eW, wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
    (s.embJW eJ).isSome = true
  emb_len : ∀ eJ < J.m, ((partialToWalk s.embJW eJ).edges.length : ℝ) ≤ wd.γ_ExpPath
  econg_half : ∀ eW < wd.W.m,
    econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW ≤ (s.η₂ + 1 / 2 : ℝ) * wd.τ₂
  j0_econg : ∀ eW < wd.j0Edges.length,
    econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW ≤ wd.τ₂ / 2
  deleted_spec : ∀ ci (hci : ci < wd.comps.length) eL,
    eL ∈ pathDS.deleted (s.dsW[ci]'(by rw [ds_len]; exact hci)) →
    eL < (wd.comps[ci]'hci).W_sub.m ∧
    (s.η₂ : ℝ) * wd.τ₂ ≤
      econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) ((wd.comps[ci]'hci).wStart + eL)
  initCount_eq : s.initCountW = s.η₂ * wd.comps.length
  initEdges_eq : s.initEdgesW = s.η₂ * (wd.comps.map fun c => c.W_sub.m).sum
  middle_eq : s.middleIters2 = s.getPathCountW
  unemb_eq : s.getPathCountW + unembeddedCount2 J s ≤ J.m
  econgUpdates_le : (s.econgUpdates : ℝ) ≤ (s.getPathCountW : ℝ) * wd.γ_ExpPath

/-- Strong invariant holding between `task3MiddleStep` calls and at the end of `task3Round`. -/
structure Task3LoopInv (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Prop extends Task3CoreInv pathDS J wd s where
  active_uncongested : ∀ ci (hci : ci < wd.comps.length) eL,
    eL < (wd.comps[ci]'hci).W_sub.m →
    eL ∉ pathDS.deleted (s.dsW[ci]'(by rw [ds_len]; exact hci)) →
    econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) ((wd.comps[ci]'hci).wStart + eL) ≤
      (s.η₂ : ℝ) * wd.τ₂

/-- Round-relative delta invariant for Task 3. -/
structure Task3RoundRel (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s_prev s : Task3State pathDS.State) : Prop where
  emb_mono : ∀ eJ < J.m, s_prev.embJW eJ = none ∨ s.embJW eJ = s_prev.embJW eJ
  inner_eq : s.innerIters2 = s_prev.innerIters2 +
    ∑ ci ∈ Finset.range wd.comps.length,
      (pathDS.deleted (s.dsW.getD ci (pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩))).card
  del_eq : s.deleteCountW = s.innerIters2 - s_prev.innerIters2 + s_prev.deleteCountW
  getPath_eq : s.getPathCountW + unembeddedCount2 J s =
    s_prev.getPathCountW + unembeddedCount2 J s_prev

/-! ## Inner loop (`task3InnerStep` and `task3InnerLoop`) -/

private theorem findCongestedWEdge_spec (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) (hlen : s.dsW.length = wd.comps.length) {ci eL : ℕ}
    (hf : findCongestedWEdge pathDS J wd s = some (ci, eL)) :
    ∃ (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      let ds := s.dsW[ci]'(by rw [hlen]; exact hci)
      eL < c.W_sub.m ∧ eL ∉ pathDS.deleted ds ∧
      (s.η₂ : ℝ) * wd.τ₂ ≤ econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) (c.wStart + eL) := by
  unfold findCongestedWEdge at hf
  have hmem := head?_some_mem2 hf
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨⟨c', ci'⟩, hzip, hfmap⟩
  obtain ⟨_, hci', hc'_eq⟩ := mem_zipIdx_spec wd.comps 0 (c', ci') hzip
  simp only [Nat.sub_zero] at hci' hc'_eq
  rw [← hc'_eq] at hfmap
  rw [List.mem_filterMap] at hfmap
  rcases hfmap with ⟨eL', heL'_r, hite⟩
  have heL'_m : eL' < (wd.comps[ci']'hci').W_sub.m := List.mem_range.mp heL'_r
  split_ifs at hite with hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hite
  rcases hite with ⟨rfl, rfl⟩
  refine ⟨hci', heL'_m, ?_⟩
  have hci_ds : ci' < s.dsW.length := by rw [hlen]; exact hci'
  rw [List.getD_eq_getElem _ _ hci_ds] at hcond
  exact hcond

private theorem task3InnerStep_inv {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task3State tools.pathDS.State}
    (hinv : Task3CoreInv tools.pathDS J (buildWitness tools H' J embJH) s)
    (hrel : Task3RoundRel tools.pathDS J (buildWitness tools H' J embJH) s_prev s)
    (hcond : task3InnerCond tools.pathDS J (buildWitness tools H' J embJH) s = true) :
    let wd := buildWitness tools H' J embJH
    let dsDef := tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
    let s' := task3InnerStep tools.pathDS J wd s
    Task3CoreInv tools.pathDS J wd s' ∧
    Task3RoundRel tools.pathDS J wd s_prev s' ∧
    (∑ ci ∈ Finset.range wd.comps.length,
      ((wd.comps[ci]?.map fun c => c.W_sub.m).getD 0 -
        (tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card)) <
    (∑ ci ∈ Finset.range wd.comps.length,
      ((wd.comps[ci]?.map fun c => c.W_sub.m).getD 0 -
        (tools.pathDS.deleted (s.dsW.getD ci dsDef)).card)) := by
  intro wd dsDef s'
  unfold task3InnerCond at hcond
  cases hf : findCongestedWEdge tools.pathDS J wd s with
  | none => rw [hf] at hcond; simp at hcond
  | some p =>
    rcases p with ⟨ci, eL⟩
    obtain ⟨hci, heL_m, heL_notdel, hecong_ge⟩ :=
      findCongestedWEdge_spec tools.pathDS J wd s hinv.ds_len hf
    set c := wd.comps[ci]'hci
    have hci_ds : ci < s.dsW.length := by rw [hinv.ds_len]; exact hci
    set ds0 := s.dsW[ci]'hci_ds
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp, _⟩
    have hdel := tools.pathDS.delete_spec wd.φ_Const wd.M_W c.W_sub ds0 eL
      hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
      (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp (hinv.ds_inv ci hci) heL_m heL_notdel
    rcases hdel with ⟨hinv1, hdel1, hVsub1, hVtop1, _, hVvol1⟩
    set res := tools.pathDS.delete ds0 eL
    have hs'_eq : s' =
        { s with
          dsW := s.dsW.set ci res.1
          deleteCountW := s.deleteCountW + 1
          innerIters2 := s.innerIters2 + 1 } := by
      dsimp only [s', task3InnerStep]
      rw [hf]
      dsimp only
      rw [List.getD_eq_getElem _ _ hci_ds]
    have hds_len' : s'.dsW.length = wd.comps.length := by
      rw [hs'_eq, List.length_set]
      exact hinv.ds_len
    have hvol1_wd : (c.W_sub.vol (tools.pathDS.Vhat res.1) : ℝ) ≤
        wd.γ_del * ((tools.pathDS.deleted res.1).card : ℝ) / wd.φ_ds := by
      have hγ : tools.pathDS.γ_del wd.φ_Const wd.M_W ≤ wd.γ_del := le_max_right _ _
      have hφ : wd.φ_ds ≤ tools.pathDS.φ_out wd.φ_Const wd.M_W := min_le_right _ _
      have hγ_nn : 0 ≤ tools.pathDS.γ_del wd.φ_Const wd.M_W :=
        le_trans (by norm_num) (tools.pathDS.hγ_del_ge wd.φ_Const wd.M_W hw.φ_Const_pos)
      have hnum : tools.pathDS.γ_del wd.φ_Const wd.M_W * ((tools.pathDS.deleted res.1).card : ℝ) ≤
          wd.γ_del * ((tools.pathDS.deleted res.1).card : ℝ) :=
        mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg _)
      have hnn : 0 ≤ tools.pathDS.γ_del wd.φ_Const wd.M_W * ((tools.pathDS.deleted res.1).card : ℝ) :=
        mul_nonneg hγ_nn (Nat.cast_nonneg _)
      exact le_trans hVvol1 (div_le_div₀ (le_trans hnn hnum) hnum hw.φ_ds_pos hφ)
    have hds_set : ∀ cj (hcj : cj < wd.comps.length),
        s'.dsW[cj]'(by rw [hds_len']; exact hcj) =
          if cj = ci then res.1 else s.dsW[cj]'(by rw [hinv.ds_len]; exact hcj) := by
      intro cj hcj
      simp only [hs'_eq]
      by_cases heq : cj = ci
      · subst heq; simp [List.getElem_set_self]
      · simp [heq, List.getElem_set_ne (Ne.symm heq)]
    have hcore' : Task3CoreInv tools.pathDS J wd s' :=
      { ds_len := hds_len'
        ds_inv := fun cj hcj => by
          rw [hds_set cj hcj]
          split_ifs with heq
          · subst heq; exact hinv1
          · exact hinv.ds_inv cj hcj
        Vhat_sub := fun cj hcj => by
          rw [hds_set cj hcj]
          split_ifs with heq
          · subst heq; exact hVtop1
          · exact hinv.Vhat_sub cj hcj
        Vhat_vol := fun cj hcj => by
          rw [hds_set cj hcj]
          split_ifs with heq
          · subst heq; exact hvol1_wd
          · exact hinv.Vhat_vol cj hcj
        partial_emb := by rw [hs'_eq]; exact hinv.partial_emb
        j0_and_loops_embedded := by rw [hs'_eq]; exact hinv.j0_and_loops_embedded
        emb_len := by rw [hs'_eq]; exact hinv.emb_len
        econg_half := by rw [hs'_eq]; exact hinv.econg_half
        j0_econg := by rw [hs'_eq]; exact hinv.j0_econg
        deleted_spec := by
          intro cj hcj b hb
          rw [hds_set cj hcj] at hb
          split_ifs at hb with heq
          · subst heq
            rw [hdel1, Finset.mem_insert] at hb
            rcases hb with rfl | hb0
            · refine ⟨heL_m, ?_⟩
              simp only [hs'_eq]
              exact hecong_ge
            · have hprev := hinv.deleted_spec cj hcj b hb0
              simp only [hs'_eq]
              exact hprev
          · have hprev := hinv.deleted_spec cj hcj b hb
            simp only [hs'_eq]
            exact hprev
        initCount_eq := by rw [hs'_eq]; exact hinv.initCount_eq
        initEdges_eq := by rw [hs'_eq]; exact hinv.initEdges_eq
        middle_eq := by rw [hs'_eq]; exact hinv.middle_eq
        unemb_eq := by
          rw [hs'_eq]
          exact hinv.unemb_eq
        econgUpdates_le := by rw [hs'_eq]; exact hinv.econgUpdates_le }
    have hcard_eq :
        ∑ cj ∈ Finset.range wd.comps.length,
          (tools.pathDS.deleted (s'.dsW.getD cj dsDef)).card =
        (∑ cj ∈ Finset.range wd.comps.length,
          (tools.pathDS.deleted (s.dsW.getD cj dsDef)).card) + 1 := by
      have hmem_ci : ci ∈ Finset.range wd.comps.length := Finset.mem_range.mpr hci
      rw [← Finset.add_sum_erase _ _ hmem_ci, ← Finset.add_sum_erase _ _ hmem_ci]
      have hrest :
          ∑ cj ∈ (Finset.range wd.comps.length).erase ci,
            (tools.pathDS.deleted (s'.dsW.getD cj dsDef)).card =
          ∑ cj ∈ (Finset.range wd.comps.length).erase ci,
            (tools.pathDS.deleted (s.dsW.getD cj dsDef)).card := by
        refine Finset.sum_congr rfl fun cj hcj_er => ?_
        have hcj := Finset.mem_range.mp (Finset.mem_of_mem_erase hcj_er)
        have hjne := Finset.ne_of_mem_erase hcj_er
        have hcj_s : cj < s.dsW.length := by rw [hinv.ds_len]; exact hcj
        have hcj_s' : cj < s'.dsW.length := by rw [hds_len']; exact hcj
        rw [List.getD_eq_getElem _ _ hcj_s, List.getD_eq_getElem _ _ hcj_s', hds_set cj hcj]
        simp only [hjne, ↓reduceIte]
      rw [hrest]
      have hci_s' : ci < s'.dsW.length := by rw [hds_len']; exact hci
      rw [List.getD_eq_getElem _ _ hci_ds, List.getD_eq_getElem _ _ hci_s', hds_set ci hci]
      simp only [↓reduceIte, hdel1, Finset.card_insert_of_notMem heL_notdel]
      ring
    have hrel' : Task3RoundRel tools.pathDS J wd s_prev s' :=
      { emb_mono := by rw [hs'_eq]; exact hrel.emb_mono
        inner_eq := by
          have hs_in : s'.innerIters2 = s.innerIters2 + 1 := by rw [hs'_eq]
          have h1 : s'.innerIters2 = s_prev.innerIters2 +
              ((∑ cj ∈ Finset.range wd.comps.length,
                (tools.pathDS.deleted (s.dsW.getD cj dsDef)).card) + 1) := by
            rw [hs_in, hrel.inner_eq]; ring
          change s'.innerIters2 = s_prev.innerIters2 +
            ∑ cj ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsW.getD cj dsDef)).card
          rw [h1, ← hcard_eq]
        del_eq := by
          have h1 : s'.innerIters2 = s.innerIters2 + 1 := by rw [hs'_eq]
          have h2 : s'.deleteCountW = s.deleteCountW + 1 := by rw [hs'_eq]
          have hle : s_prev.innerIters2 ≤ s.innerIters2 := by rw [hrel.inner_eq]; exact Nat.le_add_right _ _
          have hd := hrel.del_eq
          omega
        getPath_eq := by
          rw [hs'_eq]
          exact hrel.getPath_eq }
    have hmeas :
        (∑ cj ∈ Finset.range wd.comps.length,
          ((wd.comps[cj]?.map fun c => c.W_sub.m).getD 0 -
            (tools.pathDS.deleted (s'.dsW.getD cj dsDef)).card)) <
        (∑ cj ∈ Finset.range wd.comps.length,
          ((wd.comps[cj]?.map fun c => c.W_sub.m).getD 0 -
            (tools.pathDS.deleted (s.dsW.getD cj dsDef)).card)) := by
      have hmem_ci : ci ∈ Finset.range wd.comps.length := Finset.mem_range.mpr hci
      rw [← Finset.add_sum_erase _ _ hmem_ci, ← Finset.add_sum_erase _ _ hmem_ci]
      have hrest :
          ∑ cj ∈ (Finset.range wd.comps.length).erase ci,
            ((wd.comps[cj]?.map fun c => c.W_sub.m).getD 0 -
              (tools.pathDS.deleted (s'.dsW.getD cj dsDef)).card) =
          ∑ cj ∈ (Finset.range wd.comps.length).erase ci,
            ((wd.comps[cj]?.map fun c => c.W_sub.m).getD 0 -
              (tools.pathDS.deleted (s.dsW.getD cj dsDef)).card) := by
        refine Finset.sum_congr rfl fun cj hcj_er => ?_
        have hcj := Finset.mem_range.mp (Finset.mem_of_mem_erase hcj_er)
        have hjne := Finset.ne_of_mem_erase hcj_er
        have hcj_s : cj < s.dsW.length := by rw [hinv.ds_len]; exact hcj
        have hcj_s' : cj < s'.dsW.length := by rw [hds_len']; exact hcj
        rw [List.getD_eq_getElem _ _ hcj_s, List.getD_eq_getElem _ _ hcj_s', hds_set cj hcj]
        simp only [hjne, ↓reduceIte]
      rw [hrest]
      have hci_s' : ci < s'.dsW.length := by rw [hds_len']; exact hci
      have hcard_le : (tools.pathDS.deleted res.1).card ≤ c.W_sub.m := by
        have hsub : tools.pathDS.deleted res.1 ⊆ Finset.range c.W_sub.m := by
          intro b hb
          rw [Finset.mem_range]
          have hb' := (hcore'.deleted_spec ci hci b
            (by rw [hds_set ci hci]; simp only [↓reduceIte]; exact hb)).1
          exact hb'
        simpa [Finset.card_range] using Finset.card_le_card hsub
      have hcard_eq_ci : (tools.pathDS.deleted res.1).card = (tools.pathDS.deleted ds0).card + 1 := by
        rw [hdel1, Finset.card_insert_of_notMem heL_notdel]
      have hcomp_ci : (wd.comps[ci]?.map fun c => c.W_sub.m).getD 0 = c.W_sub.m := by
        simp [List.getElem?_eq_getElem hci, c]
      have hlt_ci : c.W_sub.m - ((tools.pathDS.deleted ds0).card + 1) <
          c.W_sub.m - (tools.pathDS.deleted ds0).card := by
        have hlt_card : (tools.pathDS.deleted ds0).card < c.W_sub.m := by omega
        exact Nat.sub_lt_sub_left hlt_card (Nat.lt_succ_self _)
      rw [List.getD_eq_getElem _ _ hci_ds, List.getD_eq_getElem _ _ hci_s', hds_set ci hci]
      simp only [↓reduceIte, hcomp_ci, hcard_eq_ci]
      exact Nat.add_lt_add_right hlt_ci _
    exact ⟨hcore', hrel', hmeas⟩

theorem task3InnerLoop_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task3State tools.pathDS.State}
    (hinv : Task3CoreInv tools.pathDS J (buildWitness tools H' J embJH) s)
    (hrel : Task3RoundRel tools.pathDS J (buildWitness tools H' J embJH) s_prev s) :
    let wd := buildWitness tools H' J embJH
    let s_out := whileFuel wd.W.m (task3InnerCond tools.pathDS J wd)
      (task3InnerStep tools.pathDS J wd) s
    Task3LoopInv tools.pathDS J wd s_out ∧
    Task3RoundRel tools.pathDS J wd s_prev s_out ∧
    s_out.embJW = s.embJW ∧
    s_out.getPathCountW = s.getPathCountW ∧
    s_out.middleIters2 = s.middleIters2 ∧
    s_out.econgUpdates = s.econgUpdates ∧
    s_out.initCountW = s.initCountW ∧
    s_out.initEdgesW = s.initEdgesW ∧
    s_out.η₂ = s.η₂ := by
  intro wd s_out
  let dsDef := tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
  let P : Task3State tools.pathDS.State → Prop := fun st =>
    Task3CoreInv tools.pathDS J wd st ∧
    Task3RoundRel tools.pathDS J wd s_prev st ∧
    st.embJW = s.embJW ∧
    st.getPathCountW = s.getPathCountW ∧
    st.middleIters2 = s.middleIters2 ∧
    st.econgUpdates = s.econgUpdates ∧
    st.initCountW = s.initCountW ∧
    st.initEdgesW = s.initEdgesW ∧
    st.η₂ = s.η₂
  let meas : Task3State tools.pathDS.State → ℕ := fun st =>
    ∑ ci ∈ Finset.range wd.comps.length,
      ((wd.comps[ci]?.map fun c => c.W_sub.m).getD 0 -
        (tools.pathDS.deleted (st.dsW.getD ci dsDef)).card)
  have hstep : ∀ st, P st → task3InnerCond tools.pathDS J wd st = true →
      P (task3InnerStep tools.pathDS J wd st) ∧
        meas (task3InnerStep tools.pathDS J wd st) < meas st := by
    intro st ⟨hst_inv, hst_rel, hrest⟩ hc
    obtain ⟨h1, h2, h3⟩ := task3InnerStep_inv tools H' J embJH hw hst_inv hst_rel hc
    refine ⟨⟨h1, h2, ?_⟩, h3⟩
    unfold task3InnerCond at hc
    cases hf : findCongestedWEdge tools.pathDS J wd st with
    | none => rw [hf] at hc; simp at hc
    | some p => simpa [task3InnerStep, hf] using hrest
  have hmeas_le : meas s ≤ wd.W.m := by
    have hsum1 : meas s ≤ ∑ ci ∈ Finset.range wd.comps.length,
        (wd.comps.getD ci defaultCompInfo).W_sub.m := by
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci := Finset.mem_range.mp hci_r
      simp only [List.getElem?_eq_getElem hci, Option.map_some, Option.getD_some,
        List.getD_eq_getElem _ _ hci]
      exact Nat.sub_le _ _
    have hsum_eq : (∑ ci ∈ Finset.range wd.comps.length,
        (wd.comps.getD ci defaultCompInfo).W_sub.m) =
        (wd.comps.map fun c => c.W_sub.m).sum := by
      induction wd.comps with
      | nil => simp
      | cons a as ih =>
        rw [List.length_cons, Finset.sum_range_succ', add_comm, List.map_cons, List.sum_cons]
        have h0 : (a :: as).getD 0 defaultCompInfo = a := rfl
        have hs : ∀ i, (a :: as).getD (i + 1) defaultCompInfo = as.getD i defaultCompInfo := fun _ => rfl
        simp_rw [hs]
        rw [h0, ih]
    have hWm : (wd.comps.map fun c => c.W_sub.m).sum ≤ wd.W.m := by
      dsimp only [wd]
      rw [hw.W_m_eq]
      exact Nat.le_add_left _ _
    exact le_trans hsum1 (le_trans (le_of_eq hsum_eq) hWm)
  have hinv_out : P s_out :=
    whileFuel_inv P (task3InnerCond tools.pathDS J wd)
      (task3InnerStep tools.pathDS J wd) (fun st h c => (hstep st h c).1) wd.W.m s
      ⟨hinv, hrel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdone : task3InnerCond tools.pathDS J wd s_out = false :=
    whileFuel_done P meas (task3InnerCond tools.pathDS J wd)
      (task3InnerStep tools.pathDS J wd) hstep wd.W.m s
      ⟨hinv, hrel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hmeas_le
  have hactive : ∀ ci (hci : ci < wd.comps.length) eL,
      eL < (wd.comps[ci]'hci).W_sub.m →
      eL ∉ tools.pathDS.deleted (s_out.dsW[ci]'(by rw [hinv_out.1.ds_len]; exact hci)) →
      econgAt J (fun _ => 1) wd.wW (partialToWalk s_out.embJW)
        ((wd.comps[ci]'hci).wStart + eL) ≤ (s_out.η₂ : ℝ) * wd.τ₂ := by
    intro ci hci eL heL hnotdel
    unfold task3InnerCond at hdone
    rw [Bool.eq_false_iff, ne_eq, Option.isSome_iff_exists] at hdone
    have hnone : findCongestedWEdge tools.pathDS J wd s_out = none := by
      cases hf : findCongestedWEdge tools.pathDS J wd s_out with
      | none => rfl
      | some a => exact False.elim (hdone ⟨a, hf⟩)
    unfold findCongestedWEdge at hnone
    dsimp only at hnone
    rw [List.head?_eq_none_iff] at hnone
    by_contra hlt
    push Not at hlt
    have hmem : (ci, eL) ∈ ([] : List (ℕ × ℕ)) := by
      rw [← hnone, List.mem_flatMap]
      refine ⟨(wd.comps[ci]'hci, ci), ?_, ?_⟩
      · simpa using getElem_mem_zipIdx wd.comps 0 ci hci
      · rw [List.mem_filterMap]
        refine ⟨eL, List.mem_range.mpr heL, ?_⟩
        have hci_ds : ci < s_out.dsW.length := by rw [hinv_out.1.ds_len]; exact hci
        simp only [List.getD_eq_getElem _ _ hci_ds]
        simp only [hnotdel, hlt.le, not_false_eq_true, and_self, ↓reduceIte]
    simp at hmem
  exact ⟨⟨hinv_out.1, hactive⟩, hinv_out.2⟩

/-! ## Middle loop (`task3MiddleStep` and `task3MiddleLoop`) -/

theorem findReadyJEdge_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    (s : Task3State tools.pathDS.State)
    (hlen : s.dsW.length = (buildWitness tools H' J embJH).comps.length)
    {eJ ci jLocal : ℕ}
    (hf : findReadyJEdge tools.pathDS J (buildWitness tools H' J embJH) s = some (eJ, ci, jLocal)) :
    let wd := buildWitness tools H' J embJH
    ∃ (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      let ds := s.dsW[ci]'(by rw [hlen]; exact hci)
      eJ < J.m ∧
      s.embJW eJ = none ∧
      wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jLocal ∧
      jLocal < c.J_sub.m ∧
      c.jSubOrigEdges.getD jLocal 0 = eJ ∧
      J.edges.getD eJ (0, 0) =
        (c.verts.getD (c.J_sub.edges.getD jLocal (0, 0)).1 0,
         c.verts.getD (c.J_sub.edges.getD jLocal (0, 0)).2 0) ∧
      (c.J_sub.edges.getD jLocal (0, 0)).1 ∉ tools.pathDS.Vhat ds ∧
      (c.J_sub.edges.getD jLocal (0, 0)).2 ∉ tools.pathDS.Vhat ds := by
  intro wd
  unfold findReadyJEdge at hf
  have hmem := head?_some_mem2 hf
  rw [List.mem_filterMap] at hmem
  rcases hmem with ⟨e', he'_range, hif⟩
  have he'm : e' < J.m := List.mem_range.mp he'_range
  dsimp only at hif
  split_ifs at hif with hnone
  cases hsrc : wd.jSources.getD e' JEdgeSource.isLoop with
  | isLoop => rw [hsrc] at hif; simp at hif
  | inJ0 _ => rw [hsrc] at hif; simp at hif
  | inComp ci' jL' =>
    rw [hsrc] at hif
    dsimp only at hif
    split_ifs at hif with hV
    simp only [Option.some.injEq, Prod.mk.injEq] at hif
    rcases hif with ⟨rfl, rfl, rfl⟩
    have hcase := jSources_cases tools H' J embJH hJ hw he'm
    dsimp only at hcase
    have hsrc' : (buildWitness tools H' J embJH).jSources.getD e' JEdgeSource.isLoop =
        JEdgeSource.inComp ci' jL' := hsrc
    rw [hsrc'] at hcase
    rcases hcase with ⟨hci, hj, horig, hjLm, hends⟩
    have hci_ds : ci' < s.dsW.length := by rw [hlen]; exact hci
    rw [List.getD_eq_getElem _ _ hci, List.getD_eq_getElem _ _ hci_ds] at hV
    refine ⟨hci, he'm, Option.isNone_iff_eq_none.mp hnone, hsrc, hjLm, ?_, hends, hV.1, hV.2⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact horig

theorem task3MiddleStep_inv {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task3State tools.pathDS.State}
    (hloop : Task3LoopInv tools.pathDS J (buildWitness tools H' J embJH) s)
    (hrel : Task3RoundRel tools.pathDS J (buildWitness tools H' J embJH) s_prev s)
    (hcond : task3MiddleCond tools.pathDS J (buildWitness tools H' J embJH) s = true) :
    let wd := buildWitness tools H' J embJH
    let s' := task3MiddleStep tools.pathDS J wd s
    Task3LoopInv tools.pathDS J wd s' ∧
    Task3RoundRel tools.pathDS J wd s_prev s' ∧
    unembeddedCount2 J s' < unembeddedCount2 J s ∧
    s'.η₂ = s.η₂ ∧
    s'.initCountW = s.initCountW ∧
    s'.initEdgesW = s.initEdgesW := by
  intro wd s'
  unfold task3MiddleCond at hcond
  cases hf : findReadyJEdge tools.pathDS J wd s with
  | none => rw [hf] at hcond; simp at hcond
  | some p =>
    rcases p with ⟨eJ, ci, jLocal⟩
    obtain ⟨hci, heJm, hs_none, _, hjLm, _, hends, hV1, hV2⟩ :=
      findReadyJEdge_spec tools H' J embJH hJ hw s hloop.ds_len hf
    set c := wd.comps[ci]'hci
    have hci_ds : ci < s.dsW.length := by rw [hloop.ds_len]; exact hci
    set ds0 := s.dsW[ci]'hci_ds
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, hc_Jn, hc_Jvalid, _, _, _, _,
       hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp,
       _, _, _, _, _, hc_wStart, _⟩
    set eLoc := c.J_sub.edges.getD jLocal (0, 0)
    have heLoc_mem : eLoc ∈ c.J_sub.edges := by
      have heq : eLoc = c.J_sub.edges[jLocal]'hjLm := List.getD_eq_getElem _ _ hjLm
      rw [heq]
      exact List.getElem_mem hjLm
    have heLoc_valid := hc_Jvalid eLoc heLoc_mem
    have hu_V : eLoc.1 ∈ c.W_sub.verts \ tools.pathDS.Vhat ds0 := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, hV1⟩
      rw [hc_Wn, ← hc_Jn]; exact heLoc_valid.1
    have hv_V : eLoc.2 ∈ c.W_sub.verts \ tools.pathDS.Vhat ds0 := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, hV2⟩
      rw [hc_Wn, ← hc_Jn]; exact heLoc_valid.2
    have hget := tools.pathDS.getPath_spec wd.φ_Const wd.M_W c.W_sub ds0 eLoc.1 eLoc.2
      hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
      (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp (hloop.ds_inv ci hci) hu_V hv_V
    rcases hget with ⟨hP_sub_walk, _, hP_sub_edges, _, hP_sub_len⟩
    set P_sub := tools.pathDS.getPath ds0 eLoc.1 eLoc.2
    set P_W := liftWSubWalk c P_sub
    have hP_W_walk : P_W.IsWalk wd.W (J.edges.getD eJ (0, 0)).1 (J.edges.getD eJ (0, 0)).2 := by
      have hw0 := isWalk_liftWSubWalk tools H' J embJH hw hci hP_sub_walk
      dsimp only [wd, c, P_W, eLoc] at hends ⊢
      rw [hends]
      exact hw0
    have hP_W_len : (P_W.edges.length : ℝ) ≤ wd.γ_ExpPath := by
      have hlen_eq : P_W.edges.length = P_sub.edges.length := liftWSubWalk_edges_length c P_sub
      rw [hlen_eq]
      exact le_trans hP_sub_len (le_max_right _ _)
    set s1 : Task3State tools.pathDS.State :=
      { s with
        embJW := Function.update s.embJW eJ (some P_W)
        getPathCountW := s.getPathCountW + 1
        econgUpdates := s.econgUpdates + P_W.edges.length
        middleIters2 := s.middleIters2 + 1 }
    have hs1_eq : s1 =
        { s with
          embJW := Function.update s.embJW eJ (some P_W)
          getPathCountW := s.getPathCountW + 1
          econgUpdates := s.econgUpdates + P_W.edges.length
          middleIters2 := s.middleIters2 + 1 } := rfl
    have hs'_eq : s' = whileFuel wd.W.m (task3InnerCond tools.pathDS J wd)
        (task3InnerStep tools.pathDS J wd) s1 := by
      have hcd : wd.comps.getD ci defaultCompInfo = c := List.getD_eq_getElem _ _ hci
      have hsd : s.dsW.getD ci (tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩) = ds0 :=
        List.getD_eq_getElem _ _ hci_ds
      dsimp only [s', task3MiddleStep]
      rw [hf]
      dsimp only
      rw [hcd, hsd]
    have htau2_half := one_div_phi_dec_le_tau2_half tools H' J embJH hw
    have hemb1 : IsPartialEmbedding J wd.W s1.embJW := by
      refine ⟨hloop.partial_emb.1, fun j hj P hP => ?_⟩
      by_cases hje : j = eJ
      · subst hje
        simp only [s1, Function.update_self, Option.some.injEq] at hP
        subst hP
        rw [List.getD_eq_getElem _ _ hj] at hP_W_walk
        exact hP_W_walk
      · simp only [s1, Function.update_of_ne hje] at hP
        exact hloop.partial_emb.2 j hj P hP
    have hunemb1 := unembeddedCount2_update_none J s heJm hs_none P_W
    have hcore1 : Task3CoreInv tools.pathDS J wd s1 :=
      { ds_len := hloop.ds_len
        ds_inv := hloop.ds_inv
        Vhat_sub := hloop.Vhat_sub
        Vhat_vol := hloop.Vhat_vol
        partial_emb := hemb1
        j0_and_loops_embedded := fun j hj hcase => by
          by_cases hje : j = eJ
          · subst hje; simp [s1]
          · simpa [s1, Function.update_of_ne hje] using hloop.j0_and_loops_embedded j hj hcase
        emb_len := fun j hj => by
          by_cases hje : j = eJ
          · subst hje
            simpa [s1, partialToWalk, Function.update_self] using hP_W_len
          · simpa [s1, partialToWalk, Function.update_of_ne hje] using hloop.emb_len j hj
        econg_half := fun eW heWm => by
          have heq := econgAt_update_none J wd.wW s.embJW heJm hs_none P_W eW
          change econgAt J (fun _ => 1) wd.wW (partialToWalk s1.embJW) eW ≤
            (s1.η₂ + 1 / 2 : ℝ) * wd.τ₂
          have hs1_eta : (s1.η₂ : ℝ) = (s.η₂ : ℝ) := rfl
          rw [show s1.embJW = Function.update s.embJW eJ (some P_W) from rfl, heq, hs1_eta]
          split_ifs with hePW
          · obtain ⟨eL, heL_sub, rfl⟩ := mem_edges_liftWSubWalk.mp hePW
            have heL_m : eL < c.W_sub.m := by
              rcases hP_sub_walk.2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hPe, _⟩
              · simp [hPe] at heL_sub
              · exact hPe eL heL_sub
            have heL_notdel : eL ∉ tools.pathDS.deleted ds0 := hP_sub_edges eL heL_sub
            have hactive := hloop.active_uncongested ci hci eL heL_m heL_notdel
            have hphi_le : wd.φ_dec ≤ wd.wW (c.wStart + eL) :=
              wW_ge_phi tools H' J embJH hw heWm
            have hdiv_le : 1 / wd.wW (c.wStart + eL) ≤ wd.τ₂ / 2 :=
              le_trans (one_div_le_one_div_of_le hw.φ_dec_pos hphi_le) htau2_half
            linarith
          · rw [add_zero]
            exact hloop.econg_half eW heWm
        j0_econg := fun eW heW0 => by
          have hnotPW : eW ∉ P_W.edges := by
            intro hePW
            obtain ⟨eL, _, rfl⟩ := mem_edges_liftWSubWalk.mp hePW
            have hw0 : wd.j0Edges.length ≤ (wd.comps[ci]'hci).wStart := hc_wStart
            change wd.j0Edges.length ≤ c.wStart at hw0
            omega
          have heq := econgAt_update_none J wd.wW s.embJW heJm hs_none P_W eW
          change econgAt J (fun _ => 1) wd.wW (partialToWalk s1.embJW) eW ≤ wd.τ₂ / 2
          rw [show s1.embJW = Function.update s.embJW eJ (some P_W) from rfl, heq]
          simp only [hnotPW, ↓reduceIte, add_zero]
          exact hloop.j0_econg eW heW0
        deleted_spec := fun cj hcj b hb => by
          have hprev := hloop.deleted_spec cj hcj b hb
          have hb_m : b < (wd.comps[cj]'hcj).W_sub.m := hprev.1
          have heWm := (W_edges_getD_comp tools H' J embJH hcj hb_m).1
          have hw_pos := wW_pos tools H' J embJH hw heWm
          have heq := econgAt_update_none_le J wd.wW s.embJW heJm hs_none P_W hw_pos
          refine ⟨hb_m, ?_⟩
          have hge0 : econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW)
              ((wd.comps[cj]'hcj).wStart + b) ≤
              econgAt J (fun _ => 1) wd.wW (partialToWalk s1.embJW)
                ((wd.comps[cj]'hcj).wStart + b) := by
            rw [show s1.embJW = Function.update s.embJW eJ (some P_W) from rfl,
              econgAt_update_none J wd.wW s.embJW heJm hs_none P_W]
            split_ifs
            · linarith [one_div_nonneg.mpr hw_pos.le]
            · linarith
          exact le_trans hprev.2 hge0
        initCount_eq := hloop.initCount_eq
        initEdges_eq := hloop.initEdges_eq
        middle_eq := by
          change s.middleIters2 + 1 = s.getPathCountW + 1
          rw [hloop.middle_eq]
        unemb_eq := by
          have hs1_gp : s1.getPathCountW = s.getPathCountW + 1 := rfl
          change s.getPathCountW + 1 + unembeddedCount2 J s1 ≤ J.m
          have hun2 : unembeddedCount2 J s1 + 1 = unembeddedCount2 J s := hunemb1.2
          have hle := hloop.unemb_eq
          omega
        econgUpdates_le := by
          change ((s.econgUpdates + P_W.edges.length : ℕ) : ℝ) ≤
            ((s.getPathCountW + 1 : ℕ) : ℝ) * wd.γ_ExpPath
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          exact add_le_add hloop.econgUpdates_le hP_W_len }
    have hrel1 : Task3RoundRel tools.pathDS J wd s_prev s1 :=
      { emb_mono := fun j hj => by
          by_cases hje : j = eJ
          · subst hje
            rcases hrel.emb_mono j hj with h | h
            · exact Or.inl h
            · rw [hs_none] at h
              exact Or.inl h.symm
          · simpa [s1, Function.update_of_ne hje] using hrel.emb_mono j hj
        inner_eq := hrel.inner_eq
        del_eq := hrel.del_eq
        getPath_eq := by
          have hun2 : unembeddedCount2 J s1 + 1 = unembeddedCount2 J s := hunemb1.2
          have hgp := hrel.getPath_eq
          change s.getPathCountW + 1 + unembeddedCount2 J s1 = s_prev.getPathCountW + unembeddedCount2 J s_prev
          omega }
    have hinner := task3InnerLoop_spec tools H' J embJH hw hcore1 hrel1
    rcases hinner with ⟨hloop', hrel', hemb_eq, _, _, _, hinitCount_eq, hinitEdges_eq, heta_eq⟩
    have hs'_eq' : s' = whileFuel (buildWitness tools H' J embJH).W.m
        (task3InnerCond tools.pathDS J (buildWitness tools H' J embJH))
        (task3InnerStep tools.pathDS J (buildWitness tools H' J embJH)) s1 := hs'_eq
    have hunemb_lt : unembeddedCount2 J s' < unembeddedCount2 J s := by
      have hun_eq : unembeddedCount2 J s' = unembeddedCount2 J s1 := by
        simp only [unembeddedCount2, unembeddedSet2]
        rw [hs'_eq', hemb_eq]
      have hun2 : unembeddedCount2 J s1 + 1 = unembeddedCount2 J s := hunemb1.2
      omega
    exact ⟨by simpa [← hs'_eq'] using hloop',
           by simpa [← hs'_eq'] using hrel',
           hunemb_lt,
           by simpa [← hs'_eq'] using heta_eq,
           by simpa [← hs'_eq'] using hinitCount_eq,
           by simpa [← hs'_eq'] using hinitEdges_eq⟩

theorem task3MiddleLoop_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task3State tools.pathDS.State}
    (hloop : Task3LoopInv tools.pathDS J (buildWitness tools H' J embJH) s)
    (hrel : Task3RoundRel tools.pathDS J (buildWitness tools H' J embJH) s_prev s) :
    let wd := buildWitness tools H' J embJH
    let s_out := whileFuel J.m (task3MiddleCond tools.pathDS J wd)
      (task3MiddleStep tools.pathDS J wd) s
    Task3LoopInv tools.pathDS J wd s_out ∧
    Task3RoundRel tools.pathDS J wd s_prev s_out ∧
    task3MiddleCond tools.pathDS J wd s_out = false ∧
    s_out.η₂ = s.η₂ ∧
    s_out.initCountW = s.initCountW ∧
    s_out.initEdgesW = s.initEdgesW := by
  intro wd s_out
  let P : Task3State tools.pathDS.State → Prop := fun st =>
    Task3LoopInv tools.pathDS J wd st ∧
    Task3RoundRel tools.pathDS J wd s_prev st ∧
    st.η₂ = s.η₂ ∧
    st.initCountW = s.initCountW ∧
    st.initEdgesW = s.initEdgesW
  let meas : Task3State tools.pathDS.State → ℕ := fun st => unembeddedCount2 J st
  have hstep : ∀ st, P st → task3MiddleCond tools.pathDS J wd st = true →
      P (task3MiddleStep tools.pathDS J wd st) ∧
        meas (task3MiddleStep tools.pathDS J wd st) < meas st := by
    intro st ⟨hst_loop, hst_rel, heta, hic, hie⟩ hc
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      task3MiddleStep_inv tools H' J embJH hJ hw hst_loop hst_rel hc
    exact ⟨⟨h1, h2, h4.trans heta, h5.trans hic, h6.trans hie⟩, h3⟩
  have hmeas_le : meas s ≤ J.m := by
    simpa [meas, unembeddedCount2, unembeddedSet2, Finset.card_range] using
      Finset.card_le_card (Finset.filter_subset _ (Finset.range J.m))
  have hinv_out : P s_out :=
    whileFuel_inv P (task3MiddleCond tools.pathDS J wd)
      (task3MiddleStep tools.pathDS J wd) (fun st h c => (hstep st h c).1) J.m s
      ⟨hloop, hrel, rfl, rfl, rfl⟩
  have hdone : task3MiddleCond tools.pathDS J wd s_out = false :=
    whileFuel_done P meas (task3MiddleCond tools.pathDS J wd)
      (task3MiddleStep tools.pathDS J wd) hstep J.m s
      ⟨hloop, hrel, rfl, rfl, rfl⟩ hmeas_le
  exact ⟨hinv_out.1, hinv_out.2.1, hdone, hinv_out.2.2⟩

end MinCostFlow.Spanner
