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
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Task 2 Invariants and Inner Step

Defines Task 2 measures (`unembeddedSet1`, `unembeddedCount1`, `volWRem`, `eta1Bound`),
invariants (`Task2CoreInv`, `Task2LoopInv`, `Task2RoundRel`), and inner-step proofs
(`deleteEdgesAtVertex_foldl_spec`, `task2InnerStep_inv`).
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## General list, Bernoulli, and congestion helpers -/

theorem find?_some_spec {α : Type*} {l : List α} {p : α → Bool} {a : α}
    (h : l.find? p = some a) : a ∈ l ∧ p a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    cases hx : p x with
    | true =>
      rw [hx] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, hx⟩
    | false =>
      rw [hx] at h
      obtain ⟨hmem, hp⟩ := ih h
      exact ⟨List.mem_cons_of_mem x hmem, hp⟩

theorem find?_none_iff {α : Type*} {l : List α} {p : α → Bool} :
    l.find? p = none ↔ ∀ a ∈ l, p a = false := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.find?_cons]
    cases hx : p x with
    | true => simp [hx]
    | false =>
      simp only [hx, ih, List.mem_cons, forall_eq_or_imp, true_and]

theorem head?_some_mem {α : Type*} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

theorem list_zip_map_length {α β γ : Type*} (l₁ : List α) (l₂ : List β) (f : α × β → γ)
    (hlen : l₁.length = l₂.length) :
    ((l₁.zip l₂).map f).length = l₁.length := by
  rw [List.length_map, List.length_zip, hlen, min_self]

theorem list_zip_map_getElem {α β γ : Type*} (l₁ : List α) (l₂ : List β) (f : α × β → γ)
    (hlen : l₁.length = l₂.length) {i : ℕ} (hi : i < l₁.length) :
    ((l₁.zip l₂).map f)[i]'(by rw [list_zip_map_length l₁ l₂ f hlen]; exact hi) =
      f (l₁[i]'hi, l₂[i]'(by omega)) := by
  simp [List.getElem_map, List.getElem_zip]

theorem sum_range_getD_real' {α : Type*} (l : List α) (d : α) (f : α → ℝ) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ', add_comm, List.map_cons, List.sum_cons]
    have h0 : (a :: as).getD 0 d = a := rfl
    have hs : ∀ i, (a :: as).getD (i + 1) d = as.getD i d := fun _ => rfl
    simp_rw [hs]
    rw [h0, ih]

theorem sum_list_map_zip_nat {α β : Type*} (l₁ : List α) (l₂ : List β)
    (d₁ : α) (d₂ : β) (f : α → β → ℕ) (hlen : l₁.length = l₂.length) :
    ((l₁.zip l₂).map (fun p => f p.1 p.2)).sum =
      ∑ i ∈ Finset.range l₁.length, f (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      rw [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
          Finset.sum_range_succ', add_comm]
      have h0 : f ((a :: as).getD 0 d₁) ((b :: bs).getD 0 d₂) = f a b := rfl
      have hs : ∀ i, f ((a :: as).getD (i + 1) d₁) ((b :: bs).getD (i + 1) d₂) =
          f (as.getD i d₁) (bs.getD i d₂) := fun _ => rfl
      simp_rw [hs]
      rw [h0, ih bs hlen']

private theorem bernoulli_half_pow {c : ℝ} (hc : 0 < c) :
    (c / (c + 1)) ^ (Nat.ceil c) ≤ (1 / 2 : ℝ) := by
  set K := Nat.ceil c
  have hK_ge : c ≤ (K : ℝ) := Nat.le_ceil c
  have hx : (-2 : ℝ) ≤ 1 / c := by
    have : 0 < 1 / c := by positivity
    linarith
  have hbern : 1 + (K : ℝ) * (1 / c) ≤ (1 + 1 / c) ^ K := one_add_mul_le_pow hx K
  have h1c : (1 + 1 / c) = (c + 1) / c := by field_simp [hc.ne']
  have h2_le : (2 : ℝ) ≤ ((c + 1) / c) ^ K := by
    rw [← h1c]
    have hKc : (1 : ℝ) ≤ (K : ℝ) * (1 / c) := by
      rw [mul_one_div, one_le_div hc]
      exact hK_ge
    linarith
  have hpow : (c / (c + 1)) ^ K = (((c + 1) / c) ^ K)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hpow, one_div]
  exact inv_anti₀ (by positivity) h2_le

theorem bernoulli_round_lt {c V φ : ℝ} (hc : 0 < c) (hV : 0 ≤ V) (hφ : 0 < φ) :
    let K := Nat.ceil c
    let B := Nat.log 2 (Nat.ceil (V / φ) + 1) + 1
    (c / (c + 1)) ^ (K * B) * V < φ := by
  intro K B
  by_cases hV0 : V = 0
  · simp [hV0, hφ]
  · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    have hratio_nonneg : 0 ≤ c / (c + 1) := by positivity
    have hhalf : (c / (c + 1)) ^ K ≤ (1 / 2 : ℝ) := bernoulli_half_pow hc
    have hpow_le : (c / (c + 1)) ^ (K * B) ≤ (1 / 2 : ℝ) ^ B := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hratio_nonneg K) hhalf B
    have hlog : Nat.ceil (V / φ) + 1 < 2 ^ B :=
      Nat.lt_pow_succ_log_self (by norm_num) (Nat.ceil (V / φ) + 1)
    have hlog_r : V / φ < (2 ^ B : ℝ) := by
      have hceil : V / φ ≤ (Nat.ceil (V / φ) : ℝ) := Nat.le_ceil _
      have hnat : (Nat.ceil (V / φ) : ℝ) + 1 < (2 ^ B : ℝ) := by exact_mod_cast hlog
      linarith
    have hpow_pos : (0 : ℝ) < (2 ^ B : ℝ) := by positivity
    have hmul : V * ((1 / 2 : ℝ) ^ B) < φ := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, div_lt_iff₀ hpow_pos]
      have h1 : V < (2 ^ B : ℝ) * φ := (div_lt_iff₀ hφ).mp hlog_r
      linarith
    calc (c / (c + 1)) ^ (K * B) * V
        ≤ (1 / 2 : ℝ) ^ B * V := mul_le_mul_of_nonneg_right hpow_le hV
      _ = V * ((1 / 2 : ℝ) ^ B) := mul_comm _ _
      _ < φ := hmul

/-! ## Walk and congestion update lemmas -/

theorem walk_verts_length_le_edges_succ {H : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk H u v) : P.verts.length ≤ P.edges.length + 1 := by
  rcases hP.2.2 with ⟨hPv, _, _⟩ | ⟨_, hlen, _⟩
  · simp [hPv]
  · omega

theorem vcongAt_update_none (W _H' J : Graph) (wW : ℕ → ℝ) (embJH : ℕ → Walk)
    (emb? : ℕ → Option Walk) {eW₀ : ℕ} (heW₀ : eW₀ < W.m) (hnone : emb? eW₀ = none)
    (P : Walk) (x : ℕ) :
    vcongAt W wW (compose J embJH (partialToWalk (Function.update emb? eW₀ (some P)))) x =
      vcongAt W wW (compose J embJH (partialToWalk emb?)) x +
        if x ∈ (composeAux J embJH P.verts P.edges).verts then wW eW₀ else 0 := by
  unfold vcongAt
  rw [Finset.sum_filter, Finset.sum_filter]
  have hzero : (if x ∈ (compose J embJH (partialToWalk emb?) eW₀).verts then wW eW₀ else 0) = 0 := by
    have hp : partialToWalk emb? eW₀ = Walk.empty := by simp [partialToWalk, hnone]
    simp [compose, hp, composeAux, Walk.empty]
  have hne : ∀ j ∈ Finset.range W.m, j ≠ eW₀ →
      (if x ∈ (compose J embJH (partialToWalk (Function.update emb? eW₀ (some P))) j).verts
        then wW j else 0) =
      (if x ∈ (compose J embJH (partialToWalk emb?) j).verts then wW j else 0) := by
    intro j _ hjne
    have hupd : partialToWalk (Function.update emb? eW₀ (some P)) j = partialToWalk emb? j := by
      simp [partialToWalk, Function.update_of_ne hjne]
    rw [compose, compose, hupd]
  have heW_mem : eW₀ ∈ Finset.range W.m := Finset.mem_range.mpr heW₀
  rw [← Finset.add_sum_erase (Finset.range W.m) _ heW_mem,
      ← Finset.add_sum_erase (Finset.range W.m) _ heW_mem]
  have hsum_eq : ∑ j ∈ (Finset.range W.m).erase eW₀,
        (if x ∈ (compose J embJH (partialToWalk (Function.update emb? eW₀ (some P))) j).verts
          then wW j else 0) =
      ∑ j ∈ (Finset.range W.m).erase eW₀,
        (if x ∈ (compose J embJH (partialToWalk emb?) j).verts then wW j else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hne j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  rw [hsum_eq, hzero, zero_add, add_comm]
  congr 1
  simp [compose, partialToWalk, Function.update_self]

theorem vcongAt_mono_diff (W J : Graph) (wW : ℕ → ℝ) (embJH : ℕ → Walk)
    (emb₀ emb₁ : ℕ → Option Walk)
    (hmono : ∀ eW < W.m, emb₀ eW = none ∨ emb₁ eW = emb₀ eW) (x : ℕ) :
    vcongAt W wW (compose J embJH (partialToWalk emb₁)) x -
      vcongAt W wW (compose J embJH (partialToWalk emb₀)) x =
      ∑ eW ∈ (Finset.range W.m).filter (fun eW =>
        (emb₀ eW).isNone = true ∧ (emb₁ eW).isSome = true ∧
          x ∈ (compose J embJH (partialToWalk emb₁) eW).verts), wW eW := by
  unfold vcongAt
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun eW heW => ?_
  have heWm : eW < W.m := Finset.mem_range.mp heW
  rcases hmono eW heWm with h0 | h01
  · have hc0 : compose J embJH (partialToWalk emb₀) eW = Walk.empty := by
      simp [compose, partialToWalk, h0, composeAux, Walk.empty]
    have hnotin : x ∉ (compose J embJH (partialToWalk emb₀) eW).verts := by
      simp [hc0, Walk.empty]
    simp only [hnotin, ↓reduceIte, sub_zero]
    cases h1 : emb₁ eW with
    | none =>
      have hc1 : compose J embJH (partialToWalk emb₁) eW = Walk.empty := by
        simp [compose, partialToWalk, h1, composeAux, Walk.empty]
      have hnotin1 : x ∉ (compose J embJH (partialToWalk emb₁) eW).verts := by
        simp [hc1, Walk.empty]
      simp [hnotin1]
    | some P₁ =>
      by_cases hx : x ∈ (compose J embJH (partialToWalk emb₁) eW).verts <;> simp [h0, hx]
  · have hcomp : compose J embJH (partialToWalk emb₁) eW =
        compose J embJH (partialToWalk emb₀) eW := by
      simp [compose, partialToWalk, h01]
    rw [hcomp, sub_self]
    cases h0 : emb₀ eW with
    | none =>
      rw [h0] at h01
      simp [h01]
    | some P₀ => simp

theorem vcongAt_update_none_le (W H' J : Graph) (wW : ℕ → ℝ) (embJH : ℕ → Walk)
    (emb? : ℕ → Option Walk) {eW₀ : ℕ} (heW₀ : eW₀ < W.m) (hnone : emb? eW₀ = none)
    (hwW : 0 ≤ wW eW₀) (P : Walk) (x : ℕ) :
    vcongAt W wW (compose J embJH (partialToWalk (Function.update emb? eW₀ (some P)))) x ≤
      vcongAt W wW (compose J embJH (partialToWalk emb?)) x + wW eW₀ := by
  rw [vcongAt_update_none W H' J wW embJH emb? heW₀ hnone P x]
  split_ifs
  · exact le_rfl
  · linarith

/-! ## Task 2 measures, invariants, and round bound -/

/-- Set of unembedded `W`-edge indices (`< wd.W.m`) in Task 2 state `s`. -/
def unembeddedSet1 {DSState : Type} (wd : WitnessData) (s : Task2State DSState) : Finset ℕ :=
  (Finset.range wd.W.m).filter fun eW => (s.embWJ eW).isNone

/-- Number of unembedded `W`-edges in Task 2 state `s`. -/
def unembeddedCount1 {DSState : Type} (wd : WitnessData) (s : Task2State DSState) : ℕ :=
  (unembeddedSet1 wd s).card

/-- Remaining `w_W`-volume of unembedded edges in Task 2 state `s` (`Claim 8.7`, p. 43). -/
noncomputable def volWRem {DSState : Type} (wd : WitnessData) (s : Task2State DSState) : ℝ :=
  ∑ eW ∈ unembeddedSet1 wd s, wd.wW eW

/-- Explicit `O(log(m / φ_dec))` upper bound on the number of rounds `η₁` in Task 2 (`Claim 8.7`). -/
noncomputable def eta1Bound (wd : WitnessData) (J : Graph) : ℕ :=
  1 + Nat.ceil (2 * wd.c_deg) *
    (Nat.log 2 (Nat.ceil (wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec)) + 1) + 1)

theorem volWRem_nonneg {DSState : Type} {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    (s : Task2State DSState) :
    0 ≤ volWRem (buildWitness tools H' J embJH) s := by
  refine Finset.sum_nonneg fun eW heW => ?_
  have heWm := Finset.mem_range.mp (Finset.mem_filter.mp heW).1
  exact (wW_pos tools H' J embJH hw heWm).le

theorem task2OuterCond_false_iff {DSState : Type} (wd : WitnessData)
    (s : Task2State DSState) :
    task2OuterCond wd s = false ↔ ∀ eW < wd.W.m, (s.embWJ eW).isSome = true := by
  unfold task2OuterCond
  rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
  push Not
  simp only [List.mem_range, Bool.not_eq_true, Option.isNone_eq_false_iff]

theorem task2OuterCond_false_iff_unemb {DSState : Type} (wd : WitnessData)
    (s : Task2State DSState) :
    task2OuterCond wd s = false ↔ unembeddedSet1 wd s = ∅ := by
  rw [task2OuterCond_false_iff]
  simp only [unembeddedSet1, Finset.filter_eq_empty_iff, Finset.mem_range,
    Option.isNone_iff_eq_none, Option.isSome_iff_ne_none, ne_eq]

theorem unembeddedCount1_update_none {DSState : Type} (wd : WitnessData)
    (s : Task2State DSState) {eW : ℕ} (heW : eW < wd.W.m) (hnone : s.embWJ eW = none)
    (P : Walk) :
    unembeddedSet1 wd { s with embWJ := Function.update s.embWJ eW (some P) } =
      (unembeddedSet1 wd s).erase eW ∧
    unembeddedCount1 wd { s with embWJ := Function.update s.embWJ eW (some P) } + 1 =
      unembeddedCount1 wd s := by
  have hmem : eW ∈ unembeddedSet1 wd s := by
    simp [unembeddedSet1, heW, hnone]
  have hset : unembeddedSet1 wd { s with embWJ := Function.update s.embWJ eW (some P) } =
      (unembeddedSet1 wd s).erase eW := by
    ext j
    simp only [unembeddedSet1, Finset.mem_filter, Finset.mem_range, Finset.mem_erase,
      Option.isNone_iff_eq_none]
    by_cases hj : j = eW
    · subst hj; simp [Function.update_self]
    · simp [hj]
  refine ⟨hset, ?_⟩
  unfold unembeddedCount1
  rw [hset]
  exact Finset.card_erase_add_one hmem

/-- Core Task 2 invariant maintained inside `task2InnerLoop`, `task2MiddleLoop`, and `task2Round`. -/
structure Task2CoreInv (pathDS : PathDSTool) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State pathDS.State) : Prop where
  ds_len : s.dsJ.length = wd.comps.length
  ds_inv : ∀ ci (hci : ci < wd.comps.length),
    pathDS.Inv wd.φ_dec wd.J0_strip.m (wd.comps[ci]'hci).J_sub
      (s.dsJ[ci]'(by rw [ds_len]; exact hci))
  Vhat_sub : ∀ ci (hci : ci < wd.comps.length),
    pathDS.Vhat (s.dsJ[ci]'(by rw [ds_len]; exact hci)) ⊆ (wd.comps[ci]'hci).J_sub.verts
  Vhat_vol : ∀ ci (hci : ci < wd.comps.length),
    ((wd.comps[ci]'hci).J_sub.vol (pathDS.Vhat (s.dsJ[ci]'(by rw [ds_len]; exact hci))) : ℝ) ≤
      wd.γ_del * ((pathDS.deleted (s.dsJ[ci]'(by rw [ds_len]; exact hci))).card : ℝ) / wd.φ_ds
  partial_emb : IsPartialEmbedding wd.W J s.embWJ
  j0_embedded : ∀ eW < wd.j0Edges.length, (s.embWJ eW).isSome = true
  emb_len : ∀ eW < wd.W.m, ((partialToWalk s.embWJ eW).edges.length : ℝ) ≤ wd.γ_ExpPath
  vcong_half : ∀ x < H'.n,
    vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x ≤ (s.η₁ + 1 / 2 : ℝ) * wd.τ₁
  processed_sub : ∀ x ∈ s.processedVerts,
    x < H'.n ∧ (s.η₁ : ℝ) * wd.τ₁ ≤ vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x
  processed_deleted : ∀ x ∈ s.processedVerts, ∀ ci (hci : ci < wd.comps.length) b,
    b < (wd.comps[ci]'hci).J_sub.m →
    x ∈ (embJH ((wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts →
    b ∈ pathDS.deleted (s.dsJ[ci]'(by rw [ds_len]; exact hci))
  deleted_sub_processed : ∀ ci (hci : ci < wd.comps.length) b,
    b ∈ pathDS.deleted (s.dsJ[ci]'(by rw [ds_len]; exact hci)) →
    b < (wd.comps[ci]'hci).J_sub.m ∧
    ∃ x ∈ s.processedVerts, x ∈ (embJH ((wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts
  initCount_eq : s.initCountJ = s.η₁ * wd.comps.length
  initEdges_eq : s.initEdgesJ = s.η₁ * (wd.comps.map fun c => c.J_sub.m).sum
  middle_eq : s.middleIters1 = s.getPathCountJ
  unemb_eq : s.getPathCountJ + unembeddedCount1 wd s = wd.W.m - wd.j0Edges.length
  vcongUpdates_le : (s.vcongUpdates : ℝ) ≤
    (s.getPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))

/-- Strong invariant holding between `task2MiddleStep` calls and at the end of `task2Round`. -/
structure Task2LoopInv (pathDS : PathDSTool) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State pathDS.State) : Prop extends
    Task2CoreInv pathDS H' J embJH wd s where
  inactive_uncongested : ∀ x < H'.n, x ∉ s.processedVerts →
    vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x ≤ (s.η₁ : ℝ) * wd.τ₁

/-- Round-relative delta invariant connecting `s_prev` (start of round) to intermediate `s`. -/
structure Task2RoundRel (pathDS : PathDSTool) (wd : WitnessData)
    (s_prev s : Task2State pathDS.State) : Prop where
  emb_mono : ∀ eW < wd.W.m, s_prev.embWJ eW = none ∨ s.embWJ eW = s_prev.embWJ eW
  inner_eq : s.innerIters1 = s_prev.innerIters1 + s.processedVerts.card
  del_eq : s.deleteCountJ = s_prev.deleteCountJ +
    ∑ ci ∈ Finset.range wd.comps.length,
      (pathDS.deleted (s.dsJ.getD ci (pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩))).card

/-! ## Inner loop (`deleteEdgesAtVertex` and `task2InnerLoop`) -/

theorem deleteEdgesAtVertex_foldl_spec (pathDS : PathDSTool) (wd : WitnessData)
    (c : CompInfo) (hc_n : c.J_sub.n = c.X.card) (hc_valid : c.J_sub.IsValid)
    (hc_m_pos : 1 ≤ c.J_sub.m) (hc_m_le : c.J_sub.m ≤ wd.J0_strip.m)
    (hc_deg : ∀ v < c.X.card, 1 ≤ c.J_sub.deg v)
    (hc_exp : c.J_sub.IsConductanceExpanderOn c.J_sub.verts wd.φ_dec)
    (hφ_pos : 0 < wd.φ_dec) (hφ_le : wd.φ_dec ≤ 1)
    (hγ_del : pathDS.γ_del wd.φ_dec wd.J0_strip.m ≤ wd.γ_del)
    (hφ_out : wd.φ_ds ≤ pathDS.φ_out wd.φ_dec wd.J0_strip.m)
    (hφ_ds_pos : 0 < wd.φ_ds)
    (hγ_del_pos : 0 ≤ pathDS.γ_del wd.φ_dec wd.J0_strip.m) :
    ∀ (l : List ℕ) (ds0 : pathDS.State) (k0 : ℕ),
      l.Nodup →
      (∀ b ∈ l, b < c.J_sub.m ∧ b ∉ pathDS.deleted ds0) →
      pathDS.Inv wd.φ_dec wd.J0_strip.m c.J_sub ds0 →
      pathDS.Vhat ds0 ⊆ c.J_sub.verts →
      (c.J_sub.vol (pathDS.Vhat ds0) : ℝ) ≤
        wd.γ_del * ((pathDS.deleted ds0).card : ℝ) / wd.φ_ds →
      let res := l.foldl (fun (acc : pathDS.State × ℕ) b =>
        let r := pathDS.delete acc.1 b
        (r.1, acc.2 + 1)) (ds0, k0)
      pathDS.Inv wd.φ_dec wd.J0_strip.m c.J_sub res.1 ∧
      pathDS.deleted res.1 = l.toFinset ∪ pathDS.deleted ds0 ∧
      pathDS.Vhat ds0 ⊆ pathDS.Vhat res.1 ∧
      pathDS.Vhat res.1 ⊆ c.J_sub.verts ∧
      (c.J_sub.vol (pathDS.Vhat res.1) : ℝ) ≤
        wd.γ_del * ((pathDS.deleted res.1).card : ℝ) / wd.φ_ds ∧
      res.2 = k0 + l.length ∧
      (pathDS.deleted res.1).card = (pathDS.deleted ds0).card + l.length := by
  intro l
  induction l with
  | nil =>
    intro ds0 k0 _ _ hinv hsub hvol
    refine ⟨hinv, ?_, Finset.Subset.rfl, hsub, hvol, rfl, rfl⟩
    simp
  | cons b bs ih =>
    intro ds0 k0 hnodup hmem hinv hsub hvol
    rw [List.nodup_cons] at hnodup
    have hb_lt := (hmem b List.mem_cons_self).1
    have hb_not := (hmem b List.mem_cons_self).2
    have hdel := pathDS.delete_spec wd.φ_dec wd.J0_strip.m c.J_sub ds0 b
      hφ_pos hφ_le hc_valid hc_m_pos hc_m_le (by simpa [hc_n] using hc_deg) hc_exp
      hinv hb_lt hb_not
    rcases hdel with ⟨hinv1, hdel1, hVsub1, hVtop1, _, hVvol1⟩
    set ds1 := (pathDS.delete ds0 b).1
    have hvol1_wd : (c.J_sub.vol (pathDS.Vhat ds1) : ℝ) ≤
        wd.γ_del * ((pathDS.deleted ds1).card : ℝ) / wd.φ_ds := by
      have hnum : pathDS.γ_del wd.φ_dec wd.J0_strip.m * ((pathDS.deleted ds1).card : ℝ) ≤
          wd.γ_del * ((pathDS.deleted ds1).card : ℝ) :=
        mul_le_mul_of_nonneg_right hγ_del (Nat.cast_nonneg _)
      have hnum_nonneg : 0 ≤ wd.γ_del * ((pathDS.deleted ds1).card : ℝ) :=
        mul_nonneg (le_trans hγ_del_pos hγ_del) (Nat.cast_nonneg _)
      exact le_trans hVvol1 (div_le_div₀ hnum_nonneg hnum hφ_ds_pos hφ_out)
    have hbs_mem : ∀ b' ∈ bs, b' < c.J_sub.m ∧ b' ∉ pathDS.deleted ds1 := by
      intro b' hb'
      have hb'0 := hmem b' (List.mem_cons_of_mem b hb')
      refine ⟨hb'0.1, ?_⟩
      rw [hdel1, Finset.mem_insert]
      rintro (rfl | hmem0)
      · exact hnodup.1 hb'
      · exact hb'0.2 hmem0
    have ih' := ih ds1 (k0 + 1) hnodup.2 hbs_mem hinv1 hVtop1 hvol1_wd
    rcases ih' with ⟨hinv2, hdel2, hVsub2, hVtop2, hvol2, hcnt2, hcard2⟩
    refine ⟨hinv2, ?_, Finset.Subset.trans hVsub1 hVsub2, hVtop2, hvol2, ?_, ?_⟩
    · rw [List.foldl_cons]
      dsimp only [ds1] at hdel2 ⊢
      rw [hdel2, hdel1]
      ext x
      simp [List.mem_toFinset]
    · rw [List.foldl_cons]
      dsimp only [ds1] at hcnt2 ⊢
      rw [hcnt2, List.length_cons]
      omega
    · rw [List.foldl_cons]
      dsimp only [ds1] at hcard2 ⊢
      rw [hcard2, hdel1, Finset.card_insert_of_notMem hb_not]
      simp [List.length_cons, Nat.add_assoc]
      omega

private theorem deleteEdgesAtVertex_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length)
    (x : ℕ) (ds0 : tools.pathDS.State)
    (hinv : tools.pathDS.Inv (buildWitness tools H' J embJH).φ_dec
      (buildWitness tools H' J embJH).J0_strip.m
      ((buildWitness tools H' J embJH).comps[ci]'hci).J_sub ds0)
    (hVsub : tools.pathDS.Vhat ds0 ⊆ ((buildWitness tools H' J embJH).comps[ci]'hci).J_sub.verts)
    (hVvol : (((buildWitness tools H' J embJH).comps[ci]'hci).J_sub.vol (tools.pathDS.Vhat ds0) : ℝ) ≤
      (buildWitness tools H' J embJH).γ_del * ((tools.pathDS.deleted ds0).card : ℝ) /
        (buildWitness tools H' J embJH).φ_ds) :
    let wd := buildWitness tools H' J embJH
    let c := wd.comps[ci]'hci
    let res := deleteEdgesAtVertex tools.pathDS embJH x c ds0
    tools.pathDS.Inv wd.φ_dec wd.J0_strip.m c.J_sub res.1 ∧
    tools.pathDS.deleted ds0 ⊆ tools.pathDS.deleted res.1 ∧
    (∀ b < c.J_sub.m, x ∈ (embJH (c.jSubOrigEdges.getD b 0)).verts → b ∈ tools.pathDS.deleted res.1) ∧
    (∀ b ∈ tools.pathDS.deleted res.1, b ∈ tools.pathDS.deleted ds0 ∨
      (b < c.J_sub.m ∧ x ∈ (embJH (c.jSubOrigEdges.getD b 0)).verts)) ∧
    tools.pathDS.Vhat ds0 ⊆ tools.pathDS.Vhat res.1 ∧
    tools.pathDS.Vhat res.1 ⊆ c.J_sub.verts ∧
    (c.J_sub.vol (tools.pathDS.Vhat res.1) : ℝ) ≤
      wd.γ_del * ((tools.pathDS.deleted res.1).card : ℝ) / wd.φ_ds ∧
    (tools.pathDS.deleted res.1).card = (tools.pathDS.deleted ds0).card + res.2 := by
  intro wd c res
  rcases hw.comp_props ci hci with
    ⟨_, _, _, _, _, hc_n, hc_valid, hc_m_pos, hc_m_le, hc_deg, hc_exp, _⟩
  let toDel :=
    letI := Classical.propDecidable
    (List.range c.J_sub.m).filter fun b =>
      decide (b ∉ tools.pathDS.deleted ds0 ∧ x ∈ (embJH (c.jSubOrigEdges.getD b 0)).verts)
  have hnodup : toDel.Nodup := List.Nodup.filter _ List.nodup_range
  have hmem : ∀ b ∈ toDel, b < c.J_sub.m ∧ b ∉ tools.pathDS.deleted ds0 := by
    intro b hb
    dsimp only [toDel] at hb
    rw [List.mem_filter, List.mem_range] at hb
    rw [@decide_eq_true_eq _ (Classical.propDecidable _)] at hb
    exact ⟨hb.1, hb.2.1⟩
  have hγ_del_le : tools.pathDS.γ_del wd.φ_dec wd.J0_strip.m ≤ wd.γ_del := le_max_left _ _
  have hφ_out_ge : wd.φ_ds ≤ tools.pathDS.φ_out wd.φ_dec wd.J0_strip.m := min_le_left _ _
  have hγ_del_nonneg : 0 ≤ tools.pathDS.γ_del wd.φ_dec wd.J0_strip.m :=
    le_trans (by norm_num) (tools.pathDS.hγ_del_ge wd.φ_dec wd.J0_strip.m hw.φ_dec_pos)
  have hfold := deleteEdgesAtVertex_foldl_spec tools.pathDS wd c hc_n hc_valid hc_m_pos hc_m_le
    hc_deg hc_exp hw.φ_dec_pos hw.φ_dec_le hγ_del_le hφ_out_ge hw.φ_ds_pos hγ_del_nonneg
    toDel ds0 0 hnodup hmem hinv hVsub hVvol
  rcases hfold with ⟨hinv1, hdel1, hVsub1, hVtop1, hvol1, hcnt1, hcard1⟩
  have hres_eq : res = toDel.foldl (fun (acc : tools.pathDS.State × ℕ) b =>
      let r := tools.pathDS.delete acc.1 b; (r.1, acc.2 + 1)) (ds0, 0) := rfl
  rw [← hres_eq] at hinv1 hdel1 hVsub1 hVtop1 hvol1 hcnt1 hcard1
  refine ⟨hinv1, ?_, ?_, ?_, hVsub1, hVtop1, hvol1, ?_⟩
  · rw [hdel1]; exact Finset.subset_union_right
  · intro b hb hbx
    rw [hdel1, Finset.mem_union, List.mem_toFinset]
    by_cases hbd : b ∈ tools.pathDS.deleted ds0
    · exact Or.inr hbd
    · left
      dsimp only [toDel]
      rw [List.mem_filter, List.mem_range, @decide_eq_true_eq _ (Classical.propDecidable _)]
      exact ⟨hb, hbd, hbx⟩
  · intro b hb
    rw [hdel1, Finset.mem_union, List.mem_toFinset] at hb
    rcases hb with hto | h0
    · right
      dsimp only [toDel] at hto
      rw [List.mem_filter, List.mem_range, @decide_eq_true_eq _ (Classical.propDecidable _)] at hto
      exact ⟨hto.1, hto.2.2⟩
    · exact Or.inl h0
  · rw [hcard1, hcnt1, Nat.zero_add]

theorem task2InnerStep_inv {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task2State tools.pathDS.State}
    (hinv : Task2CoreInv tools.pathDS H' J embJH (buildWitness tools H' J embJH) s)
    (hrel : Task2RoundRel tools.pathDS (buildWitness tools H' J embJH) s_prev s)
    (hcond : task2InnerCond H' J embJH (buildWitness tools H' J embJH) s = true) :
    let wd := buildWitness tools H' J embJH
    let s' := task2InnerStep tools.pathDS H' J embJH wd s
    Task2CoreInv tools.pathDS H' J embJH wd s' ∧
    Task2RoundRel tools.pathDS wd s_prev s' ∧
    H'.n - (s'.processedVerts ∩ Finset.range H'.n).card <
      H'.n - (s.processedVerts ∩ Finset.range H'.n).card := by
  intro wd s'
  unfold task2InnerCond at hcond
  cases hfind : findCongestedVertex H' J embJH wd s with
  | none => rw [hfind] at hcond; simp at hcond
  | some x =>
    have hx_spec := find?_some_spec hfind
    have hx_range : x < H'.n := List.mem_range.mp hx_spec.1
    have hx_cond : x ∉ s.processedVerts ∧
        (s.η₁ : ℝ) * wd.τ₁ ≤ vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x := by
      simpa [decide_eq_true_eq] using hx_spec.2
    have hs'_eq : s' =
        let updated := (wd.comps.zip s.dsJ).map fun (c, ds) =>
          deleteEdgesAtVertex tools.pathDS embJH x c ds
        { s with
          dsJ := updated.map Prod.fst
          processedVerts := insert x s.processedVerts
          deleteCountJ := s.deleteCountJ + (updated.map Prod.snd).sum
          innerIters1 := s.innerIters1 + 1 } := by
      simp [s', task2InnerStep, hfind]
    set updated := (wd.comps.zip s.dsJ).map fun (c, ds) =>
      deleteEdgesAtVertex tools.pathDS embJH x c ds
    have hds_len' : s'.dsJ.length = wd.comps.length := by
      rw [hs'_eq]; dsimp only
      rw [List.length_map, list_zip_map_length _ _ _ hinv.ds_len.symm]
    have hspec : ∀ ci (hci : ci < wd.comps.length),
        let c := wd.comps[ci]'hci
        let ds0 := s.dsJ[ci]'(by rw [hinv.ds_len]; exact hci)
        let res := deleteEdgesAtVertex tools.pathDS embJH x c ds0
        s'.dsJ[ci]'(by rw [hds_len']; exact hci) = res.1 ∧
        tools.pathDS.Inv wd.φ_dec wd.J0_strip.m c.J_sub res.1 ∧
        tools.pathDS.deleted ds0 ⊆ tools.pathDS.deleted res.1 ∧
        (∀ b < c.J_sub.m, x ∈ (embJH (c.jSubOrigEdges.getD b 0)).verts →
          b ∈ tools.pathDS.deleted res.1) ∧
        (∀ b ∈ tools.pathDS.deleted res.1, b ∈ tools.pathDS.deleted ds0 ∨
          (b < c.J_sub.m ∧ x ∈ (embJH (c.jSubOrigEdges.getD b 0)).verts)) ∧
        tools.pathDS.Vhat ds0 ⊆ tools.pathDS.Vhat res.1 ∧
        tools.pathDS.Vhat res.1 ⊆ c.J_sub.verts ∧
        (c.J_sub.vol (tools.pathDS.Vhat res.1) : ℝ) ≤
          wd.γ_del * ((tools.pathDS.deleted res.1).card : ℝ) / wd.φ_ds ∧
        (tools.pathDS.deleted res.1).card = (tools.pathDS.deleted ds0).card + res.2 := by
      intro ci hci
      have hds_eq : s'.dsJ[ci]'(by rw [hds_len']; exact hci) =
          (deleteEdgesAtVertex tools.pathDS embJH x (wd.comps[ci]'hci)
            (s.dsJ[ci]'(by rw [hinv.ds_len]; exact hci))).1 := by
        simp only [hs'_eq, List.getElem_map]
        rw [list_zip_map_getElem wd.comps s.dsJ _ hinv.ds_len.symm hci]
      exact ⟨hds_eq, deleteEdgesAtVertex_spec tools H' J embJH hw hci x
        (s.dsJ[ci]'(by rw [hinv.ds_len]; exact hci))
        (hinv.ds_inv ci hci) (hinv.Vhat_sub ci hci) (hinv.Vhat_vol ci hci)⟩
    have hcore' : Task2CoreInv tools.pathDS H' J embJH wd s' :=
      { ds_len := hds_len'
        ds_inv := fun ci hci => (hspec ci hci).1 ▸ (hspec ci hci).2.1
        Vhat_sub := fun ci hci => (hspec ci hci).1 ▸ (hspec ci hci).2.2.2.2.2.2.1
        Vhat_vol := fun ci hci => (hspec ci hci).1 ▸ (hspec ci hci).2.2.2.2.2.2.2.1
        partial_emb := by rw [hs'_eq]; exact hinv.partial_emb
        j0_embedded := by rw [hs'_eq]; exact hinv.j0_embedded
        emb_len := by rw [hs'_eq]; exact hinv.emb_len
        vcong_half := by rw [hs'_eq]; exact hinv.vcong_half
        processed_sub := by
          intro y hy
          rw [hs'_eq] at hy
          dsimp only at hy
          rw [Finset.mem_insert] at hy
          rw [hs'_eq]
          rcases hy with rfl | hy
          · exact ⟨hx_range, hx_cond.2⟩
          · exact hinv.processed_sub y hy
        processed_deleted := by
          intro y hy ci hci b hb hyb
          rw [hs'_eq] at hy
          dsimp only at hy
          rw [Finset.mem_insert] at hy
          rw [(hspec ci hci).1]
          rcases hy with rfl | hy
          · exact (hspec ci hci).2.2.2.1 b hb hyb
          · exact (hspec ci hci).2.2.1 (hinv.processed_deleted y hy ci hci b hb hyb)
        deleted_sub_processed := by
          intro ci hci b hb
          rw [(hspec ci hci).1] at hb
          rcases (hspec ci hci).2.2.2.2.1 b hb with hb0 | ⟨hb_m, hxb⟩
          · obtain ⟨hb_m, y, hy, hyb⟩ := hinv.deleted_sub_processed ci hci b hb0
            refine ⟨hb_m, y, ?_, hyb⟩
            rw [hs'_eq]; exact Finset.mem_insert_of_mem hy
          · refine ⟨hb_m, x, ?_, hxb⟩
            rw [hs'_eq]; exact Finset.mem_insert_self x _
        initCount_eq := by rw [hs'_eq]; exact hinv.initCount_eq
        initEdges_eq := by rw [hs'_eq]; exact hinv.initEdges_eq
        middle_eq := by rw [hs'_eq]; exact hinv.middle_eq
        unemb_eq := by
          have hs_un : unembeddedCount1 wd s' = unembeddedCount1 wd s := by
            simp [unembeddedCount1, unembeddedSet1, hs'_eq]
          rw [hs_un, hs'_eq]; exact hinv.unemb_eq
        vcongUpdates_le := by rw [hs'_eq]; exact hinv.vcongUpdates_le }
    have hrel' : Task2RoundRel tools.pathDS wd s_prev s' := by
      refine
        { emb_mono := by rw [hs'_eq]; exact hrel.emb_mono
          inner_eq := by
            rw [hs'_eq]
            dsimp only
            rw [Finset.card_insert_of_notMem hx_cond.1, hrel.inner_eq]
            omega
          del_eq := ?_ }
      let dsDef := tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
      have hsum_snd : (updated.map Prod.snd).sum =
          ∑ ci ∈ Finset.range wd.comps.length,
            (deleteEdgesAtVertex tools.pathDS embJH x (wd.comps.getD ci defaultCompInfo)
              (s.dsJ.getD ci dsDef)).2 := by
        simp only [updated, List.map_map]
        have hcomp_eq : (List.map (Prod.snd ∘ fun p : CompInfo × tools.pathDS.State =>
            deleteEdgesAtVertex tools.pathDS embJH x p.1 p.2) (wd.comps.zip s.dsJ)) =
            (wd.comps.zip s.dsJ).map fun p => (deleteEdgesAtVertex tools.pathDS embJH x p.1 p.2).2 := by
          rfl
        rw [hcomp_eq, sum_list_map_zip_nat wd.comps s.dsJ defaultCompInfo dsDef
          (fun c ds => (deleteEdgesAtVertex tools.pathDS embJH x c ds).2) hinv.ds_len.symm]
      have hsum_add :
          (∑ ci ∈ Finset.range wd.comps.length,
              (tools.pathDS.deleted (s.dsJ.getD ci dsDef)).card) +
            ∑ ci ∈ Finset.range wd.comps.length,
              (deleteEdgesAtVertex tools.pathDS embJH x (wd.comps.getD ci defaultCompInfo)
                (s.dsJ.getD ci dsDef)).2 =
          ∑ ci ∈ Finset.range wd.comps.length,
            (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ci hci_r => ?_
        have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
        have hci_s : ci < s.dsJ.length := by rw [hinv.ds_len]; exact hci
        have hci_s' : ci < s'.dsJ.length := by rw [hds_len']; exact hci
        rw [List.getD_eq_getElem _ _ hci_s, List.getD_eq_getElem _ _ hci_s',
            List.getD_eq_getElem _ _ hci, (hspec ci hci).1]
        exact (hspec ci hci).2.2.2.2.2.2.2.2.symm
      have hdel_eq : s'.deleteCountJ = s.deleteCountJ + (updated.map Prod.snd).sum := by
        rw [hs'_eq]
      rw [hdel_eq, hrel.del_eq, Nat.add_assoc, hsum_snd, hsum_add]
    have hmeas : H'.n - (s'.processedVerts ∩ Finset.range H'.n).card <
        H'.n - (s.processedVerts ∩ Finset.range H'.n).card := by
      have hx_mem : x ∈ Finset.range H'.n := Finset.mem_range.mpr hx_range
      have hcard_eq : (s'.processedVerts ∩ Finset.range H'.n).card =
          (s.processedVerts ∩ Finset.range H'.n).card + 1 := by
        rw [hs'_eq]; dsimp only
        rw [Finset.insert_inter_of_mem hx_mem]
        exact Finset.card_insert_of_notMem (fun h => hx_cond.1 (Finset.mem_inter.mp h).1)
      have hcard_le : (s'.processedVerts ∩ Finset.range H'.n).card ≤ H'.n := by
        calc (s'.processedVerts ∩ Finset.range H'.n).card
            ≤ (Finset.range H'.n).card := Finset.card_le_card Finset.inter_subset_right
          _ = H'.n := Finset.card_range H'.n
      omega
    exact ⟨hcore', hrel', hmeas⟩


end MinCostFlow.Spanner
