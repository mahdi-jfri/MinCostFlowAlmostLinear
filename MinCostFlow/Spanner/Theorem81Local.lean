module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.WitnessLift
public import MinCostFlow.Spanner.Task2Base
public import MinCostFlow.Spanner.Analysis1
public import MinCostFlow.Spanner.Claim87
public import MinCostFlow.Spanner.Task3Base
public import MinCostFlow.Spanner.Analysis2
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Runtime
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Theorem 8.1: the Local Form

This file holds the first part of the material of `Theorem81.lean`, split off to keep files
small. `Theorem81.lean` gives the overview.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Helper lemmas for mapped embeddings and triple composition -/

private theorem isWalk_mapEdges_of_mem {H H' : Graph} {f : ℕ → ℕ} {u v : ℕ} {P : Walk}
    (hHn : H.n ≤ H'.n)
    (hf : ∀ j ∈ P.edges, j < H.m → f j < H'.m ∧ H'.edges.getD (f j) (0, 0) = H.edges.getD j (0, 0))
    (hP : P.IsWalk H u v) : (P.mapEdges f).IsWalk H' u v := by
  rcases hP with ⟨hu, hv, ⟨hPv, hPe, huv⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · exact ⟨Nat.lt_of_lt_of_le hu hHn, Nat.lt_of_lt_of_le hv hHn,
      Or.inl ⟨hPv, by simp [Walk.mapEdges, hPe], huv⟩⟩
  · refine ⟨Nat.lt_of_lt_of_le hu hHn, Nat.lt_of_lt_of_le hv hHn, Or.inr ⟨?_, ?_, hhead, hlast, ?_, ?_⟩⟩
    · simpa [Walk.mapEdges] using hne
    · simpa [Walk.mapEdges] using hlen
    · intro k hk
      simp only [Walk.mapEdges, List.mem_map] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      exact (hf j hj (hedges j hj)).1
    · intro i hi
      simp only [Walk.mapEdges, List.length_map] at hi ⊢
      have hj_mem : P.edges.getD i 0 ∈ P.edges := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      have hji : P.edges.getD i 0 < H.m := hedges _ hj_mem
      have hmap_i : (P.edges.map f).getD i 0 = f (P.edges.getD i 0) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi),
            List.getD_eq_getElem _ _ hi, List.getElem_map]
      rw [hmap_i, (hf _ hj_mem hji).2]
      exact hstep i hi

private theorem composeAux_mem_verts_of_mem {B C : Graph} {embBC : ℕ → Walk}
    (hBC : IsEmbedding B C embBC) :
    ∀ (js vs : List ℕ) (u v k x : ℕ),
      vs.length = js.length + 1 →
      vs.head? = some u →
      vs.getLast? = some v →
      (∀ j ∈ js, j < B.m) →
      (∀ i : ℕ, i < js.length →
        Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0)) (vs.getD i 0) (vs.getD (i + 1) 0)) →
      v < B.n →
      k ∈ js →
      x ∈ (embBC k).verts →
      x ∈ (composeAux B embBC vs js).verts := by
  intro js
  induction js with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ hk; simp at hk
  | cons j js ih =>
    intro vs u v k x hlen hhead hlast hedges hstep hv hk hx
    cases vs with
    | nil => simp at hlen
    | cons a vs' =>
      cases vs' with
      | nil => simp at hlen
      | cons b vs'' =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst a
        have hjB : j < B.m := hedges j List.mem_cons_self
        have hstep0 := hstep 0 (by simp)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] at hstep0
        rw [← List.getD_eq_getElem?_getD] at hstep0
        have hBe : B.edges.getD j (0, 0) = B.edges[j]'hjB :=
          List.getD_eq_getElem _ _ hjB
        have hj_walk := hBC.2 j hjB
        have hstep_walk : (if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = b then
            embBC j else (embBC j).reverse).IsWalk C u b := by
          rw [hBe] at hstep0 ⊢
          rcases hstep0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [h1, h2, and_self, ↓reduceIte]
            simpa [h1, h2] using hj_walk
          · split_ifs with hcond
            · rw [hcond.1, hcond.2] at hj_walk
              exact hj_walk
            · rw [← h1, ← h2]
              exact Walk.isWalk_reverse hj_walk
        have hlen' : (b :: vs'').length = js.length + 1 := by simpa using hlen
        have hlast' : (b :: vs'').getLast? = some v := by
          simpa [List.getLast?_cons_cons] using hlast
        have hedges' : ∀ m ∈ js, m < B.m := fun m hm => hedges m (List.mem_cons_of_mem j hm)
        have hstep' : ∀ i : ℕ, i < js.length →
            Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0))
              ((b :: vs'').getD i 0) ((b :: vs'').getD (i + 1) 0) := by
          intro i hi
          have := hstep (i + 1) (by simpa using Nat.succ_lt_succ hi)
          simpa [List.getD_eq_getElem?_getD] using this
        have htail_walk : (composeAux B embBC (b :: vs'') js).IsWalk C b v :=
          composeAux_isWalk hBC js (b :: vs'') b v hlen' rfl hlast' hedges' hstep' hv
        dsimp only [composeAux]
        rw [Walk.mem_verts_append_iff hstep_walk htail_walk x]
        rcases List.mem_cons.mp hk with rfl | hk'
        · left
          split_ifs
          · exact hx
          · simpa [Walk.reverse] using hx
        · right
          exact ih (b :: vs'') b v k x hlen' rfl hlast' hedges' hstep' hv hk' hx

private theorem mem_verts_compose_of_mem {B C : Graph} {embBC embAB : ℕ → Walk}
    (hBC : IsEmbedding B C embBC) {eA k x : ℕ}
    (hAB_walk : ∃ u v, (embAB eA).IsWalk B u v)
    (hk : k ∈ (embAB eA).edges) (hx : x ∈ (embBC k).verts) :
    x ∈ (compose B embBC embAB eA).verts := by
  rcases hAB_walk with ⟨u, v, hu, hv, ⟨_, hPe, _⟩ | ⟨_, hlen, hhead, hlast, hedges, hstep⟩⟩
  · simp [hPe] at hk
  · exact composeAux_mem_verts_of_mem hBC (embAB eA).edges (embAB eA).verts u v k x
      hlen hhead hlast hedges hstep hv hk hx

private theorem composeAux_mapEdges_restrictEmb {J : Graph} {embJH : ℕ → Walk}
    {keptEdges : List ℕ} :
    ∀ (js vs : List ℕ), (∀ j ∈ js, j ∈ keptEdges) →
      composeAux ⟨J.n, keptEdges.map fun j => J.edges.getD j (0, 0)⟩
        (restrictEmb embJH keptEdges) vs (js.map keptEdges.idxOf) =
      composeAux J embJH vs js := by
  intro js
  induction js with
  | nil =>
    intro vs _
    cases vs with
    | nil => rfl
    | cons _ vs' => cases vs' <;> rfl
  | cons j js ih =>
    intro vs hjs
    cases vs with
    | nil => rfl
    | cons u vs' =>
      cases vs' with
      | nil => rfl
      | cons v vs'' =>
        have hj_mem : j ∈ keptEdges := hjs j List.mem_cons_self
        have hidx_lt : keptEdges.idxOf j < keptEdges.length :=
          List.idxOf_lt_length_of_mem hj_mem
        have hget_kept : keptEdges.getD (keptEdges.idxOf j) 0 = j := by
          rw [List.getD_eq_getElem _ _ hidx_lt]
          exact List.getElem_idxOf hidx_lt
        have hedge_eq :
            (⟨J.n, keptEdges.map fun k => J.edges.getD k (0, 0)⟩ : Graph).edges.getD
              (keptEdges.idxOf j) (0, 0) = J.edges.getD j (0, 0) := by
          dsimp only
          rw [List.getD_eq_getElem _ _ (by simpa using hidx_lt), List.getElem_map,
            List.getElem_idxOf hidx_lt]
        have hemb_eq : restrictEmb embJH keptEdges (keptEdges.idxOf j) = embJH j := by
          unfold restrictEmb
          rw [hget_kept]
        simp only [List.map_cons, composeAux, hedge_eq, hemb_eq,
          ih (v :: vs'') (fun m hm => hjs m (List.mem_cons_of_mem j hm))]

private theorem length_restrictEmb_le {J : Graph} {embJH : ℕ → Walk}
    {keptEdges : List ℕ} (hkept : ∀ j ∈ keptEdges, j < J.m) :
    length ⟨J.n, keptEdges.map fun j => J.edges.getD j (0, 0)⟩ (restrictEmb embJH keptEdges) ≤
      length J embJH := by
  rw [length_le_iff]
  intro k hk
  dsimp only [Graph.m] at hk
  rw [List.length_map] at hk
  have hmem : keptEdges[k]'hk ∈ keptEdges := List.getElem_mem hk
  have hj : keptEdges[k]'hk < J.m := hkept _ hmem
  have hget : keptEdges.getD k 0 = keptEdges[k]'hk := List.getD_eq_getElem _ _ hk
  dsimp only [restrictEmb]
  rw [hget]
  exact edges_length_le_length embJH hj

private theorem vcong_le_of_verts_subset {A B : Graph} {wA : ℕ → ℝ} {emb₁ emb₂ : ℕ → Walk}
    (hwA : ∀ j < A.m, 0 ≤ wA j)
    (hsub : ∀ j < A.m, ∀ x, x ∈ (emb₁ j).verts → x ∈ (emb₂ j).verts) :
    vcong A B wA emb₁ ≤ vcong A B wA emb₂ := by
  rw [vcong_le_iff]
  refine ⟨vcong_nonneg A B wA emb₂, fun v hv => ?_⟩
  refine le_trans ?_ (vcongAt_le_vcong wA emb₂ hv)
  unfold vcongAt
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j hj _ =>
    hwA j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))
  intro j hj
  rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨hj.1, hsub j hj.1 v hj.2⟩

private theorem flatMap_range_edges_length_le {n B : ℕ} {f : ℕ → Walk}
    (hf : ∀ i < n, (f i).edges.length ≤ B) :
    ((List.range n).flatMap fun i => (f i).edges).length ≤ n * B := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
        Nat.succ_mul]
    have hm : ((List.range m).flatMap fun i => (f i).edges).length ≤ m * B :=
      ih fun i hi => hf i (Nat.lt_succ_of_lt hi)
    have hlast : (f m).edges.length ≤ B := hf m (Nat.lt_succ_self m)
    exact Nat.add_le_add hm hlast

private lemma nonneg_of_pos_mul_ge {x a y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (h : y ≤ x * a) :
    0 ≤ a := by
  by_contra hlt
  push Not at hlt
  have h1 : x * a < 0 := mul_neg_of_pos_of_neg hx hlt
  linarith

private lemma theorem81_cong_step1 {v f c a₁ a₂ b₁ b₂ t₁ t₂ : ℝ}
    (hv : v ≤ f) (hf : f ≤ c) (hc : c ≤ (a₁ * t₁) * (b₁ * t₂))
    (ha₁ : 0 ≤ a₁) (ht₁ : 0 ≤ t₁) (hb₁ : 0 ≤ b₁) (ht₂ : 0 ≤ t₂)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    v ≤ (a₁ * b₁) * t₁ * t₂ ∧ v ≤ (a₂ * b₂) * t₁ * t₂ := by
  have h1 : v ≤ (a₁ * b₁) * t₁ * t₂ := by
    calc v ≤ (a₁ * t₁) * (b₁ * t₂) := le_trans hv (le_trans hf hc)
      _ = (a₁ * b₁) * t₁ * t₂ := by ring
  have ha_nn : 0 ≤ a₂ := le_trans ha₁ ha
  have h2 : (a₁ * b₁) * t₁ * t₂ ≤ (a₂ * b₂) * t₁ * t₂ := by
    calc (a₁ * b₁) * t₁ * t₂ = (a₁ * b₁) * (t₁ * t₂) := by ring
      _ ≤ (a₂ * b₂) * (t₁ * t₂) :=
          mul_le_mul_of_nonneg_right (mul_le_mul ha hb hb₁ ha_nn) (mul_nonneg ht₁ ht₂)
      _ = (a₂ * b₂) * t₁ * t₂ := by ring
  exact ⟨h1, le_trans h1 h2⟩

/-- Core graph-embedding derivation for Algorithm 4, isolated from `buildWitness`/`task2`/`task3`
definitions so kernel unification stays instantaneous. -/
theorem theorem_8_1_core (H' J W : Graph) (wW : ℕ → ℝ) (embJH embWJ embJW : ℕ → Walk)
    (hWn : W.n = J.n) (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hWJ : IsEmbedding W J embWJ) (hJW : IsEmbedding J W embJW)
    (hwW_pos : ∀ eW < W.m, 0 < wW eW)
    {a₁ a₂ b₁ b₂ t₁ t₂ Γ : ℝ}
    (ha₁_nn : 0 ≤ a₁) (ha₁_pos : 0 < a₁) (hb₁_nn : 0 ≤ b₁) (hb₁_pos : 0 < b₁)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hvc : vcong W H' wW (compose J embJH embWJ) ≤ a₁ * t₁)
    (hec : econg J W (fun _ => 1) wW embJW ≤ b₁ * t₂)
    (hlen₁ : (length W embWJ : ℝ) ≤ Γ) (hlen₂ : (length J embJW : ℝ) ≤ Γ) :
    let keptEdges := ((List.range W.m).flatMap fun eW => (embWJ eW).edges).dedup
    let Jtilde : Graph := ⟨J.n, keptEdges.map fun j => J.edges.getD j (0, 0)⟩
    let embWJtilde : ℕ → Walk := fun eW => (embWJ eW).mapEdges keptEdges.idxOf
    let embJHtilde := restrictEmb embJH keptEdges
    let embJJtilde := compose W embWJtilde embJW
    keptEdges.Nodup ∧
    (∀ j ∈ keptEdges, j < J.m) ∧
    Jtilde.n = J.n ∧
    Jtilde.m = keptEdges.length ∧
    Jtilde.IsValid ∧
    IsEmbedding W Jtilde embWJtilde ∧
    IsEmbedding Jtilde H' embJHtilde ∧
    IsEmbedding J Jtilde embJJtilde ∧
    vcong J H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤ (a₁ * b₁) * t₁ * t₂ ∧
    vcong J H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤ (a₂ * b₂) * t₁ * t₂ ∧
    (length J embJJtilde : ℝ) ≤ Γ ^ 2 ∧
    (length J (compose Jtilde embJHtilde embJJtilde) : ℝ) ≤ Γ ^ 2 * (length J embJH : ℝ) ∧
    (Jtilde.m : ℝ) ≤ (W.m : ℝ) * Γ := by
  intro keptEdges Jtilde embWJtilde embJHtilde embJJtilde
  have hnodup : keptEdges.Nodup := List.nodup_dedup _
  have hkept_edges_lt : ∀ j ∈ keptEdges, j < J.m := by
    intro j hj
    have hj' := List.mem_dedup.mp hj
    rw [List.mem_flatMap] at hj'
    rcases hj' with ⟨eW, heW_r, hj_eW⟩
    have heWm : eW < W.m := List.mem_range.mp heW_r
    have hwalk := hWJ.2 eW heWm
    rcases hwalk.2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
    · simp [hPe] at hj_eW
    · exact hedges j hj_eW
  have hJtilde_m : Jtilde.m = keptEdges.length := by
    dsimp only [Jtilde, Graph.m]
    exact List.length_map _
  have hJtilde_valid : Jtilde.IsValid := by
    intro e he
    dsimp only [Jtilde] at he ⊢
    rcases List.mem_map.mp he with ⟨j, hj, rfl⟩
    have hjm := hkept_edges_lt j hj
    have he_J : J.edges.getD j (0, 0) ∈ J.edges := by
      rw [List.getD_eq_getElem _ _ hjm]
      exact List.getElem_mem hjm
    exact hJ _ he_J
  have hemb_WJtilde : IsEmbedding W Jtilde embWJtilde := by
    refine ⟨by dsimp only [Jtilde]; exact le_of_eq hWn, fun eW heWm => ?_⟩
    have hwalk := hWJ.2 eW heWm
    refine isWalk_mapEdges_of_mem (H := J) (H' := Jtilde) le_rfl (fun j hj_edges hjm => ?_) hwalk
    have hj_kept : j ∈ keptEdges := by
      dsimp only [keptEdges]
      rw [List.mem_dedup, List.mem_flatMap]
      exact ⟨eW, List.mem_range.mpr heWm, hj_edges⟩
    have hidx_lt : keptEdges.idxOf j < keptEdges.length :=
      List.idxOf_lt_length_of_mem hj_kept
    refine ⟨by rw [hJtilde_m]; exact hidx_lt, ?_⟩
    dsimp only [Jtilde]
    rw [List.getD_eq_getElem _ _ (by simpa using hidx_lt), List.getElem_map,
      List.getElem_idxOf hidx_lt]
  have hemb_JHtilde : IsEmbedding Jtilde H' embJHtilde :=
    isEmbedding_restrictEmb hkept_edges_lt hembJH
  have hemb_JJtilde : IsEmbedding J Jtilde embJJtilde :=
    isEmbedding_compose hJW hemb_WJtilde
  have hcomp_eq : ∀ eW < W.m,
      compose Jtilde embJHtilde embWJtilde eW = compose J embJH embWJ eW := by
    intro eW heWm
    dsimp only [compose, embWJtilde]
    refine composeAux_mapEdges_restrictEmb (embWJ eW).edges (embWJ eW).verts fun j hj => ?_
    dsimp only [keptEdges]
    rw [List.mem_dedup, List.mem_flatMap]
    exact ⟨eW, List.mem_range.mpr heWm, hj⟩
  have hvcong_triple_le :
      vcong J H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
        vcong J H' (fun _ => 1) (compose W (compose J embJH embWJ) embJW) := by
    refine vcong_le_of_verts_subset (fun _ _ => zero_le_one) fun eJ heJm x hx => ?_
    obtain ⟨k, hk_edges, hx_k⟩ := mem_verts_compose hx
    obtain ⟨eW, heW_edges, hk_eW⟩ := mem_edges_compose hk_edges
    have heWm : eW < W.m := by
      rcases (hJW.2 eJ heJm).2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
      · simp [hPe] at heW_edges
      · exact hedges eW heW_edges
    have hx_sub : x ∈ (compose Jtilde embJHtilde embWJtilde eW).verts :=
      mem_verts_compose_of_mem hemb_JHtilde ⟨_, _, hemb_WJtilde.2 eW heWm⟩ hk_eW hx_k
    rw [hcomp_eq eW heWm] at hx_sub
    exact mem_verts_compose_of_mem (isEmbedding_compose hWJ hembJH)
      ⟨_, _, hJW.2 eJ heJm⟩ heW_edges hx_sub
  have hfact1 := fact_1 (A := J) (B := W) (C := H')
    (wA := fun _ => 1) (wB := wW)
    (embBC := compose J embJH embWJ) (embAB := embJW)
    (fun _ _ => zero_le_one)
    hwW_pos
    (fun eJ heJm eW heW => by
      rcases (hJW.2 eJ heJm).2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
      · simp [hPe] at heW
      · exact hedges eW heW)
  have ht₁_nn : 0 ≤ t₁ := nonneg_of_pos_mul_ge ha₁_pos (vcong_nonneg _ _ _ _) hvc
  have ht₂_nn : 0 ≤ t₂ := nonneg_of_pos_mul_ge hb₁_pos (econg_nonneg J W (fun _ => 1) wW embJW) hec
  have hvc_nn1 : 0 ≤ a₁ * t₁ := le_trans (vcong_nonneg _ _ _ _) hvc
  have hfact1_mul :
      vcong W H' wW (compose J embJH embWJ) * econg J W (fun _ => 1) wW embJW ≤
        (a₁ * t₁) * (b₁ * t₂) :=
    mul_le_mul hvc hec (econg_nonneg J W (fun _ => 1) wW embJW) hvc_nn1
  have ⟨hcong1, hcong2⟩ :=
    theorem81_cong_step1 hvcong_triple_le hfact1 hfact1_mul ha₁_nn ht₁_nn hb₁_nn ht₂_nn ha hb
  have hγE_nn : 0 ≤ Γ := le_trans (Nat.cast_nonneg _) hlen₂
  have hWJtilde_len : (length W embWJtilde : ℝ) ≤ Γ := by
    have hle : length W embWJtilde ≤ length W embWJ := by
      rw [length_le_iff]
      intro eW heWm
      dsimp only [embWJtilde, Walk.mapEdges]
      rw [List.length_map]
      exact edges_length_le_length embWJ heWm
    exact le_trans (Nat.cast_le.mpr hle) hlen₁
  have hJJtilde_len_nat : length J embJJtilde ≤ length J embJW * length W embWJtilde :=
    length_compose_le fun eJ heJm eW heW => by
      rcases (hJW.2 eJ heJm).2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
      · simp [hPe] at heW
      · exact hedges eW heW
  have hJJtilde_len : (length J embJJtilde : ℝ) ≤ Γ ^ 2 := by
    have hmul : (length J embJJtilde : ℝ) ≤ (length J embJW : ℝ) * (length W embWJtilde : ℝ) := by
      exact_mod_cast hJJtilde_len_nat
    calc (length J embJJtilde : ℝ)
        ≤ (length J embJW : ℝ) * (length W embWJtilde : ℝ) := hmul
      _ ≤ Γ * Γ := mul_le_mul hlen₂ hWJtilde_len (Nat.cast_nonneg _) hγE_nn
      _ = Γ ^ 2 := (sq _).symm
  have hcomp_len : (length J (compose Jtilde embJHtilde embJJtilde) : ℝ) ≤
      Γ ^ 2 * (length J embJH : ℝ) := by
    have hcomp_nat : length J (compose Jtilde embJHtilde embJJtilde) ≤
        length J embJJtilde * length Jtilde embJHtilde :=
      length_compose_le fun eJ heJm k hk => by
        rcases (hemb_JJtilde.2 eJ heJm).2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
        · simp [hPe] at hk
        · exact hedges k hk
    have hr_nat : length Jtilde embJHtilde ≤ length J embJH :=
      length_restrictEmb_le hkept_edges_lt
    have hcomp_real : (length J (compose Jtilde embJHtilde embJJtilde) : ℝ) ≤
        (length J embJJtilde : ℝ) * (length J embJH : ℝ) := by
      exact_mod_cast le_trans hcomp_nat (Nat.mul_le_mul_left _ hr_nat)
    exact le_trans hcomp_real (mul_le_mul_of_nonneg_right hJJtilde_len (Nat.cast_nonneg _))
  have hJtilde_m_Wm : (Jtilde.m : ℝ) ≤ (W.m : ℝ) * Γ := by
    have hdedup : keptEdges.length ≤
        ((List.range W.m).flatMap fun eW => (embWJ eW).edges).length :=
      List.Sublist.length_le (List.dedup_sublist _)
    have hflat : ((List.range W.m).flatMap fun eW => (embWJ eW).edges).length ≤
        W.m * length W embWJ :=
      flatMap_range_edges_length_le fun eW heWm => edges_length_le_length embWJ heWm
    have hnat : Jtilde.m ≤ W.m * length W embWJ := by
      rw [hJtilde_m]
      exact le_trans hdedup hflat
    have hreal : (Jtilde.m : ℝ) ≤ (W.m : ℝ) * (length W embWJ : ℝ) := by
      exact_mod_cast hnat
    exact le_trans hreal (mul_le_mul_of_nonneg_left hlen₁ (Nat.cast_nonneg _))
  exact ⟨hnodup, hkept_edges_lt, rfl, hJtilde_m, hJtilde_valid,
    hemb_WJtilde, hemb_JHtilde, hemb_JJtilde,
    hcong1, hcong2, hJJtilde_len, hcomp_len, hJtilde_m_Wm⟩

/-! ## Theorem 8.1 (`Sparsify`) -/

/-- **Theorem 8.1** (`spanner.tex`, page 39; proof pages 44–45) for `LocalSpannerTools`:
Given valid graphs `H'`, `J` with `J.n ≤ N_max`, `2 · J.m / φ_dec(stripLoops J) ≤ W_max`, and
embedding `embJH : J → H'`, `out := sparsifyLocal tools H' J embJH` outputs a subgraph
`Jtilde ⊆ J` (`keptEdges.Nodup`), valid embeddings `embWJtilde : W → Jtilde`,
`embJJtilde : J → Jtilde`, and restricted embedding `embJHtilde : Jtilde → H'` satisfying all four
guarantees: congestion (`Fact 1`, Corollaries 8.8 and 8.10), length (`γ_ExpPath²`), sparsity
(`J̃.m ≤ W.m · γ_ExpPath`), and explicit work/tool-call bounds (`out.stats`). -/
theorem theorem_8_1_local {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hNmax : J.n ≤ N_max)
    (hWmax : 2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J) ≤ W_max) :
    let out := sparsifyLocal tools H' J embJH
    let wd := out.wd
    let embJHtilde := restrictEmb embJH out.keptEdges
    let st := out.stats
    -- 1. Subgraph and embedding validity
    out.keptEdges.Nodup ∧
    (∀ j ∈ out.keptEdges, j < J.m) ∧
    out.Jtilde.n = J.n ∧
    out.Jtilde.m = out.keptEdges.length ∧
    out.Jtilde.IsValid ∧
    IsEmbedding wd.W out.Jtilde out.embWJtilde ∧
    IsEmbedding J wd.W out.embJW ∧
    IsEmbedding out.Jtilde H' embJHtilde ∧
    IsEmbedding J out.Jtilde out.embJJtilde ∧
    -- 2. Congestion bound (Conclusion 1)
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      (((st.η₁ : ℝ) + 1 / 2) * ((st.η₂ : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      (((eta1Bound wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
    -- 3. Length bound (Conclusion 2)
    (length J out.embJJtilde : ℝ) ≤ wd.γ_ExpPath ^ 2 ∧
    (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      wd.γ_ExpPath ^ 2 * (length J embJH : ℝ) ∧
    -- 4. Sparsity bound (Conclusion 3)
    (out.Jtilde.m : ℝ) ≤ (wd.W.m : ℝ) * wd.γ_ExpPath ∧
    (out.Jtilde.m : ℝ) ≤ ((J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec) *
      wd.γ_ExpPath ∧
    (out.Jtilde.m : ℝ) ≤ ((J.m : ℝ) + wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec)) * wd.γ_ExpPath ∧
    -- 5. Work & tool-call bounds (Conclusion 4)
    st.decomposeCalls = 1 ∧
    st.constructCalls = wd.comps.length ∧
    st.constructCalls ≤ J.m ∧
    st.constructVerts ≤ wd.decomp.ℓ * J.n ∧
    st.constructVerts ≤ 2 * J.m ∧
    st.constructWeightSum ≤ (J.m : ℝ) / wd.φ_dec ∧
    (1 ≤ st.η₁ ∧ st.η₁ ≤ eta1Bound wd J ∧
      st.dsInitCountJ = st.η₁ * wd.comps.length ∧
      st.dsInitEdgesJ ≤ st.η₁ * J.m ∧
      st.dsGetPathCountJ = wd.W.m - wd.j0Edges.length ∧
      st.dsGetPathCountJ ≤ wd.W.m ∧
      st.middleIters1 = st.dsGetPathCountJ ∧
      st.dsDeleteCountJ ≤ st.η₁ * J.m ∧
      (st.vcongUpdates : ℝ) ≤ (st.dsGetPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) ∧
      st.innerIters1 ≤ st.η₁ * H'.n ∧
      (st.innerIters1 : ℝ) ≤
        (st.dsGetPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))) ∧
    (1 ≤ st.η₂ ∧ st.η₂ ≤ eta2Bound J ∧
      st.dsInitCountW = st.η₂ * wd.comps.length ∧
      st.dsInitEdgesW ≤ st.η₂ * wd.W.m ∧
      st.dsGetPathCountW ≤ J.m ∧
      st.middleIters2 = st.dsGetPathCountW ∧
      st.dsDeleteCountW = st.innerIters2 ∧
      st.innerIters2 ≤ st.η₂ * wd.W.m ∧
      (st.innerIters2 : ℝ) ≤ (st.dsGetPathCountW : ℝ) * wd.γ_ExpPath ∧
      (st.econgUpdates : ℝ) ≤ (st.dsGetPathCountW : ℝ) * wd.γ_ExpPath) := by
  dsimp only [sparsifyLocal]
  set wd := buildWitness tools H' J embJH
  have hw : WitnessOK tools H' J embJH wd :=
    buildWitness_ok tools H' J embJH hJ hembJH hNmax hWmax
  have hc88 := corollary_8_8 tools H' J embJH hJ hembJH hw
  have hc810 := corollary_8_10 tools H' J embJH hJ hw
  have hst2 := task2_stats tools H' J embJH hJ hembJH hw
  have hst3 := task3_stats tools H' J embJH hJ hw
  rcases hc88 with ⟨hWJ_emb, hvcong_st, _, hWJ_len⟩
  rcases hc810 with ⟨hJW_emb, hecong_st, _, hJW_len⟩
  have hcore := theorem_8_1_core H' J wd.W wd.wW embJH
    (partialToWalk (task2 tools.pathDS H' J embJH wd).embWJ)
    (partialToWalk (task3 tools.pathDS J wd).embJW)
    rfl hJ hembJH hWJ_emb hJW_emb
    (fun eW heWm => wW_pos tools H' J embJH hw heWm)
    (add_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
    (add_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
    (add_le_add (Nat.cast_le.mpr hst2.2.1) le_rfl)
    (add_le_add (Nat.cast_le.mpr hst3.2.1) le_rfl)
    hvcong_st hecong_st hWJ_len hJW_len
  rcases hcore with ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid,
    hemb_WJtilde, hemb_JHtilde, hemb_JJtilde,
    hcong1, hcong2, hJJtilde_len, hcomp_len, hJtilde_m_Wm⟩
  have hγE_nn : 0 ≤ wd.γ_ExpPath := le_trans (Nat.cast_nonneg _) hJW_len
  have hJtilde_m_n : (((⟨J.n, (((List.range wd.W.m).flatMap fun eW =>
      (partialToWalk (task2 tools.pathDS H' J embJH wd).embWJ eW).edges).dedup).map
        fun j => J.edges.getD j (0, 0)⟩ : Graph).m : ℝ)) ≤
      ((J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec) * wd.γ_ExpPath :=
    le_trans hJtilde_m_Wm (mul_le_mul_of_nonneg_right (W_m_le_n tools H' J embJH hJ hw) hγE_nn)
  have hJtilde_m_m : (((⟨J.n, (((List.range wd.W.m).flatMap fun eW =>
      (partialToWalk (task2 tools.pathDS H' J embJH wd).embWJ eW).edges).dedup).map
        fun j => J.edges.getD j (0, 0)⟩ : Graph).m : ℝ)) ≤
      ((J.m : ℝ) + wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec)) * wd.γ_ExpPath :=
    le_trans hJtilde_m_Wm (mul_le_mul_of_nonneg_right (W_m_le_m tools H' J embJH hw) hγE_nn)
  have hvert_n := sum_comps_card_le_n tools H' J embJH hJ hw
  have hvert_m := sum_comps_card_le_m tools H' J embJH hw
  have hwsum := sum_comps_w_le_m tools H' J embJH hw
  exact ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid,
    hemb_WJtilde, hJW_emb, hemb_JHtilde, hemb_JJtilde,
    hcong1, hcong2, hJJtilde_len, hcomp_len,
    hJtilde_m_Wm, hJtilde_m_n, hJtilde_m_m,
    rfl, rfl, hst2.2.2.1, hvert_n, hvert_m, hwsum,
    ⟨hst2.1, hst2.2.1, hst2.2.2.2.1, hst2.2.2.2.2.2.1, hst2.2.2.2.2.2.2.1,
     hst2.2.2.2.2.2.2.2.1, hst2.2.2.2.2.2.2.2.2.1, hst2.2.2.2.2.2.2.2.2.2.1,
     hst2.2.2.2.2.2.2.2.2.2.2.1, hst2.2.2.2.2.2.2.2.2.2.2.2.1, hst2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hst3.1, hst3.2.1, hst3.2.2.1, hst3.2.2.2.2.1, hst3.2.2.2.2.2.1,
     hst3.2.2.2.2.2.2.1, hst3.2.2.2.2.2.2.2.1, hst3.2.2.2.2.2.2.2.2.1,
     hst3.2.2.2.2.2.2.2.2.2.1, hst3.2.2.2.2.2.2.2.2.2.2⟩⟩

/-- Internal detailed **Theorem 8.1** (`spanner.tex`, page 39; proof pages 44–45) for global `SpannerTools`. -/
theorem theorem_8_1_internal (tools : SpannerTools) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH) :
    let out := sparsify tools H' J embJH
    let wd := out.wd
    let embJHtilde := restrictEmb embJH out.keptEdges
    let st := out.stats
    out.keptEdges.Nodup ∧
    (∀ j ∈ out.keptEdges, j < J.m) ∧
    out.Jtilde.n = J.n ∧
    out.Jtilde.m = out.keptEdges.length ∧
    out.Jtilde.IsValid ∧
    IsEmbedding wd.W out.Jtilde out.embWJtilde ∧
    IsEmbedding J wd.W out.embJW ∧
    IsEmbedding out.Jtilde H' embJHtilde ∧
    IsEmbedding J out.Jtilde out.embJJtilde ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      (((st.η₁ : ℝ) + 1 / 2) * ((st.η₂ : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      (((eta1Bound wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
    (length J out.embJJtilde : ℝ) ≤ wd.γ_ExpPath ^ 2 ∧
    (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      wd.γ_ExpPath ^ 2 * (length J embJH : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤ (wd.W.m : ℝ) * wd.γ_ExpPath ∧
    (out.Jtilde.m : ℝ) ≤ ((J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec) *
      wd.γ_ExpPath ∧
    (out.Jtilde.m : ℝ) ≤ ((J.m : ℝ) + wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec)) * wd.γ_ExpPath ∧
    st.decomposeCalls = 1 ∧
    st.constructCalls = wd.comps.length ∧
    st.constructCalls ≤ J.m ∧
    st.constructVerts ≤ wd.decomp.ℓ * J.n ∧
    st.constructVerts ≤ 2 * J.m ∧
    st.constructWeightSum ≤ (J.m : ℝ) / wd.φ_dec ∧
    (1 ≤ st.η₁ ∧ st.η₁ ≤ eta1Bound wd J ∧
      st.dsInitCountJ = st.η₁ * wd.comps.length ∧
      st.dsInitEdgesJ ≤ st.η₁ * J.m ∧
      st.dsGetPathCountJ = wd.W.m - wd.j0Edges.length ∧
      st.dsGetPathCountJ ≤ wd.W.m ∧
      st.middleIters1 = st.dsGetPathCountJ ∧
      st.dsDeleteCountJ ≤ st.η₁ * J.m ∧
      (st.vcongUpdates : ℝ) ≤ (st.dsGetPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) ∧
      st.innerIters1 ≤ st.η₁ * H'.n ∧
      (st.innerIters1 : ℝ) ≤
        (st.dsGetPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))) ∧
    (1 ≤ st.η₂ ∧ st.η₂ ≤ eta2Bound J ∧
      st.dsInitCountW = st.η₂ * wd.comps.length ∧
      st.dsInitEdgesW ≤ st.η₂ * wd.W.m ∧
      st.dsGetPathCountW ≤ J.m ∧
      st.middleIters2 = st.dsGetPathCountW ∧
      st.dsDeleteCountW = st.innerIters2 ∧
      st.innerIters2 ≤ st.η₂ * wd.W.m ∧
      (st.innerIters2 : ℝ) ≤ (st.dsGetPathCountW : ℝ) * wd.γ_ExpPath ∧
      (st.econgUpdates : ℝ) ≤ (st.dsGetPathCountW : ℝ) * wd.γ_ExpPath) :=
  theorem_8_1_local
    (tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J)))
    H' J embJH hJ hembJH le_rfl le_rfl

end MinCostFlow.Spanner
