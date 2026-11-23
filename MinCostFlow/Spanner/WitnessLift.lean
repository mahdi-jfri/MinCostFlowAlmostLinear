module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps
public import MinCostFlow.Spanner.WitnessBounds
public import Mathlib.Algebra.BigOperators.Intervals

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Task 1 global bounds and walk lifting

This file completes the Task 1 properties for `wd := buildWitness tools H' J embJH`:
- Disjoint-partition counting bounds (`sum_list_card_le`, `sum_list_inside_le`).
- Witness weight and edge-count bounds (`sum_Ico_wW_eq`, `sum_wW_comp_le`, `sum_wW_le`,
  `W_m_comp_le_m`, `W_m_le_m`, `W_m_le_n`, `sum_comps_card_le_n`, `sum_comps_card_le_m`,
  `sum_comps_w_le_m`).
- Correctness and endpoint/edge properties of `liftJSubWalk` and `liftWSubWalk`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Disjoint list summation helpers -/

theorem sum_list_card_le :
    ∀ (L : List (Finset ℕ)) (U : Finset ℕ),
      L.Pairwise Disjoint → (∀ X ∈ L, X ⊆ U) → (L.map Finset.card).sum ≤ U.card := by
  intro L
  induction L with
  | nil => intro U _ _; simp
  | cons X rest ih =>
    intro U hpw hsub
    simp only [List.pairwise_cons] at hpw
    have hX : X ⊆ U := hsub X List.mem_cons_self
    have hrest : ∀ Y ∈ rest, Y ⊆ U \ X := by
      intro Y hY
      rw [Finset.subset_sdiff]
      exact ⟨hsub Y (List.mem_cons_of_mem X hY), (hpw.1 Y hY).symm⟩
    have hsum := ih (U \ X) hpw.2 hrest
    have hcard := Finset.card_sdiff_add_card_eq_card hX
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_list_inside_le (G : Graph) :
    ∀ (L : List (Finset ℕ)) (U : Finset ℕ),
      L.Pairwise Disjoint →
      (∀ X ∈ L, (insideIndices G X).toFinset ⊆ U) →
      (L.map fun X => (G.inside X).length).sum ≤ U.card := by
  intro L
  induction L with
  | nil => intro U _ _; simp
  | cons X rest ih =>
    intro U hpw hsub
    simp only [List.pairwise_cons] at hpw
    have hX : (insideIndices G X).toFinset ⊆ U := hsub X List.mem_cons_self
    have hlen_X : (G.inside X).length = (insideIndices G X).toFinset.card := by
      rw [List.toFinset_card_of_nodup (insideIndices_nodup G X),
        ← insideIndices_map_eq_inside G X, List.length_map]
    have hrest : ∀ Y ∈ rest, (insideIndices G Y).toFinset ⊆ U \ (insideIndices G X).toFinset := by
      intro Y hY
      rw [Finset.subset_sdiff]
      refine ⟨hsub Y (List.mem_cons_of_mem X hY), ?_⟩
      rw [Finset.disjoint_left]
      intro j hjY hjX
      rw [List.mem_toFinset] at hjY hjX
      have hj1 := (mem_insideIndices.mp hjX).2.1
      have hj2 := (mem_insideIndices.mp hjY).2.1
      exact Finset.disjoint_left.mp (hpw.1 Y hY) hj1 hj2
    have hsum := ih (U \ (insideIndices G X).toFinset) hpw.2 hrest
    have hcard := Finset.card_sdiff_add_card_eq_card hX
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## Component-level edge and weight bounds -/

theorem sum_range_getD_real {α : Type*} (l : List α) (d : α) (f : α → ℝ) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ', add_comm, List.map_cons, List.sum_cons]
    have h0 : (a :: as).getD 0 d = a := rfl
    have hs : ∀ i, (a :: as).getD (i + 1) d = as.getD i d := fun _ => rfl
    simp_rw [hs]
    rw [h0, ih]

theorem sum_range_getD_nat {α : Type*} (l : List α) (d : α) (f : α → ℕ) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ', add_comm, List.map_cons, List.sum_cons]
    have h0 : (a :: as).getD 0 d = a := rfl
    have hs : ∀ i, (a :: as).getD (i + 1) d = as.getD i d := fun _ => rfl
    simp_rw [hs]
    rw [h0, ih]

private theorem sum_flatMap_real {α β : Type*} (l : List α) (g : α → List β) (f : β → ℝ) :
    ((l.flatMap g).map f).sum = (l.map fun x => ((g x).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_flatMap_nat {α β : Type*} (l : List α) (g : α → List β) (f : β → ℕ) :
    ((l.flatMap g).map f).sum = (l.map fun x => ((g x).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_Ico_wW_eq {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m, wd.wW eW =
      (wd.comps.map fun c => (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ))).sum := by
  intro wd
  let S : ℕ → Finset ℕ := fun ci =>
    if h : ci < wd.comps.length then
      Finset.Ico (wd.comps[ci]'h).wStart ((wd.comps[ci]'h).wStart + (wd.comps[ci]'h).W_sub.m)
    else ∅
  have hunion : Finset.Ico wd.j0Edges.length wd.W.m = (Finset.range wd.comps.length).biUnion S := by
    ext eW
    simp only [Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range, S]
    constructor
    · rintro ⟨hle, hlt⟩
      rcases W_edge_cases tools H' J embJH hlt with hj0 | ⟨ci, hci, eL, heL, heq⟩
      · exact absurd hj0 (Nat.not_lt_of_ge hle)
      · have hci' : ci < wd.comps.length := hci
        refine ⟨ci, hci', ?_⟩
        split_ifs
        rw [Finset.mem_Ico]
        exact ⟨heq ▸ Nat.le_add_right _ _, heq ▸ Nat.add_lt_add_left heL _⟩
    · rintro ⟨ci, hci, heW⟩
      split_ifs at heW
      rw [Finset.mem_Ico] at heW
      rcases hw.comp_props ci hci with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwStart, hwEnd⟩
      exact ⟨le_trans hwStart heW.1, lt_of_lt_of_le heW.2 hwEnd⟩
  have hdisj : Set.PairwiseDisjoint ↑(Finset.range wd.comps.length) S := by
    intro ci₁ h1 ci₂ h2 hne
    have h1' : ci₁ < wd.comps.length := Finset.mem_range.mp h1
    have h2' : ci₂ < wd.comps.length := Finset.mem_range.mp h2
    simp only [Function.onFun, S, Finset.disjoint_left]
    split_ifs
    intro eW he1 he2
    rw [Finset.mem_Ico] at he1 he2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hadj := compsAligned_adjacent hw.aligned ci₁ ci₂ h1' h2' hlt
      exact absurd he2.1 (Nat.not_le_of_lt (lt_of_lt_of_le he1.2 hadj))
    · have hadj := compsAligned_adjacent hw.aligned ci₂ ci₁ h2' h1' hgt
      exact absurd he1.1 (Nat.not_le_of_lt (lt_of_lt_of_le he2.2 hadj))
  rw [hunion, Finset.sum_biUnion hdisj]
  have hcongr : ∑ ci ∈ Finset.range wd.comps.length, ∑ eW ∈ S ci, wd.wW eW =
      ∑ ci ∈ Finset.range wd.comps.length,
        ((wd.comps.getD ci defaultCompInfo).W_sub.m : ℝ) *
          (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) := by
    refine Finset.sum_congr rfl fun ci hci_r => ?_
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    set c := wd.comps[ci]'hci
    have hS : S ci = Finset.Ico c.wStart (c.wStart + c.W_sub.m) := by
      dsimp only [S]
      split_ifs
      rfl
    rw [hS]
    have hconst : ∑ eW ∈ Finset.Ico c.wStart (c.wStart + c.W_sub.m), wd.wW eW =
        ∑ _eW ∈ Finset.Ico c.wStart (c.wStart + c.W_sub.m), (wd.φ_dec * (2 ^ c.level : ℝ)) := by
      refine Finset.sum_congr rfl fun eW heW => ?_
      rw [Finset.mem_Ico] at heW
      have heL : eW - c.wStart < c.W_sub.m := by omega
      have hweq := (W_edges_getD_comp tools H' J embJH hci heL).2.2.2.2
      change wd.wW (c.wStart + (eW - c.wStart)) = wd.φ_dec * (2 ^ c.level : ℝ) at hweq
      have hidx : c.wStart + (eW - c.wStart) = eW := by omega
      simpa [hidx] using hweq
    rw [hconst, Finset.sum_const, Nat.card_Ico]
    simp only [Nat.add_sub_cancel_left, nsmul_eq_mul]
    rw [List.getD_eq_getElem _ _ hci]
  rw [hcongr]
  exact sum_range_getD_real wd.comps defaultCompInfo
    (fun c => (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)))

theorem comp_W_m_mul_weight_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length) :
    let wd := buildWitness tools H' J embJH
    let c := wd.comps[ci]'hci
    (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)) ≤ wd.c_deg * (c.J_sub.m : ℝ) := by
  intro wd c
  rcases hw.comp_props ci hci with
    ⟨_, _, _, _, _, hJn, hJvalid, _, _, _, _, hWn, hWvalid, _, _, _, _, hdegSand, _⟩
  have hφ : 0 < wd.φ_dec := hw.φ_dec_pos
  have h2W : (2 * (c.W_sub.m : ℝ)) = ∑ k ∈ Finset.range c.X.card, (c.W_sub.deg k : ℝ) := by
    have hvol := vol_verts_eq_two_mul_m hWvalid
    have hnat : 2 * c.W_sub.m = ∑ k ∈ Finset.range c.X.card, c.W_sub.deg k := by
      rw [← hvol]; unfold Graph.vol Graph.volIn Graph.deg; rw [Graph.verts, hWn]
    exact_mod_cast hnat
  have h2J : (2 * (c.J_sub.m : ℝ)) = ∑ k ∈ Finset.range c.X.card, (c.J_sub.deg k : ℝ) := by
    have hvol := vol_verts_eq_two_mul_m hJvalid
    have hnat : 2 * c.J_sub.m = ∑ k ∈ Finset.range c.X.card, c.J_sub.deg k := by
      rw [← hvol]; unfold Graph.vol Graph.volIn Graph.deg; rw [Graph.verts, hJn]
    exact_mod_cast hnat
  have hsum_le : (2 * (c.W_sub.m : ℝ)) ≤
      wd.c_deg * (2 * (c.J_sub.m : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
    rw [h2W]
    calc ∑ k ∈ Finset.range c.X.card, (c.W_sub.deg k : ℝ)
        ≤ ∑ k ∈ Finset.range c.X.card,
            wd.c_deg * ((c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ))) :=
          Finset.sum_le_sum fun k hk => (hdegSand k (Finset.mem_range.mp hk)).2
      _ = wd.c_deg * ((∑ k ∈ Finset.range c.X.card, (c.J_sub.deg k : ℝ)) /
            (wd.φ_dec * (2 ^ c.level : ℝ))) := by
          rw [← Finset.mul_sum]; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
      _ = wd.c_deg * (2 * (c.J_sub.m : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
          rw [h2J]; ring
  have hmul : (2 * (c.W_sub.m : ℝ)) * (wd.φ_dec * (2 ^ c.level : ℝ)) ≤
      wd.c_deg * (2 * (c.J_sub.m : ℝ)) :=
    (le_div_iff₀ (by positivity)).mp hsum_le
  linarith

theorem sum_wW_comp_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m, wd.wW eW ≤ wd.c_deg * (J.m : ℝ) := by
  intro wd
  rw [sum_Ico_wW_eq tools H' J embJH hw]
  rw [← sum_range_getD_real wd.comps defaultCompInfo
      (fun c => (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)))]
  have hle1 : ∑ ci ∈ Finset.range wd.comps.length,
      ((wd.comps.getD ci defaultCompInfo).W_sub.m : ℝ) *
        (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) ≤
      ∑ ci ∈ Finset.range wd.comps.length,
        wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) := by
    refine Finset.sum_le_sum fun ci hci_r => ?_
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    rw [List.getD_eq_getElem _ _ hci]
    exact comp_W_m_mul_weight_le tools H' J embJH hw hci
  have heq2 : ∑ ci ∈ Finset.range wd.comps.length,
      wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) =
      wd.c_deg * (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)]
  have hjm : wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m :=
    sum_comp_j_m_le tools H' J embJH hw
  have hstrip : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
  have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
  have hsum_jm : (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) ≤ (J.m : ℝ) :=
    Nat.cast_le.mpr (le_trans (Nat.le_add_left _ _) (le_trans hjm hstrip))
  exact le_trans hle1 (by rw [heq2]; exact mul_le_mul_of_nonneg_left hsum_jm hc)

theorem sum_wW_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    ∑ eW ∈ Finset.range wd.W.m, wd.wW eW ≤ wd.c_deg * (J.m : ℝ) := by
  intro wd
  have hj0_le_Wm : wd.j0Edges.length ≤ wd.W.m := by
    rw [hw.W_m_eq]; exact Nat.le_add_right _ _
  rw [← Finset.sum_range_add_sum_Ico wd.wW hj0_le_Wm]
  have h1 : ∑ eW ∈ Finset.range wd.j0Edges.length, wd.wW eW =
      (wd.j0Edges.length : ℝ) * wd.φ_dec := by
    have hcongr : ∑ eW ∈ Finset.range wd.j0Edges.length, wd.wW eW =
        ∑ _eW ∈ Finset.range wd.j0Edges.length, wd.φ_dec := by
      refine Finset.sum_congr rfl fun eW heW => ?_
      exact (W_edges_getD_j0 tools H' J embJH (Finset.mem_range.mp heW)).2.2.2
    rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1_le : (wd.j0Edges.length : ℝ) * wd.φ_dec ≤ wd.c_deg * (wd.j0Edges.length : ℝ) := by
    have hφc : wd.φ_dec ≤ wd.c_deg := le_trans hw.φ_dec_le hw.c_deg_ge
    nlinarith
  have h2 : ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m, wd.wW eW ≤
      wd.c_deg * (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) := by
    rw [sum_Ico_wW_eq tools H' J embJH hw, ← sum_range_getD_real wd.comps defaultCompInfo
      (fun c => (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)))]
    have hle1 : ∑ ci ∈ Finset.range wd.comps.length,
        ((wd.comps.getD ci defaultCompInfo).W_sub.m : ℝ) *
          (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) ≤
        ∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) := by
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      rw [List.getD_eq_getElem _ _ hci]
      exact comp_W_m_mul_weight_le tools H' J embJH hw hci
    have heq2 : ∑ ci ∈ Finset.range wd.comps.length,
        wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) =
        wd.c_deg * (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, ← Nat.cast_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)]
    exact le_trans hle1 (le_of_eq heq2)
  have hjm : wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m :=
    sum_comp_j_m_le tools H' J embJH hw
  have hstrip : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
  have hsum_real : ((wd.j0Edges.length : ℝ) + (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ)) ≤
      (J.m : ℝ) := by
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr (le_trans hjm hstrip)
  have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
  calc ∑ eW ∈ Finset.range wd.j0Edges.length, wd.wW eW +
        ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m, wd.wW eW
      ≤ wd.c_deg * (wd.j0Edges.length : ℝ) +
          wd.c_deg * (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) :=
        add_le_add (by rw [h1]; exact h1_le) h2
    _ = wd.c_deg * ((wd.j0Edges.length : ℝ) + (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ)) := by
        ring
    _ ≤ wd.c_deg * (J.m : ℝ) := mul_le_mul_of_nonneg_left hsum_real hc

theorem W_m_comp_le_m {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    ((wd.W.m - wd.j0Edges.length : ℕ) : ℝ) ≤ wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec) := by
  intro wd
  have hφ := hw.φ_dec_pos
  have hWeq : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := hw.W_m_eq
  have hsub_eq : wd.W.m - wd.j0Edges.length = (wd.comps.map fun c => c.W_sub.m).sum := by
    rw [hWeq]; exact Nat.add_sub_cancel_left _ _
  rw [hsub_eq]
  have hcomp_le : ∀ ci (hci : ci < wd.comps.length),
      ((wd.comps[ci]'hci).W_sub.m : ℝ) * (2 * wd.φ_dec) ≤
        wd.c_deg * ((wd.comps[ci]'hci).J_sub.m : ℝ) := by
    intro ci hci
    have hpos := (hw.comp_props ci hci).1
    have h2pow : (2 : ℝ) ≤ (2 ^ (wd.comps[ci]'hci).level : ℝ) := by
      exact_mod_cast Nat.le_self_pow hpos.ne' 2
    calc ((wd.comps[ci]'hci).W_sub.m : ℝ) * (2 * wd.φ_dec)
        = ((wd.comps[ci]'hci).W_sub.m : ℝ) * (wd.φ_dec * 2) := by ring
      _ ≤ ((wd.comps[ci]'hci).W_sub.m : ℝ) * (wd.φ_dec * (2 ^ (wd.comps[ci]'hci).level : ℝ)) := by
          gcongr
      _ ≤ wd.c_deg * ((wd.comps[ci]'hci).J_sub.m : ℝ) :=
          comp_W_m_mul_weight_le tools H' J embJH hw hci
  have hsum_mul : (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ) * (2 * wd.φ_dec) ≤
      wd.c_deg * (J.m : ℝ) := by
    rw [← sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.W_sub.m),
        Nat.cast_sum, Finset.sum_mul]
    calc ∑ ci ∈ Finset.range wd.comps.length,
          ((wd.comps.getD ci defaultCompInfo).W_sub.m : ℝ) * (2 * wd.φ_dec)
        ≤ ∑ ci ∈ Finset.range wd.comps.length,
            wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) := by
          refine Finset.sum_le_sum fun ci hci_r => ?_
          have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
          rw [List.getD_eq_getElem _ _ hci]
          exact hcomp_le ci hci
      _ = wd.c_deg * (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) := by
          rw [← Finset.mul_sum, ← Nat.cast_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)]
      _ ≤ wd.c_deg * (J.m : ℝ) := by
          have hjm := sum_comp_j_m_le tools H' J embJH hw
          have hstrip := stripLoops_m_le J
          have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
          have hsum_jm : (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) ≤ (J.m : ℝ) :=
            Nat.cast_le.mpr (le_trans (Nat.le_add_left _ _) (le_trans hjm hstrip))
          exact mul_le_mul_of_nonneg_left hsum_jm hc
  exact (le_div_iff₀ (by positivity)).mpr hsum_mul

theorem W_m_le_m {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    (wd.W.m : ℝ) ≤ (J.m : ℝ) + wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec) := by
  intro wd
  have hWeq : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := hw.W_m_eq
  have hj0_le_Wm : wd.j0Edges.length ≤ wd.W.m := by rw [hWeq]; exact Nat.le_add_right _ _
  have hjm := sum_comp_j_m_le tools H' J embJH hw
  have hstrip := stripLoops_m_le J
  have hj0_le_Jm : (wd.j0Edges.length : ℝ) ≤ (J.m : ℝ) :=
    Nat.cast_le.mpr (le_trans (Nat.le_add_right _ _) (le_trans hjm hstrip))
  have hWm_eq : (wd.W.m : ℝ) = (wd.j0Edges.length : ℝ) + ((wd.W.m - wd.j0Edges.length : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_sub_cancel' hj0_le_Wm).symm
  rw [hWm_eq]
  exact add_le_add hj0_le_Jm (W_m_comp_le_m tools H' J embJH hw)

theorem W_m_le_n {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    (wd.W.m : ℝ) ≤ (J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec := by
  intro wd
  have hdec := tools.decompose.decompose_spec wd.J0_strip (stripLoops_isValid hJ) (stripLoops_isLoopless J)
  have hj0_le : wd.j0Edges.length ≤ J.n := by
    have hm0 : (wd.decomp.graphAt wd.J0_strip 0).m ≤ 2 ^ 0 * wd.J0_strip.n :=
      hdec.2.2.1 0 (Nat.zero_le _)
    have hlen0 : wd.j0Edges.length = (wd.decomp.graphAt wd.J0_strip 0).m := by
      simp [wd, buildWitness, DecomposeOutput.graphAt, Graph.m]
    have hstrip_n : wd.J0_strip.n = J.n := rfl
    omega
  set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
    (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  have hcomp_Wm : ∀ ci (hci : ci < wd.comps.length),
      ((wd.comps[ci]'hci).W_sub.m : ℝ) ≤
        wd.c_deg * ((wd.comps[ci]'hci).J_sub.m : ℝ) / (wd.φ_dec * (2 ^ (wd.comps[ci]'hci).level : ℝ)) := by
    intro ci hci
    have hφ := hw.φ_dec_pos
    rw [le_div_iff₀ (by positivity)]
    exact comp_W_m_mul_weight_le tools H' J embJH hw hci
  have hsum_comp_bound : (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ) ≤
      (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec := by
    have hsum1 : (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ) ≤
        ∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
            (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) := by
      rw [← sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.W_sub.m), Nat.cast_sum]
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      rw [List.getD_eq_getElem _ _ hci]
      exact hcomp_Wm ci hci
    rw [sum_range_getD_real wd.comps defaultCompInfo (fun c =>
      wd.c_deg * (c.J_sub.m : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)))] at hsum1
    have hmap_pair : (wd.comps.map fun c =>
        wd.c_deg * (c.J_sub.m : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ))) =
        rawComps.map fun p =>
          wd.c_deg * (((wd.decomp.graphAt wd.J0_strip p.1).inside p.2).length : ℝ) /
            (wd.φ_dec * (2 ^ p.1 : ℝ)) := by
      have hclen : wd.comps.length = rawComps.length :=
        buildComps_length tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
      refine List.ext_getElem (by simp [hclen]) fun ci h1 h2 => ?_
      have hci : ci < wd.comps.length := by simpa using h1
      have hcir : ci < rawComps.length := by simpa using h2
      have hpair := buildComps_getElem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
        wd.j0Edges.length rawComps ci hcir
      obtain ⟨_, _, hJsub_eq, _, _⟩ :=
        buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
          (wd.comps[ci]'hci) (List.getElem_mem hci)
      have hJm : (wd.comps[ci]'hci).J_sub.m =
          ((wd.decomp.graphAt wd.J0_strip (wd.comps[ci]'hci).level).inside
            (wd.comps[ci]'hci).X).length := by
        rw [hJsub_eq]; exact inducedSubgraph_m _ _
      have hlvl : (wd.comps[ci]'hci).level = (rawComps[ci]'hcir).1 := congrArg Prod.fst hpair
      have hXeq : (wd.comps[ci]'hci).X = (rawComps[ci]'hcir).2 := congrArg Prod.snd hpair
      simp only [List.getElem_map, hJm, hlvl, hXeq]
    rw [hmap_pair] at hsum1
    have hflat : (rawComps.map fun p =>
        wd.c_deg * (((wd.decomp.graphAt wd.J0_strip p.1).inside p.2).length : ℝ) /
          (wd.φ_dec * (2 ^ p.1 : ℝ))).sum =
        ∑ i' ∈ Finset.range wd.decomp.ℓ,
          ((wd.decomp.comps (i' + 1)).map fun X =>
            wd.c_deg * (((wd.decomp.graphAt wd.J0_strip (i' + 1)).inside X).length : ℝ) /
              (wd.φ_dec * (2 ^ (i' + 1) : ℝ))).sum := by
      dsimp only [rawComps]
      rw [sum_flatMap_real, ← sum_range_getD_real (List.range wd.decomp.ℓ) 0 (fun i' =>
        (((wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)).map fun p =>
          wd.c_deg * (((wd.decomp.graphAt wd.J0_strip p.1).inside p.2).length : ℝ) /
            (wd.φ_dec * (2 ^ p.1 : ℝ))).sum), List.length_range]
      refine Finset.sum_congr rfl fun i' hi' => ?_
      rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hi'), List.getElem_range]
      simp [List.map_map, Function.comp_def]
    rw [hflat] at hsum1
    have hlevel_le : ∀ i' ∈ Finset.range wd.decomp.ℓ,
        ((wd.decomp.comps (i' + 1)).map fun X =>
          wd.c_deg * (((wd.decomp.graphAt wd.J0_strip (i' + 1)).inside X).length : ℝ) /
            (wd.φ_dec * (2 ^ (i' + 1) : ℝ))).sum ≤
          wd.c_deg * (J.n : ℝ) / wd.φ_dec := by
      intro i' hi'
      have hiℓ : i' + 1 ≤ wd.decomp.ℓ := Finset.mem_range.mp hi'
      have hi0 : 0 < i' + 1 := Nat.zero_lt_succ i'
      have hpw := (hdec.2.2.2 (i' + 1) hi0 hiℓ).1
      set J_i := wd.decomp.graphAt wd.J0_strip (i' + 1)
      have hins_sum := sum_list_inside_le J_i (wd.decomp.comps (i' + 1)) (Finset.range J_i.m) hpw
        (fun X _ j hj => Finset.mem_range.mpr (mem_insideIndices.mp (List.mem_toFinset.mp hj)).1)
      rw [Finset.card_range] at hins_sum
      have hm_le : J_i.m ≤ 2 ^ (i' + 1) * J.n := hdec.2.2.1 (i' + 1) hiℓ
      have hsum_nat : ((wd.decomp.comps (i' + 1)).map fun X => (J_i.inside X).length).sum ≤
          2 ^ (i' + 1) * J.n :=
        le_trans hins_sum hm_le
      have hconst : ((wd.decomp.comps (i' + 1)).map fun X =>
          wd.c_deg * ((J_i.inside X).length : ℝ) / (wd.φ_dec * (2 ^ (i' + 1) : ℝ))).sum =
          wd.c_deg * (((wd.decomp.comps (i' + 1)).map (fun X => (J_i.inside X).length)).sum : ℝ) /
            (wd.φ_dec * (2 ^ (i' + 1) : ℝ)) := by
        rw [← sum_range_getD_real _ ∅, ← sum_range_getD_nat _ ∅, Nat.cast_sum]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [hconst]
      have hφ := hw.φ_dec_pos
      have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
      have hsum_r : (((((wd.decomp.comps (i' + 1)).map fun X => (J_i.inside X).length).sum : ℕ) : ℝ)) ≤
          (2 ^ (i' + 1) : ℝ) * (J.n : ℝ) := by exact_mod_cast hsum_nat
      calc wd.c_deg * (((((wd.decomp.comps (i' + 1)).map fun X => (J_i.inside X).length).sum : ℕ) : ℝ)) /
            (wd.φ_dec * (2 ^ (i' + 1) : ℝ))
          ≤ wd.c_deg * ((2 ^ (i' + 1) : ℝ) * (J.n : ℝ)) / (wd.φ_dec * (2 ^ (i' + 1) : ℝ)) := by
            gcongr
        _ = wd.c_deg * (J.n : ℝ) / wd.φ_dec := by
            have hpow_ne : (2 ^ (i' + 1) : ℝ) ≠ 0 := by positivity
            field_simp [hpow_ne]
    calc (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ)
        ≤ ∑ i' ∈ Finset.range wd.decomp.ℓ,
            ((wd.decomp.comps (i' + 1)).map fun X =>
              wd.c_deg * (((wd.decomp.graphAt wd.J0_strip (i' + 1)).inside X).length : ℝ) /
                (wd.φ_dec * (2 ^ (i' + 1) : ℝ))).sum := hsum1
      _ ≤ ∑ _i' ∈ Finset.range wd.decomp.ℓ, (wd.c_deg * (J.n : ℝ) / wd.φ_dec) :=
          Finset.sum_le_sum hlevel_le
      _ = (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hWm : (wd.W.m : ℝ) = (wd.j0Edges.length : ℝ) + (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ) := by
    exact_mod_cast hw.W_m_eq
  rw [hWm]
  exact add_le_add (by exact_mod_cast hj0_le) hsum_comp_bound

theorem sum_comps_card_le_n {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (_hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    (wd.comps.map fun c => c.X.card).sum ≤ wd.decomp.ℓ * J.n := by
  intro wd
  have hdec := tools.decompose.decompose_spec wd.J0_strip (stripLoops_isValid hJ) (stripLoops_isLoopless J)
  set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
    (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  have hmap : (wd.comps.map fun c => c.X.card) = rawComps.map fun p => p.2.card := by
    have hclen : wd.comps.length = rawComps.length :=
      buildComps_length tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
    refine List.ext_getElem (by simp [hclen]) fun ci h1 h2 => ?_
    have hci : ci < wd.comps.length := by simpa using h1
    have hcir : ci < rawComps.length := by simpa using h2
    have hpair := buildComps_getElem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
      wd.j0Edges.length rawComps ci hcir
    have hX : (wd.comps[ci]'hci).X = (rawComps[ci]'hcir).2 := congrArg Prod.snd hpair
    simp only [List.getElem_map, hX]
  rw [hmap]
  dsimp only [rawComps]
  rw [sum_flatMap_nat, ← sum_range_getD_nat (List.range wd.decomp.ℓ) 0
    (fun i' => (((wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)).map fun p => p.2.card).sum),
    List.length_range]
  have hcongr : ∑ i' ∈ Finset.range wd.decomp.ℓ,
      ((((wd.decomp.comps ((List.range wd.decomp.ℓ).getD i' 0 + 1)).map fun X =>
        ((List.range wd.decomp.ℓ).getD i' 0 + 1, X)).map fun p => p.2.card).sum) =
      ∑ i' ∈ Finset.range wd.decomp.ℓ, ((wd.decomp.comps (i' + 1)).map Finset.card).sum := by
    refine Finset.sum_congr rfl fun i' hi' => ?_
    rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hi'), List.getElem_range]
    simp [List.map_map, Function.comp_def]
  rw [hcongr]
  calc ∑ i' ∈ Finset.range wd.decomp.ℓ, ((wd.decomp.comps (i' + 1)).map Finset.card).sum
      ≤ ∑ _i' ∈ Finset.range wd.decomp.ℓ, J.n := by
        refine Finset.sum_le_sum fun i' hi' => ?_
        have hiℓ : i' + 1 ≤ wd.decomp.ℓ := Finset.mem_range.mp hi'
        have hi0 : 0 < i' + 1 := Nat.zero_lt_succ i'
        have hdi := hdec.2.2.2 (i' + 1) hi0 hiℓ
        have hpw : (wd.decomp.comps (i' + 1)).Pairwise Disjoint := hdi.1
        have hsub : ∀ X ∈ wd.decomp.comps (i' + 1), X ⊆ J.verts := fun X hX => by
          simpa [wd, buildWitness, stripLoops, Graph.verts] using (hdi.2.1 X hX).1
        have hcard := sum_list_card_le (wd.decomp.comps (i' + 1)) J.verts hpw hsub
        simpa [Graph.verts, Finset.card_range] using hcard
    _ = wd.decomp.ℓ * J.n := by simp [Finset.sum_const, smul_eq_mul]

theorem sum_comps_card_le_m {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    (wd.comps.map fun c => c.X.card).sum ≤ 2 * J.m := by
  intro wd
  have hcomp : ∀ ci (hci : ci < wd.comps.length),
      (wd.comps[ci]'hci).X.card ≤ 2 * (wd.comps[ci]'hci).J_sub.m := by
    intro ci hci
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, hJn, hJvalid, _, _, hJdeg_pos, _⟩
    have hvol : (wd.comps[ci]'hci).J_sub.vol (wd.comps[ci]'hci).J_sub.verts =
        2 * (wd.comps[ci]'hci).J_sub.m := vol_verts_eq_two_mul_m hJvalid
    have hle : (wd.comps[ci]'hci).X.card ≤
        (wd.comps[ci]'hci).J_sub.vol (wd.comps[ci]'hci).J_sub.verts := by
      unfold Graph.vol Graph.volIn
      rw [Graph.verts, hJn]
      calc (wd.comps[ci]'hci).X.card
          = ∑ _k ∈ Finset.range (wd.comps[ci]'hci).X.card, 1 := by simp
        _ ≤ ∑ k ∈ Finset.range (wd.comps[ci]'hci).X.card,
              (wd.comps[ci]'hci).J_sub.degIn (Finset.range (wd.comps[ci]'hci).X.card) k :=
            Finset.sum_le_sum fun k hk => by
              simpa [Graph.deg, Graph.verts, hJn] using hJdeg_pos k (Finset.mem_range.mp hk)
    omega
  rw [← sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.X.card)]
  have hsum : ∑ ci ∈ Finset.range wd.comps.length, (wd.comps.getD ci defaultCompInfo).X.card ≤
      ∑ ci ∈ Finset.range wd.comps.length, 2 * (wd.comps.getD ci defaultCompInfo).J_sub.m := by
    refine Finset.sum_le_sum fun ci hci_r => ?_
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    rw [List.getD_eq_getElem _ _ hci]
    exact hcomp ci hci
  have heq2 : ∑ ci ∈ Finset.range wd.comps.length,
      2 * (wd.comps.getD ci defaultCompInfo).J_sub.m =
      2 * (wd.comps.map fun c => c.J_sub.m).sum := by
    rw [← Finset.mul_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)]
  have hjm := sum_comp_j_m_le tools H' J embJH hw
  have hstrip : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
  have hjm_le : (wd.comps.map fun c => c.J_sub.m).sum ≤ J.m :=
    le_trans (Nat.le_add_left _ _) (le_trans hjm hstrip)
  omega

theorem sum_comps_w_le_m {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    (wd.comps.map fun c =>
      ∑ k ∈ Finset.range c.X.card,
        ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (wd.φ_dec * (2 ^ c.level : ℝ))).sum ≤ (J.m : ℝ) / wd.φ_dec := by
  intro wd
  have hφ := hw.φ_dec_pos
  have hcomp : ∀ ci (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      (∑ k ∈ Finset.range c.X.card,
        ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (wd.φ_dec * (2 ^ c.level : ℝ))) ≤ (c.J_sub.m : ℝ) / wd.φ_dec := by
    intro ci hci c
    rcases hw.comp_props ci hci with
      ⟨hi0, _, _, _, hverts_eq, _, hJvalid, _, _, _, _, _⟩
    set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
      (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
    obtain ⟨_, _, hJsub_eq, _, _⟩ :=
      buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps c
        (List.getElem_mem hci)
    set J_i := wd.decomp.graphAt wd.J0_strip c.level
    have hsum_deg : (∑ k ∈ Finset.range c.X.card,
        (J_i.degIn c.X (c.verts.getD k 0) : ℝ)) = 2 * (c.J_sub.m : ℝ) := by
      rw [hverts_eq]
      have hin := inducedSubgraph_m J_i c.X
      rw [← hJsub_eq] at hin
      have hnat : J_i.volIn c.X c.X = 2 * c.J_sub.m := by
        rw [volIn_self_eq_two_mul_inside, hin]
      have h1 : (∑ k ∈ Finset.range c.X.card, (J_i.degIn c.X ((vertsOf c.X).getD k 0) : ℝ)) =
          (J_i.volIn c.X c.X : ℝ) := by
        rw [← Nat.cast_sum]
        congr 1
        unfold Graph.volIn
        rw [← Finset.sum_image (f := J_i.degIn c.X) (g := fun k => (vertsOf c.X).getD k 0) (by
          intro a ha b hb hab
          dsimp only at hab
          have ha' : a < c.X.card := Finset.mem_range.mp ha
          have hb' : b < c.X.card := Finset.mem_range.mp hb
          rw [← idxOf_getD_vertsOf ha', hab, idxOf_getD_vertsOf hb'])]
        congr 1
        ext v
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨fun ⟨k, hk, hv⟩ => hv ▸ getD_vertsOf_mem hk,
               fun hv => ⟨(vertsOf c.X).idxOf v, idxOf_lt_card hv, getD_vertsOf_idxOf hv⟩⟩
      rw [h1]
      exact_mod_cast hnat
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← div_eq_mul_inv, hsum_deg]
    have h2pow : (2 : ℝ) ≤ (2 ^ c.level : ℝ) := by
      exact_mod_cast Nat.le_self_pow hi0.ne' 2
    calc (2 * (c.J_sub.m : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ))
        ≤ (2 * (c.J_sub.m : ℝ)) / (wd.φ_dec * 2) :=
          div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
      _ = (c.J_sub.m : ℝ) / wd.φ_dec := by ring
  rw [← sum_range_getD_real wd.comps defaultCompInfo (fun c =>
      ∑ k ∈ Finset.range c.X.card,
        ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (wd.φ_dec * (2 ^ c.level : ℝ)))]
  have hsum : ∑ ci ∈ Finset.range wd.comps.length,
      (∑ k ∈ Finset.range (wd.comps.getD ci defaultCompInfo).X.card,
        ((wd.decomp.graphAt wd.J0_strip (wd.comps.getD ci defaultCompInfo).level).degIn
          (wd.comps.getD ci defaultCompInfo).X ((wd.comps.getD ci defaultCompInfo).verts.getD k 0) : ℝ) /
          (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ))) ≤
      ∑ ci ∈ Finset.range wd.comps.length,
        ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) / wd.φ_dec := by
    refine Finset.sum_le_sum fun ci hci_r => ?_
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    rw [List.getD_eq_getElem _ _ hci]
    exact hcomp ci hci
  refine le_trans hsum ?_
  have heq_nat : (∑ ci ∈ Finset.range wd.comps.length, (wd.comps.getD ci defaultCompInfo).J_sub.m) =
      (wd.comps.map fun c => c.J_sub.m).sum :=
    sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, heq_nat, ← div_eq_mul_inv]
  have hjm := sum_comp_j_m_le tools H' J embJH hw
  have hstrip := stripLoops_m_le J
  have hm : (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) ≤ (J.m : ℝ) :=
    Nat.cast_le.mpr (le_trans (Nat.le_add_left _ _) (le_trans hjm hstrip))
  exact div_le_div_of_nonneg_right hm hφ.le

/-! ## Walk lifting correctness for `liftJSubWalk` and `liftWSubWalk` -/

theorem liftJSubWalk_edges_length (c : CompInfo) (P : Walk) :
    (liftJSubWalk c P).edges.length = P.edges.length := by
  simp [liftJSubWalk]

theorem mem_edges_liftJSubWalk {c : CompInfo} {P : Walk} {eJ : ℕ} :
    eJ ∈ (liftJSubWalk c P).edges ↔ ∃ jL ∈ P.edges, c.jSubOrigEdges.getD jL 0 = eJ := by
  simp [liftJSubWalk]

theorem liftJSubWalk_verts_nodup {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length)
    {P : Walk} (hP_nodup : P.verts.Nodup)
    (hP_lt : ∀ x ∈ P.verts, x < ((buildWitness tools H' J embJH).comps[ci]'hci).X.card) :
    (liftJSubWalk ((buildWitness tools H' J embJH).comps[ci]'hci) P).verts.Nodup := by
  set c := (buildWitness tools H' J embJH).comps[ci]'hci
  rcases hw.comp_props ci hci with ⟨_, _, _, _, hverts_eq, _⟩
  simp only [liftJSubWalk]
  rw [List.nodup_map_iff_inj_on hP_nodup]
  intro a ha b hb hab
  have ha' : a < c.X.card := hP_lt a ha
  have hb' : b < c.X.card := hP_lt b hb
  rw [hverts_eq] at hab
  rw [← idxOf_getD_vertsOf ha', hab, idxOf_getD_vertsOf hb']

theorem isWalk_liftJSubWalk {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci u' v' : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length)
    {P : Walk} (hP : P.IsWalk ((buildWitness tools H' J embJH).comps[ci]'hci).J_sub u' v') :
    let wd := buildWitness tools H' J embJH
    let c := wd.comps[ci]'hci
    (liftJSubWalk c P).IsWalk J (c.verts.getD u' 0) (c.verts.getD v' 0) := by
  intro wd c
  set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
    (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  obtain ⟨_, hverts_eq, hJsub_eq, hjOrig_eq, _⟩ :=
    buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps c
      (List.getElem_mem hci)
  rcases hw.comp_props ci hci with
    ⟨_, _, hXJ, _, _, hJn, hJvalid, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, _, hjLt, _⟩
  have hu' : u' < c.X.card := by simpa [hJn] using hP.1
  have hv' : v' < c.X.card := by simpa [hJn] using hP.2.1
  have huJ : c.verts.getD u' 0 < J.n := by
    rw [hverts_eq]; exact Finset.mem_range.mp (hXJ (getD_vertsOf_mem hu'))
  have hvJ : c.verts.getD v' 0 < J.n := by
    rw [hverts_eq]; exact Finset.mem_range.mp (hXJ (getD_vertsOf_mem hv'))
  refine ⟨huJ, hvJ, ?_⟩
  rcases hP.2.2 with ⟨hPv, hPe, rfl⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩
  · exact Or.inl ⟨by simp [liftJSubWalk, hPv], by simp [liftJSubWalk, hPe], rfl⟩
  · refine Or.inr ⟨by simpa [liftJSubWalk] using hne, by simp [liftJSubWalk, hlen],
      by simp [liftJSubWalk, List.head?_map, hhead], by simp [liftJSubWalk, List.getLast?_map, hlast],
      ?_, ?_⟩
    · intro j hj
      rw [mem_edges_liftJSubWalk] at hj
      rcases hj with ⟨jL, hjL, rfl⟩
      have hjL_m : jL < c.J_sub.m := hedges jL hjL
      have hjL_len : jL < c.jSubOrigEdges.length := by rw [hjLen]; exact hjL_m
      rw [List.getD_eq_getElem _ _ hjL_len]
      exact hjLt _ (List.getElem_mem hjL_len)
    · intro i hi
      simp only [liftJSubWalk, List.length_map] at hi ⊢
      have hjL_m : P.edges.getD i 0 < c.J_sub.m := by
        rw [List.getD_eq_getElem _ _ hi]; exact hedges _ (List.getElem_mem hi)
      set jL := P.edges.getD i 0
      set J_i := wd.decomp.graphAt wd.J0_strip c.level
      have hidx_m : jL < (insideIndices J_i c.X).length := by
        have hm := inducedSubgraph_m J_i c.X
        have hlen := congrArg List.length (insideIndices_map_eq_inside J_i c.X)
        rw [List.length_map] at hlen
        rw [hJsub_eq] at hjL_m
        omega
      set a := (insideIndices J_i c.X)[jL]'hidx_m
      have ha_mem := mem_insideIndices.mp (List.getElem_mem hidx_m)
      have hlen_Ji : (wd.decomp.edgesAt wd.J0_strip c.level).length = J_i.m := by
        simp [J_i, DecomposeOutput.graphAt, Graph.m]
      have ha_ed_len : a < (wd.decomp.edgesAt wd.J0_strip c.level).length := by
        rw [hlen_Ji]; exact ha_mem.1
      set b := (wd.decomp.edgesAt wd.J0_strip c.level)[a]'ha_ed_len
      have hb_mem : b ∈ wd.decomp.edgesAt wd.J0_strip c.level := List.getElem_mem ha_ed_len
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb_mem
      have hnl_len : wd.nlIdx.length = wd.J0_strip.m := by
        simp [wd, buildWitness, stripLoops, Graph.m]
      have hb_nl : b < wd.nlIdx.length := by omega
      have hOrig_ed : J.edges.getD (c.jSubOrigEdges.getD jL 0) (0, 0) = J_i.edges.getD a (0, 0) := by
        have hjOrig_getD : c.jSubOrigEdges.getD jL 0 = wd.nlIdx[b]'hb_nl := by
          rw [hjOrig_eq, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hidx_m),
              List.getElem_map]
          change wd.nlIdx.getD ((wd.decomp.edgesAt wd.J0_strip c.level).getD a 0) 0 = _
          rw [List.getD_eq_getElem _ _ ha_ed_len, List.getD_eq_getElem _ _ hb_nl]
        rw [hjOrig_getD]
        have ha_ed' : a < ((wd.decomp.edgesAt wd.J0_strip c.level).map
            (fun j => wd.J0_strip.edges.getD j (0, 0))).length := by
          rw [List.length_map]; exact ha_ed_len
        have hb_ed' : b < ((nonloopIndices J).map fun j => J.edges.getD j (0, 0)).length := by
          rw [List.length_map]; simpa [wd, buildWitness] using hb_nl
        simp only [J_i, DecomposeOutput.graphAt]
        rw [List.getD_eq_getElem _ _ ha_ed', List.getElem_map]
        change J.edges.getD (wd.nlIdx[b]'hb_nl) (0, 0) = wd.J0_strip.edges.getD b (0, 0)
        change J.edges.getD (wd.nlIdx[b]'hb_nl) (0, 0) =
          ((nonloopIndices J).map fun j => J.edges.getD j (0, 0)).getD b (0, 0)
        rw [List.getD_eq_getElem _ _ hb_ed', List.getElem_map]
        rfl
      have hSub_ed : c.J_sub.edges.getD jL (0, 0) =
          ((vertsOf c.X).idxOf (J_i.edges.getD a (0, 0)).1,
           (vertsOf c.X).idxOf (J_i.edges.getD a (0, 0)).2) := by
        rw [hJsub_eq]
        have hjL_ind : jL < (inducedSubgraph J_i c.X).edges.length := by
          simpa [inducedSubgraph, Graph.m] using hidx_m
        rw [List.getD_eq_getElem _ _ hjL_ind]
        simp only [inducedSubgraph, List.getElem_map]
        rw [List.getD_eq_getElem _ _ ha_mem.1]
      have hjL_eq : P.edges[i]'hi = jL := (List.getD_eq_getElem _ _ hi).symm
      have hmap_e : (P.edges.map fun b => c.jSubOrigEdges.getD b 0).getD i 0 =
          c.jSubOrigEdges.getD jL 0 := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, hjL_eq]
      have hmap_v1 : (P.verts.map fun k => c.verts.getD k 0).getD i 0 =
          c.verts.getD (P.verts.getD i 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega : i < P.verts.length), List.getElem_map]
      have hmap_v2 : (P.verts.map fun k => c.verts.getD k 0).getD (i + 1) 0 =
          c.verts.getD (P.verts.getD (i + 1) 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega : i + 1 < P.verts.length), List.getElem_map]
      rw [hmap_e, hmap_v1, hmap_v2, hOrig_ed]
      have hsub := hstep i hi
      rw [hSub_ed] at hsub
      rcases hsub with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
      · left
        rw [hverts_eq]
        exact ⟨by rw [← ha1, getD_vertsOf_idxOf ha_mem.2.1],
               by rw [← ha2, getD_vertsOf_idxOf ha_mem.2.2]⟩
      · right
        rw [hverts_eq]
        exact ⟨by rw [← ha1, getD_vertsOf_idxOf ha_mem.2.2],
               by rw [← ha2, getD_vertsOf_idxOf ha_mem.2.1]⟩

theorem liftWSubWalk_edges_length (c : CompInfo) (P : Walk) :
    (liftWSubWalk c P).edges.length = P.edges.length := by
  simp [liftWSubWalk]

theorem mem_edges_liftWSubWalk {c : CompInfo} {P : Walk} {eW : ℕ} :
    eW ∈ (liftWSubWalk c P).edges ↔ ∃ eL ∈ P.edges, c.wStart + eL = eW := by
  simp [liftWSubWalk]

theorem liftWSubWalk_verts_nodup {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length)
    {P : Walk} (hP_nodup : P.verts.Nodup)
    (hP_lt : ∀ x ∈ P.verts, x < ((buildWitness tools H' J embJH).comps[ci]'hci).X.card) :
    (liftWSubWalk ((buildWitness tools H' J embJH).comps[ci]'hci) P).verts.Nodup := by
  set c := (buildWitness tools H' J embJH).comps[ci]'hci
  rcases hw.comp_props ci hci with ⟨_, _, _, _, hverts_eq, _⟩
  simp only [liftWSubWalk]
  rw [List.nodup_map_iff_inj_on hP_nodup]
  intro a ha b hb hab
  have ha' : a < c.X.card := hP_lt a ha
  have hb' : b < c.X.card := hP_lt b hb
  rw [hverts_eq] at hab
  rw [← idxOf_getD_vertsOf ha', hab, idxOf_getD_vertsOf hb']

theorem isWalk_liftWSubWalk {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci u' v' : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length)
    {P : Walk} (hP : P.IsWalk ((buildWitness tools H' J embJH).comps[ci]'hci).W_sub u' v') :
    let wd := buildWitness tools H' J embJH
    let c := wd.comps[ci]'hci
    (liftWSubWalk c P).IsWalk wd.W (c.verts.getD u' 0) (c.verts.getD v' 0) := by
  intro wd c
  rcases hw.comp_props ci hci with
    ⟨_, _, hXJ, _, hverts_eq, _, _, _, _, _, _, hWn, hWvalid, _, _, _, _, _, _, _, _, _, _, hwEnd⟩
  have hu' : u' < c.X.card := by simpa [hWn] using hP.1
  have hv' : v' < c.X.card := by simpa [hWn] using hP.2.1
  have huW : c.verts.getD u' 0 < wd.W.n := by
    rw [hw.W_n, hverts_eq]; exact Finset.mem_range.mp (hXJ (getD_vertsOf_mem hu'))
  have hvW : c.verts.getD v' 0 < wd.W.n := by
    rw [hw.W_n, hverts_eq]; exact Finset.mem_range.mp (hXJ (getD_vertsOf_mem hv'))
  refine ⟨huW, hvW, ?_⟩
  rcases hP.2.2 with ⟨hPv, hPe, rfl⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩
  · exact Or.inl ⟨by simp [liftWSubWalk, hPv], by simp [liftWSubWalk, hPe], rfl⟩
  · refine Or.inr ⟨by simpa [liftWSubWalk] using hne, by simp [liftWSubWalk, hlen],
      by simp [liftWSubWalk, List.head?_map, hhead], by simp [liftWSubWalk, List.getLast?_map, hlast],
      ?_, ?_⟩
    · intro eW heW
      rw [mem_edges_liftWSubWalk] at heW
      rcases heW with ⟨eL, heL, rfl⟩
      have heL_m : eL < c.W_sub.m := hedges eL heL
      exact (W_edges_getD_comp tools H' J embJH hci heL_m).1
    · intro i hi
      simp only [liftWSubWalk, List.length_map] at hi ⊢
      have heL_m : P.edges.getD i 0 < c.W_sub.m := by
        rw [List.getD_eq_getElem _ _ hi]; exact hedges _ (List.getElem_mem hi)
      set eL := P.edges.getD i 0
      have heL_eq : P.edges[i]'hi = eL := (List.getD_eq_getElem _ _ hi).symm
      have hWe := (W_edges_getD_comp tools H' J embJH hci heL_m).2.2.1
      have hmap_e : (P.edges.map fun b => c.wStart + b).getD i 0 = c.wStart + eL := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, heL_eq]
      have hmap_v1 : (P.verts.map fun k => c.verts.getD k 0).getD i 0 =
          c.verts.getD (P.verts.getD i 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega : i < P.verts.length), List.getElem_map]
      have hmap_v2 : (P.verts.map fun k => c.verts.getD k 0).getD (i + 1) 0 =
          c.verts.getD (P.verts.getD (i + 1) 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega : i + 1 < P.verts.length), List.getElem_map]
      rw [hmap_e, hmap_v1, hmap_v2, hWe]
      rcases hstep i hi with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
      · left
        exact ⟨congrArg (fun k => c.verts.getD k 0) ha1, congrArg (fun k => c.verts.getD k 0) ha2⟩
      · right
        exact ⟨congrArg (fun k => c.verts.getD k 0) ha1, congrArg (fun k => c.verts.getD k 0) ha2⟩

end MinCostFlow.Spanner
