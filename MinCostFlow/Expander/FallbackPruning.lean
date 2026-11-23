module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import MinCostFlow.Expander.GraphHelpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Greedy Strong-Expander Pruning & BFS Diameter Fallback for `PathDSTool`

When `[CS21]` cannot be initialized directly at `φ_in` (specifically, when a small component has
`φ_in < 10 * csPhi Kγ c (3 * G.m)` so `[CS21]`'s internal conductance exceeds `φ_in`), we maintain
a greedy strong `(φ_in / 6)`-expander pruning `S ⊆ V(G)` together with a volume-growth BFS query
returning a simple `u`-`v` walk in `G[V \ S] \ deleted` of length
`≤ 25 * (Real.log (2 * M + 2) + 1) / φ_in`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner

@[expose] public section

/-- Graph `G` after removing edge indices in `D : Finset ℕ`. -/
def graphAfterDelSet (G : Cited.Graph) (D : Finset ℕ) : Cited.Graph :=
  ⟨G.n, ((List.range G.m).filter fun j => j ∉ D).map fun j => G.edges.getD j (0, 0)⟩

/-- Strong `ψ`-expander condition on `(G \ D)[V \ S]` with respect to `G`. -/
def IsStrongExpanderSet (G : Cited.Graph) (D S : Finset ℕ) (ψ : ℝ) : Prop :=
  let U := G.verts \ S
  ∀ A ⊆ U, A.Nonempty → A ≠ U →
    ψ * min (G.vol A : ℝ) (G.vol (U \ A) : ℝ) ≤ ((graphAfterDelSet G D).cutIn U A : ℝ)

/-- Invariant for greedy pruning below the `[CS21]` fallback threshold (`vol(S) ≤ 6/5 · t / φ_in`). -/
def PruneInv (G : Cited.Graph) (D : Finset ℕ) (φ_in : ℝ) (S : Finset ℕ) : Prop :=
  S ⊆ G.verts ∧
  ((graphAfterDelSet G D).cut S : ℝ) ≤ (φ_in / 6) * (G.vol S : ℝ) ∧
  (G.vol S : ℝ) ≤ (6 / 5 : ℝ) * (D.card : ℝ) / φ_in

/-- Complete invariant maintained by fallback state transitions on `(D, S)`. -/
def FallbackInv (φ_in : ℝ) (G : Cited.Graph) (D S : Finset ℕ) : Prop :=
  S ⊆ G.verts ∧
  (G.vol S : ℝ) ≤ 7 * (D.card : ℝ) / φ_in ∧
  IsStrongExpanderSet G D S (φ_in / 6) ∧
  ((2 : ℝ) * (G.m : ℝ) ≤ 7 * (D.card : ℝ) / φ_in → S = G.verts) ∧
  (¬ (2 : ℝ) * (G.m : ℝ) ≤ 7 * (D.card : ℝ) / φ_in → PruneInv G D φ_in S)

end

section

private lemma getD_mem_edges_of_lt {G : Cited.Graph} {j : ℕ} (hj : j < G.m) :
    G.edges.getD j (0, 0) ∈ G.edges := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

private lemma getD_valid_of_lt {G : Cited.Graph} (hV : G.IsValid) {j : ℕ} (hj : j < G.m) :
    (G.edges.getD j (0, 0)).1 < G.n ∧ (G.edges.getD j (0, 0)).2 < G.n :=
  hV _ (getD_mem_edges_of_lt hj)

private lemma edges_eq_map_range (L : List (ℕ × ℕ)) :
    ((List.range L.length).map fun j => L.getD j (0, 0)) = L := by
  induction L with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero]
    congr 1

private lemma graph_sum_map_eq_range (G : Cited.Graph) (f : ℕ × ℕ → ℕ) :
    (G.edges.map f).sum =
      ((List.range G.m).map fun j => f (G.edges.getD j (0, 0))).sum := by
  have h : G.edges = (List.range G.m).map fun j => G.edges.getD j (0, 0) :=
    (edges_eq_map_range G.edges).symm
  conv_lhs => rw [h, List.map_map]
  rfl

private lemma graphAfterDelSet_isValid {G : Cited.Graph} (hV : G.IsValid) (D : Finset ℕ) :
    (graphAfterDelSet G D).IsValid := by
  intro e he
  simp only [graphAfterDelSet, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at he
  rcases he with ⟨j, ⟨hj, _⟩, rfl⟩
  exact getD_valid_of_lt hV hj

private lemma fb_sum_map_filter {α : Type*} (l : List α) (p : α → Bool) (g : α → ℕ) :
    ((l.filter p).map g).sum = (l.map fun x => if p x then g x else 0).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    cases hpa : p a <;> simp [hpa, ih]

private lemma graphAfterDelSet_sum_map (G : Cited.Graph) (D : Finset ℕ) (f : ℕ × ℕ → ℕ) :
    ((graphAfterDelSet G D).edges.map f).sum =
      ((List.range G.m).map fun j =>
        if j ∈ D then 0 else f (G.edges.getD j (0, 0))).sum := by
  dsimp only [graphAfterDelSet]
  rw [List.map_map, fb_sum_map_filter]
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j ∈ D <;> simp [hj]

private lemma graphAfterDelSet_cut_sum (G : Cited.Graph) (hV : G.IsValid) (D S : Finset ℕ) :
    (graphAfterDelSet G D).cut S =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        if j ∈ D then 0 else if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum := by
  unfold Cited.Graph.cut
  rw [cutIn_eq_sum_map, inside_verts_of_isValid (graphAfterDelSet_isValid hV D)]
  exact graphAfterDelSet_sum_map G D _

private lemma graphAfterDelSet_cutIn_sum (G : Cited.Graph)
    (D U A : Finset ℕ) (_hU : U ⊆ G.verts) :
    (graphAfterDelSet G D).cutIn U A =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        if j ∈ D then 0
        else if (e.1 ∈ U ∧ e.2 ∈ U ∧ (decide (e.1 ∈ A) != decide (e.2 ∈ A))) then 1 else 0).sum := by
  rw [cutIn_eq_sum_map]
  dsimp only [Cited.Graph.inside]
  rw [fb_sum_map_filter, graphAfterDelSet_sum_map]
  congr 1
  apply List.map_congr_left
  intro j _
  set p := G.edges.getD j (0, 0)
  by_cases hj : j ∈ D
  · simp [hj]
  · by_cases h1 : p.1 ∈ U
    · by_cases h2 : p.2 ∈ U <;> simp [hj, h1, h2]
    · simp [hj, h1]

private lemma graph_cut_sum (G : Cited.Graph) (hV : G.IsValid) (S : Finset ℕ) :
    G.cut S =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum := by
  unfold Cited.Graph.cut
  rw [cutIn_eq_sum_map, inside_verts_of_isValid hV]
  exact graph_sum_map_eq_range G _

private lemma graph_vol_sum (G : Cited.Graph) (hV : G.IsValid) (S : Finset ℕ) :
    G.vol S =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0)).sum := by
  unfold Cited.Graph.vol
  rw [volIn_eq_sum_map, inside_verts_of_isValid hV]
  exact graph_sum_map_eq_range G _

private lemma fb_sum_map_le {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private lemma fb_sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private lemma cut_afterDelSet_union_le {G : Cited.Graph} (hV : G.IsValid) (D S A : Finset ℕ)
    (_hS : S ⊆ G.verts) (_hA : A ⊆ G.verts \ S) :
    (graphAfterDelSet G D).cut (S ∪ A) ≤
      (graphAfterDelSet G D).cut S + (graphAfterDelSet G D).cutIn (G.verts \ S) A := by
  rw [graphAfterDelSet_cut_sum G hV D (S ∪ A), graphAfterDelSet_cut_sum G hV D S,
    graphAfterDelSet_cutIn_sum G D (G.verts \ S) A Finset.sdiff_subset, ← fb_sum_map_add]
  apply fb_sum_map_le
  intro j hj
  rw [List.mem_range] at hj
  have hv := getD_valid_of_lt hV hj
  set e := G.edges.getD j (0, 0)
  have he1 : e.1 ∈ G.verts := by simp [Cited.Graph.verts, hv.1]
  have he2 : e.2 ∈ G.verts := by simp [Cited.Graph.verts, hv.2]
  by_cases hjD : j ∈ D
  · simp [hjD]
  · simp only [hjD, ↓reduceIte]
    by_cases h1S : e.1 ∈ S <;> by_cases h2S : e.2 ∈ S <;>
      by_cases h1A : e.1 ∈ A <;> by_cases h2A : e.2 ∈ A <;>
      simp [Finset.mem_union, Finset.mem_sdiff, he1, he2, h1S, h2S, h1A, h2A]

private lemma cut_le_afterDelSet_add_card {G : Cited.Graph} (hV : G.IsValid)
    (D S : Finset ℕ) :
    G.cut S ≤ (graphAfterDelSet G D).cut S + D.card := by
  rw [graph_cut_sum G hV S, graphAfterDelSet_cut_sum G hV D S]
  have hsum_le : ((List.range G.m).map fun j =>
      let e := G.edges.getD j (0, 0)
      if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum ≤
      ((List.range G.m).map fun j =>
        (let e := G.edges.getD j (0, 0)
         if j ∈ D then 0 else if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0) +
        (if j ∈ D then 1 else 0)).sum := by
    apply fb_sum_map_le
    intro j _
    by_cases hj : j ∈ D <;> simp [hj]
    split_ifs <;> omega
  rw [fb_sum_map_add] at hsum_le
  have hD_le : ((List.range G.m).map fun j => if j ∈ D then (1 : ℕ) else 0).sum ≤ D.card := by
    have hfilt : ((List.range G.m).map fun j => if j ∈ D then (1 : ℕ) else 0).sum =
        ((List.range G.m).filter fun j => decide (j ∈ D)).length := by
      induction List.range G.m with
      | nil => simp
      | cons a as ih =>
        by_cases ha : a ∈ D
        · simp [ha, ih]; omega
        · simp [ha, ih]
    rw [hfilt]
    have hsub : ((List.range G.m).filter fun j => decide (j ∈ D)).toFinset ⊆ D := by
      intro x hx
      rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
      exact hx.2
    have hnd : ((List.range G.m).filter fun j => decide (j ∈ D)).Nodup :=
      List.nodup_range.filter _
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card hsub
  omega

private lemma cut_afterDelSet_mono {G : Cited.Graph} (hV : G.IsValid)
    {D₁ D₂ : Finset ℕ} (hD : D₁ ⊆ D₂) (S : Finset ℕ) :
    (graphAfterDelSet G D₂).cut S ≤ (graphAfterDelSet G D₁).cut S := by
  rw [graphAfterDelSet_cut_sum G hV D₂ S, graphAfterDelSet_cut_sum G hV D₁ S]
  apply fb_sum_map_le
  intro j _
  by_cases hj1 : j ∈ D₁
  · have hj2 : j ∈ D₂ := hD hj1
    simp [hj1, hj2]
  · by_cases hj2 : j ∈ D₂
    · simp [hj1, hj2]
    · simp [hj1, hj2]

private lemma cutIn_symm (H : Cited.Graph) (U A : Finset ℕ) (_hAU : A ⊆ U) :
    H.cutIn U A = H.cutIn U (U \ A) := by
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map]
  congr 1
  apply List.map_congr_left
  intro e he
  have h1 : e.1 ∈ U := (mem_inside_iff.mp he).2.1
  have h2 : e.2 ∈ U := (mem_inside_iff.mp he).2.2
  have : ∀ x ∈ U, (decide (x ∈ U \ A) = !decide (x ∈ A)) := by
    intro x hx
    by_cases hxA : x ∈ A <;> simp [Finset.mem_sdiff, hx, hxA]
  simp only [this e.1 h1, this e.2 h2]
  cases decide (e.1 ∈ A) <;> cases decide (e.2 ∈ A) <;> rfl

private lemma vol_union_disjoint (G : Cited.Graph) {S A : Finset ℕ} (hdisj : Disjoint S A) :
    G.vol (S ∪ A) = G.vol S + G.vol A :=
  Finset.sum_union hdisj

private lemma vol_sdiff (G : Cited.Graph) {A S : Finset ℕ} (h : A ⊆ S) :
    G.vol S = G.vol A + G.vol (S \ A) := by
  have := Finset.sum_sdiff h (f := G.degIn G.verts)
  unfold Cited.Graph.vol Cited.Graph.volIn
  omega

open Classical in
private noncomputable def greedyPrune (G : Cited.Graph) (D : Finset ℕ) (φ_in : ℝ) (S : Finset ℕ) :
    Finset ℕ :=
  let U := G.verts \ S
  if hBad : ∃ A ⊆ U, A.Nonempty ∧ A ≠ U ∧
      ((graphAfterDelSet G D).cutIn U A : ℝ) <
        (φ_in / 6) * min (G.vol A : ℝ) (G.vol (U \ A) : ℝ) then
    let A := Classical.choose hBad
    let A' := if G.vol A ≤ G.vol (U \ A) then A else U \ A
    if _hlt : (G.verts \ (S ∪ A')).card < (G.verts \ S).card then
      greedyPrune G D φ_in (S ∪ A')
    else S
  else S
termination_by (G.verts \ S).card
decreasing_by assumption

private lemma greedyPrune_spec (G : Cited.Graph) (D : Finset ℕ) (φ_in : ℝ)
    (hφ : 0 < φ_in) (_hφ1 : φ_in ≤ 1) (hV : G.IsValid) (hm : 1 ≤ G.m)
    (hexp : G.IsConductanceExpanderOn G.verts φ_in)
    (hbudget : ¬ (2 : ℝ) * (G.m : ℝ) ≤ 7 * (D.card : ℝ) / φ_in) :
    ∀ S : Finset ℕ, PruneInv G D φ_in S →
      let S' := greedyPrune G D φ_in S
      S ⊆ S' ∧ PruneInv G D φ_in S' ∧ IsStrongExpanderSet G D S' (φ_in / 6) := by
  classical
  intro S
  induction hn : (G.verts \ S).card using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    intro hInv
    rcases hInv with ⟨hSV, hcut_le, hvol_le⟩
    set U := G.verts \ S
    by_cases hBad : ∃ A ⊆ U, A.Nonempty ∧ A ≠ U ∧
        ((graphAfterDelSet G D).cutIn U A : ℝ) <
          (φ_in / 6) * min (G.vol A : ℝ) (G.vol (U \ A) : ℝ)
    · set A := Classical.choose hBad
      have hA_spec := Classical.choose_spec hBad
      rcases hA_spec with ⟨hAU, hAne, hAneU, hcut_bad⟩
      set A' := if G.vol A ≤ G.vol (U \ A) then A else U \ A
      have hA'U : A' ⊆ U := by
        dsimp only [A']
        split_ifs
        · exact hAU
        · exact Finset.sdiff_subset
      have hA'ne : A'.Nonempty := by
        dsimp only [A']
        split_ifs
        · exact hAne
        · refine Finset.nonempty_iff_ne_empty.mpr ?_
          intro he
          apply hAneU
          exact Finset.Subset.antisymm hAU (Finset.sdiff_eq_empty_iff_subset.mp he)
      have hA'neU : A' ≠ U := by
        dsimp only [A']
        split_ifs
        · exact hAneU
        · intro he
          rcases hAne with ⟨a, ha⟩
          have haU : a ∈ U := hAU ha
          rw [← he] at haU
          exact (Finset.mem_sdiff.mp haU).2 ha
      have hA'vol_min : G.vol A' ≤ G.vol (U \ A') := by
        dsimp only [A']
        split_ifs with hle
        · exact hle
        · have hss : U \ (U \ A) = A := Finset.sdiff_sdiff_eq_self hAU
          rw [hss]
          omega
      have hcutInA' : ((graphAfterDelSet G D).cutIn U A' : ℝ) < (φ_in / 6) * (G.vol A' : ℝ) := by
        have hmin_eq : min (G.vol A' : ℝ) (G.vol (U \ A') : ℝ) = (G.vol A' : ℝ) :=
          min_eq_left (by exact_mod_cast hA'vol_min)
        rw [← hmin_eq]
        dsimp only [A']
        split_ifs with hle
        · exact hcut_bad
        · have hss : U \ (U \ A) = A := Finset.sdiff_sdiff_eq_self hAU
          have hsym := cutIn_symm (graphAfterDelSet G D) U A hAU
          rw [hss, min_comm, ← hsym]
          exact hcut_bad
      have hlt : (G.verts \ (S ∪ A')).card < (G.verts \ S).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · rcases hA'ne with ⟨x, hx⟩
          have hxU := Finset.mem_sdiff.mp (hA'U hx)
          exact ⟨x, Finset.mem_sdiff.mpr ⟨hxU.1, hxU.2⟩,
            fun hx' => (Finset.mem_sdiff.mp hx').2 (Finset.mem_union_right _ hx)⟩
        · intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨hxV, hxSA⟩
          exact Finset.mem_sdiff.mpr ⟨hxV, fun hxS => hxSA (Finset.mem_union_left _ hxS)⟩
      set S₁ := S ∪ A'
      have hS₁V : S₁ ⊆ G.verts := Finset.union_subset hSV (hA'U.trans Finset.sdiff_subset)
      have hdisj : Disjoint S A' := Finset.disjoint_left.mpr fun x hxS hxA =>
        (Finset.mem_sdiff.mp (hA'U hxA)).2 hxS
      have hvol_sum : G.vol S₁ = G.vol S + G.vol A' := by
        dsimp only [S₁]
        exact vol_union_disjoint G hdisj
      have hcut_S₁ : ((graphAfterDelSet G D).cut S₁ : ℝ) < (φ_in / 6) * (G.vol S₁ : ℝ) := by
        have h1 : (graphAfterDelSet G D).cut S₁ ≤
            (graphAfterDelSet G D).cut S + (graphAfterDelSet G D).cutIn U A' :=
          cut_afterDelSet_union_le hV D S A' hSV hA'U
        have h1R : ((graphAfterDelSet G D).cut S₁ : ℝ) ≤
            ((graphAfterDelSet G D).cut S : ℝ) + ((graphAfterDelSet G D).cutIn U A' : ℝ) := by
          exact_mod_cast h1
        have hvol_sumR : (G.vol S₁ : ℝ) = (G.vol S : ℝ) + (G.vol A' : ℝ) := by
          exact_mod_cast hvol_sum
        have hmul : (φ_in / 6) * (G.vol S₁ : ℝ) =
            (φ_in / 6) * (G.vol S : ℝ) + (φ_in / 6) * (G.vol A' : ℝ) := by
          rw [hvol_sumR]; ring
        linarith
      have hvol_total : G.vol G.verts = 2 * G.m := vol_verts_of_isValid hV
      have hsdV : G.vol G.verts = G.vol S + G.vol U := vol_sdiff G hSV
      have hvol_U : G.vol U = 2 * G.m - G.vol S := by omega
      have hsdU : G.vol U = G.vol A' + G.vol (U \ A') := vol_sdiff G hA'U
      have hA'vol_half : 2 * G.vol A' ≤ G.vol U := by omega
      have hS_upper : (G.vol S : ℝ) < (12 / 35 : ℝ) * (G.m : ℝ) := by
        have hD_upper : (D.card : ℝ) / φ_in < (2 / 7 : ℝ) * (G.m : ℝ) := by
          have hb : 7 * ((D.card : ℝ) / φ_in) < 2 * (G.m : ℝ) := by
            have := lt_of_not_ge hbudget
            linarith [show 7 * (D.card : ℝ) / φ_in = 7 * ((D.card : ℝ) / φ_in) by ring]
          linarith
        have hvol_eq : (6 / 5 : ℝ) * (D.card : ℝ) / φ_in = (6 / 5 : ℝ) * ((D.card : ℝ) / φ_in) := by
          ring
        linarith
      have hvol_S₁_le_m : G.vol S₁ ≤ G.m := by
        by_contra hgt
        push Not at hgt
        have hS₁R_upper : (G.vol S₁ : ℝ) < (41 / 35 : ℝ) * (G.m : ℝ) := by
          have h2A : 2 * (G.vol A' : ℝ) ≤ 2 * (G.m : ℝ) - (G.vol S : ℝ) := by
            have hU_le : G.vol U ≤ 2 * G.m := by omega
            have hA'R : 2 * (G.vol A' : ℝ) ≤ (G.vol U : ℝ) := by exact_mod_cast hA'vol_half
            have hS_le_2m : G.vol S ≤ 2 * G.m := by omega
            have hUR : (G.vol U : ℝ) = 2 * (G.m : ℝ) - (G.vol S : ℝ) := by
              rw [hvol_U, Nat.cast_sub hS_le_2m]
              push_cast; ring
            linarith
          have hS₁eq : (G.vol S₁ : ℝ) = (G.vol S : ℝ) + (G.vol A' : ℝ) := by exact_mod_cast hvol_sum
          linarith
        have hS₁ne : S₁.Nonempty := by
          rcases hA'ne with ⟨x, hx⟩
          exact ⟨x, Finset.mem_union_right _ hx⟩
        have hS₁neV : S₁ ≠ G.verts := by
          intro hEq
          apply hA'neU
          ext x
          constructor
          · intro hx; exact hA'U hx
          · intro hx
            have hxV : x ∈ G.verts := (Finset.mem_sdiff.mp hx).1
            have hxnS : x ∉ S := (Finset.mem_sdiff.mp hx).2
            rw [← hEq] at hxV
            rcases Finset.mem_union.mp hxV with hxS | hxA'
            · exact absurd hxS hxnS
            · exact hxA'
        have hexpS₁ := hexp S₁ hS₁V hS₁ne hS₁neV
        change φ_in * min (G.vol S₁ : ℝ) (G.vol (G.verts \ S₁) : ℝ) ≤ (G.cut S₁ : ℝ) at hexpS₁
        have hsdS₁ := vol_sdiff G hS₁V
        have hcompl_lt : G.vol (G.verts \ S₁) ≤ G.vol S₁ := by omega
        have hmin_eq : min (G.vol S₁ : ℝ) (G.vol (G.verts \ S₁) : ℝ) =
            (G.vol (G.verts \ S₁) : ℝ) :=
          min_eq_right (by exact_mod_cast hcompl_lt)
        rw [hmin_eq] at hexpS₁
        have hcut_G : G.cut S₁ ≤ (graphAfterDelSet G D).cut S₁ + D.card :=
          cut_le_afterDelSet_add_card hV D S₁
        have hcut_GR : (G.cut S₁ : ℝ) ≤ ((graphAfterDelSet G D).cut S₁ : ℝ) + (D.card : ℝ) := by
          exact_mod_cast hcut_G
        have hcomplR : (G.vol (G.verts \ S₁) : ℝ) = 2 * (G.m : ℝ) - (G.vol S₁ : ℝ) := by
          have h1 : G.vol S₁ ≤ 2 * G.m := by omega
          have h2 : G.vol (G.verts \ S₁) = 2 * G.m - G.vol S₁ := by omega
          rw [h2, Nat.cast_sub h1]
          push_cast; ring
        have hD_upper : (D.card : ℝ) < (2 / 7 : ℝ) * φ_in * (G.m : ℝ) := by
          have hb : 7 * ((D.card : ℝ) / φ_in) < 2 * (G.m : ℝ) := by
            have := lt_of_not_ge hbudget
            linarith [show 7 * (D.card : ℝ) / φ_in = 7 * ((D.card : ℝ) / φ_in) by ring]
          have hdiv : (D.card : ℝ) / φ_in < (2 / 7 : ℝ) * (G.m : ℝ) := by linarith
          have hmul := mul_lt_mul_of_pos_right hdiv hφ
          rw [div_mul_cancel₀ _ hφ.ne'] at hmul
          linarith
        have hmR : (0 : ℝ) < φ_in * (G.m : ℝ) := mul_pos hφ (by exact_mod_cast hm)
        have hcomb : φ_in * (2 * (G.m : ℝ) - (G.vol S₁ : ℝ)) <
            (φ_in / 6) * (G.vol S₁ : ℝ) + (D.card : ℝ) := by
          rw [hcomplR] at hexpS₁
          linarith
        have hS₁_lt : (7 / 6 : ℝ) * (φ_in * (G.vol S₁ : ℝ)) <
            (7 / 6 : ℝ) * ((41 / 35 : ℝ) * (φ_in * (G.m : ℝ))) := by
          have := mul_lt_mul_of_pos_left hS₁R_upper hφ
          linarith
        linarith
      have hvol_S₁_bound : (G.vol S₁ : ℝ) ≤ (6 / 5 : ℝ) * (D.card : ℝ) / φ_in := by
        have hS₁ne : S₁.Nonempty := by
          rcases hA'ne with ⟨x, hx⟩
          exact ⟨x, Finset.mem_union_right _ hx⟩
        have hS₁neV : S₁ ≠ G.verts := by
          intro hEq
          apply hA'neU
          ext x
          constructor
          · intro hx; exact hA'U hx
          · intro hx
            have hxV := (Finset.mem_sdiff.mp hx).1
            have hxnS := (Finset.mem_sdiff.mp hx).2
            rw [← hEq] at hxV
            rcases Finset.mem_union.mp hxV with hxS | hxA'
            · exact absurd hxS hxnS
            · exact hxA'
        have hexpS₁ := hexp S₁ hS₁V hS₁ne hS₁neV
        change φ_in * min (G.vol S₁ : ℝ) (G.vol (G.verts \ S₁) : ℝ) ≤ (G.cut S₁ : ℝ) at hexpS₁
        have hsdS₁ := vol_sdiff G hS₁V
        have hS₁_le_compl : G.vol S₁ ≤ G.vol (G.verts \ S₁) := by omega
        have hmin_eq : min (G.vol S₁ : ℝ) (G.vol (G.verts \ S₁) : ℝ) = (G.vol S₁ : ℝ) :=
          min_eq_left (by exact_mod_cast hS₁_le_compl)
        rw [hmin_eq] at hexpS₁
        have hcut_G : G.cut S₁ ≤ (graphAfterDelSet G D).cut S₁ + D.card :=
          cut_le_afterDelSet_add_card hV D S₁
        have hcut_GR : (G.cut S₁ : ℝ) ≤ ((graphAfterDelSet G D).cut S₁ : ℝ) + (D.card : ℝ) := by
          exact_mod_cast hcut_G
        have h56 : (5 / 6 : ℝ) * (φ_in * (G.vol S₁ : ℝ)) ≤ (D.card : ℝ) := by linarith
        rw [le_div_iff₀ hφ]
        linarith
      have hrec := ih (G.verts \ S₁).card (hn ▸ hlt) S₁ rfl ⟨hS₁V, hcut_S₁.le, hvol_S₁_bound⟩
      have hunfold : greedyPrune G D φ_in S = greedyPrune G D φ_in S₁ := by
        conv_lhs => unfold greedyPrune
        dsimp only
        rw [dite_eq_left_of_eq_true (eq_true hBad), dite_eq_left_of_eq_true (eq_true hlt)]
      rw [hunfold]
      exact ⟨Finset.Subset.trans Finset.subset_union_left hrec.1, hrec.2.1, hrec.2.2⟩
    · have hunfold : greedyPrune G D φ_in S = S := by
        conv_lhs => unfold greedyPrune
        dsimp only
        rw [dite_eq_right_of_eq_false (eq_false hBad)]
      rw [hunfold]
      refine ⟨Finset.Subset.rfl, ⟨hSV, hcut_le, hvol_le⟩, ?_⟩
      intro A hAU hAne hAneU
      by_contra hlt
      push Not at hlt
      exact hBad ⟨A, hAU, hAne, hAneU, hlt⟩

end

public section

open Classical in
/-- State transition of the fallback pruner on edge deletions `D'`. -/
noncomputable def fbPruneStep (G : Cited.Graph) (D' : Finset ℕ) (φ_in : ℝ) (S : Finset ℕ) :
    Finset ℕ :=
  if (2 : ℝ) * (G.m : ℝ) ≤ 7 * (D'.card : ℝ) / φ_in then G.verts
  else greedyPrune G D' φ_in S

lemma fbPruneStep_init (G : Cited.Graph) (φ_in : ℝ) (hφ : 0 < φ_in) (hV : G.IsValid) (hm : 1 ≤ G.m)
    (hexp : G.IsConductanceExpanderOn G.verts φ_in) :
    FallbackInv φ_in G ∅ ∅ := by
  have hvol0 : G.vol ∅ = 0 := by simp [Cited.Graph.vol, Cited.Graph.volIn]
  have hcut0 : (graphAfterDelSet G ∅).cut ∅ = 0 := by
    rw [graphAfterDelSet_cut_sum G hV ∅ ∅]
    simp
  have hg0 : graphAfterDelSet G ∅ = G := by
    dsimp only [graphAfterDelSet]
    have hfilt : ((List.range G.m).filter fun j => j ∉ (∅ : Finset ℕ)) = List.range G.m :=
      List.filter_eq_self.mpr fun _ _ => by simp
    rw [hfilt]
    have hmap : ((List.range G.m).map fun j => G.edges.getD j (0, 0)) = G.edges :=
      edges_eq_map_range G.edges
    rw [hmap]
  refine ⟨Finset.empty_subset _, ?_, ?_, ?_, ?_⟩
  · simp [hvol0]
  · intro A hA hAne hAneU
    simp only [Finset.sdiff_empty] at hA hAneU ⊢
    rw [hg0]
    have hcut_eq : G.cutIn G.verts A = G.cut A := rfl
    rw [hcut_eq]
    have hmin_nn : 0 ≤ min (G.vol A : ℝ) (G.vol (G.verts \ A) : ℝ) := by
      apply le_min <;> exact Nat.cast_nonneg _
    have hle : φ_in / 6 ≤ φ_in := by linarith
    exact le_trans (mul_le_mul_of_nonneg_right hle hmin_nn) (hexp A hA hAne hAneU)
  · intro hge
    exfalso
    have h1 : (2 : ℝ) * (G.m : ℝ) ≤ 0 := by simpa using hge
    have hmR : (1 : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast hm
    linarith
  · intro _
    refine ⟨Finset.empty_subset _, ?_, ?_⟩
    · simp [hcut0, hvol0]
    · simp [hvol0]

lemma fbPruneStep_spec (G : Cited.Graph) (D D' : Finset ℕ) (φ_in : ℝ)
    (hφ : 0 < φ_in) (hφ1 : φ_in ≤ 1) (hV : G.IsValid) (hm : 1 ≤ G.m)
    (hexp : G.IsConductanceExpanderOn G.verts φ_in) (hDD' : D ⊆ D')
    {S : Finset ℕ} (hInv : FallbackInv φ_in G D S) :
    let S' := fbPruneStep G D' φ_in S
    S ⊆ S' ∧ FallbackInv φ_in G D' S' := by
  rcases hInv with ⟨hSV, hvol, hstrong, hfull, hpr⟩
  dsimp only [fbPruneStep]
  split_ifs with hbudget
  · refine ⟨hSV, Finset.Subset.rfl, ?_, ?_, fun _ => rfl, fun hn => absurd hbudget hn⟩
    · rw [vol_verts_of_isValid hV]
      have h2m : ((2 * G.m : ℕ) : ℝ) = (2 : ℝ) * (G.m : ℝ) := by push_cast; ring
      rw [h2m]
      exact hbudget
    · intro A hA hAne
      exfalso
      simp only [Finset.sdiff_self] at hA
      rcases hAne with ⟨a, ha⟩
      exact absurd (hA ha) (Finset.notMem_empty a)
  · have hnot_prev : ¬ (2 : ℝ) * (G.m : ℝ) ≤ 7 * (D.card : ℝ) / φ_in := by
      intro hprev
      apply hbudget
      have hcard : (D.card : ℝ) ≤ (D'.card : ℝ) := by exact_mod_cast Finset.card_le_card hDD'
      have hdiv : (D.card : ℝ) / φ_in ≤ (D'.card : ℝ) / φ_in :=
        div_le_div_of_nonneg_right hcard hφ.le
      have h1 : 7 * (D.card : ℝ) / φ_in = 7 * ((D.card : ℝ) / φ_in) := by ring
      have h2 : 7 * (D'.card : ℝ) / φ_in = 7 * ((D'.card : ℝ) / φ_in) := by ring
      linarith
    rcases hpr hnot_prev with ⟨hSV', hcut', hvol'⟩
    have hPruneD' : PruneInv G D' φ_in S := by
      refine ⟨hSV', ?_, ?_⟩
      · have hcm : (graphAfterDelSet G D').cut S ≤ (graphAfterDelSet G D).cut S :=
          cut_afterDelSet_mono hV hDD' S
        have hcmR : ((graphAfterDelSet G D').cut S : ℝ) ≤ ((graphAfterDelSet G D).cut S : ℝ) := by
          exact_mod_cast hcm
        exact le_trans hcmR hcut'
      · have hcard : (D.card : ℝ) ≤ (D'.card : ℝ) := by exact_mod_cast Finset.card_le_card hDD'
        have hdiv : (D.card : ℝ) / φ_in ≤ (D'.card : ℝ) / φ_in :=
          div_le_div_of_nonneg_right hcard hφ.le
        have : (6 / 5 : ℝ) * (D.card : ℝ) / φ_in ≤ (6 / 5 : ℝ) * (D'.card : ℝ) / φ_in := by
          rw [mul_div_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
        exact le_trans hvol' this
    have hgr := greedyPrune_spec G D' φ_in hφ hφ1 hV hm hexp hbudget S hPruneD'
    set S' := greedyPrune G D' φ_in S
    rcases hgr with ⟨hSS', ⟨hS'V, hcutS', hvolS'⟩, hstrongS'⟩
    have hvol7 : (G.vol S' : ℝ) ≤ 7 * (D'.card : ℝ) / φ_in := by
      have hnn : 0 ≤ (D'.card : ℝ) / φ_in := div_nonneg (Nat.cast_nonneg _) hφ.le
      have : (6 / 5 : ℝ) * (D'.card : ℝ) / φ_in ≤ 7 * (D'.card : ℝ) / φ_in := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by norm_num) hnn
      exact le_trans hvolS' this
    exact ⟨hSS', hS'V, hvol7, hstrongS', fun hb => absurd hb hbudget, fun _ => ⟨hS'V, hcutS', hvolS'⟩⟩

end

section

private lemma exists_dup_indices : ∀ l : List ℕ, ¬ l.Nodup →
    ∃ i j : ℕ, i < j ∧ ∃ (hi : i < l.length) (hj : j < l.length), l[i] = l[j]
  | [], h => absurd List.nodup_nil h
  | a :: t, h => by
    rw [List.nodup_cons] at h
    by_cases ha : a ∈ t
    · obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp ha
      refine ⟨0, k + 1, by omega, by simp, by simp; omega, ?_⟩
      simpa using heq.symm
    · have ht : ¬ t.Nodup := fun hnd => h ⟨ha, hnd⟩
      obtain ⟨i, j, hij, hi', hj', heq⟩ := exists_dup_indices t ht
      refine ⟨i + 1, j + 1, by omega, by simp; omega, by simp; omega, ?_⟩
      simpa using heq

private lemma take_walk {G : Cited.Graph} (hV : G.IsValid) {u v : ℕ} {P : Spanner.Walk}
    (hP : P.IsWalk G u v) {i : ℕ} (hi : i < P.verts.length) :
    let W : Spanner.Walk :=
      if i = 0 then Walk.empty else ⟨P.verts.take (i + 1), P.edges.take i⟩
    W.IsWalk G u (P.verts[i]) ∧ W.edges.length ≤ i ∧
      (∀ x ∈ W.verts, x ∈ P.verts) ∧ (∀ e ∈ W.edges, e ∈ P.edges) := by
  have hP' := hP
  rcases hP with ⟨hu, _, ⟨hPv, _, _⟩ | ⟨hne, hlen, hhead, _, hedges, hstep⟩⟩
  · simp [hPv] at hi
  · by_cases hi0 : i = 0
    · subst hi0
      have h0 : P.verts[0] = u := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hi, ← List.head?_eq_getElem?]
        exact hhead
      simp only [↓reduceIte, h0]
      exact ⟨⟨hu, hu, Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [Walk.empty],
        by simp [Walk.empty], by simp [Walk.empty]⟩
    · simp only [hi0, ↓reduceIte]
      have hi_le : i ≤ P.edges.length := by omega
      have ha_lt : P.verts[i] < G.n := Walk.isWalk_verts_lt hV hP' (P.verts[i]) (List.getElem_mem hi)
      refine ⟨⟨hu, ha_lt, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, fun x hx => List.mem_of_mem_take hx,
          fun e he => List.mem_of_mem_take he⟩
      · intro hnil
        have := congrArg List.length hnil
        rw [List.length_take, min_eq_left hi_le] at this
        simp only [List.length_nil] at this
        omega
      · rw [List.length_take, List.length_take, min_eq_left hi, min_eq_left hi_le]
      · cases hPv : P.verts with
        | nil => simp [hPv] at hhead
        | cons ph pt =>
          rw [hPv] at hhead
          simp only [List.take_succ_cons, List.head?_cons] at hhead ⊢
          exact hhead
      · rw [List.getLast?_eq_getElem?]
        have hl : (P.verts.take (i + 1)).length = i + 1 := List.length_take_of_le hi
        rw [hl, Nat.add_sub_cancel, List.getElem?_take_of_lt (by omega : i < i + 1),
          List.getElem?_eq_getElem hi]
      · exact fun e he => hedges e (List.mem_of_mem_take he)
      · intro k hk
        rw [List.length_take, min_eq_left hi_le] at hk
        have heq1 : (P.verts.take (i + 1)).getD k 0 = P.verts.getD k 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega : k < i + 1)]
        have heq2 : (P.verts.take (i + 1)).getD (k + 1) 0 = P.verts.getD (k + 1) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega : k + 1 < i + 1)]
        have heq3 : (P.edges.take i).getD k 0 = P.edges.getD k 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
        rw [heq1, heq2, heq3]
        exact hstep k (by omega)
      · rw [List.length_take, min_eq_left hi_le]

private lemma drop_walk {G : Cited.Graph} (hV : G.IsValid) {u v : ℕ} {P : Spanner.Walk}
    (hP : P.IsWalk G u v) {j : ℕ} (hj : j < P.verts.length) :
    let W : Spanner.Walk :=
      if j = P.edges.length then Walk.empty else ⟨P.verts.drop j, P.edges.drop j⟩
    W.IsWalk G (P.verts[j]) v ∧ W.edges.length = P.edges.length - j ∧
      (∀ x ∈ W.verts, x ∈ P.verts) ∧ (∀ e ∈ W.edges, e ∈ P.edges) := by
  have hP' := hP
  rcases hP with ⟨_, hv, ⟨hPv, _, _⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · simp [hPv] at hj
  · by_cases hj_end : j = P.edges.length
    · subst hj_end
      have hlast_eq : P.verts[P.edges.length] = v := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hj, show P.edges.length = P.verts.length - 1 by omega,
          ← List.getLast?_eq_getElem?]
        exact hlast
      simp only [↓reduceIte, hlast_eq, Nat.sub_self]
      exact ⟨⟨hv, hv, Or.inl ⟨rfl, rfl, rfl⟩⟩, rfl,
        by simp [Walk.empty], by simp [Walk.empty]⟩
    · simp only [hj_end, ↓reduceIte]
      have hj_lt : j < P.edges.length := by omega
      have ha_lt : P.verts[j] < G.n := Walk.isWalk_verts_lt hV hP' (P.verts[j]) (List.getElem_mem hj)
      refine ⟨⟨ha_lt, hv, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, List.length_drop,
          fun x hx => List.mem_of_mem_drop hx, fun e he => List.mem_of_mem_drop he⟩
      · intro hnil
        have := congrArg List.length hnil
        rw [List.length_drop] at this
        simp only [List.length_nil] at this
        omega
      · rw [List.length_drop, List.length_drop]
        omega
      · rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hj]
      · rw [List.getLast?_eq_getElem?, List.length_drop, List.getElem?_drop]
        have hidx : j + (P.verts.length - j - 1) = P.verts.length - 1 := by omega
        rw [hidx, ← List.getLast?_eq_getElem?]
        exact hlast
      · exact fun e he => hedges e (List.mem_of_mem_drop he)
      · intro k hk
        rw [List.length_drop] at hk
        have heq1 : (P.verts.drop j).getD k 0 = P.verts.getD (j + k) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        have heq2 : (P.verts.drop j).getD (k + 1) 0 = P.verts.getD (j + k + 1) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]
        have heq3 : (P.edges.drop j).getD k 0 = P.edges.getD (j + k) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [heq1, heq2, heq3]
        exact hstep (j + k) (by omega)

private lemma exists_simple_walk {G : Cited.Graph} (hV : G.IsValid) {u v : ℕ}
    {U D : Finset ℕ} :
    ∀ n : ℕ, ∀ P : Spanner.Walk,
      P.edges.length = n → P.IsWalk G u v →
      (∀ z ∈ P.verts, z ∈ U) → (∀ e ∈ P.edges, e ∉ D) →
      ∃ Q : Spanner.Walk, Q.IsWalk G u v ∧ Q.verts.Nodup ∧
        Q.edges.length ≤ P.edges.length ∧
        (∀ z ∈ Q.verts, z ∈ U) ∧ (∀ e ∈ Q.edges, e ∉ D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hlen hP hU hD
    by_cases hnd : P.verts.Nodup
    · exact ⟨P, hP, hnd, le_rfl, hU, hD⟩
    · obtain ⟨i, j, hij, hi, hj, heq⟩ := exists_dup_indices P.verts hnd
      have htw := take_walk hV hP hi
      have hdw := drop_walk hV hP hj
      set W₁ := if i = 0 then Walk.empty else ⟨P.verts.take (i + 1), P.edges.take i⟩
      set W₂ := if j = P.edges.length then Walk.empty else ⟨P.verts.drop j, P.edges.drop j⟩
      have hW₁ : W₁.IsWalk G u (P.verts[i]) := htw.1
      have hW₂ : W₂.IsWalk G (P.verts[i]) v := heq ▸ hdw.1
      set W' := W₁.append W₂
      have hW' : W'.IsWalk G u v := Walk.isWalk_append hW₁ hW₂
      have hlen' : W'.edges.length < n := by
        rw [Walk.edges_append, List.length_append]
        have h1 : W₁.edges.length ≤ i := htw.2.1
        have h2 : W₂.edges.length = P.edges.length - j := hdw.2.1
        have hj_le : j ≤ P.edges.length := by
          rcases hP with ⟨_, _, ⟨hPv, _, _⟩ | ⟨_, hlenP, _⟩⟩
          · simp [hPv] at hj
          · omega
        omega
      have hU' : ∀ z ∈ W'.verts, z ∈ U := by
        intro z hz
        rcases Walk.mem_verts_append_left hz with hz1 | hz2
        · exact hU z (htw.2.2.1 z hz1)
        · exact hU z (hdw.2.2.1 z hz2)
      have hD' : ∀ e ∈ W'.edges, e ∉ D := by
        intro e he
        rw [Walk.edges_append, List.mem_append] at he
        rcases he with he1 | he2
        · exact hD e (htw.2.2.2 e he1)
        · exact hD e (hdw.2.2.2 e he2)
      obtain ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5⟩ := ih W'.edges.length hlen' W' rfl hW' hU' hD'
      exact ⟨Q, hQ1, hQ2, le_trans hQ3 (by omega), hQ4, hQ5⟩

section
open Classical

private def HasWalkLen (G : Cited.Graph) (D U : Finset ℕ) (u r x : ℕ) : Prop :=
  ∃ W : Spanner.Walk, W.IsWalk G u x ∧ (∀ z ∈ W.verts, z ∈ U) ∧
    (∀ e ∈ W.edges, e ∉ D) ∧ W.edges.length ≤ r

private noncomputable def ballVerts (G : Cited.Graph) (D U : Finset ℕ) (u r : ℕ) : Finset ℕ :=
  U.filter fun x => HasWalkLen G D U u r x

private lemma ballVerts_zero_mem {G : Cited.Graph} {D U : Finset ℕ} {u r : ℕ}
    (hu : u ∈ U) (hU : U ⊆ G.verts) : u ∈ ballVerts G D U u r := by
  rw [ballVerts, Finset.mem_filter]
  refine ⟨hu, Walk.empty, ⟨?_, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [Walk.empty],
    by simp [Walk.empty], by simp [Walk.empty]⟩
  all_goals exact Finset.mem_range.mp (hU hu)

private lemma ballVerts_mono {G : Cited.Graph} {D U : Finset ℕ} {u r₁ r₂ : ℕ}
    (hr : r₁ ≤ r₂) : ballVerts G D U u r₁ ⊆ ballVerts G D U u r₂ := by
  intro x hx
  simp only [ballVerts, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxU, W, hW1, hW2, hW3, hW4⟩
  exact ⟨hxU, W, hW1, hW2, hW3, le_trans hW4 hr⟩

private lemma hasWalkLen_step {G : Cited.Graph} {U : Finset ℕ} (hU : U ⊆ G.verts)
    {D : Finset ℕ} {u r a b j : ℕ}
    (ha : a ∈ ballVerts G D U u r) (hb : b ∈ U)
    (hj : j < G.m) (hjD : j ∉ D)
    (hm : Walk.EdgeMatches (G.edges.getD j (0, 0)) a b) :
    b ∈ ballVerts G D U u (r + 1) := by
  simp only [ballVerts, Finset.mem_filter] at ha ⊢
  rcases ha with ⟨haU, W, hW1, hW2, hW3, hW4⟩
  have ha_lt : a < G.n := Finset.mem_range.mp (hU haU)
  have hb_lt : b < G.n := Finset.mem_range.mp (hU hb)
  have hs : (Walk.single a b j).IsWalk G a b := Walk.isWalk_single ha_lt hb_lt hj hm
  refine ⟨hb, W.append (Walk.single a b j), Walk.isWalk_append hW1 hs, ?_, ?_, ?_⟩
  · intro z hz
    rcases Walk.mem_verts_append_left hz with hzW | hzS
    · exact hW2 z hzW
    · simp only [Walk.single, List.mem_cons, List.not_mem_nil, or_false] at hzS
      rcases hzS with rfl | rfl <;> assumption
  · intro e he
    rw [Walk.edges_append, List.mem_append] at he
    rcases he with heW | heS
    · exact hW3 e heW
    · simp only [Walk.single, List.mem_singleton] at heS
      subst heS
      exact hjD
  · rw [Walk.edges_append, List.length_append]
    simp only [Walk.single, List.length_singleton]
    omega

private lemma cutIn_ball_le_vol_diff {G : Cited.Graph} (hV : G.IsValid)
    {D U : Finset ℕ} (hU : U ⊆ G.verts) (u r : ℕ) :
    (graphAfterDelSet G D).cutIn U (ballVerts G D U u r) ≤
      G.vol (ballVerts G D U u (r + 1) \ ballVerts G D U u r) := by
  set B := ballVerts G D U u r
  set B' := ballVerts G D U u (r + 1)
  rw [graphAfterDelSet_cutIn_sum G D U B hU, graph_vol_sum G hV (B' \ B)]
  apply fb_sum_map_le
  intro j hj
  rw [List.mem_range] at hj
  set e := G.edges.getD j (0, 0)
  by_cases hjD : j ∈ D
  · simp [hjD]
  · simp only [hjD, ↓reduceIte]
    by_cases h1U : e.1 ∈ U <;> by_cases h2U : e.2 ∈ U
    · by_cases h1B : e.1 ∈ B <;> by_cases h2B : e.2 ∈ B
      · simp [h1U, h2U, h1B, h2B]
      · have h2B' : e.2 ∈ B' := hasWalkLen_step hU h1B h2U hj hjD (Or.inl ⟨rfl, rfl⟩)
        have h2d : e.2 ∈ B' \ B := Finset.mem_sdiff.mpr ⟨h2B', h2B⟩
        simp [h1U, h2U, h1B, h2B, h2d]
      · have h1B' : e.1 ∈ B' := hasWalkLen_step hU h2B h1U hj hjD (Or.inr ⟨rfl, rfl⟩)
        have h1d : e.1 ∈ B' \ B := Finset.mem_sdiff.mpr ⟨h1B', h1B⟩
        simp [h1U, h2U, h1B, h2B, h1d]
      · simp [h1U, h2U, h1B, h2B]
    all_goals simp [h1U, h2U]

private lemma ball_step_vol_growth {G : Cited.Graph} (hV : G.IsValid) {D S : Finset ℕ}
    {ψ : ℝ} (_hψ : 0 ≤ ψ) (hstrong : IsStrongExpanderSet G D S ψ)
    (hiso : ∀ z < G.n, 1 ≤ G.deg z) {u r : ℕ} (hu : u ∈ G.verts \ S)
    (hhalf : 2 * G.vol (ballVerts G D (G.verts \ S) u r) ≤ G.vol (G.verts \ S)) :
    (1 + ψ) * (G.vol (ballVerts G D (G.verts \ S) u r) : ℝ) ≤
      (G.vol (ballVerts G D (G.verts \ S) u (r + 1)) : ℝ) := by
  set U := G.verts \ S
  set B := ballVerts G D U u r
  set B' := ballVerts G D U u (r + 1)
  have hU_sub : U ⊆ G.verts := Finset.sdiff_subset
  have hB_sub : B ⊆ U := Finset.filter_subset _ _
  have hBB' : B ⊆ B' := ballVerts_mono (Nat.le_succ r)
  have hBne : B.Nonempty := ⟨u, ballVerts_zero_mem hu hU_sub⟩
  have hBneU : B ≠ U := by
    intro hEq
    have hvolU : 1 ≤ G.vol U := by
      have hdeg := hiso u (Finset.mem_range.mp (hU_sub hu))
      have hsingle : G.deg u ≤ ∑ v ∈ U, G.deg v :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hu
      change ∑ v ∈ U, G.deg v ≥ 1
      omega
    rw [hEq] at hhalf
    omega
  have hexpB := hstrong B hB_sub hBne hBneU
  have hmin_eq : min (G.vol B : ℝ) (G.vol (U \ B) : ℝ) = (G.vol B : ℝ) := by
    have : G.vol B ≤ G.vol (U \ B) := by
      have := vol_sdiff G hB_sub
      omega
    exact min_eq_left (by exact_mod_cast this)
  rw [hmin_eq] at hexpB
  have hcut_le : (graphAfterDelSet G D).cutIn U B ≤ G.vol (B' \ B) :=
    cutIn_ball_le_vol_diff hV hU_sub u r
  have hcut_leR : ((graphAfterDelSet G D).cutIn U B : ℝ) ≤ (G.vol (B' \ B) : ℝ) := by
    exact_mod_cast hcut_le
  have hvol_diff : G.vol B' = G.vol B + G.vol (B' \ B) := by
    have := vol_sdiff G hBB'
    omega
  have hvol_diffR : (G.vol B' : ℝ) = (G.vol B : ℝ) + (G.vol (B' \ B) : ℝ) := by
    exact_mod_cast hvol_diff
  linarith

private lemma exp_half_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (x / 2) ≤ 1 + x := by
  have h1 : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
    linarith [Real.add_one_le_exp (-(x / 2))]
  have h2 : 1 ≤ (1 - x / 2) * (1 + x) := by nlinarith
  have h3 : (1 - x / 2) * (1 + x) ≤ Real.exp (-(x / 2)) * (1 + x) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h4 : 1 ≤ Real.exp (-(x / 2)) * (1 + x) := le_trans h2 h3
  have hexp_pos : 0 < Real.exp (x / 2) := Real.exp_pos _
  have h5 := mul_le_mul_of_nonneg_left h4 hexp_pos.le
  rw [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h5
  exact h5

private noncomputable def fallbackRadius (φ_in : ℝ) (M : ℕ) : ℕ :=
  Nat.ceil (12 * Real.log (2 * (M : ℝ) + 2) / φ_in)

private lemma ball_vol_exceeds_half {G : Cited.Graph} {M : ℕ} (hV : G.IsValid) (hmM : G.m ≤ M)
    (hiso : ∀ z < G.n, 1 ≤ G.deg z) {D S : Finset ℕ} {φ_in : ℝ}
    (hφ : 0 < φ_in) (hφ1 : φ_in ≤ 1)
    (hstrong : IsStrongExpanderSet G D S (φ_in / 6)) {u : ℕ} (hu : u ∈ G.verts \ S) :
    G.vol (G.verts \ S) < 2 * G.vol (ballVerts G D (G.verts \ S) u (fallbackRadius φ_in M)) := by
  set U := G.verts \ S
  set R := fallbackRadius φ_in M
  by_contra hle
  push Not at hle
  have hpow : ∀ r ≤ R,
      (1 + φ_in / 6) ^ r * (G.vol (ballVerts G D U u 0) : ℝ) ≤
        (G.vol (ballVerts G D U u r) : ℝ) := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have hih := ih (Nat.le_of_succ_le hr)
      have hhalf_r : 2 * G.vol (ballVerts G D U u r) ≤ G.vol U := by
        have hm1 : ballVerts G D U u r ⊆ ballVerts G D U u R := ballVerts_mono (Nat.le_of_succ_le hr)
        have hm2 : G.vol (ballVerts G D U u r) ≤ G.vol (ballVerts G D U u R) :=
          Finset.sum_le_sum_of_subset hm1
        omega
      have hstep := ball_step_vol_growth hV (by positivity) hstrong hiso hu hhalf_r
      have h1nn : 0 ≤ 1 + φ_in / 6 := by positivity
      calc (1 + φ_in / 6) ^ (r + 1) * (G.vol (ballVerts G D U u 0) : ℝ)
          = (1 + φ_in / 6) * ((1 + φ_in / 6) ^ r * (G.vol (ballVerts G D U u 0) : ℝ)) := by ring
        _ ≤ (1 + φ_in / 6) * (G.vol (ballVerts G D U u r) : ℝ) :=
            mul_le_mul_of_nonneg_left hih h1nn
        _ ≤ (G.vol (ballVerts G D U u (r + 1)) : ℝ) := hstep
  have hR := hpow R (le_rfl)
  have h0_ge1 : (1 : ℝ) ≤ (G.vol (ballVerts G D U u 0) : ℝ) := by
    have hu0 : u ∈ ballVerts G D U u 0 := ballVerts_zero_mem hu Finset.sdiff_subset
    have hdeg : 1 ≤ G.deg u := hiso u (Finset.mem_range.mp (Finset.sdiff_subset hu))
    have hle0 : G.deg u ≤ G.vol (ballVerts G D U u 0) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hu0
    exact_mod_cast le_trans hdeg hle0
  have hexp_step : Real.exp (φ_in / 12) ≤ 1 + φ_in / 6 := by
    simpa [show (φ_in / 6) / 2 = φ_in / 12 by ring] using
      exp_half_le_one_add (by positivity : 0 ≤ φ_in / 6) (by linarith : φ_in / 6 ≤ 1)
  have hexp_pow : Real.exp ((R : ℝ) * (φ_in / 12)) ≤ (1 + φ_in / 6) ^ R := by
    have h1 := pow_le_pow_left₀ (Real.exp_pos _).le hexp_step R
    rw [← Real.exp_nat_mul] at h1
    simpa [mul_comm] using h1
  have hR_low : Real.log (2 * (M : ℝ) + 2) ≤ (R : ℝ) * (φ_in / 12) := by
    have hceil : 12 * Real.log (2 * (M : ℝ) + 2) / φ_in ≤ (R : ℝ) := Nat.le_ceil _
    have hmul := mul_le_mul_of_nonneg_right hceil (by positivity : 0 ≤ φ_in / 12)
    have heq : (12 * Real.log (2 * (M : ℝ) + 2) / φ_in) * (φ_in / 12) =
        Real.log (2 * (M : ℝ) + 2) := by
      field_simp
    linarith
  have hval_ge : 2 * (M : ℝ) + 2 ≤ (G.vol (ballVerts G D U u R) : ℝ) := by
    have h2m_pos : 0 < 2 * (M : ℝ) + 2 := by positivity
    calc 2 * (M : ℝ) + 2 = Real.exp (Real.log (2 * (M : ℝ) + 2)) := (Real.exp_log h2m_pos).symm
      _ ≤ Real.exp ((R : ℝ) * (φ_in / 12)) := Real.exp_le_exp.mpr hR_low
      _ ≤ (1 + φ_in / 6) ^ R := hexp_pow
      _ = (1 + φ_in / 6) ^ R * 1 := by ring
      _ ≤ (1 + φ_in / 6) ^ R * (G.vol (ballVerts G D U u 0) : ℝ) :=
          mul_le_mul_of_nonneg_left h0_ge1 (by positivity)
      _ ≤ (G.vol (ballVerts G D U u R) : ℝ) := hR
  have hU_le : G.vol U ≤ 2 * G.m := by
    have : G.vol U ≤ G.vol G.verts := Finset.sum_le_sum_of_subset Finset.sdiff_subset
    linarith [vol_verts_of_isValid hV]
  have hleR : 2 * (G.vol (ballVerts G D U u R) : ℝ) ≤ (G.vol U : ℝ) := by exact_mod_cast hle
  have hUR : (G.vol U : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast le_trans hU_le (by omega : 2 * G.m ≤ 2 * M)
  linarith

end

end

public section

open Classical in
/-- BFS + cycle-shortcutting query for the fallback regime: returns a simple `u`-`v` walk in
`G[V \ S] \ D` with at most `25 * (log(2M + 2) + 1) / φ_in` edges. -/
noncomputable def fallbackGetPath (G : Cited.Graph) (D S : Finset ℕ) (φ_in : ℝ) (M u v : ℕ) :
    Spanner.Walk :=
  if _huv : u = v then Walk.empty
  else
    let U := G.verts \ S
    let R := fallbackRadius φ_in M
    let Bu := ballVerts G D U u R
    let Bv := ballVerts G D U v R
    if hne : (Bu ∩ Bv).Nonempty then
      let w := Classical.choose hne
      have hw : w ∈ Bu ∩ Bv := Classical.choose_spec hne
      have hwu : HasWalkLen G D U u R w :=
        (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
      have hwv : HasWalkLen G D U v R w :=
        (Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2
      let P₁ := Classical.choose hwu
      let P₂ := Classical.choose hwv
      let Praw := P₁.append P₂.reverse
      if hex : ∃ Q : Spanner.Walk, Q.IsWalk G u v ∧ Q.verts.Nodup ∧
          Q.edges.length ≤ Praw.edges.length ∧
          (∀ z ∈ Q.verts, z ∈ U) ∧ (∀ e ∈ Q.edges, e ∉ D) then
        Classical.choose hex
      else Walk.empty
    else Walk.empty

lemma fallbackGetPath_spec {G : Cited.Graph} {M : ℕ} (hV : G.IsValid) (hmM : G.m ≤ M)
    (hiso : ∀ z < G.n, 1 ≤ G.deg z) {D S : Finset ℕ} {φ_in : ℝ}
    (hφ : 0 < φ_in) (hφ1 : φ_in ≤ 1)
    (hstrong : IsStrongExpanderSet G D S (φ_in / 6))
    {u v : ℕ} (hu : u ∈ G.verts \ S) (hv : v ∈ G.verts \ S) :
    let P := fallbackGetPath G D S φ_in M u v
    P.IsWalk G u v ∧ P.verts.Nodup ∧ (∀ e ∈ P.edges, e ∉ D) ∧
      (∀ x ∈ P.verts, x ∉ S) ∧
      (P.edges.length : ℝ) ≤ 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / φ_in := by
  classical
  dsimp only [fallbackGetPath]
  by_cases huv : u = v
  · subst huv
    simp only [↓reduceDIte]
    have hu_lt : u < G.n := Finset.mem_range.mp (Finset.sdiff_subset hu)
    refine ⟨⟨hu_lt, hu_lt, Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [Walk.empty],
      by simp [Walk.empty], by simp [Walk.empty], ?_⟩
    simp only [Walk.empty, List.length_nil, Nat.cast_zero]
    have hlog_nn : 0 ≤ Real.log (2 * (M : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hφ.le
  · simp only [huv, ↓reduceDIte]
    set U := G.verts \ S
    set R := fallbackRadius φ_in M
    set Bu := ballVerts G D U u R
    set Bv := ballVerts G D U v R
    have hBu : G.vol U < 2 * G.vol Bu := ball_vol_exceeds_half hV hmM hiso hφ hφ1 hstrong hu
    have hBv : G.vol U < 2 * G.vol Bv := ball_vol_exceeds_half hV hmM hiso hφ hφ1 hstrong hv
    have hne : (Bu ∩ Bv).Nonempty := by
      by_contra hdisj
      rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hdisj
      have hsum := vol_union_disjoint G hdisj
      have hsub : G.vol (Bu ∪ Bv) ≤ G.vol U :=
        Finset.sum_le_sum_of_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      omega
    rw [dite_eq_left_of_eq_true (eq_true hne)]
    set w := Classical.choose hne
    have hw : w ∈ Bu ∩ Bv := Classical.choose_spec hne
    have hwu : HasWalkLen G D U u R w := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
    have hwv : HasWalkLen G D U v R w := (Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2
    set P₁ := Classical.choose hwu
    set P₂ := Classical.choose hwv
    have hP₁ := Classical.choose_spec hwu
    have hP₂ := Classical.choose_spec hwv
    set Praw := P₁.append P₂.reverse
    have hPraw_walk : Praw.IsWalk G u v := Walk.isWalk_append hP₁.1 (Walk.isWalk_reverse hP₂.1)
    have hPraw_U : ∀ z ∈ Praw.verts, z ∈ U := by
      intro z hz
      rcases Walk.mem_verts_append_left hz with hz1 | hz2
      · exact hP₁.2.1 z hz1
      · exact hP₂.2.1 z (by simpa [Walk.reverse] using hz2)
    have hPraw_D : ∀ e ∈ Praw.edges, e ∉ D := by
      intro e he
      rw [Walk.edges_append, List.mem_append] at he
      rcases he with he1 | he2
      · exact hP₁.2.2.1 e he1
      · exact hP₂.2.2.1 e (by simpa [Walk.reverse] using he2)
    have hex : ∃ Q : Spanner.Walk, Q.IsWalk G u v ∧ Q.verts.Nodup ∧
        Q.edges.length ≤ Praw.edges.length ∧
        (∀ z ∈ Q.verts, z ∈ U) ∧ (∀ e ∈ Q.edges, e ∉ D) :=
      exists_simple_walk hV Praw.edges.length Praw rfl hPraw_walk hPraw_U hPraw_D
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    set Q := Classical.choose hex
    have hQ := Classical.choose_spec hex
    refine ⟨hQ.1, hQ.2.1, hQ.2.2.2.2, fun x hx => (Finset.mem_sdiff.mp (hQ.2.2.2.1 x hx)).2, ?_⟩
    have hlen_raw : Praw.edges.length ≤ 2 * R := by
      have h1len : P₁.edges.length ≤ R := hP₁.2.2.2
      have h2len : P₂.edges.length ≤ R := hP₂.2.2.2
      rw [Walk.edges_append, List.length_append]
      simp only [Walk.reverse, List.length_reverse]
      omega
    have hR_lt : (R : ℝ) < 12 * Real.log (2 * (M : ℝ) + 2) / φ_in + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num)
        (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M]))) hφ.le)
    have hQ_le : (Q.edges.length : ℝ) ≤ 2 * (R : ℝ) := by
      exact_mod_cast le_trans hQ.2.2.1 hlen_raw
    have hlog_nn : 0 ≤ Real.log (2 * (M : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
    have hone_le : (2 : ℝ) ≤ 25 / φ_in := by
      rw [le_div_iff₀ hφ]
      nlinarith
    have h2R_lt : 2 * (R : ℝ) < 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / φ_in := by
      have hmul2 : 2 * (R : ℝ) < 2 * (12 * Real.log (2 * (M : ℝ) + 2) / φ_in + 1) := by linarith
      have heq2 : 2 * (12 * Real.log (2 * (M : ℝ) + 2) / φ_in + 1) =
          24 * (Real.log (2 * (M : ℝ) + 2) / φ_in) + 2 := by ring
      have h1 : 2 * (R : ℝ) < 24 * (Real.log (2 * (M : ℝ) + 2) / φ_in) + 2 := by linarith
      have h2 : 24 * (Real.log (2 * (M : ℝ) + 2) / φ_in) + 25 / φ_in ≤
          25 * (Real.log (2 * (M : ℝ) + 2) + 1) / φ_in := by
        have hpos : 0 ≤ Real.log (2 * (M : ℝ) + 2) / φ_in := div_nonneg hlog_nn hφ.le
        have hb : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / φ_in =
            25 * (Real.log (2 * (M : ℝ) + 2) / φ_in) + 25 / φ_in := by ring
        linarith
      linarith
    linarith

end

end MinCostFlow.Expander

