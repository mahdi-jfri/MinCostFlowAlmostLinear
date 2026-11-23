module

public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Graph helpers for expander constructions

Basic lemmas over `MinCostFlow.Cited.Graph`: degree, volume, and cut sums in terms of edge lists,
the handshaking lemma, cut symmetry, monotonicity of conductance expansion, partition cut counting
over `Cited.partsOf`, path shortcutting to simple paths, computable connected-component labeling
(`compLabels`), and computable simple-path search (`findSimplePath`).
-/

public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited

/-! ### List length-of-filter and sum helpers -/

lemma length_filter_eq_sum_map {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : p a
    · simp [h, ih]
    · simp [h, ih, Nat.add_comm]

lemma sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

lemma sum_map_le_sum_map {α : Type*} {l : List α} {f g : α → ℕ}
    (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha : f a ≤ g a := h a (by simp)
    have ht : (t.map f).sum ≤ (t.map g).sum := ih (fun x hx => h x (by simp [hx]))
    omega

lemma sum_map_const {α : Type*} (l : List α) (c : ℕ) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

lemma length_filter_le_of_imp {α : Type*} (l : List α) {p q : α → Bool}
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  rw [length_filter_eq_sum_map, length_filter_eq_sum_map]
  apply sum_map_le_sum_map
  intro x hx
  cases hp : p x
  · simp
  · simp [h x hx hp]

/-! ### Degrees, volumes, and cuts on `Cited.Graph` -/

lemma mem_inside_iff {G : Graph} {X : Finset ℕ} {e : ℕ × ℕ} :
    e ∈ G.inside X ↔ e ∈ G.edges ∧ e.1 ∈ X ∧ e.2 ∈ X := by
  simp [Graph.inside, Bool.and_eq_true]

lemma inside_verts_of_isValid {G : Graph} (hv : G.IsValid) :
    G.inside G.verts = G.edges := by
  unfold Graph.inside Graph.verts
  apply List.filter_eq_self.mpr
  intro e he
  have h := hv e he
  simp [Finset.mem_range, h.1, h.2]

lemma inside_length_le_m (G : Graph) (X : Finset ℕ) :
    (G.inside X).length ≤ G.m := by
  unfold Graph.inside Graph.m
  exact List.length_filter_le _ _

lemma degIn_eq_sum_map (G : Graph) (X : Finset ℕ) (v : ℕ) :
    G.degIn X v =
      ((G.inside X).map fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)).sum := by
  unfold Graph.degIn
  rw [length_filter_eq_sum_map, length_filter_eq_sum_map, ← sum_map_add]
  congr 1
  ext e
  simp

lemma degIn_mono {G : Graph} {X Y : Finset ℕ} (hXY : X ⊆ Y) (v : ℕ) :
    G.degIn X v ≤ G.degIn Y v := by
  unfold Graph.degIn Graph.inside
  rw [List.filter_filter, List.filter_filter, List.filter_filter, List.filter_filter]
  have h1 := length_filter_le_of_imp G.edges (p := fun e => decide (e.1 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X)))
    (q := fun e => decide (e.1 = v) && (decide (e.1 ∈ Y) && decide (e.2 ∈ Y)))
    (fun e _ h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.1, hXY h.2.1, hXY h.2.2⟩)
  have h2 := length_filter_le_of_imp G.edges (p := fun e => decide (e.2 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X)))
    (q := fun e => decide (e.2 = v) && (decide (e.1 ∈ Y) && decide (e.2 ∈ Y)))
    (fun e _ h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.1, hXY h.2.1, hXY h.2.2⟩)
  omega

lemma degIn_eq_zero_of_not_mem (G : Graph) {X : Finset ℕ} {v : ℕ} (hv : v ∉ X) :
    G.degIn X v = 0 := by
  rw [degIn_eq_sum_map]
  have h : ((G.inside X).map fun e =>
      (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)) =
      (G.inside X).map fun _ => 0 := by
    apply List.map_congr_left
    intro e he
    rw [mem_inside_iff] at he
    have h1 : e.1 ≠ v := fun hEq => hv (hEq ▸ he.2.1)
    have h2 : e.2 ≠ v := fun hEq => hv (hEq ▸ he.2.2)
    simp [h1, h2]
  rw [h, sum_map_const]
  simp

lemma volIn_eq_sum_map (G : Graph) (X S : Finset ℕ) :
    G.volIn X S =
      ((G.inside X).map fun e => (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0)).sum := by
  unfold Graph.volIn
  simp_rw [degIn_eq_sum_map]
  induction (G.inside X) with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← ih]
    have h1 : (∑ v ∈ S, if e.1 = v then 1 else 0) = if e.1 ∈ S then 1 else 0 := by
      simp
    have h2 : (∑ v ∈ S, if e.2 = v then 1 else 0) = if e.2 ∈ S then 1 else 0 := by
      simp
    omega

lemma volIn_self (G : Graph) (X : Finset ℕ) :
    G.volIn X X = 2 * (G.inside X).length := by
  rw [volIn_eq_sum_map]
  have h : ((G.inside X).map fun e =>
      (if e.1 ∈ X then 1 else 0) + (if e.2 ∈ X then 1 else 0)) =
      (G.inside X).map fun _ => 2 := by
    apply List.map_congr_left
    intro e he
    rw [mem_inside_iff] at he
    simp [he.2.1, he.2.2]
  rw [h, sum_map_const]
  ring

lemma vol_verts_of_isValid {G : Graph} (hv : G.IsValid) :
    G.vol G.verts = 2 * G.m := by
  unfold Graph.vol Graph.m
  rw [volIn_self, inside_verts_of_isValid hv]

lemma volIn_mono_left {G : Graph} {X Y : Finset ℕ} (hXY : X ⊆ Y) (S : Finset ℕ) :
    G.volIn X S ≤ G.volIn Y S := by
  unfold Graph.volIn
  exact Finset.sum_le_sum fun v _ => degIn_mono hXY v

lemma volIn_mono_right (G : Graph) (X : Finset ℕ) {S T : Finset ℕ} (hST : S ⊆ T) :
    G.volIn X S ≤ G.volIn X T := by
  unfold Graph.volIn
  exact Finset.sum_le_sum_of_subset hST

lemma volIn_disjoint_union (G : Graph) (X A B : Finset ℕ) (hd : Disjoint A B) :
    G.volIn X (A ∪ B) = G.volIn X A + G.volIn X B := by
  unfold Graph.volIn
  exact Finset.sum_union hd

lemma volIn_add_volIn_sdiff (G : Graph) (X S : Finset ℕ) (hS : S ⊆ X) :
    G.volIn X S + G.volIn X (X \ S) = 2 * (G.inside X).length := by
  rw [← volIn_disjoint_union G X S (X \ S) disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset hS, volIn_self]

lemma volIn_le_two_mul_m (G : Graph) (X S : Finset ℕ) :
    G.volIn X S ≤ 2 * G.m := by
  have h1 : G.volIn X S = G.volIn X (S ∩ X) := by
    unfold Graph.volIn
    rw [← Finset.sum_sdiff (Finset.inter_subset_left (s₁ := S) (s₂ := X))]
    have hzero : ∑ v ∈ S \ (S ∩ X), G.degIn X v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_inter] at hv
      exact degIn_eq_zero_of_not_mem G (fun hx => hv.2 ⟨hv.1, hx⟩)
    omega
  rw [h1]
  have h2 : G.volIn X (S ∩ X) ≤ G.volIn X X :=
    volIn_mono_right G X Finset.inter_subset_right
  have h3 := volIn_self G X
  have h4 := inside_length_le_m G X
  omega

lemma cutIn_eq_sum_map (G : Graph) (X S : Finset ℕ) :
    G.cutIn X S =
      ((G.inside X).map fun e =>
        if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum := by
  unfold Graph.cutIn
  rw [length_filter_eq_sum_map]

lemma cutIn_sdiff (G : Graph) (X S : Finset ℕ) (_hS : S ⊆ X) :
    G.cutIn X (X \ S) = G.cutIn X S := by
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map]
  congr 1
  apply List.map_congr_left
  intro e he
  rw [mem_inside_iff] at he
  by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;>
    simp [Finset.mem_sdiff, he.2.1, he.2.2, h1, h2]

lemma cutIn_le_volIn (G : Graph) (X S : Finset ℕ) :
    G.cutIn X S ≤ G.volIn X S := by
  rw [cutIn_eq_sum_map, volIn_eq_sum_map]
  apply sum_map_le_sum_map
  intro e _
  by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;> simp [h1, h2]

lemma deg_eq_cut_singleton {G : Graph} (hv : G.IsValid) (hl : G.IsLoopless)
    {v : ℕ} (_hvn : v < G.n) :
    G.deg v = G.cut {v} := by
  unfold Graph.deg Graph.cut
  rw [degIn_eq_sum_map, cutIn_eq_sum_map, inside_verts_of_isValid hv]
  congr 1
  apply List.map_congr_left
  intro e he
  have hne : e.1 ≠ e.2 := hl e he
  by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v
  · exact False.elim (hne (h1.trans h2.symm))
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-! ### Conductance expander properties -/

lemma isConductanceExpanderOn_mono {G : Graph} {X : Finset ℕ} {φ₁ φ₂ : ℝ}
    (hφ : φ₁ ≤ φ₂) (h : G.IsConductanceExpanderOn X φ₂) :
    G.IsConductanceExpanderOn X φ₁ := by
  intro S hSX hSne hSXne
  have h2 := h S hSX hSne hSXne
  have hmin : 0 ≤ min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) :=
    le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact le_trans (mul_le_mul_of_nonneg_right hφ hmin) h2

lemma isConductanceExpanderOn_of_card_le_one {G : Graph} {X : Finset ℕ} (hX : X.card ≤ 1)
    (φ : ℝ) : G.IsConductanceExpanderOn X φ := by
  intro S hSX hSne hSXne
  exfalso
  obtain ⟨a, ha⟩ := hSne
  have hsub : S.card ≤ X.card := Finset.card_le_card hSX
  have ha_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hScard : S.card = X.card := by omega
  exact hSXne (Finset.eq_of_subset_of_card_le hSX (by omega))

lemma isConductanceExpanderOn_of_inside_empty {G : Graph} {X : Finset ℕ}
    (hE : G.inside X = []) (φ : ℝ) : G.IsConductanceExpanderOn X φ := by
  intro S hSX _ _
  have hvol : G.volIn X S = 0 := by
    rw [volIn_eq_sum_map, hE]
    simp
  have hvol2 : G.volIn X (X \ S) = 0 := by
    rw [volIn_eq_sum_map, hE]
    simp
  simp [hvol, hvol2]

/-! ### Partition `Cited.partsOf` lemmas -/

lemma mem_partsOf_iff {G : Graph} {label : List ℕ} {X : Finset ℕ} :
    X ∈ partsOf G label ↔
      ∃ v ∈ G.verts, X = G.verts.filter fun x => label.getD x 0 = label.getD v 0 := by
  simp [partsOf, eq_comm]

lemma partsOf_nonempty {G : Graph} {label : List ℕ} {X : Finset ℕ}
    (hX : X ∈ partsOf G label) : X.Nonempty := by
  rw [mem_partsOf_iff] at hX
  obtain ⟨v, hv, rfl⟩ := hX
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩

lemma partsOf_subset_verts {G : Graph} {label : List ℕ} {X : Finset ℕ}
    (hX : X ∈ partsOf G label) : X ⊆ G.verts := by
  rw [mem_partsOf_iff] at hX
  obtain ⟨v, _, rfl⟩ := hX
  exact Finset.filter_subset _ _

lemma mem_part_iff_label_eq {G : Graph} {label : List ℕ} {X : Finset ℕ}
    (hX : X ∈ partsOf G label) {u v : ℕ} (hu : u ∈ X) (hv : v ∈ G.verts) :
    v ∈ X ↔ label.getD v 0 = label.getD u 0 := by
  rw [mem_partsOf_iff] at hX
  obtain ⟨w, _, rfl⟩ := hX
  simp only [Finset.mem_filter] at hu ⊢
  constructor
  · intro h; rw [h.2, hu.2]
  · intro h; exact ⟨hv, h.trans hu.2⟩

lemma partsOf_pairwiseDisjoint (G : Graph) (label : List ℕ) :
    (partsOf G label : Set (Finset ℕ)).PairwiseDisjoint id := by
  intro X hX Y hY hXY
  change Disjoint X Y
  rw [Finset.disjoint_left]
  intro u huX huY
  apply hXY
  change X ∈ partsOf G label at hX
  change Y ∈ partsOf G label at hY
  rw [mem_partsOf_iff] at hX hY
  obtain ⟨v₁, _, hXeq⟩ := hX
  obtain ⟨v₂, _, hYeq⟩ := hY
  rw [hXeq] at huX
  rw [hYeq] at huY
  rw [hXeq, hYeq]
  simp only [Finset.mem_filter] at huX huY
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, h1⟩; exact ⟨hz, h1.trans (huX.2.symm.trans huY.2)⟩
  · rintro ⟨hz, h2⟩; exact ⟨hz, h2.trans (huY.2.symm.trans huX.2)⟩

lemma partsOf_biUnion (G : Graph) (label : List ℕ) :
    (partsOf G label).biUnion id = G.verts := by
  ext u
  simp only [Finset.mem_biUnion, id_eq, mem_partsOf_iff]
  constructor
  · rintro ⟨X, ⟨v, _, rfl⟩, hu⟩
    exact (Finset.mem_filter.mp hu).1
  · intro hu
    refine ⟨G.verts.filter fun x => label.getD x 0 = label.getD u 0, ⟨u, hu, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hu, rfl⟩

lemma sum_cut_partsOf {G : Graph} (hv : G.IsValid) (label : List ℕ) :
    ∑ X ∈ partsOf G label, G.cut X =
      2 * (G.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length := by
  have hcut : ∀ X ∈ partsOf G label, G.cut X =
      (G.edges.map fun e => if (decide (e.1 ∈ X) != decide (e.2 ∈ X)) then 1 else 0).sum := by
    intro X _
    unfold Graph.cut
    rw [cutIn_eq_sum_map, inside_verts_of_isValid hv]
  rw [Finset.sum_congr rfl hcut, length_filter_eq_sum_map]
  have hvalid : ∀ e ∈ G.edges, e.1 ∈ G.verts ∧ e.2 ∈ G.verts := by
    intro e he
    have h := hv e he
    simp [Graph.verts, h.1, h.2]
  suffices hgen : ∀ es : List (ℕ × ℕ), (∀ e ∈ es, e.1 ∈ G.verts ∧ e.2 ∈ G.verts) →
      ∑ X ∈ partsOf G label,
        (es.map fun e => if (decide (e.1 ∈ X) != decide (e.2 ∈ X)) then 1 else 0).sum =
      2 * (es.map fun e => if decide (label.getD e.1 0 ≠ label.getD e.2 0) then 1 else 0).sum by
    exact hgen G.edges hvalid
  intro es hes
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons]
    have hev : e.1 ∈ G.verts ∧ e.2 ∈ G.verts := hes e (by simp)
    have hes' : ∀ e' ∈ es, e'.1 ∈ G.verts ∧ e'.2 ∈ G.verts := fun e' he' => hes e' (by simp [he'])
    rw [Finset.sum_add_distrib, ih hes']
    have hpoint : (∑ X ∈ partsOf G label,
        if (decide (e.1 ∈ X) != decide (e.2 ∈ X)) then 1 else 0) =
        2 * (if decide (label.getD e.1 0 ≠ label.getD e.2 0) then 1 else 0) := by
      by_cases hlbl : label.getD e.1 0 = label.getD e.2 0
      · simp only [hlbl, ne_eq, not_true_eq_false, decide_false]
        have hzero : (∑ X ∈ partsOf G label,
            if (decide (e.1 ∈ X) != decide (e.2 ∈ X)) then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro X hX
          have h1 : e.1 ∈ X ↔ e.2 ∈ X := by
            rw [mem_partsOf_iff] at hX
            obtain ⟨v, _, rfl⟩ := hX
            simp only [Finset.mem_filter, hev.1, hev.2, true_and]
            rw [hlbl]
          by_cases hm : e.1 ∈ X
          · have hm2 := h1.mp hm
            simp [hm, hm2]
          · have hm2 : e.2 ∉ X := fun h => hm (h1.mpr h)
            simp [hm, hm2]
        rw [hzero]
        simp
      · simp only [ne_eq, hlbl, not_false_eq_true, decide_true, ↓reduceIte, mul_one]
        let X₁ := G.verts.filter fun x => label.getD x 0 = label.getD e.1 0
        let X₂ := G.verts.filter fun x => label.getD x 0 = label.getD e.2 0
        have hX₁ : X₁ ∈ partsOf G label := mem_partsOf_iff.mpr ⟨e.1, hev.1, rfl⟩
        have hX₂ : X₂ ∈ partsOf G label := mem_partsOf_iff.mpr ⟨e.2, hev.2, rfl⟩
        have he1X₁ : e.1 ∈ X₁ := Finset.mem_filter.mpr ⟨hev.1, rfl⟩
        have he2X₂ : e.2 ∈ X₂ := Finset.mem_filter.mpr ⟨hev.2, rfl⟩
        have hneX : X₁ ≠ X₂ := by
          intro hEq
          have : e.1 ∈ X₂ := hEq ▸ he1X₁
          exact hlbl (Finset.mem_filter.mp this).2
        have hsum : ∀ X ∈ partsOf G label,
            (if (decide (e.1 ∈ X) != decide (e.2 ∈ X)) then 1 else 0) =
              (if X = X₁ then 1 else 0) + (if X = X₂ then 1 else 0) := by
          intro X hX
          by_cases h1 : X = X₁
          · subst h1
            have he2nX₁ : e.2 ∉ X₁ := fun h => hlbl (Finset.mem_filter.mp h).2.symm
            simp [he1X₁, he2nX₁, hneX]
          · by_cases h2 : X = X₂
            · subst h2
              have he1nX₂ : e.1 ∉ X₂ := fun h => hlbl (Finset.mem_filter.mp h).2
              simp [he1nX₂, he2X₂, Ne.symm hneX]
            · have he1nX : e.1 ∉ X := fun h => h1 ((partsOf_pairwiseDisjoint G label).eq hX hX₁ (Finset.not_disjoint_iff.mpr ⟨e.1, h, he1X₁⟩))
              have he2nX : e.2 ∉ X := fun h => h2 ((partsOf_pairwiseDisjoint G label).eq hX hX₂ (Finset.not_disjoint_iff.mpr ⟨e.2, h, he2X₂⟩))
              simp [he1nX, he2nX, h1, h2]
        rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', hX₁, hX₂]
    omega

/-! ### Paths and shortcutting to simple paths -/

lemma isPathAlong_singleton (E : List (ℕ × ℕ)) (u : ℕ) :
    IsPathAlong E u u [u] := by
  simp [IsPathAlong]

lemma isPathAlong_imp {E₁ E₂ : List (ℕ × ℕ)} (hE : ∀ e ∈ E₁, e ∈ E₂)
    {u v : ℕ} {P : List ℕ} (hP : IsPathAlong E₁ u v P) :
    IsPathAlong E₂ u v P := by
  refine ⟨hP.1, hP.2.1, hP.2.2.imp fun a b hab => ?_⟩
  rcases hab with h | h
  · exact Or.inl (hE _ h)
  · exact Or.inr (hE _ h)

lemma isPathAlong_cons {E : List (ℕ × ℕ)} {x y v : ℕ} {P : List ℕ}
    (hxy : (x, y) ∈ E ∨ (y, x) ∈ E) (hP : IsPathAlong E y v P) :
    IsPathAlong E x v (x :: P) := by
  rcases hP with ⟨hhead, hlast, hchain⟩
  cases P with
  | nil => simp at hhead
  | cons p ps =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    refine ⟨rfl, ?_, List.isChain_cons_cons.mpr ⟨hxy, hchain⟩⟩
    simpa [List.getLast?_cons] using hlast

lemma isPathAlong_append {E : List (ℕ × ℕ)} {u w v : ℕ} {P Q : List ℕ}
    (hP : IsPathAlong E u w P) (hQ : IsPathAlong E w v Q) :
    IsPathAlong E u v (P.dropLast ++ Q) := by
  rcases hQ with ⟨hQh, hQl, hQc⟩
  cases Q with
  | nil => simp at hQh
  | cons q qs =>
    simp only [List.head?_cons, Option.some.injEq] at hQh
    subst hQh
    induction P generalizing u with
    | nil => simp [IsPathAlong] at hP
    | cons p ps ih =>
      rcases hP with ⟨hPh, hPl, hPc⟩
      simp only [List.head?_cons, Option.some.injEq] at hPh
      subst hPh
      cases ps with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hPl
        subst hPl
        exact ⟨rfl, hQl, hQc⟩
      | cons p2 ps2 =>
        rw [List.isChain_cons_cons] at hPc
        have hPl' : (p2 :: ps2).getLast? = some q := by
          simpa [List.getLast?_cons] using hPl
        have hrec : IsPathAlong E p2 v ((p2 :: ps2).dropLast ++ q :: qs) :=
          ih ⟨rfl, hPl', hPc.2⟩
        have hdrop : (p :: p2 :: ps2).dropLast = p :: (p2 :: ps2).dropLast := by simp
        rw [hdrop, List.cons_append]
        cases hdl : (p2 :: ps2).dropLast ++ q :: qs with
        | nil => simp at hdl
        | cons z zs =>
          have hz : z = p2 := by
            cases ps2 <;> simp_all
          subst hz
          refine ⟨rfl, ?_, List.isChain_cons_cons.mpr ⟨?_, ?_⟩⟩
          · have hgl : (z :: zs).getLast? = some v := by rw [← hdl]; exact hrec.2.1
            simpa [List.getLast?_cons] using hgl
          · cases ps2 with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq] at hPl'
              subst hPl'
              exact hPc.1
            | cons p3 ps3 => exact hPc.1
          · rw [← hdl]; exact hrec.2.2

lemma isPathAlong_reverse {E : List (ℕ × ℕ)} {u v : ℕ} {P : List ℕ}
    (hP : IsPathAlong E u v P) : IsPathAlong E v u P.reverse := by
  induction P generalizing u with
  | nil => simp [IsPathAlong] at hP
  | cons a t ih =>
    rcases hP with ⟨hh, hl, hc⟩
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      simpa using isPathAlong_singleton E a
    | cons b bs =>
      rw [List.isChain_cons_cons] at hc
      have hl' : (b :: bs).getLast? = some v := by simpa [List.getLast?_cons] using hl
      have hrec := ih ⟨rfl, hl', hc.2⟩
      have hrev_eq : (b :: bs).reverse = (b :: bs).reverse.dropLast ++ [b] := by
        cases hrev : (b :: bs).reverse with
        | nil => simp at hrev
        | cons x xs =>
          have hx : (x :: xs).getLast (by simp) = b := by
            have := List.getLast?_reverse (l := b :: bs)
            rw [hrev] at this
            simp only [List.head?_cons] at this
            exact Option.some.inj (by rw [← List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _)]; exact this)
          have := List.dropLast_concat_getLast (l := x :: xs) (by simp)
          rw [hx] at this
          simpa [hrev] using this.symm
      have heq : (a :: b :: bs).reverse = ((b :: bs).reverse.dropLast ++ [b, a]) := by
        rw [List.reverse_cons]
        conv_lhs => rw [hrev_eq]
        rw [List.append_assoc]
        rfl
      rw [heq]
      refine isPathAlong_append hrec ?_
      refine ⟨rfl, rfl, List.isChain_cons_cons.mpr ⟨hc.1.symm, List.isChain_singleton _⟩⟩

lemma isPathAlong_mem_endpoints {E : List (ℕ × ℕ)} {u v : ℕ} {P : List ℕ}
    (hP : IsPathAlong E u v P) : u ∈ P ∧ v ∈ P := by
  exact ⟨List.mem_of_head? hP.1, List.mem_of_getLast? hP.2.1⟩

lemma isPathAlong_concat {E : List (ℕ × ℕ)} {u a w : ℕ} {P : List ℕ}
    (hP : IsPathAlong E u a P) (haw : (a, w) ∈ E ∨ (w, a) ∈ E) :
    IsPathAlong E u w (P ++ [w]) := by
  induction P using List.reverseRecOn with
  | nil => simp [IsPathAlong] at hP
  | append_singleton Q x =>
    have hxa : x = a := by
      have := hP.2.1
      simp at this
      exact this
    subst hxa
    have hdrop : (Q ++ [x]).dropLast ++ [x, w] = (Q ++ [x]) ++ [w] := by simp
    rw [← hdrop]
    exact isPathAlong_append hP ⟨rfl, rfl, List.isChain_cons_cons.mpr ⟨haw, List.isChain_singleton _⟩⟩

lemma isPathAlong_prefix_of_split {E : List (ℕ × ℕ)} {u v z : ℕ} {l₁ l₂ : List ℕ}
    (hP : IsPathAlong E u v (l₁ ++ z :: l₂)) :
    IsPathAlong E u z (l₁ ++ [z]) := by
  induction l₁ generalizing u with
  | nil =>
    simp only [List.nil_append] at hP ⊢
    have huz : z = u := by simpa [IsPathAlong] using hP.1
    rw [huz]
    exact isPathAlong_singleton E u
  | cons a as ih =>
    rcases hP with ⟨hh, hl, hc⟩
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases as with
    | nil =>
      simp only [List.cons_append, List.nil_append] at hc ⊢
      rw [List.isChain_cons_cons] at hc
      exact ⟨rfl, rfl, List.isChain_cons_cons.mpr ⟨hc.1, List.isChain_singleton _⟩⟩
    | cons b bs =>
      simp only [List.cons_append] at hc hl ⊢
      rw [List.isChain_cons_cons] at hc
      have hl' : (b :: bs ++ z :: l₂).getLast? = some v := by
        simpa [List.getLast?_cons] using hl
      have hrec := ih ⟨rfl, hl', hc.2⟩
      exact isPathAlong_cons hc.1 hrec

lemma isPathAlong_all_mem_range {E : List (ℕ × ℕ)} {n u v : ℕ}
    (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) (hu : u < n) {P : List ℕ}
    (hP : IsPathAlong E u v P) : ∀ x ∈ P, x < n := by
  rcases hP with ⟨hh, hl, hc⟩
  induction P generalizing u with
  | nil => simp at hh
  | cons a t ih =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact hu
    · cases t with
      | nil => simp at hxt
      | cons b bs =>
        rw [List.isChain_cons_cons] at hc
        have hb : b < n := by
          rcases hc.1 with h | h
          · exact (hE _ h).2
          · exact (hE _ h).1
        have hl' : (b :: bs).getLast? = some v := by simpa [List.getLast?_cons] using hl
        exact ih hb rfl hl' hc.2 x hxt

private lemma isPathAlong_drop_prefix {E : List (ℕ × ℕ)} {u v x : ℕ} {P : List ℕ}
    (hP : IsPathAlong E u v (x :: P)) {l₁ l₂ : List ℕ} (heq : x :: P = l₁ ++ x :: l₂) :
    IsPathAlong E x v (x :: l₂) := by
  rcases hP with ⟨_, hl, hc⟩
  rw [heq] at hl hc
  have hl' : (x :: l₂).getLast? = some v := by
    cases l₁ with
    | nil => simpa using hl
    | cons a as =>
      have hlast : ∀ (l : List ℕ) (c : ℕ), (c :: (l ++ x :: l₂)).getLast? = (x :: l₂).getLast? := by
        intro l
        induction l with
        | nil => intro c; simp [List.getLast?_cons]
        | cons d ds ihd =>
          intro c
          simp only [List.cons_append, List.getLast?_cons_cons]
          exact ihd d
      rw [List.cons_append, hlast as a] at hl
      exact hl
  have hc' : (x :: l₂).IsChain fun a b => (a, b) ∈ E ∨ (b, a) ∈ E := by
    have := List.isChain_append.mp hc
    exact this.2.1
  exact ⟨rfl, hl', hc'⟩

theorem exists_nodup_isPathAlong {E : List (ℕ × ℕ)} {u v : ℕ} {P : List ℕ}
    (hP : IsPathAlong E u v P) :
    ∃ Q : List ℕ, IsPathAlong E u v Q ∧ Q.Nodup ∧ Q.length ≤ P.length ∧ ∀ x ∈ Q, x ∈ P := by
  induction hn : P.length using Nat.strong_induction_on generalizing P u with
  | _ n ih =>
    subst hn
    cases P with
    | nil => simp [IsPathAlong] at hP
    | cons x xs =>
      by_cases hx : x ∈ xs
      · obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hx
        have hP' : IsPathAlong E x v (x :: l₂) := by
          have heq : x :: xs = (x :: l₁) ++ x :: l₂ := by simp [hsplit]
          exact isPathAlong_drop_prefix (by simpa using hP) heq
        have hu : x = u := by
          have := hP.1
          simp only [List.head?_cons, Option.some.injEq] at this
          exact this
        subst hu
        have hlen : (x :: l₂).length < (x :: xs).length := by
          have := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at this ⊢
          omega
        obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := ih (x :: l₂).length hlen hP' rfl
        refine ⟨Q, hQ1, hQ2, by omega, fun z hz => ?_⟩
        have hz2 := hQ4 z hz
        rcases List.mem_cons.mp hz2 with rfl | hzl2
        · simp
        · exact List.mem_cons_of_mem x (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem x hzl2))
      · cases xs with
        | nil =>
          exact ⟨[x], hP, List.nodup_singleton x, le_rfl, fun z hz => hz⟩
        | cons y ys =>
          have hPtail : IsPathAlong E y v (y :: ys) := by
            rcases hP with ⟨_, hl, hc⟩
            rw [List.isChain_cons_cons] at hc
            exact ⟨rfl, by simpa [List.getLast?_cons] using hl, hc.2⟩
          have hu : x = u := by
            have := hP.1
            simp only [List.head?_cons, Option.some.injEq] at this
            exact this
          subst hu
          obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := ih (y :: ys).length (by simp) hPtail rfl
          have hxy : (x, y) ∈ E ∨ (y, x) ∈ E := (List.isChain_cons_cons.mp hP.2.2).1
          have hxQ : x ∉ Q := fun hmem => hx (hQ4 x hmem)
          refine ⟨x :: Q, isPathAlong_cons hxy hQ1, List.nodup_cons.mpr ⟨hxQ, hQ2⟩, ?_, ?_⟩
          · have hlenQ : Q.length ≤ (y :: ys).length := hQ3
            simp only [List.length_cons] at hlenQ ⊢
            omega
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hzQ
            · simp
            · exact List.mem_cons_of_mem x (hQ4 z hzQ)


end MinCostFlow.Expander
