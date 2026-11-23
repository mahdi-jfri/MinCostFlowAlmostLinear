module

public import MinCostFlow.Basic.Forest
import Mathlib.Data.List.Nodup

/-!
# Walks, paths, and forests on `MGraph`

This file develops the basic properties of walks, simple paths, flow vectors, and forests for
`MinCostFlow.MGraph`:
* reversal and concatenation of walks and simple paths,
* shortcutting any walk to a simple path,
* uniqueness of simple paths in a forest (`IsForest`),
* edge-deletion disconnection and subgraph path lifting.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Walk endpoints, concatenation, and reversal -/

lemma mem_walkEdges_iff {e : ℕ} {P : List (ℕ × Bool)} :
    e ∈ walkEdges P ↔ ∃ b : Bool, (e, b) ∈ P := by
  simp [walkEdges, List.mem_toFinset, Prod.exists]

lemma mem_walkEdges_of_mem {x : ℕ × Bool} {P : List (ℕ × Bool)} (hx : x ∈ P) :
    x.1 ∈ walkEdges P :=
  mem_walkEdges_iff.mpr ⟨x.2, hx⟩

lemma walkEdges_cons (x : ℕ × Bool) (P : List (ℕ × Bool)) :
    walkEdges (x :: P) = insert x.1 (walkEdges P) := by
  ext e
  simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert]

lemma IsWalk_append {G : MGraph} {u w v : ℕ} {P Q : List (ℕ × Bool)}
    (hP : G.IsWalk u w P) (hQ : G.IsWalk w v Q) : G.IsWalk u v (P ++ Q) := by
  induction hP with
  | nil _ => exact hQ
  | cons he hsrc _ ih => exact .cons he hsrc (ih hQ)

lemma IsWalk_split {G : MGraph} {u v : ℕ} {P Q : List (ℕ × Bool)}
    (h : G.IsWalk u v (P ++ Q)) :
    ∃ w, G.IsWalk u w P ∧ G.IsWalk w v Q := by
  induction P generalizing u with
  | nil => exact ⟨u, .nil u, h⟩
  | cons x P ih =>
    cases h with
    | cons he hsrc hrest =>
      obtain ⟨w, hP, hQ⟩ := ih hrest
      exact ⟨w, .cons he hsrc hP, hQ⟩

lemma IsWalk_mem_split_edge {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) {a : ℕ × Bool} (ha : a ∈ P) :
    ∃ P₁ P₂, P = P₁ ++ a :: P₂ ∧ G.IsWalk u (G.src a) P₁ ∧ G.IsWalk (G.dst a) v P₂ := by
  induction hP with
  | nil _ => simp at ha
  | cons he hsrc hrest ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[], _, rfl, by simpa [hsrc] using MGraph.IsWalk.nil _, hrest⟩
    · obtain ⟨P₁, P₂, hEq, h1, h2⟩ := ih ha
      exact ⟨_ :: P₁, P₂, by rw [hEq, List.cons_append], .cons he hsrc h1, h2⟩

lemma IsWalk_edges_mem {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) {a : ℕ × Bool} (ha : a ∈ P) : a.1 ∈ G.E := by
  induction hP with
  | nil _ => simp at ha
  | cons he _ _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact ih ha

lemma IsWalk_vertices_mem {G : MGraph} (hG : G.IsValid) {u v : ℕ} {P : List (ℕ × Bool)}
    (hu : u ∈ G.V) (hP : G.IsWalk u v P) :
    v ∈ G.V ∧ ∀ w ∈ G.walkVertices u P, w ∈ G.V := by
  induction hP with
  | nil s =>
    refine ⟨hu, ?_⟩
    simp [MGraph.walkVertices, hu]
  | @cons u₀ v₀ x₀ P₀ he hsrc _ ih =>
    have hend := hG x₀.1 he
    have hdst : G.dst x₀ ∈ G.V := by
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hend.1, hend.2]
    obtain ⟨hv, hmem⟩ := ih hdst
    refine ⟨hv, fun w hw => ?_⟩
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · exact hu
    · exact hdst
    · exact hmem w (by simp [MGraph.walkVertices, hw])

lemma IsWalk_end_mem_walkVertices {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : v ∈ G.walkVertices u P := by
  induction hP with
  | nil s => simp [MGraph.walkVertices]
  | cons _ _ _ ih =>
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at ih ⊢
    exact Or.inr ih

lemma IsWalk_start_mem_walkVertices (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) :
    u ∈ G.walkVertices u P := by
  simp [MGraph.walkVertices]

lemma IsWalk_nonempty_mem {G : MGraph} (hG : G.IsValid) {u v : ℕ}
    {P : List (ℕ × Bool)} (hP : G.IsWalk u v P) (hne : P ≠ []) : u ∈ G.V ∧ v ∈ G.V := by
  cases hP with
  | nil _ => exact absurd rfl hne
  | @cons _ _ x₀ _ he hsrc hrest =>
    have hend := hG x₀.1 he
    have hu : u ∈ G.V := by
      rw [← hsrc]
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.src, hend.1, hend.2]
    have hdst : G.dst x₀ ∈ G.V := by
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hend.1, hend.2]
    exact ⟨hu, (IsWalk_vertices_mem hG hdst hrest).1⟩

lemma src_flip (G : MGraph) (x : ℕ × Bool) :
    G.src (x.1, !x.2) = G.dst x := by
  rcases x with ⟨e, _ | _⟩ <;> rfl

lemma dst_flip (G : MGraph) (x : ℕ × Bool) :
    G.dst (x.1, !x.2) = G.src x := by
  rcases x with ⟨e, _ | _⟩ <;> rfl

lemma IsWalk_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : G.IsWalk v u (walkRev P) := by
  induction hP with
  | nil s => exact .nil s
  | @cons u₀ v₀ x₀ P₀ he hsrc _ ih =>
    simp only [walkRev, List.map_cons, List.reverse_cons]
    refine IsWalk_append ih ?_
    refine .cons he (by rw [src_flip]) ?_
    rw [dst_flip, hsrc]
    exact .nil u₀

lemma walkRev_walkRev (P : List (ℕ × Bool)) : walkRev (walkRev P) = P := by
  simp only [walkRev, List.map_reverse, List.reverse_reverse, List.map_map]
  have h : (fun x : ℕ × Bool => (x.1, !!x.2)) = id := by
    funext ⟨e, b⟩
    cases b <;> rfl
  simp [Function.comp_def]

lemma walkRev_append (P Q : List (ℕ × Bool)) :
    walkRev (P ++ Q) = walkRev Q ++ walkRev P := by
  simp [walkRev, List.map_append, List.reverse_append]

lemma walkVertices_cons (G : MGraph) (u : ℕ) (x : ℕ × Bool) (P : List (ℕ × Bool)) :
    G.walkVertices u (x :: P) = u :: G.walkVertices (G.dst x) P := by
  simp [MGraph.walkVertices]

lemma walkVertices_append (G : MGraph) (u : ℕ) (P Q : List (ℕ × Bool)) :
    G.walkVertices u (P ++ Q) = G.walkVertices u P ++ Q.map G.dst := by
  simp [MGraph.walkVertices, List.map_append, List.cons_append]

lemma walkVertices_eq_map_src_append {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) :
    G.walkVertices u P = P.map G.src ++ [v] := by
  induction hP with
  | nil s => simp [MGraph.walkVertices]
  | cons _ hsrc _ ih =>
    rw [walkVertices_cons, ih, List.map_cons, List.cons_append, hsrc]

lemma walkVertices_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) :
    G.walkVertices v (walkRev P) = (G.walkVertices u P).reverse := by
  induction hP with
  | nil s => simp [MGraph.walkVertices, walkRev]
  | @cons u₀ v₀ x₀ P₀ _ hsrc _ ih =>
    simp only [walkRev, List.map_cons, List.reverse_cons]
    change G.walkVertices v₀ (walkRev P₀ ++ [(x₀.1, !x₀.2)]) = _
    rw [walkVertices_append, ih, List.map_singleton, dst_flip, hsrc, walkVertices_cons,
      List.reverse_cons]

lemma IsPath_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) : G.IsPath v u (walkRev P) := by
  refine ⟨IsWalk_walkRev hP.1, ?_⟩
  rw [walkVertices_walkRev hP.1, List.nodup_reverse]
  exact hP.2

lemma walkEdges_walkRev (P : List (ℕ × Bool)) : walkEdges (walkRev P) = walkEdges P := by
  ext e
  simp only [walkEdges, walkRev, List.mem_toFinset, List.mem_map, List.mem_reverse, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨c, d, hcd, hEq⟩, rfl⟩
    cases hEq
    exact ⟨a, d, hcd, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, !b, ⟨a, b, hab, rfl⟩, rfl⟩

lemma walkEdges_append (P Q : List (ℕ × Bool)) :
    walkEdges (P ++ Q) = walkEdges P ∪ walkEdges Q := by
  ext e
  simp [walkEdges, List.mem_toFinset]

lemma walkVertices_mem_split {G : MGraph} {u v w : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hw : w ∈ G.walkVertices u P) :
    ∃ P₁ P₂, P = P₁ ++ P₂ ∧ G.IsWalk u w P₁ ∧ G.IsWalk w v P₂ := by
  induction hP with
  | nil _ =>
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨[], [], rfl, .nil w, .nil w⟩
  | cons he hsrc hrest ih =>
    rw [walkVertices_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨[], _ :: _, rfl, .nil w, .cons he hsrc hrest⟩
    · obtain ⟨P₁, P₂, hEq, h1, h2⟩ := ih hw
      exact ⟨_ :: P₁, P₂, by rw [hEq, List.cons_append], .cons he hsrc h1, h2⟩

lemma IsWalk_firstHit {G : MGraph} {s v : ℕ} {P : List (ℕ × Bool)} (S : Finset ℕ)
    (hP : G.IsWalk s v P) (hv : v ∈ S) :
    ∃ P₁ P₂ w, P = P₁ ++ P₂ ∧ G.IsWalk s w P₁ ∧ G.IsWalk w v P₂ ∧
      w ∈ S ∧ ∀ z ∈ P₁.map G.src, z ∉ S := by
  induction hP with
  | nil s₀ =>
    exact ⟨[], [], s₀, rfl, .nil s₀, .nil s₀, hv, by simp⟩
  | @cons s₀ _ x₀ P₀ he hsrc hrest ih =>
    by_cases hs : s₀ ∈ S
    · exact ⟨[], x₀ :: P₀, s₀, rfl, .nil s₀, .cons he hsrc hrest, hs, by simp⟩
    · obtain ⟨P₁, P₂, w, hEq, h1, h2, hw, hmin⟩ := ih hv
      refine ⟨x₀ :: P₁, P₂, w, by rw [hEq, List.cons_append], .cons he hsrc h1, h2, hw, ?_⟩
      intro z hz
      simp only [List.map_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · rwa [hsrc]
      · exact hmin z hz

lemma exists_isPath_of_isWalk {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) :
    ∃ Q, G.IsPath u v Q ∧ walkEdges Q ⊆ walkEdges P ∧
      ∀ w ∈ G.walkVertices u Q, w ∈ G.walkVertices u P := by
  induction hP with
  | nil s =>
    exact ⟨[], ⟨.nil s, by simp [MGraph.walkVertices]⟩, Finset.Subset.refl _, fun _ h => h⟩
  | @cons u₀ v₀ x₀ P₀ he hsrc hrest ih =>
    obtain ⟨Q, ⟨hQw, hQnd⟩, hQedges, hQverts⟩ := ih
    by_cases huQ : u₀ ∈ G.walkVertices (G.dst x₀) Q
    · obtain ⟨Q₁, Q₂, hEq, hQ₁, hQ₂⟩ := walkVertices_mem_split hQw huQ
      have hQnd_split : (G.walkVertices (G.dst x₀) Q₁ ++ Q₂.map G.dst).Nodup := by
        simpa [hEq, walkVertices_append] using hQnd
      have hdisj := List.nodup_append.mp hQnd_split
      have hu_in_Q1 : u₀ ∈ G.walkVertices (G.dst x₀) Q₁ := IsWalk_end_mem_walkVertices hQ₁
      have hu_not_Q2 : u₀ ∉ Q₂.map G.dst := fun h => hdisj.2.2 u₀ hu_in_Q1 u₀ h rfl
      refine ⟨Q₂, ⟨hQ₂, ?_⟩, ?_, ?_⟩
      · rw [MGraph.walkVertices]
        exact List.nodup_cons.mpr ⟨hu_not_Q2, hdisj.2.1⟩
      · intro e he'
        have heQ : e ∈ walkEdges Q := by
          rw [hEq, walkEdges_append, Finset.mem_union]
          exact Or.inr he'
        rw [walkEdges_cons, Finset.mem_insert]
        exact Or.inr (hQedges heQ)
      · intro w hw
        rw [walkVertices_cons, List.mem_cons]
        simp only [MGraph.walkVertices, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact Or.inl rfl
        · refine Or.inr (hQverts w ?_)
          rw [hEq, walkVertices_append, List.mem_append]
          exact Or.inr hw
    · refine ⟨x₀ :: Q, ⟨.cons he hsrc hQw, ?_⟩, ?_, ?_⟩
      · rw [walkVertices_cons]
        exact List.nodup_cons.mpr ⟨huQ, hQnd⟩
      · intro e he'
        rw [walkEdges_cons, Finset.mem_insert] at he' ⊢
        rcases he' with rfl | he'
        · exact Or.inl rfl
        · exact Or.inr (hQedges he')
      · intro w hw
        rw [walkVertices_cons, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · exact Or.inl rfl
        · exact Or.inr (hQverts w hw)

/-! ## Edge distinctness and flow vectors of simple paths -/

lemma IsPath_append_left {G : MGraph} {u w v : ℕ} {P Q : List (ℕ × Bool)}
    (hPQ : G.IsPath u v (P ++ Q)) (hP : G.IsWalk u w P) : G.IsPath u w P := by
  refine ⟨hP, ?_⟩
  have hnd := hPQ.2
  rw [walkVertices_append] at hnd
  exact (List.nodup_append.mp hnd).1

lemma IsPath_append_right {G : MGraph} {u w v : ℕ} {P Q : List (ℕ × Bool)}
    (hPQ : G.IsPath u v (P ++ Q)) (hP : G.IsWalk u w P) (hQ : G.IsWalk w v Q) :
    G.IsPath w v Q := by
  refine ⟨hQ, ?_⟩
  have hnd := hPQ.2
  rw [walkVertices_append] at hnd
  have hsp := List.nodup_append.mp hnd
  have hw_in_P : w ∈ G.walkVertices u P := IsWalk_end_mem_walkVertices hP
  have hw_not_Q : w ∉ Q.map G.dst := fun h => hsp.2.2 w hw_in_P w h rfl
  exact List.nodup_cons.mpr ⟨hw_not_Q, hsp.2.1⟩

lemma IsWalk_mem_ends {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) {y : ℕ × Bool} (hy : y ∈ P) :
    G.src y ∈ G.walkVertices u P ∧ G.dst y ∈ G.walkVertices u P := by
  induction hP with
  | nil _ => simp at hy
  | @cons u₀ _ x₀ P₀ _ hsrc _ ih =>
    rw [List.mem_cons] at hy
    rw [walkVertices_cons]
    rcases hy with rfl | hy
    · refine ⟨by rw [hsrc]; exact List.mem_cons_self, ?_⟩
      exact List.mem_cons_of_mem _ (IsWalk_start_mem_walkVertices G (G.dst y) P₀)
    · obtain ⟨h1, h2⟩ := ih hy
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

lemma isPath_nodup_edges {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) : (P.map Prod.fst).Nodup := by
  rcases hP with ⟨hw, hnd⟩
  induction hw with
  | nil _ => simp
  | @cons u₀ _ x₀ P₀ he hsrc hrest ih =>
    rw [walkVertices_cons] at hnd
    have hnd_cons := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd_cons.2⟩
    intro hx0
    rw [List.mem_map] at hx0
    obtain ⟨y, hyP0, hy1⟩ := hx0
    have hy_in := IsWalk_mem_ends hrest hyP0
    have hsrc_eq : u₀ = G.src x₀ := hsrc.symm
    have hu_is_end : u₀ = G.src y ∨ u₀ = G.dst y := by
      rw [hsrc_eq]
      rcases x₀ with ⟨e1, _ | _⟩ <;> rcases y with ⟨e2, _ | _⟩ <;>
        simp only [MGraph.src, MGraph.dst] at hy1 ⊢ <;>
        (try simp only [hy1]) <;> tauto
    rcases hu_is_end with rfl | rfl
    · exact hnd_cons.1 hy_in.1
    · exact hnd_cons.1 hy_in.2

lemma walkFlow_eq_zero_of_not_mem {P : List (ℕ × Bool)} {e : ℕ} (he : e ∉ walkEdges P) :
    walkFlow P e = 0 := by
  simp only [walkFlow]
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hyP, rfl⟩ := hx
  have hne : y.1 ≠ e := fun h => he (h ▸ mem_walkEdges_of_mem hyP)
  simp [hne]

lemma walkFlow_abs_of_nodup {P : List (ℕ × Bool)} (hnd : (P.map Prod.fst).Nodup) (e : ℕ) :
    |walkFlow P e| = if e ∈ walkEdges P then 1 else 0 := by
  induction P with
  | nil => simp [walkFlow, walkEdges]
  | cons x P ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ih' := ih hnd.2
    simp only [walkFlow, List.map_cons, List.sum_cons] at ih' ⊢
    by_cases hxe : x.1 = e
    · subst hxe
      have heP : x.1 ∉ walkEdges P := by
        simpa [walkEdges, List.mem_toFinset] using hnd.1
      have hz := walkFlow_eq_zero_of_not_mem heP
      simp only [walkFlow] at hz
      rw [hz, add_zero]
      have he_mem : x.1 ∈ walkEdges (x :: P) := by
        rw [walkEdges_cons]
        exact Finset.mem_insert_self _ _
      rw [ite_eq_left_iff.mpr (fun h => absurd he_mem h)]
      cases x.2 <;> norm_num
    · have he_iff : e ∈ walkEdges (x :: P) ↔ e ∈ walkEdges P := by
        rw [walkEdges_cons, Finset.mem_insert, or_iff_right (Ne.symm hxe)]
      simp only [hxe, ↓reduceIte, zero_add, he_iff]
      exact ih'

lemma walkLength_eq_sum_of_nodup (ℓ : ℕ → ℝ) {P : List (ℕ × Bool)}
    (hnd : (P.map Prod.fst).Nodup) :
    walkLength ℓ P = ∑ e ∈ walkEdges P, ℓ e := by
  simp only [walkLength]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [walkFlow_abs_of_nodup hnd e, ite_eq_left_iff.mpr (fun h => absurd he h), mul_one]

lemma walkLength_eq_sum_of_isPath {G : MGraph} (ℓ : ℕ → ℝ) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) :
    walkLength ℓ P = ∑ e ∈ walkEdges P, ℓ e :=
  walkLength_eq_sum_of_nodup ℓ (isPath_nodup_edges hP)

lemma walkLength_nonneg_of_nonneg (ℓ : ℕ → ℝ) {P : List (ℕ × Bool)}
    (hℓ : ∀ e ∈ walkEdges P, 0 ≤ ℓ e) :
    0 ≤ walkLength ℓ P := by
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (hℓ e he) (abs_nonneg _)

/-! ## Connectedness -/

lemma connected_refl (G : MGraph) (u : ℕ) : G.Connected u u :=
  ⟨[], .nil u⟩

lemma connected_symm {G : MGraph} {u v : ℕ} (h : G.Connected u v) : G.Connected v u := by
  obtain ⟨P, hP⟩ := h
  exact ⟨walkRev P, IsWalk_walkRev hP⟩

lemma connected_trans {G : MGraph} {u w v : ℕ}
    (h1 : G.Connected u w) (h2 : G.Connected w v) : G.Connected u v := by
  obtain ⟨P, hP⟩ := h1
  obtain ⟨Q, hQ⟩ := h2
  exact ⟨P ++ Q, IsWalk_append hP hQ⟩

lemma connected_of_edge {G : MGraph} {e : ℕ} (he : e ∈ G.E) :
    G.Connected (G.tail e) (G.head e) :=
  ⟨[(e, true)], .cons he rfl (.nil (G.head e))⟩

lemma connected_isPath {G : MGraph} {u v : ℕ} (h : G.Connected u v) :
    ∃ P, G.IsPath u v P := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨P, hP, _⟩ := exists_isPath_of_isWalk hW
  exact ⟨P, hP⟩

/-! ## Subgraph path lifting and forest properties -/

lemma isWalk_of_subgraph {F H : MGraph} (hsub : H.IsSubgraph F) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : F.IsWalk u v P) :
    H.IsWalk u v P ∧ F.walkVertices u P = H.walkVertices u P := by
  induction hP with
  | nil s => exact ⟨.nil s, rfl⟩
  | @cons u₀ v₀ x₀ P₀ he hsrc _ ih =>
    have hend := hsub.2.2 x₀.1 he
    have hsrc' : H.src x₀ = u₀ := by
      rw [← hsrc]
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.src, hend.1, hend.2]
    have hdst' : H.dst x₀ = F.dst x₀ := by
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hend.1, hend.2]
    obtain ⟨ihw, ihv⟩ := ih
    rw [← hdst'] at ihw ihv
    refine ⟨.cons (hsub.2.1 he) hsrc' ihw, ?_⟩
    rw [walkVertices_cons, walkVertices_cons, hdst']
    exact congrArg (u₀ :: ·) (by simpa [hdst'] using ihv)

lemma isPath_of_subgraph {F H : MGraph} (hsub : H.IsSubgraph F) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : F.IsPath u v P) : H.IsPath u v P := by
  obtain ⟨hw, hverts⟩ := isWalk_of_subgraph hsub hP.1
  exact ⟨hw, hverts ▸ hP.2⟩

lemma connected_of_subgraph {F H : MGraph} (hsub : H.IsSubgraph F) {u v : ℕ}
    (h : F.Connected u v) : H.Connected u v := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, (isWalk_of_subgraph hsub hP).1⟩

lemma isForest_no_selfLoop {F : MGraph} (hF : F.IsForest) {e : ℕ} (he : e ∈ F.E) :
    F.tail e ≠ F.head e := by
  intro hEq
  refine hF.2 [(e, true)] ⟨by simp, by simp, F.tail e, ?_⟩
  exact .cons he rfl (by simpa [MGraph.dst, hEq] using MGraph.IsWalk.nil (F.tail e))

lemma isForest_subgraph {F H : MGraph} (hF : F.IsForest) (hsub : F.IsSubgraph H)
    (hvalid : H.IsValid) : H.IsForest := by
  refine ⟨hvalid, fun P hcyc => ?_⟩
  rcases hcyc with ⟨hne, hnd, u, hw⟩
  exact hF.2 P ⟨hne, hnd, u, (isWalk_of_subgraph hsub hw).1⟩

lemma isForest_eraseEdge {F : MGraph} (hF : F.IsForest) (e : ℕ) :
    ({ F with E := F.E.erase e } : MGraph).IsForest := by
  have hvalid : ({ F with E := F.E.erase e } : MGraph).IsValid := by
    intro x hx
    exact hF.1 x (Finset.mem_of_mem_erase hx)
  exact isForest_subgraph hF ⟨Finset.Subset.refl _, Finset.erase_subset e F.E, fun _ _ => ⟨rfl, rfl⟩⟩ hvalid

private lemma isWalk_of_insertVertex {F : MGraph} {v u w : ℕ} {P : List (ℕ × Bool)}
    (hP : ({ F with V := insert v F.V } : MGraph).IsWalk u w P) : F.IsWalk u w P := by
  induction hP with
  | nil s => exact .nil s
  | cons he hs _ ih => exact .cons he hs ih

lemma isForest_insertVertex {F : MGraph} (hF : F.IsForest) (v : ℕ) :
    ({ F with V := insert v F.V } : MGraph).IsForest := by
  refine ⟨fun x hx => ?_, fun P hcyc => ?_⟩
  · have h := hF.1 x hx
    exact ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_of_mem h.2⟩
  · rcases hcyc with ⟨hne, hnd, u, hw⟩
    exact hF.2 P ⟨hne, hnd, u, isWalk_of_insertVertex hw⟩

lemma IsPath_nil_of_eq {G : MGraph} {u : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u u P) : P = [] := by
  cases P with
  | nil => rfl
  | cons x P₀ =>
    exfalso
    have hnd := hP.2
    rw [walkVertices_cons] at hnd
    have h1 := (List.nodup_cons.mp hnd).1
    have h2 : u ∈ G.walkVertices (G.dst x) P₀ := by
      cases hP.1 with
      | cons _ _ hrest => exact IsWalk_end_mem_walkVertices hrest
    exact h1 h2

lemma IsPath_walk_endpoints_disjoint_edges {F : MGraph} (hF : F.IsForest) {u w : ℕ}
    {A B : List (ℕ × Bool)} (hA : F.IsPath u w A) (hB : F.IsPath u w B)
    (hdisj_verts : ∀ z ∈ A.map F.src, z = u ∨ z ∉ F.walkVertices u B) :
    A = B ∨ Disjoint (A.map Prod.fst).toFinset (B.map Prod.fst).toFinset := by
  by_cases hAB : A = B
  · exact Or.inl hAB
  · right
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [List.mem_toFinset, List.mem_map] at heA heB
    obtain ⟨a, haA, rfl⟩ := heA
    obtain ⟨b, hbB, hab⟩ := heB
    have ha_in_F : a.1 ∈ F.E := IsWalk_edges_mem hA.1 haA
    have hne_ends : F.src a ≠ F.dst a := by
      have hnl := isForest_no_selfLoop hF ha_in_F
      cases ha2 : a.2 <;> simp [MGraph.src, MGraph.dst, ha2, hnl, Ne.symm hnl]
    have hsameset : ({F.src a, F.dst a} : Set ℕ) = {F.src b, F.dst b} := by
      cases ha2 : a.2 <;> cases hb2 : b.2 <;> simp [MGraph.src, MGraph.dst, ha2, hb2, hab]
      · exact Set.pair_comm _ _
      · exact Set.pair_comm _ _
    have hb_ends := IsWalk_mem_ends hB.1 hbB
    have hsrc_in_B : F.src a ∈ F.walkVertices u B := by
      have hmem : F.src a ∈ ({F.src b, F.dst b} : Set ℕ) := by rw [← hsameset]; simp
      rcases hmem with h | h <;> [exact h ▸ hb_ends.1; exact h ▸ hb_ends.2]
    have hdst_in_B : F.dst a ∈ F.walkVertices u B := by
      have hmem : F.dst a ∈ ({F.src b, F.dst b} : Set ℕ) := by rw [← hsameset]; simp
      rcases hmem with h | h <;> [exact h ▸ hb_ends.1; exact h ▸ hb_ends.2]
    have hsrc_eq_u : F.src a = u := by
      rcases hdisj_verts (F.src a) (List.mem_map_of_mem haA) with h | h
      · exact h
      · exact absurd hsrc_in_B h
    obtain ⟨A₁, A₂, hEqA, hA1, hA2⟩ := IsWalk_mem_split_edge hA.1 haA
    have hA1_nil : A₁ = [] := by
      have hAp := IsPath_append_left (hEqA ▸ hA) hA1
      rw [hsrc_eq_u] at hAp
      exact IsPath_nil_of_eq hAp
    have hA2_nil : A₂ = [] := by
      cases A₂ with
      | nil => rfl
      | cons a2 A₂' =>
        exfalso
        have hdst_src : F.dst a ∈ A.map F.src := by
          rw [hEqA, hA1_nil, List.nil_append, List.map_cons, List.map_cons, List.mem_cons]
          right
          cases hA2 with
          | cons _ hs2 _ => rw [hs2]; exact List.mem_cons_self
        rcases hdisj_verts (F.dst a) hdst_src with h | h
        · exact hne_ends (hsrc_eq_u.trans h.symm)
        · exact h hdst_in_B
    have hA_eq : A = [a] := by simpa [hA1_nil, hA2_nil] using hEqA
    have hw_eq_dst : w = F.dst a := by
      rw [hA_eq] at hA
      cases hA.1 with | cons _ _ hr => cases hr; rfl
    have hu_ne_w : u ≠ w := by rw [← hsrc_eq_u, hw_eq_dst]; exact hne_ends
    obtain ⟨B₁, B₂, hEqB, hB1, hB2⟩ := IsWalk_mem_split_edge hB.1 hbB
    have huw : ({u, w} : Set ℕ) = {F.src b, F.dst b} := by
      rw [← hsrc_eq_u, hw_eq_dst]; exact hsameset
    have hsrc_b_eq : F.src b = u := by
      have hsb : F.src b ∈ ({u, w} : Set ℕ) := by rw [huw]; simp
      rcases hsb with h | h
      · exact h
      · exfalso
        have hBp := IsPath_append_right (hEqB ▸ hB) hB1 (.cons (IsWalk_edges_mem hB.1 hbB) rfl hB2)
        rw [h] at hBp
        exact List.cons_ne_nil b B₂ (IsPath_nil_of_eq hBp)
    have hdst_b_eq : F.dst b = w := by
      have hdb : F.dst b ∈ ({u, w} : Set ℕ) := by rw [huw]; simp
      rcases hdb with h | h
      · exfalso
        have hB_pref := IsPath_append_left (P := B₁ ++ [b]) (Q := B₂)
          (by simpa [hEqB, List.append_assoc] using hB)
          (IsWalk_append hB1 (.cons (IsWalk_edges_mem hB.1 hbB) rfl (.nil (F.dst b))))
        rw [h] at hB_pref
        have hnil := IsPath_nil_of_eq hB_pref
        simp at hnil
      · exact h
    have hB1_nil : B₁ = [] := by
      have hBp := IsPath_append_left (hEqB ▸ hB) hB1
      rw [hsrc_b_eq] at hBp
      exact IsPath_nil_of_eq hBp
    have hB2_nil : B₂ = [] := by
      have hBp := IsPath_append_right (P := B₁ ++ [b]) (Q := B₂)
        (by simpa [hEqB, List.append_assoc] using hB)
        (IsWalk_append hB1 (.cons (IsWalk_edges_mem hB.1 hbB) rfl (.nil (F.dst b)))) hB2
      rw [hdst_b_eq] at hBp
      exact IsPath_nil_of_eq hBp
    have hB_eq : B = [b] := by simpa [hB1_nil, hB2_nil] using hEqB
    have hab2 : a.2 = b.2 := by
      rcases a with ⟨ea, _ | _⟩ <;> rcases b with ⟨eb, _ | _⟩
      · rfl
      · exfalso
        have heab : eb = ea := hab
        subst heab
        simp only [MGraph.src, MGraph.dst] at hsrc_eq_u hsrc_b_eq hw_eq_dst hdst_b_eq
        exact hu_ne_w (hsrc_eq_u.symm.trans hdst_b_eq)
      · exfalso
        have heab : eb = ea := hab
        subst heab
        simp only [MGraph.src, MGraph.dst] at hsrc_eq_u hsrc_b_eq hw_eq_dst hdst_b_eq
        exact hu_ne_w (hsrc_eq_u.symm.trans hdst_b_eq)
      · rfl
    have hab_eq : a = b := Prod.ext hab.symm hab2
    exact hAB (by rw [hA_eq, hB_eq, hab_eq])

lemma isPath_unique {F : MGraph} (hF : F.IsForest) {u v : ℕ} {P Q : List (ℕ × Bool)}
    (hP : F.IsPath u v P) (hQ : F.IsPath u v Q) : P = Q := by
  induction P generalizing u Q with
  | nil =>
    cases hP.1
    exact (IsPath_nil_of_eq hQ).symm
  | cons x P₀ ih =>
    cases Q with
    | nil =>
      cases hQ.1
      exact absurd (IsPath_nil_of_eq hP) (by simp)
    | cons y Q₀ =>
      by_cases hxy : x = y
      · subst hxy
        have hPx : F.IsPath (F.dst x) v P₀ :=
          IsPath_append_right (P := [x]) (Q := P₀) hP
            (by cases hP.1 with | cons he hs _ => exact .cons he hs (.nil _))
            (by cases hP.1 with | cons _ _ hr => exact hr)
        have hQx : F.IsPath (F.dst x) v Q₀ :=
          IsPath_append_right (P := [x]) (Q := Q₀) hQ
            (by cases hQ.1 with | cons he hs _ => exact .cons he hs (.nil _))
            (by cases hQ.1 with | cons _ _ hr => exact hr)
        rw [ih hPx hQx]
      · exfalso
        have hP_dst_walk : F.IsWalk (F.dst x) v P₀ := by
          cases hP.1 with | cons _ _ hr => exact hr
        have hx_edge : x.1 ∈ F.E ∧ F.src x = u := by
          cases hP.1 with | cons he hs _ => exact ⟨he, hs⟩
        let S : Finset ℕ := (F.walkVertices u (y :: Q₀)).toFinset
        have hv_mem : v ∈ S := by
          simp only [S, List.mem_toFinset]
          exact IsWalk_end_mem_walkVertices hQ.1
        obtain ⟨P₁, P₂, w, hEqP, hP1, hP2, hwS, hmin⟩ := IsWalk_firstHit S hP_dst_walk hv_mem
        have hw_in_Q : w ∈ F.walkVertices u (y :: Q₀) := by simpa [S] using hwS
        obtain ⟨B, B', hEqQ, hBw, hB'⟩ := walkVertices_mem_split hQ.1 hw_in_Q
        let A := x :: P₁
        have hAw : F.IsWalk u w A := .cons hx_edge.1 hx_edge.2 hP1
        have hAp : F.IsPath u w A := IsPath_append_left (P := A) (Q := P₂)
          (by simpa [A, hEqP, List.cons_append] using hP) hAw
        have hBp : F.IsPath u w B := IsPath_append_left (P := B) (Q := B')
          (by simpa [hEqQ] using hQ) hBw
        have hdisj_v : ∀ z ∈ A.map F.src, z = u ∨ z ∉ F.walkVertices u B := by
          intro z hz
          simp only [A, List.map_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact Or.inl hx_edge.2
          · right
            intro hzB
            have hzS : z ∈ S := by
              simp only [S, List.mem_toFinset]
              rw [hEqQ, walkVertices_append, List.mem_append]
              exact Or.inl hzB
            exact hmin z hz hzS
        have hA_ne_B : A ≠ B := by
          intro hEqAB
          rcases B with _ | ⟨b0, B₀⟩
          · exact List.cons_ne_nil x P₁ hEqAB
          · have hxb : x = b0 := (List.cons.inj hEqAB).1
            have hyb : y = b0 := (List.cons.inj hEqQ).1
            exact hxy (hxb.trans hyb.symm)
        have hdisj_e :=
          (IsPath_walk_endpoints_disjoint_edges hF hAp hBp hdisj_v).resolve_left hA_ne_B
        refine hF.2 (A ++ walkRev B) ⟨by simp [A], ?_, u, IsWalk_append hAw (IsWalk_walkRev hBw)⟩
        rw [List.map_append, List.nodup_append]
        refine ⟨isPath_nodup_edges hAp, isPath_nodup_edges (IsPath_walkRev hBp), ?_⟩
        intro e heA _ heB hEqe
        subst hEqe
        rw [Finset.disjoint_left] at hdisj_e
        have he1 : e ∈ (A.map Prod.fst).toFinset := by simpa using heA
        have he2 : e ∈ (B.map Prod.fst).toFinset := by
          have : e ∈ walkEdges (walkRev B) := by simpa [walkEdges] using heB
          rw [walkEdges_walkRev] at this
          simpa [walkEdges] using this
        exact hdisj_e he1 he2

lemma forestPath_eq_of_isPath {F : MGraph} (hF : F.IsForest) {u v : ℕ}
    {P : List (ℕ × Bool)} (hP : F.IsPath u v P) : F.forestPath u v = P := by
  unfold MGraph.forestPath
  have hex : ∃ Q, F.IsPath u v Q := ⟨P, hP⟩
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact isPath_unique hF (Classical.choose_spec hex) hP

lemma forestPath_isPath {F : MGraph} (hF : F.IsForest) {u v : ℕ}
    (h : F.Connected u v) : F.IsPath u v (F.forestPath u v) := by
  obtain ⟨P, hP⟩ := connected_isPath h
  rw [forestPath_eq_of_isPath hF hP]
  exact hP

lemma forestPath_self {F : MGraph} (hF : F.IsForest) (u : ℕ) :
    F.forestPath u u = [] :=
  forestPath_eq_of_isPath hF ⟨.nil u, by simp [MGraph.walkVertices]⟩

lemma forestPath_rev {F : MGraph} (hF : F.IsForest) {u v : ℕ}
    (h : F.Connected u v) : F.forestPath v u = walkRev (F.forestPath u v) :=
  forestPath_eq_of_isPath hF (IsPath_walkRev (forestPath_isPath hF h))

lemma forestPath_subgraph {F H : MGraph} (hH : H.IsForest) (hsub : H.IsSubgraph F)
    {u v : ℕ} (h : F.Connected u v) : F.forestPath u v = H.forestPath u v := by
  obtain ⟨P, hP⟩ := connected_isPath h
  have hex : ∃ Q, F.IsPath u v Q := ⟨P, hP⟩
  unfold MGraph.forestPath
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact (forestPath_eq_of_isPath hH (isPath_of_subgraph hsub (Classical.choose_spec hex))).symm

lemma not_connected_erase_of_mem_forestPath {F : MGraph} (hF : F.IsForest)
    {u v e : ℕ} (he : e ∈ walkEdges (F.forestPath u v)) :
    ¬ ({ F with E := F.E.erase e } : MGraph).Connected u v := by
  intro hconn
  obtain ⟨P, hP⟩ := connected_isPath hconn
  have hsub : F.IsSubgraph { F with E := F.E.erase e } :=
    ⟨Finset.Subset.refl _, Finset.erase_subset e F.E, fun _ _ => ⟨rfl, rfl⟩⟩
  have hP_F : F.IsPath u v P := isPath_of_subgraph hsub hP
  have hEq : P = F.forestPath u v := (forestPath_eq_of_isPath hF hP_F).symm
  rw [← hEq] at he
  simp only [walkEdges, List.mem_toFinset, List.mem_map] at he
  obtain ⟨a, haP, rfl⟩ := he
  have haE := IsWalk_edges_mem hP.1 haP
  exact (Finset.notMem_erase a.1 F.E) haE

lemma mem_walkEdges_forestPath_of_isWalk {F : MGraph} (hF : F.IsForest)
    {u v : ℕ} {P : List (ℕ × Bool)} (hP : F.IsWalk u v P) :
    walkEdges (F.forestPath u v) ⊆ walkEdges P := by
  obtain ⟨Q, hQ, hQsub, _⟩ := exists_isPath_of_isWalk hP
  rwa [forestPath_eq_of_isPath hF hQ]

lemma forestPath_mem_walkVertices_split {F : MGraph} (hF : F.IsForest) {u v w : ℕ}
    (huv : F.Connected u v) (hw : w ∈ F.walkVertices u (F.forestPath u v)) :
    F.forestPath u v = F.forestPath u w ++ F.forestPath w v ∧
      Disjoint (walkEdges (F.forestPath u w)) (walkEdges (F.forestPath w v)) := by
  have hP := forestPath_isPath hF huv
  obtain ⟨P₁, P₂, hEq, h1, h2⟩ := walkVertices_mem_split hP.1 hw
  have hP1 : F.IsPath u w P₁ := IsPath_append_left (hEq ▸ hP) h1
  have hP2 : F.IsPath w v P₂ := IsPath_append_right (hEq ▸ hP) h1 h2
  have h1eq := forestPath_eq_of_isPath hF hP1
  have h2eq := forestPath_eq_of_isPath hF hP2
  refine ⟨by rw [hEq, h1eq, h2eq], ?_⟩
  have hnd := isPath_nodup_edges hP
  rw [hEq, List.map_append, List.nodup_append] at hnd
  rw [h1eq, h2eq, Finset.disjoint_left]
  intro e he1 he2
  simp only [walkEdges, List.mem_toFinset] at he1 he2
  exact hnd.2.2 e he1 e he2 rfl

lemma forestPath_concat_of_disjoint {F : MGraph} (hF : F.IsForest) {u w v : ℕ}
    (huw : F.Connected u w) (hwv : F.Connected w v)
    (hdisj : Disjoint (walkEdges (F.forestPath u w)) (walkEdges (F.forestPath w v))) :
    F.forestPath u v = F.forestPath u w ++ F.forestPath w v := by
  have hP1 := forestPath_isPath hF huw
  have hP2 := forestPath_isPath hF hwv
  refine forestPath_eq_of_isPath hF ⟨IsWalk_append hP1.1 hP2.1, ?_⟩
  rw [walkVertices_append]
  have hnd1 := hP1.2
  have hnd2 := hP2.2
  have hmap_nd : ((F.forestPath w v).map F.dst).Nodup := by
    rw [MGraph.walkVertices] at hnd2
    exact (List.nodup_cons.mp hnd2).2
  rw [List.nodup_append]
  refine ⟨hnd1, hmap_nd, ?_⟩
  intro z hz1 z' hz2 hzz'
  subst hzz'
  have hz_in_2 : z ∈ F.walkVertices w (F.forestPath w v) := List.mem_cons_of_mem w hz2
  have hzw : z ≠ w := by
    intro hEq
    subst hEq
    rw [MGraph.walkVertices] at hnd2
    exact (List.nodup_cons.mp hnd2).1 hz2
  obtain ⟨P1_l, A, hEq1, hP1_l, hA⟩ := walkVertices_mem_split hP1.1 hz1
  have hAp : F.IsPath z w A := IsPath_append_right (hEq1 ▸ hP1) hP1_l hA
  obtain ⟨B, _, hEq2, hB, _⟩ := walkVertices_mem_split hP2.1 hz_in_2
  have hBp : F.IsPath w z B := IsPath_append_left (hEq2 ▸ hP2) hB
  have hEqAB : A = walkRev B :=
    (forestPath_eq_of_isPath hF hAp).symm.trans (forestPath_eq_of_isPath hF (IsPath_walkRev hBp))
  have hAne : A ≠ [] := by
    intro hnil
    subst hnil
    cases hA
    exact hzw rfl
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil A hAne
  have he1 : a.1 ∈ walkEdges (F.forestPath u w) := by
    rw [hEq1, walkEdges_append, Finset.mem_union]
    exact Or.inr (mem_walkEdges_of_mem ha)
  have he2 : a.1 ∈ walkEdges (F.forestPath w v) := by
    have haB : a.1 ∈ walkEdges (walkRev B) := by
      rw [← hEqAB]
      exact mem_walkEdges_of_mem ha
    rw [walkEdges_walkRev] at haB
    rw [hEq2, walkEdges_append, Finset.mem_union]
    exact Or.inl haB
  exact Finset.disjoint_left.mp hdisj he1 he2

end MinCostFlow.LSF
