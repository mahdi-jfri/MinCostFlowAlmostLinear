module

public import MinCostFlow.Chain.Lemma5_11
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete Kruskal MSF and Concrete Restart Tool Instances (Examples Helpers)

Split from `MinCostFlow.Chain.Examples`: `KruskalMSF` (`kruskalLSF_holds`) and
`ConcreteTools` (`exLastTool`, `exCoreTool`, `exCoreTool_spec_on_noUpdate`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section KruskalMSF

noncomputable def insertByLen (ℓ : ℕ → ℝ) (e : ℕ) : List ℕ → List ℕ
  | [] => [e]
  | x :: xs => open Classical in if ℓ e ≤ ℓ x then e :: x :: xs else x :: insertByLen ℓ e xs

noncomputable def sortByLen (ℓ : ℕ → ℝ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertByLen ℓ x (sortByLen ℓ xs)

private lemma mem_insertByLen (ℓ : ℕ → ℝ) (e a : ℕ) (xs : List ℕ) :
    a ∈ insertByLen ℓ e xs ↔ a = e ∨ a ∈ xs := by
  induction xs with
  | nil => simp [insertByLen]
  | cons x xs ih =>
    dsimp only [insertByLen]
    split_ifs with h
    · simp [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

private lemma mem_sortByLen (ℓ : ℕ → ℝ) (a : ℕ) (xs : List ℕ) :
    a ∈ sortByLen ℓ xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [sortByLen]
  | cons x xs ih =>
    simp only [sortByLen, mem_insertByLen, List.mem_cons, ih]

private lemma pairwise_insertByLen (ℓ : ℕ → ℝ) (e : ℕ) (xs : List ℕ)
    (hxs : xs.Pairwise (fun a b => ℓ a ≤ ℓ b)) :
    (insertByLen ℓ e xs).Pairwise (fun a b => ℓ a ≤ ℓ b) := by
  induction xs with
  | nil => simp [insertByLen]
  | cons x xs ih =>
    dsimp only [insertByLen]
    split_ifs with h
    · refine List.pairwise_cons.mpr ⟨?_, hxs⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h
      · exact le_trans h ((List.pairwise_cons.mp hxs).1 y hy)
    · have hx : ∀ y ∈ xs, ℓ x ≤ ℓ y := (List.pairwise_cons.mp hxs).1
      have htail : xs.Pairwise (fun a b => ℓ a ≤ ℓ b) := (List.pairwise_cons.mp hxs).2
      refine List.pairwise_cons.mpr ⟨?_, ih htail⟩
      intro y hy
      rw [mem_insertByLen] at hy
      rcases hy with rfl | hy
      · exact le_of_not_ge h
      · exact hx y hy

private lemma pairwise_sortByLen (ℓ : ℕ → ℝ) (xs : List ℕ) :
    (sortByLen ℓ xs).Pairwise (fun a b => ℓ a ≤ ℓ b) := by
  induction xs with
  | nil => simp [sortByLen]
  | cons x xs ih => exact pairwise_insertByLen ℓ x (sortByLen ℓ xs) ih

private lemma isWalk_split {G : MGraph} :
    ∀ {u v : ℕ} {P₁ P₂ : List (ℕ × Bool)} {x : ℕ × Bool},
      G.IsWalk u v (P₁ ++ x :: P₂) →
      G.IsWalk u (G.src x) P₁ ∧ x.1 ∈ G.E ∧ G.IsWalk (G.dst x) v P₂
  | _, _, [], _, _, hW => by
    cases hW with
    | cons he hsrc hrest => exact ⟨hsrc ▸ .nil _, he, hrest⟩
  | _, _, y :: P₁, P₂, x, hW => by
    cases hW with
    | cons he hsrc hrest =>
      have ⟨h1, h2, h3⟩ := isWalk_split hrest
      exact ⟨.cons he hsrc h1, h2, h3⟩

private lemma isWalk_of_edges_mem {G H : MGraph} (ht : H.tail = G.tail) (hh : H.head = G.head)
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : G.IsWalk u v P) (hE : ∀ y ∈ P, y.1 ∈ H.E) :
    H.IsWalk u v P := by
  induction hW with
  | nil z => exact .nil z
  | @cons a b x Q _ hsrc _ ih =>
    have hxE : x.1 ∈ H.E := hE x (by simp)
    have hsrc' : H.src x = a := by
      cases hx2 : x.2 <;> simp [MGraph.src, hx2, ht, hh] at hsrc ⊢ <;> exact hsrc
    have hdst' : H.dst x = G.dst x := by
      cases hx2 : x.2 <;> simp [MGraph.dst, hx2, ht, hh]
    exact .cons hxE hsrc' (hdst' ▸ ih (fun y hy => hE y (by simp [hy])))

private lemma addEdge_isForest {F : MGraph} (hF : F.IsForest) {e : ℕ}
    (htV : F.tail e ∈ F.V) (hhV : F.head e ∈ F.V)
    (hnot : ¬ F.Connected (F.tail e) (F.head e)) :
    ({ F with E := insert e F.E } : MGraph).IsForest := by
  let F' : MGraph := { F with E := insert e F.E }
  refine ⟨?_, ?_⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hfF
    · exact ⟨htV, hhV⟩
    · exact hF.1 f hfF
  · intro P hP
    rcases hP with ⟨hPne, hPnd, u, hW⟩
    by_cases hex : ∃ x ∈ P, x.1 ∉ F.E
    · obtain ⟨x, hxP, hxnot⟩ := hex
      have hxF' : x.1 ∈ F'.E := mem_E_of_mem_walkEdges hW (by
        simp only [walkEdges, List.mem_toFinset, List.mem_map]
        exact ⟨x, hxP, rfl⟩)
      have hxe : x.1 = e := by
        rcases Finset.mem_insert.mp hxF' with h | h
        · exact h
        · exact absurd h hxnot
      obtain ⟨P₁, P₂, rfl⟩ := List.append_of_mem hxP
      have hnd_app : (P₁.map Prod.fst).Nodup ∧ (x.1 :: P₂.map Prod.fst).Nodup ∧
          ∀ a ∈ P₁.map Prod.fst, ∀ b ∈ x.1 :: P₂.map Prod.fst, a ≠ b := by
        rw [List.map_append, List.nodup_append] at hPnd
        exact hPnd
      have hxnot1 : x.1 ∉ P₁.map Prod.fst := fun hm => hnd_app.2.2 x.1 hm x.1 (by simp) rfl
      have hxnot2 : x.1 ∉ P₂.map Prod.fst := (List.nodup_cons.mp hnd_app.2.1).1
      have ⟨hW1, _, hW2⟩ := isWalk_split hW
      have hE1 : ∀ y ∈ P₁, y.1 ∈ F.E := by
        intro y hy
        have hyF' : y.1 ∈ F'.E := mem_E_of_mem_walkEdges hW1 (by
          simp only [walkEdges, List.mem_toFinset, List.mem_map]
          exact ⟨y, hy, rfl⟩)
        rcases Finset.mem_insert.mp hyF' with hyEq | hyF
        · have hxmem : x.1 ∈ P₁.map Prod.fst := by
            rw [hxe, ← hyEq]; exact List.mem_map_of_mem hy
          exact absurd hxmem hxnot1
        · exact hyF
      have hE2 : ∀ y ∈ P₂, y.1 ∈ F.E := by
        intro y hy
        have hyF' : y.1 ∈ F'.E := mem_E_of_mem_walkEdges hW2 (by
          simp only [walkEdges, List.mem_toFinset, List.mem_map]
          exact ⟨y, hy, rfl⟩)
        rcases Finset.mem_insert.mp hyF' with hyEq | hyF
        · have hxmem : x.1 ∈ P₂.map Prod.fst := by
            rw [hxe, ← hyEq]; exact List.mem_map_of_mem hy
          exact absurd hxmem hxnot2
        · exact hyF
      have hW1F : F.IsWalk u (F'.src x) P₁ := isWalk_of_edges_mem (G := F') (H := F) rfl rfl hW1 hE1
      have hW2F : F.IsWalk (F'.dst x) u P₂ := isWalk_of_edges_mem (G := F') (H := F) rfl rfl hW2 hE2
      have hConnDstSrc : F.Connected (F'.dst x) (F'.src x) :=
        ⟨P₂ ++ P₁, MGraph.isWalk_append hW2F hW1F⟩
      have hConnEnds : F.Connected (F.tail e) (F.head e) := by
        cases hxb : x.2
        · have : F'.dst x = F.tail e ∧ F'.src x = F.head e := by
            simp [MGraph.src, MGraph.dst, F', hxb, hxe]
          rw [this.1, this.2] at hConnDstSrc
          exact hConnDstSrc
        · have : F'.dst x = F.head e ∧ F'.src x = F.tail e := by
            simp [MGraph.src, MGraph.dst, F', hxb, hxe]
          rw [this.1, this.2] at hConnDstSrc
          exact MGraph.connected_symm hConnDstSrc
      exact hnot hConnEnds
    · push Not at hex
      have hWF : F.IsWalk u u P := isWalk_of_edges_mem (G := F') (H := F) rfl rfl hW hex
      exact hF.2 P ⟨hPne, hPnd, u, hWF⟩

noncomputable def kruskalStep (G F : MGraph) (e : ℕ) : MGraph :=
  open Classical in
  if e ∈ G.E ∧ ¬ F.Connected (G.tail e) (G.head e) then { F with E := insert e F.E } else F

noncomputable def kruskalList (G : MGraph) (xs : List ℕ) (F : MGraph) : MGraph :=
  xs.foldl (kruskalStep G) F

private lemma kruskalList_props (G : MGraph) (hG : G.IsValid) (ℓ : ℕ → ℝ) :
    ∀ (xs : List ℕ) (F : MGraph),
      F.IsForest → F.V = G.V → G.IsSubgraph F → F.tail = G.tail → F.head = G.head →
      xs.Pairwise (fun a b => ℓ a ≤ ℓ b) →
      (∀ f ∈ F.E, ∀ x ∈ xs, ℓ f ≤ ℓ x) →
      let F' := kruskalList G xs F
      F'.IsForest ∧ F'.V = G.V ∧ G.IsSubgraph F' ∧ F'.tail = G.tail ∧ F'.head = G.head ∧
      F.E ⊆ F'.E ∧
      (∀ e ∈ xs, e ∈ G.E → F'.Connected (G.tail e) (G.head e) ∧
        ∃ P, F'.IsPath (G.tail e) (G.head e) P ∧ ∀ y ∈ P, ℓ y.1 ≤ ℓ e)
  | [], F, hF, hV, hSub, ht, hh, _, _ =>
    ⟨hF, hV, hSub, ht, hh, Finset.Subset.refl _, fun _ hx => by cases hx⟩
  | a :: as, F, hF, hV, hSub, ht, hh, hPair, hPrev => by
    dsimp only [kruskalList, List.foldl_cons]
    have hPa := List.pairwise_cons.mp hPair
    set F₁ := kruskalStep G F a
    have hF1_props : F₁.IsForest ∧ F₁.V = G.V ∧ G.IsSubgraph F₁ ∧ F₁.tail = G.tail ∧
        F₁.head = G.head ∧ F.E ⊆ F₁.E ∧ (a ∈ G.E → F₁.Connected (G.tail a) (G.head a)) ∧
        (∀ f ∈ F₁.E, ∀ x ∈ as, ℓ f ≤ ℓ x) := by
      by_cases hAdd : a ∈ G.E ∧ ¬ F.Connected (G.tail a) (G.head a)
      · have hF1_eq : F₁ = { F with E := insert a F.E } := by
          dsimp [F₁, kruskalStep]; simp [hAdd]
        rw [hF1_eq]
        have haEnds := hG a hAdd.1
        have hnotF : ¬ F.Connected (F.tail a) (F.head a) := by
          rw [ht, hh]; exact hAdd.2
        have hF1_for : ({ F with E := insert a F.E } : MGraph).IsForest :=
          addEdge_isForest hF (ht ▸ hV ▸ haEnds.1) (hh ▸ hV ▸ haEnds.2) hnotF
        have hSub1 : G.IsSubgraph { F with E := insert a F.E } := by
          refine ⟨hSub.1, ?_, fun e _ => ⟨ht ▸ rfl, hh ▸ rfl⟩⟩
          intro e he
          rcases Finset.mem_insert.mp he with rfl | heF
          · exact hAdd.1
          · exact hSub.2.1 heF
        refine ⟨hF1_for, hV, hSub1, ht, hh, Finset.subset_insert a F.E, fun _ => ?_, ?_⟩
        · refine ⟨[(a, true)], .cons (Finset.mem_insert_self a F.E) ?_ ?_⟩
          · simp [MGraph.src, ht]
          · simp only [MGraph.dst, hh]; exact .nil _
        · intro f hf x hx
          rcases Finset.mem_insert.mp hf with rfl | hfF
          · exact hPa.1 x hx
          · exact hPrev f hfF x (by simp [hx])
      · have hF1_eq : F₁ = F := by dsimp [F₁, kruskalStep]; simp [hAdd]
        rw [hF1_eq]
        refine ⟨hF, hV, hSub, ht, hh, Finset.Subset.refl _, fun ha => ?_, fun f hf x hx => ?_⟩
        · by_contra hnc; exact hAdd ⟨ha, hnc⟩
        · exact hPrev f hf x (by simp [hx])
    have ih := kruskalList_props G hG ℓ as F₁ hF1_props.1 hF1_props.2.1 hF1_props.2.2.1
      hF1_props.2.2.2.1 hF1_props.2.2.2.2.1 hPa.2 hF1_props.2.2.2.2.2.2.2
    rcases ih with ⟨hF', hV', hSub', ht', hh', hSubE, hxs⟩
    refine ⟨hF', hV', hSub', ht', hh', Finset.Subset.trans hF1_props.2.2.2.2.2.1 hSubE, ?_⟩
    intro e he heG
    simp only [List.mem_cons] at he
    rcases he with rfl | he_as
    · by_cases hconnF : F.Connected (G.tail e) (G.head e)
      · obtain ⟨P, hP⟩ := MGraph.exists_isPath_of_connected hconnF
        have hSubFF' : (kruskalList G as F₁).IsSubgraph F :=
          ⟨by intro v hv; rw [hV] at hv; rw [hV']; exact hv,
            Finset.Subset.trans hF1_props.2.2.2.2.2.1 hSubE,
            fun f _ => ⟨ht ▸ ht' ▸ rfl, hh ▸ hh' ▸ rfl⟩⟩
        have hWF' := MGraph.isWalk_of_isSubgraph hSubFF' hP.1
        have hnd' : ((kruskalList G as F₁).walkVertices (G.tail e) P).Nodup := by
          have hwv : (kruskalList G as F₁).walkVertices (G.tail e) P = F.walkVertices (G.tail e) P := by
            simp [MGraph.walkVertices, MGraph.dst, ht, hh, ht', hh']
          rw [hwv]; exact hP.2
        refine ⟨⟨P, hWF'⟩, P, ⟨hWF', hnd'⟩, fun y hy => ?_⟩
        have hyF : y.1 ∈ F.E := mem_E_of_mem_walkEdges hP.1 (by
          simp only [walkEdges, List.mem_toFinset, List.mem_map]; exact ⟨y, hy, rfl⟩)
        exact hPrev y.1 hyF e (by simp)
      · have hF1_eq : F₁ = { F with E := insert e F.E } := by
          dsimp [F₁, kruskalStep]; simp [heG, hconnF]
        have heF1 : e ∈ F₁.E := by rw [hF1_eq]; exact Finset.mem_insert_self e F.E
        have heF' : e ∈ (kruskalList G as F₁).E := hSubE heF1
        have hnoLoop : (kruskalList G as F₁).tail e ≠ (kruskalList G as F₁).head e :=
          MGraph.no_selfLoop_of_isForest hF' heF'
        rw [ht', hh'] at hnoLoop
        have hW : (kruskalList G as F₁).IsWalk (G.tail e) (G.head e) [(e, true)] :=
          .cons heF' (by simp [MGraph.src, ht']) (by simp only [MGraph.dst, hh']; exact .nil _)
        have hnd : ((kruskalList G as F₁).walkVertices (G.tail e) [(e, true)]).Nodup := by
          simp [MGraph.walkVertices, MGraph.dst, hh', hnoLoop]
        exact ⟨⟨[(e, true)], hW⟩, [(e, true)], ⟨hW, hnd⟩, fun y hy => by
          rw [List.mem_singleton] at hy; rw [hy]⟩
    · exact hxs e he_as heG

noncomputable def kruskalSortedEdges (G : MGraph) (ℓ : ℕ → ℝ) : List ℕ :=
  sortByLen ℓ G.E.toList

/-- Kruskal's minimum-weight spanning forest of `G` with respect to `ℓ`. -/
noncomputable def kruskalForest (G : MGraph) (ℓ : ℕ → ℝ) : MGraph :=
  kruskalList G (kruskalSortedEdges G ℓ) { V := G.V, E := ∅, tail := G.tail, head := G.head }

/-- Canonical component roots for a forest `F` on `G.V`: minimum vertex ID in each `F`-component. -/
noncomputable def kruskalRoots (G F : MGraph) : Finset ℕ :=
  open Classical in
  G.V.filter fun r => ∀ v ∈ G.V, F.Connected r v → r ≤ v

/-- Kruskal LSF on `(G, ℓ)` with `T = F` and `wstr := fun _ => max 1 G.n`. -/
noncomputable def kruskalLSF (G : MGraph) (ℓ : ℕ → ℝ) : LSF :=
  let F := kruskalForest G ℓ
  { T := F
    F := { F := F, R := kruskalRoots G F }
    wstr := fun _ => max 1 (G.n : ℝ) }

private lemma kruskalRoots_spec (G F : MGraph) (_hV : F.V = G.V) :
    ∀ v ∈ G.V, ∃! r, r ∈ kruskalRoots G F ∧ F.Connected v r := by
  classical
  intro v hv
  let comp := G.V.filter (fun w => F.Connected v w)
  have hne : comp.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, MGraph.connected_refl F v⟩⟩
  let r₀ := comp.min' hne
  have hr₀_mem : r₀ ∈ comp := Finset.min'_mem comp hne
  have hr₀_filt := Finset.mem_filter.mp hr₀_mem
  have hr₀R : r₀ ∈ kruskalRoots G F := by
    rw [kruskalRoots, Finset.mem_filter]
    refine ⟨hr₀_filt.1, fun w hwG hrw => ?_⟩
    have hvw : w ∈ comp :=
      Finset.mem_filter.mpr ⟨hwG, MGraph.connected_trans hr₀_filt.2 hrw⟩
    exact Finset.min'_le comp w hvw
  refine ⟨r₀, ⟨hr₀R, hr₀_filt.2⟩, fun r ⟨hrR, hvr⟩ => ?_⟩
  have hrG := (Finset.mem_filter.mp hrR).1
  have hrMin := (Finset.mem_filter.mp hrR).2
  have hrr₀ : F.Connected r r₀ :=
    MGraph.connected_trans (MGraph.connected_symm hvr) hr₀_filt.2
  have hle1 : r ≤ r₀ := hrMin r₀ hr₀_filt.1 hrr₀
  have hle2 : r₀ ≤ r := (Finset.mem_filter.mp hr₀R).2 r hrG (MGraph.connected_symm hrr₀)
  omega

private lemma walkVertices_length_eq (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) :
    (G.walkVertices u P).length = P.length + 1 := by
  simp [MGraph.walkVertices]

private lemma walkLength_le_length_mul_max {ℓ : ℕ → ℝ} {P : List (ℕ × Bool)} {M : ℝ}
    (hM : 0 ≤ M) (_hℓ0 : ∀ y ∈ P, 0 ≤ ℓ y.1) (hℓM : ∀ y ∈ P, ℓ y.1 ≤ M) :
    walkLength ℓ P ≤ (P.length : ℝ) * M := by
  unfold walkLength
  have hle : ∑ e ∈ walkEdges P, ℓ e * |walkFlow P e| ≤
      ∑ e ∈ walkEdges P, M * |walkFlow P e| := by
    refine Finset.sum_le_sum fun e he => ?_
    simp only [walkEdges, List.mem_toFinset, List.mem_map] at he
    obtain ⟨y, hyP, rfl⟩ := he
    exact mul_le_mul_of_nonneg_right (hℓM y hyP) (abs_nonneg _)
  have hsum : ∑ e ∈ walkEdges P, M * |walkFlow P e| = M * ∑ e ∈ walkEdges P, |walkFlow P e| := by
    rw [Finset.mul_sum]
  have hflow := sum_abs_walkFlow_le_length (walkEdges P) P
  calc
    ∑ e ∈ walkEdges P, ℓ e * |walkFlow P e|
        ≤ M * ∑ e ∈ walkEdges P, |walkFlow P e| := hsum ▸ hle
    _ ≤ M * (P.length : ℝ) := mul_le_mul_of_nonneg_left hflow hM
    _ = (P.length : ℝ) * M := mul_comm _ _

theorem kruskalLSF_holds {G : MGraph} (hG : G.IsValid) {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e) :
    let L := kruskalLSF G ℓ
    L.Holds G ℓ (max 1 (G.n : ℝ)) ∧
    G.IsSubgraph L.F.F ∧
    (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v → L.F.F.Connected u v) ∧
    ((∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) → L.F.R.card ≤ 1) := by
  classical
  let F₀ : MGraph := { V := G.V, E := ∅, tail := G.tail, head := G.head }
  have hF0_for : F₀.IsForest := by
    refine ⟨(fun _ h => by cases h), fun P hP => ?_⟩
    rcases hP with ⟨hPne, _, u, hu⟩
    cases P with
    | nil => exact hPne rfl
    | cons x _ => cases hu with | cons he _ _ => cases he
  have hprops := kruskalList_props G hG ℓ (kruskalSortedEdges G ℓ) F₀ hF0_for rfl
    ⟨Finset.Subset.refl _, Finset.empty_subset _, fun _ _ => ⟨rfl, rfl⟩⟩ rfl rfl
    (pairwise_sortByLen ℓ G.E.toList) (fun _ hf => by cases hf)
  rcases hprops with ⟨hF_for, hF_V, hF_sub, hF_tail, hF_head, _, hEdges⟩
  set F := kruskalForest G ℓ
  set L := kruskalLSF G ℓ
  change F.IsForest at hF_for
  change F.V = G.V at hF_V
  change G.IsSubgraph F at hF_sub
  change ∀ e ∈ kruskalSortedEdges G ℓ, e ∈ G.E → F.Connected (G.tail e) (G.head e) ∧
    ∃ P, F.IsPath (G.tail e) (G.head e) P ∧ ∀ y ∈ P, ℓ y.1 ≤ ℓ e at hEdges
  have hRF : L.F.IsRootedSpanningForestOf G := by
    refine ⟨hF_for, hF_V, Finset.filter_subset _ _, kruskalRoots_spec G F hF_V, hF_sub⟩
  have hConnG_all : ∀ u v, G.Connected u v → F.Connected u v := by
    intro u v ⟨P, hP⟩
    induction hP with
    | nil z => exact MGraph.connected_refl F z
    | @cons a b x Q he hsrc _ ih =>
      have hxSorted : x.1 ∈ kruskalSortedEdges G ℓ := by
        rw [kruskalSortedEdges, mem_sortByLen, Finset.mem_toList]
        exact he
      have hxConn := (hEdges x.1 hxSorted he).1
      have hStep : F.Connected (G.src x) (G.dst x) := by
        cases hx2 : x.2
        · simpa [MGraph.src, MGraph.dst, hx2] using MGraph.connected_symm hxConn
        · simpa [MGraph.src, MGraph.dst, hx2] using hxConn
      exact hsrc ▸ MGraph.connected_trans hStep ih
  have hConnG : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v → F.Connected u v :=
    fun u _ v _ h => hConnG_all u v h
  have hRootCard : (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) → L.F.R.card ≤ 1 := by
    intro hConn
    refine Finset.card_le_one.mpr fun r₁ hr₁ r₂ hr₂ => ?_
    have hr1f := Finset.mem_filter.mp hr₁
    have hr2f := Finset.mem_filter.mp hr₂
    have hFconn := hConnG r₁ hr1f.1 r₂ hr2f.1 (hConn r₁ hr1f.1 r₂ hr2f.1)
    have h12 : r₁ ≤ r₂ := hr1f.2 r₂ hr2f.1 hFconn
    have h21 : r₂ ≤ r₁ := hr2f.2 r₁ hr1f.1 (MGraph.connected_symm hFconn)
    omega
  refine ⟨⟨hF_for, hRF, ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩, ?_⟩,
    hF_sub, hConnG, hRootCard⟩
  intro e he
  refine ⟨?_, le_refl _⟩
  have heSorted : e ∈ kruskalSortedEdges G ℓ := by
    rw [kruskalSortedEdges, mem_sortByLen, Finset.mem_toList]; exact he
  obtain ⟨hConnEnds, P, hP, hPwt⟩ := hEdges e heSorted he
  have hEnds := hG e he
  have hRootEq : L.F.root (G.tail e) = L.F.root (G.head e) := by
    have hspec := kruskalRoots_spec G F hF_V
    have hu_ex : ∃ r ∈ L.F.R, L.F.F.Connected (G.tail e) r := (hspec (G.tail e) hEnds.1).exists
    have hv_ex : ∃ r ∈ L.F.R, L.F.F.Connected (G.head e) r := (hspec (G.head e) hEnds.2).exists
    let ru := L.F.root (G.tail e)
    let rv := L.F.root (G.head e)
    have hru : ru ∈ L.F.R ∧ F.Connected (G.tail e) ru := by
      dsimp only [ru, RootedForest.root]; simp only [hu_ex, ↓reduceDIte]
      exact Classical.choose_spec hu_ex
    have hrv : rv ∈ L.F.R ∧ F.Connected (G.head e) rv := by
      dsimp only [rv, RootedForest.root]; simp only [hv_ex, ↓reduceDIte]
      exact Classical.choose_spec hv_ex
    have hurv : F.Connected (G.tail e) rv := MGraph.connected_trans hConnEnds hrv.2
    exact (hspec (G.tail e) hEnds.1).unique hru ⟨hrv.1, hurv⟩
  have hStretchEq : L.F.stretch G ℓ e =
      1 + walkLength ℓ (MGraph.forestPath F (G.tail e) (G.head e)) / ℓ e := by
    unfold RootedForest.stretch
    dsimp only
    simp only [hRootEq, ↓reduceIte]
    rfl
  have hFlowEq := walkFlow_eq_of_isForest hF_for (MGraph.isWalk_forestPath hConnEnds) hP.1
  have hWalkSub : ∀ {Q : List (ℕ × Bool)}, F.IsWalk (G.tail e) (G.head e) Q → walkEdges Q ⊆ F.E :=
    fun hQ f hf => mem_E_of_mem_walkEdges hQ hf
  have hLenEq : walkLength ℓ (MGraph.forestPath F (G.tail e) (G.head e)) = walkLength ℓ P := by
    rw [walkLength_eq_sum_of_subset (hWalkSub (MGraph.isWalk_forestPath hConnEnds)),
      walkLength_eq_sum_of_subset (hWalkSub hP.1)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hFlowEq f]
  have hℓe_pos : 0 < ℓ e := hℓ e he
  have hPy_nonneg : ∀ y ∈ P, 0 ≤ ℓ y.1 := fun y hy => by
    have hyF : y.1 ∈ F.E := mem_E_of_mem_walkEdges hP.1 (by
      simp only [walkEdges, List.mem_toFinset, List.mem_map]; exact ⟨y, hy, rfl⟩)
    exact le_of_lt (hℓ y.1 (hF_sub.2.1 hyF))
  have hLenLe : walkLength ℓ P ≤ (P.length : ℝ) * ℓ e :=
    walkLength_le_length_mul_max hℓe_pos.le hPy_nonneg hPwt
  have hPlen : P.length + 1 ≤ G.n := by
    have hVmem : ∀ w ∈ F.walkVertices (G.tail e) P, w ∈ F.V :=
      MGraph.walkVertices_edges_mem_V hF_for.1 hP.1 (hF_V ▸ hEnds.1)
    have hFinSub : (F.walkVertices (G.tail e) P).toFinset ⊆ G.V := by
      intro w hw
      rw [← hF_V]
      exact hVmem w (List.mem_toFinset.mp hw)
    have hcard := Finset.card_le_card hFinSub
    rw [List.toFinset_card_of_nodup hP.2, walkVertices_length_eq] at hcard
    exact hcard
  have hGn_pos : 1 ≤ G.n := Finset.card_pos.mpr ⟨G.tail e, hEnds.1⟩
  have hPlenReal : (P.length : ℝ) ≤ (G.n : ℝ) - 1 := by
    have hleN : P.length ≤ G.n - 1 := by omega
    have hleR : (P.length : ℝ) ≤ ((G.n - 1 : ℕ) : ℝ) := by exact_mod_cast hleN
    rwa [Nat.cast_sub hGn_pos, Nat.cast_one] at hleR
  have hDiv : walkLength ℓ (MGraph.forestPath F (G.tail e) (G.head e)) / ℓ e ≤ (G.n : ℝ) - 1 := by
    rw [hLenEq]
    refine (div_le_iff₀ hℓe_pos).mpr ?_
    exact le_trans hLenLe (mul_le_mul_of_nonneg_right hPlenReal hℓe_pos.le)
  rw [hStretchEq]
  have hGn_le_max : (G.n : ℝ) ≤ max 1 (G.n : ℝ) := le_max_right _ _
  change 1 + walkLength ℓ (F.forestPath (G.tail e) (G.head e)) / ℓ e ≤ max 1 (G.n : ℝ)
  linarith

end KruskalMSF

section ConcreteTools

/-- Concrete `LastLevelParams` satisfied universally by `exLastTool`. -/
def exLastParams : LastLevelParams where
  σ_last := fun n => max 1 (n : ℝ)
  σ_mwu := fun n => max 1 (n : ℝ)
  c_last := 1
  p_last := 0

lemma exLastParams_valid : exLastParams.Valid := by
  refine ⟨fun n => le_max_left _ _, fun n₁ n₂ hn => ?_, fun n => le_max_left _ _,
    fun n₁ n₂ hn => ?_, zero_le_one⟩
  · exact max_le_max_left 1 (by exact_mod_cast hn)
  · exact max_le_max_left 1 (by exact_mod_cast hn)

/-- Concrete `LastLevelTool` built from Kruskal's minimum-weight spanning forest. -/
noncomputable def exLastTool : LastLevelTool where
  build := fun G_d ℓ_d => (1, fun _ => kruskalLSF G_d ℓ_d)
  cost := fun _ => 1

/-- `exLastTool` satisfies **universal** `LastLevelTool.IsSpec exLastParams` for every valid graph
`G_d` and positive edge lengths `ℓ_d`. -/
theorem exLastTool_isSpec : exLastTool.IsSpec exLastParams := by
  intro G_d ℓ_d hG hℓ
  obtain ⟨hH, _, hConn, _⟩ := kruskalLSF_holds hG hℓ
  refine ⟨zero_lt_one, fun j hj => ?_, fun e he => ?_, fun j hj u hu v hv hC => ?_, ?_⟩
  · exact hH
  · simp only [exLastTool, kruskalLSF, exLastParams, Finset.range_one, Finset.sum_singleton,
      Nat.cast_one, div_one, le_refl]
  · exact hConn u hu v hv hC
  · simp only [exLastTool, exLastParams, pow_zero, mul_one, Nat.cast_one, one_mul]
    have hm_nn : (0 : ℝ) ≤ G_d.m := Nat.cast_nonneg _
    nlinarith

/-- Concrete `SparseCoreParams` used with `exCoreTool`. -/
def exSparseParams : SparseCoreParams where
  σ := fun _ n => max 1 (n : ℝ)
  γ_ℓ := fun _ => 1
  γ_c := fun _ => 1
  γ_r := fun _ => 1
  c_R := 1
  c_T := 1
  p_T := 0

lemma exSparseParams_valid : exSparseParams.Valid := by
  refine ⟨fun k n _ => le_max_left _ _, fun _ _ n₁ n₂ _ hn => ?_, fun _ => le_refl _,
    fun _ _ _ => le_refl _, fun _ => le_refl _, fun _ _ _ => le_refl _, fun _ => le_refl _,
    fun _ _ _ => le_refl _, zero_le_one, zero_le_one⟩
  exact max_le_max_left 1 (by exact_mod_cast hn)

/-- Concrete `SparseCoreRestartTool` built from Kruskal's minimum-weight spanning forest,
contracting each component into `S = (R, ∅)` with empty embeddings `emb _ = []` and constant
`cost = 1`. This satisfies all `SparseCoreRestartTool` specifications on arbitrary valid no-update
dynamic instances (`∀ t ≥ 1, D.U t = []`) and arbitrary branch restart schedules. -/
noncomputable def exCoreTool : SparseCoreRestartTool where
  State := LSF × MGraph
  init := fun _ _ _ G ℓ _ =>
    let L := kruskalLSF G ℓ
    (L, { V := L.F.R, E := ∅, tail := G.tail, head := G.head })
  update := fun st _ _ _ => (st, fun _ => [])
  restart := fun st _ => st
  lsfs := fun st _ => st.1
  S := fun st _ => st.2
  emb := fun _ _ _ => []
  cost := fun _ => 1

private lemma exCoreTool_foldl_restart (xs : List ℕ) (x : LSF × MGraph) :
    xs.foldl exCoreTool.restart x = x := by
  induction xs generalizing x with
  | nil => rfl
  | cons _ xs ih => exact ih x

private lemma exCoreTool_runAfterRestarts_eq (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) :
    ∀ t, (∀ s, 1 ≤ s → s ≤ t → D.U s = []) →
      exCoreTool.runAfterUpdate k M N D restarts t =
        (exCoreTool.init k M N (D.G 0) (D.ℓ 0) (D.g 0), fun _ => []) ∧
      exCoreTool.runAfterRestarts k M N D restarts t =
        exCoreTool.init k M N (D.G 0) (D.ℓ 0) (D.g 0)
  | 0, _ => by
    refine ⟨rfl, ?_⟩
    dsimp only [SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate]
    exact exCoreTool_foldl_restart _ _
  | t + 1, hU => by
    have hprev := exCoreTool_runAfterRestarts_eq k M N D restarts t
      (fun s hs1 hst => hU s hs1 (Nat.le_succ_of_le hst))
    have hpre : exCoreTool.runAfterUpdate k M N D restarts (t + 1) =
        (exCoreTool.init k M N (D.G 0) (D.ℓ 0) (D.g 0), fun _ => []) := by
      rw [exCoreTool.runAfterUpdate_succ k M N D restarts t, hprev.2]
      rfl
    refine ⟨hpre, ?_⟩
    dsimp only [SparseCoreRestartTool.runAfterRestarts]
    rw [hpre]
    exact exCoreTool_foldl_restart _ _

private lemma dyn_const_of_noUpdate {D : DynamicInstance} {τ : ℕ}
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hNoU : ∀ s, 1 ≤ s → s ≤ τ → D.U s = []) :
    ∀ t ≤ τ, D.G t = D.G 0 ∧ ∀ e ∈ (D.G 0).E, D.ℓ t e = D.ℓ 0 e := by
  intro t ht
  induction t with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ t ih =>
    have ih' := ih (Nat.le_of_succ_le ht)
    have hstep := hD (t + 1) (Nat.succ_pos t) ht
    have hU : D.U (t + 1) = [] := hNoU (t + 1) (Nat.succ_pos t) ht
    have hGeq : D.G (t + 1) = D.G 0 := by
      rw [hstep.2, hU, MGraph.applyBatch]; exact ih'.1
    refine ⟨hGeq, fun e he => ?_⟩
    have hL := hLen (t + 1) (Nat.succ_pos t) ht e (hGeq ▸ he) (ih'.1 ▸ he)
      (fun u hu => by rw [hU] at hu; cases hu)
    simp only [Nat.add_sub_cancel] at hL
    rw [hL, ih'.2 e he]

/-- On every valid dynamic instance `D` of length `τ` with **no updates** (`∀ t, D.U t = []`)
and arbitrary restart schedule `restarts`, `exCoreTool` simultaneously satisfies every conclusion of
`SparseCoreRestartTool.IsSpecRestart exSparseParams`, `ToolMWURestart (fun n => max 1 n)`,
`ToolEmbedsSurvivingRestart`, and `ToolNoReinsertRestart`. -/
theorem exCoreTool_spec_on_noUpdate (k τ : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (hk : 0 < k) (hG0 : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hNoU : ∀ s, 1 ≤ s → s ≤ τ → D.U s = []) :
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    let pre := fun t => (exCoreTool.runAfterUpdate k m₀ n₀ D restarts t).1
    let U_S := fun t => (exCoreTool.runAfterUpdate k m₀ n₀ D restarts t).2
    let st := fun t => exCoreTool.runAfterRestarts k m₀ n₀ D restarts t
    (∀ t ≤ τ, ∀ j < k,
      (exCoreTool.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (exSparseParams.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraph (D.G t) (exCoreTool.lsfs (st t) j) (D.ℓ t) (k : ℝ)
        (exSparseParams.γ_ℓ m₀) (exSparseParams.γ_c m₀)
        (exCoreTool.S (st t) j) (exCoreTool.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((exCoreTool.lsfs (st t) j).F.R.card : ℝ) ≤
          exSparseParams.c_R * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (exCoreTool.lsfs (st t) j).F.F.E ⊆ (exCoreTool.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (exCoreTool.lsfs (st t) j).wstr e = (exCoreTool.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (exCoreTool.lsfs (st t) j).wstr e = 1) ∧
      (exCoreTool.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      exCoreTool.S (pre t) j = (exCoreTool.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ r ≤ τ, ∀ p j', p ++ [j'] <+: restarts r →
      let st' := List.foldl exCoreTool.restart (pre r) p
      (∀ b < k, exCoreTool.lsfs (exCoreTool.restart st' j') b = exCoreTool.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        exCoreTool.S (exCoreTool.restart st' j') b = exCoreTool.S st' b ∧
        exCoreTool.emb (exCoreTool.restart st' j') b = exCoreTool.emb st' b) ∧
      exCoreTool.cost st' ≤ exCoreTool.cost (exCoreTool.restart st' j') ∧
      (exCoreTool.cost (exCoreTool.restart st' j') : ℝ) ≤
        (exCoreTool.cost st' : ℝ) + exSparseParams.c_T * ((m₀ : ℝ) + 1) * exSparseParams.γ_r m₀ *
          (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ exSparseParams.p_T) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      s₀ = 0 ∨ j ∈ restarts s₀ → (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        exSparseParams.γ_r m₀ * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (exCoreTool.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        exSparseParams.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ s₀ ≤ τ, ∀ j < k, ∃ Ψ' : ℝ,
      WeakHiddenStable (exCoreTool.coreInstanceFrom k m₀ n₀ D restarts s₀ j) (τ - s₀) Ψ'
        (exCoreTool.coreCFrom k m₀ n₀ D restarts c s₀ j)
        (exCoreTool.coreWFrom k m₀ n₀ D restarts w s₀ j)) ∧
    ((exCoreTool.cost (st τ) : ℝ) ≤
      exSparseParams.c_T * ((m₀ : ℝ) + 1) *
        ((k : ℝ) + ((Finset.range (τ + 1)).sum fun r => (restarts r).length : ℕ)) *
        exSparseParams.γ_r m₀ * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ exSparseParams.p_T) ∧
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (exCoreTool.lsfs (st t) j).wstr e) / (k : ℝ) ≤
        max 1 ((D.G t).n : ℝ)) ∧
    (∀ t ≤ τ, ∀ j < k, ∀ e ∈ (exCoreTool.S (st t) j).E,
      exCoreTool.emb (st t) j e = [(e, true)]) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (exCoreTool.S (st (t - 1)) j) (U_S t j)) := by
  have hconst := dyn_const_of_noUpdate hD hLen hNoU
  have hℓ0 : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he => (hWeak 0 (Nat.zero_le τ)).2.2.2 e he |>.2.2.1
  obtain ⟨hL0_holds, _, hConn0, hR0_card⟩ := kruskalLSF_holds hG0 hℓ0
  let L₀ := kruskalLSF (D.G 0) (D.ℓ 0)
  let S₀ : MGraph := { V := L₀.F.R, E := ∅, tail := (D.G 0).tail, head := (D.G 0).head }
  have hpre_eq : ∀ t ≤ τ, exCoreTool.runAfterUpdate k (D.G 0).m (D.G 0).n D restarts t = ((L₀, S₀), fun _ => []) := fun t ht =>
    (exCoreTool_runAfterRestarts_eq k (D.G 0).m (D.G 0).n D restarts t (fun s hs1 hst => hNoU s hs1 (le_trans hst ht))).1
  have hrun_eq : ∀ t ≤ τ, exCoreTool.runAfterRestarts k (D.G 0).m (D.G 0).n D restarts t = (L₀, S₀) := fun t ht =>
    (exCoreTool_runAfterRestarts_eq k (D.G 0).m (D.G 0).n D restarts t (fun s hs1 hst => hNoU s hs1 (le_trans hst ht))).2
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht j _
    rw [hrun_eq t ht]
    dsimp only [exCoreTool]
    obtain ⟨hGt, hℓt⟩ := hconst t ht
    have hH_t : L₀.Holds (D.G t) (D.ℓ t) (exSparseParams.σ k (D.G t).n) := by
      rw [hGt]
      refine ⟨hL0_holds.1, hL0_holds.2.1, hL0_holds.2.2.1, fun e he => ?_⟩
      have hstrEq : L₀.F.stretch (D.G 0) (D.ℓ t) e = L₀.F.stretch (D.G 0) (D.ℓ 0) e := by
        unfold RootedForest.stretch
        dsimp only
        have hF_for := hL0_holds.2.1.1
        have hSub := hL0_holds.2.1.2.2.2.2
        have hpthSub : ∀ a b, walkEdges (MGraph.forestPath L₀.F.F a b) ⊆ (D.G 0).E := by
          intro a b f hf
          by_cases hcab : L₀.F.F.Connected a b
          · exact hSub.2.1 (mem_E_of_mem_walkEdges (MGraph.isWalk_forestPath hcab) hf)
          · have hemp : MGraph.forestPath L₀.F.F a b = [] := by
              unfold MGraph.forestPath
              split_ifs with hP
              · exact absurd ⟨_, hP.choose_spec.1⟩ hcab
              · rfl
            rw [hemp] at hf; simp [walkEdges] at hf
        have hwl : ∀ a b, walkLength (D.ℓ t) (MGraph.forestPath L₀.F.F a b) =
            walkLength (D.ℓ 0) (MGraph.forestPath L₀.F.F a b) := fun a b => by
          unfold walkLength
          refine Finset.sum_congr rfl fun f hf => ?_
          rw [hℓt f (hpthSub a b hf)]
        rw [hℓt e he, hwl, hwl, hwl]
      rw [hstrEq]
      exact hL0_holds.2.2.2 e he
    have hSp : IsSparsifiedCoreGraph (D.G t) L₀ (D.ℓ t) (k : ℝ)
        (exSparseParams.γ_ℓ (D.G 0).m) (exSparseParams.γ_c (D.G 0).m) S₀ (fun _ => []) := by
      rw [hGt]
      refine ⟨⟨Finset.Subset.refl _, Finset.empty_subset _, fun _ hf => by cases hf⟩,
        ⟨Finset.Subset.refl _, fun e he => ?_⟩, fun e he e' he' => by simp [walkEdges] at he',
        ?_, ?_, ?_⟩
      · have heG : e ∈ (D.G 0).E := (Finset.mem_sdiff.mp he).1
        have hEnds := hG0 e heG
        have hFconn := hConn0 ((D.G 0).tail e) hEnds.1 ((D.G 0).head e) hEnds.2
          ⟨[(e, true)], .cons heG (by simp [MGraph.src]) (by simp [MGraph.dst]; exact .nil _)⟩
        have hSpec := kruskalRoots_spec (D.G 0) L₀.F.F hL0_holds.2.1.2.1
        have hRootEq : L₀.F.root ((D.G 0).tail e) = L₀.F.root ((D.G 0).head e) := by
          have hu_ex : ∃ r ∈ L₀.F.R, L₀.F.F.Connected ((D.G 0).tail e) r :=
            (hSpec ((D.G 0).tail e) hEnds.1).exists
          have hv_ex : ∃ r ∈ L₀.F.R, L₀.F.F.Connected ((D.G 0).head e) r :=
            (hSpec ((D.G 0).head e) hEnds.2).exists
          have hru : L₀.F.root ((D.G 0).tail e) ∈ L₀.F.R ∧
              L₀.F.F.Connected ((D.G 0).tail e) (L₀.F.root ((D.G 0).tail e)) := by
            dsimp only [RootedForest.root]; simp only [hu_ex, ↓reduceDIte]
            exact Classical.choose_spec hu_ex
          have hrv : L₀.F.root ((D.G 0).head e) ∈ L₀.F.R ∧
              L₀.F.F.Connected ((D.G 0).head e) (L₀.F.root ((D.G 0).head e)) := by
            dsimp only [RootedForest.root]; simp only [hv_ex, ↓reduceDIte]
            exact Classical.choose_spec hv_ex
          exact (hSpec ((D.G 0).tail e) hEnds.1).unique hru
            ⟨hrv.1, MGraph.connected_trans hFconn hrv.2⟩
        change S₀.IsWalk (L₀.F.root ((D.G 0).tail e)) (L₀.F.root ((D.G 0).head e)) []
        rw [hRootEq]
        exact .nil _
      · by_cases hne : (coreGraph (D.G 0) L₀).E.Nonempty
        · simp [Embedding.length, exSparseParams]
        · simp [Embedding.length, exSparseParams]
      · have hE0 : S₀.E = ∅ := rfl
        simp [Embedding.econg, hE0, exSparseParams]
      · simp [S₀, exSparseParams]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    refine ⟨hH_t, hSp, fun hConn => ?_⟩
    have hR1 : (L₀.F.R.card : ℝ) ≤ 1 := by exact_mod_cast hR0_card hConn
    have hm_nn : (0 : ℝ) ≤ ((D.G 0).m : ℝ) / (k : ℝ) := by positivity
    have hl_nn : (0 : ℝ) ≤ (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    simp only [exSparseParams, one_mul]
    linarith
  · intro t ht1 ht j _
    rw [hrun_eq t ht, hrun_eq (t - 1) (le_trans (Nat.sub_le t 1) ht), hpre_eq t ht]
    refine ⟨Finset.Subset.refl _, fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
    · intro e _ ⟨u, hu, _⟩
      rw [hNoU t ht1 ht] at hu; cases hu
    · simp [MGraph.BatchIsValid]
    · simp [MGraph.applyBatch]
  · intro r _ p j' _
    refine ⟨fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, le_refl _, ?_⟩
    simp only [exCoreTool, exSparseParams, Nat.cast_one, one_mul, pow_zero, mul_one]
    have hm_nn : (0 : ℝ) ≤ (D.G 0).m := Nat.cast_nonneg _
    linarith
  · intro s₀ t hst ht j _ _ _
    have hsum0 : (Finset.Icc (s₀ + 1) t).sum (fun s =>
        ((exCoreTool.runAfterUpdate k (D.G 0).m (D.G 0).n D restarts s).2 j).length) = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have hsle : s ≤ τ := le_trans (Finset.mem_Icc.mp hs).2 ht
      rw [hpre_eq s hsle]
      rfl
    have henc0 : (Finset.Icc (s₀ + 1) t).sum (fun s =>
        (exCoreTool.S (exCoreTool.runAfterRestarts k (D.G 0).m (D.G 0).n D restarts (s - 1)) j).batchEnc
          ((exCoreTool.runAfterUpdate k (D.G 0).m (D.G 0).n D restarts s).2 j)) = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have hsle : s ≤ τ := le_trans (Finset.mem_Icc.mp hs).2 ht
      rw [hpre_eq s hsle]
      simp [MGraph.batchEnc]
    rw [hsum0, henc0]
    simp only [Nat.cast_zero, exSparseParams, one_mul]
    exact ⟨by positivity, by positivity⟩
  · intro s₀ hs₀ j _
    refine ⟨0, fun t ht => ?_⟩
    have hGt : (exCoreTool.coreInstanceFrom k (D.G 0).m (D.G 0).n D restarts s₀ j).G t = S₀ := by
      dsimp only [SparseCoreRestartTool.coreInstanceFrom]
      rw [hrun_eq (s₀ + t) (by omega)]
      rfl
    refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro v _; simp [MGraph.demand, hGt, S₀]
    · intro v _; simp [MGraph.demand, hGt, S₀]
    · intro e he; rw [hGt] at he; cases he
    · intro e he; rw [hGt] at he; cases he
    · intro e he; rw [hGt] at he; cases he
  · rw [hrun_eq τ (le_refl τ)]
    simp only [exCoreTool, exSparseParams, Nat.cast_one, one_mul, pow_zero, mul_one]
    have hm_nn : (0 : ℝ) ≤ (D.G 0).m := Nat.cast_nonneg _
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hr_nn : (0 : ℝ) ≤ ((Finset.range (τ + 1)).sum fun r => (restarts r).length : ℕ) :=
      Nat.cast_nonneg _
    nlinarith
  · intro t ht e he
    rw [hrun_eq t ht, (hconst t ht).1]
    dsimp only [exCoreTool, kruskalLSF]
    have hdiv : (∑ j ∈ Finset.range k, max 1 ((D.G 0).n : ℝ)) / (k : ℝ) = max 1 ((D.G 0).n : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm,
        mul_div_cancel_right₀ _ (Nat.cast_pos.mpr hk).ne']
    exact le_of_eq hdiv
  · intro t ht j _ e he
    rw [hrun_eq t ht] at he
    cases he
  · intro t ht1 ht j _ e _ u hu
    rw [hpre_eq t ht] at hu
    cases hu

end ConcreteTools

end MinCostFlow.Chain
