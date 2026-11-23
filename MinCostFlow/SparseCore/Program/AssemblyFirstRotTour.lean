module

public import MinCostFlow.Bundle.Tour

/-!
# Equal tours when the root keeps its order

A step of a branch must give P7 a list `T₀` of the core vertices whose output list does not
already come out right from the edits of the deletions, splits and insertions (`OutRotCover`).
The core list at a root `v` is the tour of the tree of `v` that starts with the order at `v`
(`tour`). At a vertex that is not the root, the tour enters through
the forest edge from the parent and goes on after it, so only the cyclic order there matters
(`tour_filter_isRotated`). At the root the tour starts with the first end of the list, so a
rotation there rotates the whole tour.

This file proves the exact form (`tour_filter_eq_of_common`): two tours of the same tree, on two
graphs, are equal after a filter `q`, when the filtered orders are rotations of each other at
every vertex of the tree and are equal at its root. The proof is the one of
`tour_filter_isRotated` (`Bundle/Tour.lean`): both filtered tours are the same function `f`
mapped over the filtered order at the root. The helper lemmas of that proof are private to
`Bundle/Tour.lean`, so they are restated here.
-/

namespace MinCostFlow.Bundle

open MinCostFlow.LSF

private theorem afterEnd_of_append' (x : End) (before rest : List End)
    (h : x ∉ before) : afterEnd x (before ++ x :: rest) = rest ++ before := by
  have hp : ∀ y ∈ before, y != x := by
    intro y hy
    exact bne_iff_ne.mpr (fun he => h (he ▸ hy))
  simp [afterEnd, List.takeWhile_append_of_pos hp, List.drop_append]

private theorem src_flip' (G : MGraph) (x : End) : G.src x.flip = G.dst x := by
  cases x with
  | mk e b => cases b <;> rfl

private theorem src_eq_of_subgraph' {F G : MGraph} (h : G.IsSubgraph F) {x : End}
    (hx : x.1 ∈ F.E) : F.src x = G.src x := by
  obtain ⟨e, b⟩ := x
  have hs := h.2.2 e hx
  cases b
  · exact hs.2
  · exact hs.1

private theorem dst_eq_of_subgraph' {F G : MGraph} (h : G.IsSubgraph F) {x : End}
    (hx : x.1 ∈ F.E) : F.dst x = G.dst x := by
  rw [← src_flip', ← src_flip']
  exact src_eq_of_subgraph' (x := x.flip) h hx

private theorem eraseForestEdge_mono' {F H : MGraph} (hsub : F.IsSubgraph H) (e : ℕ) :
    (eraseForestEdge F e).IsSubgraph (eraseForestEdge H e) :=
  ⟨hsub.1, fun _ he => let hh := Finset.mem_erase.mp he
    Finset.mem_erase.mpr ⟨hh.1, hsub.2.1 hh.2⟩,
    fun f hf => hsub.2.2 f (Finset.mem_erase.mp hf).2⟩

/-- Pruning the forest to the edges that the walk from `v` can reach does not change the
blocks (the private `tourBlocks_prune` of `Bundle/Tour.lean`). -/
private theorem tourBlocks_prune' (G F₀ : MGraph) (ρ : Rotation G)
    (F H : MGraph) (hF : F.IsForest) (hH : H.IsForest) (hsub : F.IsSubgraph H)
    (v : ℕ) (xs : List End)
    (hkeep : ∀ x : End, x.1 ∈ F.E → F.Connected v (F.src x) → x.1 ∈ H.E) :
    tourBlocks G F₀ ρ F hF v xs = tourBlocks G F₀ ρ H hH v xs := by
  rw [tourBlocks.eq_def G F₀ ρ F, tourBlocks.eq_def G F₀ ρ H]
  apply List.flatMap_congr
  intro x _
  by_cases hopen : x.1 ∉ F₀.E
  · simp [hopen]
  by_cases ha : x.1 ∈ F.E ∧ F.src x = v
  · have hxH := hkeep x ha.1 (ha.2 ▸ connected_refl F v)
    have hsx : H.src x = v := (src_eq_of_subgraph' hsub hxH).trans ha.2
    have hd := dst_eq_of_subgraph' hsub hxH
    simp only [hopen, ↓reduceIte, ha, hsx, hxH, and_self, hd]
    apply tourBlocks_prune' G F₀ ρ _ _ _ _ (eraseForestEdge_mono' hsub x.1)
    intro y hy hc
    have hyF := (Finset.mem_erase.mp hy).2
    have hpath : F.Connected (F.dst x) (F.src y) :=
      connected_of_subgraph (eraseForestEdge_subgraph F x.1) hc
    have hxstep : F.Connected v (F.dst x) := ⟨[x], .cons ha.1 ha.2 (.nil _)⟩
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1,
      hkeep y hyF (connected_trans hxstep hpath)⟩
  · have hb : ¬ (x.1 ∈ H.E ∧ H.src x = v) := by
      intro h
      exact ha ⟨hsub.2.1 h.1, (src_eq_of_subgraph' hsub h.1).symm.trans h.2⟩
    simp [hopen, ha, hb]
termination_by (compOf F v).card
decreasing_by
  rw [← ha.2]
  exact branch_card_lt hF ha.1

private theorem afterEnd_anchor' {x : End} {xs : List End} (h : x ∈ xs) (hn : xs.Nodup) :
    xs.IsRotated (x :: afterEnd x xs) := by
  obtain ⟨pre, rest, rfl⟩ := List.mem_iff_append.mp h
  have hnot : x ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 x hm x (by simp) rfl
  rw [afterEnd_of_append' x pre rest hnot]
  exact List.isRotated_append (l := pre) (l' := x :: rest)

private theorem anchored_isRotated_eq' {x : End} {xs ys : List End}
    (h : (x :: xs).IsRotated (x :: ys)) (hn : (x :: xs).Nodup) : xs = ys := by
  obtain ⟨n, hrot⟩ := h
  have hpos : 0 < (x :: xs).length := by simp
  rw [← List.rotate_mod] at hrot
  let i := n % (x :: xs).length
  have hi : i < (x :: xs).length := Nat.mod_lt _ hpos
  have hh := congrArg List.head? hrot
  rw [List.head?_rotate hi, List.getElem?_eq_getElem hi] at hh
  have he : (x :: xs)[i] = (x :: xs)[0] := Option.some.inj hh
  have hi0 := hn.getElem_inj_iff.mp he
  change (x :: xs).rotate i = x :: ys at hrot
  rw [hi0, List.rotate_zero] at hrot
  exact (List.cons.inj hrot).2

private theorem afterEnd_filter_eq' {x : End} {xs ys : List End} (q : End → Bool)
    (hx : x ∈ xs) (hy : x ∈ ys) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hq : q x = true) (h : (xs.filter q).IsRotated (ys.filter q)) :
    (afterEnd x xs).filter q = (afterEnd x ys).filter q := by
  have ha := isRotated_filter q (afterEnd_anchor' hx hxs)
  have hb := isRotated_filter q (afterEnd_anchor' hy hys)
  rw [List.filter_cons_of_pos hq] at ha hb
  exact anchored_isRotated_eq' (ha.symm.trans (h.trans hb))
    (ha.perm.nodup_iff.mp (hxs.filter q))

private theorem filter_flatMap_eq' {α β : Type*} (p : α → Bool) (q : β → Bool)
    (f : α → List β) (xs : List α) (h : ∀ x, p x = false → (f x).filter q = []) :
    (xs.flatMap f).filter q = (xs.filter p).flatMap (fun x => (f x).filter q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x <;> simp [List.flatMap_cons, hx, h, ih]

/-- Both filtered block expansions are one function mapped over the filtered start list (the
private `tourBlocks_filter_isRotated` of `Bundle/Tour.lean`). -/
private theorem tourBlocks_filter_common {G H F₀ F₁ : MGraph}
    (ρ : Rotation G) (σ : Rotation H) (q : End → Bool)
    (hbase : ∀ x : End, q x = true → (x.1 ∈ F₀.E ↔ x.1 ∈ F₁.E))
    (F : MGraph) (hF : F.IsForest) (hG : G.IsSubgraph F) (hH : H.IsSubgraph F)
    (h₀ : F.E ⊆ F₀.E) (h₁ : F.E ⊆ F₁.E)
    (hq : ∀ x : End, x.1 ∈ F.E → q x = true)
    (v : ℕ) (xs ys : List End)
    (horder : ∀ w, F.Connected v w → ((ρ.order w).filter q).IsRotated ((σ.order w).filter q)) :
    ∃ f : End → List End,
      (tourBlocks G F₀ ρ F hF v xs).filter q = (xs.filter q).flatMap f ∧
      (tourBlocks H F₁ σ F hF v ys).filter q = (ys.filter q).flatMap f := by
  let block (J B : MGraph) (τ : Rotation J) (x : End) :=
    if x.1 ∉ B.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      tourBlocks J B τ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (τ.order (F.dst x)))
    else []
  have heq (J B : MGraph) (τ : Rotation J) (zs : List End) :
      (tourBlocks J B τ F hF v zs).filter q =
        (zs.filter q).flatMap (fun x => (block J B τ x).filter q) := by
    rw [tourBlocks.eq_def J B τ F hF v zs]
    apply filter_flatMap_eq' q q (block J B τ) zs
    intro x hx
    have hn : x.1 ∉ F.E := by
      intro he
      rw [hq x he] at hx
      contradiction
    by_cases hxB : x.1 ∈ B.E <;> simp [block, hn, hx, hxB]
  refine ⟨fun x => (block G F₀ ρ x).filter q, heq G F₀ ρ xs, ?_⟩
  rw [heq H F₁ σ]
  apply List.flatMap_congr
  intro x hx
  by_cases ha : x.1 ∈ F.E ∧ F.src x = v
  · have hsd : F.src x.flip = F.dst x := src_flip' F x
    have hxρ : x.flip ∈ ρ.order (F.dst x) :=
      (ρ.mem_order _ _).mpr ⟨hG.2.1 ha.1,
        (src_eq_of_subgraph' (x := x.flip) hG ha.1).symm.trans hsd⟩
    have hxσ : x.flip ∈ σ.order (F.dst x) :=
      (σ.mem_order _ _).mpr ⟨hH.2.1 ha.1,
        (src_eq_of_subgraph' (x := x.flip) hH ha.1).symm.trans hsd⟩
    have hstep : F.Connected v (F.dst x) := ⟨[x], .cons ha.1 ha.2 (.nil _)⟩
    have hr := afterEnd_filter_eq' q hxρ hxσ (ρ.nodup _) (σ.nodup _) (hq x.flip ha.1)
      (horder _ hstep)
    have hsub' (J : MGraph) (hsub : J.IsSubgraph F) : J.IsSubgraph (eraseForestEdge F x.1) :=
      ⟨hsub.1, fun _ he => hsub.2.1 (Finset.mem_erase.mp he).2,
        fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
    obtain ⟨f, hf₁, hf₂⟩ := tourBlocks_filter_common ρ σ q hbase _
      (isForest_eraseEdge hF x.1) (hsub' G hG) (hsub' H hH)
      (fun _ hz => h₀ (Finset.mem_erase.mp hz).2) (fun _ hz => h₁ (Finset.mem_erase.mp hz).2)
      (fun z hz => hq z (Finset.mem_erase.mp hz).2)
      (F.dst x) (afterEnd x.flip (ρ.order (F.dst x))) (afterEnd x.flip (σ.order (F.dst x)))
      (fun w hw => horder w (connected_trans hstep
        (connected_of_subgraph (eraseForestEdge_subgraph F x.1) hw)))
    simp only [block, h₀ ha.1, h₁ ha.1, ha, not_true_eq_false, and_self, ↓reduceIte,
      ↓reduceDIte]
    rw [hf₁, hf₂, hr]
  · have hh := hbase x (List.mem_filter.mp hx).2
    simp [block, ha, hh]
termination_by (compOf F v).card
decreasing_by
  rw [← ha.2]
  exact branch_card_lt hF ha.1

public section

/-- **Equal tours of a common tree.** Let the forests `F` of `G` and `F'` of `H` both contain the
forest `J`, and let `J` hold every edge of `F` and of `F'` that the walk from `v` reaches. Let `q`
keep every end of an edge of `J`, and let it see the same open ends in `F` and `F'`. If the
filtered orders are rotations of each other at every vertex of the tree of `v` in `J`, and are
equal at `v`, then the two tours at `v` are equal after the filter. -/
theorem tour_filter_eq_of_common {G H F F' J : MGraph}
    (ρ : Rotation G) (σ : Rotation H) (hF : F.IsForest) (hF' : F'.IsForest)
    (hJ : J.IsForest) (hGJ : G.IsSubgraph J) (hHJ : H.IsSubgraph J)
    (hsub : F.IsSubgraph J) (hsub' : F'.IsSubgraph J) (v : ℕ)
    (hkeep : ∀ y : End, y.1 ∈ F.E → F.Connected v (F.src y) → y.1 ∈ J.E)
    (hkeep' : ∀ y : End, y.1 ∈ F'.E → F'.Connected v (F'.src y) → y.1 ∈ J.E)
    (q : End → Bool) (hbase : ∀ x : End, q x = true → (x.1 ∈ F.E ↔ x.1 ∈ F'.E))
    (hq : ∀ x : End, x.1 ∈ J.E → q x = true)
    (horder : ∀ w, J.Connected v w → ((ρ.order w).filter q).IsRotated ((σ.order w).filter q))
    (hroot : (ρ.order v).filter q = (σ.order v).filter q) :
    (tour ρ hF v).filter q = (tour σ hF' v).filter q := by
  obtain ⟨f, h₁, h₂⟩ := tourBlocks_filter_common (F₀ := F) (F₁ := F') ρ σ q hbase J hJ hGJ hHJ
    hsub.2.1 hsub'.2.1 hq v (ρ.order v) (σ.order v) horder
  have hp := tourBlocks_prune' G F ρ _ _ hF hJ hsub v (ρ.order v) hkeep
  have hp' := tourBlocks_prune' H F' σ _ _ hF' hJ hsub' v (σ.order v) hkeep'
  unfold tour
  rw [hp, hp', h₁, h₂, hroot]

end

end MinCostFlow.Bundle
