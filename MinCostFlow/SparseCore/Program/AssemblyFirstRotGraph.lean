module

public import MinCostFlow.Basic.Dynamic
public import MinCostFlow.SparseCore.Program.AssemblyFirstRotTour

/-!
# A tree that a batch does not touch keeps its tour

The list `T₀` of a branch step must hold every root whose output list the edits of the output
batch do not already give (`OutRotCover`). This file has the graph part of that proof.

A batch moves the ends of an edge only at the vertices it names: the two endpoints of an
insertion and the two vertices of a split (`batchVerts`). So an edge that the batch keeps has the
same endpoints after the batch, unless both its old and its new endpoint are named
(`applyBatch_src_moves`).

Then take a root `v` of the new forest `F'`, and its tree `C` in `F'`. Assume that no vertex of
`C` is named by the batch, and that no forest edge of the old forest `F` that the step removes
starts in `C` (`TreeKept`). Then the tree of `v` in `F` is `C` too (`TreeKept.connected`), with
the same edges and the same endpoints. So the two tours at `v` are equal after a filter, as soon
as the filtered orders agree on `C` (`TreeKept.tour_filter_eq`, from `tour_filter_eq_of_common`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.LSF

/-! ## The vertices that a batch names -/

/-- The vertices that one update names: both endpoints of an insertion, and the old and the new
vertex of a split. A deletion names none. -/
def updVerts : Update → Finset ℕ
  | .insert _ a b => {a, b}
  | .delete _ => ∅
  | .split v v' _ _ => {v, v'}

/-- The vertices that the updates of a batch name. -/
def batchVerts : List Update → Finset ℕ
  | [] => ∅
  | u :: U => updVerts u ∪ batchVerts U

theorem updVerts_card_le (u : Update) : (updVerts u).card ≤ 2 := by
  cases u with
  | insert e a b => exact (Finset.card_insert_le _ _).trans (by simp)
  | delete e => simp [updVerts]
  | split v v' St Sh => exact (Finset.card_insert_le _ _).trans (by simp)

/-- A batch names at most two vertices per update. -/
theorem batchVerts_card_le : ∀ U : List Update, (batchVerts U).card ≤ 2 * U.length
  | [] => by simp [batchVerts]
  | u :: U => by
    have h1 := Finset.card_union_le (updVerts u) (batchVerts U)
    have h2 := updVerts_card_le u
    have h3 := batchVerts_card_le U
    simp only [batchVerts, List.length_cons]
    omega

/-! ## How a batch moves the ends of an edge -/

/-- A split moves an end only from the split vertex to the new vertex. -/
private theorem split_src (G : MGraph) (v v' : ℕ) (St Sh : Finset ℕ) (x : End) :
    (G.applyUpdate (.split v v' St Sh)).src x = G.src x ∨
      (G.src x = v ∧ (G.applyUpdate (.split v v' St Sh)).src x = v') := by
  obtain ⟨e, b⟩ := x
  cases b <;> simp only [MGraph.src, MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte] <;>
    split_ifs with h
  · exact Or.inr ⟨h.2, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h.2, rfl⟩
  · exact Or.inl rfl

/-- One valid update that does not delete the edge of `x` keeps the edge, and moves the start of
`x` only between vertices that it names. -/
private theorem applyUpdate_src_moves {G : MGraph} {u : Update} (hu : G.UpdateIsValid u)
    {x : End} (hx : x.1 ∈ G.E) (hdel : u ≠ .delete x.1) :
    x.1 ∈ (G.applyUpdate u).E ∧ ((G.applyUpdate u).src x = G.src x ∨
      (G.src x ∈ updVerts u ∧ (G.applyUpdate u).src x ∈ updVerts u)) := by
  obtain ⟨e₀, b⟩ := x
  cases u with
  | insert e a c =>
    -- the inserted edge is new, so it is not the edge of `x`
    have hne : e₀ ≠ e := fun h => hu.1 (h ▸ hx)
    refine ⟨Finset.mem_insert_of_mem hx, Or.inl ?_⟩
    cases b <;> simp [MGraph.src, MGraph.applyUpdate, Function.update_of_ne hne]
  | delete e =>
    have hne : e₀ ≠ e := fun h => hdel (by rw [h])
    exact ⟨Finset.mem_erase.mpr ⟨hne, hx⟩, Or.inl rfl⟩
  | split v v' St Sh =>
    refine ⟨hx, ?_⟩
    rcases split_src G v v' St Sh (e₀, b) with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by simp [updVerts, h1], by simp [updVerts, h2]⟩

/-- **A batch moves ends only at the vertices it names.** Let `U` be a valid batch, and let `x`
be an end of an edge of `G` that `U` does not delete. Then the edge is in the graph after the
batch, and the start of `x` is the same, or both the old and the new start of `x` are named by
`U`. -/
theorem applyBatch_src_moves : ∀ (G : MGraph) (U : List Update), G.BatchIsValid U →
    ∀ x : End, x.1 ∈ G.E → (∀ u ∈ U, u ≠ .delete x.1) →
      x.1 ∈ (G.applyBatch U).E ∧ ((G.applyBatch U).src x = G.src x ∨
        (G.src x ∈ batchVerts U ∧ (G.applyBatch U).src x ∈ batchVerts U))
  | G, [], _, x, hx, _ => ⟨hx, Or.inl rfl⟩
  | G, u :: U, hU, x, hx, hdel => by
    obtain ⟨hx₁, hs₁⟩ := applyUpdate_src_moves hU.1 hx (hdel u (List.mem_cons_self ..))
    obtain ⟨hx₂, hs₂⟩ := applyBatch_src_moves (G.applyUpdate u) U hU.2 x hx₁
      fun u' hu' => hdel u' (List.mem_cons_of_mem _ hu')
    -- the batch `u :: U` is `u`, then `U`
    change x.1 ∈ ((G.applyUpdate u).applyBatch U).E ∧
      (((G.applyUpdate u).applyBatch U).src x = G.src x ∨
        (G.src x ∈ updVerts u ∪ batchVerts U ∧
          ((G.applyUpdate u).applyBatch U).src x ∈ updVerts u ∪ batchVerts U))
    refine ⟨hx₂, ?_⟩
    rcases hs₁ with h₁ | ⟨h₁, h₁'⟩
    · rcases hs₂ with h₂ | ⟨h₂, h₂'⟩
      · exact Or.inl (h₂.trans h₁)
      · rw [h₁] at h₂
        exact Or.inr ⟨Finset.mem_union_right _ h₂, Finset.mem_union_right _ h₂'⟩
    · rcases hs₂ with h₂ | ⟨-, h₂'⟩
      · exact Or.inr ⟨Finset.mem_union_left _ h₁, h₂ ▸ Finset.mem_union_left _ h₁'⟩
      · exact Or.inr ⟨Finset.mem_union_left _ h₁, Finset.mem_union_right _ h₂'⟩

/-- The vertices after a batch are the old ones and the vertices that the batch names. -/
theorem applyBatch_V_subset : ∀ (G : MGraph) (U : List Update),
    (G.applyBatch U).V ⊆ G.V ∪ batchVerts U
  | G, [] => by simp [MGraph.applyBatch, batchVerts]
  | G, u :: U => by
    intro w hw
    have h := applyBatch_V_subset (G.applyUpdate u) U hw
    change w ∈ G.V ∪ (updVerts u ∪ batchVerts U)
    rcases Finset.mem_union.mp h with h | h
    · cases u with
      | insert e a b => exact Finset.mem_union_left _ h
      | delete e => exact Finset.mem_union_left _ h
      | split v v' St Sh =>
        rcases Finset.mem_insert.mp h with rfl | h
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [updVerts]))
        · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

/-! ## A tree that the batch does not touch -/

private theorem src_eq_of_sub {F G : MGraph} (h : G.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E) :
    F.src x = G.src x := by
  obtain ⟨e, b⟩ := x
  have he := h.2.2 e hx
  cases b <;> simp [MGraph.src, he.1, he.2]

private theorem dst_eq_of_sub {F G : MGraph} (h : G.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E) :
    F.dst x = G.dst x := by
  obtain ⟨e, b⟩ := x
  have he := h.2.2 e hx
  cases b <;> simp [MGraph.dst, he.1, he.2]

/-- The two ends of a forest edge are in the same tree. -/
private theorem conn_src_dst {F G : MGraph} (h : G.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E)
    {v : ℕ} (hc : F.Connected v (G.src x)) : F.Connected v (G.dst x) := by
  have hw : F.IsWalk (F.src x) (F.dst x) [x] := .cons hx rfl (.nil _)
  rw [src_eq_of_sub h hx, dst_eq_of_sub h hx] at hw
  exact connected_trans hc ⟨_, hw⟩

/-- The start of an end of a forest edge is in a tree exactly when the tail of the edge is. -/
private theorem conn_src_iff {F G : MGraph} (h : G.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E)
    {v : ℕ} : F.Connected v (G.src x) ↔ F.Connected v (G.tail x.1) := by
  obtain ⟨e, b⟩ := x
  cases b
  · -- the start is the head; the tail is the other end
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · exact conn_src_dst h hx hc
    · exact conn_src_dst h (x := (e, true)) hx hc
  · exact Iff.rfl

/-- The hypotheses under which the tree of `v` does not change in a step, from the old graph
`G` with forest `F` to the new graph `G'` with forest `F'`, when `B` holds the vertices that the
batch names:
* each forest is a subgraph of its graph, and the new forest edges are old forest edges;
* the batch moves the ends of a new forest edge only between vertices of `B`;
* no vertex of the tree of `v` in `F'` is in `B`;
* every old forest edge that starts in that tree is still a forest edge. -/
structure TreeKept (G G' F F' : MGraph) (B : Finset ℕ) (v : ℕ) : Prop where
  sub : G.IsSubgraph F
  sub' : G'.IsSubgraph F'
  mono : F'.E ⊆ F.E
  move : ∀ x : End, x.1 ∈ F'.E → G'.src x = G.src x ∨ (G.src x ∈ B ∧ G'.src x ∈ B)
  named : ∀ w, F'.Connected v w → w ∉ B
  cut : ∀ x : End, x.1 ∈ F.E → F'.Connected v (G.src x) → x.1 ∈ F'.E

namespace TreeKept

variable {G G' F F' : MGraph} {B : Finset ℕ} {v : ℕ}

/-- A new forest edge that starts in the tree keeps both its endpoints, and ends in the tree. -/
theorem edge' (h : TreeKept G G' F F' B v) {x : End} (hx : x.1 ∈ F'.E)
    (hc : F'.Connected v (G'.src x)) :
    G'.src x = G.src x ∧ G'.dst x = G.dst x ∧ F'.Connected v (G'.dst x) := by
  have hcd := conn_src_dst h.sub' hx hc
  refine ⟨(h.move x hx).resolve_right fun hb => h.named _ hc hb.2, ?_, hcd⟩
  -- the reversed end starts at the end of `x`
  rcases h.move (x.1, !x.2) hx with hm | hm
  · rwa [src_flip, src_flip] at hm
  · simp only [src_flip] at hm
    exact absurd hm.2 (h.named _ hcd)

/-- An old forest edge that starts in the tree is a new forest edge, keeps both its endpoints,
and ends in the tree. -/
theorem edge (h : TreeKept G G' F F' B v) {x : End} (hx : x.1 ∈ F.E)
    (hc : F'.Connected v (G.src x)) :
    x.1 ∈ F'.E ∧ G'.src x = G.src x ∧ G'.dst x = G.dst x ∧ F'.Connected v (G.dst x) := by
  have hx' := h.cut x hx hc
  have hs : G'.src x = G.src x := (h.move x hx').resolve_right fun hb => h.named _ hc hb.1
  obtain ⟨-, hd, hcd⟩ := h.edge' hx' (hs ▸ hc)
  exact ⟨hx', hs, hd, hd ▸ hcd⟩

/-- **The old tree of `v` lies in the new one.** -/
theorem connected (h : TreeKept G G' F F' B v) {w : ℕ} (hw : F.Connected v w) :
    F'.Connected v w := by
  obtain ⟨P, hP⟩ := hw
  suffices hs : ∀ u, F.IsWalk u w P → F'.Connected v u → F'.Connected v w from
    hs v hP (connected_refl _ _)
  intro u hPu
  clear hP
  induction hPu with
  | nil => exact id
  | @cons u₀ v₀ x P₀ hx hsrc _ ih =>
    intro hc
    rw [← hsrc, src_eq_of_sub h.sub hx] at hc
    have hd := (h.edge hx hc).2.2.2
    rw [← dst_eq_of_sub h.sub hx] at hd
    exact ih hd

/-- **Equal tours of a tree that the batch does not touch.** Under `TreeKept`, let `q` see the
same forest edges in `F` and `F'`, and keep every end of a new forest edge in the tree of `v`.
If the filtered orders are rotations of each other at every vertex of that tree, and are equal at
`v`, then the two tours at `v` are equal after the filter. -/
theorem tour_filter_eq (h : TreeKept G G' F F' B v) (ρ : Rotation G) (σ : Rotation G')
    (hF : F.IsForest) (hF' : F'.IsForest) (hVF : F.V = G.V) (hVF' : F'.V = G'.V)
    (q : End → Bool) (hbase : ∀ x : End, q x = true → (x.1 ∈ F.E ↔ x.1 ∈ F'.E))
    (hq : ∀ x : End, x.1 ∈ F'.E → F'.Connected v (G'.src x) → q x = true)
    (horder : ∀ w, F'.Connected v w → ((ρ.order w).filter q).IsRotated ((σ.order w).filter q))
    (hroot : (ρ.order v).filter q = (σ.order v).filter q) :
    (tour ρ hF v).filter q = (tour σ hF' v).filter q := by
  classical
  -- the common tree: the new forest edges in the tree of `v`
  let J : MGraph :=
    { V := G.V ∩ G'.V, E := F'.E.filter fun e => F'.Connected v (G'.tail e),
      tail := G'.tail, head := G'.head }
  have hJE : ∀ e, e ∈ J.E ↔ e ∈ F'.E ∧ F'.Connected v (G'.tail e) := fun e => Finset.mem_filter
  -- an edge of `J` keeps its endpoints
  have hJends : ∀ e ∈ J.E, G'.tail e = G.tail e ∧ G'.head e = G.head e := by
    intro e he
    obtain ⟨heF', hc⟩ := (hJE e).mp he
    have h' := h.edge' (x := (e, true)) heF' hc
    exact ⟨h'.1, h'.2.1⟩
  have hsub' : F'.IsSubgraph J := by
    refine ⟨fun w hw => hVF' ▸ (Finset.mem_inter.mp hw).2, fun e he => ((hJE e).mp he).1,
      fun e he => ?_⟩
    have := h.sub'.2.2 e ((hJE e).mp he).1
    exact ⟨this.1.symm, this.2.symm⟩
  have hsub : F.IsSubgraph J := by
    refine ⟨fun w hw => hVF ▸ (Finset.mem_inter.mp hw).1,
      fun e he => h.mono ((hJE e).mp he).1, fun e he => ?_⟩
    have hF := h.sub.2.2 e (h.mono ((hJE e).mp he).1)
    exact ⟨(hJends e he).1.trans hF.1.symm, (hJends e he).2.trans hF.2.symm⟩
  have hGJ : G.IsSubgraph J :=
    ⟨Finset.inter_subset_left, fun e he => h.sub.2.1 (hsub.2.1 he), fun e he => hJends e he⟩
  have hHJ : G'.IsSubgraph J :=
    ⟨Finset.inter_subset_right, fun e he => h.sub'.2.1 (hsub'.2.1 he),
      fun _ _ => ⟨rfl, rfl⟩⟩
  -- `J` is a forest, as a valid subgraph of `F'`
  have hJval : J.IsValid := by
    intro e he
    have hF'e := hF'.1 e (hsub'.2.1 he)
    have hFe := hF.1 e (hsub.2.1 he)
    have h1 := hsub'.2.2 e he
    have h2 := hsub.2.2 e he
    rw [← h1.1, ← h1.2, hVF'] at hF'e
    rw [← h2.1, ← h2.2, hVF] at hFe
    exact ⟨Finset.mem_inter.mpr ⟨hFe.1, hF'e.1⟩, Finset.mem_inter.mpr ⟨hFe.2, hF'e.2⟩⟩
  have hJ : J.IsForest := isForest_subgraph hF' hsub' hJval
  refine tour_filter_eq_of_common ρ σ hF hF' hJ hGJ hHJ hsub hsub' v ?_ ?_ q hbase ?_ ?_ hroot
  · -- an old forest edge reached from `v` is in `J`
    intro y hy hc
    rw [src_eq_of_sub h.sub hy] at hc
    have hc' := h.connected hc
    obtain ⟨hy', hs, -, -⟩ := h.edge hy hc'
    refine (hJE _).mpr ⟨hy', (conn_src_iff h.sub' hy').mp ?_⟩
    rwa [hs]
  · -- a new forest edge reached from `v` is in `J`
    intro y hy hc
    rw [src_eq_of_sub h.sub' hy] at hc
    exact (hJE _).mpr ⟨hy, (conn_src_iff h.sub' hy).mp hc⟩
  · intro x hx
    obtain ⟨hx', hc⟩ := (hJE _).mp hx
    exact hq x hx' ((conn_src_iff h.sub' hx').mpr hc)
  · intro w hw
    exact horder w (connected_of_subgraph hsub' hw)

end TreeKept

end MinCostFlow.SparseCore.Program
