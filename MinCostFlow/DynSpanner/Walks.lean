module

public import MinCostFlow.Basic.Dynamic
public import MinCostFlow.Basic.Embedding
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Graph, walk, embedding, and dynamic-update helpers for dynamic spanners

This file collects structural lemmas on `MGraph`, `IsWalk`, `Embedding`, and `Update` (edge
deletions and vertex splits) used by the dynamic spanner algorithm of Theorem 8.2:
* Walk concatenation, reversal (`walkRev`), vertex lists (`walkVertices_walkRev`), and subgraph
  monotonicity.
* Identity embedding `idEmb`, composition `Embedding.comp` preservation of `IsEmbedding` and
  `length`, and vertex-congestion transfer via an ancestor map (`vcong_le_of_map`).
* Handshaking (`two_mul_m_le_n_mul_maxDeg`) and isolated-vertex removal (`activeSubgraph`).
* Valid deletions and vertex splits: preservation of `IsValid`, edge monotonicity, degree bounds,
  vertex-ancestor tracking (`stepAnc`, `batchAnc`), and Lemma 2.1's degree-entropy potential
  (`degPot`, bounding `batchEnc` by updates plus edge insertions).
-/

namespace MinCostFlow.DynSpanner

section Walks

@[expose] public section

/-- Concatenation of two matching walks is a walk. -/
theorem IsWalk.append {G : MGraph} {u v w : ℕ} {P Q : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hQ : G.IsWalk v w Q) : G.IsWalk u w (P ++ Q) := by
  induction hP with
  | nil => simpa using hQ
  | cons he hsrc _ ih => exact .cons he hsrc (ih hQ)

/-- Every oriented edge in a walk belongs to `G.E`. -/
theorem IsWalk.mem_edge {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : ∀ x ∈ P, x.1 ∈ G.E := by
  induction hP with
  | nil => intro x hx; simp at hx
  | cons he _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he
    · exact ih x hx

/-- Every vertex in `G.walkVertices u P` is a vertex of `G` when `G` is valid and `u ∈ G.V`. -/
theorem IsWalk.walkVertices_mem_V {G : MGraph} (hV : G.IsValid) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hu : u ∈ G.V) : ∀ z ∈ G.walkVertices u P, z ∈ G.V := by
  induction hP with
  | nil _ =>
    intro z hz
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hz
    rwa [hz]
  | cons he hsrc _ ih =>
    rename_i u' v' x P' hrest
    intro z hz
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz
    have hdst : G.dst x ∈ G.V := by
      cases xb : x.2
      · simp [MGraph.dst, xb]; exact (hV x.1 he).1
      · simp [MGraph.dst, xb]; exact (hV x.1 he).2
    rcases hz with rfl | rfl | hz
    · exact hu
    · exact hdst
    · exact ih hdst z (by simp [MGraph.walkVertices, hz])

/-- The start vertex belongs to `walkVertices`. -/
theorem mem_walkVertices_start (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) :
    u ∈ G.walkVertices u P := by
  simp [MGraph.walkVertices]

/-- The end vertex of a walk belongs to `walkVertices`. -/
theorem IsWalk.end_mem_walkVertices {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : v ∈ G.walkVertices u P := by
  induction hP with
  | nil _ => simp [MGraph.walkVertices]
  | cons _ _ _ ih =>
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at ih ⊢
    rcases ih with rfl | hmem
    · right; left; rfl
    · right; right; exact hmem

/-- Membership in `walkVertices` of an appended walk. -/
theorem IsWalk.mem_walkVertices_append {G : MGraph} {u v _w : ℕ} {P Q : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) :
    ∀ z, z ∈ G.walkVertices u (P ++ Q) ↔ z ∈ G.walkVertices u P ∨ z ∈ G.walkVertices v Q := by
  intro z
  have hv : v ∈ G.walkVertices u P := IsWalk.end_mem_walkVertices hP
  simp only [MGraph.walkVertices, List.map_append, List.mem_cons, List.mem_append] at hv ⊢
  constructor
  · rintro (rfl | hzP | hzQ)
    · left; left; rfl
    · left; right; exact hzP
    · right; right; exact hzQ
  · rintro ((rfl | hzP) | (rfl | hzQ))
    · left; rfl
    · right; left; exact hzP
    · rcases hv with rfl | hvP
      · left; rfl
      · right; left; exact hvP
    · right; right; exact hzQ

@[simp] theorem MGraph.src_flip (G : MGraph) (x : ℕ × Bool) :
    G.src (x.1, !x.2) = G.dst x := by
  rcases x with ⟨e, b⟩
  cases b <;> simp [MGraph.src, MGraph.dst]

@[simp] theorem MGraph.dst_flip (G : MGraph) (x : ℕ × Bool) :
    G.dst (x.1, !x.2) = G.src x := by
  rcases x with ⟨e, b⟩
  cases b <;> simp [MGraph.src, MGraph.dst]

/-- Reversing a walk gives a walk between the swapped endpoints. -/
theorem isWalk_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : G.IsWalk v u (walkRev P) := by
  induction hP with
  | nil _ => simp [walkRev]; exact .nil _
  | @cons u' _ x _ he hsrc _ ih =>
    simp only [walkRev, List.map_cons, List.reverse_cons]
    refine IsWalk.append ih (.cons he (by simp) ?_)
    rw [MGraph.dst_flip, hsrc]
    exact .nil u'

/-- Reversing a walk reverses its vertex list. -/
theorem walkVertices_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) :
    G.walkVertices v (walkRev P) = (G.walkVertices u P).reverse := by
  induction hP with
  | nil _ => simp [walkRev, MGraph.walkVertices]
  | cons _ hsrc _ ih =>
    simp only [walkRev, MGraph.walkVertices, List.map_cons, List.reverse_cons,
      List.map_append, MGraph.dst_flip, hsrc] at ih ⊢
    rw [← List.cons_append, ih]
    simp

theorem mem_walkVertices_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (z : ℕ) :
    z ∈ G.walkVertices v (walkRev P) ↔ z ∈ G.walkVertices u P := by
  rw [walkVertices_walkRev hP, List.mem_reverse]

@[simp] theorem walkEdges_nil : walkEdges [] = ∅ := by
  simp [walkEdges]

@[simp] theorem walkEdges_singleton (x : ℕ × Bool) : walkEdges [x] = {x.1} := by
  simp [walkEdges]

theorem walkEdges_append (P Q : List (ℕ × Bool)) :
    walkEdges (P ++ Q) = walkEdges P ∪ walkEdges Q := by
  simp [walkEdges, List.toFinset_append]

theorem walkEdges_walkRev (P : List (ℕ × Bool)) :
    walkEdges (walkRev P) = walkEdges P := by
  ext e
  simp [walkEdges, walkRev]

theorem mem_walkEdges_iff {e : ℕ} {P : List (ℕ × Bool)} :
    e ∈ walkEdges P ↔ ∃ x ∈ P, x.1 = e := by
  simp [walkEdges]

theorem walkEdges_subset_of_prefix {P Q : List (ℕ × Bool)} (h : P <+: Q) :
    walkEdges P ⊆ walkEdges Q := by
  obtain ⟨R, rfl⟩ := h
  rw [walkEdges_append]
  exact Finset.subset_union_left

theorem length_walkRev (P : List (ℕ × Bool)) : (walkRev P).length = P.length := by
  simp [walkRev]

theorem walkRev_append (P Q : List (ℕ × Bool)) :
    walkRev (P ++ Q) = walkRev Q ++ walkRev P := by
  simp [walkRev, List.map_append, List.reverse_append]

@[simp] theorem walkRev_walkRev (P : List (ℕ × Bool)) : walkRev (walkRev P) = P := by
  simp [walkRev, List.map_reverse, Function.comp_def]

/-- A walk in a subgraph `H ⊆ G` (`G.IsSubgraph H`) is also a walk in `G`. -/
theorem IsWalk.of_isSubgraph {G H : MGraph} (hSub : G.IsSubgraph H)
    {u v : ℕ} {P : List (ℕ × Bool)} (hP : H.IsWalk u v P) : G.IsWalk u v P := by
  induction hP with
  | nil _ => exact .nil _
  | @cons u' v' x P' he hsrc _ ih =>
    obtain ⟨ht, hh⟩ := hSub.2.2 x.1 he
    have hsrcG : G.src x = u' := by
      rw [← hsrc]
      cases hb : x.2 <;> simp [MGraph.src, ht, hh, hb]
    have hdstG : G.dst x = H.dst x := by
      cases hb : x.2 <;> simp [MGraph.dst, ht, hh, hb]
    refine .cons (hSub.2.1 he) hsrcG ?_
    rwa [hdstG]

/-- A walk in `G` whose edges all belong to a subgraph `H ⊆ G` is a walk in `H`. -/
theorem IsWalk.to_isSubgraph {G H : MGraph} (hSub : G.IsSubgraph H)
    {u v : ℕ} {P : List (ℕ × Bool)} (hP : G.IsWalk u v P) (hE : ∀ x ∈ P, x.1 ∈ H.E) :
    H.IsWalk u v P := by
  induction hP with
  | nil _ => exact .nil _
  | @cons u' v' x P' _ hsrc _ ih =>
    have hxH : x.1 ∈ H.E := hE x List.mem_cons_self
    obtain ⟨ht, hh⟩ := hSub.2.2 x.1 hxH
    have hsrcH : H.src x = u' := by
      rw [← hsrc]
      cases hb : x.2 <;> simp [MGraph.src, ht, hh, hb]
    have hdstH : H.dst x = G.dst x := by
      cases hb : x.2 <;> simp [MGraph.dst, ht, hh, hb]
    refine .cons hxH hsrcH ?_
    rw [hdstH]
    exact ih (fun y hy => hE y (List.mem_cons_of_mem _ hy))

/-- Two graphs agreeing on `tail`/`head` on all edges of `P` produce the same `walkVertices`. -/
theorem walkVertices_congr {H₁ H₂ : MGraph} (u : ℕ) {P : List (ℕ × Bool)}
    (h : ∀ x ∈ P, H₁.dst x = H₂.dst x) : H₁.walkVertices u P = H₂.walkVertices u P := by
  simp only [MGraph.walkVertices, List.cons.injEq, true_and]
  exact List.map_congr_left h

theorem walkVertices_of_isSubgraph {G H : MGraph} (hSub : G.IsSubgraph H)
    {u v : ℕ} {P : List (ℕ × Bool)} (hP : H.IsWalk u v P) :
    G.walkVertices u P = H.walkVertices u P := by
  refine walkVertices_congr u fun x hx => ?_
  have hxH := IsWalk.mem_edge hP x hx
  obtain ⟨ht, hh⟩ := hSub.2.2 x.1 hxH
  cases xb : x.2 <;> simp [MGraph.dst, ht, hh, xb]

theorem isWalk_mem_walkVertices_src_dst {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P →
      ∀ y ∈ P, G.src y ∈ G.walkVertices u P ∧ G.dst y ∈ G.walkVertices u P := by
  intro u v P hW
  induction hW with
  | nil _ => intro y hy; simp at hy
  | @cons u' _ x P' _ hsrc _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨hsrc ▸ mem_walkVertices_start _ _ _, by simp [MGraph.walkVertices]⟩
    · obtain ⟨hs, hd⟩ := ih y hy'
      exact ⟨by simp [MGraph.walkVertices] at hs ⊢; right; exact hs,
        by simp [MGraph.walkVertices] at hd ⊢; right; exact hd⟩

theorem isPath_edges_nodup {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) : (P.map Prod.fst).Nodup := by
  rcases hP with ⟨hW, hnd⟩
  induction hW with
  | nil _ => simp
  | @cons u' _ x P' _ hsrc hW ih =>
    change (u' :: G.walkVertices (G.dst x) P').Nodup at hnd
    rw [List.nodup_cons] at hnd
    have ih' := ih hnd.2
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih'⟩
    rintro ⟨y, hyP, hyfst⟩
    obtain ⟨hys, hyd⟩ := isWalk_mem_walkVertices_src_dst hW y hyP
    have hu_mem : u' ∈ G.walkVertices (G.dst x) P' := by
      rw [← hsrc]
      cases xb : x.2 <;> cases yb : y.2 <;>
        simp [MGraph.src, MGraph.dst, xb, yb, hyfst] at hys hyd ⊢ <;>
        first | exact hys | exact hyd
    exact hnd.1 hu_mem

/-- Drop the prefix of `Q` up to the first occurrence of vertex `target` (starting at `cur`). -/
def suffixFrom (G : MGraph) (target cur : ℕ) : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => []
  | x :: xs => if cur = target then x :: xs else suffixFrom G target (G.dst x) xs

/-- Prepend step `x` (starting at `u`) onto a simple walk `Q`, shortcutting any cycle at `u`. -/
def shortcutStep (G : MGraph) (u : ℕ) (x : ℕ × Bool) (Q : List (ℕ × Bool)) : List (ℕ × Bool) :=
  if u ∈ G.walkVertices (G.dst x) Q then suffixFrom G u (G.dst x) Q else x :: Q

/-- Computably remove repeated vertices from a walk `P` starting at `u`, producing a simple path
with the same endpoints, no greater length, and subset of edges and vertices. -/
def shortcutWalk (G : MGraph) (u : ℕ) : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => []
  | x :: P => shortcutStep G u x (shortcutWalk G (G.dst x) P)

private theorem suffixFrom_length_le (G : MGraph) (target cur : ℕ) (Q : List (ℕ × Bool)) :
    (suffixFrom G target cur Q).length ≤ Q.length := by
  induction Q generalizing cur with
  | nil => simp [suffixFrom]
  | cons x xs ih =>
    simp only [suffixFrom]
    split_ifs
    · exact le_rfl
    · exact Nat.le_succ_of_le (ih (G.dst x))

private theorem suffixFrom_walkEdges_subset (G : MGraph) (target cur : ℕ) (Q : List (ℕ × Bool)) :
    walkEdges (suffixFrom G target cur Q) ⊆ walkEdges Q := by
  induction Q generalizing cur with
  | nil => simp [suffixFrom]
  | cons x xs ih =>
    simp only [suffixFrom]
    split_ifs
    · exact Finset.Subset.rfl
    · intro e he
      have he' := ih (G.dst x) he
      rw [mem_walkEdges_iff] at he' ⊢
      rcases he' with ⟨y, hy, rfl⟩
      exact ⟨y, List.mem_cons_of_mem x hy, rfl⟩

private theorem suffixFrom_walkVertices_nodup (G : MGraph) (target : ℕ) :
    ∀ (Q : List (ℕ × Bool)) (cur : ℕ),
      (G.walkVertices cur Q).Nodup → target ∈ G.walkVertices cur Q →
      (G.walkVertices target (suffixFrom G target cur Q)).Nodup
  | [], _, _, _ => by
    simp [suffixFrom, MGraph.walkVertices]
  | x :: xs, cur, hnd, hmem => by
    simp only [suffixFrom]
    split_ifs with hct
    · rwa [← hct]
    · change (cur :: G.walkVertices (G.dst x) xs).Nodup at hnd
      rw [List.nodup_cons] at hnd
      have hmem' : target ∈ G.walkVertices (G.dst x) xs := by
        change target ∈ cur :: G.walkVertices (G.dst x) xs at hmem
        exact (List.mem_cons.mp hmem).resolve_left (Ne.symm hct)
      exact suffixFrom_walkVertices_nodup G target xs (G.dst x) hnd.2 hmem'

private theorem suffixFrom_walkVertices_subset (G : MGraph) (target : ℕ) :
    ∀ (Q : List (ℕ × Bool)) (cur : ℕ),
      target ∈ G.walkVertices cur Q →
      ∀ z ∈ G.walkVertices target (suffixFrom G target cur Q), z ∈ G.walkVertices cur Q
  | [], cur, hmem, z, hz => by
    simp only [suffixFrom, MGraph.walkVertices, List.map_nil, List.mem_singleton] at hmem hz ⊢
    rw [hz, hmem]
  | x :: xs, cur, hmem, z, hz => by
    simp only [suffixFrom] at hz
    split_ifs at hz with hct
    · rwa [hct]
    · have hmem' : target ∈ G.walkVertices (G.dst x) xs := by
        change target ∈ cur :: G.walkVertices (G.dst x) xs at hmem
        exact (List.mem_cons.mp hmem).resolve_left (Ne.symm hct)
      have hz' := suffixFrom_walkVertices_subset G target xs (G.dst x) hmem' z hz
      change z ∈ cur :: G.walkVertices (G.dst x) xs
      exact List.mem_cons_of_mem cur hz'

private theorem suffixFrom_isWalk {G H : MGraph} (ht : H.tail = G.tail) (hh : H.head = G.head)
    (target : ℕ) : ∀ {cur v : ℕ} {Q : List (ℕ × Bool)},
      H.IsWalk cur v Q → target ∈ G.walkVertices cur Q →
      H.IsWalk target v (suffixFrom G target cur Q)
  | cur, _, [], .nil _, hmem => by
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hmem
    subst hmem
    simp [suffixFrom]; exact .nil target
  | cur, v, x :: xs, .cons he hsrc hW, hmem => by
    simp only [suffixFrom]
    split_ifs with hct
    · rw [← hct]; exact .cons he hsrc hW
    · have hdst : H.dst x = G.dst x := by
        cases xb : x.2 <;> simp [MGraph.dst, ht, hh, xb]
      have hmem' : target ∈ G.walkVertices (G.dst x) xs := by
        change target ∈ cur :: G.walkVertices (G.dst x) xs at hmem
        exact (List.mem_cons.mp hmem).resolve_left (Ne.symm hct)
      exact suffixFrom_isWalk ht hh target (hdst ▸ hW) hmem'

theorem walkVertices_congr_ends {G H : MGraph} (ht : H.tail = G.tail) (hh : H.head = G.head)
    (u : ℕ) (P : List (ℕ × Bool)) : H.walkVertices u P = G.walkVertices u P := by
  refine walkVertices_congr u fun x _ => ?_
  cases xb : x.2 <;> simp [MGraph.dst, ht, hh, xb]

theorem shortcutWalk_nodup (G : MGraph) :
    ∀ (P : List (ℕ × Bool)) (u : ℕ), (G.walkVertices u (shortcutWalk G u P)).Nodup
  | [], u => by simp [shortcutWalk, MGraph.walkVertices]
  | x :: P, u => by
    simp only [shortcutWalk, shortcutStep]
    have ih := shortcutWalk_nodup G P (G.dst x)
    split_ifs with hmem
    · exact suffixFrom_walkVertices_nodup G u (shortcutWalk G (G.dst x) P) (G.dst x) ih hmem
    · change (u :: G.walkVertices (G.dst x) (shortcutWalk G (G.dst x) P)).Nodup
      exact List.nodup_cons.mpr ⟨hmem, ih⟩

theorem shortcutWalk_length_le (G : MGraph) :
    ∀ (P : List (ℕ × Bool)) (u : ℕ), (shortcutWalk G u P).length ≤ P.length
  | [], _ => by simp [shortcutWalk]
  | x :: P, u => by
    simp only [shortcutWalk, shortcutStep]
    have ih := shortcutWalk_length_le G P (G.dst x)
    split_ifs
    · exact Nat.le_succ_of_le (le_trans (suffixFrom_length_le G u (G.dst x) _) ih)
    · simpa using Nat.succ_le_succ ih

theorem shortcutWalk_walkEdges_subset (G : MGraph) :
    ∀ (P : List (ℕ × Bool)) (u : ℕ), walkEdges (shortcutWalk G u P) ⊆ walkEdges P
  | [], _ => by simp [shortcutWalk]
  | x :: P, u => by
    simp only [shortcutWalk, shortcutStep]
    have ih := shortcutWalk_walkEdges_subset G P (G.dst x)
    split_ifs
    · exact Finset.Subset.trans (suffixFrom_walkEdges_subset G u (G.dst x) _)
        (Finset.Subset.trans ih fun e he => by
          rw [mem_walkEdges_iff] at he ⊢
          rcases he with ⟨y, hy, rfl⟩
          exact ⟨y, List.mem_cons_of_mem x hy, rfl⟩)
    · intro e he
      rw [mem_walkEdges_iff] at he ⊢
      rcases he with ⟨y, hy, rfl⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨y, List.mem_cons_self, rfl⟩
      · have := ih (mem_walkEdges_iff.mpr ⟨y, hy', rfl⟩)
        rw [mem_walkEdges_iff] at this
        rcases this with ⟨z, hz, hzf⟩
        exact ⟨z, List.mem_cons_of_mem x hz, hzf⟩

theorem shortcutWalk_walkVertices_subset (G : MGraph) :
    ∀ (P : List (ℕ × Bool)) (u : ℕ) (z : ℕ),
      z ∈ G.walkVertices u (shortcutWalk G u P) → z ∈ G.walkVertices u P
  | [], u, z, hz => by simpa [shortcutWalk] using hz
  | x :: P, u, z, hz => by
    simp only [shortcutWalk, shortcutStep] at hz
    split_ifs at hz with hmem
    · have hz1 := suffixFrom_walkVertices_subset G u _ (G.dst x) hmem z hz
      have hz2 := shortcutWalk_walkVertices_subset G P (G.dst x) z hz1
      simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz2 ⊢
      exact Or.inr hz2
    · simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz ⊢
      rcases hz with rfl | hzd
      · left; rfl
      · right
        have hz2 := shortcutWalk_walkVertices_subset G P (G.dst x) z
          (by simpa [MGraph.walkVertices] using hzd)
        simpa [MGraph.walkVertices] using hz2

theorem shortcutWalk_isWalk {G H : MGraph} (ht : H.tail = G.tail) (hh : H.head = G.head) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P → H.IsWalk u v (shortcutWalk G u P)
  | u, _, [], .nil _ => by simp [shortcutWalk]; exact .nil u
  | u, v, x :: P, .cons he hsrc hW => by
    have hdst : H.dst x = G.dst x := by
      cases xb : x.2 <;> simp [MGraph.dst, ht, hh, xb]
    have ih : H.IsWalk (G.dst x) v (shortcutWalk G (G.dst x) P) := by
      rw [← hdst]
      exact shortcutWalk_isWalk ht hh hW
    simp only [shortcutWalk, shortcutStep]
    split_ifs with hmem
    · exact suffixFrom_isWalk ht hh u ih hmem
    · exact .cons he hsrc (hdst ▸ ih)

theorem shortcutWalk_isPath {G H : MGraph} (ht : H.tail = G.tail) (hh : H.head = G.head)
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : H.IsWalk u v P) :
    H.IsPath u v (shortcutWalk G u P) :=
  ⟨shortcutWalk_isWalk ht hh hW,
    by rw [walkVertices_congr_ends ht hh]; exact shortcutWalk_nodup G P u⟩

private theorem suffixFrom_sublist (G : MGraph) (target : ℕ) :
    ∀ (Q : List (ℕ × Bool)) (cur : ℕ), List.Sublist (suffixFrom G target cur Q) Q
  | [], _ => by simp [suffixFrom]
  | x :: xs, cur => by
    simp only [suffixFrom]
    split_ifs
    · exact List.Sublist.refl _
    · exact List.sublist_cons_of_sublist x (suffixFrom_sublist G target xs (G.dst x))

theorem shortcutWalk_sublist (G : MGraph) :
    ∀ (P : List (ℕ × Bool)) (u : ℕ), List.Sublist (shortcutWalk G u P) P
  | [], _ => by simp [shortcutWalk]
  | x :: P, u => by
    simp only [shortcutWalk, shortcutStep]
    have ih := shortcutWalk_sublist G P (G.dst x)
    split_ifs
    · exact List.sublist_cons_of_sublist x (List.Sublist.trans (suffixFrom_sublist G u _ (G.dst x)) ih)
    · exact ih.cons_cons x

theorem comp_sublist_of_sublist (embBC emb₁ emb₂ : Embedding) {e : ℕ}
    (h : List.Sublist (emb₁ e) (emb₂ e)) :
    List.Sublist (Embedding.comp embBC emb₁ e) (Embedding.comp embBC emb₂ e) := by
  unfold Embedding.comp
  exact (h.map _).flatten

end

end Walks

section Embeddings

@[expose] public section

/-- The identity embedding mapping each edge `e` to the single-step walk `[(e, true)]`. -/
def idEmb : Embedding := fun e => [(e, true)]

theorem idEmb_isEmbedding (G : MGraph) : idEmb.IsEmbedding G G := by
  refine ⟨Finset.Subset.rfl, fun e he => ?_⟩
  exact .cons he (by simp [MGraph.src]) (.nil (G.head e))

@[simp] theorem comp_idEmb (emb : Embedding) : Embedding.comp emb idEmb = emb := by
  funext e
  simp [Embedding.comp, idEmb]

@[simp] theorem idEmb_comp (emb : Embedding) : Embedding.comp idEmb emb = emb := by
  funext e
  simp only [Embedding.comp, idEmb]
  induction emb e with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨e', b⟩
    cases b
    · simp only [List.flatMap_cons, Bool.false_eq_true, ↓reduceIte, walkRev, List.map_cons,
        List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      exact congrArg (List.cons (e', false)) ih
    · simp only [List.flatMap_cons, ↓reduceIte, List.singleton_append]
      exact congrArg (List.cons (e', true)) ih

theorem idEmb_length_le (G : MGraph) : idEmb.length G ≤ 1 := by
  unfold Embedding.length
  rw [Finset.sup_le_iff]
  intro e _
  simp [idEmb]

theorem idEmb_length_eq_one {G : MGraph} (hE : G.E.Nonempty) : idEmb.length G = 1 := by
  refine le_antisymm (idEmb_length_le G) ?_
  obtain ⟨e, he⟩ := hE
  have hle : (idEmb e).length ≤ idEmb.length G := Finset.le_sup (f := fun e => (idEmb e).length) he
  simpa [idEmb] using hle

theorem idEmb_vcong_le (G : MGraph) : idEmb.vcong G G (fun _ => 1) ≤ (G.maxDeg : ℝ) := by
  unfold Embedding.vcong
  split_ifs with hV
  · rw [Finset.sup'_le_iff]
    intro v hv
    unfold Embedding.vcongAt
    have hcard :
        (G.E.filter fun e => v ∈ G.walkVertices (G.tail e) (idEmb e)).card ≤ G.deg v := by
      have hsub : (G.E.filter fun e => v ∈ G.walkVertices (G.tail e) (idEmb e)) ⊆
          (G.E.filter fun e => G.tail e = v) ∪ (G.E.filter fun e => G.head e = v) := by
        intro e he
        simp only [Finset.mem_filter, Finset.mem_union, MGraph.walkVertices, idEmb,
          List.map_cons, List.map_nil, MGraph.dst, ↓reduceIte, List.mem_cons,
          List.not_mem_nil, or_false] at he ⊢
        rcases he with ⟨heE, htail | hhead⟩
        · left; exact ⟨heE, htail.symm⟩
        · right; exact ⟨heE, hhead.symm⟩
      calc (G.E.filter fun e => v ∈ G.walkVertices (G.tail e) (idEmb e)).card
          ≤ ((G.E.filter fun e => G.tail e = v) ∪ (G.E.filter fun e => G.head e = v)).card :=
            Finset.card_le_card hsub
        _ ≤ (G.E.filter fun e => G.tail e = v).card + (G.E.filter fun e => G.head e = v).card :=
            Finset.card_union_le _ _
        _ = G.deg v := rfl
    have hsum : (∑ e ∈ G.E with v ∈ G.walkVertices (G.tail e) (idEmb e), (1 : ℝ)) =
        ((G.E.filter fun e => v ∈ G.walkVertices (G.tail e) (idEmb e)).card : ℝ) := by
      simp
    rw [hsum]
    exact_mod_cast le_trans hcard (Finset.le_sup (f := G.deg) hv)
  · exact Nat.cast_nonneg _

theorem IsWalk.comp_flatMap {B C : MGraph} {embBC : Embedding}
    (hBC : ∀ e ∈ B.E, C.IsWalk (B.tail e) (B.head e) (embBC e))
    {u v : ℕ} {P : List (ℕ × Bool)} (hP : B.IsWalk u v P) :
    C.IsWalk u v (P.flatMap fun x => if x.2 then embBC x.1 else walkRev (embBC x.1)) := by
  induction hP with
  | nil _ => simp; exact .nil _
  | cons he hsrc _ ih =>
    rename_i u' v' x P' hrest
    simp only [List.flatMap_cons]
    have hstep : C.IsWalk u' (B.dst x) (if x.2 then embBC x.1 else walkRev (embBC x.1)) := by
      have hw := hBC x.1 he
      cases xb : x.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hs : B.src x = B.head x.1 := by simp [MGraph.src, xb]
        have hd : B.dst x = B.tail x.1 := by simp [MGraph.dst, xb]
        rw [← hsrc, hs, hd]
        exact isWalk_walkRev hw
      · simp only [↓reduceIte]
        have hs : B.src x = B.tail x.1 := by simp [MGraph.src, xb]
        have hd : B.dst x = B.head x.1 := by simp [MGraph.dst, xb]
        rw [← hsrc, hs, hd]
        exact hw
    exact IsWalk.append hstep ih

/-- Composition of valid embeddings is a valid embedding. -/
theorem comp_isEmbedding {A B C : MGraph} {embAB embBC : Embedding}
    (hAB : embAB.IsEmbedding A B) (hBC : embBC.IsEmbedding B C) :
    (Embedding.comp embBC embAB).IsEmbedding A C := by
  refine ⟨Finset.Subset.trans hAB.1 hBC.1, fun e he => ?_⟩
  exact IsWalk.comp_flatMap hBC.2 (hAB.2 e he)

theorem flatMap_length_le {P : List (ℕ × Bool)} {B : MGraph} {emb : Embedding}
    (hE : ∀ x ∈ P, x.1 ∈ B.E) :
    (P.flatMap fun x => if x.2 then emb x.1 else walkRev (emb x.1)).length ≤
      P.length * emb.length B := by
  induction P with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have hx : (if x.2 then emb x.1 else walkRev (emb x.1)).length ≤ emb.length B := by
      have hxE : x.1 ∈ B.E := hE x List.mem_cons_self
      have hlen : (emb x.1).length ≤ emb.length B :=
        Finset.le_sup (f := fun e => (emb e).length) hxE
      cases x.2 <;> simpa [length_walkRev] using hlen
    have hxs := ih (fun y hy => hE y (List.mem_cons_of_mem _ hy))
    omega

/-- Length of composed embeddings is at most the product of lengths. -/
theorem comp_length_le {A B : MGraph} {embAB embBC : Embedding}
    (hAB : embAB.IsEmbedding A B) :
    (Embedding.comp embBC embAB).length A ≤ embAB.length A * embBC.length B := by
  unfold Embedding.length
  rw [Finset.sup_le_iff]
  intro e he
  have hw := hAB.2 e he
  have h1 := flatMap_length_le (emb := embBC) (B := B) (fun x hx => IsWalk.mem_edge hw x hx)
  have h2 : (embAB e).length ≤ embAB.length A :=
    Finset.le_sup (f := fun e => (embAB e).length) he
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

theorem vcongAt_nonneg (emb : Embedding) (G H : MGraph) (v : ℕ) :
    0 ≤ emb.vcongAt G H (fun _ => 1) v := by
  unfold Embedding.vcongAt
  simp

theorem vcong_nonneg (emb : Embedding) (G H : MGraph) :
    0 ≤ emb.vcong G H (fun _ => 1) := by
  unfold Embedding.vcong
  split_ifs with hV
  · exact le_trans (vcongAt_nonneg emb G H hV.choose) (Finset.le_sup' _ hV.choose_spec)
  · exact le_rfl

/-- Vertex congestion on unit edge weights is bounded via any vertex-ancestor map preserving
walk-vertex membership. -/
theorem vcong_le_of_map {emb₁ emb₂ : Embedding} {G₁ G₂ H₁ H₂ : MGraph}
    (hE : G₁.E ⊆ G₂.E) (anc : ℕ → ℕ)
    (hAncV : ∀ v ∈ H₁.V, anc v ∈ H₂.V)
    (hAncWalk : ∀ v ∈ H₁.V, ∀ e ∈ G₁.E,
      v ∈ H₁.walkVertices (G₁.tail e) (emb₁ e) →
      anc v ∈ H₂.walkVertices (G₂.tail e) (emb₂ e)) :
    emb₁.vcong G₁ H₁ (fun _ => 1) ≤ emb₂.vcong G₂ H₂ (fun _ => 1) := by
  unfold Embedding.vcong
  by_cases h₁ : H₁.V.Nonempty <;> by_cases h₂ : H₂.V.Nonempty <;>
    simp only [h₁, h₂, ↓reduceDIte]
  · rw [Finset.sup'_le_iff]
    intro v hv
    have hAncMem : anc v ∈ H₂.V := hAncV v hv
    refine le_trans ?_ (Finset.le_sup' (Embedding.vcongAt emb₂ G₂ H₂ (fun _ => 1)) hAncMem)
    unfold Embedding.vcongAt
    have hsub : (G₁.E.filter fun e => v ∈ H₁.walkVertices (G₁.tail e) (emb₁ e)) ⊆
        (G₂.E.filter fun e => anc v ∈ H₂.walkVertices (G₂.tail e) (emb₂ e)) := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨hE he.1, hAncWalk v hv e he.1 he.2⟩
    simpa using Finset.card_le_card hsub
  · exfalso
    obtain ⟨v, hv⟩ := h₁
    exact h₂ ⟨anc v, hAncV v hv⟩
  · obtain ⟨v, hv⟩ := h₂
    exact le_trans (vcongAt_nonneg emb₂ G₂ H₂ v) (Finset.le_sup' _ hv)
  · exact le_rfl

theorem comp_length_le_of_sublist {A : MGraph} {embBC emb₁ emb₂ : Embedding}
    (h : ∀ e ∈ A.E, List.Sublist (emb₁ e) (emb₂ e)) :
    (Embedding.comp embBC emb₁).length A ≤ (Embedding.comp embBC emb₂).length A := by
  unfold Embedding.length
  rw [Finset.sup_le_iff]
  intro e he
  exact le_trans (comp_sublist_of_sublist embBC emb₁ emb₂ (h e he)).length_le
    (Finset.le_sup (f := fun x => (Embedding.comp embBC emb₂ x).length) he)

theorem comp_vcong_le_of_sublist {A H : MGraph} {embBC emb₁ emb₂ : Embedding}
    (h : ∀ e ∈ A.E, List.Sublist (emb₁ e) (emb₂ e)) :
    (Embedding.comp embBC emb₁).vcong A H (fun _ => 1) ≤
      (Embedding.comp embBC emb₂).vcong A H (fun _ => 1) := by
  refine vcong_le_of_map Finset.Subset.rfl id (fun _ hv => hv) fun v _ e he hv => ?_
  simp only [MGraph.walkVertices, List.mem_cons] at hv ⊢
  rcases hv with rfl | hv'
  · exact Or.inl rfl
  · exact Or.inr (((comp_sublist_of_sublist embBC emb₁ emb₂ (h e he)).map H.dst).mem hv')

/-- When `G` and `H₂` are valid and `emb` maps `G` into `H₂ ⊆ H₁`, vertex congestion in `H₁`
equals vertex congestion in `H₂`. -/
theorem vcong_eq_of_isSubgraph {G H₁ H₂ : MGraph} (hVG : G.IsValid) (hVH₂ : H₂.IsValid)
    (hSub : H₁.IsSubgraph H₂) {emb : Embedding} (hEmb : emb.IsEmbedding G H₂) :
    emb.vcong G H₁ (fun _ => 1) = emb.vcong G H₂ (fun _ => 1) := by
  have hcongr : ∀ e ∈ G.E, H₁.walkVertices (G.tail e) (emb e) =
      H₂.walkVertices (G.tail e) (emb e) :=
    fun e he => walkVertices_of_isSubgraph hSub (hEmb.2 e he)
  have hAtEq : ∀ v, emb.vcongAt G H₁ (fun _ => 1) v = emb.vcongAt G H₂ (fun _ => 1) v := by
    intro v
    unfold Embedding.vcongAt
    have hflt : (G.E.filter fun e => v ∈ H₁.walkVertices (G.tail e) (emb e)) =
        (G.E.filter fun e => v ∈ H₂.walkVertices (G.tail e) (emb e)) := by
      ext e
      simp only [Finset.mem_filter]
      exact and_congr_right fun he => by rw [hcongr e he]
    rw [hflt]
  apply le_antisymm
  · unfold Embedding.vcong
    by_cases h₁ : H₁.V.Nonempty <;> by_cases h₂ : H₂.V.Nonempty <;>
      simp only [h₁, h₂, ↓reduceDIte]
    · rw [Finset.sup'_le_iff]
      intro v _
      by_cases hv₂ : v ∈ H₂.V
      · rw [hAtEq v]
        exact Finset.le_sup' (Embedding.vcongAt emb G H₂ (fun _ => 1)) hv₂
      · have hzero : emb.vcongAt G H₁ (fun _ => 1) v = 0 := by
          rw [hAtEq v]
          unfold Embedding.vcongAt
          have hflt : (G.E.filter fun e => v ∈ H₂.walkVertices (G.tail e) (emb e)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro e he hmem
            have htailV : G.tail e ∈ H₂.V := hEmb.1 (hVG e he).1
            exact hv₂ (IsWalk.walkVertices_mem_V hVH₂ (hEmb.2 e he) htailV _ hmem)
          simp [hflt]
        rw [hzero]
        obtain ⟨w, hw⟩ := h₂
        exact le_trans (vcongAt_nonneg emb G H₂ w) (Finset.le_sup' _ hw)
    · rw [Finset.sup'_le_iff]
      intro v _
      rw [hAtEq v]
      unfold Embedding.vcongAt
      have hflt : (G.E.filter fun e => v ∈ H₂.walkVertices (G.tail e) (emb e)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he _
        have htailV : G.tail e ∈ H₂.V := hEmb.1 (hVG e he).1
        exact absurd htailV (fun h => h₂ ⟨G.tail e, h⟩)
      simp [hflt]
    · obtain ⟨w, hw⟩ := h₂
      exact le_trans (vcongAt_nonneg emb G H₂ w) (Finset.le_sup' _ hw)
    · exact le_rfl
  · unfold Embedding.vcong
    by_cases h₂ : H₂.V.Nonempty <;> by_cases h₁ : H₁.V.Nonempty <;>
      simp only [h₁, h₂, ↓reduceDIte]
    · rw [Finset.sup'_le_iff]
      intro v hv
      rw [← hAtEq v]
      exact Finset.le_sup' (Embedding.vcongAt emb G H₁ (fun _ => 1)) (hSub.1 hv)
    · exfalso
      obtain ⟨v, hv⟩ := h₂
      exact h₁ ⟨v, hSub.1 hv⟩
    · obtain ⟨w, hw⟩ := h₁
      exact le_trans (vcongAt_nonneg emb G H₁ w) (Finset.le_sup' _ hw)
    · exact le_rfl

end

end Embeddings

section DegreesAndActive

@[expose] public section

/-- Handshaking: for any valid `MGraph`, `∑ v ∈ G.V, G.deg v = 2 * G.m`. -/
theorem sum_deg_eq_two_mul_m {G : MGraph} (hV : G.IsValid) :
    ∑ v ∈ G.V, G.deg v = 2 * G.m := by
  have hdeg : ∀ v, G.deg v =
      (∑ e ∈ G.E, if G.tail e = v then 1 else 0) +
      (∑ e ∈ G.E, if G.head e = v then 1 else 0) := by
    intro v
    simp [MGraph.deg, Finset.card_filter]
  simp_rw [hdeg, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun v e => if G.head e = v then 1 else 0)]
  have h1 : (∑ e ∈ G.E, ∑ v ∈ G.V, if G.tail e = v then 1 else 0) = G.m := by
    calc (∑ e ∈ G.E, ∑ v ∈ G.V, if G.tail e = v then 1 else 0)
        = ∑ e ∈ G.E, 1 := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [Finset.sum_ite_eq]
          simp [(hV e he).1]
      _ = G.m := by simp [MGraph.m]
  have h2 : (∑ e ∈ G.E, ∑ v ∈ G.V, if G.head e = v then 1 else 0) = G.m := by
    calc (∑ e ∈ G.E, ∑ v ∈ G.V, if G.head e = v then 1 else 0)
        = ∑ e ∈ G.E, 1 := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [Finset.sum_ite_eq]
          simp [(hV e he).2]
      _ = G.m := by simp [MGraph.m]
  rw [h1, h2, two_mul]

/-- In any valid `MGraph`, `2 * G.m ≤ G.n * G.maxDeg`. -/
theorem two_mul_m_le_n_mul_maxDeg {G : MGraph} (hV : G.IsValid) :
    2 * G.m ≤ G.n * G.maxDeg := by
  rw [← sum_deg_eq_two_mul_m hV]
  calc ∑ v ∈ G.V, G.deg v
      ≤ ∑ _ ∈ G.V, G.maxDeg := Finset.sum_le_sum fun v hv => Finset.le_sup (f := G.deg) hv
    _ = G.n * G.maxDeg := by simp [MGraph.n, smul_eq_mul]

/-- The subgraph obtained by dropping isolated vertices (`deg v = 0`). -/
def activeSubgraph (G : MGraph) : MGraph :=
  { V := G.V.filter fun v => 1 ≤ G.deg v
    E := G.E
    tail := G.tail
    head := G.head }

theorem activeSubgraph_isSubgraph (G : MGraph) : G.IsSubgraph (activeSubgraph G) := by
  refine ⟨Finset.filter_subset _ _, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem activeSubgraph_isValid {G : MGraph} (hV : G.IsValid) : (activeSubgraph G).IsValid := by
  intro e he
  obtain ⟨ht, hh⟩ := hV e he
  refine ⟨Finset.mem_filter.mpr ⟨ht, ?_⟩, Finset.mem_filter.mpr ⟨hh, ?_⟩⟩
  · have hpos : 0 < (G.E.filter fun e' => G.tail e' = G.tail e).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    change 1 ≤ G.deg (G.tail e)
    unfold MGraph.deg
    omega
  · have hpos : 0 < (G.E.filter fun e' => G.head e' = G.head e).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    change 1 ≤ G.deg (G.head e)
    unfold MGraph.deg
    omega

theorem activeSubgraph_n_le (G : MGraph) : (activeSubgraph G).n ≤ G.n :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem activeSubgraph_deg_eq (G : MGraph) (v : ℕ) : (activeSubgraph G).deg v = G.deg v := rfl

theorem activeSubgraph_maxDeg_le (G : MGraph) : (activeSubgraph G).maxDeg ≤ G.maxDeg := by
  unfold MGraph.maxDeg
  rw [Finset.sup_le_iff]
  intro v hv
  have hvG : v ∈ G.V := (Finset.mem_filter.mp hv).1
  simpa [activeSubgraph_deg_eq] using Finset.le_sup (f := G.deg) hvG

theorem activeSubgraph_n_le_two_m {G : MGraph} (hV : G.IsValid) :
    (activeSubgraph G).n ≤ 2 * G.m := by
  have hsum : (activeSubgraph G).n ≤ ∑ v ∈ (activeSubgraph G).V, G.deg v := by
    calc (activeSubgraph G).n
        = ∑ _ ∈ (activeSubgraph G).V, 1 := by simp [MGraph.n]
      _ ≤ ∑ v ∈ (activeSubgraph G).V, G.deg v :=
          Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
  calc (activeSubgraph G).n
      ≤ ∑ v ∈ (activeSubgraph G).V, G.deg v := hsum
    _ ≤ ∑ v ∈ G.V, G.deg v := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 2 * G.m := sum_deg_eq_two_mul_m hV

theorem isEmbedding_activeSubgraph_of_isValid {G : MGraph} (_hV : G.IsValid) :
    idEmb.IsEmbedding (activeSubgraph G) (activeSubgraph G) :=
  idEmb_isEmbedding (activeSubgraph G)

end

end DegreesAndActive

section DynamicUpdates

@[expose] public section

/-- Predicate asserting an update is an edge deletion or a vertex split (no edge insertions). -/
def isDelOrSplit : Update → Prop
  | .insert _ _ _ => False
  | .delete _ => True
  | .split _ _ _ _ => True

/-- Boolean indicator of whether an update is a vertex split. -/
def isSplit : Update → Bool
  | .split _ _ _ _ => true
  | _ => false

/-- Number of vertex splits in a batch `U`. -/
def batchSplitCount (U : List Update) : ℕ :=
  U.countP isSplit

/-- Total number of updates across a prefix of batches `U 1, ..., U t`. -/
def totalUpdates (U : ℕ → List Update) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 t, (U s).length

/-- Total number of vertex splits across a prefix of batches `U 1, ..., U t`. -/
def totalSplits (U : ℕ → List Update) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 t, batchSplitCount (U s)

/-- Total encoding size of batches `U 1, ..., U t` applied starting from `G₀`. -/
def totalBatchEnc (G : ℕ → MGraph) (U : ℕ → List Update) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 t, (G (s - 1)).batchEnc (U s)

/-- Restrict a deletion or vertex split of `G` to a batch for a subgraph `H ⊆ G`. -/
def restrictUpdate (u : Update) (H : MGraph) : List Update :=
  match u with
  | .insert _ _ _ => []
  | .delete e => if e ∈ H.E then [.delete e] else []
  | .split v v' St Sh => [.split v v' (St ∩ H.E) (Sh ∩ H.E)]

/-- Vertex-ancestor function for a single update (mapping `v'` back to `v` on a split). -/
def stepAnc (u : Update) (z : ℕ) : ℕ :=
  match u with
  | .split v v' _ _ => if z = v' then v else z
  | _ => z

/-- Vertex-ancestor function across a list of updates, mapping vertices in `G.applyBatch U` back
to vertices in `G`. -/
def batchAnc (U : List Update) (z : ℕ) : ℕ :=
  U.foldr stepAnc z

@[simp] theorem batchAnc_nil (z : ℕ) : batchAnc [] z = z := rfl

@[simp] theorem batchAnc_cons (u : Update) (U : List Update) (z : ℕ) :
    batchAnc (u :: U) z = stepAnc u (batchAnc U z) := rfl

theorem batchAnc_append (U₁ U₂ : List Update) (z : ℕ) :
    batchAnc (U₁ ++ U₂) z = batchAnc U₁ (batchAnc U₂ z) := by
  simp [batchAnc, List.foldr_append]

theorem updateEnc_pos (G : MGraph) (u : Update) : 1 ≤ G.updateEnc u := by
  cases u <;> simp [MGraph.updateEnc]

theorem length_le_batchEnc : ∀ (G : MGraph) (U : List Update), U.length ≤ G.batchEnc U
  | _, [] => by simp [MGraph.batchEnc]
  | G, u :: U => by
    simp only [List.length_cons, MGraph.batchEnc]
    have h1 := updateEnc_pos G u
    have h2 := length_le_batchEnc (G.applyUpdate u) U
    omega

theorem isValid_applyUpdate_of_delOrSplit {G : MGraph} (hV : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) (hds : isDelOrSplit u) : (G.applyUpdate u).IsValid := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e =>
    intro e' he'
    simp only [MGraph.applyUpdate] at he' ⊢
    exact hV e' (Finset.mem_of_mem_erase he')
  | split v v' _ _ =>
    intro e' he'
    simp only [MGraph.applyUpdate, Finset.mem_insert] at he' ⊢
    rcases hV e' he' with ⟨ht, hh⟩
    constructor
    · split_ifs <;> [left; right] <;> simp_all
    · split_ifs <;> [left; right] <;> simp_all

theorem E_applyUpdate_subset {G : MGraph} {u : Update} (hds : isDelOrSplit u) :
    (G.applyUpdate u).E ⊆ G.E := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e => exact Finset.erase_subset _ _
  | split v v' _ _ => exact Finset.Subset.rfl

theorem V_subset_applyUpdate {G : MGraph} {u : Update} (hds : isDelOrSplit u) :
    G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete _ => exact Finset.Subset.rfl
  | split _ v' _ _ => exact Finset.subset_insert v' G.V

theorem n_applyUpdate_of_delOrSplit {G : MGraph} {u : Update}
    (hu : G.UpdateIsValid u) (hds : isDelOrSplit u) :
    (G.applyUpdate u).n = G.n + if isSplit u then 1 else 0 := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e => simp [MGraph.applyUpdate, MGraph.n, isSplit]
  | split v v' _ _ =>
    simp only [MGraph.applyUpdate, MGraph.n, isSplit, ↓reduceIte]
    exact Finset.card_insert_of_notMem hu.2.1

theorem split_deg_add {G : MGraph} (hV : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    let G' := G.applyUpdate (.split v v' St Sh)
    G'.deg v + G'.deg v' = G.deg v ∧ ∀ w ∈ G.V, w ≠ v → G'.deg w = G.deg w := by
  intro G'
  have hne : v ≠ v' := fun h => hu.2.1 (h ▸ hu.1)
  have htail :
      (G'.E.filter fun e => G'.tail e = v).card + (G'.E.filter fun e => G'.tail e = v').card =
        (G.E.filter fun e => G.tail e = v).card := by
    have hsplit : (G.E.filter fun e => G.tail e = v) =
        (G'.E.filter fun e => G'.tail e = v) ∪ (G'.E.filter fun e => G'.tail e = v') := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_union, G', MGraph.applyUpdate]
      constructor
      · rintro ⟨heE, hte⟩
        by_cases heS : e ∈ St
        · right; exact ⟨heE, by simp [heS, hte]⟩
        · left; exact ⟨heE, by simp [heS, hte]⟩
      · rintro (⟨heE, hte⟩ | ⟨heE, hte⟩)
        · refine ⟨heE, ?_⟩
          by_cases hcond : e ∈ St ∧ G.tail e = v
          · simp [hcond] at hte; exact absurd hte.symm hne
          · simpa [hcond] using hte
        · refine ⟨heE, ?_⟩
          by_cases hcond : e ∈ St ∧ G.tail e = v
          · exact hcond.2
          · simp [hcond] at hte
            exact absurd hte (fun h => hu.2.1 (h ▸ (hV e heE).1))
    have hdisj : Disjoint (G'.E.filter fun e => G'.tail e = v)
        (G'.E.filter fun e => G'.tail e = v') := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have hhead :
      (G'.E.filter fun e => G'.head e = v).card + (G'.E.filter fun e => G'.head e = v').card =
        (G.E.filter fun e => G.head e = v).card := by
    have hsplit : (G.E.filter fun e => G.head e = v) =
        (G'.E.filter fun e => G'.head e = v) ∪ (G'.E.filter fun e => G'.head e = v') := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_union, G', MGraph.applyUpdate]
      constructor
      · rintro ⟨heE, hhe⟩
        by_cases heS : e ∈ Sh
        · right; exact ⟨heE, by simp [heS, hhe]⟩
        · left; exact ⟨heE, by simp [heS, hhe]⟩
      · rintro (⟨heE, hhe⟩ | ⟨heE, hhe⟩)
        · refine ⟨heE, ?_⟩
          by_cases hcond : e ∈ Sh ∧ G.head e = v
          · simp [hcond] at hhe; exact absurd hhe.symm hne
          · simpa [hcond] using hhe
        · refine ⟨heE, ?_⟩
          by_cases hcond : e ∈ Sh ∧ G.head e = v
          · exact hcond.2
          · simp [hcond] at hhe
            exact absurd hhe (fun h => hu.2.1 (h ▸ (hV e heE).2))
    have hdisj : Disjoint (G'.E.filter fun e => G'.head e = v)
        (G'.E.filter fun e => G'.head e = v') := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  refine ⟨?_, fun w hw hne_w => ?_⟩
  · unfold MGraph.deg
    omega
  · have hw' : w ≠ v' := fun h => hu.2.1 (h ▸ hw)
    have hft : (G'.E.filter fun e => G'.tail e = w) = (G.E.filter fun e => G.tail e = w) := by
      ext e
      simp only [Finset.mem_filter, G', MGraph.applyUpdate]
      refine and_congr_right fun _ => ?_
      split_ifs with h
      · exact ⟨fun h1 => absurd h1.symm hw', fun h1 => absurd (h1.symm.trans h.2) hne_w⟩
      · rfl
    have hfh : (G'.E.filter fun e => G'.head e = w) = (G.E.filter fun e => G.head e = w) := by
      ext e
      simp only [Finset.mem_filter, G', MGraph.applyUpdate]
      refine and_congr_right fun _ => ?_
      split_ifs with h
      · exact ⟨fun h1 => absurd h1.symm hw', fun h1 => absurd (h1.symm.trans h.2) hne_w⟩
      · rfl
    unfold MGraph.deg
    rw [hft, hfh]

theorem maxDeg_applyUpdate_le {G : MGraph} (hV : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) (hds : isDelOrSplit u) : (G.applyUpdate u).maxDeg ≤ G.maxDeg := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e =>
    unfold MGraph.maxDeg
    rw [Finset.sup_le_iff]
    intro w hw
    have hdeg : (G.applyUpdate (.delete e)).deg w ≤ G.deg w := by
      unfold MGraph.deg MGraph.applyUpdate
      exact add_le_add
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))
    exact le_trans hdeg (Finset.le_sup (f := G.deg) hw)
  | split v v' St Sh =>
    obtain ⟨hsum, hother⟩ := split_deg_add hV hu
    unfold MGraph.maxDeg
    rw [Finset.sup_le_iff]
    intro w hw
    simp only [MGraph.applyUpdate, Finset.mem_insert] at hw
    rcases hw with hweq | hw
    · rw [hweq]
      have hle : (G.applyUpdate (.split v v' St Sh)).deg v' ≤ G.deg v := by omega
      exact le_trans hle (Finset.le_sup (f := G.deg) hu.1)
    · by_cases hwv : w = v
      · subst hwv
        have hle : (G.applyUpdate (.split w v' St Sh)).deg w ≤ G.deg w := by omega
        exact le_trans hle (Finset.le_sup (f := G.deg) hu.1)
      · rw [hother w hw hwv]
        exact Finset.le_sup (f := G.deg) hw

theorem isSubgraph_restrictUpdate {G H : MGraph} (hSub : G.IsSubgraph H) (hVH_eq : H.V = G.V)
    {u : Update} (hu : G.UpdateIsValid u) (hds : isDelOrSplit u) :
    let G' := G.applyUpdate u
    let H' := H.applyBatch (restrictUpdate u H)
    H.BatchIsValid (restrictUpdate u H) ∧
    G'.IsSubgraph H' ∧
    H'.V = G'.V ∧
    H'.E = H.E ∩ G'.E ∧
    (∀ e ∈ H.E, H'.tail e = G'.tail e ∧ H'.head e = G'.head e) ∧
    (restrictUpdate u H).length ≤ 1 := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e =>
    simp only [restrictUpdate, MGraph.applyUpdate]
    by_cases heH : e ∈ H.E
    · simp only [heH, ↓reduceIte, MGraph.BatchIsValid, MGraph.UpdateIsValid, MGraph.applyBatch,
        List.foldl_cons, List.foldl_nil, MGraph.applyUpdate, List.length_singleton, le_refl,
        and_true, true_and]
      refine ⟨⟨hVH_eq.le, Finset.erase_subset_erase e hSub.2.1, fun e' he' =>
        hSub.2.2 e' (Finset.mem_of_mem_erase he')⟩, hVH_eq, ?_, fun e' he' => hSub.2.2 e' he'⟩
      ext e'
      simp only [Finset.mem_inter, Finset.mem_erase]
      exact ⟨fun ⟨hne, he'⟩ => ⟨he', hne, hSub.2.1 he'⟩, fun ⟨he', hne, _⟩ => ⟨hne, he'⟩⟩
    · simp only [heH, ↓reduceIte, MGraph.BatchIsValid, MGraph.applyBatch, List.foldl_nil,
        List.length_nil, Nat.zero_le, and_true, true_and]
      refine ⟨⟨hVH_eq.le, Finset.subset_erase.mpr ⟨hSub.2.1, heH⟩, fun e' he' => hSub.2.2 e' he'⟩,
        hVH_eq, ?_, fun e' he' => hSub.2.2 e' he'⟩
      ext e'
      simp only [Finset.mem_inter, Finset.mem_erase]
      exact ⟨fun he' => ⟨he', fun h => heH (h ▸ he'), hSub.2.1 he'⟩, fun ⟨he', _⟩ => he'⟩
  | split v v' St Sh =>
    have hvH : v ∈ H.V := hVH_eq ▸ hu.1
    have hv'H : v' ∉ H.V := fun h => hu.2.1 (hVH_eq ▸ h)
    have hValSplit : H.UpdateIsValid (.split v v' (St ∩ H.E) (Sh ∩ H.E)) := by
      refine ⟨hvH, hv'H, Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right,
        fun e he => ?_⟩
      rcases Finset.mem_union.mp he with heT | heH_s
      · obtain ⟨heSt, heH⟩ := Finset.mem_inter.mp heT
        obtain ⟨ht, hh⟩ := hSub.2.2 e heH
        rw [ht, hh]
        exact hu.2.2.2 e (Finset.mem_union_left _ heSt)
      · obtain ⟨heSh, heH⟩ := Finset.mem_inter.mp heH_s
        obtain ⟨ht, hh⟩ := hSub.2.2 e heH
        rw [ht, hh]
        exact hu.2.2.2 e (Finset.mem_union_right _ heSh)
    have hVeq : insert v' H.V = insert v' G.V := by rw [hVH_eq]
    have hEnds : ∀ e ∈ H.E,
        (H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))).tail e =
          (G.applyUpdate (.split v v' St Sh)).tail e ∧
        (H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))).head e =
          (G.applyUpdate (.split v v' St Sh)).head e := by
      intro e he
      obtain ⟨ht, hh⟩ := hSub.2.2 e he
      simp [MGraph.applyUpdate, ht, hh, he]
    simp only [restrictUpdate, MGraph.BatchIsValid, MGraph.applyBatch, List.foldl_cons,
      List.foldl_nil, List.length_singleton, le_refl, and_true]
    refine ⟨hValSplit, ⟨hVeq.le, hSub.2.1, fun e he => hEnds e he⟩, hVeq, ?_, hEnds⟩
    ext e
    simp only [MGraph.applyUpdate, Finset.mem_inter, iff_self_and]
    exact fun he => hSub.2.1 he

theorem restrictUpdate_preserves_endpoints_outside {G H : MGraph}
    {u : Update} (hu : G.UpdateIsValid u) (hds : isDelOrSplit u)
    {e : ℕ} (heG : e ∉ G.E) (heH : e ∉ H.E) :
    let G' := G.applyUpdate u
    let H' := H.applyBatch (restrictUpdate u H)
    (H'.tail e = H.tail e ∧ H'.head e = H.head e) ∧
    (G'.tail e = G.tail e ∧ G'.head e = G.head e) := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete d =>
    by_cases hdH : d ∈ H.E <;> simp [restrictUpdate, hdH, MGraph.applyUpdate, MGraph.applyBatch]
  | split v v' St Sh =>
    have heSt : e ∉ St := fun h => heG (hu.2.2.1 (Finset.mem_union_left _ h))
    have heSh : e ∉ Sh := fun h => heG (hu.2.2.1 (Finset.mem_union_right _ h))
    simp [restrictUpdate, MGraph.applyUpdate, MGraph.applyBatch, heSt, heSh, heH]

theorem stepAnc_mem {G : MGraph} (_hV : G.IsValid) {u : Update} (hu : G.UpdateIsValid u)
    (hds : isDelOrSplit u) : ∀ z ∈ (G.applyUpdate u).V, stepAnc u z ∈ G.V := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete _ => intro z hz; exact hz
  | split v v' _ _ =>
    intro z hz
    simp only [MGraph.applyUpdate, Finset.mem_insert] at hz
    simp only [stepAnc]
    split_ifs with h
    · exact hu.1
    · exact hz.resolve_left h

theorem stepAnc_eq_of_mem {G : MGraph} {u : Update} (hu : G.UpdateIsValid u)
    (hds : isDelOrSplit u) : ∀ z ∈ G.V, stepAnc u z = z := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete _ => intro _ _; rfl
  | split v v' _ _ =>
    intro z hz
    simp only [stepAnc]
    split_ifs with h
    · exact absurd (h ▸ hz) hu.2.1
    · rfl

theorem stepAnc_tail_head {G : MGraph} (hV : G.IsValid) {u : Update} (hu : G.UpdateIsValid u)
    (hds : isDelOrSplit u) : ∀ e ∈ G.E,
    stepAnc u ((G.applyUpdate u).tail e) = G.tail e ∧
    stepAnc u ((G.applyUpdate u).head e) = G.head e := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete _ => intro _ _; simp [stepAnc, MGraph.applyUpdate]
  | split v v' _ _ =>
    intro e he
    have ht : G.tail e ≠ v' := fun h => hu.2.1 (h ▸ (hV e he).1)
    have hh : G.head e ≠ v' := fun h => hu.2.1 (h ▸ (hV e he).2)
    simp only [MGraph.applyUpdate, stepAnc]
    constructor <;> split_ifs <;> simp_all

theorem isValid_applyUpdate_any {H : MGraph} (hV : H.IsValid) {u : Update}
    (hu : H.UpdateIsValid u) : (H.applyUpdate u).IsValid := by
  cases u with
  | insert e a b =>
    intro e' he'
    simp only [MGraph.applyUpdate, Finset.mem_insert] at he' ⊢
    rcases he' with rfl | he'
    · rw [Function.update_self, Function.update_self]
      exact ⟨hu.2.1, hu.2.2⟩
    · have hne : e' ≠ e := fun h => hu.1 (h ▸ he')
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact hV e' he'
  | delete _ => exact isValid_applyUpdate_of_delOrSplit hV hu trivial
  | split _ _ _ _ => exact isValid_applyUpdate_of_delOrSplit hV hu trivial

end

end DynamicUpdates

end MinCostFlow.DynSpanner
