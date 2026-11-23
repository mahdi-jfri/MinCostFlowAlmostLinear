module

public import MinCostFlow.DynSpanner.Program.DynSpannerProjDefs
public import MinCostFlow.DynSpanner.Program.EmbLayouts

/-!
# Helper lemmas for the per-edge walk procedures

Facts used by the proofs of `dsProjEdgeStmt` and `dsReembedEdgeStmt`: disjointness of address
intervals (`IvlDisj`), that a stored walk survives a write elsewhere (`MWalkAt.of_frame`), and that
the walk returned by `prefixWalk` is a prefix of its input, so it is not longer and has no other
edges.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-! ## Interval helpers -/

lemma IvlDisj.or_sub {x lx y ly x' lx' : ℕ} (h : IvlDisj x lx y ly)
    (h1 : x ≤ x') (h2 : x' + lx' ≤ x + lx) : y + ly ≤ x' ∨ x' + lx' ≤ y := by
  unfold IvlDisj at h; omega

lemma IvlDisj.pts_sub {x lx y ly x' lx' : ℕ} (h : IvlDisj x lx y ly)
    (h1 : x ≤ x') (h2 : x' + lx' ≤ x + lx) : ∀ i < ly, y + i < x' ∨ x' + lx' ≤ y + i := by
  unfold IvlDisj at h; intro i hi; omega

lemma IvlDisj.addr_sub {x lx y ly x' lx' : ℕ} (h : IvlDisj x lx y ly)
    (h1 : x ≤ x') (h2 : x' + lx' ≤ x + lx) :
    ∀ addr, y ≤ addr → addr < y + ly → addr < x' ∨ x' + lx' ≤ addr := by
  unfold IvlDisj at h; intro addr ha hb; omega

lemma IvlDisj.sub_left {x lx y ly x' lx' : ℕ} (h : IvlDisj x lx y ly)
    (h1 : x ≤ x') (h2 : x' + lx' ≤ x + lx) : IvlDisj x' lx' y ly := by
  unfold IvlDisj at *; omega

lemma IvlDisj.symm {x lx y ly : ℕ} (h : IvlDisj x lx y ly) : IvlDisj y ly x lx := by
  unfold IvlDisj at *; omega

/-- A walk stored outside the block `[d, d + ld)` survives a write to that block. -/
lemma MWalkAt.of_frame {mem mem' : ℕ → ℕ} {x d ld : ℕ} {Q : List (ℕ × Bool)}
    (hQ : MWalkAt mem x Q)
    (hfr : ∀ addr, addr < d ∨ d + ld ≤ addr → mem' addr = mem addr)
    (hd : x + (2 * Q.length + 1) ≤ d ∨ d + ld ≤ x) : MWalkAt mem' x Q :=
  hQ.of_agree fun addr h1 h2 => hfr addr (by omega)

lemma prefixWalk_snd_length_le (H : MGraph) (S : Finset ℕ) :
    ∀ (a : ℕ) (W : List (ℕ × Bool)), (prefixWalk H a W S).2.length ≤ W.length
  | a, [] => by unfold prefixWalk; split_ifs <;> simp
  | a, x :: W => by
    unfold prefixWalk
    split_ifs
    · simp
    · simpa using prefixWalk_snd_length_le H S (H.dst x) W

lemma prefixWalk_snd_mem (H : MGraph) (S : Finset ℕ) :
    ∀ (a : ℕ) (W : List (ℕ × Bool)) (y : ℕ × Bool), y ∈ (prefixWalk H a W S).2 → y ∈ W
  | a, [], y, hy => by unfold prefixWalk at hy; split_ifs at hy <;> simp at hy
  | a, x :: W, y, hy => by
    unfold prefixWalk at hy
    split_ifs at hy
    · simp at hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (prefixWalk_snd_mem H S (H.dst x) W y hy)

lemma walkRev_length (P : List (ℕ × Bool)) : (walkRev P).length = P.length := by
  simp [walkRev]

lemma mem_walkRev_fst {P : List (ℕ × Bool)} {y : ℕ × Bool} (hy : y ∈ walkRev P) :
    ∃ x ∈ P, x.1 = y.1 := by
  simp only [walkRev, List.mem_reverse, List.mem_map] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

end

end MinCostFlow.DynSpanner.Program
