module

public import MinCostFlow.DynSpanner.Program.CanonicalSparsify
public import MinCostFlow.Chain.WalkFlow

/-!
# Shortcutting the output walks in `J` instead of `J̃`

`step` shortcuts each output walk in `J̃`, from the tail of the edge in `J`:
`shortcutWalk J̃ (J.tail e) (out.emb e)`. The program `dsShortcutEmbStmt` reads the start vertex
from the graph that it walks in, and asks that the edge be an edge of this graph. An edge of `J`
need not be an edge of `J̃`. The way out: the canonical sparsifier returns a `J̃` with the same
ends as `J` (`canonicalSparsify_ends`, since `outJtilde J kept` keeps `J.tail` and `J.head`), and
`shortcutWalk` uses the graph only through the ends (`shortcutWalk_congr_ends`). So the program
can shortcut in `J` itself, where every edge of `J` is an edge, and the output walks are walks in
`J` because `J̃` is a subgraph of `J`
(`isWalk_of_isSubgraph`, used in `canonicalSparsify_walk_in_J`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-- The canonical sparsifier keeps the ends of `J`. -/
theorem canonicalSparsify_ends (impl : SparsifyImpl) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) :
    (canonicalSparsify impl H' J emb).Jtilde.tail = J.tail ∧
      (canonicalSparsify impl H' J emb).Jtilde.head = J.head := by
  unfold canonicalSparsify
  split_ifs with hV
  · obtain ⟨body₀, o₀, st₀', cost₀, cJ₀, kept₀, emb₀, hp₀, hr₀, _, _, _, _, hOut₀, _⟩ :=
      canonicalGuestRun_exists impl J.m hV.2.1 hV.2.2.1 (le_refl _) hV.2.2.2.1 hV.2.2.2.2
    rw [Classical.choose_spec (canonicalGuestOut_exists impl hV) hp₀ hr₀ hOut₀]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- `suffixFrom` uses the graph only through the ends of the edges. -/
theorem suffixFrom_congr_ends {G H : MGraph} (ht : G.tail = H.tail) (hh : G.head = H.head)
    (target cur : ℕ) (Q : List (ℕ × Bool)) :
    suffixFrom G target cur Q = suffixFrom H target cur Q := by
  have hd : ∀ x, G.dst x = H.dst x := fun x => by simp [MGraph.dst, ht, hh]
  induction Q generalizing cur with
  | nil => rfl
  | cons x xs ih => simp only [suffixFrom, hd, ih]

/-- `shortcutWalk` uses the graph only through the ends of the edges. -/
theorem shortcutWalk_congr_ends {G H : MGraph} (ht : G.tail = H.tail) (hh : G.head = H.head)
    (u : ℕ) (P : List (ℕ × Bool)) : shortcutWalk G u P = shortcutWalk H u P := by
  have hd : ∀ x, G.dst x = H.dst x := fun x => by simp [MGraph.dst, ht, hh]
  have hv : ∀ v Q, G.walkVertices v Q = H.walkVertices v Q := fun v Q => by
    simp [MGraph.walkVertices, hd]
  induction P generalizing u with
  | nil => rfl
  | cons x xs ih =>
    simp only [shortcutWalk, shortcutStep, ih, hd, hv, suffixFrom_congr_ends ht hh]

/-- The output walks of the canonical sparsifier are walks in `J`: they are walks in `J̃`
(`out.emb` embeds `J` into `J̃`), and `J̃` is a subgraph of `J`. -/
theorem canonicalSparsify_walk_in_J (impl : SparsifyImpl) (mMax : ℕ) {H' J : MGraph}
    {emb : MinCostFlow.Embedding} (hH' : H'.IsValid) (hJ : J.IsValid) (hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ emb.length J) (hemb : emb.IsEmbedding J H') :
    ∀ e ∈ J.E, J.IsWalk (J.tail e) (J.head e) ((canonicalSparsify impl H' J emb).emb e) := by
  obtain ⟨hsub, hout, _⟩ :=
    canonicalSparsify_spec_with_time impl mMax H' J emb hH' hJ hJm hLen hemb
  intro e he
  exact MGraph.isWalk_of_isSubgraph hsub (hout.2 e he)

end

end MinCostFlow.DynSpanner.Program
