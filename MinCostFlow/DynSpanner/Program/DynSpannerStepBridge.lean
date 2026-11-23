module

public import MinCostFlow.DynSpanner.Defs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepHelpers

/-!
# From the host `G'` to the graph `H_{<j}` of the model

The procedures that build `J` and the new walks read the ends of edges in the graph `G'` stored
in memory, so their contracts are stated with `G'` in the place of `H_{<j}`
(`buildProjGraph G G …`, `projWalk G G …`, `reembedWalk G G …`). The model uses
`H_{<j} = unionGraphLt G' H_mid j`, whose ends are those of `G'`. The functions involved read
`H` only through its ends (`prefixWalk` follows `H.dst`, and `prefixWalk_congr_ends` in
`DynSpannerStepHelpers.lean` shows that only the ends matter), so the two versions agree. This
file proves it.
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

@[expose] public section

lemma proj_congr_ends (G : MGraph) {H₁ H₂ : MGraph} (ht : H₁.tail = H₂.tail)
    (hh : H₁.head = H₂.head) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) :
    proj G H₁ embLt S e = proj G H₂ embLt S e := by
  simp only [proj, prefixWalk_congr_ends ht hh]

lemma projWalk_congr_ends (G : MGraph) {H₁ H₂ : MGraph} (ht : H₁.tail = H₂.tail)
    (hh : H₁.head = H₂.head) (embLt : Embedding) (S : Finset ℕ) :
    projWalk G H₁ embLt S = projWalk G H₂ embLt S := by
  funext e
  simp only [projWalk, prefixWalk_congr_ends ht hh]

lemma reembedWalk_congr_ends (G : MGraph) {H₁ H₂ : MGraph} (ht : H₁.tail = H₂.tail)
    (hh : H₁.head = H₂.head) (embLt embMid : Embedding) (S : Finset ℕ) :
    reembedWalk G H₁ embLt embMid S = reembedWalk G H₂ embLt embMid S := by
  funext e
  simp only [reembedWalk, prefixWalk_congr_ends ht hh]

lemma buildProjGraph_congr_ends (G : MGraph) {H₁ H₂ : MGraph} (ht : H₁.tail = H₂.tail)
    (hh : H₁.head = H₂.head) (embLt : Embedding) (S E : Finset ℕ) :
    buildProjGraph G H₁ embLt S E = buildProjGraph G H₂ embLt S E := by
  simp only [buildProjGraph, proj_congr_ends G ht hh]

/-- `H_{<j}` has the ends of `G'`, so the model's objects of step `j > 0` are the ones computed
with `G'` in the place of `H_{<j}`. -/
lemma unionGraphLt_bridge {L : ℕ} (G : MGraph) (H : Fin (L + 1) → MGraph) (j : ℕ)
    (embLt embMid : Embedding) (S E : Finset ℕ) :
    buildProjGraph G (unionGraphLt G H j) embLt S E = buildProjGraph G G embLt S E ∧
    projWalk G (unionGraphLt G H j) embLt S = projWalk G G embLt S ∧
    reembedWalk G (unionGraphLt G H j) embLt embMid S = reembedWalk G G embLt embMid S :=
  ⟨buildProjGraph_congr_ends G (H₁ := unionGraphLt G H j) (H₂ := G) rfl rfl embLt S E,
    projWalk_congr_ends G (H₁ := unionGraphLt G H j) (H₂ := G) rfl rfl embLt S,
    reembedWalk_congr_ends G (H₁ := unionGraphLt G H j) (H₂ := G) rfl rfl embLt embMid S⟩

end

end MinCostFlow.DynSpanner.Program
