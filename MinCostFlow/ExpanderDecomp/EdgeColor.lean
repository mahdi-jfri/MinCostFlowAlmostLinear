module

public import MinCostFlow.Statement.Cited.Graphs
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Linarith

/-!
# Greedy 17-edge-colouring of degree-9 multigraphs (Step C)

In Step C of `OneShot`, we take an explicit expander `H` of maximum
degree at most `9`, delete any self-loops, and greedily colour its edges with `17` colours so that
each colour class is a matching.

This file defines the loop-deletion helper `removeLoops`, the computable greedy edge-colouring
model `greedyColorEdges` (and its 17-colour specialization `edgeColor17`), and the colour classes
`colorClass`.

Main results:
* `removeLoops_isLoopless`, `removeLoops_isValid`, `removeLoops_deg_le`, `removeLoops_cutIn`,
  `removeLoops_isExpansionExpanderOn`: deleting loops preserves validity, degree bounds, cuts, and
  expansion while making the graph loopless.
* `greedyColorEdges_map_fst`: the coloured list keeps the exact input edges in order.
* `greedyColorEdges_color_lt`: when every vertex has degree at most `Δ` in a loopless edge list and
  `2 * Δ ≤ numColors + 1`, every edge receives a colour `< numColors`.
* `colorClass_nodup_flatMap` and `colorClass_pairwise_disjoint`: each colour class is a matching
  (no two edges share an endpoint, and no edge is a loop).
* `flatMap_colorClass_perm`: the concatenation of the colour classes is a permutation of the input
  edge list.
* `edgeColor17_spec`: bundled specialization for a valid graph of maximum degree at most `9` with
  `17` colours.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Delete all self-loops from a graph `G`. -/
def removeLoops (G : Graph) : Graph :=
  { n := G.n, edges := G.edges.filter fun e => decide (e.1 ≠ e.2) }

/-- Degree of vertex `v` in an edge list `es` (a loop at `v` counts twice). -/
def listDeg (es : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (es.filter fun e => e.1 = v).length + (es.filter fun e => e.2 = v).length

/-- Test whether two edges share at least one endpoint. -/
def sharesEndpoint (e₁ e₂ : ℕ × ℕ) : Bool :=
  decide (e₁.1 = e₂.1 ∨ e₁.1 = e₂.2 ∨ e₁.2 = e₂.1 ∨ e₁.2 = e₂.2)

/-- Test whether colour `c` is already used on an edge in `colored` that shares an endpoint
with `e`. -/
def colorUsedAt (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) (c : ℕ) : Bool :=
  colored.any fun ec => decide (ec.2 = c) && sharesEndpoint ec.1 e

/-- Pick the smallest colour in `{0, …, numColors - 1}` not used at either endpoint of `e` (or `0`
if all are used). -/
def pickColor (numColors : ℕ) (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) : ℕ :=
  ((List.range numColors).find? fun c => !colorUsedAt colored e c).getD 0

/-- Auxiliary tail-recursive greedy edge colouring. -/
def greedyColorAux (numColors : ℕ) :
    List (ℕ × ℕ) → List ((ℕ × ℕ) × ℕ) → List ((ℕ × ℕ) × ℕ)
  | [], acc => acc.reverse
  | e :: rest, acc =>
      let c := pickColor numColors acc e
      greedyColorAux numColors rest ((e, c) :: acc)

/-- Greedily colour an edge list `es` using colours in `{0, …, numColors - 1}`. -/
def greedyColorEdges (numColors : ℕ) (es : List (ℕ × ℕ)) : List ((ℕ × ℕ) × ℕ) :=
  greedyColorAux numColors es []

/-- Delete loops from `G` and greedily colour the remaining edges with `17` colours. -/
def edgeColor17 (G : Graph) : List ((ℕ × ℕ) × ℕ) :=
  greedyColorEdges 17 (removeLoops G).edges

/-- The list of edges assigned colour `c`. -/
def colorClass (colored : List ((ℕ × ℕ) × ℕ)) (c : ℕ) : List (ℕ × ℕ) :=
  (colored.filter fun ec => decide (ec.2 = c)).map Prod.fst

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Deleting loops -/

theorem removeLoops_n (G : Graph) : (removeLoops G).n = G.n := rfl

theorem removeLoops_verts (G : Graph) : (removeLoops G).verts = G.verts := rfl

theorem removeLoops_isLoopless (G : Graph) : (removeLoops G).IsLoopless := by
  intro e he
  unfold removeLoops at he
  simp only [List.mem_filter, decide_eq_true_eq] at he
  exact he.2

theorem removeLoops_isValid {G : Graph} (hv : G.IsValid) : (removeLoops G).IsValid := by
  intro e he
  unfold removeLoops at he
  exact hv e (List.mem_filter.mp he).1

theorem removeLoops_degIn_le (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (removeLoops G).degIn X v ≤ G.degIn X v := by
  unfold Graph.degIn Graph.inside removeLoops
  dsimp only
  rw [List.filter_filter, List.filter_filter, List.filter_filter, List.filter_filter,
    List.filter_filter, List.filter_filter]
  have h1 := length_filter_le_of_imp G.edges
    (p := fun e => decide (e.1 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X)) && decide (e.1 ≠ e.2))
    (q := fun e => decide (e.1 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X)))
    (fun e _ h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1)
  have h2 := length_filter_le_of_imp G.edges
    (p := fun e => decide (e.2 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X)) && decide (e.1 ≠ e.2))
    (q := fun e => decide (e.2 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X)))
    (fun e _ h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1)
  omega

theorem removeLoops_deg_le (G : Graph) (v : ℕ) : (removeLoops G).deg v ≤ G.deg v :=
  removeLoops_degIn_le G G.verts v

/-- Deleting loops does not change any cut, because a loop never has exactly one end in `S`. -/
theorem removeLoops_cutIn (G : Graph) (X S : Finset ℕ) :
    (removeLoops G).cutIn X S = G.cutIn X S := by
  unfold Graph.cutIn Graph.inside removeLoops
  dsimp only
  rw [List.filter_filter, List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro e _
  by_cases heq : e.1 = e.2
  · simp [heq]
  · simp [heq]

theorem removeLoops_cut (G : Graph) (S : Finset ℕ) : (removeLoops G).cut S = G.cut S :=
  removeLoops_cutIn G G.verts S

theorem removeLoops_isExpansionExpanderOn {G : Graph} {X : Finset ℕ} {α : ℝ}
    (h : G.IsExpansionExpanderOn X α) : (removeLoops G).IsExpansionExpanderOn X α := by
  intro S hSX hne hneX
  rw [removeLoops_cutIn]
  exact h S hSX hne hneX

/-- For a valid graph `G`, `G.deg v` agrees with `listDeg G.edges v`. -/
theorem deg_eq_listDeg {G : Graph} (hv : G.IsValid) (v : ℕ) :
    G.deg v = listDeg G.edges v := by
  unfold Graph.deg Graph.degIn listDeg
  rw [inside_verts_of_isValid hv]

/-! ### Degree counting in edge lists -/

private lemma listDeg_append (l₁ l₂ : List (ℕ × ℕ)) (v : ℕ) :
    listDeg (l₁ ++ l₂) v = listDeg l₁ v + listDeg l₂ v := by
  unfold listDeg
  simp only [List.filter_append, List.length_append]
  omega

private lemma listDeg_reverse (l : List (ℕ × ℕ)) (v : ℕ) :
    listDeg l.reverse v = listDeg l v := by
  unfold listDeg
  rw [List.filter_reverse, List.filter_reverse, List.length_reverse, List.length_reverse]

private lemma listDeg_cons (e : ℕ × ℕ) (rest : List (ℕ × ℕ)) (v : ℕ) :
    listDeg (e :: rest) v =
      (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0) + listDeg rest v := by
  unfold listDeg
  simp only [List.filter_cons]
  by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v <;> simp [h1, h2] <;> omega

/-- The number of already-coloured edges sharing an endpoint with `e` is at most the sum of the
degrees of `e.1` and `e.2` in the already-coloured edges. -/
private lemma length_filter_sharesEndpoint_le (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) :
    (colored.filter fun ec => sharesEndpoint ec.1 e).length ≤
      listDeg (colored.map Prod.fst) e.1 + listDeg (colored.map Prod.fst) e.2 := by
  induction colored with
  | nil => simp [listDeg]
  | cons ec rest ih =>
    rcases ec with ⟨f, c⟩
    rw [List.filter_cons, List.map_cons, listDeg_cons, listDeg_cons]
    by_cases hs : sharesEndpoint f e = true
    · simp only [hs, ↓reduceIte, List.length_cons]
      unfold sharesEndpoint at hs
      simp only [decide_eq_true_eq] at hs
      rcases hs with h | h | h | h
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte]; omega
    · have hsf : sharesEndpoint f e = false := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ↓reduceIte]
      omega

/-- If fewer than `numColors` edges in `colored` share an endpoint with `e`, then `pickColor`
returns a colour `< numColors` not used at either endpoint of `e`. -/
private lemma pickColor_spec {numColors : ℕ} {colored : List ((ℕ × ℕ) × ℕ)} {e : ℕ × ℕ}
    (hlt : (colored.filter fun ec => sharesEndpoint ec.1 e).length < numColors) :
    pickColor numColors colored e < numColors ∧
      colorUsedAt colored e (pickColor numColors colored e) = false := by
  set inc := colored.filter fun ec => sharesEndpoint ec.1 e
  set used := (inc.map Prod.snd).toFinset
  have hcard : used.card < (Finset.range numColors).card := by
    rw [Finset.card_range]
    have h1 : used.card ≤ inc.length := by
      simpa [used, List.length_map] using List.toFinset_card_le (inc.map Prod.snd)
    omega
  have hex : ∃ c ∈ Finset.range numColors, c ∉ used := by
    by_contra h
    push Not at h
    have hsub : Finset.range numColors ⊆ used := fun c hc => h c hc
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨c₀, hc₀_range, hc₀_not⟩ := hex
  have hc₀_unused : colorUsedAt colored e c₀ = false := by
    rw [Bool.eq_false_iff]
    intro hused
    unfold colorUsedAt at hused
    rw [List.any_eq_true] at hused
    obtain ⟨ec, hec, hcond⟩ := hused
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    apply hc₀_not
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨ec, List.mem_filter.mpr ⟨hec, hcond.2⟩, hcond.1⟩
  have hmem_range : c₀ ∈ List.range numColors := List.mem_range.mpr (Finset.mem_range.mp hc₀_range)
  have hfind : ∃ c, ((List.range numColors).find? fun k => !colorUsedAt colored e k) = some c := by
    cases hf : (List.range numColors).find? fun k => !colorUsedAt colored e k with
    | none =>
      have hnone := List.find?_eq_none.mp hf c₀ hmem_range
      simp [hc₀_unused] at hnone
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hfind
  have hpick : pickColor numColors colored e = c := by
    unfold pickColor
    rw [hc]
    rfl
  rw [hpick]
  have hmem := List.mem_of_find?_eq_some hc
  have hpred := List.find?_some hc
  simp only [Bool.not_eq_true'] at hpred
  exact ⟨List.mem_range.mp hmem, hpred⟩

/-! ### Correctness of greedy edge colouring -/

private lemma greedyColorAux_map_fst (numColors : ℕ) (rest : List (ℕ × ℕ))
    (acc : List ((ℕ × ℕ) × ℕ)) :
    (greedyColorAux numColors rest acc).map Prod.fst = acc.reverse.map Prod.fst ++ rest := by
  induction rest generalizing acc with
  | nil => simp [greedyColorAux]
  | cons e rest ih =>
    unfold greedyColorAux
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

/-- `greedyColorEdges` preserves the input edge list in its exact order. -/
theorem greedyColorEdges_map_fst (numColors : ℕ) (es : List (ℕ × ℕ)) :
    (greedyColorEdges numColors es).map Prod.fst = es := by
  unfold greedyColorEdges
  rw [greedyColorAux_map_fst]
  simp

private lemma sharesEndpoint_symm (e₁ e₂ : ℕ × ℕ) :
    sharesEndpoint e₁ e₂ = sharesEndpoint e₂ e₁ := by
  unfold sharesEndpoint
  by_cases h1 : e₁.1 = e₂.1 <;> by_cases h2 : e₁.1 = e₂.2 <;>
    by_cases h3 : e₁.2 = e₂.1 <;> by_cases h4 : e₁.2 = e₂.2 <;>
    simp_all [eq_comm]

private lemma greedyColorAux_spec {numColors Δ : ℕ} (hcol : 2 * Δ ≤ numColors + 1)
    (rest : List (ℕ × ℕ)) (acc : List ((ℕ × ℕ) × ℕ))
    (hdeg : ∀ v, listDeg (acc.reverse.map Prod.fst ++ rest) v ≤ Δ)
    (hacc_lt : ∀ ec ∈ acc, ec.2 < numColors)
    (hacc_pw : acc.Pairwise fun ec₁ ec₂ => ec₁.2 = ec₂.2 → sharesEndpoint ec₁.1 ec₂.1 = false) :
    (∀ ec ∈ greedyColorAux numColors rest acc, ec.2 < numColors) ∧
      (greedyColorAux numColors rest acc).Pairwise
        fun ec₁ ec₂ => ec₁.2 = ec₂.2 → sharesEndpoint ec₁.1 ec₂.1 = false := by
  induction rest generalizing acc with
  | nil =>
    unfold greedyColorAux
    refine ⟨fun ec hec => hacc_lt ec (List.mem_reverse.mp hec), ?_⟩
    rw [List.pairwise_reverse]
    exact hacc_pw.imp fun h heq => by
      rw [sharesEndpoint_symm]
      exact h heq.symm
  | cons e rest ih =>
    unfold greedyColorAux
    dsimp only
    -- Bound the degrees of `e.1` and `e.2` in `acc`.
    have hdeg1 : listDeg (acc.map Prod.fst) e.1 + 1 ≤ Δ := by
      have hd := hdeg e.1
      rw [listDeg_append, List.map_reverse, listDeg_reverse, listDeg_cons] at hd
      simp only [↓reduceIte] at hd
      omega
    have hdeg2 : listDeg (acc.map Prod.fst) e.2 + 1 ≤ Δ := by
      have hd := hdeg e.2
      rw [listDeg_append, List.map_reverse, listDeg_reverse, listDeg_cons] at hd
      simp only [↓reduceIte] at hd
      omega
    have hlt : (acc.filter fun ec => sharesEndpoint ec.1 e).length < numColors := by
      have hle := length_filter_sharesEndpoint_le acc e
      omega
    obtain ⟨hc_lt, hc_unused⟩ := pickColor_spec hlt
    set c := pickColor numColors acc e
    have hdeg' : ∀ v, listDeg (((e, c) :: acc).reverse.map Prod.fst ++ rest) v ≤ Δ := by
      intro v
      have heq : ((e, c) :: acc).reverse.map Prod.fst ++ rest =
          acc.reverse.map Prod.fst ++ (e :: rest) := by
        simp [List.reverse_cons, List.append_assoc]
      rw [heq]
      exact hdeg v
    have hacc_lt' : ∀ ec ∈ (e, c) :: acc, ec.2 < numColors := by
      intro ec hec
      rcases List.mem_cons.mp hec with rfl | hmem
      · exact hc_lt
      · exact hacc_lt ec hmem
    have hacc_pw' : ((e, c) :: acc).Pairwise
        fun ec₁ ec₂ => ec₁.2 = ec₂.2 → sharesEndpoint ec₁.1 ec₂.1 = false := by
      rw [List.pairwise_cons]
      refine ⟨?_, hacc_pw⟩
      intro ec hec hceq
      by_contra hne
      have hsh : sharesEndpoint ec.1 e = true := by
        rw [sharesEndpoint_symm]
        exact Bool.eq_true_of_not_eq_false hne
      have hany : colorUsedAt acc e c = true := by
        unfold colorUsedAt
        rw [List.any_eq_true]
        exact ⟨ec, hec, by simp [hceq.symm, hsh]⟩
      rw [hc_unused] at hany
      exact Bool.false_ne_true hany
    exact ih ((e, c) :: acc) hdeg' hacc_lt' hacc_pw'

/-- Every edge gets a colour `< numColors` when every vertex has degree at most `Δ` and
`2 * Δ ≤ numColors + 1`. -/
theorem greedyColorEdges_color_lt {numColors Δ : ℕ} {es : List (ℕ × ℕ)}
    (hcol : 2 * Δ ≤ numColors + 1) (hdeg : ∀ v, listDeg es v ≤ Δ) :
    ∀ ec ∈ greedyColorEdges numColors es, ec.2 < numColors := by
  unfold greedyColorEdges
  exact (greedyColorAux_spec hcol es [] (by simpa using hdeg) (by simp) List.Pairwise.nil).1

/-- No two distinct edge occurrences assigned the same colour share an endpoint. -/
theorem greedyColorEdges_proper {numColors Δ : ℕ} {es : List (ℕ × ℕ)}
    (hcol : 2 * Δ ≤ numColors + 1) (hdeg : ∀ v, listDeg es v ≤ Δ) :
    (greedyColorEdges numColors es).Pairwise
      fun ec₁ ec₂ => ec₁.2 = ec₂.2 → sharesEndpoint ec₁.1 ec₂.1 = false := by
  unfold greedyColorEdges
  exact (greedyColorAux_spec hcol es [] (by simpa using hdeg) (by simp) List.Pairwise.nil).2

/-! ### Colour classes are matchings and partition the edges -/

/-- No two edges in a colour class share an endpoint. -/
theorem colorClass_pairwise_disjoint {numColors Δ : ℕ} {es : List (ℕ × ℕ)}
    (hcol : 2 * Δ ≤ numColors + 1) (hdeg : ∀ v, listDeg es v ≤ Δ) (c : ℕ) :
    (colorClass (greedyColorEdges numColors es) c).Pairwise
      fun e₁ e₂ => e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2 := by
  unfold colorClass
  have hpw := greedyColorEdges_proper hcol hdeg
  have hfilt : ((greedyColorEdges numColors es).filter fun ec => decide (ec.2 = c)).Pairwise
      fun ec₁ ec₂ => ec₁.1.1 ≠ ec₂.1.1 ∧ ec₁.1.1 ≠ ec₂.1.2 ∧
        ec₁.1.2 ≠ ec₂.1.1 ∧ ec₁.1.2 ≠ ec₂.1.2 := by
    have hsub := hpw.filter (fun ec => decide (ec.2 = c))
    have hmem : ∀ ec ∈ (greedyColorEdges numColors es).filter (fun ec => decide (ec.2 = c)),
        ec.2 = c := by
      intro ec hec
      exact decide_eq_true_eq.mp (List.mem_filter.mp hec).2
    rw [List.pairwise_iff_getElem] at hsub ⊢
    intro i j hi hj hij
    have h1 := hmem _ (List.getElem_mem hi)
    have h2 := hmem _ (List.getElem_mem hj)
    have hsh := hsub i j hi hj hij (h1.trans h2.symm)
    unfold sharesEndpoint at hsh
    simp only [decide_eq_false_iff_not, not_or] at hsh
    exact hsh
  exact List.pairwise_map.mpr hfilt

/-- In a loopless edge list of maximum degree at most `Δ`, every colour class is a matching:
all endpoints of its edges are distinct. -/
theorem colorClass_nodup_flatMap {numColors Δ : ℕ} {es : List (ℕ × ℕ)}
    (hcol : 2 * Δ ≤ numColors + 1) (hloop : ∀ e ∈ es, e.1 ≠ e.2)
    (hdeg : ∀ v, listDeg es v ≤ Δ) (c : ℕ) :
    ((colorClass (greedyColorEdges numColors es) c).flatMap fun e => [e.1, e.2]).Nodup := by
  have hpw := colorClass_pairwise_disjoint hcol hdeg c
  have hloopless : ∀ e ∈ colorClass (greedyColorEdges numColors es) c, e.1 ≠ e.2 := by
    intro e he
    unfold colorClass at he
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
    have hin : ec.1 ∈ es := by
      rw [← greedyColorEdges_map_fst numColors es]
      exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
    exact hloop ec.1 hin
  generalize hL : colorClass (greedyColorEdges numColors es) c = L at hpw hloopless ⊢
  clear hL
  induction L with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    rw [List.pairwise_cons] at hpw
    have hab : a ≠ b := hloopless (a, b) List.mem_cons_self
    have hrest_loop : ∀ e ∈ rest, e.1 ≠ e.2 :=
      fun e he => hloopless e (List.mem_cons_of_mem _ he)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
    refine ⟨?_, ?_, ih hpw.2 hrest_loop⟩
    · intro ha
      rcases List.mem_cons.mp ha with rfl | hfm
      · exact hab rfl
      · obtain ⟨e, he, hmem⟩ := List.mem_flatMap.mp hfm
        have hdisj := hpw.1 e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact hdisj.1 rfl
        · exact hdisj.2.1 rfl
    · intro hb
      obtain ⟨e, he, hmem⟩ := List.mem_flatMap.mp hb
      have hdisj := hpw.1 e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hdisj.2.2.1 rfl
      · exact hdisj.2.2.2 rfl

private lemma filter_append_perm_or {α : Type*} (l : List α) (p q : α → Bool)
    (hdisj : ∀ x ∈ l, ¬ (p x = true ∧ q x = true)) :
    (l.filter p ++ l.filter q).Perm (l.filter fun x => p x || q x) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hdisj' : ∀ x ∈ rest, ¬ (p x = true ∧ q x = true) :=
      fun x hx => hdisj x (List.mem_cons_of_mem _ hx)
    have hih := ih hdisj'
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    cases hp : p a <;> cases hq : q a
    · simp [hih]
    · simp only [Bool.false_or, ↓reduceIte]
      exact (List.perm_middle).trans (List.Perm.cons a hih)
    · simp only [Bool.true_or, ↓reduceIte, List.cons_append]
      exact List.Perm.cons a hih
    · exfalso
      exact hdisj a List.mem_cons_self ⟨hp, hq⟩

/-- The concatenation of the colour classes `0, …, numColors - 1` is a permutation of the input
edge list `es`. -/
theorem flatMap_colorClass_perm {numColors Δ : ℕ} {es : List (ℕ × ℕ)}
    (hcol : 2 * Δ ≤ numColors + 1) (hdeg : ∀ v, listDeg es v ≤ Δ) :
    ((List.range numColors).flatMap (colorClass (greedyColorEdges numColors es))).Perm es := by
  set colored := greedyColorEdges numColors es
  have hlt : ∀ ec ∈ colored, ec.2 < numColors := greedyColorEdges_color_lt hcol hdeg
  have haux : ∀ k, ((List.range k).flatMap (colorClass colored)).Perm
      ((colored.filter fun ec => decide (ec.2 < k)).map Prod.fst) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have h1 := List.Perm.append_right (colorClass colored k) ih
      unfold colorClass at h1 ⊢
      rw [← List.map_append] at h1
      refine h1.trans ?_
      apply List.Perm.map
      have hdisj : ∀ ec ∈ colored, ¬ (decide (ec.2 < k) = true ∧ decide (ec.2 = k) = true) := by
        intro ec _ h
        simp only [decide_eq_true_eq] at h
        omega
      refine (filter_append_perm_or colored _ _ hdisj).trans ?_
      have heq : colored.filter (fun ec => decide (ec.2 < k) || decide (ec.2 = k)) =
          colored.filter (fun ec => decide (ec.2 < k + 1)) := by
        apply List.filter_congr
        intro ec _
        by_cases h : ec.2 < k
        · have h' : ec.2 < k + 1 := by omega
          simp [h, h']
        · by_cases h2 : ec.2 = k
          · subst h2; simp
          · have h' : ¬ (ec.2 < k + 1) := by omega
            simp [h, h2, h']
      rw [heq]
  have hall : colored.filter (fun ec => decide (ec.2 < numColors)) = colored := by
    apply List.filter_eq_self.mpr
    intro ec hec
    exact decide_eq_true_eq.mpr (hlt ec hec)
  have hperm := haux numColors
  rw [hall, greedyColorEdges_map_fst] at hperm
  exact hperm

/-! ### Specialization to degree-9 graphs with 17 colours -/

/-- **Step C edge colouring**: deleting loops from a valid multigraph `G` of maximum degree at
most `9` and running `edgeColor17 G` colours every non-loop edge with a colour `< 17` such that:
1. the coloured edges keep `(removeLoops G).edges` in order;
2. every colour class `c` is a matching (pairwise disjoint endpoints, no loops);
3. the concatenation of colour classes `0, …, 16` is a permutation of `(removeLoops G).edges`. -/
theorem edgeColor17_spec {G : Graph} (hvalid : G.IsValid) (hdeg : ∀ v < G.n, G.deg v ≤ 9) :
    (edgeColor17 G).map Prod.fst = (removeLoops G).edges ∧
    (∀ ec ∈ edgeColor17 G, ec.2 < 17) ∧
    (∀ c, ((colorClass (edgeColor17 G) c).flatMap fun e => [e.1, e.2]).Nodup) ∧
    (∀ c, (colorClass (edgeColor17 G) c).Pairwise
      fun e₁ e₂ => e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2) ∧
    ((List.range 17).flatMap (colorClass (edgeColor17 G))).Perm (removeLoops G).edges := by
  have hvalid' : (removeLoops G).IsValid := removeLoops_isValid hvalid
  have hloop' : (removeLoops G).IsLoopless := removeLoops_isLoopless G
  have hdeg_all : ∀ v, listDeg (removeLoops G).edges v ≤ 9 := by
    intro v
    rw [← deg_eq_listDeg hvalid']
    by_cases hv : v < G.n
    · exact le_trans (removeLoops_deg_le G v) (hdeg v hv)
    · have hv' : v ∉ (removeLoops G).verts := by
        simp [Graph.verts, removeLoops_n, hv]
      rw [Graph.deg, degIn_eq_zero_of_not_mem _ hv']
      exact Nat.zero_le 9
  have hcol : 2 * 9 ≤ 17 + 1 := by omega
  unfold edgeColor17
  exact ⟨greedyColorEdges_map_fst 17 _,
    greedyColorEdges_color_lt hcol hdeg_all,
    fun c => colorClass_nodup_flatMap hcol hloop' hdeg_all c,
    fun c => colorClass_pairwise_disjoint hcol hdeg_all c,
    flatMap_colorClass_perm hcol hdeg_all⟩

end MinCostFlow.ExpanderDecomp
