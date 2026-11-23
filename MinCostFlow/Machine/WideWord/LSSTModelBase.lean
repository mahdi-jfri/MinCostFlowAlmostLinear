module

public import MinCostFlow.LSF.Tools
public import MinCostFlow.LSF.Model
public import MinCostFlow.LSF.Theorem22Aux
public import MinCostFlow.Statement.Cited.AbrahamNeiman
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import WordRAM.Exec

/-!
# Base graph types and reusable LSST reduction lemmas

This file provides the shared indexed-graph model and reusable low-stretch spanning tree
reduction lemmas for the WordRAM implementation of Theorem 2.2 (page 7):

* `IndexedGraph` and `IndexedGraph.toMGraph`: indexed multigraphs on vertices `0, …, n - 1`
  and edges `0, …, m - 1`.
* `decodedTree`: tree formed from original edge indices `< m` and fresh bridging pairs `(u, v)`
  numbered `m, m + 1, …`.
* `isLSST_of_edgeMap`: invariance of `MinCostFlow.LSF.IsLSST` under bijective relabeling of
  non-`G` bridge edges.
* `lsst_of_projectTree_gen` and `an19_stretch_sum_bound_gen`: public versions of the stretch
  lifting lemmas from `MinCostFlow.LSF.Theorem22` parameterized by arbitrary deterministic lists
  `(V_list, E_list, B)` and scale/weights `(δ, w_int)`.
* `runsTo_unique`: uniqueness of `WordRAM.RunsTo` output and cost for fixed random bits.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open MinCostFlow
open MinCostFlow.LSF

/-! ### Indexed graphs and decoded output trees -/

/-- Indexed multigraph on vertices `0, …, n - 1` and edges `0, …, m - 1`. -/
structure IndexedGraph where
  /-- Number of vertices (`n ≥ 1` for valid graphs). -/
  n : ℕ
  /-- Number of edges. -/
  m : ℕ
  /-- Tail vertex `u < n` of edge `e < m`. -/
  tail : ℕ → ℕ
  /-- Head vertex `v < n` of edge `e < m`. -/
  head : ℕ → ℕ

namespace IndexedGraph

/-- Every edge `e < m` has endpoints strictly below `n`, and `n ≥ 1`. -/
def Valid (G : IndexedGraph) : Prop :=
  1 ≤ G.n ∧ ∀ e < G.m, G.tail e < G.n ∧ G.head e < G.n

/-- Convert an `IndexedGraph` to the named-vertex/edge representation `MGraph`. -/
def toMGraph (G : IndexedGraph) : MGraph :=
  { V := Finset.range G.n
    E := Finset.range G.m
    tail := G.tail
    head := G.head }

theorem toMGraph_isValid {G : IndexedGraph} (hG : G.Valid) : G.toMGraph.IsValid := by
  intro e he
  simp only [toMGraph, Finset.mem_range] at he ⊢
  exact hG.2 e he

theorem toMGraph_V_nonempty {G : IndexedGraph} (hG : G.Valid) : G.toMGraph.V.Nonempty :=
  ⟨0, Finset.mem_range.mpr hG.1⟩

theorem toMGraph_n (G : IndexedGraph) : G.toMGraph.n = G.n := by
  simp [toMGraph, MGraph.n]

theorem toMGraph_m (G : IndexedGraph) : G.toMGraph.m = G.m := by
  simp [toMGraph, MGraph.m]

end IndexedGraph

/-- Tree on `0, …, n - 1` formed from original edge indices `origEdges` (with endpoints given by
`tail, head`) and bridging pairs `bridgePairs` (assigned edge IDs `m, m + 1, …`). -/
def decodedTree (n m : ℕ) (tail head : ℕ → ℕ)
    (origEdges : List ℕ) (bridgePairs : List (ℕ × ℕ)) : MGraph :=
  { V := Finset.range n
    E := origEdges.toFinset ∪ (List.range bridgePairs.length).toFinset.image (fun k => m + k)
    tail := fun f => if f < m then tail f else (bridgePairs.getD (f - m) (0, 0)).1
    head := fun f => if f < m then head f else (bridgePairs.getD (f - m) (0, 0)).2 }

/-! ### Determinism of `RunsTo` on a fixed random tape -/

/-- For a fixed program `p`, word width `w`, input `input`, and bit tape `ω`, `RunsTo` has a
unique output list and cost. -/
theorem runsTo_unique {w : ℕ} {p : WordRAM.Program} {input : List ℕ} {ω : ℕ → Bool}
    {out₁ out₂ : List ℕ} {c₁ c₂ : ℕ}
    (h₁ : WordRAM.RunsTo w p input ω out₁ c₁)
    (h₂ : WordRAM.RunsTo w p input ω out₂ c₂) :
    out₁ = out₂ ∧ c₁ = c₂ := by
  rcases h₁ with ⟨f₁, hf₁⟩
  rcases h₂ with ⟨f₂, hf₂⟩
  dsimp only [WordRAM.run] at hf₁ hf₂
  cases hx₁ : WordRAM.exec w p ω f₁ (.call 0 0 [.const input.length])
      { mem := WordRAM.initMem input, regs := fun _ => 0, pos := 0 } with
  | none => simp [hx₁] at hf₁
  | some r₁ =>
    cases hx₂ : WordRAM.exec w p ω f₂ (.call 0 0 [.const input.length])
        { mem := WordRAM.initMem input, regs := fun _ => 0, pos := 0 } with
    | none => simp [hx₂] at hf₂
    | some r₂ =>
      have hm₁ := WordRAM.exec_fuel_mono hx₁ (Nat.le_max_left f₁ f₂)
      have hm₂ := WordRAM.exec_fuel_mono hx₂ (Nat.le_max_right f₁ f₂)
      have hr : r₁ = r₂ := Option.some.inj (hm₁.symm.trans hm₂)
      subst hr
      simp only [hx₁, hx₂, Option.some.injEq, Prod.mk.injEq] at hf₁ hf₂
      exact ⟨hf₁.1.symm.trans hf₂.1, hf₁.2.symm.trans hf₂.2⟩

/-! ### List index helpers -/

theorem idxOf_inj_of_mem {xs : List ℕ} {x y : ℕ} (hx : x ∈ xs) (hy : y ∈ xs)
    (hEq : xs.idxOf x = xs.idxOf y) : x = y := by
  have hxlt : xs.idxOf x < xs.length := List.idxOf_lt_length_of_mem hx
  have hylt : xs.idxOf y < xs.length := List.idxOf_lt_length_of_mem hy
  calc x = xs[xs.idxOf x]'hxlt := (List.getElem_idxOf hxlt).symm
    _ = xs[xs.idxOf y]'hylt := by simp [hEq]
    _ = y := List.getElem_idxOf hylt

theorem idxOf_getElem_of_nodup {xs : List ℕ} (hnd : xs.Nodup) {i : ℕ} (hi : i < xs.length) :
    xs.idxOf (xs[i]'hi) = i :=
  (List.Nodup.getElem_inj hnd).mp
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem hi)))

/-! ### Edge-bijection invariance of `IsLSST` -/

private lemma isWalk_map_of_edgeMap {T₁ T₂ : MGraph} {φ : ℕ → ℕ}
    (hmem : ∀ f ∈ T₁.E, φ f ∈ T₂.E)
    (hend : ∀ f ∈ T₁.E, T₂.tail (φ f) = T₁.tail f ∧ T₂.head (φ f) = T₁.head f) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, T₁.IsWalk u v P →
      T₂.IsWalk u v (P.map fun x => (φ x.1, x.2)) := by
  intro u v P hP
  induction hP with
  | nil s => exact .nil s
  | @cons s _ x xs hxE hsrc _ ih =>
    have hm := hend x.1 hxE
    have hsrc' : T₂.src (φ x.1, x.2) = s := by
      cases hx2 : x.2 <;> simp only [MGraph.src, hx2, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
      · rw [hm.2]; exact hsrc
      · rw [hm.1]; exact hsrc
    have hdst' : T₂.dst (φ x.1, x.2) = T₁.dst x := by
      cases hx2 : x.2 <;> simp only [MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte]
      · exact hm.1
      · exact hm.2
    exact .cons (hmem x.1 hxE) hsrc' (hdst'.symm ▸ ih)

private lemma isWalk_unmap_of_edgeMap {T₁ T₂ : MGraph} {φ : ℕ → ℕ}
    (hsurj : ∀ f' ∈ T₂.E, ∃ f ∈ T₁.E, φ f = f')
    (hend : ∀ f ∈ T₁.E, T₂.tail (φ f) = T₁.tail f ∧ T₂.head (φ f) = T₁.head f) :
    ∀ {u v : ℕ} {Q : List (ℕ × Bool)}, T₂.IsWalk u v Q →
      ∃ P : List (ℕ × Bool), T₁.IsWalk u v P ∧ Q = P.map fun x => (φ x.1, x.2) := by
  intro u v Q hQ
  induction hQ with
  | nil s => exact ⟨[], .nil s, rfl⟩
  | @cons s _ y ys hyE hsrc _ ih =>
    obtain ⟨f, hf₁, hy_eq⟩ := hsurj y.1 hyE
    have hm := hend f hf₁
    have hy1 : T₁.src (f, y.2) = T₂.src y := by
      cases hy2 : y.2 <;> simp only [MGraph.src, hy2, Bool.false_eq_true, ↓reduceIte]
      · rw [← hy_eq, hm.2]
      · rw [← hy_eq, hm.1]
    have hsrc' : T₁.src (f, y.2) = s := hy1.trans hsrc
    have hdst' : T₁.dst (f, y.2) = T₂.dst y := by
      cases hy2 : y.2 <;> simp only [MGraph.dst, hy2, Bool.false_eq_true, ↓reduceIte]
      · rw [← hy_eq, hm.1]
      · rw [← hy_eq, hm.2]
    obtain ⟨P, hWP, hQ_eq⟩ := ih
    refine ⟨(f, y.2) :: P, .cons hf₁ hsrc' (hdst'.symm ▸ hWP), ?_⟩
    rw [List.map_cons, ← hQ_eq]
    congr 1
    exact Prod.ext hy_eq.symm rfl

/-- `IsLSST` is preserved by relabeling edges via a bijection `φ : T₁.E → T₂.E` that fixes
`G.E`, keeps non-`G.E` edges outside `G.E`, and preserves `tail` and `head`. -/
theorem isLSST_of_edgeMap {G T₁ T₂ : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ} {φ : ℕ → ℕ}
    (hG : G.IsValid)
    (hV : T₂.V = T₁.V)
    (hmem : ∀ f ∈ T₁.E, φ f ∈ T₂.E)
    (hsurj : ∀ f' ∈ T₂.E, ∃ f ∈ T₁.E, φ f = f')
    (hfix : ∀ f ∈ T₁.E, f ∈ G.E → φ f = f)
    (hnotG : ∀ f ∈ T₁.E, f ∉ G.E → φ f ∉ G.E)
    (hend : ∀ f ∈ T₁.E, T₂.tail (φ f) = T₁.tail f ∧ T₂.head (φ f) = T₁.head f)
    (hlsst : IsLSST G ℓ v γ T₁) :
    IsLSST G ℓ v γ T₂ := by
  have hT₁_st := hlsst.1
  have hT₁_G := hlsst.2.1
  have hT₁_paths := hlsst.2.2.1
  have hT₁_sum := hlsst.2.2.2
  have hT₂_val : T₂.IsValid := by
    intro f' hf'
    obtain ⟨f, hf₁, rfl⟩ := hsurj f' hf'
    rw [hV, (hend f hf₁).1, (hend f hf₁).2]
    exact hT₁_st.1.1 f hf₁
  have hT₂_forest : T₂.IsForest := by
    refine ⟨hT₂_val, fun Q hQ => ?_⟩
    rcases hQ with ⟨hQne, hQnd, u, hWQ⟩
    obtain ⟨P, hWP, rfl⟩ := isWalk_unmap_of_edgeMap hsurj hend hWQ
    have hPne : P ≠ [] := fun h => hQne (by simp [h])
    have hPnd : (P.map Prod.fst).Nodup := by
      have hEq : (P.map fun x => (φ x.1, x.2)).map Prod.fst = (P.map Prod.fst).map φ := by
        simp [List.map_map, Function.comp_def]
      rw [hEq] at hQnd
      exact List.Nodup.of_map φ hQnd
    exact hT₁_st.1.2 P ⟨hPne, hPnd, u, hWP⟩
  have hT₂_conn : ∀ u ∈ G.V, ∀ w ∈ G.V, T₂.Connected u w := by
    intro u hu w hw
    have hu1 : u ∈ T₁.V := hT₁_st.2.1 ▸ hu
    have hw1 : w ∈ T₁.V := hT₁_st.2.1 ▸ hw
    obtain ⟨P, hWP⟩ := hT₁_st.2.2 u hu w hw
    exact ⟨P.map fun x => (φ x.1, x.2), isWalk_map_of_edgeMap hmem hend hWP⟩
  have hT₂_st : T₂.IsSpanningTreeOn G.V := ⟨hT₂_forest, hV.trans hT₁_st.2.1, hT₂_conn⟩
  have hT₂_G : ∀ e ∈ T₂.E, e ∈ G.E → T₂.tail e = G.tail e ∧ T₂.head e = G.head e := by
    intro e he heG
    obtain ⟨f, hf₁, hfeq⟩ := hsurj e he
    have hfG : f ∈ G.E := by
      by_contra hnf
      exact absurd (hfeq ▸ heG) (hnotG f hf₁ hnf)
    have hφf : φ f = f := hfix f hf₁ hfG
    have hf_eq : f = e := hφf.symm.trans hfeq
    subst hf_eq
    have h1 := hend f hf₁
    rw [hφf] at h1
    have h2 := hT₁_G f hf₁ hfG
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hpath_eq : ∀ e ∈ G.E,
      T₂.forestPath (G.tail e) (G.head e) = T₁.forestPath (G.tail e) (G.head e) := by
    intro e heG
    let P := T₁.forestPath (G.tail e) (G.head e)
    have hev := hG e heG
    have hP_path : T₁.IsPath (G.tail e) (G.head e) P :=
      forestPath_isPath hT₁_st.1 (hT₁_st.2.2 _ hev.1 _ hev.2)
    have hP_G : ∀ f ∈ walkEdges P, f ∈ G.E := hT₁_paths e heG
    have hP_map_eq : P.map (fun x => (φ x.1, x.2)) = P := by
      have hcongr : P.map (fun x => (φ x.1, x.2)) = P.map id := by
        refine List.map_congr_left fun x hx => ?_
        have hxE : x.1 ∈ T₁.E := IsWalk_edges_mem hP_path.1 hx
        have hxG : x.1 ∈ G.E := hP_G x.1 (mem_walkEdges_iff.mpr ⟨x.2, hx⟩)
        exact Prod.ext (hfix x.1 hxE hxG) rfl
      simpa using hcongr
    have hP_walk2 : T₂.IsWalk (G.tail e) (G.head e) P := by
      rw [← hP_map_eq]
      exact isWalk_map_of_edgeMap hmem hend hP_path.1
    have hwalkV : T₂.walkVertices (G.tail e) P = T₁.walkVertices (G.tail e) P := by
      dsimp only [MGraph.walkVertices]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      have hxE : x.1 ∈ T₁.E := IsWalk_edges_mem hP_path.1 hx
      have hxG : x.1 ∈ G.E := hP_G x.1 (mem_walkEdges_iff.mpr ⟨x.2, hx⟩)
      have hm := hend x.1 hxE
      have hφ := hfix x.1 hxE hxG
      cases hx2 : x.2 <;> simp only [MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte]
      · exact (congrArg T₂.tail hφ.symm).trans hm.1
      · exact (congrArg T₂.head hφ.symm).trans hm.2
    exact forestPath_eq_of_isPath hT₂_forest ⟨hP_walk2, by rw [hwalkV]; exact hP_path.2⟩
  refine ⟨hT₂_st, hT₂_G, fun e heG f hf => ?_, ?_⟩
  · rw [hpath_eq e heG] at hf
    exact hT₁_paths e heG f hf
  · have hsum_eq : ∑ e ∈ G.E, v e * treeStretch G T₂ ℓ e =
        ∑ e ∈ G.E, v e * treeStretch G T₁ ℓ e := by
      refine Finset.sum_congr rfl fun e heG => ?_
      simp only [treeStretch, hpath_eq e heG]
    rw [hsum_eq]
    exact hT₁_sum

/-! ### Reusable lifting lemmas from `MinCostFlow.LSF.Theorem22` -/

/-- Case 1 (no non-loop edges): star tree on `0, …, n - 1` built from empty `origEdges` and
`n - 1` bridging pairs `[(0, 1), …, (0, n - 1)]`. -/
theorem lsst_star_no_nonloop {G : IndexedGraph} (hG : G.Valid)
    {ℓ v : ℕ → ℝ} (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hloop : ∀ e ∈ G.toMGraph.E, G.toMGraph.tail e = G.toMGraph.head e)
    {K₁ : ℝ} (hK₁ : 1 ≤ K₁) :
    let pairs := (List.range (G.n - 1)).map (fun i => (0, i + 1))
    IsLSST G.toMGraph ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2)
      (decodedTree G.n G.m G.tail G.head [] pairs) := by
  classical
  let pairs := (List.range (G.n - 1)).map (fun i => (0, i + 1))
  let T := decodedTree G.n G.m G.tail G.head [] pairs
  have hT_V : T.V = G.toMGraph.V := rfl
  have hpairs_len : pairs.length = G.n - 1 := by simp [pairs]
  have hT_edge : ∀ k (hk : k < G.n - 1),
      G.m + k ∈ T.E ∧ T.tail (G.m + k) = 0 ∧ T.head (G.m + k) = k + 1 := by
    intro k hk
    have hk_p : k < pairs.length := by rw [hpairs_len]; exact hk
    have hmem : G.m + k ∈ T.E := by
      dsimp only [T, decodedTree]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (List.mem_toFinset.mpr (List.mem_range.mpr hk_p)))
    have hnot : ¬ G.m + k < G.m := by omega
    have ht : T.tail (G.m + k) = 0 := by
      dsimp only [T, decodedTree]
      rw [ite_eq_right hnot, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk_p]
      simp [pairs]
    have hh : T.head (G.m + k) = k + 1 := by
      dsimp only [T, decodedTree]
      rw [ite_eq_right hnot, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk_p]
      simp [pairs]
    exact ⟨hmem, ht, hh⟩
  have hT_val : T.IsValid := by
    intro f hf
    dsimp only [T, decodedTree] at hf
    rw [List.toFinset_nil, Finset.empty_union, Finset.mem_image] at hf
    obtain ⟨k, hk, rfl⟩ := hf
    have hk' : k < G.n - 1 := by simpa [pairs] using List.mem_range.mp (List.mem_toFinset.mp hk)
    obtain ⟨_, ht, hh⟩ := hT_edge k hk'
    rw [ht, hh]
    exact ⟨Finset.mem_range.mpr hG.1, Finset.mem_range.mpr (by omega)⟩
  have hT_conn : ∀ u ∈ G.toMGraph.V, ∀ w ∈ G.toMGraph.V, T.Connected u w := by
    have hfrom0 : ∀ u ∈ G.toMGraph.V, T.Connected 0 u := by
      intro u hu
      rw [IndexedGraph.toMGraph] at hu
      rw [Finset.mem_range] at hu
      cases u with
      | zero => exact connected_refl T 0
      | succ k =>
        obtain ⟨hm, ht, hh⟩ := hT_edge k (by omega)
        exact ⟨[(G.m + k, true)], .cons hm (by simp [MGraph.src, ht])
          (by simpa [MGraph.dst, hh] using .nil (k + 1))⟩
    intro u hu w hw
    exact connected_trans (connected_symm (hfrom0 u hu)) (hfrom0 w hw)
  have hT_card : T.E.card ≤ T.V.card - 1 := by
    dsimp only [T, decodedTree]
    rw [List.toFinset_nil, Finset.empty_union, hpairs_len, Finset.card_range]
    calc ((List.range (G.n - 1)).toFinset.image (fun k => G.m + k)).card
        ≤ (List.range (G.n - 1)).toFinset.card := Finset.card_image_le
      _ ≤ (List.range (G.n - 1)).length := List.toFinset_card_le _
      _ = G.n - 1 := List.length_range
  have hT_forest : T.IsForest :=
    isForest_of_connected_card_le hT_val (IndexedGraph.toMGraph_V_nonempty hG) hT_conn hT_card
  have hT_st : T.IsSpanningTreeOn G.toMGraph.V := ⟨hT_forest, hT_V, hT_conn⟩
  have hT_nG : ∀ f ∈ T.E, f ∉ G.toMGraph.E := by
    intro f hf hfG
    dsimp only [T, decodedTree] at hf
    rw [List.toFinset_nil, Finset.empty_union, Finset.mem_image] at hf
    obtain ⟨k, _, rfl⟩ := hf
    simp only [IndexedGraph.toMGraph, Finset.mem_range] at hfG
    omega
  have hn1 : 1 ≤ G.toMGraph.n := by simpa [IndexedGraph.toMGraph_n] using hG.1
  have hlog2 : 1 ≤ (Real.log ((G.n : ℝ) + 2)) ^ 2 := by
    simpa [IndexedGraph.toMGraph_n] using one_le_log_add_two_sq hn1
  refine ⟨hT_st, fun f hfT hfG => absurd hfG (hT_nG f hfT), fun e he f hf => ?_, ?_⟩
  · rw [hloop e he, forestPath_self hT_st.1] at hf
    simp [walkEdges] at hf
  · have hsum : ∑ e ∈ G.toMGraph.E, v e * treeStretch G.toMGraph T ℓ e = G.toMGraph.norm1 v := by
      rw [norm1_eq_sum_pos hv]
      refine Finset.sum_congr rfl fun e he => ?_
      simp [treeStretch, hloop e he, forestPath_self hT_st.1, walkLength, walkEdges]
    rw [hsum]
    have hnorm0 : 0 ≤ G.toMGraph.norm1 v := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hcoef : 1 ≤ (4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2 := by nlinarith
    calc G.toMGraph.norm1 v = 1 * G.toMGraph.norm1 v := (one_mul _).symm
      _ ≤ ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) * G.toMGraph.norm1 v :=
          mul_le_mul_of_nonneg_right hcoef hnorm0

/-- Re-exported projection bound from `MinCostFlow.LSF.Theorem22`: lifts `IsLSST` on the
weighted-copy multigraph `G_v` back onto the original graph `G`. -/
theorem lsst_of_projectTree_gen {G G_nl G_v T_raw : MGraph} {ℓ v : ℕ → ℝ} {K₁ : ℝ}
    (hG : G.IsValid) (hV : G.V.Nonempty) (hK₁ : 1 ≤ K₁)
    (hG_nl_eq : G_nl = { G with E := G.E.filter (fun e => G.tail e ≠ G.head e) })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hE_nl : G_nl.E.Nonempty)
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (hv : ∀ e ∈ G.E, 0 < v e)
    (hT_raw_nonGv : ∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G ≤ f)
    (hlsst_raw : IsLSST G_v (weightedCopyLen G_nl ℓ) (fun _ => 1)
      ((2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T_raw) :
    let T := projectTree G_nl v T_raw
    IsLSST G ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T := by
  classical
  subst hG_nl_eq hG_v_eq
  let G_nl : MGraph := { G with E := G.E.filter (fun e => G.tail e ≠ G.head e) }
  let G_v := weightedCopyGraph G_nl v
  have hG_nl_val : G_nl.IsValid := fun e he => hG e (Finset.mem_filter.mp he).1
  have hℓ_nl : ∀ e ∈ G_nl.E, 0 < ℓ e := fun e he => hℓ e (Finset.mem_filter.mp he).1
  have hv_nl : ∀ e ∈ G_nl.E, 0 < v e := fun e he => hv e (Finset.mem_filter.mp he).1
  have hG_v_card : (G_v.E.card : ℝ) ≤ 2 * (G_nl.E.card : ℝ) := weightedCopyGraph_card_le hv_nl
  have hn1 : 1 ≤ G.n := Finset.card_pos.mpr hV
  have hlog2 : 1 ≤ (Real.log ((G.n : ℝ) + 2)) ^ 2 := one_le_log_add_two_sq hn1
  have hproj := projectTree_isLSST hG_nl_val hℓ_nl hv_nl hlsst_raw
  let T := projectTree G_nl v T_raw
  have hT_st : T.IsSpanningTreeOn G.V := hproj.1
  have hT_edges : ∀ f' ∈ T.E, f' ∈ G.E → T.tail f' = G.tail f' ∧ T.head f' = G.head f' := by
    intro f' hf'T hf'G
    have hf'' := hf'T
    dsimp only [T] at hf''
    unfold projectTree at hf''
    rw [ite_eq_left hE_nl] at hf''
    obtain ⟨f, hf_raw, hfeq⟩ := Finset.mem_image.mp hf''
    have hf_gv : f ∈ G_v.E := by
      by_contra hnf
      have hproj_eq : projectEdge G_nl v f = f + copyMod G_nl := by
        unfold projectEdge; exact ite_eq_right hnf
      have hge : copyMod G ≤ f' :=
        (hT_raw_nonGv f hf_raw hnf).trans (by rw [← hfeq, hproj_eq]; exact Nat.le_add_right _ _)
      exact Nat.not_lt_of_ge hge (lt_copyMod hf'G)
    have hf'_nl : f' ∈ G_nl.E := by
      have hproj_eq : projectEdge G_nl v f = origEdge (copyMod G_nl) f := by
        unfold projectEdge; exact ite_eq_left hf_gv
      rw [← hfeq, hproj_eq]
      exact (weightedCopyGraph_origEdge_mem hE_nl hf_gv).1
    exact hproj.2.1 f' hf'T hf'_nl
  have hT_paths : ∀ e ∈ G.E, ∀ f ∈ walkEdges (T.forestPath (G.tail e) (G.head e)), f ∈ G.E := by
    intro e he f hf
    by_cases hne : G.tail e ≠ G.head e
    · exact (Finset.mem_filter.mp (hproj.2.2.1 e (Finset.mem_filter.mpr ⟨he, hne⟩) hf)).1
    · simp only [not_ne_iff] at hne
      rw [hne, forestPath_self hT_st.1] at hf
      simp [walkEdges] at hf
  have hsum_nl : ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e ≤
      (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v := by
    have hst_match : ∀ e' ∈ G_v.E,
        treeStretch G T ℓ (origEdge (copyMod G_nl) e') =
          treeStretch G_v T (weightedCopyLen G_nl ℓ) e' := by
      intro e' he'
      have hm := weightedCopyGraph_origEdge_mem hE_nl he'
      let e := origEdge (copyMod G_nl) e'
      have hw_e : weightedCopyLen G_nl ℓ e' = ℓ e := rfl
      have hlen_eq : walkLength (weightedCopyLen G_nl ℓ) (T.forestPath (G.tail e) (G.head e)) =
          walkLength ℓ (T.forestPath (G.tail e) (G.head e)) := by
        unfold walkLength
        refine Finset.sum_congr rfl fun f hf => ?_
        have hf_nl : f ∈ G_nl.E := hproj.2.2.1 e hm.1 hf
        have hf_len : weightedCopyLen G_nl ℓ f = ℓ f := by
          unfold weightedCopyLen origEdge
          rw [Nat.mod_eq_of_lt (lt_copyMod hf_nl)]
        rw [hf_len]
      unfold treeStretch
      rw [hm.2.1, hm.2.2, hw_e, hlen_eq]
    have hcopy_sum : ∑ e ∈ G_nl.E, (edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e =
        ∑ e' ∈ G_v.E, treeStretch G_v T (weightedCopyLen G_nl ℓ) e' := by
      rw [← weightedCopyGraph_sum_eq hE_nl v (treeStretch G T ℓ)]
      exact Finset.sum_congr rfl fun e' he' => hst_match e' he'
    have hGv_bound : ∑ e' ∈ G_v.E, treeStretch G_v T (weightedCopyLen G_nl ℓ) e' ≤
        (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_nl.E.card : ℝ) := by
      have h1 := hproj.2.2.2.2
      have h2 : (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_v.E.card : ℝ) ≤
          (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (2 * (G_nl.E.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hG_v_card (by positivity)
      linarith [h1, h2]
    have hnorm_nl_pos : 0 < G_nl.norm1 v := by
      rw [norm1_eq_sum_pos hv_nl]
      exact Finset.sum_pos hv_nl hE_nl
    have hm_nl_pos : (0 : ℝ) < (G_nl.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE_nl)
    have hst_nn : ∀ e ∈ G_nl.E, 0 ≤ treeStretch G T ℓ e := fun e he => by
      unfold treeStretch
      have hwl0 : 0 ≤ walkLength ℓ (T.forestPath (G.tail e) (G.head e)) := by
        unfold walkLength
        refine Finset.sum_nonneg fun f hf => ?_
        have hf_nl := hproj.2.2.1 e he hf
        exact mul_nonneg (hℓ_nl f hf_nl).le (abs_nonneg _)
      exact add_nonneg zero_le_one (div_nonneg hwl0 (hℓ_nl e he).le)
    have hsum_scaled : ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e ≤
        (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
          ∑ e ∈ G_nl.E, (edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e he => ?_
      have hceil : (G_nl.E.card : ℝ) * v e / G_nl.norm1 v ≤ (edgeMult G_nl v e : ℝ) := by
        unfold edgeMult; exact Nat.le_ceil _
      have hve : v e ≤ (G_nl.norm1 v / (G_nl.E.card : ℝ)) * (edgeMult G_nl v e : ℝ) := by
        have := mul_le_mul_of_nonneg_left hceil (div_nonneg hnorm_nl_pos.le hm_nl_pos.le)
        have heq : (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ((G_nl.E.card : ℝ) * v e / G_nl.norm1 v) = v e := by
          field_simp [ne_of_gt hnorm_nl_pos, ne_of_gt hm_nl_pos]
        rwa [heq] at this
      calc v e * treeStretch G T ℓ e
          ≤ ((G_nl.norm1 v / (G_nl.E.card : ℝ)) * (edgeMult G_nl v e : ℝ)) *
              treeStretch G T ℓ e := mul_le_mul_of_nonneg_right hve (hst_nn e he)
        _ = (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
              ((edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e) := by ring
    have hnorm_nl_le : G_nl.norm1 v ≤ G.norm1 v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _
    calc ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e
        ≤ (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ∑ e ∈ G_nl.E, (edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e := hsum_scaled
      _ = (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ∑ e' ∈ G_v.E, treeStretch G_v T (weightedCopyLen G_nl ℓ) e' := by rw [hcopy_sum]
      _ ≤ (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ((4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_nl.E.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hGv_bound (div_nonneg hnorm_nl_pos.le hm_nl_pos.le)
      _ = (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G_nl.norm1 v := by
          field_simp [ne_of_gt hm_nl_pos]
      _ ≤ (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v :=
          mul_le_mul_of_nonneg_left hnorm_nl_le (by positivity)
  let E_loop := G.E.filter fun e => ¬ (G.tail e ≠ G.head e)
  have hsum_loop : ∑ e ∈ E_loop, v e * treeStretch G T ℓ e ≤
      (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v := by
    have hpt : ∀ e ∈ E_loop, v e * treeStretch G T ℓ e = v e := fun e he => by
      have htl := not_ne_iff.mp (Finset.mem_filter.mp he).2
      simp [treeStretch, htl, forestPath_self hT_st.1, walkLength, walkEdges]
    rw [Finset.sum_congr rfl hpt]
    have hle_norm : ∑ e ∈ E_loop, v e ≤ G.norm1 v := by
      rw [norm1_eq_sum_pos hv]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun e he _ =>
        (hv e he).le
    have hnorm0 : 0 ≤ G.norm1 v := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc ∑ e ∈ E_loop, v e ≤ G.norm1 v := hle_norm
      _ = 1 * G.norm1 v := (one_mul _).symm
      _ ≤ (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v :=
          mul_le_mul_of_nonneg_right hlog2 hnorm0
  have hsum_total : ∑ e ∈ G.E, v e * treeStretch G T ℓ e ≤
      (4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v := by
    have hpart := (Finset.sum_filter_add_sum_filter_not G.E (fun e => G.tail e ≠ G.head e)
      (fun e => v e * treeStretch G T ℓ e)).symm
    change ∑ e ∈ G.E, v e * treeStretch G T ℓ e =
        ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e +
        ∑ e ∈ E_loop, v e * treeStretch G T ℓ e at hpart
    linarith [hpart, hsum_nl, hsum_loop]
  exact ⟨hT_st, hT_edges, hT_paths, hsum_total⟩

/-- Re-exported stretch bound from `MinCostFlow.LSF.Theorem22`: bounds the sum of stretches of
`G_v`-edges in `T_raw` by `(2 * K₁ + 2) * log²(n_orig + 2) * |E(G_v)|` from an `[AN19]` tree
`out` on `G_aug`. -/
theorem an19_stretch_sum_bound_gen
    {G_v T_gv T_raw : MGraph} {n_orig : ℕ} {len : ℕ → ℝ} {w_int : ℕ → ℕ}
    {δ K_AN K₁ : ℝ} {V_act : Finset ℕ} {V_list E_list B out : List ℕ}
    {edgeIdGv : ℕ → ℕ} {G_aug : Cited.WGraph}
    (hn1 : 1 ≤ n_orig) (hV_act_ge2 : 2 ≤ V_act.card) (hV_act_le_n : V_act.card ≤ n_orig)
    (hV_len : V_list.length = V_act.card)
    (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ V_act)
    (hG_v_end : ∀ e' ∈ G_v.E, G_v.tail e' ∈ V_act ∧ G_v.head e' ∈ V_act)
    (hB_len_lt : B.length + 1 ≤ G_v.E.card)
    (hE_len : E_list.length = G_v.E.card) (hE_nd : E_list.Nodup)
    (hE_mem : ∀ e', e' ∈ E_list ↔ e' ∈ G_v.E)
    (hδ_pos : 0 < δ) (hw_int_ge : ∀ e' ∈ G_v.E, 4 ≤ w_int e')
    (hlen_pos : ∀ e' ∈ G_v.E, 0 < len e')
    (hlen_upper : ∀ f ∈ G_v.E, len f ≤ δ * ((w_int f : ℝ) + 1))
    (hlen_lower : ∀ e' ∈ G_v.E, δ * (w_int e' : ℝ) ≤ len e')
    (hδ_Vact : ∀ e' ∈ G_v.E, δ * (V_act.card : ℝ) ≤ len e' / 2)
    (hG_aug_n_len : G_aug.n = V_list.length)
    (hG_aug_m : G_aug.m = E_list.length + B.length)
    (hG_aug_edge_E : ∀ (j : ℕ) (hj : j < E_list.length),
      G_aug.edges[j]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
        (V_list.idxOf (G_v.tail (E_list[j]'hj)),
         V_list.idxOf (G_v.head (E_list[j]'hj)), w_int (E_list[j]'hj)))
    (hG_aug_edge_B : ∀ (k : ℕ) (hk : k < B.length),
      G_aug.edges[E_list.length + k]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
        (0, V_list.idxOf (B[k]'hk), 1))
    (hout_conn : ∀ u < G_aug.n, ∀ v < G_aug.n, ∃ es, G_aug.IsWalkIn out u v es)
    (htot_st : G_aug.totalStretch out ≤ K_AN * (G_aug.m : ℝ) * Cited.logLogFactor G_aug.n)
    (hK₁_ge1 : 1 ≤ K₁) (hKAN_le : K_AN ≤ K₁)
    (hedgeId_lt : ∀ j, j < E_list.length → edgeIdGv j ∈ G_v.E)
    (hedgeId_eq_E : ∀ (j : ℕ) (hj : j < E_list.length), edgeIdGv j = E_list[j]'hj)
    (hedgeId_nG_B : ∀ k ∈ out, ¬ k < E_list.length → edgeIdGv k ∉ G_v.E)
    (hT_gv_V : T_gv.V = V_act)
    (hT_gv_val : T_gv.IsValid) (hT_gv_st : T_gv.IsSpanningTreeOn V_act)
    (hT_gv_conn : ∀ u ∈ V_act, ∀ v ∈ V_act, T_gv.Connected u v)
    (hT_gv_lift : ∀ {a b : ℕ} {es : List ℕ}, G_aug.IsWalkIn out a b es →
      ∀ u ∈ V_act, ∀ v ∈ V_act, V_list.idxOf u = a → V_list.idxOf v = b →
      ∃ P : List (ℕ × Bool), T_gv.IsWalk u v P ∧ P.map Prod.fst = es.map edgeIdGv)
    (hT_gv_no_bridges : ∀ e' ∈ G_v.E,
      walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')) ⊆ G_v.E)
    (hT_raw_path_eq : ∀ e' ∈ G_v.E,
      T_raw.forestPath (G_v.tail e') (G_v.head e') =
        T_gv.forestPath (G_v.tail e') (G_v.head e')) :
    ∑ e' ∈ G_v.E, treeStretch G_v T_raw len e' ≤
      (2 * K₁ + 2) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 * G_v.norm1 (fun _ => 1) := by
  classical
  let m₁ := E_list.length
  have hIsWalkIn_mem : ∀ {a b : ℕ} {es : List ℕ},
      G_aug.IsWalkIn out a b es → ∀ j ∈ es, j ∈ out ∧ j < G_aug.m := by
    intro a b es hes
    induction hes with
    | nil _ => intro _ h; exact absurd h List.not_mem_nil
    | @cons _ _ _ k ks hk hkm _ _ ih =>
      intro j hj
      rw [List.mem_cons] at hj
      exact hj.elim (fun h => h ▸ ⟨hk, hkm⟩) (fun h => ih j h)
  let toAug : Fin m₁ → Fin G_aug.m :=
    fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 (by rw [hG_aug_m]; omega)⟩
  have htoAug_inj : Function.Injective toAug := fun a b h =>
    Fin.ext (by simpa [toAug] using congrArg Fin.val h)
  have hwalkLength_gv_le : ∀ (i : Fin m₁),
      treeStretch G_v T_raw len (E_list[i.1]'i.2) ≤
        (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
          ((G_aug.edge (toAug i)).2.2 : ℝ) + 3 / 2 := by
    intro i
    let e' := E_list[i.1]'i.2
    let j := toAug i
    have he' : e' ∈ G_v.E := (hE_mem e').mp (List.getElem_mem i.2)
    have ho := hG_v_end e' he'
    have hged : G_aug.edge j = (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e') := by
      dsimp only [Cited.WGraph.edge, j]
      exact hG_aug_edge_E i.1 i.2
    unfold treeStretch
    rw [hT_raw_path_eq e' he']
    let P := T_gv.forestPath (G_v.tail e') (G_v.head e')
    have hP_path : T_gv.IsPath (G_v.tail e') (G_v.head e') P :=
      forestPath_isPath hT_gv_st.1 (hT_gv_conn _ ho.1 _ ho.2)
    have hP_sub : walkEdges P ⊆ G_v.E := hT_gv_no_bridges e' he'
    have hlen_P : (walkEdges P).card ≤ V_act.card := by
      have hverts_sub : (T_gv.walkVertices (G_v.tail e') P).toFinset ⊆ V_act := by
        intro z hz
        exact hT_gv_V ▸ (IsWalk_vertices_mem hT_gv_val (hT_gv_V ▸ ho.1) hP_path.1).2 z
          (List.mem_toFinset.mp hz)
      have hlen_v : (T_gv.walkVertices (G_v.tail e') P).length ≤ V_act.card := by
        rw [← List.toFinset_card_of_nodup hP_path.2]
        exact Finset.card_le_card hverts_sub
      have hvw : (T_gv.walkVertices (G_v.tail e') P).length = P.length + 1 := by
        simp [MGraph.walkVertices]
      have hwe : (walkEdges P).card ≤ P.length := by
        dsimp only [walkEdges]
        calc (P.map Prod.fst).toFinset.card ≤ (P.map Prod.fst).length := List.toFinset_card_le _
          _ = P.length := List.length_map _
      omega
    have hS_ne : {d | ∃ es, G_aug.IsWalkIn out (G_aug.edge j).1 (G_aug.edge j).2.1 es ∧
        d = G_aug.weightOf es}.Nonempty := by
      rw [hged]
      obtain ⟨es, hes⟩ := hout_conn (V_list.idxOf (G_v.tail e'))
        (hG_aug_n_len ▸ List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.1))
        (V_list.idxOf (G_v.head e'))
        (hG_aug_n_len ▸ List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.2))
      exact ⟨G_aug.weightOf es, es, hes, rfl⟩
    obtain ⟨es_min, hes_min, hdist_eq⟩ := Nat.sInf_mem hS_ne
    change G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 = G_aug.weightOf es_min at hdist_eq
    have hdist_sub : (∑ f ∈ walkEdges P, (w_int f : ℝ)) ≤
        (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) := by
      rw [hged] at hes_min
      obtain ⟨Q, hWQ, hQ_map⟩ := hT_gv_lift hes_min (G_v.tail e') ho.1
        (G_v.head e') ho.2 rfl rfl
      obtain ⟨P', hP'_path, hP'_edges, _⟩ := exists_isPath_of_isWalk hWQ
      have hPP' : P = P' := forestPath_eq_of_isPath hT_gv_st.1 hP'_path
      have hP_edges_Q : walkEdges P ⊆ (es_min.map edgeIdGv).toFinset := by
        rw [hPP']
        intro f hf
        have hfQ := hP'_edges hf
        rw [walkEdges, hQ_map] at hfQ
        exact hfQ
      let wf : ℕ → ℝ := fun f => if f ∈ G_v.E then (w_int f : ℝ) else 1
      have hwf_nn : ∀ f, 0 ≤ wf f := fun f => by
        dsimp only [wf]; split_ifs <;> positivity
      have hsum1 : ∑ f ∈ walkEdges P, (w_int f : ℝ) = ∑ f ∈ walkEdges P, wf f := by
        refine Finset.sum_congr rfl fun f hf => ?_
        dsimp only [wf]; rw [ite_eq_left (hP_sub hf)]
      have hsum2 : ∑ f ∈ walkEdges P, wf f ≤ ∑ f ∈ (es_min.map edgeIdGv).toFinset, wf f :=
        Finset.sum_le_sum_of_subset_of_nonneg hP_edges_Q fun f _ _ => hwf_nn f
      have hsum3 : ∑ f ∈ (es_min.map edgeIdGv).toFinset, wf f ≤
          ((es_min.map edgeIdGv).map wf).sum :=
        finset_sum_le_list_sum_of_nonneg wf hwf_nn (es_min.map edgeIdGv)
      have hsum4 : ((es_min.map edgeIdGv).map wf).sum = (G_aug.weightOf es_min : ℝ) := by
        unfold Cited.WGraph.weightOf
        rw [Nat.cast_list_sum, List.map_map, List.map_map]
        congr 1
        refine List.map_congr_left fun k hk => ?_
        have ⟨hk_out, hk_m⟩ := hIsWalkIn_mem hes_min k hk
        have hk_len : k < G_aug.edges.length := hk_m
        dsimp only [Function.comp_def]
        rw [List.getD_eq_getElem _ _ hk_len]
        by_cases hkm1 : k < m₁
        · have hkG := hedgeId_lt k hkm1
          have hke : E_list[k]'hkm1 = edgeIdGv k := (hedgeId_eq_E k hkm1).symm
          have hged_k : G_aug.edges[k]'hk_len =
              (V_list.idxOf (G_v.tail (edgeIdGv k)), V_list.idxOf (G_v.head (edgeIdGv k)),
                w_int (edgeIdGv k)) := by
            simpa only [hke] using hG_aug_edge_E k hkm1
          dsimp only [wf]
          rw [ite_eq_left hkG, hged_k]
        · have hk_nG := hedgeId_nG_B k hk_out hkm1
          have hk_ltB : k - m₁ < B.length := by rw [hG_aug_m] at hk_m; omega
          have hm1k : E_list.length + (k - m₁) = k := by dsimp only [m₁]; omega
          have hged_k : G_aug.edges[k]'hk_len = (0, V_list.idxOf (B[k - m₁]'hk_ltB), 1) := by
            have hB' := hG_aug_edge_B (k - m₁) hk_ltB
            simpa only [hm1k] using hB'
          dsimp only [wf]
          rw [ite_eq_right hk_nG, hged_k]
          norm_num
      rw [hdist_eq, ← hsum4]
      exact hsum1.le.trans (hsum2.trans hsum3)
    have hwl_eq : walkLength len P = ∑ f ∈ walkEdges P, len f :=
      walkLength_eq_sum_of_isPath len hP_path
    have hwl_le : walkLength len P ≤
        δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) +
          δ * (V_act.card : ℝ) := by
      calc walkLength len P
          = ∑ f ∈ walkEdges P, len f := hwl_eq
        _ ≤ ∑ f ∈ walkEdges P, δ * ((w_int f : ℝ) + 1) :=
            Finset.sum_le_sum fun f hf => hlen_upper f (hP_sub hf)
        _ = δ * (∑ f ∈ walkEdges P, (w_int f : ℝ)) + δ * ((walkEdges P).card : ℝ) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              nsmul_eq_mul, mul_one, mul_comm ((walkEdges P).card : ℝ) δ]
        _ ≤ δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) +
              δ * (V_act.card : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left hdist_sub hδ_pos.le)
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen_P) hδ_pos.le)
    have hlen_e' : 0 < len e' := hlen_pos e' he'
    have hδ_le_e' : δ * (w_int e' : ℝ) ≤ len e' := hlen_lower e' he'
    have hδ_Vact_e' : δ * (V_act.card : ℝ) ≤ len e' / 2 := hδ_Vact e' he'
    have hw_edge_pos : (0 : ℝ) < (w_int e' : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by decide : 0 < 4) (hw_int_ge e' he'))
    have hterm1 : δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) / len e' ≤
        (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
          ((G_aug.edge j).2.2 : ℝ) := by
      rw [hged]
      dsimp only
      have hdiv : δ / len e' ≤ 1 / (w_int e' : ℝ) := by
        rw [div_le_div_iff₀ hlen_e' hw_edge_pos]
        linarith
      have hdt0 : 0 ≤ (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) :=
        Nat.cast_nonneg _
      have heq1 : δ * (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) /
          len e' =
        (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) *
          (δ / len e') := by ring
      have heq2 : (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) /
          (w_int e' : ℝ) =
        (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) *
          (1 / (w_int e' : ℝ)) := by ring
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_left hdiv hdt0
    have hterm2 : δ * (V_act.card : ℝ) / len e' ≤ 1 / 2 := by
      rw [div_le_iff₀ hlen_e']
      linarith
    calc 1 + walkLength len P / len e'
        ≤ 1 + (δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) +
            δ * (V_act.card : ℝ)) / len e' :=
          add_le_add le_rfl (div_le_div_of_nonneg_right hwl_le hlen_e'.le)
      _ = 1 + δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) / len e' +
          δ * (V_act.card : ℝ) / len e' := by ring
      _ ≤ 1 + (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
            ((G_aug.edge j).2.2 : ℝ) + 1 / 2 := add_le_add (add_le_add le_rfl hterm1) hterm2
      _ = (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
            ((G_aug.edge j).2.2 : ℝ) + 3 / 2 := by ring
  have hlog2 : 1 ≤ (Real.log ((n_orig : ℝ) + 2)) ^ 2 := one_le_log_add_two_sq hn1
  have hnorm1_one : G_v.norm1 (fun _ => (1 : ℝ)) = (G_v.E.card : ℝ) := by
    unfold MGraph.norm1
    simp only [abs_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_list : ∑ e' ∈ G_v.E, treeStretch G_v T_raw len e' =
      ∑ i : Fin m₁, treeStretch G_v T_raw len (E_list[i.1]'i.2) := by
    refine (Finset.sum_bij (i := fun (i : Fin m₁) _ => E_list[i.1]'i.2)
      (fun (i : Fin m₁) _ => (hE_mem (E_list[i.1]'i.2)).mp (List.getElem_mem i.2))
      (fun (i₁ : Fin m₁) _ (i₂ : Fin m₁) _ h =>
        Fin.ext ((List.Nodup.getElem_inj hE_nd).mp h))
      (fun e' he' => ⟨⟨E_list.idxOf e', List.idxOf_lt_length_of_mem ((hE_mem _).mpr he')⟩,
        Finset.mem_univ _, List.getElem_idxOf _⟩)
      (fun _ _ => rfl)).symm
  have hsum_aug_sub : ∑ i : Fin m₁,
        (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
          ((G_aug.edge (toAug i)).2.2 : ℝ) ≤ G_aug.totalStretch out := by
    have hcongr : ∑ i : Fin m₁,
          (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
            ((G_aug.edge (toAug i)).2.2 : ℝ) =
        ∑ j ∈ Finset.univ.image toAug,
          (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
            ((G_aug.edge j).2.2 : ℝ) := by
      rw [Finset.sum_image fun a _ b _ h => htoAug_inj h]
    rw [hcongr]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hll_bds := logLogFactor_bounds hV_act_ge2 hV_act_le_n
  have hG_aug_m_le : (G_aug.m : ℝ) ≤ 2 * (m₁ : ℝ) := by
    rw [hG_aug_m]
    have : B.length ≤ m₁ := by rw [← hE_len] at hB_len_lt; omega
    exact_mod_cast (by omega : m₁ + B.length ≤ 2 * m₁)
  have htot_le : G_aug.totalStretch out ≤
      2 * K₁ * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 := by
    have h1 : K_AN * (G_aug.m : ℝ) * Cited.logLogFactor G_aug.n ≤
        K₁ * (2 * (m₁ : ℝ)) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 := by
      have hG_aug_n : G_aug.n = V_act.card := hG_aug_n_len.trans hV_len
      rw [hG_aug_n]
      exact mul_le_mul
        (mul_le_mul hKAN_le hG_aug_m_le (Nat.cast_nonneg _) (by positivity))
        hll_bds.2 hll_bds.1 (by positivity)
    linarith [htot_st, h1]
  have hm1_eq : (m₁ : ℝ) = (G_v.E.card : ℝ) := by exact_mod_cast hE_len
  calc ∑ e' ∈ G_v.E, treeStretch G_v T_raw len e'
      = ∑ i : Fin m₁, treeStretch G_v T_raw len (E_list[i.1]'i.2) := hsum_list
    _ ≤ ∑ i : Fin m₁,
          ((G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
            ((G_aug.edge (toAug i)).2.2 : ℝ) + 3 / 2) :=
        Finset.sum_le_sum fun i _ => hwalkLength_gv_le i
    _ = (∑ i : Fin m₁,
          (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
            ((G_aug.edge (toAug i)).2.2 : ℝ)) + (3 / 2 : ℝ) * (m₁ : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
    _ ≤ G_aug.totalStretch out + (3 / 2 : ℝ) * (m₁ : ℝ) := add_le_add hsum_aug_sub le_rfl
    _ ≤ 2 * K₁ * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 +
          2 * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 := by
        have hm0 : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁
        have h32_1 : (3 / 2 : ℝ) * (m₁ : ℝ) ≤ 2 * (m₁ : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) hm0
        have h32_2 : 2 * (m₁ : ℝ) ≤ 2 * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 :=
          le_mul_of_one_le_right (mul_nonneg (by norm_num) hm0) hlog2
        exact add_le_add htot_le (h32_1.trans h32_2)
    _ = (2 * K₁ + 2) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 * G_v.norm1 (fun _ => 1) := by
        rw [hnorm1_one, ← hm1_eq]; ring

end MinCostFlow.WideWord
