module

public import MinCostFlow.ExpanderDecomp.Blocks
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Macro-graph block composition (macro step)

`Blocks.lean` proves `isExpansionExpanderOn_of_blocks`, which combines internal block expansion `β`
with two hypotheses on the external edges `Eext`: bounded vertex degree `Δ` and expansion `α` across
every union of blocks.

This file discharges both hypotheses for the block construction of
`Blocks.lean`:
* the vertices of `X` are partitioned by `blk : ℕ → ℕ` into `H.n` blocks of equal size `b`;
* `H` is a valid macro graph on `H.verts = Finset.range H.n` with maximum degree at most `Δ` and
  edge expansion at least `α`;
* for each macro edge occurrence `j < H.m` joining `(i, k)`, we have a bipartite perfect matching
  `M j` between block `i` and block `k`, and `Eext` is a permutation of the concatenation of these
  matchings.

Main results:
* `degIn_macro_le`: every vertex `v ∈ X` has degree at most `H.deg (blk v)` in `Eext[X]`.
* `hext_of_macro`: every union of blocks `X.filter (fun v => blk v ∈ A)` has cut at least
  `α · min(|U|, |X \ U|)` in `Eext[X]`.
* `isExpansionExpanderOn_of_macro_blocks`: composed expansion `α * β / (Δ + 1)` on `X`.
* `isExpansionExpanderOn_of_macro_blocks_nine`: specialization to `Δ = 9`, giving `α * β / 10`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- An edge list `M` is a bipartite perfect matching between `U` and `W`: every edge joins `U` to
`W`, no vertex appears twice as an endpoint, and the number of edges equals both `|U|` and `|W|`. -/
def IsBipartiteMatching (U W : Finset ℕ) (M : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ M, (e.1 ∈ U ∧ e.2 ∈ W) ∨ (e.1 ∈ W ∧ e.2 ∈ U)) ∧
    (M.flatMap fun e => [e.1, e.2]).Nodup ∧
    M.length = U.card ∧ M.length = W.card

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Helper lemmas for bipartite matchings and edge-list operations -/

/-- A directed matching from `U` to `W` (distinct first ends in `U`, distinct second ends in `W`,
with `U` and `W` disjoint and `M.length = |U| = |W|`) is a bipartite perfect matching. -/
theorem IsBipartiteMatching.of_directed {U W : Finset ℕ} {M : List (ℕ × ℕ)}
    (hdisj : Disjoint U W) (hmem : ∀ e ∈ M, e.1 ∈ U ∧ e.2 ∈ W)
    (hfst : (M.map Prod.fst).Nodup) (hsnd : (M.map Prod.snd).Nodup)
    (hU : M.length = U.card) (hW : M.length = W.card) :
    IsBipartiteMatching U W M := by
  refine ⟨fun e he => Or.inl (hmem e he), ?_, hU, hW⟩
  clear hU hW
  induction M with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [List.map_cons, List.nodup_cons] at hfst hsnd
    have hab : a ∈ U ∧ b ∈ W := hmem (a, b) List.mem_cons_self
    have hrest_mem : ∀ e ∈ rest, e.1 ∈ U ∧ e.2 ∈ W :=
      fun e he => hmem e (List.mem_cons_of_mem _ he)
    have hne_ab : a ≠ b := fun h => Finset.disjoint_left.mp hdisj hab.1 (h ▸ hab.2)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
    refine ⟨?_, ?_, ih hrest_mem hfst.2 hsnd.2⟩
    · intro ha
      rcases List.mem_cons.mp ha with rfl | hfm
      · exact hne_ab rfl
      · obtain ⟨e, he, hmem_e⟩ := List.mem_flatMap.mp hfm
        have heUW := hrest_mem e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_e
        rcases hmem_e with rfl | rfl
        · exact hfst.1 (List.mem_map.mpr ⟨e, he, rfl⟩)
        · exact Finset.disjoint_left.mp hdisj hab.1 heUW.2
    · intro hb
      obtain ⟨e, he, hmem_e⟩ := List.mem_flatMap.mp hb
      have heUW := hrest_mem e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_e
      rcases hmem_e with rfl | rfl
      · exact Finset.disjoint_left.mp hdisj heUW.1 hab.2
      · exact hsnd.1 (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- Permuting the edge list preserves `degIn`. -/
theorem degIn_of_perm (n : ℕ) {E₁ E₂ : List (ℕ × ℕ)} (hp : E₁.Perm E₂) (X : Finset ℕ) (v : ℕ) :
    (Graph.mk n E₁).degIn X v = (Graph.mk n E₂).degIn X v := by
  unfold Graph.degIn Graph.inside
  rw [((hp.filter _).filter _).length_eq, ((hp.filter _).filter _).length_eq]

/-- Permuting the edge list preserves `cutIn`. -/
theorem cutIn_of_perm (n : ℕ) {E₁ E₂ : List (ℕ × ℕ)} (hp : E₁.Perm E₂) (X S : Finset ℕ) :
    (Graph.mk n E₁).cutIn X S = (Graph.mk n E₂).cutIn X S := by
  unfold Graph.cutIn Graph.inside
  exact ((hp.filter _).filter _).length_eq

/-- Degree adds over appended edge lists. -/
theorem degIn_append (n : ℕ) (E₁ E₂ : List (ℕ × ℕ)) (X : Finset ℕ) (v : ℕ) :
    (Graph.mk n (E₁ ++ E₂)).degIn X v =
      (Graph.mk n E₁).degIn X v + (Graph.mk n E₂).degIn X v := by
  simp only [Graph.degIn, Graph.inside, List.filter_append, List.length_append]
  omega

/-- Degree of a `flatMap` over `List.range k` is the sum of the degrees. -/
theorem degIn_flatMap_range (n k : ℕ) (M : ℕ → List (ℕ × ℕ)) (X : Finset ℕ) (v : ℕ) :
    (Graph.mk n ((List.range k).flatMap M)).degIn X v =
      ∑ j ∈ Finset.range k, (Graph.mk n (M j)).degIn X v := by
  induction k with
  | zero => simp [Graph.degIn, Graph.inside]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, degIn_append, ih,
      Finset.sum_range_succ]

/-- Cut of a `flatMap` over `List.range k` is the sum of the cuts. -/
theorem cutIn_flatMap_range (n k : ℕ) (M : ℕ → List (ℕ × ℕ)) (X S : Finset ℕ) :
    (Graph.mk n ((List.range k).flatMap M)).cutIn X S =
      ∑ j ∈ Finset.range k, (Graph.mk n (M j)).cutIn X S := by
  induction k with
  | zero => simp [Graph.cutIn, Graph.inside]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, cutIn_append, ih,
      Finset.sum_range_succ]

private lemma filter_fst_add_snd_eq_count_flatMap (M : List (ℕ × ℕ)) (v : ℕ) :
    (M.filter fun e => e.1 = v).length + (M.filter fun e => e.2 = v).length =
      (M.flatMap fun e => [e.1, e.2]).count v := by
  induction M with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [List.filter_cons, List.flatMap_cons, List.cons_append, List.nil_append,
      List.count_cons, beq_iff_eq]
    by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb] <;> omega

/-- A list of edges with distinct endpoints contributes degree at most `1` at every vertex. -/
private lemma degIn_le_one_of_nodup_flatMap (n : ℕ) {M : List (ℕ × ℕ)}
    (hnd : (M.flatMap fun e => [e.1, e.2]).Nodup) (X : Finset ℕ) (v : ℕ) :
    (Graph.mk n M).degIn X v ≤ 1 := by
  have h1 : ((Graph.mk n M).inside X |>.filter fun e => e.1 = v).length ≤
      (M.filter fun e => e.1 = v).length := by
    unfold Graph.inside
    rw [List.filter_filter]
    exact length_filter_le_of_imp M fun e _ h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact h.1
  have h2 : ((Graph.mk n M).inside X |>.filter fun e => e.2 = v).length ≤
      (M.filter fun e => e.2 = v).length := by
    unfold Graph.inside
    rw [List.filter_filter]
    exact length_filter_le_of_imp M fun e _ h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact h.1
  have hcnt : (M.flatMap fun e => [e.1, e.2]).count v ≤ 1 := List.nodup_iff_count_le_one.mp hnd v
  have heq := filter_fst_add_snd_eq_count_flatMap M v
  unfold Graph.degIn
  omega

/-- A bipartite matching between `U` and `W` contributes degree `0` outside `U ∪ W`. -/
private lemma degIn_eq_zero_of_bipartiteMatching (n : ℕ) {U W : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : IsBipartiteMatching U W M) (X : Finset ℕ) {v : ℕ} (hvU : v ∉ U) (hvW : v ∉ W) :
    (Graph.mk n M).degIn X v = 0 := by
  rw [degIn_eq_sum_map]
  have h0 : ((Graph.mk n M).inside X |>.map fun e =>
      (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)) =
      ((Graph.mk n M).inside X).map fun _ => 0 := by
    apply List.map_congr_left
    intro e he
    rw [mem_inside_iff] at he
    rcases hM.1 e he.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hne1 : e.1 ≠ v := fun h => hvU (h ▸ h1)
      have hne2 : e.2 ≠ v := fun h => hvW (h ▸ h2)
      simp [hne1, hne2]
    · have hne1 : e.1 ≠ v := fun h => hvW (h ▸ h1)
      have hne2 : e.2 ≠ v := fun h => hvU (h ▸ h2)
      simp [hne1, hne2]
  rw [h0, sum_map_const]
  simp

/-- If `U` and `W` lie on opposite sides of `S` inside `X`, then every edge of a bipartite matching
between `U` and `W` crosses `S`. -/
private lemma cutIn_eq_length_of_bipartiteMatching (n : ℕ) {X S U W : Finset ℕ}
    {M : List (ℕ × ℕ)} (hUX : U ⊆ X) (hWX : W ⊆ X) (hM : IsBipartiteMatching U W M)
    (hcross : (U ⊆ S ∧ Disjoint W S) ∨ (W ⊆ S ∧ Disjoint U S)) :
    (Graph.mk n M).cutIn X S = M.length := by
  have hins : (Graph.mk n M).inside X = M := by
    unfold Graph.inside
    apply List.filter_eq_self.mpr
    intro e he
    rcases hM.1 e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [hUX h1, hWX h2]
    · simp [hWX h1, hUX h2]
  unfold Graph.cutIn
  rw [hins]
  have hfilt : M.filter (fun e => decide (e.1 ∈ S) != decide (e.2 ∈ S)) = M := by
    apply List.filter_eq_self.mpr
    intro e he
    rcases hM.1 e he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hcross with ⟨hS, hd⟩ | ⟨hS, hd⟩
    · simp [hS h1, Finset.disjoint_left.mp hd h2]
    · simp [Finset.disjoint_left.mp hd h1, hS h2]
    · simp [Finset.disjoint_left.mp hd h1, hS h2]
    · simp [hS h1, Finset.disjoint_left.mp hd h2]
  rw [hfilt]

/-! ### Degree and macro-cut bounds -/

/-- Every vertex `v` has degree in `Eext[X]` at most the macro degree `H.deg (blk v)`. -/
theorem degIn_macro_le {n : ℕ} {X : Finset ℕ} {blk : ℕ → ℕ} {H : Graph}
    {M : ℕ → List (ℕ × ℕ)} {Eext : List (ℕ × ℕ)}
    (hHvalid : H.IsValid)
    (hM : ∀ j < H.m, IsBipartiteMatching
      (X.filter fun v => blk v = (edgeAt H.edges j).1)
      (X.filter fun v => blk v = (edgeAt H.edges j).2) (M j))
    (hperm : Eext.Perm ((List.range H.m).flatMap M))
    (v : ℕ) :
    (Graph.mk n Eext).degIn X v ≤ H.deg (blk v) := by
  rw [degIn_of_perm n hperm, degIn_flatMap_range]
  have hdegH : H.deg (blk v) =
      ∑ j ∈ Finset.range H.m,
        ((if (edgeAt H.edges j).1 = blk v then 1 else 0) +
          (if (edgeAt H.edges j).2 = blk v then 1 else 0)) := by
    unfold Graph.deg
    rw [degIn_eq_sum_map, inside_verts_of_isValid hHvalid]
    have hsum : ∀ (l : List (ℕ × ℕ)),
        (l.map fun e => (if e.1 = blk v then 1 else 0) + (if e.2 = blk v then 1 else 0)).sum =
          ∑ j ∈ Finset.range l.length,
            ((if (edgeAt l j).1 = blk v then 1 else 0) +
              (if (edgeAt l j).2 = blk v then 1 else 0)) := by
      intro l
      induction l with
      | nil => simp
      | cons e rest ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
        simp only [edgeAt, List.getD_cons_zero, List.getD_cons_succ]
        exact Nat.add_comm _ _
    exact hsum H.edges
  rw [hdegH]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j < H.m := Finset.mem_range.mp hj
  have hMj := hM j hjm
  by_cases h1 : (edgeAt H.edges j).1 = blk v
  · have hle := degIn_le_one_of_nodup_flatMap n hMj.2.1 X v
    simp only [h1, ↓reduceIte]
    omega
  · by_cases h2 : (edgeAt H.edges j).2 = blk v
    · have hle := degIn_le_one_of_nodup_flatMap n hMj.2.1 X v
      simp only [h2, ↓reduceIte]
      omega
    · have hvU : v ∉ X.filter fun u => blk u = (edgeAt H.edges j).1 := by
        simp [Finset.mem_filter, Ne.symm h1]
      have hvW : v ∉ X.filter fun u => blk u = (edgeAt H.edges j).2 := by
        simp [Finset.mem_filter, Ne.symm h2]
      rw [degIn_eq_zero_of_bipartiteMatching n hMj X hvU hvW]
      exact Nat.zero_le _

/-- For equal-sized blocks of size `b`, the cardinality of a union of blocks indexed by `A` is
`b * |H.verts ∩ A|`. -/
private lemma card_filter_blk_mem {X A : Finset ℕ} {blk : ℕ → ℕ} {k b : ℕ}
    (hblk : ∀ v ∈ X, blk v < k)
    (hsize : ∀ i < k, (X.filter fun v => blk v = i).card = b) :
    (X.filter fun v => blk v ∈ A).card = b * (Finset.range k ∩ A).card := by
  have hfib : (X.filter fun v => blk v ∈ A).card =
      ∑ i ∈ Finset.range k ∩ A, ((X.filter fun v => blk v ∈ A).filter fun v => blk v = i).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (hblk v hv.1), hv.2⟩)
  rw [hfib]
  have hterm : ∀ i ∈ Finset.range k ∩ A,
      ((X.filter fun v => blk v ∈ A).filter fun v => blk v = i).card = b := by
    intro i hi
    rw [Finset.mem_inter, Finset.mem_range] at hi
    have heq : (X.filter fun v => blk v ∈ A).filter (fun v => blk v = i) =
        X.filter fun v => blk v = i := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.symm ▸ hi.2⟩, h.2⟩⟩
    rw [heq, hsize i hi.1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- For equal-sized blocks of size `b`, the complement of a union of blocks indexed by `A` has size
`b * |H.verts \ (H.verts ∩ A)|`. -/
private lemma card_sdiff_filter_blk_mem {X A : Finset ℕ} {blk : ℕ → ℕ} {k b : ℕ}
    (hblk : ∀ v ∈ X, blk v < k)
    (hsize : ∀ i < k, (X.filter fun v => blk v = i).card = b) :
    (X \ X.filter fun v => blk v ∈ A).card =
      b * (Finset.range k \ (Finset.range k ∩ A)).card := by
  have hsd : X \ X.filter (fun v => blk v ∈ A) = X.filter fun v => blk v ∈ Finset.range k \ A := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hvX, hnot⟩
      exact ⟨hvX, hblk v hvX, fun hA => hnot ⟨hvX, hA⟩⟩
    · rintro ⟨hvX, _, hnotA⟩
      exact ⟨hvX, fun h => hnotA h.2⟩
  rw [hsd, card_filter_blk_mem hblk hsize]
  congr 2
  ext i
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- **Macro step of the block composition (`hext` hypothesis)**: if the blocks of `X` have equal size `b`, the
macro graph `H` is valid and has edge expansion at least `α ≥ 0` on `H.verts`, and `Eext` is a
permutation of bipartite perfect matchings along the edges of `H`, then every union of blocks `U`
has external cut at least `α * min(|U|, |X \ U|)`. -/
theorem hext_of_macro {n b : ℕ} {X : Finset ℕ} {blk : ℕ → ℕ} {H : Graph} {α : ℝ}
    {M : ℕ → List (ℕ × ℕ)} {Eext : List (ℕ × ℕ)}
    (hHvalid : H.IsValid) (hHexp : H.IsExpansionExpanderOn H.verts α)
    (hblk : ∀ v ∈ X, blk v < H.n)
    (hsize : ∀ i < H.n, (X.filter fun v => blk v = i).card = b)
    (hM : ∀ j < H.m, IsBipartiteMatching
      (X.filter fun v => blk v = (edgeAt H.edges j).1)
      (X.filter fun v => blk v = (edgeAt H.edges j).2) (M j))
    (hperm : Eext.Perm ((List.range H.m).flatMap M))
    (A : Finset ℕ) :
    α * min ((X.filter fun v => blk v ∈ A).card : ℝ)
        (X \ X.filter fun v => blk v ∈ A).card ≤
      (Graph.mk n Eext).cutIn X (X.filter fun v => blk v ∈ A) := by
  classical
  set S := X.filter fun v => blk v ∈ A
  set B := H.verts ∩ A
  -- Bound the cut of `S` in `Eext[X]` from below by `b * H.cut B`.
  have hcut_ge : b * H.cut B ≤ (Graph.mk n Eext).cutIn X S := by
    rw [cutIn_of_perm n hperm, cutIn_flatMap_range]
    have hHcut : H.cut B = ((Finset.range H.m).filter fun j =>
        crossesB B (edgeAt H.edges j) = true).card := by
      unfold Graph.cut
      rw [cutIn_eq_card]
      congr 1
      apply Finset.filter_congr
      intro j hj
      have hjm : j < H.m := Finset.mem_range.mp hj
      have he : edgeAt H.edges j ∈ H.edges := by
        unfold edgeAt
        rw [List.getD_eq_getElem _ _ hjm]
        exact List.getElem_mem hjm
      have hv := hHvalid _ he
      have hin : insideB H.verts (edgeAt H.edges j) = true := by
        simp [insideB, Graph.verts, hv.1, hv.2]
      simp [hin]
    rw [hHcut]
    set cr := (Finset.range H.m).filter fun j => crossesB B (edgeAt H.edges j) = true
    calc b * cr.card
        = ∑ _j ∈ cr, b := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ j ∈ cr, (Graph.mk n (M j)).cutIn X S := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [cr, Finset.mem_filter, Finset.mem_range] at hj
          obtain ⟨hjm, hcr⟩ := hj
          have he : edgeAt H.edges j ∈ H.edges := by
            unfold edgeAt
            rw [List.getD_eq_getElem _ _ hjm]
            exact List.getElem_mem hjm
          have hv := hHvalid _ he
          have hMj := hM j hjm
          set U := X.filter fun v => blk v = (edgeAt H.edges j).1
          set W := X.filter fun v => blk v = (edgeAt H.edges j).2
          have hcross : (U ⊆ S ∧ Disjoint W S) ∨ (W ⊆ S ∧ Disjoint U S) := by
            unfold crossesB at hcr
            by_cases h1 : (edgeAt H.edges j).1 ∈ B
            · have h2 : (edgeAt H.edges j).2 ∉ B := by
                intro h2; simp [h1, h2] at hcr
              left
              refine ⟨?_, ?_⟩
              · intro v hvU
                simp only [U, Finset.mem_filter] at hvU
                exact Finset.mem_filter.mpr ⟨hvU.1, hvU.2.symm ▸ (Finset.mem_inter.mp h1).2⟩
              · rw [Finset.disjoint_left]
                intro v hvW hvS
                simp only [W, Finset.mem_filter] at hvW
                simp only [S, Finset.mem_filter] at hvS
                exact h2 (Finset.mem_inter.mpr
                  ⟨Finset.mem_range.mpr hv.2, hvW.2 ▸ hvS.2⟩)
            · have h2 : (edgeAt H.edges j).2 ∈ B := by
                by_contra h2; simp [h1, h2] at hcr
              right
              refine ⟨?_, ?_⟩
              · intro v hvW
                simp only [W, Finset.mem_filter] at hvW
                exact Finset.mem_filter.mpr ⟨hvW.1, hvW.2.symm ▸ (Finset.mem_inter.mp h2).2⟩
              · rw [Finset.disjoint_left]
                intro v hvU hvS
                simp only [U, Finset.mem_filter] at hvU
                simp only [S, Finset.mem_filter] at hvS
                exact h1 (Finset.mem_inter.mpr
                  ⟨Finset.mem_range.mpr hv.1, hvU.2 ▸ hvS.2⟩)
          have hlen := cutIn_eq_length_of_bipartiteMatching n
            (Finset.filter_subset _ X) (Finset.filter_subset _ X) hMj hcross
          have hUcard : U.card = b := hsize _ hv.1
          rw [hlen, hMj.2.2.1, hUcard]
      _ ≤ ∑ j ∈ Finset.range H.m, (Graph.mk n (M j)).cutIn X S :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- Combine with the macro expansion bound on `B ⊆ H.verts`.
  have hBsub : B ⊆ H.verts := Finset.inter_subset_left
  have hexpH : α * min (B.card : ℝ) (H.verts \ B).card ≤ (H.cut B : ℝ) :=
    IsExpansionExpanderOn.mul_min_le hHexp hBsub
  have hc1 : (S.card : ℝ) = (b : ℝ) * (B.card : ℝ) := by
    exact_mod_cast card_filter_blk_mem (k := H.n) (A := A) hblk hsize
  have hc2 : ((X \ S).card : ℝ) = (b : ℝ) * ((H.verts \ B).card : ℝ) := by
    exact_mod_cast card_sdiff_filter_blk_mem (k := H.n) (A := A) hblk hsize
  have hcut_ge_r : (b : ℝ) * (H.cut B : ℝ) ≤ ((Graph.mk n Eext).cutIn X S : ℝ) := by
    exact_mod_cast hcut_ge
  rw [hc1, hc2, ← mul_min_of_nonneg _ _ (Nat.cast_nonneg b)]
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hmul := mul_le_mul_of_nonneg_left hexpH hb0
  calc α * ((b : ℝ) * min (B.card : ℝ) (H.verts \ B).card)
      = (b : ℝ) * (α * min (B.card : ℝ) (H.verts \ B).card) := by ring
    _ ≤ (b : ℝ) * (H.cut B : ℝ) := hmul
    _ ≤ ((Graph.mk n Eext).cutIn X S : ℝ) := hcut_ge_r

/-! ### Composed block expansion bounds -/

/-- **Block composition** (general degree `Δ`): equal-sized blocks of expansion `β`, joined by bipartite
perfect matchings along a valid macro graph `H` of maximum degree at most `Δ` and expansion `α`,
have combined expansion at least `α * β / (Δ + 1)`. -/
theorem isExpansionExpanderOn_of_macro_blocks {n b Δ : ℕ} {Eint Eext : List (ℕ × ℕ)}
    {X : Finset ℕ} (blk : ℕ → ℕ) {H : Graph} {α β : ℝ} {M : ℕ → List (ℕ × ℕ)}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hHvalid : H.IsValid) (hHdeg : ∀ i < H.n, H.deg i ≤ Δ)
    (hHexp : H.IsExpansionExpanderOn H.verts α)
    (hblk : ∀ v ∈ X, blk v < H.n)
    (hsize : ∀ i < H.n, (X.filter fun v => blk v = i).card = b)
    (hint : ∀ i < H.n,
      (Graph.mk n Eint).IsExpansionExpanderOn (X.filter fun v => blk v = i) β)
    (hM : ∀ j < H.m, IsBipartiteMatching
      (X.filter fun v => blk v = (edgeAt H.edges j).1)
      (X.filter fun v => blk v = (edgeAt H.edges j).2) (M j))
    (hperm : Eext.Perm ((List.range H.m).flatMap M)) :
    (Graph.mk n (Eint ++ Eext)).IsExpansionExpanderOn X (α * β / (Δ + 1)) := by
  refine isExpansionExpanderOn_of_blocks blk hα0 hα1 hβ0 hβ1 ?_ ?_ ?_
  · intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hint (blk v) (hblk v hv)
  · intro v hv
    exact le_trans (degIn_macro_le hHvalid hM hperm v) (hHdeg (blk v) (hblk v hv))
  · exact hext_of_macro hHvalid hHexp hblk hsize hM hperm

/-- **Block composition** (degree-9 macro graph): equal-sized blocks of expansion `β`, joined by bipartite
perfect matchings along a degree-9 `α`-expander macro graph, have combined expansion at least
`α * β / 10`. -/
theorem isExpansionExpanderOn_of_macro_blocks_nine {n b : ℕ} {Eint Eext : List (ℕ × ℕ)}
    {X : Finset ℕ} (blk : ℕ → ℕ) {H : Graph} {α β : ℝ} {M : ℕ → List (ℕ × ℕ)}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hHvalid : H.IsValid) (hHdeg : ∀ i < H.n, H.deg i ≤ 9)
    (hHexp : H.IsExpansionExpanderOn H.verts α)
    (hblk : ∀ v ∈ X, blk v < H.n)
    (hsize : ∀ i < H.n, (X.filter fun v => blk v = i).card = b)
    (hint : ∀ i < H.n,
      (Graph.mk n Eint).IsExpansionExpanderOn (X.filter fun v => blk v = i) β)
    (hM : ∀ j < H.m, IsBipartiteMatching
      (X.filter fun v => blk v = (edgeAt H.edges j).1)
      (X.filter fun v => blk v = (edgeAt H.edges j).2) (M j))
    (hperm : Eext.Perm ((List.range H.m).flatMap M)) :
    (Graph.mk n (Eint ++ Eext)).IsExpansionExpanderOn X (α * β / 10) := by
  have h := isExpansionExpanderOn_of_macro_blocks (Δ := 9) blk hα0 hα1 hβ0 hβ1 hHvalid hHdeg
    hHexp hblk hsize hint hM hperm
  have h9 : ((9 : ℕ) : ℝ) + 1 = 10 := by norm_num
  rw [h9] at h
  exact h

end MinCostFlow.ExpanderDecomp
