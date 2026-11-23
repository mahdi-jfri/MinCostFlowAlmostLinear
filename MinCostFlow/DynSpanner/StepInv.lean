module

public import MinCostFlow.DynSpanner.RebuildSpec
public import MinCostFlow.DynSpanner.Potential

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inductive step invariant for Algorithm 6

This file proves that initialization (`init`) and each single update step (`step`) preserve the
complete structural invariant `SnapInv` of the dynamic spanner state across arbitrary valid
sequences of edge deletions and vertex splits, and produces `StepCostRecord` containing the
batch validity, edge-difference, and operation-count bounds used in `Correctness.lean` and
`Complexity.lean`.
-/

namespace MinCostFlow.DynSpanner

section HelperCongr

@[expose] public section

/-- Count of `.delete` updates in a batch. -/
def batchDeleteCount (U : List Update) : ℕ :=
  (U.filter fun u => match u with | .delete _ => true | _ => false).length

theorem batchInsertCount_append (U₁ U₂ : List Update) :
    batchInsertCount (U₁ ++ U₂) = batchInsertCount U₁ + batchInsertCount U₂ := by
  simp [batchInsertCount, List.countP_append]

theorem batchDeleteCount_append (U₁ U₂ : List Update) :
    batchDeleteCount (U₁ ++ U₂) = batchDeleteCount U₁ + batchDeleteCount U₂ := by
  simp [batchDeleteCount, List.filter_append]

theorem batchSplitCount_append (U₁ U₂ : List Update) :
    batchSplitCount (U₁ ++ U₂) = batchSplitCount U₁ + batchSplitCount U₂ := by
  simp [batchSplitCount]

theorem card_E_applyBatch_add_del :
    ∀ (U : List Update) (H : MGraph), H.BatchIsValid U →
      (H.applyBatch U).E.card + batchDeleteCount U = H.E.card + batchInsertCount U
  | [], H, _ => by simp [MGraph.applyBatch, batchDeleteCount, batchInsertCount]
  | u :: U, H, hBV => by
    obtain ⟨hu, hBV'⟩ := hBV
    have ih := card_E_applyBatch_add_del U (H.applyUpdate u) hBV'
    simp only [MGraph.applyBatch, List.foldl_cons] at ih ⊢
    cases u with
    | insert e a b =>
      have he : e ∉ H.E := hu.1
      have h1 : (H.applyUpdate (.insert e a b)).E.card = H.E.card + 1 := by
        simp [MGraph.applyUpdate, Finset.card_insert_of_notMem he]
      have hdel : batchDeleteCount (.insert e a b :: U) = batchDeleteCount U := by
        simp [batchDeleteCount]
      have hins : batchInsertCount (.insert e a b :: U) = batchInsertCount U + 1 := by
        simp [batchInsertCount]
      omega
    | delete e =>
      have he : e ∈ H.E := hu
      have h1 : (H.applyUpdate (.delete e)).E.card + 1 = H.E.card := by
        simp only [MGraph.applyUpdate]
        have := Finset.card_erase_add_one he
        omega
      have hdel : batchDeleteCount (.delete e :: U) = batchDeleteCount U + 1 := by
        simp [batchDeleteCount]
      have hins : batchInsertCount (.delete e :: U) = batchInsertCount U := by
        simp [batchInsertCount]
      omega
    | split v v' St Sh =>
      have h1 : (H.applyUpdate (.split v v' St Sh)).E.card = H.E.card := rfl
      have hdel : batchDeleteCount (.split v v' St Sh :: U) = batchDeleteCount U := by
        simp [batchDeleteCount]
      have hins : batchInsertCount (.split v v' St Sh :: U) = batchInsertCount U := by
        simp [batchInsertCount]
      omega

theorem restrictUpdate_counts (H : MGraph) (u : Update) :
    batchInsertCount (restrictUpdate u H) = 0 ∧
    batchDeleteCount (restrictUpdate u H) ≤ 1 ∧
    batchSplitCount (restrictUpdate u H) ≤ (if isSplit u then 1 else 0) := by
  cases u with
  | insert _ _ _ =>
    simp [restrictUpdate, batchInsertCount, batchDeleteCount, batchSplitCount, isSplit]
  | delete e =>
    by_cases he : e ∈ H.E <;>
      simp [restrictUpdate, he, batchInsertCount, batchDeleteCount, batchSplitCount, isSplit]
  | split _ _ _ _ =>
    simp [restrictUpdate, batchInsertCount, batchDeleteCount, batchSplitCount, isSplit]

theorem piLtFrom_one {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) :
    piLtFrom Pi_level inDom 1 = Pi_level ⟨0, Nat.zero_lt_succ L⟩ := by
  funext e
  have h1 : min 1 (L + 1) = 1 := min_eq_left (Nat.succ_le_succ (Nat.zero_le L))
  have hfind : findEmbLevel inDom 1 e = 0 := by
    unfold findEmbLevel
    rw [h1, List.range_one, List.reverse_singleton]
    simp only [List.find?_singleton]
    split_ifs <;> simp
  unfold piLtFrom
  rw [hfind]
  simp

theorem isEmbedding_congr_eq {G H : MGraph} {emb₁ emb₂ : Embedding}
    (h : ∀ e ∈ G.E, emb₁ e = emb₂ e) :
    Embedding.IsEmbedding emb₁ G H ↔ Embedding.IsEmbedding emb₂ G H := by
  constructor <;> rintro ⟨hV, hW⟩ <;> exact ⟨hV, fun e he => by
    first | (rw [← h e he]; exact hW e he) | (rw [h e he]; exact hW e he)⟩

theorem length_congr_eq {G : MGraph} {emb₁ emb₂ : Embedding}
    (h : ∀ e ∈ G.E, emb₁ e = emb₂ e) :
    Embedding.length emb₁ G = Embedding.length emb₂ G := by
  unfold Embedding.length
  exact Finset.sup_congr rfl fun e he => congrArg List.length (h e he)

theorem vcong_congr_eq {G H : MGraph} {emb₁ emb₂ : Embedding}
    (h : ∀ e ∈ G.E, emb₁ e = emb₂ e) :
    Embedding.vcong emb₁ G H (fun _ => 1) = Embedding.vcong emb₂ G H (fun _ => 1) := by
  unfold Embedding.vcong
  split_ifs with hVne
  · congr 1
    funext v
    unfold Embedding.vcongAt
    congr 1
    exact Finset.filter_congr fun e he => by rw [h e he]
  · rfl

theorem isEmbedding_graph_congr {G H₁ H₂ : MGraph} {emb : Embedding}
    (hV : H₁.V = H₂.V) (hE : H₁.E = H₂.E)
    (ht : ∀ e ∈ H₁.E, H₁.tail e = H₂.tail e)
    (hh : ∀ e ∈ H₁.E, H₁.head e = H₂.head e) :
    Embedding.IsEmbedding emb G H₁ → Embedding.IsEmbedding emb G H₂ := by
  rintro ⟨hGV, hW⟩
  refine ⟨hV ▸ hGV, fun e he => ?_⟩
  have hSub21 : H₂.IsSubgraph H₁ :=
    ⟨hV.subset, hE.subset, fun e' he' => ⟨ht e' he', hh e' he'⟩⟩
  exact IsWalk.of_isSubgraph hSub21 (hW e he)

theorem vcong_graph_congr {G H₁ H₂ : MGraph} {emb : Embedding}
    (hVG : G.IsValid) (hVH₁ : H₁.IsValid)
    (hV : H₁.V = H₂.V) (hE : H₁.E = H₂.E)
    (ht : ∀ e ∈ H₁.E, H₁.tail e = H₂.tail e)
    (hh : ∀ e ∈ H₁.E, H₁.head e = H₂.head e)
    (hEmb : Embedding.IsEmbedding emb G H₁) :
    Embedding.vcong emb G H₁ (fun _ => 1) = Embedding.vcong emb G H₂ (fun _ => 1) := by
  have hSub : H₁.IsSubgraph H₂ :=
    ⟨hV.symm.subset, hE.symm.subset, fun e he => ⟨(ht e (hE ▸ he)).symm, (hh e (hE ▸ he)).symm⟩⟩
  have hEmb2 : Embedding.IsEmbedding emb G H₂ := isEmbedding_graph_congr hV hE ht hh hEmb
  have hVH₂ : H₂.IsValid := fun e he => by
    have he1 : e ∈ H₁.E := hE ▸ he
    obtain ⟨ht1, hh1⟩ := hVH₁ e he1
    exact ⟨hV ▸ (ht e he1) ▸ ht1, hV ▸ (hh e he1) ▸ hh1⟩
  exact vcong_eq_of_isSubgraph hVG hVH₂ hSub hEmb2

theorem unionEdgesLt_mono {L : ℕ} (H_level : Fin (L + 1) → MGraph) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    unionEdgesLt H_level j₁ ⊆ unionEdgesLt H_level j₂ := by
  intro e he
  simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  rcases he with ⟨i, hij, hei⟩
  exact ⟨i, lt_of_lt_of_le hij h, hei⟩

theorem unionEdgesLt_congr {L : ℕ} {H_level : Fin (L + 1) → MGraph} {j₁ j₂ : ℕ}
    (h : j₁ ≤ j₂) (hempty : ∀ i : Fin (L + 1), j₁ ≤ i.1 → i.1 < j₂ → (H_level i).E = ∅) :
    unionEdgesLt H_level j₂ = unionEdgesLt H_level j₁ := by
  apply Finset.Subset.antisymm _ (unionEdgesLt_mono H_level h)
  intro e he
  simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  rcases he with ⟨i, hij, hei⟩
  by_cases hi1 : i.1 < j₁
  · exact ⟨i, hi1, hei⟩
  · exfalso
    rw [hempty i (Nat.le_of_not_lt hi1) hij] at hei
    simp at hei

theorem walkEdges_card_le_length (w : List (ℕ × Bool)) : (walkEdges w).card ≤ w.length := by
  unfold walkEdges
  calc (w.map Prod.fst).toFinset.card
      ≤ (w.map Prod.fst).length := List.toFinset_card_le _
    _ = w.length := List.length_map _

theorem batchIsValid_take :
    ∀ (xs : List Update) (G₀ : MGraph) (k : ℕ),
      G₀.BatchIsValid xs → (∀ u ∈ xs, isDelOrSplit u) →
      G₀.BatchIsValid (xs.take k) ∧ (∀ u ∈ xs.take k, isDelOrSplit u) ∧
      (∀ u, xs[k]? = some u → (G₀.applyBatch (xs.take k)).UpdateIsValid u ∧ isDelOrSplit u)
  | [], G₀, k, _, _ => by
    simp [MGraph.BatchIsValid]
  | x :: xs, G₀, 0, hBV, hds => by
    simp only [List.take_zero, MGraph.BatchIsValid, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, List.getElem?_cons_zero, Option.some.injEq, MGraph.applyBatch, List.foldl_nil,
      true_and]
    intro u hu
    subst hu
    exact ⟨hBV.1, hds x List.mem_cons_self⟩
  | x :: xs, G₀, k + 1, hBV, hds => by
    obtain ⟨hx, hBV'⟩ := hBV
    have hdx := hds x List.mem_cons_self
    have hds' : ∀ y ∈ xs, isDelOrSplit y := fun y hy => hds y (List.mem_cons_of_mem _ hy)
    obtain ⟨h1, h2, h3⟩ := batchIsValid_take xs (G₀.applyUpdate x) k hBV' hds'
    refine ⟨⟨hx, h1⟩, fun y hy => ?_, fun u hu => ?_⟩
    · simp only [List.take_succ_cons, List.mem_cons] at hy
      rcases hy with rfl | hy'
      · exact hdx
      · exact h2 y hy'
    · simpa [List.take_succ_cons, MGraph.applyBatch, List.foldl_cons] using h3 u hu

end

end HelperCongr

section Invariant

@[expose] public section

/-- Complete state invariant for `st = runState (L := L) G₀ q sparsify us k` at timestamp `k ≤ us.length`. -/
structure SnapInv (G₀ : MGraph) (L q mMax : ℕ) (P : SparsifyParams)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) (k : ℕ) : Prop where
  q_eq : (runState (L := L) G₀ q sparsify us k).q = q
  t_eq : (runState (L := L) G₀ q sparsify us k).t = k
  G_eq : (runState (L := L) G₀ q sparsify us k).G = G₀.applyBatch (us.take k)
  H_valid : (runState (L := L) G₀ q sparsify us k).H.IsValid
  H_V : (runState (L := L) G₀ q sparsify us k).H.V = (G₀.applyBatch (us.take k)).V
  H_E : (runState (L := L) G₀ q sparsify us k).H.E =
    unionEdgesLt (runState (L := L) G₀ q sparsify us k).H_level (L + 1)
  H_sub : (G₀.applyBatch (us.take k)).IsSubgraph (runState (L := L) G₀ q sparsify us k).H
  H_level_sub : ∀ i : Fin (L + 1),
    (G₀.applyBatch (us.take k)).IsSubgraph ((runState (L := L) G₀ q sparsify us k).H_level i)
  H_level_V : ∀ i : Fin (L + 1),
    ((runState (L := L) G₀ q sparsify us k).H_level i).V = (G₀.applyBatch (us.take k)).V
  H_level_E : ∀ i : Fin (L + 1),
    ((runState (L := L) G₀ q sparsify us k).H_level i).E =
      ((runState (L := L) G₀ q sparsify us (lastRebuild q L i.1 k)).H_level i).E ∩
      (G₀.applyBatch (us.take k)).E
  Pi_level_eq : ∀ i : Fin (L + 1),
    (runState (L := L) G₀ q sparsify us k).Pi_level i =
      (runState (L := L) G₀ q sparsify us (lastRebuild q L i.1 k)).Pi_level i
  inDom_eq : ∀ i : Fin (L + 1),
    (runState (L := L) G₀ q sparsify us k).inDom i =
      (runState (L := L) G₀ q sparsify us (lastRebuild q L i.1 k)).inDom i ∩
      (G₀.applyBatch (us.take k)).E
  S_level_eq : ∀ i : Fin (L + 1),
    (runState (L := L) G₀ q sparsify us k).S_level i =
      allTouched (G₀.applyBatch (us.take (lastRebuild q L i.1 k)))
        ((us.take k).drop (lastRebuild q L i.1 k))
  inDom0 : (runState (L := L) G₀ q sparsify us k).inDom ⟨0, Nat.zero_lt_succ L⟩ =
    (G₀.applyBatch (us.take k)).E
  inDom_sub : ∀ i : Fin (L + 1),
    (runState (L := L) G₀ q sparsify us k).inDom i ⊆ (G₀.applyBatch (us.take k)).E
  inactive : ∀ i : Fin (L + 1), chooseLevel L q (lastRebuild q L i.1 k) < i.1 →
    (runState (L := L) G₀ q sparsify us k).inDom i = ∅ ∧
    ((runState (L := L) G₀ q sparsify us k).H_level i).E = ∅
  H_level_spars : ∀ i : Fin (L + 1),
    (((runState (L := L) G₀ q sparsify us k).H_level i).m : ℝ) ≤
      P.K_s * ((G₀.applyBatch (us.take k)).n : ℝ) * P.γ_ℓ *
        (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
  emb_at : ∀ i : Fin (L + 1), chooseLevel L q k ≤ i.1 →
    Embedding.IsEmbedding (piLe (runState (L := L) G₀ q sparsify us k) i.1)
      (G₀.applyBatch (us.take k))
      (unionGraphLt (G₀.applyBatch (us.take k))
        (runState (L := L) G₀ q sparsify us k).H_level (i.1 + 1))
  len_at : ∀ i : Fin (L + 1), chooseLevel L q k ≤ i.1 →
    (Embedding.length (piLe (runState (L := L) G₀ q sparsify us k) i.1)
      (G₀.applyBatch (us.take k)) : ℝ) ≤ lenBound P.γ_ℓ i.1
  vcong_at : ∀ i : Fin (L + 1), chooseLevel L q k ≤ i.1 →
    Embedding.vcong (piLe (runState (L := L) G₀ q sparsify us k) i.1)
      (G₀.applyBatch (us.take k))
      (unionGraphLt (G₀.applyBatch (us.take k))
        (runState (L := L) G₀ q sparsify us k).H_level (i.1 + 1))
      (fun _ => 1) ≤ vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1

/-- Operation-count and recourse bounds emitted at single step `k + 1` (`us[k]? = some u`). -/
structure StepCostRecord (G₀ : MGraph) (L q : ℕ) (P : SparsifyParams)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) (k : ℕ) (u : Update) : Prop where
  uh_valid : (runState (L := L) G₀ q sparsify us k).H.BatchIsValid
    (runStepOut (L := L) G₀ q sparsify us k).UH
  uh_apply : (runState (L := L) G₀ q sparsify us k).H.applyBatch
      (runStepOut (L := L) G₀ q sparsify us k).UH =
    (runState (L := L) G₀ q sparsify us (k + 1)).H
  D_sub : (runStepOut (L := L) G₀ q sparsify us k).D ⊆
    (runState (L := L) G₀ q sparsify us (k + 1)).H.E
  uh_len : (runStepOut (L := L) G₀ q sparsify us k).UH.length ≤
    (runState (L := L) G₀ q sparsify us k).G.updateEnc u +
    batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH +
    batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH
  uh_splits : batchSplitCount (runStepOut (L := L) G₀ q sparsify us k).UH ≤
    if isSplit u then 1 else 0
  restart_bounds : chooseLevel L q (k + 1) = 0 →
    let st := runState (L := L) G₀ q sparsify us k
    let res := runStepOut (L := L) G₀ q sparsify us k
    let G' := res.state.G
    (batchInsertCount res.UH : ℝ) ≤ (res.state.H.E.card : ℝ) ∧
    (res.state.H.E.card : ℝ) ≤ P.K_s * ((activeSubgraph G').n : ℝ) * P.γ_ℓ *
      (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s ∧
    (res.D.card : ℝ) = (res.state.H.E.card : ℝ) ∧
    (res.cost : ℝ) ≤ P.K_t * (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) * P.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_t +
      (G'.n : ℝ) + (G'.m : ℝ) + 2 * (res.state.H.E.card : ℝ) + (G'.m : ℝ) * lenBound P.γ_ℓ 0 +
      (L : ℝ) + 1 + ((L : ℝ) + 1) * (st.G.updateEnc u : ℝ) + 2 * (st.H.m : ℝ) +
      (res.UH.length : ℝ) + (res.D.card : ℝ)
  rebuild_bounds : 0 < chooseLevel L q (k + 1) →
    let st := runState (L := L) G₀ q sparsify us k
    let res := runStepOut (L := L) G₀ q sparsify us k
    let G' := res.state.G
    let j := chooseLevel L q (k + 1)
    let sLen := k + 1 - lastRebuild q L (j - 1) (k + 1)
    let eaBound := 2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)
    let Λ_s := (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ_t := (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t
    let jtBound := P.K_s * (2 * eaBound) * P.γ_ℓ * Λ_s
    (batchInsertCount res.UH : ℝ) ≤ jtBound ∧
    (res.D.card : ℝ) ≤ jtBound * (lenBound P.γ_ℓ (j - 1) + 1) ∧
    (res.cost : ℝ) ≤ ((L : ℝ) + 1) * (st.G.updateEnc u : ℝ) + 2 * (sLen : ℝ) + eaBound +
      eaBound * (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) +
      P.K_t * (2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) * Λ_t +
      jtBound + jtBound * (lenBound P.γ_ℓ (j - 1) + 1) +
      (res.UH.length : ℝ) + (res.D.card : ℝ)
  /-- The sizes behind `rebuild_bounds` (step with `0 < j`, proof of Lemma 5.9): `|S_{j-1}| ≤ 2 sLen`,
  `|E_aff| ≤ |S_{j-1}| V_{j-1}`, the old walks have length at most `ℓ_{j-1}`, the size of `J`, the
  validity facts of the call `Sparsify(H_aux, J, Π_{J → H_aux})`, the length of `Π_{J → H_aux}`,
  the fact that `H_aux` is a subgraph of `G'`, the size of `J̃`, the length of the composed walks,
  and the length `ℓ_j` of the new walks. -/
  rebuild_sizes : 0 < chooseLevel L q (k + 1) →
    let st := runState (L := L) G₀ q sparsify us k
    let G' := st.G.applyUpdate u
    let j := chooseLevel L q (k + 1)
    let sLen := k + 1 - lastRebuild q L (j - 1) (k + 1)
    let H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, Nat.lt_succ_of_le (le_trans (Nat.sub_le _ _)
      (chooseLevel_le L q (k + 1)))⟩ ∪ touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    let E_aff := affectedEdges G' H_lt piLt_mid S_prev
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let H_aux := buildAuxHost G' H_lt E_aff
    let embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
    let out := sparsify H_aux J embJH
    let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    let embMid : Embedding := Embedding.comp embJH outEmb
    S_prev.card ≤ 2 * sLen ∧
    (E_aff.card : ℝ) ≤ (S_prev.card : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1) ∧
    (∀ e ∈ G'.E, ((piLt_mid e).length : ℝ) ≤ lenBound P.γ_ℓ (j - 1)) ∧
    J.n ≤ 2 * E_aff.card ∧ J.n ≤ G'.n ∧ G'.m ≤ G₀.m ∧ G'.IsValid ∧
    H_aux.IsValid ∧ J.IsValid ∧ Embedding.IsEmbedding embJH J H_aux ∧ G'.IsSubgraph H_aux ∧
    (E_aff.Nonempty →
      (Embedding.length embJH J : ℝ) ≤ lenBound P.γ_ℓ (j - 1) + 1 ∧
      (out.Jtilde.m : ℝ) ≤ P.K_s * (J.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ∧
      (Embedding.length embMid J : ℝ) ≤ P.γ_ℓ * (Embedding.length embJH J : ℝ) ∧
      ∀ e ∈ E_aff, ((reembedWalk G' H_lt piLt_mid embMid S_prev e).length : ℝ) ≤
        lenBound P.γ_ℓ j)

private theorem log_mono_nm {n₁ n₂ m₁ m₂ : ℕ} (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) (p : ℕ) :
    (1 + Real.log ((n₁ : ℝ) + (m₁ : ℝ) + 2)) ^ p ≤
      (1 + Real.log ((n₂ : ℝ) + (m₂ : ℝ) + 2)) ^ p := by
  have h1 : (1 : ℝ) ≤ (n₁ : ℝ) + (m₁ : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) m₁]
  have hlog1 : 0 ≤ Real.log ((n₁ : ℝ) + (m₁ : ℝ) + 2) := Real.log_nonneg h1
  have harg : (n₁ : ℝ) + (m₁ : ℝ) + 2 ≤ (n₂ : ℝ) + (m₂ : ℝ) + 2 := by gcongr
  have hpos : (0 : ℝ) < (n₁ : ℝ) + (m₁ : ℝ) + 2 := by linarith
  have hlog_le : 1 + Real.log ((n₁ : ℝ) + (m₁ : ℝ) + 2) ≤
      1 + Real.log ((n₂ : ℝ) + (m₂ : ℝ) + 2) := by
    linarith [Real.log_le_log hpos harg]
  exact pow_le_pow_left₀ (by linarith) hlog_le p

theorem initAt_state_props {L q t mMax maxDeg₀ : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hSpec : SparsifySpec mMax P sparsify)
    {G : MGraph} (hVG : G.IsValid) (hGm : G.m ≤ mMax) (hDeg : G.maxDeg ≤ maxDeg₀) :
    let out := initAt G L q t sparsify
    let st := out.state
    st.q = q ∧
    st.t = t ∧
    st.G = G ∧
    st.H.IsValid ∧
    st.H.V = G.V ∧
    st.H.E = unionEdgesLt st.H_level (L + 1) ∧
    G.IsSubgraph st.H ∧
    (∀ i : Fin (L + 1), G.IsSubgraph (st.H_level i)) ∧
    (∀ i : Fin (L + 1), (st.H_level i).V = G.V) ∧
    st.inDom ⟨0, Nat.zero_lt_succ L⟩ = G.E ∧
    (∀ i : Fin (L + 1), st.inDom i ⊆ G.E) ∧
    (∀ i : Fin (L + 1), 0 < i.1 → st.inDom i = ∅ ∧ (st.H_level i).E = ∅) ∧
    (∀ i : Fin (L + 1), ((st.H_level i).m : ℝ) ≤ P.K_s * ((activeSubgraph G).n : ℝ) * P.γ_ℓ *
      (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_s) ∧
    (∀ i : Fin (L + 1), Embedding.IsEmbedding (piLe st i.1) G (unionGraphLt G st.H_level (i.1 + 1))) ∧
    (∀ i : Fin (L + 1), (Embedding.length (piLe st i.1) G : ℝ) ≤ lenBound P.γ_ℓ i.1) ∧
    (∀ i : Fin (L + 1), Embedding.vcong (piLe st i.1) G (unionGraphLt G st.H_level (i.1 + 1)) (fun _ => 1) ≤
      vcongBound P.γ_c P.γ_ℓ maxDeg₀ i.1) ∧
    (out.cost : ℝ) ≤ P.K_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_t +
      (G.n : ℝ) + (G.m : ℝ) + (st.H.m : ℝ) + (G.m : ℝ) * lenBound P.γ_ℓ 0 + (L : ℝ) + 1 := by
  intro out st
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  obtain ⟨hH0_valid, hSub0, hV0, hEmb0, hLen0, hVc0, hSpars0, hCost0⟩ :=
    initCore_spec hSpec hVG hGm
  let core := initCore G sparsify
  have hH_is_core : st.H = core.1 := rfl
  have hHl_eq : ∀ i : Fin (L + 1),
      st.H_level i = if i.1 = 0 then core.1 else emptyGraphOn G := fun _ => rfl
  have hPi_eq : ∀ i : Fin (L + 1),
      st.Pi_level i = if i.1 = 0 then core.2.1 else fun _ => [] := fun _ => rfl
  have hinDom_eq : ∀ i : Fin (L + 1),
      st.inDom i = if i.1 = 0 then G.E else ∅ := fun _ => rfl
  have hUnionE : ∀ {m : ℕ}, 1 ≤ m → unionEdgesLt st.H_level m = core.1.E := by
    intro m hm
    ext e
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, hHl_eq]
    constructor
    · rintro ⟨i, _, hei⟩
      by_cases hi0 : i.1 = 0
      · simp only [hi0, ↓reduceIte] at hei; exact hei
      · simp [hi0, emptyGraphOn] at hei
    · intro he
      exact ⟨⟨0, Nat.zero_lt_succ L⟩, hm, by simpa using he⟩
  have hH_level_sub : ∀ i : Fin (L + 1), G.IsSubgraph (st.H_level i) := by
    intro i
    rw [hHl_eq]
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte]; exact hSub0
    · simp only [hi0, ↓reduceIte]
      exact ⟨Finset.Subset.rfl, Finset.empty_subset _, fun _ h => by simp [emptyGraphOn] at h⟩
  have hH_level_V : ∀ i : Fin (L + 1), (st.H_level i).V = G.V := by
    intro i
    rw [hHl_eq]
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte]; exact hV0
    · simp only [hi0, ↓reduceIte, emptyGraphOn]
  have hinDom_inactive : ∀ i : Fin (L + 1), 0 < i.1 → st.inDom i = ∅ ∧ (st.H_level i).E = ∅ := by
    intro i hi
    have hne : i.1 ≠ 0 := Nat.ne_of_gt hi
    rw [hinDom_eq, hHl_eq]
    simp [hne, emptyGraphOn]
  have hPiLe_eq : ∀ i : Fin (L + 1), ∀ e ∈ G.E, piLe st i.1 e = core.2.1 e := by
    intro i e he
    have he0 : e ∈ st.inDom ⟨0, Nat.zero_lt_succ L⟩ := by rw [hinDom_eq]; simpa using he
    have h1 := piLtFrom_eq_of_lt st.Pi_level st.inDom Nat.one_pos (Nat.succ_le_succ (Nat.zero_le i.1))
      he0 (fun k hk1 _ => (hinDom_inactive k (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)).1 ▸ Finset.notMem_empty _)
    have hpi1 : piLtFrom st.Pi_level st.inDom 1 = core.2.1 := by
      rw [piLtFrom_one, hPi_eq]
      simp
    exact h1.trans (congrFun hpi1 e)
  have hPi_all_emb : ∀ i : Fin (L + 1),
      Embedding.IsEmbedding (piLe st i.1) G (unionGraphLt G st.H_level (i.1 + 1)) := by
    intro i
    have hUE := (hUnionE (Nat.succ_pos i.1)).symm
    have hEmbCore := isEmbedding_graph_congr (G := G) (H₁ := core.1)
      (H₂ := unionGraphLt G st.H_level (i.1 + 1)) hV0 hUE
      (fun e he => (hSub0.2.2 e he).1) (fun e he => (hSub0.2.2 e he).2) hEmb0
    exact (isEmbedding_congr_eq (hPiLe_eq i)).mpr hEmbCore
  have hLen_all : ∀ i : Fin (L + 1), (Embedding.length (piLe st i.1) G : ℝ) ≤ lenBound P.γ_ℓ i.1 := by
    intro i
    rw [length_congr_eq (hPiLe_eq i)]
    exact le_trans hLen0 (lenBound_mono P.hγ_ℓ (Nat.zero_le i.1))
  have hVcong_all : ∀ i : Fin (L + 1),
      Embedding.vcong (piLe st i.1) G (unionGraphLt G st.H_level (i.1 + 1)) (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ maxDeg₀ i.1 := by
    intro i
    rw [vcong_congr_eq (hPiLe_eq i)]
    have hUE := (hUnionE (Nat.succ_pos i.1)).symm
    have hEqVc := vcong_graph_congr (H₂ := unionGraphLt G st.H_level (i.1 + 1))
      hVG hH0_valid hV0 hUE
      (fun e he => (hSub0.2.2 e he).1) (fun e he => (hSub0.2.2 e he).2) hEmb0
    rw [← hEqVc]
    have hdeg_le : vcongBound P.γ_c P.γ_ℓ G.maxDeg 0 ≤ vcongBound P.γ_c P.γ_ℓ maxDeg₀ 0 := by
      unfold vcongBound
      have h3c : 0 ≤ (3 : ℝ) ^ ((0 + 1) * (0 + 2) / 2) * P.γ_ℓ ^ (0 * (0 + 1) / 2) * P.γ_c ^ (0 + 1) := by
        positivity
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hDeg) h3c
    exact le_trans (le_trans hVc0 hdeg_le) (vcongBound_mono P.hγ_c P.hγ_ℓ maxDeg₀ (Nat.zero_le i.1))
  have hSpars_nonneg : 0 ≤ P.K_s * ((activeSubgraph G).n : ℝ) * P.γ_ℓ *
      (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_s := by
    have h1 : (1 : ℝ) ≤ ((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G).n, Nat.cast_nonneg (α := ℝ) G.m]
    have hlog := Real.log_nonneg h1
    exact mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl) (pow_nonneg (by linarith) _)
  refine ⟨rfl, rfl, rfl, hH0_valid, hV0, hUnionE (Nat.zero_lt_succ L) |>.symm, hSub0,
    hH_level_sub, hH_level_V, ?_, ?_, hinDom_inactive, ?_, hPi_all_emb, hLen_all,
    hVcong_all, ?_⟩
  · simp [hinDom_eq]
  · intro i
    rw [hinDom_eq]
    by_cases hi0 : i.1 = 0 <;> simp [hi0]
  · intro i
    rw [hHl_eq]
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte]; exact hSpars0
    · simp only [hi0, ↓reduceIte, emptyGraphOn, MGraph.m, Finset.card_empty, CharP.cast_eq_zero]
      exact hSpars_nonneg
  · have hcost : (out.cost : ℝ) = (core.2.2 : ℝ) + (L : ℝ) + 1 := by
      change ((core.2.2 + L + 1 : ℕ) : ℝ) = (core.2.2 : ℝ) + (L : ℝ) + 1
      push_cast; ring
    have hHm_eq : (st.H.m : ℝ) = (core.1.m : ℝ) := rfl
    linarith [hCost0]

/-- Every embedding walk of `initAt` visits distinct vertices. -/
theorem initAt_nodup {L q t : ℕ} (G : MGraph)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    let st := (initAt G L q t sparsify).state
    ∀ i : Fin (L + 1), ∀ e ∈ G.E,
      ((unionGraphLt G st.H_level (i.1 + 1)).walkVertices (G.tail e) (piLe st i.1 e)).Nodup := by
  intro st i e he
  let core := initCore G sparsify
  have hinDom_eq : ∀ k : Fin (L + 1), st.inDom k = if k.1 = 0 then G.E else ∅ := fun _ => rfl
  have hPi_eq : ∀ k : Fin (L + 1), st.Pi_level k = if k.1 = 0 then core.2.1 else fun _ => [] :=
    fun _ => rfl
  have he0 : e ∈ st.inDom ⟨0, Nat.zero_lt_succ L⟩ := by rw [hinDom_eq]; simpa using he
  have h1 := piLtFrom_eq_of_lt st.Pi_level st.inDom Nat.one_pos (Nat.succ_le_succ (Nat.zero_le i.1))
    he0 (fun k hk1 _ => by
      have hne : k.1 ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
      simp [hinDom_eq, hne])
  have hpi1 : piLtFrom st.Pi_level st.inDom 1 = core.2.1 := by
    rw [piLtFrom_one, hPi_eq]; simp
  have hpi : piLe st i.1 e = core.2.1 e := h1.trans (congrFun hpi1 e)
  have hE : G.E.Nonempty := ⟨e, he⟩
  have ht : (unionGraphLt G st.H_level (i.1 + 1)).tail = core.1.tail := by
    simp [core, initCore, hE, unionGraphLt]
  have hh : (unionGraphLt G st.H_level (i.1 + 1)).head = core.1.head := by
    simp [core, initCore, hE, unionGraphLt]
  rw [hpi, walkVertices_congr_ends ht hh]
  exact initCore_nodup G sparsify e he

theorem init_inv {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hGm₀ : G₀.m ≤ mMax) (hSpec : SparsifySpec mMax P sparsify)
    (us : List Update) :
    SnapInv G₀ L q mMax P sparsify us 0 := by
  have hP := initAt_state_props (L := L) (q := q) (t := 0) hSpec hVG₀ hGm₀ le_rfl
  rcases hP with ⟨hq, ht, hG, hHV, hH_V, hH_E, hH_sub, hHls, hHlV, hin0, hinsub, hinact,
    hHlsp, hemb, hlen, hvc, _⟩
  have hG0 : G₀.applyBatch (us.take 0) = G₀ := by simp [MGraph.applyBatch]
  have hLR : ∀ i : ℕ, lastRebuild q L i 0 = 0 := fun i => by simp [lastRebuild]
  refine ⟨hq, ht, hG0 ▸ hG, hHV, hG0 ▸ hH_V, hH_E, hG0 ▸ hH_sub,
    fun i => hG0 ▸ hHls i, fun i => hG0 ▸ hHlV i, ?_, ?_, ?_, ?_,
    hG0 ▸ hin0, fun i => hG0 ▸ hinsub i, ?_, ?_, fun i _ => hG0 ▸ hemb i,
    fun i _ => hG0 ▸ hlen i, fun i _ => hG0 ▸ hvc i⟩
  · intro i
    rw [hLR i.1, hG0]
    exact (Finset.inter_eq_left.mpr (hHls i).2.1).symm
  · intro i; rw [hLR i.1]
  · intro i
    rw [hLR i.1, hG0]
    exact (Finset.inter_eq_left.mpr (hinsub i)).symm
  · intro i
    simp [runState, init, initAt, hLR i.1, allTouched]
  · intro i hi
    rw [hLR i.1] at hi
    exact hinact i (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
  · intro i
    rw [hG0]
    have hlog := log_mono_nm (activeSubgraph_n_le G₀) (le_refl G₀.m) P.p_s
    have hn : ((activeSubgraph G₀).n : ℝ) ≤ (G₀.n : ℝ) := Nat.cast_le.mpr (activeSubgraph_n_le G₀)
    have h1 : P.K_s * ((activeSubgraph G₀).n : ℝ) * P.γ_ℓ *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
        P.K_s * (G₀.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := by
      have harg1 : (1 : ℝ) ≤ ((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G₀).n, Nat.cast_nonneg (α := ℝ) G₀.m]
      have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
      have hl1 : 0 ≤ (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
        pow_nonneg (by linarith [Real.log_nonneg harg1]) _
      have ha : P.K_s * ((activeSubgraph G₀).n : ℝ) * P.γ_ℓ *
          (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
          P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
          (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn P.hK_s) hγl) hl1
      have hkn : 0 ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ :=
        mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl
      exact le_trans ha (mul_le_mul_of_nonneg_left hlog hkn)
    exact le_trans (hHlsp i) h1


end

end Invariant

end MinCostFlow.DynSpanner
