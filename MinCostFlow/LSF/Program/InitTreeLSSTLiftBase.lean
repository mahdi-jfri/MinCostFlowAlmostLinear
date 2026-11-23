module

public import MinCostFlow.LSF.Program.InitTreeLSSTOps
import MinCostFlow.LSF.Program.Layout
import MinCostFlow.LSF.Theorem22Aux
import MinCostFlow.LSF.ModelWith
import Mathlib.Tactic

/-!
# InitTreeLSSTLift, first part

The first part of `InitTreeLSSTLift.lean`, split off to keep files short. It contains:
- Flat copy enumeration `copyList` and `copyIndexedGraph`
- Non-colliding bridge slots `zeroPositions` and `edgeMult` sum bound
- Vertex + edge isomorphism invariance `isLSST_of_iso`
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow
open MinCostFlow.WideWord
open MinCostFlow.LSF

@[expose] public section

/-! ## Flat copy enumeration `copyList` and `copyIndexedGraph` -/

/-- Explicit flat list of `(origEdge, copySubIdx)` pairs over edges `eList[0 .. m0 - 1]` with
multiplicities `mult 0 .. mult (m0 - 1)`. -/
def copyList (eList : List ℕ) (mult : ℕ → ℕ) (m0 : ℕ) : List (ℕ × ℕ) :=
  (List.range m0).flatMap fun j =>
    (List.range (mult j)).map fun k => (eList.getD j 0, k)

lemma copyList_zero (eList : List ℕ) (mult : ℕ → ℕ) :
    copyList eList mult 0 = [] := by
  simp [copyList]

lemma copyList_succ (eList : List ℕ) (mult : ℕ → ℕ) (m : ℕ) :
    copyList eList mult (m + 1) =
      copyList eList mult m ++ (List.range (mult m)).map fun k => (eList.getD m 0, k) := by
  simp [copyList, List.range_succ, List.flatMap_append]

lemma copyList_length (eList : List ℕ) (mult : ℕ → ℕ) (m0 : ℕ) :
    (copyList eList mult m0).length = (List.map mult (List.range m0)).sum := by
  dsimp only [copyList]
  rw [List.length_flatMap]
  congr 1
  simp [Function.comp_def]

lemma getElem_copyList (eList : List ℕ) (mult : ℕ → ℕ) :
    ∀ {m0 j k : ℕ}, j < m0 → k < mult j →
      ∃ hq : (List.map mult (List.range j)).sum + k < (copyList eList mult m0).length,
        (copyList eList mult m0)[(List.map mult (List.range j)).sum + k]'hq = (eList.getD j 0, k)
  | 0, _, _, hj, _ => by omega
  | m + 1, j, k, hj, hk => by
    have hlt_j : (List.map mult (List.range j)).sum + k < (copyList eList mult (m + 1)).length := by
      rw [copyList_length]
      have hsplit : (List.map mult (List.range (m + 1))).sum =
          (List.map mult (List.range j)).sum + mult j +
            (List.map mult ((List.range (m + 1)).drop (j + 1))).sum := by
        have hdrop : List.range (m + 1) =
            List.range (j + 1) ++ (List.range (m + 1)).drop (j + 1) := by
          conv_lhs => rw [← List.take_append_drop (j + 1) (List.range (m + 1))]
          rw [List.take_range, min_eq_left (by omega : j + 1 ≤ m + 1)]
        conv_lhs => rw [hdrop, List.map_append, List.sum_append, List.range_succ,
          List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
      omega
    refine ⟨hlt_j, ?_⟩
    by_cases hjm : j = m
    · subst j
      have hlen_m : (copyList eList mult m).length = (List.map mult (List.range m)).sum :=
        copyList_length eList mult m
      have hle_m : (copyList eList mult m).length ≤ (List.map mult (List.range m)).sum + k := by omega
      simp only [copyList_succ eList mult m]
      rw [List.getElem_append_right hle_m]
      simp [hlen_m]
    · have hj_m : j < m := by omega
      obtain ⟨hq_m, hget_m⟩ := getElem_copyList eList mult hj_m hk
      simp only [copyList_succ eList mult m]
      rw [List.getElem_append_left hq_m, hget_m]

lemma exists_coords_of_lt_copyList (eList : List ℕ) (mult : ℕ → ℕ) :
    ∀ {m0 q : ℕ}, (hq : q < (copyList eList mult m0).length) →
      ∃ j < m0, ∃ k < mult j,
        q = (List.map mult (List.range j)).sum + k ∧
        (copyList eList mult m0)[q]'hq = (eList.getD j 0, k)
  | 0, _, hq => by simp [copyList] at hq
  | m + 1, q, hq => by
    have hlen_m : (copyList eList mult m).length = (List.map mult (List.range m)).sum :=
      copyList_length eList mult m
    by_cases hqm : q < (copyList eList mult m).length
    · obtain ⟨j, hj, k, hk, hqeq, hget⟩ := exists_coords_of_lt_copyList eList mult hqm
      refine ⟨j, by omega, k, hk, hqeq, ?_⟩
      rw [← hget]
      simp [copyList_succ, List.getElem_append_left hqm]
    · have hqm' : (copyList eList mult m).length ≤ q := Nat.le_of_not_lt hqm
      have hk : q - (List.map mult (List.range m)).sum < mult m := by
        rw [copyList_length, List.range_succ, List.map_append, List.sum_append] at hq
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hq
        omega
      refine ⟨m, Nat.lt_succ_self m, q - (List.map mult (List.range m)).sum, hk, by omega, ?_⟩
      simp only [copyList_succ, List.getElem_append_right hqm', List.getElem_map,
        List.getElem_range, hlen_m]

/-- Pure `IndexedGraph` on `0 .. G₀.n - 1` matching `copyTailPtr` and `copyHeadPtr`. -/
def copyIndexedGraph (G₀ : MGraph) (vList eList : List ℕ) (mult : ℕ → ℕ) : IndexedGraph where
  n := G₀.n
  m := (copyList eList mult G₀.E.card).length
  tail q := vList.idxOf (G₀.tail ((copyList eList mult G₀.E.card).getD q (0, 0)).1)
  head q := vList.idxOf (G₀.head ((copyList eList mult G₀.E.card).getD q (0, 0)).1)

lemma copyIndexedGraph_valid {G₀ : MGraph} {vList eList : List ℕ} {mult : ℕ → ℕ}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hvLen : vList.length = G₀.n) (hvMem : ∀ u, u ∈ vList ↔ u ∈ G₀.V)
    (heLen : eList.length = G₀.E.card) (heMem : ∀ e, e ∈ eList ↔ e ∈ G₀.E) :
    (copyIndexedGraph G₀ vList eList mult).Valid := by
  refine ⟨Finset.card_pos.mpr hV₀, fun q hq => ?_⟩
  obtain ⟨j, hj, _, _, _, hgq⟩ := exists_coords_of_lt_copyList eList mult hq
  have hgD : ((copyList eList mult G₀.E.card).getD q (0, 0)).1 = eList[j]'(by omega) := by
    rw [List.getD_eq_getElem _ _ hq, hgq, List.getD_eq_getElem _ _ (by omega)]
  have hej : eList[j]'(by omega) ∈ G₀.E := (heMem _).mp (List.getElem_mem _)
  have huV : G₀.tail (eList[j]'(by omega)) ∈ vList := (hvMem _).mpr (hG₀ _ hej).1
  have hvV : G₀.head (eList[j]'(by omega)) ∈ vList := (hvMem _).mpr (hG₀ _ hej).2
  dsimp only [copyIndexedGraph]
  rw [hgD]
  exact ⟨(List.idxOf_lt_length_of_mem huV).trans_eq hvLen,
    (List.idxOf_lt_length_of_mem hvV).trans_eq hvLen⟩

/-! ## Non-colliding bridge slots `zeroPositions` and `edgeMult` sum bound -/

/-- Sorted list of offsets `z < ubLen` where `mem (usedBridgePtr + z) = 0`. -/
def zeroPositions (mem : ℕ → ℕ) (usedBridgePtr ubLen : ℕ) : List ℕ :=
  (List.range ubLen).filter fun z => mem (usedBridgePtr + z) == 0

lemma zeroPositions_nodup (mem : ℕ → ℕ) (usedBridgePtr ubLen : ℕ) :
    (zeroPositions mem usedBridgePtr ubLen).Nodup :=
  List.Nodup.filter _ List.nodup_range

lemma mem_zeroPositions_iff {mem : ℕ → ℕ} {usedBridgePtr ubLen z : ℕ} :
    z ∈ zeroPositions mem usedBridgePtr ubLen ↔ z < ubLen ∧ mem (usedBridgePtr + z) = 0 := by
  simp [zeroPositions]

lemma edgeMult_sum_le_two_mul {G₀ : MGraph} {v : ℕ → ℝ} {eList : List ℕ}
    (hv : ∀ e ∈ G₀.E, 0 < v e)
    (heLen : eList.length = G₀.E.card) (heNd : eList.Nodup) (heMem : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    {mult : ℕ → ℕ} (hmult : ∀ j < G₀.E.card, mult j = edgeMult G₀ v (eList.getD j 0)) :
    (List.map mult (List.range G₀.E.card)).sum ≤ 2 * G₀.E.card := by
  by_cases hm0 : G₀.E.card = 0
  · simp [hm0]
  · have hmPos : 0 < G₀.E.card := Nat.pos_of_ne_zero hm0
    have hEne : G₀.E.Nonempty := Finset.card_pos.mp hmPos
    have hnorm_eq : G₀.norm1 v = ∑ e ∈ G₀.E, v e := norm1_eq_sum_pos hv
    have hnorm_pos : 0 < G₀.norm1 v := by
      rw [hnorm_eq]
      exact Finset.sum_pos hv hEne
    have hlist_sum : (List.map mult (List.range G₀.E.card)).sum = ∑ e ∈ G₀.E, edgeMult G₀ v e := by
      have hmap : List.map mult (List.range G₀.E.card) = eList.map (edgeMult G₀ v) := by
        refine List.ext_getElem (by simp [heLen]) fun j hj1 hj2 => ?_
        have hj : j < G₀.E.card := by simpa using hj1
        simp only [List.getElem_map, List.getElem_range]
        rw [hmult j hj, List.getD_eq_getElem _ _ (by omega)]
      rw [hmap]
      have hsub : G₀.E = eList.toFinset := by
        ext e; exact (heMem e).symm.trans List.mem_toFinset.symm
      rw [hsub, List.sum_toFinset (edgeMult G₀ v) heNd]
    rw [hlist_sum]
    have hreal : ((∑ e ∈ G₀.E, edgeMult G₀ v e : ℕ) : ℝ) ≤ (2 * G₀.E.card : ℕ) := by
      rw [Nat.cast_sum]
      have hceil : ∀ e ∈ G₀.E,
          (edgeMult G₀ v e : ℝ) ≤ (G₀.E.card : ℝ) * v e / G₀.norm1 v + 1 := by
        intro e he
        have hlt := Nat.ceil_lt_add_one (a := (G₀.E.card : ℝ) * v e / G₀.norm1 v)
          (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hv e he).le) hnorm_pos.le)
        exact hlt.le
      calc ∑ e ∈ G₀.E, (edgeMult G₀ v e : ℝ)
          ≤ ∑ e ∈ G₀.E, ((G₀.E.card : ℝ) * v e / G₀.norm1 v + 1) := Finset.sum_le_sum hceil
        _ = (G₀.E.card : ℝ) / G₀.norm1 v * (∑ e ∈ G₀.E, v e) + (G₀.E.card : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => by ring
        _ = (G₀.E.card : ℝ) + (G₀.E.card : ℝ) := by
            rw [← hnorm_eq]
            field_simp [hnorm_pos.ne']
        _ = ((2 * G₀.E.card : ℕ) : ℝ) := by push_cast; ring
    exact_mod_cast hreal

lemma zeroPositions_card_ge {G₀ : MGraph} {eList : List ℕ} {mult : ℕ → ℕ}
    {mem : ℕ → ℕ} {usedBridgePtr eCap : ℕ}
    (hsum_le : (List.map mult (List.range G₀.E.card)).sum ≤ 2 * G₀.E.card)
    (hmark : ∀ z < 2 * G₀.E.card + G₀.n,
      (mem (usedBridgePtr + z) = 1 ↔
        ∃ j' < G₀.E.card, ∃ k < mult j', eList.getD j' 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (mem (usedBridgePtr + z) = 0 ∨ mem (usedBridgePtr + z) = 1)) :
    G₀.n ≤ (zeroPositions mem usedBridgePtr (2 * G₀.E.card + G₀.n)).length := by
  classical
  let ubLen := 2 * G₀.E.card + G₀.n
  let F0 := (Finset.range ubLen).filter fun z => mem (usedBridgePtr + z) = 0
  let F1 := (Finset.range ubLen).filter fun z => mem (usedBridgePtr + z) = 1
  have hz_card : (zeroPositions mem usedBridgePtr ubLen).length = F0.card := by
    dsimp only [zeroPositions, F0]
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)]
    congr 1
    ext z
    simp
  have hpart : F0.card + F1.card = ubLen := by
    have hdisj : Disjoint F0 F1 := by
      rw [Finset.disjoint_left]
      intro z hz0 hz1
      dsimp only [F0] at hz0
      dsimp only [F1] at hz1
      rw [Finset.mem_filter] at hz0 hz1
      omega
    have hun : F0 ∪ F1 = Finset.range ubLen := by
      ext z
      simp only [F0, F1, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        rcases (hmark z hz).2 with h0 | h1
        · exact Or.inl ⟨hz, h0⟩
        · exact Or.inr ⟨hz, h1⟩
    rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_range]
  let S : Finset (Σ _ : ℕ, ℕ) := (Finset.range G₀.E.card).sigma fun j => Finset.range (mult j)
  let g : (Σ _ : ℕ, ℕ) → ℕ := fun p => (eList.getD p.1 0 + copyMod G₀ * (p.2 + 1)) - eCap
  have hS_card : S.card = (List.map mult (List.range G₀.E.card)).sum := by
    dsimp only [S]
    rw [Finset.card_sigma]
    simp only [Finset.card_range]
    induction G₀.E.card with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append]
      simp [ih]
  have hF1_sub : F1 ⊆ S.image g := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨j, hj, k, hk, heq⟩ := (hmark z hz.1).1.mp hz.2
    rw [Finset.mem_image]
    refine ⟨⟨j, k⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩, ?_⟩
    dsimp only [g]
    omega
  have hF1_le : F1.card ≤ 2 * G₀.E.card :=
    (Finset.card_le_card hF1_sub).trans (Finset.card_image_le.trans (hS_card ▸ hsum_le))
  rw [hz_card]
  omega

/-! ## Vertex + edge isomorphism invariance `isLSST_of_iso` -/

private lemma isWalk_map_iso {T₁ T₂ : MGraph} {σV σE : ℕ → ℕ}
    (hmem : ∀ f ∈ T₁.E, σE f ∈ T₂.E)
    (hend : ∀ f ∈ T₁.E, T₂.tail (σE f) = σV (T₁.tail f) ∧ T₂.head (σE f) = σV (T₁.head f)) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, T₁.IsWalk u v P →
      T₂.IsWalk (σV u) (σV v) (P.map fun x => (σE x.1, x.2)) := by
  intro u v P hP
  induction hP with
  | nil s => exact .nil (σV s)
  | @cons s _ x xs hxE hsrc _ ih =>
    have hm := hend x.1 hxE
    have hsrc' : T₂.src (σE x.1, x.2) = σV s := by
      cases hx2 : x.2 <;> simp only [MGraph.src, hx2, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
      · rw [hm.2, hsrc]
      · rw [hm.1, hsrc]
    have hdst' : T₂.dst (σE x.1, x.2) = σV (T₁.dst x) := by
      cases hx2 : x.2 <;> simp only [MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte]
      · exact hm.1
      · exact hm.2
    exact .cons (hmem x.1 hxE) hsrc' (hdst'.symm ▸ ih)

private lemma isWalk_unmap_iso {G₁ G₂ T₁ T₂ : MGraph} {σV σV_inv σE σE_inv : ℕ → ℕ}
    (hV₁ : T₁.V = G₁.V) (hV₂ : T₂.V = G₂.V)
    (hT₁ : T₁.IsValid) (hT₂ : T₂.IsValid)
    (hσV_inv : ∀ y ∈ G₂.V, σV_inv y ∈ G₁.V ∧ σV (σV_inv y) = y)
    (hend : ∀ f ∈ T₁.E, T₂.tail (σE f) = σV (T₁.tail f) ∧ T₂.head (σE f) = σV (T₁.head f))
    (hσV_mem : ∀ x ∈ G₁.V, σV x ∈ G₂.V ∧ σV_inv (σV x) = x)
    (hσE_Tinv : ∀ f' ∈ T₂.E, σE_inv f' ∈ T₁.E ∧ σE (σE_inv f') = f') :
    ∀ {u v : ℕ} {Q : List (ℕ × Bool)}, u ∈ T₂.V → T₂.IsWalk u v Q →
      T₁.IsWalk (σV_inv u) (σV_inv v) (Q.map fun x => (σE_inv x.1, x.2)) := by
  intro u v Q hu hQ
  induction hQ with
  | nil s => exact .nil (σV_inv s)
  | @cons s _ y ys hyE hsrc hrest ih =>
    have hf := hσE_Tinv y.1 hyE
    have hm := hend (σE_inv y.1) hf.1
    rw [hf.2] at hm
    have hv1 := hT₁ _ hf.1
    rw [hV₁] at hv1
    have htail_in : T₁.tail (σE_inv y.1) ∈ G₁.V := hv1.1
    have hhead_in : T₁.head (σE_inv y.1) ∈ G₁.V := hv1.2
    have hm_inv : σV_inv (T₂.tail y.1) = T₁.tail (σE_inv y.1) ∧
        σV_inv (T₂.head y.1) = T₁.head (σE_inv y.1) := by
      refine ⟨?_, ?_⟩
      · rw [hm.1]; exact (hσV_mem _ htail_in).2
      · rw [hm.2]; exact (hσV_mem _ hhead_in).2
    have hsrc' : T₁.src (σE_inv y.1, y.2) = σV_inv s := by
      cases hy2 : y.2 <;> simp only [MGraph.src, hy2, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
      · rw [← hsrc, hm_inv.2]
      · rw [← hsrc, hm_inv.1]
    have hdst' : T₁.dst (σE_inv y.1, y.2) = σV_inv (T₂.dst y) := by
      cases hy2 : y.2 <;> simp only [MGraph.dst, hy2, Bool.false_eq_true, ↓reduceIte]
      · exact hm_inv.1.symm
      · exact hm_inv.2.symm
    have hdst_V : T₂.dst y ∈ T₂.V := by
      cases hy2 : y.2 <;> simp only [MGraph.dst, hy2, Bool.false_eq_true, ↓reduceIte]
      · exact (hT₂ _ hyE).1
      · exact (hT₂ _ hyE).2
    exact .cons hf.1 hsrc' (hdst'.symm ▸ ih hdst_V)

private lemma walkVertices_map_iso {T₁ T₂ : MGraph} {σV σE : ℕ → ℕ}
    (hend : ∀ f ∈ T₁.E, T₂.tail (σE f) = σV (T₁.tail f) ∧ T₂.head (σE f) = σV (T₁.head f)) :
    ∀ {u : ℕ} {P : List (ℕ × Bool)}, (∀ x ∈ P, x.1 ∈ T₁.E) →
      T₂.walkVertices (σV u) (P.map fun x => (σE x.1, x.2)) = (T₁.walkVertices u P).map σV
  | u, [], _ => by simp [MGraph.walkVertices]
  | u, x :: xs, hx => by
    have hxE : x.1 ∈ T₁.E := hx x (by simp)
    have hm := hend x.1 hxE
    have hdst : T₂.dst (σE x.1, x.2) = σV (T₁.dst x) := by
      cases hx2 : x.2 <;> simp only [MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte]
      · exact hm.1
      · exact hm.2
    rw [List.map_cons, walkVertices_cons, walkVertices_cons, List.map_cons, hdst]
    congr 1
    exact walkVertices_map_iso hend fun y hy => hx y (by simp [hy])

private lemma walkVertices_mem_V {T : MGraph} (hT : T.IsValid) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, u ∈ T.V → T.IsWalk u v P →
      ∀ w ∈ T.walkVertices u P, w ∈ T.V
  | _, _, _, hu, .nil _, w, hw => by
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw
    exact hw ▸ hu
  | _, _, x :: xs, hu, .cons hxE _ hrest, w, hw => by
    rw [walkVertices_cons, List.mem_cons] at hw
    rcases hw with rfl | hmem
    · exact hu
    · have hdst : T.dst x ∈ T.V := by
        cases hx2 : x.2 <;> simp only [MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte]
        · exact (hT _ hxE).1
        · exact (hT _ hxE).2
      exact walkVertices_mem_V hT hdst hrest w hmem

/-- `IsLSST` transfers across an isomorphism `(σV, σE)` between `(G₁, T₁)` and `(G₂, T₂)`. -/
theorem isLSST_of_iso {G₁ G₂ T₁ T₂ : MGraph} {ℓ₁ ℓ₂ v₁ v₂ : ℕ → ℝ} {γ : ℝ}
    {σV σV_inv σE σE_inv : ℕ → ℕ}
    (hV₁ : T₁.V = G₁.V) (hV₂ : T₂.V = G₂.V)
    (hG₁ : G₁.IsValid) (hG₂ : G₂.IsValid)
    (hT₁ : T₁.IsValid) (hT₂ : T₂.IsValid)
    (hσV_mem : ∀ x ∈ G₁.V, σV x ∈ G₂.V ∧ σV_inv (σV x) = x)
    (hσV_inv : ∀ y ∈ G₂.V, σV_inv y ∈ G₁.V ∧ σV (σV_inv y) = y)
    (hσE_G : ∀ e ∈ G₁.E, σE e ∈ G₂.E ∧ σE_inv (σE e) = e ∧
      G₂.tail (σE e) = σV (G₁.tail e) ∧ G₂.head (σE e) = σV (G₁.head e) ∧
      ℓ₂ (σE e) = ℓ₁ e ∧ v₂ (σE e) = v₁ e)
    (hσE_Ginv : ∀ e' ∈ G₂.E, σE_inv e' ∈ G₁.E ∧ σE (σE_inv e') = e')
    (hσE_T : ∀ f ∈ T₁.E, σE f ∈ T₂.E ∧ σE_inv (σE f) = f ∧
      T₂.tail (σE f) = σV (T₁.tail f) ∧ T₂.head (σE f) = σV (T₁.head f) ∧
      (f ∈ G₁.E ↔ σE f ∈ G₂.E))
    (hσE_Tinv : ∀ f' ∈ T₂.E, σE_inv f' ∈ T₁.E ∧ σE (σE_inv f') = f')
    (hT₁_lsst : IsLSST G₁ ℓ₁ v₁ γ T₁) :
    IsLSST G₂ ℓ₂ v₂ γ T₂ := by
  rcases hT₁_lsst with ⟨hT₁_st, hT₁_G, hT₁_paths, hT₁_sum⟩
  have hendT : ∀ f ∈ T₁.E, T₂.tail (σE f) = σV (T₁.tail f) ∧ T₂.head (σE f) = σV (T₁.head f) :=
    fun f hf => ⟨(hσE_T f hf).2.2.1, (hσE_T f hf).2.2.2.1⟩
  have hT₂_forest : T₂.IsForest := by
    refine ⟨hT₂, fun Q hQ => ?_⟩
    rcases hQ with ⟨hQne, hQnd, y, hWy⟩
    cases Q with
    | nil => exact hQne rfl
    | cons x xs =>
      have hyV : y ∈ T₂.V := by
        cases hWy with
        | cons hxE hsrc _ =>
          rw [← hsrc]
          cases hx2 : x.2 <;> simp only [MGraph.src, hx2, Bool.false_eq_true, ↓reduceIte]
          · exact (hT₂ _ hxE).2
          · exact (hT₂ _ hxE).1
      have hWp := isWalk_unmap_iso hV₁ hV₂ hT₁ hT₂ hσV_inv hendT hσV_mem hσE_Tinv hyV hWy
      have hPnd : (((x :: xs).map fun z => (σE_inv z.1, z.2)).map Prod.fst).Nodup := by
        rw [List.map_map]
        have hcomp : (Prod.fst ∘ fun z : ℕ × Bool => (σE_inv z.1, z.2)) = σE_inv ∘ Prod.fst := rfl
        rw [hcomp, ← List.map_map]
        refine hQnd.map_on fun a ha b hb hab => ?_
        obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp ha
        obtain ⟨f₂, hf₂, rfl⟩ := List.mem_map.mp hb
        have hf₁E : f₁.1 ∈ T₂.E := IsWalk_edges_mem hWy hf₁
        have hf₂E : f₂.1 ∈ T₂.E := IsWalk_edges_mem hWy hf₂
        have h1 := (hσE_Tinv _ hf₁E).2
        have h2 := (hσE_Tinv _ hf₂E).2
        rw [hab] at h1
        exact h1.symm.trans h2
      exact hT₁_st.1.2 _ ⟨by simp, hPnd, σV_inv y, hWp⟩
  have hT₂_conn : ∀ u ∈ G₂.V, ∀ v ∈ G₂.V, T₂.Connected u v := by
    intro u hu v hv
    obtain ⟨hu1, huEq⟩ := hσV_inv u hu
    obtain ⟨hv1, hvEq⟩ := hσV_inv v hv
    obtain ⟨P, hP⟩ := hT₁_st.2.2 _ hu1 _ hv1
    refine ⟨P.map fun x => (σE x.1, x.2), ?_⟩
    have hW := isWalk_map_iso (fun f hf => (hσE_T f hf).1) hendT hP
    rwa [huEq, hvEq] at hW
  have hT₂_st : T₂.IsSpanningTreeOn G₂.V := ⟨hT₂_forest, hV₂, hT₂_conn⟩
  have hT₂_G : ∀ e' ∈ T₂.E, e' ∈ G₂.E → T₂.tail e' = G₂.tail e' ∧ T₂.head e' = G₂.head e' := by
    intro e' he'T he'G
    obtain ⟨heT₁, heEq⟩ := hσE_Tinv e' he'T
    have heG₁ : σE_inv e' ∈ G₁.E := (hσE_T _ heT₁).2.2.2.2.mpr (heEq.symm ▸ he'G)
    have h1 := hT₁_G _ heT₁ heG₁
    have htT := hendT _ heT₁
    have hG := hσE_G _ heG₁
    rw [heEq] at htT
    rw [heEq] at hG
    exact ⟨htT.1.trans (congrArg σV h1.1 |>.trans hG.2.2.1.symm),
      htT.2.trans (congrArg σV h1.2 |>.trans hG.2.2.2.1.symm)⟩
  have hpath_map : ∀ e' ∈ G₂.E,
      T₂.forestPath (G₂.tail e') (G₂.head e') =
        (T₁.forestPath (G₁.tail (σE_inv e')) (G₁.head (σE_inv e'))).map fun x => (σE x.1, x.2) := by
    intro e' he'G
    obtain ⟨heG₁, heEq⟩ := hσE_Ginv e' he'G
    have hG₁_e := hσE_G _ heG₁
    rw [heEq] at hG₁_e
    let e := σE_inv e'
    let P := T₁.forestPath (G₁.tail e) (G₁.head e)
    have hev := hG₁ _ heG₁
    have hP_path : T₁.IsPath (G₁.tail e) (G₁.head e) P :=
      forestPath_isPath hT₁_st.1 (hT₁_st.2.2 _ hev.1 _ hev.2)
    let P' := P.map fun x => (σE x.1, x.2)
    have hP_edges : ∀ x ∈ P, x.1 ∈ T₁.E := fun x hx => IsWalk_edges_mem hP_path.1 hx
    have hP'_walk : T₂.IsWalk (G₂.tail e') (G₂.head e') P' := by
      rw [hG₁_e.2.2.1, hG₁_e.2.2.2.1]
      exact isWalk_map_iso (fun f hf => (hσE_T f hf).1) hendT hP_path.1
    have hP'_nd : (T₂.walkVertices (G₂.tail e') P').Nodup := by
      rw [hG₁_e.2.2.1, walkVertices_map_iso hendT hP_edges]
      refine hP_path.2.map_on fun a ha b hb hab => ?_
      have haV : a ∈ G₁.V := hV₁ ▸ walkVertices_mem_V hT₁ (hV₁.symm ▸ hev.1) hP_path.1 a ha
      have hbV : b ∈ G₁.V := hV₁ ▸ walkVertices_mem_V hT₁ (hV₁.symm ▸ hev.1) hP_path.1 b hb
      have h1 := (hσV_mem a haV).2
      have h2 := (hσV_mem b hbV).2
      rw [hab] at h1
      exact h1.symm.trans h2
    exact forestPath_eq_of_isPath hT₂_forest ⟨hP'_walk, hP'_nd⟩
  have hT₂_paths : ∀ e' ∈ G₂.E, ∀ f' ∈ walkEdges (T₂.forestPath (G₂.tail e') (G₂.head e')), f' ∈ G₂.E := by
    intro e' he'G f' hf'
    rw [hpath_map e' he'G, mem_walkEdges_iff] at hf'
    obtain ⟨b, hb⟩ := hf'
    rw [List.mem_map] at hb
    rcases hb with ⟨x, hxP, hxEq⟩
    have hxEq1 : σE x.1 = f' := congrArg Prod.fst hxEq
    have heG₁ := (hσE_Ginv e' he'G).1
    have hxG₁ : x.1 ∈ G₁.E := hT₁_paths _ heG₁ x.1 (mem_walkEdges_iff.mpr ⟨x.2, hxP⟩)
    exact hxEq1 ▸ (hσE_G _ hxG₁).1
  have hstr_eq : ∀ e' ∈ G₂.E,
      treeStretch G₂ T₂ ℓ₂ e' = treeStretch G₁ T₁ ℓ₁ (σE_inv e') := by
    intro e' he'G
    obtain ⟨heG₁, heEq⟩ := hσE_Ginv e' he'G
    have hev := hG₁ _ heG₁
    let P := T₁.forestPath (G₁.tail (σE_inv e')) (G₁.head (σE_inv e'))
    have hP_path : T₁.IsPath (G₁.tail (σE_inv e')) (G₁.head (σE_inv e')) P :=
      forestPath_isPath hT₁_st.1 (hT₁_st.2.2 _ hev.1 _ hev.2)
    have hP'_path : T₂.IsPath (G₂.tail e') (G₂.head e') (T₂.forestPath (G₂.tail e') (G₂.head e')) := by
      have hev2 := hG₂ _ he'G
      exact forestPath_isPath hT₂_st.1 (hT₂_st.2.2 _ (hV₂ ▸ hev2.1) _ (hV₂ ▸ hev2.2))
    have hwl₂ := walkLength_eq_sum_of_isPath ℓ₂ hP'_path
    have hwl₁ := walkLength_eq_sum_of_isPath ℓ₁ hP_path
    have hmap_we : walkEdges (T₂.forestPath (G₂.tail e') (G₂.head e')) =
        (walkEdges P).image σE := by
      ext f'
      simp only [hpath_map e' he'G, mem_walkEdges_iff, Finset.mem_image, List.mem_map]
      constructor
      · rintro ⟨b, ⟨x, hxP, hxEq⟩⟩
        exact ⟨x.1, ⟨x.2, hxP⟩, congrArg Prod.fst hxEq⟩
      · rintro ⟨f, ⟨b, hxP⟩, rfl⟩
        exact ⟨b, ⟨(f, b), hxP, rfl⟩⟩
    have hsum_wl : walkLength ℓ₂ (T₂.forestPath (G₂.tail e') (G₂.head e')) = walkLength ℓ₁ P := by
      rw [hwl₂, hwl₁, hmap_we, Finset.sum_image]
      · refine Finset.sum_congr rfl fun f hf => ?_
        exact (hσE_G f (hT₁_paths _ heG₁ _ hf)).2.2.2.2.1
      · intro f₁ hf₁ f₂ hf₂ heq
        have hf₁G := hT₁_paths _ heG₁ _ (Finset.mem_coe.mp hf₁)
        have hf₂G := hT₁_paths _ heG₁ _ (Finset.mem_coe.mp hf₂)
        have h1 := (hσE_G f₁ hf₁G).2.1
        have h2 := (hσE_G f₂ hf₂G).2.1
        rw [heq] at h1
        exact h1.symm.trans h2
    have hℓ_eq : ℓ₂ e' = ℓ₁ (σE_inv e') := by
      have h := (hσE_G _ heG₁).2.2.2.2.1
      rwa [heEq] at h
    dsimp only [treeStretch]
    rw [hsum_wl, hℓ_eq]
  have hnorm_eq : G₂.norm1 v₂ = G₁.norm1 v₁ := by
    dsimp only [MGraph.norm1]
    symm
    refine Finset.sum_bij' (fun e _ => σE e) (fun e' _ => σE_inv e')
      (fun e he => (hσE_G e he).1) (fun e' he' => (hσE_Ginv e' he').1)
      (fun e he => (hσE_G e he).2.1) (fun e' he' => (hσE_Ginv e' he').2)
      (fun e he => by rw [(hσE_G e he).2.2.2.2.2])
  have hsum_stretch : ∑ e' ∈ G₂.E, v₂ e' * treeStretch G₂ T₂ ℓ₂ e' =
      ∑ e ∈ G₁.E, v₁ e * treeStretch G₁ T₁ ℓ₁ e := by
    symm
    refine Finset.sum_bij' (fun e _ => σE e) (fun e' _ => σE_inv e')
      (fun e he => (hσE_G e he).1) (fun e' he' => (hσE_Ginv e' he').1)
      (fun e he => (hσE_G e he).2.1) (fun e' he' => (hσE_Ginv e' he').2)
      (fun e he => ?_)
    have hmem2 := (hσE_G e he).1
    have hinv := (hσE_G e he).2.1
    have hv_eq := (hσE_G e he).2.2.2.2.2
    rw [hv_eq, hstr_eq _ hmem2, hinv]
  refine ⟨hT₂_st, hT₂_G, hT₂_paths, ?_⟩
  rw [hsum_stretch, hnorm_eq]
  exact hT₁_sum


end

end MinCostFlow.LSF.Program
