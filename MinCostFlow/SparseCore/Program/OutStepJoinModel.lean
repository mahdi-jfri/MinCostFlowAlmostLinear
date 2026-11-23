module

public import MinCostFlow.SparseCore.Program.OutStepSplitModel
public import MinCostFlow.SparseCore.Program.OutStepRotW

/-!
# The model side of the output step

The run lemmas of the six phases of the output step speak about the lists that the program
reads (the leaving edges `delL`, the splits `P`, the entering edges `insL`) and about the answers
of the tour. The statement of the step speaks about the model: the output batch `U_S`, the new
output graph and the edits `outStepEditsSmall`. This file proves the facts that tie the two.

* **Lists and graphs.** Inserting a list of new edges sets their ends
  (`applyBatch_inserts_ends`). A list of splits keeps the edges, adds one vertex per split
  (`card_applyBatch_splits_V`), and has encoding size between its length and its length times
  `2 |E| + 1` (`outLength_le_batchEnc`, `batchEnc_splits_le`). The edits of the splits have the
  same encoding size as the splits (`ordEditsEnc_outPrefixEditsOn_eq`).
* **The tour answers of the insertions.** When the marked ends are the ends of the kept edges and
  of the edges inserted so far, the places that `nextMarked` gives are the places of
  `outInsertEdits` (`insEditsTour_eq`), and the marks at the end are the ends of the new output
  graph.
* **The model of a step.** The output batch is the deletions, the restricted core splits and the
  insertions (`outStep_batch_eq`), the graph after the deletions has the kept edges
  (`outStep_G₁_E`), the entering edges end at the new roots (`outStep_ins_ends`), and each end of
  a new output edge is in the core list of its vertex (`outStep_cord_mem`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-! ## Insertions -/

private theorem applyBatch_inserts_not_mem (t h : ℕ → ℕ) {e : ℕ} :
    ∀ (L : List ℕ) (G : MGraph), e ∉ L →
      (G.applyBatch (L.map fun f => Update.insert f (t f) (h f))).tail e = G.tail e ∧
        (G.applyBatch (L.map fun f => Update.insert f (t f) (h f))).head e = G.head e
  | [], _, _ => ⟨rfl, rfl⟩
  | f :: L, G, he => by
    have hf : e ≠ f := fun h' => he (h' ▸ List.mem_cons_self)
    obtain ⟨h1, h2⟩ := applyBatch_inserts_not_mem t h L (G.applyUpdate (.insert f (t f) (h f)))
      (fun h' => he (List.mem_cons_of_mem _ h'))
    refine ⟨?_, ?_⟩
    · show ((G.applyUpdate (.insert f (t f) (h f))).applyBatch _).tail e = _
      rw [h1]; simp [MGraph.applyUpdate, Function.update_of_ne hf]
    · show ((G.applyUpdate (.insert f (t f) (h f))).applyBatch _).head e = _
      rw [h2]; simp [MGraph.applyUpdate, Function.update_of_ne hf]

/-- Inserting the edges of a list without repeats sets the ends of each of them. -/
theorem applyBatch_inserts_ends (t h : ℕ → ℕ) :
    ∀ (L : List ℕ) (G : MGraph), L.Nodup → ∀ e ∈ L,
      (G.applyBatch (L.map fun f => Update.insert f (t f) (h f))).tail e = t e ∧
        (G.applyBatch (L.map fun f => Update.insert f (t f) (h f))).head e = h e
  | [], _, _, e, he => absurd he List.not_mem_nil
  | f :: L, G, hnd, e, he => by
    obtain ⟨hfL, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp he with rfl | he'
    · obtain ⟨h1, h2⟩ := applyBatch_inserts_not_mem t h L (G.applyUpdate (.insert e (t e) (h e)))
        hfL
      refine ⟨?_, ?_⟩
      · show ((G.applyUpdate (.insert e (t e) (h e))).applyBatch _).tail e = _
        rw [h1]; simp [MGraph.applyUpdate]
      · show ((G.applyUpdate (.insert e (t e) (h e))).applyBatch _).head e = _
        rw [h2]; simp [MGraph.applyUpdate]
    · exact applyBatch_inserts_ends t h L _ hnd' e he'

/-- A valid batch: each update is valid on the graph after the updates before it. -/
theorem outBatchIsValid_get : ∀ {G : MGraph} (W : List Update), G.BatchIsValid W →
    ∀ j (hj : j < W.length), (G.applyBatch (W.take j)).UpdateIsValid W[j]
  | _, [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _, _ :: _, hv, 0, _ => hv.1
  | G, u :: W, hv, j + 1, hj => outBatchIsValid_get (G := G.applyUpdate u) W hv.2 j
      (by simpa using hj)

/-! ## Splits -/

/-- Every update of a restricted core batch is a split. -/
theorem restrictSplits_isSplit (keep : Finset ℕ) :
    ∀ (UC : List Update), ∀ u ∈ restrictSplits keep UC, ∃ v v' St Sh, u = .split v v' St Sh
  | [] => by simp [restrictSplits]
  | .split v v' St Sh :: UC => by
    intro u hu
    simp only [restrictSplits, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨_, _, _, _, rfl⟩
    · exact restrictSplits_isSplit keep UC u hu
  | .insert .. :: UC => restrictSplits_isSplit keep UC
  | .delete _ :: UC => restrictSplits_isSplit keep UC

/-- Splits keep the edges. -/
theorem applyBatch_splits_E : ∀ (P : List Update) (G : MGraph),
    (∀ u ∈ P, ∃ v v' St Sh, u = .split v v' St Sh) → (G.applyBatch P).E = G.E
  | [], _, _ => rfl
  | u :: P, G, hP => by
    obtain ⟨v, v', St, Sh, rfl⟩ := hP u List.mem_cons_self
    exact applyBatch_splits_E P (G.applyUpdate (.split v v' St Sh))
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))

/-- The new vertex of a split of a valid batch is a vertex at the end of the batch. -/
theorem mem_applyBatch_V_of_split : ∀ (W : List Update) (G : MGraph), G.BatchIsValid W →
    ∀ v v' St Sh, Update.split v v' St Sh ∈ W → v' ∈ (G.applyBatch W).V
  | [], _, _, _, _, _, _, hu => absurd hu List.not_mem_nil
  | u :: W, G, hv, v, v', St, Sh, hu => by
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact V_subset_applyBatch (G.applyUpdate (.split v v' St Sh)) W
        (Finset.mem_insert_self _ _)
    · exact mem_applyBatch_V_of_split W (G.applyUpdate u) hv.2 v v' St Sh hu'

/-- A valid list of splits adds one new vertex per split. -/
theorem card_applyBatch_splits_V : ∀ (P : List Update) (G : MGraph), G.BatchIsValid P →
    (∀ u ∈ P, ∃ v v' St Sh, u = .split v v' St Sh) →
    (G.applyBatch P).V.card = G.V.card + P.length
  | [], _, _, _ => rfl
  | u :: P, G, hv, hP => by
    obtain ⟨v, v', St, Sh, rfl⟩ := hP u List.mem_cons_self
    have ih := card_applyBatch_splits_V P (G.applyUpdate (.split v v' St Sh)) hv.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))
    have hcard : (G.applyUpdate (.split v v' St Sh)).V.card = G.V.card + 1 :=
      Finset.card_insert_of_notMem hv.1.2.1
    show ((G.applyUpdate (.split v v' St Sh)).applyBatch P).V.card = _
    rw [ih, hcard, List.length_cons]
    omega

/-- A batch has at least one unit of encoding size per update. -/
theorem outLength_le_batchEnc : ∀ (G : MGraph) (W : List Update), W.length ≤ G.batchEnc W
  | _, [] => le_refl _
  | G, u :: W => by
    have h := outLength_le_batchEnc (G.applyUpdate u) W
    have hu : 1 ≤ G.updateEnc u := by
      cases u <;> simp [MGraph.updateEnc]
    simp only [List.length_cons, MGraph.batchEnc]
    omega

/-- The degree of a vertex is at most twice the number of edges. -/
theorem deg_le_two_mul_card (G : MGraph) (v : ℕ) : G.deg v ≤ 2 * G.E.card := by
  unfold MGraph.deg
  have h1 := Finset.card_filter_le G.E fun e => G.tail e = v
  have h2 := Finset.card_filter_le G.E fun e => G.head e = v
  omega

/-- A list of splits has encoding size at most `2 |E| + 1` per split. -/
theorem batchEnc_splits_le : ∀ (P : List Update) (G : MGraph),
    (∀ u ∈ P, ∃ v v' St Sh, u = .split v v' St Sh) →
    G.batchEnc P ≤ P.length * (2 * G.E.card + 1)
  | [], _, _ => by simp [MGraph.batchEnc]
  | u :: P, G, hP => by
    obtain ⟨v, v', St, Sh, rfl⟩ := hP u List.mem_cons_self
    have ih := batchEnc_splits_le P (G.applyUpdate (.split v v' St Sh))
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))
    have hE : (G.applyUpdate (.split v v' St Sh)).E = G.E := rfl
    rw [hE] at ih
    have hd := deg_le_two_mul_card (G.applyUpdate (.split v v' St Sh)) v'
    rw [hE] at hd
    have hu : G.updateEnc (.split v v' St Sh) ≤ 2 * G.E.card + 1 := by
      simp only [MGraph.updateEnc]
      have := min_le_right ((G.applyUpdate (.split v v' St Sh)).deg v)
        ((G.applyUpdate (.split v v' St Sh)).deg v')
      omega
    simp only [MGraph.batchEnc, List.length_cons]
    rw [Nat.add_mul, one_mul]
    omega

/-- **The edits of a valid list of splits have the encoding size of the splits.** -/
theorem ordEditsEnc_outPrefixEditsOn_eq : ∀ (P : List Update) (G : MGraph), G.IsValid →
    G.BatchIsValid P → (∀ u ∈ P, ∃ v v' St Sh, u = .split v v' St Sh) →
    ordEditsEnc (outPrefixEditsOn G P) = G.batchEnc P
  | [], _, _, _, _ => rfl
  | u :: P, G, hG, hval, hP => by
    obtain ⟨v, v', St, Sh, rfl⟩ := hP u List.mem_cons_self
    have ih := ordEditsEnc_outPrefixEditsOn_eq P _ (isValid_applyUpdate_of_notInsert hG hval.1)
      hval.2 (fun u hu => hP u (List.mem_cons_of_mem _ hu))
    have he := enc_outSplitEdit hG hval.1
    simp only [outPrefixEditsOn, ordEditsEnc, List.map_cons, List.sum_cons,
      MGraph.batchEnc] at ih ⊢
    omega

/-- The edits of a list without insertions have one edit per update. -/
theorem length_outPrefixEditsOn : ∀ (P : List Update) (G : MGraph),
    (∀ u ∈ P, Update.NotInsert u) → (outPrefixEditsOn G P).length = P.length
  | [], _, _ => rfl
  | .delete e :: P, G, hP => by
    simp only [outPrefixEditsOn, List.length_cons,
      length_outPrefixEditsOn P _ (fun u hu => hP u (List.mem_cons_of_mem _ hu))]
  | .split v v' St Sh :: P, G, hP => by
    simp only [outPrefixEditsOn, List.length_cons,
      length_outPrefixEditsOn P _ (fun u hu => hP u (List.mem_cons_of_mem _ hu))]
  | .insert .. :: _, _, hP => absurd (hP _ List.mem_cons_self) id

/-- The edits of deletions followed by other updates. -/
theorem outPrefixEditsOn_dels_append : ∀ (L : List ℕ) (G : MGraph) (Q : List Update),
    outPrefixEditsOn G (L.map Update.delete ++ Q) =
      L.map OrdEdit.dropEdge ++ outPrefixEditsOn (G.applyBatch (L.map Update.delete)) Q
  | [], _, _ => rfl
  | e :: L, G, Q => by
    simp only [List.map_cons, List.cons_append, outPrefixEditsOn]
    rw [outPrefixEditsOn_dels_append L (G.applyUpdate (.delete e)) Q]
    rfl

theorem batchEnc_dels : ∀ (L : List ℕ) (G : MGraph), G.batchEnc (L.map Update.delete) = L.length
  | [], _ => rfl
  | e :: L, G => by
    simp only [List.map_cons, MGraph.batchEnc, MGraph.updateEnc, batchEnc_dels L,
      List.length_cons]
    omega

theorem batchEnc_inserts (t h : ℕ → ℕ) : ∀ (L : List ℕ) (G : MGraph),
    G.batchEnc (L.map fun f => Update.insert f (t f) (h f)) = L.length
  | [], _ => rfl
  | e :: L, G => by
    simp only [List.map_cons, MGraph.batchEnc, MGraph.updateEnc, batchEnc_inserts t h L,
      List.length_cons]
    omega

theorem outBatchEnc_append : ∀ (U₁ U₂ : List Update) (G : MGraph),
    G.batchEnc (U₁ ++ U₂) = G.batchEnc U₁ + (G.applyBatch U₁).batchEnc U₂
  | [], _, _ => by simp [MGraph.batchEnc, MGraph.applyBatch]
  | u :: U₁, U₂, G => by
    have ih := outBatchEnc_append U₁ U₂ (G.applyUpdate u)
    have hstep : G.applyBatch (u :: U₁) = (G.applyUpdate u).applyBatch U₁ := rfl
    simp only [List.cons_append, MGraph.batchEnc]
    rw [ih, hstep, Nat.add_assoc]

/-! ## Encoding sizes of the edits -/

theorem ordEditsEnc_dropEdges (L : List ℕ) : ordEditsEnc (L.map OrdEdit.dropEdge) = L.length := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [ordEditsEnc, List.map_map, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    simp only [OrdEdit.enc] at ih ⊢
    omega

theorem ordEditsEnc_insEditsTour (tl hd : ℕ → ℕ) (L : List ℕ) : ∀ s,
    ordEditsEnc (insEditsTour tl hd s L) = 2 * L.length := by
  induction L with
  | nil => intro s; rfl
  | cons e L ih =>
    intro s
    rw [insEditsTour, ordEditsEnc_append, ih]
    simp only [insEditsOf, ordEditsEnc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      OrdEdit.enc, List.length_cons]
    omega

theorem ordEditsEnc_outRotateEdits (t : ℕ → List End) : ∀ X : List ℕ,
    ordEditsEnc (outRotateEdits t X) = (outRotateEdits t X).length
  | [] => rfl
  | v :: X => by
    have ih := ordEditsEnc_outRotateEdits t X
    simp only [outRotateEdits, ordEditsEnc_append, List.length_append, ih]
    split <;> simp [ordEditsEnc, OrdEdit.enc]

/-! ## The tour answers of the insertions -/

/-- When the marked ends are the ends of the edges of `E`, the marked list of a vertex is its
core list restricted to `E`. -/
theorem markedList_eq_of_marks {s : OutTourAbs} {cord : ℕ → List End} {E : Finset ℕ}
    (hmk : OutMarksOf s cord E) :
    s.markedList = fun v => (cord v).filter fun z => decide (z.1 ∈ E) := by
  funext v
  rw [markedList_eq_filter s E v (fun z hz => by
    rw [hmk.2 z]
    obtain ⟨u, hu⟩ := hz
    rw [hmk.1] at hu
    exact ⟨fun h => h.2, fun h => ⟨⟨u, hu⟩, h⟩⟩), hmk.1]

/-- **The insertion edits from the tour are the model's.** The core lists are `cord`, the new
output order `t` is `cord` restricted to the new edges `E'`, and the new edges are the edges of
`Pres` and of `L`, with no edge of `L` in `Pres`. When the marked ends are those of the edges of
`Pres`, the edits that the program writes for the entering edges `L` (with the places from
`nextMarked`) are `outInsertEdits`, and afterwards the marked ends are those of all edges of
`E'`. -/
theorem insEditsTour_eq {cord t : ℕ → List End} {E' : Finset ℕ} {src : End → ℕ} {tl hd : ℕ → ℕ}
    (ht : ∀ v, t v = (cord v).filter fun z => decide (z.1 ∈ E')) :
    ∀ (L : List ℕ) (s : OutTourAbs) (Pres : Finset ℕ), L.Nodup → (∀ e ∈ L, e ∉ Pres) →
      (∀ f, f ∈ E' ↔ f ∈ Pres ∨ f ∈ L) →
      (∀ e ∈ L, src (e, true) = tl e ∧ src (e, false) = hd e) →
      (∀ e ∈ L, (e, true) ∈ cord (tl e) ∧ (e, false) ∈ cord (hd e)) →
      OutMarksOf s cord Pres →
      insEditsTour tl hd s L = outInsertEdits t src (L.map fun e => .insert e (tl e) (hd e)) ∧
        OutMarksOf (insTourAfter s L) cord (Pres ∪ L.toFinset)
  | [], s, Pres, _, _, _, _, _, hmk => ⟨rfl, by simpa [insTourAfter] using hmk⟩
  | e :: L, s, Pres, hnd, hdis, hE, hsrc, hcord, hmk => by
    classical
    obtain ⟨heL, hnd'⟩ := List.nodup_cons.mp hnd
    have heP : e ∉ Pres := hdis e List.mem_cons_self
    have heE : e ∈ E' := (hE e).mpr (Or.inr List.mem_cons_self)
    obtain ⟨hst, hsh⟩ := hsrc e List.mem_cons_self
    obtain ⟨hct, hch⟩ := hcord e List.mem_cons_self
    have hscord : s.cord = cord := hmk.1
    -- the marks after the two ends of `e`
    have hmk' : OutMarksOf (insTourStep s e) cord (insert e Pres) := by
      refine ⟨hmk.1, fun z => ?_⟩
      unfold insTourStep
      rw [mem_mark_both, hmk.2 z, Finset.mem_insert]
      obtain ⟨z1, z2⟩ := z
      constructor
      · rintro (⟨hz, hzP⟩ | hz)
        · exact ⟨hz, Or.inr hzP⟩
        · simp only at hz
          subst hz
          cases z2
          · exact ⟨⟨_, hch⟩, Or.inl rfl⟩
          · exact ⟨⟨_, hct⟩, Or.inl rfl⟩
      · rintro ⟨hz, hzP | hzP⟩
        · exact Or.inr hzP
        · exact Or.inl ⟨hz, hzP⟩
    obtain ⟨ih1, ih2⟩ := insEditsTour_eq ht L (insTourStep s e) (insert e Pres) hnd'
      (fun f hf => by
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => heL (h ▸ hf), hdis f (List.mem_cons_of_mem _ hf)⟩)
      (fun f => by
        rw [hE f, Finset.mem_insert, List.mem_cons]
        tauto)
      (fun f hf => hsrc f (List.mem_cons_of_mem _ hf))
      (fun f hf => hcord f (List.mem_cons_of_mem _ hf)) hmk'
    refine ⟨?_, ?_⟩
    · -- the two edits of `e`
      have hins : insertedEdges (L.map fun e => Update.insert e (tl e) (hd e)) = L :=
        insertedEdges_map_insert' tl hd L
      have hn1 : s.nextMarked (tl e) (e, true) =
          cycNextWith (t (tl e)) (fun z => !decide (z.1 ∈ e :: L)) (e, true) := by
        rw [ht]
        refine hscord ▸ nextMarked_eq_cycNextWith s E' _ (tl e) (fun z hz => ?_)
          (hscord ▸ hct) heE ?_
        · rw [hmk.2 z]
          obtain ⟨u, hu⟩ := hz
          rw [hscord] at hu
          have := hE z.1
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          constructor
          · rintro ⟨-, hzP⟩
            refine ⟨this.mpr (Or.inl hzP), fun hz' => ?_⟩
            rcases List.mem_cons.mp hz' with h | h
            · exact heP (h ▸ hzP)
            · exact hdis z.1 (List.mem_cons_of_mem _ h) hzP
          · rintro ⟨hzE, hzL⟩
            refine ⟨⟨u, hu⟩, ?_⟩
            rcases this.mp hzE with h | h
            · exact h
            · exact absurd h hzL
        · rw [hmk.2]; exact fun h => heP h.2
      have hn2 : (s.setMark (e, true) 1).nextMarked (hd e) (e, false) =
          cycNextWith (t (hd e))
            (fun z => !decide (z.1 ∈ e :: L) || z == (e, true)) (e, false) := by
        rw [ht]
        have hc : (s.setMark (e, true) 1).cord = cord := hmk.1
        refine hc ▸ nextMarked_eq_cycNextWith (s.setMark (e, true) 1) E' _ (hd e)
          (fun z hz => ?_) (hc ▸ hch) heE ?_
        · simp only [OutTourAbs.setMark, ↓reduceIte, Finset.mem_insert]
          rw [hmk.2 z]
          obtain ⟨u, hu⟩ := hz
          rw [hc] at hu
          have := hE z.1
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
          constructor
          · rintro (rfl | ⟨-, hzP⟩)
            · exact ⟨heE, Or.inr rfl⟩
            · refine ⟨this.mpr (Or.inl hzP), Or.inl fun hz' => ?_⟩
              rcases List.mem_cons.mp hz' with h | h
              · exact heP (h ▸ hzP)
              · exact hdis z.1 (List.mem_cons_of_mem _ h) hzP
          · rintro ⟨hzE, hzL | rfl⟩
            · refine Or.inr ⟨⟨u, hu⟩, ?_⟩
              rcases this.mp hzE with h | h
              · exact h
              · exact absurd h hzL
            · exact Or.inl rfl
        · simp only [OutTourAbs.setMark, ↓reduceIte, Finset.mem_insert, not_or]
          refine ⟨fun h => by simp at h, ?_⟩
          rw [hmk.2]; exact fun h => heP h.2
      simp only [List.map_cons, insEditsTour, insEditsOf, outInsertEdits, hins, hst, hsh, hn1,
        hn2, ih1, List.cons_append, List.nil_append]
    · have : Pres ∪ (e :: L).toFinset = insert e Pres ∪ L.toFinset := by
        ext f; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        tauto
      rw [this]
      exact ih2

/-! ## The model of an output step -/

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- The restricted core splits of an output step. -/
noncomputable def outSplitBatch (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) : List Update :=
  restrictSplits (outKeep sparsify st U ord ord') (stepBundleTree sparsify st U ord ord').U_core

/-- The kept edges are edges of the old and of the new output graph. -/
theorem outKeep_subset (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    outKeep sparsify st U ord ord' ⊆ st.S_cur.E ∧
      outKeep sparsify st U ord ord' ⊆ (stepBundleTree sparsify st U ord ord').state.S_cur.E := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;>
  · simp only [outKeep, Finset.mem_sdiff, Finset.mem_inter] at he
    tauto

/-- **The output batch** is the deletions of the leaving edges, the restricted core splits and
the insertions of the entering edges. -/
theorem outStep_batch_eq (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree sparsify st U ord ord').U_S =
      ((outDelList sparsify st U ord ord').map Update.delete ++
        outSplitBatch sparsify st U ord ord') ++ outInsBatch sparsify st U ord ord' :=
  stepBundleTree_U_S_split sparsify st U ord ord'

/-- The new output graph is the old one after the output batch. -/
theorem outStep_S_eq (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree sparsify st U ord ord').state.S_cur =
      (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete ++
        outSplitBatch sparsify st U ord ord')).applyBatch (outInsBatch sparsify st U ord ord') := by
  show st.S_cur.applyBatch (stepBundleTree sparsify st U ord ord').U_S = _
  rw [outStep_batch_eq, applyBatch_append]

/-- The three parts of the output batch are valid, each on the graph before it. -/
theorem outStep_valid (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') :
    st.S_cur.IsValid ∧ st.S_cur.BatchIsValid ((outDelList sparsify st U ord ord').map Update.delete) ∧
      (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).BatchIsValid
        (outSplitBatch sparsify st U ord ord') ∧
      (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete ++
        outSplitBatch sparsify st U ord ord')).BatchIsValid (outInsBatch sparsify st U ord ord') := by
  obtain ⟨-, -, -, -, -, hBV⟩ := outStep_rotations sparsify st U ord ord' hready
  obtain ⟨-, -, -, -, -, hS_val, -⟩ := hready
  rw [outStep_batch_eq, batchIsValid_append, batchIsValid_append] at hBV
  exact ⟨hS_val, hBV.1.1, hBV.1.2, hBV.2⟩

/-- After the deletions, the edges of the output graph are the kept edges. -/
theorem outStep_G₁_E (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).E =
      outKeep sparsify st U ord ord' := by
  rw [(applyBatch_dels_E st.S_cur _).1, outDelList, Finset.sort_toFinset]
  have hk := (outKeep_subset sparsify st U ord ord').1
  ext e
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨he, hn⟩; by_contra hk'; exact hn ⟨he, hk'⟩
  · intro he; exact ⟨hk he, fun h => h.2 he⟩

/-- The edges of the old output graph without the leaving edges are the kept edges. -/
theorem outStep_keep_eq (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    st.S_cur.E \ (outDelList sparsify st U ord ord').toFinset = outKeep sparsify st U ord ord' := by
  rw [← outStep_G₁_E, (applyBatch_dels_E st.S_cur _).1]

/-- The edges of the new output graph are the kept edges and the entering edges. -/
theorem outStep_newE (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (f : ℕ) : f ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.E ↔
      f ∈ outKeep sparsify st U ord ord' ∨ f ∈ outInsList sparsify st U ord ord' := by
  rw [outInsList, Finset.mem_sort, Finset.mem_sdiff]
  have hk := (outKeep_subset sparsify st U ord ord').2
  constructor
  · intro hf; by_cases h : f ∈ outKeep sparsify st U ord ord'
    · exact Or.inl h
    · exact Or.inr ⟨hf, h⟩
  · rintro (h | h)
    · exact hk h
    · exact h.1

/-- The entering edges end at the new roots of their endpoints in the new output graph. -/
theorem outStep_ins_ends (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    ∀ e ∈ outInsList sparsify st U ord ord',
      (stepBundleTree sparsify st U ord ord').state.S_cur.tail e =
          (stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.tail e) ∧
        (stepBundleTree sparsify st U ord ord').state.S_cur.head e =
          (stepBundleTree sparsify st U ord ord').state.cs.RF.root
            ((stepBundleTree sparsify st U ord ord').state.cs.G.head e) := by
  intro e he
  rw [outStep_S_eq]
  exact applyBatch_inserts_ends _ _ _ _ (Finset.sort_nodup _ _) e he

/-- Each end of a new output edge is in the new core list of its vertex. -/
theorem outStep_cord_mem (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') :
    ∀ e ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.E, ∀ b : Bool,
      (e, b) ∈ outCoreOrder (stepBundleTree sparsify st U ord ord').state ord'
        ((stepBundleTree sparsify st U ord ord').state.S_cur.src (e, b)) := by
  intro e he b
  have hmem := (ordMemOf_outOrder sparsify st U ord ord' hready).2
  have h := (hmem _ (e, b)).mpr ⟨he, rfl⟩
  rw [outOrder_eq_filter] at h
  exact List.mem_of_mem_filter h

/-- The vertices and the edges of the graph after the splits: every new vertex is below `vCap`,
there are at most `vCap` splits, and they have encoding size at most `2 eCap + 1` each. -/
theorem outStep_splits_caps {vCap eCap : ℕ} (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord')
    (hR : ∀ v ∈ (stepBundleTree sparsify st U ord ord').state.cs.RF.R, v < vCap)
    (hE : ∀ e ∈ st.S_cur.E, e < eCap) :
    (∀ u ∈ outSplitBatch sparsify st U ord ord', UpdateWithinCaps vCap eCap u) ∧
      (outSplitBatch sparsify st U ord ord').length ≤ vCap ∧
      (st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete)).batchEnc
          (outSplitBatch sparsify st U ord ord') ≤
        (outSplitBatch sparsify st U ord ord').length * (2 * eCap + 1) := by
  obtain ⟨-, -, hvP, hvI⟩ := outStep_valid sparsify st U ord ord' hready
  set G₁ := st.S_cur.applyBatch ((outDelList sparsify st U ord ord').map Update.delete) with hG₁
  set P := outSplitBatch sparsify st U ord ord' with hP
  have hsplit : ∀ u ∈ P, ∃ v v' St Sh, u = .split v v' St Sh := restrictSplits_isSplit _ _
  have hV' : (stepBundleTree sparsify st U ord ord').state.S_cur.V =
      (stepBundleTree sparsify st U ord ord').state.cs.RF.R := outStep_V sparsify st U ord ord' hready
  -- the vertices after the splits are vertices of the new output graph
  have hsub : (G₁.applyBatch P).V ⊆ (stepBundleTree sparsify st U ord ord').state.S_cur.V := by
    rw [outStep_S_eq, applyBatch_append]
    exact V_subset_applyBatch _ _
  have hlt : ∀ v ∈ (G₁.applyBatch P).V, v < vCap := fun v hv => hR v (hV' ▸ hsub hv)
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, v', St, Sh, rfl⟩ := hsplit u hu
    exact hlt v' (mem_applyBatch_V_of_split P G₁ hvP v v' St Sh hu)
  · have hcard := card_applyBatch_splits_V P G₁ hvP hsplit
    have : (G₁.applyBatch P).V.card ≤ vCap := by
      calc (G₁.applyBatch P).V.card ≤ (Finset.range vCap).card :=
            Finset.card_le_card fun v hv => Finset.mem_range.mpr (hlt v hv)
        _ = vCap := Finset.card_range vCap
    omega
  · have h := batchEnc_splits_le P G₁ hsplit
    have hEc : G₁.E.card ≤ eCap := by
      calc G₁.E.card ≤ (Finset.range eCap).card := by
            refine Finset.card_le_card fun e he => Finset.mem_range.mpr (hE e ?_)
            rw [hG₁, outStep_G₁_E] at he
            exact (outKeep_subset sparsify st U ord ord').1 he
        _ = eCap := Finset.card_range eCap
    calc G₁.batchEnc P ≤ P.length * (2 * G₁.E.card + 1) := h
      _ ≤ P.length * (2 * eCap + 1) := Nat.mul_le_mul_left _ (by omega)

end MinCostFlow.SparseCore.Program
