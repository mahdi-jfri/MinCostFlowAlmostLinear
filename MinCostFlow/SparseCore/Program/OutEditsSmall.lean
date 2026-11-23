module

public import MinCostFlow.SparseCore.Program.OutEditsBatch

/-!
# Split edits that list the smaller side

The output batch must be written in its compact form (`SmallBatchAt`): a split lists either the
ends that move or the ends that stay, whichever set is smaller, so that its words are at most its
encoding size. The edits of the output order should follow the same rule: a split becomes
`moveEnds v v' sel c`, where `sel` is the smaller of the two sets and the flag `c` says that `sel`
is the set that stays (`complement`). Then the encoding size of the edits is at most the encoding
size of the batch.

This file defines these edits (`outSplitEdit`, `outPrefixEditsOn`) and proves:

* `applyOrdEdits_outPrefixEditsOn`: on an order whose lists hold exactly the ends of the graph at
  their vertices (`OrdMemOf`), these edits give the same order as the edits `outPrefixEdits`,
  which list the moved ends. The reason is that both move exactly the same ends of the
  list at the split vertex.
* `ordEditsEnc_outPrefixEditsOn_le`: their encoding size is at most the encoding size of the
  batch. A deletion costs one on both sides, and a split costs one plus the smaller degree on both
  sides, since the moved ends are the ends at the new vertex after the split and the kept ends are
  the ends at the old vertex.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

/-! ## The edits -/

/-- The ends of a split of `v` in `G` with tail set `St` and head set `Sh` that move to the new
vertex: the tails at `v` of the edges of `St` and the heads at `v` of the edges of `Sh`. -/
def splitMovedSel (G : MGraph) (v : ℕ) (St Sh : Finset ℕ) : Finset End :=
  splitSel (G.E.filter fun e => G.tail e = v ∧ e ∈ St) (G.E.filter fun e => G.head e = v ∧ e ∈ Sh)

/-- The ends at `v` that a split of `v` keeps at `v`. -/
def splitKeptSel (G : MGraph) (v : ℕ) (St Sh : Finset ℕ) : Finset End :=
  splitSel (G.E.filter fun e => G.tail e = v ∧ e ∉ St) (G.E.filter fun e => G.head e = v ∧ e ∉ Sh)

/-- The edit of a split of `v` into `v` and `v'`: move the moved ends when they are at most as
many as the kept ends, and otherwise move the ends that are not kept. -/
def outSplitEdit (G : MGraph) (v v' : ℕ) (St Sh : Finset ℕ) : OrdEdit :=
  if (splitMovedSel G v St Sh).card ≤ (splitKeptSel G v St Sh).card then
    .moveEnds v v' (splitMovedSel G v St Sh) false
  else .moveEnds v v' (splitKeptSel G v St Sh) true

/-- The edits of the deletions and splits of a batch on the graph `G`, with each split written by
its smaller side. Insertions are skipped. -/
def outPrefixEditsOn : MGraph → List Update → List OrdEdit
  | _, [] => []
  | G, .delete e :: U => .dropEdge e :: outPrefixEditsOn (G.applyUpdate (.delete e)) U
  | G, .split v v' St Sh :: U =>
    outSplitEdit G v v' St Sh :: outPrefixEditsOn (G.applyUpdate (.split v v' St Sh)) U
  | G, .insert e a b :: U => outPrefixEditsOn (G.applyUpdate (.insert e a b)) U

/-- The lists of the order `A` hold exactly the ends of the edges of `G`, each at its vertex. -/
def OrdMemOf (A : ℕ → List End) (G : MGraph) : Prop :=
  ∀ v x, x ∈ A v ↔ x.1 ∈ G.E ∧ G.src x = v

/-! ## Small facts -/

theorem mem_splitSel_true (A B : Finset ℕ) (e : ℕ) : (e, true) ∈ splitSel A B ↔ e ∈ A := by
  simp [splitSel]

theorem mem_splitSel_false (A B : Finset ℕ) (e : ℕ) : (e, false) ∈ splitSel A B ↔ e ∈ B := by
  simp [splitSel]

theorem card_splitSel (A B : Finset ℕ) : (splitSel A B).card = A.card + B.card := by
  unfold splitSel
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx'
  simp at hb

private theorem src_mem_V {G : MGraph} (hG : G.IsValid) {x : End} (hx : x.1 ∈ G.E) :
    G.src x ∈ G.V := by
  obtain ⟨e, b⟩ := x
  cases b
  · exact (hG e hx).2
  · exact (hG e hx).1

/-- A deletion or a split keeps a graph valid. -/
theorem isValid_applyUpdate_of_notInsert {G : MGraph} (hG : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) : (G.applyUpdate u).IsValid := by
  cases u with
  | insert e a b =>
    intro f hf
    simp only [MGraph.applyUpdate, Finset.mem_insert] at hf
    rcases hf with rfl | hfG
    · simp [MGraph.applyUpdate, hu.2.1, hu.2.2]
    · have hne : f ≠ e := fun h => hu.1 (h ▸ hfG)
      simpa [MGraph.applyUpdate, Function.update_of_ne hne] using hG f hfG
  | delete e =>
    intro f hf
    simp only [MGraph.applyUpdate, Finset.mem_erase] at hf
    exact hG f hf.2
  | split v v' St Sh =>
    intro f hf
    simp only [MGraph.applyUpdate] at hf ⊢
    have h := hG f hf
    constructor
    · split
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem h.1
    · split
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem h.2

/-! ## The edits move the same ends -/

/-- On the list at the split vertex, the edit of the smaller side moves exactly the ends that the
split moves. -/
theorem movedBy_outSplitEdit {G : MGraph} {v : ℕ} {St Sh : Finset ℕ} {x : End}
    (hx : x.1 ∈ G.E) (hv : G.src x = v) (sel : Finset End) (c : Bool)
    (hsel : (sel = splitMovedSel G v St Sh ∧ c = false) ∨ (sel = splitKeptSel G v St Sh ∧ c = true)) :
    movedBy sel c x = splitEnds St Sh x := by
  obtain ⟨e, b⟩ := x
  rcases hsel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases b
    · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hv
      simp [movedBy, splitMovedSel, mem_splitSel_false, splitEnds, hx, hv]
    · simp only [MGraph.src, ↓reduceIte] at hv
      simp [movedBy, splitMovedSel, mem_splitSel_true, splitEnds, hx, hv]
  · cases b
    · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hv
      simp [movedBy, splitKeptSel, mem_splitSel_false, splitEnds, hx, hv]
    · simp only [MGraph.src, ↓reduceIte] at hv
      simp [movedBy, splitKeptSel, mem_splitSel_true, splitEnds, hx, hv]

/-- On an order with the ends of `G`, the edit of the smaller side is the edit of the moved ends. -/
theorem applyOrdEdit_outSplitEdit {A : ℕ → List End} {G : MGraph} (hA : OrdMemOf A G)
    (v v' : ℕ) (St Sh : Finset ℕ) :
    applyOrdEdit A (outSplitEdit G v v' St Sh) =
      applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false) := by
  have key : ∀ (sel : Finset End) (c : Bool),
      ((sel = splitMovedSel G v St Sh ∧ c = false) ∨ (sel = splitKeptSel G v St Sh ∧ c = true)) →
      applyOrdEdit A (.moveEnds v v' sel c) = applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false) := by
    intro sel c hsel
    have hcongr : ∀ x ∈ A v, movedBy sel c x = movedBy (splitSel St Sh) false x := by
      intro x hx
      obtain ⟨hxE, hxv⟩ := (hA v x).mp hx
      rw [movedBy_outSplitEdit hxE hxv sel c hsel, movedBy_splitSel]
    have h1 : (A v).filter (fun x => !movedBy sel c x) =
        (A v).filter (fun x => !movedBy (splitSel St Sh) false x) :=
      List.filter_congr (fun x hx => by rw [hcongr x hx])
    have h2 : (A v).filter (movedBy sel c) = (A v).filter (movedBy (splitSel St Sh) false) :=
      List.filter_congr (fun x hx => hcongr x hx)
    funext u
    simp only [applyOrdEdit]
    rw [h1, h2]
  unfold outSplitEdit
  split
  · exact key _ _ (Or.inl ⟨rfl, rfl⟩)
  · exact key _ _ (Or.inr ⟨rfl, rfl⟩)

/-- A deletion keeps `OrdMemOf`. -/
theorem ordMemOf_dropEdge {A : ℕ → List End} {G : MGraph} (hA : OrdMemOf A G) (e : ℕ) :
    OrdMemOf (applyOrdEdit A (.dropEdge e)) (G.applyUpdate (.delete e)) := by
  intro u x
  simp only [applyOrdEdit, List.mem_filter, hA u x, bne_iff_ne, ne_eq]
  obtain ⟨f, b⟩ := x
  cases b <;> simp [MGraph.applyUpdate, MGraph.src, Finset.mem_erase] <;> tauto

/-- A valid split keeps `OrdMemOf`, with the moved ends of the split vertex at the back of the
new vertex. -/
theorem ordMemOf_moveEnds {A : ℕ → List End} {G : MGraph} (hA : OrdMemOf A G) (hG : G.IsValid)
    {v v' : ℕ} {St Sh : Finset ℕ} (hu : G.UpdateIsValid (.split v v' St Sh)) :
    OrdMemOf (applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false))
      (G.applyUpdate (.split v v' St Sh)) := by
  obtain ⟨hvV, hv'V, -, -⟩ := hu
  have hne : v ≠ v' := fun h => hv'V (h ▸ hvV)
  have hE : (G.applyUpdate (.split v v' St Sh)).E = G.E := rfl
  intro u x
  rw [hE, src_applySplit]
  have hnot : ∀ y, y.1 ∈ G.E → G.src y ≠ v' := fun y hy h => hv'V (h ▸ src_mem_V hG hy)
  simp only [applyOrdEdit, movedBy_splitSel]
  by_cases hu : u = v
  · subst hu
    simp only [↓reduceIte, List.mem_filter, hA u x, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨hx, hs⟩, hm⟩
      exact ⟨hx, by simp [hs, hm]⟩
    · rintro ⟨hx, hs⟩
      by_cases hc : G.src x = u ∧ splitEnds St Sh x = true
      · rw [ite_eq_left hc] at hs; exact absurd hs.symm hne
      · rw [ite_eq_right hc] at hs
        refine ⟨⟨hx, hs⟩, ?_⟩
        cases h : splitEnds St Sh x
        · rfl
        · exact absurd ⟨hs, h⟩ hc
  · by_cases hu' : u = v'
    · subst hu'
      have hA' : ∀ w y, y ∈ A w ↔ y.1 ∈ G.E ∧ G.src y = w := hA
      simp only [hu, ↓reduceIte, List.mem_append, List.mem_filter, hA']
      constructor
      · rintro (⟨hx, hs⟩ | ⟨⟨hx, hs⟩, hm⟩)
        · exact absurd hs (hnot x hx)
        · rw [movedBy_splitSel] at hm
          exact ⟨hx, by rw [ite_eq_left ⟨hs, hm⟩]⟩
      · rintro ⟨hx, hs⟩
        by_cases hc : G.src x = v ∧ splitEnds St Sh x = true
        · exact Or.inr ⟨⟨hx, hc.1⟩, by rw [movedBy_splitSel]; exact hc.2⟩
        · rw [ite_eq_right hc] at hs; exact absurd hs (hnot x hx)
    · simp only [hu, hu', ↓reduceIte, hA u x]
      constructor
      · rintro ⟨hx, hs⟩
        refine ⟨hx, ?_⟩
        rw [ite_eq_right (fun hc => hu (hs ▸ hc.1))]
        exact hs
      · rintro ⟨hx, hs⟩
        by_cases hc : G.src x = v ∧ splitEnds St Sh x = true
        · rw [ite_eq_left hc] at hs; exact absurd hs.symm hu'
        · rw [ite_eq_right hc] at hs; exact ⟨hx, hs⟩

/-- **The edits of the smaller sides give the same order.** On an order whose lists hold exactly
the ends of a valid graph `G`, the edits `outPrefixEditsOn G P` of a valid batch `P` of
deletions and splits give the same order as the edits `outPrefixEdits P`. -/
theorem applyOrdEdits_outPrefixEditsOn :
    ∀ (P : List Update) (G : MGraph) (A : ℕ → List End), OrdMemOf A G → G.IsValid →
      G.BatchIsValid P → (∀ u ∈ P, Update.NotInsert u) →
      applyOrdEdits A (outPrefixEditsOn G P) = applyOrdEdits A (outPrefixEdits P)
  | [], _, _, _, _, _, _ => rfl
  | .delete e :: P, G, A, hA, hG, hval, hP => by
    have h := applyOrdEdits_outPrefixEditsOn P (G.applyUpdate (.delete e))
      (applyOrdEdit A (.dropEdge e)) (ordMemOf_dropEdge hA e)
      (isValid_applyUpdate_of_notInsert hG hval.1) hval.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))
    simpa only [outPrefixEditsOn, outPrefixEdits, applyOrdEdits, List.foldl_cons] using h
  | .split v v' St Sh :: P, G, A, hA, hG, hval, hP => by
    have h := applyOrdEdits_outPrefixEditsOn P (G.applyUpdate (.split v v' St Sh))
      (applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false)) (ordMemOf_moveEnds hA hG hval.1)
      (isValid_applyUpdate_of_notInsert hG hval.1) hval.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))
    simp only [outPrefixEditsOn, outPrefixEdits, applyOrdEdits, List.foldl_cons] at h ⊢
    rw [applyOrdEdit_outSplitEdit hA]
    exact h
  | .insert .. :: _, _, _, _, _, _, hP => absurd (hP _ List.mem_cons_self) id

/-! ## The encoding size -/

/-- The degree of the new vertex after a valid split is the number of moved ends, and the degree
of the split vertex is the number of kept ends. -/
theorem deg_applySplit {G : MGraph} (hG : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    (G.applyUpdate (.split v v' St Sh)).deg v' = (splitMovedSel G v St Sh).card ∧
      (G.applyUpdate (.split v v' St Sh)).deg v = (splitKeptSel G v St Sh).card := by
  obtain ⟨hvV, hv'V, -, -⟩ := hu
  have hne : v ≠ v' := fun h => hv'V (h ▸ hvV)
  have ht : ∀ e ∈ G.E, G.tail e ≠ v' := fun e he h => hv'V (h ▸ (hG e he).1)
  have hh : ∀ e ∈ G.E, G.head e ≠ v' := fun e he h => hv'V (h ▸ (hG e he).2)
  have key : ∀ (E S : Finset ℕ) (f f' : ℕ → ℕ), (∀ e, f' e = if e ∈ S ∧ f e = v then v' else f e) →
      (∀ e ∈ E, f e ≠ v') →
      (E.filter fun e => f' e = v') = E.filter (fun e => f e = v ∧ e ∈ S) ∧
      (E.filter fun e => f' e = v) = E.filter (fun e => f e = v ∧ e ∉ S) := by
    intro E S f f' hf' hf
    constructor
    · ext e
      simp only [Finset.mem_filter, hf']
      constructor
      · rintro ⟨he, h⟩
        refine ⟨he, ?_⟩
        by_cases hc : e ∈ S ∧ f e = v
        · exact ⟨hc.2, hc.1⟩
        · rw [ite_eq_right hc] at h; exact absurd h (hf e he)
      · rintro ⟨he, hv, hs⟩
        exact ⟨he, by rw [ite_eq_left ⟨hs, hv⟩]⟩
    · ext e
      simp only [Finset.mem_filter, hf']
      constructor
      · rintro ⟨he, h⟩
        refine ⟨he, ?_⟩
        by_cases hc : e ∈ S ∧ f e = v
        · rw [ite_eq_left hc] at h; exact absurd h.symm hne
        · rw [ite_eq_right hc] at h; exact ⟨h, fun hs => hc ⟨hs, h⟩⟩
      · rintro ⟨he, hv, hs⟩
        exact ⟨he, by rw [ite_eq_right (fun hc => hs hc.1)]; exact hv⟩
  set G' := G.applyUpdate (.split v v' St Sh) with hG'
  obtain ⟨t₁, t₂⟩ := key G'.E St G.tail G'.tail (fun e => rfl) ht
  obtain ⟨h₁, h₂⟩ := key G'.E Sh G.head G'.head (fun e => rfl) hh
  simp only [MGraph.deg, splitMovedSel, splitKeptSel, card_splitSel]
  rw [t₁, t₂, h₁, h₂]
  exact ⟨rfl, rfl⟩

/-- The encoding size of the edit of a valid split is the encoding size of the split. -/
theorem enc_outSplitEdit {G : MGraph} (hG : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    (outSplitEdit G v v' St Sh).enc = G.updateEnc (.split v v' St Sh) := by
  obtain ⟨h₁, h₂⟩ := deg_applySplit hG hu
  simp only [MGraph.updateEnc, h₁, h₂]
  unfold outSplitEdit
  split <;> simp only [OrdEdit.enc] <;> omega

/-- **The encoding size of the edits is at most that of the batch.** -/
theorem ordEditsEnc_outPrefixEditsOn_le :
    ∀ (P : List Update) (G : MGraph), G.IsValid → G.BatchIsValid P →
      ordEditsEnc (outPrefixEditsOn G P) ≤ G.batchEnc P
  | [], _, _, _ => le_refl _
  | .delete e :: P, G, hG, hval => by
    have h := ordEditsEnc_outPrefixEditsOn_le P _ (isValid_applyUpdate_of_notInsert hG hval.1)
      hval.2
    simp only [outPrefixEditsOn, ordEditsEnc, List.map_cons, List.sum_cons, MGraph.batchEnc,
      OrdEdit.enc, MGraph.updateEnc] at h ⊢
    omega
  | .split v v' St Sh :: P, G, hG, hval => by
    have h := ordEditsEnc_outPrefixEditsOn_le P _ (isValid_applyUpdate_of_notInsert hG hval.1)
      hval.2
    have he := enc_outSplitEdit hG hval.1
    simp only [outPrefixEditsOn, ordEditsEnc, List.map_cons, List.sum_cons, MGraph.batchEnc] at h ⊢
    omega
  | .insert e a b :: P, G, hG, hval => by
    have h := ordEditsEnc_outPrefixEditsOn_le P _ (isValid_applyUpdate_of_notInsert hG hval.1)
      hval.2
    simp only [outPrefixEditsOn, MGraph.batchEnc] at h ⊢
    omega

end MinCostFlow.SparseCore.Program
