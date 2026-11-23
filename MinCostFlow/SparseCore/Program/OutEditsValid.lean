module

public import MinCostFlow.SparseCore.Program.OutEditsStep

/-!
# The edits of the output step can be sent to the order store

The edits of a level are the input edits of the next level, whose order store (piece P1) asks
that every edit names vertices below `vCap` and edges below `eCap` (`OrdEditsWithin`), and that
after every prefix of the edits each end is in at most one list, with no repeats
(`OrdEditsUniqueWithin`). This file proves both for the edits `outStepEditsSmall` of an output
step (`outStepEditsSmall_valid`).

The proof follows the three parts of the edits.
* Along the deletions and splits, the lists hold exactly the ends of the current output graph at
  their vertices (`OrdMemOf`), with no repeats. So an end is only at its own vertex.
* Along the insertions, the lists hold ends of the new output graph at their new vertices, and an
  inserted end is not yet in any list: its edge enters the output graph, so it is not a kept edge,
  and it is inserted only once.
* A `rotateTo` edit only reorders one list.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-! ## Properties of all prefixes -/

/-- The property `Q` holds after every prefix of `ds`, applied to `A`. -/
def AllPrefixes (Q : (ℕ → List End) → Prop) (A : ℕ → List End) (ds : List OrdEdit) : Prop :=
  ∀ k ≤ ds.length, Q (applyOrdEdits A (ds.take k))

theorem allPrefixes_nil {Q : (ℕ → List End) → Prop} {A : ℕ → List End} (h : Q A) :
    AllPrefixes Q A [] := by
  intro k hk
  simp only [List.length_nil, Nat.le_zero] at hk
  subst hk
  exact h

theorem allPrefixes_cons {Q : (ℕ → List End) → Prop} {A : ℕ → List End} {d : OrdEdit}
    {ds : List OrdEdit} (h : Q A) (h' : AllPrefixes Q (applyOrdEdit A d) ds) :
    AllPrefixes Q A (d :: ds) := by
  intro k hk
  cases k with
  | zero => exact h
  | succ k =>
    simp only [List.take_succ_cons]
    exact h' k (by simpa using hk)

theorem allPrefixes_append {Q : (ℕ → List End) → Prop} {A : ℕ → List End}
    {ds ds' : List OrdEdit} (h : AllPrefixes Q A ds) (h' : AllPrefixes Q (applyOrdEdits A ds) ds') :
    AllPrefixes Q A (ds ++ ds') := by
  intro k hk
  rcases Nat.lt_or_ge ds.length k with hlt | hle
  swap
  · rw [List.take_append_of_le_length hle]
    exact h k hle
  · rw [List.take_append, List.take_of_length_le (by omega), applyOrdEdits_append']
    exact h' (k - ds.length) (by simp only [List.length_append] at hk; omega)

/-! ## The deletions and splits -/

private theorem V_subset_applyUpdate (G : MGraph) (u : Update) : G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert e a b => exact le_refl _
  | delete e => exact le_refl _
  | split v v' St Sh => exact Finset.subset_insert _ _

theorem V_subset_applyBatch : ∀ (G : MGraph) (W : List Update), G.V ⊆ (G.applyBatch W).V
  | _, [] => le_refl _
  | G, u :: W => (V_subset_applyUpdate G u).trans (V_subset_applyBatch (G.applyUpdate u) W)

/-- An order whose lists hold exactly the ends of a valid graph with small names, with no
repeats, meets `OrdUniqueWithin`. -/
theorem ordUniqueWithin_of_memOf {vCap eCap : ℕ} {A : ℕ → List End} {G : MGraph}
    (hA : OrdMemOf A G) (hnd : ∀ v, (A v).Nodup) (hG : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap)
    (hE : ∀ e ∈ G.E, e < eCap) : OrdUniqueWithin vCap eCap A := by
  refine ⟨⟨hnd, fun v hv => ?_, fun v x hx => hE _ ((hA v x).mp hx).1⟩, fun u v x hu hv => ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨hxE, hxv⟩ := (hA v x).mp hx
    have : G.src x ∈ G.V := by
      obtain ⟨e, b⟩ := x
      cases b
      · exact (hG e hxE).2
      · exact (hG e hxE).1
    have := hV _ this
    omega
  · exact ((hA u x).mp hu).2.symm.trans ((hA v x).mp hv).2

/-- One step of the deletions and splits keeps `OrdMemOf` and the absence of repeats. -/
private theorem prefix_step_nodup {A : ℕ → List End} {G : MGraph} (hA : OrdMemOf A G)
    (hnd : ∀ v, (A v).Nodup) (hG : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    ∀ w, (applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false) w).Nodup := by
  obtain ⟨hvV, hv'V, -, -⟩ := hu
  have hne : v ≠ v' := fun h => hv'V (h ▸ hvV)
  have hAv' : A v' = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨hxE, hxv⟩ := (hA v' x).mp hx
    apply hv'V
    rw [← hxv]
    obtain ⟨e, b⟩ := x
    cases b
    · exact (hG e hxE).2
    · exact (hG e hxE).1
  intro w
  simp only [applyOrdEdit]
  by_cases hw : w = v
  · rw [ite_eq_left hw]; exact (hnd v).filter _
  · rw [ite_eq_right hw]
    by_cases hw' : w = v'
    · rw [ite_eq_left hw', hAv', List.nil_append]; exact (hnd v).filter _
    · rw [ite_eq_right hw']; exact hnd w

/-- **The deletions and splits.** Along the edits of a valid batch of deletions and splits, the
order meets `OrdUniqueWithin` after every prefix, and at the end it holds exactly the ends of the
graph after the batch, with no repeats. -/
theorem outPrefixEditsOn_allPrefixes {vCap eCap : ℕ} :
    ∀ (P : List Update) (G : MGraph) (A : ℕ → List End), OrdMemOf A G → (∀ v, (A v).Nodup) →
      G.IsValid → G.BatchIsValid P → (∀ u ∈ P, Update.NotInsert u) →
      (∀ v ∈ (G.applyBatch P).V, v < vCap) → (∀ e ∈ G.E, e < eCap) →
      AllPrefixes (OrdUniqueWithin vCap eCap) A (outPrefixEditsOn G P) ∧
        OrdMemOf (applyOrdEdits A (outPrefixEditsOn G P)) (G.applyBatch P) ∧
        ∀ v, (applyOrdEdits A (outPrefixEditsOn G P) v).Nodup
  | [], G, A, hA, hnd, hG, _, _, hV, hE => by
    refine ⟨allPrefixes_nil (ordUniqueWithin_of_memOf hA hnd hG hV hE), hA, hnd⟩
  | .delete e :: P, G, A, hA, hnd, hG, hval, hP, hV, hE => by
    have hQ := ordUniqueWithin_of_memOf (vCap := vCap) (eCap := eCap) hA hnd hG
      (fun v hv => hV v (V_subset_applyBatch G _ hv)) hE
    obtain ⟨h1, h2, h3⟩ := outPrefixEditsOn_allPrefixes P (G.applyUpdate (.delete e))
      (applyOrdEdit A (.dropEdge e)) (ordMemOf_dropEdge hA e) (fun v => (hnd v).filter _)
      (isValid_applyUpdate_of_notInsert hG hval.1) hval.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu)) hV
      (fun f hf => hE f (Finset.mem_of_mem_erase hf))
    exact ⟨allPrefixes_cons hQ h1, h2, h3⟩
  | .split v v' St Sh :: P, G, A, hA, hnd, hG, hval, hP, hV, hE => by
    have hQ := ordUniqueWithin_of_memOf (vCap := vCap) (eCap := eCap) hA hnd hG
      (fun v hv => hV v (V_subset_applyBatch G _ hv)) hE
    obtain ⟨h1, h2, h3⟩ := outPrefixEditsOn_allPrefixes P (G.applyUpdate (.split v v' St Sh))
      (applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false)) (ordMemOf_moveEnds hA hG hval.1)
      (prefix_step_nodup hA hnd hG hval.1) (isValid_applyUpdate_of_notInsert hG hval.1) hval.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu)) hV hE
    have heq := applyOrdEdit_outSplitEdit hA v v' St Sh
    refine ⟨allPrefixes_cons hQ ?_, ?_, ?_⟩
    · rw [heq]; exact h1
    · show OrdMemOf (applyOrdEdits (applyOrdEdit A (outSplitEdit G v v' St Sh)) _) _
      rw [heq]; exact h2
    · show ∀ w, (applyOrdEdits (applyOrdEdit A (outSplitEdit G v v' St Sh)) _ w).Nodup
      rw [heq]; exact h3
  | .insert .. :: _, _, _, _, _, _, _, hP, _, _ => absurd (hP _ List.mem_cons_self) id

/-- The edits of the deletions and splits name small vertices and edges. -/
theorem outPrefixEditsOn_within {vCap eCap : ℕ} :
    ∀ (P : List Update) (G : MGraph), G.BatchIsValid P → (∀ u ∈ P, Update.NotInsert u) →
      (∀ v ∈ (G.applyBatch P).V, v < vCap) → (∀ e ∈ G.E, e < eCap) →
      OrdEditsWithin vCap eCap (outPrefixEditsOn G P)
  | [], _, _, _, _, _ => fun _ h => by simp [outPrefixEditsOn] at h
  | .delete e :: P, G, hval, hP, hV, hE => by
    have ih := outPrefixEditsOn_within P (G.applyUpdate (.delete e)) hval.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu)) hV
      (fun f hf => hE f (Finset.mem_of_mem_erase hf))
    intro d hd
    simp only [outPrefixEditsOn, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hE e hval.1
    · exact ih d hd
  | .split v v' St Sh :: P, G, hval, hP, hV, hE => by
    have ih := outPrefixEditsOn_within P (G.applyUpdate (.split v v' St Sh)) hval.2
      (fun u hu => hP u (List.mem_cons_of_mem _ hu)) hV hE
    have hvV : v < vCap := hV v (V_subset_applyBatch _ P (Finset.mem_insert_of_mem hval.1.1))
    have hv'V : v' < vCap := hV v' (V_subset_applyBatch _ P (Finset.mem_insert_self _ _))
    have hsel : ∀ (A B : Finset ℕ), A ⊆ G.E → B ⊆ G.E → ∀ x ∈ splitSel A B, x.1 < eCap := by
      intro A B hA hB x hx
      simp only [splitSel, Finset.mem_union, Finset.mem_image] at hx
      rcases hx with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact hE e (hA he)
      · exact hE e (hB he)
    intro d hd
    simp only [outPrefixEditsOn, List.mem_cons] at hd
    rcases hd with rfl | hd
    · unfold outSplitEdit
      by_cases hc : (splitMovedSel G v St Sh).card ≤ (splitKeptSel G v St Sh).card
      · rw [ite_eq_left hc]
        exact ⟨hvV, hv'V, hsel _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _)⟩
      · rw [ite_eq_right hc]
        exact ⟨hvV, hv'V, hsel _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _)⟩
    · exact ih d hd
  | .insert .. :: _, _, _, hP, _, _ => absurd (hP _ List.mem_cons_self) id

/-! ## The insertions -/

/-- The invariant along the insertions: every end of a list is present (in `Pres`) and lies at
its vertex `src`, and no list has repeats. -/
def InsInv (src : End → ℕ) (Pres : Finset End) (A : ℕ → List End) : Prop :=
  (∀ v x, x ∈ A v → x ∈ Pres ∧ src x = v) ∧ ∀ v, (A v).Nodup

private theorem insInv_insert {src : End → ℕ} {Pres : Finset End} {A : ℕ → List End}
    (h : InsInv src Pres A) {x : End} (hx : x ∉ Pres) (y : Option End) :
    InsInv src (insert x Pres) (applyOrdEdit A (.insertBefore (src x) x y)) := by
  have hxA : x ∉ A (src x) := fun hm => hx (h.1 _ x hm).1
  have hmem : ∀ z, z ∈ insertBeforeList x y (A (src x)) ↔ z = x ∨ z ∈ A (src x) := by
    intro z
    cases y with
    | none => simp [insertBeforeList, or_comm]
    | some y =>
      simp only [insertBeforeList]
      constructor
      · intro hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Or.inr (List.mem_of_mem_take hz)
        · rcases List.mem_cons.mp hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (List.mem_of_mem_drop hz)
      · rintro (rfl | hz)
        · exact List.mem_append_right _ List.mem_cons_self
        · rw [← List.take_append_drop ((A (src x)).idxOf y) (A (src x))] at hz
          rcases List.mem_append.mp hz with hz | hz
          · exact List.mem_append_left _ hz
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  have hnd : (insertBeforeList x y (A (src x))).Nodup := by
    cases y with
    | none => exact (h.2 _).append (List.nodup_singleton x) (by simpa using hxA)
    | some y =>
      simp only [insertBeforeList]
      have hnd := h.2 (src x)
      rw [← List.take_append_drop ((A (src x)).idxOf y) (A (src x))] at hnd hxA
      rw [List.nodup_append] at hnd ⊢
      refine ⟨hnd.1, List.nodup_cons.mpr ⟨fun hm => hxA (List.mem_append_right _ hm), hnd.2.1⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rintro rfl; exact hxA (List.mem_append_left _ ha)
      · exact hnd.2.2 a ha b hb
  constructor
  · intro v z hz
    simp only [applyOrdEdit] at hz
    by_cases hv : v = src x
    · subst hv
      rw [Function.update_self] at hz
      rcases (hmem z).mp hz with rfl | hz
      · exact ⟨Finset.mem_insert_self _ _, rfl⟩
      · exact ⟨Finset.mem_insert_of_mem (h.1 _ z hz).1, (h.1 _ z hz).2⟩
    · rw [Function.update_of_ne hv] at hz
      exact ⟨Finset.mem_insert_of_mem (h.1 _ z hz).1, (h.1 _ z hz).2⟩
  · intro v
    simp only [applyOrdEdit]
    by_cases hv : v = src x
    · subst hv; rw [Function.update_self]; exact hnd
    · rw [Function.update_of_ne hv]; exact h.2 v

/-- An order with `InsInv` for present ends of a valid graph with small names meets
`OrdUniqueWithin`. -/
private theorem ordUniqueWithin_of_insInv {vCap eCap : ℕ} {G : MGraph} {Pres : Finset End}
    {A : ℕ → List End} (h : InsInv G.src Pres A) (hP : ∀ x ∈ Pres, x.1 ∈ G.E)
    (hG : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap) :
    OrdUniqueWithin vCap eCap A := by
  refine ⟨⟨h.2, fun v hv => ?_, fun v x hx => hE _ (hP x (h.1 v x hx).1)⟩,
    fun u v x hu hv => (h.1 u x hu).2.symm.trans (h.1 v x hv).2⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨hxP, hxv⟩ := h.1 v x hx
  have hxE := hP x hxP
  have : G.src x ∈ G.V := by
    obtain ⟨e, b⟩ := x
    cases b
    · exact (hG e hxE).2
    · exact (hG e hxE).1
  have := hV _ this
  omega

/-- **The insertions.** Along the insertion edits of distinct new edges, with the ends present
before them being ends of other edges, `OrdUniqueWithin` holds after every prefix. -/
theorem outInsertEdits_allPrefixes {vCap eCap : ℕ} (G : MGraph) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap) (t : ℕ → List End) :
    ∀ (I : List Update) (Pres : Finset End) (A : ℕ → List End), InsInv G.src Pres A →
      (∀ x ∈ Pres, x.1 ∈ G.E) → (insertedEdges I).Nodup →
      (∀ e ∈ insertedEdges I, e ∈ G.E ∧ ∀ b, (e, b) ∉ Pres) →
      AllPrefixes (OrdUniqueWithin vCap eCap) A (outInsertEdits t G.src I) ∧
        InsInv G.src (Pres ∪ (insertedEdges I).toFinset.biUnion fun e => {(e, true), (e, false)})
          (applyOrdEdits A (outInsertEdits t G.src I))
  | [], Pres, A, hA, hP, _, _ => by
    refine ⟨allPrefixes_nil (ordUniqueWithin_of_insInv hA hP hG hV hE), ?_⟩
    simpa [insertedEdges, outInsertEdits, applyOrdEdits] using hA
  | .insert e a b :: I, Pres, A, hA, hP, hnd, hnew => by
    simp only [insertedEdges, List.nodup_cons] at hnd
    have hn := hnew e (by simp [insertedEdges])
    have hQ := ordUniqueWithin_of_insInv (vCap := vCap) (eCap := eCap) hA hP hG hV hE
    set y₁ := cycNextWith (t (G.src (e, true))) (fun z => !decide (z.1 ∈ e :: insertedEdges I))
      (e, true)
    set y₂ := cycNextWith (t (G.src (e, false)))
      (fun z => (!decide (z.1 ∈ e :: insertedEdges I)) || z == (e, true)) (e, false)
    have hA1 := insInv_insert hA (hn.2 true) y₁
    have hA2 := insInv_insert (x := (e, false)) hA1 (fun h => by
      rcases Finset.mem_insert.mp h with h | h
      · simp at h
      · exact hn.2 false h) y₂
    have hQ1 := ordUniqueWithin_of_insInv (vCap := vCap) (eCap := eCap) hA1
      (fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hn.1
        · exact hP x hx) hG hV hE
    have hP2 : ∀ x ∈ insert (e, false) (insert (e, true) Pres), x.1 ∈ G.E := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hn.1
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hn.1
      · exact hP x hx
    obtain ⟨ih1, ih2⟩ := outInsertEdits_allPrefixes G hG hV hE t I _ _ hA2 hP2 hnd.2 (by
      intro f hf
      refine ⟨(hnew f (by simp [insertedEdges, hf])).1, fun b' hb' => ?_⟩
      have hfe : f ≠ e := fun h => hnd.1 (h ▸ hf)
      rcases Finset.mem_insert.mp hb' with h | hb'
      · exact hfe (congrArg Prod.fst h)
      rcases Finset.mem_insert.mp hb' with h | hb'
      · exact hfe (congrArg Prod.fst h)
      · exact (hnew f (by simp [insertedEdges, hf])).2 b' hb')
    refine ⟨allPrefixes_cons hQ (allPrefixes_cons hQ1 ih1), ?_⟩
    have hset : insert (e, false) (insert (e, true) Pres) ∪
        ((insertedEdges I).toFinset.biUnion fun e => {(e, true), (e, false)}) =
        Pres ∪ ((e :: insertedEdges I).toFinset.biUnion fun e => {(e, true), (e, false)}) := by
      ext z
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
        List.mem_cons, Finset.mem_singleton]
      constructor
      · rintro ((h | h | h) | ⟨f, hf, h⟩)
        · exact Or.inr ⟨e, Or.inl rfl, Or.inr h⟩
        · exact Or.inr ⟨e, Or.inl rfl, Or.inl h⟩
        · exact Or.inl h
        · exact Or.inr ⟨f, Or.inr hf, h⟩
      · rintro (h | ⟨f, rfl | hf, h | h⟩)
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨f, hf, Or.inl h⟩
        · exact Or.inr ⟨f, hf, Or.inr h⟩
    show InsInv G.src (Pres ∪ (e :: insertedEdges I).toFinset.biUnion
      fun e => {(e, true), (e, false)}) (applyOrdEdits (applyOrdEdit (applyOrdEdit A
        (.insertBefore (G.src (e, true)) (e, true) y₁)) (.insertBefore (G.src (e, false)) (e, false)
          y₂)) (outInsertEdits t G.src I))
    rw [← hset]
    exact ih2
  | .delete _ :: I, Pres, A, hA, hP, hnd, hnew => by
    simpa [insertedEdges, outInsertEdits] using
      outInsertEdits_allPrefixes G hG hV hE t I Pres A hA hP hnd
        (by simpa [insertedEdges] using hnew)
  | .split .. :: I, Pres, A, hA, hP, hnd, hnew => by
    simpa [insertedEdges, outInsertEdits] using
      outInsertEdits_allPrefixes G hG hV hE t I Pres A hA hP hnd
        (by simpa [insertedEdges] using hnew)

/-! ## The `rotateTo` edits -/

theorem rotateToList_perm (y : End) (xs : List End) : (rotateToList y xs).Perm xs := by
  unfold rotateToList
  split
  · exact (List.perm_append_comm).trans (by rw [List.take_append_drop])
  · exact List.Perm.refl _

/-- **The `rotateTo` edits** keep `InsInv`, so `OrdUniqueWithin` holds after every prefix. -/
theorem outRotateEdits_allPrefixes {vCap eCap : ℕ} (G : MGraph) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap) (t : ℕ → List End) (Pres : Finset End)
    (hP : ∀ x ∈ Pres, x.1 ∈ G.E) :
    ∀ (T : List ℕ) (A : ℕ → List End), InsInv G.src Pres A →
      AllPrefixes (OrdUniqueWithin vCap eCap) A (outRotateEdits t T)
  | [], A, hA => allPrefixes_nil (ordUniqueWithin_of_insInv hA hP hG hV hE)
  | v :: T, A, hA => by
    have hstep : ∀ y, InsInv G.src Pres (applyOrdEdit A (.rotateTo v y)) := by
      intro y
      constructor
      · intro w x hx
        simp only [applyOrdEdit] at hx
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self] at hx
          exact hA.1 w x ((rotateToList_perm y (A w)).mem_iff.mp hx)
        · rw [Function.update_of_ne hw] at hx
          exact hA.1 w x hx
      · intro w
        simp only [applyOrdEdit]
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self]
          exact (rotateToList_perm y (A w)).nodup_iff.mpr (hA.2 w)
        · rw [Function.update_of_ne hw]; exact hA.2 w
    simp only [outRotateEdits]
    have hQ := ordUniqueWithin_of_insInv (vCap := vCap) (eCap := eCap) hA hP hG hV hE
    split
    · exact allPrefixes_append (allPrefixes_nil hQ)
        (outRotateEdits_allPrefixes G hG hV hE t Pres hP T A hA)
    · rename_i y r _
      refine allPrefixes_append (allPrefixes_cons hQ (allPrefixes_nil
        (ordUniqueWithin_of_insInv (hstep y) hP hG hV hE))) ?_
      exact outRotateEdits_allPrefixes G hG hV hE t Pres hP T _ (hstep y)

/-! ## Names of the insertion and rotation edits -/

theorem mem_of_cycNextWith {l : List End} {P : End → Bool} {x y : End}
    (h : cycNextWith l P x = some y) : y ∈ l := by
  unfold cycNextWith afterEnd at h
  have hy := List.mem_of_find?_eq_some h
  rcases List.mem_append.mp hy with hy | hy
  · exact List.mem_of_mem_drop hy
  · exact (List.takeWhile_sublist _).subset hy

theorem ordEditsWithin_append {vCap eCap : ℕ} {ds ds' : List OrdEdit}
    (h : OrdEditsWithin vCap eCap ds) (h' : OrdEditsWithin vCap eCap ds') :
    OrdEditsWithin vCap eCap (ds ++ ds') := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact h d hd
  · exact h' d hd

/-- The insertion edits name small vertices and edges, when the new order `t` holds the ends of
`G`. -/
theorem outInsertEdits_within {vCap eCap : ℕ} (G : MGraph) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap) (t : ℕ → List End)
    (ht : ∀ v x, x ∈ t v → x.1 ∈ G.E) :
    ∀ I : List Update, (∀ e ∈ insertedEdges I, e ∈ G.E) →
      OrdEditsWithin vCap eCap (outInsertEdits t G.src I)
  | [], _ => fun _ h => by simp [outInsertEdits] at h
  | .insert e a b :: I, hI => by
    have he : e ∈ G.E := hI e (by simp [insertedEdges])
    have ih := outInsertEdits_within G hG hV hE t ht I
      (fun f hf => hI f (by simp [insertedEdges, hf]))
    have hsrc : ∀ c : Bool, G.src (e, c) < vCap := by
      intro c
      cases c
      · exact hV _ (hG e he).2
      · exact hV _ (hG e he).1
    intro d hd
    simp only [outInsertEdits, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · refine ⟨hsrc true, hE e he, fun y' hy' => ?_⟩
      exact hE _ (ht _ _ (mem_of_cycNextWith (Option.mem_def.mp hy')))
    · refine ⟨hsrc false, hE e he, fun y' hy' => ?_⟩
      exact hE _ (ht _ _ (mem_of_cycNextWith (Option.mem_def.mp hy')))
    · exact ih d hd
  | .delete _ :: I, hI => by
    simpa [outInsertEdits] using outInsertEdits_within G hG hV hE t ht I
      (fun f hf => hI f (by simpa [insertedEdges] using hf))
  | .split .. :: I, hI => by
    simpa [outInsertEdits] using outInsertEdits_within G hG hV hE t ht I
      (fun f hf => hI f (by simpa [insertedEdges] using hf))

/-- The `rotateTo` edits name small vertices and edges. -/
theorem outRotateEdits_within {vCap eCap : ℕ} (t : ℕ → List End)
    (ht : ∀ v x, x ∈ t v → x.1 < eCap) :
    ∀ T : List ℕ, (∀ v ∈ T, v < vCap) → OrdEditsWithin vCap eCap (outRotateEdits t T)
  | [], _ => fun _ h => by simp [outRotateEdits] at h
  | v :: T, hT => by
    simp only [outRotateEdits]
    refine ordEditsWithin_append ?_
      (outRotateEdits_within t ht T (fun w hw => hT w (List.mem_cons_of_mem _ hw)))
    cases htv : t v with
    | nil => intro d hd; simp at hd
    | cons y r =>
      intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      exact ⟨hT v List.mem_cons_self, ht v y (by rw [htv]; exact List.mem_cons_self)⟩

/-! ## The edits of an output step -/

theorem isValid_applyBatch : ∀ {G : MGraph} (W : List Update), G.IsValid → G.BatchIsValid W →
    (G.applyBatch W).IsValid
  | _, [], hG, _ => hG
  | _, _ :: W, hG, hW => isValid_applyBatch W (isValid_applyUpdate_of_notInsert hG hW.1) hW.2

/-- A valid batch of insertions inserts edges that are not in the graph, keeps the edges of the
graph and their ends. -/
theorem insertBatch_facts : ∀ {G : MGraph} (I : List Update), G.BatchIsValid I →
    (∀ u ∈ I, Update.IsInsert u) →
    (∀ e ∈ insertedEdges I, e ∉ G.E) ∧ G.E ⊆ (G.applyBatch I).E ∧
      ∀ x : End, x.1 ∈ G.E → (G.applyBatch I).src x = G.src x
  | _, [], _, _ => ⟨fun e he => by simp [insertedEdges] at he, le_refl _, fun _ _ => rfl⟩
  | G, .insert e a b :: I, hv, hI => by
    obtain ⟨h1, h2, h3⟩ := insertBatch_facts (G := G.applyUpdate (.insert e a b)) I hv.2
      (fun u hu => hI u (List.mem_cons_of_mem _ hu))
    have hsub : G.E ⊆ (G.applyUpdate (.insert e a b)).E := Finset.subset_insert _ _
    refine ⟨?_, hsub.trans h2, ?_⟩
    · intro f hf
      simp only [insertedEdges, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact hv.1.1
      · exact fun hfG => h1 f hf (hsub hfG)
    · intro x hx
      have hne : x.1 ≠ e := fun h => hv.1.1 (h ▸ hx)
      rw [show G.applyBatch (.insert e a b :: I) = (G.applyUpdate (.insert e a b)).applyBatch I
        from rfl, h3 x (hsub hx)]
      obtain ⟨f, c⟩ := x
      cases c <;> simp [MGraph.src, MGraph.applyUpdate, Function.update_of_ne hne]
  | _, .delete _ :: _, _, hI => absurd (hI _ List.mem_cons_self) id
  | _, .split .. :: _, _, hI => absurd (hI _ List.mem_cons_self) id

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- The vertices of the new output graph are the new roots. -/
theorem outStep_V (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') :
    (stepBundleTree sparsify st U ord ord').state.S_cur.V =
      (stepBundleTree sparsify st U ord ord').state.cs.RF.R := by
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, hrot⟩, hS_val, hS_V, hS_sub, hS_sub'⟩ := hready
  have hspec := buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hS_sub'.2.1
    (stepBundleTree sparsify st U ord ord').D_total
  have hS : (stepBundleTree sparsify st U ord ord').state.S_cur =
      st.S_cur.applyBatch (stepBundleTree sparsify st U ord ord').U_S := rfl
  have hcs : (stepBundleTree sparsify st U ord ord').state.cs = compLSFBatch st.cs U := rfl
  rw [hS, hcs, stepBundleTree_U_S_eq]
  exact hspec.2.2.1

/-- **The edits of an output step can be sent to the order store.** They name vertices below
`vCap` and edges below `eCap`, and after every prefix every end is in at most one list, with no
repeats. -/
theorem outStepEditsSmall_valid {vCap eCap : ℕ} (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') (T₀ : List ℕ)
    (hR : ∀ v ∈ (stepBundleTree sparsify st U ord ord').state.cs.RF.R, v < vCap)
    (hE : ∀ e ∈ st.S_cur.E, e < eCap)
    (hE' : ∀ e ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.E, e < eCap)
    (hT : ∀ v ∈ T₀, v < vCap) :
    OrdEditsWithin vCap eCap (outStepEditsSmall sparsify st U ord ord' T₀) ∧
      OrdEditsUniqueWithin vCap eCap (st.outOrder ord)
        (outStepEditsSmall sparsify st U ord ord' T₀) := by
  have hmem := ordMemOf_outOrder sparsify st U ord ord' hready
  have hV' : ∀ v ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.V, v < vCap := by
    rw [outStep_V sparsify st U ord ord' hready]; exact hR
  obtain ⟨ρS, -, hρ, -, -, hBV⟩ := outStep_rotations sparsify st U ord ord' hready
  obtain ⟨-, -, -, -, -, hS_val, -⟩ := hready
  have hsplit := stepBundleTree_U_S_split sparsify st U ord ord'
  rw [hsplit, batchIsValid_append] at hBV
  obtain ⟨hvP, hvI⟩ := hBV
  set P := outPrefixBatch sparsify st U ord ord' with hP
  set I := outInsBatch sparsify st U ord ord' with hIdef
  set S' := (stepBundleTree sparsify st U ord ord').state.S_cur with hS'def
  set t := (stepBundleTree sparsify st U ord ord').state.outOrder ord' with htdef
  set GP := st.S_cur.applyBatch P with hGP
  have hS'eq : S' = GP.applyBatch I := by
    show st.S_cur.applyBatch (stepBundleTree sparsify st U ord ord').U_S = _
    rw [hsplit, applyBatch_append]
  have hIins : ∀ u ∈ I, Update.IsInsert u := by
    intro u hu
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hu
    exact trivial
  have hGP_val := isValid_applyBatch P hS_val hvP
  have hS'_val : S'.IsValid := hS'eq ▸ isValid_applyBatch I hGP_val hvI
  obtain ⟨hnotin, hEsub, hsrcEq⟩ := insertBatch_facts I hvI hIins
  have hinsE : ∀ e ∈ insertedEdges I, e ∈ S'.E := by
    intro e he
    rw [hIdef, outInsBatch, insertedEdges_map_insert', outInsList, Finset.mem_sort] at he
    exact (Finset.mem_sdiff.mp he).1
  have hVGP : ∀ v ∈ GP.applyBatch [] |>.V, v < vCap := fun v hv =>
    hV' v (hS'eq ▸ V_subset_applyBatch GP I hv)
  -- the deletions and splits
  obtain ⟨hA1, hmemP, hndP⟩ := outPrefixEditsOn_allPrefixes (vCap := vCap) (eCap := eCap) P st.S_cur
    (st.outOrder ord) hmem.1 (fun v => hρ ▸ ρS.nodup v) hS_val hvP
    (notInsert_prefix sparsify st U ord ord') hVGP hE
  -- the insertions
  set Pres₀ : Finset End := GP.E.biUnion fun e => {(e, true), (e, false)} with hPres₀
  have hmemPres : ∀ x : End, x ∈ Pres₀ ↔ x.1 ∈ GP.E := by
    intro x
    simp only [hPres₀, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨e, he, rfl | rfl⟩ <;> exact he
    · intro hx
      obtain ⟨e, c⟩ := x
      cases c
      · exact ⟨e, hx, Or.inr rfl⟩
      · exact ⟨e, hx, Or.inl rfl⟩
  have hInv0 : InsInv S'.src Pres₀ (applyOrdEdits (st.outOrder ord) (outPrefixEditsOn st.S_cur P)) := by
    refine ⟨fun v x hx => ?_, hndP⟩
    obtain ⟨hxE, hxv⟩ := (hmemP v x).mp hx
    refine ⟨(hmemPres x).mpr hxE, ?_⟩
    rw [hS'eq, hsrcEq x hxE]
    exact hxv
  have hP0 : ∀ x ∈ Pres₀, x.1 ∈ S'.E := fun x hx => hS'eq ▸ hEsub ((hmemPres x).mp hx)
  have hnd : (insertedEdges I).Nodup := by
    rw [hIdef, outInsBatch, insertedEdges_map_insert']
    exact Finset.sort_nodup _ _
  obtain ⟨hA2, hInv1⟩ := outInsertEdits_allPrefixes (vCap := vCap) (eCap := eCap) S' hS'_val hV' hE'
    t I Pres₀ _ hInv0 hP0 hnd (fun e he => ⟨hinsE e he, fun b hb =>
      hnotin e he ((hmemPres (e, b)).mp hb)⟩)
  have hP1 : ∀ x ∈ Pres₀ ∪ (insertedEdges I).toFinset.biUnion (fun e => {(e, true), (e, false)}),
      x.1 ∈ S'.E := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hP0 x hx
    · obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
      have he' := hinsE e (List.mem_toFinset.mp he)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      rcases hxe with rfl | rfl <;> exact he'
  have hA3 := outRotateEdits_allPrefixes (vCap := vCap) (eCap := eCap) S' hS'_val hV' hE' t _ hP1 T₀ _
    hInv1
  have ht : ∀ v x, x ∈ t v → x.1 ∈ S'.E := fun v x hx => ((hmem.2 v x).mp hx).1
  constructor
  · unfold outStepEditsSmall
    refine ordEditsWithin_append (ordEditsWithin_append
      (outPrefixEditsOn_within P st.S_cur hvP (notInsert_prefix sparsify st U ord ord') hVGP hE)
      (outInsertEdits_within S' hS'_val hV' hE' t ht I hinsE))
      (outRotateEdits_within t (fun v x hx => hE' _ (ht v x hx)) T₀ hT)
  · unfold outStepEditsSmall
    refine allPrefixes_append (allPrefixes_append hA1 hA2) ?_
    rw [applyOrdEdits_append']
    exact hA3

end MinCostFlow.SparseCore.Program
