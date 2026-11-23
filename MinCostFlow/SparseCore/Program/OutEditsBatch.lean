module

public import MinCostFlow.SparseCore.Program.OutEditsList
import MinCostFlow.Bundle.Cyclic

/-!
# Order edits along an ordered batch

An ordered batch (`RotationBatch`) says how the order of ends at
each vertex changes, but only up to rotation of each list, and it does not say where an inserted
end goes. This file turns a batch of the shape of the output batch `buildUSOrd` (deletions and
splits, then insertions) into explicit edits of the order (`OrdEdit`), and proves that the edits
give the new order.

* A deletion of `e` becomes `dropEdge e`, and a split of `v` becomes `moveEnds v v' sel false`
  with `sel` the moved ends (`splitSel`). Along the deletions and splits, each list stays a
  rotation of the list of the rotation at that point.
* An insertion of `e` becomes two `insertBefore` edits, one for each end of `e`. Each end goes
  before the next end after it, in the new list, that is already present
  (`outInsertEdits`). After the insertions, each list is a rotation of the new list
  (`outBaseEdits_isRotated`).
* Last, `rotateTo v y` with `y` the first end of the new list at `v`, for each `v` of a list `T`,
  makes the list at `v` equal to the new list (`outRotateEdits_apply`). At a vertex whose new list
  is empty, the list is already empty.

The main result is `outEdits_eq`: when `T` holds every vertex whose new list is not empty, the
edits give exactly the new order.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

/-! ## The edits -/

/-- The ends that a split moves, as a set: the tails of `St` and the heads of `Sh`. -/
def splitSel (St Sh : Finset ℕ) : Finset End :=
  St.image (fun e => (e, true)) ∪ Sh.image (fun e => (e, false))

theorem movedBy_splitSel (St Sh : Finset ℕ) (x : End) :
    movedBy (splitSel St Sh) false x = splitEnds St Sh x := by
  obtain ⟨e, b⟩ := x
  cases b <;> simp [movedBy, splitSel, splitEnds]

/-- The update is not an insertion. -/
def Update.NotInsert : Update → Prop
  | .insert .. => False
  | _ => True

/-- The update is an insertion. -/
def Update.IsInsert : Update → Prop
  | .insert .. => True
  | _ => False

/-- The edits of the deletions and splits of a batch. -/
def outPrefixEdits : List Update → List OrdEdit
  | [] => []
  | .delete e :: U => .dropEdge e :: outPrefixEdits U
  | .split v v' St Sh :: U => .moveEnds v v' (splitSel St Sh) false :: outPrefixEdits U
  | .insert .. :: U => outPrefixEdits U

/-- The edges that the insertions of a batch insert, in order. -/
def insertedEdges : List Update → List ℕ
  | [] => []
  | .insert e _ _ :: U => e :: insertedEdges U
  | _ :: U => insertedEdges U

/-- The edits of the insertions of a batch, for the new order `t` and the vertex `src x` of each
new end `x`. The tail end of `e` goes before the next end after it in `t (src (e, true))` whose
edge is not inserted by this or a later insertion. The head end goes before the next such end,
where the tail end of `e` now counts as present. -/
def outInsertEdits (t : ℕ → List End) (src : End → ℕ) : List Update → List OrdEdit
  | [] => []
  | .insert e _ _ :: U =>
    let pres : End → Bool := fun z => !decide (z.1 ∈ e :: insertedEdges U)
    .insertBefore (src (e, true)) (e, true) (cycNextWith (t (src (e, true))) pres (e, true)) ::
    .insertBefore (src (e, false)) (e, false)
      (cycNextWith (t (src (e, false))) (fun z => pres z || z == (e, true)) (e, false)) ::
    outInsertEdits t src U
  | _ :: U => outInsertEdits t src U

/-- The `rotateTo` edits that make the lists at the vertices of `T` start where `t` starts. -/
def outRotateEdits (t : ℕ → List End) : List ℕ → List OrdEdit
  | [] => []
  | v :: T =>
    (match t v with
      | [] => []
      | y :: _ => [.rotateTo v y]) ++ outRotateEdits t T

/-! ## Insertions -/

private theorem applyOrdEdits_cons (A : ℕ → List End) (d : OrdEdit) (ds : List OrdEdit) :
    applyOrdEdits A (d :: ds) = applyOrdEdits (applyOrdEdit A d) ds := rfl

private theorem applyOrdEdits_append (A : ℕ → List End) (ds ds' : List OrdEdit) :
    applyOrdEdits A (ds ++ ds') = applyOrdEdits (applyOrdEdits A ds) ds' := by
  simp [applyOrdEdits, List.foldl_append]

/-- One insertion step at the vertex `a` of the new end `x`: every list stays a rotation of the
new list restricted to the present ends, now with `x`. -/
private theorem insert_step {t : ℕ → List End} {A : ℕ → List End} {P : End → Bool} {x : End}
    {a : ℕ} (ht : ∀ v, (t v).Nodup) (huniq : ∀ v w z, z ∈ t v → z ∈ t w → v = w)
    (hx : x ∈ t a) (hPx : P x = false) (hA : ∀ v, (A v).IsRotated ((t v).filter P)) :
    ∀ v, (applyOrdEdit A (.insertBefore a x (cycNextWith (t a) P x)) v).IsRotated
      ((t v).filter fun z => P z || z == x) := by
  intro v
  simp only [applyOrdEdit]
  by_cases hv : v = a
  · subst hv
    rw [Function.update_self]
    exact insert_before_cycNext_isRotated' (ht v) hx hPx (hA v)
  · rw [Function.update_of_ne hv]
    have hcongr : ((t v).filter fun z => P z || z == x) = (t v).filter P := by
      apply List.filter_congr
      intro z hz
      have hzx : (z == x) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hv (huniq _ _ _ hz hx)
      simp [hzx]
    rw [hcongr]
    exact hA v
where
  insert_before_cycNext_isRotated' {t xs : List End} {P : End → Bool} {x : End}
      (ht : t.Nodup) (hx : x ∈ t) (hPx : P x = false) (h : xs.IsRotated (t.filter P)) :=
    insertBefore_cycNext_isRotated ht hx hPx h

/-- **The insertions.** If every list is a rotation of the new list `t` without the ends of the
inserted edges, then the edits of the insertions make every list a rotation of `t`. Each new end
`x` must be in `t (src x)`, each end lies in at most one list of `t`, and the inserted edges are
distinct. -/
theorem outInsertEdits_isRotated {t : ℕ → List End} {src : End → ℕ}
    (ht : ∀ v, (t v).Nodup) (huniq : ∀ v w z, z ∈ t v → z ∈ t w → v = w) :
    ∀ (I : List Update) (A : ℕ → List End), (insertedEdges I).Nodup →
      (∀ e ∈ insertedEdges I, (e, true) ∈ t (src (e, true)) ∧ (e, false) ∈ t (src (e, false))) →
      (∀ v, (A v).IsRotated ((t v).filter fun z => !decide (z.1 ∈ insertedEdges I))) →
      ∀ v, (applyOrdEdits A (outInsertEdits t src I) v).IsRotated (t v)
  | [], A, _, _, hA => fun v => by simpa [outInsertEdits, applyOrdEdits, insertedEdges] using hA v
  | .delete _ :: I, A, hnd, hsrc, hA => outInsertEdits_isRotated ht huniq I A hnd hsrc hA
  | .split .. :: I, A, hnd, hsrc, hA => outInsertEdits_isRotated ht huniq I A hnd hsrc hA
  | .insert e a b :: I, A, hnd, hsrc, hA => by
    simp only [insertedEdges] at hnd hsrc hA
    obtain ⟨heI, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hxt, hyt⟩ := hsrc e List.mem_cons_self
    let pres : End → Bool := fun z => !decide (z.1 ∈ e :: insertedEdges I)
    have h1 := insert_step ht huniq hxt (P := pres) (by simp [pres]) hA
    have h2 := insert_step ht huniq hyt
      (P := fun z => pres z || z == (e, true)) (by simp [pres]) h1
    have hcongr : ∀ v, ((t v).filter fun z => (pres z || z == (e, true)) || z == (e, false)) =
        (t v).filter fun z => !decide (z.1 ∈ insertedEdges I) := by
      intro v
      apply List.filter_congr
      rintro ⟨f, c⟩ _
      by_cases hf : f = e
      · subst hf
        cases c <;> simp [heI]
      · have hx1 : ((f, c) == (e, true)) = false := beq_eq_false_iff_ne.mpr (by simp [hf])
        have hx2 : ((f, c) == (e, false)) = false := beq_eq_false_iff_ne.mpr (by simp [hf])
        simp [pres, hf, hx1, hx2]
    simp only [outInsertEdits, applyOrdEdits_cons]
    exact outInsertEdits_isRotated ht huniq I _ hnd'
      (fun f hf => hsrc f (List.mem_cons_of_mem _ hf)) (fun v => hcongr v ▸ h2 v)

/-- Along a batch of insertions, the new lists without the inserted ends are rotations of the old
lists. -/
theorem rotationBatch_inserts_filter {β : ℕ} :
    ∀ (I : List Update) {G : MGraph} (ρ : Rotation G) (σ : Rotation (G.applyBatch I)),
      (∀ u ∈ I, Update.IsInsert u) → RotationBatch β I ρ σ →
      ∀ v, ((σ.order v).filter fun z => !decide (z.1 ∈ insertedEdges I)).IsRotated (ρ.order v)
  | [], _, ρ, σ, _, h => by
    cases h with
    | nil hρ => intro v; simpa [insertedEdges] using hρ v
  | .delete _ :: _, _, _, _, hI, _ => absurd (hI _ List.mem_cons_self) (by simp [Update.IsInsert])
  | .split .. :: _, _, _, _, hI, _ => absurd (hI _ List.mem_cons_self) (by simp [Update.IsInsert])
  | .insert e a b :: I, _, ρ, σ, hI, h => by
    cases h with
    | cons hs hb =>
      intro v
      have ih := rotationBatch_inserts_filter I _ σ
        (fun u hu => hI u (List.mem_cons_of_mem _ hu)) hb v
      have h1 := isRotated_filter (fun x : End => x.1 != e) ih
      rw [List.filter_filter] at h1
      have hcongr : ((σ.order v).filter fun z => !decide (z.1 ∈ insertedEdges (.insert e a b :: I))) =
          (σ.order v).filter fun z => (z.1 != e) && (!decide (z.1 ∈ insertedEdges I)) := by
        apply List.filter_congr
        intro z _
        simp only [insertedEdges, List.mem_cons]
        by_cases hz : z.1 = e <;> simp [hz]
      rw [hcongr]
      exact h1.trans (hs v)

/-! ## Deletions and splits -/

/-- **The edits of a batch of the output shape.** Let `P` be deletions and splits and `I`
insertions, with a valid ordered batch `P ++ I` from `ρ` to `σ`. If every list of `A` is a
rotation of the list of `ρ`, then the edits of `P` and of `I` (placed by `σ`) make every list a
rotation of the list of `σ`. The new ends are at their vertices in `σ` (`src`), and the inserted
edges are distinct. -/
theorem outBaseEdits_isRotated {β : ℕ} (src : End → ℕ) :
    ∀ (P I : List Update) {G : MGraph} (ρ : Rotation G) (σ : Rotation (G.applyBatch (P ++ I)))
      (A : ℕ → List End), RotationBatch β (P ++ I) ρ σ → G.BatchIsValid (P ++ I) →
      (∀ u ∈ P, Update.NotInsert u) → (∀ u ∈ I, Update.IsInsert u) →
      (insertedEdges I).Nodup →
      (∀ e ∈ insertedEdges I, (e, true) ∈ σ.order (src (e, true)) ∧
        (e, false) ∈ σ.order (src (e, false))) →
      (∀ v, (A v).IsRotated (ρ.order v)) →
      ∀ v, (applyOrdEdits A (outPrefixEdits P ++ outInsertEdits σ.order src I) v).IsRotated
        (σ.order v)
  | [], I, G, ρ, σ, A, h, _, _, hI, hnd, hsrc, hA => by
    have hσ := rotationBatch_inserts_filter I ρ σ hI h
    have huniq : ∀ v w z, z ∈ σ.order v → z ∈ σ.order w → v = w := fun v w z hv hw =>
      ((σ.mem_order v z).mp hv).2.symm.trans ((σ.mem_order w z).mp hw).2
    exact outInsertEdits_isRotated σ.nodup huniq I A hnd hsrc
      (fun v => (hA v).trans (hσ v).symm)
  | .insert .. :: _, _, _, _, _, _, _, _, hP, _, _, _, _ =>
    absurd (hP _ List.mem_cons_self) (by simp [Update.NotInsert])
  | .delete e :: P, I, G, ρ, σ, A, h, hval, hP, hI, hnd, hsrc, hA => by
    cases h with
    | @cons _ _ _ _ ρ' _ hs hb =>
      have hA' : ∀ v, (applyOrdEdit A (.dropEdge e) v).IsRotated (ρ'.order v) :=
        fun v => (isRotated_filter (fun x : End => x.1 != e) (hA v)).trans (hs v).symm
      simp only [outPrefixEdits, List.cons_append, applyOrdEdits_cons]
      exact outBaseEdits_isRotated src P I _ σ _ hb hval.2
        (fun u hu => hP u (List.mem_cons_of_mem _ hu)) hI hnd hsrc hA'
  | .split v v' St Sh :: P, I, G, ρ, σ, A, h, hval, hP, hI, hnd, hsrc, hA => by
    cases h with
    | @cons _ _ _ _ ρ' _ hs hb =>
      obtain ⟨h1, h2, _, h4⟩ := hs
      have hvv : v ≠ v' := fun he => hval.1.2.1 (he ▸ hval.1.1)
      -- the list of the new vertex is empty before the split
      have hρv' : ρ.order v' = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        obtain ⟨hxE, hxs⟩ := (ρ.mem_order v' x).mp hx
        have hx' : x ∈ ρ'.order v' := by
          refine (ρ'.mem_order v' x).mpr ⟨hxE, ?_⟩
          rw [src_applySplit, ite_eq_right (fun hc => hvv (hc.1.symm.trans hxs))]
          exact hxs
        have := (h2.mem_iff.mp hx')
        obtain ⟨hxv, -⟩ := List.mem_filter.mp this
        exact hvv (((ρ.mem_order v x).mp hxv).2.symm.trans hxs)
      have hAv' : A v' = [] := List.isRotated_nil_iff.mp (hρv' ▸ hA v')
      have hA' : ∀ u, (applyOrdEdit A (.moveEnds v v' (splitSel St Sh) false) u).IsRotated
          (ρ'.order u) := by
        intro u
        have hmv : movedBy (splitSel St Sh) false = splitEnds St Sh :=
          funext (movedBy_splitSel St Sh)
        simp only [applyOrdEdit, hmv]
        by_cases hu : u = v
        · subst hu; rw [ite_eq_left rfl]
          exact (isRotated_filter _ (hA u)).trans h1.symm
        · rw [ite_eq_right hu]
          by_cases hu' : u = v'
          · subst hu'; rw [ite_eq_left rfl, hAv', List.nil_append]
            exact (isRotated_filter _ (hA v)).trans h2.symm
          · rw [ite_eq_right hu']
            exact (hA u).trans (h4 u hu hu').symm
      simp only [outPrefixEdits, List.cons_append, applyOrdEdits_cons]
      exact outBaseEdits_isRotated src P I ρ' σ _ hb hval.2
        (fun u hu => hP u (List.mem_cons_of_mem _ hu)) hI hnd hsrc hA'

/-! ## Rotations to the start -/

/-- **The `rotateTo` edits.** If every list of `A` is a rotation of the list of `t`, which has no
repeats, then after the `rotateTo` edits of `T` the list at a vertex of `T` is the list of `t`,
and the list at any other vertex is unchanged. -/
theorem outRotateEdits_apply {t : ℕ → List End} (ht : ∀ v, (t v).Nodup) :
    ∀ (T : List ℕ) (A : ℕ → List End), (∀ v, (A v).IsRotated (t v)) →
      ∀ v, applyOrdEdits A (outRotateEdits t T) v = if v ∈ T then t v else A v
  | [], A, _ => fun v => by simp [outRotateEdits, applyOrdEdits]
  | u :: T, A, hA => by
    -- one step sets the list at `u` to `t u`
    have hstep : applyOrdEdits A (match t u with | [] => [] | y :: _ => [.rotateTo u y]) =
        Function.update A u (t u) := by
      funext w
      cases htu : t u with
      | nil =>
        have hAu : A u = [] := List.isRotated_nil_iff.mp (htu ▸ hA u)
        simp only [applyOrdEdits, List.foldl_nil]
        by_cases hw : w = u
        · subst hw; rw [Function.update_self, hAu]
        · rw [Function.update_of_ne hw]
      | cons y r =>
        simp only [applyOrdEdits, List.foldl_cons, List.foldl_nil, applyOrdEdit]
        rw [rotateToList_eq_of_isRotated ((hA u).nodup_iff.mpr (htu ▸ ht u)) (htu ▸ hA u)]
    have hA' : ∀ w, (Function.update A u (t u) w).IsRotated (t w) := by
      intro w
      by_cases hw : w = u
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]; exact hA w
    intro v
    simp only [outRotateEdits]
    rw [applyOrdEdits_append, hstep, outRotateEdits_apply ht T _ hA' v]
    by_cases hvT : v ∈ T
    · simp [hvT]
    · by_cases hv : v = u
      · subst hv; simp [hvT]
      · simp [hvT, hv]

/-- **The edits give the new order.** In the setting of `outBaseEdits_isRotated`, if the list
`T` holds every vertex at which the new order is not empty, then the edits of the deletions and
splits, of the insertions, and the `rotateTo` edits of `T` turn `A` into the new order. -/
theorem outEdits_eq {β : ℕ} (src : End → ℕ) (P I : List Update) {G : MGraph}
    (ρ : Rotation G) (σ : Rotation (G.applyBatch (P ++ I))) (A : ℕ → List End)
    (h : RotationBatch β (P ++ I) ρ σ) (hval : G.BatchIsValid (P ++ I))
    (hP : ∀ u ∈ P, Update.NotInsert u) (hI : ∀ u ∈ I, Update.IsInsert u)
    (hnd : (insertedEdges I).Nodup)
    (hsrc : ∀ e ∈ insertedEdges I, (e, true) ∈ σ.order (src (e, true)) ∧
      (e, false) ∈ σ.order (src (e, false)))
    (hA : ∀ v, (A v).IsRotated (ρ.order v)) (T : List ℕ) (hT : ∀ v, σ.order v ≠ [] → v ∈ T) :
    applyOrdEdits A (outPrefixEdits P ++ outInsertEdits σ.order src I ++ outRotateEdits σ.order T) =
      σ.order := by
  have hbase := outBaseEdits_isRotated src P I ρ σ A h hval hP hI hnd hsrc hA
  funext v
  rw [applyOrdEdits_append, outRotateEdits_apply σ.nodup T _ hbase v]
  split
  · rfl
  · rename_i hvT
    have hσv : σ.order v = [] := by
      by_contra hne; exact hvT (hT v hne)
    have := hbase v
    rw [hσv] at this ⊢
    exact List.isRotated_nil_iff.mp this

end MinCostFlow.SparseCore.Program
