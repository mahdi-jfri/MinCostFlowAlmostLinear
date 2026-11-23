module

public import MinCostFlow.SparseCore.Program.OutStepSpec

/-!
# Edits of orders at a vertex they do not name

The list `T₀` of a branch step must hold every vertex at which the edits of the output batch do
not already give the new output list (`OutRotCover`). This file has the part about edits.

An edit of an order changes the list of a vertex only when it names that vertex, except for
`dropEdge`, which removes the ends of one edge everywhere. So at a vertex that no edit names, a
list of edits only filters out the dropped edges (`applyOrdEdits_of_not_mem`).

The edits of the output batch before the rotations (`outBaseEdits`) drop exactly the leaving
output edges. So at a vertex that they do not name, the list that they give is the old output
list, restricted to the output edges that stay (`outBaseOrder_of_not_mem`). The edits name at most
four vertices per update of the output batch (`ordEditVerts_outBaseEdits_card_le`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.SparseCore

/-! ## The vertices that edits name, and the edges they drop -/

/-- The vertices that one edit names. -/
def OrdEdit.verts : OrdEdit → Finset ℕ
  | .dropEdge _ => ∅
  | .moveEnds v v' _ _ => {v, v'}
  | .insertBefore v _ _ => {v}
  | .rotateTo v _ => {v}

/-- The vertices that a list of edits names. -/
def ordEditVerts : List OrdEdit → Finset ℕ
  | [] => ∅
  | d :: ds => d.verts ∪ ordEditVerts ds

/-- The edges that the `dropEdge` edits of a list drop. -/
def ordEditDrops : List OrdEdit → Finset ℕ
  | [] => ∅
  | .dropEdge e :: ds => insert e (ordEditDrops ds)
  | _ :: ds => ordEditDrops ds

theorem ordEditVerts_append : ∀ ds ds' : List OrdEdit,
    ordEditVerts (ds ++ ds') = ordEditVerts ds ∪ ordEditVerts ds'
  | [], _ => by simp [ordEditVerts]
  | d :: ds, ds' => by
    simp only [List.cons_append, ordEditVerts, ordEditVerts_append ds ds', Finset.union_assoc]

theorem ordEditDrops_append : ∀ ds ds' : List OrdEdit,
    ordEditDrops (ds ++ ds') = ordEditDrops ds ∪ ordEditDrops ds'
  | [], _ => by simp [ordEditDrops]
  | d :: ds, ds' => by
    cases d <;>
      simp only [List.cons_append, ordEditDrops, ordEditDrops_append ds ds', Finset.insert_union]

theorem OrdEdit.verts_card_le (d : OrdEdit) : d.verts.card ≤ 2 := by
  cases d with
  | moveEnds v v' sel c => exact (Finset.card_insert_le _ _).trans (by simp)
  | _ => simp [OrdEdit.verts]

/-- A list of edits names at most two vertices per edit. -/
theorem ordEditVerts_card_le : ∀ ds : List OrdEdit, (ordEditVerts ds).card ≤ 2 * ds.length
  | [] => by simp [ordEditVerts]
  | d :: ds => by
    have h1 := Finset.card_union_le d.verts (ordEditVerts ds)
    have h2 := d.verts_card_le
    have h3 := ordEditVerts_card_le ds
    simp only [ordEditVerts, List.length_cons]
    omega

/-- **Edits at a vertex they do not name.** At a vertex `u` that no edit of `ds` names, the edits
only remove the ends of the dropped edges from the list of `u`. -/
theorem applyOrdEdits_of_not_mem : ∀ (A : ℕ → List End) (ds : List OrdEdit) {u : ℕ},
    u ∉ ordEditVerts ds →
      applyOrdEdits A ds u = (A u).filter fun x => decide (x.1 ∉ ordEditDrops ds)
  | A, [], u, _ => by simp [applyOrdEdits, ordEditDrops]
  | A, d :: ds, u, hu => by
    have hu₁ : u ∉ d.verts := fun h => hu (Finset.mem_union_left _ h)
    have hu₂ : u ∉ ordEditVerts ds := fun h => hu (Finset.mem_union_right _ h)
    -- the first edit, then the rest
    change applyOrdEdits (applyOrdEdit A d) ds u = _
    rw [applyOrdEdits_of_not_mem _ ds hu₂]
    cases d with
    | dropEdge e =>
      simp only [applyOrdEdit, List.filter_filter, ordEditDrops, Finset.mem_insert]
      refine List.filter_congr fun x _ => ?_
      by_cases hx : x.1 = e <;> simp [hx]
    | moveEnds v v' sel c =>
      have hv : u ≠ v := fun h => hu₁ (by simp [OrdEdit.verts, h])
      have hv' : u ≠ v' := fun h => hu₁ (by simp [OrdEdit.verts, h])
      simp only [applyOrdEdit, hv, hv', ↓reduceIte]
      rfl
    | insertBefore v x y =>
      have hv : u ≠ v := fun h => hu₁ (by simp [OrdEdit.verts, h])
      simp only [applyOrdEdit, Function.update_of_ne hv]
      rfl
    | rotateTo v y =>
      have hv : u ≠ v := fun h => hu₁ (by simp [OrdEdit.verts, h])
      simp only [applyOrdEdit, Function.update_of_ne hv]
      rfl

/-! ## The edits of the output batch -/

/-- The edits of the deletions and splits name only their split vertices, and drop exactly the
deleted edges. -/
private theorem ordEditDrops_outPrefixEdits : ∀ (P : List Update) (e : ℕ),
    e ∈ ordEditDrops (outPrefixEdits P) ↔ Update.delete e ∈ P
  | [], e => by simp [outPrefixEdits, ordEditDrops]
  | u :: P, e => by
    have ih := ordEditDrops_outPrefixEdits P e
    cases u with
    | insert e' a b => simp [outPrefixEdits, ih]
    | delete e' =>
      simp only [outPrefixEdits, ordEditDrops, Finset.mem_insert, ih, List.mem_cons,
        Update.delete.injEq]
    | split v v' St Sh => simp [outPrefixEdits, ordEditDrops, ih]

/-- The edits of the insertions drop no edge. -/
private theorem ordEditDrops_outInsertEdits (t : ℕ → List End) (src : End → ℕ) :
    ∀ I : List Update, ordEditDrops (outInsertEdits t src I) = ∅
  | [] => rfl
  | u :: I => by
    cases u with
    | insert e a b => simp only [outInsertEdits, ordEditDrops, ordEditDrops_outInsertEdits t src I]
    | delete e => exact ordEditDrops_outInsertEdits t src I
    | split v v' St Sh => exact ordEditDrops_outInsertEdits t src I

private theorem outPrefixEdits_length_le : ∀ P : List Update, (outPrefixEdits P).length ≤ P.length
  | [] => le_rfl
  | u :: P => by
    have ih := outPrefixEdits_length_le P
    cases u <;> simp only [outPrefixEdits, List.length_cons] <;> omega

private theorem outInsertEdits_length_le (t : ℕ → List End) (src : End → ℕ) :
    ∀ I : List Update, (outInsertEdits t src I).length ≤ 2 * I.length
  | [] => le_rfl
  | u :: I => by
    have ih := outInsertEdits_length_le t src I
    cases u <;> simp only [outInsertEdits, List.length_cons] <;> omega

/-- A batch of restricted splits deletes no edge. -/
private theorem delete_not_mem_restrictSplits (keep : Finset ℕ) (e : ℕ) :
    ∀ UC : List Update, Update.delete e ∉ restrictSplits keep UC
  | [] => by simp [restrictSplits]
  | u :: UC => by
    have ih := delete_not_mem_restrictSplits keep e UC
    cases u <;> simp [restrictSplits, ih]

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- The edits of an output step before the rotations: those of the deletions and splits, then
those of the insertions. `outBaseOrder` applies them to the old output order. -/
noncomputable def outBaseEdits (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) : List OrdEdit :=
  let st' := (stepBundleTree sparsify st U ord ord').state
  outPrefixEdits (outPrefixBatch sparsify st U ord ord') ++
    outInsertEdits (st'.outOrder ord') st'.S_cur.src (outInsBatch sparsify st U ord ord')

theorem outBaseOrder_eq (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    outBaseOrder sparsify st U ord ord' =
      applyOrdEdits (st.outOrder ord) (outBaseEdits sparsify st U ord ord') := by
  unfold outBaseOrder outBaseEdits
  rfl

/-- The edits before the rotations drop exactly the leaving output edges. -/
theorem mem_ordEditDrops_outBaseEdits (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (e : ℕ) :
    e ∈ ordEditDrops (outBaseEdits sparsify st U ord ord') ↔
      e ∈ st.S_cur.E \ outKeep sparsify st U ord ord' := by
  rw [outBaseEdits, ordEditDrops_append, ordEditDrops_outInsertEdits, Finset.union_empty,
    ordEditDrops_outPrefixEdits, outPrefixBatch, List.mem_append]
  rw [or_iff_left (delete_not_mem_restrictSplits _ _ _), List.mem_map]
  constructor
  · rintro ⟨e', he', heq⟩
    cases heq
    exact (Finset.mem_sort _).mp he'
  · intro he
    exact ⟨e, (Finset.mem_sort _).mpr he, rfl⟩

/-- **The output list at a vertex that the edits do not name.** There, the edits before the
rotations give the old output list restricted to the output edges that stay. -/
theorem outBaseOrder_of_not_mem (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) {v : ℕ}
    (hv : v ∉ ordEditVerts (outBaseEdits sparsify st U ord ord')) :
    outBaseOrder sparsify st U ord ord' v =
      (st.outOrder ord v).filter fun x => decide (x.1 ∈ outKeep sparsify st U ord ord') := by
  rw [outBaseOrder_eq, applyOrdEdits_of_not_mem _ _ hv]
  refine List.filter_congr fun x hx => ?_
  -- every end of the old output list is an end of an old output edge
  rw [outOrder_eq_filter, List.mem_filter] at hx
  have hxS : x.1 ∈ st.S_cur.E := of_decide_eq_true hx.2
  simp [mem_ordEditDrops_outBaseEdits, hxS]

/-- The edits before the rotations name at most four vertices per update of the output batch. -/
theorem ordEditVerts_outBaseEdits_card_le (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) :
    (ordEditVerts (outBaseEdits sparsify st U ord ord')).card ≤
      4 * (stepBundleTree sparsify st U ord ord').U_S.length := by
  refine (ordEditVerts_card_le _).trans ?_
  rw [stepBundleTree_U_S_split, List.length_append, outBaseEdits, List.length_append]
  have h1 := outPrefixEdits_length_le (outPrefixBatch sparsify st U ord ord')
  have h2 := outInsertEdits_length_le
    ((stepBundleTree sparsify st U ord ord').state.outOrder ord')
    (stepBundleTree sparsify st U ord ord').state.S_cur.src (outInsBatch sparsify st U ord ord')
  omega

end MinCostFlow.SparseCore.Program
