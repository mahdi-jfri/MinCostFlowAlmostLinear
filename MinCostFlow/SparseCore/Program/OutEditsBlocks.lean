module

public import MinCostFlow.SparseCore.Program.OrdEditsBlocks
public import MinCostFlow.SparseCore.Program.OutEditsModel
public import MinCostFlow.SparseCore.Program.OutEditsStep
public import MinCostFlow.SparseCore.Program.OutStepSpecSmall

import MinCostFlow.SparseCore.Program.OutStepJoinModel

/-!
# P7's output edits are block-aligned for `U_S` (`OutEditsBlocks`)

Proves that the output order edits produced by piece P7 for a branch step satisfy
`OrdEditsForBatch st.S_cur (stepBundleTree sparsify st U ord ord').U_S`:
* `outStepEdits_forBatch`: holds unconditionally for `outStepEdits` (`OutEditsModel.lean`).
* `outStepEditsSmall_forBatch`: holds unconditionally for `outStepEditsSmall`
  (`OutEditsStep.lean`), the exact edit list written by `outStepBody` in `sig_outStepSmall_runs_of`
  (`OutStepSmallProof.lean`).
* `outStepEditsSmall_post_blocks`: extends `outStepEditsSmall_post` (`OutStepSpecSmall.lean`)
  with `OrdEditsForBatch`, showing that every deeper level's input batch and edits satisfy the
  block-alignment predicate.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-! ## Component lemmas for deletions/splits, insertions, and rotations -/

/-- `outPrefixEdits P` is an exact block prefix for any batch `P` without insertions. -/
theorem outPrefixEdits_exactPrefix :
    ∀ (G : MGraph) (P : List Update), (∀ u ∈ P, Update.NotInsert u) →
      OrdEditsExactPrefix G P (outPrefixEdits P)
  | _, [], _ => rfl
  | G, .delete e :: P, hP =>
    ⟨rfl, outPrefixEdits_exactPrefix (G.applyUpdate (.delete e)) P
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))⟩
  | G, .split v v' St Sh :: P, hP =>
    ⟨rfl, rfl, fun x _ _ => movedBy_splitSel St Sh x,
      outPrefixEdits_exactPrefix (G.applyUpdate (.split v v' St Sh)) P
        (fun u hu => hP u (List.mem_cons_of_mem _ hu))⟩
  | _, .insert _ _ _ :: _, hP => False.elim (hP _ List.mem_cons_self)

/-- `outPrefixEditsOn G P` (smaller-side split edits) is an exact block prefix for any batch `P`
without insertions. -/
theorem outPrefixEditsOn_exactPrefix :
    ∀ (G : MGraph) (P : List Update), (∀ u ∈ P, Update.NotInsert u) →
      OrdEditsExactPrefix G P (outPrefixEditsOn G P)
  | _, [], _ => rfl
  | G, .delete e :: P, hP =>
    ⟨rfl, outPrefixEditsOn_exactPrefix (G.applyUpdate (.delete e)) P
      (fun u hu => hP u (List.mem_cons_of_mem _ hu))⟩
  | G, .split v v' St Sh :: P, hP => by
    simp only [outPrefixEditsOn, outSplitEdit]
    split
    · exact ⟨rfl, rfl, fun x hx hv => movedBy_outSplitEdit hx hv _ _ (Or.inl ⟨rfl, rfl⟩),
        outPrefixEditsOn_exactPrefix (G.applyUpdate (.split v v' St Sh)) P
          (fun u hu => hP u (List.mem_cons_of_mem _ hu))⟩
    · exact ⟨rfl, rfl, fun x hx hv => movedBy_outSplitEdit hx hv _ _ (Or.inr ⟨rfl, rfl⟩),
        outPrefixEditsOn_exactPrefix (G.applyUpdate (.split v v' St Sh)) P
          (fun u hu => hP u (List.mem_cons_of_mem _ hu))⟩
  | _, .insert _ _ _ :: _, hP => False.elim (hP _ List.mem_cons_self)

/-- `outInsertEdits t src I` is an exact block prefix for any batch `I` of insertions whose
endpoints match `src`. -/
theorem outInsertEdits_exactPrefix (t : ℕ → List End) (src : End → ℕ) :
    ∀ (G : MGraph) (I : List Update),
      (∀ u ∈ I, match u with
        | .insert e a b => src (e, true) = a ∧ src (e, false) = b
        | _ => False) →
      OrdEditsExactPrefix G I (outInsertEdits t src I)
  | _, [], _ => rfl
  | G, .insert e a b :: I, hI => by
    obtain ⟨ha, hb⟩ := hI _ List.mem_cons_self
    exact ⟨ha, rfl, hb, rfl, outInsertEdits_exactPrefix t src (G.applyUpdate (.insert e a b)) I
      (fun u hu => hI u (List.mem_cons_of_mem _ hu))⟩
  | _, .delete _ :: _, hI => False.elim (hI _ List.mem_cons_self)
  | _, .split _ _ _ _ :: _, hI => False.elim (hI _ List.mem_cons_self)

/-- Every edit of `outRotateEdits t T` is a `rotateTo` edit. -/
theorem outRotateEdits_isRotate (t : ℕ → List End) :
    ∀ (T : List ℕ) (d : OrdEdit), d ∈ outRotateEdits t T → d.IsRotate
  | [], _, hd => by cases hd
  | v :: T, d, hd => by
    simp only [outRotateEdits, List.mem_append] at hd
    rcases hd with hd | hd
    · cases htv : t v with
      | nil => simp [htv] at hd
      | cons y _ =>
        simp only [htv, List.mem_singleton] at hd
        subst hd; trivial
    · exact outRotateEdits_isRotate t T d hd

/-! ## Main results for P7's output edits -/

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

private theorem outInsBatch_src_eq (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) :
    let st' := (stepBundleTree sparsify st U ord ord').state
    ∀ u ∈ outInsBatch sparsify st U ord ord',
      match u with
      | .insert e a b => st'.S_cur.src (e, true) = a ∧ st'.S_cur.src (e, false) = b
      | _ => False := by
  intro st' u hu
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
  have hends := outStep_ins_ends sparsify st U ord ord' e he
  exact ⟨hends.1, hends.2⟩

/-- **P7's output edits (`outStepEdits`) are block-aligned for `U_S`.** -/
theorem outStepEdits_forBatch (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (T : List ℕ) :
    OrdEditsForBatch st.S_cur (stepBundleTree sparsify st U ord ord').U_S
      (outStepEdits sparsify st U ord ord' T) := by
  rw [stepBundleTree_U_S_split]
  exact ordEditsForBatch_of_exactPrefix_append
    (ordEditsExactPrefix_append
      (outPrefixEdits_exactPrefix st.S_cur _ (notInsert_prefix sparsify st U ord ord'))
      (outInsertEdits_exactPrefix _ _ _ _ (outInsBatch_src_eq sparsify st U ord ord')))
    (outRotateEdits_isRotate _ T)

/-- **P7's compact output edits (`outStepEditsSmall`, written by `sig_outStepSmall_runs_of`) are
block-aligned for `U_S`.** -/
theorem outStepEditsSmall_forBatch (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (T₀ : List ℕ) :
    OrdEditsForBatch st.S_cur (stepBundleTree sparsify st U ord ord').U_S
      (outStepEditsSmall sparsify st U ord ord' T₀) := by
  rw [stepBundleTree_U_S_split]
  exact ordEditsForBatch_of_exactPrefix_append
    (ordEditsExactPrefix_append
      (outPrefixEditsOn_exactPrefix st.S_cur _ (notInsert_prefix sparsify st U ord ord'))
      (outInsertEdits_exactPrefix _ _ _ _ (outInsBatch_src_eq sparsify st U ord ord')))
    (outRotateEdits_isRotate _ T₀)

/-- **Combined model postcondition of P7's output step with block alignment.** Extends
`outStepEditsSmall_post` (`OutStepSpecSmall.lean`) with `OrdEditsForBatch`, showing that every
deeper level's input batch and edits satisfy the block-alignment precondition. -/
theorem outStepEditsSmall_post_blocks {vCap eCap : ℕ} (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (T₀ : List ℕ) (hready : OutStepReady sparsify st U ord ord')
    (hR : ∀ v ∈ (stepBundleTree sparsify st U ord ord').state.cs.RF.R, v < vCap)
    (hE : ∀ e ∈ st.S_cur.E, e < eCap)
    (hE' : ∀ e ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.E, e < eCap)
    (hT : ∀ v ∈ T₀, v < vCap) (hcov : OutRotCover sparsify st U ord ord' T₀) :
    let edits := outStepEditsSmall sparsify st U ord ord' T₀
    applyOrdEdits (st.outOrder ord) edits = (stepBundleTree sparsify st U ord ord').state.outOrder ord' ∧
      ordEditsEnc edits ≤ 2 * st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S +
        T₀.length ∧
      OrdEditsWithin vCap eCap edits ∧
      OrdEditsUniqueWithin vCap eCap (st.outOrder ord) edits ∧
      OrdEditsForBatch st.S_cur (stepBundleTree sparsify st U ord ord').U_S edits := by
  obtain ⟨h1, h2, h3, h4⟩ := outStepEditsSmall_post sparsify st U ord ord' T₀ hready hR hE hE' hT hcov
  exact ⟨h1, h2, h3, h4, outStepEditsSmall_forBatch sparsify st U ord ord' T₀⟩

end MinCostFlow.SparseCore.Program
