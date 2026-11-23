module

public import MinCostFlow.MinRatio.WireChainAlgebra
public import MinCostFlow.MinRatio.TreeEditLayout
public import MinCostFlow.Chain.Ordered.RenameFacts
public import MinCostFlow.IPM.Machine.MinRatioContract
import WordRAM.Tactic

/-!
# Batch edge correspondence and active tree-edit filtering (`WireChainCoreBatch`)

Provides the pure batch/tree-edit lemmas used by `ordChainUpdateCoreBody`:
1. `translateBatch_oldId_facts`: under `FreshInv` and edge-only valid batches, characterizes
   `tr.2.2.1` on old IDs `< nf`, live-edge survival in `curInt.applyBatch U_int`, range of fresh
   IDs, uniqueness (`Nodup`) of old-ID deletions in `U_int`, and the exact equivalence between
   `¬ ∃ u ∈ U, u.Inserts e` and `Update.delete (e2i e) ∉ U_int`.
2. `filterActiveEdits` and `treeEditDiff_filterActive`: restricting `TreeEditDifference oldE newE`
   to `midE = oldE ∩ liveE` when `newE ⊆ liveE` and already-deleted edges have been cut.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.IPM.Machine

/-! ### 1. `RefreshBatch` + `translateBatch` edge-correspondence lemmas -/

/-- Under `FreshInv`, `translateBatch` preserves `i2e` on all IDs `< nf`, keeps all newly inserted
internal IDs `≥ nf`, never deletes an ID `< nf` twice, and for every `.delete ei ∈ U_int` with
`ei ∈ curInt.E`, `ei` is the old internal ID of `i2e ei` and is removed from `curInt.applyBatch U_int`. -/
theorem translateBatch_oldId_facts :
    ∀ (U : List Update) (curExt curInt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      FreshInv curExt curInt e2i i2e nf → curExt.BatchIsValid U →
      (∀ u ∈ U, IsEdgeUpdate u) →
      let tr := translateBatch curExt e2i i2e nf U
      let U_int := tr.2.2.2.2
      (∀ ei < nf, tr.2.2.1 ei = i2e ei) ∧
      (∀ ei ∈ curInt.E, ei ∈ (curInt.applyBatch U_int).E ↔ Update.delete ei ∉ U_int) ∧
      (∀ u ∈ U_int, match u with
        | .insert ei _ _ => nf ≤ ei ∧ ei < tr.2.2.2.1
        | .delete ei => ei < tr.2.2.2.1
        | .split _ _ _ _ => False) ∧
      (U_int.filterMap fun u => match u with
        | .delete ei => if ei ∈ curInt.E then some ei else none
        | _ => none).Nodup ∧
      (∀ e ∈ curExt.E, e ∈ tr.1.E →
        ((¬ ∃ u ∈ U, u.Inserts e) ↔ Update.delete (e2i e) ∉ U_int)) := by
  intro U
  induction U with
  | nil =>
    intro curExt curInt e2i i2e nf _ _ _
    refine ⟨fun _ _ => rfl, fun _ h => by simp [translateBatch, MGraph.applyBatch, h],
      fun _ h => by simp [translateBatch] at h, by simp [translateBatch],
      fun _ _ _ => by simp [translateBatch]⟩
  | cons u rest ih =>
    intro curExt curInt e2i i2e nf hF hVal hEdge
    have huE := hEdge u List.mem_cons_self
    have hrestE := fun v hv => hEdge v (List.mem_cons_of_mem u hv)
    obtain ⟨hF1, _, _, _, _, _, _⟩ := translateUpdate_preserves hF hVal.1
    cases u with
    | split _ _ _ _ => exact huE.elim
    | delete e0 =>
      dsimp only [translateUpdate] at hF1
      obtain ⟨hi2eR, hDelR, hRangeR, hNodupR, hInsR⟩ :=
        ih (curExt.applyUpdate (.delete e0)) (curInt.applyUpdate (.delete (e2i e0))) e2i i2e nf hF1 hVal.2 hrestE
      have hnfLeTot : nf ≤ (translateBatch (curExt.applyUpdate (.delete e0)) e2i i2e nf rest).2.2.2.1 :=
        (translateBatch_preserves rest (curExt.applyUpdate (.delete e0))
          (curInt.applyUpdate (.delete (e2i e0))) e2i i2e nf hF1 hVal.2).2.2.2.2.2.1
      have he0Mem : e0 ∈ curExt.E := hVal.1
      have hei0Mem : e2i e0 ∈ curInt.E := hF.hE ▸ Finset.mem_image_of_mem e2i he0Mem
      have hei0Lt : e2i e0 < nf := hF.hLtFresh _ hei0Mem
      have hNotIn1 : e2i e0 ∉ (curInt.applyUpdate (.delete (e2i e0))).E := by
        simp [MGraph.applyUpdate]
      have hNotDelR : Update.delete (e2i e0) ∉
          (translateBatch (curExt.applyUpdate (.delete e0)) e2i i2e nf rest).2.2.2.2 := by
        intro hmem
        have hDelLt : ∀ (V : List Update) (G0 H0 : MGraph) (f g : ℕ → ℕ) (n0 : ℕ),
            FreshInv G0 H0 f g n0 → G0.BatchIsValid V → (∀ v ∈ V, IsEdgeUpdate v) →
            ∀ x, Update.delete x ∈ (translateBatch G0 f g n0 V).2.2.2.2 → x ∈ H0.E ∨ n0 ≤ x := by
          intro V; induction V with
          | nil => intro _ _ _ _ _ _ _ _ _ h; simp [translateBatch] at h
          | cons v vs ihV =>
            intro G0 H0 f g n0 hFv hVv hEv x hx
            obtain ⟨hFv1, _, hnv1, _, _, _, _⟩ := translateUpdate_preserves hFv hVv.1
            have hvE := hEv v List.mem_cons_self
            cases v with
            | split _ _ _ _ => exact hvE.elim
            | delete a =>
              simp only [translateBatch, translateUpdate, List.mem_cons] at hx
              rcases hx with heq | hx'
              · cases heq; exact Or.inl (hFv.hE ▸ Finset.mem_image_of_mem f hVv.1)
              · rcases ihV _ _ _ _ _ hFv1 hVv.2 (fun z hz => hEv z (List.mem_cons_of_mem _ hz)) x hx' with h1 | h2
                · exact Or.inl (Finset.mem_of_mem_erase h1)
                · exact Or.inr (le_trans hnv1 h2)
            | insert a p q =>
              simp only [translateBatch, translateUpdate, List.mem_cons] at hx
              rcases hx with heq | hx'
              · cases heq
              · rcases ihV _ _ _ _ _ hFv1 hVv.2 (fun z hz => hEv z (List.mem_cons_of_mem _ hz)) x hx' with h1 | h2
                · simp only [MGraph.applyUpdate, Finset.mem_insert] at h1
                  rcases h1 with rfl | h1'
                  · exact Or.inr le_rfl
                  · exact Or.inl h1'
                · exact Or.inr (le_trans hnv1 h2)
        rcases hDelLt rest (curExt.applyUpdate (.delete e0)) (curInt.applyUpdate (.delete (e2i e0)))
            e2i i2e nf hF1 hVal.2 hrestE (e2i e0) hmem with h1 | h2
        · exact hNotIn1 h1
        · omega
      have hNeverIns : ∀ (V : List Update) (G0 H0 : MGraph) (f g : ℕ → ℕ) (n0 : ℕ),
          FreshInv G0 H0 f g n0 → G0.BatchIsValid V → (∀ v ∈ V, IsEdgeUpdate v) →
          ∀ x, x < n0 → x ∉ H0.E → x ∉ (H0.applyBatch (translateBatch G0 f g n0 V).2.2.2.2).E := by
        intro V; induction V with
        | nil => intro _ _ _ _ _ _ _ _ _ _ hnot; simpa [translateBatch, MGraph.applyBatch] using hnot
        | cons v vs ihV =>
          intro G0 H0 f g n0 hFv hVv hEv x hx hnot
          obtain ⟨hFv1, _, hnv1, _, _, _, _⟩ := translateUpdate_preserves hFv hVv.1
          have hvE := hEv v List.mem_cons_self
          cases v with
          | split _ _ _ _ => exact hvE.elim
          | delete a =>
            simp only [translateBatch, translateUpdate, MGraph.applyBatch, List.foldl_cons]
            exact ihV _ _ _ _ _ hFv1 hVv.2 (fun z hz => hEv z (List.mem_cons_of_mem _ hz)) x
              (lt_of_lt_of_le hx hnv1) (by simp [MGraph.applyUpdate, hnot])
          | insert a p q =>
            simp only [translateBatch, translateUpdate, MGraph.applyBatch, List.foldl_cons]
            exact ihV _ _ _ _ _ hFv1 hVv.2 (fun z hz => hEv z (List.mem_cons_of_mem _ hz)) x
              (lt_of_lt_of_le hx hnv1) (by simp [MGraph.applyUpdate, hnot, show x ≠ n0 by omega])
      refine ⟨fun ei hei => hi2eR ei hei, ?_, ?_, ?_, ?_⟩
      · intro ei hei
        simp only [translateBatch, translateUpdate, MGraph.applyBatch, List.foldl_cons, List.mem_cons, not_or]
        by_cases heq : ei = e2i e0
        · subst heq
          have hna := hNeverIns rest (curExt.applyUpdate (.delete e0))
            (curInt.applyUpdate (.delete (e2i e0))) e2i i2e nf hF1 hVal.2 hrestE (e2i e0) hei0Lt hNotIn1
          simp only [MGraph.applyBatch] at hna
          simp [hna]
        · have hei1 : ei ∈ (curInt.applyUpdate (.delete (e2i e0))).E := by
            simp [MGraph.applyUpdate, heq, hei]
          have hd := hDelR ei hei1
          simp only [MGraph.applyBatch] at hd
          rw [hd]; simp [heq]
      · intro v hv
        simp only [translateBatch, translateUpdate, List.mem_cons] at hv
        rcases hv with rfl | hv'
        · exact lt_of_lt_of_le hei0Lt hnfLeTot
        · exact hRangeR v hv'
      · simp only [translateBatch, translateUpdate, List.filterMap_cons, hei0Mem, ↓reduceIte, List.nodup_cons]
        have hFiltEq :
            ((translateBatch (curExt.applyUpdate (.delete e0)) e2i i2e nf rest).2.2.2.2.filterMap fun u =>
              match u with | .delete ei => if ei ∈ curInt.E then some ei else none | _ => none) =
            ((translateBatch (curExt.applyUpdate (.delete e0)) e2i i2e nf rest).2.2.2.2.filterMap fun u =>
              match u with | .delete ei => if ei ∈ (curInt.applyUpdate (.delete (e2i e0))).E then some ei else none | _ => none) := by
          refine List.filterMap_congr (fun v hv => ?_)
          cases v with
          | insert _ _ _ => rfl
          | split _ _ _ _ => rfl
          | delete ei =>
            have hne : ei ≠ e2i e0 := fun h => hNotDelR (h ▸ hv)
            simp [MGraph.applyUpdate, hne]
        have hNotIn : e2i e0 ∉
            ((translateBatch (curExt.applyUpdate (.delete e0)) e2i i2e nf rest).2.2.2.2.filterMap fun u =>
              match u with | .delete ei => if ei ∈ curInt.E then some ei else none | _ => none) := by
          intro hm
          rw [List.mem_filterMap] at hm
          obtain ⟨v, hv, hvs⟩ := hm
          cases v with
          | insert _ _ _ => simp at hvs
          | split _ _ _ _ => simp at hvs
          | delete ei =>
            dsimp only at hvs
            split_ifs at hvs with h1
            · injection hvs with heq; subst heq; exact hNotDelR hv
        exact ⟨hNotIn, hFiltEq ▸ hNodupR⟩
      · intro e he heEnd
        simp only [translateBatch, translateUpdate, List.mem_cons, not_or] at heEnd ⊢
        by_cases hee0 : e = e0
        · subst hee0
          have hInsE0 : ∃ v ∈ rest, v.Inserts e := by
            by_contra hno
            have hnotMem : ∀ (V : List Update) (G0 : MGraph), e ∉ G0.E → (∀ v ∈ V, IsEdgeUpdate v) →
                (¬ ∃ v ∈ V, v.Inserts e) → e ∉ (G0.applyBatch V).E := by
              intro V; induction V with
              | nil => intro _ h _ _; simpa [MGraph.applyBatch] using h
              | cons v vs ihV =>
                intro G0 hnot hEv hni
                have hvE := hEv v List.mem_cons_self
                cases v with
                | split _ _ _ _ => exact hvE.elim
                | delete a =>
                  exact ihV _ (by simp [MGraph.applyUpdate, hnot]) (fun z hz => hEv z (List.mem_cons_of_mem _ hz))
                    (fun ⟨z, hz, hi⟩ => hni ⟨z, List.mem_cons_of_mem _ hz, hi⟩)
                | insert a p q =>
                  have hne : e ≠ a := fun h => hni ⟨.insert a p q, List.mem_cons_self, by simp [Update.Inserts, h]⟩
                  exact ihV _ (by simp [MGraph.applyUpdate, hnot, hne]) (fun z hz => hEv z (List.mem_cons_of_mem _ hz))
                    (fun ⟨z, hz, hi⟩ => hni ⟨z, List.mem_cons_of_mem _ hz, hi⟩)
            have h1Eq := (translateBatch_preserves rest (curExt.applyUpdate (.delete e))
              (curInt.applyUpdate (.delete (e2i e))) e2i i2e nf hF1 hVal.2).1
            exact hnotMem rest (curExt.applyUpdate (.delete e)) (by simp [MGraph.applyUpdate])
              hrestE hno (h1Eq ▸ heEnd)
          constructor
          · intro hno; exact False.elim (hno (let ⟨v, hv, hi⟩ := hInsE0; ⟨v, Or.inr hv, hi⟩))
          · intro ⟨hne, _⟩; exact False.elim (hne rfl)
        · have he1 : e ∈ (curExt.applyUpdate (.delete e0)).E := by simp [MGraph.applyUpdate, hee0, he]
          have hneI : e2i e ≠ e2i e0 := fun h => hee0 ((hF.hLeft e he).symm.trans (h ▸ hF.hLeft e0 he0Mem))
          have hr := hInsR e he1 heEnd
          constructor
          · intro hno
            refine ⟨by simp [hneI], hr.mp ?_⟩
            rintro ⟨v, hv, hi⟩; exact hno ⟨v, Or.inr hv, hi⟩
          · intro ⟨_, hnd⟩ ⟨v, hv, hi⟩
            rcases hv with rfl | hv'
            · simp [Update.Inserts] at hi
            · exact hr.mpr hnd ⟨v, hv', hi⟩
    | insert e0 p q =>
      dsimp only [translateUpdate] at hF1
      obtain ⟨hi2eR, hDelR, hRangeR, hNodupR, hInsR⟩ :=
        ih (curExt.applyUpdate (.insert e0 p q)) (curInt.applyUpdate (.insert nf p q))
          (Function.update e2i e0 nf) (Function.update i2e nf e0) (nf + 1) hF1 hVal.2 hrestE
      have hnfLeTot : nf + 1 ≤ (translateBatch (curExt.applyUpdate (.insert e0 p q))
          (Function.update e2i e0 nf) (Function.update i2e nf e0) (nf + 1) rest).2.2.2.1 :=
        (translateBatch_preserves rest (curExt.applyUpdate (.insert e0 p q))
          (curInt.applyUpdate (.insert nf p q)) (Function.update e2i e0 nf)
          (Function.update i2e nf e0) (nf + 1) hF1 hVal.2).2.2.2.2.2.1
      refine ⟨fun ei hei => (hi2eR ei (by omega)).trans (by simp [show ei ≠ nf by omega]),
        ?_, ?_, ?_, ?_⟩
      · intro ei hei
        have hei1 : ei ∈ (curInt.applyUpdate (.insert nf p q)).E := by simp [MGraph.applyUpdate, hei]
        simp only [translateBatch, translateUpdate, MGraph.applyBatch, List.foldl_cons, List.mem_cons, not_or]
        have hd := hDelR ei hei1
        simp only [MGraph.applyBatch] at hd
        rw [hd]; simp
      · intro v hv
        simp only [translateBatch, translateUpdate, List.mem_cons] at hv
        rcases hv with rfl | hv'
        · exact ⟨le_rfl, Nat.lt_of_lt_of_le (Nat.lt_succ_self nf) hnfLeTot⟩
        · have hr := hRangeR v hv'
          cases v with
          | insert ei _ _ => exact ⟨le_trans (Nat.le_succ nf) hr.1, hr.2⟩
          | delete ei => exact hr
          | split _ _ _ _ => exact hr
      · simp only [translateBatch, translateUpdate, List.filterMap_cons]
        have hSublist :
            ((translateBatch (curExt.applyUpdate (.insert e0 p q)) (Function.update e2i e0 nf)
                (Function.update i2e nf e0) (nf + 1) rest).2.2.2.2.filterMap fun u =>
              match u with | .delete ei => if ei ∈ curInt.E then some ei else none | _ => none).Sublist
            ((translateBatch (curExt.applyUpdate (.insert e0 p q)) (Function.update e2i e0 nf)
                (Function.update i2e nf e0) (nf + 1) rest).2.2.2.2.filterMap fun u =>
              match u with | .delete ei => if ei ∈ (curInt.applyUpdate (.insert nf p q)).E then some ei else none | _ => none) := by
          clear hNodupR
          induction (translateBatch (curExt.applyUpdate (.insert e0 p q)) (Function.update e2i e0 nf)
              (Function.update i2e nf e0) (nf + 1) rest).2.2.2.2 with
          | nil => exact List.Sublist.slnil
          | cons v vs ihv =>
            simp only [List.filterMap_cons]
            cases v with
            | insert _ _ _ => exact ihv
            | split _ _ _ _ => exact ihv
            | delete ei =>
              by_cases h1 : ei ∈ curInt.E
              · have h2 : ei ∈ (curInt.applyUpdate (.insert nf p q)).E := by simp [MGraph.applyUpdate, h1]
                simp only [h1, h2, ↓reduceIte]; exact ihv.cons_cons ei
              · by_cases h2 : ei ∈ (curInt.applyUpdate (.insert nf p q)).E
                · simp only [h1, h2, ↓reduceIte]; exact ihv.cons ei
                · simp only [h1, h2, ↓reduceIte]; exact ihv
        exact hNodupR.sublist hSublist
      · intro e he heEnd
        have heNe : e ≠ e0 := fun h => hVal.1.1 (h ▸ he)
        have he1 : e ∈ (curExt.applyUpdate (.insert e0 p q)).E := by simp [MGraph.applyUpdate, he]
        simp only [translateBatch, translateUpdate, List.mem_cons, not_or] at heEnd ⊢
        have hr := hInsR e he1 heEnd
        simp only [Function.update_of_ne heNe] at hr
        constructor
        · intro hno
          refine ⟨by simp, hr.mp ?_⟩
          rintro ⟨v, hv, hi⟩; exact hno ⟨v, Or.inr hv, hi⟩
        · intro ⟨_, hnd⟩ ⟨v, hv, hi⟩
          rcases hv with rfl | hv'
          · simp [Update.Inserts] at hi; exact heNe hi.symm
          · exact hr.mpr hnd ⟨v, hv', hi⟩

/-! ### 2. Filtering already-cut deletions from `TreeEditDifference` -/

/-- Filter a `TreeChange` list keeping all `.insert`s and only those `.delete e` with `e ∈ active`. -/
@[expose] def filterActiveEdits (active : Finset ℕ) (edits : List TreeChange) : List TreeChange :=
  open Classical in
  edits.filter fun c => match c with
    | .delete e => decide (e ∈ active)
    | .insert _ => true

theorem filterActiveEdits_length_le (active : Finset ℕ) (edits : List TreeChange) :
    (filterActiveEdits active edits).length ≤ edits.length :=
  List.length_filter_le _ _

private theorem list_split_del_ins :
    ∀ (l : List TreeChange),
      (∀ (p r : List TreeChange) (e j : ℕ), l = p ++ .insert e :: r → TreeChange.delete j ∉ r) →
      l = (l.filterMap fun c => match c with | .delete e => some e | .insert _ => none).map .delete ++
          (l.filterMap fun c => match c with | .insert e => some e | .delete _ => none).map .insert
  | [], _ => rfl
  | .delete e :: rest, h => by
    have hr := list_split_del_ins rest (fun p r e' j hEq =>
      h (.delete e :: p) r e' j (by simp [hEq]))
    simpa [List.filterMap_cons] using congrArg (.delete e :: ·) hr
  | .insert e :: rest, h => by
    have hnoDel : ∀ j, TreeChange.delete j ∉ rest := fun j => h [] rest e j rfl
    have hdelNil : (rest.filterMap fun c => match c with | .delete x => some x | .insert _ => none) = [] := by
      cases hfm : rest.filterMap (fun c => match c with | .delete x => some x | .insert _ => none) with
      | nil => rfl
      | cons x xs =>
        have hx : x ∈ rest.filterMap (fun c => match c with | .delete y => some y | .insert _ => none) := by
          rw [hfm]; simp
        obtain ⟨c, hc, hcs⟩ := List.mem_filterMap.mp hx
        cases c with
        | insert _ => simp at hcs
        | delete y => simp at hcs; subst hcs; exact False.elim (hnoDel y hc)
    have hr := list_split_del_ins rest (fun p r e' j hEq =>
      h (.insert e :: p) r e' j (by simp [hEq]))
    rw [hdelNil] at hr
    simpa [List.filterMap_cons, hdelNil] using congrArg (.insert e :: ·) hr

/-- Restricting `TreeEditDifference oldE newE edits` to `midE = oldE ∩ G'.E` (when `newE ⊆ G'.E`)
produces a valid `TreeEditDifference midE newE (filterActiveEdits midE edits)`. -/
theorem treeEditDiff_filterActive {oldE newE liveE : Finset ℕ} {edits : List TreeChange}
    (hDiff : TreeEditDifference oldE newE edits)
    (hNewSub : newE ⊆ liveE) :
    TreeEditDifference (oldE ∩ liveE) newE (filterActiveEdits (oldE ∩ liveE) edits) := by
  classical
  let ds := edits.filterMap fun c => match c with | .delete e => some e | .insert _ => none
  let ins := edits.filterMap fun c => match c with | .insert e => some e | .delete _ => none
  have hSplit : edits = ds.map .delete ++ ins.map .insert :=
    list_split_del_ins edits (fun p r e j hEq => (hEq ▸ hDiff).no_delete_after_insert)
  have hNd : edits.Nodup := hDiff.perm.nodup_iff.mpr (treeEdit_diff_nodup oldE newE).1
  rw [hSplit] at hNd
  have hDsNd : ds.Nodup := (List.nodup_append.mp hNd).1.of_map _
  have hInsNd : ins.Nodup := (List.nodup_append.mp hNd).2.1.of_map _
  have hDsMem (x : ℕ) : x ∈ ds ↔ x ∈ oldE \ newE := by
    simp only [ds, List.mem_filterMap]
    constructor
    · rintro ⟨c, hc, hcs⟩
      cases c with
      | insert _ => simp at hcs
      | delete y => simp at hcs; subst hcs; exact hDiff.delete_mem_sdiff hc
    · intro hx
      exact ⟨.delete x, hDiff.perm.mem_iff.mpr (treeEdit_delete_mem_diff.mpr hx), rfl⟩
  have hInsMem (x : ℕ) : x ∈ ins ↔ x ∈ newE \ oldE := by
    simp only [ins, List.mem_filterMap]
    constructor
    · rintro ⟨c, hc, hcs⟩
      cases c with
      | delete _ => simp at hcs
      | insert y => simp at hcs; subst hcs; exact hDiff.insert_mem_sdiff hc
    · intro hx
      exact ⟨.insert x, hDiff.perm.mem_iff.mpr (treeEdit_insert_mem_diff.mpr hx), rfl⟩
  let ds' := ds.filter (fun e => decide (e ∈ oldE ∩ liveE))
  let oldNames := ds' ++ ((oldE ∩ liveE) ∩ newE).toList
  let newNames := ins ++ ((oldE ∩ liveE) ∩ newE).toList
  have hOldPerm : oldNames.Perm (oldE ∩ liveE).toList := by
    refine (List.perm_ext_iff_of_nodup ?_ (Finset.nodup_toList _)).mpr ?_
    · refine List.nodup_append.mpr ⟨hDsNd.filter _, Finset.nodup_toList _, fun a ha b hb hab => ?_⟩
      subst hab
      have h1 := (hDsMem a).mp (List.mem_of_mem_filter ha)
      have h2 := Finset.mem_toList.mp hb
      exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
    · intro x
      simp only [oldNames, ds', List.mem_append, List.mem_filter, decide_eq_true_eq,
        Finset.mem_toList, Finset.mem_inter, hDsMem, Finset.mem_sdiff]
      tauto
  have hNewPerm : newNames.Perm newE.toList := by
    refine (List.perm_ext_iff_of_nodup ?_ (Finset.nodup_toList _)).mpr ?_
    · refine List.nodup_append.mpr ⟨hInsNd, Finset.nodup_toList _, fun a ha b hb hab => ?_⟩
      subst hab
      have h1 := (hInsMem a).mp ha
      have h2 := Finset.mem_toList.mp hb
      exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp (Finset.mem_inter.mp h2).1).1
    · intro x
      simp only [newNames, List.mem_append, Finset.mem_toList, Finset.mem_inter, hInsMem, Finset.mem_sdiff]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.2
      · intro hx; by_cases ho : x ∈ oldE
        · exact Or.inr ⟨⟨ho, hNewSub hx⟩, hx⟩
        · exact Or.inl ⟨hx, ho⟩
  have hOf := treeEditDifference_of_filter hOldPerm hNewPerm
  have hF1 : oldNames.filter (fun e => decide (e ∉ newE)) = ds' := by
    simp only [oldNames, List.filter_append]
    have hA : ds'.filter (fun e => decide (e ∉ newE)) = ds' :=
      List.filter_eq_self.mpr (fun x hx => by
        simp only [decide_eq_true_eq]
        exact (Finset.mem_sdiff.mp ((hDsMem x).mp (List.mem_of_mem_filter hx))).2)
    have hB : ((oldE ∩ liveE) ∩ newE).toList.filter (fun e => decide (e ∉ newE)) = [] :=
      List.filter_eq_nil_iff.mpr (fun x hx => by
        simp only [decide_eq_true_eq, not_not]
        exact (Finset.mem_inter.mp (Finset.mem_toList.mp hx)).2)
    rw [hA, hB, List.append_nil]
  have hF2 : newNames.filter (fun e => decide (e ∉ oldE ∩ liveE)) = ins := by
    simp only [newNames, List.filter_append]
    have hA : ins.filter (fun e => decide (e ∉ oldE ∩ liveE)) = ins :=
      List.filter_eq_self.mpr (fun x hx => by
        simp only [decide_eq_true_eq, Finset.mem_inter, not_and]
        intro ho; exact False.elim ((Finset.mem_sdiff.mp ((hInsMem x).mp hx)).2 ho))
    have hB : ((oldE ∩ liveE) ∩ newE).toList.filter (fun e => decide (e ∉ oldE ∩ liveE)) = [] :=
      List.filter_eq_nil_iff.mpr (fun x hx => by
        simp only [decide_eq_true_eq, not_not]
        exact (Finset.mem_inter.mp (Finset.mem_toList.mp hx)).1)
    rw [hA, hB, List.append_nil]
  have hEq : filterActiveEdits (oldE ∩ liveE) edits = ds'.map .delete ++ ins.map .insert := by
    rw [hSplit]
    simp only [filterActiveEdits, List.filter_append, List.filter_map, Function.comp_def, ds']
    congr 1
    simp
  rwa [hF1, hF2, ← hEq] at hOf

end MinCostFlow.MinRatio
