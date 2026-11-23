module

public import MinCostFlow.MinRatio.OrdBatchEdits
public import MinCostFlow.MinRatio.FreshBatchRefresh
public import MinCostFlow.SparseCore.Program.AssemblyUnique
public import MinCostFlow.SparseCore.Program.OrdEditsBlocks
import Mathlib.Tactic

/-!
# Level-0 order edits satisfy `OrdEditsValidFor`

At level `0` of the ordered chain (`Chain.Ordered.Algorithm1`), `level0BatchToOrdEditsBody`
(`MinRatio/OrdBatchEdits.lean`) translates a level-`0` fresh-ID edge-only batch `U` into
`batchToOrdEdits U`, mapping `.insert e x y` to `[.insertBefore x (e, true) none,
.insertBefore y (e, false) none]` and `.delete e` to `[.dropEdge e]`.

The uniform sparse-core contract `sparseCoreOrdMachineContractKF`
(`SparseCore/Program/AssemblyStatement.lean`) requires `OrdEditsValidFor vCap eCap a.ord edits`
(both `OrdEditsWithin` and `OrdEditsUniqueWithin`, i.e., every edit stays within `(vCap, eCap)`
and every prefix leaves every end in at most one vertex list).

Proves:
- `ordEditsWithin_batchToOrdEdits`: every edit of `batchToOrdEdits U` stays within `(vCap, eCap)`
  for any edge-only batch `U` satisfying `BatchWithinCaps vCap eCap U`.
- `ordEditsUniqueWithin_batchToOrdEdits`: every prefix of `batchToOrdEdits U` preserves
  `OrdUniqueWithin vCap eCap` starting from `sortedEnds G` whenever `G` is valid within
  `(vCap, eCap)` and `U` is a valid edge-only batch with fresh increasing edge IDs
  (`FreshIdsAlongBatch G U`).
- `ordEditsValidFor_batchToOrdEdits`: combines both into `OrdEditsValidFor`.
- `ordEditsValidFor_level0_translateBatch`: discharges `OrdEditsValidFor` directly for the
  translated internal batch produced by `translateBatch` under `FreshInv` and `RefreshBatch`.
- `ordEditsForBatch_batchToOrdEdits` and `ordEditsForBatch_level0_translateBatch`: the level-`0`
  edits come in one block per update of the batch (`OrdEditsForBatch`), which the block-aligned
  contract asks of an update. Both follow from `ordEditsForBatch_edgeOnly_flatMap`, since
  `batchToOrdEdits` maps each update to its own block and a translated batch has no split.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.IPM.Machine MinCostFlow.SparseCore.Program

/-- Every edit of `batchToOrdEdits U` names vertices below `vCap` and edges below `eCap`
whenever `G` is valid within `(vCap, eCap)` and `U` is a valid edge-only batch within
`(vCap, eCap)`. -/
theorem ordEditsWithin_batchToOrdEdits {G : MGraph} {vCap eCap : ℕ} {U : List Update}
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hval : G.BatchIsValid U) (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hcaps : BatchWithinCaps vCap eCap U) :
    OrdEditsWithin vCap eCap (batchToOrdEdits U) := by
  induction U generalizing G with
  | nil => intro edit hedit; simp [batchToOrdEdits] at hedit
  | cons u rest ih =>
    have hu := hedge u List.mem_cons_self
    have hrest := fun v hv => hedge v (List.mem_cons_of_mem u hv)
    have hcu := hcaps u List.mem_cons_self
    have hcrest := fun v hv => hcaps v (List.mem_cons_of_mem u hv)
    cases u with
    | split _ _ _ _ => exact hu.elim
    | delete e =>
      have hV1 : ∀ v ∈ (G.applyUpdate (.delete e)).V, v < vCap := hV
      have hE1 : ∀ f ∈ (G.applyUpdate (.delete e)).E, f < eCap := fun f hf =>
        hE f (Finset.mem_erase.mp hf).2
      have htail := ih hV1 hE1 hval.2 hrest hcrest
      intro edit hedit
      simp only [batchToOrdEdits, List.flatMap_cons, edgeUpdateToOrdEdits, List.singleton_append,
        List.mem_cons] at hedit
      rcases hedit with rfl | hedit
      · exact hE e hval.1
      · exact htail edit hedit
    | insert e x y =>
      have heCap : e < eCap := hcu
      have hV1 : ∀ v ∈ (G.applyUpdate (.insert e x y)).V, v < vCap := hV
      have hE1 : ∀ f ∈ (G.applyUpdate (.insert e x y)).E, f < eCap := fun f hf => by
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact heCap
        · exact hE f hf
      have htail := ih hV1 hE1 hval.2 hrest hcrest
      intro edit hedit
      simp only [batchToOrdEdits, List.flatMap_cons, edgeUpdateToOrdEdits, List.cons_append,
        List.nil_append, List.mem_cons] at hedit
      rcases hedit with rfl | rfl | hedit
      · exact ⟨hV x hval.1.2.1, heCap, fun _ h => nomatch h⟩
      · exact ⟨hV y hval.1.2.2, heCap, fun _ h => nomatch h⟩
      · exact htail edit hedit

/-- Inserting a fresh end `(e, true)` at `x < vCap` with `e < eCap` above all edges of `G`
preserves `OrdUniqueWithin vCap eCap`. -/
private theorem ordUniqueWithin_insertTail_sortedEnds {G : MGraph} {vCap eCap e x : ℕ}
    (hG : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ f ∈ G.E, f < eCap)
    (hfresh : ∀ f ∈ G.E, f < e) (hx : x < vCap) (he : e < eCap) :
    OrdUniqueWithin vCap eCap (applyOrdEdit (sortedEnds G) (.insertBefore x (e, true) none)) := by
  have hbase : OrdUniqueWithin vCap eCap (sortedEnds G) :=
    ordUniqueWithin_of_rotation (ord := sortedEnds G) hG hV hE ⟨sortedRotation G, rfl⟩
  have hnotMem : ∀ u, (e, true) ∉ sortedEnds G u := fun u hm =>
    Nat.lt_irrefl e (hfresh e ((mem_sortedEnds G u (e, true)).mp hm).1)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro v
    dsimp only [applyOrdEdit, insertBeforeList]
    by_cases hv : v = x
    · subst hv
      rw [Function.update_self, List.nodup_append]
      exact ⟨hbase.nodup v, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; intro heq; exact hnotMem v (heq ▸ ha)⟩
    · rw [Function.update_of_ne hv]
      exact hbase.nodup v
  · intro v hv
    dsimp only [applyOrdEdit, insertBeforeList]
    rw [Function.update_of_ne (by omega : v ≠ x)]
    exact hbase.eq_nil_of_ge hv
  · intro v z hz
    dsimp only [applyOrdEdit, insertBeforeList] at hz
    by_cases hv : v = x
    · subst hv
      rw [Function.update_self, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hbase.edge_lt hz
      · exact he
    · rw [Function.update_of_ne hv] at hz
      exact hbase.edge_lt hz
  · intro u v z hu hv
    dsimp only [applyOrdEdit, insertBeforeList] at hu hv
    by_cases hux : u = x <;> by_cases hvx : v = x
    · exact hux.trans hvx.symm
    · subst hux
      rw [Function.update_self, List.mem_append, List.mem_singleton] at hu
      rw [Function.update_of_ne hvx] at hv
      rcases hu with hu | rfl
      · exact hbase.unique_v hu hv
      · exact False.elim (hnotMem v hv)
    · subst hvx
      rw [Function.update_of_ne hux] at hu
      rw [Function.update_self, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hbase.unique_v hu hv
      · exact False.elim (hnotMem u hu)
    · rw [Function.update_of_ne hux] at hu
      rw [Function.update_of_ne hvx] at hv
      exact hbase.unique_v hu hv

/-- Every prefix of `batchToOrdEdits U` preserves `OrdUniqueWithin vCap eCap` starting from
`sortedEnds G`. -/
theorem ordEditsUniqueWithin_batchToOrdEdits {G : MGraph} {vCap eCap : ℕ} {U : List Update}
    (hG : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hval : G.BatchIsValid U) (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hfresh : FreshIdsAlongBatch G U) (hcaps : BatchWithinCaps vCap eCap U) :
    OrdEditsUniqueWithin vCap eCap (sortedEnds G) (batchToOrdEdits U) := by
  induction U generalizing G with
  | nil =>
    intro k hk
    have hk0 : k = 0 := by simp [batchToOrdEdits] at hk; omega
    subst hk0
    exact ordUniqueWithin_of_rotation (ord := sortedEnds G) hG hV hE ⟨sortedRotation G, rfl⟩
  | cons u rest ih =>
    have hu := hedge u List.mem_cons_self
    have hrest := fun v hv => hedge v (List.mem_cons_of_mem u hv)
    have hcu := hcaps u List.mem_cons_self
    have hcrest := fun v hv => hcaps v (List.mem_cons_of_mem u hv)
    have hG1 : (G.applyUpdate u).IsValid := applyUpdate_isValid hG hval.1
    cases u with
    | split _ _ _ _ => exact hu.elim
    | delete e =>
      have hV1 : ∀ v ∈ (G.applyUpdate (.delete e)).V, v < vCap := hV
      have hE1 : ∀ f ∈ (G.applyUpdate (.delete e)).E, f < eCap := fun f hf =>
        hE f (Finset.mem_erase.mp hf).2
      have hih := ih hG1 hV1 hE1 hval.2 hrest hfresh hcrest
      intro k hk
      cases k with
      | zero =>
        exact ordUniqueWithin_of_rotation (ord := sortedEnds G) hG hV hE ⟨sortedRotation G, rfl⟩
      | succ k' =>
        have hk' : k' ≤ (batchToOrdEdits rest).length := by
          dsimp only [batchToOrdEdits, List.flatMap_cons, edgeUpdateToOrdEdits,
            List.singleton_append, List.length_cons] at hk
          exact Nat.le_of_succ_le_succ hk
        have htake : (batchToOrdEdits (.delete e :: rest)).take (k' + 1) =
            .dropEdge e :: (batchToOrdEdits rest).take k' := by
          simp [batchToOrdEdits, edgeUpdateToOrdEdits]
        rw [htake, applyOrdEdits, List.foldl_cons, applyOrdEdit_sortedEnds_delete]
        exact hih k' hk'
    | insert e x y =>
      have heCap : e < eCap := hcu
      have hV1 : ∀ v ∈ (G.applyUpdate (.insert e x y)).V, v < vCap := hV
      have hE1 : ∀ f ∈ (G.applyUpdate (.insert e x y)).E, f < eCap := fun f hf => by
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact heCap
        · exact hE f hf
      have hih := ih hG1 hV1 hE1 hval.2 hrest hfresh.2 hcrest
      intro k hk
      match k with
      | 0 =>
        exact ordUniqueWithin_of_rotation (ord := sortedEnds G) hG hV hE ⟨sortedRotation G, rfl⟩
      | 1 =>
        have htake : (batchToOrdEdits (.insert e x y :: rest)).take 1 =
            [.insertBefore x (e, true) none] := by
          simp [batchToOrdEdits, edgeUpdateToOrdEdits]
        rw [htake, applyOrdEdits, List.foldl_cons, List.foldl_nil]
        exact ordUniqueWithin_insertTail_sortedEnds hG hV hE hfresh.1 (hV x hval.1.2.1) heCap
      | k' + 2 =>
        have hk' : k' ≤ (batchToOrdEdits rest).length := by
          simp only [batchToOrdEdits, List.flatMap_cons, edgeUpdateToOrdEdits,
            List.cons_append, List.nil_append, List.length_cons] at hk ⊢
          omega
        have htake : (batchToOrdEdits (.insert e x y :: rest)).take (k' + 2) =
            [.insertBefore x (e, true) none, .insertBefore y (e, false) none] ++
              (batchToOrdEdits rest).take k' := by
          simp [batchToOrdEdits, edgeUpdateToOrdEdits]
        rw [htake, applyOrdEdits, List.foldl_append]
        have hpair : List.foldl applyOrdEdit (sortedEnds G)
            [.insertBefore x (e, true) none, .insertBefore y (e, false) none] =
            sortedEnds (G.applyUpdate (.insert e x y)) :=
          applyOrdEdits_sortedEnds_insert hfresh.1
        rw [hpair]
        exact hih k' hk'

/-- Level-0 order edits `batchToOrdEdits U` satisfy `OrdEditsValidFor vCap eCap (sortedEnds G)`
whenever `G` is valid within `(vCap, eCap)` and `U` is a valid fresh-ID edge-only batch within
`(vCap, eCap)`. -/
theorem ordEditsValidFor_batchToOrdEdits {G : MGraph} {vCap eCap : ℕ} {U : List Update}
    (hG : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hval : G.BatchIsValid U) (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hfresh : FreshIdsAlongBatch G U) (hcaps : BatchWithinCaps vCap eCap U) :
    OrdEditsValidFor vCap eCap (sortedEnds G) (batchToOrdEdits U) :=
  ⟨ordEditsWithin_batchToOrdEdits hV hE hval hedge hcaps,
   ordEditsUniqueWithin_batchToOrdEdits hG hV hE hval hedge hfresh hcaps⟩

private theorem translateBatch_nextFresh_le (U : List Update) :
    ∀ (G : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      nf ≤ (translateBatch G e2i i2e nf U).2.2.2.1 := by
  induction U with
  | nil => intro _ _ _ _; exact le_rfl
  | cons u rest ih =>
    intro G e2i i2e nf
    cases u with
    | delete e => exact ih _ _ _ _
    | insert e x y => exact le_trans (Nat.le_succ nf) (ih _ _ _ _)
    | split v v' St Sh => exact ih _ _ _ _

/-- Helper: every update of the translated internal batch `U_int` from `translateBatch` stays
within `(vCap, eCap)` whenever `nf' ≤ eCap` and `extG.BatchIsValid U` is edge-only. -/
theorem translateBatch_withinCaps {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf vCap eCap : ℕ}
    {U : List Update}
    (hfresh : FreshInv extG intG e2i i2e nf)
    (hnfCap : (translateBatch extG e2i i2e nf U).2.2.2.1 ≤ eCap)
    (hval : extG.BatchIsValid U)
    (hedge : ∀ u ∈ U, IsEdgeUpdate u) :
    BatchWithinCaps vCap eCap (translateBatch extG e2i i2e nf U).2.2.2.2 := by
  induction U generalizing extG intG e2i i2e nf with
  | nil =>
    intro u hu; cases hu
  | cons u rest ih =>
    have hu := hedge u List.mem_cons_self
    have hrest := fun v hv => hedge v (List.mem_cons_of_mem u hv)
    have htr := translateUpdate_preserves hfresh hval.1
    cases u with
    | split _ _ _ _ => exact hu.elim
    | delete e =>
      dsimp only [translateBatch, translateUpdate] at htr hnfCap ⊢
      have htail := ih htr.1 hnfCap hval.2 hrest
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · trivial
      · exact htail w hw
    | insert e x y =>
      dsimp only [translateBatch, translateUpdate] at htr hnfCap ⊢
      have htail := ih htr.1 hnfCap hval.2 hrest
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · have hle : nf + 1 ≤ (translateBatch (extG.applyUpdate (.insert e x y))
            (Function.update e2i e nf) (Function.update i2e nf e) (nf + 1) rest).2.2.2.1 :=
          translateBatch_nextFresh_le rest _ _ _ _
        exact Nat.lt_of_succ_le (hle.trans hnfCap)
      · exact htail w hw

/-- Level-0 `translateBatch` order edits unconditionally satisfy `OrdEditsValidFor vCap eCap`
against `sortedEnds intG` whenever `intG` is valid within `(vCap, eCap)`, `FreshInv` holds,
`RefreshBatch extG U` holds, and `nf' ≤ eCap`. -/
theorem ordEditsValidFor_level0_translateBatch {extG intG : MGraph}
    {e2i i2e : ℕ → ℕ} {nf vCap eCap : ℕ} {U : List Update}
    (hG : intG.IsValid) (hV : ∀ v ∈ intG.V, v < vCap) (hE : ∀ e ∈ intG.E, e < eCap)
    (hfresh : FreshInv extG intG e2i i2e nf)
    (hRef : RefreshBatch extG U)
    (hnfCap : (translateBatch extG e2i i2e nf U).2.2.2.1 ≤ eCap) :
    OrdEditsValidFor vCap eCap (sortedEnds intG)
      (batchToOrdEdits (translateBatch extG e2i i2e nf U).2.2.2.2) := by
  have hedgeExt : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have := hRef.2.2 u hu
    cases u with
    | split _ _ _ _ => exact this
    | insert _ _ _ => trivial
    | delete _ => trivial
  have hvalInt : intG.BatchIsValid (translateBatch extG e2i i2e nf U).2.2.2.2 :=
    (translateBatch_preserves U extG intG e2i i2e nf hfresh hRef.1).2.2.1
  obtain ⟨hedgeInt, hfreshInt⟩ := translateBatch_freshIdsAlongBatch hfresh hRef.1 hedgeExt
  have hcaps := translateBatch_withinCaps (vCap := vCap) hfresh hnfCap hRef.1 hedgeExt
  exact ordEditsValidFor_batchToOrdEdits hG hV hE hvalInt hedgeInt hfreshInt hcaps

/-- The edits `batchToOrdEdits U` of an edge-only batch come in one block per update of `U`:
`[.dropEdge e]` for a deletion and two `insertBefore` edits for an insertion. -/
theorem ordEditsForBatch_batchToOrdEdits {G : MGraph} {U : List Update}
    (hedge : ∀ u ∈ U, IsEdgeUpdate u) :
    OrdEditsForBatch G U (batchToOrdEdits U) := by
  refine ordEditsForBatch_edgeOnly_flatMap (fun _ => rfl) (fun _ _ _ => ⟨none, none, rfl⟩) ?_
  intro u hu
  have h := hedge u hu
  cases u with
  | split _ _ _ _ => exact h.elim
  | insert _ _ _ => trivial
  | delete _ => trivial

/-- **Level `0` of the block-aligned contract.** The edits that the solver writes for the
translated internal batch of a refresh batch come in one block per update of that batch. The
translated batch has only edge updates (`translateBatch_freshIdsAlongBatch`), so this is
`ordEditsForBatch_batchToOrdEdits`. -/
theorem ordEditsForBatch_level0_translateBatch {extG intG : MGraph}
    {e2i i2e : ℕ → ℕ} {nf : ℕ} {U : List Update}
    (hfresh : FreshInv extG intG e2i i2e nf)
    (hRef : RefreshBatch extG U) :
    OrdEditsForBatch intG (translateBatch extG e2i i2e nf U).2.2.2.2
      (batchToOrdEdits (translateBatch extG e2i i2e nf U).2.2.2.2) := by
  have hedgeExt : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have := hRef.2.2 u hu
    cases u with
    | split _ _ _ _ => exact this
    | insert _ _ _ => trivial
    | delete _ => trivial
  exact ordEditsForBatch_batchToOrdEdits
    (translateBatch_freshIdsAlongBatch hfresh hRef.1 hedgeExt).1

end MinCostFlow.MinRatio
