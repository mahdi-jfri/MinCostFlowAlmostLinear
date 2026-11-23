module

public import MinCostFlow.SparseCore.Program.ContractOrder
public import MinCostFlow.MinRatio.OrdSparseCoreHelpers
public import MinCostFlow.MinRatio.FreshBatch
import WordRAM.Tactic

/-!
# Level-0 order edits for fresh-ID edge batches (`OrdBatchEdits`)

At level `0` of the ordered chain (`Chain.Ordered.Algorithm1`), the input order is
`Bundle.sortedEnds (G 0)`, and every batch `U_int` produced by `translateBatch` consists solely
of edge deletions and edge insertions whose internal IDs are strictly greater than every
previously live edge ID (`FreshInv`).

This file provides:
1. `edgeUpdateToOrdEdits` and `batchToOrdEdits`: pure translation mapping `.insert e x y` to
   `[.insertBefore x (e, true) none, .insertBefore y (e, false) none]` and `.delete e` to
   `[.dropEdge e]`.
2. `applyOrdEdits_sortedEnds_batch` and `orderedBatch_sortedEnds_of_edgeOnly`: proves that
   applying `batchToOrdEdits U` transforms `sortedEnds G` into `sortedEnds (G.applyBatch U)`
   and witnesses `OrderedBatch G U (sortedEnds G) (sortedEnds (G.applyBatch U))`.
3. `level0BatchToOrdEditsBody` (`NoRand`) and `level0BatchToOrdEditsBody_runs`: deterministic
   Word-RAM procedure reading `BatchAt mem uIntBuf U` and writing `OrdEditsAt mem outEdits
   (batchToOrdEdits U) editWords` in `O(|U|)` steps and at most `8 * |U| + 1` words.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Translate one edge-only update into `OrdEdit` records for `sortedEnds`.
When inserted edge IDs are strictly larger than all existing live IDs, appending `(e, true)` at
`x` then `(e, false)` at `y` preserves `endLE` order (including self-loops, since `2*e < 2*e+1`). -/
@[expose] def edgeUpdateToOrdEdits : Update → List OrdEdit
  | .insert e x y => [.insertBefore x (e, true) none, .insertBefore y (e, false) none]
  | .delete e => [.dropEdge e]
  | .split _ _ _ _ => []

/-- Translate a batch of edge-only updates into `OrdEdit` records. -/
@[expose] def batchToOrdEdits (U : List Update) : List OrdEdit :=
  U.flatMap edgeUpdateToOrdEdits

/-- Fresh-ID monotonicity along a batch: every insertion introduces an edge ID strictly larger
than every edge ID currently live in the graph. -/
@[expose] def FreshIdsAlongBatch : MGraph → List Update → Prop
  | _, [] => True
  | G, .insert e x y :: rest =>
    (∀ f ∈ G.E, f < e) ∧ FreshIdsAlongBatch (G.applyUpdate (.insert e x y)) rest
  | G, u :: rest => FreshIdsAlongBatch (G.applyUpdate u) rest

private theorem sortedEnds_eq_of_props {xs ys : List End} (hx : xs.Nodup) (hy : ys.Nodup)
    (hsx : xs.Pairwise endLE) (hsy : ys.Pairwise endLE)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys :=
  (List.perm_ext_iff_of_nodup hx hy |>.mpr hm).eq_of_pairwise' hsx hsy

private theorem sortedEnds_nodup (G : MGraph) (v : ℕ) : (sortedEnds G v).Nodup :=
  (sortedRotation G).nodup v

private theorem sortedEnds_pairwise (G : MGraph) (v : ℕ) : (sortedEnds G v).Pairwise endLE :=
  Finset.pairwise_sort _ _

/-- Applying `.dropEdge e` to `sortedEnds G` gives `sortedEnds (G.applyUpdate (.delete e))`. -/
theorem applyOrdEdit_sortedEnds_delete (G : MGraph) (e : ℕ) :
    applyOrdEdit (sortedEnds G) (.dropEdge e) = sortedEnds (G.applyUpdate (.delete e)) := by
  funext v
  refine sortedEnds_eq_of_props
    ((sortedEnds_nodup G v).filter _) (sortedEnds_nodup _ v)
    ((sortedEnds_pairwise G v).filter _) (sortedEnds_pairwise _ v) ?_
  intro x
  simp only [applyOrdEdit, List.mem_filter, mem_sortedEnds, MGraph.applyUpdate, MGraph.src,
    Finset.mem_erase, bne_iff_ne]
  exact ⟨fun ⟨⟨he, hs⟩, hn⟩ => ⟨⟨hn, he⟩, hs⟩, fun ⟨⟨hn, he⟩, hs⟩ => ⟨⟨he, hs⟩, hn⟩⟩

/-- Appending `(e, true)` at `x` then `(e, false)` at `y` to `sortedEnds G` gives
`sortedEnds (G.applyUpdate (.insert e x y))` whenever `e` is strictly above every live edge ID. -/
theorem applyOrdEdits_sortedEnds_insert {G : MGraph} {e x y : ℕ}
    (hfresh : ∀ f ∈ G.E, f < e) :
    applyOrdEdits (sortedEnds G) [.insertBefore x (e, true) none, .insertBefore y (e, false) none] =
      sortedEnds (G.applyUpdate (.insert e x y)) := by
  have hltTail : ∀ v (z : End), z ∈ sortedEnds G v → endKey z < endKey (e, true) := by
    intro v z hz
    have hf : z.1 < e := hfresh z.1 ((mem_sortedEnds G v z).mp hz).1
    cases z with | mk f b => cases b <;> simp [endKey] <;> omega
  have hltHead : ∀ v (z : End), z ∈ sortedEnds G v → endKey z < endKey (e, false) := by
    intro v z hz
    have hf : z.1 < e := hfresh z.1 ((mem_sortedEnds G v z).mp hz).1
    cases z with | mk f b => cases b <;> simp [endKey] <;> omega
  have hnotMem : ∀ v (b : Bool), (e, b) ∉ sortedEnds G v := fun v b hm =>
    Nat.lt_irrefl e (hfresh e ((mem_sortedEnds G v (e, b)).mp hm).1)
  have heNotE : e ∉ G.E := fun h => Nat.lt_irrefl e (hfresh e h)
  funext v
  dsimp only [applyOrdEdits, List.foldl, applyOrdEdit, insertBeforeList]
  have hstep : ∀ z : End,
      z ∈ Function.update (Function.update (sortedEnds G) x (sortedEnds G x ++ [(e, true)])) y
        (Function.update (sortedEnds G) x (sortedEnds G x ++ [(e, true)]) y ++ [(e, false)]) v ↔
      z ∈ sortedEnds (G.applyUpdate (.insert e x y)) v := by
    intro z
    rw [mem_sortedEnds]
    by_cases hvy : v = y <;> by_cases hvx : v = x
    · subst hvy; subst hvx
      simp only [Function.update_self, List.mem_append, List.mem_singleton, mem_sortedEnds,
        MGraph.applyUpdate, MGraph.src, Finset.mem_insert]
      cases z with
      | mk f b =>
        cases b <;> by_cases hfe : f = e
        · subst hfe; simp [heNotE]
        · simp [hfe, Function.update_of_ne]
        · subst hfe; simp [heNotE]
        · simp [hfe, Function.update_of_ne]
    · subst hvy
      simp only [Function.update_self, Function.update_of_ne hvx, List.mem_append,
        List.mem_singleton, mem_sortedEnds, MGraph.applyUpdate, MGraph.src, Finset.mem_insert]
      cases z with
      | mk f b =>
        cases b <;> by_cases hfe : f = e
        · subst hfe; simp [heNotE]
        · simp [hfe, Function.update_of_ne]
        · subst hfe; simp [heNotE, Ne.symm hvx]
        · simp [hfe, Function.update_of_ne]
    · subst hvx
      simp only [Function.update_of_ne hvy, Function.update_self, List.mem_append,
        List.mem_singleton, mem_sortedEnds, MGraph.applyUpdate, MGraph.src, Finset.mem_insert]
      cases z with
      | mk f b =>
        cases b <;> by_cases hfe : f = e
        · subst hfe; simp [heNotE, Ne.symm hvy]
        · simp [hfe, Function.update_of_ne]
        · subst hfe; simp [heNotE]
        · simp [hfe, Function.update_of_ne]
    · simp only [Function.update_of_ne hvy, Function.update_of_ne hvx, mem_sortedEnds,
        MGraph.applyUpdate, MGraph.src, Finset.mem_insert]
      cases z with
      | mk f b =>
        cases b <;> by_cases hfe : f = e
        · subst hfe; simp [heNotE, Ne.symm hvy]
        · simp [hfe, Function.update_of_ne]
        · subst hfe; simp [heNotE, Ne.symm hvx]
        · simp [hfe, Function.update_of_ne]
  refine sortedEnds_eq_of_props ?_ (sortedEnds_nodup _ v) ?_ (sortedEnds_pairwise _ v) hstep
  · by_cases hvy : v = y <;> by_cases hvx : v = x
    · subst hvy; subst hvx
      simp only [Function.update_self]
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨sortedEnds_nodup G v, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; intro heq; exact hnotMem v true (heq ▸ ha)⟩,
        List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; intro heq; subst heq
        rcases List.mem_append.mp ha with hm | hm
        · exact hnotMem v false hm
        · simp at hm⟩
    · subst hvy
      simp only [Function.update_self, Function.update_of_ne hvx]
      rw [List.nodup_append]
      exact ⟨sortedEnds_nodup G v, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; intro heq; exact hnotMem v false (heq ▸ ha)⟩
    · subst hvx
      simp only [Function.update_of_ne hvy, Function.update_self]
      rw [List.nodup_append]
      exact ⟨sortedEnds_nodup G v, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; intro heq; exact hnotMem v true (heq ▸ ha)⟩
    · simp only [Function.update_of_ne hvy, Function.update_of_ne hvx]
      exact sortedEnds_nodup G v
  · by_cases hvy : v = y <;> by_cases hvx : v = x
    · subst hvy; subst hvx
      simp only [Function.update_self]
      rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨sortedEnds_pairwise G v, List.pairwise_singleton _ _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; exact le_of_lt (hltTail v a ha)⟩,
        List.pairwise_singleton _ _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]
        rcases List.mem_append.mp ha with hm | hm
        · exact le_of_lt (hltHead v a hm)
        · rw [List.mem_singleton.mp hm]; simp [endLE, endKey]⟩
    · subst hvy
      simp only [Function.update_self, Function.update_of_ne hvx]
      rw [List.pairwise_append]
      exact ⟨sortedEnds_pairwise G v, List.pairwise_singleton _ _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; exact le_of_lt (hltHead v a ha)⟩
    · subst hvx
      simp only [Function.update_of_ne hvy, Function.update_self]
      rw [List.pairwise_append]
      exact ⟨sortedEnds_pairwise G v, List.pairwise_singleton _ _, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; exact le_of_lt (hltTail v a ha)⟩
    · simp only [Function.update_of_ne hvy, Function.update_of_ne hvx]
      exact sortedEnds_pairwise G v

/-- Applying `batchToOrdEdits U` to `sortedEnds G` gives `sortedEnds (G.applyBatch U)`
for every edge-only batch with fresh increasing edge IDs. -/
theorem applyOrdEdits_sortedEnds_batch {G : MGraph} {U : List Update}
    (hedge : ∀ u ∈ U, IsEdgeUpdate u) (hfresh : FreshIdsAlongBatch G U) :
    applyOrdEdits (sortedEnds G) (batchToOrdEdits U) = sortedEnds (G.applyBatch U) := by
  induction U generalizing G with
  | nil => rfl
  | cons u rest ih =>
    have hu := hedge u List.mem_cons_self
    have hrest := fun v hv => hedge v (List.mem_cons_of_mem u hv)
    rw [batchToOrdEdits, List.flatMap_cons, applyOrdEdits, List.foldl_append]
    dsimp only [MGraph.applyBatch]
    cases u with
    | split _ _ _ _ => exact hu.elim
    | delete e =>
      have h1 : List.foldl applyOrdEdit (sortedEnds G) (edgeUpdateToOrdEdits (.delete e)) =
          sortedEnds (G.applyUpdate (.delete e)) := by
        simpa [edgeUpdateToOrdEdits] using applyOrdEdit_sortedEnds_delete G e
      rw [h1]
      exact ih hrest hfresh
    | insert e x y =>
      have h1 : List.foldl applyOrdEdit (sortedEnds G) (edgeUpdateToOrdEdits (.insert e x y)) =
          sortedEnds (G.applyUpdate (.insert e x y)) :=
        applyOrdEdits_sortedEnds_insert hfresh.1
      rw [h1]
      exact ih hrest hfresh.2

/-- Every valid edge-only batch is an `OrderedBatch` between `sortedEnds G` and
`sortedEnds (G.applyBatch U)`. -/
theorem orderedBatch_sortedEnds_of_edgeOnly {G : MGraph} {U : List Update}
    (hval : G.BatchIsValid U) (hedge : ∀ u ∈ U, IsEdgeUpdate u) :
    OrderedBatch G U (sortedEnds G) (sortedEnds (G.applyBatch U)) :=
  ⟨sortedRotation G, sortedRotation (G.applyBatch U), rfl, rfl,
    (sortedRotation_batch hval hedge).mono (by decide)⟩

/-- Helper: `translateBatch` always produces edge-only updates with fresh increasing IDs
strictly above every live internal edge ID. -/
theorem translateBatch_freshIdsAlongBatch {extG intG : MGraph}
    {e2i i2e : ℕ → ℕ} {nf : ℕ} {U : List Update}
    (hfresh : FreshInv extG intG e2i i2e nf)
    (hvalid : extG.BatchIsValid U)
    (hedge : ∀ u ∈ U, IsEdgeUpdate u) :
    let U_int := (translateBatch extG e2i i2e nf U).2.2.2.2
    (∀ u ∈ U_int, IsEdgeUpdate u) ∧ FreshIdsAlongBatch intG U_int := by
  induction U generalizing extG intG e2i i2e nf with
  | nil =>
    simp [translateBatch, FreshIdsAlongBatch]
  | cons u rest ih =>
    have hu := hedge u List.mem_cons_self
    have hrest := fun v hv => hedge v (List.mem_cons_of_mem u hv)
    have htr := translateUpdate_preserves hfresh hvalid.1
    cases u with
    | split _ _ _ _ => exact hu.elim
    | delete e =>
      dsimp only [translateBatch, translateUpdate] at htr ⊢
      obtain ⟨hEdgeR, hFreshR⟩ := ih htr.1 hvalid.2 hrest
      refine ⟨fun v hv => ?_, hFreshR⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · trivial
      · exact hEdgeR v hv
    | insert e x y =>
      dsimp only [translateBatch, translateUpdate] at htr ⊢
      obtain ⟨hEdgeR, hFreshR⟩ := ih htr.1 hvalid.2 hrest
      refine ⟨fun v hv => ?_, ⟨fun f hf => hfresh.hLtFresh f hf, hFreshR⟩⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · trivial
      · exact hEdgeR v hv

/-- Deterministic Word-RAM procedure converting a level-0 fresh-ID edge-only batch at `reg 0`
(`BatchAt mem uIntBuf U`) into `OrdEditsAt` at `reg 1` (`outEdits`), returning `editWords`. -/
@[expose] def level0BatchToOrdEditsBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 4 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 5 (.const 0) ;;
  forRange 6 (.const 0) (.reg 2)
    (.assign 7 (.load (.reg 3)) ;;
     .cond (.bin .eq (.reg 7) (.const 0))
       (.assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .assign 9 (.load (.bin .add (.reg 3) (.const 2))) ;;
        .assign 10 (.load (.bin .add (.reg 3) (.const 3))) ;;
        .assign 11 (.bin .mul (.const 2) (.reg 8)) ;;
        .store (.reg 4) (.const 3) ;;
        .store (.bin .add (.reg 4) (.const 1)) (.reg 9) ;;
        .store (.bin .add (.reg 4) (.const 2)) (.reg 11) ;;
        .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
        .store (.bin .add (.reg 4) (.const 4)) (.const 3) ;;
        .store (.bin .add (.reg 4) (.const 5)) (.reg 10) ;;
        .store (.bin .add (.reg 4) (.const 6)) (.bin .add (.reg 11) (.const 1)) ;;
        .store (.bin .add (.reg 4) (.const 7)) (.const 0) ;;
        .assign 3 (.bin .add (.reg 3) (.const 4)) ;;
        .assign 4 (.bin .add (.reg 4) (.const 8)) ;;
        .assign 5 (.bin .add (.reg 5) (.const 2)))
       (.assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .store (.reg 4) (.const 0) ;;
        .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
        .assign 3 (.bin .add (.reg 3) (.const 2)) ;;
        .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
        .assign 5 (.bin .add (.reg 5) (.const 1)))) ;;
  .store (.reg 1) (.reg 5) ;;
  .ret (.bin .sub (.reg 4) (.reg 1))

theorem level0BatchToOrdEditsBody_noRand : level0BatchToOrdEditsBody.NoRand := by
  simp [level0BatchToOrdEditsBody, forRange, forUp, Stmt.NoRand]

/-- Word count of an `OrdEdits` encoding emitted by `level0BatchToOrdEditsBody` for one update. -/
@[expose] def edgeUpdateOrdWords : Update → ℕ
  | .insert _ _ _ => 8
  | .delete _ => 2
  | .split _ _ _ _ => 0

/-- Total payload words emitted by `level0BatchToOrdEditsBody` for a prefix `U`. -/
@[expose] def batchOrdPayloadWords (U : List Update) : ℕ :=
  (U.map edgeUpdateOrdWords).sum

private theorem batchOrdPayloadWords_le (U : List Update) :
    batchOrdPayloadWords U ≤ 8 * U.length := by
  induction U with
  | nil => simp [batchOrdPayloadWords]
  | cons u rest ih =>
    simp only [batchOrdPayloadWords, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    cases u <;> simp only [edgeUpdateOrdWords] <;> omega

private theorem batchToOrdEdits_length_le (U : List Update) :
    (batchToOrdEdits U).length ≤ 2 * U.length := by
  induction U with
  | nil => simp [batchToOrdEdits]
  | cons u rest ih =>
    simp only [batchToOrdEdits, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    cases u <;> simp only [edgeUpdateToOrdEdits, List.length_cons, List.length_nil] <;> omega

private theorem batchOrdPayloadWords_le_5_enc (U : List Update)
    (hedge : ∀ u ∈ U, IsEdgeUpdate u) :
    batchOrdPayloadWords U ≤ 5 * ordEditsEnc (batchToOrdEdits U) := by
  induction U with
  | nil => simp [batchOrdPayloadWords, batchToOrdEdits, ordEditsEnc]
  | cons u rest ih =>
    have hu := hedge u List.mem_cons_self
    have hr := ih (fun v hv => hedge v (List.mem_cons_of_mem u hv))
    simp only [batchOrdPayloadWords, List.map_cons, List.sum_cons, batchToOrdEdits,
      List.flatMap_cons, ordEditsEnc, List.map_append, List.sum_append] at hr ⊢
    cases u with
    | split _ _ _ _ => exact hu.elim
    | insert e x y => simp only [edgeUpdateOrdWords, edgeUpdateToOrdEdits, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, OrdEdit.enc]; omega
    | delete e => simp only [edgeUpdateOrdWords, edgeUpdateToOrdEdits, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, OrdEdit.enc]; omega

private theorem decodeOrdEdits_congr (mem₁ mem₂ : ℕ → ℕ) :
    ∀ (cnt a : ℕ),
      (∀ x, a ≤ x → x < a + (decodeOrdEdits mem₁ cnt a).2.sum → mem₂ x = mem₁ x) →
      decodeOrdEdits mem₂ cnt a = decodeOrdEdits mem₁ cnt a := by
  intro cnt
  induction cnt with
  | zero => intros; rfl
  | succ cnt ih =>
    intro a hag
    have hdLen : (decodeOrdEdit mem₁ a).2 ≤ (decodeOrdEdits mem₁ (cnt + 1) a).2.sum := by
      simp [decodeOrdEdits]
    have h0 : mem₂ a = mem₁ a := by
      apply hag a le_rfl
      have hpos : 0 < (decodeOrdEdit mem₁ a).2 := by
        unfold decodeOrdEdit; split_ifs <;> omega
      omega
    have hd : decodeOrdEdit mem₂ a = decodeOrdEdit mem₁ a := by
      unfold decodeOrdEdit
      rw [h0]
      by_cases htag0 : mem₁ a = 0
      · simp only [htag0, ↓reduceIte]
        have hlen : (decodeOrdEdit mem₁ a).2 = 2 := by unfold decodeOrdEdit; simp [htag0]
        have h1 := hag (a + 1) (by omega) (by omega)
        rw [h1]
      · simp only [htag0, ↓reduceIte]
        by_cases htag12 : mem₁ a = 1 ∨ mem₁ a = 2
        · simp only [htag12, ↓reduceIte]
          have hlen : (decodeOrdEdit mem₁ a).2 = 4 + mem₁ (a + 3) := by
            unfold decodeOrdEdit; simp [htag0, htag12]
          have h1 := hag (a + 1) (by omega) (by omega)
          have h2 := hag (a + 2) (by omega) (by omega)
          have h3 := hag (a + 3) (by omega) (by omega)
          have hlist : readList mem₂ (a + 4) (mem₂ (a + 3)) = readList mem₁ (a + 4) (mem₁ (a + 3)) := by
            rw [h3]
            unfold readList
            exact List.map_congr_left fun i hi =>
              hag (a + 4 + i) (by omega) (by have := List.mem_range.mp hi; omega)
          rw [hlist, h1, h2, h3]
        · simp only [htag12, ↓reduceIte]
          by_cases htag3 : mem₁ a = 3
          · simp only [htag3, ↓reduceIte]
            have hlen : (decodeOrdEdit mem₁ a).2 = 4 := by
              unfold decodeOrdEdit; simp [htag3]
            have h1 := hag (a + 1) (by omega) (by omega)
            have h2 := hag (a + 2) (by omega) (by omega)
            have h3 := hag (a + 3) (by omega) (by omega)
            rw [h1, h2, h3]
          · simp only [htag3, ↓reduceIte]
            have hlen : (decodeOrdEdit mem₁ a).2 = 3 := by
              unfold decodeOrdEdit; simp [htag0, htag12, htag3]
            have h1 := hag (a + 1) (by omega) (by omega)
            have h2 := hag (a + 2) (by omega) (by omega)
            rw [h1, h2]
    dsimp only [decodeOrdEdits]
    rw [hd]
    have hrest := ih (a + (decodeOrdEdit mem₁ a).2) (fun x hx1 hx2 => by
      apply hag x (by omega)
      have : (decodeOrdEdits mem₁ (cnt + 1) a).2.sum =
          (decodeOrdEdit mem₁ a).2 + (decodeOrdEdits mem₁ cnt (a + (decodeOrdEdit mem₁ a).2)).2.sum := by
        simp [decodeOrdEdits]
      omega)
    rw [hrest]

private theorem decodeOrdEdits_append (mem : ℕ → ℕ) :
    ∀ (c₁ c₂ a : ℕ),
      decodeOrdEdits mem (c₁ + c₂) a =
        let r₁ := decodeOrdEdits mem c₁ a
        let r₂ := decodeOrdEdits mem c₂ (a + r₁.2.sum)
        (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2) := by
  intro c₁
  induction c₁ with
  | zero =>
    intro c₂ a
    simp [decodeOrdEdits]
  | succ c₁ ih =>
    intro c₂ a
    have hadd : c₁ + 1 + c₂ = (c₁ + c₂) + 1 := by omega
    rw [hadd]
    dsimp only [decodeOrdEdits]
    rw [ih c₂ (a + (decodeOrdEdit mem a).2)]
    simp [List.sum_cons, Nat.add_assoc]

private theorem endOfKey_two_mul (e : ℕ) : endOfKey (2 * e) = (e, true) := by
  unfold endOfKey; simp [Nat.mul_mod_right]

private theorem endOfKey_two_mul_add_one (e : ℕ) : endOfKey (2 * e + 1) = (e, false) := by
  unfold endOfKey
  have h1 : (2 * e + 1) / 2 = e := by omega
  have h2 : (2 * e + 1) % 2 = 1 := by omega
  simp [h1, h2]

/-- Execution of `level0BatchToOrdEditsBody [uIntBuf, outEdits]`: reads `IPM.Machine.BatchAt`
for an edge-only batch `U` and writes `OrdEditsAt mem outEdits (batchToOrdEdits U) editWords`,
returning `editWords = 1 + batchOrdPayloadWords U ≤ 8 * U.length + 1` in `O(U.length)` steps. -/
theorem level0BatchToOrdEditsBody_runs {w uIntBuf outEdits pos : ℕ} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {U : List Update}
    (hbatch : IPM.Machine.BatchAt mem uIntBuf U)
    (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hdisj : uIntBuf + (IPM.Machine.batchWords U).length ≤ outEdits)
    (hwordsIn : ∀ j < (IPM.Machine.batchWords U).length, mem (uIntBuf + j) < 2 ^ w)
    (hEdgeKey : ∀ u ∈ U, match u with | .insert e _ _ => 2 * e + 1 < 2 ^ w | _ => True)
    (houtEnd : outEdits + 8 * U.length + 1 < 2 ^ w)
    (hw8 : 8 < 2 ^ w) :
    let edits := batchToOrdEdits U
    let editWords := 1 + batchOrdPayloadWords U
    ∃ cost out,
      Runs w p ω level0BatchToOrdEditsBody
        (startState [uIntBuf, outEdits] mem pos) (.returned editWords) out cost ∧
      cost ≤ 120 * U.length + 40 ∧
      editWords ≤ 8 * U.length + 1 ∧
      OrdEditsAt out.mem outEdits edits editWords ∧
      (∀ j < editWords, out.mem (outEdits + j) < 2 ^ w) ∧
      (∀ a, (a < outEdits ∨ outEdits + editWords ≤ a) → out.mem a = mem a) := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hUlenW : U.length < 2 ^ w := by omega
  have hcntMem : mem uIntBuf = U.length := by
    simpa [IPM.Machine.batchWords] using hbatch 0 (by simp [IPM.Machine.batchWords])
  have hbuf1W : uIntBuf + 1 < 2 ^ w := by
    have : 1 ≤ (IPM.Machine.batchWords U).length := by simp [IPM.Machine.batchWords]
    omega
  have hout1W : outEdits + 1 < 2 ^ w := by omega
  -- Prefix: load count, initialize rPtr, wPtr, editCnt
  let s0 := startState [uIntBuf, outEdits] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 2 U.length }
  let s2 : State := { s1 with regs := Function.update s1.regs 3 (uIntBuf + 1) }
  let s3 : State := { s2 with regs := Function.update s2.regs 4 (outEdits + 1) }
  let s4 : State := { s3 with regs := Function.update s3.regs 5 0 }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U.length, by simp [Expr.eval, s0, startState, hcntMem], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨uIntBuf + 1, by simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, hbuf1W], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.bin .add (.reg 1) (.const 1))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨outEdits + 1, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, hw1, hout1W], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 5 (.const 0)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Helper: read offset for prefix `U.take k`
  let rOff (k : ℕ) : ℕ := ((U.take k).flatMap IPM.Machine.updateWords).length
  let wOff (k : ℕ) : ℕ := batchOrdPayloadWords (U.take k)
  let eCnt (k : ℕ) : ℕ := (batchToOrdEdits (U.take k)).length
  have hrOff_le (k : ℕ) : 1 + rOff k ≤ (IPM.Machine.batchWords U).length := by
    have hfl : U.flatMap IPM.Machine.updateWords =
        (U.take k).flatMap IPM.Machine.updateWords ++ (U.drop k).flatMap IPM.Machine.updateWords := by
      conv_lhs => rw [← List.take_append_drop k U]
      rw [List.flatMap_append]
    simp only [IPM.Machine.batchWords, List.length_cons, hfl, List.length_append, rOff]
    omega
  have hbatchAt_elem (k : ℕ) (hk : k < U.length) (j : ℕ)
      (hj : j < (IPM.Machine.updateWords U[k]).length) :
      mem (uIntBuf + 1 + rOff k + j) = (IPM.Machine.updateWords U[k])[j] := by
    have hsplit : U = U.take k ++ U[k] :: U.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hfl : U.flatMap IPM.Machine.updateWords =
        (U.take k).flatMap IPM.Machine.updateWords ++
          (IPM.Machine.updateWords U[k] ++ (U.drop (k + 1)).flatMap IPM.Machine.updateWords) := by
      conv_lhs => rw [hsplit]
      rw [List.flatMap_append, List.flatMap_cons]
    have hidx : 1 + rOff k + j < (IPM.Machine.batchWords U).length := by
      simp only [IPM.Machine.batchWords, List.length_cons, hfl, List.length_append, rOff]
      omega
    have hread := hbatch (1 + rOff k + j) hidx
    rw [show uIntBuf + 1 + rOff k + j = uIntBuf + (1 + rOff k + j) by omega, hread]
    clear hread hbatch
    have hbw : IPM.Machine.batchWords U =
        U.length :: (((U.take k).flatMap IPM.Machine.updateWords) ++
          (IPM.Machine.updateWords U[k] ++ (U.drop (k + 1)).flatMap IPM.Machine.updateWords)) := by
      rw [IPM.Machine.batchWords, hfl]
    have hget : (IPM.Machine.batchWords U)[1 + rOff k + j] =
        (IPM.Machine.updateWords U[k])[j] := by
      simp only [hbw, show 1 + rOff k + j = (rOff k + j) + 1 by omega, List.getElem_cons_succ]
      rw [List.getElem_append_right (by dsimp [rOff]; omega)]
      simp only [show rOff k + j - ((U.take k).flatMap IPM.Machine.updateWords).length = j by
        dsimp [rOff]; omega]
      rw [List.getElem_append_left hj]
    exact hget
  -- Loop invariant at iteration `k ≤ U.length`
  let Inv (k : ℕ) (st : State) : Prop :=
    k ≤ U.length ∧
    st.regs 0 = uIntBuf ∧ st.regs 1 = outEdits ∧ st.regs 2 = U.length ∧
    st.regs 3 = uIntBuf + 1 + rOff k ∧
    st.regs 4 = outEdits + 1 + wOff k ∧
    st.regs 5 = eCnt k ∧
    st.regs 6 = k ∧
    st.pos = pos ∧
    (decodeOrdEdits st.mem (eCnt k) (outEdits + 1)).1 = batchToOrdEdits (U.take k) ∧
    (decodeOrdEdits st.mem (eCnt k) (outEdits + 1)).2.sum = wOff k ∧
    (∀ j < wOff k, st.mem (outEdits + 1 + j) < 2 ^ w) ∧
    (∀ a, (a < outEdits + 1 ∨ outEdits + 1 + wOff k ≤ a) → st.mem a = mem a)
  have hstep : ∀ k, 0 ≤ k → k < U.length →
      Triple w p (Inv k)
        (.assign 7 (.load (.reg 3)) ;;
         .cond (.bin .eq (.reg 7) (.const 0))
           (.assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
            .assign 9 (.load (.bin .add (.reg 3) (.const 2))) ;;
            .assign 10 (.load (.bin .add (.reg 3) (.const 3))) ;;
            .assign 11 (.bin .mul (.const 2) (.reg 8)) ;;
            .store (.reg 4) (.const 3) ;;
            .store (.bin .add (.reg 4) (.const 1)) (.reg 9) ;;
            .store (.bin .add (.reg 4) (.const 2)) (.reg 11) ;;
            .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
            .store (.bin .add (.reg 4) (.const 4)) (.const 3) ;;
            .store (.bin .add (.reg 4) (.const 5)) (.reg 10) ;;
            .store (.bin .add (.reg 4) (.const 6)) (.bin .add (.reg 11) (.const 1)) ;;
            .store (.bin .add (.reg 4) (.const 7)) (.const 0) ;;
            .assign 3 (.bin .add (.reg 3) (.const 4)) ;;
            .assign 4 (.bin .add (.reg 4) (.const 8)) ;;
            .assign 5 (.bin .add (.reg 5) (.const 2)))
           (.assign 8 (.load (.bin .add (.reg 3) (.const 1))) ;;
            .store (.reg 4) (.const 0) ;;
            .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
            .assign 3 (.bin .add (.reg 3) (.const 2)) ;;
            .assign 4 (.bin .add (.reg 4) (.const 2)) ;;
            .assign 5 (.bin .add (.reg 5) (.const 1))))
        (normalPost fun st' =>
          Inv (k + 1) { st' with regs := Function.update st'.regs 6 (k + 1) } ∧ st'.regs 6 = k)
        (fun _ => 110) := by
    intro k _ hk st bits hInv
    obtain ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hpos, hdec1, hdec2, hvalW, hfr⟩ := hInv
    have huMem : U[k] ∈ U := List.getElem_mem hk
    have huEdge := hedge U[k] huMem
    have hwOffLe : wOff k ≤ 8 * k := by
      have := batchOrdPayloadWords_le (U.take k); simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this; exact this
    have heCntLe : eCnt k ≤ 2 * k := by
      have := batchToOrdEdits_length_le (U.take k); simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this; exact this
    have hrOffSucc : rOff (k + 1) = rOff k + (IPM.Machine.updateWords U[k]).length := by
      dsimp only [rOff]; rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]; simp
    have hwOffSucc : wOff (k + 1) = wOff k + edgeUpdateOrdWords U[k] := by
      dsimp only [wOff, batchOrdPayloadWords]
      rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append]; simp
    have heCntSucc : eCnt (k + 1) = eCnt k + (edgeUpdateToOrdEdits U[k]).length := by
      dsimp only [eCnt, batchToOrdEdits]; rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]; simp
    have htakeSucc : batchToOrdEdits (U.take (k + 1)) =
        batchToOrdEdits (U.take k) ++ edgeUpdateToOrdEdits U[k] := by
      dsimp only [batchToOrdEdits]; rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]; simp
    have hReadIn (j : ℕ) (hj : j < (IPM.Machine.updateWords U[k]).length) :
        st.mem (uIntBuf + 1 + rOff k + j) = (IPM.Machine.updateWords U[k])[j] ∧
        (IPM.Machine.updateWords U[k])[j] < 2 ^ w := by
      have hidx : 1 + rOff k + j < (IPM.Machine.batchWords U).length := by
        have hle := hrOff_le (k + 1); rw [hrOffSucc] at hle; omega
      have hltOut : uIntBuf + 1 + rOff k + j < outEdits + 1 := by omega
      have h1 : st.mem (uIntBuf + 1 + rOff k + j) = mem (uIntBuf + 1 + rOff k + j) :=
        hfr _ (Or.inl hltOut)
      have h2 := hbatchAt_elem k hk j hj
      have h3 := hwordsIn (1 + rOff k + j) hidx
      rw [show uIntBuf + (1 + rOff k + j) = uIntBuf + 1 + rOff k + j by omega] at h3
      exact ⟨h1.trans h2, h2 ▸ h3⟩
    cases hu : U[k] with
    | split _ _ _ _ => rw [hu] at huEdge; exact huEdge.elim
    | insert e x y =>
      have h0 := hReadIn 0 (by simp [hu, IPM.Machine.updateWords])
      have h1 := hReadIn 1 (by simp [hu, IPM.Machine.updateWords])
      have h2 := hReadIn 2 (by simp [hu, IPM.Machine.updateWords])
      have h3 := hReadIn 3 (by simp [hu, IPM.Machine.updateWords])
      simp only [hu, IPM.Machine.updateWords, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
      have hkeyW : 2 * e + 1 < 2 ^ w := by simpa [hu] using hEdgeKey U[k] huMem
      have h2eW : 2 * e < 2 ^ w := by omega
      let w0 := outEdits + 1 + wOff k
      let r0 := uIntBuf + 1 + rOff k
      have hr3_r0 : st.regs 3 = r0 := hr3
      have hr4_w0 : st.regs 4 = w0 := hr4
      have hr0_1 : r0 + 1 < 2 ^ w := by have := hrOff_le (k + 1); rw [hrOffSucc, hu] at this; simp [IPM.Machine.updateWords] at this; omega
      have hr0_2 : r0 + 2 < 2 ^ w := by have := hrOff_le (k + 1); rw [hrOffSucc, hu] at this; simp [IPM.Machine.updateWords] at this; omega
      have hr0_3 : r0 + 3 < 2 ^ w := by have := hrOff_le (k + 1); rw [hrOffSucc, hu] at this; simp [IPM.Machine.updateWords] at this; omega
      have hr0_4 : r0 + 4 < 2 ^ w := by have := hrOff_le (k + 1); rw [hrOffSucc, hu] at this; simp [IPM.Machine.updateWords] at this; omega
      -- Step through the 17 statements of the `insert` branch
      let st1 : State := { st with regs := Function.update st.regs 7 0 }
      let st2 : State := { st1 with regs := Function.update st1.regs 8 e }
      let st3 : State := { st2 with regs := Function.update st2.regs 9 x }
      let st4 : State := { st3 with regs := Function.update st3.regs 10 y }
      let st5 : State := { st4 with regs := Function.update st4.regs 11 (2 * e) }
      let m1 := Function.update st.mem w0 3
      let m2 := Function.update m1 (w0 + 1) x
      let m3 := Function.update m2 (w0 + 2) (2 * e)
      let m4 := Function.update m3 (w0 + 3) 0
      let m5 := Function.update m4 (w0 + 4) 3
      let m6 := Function.update m5 (w0 + 5) y
      let m7 := Function.update m6 (w0 + 6) (2 * e + 1)
      let m8 := Function.update m7 (w0 + 7) 0
      let st6 : State := { st5 with mem := m1 }
      let st7 : State := { st6 with mem := m2 }
      let st8 : State := { st7 with mem := m3 }
      let st9 : State := { st8 with mem := m4 }
      let st10 : State := { st9 with mem := m5 }
      let st11 : State := { st10 with mem := m6 }
      let st12 : State := { st11 with mem := m7 }
      let st13 : State := { st12 with mem := m8 }
      let st14 : State := { st13 with regs := Function.update st13.regs 3 (r0 + 4) }
      let st15 : State := { st14 with regs := Function.update st14.regs 4 (w0 + 8) }
      let st16 : State := { st15 with regs := Function.update st15.regs 5 (eCnt k + 2) }
      have p0 : Runs w p bits (.assign 7 (.load (.reg 3))) st .normal st1 3 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hr3_r0, show st.mem r0 = 0 from h0.1], rfl, rfl, rfl⟩
      have hcond : (Expr.bin .eq (.reg 7) (.const 0)).eval w st1 = some 1 := by
        simp [Expr.eval, BinOp.eval, st1, hw1, show 0 < 2 ^ w by omega]
      have p1 : Runs w p bits (.assign 8 (.load (.bin .add (.reg 3) (.const 1)))) st1 .normal st2 5 :=
        runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, st1, hr3_r0, hw1, hr0_1, show st.mem (r0 + 1) = e from h1.1], rfl, rfl, rfl⟩
      have p2 : Runs w p bits (.assign 9 (.load (.bin .add (.reg 3) (.const 2)))) st2 .normal st3 5 :=
        runs_assign_iff.mpr ⟨x, by simp [Expr.eval, BinOp.eval, st2, st1, hr3_r0, hw2, hr0_2, show st.mem (r0 + 2) = x from h2.1], rfl, rfl, rfl⟩
      have p3 : Runs w p bits (.assign 10 (.load (.bin .add (.reg 3) (.const 3)))) st3 .normal st4 5 :=
        runs_assign_iff.mpr ⟨y, by simp [Expr.eval, BinOp.eval, st3, st2, st1, hr3_r0, hw3, hr0_3, show st.mem (r0 + 3) = y from h3.1], rfl, rfl, rfl⟩
      have p4 : Runs w p bits (.assign 11 (.bin .mul (.const 2) (.reg 8))) st4 .normal st5 4 :=
        runs_assign_iff.mpr ⟨2 * e, by simp [Expr.eval, BinOp.eval, st4, st3, st2, hw2, h2eW], rfl, rfl, rfl⟩
      have p5 : Runs w p bits (.store (.reg 4) (.const 3)) st5 .normal st6 3 :=
        runs_store_iff.mpr ⟨w0, 3, by simp [Expr.eval, st5, st4, st3, st2, st1, hr4_w0],
          by simp [Expr.eval, hw3], rfl, rfl, rfl⟩
      have p6 : Runs w p bits (.store (.bin .add (.reg 4) (.const 1)) (.reg 9)) st6 .normal st7 5 :=
        runs_store_iff.mpr ⟨w0 + 1, x, by simp [Expr.eval, BinOp.eval, st6, st5, st4, st3, st2, st1, hr4_w0, hw1, show w0 + 1 < 2 ^ w by omega],
          by simp [Expr.eval, st6, st5, st4, st3], rfl, rfl, rfl⟩
      have p7 : Runs w p bits (.store (.bin .add (.reg 4) (.const 2)) (.reg 11)) st7 .normal st8 5 :=
        runs_store_iff.mpr ⟨w0 + 2, 2 * e, by simp [Expr.eval, BinOp.eval, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw2, show w0 + 2 < 2 ^ w by omega],
          by simp [Expr.eval, st7, st6, st5], rfl, rfl, rfl⟩
      have p8 : Runs w p bits (.store (.bin .add (.reg 4) (.const 3)) (.const 0)) st8 .normal st9 5 :=
        runs_store_iff.mpr ⟨w0 + 3, 0, by simp [Expr.eval, BinOp.eval, st8, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw3, show w0 + 3 < 2 ^ w by omega],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p9 : Runs w p bits (.store (.bin .add (.reg 4) (.const 4)) (.const 3)) st9 .normal st10 5 :=
        runs_store_iff.mpr ⟨w0 + 4, 3, by simp [Expr.eval, BinOp.eval, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw4, show w0 + 4 < 2 ^ w by omega],
          by simp [Expr.eval, hw3], rfl, rfl, rfl⟩
      have p10 : Runs w p bits (.store (.bin .add (.reg 4) (.const 5)) (.reg 10)) st10 .normal st11 5 :=
        runs_store_iff.mpr ⟨w0 + 5, y, by simp [Expr.eval, BinOp.eval, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw5, show w0 + 5 < 2 ^ w by omega],
          by simp [Expr.eval, st10, st9, st8, st7, st6, st5, st4], rfl, rfl, rfl⟩
      have p11 : Runs w p bits (.store (.bin .add (.reg 4) (.const 6)) (.bin .add (.reg 11) (.const 1))) st11 .normal st12 7 :=
        runs_store_iff.mpr ⟨w0 + 6, 2 * e + 1, by simp [Expr.eval, BinOp.eval, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw6, show w0 + 6 < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, st11, st10, st9, st8, st7, st6, st5, hw1, hkeyW], rfl, rfl, rfl⟩
      have p12 : Runs w p bits (.store (.bin .add (.reg 4) (.const 7)) (.const 0)) st12 .normal st13 5 :=
        runs_store_iff.mpr ⟨w0 + 7, 0, by simp [Expr.eval, BinOp.eval, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw7, show w0 + 7 < 2 ^ w by omega],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p13 : Runs w p bits (.assign 3 (.bin .add (.reg 3) (.const 4))) st13 .normal st14 4 :=
        runs_assign_iff.mpr ⟨r0 + 4, by simp [Expr.eval, BinOp.eval, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr3_r0, hw4, hr0_4], rfl, rfl, rfl⟩
      have p14 : Runs w p bits (.assign 4 (.bin .add (.reg 4) (.const 8))) st14 .normal st15 4 :=
        runs_assign_iff.mpr ⟨w0 + 8, by simp [Expr.eval, BinOp.eval, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr4_w0, hw8, show w0 + 8 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p15 : Runs w p bits (.assign 5 (.bin .add (.reg 5) (.const 2))) st15 .normal st16 4 :=
        runs_assign_iff.mpr ⟨eCnt k + 2, by simp [Expr.eval, BinOp.eval, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr5, hw2, show eCnt k + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hm8_out (a : ℕ) (ha : a < w0 ∨ w0 + 8 ≤ a) : m8 a = st.mem a := by
        simp only [m8, m7, m6, m5, m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hm8_dec2 : decodeOrdEdits m8 2 w0 = ([.insertBefore x (e, true) none, .insertBefore y (e, false) none], [4, 4]) := by
        have h0' : m8 w0 = 3 := by
          dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        have h1' : m8 (w0 + 1) = x := by
          dsimp only [m8, m7, m6, m5, m4, m3, m2]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        have h2' : m8 (w0 + 2) = 2 * e := by
          dsimp only [m8, m7, m6, m5, m4, m3]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        have h3' : m8 (w0 + 3) = 0 := by
          dsimp only [m8, m7, m6, m5, m4]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        have h4' : m8 (w0 + 4) = 3 := by
          dsimp only [m8, m7, m6, m5]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        have h5' : m8 (w0 + 5) = y := by
          dsimp only [m8, m7, m6]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        have h6' : m8 (w0 + 6) = 2 * e + 1 := by
          dsimp only [m8, m7]; rw [Function.update_of_ne (by omega), Function.update_self]
        have h7' : m8 (w0 + 7) = 0 := by dsimp only [m8]; rw [Function.update_self]
        simp only [decodeOrdEdits, decodeOrdEdit, h0', h1', h2', h3', h4', h5', h6', h7',
          show (3 : ℕ) ≠ 0 by decide, show ¬ ((3 : ℕ) = 1 ∨ (3 : ℕ) = 2) by decide, ↓reduceIte,
          Nat.add_assoc, show 4 + 1 = 5 by decide, show 4 + 2 = 6 by decide, show 4 + 3 = 7 by decide,
          endOfKey_two_mul, endOfKey_two_mul_add_one]
      have hdecPref : decodeOrdEdits m8 (eCnt k) (outEdits + 1) = decodeOrdEdits st.mem (eCnt k) (outEdits + 1) :=
        decodeOrdEdits_congr st.mem m8 (eCnt k) (outEdits + 1) (fun a ha1 ha2 =>
          hm8_out a (Or.inl (by rw [hdec2] at ha2; omega)))
      have hdecAll := decodeOrdEdits_append m8 (eCnt k) 2 (outEdits + 1)
      dsimp only at hdecAll
      rw [hdecPref, hdec1, hdec2, show outEdits + 1 + wOff k = w0 from rfl, hm8_dec2] at hdecAll
      have hrunThen : Runs w p bits _ st1 .normal st16 85 :=
        runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, p1,
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, p2,
        runs_seq_iff.mpr (Or.inr ⟨st4, 5, _, p3,
        runs_seq_iff.mpr (Or.inr ⟨st5, 4, _, p4,
        runs_seq_iff.mpr (Or.inr ⟨st6, 3, _, p5,
        runs_seq_iff.mpr (Or.inr ⟨st7, 5, _, p6,
        runs_seq_iff.mpr (Or.inr ⟨st8, 5, _, p7,
        runs_seq_iff.mpr (Or.inr ⟨st9, 5, _, p8,
        runs_seq_iff.mpr (Or.inr ⟨st10, 5, _, p9,
        runs_seq_iff.mpr (Or.inr ⟨st11, 5, _, p10,
        runs_seq_iff.mpr (Or.inr ⟨st12, 7, _, p11,
        runs_seq_iff.mpr (Or.inr ⟨st13, 5, _, p12,
        runs_seq_iff.mpr (Or.inr ⟨st14, 4, _, p13,
        runs_seq_iff.mpr (Or.inr ⟨st15, 4, 4, p14, p15, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      refine ⟨.normal, st16, 93,
        runs_seq_iff.mpr (Or.inr ⟨st1, 3, 89, p0,
          runs_cond_iff.mpr ⟨1, 85, hcond, by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrunThen, by simp [Expr.size]⟩, rfl⟩),
        ⟨⟨hk, by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr0],
          by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr1],
          by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr2],
          by simp [st16, st15, st14, hrOffSucc, hu, IPM.Machine.updateWords, r0, Nat.add_assoc],
          by simp [st16, st15, hwOffSucc, hu, edgeUpdateOrdWords, w0, Nat.add_assoc],
          by simp [st16, heCntSucc, hu, edgeUpdateToOrdEdits],
          by simp, hpos, ?_, ?_, ?_, ?_⟩,
         by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hr6]⟩,
        by dsimp; omega⟩
      · change (decodeOrdEdits m8 (eCnt (k + 1)) (outEdits + 1)).1 = _
        rw [hu] at htakeSucc
        rw [heCntSucc, hu]
        simp only [edgeUpdateToOrdEdits, List.length_cons, List.length_nil] at hdecAll ⊢
        rw [hdecAll]; exact htakeSucc.symm
      · change (decodeOrdEdits m8 (eCnt (k + 1)) (outEdits + 1)).2.sum = wOff (k + 1)
        rw [heCntSucc, hwOffSucc, hu]
        simp only [edgeUpdateToOrdEdits, edgeUpdateOrdWords, List.length_cons, List.length_nil]
        rw [hdecAll]; simp [hdec2]
      · intro j hj
        change m8 (outEdits + 1 + j) < 2 ^ w
        rw [hwOffSucc, hu, edgeUpdateOrdWords] at hj
        by_cases hjlt : j < wOff k
        · rw [hm8_out _ (Or.inl (by omega))]; exact hvalW j hjlt
        · have hd : j - wOff k < 8 := by omega
          have heq : outEdits + 1 + j = w0 + (j - wOff k) := by omega
          rw [heq]
          interval_cases (j - wOff k)
          · dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), show w0 + 0 = w0 by omega, Function.update_self]
            exact hw3
          · dsimp only [m8, m7, m6, m5, m4, m3, m2]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
            exact h2.2
          · dsimp only [m8, m7, m6, m5, m4, m3]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
            exact h2eW
          · dsimp only [m8, m7, m6, m5, m4]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
            omega
          · dsimp only [m8, m7, m6, m5]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
            exact hw3
          · dsimp only [m8, m7, m6]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
            exact h3.2
          · dsimp only [m8, m7]
            rw [Function.update_of_ne (by omega), Function.update_self]
            exact hkeyW
          · dsimp only [m8]; rw [Function.update_self]; omega
      · intro a ha
        change m8 a = mem a
        rw [hwOffSucc, hu, edgeUpdateOrdWords] at ha
        rw [hm8_out a (by omega)]
        exact hfr a (by omega)
    | delete e =>
      have h0 := hReadIn 0 (by simp [hu, IPM.Machine.updateWords])
      have h1 := hReadIn 1 (by simp [hu, IPM.Machine.updateWords])
      simp only [hu, IPM.Machine.updateWords, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      let w0 := outEdits + 1 + wOff k
      let r0 := uIntBuf + 1 + rOff k
      have hr3_r0 : st.regs 3 = r0 := hr3
      have hr4_w0 : st.regs 4 = w0 := hr4
      have hr0_1 : r0 + 1 < 2 ^ w := by have := hrOff_le (k + 1); rw [hrOffSucc, hu] at this; simp [IPM.Machine.updateWords] at this; omega
      have hr0_2 : r0 + 2 < 2 ^ w := by have := hrOff_le (k + 1); rw [hrOffSucc, hu] at this; simp [IPM.Machine.updateWords] at this; omega
      let st1 : State := { st with regs := Function.update st.regs 7 1 }
      let st2 : State := { st1 with regs := Function.update st1.regs 8 e }
      let m1 := Function.update st.mem w0 0
      let m2 := Function.update m1 (w0 + 1) e
      let st3 : State := { st2 with mem := m1 }
      let st4 : State := { st3 with mem := m2 }
      let st5 : State := { st4 with regs := Function.update st4.regs 3 (r0 + 2) }
      let st6 : State := { st5 with regs := Function.update st5.regs 4 (w0 + 2) }
      let st7 : State := { st6 with regs := Function.update st6.regs 5 (eCnt k + 1) }
      have p0 : Runs w p bits (.assign 7 (.load (.reg 3))) st .normal st1 3 :=
        runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hr3_r0, show st.mem r0 = 1 from h0.1], rfl, rfl, rfl⟩
      have hcond : (Expr.bin .eq (.reg 7) (.const 0)).eval w st1 = some 0 := by
        simp [Expr.eval, BinOp.eval, st1, show 0 < 2 ^ w by omega]
      have p1 : Runs w p bits (.assign 8 (.load (.bin .add (.reg 3) (.const 1)))) st1 .normal st2 5 :=
        runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, st1, hr3_r0, hw1, hr0_1, show st.mem (r0 + 1) = e from h1.1], rfl, rfl, rfl⟩
      have p2 : Runs w p bits (.store (.reg 4) (.const 0)) st2 .normal st3 3 :=
        runs_store_iff.mpr ⟨w0, 0, by simp [Expr.eval, st2, st1, hr4_w0],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p3 : Runs w p bits (.store (.bin .add (.reg 4) (.const 1)) (.reg 8)) st3 .normal st4 5 :=
        runs_store_iff.mpr ⟨w0 + 1, e, by simp [Expr.eval, BinOp.eval, st3, st2, st1, hr4_w0, hw1, show w0 + 1 < 2 ^ w by omega],
          by simp [Expr.eval, st3, st2], rfl, rfl, rfl⟩
      have p4 : Runs w p bits (.assign 3 (.bin .add (.reg 3) (.const 2))) st4 .normal st5 4 :=
        runs_assign_iff.mpr ⟨r0 + 2, by simp [Expr.eval, BinOp.eval, st4, st3, st2, st1, hr3_r0, hw2, hr0_2], rfl, rfl, rfl⟩
      have p5 : Runs w p bits (.assign 4 (.bin .add (.reg 4) (.const 2))) st5 .normal st6 4 :=
        runs_assign_iff.mpr ⟨w0 + 2, by simp [Expr.eval, BinOp.eval, st5, st4, st3, st2, st1, hr4_w0, hw2, show w0 + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p6 : Runs w p bits (.assign 5 (.bin .add (.reg 5) (.const 1))) st6 .normal st7 4 :=
        runs_assign_iff.mpr ⟨eCnt k + 1, by simp [Expr.eval, BinOp.eval, st6, st5, st4, st3, st2, st1, hr5, hw1, show eCnt k + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hm2_out (a : ℕ) (ha : a < w0 ∨ w0 + 2 ≤ a) : m2 a = st.mem a := by
        simp only [m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hm2_dec1 : decodeOrdEdits m2 1 w0 = ([.dropEdge e], [2]) := by
        have h0' : m2 w0 = 0 := by simp [m2, m1]
        have h1' : m2 (w0 + 1) = e := by simp [m2]
        simp [decodeOrdEdits, decodeOrdEdit, h0', h1']
      have hdecPref : decodeOrdEdits m2 (eCnt k) (outEdits + 1) = decodeOrdEdits st.mem (eCnt k) (outEdits + 1) :=
        decodeOrdEdits_congr st.mem m2 (eCnt k) (outEdits + 1) (fun a ha1 ha2 =>
          hm2_out a (Or.inl (by rw [hdec2] at ha2; omega)))
      have hdecAll := decodeOrdEdits_append m2 (eCnt k) 1 (outEdits + 1)
      dsimp only at hdecAll
      rw [hdecPref, hdec1, hdec2, show outEdits + 1 + wOff k = w0 from rfl, hm2_dec1] at hdecAll
      have hrunElse : Runs w p bits _ st1 .normal st7 30 :=
        runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, p1,
        runs_seq_iff.mpr (Or.inr ⟨st3, 3, _, p2,
        runs_seq_iff.mpr (Or.inr ⟨st4, 5, _, p3,
        runs_seq_iff.mpr (Or.inr ⟨st5, 4, _, p4,
        runs_seq_iff.mpr (Or.inr ⟨st6, 4, 4, p5, p6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      refine ⟨.normal, st7, 38,
        runs_seq_iff.mpr (Or.inr ⟨st1, 3, 34, p0,
          runs_cond_iff.mpr ⟨0, 30, hcond, by simpa using hrunElse, by simp [Expr.size]⟩, rfl⟩),
        ⟨⟨hk, by simp [st7, st6, st5, st4, st3, st2, st1, hr0],
          by simp [st7, st6, st5, st4, st3, st2, st1, hr1],
          by simp [st7, st6, st5, st4, st3, st2, st1, hr2],
          by simp [st7, st6, st5, hrOffSucc, hu, IPM.Machine.updateWords, r0, Nat.add_assoc],
          by simp [st7, st6, hwOffSucc, hu, edgeUpdateOrdWords, w0, Nat.add_assoc],
          by simp [st7, heCntSucc, hu, edgeUpdateToOrdEdits],
          by simp, hpos, ?_, ?_, ?_, ?_⟩,
         by simp [st7, st6, st5, st4, st3, st2, st1, hr6]⟩,
        by dsimp; omega⟩
      · change (decodeOrdEdits m2 (eCnt (k + 1)) (outEdits + 1)).1 = _
        rw [hu] at htakeSucc
        rw [heCntSucc, hu]
        simp only [edgeUpdateToOrdEdits, List.length_cons, List.length_nil] at hdecAll ⊢
        rw [hdecAll]; exact htakeSucc.symm
      · change (decodeOrdEdits m2 (eCnt (k + 1)) (outEdits + 1)).2.sum = wOff (k + 1)
        rw [heCntSucc, hwOffSucc, hu]
        simp only [edgeUpdateToOrdEdits, edgeUpdateOrdWords, List.length_cons, List.length_nil]
        rw [hdecAll]; simp [hdec2]
      · intro j hj
        change m2 (outEdits + 1 + j) < 2 ^ w
        rw [hwOffSucc, hu, edgeUpdateOrdWords] at hj
        by_cases hjlt : j < wOff k
        · rw [hm2_out _ (Or.inl (by omega))]; exact hvalW j hjlt
        · have hd : j - wOff k < 2 := by omega
          have heq : outEdits + 1 + j = w0 + (j - wOff k) := by omega
          rw [heq]
          interval_cases (j - wOff k)
          · dsimp only [m2, m1]
            rw [Function.update_of_ne (by omega), show w0 + 0 = w0 by omega, Function.update_self]
            omega
          · dsimp only [m2]; rw [Function.update_self]; exact h1.2
      · intro a ha
        change m2 a = mem a
        rw [hwOffSucc, hu, edgeUpdateOrdWords] at ha
        rw [hm2_out a (by omega)]
        exact hfr a (by omega)
  have hloop := Triple.forRange_const (p := p) (P := fun st => st = s4) (Inv := Inv)
    (r := 6) (lo := .const 0) (hi := .reg 2) 110 0 U.length (Nat.zero_le _) hw1
    (fun _ => hUlenW)
    (by
      intro st hst; subst hst
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
        Nat.zero_le _, by simp [s4, s3, s2, s1, s0, startState],
        by simp [s4, s3, s2, s1, s0, startState], by simp [s4, s3, s2, s1],
        by simp [s4, s3, s2, rOff], by simp [s4, s3, wOff, batchOrdPayloadWords],
        by simp [s4, eCnt, batchToOrdEdits], by simp, rfl,
        by simp [eCnt, batchToOrdEdits, decodeOrdEdits],
        by simp [eCnt, wOff, batchToOrdEdits, batchOrdPayloadWords, decodeOrdEdits],
        fun j hj => by simp [wOff, batchOrdPayloadWords] at hj,
        fun a _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by simp [Expr.eval, h.2.2.2.1])
    hstep
  obtain ⟨o, s5, cLoop, rLoop, hInvEnd, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInvEnd
  | normal =>
    obtain ⟨_, _, hr1, _, _, hr4, hr5, _, hpos5, hdec1, hdec2, hvalW, hfr⟩ := hInvEnd
    have htakeAll : U.take U.length = U := List.take_length
    have hwOffAll : wOff U.length = batchOrdPayloadWords U := by simp [wOff, htakeAll]
    have heCntAll : eCnt U.length = (batchToOrdEdits U).length := by simp [eCnt, htakeAll]
    have heCntW : (batchToOrdEdits U).length < 2 ^ w := by
      have := batchToOrdEdits_length_le U; omega
    have hwAllLe : batchOrdPayloadWords U ≤ 8 * U.length := batchOrdPayloadWords_le U
    let s6 : State := { s5 with mem := Function.update s5.mem outEdits (batchToOrdEdits U).length }
    have rStore : Runs w p ω (.store (.reg 1) (.reg 5)) s5 .normal s6 3 :=
      runs_store_iff.mpr ⟨outEdits, (batchToOrdEdits U).length,
        by simp [Expr.eval, hr1], by simp [Expr.eval, hr5, heCntAll], rfl, rfl, rfl⟩
    have rRet : Runs w p ω (.ret (.bin .sub (.reg 4) (.reg 1))) s6
        (.returned (1 + batchOrdPayloadWords U)) s6 4 :=
      runs_ret_iff.mpr ⟨1 + batchOrdPayloadWords U, by
        simp only [Expr.eval, BinOp.eval, s6, hr4, hr1, hwOffAll,
          show outEdits + 1 + batchOrdPayloadWords U - outEdits = 1 + batchOrdPayloadWords U by omega,
          show 1 + batchOrdPayloadWords U < 2 ^ w by omega, ↓reduceIte], rfl, rfl, rfl⟩
    have hdecFinal : decodeOrdEdits s6.mem (batchToOrdEdits U).length (outEdits + 1) =
        decodeOrdEdits s5.mem (batchToOrdEdits U).length (outEdits + 1) :=
      decodeOrdEdits_congr s5.mem s6.mem (batchToOrdEdits U).length (outEdits + 1)
        (fun a ha1 _ => by
          change Function.update s5.mem outEdits _ a = s5.mem a
          exact Function.update_of_ne (show a ≠ outEdits by omega) _ _)
    have hOrdAt : OrdEditsAt s6.mem outEdits (batchToOrdEdits U) (1 + batchOrdPayloadWords U) := by
      refine ⟨?_, ?_, ?_⟩
      · unfold readOrdEdits
        have hs60 : s6.mem outEdits = (batchToOrdEdits U).length := by simp [s6]
        rw [hs60, hdecFinal, ← heCntAll, hdec1, htakeAll]
      · have hs60 : s6.mem outEdits = (batchToOrdEdits U).length := by simp [s6]
        rw [hs60, hdecFinal, ← heCntAll, hdec2, hwOffAll]
      · have h5 := batchOrdPayloadWords_le_5_enc U hedge; omega
    refine ⟨_, s6,
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 4, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 2, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, cLoop, _, rLoop,
      runs_seq_iff.mpr (Or.inr ⟨s6, 3, 4, rStore, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      ?_, by omega, hOrdAt, ?_, ?_⟩
    · simp only [Expr.size] at hcLoop; omega
    · intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simpa [s6] using heCntW
      · have hne : outEdits + j ≠ outEdits := by omega
        change Function.update s5.mem outEdits _ (outEdits + j) < 2 ^ w
        rw [Function.update_of_ne hne, show outEdits + j = outEdits + 1 + (j - 1) by omega]
        exact hvalW (j - 1) (by omega)
    · intro a ha
      change Function.update s5.mem outEdits _ a = mem a
      rw [Function.update_of_ne (by omega)]
      exact hfr a (by omega)

end MinCostFlow.MinRatio
