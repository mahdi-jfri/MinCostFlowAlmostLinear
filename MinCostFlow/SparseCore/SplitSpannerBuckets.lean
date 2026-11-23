module

public import MinCostFlow.SparseCore.CompLSFBridge
public import MinCostFlow.DynSpanner.Complexity

import Mathlib.Tactic.Linarith

/-!
# Empty-graph fallback, active buckets, bucket filtering, and endpoint projection

Provides the low-level building blocks for `SplitSpanner.lean`:
* `emptyGraph` and `emptyLSF` for empty-graph handling;
* `rawBucket`, `initBucketGraph`, and `initBucketGraph_spec` for per-bucket active subgraphs;
* `filterBucketStep`, `filterBucketBatch`, and `filterBucketBatch_spec` projecting quotient updates
  onto bucket graphs;
* `batchDeletes`, `compBatchParentRoot`, and `compBatchStepProj_spec` for tracking batch deletions
  and parent roots across component-LSF updates.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Empty-graph fallback and active-bucket partitioning -/

/-- Empty `MGraph` with no vertices or edges. -/
def emptyGraph : MGraph where
  V := ∅
  E := ∅
  tail := fun _ => 0
  head := fun _ => 0

/-- Empty LSF `(∅, (∅, ∅), fun _ => 1)` used when `G₀.V = ∅`. -/
def emptyLSF : LSF :=
  ⟨emptyGraph, ⟨emptyGraph, ∅⟩, fun _ => 1⟩

lemma emptyLSF_holds {G : MGraph} (hV : ¬ G.V.Nonempty) (hG : G.IsValid)
    (ℓ : ℕ → ℝ) (σ : ℝ) :
    emptyLSF.Holds G ℓ σ := by
  have hGE : G.E = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    exact hV ⟨G.tail e, (hG e he).1⟩
  have hGV : G.V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
  refine ⟨⟨fun _ h => by simp [emptyLSF, emptyGraph] at h, fun P hP => by
    rcases hP with ⟨hne, _, u, hW⟩
    cases hW with
    | nil => exact hne rfl
    | cons he _ _ => simp [emptyLSF, emptyGraph] at he⟩, ?_, ?_, fun e he => by simp [hGE] at he⟩
  · refine ⟨⟨fun _ h => by simp [emptyLSF, emptyGraph] at h, fun P hP => by
      rcases hP with ⟨hne, _, u, hW⟩
      cases hW with
      | nil => exact hne rfl
      | cons he _ _ => simp [emptyLSF, emptyGraph] at he⟩, by simp [emptyLSF, emptyGraph, hGV],
      by simp [emptyLSF, emptyGraph], fun v hv => by simp [hGV] at hv,
      ⟨by simp [emptyLSF, emptyGraph, hGV], by simp [emptyLSF, emptyGraph, hGE],
        fun _ h => by simp [emptyLSF, emptyGraph] at h⟩⟩
  · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ h => by simp [emptyLSF, emptyGraph] at h⟩

/-- Raw bucket subgraph of `\tilde{C}` restricted to edges with initial bucket `b`. -/
noncomputable def rawBucket (C : MGraph) (origBucket : ℕ → ℤ) (b : ℤ) : MGraph where
  V := C.V
  E := C.E.filter fun e => origBucket e = b
  tail := C.tail
  head := C.head

/-- Initial host graph passed to `DynSpanner.init` for bucket `b`: `activeSubgraph` trims
isolated quotient vertices so `(H₀ b).n ≤ min (2 * (H₀ b).m) tildeC0.V.card`. -/
noncomputable def initBucketGraph (S₀ : LSFState) (ℓ₀ : ℕ → ℝ) (b : ℤ) : MGraph :=
  let ts₀ := initTildeState S₀
  let origB := fun e => bucketOf (coreLen S₀.lsf ℓ₀ e)
  activeSubgraph (rawBucket ts₀.C origB b)

lemma initBucketGraph_spec {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh K_σ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (b : ℤ) :
    let ts₀ := initTildeState S₀
    let origB := fun e => bucketOf (coreLen S₀.lsf ℓ₀ e)
    let Hb₀ := initBucketGraph S₀ ℓ₀ b
    Hb₀.IsValid ∧
    ts₀.C.IsSubgraph Hb₀ ∧
    Hb₀.E = ts₀.C.E.filter (fun e => origB e = b) ∧
    (∀ e ∈ Hb₀.E, origB e = b) ∧
    Hb₀.V.card ≤ 2 * Hb₀.E.card ∧
    Hb₀.V.card ≤ ts₀.C.V.card ∧
    Hb₀.E.card ≤ ts₀.C.E.card ∧
    Hb₀.E.card ≤ S₀.G.m ∧
    Hb₀.maxDeg ≤ ts₀.C.maxDeg := by
  intro ts₀ origB Hb₀
  have hT₀ := initTildeState_inv hI₀ hCov₀
  have hRaw_val : (rawBucket ts₀.C origB b).IsValid := fun e he => by
    rw [rawBucket, Finset.mem_filter] at he
    exact hT₀.hC_val e he.1
  have hAct_sub := activeSubgraph_isSubgraph (rawBucket ts₀.C origB b)
  have hAct_val : Hb₀.IsValid := activeSubgraph_isValid hRaw_val
  have hC_sub_H : ts₀.C.IsSubgraph Hb₀ := by
    refine ⟨?_, ?_, fun e he => hAct_sub.2.2 e he⟩
    · exact Finset.Subset.trans hAct_sub.1 Finset.Subset.rfl
    · exact Finset.Subset.trans hAct_sub.2.1 (Finset.filter_subset _ _)
  have hE_eq : Hb₀.E = ts₀.C.E.filter (fun e => origB e = b) := rfl
  have hV_two : Hb₀.V.card ≤ 2 * Hb₀.E.card := by
    have hSub_V : Hb₀.V ⊆ Hb₀.E.biUnion fun e => {Hb₀.tail e, Hb₀.head e} := by
      intro v hv
      dsimp only [Hb₀, initBucketGraph, activeSubgraph] at hv
      rw [Finset.mem_filter] at hv
      have hpos : 0 < (rawBucket ts₀.C origB b).deg v := by
        dsimp only [ts₀, origB]; exact hv.2
      unfold MGraph.deg at hpos
      rw [Finset.mem_biUnion]
      by_cases h1 : ((rawBucket ts₀.C origB b).E.filter fun e =>
          (rawBucket ts₀.C origB b).tail e = v).Nonempty
      · obtain ⟨e, he⟩ := h1
        rw [Finset.mem_filter] at he
        refine ⟨e, he.1, ?_⟩
        rw [← he.2]
        exact Finset.mem_insert_self _ _
      · rw [Finset.not_nonempty_iff_eq_empty] at h1
        rw [h1, Finset.card_empty, zero_add, Finset.card_pos] at hpos
        obtain ⟨e, he⟩ := hpos
        rw [Finset.mem_filter] at he
        refine ⟨e, he.1, ?_⟩
        rw [← he.2]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    calc Hb₀.V.card
        ≤ (Hb₀.E.biUnion fun e => {Hb₀.tail e, Hb₀.head e}).card := Finset.card_le_card hSub_V
      _ ≤ ∑ _e ∈ Hb₀.E, 2 := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun e _ => ?_)
          exact le_trans (Finset.card_insert_le _ _) (by simp)
      _ = 2 * Hb₀.E.card := by simp [mul_comm]
  have hdeg_le : Hb₀.maxDeg ≤ ts₀.C.maxDeg := by
    unfold MGraph.maxDeg
    rw [Finset.sup_le_iff]
    intro v hv
    have hvC : v ∈ ts₀.C.V := hC_sub_H.1 hv
    have hdeg_v : Hb₀.deg v ≤ ts₀.C.deg v := by
      unfold MGraph.deg
      refine add_le_add (Finset.card_le_card fun e he => ?_) (Finset.card_le_card fun e he => ?_)
      · rw [Finset.mem_filter] at he ⊢
        exact ⟨hC_sub_H.2.1 he.1, (hC_sub_H.2.2 e he.1).1 ▸ he.2⟩
      · rw [Finset.mem_filter] at he ⊢
        exact ⟨hC_sub_H.2.1 he.1, (hC_sub_H.2.2 e he.1).2 ▸ he.2⟩
    exact le_trans hdeg_v (Finset.le_sup (f := ts₀.C.deg) hvC)
  have hE_le_C : Hb₀.E.card ≤ ts₀.C.E.card := Finset.card_le_card hC_sub_H.2.1
  have hE_le_G : Hb₀.E.card ≤ S₀.G.m := le_trans hE_le_C (Finset.card_le_card
    (Finset.Subset.trans hT₀.hCE_sub Finset.sdiff_subset))
  exact ⟨hAct_val, hC_sub_H, hE_eq, fun e he => (Finset.mem_filter.mp he).2,
    hV_two, Finset.card_le_card hC_sub_H.1, hE_le_C, hE_le_G, hdeg_le⟩

/-! ## 2. Filtering `\tilde{C}` updates per bucket for `DynSpanner` -/

/-- Filter one update `u_C` of `\tilde{C}` onto bucket graph `H`. -/
def filterBucketStep (H : MGraph) : Update → MGraph × List Update
  | .delete e => if e ∈ H.E then (H.applyUpdate (.delete e), [.delete e]) else (H, [])
  | .split par vid St Sh =>
    open Classical in
    if par ∈ H.V ∧ vid ∉ H.V then
      let u' := Update.split par vid (H.E ∩ St) (H.E ∩ Sh)
      (H.applyUpdate u', [u'])
    else (H, [])
  | .insert _ _ _ => (H, [])

/-- Filter a valid `delOrSplit` batch `U_C` of `\tilde{C}` onto bucket graph `H`. -/
def filterBucketBatch (H : MGraph) : List Update → MGraph × List Update
  | [] => (H, [])
  | u :: rest =>
    let r1 := filterBucketStep H u
    let r2 := filterBucketBatch r1.1 rest
    (r2.1, r1.2 ++ r2.2)

lemma filterBucketBatch_spec {C : MGraph} (hC : C.IsValid) {origBucket : ℕ → ℤ} {b : ℤ}
    {H : MGraph} (hH_val : H.IsValid) (hSub : C.IsSubgraph H)
    (hE_eq : H.E = C.E.filter fun e => origBucket e = b)
    {U_C : List Update} (hBV : C.BatchIsValid U_C) (hds : ∀ op ∈ U_C, isDelOrSplit op) :
    let res := filterBucketBatch H U_C
    let H' := res.1
    let U_b := res.2
    H.BatchIsValid U_b ∧
    H' = H.applyBatch U_b ∧
    H'.IsValid ∧
    (C.applyBatch U_C).IsSubgraph H' ∧
    H'.E = (C.applyBatch U_C).E.filter (fun e => origBucket e = b) ∧
    (∀ op ∈ U_b, isDelOrSplit op) ∧
    U_b.length ≤ U_C.length ∧
    batchSplitCount U_b ≤ batchSplitCount U_C := by
  induction U_C generalizing C H with
  | nil =>
    dsimp only [filterBucketBatch]
    refine ⟨trivial, rfl, hH_val, hSub, hE_eq, fun _ h => by simp at h, le_rfl, le_rfl⟩
  | cons u rest ih =>
    rw [MGraph.BatchIsValid] at hBV
    obtain ⟨hu, hB_rest⟩ := hBV
    have hu_ds : isDelOrSplit u := hds u List.mem_cons_self
    have hrest_ds : ∀ op ∈ rest, isDelOrSplit op := fun op hop =>
      hds op (List.mem_cons_of_mem _ hop)
    have h1 : let r1 := filterBucketStep H u
        H.BatchIsValid r1.2 ∧
        r1.1 = H.applyBatch r1.2 ∧
        r1.1.IsValid ∧
        (C.applyUpdate u).IsSubgraph r1.1 ∧
        r1.1.E = (C.applyUpdate u).E.filter (fun e => origBucket e = b) ∧
        (∀ op ∈ r1.2, isDelOrSplit op) ∧
        r1.2.length ≤ 1 ∧
        batchSplitCount r1.2 ≤ (if isSplit u then 1 else 0) := by
      cases u with
      | insert _ _ _ => exact absurd hu_ds id
      | delete e₀ =>
        dsimp only [filterBucketStep]
        by_cases he : e₀ ∈ H.E
        · simp only [he, ↓reduceIte]
          have hu_H : H.UpdateIsValid (.delete e₀) := he
          refine ⟨⟨hu_H, trivial⟩, rfl, applyUpdate_isValid hH_val hu_H, ?_, ?_,
            fun _ h => by rw [List.mem_singleton] at h; subst h; exact trivial,
            le_rfl, by simp [batchSplitCount, isSplit]⟩
          · refine ⟨hSub.1, fun f hf => ?_, fun f hf => ?_⟩
            · rw [MGraph.applyUpdate, Finset.mem_erase] at hf ⊢
              exact ⟨hf.1, hSub.2.1 hf.2⟩
            · rw [MGraph.applyUpdate, Finset.mem_erase] at hf
              exact hSub.2.2 f hf.2
          · ext f
            simp only [MGraph.applyUpdate, Finset.mem_erase, Finset.mem_filter, hE_eq]
            tauto
        · simp only [he, ↓reduceIte]
          refine ⟨trivial, rfl, hH_val, ?_, ?_, fun _ h => by simp at h, by simp,
            by simp [batchSplitCount, isSplit]⟩
          · refine ⟨hSub.1, fun f hf => ?_, fun f hf => ?_⟩
            · have hne : f ≠ e₀ := fun h => he (h ▸ hf)
              exact Finset.mem_erase.mpr ⟨hne, hSub.2.1 hf⟩
            · exact hSub.2.2 f hf
          · ext f
            simp only [MGraph.applyUpdate, Finset.mem_filter, Finset.mem_erase, hE_eq]
            constructor
            · rintro ⟨hf, hb⟩
              exact ⟨⟨fun h => he (h ▸ hE_eq ▸ Finset.mem_filter.mpr ⟨hf, hb⟩), hf⟩, hb⟩
            · rintro ⟨⟨_, hf⟩, hb⟩
              exact ⟨hf, hb⟩
      | split par vid St Sh =>
        dsimp only [filterBucketStep]
        by_cases hpv : par ∈ H.V ∧ vid ∉ H.V
        · rw [ite_eq_left_iff.mpr (fun h => absurd hpv h)]
          have hinc : ∀ e ∈ (H.E ∩ St) ∪ (H.E ∩ Sh), H.tail e = par ∨ H.head e = par := by
            intro e he
            rcases Finset.mem_union.mp he with heT | heH
            · rw [Finset.mem_inter] at heT
              have hEnd := hSub.2.2 e heT.1
              rcases hu.2.2.2 e (Finset.mem_union_left _ heT.2) with h | h
              · left; rw [hEnd.1, h]
              · right; rw [hEnd.2, h]
            · rw [Finset.mem_inter] at heH
              have hEnd := hSub.2.2 e heH.1
              rcases hu.2.2.2 e (Finset.mem_union_right _ heH.2) with h | h
              · left; rw [hEnd.1, h]
              · right; rw [hEnd.2, h]
          have hu_H : H.UpdateIsValid (.split par vid (H.E ∩ St) (H.E ∩ Sh)) :=
            ⟨hpv.1, hpv.2, Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left, hinc⟩
          refine ⟨⟨hu_H, trivial⟩, rfl, applyUpdate_isValid hH_val hu_H, ?_, ?_,
            fun _ h => by rw [List.mem_singleton] at h; subst h; exact trivial,
            le_rfl, by simp [batchSplitCount, isSplit]⟩
          · refine ⟨Finset.insert_subset_insert vid hSub.1, hSub.2.1, fun e he => ?_⟩
            have heH : e ∈ H.E := he
            have hEnd := hSub.2.2 e heH
            simp only [MGraph.applyUpdate]
            constructor
            · by_cases heSt : e ∈ St
              · simp [heH, heSt, hEnd.1]
              · simp [heH, heSt, hEnd.1]
            · by_cases heSh : e ∈ Sh
              · simp [heH, heSh, hEnd.2]
              · simp [heH, heSh, hEnd.2]
          · simp only [MGraph.applyUpdate]; exact hE_eq
        · simp only [hpv, ↓reduceIte]
          have hnot_par : par ∉ H.V := fun hp => hpv ⟨hp, fun hv => hu.2.1 (hSub.1 hv)⟩
          refine ⟨trivial, rfl, hH_val, ?_, ?_, fun _ h => by simp at h, by simp,
            by simp [batchSplitCount, isSplit]⟩
          · refine ⟨Finset.Subset.trans hSub.1 (Finset.subset_insert _ _), hSub.2.1, fun e he => ?_⟩
            have hEnd := hSub.2.2 e he
            have hV_e := hH_val e he
            have ht_ne : C.tail e ≠ par := fun h => hnot_par (h ▸ hEnd.1 ▸ hV_e.1)
            have hh_ne : C.head e ≠ par := fun h => hnot_par (h ▸ hEnd.2 ▸ hV_e.2)
            simp only [MGraph.applyUpdate, ht_ne, hh_ne, and_false, ↓reduceIte]
            exact hEnd
          · exact hE_eq
    set r1 := filterBucketStep H u
    have hC1_val : (C.applyUpdate u).IsValid := applyUpdate_isValid hC hu
    have h2 := ih hC1_val h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2.1 hB_rest hrest_ds
    rcases h2 with ⟨h2_BV, h2_app, h2_val, h2_sub, h2_E, h2_ds, h2_len, h2_sc⟩
    refine ⟨?_, ?_, h2_val, h2_sub, h2_E, ?_, ?_, ?_⟩
    · dsimp only [filterBucketBatch]
      rw [batchIsValid_append]
      exact ⟨h1.1, h1.2.1 ▸ h2_BV⟩
    · dsimp only [filterBucketBatch]
      rw [applyBatch_append, ← h1.2.1]; exact h2_app
    · intro op hop
      dsimp only [filterBucketBatch] at hop
      rcases List.mem_append.mp hop with h | h
      · exact h1.2.2.2.2.2.1 op h
      · exact h2_ds op h
    · dsimp only [filterBucketBatch]
      rw [List.length_append, List.length_cons, Nat.add_comm rest.length 1]
      exact Nat.add_le_add h1.2.2.2.2.2.2.1 h2_len
    · dsimp only [filterBucketBatch]
      rw [batchSplitCount_append]
      have h1s : batchSplitCount r1.2 ≤ (if isSplit u then 1 else 0) := h1.2.2.2.2.2.2.2
      have hsc_cons : batchSplitCount (u :: rest) =
          (if isSplit u then 1 else 0) + batchSplitCount rest := by
        simp [batchSplitCount, List.countP_cons, Nat.add_comm]
      rw [hsc_cons]
      change batchSplitCount r1.2 + batchSplitCount (filterBucketBatch r1.1 rest).2 ≤ _
      exact Nat.add_le_add h1s h2_sc

/-! ## 3. Batch endpoint projection & construction of `U_S` -/

/-- Fold step collecting explicitly deleted edge IDs. -/
def addDel (S : Finset ℕ) : Update → Finset ℕ
  | .delete e => insert e S
  | _ => S

/-- Set of edge IDs explicitly deleted in update batch `U`. -/
def batchDeletes (U : List Update) : Finset ℕ :=
  U.foldl addDel ∅

lemma mem_batchDeletes_iff (U : List Update) (e : ℕ) :
    e ∈ batchDeletes U ↔ ∃ u ∈ U, u = .delete e := by
  suffices h : ∀ (acc : Finset ℕ),
      e ∈ U.foldl addDel acc ↔ e ∈ acc ∨ ∃ u ∈ U, u = .delete e from
    by simpa [batchDeletes] using h ∅
  induction U with
  | nil => simp
  | cons u rest ih =>
    intro acc
    rw [List.foldl_cons, ih]
    cases u with
    | delete e' =>
      simp only [addDel, Finset.mem_insert, List.mem_cons, exists_eq_or_imp, Update.delete.injEq]
      tauto
    | insert _ _ _ => simp [addDel, List.mem_cons]
    | split _ _ _ _ => simp [addDel, List.mem_cons]

lemma batchDeletes_card_le (U : List Update) : (batchDeletes U).card ≤ U.length := by
  suffices h : ∀ (acc : Finset ℕ),
      (U.foldl addDel acc).card ≤ acc.card + U.length from
    by simpa [batchDeletes] using h ∅
  induction U with
  | nil => simp
  | cons u rest ih =>
    intro acc
    rw [List.foldl_cons, List.length_cons]
    cases u with
    | delete e' =>
      have h1 := ih (addDel acc (.delete e'))
      have h2 : (addDel acc (.delete e')).card ≤ acc.card + 1 := by
        simpa [addDel] using Finset.card_insert_le e' acc
      omega
    | insert a b c =>
      have h1 : (rest.foldl addDel acc).card ≤ acc.card + rest.length := ih acc
      change (rest.foldl addDel acc).card ≤ acc.card + (rest.length + 1)
      omega
    | split _ _ _ _ =>
      have h1 : (rest.foldl addDel acc).card ≤ acc.card + rest.length := ih acc
      change (rest.foldl addDel acc).card ≤ acc.card + (rest.length + 1)
      omega

/-- Parent root in `cs_old.RF.R` for a new root `r' ∈ cs_new.RF.R \ cs_old.RF.R` across `U`. -/
noncomputable def compBatchParentRoot (cs_old : CompLSFState) (U : List Update) (r' : ℕ) : ℕ :=
  cs_old.RF.root (U.foldr stepProj r')

private lemma stepProj_old_V_graph {G : MGraph} {u : Update} (hu : G.UpdateIsValid u)
    {x : ℕ} (hx : x ∈ G.V) : stepProj u x = x := by
  cases u with
  | delete _ => rfl
  | insert _ _ _ => rfl
  | split v v' _ _ =>
    have hne : x ≠ v' := fun h => hu.2.1 (h ▸ hx)
    simp [stepProj, hne]

private lemma comp_forest_connected_stepProj {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    ∀ {x y : ℕ}, (compLSFStepSingle cs u).RF.F.Connected x y →
      cs.RF.F.Connected (stepProj u x) (stepProj u y) := by
  intro x y ⟨P, hP⟩
  set cs' := compLSFStepSingle cs u
  have hRF := compLSF_RF_isRSF hI
  have hRF' := compLSF_RF_isRSF (compLSFInv_step hI hu)
  have hFE_sub : cs'.RF.F.E ⊆ cs.RF.F.E :=
    (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).1
  induction P generalizing x with
  | nil => cases hP; exact connected_refl cs.RF.F _
  | cons s rest ih =>
    cases hP with
    | cons hsE hsSrc hrest =>
      have hsF : s.1 ∈ cs.RF.F.E := hFE_sub hsE
      have hend := stepProj_applyUpdate_eq hI.hG_val hu (hRF.2.2.2.2.2.1 hsF)
        (hRF'.2.2.2.2.2.1 hsE)
      have hsrc_p : cs.RF.F.src s = stepProj u x := by
        rw [← hsSrc]; unfold MGraph.src; dsimp only [cs', compLSFStepSingle, CompLSFState.RF]
        split_ifs <;> simp [hend.1, hend.2]
      have hdst_p : cs.RF.F.dst s = stepProj u (cs'.RF.F.dst s) := by
        unfold MGraph.dst; dsimp only [cs', compLSFStepSingle, CompLSFState.RF]
        split_ifs <;> simp [hend.1, hend.2]
      exact connected_trans
        ⟨[s], .cons hsF hsrc_p (by simpa [hdst_p] using MGraph.IsWalk.nil _)⟩ (ih hrest)

lemma compBatchStepProj_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U) :
    let cs_new := compLSFBatch cs_old U
    (∀ x ∈ cs_new.G.V, U.foldr stepProj x ∈ cs_old.G.V) ∧
    (∀ x ∈ cs_old.G.V, U.foldr stepProj x = x) ∧
    (∀ e ∈ cs_old.G.E, e ∉ batchDeletes U →
      e ∈ cs_new.G.E ∧
      cs_old.G.tail e = U.foldr stepProj (cs_new.G.tail e) ∧
      cs_old.G.head e = U.foldr stepProj (cs_new.G.head e)) ∧
    (∀ x y, cs_new.RF.F.Connected x y →
      cs_old.RF.F.Connected (U.foldr stepProj x) (U.foldr stepProj y)) := by
  induction U generalizing cs_old with
  | nil =>
    refine ⟨fun _ hx => hx, fun _ _ => rfl, fun _ he _ => ⟨he, rfl, rfl⟩, fun _ _ hc => hc⟩
  | cons u rest ih =>
    rw [MGraph.BatchIsValid] at hBU
    obtain ⟨hu, hB_rest⟩ := hBU
    have hI₁ := compLSFInv_step hI hu
    set cs₁ := compLSFStepSingle cs_old u
    have hcs₁_G : cs₁.G = cs_old.G.applyUpdate u := rfl
    have hih := ih hI₁ hB_rest
    rcases hih with ⟨hV_in, hV_old, hE_surv, hConn⟩
    have huV : ∀ x ∈ cs₁.G.V, stepProj u x ∈ cs_old.G.V := by
      intro x hx
      rw [hcs₁_G] at hx
      cases u with
      | delete _ => exact hx
      | insert _ _ _ => exact hx
      | split v v' _ _ =>
        dsimp only [MGraph.applyUpdate] at hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxS
        · simp [stepProj, hu.1]
        · rw [stepProj_old_V_graph hu hxS]; exact hxS
    refine ⟨fun x hx => huV _ (hV_in x hx), fun x hx => ?_, fun e he hn => ?_, fun x y hc => ?_⟩
    · have hx1 : x ∈ cs₁.G.V := by
        rw [hcs₁_G]; cases u with
        | delete _ => exact hx
        | insert _ _ _ => exact hx
        | split _ v' _ _ => exact Finset.mem_insert_of_mem hx
      rw [List.foldr_cons, hV_old x hx1, stepProj_old_V_graph hu hx]
    · have hn_u : u ≠ .delete e := fun h =>
        hn ((mem_batchDeletes_iff (u :: rest) e).mpr ⟨u, List.mem_cons_self, h⟩)
      have hn_rest : e ∉ batchDeletes rest := fun h => by
        obtain ⟨u', hu', heq⟩ := (mem_batchDeletes_iff rest e).mp h
        exact hn ((mem_batchDeletes_iff (u :: rest) e).mpr
          ⟨u', List.mem_cons_of_mem _ hu', heq⟩)
      have he1 : e ∈ cs₁.G.E := by
        rw [hcs₁_G]; cases u with
        | delete e₀ =>
          have hne : e ≠ e₀ := fun h => hn_u (by rw [h])
          exact Finset.mem_erase.mpr ⟨hne, he⟩
        | insert e₀ _ _ => exact Finset.mem_insert_of_mem he
        | split _ _ _ _ => exact he
      have hend1 : stepProj u ((cs_old.G.applyUpdate u).tail e) = cs_old.G.tail e ∧
          stepProj u ((cs_old.G.applyUpdate u).head e) = cs_old.G.head e :=
        stepProj_applyUpdate_eq hI.hG_val hu he (hcs₁_G ▸ he1)
      obtain ⟨he_new, ht_r, hh_r⟩ := hE_surv e he1 hn_rest
      refine ⟨he_new, ?_, ?_⟩
      · change cs_old.G.tail e =
          stepProj u (List.foldr stepProj ((compLSFBatch cs₁ rest).G.tail e) rest)
        rw [← ht_r, hcs₁_G, hend1.1]
      · change cs_old.G.head e =
          stepProj u (List.foldr stepProj ((compLSFBatch cs₁ rest).G.head e) rest)
        rw [← hh_r, hcs₁_G, hend1.2]
    · rw [List.foldr_cons, List.foldr_cons]
      exact comp_forest_connected_stepProj hI hu (hConn x y hc)


end

end MinCostFlow.SparseCore
