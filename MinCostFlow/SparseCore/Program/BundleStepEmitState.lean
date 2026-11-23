module

public import MinCostFlow.SparseCore.Program.BundleStepEmitDelRecs
public import MinCostFlow.SparseCore.Program.BundleStepEmitCand
public import MinCostFlow.SparseCore.Program.BundleStepScanAmort
public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs

/-!
# Full Phase 3 single-slot emission verification (`BundleStepEmitState`)

Defines the intermediate Phase 3 table predicate `BundleTableEmitState`, proves its transitions
`of_afterScan` (entering Phase 3) and `to_tableRepAt` (exiting Phase 3 when `remTouched = []`),
and verifies `bundleStepEmitSlotStmt` end-to-end (`bundleStepEmitSlot_runs`) together with the
exact `bundleRunsStep` equivalence corollary (`bundleStepEmitSlot_eq_bundleRunsStep`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Intermediate Phase 3 table state (`BundleTableEmitState`) -/

/-- Table state during Phase 3 emission: slots in `remTouched` still hold their post-scan
deletion lists (`slotDelHead`/`slotDelNext`), candidate lists (`BundleSlotRepCand`), and
`slotTouched = 1`; slots not in `remTouched` already have clean `BundleSlotRepAt` and zeroed
scratch arrays for their updated state `S_cur`. -/
def BundleTableEmitState (slotCap vCap eCap tbl : ℕ) (S₀ : BundleTableState slotCap)
    (D : Finset ℕ) (m : BundleTableMeta slotCap) (candSet : Fin slotCap → Finset ℕ)
    (S_cur : BundleTableState slotCap) (remTouched : List ℕ) (mem : ℕ → ℕ) : Prop :=
  let prevBase := btEndPrevBase tbl slotCap eCap
  let nextBase := btEndNextBase tbl slotCap eCap
  mem (tbl + btOffSlotCap) = slotCap ∧
  mem (tbl + btOffVCap) = vCap ∧
  mem (tbl + btOffECap) = eCap ∧
  mem (tbl + btOffSlotPtr) = btSlotPtrBase tbl ∧
  mem (tbl + btOffEdgeSlot) = btEdgeSlotBase tbl slotCap ∧
  mem (tbl + btOffEndBundle) = btEndBundleBase tbl slotCap eCap ∧
  mem (tbl + btOffEndPrev) = prevBase ∧
  mem (tbl + btOffEndNext) = nextBase ∧
  mem (tbl + btOffSlotTouched) = btSlotTouchedBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotDelHead) = btSlotDelHeadBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotDelNext) = btSlotDelNextBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotCandHead) = btSlotCandHeadBase tbl slotCap eCap ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
    S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges) ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
    S_cur j₁ = some B₁ → S_cur j₂ = some B₂ → Disjoint B₁.edges B₂.edges) ∧
  (∀ j : Fin slotCap,
    match S₀ j, S_cur j with
    | none, none => True
    | some B₀, some B_cur => B_cur.edges = B₀.edges \ D ∧
        (j.1 ∈ remTouched → B_cur = { B₀ with edges := B₀.edges \ D })
    | _, _ => False) ∧
  (∀ e < eCap,
    (∀ (j : Fin slotCap) (B : BundleState), S_cur j = some B → e ∈ B.edges →
      mem (btEdgeSlotBase tbl slotCap + e) = j.1 + 1) ∧
    ((∀ (j : Fin slotCap) (B : BundleState), S_cur j = some B → e ∉ B.edges) →
      mem (btEdgeSlotBase tbl slotCap + e) = 0)) ∧
  (∀ (j : Fin slotCap) (B : BundleState), S_cur j = some B →
    ∀ x ∈ edgeEnds B.edges,
      mem (btEndBundleBase tbl slotCap eCap + endKey x) = B.bundleOf x) ∧
  (∀ j : Fin slotCap,
    match S_cur j, m.slotBlocks j with
    | none, none => mem (btSlotPtrBase tbl + j.1) = 0 ∧
        mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0 ∧ j.1 ∉ remTouched
    | some B, some (p, bunCap) =>
        mem (btSlotPtrBase tbl + j.1) = p ∧
        (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p) ∧
        (if j.1 ∈ remTouched then
          BundleSlotRepCand eCap prevBase nextBase p bunCap B
            (btSlotCandHeadBase tbl slotCap eCap + j.1) (candSet j) mem
        else
          BundleSlotRepAt eCap prevBase nextBase p bunCap B mem ∧
          mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0)
    | _, _ => False) ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ p₁ c₁ p₂ c₂,
    m.slotBlocks j₁ = some (p₁, c₁) → m.slotBlocks j₂ = some (p₂, c₂) →
    p₁ + bundleSlotBlockSize c₁ ≤ p₂ ∨ p₂ + bundleSlotBlockSize c₂ ≤ p₁) ∧
  remTouched.Nodup ∧
  (∀ s ∈ remTouched, s < slotCap) ∧
  (∀ s < slotCap, mem (btSlotTouchedBase tbl slotCap eCap + s) = if s ∈ remTouched then 1 else 0) ∧
  (∀ j : Fin slotCap,
    match S₀ j with
    | none => mem (btSlotDelHeadBase tbl slotCap eCap + j.1) = 0
    | some B₀ =>
        if j.1 ∈ remTouched then
          ∃ dL : List ℕ,
            IsSinglyLinkedList mem (btSlotDelNextBase tbl slotCap eCap)
              (btSlotDelHeadBase tbl slotCap eCap + j.1) eCap dL ∧
            (∀ e, e ∈ dL ↔ e ∈ B₀.edges ∩ D)
        else
          mem (btSlotDelHeadBase tbl slotCap eCap + j.1) = 0) ∧
  (∀ e < eCap, (∀ j : Fin slotCap, ∀ B₀, j.1 ∈ remTouched → S₀ j = some B₀ → e ∉ B₀.edges ∩ D) →
    mem (btSlotDelNextBase tbl slotCap eCap + e) = 0)

end

public section

lemma BundleTableEmitState.of_afterScan {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {touched : List ℕ} {mem : ℕ → ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (h : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem) :
    BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet (tableDelEdges S₀ D) touched mem := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    hdisj, hedSlot, hendB, hslots, hdisjB, hndT, hltT, htouch, hdel, hdelN0⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hdisj₀, hdisj, ?_, hedSlot, hendB,
    ?_, hdisjB, hndT, hltT, htouch, ?_, ?_⟩
  · intro j; cases hSj : S₀ j <;> simp [tableDelEdges, hSj]
  · intro j
    have hs := hslots j; have hd := hdel j
    cases hS0 : S₀ j with
    | none =>
      have hTd : tableDelEdges S₀ D j = none := by simp [tableDelEdges, hS0]
      rw [hTd] at hs ⊢; rw [hS0] at hd
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hs; exact ⟨hs.1, hs.2.1, hd.2⟩
      | some pb => rw [hm] at hs; exact False.elim hs
    | some B₀ =>
      have hTd : tableDelEdges S₀ D j = some { B₀ with edges := B₀.edges \ D } := by
        simp [tableDelEdges, hS0]
      rw [hTd] at hs ⊢; rw [hS0] at hd
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hs; exact False.elim hs
      | some pb =>
        rcases pb with ⟨p, bunCap⟩; rw [hm] at hs
        refine ⟨hs.1, hs.2.2, ?_⟩
        split_ifs with hmem
        · exact hs.2.1
        · have hcand0 : candSet j = ∅ := by
            ext b; simp only [Finset.notMem_empty, iff_false]
            intro hb; exact hmem (hd.1.mpr (Or.inr ⟨b, hb⟩))
          rcases hs.2.1 with ⟨nB, hV, hnB, hE, hbo, hp0, hc0, hc1, hc2, hdll, hpar, htail,
            hseen, hinC, _, ⟨cL, hsll, hcL⟩, hcN0⟩
          have hcL_nil : cL = [] := by
            cases cL with
            | nil => rfl
            | cons x _ =>
              have := (hcL x).mp List.mem_cons_self; rw [hcand0] at this; exact False.elim (by simp at this)
          subst hcL_nil
          refine ⟨⟨nB, hV, hnB, hE, hbo, hp0, hc0, hc1, hc2, hdll, hpar, htail, fun b hb =>
            ⟨hseen b hb, by rw [hinC b hb, hcand0]; simp, hcN0 b hb (by rw [hcand0]; simp)⟩⟩, hsll⟩
  · intro j
    have hd := hdel j
    cases hS0 : S₀ j with
    | none => rw [hS0] at hd; exact hd.1
    | some B₀ =>
      rw [hS0] at hd
      split_ifs with hmem
      · exact hd.2
      · rcases hd.2 with ⟨dL, hsll, hdL⟩
        have hdL_nil : dL = [] := by
          cases dL with
          | nil => rfl
          | cons e _ =>
            have := (hdL e).mp List.mem_cons_self
            exact False.elim (hmem (hd.1.mpr (Or.inl ⟨e, this⟩)))
        subst hdL_nil; exact hsll
  · intro e he hnot
    refine hdelN0 e he fun j B₀ hS0 heBD => ?_
    have hd := hdel j; rw [hS0] at hd
    exact hnot j B₀ (hd.1.mpr (Or.inl ⟨e, heBD⟩)) hS0 heBD

lemma BundleTableEmitState.to_tableRepAt {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {S_cur : BundleTableState slotCap} {mem : ℕ → ℕ}
    (h : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur [] mem)
    (hcur0 : ∀ s < slotCap, mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      mem (btCurTagBase tbl slotCap eCap + s) = 0) :
    BundleTableRepAt slotCap vCap eCap tbl S_cur m mem := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    _, hdisj, _, hedSlot, hendB, hslots, hdisjB, _, _, htouch, hdel, hdelN0⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    hdisj, hedSlot, hendB, ?_, hdisjB, ?_, (fun e he => hdelN0 e he fun _ _ hmem => by cases hmem), hcur0⟩
  · intro j
    have hs := hslots j
    cases hSc : S_cur j with
    | none =>
      rw [hSc] at hs
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hs; exact hs.1
      | some _ => rw [hm] at hs; exact False.elim hs
    | some B =>
      rw [hSc] at hs
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hs; exact False.elim hs
      | some pb =>
        rcases pb with ⟨p, bunCap⟩; rw [hm] at hs
        simp only [List.not_mem_nil, ↓reduceIte] at hs
        exact ⟨hs.1, hs.2.2.1, hs.2.1⟩
  · intro s hs
    set hj : Fin slotCap := ⟨s, hs⟩
    have h1 := htouch s hs; simp only [List.not_mem_nil, ↓reduceIte] at h1
    have h2 : mem (btSlotDelHeadBase tbl slotCap eCap + s) = 0 := by
      have hd := hdel hj
      cases hS0 : S₀ hj with
      | none => rw [hS0] at hd; exact hd
      | some B₀ => rw [hS0] at hd; simpa using hd
    have h3 : mem (btSlotCandHeadBase tbl slotCap eCap + s) = 0 := by
      have hsc := hslots hj
      cases hSc : S_cur hj with
      | none =>
        rw [hSc] at hsc
        cases hm : m.slotBlocks hj with
        | none => rw [hm] at hsc; exact hsc.2.1
        | some _ => rw [hm] at hsc; exact False.elim hsc
      | some B =>
        rw [hSc] at hsc
        cases hm : m.slotBlocks hj with
        | none => rw [hm] at hsc; exact False.elim hsc
        | some pb =>
          rcases pb with ⟨p, bunCap⟩; rw [hm] at hsc
          simpa using hsc.2.2.2
    exact ⟨h1, h2, h3⟩

/-! ## 2. Pure helpers for `runsFoldStep` over distinct candidates -/

lemma runsFoldStep_other_ends {ops : List Update} {B : BundleState} {nB b : ℕ}
    {src' : End → ℕ} (hV : B.vertices = Finset.range nB) (hb : b < nB)
    (hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB) :
    let vruns := byRootVRuns B B.edges src' b
    let res := runsFoldStep (ops, B) (b, vruns)
    res.2.vertices = Finset.range (nB + (vruns.drop 1).length) ∧
    res.2.edges = B.edges ∧
    (∀ x ∈ edgeEnds B.edges, B.bundleOf x ≠ b → res.2.bundleOf x = B.bundleOf x) ∧
    (∀ c < nB, c ≠ b → res.2.ends c = B.ends c) := by
  intro vruns res
  have hsurv : survivingEnds B B.edges b = B.ends b := by
    ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  cases hv : vruns with
  | nil =>
    have hres : res = (ops, B) := by
      simp only [res, hv, runsFoldStep, bundleSplitFoldStep, List.map_nil, bundleRunUpdates,
        List.drop_nil, List.zipIdx_nil, MGraph.applyBatch, List.foldl_nil, List.append_nil]
      refine Prod.ext rfl ?_
      rcases B with ⟨vB, eB, pB, boB⟩
      simp only [BundleState.graph, BundleState.mk.injEq, true_and]
      exact ⟨funext fun w => by simp [runParent], funext fun x : End => by rcases x with ⟨e, side⟩; cases side <;> rfl⟩
    rw [hres]; simp [hV]
  | cons vr0 rest =>
    rcases vr0 with ⟨v0, xs0⟩
    have hperm_vr : ((v0, xs0) :: rest).Perm (rawByRootVRuns B B.edges src' b) := by
      rw [← hv]; exact promoteLargestRun_perm _
    have hvr_info : ∀ vr ∈ (v0, xs0) :: rest, ∀ x ∈ vr.2, x ∈ B.ends b ∧ src' x = vr.1 := by
      intro vr hvr x hx
      have hvr' := hperm_vr.subset hvr
      simp only [rawByRootVRuns, List.mem_map, Finset.mem_sort, finalRootsOf, hsurv, Finset.mem_image] at hvr'
      rcases hvr' with ⟨v, ⟨_, _, rfl⟩, rfl⟩
      simp only [List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hx
      rcases hx with ⟨k, ⟨y, hy, heq⟩, hxy⟩
      subst heq; rw [bundle_endOfKey_endKey] at hxy; rwa [← hxy]
    have hnd : (((v0, xs0) :: rest).map Prod.fst).Nodup := by
      have hnd_raw : ((rawByRootVRuns B B.edges src' b).map Prod.fst).Nodup := by
        simp only [rawByRootVRuns, List.map_map, Function.comp_def, List.map_id']
        exact Finset.sort_nodup _ _
      exact (hperm_vr.map Prod.fst).nodup_iff.mpr hnd_raw
    have hdisj : ∀ i j (hi : i < rest.length) (hj : j < rest.length), i ≠ j →
        ∀ x ∈ rest[i].2, x ∉ rest[j].2 := fun i j hi hj hne x hxi hxj => by
      have h1 := (hvr_info _ (List.mem_cons_of_mem _ (List.getElem_mem hi)) x hxi).2
      have h2 := (hvr_info _ (List.mem_cons_of_mem _ (List.getElem_mem hj)) x hxj).2
      have hnd_r : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      exact hne ((List.Nodup.getElem_inj_iff (i := i) (j := j) (hi := by simp [hi]) (hj := by simp [hj]) hnd_r).mp
        (by simp [h1.symm.trans h2]))
    have hfold_snd : ∀ (rs : List (ℕ × List End)) (o₁ o₂ : List Update) (B' : BundleState) (nB' : ℕ),
        (foldOneSplitRuns b rs (o₁, B', nB')).2 = (foldOneSplitRuns b rs (o₂, B', nB')).2 := by
      intro rs; induction rs with
      | nil => intro _ _ _ _; rfl
      | cons vr tl ih => intro o₁ o₂ B' nB'; exact ih _ _ _ _
    obtain ⟨hfold_eq, _⟩ := runsFoldStep_eq_fold_oneRun (ops := ops) (B := B) (nB := nB) (b := b)
      (v0 := v0) (xs0 := xs0) (rest := rest) hV hb
    let B0 : BundleState := { B with parent := Function.update B.parent b v0 }
    obtain ⟨hV_f, hE_f, _, hstay_f⟩ := foldOneSplitRuns_props rest B0.graph [] B0 nB hV hb rfl
      (fun vr hvr x hx => (hvr_info vr (List.mem_cons_of_mem _ hvr) x hx).1) hdisj hbo_lt
    have hres2 : (foldOneSplitRuns b rest ([], B0, nB)).2.1 = res.2 := by
      rw [congrArg Prod.fst (hfold_snd rest [] ops B0 nB)]
      have := congrArg Prod.snd hfold_eq; simpa [res, hv] using this
    rw [hres2] at hV_f hE_f hstay_f
    have hpres_ne : ∀ x ∈ edgeEnds B.edges, B.bundleOf x ≠ b → res.2.bundleOf x = B.bundleOf x := fun x hx hne => by
      refine hstay_f x hx fun vr hvr hmem => hne ?_
      exact ((BundleState.mem_ends B b x).mp (hvr_info vr (List.mem_cons_of_mem _ hvr) x hmem).1).2
    have hmove_ge : ∀ x ∈ edgeEnds B.edges, B.bundleOf x = b → res.2.bundleOf x = b ∨ nB ≤ res.2.bundleOf x := by
      intro x hx hxb
      by_cases hxr : ∃ vr ∈ rest, x ∈ vr.2
      · right
        have hgo : ∀ (rs : List (ℕ × List End)) (B' : BundleState) (nB' : ℕ),
            B'.vertices = Finset.range nB' → b < nB' → nB ≤ nB' →
            (∀ vr ∈ rs, ∀ y ∈ vr.2, y ∈ B'.ends b) →
            (∀ i j (hi : i < rs.length) (hj : j < rs.length), i ≠ j → ∀ y ∈ rs[i].2, y ∉ rs[j].2) →
            (∀ y ∈ edgeEnds B'.edges, B'.bundleOf y < nB') →
            x ∈ edgeEnds B'.edges → (∃ vr ∈ rs, x ∈ vr.2) →
            nB ≤ (foldOneSplitRuns b rs ([], B', nB')).2.1.bundleOf x := by
          intro rs
          induction rs with
          | nil => intro _ _ _ _ _ _ _ _ _ ⟨_, h, _⟩; cases h
          | cons vr tl ihr =>
            intro B' nB' hV' hb' hnle hsub' hdj' hlt' hx' ⟨vr', hvr', hxvr'⟩
            rcases vr with ⟨vc, xs⟩
            have hxs_sub : ∀ y ∈ xs, y ∈ B'.ends b := hsub' (vc, xs) List.mem_cons_self
            obtain ⟨hV1, hE1, hsrc1, _⟩ := oneRunUpdate_graph_apply B' hV' hb' hxs_sub
            obtain ⟨hends1, _, _⟩ := applyOneSplitRun_ends hV' hb' hlt' hxs_sub
            have htl_sub : ∀ vr ∈ tl, ∀ y ∈ vr.2, y ∈ (applyOneSplitRun B' b nB' vc xs).2.ends b := by
              intro vr0 hvr0 y hy
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr0
              rw [hends1, Finset.mem_sdiff, List.mem_toFinset]
              exact ⟨hsub' _ (List.mem_cons_of_mem _ (List.getElem_mem hj)) y hy,
                fun hxxs => hdj' 0 (j + 1) (by simp) (by simp; omega) (by omega) y hxxs hy⟩
            have hdj_tl : ∀ i j (hi : i < tl.length) (hj : j < tl.length), i ≠ j → ∀ y ∈ tl[i].2, y ∉ tl[j].2 :=
              fun i j hi hj hne => hdj' (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
            have hlt1 : ∀ y ∈ edgeEnds (applyOneSplitRun B' b nB' vc xs).2.edges,
                (applyOneSplitRun B' b nB' vc xs).2.bundleOf y < nB' + 1 := fun y hy => by
              rw [hE1] at hy; rw [hsrc1 y hy]; split_ifs
              · omega
              · exact Nat.lt_succ_of_lt (hlt' y hy)
            dsimp only [foldOneSplitRuns]
            rw [congrArg Prod.fst (hfold_snd tl ([] ++ [(applyOneSplitRun B' b nB' vc xs).1]) [] _ _)]
            rcases List.mem_cons.mp hvr' with rfl | hvr_tl
            · have hbo1 : (applyOneSplitRun B' b nB' vc xs).2.bundleOf x = nB' := by
                rw [hsrc1 x hx', ite_eq_left hxvr']
              have hstay1 := (foldOneSplitRuns_props tl (applyOneSplitRun B' b nB' vc xs).2.graph []
                (applyOneSplitRun B' b nB' vc xs).2 (nB' + 1) hV1 (by omega) rfl htl_sub hdj_tl hlt1).2.2.2 x (hE1 ▸ hx')
                (fun vr0 hvr0 hmem0 => by
                  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr0
                  exact hdj' 0 (j + 1) (by simp) (by simp; omega) (by omega) x hxvr' hmem0)
              rw [hstay1, hbo1]; omega
            · exact ihr _ (nB' + 1) hV1 (by omega) (by omega) htl_sub hdj_tl hlt1 (hE1 ▸ hx') ⟨vr', hvr_tl, hxvr'⟩
        rw [← hres2]
        exact hgo rest B0 nB hV hb (le_refl _)
          (fun vr hvr y hy => (hvr_info vr (List.mem_cons_of_mem _ hvr) y hy).1) hdisj hbo_lt hx hxr
      · left; push Not at hxr; rw [hstay_f x hx hxr, hxb]
    refine ⟨by simpa using hV_f, hE_f, hpres_ne, fun c hc hcb => ?_⟩
    ext x; simp only [BundleState.mem_ends, hE_f]
    constructor
    · rintro ⟨hxE, hxc⟩
      have hxE' : x ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr hxE
      refine ⟨hxE, ?_⟩
      by_cases hxb : B.bundleOf x = b
      · rcases hmove_ge x hxE' hxb with h1 | h2 <;> omega
      · rw [← hpres_ne x hxE' hxb, hxc]
    · rintro ⟨hxE, hxc⟩
      have hxE' : x ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr hxE
      exact ⟨hxE, (hpres_ne x hxE' (by omega)).trans hxc⟩

/-! ## 3. Private helpers for `bundleStepEmitSlotStmt` -/

lemma bundleStepEmitSlot_hdr_runs {w slotCap vCap eCap tbl tourH s outDescPtr h₀ p bunCap : ℕ}
    {pProg : Program} {ω : ℕ → Bool}
    {S₀ S_cur : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {remTouched : List ℕ} {mem₀ : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hs_lt : s < slotCap) (hp_mem : mem₀ (btSlotPtrBase tbl + s) = p)
    (hcap_mem : mem₀ p = bunCap) (hemit : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur remTouched mem₀) :
    let st0 := startState [tbl, tourH, s, outDescPtr, h₀] mem₀ pos
    ∃ stH,
      (∀ {sTail o stF cTail},
        Runs w pProg ω sTail stH o stF cTail →
        Runs w pProg ω
          (.assign 5 (.load (.bin .add (.reg 0) (.const 2))) ;;
           .assign 6 (.bin .mul (.const 2) (.reg 5)) ;;
           .assign 7 (.load (.bin .add (.load (.bin .add (.reg 0) (.const 3))) (.reg 2))) ;;
           .assign 8 (.load (.reg 7)) ;;
           .assign 9 (.load (.bin .add (.reg 0) (.const 5))) ;;
           .assign 10 (.load (.bin .add (.reg 0) (.const 6))) ;;
           .assign 11 (.load (.bin .add (.reg 0) (.const 7))) ;;
           .assign 12 (.load (.bin .add (.reg 0) (.const 8))) ;;
           .assign 13 (.load (.bin .add (.reg 0) (.const 9))) ;;
           .assign 14 (.load (.bin .add (.reg 0) (.const 10))) ;;
           .assign 15 (.load (.bin .add (.reg 0) (.const 11))) ;;
           sTail) st0 o stF (66 + cTail)) ∧
      stH.mem = mem₀ ∧ stH.pos = pos ∧
      stH.regs 0 = tbl ∧ stH.regs 1 = tourH ∧ stH.regs 2 = s ∧ stH.regs 3 = outDescPtr ∧
      stH.regs 4 = h₀ ∧ stH.regs 5 = eCap ∧ stH.regs 6 = 2 * eCap ∧ stH.regs 7 = p ∧
      stH.regs 8 = bunCap ∧ stH.regs 9 = btEndBundleBase tbl slotCap eCap ∧
      stH.regs 10 = btEndPrevBase tbl slotCap eCap ∧ stH.regs 11 = btEndNextBase tbl slotCap eCap ∧
      stH.regs 12 = btSlotTouchedBase tbl slotCap eCap ∧ stH.regs 13 = btSlotDelHeadBase tbl slotCap eCap ∧
      stH.regs 14 = btSlotDelNextBase tbl slotCap eCap ∧ stH.regs 15 = btSlotCandHeadBase tbl slotCap eCap := by
  intro st0
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have hhdr_w : ∀ off < 12, tbl + off < 2 ^ w := fun off hoff => by omega
  rcases hemit with ⟨_, _, h2, h3, _, h5, h6, h7, h8, h9, h10, h11, _⟩
  dsimp only [btOffECap, btOffSlotPtr, btOffEndBundle, btOffEndPrev, btOffEndNext,
    btOffSlotTouched, btOffSlotDelHead, btOffSlotDelNext, btOffSlotCandHead] at h2 h3 h5 h6 h7 h8 h9 h10 h11
  let r5 := Function.update st0.regs 5 eCap
  let r6 := Function.update r5 6 (2 * eCap)
  let r7 := Function.update r6 7 p
  let r8 := Function.update r7 8 bunCap
  let r9 := Function.update r8 9 (btEndBundleBase tbl slotCap eCap)
  let r10 := Function.update r9 10 (btEndPrevBase tbl slotCap eCap)
  let r11 := Function.update r10 11 (btEndNextBase tbl slotCap eCap)
  let r12 := Function.update r11 12 (btSlotTouchedBase tbl slotCap eCap)
  let r13 := Function.update r12 13 (btSlotDelHeadBase tbl slotCap eCap)
  let r14 := Function.update r13 14 (btSlotDelNextBase tbl slotCap eCap)
  let r15 := Function.update r14 15 (btSlotCandHeadBase tbl slotCap eCap)
  have ha5 : Runs w pProg ω (.assign 5 (.load (.bin .add (.reg 0) (.const 2)))) st0 .normal { st0 with regs := r5 } 5 :=
    runs_assign_iff.mpr ⟨eCap, by simp [Expr.eval, BinOp.eval, st0, startState, show 2 < 2 ^ w by omega, hhdr_w 2 (by decide), h2], rfl, rfl, rfl⟩
  have ha6 : Runs w pProg ω (.assign 6 (.bin .mul (.const 2) (.reg 5))) { st0 with regs := r5 } .normal { st0 with regs := r6 } 4 :=
    runs_assign_iff.mpr ⟨2 * eCap, by simp [Expr.eval, BinOp.eval, r5, show 2 < 2 ^ w by omega, show 2 * eCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have ha7 : Runs w pProg ω (.assign 7 (.load (.bin .add (.load (.bin .add (.reg 0) (.const 3))) (.reg 2)))) { st0 with regs := r6 } .normal { st0 with regs := r7 } 8 :=
    runs_assign_iff.mpr ⟨p, by
      simp [Expr.eval, BinOp.eval, r6, r5, st0, startState, show 3 < 2 ^ w by omega, hhdr_w 3 (by decide), h3,
        show btSlotPtrBase tbl + s < 2 ^ w by unfold btSlotPtrBase; omega, hp_mem], rfl, rfl, by simp [Expr.size]⟩
  have ha8 : Runs w pProg ω (.assign 8 (.load (.reg 7))) { st0 with regs := r7 } .normal { st0 with regs := r8 } 3 :=
    runs_assign_iff.mpr ⟨bunCap, by simp [Expr.eval, r7, st0, startState, hcap_mem], rfl, rfl, rfl⟩
  have ha9 : Runs w pProg ω (.assign 9 (.load (.bin .add (.reg 0) (.const 5)))) { st0 with regs := r8 } .normal { st0 with regs := r9 } 5 :=
    runs_assign_iff.mpr ⟨btEndBundleBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r8, r7, r6, r5, st0, startState, show 5 < 2 ^ w by omega, hhdr_w 5 (by decide), h5], rfl, rfl, rfl⟩
  have ha10 : Runs w pProg ω (.assign 10 (.load (.bin .add (.reg 0) (.const 6)))) { st0 with regs := r9 } .normal { st0 with regs := r10 } 5 :=
    runs_assign_iff.mpr ⟨btEndPrevBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r9, r8, r7, r6, r5, st0, startState, show 6 < 2 ^ w by omega, hhdr_w 6 (by decide), h6], rfl, rfl, rfl⟩
  have ha11 : Runs w pProg ω (.assign 11 (.load (.bin .add (.reg 0) (.const 7)))) { st0 with regs := r10 } .normal { st0 with regs := r11 } 5 :=
    runs_assign_iff.mpr ⟨btEndNextBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r10, r9, r8, r7, r6, r5, st0, startState, show 7 < 2 ^ w by omega, hhdr_w 7 (by decide), h7], rfl, rfl, rfl⟩
  have ha12 : Runs w pProg ω (.assign 12 (.load (.bin .add (.reg 0) (.const 8)))) { st0 with regs := r11 } .normal { st0 with regs := r12 } 5 :=
    runs_assign_iff.mpr ⟨btSlotTouchedBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r11, r10, r9, r8, r7, r6, r5, st0, startState, show 8 < 2 ^ w by omega, hhdr_w 8 (by decide), h8], rfl, rfl, rfl⟩
  have ha13 : Runs w pProg ω (.assign 13 (.load (.bin .add (.reg 0) (.const 9)))) { st0 with regs := r12 } .normal { st0 with regs := r13 } 5 :=
    runs_assign_iff.mpr ⟨btSlotDelHeadBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState, show 9 < 2 ^ w by omega, hhdr_w 9 (by decide), h9], rfl, rfl, rfl⟩
  have ha14 : Runs w pProg ω (.assign 14 (.load (.bin .add (.reg 0) (.const 10)))) { st0 with regs := r13 } .normal { st0 with regs := r14 } 5 :=
    runs_assign_iff.mpr ⟨btSlotDelNextBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState, show 10 < 2 ^ w by omega, hhdr_w 10 (by decide), h10], rfl, rfl, rfl⟩
  have ha15 : Runs w pProg ω (.assign 15 (.load (.bin .add (.reg 0) (.const 11)))) { st0 with regs := r14 } .normal { st0 with regs := r15 } 5 :=
    runs_assign_iff.mpr ⟨btSlotCandHeadBase tbl slotCap eCap, by
      simp [Expr.eval, BinOp.eval, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState, show 11 < 2 ^ w by omega, hhdr_w 11 (by decide), h11], rfl, rfl, rfl⟩
  refine ⟨{ st0 with regs := r15 }, fun {sTail o stF cTail} hTail => ?_,
    rfl, rfl, by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7, r6],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8, r7],
    by simp [r15, r14, r13, r12, r11, r10, r9, r8],
    by simp [r15, r14, r13, r12, r11, r10, r9],
    by simp [r15, r14, r13, r12, r11, r10],
    by simp [r15, r14, r13, r12, r11],
    by simp [r15, r14, r13, r12],
    by simp [r15, r14, r13],
    by simp [r15, r14],
    by simp [r15]⟩
  have hrun := bundle_runs_seq_normal ha5 (bundle_runs_seq_normal ha6 (bundle_runs_seq_normal ha7
    (bundle_runs_seq_normal ha8 (bundle_runs_seq_normal ha9 (bundle_runs_seq_normal ha10
      (bundle_runs_seq_normal ha11 (bundle_runs_seq_normal ha12 (bundle_runs_seq_normal ha13
        (bundle_runs_seq_normal ha14 (bundle_runs_seq_normal ha15 hTail))))))))))
  convert hrun using 1; omega


lemma BundleSlotRepCand.of_agree_ends {eCap prevBase nextBase p bunCap candHeadAddr : ℕ}
    {B : BundleState} {candSet : Finset ℕ} {mem mem' : ℕ → ℕ}
    (h : BundleSlotRepCand eCap prevBase nextBase p bunCap B candHeadAddr candSet mem)
    (hblk : ∀ off < bundleSlotBlockSize bunCap, mem' (p + off) = mem (p + off))
    (hch : mem' candHeadAddr = mem candHeadAddr)
    (hpn : ∀ k < 2 * eCap, endOfKey k ∈ edgeEnds B.edges →
      mem' (prevBase + k) = mem (prevBase + k) ∧ mem' (nextBase + k) = mem (nextBase + k)) :
    BundleSlotRepCand eCap prevBase nextBase p bunCap B candHeadAddr candSet mem' := by
  rcases h with ⟨nB, hV, hnB, hE, hbo, hp0, hc0, hc1, hc2, hdll, hpar, htail,
    hseen, hinC, hclt, ⟨cL, hsll, hcL⟩, hcN0⟩
  refine ⟨nB, hV, hnB, hE, hbo, hp0,
    (hblk bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)).trans hc0,
    (hblk bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)).trans hc1,
    (hblk bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)).trans hc2,
    fun b hb => by
      obtain ⟨L, hL, hlen, hmem⟩ := hdll b hb
      refine ⟨L, hL.of_agree
        (by simpa [bsHeadBase, Nat.add_assoc] using hblk (3 + b) (by unfold bundleSlotBlockSize; omega))
        (fun k hk => (hpn k (hL.2.1 k hk) ((mem_edgeEnds _ _).mpr ((BundleState.mem_ends _ _ _).mp ((hmem k).mp hk)).1)).1)
        (fun k hk => (hpn k (hL.2.1 k hk) ((mem_edgeEnds _ _).mpr ((BundleState.mem_ends _ _ _).mp ((hmem k).mp hk)).1)).2),
        by simpa [bsSizeBase, Nat.add_assoc] using (hblk (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsSizeBase, Nat.add_assoc] using hlen),
        hmem⟩,
    fun b hb hem => by simpa [bsParentBase, Nat.add_assoc] using (hblk (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsParentBase, Nat.add_assoc] using hpar b hb hem),
    fun b h1 h2 => ⟨by simpa [bsHeadBase, Nat.add_assoc] using (hblk (3 + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsHeadBase, Nat.add_assoc] using (htail b h1 h2).1),
      by simpa [bsSizeBase, Nat.add_assoc] using (hblk (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsSizeBase, Nat.add_assoc] using (htail b h1 h2).2.1),
      by simpa [bsParentBase, Nat.add_assoc] using (hblk (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsParentBase, Nat.add_assoc] using (htail b h1 h2).2.2)⟩,
    fun b hb => by simpa [bsSeenBase, Nat.add_assoc] using (hblk (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsSeenBase, Nat.add_assoc] using hseen b hb),
    fun b hb => by simpa [bsInCandBase, Nat.add_assoc] using (hblk (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsInCandBase, Nat.add_assoc] using hinC b hb),
    hclt, ⟨cL, hsll.of_agree hch fun b hb => by
      have := hsll.mem_lt b hb
      simpa [bsCandNextBase, Nat.add_assoc] using hblk (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega), hcL⟩,
    fun b hb hnot => by simpa [bsCandNextBase, Nat.add_assoc] using (hblk (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsCandNextBase, Nat.add_assoc] using hcN0 b hb hnot)⟩

lemma BundleSlotRepAt.of_agree_ends {eCap prevBase nextBase p bunCap : ℕ}
    {B : BundleState} {mem mem' : ℕ → ℕ}
    (h : BundleSlotRepAt eCap prevBase nextBase p bunCap B mem)
    (hblk : ∀ off < bundleSlotBlockSize bunCap, mem' (p + off) = mem (p + off))
    (hpn : ∀ k < 2 * eCap, endOfKey k ∈ edgeEnds B.edges →
      mem' (prevBase + k) = mem (prevBase + k) ∧ mem' (nextBase + k) = mem (nextBase + k)) :
    BundleSlotRepAt eCap prevBase nextBase p bunCap B mem' := by
  rcases h with ⟨nB, hV, hnB, hE, hbo, hp0, hc0, hc1, hc2, hdll, hpar, htail, hscr⟩
  refine ⟨nB, hV, hnB, hE, hbo, hp0,
    (hblk bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)).trans hc0,
    (hblk bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)).trans hc1,
    (hblk bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)).trans hc2,
    fun b hb => by
      obtain ⟨L, hL, hlen, hmem⟩ := hdll b hb
      refine ⟨L, hL.of_agree
        (by simpa [bsHeadBase, Nat.add_assoc] using hblk (3 + b) (by unfold bundleSlotBlockSize; omega))
        (fun k hk => (hpn k (hL.2.1 k hk) ((mem_edgeEnds _ _).mpr ((BundleState.mem_ends _ _ _).mp ((hmem k).mp hk)).1)).1)
        (fun k hk => (hpn k (hL.2.1 k hk) ((mem_edgeEnds _ _).mpr ((BundleState.mem_ends _ _ _).mp ((hmem k).mp hk)).1)).2),
        by simpa [bsSizeBase, Nat.add_assoc] using (hblk (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsSizeBase, Nat.add_assoc] using hlen),
        hmem⟩,
    fun b hb hem => by simpa [bsParentBase, Nat.add_assoc] using (hblk (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsParentBase, Nat.add_assoc] using hpar b hb hem),
    fun b h1 h2 => ⟨by simpa [bsHeadBase, Nat.add_assoc] using (hblk (3 + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsHeadBase, Nat.add_assoc] using (htail b h1 h2).1),
      by simpa [bsSizeBase, Nat.add_assoc] using (hblk (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsSizeBase, Nat.add_assoc] using (htail b h1 h2).2.1),
      by simpa [bsParentBase, Nat.add_assoc] using (hblk (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsParentBase, Nat.add_assoc] using (htail b h1 h2).2.2)⟩,
    fun b hb => ⟨by simpa [bsSeenBase, Nat.add_assoc] using (hblk (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsSeenBase, Nat.add_assoc] using (hscr b hb).1),
      by simpa [bsInCandBase, Nat.add_assoc] using (hblk (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsInCandBase, Nat.add_assoc] using (hscr b hb).2.1),
      by simpa [bsCandNextBase, Nat.add_assoc] using (hblk (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega)).trans (by simpa [bsCandNextBase, Nat.add_assoc] using (hscr b hb).2.2)⟩⟩

end

end MinCostFlow.SparseCore.Program
