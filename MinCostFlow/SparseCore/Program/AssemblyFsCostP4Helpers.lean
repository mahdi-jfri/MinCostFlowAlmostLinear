module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCostGoal
public import MinCostFlow.SparseCore.Program.AssemblyFsCostP4WS

import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideSpan
import Mathlib.Tactic

/-!
# Shared Phase 4 slot, Finset, and history helpers (`AssemblyFsCostP4Helpers`)

Pure lemmas shared by `AssemblyFsCostP4Tasks` and `AssemblyFsCostP4New`:

* `p4SpanAfter_eq_of_mem_nodup`, `p4SpanAfter_eq_self_of_empty`, `bucketSpannerRep_slot_dsRepAt`,
  `dsHist_applyBatch_eq_state_G`, `p4Span_slotData`.
* `sum_activePairs_eq`, `list_sum_le_finset_sum_of_pmap`, `update_nil_counts`,
  `batchDeletes_card_le`, `batchInsEdges_card_le`.
* `foldl_p4WVStep_delSup_insSup_le`, `foldl_p4NewStep_delSup_insSup_le`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- If `t ∈ ts` is the unique task on slot `j` (by `Nodup` of task slots), `S6 j = some d₀`, and
`mem₀ t.batchPtr ≠ 0`, then `p4SpanAfter` sets slot `j` to `some (p4NewHist P mem₀ d₀ t)`. -/
lemma p4SpanAfter_eq_of_mem_nodup (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) {j : Fin cap} {d₀ : DSHist} (hd₀ : S6 j = some d₀) :
    ∀ (ts : List SpanUpdTask) (S : BucketSpannerState cap) (t : SpanUpdTask),
      t ∈ ts → (ts.map SpanUpdTask.slot).Nodup → t.slot = j.1 → mem₀ t.batchPtr ≠ 0 →
      ts.foldl (p4SpanStep P S6 mem₀) S j = some (p4NewHist P mem₀ d₀ t)
  | [], _, _, ht, _, _, _ => absurd ht (by simp)
  | a :: ts, S, t, ht, hnd, hslot, hnz => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ht with rfl | hmem
      · have hnot : j.1 ∉ ts.map SpanUpdTask.slot := by rw [← hslot]; exact hnd.1
        rw [p4SpanAfter_unchanged P S6 mem₀ hnot]
        unfold p4SpanStep
        have hs : t.slot < cap := hslot ▸ j.2
        have hd' : S6 ⟨t.slot, hs⟩ = some d₀ := by
          rw [show (⟨t.slot, hs⟩ : Fin cap) = j from Fin.ext hslot]; exact hd₀
        rw [p4OnTask_of hs hd' hnz]
        have hfin : (⟨t.slot, hs⟩ : Fin cap) = j := Fin.ext hslot
        simp [BucketSpannerState.set, hfin]
      · exact p4SpanAfter_eq_of_mem_nodup P S6 mem₀ hd₀ ts _ t hmem hnd.2 hslot hnz

/-- If every task on slot `j` has `mem₀ t.batchPtr = 0`, then `p4SpanAfter` leaves slot `j`
unchanged. -/
lemma p4SpanAfter_eq_self_of_empty (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (ts : List SpanUpdTask) {j : Fin cap}
    (hempty : ∀ t ∈ ts, t.slot = j.1 → mem₀ t.batchPtr = 0) :
    p4SpanAfter P S6 mem₀ ts j = S6 j := by
  rcases p4SpanAfter_cases P S6 mem₀ j ts S6 with h | ⟨t, ht, -, hslot, -, hnz, -⟩
  · exact h
  · exact absurd (hempty t ht hslot) hnz

/-- Extracting `DSRepAt` and `1 ≤ max impl.p_s impl.p_t` from a populated slot of
`(bucketSpannerRep P cap).rep`. -/
lemma bucketSpannerRep_slot_dsRepAt {P : DSParams} {cap tbl : ℕ} {S : BucketSpannerState cap}
    {x : BucketSpannerMeta P.L cap} {mem : ℕ → ℕ} (h : (bucketSpannerRep P cap).rep tbl S x mem)
    {j : Fin cap} {d : DSHist} (hj : S j = some d) :
    (∃ b m, DSRepAt P b d m mem) ∧ 1 ≤ max P.impl.p_s P.impl.p_t := by
  have hslot := h.1 j
  rw [hj] at hslot
  cases hx : x.slots j with
  | none => rw [hx] at hslot; exact hslot.elim
  | some bm =>
    rw [hx] at hslot
    obtain ⟨-, ⟨-, hdsRep, hp⟩, -⟩ := hslot
    exact ⟨⟨bm.1, bm.2.2, hdsRep⟩, hp⟩

/-- `d.G₀.applyBatch d.flat = (d.state P).G` for any valid history with `1 ≤ P.L`,
`d.G₀.m ≤ P.mMax`, valid `d.flat`, and delete/split entries. -/
lemma dsHist_applyBatch_eq_state_G (P : DSParams) (d : DSHist)
    (hVG₀ : d.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hBV : d.G₀.BatchIsValid d.flat) (hds : ∀ u ∈ d.flat, isDelOrSplit u) :
    d.G₀.applyBatch d.flat = (d.state P).G := by
  have hq : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have h := (runInv_all hVG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
    hBV hds d.flat.length le_rfl).1.G_eq
  rw [List.take_length] at h
  exact h.symm

/-- Rewriting a double sum over `tr.activeComps` and `tr.activeBuckets` as a sum over
`activePairs tr`. -/
lemma sum_activePairs_eq {L : ℕ} (tr : BundleTreeState L) (f : Finset ℕ × ℤ → ℕ) :
    (activePairs tr).sum f =
      tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b => f (C, b) := by
  classical
  unfold activePairs
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_image]
    intro b₁ _ b₂ _ h; exact (Prod.mk.inj h).2
  · intro C₁ _ C₂ _ hne
    refine Finset.disjoint_left.mpr fun p h1 h2 => ?_
    obtain ⟨b₁, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b₂, -, heq⟩ := Finset.mem_image.mp h2
    exact hne (Prod.mk.inj heq).1.symm

/-- Injection bound: given a partial map `φ : α → Option β` on `l` such that `φ` is
injective on `l` where it returns `some b` (`b ∈ S`), and `f a = 0` when `φ a = none` and
`f a ≤ g b` when `φ a = some b`, we have `(l.map f).sum ≤ S.sum g`. -/
lemma list_sum_le_finset_sum_of_pmap {α β : Type*} [DecidableEq β]
    (S : Finset β) (f : α → ℕ) (g : β → ℕ) (φ : α → Option β) :
    ∀ l : List α,
      (∀ a ∈ l, match φ a with | none => f a = 0 | some b => b ∈ S ∧ f a ≤ g b) →
      (∀ i (hi : i < l.length) j (hj : j < l.length) (b : β),
        φ (l[i]'hi) = some b → φ (l[j]'hj) = some b → i = j) →
      (l.map f).sum ≤ S.sum g
  | [], _, _ => Nat.zero_le _
  | a :: tl, hmem, hinj => by
      simp only [List.map_cons, List.sum_cons]
      have htl_inj : ∀ i (hi : i < tl.length) j (hj : j < tl.length) (b : β),
          φ (tl[i]'hi) = some b → φ (tl[j]'hj) = some b → i = j := by
        intro i hi j hj b h1 h2
        have := hinj (i + 1) (Nat.succ_lt_succ hi) (j + 1) (Nat.succ_lt_succ hj) b h1 h2
        omega
      cases hφ : φ a with
      | none =>
        have h0 : f a = 0 := by
          have := hmem a List.mem_cons_self; rwa [hφ] at this
        rw [h0, zero_add]
        exact list_sum_le_finset_sum_of_pmap S f g φ tl
          (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) htl_inj
      | some b =>
        have ha := hmem a List.mem_cons_self
        rw [hφ] at ha
        obtain ⟨hbS, hle⟩ := ha
        have htl_mem : ∀ x ∈ tl, match φ x with
            | none => f x = 0 | some b' => b' ∈ S.erase b ∧ f x ≤ g b' := by
          intro x hx
          have hxm := hmem x (List.mem_cons_of_mem _ hx)
          cases hφx : φ x with
          | none => rwa [hφx] at hxm
          | some b' =>
            rw [hφx] at hxm
            refine ⟨Finset.mem_erase.mpr ⟨?_, hxm.1⟩, hxm.2⟩
            intro heq
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
            have h0 := hinj 0 (by simp) (i + 1) (Nat.succ_lt_succ hi) b' (heq ▸ hφ) hφx
            omega
        have ih := list_sum_le_finset_sum_of_pmap (S.erase b) f g φ tl htl_mem htl_inj
        have hsum : S.sum g = g b + (S.erase b).sum g := (Finset.add_sum_erase S g hbS).symm
        omega

/-- Empty update batch leaves `UH`, `D`, and `updateReembSet` empty. -/
lemma update_nil_counts {L : ℕ} (st : DynSpannerState L)
    (sp : MGraph → MGraph → Embedding → SparsifyOut) :
    (update st [] sp).UH = [] ∧ (update st [] sp).D = ∅ ∧ updateReembSet st [] sp = ∅ :=
  ⟨by simp [update, updateGo], by simp [update, updateGo], updateReembSet_nil st sp⟩

/-- Cardinality of `batchDeletes U` is at most `U.length`. -/
lemma batchDeletes_card_le (U : List Update) : (batchDeletes U).card ≤ U.length := by
  have hsub : batchDeletes U ⊆ (U.filterMap fun | .delete e => some e | _ => none).toFinset := by
    intro e he
    obtain ⟨w, hw, hw_eq⟩ := (mem_batchDeletes_iff _ _).mp he
    subst hw_eq
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.delete e, hw, rfl⟩)
  exact (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le _).trans (List.length_filterMap_le _ _))

/-- Cardinality of `batchInsEdges U` is at most `U.length`. -/
lemma batchInsEdges_card_le (U : List Update) : (batchInsEdges U).card ≤ U.length := by
  unfold batchInsEdges
  exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

/-- Per-pair slot data extracted from `P4SlotTasks`, `hspanS`, and `hRepX'`. -/
lemma p4Span_slotData {P : DSParams} {cap tbl lo hi : ℕ}
    {tr : BundleTreeState P.L} {U : List Update} {ord ord' : ℕ → List End}
    {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap} {mem₀ mem₄ : ℕ → ℕ}
    {tasks : List SpanUpdTask} {x' : BucketSpannerMeta P.L cap}
    (hT : P4SlotTasks P tr
      (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord') slotOf S6 mem₀ tasks
      lo hi)
    (hspanS : ∀ q ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ∃ (hs : slotOf q < cap) (d : DSHist),
        S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q ∧ d.G₀ = tr.initBunG q)
    (hRepX' : (bucketSpannerRep P cap).rep tbl (p4SpanAfter P S6 mem₀ tasks) x' mem₄) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let tr' := info.state
    ∀ q ∈ activePairs tr',
      ∃ (hs : slotOf q < cap) (d₀ : DSHist),
        S6 ⟨slotOf q, hs⟩ = some d₀ ∧
        d₀.state P = tr.dyn q ∧
        d₀.G₀ = tr.initBunG q ∧
        (info.U_B q = [] →
          p4SpanAfter P S6 mem₀ tasks ⟨slotOf q, hs⟩ = some d₀ ∧
          d₀.G₀.IsValid ∧ d₀.G₀.m ≤ P.mMax ∧
          d₀.G₀.BatchIsValid d₀.flat ∧ (∀ u ∈ d₀.flat, isDelOrSplit u)) ∧
        (info.U_B q ≠ [] →
          let d₁ : DSHist := ⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩
          p4SpanAfter P S6 mem₀ tasks ⟨slotOf q, hs⟩ = some d₁ ∧
          d₁.state P = tr'.dyn q ∧
          d₀.G₀.IsValid ∧ d₀.G₀.m ≤ P.mMax ∧
          d₀.G₀.BatchIsValid (d₀.flat ++ info.U_B q) ∧
          (∀ u ∈ d₀.flat ++ info.U_B q, isDelOrSplit u) ∧
          batchSplitCount d₀.flat + batchSplitCount (info.U_B q) ≤ P.splitBound ∧
          1 ≤ max P.impl.p_s P.impl.p_t) := by
  intro sp info tr' q hq
  obtain ⟨hs, d₀, hd₀, hst₀, hG₀⟩ := hspanS q hq
  refine ⟨hs, d₀, hd₀, hst₀, hG₀, ?_, ?_⟩
  · intro hempty
    have hpa : p4SpanAfter P S6 mem₀ tasks ⟨slotOf q, hs⟩ = some d₀ := by
      rw [p4SpanAfter_eq_self_of_empty P S6 mem₀ tasks]
      · exact hd₀
      · intro t ht hts
        obtain ⟨p', hp', hps, hbat⟩ := hT.htask t ht
        have hpq : p' = q := hT.hinj p' hp' q hq (hps.symm.trans hts)
        subst hpq
        have hs' : t.slot < cap := hts ▸ hs
        have hd₀' : S6 ⟨t.slot, hs'⟩ = some d₀ := by
          rw [show (⟨t.slot, hs'⟩ : Fin cap) = ⟨slotOf p', hs⟩ from Fin.ext hts]; exact hd₀
        exact (hbat hs' d₀ hd₀').2.mpr hempty
    obtain ⟨⟨b0, m0, hrep0⟩, -⟩ := bucketSpannerRep_slot_dsRepAt hRepX' hpa
    exact ⟨hpa, hrep0.2.1, hrep0.2.2.1, hrep0.2.2.2.2.1, hrep0.2.2.2.2.2.1⟩
  · intro hne
    obtain ⟨t, ht, hts⟩ := hT.hcover q hq hne
    obtain ⟨p', hp', hps, hbat⟩ := hT.htask t ht
    have hpq : p' = q := hT.hinj p' hp' q hq (hps.symm.trans hts)
    subst hpq
    have hs' : t.slot < cap := hts ▸ hs
    have hd₀' : S6 ⟨t.slot, hs'⟩ = some d₀ := by
      rw [show (⟨t.slot, hs'⟩ : Fin cap) = ⟨slotOf p', hs⟩ from Fin.ext hts]; exact hd₀
    obtain ⟨hdec, hzero⟩ := hbat hs' d₀ hd₀'
    have hnz : mem₀ t.batchPtr ≠ 0 := fun hz => hne (hzero.mp hz)
    have hpa := p4SpanAfter_eq_of_mem_nodup P S6 mem₀ hd₀ tasks S6 t ht hT.hnd hts hnz
    have hnh : p4NewHist P mem₀ d₀ t = ⟨d₀.G₀, d₀.Us ++ [info.U_B p']⟩ := by
      unfold p4NewHist; rw [hdec]
    rw [hnh] at hpa
    obtain ⟨⟨b1, m1, hrep1⟩, hp1⟩ := bucketSpannerRep_slot_dsRepAt hRepX' hpa
    have hfl : (⟨d₀.G₀, d₀.Us ++ [info.U_B p']⟩ : DSHist).flat = d₀.flat ++ info.U_B p' :=
      dsHist_flat_append d₀ (info.U_B p')
    have hst1 : (⟨d₀.G₀, d₀.Us ++ [info.U_B p']⟩ : DSHist).state P = tr'.dyn p' := by
      rw [dsHist_append_state_eq_update, hst₀]
      show (update (tr.dyn p') (info.U_B p') (canonicalSparsify P.impl)).state =
        (stepBundleTree sp tr U ord ord').state.dyn p'
      rfl
    have hsc := hrep1.2.2.2.2.2.2.1
    rw [hfl, batchSplitCount_append] at hsc
    exact ⟨hpa, hst1, hrep1.2.1, hrep1.2.2.1, hfl ▸ hrep1.2.2.2.2.1,
      hfl ▸ hrep1.2.2.2.2.2.1, hsc, hp1⟩

/-- `p4SpanWV` workspace fold over `qs`: upper bound on `delSup` and `insSup` cardinalities. -/
lemma foldl_p4WVStep_delSup_insSup_le (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) :
    ∀ (qs : List (SpanUpdTask × P4TaskOut)) (A : Phase4WS × EmbView),
      (∀ q ∈ qs, P4OutOK P S6 mem₀ q) →
      (∀ q ∈ qs, ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d →
        mem₀ q.1.batchPtr ≠ 0 →
        let U := (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1
        d.G₀.IsValid ∧ 1 ≤ P.L ∧ d.G₀.m ≤ P.mMax ∧
        d.G₀.BatchIsValid (d.flat ++ U) ∧ ∀ u ∈ d.flat ++ U, isDelOrSplit u) →
      let stepCnt (q : SpanUpdTask × P4TaskOut) : ℕ :=
        p4OnTask S6 mem₀ 0 (fun _ _ d =>
          let U := (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1
          let d' : DSHist := ⟨d.G₀, d.Us ++ [U]⟩
          (update (d.state P) U (canonicalSparsify P.impl)).UH.length +
            (update (d.state P) U (canonicalSparsify P.impl)).D.card +
            (updateReembSet (d.state P) U (canonicalSparsify P.impl)).sum
              (fun e => (piTotal (d'.state P) e).length)) q.1
      (qs.foldl (p4WVStep P S6 mem₀ OS) A).1.delSup.toFinset.card ≤
        A.1.delSup.toFinset.card + (qs.map stepCnt).sum ∧
      (qs.foldl (p4WVStep P S6 mem₀ OS) A).1.insSup.toFinset.card ≤
        A.1.insSup.toFinset.card + (qs.map stepCnt).sum
  | [], A, _, _ => by simp
  | q :: rest, A, hok, hval => by
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4WVStep_delSup_insSup_le P S6 mem₀ OS rest
        (p4WVStep P S6 mem₀ OS A q)
        (fun x hx => hok x (List.mem_cons_of_mem _ hx))
        (fun x hx => hval x (List.mem_cons_of_mem _ hx))
      have hstep :
          (p4WVStep P S6 mem₀ OS A q).1.delSup.toFinset.card ≤
            A.1.delSup.toFinset.card +
              p4OnTask S6 mem₀ 0 (fun _ _ d =>
                let U := (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1
                let d' : DSHist := ⟨d.G₀, d.Us ++ [U]⟩
                (update (d.state P) U (canonicalSparsify P.impl)).UH.length +
                  (update (d.state P) U (canonicalSparsify P.impl)).D.card +
                  (updateReembSet (d.state P) U (canonicalSparsify P.impl)).sum
                    (fun e => (piTotal (d'.state P) e).length)) q.1 ∧
          (p4WVStep P S6 mem₀ OS A q).1.insSup.toFinset.card ≤
            A.1.insSup.toFinset.card +
              p4OnTask S6 mem₀ 0 (fun _ _ d =>
                let U := (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1
                let d' : DSHist := ⟨d.G₀, d.Us ++ [U]⟩
                (update (d.state P) U (canonicalSparsify P.impl)).UH.length +
                  (update (d.state P) U (canonicalSparsify P.impl)).D.card +
                  (updateReembSet (d.state P) U (canonicalSparsify P.impl)).sum
                    (fun e => (piTotal (d'.state P) e).length)) q.1 := by
        unfold p4WVStep p4OnTask
        by_cases hs : q.1.slot < cap
        · simp only [hs, ↓reduceDIte]
          cases hd : S6 ⟨q.1.slot, hs⟩ with
          | none => simp
          | some d =>
            by_cases hnz : mem₀ q.1.batchPtr = 0
            · simp [hnz]
            · simp only [hnz, ↓reduceIte]
              obtain ⟨hVG₀, hL, hGm₀, hBV, hds⟩ := hval q List.mem_cons_self hs d hd hnz
              have hF := hok q List.mem_cons_self hs d hd hnz
              have hWS := p4TaskWS_delSup_insSup_card_le P d
                (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1 OS q.2 A.1 hVG₀ hL hGm₀ hBV hds hF
              dsimp only [p4NewHist] at hWS ⊢
              exact ⟨by omega, by omega⟩
        · simp [hs]
      dsimp only at ih1 ih2 hstep ⊢
      exact ⟨by omega, by omega⟩

/-- `p4SpanWV` workspace fold over new slots `ns`: `delSup` is unchanged and `insSup` grows by at
most the sum of `q.2.toFinset.card`. -/
lemma foldl_p4NewStep_delSup_insSup_le (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) :
    ∀ (ns : List (ℕ × List ℕ)) (A : Phase4WS × EmbView),
      (ns.foldl (p4NewStep P S6) A).1.delSup = A.1.delSup ∧
      (ns.foldl (p4NewStep P S6) A).1.insSup.toFinset.card ≤
        A.1.insSup.toFinset.card + (ns.map fun q => q.2.toFinset.card).sum
  | [], A => by simp
  | q :: rest, A => by
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4NewStep_delSup_insSup_le P S6 rest (p4NewStep P S6 A q)
      have hstep :
          (p4NewStep P S6 A q).1.delSup = A.1.delSup ∧
          (p4NewStep P S6 A q).1.insSup.toFinset.card ≤
            A.1.insSup.toFinset.card + q.2.toFinset.card := by
        unfold p4NewStep
        by_cases hs : q.1 < cap
        · simp only [hs, ↓reduceDIte]
          cases hd : S6 ⟨q.1, hs⟩ with
          | none => simp
          | some d =>
            have h := foldl_p4StepNew_delSup_insSup (d.state P).H.E q.2 { A.1 with copyBuf := [] }
            exact ⟨h.1, (Finset.card_le_card h.2).trans (Finset.card_union_le _ _)⟩
        · simp [hs]
      exact ⟨ih1.trans hstep.1, by omega⟩

end

end MinCostFlow.SparseCore.Program
