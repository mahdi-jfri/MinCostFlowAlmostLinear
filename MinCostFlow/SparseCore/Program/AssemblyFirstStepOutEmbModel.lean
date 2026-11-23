module

public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstRotProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Proof
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActProof
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Model
public import MinCostFlow.SparseCore.Program.AssemblyFirstSpan
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepIface

import Mathlib.Tactic

/-!
# Phase 4 pure model theorems: `batchLastOp`, `targetE'`, and candidate supersets (`AssemblyFirstStepOutEmbModel`)

Provides the pure model lemmas for Phase 4's output-edge selection and embedding updates:
1. `AsmFirstStepExtraInv` (the three side invariants of `AssemblyBranchSideGapS8.lean`).
2. `batchLastOp`, `batchLastOpFold`, `mem_applyBatch_E_iff_lastOp`.
3. Untouched-slot empty-batch lemmas (`dsHist_append_nil_state`, `dsHist_append_nil_bank`,
   `spanUpdAfter_not_mem`, `spanUpdAfter_mem`).
4. Exact `O(1)` decision predicate `mem_targetE'_iff_dec` for `e ∈ info.state.S_cur.E`.
5. Exact candidate supersets `outDelSet_subset_sup`, `outInsSet_subset_sup`, and
   `stepBundleTree_reembSet_eq_sup`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

/-! ## 1. Definitions -/

@[expose] public section

/-- **The extra side invariant** on `(tr, y)`:
1. inactive components have initial spanner states `⟨tr.initBunG (C, b), []⟩`;
2. active bucket spanners have valid initial graphs `m ≤ y.mMax` and cumulative split
   counts `batchSplitCount d.flat ≤ (asmBrSP impl w depth y).splitBound`;
3. `1 ≤ max impl.p_s impl.p_t`. -/
def AsmFirstStepExtraInv
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w depth : ℕ) (tr : BundleTreeState depth)
    (y : AsmBrSide B5 depth) : Prop :=
  (∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
    ∀ b ∈ tr.activeBuckets C,
      tr.dyn (C, b) = DSHist.state (asmBrSP impl w depth y) ⟨tr.initBunG (C, b), []⟩) ∧
  (∀ q ∈ activePairs tr, ∀ (hs : y.slotOf q < y.cap) (d : DSHist),
    y.spanS ⟨y.slotOf q, hs⟩ = some d →
    d.G₀.IsValid ∧ d.G₀.m ≤ y.mMax ∧
    batchSplitCount d.flat ≤ (asmBrSP impl w depth y).splitBound) ∧
  1 ≤ max impl.p_s impl.p_t

/-- Last insert/delete operation on edge `e` in `U`: `0` untouched, `1` insert, `2` delete. -/
def batchLastOp : List Update → ℕ → ℕ
  | [], _ => 0
  | u :: rest, e =>
    if batchLastOp rest e ≠ 0 then batchLastOp rest e
    else match u with
      | .insert e' _ _ => if e' = e then 1 else 0
      | .delete e' => if e' = e then 2 else 0
      | .split _ _ _ _ => 0

/-- Forward fold matching the Word-RAM scan of `batch` to populate `lastOp[e]`. -/
def batchLastOpFold (U : List Update) (f : ℕ → ℕ) : ℕ → ℕ :=
  U.foldl (fun acc u => match u with
    | .insert e _ _ => Function.update acc e 1
    | .delete e => Function.update acc e 2
    | .split _ _ _ _ => acc) f

/-- Edges deleted from `H` in a spanner update batch `UH`. -/
def uhDelFinset (UH : List Update) : Finset ℕ :=
  (UH.filterMap fun | .delete e => some e | _ => none).toFinset

/-- Edges inserted into `H` in a spanner update batch `UH`. -/
def uhInsFinset (UH : List Update) : Finset ℕ :=
  (UH.filterMap fun | .insert e _ _ => some e | _ => none).toFinset

end

/-! ## 2. `batchLastOp` and untouched-slot spanner lemmas -/

public section

@[simp] lemma batchLastOp_nil (e : ℕ) : batchLastOp [] e = 0 := rfl

@[simp] lemma batchLastOp_cons (u : Update) (rest : List Update) (e : ℕ) :
    batchLastOp (u :: rest) e =
      if batchLastOp rest e ≠ 0 then batchLastOp rest e
      else match u with
        | .insert e' _ _ => if e' = e then 1 else 0
        | .delete e' => if e' = e then 2 else 0
        | .split _ _ _ _ => 0 := rfl

lemma batchLastOp_le_two (U : List Update) (e : ℕ) : batchLastOp U e ≤ 2 := by
  induction U with
  | nil => simp
  | cons u rest ih =>
    rw [batchLastOp_cons]; split_ifs with hr
    · exact ih
    · cases u with
      | insert e' _ _ => by_cases h : e' = e <;> simp [h]
      | delete e' => by_cases h : e' = e <;> simp [h]
      | split _ _ _ _ => simp

lemma batchLastOpFold_eq (U : List Update) (f : ℕ → ℕ) (e : ℕ) :
    batchLastOpFold U f e = if batchLastOp U e ≠ 0 then batchLastOp U e else f e := by
  induction U generalizing f with
  | nil => simp [batchLastOpFold]
  | cons u rest ih =>
    change batchLastOpFold rest _ e = _
    rw [ih, batchLastOp_cons]
    by_cases hr : batchLastOp rest e ≠ 0
    · simp [hr]
    · have hr0 : batchLastOp rest e = 0 := Classical.not_not.mp hr
      simp only [hr0, ne_eq, not_true_eq_false, ↓reduceIte]
      cases u with
      | insert e' _ _ =>
        by_cases he : e' = e
        · subst he; simp
        · simp [he, Function.update_of_ne (Ne.symm he)]
      | delete e' =>
        by_cases he : e' = e
        · subst he; simp
        · simp [he, Function.update_of_ne (Ne.symm he)]
      | split _ _ _ _ => simp

lemma batchLastOpFold_zero (U : List Update) (e : ℕ) :
    batchLastOpFold U (fun _ => 0) e = batchLastOp U e := by
  rw [batchLastOpFold_eq]; split_ifs <;> omega

theorem mem_applyBatch_E_iff_lastOp (G : MGraph) (U : List Update) (e : ℕ) :
    e ∈ (G.applyBatch U).E ↔ batchLastOp U e = 1 ∨ (batchLastOp U e = 0 ∧ e ∈ G.E) := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons u rest ih =>
    change e ∈ ((G.applyUpdate u).applyBatch rest).E ↔ _
    rw [ih, batchLastOp_cons]
    by_cases hr : batchLastOp rest e ≠ 0
    · simp [hr]
    · have hr0 : batchLastOp rest e = 0 := Classical.not_not.mp hr
      simp only [hr0, ne_eq, not_true_eq_false, ↓reduceIte, zero_ne_one, false_or, true_and]
      cases u with
      | insert e' _ _ =>
        by_cases he : e' = e
        · subst he; simp [MGraph.applyUpdate]
        · simp [MGraph.applyUpdate, he, Ne.symm he]
      | delete e' =>
        by_cases he : e' = e
        · subst he; simp [MGraph.applyUpdate]
        · simp [MGraph.applyUpdate, he, Ne.symm he]
      | split _ _ _ _ => simp [MGraph.applyUpdate]

theorem mem_applyBatch_E_of_mem_iff (G : MGraph) (U : List Update) {e : ℕ} (he : e ∈ G.E) :
    e ∈ (G.applyBatch U).E ↔ batchLastOp U e ≠ 2 := by
  rw [mem_applyBatch_E_iff_lastOp]
  have := batchLastOp_le_two U e
  constructor
  · rintro (h | ⟨h, _⟩) <;> omega
  · intro hne
    by_cases h1 : batchLastOp U e = 1
    · exact Or.inl h1
    · exact Or.inr ⟨by omega, he⟩

theorem dsHist_append_nil_state (P : DSParams) (d : DSHist) :
    DSHist.state P ⟨d.G₀, d.Us ++ [[]]⟩ = d.state P := by
  simp [DSHist.state, DSHist.flat, DSHist.q, List.flatten_append]

theorem dsHist_append_nil_bank (P : DSParams) (d : DSHist) :
    DSHist.bank P ⟨d.G₀, d.Us ++ [[]]⟩ = d.bank P := by
  have hfl : (d.Us ++ [[]]).flatten = d.flat := by simp [DSHist.flat]
  have hch : dsBatchCharge P.impl P.mMax P.L (d.G₀.n + P.splitBound) d.G₀
      (d.G₀.applyBatch d.flat) [] = 0 := by simp [dsBatchCharge, MGraph.batchEnc]
  simp only [DSHist.bank, dsBank, DSHist.q]
  rw [dsBankTotal_append, show d.Us.flatten = d.flat from rfl, hch, Nat.add_zero, hfl]

theorem spanUpdAfter_not_mem (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (tasks : List SpanUpdTask) {j : Fin cap}
    (hnot : j.1 ∉ tasks.map SpanUpdTask.slot) :
    spanUpdAfter P S6 mem₀ tasks j = S6 j := by
  induction tasks generalizing S6 with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [spanUpdAfter]
    rw [ih _ hnot.2]
    split_ifs with hs
    · cases S6 ⟨t.slot, hs⟩ with
      | none => rfl
      | some d =>
        have hne : j ≠ ⟨t.slot, hs⟩ := fun h => hnot.1 (congrArg Fin.val h)
        simp [BucketSpannerState.set, Function.update_of_ne hne]
    · rfl

theorem spanUpdAfter_mem (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (tasks : List SpanUpdTask) (hnd : (tasks.map SpanUpdTask.slot).Nodup)
    {t : SpanUpdTask} (ht : t ∈ tasks) {hs : t.slot < cap} {d : DSHist}
    (hS : S6 ⟨t.slot, hs⟩ = some d) :
    spanUpdAfter P S6 mem₀ tasks ⟨t.slot, hs⟩ =
      some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ := by
  induction tasks generalizing S6 with
  | nil => cases ht
  | cons t0 ts ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at ht
    simp only [spanUpdAfter]
    rcases ht with rfl | hmem
    · simp only [hs, ↓reduceDIte, hS]
      rw [spanUpdAfter_not_mem P _ mem₀ ts hnd.1]
      simp [BucketSpannerState.set, Function.update_self]
    · have hne : t.slot ≠ t0.slot := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨t, hmem, rfl⟩)
      refine ih _ hnd.2 hmem ?_
      split_ifs with hs0
      · cases S6 ⟨t0.slot, hs0⟩ with
        | none => exact hS
        | some d0 =>
          have hneF : (⟨t.slot, hs⟩ : Fin cap) ≠ ⟨t0.slot, hs0⟩ := fun h => hne (congrArg Fin.val h)
          simpa [BucketSpannerState.set, Function.update_of_ne hneF] using hS
      · exact hS

/-! ## 3. Shared `CompLSF` stay/back lemmas under `batchLastOp` -/

private lemma compLSFInv_step_local {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) :=
  compLSFBatch_inv hI (U := [u]) ⟨hu, trivial⟩

private lemma batchIsValid_step_rest {cs : CompLSFState} {u : Update} {rest : List Update}
    (hU : cs.G.BatchIsValid (u :: rest)) :
    (compLSFStepSingle cs u).G.BatchIsValid rest := by
  have hG1 : (compLSFStepSingle cs u).G = cs.G.applyUpdate u := rfl
  rw [hG1]; exact hU.2

private lemma comp_edge_stay_step {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) {e : ℕ}
    (he : e ∈ (cs.compSt C).G.E) (hne : u ≠ .delete e) :
    e ∈ ((compLSFStepSingle cs u).compSt C).G.E := by
  have hGeq : ((compLSFStepSingle cs u).compSt C).G =
      (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) := by
    have h := (compLSFBatch_compSt hI (U := [u]) ⟨hu, trivial⟩ hC).2.1
    simpa [compLSFBatch, projCompBatchG] using h
  rw [hGeq]
  cases u with
  | insert e' a b =>
    have hne_i : e ≠ e' := fun h => hu.1 (h ▸ hI.hCE_sub C hC he)
    simp only [projCompUpdateG]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, he, hne_i]
  | delete e' =>
    have hee : e' ≠ e := fun h => hne (h ▸ rfl)
    simp only [projCompUpdateG]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, Ne.symm hee, he]
  | split v v' St Sh =>
    simp only [projCompUpdateG]; split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, he]

lemma comp_edge_stay_of_lastOp_zero {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {C : Finset ℕ} {e : ℕ} :
    ∀ {U : List Update} {cs : CompLSFState}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      C ∈ components cs.G₀ → e ∈ (cs.compSt C).G.E → batchLastOp U e = 0 →
      e ∈ ((compLSFBatch cs U).compSt C).G.E
  | [], _, _, _, _, h, _ => h
  | u :: rest, cs, hI, hU, hC, he, hl => by
    rw [batchLastOp_cons] at hl
    split_ifs at hl with hr
    · omega
    · have hr0 : batchLastOp rest e = 0 := Classical.not_not.mp hr
      have hne : u ≠ .delete e := by
        cases u with
        | insert _ _ _ => intro h; cases h
        | delete e' => intro h; cases h; simp at hl
        | split _ _ _ _ => intro h; cases h
      exact comp_edge_stay_of_lastOp_zero (U := rest) (cs := compLSFStepSingle cs u)
        (compLSFInv_step_local hI hU.1) (batchIsValid_step_rest hU)
        hC (comp_edge_stay_step hI hU.1 hC he hne) hr0

lemma cross_edge_stay_of_lastOp_zero {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {e : ℕ} :
    ∀ {U : List Update} {cs : CompLSFState}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      e ∈ cs.crossEdges → batchLastOp U e = 0 → e ∈ (compLSFBatch cs U).crossEdges
  | [], _, _, _, h, _ => h
  | u :: rest, cs, hI, hU, hcr, hl => by
    rw [batchLastOp_cons] at hl
    split_ifs at hl with hr
    · omega
    · have hr0 : batchLastOp rest e = 0 := Classical.not_not.mp hr
      refine cross_edge_stay_of_lastOp_zero (U := rest) (cs := compLSFStepSingle cs u)
        (compLSFInv_step_local hI hU.1) (batchIsValid_step_rest hU) ?_ hr0
      cases u with
      | insert _ _ _ =>
        simp only [compLSFStepSingle]; split_ifs <;> [exact hcr; exact Finset.mem_insert_of_mem hcr]
      | delete e' =>
        have hee : e' ≠ e := by intro h; subst h; simp at hl
        simpa [compLSFStepSingle, Ne.symm hee] using hcr
      | split _ _ _ _ => simpa [compLSFStepSingle] using hcr

private lemma cross_edge_back_of_lastOp_zero {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {e : ℕ} :
    ∀ {U : List Update} {cs : CompLSFState}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      e ∈ (compLSFBatch cs U).crossEdges → batchLastOp U e = 0 → e ∈ cs.crossEdges
  | [], _, _, _, h, _ => h
  | u :: rest, cs, hI, hU, hcr, hl => by
    rw [batchLastOp_cons] at hl
    split_ifs at hl with hr
    · omega
    · have hr0 : batchLastOp rest e = 0 := Classical.not_not.mp hr
      have h1 := cross_edge_back_of_lastOp_zero (U := rest) (cs := compLSFStepSingle cs u)
        (compLSFInv_step_local hI hU.1) (batchIsValid_step_rest hU) hcr hr0
      cases u with
      | insert e' _ _ =>
        have hee : e' ≠ e := by intro h; subst h; simp at hl
        simp only [compLSFStepSingle] at h1
        split_ifs at h1
        · exact h1
        · exact (Finset.mem_insert.mp h1).resolve_left (Ne.symm hee)
      | delete _ =>
        simp only [compLSFStepSingle] at h1
        exact Finset.erase_subset _ _ h1
      | split _ _ _ _ => simpa [compLSFStepSingle] using h1

lemma lastOp_zero_of_mem_not_del {e : ℕ} :
    ∀ {U : List Update} {G : MGraph}, G.BatchIsValid U → e ∈ G.E → e ∉ batchDeletes U →
      batchLastOp U e = 0
  | [], _, _, _, _ => rfl
  | u :: rest, G, hU, he, hnd => by
    have hne_d : u ≠ .delete e := fun h => hnd ((mem_batchDeletes_iff _ _).mpr ⟨u, List.mem_cons_self, h⟩)
    have hnd_r : e ∉ batchDeletes rest := fun h => by
      obtain ⟨u0, hu0, rfl⟩ := (mem_batchDeletes_iff _ _).mp h
      exact hnd ((mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_cons_of_mem _ hu0, rfl⟩)
    have hne_i : ∀ a b, u ≠ .insert e a b := fun a b h => by rw [h] at hU; exact hU.1.1 he
    have he1 : e ∈ (G.applyUpdate u).E := by
      cases u with
      | insert _ _ _ => exact Finset.mem_insert_of_mem he
      | delete e' => exact Finset.mem_erase.mpr ⟨fun h => hne_d (h ▸ rfl), he⟩
      | split _ _ _ _ => exact he
    have hr := lastOp_zero_of_mem_not_del hU.2 he1 hnd_r
    simp only [batchLastOp, hr, ne_eq, not_true_eq_false, ↓reduceIte]
    cases u with
    | insert e' a b =>
      have : e' ≠ e := fun h => hne_i a b (h ▸ rfl); simp [this]
    | delete e' =>
      have : e' ≠ e := fun h => hne_d (h ▸ rfl); simp [this]
    | split _ _ _ _ => rfl

lemma comp_edge_disj_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C₁ C₂ : Finset ℕ}
    (hC₁ : C₁ ∈ components cs.G₀) (hC₂ : C₂ ∈ components cs.G₀) (hne : C₁ ≠ C₂)
    {e : ℕ} (h1 : e ∈ (cs.compSt C₁).G.E) (h2 : e ∈ (cs.compSt C₂).G.E) : False := by
  have ht1 := ((hI.hCompLSF C₁ hC₁).1.hG_val e h1).1
  have ht2 := ((hI.hCompLSF C₂ hC₂).1.hG_val e h2).1
  rw [(hI.compEnds_eq hC₁ h1).1] at ht1
  rw [(hI.compEnds_eq hC₂ h2).1] at ht2
  exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C₂ hC₂ hne) ht1 ht2

private lemma mem_RF_F_E_iff (cs : CompLSFState) (e : ℕ) :
    e ∈ cs.RF.F.E ↔ ∃ C ∈ components cs.G₀, e ∈ (cs.compSt C).RF.F.E := by
  change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) ↔ _
  exact Finset.mem_biUnion

private lemma not_mem_RF_E_of_lastOp_one {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ {cs : CompLSFState} {U : List Update}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      ∀ {e : ℕ}, batchLastOp U e = 1 → e ∉ (compLSFBatch cs U).RF.F.E
  | _, [], _, _, _, h => by simp at h
  | cs, u :: rest, hI, hU, e, h => by
    have hI1 := compLSFInv_step_local hI hU.1
    have hU1 := batchIsValid_step_rest hU
    rw [batchLastOp_cons] at h
    split_ifs at h with hr
    · exact not_mem_RF_E_of_lastOp_one hI1 hU1 h
    · cases u with
      | insert e' _ _ =>
        by_cases hee : e' = e
        · subst hee; intro hmem
          have h1 := (compLSFBatch_decremental hI1 hU1).1 hmem
          have h0 := (compLSFBatch_decremental hI (U := [.insert e' _ _]) ⟨hU.1, trivial⟩).1 h1
          exact hU.1.1 ((compLSF_RF_isRSF hI).2.2.2.2.2.1 h0)
        · simp [hee] at h
      | delete e' => by_cases hee : e' = e <;> simp [hee] at h
      | split _ _ _ _ => simp at h

private lemma mem_insU_of_lastOp_one {e : ℕ} :
    ∀ {U : List Update}, batchLastOp U e = 1 →
      e ∈ (U.filterMap fun | .insert e' _ _ => some e' | _ => none).toFinset
  | [], h => by simp at h
  | u :: rest, h => by
    rw [batchLastOp_cons] at h
    split_ifs at h with hr
    · have ih := List.mem_toFinset.mp (mem_insU_of_lastOp_one h)
      obtain ⟨u0, hu0, hs⟩ := List.mem_filterMap.mp ih
      exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨u0, List.mem_cons_of_mem _ hu0, hs⟩)
    · cases u with
      | insert e' a b =>
        by_cases hee : e' = e
        · subst hee
          exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.insert e' a b, List.mem_cons_self, rfl⟩)
        · simp [hee] at h
      | delete e' => by_cases hee : e' = e <;> simp [hee] at h
      | split _ _ _ _ => simp at h

private lemma mem_touched_or_cross_of_lastOp_one {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    {e : ℕ} (h1 : batchLastOp U e = 1) :
    e ∈ (compLSFBatch cs U).crossEdges ∨
      ∃ C ∈ touchedCompsBatch cs U, e ∈ ((compLSFBatch cs U).compSt C).G.E := by
  have hI' := compLSFBatch_inv hI hU
  have heG' : e ∈ (compLSFBatch cs U).G.E := by
    rw [compLSFBatch_G, mem_applyBatch_E_iff_lastOp]; exact Or.inl h1
  by_cases hcr : e ∈ (compLSFBatch cs U).crossEdges
  · exact Or.inl hcr
  · right
    obtain ⟨C, hC, heC⟩ := hI'.hEdge_cover e heG' hcr
    have hC0 : C ∈ components cs.G₀ := by rwa [compLSFBatch_G₀] at hC
    refine ⟨C, ?_, heC⟩
    by_contra hnt
    rw [(compLSFBatch_untouched hI hU hC0 hnt).2] at heC
    have heG0 : e ∈ cs.G.E := hI.hCE_sub C hC0 heC
    have hdel : Update.delete e ∈ U := by
      by_contra hnd
      have hz := lastOp_zero_of_mem_not_del hU heG0 (fun hd => by
        obtain ⟨u0, hu0, rfl⟩ := (mem_batchDeletes_iff _ _).mp hd; exact hnd hu0)
      omega
    have hnil : projCompBatchG cs.G (cs.compSt C).G U = [] := (compLSFBatch_untouched hI hU hC0 hnt).1
    have hne : ∀ (U' : List Update) (cs0 : CompLSFState),
        CompLSFInv C_lsst ℓ₀ cs0 → cs0.G.BatchIsValid U' → C ∈ components cs0.G₀ →
        e ∈ (cs0.compSt C).G.E → Update.delete e ∈ U' →
        projCompBatchG cs0.G (cs0.compSt C).G U' ≠ [] := by
      intro U'; induction U' with
      | nil => intro _ _ _ _ _ h; cases h
      | cons u' r' ih' =>
        intro cs0 hI0 hU0 hC0' he0 hm0
        simp only [projCompBatchG]
        rcases List.mem_cons.mp hm0 with rfl | hm1
        · simp [projCompUpdateG, he0]
        · intro hemp
          obtain ⟨hp1, hp2⟩ := List.append_eq_nil_iff.mp hemp
          have hI1 := compLSFInv_step_local hI0 hU0.1
          have hG1 : (compLSFStepSingle cs0 u').G = cs0.G.applyUpdate u' := rfl
          have hCG1 : ((compLSFStepSingle cs0 u').compSt C).G =
              (cs0.compSt C).G.applyBatch (projCompUpdateG cs0.G (cs0.compSt C).G u') := by
            have h := (compLSFBatch_compSt hI0 (U := [u']) ⟨hU0.1, trivial⟩ hC0').2.1
            simpa [compLSFBatch, projCompBatchG] using h
          have he1 : e ∈ ((compLSFStepSingle cs0 u').compSt C).G.E := by rw [hCG1, hp1]; exact he0
          have hp2' : projCompBatchG (compLSFStepSingle cs0 u').G ((compLSFStepSingle cs0 u').compSt C).G r' = [] := by
            rw [hG1, hCG1]; exact hp2
          exact ih' _ hI1 (batchIsValid_step_rest hU0) hC0' he1 hm1 hp2'
    exact hne U cs hI hU hC0 heC hdel hnil

/-! ## 4. Exact `O(1)` decision test for `targetE'` and candidate supersets -/

/-- **Exact `O(1)` decision test for `e ∈ info.state.S_cur.E` (`targetE'`)**. -/
theorem mem_targetE'_iff_dec {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {P : DSParams} {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hMod : RestartScurModelInv tr) (hMod' : RestartScurModelInv
      (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG' : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn p).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges)
    (hInactiveBkts : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ e ∈ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E,
        ∃ b ∈ tr.activeBuckets C, e ∈ (tr.bun (C, b)).edges)
    (hBunEdges : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges =
        (tr.bun p).edges \ batchDeletes U)
    (e : ℕ) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let tr' := info.state
    (∀ p ∈ activePairs tr', e ∈ (tr'.bun p).edges → (e ∈ tr'.S_cur.E ↔ e ∈ (tr'.dyn p).H.E)) ∧
    ((∀ p ∈ activePairs tr', e ∉ (tr'.bun p).edges) →
      (e ∈ tr'.S_cur.E ↔
        batchLastOp U e = 1 ∨
          (batchLastOp U e = 0 ∧ (e ∈ tr.S_cur.E ∨ e ∈ tr.cs.RF.F.E \ tr'.cs.RF.F.E)))) := by
  classical
  intro sp info tr'
  have hI' := compLSFBatch_inv hI hU
  have hG0' : tr'.cs.G₀ = tr.cs.G₀ := compLSFBatch_G₀ tr.cs U
  constructor
  · intro p hp heB
    have ⟨hC, hb⟩ := mem_activePairs.mp hp
    have hsc := scur_inter_dynG_eq_dynH hI' hMod' hBD' hC hb (hDynG' p hp)
    have heG : e ∈ (tr'.dyn p).G.E := (hDynG' p hp) ▸ heB
    exact ⟨fun hS => hsc ▸ Finset.mem_inter.mpr ⟨hS, heG⟩,
      fun hH => (Finset.mem_inter.mp (hsc.symm ▸ hH)).1⟩
  · intro hNotBun
    have hTouchedSub : touchedCompsBatch tr.cs U ⊆ tr'.activeComps := fun C hC => by
      change C ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps)
      by_cases ha : C ∈ tr.activeComps
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hC, ha⟩)
    have hSE_simp : e ∈ tr'.S_cur.E ↔
        (∃ C ∈ tr'.activeComps, e ∈ (tr'.cs.compSt C).G.E ∧ e ∉ (tr'.cs.compSt C).RF.F.E) ∨
          e ∈ tr'.cs.crossEdges := by
      rw [hMod'.2.2.1]
      simp only [Finset.mem_union, Finset.mem_biUnion, BundleTreeState.extraEdges, Finset.mem_sdiff]
      constructor
      · rintro ((⟨C, hC, b, hb, heH⟩ | ⟨C, hC, ⟨heC, hnf⟩, _⟩) | hcr)
        · exact absurd ((hMod'.2.2.2.2 C hC b hb).2.2.2 heH)
            (hNotBun (C, b) (mem_activePairs.mpr ⟨hC, hb⟩))
        · exact Or.inl ⟨C, hC, heC, hnf⟩
        · exact Or.inr hcr
      · rintro (⟨C, hC, heC, hnf⟩ | hcr)
        · left; right; refine ⟨C, hC, ⟨heC, hnf⟩, fun hbi => ?_⟩
          obtain ⟨b, hb, heB⟩ := hbi
          exact hNotBun (C, b) (mem_activePairs.mpr ⟨hC, hb⟩) heB
        · exact Or.inr hcr
    rw [hSE_simp]
    have hcs'G : tr'.cs.G = tr.cs.G.applyBatch U := compLSFBatch_G tr.cs U
    have hNotDel_of_last0 : batchLastOp U e = 0 → e ∉ batchDeletes U := by
      intro hl0 hdel
      obtain ⟨u0, hu0, rfl⟩ := (mem_batchDeletes_iff _ _).mp hdel
      clear * - hl0 hu0
      induction U with
      | nil => cases hu0
      | cons u r ih =>
        rw [batchLastOp_cons] at hl0
        split_ifs at hl0 with hr
        · omega
        · have hr0 : batchLastOp r e = 0 := Classical.not_not.mp hr
          rcases List.mem_cons.mp hu0 with rfl | hu1
          · simp at hl0
          · exact ih hr0 hu1
    constructor
    · rintro (⟨C, hC, heC, hnf⟩ | hcr)
      · have hC0' : C ∈ components tr'.cs.G₀ := hMod'.1 hC
        have hC0 : C ∈ components tr.cs.G₀ := hG0' ▸ hC0'
        have heG' : e ∈ tr'.cs.G.E := hI'.hCE_sub C hC0' heC
        rw [hcs'G, mem_applyBatch_E_iff_lastOp] at heG'
        rcases heG' with h1 | ⟨h0, heG0⟩
        · exact Or.inl h1
        · right; refine ⟨h0, ?_⟩
          by_cases hF0 : e ∈ tr.cs.RF.F.E
          · right; refine Finset.mem_sdiff.mpr ⟨hF0, fun hF' => hnf ?_⟩
            obtain ⟨C', hC', heF'⟩ := (mem_RF_F_E_iff tr'.cs e).mp hF'
            by_cases hCC : C' = C
            · rwa [hCC] at heF'
            · exact absurd ((hI'.hCompLSF C' hC').1.hF_sub_G.2.1 heF')
                (fun h => comp_edge_disj_inv hI' hC0' hC' (Ne.symm hCC) heC h)
          · left
            have hnc' : e ∉ tr'.cs.crossEdges := hI'.hCompE_notCross C hC0' e heC
            have hnc0 : e ∉ tr.cs.crossEdges := fun hc => hnc' (cross_edge_stay_of_lastOp_zero hI hU hc h0)
            have heC0 : e ∈ (tr.cs.compSt C).G.E := by
              obtain ⟨C', hC', heC'⟩ := hI.hEdge_cover e heG0 hnc0
              by_cases hCC : C' = C
              · rwa [hCC] at heC'
              · exact absurd (comp_edge_stay_of_lastOp_zero hI hU hC' heC' h0)
                  (fun h => comp_edge_disj_inv hI' hC0' (hG0'.symm ▸ hC') (Ne.symm hCC) heC h)
            have hnf0 : e ∉ (tr.cs.compSt C).RF.F.E := fun h =>
              hF0 ((mem_RF_F_E_iff tr.cs e).mpr ⟨C, hC0, h⟩)
            by_cases hCact : C ∈ tr.activeComps
            · rw [hMod.2.2.1]
              refine Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨C, hCact,
                  Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heC0, hnf0⟩, fun hbi => ?_⟩⟩))
              obtain ⟨b, hb, heB0⟩ := Finset.mem_biUnion.mp hbi
              have hp' : (C, b) ∈ activePairs tr' := mem_activePairs.mpr ⟨hC, hb⟩
              exact hNotBun (C, b) hp'
                (by rw [hBunEdges (C, b) hp']; exact Finset.mem_sdiff.mpr ⟨heB0, hNotDel_of_last0 h0⟩)
            · exfalso
              obtain ⟨b, hb, heB0⟩ := hInactiveBkts C hC0 hCact e (Finset.mem_sdiff.mpr ⟨heC0, hnf0⟩)
              have hp' : (C, b) ∈ activePairs tr' := mem_activePairs.mpr ⟨hC, hb⟩
              exact hNotBun (C, b) hp'
                (by rw [hBunEdges (C, b) hp']; exact Finset.mem_sdiff.mpr ⟨heB0, hNotDel_of_last0 h0⟩)
      · have heG' : e ∈ tr'.cs.G.E := hI'.hIns_sub (hI'.hCross_sub hcr)
        rw [hcs'G, mem_applyBatch_E_iff_lastOp] at heG'
        rcases heG' with h1 | ⟨h0, _⟩
        · exact Or.inl h1
        · right; refine ⟨h0, Or.inl ?_⟩
          rw [hMod.2.2.1]; exact Finset.mem_union_right _ (cross_edge_back_of_lastOp_zero hI hU hcr h0)
    · rintro (h1 | ⟨h0, hS0 | hFdel⟩)
      · rcases mem_touched_or_cross_of_lastOp_one hI hU h1 with hcr | ⟨C, hCt, heC⟩
        · exact Or.inr hcr
        · left; refine ⟨C, hTouchedSub hCt, heC, fun hF =>
            not_mem_RF_E_of_lastOp_one hI hU h1
              ((mem_RF_F_E_iff tr'.cs e).mpr ⟨C, hMod'.1 (hTouchedSub hCt), hF⟩)⟩
      · have hnf' : e ∉ tr'.cs.RF.F.E := fun h =>
          (Finset.mem_sdiff.mp (hMod.2.2.2.1.2.1 hS0)).2 ((compLSFBatch_decremental hI hU).1 h)
        rw [hMod.2.2.1] at hS0
        simp only [Finset.mem_union, Finset.mem_biUnion, BundleTreeState.extraEdges, Finset.mem_sdiff] at hS0
        rcases hS0 with (⟨C, hC, b, hb, heH⟩ | ⟨C, hC, ⟨heC, _⟩, _⟩) | hcr0
        · left
          have heC := (hMod.2.2.2.2 C hC b hb).2.1 ((hMod.2.2.2.2 C hC b hb).2.2.2 heH)
          exact ⟨C, Finset.mem_union_left _ hC, comp_edge_stay_of_lastOp_zero hI hU (hMod.1 hC) heC h0,
            fun hF => hnf' ((mem_RF_F_E_iff tr'.cs e).mpr ⟨C, hG0'.symm ▸ hMod.1 hC, hF⟩)⟩
        · left
          exact ⟨C, Finset.mem_union_left _ hC, comp_edge_stay_of_lastOp_zero hI hU (hMod.1 hC) heC h0,
            fun hF => hnf' ((mem_RF_F_E_iff tr'.cs e).mpr ⟨C, hG0'.symm ▸ hMod.1 hC, hF⟩)⟩
        · exact Or.inr (cross_edge_stay_of_lastOp_zero hI hU hcr0 h0)
      · obtain ⟨hF0, hnf'⟩ := Finset.mem_sdiff.mp hFdel
        obtain ⟨C, hC, heF0⟩ := (mem_RF_F_E_iff tr.cs e).mp hF0
        have heC0 := (hI.hCompLSF C hC).1.hF_sub_G.2.1 heF0
        have hCt : C ∈ touchedCompsBatch tr.cs U := by
          by_contra hnt
          exact hnf' ((mem_RF_F_E_iff tr'.cs e).mpr
            ⟨C, hG0'.symm ▸ hC, (compLSFBatch_untouched hI hU hC hnt).2.symm ▸ heF0⟩)
        left
        exact ⟨C, hTouchedSub hCt, comp_edge_stay_of_lastOp_zero hI hU hC heC0 h0,
          fun hF => hnf' ((mem_RF_F_E_iff tr'.cs e).mpr ⟨C, hG0'.symm ▸ hC, hF⟩)⟩

lemma sdiff_subset_uhDelFinset (H : MGraph) (UH : List Update) :
    H.E \ (H.applyBatch UH).E ⊆ uhDelFinset UH := by
  induction UH generalizing H with
  | nil => simp [MGraph.applyBatch]
  | cons u rest ih =>
    intro e he; obtain ⟨heH, hne⟩ := Finset.mem_sdiff.mp he
    simp only [MGraph.applyBatch] at hne
    by_cases he1 : e ∈ (H.applyUpdate u).E
    · have := ih (H.applyUpdate u) (Finset.mem_sdiff.mpr ⟨he1, hne⟩)
      cases u <;> simp_all [uhDelFinset]
    · cases u with
      | insert _ _ _ => exact absurd (Finset.mem_insert_of_mem heH) he1
      | split _ _ _ _ => exact absurd heH he1
      | delete e' =>
        have hee : e' = e := by by_contra h; exact he1 (Finset.mem_erase.mpr ⟨Ne.symm h, heH⟩)
        subst hee; simp [uhDelFinset]

lemma sdiff_subset_uhInsFinset (H : MGraph) (UH : List Update) :
    (H.applyBatch UH).E \ H.E ⊆ uhInsFinset UH := by
  induction UH generalizing H with
  | nil => simp [MGraph.applyBatch]
  | cons u rest ih =>
    intro e he; obtain ⟨heR, hne⟩ := Finset.mem_sdiff.mp he
    simp only [MGraph.applyBatch] at heR
    by_cases he1 : e ∈ (H.applyUpdate u).E
    · cases u with
      | delete _ => exact absurd (Finset.mem_of_mem_erase he1) hne
      | split _ _ _ _ => exact absurd he1 hne
      | insert e' _ _ =>
        have hee : e' = e := ((Finset.mem_insert.mp he1).resolve_right hne).symm
        subst hee; simp [uhInsFinset]
    · have := ih (H.applyUpdate u) (Finset.mem_sdiff.mpr ⟨heR, he1⟩)
      cases u <;> simp_all [uhInsFinset]

/-- **`stepBundleTree_reembSet` exact decomposition**: newly active bundle edges, updated spanner
`updateReembSet`, and `outDelSet`. -/
theorem stepBundleTree_reembSet_eq_sup {depth : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sp tr U ord ord'
    stepBundleTree_reembSet sp tr U ord ord' =
      (info.newlyActive.biUnion fun C => (tr.activeBuckets C).biUnion fun b => (tr.bun (C, b)).edges) ∪
      (info.state.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
        DynSpanner.updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (sp tr.m₀)) ∪
      outDelSet sp tr U ord ord' := by
  classical
  intro info
  have hDelEq : (info.U_S.filterMap fun u => match u with | .delete e => some e | _ => none).toFinset =
      outDelSet sp tr U ord ord' := by
    ext e
    simp only [List.mem_toFinset, List.mem_filterMap]
    rw [stepBundleTree_U_S_split, outPrefixBatch, outDelList, outInsBatch]
    constructor
    · rintro ⟨u, hu, hsome⟩
      cases u with
      | insert _ _ _ => simp at hsome
      | split _ _ _ _ => simp at hsome
      | delete e' =>
        simp only [Option.some.injEq] at hsome; subst hsome
        rcases List.mem_append.mp hu with hpref | hins
        · rcases List.mem_append.mp hpref with hdel | hspl
          · obtain ⟨e0, he0, heq⟩ := List.mem_map.mp hdel; cases heq
            exact (Finset.mem_sort (· ≤ ·)).mp he0
          · exfalso
            have hno : ∀ P : List Update, Update.delete e' ∉ restrictSplits (outKeep sp tr U ord ord') P := by
              intro P; induction P with
              | nil => simp [restrictSplits]
              | cons u0 r ih => cases u0 <;> simp [restrictSplits, ih]
            exact hno _ hspl
        · obtain ⟨_, _, heq⟩ := List.mem_map.mp hins; cases heq
    · intro he
      exact ⟨.delete e, List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨e, (Finset.mem_sort (· ≤ ·)).mpr he, rfl⟩)), rfl⟩
  unfold stepBundleTree_reembSet
  exact congrArg (_ ∪ ·) hDelEq

/-- **`outDelSet` superset coverage**. -/
theorem outDelSet_subset_sup {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {P : DSParams}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hMod' : RestartScurModelInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG' : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn p).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges)
    (hInactiveBkts : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ e ∈ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E,
        ∃ b ∈ tr.activeBuckets C, e ∈ (tr.bun (C, b)).edges)
    (hBunEdges : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges =
        (tr.bun p).edges \ batchDeletes U)
    (hHApply : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      (tr.dyn p).H.applyBatch ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').stepOut p).UH =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn p).H)
    (hDynG : ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    outDelSet sp tr U ord ord' ⊆
      batchDeletes U ∪ info.D_total ∪
        (activePairs info.state).biUnion fun p => uhDelFinset (info.stepOut p).UH := by
  intro sp info e he
  rw [mem_outDelSet_iff] at he
  obtain ⟨heS, hnS' | hdel | hD⟩ := he
  · by_cases hdelU : e ∈ batchDeletes U
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hdelU)
    · have hdec := mem_targetE'_iff_dec (P := P) hI hU hMod hMod' hBD' hDynG' hInactiveBkts hBunEdges e
      have heG0 : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp (hMod.2.2.2.1.2.1 heS)).1
      have hl0 : batchLastOp U e = 0 := lastOp_zero_of_mem_not_del hU heG0 hdelU
      by_cases hInB : ∃ p ∈ activePairs info.state, e ∈ (info.state.bun p).edges
      · obtain ⟨p, hp, heBp⟩ := hInB
        have hnH' : e ∉ (info.state.dyn p).H.E := fun h => hnS' ((hdec.1 p hp heBp).mpr h)
        by_cases hp0 : p ∈ activePairs tr
        · obtain ⟨hC0, hb0⟩ := mem_activePairs.mp hp0
          have hsc0 := scur_inter_dynG_eq_dynH hI hMod hBD hC0 hb0 (hDynG p hp0)
          have heG0p : e ∈ (tr.dyn p).G.E :=
            (hDynG p hp0).symm ▸ (Finset.mem_sdiff.mp ((hBunEdges p hp) ▸ heBp)).1
          have heH0 : e ∈ (tr.dyn p).H.E := hsc0 ▸ Finset.mem_inter.mpr ⟨heS, heG0p⟩
          apply Finset.mem_union_right
          refine Finset.mem_biUnion.mpr ⟨p, hp, sdiff_subset_uhDelFinset (tr.dyn p).H (info.stepOut p).UH ?_⟩
          rw [hHApply p hp]; exact Finset.mem_sdiff.mpr ⟨heH0, hnH'⟩
        · exfalso
          have hI' := compLSFBatch_inv hI hU
          have hG0' : info.state.cs.G₀ = tr.cs.G₀ := compLSFBatch_G₀ tr.cs U
          have hC0' : p.1 ∈ components info.state.cs.G₀ := hMod'.1 (mem_activePairs.mp hp).1
          have hnotAct : p.1 ∉ tr.activeComps := fun ha => hp0 (mem_activePairs.mpr ⟨ha, (mem_activePairs.mp hp).2⟩)
          have heCp := (hMod'.2.2.2.2 p.1 (mem_activePairs.mp hp).1 p.2 (mem_activePairs.mp hp).2).2.1 heBp
          have hnc' : e ∉ info.state.cs.crossEdges := fun hc => Finset.disjoint_left.mp (hBD'.2 p hp) heBp hc
          rw [hMod.2.2.1] at heS
          simp only [Finset.mem_union, Finset.mem_biUnion, BundleTreeState.extraEdges, Finset.mem_sdiff] at heS
          rcases heS with (⟨C', hC', b', hb', heH'⟩ | ⟨C', hC', ⟨heC0, _⟩, _⟩) | hcr0
          · exact comp_edge_disj_inv hI' (hG0'.symm ▸ hMod.1 hC') hC0' (fun h => hnotAct (h ▸ hC'))
              (comp_edge_stay_of_lastOp_zero hI hU (hMod.1 hC')
                ((hMod.2.2.2.2 C' hC' b' hb').2.1 ((hMod.2.2.2.2 C' hC' b' hb').2.2.2 heH')) hl0) heCp
          · exact comp_edge_disj_inv hI' (hG0'.symm ▸ hMod.1 hC') hC0' (fun h => hnotAct (h ▸ hC'))
              (comp_edge_stay_of_lastOp_zero hI hU (hMod.1 hC') heC0 hl0) heCp
          · exact hnc' (cross_edge_stay_of_lastOp_zero hI hU hcr0 hl0)
      · have hnb : ∀ p ∈ activePairs info.state, e ∉ (info.state.bun p).edges := fun p hp h => hInB ⟨p, hp, h⟩
        exact absurd ((hdec.2 hnb).mpr (Or.inr ⟨hl0, Or.inl heS⟩)) hnS'
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hdel)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hD)

/-- **`outInsSet` superset coverage**. -/
theorem outInsSet_subset_sup {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {P : DSParams}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hMod' : RestartScurModelInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG' : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn p).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges)
    (hInactiveBkts : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ e ∈ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E,
        ∃ b ∈ tr.activeBuckets C, e ∈ (tr.bun (C, b)).edges)
    (hBunEdges : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges =
        (tr.bun p).edges \ batchDeletes U)
    (hHApply : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      (tr.dyn p).H.applyBatch ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').stepOut p).UH =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn p).H)
    (hDynG : ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let insU := (U.filterMap fun | .insert e _ _ => some e | _ => none).toFinset
    let lazyE := info.newlyActive.biUnion fun C => (tr.activeBuckets C).biUnion fun b => (tr.bun (C, b)).edges
    outInsSet sp tr U ord ord' ⊆
      batchDeletes U ∪ insU ∪ (tr.cs.RF.F.E \ info.state.cs.RF.F.E) ∪ info.D_total ∪ lazyE ∪
        (activePairs info.state).biUnion fun p => uhInsFinset (info.stepOut p).UH := by
  intro sp info insU lazyE e he
  rw [mem_outInsSet_iff] at he
  obtain ⟨heS', hnS | hdel | hD⟩ := he
  · have hdec := mem_targetE'_iff_dec (P := P) hI hU hMod hMod' hBD' hDynG' hInactiveBkts hBunEdges e
    by_cases hInB : ∃ p ∈ activePairs info.state, e ∈ (info.state.bun p).edges
    · obtain ⟨p, hp, heBp⟩ := hInB
      have heH' : e ∈ (info.state.dyn p).H.E := (hdec.1 p hp heBp).mp heS'
      by_cases hp0 : p ∈ activePairs tr
      · obtain ⟨hC0, hb0⟩ := mem_activePairs.mp hp0
        have hnH0 : e ∉ (tr.dyn p).H.E := fun hH0 =>
          hnS (Finset.mem_inter.mp ((scur_inter_dynG_eq_dynH hI hMod hBD hC0 hb0 (hDynG p hp0)).symm ▸ hH0)).1
        apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨p, hp, sdiff_subset_uhInsFinset (tr.dyn p).H (info.stepOut p).UH ?_⟩
        rw [hHApply p hp]; exact Finset.mem_sdiff.mpr ⟨heH', hnH0⟩
      · apply Finset.mem_union_left; apply Finset.mem_union_right
        have heB0 : e ∈ (tr.bun p).edges := (Finset.mem_sdiff.mp ((hBunEdges p hp) ▸ heBp)).1
        obtain ⟨hC', hb⟩ := mem_activePairs.mp hp
        have hCnew : p.1 ∈ info.newlyActive :=
          (Finset.mem_union.mp hC').resolve_left fun ha => hp0 (mem_activePairs.mpr ⟨ha, hb⟩)
        exact Finset.mem_biUnion.mpr ⟨p.1, hCnew, Finset.mem_biUnion.mpr ⟨p.2, hb, heB0⟩⟩
    · have hnb : ∀ p ∈ activePairs info.state, e ∉ (info.state.bun p).edges := fun p hp h => hInB ⟨p, hp, h⟩
      rcases (hdec.2 hnb).mp heS' with h1 | ⟨_, hS0 | hFdel⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_insU_of_lastOp_one h1)))))
      · exact absurd hS0 hnS
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ hFdel)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hdel))))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hD))

end

end MinCostFlow.SparseCore.Program
