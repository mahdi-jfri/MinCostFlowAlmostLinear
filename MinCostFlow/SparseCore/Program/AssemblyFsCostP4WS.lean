module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Front
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4New
public import MinCostFlow.SparseCore.Program.AssemblyFsCostSpanCand

import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4TaskDefs
import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanProof
import MinCostFlow.SparseCore.Program.AssemblyFirstStepGroupsModel
import MinCostFlow.SparseCore.BundleSpanCharge
import Mathlib.Tactic

/-!
# Pure workspace, copy-edge, new-slot, and LSF-deletion bounds for Phase 4 (`AssemblyFsCostP4WS`)

Supplies the model-level inequalities consumed by Phase 4's cost proof:

* `p4TaskWS_delSup_sub` / `p4TaskWS_insSup_sub` and `p4WVStep_delSup_insSup_card_le`: tracks the
  exact growth of `delSup.toFinset.card` and `insSup.toFinset.card` across `p4TaskWS` and `p4NewStep`.
* `p4CopyEdgeCost_le`: `p4CopyEdgeCost P (S6.set ...) s d' e ≤ 584 * |piTotal d' e| + 207 * P.L + 676`
  for every `e ∈ p4CopyCand P d U`.
* `p4NewWork_le`: bounds `p4NewWork P S6 s d' + 20` in terms of `d'.G₀.m`, `P.L`, and off-spanner walks.
* `fDel_length_le`: `c.fDel.length ≤ U.length + (canonSplitList tr.cs U).length` from `c.Exact`.
* `m_add_one_le_spanInitBound`, `batchEnc_pos_of_ne_nil`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

public section

/-! ## 1. `pushDedup`, `p4TaskWS`, and `p4StepNew` candidate-list growth -/

private lemma pushDedup_toFinset_sub (L : List ℕ) (e : ℕ) :
    (pushDedup L e).toFinset ⊆ insert e L.toFinset := by
  intro x hx
  unfold pushDedup at hx
  split_ifs at hx
  · exact Finset.mem_insert_of_mem hx
  · simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty, or_false] at hx
    rcases hx with h | rfl
    · exact Finset.mem_insert_of_mem h
    · exact Finset.mem_insert_self _ _

private lemma p4StepEdge_delSup_sub (GE HE : Finset ℕ) (fD fDel fIns fCopy : Bool)
    (S : Phase4WS) (e : ℕ) :
    (p4StepEdge GE HE fD fDel fIns fCopy S e).delSup.toFinset ⊆
      if fDel then insert e S.delSup.toFinset else S.delSup.toFinset := by
  unfold p4StepEdge
  cases fCopy <;> cases fIns <;> cases fDel <;> cases fD
  all_goals simp only [p4Mark, pushCopy, Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact Finset.Subset.rfl
    | (split_ifs <;> exact Finset.Subset.rfl)
    | exact pushDedup_toFinset_sub _ _
    | (split_ifs <;> exact pushDedup_toFinset_sub _ _)

private lemma p4StepEdge_insSup_sub (GE HE : Finset ℕ) (fD fDel fIns fCopy : Bool)
    (S : Phase4WS) (e : ℕ) :
    (p4StepEdge GE HE fD fDel fIns fCopy S e).insSup.toFinset ⊆
      if fIns then insert e S.insSup.toFinset else S.insSup.toFinset := by
  unfold p4StepEdge
  cases fCopy <;> cases fIns <;> cases fDel <;> cases fD
  all_goals simp only [p4Mark, pushCopy, Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact Finset.Subset.rfl
    | (split_ifs <;> exact Finset.Subset.rfl)
    | exact pushDedup_toFinset_sub _ _
    | (split_ifs <;> exact pushDedup_toFinset_sub _ _)

private lemma foldl_p4StepUH_sub (GE HE OS : Finset ℕ) (isOld : Bool) :
    ∀ (UH : List Update) (S : Phase4WS),
      (UH.foldl (p4StepUH GE HE OS isOld) S).delSup.toFinset ⊆
        S.delSup.toFinset ∪ uhDelFinset UH ∧
      (UH.foldl (p4StepUH GE HE OS isOld) S).insSup.toFinset ⊆
        S.insSup.toFinset ∪ uhInsFinset UH
  | [], S => ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  | u :: rest, S => by
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4StepUH_sub GE HE OS isOld rest (p4StepUH GE HE OS isOld S u)
      cases u with
      | insert e a b =>
        have h1 : (p4StepUH GE HE OS isOld S (.insert e a b)).delSup.toFinset ⊆ S.delSup.toFinset :=
          p4StepEdge_delSup_sub GE HE false false true false S e
        have h2 : (p4StepUH GE HE OS isOld S (.insert e a b)).insSup.toFinset ⊆
            insert e S.insSup.toFinset :=
          p4StepEdge_insSup_sub GE HE false false true false S e
        refine ⟨ih1.trans (Finset.union_subset_union h1 (by simp [uhDelFinset])), ?_⟩
        intro x hx
        have h' := ih2 hx
        rcases Finset.mem_union.mp h' with h' | h'
        · rcases Finset.mem_insert.mp (h2 h') with rfl | hs
          · exact Finset.mem_union_right _ (by simp [uhInsFinset])
          · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by
            simp only [uhInsFinset, List.filterMap_cons, List.toFinset_cons, Finset.mem_insert]
            exact Or.inr h')
      | delete e =>
        have h1 : (p4StepUH GE HE OS isOld S (.delete e)).delSup.toFinset ⊆
            insert e S.delSup.toFinset :=
          p4StepEdge_delSup_sub GE HE false true false _ S e
        have h2 : (p4StepUH GE HE OS isOld S (.delete e)).insSup.toFinset ⊆ S.insSup.toFinset :=
          p4StepEdge_insSup_sub GE HE false true false _ S e
        refine ⟨?_, ih2.trans (Finset.union_subset_union h2 (by simp [uhInsFinset]))⟩
        intro x hx
        have h' := ih1 hx
        rcases Finset.mem_union.mp h' with h' | h'
        · rcases Finset.mem_insert.mp (h1 h') with rfl | hs
          · exact Finset.mem_union_right _ (by simp [uhDelFinset])
          · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by
            simp only [uhDelFinset, List.filterMap_cons, List.toFinset_cons, Finset.mem_insert]
            exact Or.inr h')
      | split v v' St Sh =>
        refine ⟨ih1.trans (Finset.union_subset_union_right (by simp [uhDelFinset])),
          ih2.trans (Finset.union_subset_union_right (by simp [uhInsFinset]))⟩

private lemma foldl_p4StepD_sub (GE HE : Finset ℕ) :
    ∀ (D : List ℕ) (S : Phase4WS),
      (D.foldl (p4StepD GE HE) S).delSup.toFinset ⊆ S.delSup.toFinset ∪ D.toFinset ∧
      (D.foldl (p4StepD GE HE) S).insSup.toFinset ⊆ S.insSup.toFinset ∪ D.toFinset
  | [], S => ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  | e :: rest, S => by
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4StepD_sub GE HE rest (p4StepD GE HE S e)
      have h1 : (p4StepD GE HE S e).delSup.toFinset ⊆ insert e S.delSup.toFinset :=
        p4StepEdge_delSup_sub GE HE true true true false S e
      have h2 : (p4StepD GE HE S e).insSup.toFinset ⊆ insert e S.insSup.toFinset :=
        p4StepEdge_insSup_sub GE HE true true true false S e
      constructor
      · intro x hx
        rcases Finset.mem_union.mp (ih1 hx) with h | h
        · rcases Finset.mem_insert.mp (h1 h) with rfl | hs
          · exact Finset.mem_union_right _ (by simp)
          · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by simp [h])
      · intro x hx
        rcases Finset.mem_union.mp (ih2 hx) with h | h
        · rcases Finset.mem_insert.mp (h2 h) with rfl | hs
          · exact Finset.mem_union_right _ (by simp)
          · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by simp [h])

private lemma foldl_p4StepR_eq (GE HE : Finset ℕ) (isOld : Bool) :
    ∀ (R : List ℕ) (S : Phase4WS),
      (R.foldl (p4StepR GE HE isOld) S).delSup = S.delSup ∧
      (R.foldl (p4StepR GE HE isOld) S).insSup = S.insSup
  | [], S => ⟨rfl, rfl⟩
  | e :: rest, S => by
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4StepR_eq GE HE isOld rest (p4StepR GE HE isOld S e)
      have h1 : (p4StepR GE HE isOld S e).delSup = S.delSup := by
        unfold p4StepR; split_ifs; simp [pushCopy]; split_ifs <;> rfl; rfl
      have h2 : (p4StepR GE HE isOld S e).insSup = S.insSup := by
        unfold p4StepR; split_ifs; simp [pushCopy]; split_ifs <;> rfl; rfl
      exact ⟨ih1.trans h1, ih2.trans h2⟩

private lemma foldl_p4StepEdge_walk_sub (GE HE : Finset ℕ) :
    ∀ (l : List ℕ) (S : Phase4WS),
      (l.foldl (p4StepEdge GE HE true true true false) S).delSup.toFinset ⊆
        S.delSup.toFinset ∪ l.toFinset ∧
      (l.foldl (p4StepEdge GE HE true true true false) S).insSup.toFinset ⊆
        S.insSup.toFinset ∪ l.toFinset
  | [], S => ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  | e :: rest, S => by
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4StepEdge_walk_sub GE HE rest
        (p4StepEdge GE HE true true true false S e)
      have h1 := p4StepEdge_delSup_sub GE HE true true true false S e
      have h2 := p4StepEdge_insSup_sub GE HE true true true false S e
      simp only [↓reduceIte] at h1 h2
      constructor
      · intro x hx
        rcases Finset.mem_union.mp (ih1 hx) with h | h
        · rcases Finset.mem_insert.mp (h1 h) with rfl | hs
          · exact Finset.mem_union_right _ (by simp)
          · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by simp [h])
      · intro x hx
        rcases Finset.mem_union.mp (ih2 hx) with h | h
        · rcases Finset.mem_insert.mp (h2 h) with rfl | hs
          · exact Finset.mem_union_right _ (by simp)
          · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by simp [h])

private lemma foldl_p4StepDleft_sub (GE HE OS : Finset ℕ) (walk : ℕ → List (ℕ × Bool)) :
    ∀ (cb : List ℕ) (S : Phase4WS),
      (cb.foldl (p4StepDleft GE HE OS walk) S).delSup.toFinset ⊆
        S.delSup.toFinset ∪ cb.toFinset.biUnion (fun e => ((walk e).map Prod.fst).toFinset) ∧
      (cb.foldl (p4StepDleft GE HE OS walk) S).insSup.toFinset ⊆
        S.insSup.toFinset ∪ cb.toFinset.biUnion (fun e => ((walk e).map Prod.fst).toFinset)
  | [], S => ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  | e :: rest, S => by
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4StepDleft_sub GE HE OS walk rest
        (p4StepDleft GE HE OS walk S e)
      have hstep : (p4StepDleft GE HE OS walk S e).delSup.toFinset ⊆
            S.delSup.toFinset ∪ ((walk e).map Prod.fst).toFinset ∧
          (p4StepDleft GE HE OS walk S e).insSup.toFinset ⊆
            S.insSup.toFinset ∪ ((walk e).map Prod.fst).toFinset := by
        unfold p4StepDleft
        split_ifs
        · exact foldl_p4StepEdge_walk_sub GE HE ((walk e).map Prod.fst) S
        · exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩
      constructor
      · intro x hx
        rcases Finset.mem_union.mp (ih1 hx) with h | h
        · rcases Finset.mem_union.mp (hstep.1 h) with hs | hw
          · exact Finset.mem_union_left _ hs
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, by simp, hw⟩)
        · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp h
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, by simp [hy], hxy⟩)
      · intro x hx
        rcases Finset.mem_union.mp (ih2 hx) with h | h
        · rcases Finset.mem_union.mp (hstep.2 h) with hs | hw
          · exact Finset.mem_union_left _ hs
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, by simp, hw⟩)
        · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp h
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, by simp [hy], hxy⟩)

/-- **Candidate-list cardinality growth across one task (`p4TaskWS`)**: when `o` satisfies
`P4OutFacts P d U o` and `d' = ⟨d.G₀, d.Us ++ [U]⟩`, `p4TaskWS` grows `delSup.toFinset.card` and
`insSup.toFinset.card` by at most `out.UH.length + out.D.card + ∑ e ∈ R, |piTotal d' e|`. -/
theorem p4TaskWS_delSup_insSup_card_le (P : DSParams) (d : DSHist) (U : List Update)
    (OS : Finset ℕ) (o : P4TaskOut) (S : Phase4WS)
    (hVG₀ : d.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hBV : d.G₀.BatchIsValid (d.flat ++ U)) (hds : ∀ u ∈ d.flat ++ U, isDelOrSplit u)
    (hF : P4OutFacts P d U o) :
    let d' : DSHist := ⟨d.G₀, d.Us ++ [U]⟩
    let out := update (d.state P) U (canonicalSparsify P.impl)
    let R := updateReembSet (d.state P) U (canonicalSparsify P.impl)
    (p4TaskWS P d' OS o.UH o.dL o.rL S).delSup.toFinset.card ≤
      S.delSup.toFinset.card + out.UH.length + out.D.card +
        R.sum (fun e => (piTotal (d'.state P) e).length) ∧
    (p4TaskWS P d' OS o.UH o.dL o.rL S).insSup.toFinset.card ≤
      S.insSup.toFinset.card + out.UH.length + out.D.card +
        R.sum (fun e => (piTotal (d'.state P) e).length) := by
  intro d' out R
  set S₀ : Phase4WS := { S with copyBuf := [] }
  set S₁ := o.UH.foldl (p4StepUH (d'.state P).G.E (d'.state P).H.E OS true) S₀
  set S₂ := o.dL.foldl (p4StepD (d'.state P).G.E (d'.state P).H.E) S₁
  set S₃ := o.rL.foldl (p4StepR (d'.state P).G.E (d'.state P).H.E true) S₂
  have h1 := foldl_p4StepUH_sub (d'.state P).G.E (d'.state P).H.E OS true o.UH S₀
  have h2 := foldl_p4StepD_sub (d'.state P).G.E (d'.state P).H.E o.dL S₁
  have h3 := foldl_p4StepR_eq (d'.state P).G.E (d'.state P).H.E true o.rL S₂
  have h4 := foldl_p4StepDleft_sub (d'.state P).G.E (d'.state P).H.E OS (piTotal (d'.state P))
    S₃.copyBuf S₃
  -- `S₃.copyBuf.toFinset ⊆ p4CopyCand P d U ⊆ R`
  have hcb_sub : S₃.copyBuf.toFinset ⊆ R := by
    intro e he
    have hmem := mem_p4TaskScan_copyBuf_cand (List.mem_toFinset.mp he)
    have hcand : e ∈ p4CopyCand P d U := by
      unfold p4CopyCand
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨?_, hmem.2.1⟩, hmem.2.2⟩
      rcases hmem.1 with hUH | hR
      · rw [uhDelFinset_perm hF.1] at hUH
        exact Finset.mem_union_left _ hUH
      · have : e ∈ o.rL.toFinset := List.mem_toFinset.mpr hR
        rw [hF.2.2.2.2.2.1] at this
        exact Finset.mem_union_right _ this
    exact p4CopyCand_sub_updateReembSet P d U hVG₀ hL hGm₀ hBV hds hcand
  have hUH_del : (uhDelFinset o.UH).card ≤ out.UH.length := by
    rw [uhDelFinset_perm hF.1]
    unfold uhDelFinset
    exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)
  have hUH_ins : (uhInsFinset o.UH).card ≤ out.UH.length := by
    have hlen : o.UH.length = out.UH.length := hF.1.length_eq
    unfold uhInsFinset
    exact ((List.toFinset_card_le _).trans (List.length_filterMap_le _ _)).trans (le_of_eq hlen)
  have hD_card : o.dL.toFinset.card = out.D.card := congrArg Finset.card hF.2.2.2.1
  have hwalk_card : (S₃.copyBuf.toFinset.biUnion
      fun e => ((piTotal (d'.state P) e).map Prod.fst).toFinset).card ≤
      R.sum (fun e => (piTotal (d'.state P) e).length) := by
    calc (S₃.copyBuf.toFinset.biUnion fun e => ((piTotal (d'.state P) e).map Prod.fst).toFinset).card
        ≤ S₃.copyBuf.toFinset.sum fun e => ((piTotal (d'.state P) e).map Prod.fst).toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ S₃.copyBuf.toFinset.sum fun e => (piTotal (d'.state P) e).length :=
          Finset.sum_le_sum fun e _ => (List.toFinset_card_le _).trans (by simp)
      _ ≤ R.sum fun e => (piTotal (d'.state P) e).length := Finset.sum_le_sum_of_subset hcb_sub
  constructor
  · have hsub : (p4TaskWS P d' OS o.UH o.dL o.rL S).delSup.toFinset ⊆
        S.delSup.toFinset ∪ uhDelFinset o.UH ∪ o.dL.toFinset ∪
        S₃.copyBuf.toFinset.biUnion (fun e => ((piTotal (d'.state P) e).map Prod.fst).toFinset) := by
      calc (p4TaskWS P d' OS o.UH o.dL o.rL S).delSup.toFinset
          ⊆ S₃.delSup.toFinset ∪ _ := h4.1
        _ = S₂.delSup.toFinset ∪ _ := by rw [h3.1]
        _ ⊆ (S₁.delSup.toFinset ∪ o.dL.toFinset) ∪ _ := Finset.union_subset_union_left h2.1
        _ ⊆ ((S.delSup.toFinset ∪ uhDelFinset o.UH) ∪ o.dL.toFinset) ∪ _ :=
            Finset.union_subset_union_left (Finset.union_subset_union_left h1.1)
    have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc2 := Finset.card_union_le (S.delSup.toFinset ∪ uhDelFinset o.UH) o.dL.toFinset
    have hc3 := Finset.card_union_le S.delSup.toFinset (uhDelFinset o.UH)
    omega
  · have hsub : (p4TaskWS P d' OS o.UH o.dL o.rL S).insSup.toFinset ⊆
        S.insSup.toFinset ∪ uhInsFinset o.UH ∪ o.dL.toFinset ∪
        S₃.copyBuf.toFinset.biUnion (fun e => ((piTotal (d'.state P) e).map Prod.fst).toFinset) := by
      calc (p4TaskWS P d' OS o.UH o.dL o.rL S).insSup.toFinset
          ⊆ S₃.insSup.toFinset ∪ _ := h4.2
        _ = S₂.insSup.toFinset ∪ _ := by rw [h3.2]
        _ ⊆ (S₁.insSup.toFinset ∪ o.dL.toFinset) ∪ _ := Finset.union_subset_union_left h2.2
        _ ⊆ ((S.insSup.toFinset ∪ uhInsFinset o.UH) ∪ o.dL.toFinset) ∪ _ :=
            Finset.union_subset_union_left (Finset.union_subset_union_left h1.2)
    have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc2 := Finset.card_union_le (S.insSup.toFinset ∪ uhInsFinset o.UH) o.dL.toFinset
    have hc3 := Finset.card_union_le S.insSup.toFinset (uhInsFinset o.UH)
    omega

/-- **New-slot scan growth**: `p4StepNew` leaves `delSup` unchanged and adds only edges of `gL`
to `insSup`. -/
theorem foldl_p4StepNew_delSup_insSup (HE : Finset ℕ) :
    ∀ (gL : List ℕ) (S : Phase4WS),
      (gL.foldl (p4StepNew HE) S).delSup = S.delSup ∧
      (gL.foldl (p4StepNew HE) S).insSup.toFinset ⊆ S.insSup.toFinset ∪ gL.toFinset
  | [], S => ⟨rfl, Finset.subset_union_left⟩
  | e :: rest, S => by
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := foldl_p4StepNew_delSup_insSup HE rest (p4StepNew HE S e)
      have h1 : (p4StepNew HE S e).delSup = S.delSup := by
        unfold p4StepNew
        by_cases heH : e ∈ HE
        · simp [heH]
        · simp only [heH, not_false_eq_true, ↓reduceIte, pushCopy]
          split_ifs <;> rfl
      have h2 : (p4StepNew HE S e).insSup.toFinset ⊆ insert e S.insSup.toFinset := by
        unfold p4StepNew
        by_cases heH : e ∈ HE
        · simp only [heH, not_true_eq_false, ↓reduceIte]
          exact pushDedup_toFinset_sub _ _
        · simp only [heH, not_false_eq_true, ↓reduceIte, pushCopy]
          split_ifs <;> exact pushDedup_toFinset_sub _ _
      refine ⟨ih1.trans h1, fun x hx => ?_⟩
      rcases Finset.mem_union.mp (ih2 hx) with h | h
      · rcases Finset.mem_insert.mp (h2 h) with rfl | hs
        · exact Finset.mem_union_right _ (by simp)
        · exact Finset.mem_union_left _ hs
      · exact Finset.mem_union_right _ (by simp [h])

/-! ## 2. `p4CopyEdgeCost` and `p4NewWork` bounds -/

/-- Upper bound on `p4CopyEdgeCost` for an edge `e ∈ p4CopyCand P d U`. -/
theorem p4CopyEdgeCost_le (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ)
    (hs : s < cap) (d : DSHist) (U : List Update) {e : ℕ} (he : e ∈ p4CopyCand P d U) :
    let d' : DSHist := ⟨d.G₀, d.Us ++ [U]⟩
    p4CopyEdgeCost P (S6.set ⟨s, hs⟩ (some d')) s d' e ≤
      584 * (piTotal (d'.state P) e).length + 207 * P.L + 676 := by
  intro d'
  unfold p4CopyEdgeCost p4DleftEdgeCost
  have hnotH : e ∉ (d'.state P).H.E := (Finset.mem_sdiff.mp he).2
  have hsw : slotWalk P (S6.set ⟨s, hs⟩ (some d')) s e = piTotal (d'.state P) e := by
    unfold slotWalk
    simp [hs, BucketSpannerState.set, hnotH]
  rw [hsw]
  unfold Read.walkWords
  split_ifs <;> omega

/-- Upper bound on `p4NewWork P S6 s d' + 20` when `S6 ⟨s, hs⟩ = some d'`. -/
theorem p4NewWork_add_20_le (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ)
    (hs : s < cap) (d' : DSHist) (hd' : S6 ⟨s, hs⟩ = some d')
    (hEsub : (d'.state P).G.E ⊆ d'.G₀.E) :
    p4NewWork P S6 s d' + 20 ≤
      (561 + 142 * P.L) * d'.G₀.m + 420 +
        284 * ((d'.state P).G.E \ (d'.state P).H.E).sum (fun e => (piTotal (d'.state P) e).length) := by
  unfold p4NewWork
  have hGcard : (d'.state P).G.E.card ≤ d'.G₀.m := Finset.card_le_card hEsub
  have hDiffCard : ((d'.state P).G.E \ (d'.state P).H.E).card ≤ d'.G₀.m :=
    (Finset.card_le_card Finset.sdiff_subset).trans hGcard
  have hsum : ((d'.state P).G.E \ (d'.state P).H.E).sum
        (fun e => Read.walkWords (slotWalk P S6 s e) + (if d'.Us = [] then 0 else P.L) + 2) ≤
      2 * ((d'.state P).G.E \ (d'.state P).H.E).sum (fun e => (piTotal (d'.state P) e).length) +
        (3 + P.L) * d'.G₀.m := by
    have hterm : ∀ e ∈ (d'.state P).G.E \ (d'.state P).H.E,
        Read.walkWords (slotWalk P S6 s e) + (if d'.Us = [] then 0 else P.L) + 2 ≤
          2 * (piTotal (d'.state P) e).length + (3 + P.L) := by
      intro e he
      have hnotH : e ∉ (d'.state P).H.E := (Finset.mem_sdiff.mp he).2
      have hsw : slotWalk P S6 s e = piTotal (d'.state P) e := by
        unfold slotWalk; simp [hs, hd', hnotH]
      rw [hsw]; unfold Read.walkWords
      split_ifs <;> omega
    calc ((d'.state P).G.E \ (d'.state P).H.E).sum _
        ≤ ((d'.state P).G.E \ (d'.state P).H.E).sum
            (fun e => 2 * (piTotal (d'.state P) e).length + (3 + P.L)) :=
          Finset.sum_le_sum hterm
      _ = 2 * ((d'.state P).G.E \ (d'.state P).H.E).sum (fun e => (piTotal (d'.state P) e).length) +
            ((d'.state P).G.E \ (d'.state P).H.E).card * (3 + P.L) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]
      _ ≤ 2 * ((d'.state P).G.E \ (d'.state P).H.E).sum (fun e => (piTotal (d'.state P) e).length) +
            (3 + P.L) * d'.G₀.m := by
          rw [mul_comm (3 + P.L)]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hDiffCard) _
  have h1 : 142 * ((d'.state P).G.E \ (d'.state P).H.E).sum
        (fun e => Read.walkWords (slotWalk P S6 s e) + (if d'.Us = [] then 0 else P.L) + 2) ≤
      284 * ((d'.state P).G.E \ (d'.state P).H.E).sum (fun e => (piTotal (d'.state P) e).length) +
        (426 + 142 * P.L) * d'.G₀.m := by
    have := Nat.mul_le_mul_left 142 hsum
    have hring : 142 * (2 * ((d'.state P).G.E \ (d'.state P).H.E).sum
          (fun e => (piTotal (d'.state P) e).length) + (3 + P.L) * d'.G₀.m) =
        284 * ((d'.state P).G.E \ (d'.state P).H.E).sum (fun e => (piTotal (d'.state P) e).length) +
          (426 + 142 * P.L) * d'.G₀.m := by ring
    omega
  have h2 : 135 * (d'.state P).G.E.card ≤ 135 * d'.G₀.m := Nat.mul_le_mul_left 135 hGcard
  have hring2 : 135 * d'.G₀.m + (426 + 142 * P.L) * d'.G₀.m = (561 + 142 * P.L) * d'.G₀.m := by
    ring
  omega

/-! ## 3. LSF forest deletions, `spanInitBound`, and `batchEnc` positivity -/

/-- Every forest edge removed during `compLSFBatch cs U` is either deleted by `U` or released as a
canonical split entry in `canonSplitList cs U`. -/
theorem fDel_subset_batchDeletes_union_splits {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (cs : CompLSFState) (U : List Update),
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      cs.lsf.F.F.E \ (compLSFBatch cs U).lsf.F.F.E ⊆
        batchDeletes U ∪ ((canonSplitList cs U).map CompSplitEntry.edge).toFinset
  | cs, [], _, _ => by simp [compLSFBatch]
  | cs, u :: rest, hI, hU => by
      obtain ⟨hu, hrest⟩ := hU
      have hI1 := compLSFInv_step hI hu
      have ih := fDel_subset_batchDeletes_union_splits (compLSFStepSingle cs u) rest hI1 hrest
      intro e he
      obtain ⟨he0, heNotEnd⟩ := Finset.mem_sdiff.mp he
      by_cases he1 : e ∈ (compLSFStepSingle cs u).lsf.F.F.E
      · have hmem := ih (Finset.mem_sdiff.mpr ⟨he1, heNotEnd⟩)
        rcases Finset.mem_union.mp hmem with hd | hs
        · exact Finset.mem_union_left _ (by
            obtain ⟨w, hw, hw_eq⟩ := (mem_batchDeletes_iff _ _).mp hd
            exact (mem_batchDeletes_iff _ _).mpr ⟨w, List.mem_cons_of_mem _ hw, hw_eq⟩)
        · exact Finset.mem_union_right _ (by
            simp only [canonSplitList, List.map_append, List.toFinset_append, Finset.mem_union]
            exact Or.inr hs)
      · -- `e` left the forest at step `u`: either `u = .delete e` or `e` was released at `u`.
        by_cases hdel : e ∈ batchDeletes [u]
        · exact Finset.mem_union_left _ (by
            obtain ⟨w, hw, hw_eq⟩ := (mem_batchDeletes_iff _ _).mp hdel
            simp only [List.mem_singleton] at hw
            exact (mem_batchDeletes_iff _ _).mpr ⟨w, hw ▸ List.mem_cons_self, hw_eq⟩)
        · refine Finset.mem_union_right _ ?_
          simp only [canonSplitList, List.map_append, List.toFinset_append, Finset.mem_union]
          left
          have heAfter : e ∈ (forestAfterInput cs.RF.F u).E := by
            cases u with
            | insert e' a b => exact he0
            | delete e' =>
              simp only [forestAfterInput, Finset.mem_erase]
              refine ⟨?_, he0⟩
              intro heq; subst heq
              exact hdel ((mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_singleton_self _, rfl⟩)
            | split v v' St Sh => exact he0
          have heRel : e ∈ (forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E :=
            Finset.mem_sdiff.mpr ⟨heAfter, he1⟩
          -- Released forest edges appear in `canonStepSplits cs u` via `releasesSplitEntries`.
          have hmem_sort : e ∈ ((forestAfterInput cs.RF.F u).E \
              (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·) :=
            (Finset.mem_sort _).mpr heRel
          have hrel_edges : ∀ (R : Finset ℕ) (L : LSF) (l : List ℕ),
              (releasesSplitEntries R L l).map CompSplitEntry.edge = l := by
            intro R L l
            induction l generalizing L with
            | nil => rfl
            | cons x xs ihx =>
              simp only [releasesSplitEntries, List.map_cons, ihx]
          unfold canonStepSplits
          simp only [List.map_append, List.toFinset_append, Finset.mem_union]
          right
          rw [hrel_edges]
          exact List.mem_toFinset.mpr hmem_sort

/-- Under `c.Exact`, `c.fDel.length ≤ U.length + (canonSplitList tr.cs U).length`. -/
theorem fDel_length_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    {c : LSFChange} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hEx : c.Exact cs.lsf (compLSFBatch cs U).lsf) :
    c.fDel.length ≤ U.length + (canonSplitList cs U).length := by
  have hnd : c.fDel.Nodup := hEx.2.2.1
  have hset : c.fDel.toFinset = cs.lsf.F.F.E \ (compLSFBatch cs U).lsf.F.F.E := hEx.2.2.2
  rw [← List.toFinset_card_of_nodup hnd, hset]
  have hsub := fDel_subset_batchDeletes_union_splits cs U hI hU
  have hbd : (batchDeletes U).card ≤ U.length := by
    have hsubD : batchDeletes U ⊆
        (U.filterMap fun | .delete e => some e | _ => none).toFinset := by
      intro e he
      obtain ⟨w, hw, hw_eq⟩ := (mem_batchDeletes_iff _ _).mp he
      subst hw_eq
      exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.delete e, hw, rfl⟩)
    exact (Finset.card_le_card hsubD).trans
      ((List.toFinset_card_le _).trans (List.length_filterMap_le _ _))
  have hsp : ((canonSplitList cs U).map CompSplitEntry.edge).toFinset.card ≤
      (canonSplitList cs U).length :=
    (List.toFinset_card_le _).trans (by simp)
  exact ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _)).trans (Nat.add_le_add hbd hsp)

/-- `Hb.m + 1 ≤ spanInitBound P_b L splitBound Hb`. -/
theorem m_add_one_le_spanInitBound (P_b : SparsifyParams) (L splitBound : ℕ) (Hb : MGraph) :
    Hb.m + 1 ≤ spanInitBound P_b L splitBound Hb := by
  unfold spanInitBound
  have h1a : (0 : ℝ) ≤ ((activeSubgraph Hb).n : ℝ) := Nat.cast_nonneg _
  have h1b : (0 : ℝ) ≤ (Hb.m : ℝ) := Nat.cast_nonneg _
  have h1c : (0 : ℝ) ≤ (Hb.n : ℝ) := Nat.cast_nonneg _
  have h1d : (0 : ℝ) ≤ ((Hb.n + splitBound : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog1 : 0 ≤ Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hlog3 : 0 ≤ Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have ht1 : 0 ≤ P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) := by
    have := P_b.hK_t; have := P_b.hγ_ℓ; positivity
  have ht2 : 0 ≤ P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
      (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s := by
    have := P_b.hK_s; have := P_b.hγ_ℓ; positivity
  have ht3 : 0 ≤ (Hb.m : ℝ) * P_b.γ_ℓ := by have := P_b.hγ_ℓ; positivity
  have ht4 : 0 ≤ ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) := by
    positivity
  have hle : ((Hb.m + 1 : ℕ) : ℝ) ≤
      P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) +
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]; linarith
  exact_mod_cast le_trans hle (Nat.le_ceil _)

/-- Any nonempty update batch has encoding size at least `1`. -/
theorem batchEnc_pos_of_ne_nil (G : MGraph) {U : List Update} (hU : U ≠ []) :
    1 ≤ G.batchEnc U := by
  cases U with
  | nil => exact absurd rfl hU
  | cons u rest =>
    simp only [MGraph.batchEnc]
    have hu : 1 ≤ G.updateEnc u := by
      cases u <;> simp [MGraph.updateEnc]
    omega

end

end MinCostFlow.SparseCore.Program
