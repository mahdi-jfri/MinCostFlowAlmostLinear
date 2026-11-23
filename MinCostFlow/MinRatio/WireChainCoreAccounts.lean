module

public import MinCostFlow.MinRatio.WireChainCoreBatch
public import MinCostFlow.MinRatio.WireChainCoreFilter
public import MinCostFlow.MinRatio.InitDetectThresholds
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.IsNegative
import WordRAM.Tactic

/-!
# Deleted-edge tree edit emission and single-edge account refresh (`WireChainCoreAccounts`)

Provides two deterministic Word-RAM subroutines used during Algorithm 2 chain update:
1. `wireEmitDeletedTreeEditsBody`: scans an edge-only internal batch `U_int` and emits
   `TreeChange.delete ei` for every `.delete ei` that is live in `G₀` (`rootGraph`) and currently
   active in the path tree (`slots[ei] ≠ 0`), producing an exact
   `TreeEditDifference oldF.E (oldF.E ∩ G₀'.E) delEdits` so `wireTreeSyncLoop` cuts every deleted
   tree edge and saves its canonical `PathEdgeAt` record.
2. `wireRefreshOneAccountBody`: given a replaced edge's canonical old record `oldRecPtr`, old
   threshold `oldThrPtr`, new external gradient `gPtr` and length `lPtr`, and `-ε` block,
   computes `thrNew = detectorThreshold P ε lNew`, `acc = detOld + thrOld`, `detNew = acc - thrNew`,
   builds the canonical `PathEdgeAt` record `[1, 1, gNew, lNew, oldFlow, detNew]`, and writes
   `(thrNewPtr, recNewPtr, isNegBit)` at `[nextHeap - 3, nextHeap)` in `O(L^2)` steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.IPM.Machine

/-! ### 1. Emitting deleted tree edges from `U_int` (`wireEmitDeletedTreeEditsBody`) -/

/-- Procedure `[uIntBuf, rootGraph, slots, outPtr]` (`reg 0..3`): scans edge-only `U_int` at
`uIntBuf` and writes `[0, ei]` at `outPtr` for every `.delete ei` whose edge is present in
`rootGraph` (`ePres[ei] ≠ 0`) and active in `slots` (`slots[ei] ≠ 0`). Returns the count. -/
@[expose] def wireEmitDeletedTreeEditsBody : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 6 (.load (.reg 1)) ;;
  .assign 7 (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 7) (.reg 6))) ;;
  .assign 8 (.const 0) ;;
  forRange 9 (.const 0) (.reg 4)
    (.assign 10 (.load (.reg 5)) ;;
     .cond (.bin .eq (.reg 10) (.const 0))
       (.assign 5 (.bin .add (.reg 5) (.const 4)))
       (.assign 11 (.load (.bin .add (.reg 5) (.const 1))) ;;
        .cond (.load (.bin .add (.reg 7) (.reg 11)))
          (.cond (.load (.bin .add (.reg 2) (.reg 11)))
            (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 0) ;;
             .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 1)) (.reg 11) ;;
             .assign 8 (.bin .add (.reg 8) (.const 1)))
            .nop)
          .nop ;;
        .assign 5 (.bin .add (.reg 5) (.const 2)))) ;;
  .ret (.reg 8)

theorem wireEmitDeletedTreeEditsBody_noRand : wireEmitDeletedTreeEditsBody.NoRand := by
  simp [wireEmitDeletedTreeEditsBody, forRange, forUp, Stmt.NoRand]

/-- Pure list of deleted tree-edge changes emitted by `wireEmitDeletedTreeEditsBody`. -/
@[expose] def deletedTreeEdits (G0E activeE : Finset ℕ) (U_int : List Update) : List TreeChange :=
  open Classical in
  U_int.filterMap fun u => match u with
    | .delete ei => if ei ∈ G0E ∧ ei ∈ activeE then some (.delete ei) else none
    | _ => none

theorem deletedTreeEdits_length_le (G0E activeE : Finset ℕ) (U_int : List Update) :
    (deletedTreeEdits G0E activeE U_int).length ≤ U_int.length := by
  unfold deletedTreeEdits
  induction U_int with
  | nil => simp
  | cons u rest ih =>
    cases u <;> simp only [List.filterMap_cons]
    · exact ih.trans (Nat.le_succ _)
    · split_ifs
      · simp only [List.length_cons]; omega
      · exact ih.trans (Nat.le_succ _)
    · exact ih.trans (Nat.le_succ _)

/-- Under `translateBatch_oldId_facts`, `deletedTreeEdits G0.E oldF.E U_int` is a valid
`TreeEditDifference oldF.E (oldF.E ∩ G0'.E)`. -/
theorem treeEditDiff_deletedTreeEdits {G0 : MGraph} {oldF : Finset ℕ} {U_int : List Update}
    (hOldSub : oldF ⊆ G0.E)
    (hSurv : ∀ ei ∈ G0.E, ei ∈ (G0.applyBatch U_int).E ↔ Update.delete ei ∉ U_int)
    (hNodup : (U_int.filterMap fun u => match u with
      | .delete ei => if ei ∈ G0.E then some ei else none | _ => none).Nodup) :
    TreeEditDifference oldF (oldF ∩ (G0.applyBatch U_int).E) (deletedTreeEdits G0.E oldF U_int) := by
  classical
  let delIds := U_int.filterMap fun u => match u with
    | .delete ei => if ei ∈ G0.E ∧ ei ∈ oldF then some ei else none | _ => none
  have hSublist : delIds.Sublist (U_int.filterMap fun u => match u with
      | .delete ei => if ei ∈ G0.E then some ei else none | _ => none) := by
    dsimp only [delIds]
    clear hOldSub hSurv hNodup
    induction U_int with
    | nil => exact List.Sublist.slnil
    | cons u rest ih =>
      cases u with
      | insert _ _ _ => exact ih
      | split _ _ _ _ => exact ih
      | delete ei =>
        simp only [List.filterMap_cons]
        by_cases h1 : ei ∈ G0.E
        · by_cases h2 : ei ∈ oldF
          · simp only [h1, h2, and_self, ↓reduceIte]; exact ih.cons_cons ei
          · simp only [h1, h2, and_false, ↓reduceIte]; exact ih.cons ei
        · simp only [h1, false_and, ↓reduceIte]; exact ih
  have hDelNd : delIds.Nodup := hNodup.sublist hSublist
  have hDelMem (x : ℕ) : x ∈ delIds ↔ x ∈ oldF \ (oldF ∩ (G0.applyBatch U_int).E) := by
    simp only [delIds, List.mem_filterMap, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨u, hu, hus⟩
      cases u with
      | insert _ _ _ => simp at hus
      | split _ _ _ _ => simp at hus
      | delete ei =>
        dsimp only at hus
        split_ifs at hus with h1
        · injection hus with heq; subst heq
          refine ⟨h1.2, fun ⟨_, hlive⟩ => ((hSurv _ h1.1).mp hlive) hu⟩
    · rintro ⟨hOld, hNot⟩
      have hG0 : x ∈ G0.E := hOldSub hOld
      have hNotLive : x ∉ (G0.applyBatch U_int).E := fun hl => hNot ⟨hOld, hl⟩
      have hDelU : Update.delete x ∈ U_int := by
        by_contra hnd; exact hNotLive ((hSurv x hG0).mpr hnd)
      exact ⟨.delete x, hDelU, by simp [hG0, hOld]⟩
  let oldNames := delIds ++ (oldF ∩ (G0.applyBatch U_int).E).toList
  let newNames := (oldF ∩ (G0.applyBatch U_int).E).toList
  have hOldPerm : oldNames.Perm oldF.toList := by
    refine (List.perm_ext_iff_of_nodup ?_ (Finset.nodup_toList _)).mpr ?_
    · refine List.nodup_append.mpr ⟨hDelNd, Finset.nodup_toList _, fun a ha b hb hab => ?_⟩
      subst hab
      exact (Finset.mem_sdiff.mp ((hDelMem a).mp ha)).2 (Finset.mem_toList.mp hb)
    · intro x
      simp only [oldNames, List.mem_append, hDelMem, Finset.mem_toList, Finset.mem_sdiff, Finset.mem_inter]
      tauto
  have hOf := treeEditDifference_of_filter hOldPerm (List.Perm.refl newNames)
  have hF1 : oldNames.filter (fun e => decide (e ∉ oldF ∩ (G0.applyBatch U_int).E)) = delIds := by
    simp only [oldNames, List.filter_append]
    have hA : delIds.filter (fun e => decide (e ∉ oldF ∩ (G0.applyBatch U_int).E)) = delIds :=
      List.filter_eq_self.mpr (fun x hx => by
        simp only [decide_eq_true_eq]; exact (Finset.mem_sdiff.mp ((hDelMem x).mp hx)).2)
    have hB : newNames.filter (fun e => decide (e ∉ oldF ∩ (G0.applyBatch U_int).E)) = [] :=
      List.filter_eq_nil_iff.mpr (fun x hx => by
        simp only [decide_eq_true_eq, not_not]; exact Finset.mem_toList.mp hx)
    rw [hA, hB, List.append_nil]
  have hF2 : newNames.filter (fun e => decide (e ∉ oldF)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by
      simp only [decide_eq_true_eq, not_not]; exact (Finset.mem_inter.mp (Finset.mem_toList.mp hx)).1)
  have hMapEq : delIds.map TreeChange.delete = deletedTreeEdits G0.E oldF U_int := by
    dsimp only [delIds, deletedTreeEdits]
    clear hOldSub hSurv hNodup hSublist hDelNd hDelMem hOldPerm hOf hF1 hF2
    induction U_int with
    | nil => rfl
    | cons u rest ih =>
      cases u with
      | insert _ _ _ => exact ih
      | split _ _ _ _ => exact ih
      | delete ei =>
        simp only [List.filterMap_cons]
        split_ifs <;> simp [List.map_cons, ih]
  rw [hF1, hF2, List.map_nil, List.append_nil, hMapEq] at hOf
  exact hOf

private def delRecOff (U : List Update) (k : ℕ) : ℕ :=
  ((U.take k).flatMap updateWords).length

private theorem delRecOff_succ {U : List Update} {k : ℕ} (hk : k < U.length) :
    delRecOff U (k + 1) = delRecOff U k + (updateWords U[k]).length := by
  unfold delRecOff
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp

private theorem delBatch_word {mem : ℕ → ℕ} {a : ℕ} {U : List Update}
    (hb : IPM.Machine.BatchAt mem a U) {k : ℕ} (hk : k < U.length)
    {j : ℕ} (hj : j < (updateWords U[k]).length) :
    mem (a + 1 + delRecOff U k + j) = (updateWords U[k])[j] ∧
      1 + delRecOff U k + j < (batchWords U).length := by
  have hsplit : U = U.take k ++ U[k] :: U.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hfl : U.flatMap updateWords =
      (U.take k).flatMap updateWords ++ (updateWords U[k] ++ (U.drop (k + 1)).flatMap updateWords) := by
    conv_lhs => rw [hsplit]; rw [List.flatMap_append, List.flatMap_cons]
  have hidx : (delRecOff U k + j) + 1 < (batchWords U).length := by
    simp only [batchWords, List.length_cons, hfl, List.length_append, delRecOff]; omega
  refine ⟨?_, by omega⟩
  have hr := hb ((delRecOff U k + j) + 1) hidx
  rw [show a + 1 + delRecOff U k + j = a + ((delRecOff U k + j) + 1) by omega, hr]
  simp only [batchWords, List.getElem_cons_succ]
  have h1 : (U.flatMap updateWords)[delRecOff U k + j]'(by simp only [hfl, List.length_append, delRecOff]; omega) =
      ((U.take k).flatMap updateWords ++ (updateWords U[k] ++ (U.drop (k + 1)).flatMap updateWords))[delRecOff U k + j]'(by
        simp only [List.length_append, delRecOff]; omega) := by congr 1
  rw [h1, List.getElem_append_right (by dsimp [delRecOff]; omega)]
  simp only [delRecOff, Nat.add_sub_cancel_left]
  exact List.getElem_append_left hj

/-- Execute `wireEmitDeletedTreeEditsBody`: emits `deletedTreeEdits G0.E activeE U_int` into
`outPtr` in `O(|U_int|)` deterministic steps. -/
theorem wireEmitDeletedTreeEditsBody_runs
    {w uIntBuf rootGraph slots outPtr vCap eCap intCap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {G0 : MGraph} {activeE : Finset ℕ}
    {U_int : List Update}
    (hBatch : IPM.Machine.BatchAt mem uIntBuf U_int)
    (hEdgeOnly : ∀ u ∈ U_int, IsEdgeUpdate u)
    (hDelCap : ∀ u ∈ U_int, match u with | .delete ei => ei < eCap ∧ ei < intCap | _ => True)
    (hRootG : DynGraphAt mem rootGraph vCap eCap G0)
    (hSlots : ∀ e < intCap, mem (slots + e) ≠ 0 ↔ e ∈ activeE)
    (hBatchLe : uIntBuf + (batchWords U_int).length ≤ outPtr)
    (hRootLe : rootGraph + dynGraphSize vCap eCap ≤ outPtr)
    (hSlotsLe : slots + intCap ≤ outPtr)
    (hz : ZeroFrom mem outPtr)
    (hRoom : outPtr + 2 * U_int.length < 2 ^ w) (hw7 : 7 < 2 ^ w) :
    let emitted := deletedTreeEdits G0.E activeE U_int
    ∃ out cost,
      Runs w p ω wireEmitDeletedTreeEditsBody
        (startState [uIntBuf, rootGraph, slots, outPtr] mem pos)
        (.returned emitted.length) out cost ∧
      cost ≤ 64 * U_int.length + 40 ∧
      TreeEditsAt out.mem outPtr emitted ∧
      ZeroFrom out.mem (outPtr + 2 * emitted.length) ∧
      ∀ a < outPtr, out.mem a = mem a := by
  classical
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hLenB0 : mem uIntBuf = U_int.length := by simpa [batchWords] using hBatch 0 (by simp [batchWords])
  have hVCapEq : mem rootGraph = vCap := by simpa [dgVCapOff] using hRootG.2.2.2.1
  have hEPresMem : ∀ e < eCap, mem (dgEPresBase rootGraph vCap + e) = if e ∈ G0.E then 1 else 0 :=
    hRootG.2.2.2.2.2.2.2.2.2.2.2.1
  have hDgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  let ePresBase := dgEPresBase rootGraph vCap
  have hePresDef : ePresBase = rootGraph + 4 + 7 * vCap := rfl
  let s0 := startState [uIntBuf, rootGraph, slots, outPtr] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 4 U_int.length }
  let s2 := { s1 with regs := Function.update s1.regs 5 (uIntBuf + 1) }
  let s3 := { s2 with regs := Function.update s2.regs 6 vCap }
  let s4 := { s3 with regs := Function.update s3.regs 7 ePresBase }
  let s5 := { s4 with regs := Function.update s4.regs 8 0 }
  have r1 : Runs w p ω (.assign 4 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U_int.length, by simp [Expr.eval, s0, startState, hLenB0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 5 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨uIntBuf + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1,
        show uIntBuf + 1 < 2 ^ w by simp [batchWords] at hBatchLe; omega], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 6 (.load (.reg 1))) s2 .normal s3 3 :=
    runs_assign_iff.mpr ⟨vCap, by simp [Expr.eval, s2, s1, s0, startState, hVCapEq], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 7 (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 7) (.reg 6))))
      s3 .normal s4 8 :=
    runs_assign_iff.mpr ⟨ePresBase, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw4, hw7, hePresDef,
        show rootGraph + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
        show rootGraph + 4 + 7 * vCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 8 (.const 0)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    let pref := deletedTreeEdits G0.E activeE (U_int.take i)
    s.regs 0 = uIntBuf ∧ s.regs 1 = rootGraph ∧ s.regs 2 = slots ∧ s.regs 3 = outPtr ∧
    s.regs 4 = U_int.length ∧ s.regs 5 = uIntBuf + 1 + delRecOff U_int i ∧
    s.regs 7 = ePresBase ∧ s.regs 8 = pref.length ∧ s.regs 9 = i ∧
    TreeEditsAt s.mem outPtr pref ∧
    ZeroFrom s.mem (outPtr + 2 * pref.length) ∧
    ∀ a < outPtr, s.mem a = mem a
  let stepCost := 55
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 4)
    (P := fun s => s = s5) (Inv := Inv) (fun _ => stepCost) 0 U_int.length (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
        by simp [s5, s4, s3, s2, s1, s0, startState], by simp [s5, s4, s3, s2, s1, s0, startState],
        by simp [s5, s4, s3, s2, s1, s0, startState], by simp [s5, s4, s3, s2, s1, s0, startState],
        by simp [s5, s4, s3, s2, s1], by simp [s5, s4, s3, s2, delRecOff],
        by simp [s5, s4], by simp [s5, deletedTreeEdits], by simp,
        fun _ h => absurd h (by simp [deletedTreeEdits]),
        by simpa [s5, s4, s3, s2, s1, s0, startState, deletedTreeEdits] using hz,
        fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.2.2.2.1])
    (fun i _ hi => by
      intro s ω' hI
      obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, hAt, hzS, hFr⟩ := hI
      set pref := deletedTreeEdits G0.E activeE (U_int.take i)
      have hPrefLe : pref.length ≤ i :=
        (deletedTreeEdits_length_le _ _ _).trans (by simp [List.length_take, le_of_lt hi])
      have huE := hEdgeOnly U_int[i] (List.getElem_mem hi)
      have hTakeNext : deletedTreeEdits G0.E activeE (U_int.take (i + 1)) =
          pref ++ deletedTreeEdits G0.E activeE [U_int[i]] := by
        simp only [deletedTreeEdits, List.take_succ_eq_append_getElem hi, List.filterMap_append, pref]
      cases hUi : U_int[i] with
      | split _ _ _ _ => rw [hUi] at huE; exact huE.elim
      | insert ei u v =>
        have hRec0 := delBatch_word hBatch hi (j := 0) (by simp [hUi, updateWords])
        have hTagS : s.mem (uIntBuf + 1 + delRecOff U_int i) = 0 := by
          rw [hFr _ (by omega)]; simpa [hUi, updateWords] using hRec0.1
        have hOffNext : delRecOff U_int (i + 1) = delRecOff U_int i + 4 := by
          rw [delRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + delRecOff U_int (i + 1) < 2 ^ w := by
          have := (delBatch_word hBatch hi (j := 3) (by simp [hUi, updateWords])).2; omega
        let t1 := { s with regs := Function.update s.regs 10 0 }
        let t2 := { t1 with regs := Function.update t1.regs 5 (uIntBuf + 1 + delRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω' (.assign 10 (.load (.reg 5))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h5, hTagS], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 5 (.bin .add (.reg 5) (.const 4))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + delRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t1, h5, hw4,
              show uIntBuf + 1 + delRecOff U_int i + 4 < 2 ^ w by omega, ↓reduceIte,
              Option.some.injEq, Function.update_of_ne (by decide : (5 : ℕ) ≠ 10)]
            omega, rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 10) (.const 0)) (.assign 5 (.bin .add (.reg 5) (.const 4)))
              (.assign 11 (.load (.bin .add (.reg 5) (.const 1))) ;;
               .cond (.load (.bin .add (.reg 7) (.reg 11)))
                 (.cond (.load (.bin .add (.reg 2) (.reg 11)))
                   (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 0) ;;
                    .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 1)) (.reg 11) ;;
                    .assign 8 (.bin .add (.reg 8) (.const 1)))
                   .nop)
                 .nop ;;
               .assign 5 (.bin .add (.reg 5) (.const 2))))
            t1 .normal t2 8 :=
          runs_cond_iff.mpr ⟨1, 4, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rt2, by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t2 with regs := Function.update t2.regs 9 (i + 1) } := by
          dsimp only [Inv]; rw [hTakeNext, hUi]; simp only [deletedTreeEdits, List.filterMap_cons,
            List.filterMap_nil, List.append_nil]
          exact ⟨by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2, t1, h3],
            by simp [t2, t1, h4], by simp [t2], by simp [t2, t1, h7], by simp [t2, t1, h8], by simp,
            hAt, hzS, hFr⟩
        refine ⟨.normal, t2, 3 + 8 + 1, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 8, rt1, rCond, rfl⟩),
          ⟨hInvN, by simp [t2, t1, h9]⟩, by dsimp [stepCost]; omega⟩
      | delete ei =>
        obtain ⟨heiECap, heiIntCap⟩ := hDelCap (.delete ei) (hUi ▸ List.getElem_mem hi)
        have hRec0 := delBatch_word hBatch hi (j := 0) (by simp [hUi, updateWords])
        have hRec1 := delBatch_word hBatch hi (j := 1) (by simp [hUi, updateWords])
        have hTagS : s.mem (uIntBuf + 1 + delRecOff U_int i) = 1 := by
          rw [hFr _ (by omega)]; simpa [hUi, updateWords] using hRec0.1
        have hEiS : s.mem (uIntBuf + 1 + delRecOff U_int i + 1) = ei := by
          rw [hFr _ (by omega)]; simpa [hUi, updateWords] using hRec1.1
        have hOffNext : delRecOff U_int (i + 1) = delRecOff U_int i + 2 := by
          rw [delRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + delRecOff U_int (i + 1) < 2 ^ w := by omega
        have hPresS : s.mem (ePresBase + ei) = if ei ∈ G0.E then 1 else 0 :=
          (hFr _ (by omega)).trans (hEPresMem ei heiECap)
        have hSlotS : s.mem (slots + ei) = mem (slots + ei) := hFr _ (by omega)
        let t1 := { s with regs := Function.update s.regs 10 1 }
        let t2 := { t1 with regs := Function.update t1.regs 11 ei }
        have rt1 : Runs w p ω' (.assign 10 (.load (.reg 5))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h5, hTagS], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 11 (.load (.bin .add (.reg 5) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨ei, by
            simp [Expr.eval, BinOp.eval, t1, h5, hw1, show uIntBuf + 1 + delRecOff U_int i + 1 < 2 ^ w by omega,
              hEiS], rfl, rfl, rfl⟩
        by_cases hEmit : ei ∈ G0.E ∧ ei ∈ activeE
        · have hPres1 : t2.mem (ePresBase + ei) = 1 := by simp [t2, t1, hPresS, hEmit.1]
          have hSlotNZ : t2.mem (slots + ei) ≠ 0 := by rw [show t2.mem _ = mem (slots + ei) from hSlotS]; exact (hSlots ei heiIntCap).mpr hEmit.2
          let a0 := outPtr + 2 * pref.length
          let t3 := { t2 with mem := Function.update t2.mem a0 0 }
          let t4 := { t3 with mem := Function.update t3.mem (a0 + 1) ei }
          let t5 := { t4 with regs := Function.update t4.regs 8 (pref.length + 1) }
          let t6 := { t5 with regs := Function.update t5.regs 5 (uIntBuf + 1 + delRecOff U_int (i + 1)) }
          have rt3 : Runs w p ω' (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 0)) t2 .normal t3 7 :=
            runs_store_iff.mpr ⟨a0, 0, by
              simp [Expr.eval, BinOp.eval, t2, t1, h3, h8, hw2, show 2 * pref.length < 2 ^ w by omega,
                show a0 < 2 ^ w by dsimp [a0]; omega, a0],
              by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
          have rt4 : Runs w p ω' (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 1)) (.reg 11))
              t3 .normal t4 9 :=
            runs_store_iff.mpr ⟨a0 + 1, ei, by
              simp [Expr.eval, BinOp.eval, t3, t2, t1, h3, h8, hw2, hw1, show 2 * pref.length < 2 ^ w by omega,
                show a0 < 2 ^ w by dsimp [a0]; omega, show a0 + 1 < 2 ^ w by dsimp [a0]; omega, a0],
              by simp [Expr.eval, t3, t2], rfl, rfl, rfl⟩
          have rt5 : Runs w p ω' (.assign 8 (.bin .add (.reg 8) (.const 1))) t4 .normal t5 4 :=
            runs_assign_iff.mpr ⟨pref.length + 1, by
              simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h8, hw1, show pref.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          have rInner : Runs w p ω' (.cond (.load (.bin .add (.reg 2) (.reg 11))) _ .nop) t2 .normal t5 27 :=
            runs_cond_iff.mpr ⟨t2.mem (slots + ei), 22, by
              simp [Expr.eval, BinOp.eval, t2, t1, h2, show slots + ei < 2 ^ w by omega],
              by simp only [hSlotNZ, ↓reduceIte]
                 exact runs_seq_iff.mpr (Or.inr ⟨t3, 7, _, rt3, runs_seq_iff.mpr (Or.inr ⟨t4, 9, 4, rt4, rt5, rfl⟩), rfl⟩),
              by simp [Expr.size]⟩
          have rOuter : Runs w p ω' (.cond (.load (.bin .add (.reg 7) (.reg 11))) _ .nop) t2 .normal t5 32 :=
            runs_cond_iff.mpr ⟨1, 27, by
              simp [Expr.eval, BinOp.eval, t2, t1, h7, show ePresBase + ei < 2 ^ w by omega, hPresS, hEmit.1],
              by simpa using rInner, by simp [Expr.size]⟩
          have rt6 : Runs w p ω' (.assign 5 (.bin .add (.reg 5) (.const 2))) t5 .normal t6 4 :=
            runs_assign_iff.mpr ⟨uIntBuf + 1 + delRecOff U_int (i + 1), by
              simp only [Expr.eval, BinOp.eval, t5, t4, t3, t2, t1, h5, hw2,
                show uIntBuf + 1 + delRecOff U_int i + 2 < 2 ^ w by omega, ↓reduceIte, Option.some.injEq,
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 8),
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 11),
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 10)]
              omega, rfl, rfl, rfl⟩
          have rElse : Runs w p ω' _ t1 .normal t6 (5 + (32 + 4 + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2, runs_seq_iff.mpr (Or.inr ⟨t5, 32, 4, rOuter, rt6, rfl⟩), rfl⟩)
          have rCond : Runs w p ω'
              (.cond (.bin .eq (.reg 10) (.const 0)) (.assign 5 (.bin .add (.reg 5) (.const 4))) _)
              t1 .normal t6 (3 + (5 + (32 + 4 + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, show 0 < 2 ^ w by omega],
              by simpa using rElse, by simp [Expr.size]⟩
          have hInvN : Inv (i + 1) { t6 with regs := Function.update t6.regs 9 (i + 1) } := by
            have hSingle : deletedTreeEdits G0.E activeE [.delete ei] = [.delete ei] := by
              simp [deletedTreeEdits, hEmit]
            dsimp only [Inv]; rw [hTakeNext, hUi, hSingle, List.length_append, List.length_singleton]
            refine ⟨by simp [t6, t5, t4, t3, t2, t1, h0], by simp [t6, t5, t4, t3, t2, t1, h1],
              by simp [t6, t5, t4, t3, t2, t1, h2], by simp [t6, t5, t4, t3, t2, t1, h3],
              by simp [t6, t5, t4, t3, t2, t1, h4], by simp [t6],
              by simp [t6, t5, t4, t3, t2, t1, h7], by simp [t6, t5], by simp, ?_, ?_, ?_⟩
            · refine treeEditsAt_append_singleton
                (treeEditsAt_of_agree hAt (fun j hj => by
                  simp only [t6, t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp [a0]; omega : outPtr + j ≠ a0 + 1),
                    Function.update_of_ne (by dsimp [a0]; omega : outPtr + j ≠ a0)]))
                (by simp [t6, t5, t4, t3, a0, treeChangeTag])
                (by simp [t6, t5, t4, t3, a0, treeChangeEdge])
            · intro a ha
              simp only [t6, t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0 + 1),
                Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0)]
              exact hzS a (by omega)
            · intro a ha
              simp only [t6, t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0 + 1),
                Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0)]
              exact hFr a ha
          refine ⟨.normal, t6, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩),
            ⟨hInvN, by simp [t6, t5, t4, t3, t2, t1, h9]⟩, by dsimp [stepCost]; omega⟩
        · let emitThen : Stmt :=
            .cond (.load (.bin .add (.reg 2) (.reg 11)))
              (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 0) ;;
               .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 1)) (.reg 11) ;;
               .assign 8 (.bin .add (.reg 8) (.const 1)))
              .nop
          have rOuter : ∃ cO, Runs w p ω' (.cond (.load (.bin .add (.reg 7) (.reg 11))) emitThen .nop) t2 .normal t2 cO ∧ cO ≤ 12 := by
            by_cases hG0m : ei ∈ G0.E
            · have hNotAct : ei ∉ activeE := fun ha => hEmit ⟨hG0m, ha⟩
              have hSlot0 : s.mem (slots + ei) = 0 := by
                by_contra hne; exact hNotAct ((hSlots ei heiIntCap).mp (hSlotS ▸ hne))
              have rIn : Runs w p ω' emitThen t2 .normal t2 6 :=
                runs_cond_iff.mpr ⟨0, 1, by
                  simp [Expr.eval, BinOp.eval, t2, t1, h2, show slots + ei < 2 ^ w by omega, hSlot0],
                  by simp [runs_nop_iff], by simp [Expr.size]⟩
              exact ⟨11, runs_cond_iff.mpr ⟨1, 6, by
                simp [Expr.eval, BinOp.eval, t2, t1, h7, show ePresBase + ei < 2 ^ w by omega, hPresS, hG0m],
                by simpa using rIn, by simp [Expr.size]⟩, by omega⟩
            · exact ⟨6, runs_cond_iff.mpr ⟨0, 1, by
                simp [Expr.eval, BinOp.eval, t2, t1, h7, show ePresBase + ei < 2 ^ w by omega, hPresS, hG0m],
                by simp [runs_nop_iff], by simp [Expr.size]⟩, by omega⟩
          obtain ⟨cO, rO, hcO⟩ := rOuter
          let t3 := { t2 with regs := Function.update t2.regs 5 (uIntBuf + 1 + delRecOff U_int (i + 1)) }
          have rt3 : Runs w p ω' (.assign 5 (.bin .add (.reg 5) (.const 2))) t2 .normal t3 4 :=
            runs_assign_iff.mpr ⟨uIntBuf + 1 + delRecOff U_int (i + 1), by
              simp only [Expr.eval, BinOp.eval, t2, t1, h5, hw2,
                show uIntBuf + 1 + delRecOff U_int i + 2 < 2 ^ w by omega, ↓reduceIte, Option.some.injEq,
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 11),
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 10)]
              omega, rfl, rfl, rfl⟩
          have rElse : Runs w p ω' _ t1 .normal t3 (5 + (cO + 4 + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2, runs_seq_iff.mpr (Or.inr ⟨t2, cO, 4, rO, rt3, rfl⟩), rfl⟩)
          have rCond : Runs w p ω'
              (.cond (.bin .eq (.reg 10) (.const 0)) (.assign 5 (.bin .add (.reg 5) (.const 4))) _)
              t1 .normal t3 (3 + (5 + (cO + 4 + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, show 0 < 2 ^ w by omega],
              by simpa using rElse, by simp [Expr.size]⟩
          have hInvN : Inv (i + 1) { t3 with regs := Function.update t3.regs 9 (i + 1) } := by
            have hSingle : deletedTreeEdits G0.E activeE [.delete ei] = [] := by
              simp [deletedTreeEdits, hEmit]
            dsimp only [Inv]; rw [hTakeNext, hUi, hSingle, List.append_nil]
            exact ⟨by simp [t3, t2, t1, h0], by simp [t3, t2, t1, h1], by simp [t3, t2, t1, h2],
              by simp [t3, t2, t1, h3], by simp [t3, t2, t1, h4], by simp [t3],
              by simp [t3, t2, t1, h7], by simp [t3, t2, t1, h8], by simp, hAt, hzS, hFr⟩
          refine ⟨.normal, t3, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩),
            ⟨hInvN, by simp [t3, t2, t1, h9]⟩, by dsimp [stepCost]; omega⟩)
  obtain ⟨o, out, cLoop, rLoop, hout, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨_, _, _, _, _, _, _, h8End, _, hAtEnd, hzEnd, hFrEnd⟩ := hout
    rw [List.take_length] at h8End hAtEnd hzEnd
    have rRet : Runs w p ω (.ret (.reg 8)) out (.returned (deletedTreeEdits G0.E activeE U_int).length) out 2 :=
      runs_ret_iff.mpr ⟨_, by simp [Expr.eval, h8End], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 8, _, r4,
            runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
              runs_seq_iff.mpr (Or.inr ⟨out, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨out, _, rAll, ?_, hAtEnd, hzEnd, hFrEnd⟩
    have hrc : rangeCost (fun _ => stepCost) 0 U_int.length = U_int.length * stepCost := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    have hm : U_int.length * stepCost + U_int.length * 9 = 64 * U_int.length := by dsimp [stepCost]; ring
    omega

/-! ### 2. Refreshing one replaced edge's threshold and canonical `PathEdgeAt` record -/

/-- Heap words allocated by `wireRefreshOneAccountBody`. -/
@[expose] def wireRefreshOneSpace (L : ℕ) : ℕ :=
  Num.fixedDivideSpace L + 8 * L + 5

/-- Step bound for `wireRefreshOneAccountBody`. -/
@[expose] def wireRefreshOneCost (L : ℕ) : ℕ :=
  2700 * L ^ 2 + 3350 * L + 1300

/-- Procedure `[oldRecPtr, oldThrPtr, gPtr, lPtr, negEpsPtr, L, P, heap]` (`reg 0..7`):
computes `thrNew = detectorThreshold P ε lNew`, `acc = detOld + thrOld`, `detNew = acc - thrNew`,
writes canonical `PathEdgeAt` `[1, 1, gNew, lNew, oldFlow, detNew]` at `recNew`, checks
`isNegBit = isNeg detNew`, stores `[thrNewPtr, recNew, isNegBit]` at `[nextHeap - 3, nextHeap)`,
and returns `nextHeap = heap + wireRefreshOneSpace L`. -/
@[expose] def wireRefreshOneAccountBody (divide add sub negate copy isNeg : ℕ) : Stmt :=
  .call 8 divide [.reg 4, .reg 3, .reg 5, .reg 6, .reg 7] ;;
  .assign 9 (.bin .sub (.reg 8) (.reg 5)) ;;
  .call 10 negate [.reg 9, .reg 5, .reg 8] ;;
  .assign 11 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 3) (.reg 5))) ;;
  .call 12 add [.reg 11, .reg 1, .reg 5, .reg 10] ;;
  .call 13 sub [.reg 10, .reg 8, .reg 5, .reg 12] ;;
  .assign 14 (.bin .add (.reg 12) (.reg 5)) ;;
  .store (.reg 13) (.const 1) ;;
  .store (.bin .add (.reg 13) (.const 1)) (.const 1) ;;
  .call 15 copy [.reg 2, .bin .add (.reg 13) (.const 2), .reg 5] ;;
  .call 15 copy [.reg 3, .bin .add (.bin .add (.reg 13) (.const 2)) (.reg 5), .reg 5] ;;
  .call 15 copy [.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 5)),
    .bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 5)), .reg 5] ;;
  .call 15 copy [.reg 14,
    .bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 3) (.reg 5)), .reg 5] ;;
  .call 16 isNeg [.reg 14, .reg 5] ;;
  .assign 17 (.bin .add (.reg 13) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 5)))) ;;
  .store (.reg 17) (.reg 8) ;;
  .store (.bin .add (.reg 17) (.const 1)) (.reg 13) ;;
  .store (.bin .add (.reg 17) (.const 2)) (.reg 16) ;;
  .ret (.bin .add (.reg 17) (.const 3))

theorem wireRefreshOneAccountBody_noRand (divide add sub negate copy isNeg : ℕ) :
    (wireRefreshOneAccountBody divide add sub negate copy isNeg).NoRand := by
  simp [wireRefreshOneAccountBody, Stmt.NoRand]

end MinCostFlow.MinRatio
