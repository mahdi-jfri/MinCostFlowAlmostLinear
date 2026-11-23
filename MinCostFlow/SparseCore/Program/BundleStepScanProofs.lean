module

public import MinCostFlow.SparseCore.Program.BundleStepScanGroup

/-!
# Full Phase 2 verification, exactness, and potential telescoping (`BundleStepScanProofs`)

Proves:
1. `bundleStepScan_runs`: end-to-end verification of `bundleStepScanStmt bTourLen bTourList`.
2. `scanCands_eq_exactSplitCands`: exact equality between Phase 2's candidate sets and
   `exactSplitCands` (`BundleModelBridge.lean`) via `splitCands_exact_iff`.
3. `scanNonMaxSum_le_tourPot_drop`: telescoping of the smaller-side root-scan work into
   `tourPot R_old cord - tourPot R_new cord'` via `tourPotTerm_sum_split`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical

/-- Offset (in words) of group `k` inside concatenated group records `gs`. -/
def groupOffset (gs : List (List ℕ)) (k : ℕ) : ℕ :=
  ((gs.take k).map fun G => 1 + G.length).sum

/-- Candidate sets produced by scanning groups `0..k-1` with maximal indices `maxIdxs`. -/
noncomputable def addCandsForGroups {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) : ℕ → Fin slotCap → Finset ℕ
  | 0 => cand₀
  | k + 1 =>
    addCandsForGroupPrefix S cord' (gs.getD k []) (maxIdxs.getD k 0)
      (addCandsForGroups S cord' gs maxIdxs cand₀ k) (gs.getD k []).length

/-- Scanned candidate-bundle ends accumulated across groups `0..k-1` with maximal indices `maxIdxs`. -/
noncomputable def addScanEndsForGroups {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) :
    ℕ → Fin slotCap → List (ℕ × ℕ × ℕ)
  | 0 => scan₀
  | k + 1 =>
    addScanEndsForGroupPrefix S cord' (gs.getD k []) (maxIdxs.getD k 0)
      (addCandsForGroups S cord' gs maxIdxs cand₀ k)
      (addScanEndsForGroups S cord' gs maxIdxs cand₀ scan₀ k) (gs.getD k []).length

/-- Total non-maximal tour length scanned across all groups `gs` given maximal indices `maxIdxs`. -/
def totalNonMaxLen (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ) : ℕ :=
  ∑ gi ∈ Finset.range gs.length,
    ∑ j ∈ (Finset.range (gs.getD gi []).length).erase (maxIdxs.getD gi 0),
      (cord' ((gs.getD gi []).getD j 0)).length

end

public section

open Classical

/-! ## 1. Helper lemmas for `readGroups`, `groupOffset`, and `forRange` with accumulated work -/

lemma readGroups_length (mem : ℕ → ℕ) (ptr g : ℕ) :
    (readGroups mem ptr g).length = g := by
  induction g generalizing ptr with
  | zero => rfl
  | succ g ih => simp [readGroups, ih]

lemma groupOffset_zero (gs : List (List ℕ)) : groupOffset gs 0 = 0 := by
  simp [groupOffset]

lemma groupOffset_succ (gs : List (List ℕ)) {k : ℕ} (hk : k < gs.length) :
    groupOffset gs (k + 1) = groupOffset gs k + 1 + gs[k].length := by
  simp only [groupOffset, List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]
  omega

lemma groupOffset_full (gs : List (List ℕ)) : groupOffset gs gs.length = groupsWords gs := by
  simp [groupOffset, groupsWords, List.take_length]

lemma groupOffset_mono (gs : List (List ℕ)) {a b : ℕ} (hab : a ≤ b) :
    groupOffset gs a ≤ groupOffset gs b := by
  induction hab with
  | refl => exact le_refl _
  | @step m _ ih =>
    by_cases hm : m < gs.length
    · rw [groupOffset_succ gs hm]; omega
    · have htake : gs.take (m + 1) = gs.take m := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simpa [groupOffset, htake] using ih

lemma readGroups_getElem_mem {mem : ℕ → ℕ} {ptr g : ℕ} {gs : List (List ℕ)}
    (hgs : readGroups mem ptr g = gs) :
    ∀ k (hk : k < gs.length),
      mem (ptr + groupOffset gs k) = gs[k].length ∧
      ListAt mem (ptr + groupOffset gs k + 1) gs[k] := by
  induction g generalizing ptr gs with
  | zero =>
    intro k hk; subst hgs; simp [readGroups] at hk
  | succ g ih =>
    subst hgs
    intro k hk
    cases k with
    | zero =>
      simp only [readGroups, groupOffset_zero, add_zero, List.getElem_cons_zero]
      refine ⟨by simp, fun j hj => ?_⟩
      simp only [List.length_map, List.length_range] at hj
      simp
    | succ k' =>
      have hk' : k' < (readGroups mem (ptr + 1 + mem ptr) g).length := by
        simp only [readGroups, List.length_cons] at hk; omega
      have hsub := ih (ptr := ptr + 1 + mem ptr) rfl k' hk'
      have hoff : groupOffset (((List.range (mem ptr)).map fun j => mem (ptr + 1 + j)) ::
            readGroups mem (ptr + 1 + mem ptr) g) (k' + 1) =
          1 + mem ptr + groupOffset (readGroups mem (ptr + 1 + mem ptr) g) k' := by
        simp [groupOffset]
      have haddr : ptr + groupOffset (((List.range (mem ptr)).map fun j => mem (ptr + 1 + j)) ::
            readGroups mem (ptr + 1 + mem ptr) g) (k' + 1) =
          (ptr + 1 + mem ptr) + groupOffset (readGroups mem (ptr + 1 + mem ptr) g) k' := by
        rw [hoff]; omega
      simp only [readGroups, List.getElem_cons_succ]
      rw [haddr]
      exact hsub

lemma mem_addCandsForGroups_iff {slotCap : ℕ} {S : BundleTableState slotCap}
    {cord' : ℕ → List End} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    {cand₀ : Fin slotCap → Finset ℕ} {j : Fin slotCap} {B : BundleState}
    (hSj : S j = some B) (hnd : ∀ G ∈ gs, ∀ w ∈ G, (cord' w).Nodup) :
    ∀ k ≤ gs.length, ∀ b,
      b ∈ addCandsForGroups S cord' gs maxIdxs cand₀ k j ↔
        b ∈ cand₀ j ∨
          (b ∈ B.vertices ∧ ∃ gi, ∃ (_hgi : gi < k) (hgi' : gi < gs.length),
            ∃ t, ∃ (_ht : t < gs[gi].length), t ≠ maxIdxs.getD gi 0 ∧
              0 < ((B.ends b).filter fun x => x ∈ cord' (gs[gi][t])).card ∧
              ((B.ends b).filter fun x => x ∈ cord' (gs[gi][t])).card < (B.ends b).card) := by
  intro k
  induction k with
  | zero => intro _ b; simp [addCandsForGroups]
  | succ k ih =>
    intro hk b
    have hkG : k < gs.length := by omega
    have hgetk : gs.getD k [] = gs[k] := List.getD_eq_getElem gs [] hkG
    have ih' := ih (by omega) b
    simp only [addCandsForGroups, hgetk]
    rw [mem_addCandsForGroupPrefix_iff hSj (hnd _ (List.getElem_mem hkG)) _ (le_refl _), ih']
    constructor
    · rintro ((h0 | ⟨hbV, gi, hgi, hgi', t, ht, hne, h1, h2⟩) | ⟨hbV, t, ht, _, hne, h1, h2⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨hbV, gi, by omega, hgi', t, ht, hne, h1, h2⟩
      · exact Or.inr ⟨hbV, k, by omega, hkG, t, ht, hne, h1, h2⟩
    · rintro (h0 | ⟨hbV, gi, hgi, hgi', t, ht, hne, h1, h2⟩)
      · exact Or.inl (Or.inl h0)
      · by_cases hgk : gi = k
        · subst hgk; exact Or.inr ⟨hbV, t, ht, ht, hne, h1, h2⟩
        · exact Or.inl (Or.inr ⟨hbV, gi, by omega, hgi', t, ht, hne, h1, h2⟩)

lemma addCandsForGroups_append_max {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (ms : List ℕ) (m : ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) :
    ∀ k ≤ ms.length,
      addCandsForGroups S cord' gs (ms ++ [m]) cand₀ k =
        addCandsForGroups S cord' gs ms cand₀ k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [addCandsForGroups, ih (by omega)]
    have hget : (ms ++ [m]).getD k 0 = ms.getD k 0 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega),
        List.getElem_append_left (by omega)]
    rw [hget]

lemma addScanEndsForGroups_append_max {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (ms : List ℕ) (m : ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) :
    ∀ k ≤ ms.length,
      addScanEndsForGroups S cord' gs (ms ++ [m]) cand₀ scan₀ k =
        addScanEndsForGroups S cord' gs ms cand₀ scan₀ k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [addScanEndsForGroups, ih (by omega), addCandsForGroups_append_max S cord' gs ms m cand₀ k (by omega)]
    have hget : (ms ++ [m]).getD k 0 = ms.getD k 0 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega),
        List.getElem_append_left (by omega)]
    rw [hget]

private lemma scanSpace_take_succ (TS : BundleTourSpec) (cord' : ℕ → List End)
    (gs : List (List ℕ)) {k : ℕ} (hk : k < gs.length) :
    bundleStepScanSpace TS cord' (gs.take (k + 1)) =
      bundleStepScanSpace TS cord' (gs.take k) +
        TS.querySpace * gs[k].length +
        (gs[k].map fun v => TS.listSpace (cord' v).length + 3 * (cord' v).length).sum := by
  unfold bundleStepScanSpace groupsTotalLen
  simp only [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]
  ring

private lemma scanSpace_take_le (TS : BundleTourSpec) (cord' : ℕ → List End)
    (gs : List (List ℕ)) {k : ℕ} (hk : k ≤ gs.length) :
    bundleStepScanSpace TS cord' (gs.take k) ≤ bundleStepScanSpace TS cord' gs := by
  have hmono : ∀ a b, a ≤ b → b ≤ gs.length →
      bundleStepScanSpace TS cord' (gs.take a) ≤ bundleStepScanSpace TS cord' (gs.take b) := by
    intro a b hab
    induction hab with
    | refl => intro _; exact le_refl _
    | @step m _ ih =>
      intro hm
      rw [scanSpace_take_succ TS cord' gs (by omega)]
      have := ih (by omega); omega
  simpa [List.take_length] using hmono k gs.length hk (le_refl _)

private lemma runs_forRange_accum {w r n : ℕ} {pProg : Program} {ω : ℕ → Bool} {s : Stmt}
    {α : Type*} (InvA : ℕ → α → State → Prop) (phiA : α → State → ℕ)
    (baseStep : ℕ → ℕ) (workOf : α → ℕ) (stInit : State) (aInit : α)
    (hw2 : 2 ≤ 2 ^ w) (hn : n < 2 ^ w) (hn1 : ∀ i < n, i + 1 < 2 ^ w)
    (hinit : Expr.eval w stInit (.const 0) = some 0 ∧
      InvA 0 aInit { stInit with regs := Function.update stInit.regs r 0 } ∧ workOf aInit = 0)
    (hreg : ∀ i a st, i ≤ n → InvA i a st → st.regs r = i)
    (hhi : ∀ i a st, i ≤ n → InvA i a st → st.regs 2 = n)
    (hstep : ∀ i a st, i < n → InvA i a st →
      ∃ st1 c1 a1, Runs w pProg ω s st .normal st1 c1 ∧ st1.regs r = i ∧
        InvA (i + 1) a1 { st1 with regs := Function.update st1.regs r (i + 1) } ∧
        workOf a ≤ workOf a1 ∧
        c1 + phiA a1 { st1 with regs := Function.update st1.regs r (i + 1) } ≤
          baseStep i + (workOf a1 - workOf a) + phiA a st) :
    ∃ stEnd cEnd aEnd,
      Runs w pProg ω (forRange r (.const 0) (.reg 2) s) stInit .normal stEnd cEnd ∧
      InvA n aEnd stEnd ∧
      cEnd + phiA aEnd stEnd ≤
        rangeCost baseStep 0 n + workOf aEnd + 9 * n + 7 +
          phiA aInit { stInit with regs := Function.update stInit.regs r 0 } := by
  have h1_w : 1 < 2 ^ w := by omega
  have hloop : ∀ d k (hd : k + d = n) a st, InvA k a st →
      ∃ stEnd cEnd aEnd,
        Runs w pProg ω (.loop (.bin .lt (.reg r) (.reg 2)) (s ;; .assign r (.bin .add (.reg r) (.const 1))))
          st .normal stEnd cEnd ∧
        InvA n aEnd stEnd ∧
        workOf a ≤ workOf aEnd ∧
        cEnd + phiA aEnd stEnd ≤
          rangeCost baseStep k n + (workOf aEnd - workOf a) + 9 * d + 4 + phiA a st := by
    intro d
    induction d with
    | zero =>
      intro k hd a st hI
      have hkn : k = n := by omega
      subst hkn
      have hcond0 : Expr.eval w st (.bin .lt (.reg r) (.reg 2)) = some 0 := by
        simp [Expr.eval, BinOp.eval, hreg _ _ _ (le_refl _) hI, hhi _ _ _ (le_refl _) hI,
          show 0 < 2 ^ w by omega]
      refine ⟨st, 4, a, runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
        hI, le_refl _, by simp [rangeCost]⟩
    | succ d ih =>
      intro k hd a st hI
      have hk_lt : k < n := by omega
      obtain ⟨st1, c1, a1, hs1, hr1, hI1, hwk, hc1⟩ := hstep k a st hk_lt hI
      set st2 := { st1 with regs := Function.update st1.regs r (k + 1) }
      have hinc : Runs w pProg ω (.assign r (.bin .add (.reg r) (.const 1))) st1 .normal st2 4 :=
        runs_assign_iff.mpr ⟨k + 1, by simp [Expr.eval, BinOp.eval, hr1, h1_w, hn1 k hk_lt], rfl, rfl, rfl⟩
      obtain ⟨stEnd, cEnd, aEnd, hrest, hIEnd, hwk2, hcEnd⟩ := ih (k + 1) (by omega) a1 st2 hI1
      have hcond1 : Expr.eval w st (.bin .lt (.reg r) (.reg 2)) = some 1 := by
        simp [Expr.eval, BinOp.eval, hreg _ _ _ (by omega) hI, hhi _ _ _ (by omega) hI, hk_lt, h1_w]
      have hrun := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, c1 + 4 + 1, cEnd, hcond1, by decide,
        bundle_runs_seq_normal hs1 hinc, hrest, rfl⟩))
      have hrc_s : rangeCost baseStep k n = baseStep k + rangeCost baseStep (k + 1) n := by
        unfold rangeCost
        have hsub : n - k = (n - (k + 1)) + 1 := by omega
        rw [hsub, List.range'_succ]; simp
      refine ⟨stEnd, _, aEnd, hrun, hIEnd, le_trans hwk hwk2, ?_⟩
      simp only [Expr.size] at *
      omega
  set st0 := { stInit with regs := Function.update stInit.regs r 0 }
  have ha0 : Runs w pProg ω (.assign r (.const 0)) stInit .normal st0 2 :=
    runs_assign_iff.mpr ⟨0, hinit.1, rfl, rfl, rfl⟩
  obtain ⟨stEnd, cEnd, aEnd, hrunL, hIEnd, _, hcEnd⟩ := hloop n 0 (by omega) aInit st0 hinit.2.1
  refine ⟨stEnd, 2 + cEnd + 1, aEnd, bundle_runs_seq_normal ha0 hrunL, hIEnd, ?_⟩
  rw [hinit.2.2, Nat.sub_zero] at hcEnd; omega

/-! ## 2. Full Phase 2 verification (`bundleStepScan_runs`) -/

/-- End-to-end verification of `bundleStepScanStmt bTourLen bTourList`:
`args = [tbl, tourH, gs.length, groupPtr, touchedCountPtr, touchedBufPtr, h₀]`. -/
theorem bundleStepScan_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH groupPtr touchedCountPtr touchedBufPtr h₀ pos : ℕ}
    {pProg : Program} {bTourList bTourLen bTourOwner : ℕ}
    (htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched₀ : List ℕ}
    {gs : List (List ℕ)} {cord' : ℕ → List End} {tx₀ : htour.rep.τ}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ p c, m.slotBlocks js = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (_htcnt_w : touchedCountPtr < 2 ^ w)
    (htouch_w : touchedBufPtr + slotCap < 2 ^ w)
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_ends_lt : ∀ G ∈ gs, ∀ v ∈ G, ∀ x ∈ cord' v, x.1 < eCap)
    (hgs_nd : ∀ G ∈ gs, ∀ v ∈ G, (cord' v).Nodup)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < h₀)
    (htouch_lt : touchedBufPtr + slotCap ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (htcnt_lt : touchedCountPtr < h₀)
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (htouch_disj_cur : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ bundleTableFoot eCap tbl m a)
    (hgrp_disj_touch : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (htcnt_not_foot : ¬ bundleTableCoreFoot eCap tbl m touchedCountPtr)
    (htcnt_not_cur : touchedCountPtr < btCurBunBase tbl slotCap eCap ∨
      btCurTagBase tbl slotCap eCap + slotCap ≤ touchedCountPtr)
    (htcnt_not_touch : touchedCountPtr < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ touchedCountPtr)
    (htcnt_not_grp : touchedCountPtr < groupPtr ∨ groupPtr + groupsWords gs ≤ touchedCountPtr)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_disj_touch : ∀ a, htour.rep.foot tourH tx₀ a →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a →
      a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_not_tcnt : ¬ htour.rep.foot tourH tx₀ touchedCountPtr)
    (hzero : ZeroFrom mem₀ h₀)
    (hh_sp : h₀ + bundleStepScanSpace TS cord' gs < 2 ^ w)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hafter₀ : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ mem₀)
    (htouch₀ : ListAt mem₀ touchedBufPtr touched₀)
    (hcur₀ : ∀ s < slotCap,
      mem₀ (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      mem₀ (btCurTagBase tbl slotCap eCap + s) = 0)
    (htcnt_mem : mem₀ touchedCountPtr = touched₀.length) :
    let S := tableDelEdges S₀ D
    ∃ st' c h' tx' maxIdxs touched',
      Runs w pProg ω (bundleStepScanStmt bTourLen bTourList)
        (startState [tbl, tourH, gs.length, groupPtr, touchedCountPtr, touchedBufPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      maxIdxs.length = gs.length ∧
      (∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
        ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepScanSpace TS cord' gs ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
        (addCandsForGroups S cord' gs maxIdxs cand₀ gs.length) touched' st'.mem ∧
      ListAt st'.mem touchedBufPtr touched' ∧
      SlotScanListAt slotCap eCap tbl st'.mem h₀ h'
        (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gs.length) ∧
      (∀ js : Fin slotCap, ScanNodesIn st'.mem (fun a => ¬ htour.rep.foot tourH tx' a)
        (st'.mem (btCurBunBase tbl slotCap eCap + js.1))
        (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gs.length js)) ∧
      st'.mem touchedCountPtr = touched'.length ∧
      (∀ a < h₀, ¬ bundleTableCoreFoot eCap tbl m a →
        (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
        (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) →
        a ≠ touchedCountPtr → ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepScanCost TS eCap gs +
        (TS.mul * ordStoreLog eCap + 360) * totalNonMaxLen cord' gs maxIdxs +
        htour.rep.phi tourH tx₀ mem₀ := by
  intro S
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
  have hgs_len_le : gs.length ≤ groupsWords gs := by
    have hgo : ∀ l : List (List ℕ), l.length ≤ groupsWords l := by
      intro l; induction l with
      | nil => simp [groupsWords]
      | cons G rest ih => simp [groupsWords]; omega
    exact hgo gs
  have hhdr_w : ∀ off < 12, tbl + off < 2 ^ w := fun off hoff => by clear * - htbl_w' hoff; omega
  set st0 := startState [tbl, tourH, gs.length, groupPtr, touchedCountPtr, touchedBufPtr, h₀] mem₀ pos
  set r7 := Function.update st0.regs 7 (btSlotPtrBase tbl)
  set r8 := Function.update r7 8 (btEdgeSlotBase tbl slotCap)
  set r9 := Function.update r8 9 (btEndBundleBase tbl slotCap eCap)
  set r10 := Function.update r9 10 (btSlotTouchedBase tbl slotCap eCap)
  set r11 := Function.update r10 11 (btSlotCandHeadBase tbl slotCap eCap)
  set r12 := Function.update r11 12 groupPtr
  set r13 := Function.update r12 13 touched₀.length
  set st_h : State := { st0 with regs := r13 }
  have hhdr_cps : ∀ {sTail : Stmt} {o : Outcome} {stF : State} {cTail : ℕ},
      Runs w pProg ω sTail st_h o stF cTail →
      Runs w pProg ω
        (.assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const 4))) ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const 5))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.const 8))) ;;
         .assign 11 (.load (.bin .add (.reg 0) (.const 11))) ;;
         .assign 12 (.reg 3) ;;
         .assign 13 (.load (.reg 4)) ;;
         sTail) st0 o stF (37 + cTail) := by
    intro sTail o stF cTail hTail
    have ha7 : Runs w pProg ω (.assign 7 (.load (.bin .add (.reg 0) (.const 3)))) st0 .normal { st0 with regs := r7 } 5 :=
      runs_assign_iff.mpr ⟨btSlotPtrBase tbl, by
        simp [Expr.eval, BinOp.eval, st0, startState, show 3 < 2 ^ w by omega, hhdr_w 3 (by decide)]
        exact hafter₀.2.2.2.1, rfl, rfl, rfl⟩
    have ha8 : Runs w pProg ω (.assign 8 (.load (.bin .add (.reg 0) (.const 4)))) { st0 with regs := r7 } .normal { st0 with regs := r8 } 5 :=
      runs_assign_iff.mpr ⟨btEdgeSlotBase tbl slotCap, by
        simp [Expr.eval, BinOp.eval, r7, st0, startState, show 4 < 2 ^ w by omega, hhdr_w 4 (by decide)]
        exact hafter₀.2.2.2.2.1, rfl, rfl, rfl⟩
    have ha9 : Runs w pProg ω (.assign 9 (.load (.bin .add (.reg 0) (.const 5)))) { st0 with regs := r8 } .normal { st0 with regs := r9 } 5 :=
      runs_assign_iff.mpr ⟨btEndBundleBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r8, r7, st0, startState, show 5 < 2 ^ w by omega, hhdr_w 5 (by decide)]
        exact hafter₀.2.2.2.2.2.1, rfl, rfl, rfl⟩
    have ha10 : Runs w pProg ω (.assign 10 (.load (.bin .add (.reg 0) (.const 8)))) { st0 with regs := r9 } .normal { st0 with regs := r10 } 5 :=
      runs_assign_iff.mpr ⟨btSlotTouchedBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r9, r8, r7, st0, startState, show 8 < 2 ^ w by omega, hhdr_w 8 (by decide)]
        exact hafter₀.2.2.2.2.2.2.2.2.1, rfl, rfl, rfl⟩
    have ha11 : Runs w pProg ω (.assign 11 (.load (.bin .add (.reg 0) (.const 11)))) { st0 with regs := r10 } .normal { st0 with regs := r11 } 5 :=
      runs_assign_iff.mpr ⟨btSlotCandHeadBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r10, r9, r8, r7, st0, startState, show 11 < 2 ^ w by omega, hhdr_w 11 (by decide)]
        exact hafter₀.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, rfl⟩
    have ha12 : Runs w pProg ω (.assign 12 (.reg 3)) { st0 with regs := r11 } .normal { st0 with regs := r12 } 2 :=
      runs_assign_iff.mpr ⟨groupPtr, by simp [Expr.eval, r11, r10, r9, r8, r7, st0, startState], rfl, rfl, rfl⟩
    have ha13 : Runs w pProg ω (.assign 13 (.load (.reg 4))) { st0 with regs := r12 } .normal st_h 3 :=
      runs_assign_iff.mpr ⟨touched₀.length, by
        simp [Expr.eval, r12, r11, r10, r9, r8, r7, st0, startState, htcnt_mem], rfl, rfl, rfl⟩
    exact (show 5 + (5 + (5 + (5 + (5 + (2 + (3 + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 37 + cTail by omega) ▸
      bundle_runs_seq_normal ha7 (bundle_runs_seq_normal ha8 (bundle_runs_seq_normal ha9
        (bundle_runs_seq_normal ha10 (bundle_runs_seq_normal ha11 (bundle_runs_seq_normal ha12
          (bundle_runs_seq_normal ha13 hTail))))))
  let Acc := ℕ × htour.rep.τ × List ℕ × List ℕ × ℕ
  let Inv : ℕ → Acc → State → Prop := fun gi acc st =>
    let (hCur, tx, maxIdxs, touched, extraWork) := acc
    (∀ r, r ≤ 11 → r ≠ 6 → st.regs r = st_h.regs r) ∧
    st.regs 6 = hCur ∧ st.regs 12 = groupPtr + groupOffset gs gi ∧
    st.regs 13 = touched.length ∧ st.regs 14 = gi ∧
    maxIdxs.length = gi ∧
    (∀ k (hk : k < gi) (hk' : k < gs.length), ∃ hm : maxIdxs.getD k 0 < gs[k].length,
      ∀ j (hj : j < gs[k].length), (cord' gs[k][j]).length ≤ (cord' gs[k][maxIdxs.getD k 0]).length) ∧
    extraWork = ∑ k ∈ Finset.range gi,
      ∑ j ∈ (Finset.range (gs.getD k []).length).erase (maxIdxs.getD k 0),
        (cord' ((gs.getD k []).getD j 0)).length ∧
    h₀ ≤ hCur ∧ hCur ≤ h₀ + bundleStepScanSpace TS cord' (gs.take gi) ∧
    ZeroFrom st.mem hCur ∧
    htour.rep.rep tourH cord' tx st.mem ∧
    (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < hCur)) ∧
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
      (addCandsForGroups S cord' gs maxIdxs cand₀ gi) touched st.mem ∧
    ListAt st.mem touchedBufPtr touched ∧
    SlotScanListAt slotCap eCap tbl st.mem h₀ hCur
      (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gi) ∧
    (∀ js : Fin slotCap, ScanNodesIn st.mem (fun a => ¬ htour.rep.foot tourH tx a)
      (st.mem (btCurBunBase tbl slotCap eCap + js.1))
      (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gi js)) ∧
    (∀ js : Fin slotCap, (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gi js).length ≤ hCur) ∧
    (∀ a < h₀, ¬ bundleTableCoreFoot eCap tbl m a →
      (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
      (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) →
      ¬ htour.rep.foot tourH tx₀ a → st.mem a = mem₀ a)
  let baseStep : ℕ → ℕ := fun gi =>
    (2 * TS.mul * ordStoreLog eCap + 170) * (gs.getD gi []).length + 61
  let workOf : Acc → ℕ := fun acc => (TS.mul * ordStoreLog eCap + 355) * acc.2.2.2.2
  let outerBody : Stmt :=
    .assign 15 (.load (.reg 12)) ;;
    .assign 16 (.bin .add (.reg 12) (.const 1)) ;;
    bundleStepScanMaxStmt bTourLen ;;
    forRange 19 (.const 0) (.reg 15)
      (.cond (.bin .eq (.reg 19) (.reg 17)) .nop (bundleStepScanRootStmt bTourList)) ;;
    .assign 12 (.bin .add (.bin .add (.reg 12) (.const 1)) (.reg 15))
  obtain ⟨st_loop, c_loop, ⟨hEnd, txEnd, maxIdxs, touchedEnd, extraWorkEnd⟩, hrun_loop, hInv_end, hc_loop⟩ :=
    runs_forRange_accum (w := w) (r := 14) (n := gs.length) (pProg := pProg) (ω := ω) (s := outerBody)
      Inv (fun acc st => htour.rep.phi tourH acc.2.1 st.mem) baseStep workOf st_h
      (h₀, tx₀, [], touched₀, 0) (by omega) (by omega) (fun i hi => by omega)
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, by simp [workOf]⟩
        refine ⟨fun r hr _ => by simp [show r ≠ 14 by omega],
          by simp [st_h, r13, r12, r11, r10, r9, r8, r7, st0, startState],
          by simp [st_h, r13, r12, groupOffset_zero],
          by simp [st_h, r13], by simp, rfl, fun _ h => by omega, by simp,
          le_refl _, by simp [bundleStepScanSpace, groupsTotalLen], hzero, htrep,
          fun _ h => Or.inl h, hafter₀, htouch₀, slotScanListAt_empty hcur₀,
          fun js => (hcur₀ js.1 js.2).1,
          fun _ => by simp [addScanEndsForGroups], fun _ _ _ _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.1)
      (fun _ _ st _ hI => by
        have hr2 := hI.1 2 (by decide) (by decide)
        simp [hr2, st_h, r13, r12, r11, r10, r9, r8, r7, st0, startState])
      (fun gi ⟨hCur, tx, ms, touched, ew⟩ st hgi hI => by
        rcases hI with ⟨hregs, hr6c, hr12c, hr13c, hr14c, hms_len, hms_max, hew_eq,
          hh0_le, hhCur_le, hzeroC, htrepC, htfootC, hafterC, htouchC, hscanC, hscanInC, hcntC, hfrC⟩
        set G := gs[gi]'hgi
        have hGlen : G.length = gs[gi].length := rfl
        set curPtr := groupPtr + groupOffset gs gi
        set wBase := curPtr + 1
        have hG_read := readGroups_getElem_mem hgs_mem gi hgi
        have hoff_succ := groupOffset_succ gs hgi
        have hoff_le : groupOffset gs (gi + 1) ≤ groupsWords gs := by
          rw [← groupOffset_full gs]; exact groupOffset_mono gs (by omega)
        have hgrp_disj_cur : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
            a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a := fun a ha1 ha2 => by
          by_contra hnot; push Not at hnot
          exact hgrp_disj_foot a ha1 ha2 (Or.inl ⟨by unfold btCurBunBase at hnot; omega,
            by unfold btCurTagBase at hnot; unfold bundleTableFixedSize; omega⟩)
        have hcur_eq : st.mem curPtr = G.length := by
          rw [hfrC curPtr (by omega)
            (fun hf => hgrp_disj_foot curPtr (by omega) (by omega) (bundleTableCoreFoot_subset_foot hf))
            (hgrp_disj_cur curPtr (by omega) (by omega))
            (hgrp_disj_touch curPtr (by omega) (by omega))
            (fun ht => by have := htfoot_disj_grp curPtr ht; omega)]
          exact hG_read.1
        have hG_mem_st : ListAt st.mem wBase G := fun j hj => by
          rw [hfrC (wBase + j) (by omega)
            (fun hf => hgrp_disj_foot _ (by omega) (by omega) (bundleTableCoreFoot_subset_foot hf))
            (hgrp_disj_cur _ (by omega) (by omega))
            (hgrp_disj_touch _ (by omega) (by omega))
            (fun ht => by have := htfoot_disj_grp _ ht; omega)]
          exact hG_read.2 j hj
        set st1 : State := { st with regs := Function.update st.regs 15 G.length }
        set st2 : State := { st1 with regs := Function.update st1.regs 16 wBase }
        have ha15 : Runs w pProg ω (.assign 15 (.load (.reg 12))) st .normal st1 3 :=
          runs_assign_iff.mpr ⟨G.length, by simp [Expr.eval, hr12c, hcur_eq], rfl, rfl, rfl⟩
        have ha16 : Runs w pProg ω (.assign 16 (.bin .add (.reg 12) (.const 1))) st1 .normal st2 4 :=
          runs_assign_iff.mpr ⟨wBase, by
            simp [Expr.eval, BinOp.eval, st1, hr12c, h1_w, show curPtr + 1 < 2 ^ w by omega, wBase], rfl, rfl, rfl⟩
        have hsp_next_le := scanSpace_take_le TS cord' gs (k := gi + 1) (by omega)
        have hsp_succ := scanSpace_take_succ TS cord' gs hgi
        have htfoot_ltC : ∀ a, htour.rep.foot tourH tx a → a < hCur := fun a ha => by
          rcases htfootC a ha with h0 | ⟨_, hlt⟩
          · exact Nat.lt_of_lt_of_le (htfoot_lt a h0) hh0_le
          · exact hlt
        have htfoot_disj_tblC : ∀ a, htour.rep.foot tourH tx a → ¬ bundleTableFoot eCap tbl m a := fun a ha hf => by
          rcases htfootC a ha with h0 | ⟨ha1, _⟩
          · exact htfoot_disj_tbl a h0 hf
          · exact absurd (hfoot_lt a hf) (by omega)
        have htfoot_disj_touchC : ∀ a, htour.rep.foot tourH tx a →
            a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a := fun a ha => by
          rcases htfootC a ha with h0 | ⟨ha1, _⟩
          · exact htfoot_disj_touch a h0
          · exact Or.inr (by omega)
        have htfoot_disj_wBaseC : ∀ a, htour.rep.foot tourH tx a → a < wBase ∨ wBase + G.length ≤ a := fun a ha => by
          rcases htfootC a ha with h0 | ⟨ha1, _⟩
          · have := htfoot_disj_grp a h0; omega
          · exact Or.inr (by omega)
        obtain ⟨stG, cG, hG, txG, maxIdx, touchedG, hrunG, hregsG, hr6G, hr13G, hmaxG,
          hhC_leG, hhG_le, hzeroG, htrepG, htfootG, hafterG, htouchG, hscanG, hscanInG, hcntG, hfrG, hcG⟩ :=
          bundleStepScanGroup_runs (st₀ := st2) (ω := ω) (hStart := h₀) htour hw16 htourH_w hpk_w htbl_w hblks_w htouch_w
            (hgs_pos G (List.getElem_mem hgi)) (hgs_lt G (List.getElem_mem hgi))
            (hgs_ends_lt G (List.getElem_mem hgi)) (hgs_nd G (List.getElem_mem hgi))
            (by omega) hG_mem_st hh0_le hfoot_lt htouch_lt (by omega)
            htouch_disj_foot htouch_disj_cur
            (fun a ha1 ha2 => hgrp_disj_foot a (by omega) (by omega))
            (fun a ha1 ha2 => hgrp_disj_touch a (by omega) (by omega))
            htfoot_ltC htfoot_disj_tblC htfoot_disj_touchC htfoot_disj_wBaseC
            hzeroC (by dsimp only [G]; omega) htrepC hafterC htouchC hscanC hscanInC hcntC
            (by simp [st2, st1, hregs 0 (by decide) (by decide), st_h, r13, r12, r11, r10, r9, r8, r7, st0, startState])
            (by simp [st2, st1, hregs 1 (by decide) (by decide), st_h, r13, r12, r11, r10, r9, r8, r7, st0, startState])
            (by simp [st2, st1, hregs 5 (by decide) (by decide), st_h, r13, r12, r11, r10, r9, r8, r7, st0, startState])
            (by simp [st2, st1, hr6c])
            (by simp [st2, st1, hregs 7 (by decide) (by decide), st_h, r13, r12, r11, r10, r9, r8, r7])
            (by simp [st2, st1, hregs 8 (by decide) (by decide), st_h, r13, r12, r11, r10, r9, r8])
            (by simp [st2, st1, hregs 9 (by decide) (by decide), st_h, r13, r12, r11, r10, r9])
            (by simp [st2, st1, hregs 10 (by decide) (by decide), st_h, r13, r12, r11, r10])
            (by simp [st2, st1, hregs 11 (by decide) (by decide), st_h, r13, r12, r11])
            (by simp [st2, st1, hr13c]) (by simp [st2, st1]) (by simp [st2])
        set nextPtr := curPtr + 1 + G.length
        set stF : State := { stG with regs := Function.update stG.regs 12 nextPtr }
        have ha12_adv : Runs w pProg ω (.assign 12 (.bin .add (.bin .add (.reg 12) (.const 1)) (.reg 15)))
            stG .normal stF 6 :=
          runs_assign_iff.mpr ⟨nextPtr, by
            have hr12G : stG.regs 12 = curPtr := by rw [hregsG 12 (by decide) (by decide) (by decide)]; simp [st2, st1, hr12c]
            have hr15G : stG.regs 15 = G.length := by rw [hregsG 15 (by decide) (by decide) (by decide)]; simp [st2, st1]
            simp [Expr.eval, BinOp.eval, hr12G, hr15G, h1_w, show curPtr + 1 < 2 ^ w by omega,
              show curPtr + 1 + G.length < 2 ^ w by omega, nextPtr], rfl, rfl, rfl⟩
        have hrun_body : Runs w pProg ω outerBody st .normal stF (3 + (4 + (cG + 6 + 1) + 1) + 1) := by
          dsimp only [outerBody]
          rcases runs_seq_iff.mp hrunG with hret | ⟨s12, c1, c2, h1, h2, hc12⟩
          · obtain ⟨_, _, _, heq, _⟩ := hret; cases heq
          · have htail := bundle_runs_seq_normal h1 (bundle_runs_seq_normal h2 ha12_adv)
            have hc_eq : c1 + (c2 + 6 + 1) + 1 = cG + 6 + 1 := by omega
            exact bundle_runs_seq_normal ha15 (bundle_runs_seq_normal ha16 (hc_eq ▸ htail))
        set stepNonMax := ∑ j ∈ (Finset.range G.length).erase maxIdx, (cord' (G.getD j 0)).length
        set ms' := ms ++ [maxIdx]
        have hms'_get : ∀ k < gi, ms'.getD k 0 = ms.getD k 0 := fun k hk => by
          rw [List.getD_eq_getElem _ _ (by simp [ms']; omega), List.getD_eq_getElem _ _ (by omega),
            List.getElem_append_left (by omega)]
        have hms'_last : ms'.getD gi 0 = maxIdx := by
          rw [List.getD_eq_getElem _ _ (by simp [ms', hms_len])]
          simp [ms', hms_len]
        have hcand_step : addCandsForGroups S cord' gs ms' cand₀ (gi + 1) =
            addCandsForGroupPrefix S cord' G maxIdx (addCandsForGroups S cord' gs ms cand₀ gi) G.length := by
          simp only [addCandsForGroups, List.getD_eq_getElem gs [] hgi, hms'_last]
          rw [addCandsForGroups_append_max S cord' gs ms maxIdx cand₀ gi (by omega)]
        have hscan_step : addScanEndsForGroups S cord' gs ms' cand₀ (fun _ => []) (gi + 1) =
            addScanEndsForGroupPrefix S cord' G maxIdx (addCandsForGroups S cord' gs ms cand₀ gi)
              (addScanEndsForGroups S cord' gs ms cand₀ (fun _ => []) gi) G.length := by
          simp only [addScanEndsForGroups, List.getD_eq_getElem gs [] hgi, hms'_last]
          rw [addCandsForGroups_append_max S cord' gs ms maxIdx cand₀ gi (by omega),
            addScanEndsForGroups_append_max S cord' gs ms maxIdx cand₀ (fun _ => []) gi (by omega)]
        have hew_step : ew + stepNonMax = ∑ k ∈ Finset.range (gi + 1),
            ∑ j ∈ (Finset.range (gs.getD k []).length).erase (ms'.getD k 0),
              (cord' ((gs.getD k []).getD j 0)).length := by
          rw [Finset.sum_range_succ, hew_eq]
          congr 1
          · refine Finset.sum_congr rfl fun k hk => ?_
            rw [hms'_get k (Finset.mem_range.mp hk)]
          · rw [List.getD_eq_getElem gs [] hgi, hms'_last]
        refine ⟨stF, 3 + (4 + (cG + 6 + 1) + 1) + 1, (hG, txG, ms', touchedG, ew + stepNonMax),
          hrun_body, by simp [stF, hregsG 14 (by decide) (by decide) (by decide), st2, st1, hr14c], ?_,
          by simp [workOf], ?_⟩
        · refine ⟨fun r hr h6 => by
              simp only [Function.update_of_ne (show r ≠ 14 by omega), stF,
                Function.update_of_ne (show r ≠ 12 by omega)]
              by_cases h13 : r = 13
              · omega
              · rw [hregsG r (by omega) h6 h13]; simp [st2, st1, show r ≠ 16 by omega, show r ≠ 15 by omega, hregs r hr h6],
            by simp [stF, hr6G],
            by simp [stF, nextPtr, curPtr, hoff_succ, G, Nat.add_assoc],
            by simp [stF, hr13G], by simp,
            by simp [ms', hms_len],
            fun k hk hk' => by
              by_cases hkg : k = gi
              · subst hkg; rw [hms'_last]; exact hmaxG
              · rw [hms'_get k (by omega)]; exact hms_max k (by omega) hk',
            hew_step,
            le_trans hh0_le hhC_leG, by rw [hsp_succ]; dsimp only [G] at hhG_le; omega,
            hzeroG, htrepG,
            fun a ha => by
              rcases htfootG a ha with h1 | ⟨h1, h2⟩
              · rcases htfootC a h1 with h0 | ⟨ha1, ha2⟩
                · exact Or.inl h0
                · exact Or.inr ⟨ha1, Nat.lt_of_lt_of_le ha2 hhC_leG⟩
              · exact Or.inr ⟨le_trans hh0_le h1, h2⟩,
            hcand_step ▸ hafterG, htouchG,
            hscan_step ▸ hscanG, hscan_step ▸ hscanInG, hscan_step ▸ hcntG,
            fun a ha hnf hnc hout hntf => by
              have hntfC : ¬ htour.rep.foot tourH tx a := fun h => by
                rcases htfootC a h with h0 | ⟨ha1, _⟩
                · exact hntf h0
                · omega
              exact (hfrG a (Nat.lt_of_lt_of_le ha hh0_le) hnf hnc hout hntfC).trans (hfrC a ha hnf hnc hout hntf)⟩
        · simp only [workOf, baseStep, List.getD_eq_getElem gs [] hgi]
          have hsub : (TS.mul * ordStoreLog eCap + 355) * (ew + stepNonMax) -
              (TS.mul * ordStoreLog eCap + 355) * ew =
              (TS.mul * ordStoreLog eCap + 355) * stepNonMax := by
            rw [Nat.mul_add, Nat.add_sub_cancel_left]
          rw [hsub]; dsimp only [stF, st2, st1, G] at hcG ⊢; omega)
  -- Trailing store + ret
  rcases hInv_end with ⟨hregsE, hr6E, _, hr13E, _, hms_len, hms_max, hew_end,
    hh0_leE, hhEnd_le, hzeroE, htrepE, htfootE, hafterE, htouchE, hscanE, hscanInE, _, hfrE⟩
  rw [List.take_length] at hhEnd_le
  set st_final : State := { st_loop with mem := Function.update st_loop.mem touchedCountPtr touchedEnd.length }
  have htcnt_eq_r4 : st_loop.regs 4 = touchedCountPtr := by
    rw [hregsE 4 (by decide) (by decide)]; simp [st_h, r13, r12, r11, r10, r9, r8, r7, st0, startState]
  have htlen_w : touchedEnd.length < 2 ^ w := by
    have hle : touchedEnd.length ≤ slotCap := by
      have hc := Finset.card_le_card (show touchedEnd.toFinset ⊆ Finset.range slotCap from
        fun y hy => Finset.mem_range.mpr (hafterE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y (List.mem_toFinset.mp hy)))
      simpa [List.toFinset_card_of_nodup hafterE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using hc
    clear * - hle htbl_w'; omega
  have hst_tcnt : Runs w pProg ω (.store (.reg 4) (.reg 13)) st_loop .normal st_final 3 :=
    runs_store_iff.mpr ⟨touchedCountPtr, touchedEnd.length,
      by simp [Expr.eval, htcnt_eq_r4], by simp [Expr.eval, hr13E], rfl, rfl, rfl⟩
  have hret : Runs w pProg ω (.ret (.reg 6)) st_final (.returned hEnd) st_final 2 :=
    runs_ret_iff.mpr ⟨hEnd, by simp [Expr.eval, st_final, hr6E], rfl, rfl, rfl⟩
  have htcnt_not_tfootE : ¬ htour.rep.foot tourH txEnd touchedCountPtr := fun ht => by
    rcases htfootE touchedCountPtr ht with h0 | ⟨ha1, _⟩
    · exact htfoot_not_tcnt h0
    · omega
  have htrep_final : htour.rep.rep tourH cord' txEnd st_final.mem :=
    (htour.rep_local tourH cord' txEnd st_loop.mem st_final.mem fun a ha => by
      dsimp only [st_final]
      have hne : a ≠ touchedCountPtr := fun h => htcnt_not_tfootE (h ▸ ha)
      exact (Function.update_of_ne hne _ _).symm).1 htrepE
  have hphi_final : htour.rep.phi tourH txEnd st_final.mem = htour.rep.phi tourH txEnd st_loop.mem :=
    (htour.rep_local tourH cord' txEnd st_loop.mem st_final.mem fun a ha => by
      dsimp only [st_final]
      have hne : a ≠ touchedCountPtr := fun h => htcnt_not_tfootE (h ▸ ha)
      exact (Function.update_of_ne hne _ _).symm).2.symm
  have hafter_final : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
      (addCandsForGroups S cord' gs maxIdxs cand₀ gs.length) touchedEnd st_final.mem :=
    hafterE.of_agree fun a ha => by
      dsimp only [st_final]
      have hne : a ≠ touchedCountPtr := fun h => htcnt_not_foot (h ▸ ha)
      exact (Function.update_of_ne hne _ _).symm
  have htouch_final : ListAt st_final.mem touchedBufPtr touchedEnd := fun idx hidx => by
    have hle : touchedEnd.length ≤ slotCap := by
      have hc := Finset.card_le_card (show touchedEnd.toFinset ⊆ Finset.range slotCap from
        fun y hy => Finset.mem_range.mpr (hafterE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y (List.mem_toFinset.mp hy)))
      simpa [List.toFinset_card_of_nodup hafterE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using hc
    dsimp only [st_final]; rw [Function.update_of_ne (by omega)]
    exact htouchE idx hidx
  have hscan_final : SlotScanListAt slotCap eCap tbl st_final.mem h₀ hEnd
      (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gs.length) :=
    slotScanListAt_mono hscanE (le_refl _)
      (fun s hs => by
        dsimp only [st_final]
        have hne1 : btCurBunBase tbl slotCap eCap + s ≠ touchedCountPtr := by
          unfold btCurBunBase btCurTagBase at htcnt_not_cur; unfold btCurBunBase; omega
        have hne2 : btCurTagBase tbl slotCap eCap + s ≠ touchedCountPtr := by
          unfold btCurBunBase btCurTagBase at htcnt_not_cur; unfold btCurTagBase; omega
        exact ⟨Function.update_of_ne hne1 _ _, Function.update_of_ne hne2 _ _⟩)
      (fun a ha1 _ => by dsimp only [st_final]; exact Function.update_of_ne (by omega) _ _)
  have hscanIn_final : ∀ js : Fin slotCap,
      ScanNodesIn st_final.mem (fun a => ¬ htour.rep.foot tourH txEnd a)
        (st_final.mem (btCurBunBase tbl slotCap eCap + js.1))
        (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gs.length js) := fun js => by
    have hne1 : btCurBunBase tbl slotCap eCap + js.1 ≠ touchedCountPtr := by
      have := js.2; unfold btCurBunBase btCurTagBase at htcnt_not_cur; unfold btCurBunBase; omega
    dsimp only [st_final]; rw [Function.update_of_ne hne1]
    exact (scanNodesAt_mono_of_in (hscanE js).1 (hscanInE js) (le_refl _)
      (fun a ha1 _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ _ hp => hp)).2
  have hzero_final : ZeroFrom st_final.mem hEnd := fun a ha => by
    dsimp only [st_final]; rw [Function.update_of_ne (by omega)]; exact hzeroE a ha
  refine ⟨st_final, 37 + (c_loop + (3 + 2 + 1) + 1), hEnd, txEnd, maxIdxs, touchedEnd,
    hhdr_cps (bundle_runs_seq_normal hrun_loop (bundle_runs_seq_normal hst_tcnt hret)),
    hms_len, fun gi hgi => hms_max gi hgi hgi, hh0_leE, hhEnd_le, hzero_final, htrep_final,
    htfootE, hafter_final, htouch_final, hscan_final, hscanIn_final, by simp [st_final],
    fun a ha hnf hnc hout hntc hntf => by
      simp only [st_final, Function.update_of_ne hntc]; exact hfrE a ha hnf hnc hout hntf, ?_⟩
  rw [hphi_final]
  have hrc : rangeCost baseStep 0 gs.length =
      (2 * TS.mul * ordStoreLog eCap + 170) * groupsTotalLen gs + 61 * gs.length := by
    have hgo : ∀ k ≤ gs.length, rangeCost baseStep 0 k =
        (2 * TS.mul * ordStoreLog eCap + 170) * groupsTotalLen (gs.take k) + 61 * k := by
      intro k
      induction k with
      | zero => intro _; simp [rangeCost, groupsTotalLen]
      | succ k ih =>
        intro hk
        have hkG : k < gs.length := by omega
        rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton, ← rangeCost_zero_eq_range, ih (by omega)]
        simp only [baseStep, List.getD_eq_getElem gs [] hkG, groupsTotalLen,
          List.take_succ_eq_append_getElem hkG, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton]
        ring
    simpa [List.take_length] using hgo gs.length (le_refl _)
  rw [hrc] at hc_loop
  dsimp only [st_h, st0, startState] at hc_loop
  simp only [workOf, hew_end, totalNonMaxLen, bundleStepScanCost] at hc_loop ⊢
  have h1 : (2 * TS.mul * ordStoreLog eCap + 170) * groupsTotalLen gs ≤
      (2 * TS.mul * ordStoreLog eCap + 200) * groupsTotalLen gs :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (TS.mul * ordStoreLog eCap + 355) * (∑ gi ∈ Finset.range gs.length,
        ∑ j ∈ (Finset.range (gs.getD gi []).length).erase (maxIdxs.getD gi 0),
          (cord' ((gs.getD gi []).getD j 0)).length) ≤
      (TS.mul * ordStoreLog eCap + 360) * (∑ gi ∈ Finset.range gs.length,
        ∑ j ∈ (Finset.range (gs.getD gi []).length).erase (maxIdxs.getD gi 0),
          (cord' ((gs.getD gi []).getD j 0)).length) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end

end MinCostFlow.SparseCore.Program
