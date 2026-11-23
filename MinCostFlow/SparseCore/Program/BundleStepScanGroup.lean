module

public import MinCostFlow.SparseCore.Program.BundleStepScanPassB
public import MinCostFlow.SparseCore.Program.BundleStepScanPassC

/-!
# Root-scan and group-scan verification for Phase 2 (`BundleStepScanGroup`)

Verifies `bundleStepScanRootStmt` (single non-maximal root: `bTourList` + Pass A + Pass B) and
the per-group body of `bundleStepScanStmt` (`bundleStepScanMaxStmt` + `forRange 19` over all
non-maximal roots in a split group `G`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical

/-- Candidate bundles added by scanning a single end list `xs` (all ends processed). -/
noncomputable def addCandsForList {slotCap : ℕ} (S : BundleTableState slotCap) (xs : List End)
    (cand₀ : Fin slotCap → Finset ℕ) : Fin slotCap → Finset ℕ :=
  passBCands S xs xs.length cand₀

/-- Candidate bundles added by scanning every root `G[j]` (`j < k`, `j ≠ maxIdx`) of group `G`. -/
noncomputable def addCandsForGroupPrefix {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (G : List ℕ) (maxIdx : ℕ) (cand₀ : Fin slotCap → Finset ℕ) :
    ℕ → Fin slotCap → Finset ℕ
  | 0 => cand₀
  | k + 1 =>
    if h : k < G.length then
      if k = maxIdx then addCandsForGroupPrefix S cord' G maxIdx cand₀ k
      else addCandsForList S (cord' (G[k]'h)) (addCandsForGroupPrefix S cord' G maxIdx cand₀ k)
    else addCandsForGroupPrefix S cord' G maxIdx cand₀ k

/-- Scanned candidate-bundle ends accumulated across roots `G[j]` (`j < k`, `j ≠ maxIdx`) of
group `G`. -/
noncomputable def addScanEndsForGroupPrefix {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (G : List ℕ) (maxIdx : ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) :
    ℕ → Fin slotCap → List (ℕ × ℕ × ℕ)
  | 0 => scan₀
  | k + 1 =>
    if h : k < G.length then
      if k = maxIdx then addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ k
      else addScanEndsForList S (addCandsForGroupPrefix S cord' G maxIdx cand₀ (k + 1))
        (G[k]'h) (cord' (G[k]'h)) (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ k)
    else addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ k

end

public section

open Classical

lemma mem_addCandsForList_iff {slotCap : ℕ} {S : BundleTableState slotCap}
    {xs : List End} {cand₀ : Fin slotCap → Finset ℕ} {j : Fin slotCap} {B : BundleState}
    (hnd : xs.Nodup) (hSj : S j = some B) (b : ℕ) :
    b ∈ addCandsForList S xs cand₀ j ↔
      b ∈ cand₀ j ∨
        (b ∈ B.vertices ∧ 0 < ((B.ends b).filter fun x => x ∈ xs).card ∧
          ((B.ends b).filter fun x => x ∈ xs).card < (B.ends b).card) := by
  simp only [addCandsForList, passBCands, hSj, Finset.mem_union, Finset.mem_filter,
    seenVisited_iff_pos, seenCount_eq_card_filter hnd hSj b]

lemma addCandsForList_none {slotCap : ℕ} {S : BundleTableState slotCap}
    {xs : List End} {cand₀ : Fin slotCap → Finset ℕ} {j : Fin slotCap}
    (hSj : S j = none) :
    addCandsForList S xs cand₀ j = cand₀ j := by
  simp [addCandsForList, passBCands, hSj]

lemma mem_addCandsForGroupPrefix_iff {slotCap : ℕ} {S : BundleTableState slotCap}
    {cord' : ℕ → List End} {G : List ℕ} {maxIdx : ℕ} {cand₀ : Fin slotCap → Finset ℕ}
    {j : Fin slotCap} {B : BundleState} (hSj : S j = some B)
    (hnd : ∀ w ∈ G, (cord' w).Nodup) :
    ∀ k ≤ G.length, ∀ b,
      b ∈ addCandsForGroupPrefix S cord' G maxIdx cand₀ k j ↔
        b ∈ cand₀ j ∨
          (b ∈ B.vertices ∧ ∃ t, ∃ (_ht : t < k) (htG : t < G.length), t ≠ maxIdx ∧
            0 < ((B.ends b).filter fun x => x ∈ cord' (G[t]'htG)).card ∧
            ((B.ends b).filter fun x => x ∈ cord' (G[t]'htG)).card < (B.ends b).card) := by
  intro k
  induction k with
  | zero => intro _ b; simp [addCandsForGroupPrefix]
  | succ k ih =>
    intro hk b
    have hkG : k < G.length := by omega
    have ih' := ih (by omega) b
    simp only [addCandsForGroupPrefix, hkG, ↓reduceDIte]
    split_ifs with hkm
    · rw [ih']
      constructor
      · rintro (h0 | ⟨hbV, t, ht, htG, hne, h1, h2⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨hbV, t, by omega, htG, hne, h1, h2⟩
      · rintro (h0 | ⟨hbV, t, ht, htG, hne, h1, h2⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨hbV, t, by omega, htG, hne, h1, h2⟩
    · rw [mem_addCandsForList_iff (hnd _ (List.getElem_mem hkG)) hSj b, ih']
      constructor
      · rintro ((h0 | ⟨hbV, t, ht, htG, hne, h1, h2⟩) | ⟨hbV, h1, h2⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨hbV, t, by omega, htG, hne, h1, h2⟩
        · exact Or.inr ⟨hbV, k, by omega, hkG, hkm, h1, h2⟩
      · rintro (h0 | ⟨hbV, t, ht, htG, hne, h1, h2⟩)
        · exact Or.inl (Or.inl h0)
        · by_cases htk : t = k
          · subst htk; exact Or.inr ⟨hbV, h1, h2⟩
          · exact Or.inl (Or.inr ⟨hbV, t, by omega, htG, hne, h1, h2⟩)

lemma addCandsForGroupPrefix_none {slotCap : ℕ} {S : BundleTableState slotCap}
    {cord' : ℕ → List End} {G : List ℕ} {maxIdx : ℕ} {cand₀ : Fin slotCap → Finset ℕ}
    {j : Fin slotCap} (hSj : S j = none) :
    ∀ k, addCandsForGroupPrefix S cord' G maxIdx cand₀ k j = cand₀ j := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [addCandsForGroupPrefix]
    split_ifs
    · exact ih
    · rw [addCandsForList_none hSj, ih]
    · exact ih

/-! ## 1. Single non-maximal root verification (`bundleStepScanRoot_runs`) -/

/-- Verifies `bundleStepScanRootStmt bTourList` on root `v = G[j]`: calls `bTourList`, then
runs Pass A, Pass B, and Pass C to enqueue splitting bundles and record their scanned ends. -/
lemma bundleStepScanRoot_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH touchedBufPtr wBase hStart h₀ j : ℕ}
    {pProg : Program} {bTourList bTourLen bTourOwner : ℕ}
    (htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched₀ : List ℕ}
    {scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)}
    {G : List ℕ} {cord' : ℕ → List End} {tx₀ : htour.rep.τ} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ p c, m.slotBlocks js = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (htouch_w : touchedBufPtr + slotCap < 2 ^ w)
    (hj : j < G.length)
    (hv_lt : G[j] < vCap ∧ G[j] < 2 ^ w)
    (hxs_lt : ∀ x ∈ cord' G[j], x.1 < eCap)
    (hxs_nd : (cord' G[j]).Nodup)
    (hwBase_j_w : wBase + j < 2 ^ w)
    (hmem_v : st₀.mem (wBase + j) = G[j])
    (hhStart_le : hStart ≤ h₀)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < hStart)
    (htouch_lt : touchedBufPtr + slotCap ≤ hStart)
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (htouch_disj_cur : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_disj_touch : ∀ a, htour.rep.foot tourH tx₀ a →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (hzero : ZeroFrom st₀.mem h₀)
    (hh_sp : h₀ + TS.listSpace (cord' G[j]).length + 3 * (cord' G[j]).length < 2 ^ w)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (hafter₀ : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ st₀.mem)
    (htouch₀ : ListAt st₀.mem touchedBufPtr touched₀)
    (hscan₀ : SlotScanListAt slotCap eCap tbl st₀.mem hStart h₀ scan₀)
    (hscanIn₀ : ∀ js : Fin slotCap, ScanNodesIn st₀.mem (fun a => ¬ htour.rep.foot tourH tx₀ a)
      (st₀.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js))
    (hcnt₀ : ∀ js : Fin slotCap, (scan₀ js).length ≤ h₀)
    (hr0 : st₀.regs 0 = tbl) (hr1 : st₀.regs 1 = tourH) (hr5 : st₀.regs 5 = touchedBufPtr) (hr6 : st₀.regs 6 = h₀)
    (hr7 : st₀.regs 7 = btSlotPtrBase tbl) (hr8 : st₀.regs 8 = btEdgeSlotBase tbl slotCap)
    (hr9 : st₀.regs 9 = btEndBundleBase tbl slotCap eCap)
    (hr10 : st₀.regs 10 = btSlotTouchedBase tbl slotCap eCap)
    (hr11 : st₀.regs 11 = btSlotCandHeadBase tbl slotCap eCap)
    (hr13 : st₀.regs 13 = touched₀.length) (hr16 : st₀.regs 16 = wBase)
    (hr19 : st₀.regs 19 = j) :
    let v := G[j]
    let S := tableDelEdges S₀ D
    let cand' := addCandsForList S (cord' v) cand₀
    let scan' := addScanEndsForList S cand' v (cord' v) scan₀
    ∃ st' c h' tx' touched',
      Runs w pProg ω (bundleStepScanRootStmt bTourList) st₀ .normal st' c ∧
      (∀ r, r ≤ 19 → r ≠ 6 → r ≠ 13 → st'.regs r = st₀.regs r) ∧
      st'.regs 6 = h' ∧ st'.regs 13 = touched'.length ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + TS.listSpace (cord' v).length + 3 * (cord' v).length ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand' touched' st'.mem ∧
      ListAt st'.mem touchedBufPtr touched' ∧
      SlotScanListAt slotCap eCap tbl st'.mem hStart h' scan' ∧
      (∀ js : Fin slotCap, ScanNodesIn st'.mem (fun a => ¬ htour.rep.foot tourH tx' a)
        (st'.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan' js)) ∧
      (∀ js : Fin slotCap, (scan' js).length ≤ h') ∧
      (∀ a < h₀, ¬ bundleTableCoreFoot eCap tbl m a →
        (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
        (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = st₀.mem a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        (TS.mul * ordStoreLog eCap + 355) * (cord' v).length + TS.mul * ordStoreLog eCap + 95 +
          htour.rep.phi tourH tx₀ st₀.mem := by
  intro v S cand' scan'
  have hfoot_lt0 : ∀ a, bundleTableFoot eCap tbl m a → a < h₀ :=
    fun a ha => Nat.lt_of_lt_of_le (hfoot_lt a ha) hhStart_le
  have hsp_ge := TS.listSpace_ge (cord' v).length
  have hh_sp_L : h₀ + TS.listSpace (cord' v).length < 2 ^ w := by dsimp only [v]; omega
  have hlist_w : h₀ + 1 + (cord' v).length < 2 ^ w := by clear * - hh_sp_L hsp_ge; omega
  set st1 : State := { st₀ with regs := Function.update st₀.regs 20 v }
  set st2 : State := { st1 with regs := Function.update st1.regs 21 h₀ }
  have ha20 : Runs w pProg ω (.assign 20 (.load (.bin .add (.reg 16) (.reg 19)))) st₀ .normal st1 5 :=
    runs_assign_iff.mpr ⟨v, by simp [Expr.eval, BinOp.eval, hr16, hr19, hmem_v, hwBase_j_w, v], rfl, rfl, rfl⟩
  have ha21 : Runs w pProg ω (.assign 21 (.reg 6)) st1 .normal st2 2 :=
    runs_assign_iff.mpr ⟨h₀, by simp [Expr.eval, st1, hr6], rfl, rfl, rfl⟩
  obtain ⟨body, hbody, oL, st3_raw, cL, tx', hrunL, htrep', hlistL, hh'_ge, hresp, hcL⟩ :=
    htour.list_runs tourH v h₀ cord' tx₀ st₀.mem st2.pos ω htourH_w hv_lt.1 hv_lt.2
      (by omega) htrep htfoot_lt hzero hh_sp_L
  rcases hresp with ⟨hh0_le, hh'_le, hzero', hfrL, htfoot'⟩
  set h' := oL.value
  set st3 : State := { mem := st3_raw.mem, regs := Function.update st2.regs 6 h', pos := st3_raw.pos }
  have hcall : Runs w pProg ω (.call 6 bTourList [.reg 1, .reg 20, .reg 6]) st2 .normal st3 (cL + 4) := by
    have hargs : evalArgs w st2 [.reg 1, .reg 20, .reg 6] = some [tourH, v, h₀] := by
      simp [evalArgs, Expr.eval, st2, st1, hr1, hr6]
    have hc : Runs w pProg ω (.call 6 bTourList [.reg 1, .reg 20, .reg 6]) st2 .normal
        { mem := st3_raw.mem, regs := Function.update st2.regs 6 oL.value, pos := st3_raw.pos }
        (argsSize [.reg 1, .reg 20, .reg 6] + cL + 1) :=
      runs_call_iff.mpr ⟨[tourH, v, h₀], body, oL, st3_raw, cL, hargs, hbody, hrunL, rfl, rfl, rfl⟩
    simpa [argsSize, Expr.size, st3, h', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
  set st4 : State := { st3 with regs := Function.update st3.regs 22 (cord' v).length }
  have ha22 : Runs w pProg ω (.assign 22 (.load (.reg 21))) st3 .normal st4 3 :=
    runs_assign_iff.mpr ⟨(cord' v).length, by simp [Expr.eval, st3, st2, hlistL.1], rfl, rfl, rfl⟩
  -- Transfer BundleTableAfterScan and ListAt across the bTourList call
  have hafter3 : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ st4.mem :=
    hafter₀.of_agree fun a ha => (hfrL a (hfoot_lt0 a (bundleTableCoreFoot_subset_foot ha))
      (fun ht => htfoot_disj_tbl a ht (bundleTableCoreFoot_subset_foot ha))).symm
  have htouch3 : ListAt st4.mem touchedBufPtr touched₀ := fun idx hidx => by
    have hlt_len : touched₀.length ≤ slotCap := by
      have hc := Finset.card_le_card (show touched₀.toFinset ⊆ Finset.range slotCap from
        fun y hy => Finset.mem_range.mpr (hafter₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y (List.mem_toFinset.mp hy)))
      simpa [List.toFinset_card_of_nodup hafter₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using hc
    have h1 := hfrL (touchedBufPtr + idx) (by omega) (fun ht => by
      have := htfoot_disj_touch _ ht; omega)
    exact h1.trans (htouch₀ idx hidx)
  have hlist_disj_foot : ∀ a, h₀ ≤ a → a < h₀ + 1 + (cord' v).length → ¬ bundleTableFoot eCap tbl m a :=
    fun a ha1 _ hf => absurd (hfoot_lt0 a hf) (by omega)
  have hlist_disj_touch : ∀ a, h₀ ≤ a → a < h₀ + 1 + (cord' v).length →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a :=
    fun a ha1 _ => Or.inr (by omega)
  -- Run Pass A
  obtain ⟨stA, cA, hrunA, hregsA, hseenA, hfrA, hcA⟩ :=
    bundleStepScanPassA_runs (st₀ := st4) hw16 htbl_w hblks_w hlist_w hlist_disj_foot
      hlistL hxs_lt hxs_nd hafter3
      (by simp [st4, st3, st2, st1, hr7]) (by simp [st4, st3, st2, st1, hr8])
      (by simp [st4, st3, st2, st1, hr9]) (by simp [st4, st3, st2]) (by simp [st4])
  -- Run Pass B
  obtain ⟨touched', stB, cB, hrunB, hregsB, hr13B, hafterB, htouchB, hfrB, hcB⟩ :=
    bundleStepScanPassB_runs (mem₀ := st4.mem) (st₀ := stA) hw16 htbl_w hblks_w hlist_w htouch_w
      hlist_disj_foot hlist_disj_touch htouch_disj_foot hlistL hxs_lt hxs_nd hafter3 htouch3
      hseenA hfrA
      (by rw [hregsA 5 (by decide)]; simp [st4, st3, st2, st1, hr5])
      (by rw [hregsA 7 (by decide)]; simp [st4, st3, st2, st1, hr7])
      (by rw [hregsA 8 (by decide)]; simp [st4, st3, st2, st1, hr8])
      (by rw [hregsA 9 (by decide)]; simp [st4, st3, st2, st1, hr9])
      (by rw [hregsA 10 (by decide)]; simp [st4, st3, st2, st1, hr10])
      (by rw [hregsA 11 (by decide)]; simp [st4, st3, st2, st1, hr11])
      (by rw [hregsA 13 (by decide)]; simp [st4, st3, st2, st1, hr13])
      (by rw [hregsA 21 (by decide)]; simp [st4, st3, st2])
      (by rw [hregsA 22 (by decide)]; simp [st4])
  -- Transfer EndListAt, ZeroFrom, and SlotScanListAt across Pass A + Pass B
  have hcur_not_core : ∀ a, btCurBunBase tbl slotCap eCap ≤ a →
      a < btCurTagBase tbl slotCap eCap + slotCap → ¬ bundleTableCoreFoot eCap tbl m a := by
    intro a ha1 ha2 hc
    rcases hc with ⟨_, hc2⟩ | ⟨js, p, cap, hm, hp1, hp2⟩
    · unfold btCurBunBase at ha1; unfold bundleTableCoreSize at hc2; omega
    · have hsj := hafter₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 js
      cases hS : tableDelEdges S₀ D js with
      | none => rw [hS, hm] at hsj; exact False.elim hsj
      | some B =>
        rw [hS, hm] at hsj; have hdj := hsj.2.2
        unfold btCurBunBase at ha1; unfold btCurTagBase at ha2; unfold bundleTableFixedSize at hdj; omega
  have hcur_in_foot : ∀ a, btCurBunBase tbl slotCap eCap ≤ a →
      a < btCurTagBase tbl slotCap eCap + slotCap → bundleTableFoot eCap tbl m a := fun a ha1 ha2 =>
    Or.inl ⟨by unfold btCurBunBase at ha1; omega,
      by unfold btCurTagBase at ha2; unfold bundleTableFixedSize; omega⟩
  have hcur_disj_touch : ∀ a, btCurBunBase tbl slotCap eCap ≤ a →
      a < btCurTagBase tbl slotCap eCap + slotCap →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a := fun a ha1 ha2 => by
    by_contra hnot; push Not at hnot
    rcases htouch_disj_cur a hnot.1 hnot.2 with h1 | h2 <;> omega
  have hlistB : EndListAt stB.mem h₀ (cord' v) := by
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hfrB h₀ (fun hf => hlist_disj_foot h₀ (le_refl _) (by omega) (bundleTableCoreFoot_subset_foot hf))
        (hlist_disj_touch h₀ (le_refl _) (by omega))]
      exact hlistL.1
    · rw [hfrB (h₀ + 1 + i) (fun hf => hlist_disj_foot _ (by omega) (by omega) (bundleTableCoreFoot_subset_foot hf))
        (hlist_disj_touch _ (by omega) (by omega))]
      exact hlistL.2 i hi
  have hzeroB : ZeroFrom stB.mem h' := fun a ha => by
    rw [hfrB a (fun hf => absurd (hfoot_lt0 a (bundleTableCoreFoot_subset_foot hf)) (by omega)) (Or.inr (by omega))]
    exact hzero' a ha
  have hcur_eq_B : ∀ s < slotCap,
      stB.mem (btCurBunBase tbl slotCap eCap + s) = st₀.mem (btCurBunBase tbl slotCap eCap + s) ∧
      stB.mem (btCurTagBase tbl slotCap eCap + s) = st₀.mem (btCurTagBase tbl slotCap eCap + s) := fun s hs => by
    have hcb_a : btCurBunBase tbl slotCap eCap ≤ btCurBunBase tbl slotCap eCap + s ∧
        btCurBunBase tbl slotCap eCap + s < btCurTagBase tbl slotCap eCap + slotCap :=
      ⟨by omega, by unfold btCurBunBase btCurTagBase; omega⟩
    have hct_a : btCurBunBase tbl slotCap eCap ≤ btCurTagBase tbl slotCap eCap + s ∧
        btCurTagBase tbl slotCap eCap + s < btCurTagBase tbl slotCap eCap + slotCap :=
      ⟨by unfold btCurBunBase btCurTagBase; omega, by omega⟩
    exact ⟨(hfrB _ (hcur_not_core _ hcb_a.1 hcb_a.2) (hcur_disj_touch _ hcb_a.1 hcb_a.2)).trans
        (hfrL _ (hfoot_lt0 _ (hcur_in_foot _ hcb_a.1 hcb_a.2))
          (fun ht => htfoot_disj_tbl _ ht (hcur_in_foot _ hcb_a.1 hcb_a.2))),
      (hfrB _ (hcur_not_core _ hct_a.1 hct_a.2) (hcur_disj_touch _ hct_a.1 hct_a.2)).trans
        (hfrL _ (hfoot_lt0 _ (hcur_in_foot _ hct_a.1 hct_a.2))
          (fun ht => htfoot_disj_tbl _ ht (hcur_in_foot _ hct_a.1 hct_a.2)))⟩
  have hscanB_both : ∀ js : Fin slotCap,
      (ScanNodesAt eCap stB.mem hStart h' (stB.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js) ∧
        ScanNodesIn stB.mem (fun a => ¬ htour.rep.foot tourH tx' a)
          (stB.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js)) ∧
      stB.mem (btCurTagBase tbl slotCap eCap + js.1) = (scan₀ js).length := fun js => by
    obtain ⟨hcb, hct⟩ := hcur_eq_B js.1 js.2
    rw [hcb, hct]
    refine ⟨scanNodesAt_mono_of_in (hscan₀ js).1 (hscanIn₀ js) hh0_le
      (fun a ha1 ha2 hntf => by
        have hnf : ¬ bundleTableFoot eCap tbl m a := fun hf => absurd (hfoot_lt a hf) (by omega)
        have hout : a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a := Or.inr (by omega)
        exact (hfrB a (fun hc => hnf (bundleTableCoreFoot_subset_foot hc)) hout).trans (hfrL a ha2 hntf))
      (fun a _ ha2 hntf htf' => by
        rcases htfoot' a htf' with h0 | ⟨ha1, _⟩
        · exact hntf h0
        · omega),
      (hscan₀ js).2⟩
  have hscanB : SlotScanListAt slotCap eCap tbl stB.mem hStart h' scan₀ :=
    fun js => ⟨(hscanB_both js).1.1, (hscanB_both js).2⟩
  have hscanInB : ∀ js : Fin slotCap, ScanNodesIn stB.mem (fun a => ¬ htour.rep.foot tourH tx' a)
      (stB.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js) :=
    fun js => (hscanB_both js).1.2
  -- Run Pass C
  obtain ⟨stC, cC, h'', hrunC, hregsC, hr6C, hh'_leC, hh''_le, hzeroC, hscanC, hscanInC, hcntC, hfrC, hcC⟩ :=
    bundleStepScanPassC_runs (st₀ := stB) (v := v) (hStart := hStart) (hCur := h')
      (P := fun a => ¬ htour.rep.foot tourH tx' a)
      hw16 hpk_w htbl_w hblks_w
      hlist_w hv_lt.1 hxs_lt hfoot_lt (le_trans hhStart_le hh0_le) (by omega)
      (fun a ha1 _ => Or.inr (by
        have := hfoot_lt0 (btCurTagBase tbl slotCap eCap + slotCap - 1)
          (Or.inl ⟨by unfold btCurTagBase; omega, by unfold btCurTagBase bundleTableFixedSize; omega⟩)
        unfold btCurTagBase at this ⊢; omega))
      (fun js => le_trans (hcnt₀ js) hh0_le) (by dsimp only [v] at hh'_le ⊢; omega) hzeroB hlistB hafterB hscanB hscanInB
      (fun a ha htf' => by
        rcases htfoot' a htf' with h0 | ⟨_, hlt⟩
        · exact absurd (htfoot_lt a h0) (by omega)
        · omega)
      (by rw [hregsB 0 (by decide) (by decide), hregsA 0 (by decide)]; simp [st4, st3, st2, st1, hr0])
      (by rw [hregsB 6 (by decide) (by decide), hregsA 6 (by decide)]; simp [st4, st3])
      (by rw [hregsB 7 (by decide) (by decide), hregsA 7 (by decide)]; simp [st4, st3, st2, st1, hr7])
      (by rw [hregsB 8 (by decide) (by decide), hregsA 8 (by decide)]; simp [st4, st3, st2, st1, hr8])
      (by rw [hregsB 9 (by decide) (by decide), hregsA 9 (by decide)]; simp [st4, st3, st2, st1, hr9])
      (by rw [hregsB 11 (by decide) (by decide), hregsA 11 (by decide)]; simp [st4, st3, st2, st1, hr11])
      (by rw [hregsB 20 (by decide) (by decide), hregsA 20 (by decide)]; simp [st4, st3, st2, st1])
      (by rw [hregsB 21 (by decide) (by decide), hregsA 21 (by decide)]; simp [st4, st3, st2])
      (by rw [hregsB 22 (by decide) (by decide), hregsA 22 (by decide)]; simp [st4])
  -- Transfer BundleTableAfterScan, ListAt, and tour rep/phi across Pass C
  have hafterC : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand' touched' stC.mem :=
    hafterB.of_agree fun a ha => (hfrC a
      (by by_contra hnot; push Not at hnot; exact hcur_not_core a hnot.1 hnot.2 ha)
      (Or.inl (Nat.lt_of_lt_of_le (hfoot_lt0 a (bundleTableCoreFoot_subset_foot ha)) hh0_le))).symm
  have htouchC : ListAt stC.mem touchedBufPtr touched' := fun idx hidx => by
    have hlt_len : touched'.length ≤ slotCap := by
      have hc := Finset.card_le_card (show touched'.toFinset ⊆ Finset.range slotCap from
        fun y hy => Finset.mem_range.mpr (hafterB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y (List.mem_toFinset.mp hy)))
      simpa [List.toFinset_card_of_nodup hafterB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using hc
    exact (hfrC (touchedBufPtr + idx) (htouch_disj_cur _ (by omega) (by omega))
      (Or.inl (by omega))).trans (htouchB idx hidx)
  have htfoot'_disj_mut : ∀ a, htour.rep.foot tourH tx' a →
      ¬ bundleTableFoot eCap tbl m a ∧ (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) ∧ a < h' := by
    intro a ha
    rcases htfoot' a ha with h0 | ⟨ha1, ha2⟩
    · exact ⟨htfoot_disj_tbl a h0, htfoot_disj_touch a h0, Nat.lt_of_lt_of_le (htfoot_lt a h0) hh0_le⟩
    · exact ⟨fun hf => absurd (hfoot_lt0 a hf) (by omega), Or.inr (by omega), ha2⟩
  have hmem_tour_agree : ∀ a, htour.rep.foot tourH tx' a → stC.mem a = st3_raw.mem a := fun a ha => by
    have hdisj := htfoot'_disj_mut a ha
    have hnc : a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a := by
      by_contra hnot; push Not at hnot; exact hdisj.1 (hcur_in_foot a hnot.1 hnot.2)
    exact (hfrC a hnc (Or.inl hdisj.2.2)).trans
      (hfrB a (fun hf => hdisj.1 (bundleTableCoreFoot_subset_foot hf)) hdisj.2.1)
  have htrep_C : htour.rep.rep tourH cord' tx' stC.mem :=
    (htour.rep_local tourH cord' tx' st3_raw.mem stC.mem (fun a ha => (hmem_tour_agree a ha).symm)).1 htrep'
  have hphi_C : htour.rep.phi tourH tx' stC.mem = htour.rep.phi tourH tx' st3_raw.mem :=
    (htour.rep_local tourH cord' tx' st3_raw.mem stC.mem (fun a ha => (hmem_tour_agree a ha).symm)).2.symm
  refine ⟨stC, 5 + (2 + ((cL + 4) + (3 + (cA + (cB + cC + 1) + 1) + 1) + 1) + 1) + 1, h'', tx', touched',
    bundle_runs_seq_normal ha20 (bundle_runs_seq_normal ha21 (bundle_runs_seq_normal hcall
      (bundle_runs_seq_normal ha22 (bundle_runs_seq_normal hrunA (bundle_runs_seq_normal hrunB hrunC))))),
    fun r hr hne6 hne13 => by
      rw [hregsC r (by omega) hne6, hregsB r (by omega) hne13, hregsA r (by omega)]
      simp [st4, st3, st2, st1, show r ≠ 22 by omega, show r ≠ 21 by omega, show r ≠ 20 by omega, hne6],
    hr6C, (hregsC 13 (by decide) (by decide)).trans hr13B,
    le_trans hh0_le hh'_leC, by omega, hzeroC, htrep_C,
    fun a ha => by
      rcases htfoot' a ha with h0 | ⟨ha1, ha2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨ha1, Nat.lt_of_lt_of_le ha2 hh'_leC⟩,
    hafterC, htouchC, hscanC, hscanInC, hcntC,
    fun a ha hnf hnc hout hntf =>
      (hfrC a hnc (Or.inl (Nat.lt_of_lt_of_le ha hh0_le))).trans ((hfrB a hnf hout).trans (hfrL a ha hntf)), ?_⟩
  rw [hphi_C]
  have hmul : TS.mul * ((cord' v).length + 1) * ordStoreLog eCap =
      TS.mul * ordStoreLog eCap * (cord' v).length + TS.mul * ordStoreLog eCap := by ring
  have hmul2 : (TS.mul * ordStoreLog eCap + 355) * (cord' v).length =
      TS.mul * ordStoreLog eCap * (cord' v).length + 355 * (cord' v).length := by ring
  omega

/-! ## 2. Per-group scan verification (`bundleStepScanGroup_runs`) -/

/-- Sum of `(cord' G[j]).length` over all non-maximal indices `j < k, j ≠ maxIdx`. -/
@[expose] def nonMaxLenPrefix (cord' : ℕ → List End) (G : List ℕ) (maxIdx : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    nonMaxLenPrefix cord' G maxIdx k +
      if h : k < G.length then if k = maxIdx then 0 else (cord' (G[k]'h)).length else 0

/-- Sum of `TS.listSpace (cord' G[j]).length + 3 * (cord' G[j]).length` over `j < k`. -/
@[expose] def listSpacePrefix (TS : BundleTourSpec) (cord' : ℕ → List End) (G : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    listSpacePrefix TS cord' G k +
      if h : k < G.length then TS.listSpace (cord' (G[k]'h)).length + 3 * (cord' (G[k]'h)).length else 0

lemma listSpacePrefix_eq_sum (TS : BundleTourSpec) (cord' : ℕ → List End) (G : List ℕ) :
    listSpacePrefix TS cord' G G.length =
      (G.map fun w => TS.listSpace (cord' w).length + 3 * (cord' w).length).sum := by
  have hgo : ∀ k ≤ G.length, listSpacePrefix TS cord' G k =
      ((G.take k).map fun w => TS.listSpace (cord' w).length + 3 * (cord' w).length).sum := by
    intro k
    induction k with
    | zero => intro _; simp [listSpacePrefix]
    | succ k ih =>
      intro hk
      have hkG : k < G.length := by omega
      simp only [listSpacePrefix, hkG, ↓reduceDIte, List.take_succ_eq_append_getElem hkG,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      rw [ih (by omega)]
  simpa [List.take_length] using hgo G.length (le_refl _)

lemma nonMaxLenPrefix_eq_finset_sum (cord' : ℕ → List End) (G : List ℕ) (maxIdx : ℕ) :
    nonMaxLenPrefix cord' G maxIdx G.length =
      ∑ j ∈ (Finset.range G.length).erase maxIdx, (cord' (G.getD j 0)).length := by
  have hgo : ∀ k ≤ G.length, nonMaxLenPrefix cord' G maxIdx k =
      ∑ j ∈ (Finset.range k).erase maxIdx, (cord' (G.getD j 0)).length := by
    intro k
    induction k with
    | zero => intro _; simp [nonMaxLenPrefix]
    | succ k ih =>
      intro hk
      have hkG : k < G.length := by omega
      simp only [nonMaxLenPrefix, hkG, ↓reduceDIte, Finset.range_add_one]
      rw [ih (by omega)]
      by_cases hkm : k = maxIdx
      · subst hkm
        simp only [↓reduceIte, add_zero, Finset.erase_insert Finset.notMem_range_self,
          Finset.erase_eq_of_notMem Finset.notMem_range_self]
      · simp only [hkm, ↓reduceIte, Finset.erase_insert_of_ne hkm,
          Finset.sum_insert (fun h => Finset.notMem_range_self (Finset.mem_of_mem_erase h)),
          List.getD_eq_getElem G 0 hkG, Nat.add_comm]
  exact hgo G.length (le_refl _)

/-- Verifies the per-group body of `bundleStepScanStmt` (`bundleStepScanMaxStmt` followed by
`forRange 19` scanning every root `j ≠ maxIdx` of group `G`). -/
lemma bundleStepScanGroup_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH touchedBufPtr wBase hStart h₀ : ℕ}
    {pProg : Program} {bTourList bTourLen bTourOwner : ℕ}
    (htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched₀ : List ℕ}
    {scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)}
    {G : List ℕ} {cord' : ℕ → List End} {tx₀ : htour.rep.τ} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ p c, m.slotBlocks js = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (htouch_w : touchedBufPtr + slotCap < 2 ^ w)
    (hG_pos : 0 < G.length)
    (hG_lt : ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hG_ends_lt : ∀ v ∈ G, ∀ x ∈ cord' v, x.1 < eCap)
    (hG_nd : ∀ v ∈ G, (cord' v).Nodup)
    (hwBase_w : wBase + G.length < 2 ^ w)
    (hG_mem : ListAt st₀.mem wBase G)
    (hhStart_le : hStart ≤ h₀)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < hStart)
    (htouch_lt : touchedBufPtr + slotCap ≤ hStart)
    (hwBase_lt : wBase + G.length ≤ hStart)
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (htouch_disj_cur : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a)
    (hwBase_disj_foot : ∀ a, wBase ≤ a → a < wBase + G.length → ¬ bundleTableFoot eCap tbl m a)
    (hwBase_disj_touch : ∀ a, wBase ≤ a → a < wBase + G.length →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_disj_touch : ∀ a, htour.rep.foot tourH tx₀ a →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (htfoot_disj_wBase : ∀ a, htour.rep.foot tourH tx₀ a → a < wBase ∨ wBase + G.length ≤ a)
    (hzero : ZeroFrom st₀.mem h₀)
    (hh_sp : h₀ + TS.querySpace * G.length +
      (G.map fun v => TS.listSpace (cord' v).length + 3 * (cord' v).length).sum < 2 ^ w)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (hafter₀ : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ st₀.mem)
    (htouch₀ : ListAt st₀.mem touchedBufPtr touched₀)
    (hscan₀ : SlotScanListAt slotCap eCap tbl st₀.mem hStart h₀ scan₀)
    (hscanIn₀ : ∀ js : Fin slotCap, ScanNodesIn st₀.mem (fun a => ¬ htour.rep.foot tourH tx₀ a)
      (st₀.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js))
    (hcnt₀ : ∀ js : Fin slotCap, (scan₀ js).length ≤ h₀)
    (hr0 : st₀.regs 0 = tbl) (hr1 : st₀.regs 1 = tourH) (hr5 : st₀.regs 5 = touchedBufPtr) (hr6 : st₀.regs 6 = h₀)
    (hr7 : st₀.regs 7 = btSlotPtrBase tbl) (hr8 : st₀.regs 8 = btEdgeSlotBase tbl slotCap)
    (hr9 : st₀.regs 9 = btEndBundleBase tbl slotCap eCap)
    (hr10 : st₀.regs 10 = btSlotTouchedBase tbl slotCap eCap)
    (hr11 : st₀.regs 11 = btSlotCandHeadBase tbl slotCap eCap)
    (hr13 : st₀.regs 13 = touched₀.length) (hr15 : st₀.regs 15 = G.length)
    (hr16 : st₀.regs 16 = wBase) :
    let S := tableDelEdges S₀ D
    ∃ st' c h' tx' maxIdx touched',
      Runs w pProg ω
        (bundleStepScanMaxStmt bTourLen ;;
         forRange 19 (.const 0) (.reg 15)
           (.cond (.bin .eq (.reg 19) (.reg 17)) .nop (bundleStepScanRootStmt bTourList)))
        st₀ .normal st' c ∧
      (∀ r, r ≤ 16 → r ≠ 6 → r ≠ 13 → st'.regs r = st₀.regs r) ∧
      st'.regs 6 = h' ∧ st'.regs 13 = touched'.length ∧
      (∃ hm : maxIdx < G.length, ∀ j (hj : j < G.length), (cord' G[j]).length ≤ (cord' G[maxIdx]).length) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + TS.querySpace * G.length +
        (G.map fun v => TS.listSpace (cord' v).length + 3 * (cord' v).length).sum ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
        (addCandsForGroupPrefix S cord' G maxIdx cand₀ G.length) touched' st'.mem ∧
      ListAt st'.mem touchedBufPtr touched' ∧
      SlotScanListAt slotCap eCap tbl st'.mem hStart h'
        (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ G.length) ∧
      (∀ js : Fin slotCap, ScanNodesIn st'.mem (fun a => ¬ htour.rep.foot tourH tx' a)
        (st'.mem (btCurBunBase tbl slotCap eCap + js.1))
        (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ G.length js)) ∧
      (∀ js : Fin slotCap, (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ G.length js).length ≤ h') ∧
      (∀ a < h₀, ¬ bundleTableCoreFoot eCap tbl m a →
        (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
        (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = st₀.mem a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        (2 * TS.mul * ordStoreLog eCap + 170) * G.length + 45 +
        (TS.mul * ordStoreLog eCap + 355) * (∑ j ∈ (Finset.range G.length).erase maxIdx, (cord' (G.getD j 0)).length) +
        htour.rep.phi tourH tx₀ st₀.mem := by
  intro S
  have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
  have hfoot_lt0 : ∀ a, bundleTableFoot eCap tbl m a → a < h₀ :=
    fun a ha => Nat.lt_of_lt_of_le (hfoot_lt a ha) hhStart_le
  -- Step 1: bundleStepScanMaxStmt
  obtain ⟨stM, cM, hM, txM, maxIdx, hrunM, hregsM, hr6M, hr17M, hmax, hh0_leM, hhM_le,
    hzeroM, htrepM, htfootM, hfrM, hcM⟩ :=
    bundleStepScanMax_runs (htour := htour) hw16 htourH_w hG_pos hG_lt hG_mem (by omega)
      (fun a ha1 ha2 ht => by have := htfoot_disj_wBase a ht; omega) (by omega)
      htrep htfoot_lt hzero hr1 hr6 hr15 hr16
  have hafterM : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ stM.mem :=
    hafter₀.of_agree fun a ha => (hfrM a (hfoot_lt0 a (bundleTableCoreFoot_subset_foot ha))
      (fun ht => htfoot_disj_tbl a ht (bundleTableCoreFoot_subset_foot ha))).symm
  have htouchM : ListAt stM.mem touchedBufPtr touched₀ := fun idx hidx => by
    have hlt_len : touched₀.length ≤ slotCap := by
      have hc := Finset.card_le_card (show touched₀.toFinset ⊆ Finset.range slotCap from
        fun y hy => Finset.mem_range.mpr (hafter₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y (List.mem_toFinset.mp hy)))
      simpa [List.toFinset_card_of_nodup hafter₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using hc
    exact (hfrM (touchedBufPtr + idx) (by omega) (fun ht => by have := htfoot_disj_touch _ ht; omega)).trans
      (htouch₀ idx hidx)
  have hscanM_both : ∀ js : Fin slotCap,
      (ScanNodesAt eCap stM.mem hStart hM (stM.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js) ∧
        ScanNodesIn stM.mem (fun a => ¬ htour.rep.foot tourH txM a)
          (stM.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js)) ∧
      stM.mem (btCurTagBase tbl slotCap eCap + js.1) = (scan₀ js).length := fun js => by
    have hcb_f : bundleTableFoot eCap tbl m (btCurBunBase tbl slotCap eCap + js.1) :=
      Or.inl ⟨by unfold btCurBunBase; omega, by unfold btCurBunBase bundleTableFixedSize; omega⟩
    have hct_f : bundleTableFoot eCap tbl m (btCurTagBase tbl slotCap eCap + js.1) :=
      Or.inl ⟨by unfold btCurTagBase; omega, by unfold btCurTagBase bundleTableFixedSize; omega⟩
    rw [hfrM _ (hfoot_lt0 _ hcb_f) (fun ht => htfoot_disj_tbl _ ht hcb_f),
      hfrM _ (hfoot_lt0 _ hct_f) (fun ht => htfoot_disj_tbl _ ht hct_f)]
    refine ⟨scanNodesAt_mono_of_in (hscan₀ js).1 (hscanIn₀ js) hh0_leM
      (fun a _ ha2 hntf => hfrM a ha2 hntf)
      (fun a _ ha2 hntf htfM => by
        rcases htfootM a htfM with h0 | ⟨ha1, _⟩
        · exact hntf h0
        · omega),
      (hscan₀ js).2⟩
  have hscanM : SlotScanListAt slotCap eCap tbl stM.mem hStart hM scan₀ :=
    fun js => ⟨(hscanM_both js).1.1, (hscanM_both js).2⟩
  have hscanInM : ∀ js : Fin slotCap, ScanNodesIn stM.mem (fun a => ¬ htour.rep.foot tourH txM a)
      (stM.mem (btCurBunBase tbl slotCap eCap + js.1)) (scan₀ js) :=
    fun js => (hscanM_both js).1.2
  -- Step 2: forRange 19 over non-maximal roots
  let Acc := ℕ × htour.rep.τ × List ℕ
  let Inv : ℕ → Acc → State → Prop := fun j acc st =>
    let (hCur, tx, touched) := acc
    (∀ r, r ≤ 16 → r ≠ 6 → r ≠ 13 → st.regs r = st₀.regs r) ∧
    st.regs 6 = hCur ∧ st.regs 13 = touched.length ∧ st.regs 17 = maxIdx ∧ st.regs 19 = j ∧
    hM ≤ hCur ∧ hCur ≤ hM + listSpacePrefix TS cord' G j ∧
    ZeroFrom st.mem hCur ∧
    htour.rep.rep tourH cord' tx st.mem ∧
    (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < hCur)) ∧
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
      (addCandsForGroupPrefix S cord' G maxIdx cand₀ j) touched st.mem ∧
    ListAt st.mem touchedBufPtr touched ∧
    SlotScanListAt slotCap eCap tbl st.mem hStart hCur
      (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ j) ∧
    (∀ js : Fin slotCap, ScanNodesIn st.mem (fun a => ¬ htour.rep.foot tourH tx a)
      (st.mem (btCurBunBase tbl slotCap eCap + js.1))
      (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ j js)) ∧
    (∀ js : Fin slotCap, (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ j js).length ≤ hCur) ∧
    (∀ a < h₀, ¬ bundleTableCoreFoot eCap tbl m a →
      (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
      (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) →
      ¬ htour.rep.foot tourH tx₀ a → st.mem a = st₀.mem a)
  let sc : ℕ → ℕ := fun j =>
    (TS.mul * ordStoreLog eCap + 110) + if h : j < G.length then if j = maxIdx then 0 else (TS.mul * ordStoreLog eCap + 355) * (cord' (G[j]'h)).length else 0
  obtain ⟨st_end, c_loop, ⟨hEnd, txEnd, touchedEnd⟩, hrun_loop, hInv_end, hc_loop⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 19) (lo := .const 0) (hi := .reg 15)
      (phi := fun acc st => htour.rep.phi tourH acc.2.1 st.mem) (Inv := Inv) (stepCost := sc)
      G.length (by omega) (fun _ => by omega) (st₀ := stM) (a₀ := (hM, txM, touched₀))
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        exact ⟨fun r hr h6 h13 => by
            simp only [Function.update_of_ne (show r ≠ 19 by omega)]
            exact hregsM r hr h6,
          by simp [hr6M], by simp [hregsM 13 (by decide) (by decide), hr13], by simp [hr17M], by simp,
          le_refl _, by simp [listSpacePrefix], hzeroM, htrepM, htfootM, hafterM, htouchM,
          hscanM, hscanInM, fun js => le_trans (hcnt₀ js) hh0_leM,
          fun a ha _ _ _ hntf => hfrM a ha hntf⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 15 (by decide) (by decide) (by decide), hr15])
      (fun j ⟨hCur, tx, touched⟩ st hj hI => by
        rcases hI with ⟨hregs, hr6c, hr13c, hr17c, hr19c, hhM_leC, hhCur_le, hzeroC, htrepC,
          htfootC, hafterC, htouchC, hscanC, hscanInC, hcntC, hfrC⟩
        have hsp_pref_le : listSpacePrefix TS cord' G (j + 1) ≤
            (G.map fun v => TS.listSpace (cord' v).length + 3 * (cord' v).length).sum := by
          rw [← listSpacePrefix_eq_sum TS cord' G]
          have hmono : ∀ a b, a ≤ b → listSpacePrefix TS cord' G a ≤ listSpacePrefix TS cord' G b := by
            intro a b hab; induction hab with
            | refl => exact le_refl _
            | @step m _ ih => exact le_trans ih (by simp only [listSpacePrefix]; exact Nat.le_add_right _ _)
          exact hmono (j + 1) G.length (by omega)
        have hlist_sp_cur : hCur + TS.listSpace (cord' G[j]).length + 3 * (cord' G[j]).length < 2 ^ w := by
          have heq : listSpacePrefix TS cord' G (j + 1) =
              listSpacePrefix TS cord' G j + (TS.listSpace (cord' G[j]).length + 3 * (cord' G[j]).length) := by
            simp only [listSpacePrefix, hj, ↓reduceDIte]
          have hsum_le : listSpacePrefix TS cord' G j + (TS.listSpace (cord' G[j]).length + 3 * (cord' G[j]).length) ≤
              (G.map fun v => TS.listSpace (cord' v).length + 3 * (cord' v).length).sum := heq ▸ hsp_pref_le
          omega
        by_cases hjm : j = maxIdx
        · have hcond : Runs w pProg ω (.cond (.bin .eq (.reg 19) (.reg 17)) .nop (bundleStepScanRootStmt bTourList))
              st .normal st 5 :=
            runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, BinOp.eval, hr19c, hr17c, hjm, h1_w],
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          have hcand_eq : addCandsForGroupPrefix S cord' G maxIdx cand₀ (j + 1) =
              addCandsForGroupPrefix S cord' G maxIdx cand₀ j := by
            simp [addCandsForGroupPrefix, hjm]
          have hscan_eq : addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ (j + 1) =
              addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ j := by
            simp [addScanEndsForGroupPrefix, hjm]
          refine ⟨st, 5, (hCur, tx, touched), hcond, hr19c, ?_, rfl, ?_⟩
          · refine ⟨fun r hr h6 h13 => by
                simp only [Function.update_of_ne (show r ≠ 19 by omega)]
                exact hregs r hr h6 h13,
              by simp [hr6c], by simp [hr13c], by simp [hr17c], by simp,
              hhM_leC, le_trans hhCur_le (by simp [listSpacePrefix, hj]),
              hzeroC, htrepC, htfootC, hcand_eq ▸ hafterC, htouchC,
              hscan_eq ▸ hscanC, hscan_eq ▸ hscanInC, hscan_eq ▸ hcntC, hfrC⟩
          · dsimp only [sc]; simp only [hjm, ↓reduceIte]; omega
        · have hmem_v : st.mem (wBase + j) = G[j] := by
            have hw_disj_cur : wBase + j < btCurBunBase tbl slotCap eCap ∨
                btCurTagBase tbl slotCap eCap + slotCap ≤ wBase + j := by
              by_contra hnot; push Not at hnot
              exact hwBase_disj_foot (wBase + j) (by omega) (by omega)
                (Or.inl ⟨by unfold btCurBunBase at hnot; omega,
                  by unfold btCurTagBase at hnot; unfold bundleTableFixedSize; omega⟩)
            rw [hfrC (wBase + j) (by omega)
              (fun hf => hwBase_disj_foot _ (by omega) (by omega) (bundleTableCoreFoot_subset_foot hf))
              hw_disj_cur
              (hwBase_disj_touch _ (by omega) (by omega))
              (fun ht => by have := htfoot_disj_wBase _ ht; omega)]
            exact hG_mem j hj
          have htfoot_ltC : ∀ a, htour.rep.foot tourH tx a → a < hCur := fun a ha => by
            rcases htfootC a ha with h0 | ⟨_, hlt⟩
            · exact Nat.lt_of_lt_of_le (htfoot_lt a h0) (le_trans hh0_leM hhM_leC)
            · exact hlt
          have htfoot_disj_tblC : ∀ a, htour.rep.foot tourH tx a → ¬ bundleTableFoot eCap tbl m a := fun a ha hf => by
            rcases htfootC a ha with h0 | ⟨ha1, _⟩
            · exact htfoot_disj_tbl a h0 hf
            · exact absurd (hfoot_lt0 a hf) (by omega)
          have htfoot_disj_touchC : ∀ a, htour.rep.foot tourH tx a →
              a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a := fun a ha => by
            rcases htfootC a ha with h0 | ⟨ha1, _⟩
            · exact htfoot_disj_touch a h0
            · exact Or.inr (by omega)
          obtain ⟨stR, cR, hR, txR, touchedR, hrunR, hregsR, hr6R, hr13R, hhC_leR, hhR_le,
            hzeroR, htrepR, htfootR, hafterR, htouchR, hscanR, hscanInR, hcntR, hfrR, hcR⟩ :=
            bundleStepScanRoot_runs htour hw16 htourH_w hpk_w htbl_w hblks_w htouch_w hj
              (hG_lt _ (List.getElem_mem hj)) (hG_ends_lt _ (List.getElem_mem hj))
              (hG_nd _ (List.getElem_mem hj)) (by omega) hmem_v
              (le_trans hhStart_le (le_trans hh0_leM hhM_leC))
              hfoot_lt htouch_lt htouch_disj_foot htouch_disj_cur
              htfoot_ltC htfoot_disj_tblC htfoot_disj_touchC
              hzeroC hlist_sp_cur htrepC hafterC htouchC hscanC hscanInC hcntC
              (by rw [hregs 0 (by decide) (by decide) (by decide), hr0])
              (by rw [hregs 1 (by decide) (by decide) (by decide), hr1])
              (by rw [hregs 5 (by decide) (by decide) (by decide), hr5]) hr6c
              (by rw [hregs 7 (by decide) (by decide) (by decide), hr7])
              (by rw [hregs 8 (by decide) (by decide) (by decide), hr8])
              (by rw [hregs 9 (by decide) (by decide) (by decide), hr9])
              (by rw [hregs 10 (by decide) (by decide) (by decide), hr10])
              (by rw [hregs 11 (by decide) (by decide) (by decide), hr11])
              hr13c (by rw [hregs 16 (by decide) (by decide) (by decide), hr16]) hr19c
          have hcond : Runs w pProg ω (.cond (.bin .eq (.reg 19) (.reg 17)) .nop (bundleStepScanRootStmt bTourList))
              st .normal stR (3 + cR + 1) :=
            runs_cond_iff.mpr ⟨0, cR, by simp [Expr.eval, BinOp.eval, hr19c, hr17c, hjm],
              by simpa using hrunR, rfl⟩
          have hcand_step : addCandsForGroupPrefix S cord' G maxIdx cand₀ (j + 1) =
              addCandsForList S (cord' G[j]) (addCandsForGroupPrefix S cord' G maxIdx cand₀ j) := by
            simp [addCandsForGroupPrefix, hj, hjm]
          have hscan_step : addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ (j + 1) =
              addScanEndsForList S (addCandsForList S (cord' G[j]) (addCandsForGroupPrefix S cord' G maxIdx cand₀ j))
                G[j] (cord' G[j]) (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ j) := by
            simp [addScanEndsForGroupPrefix, hj, hjm, hcand_step]
          refine ⟨stR, 3 + cR + 1, (hR, txR, touchedR), hcond,
            (hregsR 19 (by decide) (by decide) (by decide)).trans hr19c, ?_, rfl, ?_⟩
          · refine ⟨fun r hr h6 h13 => by
                simp only [Function.update_of_ne (show r ≠ 19 by omega)]
                exact (hregsR r (by omega) h6 h13).trans (hregs r hr h6 h13),
              by simp [hr6R], by simp [hr13R],
              by simp [hregsR 17 (by decide) (by decide) (by decide), hr17c], by simp,
              le_trans hhM_leC hhC_leR,
              by simp only [listSpacePrefix, hj, ↓reduceDIte]; omega,
              hzeroR, htrepR,
              fun a ha => by
                rcases htfootR a ha with h1 | ⟨h1, h2⟩
                · rcases htfootC a h1 with h0 | ⟨ha1, ha2⟩
                  · exact Or.inl h0
                  · exact Or.inr ⟨ha1, Nat.lt_of_lt_of_le ha2 hhC_leR⟩
                · exact Or.inr ⟨le_trans (le_trans hh0_leM hhM_leC) h1, h2⟩,
              hcand_step ▸ hafterR, htouchR,
              hscan_step ▸ hscanR, hscan_step ▸ hscanInR, hscan_step ▸ hcntR,
              fun a ha hnf hnc hout hntf => by
                have hntfC : ¬ htour.rep.foot tourH tx a := fun h => by
                  rcases htfootC a h with h0 | ⟨ha1, _⟩
                  · exact hntf h0
                  · omega
                exact (hfrR a (Nat.lt_of_lt_of_le ha (le_trans hh0_leM hhM_leC)) hnf hnc hout hntfC).trans
                  (hfrC a ha hnf hnc hout hntf)⟩
          · dsimp only [sc]; simp only [hj, hjm, ↓reduceDIte, ↓reduceIte]; omega)
  rcases hInv_end with ⟨hregsE, hr6E, hr13E, _, _, hhM_leE, hhEnd_le, hzeroE, htrepE,
    htfootE, hafterE, htouchE, hscanE, hscanInE, hcntE, hfrE⟩
  rw [listSpacePrefix_eq_sum] at hhEnd_le
  refine ⟨st_end, cM + c_loop + 1, hEnd, txEnd, maxIdx, touchedEnd,
    bundle_runs_seq_normal hrunM hrun_loop,
    hregsE, hr6E, hr13E, hmax, le_trans hh0_leM hhM_leE, by omega,
    hzeroE, htrepE, htfootE, hafterE, htouchE, hscanE, hscanInE, hcntE, hfrE, ?_⟩
  have hrc : rangeCost sc 0 G.length =
      (TS.mul * ordStoreLog eCap + 110) * G.length +
        (TS.mul * ordStoreLog eCap + 355) * nonMaxLenPrefix cord' G maxIdx G.length := by
    have hgo : ∀ k ≤ G.length, rangeCost sc 0 k =
        (TS.mul * ordStoreLog eCap + 110) * k +
          (TS.mul * ordStoreLog eCap + 355) * nonMaxLenPrefix cord' G maxIdx k := by
      intro k
      induction k with
      | zero => intro _; simp [rangeCost, nonMaxLenPrefix]
      | succ k ih =>
        intro hk
        have hkG : k < G.length := by omega
        rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton, ← rangeCost_zero_eq_range, ih (by omega)]
        simp only [sc, nonMaxLenPrefix, hkG, ↓reduceDIte]
        split_ifs <;> ring
    exact hgo G.length (le_refl _)
  rw [hrc, nonMaxLenPrefix_eq_finset_sum] at hc_loop
  simp only [Expr.size_const, Expr.size_reg] at hc_loop
  have hmul : (2 * TS.mul * ordStoreLog eCap + 170) * G.length =
      (TS.mul * ordStoreLog eCap + 50) * G.length +
        (TS.mul * ordStoreLog eCap + 110) * G.length + 10 * G.length := by ring
  omega

end

end MinCostFlow.SparseCore.Program
