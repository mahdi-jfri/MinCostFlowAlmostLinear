module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepBunPrepProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstOutEdges
public import MinCostFlow.DynSpanner.Program.MergeSort

import WordRAM.Tactic

/-!
# Split-groups builder helpers and first half (`AssemblyFirstStepGroupsDefs`)

Provides the pure list/layout lemmas for `splitGroupsOf` and `readGroups` together with
`asmFirstBuildGroups_part1_runs`, which verifies the first half of the non-empty branch of
`asmFirstBuildGroupsStmt bSort`:
1. ancestor-tracking loop (`forRange 9 0 m`),
2. `mergeSort` and `dedup` producing `uniqL = splitOldRoots pairs`,
3. base-pointer setup (`grpOf`, `cntBase`, `curBase`, `groupPtr`),
4. `cnt` initialization loop (`forRange 9 0 nG`),
5. `binSearch` / `grpOf` / `cnt` counting loop (`forRange 9 0 m`).

The second half (group-header emission, scatter loop, and top-level `asmFirstBuildGroups_runs`)
lives in `AssemblyFirstStepGroupsProg.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## First half of `asmFirstBuildGroupsStmt`: loops 1–3 + sort/dedup -/

@[expose] public section

/-- The first half of the non-empty branch of `asmFirstBuildGroupsStmt`: ancestor scan,
`mergeSort`, `dedup`, pointer setup, `cnt := 1`, and `binSearch` / `grpOf` / `cnt` fill. -/
def asmFirstBuildGroupsPart1Stmt (bSort : ℕ) : Stmt :=
  .assign 4 (.bin .add (.reg 2) (.const 2)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 3)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
  forRange 9 (.const 0) (.reg 3)
    (.assign 10 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 4) (.reg 9)))) ;;
     .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9)))) ;;
     .assign 12 (.load (.bin .add (.reg 4) (.reg 10))) ;;
     .cond (.bin .eq (.reg 12) (.const 0))
       (.assign 13 (.reg 10))
       (.assign 13 (.bin .sub (.reg 12) (.const 1))) ;;
     .store (.bin .add (.reg 4) (.reg 11)) (.bin .add (.reg 13) (.const 1)) ;;
     .store (.bin .add (.reg 5) (.reg 9)) (.reg 13) ;;
     .store (.bin .add (.reg 6) (.reg 9)) (.reg 13)) ;;
  .call 14 (bSort + sortIdxMergeSort) [.reg 6, .reg 3, .reg 7] ;;
  .call 14 (bSort + sortIdxDedup) [.reg 6, .reg 3, .reg 8] ;;
  .assign 15 (.bin .add (.reg 8) (.reg 14)) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 3)) ;;
  .assign 17 (.bin .add (.reg 16) (.reg 14)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 14)) ;;
  forRange 9 (.const 0) (.reg 14)
    (.store (.bin .add (.reg 16) (.reg 9)) (.const 1)) ;;
  forRange 9 (.const 0) (.reg 3)
    (.assign 11 (.load (.bin .add (.reg 5) (.reg 9))) ;;
     .call 10 (bSort + sortIdxBinSearch) [.reg 8, .reg 14, .reg 11] ;;
     .store (.bin .add (.reg 15) (.reg 9)) (.reg 10) ;;
     .assign 12 (.load (.bin .add (.reg 16) (.reg 10))) ;;
     .store (.bin .add (.reg 16) (.reg 10)) (.bin .add (.reg 12) (.const 1)))

end

public section

private theorem asmFirstBuildGroups_loop2_runs {w spPtr vCap h m nG oldArr uniqOld grpOf cntBase curBase groupPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {s18 : State}
    (hw16 : 16 ≤ 2 ^ w) (hnG_le : nG ≤ m)
    (hSpace : h + (2 + vCap + 10 * m) < 2 ^ w)
    (huniqOld_eq : uniqOld = h + 2 + vCap + 3 * m)
    (hgrpOf_eq : grpOf = uniqOld + nG) (hcntBase_eq : cntBase = grpOf + m)
    (hcurBase_eq : curBase = cntBase + nG) (hgroupPtr_eq : groupPtr = curBase + nG)
    (hs18_0 : s18.regs 0 = spPtr) (hs18_2 : s18.regs 2 = h) (hs18_3 : s18.regs 3 = m)
    (hs18_5 : s18.regs 5 = oldArr) (hs18_8 : s18.regs 8 = uniqOld) (hs18_14 : s18.regs 14 = nG)
    (hs18_15 : s18.regs 15 = grpOf) (hs18_16 : s18.regs 16 = cntBase)
    (hs18_17 : s18.regs 17 = curBase) (hs18_18 : s18.regs 18 = groupPtr) :
    ∃ stL2 c,
      Runs w p ω
        (forRange 9 (.const 0) (.reg 14) (.store (.bin .add (.reg 16) (.reg 9)) (.const 1)))
        s18 .normal stL2 c ∧
      stL2.regs 0 = spPtr ∧ stL2.regs 2 = h ∧ stL2.regs 3 = m ∧ stL2.regs 5 = oldArr ∧
      stL2.regs 8 = uniqOld ∧ stL2.regs 14 = nG ∧
      stL2.regs 15 = grpOf ∧ stL2.regs 16 = cntBase ∧
      stL2.regs 17 = curBase ∧ stL2.regs 18 = groupPtr ∧
      (∀ gi < nG, stL2.mem (cntBase + gi) = 1) ∧
      (∀ a, a < cntBase ∨ curBase ≤ a → stL2.mem a = s18.mem a) ∧
      c ≤ 35 * nG + 15 := by
  have h1w : 1 < 2 ^ w := by omega
  let Inv2 : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r ≤ 18, r ≠ 9 → st.regs r = s18.regs r) ∧
    st.regs 9 = i ∧
    (∀ gi < i, st.mem (cntBase + gi) = 1) ∧
    (∀ a, a < cntBase ∨ curBase ≤ a → st.mem a = s18.mem a)
  have hInv2_0 : Inv2 0 () { s18 with regs := Function.update s18.regs 9 0 } :=
    ⟨fun r _ hne => Function.update_of_ne hne _ _, by simp [Function.update],
     fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  obtain ⟨stL2, cL2, _, hrunL2, ⟨hregsL2, _, hcntL2, hfrL2⟩, hcL2⟩ :=
    forRange_amort (ω := ω) (a₀ := ()) Inv2 (fun _ _ => 0) (fun _ => 20) nG h1w (by omega) hInv2_0
      (fun _ _ _ _ ⟨_, hr9, _⟩ => hr9)
      (fun _ _ _ _ ⟨hregs, _⟩ => Expr.eval_reg_of_eq ((hregs 14 (by omega) (by omega)).trans hs18_14))
      (fun i _ st hi ⟨hregs, hr9, hcnt, hfr⟩ => by
        have hr16 : st.regs 16 = cntBase := (hregs 16 (by omega) (by omega)).trans hs18_16
        set m' := Function.update st.mem (cntBase + i) 1
        have hst : Runs w p ω (.store (.bin .add (.reg 16) (.reg 9)) (.const 1)) st .normal ⟨m', st.regs, st.pos⟩ 5 :=
          runs_store_iff.mpr ⟨cntBase + i, 1, Expr.eval_add (Expr.eval_reg_of_eq hr16) (Expr.eval_reg_of_eq hr9) (by omega),
            Expr.eval_const h1w, rfl, rfl, rfl⟩
        refine ⟨⟨m', st.regs, st.pos⟩, 5, (), hst, hr9, ?_, rfl, by omega⟩
        refine ⟨fun r hr hne => by simp [Function.update_of_ne hne, hregs r hr hne],
          by simp [Function.update],
          fun gi hgi => by
            change m' (cntBase + gi) = 1; dsimp only [m']
            by_cases hEq : gi = i
            · subst hEq; exact Function.update_self _ _ _
            · rw [Function.update_of_ne (by omega)]; exact hcnt gi (by omega),
          fun a ha => by
            have hne : a ≠ cntBase + i := by clear * - ha hi hcurBase_eq; omega
            change m' a = s18.mem a; dsimp only [m']
            rw [Function.update_of_ne hne]; exact hfr a ha⟩)
  refine ⟨stL2, cL2, hrunL2,
    (hregsL2 0 (by omega) (by omega)).trans hs18_0, (hregsL2 2 (by omega) (by omega)).trans hs18_2,
    (hregsL2 3 (by omega) (by omega)).trans hs18_3, (hregsL2 5 (by omega) (by omega)).trans hs18_5,
    (hregsL2 8 (by omega) (by omega)).trans hs18_8, (hregsL2 14 (by omega) (by omega)).trans hs18_14,
    (hregsL2 15 (by omega) (by omega)).trans hs18_15, (hregsL2 16 (by omega) (by omega)).trans hs18_16,
    (hregsL2 17 (by omega) (by omega)).trans hs18_17, (hregsL2 18 (by omega) (by omega)).trans hs18_18,
    hcntL2, hfrL2, ?_⟩
  rw [rangeCost_const_eq] at hcL2
  simp only [Expr.size] at hcL2 ⊢
  omega

set_option maxHeartbeats 1200000 in
private theorem asmFirstBuildGroups_loop3_runs {w bSort spPtr vCap h m nG oldArr uniqOld grpOf cntBase curBase groupPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {pairs : List (ℕ × ℕ)} {oldL uniqL : List ℕ}
    {mem₀ : ℕ → ℕ} {stL2 : State}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w)
    (hpairs_len : pairs.length = m) (holdL_len : oldL.length = m)
    (hnG_def : nG = uniqL.length) (hnG_le : nG ≤ m)
    (hSpace : h + (2 + vCap + 10 * m) < 2 ^ w)
    (holdArr_eq : oldArr = h + 2 + vCap) (huniqOld_eq : uniqOld = h + 2 + vCap + 3 * m)
    (hgrpOf_eq : grpOf = uniqOld + nG) (hcntBase_eq : cntBase = grpOf + m)
    (hcurBase_eq : curBase = cntBase + nG) (hgroupPtr_eq : groupPtr = curBase + nG)
    (hUniqPW : uniqL.Pairwise (· < ·))
    (hUniq_mem_old : ∀ x, x ∈ uniqL ↔ x ∈ oldL)
    (hUniq_lt : ∀ x ∈ uniqL, x < vCap)
    (hr0 : stL2.regs 0 = spPtr) (hr2 : stL2.regs 2 = h) (hr3 : stL2.regs 3 = m) (hr5 : stL2.regs 5 = oldArr)
    (hr8 : stL2.regs 8 = uniqOld) (hr14 : stL2.regs 14 = nG)
    (hr15 : stL2.regs 15 = grpOf) (hr16 : stL2.regs 16 = cntBase)
    (hr17 : stL2.regs 17 = curBase) (hr18 : stL2.regs 18 = groupPtr)
    (hDD_oldAt : ListAt stL2.mem oldArr oldL)
    (hUniqAt : ListAt stL2.mem uniqOld uniqL)
    (hcntL2 : ∀ gi < nG, stL2.mem (cntBase + gi) = 1)
    (hDD_zr : ZeroFrom stL2.mem curBase)
    (hDD_fr : ∀ a < h, stL2.mem a = mem₀ a) :
    ∃ stL3 c,
      Runs w p ω
        (forRange 9 (.const 0) (.reg 3)
          (.assign 11 (.load (.bin .add (.reg 5) (.reg 9))) ;;
           .call 10 (bSort + sortIdxBinSearch) [.reg 8, .reg 14, .reg 11] ;;
           .store (.bin .add (.reg 15) (.reg 9)) (.reg 10) ;;
           .assign 12 (.load (.bin .add (.reg 16) (.reg 10))) ;;
           .store (.bin .add (.reg 16) (.reg 10)) (.bin .add (.reg 12) (.const 1))))
        stL2 .normal stL3 c ∧
      stL3.regs 0 = spPtr ∧ stL3.regs 2 = h ∧ stL3.regs 3 = m ∧
      stL3.regs 8 = uniqOld ∧ stL3.regs 14 = nG ∧
      stL3.regs 15 = grpOf ∧ stL3.regs 16 = cntBase ∧
      stL3.regs 17 = curBase ∧ stL3.regs 18 = groupPtr ∧
      ListAt stL3.mem uniqOld uniqL ∧
      (∀ j < m, stL3.mem (grpOf + j) = uniqL.idxOf (oldL.getD j 0)) ∧
      (∀ gi (hgi : gi < nG),
        stL3.mem (cntBase + gi) = 1 + (groupMembers pairs oldL (uniqL[gi]'(by omega))).length) ∧
      ZeroFrom stL3.mem curBase ∧
      (∀ a < h, stL3.mem a = mem₀ a) ∧
      c ≤ m * (45 * (Nat.log 2 (m + 1) + 1) + 95) + 30 := by
  have h1w : 1 < 2 ^ w := by omega
  have hUniq_nd : uniqL.Nodup := hUniqPW.imp fun hab => ne_of_lt hab
  let Inv3 : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r ≤ 18, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → st.regs r = stL2.regs r) ∧
    st.regs 9 = i ∧
    (∀ j (hj : j < i), st.mem (grpOf + j) = uniqL.idxOf (oldL.getD j 0)) ∧
    (∀ gi (hgi : gi < nG),
      st.mem (cntBase + gi) = 1 + (groupMembers (pairs.take i) oldL (uniqL[gi]'(by omega))).length) ∧
    (∀ a, a < grpOf ∨ curBase ≤ a → st.mem a = stL2.mem a)
  have hInv3_0 : Inv3 0 () { stL2 with regs := Function.update stL2.regs 9 0 } :=
    ⟨fun r _ h9 _ _ _ => Function.update_of_ne h9 _ _, by simp [Function.update],
     fun _ h => absurd h (Nat.not_lt_zero _),
     fun gi hgi => by simp [groupMembers, hcntL2 gi hgi],
     fun _ _ => rfl⟩
  obtain ⟨stL3, cL3, _, hrunL3, ⟨hregsL3, _, hgrpL3, hcntL3, hfrL3⟩, hcL3⟩ :=
    forRange_amort (ω := ω) (a₀ := ()) Inv3 (fun _ _ => 0)
      (fun _ => 45 * (Nat.log 2 (m + 1) + 1) + 80) m h1w (by omega) hInv3_0
      (fun _ _ _ _ ⟨_, hr9, _⟩ => hr9)
      (fun _ _ _ _ ⟨hregs, _⟩ => Expr.eval_reg_of_eq ((hregs 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr3))
      (fun i _ st hi ⟨hregs, hr9, hgrp, hcnt, hfr⟩ => by
        have hsr5 : st.regs 5 = oldArr := (hregs 5 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr5
        have hsr8 : st.regs 8 = uniqOld := (hregs 8 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr8
        have hsr14 : st.regs 14 = nG := (hregs 14 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr14
        have hsr15 : st.regs 15 = grpOf := (hregs 15 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr15
        have hsr16 : st.regs 16 = cntBase := (hregs 16 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr16
        set key := oldL.getD i 0
        have hkey_eq : st.mem (oldArr + i) = key := by
          rw [hfr _ (Or.inl (by omega)), hDD_oldAt i (by omega)]
          exact (List.getD_eq_getElem oldL 0 (by omega)).symm
        have hkey_in : key ∈ uniqL := (hUniq_mem_old key).mpr (by
          rw [show key = oldL[i]'(by omega) from List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
        have hkey_w : key < 2 ^ w := lt_trans (hUniq_lt key hkey_in) (by omega)
        have hUniq_st : ListAt st.mem uniqOld uniqL := fun j hj => by
          rw [hfr _ (Or.inl (by omega))]; exact hUniqAt j hj
        obtain ⟨bdBS, hbdBS, oBS, stBS, cBS, hrunBS, hpostBS, hcBS⟩ :=
          binSearch_meetsContract (w := w) (L := uniqL) (key := key) hpSort [uniqOld, nG, key] st.mem st.pos ω
            (fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
            ⟨uniqOld, by simp [hnG_def], hw16, by omega, hUniqPW, hkey_in, hUniq_st, fun x hx => lt_trans (hUniq_lt x hx) (by omega)⟩
        rcases hpostBS with ⟨_, _, hBSmem, hgi_eq, hgi_lt⟩
        set gi := uniqL.idxOf key
        have hgi_lt' : gi < nG := by rw [hnG_def]; exact hgi_eq ▸ hgi_lt
        have hgi_lt_u : gi < uniqL.length := by omega
        have hgi_val : uniqL[gi]'hgi_lt_u = key := List.getElem_idxOf hgi_lt_u
        set curC := st.mem (cntBase + gi)
        have hcurC_le : curC ≤ m + 1 := by
          have := hcnt gi hgi_lt'
          have hgm_le : (groupMembers (pairs.take i) oldL (uniqL[gi]'hgi_lt_u)).length ≤ m := by
            unfold groupMembers; rw [List.length_map]
            exact (List.length_filter_le _ _).trans (by simp; omega)
          omega
        set s11 : State := { st with regs := Function.update st.regs 11 key }
        set s10 : State := ⟨st.mem, Function.update s11.regs 10 gi, stBS.pos⟩
        set m1 := Function.update st.mem (grpOf + i) gi
        set s12 : State := ⟨m1, Function.update s10.regs 12 curC, stBS.pos⟩
        set m2 := Function.update m1 (cntBase + gi) (curC + 1)
        set sF : State := ⟨m2, s12.regs, stBS.pos⟩
        have e11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 5) (.reg 9)))) st .normal s11 5 :=
          runs_assign_iff.mpr ⟨key, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hsr5) (Expr.eval_reg_of_eq hr9) (by omega)) hkey_eq, rfl, rfl, rfl⟩
        have ec : Runs w p ω (.call 10 (bSort + sortIdxBinSearch) [.reg 8, .reg 14, .reg 11]) s11 .normal s10 (argsSize [.reg 8, .reg 14, .reg 11] + cBS + 1) :=
          runs_call_iff.mpr ⟨[uniqOld, nG, key], bdBS, oBS, stBS, cBS,
            by simp [evalArgs, Expr.eval, s11, hsr8, hsr14], hbdBS, hrunBS, rfl, by simp [s10, hBSmem, hgi_eq, gi], rfl⟩
        have es1 : Runs w p ω (.store (.bin .add (.reg 15) (.reg 9)) (.reg 10)) s10 .normal ⟨m1, s10.regs, stBS.pos⟩ 5 :=
          runs_store_iff.mpr ⟨grpOf + i, gi, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s10, s11, hsr15]))
            (Expr.eval_reg_of_eq (by simp [s10, s11, hr9])) (by omega), Expr.eval_reg_of_eq (by simp [s10]), rfl, rfl, rfl⟩
        have e12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 16) (.reg 10)))) ⟨m1, s10.regs, stBS.pos⟩ .normal s12 5 :=
          runs_assign_iff.mpr ⟨curC, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s10, s11, hsr16]))
            (Expr.eval_reg_of_eq (by simp [s10])) (by omega)) (Function.update_of_ne (by omega) _ _), rfl, rfl, rfl⟩
        have es2 : Runs w p ω (.store (.bin .add (.reg 16) (.reg 10)) (.bin .add (.reg 12) (.const 1))) s12 .normal sF 7 :=
          runs_store_iff.mpr ⟨cntBase + gi, curC + 1,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [s12, s10, s11, hsr16])) (Expr.eval_reg_of_eq (by simp [s12, s10])) (by omega),
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [s12])) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
        have hrun := runs_seq_iff.mpr (Or.inr ⟨s11, _, _, e11,
          runs_seq_iff.mpr (Or.inr ⟨s10, _, _, ec,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es1,
          runs_seq_iff.mpr (Or.inr ⟨s12, _, _, e12, es2, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have hlog_le : Nat.log 2 (nG + 1) ≤ Nat.log 2 (m + 1) := Nat.log_mono_right (by omega)
        refine ⟨sF, _, (), hrun, by simp [sF, s12, s10, s11, hr9], ?_, rfl, ?_⟩
        · refine ⟨fun r hr h9 h10 h11 h12 => by
              simp [sF, s12, s10, s11, Function.update_of_ne h9, Function.update_of_ne h12,
                Function.update_of_ne h10, Function.update_of_ne h11, hregs r hr h9 h10 h11 h12],
            by simp [Function.update],
            fun j hj => by
              change m2 (grpOf + j) = _; dsimp only [m2, m1]
              rw [Function.update_of_ne (by omega)]
              by_cases hEq : j = i
              · subst hEq; simp [gi, key]
              · rw [Function.update_of_ne (by omega)]; exact hgrp j (by omega),
            fun gj hgj => by
              change m2 (cntBase + gj) = _; dsimp only [m2, m1]
              rw [groupMembers_take_succ pairs oldL (uniqL[gj]'(by omega)) (by omega), List.length_append]
              by_cases hEq : gj = gi
              · subst hEq; simp [curC, hcnt gi hgi_lt', hgi_val, key]; omega
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                have hne_v : key ≠ uniqL[gj]'(by omega) := fun h =>
                  hEq (congrArg Fin.val (List.nodup_iff_injective_getElem.mp
                    hUniq_nd (a₁ := ⟨gi, hgi_lt_u⟩) (a₂ := ⟨gj, by omega⟩) (hgi_val.trans h)).symm)
                rw [show oldL.getD i 0 = key from rfl, ite_eq_right_iff.mpr (fun h => absurd h hne_v), List.length_nil, Nat.add_zero]
                exact hcnt gj hgj,
            fun a ha => by
              have hne1 : a ≠ cntBase + gi := by clear * - ha hgi_lt' hcurBase_eq hcntBase_eq; omega
              have hne2 : a ≠ grpOf + i := by clear * - ha hi hcntBase_eq hcurBase_eq; omega
              change m2 a = stL2.mem a; dsimp only [m2, m1]
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2]; exact hfr a ha⟩
        · dsimp only [binSearchContract] at hcBS
          rw [← hnG_def] at hcBS
          simp only [argsSize, Expr.size]
          clear * - hcBS hlog_le
          have : 45 * (Nat.log 2 (nG + 1) + 1) ≤ 45 * (Nat.log 2 (m + 1) + 1) :=
            Nat.mul_le_mul_left 45 (by omega)
          omega)
  refine ⟨stL3, cL3, hrunL3,
    (hregsL3 0 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr0,
    (hregsL3 2 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr2,
    (hregsL3 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr3,
    (hregsL3 8 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr8,
    (hregsL3 14 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr14,
    (hregsL3 15 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr15,
    (hregsL3 16 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr16,
    (hregsL3 17 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr17,
    (hregsL3 18 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr18,
    fun j hj => (hfrL3 _ (Or.inl (by omega))).trans (hUniqAt j hj),
    hgrpL3,
    fun gi hgi => by
      have htk : pairs.take m = pairs := by rw [← hpairs_len, List.take_length]
      have h := hcntL3 gi hgi; rwa [htk] at h,
    fun a ha => (hfrL3 a (Or.inr ha)).trans (hDD_zr a ha),
    fun a ha => (hfrL3 a (Or.inl (by omega))).trans (hDD_fr a ha), ?_⟩
  rw [rangeCost_const_eq] at hcL3
  simp only [Expr.size] at hcL3 ⊢
  nlinarith

set_option maxHeartbeats 600000 in
private theorem asmFirstBuildGroups_part1b_runs {w bSort spPtr vCap h m nG oldArr uniqOld grpOf cntBase curBase groupPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {pairs : List (ℕ × ℕ)} {oldL uniqL : List ℕ}
    {mem₀ : ℕ → ℕ} {stDD' : State}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w)
    (hpairs_len : pairs.length = m) (holdL_len : oldL.length = m)
    (hnG_def : nG = uniqL.length) (hnG_le : nG ≤ m)
    (hSpace : h + (2 + vCap + 10 * m) < 2 ^ w)
    (holdArr_eq : oldArr = h + 2 + vCap) (huniqOld_eq : uniqOld = h + 2 + vCap + 3 * m)
    (hgrpOf_eq : grpOf = uniqOld + nG) (hcntBase_eq : cntBase = grpOf + m)
    (hcurBase_eq : curBase = cntBase + nG) (hgroupPtr_eq : groupPtr = curBase + nG)
    (hUniqPW : uniqL.Pairwise (· < ·))
    (hUniq_mem_old : ∀ x, x ∈ uniqL ↔ x ∈ oldL)
    (hUniq_lt : ∀ x ∈ uniqL, x < vCap)
    (hhr0 : stDD'.regs 0 = spPtr) (hhr2 : stDD'.regs 2 = h) (hhr3 : stDD'.regs 3 = m)
    (hhr5 : stDD'.regs 5 = oldArr) (hhr8 : stDD'.regs 8 = uniqOld) (hhr14 : stDD'.regs 14 = nG)
    (hDD_oldAt : ListAt stDD'.mem oldArr oldL)
    (hUniqAt : ListAt stDD'.mem uniqOld uniqL)
    (hDD_zr : ZeroFrom stDD'.mem (uniqOld + nG))
    (hDD_fr : ∀ a < h, stDD'.mem a = mem₀ a) :
    ∃ stL3 c,
      Runs w p ω
        (.assign 15 (.bin .add (.reg 8) (.reg 14)) ;;
         .assign 16 (.bin .add (.reg 15) (.reg 3)) ;;
         .assign 17 (.bin .add (.reg 16) (.reg 14)) ;;
         .assign 18 (.bin .add (.reg 17) (.reg 14)) ;;
         forRange 9 (.const 0) (.reg 14) (.store (.bin .add (.reg 16) (.reg 9)) (.const 1)) ;;
         forRange 9 (.const 0) (.reg 3)
           (.assign 11 (.load (.bin .add (.reg 5) (.reg 9))) ;;
            .call 10 (bSort + sortIdxBinSearch) [.reg 8, .reg 14, .reg 11] ;;
            .store (.bin .add (.reg 15) (.reg 9)) (.reg 10) ;;
            .assign 12 (.load (.bin .add (.reg 16) (.reg 10))) ;;
            .store (.bin .add (.reg 16) (.reg 10)) (.bin .add (.reg 12) (.const 1))))
        stDD' .normal stL3 c ∧
      stL3.regs 0 = spPtr ∧ stL3.regs 2 = h ∧ stL3.regs 3 = m ∧
      stL3.regs 8 = uniqOld ∧ stL3.regs 14 = nG ∧
      stL3.regs 15 = grpOf ∧ stL3.regs 16 = cntBase ∧
      stL3.regs 17 = curBase ∧ stL3.regs 18 = groupPtr ∧
      ListAt stL3.mem uniqOld uniqL ∧
      (∀ j < m, stL3.mem (grpOf + j) = uniqL.idxOf (oldL.getD j 0)) ∧
      (∀ gi (hgi : gi < nG),
        stL3.mem (cntBase + gi) = 1 + (groupMembers pairs oldL (uniqL[gi]'(by omega))).length) ∧
      ZeroFrom stL3.mem curBase ∧
      (∀ a < h, stL3.mem a = mem₀ a) ∧
      c ≤ m * (45 * (Nat.log 2 (m + 1) + 1) + 95) + 35 * nG + 80 := by
  set s15 : State := { stDD' with regs := Function.update stDD'.regs 15 grpOf }
  set s16 : State := { s15 with regs := Function.update s15.regs 16 cntBase }
  set s17 : State := { s16 with regs := Function.update s16.regs 17 curBase }
  set s18 : State := { s17 with regs := Function.update s17.regs 18 groupPtr }
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 8) (.reg 14))) stDD' .normal s15 4 := by
    refine runs_assign_iff.mpr ⟨grpOf, ?_, rfl, rfl, rfl⟩
    rw [hgrpOf_eq]; exact Expr.eval_add (w := w) (Expr.eval_reg_of_eq hhr8) (Expr.eval_reg_of_eq hhr14) (by omega)
  have ha16 : Runs w p ω (.assign 16 (.bin .add (.reg 15) (.reg 3))) s15 .normal s16 4 := by
    refine runs_assign_iff.mpr ⟨cntBase, ?_, rfl, rfl, rfl⟩
    rw [hcntBase_eq]
    exact Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s15.regs 15 = grpOf by simp [s15]))
      (Expr.eval_reg_of_eq (show s15.regs 3 = m by simp [s15, hhr3])) (by omega)
  have ha17 : Runs w p ω (.assign 17 (.bin .add (.reg 16) (.reg 14))) s16 .normal s17 4 := by
    refine runs_assign_iff.mpr ⟨curBase, ?_, rfl, rfl, rfl⟩
    rw [hcurBase_eq]
    exact Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s16.regs 16 = cntBase by simp [s16]))
      (Expr.eval_reg_of_eq (show s16.regs 14 = nG by simp [s16, s15, hhr14])) (by omega)
  have ha18 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.reg 14))) s17 .normal s18 4 := by
    refine runs_assign_iff.mpr ⟨groupPtr, ?_, rfl, rfl, rfl⟩
    rw [hgroupPtr_eq]
    exact Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s17.regs 17 = curBase by simp [s17]))
      (Expr.eval_reg_of_eq (show s17.regs 14 = nG by simp [s17, s16, s15, hhr14])) (by omega)
  obtain ⟨stL2, c2, hL2, r0, r2, r3, r5, r8, r14, r15, r16, r17, r18, hcnt2, hfr2, hc2⟩ :=
    asmFirstBuildGroups_loop2_runs (spPtr := spPtr) (oldArr := oldArr) (s18 := s18) hw16 hnG_le hSpace huniqOld_eq hgrpOf_eq hcntBase_eq hcurBase_eq
      hgroupPtr_eq (by simp [s18, s17, s16, s15, hhr0]) (by simp [s18, s17, s16, s15, hhr2])
      (by simp [s18, s17, s16, s15, hhr3]) (by simp [s18, s17, s16, s15, hhr5])
      (by simp [s18, s17, s16, s15, hhr8]) (by simp [s18, s17, s16, s15, hhr14])
      (by simp [s18, s17, s16, s15]) (by simp [s18, s17, s16]) (by simp [s18, s17]) (by simp [s18])
  obtain ⟨stL3, c3, hrun3, hr0, hr2, hr3, hr8, hr14, hr15, hr16, hr17, hr18, hU3, hgrp3, hcnt3, hzr3, hfr3, hc3⟩ :=
    asmFirstBuildGroups_loop3_runs hpSort hw16 hpairs_len holdL_len hnG_def hnG_le hSpace
      holdArr_eq huniqOld_eq hgrpOf_eq hcntBase_eq hcurBase_eq hgroupPtr_eq
      hUniqPW hUniq_mem_old hUniq_lt r0 r2 r3 r5 r8 r14 r15 r16 r17 r18
      (fun j hj => (hfr2 _ (Or.inl (by omega))).trans (hDD_oldAt j hj))
      (fun j hj => (hfr2 _ (Or.inl (by omega))).trans (hUniqAt j hj))
      hcnt2 (fun a ha => (hfr2 a (Or.inr ha)).trans (hDD_zr a (by omega)))
      (fun a ha => (hfr2 a (Or.inl (by omega))).trans (hDD_fr a ha))
  have hfull :=
    runs_seq_iff.mpr (Or.inr ⟨s15, _, _, ha15,
    runs_seq_iff.mpr (Or.inr ⟨s16, _, _, ha16,
    runs_seq_iff.mpr (Or.inr ⟨s17, _, _, ha17,
    runs_seq_iff.mpr (Or.inr ⟨s18, _, _, ha18,
    runs_seq_iff.mpr (Or.inr ⟨stL2, _, _, hL2, hrun3, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hcost : 4 + (4 + (4 + (4 + (c2 + c3 + 1) + 1) + 1) + 1) + 1 ≤
      m * (45 * (Nat.log 2 (m + 1) + 1) + 95) + 35 * nG + 80 := by
    clear * - hc2 hc3; omega
  exact ⟨stL3, _, hfull, hr0, hr2, hr3, hr8, hr14, hr15, hr16, hr17, hr18, hU3, hgrp3, hcnt3, hzr3, hfr3, hcost⟩

set_option maxHeartbeats 1200000 in
theorem asmFirstBuildGroups_part1_runs {w bSort spPtr vCap h pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {L : List CompSplitEntry} {mem₀ : ℕ → ℕ}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w)
    (hSp : SplitEntriesAt mem₀ spPtr L)
    (hSp_lt : spPtr + splitEntriesWords L ≤ h)
    (hL_vCap : ∀ s ∈ L, s.kept < vCap ∧ s.fresh < vCap)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + buildGroupsSpace vCap L.length < 2 ^ w) :
    let m := L.length
    let pairs := L.map fun s => (s.kept, s.fresh)
    let oldL := splitOldList pairs (fun _ => 0)
    let uniqL := splitOldRoots pairs
    let nG := uniqL.length
    let uniqOld := h + 2 + vCap + 3 * m
    let grpOf := uniqOld + nG
    let cntBase := grpOf + m
    let curBase := cntBase + nG
    let groupPtr := curBase + nG
    let stA : State := { startState [spPtr, vCap, h] mem₀ pos with
      regs := Function.update (startState [spPtr, vCap, h] mem₀ pos).regs 3 m }
    ∃ st3 c,
      Runs w p ω (asmFirstBuildGroupsPart1Stmt bSort) stA .normal st3 c ∧
      uniqL.Pairwise (· < ·) ∧
      (∀ x, x ∈ uniqL ↔ x ∈ oldL) ∧
      nG ≤ m ∧
      st3.regs 0 = spPtr ∧ st3.regs 2 = h ∧ st3.regs 3 = m ∧
      st3.regs 8 = uniqOld ∧ st3.regs 14 = nG ∧
      st3.regs 15 = grpOf ∧ st3.regs 16 = cntBase ∧
      st3.regs 17 = curBase ∧ st3.regs 18 = groupPtr ∧
      ListAt st3.mem uniqOld uniqL ∧
      (∀ j < m, st3.mem (grpOf + j) = uniqL.idxOf (oldL.getD j 0)) ∧
      (∀ gi (hgi : gi < nG),
        st3.mem (cntBase + gi) = 1 + (groupMembers pairs oldL (uniqL[gi]'hgi)).length) ∧
      ZeroFrom st3.mem curBase ∧
      (∀ a < h, st3.mem a = mem₀ a) ∧
      c ≤ 245 * m * (Nat.log 2 (m + 1) + 1) + 320 * m + 350 := by
  intro m pairs oldL uniqL nG uniqOld grpOf cntBase curBase groupPtr stA
  have hpairs_len : pairs.length = m := List.length_map _
  have holdL_len : oldL.length = m := by rw [splitOldList_length, hpairs_len]
  have hpairs_lt : ∀ q ∈ pairs, q.1 < vCap ∧ q.2 < vCap := fun q hq => by
    rcases List.mem_map.mp hq with ⟨s, hs, rfl⟩; exact hL_vCap s hs
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hSp_words : splitEntriesWords L = 1 + 4 * m := rfl
  have hSpace_un : h + (2 + vCap + 10 * m) < 2 ^ w := by unfold buildGroupsSpace at hSpace; exact hSpace
  set st0 := startState [spPtr, vCap, h] mem₀ pos
  set ancBase := h + 2
  set oldArr := ancBase + vCap
  set oldSorted := oldArr + m
  set scr := oldSorted + m
  have huniqOld_eq : scr + m = uniqOld := by omega
  set st4 : State := { stA with regs := Function.update stA.regs 4 ancBase }
  set st5 : State := { st4 with regs := Function.update st4.regs 5 oldArr }
  set st6 : State := { st5 with regs := Function.update st5.regs 6 oldSorted }
  set st7 : State := { st6 with regs := Function.update st6.regs 7 scr }
  set st8 : State := { st7 with regs := Function.update st7.regs 8 uniqOld }
  have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 2) (.const 2))) stA .normal st4 4 :=
    runs_assign_iff.mpr ⟨ancBase, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, startState])) (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
  have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.reg 1))) st4 .normal st5 4 :=
    runs_assign_iff.mpr ⟨oldArr, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4])) (Expr.eval_reg_of_eq (by simp [st4, stA, startState])) (by omega), rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 3))) st5 .normal st6 4 :=
    runs_assign_iff.mpr ⟨oldSorted, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5])) (Expr.eval_reg_of_eq (by simp [st5, st4, stA])) (by omega), rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 3))) st6 .normal st7 4 :=
    runs_assign_iff.mpr ⟨scr, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6])) (Expr.eval_reg_of_eq (by simp [st6, st5, st4, stA])) (by omega), rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.reg 3))) st7 .normal st8 4 :=
    runs_assign_iff.mpr ⟨uniqOld, by rw [← huniqOld_eq]; exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [st7])) (Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, stA])) (by omega), rfl, rfl, rfl⟩
  -- Loop 1 (`forRange 9 0 m`)
  let Inv1 : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r ≤ 8, st.regs r = st8.regs r) ∧
    st.regs 9 = i ∧
    (∀ v < vCap, st.mem (ancBase + v) = splitAncFold (pairs.take i) (fun _ => 0) v) ∧
    (∀ j (hj : j < i), ∀ hjm : j < m,
      st.mem (oldArr + j) = oldL[j]'(by omega) ∧
      st.mem (oldSorted + j) = oldL[j]'(by omega)) ∧
    ZeroFrom st.mem scr ∧
    (∀ a < h, st.mem a = mem₀ a)
  have hInv1_0 : Inv1 0 () { st8 with regs := Function.update st8.regs 9 0 } :=
    ⟨fun r hr => Function.update_of_ne (by omega : r ≠ 9) _ _, by simp [Function.update],
     fun v hv => by simp [splitAncFold]; exact hZero (ancBase + v) (by omega),
     fun _ hj => absurd hj (Nat.not_lt_zero _),
     fun a ha => hZero a (by omega), fun _ _ => rfl⟩
  obtain ⟨stL1, cL1, _, hrunL1, ⟨hregsL1, _, _, holdL1, hzrL1, hfrL1⟩, hcL1⟩ :=
    forRange_amort (ω := ω) (a₀ := ()) Inv1 (fun _ _ => 0) (fun _ => 75) m h1w (by omega) hInv1_0
      (fun _ _ _ _ ⟨_, hr9, _⟩ => hr9)
      (fun _ _ _ _ ⟨hregs, _⟩ => Expr.eval_reg_of_eq ((hregs 3 (by omega)).trans (by simp [st8, st7, st6, st5, st4, stA])))
      (fun i _ st hi ⟨hregs, hr9, hanc, hold_i, hzr, hfr⟩ => by
        have hr0 : st.regs 0 = spPtr := (hregs 0 (by omega)).trans (by simp [st8, st7, st6, st5, st4, stA, startState])
        have hr4 : st.regs 4 = ancBase := (hregs 4 (by omega)).trans (by simp [st8, st7, st6, st5, st4])
        have hr5 : st.regs 5 = oldArr := (hregs 5 (by omega)).trans (by simp [st8, st7, st6, st5])
        have hr6 : st.regs 6 = oldSorted := (hregs 6 (by omega)).trans (by simp [st8, st7, st6])
        set kept := (L[i]'hi).kept
        set fresh := (L[i]'hi).fresh
        have hk_lt : kept < vCap := (hL_vCap _ (List.getElem_mem hi)).1
        have hf_lt : fresh < vCap := (hL_vCap _ (List.getElem_mem hi)).2
        have hk_mem : st.mem (spPtr + 3 + 4 * i) = kept := by
          rw [hfr _ (by omega), show spPtr + 3 + 4 * i = spPtr + 1 + 4 * i + 2 by omega]
          exact (hSp.2 i hi).2.2.1
        have hf_mem : st.mem (spPtr + 4 + 4 * i) = fresh := by
          rw [hfr _ (by omega), show spPtr + 4 + 4 * i = spPtr + 1 + 4 * i + 3 by omega]
          exact (hSp.2 i hi).2.2.2
        set anc_i := splitAncFold (pairs.take i) (fun _ => 0)
        have hanc_le : ∀ v < vCap, anc_i v ≤ vCap :=
          (splitAncFold_lt (pairs.take i) vCap (fun q hq => hpairs_lt q (List.mem_of_mem_take hq))
            (fun _ => 0) (fun _ _ => Nat.zero_le _) (fun _ _ => rfl)).1
        set aVal := anc_i kept
        have ha_mem : st.mem (ancBase + kept) = aVal := hanc kept hk_lt
        set rVal := ancDecode anc_i kept
        have hr_lt : rVal < vCap := by
          unfold rVal ancDecode; split_ifs with h0; exact hk_lt; have := hanc_le kept hk_lt; omega
        have hr_eq_old : rVal = oldL[i]'(by omega) := by
          have hi_p : i < pairs.length := by omega
          have hget := splitOldList_getElem pairs (fun _ => 0) hi_p
          have hp_i : (pairs[i]'hi_p) = (kept, fresh) := by simp [pairs, kept, fresh]
          simpa [oldL, anc_i, rVal, hp_i] using hget.symm
        set s10 : State := { st with regs := Function.update st.regs 10 kept }
        set s11 : State := { s10 with regs := Function.update s10.regs 11 fresh }
        set s12 : State := { s11 with regs := Function.update s11.regs 12 aVal }
        set s13 : State := { s12 with regs := Function.update s12.regs 13 rVal }
        set m1 := Function.update st.mem (ancBase + fresh) (rVal + 1)
        set m2 := Function.update m1 (oldArr + i) rVal
        set m3 := Function.update m2 (oldSorted + i) rVal
        set sF : State := ⟨m3, s13.regs, st.pos⟩
        have e10 : Runs w p ω (.assign 10 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 4) (.reg 9))))) st .normal s10 _ :=
          runs_assign_iff.mpr ⟨kept, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const h3w) (by omega))
            (Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq hr9) (by omega)) (by omega)) hk_mem, rfl, rfl, rfl⟩
        have e11 : Runs w p ω (.assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9))))) s10 .normal s11 _ :=
          runs_assign_iff.mpr ⟨fresh, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s10, hr0])) (Expr.eval_const h4w) (by omega))
            (Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq (by simp [s10, hr9])) (by omega)) (by omega)) hf_mem, rfl, rfl, rfl⟩
        have e12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 4) (.reg 10)))) s11 .normal s12 _ :=
          runs_assign_iff.mpr ⟨aVal, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s11, s10, hr4]))
            (Expr.eval_reg_of_eq (by simp [s11, s10])) (by omega)) ha_mem, rfl, rfl, rfl⟩
        have e13 : ∃ c13, Runs w p ω (.cond (.bin .eq (.reg 12) (.const 0)) (.assign 13 (.reg 10))
            (.assign 13 (.bin .sub (.reg 12) (.const 1)))) s12 .normal s13 c13 ∧ c13 ≤ 10 := by
          by_cases ha0 : aVal = 0
          · have hr_k : rVal = kept := by dsimp only [rVal, ancDecode]; rw [show anc_i kept = 0 from ha0]; simp
            have hc : (Expr.bin .eq (.reg 12) (.const 0)).eval w s12 = some 1 := by simp [Expr.eval, BinOp.eval, s12, ha0, h0w, h1w]
            have et : Runs w p ω (.assign 13 (.reg 10)) s12 .normal s13 2 :=
              runs_assign_iff.mpr ⟨kept, Expr.eval_reg_of_eq (by simp [s12, s11, s10]), rfl, by simp [s13, hr_k], rfl⟩
            exact ⟨_, runs_cond_iff.mpr ⟨1, 2, hc, by simp only [one_ne_zero, ↓reduceIte]; exact et, rfl⟩, by simp [Expr.size]⟩
          · have hr_s : rVal = aVal - 1 := by
              dsimp only [rVal, ancDecode]; rw [ite_eq_right_iff.mpr (fun h => absurd h ha0)]
            have hc : (Expr.bin .eq (.reg 12) (.const 0)).eval w s12 = some 0 := by simp [Expr.eval, BinOp.eval, s12, ha0, h0w]
            have ha_w : aVal < 2 ^ w := by have := hanc_le kept hk_lt; omega
            have es := Expr.eval_sub (Expr.eval_reg_of_eq (show s12.regs 12 = aVal by simp [s12])) (Expr.eval_const h1w) ha_w
            have ef : Runs w p ω (.assign 13 (.bin .sub (.reg 12) (.const 1))) s12 .normal s13 4 :=
              runs_assign_iff.mpr ⟨aVal - 1, es, rfl, by simp [s13, hr_s], rfl⟩
            exact ⟨_, runs_cond_iff.mpr ⟨0, 4, hc, by simp only [↓reduceIte]; exact ef, rfl⟩, by simp [Expr.size]⟩
        obtain ⟨c13, h13, hc13⟩ := e13
        have es1 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 11)) (.bin .add (.reg 13) (.const 1))) s13 .normal ⟨m1, s13.regs, st.pos⟩ _ :=
          runs_store_iff.mpr ⟨ancBase + fresh, rVal + 1,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [s13, s12, s11, s10, hr4])) (Expr.eval_reg_of_eq (by simp [s13, s12, s11])) (by omega),
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [s13])) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
        have es2 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 9)) (.reg 13)) ⟨m1, s13.regs, st.pos⟩ .normal ⟨m2, s13.regs, st.pos⟩ _ :=
          runs_store_iff.mpr ⟨oldArr + i, rVal,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [s13, s12, s11, s10, hr5])) (Expr.eval_reg_of_eq (by simp [s13, s12, s11, s10, hr9])) (by omega),
            Expr.eval_reg_of_eq (by simp [s13]), rfl, rfl, rfl⟩
        have es3 : Runs w p ω (.store (.bin .add (.reg 6) (.reg 9)) (.reg 13)) ⟨m2, s13.regs, st.pos⟩ .normal sF _ :=
          runs_store_iff.mpr ⟨oldSorted + i, rVal,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [s13, s12, s11, s10, hr6])) (Expr.eval_reg_of_eq (by simp [s13, s12, s11, s10, hr9])) (by omega),
            Expr.eval_reg_of_eq (by simp [s13]), rfl, rfl, rfl⟩
        have hrun := runs_seq_iff.mpr (Or.inr ⟨s10, _, _, e10,
          runs_seq_iff.mpr (Or.inr ⟨s11, _, _, e11,
          runs_seq_iff.mpr (Or.inr ⟨s12, _, _, e12,
          runs_seq_iff.mpr (Or.inr ⟨s13, _, _, h13,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es2, es3, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have hanc_next : splitAncFold (pairs.take (i + 1)) (fun _ => 0) = splitAncStep anc_i (kept, fresh) := by
          have hi_p : i < pairs.length := by omega
          have h1 := splitAncFold_take_succ pairs (fun _ => 0) hi_p
          have hp_i : (pairs[i]'hi_p) = (kept, fresh) := by simp [pairs, kept, fresh]
          rwa [hp_i] at h1
        refine ⟨sF, _, (), hrun, by simp [sF, s13, s12, s11, s10, hr9], ?_, rfl, by simp only [Expr.size]; omega⟩
        refine ⟨fun r hr => by simp [sF, s13, s12, s11, s10, Function.update_of_ne (by omega : r ≠ 9),
            Function.update_of_ne (by omega : r ≠ 13),
            Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11),
            Function.update_of_ne (by omega : r ≠ 10), hregs r hr],
          by simp [Function.update],
          fun v hv => by
            rw [hanc_next]; change m3 (ancBase + v) = splitAncStep anc_i (kept, fresh) v
            dsimp only [m3, m2, m1, splitAncStep]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            by_cases heq : v = fresh
            · subst heq; simp [rVal]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne heq]; exact hanc v hv,
          fun j hj hjm => by
            change m3 (oldArr + j) = _ ∧ m3 (oldSorted + j) = _
            dsimp only [m3, m2, m1]
            by_cases hji : j < i
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hold_i j hji hjm
            · have heq : j = i := by omega
              subst heq
              exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self]; exact hr_eq_old,
                by rw [Function.update_self]; exact hr_eq_old⟩,
          fun a ha => by
            change m3 a = 0; dsimp only [m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hzr a ha,
          fun a ha => by
            change m3 a = mem₀ a; dsimp only [m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr a ha⟩)
  have hL1_oldAt : ListAt stL1.mem oldArr oldL := fun i hi => (holdL1 i (by omega) (by omega)).1
  have hL1_srtAt : ListAt stL1.mem oldSorted oldL := fun i hi => (holdL1 i (by omega) (by omega)).2
  have holdL_lt : ∀ x ∈ oldL, x < vCap := fun x hx => by
    rw [List.mem_iff_getElem] at hx; rcases hx with ⟨i, hi, rfl⟩
    have him : i < pairs.length := by omega
    rw [splitOldList_getElem pairs (fun _ => 0) him]
    have hanc_le := (splitAncFold_lt (pairs.take i) vCap
      (fun q hq => hpairs_lt q (List.mem_of_mem_take hq)) (fun _ => 0)
      (fun _ _ => Nat.zero_le _) (fun _ _ => rfl)).1
    have h1 := (hpairs_lt _ (List.getElem_mem him)).1
    unfold ancDecode; split_ifs; exact h1; have := hanc_le _ h1; omega
  -- `mergeSort` and `dedup`
  obtain ⟨bdMS, hbdMS, oMS, stMS, cMS, hrunMS, hpostMS, hcMS⟩ :=
    mergeSort_meetsContract (w := w) (L := oldL) hpSort hpSort [oldSorted, m, scr] stL1.mem stL1.pos ω
      (fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨oldSorted, scr, by simp [holdL_len], hw16, by omega, by omega, Or.inl (by omega),
       hL1_srtAt, fun x hx => lt_trans (holdL_lt x hx) (by omega)⟩
  rcases hpostMS with ⟨aMS, scrMS, L', hargsMS, _, hPerm, hSorted, hAtMS, hfrMS⟩
  have haMS : aMS = oldSorted := by injection hargsMS with h1; exact h1.symm
  have hscrMS : scrMS = scr := by injection hargsMS with _ h2; injection h2 with _ h3; injection h3 with h4; exact h4.symm
  subst haMS hscrMS
  have hL'_len : L'.length = m := by rw [hPerm.length_eq, holdL_len]
  set stMS' : State := ⟨stMS.mem, Function.update stL1.regs 14 oMS.value, stMS.pos⟩
  have hcallMS : Runs w p ω (.call 14 (bSort + sortIdxMergeSort) [.reg 6, .reg 3, .reg 7]) stL1 .normal stMS' _ :=
    runs_call_iff.mpr ⟨[oldSorted, m, scr], bdMS, oMS, stMS, cMS,
      by simp [evalArgs, Expr.eval, hregsL1 6 (by omega), hregsL1 3 (by omega), hregsL1 7 (by omega),
               st8, st7, st6, st5, st4, stA], hbdMS, hrunMS, rfl, rfl, rfl⟩
  have hMS_oldAt : ListAt stMS.mem oldArr oldL := fun i hi => by
    rw [hfrMS (oldArr + i) (Or.inl (by omega)) (Or.inl (by omega))]; exact hL1_oldAt i hi
  have hMS_zr : ZeroFrom stMS.mem uniqOld := fun a ha => by
    rw [hfrMS a (Or.inr (by omega)) (Or.inr (by omega))]; exact hzrL1 a (by omega)
  have hMS_fr : ∀ a < h, stMS.mem a = mem₀ a := fun a ha => by
    rw [hfrMS a (Or.inl (by omega)) (Or.inl (by omega))]; exact hfrL1 a ha
  obtain ⟨bdDD, hbdDD, oDD, stDD, cDD, hrunDD, hpostDD, hcDD⟩ :=
    dedup_meetsContract (w := w) (L := L') hpSort [oldSorted, m, uniqOld] stMS.mem stMS.pos ω
      (fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨oldSorted, uniqOld, by simp [hL'_len], hw16, by omega, by omega, Or.inl (by omega),
       hSorted, hAtMS, fun x hx => lt_trans (holdL_lt x (hPerm.subset hx)) (by omega)⟩
  rcases hpostDD with ⟨srcDD, dstDD, hargsDD, hrDD, hUniqPW, hUniqIff, hUniqAt, hfrDD⟩
  have hdstDD : dstDD = uniqOld := by injection hargsDD with _ h2; injection h2 with _ h3; injection h3 with h4; exact h4.symm
  subst hdstDD
  have huniq_eq : sortedDedup L' = uniqL :=
    sortedDedup_perm_eq_finset_sort hPerm hSorted fun x => List.mem_toFinset.symm
  rw [huniq_eq] at hrDD hUniqPW hUniqIff hUniqAt hfrDD
  have hUniq_nd : uniqL.Nodup := hUniqPW.imp fun hab => ne_of_lt hab
  have hUniq_mem_old : ∀ x, x ∈ uniqL ↔ x ∈ oldL := fun x => (hUniqIff x).trans hPerm.mem_iff
  have hnG_le : nG ≤ m := by
    rw [show nG = uniqL.length from rfl, ← List.toFinset_card_of_nodup hUniq_nd, ← holdL_len]
    have hsub : uniqL.toFinset ⊆ oldL.toFinset := fun x hx =>
      List.mem_toFinset.mpr ((hUniq_mem_old x).mp (List.mem_toFinset.mp hx))
    exact (Finset.card_le_card hsub).trans (List.toFinset_card_le oldL)
  have hUniq_lt : ∀ x ∈ uniqL, x < vCap := fun x hx => holdL_lt x ((hUniq_mem_old x).mp hx)
  set stDD' : State := ⟨stDD.mem, Function.update stMS'.regs 14 nG, stDD.pos⟩
  have hcallDD : Runs w p ω (.call 14 (bSort + sortIdxDedup) [.reg 6, .reg 3, .reg 8]) stMS' .normal stDD' _ :=
    runs_call_iff.mpr ⟨[oldSorted, m, uniqOld], bdDD, oDD, stDD, cDD,
      by simp [evalArgs, Expr.eval, stMS', hregsL1 6 (by omega), hregsL1 3 (by omega), hregsL1 8 (by omega),
               st8, st7, st6, st5, st4, stA],
      hbdDD, hrunDD, rfl, by simp [stDD', hrDD, nG], rfl⟩
  have hDD_oldAt : ListAt stDD.mem oldArr oldL := fun i hi => by
    rw [hfrDD (oldArr + i) (Or.inl (by omega))]; exact hMS_oldAt i hi
  have hDD_zr : ZeroFrom stDD.mem (uniqOld + nG) := fun a ha => by
    rw [hfrDD a (Or.inr ha)]; exact hMS_zr a (by omega)
  have hDD_fr : ∀ a < h, stDD.mem a = mem₀ a := fun a ha => by
    rw [hfrDD a (Or.inl (by omega))]; exact hMS_fr a ha
  -- Call `asmFirstBuildGroups_part1b_runs` for `a15..a18` + Loop 2 + Loop 3
  have hhr0 : stDD'.regs 0 = spPtr := by simp [stDD', stMS', hregsL1 0 (by omega), st8, st7, st6, st5, st4, stA, startState]
  have hhr2 : stDD'.regs 2 = h := by simp [stDD', stMS', hregsL1 2 (by omega), st8, st7, st6, st5, st4, stA, startState]
  have hhr3 : stDD'.regs 3 = m := by simp [stDD', stMS', hregsL1 3 (by omega), st8, st7, st6, st5, st4, stA]
  have hhr5 : stDD'.regs 5 = oldArr := by simp [stDD', stMS', hregsL1 5 (by omega), st8, st7, st6, st5]
  have hhr8 : stDD'.regs 8 = uniqOld := by simp [stDD', stMS', hregsL1 8 (by omega), st8]
  have hhr14 : stDD'.regs 14 = nG := by simp [stDD']
  obtain ⟨stL3, c1b, hrun1b, hr0_3, hr2_3, hr3_3, hr8_3, hr14_3, hr15_3, hr16_3, hr17_3, hr18_3,
      hUniq3, hgrpL3, hcntL3, hzrL3, hfrL3, hc1b⟩ :=
    asmFirstBuildGroups_part1b_runs hpSort hw16 hpairs_len holdL_len rfl hnG_le hSpace_un
      rfl (by omega) rfl rfl rfl rfl hUniqPW hUniq_mem_old hUniq_lt
      hhr0 hhr2 hhr3 hhr5 hhr8 hhr14 hDD_oldAt hUniqAt hDD_zr hDD_fr
  have hpart1 :=
    runs_seq_iff.mpr (Or.inr ⟨st4, _, _, ha4,
    runs_seq_iff.mpr (Or.inr ⟨st5, _, _, ha5,
    runs_seq_iff.mpr (Or.inr ⟨st6, _, _, ha6,
    runs_seq_iff.mpr (Or.inr ⟨st7, _, _, ha7,
    runs_seq_iff.mpr (Or.inr ⟨st8, _, _, ha8,
    runs_seq_iff.mpr (Or.inr ⟨stL1, _, _, hrunL1,
    runs_seq_iff.mpr (Or.inr ⟨stMS', _, _, hcallMS,
    runs_seq_iff.mpr (Or.inr ⟨stDD', _, _, hcallDD, hrun1b, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨stL3, _, hpart1, hUniqPW, hUniq_mem_old, hnG_le,
    hr0_3, hr2_3, hr3_3, hr8_3, hr14_3, hr15_3, hr16_3, hr17_3, hr18_3,
    hUniq3, hgrpL3, hcntL3, hzrL3, hfrL3, ?_⟩
  dsimp only [mergeSortContract, dedupContract] at hcMS hcDD
  rw [rangeCost_const_eq] at hcL1
  rw [holdL_len] at hcMS; rw [hL'_len] at hcDD
  simp only [argsSize, Expr.size] at hcL1 ⊢
  nlinarith

end

end MinCostFlow.SparseCore.Program
