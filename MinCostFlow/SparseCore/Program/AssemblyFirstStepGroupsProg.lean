module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGroupsDefs

import WordRAM.Tactic

/-!
# Verification of the split-groups builder (`AssemblyFirstStepGroupsProg`)

Completes the Word-RAM verification `asmFirstBuildGroups_runs` of `asmFirstBuildGroupsStmt bSort`
on `[spPtr, vCap, h]`, chaining `asmFirstBuildGroups_part1_runs` (`AssemblyFirstStepGroupsDefs.lean`)
with the group-header emission loop (Loop 4), the fresh-root scatter loop (Loop 5), and the 2-word
output epilogue `[gs.length, groupPtr]`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

private lemma runs_seq_split {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st₀ st₁ : State} {c : ℕ}
    (h : Runs w p ω (s₁ ;; s₂) st₀ .normal st₁ c) :
    ∃ stM c₁ c₂, Runs w p ω s₁ st₀ .normal stM c₁ ∧
      Runs w p ω s₂ stM .normal st₁ c₂ ∧ c = c₁ + c₂ + 1 := by
  rcases runs_seq_iff.mp h with hbad | ⟨stM, c₁, c₂, h1, h2, rfl⟩
  · simp at hbad
  · exact ⟨stM, c₁, c₂, h1, h2, rfl⟩

private lemma runs_part1_append {w bSort : ℕ} {p : Program} {ω : ℕ → Bool}
    {sTail : Stmt} {stA st3 stEnd : State} {o : Outcome} {c1 c2 : ℕ}
    (h1 : Runs w p ω (asmFirstBuildGroupsPart1Stmt bSort) stA .normal st3 c1)
    (h2 : Runs w p ω sTail st3 o stEnd c2) :
    ∃ c, Runs w p ω
      (.assign 4 (.bin .add (.reg 2) (.const 2)) ;;
       .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;
       .assign 6 (.bin .add (.reg 5) (.reg 3)) ;;
       .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
       .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
       forRange 9 (.const 0) (.reg 3)
         (.assign 10 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 4) (.reg 9)))) ;;
          .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9)))) ;;
          .assign 12 (.load (.bin .add (.reg 4) (.reg 10))) ;;
          .cond (.bin .eq (.reg 12) (.const 0)) (.assign 13 (.reg 10)) (.assign 13 (.bin .sub (.reg 12) (.const 1))) ;;
          .store (.bin .add (.reg 4) (.reg 11)) (.bin .add (.reg 13) (.const 1)) ;;
          .store (.bin .add (.reg 5) (.reg 9)) (.reg 13) ;;
          .store (.bin .add (.reg 6) (.reg 9)) (.reg 13)) ;;
       .call 14 (bSort + sortIdxMergeSort) [.reg 6, .reg 3, .reg 7] ;;
       .call 14 (bSort + sortIdxDedup) [.reg 6, .reg 3, .reg 8] ;;
       .assign 15 (.bin .add (.reg 8) (.reg 14)) ;;
       .assign 16 (.bin .add (.reg 15) (.reg 3)) ;;
       .assign 17 (.bin .add (.reg 16) (.reg 14)) ;;
       .assign 18 (.bin .add (.reg 17) (.reg 14)) ;;
       forRange 9 (.const 0) (.reg 14) (.store (.bin .add (.reg 16) (.reg 9)) (.const 1)) ;;
       forRange 9 (.const 0) (.reg 3)
         (.assign 11 (.load (.bin .add (.reg 5) (.reg 9))) ;;
          .call 10 (bSort + sortIdxBinSearch) [.reg 8, .reg 14, .reg 11] ;;
          .store (.bin .add (.reg 15) (.reg 9)) (.reg 10) ;;
          .assign 12 (.load (.bin .add (.reg 16) (.reg 10))) ;;
          .store (.bin .add (.reg 16) (.reg 10)) (.bin .add (.reg 12) (.const 1))) ;;
       sTail) stA o stEnd c ∧ c = c1 + c2 + 1 := by
  unfold asmFirstBuildGroupsPart1Stmt at h1
  obtain ⟨m1, a1, r1, ha1, hr1, e1⟩ := runs_seq_split h1
  obtain ⟨m2, a2, r2, ha2, hr2, e2⟩ := runs_seq_split hr1
  obtain ⟨m3, a3, r3, ha3, hr3, e3⟩ := runs_seq_split hr2
  obtain ⟨m4, a4, r4, ha4, hr4, e4⟩ := runs_seq_split hr3
  obtain ⟨m5, a5, r5, ha5, hr5, e5⟩ := runs_seq_split hr4
  obtain ⟨m6, a6, r6, ha6, hr6, e6⟩ := runs_seq_split hr5
  obtain ⟨m7, a7, r7, ha7, hr7, e7⟩ := runs_seq_split hr6
  obtain ⟨m8, a8, r8, ha8, hr8, e8⟩ := runs_seq_split hr7
  obtain ⟨m9, a9, r9, ha9, hr9, e9⟩ := runs_seq_split hr8
  obtain ⟨m10, a10, r10, ha10, hr10, e10⟩ := runs_seq_split hr9
  obtain ⟨m11, a11, r11, ha11, hr11, e11⟩ := runs_seq_split hr10
  obtain ⟨m12, a12, r12, ha12, hr12, e12⟩ := runs_seq_split hr11
  obtain ⟨m13, a13, a14, ha13, ha14, e13⟩ := runs_seq_split hr12
  refine ⟨_,
    runs_seq_iff.mpr (Or.inr ⟨m1, _, _, ha1,
    runs_seq_iff.mpr (Or.inr ⟨m2, _, _, ha2,
    runs_seq_iff.mpr (Or.inr ⟨m3, _, _, ha3,
    runs_seq_iff.mpr (Or.inr ⟨m4, _, _, ha4,
    runs_seq_iff.mpr (Or.inr ⟨m5, _, _, ha5,
    runs_seq_iff.mpr (Or.inr ⟨m6, _, _, ha6,
    runs_seq_iff.mpr (Or.inr ⟨m7, _, _, ha7,
    runs_seq_iff.mpr (Or.inr ⟨m8, _, _, ha8,
    runs_seq_iff.mpr (Or.inr ⟨m9, _, _, ha9,
    runs_seq_iff.mpr (Or.inr ⟨m10, _, _, ha10,
    runs_seq_iff.mpr (Or.inr ⟨m11, _, _, ha11,
    runs_seq_iff.mpr (Or.inr ⟨m12, _, _, ha12,
    runs_seq_iff.mpr (Or.inr ⟨m13, _, _, ha13,
    runs_seq_iff.mpr (Or.inr ⟨st3, _, _, ha14, h2, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩

private lemma runs_groups_else_stitch {w bSort hEnd cP1 cL4 cL5 : ℕ}
    {p : Program} {ω : ℕ → Bool} {st0 stA stL3 stL4 stL5 stM1 stEnd : State}
    (ha3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal stA 3)
    (hcondF : (Expr.bin .eq (.reg 3) (.const 0)).eval w stA = some 0)
    (hrunP1 : Runs w p ω (asmFirstBuildGroupsPart1Stmt bSort) stA .normal stL3 cP1)
    (hrunL4 : Runs w p ω
      (.assign 19 (.const 0) ;;
       forRange 9 (.const 0) (.reg 14)
         (.assign 10 (.load (.bin .add (.reg 16) (.reg 9))) ;;
          .assign 11 (.load (.bin .add (.reg 8) (.reg 9))) ;;
          .store (.bin .add (.reg 18) (.reg 19)) (.reg 10) ;;
          .store (.bin .add (.reg 18) (.bin .add (.reg 19) (.const 1))) (.reg 11) ;;
          .store (.bin .add (.reg 17) (.reg 9)) (.bin .add (.reg 19) (.const 2)) ;;
          .assign 19 (.bin .add (.bin .add (.reg 19) (.const 1)) (.reg 10))))
      stL3 .normal stL4 cL4)
    (hrunL5 : Runs w p ω
      (forRange 9 (.const 0) (.reg 3)
        (.assign 10 (.load (.bin .add (.reg 15) (.reg 9))) ;;
         .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9)))) ;;
         .assign 12 (.load (.bin .add (.reg 17) (.reg 10))) ;;
         .store (.bin .add (.reg 18) (.reg 12)) (.reg 11) ;;
         .store (.bin .add (.reg 17) (.reg 10)) (.bin .add (.reg 12) (.const 1))))
      stL4 .normal stL5 cL5)
    (hsOut1 : Runs w p ω (.store (.reg 2) (.reg 14)) stL5 .normal stM1 3)
    (hsOut2 : Runs w p ω (.store (.bin .add (.reg 2) (.const 1)) (.reg 18)) stM1 .normal stEnd 5)
    (hret : Runs w p ω (.ret (.bin .add (.reg 18) (.reg 19))) stEnd (.returned hEnd) stEnd 4) :
    ∃ c, Runs w p ω (asmFirstBuildGroupsStmt bSort) st0 (.returned hEnd) stEnd c ∧
      c ≤ cP1 + cL4 + cL5 + 40 := by
  obtain ⟨st19, c19, cL4', h19, hL4', hc4⟩ := runs_seq_split hrunL4
  have htail :=
    runs_seq_iff.mpr (Or.inr ⟨st19, _, _, h19,
    runs_seq_iff.mpr (Or.inr ⟨stL4, _, _, hL4',
    runs_seq_iff.mpr (Or.inr ⟨stL5, _, _, hrunL5,
    runs_seq_iff.mpr (Or.inr ⟨stM1, _, _, hsOut1,
    runs_seq_iff.mpr (Or.inr ⟨stEnd, _, _, hsOut2, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  obtain ⟨cElse, helse, hcElse⟩ := runs_part1_append hrunP1 htail
  refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨stA, _, _, ha3,
    runs_cond_iff.mpr ⟨0, cElse, hcondF, by simp only [↓reduceIte]; exact helse, rfl⟩, rfl⟩), ?_⟩
  simp only [Expr.size]
  omega

private lemma groupsWords_take_succ {gs : List (List ℕ)} {k : ℕ} (hk : k < gs.length) :
    groupsWords (gs.take (k + 1)) = groupsWords (gs.take k) + 1 + (gs[k]'hk).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  unfold groupsWords
  rw [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
  omega

private lemma groupsWords_take_mono {gs : List (List ℕ)} {a b : ℕ} (hab : a ≤ b) :
    groupsWords (gs.take a) ≤ groupsWords (gs.take b) := by
  have h1 : gs.take b = gs.take a ++ (gs.take b).drop a := by
    simpa [List.take_take, Nat.min_eq_left hab] using (List.take_append_drop a (gs.take b)).symm
  conv_rhs => rw [h1]
  unfold groupsWords
  rw [List.map_append, List.sum_append]
  omega

private lemma groupsWords_take_le {gs : List (List ℕ)} (k : ℕ) :
    groupsWords (gs.take k) ≤ groupsWords gs := by
  have h1 : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_rhs => rw [h1]
  unfold groupsWords
  rw [List.map_append, List.sum_append]
  omega

private lemma groupMembers_take_le {pairs : List (ℕ × ℕ)} {oldL : List ℕ} {r i : ℕ}
    (hi : i ≤ pairs.length) :
    (groupMembers (pairs.take i) oldL r).length ≤ (groupMembers pairs oldL r).length := by
  unfold groupMembers
  rw [List.length_map, List.length_map, List.length_take, Nat.min_eq_left hi]
  have h3 : List.range pairs.length = List.range i ++ List.range' i (pairs.length - i) := by
    refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
    by_cases hki : k < i
    · rw [List.getElem_append_left (by simp; exact hki)]; simp
    · rw [List.getElem_append_right (by simp; omega)]; simp; omega
  rw [h3, List.filter_append, List.length_append]
  omega

private theorem asmFirstBuildGroups_loop4_runs {w nG uniqOld cntBase curBase groupPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {uniqL : List ℕ} {gs : List (List ℕ)} {stL3 : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hnG_def : nG = uniqL.length) (hgs_len : gs.length = nG)
    (huniq_lt : uniqOld + nG ≤ cntBase) (hcnt_le : cntBase + nG ≤ curBase)
    (hcur_le : curBase + nG = groupPtr)
    (hSpace : groupPtr + groupsWords gs < 2 ^ w)
    (hgs_pos : ∀ k (hk : k < nG), 0 < (gs[k]'(by omega)).length)
    (hr8_3 : stL3.regs 8 = uniqOld) (hr14_3 : stL3.regs 14 = nG)
    (hr16_3 : stL3.regs 16 = cntBase) (hr17_3 : stL3.regs 17 = curBase)
    (hr18_3 : stL3.regs 18 = groupPtr)
    (hUniqAt : ListAt stL3.mem uniqOld uniqL)
    (hcnt_at : ∀ k (hk : k < nG), stL3.mem (cntBase + k) = (gs[k]'(by omega)).length) :
    ∃ stL4 cL4,
      Runs w p ω
        (.assign 19 (.const 0) ;;
         forRange 9 (.const 0) (.reg 14)
           (.assign 10 (.load (.bin .add (.reg 16) (.reg 9))) ;;
            .assign 11 (.load (.bin .add (.reg 8) (.reg 9))) ;;
            .store (.bin .add (.reg 18) (.reg 19)) (.reg 10) ;;
            .store (.bin .add (.reg 18) (.bin .add (.reg 19) (.const 1))) (.reg 11) ;;
            .store (.bin .add (.reg 17) (.reg 9)) (.bin .add (.reg 19) (.const 2)) ;;
            .assign 19 (.bin .add (.bin .add (.reg 19) (.const 1)) (.reg 10))))
        stL3 .normal stL4 cL4 ∧
      (∀ r ≤ 18, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → stL4.regs r = stL3.regs r) ∧
      stL4.regs 19 = groupsWords gs ∧
      (∀ k (hk : k < nG),
        stL4.mem (groupPtr + groupsWords (gs.take k)) = (gs[k]'(by omega)).length ∧
        stL4.mem (groupPtr + groupsWords (gs.take k) + 1) = uniqL[k]'(by omega) ∧
        stL4.mem (curBase + k) = groupsWords (gs.take k) + 2) ∧
      (∀ a, a < curBase ∨ groupPtr + groupsWords gs ≤ a → stL4.mem a = stL3.mem a) ∧
      cL4 ≤ 70 * nG + 20 := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  set st19 : State := { stL3 with regs := Function.update stL3.regs 19 0 }
  have ha19 : Runs w p ω (.assign 19 (.const 0)) stL3 .normal st19 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  let Inv4 : ℕ → Unit → State → Prop := fun gi _ st =>
    (∀ r ≤ 18, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → st.regs r = stL3.regs r) ∧
    st.regs 9 = gi ∧
    st.regs 19 = groupsWords (gs.take gi) ∧
    (∀ k (hk : k < gi) (hkn : k < nG),
      st.mem (groupPtr + groupsWords (gs.take k)) = (gs[k]'(by omega)).length ∧
      st.mem (groupPtr + groupsWords (gs.take k) + 1) = uniqL[k]'(by omega) ∧
      st.mem (curBase + k) = groupsWords (gs.take k) + 2) ∧
    (∀ a, a < curBase ∨ groupPtr + groupsWords (gs.take gi) ≤ a → st.mem a = stL3.mem a)
  have hInv4_0 : Inv4 0 () { st19 with regs := Function.update st19.regs 9 0 } :=
    ⟨fun r hr h9 _ _ _ => (Function.update_of_ne h9 _ _).trans (Function.update_of_ne (by omega : r ≠ 19) _ _),
     by simp [Function.update], by simp [st19, groupsWords],
     fun _ h _ => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  obtain ⟨stL4, cL4, _, hrunL4, ⟨hregsL4, _, hr19L4, hhdrL4, hfrL4⟩, hcL4⟩ :=
    forRange_amort (ω := ω) (a₀ := ()) Inv4 (fun _ _ => 0) (fun _ => 55) nG h1w (by omega) hInv4_0
      (fun _ _ _ _ ⟨_, hr9, _⟩ => hr9)
      (fun _ _ _ _ ⟨hregs, _⟩ => Expr.eval_reg_of_eq ((hregs 14 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr14_3))
      (fun gi _ st hgi ⟨hregs, hr9, hr19, hhdr, hfr⟩ => by
        have hr8 : st.regs 8 = uniqOld := (hregs 8 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr8_3
        have hr16 : st.regs 16 = cntBase := (hregs 16 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr16_3
        have hr17 : st.regs 17 = curBase := (hregs 17 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr17_3
        have hr18 : st.regs 18 = groupPtr := (hregs 18 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr18_3
        set off := groupsWords (gs.take gi)
        set cVal := (gs[gi]'(by omega)).length
        set uVal := uniqL[gi]'(by omega)
        have hgw_next : groupsWords (gs.take (gi + 1)) = off + 1 + cVal :=
          groupsWords_take_succ (by omega)
        have hgw_le : groupsWords (gs.take (gi + 1)) ≤ groupsWords gs :=
          groupsWords_take_le (gi + 1)
        have hc_pos : 0 < cVal := hgs_pos gi hgi
        have hc_mem : st.mem (cntBase + gi) = cVal := by
          rw [hfr _ (Or.inl (by omega))]; exact hcnt_at gi hgi
        have hu_mem : st.mem (uniqOld + gi) = uVal := by
          rw [hfr _ (Or.inl (by omega))]; exact hUniqAt gi (by omega)
        set t10 : State := { st with regs := Function.update st.regs 10 cVal }
        set t11 : State := { t10 with regs := Function.update t10.regs 11 uVal }
        set m1 := Function.update st.mem (groupPtr + off) cVal
        set m2 := Function.update m1 (groupPtr + (off + 1)) uVal
        set m3 := Function.update m2 (curBase + gi) (off + 2)
        set tF : State := ⟨m3, Function.update t11.regs 19 (off + 1 + cVal), st.pos⟩
        have e10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 16) (.reg 9)))) st .normal t10 5 :=
          runs_assign_iff.mpr ⟨cVal, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr16) (Expr.eval_reg_of_eq hr9) (by omega)) hc_mem, rfl, rfl, rfl⟩
        have e11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 8) (.reg 9)))) t10 .normal t11 5 :=
          runs_assign_iff.mpr ⟨uVal, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [t10, hr8]))
            (Expr.eval_reg_of_eq (by simp [t10, hr9])) (by omega)) hu_mem, rfl, rfl, rfl⟩
        have es1 : Runs w p ω (.store (.bin .add (.reg 18) (.reg 19)) (.reg 10)) t11 .normal ⟨m1, t11.regs, st.pos⟩ 5 :=
          runs_store_iff.mpr ⟨groupPtr + off, cVal, Expr.eval_add (Expr.eval_reg_of_eq (by simp [t11, t10, hr18]))
            (Expr.eval_reg_of_eq (by simp [t11, t10, hr19])) (by omega), Expr.eval_reg_of_eq (by simp [t11, t10]), rfl, rfl, rfl⟩
        have es2 : Runs w p ω (.store (.bin .add (.reg 18) (.bin .add (.reg 19) (.const 1))) (.reg 11))
            ⟨m1, t11.regs, st.pos⟩ .normal ⟨m2, t11.regs, st.pos⟩ 7 :=
          runs_store_iff.mpr ⟨groupPtr + (off + 1), uVal, Expr.eval_add (Expr.eval_reg_of_eq (by simp [t11, t10, hr18]))
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [t11, t10, hr19])) (Expr.eval_const h1w) (by omega)) (by omega),
            Expr.eval_reg_of_eq (by simp [t11]), rfl, rfl, rfl⟩
        have es3 : Runs w p ω (.store (.bin .add (.reg 17) (.reg 9)) (.bin .add (.reg 19) (.const 2)))
            ⟨m2, t11.regs, st.pos⟩ .normal ⟨m3, t11.regs, st.pos⟩ 7 :=
          runs_store_iff.mpr ⟨curBase + gi, off + 2, Expr.eval_add (Expr.eval_reg_of_eq (by simp [t11, t10, hr17]))
            (Expr.eval_reg_of_eq (by simp [t11, t10, hr9])) (by omega),
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [t11, t10, hr19])) (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
        have e19 : Runs w p ω (.assign 19 (.bin .add (.bin .add (.reg 19) (.const 1)) (.reg 10)))
            ⟨m3, t11.regs, st.pos⟩ .normal tF 6 :=
          runs_assign_iff.mpr ⟨off + 1 + cVal, Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [t11, t10, hr19]))
            (Expr.eval_const h1w) (by omega)) (Expr.eval_reg_of_eq (by simp [t11, t10])) (by omega), rfl, rfl, rfl⟩
        have hrun := runs_seq_iff.mpr (Or.inr ⟨t10, _, _, e10,
          runs_seq_iff.mpr (Or.inr ⟨t11, _, _, e11,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es2,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es3, e19, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        refine ⟨tF, _, (), hrun, by simp [tF, t11, t10, hr9], ?_, rfl, by omega⟩
        refine ⟨fun r hr h9 h10 h11 h12 => by
            simp [tF, t11, t10, Function.update_of_ne h9, Function.update_of_ne (by omega : r ≠ 19),
              Function.update_of_ne h11, Function.update_of_ne h10, hregs r hr h9 h10 h11 h12],
          by simp [Function.update], by simp [tF, hgw_next],
          fun k hk hkn => by
            by_cases hlt : k < gi
            · have hpos_k : 0 < (gs[k]'(by omega)).length := hgs_pos k hkn
              have hgw_k1 := groupsWords_take_succ (gs := gs) (k := k) (by omega)
              have hgw_mono : groupsWords (gs.take (k + 1)) ≤ off := groupsWords_take_mono (by omega)
              obtain ⟨h1, h2, h3⟩ := hhdr k hlt hkn
              have hne1 : groupPtr + groupsWords (gs.take k) ≠ curBase + gi := by clear * - hcur_le hgi; omega
              have hne2 : groupPtr + groupsWords (gs.take k) ≠ groupPtr + (off + 1) := by clear * - hpos_k hgw_k1 hgw_mono; omega
              have hne3 : groupPtr + groupsWords (gs.take k) ≠ groupPtr + off := by clear * - hpos_k hgw_k1 hgw_mono; omega
              have hne4 : groupPtr + groupsWords (gs.take k) + 1 ≠ curBase + gi := by clear * - hcur_le hgi; omega
              have hne5 : groupPtr + groupsWords (gs.take k) + 1 ≠ groupPtr + (off + 1) := by clear * - hpos_k hgw_k1 hgw_mono; omega
              have hne6 : groupPtr + groupsWords (gs.take k) + 1 ≠ groupPtr + off := by clear * - hpos_k hgw_k1 hgw_mono; omega
              have hne7 : curBase + k ≠ curBase + gi := by clear * - hlt; omega
              have hne8 : curBase + k ≠ groupPtr + (off + 1) := by clear * - hcur_le hkn; omega
              have hne9 : curBase + k ≠ groupPtr + off := by clear * - hcur_le hkn; omega
              exact ⟨by change m3 _ = _; dsimp only [m3, m2, m1]; rw [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3]; exact h1,
                by change m3 _ = _; dsimp only [m3, m2, m1]; rw [Function.update_of_ne hne4, Function.update_of_ne hne5, Function.update_of_ne hne6]; exact h2,
                by change m3 _ = _; dsimp only [m3, m2, m1]; rw [Function.update_of_ne hne7, Function.update_of_ne hne8, Function.update_of_ne hne9]; exact h3⟩
            · have heq : k = gi := by omega
              subst heq
              exact ⟨by change m3 _ = _; dsimp only [m3, m2, m1]; rw [Function.update_of_ne (by clear * - hcur_le hgi; omega), Function.update_of_ne (by omega), Function.update_self],
                by change m3 _ = _; dsimp only [m3, m2, m1]; rw [Function.update_of_ne (by clear * - hcur_le hgi; omega), show groupPtr + off + 1 = groupPtr + (off + 1) by omega, Function.update_self],
                by change m3 _ = _; dsimp only [m3, m2, m1]; rw [Function.update_self]⟩,
          fun a ha => by
            change m3 a = stL3.mem a; dsimp only [m3, m2, m1]
            have h1 : a ≠ curBase + gi := by clear * - ha hcur_le hgi; rcases ha with h | h <;> omega
            have h2 : a ≠ groupPtr + (off + 1) := by clear * - ha hcur_le hgw_next hc_pos; rcases ha with h | h <;> omega
            have h3 : a ≠ groupPtr + off := by clear * - ha hcur_le hgw_next hc_pos; rcases ha with h | h <;> omega
            rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
            exact hfr a (by clear * - ha hgw_next; rcases ha with h | h; exact Or.inl h; exact Or.inr (by omega))⟩)
  have htake_all : gs.take nG = gs := by rw [← hgs_len, List.take_length]
  refine ⟨stL4, _, runs_seq_iff.mpr (Or.inr ⟨st19, _, _, ha19, hrunL4, rfl⟩),
    hregsL4, by rw [hr19L4, htake_all], fun k hk => hhdrL4 k hk hk,
    fun a ha => hfrL4 a (by rw [htake_all]; exact ha), ?_⟩
  rw [rangeCost_const_eq] at hcL4
  simp only [Expr.size] at hcL4
  omega

private theorem asmFirstBuildGroups_loop5_runs {w spPtr m nG grpOf curBase groupPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {L : List CompSplitEntry} {oldL uniqL : List ℕ}
    {gs : List (List ℕ)} {stL4 : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hm_def : L.length = m) (holdL_len : oldL.length = m)
    (hnG_def : nG = uniqL.length) (hgs_len : gs.length = nG)
    (hSp_lt : spPtr + (1 + 4 * m) ≤ curBase) (hgrpOf_le : grpOf + m ≤ curBase)
    (hcur_le : curBase + nG = groupPtr)
    (hSpace : groupPtr + groupsWords gs < 2 ^ w)
    (hUniq_nd : uniqL.Nodup) (hUniq_mem_old : ∀ x, x ∈ uniqL ↔ x ∈ oldL)
    (hgs_get : ∀ gi (hgi : gi < nG),
      gs[gi]'(by omega) = uniqL[gi]'(by omega) :: groupMembers (L.map fun s => (s.kept, s.fresh)) oldL (uniqL[gi]'(by omega)))
    (hr0_4 : stL4.regs 0 = spPtr) (hr3_4 : stL4.regs 3 = m)
    (hr15_4 : stL4.regs 15 = grpOf) (hr17_4 : stL4.regs 17 = curBase)
    (hr18_4 : stL4.regs 18 = groupPtr)
    (hSp_fresh : ∀ i (hi : i < m), stL4.mem (spPtr + 4 + 4 * i) = (L[i]'(by omega)).fresh)
    (hgrp_at : ∀ i (_hi : i < m), stL4.mem (grpOf + i) = uniqL.idxOf (oldL.getD i 0))
    (hhdrL4 : ∀ gi (hgi : gi < nG),
      stL4.mem (groupPtr + groupsWords (gs.take gi)) = (gs[gi]'(by omega)).length ∧
      stL4.mem (groupPtr + groupsWords (gs.take gi) + 1) = uniqL[gi]'(by omega) ∧
      stL4.mem (curBase + gi) = groupsWords (gs.take gi) + 2) :
    let pairs := L.map fun s => (s.kept, s.fresh)
    ∃ stL5 cL5,
      Runs w p ω
        (forRange 9 (.const 0) (.reg 3)
          (.assign 10 (.load (.bin .add (.reg 15) (.reg 9))) ;;
           .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9)))) ;;
           .assign 12 (.load (.bin .add (.reg 17) (.reg 10))) ;;
           .store (.bin .add (.reg 18) (.reg 12)) (.reg 11) ;;
           .store (.bin .add (.reg 17) (.reg 10)) (.bin .add (.reg 12) (.const 1))))
        stL4 .normal stL5 cL5 ∧
      (∀ r ≤ 19, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → stL5.regs r = stL4.regs r) ∧
      (∀ gi (hgi : gi < nG),
        stL5.mem (groupPtr + groupsWords (gs.take gi)) = (gs[gi]'(by omega)).length ∧
        stL5.mem (groupPtr + groupsWords (gs.take gi) + 1) = uniqL[gi]'(by omega) ∧
        (∀ t (ht : t < (groupMembers pairs oldL (uniqL[gi]'(by omega))).length),
          stL5.mem (groupPtr + groupsWords (gs.take gi) + 2 + t) =
            (groupMembers pairs oldL (uniqL[gi]'(by omega)))[t]'ht)) ∧
      (∀ a, a < curBase ∨ groupPtr + groupsWords gs ≤ a → stL5.mem a = stL4.mem a) ∧
      cL5 ≤ 65 * m + 20 := by
  intro pairs
  have hpairs_len : pairs.length = m := by simp [pairs, hm_def]
  have h1w : 1 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  let Inv5 : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r ≤ 19, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → st.regs r = stL4.regs r) ∧
    st.regs 9 = i ∧
    (∀ gi (hgi : gi < nG),
      st.mem (groupPtr + groupsWords (gs.take gi)) = (gs[gi]'(by omega)).length ∧
      st.mem (groupPtr + groupsWords (gs.take gi) + 1) = uniqL[gi]'(by omega) ∧
      st.mem (curBase + gi) = groupsWords (gs.take gi) + 2 + (groupMembers (pairs.take i) oldL (uniqL[gi]'(by omega))).length ∧
      (∀ t (ht : t < (groupMembers (pairs.take i) oldL (uniqL[gi]'(by omega))).length),
        st.mem (groupPtr + groupsWords (gs.take gi) + 2 + t) =
          (groupMembers (pairs.take i) oldL (uniqL[gi]'(by omega)))[t]'ht)) ∧
    (∀ a, a < curBase ∨ groupPtr + groupsWords gs ≤ a → st.mem a = stL4.mem a)
  have hInv5_0 : Inv5 0 () { stL4 with regs := Function.update stL4.regs 9 0 } :=
    ⟨fun r _ h9 _ _ _ => Function.update_of_ne h9 _ _, by simp [Function.update],
     fun gi hgi => by
       obtain ⟨h1, h2, h3⟩ := hhdrL4 gi hgi
       exact ⟨h1, h2, by simpa [groupMembers] using h3, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
     fun _ _ => rfl⟩
  obtain ⟨stL5, cL5, _, hrunL5, ⟨hregsL5, _, hgrpL5, hfrL5⟩, hcL5⟩ :=
    forRange_amort (ω := ω) (a₀ := ()) Inv5 (fun _ _ => 0) (fun _ => 50) m h1w (by omega) hInv5_0
      (fun _ _ _ _ ⟨_, hr9, _⟩ => hr9)
      (fun _ _ _ _ ⟨hregs, _⟩ => Expr.eval_reg_of_eq ((hregs 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr3_4))
      (fun i _ st hi ⟨hregs, hr9, hgrp, hfr⟩ => by
        have hr0 : st.regs 0 = spPtr := (hregs 0 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr0_4
        have hr15 : st.regs 15 = grpOf := (hregs 15 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr15_4
        have hr17 : st.regs 17 = curBase := (hregs 17 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr17_4
        have hr18 : st.regs 18 = groupPtr := (hregs 18 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr18_4
        set key := oldL.getD i 0
        have hkey_in : key ∈ uniqL := (hUniq_mem_old key).mpr (by
          rw [show key = oldL[i]'(by omega) from List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
        set gi := uniqL.idxOf key
        have hgi_lt : gi < nG := by rw [hnG_def]; exact List.idxOf_lt_length_iff.mpr hkey_in
        have hgi_val : uniqL[gi]'(by omega) = key := List.getElem_idxOf (by omega)
        have hgi_mem : st.mem (grpOf + i) = gi := by rw [hfr _ (Or.inl (by omega))]; exact hgrp_at i hi
        set fresh := (L[i]'(by omega)).fresh
        have hf_mem : st.mem (spPtr + 4 + 4 * i) = fresh := by
          rw [hfr _ (Or.inl (by omega))]; exact hSp_fresh i hi
        set off := groupsWords (gs.take gi)
        set sub := groupMembers (pairs.take i) oldL (uniqL[gi]'(by omega))
        have hsub_lt : sub.length < (groupMembers pairs oldL (uniqL[gi]'(by omega))).length := by
          have h1 : (groupMembers (pairs.take (i + 1)) oldL (uniqL[gi]'(by omega))).length = sub.length + 1 := by
            rw [groupMembers_take_succ pairs oldL _ (by omega), List.length_append]
            simp [hgi_val, key, sub]
          have h2 := groupMembers_take_le (pairs := pairs) (oldL := oldL) (r := uniqL[gi]'(by omega)) (i := i + 1) (by omega)
          omega
        have hgi_len_eq : (gs[gi]'(by omega)).length = 1 + (groupMembers pairs oldL (uniqL[gi]'(by omega))).length := by
          rw [hgs_get gi hgi_lt]; simp only [List.length_cons]; dsimp only [pairs]; omega
        have hgw_gi1 : groupsWords (gs.take (gi + 1)) = off + 1 + (gs[gi]'(by omega)).length :=
          groupsWords_take_succ (by omega)
        have hgw_gi1_le : groupsWords (gs.take (gi + 1)) ≤ groupsWords gs := groupsWords_take_le (gi + 1)
        have hpos_lt : off + 2 + sub.length < groupsWords gs := by
          clear * - hsub_lt hgi_len_eq hgw_gi1 hgw_gi1_le; omega
        have hcur_mem : st.mem (curBase + gi) = off + 2 + sub.length := (hgrp gi hgi_lt).2.2.1
        set u10 : State := { st with regs := Function.update st.regs 10 gi }
        set u11 : State := { u10 with regs := Function.update u10.regs 11 fresh }
        set u12 : State := { u11 with regs := Function.update u11.regs 12 (off + 2 + sub.length) }
        set m1 := Function.update st.mem (groupPtr + (off + 2 + sub.length)) fresh
        set m2 := Function.update m1 (curBase + gi) (off + 2 + sub.length + 1)
        set uF : State := ⟨m2, u12.regs, st.pos⟩
        have e10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 15) (.reg 9)))) st .normal u10 5 :=
          runs_assign_iff.mpr ⟨gi, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr15) (Expr.eval_reg_of_eq hr9) (by omega)) hgi_mem, rfl, rfl, rfl⟩
        have e11 : Runs w p ω (.assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9))))) u10 .normal u11 9 :=
          runs_assign_iff.mpr ⟨fresh, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [u10, hr0]))
            (Expr.eval_const h4w) (by omega)) (Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq (by simp [u10, hr9])) (by omega)) (by omega)) hf_mem, rfl, rfl, rfl⟩
        have e12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 17) (.reg 10)))) u11 .normal u12 5 :=
          runs_assign_iff.mpr ⟨off + 2 + sub.length, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [u11, u10, hr17]))
            (Expr.eval_reg_of_eq (by simp [u11, u10])) (by omega)) hcur_mem, rfl, rfl, rfl⟩
        have es1 : Runs w p ω (.store (.bin .add (.reg 18) (.reg 12)) (.reg 11)) u12 .normal ⟨m1, u12.regs, st.pos⟩ 5 :=
          runs_store_iff.mpr ⟨groupPtr + (off + 2 + sub.length), fresh, Expr.eval_add (Expr.eval_reg_of_eq (by simp [u12, u11, u10, hr18]))
            (Expr.eval_reg_of_eq (by simp [u12])) (by omega), Expr.eval_reg_of_eq (by simp [u12, u11]), rfl, rfl, rfl⟩
        have es2 : Runs w p ω (.store (.bin .add (.reg 17) (.reg 10)) (.bin .add (.reg 12) (.const 1)))
            ⟨m1, u12.regs, st.pos⟩ .normal uF 7 :=
          runs_store_iff.mpr ⟨curBase + gi, off + 2 + sub.length + 1,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [u12, u11, u10, hr17])) (Expr.eval_reg_of_eq (by simp [u12, u11, u10])) (by omega),
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [u12])) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
        have hrun := runs_seq_iff.mpr (Or.inr ⟨u10, _, _, e10,
          runs_seq_iff.mpr (Or.inr ⟨u11, _, _, e11,
          runs_seq_iff.mpr (Or.inr ⟨u12, _, _, e12,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, es1, es2, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have hgi_range : ∀ gj (hgj : gj < nG), gj ≠ gi →
            groupsWords (gs.take gj) + 1 + (gs[gj]'(by omega)).length ≤ off ∨
            off + 2 + sub.length < groupsWords (gs.take gj) := fun gj hgj hne => by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have h1 := groupsWords_take_succ (gs := gs) (k := gj) (by omega)
            have h2 := groupsWords_take_mono (gs := gs) (a := gj + 1) (b := gi) (by omega)
            left; clear * - h1 h2; omega
          · have h2 := groupsWords_take_mono (gs := gs) (a := gi + 1) (b := gj) (by omega)
            right; clear * - hsub_lt hgi_len_eq hgw_gi1 h2; omega
        refine ⟨uF, _, (), hrun, by simp [uF, u12, u11, u10, hr9], ?_, rfl, by omega⟩
        refine ⟨fun r hr h9 h10 h11 h12 => by
            simp [uF, u12, u11, u10, Function.update_of_ne h9, Function.update_of_ne h12,
              Function.update_of_ne h11, Function.update_of_ne h10, hregs r hr h9 h10 h11 h12],
          by simp [Function.update],
          fun gj hgj => by
            obtain ⟨h1, h2, h3, h4⟩ := hgrp gj hgj
            by_cases hEq : gj = gi
            · subst hEq
              have hsub_next : groupMembers (pairs.take (i + 1)) oldL (uniqL[gi]'(by omega)) = sub ++ [fresh] := by
                rw [groupMembers_take_succ pairs oldL _ (by omega)]
                have hp_i : (pairs[i]'(by omega)).2 = fresh := by simp [pairs, fresh]
                simp [hgi_val, key, sub, hp_i]
              refine ⟨by change m2 _ = _; dsimp only [m2, m1]; rw [Function.update_of_ne (by clear * - hcur_le hgi_lt; omega), Function.update_of_ne (by omega)]; exact h1,
                by change m2 _ = _; dsimp only [m2, m1]; rw [Function.update_of_ne (by clear * - hcur_le hgi_lt; omega), Function.update_of_ne (by omega)]; exact h2,
                by change m2 _ = _; dsimp only [m2, m1]; rw [Function.update_self, hsub_next, List.length_append]; simp; omega,
                fun t ht => by
                  change m2 _ = _; dsimp only [m2, m1]
                  rw [Function.update_of_ne (by clear * - hcur_le hgi_lt; omega)]
                  have hget : (groupMembers (pairs.take (i + 1)) oldL (uniqL[gi]'(by omega)))[t]'ht =
                      (sub ++ [fresh])[t]'(by rw [← hsub_next]; exact ht) := by
                    simp [hsub_next]
                  rw [hget]
                  by_cases ht_lt : t < sub.length
                  · rw [Function.update_of_ne (by omega), List.getElem_append_left ht_lt]; exact h4 t ht_lt
                  · have hteq : t = sub.length := by
                      have hlen : (groupMembers (pairs.take (i + 1)) oldL (uniqL[gi]'(by omega))).length = sub.length + 1 := by
                        rw [hsub_next, List.length_append]; simp
                      omega
                    subst hteq
                    rw [show groupPtr + off + 2 + sub.length = groupPtr + (off + 2 + sub.length) by omega,
                      Function.update_self, List.getElem_append_right (le_refl _)]; simp⟩
            · have hne_v : key ≠ uniqL[gj]'(by omega) := fun h => hEq (by
                have hinj := List.nodup_iff_injective_getElem.mp hUniq_nd
                  (a₁ := ⟨gi, by omega⟩) (a₂ := ⟨gj, by omega⟩) (hgi_val.trans h)
                exact (Fin.ext_iff.mp hinj).symm)
              have hsub_same : groupMembers (pairs.take (i + 1)) oldL (uniqL[gj]'(by omega)) =
                  groupMembers (pairs.take i) oldL (uniqL[gj]'(by omega)) := by
                rw [groupMembers_take_succ pairs oldL _ (by omega),
                  ite_eq_right_iff.mpr fun h => absurd h hne_v, List.append_nil]
              have hdisj := hgi_range gj hgj hEq
              have hgm_le : (groupMembers (pairs.take i) oldL (uniqL[gj]'(by omega))).length + 1 ≤ (gs[gj]'(by omega)).length := by
                rw [hgs_get gj hgj]; simp only [List.length_cons]
                have hle_m := groupMembers_take_le (pairs := pairs) (oldL := oldL) (r := uniqL[gj]'(by omega)) (i := i) (by omega)
                change (groupMembers (pairs.take i) oldL (uniqL[gj]'(by omega))).length + 1 ≤
                  (groupMembers pairs oldL (uniqL[gj]'(by omega))).length + 1
                omega
              refine ⟨by change m2 _ = _; dsimp only [m2, m1]; rw [Function.update_of_ne (by clear * - hcur_le hgi_lt; omega), Function.update_of_ne (by clear * - hdisj hgm_le; rcases hdisj with h | h <;> omega)]; exact h1,
                by change m2 _ = _; dsimp only [m2, m1]; rw [Function.update_of_ne (by clear * - hcur_le hgi_lt; omega), Function.update_of_ne (by clear * - hdisj hgm_le; rcases hdisj with h | h <;> omega)]; exact h2,
                by change m2 _ = _; dsimp only [m2, m1]; rw [Function.update_of_ne (by clear * - hEq; omega), Function.update_of_ne (by clear * - hcur_le hgj; omega), hsub_same]; exact h3,
                fun t ht => by
                  change m2 _ = _; dsimp only [m2, m1]
                  have ht' : t < (groupMembers (pairs.take i) oldL (uniqL[gj]'(by omega))).length := by
                    rwa [← hsub_same]
                  have hget : (groupMembers (pairs.take (i + 1)) oldL (uniqL[gj]'(by omega)))[t]'ht =
                      (groupMembers (pairs.take i) oldL (uniqL[gj]'(by omega)))[t]'ht' := by
                    simp [hsub_same]
                  rw [hget, Function.update_of_ne (by clear * - hcur_le hgi_lt; omega),
                    Function.update_of_ne (by clear * - hdisj hgm_le ht'; rcases hdisj with h | h <;> omega)]
                  exact h4 t ht'⟩,
          fun a ha => by
            change m2 a = stL4.mem a; dsimp only [m2, m1]
            have hne1 : a ≠ curBase + gi := by clear * - ha hcur_le hgi_lt; rcases ha with h | h <;> omega
            have hne2 : a ≠ groupPtr + (off + 2 + sub.length) := by clear * - ha hcur_le hpos_lt; rcases ha with h | h <;> omega
            rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
            exact hfr a ha⟩)
  have htake_all : pairs.take m = pairs := by rw [← hpairs_len, List.take_length]
  refine ⟨stL5, cL5, hrunL5, hregsL5, fun gi hgi => ?_, hfrL5, ?_⟩
  · obtain ⟨h1, h2, _, h4⟩ := hgrpL5 gi hgi
    simp only [htake_all] at h4
    exact ⟨h1, h2, h4⟩
  · rw [rangeCost_const_eq] at hcL5
    simp only [Expr.size] at hcL5
    omega

set_option maxHeartbeats 600000 in
private theorem asmFirstBuildGroups_epilogue {w bSort spPtr vCap h m nG uniqOld grpOf cntBase curBase groupPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {L : List CompSplitEntry} {oldL uniqL : List ℕ}
    {gs : List (List ℕ)} {mem₀ : ℕ → ℕ} {st0 stA stL3 : State} {cP1 : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hm_def : L.length = m) (holdL_len : oldL.length = m)
    (hnG_def : nG = uniqL.length) (hnG_le : nG ≤ m) (hgs_len : gs.length = nG)
    (hSp : SplitEntriesAt mem₀ spPtr L) (hSp_lt : spPtr + (1 + 4 * m) ≤ h)
    (huniq_eq : uniqOld = h + 2 + vCap + 3 * m) (hgrpOf_eq : grpOf = uniqOld + nG)
    (hcnt_eq : cntBase = grpOf + m) (hcur_eq : curBase = cntBase + nG) (hgp_eq : groupPtr = curBase + nG)
    (hgs_words : groupsWords gs = 2 * nG + m)
    (hSpace : h + (2 + vCap + 10 * m) < 2 ^ w)
    (hUniq_nd : uniqL.Nodup) (hUniq_mem_old : ∀ x, x ∈ uniqL ↔ x ∈ oldL)
    (hgs_get : ∀ gi (hgi : gi < nG),
      gs[gi]'(by omega) = uniqL[gi]'(by omega) :: groupMembers (L.map fun s => (s.kept, s.fresh)) oldL (uniqL[gi]'(by omega)))
    (ha3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal stA 3)
    (hcondF : (Expr.bin .eq (.reg 3) (.const 0)).eval w stA = some 0)
    (hrunP1 : Runs w p ω (asmFirstBuildGroupsPart1Stmt bSort) stA .normal stL3 cP1)
    (hcP1 : cP1 ≤ 245 * m * (Nat.log 2 (m + 1) + 1) + 320 * m + 350)
    (hr0_3 : stL3.regs 0 = spPtr) (hr2_3 : stL3.regs 2 = h) (hr3_3 : stL3.regs 3 = m)
    (hr8_3 : stL3.regs 8 = uniqOld) (hr14_3 : stL3.regs 14 = nG)
    (hr15_3 : stL3.regs 15 = grpOf) (hr16_3 : stL3.regs 16 = cntBase)
    (hr17_3 : stL3.regs 17 = curBase) (hr18_3 : stL3.regs 18 = groupPtr)
    (hUniqAt : ListAt stL3.mem uniqOld uniqL)
    (hgrpL3 : ∀ i (_hi : i < m), stL3.mem (grpOf + i) = uniqL.idxOf (oldL.getD i 0))
    (hcntL3 : ∀ gi (hgi : gi < nG),
      stL3.mem (cntBase + gi) = 1 + (groupMembers (L.map fun s => (s.kept, s.fresh)) oldL (uniqL[gi]'(by omega))).length)
    (hzrL3 : ZeroFrom stL3.mem curBase)
    (hfrL3 : ∀ a < h, stL3.mem a = mem₀ a) :
    ∃ hEnd st' c,
      Runs w p ω (asmFirstBuildGroupsStmt bSort) st0 (.returned hEnd) st' c ∧
      st'.mem h = gs.length ∧
      st'.mem (h + 1) = groupPtr ∧
      readGroups st'.mem groupPtr gs.length = gs ∧
      h + 2 ≤ groupPtr ∧
      groupPtr + groupsWords gs = hEnd ∧
      hEnd ≤ h + buildGroupsSpace vCap m ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      c ≤ buildGroupsCost m := by
  have h1w : 1 < 2 ^ w := by omega
  have hgs_pos : ∀ k (hk : k < nG), 0 < (gs[k]'(by omega)).length := fun k hk => by
    rw [hgs_get k hk]; simp
  have hcnt_at : ∀ k (hk : k < nG), stL3.mem (cntBase + k) = (gs[k]'(by omega)).length := fun k hk => by
    rw [hcntL3 k hk, hgs_get k hk, List.length_cons]; omega
  obtain ⟨stL4, cL4, hrunL4, hregsL4, hr19L4, hhdrL4, hfrL4, hcL4⟩ :=
    asmFirstBuildGroups_loop4_runs (ω := ω) hw16 hnG_def hgs_len
      (by clear * - hgrpOf_eq hcnt_eq; omega) (by clear * - hcur_eq; omega) hgp_eq.symm
      (by clear * - huniq_eq hgrpOf_eq hcnt_eq hcur_eq hgp_eq hgs_words hnG_le hSpace; omega)
      hgs_pos hr8_3 hr14_3 hr16_3 hr17_3 hr18_3 hUniqAt hcnt_at
  have hr0_4 : stL4.regs 0 = spPtr := (hregsL4 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr0_3
  have hr2_4 : stL4.regs 2 = h := (hregsL4 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr2_3
  have hr3_4 : stL4.regs 3 = m := (hregsL4 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr3_3
  have hr14_4 : stL4.regs 14 = nG := (hregsL4 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr14_3
  have hr15_4 : stL4.regs 15 = grpOf := (hregsL4 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr15_3
  have hr17_4 : stL4.regs 17 = curBase := (hregsL4 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr17_3
  have hr18_4 : stL4.regs 18 = groupPtr := (hregsL4 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr18_3
  obtain ⟨stL5, cL5, hrunL5, hregsL5, hgrpL5, hfrL5, hcL5⟩ :=
    asmFirstBuildGroups_loop5_runs (ω := ω) hw16 hm_def holdL_len hnG_def hgs_len
      (by clear * - hSp_lt huniq_eq hgrpOf_eq hcnt_eq hcur_eq; omega)
      (by clear * - hcnt_eq hcur_eq; omega) hgp_eq.symm
      (by clear * - huniq_eq hgrpOf_eq hcnt_eq hcur_eq hgp_eq hgs_words hnG_le hSpace; omega)
      hUniq_nd hUniq_mem_old hgs_get hr0_4 hr3_4 hr15_4 hr17_4 hr18_4
      (fun i hi => by
        rw [hfrL4 _ (Or.inl (by clear * - hSp_lt hi huniq_eq hgrpOf_eq hcnt_eq hcur_eq; omega)),
          hfrL3 _ (by clear * - hSp_lt hi; omega),
          show spPtr + 4 + 4 * i = spPtr + 1 + 4 * i + 3 by omega]
        exact (hSp.2 i (by clear * - hm_def hi; omega)).2.2.2)
      (fun i hi => by rw [hfrL4 _ (Or.inl (by clear * - hi hcnt_eq hcur_eq; omega))]; exact hgrpL3 i hi)
      hhdrL4
  set hEnd := groupPtr + groupsWords gs
  set mEnd1 := Function.update stL5.mem h nG
  set mEnd := Function.update mEnd1 (h + 1) groupPtr
  set stEnd : State := ⟨mEnd, stL5.regs, stL5.pos⟩
  have hr2_5 : stL5.regs 2 = h := (hregsL5 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr2_4
  have hr14_5 : stL5.regs 14 = nG := (hregsL5 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr14_4
  have hr18_5 : stL5.regs 18 = groupPtr := (hregsL5 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr18_4
  have hr19_5 : stL5.regs 19 = groupsWords gs := (hregsL5 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr19L4
  have hsOut1 : Runs w p ω (.store (.reg 2) (.reg 14)) stL5 .normal ⟨mEnd1, stL5.regs, stL5.pos⟩ 3 :=
    runs_store_iff.mpr ⟨h, nG, Expr.eval_reg_of_eq hr2_5, Expr.eval_reg_of_eq hr14_5, rfl, rfl, rfl⟩
  have hsOut2 : Runs w p ω (.store (.bin .add (.reg 2) (.const 1)) (.reg 18))
      ⟨mEnd1, stL5.regs, stL5.pos⟩ .normal stEnd 5 :=
    runs_store_iff.mpr ⟨h + 1, groupPtr, Expr.eval_add (Expr.eval_reg_of_eq hr2_5) (Expr.eval_const h1w) (by clear * - hSpace; omega),
      Expr.eval_reg_of_eq hr18_5, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 18) (.reg 19))) stEnd (.returned hEnd) stEnd 4 :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_add (Expr.eval_reg_of_eq hr18_5) (Expr.eval_reg_of_eq hr19_5)
      (by clear * - huniq_eq hgrpOf_eq hcnt_eq hcur_eq hgp_eq hgs_words hnG_le hSpace; omega), rfl, rfl, rfl⟩
  obtain ⟨cAll, hfull, hcAll⟩ :=
    runs_groups_else_stitch ha3 hcondF hrunP1 hrunL4 hrunL5 hsOut1 hsOut2 hret
  clear hrunP1 hrunL4 hrunL5 hsOut1 hsOut2 hret ha3 hcondF
  have hgp_lo : h + 2 ≤ groupPtr := by clear * - huniq_eq hgrpOf_eq hcnt_eq hcur_eq hgp_eq; omega
  have hcb_lo : h ≤ curBase := by clear * - huniq_eq hgrpOf_eq hcnt_eq hcur_eq; omega
  have hcb_le_gp : curBase ≤ groupPtr := by clear * - hgp_eq; omega
  refine ⟨hEnd, stEnd, cAll, hfull,
    by change mEnd h = gs.length; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by clear * -; omega), Function.update_self, hgs_len],
    by change mEnd (h + 1) = groupPtr; dsimp only [mEnd]; exact Function.update_self _ _ _,
    ?_, hgp_lo, rfl, by unfold buildGroupsSpace; clear * - huniq_eq hgrpOf_eq hcnt_eq hcur_eq hgp_eq hgs_words hnG_le; omega,
    fun a ha => by
      change mEnd a = 0; dsimp only [mEnd, mEnd1]
      rw [Function.update_of_ne (by clear * - ha hgp_lo; omega), Function.update_of_ne (by clear * - ha hgp_lo; omega),
        hfrL5 a (Or.inr ha), hfrL4 a (Or.inr ha)]
      exact hzrL3 a (by clear * - ha hcb_le_gp; omega),
    fun a ha => by
      change mEnd a = mem₀ a; dsimp only [mEnd, mEnd1]
      rw [Function.update_of_ne (by clear * - ha; omega), Function.update_of_ne (by clear * - ha; omega),
        hfrL5 a (Or.inl (by clear * - ha hcb_lo; omega)), hfrL4 a (Or.inl (by clear * - ha hcb_lo; omega))]
      exact hfrL3 a ha, ?_⟩
  · refine readGroups_of_layout fun gi hgi => ?_
    have hgi' : gi < nG := by clear * - hgi hgs_len; omega
    obtain ⟨h1, h2, h4⟩ := hgrpL5 gi hgi'
    refine ⟨by change mEnd _ = _; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by clear * - hgp_lo; omega), Function.update_of_ne (by clear * - hgp_lo; omega)]; exact h1,
      fun j hj => by
        change mEnd _ = _; dsimp only [mEnd, mEnd1]
        rw [Function.update_of_ne (by clear * - hgp_lo; omega), Function.update_of_ne (by clear * - hgp_lo; omega)]
        cases j with
        | zero =>
          simp only [Nat.add_zero, h2]
          have hget := hgs_get gi hgi'
          simp [hget]
        | succ t =>
          have hget := hgs_get gi hgi'
          have ht : t < (groupMembers (L.map fun s => (s.kept, s.fresh)) oldL (uniqL[gi]'(by clear * - hgi' hnG_def; omega))).length := by
            simp only [hget, List.length_cons] at hj; omega
          rw [show groupPtr + groupsWords (gs.take gi) + 1 + (t + 1) =
            groupPtr + groupsWords (gs.take gi) + 2 + t by clear * -; omega, h4 t ht]
          simp [hget]⟩
  · unfold buildGroupsCost
    have hlg1 : 1 ≤ Nat.log 2 (m + 1) + 1 := by clear * -; omega
    have hmul : m ≤ m * (Nat.log 2 (m + 1) + 1) := Nat.le_mul_of_pos_right m hlg1
    rw [Nat.mul_assoc] at hcP1 ⊢
    clear * - hcP1 hcL4 hcL5 hcAll hnG_le hmul
    omega

public section

/-- **Verification of `asmFirstBuildGroupsStmt bSort`** on `[spPtr, vCap, h]`:
builds `gs = splitGroupsOf (L.map fun s => (s.kept, s.fresh))` in `readGroups` format, writes
`[gs.length, groupPtr]` at `[h, h + 2)`, preserves memory below `h` and `ZeroFrom`, uses at most
`buildGroupsSpace vCap L.length` heap words, and runs in at most `buildGroupsCost L.length` steps. -/
theorem asmFirstBuildGroups_runs {w bSort spPtr vCap h pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {L : List CompSplitEntry} {mem₀ : ℕ → ℕ}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w)
    (hSp : SplitEntriesAt mem₀ spPtr L)
    (hSp_lt : spPtr + splitEntriesWords L ≤ h)
    (hL_vCap : ∀ s ∈ L, s.kept < vCap ∧ s.fresh < vCap)
    (hold_eq :
      let pairs := L.map fun s => (s.kept, s.fresh)
      splitOldList pairs (fun _ => 0) =
        pairs.map fun p => ancDecode (splitAncFold pairs (fun _ => 0)) p.2)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + buildGroupsSpace vCap L.length < 2 ^ w) :
    let pairs := L.map fun s => (s.kept, s.fresh)
    let gs := splitGroupsOf pairs
    ∃ hEnd groupPtr st' c,
      Runs w p ω (asmFirstBuildGroupsStmt bSort)
        (startState [spPtr, vCap, h] mem₀ pos) (.returned hEnd) st' c ∧
      st'.mem h = gs.length ∧
      st'.mem (h + 1) = groupPtr ∧
      readGroups st'.mem groupPtr gs.length = gs ∧
      h + 2 ≤ groupPtr ∧
      groupPtr + groupsWords gs = hEnd ∧
      hEnd ≤ h + buildGroupsSpace vCap L.length ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      c ≤ buildGroupsCost L.length := by
  intro pairs gs
  set m := L.length
  have hpairs_len : pairs.length = m := List.length_map _
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hSp_words : splitEntriesWords L = 1 + 4 * m := rfl
  have hSpace_un : h + (2 + vCap + 10 * m) < 2 ^ w := by unfold buildGroupsSpace at hSpace; exact hSpace
  set st0 := startState [spPtr, vCap, h] mem₀ pos
  set stA : State := { st0 with regs := Function.update st0.regs 3 m }
  have ha3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal stA 3 :=
    runs_assign_iff.mpr ⟨m, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st0, startState])) hSp.1, rfl, rfl, rfl⟩
  -- Case 1: `m = 0`
  by_cases hm0 : m = 0
  · have hL_nil : L = [] := List.eq_nil_of_length_eq_zero hm0
    have hgs_nil : gs = [] := by simp [gs, pairs, hL_nil, splitGroupsOf, splitOldRoots, splitOldList]
    have hcond : (Expr.bin .eq (.reg 3) (.const 0)).eval w stA = some 1 := by
      simp [Expr.eval, BinOp.eval, stA, hm0, h0w, h1w]
    set mem1 := Function.update mem₀ h 0
    set mem2 := Function.update mem1 (h + 1) (h + 2)
    have hs1 : Runs w p ω (.store (.reg 2) (.const 0)) stA .normal ⟨mem1, stA.regs, pos⟩ 3 :=
      runs_store_iff.mpr ⟨h, 0, Expr.eval_reg_of_eq (by simp [stA, st0, startState]), Expr.eval_const h0w, rfl, rfl, rfl⟩
    have hs2 : Runs w p ω (.store (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 2) (.const 2)))
        ⟨mem1, stA.regs, pos⟩ .normal ⟨mem2, stA.regs, pos⟩ 7 :=
      runs_store_iff.mpr ⟨h + 1, h + 2,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, st0, startState])) (Expr.eval_const h1w) (by omega),
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, st0, startState])) (Expr.eval_const h2w) (by omega),
        rfl, rfl, rfl⟩
    have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 2)))
        ⟨mem2, stA.regs, pos⟩ (.returned (h + 2)) ⟨mem2, stA.regs, pos⟩ 4 :=
      runs_ret_iff.mpr ⟨h + 2,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, st0, startState])) (Expr.eval_const h2w) (by omega),
        rfl, rfl, rfl⟩
    have hthen := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2, hret, rfl⟩), rfl⟩)
    have hfull : Runs w p ω (asmFirstBuildGroupsStmt bSort) st0 (.returned (h + 2)) ⟨mem2, stA.regs, pos⟩ _ :=
      runs_seq_iff.mpr (Or.inr ⟨stA, _, _, ha3,
        runs_cond_iff.mpr ⟨1, _, hcond, by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩)
    refine ⟨h + 2, h + 2, ⟨mem2, stA.regs, pos⟩, _, hfull,
      by change mem2 h = gs.length; dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_self, hgs_nil]; rfl,
      by change mem2 (h + 1) = h + 2; dsimp only [mem2]; exact Function.update_self _ _ _,
      by simp [hgs_nil, readGroups], le_refl _, by simp [hgs_nil, groupsWords],
      by unfold buildGroupsSpace; omega,
      fun a ha => by
        change mem2 a = 0; dsimp only [mem2, mem1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hZero a (by omega),
      fun a ha => by
        change mem2 a = mem₀ a; dsimp only [mem2, mem1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
      by unfold buildGroupsCost; simp [Expr.size]⟩
  -- Case 2: `m > 0`
  have hcondF : (Expr.bin .eq (.reg 3) (.const 0)).eval w stA = some 0 := by
    simp [Expr.eval, BinOp.eval, stA, hm0, h0w]
  obtain ⟨stL3, cP1, hrunP1, hUniqPW, hUniq_mem_old, hnG_le,
    hr0_3, hr2_3, hr3_3, hr8_3, hr14_3, hr15_3, hr16_3, hr17_3, hr18_3,
    hUniqAt, hgrpL3, hcntL3, hzrL3, hfrL3, hcP1⟩ :=
    asmFirstBuildGroups_part1_runs (ω := ω) (pos := pos) hpSort hw16 hSp hSp_lt hL_vCap hZero hSpace
  set oldL := splitOldList pairs (fun _ => 0)
  set uniqL := splitOldRoots pairs
  set nG := uniqL.length
  set uniqOld := h + 2 + vCap + 3 * m
  set grpOf := uniqOld + nG
  set cntBase := grpOf + m
  set curBase := cntBase + nG
  set groupPtr := curBase + nG
  have holdL_len : oldL.length = m := by rw [splitOldList_length, hpairs_len]
  have hUniq_nd : uniqL.Nodup := hUniqPW.imp fun hab => ne_of_lt hab
  have hgs_eq : gs = uniqL.map fun r => r :: groupMembers pairs oldL r := by
    unfold gs splitGroupsOf
    refine List.map_congr_left fun r _ => ?_
    congr 1
    exact (groupMembers_eq_filter_snd pairs oldL (splitAncFold pairs (fun _ => 0)) hold_eq r).symm
  have hgs_len : gs.length = nG := by rw [hgs_eq, List.length_map]
  have hgs_get : ∀ gi (hgi : gi < nG),
      gs[gi]'(by omega) = uniqL[gi]'hgi :: groupMembers pairs oldL (uniqL[gi]'hgi) := fun gi hgi => by
    simp [hgs_eq]
  have hgs_words : groupsWords gs = 2 * nG + m := by
    rw [groupsWords_eq_sum_lengths, hgs_len]
    have htot : groupsTotalLen gs = nG + m := by
      unfold groupsTotalLen
      rw [hgs_eq, List.map_map]
      have h1 : ∀ (l : List ℕ) (f : ℕ → ℕ), (l.map fun r => 1 + f r).sum = l.length + (l.map f).sum := by
        intro l f; induction l with | nil => simp | cons a tl ihl => simp [ihl]; omega
      have h2 : (uniqL.map fun r => (r :: groupMembers pairs oldL r).length).sum =
          nG + (uniqL.map fun r => (groupMembers pairs oldL r).length).sum := by
        change (uniqL.map fun r => (r :: groupMembers pairs oldL r).length).sum =
          uniqL.length + (uniqL.map fun r => (groupMembers pairs oldL r).length).sum
        simpa only [List.length_cons, Nat.add_comm] using h1 uniqL (fun r => (groupMembers pairs oldL r).length)
      rw [show (List.map (List.length ∘ fun r => r :: groupMembers pairs oldL r) uniqL).sum =
          (uniqL.map fun r => (r :: groupMembers pairs oldL r).length).sum from rfl, h2,
        sum_groupMembers_length (by omega : oldL.length = pairs.length) hUniq_nd hUniq_mem_old, hpairs_len]
    omega
  obtain ⟨hEnd, stEnd, cAll, hfull, hm0, hm1, hrg, hgp_lo, hgp_end, hsp_end, hz_end, hfr_end, hc_end⟩ :=
    asmFirstBuildGroups_epilogue hw16 rfl holdL_len rfl hnG_le hgs_len hSp hSp_lt rfl rfl rfl rfl rfl
      hgs_words hSpace_un hUniq_nd hUniq_mem_old hgs_get ha3 hcondF hrunP1 hcP1
      hr0_3 hr2_3 hr3_3 hr8_3 hr14_3 hr15_3 hr16_3 hr17_3 hr18_3 hUniqAt hgrpL3 hcntL3 hzrL3 hfrL3
  exact ⟨hEnd, groupPtr, stEnd, cAll, hfull, hm0, hm1, hrg, hgp_lo, hgp_end, hsp_end, hz_end, hfr_end, hc_end⟩

end

end MinCostFlow.SparseCore.Program
