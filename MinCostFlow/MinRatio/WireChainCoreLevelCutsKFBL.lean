module

public import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
import WordRAM.Memory
import WordRAM.Tactic

/-!
# The cuts of the lists `fDel j` of the plain levels (`WireChainCoreLevelCutsKFBL`)

After the loop of Branch B, the plain levels `j < i₀` have lost the edges of their lists
`fDel j` from their forests. Step 4 of Branch B cuts these edges from the path tree. The slot of
level `j` names its list: word `2` holds its address and word `3` its length.

`wireEmitLevelCutsLoop` runs the cut emitter (`wireEmitTreeCutsBody`) on the list of each level in
turn and puts the cut lists one after the other in one buffer. The emitter keeps an edge when its
word in the table `pres` is not `0`. Step 4 passes the presence array of the root graph, so a cut
is kept exactly when its edge is still in the graph. `wireEmitLevelCutsLoop_runs` gives its run:
the buffer holds the cuts of all levels in level order, at cost `40` per entry and `64` per level
plus `7`, and no word below the buffer changes.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program

/-- The loop of step 4: for `j = reg 96 < reg 99`, read the list of level `j` from words `2`, `3`
of the slot `reg 72 + 1 + 12 j`, and emit its cuts at `reg 16 + 2 · reg 17`, where `reg 17`
counts the cuts so far and `reg 15` is the table that the emitter tests. -/
@[expose] def wireEmitLevelCutsLoop (emitCuts : ℕ) : Stmt :=
  forRange 96 (.const 0) (.reg 99)
    (.assign 33 (.bin .add (.bin .add (.reg 72) (.const 1)) (.bin .mul (.const 12) (.reg 96))) ;;
     .assign 34 (.load (.bin .add (.reg 33) (.const 2))) ;;
     .assign 35 (.load (.bin .add (.reg 33) (.const 3))) ;;
     .assign 36 (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))) ;;
     .call 18 emitCuts [.reg 34, .reg 35, .const 1, .const 0, .reg 15, .reg 36] ;;
     .assign 17 (.bin .add (.reg 17) (.reg 18)))

theorem wireEmitLevelCutsLoop_noRand (emitCuts : ℕ) : (wireEmitLevelCutsLoop emitCuts).NoRand := by
  simp [wireEmitLevelCutsLoop, forRange, forUp, Stmt.NoRand]

/-- The cuts of the levels `j < n`, in level order. -/
@[expose] def levelCutsOf (pres : ℕ → ℕ) (fDel : ℕ → List ℕ) (n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun j => treeCutsOf pres (fDel j))

theorem levelCutsOf_succ (pres : ℕ → ℕ) (fDel : ℕ → List ℕ) (n : ℕ) :
    levelCutsOf pres fDel (n + 1) = levelCutsOf pres fDel n ++ treeCutsOf pres (fDel n) := by
  simp [levelCutsOf, List.range_succ, List.flatMap_append]

theorem levelCutsOf_length_le (pres : ℕ → ℕ) (fDel : ℕ → List ℕ) (n : ℕ) :
    (levelCutsOf pres fDel n).length ≤ ∑ j ∈ Finset.range n, (fDel j).length := by
  induction n with
  | zero => simp [levelCutsOf]
  | succ n ih =>
    rw [levelCutsOf_succ, List.length_append, Finset.sum_range_succ]
    have := treeCutsOf_length_le pres (fDel n)
    omega

theorem mem_levelCutsOf {pres : ℕ → ℕ} {fDel : ℕ → List ℕ} {n e : ℕ} :
    e ∈ levelCutsOf pres fDel n ↔ ∃ j < n, e ∈ fDel j ∧ pres e ≠ 0 := by
  simp [levelCutsOf, mem_treeCutsOf]

/-- Two packed edit lists one after the other. -/
theorem treeEditsAt_append {mem : ℕ → ℕ} {base : ℕ} {xs ys : List TreeChange}
    (hx : TreeEditsAt mem base xs) (hy : TreeEditsAt mem (base + 2 * xs.length) ys) :
    TreeEditsAt mem base (xs ++ ys) := by
  unfold TreeEditsAt at hx hy ⊢
  rw [List.flatMap_append]
  refine listAt_append.mpr ⟨hx, ?_⟩
  rw [treeEditWords_length]
  exact hy

theorem rangeCost_zero_eq_sum (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [rangeCost, List.range'_concat]

set_option maxHeartbeats 1600000 in
/-- The run of `wireEmitLevelCutsLoop` over the levels `j < n`. The slot words, the lists and the
tested words of their entries lie below the zero buffer at `base`. Afterwards the buffer holds
`levelCutsOf (fun e => mem (pres + e)) fDel n`, `reg 17` its length, the words from its end on
are zero, and no word below `base` changes. -/
theorem wireEmitLevelCutsLoop_runs
    {w emitCuts selBase pres base n : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {fPtr : ℕ → ℕ} {fDel : ℕ → List ℕ}
    (hEmit : p.procs[emitCuts]? = some wireEmitTreeCutsBody)
    (hRegs : st.regs 72 = selBase ∧ st.regs 99 = n ∧ st.regs 15 = pres ∧ st.regs 16 = base ∧
      st.regs 17 = 0)
    (hSlot : ∀ j < n, st.mem (selBase + 1 + 12 * j + 2) = fPtr j ∧
      st.mem (selBase + 1 + 12 * j + 3) = (fDel j).length ∧ ListAt st.mem (fPtr j) (fDel j) ∧
      fPtr j + (fDel j).length ≤ base ∧ selBase + 1 + 12 * j + 3 < base)
    (hPresLt : ∀ j < n, ∀ e ∈ fDel j, pres + e < base)
    (hz : ZeroFrom st.mem base)
    (hRoom : base + 2 * ∑ j ∈ Finset.range n, (fDel j).length + 1 < 2 ^ w)
    (hw : 12 < 2 ^ w) :
    let cuts := levelCutsOf (fun e => st.mem (pres + e)) fDel n
    ∃ out cost,
      Runs w p ω (wireEmitLevelCutsLoop emitCuts) st .normal out cost ∧
      cost ≤ 40 * ∑ j ∈ Finset.range n, (fDel j).length + 64 * n + 7 ∧
      out.regs 17 = cuts.length ∧
      (∀ r, r ≠ 17 → r ≠ 18 → r ≠ 33 → r ≠ 34 → r ≠ 35 → r ≠ 36 → r ≠ 96 →
        out.regs r = st.regs r) ∧
      TreeEditsAt out.mem base (cuts.map TreeChange.delete) ∧
      ZeroFrom out.mem (base + 2 * cuts.length) ∧
      ∀ a < base, out.mem a = st.mem a := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hwne : w ≠ 0 := by rintro rfl; simp at hw1
  have hnW : n < 2 ^ w := by
    by_cases hn : n = 0
    · omega
    · have := (hSlot (n - 1) (by omega)).2.2.2.2
      omega
  let presFn : ℕ → ℕ := fun e => st.mem (pres + e)
  let T : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, (fDel j).length
  have hTmono : ∀ i ≤ n, T i ≤ T n := fun i hi =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hi)
  have hRoomT : base + 2 * T n + 1 < 2 ^ w := hRoom
  let Inv (i : ℕ) (s : State) : Prop :=
    let pref := levelCutsOf presFn fDel i
    s.regs 17 = pref.length ∧ s.regs 96 = i ∧
    (∀ r, r ≠ 17 → r ≠ 18 → r ≠ 33 → r ≠ 34 → r ≠ 35 → r ≠ 36 → r ≠ 96 →
      s.regs r = st.regs r) ∧
    TreeEditsAt s.mem base (pref.map TreeChange.delete) ∧
    ZeroFrom s.mem (base + 2 * pref.length) ∧
    ∀ a < base, s.mem a = st.mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 96) (lo := .const 0) (hi := .reg 99)
    (P := fun s => s = st) (Inv := Inv) (fun i => 40 * (fDel i).length + 55) 0 n
    (Nat.zero_le _) hw1 (fun _ => hnW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w], ?_⟩
      refine ⟨by simp [levelCutsOf, hRegs.2.2.2.2], by simp, fun r h17 _ _ _ _ _ h96 => by
          simp [Function.update_of_ne h96],
        by simp [levelCutsOf, TreeEditsAt, ListAt],
        by simpa [levelCutsOf] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by
      have := h.2.2.1 99 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
      simp [Expr.eval, this, hRegs.2.1])
    (fun i _ hi s ω' ⟨h17, h96, hRest, hList, hZ, hFr⟩ => by
      set pref := levelCutsOf presFn fDel i with hpref
      obtain ⟨hP2, hP3, hLA, hEnd, hSlotLt⟩ := hSlot i hi
      have hPrefLe : pref.length ≤ T i := levelCutsOf_length_le presFn fDel i
      have hTi : T i + (fDel i).length = T (i + 1) := (Finset.sum_range_succ _ _).symm
      have hTi1 := hTmono (i + 1) (by omega)
      have h72 : s.regs 72 = selBase := (hRest 72 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hRegs.1
      have h15 : s.regs 15 = pres := (hRest 15 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hRegs.2.2.1
      have h16 : s.regs 16 = base := (hRest 16 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hRegs.2.2.2.1
      have hSl : selBase + 1 + 12 * i + 3 < 2 ^ w := by omega
      let a33 := selBase + 1 + 12 * i
      let ob := base + 2 * pref.length
      let t1 := { s with regs := Function.update s.regs 33 a33 }
      let t2 := { t1 with regs := Function.update t1.regs 34 (fPtr i) }
      let t3 := { t2 with regs := Function.update t2.regs 35 (fDel i).length }
      let t4 := { t3 with regs := Function.update t3.regs 36 ob }
      have hob : ob = base + 2 * pref.length := rfl
      have ha33 : a33 = selBase + 1 + 12 * i := rfl
      have rt1 : Runs w p ω' (.assign 33 (.bin .add (.bin .add (.reg 72) (.const 1))
          (.bin .mul (.const 12) (.reg 96)))) s .normal t1 8 :=
        runs_assign_iff.mpr ⟨a33, by
          simp [Expr.eval, BinOp.eval, h72, h96, hw1, hw, show selBase + 1 < 2 ^ w by omega,
            show 12 * i < 2 ^ w by omega, show selBase + 1 + 12 * i < 2 ^ w by omega, a33],
          rfl, rfl, rfl⟩
      have rt2 : Runs w p ω' (.assign 34 (.load (.bin .add (.reg 33) (.const 2)))) t1 .normal
          t2 5 :=
        runs_assign_iff.mpr ⟨fPtr i, by
          simp [Expr.eval, BinOp.eval, t1, hw2, show a33 + 2 < 2 ^ w by omega]
          rw [hFr _ (by omega)]; exact hP2, rfl, rfl, rfl⟩
      have rt3 : Runs w p ω' (.assign 35 (.load (.bin .add (.reg 33) (.const 3)))) t2 .normal
          t3 5 :=
        runs_assign_iff.mpr ⟨(fDel i).length, by
          simp [Expr.eval, BinOp.eval, t2, t1, show 3 < 2 ^ w by omega,
            show a33 + 3 < 2 ^ w by omega]
          rw [hFr _ (by omega)]; exact hP3, rfl, rfl, rfl⟩
      have rt4 : Runs w p ω' (.assign 36 (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))))
          t3 .normal t4 6 :=
        runs_assign_iff.mpr ⟨ob, by
          simp [Expr.eval, BinOp.eval, t3, t2, t1, h16, h17, hw2,
            show 2 * pref.length < 2 ^ w by omega, show ob < 2 ^ w by omega, ob],
          rfl, rfl, rfl⟩
      -- the emitter on the list of level `i`
      have hCutsEq : treeCutsOf (fun e => t4.mem (pres + e)) (fDel i) =
          treeCutsOf presFn (fDel i) := by
        unfold treeCutsOf
        refine List.filter_congr (fun e he => ?_)
        have := hPresLt i hi e he
        simp only [t4, t3, t2, t1, presFn]
        rw [hFr _ this]
      obtain ⟨outE, cE, rE, hcE, hListE, hZE, hFrE⟩ :=
        wireEmitTreeCutsBody_runs (w := w) (src := fPtr i) (len := (fDel i).length)
          (stride := 1) (off := 0) (slots := pres) (outBuf := ob) (pos := t4.pos) (p := p)
          (ω := ω') (mem := t4.mem) (es := fDel i) rfl
          (fun k hk => by
            simp only [t4, t3, t2, t1, one_mul, add_zero]
            rw [hFr _ (by omega)]; exact hLA k hk)
          (fun k hk => by omega) (fun e he => by have := hPresLt i hi e he; omega)
          (fun a ha => by
            simp only [t4, t3, t2, t1]
            exact hZ a ha)
          (by omega) hw2
      rw [hCutsEq] at rE hListE hZE
      set ci := treeCutsOf presFn (fDel i) with hci
      have hciLe : ci.length ≤ (fDel i).length := treeCutsOf_length_le _ _
      let t5 := { outE with regs := Function.update t4.regs 18 ci.length }
      have rt5 : Runs w p ω'
          (.call 18 emitCuts [.reg 34, .reg 35, .const 1, .const 0, .reg 15, .reg 36]) t4
            .normal t5 (6 + cE + 1) :=
        runs_call_iff.mpr ⟨[fPtr i, (fDel i).length, 1, 0, pres, ob], wireEmitTreeCutsBody,
          .returned ci.length, outE, cE,
          by simp [evalArgs, Expr.eval, t4, t3, t2, t1, h15, Nat.two_pow_pos w, hw1],
          hEmit, rE, rfl, rfl, by simp [argsSize, Expr.size]⟩
      let t6 := { t5 with regs := Function.update t5.regs 17 (pref.length + ci.length) }
      have rt6 : Runs w p ω' (.assign 17 (.bin .add (.reg 17) (.reg 18))) t5 .normal t6 4 :=
        runs_assign_iff.mpr ⟨pref.length + ci.length, by
          simp [Expr.eval, BinOp.eval, t5, t4, t3, t2, t1, h17,
            show pref.length + ci.length < 2 ^ w by omega], rfl, rfl, rfl⟩
      have rBody : Runs w p ω' _ s .normal t6 _ :=
        runs_seq_iff.mpr (Or.inr ⟨t1, 8, _, rt1,
          runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 5, _, rt3,
              runs_seq_iff.mpr (Or.inr ⟨t4, 6, _, rt4,
                runs_seq_iff.mpr (Or.inr ⟨t5, 6 + cE + 1, 4, rt5, rt6, rfl⟩), rfl⟩), rfl⟩),
            rfl⟩), rfl⟩)
      have hNew : levelCutsOf presFn fDel (i + 1) = pref ++ ci := levelCutsOf_succ _ _ _
      refine ⟨.normal, t6, _, rBody, ⟨?_, ?_⟩, by dsimp only; omega⟩
      · dsimp only [Inv]
        rw [hNew]
        refine ⟨by simp [t6], ?_, fun r h17' h18 h33 h34 h35 h36 h96' => ?_, ?_, ?_, ?_⟩
        · simp [t6, t5, t4, t3, t2, t1]
        · have := hRest r h17' h18 h33 h34 h35 h36 h96'
          simp [t6, t5, t4, t3, t2, t1, Function.update_of_ne, h17', h18, h33, h34, h35, h36,
            h96', this]
        · rw [List.map_append]
          refine treeEditsAt_append ?_ ?_
          · intro j hj
            have hjlt : j < 2 * pref.length := by
              rw [treeEditWords_length, List.length_map] at hj; exact hj
            change outE.mem (base + j) = _
            rw [hFrE _ (by omega)]
            exact hList j hj
          · rw [List.length_map]
            exact hListE
        · intro a ha
          change outE.mem a = 0
          rw [List.length_append] at ha
          exact hZE a (by omega)
        · intro a ha
          change outE.mem a = st.mem a
          rw [hFrE a (by omega)]
          exact hFr a ha
      · simp [t6, t5, t4, t3, t2, t1, h96])
  obtain ⟨o, sE, cLoop, rLoop, hInvE, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInvE
  | normal =>
    obtain ⟨h17E, _, hRestE, hListE, hZE, hFrE⟩ := hInvE
    have hrc : rangeCost (fun i => 40 * (fDel i).length + 55) 0 n =
        40 * ∑ j ∈ Finset.range n, (fDel j).length + 55 * n := by
      rw [rangeCost_zero_eq_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_comm n 55]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨sE, cLoop, rLoop, by omega, h17E, fun r h1 h2 h3 h4 h5 h6 h7 =>
      hRestE r h1 h2 h3 h4 h5 h6 h7, hListE, hZE, hFrE⟩

end MinCostFlow.MinRatio
