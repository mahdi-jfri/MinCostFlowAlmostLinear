module

public import MinCostFlow.SparseCore.Program.CompSplitListBranchBase
import WordRAM.Tactic

/-!
# Per-Branch Cut-Scan and `isNew`-Unmark Loops (`CompSplitListScan`)

Defines and verifies the two linear scan loops inside `compEmitBranchSplitProc`:

1. `compScanCutsStmt` / `compScanCuts_runs`: scans `cuts1` at `[oldC, newC)` in `rootsPtr` and
   `fDelPtr`, marking `isNew[r] := 1` in `[ufBase, ufBase + vCap)`, setting `hasInp := 1` if
   `tag = 1 ∧ fDel[q] = delE`, and copying the remaining released forest edges into `dBuf[0..t)`.
2. `compUnmarkIsNewStmt` / `compUnmarkIsNew_runs`: clears `isNew[r] := 0` for every root
   marked in `compScanCutsStmt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Scan `q = r20 (oldC) .. r5 (newC) - 1`: mark `isNew[roots[q]] := 1`; if `tag = 1 ∧ fDel[q] = delE`
set `r19 := 1`, else append `fDel[q]` to `dBuf[r18++]`. -/
def compScanCutsStmt : Stmt :=
  .loop (.bin .lt (.reg 20) (.reg 5))
    (.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
     .store (.bin .add (.reg 12) (.reg 21)) (.const 1) ;;
     .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
     .assign 23 (.bin .mul (.bin .eq (.reg 6) (.const 1)) (.bin .eq (.reg 22) (.reg 7))) ;;
     .cond (.reg 23)
       (.assign 19 (.const 1))
       (.store (.bin .add (.reg 15) (.reg 18)) (.reg 22) ;;
        .assign 18 (.bin .add (.reg 18) (.const 1))) ;;
     .assign 20 (.bin .add (.reg 20) (.const 1)))

/-- Clear `isNew[roots[q]] := 0` for `q = r20 (oldC) .. r5 (newC) - 1`. -/
def compUnmarkIsNewStmt : Stmt :=
  .loop (.bin .lt (.reg 20) (.reg 5))
    (.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
     .store (.bin .add (.reg 12) (.reg 21)) (.const 0) ;;
     .assign 20 (.bin .add (.reg 20) (.const 1)))

lemma compScanCutsStmt_noRand : compScanCutsStmt.NoRand := by simp [compScanCutsStmt, Stmt.NoRand]
lemma compUnmarkIsNewStmt_noRand : compUnmarkIsNewStmt.NoRand := by simp [compUnmarkIsNewStmt, Stmt.NoRand]

set_option maxHeartbeats 600000 in
/-- Verification of `compScanCutsStmt`: marks `isNew` for every cut root, detects `tag = 1 ∧ delE`
in `cuts1`, and writes the released edges `D_raw` contiguously at `dBuf`, in `≤ 55 * cuts1.length + 10`
steps. -/
theorem compScanCuts_runs {w rootsPtr fDelPtr oldC tag delE ufBase vCap dBuf : ℕ}
    {cuts1 : List (ℕ × ℕ)} {p : Program} {ω : ℕ → Bool} {st : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hrts_w : rootsPtr + oldC + cuts1.length < 2 ^ w)
    (hfdel_w : fDelPtr + oldC + cuts1.length < 2 ^ w)
    (huf_w : ufBase + vCap < 2 ^ w)
    (hdbuf_w : dBuf + cuts1.length < 2 ^ w)
    (hdisj_ru : rootsPtr + oldC + cuts1.length ≤ ufBase ∨ ufBase + vCap ≤ rootsPtr + oldC)
    (hdisj_fu : fDelPtr + oldC + cuts1.length ≤ ufBase ∨ ufBase + vCap ≤ fDelPtr + oldC)
    (hdisj_rd : rootsPtr + oldC + cuts1.length ≤ dBuf ∨ dBuf + cuts1.length ≤ rootsPtr + oldC)
    (hdisj_fd : fDelPtr + oldC + cuts1.length ≤ dBuf ∨ dBuf + cuts1.length ≤ fDelPtr + oldC)
    (hdisj_ud : ufBase + vCap ≤ dBuf)
    (hcut_r : ∀ p ∈ cuts1, p.2 < vCap)
    (hcut_m : ∀ i (hi : i < cuts1.length),
      st.mem (rootsPtr + (oldC + i)) = cuts1[i].2 ∧ st.mem (fDelPtr + (oldC + i)) = cuts1[i].1)
    (hr2 : st.regs 2 = rootsPtr) (hr3 : st.regs 3 = fDelPtr)
    (hr5 : st.regs 5 = oldC + cuts1.length) (hr6 : st.regs 6 = tag) (hr7 : st.regs 7 = delE)
    (hr12 : st.regs 12 = ufBase) (hr15 : st.regs 15 = dBuf)
    (hr18 : st.regs 18 = 0) (hr19 : st.regs 19 = 0) (hr20 : st.regs 20 = oldC) :
    let D_raw := if tag = 1 then (cuts1.map Prod.fst).filter (· ≠ delE) else cuts1.map Prod.fst
    let hasInp := if tag = 1 ∧ delE ∈ cuts1.map Prod.fst then 1 else 0
    ∃ st' c,
      Runs w p ω compScanCutsStmt st .normal st' c ∧
      (∀ r < 18, st'.regs r = st.regs r) ∧
      st'.regs 18 = D_raw.length ∧
      st'.regs 19 = hasInp ∧
      ListAt st'.mem dBuf D_raw ∧
      (∀ v < vCap, st'.mem (ufBase + v) = if v ∈ cuts1.map Prod.snd then 1 else st.mem (ufBase + v)) ∧
      (∀ a, (a < ufBase ∨ ufBase + vCap ≤ a) → (a < dBuf ∨ dBuf + D_raw.length ≤ a) →
        st'.mem a = st.mem a) ∧
      c ≤ 55 * cuts1.length + 10 := by
  intro D_raw hasInp
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw1 : 1 < 2 ^ w := by omega
  let prefD : ℕ → List ℕ := fun i =>
    if tag = 1 then ((cuts1.take i).map Prod.fst).filter (· ≠ delE) else (cuts1.take i).map Prod.fst
  let prefH : ℕ → ℕ := fun i => if tag = 1 ∧ delE ∈ (cuts1.take i).map Prod.fst then 1 else 0
  have hprefD_le : ∀ i ≤ cuts1.length, (prefD i).length ≤ i := fun i hi => by
    dsimp only [prefD]; split_ifs
    · exact le_trans (List.length_filter_le ..) (by simp [hi])
    · simp [hi]
  have hloop : ∀ rem i (s : State) (hi : i ≤ cuts1.length), cuts1.length - i = rem →
      (∀ r < 18, s.regs r = st.regs r) →
      s.regs 18 = (prefD i).length → s.regs 19 = prefH i → s.regs 20 = oldC + i →
      ListAt s.mem dBuf (prefD i) →
      (∀ v < vCap, s.mem (ufBase + v) =
        if v ∈ (cuts1.take i).map Prod.snd then 1 else st.mem (ufBase + v)) →
      (∀ a, (a < ufBase ∨ ufBase + vCap ≤ a) → (a < dBuf ∨ dBuf + (prefD i).length ≤ a) →
        s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω compScanCutsStmt s .normal st' c ∧
        (∀ r < 18, st'.regs r = st.regs r) ∧
        st'.regs 18 = D_raw.length ∧ st'.regs 19 = hasInp ∧
        ListAt st'.mem dBuf D_raw ∧
        (∀ v < vCap, st'.mem (ufBase + v) = if v ∈ cuts1.map Prod.snd then 1 else st.mem (ufBase + v)) ∧
        (∀ a, (a < ufBase ∨ ufBase + vCap ≤ a) → (a < dBuf ∨ dBuf + D_raw.length ≤ a) →
          st'.mem a = st.mem a) ∧
        c ≤ 55 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hr_o hr18s hr19s hr20s hLA hIs hfr
      have hi_eq : i = cuts1.length := by omega
      subst hi_eq
      have htk : cuts1.take cuts1.length = cuts1 := List.take_length
      have hDeq : prefD cuts1.length = D_raw := by dsimp only [prefD, D_raw]; rw [htk]
      have hHeq : prefH cuts1.length = hasInp := by dsimp only [prefH, hasInp]; rw [htk]
      rw [hDeq] at hr18s hLA hfr; rw [hHeq] at hr19s; rw [htk] at hIs
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr20s, hr_o 5 (by omega), hr5],
        rfl, rfl, by simp [Expr.size]⟩), hr_o, hr18s, hr19s, hLA, hIs, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hr_o hr18s hr19s hr20s hLA hIs hfr
      have hi_lt : i < cuts1.length := by omega
      set r_i := cuts1[i].2
      set e_i := cuts1[i].1
      have hri_lt : r_i < vCap := hcut_r cuts1[i] (List.getElem_mem hi_lt)
      have hlen_le : (prefD i).length ≤ i := hprefD_le i (by omega)
      have hs_r : s.mem (rootsPtr + (oldC + i)) = r_i := by
        rw [hfr _ (by rcases hdisj_ru with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
          (by rcases hdisj_rd with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
        exact (hcut_m i hi_lt).1
      have hs_e : s.mem (fDelPtr + (oldC + i)) = e_i := by
        rw [hfr _ (by rcases hdisj_fu with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
          (by rcases hdisj_fd with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
        exact (hcut_m i hi_lt).2
      have htake_succ : cuts1.take (i + 1) = cuts1.take i ++ [cuts1[i]] := List.take_succ_eq_append_getElem hi_lt
      let s1 : State := { s with regs := Function.update s.regs 21 r_i }
      let s2 : State := { s1 with mem := Function.update s1.mem (ufBase + r_i) 1 }
      let s3 : State := { s2 with regs := Function.update s2.regs 22 e_i }
      set isMatch := (if tag = 1 then 1 else 0) * (if e_i = delE then 1 else 0)
      let s4 : State := { s3 with regs := Function.update s3.regs 23 isMatch }
      have hs1 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 2) (.reg 20)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨r_i, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_o 2 (by omega), hr2, hr20s, show rootsPtr + (oldC + i) < 2 ^ w by omega])
          hs_r, rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg 12) (.reg 21)) (.const 1)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨ufBase + r_i, 1,
          by simp [s1, Expr.eval, BinOp.eval, hr_o 12 (by omega), hr12, show ufBase + r_i < 2 ^ w by omega],
          by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
      have hs2_e : s2.mem (fDelPtr + (oldC + i)) = e_i := by
        dsimp only [s2, s1]
        rw [Function.update_of_ne (by rcases hdisj_fu with h | h <;> omega)]
        exact hs_e
      have hs3 : Runs w p ω (.assign 22 (.load (.bin .add (.reg 3) (.reg 20)))) s2 .normal s3 5 :=
        runs_assign_iff.mpr ⟨e_i, Expr.eval_load_of_eq (by
          simp [s2, s1, Expr.eval, BinOp.eval, hr_o 3 (by omega), hr3, hr20s, show fDelPtr + (oldC + i) < 2 ^ w by omega])
          hs2_e, rfl, rfl, by simp [Expr.size]⟩
      have hs4 : Runs w p ω
          (.assign 23 (.bin .mul (.bin .eq (.reg 6) (.const 1)) (.bin .eq (.reg 22) (.reg 7)))) s3 .normal s4 8 :=
        runs_assign_iff.mpr ⟨isMatch, by
          have ht_w : (if tag = 1 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
          have he_w : (if e_i = delE then 1 else 0) < 2 ^ w := by split_ifs <;> omega
          have hisM_w : isMatch < 2 ^ w := by dsimp [isMatch]; split_ifs <;> omega
          by_cases ht : tag = 1 <;> by_cases he : e_i = delE <;>
            simp [s3, s2, s1, Expr.eval, BinOp.eval, hr_o 6 (by omega), hr6, hr_o 7 (by omega), hr7,
              hw1, ht, he, isMatch], rfl, rfl, by simp [Expr.size]⟩
      have hIs_s2 : ∀ v < vCap, s2.mem (ufBase + v) =
          if v ∈ (cuts1.take (i + 1)).map Prod.snd then 1 else st.mem (ufBase + v) := fun v hv => by
        dsimp only [s2, s1]
        rw [htake_succ, List.map_append, List.map_singleton]
        by_cases hvr : v = r_i
        · subst hvr; simp [r_i]
        · rw [Function.update_of_ne (by omega), hIs v hv]
          simp [r_i, hvr]
      have hbranch : ∃ s5 cB,
          Runs w p ω
            (.cond (.reg 23) (.assign 19 (.const 1))
              (.store (.bin .add (.reg 15) (.reg 18)) (.reg 22) ;;
               .assign 18 (.bin .add (.reg 18) (.const 1)))) s4 .normal s5 cB ∧
          (∀ r < 18, s5.regs r = st.regs r) ∧
          s5.regs 18 = (prefD (i + 1)).length ∧ s5.regs 19 = prefH (i + 1) ∧
          s5.regs 20 = oldC + i ∧
          ListAt s5.mem dBuf (prefD (i + 1)) ∧
          (∀ v < vCap, s5.mem (ufBase + v) =
            if v ∈ (cuts1.take (i + 1)).map Prod.snd then 1 else st.mem (ufBase + v)) ∧
          (∀ a, (a < ufBase ∨ ufBase + vCap ≤ a) → (a < dBuf ∨ dBuf + (prefD (i + 1)).length ≤ a) →
            s5.mem a = st.mem a) ∧ cB ≤ 16 := by
        by_cases hm : tag = 1 ∧ e_i = delE
        · have hisM1 : isMatch = 1 := by simp [isMatch, hm.1, hm.2]
          have hD' : prefD (i + 1) = prefD i := by
            dsimp only [prefD]
            rw [htake_succ, List.map_append, List.map_singleton, List.filter_append]
            simp only [hm.1, ↓reduceIte, List.filter_cons, List.filter_nil, e_i, hm.2, ne_eq,
              not_true_eq_false, decide_false, Bool.false_eq_true, List.append_nil]
          have hH' : prefH (i + 1) = 1 := by
            dsimp only [prefH]
            rw [htake_succ, List.map_append, List.map_singleton]
            simp only [hm.1, List.mem_append, List.mem_singleton, e_i, hm.2, or_true, and_self, ↓reduceIte]
          let s5 : State := { s4 with regs := Function.update s4.regs 19 1 }
          have h5 : Runs w p ω (.assign 19 (.const 1)) s4 .normal s5 2 :=
            runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
          refine ⟨s5, 4, runs_cond_iff.mpr ⟨1, 2, by simp [s4, Expr.eval, hisM1],
            by simp only [one_ne_zero, ↓reduceIte]; exact h5, by simp [Expr.size]⟩,
            fun r hr => by simp [s5, s4, s3, s2, s1, show r ≠ 19 by omega, show r ≠ 21 by omega,
              show r ≠ 22 by omega, show r ≠ 23 by omega, hr_o r hr],
            by simp [s5, s4, s3, s2, s1, hr18s, hD'], by simp [s5, hH'],
            by simp [s5, s4, s3, s2, s1, hr20s],
            by rw [hD']; intro q hq; dsimp only [s5, s4, s3, s2, s1]
               rw [Function.update_of_ne (by omega)]; exact hLA q hq,
            fun v hv => hIs_s2 v hv,
            fun a ha1 ha2 => by
              dsimp only [s5, s4, s3, s2, s1]; rw [Function.update_of_ne (by omega)]
              exact hfr a ha1 (hD' ▸ ha2), by omega⟩
        · have hisM0 : isMatch = 0 := by
            by_cases ht : tag = 1
            · have hne : e_i ≠ delE := fun h => hm ⟨ht, h⟩
              simp [isMatch, ht, hne]
            · simp [isMatch, ht]
          have hD' : prefD (i + 1) = prefD i ++ [e_i] := by
            dsimp only [prefD]
            rw [htake_succ, List.map_append, List.map_singleton]
            by_cases ht : tag = 1
            · have hne : e_i ≠ delE := fun h => hm ⟨ht, h⟩
              simp only [ht, ↓reduceIte, List.filter_append, List.filter_cons, List.filter_nil,
                e_i, ne_eq, hne, not_false_eq_true, decide_true]
            · simp only [ht, ↓reduceIte, e_i]
          have hH' : prefH (i + 1) = prefH i := by
            dsimp only [prefH]
            rw [htake_succ, List.map_append, List.map_singleton]
            by_cases ht : tag = 1
            · have hne : e_i ≠ delE := fun h => hm ⟨ht, h⟩
              simp only [ht, true_and, List.mem_append, List.mem_singleton, e_i, Ne.symm hne, or_false]
            · simp only [ht, false_and, ↓reduceIte]
          let s4a : State := { s4 with mem := Function.update s4.mem (dBuf + (prefD i).length) e_i }
          let s5 : State := { s4a with regs := Function.update s4a.regs 18 ((prefD i).length + 1) }
          have ha : Runs w p ω (.store (.bin .add (.reg 15) (.reg 18)) (.reg 22)) s4 .normal s4a 5 :=
            runs_store_iff.mpr ⟨dBuf + (prefD i).length, e_i,
              by simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr_o 15 (by omega), hr15, hr18s,
                show dBuf + (prefD i).length < 2 ^ w by omega],
              by simp [s4, s3, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
          have hb : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.const 1))) s4a .normal s5 4 :=
            runs_assign_iff.mpr ⟨(prefD i).length + 1,
              by simp [s4a, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr18s, hw1, show (prefD i).length + 1 < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have hseq := runs_seq_iff.mpr (Or.inr ⟨s4a, 5, 4, ha, hb, rfl⟩)
          refine ⟨s5, 12, runs_cond_iff.mpr ⟨0, 10, by simp [s4, Expr.eval, hisM0],
            by simp only [↓reduceIte]; exact hseq, by simp [Expr.size]⟩,
            fun r hr => by simp [s5, s4a, s4, s3, s2, s1, show r ≠ 18 by omega, show r ≠ 21 by omega,
              show r ≠ 22 by omega, show r ≠ 23 by omega, hr_o r hr],
            by simp [s5, hD'], by simp [s5, s4a, s4, s3, s2, s1, hr19s, hH'],
            by simp [s5, s4a, s4, s3, s2, s1, hr20s],
            by rw [hD']; intro q hq
               simp only [List.length_append, List.length_singleton] at hq
               dsimp only [s5, s4a, s4, s3, s2, s1]
               by_cases hql : q = (prefD i).length
               · subst hql; simp
               · have hqlt : q < (prefD i).length := by omega
                 rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hLA q hqlt]
                 exact (List.getElem_append_left hqlt).symm,
            fun v hv => by
              dsimp only [s5, s4a, s4, s3]
              rw [Function.update_of_ne (by omega)]
              exact hIs_s2 v hv,
            fun a ha1 ha2 => by
              simp only [hD', List.length_append, List.length_singleton] at ha2
              dsimp only [s5, s4a, s4, s3, s2, s1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hfr a ha1 (by omega), by omega⟩
      obtain ⟨s5, cB, hB, hr5_o, hr5_18, hr5_19, hr5_20, hLA5, hIs5, hfr5, hcB⟩ := hbranch
      let s6 : State := { s5 with regs := Function.update s5.regs 20 (oldC + (i + 1)) }
      have hs6 : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1))) s5 .normal s6 4 :=
        runs_assign_iff.mpr ⟨oldC + (i + 1), by
          simp [Expr.eval, BinOp.eval, hr5_20, hw1, show oldC + i + 1 < 2 ^ w by omega]; omega,
          rfl, rfl, by simp [Expr.size]⟩
      have t5 := runs_seq_iff.mpr (Or.inr ⟨s5, cB, 4, hB, hs6, rfl⟩)
      have t4 := runs_seq_iff.mpr (Or.inr ⟨s4, 8, _, hs4, t5, rfl⟩)
      have t3 := runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, hs3, t4, rfl⟩)
      have t2 := runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hs2, t3, rfl⟩)
      have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hs1, t2, rfl⟩)
      obtain ⟨st', cRest, hrest, hr'_o, hr'_18, hr'_19, hLA', hIs', hfr', hcRest⟩ :=
        ih (i + 1) s6 (by omega) (by omega)
          (fun r hr => by simp [s6, show r ≠ 20 by omega, hr5_o r hr])
          (by simp [s6, hr5_18]) (by simp [s6, hr5_19]) (by simp [s6]) hLA5 hIs5 hfr5
      have hfull : Runs w p ω compScanCutsStmt s .normal st' _ :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s6, _, cRest,
          by simp [Expr.eval, BinOp.eval, hr20s, hr_o 5 (by omega), hr5, hw0, show oldC + i < oldC + cuts1.length by omega],
          by decide, hbody, hrest, by simp [Expr.size]; rfl⟩))
      exact ⟨st', _, hfull, hr'_o, hr'_18, hr'_19, hLA', hIs', hfr', by omega⟩
  obtain ⟨st', c, hrun, hr_o, hr18', hr19', hLA', hIs', hfr', hc⟩ :=
    hloop cuts1.length 0 st (Nat.zero_le _) (Nat.sub_zero _) (fun _ _ => rfl)
      (by simp [prefD, hr18]) (by simp [prefH, hr19]) (by simpa using hr20)
      (by intro q hq; simp [prefD] at hq) (fun v _ => by simp) (fun _ _ _ => rfl)
  exact ⟨st', c, hrun, hr_o, hr18', hr19', hLA', hIs', hfr', by omega⟩

/-- Verification of `compUnmarkIsNewStmt`: clears `ufBase + r` to `0` for every `r ∈ cuts1.map Prod.snd`,
preserving all other memory, in `≤ 25 * cuts1.length + 10` steps. -/
theorem compUnmarkIsNew_runs {w rootsPtr oldC ufBase vCap : ℕ}
    {cuts1 : List (ℕ × ℕ)} {p : Program} {ω : ℕ → Bool} {st : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hrts_w : rootsPtr + oldC + cuts1.length < 2 ^ w)
    (huf_w : ufBase + vCap < 2 ^ w)
    (hdisj : rootsPtr + oldC + cuts1.length ≤ ufBase ∨ ufBase + vCap ≤ rootsPtr + oldC)
    (hcut_r : ∀ p ∈ cuts1, p.2 < vCap)
    (hcut_m : ∀ i (hi : i < cuts1.length), st.mem (rootsPtr + (oldC + i)) = cuts1[i].2)
    (hr2 : st.regs 2 = rootsPtr) (hr5 : st.regs 5 = oldC + cuts1.length)
    (hr12 : st.regs 12 = ufBase) (hr20 : st.regs 20 = oldC) :
    ∃ st' c,
      Runs w p ω compUnmarkIsNewStmt st .normal st' c ∧
      (∀ r < 20, st'.regs r = st.regs r) ∧
      (∀ r ∈ cuts1.map Prod.snd, st'.mem (ufBase + r) = 0) ∧
      (∀ a, (∀ r ∈ cuts1.map Prod.snd, a ≠ ufBase + r) → st'.mem a = st.mem a) ∧
      c ≤ 25 * cuts1.length + 10 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hloop : ∀ rem i (s : State) (hi : i ≤ cuts1.length), cuts1.length - i = rem →
      (∀ r < 20, s.regs r = st.regs r) → s.regs 20 = oldC + i →
      (∀ j (hj : j < i), s.mem (ufBase + cuts1[j].2) = 0) →
      (∀ a, (∀ j (hj : j < i), a ≠ ufBase + cuts1[j].2) → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω compUnmarkIsNewStmt s .normal st' c ∧
        (∀ r < 20, st'.regs r = st.regs r) ∧
        (∀ j (hj : j < cuts1.length), st'.mem (ufBase + cuts1[j].2) = 0) ∧
        (∀ a, (∀ j (hj : j < cuts1.length), a ≠ ufBase + cuts1[j].2) → st'.mem a = st.mem a) ∧
        c ≤ 25 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hr_o hr20s hz hfr
      have hi_eq : i = cuts1.length := by omega
      subst hi_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr20s, hr_o 5 (by omega), hr5],
        rfl, rfl, by simp [Expr.size]⟩), hr_o, hz, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hr_o hr20s hz hfr
      have hi_lt : i < cuts1.length := by omega
      set r_i := cuts1[i].2
      have hri_lt : r_i < vCap := hcut_r cuts1[i] (List.getElem_mem hi_lt)
      have hs_r : s.mem (rootsPtr + (oldC + i)) = r_i := by
        rw [hfr _ fun j hj => by
          have := hcut_r cuts1[j] (List.getElem_mem (show j < cuts1.length by omega))
          rcases hdisj with h | h <;> omega]
        exact hcut_m i hi_lt
      let s1 : State := { s with regs := Function.update s.regs 21 r_i }
      let s2 : State := { s1 with mem := Function.update s1.mem (ufBase + r_i) 0 }
      let s3 : State := { s2 with regs := Function.update s2.regs 20 (oldC + (i + 1)) }
      have h1 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 2) (.reg 20)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨r_i, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_o 2 (by omega), hr2, hr20s, show rootsPtr + (oldC + i) < 2 ^ w by omega])
          hs_r, rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.store (.bin .add (.reg 12) (.reg 21)) (.const 0)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨ufBase + r_i, 0,
          by simp [s1, Expr.eval, BinOp.eval, hr_o 12 (by omega), hr12, show ufBase + r_i < 2 ^ w by omega],
          by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have h3 : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨oldC + (i + 1), by
          simp [s2, s1, Expr.eval, BinOp.eval, hr20s, hw1, show oldC + i + 1 < 2 ^ w by omega]; omega,
          rfl, rfl, by simp [Expr.size]⟩
      have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, h1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, 4, h2, h3, rfl⟩), rfl⟩)
      obtain ⟨st', cRest, hrest, hr', hz', hfr', hcRest⟩ :=
        ih (i + 1) s3 (by omega) (by omega)
          (fun r hr => by simp [s3, s2, s1, show r ≠ 20 by omega, show r ≠ 21 by omega, hr_o r hr])
          (by simp [s3])
          (fun j hj => by
            dsimp only [s3, s2, s1]
            by_cases hji : j = i
            · subst hji; simp [r_i]
            · by_cases heq : ufBase + cuts1[j].2 = ufBase + r_i
              · rw [heq, Function.update_self]
              · rw [Function.update_of_ne heq]; exact hz j (by omega))
          (fun a ha => by
            dsimp only [s3, s2, s1]
            rw [Function.update_of_ne (show a ≠ ufBase + r_i from ha i (by omega))]
            exact hfr a fun j hj => ha j (by omega))
      have hfull : Runs w p ω compUnmarkIsNewStmt s .normal st' _ :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, _, cRest,
          by simp [Expr.eval, BinOp.eval, hr20s, hr_o 5 (by omega), hr5, hw0, show oldC + i < oldC + cuts1.length by omega],
          by decide, hbody, hrest, by simp [Expr.size]; rfl⟩))
      exact ⟨st', _, hfull, hr', hz', hfr', by omega⟩
  obtain ⟨st', c, hrun, hr', hz', hfr', hc⟩ :=
    hloop cuts1.length 0 st (Nat.zero_le _) (Nat.sub_zero _) (fun _ _ => rfl) (by simpa using hr20)
      (fun _ h => by omega) (fun _ _ => rfl)
  refine ⟨st', c, hrun, hr', fun r hr => ?_, fun a ha => hfr' a fun j hj =>
    ha _ (List.mem_map.mpr ⟨cuts1[j], List.getElem_mem hj, rfl⟩), by omega⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  exact hz' j hj

end

end MinCostFlow.SparseCore.Program
