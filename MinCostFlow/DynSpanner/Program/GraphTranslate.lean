module

public import MinCostFlow.DynSpanner.Program.GraphTranslateProcs
public import MinCostFlow.DynSpanner.Program.MergeSort
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Program.EmbLayouts
public import MinCostFlow.Spanner.MGraphTranslate
public import MinCostFlow.Spanner.Layouts

import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Log

/-!
# Primitives for `MGraph` ↔ `Cited.Graph` Translation (`GraphTranslate`)

Implements and verifies the deterministic Word-RAM primitives needed to translate dynamic
multigraphs and embeddings (`DynGraphAt`, `MEmbAt`) to and from the canonical `Cited.Graph`
layouts (`GraphAt`, `WalkAt`, `EmbAt`) used by `Sparsify`:

* `binSearchOptContract` / `binSearchOpt_meetsContract`: generalizes `SortOps.binSearchStmt`
  to arbitrary `key < 2 ^ w` without assuming `key ∈ L`.
* `vertsOf` / `sortedDedup` / `sortedDiff` pure equivalence lemmas connecting sorted-deduped
  and two-pointer-differenced arrays to `Spanner.vertsOf`, `usedHEdges`, `hEdges`, and `hVerts`.
* `gtSortDedupStmt` (`gtIdxSortDedup = 0`): in-place merge sort + deduplication into `vertsOf X`.
* `gtSortedDiffStmt` (`gtIdxSortedDiff = 1`): linear-time two-pointer difference of strictly
  increasing arrays into `vertsOf (U \ J)`.
* `gtLookupHVertStmt` (`gtIdxLookupHVert = 2`): index lookup `(jVs ++ extraVs).idxOf z` in
  `O(log(|hVerts| + 1) + 1)` time.
* `gtCollectRawEsStmt` (`gtIdxCollectRawEs = 3`) & `gtCollectRawVsStmt` (`gtIdxCollectRawVs = 4`)
  (verified in `GraphTranslateCollect.lean`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

theorem gtSortedDiff_meetsContract {w : ℕ} {p : Program} {b bSort bOps : ℕ}
    {us js : List ℕ} {U J : Finset ℕ}
    (hp : p.HasAt b (gtProcs bSort bOps)) :
    MeetsContract w p (b + gtIdxSortedDiff) (gtSortedDiffContract w us js U J) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxSortedDiff) (by simp [gtProcs, gtIdxSortedDiff]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨aU, aJ, dst, rfl, hw16, haUB, haJB, hdstB, hdisjU, hdisjJ,
    husPair, hjsPair, huMem, hjMem, hUat, hJat, hUw, hJw⟩
  have hlt_aU : aU < 2 ^ w := hargs aU (by simp)
  have hlt_nU : us.length < 2 ^ w := hargs us.length (by simp)
  have hlt_aJ : aJ < 2 ^ w := hargs aJ (by simp)
  have hlt_nJ : js.length < 2 ^ w := hargs js.length (by simp)
  have hlt_dst : dst < 2 ^ w := hargs dst (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have hsd_eq : sortedDiff us js = vertsOf (U \ J) :=
    sortedDiff_eq_vertsOf_sdiff husPair hjsPair huMem hjMem
  have hsd_len : (sortedDiff us js).length ≤ us.length := sortedDiff_length_le us js
  refine runs_start_le ?_
  dsimp only [gtProcs, gtIdxSortedDiff, List.getElem_cons_succ, List.getElem_cons_zero,
    gtSortedDiffStmt]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  let Inv : State → Prop := fun st =>
    ∃ (i k : ℕ) (acc : List ℕ),
      i ≤ us.length ∧ k ≤ js.length ∧
      acc.length ≤ i ∧ acc ++ sortedDiff (us.drop i) (js.drop k) = sortedDiff us js ∧
      st.regs 0 = aU ∧ st.regs 1 = us.length ∧ st.regs 2 = aJ ∧ st.regs 3 = js.length ∧
      st.regs 4 = dst ∧ st.regs 5 = i ∧ st.regs 6 = k ∧ st.regs 7 = acc.length ∧
      ListAt st.mem dst acc ∧
      (∀ t < us.length, st.mem (aU + t) = mem (aU + t)) ∧
      (∀ t < js.length, st.mem (aJ + t) = mem (aJ + t)) ∧
      (∀ addr, addr < dst ∨ dst + acc.length ≤ addr → st.mem addr = mem addr)
  let condExpr : Expr := .bin .lt (.reg 5) (.reg 1)
  let bodyStmt : Stmt :=
    .cond (.bin .lt (.reg 6) (.reg 3))
      (.assign 8 (.load (.bin .add (.reg 0) (.reg 5))) ;;
       .assign 9 (.load (.bin .add (.reg 2) (.reg 6))) ;;
       .cond (.bin .lt (.reg 8) (.reg 9))
         (.store (.bin .add (.reg 4) (.reg 7)) (.reg 8) ;;
          .assign 7 (.bin .add (.reg 7) (.const 1)) ;;
          .assign 5 (.bin .add (.reg 5) (.const 1)))
         (.cond (.bin .lt (.reg 9) (.reg 8))
            (.assign 6 (.bin .add (.reg 6) (.const 1)))
            (.assign 5 (.bin .add (.reg 5) (.const 1)) ;;
             .assign 6 (.bin .add (.reg 6) (.const 1)))))
      (.assign 8 (.load (.bin .add (.reg 0) (.reg 5))) ;;
       .store (.bin .add (.reg 4) (.reg 7)) (.reg 8) ;;
       .assign 7 (.bin .add (.reg 7) (.const 1)) ;;
       .assign 5 (.bin .add (.reg 5) (.const 1)))
  let mFn : State → ℕ := fun st => (us.length - st.regs 5) + (js.length - st.regs 6)
  let remFn : State → ℕ := fun st => 50 * ((us.length - st.regs 5) + (js.length - st.regs 6)) + 10
  let condFn : State → ℕ := fun st => if st.regs 5 < us.length then 1 else 0
  have hloop : Triple w p Inv (.loop condExpr bodyStmt)
      (normalPost fun st =>
        st.regs 7 = (vertsOf (U \ J)).length ∧
        ListAt st.mem dst (vertsOf (U \ J)) ∧
        ∀ addr, addr < dst ∨ dst + (vertsOf (U \ J)).length ≤ addr → st.mem addr = mem addr) remFn := by
    refine Triple.loop_measure (condVal := condFn) (m := mFn) (rem := remFn)
      (fun st hInv => by
        rcases hInv with ⟨i, k, acc, hi, hk, hlen, heq, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7,
          hacc, hUeq, hJeq, hfr⟩
        dsimp only [condExpr, condFn]
        rw [hr5]
        split_ifs with hlt <;> simp [Expr.eval, BinOp.eval, hr1, hr5, hlt, h0_lt, h1_lt])
      (fun st hInv hv => by
        rcases hInv with ⟨i, k, acc, hi, hk, hlen, hacc_eq, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7,
          hacc, hUeq, hJeq, hfr⟩
        dsimp only [condFn] at hv
        have hi_eq : i = us.length := by
          rw [hr5] at hv; by_contra hc; simp [show i < us.length by omega] at hv
        subst hi_eq
        simp only [List.drop_length, sortedDiff_nil_left, List.append_nil] at hacc_eq
        rw [hsd_eq] at hacc_eq
        subst acc
        refine ⟨⟨hr7, hacc, hfr⟩, by dsimp only [condExpr, Expr.size, remFn]; omega⟩)
      (fun st hInv hv => by
        rcases hInv with ⟨i, k, acc, hi_le, hk_le, hacc_len, hacc_eq,
          hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hacc, hUeq, hJeq, hfr⟩
        dsimp only [condFn] at hv
        have hi_lt : i < us.length := by rw [hr5] at hv; by_contra hc; simp [hc] at hv
        have hi_ltw : i < 2 ^ w := by omega
        have hk_ltw : k < 2 ^ w := by omega
        have haUi_lt : aU + i < 2 ^ w := by omega
        have hu_mem : st.mem (aU + i) = us[i] := by rw [hUeq i hi_lt]; exact hUat i hi_lt
        have hu_ltw : us[i] < 2 ^ w := hUw _ (List.getElem_mem hi_lt)
        have hdst_acc_lt : dst + acc.length < 2 ^ w := by omega
        have hi1_ltw : i + 1 < 2 ^ w := by omega
        have hacc1_ltw : acc.length + 1 < 2 ^ w := by omega
        have hdropU : us.drop i = us[i] :: us.drop (i + 1) := List.drop_eq_getElem_cons hi_lt
        refine ⟨42, ?_⟩
        intro s ω' hs_eq
        subst s
        suffices h : ∃ o s' c, Runs w p ω' bodyStmt st o s' c ∧
            (match o with
              | .returned u => normalPost (fun st => st.regs 7 = (vertsOf (U \ J)).length ∧
                  ListAt st.mem dst (vertsOf (U \ J)) ∧
                  ∀ addr, addr < dst ∨ dst + (vertsOf (U \ J)).length ≤ addr → st.mem addr = mem addr)
                  (.returned u) s' ∧ condExpr.size + 42 + 1 ≤ remFn st
              | .normal => Inv s' ∧ mFn s' < mFn st ∧ condExpr.size + 42 + remFn s' + 1 ≤ remFn st) ∧
            0 + c ≤ 42 by
          rcases h with ⟨o, s', c, hr, hq, hc⟩
          exact ⟨o, s', c, hr, hq, by simpa using hc⟩
        dsimp only [bodyStmt]
        by_cases hk_lt : k < js.length
        · have haJk_lt : aJ + k < 2 ^ w := by omega
          have hv_mem : st.mem (aJ + k) = js[k] := by rw [hJeq k hk_lt]; exact hJat k hk_lt
          have hv_ltw : js[k] < 2 ^ w := hJw _ (List.getElem_mem hk_lt)
          have hk1_ltw : k + 1 < 2 ^ w := by omega
          have hdropJ : js.drop k = js[k] :: js.drop (k + 1) := List.drop_eq_getElem_cons hk_lt
          refine runs_cond_le_gt (v := 1)
            (by simp [Expr.eval, BinOp.eval, hr3, hr6, hk_lt, h1_lt]) ?_ ?_
          · intro _
            refine runs_seq_assign_le
              (Expr.eval_load_of_eq (v := us[i]) (by simp [Expr.eval, BinOp.eval, hr0, hr5, haUi_lt]) hu_mem) ?_
            refine runs_seq_assign_le
              (Expr.eval_load_of_eq (v := js[k])
                (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hr6, haJk_lt]) hv_mem) ?_
            by_cases huv : us[i] < js[k]
            · refine runs_cond_le_gt (v := 1)
                (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, huv, h1_lt]) ?_ ?_
              · intro _
                refine runs_seq_store_le (x := dst + acc.length) (v := us[i])
                  (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr4, hr7, hdst_acc_lt])
                  (by eval_expr) ?_
                refine runs_seq_assign_le (v := acc.length + 1)
                  (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr7, h1_lt, hacc1_ltw]) ?_
                refine runs_assign_le (v := i + 1)
                  (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr5, h1_lt, hi1_ltw]) ?_
                  (by dsimp only [Expr.size]; omega)
                refine ⟨⟨i + 1, k, acc ++ [us[i]], hi_lt, hk_le, by simp; omega, ?_,
                  by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
                  by simp, by simp [hr6], by simp, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
                · rw [hdropU, hdropJ, sortedDiff_cons_lt huv] at hacc_eq
                  simpa [← hdropJ, List.append_assoc] using hacc_eq
                · simpa using listAt_append.mpr ⟨ListAt.update_ge hacc (le_refl _),
                    fun t ht => by simp at ht; subst t; simp⟩
                · intro t ht
                  dsimp only
                  rw [Function.update_of_ne (by rcases hdisjU t ht with h | h <;> omega)]
                  exact hUeq t ht
                · intro t ht
                  dsimp only
                  rw [Function.update_of_ne (by rcases hdisjJ t ht with h | h <;> omega)]
                  exact hJeq t ht
                · intro addr had
                  have hne : addr ≠ dst + acc.length := by simp at had; omega
                  dsimp only
                  rw [Function.update_of_ne hne]
                  exact hfr addr (by
                    simp only [List.length_append, List.length_cons, List.length_nil] at had
                    omega)
                · dsimp only [mFn]; simp [hr5, hr6]; omega
                · dsimp only [condExpr, Expr.size, remFn]; simp [hr5, hr6]; omega
              · intro hc; cases hc
            · refine runs_cond_le_gt (v := 0)
                (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, huv, h0_lt]) ?_ ?_
              · intro hc; exact absurd rfl hc
              · intro _
                by_cases hvu : js[k] < us[i]
                · refine runs_cond_le_gt (v := 1)
                    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hvu, h1_lt]) ?_ ?_
                  · intro _
                    refine runs_assign_le (v := k + 1)
                      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr6, h1_lt, hk1_ltw]) ?_
                      (by dsimp only [Expr.size]; omega)
                    refine ⟨⟨i, k + 1, acc, hi_le, hk_lt, hacc_len, ?_,
                      by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
                      by simp [hr5], by simp, by simp [hr7], hacc, hUeq, hJeq, hfr⟩, ?_, ?_⟩
                    · rw [hdropU, hdropJ, sortedDiff_cons_gt hvu] at hacc_eq
                      simpa [← hdropU] using hacc_eq
                    · dsimp only [mFn]; simp [hr5, hr6]; omega
                    · dsimp only [condExpr, Expr.size, remFn]; simp [hr5, hr6]; omega
                  · intro hc; cases hc
                · have heq : us[i] = js[k] := Nat.le_antisymm (Nat.le_of_not_lt hvu) (Nat.le_of_not_lt huv)
                  refine runs_cond_le_gt (v := 0)
                    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hvu, h0_lt]) ?_ ?_
                  · intro hc; exact absurd rfl hc
                  · intro _
                    refine runs_seq_assign_le (v := i + 1)
                      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr5, h1_lt, hi1_ltw]) ?_
                    refine runs_assign_le (v := k + 1)
                      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr6, h1_lt, hk1_ltw]) ?_
                      (by dsimp only [Expr.size]; omega)
                    refine ⟨⟨i + 1, k + 1, acc, hi_lt, hk_lt, by omega, ?_,
                      by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
                      by simp, by simp, by simp [hr7], hacc, hUeq, hJeq, hfr⟩, ?_, ?_⟩
                    · rw [hdropU, hdropJ, heq, sortedDiff_cons_eq] at hacc_eq
                      exact hacc_eq
                    · dsimp only [mFn]; simp [hr5, hr6]; omega
                    · dsimp only [condExpr, Expr.size, remFn]; simp [hr5, hr6]; omega
          · intro hc; cases hc
        · have hk_eq : k = js.length := by omega
          refine runs_cond_le_gt (v := 0)
            (by simp [Expr.eval, BinOp.eval, hr3, hr6, hk_lt, h0_lt]) ?_ ?_
          · intro hc; exact absurd rfl hc
          · intro _
            refine runs_seq_assign_le
              (Expr.eval_load_of_eq (v := us[i]) (by simp [Expr.eval, BinOp.eval, hr0, hr5, haUi_lt]) hu_mem) ?_
            refine runs_seq_store_le (x := dst + acc.length) (v := us[i])
              (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr4, hr7, hdst_acc_lt])
              (by eval_expr) ?_
            refine runs_seq_assign_le (v := acc.length + 1)
              (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr7, h1_lt, hacc1_ltw]) ?_
            refine runs_assign_le (v := i + 1)
              (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr5, h1_lt, hi1_ltw]) ?_
              (by dsimp only [Expr.size]; omega)
            refine ⟨⟨i + 1, k, acc ++ [us[i]], hi_lt, hk_le, by simp; omega, ?_,
              by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
              by simp, by simp [hr6], by simp, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
            · have hjnil : js.drop k = [] := List.drop_of_length_le (by omega)
              rw [hjnil, hdropU, sortedDiff_nil_right] at hacc_eq
              simpa [hjnil, sortedDiff_nil_right, List.append_assoc] using hacc_eq
            · simpa using listAt_append.mpr ⟨ListAt.update_ge hacc (le_refl _),
                fun t ht => by simp at ht; subst t; simp⟩
            · intro t ht
              dsimp only
              rw [Function.update_of_ne (by rcases hdisjU t ht with h | h <;> omega)]
              exact hUeq t ht
            · intro t ht
              dsimp only
              rw [Function.update_of_ne (by rcases hdisjJ t ht with h | h <;> omega)]
              exact hJeq t ht
            · intro addr had
              have hne : addr ≠ dst + acc.length := by simp at had; omega
              dsimp only
              rw [Function.update_of_ne hne]
              exact hfr addr (by
                simp only [List.length_append, List.length_cons, List.length_nil] at had
                omega)
            · dsimp only [mFn]; simp [hr5, hr6]; omega
            · dsimp only [condExpr, Expr.size, remFn]; simp [hr5, hr6]; omega)
  refine runs_seq_triple_le hloop
    ⟨0, 0, [], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl,
     by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], listAt_nil _ _,
     fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ ?_
  intro st' ⟨h7, hUat', hfr'⟩
  refine runs_ret_le (by eval_expr) ⟨aU, aJ, dst, rfl, h7, hUat', hfr'⟩ ?_
  dsimp only [gtSortedDiffContract, remFn, Expr.size]
  simp only [startState, Function.update_self, Function.update_of_ne (by decide : (5 : ℕ) ≠ 6),
    Function.update_of_ne (by decide : (5 : ℕ) ≠ 7),
    Function.update_of_ne (by decide : (6 : ℕ) ≠ 7), Nat.sub_zero]
  omega

theorem gtLookupHVert_meetsContract {w : ℕ} {p : Program} {b bSort bOps : ℕ}
    {jVs exVs : List ℕ} {key : ℕ}
    (hp : p.HasAt b (gtProcs bSort bOps)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (b + gtIdxLookupHVert) (gtLookupHVertContract w jVs exVs key) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxLookupHVert) (by simp [gtProcs, gtIdxLookupHVert]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨jVsPtr, exVsPtr, rfl, hw16, hjB, hexB, hkey_lt, htot_lt,
    hjPair, hexPair, hdisj, hkey_mem, hjAt, hexAt, hjw, hexw⟩
  have hlt_jP : jVsPtr < 2 ^ w := hargs jVsPtr (by simp)
  have hlt_nJ : jVs.length < 2 ^ w := hargs jVs.length (by simp)
  have hlt_exP : exVsPtr < 2 ^ w := hargs exVsPtr (by simp)
  have hlt_nEx : exVs.length < 2 ^ w := hargs exVs.length (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have hidx_lt_sum : (jVs ++ exVs).idxOf key < jVs.length + exVs.length := by
    rw [← List.length_append]
    exact List.idxOf_lt_length_iff.mpr hkey_mem
  have hwords1 : ∀ v ∈ [jVsPtr, jVs.length, key], v < 2 ^ w := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_jP
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
    rcases List.mem_cons.mp hv with rfl | hv; · exact hkey_lt
    cases hv
  have hwords2 : ∀ v ∈ [exVsPtr, exVs.length, key], v < 2 ^ w := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_exP
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nEx
    rcases List.mem_cons.mp hv with rfl | hv; · exact hkey_lt
    cases hv
  refine runs_start_le ?_
  dsimp only [gtProcs, gtIdxLookupHVert, List.getElem_cons_succ, List.getElem_cons_zero,
    gtLookupHVertStmt]
  by_cases hjpos : 0 < jVs.length
  · refine runs_cond_le_gt (v := 1) (by simp [Expr.eval, BinOp.eval, startState, hjpos, h1_lt]) ?_ ?_
    · intro _
      have hpre_opt : (binSearchOptContract w jVs key).pre [jVsPtr, jVs.length, key] mem :=
        ⟨jVsPtr, rfl, hw16, hjB, hkey_lt, hjPair, hjAt, hjw⟩
      refine runs_seq_call_le (binSearchOpt_meetsContract hpSort) (by eval_expr)
        hwords1 hpre_opt ?_
      rintro ret1 mem1 _ ⟨_, _, hmem1, _, hpos1⟩
      subst mem1
      obtain ⟨hret_lt, hiff, hidx1⟩ := hpos1 hjpos
      have haddr_lt : jVsPtr + ret1 < 2 ^ w := by omega
      have hval_lt : jVs[ret1] < 2 ^ w := hjw _ (List.getElem_mem hret_lt)
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (v := jVs[ret1])
          (by simp [Expr.eval, BinOp.eval, startState, Function.update_of_ne, haddr_lt])
          (hjAt ret1 hret_lt)) ?_
      by_cases heq : jVs[ret1] = key
      · have hkm : key ∈ jVs := hiff.mpr (by rw [List.getElem?_eq_getElem hret_lt, heq])
        have hidx_eq : (jVs ++ exVs).idxOf key = ret1 := by
          rw [List.idxOf_append_of_mem hkm, hidx1 hkm]
        refine runs_cond_le_gt (v := 1)
          (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, startState, heq, h1_lt]) ?_ ?_
        · intro _
          refine runs_ret_le (v := ret1) (by simp [Expr.eval, Function.update_of_ne])
            ⟨jVsPtr, exVsPtr, rfl, rfl,
              by dsimp only [Outcome.value]; exact hidx_eq.symm,
              by dsimp only [Outcome.value]; omega⟩ ?_
          dsimp only [gtLookupHVertContract, binSearchOptContract, argsSize, Expr.size]
          have hlog : Nat.log 2 (jVs.length + 1) ≤ Nat.log 2 (jVs.length + exVs.length + 1) :=
            Nat.log_mono_right (by omega)
          omega
        · intro hc; cases hc
      · have hk_nmem : key ∉ jVs := fun hm => by
          have hget := hiff.mp hm
          rw [List.getElem?_eq_getElem hret_lt, Option.some.injEq] at hget
          exact heq hget
        have hk_ex : key ∈ exVs := by
          rcases List.mem_append.mp hkey_mem with h | h
          · exact absurd h hk_nmem
          · exact h
        have hidx_eq : (jVs ++ exVs).idxOf key = jVs.length + exVs.idxOf key :=
          List.idxOf_append_of_notMem hk_nmem
        refine runs_cond_le_gt (v := 0)
          (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, startState, heq, h0_lt]) ?_ ?_
        · intro hc; exact absurd rfl hc
        · intro _
          have hpre2 : (binSearchContract w exVs key).pre [exVsPtr, exVs.length, key] mem :=
            ⟨exVsPtr, rfl, hw16, hexB, hexPair, hk_ex, hexAt, hexw⟩
          refine runs_seq_call_le (binSearch_meetsContract hpSort)
            (by simp [evalArgs, Expr.eval, Function.update_of_ne, startState])
            hwords2 hpre2 ?_
          rintro ret2 mem2 _ ⟨_, _, hmem2, hret2, hret2_lt⟩
          subst mem2
          have hsum_lt : jVs.length + ret2 < 2 ^ w := by omega
          refine runs_ret_le (v := jVs.length + ret2)
            (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, startState, hsum_lt])
            ⟨jVsPtr, exVsPtr, rfl, rfl,
              by dsimp only [Outcome.value]; rw [hidx_eq, hret2],
              by dsimp only [Outcome.value]; omega⟩ ?_
          dsimp only [gtLookupHVertContract, binSearchOptContract, binSearchContract, argsSize, Expr.size]
          have hlog1 : Nat.log 2 (jVs.length + 1) ≤ Nat.log 2 (jVs.length + exVs.length + 1) :=
            Nat.log_mono_right (by omega)
          have hlog2 : Nat.log 2 (exVs.length + 1) ≤ Nat.log 2 (jVs.length + exVs.length + 1) :=
            Nat.log_mono_right (by omega)
          omega
    · intro hc; cases hc
  · have hj0 : jVs = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    have hk_ex : key ∈ exVs := by simpa [hj0] using hkey_mem
    refine runs_cond_le_gt (v := 0) (by simp [Expr.eval, BinOp.eval, startState, hjpos, h0_lt]) ?_ ?_
    · intro hc; exact absurd rfl hc
    · intro _
      have hpre2 : (binSearchContract w exVs key).pre [exVsPtr, exVs.length, key] mem :=
        ⟨exVsPtr, rfl, hw16, hexB, hexPair, hk_ex, hexAt, hexw⟩
      refine runs_seq_call_le (binSearch_meetsContract hpSort) (by eval_expr)
        hwords2 hpre2 ?_
      rintro ret2 mem2 _ ⟨_, _, hmem2, hret2, hret2_lt⟩
      subst mem2
      refine runs_ret_le (v := ret2) (by simp [Expr.eval])
        ⟨jVsPtr, exVsPtr, rfl, rfl,
          by dsimp only [Outcome.value]; rw [hj0, List.nil_append, hret2],
          by dsimp only [Outcome.value]; omega⟩ ?_
      dsimp only [gtLookupHVertContract, binSearchContract, argsSize, Expr.size]
      have hlog2 : Nat.log 2 (exVs.length + 1) ≤ Nat.log 2 (jVs.length + exVs.length + 1) :=
        Nat.log_mono_right (by omega)
      omega

end

end MinCostFlow.DynSpanner.Program
