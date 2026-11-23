module

public import MinCostFlow.HierPaths.BuildRouterBridgeOutA
import Mathlib.Tactic.Linarith

/-!
# Output packing section 1 of the static router bridge (`BuildRouterBridgeOutSec1`)

Emits section 1 (the CSR of per-pair matchings `Ms`) at `resBuf + 5`, setting `r25 = sec1.length`
and `r26 = resBuf + 5 + sec1.length`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

def bridgeEmitSec1Init : Stmt :=
  .assign 20 (.const 0) ;;
  .assign 21 (.const 0) ;;
  .assign 22 (.bin .add (.reg 19) (.const 5))

def bridgeEmitSec1Body : Stmt :=
  .store (.bin .add (.reg 22) (.reg 20)) (.reg 21) ;;
  .assign 23 (.load (.bin .add (.reg 18) (.reg 20))) ;;
  .assign 21 (.bin .add (.reg 21) (.bin .add (.reg 23) (.reg 23))) ;;
  .assign 20 (.bin .add (.reg 20) (.const 1))

def bridgeEmitSec1Tail (fCopy : ℕ) : Stmt :=
  .store (.bin .add (.reg 22) (.reg 8)) (.reg 21) ;;
  .call 24 fCopy
    [ .bin .add (.reg 12) (.const 2)
    , .bin .add (.reg 16) (.reg 16)
    , .bin .add (.bin .add (.reg 22) (.reg 8)) (.const 1) ] ;;
  .assign 25 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .add (.reg 16) (.reg 16))) ;;
  .assign 26 (.bin .add (.reg 22) (.reg 25))

/-- Emit section 1 (CSR of per-pair matchings) at `resBuf + 5`, setting `r25 = sec1.length` and
`r26 = resBuf + 5 + sec1.length`. -/
def bridgeEmitSec1Stmt (fCopy : ℕ) : Stmt :=
  bridgeEmitSec1Init ;;
  (.loop (.bin .lt (.reg 20) (.reg 8)) bridgeEmitSec1Body ;;
   bridgeEmitSec1Tail fCopy)

theorem bridgeEmitSec1Stmt_noRand (fCopy : ℕ) : (bridgeEmitSec1Stmt fCopy).NoRand := by
  simp [bridgeEmitSec1Stmt, bridgeEmitSec1Init, bridgeEmitSec1Body, bridgeEmitSec1Tail, Stmt.NoRand]

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private lemma runs_loop_zero_s1 {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_step_s1 {w c1 c2 : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st st1 st2 : State} {v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st1 c1)
    (h2 : Runs w p ω (.loop e body) st1 .normal st2 c2) :
    Runs w p ω (.loop e body) st .normal st2 (e.size + c1 + c2 + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st1, c1, c2, he, hv, h1, h2, rfl⟩))

private lemma flatMap_pair_len (es : List (ℕ × ℕ)) :
    (es.flatMap fun e => [e.1, e.2]).length = 2 * es.length := by
  induction es with
  | nil => simp
  | cons _ _ ih => simp [ih]; omega

/-- Verification of `bridgeEmitSec1Stmt`: writes the CSR of per-pair matchings `sec1` at
`resBuf + 5`, preserving memory `< resBuf + 5` and `ZeroFrom (resBuf + 5 + sec1.length)`. -/
theorem bridgeEmitSec1_runs {w fCopy outAddr resBuf : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    {Ms : List (List (ℕ × ℕ))} {k cnt : ℕ}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hMsLen : Ms.length = k)
    (hr8 : st.regs 8 = k) (hr12 : st.regs 12 = outAddr)
    (hr16 : st.regs 16 = Ms.flatten.length)
    (hr18 : st.regs 18 = cnt) (hr19 : st.regs 19 = resBuf)
    (hEdges : EdgesAt st.mem (outAddr + 2) Ms.flatten)
    (hCnt : ∀ i < k, st.mem (cnt + i) = (Ms.getD i []).length)
    (hCntEnd : cnt + k ≤ resBuf)
    (hOutEnd : outAddr + 2 + 2 * Ms.flatten.length ≤ resBuf)
    (hZ : ZeroFrom st.mem resBuf)
    (hRoom : resBuf + 5 + (k + 1 + 2 * Ms.flatten.length) + 16 < 2 ^ w) :
    let sec1 := csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])
    let sec1Addr := resBuf + 5
    ∃ st' c,
      Runs w p ω (bridgeEmitSec1Stmt fCopy) st .normal st' c ∧
      (∀ r ≤ 19, st'.regs r = st.regs r) ∧
      st'.regs 25 = sec1.length ∧
      st'.regs 26 = sec1Addr + sec1.length ∧
      ListAt st'.mem sec1Addr sec1 ∧
      (∀ a < sec1Addr, st'.mem a = st.mem a) ∧
      ZeroFrom st'.mem (sec1Addr + sec1.length) ∧
      c ≤ 45 * k + 34 * Ms.flatten.length + 80 := by
  set total := Ms.flatten.length
  set sec1 := csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])
  set sec1Addr := resBuf + 5
  have hCopyMC := buildCopyProc_meetsContract (w := w) hCopy
  have hSec1Len : sec1.length = k + 1 + 2 * total := by
    dsimp only [sec1]
    rw [csrList, List.length_append, length_csrOffsets, csrData_matchings_eq_flatten, hMsLen,
      flatMap_pair_len]
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  -- Init
  have hInit : ∃ st1 c1,
      Runs w p ω bridgeEmitSec1Init st .normal st1 c1 ∧
      st1.mem = st.mem ∧ (∀ r ≤ 19, st1.regs r = st.regs r) ∧
      st1.regs 20 = 0 ∧ st1.regs 21 = 0 ∧ st1.regs 22 = sec1Addr ∧ c1 ≤ 15 := by
    suffices hS : ∃ o st1 c1,
        Runs w p ω bridgeEmitSec1Init st o st1 c1 ∧
        (o = .normal ∧ st1.mem = st.mem ∧ (∀ r ≤ 19, st1.regs r = st.regs r) ∧
         st1.regs 20 = 0 ∧ st1.regs 21 = 0 ∧ st1.regs 22 = sec1Addr) ∧ 0 + c1 ≤ 15 by
      obtain ⟨_, st1, c1, hr, ⟨rfl, h1⟩, hc⟩ := hS
      exact ⟨st1, c1, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2, by omega⟩
    unfold bridgeEmitSec1Init
    refine runs_seq_assign_le (v := 0) (by simp [Expr.eval]) ?_
    refine runs_seq_assign_le (v := 0) (by simp [Expr.eval]) ?_
    refine runs_assign_le (v := sec1Addr)
      (by simp [Expr.eval, BinOp.eval, hr19, hw5, sec1Addr, show resBuf + 5 < 2 ^ w by omega]) ?_
      (by simp [Expr.size])
    refine ⟨rfl, rfl, fun r hr => ?_, by simp, by simp, by simp⟩
    simp [Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21),
      Function.update_of_ne (by omega : r ≠ 20)]
  rcases hInit with ⟨st1, c1, hrun1, hmem1, hr1lo, hr1_20, hr1_21, hr1_22, hc1⟩
  -- Loop over `i = 0 .. k` writing CSR offsets
  have hLoop : ∀ rem i (s : State),
      (hi : i + rem = k) →
      (∀ r ≤ 19, s.regs r = st.regs r) →
      s.regs 20 = i → s.regs 21 = 2 * ((Ms.take i).map List.length).sum → s.regs 22 = sec1Addr →
      (∀ a < sec1Addr, s.mem a = st.mem a) →
      (∀ t (ht : t < i), s.mem (sec1Addr + t) = 2 * ((Ms.take t).map List.length).sum) →
      ZeroFrom s.mem (sec1Addr + i) →
      ∃ st2 c2,
        Runs w p ω (.loop (.bin .lt (.reg 20) (.reg 8)) bridgeEmitSec1Body) s .normal st2 c2 ∧
        (∀ r ≤ 19, st2.regs r = st.regs r) ∧
        st2.regs 21 = 2 * total ∧ st2.regs 22 = sec1Addr ∧
        (∀ a < sec1Addr, st2.mem a = st.mem a) ∧
        (∀ t (ht : t < k), st2.mem (sec1Addr + t) = 2 * ((Ms.take t).map List.length).sum) ∧
        ZeroFrom st2.mem (sec1Addr + k) ∧
        c2 ≤ 40 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrlo hr20 hr21 hr22 hfr hoff hz
      have hieq : i = k := by omega
      rw [hieq] at hr20 hr21 hoff hz
      have hc0 : (Expr.bin .lt (.reg 20) (.reg 8)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 8 (by decide), hr8]
      have htot : ((Ms.take k).map List.length).sum = total := by
        rw [← hMsLen, List.take_length, ← List.length_flatten]
      rw [htot] at hr21
      exact ⟨s, _, runs_loop_zero_s1 hc0, hrlo, hr21, hr22, hfr, hoff, hz, by simp [Expr.size]⟩
    | succ rem ih =>
      intro i s hi hrlo hr20 hr21 hr22 hfr hoff hz
      have hi_lt : i < k := by omega
      have hc1' : (Expr.bin .lt (.reg 20) (.reg 8)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 8 (by decide), hr8, hi_lt, hw1]
      set pref := ((Ms.take i).map List.length).sum
      set rowLen := (Ms.getD i []).length
      have hnextPref : ((Ms.take (i + 1)).map List.length).sum = pref + rowLen := by
        have hiM : i < Ms.length := by omega
        dsimp only [pref, rowLen]
        rw [List.take_succ_eq_append_getElem hiM, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton, List.getD_eq_getElem _ _ hiM]
      have hnextLe : pref + rowLen ≤ total := by
        rw [← hnextPref]
        have h1 : (Ms.take (i + 1)).flatten.length ≤ Ms.flatten.length := by
          calc (Ms.take (i + 1)).flatten.length
              ≤ (Ms.take (i + 1)).flatten.length + (Ms.drop (i + 1)).flatten.length := Nat.le_add_right _ _
            _ = (Ms.take (i + 1) ++ Ms.drop (i + 1)).flatten.length := by rw [List.flatten_append, List.length_append]
            _ = Ms.flatten.length := by rw [List.take_append_drop]
        simpa [List.length_flatten, total] using h1
      have hcntI : s.mem (cnt + i) = rowLen := by
        rw [hfr _ (by omega)]; exact hCnt i hi_lt
      have hStep : ∃ s1 cB,
          Runs w p ω bridgeEmitSec1Body s .normal s1 cB ∧
          (∀ r ≤ 19, s1.regs r = st.regs r) ∧
          s1.regs 20 = i + 1 ∧ s1.regs 21 = 2 * (pref + rowLen) ∧ s1.regs 22 = sec1Addr ∧
          (∀ a < sec1Addr, s1.mem a = st.mem a) ∧
          (∀ t (ht : t < i + 1), s1.mem (sec1Addr + t) = 2 * ((Ms.take t).map List.length).sum) ∧
          ZeroFrom s1.mem (sec1Addr + (i + 1)) ∧ cB ≤ 34 := by
        suffices hS : ∃ o s1 cB,
            Runs w p ω bridgeEmitSec1Body s o s1 cB ∧
            (o = .normal ∧ (∀ r ≤ 19, s1.regs r = st.regs r) ∧
             s1.regs 20 = i + 1 ∧ s1.regs 21 = 2 * (pref + rowLen) ∧ s1.regs 22 = sec1Addr ∧
             (∀ a < sec1Addr, s1.mem a = st.mem a) ∧
             (∀ t (ht : t < i + 1), s1.mem (sec1Addr + t) = 2 * ((Ms.take t).map List.length).sum) ∧
             ZeroFrom s1.mem (sec1Addr + (i + 1))) ∧ 0 + cB ≤ 34 by
          obtain ⟨_, s1, cB, hr, ⟨rfl, h1⟩, hc⟩ := hS
          exact ⟨s1, cB, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
            h1.2.2.2.2.2.2, by omega⟩
        unfold bridgeEmitSec1Body
        refine runs_seq_store_le (x := sec1Addr + i) (v := 2 * pref)
          (by simp [Expr.eval, BinOp.eval, hr22, hr20, show sec1Addr + i < 2 ^ w by omega])
          (by simp [Expr.eval, hr21]) ?_
        refine runs_seq_assign_le (v := rowLen)
          (by simp [Expr.eval, BinOp.eval, hrlo 18 (by decide), hr18, hr20,
            show cnt + i < 2 ^ w by omega, Function.update_of_ne (by omega : cnt + i ≠ sec1Addr + i),
            hcntI]) ?_
        refine runs_seq_assign_le (v := 2 * (pref + rowLen))
          (by simp [Expr.eval, BinOp.eval, hr21, show rowLen + rowLen < 2 ^ w by omega,
            show 2 * pref + (rowLen + rowLen) = 2 * (pref + rowLen) by omega,
            show 2 * (pref + rowLen) < 2 ^ w by omega]) ?_
        refine runs_assign_le (v := i + 1)
          (by simp [Expr.eval, BinOp.eval, hr20, hw1, show i + 1 < 2 ^ w by omega]) ?_
          (by simp [Expr.size])
        refine ⟨rfl, fun r hr => ?_, by simp, by simp, by simp [hr22], ?_, ?_, ?_⟩
        · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 21),
            Function.update_of_ne (by omega : r ≠ 23), hrlo r hr]
        · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · intro t ht
          dsimp only
          by_cases hti : t = i
          · subst hti; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hoff t (by omega)
        · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hz a (by omega)
      rcases hStep with ⟨s1, cB, hrunB, hr1'lo, hr1'_20, hr1'_21, hr1'_22, h1'fr, h1'off, h1'z, hcB⟩
      rw [← hnextPref] at hr1'_21
      obtain ⟨st2, c2, hrun2, hr2lo, hr2_21, hr2_22, h2fr, h2off, h2z, hc2⟩ :=
        ih (i + 1) s1 (by omega) hr1'lo hr1'_20 hr1'_21 hr1'_22 h1'fr h1'off h1'z
      exact ⟨st2, _, runs_loop_step_s1 hc1' (by decide) hrunB hrun2, hr2lo, hr2_21, hr2_22,
        h2fr, h2off, h2z, by simp only [Expr.size]; omega⟩
  obtain ⟨st2, c2, hrun2, hr2lo, hr2_21, hr2_22, h2fr, h2off, h2z, hc2⟩ :=
    hLoop k 0 st1 (by omega) hr1lo hr1_20 (by simpa using hr1_21) hr1_22
      (by rw [hmem1]; exact fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun a ha => by rw [hmem1]; exact hZ a (by omega))
  -- Tail: store final offset, copy `2 * total` edge words, set `r25 = sec1.length`, `r26 = sec2Addr`
  have hTail : ∃ st3 c3,
      Runs w p ω (bridgeEmitSec1Tail fCopy) st2 .normal st3 c3 ∧
      (∀ r ≤ 19, st3.regs r = st.regs r) ∧
      st3.regs 25 = sec1.length ∧ st3.regs 26 = sec1Addr + sec1.length ∧
      ListAt st3.mem sec1Addr sec1 ∧
      (∀ a < sec1Addr, st3.mem a = st.mem a) ∧
      ZeroFrom st3.mem (sec1Addr + sec1.length) ∧
      c3 ≤ 34 * total + 50 := by
    suffices hS : ∃ o st3 c3,
        Runs w p ω (bridgeEmitSec1Tail fCopy) st2 o st3 c3 ∧
        (o = .normal ∧ (∀ r ≤ 19, st3.regs r = st.regs r) ∧
         st3.regs 25 = sec1.length ∧ st3.regs 26 = sec1Addr + sec1.length ∧
         ListAt st3.mem sec1Addr sec1 ∧
         (∀ a < sec1Addr, st3.mem a = st.mem a) ∧
         ZeroFrom st3.mem (sec1Addr + sec1.length)) ∧ 0 + c3 ≤ 34 * total + 50 by
      obtain ⟨_, st3, c3, hr, ⟨rfl, h1⟩, hc⟩ := hS
      exact ⟨st3, c3, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2, by omega⟩
    unfold bridgeEmitSec1Tail
    refine runs_seq_store_le (x := sec1Addr + k) (v := 2 * total)
      (by simp [Expr.eval, BinOp.eval, hr2_22, hr2lo 8 (by decide), hr8,
        show sec1Addr + k < 2 ^ w by omega])
      (by simp [Expr.eval, hr2_21]) ?_
    refine runs_seq_call_le hCopyMC (vs := [outAddr + 2, 2 * total, sec1Addr + k + 1])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hr2lo 12 (by decide), hr12,
        hr2lo 16 (by decide), hr16, hr2_22, hr2lo 8 (by decide), hr8, hw1, hw2,
        show outAddr + 2 < 2 ^ w by omega, show total + total = 2 * total by omega,
        show 2 * total < 2 ^ w by omega, show sec1Addr + k < 2 ^ w by omega,
        show sec1Addr + k + 1 < 2 ^ w by omega])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      ⟨outAddr + 2, 2 * total, sec1Addr + k + 1, rfl, by omega, by omega, hw1⟩ ?_
    intro _ mem3 pos3 hPost
    obtain ⟨_, _, _, hEq, hCop, hFr⟩ := hPost
    simp only [List.cons.injEq, and_true] at hEq
    obtain ⟨rfl, rfl, rfl⟩ := hEq
    dsimp only at hCop hFr
    refine runs_seq_assign_le (v := sec1.length)
      (by rw [hSec1Len]; simp [Expr.eval, BinOp.eval, hr2lo 8 (by decide), hr8,
        hr2lo 16 (by decide), hr16, hw1, show k + 1 < 2 ^ w by omega,
        show total + total = 2 * total by omega, show 2 * total < 2 ^ w by omega,
        show k + 1 + 2 * total < 2 ^ w by omega]) ?_
    refine runs_assign_le (v := sec1Addr + sec1.length)
      (by simp [Expr.eval, BinOp.eval, hr2_22, show sec1Addr + sec1.length < 2 ^ w by omega]) ?_ ?_
    · refine ⟨rfl, fun r hr => ?_, by simp, by simp, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne (by omega : r ≠ 26), Function.update_of_ne (by omega : r ≠ 25),
          Function.update_of_ne (by omega : r ≠ 24), hr2lo r hr]
      · dsimp only [sec1, csrList]
        refine listAt_append.mpr ⟨?_, ?_⟩
        · intro i hi
          rw [length_csrOffsets, hMsLen] at hi
          rw [csrOffsets_matchings_getElem Ms (by omega)]
          by_cases hik : i = k
          · subst hik
            rw [hFr _ (Or.inl (by omega)), Function.update_self, ← hMsLen, List.take_length,
              ← List.length_flatten]
          · rw [hFr _ (Or.inl (by omega)), Function.update_of_ne (by omega)]
            exact h2off i (by omega)
        · rw [length_csrOffsets, csrData_matchings_eq_flatten, hMsLen]
          have hFlat : ListAt st.mem (outAddr + 2) (Ms.flatten.flatMap fun e => [e.1, e.2]) :=
            edgesAt_iff_listAt_flatMap.mp hEdges
          have hFlatLen : (Ms.flatten.flatMap fun e => [e.1, e.2]).length = 2 * total :=
            flatMap_pair_len Ms.flatten
          intro j hj
          rw [hFlatLen] at hj
          rw [← Nat.add_assoc, hCop j hj, Function.update_of_ne (by omega), h2fr _ (by omega)]
          exact hFlat j (by rw [hFlatLen]; exact hj)
      · intro a ha; dsimp only
        rw [hFr a (Or.inl (by omega)), Function.update_of_ne (by omega)]
        exact h2fr a ha
      · intro a ha; dsimp only
        rw [hFr a (Or.inr (by omega)), Function.update_of_ne (by omega)]
        exact h2z a (by omega)
    · simp only [buildCopyContract, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
      omega
  rcases hTail with ⟨st3, c3, hrun3, hr3lo, hr3_25, hr3_26, hList1, hFr3, hZ3, hc3⟩
  have hFull : Runs w p ω (bridgeEmitSec1Stmt fCopy) st .normal st3 (c1 + (c2 + c3 + 1) + 1) := by
    unfold bridgeEmitSec1Stmt
    exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + c3 + 1, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3, hrun2, hrun3, rfl⟩), rfl⟩)
  exact ⟨st3, _, hFull, hr3lo, hr3_25, hr3_26, hList1, hFr3, hZ3, by omega⟩

end MinCostFlow.HierPaths
