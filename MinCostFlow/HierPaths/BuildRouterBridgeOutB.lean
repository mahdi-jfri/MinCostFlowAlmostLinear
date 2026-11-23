module

public import MinCostFlow.HierPaths.BuildRouterBridgeOutSec1
import Mathlib.Tactic.Linarith

/-!
# Output packing stage B of the static router bridge (`BuildRouterBridgeOutB`)

Completes the matched output packing branch (`bridgePackMatchedStmt`):
1. `bridgeEmitSec2Stmt`: writes the CSR of walk embeddings `sec2` at `sec2Addr` from `WalksAt`
   at `hInner`.
2. `bridgeMatchFinishStmt`: writes the 5-word `routeResultWords` header at `resBuf`, copies the
   packed result down to `h`, and returns `resEnd = resBuf + (routeResultWords ...).length`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

def bridgeEmitSec2OffInit : Stmt :=
  .assign 20 (.const 0) ;;
  .assign 21 (.const 0)

def bridgeEmitSec2OffBody : Stmt :=
  .store (.bin .add (.reg 26) (.reg 20)) (.reg 21) ;;
  .assign 22 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 20))) ;;
  .assign 23 (.load (.reg 22)) ;;
  .assign 21 (.bin .add (.reg 21) (.reg 23)) ;;
  .assign 20 (.bin .add (.reg 20) (.const 1))

def bridgeEmitSec2Mid : Stmt :=
  .store (.bin .add (.reg 26) (.reg 16)) (.reg 21) ;;
  .assign 27 (.bin .add (.bin .add (.reg 16) (.const 1)) (.reg 21)) ;;
  .assign 28 (.bin .add (.bin .add (.reg 26) (.reg 16)) (.const 1)) ;;
  .assign 20 (.const 0)

def bridgeEmitSec2CopyBody (fCopy : ℕ) : Stmt :=
  .assign 22 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 20))) ;;
  .assign 23 (.load (.reg 22)) ;;
  .call 24 fCopy [.bin .add (.reg 22) (.const 1), .reg 23, .reg 28] ;;
  .assign 28 (.bin .add (.reg 28) (.reg 23)) ;;
  .assign 20 (.bin .add (.reg 20) (.const 1))

/-- Emit section 2 (CSR of walks) at `r26`, setting `r27 = sec2.length`. -/
def bridgeEmitSec2Stmt (fCopy : ℕ) : Stmt :=
  bridgeEmitSec2OffInit ;;
  (.loop (.bin .lt (.reg 20) (.reg 16)) bridgeEmitSec2OffBody ;;
   (bridgeEmitSec2Mid ;;
    .loop (.bin .lt (.reg 20) (.reg 16)) (bridgeEmitSec2CopyBody fCopy)))

/-- Write the 5-word top header at `resBuf`, copy `routeResultWords (.matched Ms emb)` down to
`h`, and return `resEnd = resBuf + totalWords`. -/
def bridgeMatchFinishStmt (fCopy : ℕ) : Stmt :=
  .assign 21 (.bin .add (.const 1) (.reg 25)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 27)) ;;
  .store (.reg 19) (.const 0) ;;
  .store (.bin .add (.reg 19) (.const 1)) (.const 1) ;;
  .store (.bin .add (.reg 19) (.const 2)) (.reg 21) ;;
  .store (.bin .add (.reg 19) (.const 3)) (.reg 22) ;;
  .store (.bin .add (.reg 19) (.const 4)) (.const 0) ;;
  .assign 29 (.bin .add (.bin .add (.const 5) (.reg 25)) (.reg 27)) ;;
  .assign 30 (.bin .add (.reg 19) (.reg 29)) ;;
  .call 24 fCopy [.reg 19, .reg 29, .reg 9] ;;
  .ret (.reg 30)

/-- Full matched output packing branch of `routerBridgeProc`. -/
def bridgePackMatchedStmt (fCopy : ℕ) : Stmt :=
  bridgeCountPrefixStmt ;;
  (bridgeEmitSec1Stmt fCopy ;;
   (bridgeEmitSec2Stmt fCopy ;;
    bridgeMatchFinishStmt fCopy))

theorem bridgePackMatchedStmt_noRand (fCopy : ℕ) : (bridgePackMatchedStmt fCopy).NoRand := by
  simp [bridgePackMatchedStmt, bridgeCountPrefixStmt_noRand, bridgeEmitSec1Stmt_noRand,
    bridgeEmitSec2Stmt, bridgeEmitSec2OffInit, bridgeEmitSec2OffBody, bridgeEmitSec2Mid,
    bridgeEmitSec2CopyBody, bridgeMatchFinishStmt, Stmt.NoRand]

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private lemma runs_loop_zero_ob {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_step_ob {w c1 c2 : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st st1 st2 : State} {v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st1 c1)
    (h2 : Runs w p ω (.loop e body) st1 .normal st2 c2) :
    Runs w p ω (.loop e body) st .normal st2 (e.size + c1 + c2 + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st1, c1, c2, he, hv, h1, h2, rfl⟩))

private lemma walkPrefixSum_succ (emb : ℕ → List ℕ) (j : ℕ) :
    ((List.range (j + 1)).map fun t => (emb t).length).sum =
      ((List.range j).map fun t => (emb t).length).sum + (emb j).length := by
  rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

private lemma walkPrefixSum_mono (emb : ℕ → List ℕ) {a b : ℕ} (hab : a ≤ b) :
    ((List.range a).map fun t => (emb t).length).sum ≤
      ((List.range b).map fun t => (emb t).length).sum := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih => rw [walkPrefixSum_succ]; omega

private lemma csrData_take_len (emb : ℕ → List ℕ) (j : ℕ) :
    ((List.range j).flatMap emb).length = ((List.range j).map fun t => (emb t).length).sum := by
  rw [List.length_flatMap]

private lemma flatMap_range_succ (emb : ℕ → List ℕ) (j : ℕ) :
    (List.range (j + 1)).flatMap emb = (List.range j).flatMap emb ++ emb j := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

private lemma csrOffsets_walks_getElem (total : ℕ) (emb : ℕ → List ℕ) {j : ℕ} (hj : j ≤ total) :
    (csrOffsets total emb)[j]'(by rw [length_csrOffsets]; omega) =
      ((List.range j).map fun t => (emb t).length).sum := by
  simp [csrOffsets]

private lemma bridgeEmitSec2_runs {w fCopy hInner sec2Addr total : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {emb : ℕ → List ℕ}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hr13 : st.regs 13 = hInner) (hr16 : st.regs 16 = total) (hr26 : st.regs 26 = sec2Addr)
    (hWalks : WalksAt st.mem hInner total emb)
    (hWalksBnd : ∀ idx < total,
      hInner ≤ st.mem (hInner + 1 + idx) ∧
      st.mem (hInner + 1 + idx) + 1 + (emb idx).length ≤ sec2Addr)
    (hInnerEnd : hInner + 1 + total ≤ sec2Addr)
    (hZ : ZeroFrom st.mem sec2Addr)
    (hRoom : sec2Addr + (total + 1 + ((List.range total).map fun j => (emb j).length).sum) + 16 < 2 ^ w) :
    let sec2 := csrList total emb
    ∃ st' c,
      Runs w p ω (bridgeEmitSec2Stmt fCopy) st .normal st' c ∧
      (∀ r ≤ 19, st'.regs r = st.regs r) ∧
      st'.regs 25 = st.regs 25 ∧ st'.regs 26 = sec2Addr ∧ st'.regs 27 = sec2.length ∧
      ListAt st'.mem sec2Addr sec2 ∧
      (∀ a < sec2Addr, st'.mem a = st.mem a) ∧
      ZeroFrom st'.mem (sec2Addr + sec2.length) ∧
      c ≤ 125 * total + 17 * ((List.range total).map fun j => (emb j).length).sum + 80 := by
  set sumW := ((List.range total).map fun j => (emb j).length).sum
  set sec2 := csrList total emb
  have hCopyMC := buildCopyProc_meetsContract (w := w) hCopy
  have hSec2Len : sec2.length = total + 1 + sumW := by
    dsimp only [sec2, csrList, csrData, sumW]
    rw [List.length_append, length_csrOffsets, List.length_flatMap]
  have hw1 : 1 < 2 ^ w := by omega
  -- Pass 1 init
  have hInit1 : ∃ st1 c1,
      Runs w p ω bridgeEmitSec2OffInit st .normal st1 c1 ∧
      st1.mem = st.mem ∧ (∀ r ≤ 19, st1.regs r = st.regs r) ∧
      st1.regs 25 = st.regs 25 ∧ st1.regs 26 = sec2Addr ∧
      st1.regs 20 = 0 ∧ st1.regs 21 = 0 ∧ c1 ≤ 10 := by
    suffices hS : ∃ o st1 c1,
        Runs w p ω bridgeEmitSec2OffInit st o st1 c1 ∧
        (o = .normal ∧ st1.mem = st.mem ∧ (∀ r ≤ 19, st1.regs r = st.regs r) ∧
         st1.regs 25 = st.regs 25 ∧ st1.regs 26 = sec2Addr ∧
         st1.regs 20 = 0 ∧ st1.regs 21 = 0) ∧ 0 + c1 ≤ 10 by
      obtain ⟨_, st1, c1, hr, ⟨rfl, h1⟩, hc⟩ := hS
      exact ⟨st1, c1, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2, by omega⟩
    unfold bridgeEmitSec2OffInit
    refine runs_seq_assign_le (v := 0) (by simp [Expr.eval]) ?_
    refine runs_assign_le (v := 0) (by simp [Expr.eval]) ?_ (by simp [Expr.size])
    refine ⟨rfl, rfl, fun r hr => ?_, by simp, by simp [hr26], by simp, by simp⟩
    simp [Function.update_of_ne (by omega : r ≠ 21), Function.update_of_ne (by omega : r ≠ 20)]
  rcases hInit1 with ⟨st1, c1, hrun1, hmem1, hr1lo, hr1_25, hr1_26, hr1_20, hr1_21, hc1⟩
  -- Pass 1 loop: write CSR offsets
  have hLoop1 : ∀ rem j (s : State),
      (hj : j + rem = total) →
      (∀ r ≤ 19, s.regs r = st.regs r) →
      s.regs 25 = st.regs 25 → s.regs 26 = sec2Addr →
      s.regs 20 = j → s.regs 21 = ((List.range j).map fun t => (emb t).length).sum →
      (∀ a < sec2Addr, s.mem a = st.mem a) →
      (∀ t (ht : t < j), s.mem (sec2Addr + t) = ((List.range t).map fun u => (emb u).length).sum) →
      ZeroFrom s.mem (sec2Addr + j) →
      ∃ st2 c2,
        Runs w p ω (.loop (.bin .lt (.reg 20) (.reg 16)) bridgeEmitSec2OffBody) s .normal st2 c2 ∧
        (∀ r ≤ 19, st2.regs r = st.regs r) ∧
        st2.regs 25 = st.regs 25 ∧ st2.regs 26 = sec2Addr ∧ st2.regs 21 = sumW ∧
        (∀ a < sec2Addr, st2.mem a = st.mem a) ∧
        (∀ t (ht : t < total), st2.mem (sec2Addr + t) = ((List.range t).map fun u => (emb u).length).sum) ∧
        ZeroFrom st2.mem (sec2Addr + total) ∧
        c2 ≤ 50 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro j s hj hrlo hr25 hr26' hr20 hr21 hfr hoff hz
      have hjeq : j = total := by omega
      subst hjeq
      have hc0 : (Expr.bin .lt (.reg 20) (.reg 16)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 16 (by decide), hr16]
      exact ⟨s, _, runs_loop_zero_ob hc0, hrlo, hr25, hr26', hr21, hfr, hoff, hz,
        by simp [Expr.size]⟩
    | succ rem ih =>
      intro j s hj hrlo hr25 hr26' hr20 hr21 hfr hoff hz
      have hj_lt : j < total := by omega
      have hc1' : (Expr.bin .lt (.reg 20) (.reg 16)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 16 (by decide), hr16, hj_lt, hw1]
      set pref := ((List.range j).map fun t => (emb t).length).sum
      set wPtr := st.mem (hInner + 1 + j)
      set wLen := (emb j).length
      have hBndJ := hWalksBnd j hj_lt
      have hSeqJ := hWalks.2 j hj_lt
      have hNextLe : pref + wLen ≤ sumW := by
        have := walkPrefixSum_mono emb (show j + 1 ≤ total by omega)
        rw [walkPrefixSum_succ] at this; exact this
      have hStep : ∃ s1 cB,
          Runs w p ω bridgeEmitSec2OffBody s .normal s1 cB ∧
          (∀ r ≤ 19, s1.regs r = st.regs r) ∧
          s1.regs 25 = st.regs 25 ∧ s1.regs 26 = sec2Addr ∧
          s1.regs 20 = j + 1 ∧ s1.regs 21 = pref + wLen ∧
          (∀ a < sec2Addr, s1.mem a = st.mem a) ∧
          (∀ t (ht : t < j + 1), s1.mem (sec2Addr + t) = ((List.range t).map fun u => (emb u).length).sum) ∧
          ZeroFrom s1.mem (sec2Addr + (j + 1)) ∧ cB ≤ 44 := by
        suffices hS : ∃ o s1 cB,
            Runs w p ω bridgeEmitSec2OffBody s o s1 cB ∧
            (o = .normal ∧ (∀ r ≤ 19, s1.regs r = st.regs r) ∧
             s1.regs 25 = st.regs 25 ∧ s1.regs 26 = sec2Addr ∧
             s1.regs 20 = j + 1 ∧ s1.regs 21 = pref + wLen ∧
             (∀ a < sec2Addr, s1.mem a = st.mem a) ∧
             (∀ t (ht : t < j + 1), s1.mem (sec2Addr + t) = ((List.range t).map fun u => (emb u).length).sum) ∧
             ZeroFrom s1.mem (sec2Addr + (j + 1))) ∧ 0 + cB ≤ 44 by
          obtain ⟨_, s1, cB, hr, ⟨rfl, h1⟩, hc⟩ := hS
          exact ⟨s1, cB, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
            h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2, by omega⟩
        unfold bridgeEmitSec2OffBody
        refine runs_seq_store_le (x := sec2Addr + j) (v := pref)
          (by simp [Expr.eval, BinOp.eval, hr26', hr20, show sec2Addr + j < 2 ^ w by omega])
          (by simp [Expr.eval, hr21]) ?_
        refine runs_seq_assign_le (v := wPtr)
          (by simp [Expr.eval, BinOp.eval, hrlo 13 (by decide), hr13, hr20, hw1,
            show hInner + 1 < 2 ^ w by omega, show hInner + 1 + j < 2 ^ w by omega,
            Function.update_of_ne (by omega : hInner + 1 + j ≠ sec2Addr + j),
            hfr (hInner + 1 + j) (by omega), wPtr]) ?_
        refine runs_seq_assign_le (v := wLen)
          (by simp [Expr.eval, Function.update_of_ne (by omega : wPtr ≠ sec2Addr + j),
            hfr wPtr (by omega), wPtr, hSeqJ.1, wLen]) ?_
        refine runs_seq_assign_le (v := pref + wLen)
          (by simp [Expr.eval, BinOp.eval, hr21, show pref + wLen < 2 ^ w by omega]) ?_
        refine runs_assign_le (v := j + 1)
          (by simp [Expr.eval, BinOp.eval, hr20, hw1, show j + 1 < 2 ^ w by omega]) ?_
          (by simp [Expr.size])
        refine ⟨rfl, fun r hr => ?_, by simp [hr25], by simp [hr26'], by simp, by simp,
          ?_, ?_, ?_⟩
        · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 21),
            Function.update_of_ne (by omega : r ≠ 23), Function.update_of_ne (by omega : r ≠ 22),
            hrlo r hr]
        · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · intro t ht
          dsimp only
          by_cases htj : t = j
          · subst htj; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hoff t (by omega)
        · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hz a (by omega)
      rcases hStep with ⟨s1, cB, hrunB, hr1'lo, hr1'_25, hr1'_26, hr1'_20, hr1'_21, h1'fr, h1'off, h1'z, hcB⟩
      rw [← walkPrefixSum_succ emb j] at hr1'_21
      obtain ⟨st2, c2, hrun2, hr2lo, hr2_25, hr2_26, hr2_21, h2fr, h2off, h2z, hc2⟩ :=
        ih (j + 1) s1 (by omega) hr1'lo hr1'_25 hr1'_26 hr1'_20 hr1'_21 h1'fr h1'off h1'z
      exact ⟨st2, _, runs_loop_step_ob hc1' (by decide) hrunB hrun2, hr2lo, hr2_25, hr2_26,
        hr2_21, h2fr, h2off, h2z, by simp only [Expr.size]; omega⟩
  obtain ⟨st2, c2, hrun2, hr2lo, hr2_25, hr2_26, hr2_21, h2fr, h2off, h2z, hc2⟩ :=
    hLoop1 total 0 st1 (by omega) hr1lo hr1_25 hr1_26 hr1_20 (by simpa using hr1_21)
      (by rw [hmem1]; exact fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun a ha => by rw [hmem1]; exact hZ a (by omega))
  -- Middle transition
  have hMid : ∃ st3 c3,
      Runs w p ω bridgeEmitSec2Mid st2 .normal st3 c3 ∧
      (∀ r ≤ 19, st3.regs r = st.regs r) ∧
      st3.regs 25 = st.regs 25 ∧ st3.regs 26 = sec2Addr ∧ st3.regs 27 = sec2.length ∧
      st3.regs 28 = sec2Addr + total + 1 ∧ st3.regs 20 = 0 ∧
      (∀ a < sec2Addr, st3.mem a = st.mem a) ∧
      ListAt st3.mem sec2Addr (csrOffsets total emb) ∧
      ZeroFrom st3.mem (sec2Addr + total + 1) ∧ c3 ≤ 25 := by
    suffices hS : ∃ o st3 c3,
        Runs w p ω bridgeEmitSec2Mid st2 o st3 c3 ∧
        (o = .normal ∧ (∀ r ≤ 19, st3.regs r = st.regs r) ∧
         st3.regs 25 = st.regs 25 ∧ st3.regs 26 = sec2Addr ∧ st3.regs 27 = sec2.length ∧
         st3.regs 28 = sec2Addr + total + 1 ∧ st3.regs 20 = 0 ∧
         (∀ a < sec2Addr, st3.mem a = st.mem a) ∧
         ListAt st3.mem sec2Addr (csrOffsets total emb) ∧
         ZeroFrom st3.mem (sec2Addr + total + 1)) ∧ 0 + c3 ≤ 25 by
      obtain ⟨_, st3, c3, hr, ⟨rfl, h1⟩, hc⟩ := hS
      exact ⟨st3, c3, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
        h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2, by omega⟩
    unfold bridgeEmitSec2Mid
    refine runs_seq_store_le (x := sec2Addr + total) (v := sumW)
      (by simp [Expr.eval, BinOp.eval, hr2_26, hr2lo 16 (by decide), hr16,
        show sec2Addr + total < 2 ^ w by omega])
      (by simp [Expr.eval, hr2_21]) ?_
    refine runs_seq_assign_le (v := sec2.length)
      (by rw [hSec2Len]; simp [Expr.eval, BinOp.eval, hr2lo 16 (by decide), hr16, hr2_21, hw1,
        show total + 1 < 2 ^ w by omega, show total + 1 + sumW < 2 ^ w by omega]) ?_
    refine runs_seq_assign_le (v := sec2Addr + total + 1)
      (by simp [Expr.eval, BinOp.eval, hr2_26, hr2lo 16 (by decide), hr16, hw1,
        show sec2Addr + total < 2 ^ w by omega, show sec2Addr + total + 1 < 2 ^ w by omega]) ?_
    refine runs_assign_le (v := 0) (by simp [Expr.eval]) ?_ (by simp [Expr.size])
    refine ⟨rfl, fun r hr => ?_, by simp [hr2_25], by simp [hr2_26], by simp, by simp, by simp,
      ?_, ?_, ?_⟩
    · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 28),
        Function.update_of_ne (by omega : r ≠ 27), hr2lo r hr]
    · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact h2fr a ha
    · intro j hj
      rw [length_csrOffsets] at hj
      rw [csrOffsets_walks_getElem total emb (by omega)]
      dsimp only
      by_cases hjt : j = total
      · subst hjt; rw [Function.update_self]
      · rw [Function.update_of_ne (by omega)]; exact h2off j (by omega)
    · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact h2z a (by omega)
  rcases hMid with ⟨st3, c3, hrun3, hr3lo, hr3_25, hr3_26, hr3_27, hr3_28, hr3_20, h3fr, h3off, h3z, hc3⟩
  -- Pass 2 loop: copy walks
  have hLoop2 : ∀ rem j (s : State),
      (hj : j + rem = total) →
      (∀ r ≤ 19, s.regs r = st.regs r) →
      s.regs 25 = st.regs 25 → s.regs 26 = sec2Addr → s.regs 27 = sec2.length →
      s.regs 28 = sec2Addr + total + 1 + ((List.range j).map fun t => (emb t).length).sum →
      s.regs 20 = j →
      (∀ a < sec2Addr + total + 1, s.mem a = st3.mem a) →
      ListAt s.mem (sec2Addr + total + 1) ((List.range j).flatMap emb) →
      ZeroFrom s.mem (sec2Addr + total + 1 + ((List.range j).map fun t => (emb t).length).sum) →
      ∃ st4 c4,
        Runs w p ω (.loop (.bin .lt (.reg 20) (.reg 16)) (bridgeEmitSec2CopyBody fCopy)) s .normal st4 c4 ∧
        (∀ r ≤ 19, st4.regs r = st.regs r) ∧
        st4.regs 25 = st.regs 25 ∧ st4.regs 26 = sec2Addr ∧ st4.regs 27 = sec2.length ∧
        (∀ a < sec2Addr + total + 1, st4.mem a = st3.mem a) ∧
        ListAt st4.mem (sec2Addr + total + 1) (csrData total emb) ∧
        ZeroFrom st4.mem (sec2Addr + sec2.length) ∧
        c4 ≤ 70 * rem + 17 * (((List.range total).drop j).map fun t => (emb t).length).sum + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro j s hj hrlo hr25 hr26' hr27 hr28 hr20 hfr hdata hz
      have hjeq : j = total := by omega
      subst hjeq
      have hc0 : (Expr.bin .lt (.reg 20) (.reg 16)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 16 (by decide), hr16]
      refine ⟨s, _, runs_loop_zero_ob hc0, hrlo, hr25, hr26', hr27, hfr, hdata, ?_,
        by simp [Expr.size]⟩
      intro a ha; exact hz a (by rw [hSec2Len] at ha; omega)
    | succ rem ih =>
      intro j s hj hrlo hr25 hr26' hr27 hr28 hr20 hfr hdata hz
      have hj_lt : j < total := by omega
      have hc1' : (Expr.bin .lt (.reg 20) (.reg 16)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 16 (by decide), hr16, hj_lt, hw1]
      set pref := ((List.range j).map fun t => (emb t).length).sum
      set dst := sec2Addr + total + 1 + pref
      set wPtr := st.mem (hInner + 1 + j)
      set wLen := (emb j).length
      have hBndJ := hWalksBnd j hj_lt
      have hSeqJ := hWalks.2 j hj_lt
      have hNextLe : pref + wLen ≤ sumW := by
        have := walkPrefixSum_mono emb (show j + 1 ≤ total by omega)
        rw [walkPrefixSum_succ] at this; exact this
      have hStep2 : ∃ s1 cB,
          Runs w p ω (bridgeEmitSec2CopyBody fCopy) s .normal s1 cB ∧
          (∀ r ≤ 19, s1.regs r = st.regs r) ∧
          s1.regs 25 = st.regs 25 ∧ s1.regs 26 = sec2Addr ∧ s1.regs 27 = sec2.length ∧
          s1.regs 28 = dst + wLen ∧ s1.regs 20 = j + 1 ∧
          (∀ a < sec2Addr + total + 1, s1.mem a = st3.mem a) ∧
          ListAt s1.mem (sec2Addr + total + 1) ((List.range (j + 1)).flatMap emb) ∧
          ZeroFrom s1.mem (dst + wLen) ∧ cB ≤ 64 + 17 * wLen := by
        suffices hS : ∃ o s1 cB,
            Runs w p ω (bridgeEmitSec2CopyBody fCopy) s o s1 cB ∧
            (o = .normal ∧ (∀ r ≤ 19, s1.regs r = st.regs r) ∧
             s1.regs 25 = st.regs 25 ∧ s1.regs 26 = sec2Addr ∧ s1.regs 27 = sec2.length ∧
             s1.regs 28 = dst + wLen ∧ s1.regs 20 = j + 1 ∧
             (∀ a < sec2Addr + total + 1, s1.mem a = st3.mem a) ∧
             ListAt s1.mem (sec2Addr + total + 1) ((List.range (j + 1)).flatMap emb) ∧
             ZeroFrom s1.mem (dst + wLen)) ∧ 0 + cB ≤ 64 + 17 * wLen by
          obtain ⟨_, s1, cB, hr, ⟨rfl, h1⟩, hc⟩ := hS
          exact ⟨s1, cB, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
            h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2, by omega⟩
        unfold bridgeEmitSec2CopyBody
        refine runs_seq_assign_le (v := wPtr)
          (by simp [Expr.eval, BinOp.eval, hrlo 13 (by decide), hr13, hr20, hw1,
            show hInner + 1 < 2 ^ w by omega, show hInner + 1 + j < 2 ^ w by omega,
            hfr (hInner + 1 + j) (by omega), h3fr (hInner + 1 + j) (by omega), wPtr]) ?_
        refine runs_seq_assign_le (v := wLen)
          (by simp [Expr.eval, hfr wPtr (by omega), h3fr wPtr (by omega), wPtr, hSeqJ.1, wLen]) ?_
        refine runs_seq_call_le hCopyMC (vs := [wPtr + 1, wLen, dst])
          (by simp [evalArgs, Expr.eval, BinOp.eval, hr28, hw1,
            show wPtr + 1 < 2 ^ w by omega])
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl <;> omega)
          ⟨wPtr + 1, wLen, dst, rfl, by omega, by omega, hw1⟩ ?_
        intro _ memB posB hPostB
        obtain ⟨_, _, _, hEqB, hCopB, hFrB⟩ := hPostB
        simp only [List.cons.injEq, and_true] at hEqB
        obtain ⟨rfl, rfl, rfl⟩ := hEqB
        dsimp only at hCopB hFrB
        refine runs_seq_assign_le (v := dst + wLen)
          (by simp [Expr.eval, BinOp.eval, hr28, show dst + wLen < 2 ^ w by omega]) ?_
        refine runs_assign_le (v := j + 1)
          (by simp [Expr.eval, BinOp.eval, hr20, hw1, show j + 1 < 2 ^ w by omega]) ?_ ?_
        · refine ⟨rfl, fun r hr => ?_, by simp [hr25], by simp [hr26'], by simp [hr27],
            by simp, by simp, ?_, ?_, ?_⟩
          · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 28),
              Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23),
              Function.update_of_ne (by omega : r ≠ 22), hrlo r hr]
          · intro a ha; dsimp only; rw [hFrB a (Or.inl (by omega))]; exact hfr a ha
          · rw [flatMap_range_succ]
            refine listAt_append.mpr ⟨?_, ?_⟩
            · intro u hu
              have hlenU : u < pref := by rwa [csrData_take_len] at hu
              dsimp only; rw [hFrB _ (Or.inl (by omega))]; exact hdata u hu
            · rw [csrData_take_len]
              intro u hu
              dsimp only
              rw [hCopB u hu, hfr _ (by omega), h3fr _ (by omega)]
              exact hSeqJ.2 u hu
          · intro a ha; dsimp only; rw [hFrB a (Or.inr (by omega))]; exact hz a (by omega)
        · simp only [buildCopyContract, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
          omega
      rcases hStep2 with ⟨s1, cB, hrunB, hr1'lo, hr1'_25, hr1'_26, hr1'_27, hr1'_28, hr1'_20,
        h1'fr, h1'data, h1'z, hcB⟩
      have hr1'_28' : s1.regs 28 =
          sec2Addr + total + 1 + ((List.range (j + 1)).map fun t => (emb t).length).sum := by
        rw [walkPrefixSum_succ, ← Nat.add_assoc]; exact hr1'_28
      have h1'z' : ZeroFrom s1.mem
          (sec2Addr + total + 1 + ((List.range (j + 1)).map fun t => (emb t).length).sum) := by
        intro a ha; exact h1'z a (by rw [walkPrefixSum_succ] at ha; omega)
      obtain ⟨st4, c4, hrun4, hr4lo, hr4_25, hr4_26, hr4_27, h4fr, h4data, h4z, hc4⟩ :=
        ih (j + 1) s1 (by omega) hr1'lo hr1'_25 hr1'_26 hr1'_27 hr1'_28' hr1'_20 h1'fr h1'data h1'z'
      have hdrop : (((List.range total).drop j).map fun t => (emb t).length).sum =
          wLen + (((List.range total).drop (j + 1)).map fun t => (emb t).length).sum := by
        have hcons : (List.range total).drop j = j :: (List.range total).drop (j + 1) := by
          have := List.drop_eq_getElem_cons (l := List.range total) (i := j) (by simp [hj_lt])
          simpa using this
        rw [hcons, List.map_cons, List.sum_cons]
      exact ⟨st4, _, runs_loop_step_ob hc1' (by decide) hrunB hrun4, hr4lo, hr4_25, hr4_26,
        hr4_27, h4fr, h4data, h4z, by simp only [Expr.size]; omega⟩
  obtain ⟨st4, c4, hrun4, hr4lo, hr4_25, hr4_26, hr4_27, h4fr, h4data, h4z, hc4⟩ :=
    hLoop2 total 0 st3 (by omega) hr3lo hr3_25 hr3_26 hr3_27 (by simpa using hr3_28) hr3_20
      (fun _ _ => rfl) (by simp [ListAt]) (by simpa using h3z)
  have hFull : Runs w p ω (bridgeEmitSec2Stmt fCopy) st .normal st4
      (c1 + (c2 + (c3 + c4 + 1) + 1) + 1) := by
    unfold bridgeEmitSec2Stmt
    exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + (c3 + c4 + 1) + 1, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3 + c4 + 1, hrun2,
        runs_seq_iff.mpr (Or.inr ⟨st3, c3, c4, hrun3, hrun4, rfl⟩), rfl⟩), rfl⟩)
  have hList2 : ListAt st4.mem sec2Addr sec2 := by
    dsimp only [sec2, csrList]
    refine listAt_append.mpr ⟨?_, ?_⟩
    · intro j hj
      rw [length_csrOffsets] at hj
      rw [h4fr _ (by omega)]
      exact h3off j (by rw [length_csrOffsets]; exact hj)
    · rw [length_csrOffsets, ← Nat.add_assoc]
      exact h4data
  refine ⟨st4, _, hFull, hr4lo, hr4_25, hr4_26, hr4_27, hList2,
    fun a ha => (h4fr a (by omega)).trans (h3fr a ha), h4z, ?_⟩
  simp only [List.drop_zero] at hc4
  omega

private lemma bridgeMatchFinish_runs {w fCopy h resBuf : ℕ}
    {p : Program} {ω : ℕ → Bool} {st3 : State}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hr9 : st3.regs 9 = h) (hr19 : st3.regs 19 = resBuf)
    (hr25 : st3.regs 25 = (csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])).length)
    (hr27 : st3.regs 27 = (csrList Ms.flatten.length emb).length)
    (hList1 : ListAt st3.mem (resBuf + 5) (csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])))
    (hList2 : ListAt st3.mem (resBuf + 5 + (csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])).length)
      (csrList Ms.flatten.length emb))
    (hh_le : h ≤ resBuf)
    (hZ3 : ZeroFrom st3.mem (resBuf + (routeResultWords (.matched Ms emb)).length))
    (hRoom : resBuf + (routeResultWords (.matched Ms emb)).length + 16 < 2 ^ w) :
    let resEnd := resBuf + (routeResultWords (.matched Ms emb)).length
    ∃ st4 c4,
      Runs w p ω (bridgeMatchFinishStmt fCopy) st3 (.returned resEnd) st4 c4 ∧
      ListAt st4.mem h (routeResultWords (.matched Ms emb)) ∧
      ZeroFrom st4.mem resEnd ∧
      (∀ a < h, st4.mem a = st3.mem a) ∧
      c4 ≤ 17 * (routeResultWords (.matched Ms emb)).length + 100 := by
  set sec1 := csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])
  set sec2 := csrList Ms.flatten.length emb
  set totalWords := (routeResultWords (.matched Ms emb)).length
  set resEnd := resBuf + totalWords
  have hTotWords : totalWords = 5 + sec1.length + sec2.length := by
    dsimp only [totalWords, sec1, sec2]
    rw [routeResultWords_matched_eq]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hCopyDown := buildCopyProc_meetsDownContract (w := w) hCopy
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  suffices hS : ∃ o st4 c4,
      Runs w p ω (bridgeMatchFinishStmt fCopy) st3 o st4 c4 ∧
      (o = .returned resEnd ∧
       ListAt st4.mem h (routeResultWords (.matched Ms emb)) ∧
       ZeroFrom st4.mem resEnd ∧
       (∀ a < h, st4.mem a = st3.mem a)) ∧ 0 + c4 ≤ 17 * totalWords + 100 by
    obtain ⟨_, st4, c4, hr, ⟨rfl, h1, h2, h3⟩, hc⟩ := hS
    exact ⟨st4, c4, hr, h1, h2, h3, by omega⟩
  unfold bridgeMatchFinishStmt
  refine runs_seq_assign_le (v := 1 + sec1.length)
    (by simp [Expr.eval, BinOp.eval, hr25, hw1, show 1 + sec1.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := 1 + sec1.length + sec2.length)
    (by simp [Expr.eval, BinOp.eval, hr27, show 1 + sec1.length + sec2.length < 2 ^ w by omega]) ?_
  refine runs_seq_store_le (x := resBuf) (v := 0) (by simp [Expr.eval, hr19]) (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := resBuf + 1) (v := 1)
    (by simp [Expr.eval, BinOp.eval, hr19, hw1, show resBuf + 1 < 2 ^ w by omega])
    (by simp [Expr.eval, hw1]) ?_
  refine runs_seq_store_le (x := resBuf + 2) (v := 1 + sec1.length)
    (by simp [Expr.eval, BinOp.eval, hr19, hw2, show resBuf + 2 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := resBuf + 3) (v := 1 + sec1.length + sec2.length)
    (by simp [Expr.eval, BinOp.eval, hr19, hw3, show resBuf + 3 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := resBuf + 4) (v := 0)
    (by simp [Expr.eval, BinOp.eval, hr19, hw4, show resBuf + 4 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_assign_le (v := totalWords)
    (by rw [hTotWords]; simp [Expr.eval, BinOp.eval, hr25, hr27, hw5,
      show 5 + sec1.length < 2 ^ w by omega, show 5 + sec1.length + sec2.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := resEnd)
    (by simp [Expr.eval, BinOp.eval, hr19, resEnd, show resBuf + totalWords < 2 ^ w by omega]) ?_
  refine runs_seq_call_le hCopyDown (vs := [resBuf, totalWords, h])
    (by simp [evalArgs, Expr.eval, hr19, hr9])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
    ⟨resBuf, totalWords, h, rfl, by omega, by omega, hw1⟩ ?_
  intro _ mem4 pos4 hPost4
  obtain ⟨_, _, _, hEq4, hCop4, hFr4⟩ := hPost4
  simp only [List.cons.injEq, and_true] at hEq4
  obtain ⟨rfl, rfl, rfl⟩ := hEq4
  dsimp only at hCop4 hFr4
  refine runs_ret_le (v := resEnd) (by simp [Expr.eval]) ?_ ?_
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · have hPreRes : ListAt
          (Function.update (Function.update (Function.update (Function.update
            (Function.update st3.mem resBuf 0) (resBuf + 1) 1)
            (resBuf + 2) (1 + sec1.length)) (resBuf + 3) (1 + sec1.length + sec2.length))
            (resBuf + 4) 0)
          resBuf (routeResultWords (.matched Ms emb)) := by
        rw [routeResultWords_matched_eq]
        refine listAt_append.mpr ⟨listAt_append.mpr ⟨?_, ?_⟩, ?_⟩
        · refine listAt_cons.mpr ⟨?_, listAt_cons.mpr ⟨?_, listAt_cons.mpr ⟨?_,
            listAt_cons.mpr ⟨?_, listAt_cons.mpr ⟨?_, by simp [ListAt]⟩⟩⟩⟩⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [show resBuf + 1 + 1 = resBuf + 2 by omega,
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · rw [show resBuf + 1 + 1 + 1 = resBuf + 3 by omega,
              Function.update_of_ne (by omega), Function.update_self]
          · rw [show resBuf + 1 + 1 + 1 + 1 = resBuf + 4 by omega, Function.update_self]
        · simp only [List.length_cons, List.length_nil]
          intro j hj
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hList1 j hj
        · simp only [List.length_append, List.length_cons, List.length_nil]
          intro j hj
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), ← Nat.add_assoc]
          exact hList2 j hj
      intro j hj
      dsimp only
      rw [hCop4 j hj]
      exact hPreRes j hj
    · intro a ha
      dsimp only
      rw [hFr4 a (Or.inr (by omega)), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hZ3 a (by omega)
    · intro a ha
      dsimp only
      rw [hFr4 a (Or.inl (by omega)), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · simp only [buildCopyDownContract, buildCopyContract, List.getD_cons_zero, List.getD_cons_succ,
      argsSize, Expr.size]
    omega

/-- Full verification of `bridgePackMatchedStmt`: packs `routeResultWords (.matched Ms emb)` at `h`,
preserves memory `< h`, establishes `ZeroFrom st'.mem resEnd`, and returns `resEnd`. -/
theorem bridgePackMatched_runs {w fCopy h pTable outAddr hInner vInner : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {Δ L b z : ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hr8 : st.regs 8 = pairs.length)
    (hr9 : st.regs 9 = h)
    (hr11 : st.regs 11 = pTable)
    (hr12 : st.regs 12 = outAddr)
    (hr13 : st.regs 13 = hInner)
    (hr14 : st.regs 14 = vInner)
    (hr15 : st.regs 15 = G.n)
    (hXsub : X ⊆ Finset.range G.n)
    (hValid : ValidTerminalPairs X pairs)
    (hSpec : RouteMatchedSpec G X pairs Δ L b z Ms emb)
    (hPairs : PairsAt st.mem pTable pairs)
    (hPairsB : PairsBounded st.mem pTable pairs outAddr)
    (hOut : RouteOutSortedAt st.mem outAddr (.matched Ms emb))
    (hWalks : WalksAt st.mem hInner Ms.flatten.length emb)
    (hWalksBnd : ∀ idx < Ms.flatten.length,
      hInner ≤ st.mem (hInner + 1 + idx) ∧
      st.mem (hInner + 1 + idx) + 1 + (emb idx).length ≤ vInner)
    (hh_le_v : h ≤ vInner)
    (hOutInner : outAddr + 2 + 2 * G.n = hInner)
    (hInnerV : hInner + (1 + X.card) ≤ vInner)
    (hZ : ZeroFrom st.mem vInner)
    (hRoom : vInner + G.n + pairs.length + (routeResultWords (.matched Ms emb)).length + 32 < 2 ^ w) :
    let resEnd := vInner + G.n + pairs.length + (routeResultWords (.matched Ms emb)).length
    ∃ st' c,
      Runs w p ω (bridgePackMatchedStmt fCopy) st (.returned resEnd) st' c ∧
      ListAt st'.mem h (routeResultWords (.matched Ms emb)) ∧
      h + (routeResultWords (.matched Ms emb)).length ≤ resEnd ∧
      ZeroFrom st'.mem resEnd ∧
      (∀ a < h, st'.mem a = st.mem a) ∧
      c ≤ 100 * (pairsWords pairs).length + 300 * Ms.flatten.length +
          40 * ((List.range Ms.flatten.length).map fun j => (emb j).length).sum + 500 := by
  set k := pairs.length
  set total := Ms.flatten.length
  set sumW := ((List.range total).map fun j => (emb j).length).sum
  set sec1 := csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])
  set sec2 := csrList total emb
  set resBuf := vInner + G.n + k
  set totalWords := (routeResultWords (.matched Ms emb)).length
  set resEnd := resBuf + totalWords
  have hMsLen : Ms.length = k := hSpec.1
  have hTotLeX : total ≤ X.card := matched_total_le_cardX hValid hSpec
  have hXleN : X.card ≤ G.n := by simpa using Finset.card_le_card hXsub
  have hSec1Len : sec1.length = k + 1 + 2 * total := by
    have hf : ∀ es : List (ℕ × ℕ), (es.flatMap fun e => [e.1, e.2]).length = 2 * es.length := by
      intro es; induction es with | nil => simp | cons _ _ ih => simp [ih]; omega
    dsimp only [sec1, total]
    rw [csrList, List.length_append, length_csrOffsets, csrData_matchings_eq_flatten, hMsLen, hf]
  have hSec2Len : sec2.length = total + 1 + sumW := by
    dsimp only [sec2, csrList, csrData, sumW]
    rw [List.length_append, length_csrOffsets, List.length_flatMap]
  have hTotWords : totalWords = 5 + sec1.length + sec2.length := by
    dsimp only [totalWords, sec1, sec2, total]
    rw [routeResultWords_matched_eq]
    simp only [List.length_append, List.length_cons, List.length_nil]
  -- Stage A+B: count
  obtain ⟨st1, c1, hrun1, hr1lo, hr1_16, hr1_17, hr1_18, hr1_19, hFr1, hCnt1, hZ1, hc1⟩ :=
    bridgeCountPrefix_runs (w := w) (p := p) (ω := ω) hr8 hr11 hr12 hr14 hr15 hXsub hValid hSpec hPairs hPairsB hOut
      (by omega) hZ (by omega)
  -- Stage C: emit sec1
  have hEdges1 : EdgesAt st1.mem (outAddr + 2) Ms.flatten := fun j hj => by
    rw [hFr1 _ (by omega), hFr1 _ (by omega)]
    exact hOut.2.2 j hj
  obtain ⟨st2, c2, hrun2, hr2lo, hr2_25, hr2_26, hList1, hFr2, hZ2, hc2⟩ :=
    bridgeEmitSec1_runs (w := w) (p := p) (ω := ω) hCopy hMsLen
      (by rw [hr1lo 8 (by decide), hr8]) (by rw [hr1lo 12 (by decide), hr12])
      hr1_16 hr1_18 hr1_19 hEdges1 hCnt1 (by omega) (by omega) hZ1 (by omega)
  -- Stage D: emit sec2
  have hWalks2 : WalksAt st2.mem hInner total emb := by
    refine ⟨by rw [hFr2 _ (by omega), hFr1 _ (by omega)]; exact hWalks.1, fun j hj => ?_⟩
    have hbj := hWalksBnd j hj
    have hptr : st2.mem (hInner + 1 + j) = st.mem (hInner + 1 + j) := by
      rw [hFr2 _ (by omega), hFr1 _ (by omega)]
    rw [hptr]
    refine ⟨by rw [hFr2 _ (by omega), hFr1 _ (by omega)]; exact (hWalks.2 j hj).1, fun u hu => ?_⟩
    rw [hFr2 _ (by omega), hFr1 _ (by omega)]
    exact (hWalks.2 j hj).2 u hu
  have hWalksBnd2 : ∀ idx < total,
      hInner ≤ st2.mem (hInner + 1 + idx) ∧
      st2.mem (hInner + 1 + idx) + 1 + (emb idx).length ≤ resBuf + 5 + sec1.length := by
    intro idx hidx
    have hptr : st2.mem (hInner + 1 + idx) = st.mem (hInner + 1 + idx) := by
      rw [hFr2 _ (by omega), hFr1 _ (by omega)]
    rw [hptr]
    have hb := hWalksBnd idx hidx
    exact ⟨hb.1, by omega⟩
  have hRoom2 : resBuf + 5 + sec1.length + (total + 1 + sumW) + 16 < 2 ^ w := by
    dsimp only [resBuf, totalWords] at hTotWords hRoom ⊢; omega
  obtain ⟨st3, c3, hrun3, hr3lo, hr3_25, hr3_26, hr3_27, hList2, hFr3, hZ3, hc3⟩ :=
    bridgeEmitSec2_runs (w := w) (p := p) (ω := ω) hCopy
      (by rw [hr2lo 13 (by decide), hr1lo 13 (by decide), hr13])
      (by rw [hr2lo 16 (by decide), hr1_16]) hr2_26 hWalks2 hWalksBnd2 (by omega) hZ2 hRoom2
  -- Stage E: write 5-word header, copy down to `h`, return `resEnd`
  have hList1_3 : ListAt st3.mem (resBuf + 5) sec1 := fun j hj => by
    rw [hFr3 _ (by dsimp only [sec1] at hj ⊢; omega)]; exact hList1 j hj
  have hZ3_end : ZeroFrom st3.mem (resBuf + totalWords) := fun a ha =>
    hZ3 a (by dsimp only [sec1, sec2, totalWords] at hTotWords ha ⊢; omega)
  obtain ⟨st4, c4, hrun4, hList4, hZ4, hFr4, hc4⟩ :=
    bridgeMatchFinish_runs (w := w) (p := p) (ω := ω) hCopy
      (by rw [hr3lo 9 (by decide), hr2lo 9 (by decide), hr1lo 9 (by decide), hr9])
      (by rw [hr3lo 19 (by decide), hr2lo 19 (by decide), hr1_19])
      (by rw [hr3_25, hr2_25]) hr3_27 hList1_3 hList2 (by omega) hZ3_end (by omega)
  have hFull : Runs w p ω (bridgePackMatchedStmt fCopy) st (.returned resEnd) st4
      (c1 + (c2 + (c3 + c4 + 1) + 1) + 1) := by
    unfold bridgePackMatchedStmt
    exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + (c3 + c4 + 1) + 1, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3 + c4 + 1, hrun2,
        runs_seq_iff.mpr (Or.inr ⟨st3, c3, c4, hrun3, hrun4, rfl⟩), rfl⟩), rfl⟩)
  have hk_le_pLen : 2 * k + 1 ≤ (pairsWords pairs).length := by
    have := pairsWords_length_eq pairs; omega
  exact ⟨st4, _, hFull, hList4, by omega, hZ4,
    fun a ha => (hFr4 a ha).trans ((hFr3 a (by omega)).trans ((hFr2 a (by omega)).trans (hFr1 a (by omega)))),
    by omega⟩

end MinCostFlow.HierPaths
