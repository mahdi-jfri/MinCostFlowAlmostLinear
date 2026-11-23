module

public import MinCostFlow.HierPaths.BuildRouterBridgeMath
public import MinCostFlow.HierPaths.BuildProgCopy
import Mathlib.Tactic.Linarith

/-!
# Input conversion stage of the static router bridge (`BuildRouterBridgeIn`)

Converts the `RouterProcContract` inputs (`finsetWords X` at `xAddr`, `pairsWords pairs` at
`pAddr`) into the `routeOrCutPairsWithWalksContract` inputs (`VertSetAt` at `xBuf = h`,
`PairsAt` + `PairsBounded` at `pTable = h + 1 + X.card`), allocating `outAddr` and `hInner`
above them while preserving all memory below `h` and `ZeroFrom` from `hInner`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Cursor inside the packed `SeqAt` sets after emitting the first `j` sections of `pairsSections`. -/
def bridgePairCur (pTable k : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (j : ℕ) : ℕ :=
  pTable + 1 + 2 * k + j + pairsSecOff pairs j

/-- Input conversion loop body: convert section `j = reg 20` of `pairsWords` at `reg 2` into a
length-prefixed `SeqAt` block at `reg 18` and record its pointer in `pTable[1 + j]`. -/
def bridgePairsLoopBody (fCopy : ℕ) : Stmt :=
  .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
  .assign 22 (.load (.bin .add (.bin .add (.reg 2) (.reg 20)) (.const 1))) ;;
  .assign 23 (.bin .sub (.reg 22) (.reg 21)) ;;
  .store (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 20)) (.reg 18) ;;
  .store (.reg 18) (.reg 23) ;;
  .call 16 fCopy [.bin .add (.reg 19) (.reg 21), .reg 23, .bin .add (.reg 18) (.const 1)] ;;
  .assign 18 (.bin .add (.bin .add (.reg 18) (.const 1)) (.reg 23)) ;;
  .assign 20 (.bin .add (.reg 20) (.const 1))

def bridgePrepPrefix (fCopy : ℕ) : Stmt :=
  .assign 15 (.load (.reg 0)) ;;
  .assign 10 (.reg 9) ;;
  .store (.reg 10) (.reg 7) ;;
  .call 16 fCopy [.reg 1, .reg 7, .bin .add (.reg 10) (.const 1)] ;;
  .assign 11 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 7)) ;;
  .store (.reg 11) (.reg 8) ;;
  .assign 17 (.bin .add (.reg 8) (.reg 8)) ;;
  .assign 18 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 17)) ;;
  .assign 19 (.bin .add (.bin .add (.reg 2) (.reg 17)) (.const 1)) ;;
  .assign 20 (.const 0)

def bridgePrepTail : Stmt :=
  .assign 12 (.bin .add (.reg 18) (.const 5)) ;;
  .assign 13 (.bin .add (.bin .add (.reg 12) (.const 2)) (.bin .add (.reg 15) (.reg 15)))

/-- Input conversion stage of `routerBridgeProc`.
Reads `regs 0..9 = [gAddr, xAddr, pAddr, Δ, L, b, z, nX, k, h]`, sets:
* `reg 10 = xBuf = h`, writing `VertSetAt` for `X`;
* `reg 11 = pTable = h + 1 + nX`, writing `PairsAt` + `PairsBounded` for `pairs`;
* `reg 12 = outAddr = bridgePairCur pTable k pairs (2 * k) + 5`;
* `reg 13 = hInner = outAddr + 2 + 2 * G.n`;
* `reg 15 = G.n`. -/
def bridgePrepInputsStmt (fCopy : ℕ) : Stmt :=
  bridgePrepPrefix fCopy ;;
  (.loop (.bin .lt (.reg 20) (.reg 17)) (bridgePairsLoopBody fCopy) ;;
   bridgePrepTail)

theorem bridgePrepInputsStmt_noRand (fCopy : ℕ) : (bridgePrepInputsStmt fCopy).NoRand := by
  simp [bridgePrepInputsStmt, bridgePrepPrefix, bridgePrepTail, bridgePairsLoopBody, Stmt.NoRand]

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private lemma runs_loop_zero_in {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_step_in {w c1 c2 : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st st1 st2 : State} {v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st1 c1)
    (h2 : Runs w p ω (.loop e body) st1 .normal st2 c2) :
    Runs w p ω (.loop e body) st .normal st2 (e.size + c1 + c2 + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st1, c1, c2, he, hv, h1, h2, rfl⟩))

private lemma bridgePairCur_zero (pTable k : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) :
    bridgePairCur pTable k pairs 0 = pTable + 1 + 2 * k := by
  simp [bridgePairCur, pairsSecOff_zero]

private lemma bridgePairCur_succ (pTable k : ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    {j : ℕ} (hj : j < 2 * pairs.length) :
    bridgePairCur pTable k pairs (j + 1) =
      bridgePairCur pTable k pairs j + 1 +
        ((pairsSections pairs)[j]'(by rw [pairsSections_length]; exact hj)).length := by
  unfold bridgePairCur
  rw [pairsSecOff_succ hj]
  omega

private lemma bridgePairCur_le_end (pTable : ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    {j : ℕ} (hj : j ≤ 2 * pairs.length) :
    bridgePairCur pTable pairs.length pairs j ≤
      pTable + 1 + 2 * pairs.length + (pairsWords pairs).length := by
  unfold bridgePairCur
  have h1 := pairsSecOff_le_total pairs j
  have h2 := pairsWords_length_eq pairs
  omega

/-- Full verification of `bridgePrepInputsStmt`: produces `VertSetAt` at `h`, `PairsAt` +
`PairsBounded` at `pTable = h + 1 + X.card`, `outAddr`, and `hInner = outAddr + 2 + 2 * G.n`
with `ZeroFrom mem' hInner` and cost `≤ 17 * X.card + 80 * (pairsWords pairs).length + 120`. -/
theorem bridgePrepInputs_runs {w fCopy : ℕ} {p : Program} {ω : ℕ → Bool}
    {gAddr xAddr pAddr Δ L b z h pos : ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {mem : ℕ → ℕ}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hG : GraphAt mem gAddr G)
    (hX : ListAt mem xAddr (finsetWords X))
    (hP : ListAt mem pAddr (pairsWords pairs))
    (hg : gAddr + G.encode.length ≤ h)
    (hx : xAddr + (finsetWords X).length ≤ h)
    (hp : pAddr + (pairsWords pairs).length ≤ h)
    (hZ : ZeroFrom mem h)
    (hRoom : h + (1 + X.card) + (1 + 2 * pairs.length) + (pairsWords pairs).length + 5 +
      (2 + 2 * G.n) + 16 < 2 ^ w) :
    let st0 := startState [gAddr, xAddr, pAddr, Δ, L, b, z, X.card, pairs.length, h] mem pos
    let xBuf := h
    let pTable := h + 1 + X.card
    let curEnd := bridgePairCur pTable pairs.length pairs (2 * pairs.length)
    let outAddr := curEnd + 5
    let hInner := outAddr + 2 + 2 * G.n
    ∃ st' c,
      Runs w p ω (bridgePrepInputsStmt fCopy) st0 .normal st' c ∧
      (∀ r ≤ 9, st'.regs r = st0.regs r) ∧
      st'.regs 10 = xBuf ∧ st'.regs 11 = pTable ∧
      st'.regs 12 = outAddr ∧ st'.regs 13 = hInner ∧ st'.regs 15 = G.n ∧
      VertSetAt st'.mem xBuf X ∧
      PairsAt st'.mem pTable pairs ∧
      PairsBounded st'.mem pTable pairs outAddr ∧
      curEnd ≤ pTable + 1 + 2 * pairs.length + (pairsWords pairs).length ∧
      (∀ a < h, st'.mem a = mem a) ∧
      ZeroFrom st'.mem curEnd ∧
      c ≤ 17 * X.card + 100 * (pairsWords pairs).length + 120 := by
  set nX := X.card
  set k := pairs.length
  set pLen := (pairsWords pairs).length
  set st0 := startState [gAddr, xAddr, pAddr, Δ, L, b, z, nX, k, h] mem pos
  set xBuf := h
  set pTable := h + 1 + nX
  set dataBase := pAddr + 2 * k + 1
  set curEnd := bridgePairCur pTable k pairs (2 * k)
  set outAddr := curEnd + 5
  set hInner := outAddr + 2 + 2 * G.n
  have hCopyMC := buildCopyProc_meetsContract (w := w) hCopy
  have hXlen : (finsetWords X).length = nX := Finset.length_sort _
  have hGnMem : mem gAddr = G.n := by
    have h0 := hG 0 (by simp [Graph.encode])
    simpa [Graph.encode] using h0
  have hPLenEq : pLen = 2 * k + 1 + ((pairsSections pairs).map List.length).sum :=
    pairsWords_length_eq pairs
  have hCurEndLe : curEnd ≤ pTable + 1 + 2 * k + pLen := bridgePairCur_le_end pTable pairs le_rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hOutW : outAddr < 2 ^ w := by dsimp only [outAddr, pTable]; omega
  have hInnerW : hInner < 2 ^ w := by dsimp only [hInner, outAddr, pTable]; omega
  have hGnW : G.n < 2 ^ w := by omega
  have h2GnW : 2 * G.n < 2 ^ w := by omega
  have h2KW : 2 * k < 2 ^ w := by omega
  have hDBW : dataBase < 2 ^ w := by dsimp only [dataBase]; omega
  -- Prefix before the loop
  have hPreRun : ∃ st1 c1,
      Runs w p ω
        (.assign 15 (.load (.reg 0)) ;;
         .assign 10 (.reg 9) ;;
         .store (.reg 10) (.reg 7) ;;
         .call 16 fCopy [.reg 1, .reg 7, .bin .add (.reg 10) (.const 1)] ;;
         .assign 11 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 7)) ;;
         .store (.reg 11) (.reg 8) ;;
         .assign 17 (.bin .add (.reg 8) (.reg 8)) ;;
         .assign 18 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 17)) ;;
         .assign 19 (.bin .add (.bin .add (.reg 2) (.reg 17)) (.const 1)) ;;
         .assign 20 (.const 0))
        st0 .normal st1 c1 ∧
      (∀ r ≤ 9, st1.regs r = st0.regs r) ∧
      st1.regs 10 = xBuf ∧ st1.regs 11 = pTable ∧ st1.regs 15 = G.n ∧
      st1.regs 17 = 2 * k ∧ st1.regs 18 = bridgePairCur pTable k pairs 0 ∧
      st1.regs 19 = dataBase ∧ st1.regs 20 = 0 ∧
      SeqAt st1.mem xBuf (finsetWords X) ∧
      st1.mem pTable = k ∧
      (∀ a < h, st1.mem a = mem a) ∧
      ZeroFrom st1.mem (pTable + 1) ∧
      c1 ≤ 17 * nX + 70 := by
    suffices hStep : ∃ o st1 c1,
        Runs w p ω
          (.assign 15 (.load (.reg 0)) ;;
           .assign 10 (.reg 9) ;;
           .store (.reg 10) (.reg 7) ;;
           .call 16 fCopy [.reg 1, .reg 7, .bin .add (.reg 10) (.const 1)] ;;
           .assign 11 (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 7)) ;;
           .store (.reg 11) (.reg 8) ;;
           .assign 17 (.bin .add (.reg 8) (.reg 8)) ;;
           .assign 18 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 17)) ;;
           .assign 19 (.bin .add (.bin .add (.reg 2) (.reg 17)) (.const 1)) ;;
           .assign 20 (.const 0))
          st0 o st1 c1 ∧
        (o = .normal ∧
         (∀ r ≤ 9, st1.regs r = st0.regs r) ∧
         st1.regs 10 = xBuf ∧ st1.regs 11 = pTable ∧ st1.regs 15 = G.n ∧
         st1.regs 17 = 2 * k ∧ st1.regs 18 = bridgePairCur pTable k pairs 0 ∧
         st1.regs 19 = dataBase ∧ st1.regs 20 = 0 ∧
         SeqAt st1.mem xBuf (finsetWords X) ∧
         st1.mem pTable = k ∧
         (∀ a < h, st1.mem a = mem a) ∧
         ZeroFrom st1.mem (pTable + 1)) ∧
        0 + c1 ≤ 17 * nX + 70 by
      obtain ⟨_, st1, c1, hr, ⟨rfl, h1⟩, hc⟩ := hStep
      exact ⟨st1, c1, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
        h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.1,
        h1.2.2.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2.2, by omega⟩
    refine runs_seq_assign_le (v := G.n) (by simp [Expr.eval, st0, startState, hGnMem]) ?_
    refine runs_seq_assign_le (v := xBuf) (by simp [Expr.eval, st0, startState, xBuf]) ?_
    refine runs_seq_store_le (x := xBuf) (v := nX) (by simp [Expr.eval])
      (by simp [Expr.eval, st0, startState]) ?_
    have hX1W : xBuf + 1 < 2 ^ w := by dsimp only [xBuf]; omega
    refine runs_seq_call_le hCopyMC (vs := [xAddr, nX, xBuf + 1])
      (by simp [evalArgs, Expr.eval, st0, startState, hw1, hX1W])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      ⟨xAddr, nX, xBuf + 1, rfl, by omega, by omega, hw1⟩ ?_
    intro _ mem₁ pos₁ hPostC
    obtain ⟨_, _, _, hEqC, hCopied, hFrC⟩ := hPostC
    simp only [List.cons.injEq, and_true] at hEqC
    obtain ⟨rfl, rfl, rfl⟩ := hEqC
    dsimp only at hCopied hFrC
    have hPTW : pTable < 2 ^ w := by dsimp only [pTable]; omega
    refine runs_seq_assign_le (v := pTable)
      (by simp [Expr.eval, st0, startState, pTable, xBuf, hw1, hX1W, hPTW]) ?_
    refine runs_seq_store_le (x := pTable) (v := k) (by simp [Expr.eval])
      (by simp [Expr.eval, st0, startState]) ?_
    refine runs_seq_assign_le (v := 2 * k)
      (by simp [Expr.eval, st0, startState, ← Nat.two_mul, h2KW]) ?_
    have hPT1W : pTable + 1 < 2 ^ w := by dsimp only [pTable]; omega
    have hCur0W : pTable + 1 + 2 * k < 2 ^ w := by dsimp only [pTable]; omega
    refine runs_seq_assign_le (v := bridgePairCur pTable k pairs 0)
      (by rw [bridgePairCur_zero]; simp [Expr.eval, hw1, hPT1W, hCur0W]) ?_
    have hP2KW : pAddr + 2 * k < 2 ^ w := by omega
    refine runs_seq_assign_le (v := dataBase)
      (by simp [Expr.eval, st0, startState, dataBase, hw1, hP2KW, hDBW]) ?_
    refine runs_assign_le (v := 0) (by simp [Expr.eval]) ?_ ?_
    · refine ⟨rfl, fun r hr => ?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        ?_, by simp, ?_, ?_⟩
      · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 19),
          Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 17),
          Function.update_of_ne (by omega : r ≠ 11), Function.update_of_ne (by omega : r ≠ 16),
          Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 15)]
      · refine ⟨?_, fun j hj => ?_⟩
        · dsimp only
          rw [Function.update_of_ne (by dsimp only [pTable, xBuf]; omega),
            hFrC xBuf (Or.inl (by omega)), Function.update_self, hXlen]
        · rw [hXlen] at hj
          dsimp only
          rw [Function.update_of_ne (by dsimp only [pTable, xBuf]; omega),
            hCopied j hj, Function.update_of_ne (by omega)]
          exact hX j (by rw [hXlen]; exact hj)
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by dsimp only [pTable]; omega),
          hFrC a (Or.inl (by dsimp only [xBuf]; omega)),
          Function.update_of_ne (by dsimp only [xBuf]; omega)]
        rfl
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega),
          hFrC a (Or.inr (by dsimp only [pTable, xBuf] at ha ⊢; omega)),
          Function.update_of_ne (by dsimp only [pTable, xBuf] at ha ⊢; omega)]
        exact hZ a (by dsimp only [pTable] at ha; omega)
    · simp only [buildCopyContract, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
      omega
  rcases hPreRun with ⟨st1, c1, hrun1, hr1_lo, hr1_10, hr1_11, hr1_15, hr1_17, hr1_18, hr1_19,
    hr1_20, hSeqX1, hPTk1, hFr1, hZ1, hc1⟩
  -- Inductive loop over `j = 0 .. 2 * k`
  have hLoopInd : ∀ rem j (st : State),
      (hj : j + rem = 2 * k) →
      (∀ r ≤ 9, st.regs r = st0.regs r) →
      st.regs 10 = xBuf → st.regs 11 = pTable → st.regs 15 = G.n →
      st.regs 17 = 2 * k → st.regs 18 = bridgePairCur pTable k pairs j →
      st.regs 19 = dataBase → st.regs 20 = j →
      (∀ a < pTable + 1, st.mem a = st1.mem a) →
      (∀ t (ht : t < j),
        let addr := bridgePairCur pTable k pairs t
        st.mem (pTable + 1 + t) = addr ∧
        SeqAt st.mem addr ((pairsSections pairs)[t]'(by rw [pairsSections_length]; omega))) →
      ZeroFrom st.mem (bridgePairCur pTable k pairs j) →
      ∃ st2 c2,
        Runs w p ω (.loop (.bin .lt (.reg 20) (.reg 17)) (bridgePairsLoopBody fCopy))
          st .normal st2 c2 ∧
        (∀ r ≤ 9, st2.regs r = st0.regs r) ∧
        st2.regs 10 = xBuf ∧ st2.regs 11 = pTable ∧ st2.regs 15 = G.n ∧
        st2.regs 18 = curEnd ∧
        (∀ a < pTable + 1, st2.mem a = st1.mem a) ∧
        (∀ t (ht : t < 2 * k),
          let addr := bridgePairCur pTable k pairs t
          st2.mem (pTable + 1 + t) = addr ∧
          SeqAt st2.mem addr ((pairsSections pairs)[t]'(by rw [pairsSections_length]; omega))) ∧
        ZeroFrom st2.mem curEnd ∧
        c2 ≤ 80 * rem + 17 * (((pairsSections pairs).drop j).map List.length).sum + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro j st hj hrlo hr10 hr11 hr15 hr17 hr18 hr19 hr20 hfr htab hz
      have hjeq : j = 2 * k := by omega
      subst hjeq
      have hcond0 : (Expr.bin .lt (.reg 20) (.reg 17)).eval w st = some 0 := by
        simp [Expr.eval, BinOp.eval, hr20, hr17]
      exact ⟨st, _, runs_loop_zero_in hcond0, hrlo, hr10, hr11, hr15, hr18, hfr, htab, hz,
        by simp [Expr.size]⟩
    | succ rem ih =>
      intro j st hj hrlo hr10 hr11 hr15 hr17 hr18 hr19 hr20 hfr htab hz
      have hj_lt : j < 2 * k := by omega
      have hcond1 : (Expr.bin .lt (.reg 20) (.reg 17)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hr20, hr17, hj_lt, hw1]
      set sec := (pairsSections pairs)[j]'(by rw [pairsSections_length]; exact hj_lt)
      set o0 := pairsSecOff pairs j
      set o1 := pairsSecOff pairs (j + 1)
      set cur := bridgePairCur pTable k pairs j
      set curNext := bridgePairCur pTable k pairs (j + 1)
      have ho1_eq : o1 = o0 + sec.length := pairsSecOff_succ hj_lt
      have hcur_next : curNext = cur + 1 + sec.length := bridgePairCur_succ pTable k pairs hj_lt
      have hcur_next_le : curNext ≤ pTable + 1 + 2 * k + pLen :=
        bridgePairCur_le_end pTable pairs (by omega)
      have hmo0 : st.mem (pAddr + j) = o0 := by
        rw [hfr _ (by dsimp only [pTable]; omega), hFr1 _ (by omega)]
        exact pairsWords_offset_eq hP (by omega)
      have hmo1 : st.mem (pAddr + j + 1) = o1 := by
        rw [hfr _ (by dsimp only [pTable]; omega), hFr1 _ (by omega), Nat.add_assoc]
        exact pairsWords_offset_eq hP (by omega)
      have hSecAt : ListAt st.mem (dataBase + o0) sec := by
        have h0 := pairsWords_section_listAt hP hj_lt
        have hle : dataBase + o0 + sec.length ≤ pAddr + pLen := by
          have := pairsSecOff_le_total pairs (j + 1)
          dsimp only [dataBase, o0, o1, sec] at ho1_eq ⊢; omega
        intro u hu
        rw [hfr _ (by dsimp only [pTable]; omega), hFr1 _ (by omega)]
        exact h0 u hu
      have hr2 : st.regs 2 = pAddr := by rw [hrlo 2 (by decide)]; rfl
      have hBody : ∃ stB cB,
          Runs w p ω (bridgePairsLoopBody fCopy) st .normal stB cB ∧
          (∀ r ≤ 9, stB.regs r = st0.regs r) ∧
          stB.regs 10 = xBuf ∧ stB.regs 11 = pTable ∧ stB.regs 15 = G.n ∧
          stB.regs 17 = 2 * k ∧ stB.regs 18 = curNext ∧
          stB.regs 19 = dataBase ∧ stB.regs 20 = j + 1 ∧
          (∀ a < pTable + 1, stB.mem a = st1.mem a) ∧
          (∀ t (ht : t < j + 1),
            let addr := bridgePairCur pTable k pairs t
            stB.mem (pTable + 1 + t) = addr ∧
            SeqAt stB.mem addr ((pairsSections pairs)[t]'(by rw [pairsSections_length]; omega))) ∧
          ZeroFrom stB.mem curNext ∧
          cB ≤ 72 + 17 * sec.length := by
        suffices hB : ∃ o stB cB,
            Runs w p ω (bridgePairsLoopBody fCopy) st o stB cB ∧
            (o = .normal ∧
             (∀ r ≤ 9, stB.regs r = st0.regs r) ∧
             stB.regs 10 = xBuf ∧ stB.regs 11 = pTable ∧ stB.regs 15 = G.n ∧
             stB.regs 17 = 2 * k ∧ stB.regs 18 = curNext ∧
             stB.regs 19 = dataBase ∧ stB.regs 20 = j + 1 ∧
             (∀ a < pTable + 1, stB.mem a = st1.mem a) ∧
             (∀ t (ht : t < j + 1),
               let addr := bridgePairCur pTable k pairs t
               stB.mem (pTable + 1 + t) = addr ∧
               SeqAt stB.mem addr ((pairsSections pairs)[t]'(by rw [pairsSections_length]; omega))) ∧
             ZeroFrom stB.mem curNext) ∧
            0 + cB ≤ 72 + 17 * sec.length by
          obtain ⟨_, stB, cB, hr, ⟨rfl, h1⟩, hc⟩ := hB
          exact ⟨stB, cB, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
            h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.1,
            h1.2.2.2.2.2.2.2.2.2.2, by omega⟩
        have hpjW : pAddr + j < 2 ^ w := by omega
        have hpj1W : pAddr + j + 1 < 2 ^ w := by omega
        have hlenW : sec.length < 2 ^ w := by dsimp only [pTable] at hcur_next_le; omega
        have hpt1W : pTable + 1 < 2 ^ w := by dsimp only [pTable]; omega
        have hpt1jW : pTable + 1 + j < 2 ^ w := by dsimp only [pTable]; omega
        have hcur1W : cur + 1 < 2 ^ w := by dsimp only [pTable] at hcur_next_le; omega
        have hcurNW : curNext < 2 ^ w := by dsimp only [pTable] at hcur_next_le; omega
        have hsrcW : dataBase + o0 < 2 ^ w := by
          have := pairsSecOff_le_total pairs j; dsimp only [dataBase, o0]; omega
        have hsrcEnd : dataBase + o0 + sec.length ≤ cur + 1 := by
          have := pairsSecOff_le_total pairs (j + 1)
          have hcurGe : pTable + 1 + 2 * k ≤ cur := by dsimp only [cur, bridgePairCur]; omega
          dsimp only [dataBase, o0, o1, pTable] at ho1_eq ⊢; omega
        unfold bridgePairsLoopBody
        refine runs_seq_assign_le (v := o0)
          (by simp [Expr.eval, BinOp.eval, hr2, hr20, hpjW, hmo0]) ?_
        refine runs_seq_assign_le (v := o1)
          (by simp [Expr.eval, BinOp.eval, hr2, hr20, hpjW, hpj1W, hw1, hmo1]) ?_
        refine runs_seq_assign_le (v := sec.length)
          (by simp [Expr.eval, BinOp.eval, ho1_eq, hlenW]) ?_
        refine runs_seq_store_le (x := pTable + 1 + j) (v := cur)
          (by simp [Expr.eval, BinOp.eval, hr11, hr20, hw1, hpt1W, hpt1jW])
          (by simp [Expr.eval, hr18]) ?_
        refine runs_seq_store_le (x := cur) (v := sec.length)
          (by simp [Expr.eval, hr18]) (by simp [Expr.eval]) ?_
        refine runs_seq_call_le hCopyMC (vs := [dataBase + o0, sec.length, cur + 1])
          (by simp [evalArgs, Expr.eval, BinOp.eval, hr19, hr18, hw1, hsrcW, hcur1W])
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl <;> omega)
          ⟨dataBase + o0, sec.length, cur + 1, rfl, hsrcEnd, by omega, hw1⟩ ?_
        intro _ memB posB hPostB
        obtain ⟨_, _, _, hEqB, hCopB, hFrB⟩ := hPostB
        simp only [List.cons.injEq, and_true] at hEqB
        obtain ⟨rfl, rfl, rfl⟩ := hEqB
        dsimp only at hCopB hFrB
        refine runs_seq_assign_le (v := curNext)
          (by rw [hcur_next]; simp [Expr.eval, BinOp.eval, hr18, hw1, hcur1W,
            show cur + 1 + sec.length < 2 ^ w by omega]) ?_
        refine runs_assign_le (v := j + 1)
          (by simp [Expr.eval, BinOp.eval, hr20, hw1, show j + 1 < 2 ^ w by omega]) ?_ ?_
        · have hcur_ge_pt : pTable + 1 + 2 * k ≤ cur := by dsimp only [cur, bridgePairCur]; omega
          refine ⟨rfl, fun r hr => ?_, ?_, ?_, ?_, ?_, by simp, ?_, by simp, ?_, ?_, ?_⟩
          · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 18),
              Function.update_of_ne (by omega : r ≠ 16), Function.update_of_ne (by omega : r ≠ 23),
              Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21),
              hrlo r hr]
          · simp [hr10]
          · simp [hr11]
          · simp [hr15]
          · simp [hr17]
          · simp [hr19]
          · intro a ha
            dsimp only
            rw [hFrB a (Or.inl (by omega)), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hfr a ha
          · intro t ht
            by_cases htj : t = j
            · subst htj
              refine ⟨?_, ?_, fun u hu => ?_⟩
              · dsimp only
                rw [hFrB _ (Or.inl (by omega)), Function.update_of_ne (by omega), Function.update_self]
              · dsimp only
                rw [hFrB cur (Or.inl (by omega)), Function.update_self]
              · dsimp only
                have hu' : u < sec.length := hu
                have hsrc_lt_h : dataBase + o0 + sec.length ≤ h := by
                  have := pairsSecOff_le_total pairs (t + 1)
                  dsimp only [dataBase, o0, o1, sec] at ho1_eq ⊢; omega
                have hpt_gt_h : h < pTable := by dsimp only [pTable]; omega
                rw [hCopB u hu, Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hSecAt u hu
            · have ht_lt : t < j := by omega
              have hprev := htab t ht_lt
              set prevCur := bridgePairCur pTable k pairs t
              have hprev_end : prevCur + 1 +
                  ((pairsSections pairs)[t]'(by rw [pairsSections_length]; omega)).length ≤ cur := by
                have hs := bridgePairCur_succ pTable k pairs (show t < 2 * k by omega)
                have hmono : bridgePairCur pTable k pairs (t + 1) ≤ cur := by
                  dsimp only [cur, bridgePairCur]
                  have htake : pairsSecOff pairs (t + 1) ≤ pairsSecOff pairs j := by
                    unfold pairsSecOff
                    have hsplit : (pairsSections pairs).take j =
                        (pairsSections pairs).take (t + 1) ++
                          ((pairsSections pairs).take j).drop (t + 1) := by
                      have h1 := (List.take_append_drop (t + 1) ((pairsSections pairs).take j)).symm
                      rw [List.take_take, Nat.min_eq_left (by omega)] at h1
                      exact h1
                    rw [hsplit, List.map_append, List.sum_append]; omega
                  omega
                omega
              have hprev_ge : pTable + 1 + 2 * k ≤ prevCur := by
                dsimp only [prevCur, bridgePairCur]; omega
              refine ⟨?_, ?_, fun u hu => ?_⟩
              · dsimp only
                rw [hFrB _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hprev.1
              · dsimp only
                rw [hFrB _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hprev.2.1
              · dsimp only
                rw [hFrB _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hprev.2.2 u hu
          · intro a ha
            dsimp only
            rw [hFrB a (Or.inr (by omega)), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hz a (by omega)
        · simp only [buildCopyContract, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
          omega
      rcases hBody with ⟨stB, cB, hrunB, hrBlo, hrB10, hrB11, hrB15, hrB17, hrB18, hrB19, hrB20,
        hBfr, hBtab, hBz, hcB⟩
      obtain ⟨st2, c2, hrun2, hr2lo, hr2_10, hr2_11, hr2_15, hr2_18, h2fr, h2tab, h2z, hc2⟩ :=
        ih (j + 1) stB (by omega) hrBlo hrB10 hrB11 hrB15 hrB17 hrB18 hrB19 hrB20 hBfr hBtab hBz
      have hdrop : (((pairsSections pairs).drop j).map List.length).sum =
          sec.length + (((pairsSections pairs).drop (j + 1)).map List.length).sum := by
        have hcons : (pairsSections pairs).drop j = sec :: (pairsSections pairs).drop (j + 1) :=
          List.drop_eq_getElem_cons (by rw [pairsSections_length]; exact hj_lt)
        rw [hcons, List.map_cons, List.sum_cons]
      refine ⟨st2, _, runs_loop_step_in hcond1 (by decide) hrunB hrun2, hr2lo, hr2_10, hr2_11,
        hr2_15, hr2_18, h2fr, h2tab, h2z, ?_⟩
      simp only [Expr.size]
      omega
  obtain ⟨st2, c2, hrun2, hr2lo, hr2_10, hr2_11, hr2_15, hr2_18, h2fr, h2tab, h2z, hc2⟩ :=
    hLoopInd (2 * k) 0 st1 (by omega) hr1_lo hr1_10 hr1_11 hr1_15 hr1_17 hr1_18 hr1_19 hr1_20
      (fun _ _ => rfl) (fun _ ht => absurd ht (Nat.not_lt_zero _))
      (fun a ha => hZ1 a (by rw [bridgePairCur_zero] at ha; omega))
  -- Tail: compute outAddr = curEnd + 5 and hInner = outAddr + 2 + 2 * G.n
  have hTail : ∃ st3 c3,
      Runs w p ω
        (.assign 12 (.bin .add (.reg 18) (.const 5)) ;;
         .assign 13 (.bin .add (.bin .add (.reg 12) (.const 2)) (.bin .add (.reg 15) (.reg 15))))
        st2 .normal st3 c3 ∧
      st3.mem = st2.mem ∧
      (∀ r ≤ 9, st3.regs r = st0.regs r) ∧
      st3.regs 10 = xBuf ∧ st3.regs 11 = pTable ∧
      st3.regs 12 = outAddr ∧ st3.regs 13 = hInner ∧ st3.regs 15 = G.n ∧
      c3 ≤ 25 := by
    suffices hT : ∃ o st3 c3,
        Runs w p ω
          (.assign 12 (.bin .add (.reg 18) (.const 5)) ;;
           .assign 13 (.bin .add (.bin .add (.reg 12) (.const 2)) (.bin .add (.reg 15) (.reg 15))))
          st2 o st3 c3 ∧
        (o = .normal ∧ st3.mem = st2.mem ∧ (∀ r ≤ 9, st3.regs r = st0.regs r) ∧
         st3.regs 10 = xBuf ∧ st3.regs 11 = pTable ∧
         st3.regs 12 = outAddr ∧ st3.regs 13 = hInner ∧ st3.regs 15 = G.n) ∧
        0 + c3 ≤ 25 by
      obtain ⟨_, st3, c3, hr, ⟨rfl, h1⟩, hc⟩ := hT
      exact ⟨st3, c3, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
        h1.2.2.2.2.2.2, by omega⟩
    refine runs_seq_assign_le (v := outAddr)
      (by simp [Expr.eval, BinOp.eval, hr2_18, hw5, outAddr, hOutW]) ?_
    refine runs_assign_le (v := hInner)
      (by simp [Expr.eval, BinOp.eval, hr2_15, show 2 < 2 ^ w by omega,
        show outAddr + 2 < 2 ^ w by omega, ← Nat.two_mul, h2GnW, hInner, hInnerW]) ?_
      (by simp [Expr.size])
    refine ⟨rfl, rfl, fun r hr => ?_, by simp [hr2_10], by simp [hr2_11], by simp, by simp,
      by simp [hr2_15]⟩
    simp [Function.update_of_ne (by omega : r ≠ 13), Function.update_of_ne (by omega : r ≠ 12),
      hr2lo r hr]
  rcases hTail with ⟨st3, c3, hrun3, hmem3, hr3lo, hr3_10, hr3_11, hr3_12, hr3_13, hr3_15, hc3⟩
  -- Assemble full run of `bridgePrepInputsStmt`
  have hFull : Runs w p ω (bridgePrepInputsStmt fCopy) st0 .normal st3 (c1 + (c2 + c3 + 1) + 1) := by
    unfold bridgePrepInputsStmt bridgePrepPrefix bridgePrepTail
    have h12 : Runs w p ω
        ((.loop (.bin .lt (.reg 20) (.reg 17)) (bridgePairsLoopBody fCopy)) ;;
         (.assign 12 (.bin .add (.reg 18) (.const 5)) ;;
          .assign 13 (.bin .add (.bin .add (.reg 12) (.const 2)) (.bin .add (.reg 15) (.reg 15)))))
        st1 .normal st3 (c2 + c3 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3, hrun2, hrun3, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + c3 + 1, hrun1, h12, rfl⟩)
  -- Build `VertSetAt`, `PairsAt`, `PairsBounded` on `st3.mem`
  have hVertSet : VertSetAt st3.mem xBuf X := by
    refine ⟨finsetWords X, Finset.sort_nodup X (· ≤ ·), Finset.sort_toFinset X (· ≤ ·), ?_⟩
    rw [hmem3]
    refine ⟨(h2fr xBuf (by dsimp only [pTable, xBuf]; omega)).trans hSeqX1.1, fun j hj => ?_⟩
    rw [h2fr _ (by dsimp only [pTable, xBuf]; rw [hXlen] at hj; omega)]
    exact hSeqX1.2 j hj
  have hPairsAt : PairsAt st3.mem pTable pairs := by
    rw [hmem3]
    refine ⟨(h2fr pTable (by omega)).trans hPTk1, fun i hi => ?_⟩
    have he := h2tab (2 * i) (by omega)
    have ho := h2tab (2 * i + 1) (by omega)
    have hEv := pairsSections_getElem_even hi
    have hOd := pairsSections_getElem_odd hi
    rw [hEv] at he
    rw [hOd] at ho
    refine ⟨?_, ?_⟩
    · rw [he.1]
      exact ⟨finsetWords (pairs[i]'hi).1, Finset.sort_nodup _ _, Finset.sort_toFinset _ _, he.2⟩
    · have hidx : pTable + 2 + 2 * i = pTable + 1 + (2 * i + 1) := by omega
      rw [hidx, ho.1]
      exact ⟨finsetWords (pairs[i]'hi).2, Finset.sort_nodup _ _, Finset.sort_toFinset _ _, ho.2⟩
  have hPairsBnd : PairsBounded st3.mem pTable pairs outAddr := by
    rw [hmem3]
    refine ⟨by dsimp only [outAddr, curEnd, bridgePairCur]; omega, fun i hi => ?_⟩
    have he := h2tab (2 * i) (by omega)
    have ho := h2tab (2 * i + 1) (by omega)
    have hEv := pairsSections_getElem_even hi
    have hOd := pairsSections_getElem_odd hi
    have hidx : pTable + 2 + 2 * i = pTable + 1 + (2 * i + 1) := by omega
    rw [he.1, hidx, ho.1]
    have hs1 := bridgePairCur_succ pTable k pairs (show 2 * i < 2 * k by omega)
    have hs2 := bridgePairCur_succ pTable k pairs (show 2 * i + 1 < 2 * k by omega)
    rw [hEv, finsetWords, Finset.length_sort] at hs1
    rw [hOd, finsetWords, Finset.length_sort] at hs2
    have h2i2 : 2 * i + 1 + 1 = 2 * i + 2 := by omega
    rw [h2i2] at hs2
    have hmono1 : bridgePairCur pTable k pairs (2 * i + 1) ≤ curEnd := by
      dsimp only [curEnd, bridgePairCur]
      have h1 := pairsSecOff_le_total pairs (2 * i + 1)
      have h2 : pairsSecOff pairs (2 * k) = ((pairsSections pairs).map List.length).sum := by
        unfold pairsSecOff; rw [← pairsSections_length, List.take_length]
      omega
    have hmono2 : bridgePairCur pTable k pairs (2 * i + 2) ≤ curEnd := by
      dsimp only [curEnd, bridgePairCur]
      have h1 := pairsSecOff_le_total pairs (2 * i + 2)
      have h2 : pairsSecOff pairs (2 * k) = ((pairsSections pairs).map List.length).sum := by
        unfold pairsSecOff; rw [← pairsSections_length, List.take_length]
      omega
    dsimp only [outAddr]; omega
  refine ⟨st3, _, hFull, hr3lo, hr3_10, hr3_11, hr3_12, hr3_13, hr3_15, hVertSet, hPairsAt,
    hPairsBnd, hCurEndLe, fun a ha => ?_, fun a ha => by rw [hmem3]; exact h2z a ha, ?_⟩
  · rw [hmem3, h2fr a (by dsimp only [pTable]; omega), hFr1 a ha]
  · simp only [List.drop_zero] at hc2
    omega

end MinCostFlow.HierPaths
