module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Bundle.Ordered
public import WordRAM.CopyWords
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# `Update` copies the inserted entries of the gradient and length arrays

The caller of `Update` passes its gradient and length arrays `g` and `l`, each with `m` blocks
of `L` limbs. The contract places them below `heap`, as it places the solver's footprint, but it
does not say that they miss the footprint. So once `Update` writes into its footprint, it may
change the caller's arrays. `Update` needs only the entries at the edges that the batch inserts:
for every other live edge, the caller's values equal the values the solver stored before
(`MinRatio/OrdSolverHistory.lean`). So, before it writes anything below `heap`, `Update` copies
those entries above `heap`.

The copy goes into two shadow arrays `gC` and `lC` with the same layout as `g` and `l`: the
block of edge `e` is at `gC + e * L`. The memory above `heap` is zero, so the blocks that are
not written need no initialisation. The loop `copyInsertedStmt` walks the batch records once.
For an insertion of an edge `e < m` it copies the two blocks of `e` with `copyWords`. A batch with
`|U|` records costs `O(|U| · L)` steps (`copyInsertedStmt_runs`). The main result of this file is
`copyInsertedStmt_runs`, and its reading in terms of `readVector` is
`readVector_copyInserted`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle IPM.Machine

/-- One record of the copy loop. Register `43` points to the current record of the batch, `40`
holds `m`, `7` holds `L`, `2` and `3` hold `g` and `l`, and `41` and `42` hold the shadow arrays.
An insertion of an edge `e < m` copies the blocks of `e`. Every record then moves the pointer
past itself (`4` words for an insertion, `2` for a deletion). -/
@[expose] def copyInsertedStep (copyWords : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.reg 43)) (.const 0))
    (.assign 45 (.load (.bin .add (.reg 43) (.const 1))) ;;
     .cond (.bin .lt (.reg 45) (.reg 40))
       (.assign 47 (.bin .mul (.reg 45) (.reg 7)) ;;
        .call 30 copyWords [.bin .add (.reg 2) (.reg 47), .bin .add (.reg 41) (.reg 47), .reg 7] ;;
        .call 30 copyWords [.bin .add (.reg 3) (.reg 47), .bin .add (.reg 42) (.reg 47), .reg 7])
       .nop ;;
     .assign 43 (.bin .add (.reg 43) (.const 4)))
    (.assign 43 (.bin .add (.reg 43) (.const 2)))

/-- The copy step of `Update`. Register `6` holds the solver's handle, whose word `9` is `m`.
Register `32` holds the saved batch and `18` its reserved length, so the shadow array `gC`
starts right after it. Register `16` gets the first free address after the two shadow arrays. -/
@[expose] def copyInsertedStmt (copyWords : ℕ) : Stmt :=
  .assign 40 (.load (.bin .add (.reg 6) (.const 9))) ;;
  .assign 46 (.bin .mul (.reg 40) (.reg 7)) ;;
  .assign 41 (.bin .add (.reg 32) (.reg 18)) ;;
  .assign 42 (.bin .add (.reg 41) (.reg 46)) ;;
  .assign 16 (.bin .add (.reg 42) (.reg 46)) ;;
  .assign 43 (.bin .add (.reg 32) (.const 1)) ;;
  forRange 44 (.const 0) (.reg 12) (copyInsertedStep copyWords)

theorem copyInsertedStmt_noRand (copyWords : ℕ) : (copyInsertedStmt copyWords).NoRand := by
  unfold copyInsertedStmt copyInsertedStep forRange forUp
  repeat (first | exact trivial | constructor)

/-- The offset of record `k` in the body of a batch. -/
private def recOff (U : List Update) (k : ℕ) : ℕ := ((U.take k).flatMap updateWords).length

private theorem recOff_succ {U : List Update} {k : ℕ} (hk : k < U.length) :
    recOff U (k + 1) = recOff U k + (updateWords U[k]).length := by
  unfold recOff
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp

private theorem recOff_le (U : List Update) (k : ℕ) : 1 + recOff U k ≤ (batchWords U).length := by
  have hfl : U.flatMap updateWords =
      (U.take k).flatMap updateWords ++ (U.drop k).flatMap updateWords := by
    conv_lhs => rw [← List.take_append_drop k U]
    rw [List.flatMap_append]
  simp only [batchWords, List.length_cons, hfl, List.length_append, recOff]
  omega

/-- The words of record `k` of a batch in memory. -/
private theorem batchAt_record {mem : ℕ → ℕ} {a : ℕ} {U : List Update} (hb : BatchAt mem a U)
    {k : ℕ} (hk : k < U.length) {j : ℕ} (hj : j < (updateWords U[k]).length) :
    mem (a + 1 + recOff U k + j) = (updateWords U[k])[j] ∧
      1 + recOff U k + j < (batchWords U).length := by
  have hsplit : U = U.take k ++ U[k] :: U.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hfl : U.flatMap updateWords =
      (U.take k).flatMap updateWords ++
        (updateWords U[k] ++ (U.drop (k + 1)).flatMap updateWords) := by
    conv_lhs => rw [hsplit]
    rw [List.flatMap_append, List.flatMap_cons]
  have hidx : 1 + recOff U k + j < (batchWords U).length := by
    simp only [batchWords, List.length_cons, hfl, List.length_append, recOff]
    omega
  refine ⟨?_, hidx⟩
  have hread := hb (1 + recOff U k + j) hidx
  rw [show a + 1 + recOff U k + j = a + (1 + recOff U k + j) by omega, hread]
  have hbw : batchWords U = U.length :: (((U.take k).flatMap updateWords) ++
      (updateWords U[k] ++ (U.drop (k + 1)).flatMap updateWords)) := by
    rw [batchWords, hfl]
  simp only [hbw, show 1 + recOff U k + j = (recOff U k + j) + 1 by omega,
    List.getElem_cons_succ]
  rw [List.getElem_append_right (by simp [recOff])]
  simp only [show recOff U k + j - ((U.take k).flatMap updateWords).length = j by
    simp [recOff]]
  rw [List.getElem_append_left hj]

/-- Two blocks of `L` words of different indices do not meet. -/
private theorem block_ne {e e' L j j' : ℕ} (hne : e ≠ e') (hj : j < L) (hj' : j' < L) :
    e * L + j ≠ e' * L + j' := by
  intro h
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  · have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega

/-- A block of index `e < m` lies inside the array of `m` blocks. -/
private theorem block_lt {e m L j : ℕ} (he : e < m) (hj : j < L) : e * L + j < m * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at this
  omega

/-- Run of `copyInsertedStmt`. With `gC` the end of the saved batch and `lC = gC + m * L`, the
loop leaves the memory outside `[gC, lC + m * L)` unchanged, and for every edge `e < m` that
the batch inserts, the blocks of `e` in `gC` and `lC` are those of `g` and `l`. It changes only
registers `16`, `30` and those from `40` on. It costs at most `|U| (34 L + 100) + 50` steps. -/
theorem copyInsertedStmt_runs {w copyWords handle m L g l bs copyLen : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State} {U : List Update}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hr2 : st.regs 2 = g) (hr3 : st.regs 3 = l) (hr6 : st.regs 6 = handle)
    (hr7 : st.regs 7 = L) (hr12 : st.regs 12 = U.length) (hr18 : st.regs 18 = copyLen)
    (hr32 : st.regs 32 = bs)
    (hm : st.mem (handle + 9) = m) (hhW : handle + 9 < 2 ^ w)
    (hbatch : BatchAt st.mem bs U) (hedge : ∀ u ∈ U, IsEdgeUpdate u)
    (hwords : ∀ x ∈ batchWords U, x < 2 ^ w)
    (hlen : (batchWords U).length ≤ copyLen)
    (hg : g + m * L ≤ bs + copyLen) (hl : l + m * L ≤ bs + copyLen)
    (hroomW : bs + copyLen + 2 * (m * L) < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    let gC := bs + copyLen
    let lC := gC + m * L
    ∃ st' c, Runs w p ω (copyInsertedStmt copyWords) st .normal st' c ∧
      (∀ r, r ≠ 16 → r ≠ 30 → r < 40 → st'.regs r = st.regs r) ∧
      st'.regs 16 = lC + m * L ∧ st'.regs 41 = gC ∧ st'.regs 42 = lC ∧
      (∀ a, (a < gC ∨ lC + m * L ≤ a) → st'.mem a = st.mem a) ∧
      (∀ e < m, (∃ u ∈ U, u.Inserts e) → ∀ j < L,
        st'.mem (gC + e * L + j) = st.mem (g + e * L + j) ∧
          st'.mem (lC + e * L + j) = st.mem (l + e * L + j)) ∧
      c ≤ U.length * (34 * L + 100) + 50 := by
  intro gC lC
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hmLW : m * L < 2 ^ w := by omega
  have hgCW : gC < 2 ^ w := by omega
  have hlCW : lC < 2 ^ w := by omega
  have hendW : lC + m * L < 2 ^ w := by omega
  have hlenPos : 1 ≤ (batchWords U).length := by simp [batchWords]
  have hbs1W : bs + 1 < 2 ^ w := by omega
  have hUlenW : U.length < 2 ^ w := by
    have : U.length ∈ batchWords U := by simp [batchWords]
    exact hwords _ this
  -- The six setup assignments
  let R : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update st.regs 40 m) 46 (m * L)) 41 gC) 42 lC) 16 (lC + m * L)) 43 (bs + 1)
  let sI : State := { st with regs := R }
  have hsetup : ∀ st' c, Runs w p ω (forRange 44 (.const 0) (.reg 12) (copyInsertedStep copyWords))
      sI .normal st' c → Runs w p ω (copyInsertedStmt copyWords) st .normal st' (c + 31) := by
    intro st' c hrun
    let t1 : State := { st with regs := Function.update st.regs 40 m }
    let t2 : State := { t1 with regs := Function.update t1.regs 46 (m * L) }
    let t3 : State := { t2 with regs := Function.update t2.regs 41 gC }
    let t4 : State := { t3 with regs := Function.update t3.regs 42 lC }
    let t5 : State := { t4 with regs := Function.update t4.regs 16 (lC + m * L) }
    have q1 : Runs w p ω (.assign 40 (.load (.bin .add (.reg 6) (.const 9)))) st .normal t1 5 :=
      runs_assign_iff.mpr ⟨m, by
        simp [Expr.eval, BinOp.eval, hr6, hhW, show 9 < 2 ^ w by omega, hm], rfl, rfl, rfl⟩
    have q2 : Runs w p ω (.assign 46 (.bin .mul (.reg 40) (.reg 7))) t1 .normal t2 4 :=
      runs_assign_iff.mpr ⟨m * L, by simp [Expr.eval, BinOp.eval, t1, hr7, hmLW], rfl, rfl, rfl⟩
    have q3 : Runs w p ω (.assign 41 (.bin .add (.reg 32) (.reg 18))) t2 .normal t3 4 :=
      runs_assign_iff.mpr ⟨gC, by simp [Expr.eval, BinOp.eval, t2, t1, hr32, hr18, hgCW, gC],
        rfl, rfl, rfl⟩
    have q4 : Runs w p ω (.assign 42 (.bin .add (.reg 41) (.reg 46))) t3 .normal t4 4 :=
      runs_assign_iff.mpr ⟨lC, by simp [Expr.eval, BinOp.eval, t3, t2, hlCW, lC], rfl, rfl, rfl⟩
    have q5 : Runs w p ω (.assign 16 (.bin .add (.reg 42) (.reg 46))) t4 .normal t5 4 :=
      runs_assign_iff.mpr ⟨lC + m * L, by simp [Expr.eval, BinOp.eval, t4, t3, t2, hendW],
        rfl, rfl, rfl⟩
    have q6 : Runs w p ω (.assign 43 (.bin .add (.reg 32) (.const 1))) t5 .normal sI 4 :=
      runs_assign_iff.mpr ⟨bs + 1, by
        simp [Expr.eval, BinOp.eval, t5, t4, t3, t2, t1, hr32, hw1, hbs1W], rfl, rfl, rfl⟩
    have := runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, q1,
      runs_seq_iff.mpr (Or.inr ⟨t2, 4, _, q2,
      runs_seq_iff.mpr (Or.inr ⟨t3, 4, _, q3,
      runs_seq_iff.mpr (Or.inr ⟨t4, 4, _, q4,
      runs_seq_iff.mpr (Or.inr ⟨t5, 4, _, q5,
      runs_seq_iff.mpr (Or.inr ⟨sI, 4, c, q6, hrun, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    unfold copyInsertedStmt
    convert this using 1
    omega
  have hR2 : R 2 = g := by simp [R, hr2]
  have hR3 : R 3 = l := by simp [R, hr3]
  have hR7 : R 7 = L := by simp [R, hr7]
  have hR12 : R 12 = U.length := by simp [R, hr12]
  have hR40 : R 40 = m := by simp [R]
  have hR41 : R 41 = gC := by simp [R]
  have hR42 : R 42 = lC := by simp [R]
  -- The loop invariant after `k` records
  let Inv (k : ℕ) (s : State) : Prop :=
    (∀ r, r ≠ 30 → r ≠ 43 → r ≠ 44 → r ≠ 45 → r ≠ 47 → s.regs r = R r) ∧
    s.regs 43 = bs + 1 + recOff U k ∧ s.regs 44 = k ∧
    (∀ a, (a < gC ∨ lC + m * L ≤ a) → s.mem a = st.mem a) ∧
    (∀ e < m, (∃ u ∈ U.take k, u.Inserts e) → ∀ j < L,
      s.mem (gC + e * L + j) = st.mem (g + e * L + j) ∧
        s.mem (lC + e * L + j) = st.mem (l + e * L + j))
  have hstep : ∀ k, 0 ≤ k → k < U.length →
      Triple w p (Inv k) (copyInsertedStep copyWords)
        (normalPost fun s' =>
          Inv (k + 1) { s' with regs := Function.update s'.regs 44 (k + 1) } ∧ s'.regs 44 = k)
        (fun _ => 34 * L + 90) := by
    intro k _ hk s ω' hInv
    obtain ⟨hregs, h43, h44, hfr, hcp⟩ := hInv
    have hs2 : s.regs 2 = g := (hregs 2 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR2
    have hs3 : s.regs 3 = l := (hregs 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR3
    have hs7 : s.regs 7 = L := (hregs 7 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR7
    have hs40 : s.regs 40 = m := (hregs 40 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR40
    have hs41 : s.regs 41 = gC := (hregs 41 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR41
    have hs42 : s.regs 42 = lC := (hregs 42 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR42
    have hread (j : ℕ) (hj : j < (updateWords U[k]).length) :
        s.mem (bs + 1 + recOff U k + j) = (updateWords U[k])[j] ∧
          bs + 1 + recOff U k + j < 2 ^ w := by
      obtain ⟨h1, h2⟩ := batchAt_record hbatch hk hj
      refine ⟨(hfr _ (Or.inl (by omega))).trans h1, by omega⟩
    have htake : U.take (k + 1) = U.take k ++ [U[k]] := List.take_succ_eq_append_getElem hk
    have hOff := recOff_succ hk
    have hle := recOff_le U (k + 1)
    have hpW : bs + 1 + recOff U (k + 1) < 2 ^ w := by
      have : bs + copyLen < 2 ^ w := by omega
      omega
    have hedgeK := hedge U[k] (List.getElem_mem hk)
    cases hu : U[k] with
    | split _ _ _ _ => rw [hu] at hedgeK; exact hedgeK.elim
    | delete e =>
      obtain ⟨h0, _⟩ := hread 0 (by simp [hu, updateWords])
      simp only [hu, updateWords, List.getElem_cons_zero, Nat.add_zero] at h0
      rw [hu] at hOff
      simp only [updateWords, List.length_cons, List.length_nil] at hOff
      let s1 : State := { s with regs := Function.update s.regs 43 (bs + 1 + recOff U k + 2) }
      have q : Runs w p ω' (.assign 43 (.bin .add (.reg 43) (.const 2))) s .normal s1 4 :=
        runs_assign_iff.mpr ⟨bs + 1 + recOff U k + 2, by
          simp [Expr.eval, BinOp.eval, h43, hw2, show bs + 1 + recOff U k + 2 < 2 ^ w by omega],
          rfl, rfl, rfl⟩
      refine ⟨.normal, s1, 4 + 4 + 1, runs_cond_iff.mpr ⟨0, 4, ?_, by simpa using q, rfl⟩,
        ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, show 4 + 4 + 1 ≤ 34 * L + 90 by omega⟩
      · simp [Expr.eval, BinOp.eval, h43, h0, show 0 < 2 ^ w by omega, hw1]
      · intro r h30 h43' h44' h45 h47
        simp [s1, Function.update_of_ne h44', Function.update_of_ne h43', hregs r h30 h43' h44' h45 h47]
      · simp only [s1, Function.update_of_ne (show (43:ℕ) ≠ 44 by omega), Function.update_self]
        omega
      · simp
      · exact fun a ha => hfr a ha
      · intro e' he' hins j hj
        rw [htake] at hins
        obtain ⟨u, hu', hue⟩ := hins
        rcases List.mem_append.mp hu' with hu' | hu'
        · exact hcp e' he' ⟨u, hu', hue⟩ j hj
        · rw [List.mem_singleton.mp hu', hu] at hue; exact hue.elim
      · simpa [s1] using h44
    | insert e x y =>
      obtain ⟨h0, _⟩ := hread 0 (by simp [hu, updateWords])
      obtain ⟨h1, h1W⟩ := hread 1 (by simp [hu, updateWords])
      simp only [hu, updateWords, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
      rw [hu] at hOff
      simp only [updateWords, List.length_cons, List.length_nil] at hOff
      have hcond1 : (Expr.bin .eq (.load (.reg 43)) (.const 0)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, h43, h0, show 0 < 2 ^ w by omega, hw1]
      let s1 : State := { s with regs := Function.update s.regs 45 e }
      have q1 : Runs w p ω' (.assign 45 (.load (.bin .add (.reg 43) (.const 1)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨e, by
          simp [Expr.eval, BinOp.eval, h43, hw1, show bs + 1 + recOff U k + 1 < 2 ^ w by omega,
            h1], rfl, rfl, rfl⟩
      let pEnd : ℕ := bs + 1 + recOff U k + 4
      have hpEndW : pEnd < 2 ^ w := by dsimp only [pEnd]; omega
      -- The final assignment, from any state that keeps register `43`
      have qEnd : ∀ t : State, t.regs 43 = bs + 1 + recOff U k →
          Runs w p ω' (.assign 43 (.bin .add (.reg 43) (.const 4))) t .normal
            { t with regs := Function.update t.regs 43 pEnd } 4 := fun t ht =>
        runs_assign_iff.mpr ⟨pEnd, by simp [Expr.eval, BinOp.eval, ht, hw4, hpEndW, pEnd],
          rfl, rfl, rfl⟩
      by_cases hem : e < m
      · have hcond2 : (Expr.bin .lt (.reg 45) (.reg 40)).eval w s1 = some 1 := by
          simp [Expr.eval, BinOp.eval, s1, hs40, hem, hw1]
        have heLW : e * L + L ≤ m * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hem)
          rwa [Nat.succ_mul] at this
        let s2 : State := { s1 with regs := Function.update s1.regs 47 (e * L) }
        have q2 : Runs w p ω' (.assign 47 (.bin .mul (.reg 45) (.reg 7))) s1 .normal s2 4 :=
          runs_assign_iff.mpr ⟨e * L, by
            simp [Expr.eval, BinOp.eval, s1, hs7, show e * L < 2 ^ w by omega], rfl, rfl, rfl⟩
        obtain ⟨s3, c3, v3, q3, ⟨src3, dst3, len3, hargs3, _, hcp3, hfr3⟩, hr3', hro3, hc3⟩ :=
          runs_call_of_meetsContract (r := 30)
            (args := [.bin .add (.reg 2) (.reg 47), .bin .add (.reg 41) (.reg 47), .reg 7])
            (st := s2) (vs := [g + e * L, gC + e * L, L]) hCopy
            (by simp [evalArgs, Expr.eval, BinOp.eval, s2, s1, hs2, hs41, hs7,
                  show g + e * L < 2 ^ w by omega, show gC + e * L < 2 ^ w by omega])
            (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                rcases hv with rfl | rfl | rfl <;> omega)
            ⟨g + e * L, gC + e * L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩ ω'
        injection hargs3 with e1 t1; injection t1 with e2 t2; injection t2 with e3 _
        subst e1; subst e2; subst e3
        change c3 ≤ argsSize _ + (17 * L + 10) + 1 at hc3
        have hs3r (r : ℕ) (hr : r ≠ 30) : s3.regs r = s2.regs r := hro3 r hr
        obtain ⟨s4, c4, v4, q4, ⟨src4, dst4, len4, hargs4, _, hcp4, hfr4⟩, hr4', hro4, hc4⟩ :=
          runs_call_of_meetsContract (r := 30)
            (args := [.bin .add (.reg 3) (.reg 47), .bin .add (.reg 42) (.reg 47), .reg 7])
            (st := s3) (vs := [l + e * L, lC + e * L, L]) hCopy
            (by simp [evalArgs, Expr.eval, BinOp.eval, hs3r 3 (by omega), hs3r 47 (by omega),
                  hs3r 42 (by omega), hs3r 7 (by omega), s2, s1, hs3, hs42, hs7,
                  show l + e * L < 2 ^ w by omega, show lC + e * L < 2 ^ w by omega])
            (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                rcases hv with rfl | rfl | rfl <;> omega)
            ⟨l + e * L, lC + e * L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩ ω'
        injection hargs4 with e1 t1; injection t1 with e2 t2; injection t2 with e3 _
        subst e1; subst e2; subst e3
        change c4 ≤ argsSize _ + (17 * L + 10) + 1 at hc4
        have hs4r (r : ℕ) (hr : r ≠ 30) : s4.regs r = s2.regs r := (hro4 r hr).trans (hs3r r hr)
        have h43s4 : s4.regs 43 = bs + 1 + recOff U k := by
          rw [hs4r 43 (by omega)]; simpa [s2, s1] using h43
        let s5 : State := { s4 with regs := Function.update s4.regs 43 pEnd }
        have qIn : Runs w p ω' (.assign 47 (.bin .mul (.reg 45) (.reg 7)) ;;
            .call 30 copyWords [.bin .add (.reg 2) (.reg 47), .bin .add (.reg 41) (.reg 47), .reg 7] ;;
            .call 30 copyWords [.bin .add (.reg 3) (.reg 47), .bin .add (.reg 42) (.reg 47), .reg 7])
            s1 .normal s4 (4 + (c3 + c4 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, q2, runs_seq_iff.mpr (Or.inr ⟨s3, c3, c4, q3, q4, rfl⟩), rfl⟩)
        have qCond2 := (runs_cond_iff (t := .nop)).mpr ⟨1, _, hcond2, by simpa using qIn, rfl⟩
        have qThen := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, q1,
          runs_seq_iff.mpr (Or.inr ⟨s4, _, 4, qCond2, qEnd s4 h43s4, rfl⟩), rfl⟩)
        have hsz : argsSize [Expr.bin .add (.reg 2) (.reg 47), Expr.bin .add (.reg 41) (.reg 47),
            Expr.reg 7] = 7 := by simp [argsSize, Expr.size]
        have hsz' : argsSize [Expr.bin .add (.reg 3) (.reg 47), Expr.bin .add (.reg 42) (.reg 47),
            Expr.reg 7] = 7 := by simp [argsSize, Expr.size]
        rw [hsz] at hc3; rw [hsz'] at hc4
        refine ⟨.normal, s5, _, (runs_cond_iff (t := .assign 43 (.bin .add (.reg 43) (.const 2)))).mpr
          ⟨1, _, hcond1, by simpa using qThen, rfl⟩,
          ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · intro r h30 h43' h44' h45 h47
          simp only [s5, Function.update_of_ne h44', Function.update_of_ne h43']
          rw [hs4r r h30]
          simp [s2, s1, Function.update_of_ne h47, Function.update_of_ne h45,
            hregs r h30 h43' h44' h45 h47]
        · simp only [s5, Function.update_of_ne (show (43:ℕ) ≠ 44 by omega), Function.update_self, pEnd]
          omega
        · simp
        · intro a ha
          rw [hfr4 a (by rcases ha with ha | ha <;> [left; right] <;> omega),
            hfr3 a (by rcases ha with ha | ha <;> [left; right] <;> omega)]
          exact hfr a ha
        · intro e' he' hins j hj
          have hjB := block_lt he' hj
          have hA : ∀ a, a < gC → s4.mem a = s.mem a := fun a ha => by
            rw [hfr4 a (Or.inl (by omega)), hfr3 a (Or.inl (by omega))]
          by_cases hee : e' = e
          · subst hee
            refine ⟨?_, ?_⟩
            · simp only [s5]
              rw [hfr4 _ (Or.inl (by omega)), show gC + e' * L + j = gC + e' * L + j from rfl,
                hcp3 j hj, hfr _ (Or.inl (by omega))]
            · simp only [s5]
              rw [show lC + e' * L + j = lC + e' * L + j from rfl, hcp4 j hj,
                hfr3 _ (Or.inl (by omega)), hfr _ (Or.inl (by omega))]
          · have hold : ∃ u ∈ U.take k, u.Inserts e' := by
              rw [htake] at hins
              obtain ⟨u, hu', hue⟩ := hins
              rcases List.mem_append.mp hu' with hu' | hu'
              · exact ⟨u, hu', hue⟩
              · rw [List.mem_singleton.mp hu', hu] at hue; exact absurd hue.symm hee
            obtain ⟨hcg, hcl⟩ := hcp e' he' hold j hj
            have hne := fun j' (hj' : j' < L) => block_ne (L := L) (j := j) (j' := j') hee hj hj'
            refine ⟨?_, ?_⟩
            · simp only [s5]
              rw [hfr4 _ (Or.inl (by omega)), hfr3 _ ?_, hcg]
              by_contra hcon
              push_neg at hcon
              exact hne (gC + e' * L + j - (gC + e * L)) (by omega) (by omega)
            · simp only [s5]
              rw [hfr4 _ ?_, hfr3 _ (Or.inr (by omega)), hcl]
              by_contra hcon
              push_neg at hcon
              exact hne (lC + e' * L + j - (lC + e * L)) (by omega) (by omega)
        · simp [s5, hs4r 44 (by omega), s2, s1, h44]
        · show _ ≤ 34 * L + 90
          simp only [Expr.size, ↓reduceIte, Nat.one_ne_zero]
          omega
      · have hcond2 : (Expr.bin .lt (.reg 45) (.reg 40)).eval w s1 = some 0 := by
          simp [Expr.eval, BinOp.eval, s1, hs40, hem, show 0 < 2 ^ w by omega]
        have h43s1 : s1.regs 43 = bs + 1 + recOff U k := by simpa [s1] using h43
        let s5 : State := { s1 with regs := Function.update s1.regs 43 pEnd }
        have qCond2 := (runs_cond_iff (s := .assign 47 (.bin .mul (.reg 45) (.reg 7)) ;;
            .call 30 copyWords [.bin .add (.reg 2) (.reg 47), .bin .add (.reg 41) (.reg 47), .reg 7] ;;
            .call 30 copyWords [.bin .add (.reg 3) (.reg 47), .bin .add (.reg 42) (.reg 47), .reg 7])).mpr
          ⟨0, 1, hcond2, by simpa using
          (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w p ω' .nop s1 .normal s1 1), rfl⟩
        have qThen := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, q1,
          runs_seq_iff.mpr (Or.inr ⟨s1, _, 4, qCond2, qEnd s1 h43s1, rfl⟩), rfl⟩)
        refine ⟨.normal, s5, _, (runs_cond_iff (t := .assign 43 (.bin .add (.reg 43) (.const 2)))).mpr
          ⟨1, _, hcond1, by simpa using qThen, rfl⟩,
          ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · intro r h30 h43' h44' h45 h47
          simp [s5, s1, Function.update_of_ne h44', Function.update_of_ne h43',
            Function.update_of_ne h45, hregs r h30 h43' h44' h45 h47]
        · simp only [s5, Function.update_of_ne (show (43:ℕ) ≠ 44 by omega), Function.update_self, pEnd]
          omega
        · simp
        · exact fun a ha => hfr a ha
        · intro e' he' hins j hj
          have hold : ∃ u ∈ U.take k, u.Inserts e' := by
            rw [htake] at hins
            obtain ⟨u, hu', hue⟩ := hins
            rcases List.mem_append.mp hu' with hu' | hu'
            · exact ⟨u, hu', hue⟩
            · rw [List.mem_singleton.mp hu', hu] at hue
              exact absurd (hue ▸ he') hem
          exact hcp e' he' hold j hj
        · simp [s5, s1, h44]
        · simp [Expr.size]
  -- The loop
  have hloop := Triple.forRange_const (P := fun s => s = sI) (r := 44) (lo := .const 0)
    (hi := .reg 12) (body := copyInsertedStep copyWords) (Inv := Inv) (34 * L + 90) 0 U.length
    (Nat.zero_le _) hw1 (fun _ => hUlenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, ?_, ?_, ?_, ?_⟩
      · intro r _ h43 h44 _ _
        simp [sI, Function.update_of_ne h44]
      · simp [sI, R, recOff]
      · simp
      · exact fun _ _ => rfl
      · intro e _ hins
        simp at hins)
    (fun i s _ _ hI => hI.2.2.1)
    (fun i s _ _ hI => by
      simp [Expr.eval, (hI.1 12 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hR12])
    hstep
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := hloop sI ω rfl
  cases o with
  | returned v => exact hpost.elim
  | normal =>
    obtain ⟨hregs, _, _, hfr, hcp⟩ := hpost
    refine ⟨st', c + 31, hsetup st' c hrun, ?_, ?_, ?_, ?_, hfr, ?_, ?_⟩
    · intro r h16 h30 h40
      rw [hregs r h30 (by omega) (by omega) (by omega) (by omega)]
      simp [R, Function.update_of_ne (show r ≠ 43 by omega), Function.update_of_ne h16,
        Function.update_of_ne (show r ≠ 42 by omega), Function.update_of_ne (show r ≠ 41 by omega),
        Function.update_of_ne (show r ≠ 46 by omega), Function.update_of_ne (show r ≠ 40 by omega)]
    · rw [hregs 16 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [R]
    · rw [hregs 41 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hR41
    · rw [hregs 42 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hR42
    · intro e he hins j hj
      exact hcp e he (by rwa [List.take_length]) j hj
    · simp only [Expr.size, Nat.sub_zero] at hc
      have := Nat.mul_le_mul_left U.length (show 34 * L + 90 + 1 + 8 ≤ 34 * L + 100 by omega)
      omega

/-- A block of `L` limbs read at two addresses with the same words has the same value. -/
theorem fixVal_congr_block {m₁ m₂ : ℕ → ℕ} {a₁ a₂ h L P : ℕ}
    (hag : ∀ j < L, m₂ (a₂ + j) = m₁ (a₁ + j)) :
    Num.fixVal m₂ a₂ h L P = Num.fixVal m₁ a₁ h L P := by
  unfold Num.fixVal Num.intVal
  congr 3
  induction L generalizing a₁ a₂ with
  | zero => rfl
  | succ k ih =>
    simp only [Num.unsignedVal]
    rw [show m₂ a₂ = m₁ a₁ by simpa using hag 0 (Nat.zero_lt_succ k),
      ih (a₁ := a₁ + 1) (a₂ := a₂ + 1) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using hag (j + 1) (by omega)]

/-- The copied blocks, read as vectors: at every edge that the batch inserts, the shadow array
has the value of the caller's array. For an edge `e ≥ m` both reads are `0` by the definition
of `readVector`. For `e < m` the blocks agree word by word (`copyInsertedStmt_runs`). -/
theorem readVector_copyInserted {mem mem' : ℕ → ℕ} {src dst h L P m e : ℕ}
    (hcp : e < m → ∀ j < L, mem' (dst + e * L + j) = mem (src + e * L + j)) :
    readVector mem' dst h L P m e = readVector mem src h L P m e := by
  unfold readVector
  split_ifs with he
  · exact fixVal_congr_block fun j hj => by simpa [Nat.add_assoc] using hcp he j hj
  · rfl

end MinCostFlow.MinRatio

end
