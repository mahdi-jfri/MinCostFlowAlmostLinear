module

public import MinCostFlow.LSF.Program.InitTreeLSSTLiftBase
public import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# The edge arrays of `T₀`

After the `[AN19]` call, `T₀` is given by two lists in memory (`lsst_decode_lift`): the copies
`q` of edges of `G₀` that the tree uses, and the pairs of vertex indices joined by bridge edges.
A bridge edge gets the ID `eCap + z`, where `z` runs over the free slots of the bridge table.

`t0EdgesProc` writes the `tM = nOrig + nBr` edges of `T₀` as three arrays: the edge IDs
(`tOrig`), and the indices in `vList` of their tails and heads (`tTail`, `tHead`). The tree
edges come first, in the order of the output, and the bridge edges after them. The rooting
procedure (`RootTree.lean`) reads the index arrays, and the `T` block stores the ID array.
`t0Edges_meetsContract` proves the procedure correct; it runs in time `O(nOrig + ubLen)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-! ## The procedure -/

/-- One tree edge: copy `q = outOrig[i]` gives the ID `copyOrig[q]` and the end indices
`copyTail[q]`, `copyHead[q]`. Register `13` is `i`. -/
def t0OrigBody : Stmt :=
  .assign 16 (.load (.bin .add (.reg 2) (.reg 13))) ;;
  .store (.bin .add (.reg 10) (.reg 13)) (.load (.bin .add (.reg 6) (.reg 16))) ;;
  .store (.bin .add (.reg 11) (.reg 13)) (.load (.bin .add (.reg 4) (.reg 16))) ;;
  .store (.bin .add (.reg 12) (.reg 13)) (.load (.bin .add (.reg 5) (.reg 16)))

/-- One slot `z` (register `14`) of the bridge table: if fewer than `nBr` bridges are written
(register `15` counts them) and the slot is free, the next bridge gets the ID `eCap + z`. -/
def t0BrBody : Stmt :=
  .cond (.bin .lt (.reg 15) (.reg 1))
    (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 14))) (.const 0))
      (.assign 16 (.bin .add (.reg 0) (.reg 15)) ;;
       .store (.bin .add (.reg 10) (.reg 16)) (.bin .add (.reg 9) (.reg 14)) ;;
       .assign 17 (.bin .add (.reg 15) (.reg 15)) ;;
       .store (.bin .add (.reg 11) (.reg 16)) (.load (.bin .add (.reg 3) (.reg 17))) ;;
       .store (.bin .add (.reg 12) (.reg 16))
         (.load (.bin .add (.bin .add (.reg 3) (.reg 17)) (.const 1))) ;;
       .assign 15 (.bin .add (.reg 15) (.const 1)))
      .nop)
    .nop

/-- Args: `[nOrig, nBr, outOrigPtr, outBridgePtr, copyTailPtr, copyHeadPtr, copyOrigIdxPtr,
usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr, tHeadPtr]`. -/
def t0EdgesProc : Stmt :=
  forRange 13 (.const 0) (.reg 0) t0OrigBody ;;
  .assign 15 (.const 0) ;;
  forRange 14 (.const 0) (.reg 8) t0BrBody ;;
  .ret (.const 0)

lemma t0EdgesProc_noRand : t0EdgesProc.NoRand := by
  simp [t0EdgesProc, t0OrigBody, t0BrBody, forRange, forUp, Stmt.NoRand]

/-! ## Free slots of the bridge table -/

lemma zeroPositions_succ (mem : ℕ → ℕ) (u z : ℕ) :
    zeroPositions mem u (z + 1) =
      zeroPositions mem u z ++ (if mem (u + z) = 0 then [z] else []) := by
  unfold zeroPositions
  rw [List.range_succ, List.filter_append]
  by_cases h : mem (u + z) = 0 <;> simp [h]

lemma zeroPositions_getD_of_le (mem : ℕ → ℕ) (u : ℕ) {z z' j : ℕ} (hz : z ≤ z')
    (hj : j < (zeroPositions mem u z).length) :
    (zeroPositions mem u z').getD j 0 = (zeroPositions mem u z).getD j 0 := by
  induction z', hz using Nat.le_induction with
  | base => rfl
  | succ z' hle ih =>
    have hlen : (zeroPositions mem u z).length ≤ (zeroPositions mem u z').length := by
      unfold zeroPositions
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [List.range_add, List.filter_append, List.length_append]
      omega
    rw [zeroPositions_succ, List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_left (by omega), ← List.getD_eq_getElem _ _ (by omega), ih]

/-! ## Contract -/

/-- The contract of `t0EdgesProc`. -/
def t0EdgesContract (w : ℕ) : Contract where
  pre args mem := ∃ (nOrig nBr outOrigPtr outBridgePtr copyTailPtr copyHeadPtr copyOrigIdxPtr
      usedBridgePtr ubLen eCap tOrigPtr tTailPtr tHeadPtr M : ℕ),
    args = [nOrig, nBr, outOrigPtr, outBridgePtr, copyTailPtr, copyHeadPtr, copyOrigIdxPtr,
      usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr, tHeadPtr] ∧
    16 ≤ 2 ^ w ∧
    (∀ i < nOrig, mem (outOrigPtr + i) < M) ∧
    nBr ≤ (zeroPositions mem usedBridgePtr ubLen).length ∧
    outOrigPtr + nOrig ≤ tOrigPtr ∧ outBridgePtr + 2 * nBr ≤ tOrigPtr ∧
    copyTailPtr + M ≤ tOrigPtr ∧ copyHeadPtr + M ≤ tOrigPtr ∧ copyOrigIdxPtr + M ≤ tOrigPtr ∧
    usedBridgePtr + ubLen ≤ tOrigPtr ∧ eCap + ubLen < 2 ^ w ∧
    tOrigPtr + (nOrig + nBr) ≤ tTailPtr ∧ tTailPtr + (nOrig + nBr) ≤ tHeadPtr ∧
    tHeadPtr + (nOrig + nBr) < 2 ^ w
  post args mem ret mem' := ∃ (nOrig nBr outOrigPtr outBridgePtr copyTailPtr copyHeadPtr
      copyOrigIdxPtr usedBridgePtr ubLen eCap tOrigPtr tTailPtr tHeadPtr : ℕ),
    args = [nOrig, nBr, outOrigPtr, outBridgePtr, copyTailPtr, copyHeadPtr, copyOrigIdxPtr,
      usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr, tHeadPtr] ∧ ret = 0 ∧
    (∀ i < nOrig,
      mem' (tOrigPtr + i) = mem (copyOrigIdxPtr + mem (outOrigPtr + i)) ∧
      mem' (tTailPtr + i) = mem (copyTailPtr + mem (outOrigPtr + i)) ∧
      mem' (tHeadPtr + i) = mem (copyHeadPtr + mem (outOrigPtr + i))) ∧
    (∀ k < nBr,
      mem' (tOrigPtr + (nOrig + k)) = eCap + (zeroPositions mem usedBridgePtr ubLen).getD k 0 ∧
      mem' (tTailPtr + (nOrig + k)) = mem (outBridgePtr + 2 * k) ∧
      mem' (tHeadPtr + (nOrig + k)) = mem (outBridgePtr + 2 * k + 1)) ∧
    ∀ a, a < tOrigPtr ∨ tHeadPtr + (nOrig + nBr) ≤ a → mem' a = mem a
  cost args _ := 60 * args.getD 0 0 + 80 * args.getD 8 0 + 60

/-! ## Proof -/

/-- The argument registers `0, …, 12`. -/
def T0Regs (st : State) (args : List ℕ) : Prop := ∀ i < 13, st.regs i = args.getD i 0

lemma T0Regs.upd {st : State} {args : List ℕ} (h : T0Regs st args) (q v : ℕ) (hq : 13 ≤ q) :
    T0Regs { st with regs := Function.update st.regs q v } args := fun i hi => by
  simp only [Function.update_of_ne (show i ≠ q by omega)]; exact h i hi

lemma T0Regs.mem {st : State} {args : List ℕ} (h : T0Regs st args) (m : ℕ → ℕ) :
    T0Regs { st with mem := m } args := h

/-- The facts of the first loop for the tree edges `j < i`. -/
def T0OrigDone (mem₀ : ℕ → ℕ) (outOrigPtr copyTailPtr copyHeadPtr copyOrigIdxPtr tOrigPtr
    tTailPtr tHeadPtr : ℕ) (i : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ j < i,
    mem (tOrigPtr + j) = mem₀ (copyOrigIdxPtr + mem₀ (outOrigPtr + j)) ∧
    mem (tTailPtr + j) = mem₀ (copyTailPtr + mem₀ (outOrigPtr + j)) ∧
    mem (tHeadPtr + j) = mem₀ (copyHeadPtr + mem₀ (outOrigPtr + j))

/-- The facts of the second loop for the bridges `k < c`, where `Z` lists the free slots seen. -/
def T0BrDone (mem₀ : ℕ → ℕ) (nOrig outBridgePtr eCap tOrigPtr tTailPtr tHeadPtr : ℕ)
    (Z : List ℕ) (c : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ k < c,
    mem (tOrigPtr + (nOrig + k)) = eCap + Z.getD k 0 ∧
    mem (tTailPtr + (nOrig + k)) = mem₀ (outBridgePtr + 2 * k) ∧
    mem (tHeadPtr + (nOrig + k)) = mem₀ (outBridgePtr + 2 * k + 1)

theorem t0Edges_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some t0EdgesProc) :
    MeetsContract w p b (t0EdgesContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨nOrig, nBr, outOrigPtr, outBridgePtr, copyTailPtr, copyHeadPtr, copyOrigIdxPtr,
    usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr, tHeadPtr, M, rfl, hw, hq, hnBr, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [nOrig, nBr, outOrigPtr, outBridgePtr, copyTailPtr, copyHeadPtr, copyOrigIdxPtr,
      usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr, tHeadPtr] with hargs
  set tM := nOrig + nBr with htM
  -- the frame: cells outside the output arrays keep their values
  let Frame : (ℕ → ℕ) → Prop := fun m => ∀ a, a < tOrigPtr ∨ tHeadPtr + tM ≤ a → m a = mem a
  -- first loop
  let Inv1 : ℕ → State → Prop := fun i st =>
    T0Regs st args ∧ st.regs 13 = i ∧ Frame st.mem ∧
    T0OrigDone mem outOrigPtr copyTailPtr copyHeadPtr copyOrigIdxPtr tOrigPtr tTailPtr tHeadPtr i
      st.mem
  have hloop1 : Triple w p (fun st => st = startState args mem pos)
      (forRange 13 (.const 0) (.reg 0) t0OrigBody) (normalPost (Inv1 nOrig))
      (fun _ => nOrig * (40 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) := by
    refine Triple.forRange_const 40 0 nOrig (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, ?_, by simp, fun a _ => rfl, fun j hj => absurd hj (by omega)⟩
      intro i hi
      simp only [Function.update_of_ne (show i ≠ 13 by omega)]
      interval_cases i <;> rfl
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have r0 : st.regs 0 = nOrig := h.1 0 (by omega)
      eval_expr
    · intro i _ hi st ω' hinv
      obtain ⟨hR, h13, hfr, hdone⟩ := hinv
      have r2 : st.regs 2 = outOrigPtr := hR 2 (by omega)
      have r4 : st.regs 4 = copyTailPtr := hR 4 (by omega)
      have r5 : st.regs 5 = copyHeadPtr := hR 5 (by omega)
      have r6 : st.regs 6 = copyOrigIdxPtr := hR 6 (by omega)
      have r10 : st.regs 10 = tOrigPtr := hR 10 (by omega)
      have r11 : st.regs 11 = tTailPtr := hR 11 (by omega)
      have r12 : st.regs 12 = tHeadPtr := hR 12 (by omega)
      have hqi := hq i hi
      have hO : st.mem (outOrigPtr + i) = mem (outOrigPtr + i) := hfr _ (Or.inl (by omega))
      set q := mem (outOrigPtr + i) with hq_def
      have hcO : st.mem (copyOrigIdxPtr + q) = mem (copyOrigIdxPtr + q) :=
        hfr _ (Or.inl (by omega))
      have hcT : st.mem (copyTailPtr + q) = mem (copyTailPtr + q) := hfr _ (Or.inl (by omega))
      have hcH : st.mem (copyHeadPtr + q) = mem (copyHeadPtr + q) := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      unfold t0OrigBody
      refine runs_seq_assign_le (v := q) (by rw [← hO]; eval_expr) ?_
      refine runs_seq_store_le (x := tOrigPtr + i) (v := mem (copyOrigIdxPtr + q))
        (by eval_expr) (by rw [← hcO]; eval_expr) ?_
      set m1 := Function.update st.mem (tOrigPtr + i) (mem (copyOrigIdxPtr + q))
      have hcT1 : m1 (copyTailPtr + q) = mem (copyTailPtr + q) := by
        simp only [m1]; rw [Function.update_of_ne (by omega), hcT]
      refine runs_seq_store_le (x := tTailPtr + i) (v := mem (copyTailPtr + q))
        (by eval_expr) (by rw [← hcT1]; eval_expr) ?_
      set m2 := Function.update m1 (tTailPtr + i) (mem (copyTailPtr + q))
      have hcH2 : m2 (copyHeadPtr + q) = mem (copyHeadPtr + q) := by
        simp only [m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcH]
      refine runs_store_le (x := tHeadPtr + i) (v := mem (copyHeadPtr + q))
        (by eval_expr) (by rw [← hcH2]; eval_expr) ⟨⟨((hR.upd 16 q (by omega)).mem _).mem _
          |>.mem _ |>.upd 13 (i + 1) (by omega), by simp, ?_, ?_⟩, by simpa using h13⟩ ?_
      · intro a ha
        simp only [m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro j hj
        simp only [m2, m1]
        by_cases hji : j = i
        · subst hji
          refine ⟨?_, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_self]
        · obtain ⟨d1, d2, d3⟩ := hdone j (by omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), d1]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), d2]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), d3]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- second loop
  let Inv2 : ℕ → State → Prop := fun z st =>
    T0Regs st args ∧ st.regs 14 = z ∧ st.regs 15 = min nBr (zeroPositions mem usedBridgePtr z).length ∧ Frame st.mem ∧
    T0OrigDone mem outOrigPtr copyTailPtr copyHeadPtr copyOrigIdxPtr tOrigPtr tTailPtr tHeadPtr
      nOrig st.mem ∧
    T0BrDone mem nOrig outBridgePtr eCap tOrigPtr tTailPtr tHeadPtr (zeroPositions mem usedBridgePtr z) (min nBr (zeroPositions mem usedBridgePtr z).length)
      st.mem
  have hloop2 : Triple w p (fun st => T0Regs st args ∧ st.regs 15 = 0 ∧ Frame st.mem ∧
        T0OrigDone mem outOrigPtr copyTailPtr copyHeadPtr copyOrigIdxPtr tOrigPtr tTailPtr
          tHeadPtr nOrig st.mem)
      (forRange 14 (.const 0) (.reg 8) t0BrBody) (normalPost (Inv2 ubLen))
      (fun _ => ubLen * (60 + Expr.size (.reg 8) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 8) + 5)) := by
    refine Triple.forRange_const 60 0 ubLen (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, h15, hfr, hdone⟩
      refine ⟨by eval_expr, hR.upd 14 0 (by omega), by simp, ?_, hfr, hdone, ?_⟩
      · simp [zeroPositions, h15]
      · intro k hk; simp [zeroPositions] at hk
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have r8 : st.regs 8 = ubLen := h.1 8 (by omega)
      eval_expr
    · intro z _ hz st ω' hinv
      obtain ⟨hR, h14, h15, hfr, hdone, hbr⟩ := hinv
      have r0 : st.regs 0 = nOrig := hR 0 (by omega)
      have r1 : st.regs 1 = nBr := hR 1 (by omega)
      have r3 : st.regs 3 = outBridgePtr := hR 3 (by omega)
      have r7 : st.regs 7 = usedBridgePtr := hR 7 (by omega)
      have r9 : st.regs 9 = eCap := hR 9 (by omega)
      have r10 : st.regs 10 = tOrigPtr := hR 10 (by omega)
      have r11 : st.regs 11 = tTailPtr := hR 11 (by omega)
      have r12 : st.regs 12 = tHeadPtr := hR 12 (by omega)
      have hU : st.mem (usedBridgePtr + z) = mem (usedBridgePtr + z) := hfr _ (Or.inl (by omega))
      have hZs := zeroPositions_succ mem usedBridgePtr z
      set c := min nBr (zeroPositions mem usedBridgePtr z).length with hc
      have hcn : c ≤ nBr := min_le_left _ _
      -- the state does not change: the invariant at `z + 1` with the same count
      have hsame : (¬ c < nBr ∨ mem (usedBridgePtr + z) ≠ 0) →
          Inv2 (z + 1) { st with regs := Function.update st.regs 14 (z + 1) } := by
        intro hcase
        have hc' : min nBr (zeroPositions mem usedBridgePtr (z + 1)).length = c := by
          rcases hcase with hcase | hcase
          · have : (zeroPositions mem usedBridgePtr z).length ≤ (zeroPositions mem usedBridgePtr (z + 1)).length := by
              simp only [hZs, List.length_append]; omega
            omega
          · simp only [hZs, hcase, ↓reduceIte, List.append_nil]; rfl
        refine ⟨hR.upd 14 _ (by omega), by simp, ?_, hfr, hdone, ?_⟩
        · simp only [Function.update_of_ne (show (15 : ℕ) ≠ 14 by omega)]; rw [hc', h15]
        · rw [hc']
          intro k hk
          obtain ⟨d1, d2, d3⟩ := hbr k hk
          refine ⟨?_, d2, d3⟩
          rw [d1]
          congr 1
          exact (zeroPositions_getD_of_le mem usedBridgePtr (Nat.le_succ z)
            (Nat.lt_of_lt_of_le hk (min_le_right _ _))).symm
      refine runs_start_le ?_
      unfold t0BrBody
      refine runs_cond_le (v := if c < nBr then 1 else 0) (by rw [← h15] at *; eval_expr) ?_ ?_
      · intro hne
        have hlt : c < nBr := by by_contra h; simp [h] at hne
        refine runs_cond_le (v := if mem (usedBridgePtr + z) = 0 then 1 else 0)
          (by rw [← hU]; eval_expr) ?_ ?_
        · intro hne2
          have hz0 : mem (usedBridgePtr + z) = 0 := by by_contra h; simp [h] at hne2
          have hclen : c = (zeroPositions mem usedBridgePtr z).length := by
            have : (zeroPositions mem usedBridgePtr z).length < nBr ∨ (zeroPositions mem usedBridgePtr z).length ≥ nBr := lt_or_ge _ _
            omega
          have hZ1 : zeroPositions mem usedBridgePtr (z + 1) = zeroPositions mem usedBridgePtr z ++ [z] := by simp only [hZs, hz0, ↓reduceIte]
          have hc1 : min nBr (zeroPositions mem usedBridgePtr (z + 1)).length = c + 1 := by
            rw [hZ1, List.length_append, List.length_singleton]; omega
          have hB : st.mem (outBridgePtr + 2 * c) = mem (outBridgePtr + 2 * c) :=
            hfr _ (Or.inl (by omega))
          refine runs_seq_assign_le (v := nOrig + c) (by eval_expr) ?_
          refine runs_seq_store_le (x := tOrigPtr + (nOrig + c)) (v := eCap + z)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := c + c) (by eval_expr) ?_
          set m1 := Function.update st.mem (tOrigPtr + (nOrig + c)) (eCap + z)
          have hB1 : m1 (outBridgePtr + (c + c)) = mem (outBridgePtr + 2 * c) := by
            simp only [m1]; rw [Function.update_of_ne (by omega), ← hB]; congr 2; ring
          refine runs_seq_store_le (x := tTailPtr + (nOrig + c))
            (v := mem (outBridgePtr + 2 * c)) (by eval_expr) (by rw [← hB1]; eval_expr) ?_
          set m2 := Function.update m1 (tTailPtr + (nOrig + c)) (mem (outBridgePtr + 2 * c))
          have hB' : st.mem (outBridgePtr + 2 * c + 1) = mem (outBridgePtr + 2 * c + 1) :=
            hfr _ (Or.inl (by omega))
          have hB2 : m2 (outBridgePtr + (c + c) + 1) = mem (outBridgePtr + 2 * c + 1) := by
            simp only [m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), ← hB']
            congr 2; ring
          refine runs_seq_store_le (x := tHeadPtr + (nOrig + c))
            (v := mem (outBridgePtr + 2 * c + 1)) (by eval_expr) (by rw [← hB2]; eval_expr) ?_
          set m3 := Function.update m2 (tHeadPtr + (nOrig + c)) (mem (outBridgePtr + 2 * c + 1))
          refine runs_assign_le (v := c + 1) (by eval_expr) ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
          · exact ((((hR.upd 16 _ (by omega)).mem _).upd 17 _ (by omega)).mem _ |>.mem _
              |>.upd 15 _ (by omega) |>.upd 14 _ (by omega))
          · simp
          · simp only [Function.update_of_ne (show (15 : ℕ) ≠ 14 by omega),
              Function.update_self]
            exact hc1.symm
          · intro a ha
            show m3 a = mem a
            simp only [m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hfr a ha
          · intro j hj
            show m3 _ = _ ∧ m3 _ = _ ∧ m3 _ = _
            simp only [m3, m2, m1]
            obtain ⟨d1, d2, d3⟩ := hdone j hj
            refine ⟨?_, ?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), d1]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), d2]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), d3]
          · rw [hc1]
            intro k hk
            show m3 _ = _ ∧ m3 _ = _ ∧ m3 _ = _
            simp only [m3, m2, m1]
            have hk1 : k < (zeroPositions mem usedBridgePtr z ++ [z]).length := by
              simp only [List.length_append, List.length_singleton]; omega
            by_cases hkc : k = c
            · subst hkc
              have hget : (zeroPositions mem usedBridgePtr z ++ [z]).getD c 0 = z := by
                rw [List.getD_eq_getElem _ _ hk1, List.getElem_append_right (by omega)]
                simp [hclen]
              refine ⟨?_, ?_, ?_⟩
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_self, hZ1, hget]
              · rw [Function.update_of_ne (by omega), Function.update_self]
              · rw [Function.update_self]
            · obtain ⟨d1, d2, d3⟩ := hbr k (by omega)
              have hkZ : k < (zeroPositions mem usedBridgePtr z).length := by omega
              have hget : (zeroPositions mem usedBridgePtr z ++ [z]).getD k 0 =
                  (zeroPositions mem usedBridgePtr z).getD k 0 := by
                rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hkZ,
                  List.getElem_append_left hkZ]
              refine ⟨?_, ?_, ?_⟩
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), d1, hZ1, hget]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), d2]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), d3]
          · simpa using h14
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
        · intro hz2
          have hz0 : mem (usedBridgePtr + z) ≠ 0 := by intro h; simp [h] at hz2
          exact runs_nop_le ⟨hsame (Or.inr hz0), by simpa using h14⟩
            (by simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega)
      · intro hz2
        have hc0 : ¬ c < nBr := by intro h; simp [h] at hz2
        exact runs_nop_le ⟨hsame (Or.inl hc0), by simpa using h14⟩
          (by simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega)
  -- the whole procedure
  refine runs_start_le ?_
  unfold t0EdgesProc
  refine runs_seq_triple_le hloop1 rfl ?_
  rintro st₁ ⟨hR, -, hfr, hdone⟩
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop2 ⟨hR.upd 15 0 (by omega), by simp, hfr, hdone⟩ ?_
  rintro st₂ ⟨-, -, -, hfr2, hdone2, hbr2⟩
  have hmin : min nBr (zeroPositions mem usedBridgePtr ubLen).length = nBr := min_eq_left hnBr
  rw [hmin] at hbr2
  refine runs_ret_le (by eval_expr) ⟨nOrig, nBr, outOrigPtr, outBridgePtr, copyTailPtr,
    copyHeadPtr, copyOrigIdxPtr, usedBridgePtr, ubLen, eCap, tOrigPtr, tTailPtr, tHeadPtr, rfl,
    rfl, hdone2, hbr2, hfr2⟩ ?_
  simp only [t0EdgesContract, hargs, Expr.size_const, Expr.size_reg, List.getD_cons_zero,
    List.getD_cons_succ]
  omega

end

end MinCostFlow.LSF.Program
