module

public import MinCostFlow.LSF.Program.Spec
public import MinCostFlow.LSF.Program.Utils
public import WordRAM.Tactic

/-!
# The header and the index arrays of the `T` block

Besides the tracker graph (`TTrack.lean`), the edge IDs and the order `π`, the `T` block
(`TBlockAt`) has an 8-word header of pointers, two frozen arrays with the ends of the tree
edges, and the table `idxOfEdge`, which maps an edge ID `e < eCap` to one more than its position
in the ID array (and `0` for an ID that is not there).

`tBlockFillProc` writes these. It computes the sub-block pointers of the layout
(`Layout.lean`) from `tPtr`, `vCap`, `eCap` and `tM`, stores the header, and then for each
`i < tM` stores the ends `vList[tTail[i]]` and `vList[tHead[i]]` and, when the ID `e` at position
`i` is below `eCap`, stores `i + 1` at `idxOfEdge[e]`. The ID array must already be in place and
`idxOfEdge` must already be zeroed. The cost is `O(tM)` (`tBlockFill_meetsContract`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## The procedure -/

/-- One tree edge (register `15` is `i`). The sub-block pointers are in registers `8`–`12`. -/
def tBlockFillBody : Stmt :=
  .store (.bin .add (.reg 10) (.reg 15))
    (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 5) (.reg 15))))) ;;
  .store (.bin .add (.reg 11) (.reg 15))
    (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 15))))) ;;
  .assign 16 (.load (.bin .add (.reg 8) (.reg 15))) ;;
  .cond (.bin .lt (.reg 16) (.reg 2))
    (.store (.bin .add (.reg 12) (.reg 16)) (.bin .add (.reg 15) (.const 1)))
    .nop

/-- Args: `[tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr]`. -/
def tBlockFillProc : Stmt :=
  .assign 7 (.bin .add (.reg 0) (.const 8)) ;;
  .assign 8 (.bin .add (.reg 7) (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 1)))
    (.bin .mul (.const 9) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1))))) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 3)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 3)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 3)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 3)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 2)) ;;
  .store (.bin .add (.reg 0) (.const 0)) (.reg 3) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 7) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.reg 9) ;;
  .store (.bin .add (.reg 0) (.const 4)) (.reg 10) ;;
  .store (.bin .add (.reg 0) (.const 5)) (.reg 11) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 12) ;;
  .store (.bin .add (.reg 0) (.const 7)) (.reg 13) ;;
  forRange 15 (.const 0) (.reg 3) tBlockFillBody ;;
  .ret (.const 0)

lemma tBlockFillProc_noRand : tBlockFillProc.NoRand := by
  simp [tBlockFillProc, tBlockFillBody, forRange, forUp, Stmt.NoRand]

/-- The header of the `T` block, as `TBlockAt` states it. -/
def TBlockHeader (mem : ℕ → ℕ) (tPtr vCap eCap tM : ℕ) : Prop :=
  mem (tPtr + tOffM) = tM ∧
  mem (tPtr + tOffDgTPtr) = tDgTPtr tPtr ∧
  mem (tPtr + tOffOrigIdPtr) = tOrigIdBase tPtr vCap tM ∧
  mem (tPtr + tOffPiPtr) = tPiBase tPtr vCap tM ∧
  mem (tPtr + tOffFrozenTailPtr) = tFrozenTailBase tPtr vCap tM ∧
  mem (tPtr + tOffFrozenHeadPtr) = tFrozenHeadBase tPtr vCap tM ∧
  mem (tPtr + tOffIdxOfEdgePtr) = tIdxOfEdgeBase tPtr vCap tM ∧
  mem (tPtr + tOffSplitScratchPtr) = tSplitScratchBase tPtr vCap eCap tM

/-- The contract of `tBlockFillProc`. The arrays it reads lie after the `T` block, the IDs at
`tOrigIdBase` are distinct, and `idxOfEdge` starts zeroed. -/
def tBlockFillContract (w : ℕ) : Contract where
  pre args mem := ∃ (tPtr vCap eCap tM vListPtr tTailPtr tHeadPtr n0 : ℕ),
    args = [tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr] ∧ 16 ≤ 2 ^ w ∧
    tPtr + tBlockSize vCap eCap tM ≤ vListPtr ∧ vListPtr + n0 < 2 ^ w ∧
    tPtr + tBlockSize vCap eCap tM ≤ tTailPtr ∧ tTailPtr + tM < 2 ^ w ∧
    tPtr + tBlockSize vCap eCap tM ≤ tHeadPtr ∧ tHeadPtr + tM < 2 ^ w ∧
    (∀ i < tM, mem (tTailPtr + i) < n0 ∧ mem (tHeadPtr + i) < n0) ∧
    (∀ i < tM, ∀ j < tM, mem (tOrigIdBase tPtr vCap tM + i) = mem (tOrigIdBase tPtr vCap tM + j) →
      i = j) ∧
    (∀ e < eCap, mem (tIdxOfEdgeBase tPtr vCap tM + e) = 0)
  post args mem ret mem' := ∃ (tPtr vCap eCap tM vListPtr tTailPtr tHeadPtr : ℕ),
    args = [tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr] ∧ ret = 0 ∧
    TBlockHeader mem' tPtr vCap eCap tM ∧
    (∀ i < tM, mem' (tFrozenTailBase tPtr vCap tM + i) = mem (vListPtr + mem (tTailPtr + i)) ∧
      mem' (tFrozenHeadBase tPtr vCap tM + i) = mem (vListPtr + mem (tHeadPtr + i))) ∧
    (∀ i < tM, mem (tOrigIdBase tPtr vCap tM + i) < eCap →
      mem' (tIdxOfEdgeBase tPtr vCap tM + mem (tOrigIdBase tPtr vCap tM + i)) = i + 1) ∧
    (∀ e < eCap, (∀ i < tM, mem (tOrigIdBase tPtr vCap tM + i) ≠ e) →
      mem' (tIdxOfEdgeBase tPtr vCap tM + e) = 0) ∧
    ∀ a, a < tPtr ∨ (tPtr + tHdrSize ≤ a ∧ a < tFrozenTailBase tPtr vCap tM) ∨
      tSplitScratchBase tPtr vCap eCap tM ≤ a → mem' a = mem a
  cost args _ := 60 * args.getD 3 0 + 200

/-! ## Proof -/

/-- The memory after the eight header stores. -/
def headerMem (mem : ℕ → ℕ) (tPtr tM oB pB fT fH iB sB : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update mem (tPtr + 0) tM)
    (tPtr + 1) (tPtr + 8)) (tPtr + 2) oB) (tPtr + 3) pB) (tPtr + 4) fT) (tPtr + 5) fH)
    (tPtr + 6) iB) (tPtr + 7) sB

set_option maxHeartbeats 800000 in
theorem tBlockFill_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some tBlockFillProc) :
    MeetsContract w p b (tBlockFillContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr, n0, rfl, h16, hv1, hv2, ht1, ht2,
    hh1, hh2, hidx, hinj, hzIdx⟩ := hpre
  set args := [tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  -- the sub-block pointers
  set oB := tOrigIdBase tPtr vCap tM with hoB_def
  set pB := tPiBase tPtr vCap tM with hpB_def
  set fT := tFrozenTailBase tPtr vCap tM with hfT_def
  set fH := tFrozenHeadBase tPtr vCap tM with hfH_def
  set iB := tIdxOfEdgeBase tPtr vCap tM with hiB_def
  set sB := tSplitScratchBase tPtr vCap eCap tM with hsB_def
  have hoB : oB = tPtr + 8 + (4 + 7 * vCap + 9 * (2 * tM + 1)) := by
    simp only [hoB_def, tOrigIdBase, tDgTPtr, tHdrSize, dynGraphSize]
  have hpB : pB = oB + tM := rfl
  have hfT : fT = pB + tM := rfl
  have hfH : fH = fT + tM := rfl
  have hiB : iB = fH + tM := rfl
  have hsB : sB = iB + eCap := rfl
  have hTB : sB + (4 + 2 * tM) = tPtr + tBlockSize vCap eCap tM := by
    simp only [hsB, hiB, hfH, hfT, hpB, hoB, tBlockSize, tHdrSize, dynGraphSize]; ring
  have hsBw : sB < 2 ^ w := by omega
  replace hTB := And.intro hTB True.intro
  clear_value sB iB fH fT pB oB
  have hdefs := And.intro hoB_def (And.intro hpB_def (And.intro hfT_def (And.intro hfH_def
    (And.intro hiB_def hsB_def))))
  clear hoB_def hpB_def hfT_def hfH_def hiB_def hsB_def
  -- the eight header words
  refine runs_start_le ?_
  unfold tBlockFillProc
  refine runs_seq_assign_le (v := tPtr + 8) (by eval_expr) ?_
  refine runs_seq_assign_le (v := oB) (by rw [hoB]; eval_expr) ?_
  refine runs_seq_assign_le (v := pB) (by rw [hpB]; eval_expr) ?_
  refine runs_seq_assign_le (v := fT) (by rw [hfT]; eval_expr) ?_
  refine runs_seq_assign_le (v := fH) (by rw [hfH]; eval_expr) ?_
  refine runs_seq_assign_le (v := iB) (by rw [hiB]; eval_expr) ?_
  refine runs_seq_assign_le (v := sB) (by rw [hsB]; eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 0) (v := tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 1) (v := tPtr + 8) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 2) (v := oB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 3) (v := pB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 4) (v := fT) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 5) (v := fH) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 6) (v := iB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := tPtr + 7) (v := sB) (by eval_expr) (by eval_expr) ?_
  have hHfr : ∀ a, a < tPtr ∨ tPtr + 8 ≤ a → headerMem mem tPtr tM oB pB fT fH iB sB a = mem a :=
      fun a ha => by
    simp only [headerMem, Function.update_apply, show ¬ (a = tPtr + 0) by omega,
      show ¬ (a = tPtr + 1) by omega, show ¬ (a = tPtr + 2) by omega,
      show ¬ (a = tPtr + 3) by omega, show ¬ (a = tPtr + 4) by omega,
      show ¬ (a = tPtr + 5) by omega, show ¬ (a = tPtr + 6) by omega,
      show ¬ (a = tPtr + 7) by omega, if_false]
  have hHdr : TBlockHeader (headerMem mem tPtr tM oB pB fT fH iB sB) tPtr vCap eCap tM := by
    simp only [TBlockHeader, tOffM, tOffDgTPtr, tOffOrigIdPtr, tOffPiPtr, tOffFrozenTailPtr,
      tOffFrozenHeadPtr, tOffIdxOfEdgePtr, tOffSplitScratchPtr, headerMem, Function.update_apply,
      ← hdefs.1, ← hdefs.2.1, ← hdefs.2.2.1, ← hdefs.2.2.2.1, ← hdefs.2.2.2.2.1,
      ← hdefs.2.2.2.2.2]
    simp [tDgTPtr, tHdrSize]
  -- `idxOfEdge` is already zeroed after the header writes
  let mem₉ := headerMem mem tPtr tM oB pB fT fH iB sB
  have h9mem : ∀ a, a < tPtr ∨ (tPtr + 8 ≤ a ∧ a < iB) ∨ sB ≤ a → mem₉ a = mem a := fun a ha =>
    hHfr a (by omega)
  have h9hdr : TBlockHeader mem₉ tPtr vCap eCap tM := hHdr
  have hz₉ : ∀ e < eCap, mem₉ (iB + e) = 0 := fun e he =>
    (hHfr (iB + e) (Or.inr (by omega))).trans (hzIdx e he)
  -- the loop
  let Done : ℕ → (ℕ → ℕ) → Prop := fun i m =>
    (∀ j < i, m (fT + j) = mem (vListPtr + mem (tTailPtr + j)) ∧
      m (fH + j) = mem (vListPtr + mem (tHeadPtr + j))) ∧
    (∀ j < i, mem (oB + j) < eCap → m (iB + mem (oB + j)) = j + 1) ∧
    (∀ e < eCap, (∀ j < i, mem (oB + j) ≠ e) → m (iB + e) = 0)
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = tPtr ∧ st.regs 2 = eCap ∧ st.regs 4 = vListPtr ∧ st.regs 5 = tTailPtr ∧
    st.regs 6 = tHeadPtr ∧ st.regs 8 = oB ∧ st.regs 10 = fT ∧ st.regs 11 = fH ∧
    st.regs 12 = iB ∧ st.regs 3 = tM ∧ st.regs 15 = i ∧
    (∀ a, a < fT ∨ sB ≤ a → st.mem a = mem₉ a) ∧ Done i st.mem
  have hloop : Triple w p (fun st => st.regs 0 = tPtr ∧ st.regs 2 = eCap ∧ st.regs 4 = vListPtr ∧
        st.regs 5 = tTailPtr ∧ st.regs 6 = tHeadPtr ∧ st.regs 8 = oB ∧ st.regs 10 = fT ∧
        st.regs 11 = fH ∧ st.regs 12 = iB ∧ st.regs 3 = tM ∧ st.mem = mem₉)
      (forRange 15 (.const 0) (.reg 3) tBlockFillBody) (normalPost (Inv tM))
      (fun _ => (tM - 0) * (50 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.forRange_const 50 0 tM (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st ⟨r0, r2, r4, r5, r6, r8, r10, r11, r12, r3, hm⟩
      refine ⟨by eval_expr, by simpa using r0, by simpa using r2, by simpa using r4,
        by simpa using r5, by simpa using r6, by simpa using r8, by simpa using r10,
        by simpa using r11, by simpa using r12, by simpa using r3, by simp,
        fun a _ => by rw [hm], fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega), fun e he _ => ?_⟩
      show st.mem (iB + e) = 0
      rw [hm]; exact hz₉ e he
    · intro i st _ _ hI; exact hI.2.2.2.2.2.2.2.2.2.2.1
    · intro i st _ _ hI
      have r3 : st.regs 3 = tM := hI.2.2.2.2.2.2.2.2.2.1
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨r0, r2, r4, r5, r6, r8, r10, r11, r12, r3, r15, hfr, hdT, hdI, hdZ⟩ := hI
      obtain ⟨hti, hhi⟩ := hidx i hi
      have hT0 : st.mem (tTailPtr + i) = mem (tTailPtr + i) := by
        rw [hfr _ (Or.inr (by omega)), h9mem _ (Or.inr (Or.inr (by omega)))]
      have hT : st.mem (vListPtr + st.mem (tTailPtr + i)) = mem (vListPtr + mem (tTailPtr + i)) := by
        rw [hT0, hfr _ (Or.inr (by omega)), h9mem _ (Or.inr (Or.inr (by omega)))]
      refine runs_start_le ?_
      unfold tBlockFillBody
      refine runs_seq_store_le (x := fT + i) (v := mem (vListPtr + mem (tTailPtr + i)))
        (by eval_expr) (by rw [← hT]; eval_expr) ?_
      set m1 := Function.update st.mem (fT + i) (mem (vListPtr + mem (tTailPtr + i))) with hm1
      have hfr1 : ∀ a, a < fT ∨ sB ≤ a → m1 a = mem₉ a := fun a ha => by
        rw [hm1, Function.update_of_ne (by omega)]; exact hfr a ha
      have hH0 : m1 (tHeadPtr + i) = mem (tHeadPtr + i) := by
        rw [hfr1 _ (Or.inr (by omega)), h9mem _ (Or.inr (Or.inr (by omega)))]
      have hH : m1 (vListPtr + m1 (tHeadPtr + i)) = mem (vListPtr + mem (tHeadPtr + i)) := by
        rw [hH0, hfr1 _ (Or.inr (by omega)), h9mem _ (Or.inr (Or.inr (by omega)))]
      refine runs_seq_store_le (x := fH + i) (v := mem (vListPtr + mem (tHeadPtr + i)))
        (by eval_expr) (by rw [← hH]; eval_expr) ?_
      set m2 := Function.update m1 (fH + i) (mem (vListPtr + mem (tHeadPtr + i))) with hm2
      have hfr2 : ∀ a, a < fT ∨ sB ≤ a → m2 a = mem₉ a := fun a ha => by
        rw [hm2, Function.update_of_ne (by omega)]; exact hfr1 a ha
      have hE : m2 (oB + i) = mem (oB + i) := by
        rw [hfr2 _ (Or.inl (by omega)), h9mem _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      set e := mem (oB + i) with he
      have hdT2 : ∀ j < i + 1, m2 (fT + j) = mem (vListPtr + mem (tTailPtr + j)) ∧
          m2 (fH + j) = mem (vListPtr + mem (tHeadPtr + j)) := fun j hj => by
        rw [hm2, hm1]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hdT j hj
        · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
          exact ⟨rfl, rfl⟩
      have hidxm : ∀ x, iB ≤ x → m2 x = st.mem x := fun x hx => by
        rw [hm2, hm1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine runs_seq_assign_le (v := e) (by rw [← hE]; eval_expr) ?_
      refine WordRAM.runs_cond_le (v := if e < eCap then 1 else 0) (by eval_expr) ?_ ?_
      · intro hne
        have hlt : e < eCap := by by_contra hc; simp [hc] at hne
        refine runs_store_le (x := iB + e) (v := i + 1) (by eval_expr) (by eval_expr)
          ⟨⟨by simpa using r0, by simpa using r2, by simpa using r4, by simpa using r5,
            by simpa using r6, by simpa using r8, by simpa using r10, by simpa using r11,
            by simpa using r12, by simpa using r3, by simp, fun a ha => ?_,
            fun j hj => ?_, fun j hj hjE => ?_, fun e' he' hne' => ?_⟩,
            by simpa using r15⟩ (by simp [Expr.size])
        · show Function.update m2 (iB + e) (i + 1) a = mem₉ a
          rw [Function.update_of_ne (by omega)]; exact hfr2 a ha
        · show Function.update m2 (iB + e) (i + 1) (fT + j) = _ ∧
            Function.update m2 (iB + e) (i + 1) (fH + j) = _
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hdT2 j hj
        · show Function.update m2 (iB + e) (i + 1) (iB + mem (oB + j)) = j + 1
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · have hne : mem (oB + j) ≠ e := fun h => by
              have := hinj j (by omega) i hi h; omega
            rw [Function.update_of_ne (by omega), hidxm _ (by omega)]; exact hdI j hj hjE
          · rw [← he, Function.update_self]
        · show Function.update m2 (iB + e) (i + 1) (iB + e') = 0
          have hne : e' ≠ e := fun h => hne' i (by omega) (by rw [h])
          rw [Function.update_of_ne (by omega), hidxm _ (by omega)]
          exact hdZ e' he' fun j hj => hne' j (by omega)
      · intro hz
        have hge : ¬ e < eCap := by intro hc; simp [hc] at hz
        refine runs_nop_le
          ⟨⟨by simpa using r0, by simpa using r2, by simpa using r4, by simpa using r5,
            by simpa using r6, by simpa using r8, by simpa using r10, by simpa using r11,
            by simpa using r12, by simpa using r3, by simp, fun a ha => hfr2 a ha,
            hdT2, fun j hj hjE => ?_, fun e' he' hne' => ?_⟩,
            by simpa using r15⟩ (by simp [Expr.size])
        · show m2 (iB + mem (oB + j)) = j + 1
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · rw [hidxm _ (by omega)]; exact hdI j hj hjE
          · exact absurd hjE hge
        · show m2 (iB + e') = 0
          rw [hidxm _ (by omega)]
          exact hdZ e' he' fun j hj => hne' j (by omega)
  refine runs_seq_triple_le hloop ⟨by simp [startState, hargs], by simp [startState, hargs],
    by simp [startState, hargs], by simp [startState, hargs], by simp [startState, hargs],
    by simp, by simp, by simp, by simp, by simp [startState, hargs], rfl⟩ ?_
  rintro st ⟨-, -, -, -, -, -, -, -, -, -, -, hfr, hdT, hdI, hdZ⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨tPtr, vCap, eCap, tM, vListPtr, tTailPtr, tHeadPtr,
    rfl, rfl, ?_, by rw [← hdefs.2.2.1, ← hdefs.2.2.2.1]; exact hdT,
    by rw [← hdefs.1, ← hdefs.2.2.2.2.1]; exact hdI,
    by rw [← hdefs.1, ← hdefs.2.2.2.2.1]; exact hdZ, fun a ha => ?_⟩ ?_
  · obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := h9hdr
    have hag : ∀ k < 8, st.mem (tPtr + k) = mem₉ (tPtr + k) := fun k hk =>
      hfr _ (Or.inl (by omega))
    simp only [TBlockHeader, tOffM, tOffDgTPtr, tOffOrigIdPtr, tOffPiPtr, tOffFrozenTailPtr,
      tOffFrozenHeadPtr, tOffIdxOfEdgePtr, tOffSplitScratchPtr] at a0 a1 a2 a3 a4 a5 a6 a7 ⊢
    exact ⟨(hag 0 (by omega)).trans a0, (hag 1 (by omega)).trans a1, (hag 2 (by omega)).trans a2,
      (hag 3 (by omega)).trans a3, (hag 4 (by omega)).trans a4, (hag 5 (by omega)).trans a5,
      (hag 6 (by omega)).trans a6, (hag 7 (by omega)).trans a7⟩
  · simp only [tHdrSize, ← hdefs.2.2.1, ← hdefs.2.2.2.2.2] at ha
    rw [hfr a (by omega)]; exact h9mem a (by omega)
  · simp only [tBlockFillContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin, Nat.sub_zero]
    omega

end

end MinCostFlow.LSF.Program
