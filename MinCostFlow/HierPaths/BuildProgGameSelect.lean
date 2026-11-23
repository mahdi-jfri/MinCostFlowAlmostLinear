module

public import MinCostFlow.HierPaths.BuildProgGameScan

/-!
# Selecting children that returned cuts

The core replies are in active-child order. Copy the indices of replies tagged as
cuts to a dense list. This list is also the order in which the batch router must
return matchings, so the next stage can put each matching back in its child.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Active indices selected by the first `i` replies. -/
def cutReplyIndices (answer : ℕ → CoreResult) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun j => decide (coreTag (answer j) = 0))

/-- A reply pointer and the tag at offset three are available for each active index. -/
def ReplyTagsAt (mem : ℕ → ℕ) (replies count ceiling : ℕ) (answer : ℕ → CoreResult) : Prop :=
  ∀ i < count, mem (replies + i) + 3 < ceiling ∧
    mem (mem (replies + i) + 3) = coreTag (answer i)

/-- Inspect reply `r3`. Append its index if the reply is a cut. -/
def buildGameSelectStep : Stmt :=
  .cond (.load (.bin .add (.load (.bin .add (.reg 0) (.reg 3))) (.const 3))) .nop
    (.seq (.store (.bin .add (.reg 2) (.reg 4)) (.reg 3))
      (.assign 4 (.bin .add (.reg 4) (.const 1))))

/-- Args are the reply pointer table, its length, and the destination. -/
def buildGameSelectProc : Stmt :=
  .seq (.assign 4 (.const 0))
    (.seq (forRange 3 (.const 0) (.reg 1) buildGameSelectStep) (.ret (.reg 4)))

/-- The dense list is built above all replies and the reply pointer table. -/
def buildGameSelectContract (w count : ℕ) (answer : ℕ → CoreResult) : Contract where
  pre args mem := ∃ replies out, args = [replies, count, out] ∧
    replies + count ≤ out ∧ out + count < 2 ^ w ∧ 3 < 2 ^ w ∧
    ReplyTagsAt mem replies count out answer
  post args mem v mem' := ∃ replies out, args = [replies, count, out] ∧
    v = (cutReplyIndices answer count).length ∧
    ListAt mem' out (cutReplyIndices answer count) ∧
    ∀ j, (j < out ∨ out + v ≤ j) → mem' j = mem j
  cost _ _ := 36 * count + 16

theorem buildGameSelectProc_noRand : buildGameSelectProc.NoRand := by
  simp [buildGameSelectProc, buildGameSelectStep, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private theorem cutReplyIndices_length (answer : ℕ → CoreResult) (i : ℕ) :
    (cutReplyIndices answer i).length ≤ i := by
  simpa [cutReplyIndices] using List.length_filter_le
    (fun j => decide (coreTag (answer j) = 0)) (List.range i)

private theorem cutReplyIndices_succ (answer : ℕ → CoreResult) (i : ℕ) :
    cutReplyIndices answer (i + 1) =
      cutReplyIndices answer i ++ (if coreTag (answer i) = 0 then [i] else []) := by
  by_cases h : coreTag (answer i) = 0 <;>
    simp [cutReplyIndices, List.range_succ, List.filter_append, h]

/-- The selected child at position `j` has index at least `j`.
Thus its active-table entries can be compacted in place. -/
theorem le_cutReplyIndex (answer : ℕ → CoreResult) (n : ℕ) :
    ∀ j (hj : j < (cutReplyIndices answer n).length), j ≤ (cutReplyIndices answer n)[j] := by
  suffices ∀ j < (cutReplyIndices answer n).length, j ≤ (cutReplyIndices answer n).getD j 0 from
    fun j hj => (List.getD_eq_getElem _ _ hj) ▸ this j hj
  induction n with
  | zero => simp [cutReplyIndices]
  | succ n ih =>
    intro j hj
    rw [cutReplyIndices_succ] at hj ⊢
    by_cases h : coreTag (answer n) = 0
    · simp only [h, ite_true, List.length_append, List.length_cons, List.length_nil] at hj ⊢
      by_cases hj' : j < (cutReplyIndices answer n).length
      · rw [List.getD_append _ _ _ _ hj']
        exact ih j hj'
      · have hjEq : j = (cutReplyIndices answer n).length := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), hjEq, Nat.sub_self, List.getD_cons_zero]
        exact cutReplyIndices_length _ _
    · simp only [h, ite_false, List.append_nil] at hj ⊢
      exact ih j hj

private def selectInv (mem : ℕ → ℕ) (replies count out : ℕ) (answer : ℕ → CoreResult)
    (i : ℕ) (st : State) : Prop :=
  st.regs 0 = replies ∧ st.regs 1 = count ∧ st.regs 2 = out ∧ st.regs 3 = i ∧
    st.regs 4 = (cutReplyIndices answer i).length ∧
    ListAt st.mem out (cutReplyIndices answer i) ∧
    (∀ j, (j < out ∨ out + (cutReplyIndices answer i).length ≤ j) → st.mem j = mem j)

private theorem buildSelect_step {w replies count out i : ℕ} {answer : ℕ → CoreResult}
    {mem : ℕ → ℕ} (p : Program) (hi : i < count) (hSep : replies + count ≤ out)
    (hEnd : out + count < 2 ^ w) (hw : 3 < 2 ^ w)
    (hTags : ReplyTagsAt mem replies count out answer) :
    Triple w p (selectInv mem replies count out answer i) buildGameSelectStep
      (normalPost fun st => selectInv mem replies count out answer (i + 1)
        {st with regs := Function.update st.regs 3 (i + 1)} ∧ st.regs 3 = i)
      (fun _ => 26) := by
  intro st ω ⟨h0, h1, h2, h3, h4, hAt, hFrame⟩
  let old := cutReplyIndices answer i
  have hLen : old.length ≤ i := cutReplyIndices_length ..
  obtain ⟨hTagAddr, hTag⟩ := hTags i hi
  have hReplyW : replies + i < 2 ^ w := by omega
  have hTagW : mem (replies + i) + 3 < 2 ^ w := by omega
  have hReplyRead : st.mem (replies + i) = mem (replies + i) := hFrame _ (Or.inl (by omega))
  have hTagRead : st.mem (mem (replies + i) + 3) = coreTag (answer i) :=
    (hFrame _ (Or.inl hTagAddr)).trans hTag
  have hEval : (Expr.load (.bin .add (.load (.bin .add (.reg 0) (.reg 3))) (.const 3))).eval w st =
      some (coreTag (answer i)) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq h0) (Expr.eval_reg_of_eq h3) hReplyW) hReplyRead)
        (Expr.eval_const hw) hTagW) hTagRead
  unfold buildGameSelectStep
  by_cases h : coreTag (answer i) = 0
  · have hNext : cutReplyIndices answer (i + 1) = old ++ [i] := by
      rw [cutReplyIndices_succ, ite_eq_left h]
    have hDW : out + old.length < 2 ^ w := by omega
    have hCW : old.length + 1 < 2 ^ w := by omega
    have hOne : 1 < 2 ^ w := by omega
    have hOld : st.regs 4 = old.length := h4
    obtain ⟨o, outSt, c, hr, hp, hc⟩ := (show ∃ o st' c, Runs w p ω
        (.seq (.store (.bin .add (.reg 2) (.reg 4)) (.reg 3))
          (.assign 4 (.bin .add (.reg 4) (.const 1)))) st o st' c ∧
        (normalPost fun st => selectInv mem replies count out answer (i + 1)
          {st with regs := Function.update st.regs 3 (i + 1)} ∧ st.regs 3 = i) o st' ∧
        0 + c ≤ 14 from by
      refine runs_seq_store_le (x := out + old.length) (v := i) ?_ (Expr.eval_reg_of_eq h3) ?_
      · exact Expr.eval_add (Expr.eval_reg_of_eq h2) (Expr.eval_reg_of_eq hOld) hDW
      refine runs_assign_le (v := old.length + 1) ?_ ?_ ?_
      · simp [Expr.eval, hOld, hOne, hCW]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp,
          by simp [hNext], ?_, ?_⟩, h3⟩
        · change ListAt (Function.update st.mem (out + old.length) i) out _
          rw [hNext, listAt_append]
          refine ⟨?_, ?_⟩
          · intro j hj
            rw [Function.update_of_ne (by omega)]
            exact hAt j hj
          · intro j hj
            have hz : j = 0 := by simpa using hj
            subst j; simp
        · intro j hj
          simp only [hNext, List.length_append, List.length_cons, List.length_nil] at hj
          change Function.update st.mem (out + old.length) i j = mem j
          rw [Function.update_of_ne (by omega)]
          exact hFrame j (by omega)
      · simp [Expr.size])
    exact ⟨o, outSt, _, runs_cond_iff.mpr ⟨0, c, h ▸ hEval, by simpa using hr, rfl⟩, hp,
      by simp [Expr.size]; omega⟩
  · have hNext : cutReplyIndices answer (i + 1) = old := by simp [cutReplyIndices_succ, h, old]
    refine ⟨.normal, st, _, runs_cond_iff.mpr ⟨_, 1, hEval, ?_, rfl⟩, ?_, by simp [Expr.size]⟩
    · simpa [h] using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w p ω .nop st .normal st 1)
    · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp,
          by simpa [hNext] using h4, ?_, ?_⟩, h3⟩
      · exact hNext ▸ hAt
      · simpa [hNext] using hFrame

/-- The selection scan gives the indices of all and only the cut replies. -/
theorem buildGameSelectProc_meetsContract {w count f : ℕ} {p : Program} {answer : ℕ → CoreResult}
    (hf : p.procs[f]? = some buildGameSelectProc) :
    MeetsContract w p f (buildGameSelectContract w count answer) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨replies, out, rfl, hSep, hEnd, hw, hTags⟩ := hPre
  let st0 := startState [replies, count, out] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 4 0 }
  have hw1 : 1 < 2 ^ w := by omega
  have hLoop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := buildGameSelectStep) (P := fun st => st = st1)
    (Inv := selectInv mem replies count out answer) 26 0 count (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st h => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl, rfl, rfl, rfl, rfl,
        fun j hj => False.elim (Nat.not_lt_zero j hj), fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun _ _ hi => buildSelect_step p hi hSep hEnd hw hTags)
  refine runs_start_le ?_
  unfold buildGameSelectProc
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _)) ?_
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_, _, _, _, hLen, hAt, hFrame⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hLen) ⟨replies, out, rfl, rfl, hAt, hFrame⟩ ?_
  simp [buildGameSelectContract, Expr.size]
  omega

end MinCostFlow.HierPaths
