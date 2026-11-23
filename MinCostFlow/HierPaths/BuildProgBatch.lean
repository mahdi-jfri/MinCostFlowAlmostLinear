module

public import MinCostFlow.HierPaths.BuildProgGameSelect
public import MinCostFlow.HierPaths.BuildProgCopy

/-!
# Gathering the batched routing request

All child bisections at one group have the same size. Each pair of sides uses
one fixed-size record, so one scan copies the records and writes their section
offsets. The scan follows the indices of the cut replies.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The two sections of pair `i`, taken together. -/
def buildBatchRow (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) : List ℕ :=
  let p := pairs.getD i (∅, ∅)
  finsetWords p.1 ++ finsetWords p.2

/-- Read the next reply pointer `replies[idx + 1]` (the end of child `idx`'s prepared block),
copy the pair from `next - 2 * s`, and record its two offsets. -/
def buildBatchStep (fCopy : ℕ) : Stmt :=
  .seq (.assign 8 (.bin .mul (.reg 7) (.reg 3)))
    (.seq (.assign 9 (.load (.bin .add (.bin .add (.reg 0) (.load (.bin .add (.reg 1) (.reg 7)))) (.const 1))))
      (.seq (.call 10 fCopy [
            .bin .sub (.reg 9) (.bin .add (.reg 3) (.reg 3)),
            .reg 3, .bin .add (.reg 5) (.reg 8)])
        (.seq (.store (.bin .add (.reg 4) (.bin .add (.reg 7) (.reg 7))) (.reg 8))
          (.store (.bin .add (.bin .add (.reg 4) (.bin .add (.reg 7) (.reg 7))) (.const 1))
            (.bin .add (.reg 8) (.reg 6))))))

/-- Args are `[replies, cuts, pairs, childSize, out]`. -/
def buildBatchProc (fCopy : ℕ) : Stmt :=
  .seq (.assign 5 (.bin .add (.bin .add (.reg 4) (.bin .add (.reg 2) (.reg 2))) (.const 1)))
    (.seq (.assign 6 (.bin .div (.reg 3) (.const 2)))
      (.seq (forRange 7 (.const 0) (.reg 2) (buildBatchStep fCopy))
        (.seq (.store (.bin .add (.reg 4) (.bin .add (.reg 2) (.reg 2)))
            (.bin .mul (.reg 2) (.reg 3)))
          (.ret (.bin .add (.reg 5) (.bin .mul (.reg 2) (.reg 3)))))))

theorem buildBatchProc_noRand (fCopy : ℕ) : (buildBatchProc fCopy).NoRand := by
  simp [buildBatchProc, buildBatchStep, forRange, forUp, Stmt.NoRand]

/-- The interval of the new router batch. -/
def buildBatchEnd (out k s : ℕ) : ℕ := out + 2 * k + 1 + k * s

/-- The selected reply provides one row of the batch. Its prepared block ends at
`next = mem (replies + idx + 1) = e + 3 * s`, and the two packed request sides of total
length `s` sit at `src = next - 2 * s = e + s`, independent of any bump gap inside the core. -/
def BatchRowsAt (mem : ℕ → ℕ) (replies cuts out s : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  ∀ i < pairs.length,
    let idx := mem (cuts + i)
    let next := mem (replies + idx + 1)
    let src := next - 2 * s
    replies + idx + 1 < out ∧ 2 * s ≤ next ∧ next ≤ out ∧
    ListAt mem src (buildBatchRow pairs i)

/-- The scan writes the two offsets and the data of each pair, then the final offset. -/
def BatchWritten (mem : ℕ → ℕ) (out s : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  mem (out + 2 * pairs.length) = pairs.length * s ∧
  ∀ i < pairs.length,
    mem (out + 2 * i) = i * s ∧ mem (out + 2 * i + 1) = i * s + s / 2 ∧
    ListAt mem (out + 2 * pairs.length + 1 + i * s) (buildBatchRow pairs i)

/-- The input replies and selection table lie below the new batch. -/
def buildBatchContract (w s : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Contract where
  pre args mem := ∃ replies cuts out, args = [replies, cuts, pairs.length, s, out] ∧
    cuts + pairs.length ≤ out ∧ buildBatchEnd out pairs.length s < 2 ^ w ∧ 3 < 2 ^ w ∧
    BatchRowsAt mem replies cuts out s pairs ∧ ∀ j < pairs.length, (buildBatchRow pairs j).length = s
  post args mem v mem' := ∃ replies cuts out, args = [replies, cuts, pairs.length, s, out] ∧
    v = buildBatchEnd out pairs.length s ∧ BatchWritten mem' out s pairs ∧
    ∀ j, (j < out ∨ buildBatchEnd out pairs.length s ≤ j) → mem' j = mem j
  cost _ _ := pairs.length * (17 * s + 128) + 48

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private def batchInv (mem : ℕ → ℕ) (replies cuts out s : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = replies ∧ st.regs 1 = cuts ∧ st.regs 2 = pairs.length ∧
    st.regs 3 = s ∧ st.regs 4 = out ∧ st.regs 5 = out + 2 * pairs.length + 1 ∧
    st.regs 6 = s / 2 ∧ st.regs 7 = i ∧
    (∀ j < i, st.mem (out + 2 * j) = j * s ∧ st.mem (out + 2 * j + 1) = j * s + s / 2 ∧
      ListAt st.mem (out + 2 * pairs.length + 1 + j * s) (buildBatchRow pairs j)) ∧
    (∀ j, (j < out ∨ (out + 2 * i ≤ j ∧ j < out + 2 * pairs.length + 1) ∨
      out + 2 * pairs.length + 1 + i * s ≤ j) → st.mem j = mem j)

private theorem buildBatch_step {w replies cuts out s i fCopy : ℕ} {p : Program}
    {mem : ℕ → ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hCopy : p.procs[fCopy]? = some buildCopyProc)
    (hi : i < pairs.length) (hCuts : cuts + pairs.length ≤ out)
    (hEnd : buildBatchEnd out pairs.length s < 2 ^ w) (hw : 3 < 2 ^ w)
    (hRows : BatchRowsAt mem replies cuts out s pairs)
    (hLen : ∀ j < pairs.length, (buildBatchRow pairs j).length = s) :
    Triple w p (batchInv mem replies cuts out s pairs i) (buildBatchStep fCopy)
      (normalPost fun st => batchInv mem replies cuts out s pairs (i + 1)
        {st with regs := Function.update st.regs 7 (i + 1)} ∧ st.regs 7 = i)
      (fun _ => 17 * s + 110) := by
  intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,hPrev,hFrame⟩
  let data := out + 2 * pairs.length + 1
  let idx := mem (cuts + i)
  let nextPtr := mem (replies + idx + 1)
  let src := nextPtr - 2 * s
  let dest := data + i * s
  have hend : data + pairs.length * s < 2 ^ w := hEnd
  have hs : i * s + s ≤ pairs.length * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s (by omega)
  have hiLast : (i + 1) * s = i * s + s := Nat.succ_mul i s
  have hiWord : i * s < 2 ^ w := by omega
  have hFit : dest + s < 2 ^ w := by dsimp [dest]; omega
  obtain ⟨hIdx, h2s, hNextOut, hAt⟩ := hRows i hi
  change replies + idx + 1 < out at hIdx
  change 2 * s ≤ nextPtr at h2s
  change nextPtr ≤ out at hNextOut
  have hSrc : src + s ≤ out := by dsimp [src]; omega
  have hReadIdx : st.mem (cuts + i) = idx := hFrame _ (Or.inl (by omega))
  have hReadNext : st.mem (replies + idx + 1) = nextPtr := hFrame _ (Or.inl hIdx)
  have hCutsW : cuts + i < 2 ^ w := by omega
  have hIdxW : replies + idx < 2 ^ w := by omega
  have hIdx1W : replies + idx + 1 < 2 ^ w := by omega
  have h2sW : s + s < 2 ^ w := by omega
  have hSrcW : src < 2 ^ w := by omega
  have hDestW : dest < 2 ^ w := by omega
  change out + 2 * pairs.length + 1 + i * s < 2 ^ w at hDestW
  have hOne : 1 < 2 ^ w := by omega
  have hTwo : 2 < 2 ^ w := by omega
  have hsW : s < 2 ^ w := by omega
  have hi2W : i + i < 2 ^ w := by omega
  have hOffW : out + (i + i) < 2 ^ w := by omega
  have hOff1W : out + (i + i) + 1 < 2 ^ w := by omega
  have hMidW : i * s + s / 2 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildBatchStep
  refine runs_seq_assign_le (v := i * s) (Expr.eval_mul (Expr.eval_reg_of_eq h7)
    (Expr.eval_reg_of_eq h3) hiWord) ?_
  refine runs_seq_assign_le (v := nextPtr) ?_ ?_
  · simp [Expr.eval, Function.update, h0, h1, h7, hCutsW, hIdxW, hIdx1W, hOne, hReadIdx, hReadNext]
  refine runs_seq_call_le (buildCopyProc_meetsContract hCopy) (vs := [src, s, dest]) ?_ ?_
    ⟨src, s, dest, rfl, by dsimp [dest, data]; omega, hFit, hOne⟩ ?_
  · have hSubEq : nextPtr - (s + s) = src := by dsimp [src]; omega
    simp [Expr.eval, evalArgs, Function.update, h2sW, hSubEq, hSrcW, hDestW, h3, h5, dest, data]
  · wram_words
  intro _ mem' pos' hPost
  obtain ⟨_, _, _, he, hCopy, hBelow⟩ := hPost
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hCopy' : ListAt mem' dest (buildBatchRow pairs i) := by
    intro j hj
    have hj' : j < s := (hLen i hi) ▸ hj
    exact (hCopy j hj').trans ((hFrame _ (Or.inl (by omega))).trans (hAt j hj))
  have hBelow' : ∀ a, a < dest ∨ dest + s ≤ a → mem' a = st.mem a := hBelow
  refine runs_seq_store_le (x := out + 2 * i) (v := i * s) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, h4, h7, hi2W, hOffW, Nat.two_mul]
  · simp [Expr.eval, Function.update]
  refine runs_store_le (x := out + 2 * i + 1) (v := i * s + s / 2) ?_ ?_ ?_ ?_
  · simp [Expr.eval, Function.update, h4, h7, hi2W, hOffW, hOff1W, hOne, Nat.two_mul]
  · simp [Expr.eval, Function.update, h6, hMidW]
  · let next := Function.update (Function.update mem' (out + 2 * i) (i * s))
        (out + 2 * i + 1) (i * s + s / 2)
    have hNoTouch {a : ℕ} (ha : a ≠ out + 2 * i) (hb : a ≠ out + 2 * i + 1) : next a = mem' a := by
      simp [next, Function.update_of_ne, ha, hb]
    refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
      by simpa using h4, by simpa using h5, by simpa using h6, by simp, ?_, ?_⟩, h7⟩
    · intro j hj
      change next (out + 2 * j) = j * s ∧ next (out + 2 * j + 1) = j * s + s / 2 ∧ _
      have hData : ∀ a, data ≤ a → next a = mem' a := fun a ha => hNoTouch (by omega) (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hl, hr, hOld⟩ := hPrev j hj
        have hjmul : j * s + s ≤ i * s := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right s (by omega)
        refine ⟨?_, ?_, ?_⟩
        · rw [hNoTouch (by omega) (by omega), hBelow' _ (Or.inl (by dsimp [dest]; omega))]
          exact hl
        · rw [hNoTouch (by omega) (by omega), hBelow' _ (Or.inl (by dsimp [dest]; omega))]
          exact hr
        · exact WordRAM.ListAt.congr hOld fun a ha hb => (hData a (by omega)).trans
            (hBelow' a (Or.inl (by rw [hLen j (hj.trans hi)] at hb; dsimp [dest]; omega)))
      · refine ⟨?_, by simp [next], ?_⟩
        · simp [next]
        · exact WordRAM.ListAt.congr hCopy' fun a ha _ => hData a (by change data + j * s ≤ a at ha; omega)
    · intro j hj
      change next j = mem j
      have hNever : j ≠ out + 2 * i ∧ j ≠ out + 2 * i + 1 := by
        rw [hiLast] at hj
        omega
      rw [hNoTouch hNever.1 hNever.2]
      refine (hBelow' _ ?_).trans (hFrame _ ?_)
      · rw [hiLast] at hj
        dsimp [dest]
        omega
      · rw [hiLast] at hj
        omega
  · simp [buildCopyContract, argsSize, Expr.size]
    omega

/-- The gathering procedure writes a contiguous batch and its two section offsets
per child, in time linear in the number of written words. -/
theorem buildBatchProc_meetsContract {w s f fCopy : ℕ} {p : Program}
    {pairs : List (Finset ℕ × Finset ℕ)}
    (hf : p.procs[f]? = some (buildBatchProc fCopy))
    (hc : p.procs[fCopy]? = some buildCopyProc) :
    MeetsContract w p f (buildBatchContract w s pairs) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨replies, cuts, out, rfl, hCuts, hEnd, hw, hRows, hLen⟩ := hPre
  let k := pairs.length
  let data := out + 2 * k + 1
  have hFit : out + 2 * k + 1 + k * s < 2 ^ w := hEnd
  have hData : data < 2 ^ w := by dsimp [data]; omega
  have hOne : 1 < 2 ^ w := by omega
  have hTwo : 2 < 2 ^ w := by omega
  have hK2 : k + k < 2 ^ w := by omega
  have hOutK : out + (k + k) < 2 ^ w := by omega
  have hProd : k * s < 2 ^ w := by omega
  have hS : s < 2 ^ w := hWords _ (by simp)
  have hHalf : s / 2 < 2 ^ w := (Nat.div_le_self ..).trans_lt hS
  let st0 := startState [replies, cuts, k, s, out] mem pos
  let st1 : State := {st0 with regs := Function.update (Function.update st0.regs 5 data) 6 (s / 2)}
  have hLoop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 2)
    (body := buildBatchStep fCopy) (P := fun st => st = st1)
    (Inv := batchInv mem replies cuts out s pairs)
    (17 * s + 110) 0 k (Nat.zero_le _) hOne (fun _ => by omega)
    (fun st hEq => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _), ?_⟩
      exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ hj => False.elim (Nat.not_lt_zero _ hj),
        fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => buildBatch_step hc hi hCuts hEnd hw hRows hLen)
  refine runs_start_le ?_
  unfold buildBatchProc
  refine runs_seq_assign_le (v := data) ?_ ?_
  · change pairs.length + pairs.length < 2 ^ w at hK2
    change out + (pairs.length + pairs.length) < 2 ^ w at hOutK
    have hData' : out + (pairs.length + pairs.length) + 1 < 2 ^ w := by omega
    simp [Expr.eval, startState, hK2, hOutK, hOne, hData', data, Nat.two_mul]; rfl
  refine runs_seq_assign_le (v := s / 2) ?_ ?_
  · simp [Expr.eval, startState, Function.update, hTwo, hHalf]
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_, _, h2, h3, h4, h5, _, _, hRowsOut, hFrame⟩
  have h2' : st.regs 2 = k := h2
  have h5' : st.regs 5 = data := h5
  refine runs_seq_store_le (x := out + 2 * k) (v := k * s) ?_ ?_ ?_
  · simp [Expr.eval, h2', h4, hK2, hOutK, Nat.two_mul]
  · exact Expr.eval_mul (Expr.eval_reg_of_eq h2') (Expr.eval_reg_of_eq h3) hProd
  refine runs_ret_le (v := buildBatchEnd out k s) ?_ ?_ ?_
  · exact Expr.eval_add (Expr.eval_reg_of_eq h5')
      (Expr.eval_mul (Expr.eval_reg_of_eq h2') (Expr.eval_reg_of_eq h3) hProd) hFit
  · let next := Function.update st.mem (out + 2 * k) (k * s)
    have hk : k = pairs.length := rfl
    refine ⟨replies, cuts, out, rfl, rfl, ⟨by simp [hk], ?_⟩, ?_⟩
    · intro j hj
      have hj' : j < k := hj
      obtain ⟨hl, hr, hAt⟩ := hRowsOut j hj
      have hNoTouch : ∀ a ≠ out + 2 * k, next a = st.mem a :=
        fun _ ha => Function.update_of_ne ha _ _
      change next (out + 2 * j) = _ ∧ next (out + 2 * j + 1) = _ ∧ ListAt next _ _
      refine ⟨(hNoTouch _ (by omega)).trans hl, (hNoTouch _ (by omega)).trans hr, ?_⟩
      exact WordRAM.ListAt.congr hAt fun a ha _ => hNoTouch a (by omega)
    · intro j hj
      change next j = mem j
      change j < out ∨ out + 2 * k + 1 + k * s ≤ j at hj
      rw [show next j = st.mem j from Function.update_of_ne (by omega) _ _]
      exact hFrame j (by
        rcases hj with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
  · simp [buildBatchContract, Expr.size, k, Nat.mul_add]
    omega

end MinCostFlow.HierPaths
