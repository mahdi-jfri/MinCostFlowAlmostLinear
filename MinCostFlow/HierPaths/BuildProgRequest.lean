module

public import MinCostFlow.HierPaths.BuildProgCutMask

/-!
# Preparing one child's routing request

A core cut is a sorted list of local vertices. Select its smaller side, fill the
membership mask, and pad it. Pack the two sides consecutively in parent terminal
numbers. The returned count separates the two sides.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Args are `[src, cutSize, childSize, mask, out, off]`. Return the first side's length. -/
def buildRequestProc (fMask fPad fPack : ℕ) : Stmt :=
  .seq (.assign 6 (.bin .div (.reg 2) (.const 2)))
    (.seq (.assign 7 (.bin .lt (.reg 6) (.reg 1)))
      (.seq (.assign 8 (.bin .sub (.reg 6)
        (.bin .add (.bin .mul (.bin .sub (.const 1) (.reg 7)) (.reg 1))
          (.bin .mul (.reg 7) (.bin .sub (.reg 2) (.reg 1))))))
        (.seq (.call 9 fMask [.reg 0, .reg 1, .reg 3, .reg 2, .reg 7])
          (.seq (.call 9 fPad [.reg 3, .reg 2, .reg 8])
            (.seq (.call 10 fPack [.reg 3, .reg 2, .reg 4, .reg 5, .const 1])
              (.seq (.call 11 fPack [.reg 3, .reg 2, .bin .add (.reg 4) (.reg 10), .reg 5, .const 0])
                (.ret (.reg 10))))))))

theorem buildRequestProc_noRand (fMask fPad fPack : ℕ) :
    (buildRequestProc fMask fPad fPack).NoRand := by
  simp [buildRequestProc, Stmt.NoRand]

/-- The two request sets for a core cut, in the router's list order. -/
def requestSides (s off : ℕ) (U : Finset ℕ) : List ℕ × List ℕ :=
  (finsetWords (shiftSet off (bisectOf s U)),
    finsetWords (shiftSet off (Finset.range s \ bisectOf s U)))

/-- The output is two consecutive lists. The cut and memory outside the mask and
output ranges are kept. -/
def buildRequestContract (w s : ℕ) (U : Finset ℕ) : Contract where
  pre args mem := ∃ src mask out off, args = [src, U.card, s, mask, out, off] ∧
    ListAt mem src (finsetWords U) ∧ U ⊆ Finset.range s ∧ 2 ≤ s ∧
    src + U.card ≤ mask ∧ mask + s ≤ out ∧ out + 2 * s < 2 ^ w ∧ off + s < 2 ^ w
  post args mem v mem' := ∃ src mask out off, args = [src, U.card, s, mask, out, off] ∧
    v = (requestSides s off U).1.length ∧
    ListAt mem' out ((requestSides s off U).1 ++ (requestSides s off U).2) ∧
    ∀ j, (j < mask ∨ mask + s ≤ j) →
      (j < out ∨ out + 2 * s ≤ j) → mem' j = mem j
  cost _ _ := 160 * s + 180

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

private theorem smallerSide_count {s : ℕ} {U : Finset ℕ} (hU : U ⊆ Finset.range s) :
    let C := smallerSide (Finset.range s) U
    let flip := if s / 2 < U.card then 1 else 0
    C.card = (1 - flip) * U.card + flip * (s - U.card) ∧
      ∀ i < s, (if i ∈ U then 1 - flip else flip) = if i ∈ C then 1 else 0 := by
  have hDiff : ((Finset.range s) \ U).card = s - U.card := by
    rw [Finset.card_sdiff_of_subset hU, Finset.card_range]
  have hCard : U.card ≤ s := by simpa using Finset.card_le_card hU
  dsimp only
  by_cases h : s / 2 < U.card
  · have hn : ¬ U.card ≤ s - U.card := by omega
    simp only [smallerSide, ite_eq_left h, ite_eq_right hn, Nat.sub_self, Nat.zero_mul,
      Nat.one_mul, Nat.zero_add, hDiff, true_and]
    intro i hi
    by_cases hm : i ∈ U <;> simp [Finset.mem_sdiff, Finset.mem_range, hi, hm]
  · have hn : U.card ≤ ((Finset.range s) \ U).card := by rw [hDiff]; omega
    simp [smallerSide, h, hn]

private theorem smallerSide_le_size {s : ℕ} {U : Finset ℕ} (hU : U ⊆ Finset.range s) :
    (smallerSide (Finset.range s) U).card ≤ s := by
  simpa using Finset.card_le_card (smallerSide_subset hU)

/-- The two sides of a request are lists of equal length when the child size is even. -/
theorem requestSides_lengths {s off : ℕ} {U : Finset ℕ} (hU : U ⊆ Finset.range s)
    (hEven : 2 * (s / 2) = s) :
    (requestSides s off U).1.length = s / 2 ∧ (requestSides s off U).2.length = s / 2 := by
  let C := smallerSide (Finset.range s) U
  have hC : C ⊆ Finset.range s := smallerSide_subset hU
  have hCs : C.card ≤ s / 2 := by
    have hh := (card_smallerSide hU).1
    rw [Finset.card_range] at hh
    change 2 * C.card ≤ s at hh
    omega
  have hA : (bisectOf s U).card = s / 2 := card_padHalf hC hCs
  have hAc : (Finset.range s \ bisectOf s U).card = s / 2 := by
    have hSub : bisectOf s U ⊆ Finset.range s := padHalf_subset hC
    rw [Finset.card_sdiff_of_subset hSub, Finset.card_range, hA]
    omega
  constructor
  · change (finsetWords (shiftSet off (bisectOf s U))).length = _
    rw [finsetWords, Finset.length_sort, card_shiftSet, hA]
  · change (finsetWords (shiftSet off (Finset.range s \ bisectOf s U))).length = _
    rw [finsetWords, Finset.length_sort, card_shiftSet, hAc]

/-- Build the request for a cut, with the list layout needed by the batched router. -/
theorem buildRequestProc_meetsContract {w s : ℕ} {U : Finset ℕ} {p : Program}
    {f fMask fPad fPack : ℕ} (hf : p.procs[f]? = some (buildRequestProc fMask fPad fPack))
    (hMaskP : p.procs[fMask]? = some buildCutMaskProc)
    (hPadP : p.procs[fPad]? = some buildPadHalfProc)
    (hPackP : p.procs[fPack]? = some buildCutPackProc) :
    MeetsContract w p f (buildRequestContract w s U) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨src, mask, out, off, rfl, hList, hU, hs, hSep, hMO, hOut, hOff⟩ := hPre
  let C := smallerSide (Finset.range s) U
  let A := bisectOf s U
  let flip : ℕ := if s / 2 < U.card then 1 else 0
  let need := s / 2 - C.card
  let left := (requestSides s off U).1
  let right := (requestSides s off U).2
  have hw : 1 < 2 ^ w := by omega
  have hw₂ : 2 < 2 ^ w := by omega
  have hCard : U.card ≤ s := by simpa using Finset.card_le_card hU
  have hCFit : C.card ≤ s := smallerSide_le_size hU
  have hHalf : s / 2 < 2 ^ w := by omega
  have hFlip : flip ≤ 1 := by dsimp [flip]; split <;> omega
  have hNeed : need < 2 ^ w := by dsimp [need]; omega
  obtain ⟨hCount, hBits⟩ := smallerSide_count hU
  change C.card = (1 - flip) * U.card + flip * (s - U.card) at hCount
  change ∀ i < s, (if i ∈ U then 1 - flip else flip) = if i ∈ C then 1 else 0 at hBits
  have hA : A ⊆ Finset.range s := padHalf_subset (smallerSide_subset hU)
  have hLeft : packedCutSide A off 1 s = left := packedCutSide_one hA off
  have hRight : packedCutSide A off 0 s = right := packedCutSide_zero s off A
  have hLeftLen : left.length ≤ s := by
    have he : left.length = A.card := by
      dsimp [left, requestSides]
      rw [finsetWords, Finset.length_sort, card_shiftSet]
    exact he ▸ (by simpa using Finset.card_le_card hA)
  refine runs_start_le ?_
  unfold buildRequestProc
  refine runs_seq_assign_le (v := s / 2) ?_ ?_
  · simp [Expr.eval, startState, hw₂, hHalf]
  refine runs_seq_assign_le (v := flip) ?_ ?_
  · exact Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp [startState, Function.update])) hw
  refine runs_seq_assign_le (v := need) ?_ ?_
  · have hdw : s - U.card < 2 ^ w := by omega
    have huw : U.card < 2 ^ w := by omega
    by_cases hf : s / 2 < U.card
    · have hc : C.card = s - U.card := by simpa [flip, hf] using hCount
      have hq : s / 2 - (s - U.card) < 2 ^ w := (Nat.sub_le ..).trans_lt hHalf
      simp [Expr.eval, startState, Function.update, flip, hf, hw, hdw, need, hc, hq]
    · have hc : C.card = U.card := by simpa [flip, hf] using hCount
      have hq : s / 2 - U.card < 2 ^ w := (Nat.sub_le ..).trans_lt hHalf
      simp [Expr.eval, startState, Function.update, flip, hf, hw, hdw, huw, need, hc, hq]
  refine runs_seq_call_le (buildCutMaskProc_meetsContract hMaskP)
    (vs := [src, U.card, mask, s, flip]) ?_ ?_
    ⟨src, mask, flip, rfl, hList, hU, hSep, by omega, hw, hFlip⟩ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update]
  · wram_words
  intro _ mem₁ pos₁ hMask
  obtain ⟨_, _, _, ha, hM, hFrame₁⟩ := hMask
  simp only [List.cons.injEq, and_true, true_and] at ha
  obtain ⟨rfl, rfl, rfl⟩ := ha
  refine runs_seq_call_le (buildPadHalfProc_meetsContract hPadP)
    (vs := [mask, s, need]) ?_ ?_
    ⟨mask, rfl, by omega, hw, fun i hi => (hM i hi).trans (hBits i hi)⟩ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update]
  · wram_words
  intro _ mem₂ pos₂ hPad
  obtain ⟨mask₂, ha, hM₂, hFrame₂⟩ := hPad
  have he : mask = mask₂ := congrArg (fun l : List ℕ => l.headD 0) ha
  subst mask₂
  refine runs_seq_call_le (buildCutPackProc_meetsContract (C := A) hPackP)
    (vs := [mask, s, out, off, 1]) ?_ ?_
    ⟨mask, out, off, 1, rfl, hMO, by omega, hOff, hw, hM₂⟩ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update, hw]
  · wram_words
  intro a mem₃ pos₃ hL
  obtain ⟨_, _, _, _, ha, hLen, hLAt, hFrame₃⟩ := hL
  simp only [List.cons.injEq, and_true, true_and] at ha
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  rw [hLeft] at hLen hLAt
  change a = left.length at hLen
  have haOut : out + a + s < 2 ^ w := by omega
  refine runs_seq_call_le (buildCutPackProc_meetsContract (C := A) hPackP)
    (vs := [mask, s, out + a, off, 0]) ?_ ?_
    ⟨mask, out + a, off, 0, rfl, by omega, haOut, hOff, hw, ?_⟩ ?_
  · have hoa : out + a < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, startState, Function.update, hoa]
  · wram_words
  · intro i hi
    exact (hFrame₃ _ (Or.inl (by omega))).trans (hM₂ i hi)
  intro b mem₄ pos₄ hR
  obtain ⟨_, _, _, _, ha, hRLen, hRAt, hFrame₄⟩ := hR
  simp only [List.cons.injEq, and_true, true_and] at ha
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  rw [hRight] at hRLen hRAt
  change b = right.length at hRLen
  have hRightLen : right.length ≤ s := by
    have he : right.length = (Finset.range s \ A).card := by
      dsimp [right, requestSides]
      rw [finsetWords, Finset.length_sort, card_shiftSet]
    exact he ▸ (by simpa using Finset.card_le_card (s := Finset.range s \ A) Finset.sdiff_subset)
  refine runs_ret_le (v := a) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨src, mask, out, off, rfl, hLen, ?_, ?_⟩
    · apply listAt_append.mpr
      refine ⟨?_, hLen ▸ hRAt⟩
      intro j hj
      change j < left.length at hj
      change mem₄ (out + j) = left[j]
      exact (hFrame₄ _ (Or.inl (by omega))).trans (hLAt j hj)
    · intro j hj ho
      have h3 := hFrame₃ j (by omega)
      have h4 := hFrame₄ j (by omega)
      exact h4.trans (h3.trans ((hFrame₂ j hj).trans (hFrame₁ j hj)))
  · simp [buildRequestContract, buildCutMaskContract, buildPadHalfContract, buildCutPackContract,
      argsSize, Expr.size]
    omega

end MinCostFlow.HierPaths
