module

public import MinCostFlow.HierPaths.BuildProgCutMask
public import MinCostFlow.HierPaths.BuildProgCutPack

/-!
# Packing the two sides of a saved child

The injection call routes the complement of a saved set into that set.
The mask starts with ones and clears the positions of saved terminals.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the saved list base and length, child size, mask base,
destination and terminal offset. Return the length of the complement. -/
def buildInjectSidesProc (fMask fPack : ℕ) : Stmt :=
  .seq (.call 9 fMask [.reg 0,.reg 1,.reg 3,.reg 2,.const 1])
    (.seq (.call 10 fPack [.reg 3,.reg 2,.reg 4,.reg 5,.const 1])
      (.seq (.call 11 fPack [.reg 3,.reg 2,.bin .add (.reg 4) (.reg 10),.reg 5,.const 0])
        (.ret (.reg 10))))

theorem buildInjectSidesProc_noRand (fMask fPack : ℕ) :
    (buildInjectSidesProc fMask fPack).NoRand := by
  simp [buildInjectSidesProc, Stmt.NoRand]

/-- The complement and saved set in the router's terminal numbering. -/
def injectSides (s off : ℕ) (S : Finset ℕ) : List ℕ × List ℕ :=
  (finsetWords (shiftSet off (Finset.range s \ S)),finsetWords (shiftSet off S))

/-- Both arrays occupy exactly one child size in total. -/
theorem injectSides_length {s off : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range s) :
    (injectSides s off S).1.length + (injectSides s off S).2.length = s := by
  have hc := Finset.card_le_card hS
  simp only [Finset.card_range] at hc
  simp only [injectSides,finsetWords,Finset.length_sort,card_shiftSet,
    Finset.card_sdiff_of_subset hS,Finset.card_range]
  omega

/-- The injection scan keeps all cells outside the mask and the two output lists. -/
def buildInjectSidesContract (w s : ℕ) (S : Finset ℕ) : Contract where
  pre args mem := ∃ src mask out off, args = [src,S.card,s,mask,out,off] ∧
    ListAt mem src (finsetWords S) ∧ S ⊆ Finset.range s ∧
    src+S.card ≤ mask ∧ mask+s ≤ out ∧ out+2*s < 2^w ∧ off+s < 2^w ∧ 1 < 2^w
  post args mem v mem' := ∃ src mask out off, args = [src,S.card,s,mask,out,off] ∧
    v = (injectSides s off S).1.length ∧
    ListAt mem' out ((injectSides s off S).1 ++ (injectSides s off S).2) ∧
    ∀ j, (j < mask ∨ mask+s ≤ j) →
      (j < out ∨ out+s ≤ j) → mem' j = mem j
  cost _ _ := 120*s+120

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Two linear packing calls write the complete injection row. -/
theorem buildInjectSidesProc_meetsContract {w s : ℕ} {U : Finset ℕ} {p : Program}
    {f fMask fPack : ℕ} (hf : p.procs[f]? = some (buildInjectSidesProc fMask fPack))
    (hMaskP : p.procs[fMask]? = some buildCutMaskProc)
    (hPackP : p.procs[fPack]? = some buildCutPackProc) :
    MeetsContract w p f (buildInjectSidesContract w s U) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨src, mask, out, off, rfl, hList, hU, hSep, hMO, hOut, hOff, hw⟩ := hPre
  let A := Finset.range s \ U
  let left := (injectSides s off U).1
  let right := (injectSides s off U).2
  have hCard : U.card ≤ s := by simpa using Finset.card_le_card hU
  have hA : A ⊆ Finset.range s := Finset.sdiff_subset
  have hLeft : packedCutSide A off 1 s = left := packedCutSide_one hA off
  have hRight : packedCutSide A off 0 s = right := by
    rw [packedCutSide_zero]
    change finsetWords (shiftSet off (Finset.range s \ A)) = finsetWords (shiftSet off U)
    congr 2
    ext j
    by_cases hj : j ∈ U
    · simp [A,hj,hU hj]
    · simp [A,hj]
  have hBoth : left.length + right.length = s := injectSides_length hU
  have hLeftLen : left.length ≤ s := by omega
  refine runs_start_le ?_
  unfold buildInjectSidesProc
  refine runs_seq_call_le (buildCutMaskProc_meetsContract hMaskP)
    (vs := [src,U.card,mask,s,1]) ?_ ?_
    ⟨src,mask,1,rfl,hList,hU,hSep,by omega,hw,le_rfl⟩ ?_
  · simp [evalArgs,Expr.eval,startState,hw]
  · wram_words
  intro _ mem₁ pos₁ hMask
  obtain ⟨_,_,_,ha,hM,hFrame₁⟩ := hMask
  simp only [List.cons.injEq,and_true,true_and] at ha
  obtain ⟨rfl,rfl,rfl⟩ := ha
  have hM₂ (i : ℕ) (hi : i < s) : mem₁ (mask+i) = if i ∈ A then 1 else 0 := by
    have hir : i ∈ Finset.range s := Finset.mem_range.mpr hi
    rw [hM i hi]
    by_cases his : i ∈ U <;> simp [A,hir,his]
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
      exact h4.trans (h3.trans (hFrame₁ j hj))
  · simp [buildInjectSidesContract, buildCutMaskContract, buildCutPackContract,
      argsSize, Expr.size]
    omega

end MinCostFlow.HierPaths
