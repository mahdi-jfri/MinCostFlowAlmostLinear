module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepRead
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepOut
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepRun

/-!
# Tools for the step of a branch: cells, space and copies (`AssemblyBranchStepFrame`)

The step of a branch (`asmBrStepStmt`) runs three calls, each on new heap cells above the last.
The proof that the step keeps the representation of the branch (`AssemblyBranchStep.lean`) needs a
few facts that do not depend on the pieces:
* `asmBrDisjoint_of_grow`: the six parts stay apart when each part only gains cells in its own new
  range, and the new ranges lie outside the old cells;
* `asmBrStepSpace`: the heap space of the step, a monotone function of the caps and the sizes of
  the inputs. The change record of P4 has at most `vCap + eCap + 2` words, and P7's output batch
  lies in the space of P7's step, so the space of P10's update is bounded by the caps too;
* `lsfChangeAt_of_agree`: a change record depends only on its own cells;
* `zeroFrom_asmBrStepCopy`: the six copies at the end of the step keep the memory zero above the
  heap pointer.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.SparseCore.Program.Read

/-! ## The parts stay apart -/

/-- **The parts stay apart.** Let the six parts of `x₁` be pairwise apart, and let each part `i`
of `x'` lie in part `i` of `x₁` or in a new range `N i`. If no new range meets the cells of `x₁`
and distinct new ranges do not meet, then the six parts of `x'` are pairwise apart. -/
theorem asmBrDisjoint_of_grow {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b : ℕ} {x₁ x' : AsmBrConc TR X.τ} (N : ℕ → ℕ → Prop) (hd : AsmBrDisjoint X b x₁)
    (hgrow : ∀ i < 6, ∀ a, asmBrPart X b x' i a → asmBrPart X b x₁ i a ∨ N i a)
    (hnew : ∀ i < 6, ∀ a, N i a → ¬ asmBrFoot X b x₁ a)
    (hNN : ∀ i < 6, ∀ j < 6, i ≠ j → ∀ a, N i a → ¬ N j a) :
    AsmBrDisjoint X b x' := by
  intro i hi j hj hij a hai haj
  rcases hgrow i hi a hai with h1 | h1 <;> rcases hgrow j hj a haj with h2 | h2
  · exact hd i hi j hj hij a h1 h2
  · exact hnew j hj a h2 ⟨i, hi, h1⟩
  · exact hnew i hi a h1 ⟨j, hj, h2⟩
  · exact hNN i hi j hj hij a h1 h2

/-! ## The space of the step -/

/-- **The heap space of the step of a branch**, for the space `space` of the first phase, the
factor `readMul` of P10's update and the tour spec `OS` of P7: the first phase on the inputs and a
change record of at most `vCap + eCap + 2` words, P7's output step, and P10's update on the inputs,
the change record and P7's output batch (at most `outStepSpace OS vCap eCap` words). -/
def asmBrStepSpace (space : ℕ → ℕ) (readMul : ℕ) (OS : OutTourSpec)
    (k M N L depth vCap eCap tCap L_w words editWords : ℕ) : ℕ :=
  space (M + N + k + vCap + eCap + L + depth + words + editWords) + outStepSpace OS vCap eCap +
    readSpace readMul vCap tCap L_w (words + (vCap + eCap + 2) + outStepSpace OS vCap eCap)

/-- The space of P10's update grows with the number of words it reads. -/
theorem readSpace_mono {mul vCap tCap L_w x y : ℕ} (hxy : x ≤ y) :
    readSpace mul vCap tCap L_w x ≤ readSpace mul vCap tCap L_w y := by
  unfold readSpace
  gcongr

/-- P7's output step has room for at least `1000` cells. -/
theorem outStepSpace_ge (OS : OutTourSpec) (vCap eCap : ℕ) : 1000 ≤ outStepSpace OS vCap eCap := by
  unfold outStepSpace
  calc 1000 = 1000 * 1 * 1 * 1 := by norm_num
    _ ≤ 1000 * (vCap + 1) * (eCap + 1) * (OS.querySpace + 1) := by gcongr <;> omega

/-- The change record of P4 has at most `vCap + eCap + 2` words, when it is exact for an LSF state
whose forest edges are below `eCap` and whose new roots are below `vCap`. -/
theorem lsfChange_words_le {c : LSFChange} {lsf lsf' : LSF} {vCap eCap : ℕ}
    (hc : c.Exact lsf lsf') (hR : ∀ x ∈ lsf'.F.R, x < vCap) (hF : ∀ e ∈ lsf.F.F.E, e < eCap) :
    c.words ≤ vCap + eCap + 2 := by
  have h1 := lsfChange_size_eq hc
  have h2 := lsfChangeSize_le hR hF
  simp only [LSFChange.words]
  omega

/-! ## Memory -/

/-- A change record depends only on its own `c.words` cells. -/
theorem lsfChangeAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {c : LSFChange}
    (hC : LSFChangeAt mem₁ a c) (h : ∀ x, a ≤ x → x < a + c.words → mem₂ x = mem₁ x) :
    LSFChangeAt mem₂ a c := by
  obtain ⟨h0, hr, h1, hf⟩ := hC
  have hw : c.words = 2 + (c.roots.length + c.fDel.length) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h a le_rfl (by omega)]; exact h0
  · exact listAt_of_agree hr fun x hx1 hx2 => h x (by omega) (by omega)
  · rw [h _ (by omega) (by omega)]; exact h1
  · exact listAt_of_agree hf fun x hx1 hx2 => h x (by omega) (by omega)

/-- The six copies of the step write below `z` only, so they keep the memory zero from `z`. -/
theorem zeroFrom_asmBrStepCopy {m : ℕ → ℕ} {o r h₁ h z : ℕ} (hz : ZeroFrom m z)
    (ho : o + 4 ≤ z) (hr : r + 2 ≤ z) : ZeroFrom (asmBrStepCopy m o r h₁ h) z := by
  intro a ha
  rw [asmBrStepCopy_other (by omega) (by omega)]
  exact hz a ha

/-- The six copies keep every cell outside the two target ranges. -/
theorem asmBrStepCopy_keep {m : ℕ → ℕ} {o r h₁ h a : ℕ} (ho : ¬ (o ≤ a ∧ a < o + 4))
    (hr : ¬ (r ≤ a ∧ a < r + 2)) : asmBrStepCopy m o r h₁ h a = m a :=
  asmBrStepCopy_other (by omega) (by omega)

/-- Two ranges of four and two cells, of which no cell of the first lies in the second, are
apart. -/
theorem slots_apart {o r : ℕ} (h : ∀ a, o ≤ a → a < o + 4 → ¬ (r ≤ a ∧ a < r + 2)) :
    o + 4 ≤ r ∨ r + 2 ≤ o := by
  by_contra hc
  exact h (max o r) (le_max_left _ _) (by omega) ⟨le_max_right _ _, by omega⟩

end MinCostFlow.SparseCore.Program
