module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPostRec

import Mathlib.Tactic

/-!
# The tour at the end of the first step (`AssemblyFirstStepPostTour`)

The post of the step asks for the tour of the branch in P7's view (`asmBrTourView`), at the caps
`vCap`, `eCap` of the branch, with the new core lists `outCoreOrder info.state ord'` and marks
that are those of some set `E₀` of old output edges (`OutMarksOf`). Phase 4 leaves P2's tour for
`⟨ord', cs'.RF, mk'⟩` at the caps of the bundle side, and Phase 3 gives the marks.

* `tourRep_heq`: a tour state at equal caps, equal up to `HEq`, has the same rep, cells and
  potential. The caps of the bundle side equal those of the branch (from the rep), so this moves
  the tour of Phase 4 to the caps of the branch.
* `asmFsPost_tourView`: P2's tour for `⟨ord', tr'.cs.RF, mk⟩` is P7's view for the core lists
  `outCoreOrder tr' ord'` and the marks `mk`, when `ord'` is the order of a rotation of the new
  graph (`HasRotOrder`, from `AsmBrModelFacts` of the new state): the core lists fit the order
  and the forest (`coreCordOf_outCoreOrder`).
* `outSplitListsAt_le_top`: the place of the first split record is at most the top, so the word
  that the driver writes at `h + 1` is below `2 ^ w`.
* `outMarksOf_cord`: the marks of `OutMarksOf` do not depend on the lists of the state, so the
  marks of Phase 3 (for the lists `coreTour ord' RF`) are marks for the lists `outCoreOrder`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **A tour state along equal caps.** If `v = v'`, `e = e'` and `t` is `t'` up to `HEq`, then
`t` and `t'` have the same rep, the same cells and the same potential. -/
theorem tourRep_heq {TR : ℕ → ℕ → DSRep AsmTourAbs} {v v' e e' : ℕ} (hv : v = v') (he : e = e')
    {t : (TR v e).τ} {t' : (TR v' e').τ} (ht : HEq t t') (tourH : ℕ) :
    (∀ (a : AsmTourAbs) (mem : ℕ → ℕ), (TR v e).rep tourH a t mem ↔ (TR v' e').rep tourH a t' mem) ∧
    (∀ x, (TR v e).foot tourH t x ↔ (TR v' e').foot tourH t' x) ∧
    (∀ mem : ℕ → ℕ, (TR v e).phi tourH t mem = (TR v' e').phi tourH t' mem) := by
  subst hv he
  cases ht
  exact ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl⟩

/-- **P7's view of the new tour.** If `ord'` is the order of a rotation of the graph of `tr'`
and P2's tour holds `⟨ord', tr'.cs.RF, mk⟩`, then P7's view of the tour for the branch state
`⟨tr', ord'⟩` holds the core lists `outCoreOrder tr' ord'` with the marks `mk`. -/
theorem asmFsPost_tourView {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs} {vCap eCap tourH : ℕ}
    {tr' : BundleTreeState depth} {ord' : ℕ → List End} {mk : Finset End}
    {tx : (TR vCap eCap).τ} {mem : ℕ → ℕ} (hrot : HasRotOrder tr' ord')
    (hrep : (TR vCap eCap).rep tourH ⟨ord', tr'.cs.RF, mk⟩ tx mem) :
    (asmBrTourView TR ⟨tr', ord', vCap, eCap⟩ vCap eCap).rep tourH
      ⟨outCoreOrder tr' ord', mk⟩ tx mem :=
  ⟨rfl, ⟨tr'.cs, coreCordOf_outCoreOrder hrot, rfl⟩, hrep⟩

/-- **The place of the first split record is at most `top`.** With no split the place is `0`, and
otherwise the record of five words lies below `top`. So the word that the driver writes at
`h + 1` is below `2 ^ w` when `top` is. -/
theorem outSplitListsAt_le_top {mem : ℕ → ℕ} {top : ℕ} {avoid : ℕ → Prop} {keep E₀ : Finset ℕ}
    {a : ℕ} {G : MGraph} {P : List Update} {Ys : List (List End)}
    (h : OutSplitListsAt mem top avoid keep E₀ a G P Ys) : a ≤ top := by
  match P, Ys, h with
  | [], [], h => simp only [OutSplitListsAt] at h; omega
  | .split _ _ _ _ :: _, _ :: _, h => simp only [OutSplitListsAt] at h; omega

/-- **The marks for other lists.** `OutMarksOf ⟨c, mk⟩ cord E` gives `OutMarksOf ⟨cord, mk⟩ cord E`:
its first part says `c = cord`, and its second part reads only the marks. -/
theorem outMarksOf_cord {c cord : ℕ → List End} {mk : Finset End} {E : Finset ℕ}
    (h : OutMarksOf ⟨c, mk⟩ cord E) : OutMarksOf ⟨cord, mk⟩ cord E :=
  ⟨rfl, h.2⟩

end

end MinCostFlow.SparseCore.Program
