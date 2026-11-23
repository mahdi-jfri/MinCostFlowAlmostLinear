module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue9
public import MinCostFlow.SparseCore.Program.ReadEmbOps

import Mathlib.Tactic

/-!
# The old data that Phase 4 reads (`AssemblyFirstStepGlue10`)

Phase 4 (`asmFirstP4Sel_runs`, `asmFirstPhase4_runs_of_sel`) reads data that the step got as
input and that Phases 1 to 3 do not write: the batch, the order edits, the change record of the
forest, the split entries, the embedding table and the flags of the old output graph. This file
shows that these are still in place after Phase 3.

* `asmFirstStep_keep123`: Phases 1 to 3 keep every cell below `h` outside the old side record and
  the old tour. Phases 1 and 2 keep them (`asmFirstStep_keep12`). Phase 3 keeps every cell below
  its start outside the bundle table and the tour after Phase 2, and below `h` these lie in the
  old side record and the old tour, since all that Phase 2 adds lies at `h` or above.
* `asmFirstStep_p4_inputs`: so the inputs are in place, since they lie below `h` outside every
  part of the branch.
* `asmFirstStep_p4_emb_out`: so are the embedding table and the flags of the old output graph
  (`dgEPresBase`), which are parts of the branch apart from the side record and the tour.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- A change record depends only on its own `c.words` cells. -/
private theorem lsfChangeAt_of_agree' {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {c : LSFChange}
    (hC : LSFChangeAt mem₁ a c) (h : ∀ x, a ≤ x → x < a + c.words → mem₂ x = mem₁ x) :
    LSFChangeAt mem₂ a c := by
  obtain ⟨h0, hr, h1, hf⟩ := hC
  have hw : c.words = 2 + (c.roots.length + c.fDel.length) := rfl
  refine ⟨?_, fun k hk => ?_, ?_, fun k hk => ?_⟩
  · rw [h a le_rfl (by omega)]; exact h0
  · rw [h _ (by omega) (by omega)]; exact hr k hk
  · rw [h _ (by omega) (by omega)]; exact h1
  · rw [h _ (by omega) (by omega)]; exact hf k hk

public section

/-- **Phases 1 to 3 keep the old cells below `h`.** Phases 1 and 2 keep the cells below `h`
outside the side record `Sd` and the tour `Tf₀` (`hK`). Phase 3 keeps the cells below its start
`h₂ ≥ h` outside the bundle table `Bf` and the tour `Tf₁` after Phase 2 (`hK3`). Below `h`, a cell
of `Bf` lies in `Sd`, and a cell of `Tf₁` lies in `Tf₀` (`hBf`, `hTf`). -/
theorem asmFirstStep_keep123 {Sd Tf₀ Tf₁ Bf : ℕ → Prop} {h h₂ : ℕ} {mem mem₂ mem₃ : ℕ → ℕ}
    (hK : ∀ a < h, ¬ Sd a → ¬ Tf₀ a → mem₂ a = mem a)
    (hK3 : ∀ a < h₂, ¬ Bf a → ¬ Tf₁ a → mem₃ a = mem₂ a)
    (hBf : ∀ a, Bf a → Sd a ∨ h ≤ a) (hTf : ∀ a, Tf₁ a → Tf₀ a ∨ h ≤ a) (hh : h ≤ h₂) :
    ∀ a < h, ¬ Sd a → ¬ Tf₀ a → mem₃ a = mem a := by
  intro a ha hs ht
  have hb : ¬ Bf a := fun hb => by
    rcases hBf a hb with h1 | h1
    · exact hs h1
    · omega
  have ht1 : ¬ Tf₁ a := fun ht1 => by
    rcases hTf a ht1 with h1 | h1
    · exact ht h1
    · omega
  rw [hK3 a (by omega) hb ht1]
  exact hK a ha hs ht

/-- **The inputs after Phase 3.** The batch, the order edits, the change record and the split
entries lie below `h` outside the foot `F` of the branch (`InputAt`), which contains the side
record and the tour. Phases 1 to 3 keep such cells (`hK`, from `asmFirstStep_keep123`). -/
theorem asmFirstStep_p4_inputs {F Sd Tf : ℕ → Prop} {w h batch words edits editWords chg spPtr : ℕ}
    {mem mem₃ : ℕ → ℕ} {G : MGraph} {U : List Update} {ed : List OrdEdit} {c : LSFChange}
    {L : List CompSplitEntry}
    (hSd : ∀ a, Sd a → F a) (hTf : ∀ a, Tf a → F a)
    (hK : ∀ a < h, ¬ Sd a → ¬ Tf a → mem₃ a = mem a)
    (hB : SmallBatchAt mem batch G U words) (hBin : InputAt w mem F batch words h)
    (hE : OrdEditsAt mem edits ed editWords) (hEin : InputAt w mem F edits editWords h)
    (hC : LSFChangeAt mem chg c) (hCin : InputAt w mem F chg c.words h)
    (hS : SplitEntriesAt mem spPtr L) (hSin : InputAt w mem F spPtr (splitEntriesWords L) h) :
    SmallBatchAt mem₃ batch G U words ∧ OrdEditsAt mem₃ edits ed editWords ∧
      LSFChangeAt mem₃ chg c ∧ SplitEntriesAt mem₃ spPtr L := by
  have hkeep : ∀ a n, InputAt w mem F a n h → ∀ x, a ≤ x → x < a + n → mem₃ x = mem x := by
    intro a n hin x h1 h2
    have hx := (hin.2 (x - a) (by omega)).2
    rw [Nat.add_sub_cancel' h1] at hx
    exact hK x (by have := hin.1; omega) (fun hs => hx (hSd x hs)) (fun ht => hx (hTf x ht))
  exact ⟨smallBatchAt_of_agree hB (hkeep _ _ hBin), ordEditsAt_of_agree hE (hkeep _ _ hEin),
    lsfChangeAt_of_agree' hC (hkeep _ _ hCin), splitEntriesAt_of_agree hS (hkeep _ _ hSin)⟩

/-- **The embedding table and the old output flags after Phase 3.** Both lie below `h` outside
the side record and the tour (`hEf`, `hOf`), so Phases 1 to 3 keep their cells (`hK`). The table
depends only on its cells (`embRep_local`), and the flags of the edges of the old output graph
are the presence flags of its block (`DynGraphAt`, at `dgEPresBase`). -/
theorem asmFirstStep_p4_emb_out {Sd Tf : ℕ → Prop} {h eCap embH g vCap : ℕ} {mem mem₃ : ℕ → ℕ}
    {v : EmbView} {yE : EmbConc} {S : MGraph}
    (hK : ∀ a < h, ¬ Sd a → ¬ Tf a → mem₃ a = mem a)
    (hEmb : (embRep eCap).rep embH v yE mem)
    (hEf : ∀ a, embFoot eCap embH yE a → a < h ∧ ¬ Sd a ∧ ¬ Tf a)
    (hDG : DynGraphAt mem g vCap eCap S)
    (hOf : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → a < h ∧ ¬ Sd a ∧ ¬ Tf a) :
    (embRep eCap).rep embH v yE mem₃ ∧
      ∀ e < eCap, mem₃ (g + 4 + 7 * vCap + e) = if e ∈ S.E then 1 else 0 := by
  refine ⟨(embRep_local eCap embH v yE mem mem₃ fun a ha => ?_).1 hEmb, fun e he => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hEf a ha
    exact (hK a h1 h2 h3).symm
  · have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
    obtain ⟨h1, h2, h3⟩ := hOf (g + 4 + 7 * vCap + e) (by omega) (by omega)
    rw [hK _ h1 h2 h3]
    exact hDG.2.2.2.2.2.2.2.2.2.2.2.1 e he

end

end MinCostFlow.SparseCore.Program
