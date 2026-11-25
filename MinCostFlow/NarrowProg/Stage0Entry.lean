module

public import WordRAM.Sep.Adequacy
public import WordRAM.Sep.Layout
public import WordRAM.Entry
public import MinCostFlow.NarrowProg.Stage0Defs

/-!
# Entry theorem for `narrowMain`

`WordRAM.runsTo_of_meets_entry` (`WordRAM/Sep/Entry.lean`) takes a specification whose named value
is the raw input list `List ℕ`. This file proves the analogous entry theorem
`runsTo_of_meets_narrowEntry` for a specification whose named value is a valid instance
`{ I : Instance // I.IsValid }` with `narrowEncode I` at address `0` and an explicit word-size
precondition `Fits I hv`, avoiding any input-decoding obligation at the entry boundary.
-/

@[expose] public section

open WordRAM WordRAM.Sep

namespace MinCostFlow.NarrowProg

/-- Entry specification of procedure `0` whose named value is a valid instance `(I, hv)`, owning
`narrowEncode I` at address `0`, zeroed free memory up to `2 ^ w`, and `T I hv` credits, and
returning an output list at address `0` satisfying `Good I hv out`. -/
def narrowEntrySpec (w : ℕ)
    (Fits : (I : Instance) → I.IsValid → Prop)
    (T : (I : Instance) → I.IsValid → ℕ)
    (Good : (I : Instance) → I.IsValid → List ℕ → Prop) :
    Spec { I : Instance // I.IsValid } where
  pre d args := ⌜args = [(narrowEncode d.1).length] ∧ Fits d.1 d.2⌝ * $ (T d.1 d.2 : ℤ) *
    (Assn.list 0 (narrowEncode d.1) *
      Assn.free (narrowEncode d.1).length (2 ^ w - (narrowEncode d.1).length))
  post d _ v := ⨆ out : List ℕ, ⌜v = out.length ∧ Good d.1 d.2 out⌝ * Assn.list 0 out

/-- **Entry theorem for valid instances.** If procedure `0` meets `narrowEntrySpec w Fits T Good`,
then on every valid instance `(I, hv)` satisfying `Fits I hv` whose encoded words and length fit
in `w`-bit words, and for every random tape `ω`, the program halts with an output satisfying
`Good I hv out` in at most `T I hv + 2` steps. -/
theorem runsTo_of_meets_narrowEntry {w : ℕ} {p : Program}
    {Fits : (I : Instance) → I.IsValid → Prop}
    {T : (I : Instance) → I.IsValid → ℕ}
    {Good : (I : Instance) → I.IsValid → List ℕ → Prop}
    (hp : Meets w p 0 (narrowEntrySpec w Fits T Good))
    {I : Instance} (hv : I.IsValid) (hfits : Fits I hv)
    (hlen : (narrowEncode I).length < 2 ^ w)
    (hwords : ∀ x ∈ narrowEncode I, x < 2 ^ w) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo w p (narrowEncode I) ω out cost ∧ Good I hv out ∧ cost ≤ T I hv + 2 := by
  obtain ⟨body, hproc, ht⟩ := hp
  set input := narrowEncode I
  have hlist : ListAt (initMem input) 0 (input ++ List.replicate (2 ^ w - input.length) 0) :=
    listAt_append.mpr ⟨listAt_initMem input,
      (zeroFrom_initMem input).listAt_replicate (by omega)⟩
  obtain ⟨h, hl, hin, hok⟩ := Assn.exists_list_of_listAt (w := w) hlist (by simp; omega)
  rw [Assn.list_append, zero_add] at hl
  have hmem : ∀ a, initMem input a < 2 ^ w := by
    intro a
    simp only [initMem]
    rcases Nat.lt_or_ge a input.length with ha | ha
    · rw [List.getD_eq_getElem _ _ ha]; exact hwords _ (List.getElem_mem ha)
    · rw [List.getD_eq_default _ _ ha]; exact Nat.two_pow_pos w
  have hpre : (⌜argRegs [input.length] = argRegs [input.length]⌝ *
      (narrowEntrySpec w Fits T Good).pre ⟨I, hv⟩ [input.length]) h (T I hv) :=
    Assn.pure_mul_apply.mpr ⟨rfl, Assn.pure_credits_apply.mpr ⟨⟨rfl, hfits⟩, by
      rw [sub_self]; exact hl⟩⟩
  obtain ⟨o, st', k, h', hrun, ⟨c', hq⟩, hin', -, -, -, hk⟩ :=
    (ht ⟨I, hv⟩ [input.length]).runs
      (fun _ _ => Assn.noDebt_iSup fun _ => (Assn.noDebt_pure _).mul (Assn.noDebt_list _ _))
      (st := startState [input.length] (initMem input) 0) hpre hin hok
      (wordsOk_startState (by simpa using hlen) hmem) ω
  obtain ⟨h₁, h₂, c₁, c₂, hd, rfl, -, hpost, -⟩ := hq
  obtain ⟨out, hout⟩ := (Assn.iSup_apply _ _ _).mp hpost
  obtain ⟨⟨hret, hgood⟩, hlo⟩ := Assn.pure_mul_apply.mp hout
  have hat : ListAt st'.mem 0 out := Assn.listAt_of_list hlo ((Heap.in_union hd).mp hin').1
  refine ⟨out, argsSize [.const input.length] + k + 1, ?_, hgood, ?_⟩
  · refine runsTo_iff_exists_runs.mpr ⟨.normal,
      { st' with regs := Function.update (fun _ => 0) 0 o.value },
      runs_call_iff.mpr ⟨[input.length], body, o, st', k, by simp [evalArgs, Expr.eval, hlen],
        hproc, hrun, rfl, rfl, rfl⟩, ?_⟩
    simp only [Function.update_self]
    refine List.ext_getElem (by simp [hret]) fun i hi _ => ?_
    simp only [List.getElem_map, List.getElem_range]
    simpa using hat i (by simp at hi; omega)
  · simp only [argsSize, Expr.size]
    omega

end MinCostFlow.NarrowProg
