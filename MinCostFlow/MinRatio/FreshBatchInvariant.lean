module

public import MinCostFlow.MinRatio.FreshRecordInput
public import MinCostFlow.MinRatio.FreshBatchStep

/-!
# Invariant for the fresh-name scan

The scan reads the unread suffix of the external batch and appends to
the translated prefix. At each position the current name tables realize
the model's maps. The model result of translating the suffix, together
with the already written prefix, gives the final answer.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- Address ranges for the input, name tables, counter and output. -/
structure FreshBatchRegions where
  forward : ℕ
  inverse : ℕ
  counter : ℕ
  externalCap : ℕ
  internalCap : ℕ
  input : ℕ
  output : ℕ

/-- The maps and counter lie in distinct regions before the input. -/
def FreshBatchRegions.Separated (r : FreshBatchRegions) : Prop :=
  r.forward + r.externalCap ≤ r.input ∧ r.inverse + r.internalCap ≤ r.input ∧
  r.counter < r.input ∧
  (r.forward + r.externalCap ≤ r.inverse ∨ r.inverse + r.internalCap ≤ r.forward) ∧
  (r.counter < r.forward ∨ r.forward + r.externalCap ≤ r.counter) ∧
  (r.counter < r.inverse ∨ r.inverse + r.internalCap ≤ r.counter)

/-- Addresses that the name translator may change before its output. -/
def FreshBatchRegions.mutable (r : FreshBatchRegions) (a : ℕ) : Prop :=
  a = r.counter ∨ (r.forward ≤ a ∧ a < r.forward + r.externalCap) ∨
    (r.inverse ≤ a ∧ a < r.inverse + r.internalCap)

/-- The exact result returned by the model batch translator. -/
abbrev FreshBatchResult := MGraph × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × List Update

/-- Precondition at a particular point of the scan, including room for
the remaining records and their fresh names. -/
structure FreshBatchInvariant (w : ℕ) (region : FreshBatchRegions)
    (target : FreshBatchResult) (initial : ℕ → ℕ) (rest : List Update) (st : State) where
  external : MGraph
  internal : MGraph
  forward : ℕ → ℕ
  inverse : ℕ → ℕ
  next : ℕ
  written : List Update
  fresh : FreshInv external internal forward inverse next
  valid : external.BatchIsValid rest
  inputFits : ∀ x ∈ rest.flatMap updateWords, x < 2 ^ w
  recordFits : ∀ u ∈ rest, FreshRecordFits region.externalCap u
  spareNames : next + rest.length ≤ region.internalCap
  inputStart : region.input ≤ st.regs 0
  inputEnd : st.regs 0 + (rest.flatMap updateWords).length ≤ region.output
  outputCursor : st.regs 4 = region.output + (written.flatMap updateWords).length
  outputEnd : st.regs 4 + (rest.flatMap updateWords).length < 2 ^ w
  leftWord : rest.length < 2 ^ w
  registers : st.regs 1 = region.forward ∧ st.regs 2 = region.inverse ∧
    st.regs 3 = region.counter ∧ st.regs 5 = rest.length
  tables : FreshTablesAt st.mem region.forward region.inverse region.counter
    region.externalCap region.internalCap forward inverse next
  inputWords : ListAt st.mem (st.regs 0) (rest.flatMap updateWords)
  outputWords : ListAt st.mem region.output (written.flatMap updateWords)
  zero : ZeroFrom st.mem (st.regs 4)
  frame : ∀ a < region.output, ¬ region.mutable a → st.mem a = initial a
  targetEq :
    let suffix := translateBatch external forward inverse next rest
    (suffix.1, suffix.2.1, suffix.2.2.1, suffix.2.2.2.1, written ++ suffix.2.2.2.2) = target

/-- On exit the output contains the translated words and the name tables
hold the model's final values. -/
def FreshBatchDone (region : FreshBatchRegions) (target : FreshBatchResult) (initial : ℕ → ℕ) (st : State) : Prop :=
  ListAt st.mem region.output (target.2.2.2.2.flatMap updateWords) ∧
    FreshTablesAt st.mem region.forward region.inverse region.counter region.externalCap
      region.internalCap target.2.1 target.2.2.1 target.2.2.2.1 ∧
    st.regs 4 = region.output + (target.2.2.2.2.flatMap updateWords).length ∧
    ZeroFrom st.mem (st.regs 4) ∧
    ∀ a < region.output, ¬ region.mutable a → st.mem a = initial a

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- With no unread records, the invariant gives the final output. -/
theorem FreshBatchInvariant.done {w : ℕ} {region : FreshBatchRegions} {target : FreshBatchResult}
    {st : State} {initial : ℕ → ℕ} (h : FreshBatchInvariant w region target initial [] st) :
    FreshBatchDone region target initial st := by
  have heq : (h.external, h.forward, h.inverse, h.next, h.written) = target := by
    simpa only [translateBatch, List.append_nil] using h.targetEq
  rw [← heq]
  exact ⟨h.outputWords, h.tables, h.outputCursor, h.zero, h.frame⟩

end MinCostFlow.MinRatio
