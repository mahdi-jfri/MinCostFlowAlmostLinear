module

public import MinCostFlow.MinRatio.FreshBatchLoop
import WordRAM.Tactic

/-!
# Running the fresh-name batch scan as a procedure

The body runs the verified scan on the words after the two batch headers
and returns the end of the translated records. The input count is a
separate argument. A caller can retain the original output address while
the scan advances its cursor. This is the sequential translation in
Algorithm 2 (page 29) for the fixed-graph batches accepted by the IPM.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- Arguments are input body, forward and inverse table bases, counter
address, output body, and number of input records. -/
def freshBatchBody (dispatch : ℕ) : Stmt :=
  freshBatchLoop dispatch ;; .ret (.reg 4)

/-- The initial layout for a scan, before any translated records are written. -/
def FreshBatchInput (w : ℕ) (r : FreshBatchRegions) (G H : MGraph)
    (f g : ℕ → ℕ) (next : ℕ) (updates : List Update) (mem : ℕ → ℕ) : Prop :=
  r.Separated ∧ FreshInv G H f g next ∧ G.BatchIsValid updates ∧
  FreshTablesAt mem r.forward r.inverse r.counter r.externalCap r.internalCap f g next ∧
  (∀ u ∈ updates, FreshRecordFits r.externalCap u) ∧
  (∀ x ∈ updates.flatMap updateWords, x < 2 ^ w) ∧
  next + updates.length ≤ r.internalCap ∧
  r.input + (updates.flatMap updateWords).length ≤ r.output ∧
  r.output + (updates.flatMap updateWords).length < 2 ^ w ∧ updates.length < 2 ^ w ∧
  ListAt mem r.input (updates.flatMap updateWords) ∧ ZeroFrom mem r.output

/-- The procedure exposes the exact model output and table state. -/
def freshBatchBodyContract (w : ℕ) (r : FreshBatchRegions) (G H : MGraph)
    (f g : ℕ → ℕ) (next : ℕ) (updates : List Update) : Contract where
  pre args mem :=
    args = [r.input, r.forward, r.inverse, r.counter, r.output, updates.length] ∧
    FreshBatchInput w r G H f g next updates mem
  post _ mem ret mem' :=
    let target := translateBatch G f g next updates
    ListAt mem' r.output (target.2.2.2.2.flatMap updateWords) ∧
      FreshTablesAt mem' r.forward r.inverse r.counter r.externalCap r.internalCap
        target.2.1 target.2.2.1 target.2.2.2.1 ∧
      ret = r.output + (target.2.2.2.2.flatMap updateWords).length ∧ ZeroFrom mem' ret ∧
      ∀ a < r.output, ¬ r.mutable a → mem' a = mem a
  cost _ _ := 162 * updates.length + 5

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- The initial memory conditions imply the scan invariant with empty output. -/
def FreshBatchInput.invariant {w : ℕ} {r : FreshBatchRegions} {G H : MGraph}
    {f g : ℕ → ℕ} {next pos : ℕ} {updates : List Update} {mem : ℕ → ℕ}
    (h : FreshBatchInput w r G H f g next updates mem) :
    FreshBatchInvariant w r (translateBatch G f g next updates) mem updates
      (startState [r.input, r.forward, r.inverse, r.counter, r.output, updates.length] mem pos) := by
  rcases h with ⟨_, hf, hv, ht, hr, hw, hs, hi, ho, hl, hwords, hz⟩
  exact {
    external := G
    internal := H
    forward := f
    inverse := g
    next := next
    written := []
    fresh := hf
    valid := hv
    inputFits := hw
    recordFits := hr
    spareNames := hs
    inputStart := le_rfl
    inputEnd := hi
    outputCursor := rfl
    outputEnd := ho
    leftWord := hl
    registers := ⟨rfl, rfl, rfl, rfl⟩
    tables := ht
    inputWords := hwords
    outputWords := fun i hlt => by cases hlt
    zero := hz
    frame := fun _ _ _ => rfl
    targetEq := rfl }

/-- The scan procedure is deterministic. -/
theorem freshBatchBody_noRand (dispatch : ℕ) : (freshBatchBody dispatch).NoRand :=
  ⟨freshBatchLoop_noRand dispatch, trivial⟩

/-- The linked scan returns the exact fresh-name batch in at most
`162 * updates.length + 5` machine steps. -/
theorem freshBatchBody_meetsContract {w base ins del dispatch : ℕ} {p : Program}
    (r : FreshBatchRegions) (G H : MGraph) (f g : ℕ → ℕ) (next : ℕ) (updates : List Update)
    (hp : p.HasAt base [freshBatchBody dispatch])
    (hd : p.HasAt dispatch [freshRecordBody ins del])
    (hi : p.HasAt ins [freshInsertBody]) (he : p.HasAt del [freshDeleteBody]) :
    MeetsContract w p base (freshBatchBodyContract w r G H f g next updates) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hpre⟩ := hpre
  have hsep : r.Separated := hpre.1
  have hlo := hpre.invariant (pos := pos)
  have ht := freshBatchLoop_triple_of_placement (w := w)
    (target := translateBatch G f g next updates) (initial := mem) hsep updates hd hi he
  apply runs_start_le
  unfold freshBatchBody
  refine runs_seq_triple_le ht ⟨hlo⟩ ?_
  intro st hdone
  refine runs_ret_le (v := st.regs 4) (by rfl) hdone ?_
  change 0 + (162 * updates.length + 2) + 1 + 2 ≤ 162 * updates.length + 5
  omega

end MinCostFlow.MinRatio
