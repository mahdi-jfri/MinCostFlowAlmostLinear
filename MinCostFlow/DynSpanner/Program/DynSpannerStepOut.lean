module

public import MinCostFlow.DynSpanner.Program.StateLayout
public import MinCostFlow.DynSpanner.Program.CanonicalSparsify
public import MinCostFlow.DynSpanner.ReembDefs

/-!
# The postcondition of one step of Algorithm 6 (`DynSpannerStepOut`)

One update of Algorithm 6 (Theorem 8.2, page 64) is the model function `step` of
`MinCostFlow/DynSpanner/Defs.lean`. Its program has two branches, `0 < j` and `j = 0`, where `j`
is the level that `chooseLevel` picks. Both branches end in the same state of memory, which this
file names `StepOutPost`, so that the loop over a batch of updates can be proved once against it.

The file has only the definition. The theorems that a branch meets it are in the files of that
branch.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-- The memory after one step of Algorithm 6 (Theorem 8.2, page 64) on the update `u`, run from the
state `runState G₀ q (canonicalSparsify impl) us k`. A caller has `us[k]? = some u`, so that the
new state is `runState … us (k + 1)`.

* The words `heapStep, …, heapStep + 4` hold the step's output header
  `[uhPtr, |U_H|, uhWords, dPtr, |D|]`.
* At `uhPtr` lies a batch of `uhWords` words whose records are a reordering of `U_H`, the changes
  to `H`. At `dPtr` lies a list without repeats of the edges of `D`.
* Memory is zero from the returned pointer `retFinal` on.
* With new metadata `x'` (one more heap interval `[heapStep, retFinal)`), the memory holds the new
  state (`DynSpannerStateAt`) and the history invariant at `k + 1` (`RevHistoryInv`).
* Below `heapStep`, every word outside the old state's footprint `metaFoot b x` is unchanged. -/
def StepOutPost (G₀ : MGraph) (L q vCap eCap b k : ℕ) (impl : SparsifyImpl)
    (us : List Update) (u : Update) (mem0 : ℕ → ℕ) (x : DynSpannerMeta L)
    (heapStep : ℕ) (memFinal : ℕ → ℕ) (retFinal : ℕ) : Prop :=
  let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  let res := step st u (canonicalSparsify impl)
  ∃ (uhPtr uhWords dPtr : ℕ) (uhActual : List Update) (dL : List ℕ) (x' : DynSpannerMeta L),
    memFinal heapStep = uhPtr ∧
    memFinal (heapStep + 1) = uhActual.length ∧
    memFinal (heapStep + 2) = uhWords ∧
    memFinal (heapStep + 3) = dPtr ∧
    memFinal (heapStep + 4) = dL.length ∧
    heapStep + 5 ≤ dPtr ∧ dPtr + dL.length ≤ uhPtr ∧ uhPtr + uhWords = retFinal ∧
    BatchBodyAt memFinal uhPtr st.H uhActual uhWords ∧
    uhActual.Perm res.UH ∧
    dL.Nodup ∧ dL.toFinset = res.D ∧ ListAt memFinal dPtr dL ∧
    ZeroFrom memFinal retFinal ∧
    x'.vCap = vCap ∧ x'.eCap = eCap ∧
    x'.intervals = x.intervals ++ [(heapStep, retFinal)] ∧
    DynSpannerStateAt L vCap eCap b memFinal x' res.state ∧
    RevHistoryInv G₀ q (canonicalSparsify impl) us (k + 1) x' ∧
    (∀ a < heapStep, ¬ metaFoot b x a → memFinal a = mem0 a)

/-- `StepOutPost` extended with a 2-word suffix `[rPtr, rL.length]` stored at `[ret0, ret0 + 1]`,
where `retFinal = ret0 + 2` and `rL` is a duplicate-free list at `rPtr` (below `ret0`) whose
elements are `stepReembSet st u`. -/
def StepReembOutPost (G₀ : MGraph) (L q vCap eCap b k : ℕ) (impl : SparsifyImpl)
    (us : List Update) (u : Update) (mem0 : ℕ → ℕ) (x : DynSpannerMeta L)
    (heapStep : ℕ) (memFinal : ℕ → ℕ) (retFinal : ℕ) : Prop :=
  let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  ∃ (memPre : ℕ → ℕ) (ret0 rPtr : ℕ) (rL : List ℕ),
    retFinal = ret0 + 2 ∧
    StepOutPost G₀ L q vCap eCap b k impl us u mem0 x heapStep memPre ret0 ∧
    memFinal = Function.update (Function.update memPre ret0 rPtr) (ret0 + 1) rL.length ∧
    rL.Nodup ∧ rL.toFinset = stepReembSet st u ∧
    (rPtr + rL.length ≤ b + dsFixedSize L vCap eCap ∨ (heapStep ≤ rPtr ∧ rPtr + rL.length ≤ ret0)) ∧
    ListAt memPre rPtr rL

end

end MinCostFlow.DynSpanner.Program
