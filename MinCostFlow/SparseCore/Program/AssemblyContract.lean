module

public import MinCostFlow.SparseCore.Program.Contract
public import MinCostFlow.Chain.BundleRestartMach
public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.DynSpanner.Program.CanonicalSparsify
public import MinCostFlow.DynSpanner.Program.DynSpannerDSBank

/-!
# The ordered sparse-core contract with the parameters a program needs

A program of the sparse-core tool (Lemma 5.17, page 23, with the bundle repair described in the
README) must
meet `sparseCoreOrdMachineContract` for every level of the chain with one and the same code. The
contract fixes the number of branches `k`, the size bounds `M`, `N`, the limb count `L` and the
number format as logical parameters only: no argument and no memory word holds them. So a single
program cannot know how many branches to build, and cannot find the length of edge `e` (it is at
`lengths + e * L`). Its costs also grow with `log (eCap + 2)` (order store and tours) and with
`L` (the LSF numbers), while the model pays `bundleLogFactor M N`.

This file states the smallest change of the contract that removes these problems, as a separate
definition. The contract itself is unchanged.

* `sparseCoreOrdMachineContractK`: the initialization also receives `k`, `M` and `N` as words;
  the update costs `(k + 1) · (words + editWords + 1) · bundleLogFactor M N` more, because every
  branch applies the input batch and the edits to its own search trees; readout `5` costs the log
  factor per word, because listing the ends of a branch's output graph in its tours costs a
  search-tree step per end; readout `2` gives the stretches with their own limb count `L_w`,
  which it writes after the four pointers, with
  `L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) · (⌊log₂ (M + N + 2)⌋ + 1)`.
* `SparseCoreCapHyp capExp limbMul L M N vCap eCap`: the capacities are at most `(M + N + 2) ^ capExp`
  and the limb count is at most `limbMul · bundleLogFactor M N`. Splitting `capExp` from `limbMul`
  keeps the word-size exponent `P.wordExp` independent of `limbMul`, while `P.mul` may depend on
  both `capExp` and `limbMul`.
* `SparseCoreOrdProgramImplements`: the statement that a program implements the changed contract
  for the bundle tool with the machine cost, at the number format of its LSF initializer.

Only definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.MinRatio MinCostFlow.LSF

/-- Input-independent additive constant for readout `2`'s stretch limb-count bound
`L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)`.
Chosen (`128`) so that P3's canonical stretch limb count `canonLw` (which has additive terms
`Nat.log 2 (lemma55RhoConst K_AN + 1) + 6 * Nat.log 2 (Nat.log 2 (n₀ + 2) + 2) + 8`, totaling
at most `79 + 6 * (log₂ (M + N + 2) + 1)` for `lowStretchSpanningTree_lsst`) meets the bound for
every `capExp : ℕ`. -/
def sparseCoreReadout2LimbConst : ℕ := 128

/-- The ordered sparse-core contract with the parameters a program needs. It is
`sparseCoreOrdMachineContract` with four changes.
* Initialization arguments `[graph, lengths, gradient, ord, k, M, N, heap]`. The words at
  positions `1`–`3` are those of the old contract, so `initPost` and `initCost` read the same
  words.
* Update (`0`) costs `P.mul · (Δ cost + (k + 1) · (words + editWords + 1) · bundleLogFactor M N)`.
* LSF readout (`2`) writes, after the four pointers of `LSFAt`, the limb count `L_w` of the
  stretch arrays, with `L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) · (⌊log₂ (M + N + 2)⌋ + 1)`,
  and its space is `5`.
* Order readout (`5`) costs `P.mul · (ordRotWords + 1) · bundleLogFactor M N`. -/
noncomputable def sparseCoreOrdMachineContractK {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation
  { D with
    initPre := fun args mem => ∃ graph lengths gradient ord heap,
      args = [graph, lengths, gradient, ord, k, M, N, heap] ∧
      (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w ∧
      D.initPre [graph, lengths, gradient, ord, heap] mem
    post := fun i a args mem a' mem' => match i with
      | 2 => a' = a ∧ ∃ forestVCap forestECap,
          mem' (heapArg args + 4) ≤
            L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
          LSFAt mem' (heapArg args) forestVCap forestECap fmt.limbBits
            (mem' (heapArg args + 4)) fmt.precision a.G.E (tool.lsfs a.st (args.getD 1 0))
      | i => D.post i a args mem a' mem'
    cost := fun i a args mem => match i with
      | 0 => P.mul * (tool.cost (ordUpdateNext fmt L a args mem).st - tool.cost a.st +
          (k + 1) * (args.getD 3 0 + args.getD 5 0 + 1) * SparseCore.bundleLogFactor M N)
      | 5 => P.mul * (ordRotWords a (args.getD 1 0) + 1) * SparseCore.bundleLogFactor M N
      | i => D.cost i a args mem
    space := fun i a args mem => match i with
      | 2 => 5
      | i => D.space i a args mem }

/-- The capacities and the limb count are bounded in terms of the size bounds:
`vCap + eCap + 2 ≤ (M + N + 2) ^ capExp` and `L ≤ limbMul · bundleLogFactor M N`. Splitting
`capExp` from `limbMul` keeps the word-size exponent `P.wordExp` independent of `limbMul`
(the solver meets `capExp = 3` while `limbMul` is near `220000`), while `P.mul` may depend on
both `capExp` and `limbMul`. -/
def SparseCoreCapHyp (capExp limbMul L M N vCap eCap : ℕ) : Prop :=
  vCap + eCap + 2 ≤ (M + N + 2) ^ capExp ∧ L ≤ limbMul * SparseCore.bundleLogFactor M N

/-- The program `p` with procedures `init` and `op 0, …, op 5` implements the changed ordered
contract for the bundle tool with the machine cost, `lsfInit` and the sparsifier `canonicalSparsify
impl`, at the number format of the LSF initializer (limbs of `4` bits, `L_in` limbs, precision
`P_fp`). The word-size exponent `wordExp` depends on `capExp` alone (before `limbMul`); the cost
multiplier `P.mul` and space function `allocation` may depend on both `capExp` and `limbMul`,
still free of the input. -/
def SparseCoreOrdProgramImplements (E : SparseCoreEnv) (lsfInit : LSFInit) (L_in P_fp : ℕ)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (w : ℕ) (fmt : Num.Format w) (L : ℕ) (G : MGraph) (k M N vCap eCap : ℕ),
        fmt.limbBits = 4 → L = L_in → fmt.precision = P_fp →
        SparseCoreCapHyp capExp limbMul L M N vCap eCap →
        ∃ R : DSRep (SparseCoreOrdAbs (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L
            (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl))),
          R.Local ∧ R.Implements w p init op
            (sparseCoreOrdMachineContractK fmt L
              (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L
                (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl))
              G k M N vCap eCap capExp P allocation)

end MinCostFlow.SparseCore.Program
