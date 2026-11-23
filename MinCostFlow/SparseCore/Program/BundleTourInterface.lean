module

public import MinCostFlow.SparseCore.Program.OrdStoreContract
public import WordRAM.DataStructure

/-!
# Tour query interface for the bundle program (`BundleTourInterface`)

Specifies the three read-only tour operations that the bundle manager needs from
the core rotation tour data structure:

1. `idxList` (`[tourH, v, h]`): writes the end list `cord v` in `EndListAt` layout at `h`
   (matching `ordStoreContract` op `1`), in amortized cost `≤ S.mul * ((cord v).length + 1) * ordStoreLog eCap`.
2. `idxLen` (`[tourH, v, h]`): writes `(cord v).length` at `h`, in amortized cost
   `≤ S.mul * ordStoreLog eCap`.
3. `idxOwner` (`[tourH, key, h]`): for a live end `key = endKey x` belonging to a unique core
   vertex `v`, writes `v` at `h`, in amortized cost `≤ S.mul * ordStoreLog eCap`.

All three follow the `WordRAM.DataStructure` calling convention (last argument is the heap pointer
`h`, return value is the new heap pointer `h'`, `ZeroFrom mem' h'`, and the tour may mutate cells
inside its own `rep.foot` and charge against its own `rep.phi`, accommodating in-place splay
trees). No per-bucket data is needed inside the tour structure.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle

@[expose] public section

/-- Input-independent cost and space parameters of a core-rotation tour module. -/
structure BundleTourSpec where
  /-- Cost multiplier (free of the input). -/
  mul : ℕ
  /-- Heap space bound of `idxList` on a tour of length `len`. -/
  listSpace : ℕ → ℕ
  /-- Heap space bound of `idxLen` and `idxOwner` (at least `1` word for the answer at `h`). -/
  querySpace : ℕ
  listSpace_ge : ∀ len, 1 + len ≤ listSpace len
  listSpace_mono : ∀ {a b}, a ≤ b → listSpace a ≤ listSpace b
  querySpace_ge : 1 ≤ querySpace

/-- Proof that procedures `idxList`, `idxLen`, `idxOwner` of program `p` (at word size `w` and
capacities `vCap, eCap`) provide the three read-only tour queries on a `DSRep (ℕ → List End)`
representation `rep` meeting `S : BundleTourSpec`. -/
structure BundleTourAt (S : BundleTourSpec) (w vCap eCap : ℕ) (p : Program)
    (idxList idxLen idxOwner : ℕ) where
  rep : DSRep (ℕ → List End)
  rep_local : rep.Local
  list_runs : ∀ (tourH v h : ℕ) (cord : ℕ → List End) (tx : rep.τ) (mem : ℕ → ℕ) (pos : ℕ)
      (ω : ℕ → Bool),
      tourH < 2 ^ w → v < vCap → v < 2 ^ w → h < 2 ^ w →
      rep.rep tourH cord tx mem →
      (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.listSpace (cord v).length < 2 ^ w →
      ∃ body, p.procs[idxList]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, v, h] mem pos) o st' c ∧
        rep.rep tourH cord tx' st'.mem ∧
        EndListAt st'.mem h (cord v) ∧
        h + 1 + (cord v).length ≤ o.value ∧
        rep.Respects (rep.foot tourH tx) h (S.listSpace (cord v).length) mem o.value tourH tx'
          st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤
          S.mul * ((cord v).length + 1) * ordStoreLog eCap + rep.phi tourH tx mem
  len_runs : ∀ (tourH v h : ℕ) (cord : ℕ → List End) (tx : rep.τ) (mem : ℕ → ℕ) (pos : ℕ)
      (ω : ℕ → Bool),
      tourH < 2 ^ w → v < vCap → v < 2 ^ w → h < 2 ^ w →
      rep.rep tourH cord tx mem →
      (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.querySpace < 2 ^ w →
      ∃ body, p.procs[idxLen]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, v, h] mem pos) o st' c ∧
        rep.rep tourH cord tx' st'.mem ∧
        st'.mem h = (cord v).length ∧
        h + 1 ≤ o.value ∧
        rep.Respects (rep.foot tourH tx) h S.querySpace mem o.value tourH tx' st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤ S.mul * ordStoreLog eCap + rep.phi tourH tx mem
  owner_runs : ∀ (tourH key v h : ℕ) (cord : ℕ → List End) (tx : rep.τ) (mem : ℕ → ℕ) (pos : ℕ)
      (ω : ℕ → Bool),
      tourH < 2 ^ w → key < 2 * eCap → key < 2 ^ w → v < vCap → h < 2 ^ w →
      endOfKey key ∈ cord v →
      (∀ v', endOfKey key ∈ cord v' → v' = v) →
      rep.rep tourH cord tx mem →
      (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.querySpace < 2 ^ w →
      ∃ body, p.procs[idxOwner]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, key, h] mem pos) o st' c ∧
        rep.rep tourH cord tx' st'.mem ∧
        st'.mem h = v ∧
        h + 1 ≤ o.value ∧
        rep.Respects (rep.foot tourH tx) h S.querySpace mem o.value tourH tx' st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤ S.mul * ordStoreLog eCap + rep.phi tourH tx mem

end

end MinCostFlow.SparseCore.Program
