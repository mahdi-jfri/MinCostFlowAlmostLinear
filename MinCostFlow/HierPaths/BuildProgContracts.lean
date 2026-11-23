module

public import MinCostFlow.HierPaths.BuildProgData

/-!
# The router and the core as procedures

The program of the static construction calls two procedures it does not implement: the router
(`RouterFn`, with the operation count `RouterCostFn`) and the core cut player
(`core`, with the count `coreCost`). This file states their contracts in the heap discipline
(`heapContract`: the last argument is the heap pointer, memory below it is kept, memory from
the returned pointer on is zero).

The words of the inputs and outputs:
* a vertex set `X` is its sorted list of members (`finsetWords`);
* the terminal pairs are a `layoutList` of the sets `A_1, B_1, A_2, B_2, …` (`pairsWords`);
* a router result is a `layoutList` with a tag: `[0]`, then the matchings (each a list of
  `u, v` words, in `csrList` form), then the walks `emb j` of the flattened matching; or `[1]`
  then the cut `U` and an empty third section (`routeResultWords`);
* a core result is a tag and a set: `[0]` and the cut, or `[1]` and the expander
  (`coreResultWords`).

`RouterProcContract` and `CoreProcContract` are indexed by the inputs, as `InitRestContract` is:
a procedure meets the router contract when it meets `RouterProcContract … G X pairs` for all
inputs. The cost of a call is `K` times the count of the abstract player plus `K` per input
word, so the counts `routeCost` and `coreCost` of `buildCost` are the costs of the calls up to
the constant `K`, and the bounds `IsMatchingPlayer.cost_bound` and `IsCorePlayer.cost_le` carry
over.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The words of a vertex set: its members in increasing order. -/
def finsetWords (X : Finset ℕ) : List ℕ := X.sort (· ≤ ·)

/-- The words of a list of terminal pairs: the sets `A_1, B_1, A_2, B_2, …` as a `layoutList`. -/
def pairsWords (pairs : List (Finset ℕ × Finset ℕ)) : List ℕ :=
  layoutList (pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2])

/-- The words of a router result. -/
def routeResultWords : RouteResult → List ℕ
  | .matched Ms emb => layoutList
      [[0], csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2]),
        csrList Ms.flatten.length emb]
  | .cut U => layoutList [[1], finsetWords U, []]

/-- The words of a core result. -/
def coreResultWords : CoreResult → List ℕ
  | .cut U => layoutList [[0], finsetWords U]
  | .expander S => layoutList [[1], finsetWords S]

/-- Supremum of `sR gn gLen pLen` over parameter budgets `0 .. parCap`. -/
def routerSpaceUpTo (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (gn gLen pLen parCap : ℕ) : ℕ :=
  (Finset.range (parCap + 1)).sup (sR gn gLen pLen)

theorem le_routerSpaceUpTo {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {gn gLen pLen par parCap : ℕ}
    (h : par ≤ parCap) :
    sR gn gLen pLen par ≤ routerSpaceUpTo sR gn gLen pLen parCap :=
  Finset.le_sup (f := sR gn gLen pLen) (Finset.mem_range.mpr (by omega))

theorem routerSpaceUpTo_mono {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {gn gLen pLen par₁ par₂ : ℕ}
    (h : par₁ ≤ par₂) :
    routerSpaceUpTo sR gn gLen pLen par₁ ≤ routerSpaceUpTo sR gn gLen pLen par₂ :=
  Finset.sup_le fun _ hx => le_routerSpaceUpTo (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)) h)

/-- **The contract of the router**, for the host `G`, the set `X` and the pairs `pairs`. The
arguments are `[gAddr, xAddr, pAddr, Δ, L, b, z, X.card, pairs.length, h]`: the host, the set and
the pairs are at `gAddr`, `xAddr`, `pAddr`, below the heap pointer `h`. Under `G.IsValid` and the
preconditions of `IsMatchingPlayer.spec` (`RouterPre`, `2 ≤ b`), the call writes `routeResultWords`
of `route G X pairs Δ L b z` at `h` and returns a bumped heap cursor `v ≥ h + |output|` with
`ZeroFrom mem' v`. It costs at most
`K (routeCost G X pairs Δ L b z + |G| + |X| * (L + 1) + |pairs| + 1)` and uses at most
`sR G.n G.encode.length (pairsWords pairs).length (Δ + L + b + z)` new cells. -/
def RouterProcContract (w K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) :
    Contract :=
  let C := heapContract w
    (fun args mem => ∃ (gAddr xAddr pAddr Δ L b z h : ℕ),
      args = [gAddr, xAddr, pAddr, Δ, L, b, z, X.card, pairs.length, h] ∧
      GraphAt mem gAddr G ∧ G.IsValid ∧
      ListAt mem xAddr (finsetWords X) ∧ ListAt mem pAddr (pairsWords pairs) ∧
      gAddr + G.encode.length ≤ h ∧ xAddr + (finsetWords X).length ≤ h ∧
      pAddr + (pairsWords pairs).length ≤ h ∧ RouterPre G X pairs Δ L ∧ 2 ≤ b)
    (fun _ _ _ => True)
    (fun args _ => K * (routeCost G X pairs (args.getD 3 0) (args.getD 4 0) (args.getD 5 0)
      (args.getD 6 0) + G.encode.length + (finsetWords X).length * (args.getD 4 0 + 1) +
      (pairsWords pairs).length + 1))
    (fun args _ => sR G.n G.encode.length (pairsWords pairs).length
      (args.getD 3 0 + args.getD 4 0 + args.getD 5 0 + args.getD 6 0))
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
        ∃ (gAddr xAddr pAddr Δ L b z h : ℕ),
          args = [gAddr, xAddr, pAddr, Δ, L, b, z, X.card, pairs.length, h] ∧
          ListAt mem' h (routeResultWords (route G X pairs Δ L b z)) ∧
          h + (routeResultWords (route G X pairs Δ L b z)).length ≤ v }

/-- The shared precondition, frame, cost, and space of a core call. -/
def coreHeapContract (w K M r : ℕ) (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ)
    (q : ℕ) (G : Graph) : Contract :=
  heapContract w
    (fun args mem => ∃ (gAddr h : ℕ), args = [q, gAddr, M, r, h] ∧ GraphAt mem gAddr G ∧
      gAddr + G.encode.length ≤ h ∧ q ≤ r ∧ G.IsValid ∧ G.IsLoopless ∧
      G.n ≤ (NOf M r) ^ q ∧ ∀ v < G.n, G.deg v ≤ deltaParam M)
    (fun _ _ _ => True)
    (fun _ _ => K * (coreCost q G + G.encode.length + 1))
    (fun _ _ => sC G.encode.length)

/-- **The contract of the core.** The call reads the graph and the levels from
the words `[q, gAddr, M, r, h]` (with `q ≤ r ≤ ell M`), writes a certified answer at `h`,
and returns a bumped heap cursor `v ≥ h + (coreResultWords res).length` with `ZeroFrom mem' v`. -/
def CoreProcContract (w K M r : ℕ) (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ)
    (q : ℕ) (G : Graph) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ (gAddr h : ℕ), args = [q, gAddr, M, r, h] ∧ GraphAt mem gAddr G ∧
      gAddr + G.encode.length ≤ h ∧ q ≤ r ∧ r ≤ ell M ∧ G.IsValid ∧ G.IsLoopless ∧
      G.n ≤ (NOf M r) ^ q ∧ ∀ v < G.n, G.deg v ≤ deltaParam M)
    (fun _ _ _ => True)
    (fun _ _ => K * (coreCost q G + G.encode.length + 1))
    (fun _ _ => sC G.encode.length)
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
        ∃ (gAddr h : ℕ) (res : CoreResult), args = [q, gAddr, M, r, h] ∧
          ListAt mem' h (coreResultWords res) ∧ h + (coreResultWords res).length ≤ v ∧
          CoreOutcomeSpec ParamConfig.default M q G res }

/-- The specialization that writes a particular model answer. -/
def CoreExactProcContract (w K M r : ℕ) (core : ℕ → Graph → CoreResult)
    (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ) (q : ℕ) (G : Graph) : Contract :=
  let C := coreHeapContract w K M r coreCost sC q G
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
        ∃ (gAddr h : ℕ), args = [q, gAddr, M, r, h] ∧ ListAt mem' h (coreResultWords (core q G)) ∧
          v = h + (coreResultWords (core q G)).length }

/-- A program provides the router at procedure `f` when `f` meets the router contract for all
inputs. -/
def ProvidesRouter (w K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ G X pairs, MeetsContract w p f (RouterProcContract w K route routeCost sR G X pairs)

/-- A program provides the core when every valid call writes a certified answer. -/
def ProvidesCore (w K M r : ℕ) (coreCost : ℕ → Graph → ℕ)
    (sC : ℕ → ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ q G, MeetsContract w p f (CoreProcContract w K M r coreCost sC q G)

/-- A core that is specified by an exact model function. -/
def ProvidesExactCore (w K M r : ℕ) (core : ℕ → Graph → CoreResult)
    (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ q G, MeetsContract w p f (CoreExactProcContract w K M r core coreCost sC q G)

end MinCostFlow.HierPaths
