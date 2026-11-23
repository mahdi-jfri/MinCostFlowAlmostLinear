module

public import MinCostFlow.HierPaths.BuildGame
public import MinCostFlow.HierPaths.BuildConn
public import MinCostFlow.HierPaths.BuildErase
public import MinCostFlow.ExpanderDecomp.OuterCorePlayer

/-!
# The batched game of `lemma_3` at one group: the model

The child construction (`lemma_3`) builds, inside the host `G[X]` of a group, an expanding host for
every child, with walks that embed it into `G[X]`. All children have the same size `s` (even, at
least `2`) and child `c` is the interval of terminals `off c, …, off c + s − 1`. Each child keeps
its game graph with the local vertices `0, …, s − 1`, which is the form the core cut player
(`ExpanderDecomp.IsCorePlayer`) takes.

One round (`gameRound`):
1. Every active child asks the core about its game graph (`coreAnswer`). A child whose answer is
   an expander `S` saves `S` and leaves the game.
2. Every other active child takes the smaller side of the core's cut, pads it to a bisection
   `(C', V \ C')` (`padHalf`), and requests a matching from `C'` to `V \ C'`, shifted to terminal
   numbers (`request`).
3. One full-routing call (`lemma1Route`, see `lemma_1`) serves all requests at once. Each requesting
   child takes the matched edges whose first end lies in it, with their walks, shifted back to
   local numbers (`takeEntries`), as its next round.

After the rounds, one more call routes the complement of each child's saved set into the saved set
(`injPairs`). The child host is the game graph plus these injection edges (`childEdges`), with
the walks of all its edges (`childWalks`).

The proofs are in `BuildChildSpec.lean`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The state of one child's game: its rounds, each a list of local matching edges with the host
walk of each edge, and its saved set once the core answered with an expander. -/
structure ChildState where
  /-- The rounds: local edges with their host walks. -/
  rounds : List (List ((ℕ × ℕ) × List ℕ))
  /-- The saved expanding set, once the game of this child has ended. -/
  saved : Option (Finset ℕ)

/-- The start of the game: no rounds and nothing saved. -/
def ChildState.init : ChildState := ⟨[], none⟩

/-- The local matching of round `j`. -/
def ChildState.M (st : ChildState) (j : ℕ) : List (ℕ × ℕ) :=
  (st.rounds.getD j []).map Prod.fst

/-- The game graph of a child: the local matchings of all its rounds, on `0, …, s − 1`. -/
def gameGraph (s : ℕ) (st : ChildState) : Graph :=
  ⟨s, witnessEdges st.M st.rounds.length⟩

/-- The core's answer for a child of size `s`, at the least level `q` with `s ≤ N^q`. -/
def coreAnswer (core : ℕ → Graph → CoreResult) (M r s : ℕ) (st : ChildState) : CoreResult :=
  core (coreLevel M r s) (gameGraph s st)

/-- The bisection `C'` that a child pads from the core's cut `U`. -/
def bisectOf (s : ℕ) (U : Finset ℕ) : Finset ℕ :=
  padHalf s (smallerSide (Finset.range s) U)

/-- The request of a child at offset `o`: the shifted bisection `(C', V \ C')` when the child is
active and the core answered with a cut, and nothing otherwise. -/
def request (core : ℕ → Graph → CoreResult) (M r s o : ℕ) (st : ChildState) :
    Option (Finset ℕ × Finset ℕ) :=
  match st.saved with
  | some _ => none
  | none =>
    match coreAnswer core M r s st with
    | .expander _ => none
    | .cut U => some (shiftSet o (bisectOf s U), shiftSet o (Finset.range s \ bisectOf s U))

/-- The children that request a matching in this round. -/
def requesting (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ)
    (sts : ℕ → ChildState) : List ℕ :=
  (List.range k).filter fun c => (request core M r s (off c) (sts c)).isSome

/-- The terminal pairs of one round's router call. -/
def roundPairs (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ)
    (sts : ℕ → ChildState) : List (Finset ℕ × Finset ℕ) :=
  (requesting core M r s k off sts).map fun c => (request core M r s (off c) (sts c)).getD (∅, ∅)

/-- The edges of `F` with the walks `emb`. -/
def rawEntries (F : List (ℕ × ℕ)) (emb : ℕ → List ℕ) : List ((ℕ × ℕ) × List ℕ) :=
  (List.range F.length).map fun j => (edgeAt F j, emb j)

/-- The matched edges of a call with their walks in the host edge list `E`, each shortcut to a walk
that repeats no edge (`erase`). -/
def callEntries (E : List (ℕ × ℕ)) : RouteResult → List ((ℕ × ℕ) × List ℕ)
  | .matched Ms emb => rawEntries Ms.flatten fun j => erase E (edgeAt Ms.flatten j).1 (emb j)
  | .cut _ => []

/-- The entries of a call whose first end lies in the child at offset `o`, shifted back to local
numbers. -/
def takeEntries (s o : ℕ) (es : List ((ℕ × ℕ) × List ℕ)) : List ((ℕ × ℕ) × List ℕ) :=
  (es.filter fun en => decide (en.1.1 ∈ shiftSet o (Finset.range s))).map
    fun en => ((en.1.1 - o, en.1.2 - o), en.2)

/-- One round of the batched game. -/
def gameRound (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) :
    ℕ → ChildState := fun c =>
  let es := callEntries G.edges (lemma1Route route G X (roundPairs core M r s k off sts) Δ L).1
  match (sts c).saved with
  | some _ => sts c
  | none =>
    match coreAnswer core M r s (sts c) with
    | .expander S => ⟨(sts c).rounds, some S⟩
    | .cut _ => ⟨(sts c).rounds ++ [takeEntries s (off c) es], none⟩

/-- The game after `t` rounds. -/
def gameRun (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ) : ℕ → ℕ → ChildState
  | 0 => fun _ => ChildState.init
  | t + 1 => gameRound route G X Δ L core M r s k off (gameRun route G X Δ L core M r s k off t)

/-- The saved set of a child (all of `range s` if the game of the child has not ended). -/
def savedSet (s : ℕ) (st : ChildState) : Finset ℕ :=
  st.saved.getD (Finset.range s)

/-- The terminal pairs of the injection call: each child's complement of its saved set, into the
saved set, shifted to terminal numbers. -/
def injPairs (s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) : List (Finset ℕ × Finset ℕ) :=
  (List.range k).map fun c =>
    (shiftSet (off c) (Finset.range s \ savedSet s (sts c)), shiftSet (off c) (savedSet s (sts c)))

/-- The injection entries of each child after `t` rounds. -/
def injEntries (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ) (t c : ℕ) :
    List ((ℕ × ℕ) × List ℕ) :=
  let sts := gameRun route G X Δ L core M r s k off t
  takeEntries s (off c) (callEntries G.edges (lemma1Route route G X (injPairs s k off sts) Δ L).1)

/-- The local edges of the host of child `c` after `t` rounds: its game graph and its injection
edges. -/
def childEdges (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ) (t c : ℕ) : List (ℕ × ℕ) :=
  let st := gameRun route G X Δ L core M r s k off t c
  witnessEdges st.M st.rounds.length ++
    (injEntries route G X Δ L core M r s k off t c).map Prod.fst

/-- All entries of child `c`: its rounds, then its injection entries. -/
def childFamily (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ) (t c : ℕ) :
    List ((ℕ × ℕ) × List ℕ) :=
  (gameRun route G X Δ L core M r s k off t c).rounds.flatten ++
    injEntries route G X Δ L core M r s k off t c

end MinCostFlow.HierPaths
