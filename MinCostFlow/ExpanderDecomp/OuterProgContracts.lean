module

public import WordRAM.Contract
public import WordRAM.Logic
public import MinCostFlow.ExpanderDecomp.OuterCorePlayer
public import MinCostFlow.ExpanderDecomp.OuterCost
public import MinCostFlow.ExpanderDecomp.MatchingPlayer
public import MinCostFlow.ExpanderDecomp.RouteMeets
public import MinCostFlow.ExpanderDecomp.RouteCallCost
public import MinCostFlow.ExpanderDecomp.PortGraph
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.ExpanderDecomp.ProgRemoveFake
public import MinCostFlow.ExpanderDecomp.ProgCloud
public import MinCostFlow.ExpanderDecomp.ProgCompLabels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Word-RAM Contracts for the Subprocedures of the Outer Expander Decomposition

This file fixes the shared memory layouts and Word-RAM `Contract` specifications for every
subprocedure called by the outer expander decomposition program:

1. **Shared flat memory layouts**, matching `ProgRelabel.lean`, `ProgCloud.lean`,
   `ProgRemoveFake.lean`, and `ProgCompLabels.lean`:
   - graphs as `GraphAt mem gAddr G` (read back by `readGraph`);
   - vertex sets as `ListAt mem vertsAddr verts` (or length-prefixed `LenListAt`, read back by
     `readLenPrefixedList`);
   - edge lists as `EdgesAt mem edgesAddr edges`;
   - single terminal pairs as `SinglePairAt mem pairsAddr A_list B_list` (read back by
     `readSinglePair`);
   - port owners as `portOwnersList edges`;
   - router and core outcomes as `RouteOutAt` and `CoreOutAt`.
2. **Concrete merged contracts**:
   - `cloud_isCloudExpander`: connects `ProgCloud.cloud` (built by `cloudExpanderContract`) to
     `PortGraph.IsCloudExpander`;
   - `removeFakeContract` (`ProgRemoveFake.lean`), together with `progRemoveFakeCost_le_trim`
     showing `ProgRemoveFake.removeFakeCost` meets the trimming bound of `OuterCost.lean` with
     `trimC = 2 ^ 30`;
   - `compLabelsInContract` (`ProgCompLabels.lean`).
3. **Parameterized subprocedure contracts**:
   - `outerPortGraphContract`: builds `portGraph cloud G X` and `portOwnersList` in linear time
     `O(|X| + |E| + 1)` using a reusable zeroed local-ID table `locAddr` and heap `h`;
   - `outerRouterContract` (and specialization `routeOrCutContract` for `routeOrCut` /
     `routeOrCutCost`): computes the static matching player output within `C_rt * routeCost + C_rt`;
   - `outerCoreContract`: computes the recursive core player output within `C_core * coreCost + C_core`;
   - `OuterSubprocIndices` and `OuterSubprocContracts`: bundled indices and `MeetsContract`
     hypotheses for the outer procedures and top-level program.
4. **Non-vacuity witnesses**: `outerPortGraphContract_pre_example`,
   `outerRouterContract_pre_example`, and `outerCoreContract_pre_example`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Shared Memory Readers and Layout Predicates -/

/-- Read a graph stored in `GraphAt` format (`[n, m, u_0, v_0, ...]`) at `gAddr`. -/
def readGraph (mem : ℕ → ℕ) (gAddr : ℕ) : Graph :=
  ⟨mem gAddr, readEdges mem (gAddr + 2) (mem (gAddr + 1))⟩

/-- A list `xs` stored with its length prefix `[xs.length, x_0, x_1, ...]` at `addr`. -/
def LenListAt (mem : ℕ → ℕ) (addr : ℕ) (xs : List ℕ) : Prop :=
  mem addr = xs.length ∧ ListAt mem (addr + 1) xs

/-- Read a length-prefixed list stored at `addr`. -/
def readLenPrefixedList (mem : ℕ → ℕ) (addr : ℕ) : List ℕ :=
  readList mem (addr + 1) (mem addr)

/-- A single terminal pair `(A_list, B_list)` stored in flat multi-pair layout
`[1, |A|, a_0, ..., |B|, b_0, ...]` at `addr` (total `3 + |A| + |B|` words). -/
def SinglePairAt (mem : ℕ → ℕ) (addr : ℕ) (A_list B_list : List ℕ) : Prop :=
  mem addr = 1 ∧
  mem (addr + 1) = A_list.length ∧
  ListAt mem (addr + 2) A_list ∧
  mem (addr + 2 + A_list.length) = B_list.length ∧
  ListAt mem (addr + 3 + A_list.length) B_list

/-- Read the single terminal pair `(A, B)` stored at `addr` in `SinglePairAt` format. -/
def readSinglePair (mem : ℕ → ℕ) (addr : ℕ) : Finset ℕ × Finset ℕ :=
  let lenA := mem (addr + 1)
  let lenB := mem (addr + 2 + lenA)
  ((readList mem (addr + 2) lenA).toFinset, (readList mem (addr + 3 + lenA) lenB).toFinset)

/-- Flat list of port owners `[e_0.1, e_0.2, e_1.1, e_1.2, ...]` of length `2 * edges.length`. -/
def portOwnersList (edges : List (ℕ × ℕ)) : List ℕ :=
  edges.flatMap fun e => [e.1, e.2]

/-- Output layout of a static matching-player call at `outAddr`:
* `.matched matchings _`: tag `0`, total matching edge count `|matchings.flatten|`, and flat edge
  pairs `matchings.flatten` at `outAddr + 2`;
* `.cut U`: tag `1`, nodup vertex list `U_list` with `U_list.toFinset = U`, length at `outAddr + 1`,
  and entries at `outAddr + 2`. -/
def RouteOutAt (mem : ℕ → ℕ) (outAddr : ℕ) : RouteResult → Prop
  | .matched matchings _ =>
      mem outAddr = 0 ∧
      mem (outAddr + 1) = matchings.flatten.length ∧
      EdgesAt mem (outAddr + 2) matchings.flatten
  | .cut U =>
      mem outAddr = 1 ∧
      ∃ U_list : List ℕ,
        U_list.Nodup ∧ U_list.toFinset = U ∧
        mem (outAddr + 1) = U_list.length ∧
        ListAt mem (outAddr + 2) U_list

/-- Output layout of a recursive core-player call at `outAddr`:
* `.cut U`: tag `0`, nodup vertex list `U_list` with `U_list.toFinset = U`, length at `outAddr + 1`,
  and entries at `outAddr + 2`;
* `.expander S`: tag `1`, nodup vertex list `S_list` with `S_list.toFinset = S`, length at
  `outAddr + 1`, and entries at `outAddr + 2`. -/
def CoreOutAt (mem : ℕ → ℕ) (outAddr : ℕ) : CoreResult → Prop
  | .cut U =>
      mem outAddr = 0 ∧
      ∃ U_list : List ℕ,
        U_list.Nodup ∧ U_list.toFinset = U ∧
        mem (outAddr + 1) = U_list.length ∧
        ListAt mem (outAddr + 2) U_list
  | .expander S =>
      mem outAddr = 1 ∧
      ∃ S_list : List ℕ,
        S_list.Nodup ∧ S_list.toFinset = S ∧
        mem (outAddr + 1) = S_list.length ∧
        ListAt mem (outAddr + 2) S_list

/-! ## 2. Subprocedure Space Bounds and Contracts -/

/-- Heap space bound for the port-graph construction procedure on `k` vertices and `e` edges.
Covers `O(k + e)` internal scratch plus `cloudExpanderSpace (deg v)` across all clouds. -/
def outerPortGraphSpace (C_sp k e : ℕ) : ℕ :=
  C_sp * ((e + 3) ^ 5 + k + 1)

/-- Word-size bound for the port-graph construction contract. -/
def OuterPortGraphWordBound (w n k e vertsAddr edgesAddr locAddr outPgAddr outOwnerAddr h C_sp : ℕ) :
    Prop :=
  vertsAddr + k < 2 ^ w ∧
  edgesAddr + 2 * e < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outPgAddr + 2 + 20 * e ≤ h ∧
  outOwnerAddr + 2 * e ≤ h ∧
  h + outerPortGraphSpace C_sp k e < 2 ^ w ∧
  16 < 2 ^ w

/-- Buffer disjointness for the port-graph construction contract. -/
def OuterPortGraphDisjoint (n k e vertsAddr edgesAddr locAddr outPgAddr outOwnerAddr : ℕ) : Prop :=
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n edgesAddr (2 * e) ∧
  DisjointRange locAddr n outPgAddr (2 + 20 * e) ∧
  DisjointRange locAddr n outOwnerAddr (2 * e) ∧
  DisjointRange outPgAddr (2 + 20 * e) vertsAddr k ∧
  DisjointRange outPgAddr (2 + 20 * e) edgesAddr (2 * e) ∧
  DisjointRange outPgAddr (2 + 20 * e) outOwnerAddr (2 * e) ∧
  DisjointRange outOwnerAddr (2 * e) vertsAddr k ∧
  DisjointRange outOwnerAddr (2 * e) edgesAddr (2 * e)

/-- Contract for building `portGraph cloud G X` and `portOwnersList` from a compact subgraph
`(verts, edges)`. Args: `[k, vertsAddr, e, edgesAddr, locAddr, outPgAddr, outOwnerAddr, h]`.
Restores `locAddr` to all zeros, writes `portGraph cloud ⟨n, edges⟩ X` at `outPgAddr` and
`portOwnersList edges` at `outOwnerAddr`, returns the updated zero-heap cursor `h'`, and runs in
`C_pg * (k + e + 1)` steps. -/
def outerPortGraphContract (cloud : ℕ → Graph) (C_pg C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr e edgesAddr locAddr outPgAddr outOwnerAddr h : ℕ)
      (verts : List ℕ) (edges : List (ℕ × ℕ)),
      args = [k, vertsAddr, e, edgesAddr, locAddr, outPgAddr, outOwnerAddr, h] ∧
      verts.length = k ∧ verts.Nodup ∧ (∀ u ∈ verts, u < n) ∧
      edges.length = e ∧ (∀ ed ∈ edges, ed.1 ∈ verts.toFinset ∧ ed.2 ∈ verts.toFinset) ∧
      ListAt mem vertsAddr verts ∧
      EdgesAt mem edgesAddr edges ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      ZeroFrom mem h ∧
      vertsAddr + k ≤ h ∧
      edgesAddr + 2 * e ≤ h ∧
      locAddr + n ≤ h ∧
      OuterPortGraphWordBound w n k e vertsAddr edgesAddr locAddr outPgAddr outOwnerAddr h C_sp ∧
      OuterPortGraphDisjoint n k e vertsAddr edgesAddr locAddr outPgAddr outOwnerAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let e := args.getD 2 0
    let edgesAddr := args.getD 3 0
    let locAddr := args.getD 4 0
    let outPgAddr := args.getD 5 0
    let outOwnerAddr := args.getD 6 0
    let h := args.getD 7 0
    let verts := readList mem vertsAddr k
    let edges := readEdges mem edgesAddr e
    let X := verts.toFinset
    GraphAt mem' outPgAddr (portGraph cloud (Graph.mk 0 edges) X) ∧
    ListAt mem' outOwnerAddr (portOwnersList edges) ∧
    (∀ u ∈ verts, mem' (locAddr + u) = 0) ∧
    h ≤ v ∧
    v ≤ h + outerPortGraphSpace C_sp k e ∧
    ZeroFrom mem' v ∧
    (∀ a < h,
      (∀ u ∈ verts, a ≠ locAddr + u) →
      (a < outPgAddr ∨ outPgAddr + 2 + 20 * e ≤ a) →
      (a < outOwnerAddr ∨ outOwnerAddr + 2 * e ≤ a) →
      mem' a = mem a)
  cost args _mem :=
    C_pg * (args.getD 0 0 + args.getD 2 0 + 1)

/-- Heap space bound for a static matching-player call on an `n`-vertex host with model cost
`rcost`. -/
def outerRouterSpace (C_sp n rcost : ℕ) : ℕ :=
  C_sp * (rcost + (n + 3) ^ 4 + 1)

/-- Contract for a static matching player (`route`, `routeCost`) invoked on a single terminal pair
`[(A, B)]`. Args: `[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]`.
Writes `RouteOutAt mem' outAddr (route G X [(A, B)] Δ L b z)`, returns the updated zero-heap cursor
`h'`, preserves all memory below `h` outside `[outAddr, outAddr + 2 + 2 * G.n)`, and costs at most
`C_rt * routeCost G X [(A, B)] Δ L b z + C_rt`. The caller gives a host graph with at most
`2 Δ |X|` edges and a threshold `z ≤ |X|`, so that reading the input fits in a cost free of any
larger graph. -/
noncomputable def outerRouterContract (route : RouterFn) (routeCost : RouterCostFn)
    (C_rt C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr pairsAddr Δ L b z outAddr h : ℕ)
      (G : Graph) (X_list A_list B_list : List ℕ),
      args = [gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      LenListAt mem xAddr X_list ∧
      X_list.Nodup ∧
      X_list.toFinset ⊆ Finset.range G.n ∧
      (∀ ed ∈ G.inside X_list.toFinset, ed.1 ≠ ed.2) ∧
      1 ≤ Δ ∧
      (∀ v ∈ X_list.toFinset, G.degIn X_list.toFinset v ≤ Δ) ∧
      1 ≤ L ∧
      X_list.toFinset.card < 2 ^ L ∧
      2 ≤ b ∧
      SinglePairAt mem pairsAddr A_list B_list ∧
      A_list.Nodup ∧ B_list.Nodup ∧
      ValidTerminalPairs X_list.toFinset [(A_list.toFinset, B_list.toFinset)] ∧
      ZeroFrom mem h ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + 1 + X_list.length ≤ h ∧
      pairsAddr + 3 + A_list.length + B_list.length ≤ h ∧
      outAddr + 2 + 2 * G.n ≤ h ∧
      DisjointRange outAddr (2 + 2 * G.n) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + 2 * G.n) xAddr (1 + X_list.length) ∧
      DisjointRange outAddr (2 + 2 * G.n) pairsAddr (3 + A_list.length + B_list.length) ∧
      h + outerRouterSpace C_sp G.n
        (routeCost G X_list.toFinset [(A_list.toFinset, B_list.toFinset)] Δ L b z) < 2 ^ w ∧
      16 < 2 ^ w ∧
      G.m ≤ 2 * Δ * X_list.length ∧
      z ≤ X_list.length
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let pairsAddr := args.getD 2 0
    let Δ := args.getD 3 0
    let L := args.getD 4 0
    let b := args.getD 5 0
    let z := args.getD 6 0
    let outAddr := args.getD 7 0
    let h := args.getD 8 0
    let G := readGraph mem gAddr
    let X := (readLenPrefixedList mem xAddr).toFinset
    let pair := readSinglePair mem pairsAddr
    RouteOutAt mem' outAddr (route G X [pair] Δ L b z) ∧
    h ≤ v ∧
    v ≤ h + outerRouterSpace C_sp G.n (routeCost G X [pair] Δ L b z) ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < outAddr ∨ outAddr + 2 + 2 * G.n ≤ a) → mem' a = mem a)
  cost args mem :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let pairsAddr := args.getD 2 0
    let Δ := args.getD 3 0
    let L := args.getD 4 0
    let b := args.getD 5 0
    let z := args.getD 6 0
    let G := readGraph mem gAddr
    let X := (readLenPrefixedList mem xAddr).toFinset
    let pair := readSinglePair mem pairsAddr
    C_rt * routeCost G X [pair] Δ L b z + C_rt

/-- Specialization of `outerRouterContract` to the concrete static router `routeOrCut` and its
call cost `routerCallCost` (`RouteCallCost.lean`): the model count `routeOrCutCost` plus the work
of reading the input, which has no term in `G.m`. -/
noncomputable def routeOrCutContract (C_rt C_sp w : ℕ) : Contract :=
  outerRouterContract routeOrCut routerCallCost C_rt C_sp w

/-- Heap space bound for a recursive core-player call on an `n`-vertex witness graph with model
cost `ccost`. -/
def outerCoreSpace (C_sp n ccost : ℕ) : ℕ :=
  C_sp * (ccost + (n + 3) ^ 5 + 1)

/-- Contract for a recursive core cut player (`core`, `coreCost`) satisfying `IsCorePlayer`.
Args: `[q, wAddr, M_arg, r_arg, outAddr, h]`.
Writes `CoreOutAt mem' outAddr (core q W)`, returns the updated zero-heap cursor `h'`, preserves
all memory below `h` outside `[outAddr, outAddr + 2 + W.n)`, and costs at most
`C_core * coreCost q W + C_core`. -/
noncomputable def outerCoreContract (M r : ℕ)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (C_core C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (q wAddr outAddr h : ℕ) (W : Graph),
      args = [q, wAddr, M, r, outAddr, h] ∧
      1 ≤ q ∧ q ≤ r ∧
      GraphAt mem wAddr W ∧
      W.IsValid ∧ W.IsLoopless ∧
      (NOf M r) ^ (q - 1) < W.n ∧
      W.n ≤ (NOf M r) ^ q ∧
      (∀ v < W.n, W.deg v ≤ deltaParam M) ∧
      ZeroFrom mem h ∧
      wAddr + 2 + 2 * W.m ≤ h ∧
      outAddr + 2 + W.n ≤ h ∧
      DisjointRange outAddr (2 + W.n) wAddr (2 + 2 * W.m) ∧
      h + outerCoreSpace C_sp W.n (coreCost q W) < 2 ^ w ∧
      16 < 2 ^ w ∧
      M < 2 ^ w ∧
      r < 2 ^ w
  post args mem v mem' :=
    let q := args.getD 0 0
    let wAddr := args.getD 1 0
    let outAddr := args.getD 4 0
    let h := args.getD 5 0
    let W := readGraph mem wAddr
    CoreOutAt mem' outAddr (core q W) ∧
    h ≤ v ∧
    v ≤ h + outerCoreSpace C_sp W.n (coreCost q W) ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < outAddr ∨ outAddr + 2 + W.n ≤ a) → mem' a = mem a)
  cost args mem :=
    let q := args.getD 0 0
    let wAddr := args.getD 1 0
    let W := readGraph mem wAddr
    C_core * coreCost q W + C_core

/-- Procedure indices of the five external subprocedures called by the outer decomposition program. -/
structure OuterSubprocIndices where
  /-- Index of the port-graph builder meeting `outerPortGraphContract`. -/
  bPort : ℕ
  /-- Index of the recursive core player meeting `outerCoreContract`. -/
  bCore : ℕ
  /-- Index of the static matching player meeting `outerRouterContract`. -/
  bRoute : ℕ
  /-- Index of `RemoveFake` meeting `removeFakeContract` (`ProgRemoveFake.lean`). -/
  bRF : ℕ
  /-- Index of `compLabelsInEntry` meeting `compLabelsInContract` (`ProgCompLabels.lean`). -/
  bComp : ℕ

/-- Bundled `MeetsContract` hypotheses for the five subprocedures of the outer decomposition at
word size `w`, together with the model specifications (`IsCloudExpander`, `IsCorePlayer`,
`IsMatchingPlayer`) and cost/space constants. -/
structure OuterSubprocContracts (cfg : ParamConfig) (M r w : ℕ) (p : Program)
    (idx : OuterSubprocIndices)
    (cloud : ℕ → Graph) (α : ℝ)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (C_pg C_core C_rt C_sp routeC : ℕ) : Prop where
  /-- Cloud expanders have expansion `≥ α ≥ 1 / cfg.a₀`. -/
  hcloud : IsCloudExpander cloud α
  /-- Cloud expansion matches `cfg.a₀`. -/
  hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ α
  /-- Core player satisfies the core theorem and the size-sensitive cost bound. -/
  hcore : IsCorePlayer cfg M r core coreCost
  /-- Matching player satisfies the router specification and its step-count bound. -/
  hroute : IsMatchingPlayer route routeCost
  /-- Explicit cost constant `routeC` for `routeCost`. -/
  hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
    X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
    1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
    ValidTerminalPairs X' pairs →
    routeCost G' X' pairs Δ L b z' ≤
      routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L + 1)
  /-- Port-graph builder meets `outerPortGraphContract`. -/
  hPort : MeetsContract w p idx.bPort (outerPortGraphContract cloud C_pg C_sp w)
  /-- Recursive core player meets `outerCoreContract`. -/
  hCoreProg : MeetsContract w p idx.bCore (outerCoreContract M r core coreCost C_core C_sp w)
  /-- Static matching player meets `outerRouterContract`. -/
  hRouteProg : MeetsContract w p idx.bRoute (outerRouterContract route routeCost C_rt C_sp w)
  /-- `RemoveFake` meets `removeFakeContract` (`ProgRemoveFake.lean`). -/
  hRF : MeetsContract w p idx.bRF (removeFakeContract w)
  /-- Connected-component labeling meets `compLabelsInContract` (`ProgCompLabels.lean`). -/
  hComp : MeetsContract w p idx.bComp (compLabelsInContract w)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Layout Reader Equivalences -/

lemma readGraph_eq_of_graphAt {mem : ℕ → ℕ} {gAddr : ℕ} {G : Graph}
    (h : GraphAt mem gAddr G) : readGraph mem gAddr = G := by
  cases G with
  | mk n edges =>
    unfold readGraph
    have hn : mem gAddr = n := graphAt_n h
    have hm : mem (gAddr + 1) = edges.length := graphAt_m h
    have he : EdgesAt mem (gAddr + 2) edges := graphAt_to_edgesAt h
    rw [hn, hm, readEdges_eq_of_edgesAt he]

lemma readLenPrefixedList_eq_of_lenListAt {mem : ℕ → ℕ} {addr : ℕ} {xs : List ℕ}
    (h : LenListAt mem addr xs) : readLenPrefixedList mem addr = xs := by
  unfold readLenPrefixedList
  rw [h.1]
  exact readList_eq_of_listAt h.2

lemma readSinglePair_eq_of_singlePairAt {mem : ℕ → ℕ} {addr : ℕ} {A_list B_list : List ℕ}
    (h : SinglePairAt mem addr A_list B_list) :
    readSinglePair mem addr = (A_list.toFinset, B_list.toFinset) := by
  rcases h with ⟨_, hlenA, hA, hlenB, hB⟩
  unfold readSinglePair
  simp only [hlenA, hlenB]
  rw [readList_eq_of_listAt hA, readList_eq_of_listAt hB]

lemma portOwnersList_length (edges : List (ℕ × ℕ)) :
    (portOwnersList edges).length = 2 * edges.length := by
  induction edges with
  | nil => simp [portOwnersList]
  | cons e rest ih =>
    simp only [portOwnersList, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

lemma portOwnersList_getD (edges : List (ℕ × ℕ)) {p : ℕ} (hp : p < 2 * edges.length) :
    (portOwnersList edges).getD p 0 =
      let e := edges.getD (p / 2) (0, 0)
      if p % 2 = 0 then e.1 else e.2 := by
  induction edges generalizing p with
  | nil => simp at hp
  | cons ed rest ih =>
    cases p with
    | zero =>
      simp [portOwnersList]
    | succ p' =>
      cases p' with
      | zero =>
        simp [portOwnersList]
      | succ p'' =>
        have hlen : p'' < 2 * rest.length := by simp at hp; omega
        have hdiv : (p'' + 2) / 2 = p'' / 2 + 1 := by omega
        have hmod : (p'' + 2) % 2 = p'' % 2 := by omega
        simpa [portOwnersList, hdiv, hmod] using ih hlen

lemma inside_mk_eq_self {n : ℕ} {edges : List (ℕ × ℕ)} {X : Finset ℕ}
    (hed : ∀ ed ∈ edges, ed.1 ∈ X ∧ ed.2 ∈ X) :
    (Graph.mk n edges).inside X = edges := by
  unfold Graph.inside
  exact List.filter_eq_self.mpr fun e he => by
    have h := hed e he
    simp [h.1, h.2]

/-- `portOwner` depends on `G` only through `G.inside X`. -/
lemma portOwner_eq_of_inside_eq {G₁ G₂ : Graph} {X : Finset ℕ}
    (h : G₁.inside X = G₂.inside X) (p : ℕ) :
    portOwner G₁ X p = portOwner G₂ X p := by
  unfold portOwner
  rw [h]

/-- `portGraph` depends on `G` only through `G.inside X`. -/
lemma portGraph_eq_of_inside_eq (cloud : ℕ → Graph) {G₁ G₂ : Graph} {X : Finset ℕ}
    (h : G₁.inside X = G₂.inside X) :
    portGraph cloud G₁ X = portGraph cloud G₂ X := by
  unfold portGraph allCloudEdges cloudEdgesFor cloudPortsList
  have hpo : portOwner G₁ X = portOwner G₂ X := funext (portOwner_eq_of_inside_eq h)
  rw [h, hpo]

/-- Every entry `p < 2 * edges.length` of `portOwnersList edges` equals `portOwner G X p` whenever
`G.inside X = edges`. -/
lemma portOwnersList_getD_eq_portOwner {G : Graph} {X : Finset ℕ} {edges : List (ℕ × ℕ)}
    (hin : G.inside X = edges) {p : ℕ} (hp : p < 2 * edges.length) :
    (portOwnersList edges).getD p 0 = portOwner G X p := by
  rw [portOwnersList_getD edges hp]
  unfold portOwner
  rw [hin]

/-! ## 4. Bridges to Merged `ProgCloud` and `ProgRemoveFake` -/

/-- `ProgCloud.cloud` satisfies `PortGraph.IsCloudExpander` with `cloudAlpha = 1 / 12`. -/
theorem cloud_isCloudExpander : IsCloudExpander cloud cloudAlpha where
  n_eq _ hs := (cloud_spec hs).1
  isValid _ hs := (cloud_spec hs).2.1
  deg_le _ hs := (cloud_spec hs).2.2.2.1
  expansion _ hs := (cloud_spec hs).2.2.2.2

/-- The concrete step bound `ProgRemoveFake.removeFakeCost` at `ρ = 1 / Λ` satisfies the trimming
cost shape of `OuterCost.lean` with constant `2 ^ 30` (fitting `trimC ≤ 2 ^ 36 * cfg.u ^ 3` even at
`cfg.u = 1`). -/
theorem progRemoveFakeCost_le_trim {M k e mF Λ : ℕ}
    (hk : k ≤ 2 * e) (hmF : mF ≤ e) (heM : e ≤ M) (he1 : 1 ≤ e) (hLam1 : 1 ≤ Λ) :
    removeFakeCost k e mF 1 Λ ≤ 2 ^ 30 * (e * Λ ^ 2 * (LParam M) ^ 2) := by
  have hasymp := removeFakeCost_le_asymptotic k e mF 1 Λ le_rfl hLam1
  dsimp only at hasymp
  have hlog_le : Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 ≤ LParam M := by
    have h2 : 2 * (e + 2 * mF) + 1 ≤ 2 ^ (ell M + 2) := by
      have hpow : 2 * M + 2 ≤ 2 ^ ell M := Nat.le_pow_clog (by decide) (2 * M + 2)
      have h4 : 2 ^ (ell M + 2) = 4 * 2 ^ ell M := by ring
      omega
    have hlog2 : Nat.log 2 (2 * (e + 2 * mF) + 1) ≤ ell M + 2 := by
      have := Nat.log_mono_right (b := 2) h2
      rwa [Nat.log_pow (by decide)] at this
    have hell1 : 1 ≤ ell M := one_le_ell M
    unfold LParam
    omega
  have hLam_pos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hLam1
  have hL_pos : (1 : ℝ) ≤ (LParam M : ℝ) := by
    have := four_le_LParam M
    exact_mod_cast (by omega : 1 ≤ LParam M)
  have hL_ge : ((Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 : ℕ) : ℝ) ≤ (LParam M : ℝ) := by
    exact_mod_cast hlog_le
  have hdiv : ((1 : ℕ) : ℝ) / (Λ : ℝ) = 1 / (Λ : ℝ) := by norm_num
  have hinv_sq :
      ((Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 : ℕ) : ℝ) ^ 2 / ((1 : ℝ) / (Λ : ℝ)) ^ 2 ≤
        (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2 := by
    rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hL_ge 2) (by positivity)
  have hLamL_ge1 : (1 : ℝ) ≤ (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hLam1
    have h1sq : (1 : ℝ) ≤ (Λ : ℝ) ^ 2 := by nlinarith
    have hLsq : (1 : ℝ) ≤ (LParam M : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hk_r : (k : ℝ) ≤ 2 * (e : ℝ) := by exact_mod_cast hk
  have hmF_r : (mF : ℝ) ≤ (e : ℝ) := by exact_mod_cast hmF
  have he1_r : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
  have hterm1 : (k : ℝ) + (mF : ℝ) ≤ 3 * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by
    have hkm : (k : ℝ) + (mF : ℝ) ≤ 3 * (e : ℝ) := by linarith
    calc (k : ℝ) + (mF : ℝ) ≤ 3 * (e : ℝ) * 1 := by linarith
      _ ≤ 3 * (e : ℝ) * ((Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hLamL_ge1 (by positivity)
      _ = 3 * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by ring
  have hterm2 :
      ((e : ℝ) + (mF : ℝ) + 1) * ((Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 : ℕ) : ℝ) ^ 2 /
        (((1 : ℕ) : ℝ) / (Λ : ℝ)) ^ 2 ≤
      3 * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by
    rw [mul_div_assoc, hdiv]
    calc ((e : ℝ) + (mF : ℝ) + 1) *
          (((Nat.log 2 (2 * (e + 2 * mF) + 1) + 1 : ℕ) : ℝ) ^ 2 / (1 / (Λ : ℝ)) ^ 2)
        ≤ (3 * (e : ℝ)) * ((Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) :=
          mul_le_mul (by linarith) hinv_sq (by positivity) (by positivity)
      _ = 3 * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by ring
  have hreal : (removeFakeCost k e mF 1 Λ : ℝ) ≤
      (2 ^ 30 * (e * Λ ^ 2 * (LParam M) ^ 2) : ℕ) := by
    have hsum : (removeFakeCost k e mF 1 Λ : ℝ) ≤
        600000000 * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by
      linarith
    have hconst : (600000000 : ℝ) ≤ ((2 ^ 30 : ℕ) : ℝ) := by norm_num
    calc (removeFakeCost k e mF 1 Λ : ℝ)
        ≤ 600000000 * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := hsum
      _ ≤ ((2 ^ 30 : ℕ) : ℝ) * ((e : ℝ) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (2 ^ 30 * (e * Λ ^ 2 * (LParam M) ^ 2) : ℕ) := by push_cast; ring
  exact_mod_cast hreal

/-! ## 5. Non-Vacuity Witnesses -/

/-- Non-vacuity of `outerPortGraphContract`: all precondition hypotheses hold simultaneously on the
empty compact subgraph. -/
theorem outerPortGraphContract_pre_example (cloud : ℕ → Graph) (C_pg : ℕ) :
    (outerPortGraphContract cloud C_pg 1 20).pre
      [0, 0, 0, 0, 0, 0, 2, 10] (fun _ => 0) := by
  refine ⟨0, 0, 0, 0, 0, 0, 0, 2, 10, [], [], rfl, rfl, List.nodup_nil,
    by simp, rfl, by simp, fun i hi => by simp at hi, fun j hj => by simp at hj,
    fun _ _ => rfl, fun _ _ => rfl, by omega, by omega, by omega, ?_, ?_⟩
  · unfold OuterPortGraphWordBound outerPortGraphSpace
    omega
  · unfold OuterPortGraphDisjoint DisjointRange
    omega

/-- Non-vacuity of `outerRouterContract`: all precondition hypotheses hold simultaneously on the
empty host graph with empty terminal pair. -/
theorem outerRouterContract_pre_example (route : RouterFn) (routeCost : RouterCostFn)
    (C_rt : ℕ) (h0 : routeCost (Graph.mk 0 []) ∅ [(∅, ∅)] 1 1 2 0 = 0) :
    (outerRouterContract route routeCost C_rt 1 20).pre
      [0, 2, 3, 1, 1, 2, 0, 10, 20]
      (fun a => if a = 3 then 1 else 0) := by
  refine ⟨0, 2, 3, 1, 1, 2, 0, 10, 20, Graph.mk 0 [], [], [], [], rfl,
    ?_, ?_, ?_, List.nodup_nil, by simp, by simp [Graph.inside], le_rfl, by simp,
    le_rfl, by norm_num, by decide, ?_, List.nodup_nil, List.nodup_nil, ?_,
    ?_, by simp [Graph.m], by simp, by simp, by simp,
    Or.inr (by simp [Graph.m]), Or.inr (by simp), Or.inr (by simp), ?_, by decide,
    by simp [Graph.m], by simp⟩
  · intro i hi
    rcases i with _ | _ | i <;> simp [Graph.encode, Graph.m] at hi ⊢
  · intro e he; simp at he
  · exact ⟨by simp, fun i hi => by simp at hi⟩
  · exact ⟨by simp, by simp, fun i hi => by simp at hi, by simp, fun i hi => by simp at hi⟩
  · refine ⟨by simp, ?_⟩
    simp
  · intro a ha
    have : a ≠ 3 := by omega
    simp [this]
  · simp only [List.toFinset_nil, h0]
    unfold outerRouterSpace
    norm_num

/-- Non-vacuity of `outerCoreContract`: all precondition hypotheses hold simultaneously on a
2-vertex edgeless graph at level `q = 1`. -/
theorem outerCoreContract_pre_example
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (C_core : ℕ) (h0 : coreCost 1 (Graph.mk 2 []) = 0) :
    (outerCoreContract 4 1 core coreCost C_core 1 20).pre
      [1, 0, 4, 1, 4, 20]
      (fun a => if a = 0 then 2 else 0) := by
  refine ⟨1, 0, 4, 20, Graph.mk 2 [], rfl, le_rfl, le_rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [Graph.m], by simp, Or.inr (by simp [Graph.m]), ?_,
    by decide, by decide, by decide⟩
  · intro i hi
    rcases i with _ | _ | i <;> simp [Graph.encode, Graph.m] at hi ⊢
  · intro e he; simp at he
  · intro e he; simp at he
  · simp
  · have h4 : 4 ≤ NOf 4 1 := four_le_NOf 4 1
    simp only [pow_one]
    omega
  · intro v _
    simp [Graph.deg, Graph.degIn, Graph.inside]
  · intro a ha
    have : a ≠ 0 := by omega
    simp [this]
  · simp only [h0]
    unfold outerCoreSpace
    norm_num

end MinCostFlow.ExpanderDecomp
