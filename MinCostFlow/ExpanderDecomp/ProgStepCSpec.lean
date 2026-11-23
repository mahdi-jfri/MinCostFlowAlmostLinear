module

public import WordRAM.Contract
public import WordRAM.Logic
public import MinCostFlow.ExpanderDecomp.OneShot
public import MinCostFlow.ExpanderDecomp.CoreCost
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.ProgEdgeColorBase

import Mathlib.Tactic.Linarith

/-!
# Step C Word-RAM Contracts and Multi-Pair Router Contract (`ProgStepCSpec`)

Fixes the memory layouts and Word-RAM `Contract` specifications for Step C of `OneShot`
(`OneShot.lean`, `CoreCost.lean`):

1. **Multi-pair terminal layout and router contract:**
   - `encodePairs` / `MultiPairsAt` / `readMultiPairs`: flat multi-pair layout
     `[t, |A_0|, a_{0,0}, ..., |B_0|, b_{0,0}, ..., |A_{t-1}|, ..., |B_{t-1}|, ...]`, whose `t = 1`
     case coincides identically with `SinglePairAt` (`OuterProgContracts.lean`), proved in
     `singlePairAt_iff_multiPairsAt`.
   - `multiPairRouterContract C_rt C_sp w`: direct multi-pair generalization of
     `routeOrCutContract C_rt C_sp w` (`OuterProgContracts.lean`) using the same arguments
     `[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]`, output layout `RouteOutAt`, heap bound
     `outerRouterSpace`, and cost `C_rt * routerCallCost ... + C_rt`. Proves
     `multiPairRouterContract_implies_routeOrCutContract`.
2. **Shared routing-phase output layout (`StepOutAt`):**
   - For `Sum.inr calls`: tag `0`, length `|(callsFakeEdges calls)|`, and flat edge list
     `EdgesAt mem (outAddr + 2) (callsFakeEdges calls)` (passed directly to `removeFake` in Step D).
   - For `Sum.inl U`: tag `1`, nodup list `U_list` with `U_list.toFinset = U`, length at
     `outAddr + 1`, and entries at `outAddr + 2` (matching `RouteOutAt` / `CoreOutAt`).
3. **Step C contracts (`stepCContract` and `stepCLeftoverContract`):**
   - `stepCContract cfg cloud C_stepC C_sp w`: computes `stepCMacro cfg routeOrCut cloud G X vs b k z`
     from `GraphAt`, `LenListAt`, and `ColoredEdgesAt` of `edgeColor17 (cloud k)` in cost at most
     `C_stepC * stepCMacroCost ... + C_stepC`, restoring the pre-zeroed `locAddr` array without
     scanning `range G.n`.
   - `stepCLeftoverContract cfg C_left C_sp w`: computes `stepCLeftover cfg routeOrCut G X vs b z`
     (calling the router on the single pair `[(leftoverVerts vs b, fullVerts vs b)]`, compatible
     directly with `routeOrCutContract`) in cost at most `C_left * stepCLeftoverCost ... + C_left`.
4. **Non-vacuity witnesses:** `multiPairRouterContract_pre_example`, `stepCContract_pre_example`,
   and `stepCLeftoverContract_pre_example`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Flat Multi-Pair Terminal Layout and Multi-Pair Router Contract -/

/-- Flat encoding of one terminal pair `(A_list, B_list)`: `[|A|, a_0, ..., |B|, b_0, ...]`. -/
def encodePair (p : List ℕ × List ℕ) : List ℕ :=
  p.1.length :: p.1 ++ p.2.length :: p.2

/-- Flat encoding of a list of terminal pairs `pairs`:
`[pairs.length] ++ pairs.flatMap encodePair`. At `pairs = [(A, B)]` this coincides with
`SinglePairAt` (`OuterProgContracts.lean`). -/
def encodePairs (pairs : List (List ℕ × List ℕ)) : List ℕ :=
  pairs.length :: pairs.flatMap encodePair

/-- Flat multi-pair layout at `addr`: `ListAt mem addr (encodePairs pairs)`. -/
def MultiPairsAt (mem : ℕ → ℕ) (addr : ℕ) (pairs : List (List ℕ × List ℕ)) : Prop :=
  ListAt mem addr (encodePairs pairs)

/-- Read `count` encoded terminal pairs starting at word offset `off` in `mem`. -/
def readMultiPairsAux (mem : ℕ → ℕ) : ℕ → ℕ → List (Finset ℕ × Finset ℕ)
  | 0, _ => []
  | count + 1, off =>
      let lenA := mem off
      let lenB := mem (off + 1 + lenA)
      let pair := ((readList mem (off + 1) lenA).toFinset,
        (readList mem (off + 2 + lenA) lenB).toFinset)
      pair :: readMultiPairsAux mem count (off + 2 + lenA + lenB)

/-- Read the list of terminal pairs stored at `addr` in `MultiPairsAt` format. -/
def readMultiPairs (mem : ℕ → ℕ) (addr : ℕ) : List (Finset ℕ × Finset ℕ) :=
  readMultiPairsAux mem (mem addr) (addr + 1)

/-- Multi-pair generalization of `routeOrCutContract` (`OuterProgContracts.lean`), using the exact
same arguments `[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]`, output layout `RouteOutAt`,
heap space `outerRouterSpace`, and cost `C_rt * routerCallCost ... + C_rt`. The caller gives a
host graph with at most `2 Δ |X|` edges and a threshold `z ≤ |X|`; the call cost
`routerCallCost` (`RouteCallCost.lean`) then pays for reading the input with no term in `G.m`. -/
noncomputable def multiPairRouterContract (C_rt C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr pairsAddr Δ L b z outAddr h : ℕ)
      (G : Graph) (X_list : List ℕ) (pairLists : List (List ℕ × List ℕ)),
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
      MultiPairsAt mem pairsAddr pairLists ∧
      (∀ p ∈ pairLists, p.1.Nodup ∧ p.2.Nodup) ∧
      ValidTerminalPairs X_list.toFinset (pairLists.map fun p => (p.1.toFinset, p.2.toFinset)) ∧
      ZeroFrom mem h ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + 1 + X_list.length ≤ h ∧
      pairsAddr + (encodePairs pairLists).length ≤ h ∧
      outAddr + 2 + 2 * G.n ≤ h ∧
      DisjointRange outAddr (2 + 2 * G.n) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + 2 * G.n) xAddr (1 + X_list.length) ∧
      DisjointRange outAddr (2 + 2 * G.n) pairsAddr (encodePairs pairLists).length ∧
      h + outerRouterSpace C_sp G.n
        (routerCallCost G X_list.toFinset
          (pairLists.map fun p => (p.1.toFinset, p.2.toFinset)) Δ L b z) < 2 ^ w ∧
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
    let pairs := readMultiPairs mem pairsAddr
    RouteOutAt mem' outAddr (routeOrCut G X pairs Δ L b z) ∧
    h ≤ v ∧
    v ≤ h + outerRouterSpace C_sp G.n (routerCallCost G X pairs Δ L b z) ∧
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
    let pairs := readMultiPairs mem pairsAddr
    C_rt * routerCallCost G X pairs Δ L b z + C_rt

/-! ## 2. Shared Output Layout and Step C Contracts -/

/-- Output layout of a `OneShot` routing phase (`stepB`, `stepCMacro`, or `stepCLeftover`) at
`outAddr`:
* `Sum.inr calls`: tag `0`, length `|(callsFakeEdges calls)|`, and flat edge pairs
  `callsFakeEdges calls` at `outAddr + 2` (matching `EdgesAt` for `removeFake`);
* `Sum.inl U`: tag `1`, nodup vertex list `U_list` with `U_list.toFinset = U`, length at
  `outAddr + 1`, and entries at `outAddr + 2` (matching `RouteOutAt` / `CoreOutAt`). -/
def StepOutAt (mem : ℕ → ℕ) (outAddr : ℕ) : (Finset ℕ ⊕ List RoutedCall) → Prop
  | .inr calls =>
      mem outAddr = 0 ∧
      mem (outAddr + 1) = (callsFakeEdges calls).length ∧
      EdgesAt mem (outAddr + 2) (callsFakeEdges calls)
  | .inl U =>
      mem outAddr = 1 ∧
      ∃ U_list : List ℕ,
        U_list.Nodup ∧ U_list.toFinset = U ∧
        mem (outAddr + 1) = U_list.length ∧
        ListAt mem (outAddr + 2) U_list

/-- Heap-space bound for `stepCContract` (`stepCMacro`). -/
def stepCSpace (C_sp n xLen k costM : ℕ) : ℕ :=
  (C_sp + 1) * (costM + 20 * (n + 3) ^ 4 + 400 * (xLen + k + 1))

/-- Output buffer size for `stepCContract` (`2 + 34 * xLen` words, covering either a cut `U ⊆ X`
or up to `17 * xLen` fake edges). -/
def stepCOutSize (xLen : ℕ) : ℕ :=
  2 + 34 * xLen

/-- Word-size and disjointness bundle for `stepCContract`. -/
def StepCLayout (w n m xLen k colM gAddr xAddr colAddr locAddr outAddr h C_sp costM : ℕ) : Prop :=
  gAddr + 2 + 2 * m ≤ h ∧
  xAddr + 1 + xLen ≤ h ∧
  colAddr + 3 * colM ≤ h ∧
  locAddr + n ≤ h ∧
  outAddr + stepCOutSize xLen ≤ h ∧
  DisjointRange locAddr n gAddr (2 + 2 * m) ∧
  DisjointRange locAddr n xAddr (1 + xLen) ∧
  DisjointRange locAddr n colAddr (3 * colM) ∧
  DisjointRange locAddr n outAddr (stepCOutSize xLen) ∧
  DisjointRange outAddr (stepCOutSize xLen) gAddr (2 + 2 * m) ∧
  DisjointRange outAddr (stepCOutSize xLen) xAddr (1 + xLen) ∧
  DisjointRange outAddr (stepCOutSize xLen) colAddr (3 * colM) ∧
  h + stepCSpace C_sp n xLen k costM < 2 ^ w ∧
  16 < 2 ^ w

/-- **Step C macro-join contract** (`stepCMacro` in `OneShot.lean`).
Args: `[gAddr, xAddr, b, k, z, Δ, L, colM, colAddr, locAddr, outAddr, h]`.
Given `GraphAt mem gAddr G`, sorted vertex list `LenListAt mem xAddr vs`, `b > 0`,
`k = numFullBlocks vs b`, `Δ = cfg.Δ`, `L = cfg.L`, `ColoredEdgesAt mem colAddr (edgeColor17 (cloud k))`
(when `2 ≤ k`), a pre-zeroed reusable `locAddr` array of size `G.n`, and zero-heap `h`:
- writes `StepOutAt mem' outAddr (stepCMacro cfg routeOrCut cloud G vs.toFinset vs b k z)`;
- restores `locAddr` to all zeros without scanning `range G.n`;
- preserves all memory `< h` outside `locAddr` and `[outAddr, outAddr + stepCOutSize vs.length)`;
- returns the updated zero-heap cursor `h' ∈ [h, h + stepCSpace ...]` with `ZeroFrom mem' h'`;
- runs in at most `C_stepC * stepCMacroCost cfg routeOrCut routerCallCost cloud G X vs b k z + C_stepC`
  deterministic steps. -/
noncomputable def stepCContract (cfg : CoreParams) (cloud : ℕ → Graph)
    (C_stepC C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr b k z colM colAddr locAddr outAddr h : ℕ)
      (G : Graph) (vs : List ℕ),
      args = [gAddr, xAddr, b, k, z, cfg.Δ, cfg.L, colM, colAddr, locAddr, outAddr, h] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      LenListAt mem xAddr vs ∧
      vs.Pairwise (· < ·) ∧
      vs.toFinset ⊆ Finset.range G.n ∧
      (∀ ed ∈ G.inside vs.toFinset, ed.1 ≠ ed.2) ∧
      1 ≤ cfg.Δ ∧
      (∀ v ∈ vs.toFinset, G.degIn vs.toFinset v ≤ cfg.Δ) ∧
      1 ≤ cfg.L ∧
      vs.length < 2 ^ cfg.L ∧
      0 < b ∧
      k = numFullBlocks vs b ∧
      (2 ≤ k →
        (cloud k).n = k ∧
        (cloud k).IsValid ∧
        (∀ v < k, (cloud k).deg v ≤ 9) ∧
        colM = (edgeColor17 (cloud k)).length ∧
        ColoredEdgesAt mem colAddr (edgeColor17 (cloud k))) ∧
      (∀ u < G.n, mem (locAddr + u) = 0) ∧
      ZeroFrom mem h ∧
      StepCLayout w G.n G.m vs.length k colM gAddr xAddr colAddr locAddr outAddr h C_sp
        (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z) ∧
      G.m ≤ 2 * cfg.Δ * vs.length ∧
      z ≤ vs.length
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let b := args.getD 2 0
    let k := args.getD 3 0
    let z := args.getD 4 0
    let locAddr := args.getD 9 0
    let outAddr := args.getD 10 0
    let h := args.getD 11 0
    let G := readGraph mem gAddr
    let vs := readLenPrefixedList mem xAddr
    let X := vs.toFinset
    let costM := stepCMacroCost cfg routeOrCut routerCallCost cloud G X vs b k z
    StepOutAt mem' outAddr (stepCMacro cfg routeOrCut cloud G X vs b k z) ∧
    (∀ u < G.n, mem' (locAddr + u) = 0) ∧
    h ≤ v ∧
    v ≤ h + stepCSpace C_sp G.n vs.length k costM ∧
    ZeroFrom mem' v ∧
    (∀ a < h,
      (a < locAddr ∨ locAddr + G.n ≤ a) →
      (a < outAddr ∨ outAddr + stepCOutSize vs.length ≤ a) →
      mem' a = mem a)
  cost args mem :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let b := args.getD 2 0
    let k := args.getD 3 0
    let z := args.getD 4 0
    let G := readGraph mem gAddr
    let vs := readLenPrefixedList mem xAddr
    let X := vs.toFinset
    C_stepC * stepCMacroCost cfg routeOrCut routerCallCost cloud G X vs b k z + C_stepC

/-- Heap-space bound for `stepCLeftoverContract` (`stepCLeftover`). -/
def stepCLeftoverSpace (C_sp n xLen costL : ℕ) : ℕ :=
  (C_sp + 1) * (costL + 2 * (n + 3) ^ 4 + 20 * (xLen + 1))

/-- **Step C leftover-injection contract** (`stepCLeftover` in `OneShot.lean`).
Args: `[gAddr, xAddr, b, z, Δ, L, locAddr, outAddr, h]`.
Calls the single-pair router (`routeOrCutContract`) when `leftoverVerts vs b` is nonempty,
writes `StepOutAt mem' outAddr (stepCLeftover cfg routeOrCut G vs.toFinset vs b z)` into
`[outAddr, outAddr + 2 + 2 * vs.length)`, restores `locAddr` to zeros, and runs in
`C_left * stepCLeftoverCost ... + C_left` deterministic steps. -/
noncomputable def stepCLeftoverContract (cfg : CoreParams) (C_left C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr b z locAddr outAddr h : ℕ) (G : Graph) (vs : List ℕ),
      args = [gAddr, xAddr, b, z, cfg.Δ, cfg.L, locAddr, outAddr, h] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      LenListAt mem xAddr vs ∧
      vs.Pairwise (· < ·) ∧
      vs.toFinset ⊆ Finset.range G.n ∧
      (∀ ed ∈ G.inside vs.toFinset, ed.1 ≠ ed.2) ∧
      1 ≤ cfg.Δ ∧
      (∀ v ∈ vs.toFinset, G.degIn vs.toFinset v ≤ cfg.Δ) ∧
      1 ≤ cfg.L ∧
      vs.length < 2 ^ cfg.L ∧
      0 < b ∧
      (0 < vs.length % b → b ≤ vs.length) ∧
      (∀ u < G.n, mem (locAddr + u) = 0) ∧
      ZeroFrom mem h ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + 1 + vs.length ≤ h ∧
      locAddr + G.n ≤ h ∧
      outAddr + 2 + 2 * vs.length ≤ h ∧
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) ∧
      DisjointRange locAddr G.n xAddr (1 + vs.length) ∧
      DisjointRange locAddr G.n outAddr (2 + 2 * vs.length) ∧
      DisjointRange outAddr (2 + 2 * vs.length) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + 2 * vs.length) xAddr (1 + vs.length) ∧
      h + stepCLeftoverSpace C_sp G.n vs.length
        (stepCLeftoverCost cfg routerCallCost G vs.toFinset vs b z) < 2 ^ w ∧
      16 < 2 ^ w ∧
      G.m ≤ 2 * cfg.Δ * vs.length ∧
      z ≤ vs.length
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let b := args.getD 2 0
    let z := args.getD 3 0
    let locAddr := args.getD 6 0
    let outAddr := args.getD 7 0
    let h := args.getD 8 0
    let G := readGraph mem gAddr
    let vs := readLenPrefixedList mem xAddr
    let X := vs.toFinset
    let costL := stepCLeftoverCost cfg routerCallCost G X vs b z
    StepOutAt mem' outAddr (stepCLeftover cfg routeOrCut G X vs b z) ∧
    (∀ u < G.n, mem' (locAddr + u) = 0) ∧
    h ≤ v ∧
    v ≤ h + stepCLeftoverSpace C_sp G.n vs.length costL ∧
    ZeroFrom mem' v ∧
    (∀ a < h,
      (a < locAddr ∨ locAddr + G.n ≤ a) →
      (a < outAddr ∨ outAddr + 2 + 2 * vs.length ≤ a) →
      mem' a = mem a)
  cost args mem :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let b := args.getD 2 0
    let z := args.getD 3 0
    let G := readGraph mem gAddr
    let vs := readLenPrefixedList mem xAddr
    let X := vs.toFinset
    C_left * stepCLeftoverCost cfg routerCallCost G X vs b z + C_left

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Multi-Pair Layout Lemmas and Compatibility with `routeOrCutContract` -/

lemma encodePair_length (p : List ℕ × List ℕ) :
    (encodePair p).length = 2 + p.1.length + p.2.length := by
  simp only [encodePair, List.length_cons, List.length_append]
  omega

lemma encodePairs_singleton_length (A B : List ℕ) :
    (encodePairs [(A, B)]).length = 3 + A.length + B.length := by
  simp only [encodePairs, List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, encodePair_length]
  omega

/-- `SinglePairAt` (`OuterProgContracts.lean`) is identically the 1-pair case of `MultiPairsAt`. -/
theorem singlePairAt_iff_multiPairsAt {mem : ℕ → ℕ} {addr : ℕ} {A B : List ℕ} :
    SinglePairAt mem addr A B ↔ MultiPairsAt mem addr [(A, B)] := by
  unfold SinglePairAt MultiPairsAt encodePairs encodePair
  simp only [List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append]
  constructor
  · rintro ⟨h0, h1, hA, h2, hB⟩
    rw [listAt_cons]
    refine ⟨h0, ?_⟩
    rw [listAt_cons]
    refine ⟨h1, ?_⟩
    rw [listAt_append]
    refine ⟨hA, ?_⟩
    have hshift : addr + 1 + 1 + A.length = addr + 2 + A.length := by omega
    rw [hshift, listAt_cons]
    refine ⟨h2, ?_⟩
    have hshift2 : addr + 2 + A.length + 1 = addr + 3 + A.length := by omega
    rwa [hshift2]
  · intro h
    rw [listAt_cons] at h
    rcases h with ⟨h0, h⟩
    rw [listAt_cons] at h
    rcases h with ⟨h1, h⟩
    rw [listAt_append] at h
    rcases h with ⟨hA, h⟩
    have hshift : addr + 1 + 1 + A.length = addr + 2 + A.length := by omega
    rw [hshift, listAt_cons] at h
    rcases h with ⟨h2, hB⟩
    have hshift2 : addr + 2 + A.length + 1 = addr + 3 + A.length := by omega
    rw [hshift2] at hB
    exact ⟨h0, h1, hA, h2, hB⟩

lemma readMultiPairsAux_of_listAt {mem : ℕ → ℕ} :
    ∀ (pairs : List (List ℕ × List ℕ)) (off : ℕ),
      ListAt mem off (pairs.flatMap encodePair) →
      readMultiPairsAux mem pairs.length off = pairs.map fun p => (p.1.toFinset, p.2.toFinset)
  | [], _, _ => rfl
  | (A, B) :: rest, off, h => by
    simp only [List.flatMap_cons, List.length_cons, List.map_cons] at h ⊢
    rw [listAt_append] at h
    rcases h with ⟨hpair, hrest⟩
    unfold encodePair at hpair
    rw [List.cons_append, listAt_cons] at hpair
    rcases hpair with ⟨hlenA, hpair⟩
    rw [listAt_append] at hpair
    rcases hpair with ⟨hA, hpair⟩
    rw [listAt_cons] at hpair
    rcases hpair with ⟨hlenB, hB⟩
    unfold readMultiPairsAux
    dsimp only
    rw [hlenA, hlenB, readList_eq_of_listAt hA]
    have hB' : ListAt mem (off + 2 + A.length) B := by
      have : off + 1 + A.length + 1 = off + 2 + A.length := by omega
      rwa [← this]
    rw [readList_eq_of_listAt hB']
    congr 1
    have hoff : off + (encodePair (A, B)).length = off + 2 + A.length + B.length := by
      rw [encodePair_length]; dsimp only; omega
    rw [hoff] at hrest
    exact readMultiPairsAux_of_listAt rest (off + 2 + A.length + B.length) hrest

lemma readMultiPairs_eq_of_multiPairsAt {mem : ℕ → ℕ} {addr : ℕ}
    {pairs : List (List ℕ × List ℕ)} (h : MultiPairsAt mem addr pairs) :
    readMultiPairs mem addr = pairs.map fun p => (p.1.toFinset, p.2.toFinset) := by
  unfold MultiPairsAt encodePairs at h
  rw [listAt_cons] at h
  unfold readMultiPairs
  rw [h.1]
  exact readMultiPairsAux_of_listAt pairs (addr + 1) h.2

/-- Any router procedure meeting `multiPairRouterContract C_rt C_sp w` immediately meets the
single-pair `routeOrCutContract C_rt C_sp w` (`OuterProgContracts.lean`). -/
theorem multiPairRouterContract_implies_routeOrCutContract {w f C_rt C_sp : ℕ} {p : Program}
    (h : MeetsContract w p f (multiPairRouterContract C_rt C_sp w)) :
    MeetsContract w p f (routeOrCutContract C_rt C_sp w) := by
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr, G, X_list, A_list, B_list,
    rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hsp, hAnd, hBnd, hvtp,
    hzf, hg_h, hx_h, hp_h, ho_h, hdg, hdx, hdp, hsp_w, h16, hGm, hz⟩
  have hmp : MultiPairsAt mem pairsAddr [(A_list, B_list)] :=
    singlePairAt_iff_multiPairsAt.mp hsp
  have hlen_p : (encodePairs [(A_list, B_list)]).length = 3 + A_list.length + B_list.length :=
    encodePairs_singleton_length A_list B_list
  have hpre_m : (multiPairRouterContract C_rt C_sp w).pre
      [gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr] mem :=
    ⟨gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h_ptr, G, X_list, [(A_list, B_list)],
      rfl, hGA, hGval, hX_at, hX_nd, hX_sub, hGloop, hΔ, hdeg, hL, hXL, hb, hmp,
      by simp [hAnd, hBnd], by simpa using hvtp, hzf, hg_h, hx_h, by omega, ho_h,
      hdg, hdx, by rcases hdp with h1 | h1 <;> [left; right] <;> omega, by simpa using hsp_w, h16,
      hGm, hz⟩
  obtain ⟨body, hbody, o, st', c, hrun, hpost, hcost⟩ := h _ mem pos ω hwords hpre_m
  have hread_eq : readMultiPairs mem pairsAddr = [readSinglePair mem pairsAddr] := by
    rw [readMultiPairs_eq_of_multiPairsAt hmp, readSinglePair_eq_of_singlePairAt hsp]
    rfl
  refine ⟨body, hbody, o, st', c, hrun, ?_, ?_⟩
  · dsimp only [routeOrCutContract, outerRouterContract]
    dsimp only [multiPairRouterContract] at hpost
    simpa only [List.getD_cons_zero, List.getD_cons_succ, hread_eq] using hpost
  · dsimp only [routeOrCutContract, outerRouterContract]
    dsimp only [multiPairRouterContract] at hcost
    simpa only [List.getD_cons_zero, List.getD_cons_succ, hread_eq] using hcost

/-! ## 4. Non-Vacuity Witnesses -/

/-- Non-vacuity witness for `multiPairRouterContract`. -/
theorem multiPairRouterContract_pre_example (C_rt : ℕ) :
    (multiPairRouterContract C_rt 1 20).pre
      [0, 2, 3, 1, 1, 2, 0, 10, 20] (fun _ => 0) := by
  refine ⟨0, 2, 3, 1, 1, 2, 0, 10, 20, Graph.mk 0 [], [], [], rfl,
    ?_, ?_, ?_, List.nodup_nil, by simp, by simp [Graph.inside], le_rfl, by simp,
    le_rfl, by norm_num, by decide, ?_, by simp, ?_, fun _ _ => rfl,
    by simp [Graph.m], by simp, by simp [encodePairs], by simp,
    Or.inr (by simp [Graph.m]), Or.inr (by simp), Or.inr (by simp [encodePairs]), ?_, by decide,
    by simp [Graph.m], by simp⟩
  · intro i hi; rcases i with _ | _ | i <;> simp [Graph.encode, Graph.m] at hi ⊢
  · intro e he; simp at he
  · exact ⟨rfl, fun i hi => by simp at hi⟩
  · intro i hi; rcases i with _ | i <;> simp [encodePairs] at hi ⊢
  · exact ⟨by simp, by simp⟩
  · simp only [List.map_nil, routerCallCost_nil, outerRouterSpace]
    norm_num

/-- Non-vacuity witness for `stepCContract` (with `k = 0`, `vs = []`, `b = 1`). -/
theorem stepCContract_pre_example (cfg : CoreParams) (cloud : ℕ → Graph)
    (hΔ : 1 ≤ cfg.Δ) (hL : 1 ≤ cfg.L) (C_stepC : ℕ) :
    (stepCContract cfg cloud C_stepC 1 20).pre
      [0, 2, 1, 0, 0, cfg.Δ, cfg.L, 0, 3, 3, 3, 20] (fun _ => 0) := by
  refine ⟨0, 2, 1, 0, 0, 0, 3, 3, 3, 20, Graph.mk 0 [], [], rfl,
    ?_, ?_, ?_, List.Pairwise.nil, by simp, by simp [Graph.inside], hΔ, by simp, hL,
    by simp, by decide, by simp [numFullBlocks],
    fun h2 => by omega, fun _ _ => rfl, fun _ _ => rfl, ?_, by simp [Graph.m], by simp⟩
  · intro i hi; rcases i with _ | _ | i <;> simp [Graph.encode, Graph.m] at hi ⊢
  · intro e he; simp at he
  · exact ⟨rfl, fun i hi => by simp at hi⟩
  · refine ⟨by simp [Graph.m], by simp, by simp, by simp, by simp [stepCOutSize],
      Or.inr (by simp [Graph.m]), Or.inr (by simp), Or.inl (by simp), Or.inl (by simp),
      Or.inr (by simp [Graph.m]), Or.inr (by simp), Or.inr (by simp), ?_, by decide⟩
    simp only [stepCMacroCost, stepCSpace]
    norm_num

/-- Non-vacuity witness for `stepCLeftoverContract` (with `vs = []`, `b = 1`). -/
theorem stepCLeftoverContract_pre_example (cfg : CoreParams)
    (hΔ : 1 ≤ cfg.Δ) (hL : 1 ≤ cfg.L) (C_left : ℕ) :
    (stepCLeftoverContract cfg C_left 1 20).pre
      [0, 2, 1, 0, cfg.Δ, cfg.L, 3, 3, 20] (fun _ => 0) := by
  refine ⟨0, 2, 1, 0, 3, 3, 20, Graph.mk 0 [], [], rfl,
    ?_, ?_, ?_, List.Pairwise.nil, by simp, by simp [Graph.inside], hΔ, by simp, hL,
    by simp, by decide, by simp, fun _ _ => rfl, fun _ _ => rfl,
    by simp [Graph.m], by simp, by simp, by simp,
    Or.inr (by simp [Graph.m]), Or.inr (by simp), Or.inl (by simp),
    Or.inr (by simp [Graph.m]), Or.inr (by simp), ?_, by decide, by simp [Graph.m], by simp⟩
  · intro i hi; rcases i with _ | _ | i <;> simp [Graph.encode, Graph.m] at hi ⊢
  · intro e he; simp at he
  · exact ⟨rfl, fun i hi => by simp at hi⟩
  · simp only [stepCLeftoverCost, leftoverVerts, leftoverList, List.drop_nil, List.toFinset_nil,
      Finset.not_nonempty_empty, ↓reduceIte, stepCLeftoverSpace]
    norm_num

end MinCostFlow.ExpanderDecomp
