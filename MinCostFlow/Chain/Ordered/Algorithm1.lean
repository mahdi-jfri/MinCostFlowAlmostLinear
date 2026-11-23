module

public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.Chain.SparseCoreOrdSpec
public import MinCostFlow.Chain.Ordered.SpecOn
public import MinCostFlow.Chain.Ordered.Compact

/-!
# Algorithm 1 with orders of ends

This file defines Algorithm 1 (`jtree.tex`, pages 20–21) as in `Chain/Algorithm1.lean`, but with
the orders of ends that the repaired Lemma 5.17 needs. Every level passes to its tool the order of
the ends of its current graph: `initOrd` at an initialization and `updateOrd` after a batch. Level
`0` gets its ends sorted by edge name, tail before head (`Bundle.sortedEnds`). Level `i + 1` gets
the tours of the branch forest of level `i`, restricted to its ends, which the tool returns as
`rot`. So the order of a level is a function of the state, `chainLevelOrd`, and the chain state
`ChainState` does not change. A restart keeps the order the tool stores.

The procedures, the per-level history `LevelHistory` and the invariant `ChainInv` keep the names
of `Chain/Algorithm1.lean` in the namespace `MinCostFlow.Chain.Ordered`. The history adds the
sequence of orders `ord` of the level's input, ordered with split bound `2`, and its run is the run
with orders. It also records that the tool meets its specification on every history with the level's
start (`hOK`). The chain gets this fact for a fresh level from `ChainToolSupply`, a property of the
tool on the inputs whose lengths lie in the range `LevelLenRange`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section Algorithm1Defs

/-- The order of the ends of `G i` passed to the tool of level `i`:
the ends sorted by edge name at level `0`, and the order `rot` that the tool of level `i - 1`
returns for its active branch at level `i ≥ 1`. -/
def chainLevelOrd (T : SparseCoreRestartTool) (G : ℕ → MGraph) (sc : ℕ → T.State)
    (bran : ℕ → ℕ) (i : ℕ) : ℕ → List End :=
  if i = 0 then sortedEnds (G 0) else T.rot (sc (i - 1)) (bran (i - 1))

/-- The order of the ends of `st.G i` (`chainLevelOrd` of the state). -/
def _root_.MinCostFlow.Chain.ChainState.levelOrd {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) (i : ℕ) : ℕ → List End :=
  chainLevelOrd T st.G st.scState st.bran i

/-- Recursive suffix builder: given `G, scState, bran, …` already fixed up to `idx`, initializes
levels `idx, idx + 1, …, P.d - 1` and returns the updated state arrays plus level-`d` LSF/MWU. -/
noncomputable def rebuildSuffix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    (rem idx : ℕ) →
      (ℕ → MGraph) → (ℕ → T.State) → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) →
      (ℕ → MGraph) × (ℕ → T.State) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) ×
        (ℕ × (ℕ → LSF)) × ℕ
  | 0, idx, G, sc, bran, upd, cEnc, cDec, cFwd =>
    let Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let ℓd := Cpartial.chainLen ℓ₀ idx
    (G, sc, bran, upd, cEnc, cDec, cFwd, L.build (G idx) ℓd, L.cost (G idx))
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd =>
    let Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let ℓi := Cpartial.chainLen ℓ₀ idx
    let gi := Cpartial.chainGrad g₀ idx
    let Gi := G idx
    let sc_i := T.initOrd P.k (lvlM idx) N₀ Gi ℓi gi (chainLevelOrd T G sc bran idx)
    let Gi1 := T.S sc_i 0
    let G' := fun j => if j = idx + 1 then Gi1 else G j
    let sc' := fun j => if j = idx then sc_i else sc j
    let bran' := fun j => if j = idx then 0 else bran j
    let upd' := fun j => if j = idx then 0 else upd j
    let cEnc' := fun j => if j = idx then 0 else cEnc j
    let cDec' := fun j => if j = idx then 0 else cDec j
    let cFwd' := fun j => if j = idx then 0 else cFwd j
    rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) G' sc' bran' upd' cEnc' cDec' cFwd'

/-- **Algorithm 1 `Initialize(G^{(0)}, ℓ, g)`** (`jtree.tex`, page 20): initializes `G_0 ← G^{(0)}`,
`passes_i ← 0`, builds all levels `0, …, d` via `rebuildSuffix`, and emits initial `T^𝒢` edge
insertions. -/
noncomputable def algorithm1_initialize (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    ChainState T P × List TreeChange :=
  let dummySc := T.initOrd P.k (lvlM 0) N₀ G₀ ℓ₀ g₀ (Bundle.sortedEnds G₀)
  let (G', sc', bran', upd', cEnc', cDec', cFwd', lastRes, lastCost) :=
    rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ P.d 0
      (fun _ => G₀) (fun _ => dummySc) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => 0)
  let st : ChainState T P :=
    { G := G'
      scState := sc'
      curRestarts := fun _ => 0
      bran := bran'
      updCount := upd'
      recUpdates := fun _ => 0
      curFwd := cFwd'
      lastK := lastRes.1
      lastLSFs := lastRes.2
      lastBran := 0
      ℓ := ℓ₀
      g := g₀
      passes := fun _ => 0
      shiftCount := fun _ => 0
      rebuildCount := fun _ => 0
      closedRuntime := 0
      curLastRebuilds := 0
      curLastCost := lastCost
      curEnc := cEnc'
      closedTreeUpdates := 0
      curDecUpdates := cDec'
      curLastTreeUpdates := 0
      lvlM := lvlM
      N₀ := N₀ }
  let changes := diffTreeChanges ∅ st.toTreeChain.chainTree.E
  let st' := { st with closedTreeUpdates := changes.length }
  (st', changes)

/-- **Algorithm 1 `Rebuild(i_0)`** (`jtree.tex`, page 20): re-initializes levels `i_0, …, d - 1`
(and level `d`) starting from `Gnew` at level `i_0`, retiring active costs of levels `≥ i_0` and
emitting the `TreeChange`s on `T^𝒢`. Note: when called directly with `i_0 < P.d`, uses `Gnew` as
`G_{i_0}`; when `i_0 = P.d`, rebuilds level `d`. -/
noncomputable def algorithm1_rebuild (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph)
    (extraEnc : ℕ := 0) : ChainState T P × List TreeChange :=
  if _hi : i₀ < P.d then
    let G0 := fun j => if j = i₀ then Gnew else st.G j
    let (G', sc', bran', upd', cEnc', cDec', cFwd', lastRes, lastCost) :=
      rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
        G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
    let retiredTool := (Finset.Ico i₀ P.d).sum fun j => T.cost (st.scState j) + st.curEnc j
    let retiredDec := (Finset.Ico i₀ P.d).sum fun j => st.curDecUpdates j
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        G := G'
        scState := sc'
        curRestarts := fun j => if i₀ ≤ j ∧ j < P.d then 0 else st.curRestarts j
        bran := bran'
        updCount := upd'
        curFwd := cFwd'
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        rebuildCount := fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j
        closedRuntime := st.closedRuntime + retiredTool + st.curLastCost + extraEnc
        curLastRebuilds := 0
        curLastCost := lastCost
        curEnc := cEnc'
        closedTreeUpdates := st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates
        curDecUpdates := cDec'
        curLastTreeUpdates := 0 }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)
  else
    -- `i₀ = P.d`: rebuild level `d` only
    let ℓd := st.toTreeChain.chainLen st.ℓ P.d
    let lastRes := L.build Gnew ℓd
    let lastCost := L.cost Gnew
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        G := fun j => if j = P.d then Gnew else st.G j
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        rebuildCount := fun j => if j = P.d then st.rebuildCount P.d + 1 else st.rebuildCount j
        closedRuntime := st.closedRuntime + st.curLastCost + extraEnc
        curLastRebuilds := 0
        curLastCost := lastCost
        closedTreeUpdates := st.closedTreeUpdates + st.curLastTreeUpdates
        curLastTreeUpdates := 0 }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)

/-- **Algorithm 1 `Shift(i_0)`** (`jtree.tex`, page 20): increments `bran_{i_0} ← (bran_{i_0} + 1) % k`,
restarts level `i_0`'s core tool on `newBran` via `T.restart`,
sets `G_{i_0+1} ← 𝒮(G_{i_0}, F^{G_{i_0}}_{bran_{i_0}})`, and re-initializes levels `i_0 + 1, …, d`.
For `i_0 = P.d`, advances `lastBran`. -/
noncomputable def algorithm1_shift (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) : ChainState T P × List TreeChange :=
  if _hi : i₀ < P.d then
    let newBran := (st.bran i₀ + 1) % P.k
    let sc_i0 := T.restart (st.scState i₀) newBran
    let Gnext := T.S sc_i0 newBran
    let G0 := fun j => if j = i₀ + 1 then Gnext else st.G j
    let sc0 := fun j => if j = i₀ then sc_i0 else st.scState j
    let bran0 := fun j => if j = i₀ then newBran else st.bran j
    let cDec0 := fun j => if j = i₀ then 0 else st.curDecUpdates j
    let cEnc0 := fun j => if j = i₀ + 1 then 0 else st.curEnc j
    let (G', sc', bran', upd', cEnc', cDec', cFwd', lastRes, lastCost) :=
      rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
        G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd
    let retiredTool := (Finset.Ico (i₀ + 1) P.d).sum fun j => T.cost (st.scState j) + st.curEnc j
    let retiredDec := (Finset.Ico i₀ P.d).sum fun j => st.curDecUpdates j
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        G := G'
        scState := sc'
        curRestarts := fun j =>
          if j = i₀ then st.curRestarts i₀ + 1
          else if i₀ + 1 ≤ j ∧ j < P.d then 0
          else st.curRestarts j
        bran := bran'
        updCount := upd'
        curFwd := cFwd'
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        shiftCount := fun j => if j = i₀ then st.shiftCount i₀ + 1 else st.shiftCount j
        closedRuntime := st.closedRuntime + retiredTool + st.curLastCost
        curLastRebuilds := 0
        curLastCost := lastCost
        curEnc := cEnc'
        closedTreeUpdates := st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates
        curDecUpdates := cDec'
        curLastTreeUpdates := 0 }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)
  else
    let newLastBran := (st.lastBran + 1) % st.lastK
    let oldE := st.toTreeChain.chainTree.E
    let stMid : ChainState T P :=
      { st with
        lastBran := newLastBran
        shiftCount := fun j => if j = P.d then st.shiftCount P.d + 1 else st.shiftCount j }
    let changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    let stFinal := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    (stFinal, changes)

/-- Recursive level-by-level update loop for **Algorithm 1 `Update(U^{(t)}, g^{(t)}, ℓ^{(t)})`**.
At level `idx`: if `intRebuildThreshold P N₀ idx < updCount idx + curU.length`,
calls `algorithm1_rebuild` from `idx` and stops; otherwise invokes `T.update`, forwards the
active branch batch `U_{S, bran idx}`, and proceeds to `idx + 1`. A rebuild of level `0` starts
every level from scratch, so it first renames the edges of the new level-`0` graph to
`0, …, |E| - 1` in increasing order (`rebuildStartGraph`, `rebuildStartFn`). The paper's Rebuild
works on edges, not on names (page 20), so this is the paper's step. -/
noncomputable def updateLoop (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    (rem idx : ℕ) → (st : ChainState T P) → (curG : MGraph) → (curU : List Update) → (curEncAcc : ℕ) →
      ChainState T P × List TreeChange
  | 0, _, st, curG, curU, _ =>
    if curU = [] then
      let st' := { st with G := fun j => if j = P.d then curG else st.G j, ℓ := ℓ', g := g' }
      (st', [])
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }
      let ℓd := Cpartial.chainLen ℓ' P.d
      let lastRes := L.build curG ℓd
      let lastCost := L.cost curG
      let oldFdE := (st.lastLSFs st.lastBran).F.F.E
      let newFdE := (lastRes.2 0).F.F.E
      let fdChanges := diffTreeChanges oldFdE newFdE
      let st' : ChainState T P :=
        { st with
          G := fun j => if j = P.d then curG else st.G j
          lastK := lastRes.1
          lastLSFs := lastRes.2
          lastBran := 0
          ℓ := ℓ'
          g := g'
          curLastRebuilds := st.curLastRebuilds + 1
          curLastCost := st.curLastCost + lastCost
          curLastTreeUpdates := st.curLastTreeUpdates + fdChanges.length }
      (st', fdChanges)
  | rem + 1, idx, st, curG, curU, curEncStep =>
    if intRebuildThreshold P N₀ idx < st.updCount idx + curU.length then
      let stWithLG :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      algorithm1_rebuild T L P stWithLG idx (rebuildStartGraph idx curG) curEncStep
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let (sc', U_S) := T.updateOrd (st.scState idx) curU ℓi gi
        (chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)
      let oldFiE := (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
      let newFiE := (T.lsfs sc' (st.bran idx)).F.F.E
      let fiChanges := diffTreeChanges oldFiE newFiE
      let nextG := T.S sc' (st.bran idx)
      let nextU := U_S (st.bran idx)
      let nextEnc := (st.G (idx + 1)).batchEnc nextU
      let stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncStep
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      let (stEnd, restChanges) := updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) stNext nextG nextU 0
      (stEnd, fiChanges ++ restChanges)

/-- **Algorithm 1 `Update(U^{(t)}, g^{(t)}, ℓ^{(t)})`** (`jtree.tex`, page 21): applies `U^{(t)}`
to `G_0`, propagates updates through levels `0, …, d - 1` (rebuilding whenever a level would exceed
`M_i / (k log² N₀)`), updates level `d` if `U^{(t)}_{G_d}` is nonempty, and returns the updated state
and exact `TreeChange` list for `T^𝒢`. -/
noncomputable def algorithm1_update (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) :
    ChainState T P × List TreeChange :=
  let oldE := st.toTreeChain.chainTree.E
  let G₀' := (st.G 0).applyBatch U
  let enc₀ := (st.G 0).batchEnc U
  let st0 : ChainState T P :=
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
  let (st', _) := updateLoop T L TP P N₀ ℓ' g' P.d 0 st0 G₀' U enc₀
  (st', diffTreeChanges oldE st'.toTreeChain.chainTree.E)

end Algorithm1Defs

section Invariants

/-- The lengths `ℓ` of the edges of a graph `G` at level `i` lie in `[e^{-Λ}, e^Λ σ^i]`, with
`σ = max 2 (TP.σ P.k N₀)` the stretch bound of a level. A level stretches the lengths of the edges
it keeps by a factor in `[1, σ]`, so lengths in `[e^{-Λ}, e^Λ]` at level `0` give this range at
level `i`. -/
def LevelLenRange (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (Λ : ℝ) (i : ℕ)
    (G : MGraph) (ℓ : ℕ → ℝ) : Prop :=
  ∀ e ∈ G.E, Real.exp (-Λ) ≤ ℓ e ∧ ℓ e ≤ Real.exp Λ * max 2 (TP.σ P.k N₀) ^ i

/-- The tool meets its specification at every level `i < P.d` on every history that starts at a
valid graph with at most `N₀` vertices and lengths in the range `LevelLenRange` of level `i`. -/
def ChainToolSupply (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (N₀ : ℕ) (Λ : ℝ) : Prop :=
  ∀ i < P.d, ∀ (G : MGraph) (ℓ : ℕ → ℝ), G.IsValid → G.n ≤ N₀ →
    LevelLenRange TP P N₀ Λ i G ℓ → T.ToolOKAt TP P.k (levelM TP P i) N₀ G ℓ

/-- A tool that meets the unrestricted specification `IsSpecOrdRestart` meets it on every start,
so it gives `ChainToolSupply` for every `Λ`. -/
lemma chainToolSupply_of_isSpecOrdRestart {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    (hT : T.IsSpecOrdRestart TP) (P : ChainParams) (N₀ : ℕ) (Λ : ℝ) :
    ChainToolSupply T TP P N₀ Λ :=
  fun _ _ _ _ _ _ _ => hT.toOn _

/-- The lengths `ℓ` of the edges of `G` lie in `[e^{-Λ}, e^Λ]`. -/
def LenInRange (Λ : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) : Prop :=
  ∀ e ∈ G.E, Real.exp (-Λ) ≤ ℓ e ∧ ℓ e ≤ Real.exp Λ

lemma LenInRange.pos {Λ : ℝ} {G : MGraph} {ℓ : ℕ → ℝ} (h : LenInRange Λ G ℓ) :
    ∀ e ∈ G.E, 0 < ℓ e :=
  fun e he => lt_of_lt_of_le (Real.exp_pos _) (h e he).1

lemma LenInRange.toLevel {Λ : ℝ} {G : MGraph} {ℓ : ℕ → ℝ} (h : LenInRange Λ G ℓ)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) : LevelLenRange TP P N₀ Λ 0 G ℓ :=
  fun e he => ⟨(h e he).1, by rw [pow_zero, mul_one]; exact (h e he).2⟩

/-- Renaming the edges by `MGraph.compact` keeps the lengths in `[e^{-Λ}, e^Λ]`. -/
lemma LenInRange.compact {Λ : ℝ} {G : MGraph} {ℓ : ℕ → ℝ} (h : LenInRange Λ G ℓ) :
    LenInRange Λ G.compact (fun j => ℓ (compactUnrank G.E j)) :=
  fun _ hj => h _ (compactUnrank_mem_of_mem_compact hj)

lemma LevelLenRange.pos {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ} {Λ : ℝ} {i : ℕ}
    {G : MGraph} {ℓ : ℕ → ℝ} (h : LevelLenRange TP P N₀ Λ i G ℓ) : ∀ e ∈ G.E, 0 < ℓ e :=
  fun e he => lt_of_lt_of_le (Real.exp_pos _) (h e he).1

/-- A stretch `w ∈ [1, σ]` maps a length in the range of level `i` to a length in the range of
level `i + 1`. -/
lemma LevelLenRange.stretch_step {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ} {Λ : ℝ}
    {i : ℕ} {G : MGraph} {ℓ : ℕ → ℝ} (h : LevelLenRange TP P N₀ Λ i G ℓ) {e : ℕ} (he : e ∈ G.E)
    {w : ℝ} (hw1 : 1 ≤ w) (hwσ : w ≤ max 2 (TP.σ P.k N₀)) :
    Real.exp (-Λ) ≤ w * ℓ e ∧ w * ℓ e ≤ Real.exp Λ * max 2 (TP.σ P.k N₀) ^ (i + 1) := by
  have hR := h e he
  have h0 : 0 ≤ ℓ e := le_trans (Real.exp_pos _).le hR.1
  have hσ0 : 0 ≤ max 2 (TP.σ P.k N₀) := le_trans zero_le_two (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · calc Real.exp (-Λ) ≤ ℓ e := hR.1
      _ = 1 * ℓ e := (one_mul _).symm
      _ ≤ w * ℓ e := mul_le_mul_of_nonneg_right hw1 h0
  · calc w * ℓ e ≤ max 2 (TP.σ P.k N₀) * (Real.exp Λ * max 2 (TP.σ P.k N₀) ^ i) :=
          mul_le_mul hwσ hR.2 h0 hσ0
      _ = Real.exp Λ * max 2 (TP.σ P.k N₀) ^ (i + 1) := by rw [pow_succ]; ring

/-- Per-level history witness linking `st.scState i` to a valid `SparseCoreRestartTool` run with
orders and restarts over a dynamic graph history of length `len_i` bounded by
`(levelM TP P i, N₀)`. The input orders `ord` are ordered with split bound `2`, and the last one is
the order the chain passes to level `i`. -/
structure LevelHistory (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (N₀ : ℕ) (st : ChainState T P) (i : ℕ) where
  D : DynamicInstance
  len : ℕ
  s₀ : ℕ
  hs₀ : s₀ ≤ len
  restarts : ℕ → List ℕ
  hRestartsLt : ∀ r ≤ len, ∀ j ∈ restarts r, j < P.k
  hRestartsCount : (Finset.range (len + 1)).sum (fun r => (restarts r).length) = st.curRestarts i
  hS0Fresh : s₀ = 0 ∨ st.bran i ∈ restarts s₀
  hNoRestartAfterS0 : ∀ r, s₀ < r → r ≤ len → st.bran i ∉ restarts r
  hG0 : (D.G 0).IsValid
  hD : D.IsValid len
  hLen : LengthsStable D len
  hℓPos : ∀ s ≤ len, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e
  hEndG : D.G len = st.G i
  hEndℓ : ∀ e ∈ (st.G i).E, D.ℓ len e = st.toTreeChain.chainLen st.ℓ i e
  hEndg : D.g len = st.toTreeChain.chainGrad st.g i
  hUpd : (Finset.Icc 1 len).sum (fun s => (D.U s).length) = st.updCount i
  hThresh : ((st.updCount i : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P i) N₀
  hInitMBound : (D.G 0).m ≤ levelM TP P i
  hInitNBound : (D.G 0).n ≤ N₀
  ord : ℕ → ℕ → List End
  hOrd : OrderedUpTo D len 2 ord
  hEndOrd : ord len = st.levelOrd i
  hRun : st.scState i = T.runOrdAfterRestarts P.k (levelM TP P i) N₀ D ord restarts len
  hOK : T.ToolOKAt TP P.k (levelM TP P i) N₀ (D.G 0) (D.ℓ 0)
  branchSeq : ℕ → ℕ
  hBranch : ∀ s, branchSeq s < P.k
  hBranchTail : ∀ s, s₀ < s → s ≤ len → branchSeq s = st.bran i
  hWinFwdBound :
    (((Finset.Icc 1 s₀).sum fun s =>
      ((T.runOrdAfterUpdate P.k (levelM TP P i) N₀ D ord restarts s).2
        (branchSeq s)).length : ℕ) : ℝ) ≤
      TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc 1 s₀).sum fun s => (D.U s).length : ℕ) : ℝ)
  hCurFwdEq : st.curFwd i =
    (Finset.Icc 1 len).sum fun s =>
      ((T.runOrdAfterUpdate P.k (levelM TP P i) N₀ D ord restarts s).2 (branchSeq s)).length
  hDecEq : st.curDecUpdates i + (T.lsfs (st.scState i) (st.bran i)).F.F.E.card =
    (T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P i) N₀ D ord restarts s₀) (st.bran i)).F.F.E.card
  hEnc0Le : i = 0 →
    st.curEnc 0 ≤ (Finset.Icc 1 len).sum fun s => (D.G (s - 1)).batchEnc (D.U s)
  hEncLe : i + 1 < P.d →
    st.curEnc (i + 1) ≤
      (Finset.Icc (s₀ + 1) len).sum fun s =>
        (T.S (T.runOrdAfterRestarts P.k (levelM TP P i) N₀ D ord restarts (s - 1))
          (st.bran i)).batchEnc
          ((T.runOrdAfterUpdate P.k (levelM TP P i) N₀ D ord restarts s).2 (st.bran i))

/-- Master invariant maintained by Algorithm 1 with orders across `Initialize`, `Rebuild`,
`Shift`, and `Update`: the invariant of `Chain/Algorithm1.lean` with the ordered level
histories. -/
structure ChainInv (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P) : Prop where
  hG0Valid : (st.G 0).IsValid
  hG0m : (st.G 0).m ≤ P.M₀
  hG0n : (st.G 0).n ≤ N₀
  hℓPos : ∀ e ∈ (st.G 0).E, 0 < st.ℓ e
  hLastK : 0 < st.lastK
  hLastBran : st.lastBran < st.lastK
  hLastHolds : ∀ j < st.lastK, (st.lastLSFs j).Holds (st.G P.d) (st.toTreeChain.chainLen st.ℓ P.d)
    (LP.σ_last (st.G P.d).n)
  hLastMWU : ∀ e ∈ (st.G P.d).E,
    (∑ j ∈ Finset.range st.lastK, (st.lastLSFs j).wstr e) / (st.lastK : ℝ) ≤
      LP.σ_mwu (st.G P.d).n
  hLastSpans : ∀ j < st.lastK, ∀ u ∈ (st.G P.d).V, ∀ v ∈ (st.G P.d).V,
    (st.G P.d).Connected u v → (st.lastLSFs j).F.F.Connected u v
  hBran : ∀ i < P.d, st.bran i < P.k
  hGSucc : ∀ i < P.d, st.G (i + 1) = T.S (st.scState i) (st.bran i)
  hHist : ∀ i < P.d, Nonempty (LevelHistory T TP P N₀ st i)
  hRecRebuild : ∀ i < P.d,
    (st.rebuildCount i : ℝ) * ((intRebuildThreshold P N₀ i : ℝ) + 1) +
      (st.updCount i : ℝ) ≤ (st.recUpdates i : ℝ)
  hRecFwd : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) st
  hEnc0 : (st.curEnc 0 : ℝ) ≤
    20 * ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ)) *
      Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2)
  hLastCap : 0 < P.d →
    (∃ H : LevelHistory T TP P N₀ st (P.d - 1),
      st.curLastRebuilds ≤
        (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
          ((T.runOrdAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.ord H.restarts s).2
            (st.bran (P.d - 1))).length) ∧
    (st.curLastCost : ℝ) ≤
      ((st.curLastRebuilds + 1 : ℕ) : ℝ) *
        (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2)) ^
            LP.p_last) ∧
    (st.curLastTreeUpdates : ℝ) ≤
      2 * (st.curLastRebuilds : ℝ) * (levelM TP P P.d : ℝ)
  hLvlM : st.lvlM = levelM TP P
  hN0 : st.N₀ = N₀

end Invariants

end MinCostFlow.Chain.Ordered
