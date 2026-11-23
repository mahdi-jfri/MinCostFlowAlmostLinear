module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.ExpanderDecomp.RouteProgLayout
public import MinCostFlow.ExpanderDecomp.RouteBFS

import Mathlib.Tactic.Linarith

/-!
# Layered BFS Program: Layout, Statements, Contract, and Helper Stages

Defines the memory configuration (`BfsCfg`, `BfsCfgAt`), output layout (`BfsOutAt`),
disjointness/frame predicates (`DisjRange`, `BfsWriteSet`, `BfsDisj`), deterministic Word-RAM
statements (`bfsInitStmt`, `bfsScanInnerStmt`, `bfsExpandStmt`, `bfsRevCopyStmt`,
`bfsLayersProc`), contract `bfsLayersContract`, pure prefix/append lemmas for `bfsScanAdj` and
`bfsExpandFrontier`, and verifies `bfsInit_triple` and `bfsRevCopy_triple`. The frontier scan,
main loop, and `bfsLayers_meetsContract` proof live in `RouteProgBFS.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Configuration, Output Layout, and Disjointness -/

/-- Two half-open memory intervals `[a, a + la)` and `[b, b + lb)` are disjoint. -/
def DisjRange (a la b lb : ℕ) : Prop :=
  a + la ≤ b ∨ b + lb ≤ a

/-- Configuration words stored at `cfgAddr + 0 .. cfgAddr + 15` for `bfsLayersProc`. -/
structure BfsCfg where
  offAddr : ℕ
  nbAddr : ℕ
  maskArrAddr : ℕ
  maskBadVal : ℕ
  hasStop : ℕ
  stopArrAddr : ℕ
  stopVal : ℕ
  visStampAddr : ℕ
  distAddr : ℕ
  layerOffAddr : ℕ
  layerDataAddr : ℕ
  tmpNxtAddr : ℕ
  bfsGen : ℕ
  maxDist : ℕ
  initPtr : ℕ
  initLen : ℕ

/-- `cfg` is stored at `cfgAddr + 0 .. cfgAddr + 15`. -/
def BfsCfgAt (mem : ℕ → ℕ) (cfgAddr : ℕ) (cfg : BfsCfg) : Prop :=
  mem (cfgAddr + 0) = cfg.offAddr ∧
  mem (cfgAddr + 1) = cfg.nbAddr ∧
  mem (cfgAddr + 2) = cfg.maskArrAddr ∧
  mem (cfgAddr + 3) = cfg.maskBadVal ∧
  mem (cfgAddr + 4) = cfg.hasStop ∧
  mem (cfgAddr + 5) = cfg.stopArrAddr ∧
  mem (cfgAddr + 6) = cfg.stopVal ∧
  mem (cfgAddr + 7) = cfg.visStampAddr ∧
  mem (cfgAddr + 8) = cfg.distAddr ∧
  mem (cfgAddr + 9) = cfg.layerOffAddr ∧
  mem (cfgAddr + 10) = cfg.layerDataAddr ∧
  mem (cfgAddr + 11) = cfg.tmpNxtAddr ∧
  mem (cfgAddr + 12) = cfg.bfsGen ∧
  mem (cfgAddr + 13) = cfg.maxDist ∧
  mem (cfgAddr + 14) = cfg.initPtr ∧
  mem (cfgAddr + 15) = cfg.initLen

/-- Set of addresses that `bfsLayersProc` may overwrite. -/
def BfsWriteSet (nX : ℕ) (cfg : BfsCfg) (cfgAddr : ℕ) (a : ℕ) : Prop :=
  (cfg.visStampAddr ≤ a ∧ a < cfg.visStampAddr + nX) ∨
  (cfg.distAddr ≤ a ∧ a < cfg.distAddr + nX) ∨
  (cfg.layerOffAddr ≤ a ∧ a < cfg.layerOffAddr + nX + 1) ∨
  (cfg.layerDataAddr ≤ a ∧ a < cfg.layerDataAddr + nX) ∨
  (cfg.tmpNxtAddr ≤ a ∧ a < cfg.tmpNxtAddr + nX) ∨
  (cfgAddr + 16 ≤ a ∧ a < cfgAddr + 21)

/-- Pairwise disjointness and word-size bounds for the BFS buffers and read-only inputs. -/
def BfsDisj (w nX m2 : ℕ) (cfg : BfsCfg) (cfgAddr : ℕ) : Prop :=
  -- Writable ranges pairwise disjoint
  DisjRange cfg.visStampAddr nX cfg.distAddr nX ∧
  DisjRange cfg.visStampAddr nX cfg.layerOffAddr (nX + 1) ∧
  DisjRange cfg.visStampAddr nX cfg.layerDataAddr nX ∧
  DisjRange cfg.visStampAddr nX cfg.tmpNxtAddr nX ∧
  DisjRange cfg.visStampAddr nX (cfgAddr + 16) 5 ∧
  DisjRange cfg.distAddr nX cfg.layerOffAddr (nX + 1) ∧
  DisjRange cfg.distAddr nX cfg.layerDataAddr nX ∧
  DisjRange cfg.distAddr nX cfg.tmpNxtAddr nX ∧
  DisjRange cfg.distAddr nX (cfgAddr + 16) 5 ∧
  DisjRange cfg.layerOffAddr (nX + 1) cfg.layerDataAddr nX ∧
  DisjRange cfg.layerOffAddr (nX + 1) cfg.tmpNxtAddr nX ∧
  DisjRange cfg.layerOffAddr (nX + 1) (cfgAddr + 16) 5 ∧
  DisjRange cfg.layerDataAddr nX cfg.tmpNxtAddr nX ∧
  DisjRange cfg.layerDataAddr nX (cfgAddr + 16) 5 ∧
  DisjRange cfg.tmpNxtAddr nX (cfgAddr + 16) 5 ∧
  -- Read-only ranges disjoint from all writable ranges
  (∀ a, cfgAddr ≤ a ∧ a < cfgAddr + 16 → ¬ BfsWriteSet nX cfg cfgAddr a) ∧
  (∀ a, cfg.offAddr ≤ a ∧ a < cfg.offAddr + nX + 1 → ¬ BfsWriteSet nX cfg cfgAddr a) ∧
  (∀ a, cfg.nbAddr ≤ a ∧ a < cfg.nbAddr + m2 → ¬ BfsWriteSet nX cfg cfgAddr a) ∧
  (∀ a, cfg.maskArrAddr ≤ a ∧ a < cfg.maskArrAddr + nX → ¬ BfsWriteSet nX cfg cfgAddr a) ∧
  (cfg.hasStop ≠ 0 →
    ∀ a, cfg.stopArrAddr ≤ a ∧ a < cfg.stopArrAddr + nX → ¬ BfsWriteSet nX cfg cfgAddr a) ∧
  (∀ a, cfg.initPtr ≤ a ∧ a < cfg.initPtr + cfg.initLen → ¬ BfsWriteSet nX cfg cfgAddr a) ∧
  -- Word-size bounds
  cfgAddr + 25 < 2 ^ w ∧
  cfg.offAddr + nX + 5 < 2 ^ w ∧
  cfg.nbAddr + m2 + 5 < 2 ^ w ∧
  cfg.maskArrAddr + nX + 5 < 2 ^ w ∧
  (cfg.hasStop ≠ 0 → cfg.stopArrAddr + nX + 5 < 2 ^ w) ∧
  cfg.visStampAddr + nX + 5 < 2 ^ w ∧
  cfg.distAddr + nX + 5 < 2 ^ w ∧
  cfg.layerOffAddr + nX + 5 < 2 ^ w ∧
  cfg.layerDataAddr + nX + 5 < 2 ^ w ∧
  cfg.tmpNxtAddr + nX + 5 < 2 ^ w ∧
  cfg.initPtr + cfg.initLen + 5 < 2 ^ w ∧
  cfg.maskBadVal < 2 ^ w ∧
  cfg.hasStop < 2 ^ w ∧
  cfg.stopVal < 2 ^ w ∧
  cfg.bfsGen < 2 ^ w ∧
  cfg.maxDist < 2 ^ w ∧
  m2 + 5 < 2 ^ w ∧
  nX + 5 < 2 ^ w ∧
  4 ≤ 2 ^ w

/-- Memory predicate for the output of `bfsLayersProc` matching `res : BFSResult`. -/
def BfsOutAt (mem : ℕ → ℕ) (X : Finset ℕ) (cfg : BfsCfg) (cfgAddr : ℕ)
    (res : BFSResult) : Prop :=
  (∀ r ≤ res.layers.length,
    mem (cfg.layerOffAddr + r) = ((res.layers.take r).map List.length).sum) ∧
  (∀ r (hr : r < res.layers.length),
    ListAt mem (cfg.layerDataAddr + ((res.layers.take r).map List.length).sum)
      ((res.layers[r]'hr).map (locOf X))) ∧
  (∀ v < X.card, mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ res.visited) ∧
  (∀ v < X.card, origOf X v ∈ res.visited →
    res.dist (origOf X v) = some (mem (cfg.distAddr + v))) ∧
  mem (cfgAddr + 16) = res.layers.length ∧
  mem (cfgAddr + 17) = res.visited.card ∧
  mem (cfgAddr + 18) = res.maxReached ∧
  mem (cfgAddr + 19) = (if res.hitStop then 1 else 0) ∧
  mem (cfgAddr + 20) = (if res.exhausted then 1 else 0)

/-- Explicit step bound for `bfsLayersProc` as a linear function of `res.cost`. -/
def bfsProgCost (modelCost : ℕ) : ℕ :=
  140 * modelCost + 180

/-! ## 2. Procedure Statements -/

/-- Store the 5 output words `(numLayers, totalVis, maxReached, hitStop, exhausted)` at
`cfgAddr + 16 .. cfgAddr + 20` and return `totalVis`. -/
def bfsWriteRetStmt (eNumL eTotV eMaxR eHit eExh : Expr) : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 0) (.const 16)) eNumL
    , .store (.bin .add (.reg 0) (.const 17)) eTotV
    , .store (.bin .add (.reg 0) (.const 18)) eMaxR
    , .store (.bin .add (.reg 0) (.const 19)) eHit
    , .store (.bin .add (.reg 0) (.const 20)) eExh
    , .ret eTotV ]

/-- Initialize layer 0 from `initPtr[0 .. initLen - 1]`, setting `visStamp`, `dist`, and `hit`. -/
def bfsInitStmt : Stmt :=
  seqStmts
    [ .assign 21 (.const 0)
    , .assign 22 (.const 0)
    , .loop (.bin .lt (.reg 22) (.reg 16))
        (seqStmts
          [ .assign 26 (.load (.bin .add (.reg 15) (.reg 22)))
          , .store (.bin .add (.reg 11) (.reg 22)) (.reg 26)
          , .store (.bin .add (.reg 8) (.reg 26)) (.reg 13)
          , .store (.bin .add (.reg 9) (.reg 26)) (.const 0)
          , .cond (.reg 5)
              (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 26))) (.reg 7))
                (.assign 21 (.const 1))
                .nop)
              .nop
          , .assign 22 (.bin .add (.reg 22) (.const 1)) ])
    , .store (.bin .add (.reg 10) (.const 1)) (.reg 16) ]

/-- Inner neighbor-scan loop for one frontier vertex `u` over CSR edges `[r24, r25)`. -/
def bfsScanInnerStmt : Stmt :=
  .loop (.bin .lt (.reg 24) (.reg 25))
    (seqStmts
      [ .assign 26 (.load (.bin .add (.reg 2) (.reg 24)))
      , .cond (.bin .eq (.load (.bin .add (.reg 3) (.reg 26))) (.reg 4))
          .nop
          (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 26))) (.reg 13))
            .nop
            (seqStmts
              [ .store (.bin .add (.reg 8) (.reg 26)) (.reg 13)
              , .store (.bin .add (.reg 9) (.reg 26)) (.bin .add (.reg 17) (.const 1))
              , .store (.bin .add (.reg 12) (.reg 20)) (.reg 26)
              , .assign 20 (.bin .add (.reg 20) (.const 1)) ]))
      , .assign 24 (.bin .add (.reg 24) (.const 1)) ])

/-- Expand frontier `layerData[layerStart .. layerEnd - 1]`, writing newly discovered vertices
into `tmpNxt[0 .. nxtLen - 1]`. -/
def bfsExpandStmt : Stmt :=
  seqStmts
    [ .assign 20 (.const 0)
    , .assign 22 (.reg 18)
    , .loop (.bin .lt (.reg 22) (.reg 19))
        (seqStmts
          [ .assign 23 (.load (.bin .add (.reg 11) (.reg 22)))
          , .assign 24 (.load (.bin .add (.reg 1) (.reg 23)))
          , .assign 25 (.load (.bin .add (.bin .add (.reg 1) (.reg 23)) (.const 1)))
          , bfsScanInnerStmt
          , .assign 22 (.bin .add (.reg 22) (.const 1)) ]) ]

/-- Copy `tmpNxt[0 .. nxtLen - 1]` in reverse into `layerData[layerEnd .. layerEnd + nxtLen - 1]`
while computing `hit` (`r21`). -/
def bfsRevCopyStmt : Stmt :=
  seqStmts
    [ .assign 21 (.const 0)
    , .assign 22 (.const 0)
    , .loop (.bin .lt (.reg 22) (.reg 20))
        (seqStmts
          [ .assign 26 (.load (.bin .add (.reg 12)
              (.bin .sub (.bin .sub (.reg 20) (.const 1)) (.reg 22))))
          , .store (.bin .add (.reg 11) (.bin .add (.reg 19) (.reg 22))) (.reg 26)
          , .cond (.reg 5)
              (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 26))) (.reg 7))
                (.assign 21 (.const 1))
                .nop)
              .nop
          , .assign 22 (.bin .add (.reg 22) (.const 1)) ]) ]

/-- Main BFS layer loop matching `bfsLoop`. -/
def bfsMainLoopStmt : Stmt :=
  .loop (.reg 14)
    (seqStmts
      [ bfsExpandStmt
      , .cond (.reg 20)
          (seqStmts
            [ bfsRevCopyStmt
            , .assign 18 (.reg 19)
            , .assign 19 (.bin .add (.reg 19) (.reg 20))
            , .assign 17 (.bin .add (.reg 17) (.const 1))
            , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19)
            , .cond (.reg 21)
                (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                  (.const 1) (.const 0))
                (.assign 14 (.bin .sub (.reg 14) (.const 1))) ])
          (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
            (.const 0) (.const 1)) ])

/-- Load the 16 config words from `cfgAddr = r0` into `r1 .. r16`. -/
def bfsLoadCfgStmt : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
    , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 3 (.load (.bin .add (.reg 0) (.const 2)))
    , .assign 4 (.load (.bin .add (.reg 0) (.const 3)))
    , .assign 5 (.load (.bin .add (.reg 0) (.const 4)))
    , .assign 6 (.load (.bin .add (.reg 0) (.const 5)))
    , .assign 7 (.load (.bin .add (.reg 0) (.const 6)))
    , .assign 8 (.load (.bin .add (.reg 0) (.const 7)))
    , .assign 9 (.load (.bin .add (.reg 0) (.const 8)))
    , .assign 10 (.load (.bin .add (.reg 0) (.const 9)))
    , .assign 11 (.load (.bin .add (.reg 0) (.const 10)))
    , .assign 12 (.load (.bin .add (.reg 0) (.const 11)))
    , .assign 13 (.load (.bin .add (.reg 0) (.const 12)))
    , .assign 14 (.load (.bin .add (.reg 0) (.const 13)))
    , .assign 15 (.load (.bin .add (.reg 0) (.const 14)))
    , .assign 16 (.load (.bin .add (.reg 0) (.const 15))) ]

/-- Multi-source layered BFS procedure taking `[cfgAddr]`, matching `bfsLayers`. -/
def bfsLayersProc : Stmt :=
  seqStmts
    [ bfsLoadCfgStmt
    , .store (.reg 10) (.const 0)
    , .cond (.reg 16)
        (seqStmts
          [ bfsInitStmt
          , .cond (.reg 21)
              (bfsWriteRetStmt (.const 1) (.reg 16) (.const 0) (.const 1) (.const 0))
              (seqStmts
                [ .assign 17 (.const 0)
                , .assign 18 (.const 0)
                , .assign 19 (.reg 16)
                , bfsMainLoopStmt
                , bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                    (.const 0) (.const 0) ]) ])
        (bfsWriteRetStmt (.const 0) (.const 0) (.const 0) (.const 0) (.const 1)) ]

theorem bfsLayersProc_noRand : Stmt.NoRand bfsLayersProc := by
  unfold bfsLayersProc bfsLoadCfgStmt bfsInitStmt bfsMainLoopStmt bfsExpandStmt
    bfsScanInnerStmt bfsRevCopyStmt bfsWriteRetStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-! ## 3. Pure Model Prefix/Append Lemmas -/

lemma bfsScanAdj_append (V : Finset ℕ) (nextDist : ℕ) (l₁ l₂ : List (ℕ × ℕ))
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    let r1 := bfsScanAdj V nextDist l₁ nxt vis dist
    let r2 := bfsScanAdj V nextDist l₂ r1.1 r1.2.1 r1.2.2.1
    bfsScanAdj V nextDist (l₁ ++ l₂) nxt vis dist =
      (r2.1, r2.2.1, r2.2.2.1, r1.2.2.2 + r2.2.2.2) := by
  induction l₁ generalizing nxt vis dist with
  | nil => simp [bfsScanAdj]
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [List.cons_append, bfsScanAdj]
    split_ifs
    · have h := ih (w :: nxt) (insert w vis) (Function.update dist w (some nextDist))
      simp only at h
      rw [h]; ext <;> simp [Nat.add_assoc, Nat.add_comm]
    · have h := ih nxt vis dist
      simp only at h
      rw [h]; ext <;> simp [Nat.add_assoc, Nat.add_comm]

lemma bfsScanAdj_take_succ (V : Finset ℕ) (nextDist : ℕ) (l : List (ℕ × ℕ))
    {j : ℕ} (hj : j < l.length) (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    let r := bfsScanAdj V nextDist (l.take j) nxt vis dist
    let w := (l[j]'hj).1
    bfsScanAdj V nextDist (l.take (j + 1)) nxt vis dist =
      if w ∈ V ∧ w ∉ r.2.1 then
        (w :: r.1, insert w r.2.1, Function.update r.2.2.1 w (some nextDist), r.2.2.2 + 1)
      else
        (r.1, r.2.1, r.2.2.1, r.2.2.2 + 1) := by
  rw [List.take_succ_eq_append_getElem hj]
  have h := bfsScanAdj_append V nextDist (l.take j) [l[j]'hj] nxt vis dist
  simp only at h
  rw [h]
  rcases hl : l[j]'hj with ⟨w, e⟩
  simp only [bfsScanAdj]
  split_ifs <;> rfl

lemma bfsExpandFrontier_append (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ)
    (f₁ f₂ : List ℕ) (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    let r1 := bfsExpandFrontier adj V nextDist f₁ nxt vis dist
    let r2 := bfsExpandFrontier adj V nextDist f₂ r1.1 r1.2.1 r1.2.2.1
    bfsExpandFrontier adj V nextDist (f₁ ++ f₂) nxt vis dist =
      (r2.1, r2.2.1, r2.2.2.1, r1.2.2.2 + r2.2.2.2) := by
  induction f₁ generalizing nxt vis dist with
  | nil => simp [bfsExpandFrontier]
  | cons u rest ih =>
    simp only [List.cons_append, bfsExpandFrontier]
    set s := bfsScanAdj V nextDist (adj u) nxt vis dist
    have h := ih s.1 s.2.1 s.2.2.1
    simp only at h
    rw [h]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    dsimp only; omega

lemma bfsExpandFrontier_take_succ (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ)
    (frontier : List ℕ) {q : ℕ} (hq : q < frontier.length)
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    let r := bfsExpandFrontier adj V nextDist (frontier.take q) nxt vis dist
    let s := bfsScanAdj V nextDist (adj (frontier[q]'hq)) r.1 r.2.1 r.2.2.1
    bfsExpandFrontier adj V nextDist (frontier.take (q + 1)) nxt vis dist =
      (s.1, s.2.1, s.2.2.1, r.2.2.2 + s.2.2.2 + 1) := by
  rw [List.take_succ_eq_append_getElem hq]
  have h := bfsExpandFrontier_append adj V nextDist (frontier.take q) [frontier[q]'hq] nxt vis dist
  simp only [bfsExpandFrontier] at h
  rw [h]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  dsimp only; omega

lemma bfsScanAdj_length_le_card (V : Finset ℕ) (nextDist : ℕ) (l : List (ℕ × ℕ))
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    let r := bfsScanAdj V nextDist l nxt vis dist
    (r.1.length - nxt.length) + vis.card = r.2.1.card ∧ nxt.length ≤ r.1.length := by
  induction l generalizing nxt vis dist with
  | nil => simp [bfsScanAdj]
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [bfsScanAdj]
    split_ifs with h
    · have h1 := ih (w :: nxt) (insert w vis) (Function.update dist w (some nextDist))
      simp only [List.length_cons, Finset.card_insert_of_notMem h.2] at h1
      dsimp only at h1 ⊢; omega
    · exact ih nxt vis dist

lemma bfsScanAdj_subset_V (V : Finset ℕ) (nextDist : ℕ) (l : List (ℕ × ℕ))
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ)
    (hvis : vis ⊆ V) (hnxt : ∀ x ∈ nxt, x ∈ vis) :
    let r := bfsScanAdj V nextDist l nxt vis dist
    vis ⊆ r.2.1 ∧ r.2.1 ⊆ V ∧ (∀ x ∈ r.1, x ∈ r.2.1) := by
  induction l generalizing nxt vis dist with
  | nil => exact ⟨Finset.Subset.refl _, hvis, hnxt⟩
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [bfsScanAdj]
    split_ifs with h
    · have h1 := ih (w :: nxt) (insert w vis) (Function.update dist w (some nextDist))
        (Finset.insert_subset h.1 hvis)
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hnxt x hx))
      exact ⟨Finset.Subset.trans (Finset.subset_insert _ _) h1.1, h1.2.1, h1.2.2⟩
    · exact ih nxt vis dist hvis hnxt

lemma bfsExpandFrontier_length_card (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ)
    (frontier nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    let r := bfsExpandFrontier adj V nextDist frontier nxt vis dist
    (r.1.length - nxt.length) + vis.card = r.2.1.card ∧ nxt.length ≤ r.1.length := by
  induction frontier generalizing nxt vis dist with
  | nil => simp [bfsExpandFrontier]
  | cons u rest ih =>
    simp only [bfsExpandFrontier]
    have h1 := bfsScanAdj_length_le_card V nextDist (adj u) nxt vis dist
    set s := bfsScanAdj V nextDist (adj u) nxt vis dist
    have h2 := ih s.1 s.2.1 s.2.2.1
    dsimp only at h1 h2 ⊢; omega

lemma bfsExpandFrontier_subset_V (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ)
    (frontier nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ)
    (hvis : vis ⊆ V) (hnxt : ∀ x ∈ nxt, x ∈ vis) :
    let r := bfsExpandFrontier adj V nextDist frontier nxt vis dist
    vis ⊆ r.2.1 ∧ r.2.1 ⊆ V ∧ (∀ x ∈ r.1, x ∈ r.2.1) := by
  induction frontier generalizing nxt vis dist with
  | nil => exact ⟨Finset.Subset.refl _, hvis, hnxt⟩
  | cons u rest ih =>
    simp only [bfsExpandFrontier]
    have h1 := bfsScanAdj_subset_V V nextDist (adj u) nxt vis dist hvis hnxt
    set s := bfsScanAdj V nextDist (adj u) nxt vis dist
    have h2 := ih s.1 s.2.1 s.2.2.1 h1.2.1 h1.2.2
    exact ⟨Finset.Subset.trans h1.1 h2.1, h2.2.1, h2.2.2⟩

lemma bfsLoop_cost_ge (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ)
    (rem curDist : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
    (vis : Finset ℕ) (dist : ℕ → Option ℕ) (cost : ℕ) :
    cost ≤ (bfsLoop adj V stopSet rem curDist frontier revLayers vis dist cost).cost := by
  induction rem generalizing curDist frontier revLayers vis dist cost with
  | zero => simp [bfsLoop]
  | succ rem ih =>
    simp only [bfsLoop]
    set r := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist
    split_ifs
    · simp; omega
    · simp; omega
    · have h := ih (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1
        (cost + r.2.2.2 + 1 + r.1.length)
      omega

lemma bfsLoop_cost_add (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ)
    (rem curDist : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
    (vis : Finset ℕ) (dist : ℕ → Option ℕ) (cost delta : ℕ) :
    (bfsLoop adj V stopSet rem curDist frontier revLayers vis dist (cost + delta)).cost =
      (bfsLoop adj V stopSet rem curDist frontier revLayers vis dist cost).cost + delta := by
  induction rem generalizing curDist frontier revLayers vis dist cost with
  | zero => simp [bfsLoop]
  | succ rem ih =>
    simp only [bfsLoop]
    set r := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist
    split_ifs
    · simp; omega
    · simp; omega
    · have h := ih (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1
        (cost + r.2.2.2 + 1 + r.1.length)
      have heq : cost + delta + r.2.2.2 + 1 + r.1.length =
        (cost + r.2.2.2 + 1 + r.1.length) + delta := by omega
      rw [heq]; exact h

/-! ## 4. Helper Stage Triples: `bfsInit_triple` and `bfsRevCopy_triple` -/

/-- Helper to check disjointness from `DisjRange`. -/
lemma disjRange_ne {a la b lb i j : ℕ} (h : DisjRange a la b lb) (hi : i < la) (hj : j < lb) :
    a + i ≠ b + j := by
  rcases h with h | h <;> omega

lemma bfsInit_triple {w : ℕ} {p : Program}
    {X S0 stopSet : Finset ℕ} {cfg : BfsCfg} {cfgAddr : ℕ} {m2 : ℕ} {st0 : State}
    (hS0 : S0 ⊆ X)
    (hdisj : BfsDisj w X.card m2 cfg cfgAddr)
    (hinit_list : ListAt st0.mem cfg.initPtr ((S0.sort (· ≤ ·)).map (locOf X)))
    (hinit_len : cfg.initLen = S0.card)
    (hinit_pos : 0 < S0.card)
    (hstop : cfg.hasStop = 0 → stopSet = ∅)
    (hstop_mem : cfg.hasStop ≠ 0 →
      ∀ v < X.card, st0.mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet)
    (hvis0 : ∀ v < X.card, st0.mem (cfg.visStampAddr + v) ≠ cfg.bfsGen)
    (hregs0 : ∀ r ≤ 16, st0.regs r =
      match r with
      | 0 => cfgAddr | 1 => cfg.offAddr | 2 => cfg.nbAddr
      | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
      | 5 => cfg.hasStop | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
      | 8 => cfg.visStampAddr | 9 => cfg.distAddr
      | 10 => cfg.layerOffAddr | 11 => cfg.layerDataAddr | 12 => cfg.tmpNxtAddr
      | 13 => cfg.bfsGen | 14 => cfg.maxDist | 15 => cfg.initPtr | _ => cfg.initLen) :
    Triple w p (fun st => st = st0) bfsInitStmt
      (normalPost fun st' =>
        (∀ r ≤ 16, st'.regs r = st0.regs r) ∧
        st'.regs 21 = (if (S0.sort (· ≤ ·)).any (fun v => decide (v ∈ stopSet)) then 1 else 0) ∧
        st'.mem (cfg.layerOffAddr + 1) = S0.card ∧
        ListAt st'.mem cfg.layerDataAddr ((S0.sort (· ≤ ·)).map (locOf X)) ∧
        (∀ v < X.card, st'.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ S0) ∧
        (∀ v < X.card, origOf X v ∈ S0 → st'.mem (cfg.distAddr + v) = 0) ∧
        (∀ v < X.card, st'.mem (cfg.visStampAddr + v) =
          if origOf X v ∈ S0 then cfg.bfsGen else st0.mem (cfg.visStampAddr + v)) ∧
        (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st'.mem a = st0.mem a) ∧
        st'.mem cfg.layerOffAddr = st0.mem cfg.layerOffAddr)
      (fun _ => 60 * S0.card + 20) := by
  set L0 := S0.sort (· ≤ ·)
  have hL0_len : L0.length = S0.card := Finset.length_sort (· ≤ ·)
  have hS0_le : S0.card ≤ X.card := Finset.card_le_card hS0
  rcases hdisj with ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
    hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
    hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
    hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
    hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  let I : State → Prop := fun st =>
    (∀ r ≤ 16, st.regs r = st0.regs r) ∧
    st.regs 22 ≤ S0.card ∧
    st.regs 21 = (if (L0.take (st.regs 22)).any (fun v => decide (v ∈ stopSet)) then 1 else 0) ∧
    (∀ j < st.regs 22, st.mem (cfg.layerDataAddr + j) = locOf X (L0.getD j 0)) ∧
    (∀ v < X.card, st.mem (cfg.visStampAddr + v) =
      if origOf X v ∈ L0.take (st.regs 22) then cfg.bfsGen else st0.mem (cfg.visStampAddr + v)) ∧
    (∀ v < X.card, origOf X v ∈ L0.take (st.regs 22) → st.mem (cfg.distAddr + v) = 0) ∧
    (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st.mem a = st0.mem a) ∧
    st.mem cfg.layerOffAddr = st0.mem cfg.layerOffAddr
  have hloop :
      Triple w p I
        (.loop (.bin .lt (.reg 22) (.reg 16))
          (seqStmts
            [ .assign 26 (.load (.bin .add (.reg 15) (.reg 22)))
            , .store (.bin .add (.reg 11) (.reg 22)) (.reg 26)
            , .store (.bin .add (.reg 8) (.reg 26)) (.reg 13)
            , .store (.bin .add (.reg 9) (.reg 26)) (.const 0)
            , .cond (.reg 5)
                (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 26))) (.reg 7))
                  (.assign 21 (.const 1))
                  .nop)
                .nop
            , .assign 22 (.bin .add (.reg 22) (.const 1)) ]))
        (normalPost fun st' =>
          (∀ r ≤ 16, st'.regs r = st0.regs r) ∧
          st'.regs 21 = (if L0.any (fun v => decide (v ∈ stopSet)) then 1 else 0) ∧
          (∀ j < S0.card, st'.mem (cfg.layerDataAddr + j) = locOf X (L0.getD j 0)) ∧
          (∀ v < X.card, st'.mem (cfg.visStampAddr + v) =
            if origOf X v ∈ S0 then cfg.bfsGen else st0.mem (cfg.visStampAddr + v)) ∧
          (∀ v < X.card, origOf X v ∈ S0 → st'.mem (cfg.distAddr + v) = 0) ∧
          (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st'.mem a = st0.mem a) ∧
          st'.mem cfg.layerOffAddr = st0.mem cfg.layerOffAddr)
        (fun st => ((Expr.bin .lt (.reg 22) (.reg 16)).size + 52 + 1) * (S0.card - st.regs 22) +
          (Expr.bin .lt (.reg 22) (.reg 16)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => S0.card - st.regs 22)
      (condVal := fun st => if st.regs 22 < S0.card then 1 else 0)
      (bodyBound := 52) ?_ ?_ ?_
    · intro stL ⟨hregs, _, _, _, _, _, _, _⟩
      have hr16 : stL.regs 16 = S0.card := ((hregs 16 (by decide)).trans (hregs0 16 (by decide))).trans hinit_len
      eval_expr
    · intro stL ⟨hregs, hq_le, hhit, hld, hvis, hdist, hfr, hlo0⟩ hv
      have hq_eq : stL.regs 22 = S0.card := by split_ifs at hv; omega
      have htake_full : L0.take (stL.regs 22) = L0 := by rw [hq_eq, ← hL0_len, List.take_length]
      have hmem_L0 : ∀ u, u ∈ L0 ↔ u ∈ S0 := fun u => Finset.mem_sort (· ≤ ·)
      rw [htake_full] at hhit hvis hdist
      refine ⟨hregs, hhit, by rwa [hq_eq] at hld, ?_, ?_, hfr, hlo0⟩
      · intro v hv'; have h := hvis v hv'; simp only [hmem_L0] at h; exact h
      · intro v hv' hmem; exact hdist v hv' ((hmem_L0 _).mpr hmem)
    · intro stL ⟨hregs, hq_le, hhit, hld, hvis, hdist, hfr, hlo0⟩ hv
      have hr : ∀ r ≤ 16, stL.regs r = _ := fun r hr => (hregs r hr).trans (hregs0 r hr)
      have hr5 : stL.regs 5 = cfg.hasStop := hr 5 (by decide)
      have hr6 : stL.regs 6 = cfg.stopArrAddr := hr 6 (by decide)
      have hr7 : stL.regs 7 = cfg.stopVal := hr 7 (by decide)
      have hr8 : stL.regs 8 = cfg.visStampAddr := hr 8 (by decide)
      have hr9 : stL.regs 9 = cfg.distAddr := hr 9 (by decide)
      have hr11 : stL.regs 11 = cfg.layerDataAddr := hr 11 (by decide)
      have hr13 : stL.regs 13 = cfg.bfsGen := hr 13 (by decide)
      have hr15 : stL.regs 15 = cfg.initPtr := hr 15 (by decide)
      have hr16 : stL.regs 16 = S0.card := (hr 16 (by decide)).trans hinit_len
      have hq_lt : stL.regs 22 < S0.card := by split_ifs at hv <;> omega
      set q := stL.regs 22
      have hq_L0 : q < L0.length := by omega
      set u := L0[q]'hq_L0
      have hu_S0 : u ∈ S0 := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hq_L0)
      have hu_X : u ∈ X := hS0 hu_S0
      set wLoc := locOf X u
      have hwLoc_lt : wLoc < X.card := locOf_lt hu_X
      have hmem_w : stL.mem (cfg.initPtr + q) = wLoc := by
        rw [hfr _ (hr_init _ ⟨by omega, by omega⟩)]
        have h := hinit_list q (by simp [L0, hL0_len, hq_lt])
        simpa [u, wLoc] using h
      have hnot_ws_init : ∀ a, cfg.initPtr ≤ a ∧ a < cfg.initPtr + cfg.initLen →
          ¬ BfsWriteSet X.card cfg cfgAddr a := hr_init
      wram_enter
      subst st
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wLoc) (by rw [← hmem_w]; eval_expr) ?_
      refine runs_seq_store_le (x := cfg.layerDataAddr + q) (v := wLoc)
        (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.visStampAddr + wLoc) (v := cfg.bfsGen)
        (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := cfg.distAddr + wLoc) (v := 0)
        (by eval_expr) (by eval_expr) ?_
      set mem1 := Function.update
        (Function.update (Function.update stL.mem (cfg.layerDataAddr + q) wLoc)
          (cfg.visStampAddr + wLoc) cfg.bfsGen)
        (cfg.distAddr + wLoc) 0
      have hmem1_fr : ∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → mem1 a = st0.mem a := by
        intro a ha
        have hne1 : a ≠ cfg.distAddr + wLoc := fun h => ha (Or.inr (Or.inl (by omega)))
        have hne2 : a ≠ cfg.visStampAddr + wLoc := fun h => ha (Or.inl (by omega))
        have hne3 : a ≠ cfg.layerDataAddr + q := fun h => ha (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
        simp only [mem1, Function.update_of_ne hne1, Function.update_of_ne hne2,
          Function.update_of_ne hne3]
        exact hfr a ha
      have hmem1_lo0 : mem1 cfg.layerOffAddr = st0.mem cfg.layerOffAddr := by
        have h1 : cfg.layerOffAddr ≠ cfg.distAddr + wLoc := by
          have := disjRange_ne hd_dlo hwLoc_lt (by omega : 0 < X.card + 1); omega
        have h2 : cfg.layerOffAddr ≠ cfg.visStampAddr + wLoc := by
          have := disjRange_ne hd_vlo hwLoc_lt (by omega : 0 < X.card + 1); omega
        have h3 : cfg.layerOffAddr ≠ cfg.layerDataAddr + q := by
          have := disjRange_ne hd_lold (by omega : 0 < X.card + 1) (by omega : q < X.card); omega
        simp only [mem1, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3, hlo0]
      have hmem1_ld : ∀ j < q + 1, mem1 (cfg.layerDataAddr + j) = locOf X (L0.getD j 0) := by
        intro j hj
        have hj_lt_nX : j < X.card := by omega
        have h1 : cfg.layerDataAddr + j ≠ cfg.distAddr + wLoc :=
          (disjRange_ne hd_dld hwLoc_lt hj_lt_nX).symm
        have h2 : cfg.layerDataAddr + j ≠ cfg.visStampAddr + wLoc :=
          (disjRange_ne hd_vld hwLoc_lt hj_lt_nX).symm
        simp only [mem1, Function.update_of_ne h1, Function.update_of_ne h2]
        by_cases hjq : j = q
        · subst hjq
          rw [Function.update_self, List.getD_eq_getElem _ 0 hq_L0]
        · rw [Function.update_of_ne (by omega)]; exact hld j (by omega)
      have hmem1_vis : ∀ v < X.card, mem1 (cfg.visStampAddr + v) =
          if origOf X v ∈ L0.take (q + 1) then cfg.bfsGen else st0.mem (cfg.visStampAddr + v) := by
        intro v hv'
        have h1 : cfg.visStampAddr + v ≠ cfg.distAddr + wLoc :=
          disjRange_ne hd_vd hv' hwLoc_lt
        simp only [mem1, Function.update_of_ne h1]
        by_cases hvw : v = wLoc
        · subst hvw
          have horig : origOf X wLoc = u := origOf_locOf hu_X
          have hmem_t : u ∈ L0.take (q + 1) := by
            rw [List.take_succ_eq_append_getElem hq_L0]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          rw [Function.update_self, horig]
          simp only [hmem_t, ↓reduceIte]
        · have h2 : cfg.visStampAddr + v ≠ cfg.layerDataAddr + q :=
            disjRange_ne hd_vld hv' (by omega)
          have hne_u : origOf X v ≠ u := fun h => hvw (by rw [← locOf_origOf hv', h])
          have hiff : origOf X v ∈ L0.take (q + 1) ↔ origOf X v ∈ L0.take q := by
            rw [List.take_succ_eq_append_getElem hq_L0, List.mem_append, List.mem_singleton]
            exact ⟨fun h => h.resolve_right hne_u, Or.inl⟩
          rw [Function.update_of_ne (by omega), Function.update_of_ne h2, hvis v hv']
          simp only [hiff]
      have hmem1_dist : ∀ v < X.card, origOf X v ∈ L0.take (q + 1) → mem1 (cfg.distAddr + v) = 0 := by
        intro v hv' hmem_t
        by_cases hvw : v = wLoc
        · subst hvw; simp only [mem1, Function.update_self]
        · have hne_u : origOf X v ≠ u := fun h => hvw (by rw [← locOf_origOf hv', h])
          have hmem_old : origOf X v ∈ L0.take q := by
            rw [List.take_succ_eq_append_getElem hq_L0, List.mem_append, List.mem_singleton] at hmem_t
            exact hmem_t.resolve_right hne_u
          have h1 : cfg.distAddr + v ≠ cfg.distAddr + wLoc := by omega
          have h2 : cfg.distAddr + v ≠ cfg.visStampAddr + wLoc :=
            (disjRange_ne hd_vd hwLoc_lt hv').symm
          have h3 : cfg.distAddr + v ≠ cfg.layerDataAddr + q :=
            disjRange_ne hd_dld hv' (by omega)
          dsimp only [mem1]
          rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
          exact hdist v hv' hmem_old
      have hany_succ :
          (L0.take (q + 1)).any (fun v => decide (v ∈ stopSet)) =
            ((L0.take q).any (fun v => decide (v ∈ stopSet)) || decide (u ∈ stopSet)) := by
        rw [List.take_succ_eq_append_getElem hq_L0, List.any_append]
        simp [u]
      refine runs_seq_cond_le (v := cfg.hasStop) (by eval_expr)
        (fun hhs_ne => ?_) (fun hhs_zero => ?_)
      · have hstop_w_lt : cfg.stopArrAddr + wLoc < 2 ^ w := by have := hw_stop hhs_ne; omega
        have hstop_w_mem : mem1 (cfg.stopArrAddr + wLoc) = st0.mem (cfg.stopArrAddr + wLoc) :=
          hmem1_fr _ (hr_stop hhs_ne _ ⟨by omega, by omega⟩)
        have hu_stop_iff : st0.mem (cfg.stopArrAddr + wLoc) = cfg.stopVal ↔ u ∈ stopSet := by
          have := hstop_mem hhs_ne wLoc hwLoc_lt
          rwa [origOf_locOf hu_X] at this
        by_cases hu_stop : u ∈ stopSet
        · have heq_sv : mem1 (cfg.stopArrAddr + wLoc) = cfg.stopVal :=
            hstop_w_mem.trans (hu_stop_iff.mpr hu_stop)
          refine runs_seq_cond_le (v := 1)
            (by
              change Expr.eval w { mem := mem1, regs := Function.update stL.regs 26 wLoc, pos := stL.pos } _ = _
              simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (6 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (7 : ℕ) ≠ 26), Function.update_self,
                hr6, hr7, hstop_w_lt, ↓reduceIte, Option.map_some, heq_sv,
                show 1 < 2 ^ w by omega])
            (fun _ => ?_) (fun h0 => absurd h0 (by decide))
          refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
          refine runs_assign_le (v := q + 1) (by eval_expr) ?_ ?_
          · dsimp only [normalPost]
            refine ⟨⟨?_, by simp; omega, ?_, hmem1_ld, hmem1_vis, hmem1_dist, hmem1_fr, hmem1_lo0⟩,
              by simp; omega⟩
            · intro r hr_le
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              exact hregs r hr_le
            · simp only [Function.update_self, Function.update_of_ne (by decide : (21 : ℕ) ≠ 22),
                hany_succ, decide_eq_true hu_stop, Bool.or_true, ↓reduceIte]
          · wram_cost
        · have hne_sv : mem1 (cfg.stopArrAddr + wLoc) ≠ cfg.stopVal := fun h =>
            hu_stop (hu_stop_iff.mp (hstop_w_mem.symm.trans h))
          refine runs_seq_cond_le (v := 0)
            (by
              change Expr.eval w { mem := mem1, regs := Function.update stL.regs 26 wLoc, pos := stL.pos } _ = _
              simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (6 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (7 : ℕ) ≠ 26), Function.update_self,
                hr6, hr7, hstop_w_lt, ↓reduceIte, Option.map_some, hne_sv,
                show 0 < 2 ^ w by omega])
            (fun h0 => absurd rfl h0) (fun _ => ?_)
          refine runs_seq_nop_le ?_
          refine runs_assign_le (v := q + 1) (by eval_expr) ?_ ?_
          · dsimp only [normalPost]
            refine ⟨⟨?_, by simp; omega, ?_, hmem1_ld, hmem1_vis, hmem1_dist, hmem1_fr, hmem1_lo0⟩,
              by simp; omega⟩
            · intro r hr_le
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hregs r hr_le
            · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22),
                Function.update_of_ne (by decide : (21 : ℕ) ≠ 26), Function.update_self,
                hany_succ, decide_eq_false hu_stop, Bool.or_false, hhit]
          · wram_cost
      · refine runs_seq_nop_le ?_
        refine runs_assign_le (v := q + 1) (by eval_expr) ?_ ?_
        · dsimp only [normalPost]
          have hstop_empty : stopSet = ∅ := hstop hhs_zero
          refine ⟨⟨?_, by simp; omega, ?_, hmem1_ld, hmem1_vis, hmem1_dist, hmem1_fr, hmem1_lo0⟩,
            by simp; omega⟩
          · intro r hr_le
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hregs r hr_le
          · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22),
              Function.update_of_ne (by decide : (21 : ℕ) ≠ 26), Function.update_self]
            rw [hany_succ]
            simp only [hstop_empty, Finset.notMem_empty, decide_false, Bool.or_false, hhit]
        · wram_cost
  wram_enter
  subst st
  unfold bfsInitStmt
  dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set stInit : State := { st0 with regs := Function.update (Function.update st0.regs 21 0) 22 0 }
  have hinit : I stInit := by
    refine ⟨?_, by simp [stInit], by simp [stInit],
      fun j hj => by simp [stInit] at hj,
      fun v _ => by simp [stInit],
      fun v _ h => by simp [stInit] at h,
      fun _ _ => rfl, rfl⟩
    intro r hr_le
    simp only [stInit, Function.update_of_ne (by omega : r ≠ 22),
      Function.update_of_ne (by omega : r ≠ 21)]
  refine runs_seq_triple_le hloop hinit (fun st1 hst1 => ?_)
  rcases hst1 with ⟨hr1, hhit1, hld1, hvis1, hdist1, hfr1, hlo0_1⟩
  have hr1_10 : st1.regs 10 = cfg.layerOffAddr := (hr1 10 (by decide)).trans (hregs0 10 (by decide))
  have hr1_16 : st1.regs 16 = S0.card := ((hr1 16 (by decide)).trans (hregs0 16 (by decide))).trans hinit_len
  refine runs_store_le (x := cfg.layerOffAddr + 1) (v := S0.card) (by eval_expr) (by eval_expr) ?_ ?_
  · dsimp only [normalPost]
    refine ⟨hr1, hhit1, Function.update_self _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_map, hL0_len] at hj
      have hne : cfg.layerDataAddr + j ≠ cfg.layerOffAddr + 1 :=
        (disjRange_ne hd_lold (by omega : 1 < X.card + 1) (by omega : j < X.card)).symm
      rw [Function.update_of_ne hne, hld1 j hj, List.getElem_map, List.getD_eq_getElem _ 0 (by omega)]
    · intro v hv'
      have hne : cfg.visStampAddr + v ≠ cfg.layerOffAddr + 1 :=
        disjRange_ne hd_vlo hv' (by omega : 1 < X.card + 1)
      rw [Function.update_of_ne hne, hvis1 v hv']
      by_cases hm : origOf X v ∈ S0
      · simp only [hm, ↓reduceIte]
      · simp only [hm, ↓reduceIte, iff_false]; exact hvis0 v hv'
    · intro v hv' hm
      have hne : cfg.distAddr + v ≠ cfg.layerOffAddr + 1 :=
        disjRange_ne hd_dlo hv' (by omega : 1 < X.card + 1)
      rw [Function.update_of_ne hne]; exact hdist1 v hv' hm
    · intro v hv'
      have hne : cfg.visStampAddr + v ≠ cfg.layerOffAddr + 1 :=
        disjRange_ne hd_vlo hv' (by omega : 1 < X.card + 1)
      rw [Function.update_of_ne hne]; exact hvis1 v hv'
    · intro a ha
      have hne : a ≠ cfg.layerOffAddr + 1 := fun h =>
        ha (Or.inr (Or.inr (Or.inl (by omega))))
      rw [Function.update_of_ne hne]; exact hfr1 a ha
    · rw [Function.update_of_ne (by omega)]; exact hlo0_1
  · have hsz : (Expr.bin .lt (.reg 22) (.reg 16)).size = 3 := rfl
    simp only [stInit, Function.update_self, Nat.sub_zero, hsz]
    wram_cost

end MinCostFlow.ExpanderDecomp
