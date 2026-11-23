module

public import MinCostFlow.ExpanderDecomp.RouteDFS
public import MinCostFlow.ExpanderDecomp.RouteProgBFSBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking DFS Word-RAM Procedure: Definitions, Layouts, and Base Helpers

Defines the Word-RAM configuration block (`DfsCfg`, `DfsCfgAt`), disjointness
invariant (`DfsDisj`), output predicate (`DfsOutAt`), deterministic procedure
`dfsBlockProc` matching `dfsBlock`, pure `dfsStep`/`dfsSources`
cost/path-append lemmas, and the accepted-path & return-block sub-triples.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Configuration Block, Memory Regions, and Output Predicates -/

/-- Input configuration words at `cfgAddr + 0 .. cfgAddr + 23` for `dfsBlockProc`. -/
structure DfsCfg where
  offAddr : ℕ
  nbAddr : ℕ
  edgeAddr : ℕ
  maskArrAddr : ℕ
  maskBadVal : ℕ
  stopArrAddr : ℕ
  stopVal : ℕ
  visStampAddr : ℕ
  bfsGen : ℕ
  distAddr : ℕ
  curStampAddr : ℕ
  curAddr : ℕ
  usedStampAddr : ℕ
  deadStampAddr : ℕ
  stkVertAddr : ℕ
  stkEdgeAddr : ℕ
  usedListAddr : ℕ
  dfsGen : ℕ
  targetDepth : ℕ
  srcPtr : ℕ
  srcLen : ℕ
  heapIn : ℕ
  inHead : ℕ
  inTail : ℕ

/-- The 24 input configuration words of `cfg` reside at `cfgAddr .. cfgAddr + 23`. -/
def DfsCfgAt (mem : ℕ → ℕ) (cfgAddr : ℕ) (cfg : DfsCfg) : Prop :=
  mem (cfgAddr + 0) = cfg.offAddr ∧
  mem (cfgAddr + 1) = cfg.nbAddr ∧
  mem (cfgAddr + 2) = cfg.edgeAddr ∧
  mem (cfgAddr + 3) = cfg.maskArrAddr ∧
  mem (cfgAddr + 4) = cfg.maskBadVal ∧
  mem (cfgAddr + 5) = cfg.stopArrAddr ∧
  mem (cfgAddr + 6) = cfg.stopVal ∧
  mem (cfgAddr + 7) = cfg.visStampAddr ∧
  mem (cfgAddr + 8) = cfg.bfsGen ∧
  mem (cfgAddr + 9) = cfg.distAddr ∧
  mem (cfgAddr + 10) = cfg.curStampAddr ∧
  mem (cfgAddr + 11) = cfg.curAddr ∧
  mem (cfgAddr + 12) = cfg.usedStampAddr ∧
  mem (cfgAddr + 13) = cfg.deadStampAddr ∧
  mem (cfgAddr + 14) = cfg.stkVertAddr ∧
  mem (cfgAddr + 15) = cfg.stkEdgeAddr ∧
  mem (cfgAddr + 16) = cfg.usedListAddr ∧
  mem (cfgAddr + 17) = cfg.dfsGen ∧
  mem (cfgAddr + 18) = cfg.targetDepth ∧
  mem (cfgAddr + 19) = cfg.srcPtr ∧
  mem (cfgAddr + 20) = cfg.srcLen ∧
  mem (cfgAddr + 21) = cfg.heapIn ∧
  mem (cfgAddr + 22) = cfg.inHead ∧
  mem (cfgAddr + 23) = cfg.inTail

/-- Addresses that `dfsBlockProc` may overwrite (all scratch arrays, output slots, and heap
interval `[cfg.heapIn, cfg.heapIn + 5 * nX)`). -/
def DfsWriteSet (nX : ℕ) (cfg : DfsCfg) (cfgAddr : ℕ) (a : ℕ) : Prop :=
  (cfg.curStampAddr ≤ a ∧ a < cfg.curStampAddr + nX) ∨
  (cfg.curAddr ≤ a ∧ a < cfg.curAddr + nX) ∨
  (cfg.usedStampAddr ≤ a ∧ a < cfg.usedStampAddr + nX) ∨
  (cfg.deadStampAddr ≤ a ∧ a < cfg.deadStampAddr + nX) ∨
  (cfg.stkVertAddr ≤ a ∧ a < cfg.stkVertAddr + nX) ∨
  (cfg.stkEdgeAddr ≤ a ∧ a < cfg.stkEdgeAddr + nX) ∨
  (cfg.usedListAddr ≤ a ∧ a < cfg.usedListAddr + nX) ∨
  (cfgAddr + 24 ≤ a ∧ a < cfgAddr + 29) ∨
  (cfg.heapIn ≤ a ∧ a < cfg.heapIn + 5 * nX)

/-- Pairwise disjointness and word-size bounds for `dfsBlockProc`. -/
structure DfsDisj (w nX m2 : ℕ) (cfg : DfsCfg) (cfgAddr : ℕ) : Prop where
  -- Pairwise disjointness of the 9 writable regions
  -- 1: curStamp, 2: cur, 3: usedStamp, 4: deadStamp, 5: stkVert, 6: stkEdge, 7: usedList, 8: cfgOut, 9: heap
  cs_cur : DisjRange cfg.curStampAddr nX cfg.curAddr nX
  cs_us : DisjRange cfg.curStampAddr nX cfg.usedStampAddr nX
  cs_ds : DisjRange cfg.curStampAddr nX cfg.deadStampAddr nX
  cs_sv : DisjRange cfg.curStampAddr nX cfg.stkVertAddr nX
  cs_se : DisjRange cfg.curStampAddr nX cfg.stkEdgeAddr nX
  cs_ul : DisjRange cfg.curStampAddr nX cfg.usedListAddr nX
  cs_co : DisjRange cfg.curStampAddr nX (cfgAddr + 24) 5
  cs_hp : DisjRange cfg.curStampAddr nX cfg.heapIn (5 * nX)
  cur_us : DisjRange cfg.curAddr nX cfg.usedStampAddr nX
  cur_ds : DisjRange cfg.curAddr nX cfg.deadStampAddr nX
  cur_sv : DisjRange cfg.curAddr nX cfg.stkVertAddr nX
  cur_se : DisjRange cfg.curAddr nX cfg.stkEdgeAddr nX
  cur_ul : DisjRange cfg.curAddr nX cfg.usedListAddr nX
  cur_co : DisjRange cfg.curAddr nX (cfgAddr + 24) 5
  cur_hp : DisjRange cfg.curAddr nX cfg.heapIn (5 * nX)
  us_ds : DisjRange cfg.usedStampAddr nX cfg.deadStampAddr nX
  us_sv : DisjRange cfg.usedStampAddr nX cfg.stkVertAddr nX
  us_se : DisjRange cfg.usedStampAddr nX cfg.stkEdgeAddr nX
  us_ul : DisjRange cfg.usedStampAddr nX cfg.usedListAddr nX
  us_co : DisjRange cfg.usedStampAddr nX (cfgAddr + 24) 5
  us_hp : DisjRange cfg.usedStampAddr nX cfg.heapIn (5 * nX)
  ds_sv : DisjRange cfg.deadStampAddr nX cfg.stkVertAddr nX
  ds_se : DisjRange cfg.deadStampAddr nX cfg.stkEdgeAddr nX
  ds_ul : DisjRange cfg.deadStampAddr nX cfg.usedListAddr nX
  ds_co : DisjRange cfg.deadStampAddr nX (cfgAddr + 24) 5
  ds_hp : DisjRange cfg.deadStampAddr nX cfg.heapIn (5 * nX)
  sv_se : DisjRange cfg.stkVertAddr nX cfg.stkEdgeAddr nX
  sv_ul : DisjRange cfg.stkVertAddr nX cfg.usedListAddr nX
  sv_co : DisjRange cfg.stkVertAddr nX (cfgAddr + 24) 5
  sv_hp : DisjRange cfg.stkVertAddr nX cfg.heapIn (5 * nX)
  se_ul : DisjRange cfg.stkEdgeAddr nX cfg.usedListAddr nX
  se_co : DisjRange cfg.stkEdgeAddr nX (cfgAddr + 24) 5
  se_hp : DisjRange cfg.stkEdgeAddr nX cfg.heapIn (5 * nX)
  ul_co : DisjRange cfg.usedListAddr nX (cfgAddr + 24) 5
  ul_hp : DisjRange cfg.usedListAddr nX cfg.heapIn (5 * nX)
  co_hp : DisjRange (cfgAddr + 24) 5 cfg.heapIn (5 * nX)
  -- Read-only regions disjoint from DfsWriteSet
  ro_cfg : ∀ a, cfgAddr ≤ a ∧ a < cfgAddr + 24 → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_off : ∀ a, cfg.offAddr ≤ a ∧ a < cfg.offAddr + nX + 1 → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_nb : ∀ a, cfg.nbAddr ≤ a ∧ a < cfg.nbAddr + m2 → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_edge : ∀ a, cfg.edgeAddr ≤ a ∧ a < cfg.edgeAddr + m2 → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_mask : ∀ a, cfg.maskArrAddr ≤ a ∧ a < cfg.maskArrAddr + nX → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_stop : ∀ a, cfg.stopArrAddr ≤ a ∧ a < cfg.stopArrAddr + nX → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_vis : ∀ a, cfg.visStampAddr ≤ a ∧ a < cfg.visStampAddr + nX → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_dist : ∀ a, cfg.distAddr ≤ a ∧ a < cfg.distAddr + nX → ¬ DfsWriteSet nX cfg cfgAddr a
  ro_src : ∀ a, cfg.srcPtr ≤ a ∧ a < cfg.srcPtr + cfg.srcLen → ¬ DfsWriteSet nX cfg cfgAddr a
  -- Word-size and heap bounds
  hheap_pos : 1 ≤ cfg.heapIn
  w_cfg : cfgAddr + 32 < 2 ^ w
  w_off : cfg.offAddr + nX + 5 < 2 ^ w
  w_nb : cfg.nbAddr + m2 + 5 < 2 ^ w
  w_edge : cfg.edgeAddr + m2 + 5 < 2 ^ w
  w_mask : cfg.maskArrAddr + nX + 5 < 2 ^ w
  w_stop : cfg.stopArrAddr + nX + 5 < 2 ^ w
  w_vis : cfg.visStampAddr + nX + 5 < 2 ^ w
  w_dist : cfg.distAddr + nX + 5 < 2 ^ w
  w_cs : cfg.curStampAddr + nX + 5 < 2 ^ w
  w_cur : cfg.curAddr + nX + 5 < 2 ^ w
  w_us : cfg.usedStampAddr + nX + 5 < 2 ^ w
  w_ds : cfg.deadStampAddr + nX + 5 < 2 ^ w
  w_sv : cfg.stkVertAddr + nX + 5 < 2 ^ w
  w_se : cfg.stkEdgeAddr + nX + 5 < 2 ^ w
  w_ul : cfg.usedListAddr + nX + 5 < 2 ^ w
  w_src : cfg.srcPtr + cfg.srcLen + 5 < 2 ^ w
  w_heap : cfg.heapIn + 5 * nX + 5 < 2 ^ w
  w_mb : cfg.maskBadVal < 2 ^ w
  w_sv_val : cfg.stopVal < 2 ^ w
  w_bgen : cfg.bfsGen < 2 ^ w
  w_dgen : cfg.dfsGen < 2 ^ w
  w_td : cfg.targetDepth + 2 < 2 ^ w
  w_m2 : m2 + 5 < 2 ^ w
  w_nX : nX + 5 < 2 ^ w
  w4 : 4 ≤ 2 ^ w

/-- Post-state representation of `dfsBlockProc` matching `res : DFSState` prepended onto `acc`. -/
def DfsOutAt (mem : ℕ → ℕ) (X : Finset ℕ) (cfg : DfsCfg) (cfgAddr heapLo : ℕ)
    (acc : List ((ℕ × ℕ) × List ℕ)) (res : DFSState) : Prop :=
  let outUsedCount := mem (cfgAddr + 24)
  let outPathsCount := mem (cfgAddr + 25)
  let outHead := mem (cfgAddr + 26)
  let outTail := mem (cfgAddr + 27)
  let outHeap := mem (cfgAddr + 28)
  outUsedCount = res.used.card ∧
  outPathsCount = res.paths.length ∧
  cfg.heapIn ≤ outHeap ∧
  outHeap ≤ cfg.heapIn + 5 * res.used.card ∧
  (∃ ul : List ℕ, ul.length = res.used.card ∧ ul.Nodup ∧
    (∀ x ∈ ul, x < X.card ∧ origOf X x ∈ res.used) ∧
    (∀ v ∈ res.used, v ∈ X ∧ locOf X v ∈ ul) ∧
    ListAt mem cfg.usedListAddr ul) ∧
  (∀ v < X.card, mem (cfg.usedStampAddr + v) = cfg.dfsGen ↔ origOf X v ∈ res.used) ∧
  PathChainAt mem X heapLo outHeap outHead outTail (res.paths ++ acc)

/-- Explicit cost bound for `dfsBlockProc` in terms of `(dfsBlock ...).cost`. -/
def dfsProgCost (modelCost : ℕ) : ℕ :=
  150 * modelCost + 260

/-! ## 2. Word-RAM Statements for `dfsBlockProc` -/

/-- Write the 5 DFS output words to `cfgAddr + 24 .. cfgAddr + 28` and return `usedCount` (`r25`). -/
def dfsWriteRetStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 0) (.const 24)) (.reg 25)
    , .store (.bin .add (.reg 0) (.const 25)) (.reg 26)
    , .store (.bin .add (.reg 0) (.const 26)) (.reg 23)
    , .store (.bin .add (.reg 0) (.const 27)) (.reg 24)
    , .store (.bin .add (.reg 0) (.const 28)) (.reg 22)
    , .ret (.reg 25) ]

/-- Accept path when `u ∈ T`: copy `stkEdge[0..depth-1]` to heap, prepend a 4-word `PathChainAt`
node onto `(r23, r24)`, stamp & record all `depth + 1` vertices on `stkVert[0..depth]` in
`usedStamp`/`usedList`, and clear `active` (`r29 := 0`). -/
def dfsAcceptStmt : Stmt :=
  seqStmts
    [ .assign 34 (.reg 22)
    , .store (.reg 22) (.reg 30)
    , .assign 22 (.bin .add (.reg 22) (.const 1))
    , .assign 32 (.const 0)
    , .loop (.bin .lt (.reg 32) (.reg 30))
        (seqStmts
          [ .store (.bin .add (.reg 22) (.reg 32))
              (.load (.bin .add (.reg 16) (.reg 32)))
          , .assign 32 (.bin .add (.reg 32) (.const 1)) ])
    , .assign 22 (.bin .add (.reg 22) (.reg 30))
    , .store (.reg 22) (.reg 28)
    , .store (.bin .add (.reg 22) (.const 1)) (.reg 31)
    , .store (.bin .add (.reg 22) (.const 2)) (.reg 34)
    , .store (.bin .add (.reg 22) (.const 3)) (.reg 23)
    , .cond (.bin .eq (.reg 23) (.const 0)) (.assign 24 (.reg 22)) .nop
    , .assign 23 (.reg 22)
    , .assign 22 (.bin .add (.reg 22) (.const 4))
    , .assign 26 (.bin .add (.reg 26) (.const 1))
    , .assign 32 (.const 0)
    , .loop (.bin .lt (.reg 32) (.bin .add (.reg 30) (.const 1)))
        (seqStmts
          [ .assign 35 (.load (.bin .add (.reg 15) (.reg 32)))
          , .store (.bin .add (.reg 13) (.reg 35)) (.reg 18)
          , .store (.bin .add (.reg 17) (.reg 25)) (.reg 35)
          , .assign 25 (.bin .add (.reg 25) (.const 1))
          , .assign 32 (.bin .add (.reg 32) (.const 1)) ])
    , .assign 29 (.const 0) ]

/-- Mark current tip `u` (`r31`) dead and backtrack one level (or stop if `depth = 0`). -/
def dfsBacktrackStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 14) (.reg 31)) (.reg 18)
    , .cond (.reg 30)
        (seqStmts
          [ .assign 30 (.bin .sub (.reg 30) (.const 1))
          , .assign 31 (.load (.bin .add (.reg 15) (.reg 30))) ])
        (.assign 29 (.const 0)) ]

/-- One iteration of the DFS stack loop matching one step of `dfsStep`. -/
def dfsStepBodyStmt : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7))
    dfsAcceptStmt
    (.cond (.bin .eq (.reg 30) (.reg 19))
      dfsBacktrackStmt
      (seqStmts
        [ .cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 31))) (.reg 18))
            .nop
            (seqStmts
              [ .store (.bin .add (.reg 11) (.reg 31)) (.reg 18)
              , .store (.bin .add (.reg 12) (.reg 31))
                  (.load (.bin .add (.reg 1) (.reg 31))) ])
        , .assign 32 (.load (.bin .add (.reg 12) (.reg 31)))
        , .assign 33 (.load (.bin .add (.reg 1) (.bin .add (.reg 31) (.const 1))))
        , .cond (.bin .eq (.reg 32) (.reg 33))
            dfsBacktrackStmt
            (seqStmts
              [ .store (.bin .add (.reg 12) (.reg 31)) (.bin .add (.reg 32) (.const 1))
              , .assign 33 (.load (.bin .add (.reg 2) (.reg 32)))
              , .assign 34 (.load (.bin .add (.reg 3) (.reg 32)))
              , .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 33))) (.reg 5))
                  .nop
                  (.cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 33))) (.reg 18))
                    .nop
                    (.cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 33))) (.reg 18))
                      .nop
                      (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 33))) (.reg 9))
                        (.cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 33)))
                                  (.bin .add (.reg 30) (.const 1)))
                          (seqStmts
                            [ .store (.bin .add (.reg 16) (.reg 30)) (.reg 34)
                            , .assign 30 (.bin .add (.reg 30) (.const 1))
                            , .store (.bin .add (.reg 15) (.reg 30)) (.reg 33)
                            , .assign 31 (.reg 33) ])
                          .nop)
                        .nop))) ]) ]))

/-- Iterative DFS stack loop from one source `s`. -/
def dfsStepLoopStmt : Stmt :=
  .loop (.reg 29) dfsStepBodyStmt

/-- Outer loop over all sources `srcIdx = 0 .. srcLen - 1`, matching `dfsSources`. -/
def dfsSourcesLoopStmt : Stmt :=
  .loop (.bin .lt (.reg 27) (.reg 21))
    (seqStmts
      [ .assign 28 (.load (.bin .add (.reg 20) (.reg 27)))
      , .cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 28))) (.reg 18))
          .nop
          (.cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 28))) (.reg 18))
            .nop
            (seqStmts
              [ .store (.reg 15) (.reg 28)
              , .assign 30 (.const 0)
              , .assign 31 (.reg 28)
              , .assign 29 (.const 1)
              , dfsStepLoopStmt ]))
      , .assign 27 (.bin .add (.reg 27) (.const 1)) ])

/-- Load the 24 config words from `cfgAddr = r0` into `r1 .. r24`. -/
def dfsLoadCfgStmt : Stmt :=
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
    , .assign 16 (.load (.bin .add (.reg 0) (.const 15)))
    , .assign 17 (.load (.bin .add (.reg 0) (.const 16)))
    , .assign 18 (.load (.bin .add (.reg 0) (.const 17)))
    , .assign 19 (.load (.bin .add (.reg 0) (.const 18)))
    , .assign 20 (.load (.bin .add (.reg 0) (.const 19)))
    , .assign 21 (.load (.bin .add (.reg 0) (.const 20)))
    , .assign 22 (.load (.bin .add (.reg 0) (.const 21)))
    , .assign 23 (.load (.bin .add (.reg 0) (.const 22)))
    , .assign 24 (.load (.bin .add (.reg 0) (.const 23))) ]

/-- Full blocking DFS procedure taking `[cfgAddr]`, matching `dfsBlock`. -/
def dfsBlockProc : Stmt :=
  seqStmts
    [ dfsLoadCfgStmt
    , .assign 25 (.const 0)
    , .assign 26 (.const 0)
    , .assign 27 (.const 0)
    , dfsSourcesLoopStmt
    , dfsWriteRetStmt ]

theorem dfsBlockProc_noRand : Stmt.NoRand dfsBlockProc := by
  unfold dfsBlockProc dfsLoadCfgStmt dfsSourcesLoopStmt dfsStepLoopStmt
    dfsStepBodyStmt dfsAcceptStmt dfsBacktrackStmt dfsWriteRetStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-! ## 3. Pure Model Lemmas for `dfsStep`, `dfsSources`, and `dfsPot` -/

lemma dfsStep_cost_add (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j s fuel u r : ℕ)
    (trail : List (ℕ × ℕ)) (st : DFSState) (k : ℕ) :
    let a := dfsStep V T dist j s fuel u r trail { st with cost := st.cost + k }
    let b := dfsStep V T dist j s fuel u r trail st
    a.used = b.used ∧ a.dead = b.dead ∧ a.cursor = b.cursor ∧
      a.paths = b.paths ∧ a.cost = b.cost + k := by
  induction fuel generalizing u r trail st with
  | zero => simp [dfsStep]
  | succ f ih =>
    simp only [dfsStep]
    by_cases hT : u ∈ T
    · simp [hT]; omega
    · simp only [hT, ↓reduceIte]
      by_cases hrj : r = j
      · subst hrj; simp only [↓reduceIte]
        cases trail with
        | nil => dsimp only; exact ⟨rfl, rfl, rfl, rfl, by omega⟩
        | cons pe rest =>
          rcases pe with ⟨p, e⟩; dsimp only
          have h1 := ih p (r - 1) rest { st with dead := insert u st.dead, cost := st.cost + 1 }
          simpa [Nat.add_assoc, Nat.add_comm] using h1
      · simp only [hrj, ↓reduceIte]
        cases hcur : st.cursor u with
        | nil =>
          dsimp only
          cases trail with
          | nil => dsimp only; exact ⟨rfl, rfl, rfl, rfl, by omega⟩
          | cons pe rest =>
            rcases pe with ⟨p, e⟩; dsimp only
            have h1 := ih p (r - 1) rest { st with dead := insert u st.dead, cost := st.cost + 1 }
            simpa [Nat.add_assoc, Nat.add_comm] using h1
        | cons we rest =>
          rcases we with ⟨w, e⟩; dsimp only
          by_cases hcond : w ∈ V ∧ w ∉ st.used ∧ w ∉ st.dead ∧ r < j ∧ dist w = some (r + 1)
          · simp only [hcond]
            have h1 := ih w (r + 1) ((u, e) :: trail)
              { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
            simpa [Nat.add_assoc, Nat.add_comm] using h1
          · simp only [hcond, ↓reduceIte]
            have h1 := ih u r trail
              { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
            simpa [Nat.add_assoc, Nat.add_comm] using h1

lemma dfsStep_paths_append (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j s fuel u r : ℕ)
    (trail : List (ℕ × ℕ)) (st : DFSState) (acc : List ((ℕ × ℕ) × List ℕ)) :
    let a := dfsStep V T dist j s fuel u r trail { st with paths := st.paths ++ acc }
    let b := dfsStep V T dist j s fuel u r trail st
    a.used = b.used ∧ a.dead = b.dead ∧ a.cursor = b.cursor ∧
      a.paths = b.paths ++ acc ∧ a.cost = b.cost := by
  induction fuel generalizing u r trail st with
  | zero => simp [dfsStep]
  | succ f ih =>
    simp only [dfsStep]
    by_cases hT : u ∈ T
    · simp [hT]
    · simp only [hT, ↓reduceIte]
      by_cases hrj : r = j
      · subst hrj; simp only [↓reduceIte]
        cases trail with
        | nil => dsimp only; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        | cons pe rest =>
          rcases pe with ⟨p, e⟩; dsimp only
          exact ih p (r - 1) rest { st with dead := insert u st.dead, cost := st.cost + 1 }
      · simp only [hrj, ↓reduceIte]
        cases hcur : st.cursor u with
        | nil =>
          dsimp only
          cases trail with
          | nil => dsimp only; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
          | cons pe rest =>
            rcases pe with ⟨p, e⟩; dsimp only
            exact ih p (r - 1) rest { st with dead := insert u st.dead, cost := st.cost + 1 }
        | cons we rest =>
          rcases we with ⟨w, e⟩; dsimp only
          by_cases hcond : w ∈ V ∧ w ∉ st.used ∧ w ∉ st.dead ∧ r < j ∧ dist w = some (r + 1)
          · simp only [hcond]
            exact ih w (r + 1) ((u, e) :: trail)
              { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
          · simp only [hcond, ↓reduceIte]
            exact ih u r trail
              { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }

lemma dfsPot_update_cursor_tail (V : Finset ℕ) (st : DFSState) {u w e : ℕ}
    {rest : List (ℕ × ℕ)} (huV : u ∈ V) (hcur : st.cursor u = (w, e) :: rest) :
    dfsPot V { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 } + 1 =
      dfsPot V st := by
  unfold dfsPot; dsimp only
  have hsum :
      ∑ v ∈ V, (Function.update st.cursor u rest v).length + 1 =
        ∑ v ∈ V, (st.cursor v).length := by
    rw [← Finset.add_sum_erase _ _ huV, ← Finset.add_sum_erase _ (fun v => (st.cursor v).length) huV]
    have hrest : ∑ v ∈ V.erase u, (Function.update st.cursor u rest v).length =
        ∑ v ∈ V.erase u, (st.cursor v).length :=
      Finset.sum_congr rfl fun v hv => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [hrest, Function.update_self, hcur, List.length_cons]; omega
  omega

lemma dfsPot_insert_dead_eq (V : Finset ℕ) (st : DFSState) {u : ℕ}
    (huV : u ∈ V) (huD : u ∉ st.dead) :
    dfsPot V { st with dead := insert u st.dead, cost := st.cost + 1 } + 1 = dfsPot V st := by
  unfold dfsPot; dsimp only
  have hmem : u ∈ V \ st.dead := Finset.mem_sdiff.mpr ⟨huV, huD⟩
  have heq : V \ insert u st.dead = (V \ st.dead).erase u := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]; tauto
  rw [heq, Finset.card_erase_of_mem hmem]
  have hpos : 1 ≤ (V \ st.dead).card := Finset.one_le_card.mpr ⟨u, hmem⟩
  omega

lemma dfsPot_dfsStep_le (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j s fuel u r : ℕ)
    (trail : List (ℕ × ℕ)) (st : DFSState) :
    dfsPot V (dfsStep V T dist j s fuel u r trail st) ≤ dfsPot V st := by
  have hdead_le : ∀ (st0 : DFSState) (x : ℕ),
      dfsPot V { st0 with dead := insert x st0.dead, cost := st0.cost + 1 } ≤ dfsPot V st0 := by
    intro st0 x; unfold dfsPot; dsimp only
    have hsub : V \ insert x st0.dead ⊆ V \ st0.dead := by
      intro y hy
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hy ⊢
      exact ⟨hy.1, hy.2.2⟩
    have := Finset.card_le_card hsub; omega
  have hcur_le : ∀ (st0 : DFSState) (x : ℕ) (we : ℕ × ℕ) (rest : List (ℕ × ℕ)),
      st0.cursor x = we :: rest →
      dfsPot V { st0 with cursor := Function.update st0.cursor x rest, cost := st0.cost + 1 } ≤
        dfsPot V st0 := by
    intro st0 x we rest hcur; unfold dfsPot; dsimp only
    have hsum : ∑ v ∈ V, (Function.update st0.cursor x rest v).length ≤
        ∑ v ∈ V, (st0.cursor v).length := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v = x
      · subst hv; rw [Function.update_self, hcur, List.length_cons]; omega
      · rw [Function.update_of_ne hv]
    omega
  induction fuel generalizing u r trail st with
  | zero => exact le_rfl
  | succ f ih =>
    simp only [dfsStep]
    by_cases hT : u ∈ T
    · simp only [hT, ↓reduceIte, dfsPot]; exact le_rfl
    · simp only [hT, ↓reduceIte]
      by_cases hrj : r = j
      · subst hrj; simp only [↓reduceIte]
        have h1 := hdead_le st u
        cases trail with
        | nil => exact h1
        | cons pe rest =>
          rcases pe with ⟨p, e⟩
          exact le_trans (ih p (r - 1) rest _) h1
      · simp only [hrj, ↓reduceIte]
        cases hcur : st.cursor u with
        | nil =>
          have h1 := hdead_le st u
          cases trail with
          | nil => exact h1
          | cons pe rest =>
            rcases pe with ⟨p, e⟩
            exact le_trans (ih p (r - 1) rest _) h1
        | cons we rest =>
          rcases we with ⟨w, e⟩; dsimp only
          have h1 := hcur_le st u (w, e) rest hcur
          by_cases hcond : w ∈ V ∧ w ∉ st.used ∧ w ∉ st.dead ∧ r < j ∧ dist w = some (r + 1)
          · simp only [hcond]
            exact le_trans (ih w (r + 1) ((u, e) :: trail) _) h1
          · simp only [hcond, ↓reduceIte]
            exact le_trans (ih u r trail _) h1

lemma dfsSources_cost_add (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j fuel : ℕ)
    (srcs : List ℕ) (st : DFSState) (k : ℕ) :
    let a := dfsSources V T dist j fuel srcs { st with cost := st.cost + k }
    let b := dfsSources V T dist j fuel srcs st
    a.used = b.used ∧ a.dead = b.dead ∧ a.cursor = b.cursor ∧
      a.paths = b.paths ∧ a.cost = b.cost + k := by
  induction srcs generalizing st with
  | nil => simp [dfsSources]
  | cons s rest ih =>
    simp only [dfsSources]
    by_cases hsd : s ∈ st.used ∨ s ∈ st.dead
    · simp only [hsd, ↓reduceIte]
      have h1 := ih { st with cost := st.cost + 1 }
      simpa [Nat.add_assoc, Nat.add_comm] using h1
    · simp only [hsd, ↓reduceIte]
      have hstep := dfsStep_cost_add V T dist j s fuel s 0 [] { st with cost := st.cost + 1 } k
      set b1 := dfsStep V T dist j s fuel s 0 [] { st with cost := st.cost + 1 }
      have heq : dfsStep V T dist j s fuel s 0 [] { st with cost := st.cost + k + 1 } =
          { b1 with cost := b1.cost + k } := by
        have hcomm : st.cost + k + 1 = st.cost + 1 + k := by omega
        rw [hcomm]
        rcases hstep with ⟨h1, h2, h3, h4, h5⟩
        cases hA : dfsStep V T dist j s fuel s 0 [] { st with cost := st.cost + 1 + k }
        cases hB : b1
        simp only [hA, hB] at h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5]
      rw [heq]
      exact ih b1

lemma dfsSources_paths_append (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j fuel : ℕ)
    (srcs : List ℕ) (st : DFSState) (acc : List ((ℕ × ℕ) × List ℕ)) :
    let a := dfsSources V T dist j fuel srcs { st with paths := st.paths ++ acc }
    let b := dfsSources V T dist j fuel srcs st
    a.used = b.used ∧ a.dead = b.dead ∧ a.cursor = b.cursor ∧
      a.paths = b.paths ++ acc ∧ a.cost = b.cost := by
  induction srcs generalizing st with
  | nil => simp [dfsSources]
  | cons s rest ih =>
    simp only [dfsSources]
    by_cases hsd : s ∈ st.used ∨ s ∈ st.dead
    · simp only [hsd, ↓reduceIte]
      exact ih { st with cost := st.cost + 1 }
    · simp only [hsd, ↓reduceIte]
      have hstep := dfsStep_paths_append V T dist j s fuel s 0 [] { st with cost := st.cost + 1 } acc
      set b1 := dfsStep V T dist j s fuel s 0 [] { st with cost := st.cost + 1 }
      have heq : dfsStep V T dist j s fuel s 0 []
          { st with paths := st.paths ++ acc, cost := st.cost + 1 } =
          { b1 with paths := b1.paths ++ acc } := by
        rcases hstep with ⟨h1, h2, h3, h4, h5⟩
        cases hA : dfsStep V T dist j s fuel s 0 []
          { st with paths := st.paths ++ acc, cost := st.cost + 1 }
        cases hB : b1
        simp only [hA, hB] at h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5]
      rw [heq]
      exact ih b1

/-! ## 4. Base Sub-Triples (`dfsWriteRet_triple` and `dfsAccept_triple`) -/

lemma dfsWriteRet_triple {w : ℕ} {p : Program}
    {cfgAddr : ℕ} {st0 : State}
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 32 < 2 ^ w) :
    Triple w p (fun st => st = st0) dfsWriteRetStmt
      (retPost fun v st' =>
        v = st0.regs 25 ∧
        st'.mem (cfgAddr + 24) = st0.regs 25 ∧
        st'.mem (cfgAddr + 25) = st0.regs 26 ∧
        st'.mem (cfgAddr + 26) = st0.regs 23 ∧
        st'.mem (cfgAddr + 27) = st0.regs 24 ∧
        st'.mem (cfgAddr + 28) = st0.regs 22 ∧
        (∀ a, a < cfgAddr + 24 ∨ cfgAddr + 29 ≤ a → st'.mem a = st0.mem a))
      (fun _ => 40) := by
  wram_enter; subst st; unfold dfsWriteRetStmt; dsimp only [seqStmts]
  refine runs_seq_store_le (x := cfgAddr + 24) (v := st0.regs 25) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 25) (v := st0.regs 26) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 26) (v := st0.regs 23) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 27) (v := st0.regs 24) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfgAddr + 28) (v := st0.regs 22) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := st0.regs 25) (by eval_expr) ?_ (by wram_cost)
  dsimp only [retPost]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp
  · intro a ha
    have h1 : a ≠ cfgAddr + 24 := by omega
    have h2 : a ≠ cfgAddr + 25 := by omega
    have h3 : a ≠ cfgAddr + 26 := by omega
    have h4 : a ≠ cfgAddr + 27 := by omega
    have h5 : a ≠ cfgAddr + 28 := by omega
    simp [Function.update_of_ne, h1, h2, h3, h4, h5]

end MinCostFlow.ExpanderDecomp
