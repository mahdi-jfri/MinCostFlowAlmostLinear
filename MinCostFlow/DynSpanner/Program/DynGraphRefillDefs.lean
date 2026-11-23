module

public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# In-place refill of a dynamic graph from vertex and edge lists (`DynGraphRefillDefs`)

Defines the deterministic Word-RAM procedures, contracts, and relocatable procedure blocks for
refilling an existing `DynGraphAt` block in place in `O(G_old.n + G_old.m + G_new.n + G_new.m + 1)`
time and zero scratch memory:

* `dgClearStmt` (`dgIdxClear = 0`): clears a `DynGraphAt mem gPtr vCap eCap G_old` into the empty
  graph by walking only the live vertex list `vL` and live edge list `eL` (resetting `vPres`,
  `slotDeg`, `incHead`, `ePres`, and `n = m = 0`).
* `dgFillEmptyFromListsStmt` (`dgIdxFillEmptyFromLists = 1`): populates an already-empty
  `DynGraphAt` from vertex and edge-triple lists disjoint from the graph block (either below or
  above `gPtr`), without requiring `ZeroFrom`.
* `dgRefillFromListsStmt` (`dgIdxRefillFromLists = 2`): composes `dgClear` followed by
  `dgFillEmptyFromLists`.
* `dgRefillProcs bOps bEdge bRefill` (`3` procedures, reusing `dgOpsProcs` and `dgEdgeProcs`) and
  `dgRefillModule b` (`12` procedures, completely self-contained).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices and bodies -/

def dgIdxClear : ℕ := 0
def dgIdxFillEmptyFromLists : ℕ := 1
def dgIdxRefillFromLists : ℕ := 2

/-- Clear a `DynGraphAt` at `[gPtr]` into the empty graph by walking only its live vertex and edge
lists (`O(G.n + G.m + 1)` steps, zero scratch). Preserves `vCap`, `eCap`, and all memory outside
`[gPtr, gPtr + dynGraphSize vCap eCap)`. -/
def dgClearStmt : Stmt :=
  .assign 1 (.load (.reg 0)) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 5 (.bin .add (.reg 0) (.const 4)) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 1)) ;;
  .assign 7 (.bin .add (.reg 5) (.bin .mul (.const 5) (.reg 1))) ;;
  .assign 8 (.bin .add (.reg 5) (.bin .mul (.const 6) (.reg 1))) ;;
  WordRAM.forRange 9 (.const 0) (.reg 3)
    (.assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
     .store (.bin .add (.reg 5) (.reg 10)) (.const 0) ;;
     .store (.bin .add (.reg 7) (.reg 10)) (.const 0) ;;
     .store (.bin .add (.reg 8) (.reg 10)) (.const 0)) ;;
  .assign 5 (.bin .add (.reg 5) (.bin .mul (.const 7) (.reg 1))) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 2)) ;;
  WordRAM.forRange 9 (.const 0) (.reg 4)
    (.assign 10 (.load (.bin .add (.reg 6) (.reg 9))) ;;
     .store (.bin .add (.reg 5) (.reg 10)) (.const 0)) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.const 0) ;;
  .ret (.reg 0)

/-- Populate an empty `DynGraphAt` at `gPtr` from a vertex list (`V_ptr`, length `V_len`) and an
edge-triple list (`E_ptr`, `E_len` triples `[e, u, v]`): `[gPtr, V_len, V_ptr, E_len, E_ptr]`,
returning `gPtr`. Unlike `dgInitFromListsStmt`, requires an empty `DynGraphAt` instead of
`ZeroFrom`, and allows the input lists to lie either below or above the graph block. -/
def dgFillEmptyFromListsStmt (bOps bEdge : ℕ) : Stmt :=
  WordRAM.forRange 5 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 2) (.reg 5))) ;;
     .call 7 (bOps + dgIdxAddVertex) [.reg 0, .reg 6]) ;;
  WordRAM.forRange 5 (.const 0) (.reg 3)
    (.assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 5))) ;;
     .assign 7 (.load (.reg 6)) ;;
     .assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
     .assign 9 (.load (.bin .add (.reg 6) (.const 2))) ;;
     .call 10 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 7, .reg 8, .reg 9]) ;;
  .ret (.reg 0)

/-- Refill an existing `DynGraphAt` at `gPtr` in place from vertex and edge-triple lists:
`[gPtr, V_len, V_ptr, E_len, E_ptr]`, returning `gPtr`. Clears the old graph via `clearProc`, then
inserts the new vertices and edges via `fillProc`. -/
def dgRefillFromListsStmt (clearProc fillProc : ℕ) : Stmt :=
  .call 5 clearProc [.reg 0] ;;
  .call 6 fillProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .ret (.reg 6)

/-- Relocatable 3-procedure refill block sharing `dgOpsProcs` at `bOps` and `dgEdgeProcs` at
`bEdge`:
- `bRefill + 0`: `dgClearStmt`
- `bRefill + 1`: `dgFillEmptyFromListsStmt bOps bEdge`
- `bRefill + 2`: `dgRefillFromListsStmt (bRefill + 0) (bRefill + 1)`. -/
def dgRefillProcs (bOps bEdge bRefill : ℕ) : List Stmt :=
  [ dgClearStmt
  , dgFillEmptyFromListsStmt bOps bEdge
  , dgRefillFromListsStmt (bRefill + dgIdxClear) (bRefill + dgIdxFillEmptyFromLists) ]

lemma dgRefillProcs_length (bOps bEdge bRefill : ℕ) :
    (dgRefillProcs bOps bEdge bRefill).length = 3 := rfl

lemma dgClearStmt_noRand : dgClearStmt.NoRand := by
  simp [dgClearStmt, forRange, forUp, Stmt.NoRand]

lemma dgFillEmptyFromListsStmt_noRand (bOps bEdge : ℕ) :
    (dgFillEmptyFromListsStmt bOps bEdge).NoRand := by
  simp [dgFillEmptyFromListsStmt, forRange, forUp, Stmt.NoRand]

lemma dgRefillFromListsStmt_noRand (clearProc fillProc : ℕ) :
    (dgRefillFromListsStmt clearProc fillProc).NoRand := by
  simp [dgRefillFromListsStmt, Stmt.NoRand]

lemma dgRefillProcs_noRand (bOps bEdge bRefill : ℕ) :
    ∀ s ∈ dgRefillProcs bOps bEdge bRefill, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact dgClearStmt_noRand
  rcases List.mem_cons.mp hs with rfl | hs
  · exact dgFillEmptyFromListsStmt_noRand _ _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact dgRefillFromListsStmt_noRand _ _
  cases hs

/-- Self-contained relocatable 12-procedure refill module starting at `b`:
- `b + 0 .. b + 6`: `dgOpsProcs`
- `b + 7 .. b + 8`: `dgEdgeProcs b`
- `b + 9 .. b + 11`: `dgRefillProcs b (b + 7) (b + 9)` (entry `dgRefillFromLists` at `b + 11`). -/
def dgRefillModule (b : ℕ) : List Stmt :=
  dgOpsProcs ++ dgEdgeProcs b ++ dgRefillProcs b (b + 7) (b + 9)

lemma dgRefillModule_length (b : ℕ) : (dgRefillModule b).length = 12 := rfl

lemma dgRefillModule_noRand (b : ℕ) : ∀ s ∈ dgRefillModule b, s.NoRand := by
  intro s hs
  simp only [dgRefillModule, List.mem_append] at hs
  rcases hs with (h | h) | h
  · exact dgOpsProcs_noRand s h
  · exact dgEdgeProcs_noRand b s h
  · exact dgRefillProcs_noRand b (b + 7) (b + 9) s h

/-! ## Cost bounds and contracts -/

/-- Exact empty `MGraph` produced by `dgClearStmt`. -/
def dgEmptyGraph : MGraph :=
  { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }

/-- Step cost bound for `dgClearStmt` on a graph with `n` vertices and `m` edges. -/
def dgClearCost (n m : ℕ) : ℕ := 40 * n + 30 * m + 120

/-- Step cost bound for `dgFillEmptyFromListsStmt` on lists of lengths `V_len` and `E_len`. -/
def dgFillEmptyFromListsCost (V_len E_len : ℕ) : ℕ := 130 * V_len + 490 * E_len + 50

/-- Step cost bound for `dgRefillFromListsStmt`. -/
def dgRefillFromListsCost (nOld mOld V_len E_len : ℕ) : ℕ :=
  40 * nOld + 30 * mOld + 130 * V_len + 490 * E_len + 200

/-- Contract for `dgClearStmt` (`[gPtr]`): resets `DynGraphAt mem gPtr vCap eCap G` to the empty
graph in `O(G.n + G.m + 1)` steps, preserving all memory outside the graph block. -/
def dgClearContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr, args = [gPtr] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr, args = [gPtr] ∧ ret = gPtr ∧
    DynGraphAt mem' gPtr vCap eCap dgEmptyGraph ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost args mem := dgClearCost (mem (args.getD 0 0 + dgNOff)) (mem (args.getD 0 0 + dgMOff))

/-- Contract for `dgFillEmptyFromListsStmt` (`[gPtr, V_len, V_ptr, E_len, E_ptr]`): populates an
empty `DynGraphAt` at `gPtr` from disjoint vertex and edge-triple lists, preserving all memory
outside the graph block. -/
def dgFillEmptyFromListsContract (w vCap eCap : ℕ) (G : MGraph) (vL : List ℕ)
    (eEdges : List (ℕ × ℕ × ℕ)) : Contract where
  pre args mem := ∃ gPtr V_len V_ptr E_len E_ptr,
    args = [gPtr, V_len, V_ptr, E_len, E_ptr] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    DynGraphAt mem gPtr vCap eCap dgEmptyGraph ∧
    G.IsValid ∧ (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    vL.length = V_len ∧ ListAt mem V_ptr vL ∧ (∀ v, v ∈ vL ↔ v ∈ G.V) ∧
    V_ptr + V_len < 2 ^ w ∧
    (∀ i < V_len, V_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ V_ptr + i) ∧
    eEdges.length = E_len ∧ (eEdges.map Prod.fst).Nodup ∧
    (∀ i (hi : i < eEdges.length),
      mem (E_ptr + 3 * i) = eEdges[i].1 ∧
      mem (E_ptr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem (E_ptr + 3 * i + 2) = eEdges[i].2.2) ∧
    (∀ t ∈ eEdges, t.1 ∈ G.E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1) ∧
    (∀ e ∈ G.E, ∃ t ∈ eEdges, t.1 = e) ∧
    E_ptr + 3 * E_len < 2 ^ w ∧
    (∀ i < 3 * E_len, E_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ E_ptr + i)
  post args mem ret mem' := ∃ gPtr V_len V_ptr E_len E_ptr,
    args = [gPtr, V_len, V_ptr, E_len, E_ptr] ∧ ret = gPtr ∧
    DynGraphAt mem' gPtr vCap eCap G ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost args _ := dgFillEmptyFromListsCost (args.getD 1 0) (args.getD 3 0)

/-- Contract for `dgRefillFromListsStmt` (`[gPtr, V_len, V_ptr, E_len, E_ptr]`): replaces `G_old`
at `gPtr` with `G_new` given by disjoint vertex and edge-triple lists, using zero scratch and
preserving all memory outside `[gPtr, gPtr + dynGraphSize vCap eCap)`. -/
def dgRefillFromListsContract (w vCap eCap : ℕ) (G_old G_new : MGraph) (vL : List ℕ)
    (eEdges : List (ℕ × ℕ × ℕ)) : Contract where
  pre args mem := ∃ gPtr V_len V_ptr E_len E_ptr,
    args = [gPtr, V_len, V_ptr, E_len, E_ptr] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    DynGraphAt mem gPtr vCap eCap G_old ∧
    G_new.IsValid ∧ (∀ v ∈ G_new.V, v < vCap) ∧ (∀ e ∈ G_new.E, e < eCap) ∧
    vL.length = V_len ∧ ListAt mem V_ptr vL ∧ (∀ v, v ∈ vL ↔ v ∈ G_new.V) ∧
    V_ptr + V_len < 2 ^ w ∧
    (∀ i < V_len, V_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ V_ptr + i) ∧
    eEdges.length = E_len ∧ (eEdges.map Prod.fst).Nodup ∧
    (∀ i (hi : i < eEdges.length),
      mem (E_ptr + 3 * i) = eEdges[i].1 ∧
      mem (E_ptr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem (E_ptr + 3 * i + 2) = eEdges[i].2.2) ∧
    (∀ t ∈ eEdges, t.1 ∈ G_new.E ∧ t.2.1 = G_new.tail t.1 ∧ t.2.2 = G_new.head t.1) ∧
    (∀ e ∈ G_new.E, ∃ t ∈ eEdges, t.1 = e) ∧
    E_ptr + 3 * E_len < 2 ^ w ∧
    (∀ i < 3 * E_len, E_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ E_ptr + i)
  post args mem ret mem' := ∃ gPtr V_len V_ptr E_len E_ptr,
    args = [gPtr, V_len, V_ptr, E_len, E_ptr] ∧ ret = gPtr ∧
    DynGraphAt mem' gPtr vCap eCap G_new ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost args mem :=
    dgRefillFromListsCost (mem (args.getD 0 0 + dgNOff)) (mem (args.getD 0 0 + dgMOff))
      (args.getD 1 0) (args.getD 3 0)

end

public section

/-- When the input vertex list `vL` has no duplicates, `dgRefillFromListsContract.cost` is at most
`490 * (G_old.n + G_old.m + G_new.n + G_new.m + 1)`. -/
theorem dgRefillFromLists_cost_le {w vCap eCap : ℕ} {G_old G_new : MGraph} {vL : List ℕ}
    {eEdges : List (ℕ × ℕ × ℕ)} {args : List ℕ} {mem : ℕ → ℕ}
    (hpre : (dgRefillFromListsContract w vCap eCap G_old G_new vL eEdges).pre args mem)
    (hvNd : vL.Nodup) :
    (dgRefillFromListsContract w vCap eCap G_old G_new vL eEdges).cost args mem ≤
      490 * (G_old.n + G_old.m + G_new.n + G_new.m + 1) := by
  rcases hpre with ⟨gPtr, V_len, V_ptr, E_len, E_ptr, rfl, _, _, hOld, _, _, _,
    hvLen, _, hvMem, _, _, heLen, heNd, _, heSpec, heCov, _, _⟩
  have hVlen : V_len = G_new.n := by
    rw [← hvLen, ← List.toFinset_card_of_nodup hvNd]
    congr 1
    ext v
    simpa using hvMem v
  have hElen : E_len = G_new.m := by
    have hmapLen : (eEdges.map Prod.fst).length = E_len := by simp [heLen]
    rw [← hmapLen, ← List.toFinset_card_of_nodup heNd]
    congr 1
    ext e
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact (heSpec t ht).1
    · intro he; exact heCov e he
  have hOldN : mem (gPtr + dgNOff) = G_old.n := hOld.2.2.2.2.2.1
  have hOldM : mem (gPtr + dgMOff) = G_old.m := hOld.2.2.2.2.2.2.1
  simp only [dgRefillFromListsContract, dgRefillFromListsCost, List.getD_cons_zero,
    List.getD_cons_succ, hOldN, hOldM, hVlen, hElen]
  omega

end

end MinCostFlow.DynSpanner.Program
