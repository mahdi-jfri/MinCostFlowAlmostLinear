module

public import MinCostFlow.DynSpanner.Program.DynGraphSplit
public import MinCostFlow.DynSpanner.Walks
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.TakeDrop
import MinCostFlow.DynSpanner.Program.DynGraphDelete
import MinCostFlow.DynSpanner.Program.DynGraphInsert

/-!
# Dynamic graph update, batch, and initialization definitions (`DynGraphBatch`)

This file extends `DynGraphLayout`, `DynGraphOps`, `DynGraphEdges`, and `DynGraphSplit` with:

* Frame and compact-existence lemmas for `UpdateAt`, `BatchBodyAt`, and `BatchAt`
  (`exists_small_batchAt`), plus `DynGraphAt.congr_ends` and subgraph restriction helpers
  (`dgBatchTarget`, `dgBatchTarget_preserves_subgraph`).
* The Word-RAM batch/initialization procedures `dgBatchProcs` (`dgIdxApplyUpdate = 0`,
  `dgIdxApplyBatch = 1`, `dgIdxInitFromLists = 2`) and the complete bundled library `dgProcs` (`15`
  procedures).
* Full verification of `dgApplyUpdate_meetsContract` and `dgApplyBatch_meetsContract` covering both
  direct updates on `G` (`allowInsert ≠ 0`) and restricted updates on any subgraph `H ⊆ G` sharing
  `H.V = G.V` (`allowInsert = 0`), running in `O(totalWords + 1)` (hence `O(G.batchEnc U + 1)`
  for `SmallBatchAt`) time.

The verification of `dgInitFromLists_meetsContract` lives in
`MinCostFlow.DynSpanner.Program.DynGraphInit`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices and bodies -/

def dgIdxApplyUpdate : ℕ := 0
def dgIdxApplyBatch : ℕ := 1
def dgIdxInitFromLists : ℕ := 2

/-- Length (in words) of the encoded update starting at `updPtr` in `mem`. -/
def dgUpdateMemLen (mem : ℕ → ℕ) (updPtr : ℕ) : ℕ :=
  if mem updPtr = 0 then 4 else if mem updPtr = 1 then 2
  else 5 + mem (updPtr + 3) + mem (updPtr + 4)

/-- Capacity bounds needed when applying updates to `DynGraphAt mem gPtr vCap eCap G`. -/
def UpdateWithinCaps (vCap eCap : ℕ) : Update → Prop
  | .insert e _ _ => e < eCap
  | .delete _ => True
  | .split _ v' _ _ => v' < vCap

/-- Every update in batch `U` respects `(vCap, eCap)`. -/
def BatchWithinCaps (vCap eCap : ℕ) (U : List Update) : Prop :=
  ∀ u ∈ U, UpdateWithinCaps vCap eCap u

/-- Uniform target graph step for `dgApplyUpdate`: when `allowInsert = 0`, applies
`restrictUpdate u H` to `H`; otherwise applies `u` directly to `H`. -/
def dgBatchTarget (allowInsert : ℕ) (H : MGraph) (u : Update) : MGraph :=
  if allowInsert = 0 then H.applyBatch (restrictUpdate u H) else H.applyUpdate u

/-- Apply one encoded update at `updPtr` to `DynGraphAt` at `gPtr` (`[gPtr, updPtr, allowInsert]`),
returning the number of words consumed (`4`, `2`, or `4 + k`). When `allowInsert = 0`, edge
insertions (`tag = 0`) are skipped as no-ops so the same procedure updates subgraphs `H ⊆ G`. -/
def dgApplyUpdateStmt (bEdge bSplit : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (.assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
     .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;;
     .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;;
     .cond (.reg 2)
       (.call 7 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 4, .reg 5, .reg 6])
       .nop ;;
     .ret (.const 4))
    (.cond (.bin .eq (.reg 3) (.const 1))
      (.assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
       .call 7 (bEdge + dgIdxDeleteEdge) [.reg 0, .reg 4] ;;
       .ret (.const 2))
      (.assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
       .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;;
       .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;;
       .assign 7 (.load (.bin .add (.reg 1) (.const 4))) ;;
       .call 8 (bSplit + dgIdxApplySplit)
         [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .bin .add (.reg 1) (.const 5)] ;;
       .ret (.bin .add (.bin .add (.const 5) (.reg 6)) (.reg 7))))

/-- Apply an encoded batch at `batchPtr` (`[gPtr, batchPtr, allowInsert]`) in `O(totalWords + 1)`
time. -/
def dgApplyBatchStmt (bBatch : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.const 0) ;;
  .assign 5 (.bin .add (.reg 1) (.const 1)) ;;
  .loop (.bin .lt (.reg 4) (.reg 3))
    (.call 6 (bBatch + dgIdxApplyUpdate) [.reg 0, .reg 5, .reg 2] ;;
     .assign 5 (.bin .add (.reg 5) (.reg 6)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .ret (.const 0)

/-- Initialize a `DynGraphAt` from a vertex list (`V_ptr`, length `V_len`) and an edge-triple list
(`E_ptr`, `E_len` triples `[e, u, v]`): `[gPtr, vCap, eCap, V_len, V_ptr, E_len, E_ptr]`,
returning `gPtr`. Assumes `ZeroFrom mem gPtr`. -/
def dgInitFromListsStmt (bOps bEdge : ℕ) : Stmt :=
  .call 7 (bOps + dgIdxInitEmpty) [.reg 0, .reg 1, .reg 2] ;;
  WordRAM.forRange 7 (.const 0) (.reg 3)
    (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .call 9 (bOps + dgIdxAddVertex) [.reg 0, .reg 8]) ;;
  WordRAM.forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 7))) ;;
     .assign 9 (.load (.reg 8)) ;;
     .assign 10 (.load (.bin .add (.reg 8) (.const 1))) ;;
     .assign 11 (.load (.bin .add (.reg 8) (.const 2))) ;;
     .call 12 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 9, .reg 10, .reg 11]) ;;
  .ret (.reg 0)

/-- Dynamic-graph update, batch, and initialization procedures (`0..2`). -/
def dgBatchProcs (bOps bEdge bSplit bBatch : ℕ) : List Stmt :=
  [dgApplyUpdateStmt bEdge bSplit, dgApplyBatchStmt bBatch, dgInitFromListsStmt bOps bEdge]

lemma dgBatchProcs_length (bOps bEdge bSplit bBatch : ℕ) :
    (dgBatchProcs bOps bEdge bSplit bBatch).length = 3 := rfl

lemma dgBatchProcs_noRand (bOps bEdge bSplit bBatch : ℕ) :
    ∀ s ∈ dgBatchProcs bOps bEdge bSplit bBatch, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

def dgBaseOps : ℕ := 0
def dgBaseEdge : ℕ := 7
def dgBaseSplit : ℕ := 9
def dgBaseBatch : ℕ := 12

/-- Complete dynamic-graph procedure library (`15` deterministic procedures). -/
def dgProcs : List Stmt :=
  dgOpsProcs ++
  dgEdgeProcs dgBaseOps ++
  dgSplitProcs dgBaseOps dgBaseSplit ++
  dgBatchProcs dgBaseOps dgBaseEdge dgBaseSplit dgBaseBatch

lemma dgProcs_length : dgProcs.length = 15 := rfl

lemma dgProcs_noRand : ∀ s ∈ dgProcs, s.NoRand := by
  intro s hs
  simp only [dgProcs, List.mem_append] at hs
  rcases hs with ((h | h) | h) | h
  · exact dgOpsProcs_noRand s h
  · exact dgEdgeProcs_noRand dgBaseOps s h
  · exact dgSplitProcs_noRand dgBaseOps dgBaseSplit s h
  · exact dgBatchProcs_noRand dgBaseOps dgBaseEdge dgBaseSplit dgBaseBatch s h

/-! ## Contracts -/

/-- Contract for `dgApplyUpdateStmt` (`[gPtr, updPtr, allowInsert]`). -/
def dgApplyUpdateContract (w vCap eCap : ℕ) (G H : MGraph) (u : Update) (len : ℕ) :
    Contract where
  pre args mem := ∃ gPtr updPtr allowInsert,
    args = [gPtr, updPtr, allowInsert] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ updPtr + len < 2 ^ w ∧
    (∀ i < len, updPtr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ updPtr + i) ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    UpdateAt mem updPtr G u len ∧
    G.UpdateIsValid u ∧ UpdateWithinCaps vCap eCap u ∧
    DynGraphAt mem gPtr vCap eCap H ∧
    ((allowInsert ≠ 0 ∧ H = G) ∨ (allowInsert = 0 ∧ G.IsSubgraph H ∧ H.V = G.V))
  post args mem ret mem' := ∃ gPtr updPtr allowInsert,
    args = [gPtr, updPtr, allowInsert] ∧ ret = len ∧
    DynGraphAt mem' gPtr vCap eCap (dgBatchTarget allowInsert H u) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost args mem := 640 * dgUpdateMemLen mem (args[1]?.getD 0)

/-- Contract for `dgApplyBatchStmt` (`[gPtr, batchPtr, allowInsert]`). -/
def dgApplyBatchContract (w vCap eCap : ℕ) (G H : MGraph) (U : List Update) (totalWords : ℕ) :
    Contract where
  pre args mem := ∃ gPtr batchPtr allowInsert,
    args = [gPtr, batchPtr, allowInsert] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ batchPtr + totalWords < 2 ^ w ∧
    (∀ i < totalWords, batchPtr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ batchPtr + i) ∧
    (∀ i < totalWords, mem (batchPtr + i) < 2 ^ w) ∧
    BatchAt mem batchPtr G U totalWords ∧
    G.BatchIsValid U ∧ BatchWithinCaps vCap eCap U ∧
    DynGraphAt mem gPtr vCap eCap H ∧
    ((allowInsert ≠ 0 ∧ H = G) ∨ (allowInsert = 0 ∧ G.IsSubgraph H ∧ H.V = G.V))
  post args mem ret mem' := ∃ gPtr batchPtr allowInsert,
    args = [gPtr, batchPtr, allowInsert] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap (U.foldl (dgBatchTarget allowInsert) H) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 670 * totalWords + 30

/-- Contract for `dgInitFromListsStmt` (`[gPtr, vCap, eCap, V_len, V_ptr, E_len, E_ptr]`). -/
def dgInitFromListsContract (w vCap eCap : ℕ) (G : MGraph) (vL : List ℕ)
    (eEdges : List (ℕ × ℕ × ℕ)) : Contract where
  pre args mem := ∃ gPtr V_len V_ptr E_len E_ptr,
    args = [gPtr, vCap, eCap, V_len, V_ptr, E_len, E_ptr] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ ZeroFrom mem gPtr ∧
    G.IsValid ∧ (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    vL.length = V_len ∧ ListAt mem V_ptr vL ∧ (∀ v, v ∈ vL ↔ v ∈ G.V) ∧
    (∀ i < V_len, V_ptr + i < gPtr) ∧
    eEdges.length = E_len ∧ (eEdges.map Prod.fst).Nodup ∧
    (∀ i (hi : i < eEdges.length),
      mem (E_ptr + 3 * i) = eEdges[i].1 ∧
      mem (E_ptr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem (E_ptr + 3 * i + 2) = eEdges[i].2.2) ∧
    (∀ t ∈ eEdges, t.1 ∈ G.E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1) ∧
    (∀ e ∈ G.E, ∃ t ∈ eEdges, t.1 = e) ∧
    (∀ i < 3 * E_len, E_ptr + i < gPtr)
  post args mem ret mem' := ∃ gPtr V_len V_ptr E_len E_ptr,
    args = [gPtr, vCap, eCap, V_len, V_ptr, E_len, E_ptr] ∧ ret = gPtr ∧
    DynGraphAt mem' gPtr vCap eCap G ∧
    (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr) ∧
    ZeroFrom mem' (gPtr + dynGraphSize vCap eCap)
  cost args _ := 130 * (args[3]?.getD 0) + 490 * (args[5]?.getD 0) + 100

end

/-! ## Structural, batch, and frame lemmas -/

public section

lemma dgProcs_hasOps {p : Program} (hp : p.HasAt 0 dgProcs) :
    p.HasAt dgBaseOps dgOpsProcs := by
  intro i hi
  have hlt : dgBaseOps + i < dgProcs.length := by
    have : dgOpsProcs.length = 7 := dgOpsProcs_length
    have : dgProcs.length = 15 := dgProcs_length
    dsimp [dgBaseOps]; omega
  simpa [dgProcs, dgBaseOps, List.getElem_append_left (show i < dgOpsProcs.length from hi)] using
    hp (dgBaseOps + i) hlt

lemma dgProcs_hasEdge {p : Program} (hp : p.HasAt 0 dgProcs) :
    p.HasAt dgBaseEdge (dgEdgeProcs dgBaseOps) := by
  intro i hi
  have hl1 : dgOpsProcs.length = 7 := dgOpsProcs_length
  have hl2 : (dgEdgeProcs dgBaseOps).length = 2 := dgEdgeProcs_length _
  have hlt : dgBaseEdge + i < dgProcs.length := by
    have : dgProcs.length = 15 := dgProcs_length
    dsimp [dgBaseEdge]; omega
  have h := hp (dgBaseEdge + i) hlt
  simp only [Nat.zero_add, dgBaseEdge] at h ⊢
  rw [h]; congr 1
  simp only [dgProcs, List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
  simp [hl1]

lemma dgProcs_hasSplit {p : Program} (hp : p.HasAt 0 dgProcs) :
    p.HasAt dgBaseSplit (dgSplitProcs dgBaseOps dgBaseSplit) := by
  intro i hi
  dsimp only [dgBaseOps, dgBaseEdge, dgBaseSplit] at hi ⊢
  have hl1 : dgOpsProcs.length = 7 := dgOpsProcs_length
  have hl2 : (dgEdgeProcs 0).length = 2 := dgEdgeProcs_length 0
  have hl3 : (dgSplitProcs 0 9).length = 3 := dgSplitProcs_length 0 9
  have hlt : 9 + i < dgProcs.length := by
    have : dgProcs.length = 15 := dgProcs_length
    omega
  have h := hp (9 + i) hlt
  simp only [Nat.zero_add] at h
  rw [h]; congr 1
  simp only [dgProcs, dgBaseOps, dgBaseEdge, dgBaseSplit, List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
    List.getElem_append_left (by omega)]
  simp only [hl1, hl2, show 9 + i - 7 - 2 = i by omega]

lemma dgProcs_hasBatch {p : Program} (hp : p.HasAt 0 dgProcs) :
    p.HasAt dgBaseBatch (dgBatchProcs dgBaseOps dgBaseEdge dgBaseSplit dgBaseBatch) := by
  intro i hi
  dsimp only [dgBaseOps, dgBaseEdge, dgBaseSplit, dgBaseBatch] at hi ⊢
  have hl1 : dgOpsProcs.length = 7 := dgOpsProcs_length
  have hl2 : (dgEdgeProcs 0).length = 2 := dgEdgeProcs_length 0
  have hl3 : (dgSplitProcs 0 9).length = 3 := dgSplitProcs_length 0 9
  have hl4 : (dgBatchProcs 0 7 9 12).length = 3 := by simp [dgBatchProcs]
  have hlt : 12 + i < dgProcs.length := by
    have : dgProcs.length = 15 := dgProcs_length
    omega
  have h := hp (12 + i) hlt
  simp only [Nat.zero_add] at h
  rw [h]; congr 1
  simp only [dgProcs, dgBaseOps, dgBaseEdge, dgBaseSplit, dgBaseBatch, List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
    List.getElem_append_right (by omega)]
  simp only [hl1, hl2, hl3, show 12 + i - 7 - 2 - 3 = i by omega]

lemma UpdateAt.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (hu : UpdateAt mem a G u len)
    (hagree : ∀ i < len, mem' (a + i) = mem (a + i)) :
    UpdateAt mem' a G u len := by
  cases u with
  | insert e x y =>
    rcases hu with ⟨rfl, hat⟩
    exact ⟨rfl, fun i hi => (hagree i (by simpa using hi)).trans (hat i hi)⟩
  | delete e =>
    rcases hu with ⟨rfl, hat⟩
    exact ⟨rfl, fun i hi => (hagree i (by simpa using hi)).trans (hat i hi)⟩
  | split v v' St Sh =>
    rcases hu with ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, hat⟩ | ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, hat⟩
    · exact Or.inl ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, fun i hi =>
        (hagree i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)).trans (hat i hi)⟩
    · exact Or.inr ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, fun i hi =>
        (hagree i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)).trans (hat i hi)⟩

private lemma UpdateAt.shift {mem mem' : ℕ → ℕ} {a b : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (hu : UpdateAt mem a G u len)
    (hagree : ∀ i < len, mem' (b + i) = mem (a + i)) :
    UpdateAt mem' b G u len := by
  cases u with
  | insert e x y =>
    rcases hu with ⟨rfl, hat⟩
    exact ⟨rfl, fun i hi => (hagree i (by simpa using hi)).trans (hat i hi)⟩
  | delete e =>
    rcases hu with ⟨rfl, hat⟩
    exact ⟨rfl, fun i hi => (hagree i (by simpa using hi)).trans (hat i hi)⟩
  | split v v' St Sh =>
    rcases hu with ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, hat⟩ | ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, hat⟩
    · exact Or.inl ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, fun i hi =>
        (hagree i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)).trans (hat i hi)⟩
    · exact Or.inr ⟨Lt, Lh, ht, hh, hmt, hmh, rfl, fun i hi =>
        (hagree i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)).trans (hat i hi)⟩

private lemma BatchBodyAt.shift {mem mem' : ℕ → ℕ} :
    ∀ {U : List Update} {a b : ℕ} {G : MGraph} {totalWords : ℕ},
      BatchBodyAt mem a G U totalWords →
      (∀ i < totalWords, mem' (b + i) = mem (a + i)) →
      BatchBodyAt mem' b G U totalWords
  | [], _, _, _, _, hB, _ => hB
  | u :: us, a, b, G, totalWords, ⟨len, hlen, hu, hrest⟩, hagree => by
    refine ⟨len, hlen, hu.shift fun i hi => hagree i (hi.trans_le hlen), ?_⟩
    exact BatchBodyAt.shift hrest fun i hi => by
      simpa [Nat.add_assoc] using hagree (len + i) (by omega)

lemma BatchBodyAt.of_agree {mem mem' : ℕ → ℕ} :
    ∀ {U : List Update} {a : ℕ} {G : MGraph} {totalWords : ℕ},
      BatchBodyAt mem a G U totalWords →
      (∀ i < totalWords, mem' (a + i) = mem (a + i)) →
      BatchBodyAt mem' a G U totalWords
  | [], _, _, _, hB, _ => hB
  | u :: us, a, G, totalWords, ⟨len, hlen, hu, hrest⟩, hagree => by
    refine ⟨len, hlen, hu.of_agree fun i hi => hagree i (hi.trans_le hlen), ?_⟩
    exact BatchBodyAt.of_agree hrest fun i hi => by
      simpa [Nat.add_assoc] using hagree (len + i) (by omega)

lemma BatchAt.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {totalWords : ℕ}
    (hB : BatchAt mem a G U totalWords)
    (hagree : ∀ i < totalWords, mem' (a + i) = mem (a + i)) :
    BatchAt mem' a G U totalWords := by
  rcases hB with ⟨hpos, hlen, hbody⟩
  refine ⟨hpos, (hagree 0 (by omega)).trans hlen, ?_⟩
  exact hbody.of_agree fun i hi => by
    simpa [Nat.add_assoc] using hagree (1 + i) (by omega)

lemma UpdateAt.ge_two {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (hu : UpdateAt mem a G u len) : 2 ≤ len := by
  cases u with
  | insert _ _ _ => rcases hu with ⟨rfl, _⟩; omega
  | delete _ => rcases hu with ⟨rfl, _⟩; omega
  | split _ _ _ _ =>
    rcases hu with ⟨Lt, Lh, _, _, _, _, rfl, _⟩ | ⟨Lt, Lh, _, _, _, _, rfl, _⟩ <;> omega

lemma BatchBodyAt.two_mul_length_le {mem : ℕ → ℕ} :
    ∀ {U : List Update} {a : ℕ} {G : MGraph} {totalWords : ℕ},
      BatchBodyAt mem a G U totalWords → 2 * U.length ≤ totalWords
  | [], _, _, _, _ => by simp
  | u :: us, a, G, totalWords, ⟨len, hlen, hu, hrest⟩ => by
    have h2 := hu.ge_two
    have ih := BatchBodyAt.two_mul_length_le hrest
    simp only [List.length_cons]
    omega

lemma exists_small_batchBodyAt :
    ∀ {U : List Update} {G : MGraph},
      G.BatchIsValid U →
      ∃ totalWords mem, BatchBodyAt mem 0 G U totalWords ∧ totalWords ≤ 5 * G.batchEnc U
  | [], _, _ => ⟨0, fun _ => 0, rfl, Nat.zero_le _⟩
  | u :: us, G, ⟨hu, hus⟩ => by
    rcases exists_small_updateAt hu with ⟨len, memU, hU_at, hU_le⟩
    rcases exists_small_batchBodyAt hus with ⟨twRest, memRest, hRest_at, hRest_le⟩
    let mem : ℕ → ℕ := fun i => if i < len then memU i else memRest (i - len)
    refine ⟨len + twRest, mem, ⟨len, Nat.le_add_right _ _, ?_, ?_⟩, ?_⟩
    · exact hU_at.of_agree fun i hi => by simp [mem, hi]
    · rw [Nat.zero_add, Nat.add_sub_cancel_left]
      exact hRest_at.shift fun i hi => by
        dsimp only [mem]
        split_ifs
        · omega
        · congr 1; omega
    · have hpos := updateEnc_pos G u
      simp only [MGraph.batchEnc]
      omega

/-- Every valid batch of updates admits a compact Word-RAM encoding `SmallBatchAt`. -/
lemma exists_small_batchAt {G : MGraph} {U : List Update} (hU : G.BatchIsValid U) :
    ∃ totalWords mem, SmallBatchAt mem 0 G U totalWords := by
  rcases exists_small_batchBodyAt hU with ⟨twBody, memBody, hBody, hle⟩
  let mem : ℕ → ℕ := fun i => if i = 0 then U.length else memBody (i - 1)
  refine ⟨1 + twBody, mem, ⟨by omega, by simp [mem], ?_⟩, by omega⟩
  rw [Nat.zero_add, Nat.add_sub_cancel_left]
  exact hBody.shift fun i hi => by
    dsimp only [mem]
    split_ifs
    · omega
    · congr 1; omega

lemma DynGraphAt.congr_ends {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G₁ G₂ : MGraph}
    (hV : G₁.V = G₂.V) (hE : G₁.E = G₂.E)
    (hEnds : ∀ e ∈ G₁.E, G₁.tail e = G₂.tail e ∧ G₁.head e = G₂.head e)
    (hG₁ : DynGraphAt mem a vCap eCap G₁) :
    DynGraphAt mem a vCap eCap G₂ := by
  rcases hG₁ with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti, hite, hep, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩,
    hets_ehs, ⟨incL, hincL⟩⟩
  have hn : G₁.n = G₂.n := congrArg Finset.card hV
  have hm : G₁.m = G₂.m := congrArg Finset.card hE
  refine ⟨?_, ?_, ?_, h0, h1, hn ▸ h2, hm ▸ h3, ?_, ⟨vL, hn ▸ hvL_len, hvL_nd, ?_, hvL_at,
    hvL_pos⟩, ?_, ?_, ?_, ⟨eL, hm ▸ heL_len, heL_nd, ?_, heL_at, heL_pos⟩, ?_, ⟨incL, fun s hs => ?_⟩⟩
  · intro e he
    have he1 : e ∈ G₁.E := hE ▸ he
    rcases hEnds e he1 with ⟨ht, hh⟩
    rcases hval e he1 with ⟨htV, hhV⟩
    exact ⟨hV ▸ ht ▸ htV, hV ▸ hh ▸ hhV⟩
  · intro v hv; exact hvCap v (hV ▸ hv)
  · intro e he; exact heCap e (hE ▸ he)
  · intro v hv; simpa [hV] using hvp v hv
  · intro v; simpa [hV] using hvL_mem v
  · intro v hv; simpa [hV] using heti v (hV ▸ hv)
  · intro s hs; simpa [hV] using hite s (hV ▸ hs)
  · intro e he; simpa [hE] using hep e he
  · intro e; simpa [hE] using heL_mem e
  · intro e he
    have he1 : e ∈ G₁.E := hE ▸ he
    rcases hEnds e he1 with ⟨ht, hh⟩
    simpa [ht, hh] using hets_ehs e he1
  · rcases hincL s hs with ⟨hdll, hdeg, hmem⟩
    refine ⟨hdll, hdeg, fun h => ?_⟩
    simpa [hE] using hmem h

lemma dgBatchTarget_preserves_subgraph {G H : MGraph} {u : Update}
    (hG : G.UpdateIsValid u) (hSub : G.IsSubgraph H) (hVH : H.V = G.V) :
    (G.applyUpdate u).IsSubgraph (H.applyBatch (restrictUpdate u H)) ∧
    (H.applyBatch (restrictUpdate u H)).V = (G.applyUpdate u).V := by
  cases u with
  | insert e x y =>
    rcases hG with ⟨he_not, _, _⟩
    simp only [restrictUpdate, MGraph.applyBatch, List.foldl_nil, MGraph.applyUpdate]
    refine ⟨⟨hVH.le, hSub.2.1.trans (Finset.subset_insert _ _), fun e' he' => ?_⟩, hVH⟩
    have hne : e' ≠ e := fun hc => he_not (hc ▸ hSub.2.1 he')
    rcases hSub.2.2 e' he' with ⟨ht, hh⟩
    simp [hne, ht, hh]
  | delete e =>
    have hr := isSubgraph_restrictUpdate hSub hVH hG (by trivial)
    exact ⟨hr.2.1, hr.2.2.1⟩
  | split v v' St Sh =>
    have hr := isSubgraph_restrictUpdate hSub hVH hG (by trivial)
    exact ⟨hr.2.1, hr.2.2.1⟩

lemma dgBatchTarget_step_invariant {G H : MGraph} (allowInsert : ℕ)
    (hH_base : (allowInsert ≠ 0 ∧ H = G) ∨ (allowInsert = 0 ∧ G.IsSubgraph H ∧ H.V = G.V))
    {u : Update} (hG : G.UpdateIsValid u) :
    (allowInsert ≠ 0 ∧ dgBatchTarget allowInsert H u = G.applyUpdate u) ∨
    (allowInsert = 0 ∧ (G.applyUpdate u).IsSubgraph (dgBatchTarget allowInsert H u) ∧
      (dgBatchTarget allowInsert H u).V = (G.applyUpdate u).V) := by
  rcases hH_base with ⟨ha, rfl⟩ | ⟨rfl, hSub, hVH⟩
  · exact Or.inl ⟨ha, by simp [dgBatchTarget, ha]⟩
  · rcases dgBatchTarget_preserves_subgraph hG hSub hVH with ⟨h1, h2⟩
    exact Or.inr ⟨rfl, by simpa [dgBatchTarget] using h1, by simpa [dgBatchTarget] using h2⟩

lemma dgUpdateMemLen_eq {mem : ℕ → ℕ} {updPtr : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (hu : UpdateAt mem updPtr G u len) :
    dgUpdateMemLen mem updPtr = len := by
  cases u with
  | insert e x y =>
    rcases hu with ⟨rfl, hat⟩
    have h0 : mem updPtr = 0 := by simpa using hat 0 (by simp)
    simp [dgUpdateMemLen, h0]
  | delete e =>
    rcases hu with ⟨rfl, hat⟩
    have h0 : mem updPtr = 1 := by simpa using hat 0 (by simp)
    simp [dgUpdateMemLen, h0]
  | split v v' St Sh =>
    rcases hu with ⟨Lt, Lh, _, _, _, _, rfl, hat⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hat⟩
    · have h0 := hat 0 (by simp)
      have h3 := hat 3 (by simp)
      have h4 := hat 4 (by simp)
      simp only [List.append_assoc, List.getElem_cons_zero, List.getElem_cons_succ,
        List.cons_append, Nat.add_zero] at h0 h3 h4
      simp [dgUpdateMemLen, h0, h3, h4]
    · have h0 := hat 0 (by simp)
      have h3 := hat 3 (by simp)
      have h4 := hat 4 (by simp)
      simp only [List.append_assoc, List.getElem_cons_zero, List.getElem_cons_succ,
        List.cons_append, Nat.add_zero] at h0 h3 h4
      simp [dgUpdateMemLen, h0, h3, h4]

/-! ## Verification of `dgApplyUpdate` and `dgApplyBatch` -/

theorem dgApplyUpdate_meetsContract {w : ℕ} {p : Program} {bEdge bSplit bOps bBatch vCap eCap : ℕ}
    {G H : MGraph} {u : Update} {len : ℕ}
    (hp : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bBatch + dgIdxApplyUpdate)
      (dgApplyUpdateContract w vCap eCap G H u len) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxApplyUpdate) (by simp [dgBatchProcs, dgIdxApplyUpdate]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, updPtr, allowInsert, rfl, hw16, hbound, hubound,
    hu_disj, hu_words, hu_at, hu_valid, hu_caps, hH, hrel⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_up : updPtr < 2 ^ w := hargs updPtr (by simp)
  have hlt_ai : allowInsert < 2 ^ w := hargs allowInsert (by simp)
  have hlen_mem : dgUpdateMemLen mem updPtr = len := dgUpdateMemLen_eq hu_at
  have hw_ne0 : w ≠ 0 := by rintro rfl; omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgBatchProcs, dgIdxApplyUpdate, List.getElem_cons_zero, dgApplyUpdateStmt]
  cases u with
  | insert e x y =>
    rcases hu_at with ⟨rfl, hat⟩
    have h0 : mem updPtr = 0 := by simpa using hat 0 (by simp)
    have h1 : mem (updPtr + 1) = e := by simpa using hat 1 (by simp)
    have h2 : mem (updPtr + 2) = x := by simpa using hat 2 (by simp)
    have h3 : mem (updPtr + 3) = y := by simpa using hat 3 (by simp)
    have hlt_e : e < 2 ^ w := h1 ▸ hu_words 1 (by omega)
    have hlt_x : x < 2 ^ w := h2 ▸ hu_words 2 (by omega)
    have hlt_y : y < 2 ^ w := h3 ▸ hu_words 3 (by omega)
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := 0) (by eval_expr)
      (by simpa [startState] using h0)) ?_
    refine runs_cond_le (v := 1)
      (by simp [Expr.eval, BinOp.eval, Function.update_self, hw_ne0, h0_lt]) ?_ ?_
    · intro _
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := e) (by eval_expr)
        (by simpa [startState] using h1)) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := x) (by eval_expr)
        (by simpa [startState] using h2)) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := y) (by eval_expr)
        (by simpa [startState] using h3)) ?_
      refine runs_seq_cond_le (v := allowInsert) (by eval_expr) ?_ ?_
      · intro hne
        rcases hrel with ⟨_, rfl⟩ | ⟨hz, _, _⟩
        · have hxV : x ∈ H.V := hu_valid.2.1
          have hyV : y ∈ H.V := hu_valid.2.2
          have heCap : e < eCap := hu_caps
          have heNot : e ∉ H.E := hu_valid.1
          have hpre_ins : (dgInsertEdgeContract w vCap eCap H).pre [gPtr, e, x, y] mem :=
            ⟨gPtr, e, x, y, rfl, hw16, hbound, hxV, hyV, hH⟩
          refine runs_seq_call_le (dgInsertEdge_meetsContract hpEdge hpOps) (by eval_expr)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl) <;> assumption)
            hpre_ins ?_
          rintro _ mem' pos' ⟨_, _, _, _, hEq, _, hG', hfr'⟩
          simp only [List.cons.injEq, and_true] at hEq
          rcases hEq with ⟨h1', h2', h3', h4'⟩
          subst h1' h2' h3' h4'
          refine runs_ret_le (by eval_expr) ⟨gPtr, updPtr, allowInsert, rfl, rfl, ?_, hfr'⟩ ?_
          · simp [dgBatchTarget, hne, heCap, heNot] at hG' ⊢; exact hG'
          · simp only [dgApplyUpdateContract, dgInsertEdgeContract, List.getElem?_cons_succ,
              List.getElem?_cons_zero, Option.getD_some, hlen_mem, argsSize, Expr.size]
            omega
        · exact absurd rfl (hz ▸ hne)
      · intro hzero
        refine runs_seq_nop_le ?_
        refine runs_ret_le (by eval_expr) ⟨gPtr, updPtr, allowInsert, rfl, rfl, ?_, fun _ _ => rfl⟩ ?_
        · simp only [dgBatchTarget, hzero, ↓reduceIte, restrictUpdate, MGraph.applyBatch, List.foldl_nil]
          exact hH
        · simp only [dgApplyUpdateContract, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.getD_some, hlen_mem, Expr.size]
          omega
    · intro hc; cases hc
  | delete e =>
    rcases hu_at with ⟨rfl, hat⟩
    have h0 : mem updPtr = 1 := by simpa using hat 0 (by simp)
    have h1 : mem (updPtr + 1) = e := by simpa using hat 1 (by simp)
    have hlt_e : e < 2 ^ w := h1 ▸ hu_words 1 (by omega)
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := 1) (by eval_expr)
      (by simpa [startState] using h0)) ?_
    refine runs_cond_le (v := 0)
      (by simp [Expr.eval, BinOp.eval, Function.update_self, h0_lt]) ?_ ?_
    · intro hc; exact absurd rfl hc
    · intro _
      refine runs_cond_le (v := 1)
        (by simp [Expr.eval, BinOp.eval, Function.update_self, h1_lt]) ?_ ?_
      · intro _
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := e) (by eval_expr)
          (by simpa [startState] using h1)) ?_
        have hpre_del : (dgDeleteEdgeContract w vCap eCap H).pre [gPtr, e] mem :=
          ⟨gPtr, e, rfl, hw16, hbound, hH⟩
        refine runs_seq_call_le (dgDeleteEdge_meetsContract hpEdge hpOps) (by eval_expr)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl) <;> assumption)
          hpre_del ?_
        rintro _ mem' pos' ⟨_, _, hEq, _, hH', hfr'⟩
        simp only [List.cons.injEq, and_true] at hEq
        rcases hEq with ⟨h1', h2'⟩
        subst h1' h2'
        refine runs_ret_le (by eval_expr) ⟨gPtr, updPtr, allowInsert, rfl, rfl, ?_, hfr'⟩ ?_
        · by_cases ha : allowInsert = 0
          · simp only [dgBatchTarget, ha, ↓reduceIte, restrictUpdate]
            by_cases heH : e ∈ H.E
            · simp only [heH, ↓reduceIte, MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at hH' ⊢
              exact hH'
            · simp only [heH, ↓reduceIte, MGraph.applyBatch, List.foldl_nil] at hH' ⊢
              exact hH'
          · rcases hrel with ⟨_, rfl⟩ | ⟨hz, _, _⟩
            · simp only [dgBatchTarget, ha, ↓reduceIte]
              have heH : e ∈ H.E := hu_valid
              simpa [heH] using hH'
            · exact absurd hz ha
        · simp only [dgApplyUpdateContract, dgDeleteEdgeContract, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.getD_some, hlen_mem, argsSize, Expr.size]
          omega
      · intro hc; cases hc
  | split v v' St Sh =>
    have hsplit_aux : ∀ (tag : ℕ) (Lt Lh : List ℕ),
        (tag = 2 ∨ tag = 3) →
        len = 5 + Lt.length + Lh.length →
        ListAt mem updPtr ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) →
        ((tag = 2 ∧ (∀ e ∈ H.E, e ∈ Lt ↔ H.tail e = v ∧ e ∈ St) ∧
           (∀ e ∈ H.E, e ∈ Lh ↔ H.head e = v ∧ e ∈ Sh)) ∨
         (tag = 3 ∧ (∀ e ∈ H.E, e ∈ Lt ↔ H.tail e = v ∧ e ∉ St) ∧
           (∀ e ∈ H.E, e ∈ Lh ↔ H.head e = v ∧ e ∉ Sh))) →
        ∃ o st' c,
          Runs w p ω
            (.assign 3 (.load (.reg 1)) ;;
             .cond (.bin .eq (.reg 3) (.const 0))
               (.assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
                .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;;
                .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;;
                .cond (.reg 2)
                  (.call 7 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 4, .reg 5, .reg 6])
                  .nop ;;
                .ret (.const 4))
               (.cond (.bin .eq (.reg 3) (.const 1))
                 (.assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
                  .call 7 (bEdge + dgIdxDeleteEdge) [.reg 0, .reg 4] ;;
                  .ret (.const 2))
                 (.assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
                  .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;;
                  .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;;
                  .assign 7 (.load (.bin .add (.reg 1) (.const 4))) ;;
                  .call 8 (bSplit + dgIdxApplySplit)
                    [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .bin .add (.reg 1) (.const 5)] ;;
                  .ret (.bin .add (.bin .add (.const 5) (.reg 6)) (.reg 7)))))
            (startState [gPtr, updPtr, allowInsert] mem pos) o st' c ∧
          (dgApplyUpdateContract w vCap eCap G H (.split v v' St Sh) len).post
            [gPtr, updPtr, allowInsert] mem o.value st'.mem ∧
          0 + c ≤ (dgApplyUpdateContract w vCap eCap G H (.split v v' St Sh) len).cost
            [gPtr, updPtr, allowInsert] mem := by
      intro tag Lt Lh htag_eq hlen hat htag_spec
      subst hlen
      have hat' : ListAt mem updPtr ([tag, v, v', Lt.length, Lh.length] ++ (Lt ++ Lh)) := by
        simpa [List.append_assoc] using hat
      have h0 : mem updPtr = tag := by simpa using hat' 0 (by simp)
      have h1 : mem (updPtr + 1) = v := by simpa using hat' 1 (by simp)
      have h2 : mem (updPtr + 2) = v' := by simpa using hat' 2 (by simp)
      have h3 : mem (updPtr + 3) = Lt.length := by simpa using hat' 3 (by simp)
      have h4 : mem (updPtr + 4) = Lh.length := by simpa using hat' 4 (by simp)
      have hL_at : ListAt mem (updPtr + 5) (Lt ++ Lh) := fun i hi => by
        have hi' : 5 + i < ([tag, v, v', Lt.length, Lh.length] ++ (Lt ++ Lh)).length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hi ⊢; omega
        have hget := hat' (5 + i) hi'
        have hlen5 : ([tag, v, v', Lt.length, Lh.length] : List ℕ).length ≤ 5 + i := by simp
        rw [List.getElem_append_right hlen5] at hget
        simpa [Nat.add_assoc] using hget
      have hL_word : ∀ x ∈ Lt ++ Lh, x < 2 ^ w := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have := hL_at j hj
        rw [← this, Nat.add_assoc]
        have hj' : j < Lt.length + Lh.length := by simpa only [List.length_append] using hj
        exact hu_words (5 + j) (by omega)
      have hlt_tag : tag < 2 ^ w := h0 ▸ hu_words 0 (by omega)
      have hlt_v : v < 2 ^ w := h1 ▸ hu_words 1 (by omega)
      have hlt_v' : v' < 2 ^ w := h2 ▸ hu_words 2 (by omega)
      have hlt_Ltlen : Lt.length < 2 ^ w := h3 ▸ hu_words 3 (by omega)
      have hlt_Lhlen : Lh.length < 2 ^ w := h4 ▸ hu_words 4 (by omega)
      have hlt_5 : 5 < 2 ^ w := by omega
      have hlt_5t : 5 + Lt.length < 2 ^ w := by omega
      have hlt_len : 5 + Lt.length + Lh.length < 2 ^ w := by omega
      have hL_disj : ∀ i < Lt.length + Lh.length,
          updPtr + 5 + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ updPtr + 5 + i :=
        fun i hi => by simpa [Nat.add_assoc] using hu_disj (5 + i) (by omega)
      have hne0 : tag ≠ 0 := by rcases htag_eq with rfl | rfl <;> decide
      have hne1 : tag ≠ 1 := by rcases htag_eq with rfl | rfl <;> decide
      have hvH : v ∈ H.V := by
        rcases hrel with ⟨_, rfl⟩ | ⟨_, _, hVH⟩
        · exact hu_valid.1
        · exact hVH ▸ hu_valid.1
      have hv'H : v' ∉ H.V := by
        rcases hrel with ⟨_, rfl⟩ | ⟨_, _, hVH⟩
        · exact hu_valid.2.1
        · simpa [hVH] using hu_valid.2.1
      have hv'_cap : v' < vCap := hu_caps
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tag) (by eval_expr)
        (by simpa [startState] using h0)) ?_
      refine runs_cond_le (v := 0)
        (by simp [Expr.eval, BinOp.eval, Function.update_self, h0_lt, hne0]) ?_ ?_
      · intro hc; exact absurd rfl hc
      · intro _
        refine runs_cond_le (v := 0)
          (by simp [Expr.eval, BinOp.eval, Function.update_self, h1_lt, hne1]) ?_ ?_
        · intro hc; exact absurd rfl hc
        · intro _
          refine runs_seq_assign_le (Expr.eval_load_of_eq (v := v) (by eval_expr)
            (by simpa [startState] using h1)) ?_
          refine runs_seq_assign_le (Expr.eval_load_of_eq (v := v') (by eval_expr)
            (by simpa [startState] using h2)) ?_
          refine runs_seq_assign_le (Expr.eval_load_of_eq (v := Lt.length) (by eval_expr)
            (by simpa [startState] using h3)) ?_
          refine runs_seq_assign_le (Expr.eval_load_of_eq (v := Lh.length) (by eval_expr)
            (by simpa [startState] using h4)) ?_
          refine runs_seq_call_le (dgApplySplit_meetsContract hpSplit hpOps) (by eval_expr)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                rintro z (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega)
            ⟨gPtr, tag, v, v', Lt.length, Lh.length, updPtr + 5, rfl, hw16, hbound, by omega,
              hvH, hv'H, hv'_cap, hH, rfl, rfl, hL_at, hL_word, hL_disj, htag_spec⟩ ?_
          rintro _ mem' pos' ⟨_, _, _, _, _, _, _, hEq, _, hH', hfr'⟩
          simp only [List.cons.injEq, and_true] at hEq
          rcases hEq with ⟨h1', h2', h3', h4', h5', h6', h7'⟩
          subst h1' h2' h3' h4' h5' h6' h7'
          refine runs_ret_le (by eval_expr) ⟨gPtr, updPtr, allowInsert, rfl, rfl, ?_, hfr'⟩ ?_
          · by_cases ha : allowInsert = 0
            · simpa [dgBatchTarget, ha, restrictUpdate, MGraph.applyBatch] using hH'
            · rcases hrel with ⟨_, rfl⟩ | ⟨hz, _, _⟩
              · have hStE : St ∩ H.E = St := Finset.inter_eq_left.mpr
                  (Finset.subset_union_left.trans hu_valid.2.2.1)
                have hShE : Sh ∩ H.E = Sh := Finset.inter_eq_left.mpr
                  (Finset.subset_union_right.trans hu_valid.2.2.1)
                simpa [dgBatchTarget, ha, hStE, hShE] using hH'
              · exact absurd hz ha
          · simp only [dgApplyUpdateContract, dgApplySplitContract, List.getElem?_cons_succ,
              List.getElem?_cons_zero, Option.getD_some, hlen_mem, argsSize, Expr.size]
            omega
    rcases hu_at with ⟨Lt, Lh, _, _, hLt_S, hLh_S, hlen, hat⟩ |
        ⟨Lt, Lh, _, _, hLt_K, hLh_K, hlen, hat⟩
    · refine hsplit_aux 2 Lt Lh (Or.inl rfl) hlen hat (Or.inl ⟨rfl, fun e heH => ?_, fun e heH => ?_⟩)
      · rcases hrel with ⟨_, rfl⟩ | ⟨_, hSub, _⟩
        · constructor
          · intro h; exact ⟨((hLt_S e).mp h).2.1, ((hLt_S e).mp h).2.2⟩
          · intro h; exact (hLt_S e).mpr ⟨heH, h.1, h.2⟩
        · have heG : e ∈ G.E := hSub.2.1 heH
          rcases hSub.2.2 e heH with ⟨ht, _⟩
          constructor
          · intro h; have h' := (hLt_S e).mp h; exact ⟨ht.symm ▸ h'.2.1, h'.2.2⟩
          · intro h; exact (hLt_S e).mpr ⟨heG, ht ▸ h.1, h.2⟩
      · rcases hrel with ⟨_, rfl⟩ | ⟨_, hSub, _⟩
        · constructor
          · intro h; exact ⟨((hLh_S e).mp h).2.1, ((hLh_S e).mp h).2.2⟩
          · intro h; exact (hLh_S e).mpr ⟨heH, h.1, h.2⟩
        · have heG : e ∈ G.E := hSub.2.1 heH
          rcases hSub.2.2 e heH with ⟨_, hh⟩
          constructor
          · intro h; have h' := (hLh_S e).mp h; exact ⟨hh.symm ▸ h'.2.1, h'.2.2⟩
          · intro h; exact (hLh_S e).mpr ⟨heG, hh ▸ h.1, h.2⟩
    · refine hsplit_aux 3 Lt Lh (Or.inr rfl) hlen hat (Or.inr ⟨rfl, fun e heH => ?_, fun e heH => ?_⟩)
      · rcases hrel with ⟨_, rfl⟩ | ⟨_, hSub, _⟩
        · constructor
          · intro h; exact ⟨((hLt_K e).mp h).2.1, ((hLt_K e).mp h).2.2⟩
          · intro h; exact (hLt_K e).mpr ⟨heH, h.1, h.2⟩
        · have heG : e ∈ G.E := hSub.2.1 heH
          rcases hSub.2.2 e heH with ⟨ht, _⟩
          constructor
          · intro h; have h' := (hLt_K e).mp h; exact ⟨ht.symm ▸ h'.2.1, h'.2.2⟩
          · intro h; exact (hLt_K e).mpr ⟨heG, ht ▸ h.1, h.2⟩
      · rcases hrel with ⟨_, rfl⟩ | ⟨_, hSub, _⟩
        · constructor
          · intro h; exact ⟨((hLh_K e).mp h).2.1, ((hLh_K e).mp h).2.2⟩
          · intro h; exact (hLh_K e).mpr ⟨heH, h.1, h.2⟩
        · have heG : e ∈ G.E := hSub.2.1 heH
          rcases hSub.2.2 e heH with ⟨_, hh⟩
          constructor
          · intro h; have h' := (hLh_K e).mp h; exact ⟨hh.symm ▸ h'.2.1, h'.2.2⟩
          · intro h; exact (hLh_K e).mpr ⟨heG, hh ▸ h.1, h.2⟩

private lemma batchIsValid_take_drop :
    ∀ (idx : ℕ) (G : MGraph) (U : List Update),
      G.BatchIsValid U →
      (G.applyBatch (U.take idx)).BatchIsValid (U.drop idx)
  | 0, _, _, h => by simpa [MGraph.applyBatch] using h
  | idx + 1, G, [], h => by simpa [MGraph.applyBatch] using h
  | idx + 1, G, u :: us, ⟨hu, hus⟩ => by
    simpa [MGraph.applyBatch] using batchIsValid_take_drop idx (G.applyUpdate u) us hus

theorem dgApplyBatch_meetsContract {w : ℕ} {p : Program} {bOps bEdge bSplit bBatch vCap eCap : ℕ}
    {G H : MGraph} {U : List Update} {totalWords : ℕ}
    (hp : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bBatch + dgIdxApplyBatch)
      (dgApplyBatchContract w vCap eCap G H U totalWords) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxApplyBatch) (by simp [dgBatchProcs, dgIdxApplyBatch]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, batchPtr, allowInsert, rfl, hw16, hbound, htwbound,
    hb_disj, hb_words, hb_at, hb_valid, hb_caps, hH, hrel⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_bp : batchPtr < 2 ^ w := hargs batchPtr (by simp)
  have hlt_ai : allowInsert < 2 ^ w := hargs allowInsert (by simp)
  rcases hb_at with ⟨htw_pos, hbp_len, hbody⟩
  have h2len := BatchBodyAt.two_mul_length_le hbody
  have hlt_Ulen : U.length < 2 ^ w := by omega
  have hlt_bp1 : batchPtr + 1 < 2 ^ w := by omega
  let Inv : State → Prop := fun st =>
    ∃ (idx remWords : ℕ),
      idx ≤ U.length ∧ remWords ≤ totalWords - 1 ∧
      st.regs 0 = gPtr ∧ st.regs 2 = allowInsert ∧ st.regs 3 = U.length ∧
      st.regs 4 = idx ∧ st.regs 5 + remWords = batchPtr + totalWords ∧
      BatchBodyAt st.mem (st.regs 5) (G.applyBatch (U.take idx)) (U.drop idx) remWords ∧
      (∀ i < totalWords, st.mem (batchPtr + i) = mem (batchPtr + i)) ∧
      DynGraphAt st.mem gPtr vCap eCap ((U.take idx).foldl (dgBatchTarget allowInsert) H) ∧
      ((allowInsert ≠ 0 ∧ (U.take idx).foldl (dgBatchTarget allowInsert) H = G.applyBatch (U.take idx)) ∨
       (allowInsert = 0 ∧ (G.applyBatch (U.take idx)).IsSubgraph ((U.take idx).foldl (dgBatchTarget allowInsert) H) ∧
         ((U.take idx).foldl (dgBatchTarget allowInsert) H).V = (G.applyBatch (U.take idx)).V)) ∧
      (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  let condExpr : Expr := .bin .lt (.reg 4) (.reg 3)
  let bodyStmt : Stmt :=
    .call 6 (bBatch + dgIdxApplyUpdate) [.reg 0, .reg 5, .reg 2] ;;
    .assign 5 (.bin .add (.reg 5) (.reg 6)) ;;
    .assign 4 (.bin .add (.reg 4) (.const 1))
  let mFn : State → ℕ := fun st => U.length - st.regs 4
  let remFn : State → ℕ := fun st =>
    650 * (batchPtr + totalWords - st.regs 5) + 30 * (U.length - st.regs 4) + 10
  let condFn : State → ℕ := fun st => if st.regs 4 < U.length then 1 else 0
  have hloop : Triple w p Inv (.loop condExpr bodyStmt)
      (normalPost fun st =>
        DynGraphAt st.mem gPtr vCap eCap (U.foldl (dgBatchTarget allowInsert) H) ∧
        (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr))
      remFn := by
    refine Triple.loop_measure
      (condVal := condFn) (m := mFn) (rem := remFn)
      (fun st hInv => by
        rcases hInv with ⟨idx, _, hidx, _, _, _, hr3, hr4, _, _, _, _, _, _⟩
        dsimp only [condExpr, condFn]
        rw [hr4]; eval_expr)
      (fun st hInv hv => by
        rcases hInv with ⟨idx, _, hidx, _, _, _, _, hr4, _, _, _, hH_idx, _, hfr_idx⟩
        dsimp only [condFn] at hv
        have hidx_eq : idx = U.length := by rw [hr4] at hv; by_contra hc; simp [show idx < U.length by omega] at hv
        subst hidx_eq
        refine ⟨⟨?_, hfr_idx⟩, by dsimp [condExpr, Expr.size, remFn]; omega⟩
        simpa [List.take_length] using hH_idx)
      (fun st hInv hv => by
        rcases hInv with ⟨idx, remWords, hidx, hrem_le, hr0, hr2, hr3, hr4, hr5_eq,
          hbody_idx, hmem_eq, hH_idx, hrel_idx, hfr_idx⟩
        dsimp only [condFn] at hv
        have hidx_lt : idx < U.length := by rw [hr4] at hv; by_contra hc; simp [hc] at hv
        have hdrop : U.drop idx = U[idx] :: U.drop (idx + 1) :=
          (List.cons_getElem_drop_succ (h := hidx_lt)).symm
        rw [hdrop] at hbody_idx
        rcases hbody_idx with ⟨len, hlen_rem, hu_at, hrest_body⟩
        have hlen_ltw : len < 2 ^ w := by omega
        have hcur_lo : batchPtr + 1 ≤ st.regs 5 := by omega
        have hcur_ltw : st.regs 5 < 2 ^ w := by omega
        have hcur_end_ltw : st.regs 5 + len < 2 ^ w := by omega
        have hidx1_ltw : idx + 1 < 2 ^ w := by omega
        have hu_disj : ∀ i < len, st.regs 5 + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ st.regs 5 + i := by
          intro i hi
          have hi_tot : st.regs 5 - batchPtr + i < totalWords := by omega
          simpa [show batchPtr + (st.regs 5 - batchPtr + i) = st.regs 5 + i by omega] using hb_disj _ hi_tot
        have hu_words : ∀ i < len, st.mem (st.regs 5 + i) < 2 ^ w := by
          intro i hi
          have hi_tot : st.regs 5 - batchPtr + i < totalWords := by omega
          have heq := hmem_eq _ hi_tot
          have hbw := hb_words _ hi_tot
          have haddr : batchPtr + (st.regs 5 - batchPtr + i) = st.regs 5 + i := by omega
          rw [haddr] at heq hbw
          rw [heq]; exact hbw
        have hu_val_idx : (G.applyBatch (U.take idx)).UpdateIsValid U[idx] := by
          have hv_drop := batchIsValid_take_drop idx G U hb_valid
          rw [hdrop] at hv_drop
          exact hv_drop.1
        have hu_caps_idx : UpdateWithinCaps vCap eCap U[idx] := hb_caps U[idx] (List.getElem_mem hidx_lt)
        refine ⟨640 * len + 20, ?_⟩
        intro s ω' hs_eq
        subst s
        suffices h : ∃ o s' c, Runs w p ω' bodyStmt st o s' c ∧
            (match o with
              | .returned u => normalPost (fun st =>
                  DynGraphAt st.mem gPtr vCap eCap (U.foldl (dgBatchTarget allowInsert) H) ∧
                  (∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr))
                  (.returned u) s' ∧ condExpr.size + (640 * len + 20) + 1 ≤ remFn st
              | .normal => Inv s' ∧ mFn s' < mFn st ∧
                  condExpr.size + (640 * len + 20) + remFn s' + 1 ≤ remFn st) ∧
            0 + c ≤ 640 * len + 20 by
          rcases h with ⟨o, s', c, hr, hq, hc⟩
          exact ⟨o, s', c, hr, hq, by simpa using hc⟩
        dsimp only [bodyStmt]
        have hpre_u : (dgApplyUpdateContract w vCap eCap (G.applyBatch (U.take idx))
            ((U.take idx).foldl (dgBatchTarget allowInsert) H) U[idx] len).pre
            [gPtr, st.regs 5, allowInsert] st.mem :=
          ⟨gPtr, st.regs 5, allowInsert, rfl, hw16, hbound, by omega,
            hu_disj, hu_words, hu_at, hu_val_idx, hu_caps_idx, hH_idx, hrel_idx⟩
        refine runs_seq_call_le (dgApplyUpdate_meetsContract hp hpEdge hpSplit hpOps)
          (by eval_expr)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl) <;> omega)
          hpre_u ?_
        rintro ret_u mem' pos' ⟨_, _, _, hEq_u, hret_len, hH_next, hfr_u⟩
        simp only [List.cons.injEq, and_true] at hEq_u
        rcases hEq_u with ⟨h1', h2', h3'⟩
        subst h1' h2' h3'
        have hret_eq : ret_u = len := by omega
        rw [hret_eq]
        have hw_ne0 : w ≠ 0 := by rintro rfl; omega
        refine runs_seq_assign_le (v := st.regs 5 + len) (by eval_expr) ?_
        refine runs_assign_le (v := idx + 1)
          (by dsimp only; simp [Expr.eval, BinOp.eval, hr4, hw_ne0, hidx1_ltw]) ?_ ?_
        · have hmem'_eq : ∀ i < totalWords, mem' (batchPtr + i) = mem (batchPtr + i) := by
            intro i hi
            exact (hfr_u _ (hb_disj i hi)).trans (hmem_eq i hi)
          have hrest_body' : BatchBodyAt mem' (st.regs 5 + len)
              ((G.applyBatch (U.take idx)).applyUpdate U[idx]) (U.drop (idx + 1)) (remWords - len) :=
            hrest_body.of_agree fun i hi => by
              have hdisj : st.regs 5 + len + i < gPtr ∨
                  gPtr + dynGraphSize vCap eCap ≤ st.regs 5 + len + i := by
                have hi_tot : st.regs 5 - batchPtr + len + i < totalWords := by omega
                simpa [show batchPtr + (st.regs 5 - batchPtr + len + i) = st.regs 5 + len + i by omega] using
                  hb_disj _ hi_tot
              exact hfr_u _ hdisj
          have htake1 : U.take (idx + 1) = U.take idx ++ [U[idx]] :=
            List.take_succ_eq_append_getElem hidx_lt
          have hG_next : G.applyBatch (U.take (idx + 1)) =
              (G.applyBatch (U.take idx)).applyUpdate U[idx] := by
            simp only [MGraph.applyBatch, htake1, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hH_next_eq : (U.take (idx + 1)).foldl (dgBatchTarget allowInsert) H =
              dgBatchTarget allowInsert ((U.take idx).foldl (dgBatchTarget allowInsert) H) U[idx] := by
            simp only [htake1, List.foldl_append, List.foldl_cons, List.foldl_nil]
          refine ⟨⟨idx + 1, remWords - len, hidx_lt, by omega, ?_, ?_, ?_, ?_, by simp; omega,
              ?_, hmem'_eq, ?_, ?_, fun addr hout => (hfr_u addr hout).trans (hfr_idx addr hout)⟩, ?_, ?_⟩
          · simp [hr0]
          · simp [hr2]
          · simp [hr3]
          · simp
          · simpa [hG_next] using hrest_body'
          · simpa [hH_next_eq] using hH_next
          · simpa [hG_next, hH_next_eq] using dgBatchTarget_step_invariant allowInsert hrel_idx hu_val_idx
          · dsimp only [mFn]; simp [hr4]; omega
          · dsimp only [condExpr, remFn, Expr.size]
            simp only [Function.update_self, Function.update_of_ne (by decide : (5 : ℕ) ≠ 4)]
            have h1_sub : batchPtr + totalWords - (st.regs 5 + len) + len = batchPtr + totalWords - st.regs 5 := by
              omega
            have h2_sub : U.length - (idx + 1) + 1 = U.length - idx := by omega
            omega
        · have hlen_cost : dgUpdateMemLen st.mem (st.regs 5) = len := dgUpdateMemLen_eq hu_at
          simp only [dgApplyUpdateContract, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.getD_some, hlen_cost, argsSize, Expr.size]
          omega)
  refine runs_start_le ?_
  dsimp only [dgBatchProcs, dgIdxApplyBatch, List.getElem_cons_succ, List.getElem_cons_zero,
    dgApplyBatchStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := U.length) (by eval_expr)
    (by simpa [startState] using hbp_len)) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := batchPtr + 1) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨0, totalWords - 1, Nat.zero_le _, le_refl _, ?_, ?_, ?_, ?_, by simp; omega,
      ?_, fun _ _ => rfl, ?_, ?_, fun _ _ => rfl⟩
    · simp [startState]
    · simp [startState]
    · simp [startState]
    · simp
    · simpa [startState, MGraph.applyBatch] using hbody
    · simpa [startState] using hH
    · simpa [MGraph.applyBatch] using hrel
  · rintro st' ⟨hH_out, hfr_out⟩
    refine runs_ret_le (by eval_expr) ⟨gPtr, batchPtr, allowInsert, rfl, rfl, hH_out, hfr_out⟩ ?_
    · dsimp only [dgApplyBatchContract, remFn, Expr.size]
      have : 2 * U.length ≤ totalWords - 1 := h2len
      simp only [Function.update_self]
      omega

end

end MinCostFlow.DynSpanner.Program

