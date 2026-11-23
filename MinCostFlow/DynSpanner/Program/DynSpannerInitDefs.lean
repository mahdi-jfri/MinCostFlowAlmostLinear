module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalks
public import MinCostFlow.DynSpanner.Program.DynSpannerPhase
public import MinCostFlow.DynSpanner.Program.SparsifyHost
public import MinCostFlow.DynSpanner.Program.DynGraphInit
public import MinCostFlow.DynSpanner.RebuildSpec

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithm 6 Initialization Procedures (`DynSpannerInit`)

Implements and verifies deterministic Word-RAM initialization procedures (`initProcs`, length `3`):
* `dsInitCoreStmt` (`initIdxCore = 0`): builds `H₀, Π₀, inDom 0, revLists 0, hBuckets 0` from `G`
  at `dsGPtr b` (`O(sparsifyDyn + G.n + G.m + H₀.m + ∑ (Π₀ e).length + 1)`), matching
  `DynSpanner.initCore G (canonicalSparsify impl)`.
* `dsInitAtStmt` (`initIdxAt = 1`): initializes header scalars, `G`, `H`, `Aux`, and calls
  `dsInitCoreStmt`, establishing full `DynSpannerStateAt`.
* `dsInitStmt` (`initIdx = 2`): `WordRAM.DataStructure` initialization wrapper allocating handle
  `b := heapPtr` (`t = 0`), establishing `DynSpannerStateAt` and `RevHistoryInv 0`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices -/

def initIdxCore : ℕ := 0
def initIdxAt : ℕ := 1
def initIdx : ℕ := 2

/-! ## Word-RAM statement bodies -/

/-- Part 1 of `dsInitCoreStmt`: compute fixed offsets into `r2..r11` and insert `G.V` into `H`. -/
def dsInitCorePrepStmt (bOps : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 5 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 2)) (.bin .mul (.const 9) (.reg 3)))) ;;
  .assign 6 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 5)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 5)) ;;
  .assign 9 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 5))) ;;
  .assign 9 (.bin .add (.reg 9)
    (.bin .add (.bin .mul (.const 3) (.reg 3))
      (.bin .mul (.const 2) (.bin .add (.reg 4) (.const 1))))) ;;
  .assign 9 (.bin .add (.reg 9)
    (.bin .add (.bin .add (.reg 4) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 4) (.const 1)) (.reg 3))))) ;;
  .assign 9 (.bin .add (.reg 9)
    (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 4) (.const 1)) (.reg 2)))
      (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 4) (.const 1))) (.reg 2)))) ;;
  .assign 9 (.bin .add (.reg 9) (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 3)))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const (dsHdrSize + dgNOff)))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const (dsHdrSize + dgMOff)))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 6) (.const 4)) (.reg 2)) ;;
  forRange 13 (.const 0) (.reg 10)
    (.assign 14 (.load (.bin .add (.reg 12) (.reg 13))) ;;
     .call 14 (bOps + dgIdxAddVertex) [.reg 7, .reg 14])

/-- `args = [b, heapPtr]`: run `initCore` assuming `G` at `dsGPtr b` and empty `H, Aux`, setting
`H₀, Π₀, inDom 0, revLists 0, hBuckets 0` and returning `heapFinal`. -/
def dsInitCoreStmt (bOps bEdge bPhase bLW bSpDyn : ℕ) : Stmt :=
  dsInitCorePrepStmt bOps ;;
  .cond (.reg 11)
    (.call 12 (bPhase + phaseIdxBuildActive) [.reg 6, .reg 8] ;;
     .call 1 (bLW + lwIdxWriteIdEmb) [.reg 8, .reg 9, .reg 1] ;;
     .assign 12 (.reg 1) ;;
     .assign 13 (.load (.bin .add (.reg 8) (.const dgNOff))) ;;
     .assign 14 (.bin .add (.reg 12)
       (.bin .add (.const 8)
         (.bin .add (.bin .mul (.const 3) (.reg 13)) (.bin .mul (.const 11) (.reg 11))))) ;;
     .call 15 (bSpDyn + gtIdxSparsifyDyn)
       [.reg 8, .reg 8, .reg 9, .reg 2, .reg 3, .reg 12, .reg 14] ;;
     .assign 16 (.load (.reg 12)) ;;
     .assign 17 (.load (.bin .add (.reg 12) (.const 1))) ;;
     .assign 18 (.load (.bin .add (.reg 16) (.const dgMOff))) ;;
     .assign 19 (.bin .add (.bin .add (.reg 16) (.const 4))
       (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
     forRange 20 (.const 0) (.reg 18)
       (.assign 21 (.load (.bin .add (.reg 19) (.reg 20))) ;;
        .call 22 (bOps + dgIdxGetTail) [.reg 6, .reg 21] ;;
        .call 23 (bOps + dgIdxGetHead) [.reg 6, .reg 21] ;;
        .call 24 (bEdge + dgIdxInsertEdge) [.reg 7, .reg 21, .reg 22, .reg 23] ;;
        .call 24 (bPhase + phaseIdxHBucketCons) [.reg 0, .const 0, .reg 21]) ;;
     .call 13 (bPhase + phaseIdxClearAux) [.reg 8] ;;
     .assign 12 (.bin .add (.bin .add (.reg 6) (.const 4))
       (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
     .call 15 (bLW + lwIdxShortcutEmb) [.reg 0, .reg 6, .reg 12, .reg 11, .reg 17, .reg 15] ;;
     .call 1 (bLW + lwIdxSetLevelWalks) [.reg 0, .const 0, .reg 12, .reg 11, .reg 17, .reg 15])
    (.assign 12 (.bin .add (.bin .add (.reg 6) (.const 4))
       (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
     .call 1 (bLW + lwIdxSetLevelWalks) [.reg 0, .const 0, .reg 12, .const 0, .reg 9, .reg 1]) ;;
  .ret (.reg 1)

/-- `args = [b, L, q, t, vCap, eCap, V_len, V_ptr, E_len, E_ptr, heapPtr]`: initialize a
fresh `DynSpannerStateAt` block at `b` from zeroed memory `[b ..)`. -/
def dsInitAtStmt (bOps bBatch bInit : ℕ) : Stmt :=
  .store (.bin .add (.reg 0) (.const dsQOff)) (.reg 2) ;;
  .store (.bin .add (.reg 0) (.const dsTOff)) (.reg 3) ;;
  .store (.bin .add (.reg 0) (.const dsLOff)) (.reg 1) ;;
  .store (.bin .add (.reg 0) (.const dsVCapOff)) (.reg 4) ;;
  .store (.bin .add (.reg 0) (.const dsECapOff)) (.reg 5) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.const 0) ;;
  .assign 11 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 4)) (.bin .mul (.const 9) (.reg 5)))) ;;
  .assign 12 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 11)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 11)) ;;
  .call 15 (bBatch + dgIdxInitFromLists) [.reg 12, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9] ;;
  .call 15 (bOps + dgIdxInitEmpty) [.reg 13, .reg 4, .reg 5] ;;
  .call 15 (bOps + dgIdxInitEmpty) [.reg 14, .reg 4, .reg 5] ;;
  .call 15 (bInit + initIdxCore) [.reg 0, .reg 10] ;;
  .ret (.reg 15)

/-- `args = [L, q, vCap, eCap, V_len, V_ptr, E_len, E_ptr, heapPtr]`: `DataStructure.init`
entrypoint at handle `b := heapPtr`, `t = 0`. -/
def dsInitStmt (bInit : ℕ) : Stmt :=
  .assign 9 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 2)) (.bin .mul (.const 9) (.reg 3)))) ;;
  .assign 10 (.bin .add (.bin .add (.const dsHdrSize) (.bin .mul (.const 3) (.reg 9)))
    (.bin .add (.bin .mul (.const 3) (.reg 3))
      (.bin .mul (.const 2) (.bin .add (.reg 0) (.const 1))))) ;;
  .assign 10 (.bin .add (.reg 10)
    (.bin .add (.bin .add (.reg 0) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 3))))) ;;
  .assign 10 (.bin .add (.reg 10)
    (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 2)))
      (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 0) (.const 1))) (.reg 2)))) ;;
  .assign 10 (.bin .add (.reg 10) (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 3)))) ;;
  .call 11 (bInit + initIdxAt)
    [.reg 8, .reg 0, .reg 1, .const 0, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
      .bin .add (.reg 8) (.reg 10)] ;;
  .ret (.reg 11)

/-- Initialization module (`3` deterministic procedures). -/
def initProcs (bOps bEdge bBatch bPhase bLW bSpDyn bInit : ℕ) : List Stmt :=
  [dsInitCoreStmt bOps bEdge bPhase bLW bSpDyn, dsInitAtStmt bOps bBatch bInit, dsInitStmt bInit]

lemma initProcs_length (bOps bEdge bBatch bPhase bLW bSpDyn bInit : ℕ) :
    (initProcs bOps bEdge bBatch bPhase bLW bSpDyn bInit).length = 3 := rfl

lemma initProcs_noRand (bOps bEdge bBatch bPhase bLW bSpDyn bInit : ℕ) :
    ∀ s ∈ initProcs bOps bEdge bBatch bPhase bLW bSpDyn bInit, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Space & Cost Bounds and Contracts -/

/-- Exact cost expression of `sparsifyDynContract impl mMax`. -/
noncomputable def sparsifyDynCost (impl : SparsifyImpl) (mMax : ℕ) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) : ℕ :=
  (sparsifyDynContract impl mMax 0 0 0 0 0 0 0 H' J emb).cost [] (fun _ => 0)

/-- Exact heap space upper bound needed by `dsInitCoreStmt` above `heapPtr`. -/
noncomputable def dsInitCoreSpaceBound (impl : SparsifyImpl) (mMax vCap eCap : ℕ)
    (G : MGraph) : ℕ :=
  let Gact := activeSubgraph G
  let w' := wordSize impl.cw (canonSparsifyInput Gact Gact idEmb)
  3 * G.m + (8 + 3 * Gact.n + 11 * G.m) + 2 ^ (w' + 1) + 2 + 3 * G.m +
    dynGraphSize vCap eCap + eCap + G.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax)) +
    9 * G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1)

/-- Word-RAM cost bound for `dsInitCoreStmt`. -/
noncomputable def dsInitCoreCost (impl : SparsifyImpl) (mMax : ℕ) (G : MGraph) : ℕ :=
  let Gact := activeSubgraph G
  let out := canonicalSparsify impl Gact Gact idEmb
  (if G.m = 0 then 0 else sparsifyDynCost impl mMax Gact Gact idEmb) +
    800 * (∑ e ∈ G.E, (out.emb e).length) + 170 * G.n + 2600 * G.m + 820 * out.Jtilde.E.card + 1300

/-- Predicate for addresses outside the regions modified by `dsInitCoreStmt`. -/
def dsInitCoreFrameCond (L vCap eCap b heapPtr ret addr : ℕ) : Prop :=
  addr ≠ b + dsGenOff ∧
  (addr < dsHPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) ∧
  (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) ∧
  addr ≠ dsHHeadBase b vCap eCap ∧
  addr ≠ dsHDegDummyBase b L vCap eCap ∧
  (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) ∧
  (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) ∧
  addr ≠ dsDomGenBase b L vCap eCap ∧
  (∀ e < eCap, addr ≠ dsEdgeDomGenBase b L vCap eCap + e) ∧
  (∀ e < eCap, addr ≠ dsPiPtrBase b L vCap eCap + e) ∧
  (∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + v) ∧
  (∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + v) ∧
  (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) ∧
  (∀ e < eCap, addr ≠ dsMEmbTempBase b L vCap eCap + e) ∧
  (addr < heapPtr ∨ ret ≤ addr)

/-- Contract for `dsInitCoreStmt` (`[b, heapPtr]`). -/
noncomputable def dsInitCoreContract (impl : SparsifyImpl) (mMax w L vCap eCap b : ℕ)
    (G : MGraph) : Contract where
  pre args mem := ∃ heapPtr,
    args = [b, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ b ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G < 2 ^ w ∧
    ZeroFrom mem heapPtr ∧
    (G.E.Nonempty → wordSize impl.cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤ w) ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    mem (b + dsGenOff) + 1 + G.m < 2 ^ w ∧
    (∀ e < eCap, mem (dsMinHBase b vCap eCap + e) = 0) ∧
    IsDoublyLinkedList mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap) eCap [] ∧
    mem (dsHDegDummyBase b L vCap eCap) = 0 ∧
    mem (dsDomGenBase b L vCap eCap) ≤ mem (b + dsGenOff) ∧
    (∀ e < eCap, mem (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem (b + dsGenOff)) ∧
    (∀ v < vCap, mem (dsRevGenBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    (∀ v < vCap, mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    DynGraphAt mem (dsGPtr b) vCap eCap G ∧
    DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap emptyMGraph ∧
    DynGraphAt mem (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph ∧
    G.IsValid ∧ G.m ≤ mMax ∧ (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap)
  post args mem ret mem' := ∃ heapPtr,
    let core := initCore G (canonicalSparsify impl)
    let H₀ := core.1
    let Pi₀ := core.2.1
    args = [b, heapPtr] ∧
    heapPtr ≤ ret ∧ ret ≤ heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G ∧ ZeroFrom mem' ret ∧
    mem' (b + dsGenOff) = mem (b + dsGenOff) + 1 + G.m ∧
    mem' (dsDomGenBase b L vCap eCap) = mem (b + dsGenOff) + 1 ∧
    (∀ v < vCap, mem' (dsVStampBase b L vCap eCap + v) ≤ mem' (b + dsGenOff)) ∧
    (∀ e < eCap, mem' (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem' (b + dsGenOff)) ∧
    DynGraphAt mem' (dsHPtr b vCap eCap) vCap eCap H₀ ∧
    DynGraphAt mem' (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph ∧
    (∀ e < eCap,
      (mem' (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
      (e ∈ H₀.E → mem' (dsMinHBase b vCap eCap + e) = 1)) ∧
    (∃ buck0 : List ℕ,
      IsDoublyLinkedList mem' (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap) eCap buck0 ∧
      mem' (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
      (∀ e, e ∈ buck0 ↔ e ∈ H₀.E)) ∧
    (∀ e < eCap,
      (0 < mem' (dsDomGenBase b L vCap eCap) ∧
       mem' (dsEdgeDomGenBase b L vCap eCap + e) = mem' (dsDomGenBase b L vCap eCap)) ↔
        e ∈ G.E) ∧
    (∀ e ∈ G.E,
      let ptr := mem' (dsPiPtrBase b L vCap eCap + e)
      MWalkAt mem' ptr (Pi₀ e) ∧ heapPtr ≤ ptr ∧ ptr + (mWalkEncode (Pi₀ e)).length ≤ ret) ∧
    (∃ rev0 : ℕ → List ℕ, ∀ v < vCap,
      mem' (dsRevGenBase b L vCap eCap + v) ≤ mem' (b + dsGenOff) ∧
      (rev0 v).Nodup ∧
      (∀ e, e ∈ rev0 v ↔ e ∈ G.E ∧ v ∈ H₀.walkVertices (G.tail e) (Pi₀ e)) ∧
      (if 0 < mem' (dsDomGenBase b L vCap eCap) ∧
          mem' (dsRevGenBase b L vCap eCap + v) = mem' (dsDomGenBase b L vCap eCap)
       then LinkedListIn (fun a => heapPtr ≤ a ∧ a < ret) mem'
              (mem' (dsRevHeadBase b L vCap eCap + v)) (rev0 v)
       else rev0 v = [])) ∧
    ∀ addr, dsInitCoreFrameCond L vCap eCap b heapPtr ret addr → mem' addr = mem addr
  cost _ _ := dsInitCoreCost impl mMax G

/-- Contract for `dsInitAtStmt` (`[b, L, q, t, vCap, eCap, V_len, V_ptr, E_len, E_ptr, heapPtr]`). -/
noncomputable def dsInitAtContract (impl : SparsifyImpl) (mMax w L q t vCap eCap b : ℕ)
    (G : MGraph) (vL : List ℕ) (eEdges : List (ℕ × ℕ × ℕ)) : Contract where
  pre args mem := ∃ V_ptr E_ptr heapPtr,
    args = [b, L, q, t, vCap, eCap, vL.length, V_ptr, eEdges.length, E_ptr, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ b ∧ 1 ≤ q ∧ t < 2 ^ w ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G < 2 ^ w ∧
    ZeroFrom mem b ∧
    1 + G.m < 2 ^ w ∧
    (G.E.Nonempty → wordSize impl.cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤ w) ∧
    G.IsValid ∧ G.m ≤ mMax ∧ (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    vL.length = G.n ∧ ListAt mem V_ptr vL ∧ (∀ v, v ∈ vL ↔ v ∈ G.V) ∧
    (∀ i < vL.length, V_ptr + i < b) ∧
    eEdges.length = G.m ∧ (eEdges.map Prod.fst).Nodup ∧
    (∀ i (hi : i < eEdges.length),
      mem (E_ptr + 3 * i) = eEdges[i].1 ∧
      mem (E_ptr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem (E_ptr + 3 * i + 2) = eEdges[i].2.2) ∧
    (∀ t' ∈ eEdges, t'.1 ∈ G.E ∧ t'.2.1 = G.tail t'.1 ∧ t'.2.2 = G.head t'.1) ∧
    (∀ e ∈ G.E, ∃ t' ∈ eEdges, t'.1 = e) ∧
    (∀ i < 3 * eEdges.length, E_ptr + i < b)
  post args mem ret mem' := ∃ V_ptr E_ptr heapPtr,
    args = [b, L, q, t, vCap, eCap, vL.length, V_ptr, eEdges.length, E_ptr, heapPtr] ∧
    heapPtr ≤ ret ∧ ret ≤ heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G ∧ ZeroFrom mem' ret ∧
    (∃ x : DynSpannerMeta L,
      x.vCap = vCap ∧ x.eCap = eCap ∧ x.intervals = [(heapPtr, ret)] ∧
      (∀ i : Fin (L + 1), x.sLists i = []) ∧
      x.memInDom ⟨0, Nat.zero_lt_succ L⟩ = G.E ∧
      (∀ i : Fin (L + 1), 0 < i.1 → x.memInDom i = ∅ ∧ ∀ v < vCap, x.revLists i v = []) ∧
      (∀ v < vCap, ∀ e, e ∈ x.revLists ⟨0, Nat.zero_lt_succ L⟩ v ↔
        e ∈ G.E ∧ v ∈ (initAt G L q t (canonicalSparsify impl)).state.H.walkVertices
          (G.tail e) ((initAt G L q t (canonicalSparsify impl)).state.Pi_level ⟨0, Nat.zero_lt_succ L⟩ e)) ∧
      DynSpannerStateAt L vCap eCap b mem' x (initAt G L q t (canonicalSparsify impl)).state) ∧
    (∀ addr < b, mem' addr = mem addr) ∧
    mem' (b + dsGenOff) = 1 + G.m
  cost _ _ := dsInitCoreCost impl mMax G + 140 * G.n + 500 * G.m + 320

/-- Contract for `dsInitStmt` (`[L, q, vCap, eCap, V_len, V_ptr, E_len, E_ptr, heapPtr]`). -/
noncomputable def dsInitContract (impl : SparsifyImpl) (mMax w L q vCap eCap : ℕ)
    (G : MGraph) (vL : List ℕ) (eEdges : List (ℕ × ℕ × ℕ)) : Contract where
  pre args mem := ∃ V_ptr E_ptr heapPtr,
    args = [L, q, vCap, eCap, vL.length, V_ptr, eEdges.length, E_ptr, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ heapPtr ∧ 1 ≤ q ∧
    heapPtr + dsFixedSize L vCap eCap + dsInitCoreSpaceBound impl mMax vCap eCap G < 2 ^ w ∧
    ZeroFrom mem heapPtr ∧
    1 + G.m < 2 ^ w ∧
    (G.E.Nonempty → wordSize impl.cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤ w) ∧
    G.IsValid ∧ G.m ≤ mMax ∧ (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    vL.length = G.n ∧ ListAt mem V_ptr vL ∧ (∀ v, v ∈ vL ↔ v ∈ G.V) ∧
    (∀ i < vL.length, V_ptr + i < heapPtr) ∧
    eEdges.length = G.m ∧ (eEdges.map Prod.fst).Nodup ∧
    (∀ i (hi : i < eEdges.length),
      mem (E_ptr + 3 * i) = eEdges[i].1 ∧
      mem (E_ptr + 3 * i + 1) = eEdges[i].2.1 ∧
      mem (E_ptr + 3 * i + 2) = eEdges[i].2.2) ∧
    (∀ t' ∈ eEdges, t'.1 ∈ G.E ∧ t'.2.1 = G.tail t'.1 ∧ t'.2.2 = G.head t'.1) ∧
    (∀ e ∈ G.E, ∃ t' ∈ eEdges, t'.1 = e) ∧
    (∀ i < 3 * eEdges.length, E_ptr + i < heapPtr)
  post args mem ret mem' := ∃ V_ptr E_ptr b,
    args = [L, q, vCap, eCap, vL.length, V_ptr, eEdges.length, E_ptr, b] ∧
    b + dsFixedSize L vCap eCap ≤ ret ∧
    ret ≤ b + dsFixedSize L vCap eCap + dsInitCoreSpaceBound impl mMax vCap eCap G ∧
    ZeroFrom mem' ret ∧
    (∃ x : DynSpannerMeta L,
      x.vCap = vCap ∧ x.eCap = eCap ∧ x.intervals = [(b + dsFixedSize L vCap eCap, ret)] ∧
      (∀ i : Fin (L + 1), x.sLists i = []) ∧
      DynSpannerStateAt L vCap eCap b mem' x (init G L q (canonicalSparsify impl)).state ∧
      ∀ us : List Update, RevHistoryInv G q (canonicalSparsify impl) us 0 x) ∧
    (∀ addr < b, mem' addr = mem addr) ∧
    mem' (b + dsGenOff) = 1 + G.m
  cost _ _ := dsInitCoreCost impl mMax G + 140 * G.n + 500 * G.m + 420

/-! ## Layout and Graph Helpers -/

lemma dsMEmbTempBase_eq (b L vCap eCap : ℕ) :
    dsMEmbTempBase b L vCap eCap =
      dsRevGenBase b L vCap eCap + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) +
        (vCap + 2 * eCap) := by
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase]
  omega

lemma dsInitCoreFrameCond_mono {L vCap eCap b h0 h1 h2 addr : ℕ}
    (hle : h1 ≤ h2) (h : dsInitCoreFrameCond L vCap eCap b h0 h2 addr) :
    dsInitCoreFrameCond L vCap eCap b h0 h1 addr := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr (le_trans hle hge)

lemma dsInitCoreFrameCond_to_lw {L vCap eCap b h0 h1 ret addr : ℕ}
    (hle : h0 ≤ h1) (h : dsInitCoreFrameCond L vCap eCap b h0 ret addr) :
    dsLevelWalksFrameCond L vCap eCap b 0 h1 ret addr := by
  refine ⟨h.1, by simpa using h.2.2.2.2.2.2.2.1,
    fun e he => by simpa using h.2.2.2.2.2.2.2.2.1 e he,
    fun e he => by simpa using h.2.2.2.2.2.2.2.2.2.1 e he,
    fun v hv => by simpa using h.2.2.2.2.2.2.2.2.2.2.1 v hv,
    fun v hv => by simpa using h.2.2.2.2.2.2.2.2.2.2.2.1 v hv,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with hlt | hge
  · exact Or.inl (lt_of_lt_of_le hlt hle)
  · exact Or.inr hge

private lemma dsAddrs_all {w L vCap eCap b heapPtr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hlt : heapPtr < 2 ^ w) :
    dsGPtr b < 2 ^ w ∧ dsHPtr b vCap eCap < 2 ^ w ∧ dsAuxPtr b vCap eCap < 2 ^ w ∧
    dsHHeadBase b vCap eCap < 2 ^ w ∧ dsHDegDummyBase b L vCap eCap < 2 ^ w ∧
    dsMEmbTempBase b L vCap eCap < 2 ^ w := by
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq b L vCap eCap
  have hg : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
  have hh : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
  have ha : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
  have hhd : dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap := rfl
  have hdg : dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap := rfl
  omega

end

end MinCostFlow.DynSpanner.Program
