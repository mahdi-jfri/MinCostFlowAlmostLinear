module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutDefs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Level-walk and identity-embedding initialization procedures (`DynSpannerLevelWalks`)

Implements and verifies deterministic Word-RAM procedures (`levelWalkProcs bOps bRev`, length `3`)
using `DynSpannerRev` and `DynSpannerShortcutDefs`:
* `dsWriteIdEmbStmt` (`lwIdxWriteIdEmb = 0`): `O(G.m + 1)` materialization of `idEmb` at heap.
* `dsSetLevelWalksStmt` (`lwIdxSetLevelWalks = 1`): `O(|eL| + ∑_{e ∈ eL} (emb e).length + 1)`
  level rebuild setting `domGen`, `edgeDomGen`, `piPtr`, and all reverse buckets `revLists[lvl]`.
* `dsShortcutEmbStmt` (`lwIdxShortcutEmb = 2`): `O(|eL| + ∑_{e ∈ eL} (emb e).length + 1)`
  cycle-removal shortcutting of walks via stack/stamp pass.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices -/

def lwIdxWriteIdEmb : ℕ := 0
def lwIdxSetLevelWalks : ℕ := 1

/-! ## Word-RAM statement bodies -/

/-- `args = [gPtr, mEmbPtr, heapPtr]`: writes `MWalkAt` encodings of `[(e, true)]` for all
`e ∈ G.E` into `[heapPtr .. heapPtr + 3 * G.m)` and stores pointers into `mEmbPtr[e]`. -/
def dsWriteIdEmbStmt : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 6 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 3))) (.reg 4)) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.load (.bin .add (.reg 6) (.reg 7))) ;;
     .store (.reg 2) (.const 1) ;;
     .store (.bin .add (.reg 2) (.const 1)) (.reg 8) ;;
     .store (.bin .add (.reg 2) (.const 2)) (.const 1) ;;
     .store (.bin .add (.reg 1) (.reg 8)) (.reg 2) ;;
     .assign 2 (.bin .add (.reg 2) (.const 3))) ;;
  .ret (.reg 2)

/-- `args = [b, lvl, eListPtr, numEdges, mEmbPtr, heapPtr]`: bumps `domGen[lvl]` to a fresh
generation, sets `edgeDomGen[lvl, e]`, `piPtr[lvl, e] := mEmbPtr[e]`, and inserts each `e`
into `revLists lvl v` along `mEmbPtr[e]`. Returns the new heap pointer. -/
def dsSetLevelWalksStmt (bOps bRev : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 9 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 6)) (.bin .mul (.const 9) (.reg 7)))) ;;
  .assign 10 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 9)) ;;
  .assign 9 (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 9))) ;;
  .assign 9 (.bin .add (.reg 9)
    (.bin .add (.bin .mul (.const 3) (.reg 7))
      (.bin .mul (.const 2) (.bin .add (.reg 8) (.const 1))))) ;;
  .assign 12 (.bin .add (.reg 9) (.bin .add (.reg 8) (.const 1))) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.bin .add (.reg 8) (.const 1)) (.reg 7))) ;;
  .assign 8 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 8) ;;
  .store (.bin .add (.reg 9) (.reg 1)) (.reg 8) ;;
  forRange 6 (.const 0) (.reg 3)
    (.assign 9 (.load (.bin .add (.reg 2) (.reg 6))) ;;
     .assign 14 (.bin .add (.bin .mul (.reg 1) (.reg 7)) (.reg 9)) ;;
     .store (.bin .add (.reg 12) (.reg 14)) (.reg 8) ;;
     .assign 15 (.load (.bin .add (.reg 4) (.reg 9))) ;;
     .store (.bin .add (.reg 13) (.reg 14)) (.reg 15) ;;
     .call 14 (bOps + dgIdxGetTail) [.reg 10, .reg 9] ;;
     .call 5 (bRev + revIdxInsertWalk) [.reg 0, .reg 1, .reg 9, .reg 14, .reg 15, .reg 11, .reg 5]) ;;
  .ret (.reg 5)

/-- Level-walk initialization module (`3` deterministic procedures). -/
def levelWalkProcs (bOps bRev : ℕ) : List Stmt :=
  [dsWriteIdEmbStmt, dsSetLevelWalksStmt bOps bRev, dsShortcutEmbStmt bOps]

lemma levelWalkProcs_length (bOps bRev : ℕ) : (levelWalkProcs bOps bRev).length = 3 := rfl

lemma levelWalkProcs_noRand (bOps bRev : ℕ) : ∀ s ∈ levelWalkProcs bOps bRev, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · exact dsShortcutEmbStmt_noRand bOps
  cases hs

/-! ## Contracts -/

/-- Contract for `dsWriteIdEmbStmt` (`[gPtr, mEmbPtr, heapPtr]`). -/
def dsWriteIdEmbContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr mEmbPtr heapPtr,
    args = [gPtr, mEmbPtr, heapPtr] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    mEmbPtr + eCap < 2 ^ w ∧ heapPtr + 3 * G.m < 2 ^ w ∧
    (∀ k < dynGraphSize vCap eCap,
      (gPtr + k < mEmbPtr ∨ mEmbPtr + eCap ≤ gPtr + k) ∧
      (gPtr + k < heapPtr ∨ heapPtr + 3 * G.m ≤ gPtr + k)) ∧
    (mEmbPtr + eCap ≤ heapPtr ∨ heapPtr + 3 * G.m ≤ mEmbPtr) ∧
    DynGraphAt mem gPtr vCap eCap G ∧
    (∀ e ∈ G.E, e < eCap)
  post args mem ret mem' := ∃ gPtr mEmbPtr heapPtr,
    args = [gPtr, mEmbPtr, heapPtr] ∧
    ret = heapPtr + 3 * G.m ∧
    MEmbAt mem' mEmbPtr G.E eCap idEmb ∧
    (∀ e ∈ G.E, heapPtr ≤ mem' (mEmbPtr + e) ∧ mem' (mEmbPtr + e) + 3 ≤ heapPtr + 3 * G.m) ∧
    ∀ addr,
      (addr < mEmbPtr ∨ mEmbPtr + eCap ≤ addr) →
      (addr < heapPtr ∨ heapPtr + 3 * G.m ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 60 * G.m + 45

/-- Predicate stating `addr` is outside the fields modified by `dsSetLevelWalksStmt`. -/
def dsLevelWalksFrameCond (L vCap eCap b lvl heapPtr ret addr : ℕ) : Prop :=
  addr ≠ b + dsGenOff ∧
  addr ≠ dsDomGenBase b L vCap eCap + lvl ∧
  (∀ e < eCap, addr ≠ dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) ∧
  (∀ e < eCap, addr ≠ dsPiPtrBase b L vCap eCap + lvl * eCap + e) ∧
  (∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + lvl * vCap + v) ∧
  (∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + lvl * vCap + v) ∧
  (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) ∧
  (addr < heapPtr ∨ ret ≤ addr)

/-- Contract for `dsSetLevelWalksStmt` (`[b, lvl, eListPtr, numEdges, mEmbPtr, heapPtr]`). -/
def dsSetLevelWalksContract (w L vCap eCap b lvl : ℕ)
    (G H : MGraph) (eL : List ℕ) (emb : MinCostFlow.Embedding) (foot0 : ℕ → Prop) : Contract where
  pre args mem := ∃ eListPtr mEmbPtr heapPtr,
    let heapMax := heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum
    args = [b, lvl, eListPtr, eL.length, mEmbPtr, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ b ∧ lvl ≤ L ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapMax < 2 ^ w ∧
    eListPtr + eL.length < 2 ^ w ∧ mEmbPtr + eCap < 2 ^ w ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    mem (b + dsGenOff) + 1 + eL.length < 2 ^ w ∧
    (∀ v < vCap, mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    (∀ e < eCap, mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) ≤ mem (b + dsGenOff)) ∧
    (∀ v < vCap, mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) ≤ mem (b + dsGenOff)) ∧
    (∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) ∧
    (∀ k < eL.length, dsLevelWalksFrameCond L vCap eCap b lvl heapPtr heapMax (eListPtr + k)) ∧
    (∀ e ∈ eL, dsLevelWalksFrameCond L vCap eCap b lvl heapPtr heapMax (mEmbPtr + e)) ∧
    eL.Nodup ∧ ListAt mem eListPtr eL ∧
    DynGraphAt mem (dsGPtr b) vCap eCap G ∧ G.IsValid ∧
    (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap H ∧ H.IsValid ∧
    G.V ⊆ H.V ∧
    (∀ v ∈ H.V, v < vCap) ∧ (∀ e ∈ H.E, e < eCap) ∧
    (∀ e ∈ eL, e ∈ G.E ∧ H.IsWalk (G.tail e) (G.head e) (emb e) ∧
      MWalkAt mem (mem (mEmbPtr + e)) (emb e) ∧
      b + dsFixedSize L vCap eCap ≤ mem (mEmbPtr + e) ∧
      mem (mEmbPtr + e) + (mWalkEncode (emb e)).length ≤ heapPtr)
  post args mem ret mem' := ∃ eListPtr mEmbPtr heapPtr,
    args = [b, lvl, eListPtr, eL.length, mEmbPtr, heapPtr] ∧
    heapPtr ≤ ret ∧
    ret ≤ heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum ∧
    mem' (b + dsGenOff) = mem (b + dsGenOff) + 1 + eL.length ∧
    mem' (dsDomGenBase b L vCap eCap + lvl) = mem (b + dsGenOff) + 1 ∧
    (∀ v < vCap, mem' (dsVStampBase b L vCap eCap + v) ≤ mem' (b + dsGenOff)) ∧
    (∀ e < eCap, mem' (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) ≤ mem' (b + dsGenOff)) ∧
    (∀ e < eCap,
      (0 < mem' (dsDomGenBase b L vCap eCap + lvl) ∧
       mem' (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) =
         mem' (dsDomGenBase b L vCap eCap + lvl)) ↔ e ∈ eL) ∧
    (∀ e ∈ eL,
      mem' (dsPiPtrBase b L vCap eCap + lvl * eCap + e) = mem (mEmbPtr + e) ∧
      MWalkAt mem' (mem' (dsPiPtrBase b L vCap eCap + lvl * eCap + e)) (emb e)) ∧
    (∃ rev' : ℕ → List ℕ, ∀ v < vCap,
      mem' (dsRevGenBase b L vCap eCap + lvl * vCap + v) ≤ mem' (b + dsGenOff) ∧
      (rev' v).Nodup ∧
      (∀ e, e ∈ rev' v ↔ e ∈ eL ∧ v ∈ H.walkVertices (G.tail e) (emb e)) ∧
      (if 0 < mem' (dsDomGenBase b L vCap eCap + lvl) ∧
          mem' (dsRevGenBase b L vCap eCap + lvl * vCap + v) =
            mem' (dsDomGenBase b L vCap eCap + lvl)
       then LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < ret)) mem'
              (mem' (dsRevHeadBase b L vCap eCap + lvl * vCap + v)) (rev' v)
       else rev' v = [])) ∧
    ∀ addr, dsLevelWalksFrameCond L vCap eCap b lvl heapPtr ret addr → mem' addr = mem addr
  cost _ _ := 400 * (eL.map fun e => (emb e).length).sum + 620 * eL.length + 220

lemma dsLevelWalksFrameCond_mono {L vCap eCap b lvl h0 h1 h2 addr : ℕ}
    (hle : h1 ≤ h2) (hfr : dsLevelWalksFrameCond L vCap eCap b lvl h0 h2 addr) :
    dsLevelWalksFrameCond L vCap eCap b lvl h0 h1 addr := by
  rcases hfr with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  refine ⟨a1, a2, a3, a4, a5, a6, a7, ?_⟩
  rcases a8 with h | h <;> [exact Or.inl h; exact Or.inr (le_trans hle h)]

lemma dsLevelWalksFrameCond_lt_domGen {L vCap eCap b lvl h0 ret addr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ h0)
    (hb : addr < dsDomGenBase b L vCap eCap) (hne : addr ≠ b + dsGenOff) :
    dsLevelWalksFrameCond L vCap eCap b lvl h0 ret addr := by
  have hf := dsFixedSize_add b L vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hvs : dsDomGenBase b L vCap eCap ≤ dsVStampBase b L vCap eCap := by omega
  have he1 : dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap := by
    simp [dsEdgeDomGenBase]
  have he2 : dsDomGenBase b L vCap eCap ≤ dsPiPtrBase b L vCap eCap := by
    simp [dsPiPtrBase, dsEdgeDomGenBase]; omega
  have hr1 : dsDomGenBase b L vCap eCap ≤ dsRevGenBase b L vCap eCap := by omega
  have hr2 : dsDomGenBase b L vCap eCap ≤ dsRevHeadBase b L vCap eCap := by omega
  have hdom_le : dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hf]
    simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase,
      dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]
    omega
  have h_le_fixed : addr < b + dsFixedSize L vCap eCap := lt_of_lt_of_le hb hdom_le
  exact ⟨hne, by omega, fun e _ => by omega, fun e _ => by omega,
    fun v _ => by omega, fun v _ => by omega, fun v _ => by omega, Or.inl (lt_of_lt_of_le h_le_fixed hfix)⟩

lemma dsLevelWalksFrameCond_mEmbTemp {L vCap eCap b lvl h0 ret e : ℕ}
    (hlvl : lvl ≤ L) (hfix : b + dsFixedSize L vCap eCap ≤ h0) (he : e < eCap) :
    dsLevelWalksFrameCond L vCap eCap b lvl h0 ret (dsMEmbTempBase b L vCap eCap + e) := by
  have hf := dsFixedSize_add b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hmt : dsVStampBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap := by
    simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  have hdg : dsDomGenBase b L vCap eCap ≤ dsRevGenBase b L vCap eCap := by omega
  have hed : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsPiPtrBase b L vCap eCap := by
    simp [dsPiPtrBase]
  have hpi : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hrg : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  have hgen_lt : b + dsGenOff < dsMEmbTempBase b L vCap eCap + e := by
    simp only [dsGenOff, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
      dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
      dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
      dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr, dsHdrSize]
    omega
  have hm_e : ∀ e' < eCap, lvl * eCap + e' < (L + 1) * eCap := fun e' he' => by
    calc lvl * eCap + e' < lvl * eCap + eCap := Nat.add_lt_add_left he' _
      _ = (lvl + 1) * eCap := by ring
      _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvl)
  have hm_v : ∀ v < vCap, lvl * vCap + v < (L + 1) * vCap := fun v hv => by
    calc lvl * vCap + v < lvl * vCap + vCap := Nat.add_lt_add_left hv _
      _ = (lvl + 1) * vCap := by ring
      _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right vCap (Nat.succ_le_succ hlvl)
  refine ⟨Nat.ne_of_gt hgen_lt, by omega,
    fun e' he' => by have := hm_e e' he'; omega,
    fun e' he' => by have := hm_e e' he'; omega,
    fun v hv => by have := hm_v v hv; omega,
    fun v hv => by have := hm_v v hv; omega,
    fun v hv => by omega,
    Or.inl (by omega)⟩

lemma dsLevelWalksFrameCond_heap_lt {L vCap eCap b lvl h0 ret addr : ℕ}
    (hlvl : lvl ≤ L) (hle : b + dsFixedSize L vCap eCap ≤ addr) (hlt : addr < h0) :
    dsLevelWalksFrameCond L vCap eCap b lvl h0 ret addr := by
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hvs : dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hf]; simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  have hed : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsPiPtrBase b L vCap eCap := by
    simp [dsPiPtrBase]
  have hpi : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hrg : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  have hgen_lt : b + dsGenOff < b + dsFixedSize L vCap eCap := by
    simp only [dsGenOff, dsHdrSize] at *; omega
  refine ⟨by omega, by omega, fun e he => ?_, fun e he => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => by omega, Or.inl hlt⟩
  · have hm : lvl * eCap + e < (L + 1) * eCap := by
      calc lvl * eCap + e < lvl * eCap + eCap := Nat.add_lt_add_left he _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvl)
    omega
  · have hm : lvl * eCap + e < (L + 1) * eCap := by
      calc lvl * eCap + e < lvl * eCap + eCap := Nat.add_lt_add_left he _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvl)
    omega
  · have hm : lvl * vCap + v < (L + 1) * vCap := by
      calc lvl * vCap + v < lvl * vCap + vCap := Nat.add_lt_add_left hv _
        _ = (lvl + 1) * vCap := by ring
        _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right vCap (Nat.succ_le_succ hlvl)
    omega
  · have hm : lvl * vCap + v < (L + 1) * vCap := by
      calc lvl * vCap + v < lvl * vCap + vCap := Nat.add_lt_add_left hv _
        _ = (lvl + 1) * vCap := by ring
        _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right vCap (Nat.succ_le_succ hlvl)
    omega

private lemma getElem_not_mem_take {α : Type*} {xs : List α} (hnd : xs.Nodup) {k : ℕ}
    (hk : k < xs.length) : xs[k]'hk ∉ xs.take k := by
  intro hmem
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨j, hj_len, hj_eq⟩
  have hj_k : j < k := by rw [List.length_take] at hj_len; omega
  have hj_xs : j < xs.length := lt_trans hj_k hk
  rw [List.getElem_take] at hj_eq
  have : j = k := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨j, hj_xs⟩) (a₂ := ⟨k, hk⟩)
    (by simpa using hj_eq) |> fun h => by simpa using h
  omega

end

public section

lemma rangeCost_setWalks (eL : List ℕ) (emb : MinCostFlow.Embedding) :
    rangeCost (fun k => match eL[k]? with | some e => 380 * (emb e).length + 540 | none => 0)
      0 eL.length = 380 * (eL.map fun e => (emb e).length).sum + 540 * eL.length := by
  rw [rangeCost_zero_eq_range]
  induction eL with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getElem?_cons_zero,
      List.sum_cons]
    have hmap : (List.map Nat.succ (List.range xs.length)).map
        (fun k => match (x :: xs)[k]? with | some e => 380 * (emb e).length + 540 | none => 0) =
        (List.range xs.length).map
          (fun k => match xs[k]? with | some e => 380 * (emb e).length + 540 | none => 0) := by
      simp [List.map_map, Function.comp_def]
    rw [hmap, ih]
    ring

lemma take_succ_sum_walks (eL : List ℕ) (emb : MinCostFlow.Embedding)
    {k : ℕ} (hk : k < eL.length) :
    ((eL.take (k + 1)).map fun e => (emb e).length + 1).sum =
      ((eL.take k).map fun e => (emb e).length + 1).sum + ((emb (eL[k]'hk)).length + 1) := by
  rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append]
  simp

lemma take_sum_walks_le (eL : List ℕ) (emb : MinCostFlow.Embedding) (k : ℕ) :
    ((eL.take k).map fun e => (emb e).length + 1).sum ≤
      (eL.map fun e => (emb e).length + 1).sum := by
  have hp : eL.take k <+: eL := List.take_prefix k eL
  obtain ⟨t, ht⟩ := hp
  conv_rhs => rw [← ht, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- Loop invariant for `dsSetLevelWalksStmt` (`forRange 6 0 eL.length`). -/
@[expose] def dsSetLevelWalksInv (L vCap eCap b lvl eListPtr mEmbPtr heapPtr gen0 : ℕ)
    (G H : MGraph) (eL : List ℕ) (emb : MinCostFlow.Embedding) (foot0 : ℕ → Prop)
    (mem : ℕ → ℕ) (k : ℕ) (st : State) : Prop :=
  let domAddr := dsDomGenBase b L vCap eCap + lvl
  let footOf (heapCur : ℕ) (a : ℕ) : Prop := foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)
  ∃ (heapCur : ℕ) (revCur : ℕ → List ℕ),
    heapPtr ≤ heapCur ∧
    heapCur ≤ heapPtr + 2 * ((eL.take k).map fun e => (emb e).length + 1).sum ∧
    st.regs 0 = b ∧ st.regs 1 = lvl ∧ st.regs 2 = eListPtr ∧ st.regs 3 = eL.length ∧
    st.regs 4 = mEmbPtr ∧ st.regs 5 = heapCur ∧ st.regs 6 = k ∧
    st.regs 7 = eCap ∧ st.regs 8 = gen0 + 1 ∧ st.regs 10 = dsGPtr b ∧
    st.regs 11 = dsHPtr b vCap eCap ∧ st.regs 12 = dsEdgeDomGenBase b L vCap eCap ∧
    st.regs 13 = dsPiPtrBase b L vCap eCap ∧
    st.mem (b + dsGenOff) = gen0 + 1 + k ∧
    st.mem domAddr = gen0 + 1 ∧
    (∀ v < vCap, st.mem (dsVStampBase b L vCap eCap + v) ≤ st.mem (b + dsGenOff)) ∧
    (∀ e < eCap, st.mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) ≤ st.mem (b + dsGenOff)) ∧
    (∀ e < eCap, st.mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) = gen0 + 1 ↔ e ∈ eL.take k) ∧
    (∀ e ∈ eL.take k,
      st.mem (dsPiPtrBase b L vCap eCap + lvl * eCap + e) = mem (mEmbPtr + e) ∧
      MWalkAt st.mem (st.mem (dsPiPtrBase b L vCap eCap + lvl * eCap + e)) (emb e)) ∧
    (∀ v < vCap,
      st.mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) ≤ st.mem (b + dsGenOff) ∧
      (revCur v).Nodup ∧
      (∀ e, e ∈ revCur v ↔ e ∈ eL.take k ∧ v ∈ H.walkVertices (G.tail e) (emb e)) ∧
      (if 0 < st.mem domAddr ∧ st.mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) = st.mem domAddr
       then LinkedListIn (footOf heapCur) st.mem
              (st.mem (dsRevHeadBase b L vCap eCap + lvl * vCap + v)) (revCur v)
       else revCur v = [])) ∧
    ∀ addr, dsLevelWalksFrameCond L vCap eCap b lvl heapPtr heapCur addr → st.mem addr = mem addr

end

end MinCostFlow.DynSpanner.Program
