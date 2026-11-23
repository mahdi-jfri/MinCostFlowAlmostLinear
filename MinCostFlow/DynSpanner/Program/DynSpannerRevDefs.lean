module

public import MinCostFlow.DynSpanner.Program.StateLayout
public import MinCostFlow.DynSpanner.Program.EmbLayouts
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reverse-index procedure definitions and address bounds (`DynSpannerRevDefs`)

Defines the deterministic Word-RAM reverse-adjacency procedures (`revProcs bOps bRev`:
`dsRevConsStmt` at `revIdxRevCons = 0` and `dsInsertWalkRevStmt` at `revIdxInsertWalk = 1`),
their contracts (`dsRevConsContract`, `dsInsertWalkRevContract`), and shared address bounds
(`isWalk_mem_V_tail_head`, `dsRevGen_ne_dsRevHead`, `dsAddrs_bound`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices -/

def revIdxRevCons : ℕ := 0
def revIdxInsertWalk : ℕ := 1

/-! ## Word-RAM statement bodies -/

/-- `args = [b, i, v, e, heapPtr]`: pushes `e` onto `revLists i v` (initializing `revHead[i, v]`
to `0` when `revGen[i, v] ≠ domGen[i]`) and returns `heapPtr + 2`. -/
def dsRevConsStmt : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 8 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 9) (.reg 6)))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 8))) ;;
  .assign 9 (.bin .add (.reg 8)
    (.bin .add (.bin .mul (.const 3) (.reg 6))
      (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1))))) ;;
  .assign 10 (.bin .add (.reg 9)
    (.bin .add (.bin .add (.reg 7) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))))) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 5))) ;;
  .assign 12 (.bin .add (.bin .mul (.reg 1) (.reg 5)) (.reg 2)) ;;
  .assign 13 (.bin .add (.reg 10) (.reg 12)) ;;
  .assign 14 (.bin .add (.reg 11) (.reg 12)) ;;
  .assign 8 (.load (.bin .add (.reg 9) (.reg 1))) ;;
  .assign 15 (.load (.reg 13)) ;;
  .cond (.bin .eq (.reg 15) (.reg 8))
    (.nop)
    (.store (.reg 13) (.reg 8) ;;
     .store (.reg 14) (.const 0)) ;;
  .assign 9 (.load (.reg 14)) ;;
  .store (.reg 4) (.reg 3) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 9) ;;
  .store (.reg 14) (.reg 4) ;;
  .ret (.bin .add (.reg 4) (.const 2))

/-- `args = [b, i, e, uStart, wPtr, hPtr, heapPtr]`: bumps `genCnt`, records `uStart` and each
walk destination vertex via `vStamp`, and pushes `e` onto each unique visited vertex's reverse
list at level `i`. Returns the new heap pointer. -/
def dsInsertWalkRevStmt (bOps bRev : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 10 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 7)) (.bin .mul (.const 9) (.reg 8)))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 10))) ;;
  .assign 10 (.bin .add (.reg 10)
    (.bin .add (.bin .mul (.const 3) (.reg 8))
      (.bin .mul (.const 2) (.bin .add (.reg 9) (.const 1))))) ;;
  .assign 10 (.bin .add (.reg 10)
    (.bin .add (.bin .add (.reg 9) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 8))))) ;;
  .assign 10 (.bin .add (.reg 10) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 7))) ;;
  .assign 10 (.bin .add (.reg 10)
    (.bin .add (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 7)))
      (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 9) (.const 1))) (.reg 7)))) ;;
  .assign 11 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 11) ;;
  .store (.bin .add (.reg 10) (.reg 3)) (.reg 11) ;;
  .call 6 (bRev + revIdxRevCons) [.reg 0, .reg 1, .reg 3, .reg 2, .reg 6] ;;
  .assign 12 (.load (.reg 4)) ;;
  forRange 13 (.const 0) (.reg 12)
    (.assign 14 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 13))) ;;
     .assign 15 (.load (.bin .add (.reg 4) (.reg 14))) ;;
     .assign 14 (.load (.bin .add (.bin .add (.reg 4) (.reg 14)) (.const 1))) ;;
     .cond (.reg 14)
       (.call 15 (bOps + dgIdxGetHead) [.reg 5, .reg 15])
       (.call 15 (bOps + dgIdxGetTail) [.reg 5, .reg 15]) ;;
     .assign 14 (.load (.bin .add (.reg 10) (.reg 15))) ;;
     .cond (.bin .eq (.reg 14) (.reg 11))
       (.nop)
       (.store (.bin .add (.reg 10) (.reg 15)) (.reg 11) ;;
        .call 6 (bRev + revIdxRevCons) [.reg 0, .reg 1, .reg 15, .reg 2, .reg 6])) ;;
  .ret (.reg 6)

/-- Reverse-index module (`2` deterministic procedures). -/
def revProcs (bOps bRev : ℕ) : List Stmt :=
  [ dsRevConsStmt
  , dsInsertWalkRevStmt bOps bRev ]

lemma revProcs_length (bOps bRev : ℕ) : (revProcs bOps bRev).length = 2 := rfl

lemma revProcs_noRand (bOps bRev : ℕ) : ∀ s ∈ revProcs bOps bRev, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts -/

/-- Contract for `dsRevConsStmt` (`[b, i, v, e, heapPtr]`). -/
def dsRevConsContract (w L vCap eCap b i v e : ℕ) (xs : List ℕ) (foot : ℕ → Prop) :
    Contract where
  pre args mem := ∃ heapPtr,
    args = [b, i, v, e, heapPtr] ∧
    16 ≤ 2 ^ w ∧ b + dsFixedSize L vCap eCap ≤ heapPtr ∧ heapPtr + 2 < 2 ^ w ∧
    i ≤ L ∧ v < vCap ∧ e < 2 ^ w ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    0 < mem (dsDomGenBase b L vCap eCap + i) ∧
    (∀ a, foot a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) ∧
    (if mem (dsRevGenBase b L vCap eCap + i * vCap + v) = mem (dsDomGenBase b L vCap eCap + i)
     then LinkedListIn foot mem (mem (dsRevHeadBase b L vCap eCap + i * vCap + v)) xs
     else xs = [])
  post args mem ret mem' := ∃ heapPtr,
    args = [b, i, v, e, heapPtr] ∧
    ret = heapPtr + 2 ∧
    mem' (dsRevGenBase b L vCap eCap + i * vCap + v) = mem (dsDomGenBase b L vCap eCap + i) ∧
    LinkedListIn (fun a => foot a ∨ a = heapPtr ∨ a = heapPtr + 1) mem'
      (mem' (dsRevHeadBase b L vCap eCap + i * vCap + v)) (e :: xs) ∧
    ∀ addr,
      addr ≠ dsRevGenBase b L vCap eCap + i * vCap + v →
      addr ≠ dsRevHeadBase b L vCap eCap + i * vCap + v →
      addr ≠ heapPtr → addr ≠ heapPtr + 1 → mem' addr = mem addr
  cost _ _ := 220

/-- Contract for `dsInsertWalkRevStmt` (`[b, i, e, uStart, wPtr, hPtr, heapPtr]`). -/
def dsInsertWalkRevContract (w L vCap eCap b i e uStart : ℕ)
    (H : MGraph) (W : List (ℕ × Bool)) (rev0 : ℕ → List ℕ) (foot0 : ℕ → Prop) : Contract where
  pre args mem := ∃ wPtr hPtr heapPtr,
    args = [b, i, e, uStart, wPtr, hPtr, heapPtr] ∧
    16 ≤ 2 ^ w ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapPtr + 2 * (W.length + 1) < 2 ^ w ∧
    i ≤ L ∧ e < 2 ^ w ∧ uStart < vCap ∧
    b + dsFixedSize L vCap eCap ≤ wPtr ∧ wPtr + (2 * W.length + 1) ≤ heapPtr ∧
    b + dsHdrSize ≤ hPtr ∧ hPtr + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    mem (b + dsGenOff) + 1 < 2 ^ w ∧
    0 < mem (dsDomGenBase b L vCap eCap + i) ∧
    (∀ v < vCap, mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    (∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) ∧
    DynGraphAt mem hPtr vCap eCap H ∧
    H.IsValid ∧ (∀ v ∈ H.V, v < vCap) ∧ (∀ e' ∈ H.E, e' < eCap) ∧
    uStart ∈ H.V ∧ (∃ vEnd, H.IsWalk uStart vEnd W) ∧
    MWalkAt mem wPtr W ∧
    (∀ v < vCap,
      if mem (dsRevGenBase b L vCap eCap + i * vCap + v) = mem (dsDomGenBase b L vCap eCap + i)
      then LinkedListIn foot0 mem (mem (dsRevHeadBase b L vCap eCap + i * vCap + v)) (rev0 v)
      else rev0 v = [])
  post args mem ret mem' := ∃ wPtr hPtr heapPtr,
    args = [b, i, e, uStart, wPtr, hPtr, heapPtr] ∧
    heapPtr + 2 ≤ ret ∧ ret ≤ heapPtr + 2 * (W.length + 1) ∧
    mem' (b + dsGenOff) = mem (b + dsGenOff) + 1 ∧
    (∀ v < vCap, mem' (dsVStampBase b L vCap eCap + v) ≤ mem' (b + dsGenOff)) ∧
    (∀ v < vCap,
      if v ∈ H.walkVertices uStart W then
        mem' (dsRevGenBase b L vCap eCap + i * vCap + v) = mem (dsDomGenBase b L vCap eCap + i) ∧
        LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < ret)) mem'
          (mem' (dsRevHeadBase b L vCap eCap + i * vCap + v)) (e :: rev0 v)
      else
        mem' (dsRevGenBase b L vCap eCap + i * vCap + v) =
          mem (dsRevGenBase b L vCap eCap + i * vCap + v) ∧
        mem' (dsRevHeadBase b L vCap eCap + i * vCap + v) =
          mem (dsRevHeadBase b L vCap eCap + i * vCap + v) ∧
        (if mem' (dsRevGenBase b L vCap eCap + i * vCap + v) =
            mem (dsDomGenBase b L vCap eCap + i)
         then LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < ret)) mem'
                (mem' (dsRevHeadBase b L vCap eCap + i * vCap + v)) (rev0 v)
         else rev0 v = [])) ∧
    ∀ addr,
      addr ≠ b + dsGenOff →
      (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) →
      (∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + i * vCap + v) →
      (∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + i * vCap + v) →
      (addr < heapPtr ∨ ret ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 380 * W.length + 450

end

/-! ## Shared address & walk helpers -/

public section

lemma isWalk_mem_V_tail_head {H : MGraph} (hVal : H.IsValid) :
    ∀ {u v : ℕ} {W : List (ℕ × Bool)}, u ∈ H.V → H.IsWalk u v W →
      ∀ x ∈ W, x.1 ∈ H.E ∧ H.dst x ∈ H.V
  | _, _, [], _, _, _, hx => by cases hx
  | _, _, x :: xs, _, .cons he _ hW, y, hy => by
    have hdstV : H.dst x ∈ H.V := by
      rcases x with ⟨e, b⟩
      cases b <;> [exact (hVal e he).1; exact (hVal e he).2]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨he, hdstV⟩
    · exact isWalk_mem_V_tail_head hVal hdstV hW y hy

lemma mul_add_lt_mul_succ {i L v vCap : ℕ} (hi : i ≤ L) (hv : v < vCap) :
    i * vCap + v < (L + 1) * vCap := by
  calc i * vCap + v < i * vCap + vCap := Nat.add_lt_add_left hv _
    _ = (i + 1) * vCap := by ring
    _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right vCap (Nat.succ_le_succ hi)

lemma dsRevGen_ne_dsRevHead {b L vCap eCap i v i' v' : ℕ}
    (hi : i ≤ L) (hv : v < vCap) :
    dsRevGenBase b L vCap eCap + i * vCap + v ≠
      dsRevHeadBase b L vCap eCap + i' * vCap + v' := by
  have hml := mul_add_lt_mul_succ hi hv
  have : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  omega

lemma dsAddrs_bound {w b L vCap eCap heapPtr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hlt : heapPtr < 2 ^ w) :
    4 + 7 * vCap + 9 * eCap = dynGraphSize vCap eCap ∧
    dynGraphSize vCap eCap < 2 ^ w ∧
    b + dsHdrSize + 3 * dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap < 2 ^ w ∧
    dsDomGenBase b L vCap eCap < 2 ^ w ∧
    dsEdgeDomGenBase b L vCap eCap < 2 ^ w ∧
    dsPiPtrBase b L vCap eCap < 2 ^ w ∧
    dsRevGenBase b L vCap eCap < 2 ^ w ∧
    dsRevHeadBase b L vCap eCap < 2 ^ w ∧
    dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap := by
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hdg_eq : 4 + 7 * vCap + 9 * eCap = dynGraphSize vCap eCap := rfl
  have hvs : dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hf]; simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  have haux : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap := by
    simp only [dsAuxPtr]; exact le_rfl
  have haux2 : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap := by
    simp only [dsMinHBase]; exact le_rfl
  have hdg_le_min : dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap := by omega
  have hmin_le : dsMinHBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := by omega
  refine ⟨hdg_eq, by omega, h1.symm, by omega, by omega, ?_, ?_, by omega, by omega, hvs, haux, haux2⟩
  · have : dsEdgeDomGenBase b L vCap eCap = dsDomGenBase b L vCap eCap + (L + 1) := rfl
    have : dsDomGenBase b L vCap eCap + (L + 1) ≤ dsRevGenBase b L vCap eCap := by omega
    omega
  · have : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
    omega

end


end MinCostFlow.DynSpanner.Program
