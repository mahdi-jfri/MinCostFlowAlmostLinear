module

public import MinCostFlow.SparseCore.Program.LSFWindowReloc
public import MinCostFlow.DynSpanner.Program.MergeSort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Canonical Guest Memory Builder Procedures (`LSFWindowBuildDefs`)

Defines the deterministic Word-RAM procedures that construct `canonGuestMem G₀ ℓ₀ h L_in P_fp`
at `[guestBase, guestBase + canonHandlesOut G₀ L_in)` in fresh zeroed host memory from a host
`DynGraphAt mem g0Ptr vCap0 eCap0 G₀` and edge-length array `lenArr` in
`O(n₀ log(n₀ + 1) + m₀ log(m₀ + 1) + m₀ * L_in + 1)` time (no `vCap` or `eCap` scan):

* `pushHalfEdgeProc`: prepends half-edge `he` to incidence list of slot `s` at base `guestBase`.
* `maxListProc`: computes `max_{i < len} mem[arr + i] + 1` (or `1` if `len = 0`).
* `buildCanonVertsProc`: populates `vPres`, `vPos`, `extToInt`, `intToExt` from sorted `vList`.
* `buildCanonEdgesProc`: populates `ePres`, `ePos`, `eTailSlot`, `eHeadSlot` and copies `L_in`
  limbs per edge from `lenArr`.
* `buildCanonIncProc`: builds the canonical doubly-linked incidence lists by calling
  `pushHalfEdgeProc` in `canonEList G₀` order.
* `buildCanonGuestProc`: orchestrates the five steps using `sortProcs`, `memCopyStmt`, and
  `memFillStmt`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## Procedure definitions -/

/-- Prepend half-edge `he` to the doubly-linked incidence list of slot `s` in a `DynGraphAt`
starting at `base` with capacities `(vCap, eCap)`. Args: `[base, vCap, eCap, s, he]`. -/
def pushHalfEdgeProc : Stmt :=
  .assign 5 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 1))) (.reg 3)) ;;
  .assign 6 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 1))) (.reg 3)) ;;
  .assign 7 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 1)))
    (.bin .mul (.const 5) (.reg 2))) ;;
  .assign 8 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 1)))
    (.bin .mul (.const 7) (.reg 2))) ;;
  .assign 9 (.load (.reg 5)) ;;
  .assign 10 (.load (.reg 6)) ;;
  .store (.bin .add (.reg 7) (.reg 4)) (.const 0) ;;
  .store (.bin .add (.reg 8) (.reg 4)) (.reg 9) ;;
  .cond (.bin .lt (.const 0) (.reg 9))
    (.store (.bin .add (.reg 7) (.bin .sub (.reg 9) (.const 1))) (.bin .add (.reg 4) (.const 1)))
    .nop ;;
  .store (.reg 5) (.bin .add (.reg 4) (.const 1)) ;;
  .store (.reg 6) (.bin .add (.reg 10) (.const 1)) ;;
  .ret (.const 0)

/-- Compute `max 1 (max_{i < len} mem[arr + i] + 1)` (equals `1` if `len = 0`).
Args: `[arr, len]`. -/
def maxCapListProc : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.ret (.const 1))
    (.assign 2 (.const 0) ;;
     forRange 3 (.const 0) (.reg 1)
       (.assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
        .cond (.bin .lt (.reg 2) (.reg 4))
          (.assign 2 (.reg 4))
          .nop) ;;
     .ret (.bin .add (.reg 2) (.const 1)))

/-- Populate `vPres`, `vPos`, `extToInt`, `intToExt` at `guestBase` from the sorted vertex list
already stored at `dgVListBase guestBase vCap`. Args: `[guestBase, vCap, n0]`. -/
def buildCanonVertsProc : Stmt :=
  .assign 3 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 1)) ;;
  .assign 4 (.bin .add (.reg 0) (.const 4)) ;;
  .assign 5 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 2) (.reg 1))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 1))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 1))) ;;
  forRange 8 (.const 0) (.reg 2)
    (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
     .store (.bin .add (.reg 4) (.reg 9)) (.const 1) ;;
     .store (.bin .add (.reg 5) (.reg 9)) (.reg 8) ;;
     .store (.bin .add (.reg 6) (.reg 9)) (.reg 9) ;;
     .store (.bin .add (.reg 7) (.reg 9)) (.reg 9)) ;;
  .ret (.const 0)

/-- Populate `ePres`, `ePos`, `eTailSlot`, `eHeadSlot` at `guestBase` and copy `L_in` edge-length
limbs per edge into `dstLenArr` from the sorted edge list already stored at
`dgEListBase guestBase vCap_can eCap_can`.
Args: `[g0Ptr, lenArr, L_in, guestBase, vCap_can, eCap_can, m0, dstLenArr]`. -/
def buildCanonEdgesProc (bCopy : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 8))) ;;
  .assign 11 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 8)))
    (.bin .mul (.const 3) (.reg 9))) ;;
  .assign 12 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 8)))
    (.bin .mul (.const 4) (.reg 9))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 3) (.const 4)) (.bin .mul (.const 7) (.reg 4))) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 5)) ;;
  .assign 15 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 5))) ;;
  .assign 16 (.bin .add (.reg 13) (.bin .mul (.const 3) (.reg 5))) ;;
  .assign 17 (.bin .add (.reg 13) (.bin .mul (.const 4) (.reg 5))) ;;
  forRange 18 (.const 0) (.reg 6)
    (.assign 19 (.load (.bin .add (.reg 14) (.reg 18))) ;;
     .assign 20 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 11) (.reg 19))))) ;;
     .assign 21 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 19))))) ;;
     .store (.bin .add (.reg 13) (.reg 19)) (.const 1) ;;
     .store (.bin .add (.reg 15) (.reg 19)) (.reg 18) ;;
     .store (.bin .add (.reg 16) (.reg 19)) (.reg 20) ;;
     .store (.bin .add (.reg 17) (.reg 19)) (.reg 21) ;;
     .call 22 bCopy
       [.bin .add (.reg 7) (.bin .mul (.reg 19) (.reg 2)),
        .bin .add (.reg 1) (.bin .mul (.reg 19) (.reg 2)),
        .reg 2]) ;;
  .ret (.const 0)

/-- Populate canonical incidence lists at `guestBase` by pushing `(2 * e)` and `(2 * e + 1)`
in `canonEList G₀` order. Args: `[guestBase, vCap_can, eCap_can, m0]`. -/
def buildCanonIncProc (bPush : ℕ) : Stmt :=
  .assign 4 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 1))) (.reg 2)) ;;
  .assign 5 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 1)))
    (.bin .mul (.const 3) (.reg 2))) ;;
  .assign 6 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 1)))
    (.bin .mul (.const 4) (.reg 2))) ;;
  forRange 7 (.const 0) (.reg 3)
    (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .assign 9 (.load (.bin .add (.reg 5) (.reg 8))) ;;
     .assign 10 (.load (.bin .add (.reg 6) (.reg 8))) ;;
     .call 11 bPush [.reg 0, .reg 1, .reg 2, .reg 9, .bin .mul (.const 2) (.reg 8)] ;;
     .call 11 bPush [.reg 0, .reg 1, .reg 2, .reg 10, .bin .add (.bin .mul (.const 2) (.reg 8)) (.const 1)]) ;;
  .ret (.const 0)

/-- Top-level builder of `canonGuestMem` at `[guestBase, guestBase + canonHandlesOut G₀ L_in)`.
Args: `[g0Ptr, lenArr, L_in, guestBase]`. Returns `0`. -/
def buildCanonGuestProc (bSort bCopy bFill bMaxCap bVerts bEdges bInc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 4)) ;;
  .assign 9 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 4))) (.reg 5)) ;;
  .call 10 bMaxCap [.reg 8, .reg 6] ;;
  .call 11 bMaxCap [.reg 9, .reg 7] ;;
  .store (.bin .add (.reg 3) (.const dgVCapOff)) (.reg 10) ;;
  .store (.bin .add (.reg 3) (.const dgECapOff)) (.reg 11) ;;
  .store (.bin .add (.reg 3) (.const dgNOff)) (.reg 6) ;;
  .store (.bin .add (.reg 3) (.const dgMOff)) (.reg 7) ;;
  .assign 12 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 4)) (.bin .mul (.const 7) (.reg 10)))
    (.bin .mul (.const 9) (.reg 11))) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.reg 11) (.reg 2))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 3) (.const 4)) (.reg 10)) ;;
  .call 15 bCopy [.reg 14, .reg 8, .reg 6] ;;
  .call 15 (bSort + sortIdxMergeSort) [.reg 14, .reg 6, .reg 13] ;;
  .call 15 bFill [.reg 13, .reg 6, .const 0] ;;
  .call 15 bVerts [.reg 3, .reg 10, .reg 6] ;;
  .assign 14 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 4)) (.bin .mul (.const 7) (.reg 10))) (.reg 11)) ;;
  .call 15 bCopy [.reg 14, .reg 9, .reg 7] ;;
  .call 15 (bSort + sortIdxMergeSort) [.reg 14, .reg 7, .reg 13] ;;
  .call 15 bFill [.reg 13, .reg 7, .const 0] ;;
  .call 15 bEdges [.reg 0, .reg 1, .reg 2, .reg 3, .reg 10, .reg 11, .reg 7, .reg 12] ;;
  .call 15 bInc [.reg 3, .reg 10, .reg 11, .reg 7] ;;
  .ret (.const 0)

def canonBuildProcs (bBuild bSort bCopy bFill : ℕ) : List Stmt :=
  [pushHalfEdgeProc,
   maxCapListProc,
   buildCanonVertsProc,
   buildCanonEdgesProc bCopy,
   buildCanonIncProc (bBuild + 0),
   buildCanonGuestProc bSort bCopy bFill (bBuild + 1) (bBuild + 2) (bBuild + 3) (bBuild + 4)]

lemma canonBuildProcs_length (bBuild bSort bCopy bFill : ℕ) :
    (canonBuildProcs bBuild bSort bCopy bFill).length = 6 := rfl

lemma canonBuildProcs_noRand (bBuild bSort bCopy bFill : ℕ) :
    ∀ s ∈ canonBuildProcs bBuild bSort bCopy bFill, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · simp [pushHalfEdgeProc, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [maxCapListProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [buildCanonVertsProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [buildCanonEdgesProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [buildCanonIncProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [buildCanonGuestProc, Stmt.NoRand]
  cases hs

/-! ## Pure list/Finset helpers for sorting and max-capacity -/

lemma eq_finset_sort_of_perm {S : Finset ℕ} {L L' : List ℕ}
    (hnd : L.Nodup) (hmem : ∀ x, x ∈ L ↔ x ∈ S)
    (hperm : L'.Perm L) (hpair : L'.Pairwise (· ≤ ·)) :
    L' = S.sort (· ≤ ·) := by
  have hnd' : L'.Nodup := hperm.nodup_iff.mpr hnd
  have hmem' : ∀ x, x ∈ L' ↔ x ∈ S.sort (· ≤ ·) := fun x => by
    rw [hperm.mem_iff, hmem x, S.mem_sort (· ≤ ·)]
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ => le_antisymm) hpair (S.pairwise_sort (· ≤ ·))
    ((List.perm_ext_iff_of_nodup hnd' (S.sort_nodup (· ≤ ·))).mpr hmem')

lemma foldl_max_eq_finset_sup {S : Finset ℕ} {L : List ℕ}
    (hmem : ∀ x, x ∈ L ↔ x ∈ S) :
    L.foldl max 0 = S.sup id := by
  have hfold_le : ∀ (xs : List ℕ) (init : ℕ),
      (∀ x ∈ xs, x ≤ xs.foldl max init) ∧ init ≤ xs.foldl max init := by
    intro xs
    induction xs with
    | nil => intro init; exact ⟨(fun _ h => nomatch h), le_rfl⟩
    | cons x xs ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (max init x)
      refine ⟨fun y hy => ?_, le_trans (le_max_left _ _) h2⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact le_trans (le_max_right _ _) h2
      · exact h1 y hy'
  have hfold_ub : ∀ (xs : List ℕ) (init M : ℕ),
      init ≤ M → (∀ x ∈ xs, x ≤ M) → xs.foldl max init ≤ M := by
    intro xs
    induction xs with
    | nil => intro init M h _; exact h
    | cons x xs ih =>
      intro init M h hxs
      exact ih (max init x) M (max_le h (hxs x List.mem_cons_self))
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
  apply le_antisymm
  · exact hfold_ub L 0 (S.sup id) (Nat.zero_le _)
      (fun x hx => Finset.le_sup (f := id) ((hmem x).mp hx))
  · exact Finset.sup_le fun x hx => (hfold_le L 0).1 x ((hmem x).mpr hx)

/-- Cost bound for `buildCanonGuestProc`. -/
def buildCanonGuestCost (n0 m0 L_in : ℕ) : ℕ :=
  250 * n0 * (Nat.log 2 (n0 + 1) + 1) +
  250 * m0 * (Nat.log 2 (m0 + 1) + 1) +
  30 * m0 * L_in + 400 * n0 + 600 * m0 + 1000

end MinCostFlow.SparseCore.Program
