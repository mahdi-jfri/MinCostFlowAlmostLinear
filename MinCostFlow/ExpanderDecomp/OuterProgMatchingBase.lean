module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OuterMatching
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.OuterProgSubgraphOps
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Matching-Level Word-RAM Procedures for the Outer Cut-Matching Game (`OuterProgMatching`)

Implements and verifies the three deterministic (`NoRand`), linear-time port-array procedures used
inside each round of the outer cut-matching game:

1. `padToBisectionProc`: given a port cut `U ⊆ range (2 * e)`, computes `(A, B) = padToBisection e U`
   exact to the model and writes `SinglePairAt` at `outPairsAddr` in `O(e + |U| + 1)` time and
   `2 * e` heap words.
2. `buildInjPairProc`: given a port subset `S ⊆ range (2 * e)`, computes the injection terminal pair
   `((range (2 * e) \ S).sort (· ≤ ·), S)` and writes `SinglePairAt` at `outPairsAddr` in
   `O(e + |S| + 1)` time and `2 * e` heap words.
3. `fakeCompletionProc`: given a single terminal pair `(A, B)` in `SinglePairAt` format and a partial
   matching `M`, computes `OuterMatching.fakeCompletion A B M` bit-for-bit identically at `outFAddr`
   with length at `outLenAddr` in `O(e + |M| + 1)` time and `8 * e` heap words.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited

/-! ## 1. `padToBisectionProc` -/

/-- Heap scratch space (words) for `padToBisectionProc`. -/
def padToBisectionSpace (e : ℕ) : ℕ := 2 * e

/-- Step bound for `padToBisectionProc`: `O(e + kU + 1)`. -/
def padToBisectionCost (e kU : ℕ) : ℕ := 260 * e + 60 * kU + 160

/-- Pass 1 of `padToBisectionProc`: collect ports in the smaller side `C` into `aBase`. -/
def padPass1Stmt : Stmt :=
  .assign 11 (.const 0) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .cond (.bin .eq (.reg 8) (.reg 6))
       (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
        .assign 11 (.bin .add (.reg 11) (.const 1)))
       .nop)

/-- Pass 2 of `padToBisectionProc`: pad `A` up to size `e` from `V \ C` in increasing order, and
send the remaining `e` ports of `V \ C` into `B` at `bBase`. -/
def padPass2Stmt : Stmt :=
  .assign 12 (.const 0) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .cond (.bin .eq (.reg 8) (.reg 6))
       .nop
       (.cond (.bin .lt (.reg 11) (.reg 0))
         (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
          .assign 11 (.bin .add (.reg 11) (.const 1)))
         (.store (.bin .add (.reg 10) (.reg 12)) (.reg 7) ;;
          .assign 12 (.bin .add (.reg 12) (.const 1)))))

/-- Write `SinglePairAt` for `padToBisection e U` at `outPairsAddr` and return `h + 2 * e`.
Args: `[e, kU, uAddr, outPairsAddr, h]`. -/
def padToBisectionProc : Stmt :=
  (.assign 5 (.bin .mul (.const 2) (.reg 0)) ;;
   .cond (.bin .lt (.reg 0) (.reg 1))
     (.assign 6 (.const 0))
     (.assign 6 (.const 1))) ;;
  markVertsStmt 1 2 4 7 8 1 ;;
  (.store (.reg 3) (.const 1) ;;
   .store (.bin .add (.reg 3) (.const 1)) (.reg 0) ;;
   .store (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 0)) (.reg 0) ;;
   .assign 9 (.bin .add (.reg 3) (.const 2)) ;;
   .assign 10 (.bin .add (.bin .add (.reg 3) (.const 3)) (.reg 0))) ;;
  padPass1Stmt ;;
  padPass2Stmt ;;
  .ret (.bin .add (.reg 4) (.reg 5))

/-- Contract for `padToBisectionProc`: writes nodup lists `(A_list, B_list)` of length `e` in
`SinglePairAt` format at `outPairsAddr` whose finsets equal `padToBisection e uList.toFinset`,
returns `h + 2 * e` preserving `ZeroFrom` and memory `< h` outside `[outPairsAddr, outPairsAddr + 3 + 2 * e)`. -/
def padToBisectionContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (e kU uAddr outPairsAddr h : ℕ) (uList : List ℕ),
      args = [e, kU, uAddr, outPairsAddr, h] ∧
      uList.length = kU ∧ uList.Nodup ∧ (∀ p ∈ uList, p < 2 * e) ∧
      ListAt mem uAddr uList ∧
      ZeroFrom mem h ∧
      uAddr + kU ≤ h ∧
      outPairsAddr + 3 + 2 * e ≤ h ∧
      DisjointRange outPairsAddr (3 + 2 * e) uAddr kU ∧
      h + padToBisectionSpace e < 2 ^ w ∧
      4 * e + 16 < 2 ^ w
  post args mem v mem' :=
    let e := args.getD 0 0
    let kU := args.getD 1 0
    let uAddr := args.getD 2 0
    let outPairsAddr := args.getD 3 0
    let h := args.getD 4 0
    let U := (readList mem uAddr kU).toFinset
    v = h + padToBisectionSpace e ∧
    ZeroFrom mem' v ∧
    (∃ A_list B_list : List ℕ,
      A_list.Nodup ∧ B_list.Nodup ∧
      A_list.length = e ∧ B_list.length = e ∧
      (∀ p ∈ A_list, p < 2 * e) ∧ (∀ p ∈ B_list, p < 2 * e) ∧
      (A_list.toFinset, B_list.toFinset) = padToBisection e U ∧
      SinglePairAt mem' outPairsAddr A_list B_list) ∧
    (∀ a < h, a < outPairsAddr ∨ outPairsAddr + 3 + 2 * e ≤ a → mem' a = mem a)
  cost args _mem :=
    padToBisectionCost (args.getD 0 0) (args.getD 1 0)

/-! ## 2. `buildInjPairProc` -/

/-- Heap scratch space (words) for `buildInjPairProc`. -/
def buildInjPairSpace (e : ℕ) : ℕ := 2 * e

/-- Step bound for `buildInjPairProc`: `O(e + kS + 1)`. -/
def buildInjPairCost (e kS : ℕ) : ℕ := 160 * e + 100 * kS + 160

/-- Scan `0 .. 2*e - 1` and collect unmarked ports into `aBase` (reg 9). -/
def injScanStmt : Stmt :=
  .assign 11 (.const 0) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.store (.bin .add (.reg 9) (.reg 11)) (.reg 7) ;;
        .assign 11 (.bin .add (.reg 11) (.const 1)))
       .nop)

/-- Copy `sList` of length `kS` (reg 1) from `sAddr` (reg 2) to `bBase` (reg 10). -/
def injCopyStmt : Stmt :=
  forRange 7 (.const 0) (.reg 1)
    (.assign 8 (.load (.bin .add (.reg 2) (.reg 7))) ;;
     .store (.bin .add (.reg 10) (.reg 7)) (.reg 8))

/-- Write `SinglePairAt` for `(range (2 * e) \ S, S)` at `outPairsAddr` and return `h + 2 * e`.
Args: `[e, kS, sAddr, outPairsAddr, h]`. -/
def buildInjPairProc : Stmt :=
  .assign 5 (.bin .mul (.const 2) (.reg 0)) ;;
  .assign 6 (.bin .sub (.reg 5) (.reg 1)) ;;
  markVertsStmt 1 2 4 7 8 1 ;;
  (.store (.reg 3) (.const 1) ;;
   .store (.bin .add (.reg 3) (.const 1)) (.reg 6) ;;
   .store (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 6)) (.reg 1) ;;
   .assign 9 (.bin .add (.reg 3) (.const 2)) ;;
   .assign 10 (.bin .add (.bin .add (.reg 3) (.const 3)) (.reg 6))) ;;
  injScanStmt ;;
  injCopyStmt ;;
  .ret (.bin .add (.reg 4) (.reg 5))

/-- Contract for `buildInjPairProc`: writes `SinglePairAt mem' outPairsAddr A_list sList` where
`A_list = (Finset.range (2 * e) \ sList.toFinset).sort (· ≤ ·)`, returns `h + 2 * e` preserving
`ZeroFrom` and memory `< h` outside `[outPairsAddr, outPairsAddr + 3 + 2 * e)`. -/
def buildInjPairContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (e kS sAddr outPairsAddr h : ℕ) (sList : List ℕ),
      args = [e, kS, sAddr, outPairsAddr, h] ∧
      sList.length = kS ∧ sList.Nodup ∧ (∀ p ∈ sList, p < 2 * e) ∧
      ListAt mem sAddr sList ∧
      ZeroFrom mem h ∧
      sAddr + kS ≤ h ∧
      outPairsAddr + 3 + 2 * e ≤ h ∧
      DisjointRange outPairsAddr (3 + 2 * e) sAddr kS ∧
      h + buildInjPairSpace e < 2 ^ w ∧
      4 * e + 16 < 2 ^ w
  post args mem v mem' :=
    let e := args.getD 0 0
    let kS := args.getD 1 0
    let sAddr := args.getD 2 0
    let outPairsAddr := args.getD 3 0
    let h := args.getD 4 0
    let sList := readList mem sAddr kS
    let A_list := (Finset.range (2 * e) \ sList.toFinset).sort (· ≤ ·)
    v = h + buildInjPairSpace e ∧
    ZeroFrom mem' v ∧
    A_list.Nodup ∧
    A_list.toFinset = Finset.range (2 * e) \ sList.toFinset ∧
    SinglePairAt mem' outPairsAddr A_list sList ∧
    (∀ a < h, a < outPairsAddr ∨ outPairsAddr + 3 + 2 * e ≤ a → mem' a = mem a)
  cost args _mem :=
    buildInjPairCost (args.getD 0 0) (args.getD 1 0)

/-! ## 3. `fakeCompletionProc` -/

/-- Heap scratch space (words) for `fakeCompletionProc`. -/
def fakeCompletionSpace (e : ℕ) : ℕ := 8 * e

/-- Step bound for `fakeCompletionProc`: `O(e + mM + 1)`. -/
def fakeCompletionCost (e mM : ℕ) : ℕ := 400 * e + 80 * mM + 260

/-- Clear `flagA[u]` and `flagB[v]` for each matching edge `(u, v)` in `M`. -/
def fcUnmarkStmt : Stmt :=
  forRange 16 (.const 0) (.reg 2)
    (.assign 17 (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 16)))) ;;
     .assign 18 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 16))) (.const 1))) ;;
     .store (.bin .add (.reg 8) (.reg 17)) (.const 0) ;;
     .store (.bin .add (.reg 9) (.reg 18)) (.const 0))

/-- Scan `0 .. len - 1` and collect indices `p` with `mem[flagAddr + p] > 0` into `outAddr`
(count in `rCnt`). -/
def collectFlagStmt (rLen rFlag rOut rI rVal rCnt : ℕ) : Stmt :=
  .assign rCnt (.const 0) ;;
  forRange rI (.const 0) (.reg rLen)
    (.assign rVal (.load (.bin .add (.reg rFlag) (.reg rI))) ;;
     .cond (.bin .lt (.const 0) (.reg rVal))
       (.store (.bin .add (.reg rOut) (.reg rCnt)) (.reg rI) ;;
        .assign rCnt (.bin .add (.reg rCnt) (.const 1)))
       .nop)

/-- Scan `0 .. 2*e - 1` and collect surviving `flagA` ports into `unA` (reg 10, count reg 19)
and surviving `flagB` ports into `unB` (reg 11, count reg 20). -/
def fcCollectStmt : Stmt :=
  collectFlagStmt 7 8 10 16 17 19 ;;
  collectFlagStmt 7 9 11 16 17 20

/-- Zip `unA` and `unB` up to `min cntA cntB` into `outFAddr` (reg 4) and store length at
`outLenAddr` (reg 5). -/
def fcZipStmt : Stmt :=
  .cond (.bin .lt (.reg 19) (.reg 20))
    (.assign 21 (.reg 19))
    (.assign 21 (.reg 20)) ;;
  forRange 16 (.const 0) (.reg 21)
    (.assign 17 (.load (.bin .add (.reg 10) (.reg 16))) ;;
     .assign 18 (.load (.bin .add (.reg 11) (.reg 16))) ;;
     .store (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 16))) (.reg 17) ;;
     .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 18)) ;;
  .store (.reg 5) (.reg 21)

/-- Compute `OuterMatching.fakeCompletion A B M` from `SinglePairAt` at `pairsAddr` and `EdgesAt`
at `mAddr`, writing the fake edges at `outFAddr`, their count at `outLenAddr`, and returning
`h + 8 * e`. Args: `[e, pairsAddr, mM, mAddr, outFAddr, outLenAddr, h]`. -/
def fakeCompletionProc : Stmt :=
  (.assign 7 (.bin .mul (.const 2) (.reg 0)) ;;
   .assign 8 (.reg 6) ;;
   .assign 9 (.bin .add (.reg 8) (.reg 7)) ;;
   .assign 10 (.bin .add (.reg 9) (.reg 7)) ;;
   .assign 11 (.bin .add (.reg 10) (.reg 7))) ;;
  (.assign 12 (.load (.bin .add (.reg 1) (.const 1))) ;;
   .assign 13 (.bin .add (.reg 1) (.const 2)) ;;
   .assign 14 (.load (.bin .add (.reg 13) (.reg 12))) ;;
   .assign 15 (.bin .add (.bin .add (.reg 13) (.reg 12)) (.const 1))) ;;
  markVertsStmt 12 13 8 16 17 1 ;;
  markVertsStmt 14 15 9 16 17 1 ;;
  fcUnmarkStmt ;;
  fcCollectStmt ;;
  fcZipStmt ;;
  .ret (.bin .add (.reg 11) (.reg 7))

/-- Contract for `fakeCompletionProc`: computes `fakeCompletion A B M` bit-for-bit identically at
`outFAddr` (of size `2 * e`, valid whenever `A_list.length + B_list.length ≤ 2 * e`), stores its
length at `outLenAddr`, and returns `h + 8 * e`. -/
def fakeCompletionContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (e pairsAddr mM mAddr outFAddr outLenAddr h : ℕ)
      (A_list B_list : List ℕ) (M : List (ℕ × ℕ)),
      args = [e, pairsAddr, mM, mAddr, outFAddr, outLenAddr, h] ∧
      A_list.length + B_list.length ≤ 2 * e ∧
      (∀ p ∈ A_list, p < 2 * e) ∧
      (∀ p ∈ B_list, p < 2 * e) ∧
      SinglePairAt mem pairsAddr A_list B_list ∧
      M.length = mM ∧
      (∀ ed ∈ M, ed.1 < 2 * e ∧ ed.2 < 2 * e) ∧
      EdgesAt mem mAddr M ∧
      ZeroFrom mem h ∧
      pairsAddr + 3 + A_list.length + B_list.length ≤ h ∧
      mAddr + 2 * mM ≤ h ∧
      outFAddr + 2 * e ≤ h ∧
      outLenAddr + 1 ≤ h ∧
      DisjointRange outFAddr (2 * e) pairsAddr (3 + A_list.length + B_list.length) ∧
      DisjointRange outFAddr (2 * e) mAddr (2 * mM) ∧
      DisjointRange outFAddr (2 * e) outLenAddr 1 ∧
      DisjointRange outLenAddr 1 pairsAddr (3 + A_list.length + B_list.length) ∧
      DisjointRange outLenAddr 1 mAddr (2 * mM) ∧
      h + fakeCompletionSpace e < 2 ^ w ∧
      4 * e + 16 < 2 ^ w ∧
      2 * mM + 16 < 2 ^ w
  post args mem v mem' :=
    let e := args.getD 0 0
    let pairsAddr := args.getD 1 0
    let mM := args.getD 2 0
    let mAddr := args.getD 3 0
    let outFAddr := args.getD 4 0
    let outLenAddr := args.getD 5 0
    let h := args.getD 6 0
    let ab := readSinglePair mem pairsAddr
    let M := readEdges mem mAddr mM
    let F := fakeCompletion ab.1 ab.2 M
    v = h + fakeCompletionSpace e ∧
    ZeroFrom mem' v ∧
    mem' outLenAddr = F.length ∧
    EdgesAt mem' outFAddr F ∧
    (∀ a < h,
      (a < outFAddr ∨ outFAddr + 2 * e ≤ a) →
      a ≠ outLenAddr →
      mem' a = mem a)
  cost args _mem :=
    fakeCompletionCost (args.getD 0 0) (args.getD 2 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited

lemma padToBisectionProc_noRand : padToBisectionProc.NoRand := by
  simp [padToBisectionProc, padPass1Stmt, padPass2Stmt, markVertsStmt_noRand,
    forRange, forUp, Stmt.NoRand]

lemma buildInjPairProc_noRand : buildInjPairProc.NoRand := by
  simp [buildInjPairProc, injScanStmt, injCopyStmt, markVertsStmt_noRand,
    forRange, forUp, Stmt.NoRand]

lemma fakeCompletionProc_noRand : fakeCompletionProc.NoRand := by
  simp [fakeCompletionProc, fcUnmarkStmt, fcCollectStmt, collectFlagStmt, fcZipStmt,
    markVertsStmt_noRand, forRange, forUp, Stmt.NoRand]

/-! ## 4. Pure List/Finset Bridges -/

/-- Filtering `List.range N` by membership in a subset `S ⊆ Finset.range N` yields `S.sort (· ≤ ·)`. -/
lemma list_range_filter_eq_finset_sort {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    (List.range N).filter (fun x => decide (x ∈ S)) = S.sort (· ≤ ·) := by
  have hnd1 : ((List.range N).filter (fun x => decide (x ∈ S))).Nodup :=
    List.nodup_range.filter _
  have hnd2 : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
  have hpw1 : ((List.range N).filter (fun x => decide (x ∈ S))).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp (fun h => Nat.le_of_lt h)
  have hpw2 : (S.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hperm : ((List.range N).filter (fun x => decide (x ∈ S))).Perm (S.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hnd1 hnd2]
    intro x
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Finset.mem_sort]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨Finset.mem_range.mp (hS hx), hx⟩⟩
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hpw1 hpw2

lemma list_take_append_singleton_lt {α : Type*} {xs : List α} {x : α} {n : ℕ}
    (h : xs.length < n) : (xs ++ [x]).take n = xs ++ [x] := by
  rw [List.take_of_length_le]; simp; omega

lemma list_take_append_singleton_ge {α : Type*} {xs : List α} {x : α} {n : ℕ}
    (h : n ≤ xs.length) : (xs ++ [x]).take n = xs.take n := by
  rw [List.take_append_of_le_length h]

lemma list_drop_append_singleton_lt {α : Type*} {xs : List α} {x : α} {n : ℕ}
    (h : xs.length < n) : (xs ++ [x]).drop n = [] := by
  rw [List.drop_eq_nil_iff]; simp; omega

lemma list_drop_append_singleton_ge {α : Type*} {xs : List α} {x : α} {n : ℕ}
    (h : n ≤ xs.length) : (xs ++ [x]).drop n = xs.drop n ++ [x] := by
  rw [List.drop_append_of_le_length h]


end MinCostFlow.ExpanderDecomp
