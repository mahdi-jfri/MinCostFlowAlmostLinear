module

public import MinCostFlow.LSF.Program.WScanMem

/-!
# The scan that writes the `W` block

`wScanProc` reads a list `s 0, …, s (cnt - 1)` of kept indices, sorted by key, and writes the
CSR arrays of the `W` block (`WBlockAt`, `BlockRep.lean`). The key of an index `x` is the triple
`(labY x, labB x, rt x)`. Position `k` starts a new group when `k = 0` or the key of `s k`
differs from the key of `s (k - 1)`. For each position the scan

* starts a new group when needed: it writes the two offsets of the group;
* writes the parent edge `fid (pe x)` of `x = s k` into the edge list;
* adds the vertices of `x` and `par x` to the group with `wAddVProc`, which skips a vertex that
  the group already has (stamp array).

The groups are `wGroups K s par cnt` (`WScanMath.lean`) for any numeric key `K` that is sorted
along the list and that is equal exactly when the triples are equal. The result is
`wScan_meetsContract`, at cost `O(cnt)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Start a new group: write its two offsets. -/
def wScanNew : Stmt :=
  .store (.bin .add (.reg 12) (.reg 16)) (.reg 17) ;;
  .store (.bin .add (.reg 14) (.reg 16)) (.reg 18) ;;
  .assign 16 (.bin .add (.reg 16) (.const 1))

/-- Write the edge of `x` (register `19`) and add the vertices `x` and `par x`. -/
def wScanRest (bAdd : ℕ) : Stmt :=
  .store (.bin .add (.reg 15) (.reg 18))
    (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 2) (.reg 19))))) ;;
  .call 17 bAdd [.reg 9, .reg 5, .reg 13, .reg 19, .reg 16, .reg 17] ;;
  .call 17 bAdd [.reg 9, .reg 5, .reg 13, .load (.bin .add (.reg 3) (.reg 19)), .reg 16, .reg 17]

/-- The loop body (register `18` is `k`). -/
def wScanBody (bAdd : ℕ) : Stmt :=
  .assign 19 (.load (.bin .add (.reg 1) (.reg 18))) ;;
  .assign 20 (.load (.bin .add (.reg 1) (.bin .sub (.reg 18) (.const 1)))) ;;
  .assign 21 (.bin .eq (.reg 18) (.const 0)) ;;
  .assign 22 (.bin .eq (.load (.bin .add (.reg 6) (.reg 19))) (.load (.bin .add (.reg 6) (.reg 20)))) ;;
  .assign 23 (.bin .eq (.load (.bin .add (.reg 7) (.reg 19))) (.load (.bin .add (.reg 7) (.reg 20)))) ;;
  .assign 24 (.bin .eq (.load (.bin .add (.reg 8) (.reg 19))) (.load (.bin .add (.reg 8) (.reg 20)))) ;;
  .cond (.bin .lt (.bin .add (.reg 22) (.bin .add (.reg 23) (.reg 24)))
      (.bin .add (.const 3) (.reg 21))) wScanNew .nop ;;
  wScanRest bAdd

/-- Args: `[cnt, arrPtr, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr, rtPtr, stPtr, wPtr,
n0, n]` (`n` is the number of stamps; it is not read). Registers `12`–`15` hold the bases `VO`, `VS`, `EO`, `ES` of the four arrays, `16` the
number of groups and `17` the number of vertices. -/
def wScanProc (bAdd : ℕ) : Stmt :=
  .assign 12 (.bin .add (.reg 10) (.const 7)) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .add (.reg 11) (.const 1))) ;;
  .assign 14 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 11))) ;;
  .assign 15 (.bin .add (.reg 14) (.bin .add (.reg 11) (.const 1))) ;;
  .assign 16 (.const 0) ;;
  .assign 17 (.const 0) ;;
  forRange 18 (.const 0) (.reg 0) (wScanBody bAdd) ;;
  .store (.bin .add (.reg 12) (.reg 16)) (.reg 17) ;;
  .store (.bin .add (.reg 14) (.reg 16)) (.reg 0) ;;
  .store (.reg 10) (.reg 16) ;;
  .store (.bin .add (.reg 10) (.const 1)) (.reg 12) ;;
  .store (.bin .add (.reg 10) (.const 2)) (.reg 13) ;;
  .store (.bin .add (.reg 10) (.const 3)) (.reg 14) ;;
  .store (.bin .add (.reg 10) (.const 4)) (.reg 15) ;;
  .store (.bin .add (.reg 10) (.const 5)) (.reg 17) ;;
  .store (.bin .add (.reg 10) (.const 6)) (.reg 0) ;;
  .ret (.const 0)

lemma wScanProc_noRand (bAdd : ℕ) : (wScanProc bAdd).NoRand := by
  simp [wScanProc, wScanBody, wScanNew, wScanRest, forRange, forUp, Stmt.NoRand]

/-- A read array `[a, a + len)` lies outside the `W` block and the stamps. -/
def WAway (w wPtr n0 stPtr n a len : ℕ) : Prop :=
  OutsideBlock w wPtr (wBlockSize n0) a len ∧ (a + len ≤ stPtr ∨ stPtr + n ≤ a)

/-- The facts on the key `K` along the list `s`: sorted, and equal exactly when the three
labels are equal. -/
def WKeyOK (K s lY lB rt : ℕ → ℕ) (cnt : ℕ) : Prop :=
  (∀ i j, i ≤ j → j < cnt → K (s i) ≤ K (s j)) ∧
  ∀ j < cnt, ∀ j' < cnt, (K (s j) = K (s j') ↔ lY (s j) = lY (s j') ∧ lB (s j) = lB (s j') ∧
    rt (s j) = rt (s j'))

/-- The contract of `wScanProc`. -/
def wScanContract (w : ℕ) : Contract where
  pre args mem := ∃ (cnt arrPtr pePtr parPtr fidPtr vListPtr labYPtr labBPtr rtPtr stPtr wPtr
      n0 n tM : ℕ) (K : ℕ → ℕ),
    args = [cnt, arrPtr, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr, rtPtr, stPtr, wPtr,
      n0, n] ∧
    16 ≤ 2 ^ w ∧ cnt ≤ n0 ∧ wPtr + wBlockSize n0 < 2 ^ w ∧ stPtr + n < 2 ^ w ∧
    (stPtr + n ≤ wPtr ∨ wPtr + wBlockSize n0 ≤ stPtr) ∧ (∀ y < n, mem (stPtr + y) = 0) ∧
    WAway w wPtr n0 stPtr n arrPtr cnt ∧ WAway w wPtr n0 stPtr n pePtr n ∧
    WAway w wPtr n0 stPtr n parPtr n ∧ WAway w wPtr n0 stPtr n fidPtr tM ∧
    WAway w wPtr n0 stPtr n vListPtr n ∧ WAway w wPtr n0 stPtr n labYPtr n ∧
    WAway w wPtr n0 stPtr n labBPtr n ∧ WAway w wPtr n0 stPtr n rtPtr n ∧
    (∀ j < cnt, mem (arrPtr + j) < n ∧ mem (parPtr + mem (arrPtr + j)) < n ∧
      mem (pePtr + mem (arrPtr + j)) < tM) ∧
    WKeyOK K (fun j => mem (arrPtr + j)) (fun y => mem (labYPtr + y))
      (fun y => mem (labBPtr + y)) (fun y => mem (rtPtr + y)) cnt
  post args mem ret mem' := ∃ (cnt arrPtr pePtr parPtr fidPtr vListPtr labYPtr labBPtr rtPtr stPtr
      wPtr n0 n : ℕ) (K : ℕ → ℕ),
    args = [cnt, arrPtr, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr, rtPtr, stPtr, wPtr,
      n0, n] ∧ ret = 0 ∧
    WKeyOK K (fun j => mem (arrPtr + j)) (fun y => mem (labYPtr + y))
      (fun y => mem (labBPtr + y)) (fun y => mem (rtPtr + y)) cnt ∧
    (∀ a, (a < wPtr ∨ wPtr + wBlockSize n0 ≤ a) → (a < stPtr ∨ stPtr + n ≤ a) → mem' a = mem a) ∧
    let G := wGroups K (fun j => mem (arrPtr + j)) (fun y => mem (parPtr + y)) cnt
    mem' (wPtr + wOffNumPieces) = G.length ∧
    mem' (wPtr + wOffVertOffPtr) = wVertOffBase wPtr ∧
    mem' (wPtr + wOffVertsPtr) = wVertsBase wPtr n0 ∧
    mem' (wPtr + wOffEdgeOffPtr) = wEdgeOffBase wPtr n0 ∧
    mem' (wPtr + wOffEdgesPtr) = wEdgesBase wPtr n0 ∧
    mem' (wPtr + wOffTotalVerts) = vTotal G ∧
    mem' (wPtr + wOffTotalEdges) = cnt ∧
    (∀ i ≤ G.length, mem' (wVertOffBase wPtr + i) = vStart G i) ∧
    (∀ i ≤ G.length, mem' (wEdgeOffBase wPtr n0 + i) = eStart G i) ∧
    ListAt mem' (wVertsBase wPtr n0) ((flatV G).map (fun y => mem (vListPtr + y))) ∧
    (∀ j < cnt, mem' (wEdgesBase wPtr n0 + j) = mem (fidPtr + mem (pePtr + mem (arrPtr + j))))
  cost args _ := 400 * args.getD 0 0 + 200

/-- The value of the boundary test. -/
lemma wBnd_iff (k : ℕ) (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    ((if A then 1 else 0) + ((if B then 1 else 0) + (if C then 1 else 0)) <
      3 + (if k = 0 then 1 else 0)) ↔ (k = 0 ∨ ¬(A ∧ B ∧ C)) := by
  by_cases hk : k = 0 <;> by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    simp [hk, hA, hB, hC]

end

end MinCostFlow.LSF.Program
