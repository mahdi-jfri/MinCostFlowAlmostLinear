module

public import MinCostFlow.LSF.Program.WKeys
public import MinCostFlow.LSF.Program.WScan
public import MinCostFlow.LSF.Program.KeyedSort

/-!
# Writing the `W` block

`wBlockProc` writes the `W` block in three passes:

1. `wKeysProc` writes the key of every index and lists the kept indices;
2. `keyedMergeSortStmt` sorts the kept indices by key;
3. `wScanProc` groups the sorted list and writes the CSR arrays.

It uses a work area at `base`: the keys (`n · 3L` cells), the list (`n` cells), the sort scratch
(`n` cells) and the stamps (`n` cells, zero at the start). The result `wBlock_meetsContract`
gives the facts that `wBlock_bridge` (`WBridge.lean`) turns into `WBlockAt`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The groups depend on `pa` only at the listed elements. -/
lemma wGroups_congr_pa {K s pa pa' : ℕ → ℕ} :
    ∀ k, (∀ j < k, pa (s j) = pa' (s j)) → wGroups K s pa k = wGroups K s pa' k
  | 0, _ => rfl
  | k + 1, h => by
    rw [wGroups, wGroups, wGroups_congr_pa k (fun j hj => h j (by omega))]
    simp only [grpAdd, h k (by omega)]

/-- Args: `[n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, parPtr, fidPtr, vListPtr,
wPtr, n0]`. Registers `17`–`19` hold the list, the scratch and the stamps; `20` the number of
kept indices. -/
def wBlockProc (bKeys bSort bScan : ℕ) : Stmt :=
  .assign 17 (.bin .add (.reg 8) (.bin .mul (.reg 0) (.bin .mul (.const 3) (.reg 7)))) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 0)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 0)) ;;
  .call 20 bKeys [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 17] ;;
  .call 21 bSort [.reg 17, .reg 18, .reg 8, .bin .mul (.const 3) (.reg 7), .const 0, .reg 20] ;;
  .call 21 bScan [.reg 20, .reg 17, .reg 2, .reg 9, .reg 10, .reg 11, .reg 4, .reg 5, .reg 6,
    .reg 19, .reg 12, .reg 13, .reg 0] ;;
  .ret (.reg 20)

lemma wBlockProc_noRand (bKeys bSort bScan : ℕ) : (wBlockProc bKeys bSort bScan).NoRand := by
  simp [wBlockProc, Stmt.NoRand]

/-- The size of the work area. -/
def wWorkSize (n L : ℕ) : ℕ := n * (3 * L) + 3 * n

/-- A read array `[a, a + len)` lies outside the work area and the `W` block. -/
def BAway (w base wsz wPtr n0 a len : ℕ) : Prop :=
  (a + len ≤ base ∨ base + wsz ≤ a) ∧ (a + len ≤ wPtr ∨ wPtr + wBlockSize n0 ≤ a) ∧
    a + len < 2 ^ w

/-- The contract of `wBlockProc`. -/
def wBlockContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n r pePtr ownPtr labYPtr labBPtr rtPtr L base parPtr fidPtr vListPtr wPtr n0
      tM : ℕ),
    args = [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, parPtr, fidPtr, vListPtr,
      wPtr, n0] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ L ∧ 3 * L < 2 ^ w ∧ n ≤ capacity h L ∧ n ≤ n0 ∧
    base + wWorkSize n L < 2 ^ w ∧ wPtr + wBlockSize n0 < 2 ^ w ∧
    (base + wWorkSize n L ≤ wPtr ∨ wPtr + wBlockSize n0 ≤ base) ∧
    (∀ y < n, mem (base + n * (3 * L) + 2 * n + y) = 0) ∧
    BAway w base (wWorkSize n L) wPtr n0 pePtr n ∧ BAway w base (wWorkSize n L) wPtr n0 ownPtr tM ∧
    BAway w base (wWorkSize n L) wPtr n0 labYPtr n ∧
    BAway w base (wWorkSize n L) wPtr n0 labBPtr n ∧
    BAway w base (wWorkSize n L) wPtr n0 rtPtr n ∧ BAway w base (wWorkSize n L) wPtr n0 parPtr n ∧
    BAway w base (wWorkSize n L) wPtr n0 fidPtr tM ∧
    BAway w base (wWorkSize n L) wPtr n0 vListPtr n ∧
    (∀ x < n, x ≠ r → mem (pePtr + x) < tM) ∧ (∀ x < n, mem (parPtr + x) < n) ∧
    (∀ x < n, mem (labYPtr + x) < n ∧ mem (labBPtr + x) < n ∧ mem (rtPtr + x) < n)
  post args mem ret mem' := ∃ (n r pePtr ownPtr labYPtr labBPtr rtPtr L base parPtr fidPtr vListPtr
      wPtr n0 cnt : ℕ) (K s : ℕ → ℕ),
    args = [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, parPtr, fidPtr, vListPtr,
      wPtr, n0] ∧ ret = cnt ∧ cnt ≤ n ∧
    (∀ a, (a < base ∨ base + wWorkSize n L ≤ a) → (a < wPtr ∨ wPtr + wBlockSize n0 ≤ a) →
      mem' a = mem a) ∧
    ((List.range cnt).map s).Nodup ∧
    (∀ y, y ∈ (List.range cnt).map s ↔ y < n ∧ y ≠ r ∧ mem (ownPtr + mem (pePtr + y)) = 0) ∧
    WKeyOK K s (fun y => mem (labYPtr + y)) (fun y => mem (labBPtr + y)) (fun y => mem (rtPtr + y))
      cnt ∧
    let G := wGroups K s (fun y => mem (parPtr + y)) cnt
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
    (∀ j < cnt, mem' (wEdgesBase wPtr n0 + j) = mem (fidPtr + mem (pePtr + s j)))
  cost args _ :=
    let n := args.getD 0 0
    let L := args.getD 7 0
    n * (90 * L + 250) + (270 * L + 180) * n * (Nat.clog 2 n + 1) + 400 * n + 600

end

end MinCostFlow.LSF.Program
