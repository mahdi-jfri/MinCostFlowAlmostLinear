module

public import MinCostFlow.LSF.Program.WKeyMath
public import MinCostFlow.LSF.Program.UArithMul
public import MinCostFlow.LSF.Program.WAddV

/-!
# The keys and the list of the kept indices

Before the sort, `wKeysProc` makes one pass over the indices `x < n`. It writes the key of `x`
as a block of `3L` limbs at `keysPtr + x · 3L`: the numbers `labY x`, `labB x` and `rt x` in
`L` limbs each (three calls of `uLoadWordProc`). So the block holds
`key3 C (labY x) (labB x) (rt x)` (`WKeyMath.lean`). It also lists the kept indices (the
indices `x ≠ r` with `own (pe x) = 0`) in index order at `arrPtr`, and returns their number.
The result is `wKeys_meetsContract`, at cost `O(n L)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The kept indices below `j`, in index order. -/
def keptList (r : ℕ) (own pe : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range j).filter (fun x => decide (x ≠ r ∧ own (pe x) = 0))

lemma keptList_succ (r : ℕ) (own pe : ℕ → ℕ) (j : ℕ) :
    keptList r own pe (j + 1) =
      if j ≠ r ∧ own (pe j) = 0 then keptList r own pe j ++ [j] else keptList r own pe j := by
  unfold keptList
  rw [List.range_succ, List.filter_append]
  by_cases h : j ≠ r ∧ own (pe j) = 0
  · simp [h]
  · rw [if_neg h]; simp [h]

lemma keptList_length_le (r : ℕ) (own pe : ℕ → ℕ) (j : ℕ) : (keptList r own pe j).length ≤ j :=
  (List.length_filter_le _ _).trans (by simp)

lemma mem_keptList {r : ℕ} {own pe : ℕ → ℕ} {j y : ℕ} :
    y ∈ keptList r own pe j ↔ y < j ∧ y ≠ r ∧ own (pe y) = 0 := by
  simp [keptList]

lemma keptList_nodup (r : ℕ) (own pe : ℕ → ℕ) (j : ℕ) : (keptList r own pe j).Nodup :=
  List.nodup_range.filter _

/-- The loop body (register `14` is `x`, `10` the count, `11` is `3L`). -/
def wKeysBody (bLoad : ℕ) : Stmt :=
  .assign 12 (.bin .add (.reg 8) (.bin .mul (.reg 14) (.reg 11))) ;;
  .call 13 bLoad [.reg 12, .reg 7, .load (.bin .add (.reg 4) (.reg 14))] ;;
  .call 13 bLoad [.bin .add (.reg 12) (.reg 7), .reg 7, .load (.bin .add (.reg 5) (.reg 14))] ;;
  .call 13 bLoad [.bin .add (.reg 12) (.bin .add (.reg 7) (.reg 7)), .reg 7,
    .load (.bin .add (.reg 6) (.reg 14))] ;;
  .cond (.bin .eq (.reg 14) (.reg 1)) .nop
    (.cond (.bin .eq (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 2) (.reg 14)))))
        (.const 0))
      (.store (.bin .add (.reg 9) (.reg 10)) (.reg 14) ;;
       .assign 10 (.bin .add (.reg 10) (.const 1)))
      .nop)

/-- Args: `[n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, keysPtr, arrPtr]`. -/
def wKeysProc (bLoad : ℕ) : Stmt :=
  .assign 10 (.const 0) ;;
  .assign 11 (.bin .mul (.const 3) (.reg 7)) ;;
  forRange 14 (.const 0) (.reg 0) (wKeysBody bLoad) ;;
  .ret (.reg 10)

lemma wKeysProc_noRand (bLoad : ℕ) : (wKeysProc bLoad).NoRand := by
  simp [wKeysProc, wKeysBody, forRange, forUp, Stmt.NoRand]

/-- A read array `[a, a + len)` lies outside the keys and the list. -/
def KAway (w keysPtr kLen arrPtr n a len : ℕ) : Prop :=
  (a + len ≤ keysPtr ∨ keysPtr + kLen ≤ a) ∧ (a + len ≤ arrPtr ∨ arrPtr + n ≤ a) ∧ a + len < 2 ^ w

/-- The contract of `wKeysProc`. -/
def wKeysContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n r pePtr ownPtr labYPtr labBPtr rtPtr L keysPtr arrPtr tM : ℕ),
    args = [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, keysPtr, arrPtr] ∧
    2 < 2 ^ w ∧ 1 ≤ L ∧ 3 * L < 2 ^ w ∧ n ≤ capacity h L ∧ keysPtr + n * (3 * L) < 2 ^ w ∧
    arrPtr + n < 2 ^ w ∧ (arrPtr + n ≤ keysPtr ∨ keysPtr + n * (3 * L) ≤ arrPtr) ∧
    KAway w keysPtr (n * (3 * L)) arrPtr n pePtr n ∧ KAway w keysPtr (n * (3 * L)) arrPtr n ownPtr tM ∧
    KAway w keysPtr (n * (3 * L)) arrPtr n labYPtr n ∧
    KAway w keysPtr (n * (3 * L)) arrPtr n labBPtr n ∧
    KAway w keysPtr (n * (3 * L)) arrPtr n rtPtr n ∧
    (∀ x < n, x ≠ r → mem (pePtr + x) < tM) ∧
    (∀ x < n, mem (labYPtr + x) < n ∧ mem (labBPtr + x) < n ∧ mem (rtPtr + x) < n)
  post args mem ret mem' := ∃ (n r pePtr ownPtr labYPtr labBPtr rtPtr L keysPtr arrPtr : ℕ),
    args = [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, keysPtr, arrPtr] ∧
    (∀ a, (a < keysPtr ∨ keysPtr + n * (3 * L) ≤ a) → (a < arrPtr ∨ arrPtr + n ≤ a) →
      mem' a = mem a) ∧
    let kl := keptList r (fun i => mem (ownPtr + i)) (fun x => mem (pePtr + x)) n
    ret = kl.length ∧ ListAt mem' arrPtr kl ∧
    ∀ x < n, Valid mem' (keysPtr + x * (3 * L)) h (3 * L) ∧
      unsignedVal mem' (keysPtr + x * (3 * L)) h (3 * L) =
        key3 (capacity h L) (mem (labYPtr + x)) (mem (labBPtr + x)) (mem (rtPtr + x))
  cost args _ := args.getD 0 0 * (90 * args.getD 7 0 + 250) + 100

/-- The key facts of a block only read the block. -/
lemma key_congr {m m' : ℕ → ℕ} {a h L v : ℕ}
    (hk : Valid m a h L ∧ unsignedVal m a h L = v)
    (hag : ∀ i < L, m' (a + i) = m (a + i)) : Valid m' a h L ∧ unsignedVal m' a h L = v :=
  ⟨fun i hi => by rw [hag i hi]; exact hk.1 i hi,
    by rw [← hk.2]; exact unsignedVal_congr fun i hi => hag i hi⟩

end

end MinCostFlow.LSF.Program
