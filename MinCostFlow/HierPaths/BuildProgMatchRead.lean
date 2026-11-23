module

public import MinCostFlow.HierPaths.BuildProgMatchRow
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Reading the coordinates of one matching row

The first endpoint offset gives the first matching edge. The next offset
gives the matching length, and the last offset gives the total number of
matched edges across the batch. Reading four words suffices.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Args are `[matchingTable, numberOfRows, row, destination]`. -/
def buildMatchReadProc : Stmt :=
  .seq (.assign 4 (.bin .add (.reg 0) (.reg 2)))
    (.seq (.assign 5 (.load (.reg 4)))
      (.seq (.assign 6 (.bin .sub (.load (.bin .add (.reg 4) (.const 1))) (.reg 5)))
        (.seq (.store (.reg 3)
            (.bin .add (.bin .add (.reg 0) (.bin .add (.reg 1) (.const 1))) (.reg 5)))
          (.seq (.store (.bin .add (.reg 3) (.const 1)) (.bin .div (.reg 6) (.const 2)))
            (.seq (.store (.bin .add (.reg 3) (.const 2)) (.bin .div (.reg 5) (.const 2)))
              (.seq (.store (.bin .add (.reg 3) (.const 3))
                (.bin .div (.load (.bin .add (.reg 0) (.reg 1))) (.const 2)))
                (.ret (.const 0))))))))

/-- The base, count, flattened first edge and total count of the routed matching. -/
def matchReadWords (Ms : List (List (ℕ × ℕ))) (tb i : ℕ) : List ℕ :=
  [tb + (Ms.length + 1) + 2 * flatIndex Ms i 0,
    (Ms.getD i []).length, flatIndex Ms i 0, Ms.flatten.length]

/-- Read a row of the endpoint table into four consecutive words disjoint from the table. -/
def buildMatchReadContract (w i : ℕ) (Ms : List (List (ℕ × ℕ))) : Contract where
  pre args mem := ∃ tb dst, args = [tb, Ms.length, i, dst] ∧ i < Ms.length ∧
    ListAt mem tb (csrList Ms.length (matchingRowWords Ms)) ∧
    tb + (csrList Ms.length (matchingRowWords Ms)).length ≤ dst ∧ dst + 4 < 2 ^ w
  post args mem _ mem' := ∃ tb dst, args = [tb, Ms.length, i, dst] ∧
    ListAt mem' dst (matchReadWords Ms tb i) ∧
    ∀ a, (a < dst ∨ dst + 4 ≤ a) → mem' a = mem a
  cost _ _ := 80

theorem buildMatchReadProc_noRand : buildMatchReadProc.NoRand := by
  simp [buildMatchReadProc, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Recover the coordinates of a matching row in constant time. -/
theorem buildMatchReadProc_meetsContract {w f i : ℕ} {p : Program}
    {Ms : List (List (ℕ × ℕ))} (hf : p.procs[f]? = some buildMatchReadProc) :
    MeetsContract w p f (buildMatchReadContract w i Ms) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨tb, dst, rfl, hi, hAt, hSep, hFit⟩ := hPre
  let k := Ms.length
  let j := flatIndex Ms i 0
  let n := (Ms.getD i []).length
  let tot := Ms.flatten.length
  let src := tb + (k + 1) + 2 * j
  obtain ⟨hCur, hNext, hTot, _⟩ := matchingRow_view hi hAt
  change mem (tb + i) = 2 * j at hCur
  change mem (tb + i + 1) = 2 * (j + n) at hNext
  change mem (tb + k) = 2 * tot at hTot
  have hSize : (csrList k (matchingRowWords Ms)).length = k + 1 + 2 * tot := by
    simp only [csrList, List.length_append, length_csrOffsets, csrData, List.length_flatMap]
    rw [← hTot]
    exact congrArg (k + 1 + ·) (csrList_offset hAt (show k ≤ Ms.length from le_rfl)).symm
  rw [hSize] at hSep
  have hj : j + n ≤ tot := by
    by_cases hn : n = 0
    · have hp := congrArg List.length (List.take_append_drop i Ms)
      have ht : flatIndex Ms i 0 = (Ms.take i).flatten.length := by simp [flatIndex, List.length_flatten]
      have hsub := (List.take_sublist i Ms).flatten
      have hL := hsub.length_le
      change j = (Ms.take i).flatten.length at ht
      change (Ms.take i).flatten.length ≤ tot at hL
      omega
    · have hn' : n - 1 < (Ms.getD i []).length := by change n - 1 < n; omega
      have hj' := (getD_flatten_flatIndex Ms (0, 0) hi hn').1
      change j + (n - 1) < tot at hj'
      omega
  have hb : k + 1 < 2 ^ w := by omega
  have hAbi : tb + i < 2 ^ w := by omega
  have hAbj : tb + i + 1 < 2 ^ w := by omega
  have hAbk : tb + k < 2 ^ w := by omega
  have hOff : 2 * n < 2 ^ w := by omega
  have hBase : tb + (k + 1) < 2 ^ w := by omega
  have hSrc : src < 2 ^ w := by dsimp [src]; omega
  have hOne : 1 < 2 ^ w := by omega
  have hTwo : 2 < 2 ^ w := by omega
  have hThree : 3 < 2 ^ w := by omega
  have hD1 : dst + 1 < 2 ^ w := by omega
  have hD2 : dst + 2 < 2 ^ w := by omega
  have hD3 : dst + 3 < 2 ^ w := by omega
  have hN : n < 2 ^ w := by omega
  have hJ : j < 2 ^ w := by omega
  have hT : tot < 2 ^ w := by omega
  have hd : 2 * (j + n) - 2 * j = 2 * n := by omega
  refine runs_start_le ?_
  unfold buildMatchReadProc
  refine runs_seq_assign_le (v := tb + i) ?_ ?_
  · simp [Expr.eval, startState, hAbi]
  refine runs_seq_assign_le (v := 2 * j) ?_ ?_
  · simp [Expr.eval, startState, Function.update, hCur]
  refine runs_seq_assign_le (v := 2 * n) ?_ ?_
  · simp [Expr.eval, startState, Function.update, hOne, hAbj, hNext, hd, hOff]
  refine runs_seq_store_le (x := dst) (v := src) ?_ ?_ ?_
  · simp [Expr.eval, startState, Function.update]
  · have hK : Ms.length + 1 < 2 ^ w := hb
    have hB : tb + (Ms.length + 1) < 2 ^ w := hBase
    have hS : tb + (Ms.length + 1) + 2 * j < 2 ^ w := hSrc
    simp [Expr.eval, startState, Function.update, hOne, hK, hB, hS, src, k]
  refine runs_seq_store_le (x := dst + 1) (v := n) ?_ ?_ ?_
  · simp [Expr.eval, startState, Function.update, hOne, hD1]
  · simp [Expr.eval, Function.update, hTwo, hN]
  refine runs_seq_store_le (x := dst + 2) (v := j) ?_ ?_ ?_
  · simp [Expr.eval, startState, Function.update, hTwo, hD2]
  · simp [Expr.eval, Function.update, hTwo, hJ]
  refine runs_seq_store_le (x := dst + 3) (v := tot) ?_ ?_ ?_
  · simp [Expr.eval, startState, Function.update, hThree, hD3]
  · have hk' : tb + Ms.length < 2 ^ w := hAbk
    have ha : tb + Ms.length ≠ dst := by change tb + k ≠ dst; omega
    have hb : tb + Ms.length ≠ dst + 1 := by change tb + k ≠ dst + 1; omega
    have hc : tb + Ms.length ≠ dst + 2 := by change tb + k ≠ dst + 2; omega
    have ht : mem (tb + Ms.length) = 2 * tot := hTot
    simp [Expr.eval, startState, Function.update_of_ne, hk', hTwo, ha, hb, hc, ht, hT]
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _)) ?_ ?_
  · let next := Function.update (Function.update (Function.update (Function.update mem dst src)
      (dst + 1) n) (dst + 2) j) (dst + 3) tot
    refine ⟨tb, dst, rfl, ?_, ?_⟩
    · intro a ha
      have ha' : a < 4 := ha
      have hf : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
      change next (dst + a) = (matchReadWords Ms tb i)[a]
      rcases hf with rfl | rfl | rfl | rfl
      all_goals simp [next, matchReadWords, Function.update, src, k, j, n, tot]
    · intro a ha
      change next a = mem a
      simp [next, Function.update_of_ne, show a ≠ dst by omega, show a ≠ dst + 1 by omega,
        show a ≠ dst + 2 by omega, show a ≠ dst + 3 by omega]
  · simp [buildMatchReadContract, Expr.size]

end MinCostFlow.HierPaths
