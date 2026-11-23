module

public import MinCostFlow.LinkCut.Path.Steps
public import MinCostFlow.LinkCut.Gen.Descend
public import MinCostFlow.LinkCut.PathTree.FindModel
import MinCostFlow.Num.SignFacts

/-!
# The readiness tests of the path payload

A summary is ready when its detector flag is set and the detector is not negative; a value is
ready when it is an edge and its detector is not negative. A `K`-limb number is negative
exactly when its top limb is at least half the base (`intVal_neg_iff_top`), so each test reads
two words.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree

/-- `sumTest [a]` for the path payload, on the record at `a`: `K` is word `9`, the flag of the
summary is at `a + 12 + 6 K`, and the top limb of the detector at `a + 12 + 7 K`. -/
def pathSumTestBody (h : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .cond (.load (kAddr 12 6))
    (.ret (.bin .lt (.load (kAddr 12 7)) (.const (base h / 2))))
    (.ret (.const 0))

/-- `valTest [a]` for the path payload, on the value block at `a`: `K` is word `3`, the edge
header is at `a + 4`, and the top limb of the detector at `a + 5 + 4 K`. -/
def pathValTestBody (h : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .cond (.load (.bin .add (.reg 0) (.const 4)))
    (.ret (.bin .lt (.load (kAddr 5 4)) (.const (base h / 2))))
    (.ret (.const 0))

theorem pathSumTestBody_noRand (h : ℕ) : (pathSumTestBody h).NoRand := by
  simp [pathSumTestBody, Stmt.NoRand]

theorem pathValTestBody_noRand (h : ℕ) : (pathValTestBody h).NoRand := by
  simp [pathValTestBody, Stmt.NoRand]

/-- A `K`-limb number is not negative exactly when its top limb is below half the base. -/
theorem nonneg_iff_top {mem : ℕ → ℕ} {a h K : ℕ} {z : ℤ} (hh : 0 < h)
    (hz : PathIntAt mem a h (K + 1) z) : 0 ≤ z ↔ mem (a + K) < base h / 2 := by
  have := intVal_neg_iff_top hh hz.1
  rw [hz.2] at this
  constructor
  · intro h0; by_contra hc; push_neg at hc; exact absurd (this.mpr hc) (by omega)
  · intro h0; by_contra hc; push_neg at hc; exact absurd (this.mp hc) (by omega)

theorem pathSumTest_meetsContract {w h K f : ℕ} {p : Program} (hh : 0 < h) (hK : 0 < K)
    (hbase : base h < 2 ^ w) (hb : p.procs[f]? = some (pathSumTestBody h)) :
    MeetsContract w p f (sumTestContract (pathLayout h K) pathRs w 40) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, v, s, rfl, ha, hv, hs⟩
  rw [pathLayout_stride] at ha
  have hKm : mem (a + 9) = K := (hv : PathValAt mem (a + 6) h K v).2.2.2.1
  have hhalf : base h / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hbase
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  -- the answer for any summary stored in the record at `a`
  have key : ∀ s' : PathSummary,
      (pathLayout h (K' + 1)).SumAt mem (a + (pathLayout h (K' + 1)).offSum) s' →
      (if mem (a + (12 + 6 * (K' + 1))) = 0 then 0
        else if mem (a + (12 + 7 * (K' + 1))) < base h / 2 then 1 else 0) =
        if pathRs s' then 1 else 0 := by
    intro s' hs'
    rw [pathLayout_offSum] at hs'
    obtain ⟨-, -, hd⟩ := (hs' : PathSummaryAt mem _ h (K' + 1) s')
    unfold pathRs
    cases hz : s'.detector with
    | none =>
      simp only [hz] at hd
      rw [show a + (12 + 4 * (K' + 1)) + 2 * (K' + 1) = a + (12 + 6 * (K' + 1)) by ring] at hd
      simp [hd]
    | some z =>
      simp only [hz] at hd
      obtain ⟨h1, hzv⟩ := hd
      rw [show a + (12 + 4 * (K' + 1)) + 2 * (K' + 1) = a + (12 + 6 * (K' + 1)) by ring] at h1
      have := nonneg_iff_top hh hzv
      rw [show a + (12 + 4 * (K' + 1)) + 2 * (K' + 1) + 1 + K' = a + (12 + 7 * (K' + 1)) by ring]
        at this
      simp [h1, this]
  apply runs_start_le
  unfold pathSumTestBody
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hKm) ?_
  refine runs_cond_le (by eval_expr) ?_ ?_
  · intro hne
    refine runs_ret_le (by eval_expr) ⟨rfl, fun s' hs' => ?_⟩ ?_
    · rw [← key s' hs', if_neg (show mem (a + (12 + 6 * (K' + 1))) ≠ 0 from hne)]
      rfl
    · simp only [sumTestContract, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
        kAddr, kAt, kOff]
      omega
  · intro h0
    refine runs_ret_le (by eval_expr) ⟨rfl, fun s' hs' => ?_⟩ ?_
    · rw [← key s' hs', if_pos (show mem (a + (12 + 6 * (K' + 1))) = 0 from h0)]
      rfl
    · simp only [sumTestContract, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
        kAddr, kAt, kOff]
      omega

theorem pathValTest_meetsContract {w h K f : ℕ} {p : Program} (hh : 0 < h) (hK : 0 < K)
    (hbase : base h < 2 ^ w) (hb : p.procs[f]? = some (pathValTestBody h)) :
    MeetsContract w p f (valTestContract (pathLayout h K) pathRv w 40) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, v, rfl, ha, hv⟩
  change a + (6 + 4 * K) < 2 ^ w at ha
  have hKm : mem (a + 3) = K := (hv : PathValAt mem a h K v).2.2.2.1
  have hhalf : base h / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hbase
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have key : ∀ v' : Option PathEdgeValue, (pathLayout h (K' + 1)).ValAt mem a v' →
      (if mem (a + 4) = 0 then 0
        else if mem (a + (5 + 4 * (K' + 1))) < base h / 2 then 1 else 0) =
        if pathRv v' then 1 else 0 := by
    intro v' hv'
    have hv'' := (hv' : PathValAt mem a h (K' + 1) v').2.2.2.2
    unfold pathRv
    cases v' with
    | none =>
      change mem (a + 4) = 0 at hv''
      simp [hv'']
    | some e =>
      obtain ⟨h1, -, -, -, -, hzv⟩ := hv''
      have := nonneg_iff_top hh hzv
      rw [show a + 4 + 2 + 3 * (K' + 1) + K' = a + (5 + 4 * (K' + 1)) by ring] at this
      simp [h1, this]
  apply runs_start_le
  unfold pathValTestBody
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hKm) ?_
  refine runs_cond_le (by eval_expr) ?_ ?_
  · intro hne
    refine runs_ret_le (by eval_expr) ⟨rfl, fun v' hv' => ?_⟩ ?_
    · rw [← key v' hv', if_neg (show mem (a + 4) ≠ 0 from hne)]
      rfl
    · simp only [valTestContract, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
        kAddr, kAt, kOff]
      omega
  · intro h0
    refine runs_ret_le (by eval_expr) ⟨rfl, fun v' hv' => ?_⟩ ?_
    · rw [← key v' hv', if_pos (show mem (a + 4) = 0 from h0)]
      rfl
    · simp only [valTestContract, Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load,
        kAddr, kAt, kOff]
      omega

end MinCostFlow.LinkCut.Path
