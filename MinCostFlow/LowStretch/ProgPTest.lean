module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The two tests of a candidate radius

`ptest` reads the five sums of region growing at `SUM` (see `psum`): the count `I`, the plus and
minus parts of `C`, and the plus and minus parts of `V'`. With `C = C+ - C-`, `V' = V'+ - V'-`
and `vol8 = 8 M (κ + I) + r C - V'`, it returns `1` when both
* `C · sq ≤ vol8` (the first test, see `test1_iff`), and
* `vol8 · 2^λ ≤ 8 M (4 (κ + nact) + κ · 2^λ)` (the volume test, see `test2_iff`)

hold, and `0` otherwise. It does not change the memory (`ptest_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers that `ptest` uses. `P2` stands for `2^λ`. -/
structure PT where
  r : ℕ
  SUM : ℕ
  M : ℕ
  κ : ℕ
  sq : ℕ
  P2 : ℕ
  nact : ℕ

namespace PT

variable (F : PT) (mem : ℕ → ℕ)

def args : List ℕ := [F.r, F.SUM, F.M, F.κ, F.sq, F.P2, F.nact]

theorem eq_of_args {F F' : PT} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [PT.args, List.cons.injEq] at h
  simp_all

/-- The count of pairs inside. -/
def I : ℕ := mem F.SUM
/-- The scaled cost. -/
def C : ℕ := mem (F.SUM + 1) - mem (F.SUM + 2)
/-- The weighted sum of entry costs. -/
def V : ℕ := mem (F.SUM + 3) - mem (F.SUM + 4)
/-- Eight times the scaled volume. -/
def vol8 : ℕ := 8 * F.M * (F.κ + F.I mem) + F.r * F.C mem - F.V mem
/-- The right side of the volume test. -/
def rhs : ℕ := 8 * F.M * (4 * (F.κ + F.nact) + F.κ * F.P2)

/-- Both tests pass. -/
def Pass : Prop := F.C mem * F.sq ≤ F.vol8 mem ∧ F.vol8 mem * F.P2 ≤ F.rhs

/-- The precondition of `ptest`: all the values it computes are words. -/
structure Pre (w : ℕ) : Prop where
  hM : 1 ≤ F.M
  hκ : 1 ≤ F.κ
  lw : F.SUM + 4 < 2 ^ w
  w1 : 8 * F.M * (F.κ + F.I mem) + F.r * F.C mem < 2 ^ w
  w2 : F.C mem * F.sq < 2 ^ w
  w3 : F.rhs < 2 ^ w
  w4 : F.vol8 mem * F.P2 < 2 ^ w
  w5 : mem (F.SUM + 1) < 2 ^ w
  w6 : mem (F.SUM + 3) < 2 ^ w

end PT

/-- `ptest` with `args = F.args`. -/
def ptest : Stmt :=
  .seq (.assign 7 (.load (.reg 1)))
  (.seq (.assign 8 (.bin .sub (.load (.bin .add (.reg 1) (.const 1)))
    (.load (.bin .add (.reg 1) (.const 2)))))
  (.seq (.assign 9 (.bin .sub (.load (.bin .add (.reg 1) (.const 3)))
    (.load (.bin .add (.reg 1) (.const 4)))))
  (.seq (.assign 10 (.bin .sub (.bin .add (.bin .mul (.bin .mul (.const 8) (.reg 2))
      (.bin .add (.reg 3) (.reg 7))) (.bin .mul (.reg 0) (.reg 8))) (.reg 9)))
  (.cond (.bin .lt (.reg 10) (.bin .mul (.reg 8) (.reg 4))) (.ret (.const 0))
    (.cond (.bin .lt (.bin .mul (.bin .mul (.const 8) (.reg 2))
        (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 3) (.reg 6)))
          (.bin .mul (.reg 3) (.reg 5))))
        (.bin .mul (.reg 10) (.reg 5)))
      (.ret (.const 0)) (.ret (.const 1)))))))

theorem ptest_noRand : ptest.NoRand := by simp [ptest, Stmt.NoRand]

open Classical in
/-- The contract of `ptest`. -/
noncomputable def ptestC (w : ℕ) : Contract where
  pre args mem := ∃ F : PT, args = F.args ∧ F.Pre mem w
  post args mem v mem' := mem' = mem ∧ ∀ F : PT, args = F.args → v = if F.Pass mem then 1 else 0
  cost _ _ := 100

theorem ptest_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [ptest]) :
    MeetsContract w p b (ptestC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some ptest := hp 0 (by simp)
  clear hp
  have hwA : ∀ a ∈ F.args, a < 2 ^ w := hwords
  simp only [PT.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  obtain ⟨wr, wSUM, wM, wκ, wsq, wP2, wn⟩ := hwA
  have hM := h.hM; have hκ := h.hκ; have lw := h.lw; have w1 := h.w1; have w2 := h.w2
  have w3 := h.w3; have w4 := h.w4; have w5 := h.w5; have w6 := h.w6
  have hw8 : 8 < 2 ^ w := by
    have : 8 ≤ 8 * F.M * (F.κ + F.I mem) := by
      have := Nat.mul_le_mul (show 8 ≤ 8 * F.M by omega) (show 1 ≤ F.κ + F.I mem by omega)
      simpa using this
    omega
  have e8 : 8 * F.M ≤ 8 * F.M * (F.κ + F.I mem) := Nat.le_mul_of_pos_right _ (by omega)
  have eI : F.κ + F.I mem ≤ 8 * F.M * (F.κ + F.I mem) := Nat.le_mul_of_pos_left _ (by omega)
  have erC : F.r * F.C mem ≤ 8 * F.M * (F.κ + F.I mem) + F.r * F.C mem := Nat.le_add_left _ _
  have eR1 : 4 * (F.κ + F.nact) + F.κ * F.P2 ≤ F.rhs := Nat.le_mul_of_pos_left _ (by omega)
  have eR2 : 8 * F.M ≤ F.rhs := Nat.le_mul_of_pos_right _ (by omega)
  have eR3 : F.κ * F.P2 ≤ 4 * (F.κ + F.nact) + F.κ * F.P2 := Nat.le_add_left _ _
  have eR4 : 4 * (F.κ + F.nact) ≤ 4 * (F.κ + F.nact) + F.κ * F.P2 := Nat.le_add_right _ _
  have hC : F.C mem ≤ mem (F.SUM + 1) := Nat.sub_le _ _
  have hV : F.V mem ≤ mem (F.SUM + 3) := Nat.sub_le _ _
  have hvol : F.vol8 mem ≤ 8 * F.M * (F.κ + F.I mem) + F.r * F.C mem := Nat.sub_le _ _
  unfold PT.rhs at eR1 eR2 w3
  unfold PT.vol8 at hvol w4
  unfold PT.C at hC erC w1 w2 hvol w4
  unfold PT.V at hV hvol w4
  unfold PT.I at e8 eI erC w1 hw8 hvol w4
  refine ⟨ptest, hproc, ?_⟩
  obtain ⟨r, SUM, M, κ, sq, P2, nact⟩ := F
  dsimp only at *
  simp only [PT.args]
  have w5' : (startState [r, SUM, M, κ, sq, P2, nact] mem pos).mem (SUM + 1) < 2 ^ w := w5
  have w6' : (startState [r, SUM, M, κ, sq, P2, nact] mem pos).mem (SUM + 3) < 2 ^ w := w6
  dsimp only [ptest]
  refine runs_start_le ?_
  wram_run
  all_goals first
    | (simp only [ptestC]; wram_cost)
    | (simp only [ptestC, Outcome.value]
       refine ⟨by simp [startState], fun F' he => ?_⟩
       obtain rfl := PT.eq_of_args (F := ⟨r, SUM, M, κ, sq, P2, nact⟩) he
       first
         | (rw [if_neg (by simp only [PT.Pass, PT.C, PT.V, PT.vol8, PT.rhs, PT.I]; omega)])
         | (rw [if_pos (by simp only [PT.Pass, PT.C, PT.V, PT.vol8, PT.rhs, PT.I]; omega)]))

end MinCostFlow.LowStretch
