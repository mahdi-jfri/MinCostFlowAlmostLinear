module

public import MinCostFlow.NarrowTop.Statement
public import MinCostFlow.NarrowTop.HostSolver
public import MinCostFlow.NarrowTop.WordBounds
public import MinCostFlow.NarrowTop.TimeBound
public import MinCostFlow.NarrowTop.Program
public import MinCostFlow.NarrowTop.Main
public import MinCostFlow.NarrowTop.Stage0Calls
public import MinCostFlow.Final.Theorem11Bundle

/-!
# The narrow-word top theorem (`narrowStatement_of_dyadic_withV`, `narrowStatement_proved`)

Assembles `NarrowMinCostFlowStatement` from `DyadicWithVConcretePrograms` using:
- the linked deterministic program `narrowProgram` (`NarrowTop/Program.lean`) with the outer
  `narrowMain` module (`NarrowTop/Main.lean`) and host-width solver adapter
  `narrowSolverAdapter` (`NarrowTop/HostSolver.lean`),
- the proved word-size bounds (`NarrowTop/WordBounds.lean`) and almost-linear time bound
  (`NarrowTop/TimeBound.lean`), and
- the factored unconditional solver bundle `Final.DryRun.dryDyadicWithVBundle_proved`
  (`MinCostFlow/Final/Theorem11Bundle.lean`).
-/

@[expose] public section

open WordRAM Filter Topology
open MinCostFlow.Scaling MinCostFlow.Scaling.Machine MinCostFlow.Final
open MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowTop

/-- Interface package for the word-bound and time-bound theorems (`NarrowTop/WordBounds.lean` and
`NarrowTop/TimeBound.lean`). -/
structure NarrowBoundsPkg where
  /-- Word-size multiplier `c` as a function of `P.scratchDegree`. -/
  wordMult : ℕ → ℕ
  /-- `NarrowMainFits` holds at `wordSize (wordMult d) (narrowEncode I)` for every valid `I`
  and any solver space `S` bounded by `8 * (n + m + 2) ^ (42 * scratchWordMultiplier 1 d)`. -/
  fits : ∀ {d : ℕ} {S : ℕ → ℕ → ℕ},
    (∀ n m, S n m ≤ 8 * (n + m + 2) ^ (42 * scratchWordMultiplier 1 d)) →
    ∀ (I : Instance) (hv : I.IsValid),
      NarrowMainFits (wordSize (wordMult d) (narrowEncode I)) S I hv
  /-- Input length and every input word fit in `wordSize (wordMult d) (narrowEncode I)`. -/
  wordsAndLen : ∀ (d : ℕ) (I : Instance),
    (narrowEncode I).length < 2 ^ wordSize (wordMult d) (narrowEncode I) ∧
    ∀ x ∈ narrowEncode I, x < 2 ^ wordSize (wordMult d) (narrowEncode I)
  /-- Monotone Stage 1 cost envelope `narrowStage1CostEnvelope T_sol m U C`. -/
  stage1Env : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ
  /-- Monotonicity of `stage1Env` in `(m, U, C)`. -/
  stage1Env_mono : ∀ {T_sol : ℕ → ℕ → ℕ}, SolverTimeMonotone T_sol →
    ∀ {m m' U U' C C' : ℕ}, m ≤ m' → U ≤ U' → C ≤ C' →
      stage1Env T_sol m U C ≤ stage1Env T_sol m' U' C'
  /-- `narrowStage1CostShape T_sol K k` is bounded by `stage1Env T_sol K.m (circMaxCapacity K) (circMaxCost K)`. -/
  stage1Shape_le : ∀ {T_sol : ℕ → ℕ → ℕ}, SolverTimeMonotone T_sol →
    ∀ (K : Circulation) (k : ℕ),
      narrowStage1CostShape T_sol K k ≤
        stage1Env T_sol K.m (circMaxCapacity K) (circMaxCost K)
  /-- Outer time constant `K` as a function of `(A, B, a0, a1)`. -/
  timeConst : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- Vanishing edge exponent `ε(m)` as a function of `(P, A, B, a0, a1)`. -/
  timeExp : DyadicWithVConcretePrograms → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  /-- `timeExp P A B a0 a1` tends to `0`. -/
  timeExp_tendsto : ∀ (P : DyadicWithVConcretePrograms) (A B a0 a1 : ℕ),
    Tendsto (timeExp P A B a0 a1) atTop (𝓝 0)
  /-- Total outer cost bound implies `timeBound (timeConst A B a0 a1) (timeExp P A B a0 a1) I`. -/
  cost_le_timeBound : ∀ (P : DyadicWithVConcretePrograms) {T_sol : ℕ → ℕ → ℕ} {A B : ℕ},
    SolverTimeMonotone T_sol →
    (∀ n m, T_sol n m ≤ A * linkedForestSolverTime P.runtimeResources (2 * m) m + B * (m + 1)) →
    ∀ (a0 a1 : ℕ) (I : Instance) (cost : ℕ),
      cost ≤ a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) +
        a1 * (stage1Env T_sol (3 * I.m) (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
              stage1Env T_sol (2 * I.m) (2 * I.maxCapacity) I.maxCost) + 2 →
      (cost : ℝ) ≤ timeBound (timeConst A B a0 a1) (timeExp P A B a0 a1) I

/-- Proved instance of `NarrowBoundsPkg` from `WordBounds.lean` and `TimeBound.lean`. -/
noncomputable def narrowBoundsPkg : NarrowBoundsPkg where
  wordMult := narrowWordMultiplier
  fits := fun {_ _} hS I hv => narrowMainFits_wordSize hS I hv
  wordsAndLen := narrowEncode_words_and_len_lt
  stage1Env := narrowStage1CostEnvelope
  stage1Env_mono := fun {_} hmono {_ _ _ _ _ _} hm hU hC =>
    narrowStage1CostEnvelope_mono hmono hm hU hC
  stage1Shape_le := fun {_} hmono K k => stage1CostShape_le_envelope hmono K k
  timeConst := narrowTimeConstant
  timeExp := narrowTimeExponent
  timeExp_tendsto := narrowTimeExponent_tendsto
  cost_le_timeBound := fun P {_ _ _} hmono hle a0 a1 I cost hcost =>
    narrowCost_le_timeBound P hmono hle a0 a1 I cost hcost

/-- **Theorem 1.1 (narrow-word statement, page 2)** from `DyadicWithVConcretePrograms`,
parameterized by `NarrowMainPkg` and `NarrowBoundsPkg`. -/
theorem narrowStatement_of_dyadic_withV_of_pkgs (pkg : NarrowMainPkg) (bnds : NarrowBoundsPkg) :
    DyadicWithVConcretePrograms → NarrowMinCostFlowStatement := by
  intro P
  let A := P.solver.regBound + 6
  let B := 3400 * scratchWordMultiplier 1 P.scratchDegree + P.solver.regBound + 6000
  let a0 := pkg.a0
  let a1 := narrowStage1Const
  refine ⟨narrowProgram P pkg, bnds.wordMult P.scratchDegree,
    bnds.timeConst A B a0 a1, bnds.timeExp P A B a0 a1,
    narrowProgram_isDeterministic P pkg,
    bnds.timeExp_tendsto P A B a0 a1, ?_⟩
  intro I hv ω
  have hfits := bnds.fits (narrowSolverSpace_poly P.scratchDegree) I hv
  obtain ⟨hlen, hwords⟩ := bnds.wordsAndLen P.scratchDegree I
  let Benv : ℕ → ℕ → ℕ → ℕ → ℕ := fun _ m U C => a1 * bnds.stage1Env (narrowSolverTime P) m U C
  have hBenv_mono : ∀ n n' m m' u u' c c', n ≤ n' → m ≤ m' → u ≤ u' → c ≤ c' →
      Benv n m u c ≤ Benv n' m' u' c' := fun _ _ _ _ _ _ _ _ _ hm hu hc =>
    Nat.mul_le_mul_left a1 (bnds.stage1Env_mono (narrowSolverTime_mono P) hm hu hc)
  have hBenv_ge : ∀ (K : Circulation) (k : ℕ),
      narrowStage1Const * narrowStage1CostShape (narrowSolverTime P) K k ≤
        Benv K.n K.m (circMaxCapacity K) (circMaxCost K) := fun K k =>
    Nat.mul_le_mul_left a1 (bnds.stage1Shape_le (narrowSolverTime_mono P) K k)
  obtain ⟨out, cost, hrun, hgood, hcost⟩ :=
    narrowProgram_runsTo P pkg Benv hBenv_mono hBenv_ge hv hfits hlen hwords ω
  refine ⟨out, cost, hrun, hgood, ?_⟩
  have hcost' : cost ≤ a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) +
      a1 * (bnds.stage1Env (narrowSolverTime P) (3 * I.m)
              (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
            bnds.stage1Env (narrowSolverTime P) (2 * I.m)
              (2 * I.maxCapacity) I.maxCost) + 2 := by
    dsimp only [Benv, a0] at hcost ⊢
    rw [Nat.mul_add a1]
    omega
  exact bnds.cost_le_timeBound P (narrowSolverTime_mono P) (fun _ _ => le_rfl) a0 a1 I cost hcost'

/-- **Theorem 1.1 (narrow-word statement, page 2)** from `DyadicWithVConcretePrograms`
using the proved `narrowMainPkg` and `narrowBoundsPkg`. -/
theorem narrowStatement_of_dyadic_withV (calls : Stage0CallsPkg) :
    DyadicWithVConcretePrograms → NarrowMinCostFlowStatement :=
  narrowStatement_of_dyadic_withV_of_pkgs (narrowMainPkg calls) narrowBoundsPkg

/-- **Theorem 1.1 (narrow-word statement, page 2)** with no hypothesis, instantiated with
`narrowMainPkg stage0CallsPkg`, `narrowBoundsPkg`, and the proved solver bundle
`Final.DryRun.dryDyadicWithVBundle_proved`. -/
theorem narrowStatement_proved : NarrowMinCostFlowStatement :=
  narrowStatement_of_dyadic_withV stage0CallsPkg Final.DryRun.dryDyadicWithVBundle_proved

/-! ### Equivalence with `MinCostFlowStatement` (`Statement/Main.lean`) -/

/-- `narrowEncode` agrees with `Instance.encode` (`MinCostFlow/Statement/Problem.lean`) by
unfolding (`rfl`). -/
theorem narrowEncode_eq_encode (I : Instance) : narrowEncode I = I.encode := rfl

/-- `narrowIsCorrectAnswer` agrees with `Instance.IsCorrectAnswer`
(`MinCostFlow/Statement/Problem.lean`) by unfolding (`rfl`). -/
theorem narrowIsCorrectAnswer_eq (I : Instance) :
    narrowIsCorrectAnswer I = I.IsCorrectAnswer := rfl

/-- `NarrowMinCostFlowStatement` is definitionally equal to `MinCostFlowStatement`
(`MinCostFlow/Statement/Main.lean`). -/
theorem minCostFlowStatement_of_narrow (h : NarrowMinCostFlowStatement) :
    MinCostFlowStatement := h

end MinCostFlow.NarrowTop
