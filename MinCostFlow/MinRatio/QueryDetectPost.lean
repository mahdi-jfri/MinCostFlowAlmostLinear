module

public import MinCostFlow.MinRatio.QueryOutputModel
public import MinCostFlow.MinRatio.DetectOutput
public import MinCostFlow.Chain.Theorem5_1Helpers
public import MinCostFlow.IPM.Machine.MinRatioContract

/-!
# The Query and Detect boundary of Algorithm 2

The output routines write the layouts expected by the IPM. Once the
resolved edge value or list of reported edges is correct, their
postconditions imply the output part of the min-ratio machine contract.
Detect also preserves the fixed-point representability of every flow
coordinate, since it resets only detection accounts.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- Writing the resolved original-direction coordinate gives the
Query postcondition of Definition 4.5 (page 14). -/
theorem queryOutput_minRatio_post {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle heap edge address ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailure cfg).State} {mem mem' : ℕ → ℕ} {value : PathEdgeValue}
    (hv : PathEdgeAt mem address F.fmt.limbBits F.limbs (some value))
    (hflow : (value.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision =
      algorithm2_query cfg s edge)
    (hout : (queryOutputContract w F.fmt.limbBits F.fmt.precision).post
      [address + 2 + 2 * F.limbs, (if value.forward then 1 else 0), F.limbs, heap] mem ret mem') :
    (minRatioMachineContract F (algorithm2_dsWithFailure cfg) G m κ α rate allocation).post
      1 s [handle, edge, heap] mem s mem' :=
  ⟨rfl, queryOutput_algorithm2_scalar hv hflow hout⟩

/-- Detect's report and account resets give the IPM postcondition.
The reset leaves each modeled flow coordinate equal to its old value. -/
theorem detectFinish_minRatio_post {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle heap ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailureWith cfg κ).State} {mem mem' : ℕ → ℕ} {reported : List ℕ}
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs F.fmt.precision s)
    (hset : ∀ e, e ∈ reported ↔ e ∈ s.extG.E ∧ cfg.ε ≤ s.extℓ e * s.detectAccum e)
    (hout : (detectFinishContract w reported).post [heap, reported.length] mem ret mem') :
    (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate allocation).post
      2 s [handle, heap] mem (algorithm2_detect cfg s).2 mem' := by
  refine ⟨rfl, detectFinish_algorithm2_set hset hout, ?_⟩
  intro e he
  exact hfit e he

end MinCostFlow.MinRatio
