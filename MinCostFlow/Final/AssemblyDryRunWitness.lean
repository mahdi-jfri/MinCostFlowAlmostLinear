module

public import MinCostFlow.Final.AssemblyDryRunSigs
public import MinCostFlow.LastLevelProgram.RelocatedProgram
import Mathlib.Tactic

/-!
# The last-level tool and the chain witness of the dry run

The package `DyadicWithVConcretePrograms` starts with a last-level tool, its specification, and
the chain witness `ConcreteChainWitnessWithLast`. Here we build these three fields.

* The last-level tool is the fixed-point tool of the last-level program
  (`packedLastLevelProgram_implements`). That theorem gives the program and the tool together, so
  we choose them together: the tool `dryLastTool` is the one the program implements.
* The witness is `concreteChainWitnessWithLastOf` with the family of canonical LSF initializers
  of piece P3, one for each number format `(L_in, P_fp)`, and the canonical sparsifier
  `canonicalSparsify impl`. Both data fields are the arguments, by definition
  (`dryWitness_lsfInit`, `dryWitness_sparsify`). The configuration of each instance uses the
  member at the solver's format (`concreteCirculationCfgWithLast_T`).

The witness here takes two inputs. The first is an initializer `canonicalLSFInit` with the
statement `sig_canonicalLSFInit_spec` of piece P3. The dry run uses
`SparseCore.Program.canonicalLSFInit`, which meets it (`canonicalLSFInit_spec`). The sparsifier
program `impl` must meet `SparsifyImplHyp`: unit time factor, `p_s = p_t = 1`, and `γ` bounds
`exp(C_sp log^{7/8}(m + 2))`. The program `sparsifyImplUsed` of the library meets it
(`sparsifyImplHyp_sparsifyImplUsed`, `Final/SparsifyImplHyp.lean`), and the dry run uses it. From
the statement of P3 we get the constant `C_lsst` with `IsConcreteLSFInit`
(`isConcreteLSFInit_of_approx`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program
  MinCostFlow.Chain MinCostFlow.LastLevelProgram

/-! ## The last-level tool -/

/-- The data of `packedLastLevelProgram_implements`: guest program, word constant, the two
constants of the canonical stretch, and the oracle, chosen together. -/
def lastGuest : Program := Classical.choose packedLastLevelProgram_implements

/-- The word constant of the last-level program. -/
def lastWordConst : ℕ := Classical.choose (Classical.choose_spec packedLastLevelProgram_implements)

/-- The stretch constant `K` of the last-level program. -/
def lastK : ℝ := Classical.choose (Classical.choose_spec
  (Classical.choose_spec packedLastLevelProgram_implements))

/-- The fallback constant of the last-level program. -/
def lastFallback : ℝ := Classical.choose (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec packedLastLevelProgram_implements)))

/-- The oracle of the last-level program. -/
def lastOracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec packedLastLevelProgram_implements))))

/-- The constant `C` of the fixed-point tool. -/
def lastCanonConst : ℝ := graphCanonicalConstant lastK lastFallback

/-- The last-level tool of the dry run: the fixed-point tool that the last-level program
implements. -/
def dryLastTool : LastLevelTool := fixedPointLastLevelTool lastOracle lastCanonConst

/-- The constant of `lastLevelParams` for `dryLastTool`. -/
def dryLastConstant : ℝ := 128 * max 1 lastCanonConst

/-- `dryLastTool` meets Definition 5.8 (pages 19–20) at `lastLevelParams dryLastConstant`. -/
theorem dryLastSpec : dryLastTool.IsSpec (lastLevelParams dryLastConstant) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec packedLastLevelProgram_implements))))).1

/-- The same choice also gives the program: the last-level program implements the runtime
contract of `dryLastTool` on every connected graph. -/
theorem dryLast_implements :
    ∀ {w L vCap eCap : ℕ} (fmt : Num.Format w) (G : MGraph),
      fmt.limbBits = 4 →
      (∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) → G.n ≤ G.m + 1 →
      (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
        w (packedLastLevelProgram lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst) 15 (fun _ => 16)
        (MinRatio.lastLevelRuntimeMachineContract fmt L dryLastTool G vCap eCap
          (packedLastLevelMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK G L)
          ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (G.m + 1).size)
          (packedRuntimeAllocation G lastGuest lastCanonConst lastWordConst L vCap eCap)) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec packedLastLevelProgram_implements))))).2

/-- The relocated last-level bodies `packedLastLevelBodies` implement the runtime contract of
`dryLastTool` inside any host program embedding them at `b`, at entries `b + 15` and
`fun _ => b + 16`. -/
theorem dryLastBodies_implements {p : Program} {b : ℕ}
    (hp : p.HasAt b (packedLastLevelBodies lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst b)) :
    ∀ {w L vCap eCap : ℕ} (fmt : Num.Format w) (G : MGraph),
      fmt.limbBits = 4 →
      (∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) → G.n ≤ G.m + 1 →
      (lastLevelRepresentation vCap eCap 4 L fmt.precision G.E).Implements
        w p (b + 15) (fun _ => b + 16)
        (MinRatio.lastLevelRuntimeMachineContract fmt L dryLastTool G vCap eCap
          (packedLastLevelMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK G L)
          ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (G.m + 1).size)
          (packedRuntimeAllocation G lastGuest lastCanonConst lastWordConst L vCap eCap)) := by
  intro w L vCap eCap fmt G hfmt hconn hn
  have h := dryLast_implements (L := L) (vCap := vCap) (eCap := eCap) fmt G hfmt hconn hn
  rw [hfmt] at h
  exact MinRatio.dsRep_implements_shift hp h

/-! ## The LSF initializer -/

/-- From the hypotheses of `lemma_5_5_approx` with constants `C₀ α K_σ K_ρ` (`1 ≤ K_ρ`), the
initializer fits the concrete chain at `C_lsst = max K_σ (3 K_ρ max K_σ (max (112 (1 + α)
max 1 C₀) 2240))`: both conditions of `IsConcreteLSFInit` hold, since
`mwuK0 C_lsst = 6272 max 1 C_lsst ≥ C_lsst`. -/
theorem isConcreteLSFInit_of_approx {lsfInit : LSFInit} {C₀ α K_σ K_ρ : ℝ}
    (hA : IsApproxMWUInit lsfInit C₀ α K_σ K_ρ) (hK : 1 ≤ K_ρ) :
    Chain.Ordered.IsConcreteLSFInit lsfInit
      (max K_σ (3 * K_ρ * max K_σ (max (112 * (1 + α) * max 1 C₀) 2240))) := by
  set C := max K_σ (3 * K_ρ * max K_σ (max (112 * (1 + α) * max 1 C₀) 2240)) with hC
  have h1 : C ≤ mwuK0 C := by
    unfold mwuK0
    have := le_max_right 1 C
    have := le_max_left 1 C
    linarith
  refine ⟨C₀, α, K_σ, K_ρ, hA, hK, (le_max_left _ _).trans h1, ?_⟩
  have h2 : 3 * K_ρ * max K_σ (max (112 * (1 + α) * max 1 C₀) 2240) ≤ C := le_max_right _ _
  have h3 : 0 ≤ mwuK0 C := (mwuK0_pos C).le
  linarith

/-- The `[AN19]` program of the library, chosen once with its full specification (`FullAN19Spec`)
and explicit constants. -/
def anProgram : Program := Classical.choose an19_full_of_lowStretchSpanningTree

/-- The word constant of `anProgram`. -/
def anWordConst : ℕ := Classical.choose (Classical.choose_spec an19_full_of_lowStretchSpanningTree)

/-- The stretch constant of `anProgram`. -/
def anK : ℝ := Classical.choose (Classical.choose_spec
  (Classical.choose_spec an19_full_of_lowStretchSpanningTree))

/-- `anProgram`, `anWordConst`, `anK` satisfy `FullAN19Spec` (both `1 ≤ anWordConst` and the
`[AN19]` running-time bound). -/
theorem an_fullSpec : FullAN19Spec anProgram anWordConst anK :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec an19_full_of_lowStretchSpanningTree))).1

/-- `1 ≤ anWordConst`, projected from `an_fullSpec`. -/
theorem anWordConst_pos : 1 ≤ anWordConst := an_fullSpec.1

/-- Exact value `anWordConst = anWordConstBound` (`= 20000340`). -/
theorem anWordConst_eq : anWordConst = anWordConstBound :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec an19_full_of_lowStretchSpanningTree))).2.1

/-- Explicit upper bound `anWordConst ≤ anWordConstBound` (`= 20000340`). -/
theorem anWordConst_le : anWordConst ≤ anWordConstBound := anWordConst_eq.le

/-- Exact value `anK = (anKBound : ℝ)` (`= 5005385063200`). -/
theorem anK_eq : anK = (anKBound : ℝ) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec an19_full_of_lowStretchSpanningTree))).2.2

/-- Explicit upper bound `anK ≤ (anKBound : ℝ)` (`= 5005385063200`). -/
theorem anK_le : anK ≤ (anKBound : ℝ) := anK_eq.le

/-- Stretch-only `[AN19]` hypothesis `AN19Hyp`, projected from `an_fullSpec`. -/
theorem an_hyp : AN19Hyp anProgram anWordConst anK :=
  fullAN19_to_stretchOnly an_fullSpec

/-- Explicit value of `defaultC_ceil anK` (`= 20021540252805`). -/
theorem anDefaultC_ceil_eq :
    MinCostFlow.LSF.Program.defaultC_ceil anK = 20021540252805 := by
  unfold MinCostFlow.LSF.Program.defaultC_ceil
  rw [anK_eq]
  have hmax : max (anKBound : ℝ) 1 = (anKBound : ℝ) :=
    max_eq_left (by unfold anKBound; norm_num)
  rw [hmax, Nat.ceil_natCast]
  unfold anKBound
  norm_num

/-- Explicit value of `defaultK_sigma anK` (`= 5904592479035228160`). -/
theorem anDefaultK_sigma_eq :
    MinCostFlow.LSF.Program.defaultK_sigma anK = 5904592479035228160 := by
  unfold MinCostFlow.LSF.Program.defaultK_sigma
  rw [anDefaultC_ceil_eq]

section Witness

variable (canonicalLSFInit : Program → ℕ → ℝ → ℕ → ℕ → LSFInit)
  (hP3 : sig_canonicalLSFInit_spec canonicalLSFInit)

/-- The family of LSF initializers of the dry run: P3's initializer on the library's `[AN19]`
program, in the number format `(L_in, P_fp)` (limbs, precision). -/
def dryLSFInit (L_in P_fp : ℕ) : LSFInit := canonicalLSFInit anProgram anWordConst anK L_in P_fp

/-- The constant `K_ρ` that the statement of P3 gives for `dryLSFInit`, the same for every
format. -/
def dryKρ : ℝ := Classical.choose (hP3 anProgram anWordConst anK an_hyp)

theorem dryKρ_spec :
    1 ≤ dryKρ canonicalLSFInit hP3 ∧ ∀ L_in P_fp,
      IsApproxMWUInit (dryLSFInit canonicalLSFInit L_in P_fp) (4 * max anK 1 + 5) (5 / 4)
        (MinCostFlow.LSF.Program.defaultK_sigma anK) (dryKρ canonicalLSFInit hP3) :=
  Classical.choose_spec (hP3 anProgram anWordConst anK an_hyp)

/-- The constant `C_lsst` of the core tool, from `isConcreteLSFInit_of_approx`. It does not
depend on the format. -/
def dryCLsst : ℝ :=
  max (MinCostFlow.LSF.Program.defaultK_sigma anK : ℝ)
    (3 * dryKρ canonicalLSFInit hP3 *
      max (MinCostFlow.LSF.Program.defaultK_sigma anK : ℝ)
        (max (112 * (1 + 5 / 4) * max 1 (4 * max anK 1 + 5)) 2240))

/-- Every member of the family fits the one constant `dryCLsst`. -/
theorem dryLSFInit_concrete (L_in P_fp : ℕ) :
    Chain.Ordered.IsConcreteLSFInit (dryLSFInit canonicalLSFInit L_in P_fp)
      (dryCLsst canonicalLSFInit hP3) :=
  isConcreteLSFInit_of_approx ((dryKρ_spec canonicalLSFInit hP3).2 L_in P_fp)
    (dryKρ_spec canonicalLSFInit hP3).1

end Witness

/-! ## The sparsifier -/

/-- What the chain needs from a sparsifier program `impl`, in the form of the hypothesis
`hp_spec` of `concreteChainWitnessWithLastOf` for `canonicalSparsifyParams impl`: unit time
factor (so that `canonicalSparsify_spec` applies), `p_s = p_t = 1`, and both `γ` factors at most
`exp(C_sp log^{7/8}(m + 2))` (Theorem 8.1, page 39). The program `sparsifyImplUsed` meets it
(`sparsifyImplHyp_sparsifyImplUsed`). -/
def SparsifyImplHyp (impl : SparsifyImpl) (C_sp : ℝ) : Prop :=
  0 < C_sp ∧ impl.p_s = 1 ∧ impl.p_t = 1 ∧ (∀ m, impl.γ_t m = 1) ∧
    ∀ m : ℕ, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      impl.γ_c m + 1 ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))

theorem hp_spec_of_sparsifyImplHyp {impl : SparsifyImpl} {C_sp : ℝ} (h : SparsifyImplHyp impl C_sp)
    (m : ℕ) :
    (canonicalSparsifyParams impl m).K_s = impl.K_s ∧ (canonicalSparsifyParams impl m).p_s = 1 ∧
      (canonicalSparsifyParams impl m).K_t = 2 * impl.K_t + 1 ∧
      (canonicalSparsifyParams impl m).p_t = 1 ∧
      (canonicalSparsifyParams impl m).γ_ℓ ≤
        Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (canonicalSparsifyParams impl m).γ_c ≤
        Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
  ⟨rfl, h.2.1, rfl, h.2.2.1, (h.2.2.2.2 m).1, (h.2.2.2.2 m).2⟩

/-! ## The witness -/

section Witness

variable (canonicalLSFInit : Program → ℕ → ℝ → ℕ → ℕ → LSFInit)
  (hP3 : sig_canonicalLSFInit_spec canonicalLSFInit)
  (impl : SparsifyImpl) (C_sp : ℝ) (hImpl : SparsifyImplHyp impl C_sp)

/-- The chain witness of the dry run, by `concreteChainWitnessWithLastOf` with the data of this
file. Only its constants `C_γ` and `M_thresh` are chosen. -/
def dryWitness : ConcreteChainWitnessWithLast dryLastTool dryLastConstant dryLastSpec :=
  concreteChainWitnessWithLastOf dryLastTool dryLastConstant dryLastSpec
    (dryLSFInit canonicalLSFInit) (dryCLsst canonicalLSFInit hP3)
    (dryLSFInit_concrete canonicalLSFInit hP3)
    (canonicalSparsify impl) (canonicalSparsifyParams impl) C_sp impl.K_s (2 * impl.K_t + 1)
    hImpl.1 impl.hK_s (by linarith [impl.hK_t]) (hp_spec_of_sparsifyImplHyp hImpl)
    (fun m => canonicalSparsify_spec impl m (hImpl.2.2.2.1 m))
    (dsAmortConst impl) (by unfold dsAmortConst; omega)

theorem dryWitness_lsfInit :
    (dryWitness canonicalLSFInit hP3 impl C_sp hImpl).lsfInit =
      fun L_in P_fp => canonicalLSFInit anProgram anWordConst anK L_in P_fp := rfl

theorem dryWitness_sparsify :
    (dryWitness canonicalLSFInit hP3 impl C_sp hImpl).sparsify = canonicalSparsify impl :=
  rfl

theorem dryWitness_params :
    (dryWitness canonicalLSFInit hP3 impl C_sp hImpl).params = canonicalSparsifyParams impl :=
  rfl

theorem dryWitness_spanConst :
    (dryWitness canonicalLSFInit hP3 impl C_sp hImpl).spanConst = dsAmortConst impl :=
  rfl

theorem dryWitness_C_lsst :
    (dryWitness canonicalLSFInit hP3 impl C_sp hImpl).C_lsst = dryCLsst canonicalLSFInit hP3 :=
  rfl

end Witness

end MinCostFlow.Final.DryRun
