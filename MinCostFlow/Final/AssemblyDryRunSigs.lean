module

public import MinCostFlow.Final.ForestConcretePrograms
public import MinCostFlow.SparseCore.Program.Contract
public import MinCostFlow.LSF.Program.Layout
public import MinCostFlow.DynSpanner.Program.CanonicalSparsify
public import MinCostFlow.DynSpanner.Program.DynSpannerDSBank
public import MinCostFlow.Statement.Cited.AbrahamNeiman
public import MinCostFlow.SparseCore.Program.LSFWindowLSST
import MinCostFlow.LowStretch.ProgClusterSetupLs
import Mathlib.Tactic.NormNum

/-!
# Statements of two pieces used by the dry run of the final assembly

The final assembly of Theorem 1.1 (page 2) fills the package `DyadicWithVConcretePrograms`. Here
we write the statements of two of its pieces as `Prop`s, so that the dry run
(`Final/AssemblyDryRun.lean`) can take them as hypotheses.

* `sig_canonicalLSFInit_spec` is the statement of piece P3 (the canonical LSF initializer), for an
  initializer `canonicalLSFInit` given as a parameter. The library proves it for
  `SparseCore.Program.canonicalLSFInit` (`canonicalLSFInit_spec`,
  `SparseCore/Program/LSFWindowSpec.lean`).
* `sig_sparseCoreOrdProgram_implements` is the statement of piece P9 (the sparse-core program),
  with the machine-cost tool `sparseCoreBundleRestartToolMachWith` that the chain uses.

We also check one thing that is already in the library: the hypothesis of P3 on the
`[AN19]` program holds for the program of `lowStretchSpanningTree_lsst`
(`an19_hyp_of_lowStretchSpanningTree`).
-/

@[expose] public section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program
  MinCostFlow.Chain

/-- The hypothesis of P3 on a Word-RAM program `Q_AN` for `[AN19]`: on every connected loopless
weighted graph with weights at least one, it returns a spanning tree of total stretch at most
`K_AN · m · logLogFactor n`. -/
def AN19Hyp (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) : Prop :=
  ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
    (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
    ∃ out cost,
      RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
        G_a.IsSpanningTree out ∧
        G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n

/-- Statement of piece P3, for a given initializer
`canonicalLSFInit`: if `Q_AN` meets `AN19Hyp`, the initializer meets the hypotheses of
`lemma_5_5_approx` (Lemma 5.5, page 18) with `α = 5/4`, in every number format `(L_in, P_fp)`.
The constant `K_ρ` comes before the format, so one constant serves every format. -/
def sig_canonicalLSFInit_spec (canonicalLSFInit : Program → ℕ → ℝ → ℕ → ℕ → LSFInit) : Prop :=
  ∀ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
    AN19Hyp Q_AN c_AN K_AN →
    ∃ K_ρ : ℝ, 1 ≤ K_ρ ∧ ∀ (L_in P_fp : ℕ),
      IsApproxMWUInit (canonicalLSFInit Q_AN c_AN K_AN L_in P_fp) (4 * max K_AN 1 + 5) (5 / 4)
        (MinCostFlow.LSF.Program.defaultK_sigma K_AN) K_ρ

/-- Statement of piece P9 for the tool that the chain
uses, `sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L (fun _ => canonicalSparsify impl)`:
the program `p` with entries `init` and `op` implements the ordered sparse-core contract. -/
def sig_sparseCoreOrdProgram_implements (E : SparseCoreEnv) (lsfInit : LSFInit)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
    ∀ (w : ℕ) (fmt : Num.Format w) (L : ℕ) (G : MGraph) (k M N vCap eCap : ℕ),
      ∃ R : DSRep (SparseCoreOrdAbs (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L
          (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl))),
        R.Local ∧ R.Implements w p init op
          (sparseCoreOrdMachineContract fmt L
            (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L
              (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl))
            G k M N vCap eCap P allocation)

/-- Concrete word-size constant `340 + bodyA` (`= 20000340`) of `lowStretchSpanningTree_lsst`. -/
def anWordConstBound : ℕ := 20000340

/-- Concrete stretch and running-time constant `Kst + (800000000 + 250000 * bodyA)`
(`= 5005385063200`) of `lowStretchSpanningTree_lsst`. -/
def anKBound : ℕ := 5005385063200

/-- The program of `lowStretchSpanningTree_lsst` (`[AN19]`, Theorem 1, proved in the library)
meets the full specification `FullAN19Spec` (both `1 ≤ c_AN` and the running-time bound) with
explicit constants `c_AN = anWordConstBound` and `K_AN = (anKBound : ℝ)`. -/
theorem an19_full_of_lowStretchSpanningTree :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      FullAN19Spec Q_AN c_AN K_AN ∧
      c_AN = anWordConstBound ∧
      K_AN = (anKBound : ℝ) := by
  refine ⟨MinCostFlow.LowStretch.lsstP, MinCostFlow.LowStretch.lsstWordConst,
    MinCostFlow.LowStretch.lsstK, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold MinCostFlow.LowStretch.lsstWordConst MinCostFlow.LowStretch.bodyA
    omega
  · intro G hV hL hC hw
    exact MinCostFlow.LowStretch.lowStretchSpanningTree_lsst_explicit G hV hL hC hw (fun _ => false)
  · unfold MinCostFlow.LowStretch.lsstWordConst MinCostFlow.LowStretch.bodyA anWordConstBound
    rfl
  · unfold MinCostFlow.LowStretch.lsstK MinCostFlow.LowStretch.lowStretchConst
      MinCostFlow.LowStretch.Kst MinCostFlow.LowStretch.bodyA anKBound
    norm_num

/-- The program of `lowStretchSpanningTree_lsst` (`[AN19]`, Theorem 1, proved in the library)
meets the hypothesis of P3. We drop its running-time clause and run it on the all-`false` random
tape. -/
theorem an19_hyp_of_lowStretchSpanningTree :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ), AN19Hyp Q_AN c_AN K_AN := by
  obtain ⟨P, c, K, hfull, _, _⟩ := an19_full_of_lowStretchSpanningTree
  exact ⟨P, c, K, fullAN19_to_stretchOnly hfull⟩

end MinCostFlow.Final.DryRun
