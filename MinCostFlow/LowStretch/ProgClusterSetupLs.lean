module

public import MinCostFlow.LowStretch.ProgClusterSetupRn
public import MinCostFlow.LowStretch.ProgramRest

/-!
# The setup of a cluster in the program `lsstP`

The setup at index `68` of `lsstP` meets its contract `setupC` (`setup_meets_lsst`), as
`lowStretchSpanningTree_of_setup` asks. The callees are those of `setupCallees_meets`, except
that the setup reads `drawP` at `48` through the contract `drawC2`, which `drawP_spec2` gives
from the same callees as `lsstP_draw`. With it, `lowStretchSpanningTree_of_setup` gives
`lowStretchSpanningTree_lsst`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- `drawP` at `48` meets `drawC2`. -/
theorem lsstP_draw2 {w : ℕ} : MeetsContract w lsstP 48 (drawC2 w) := by
  have hP := petalProcs_meets (w := w) lsstP_petals
  have hStep : MeetsContract w lsstP 38 (dijStepC w) := petalProcs_dijStep lsstP_petals
  exact drawP_spec2 (lsstP_at 1 (by decide))
    (arcP_spec (lsstP_at 2 (by decide)) (lsstP_at 3 (by decide)) (lsstP_at 4 (by decide))
      (lsstP_at 5 (by decide)))
    hP.2.2.2.1 (dijRun_spec (lsstP_at 6 (by decide)) hP.2.1 hStep)
    (maxP_spec (lsstP_at 7 (by decide)))

/-- **The setup at `68` meets its contract.** -/
theorem setup_meets_lsst {w : ℕ} : MeetsContract w lsstP 68 (setupC w) := by
  obtain ⟨hproc, hLg, -, hTr, hHf, hAc, hPg, hCp, hHl, hEx, hMx, hP2, hSq, hCl⟩ :=
    setupCallees_meets (w := w)
  exact setup_meets hproc hLg lsstP_draw2 hTr hHf hAc hPg hCp hHl hEx hMx hP2 hSq hCl

/-- The explicit word-size constant `340 + bodyA` (`= 20000340`) of `lsstP`. -/
def lsstWordConst : ℕ := 340 + bodyA

/-- The explicit stretch and running-time constant `lowStretchConst bodyA` (`= 5005385063200`)
of `lsstP`. -/
def lsstK : ℝ := lowStretchConst bodyA

/-- **[AN19] Theorem 1 for the program `lsstP` with explicit constants** `lsstWordConst` and
`lsstK`, exposing the concrete constants proved by `lowStretch_of_cl_explicit`. -/
theorem lowStretchSpanningTree_lsst_explicit :
    ∀ G : WGraph, G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
      (∀ e ∈ G.edges, 1 ≤ e.2.2) → ∀ ω, ∃ out cost,
        RunsTo (wordSize lsstWordConst G.encode) lsstP G.encode ω out cost ∧ G.IsSpanningTree out ∧
        G.totalStretch out ≤ lsstK * G.m * logLogFactor G.n ∧
        (cost : ℝ) ≤ lsstK * (G.m + 1) * (logLogFactor G.n + weightFactor G.n G.maxWeight) := by
  obtain ⟨h30, h31, h32, h33⟩ := lsstBody_procs restProcs 68 55
  have hBody : ∀ w, MeetsBody w bodyA lsstP 30 := fun w => by
    refine bodyP_meets h30 ?_ (by unfold bodyA; omega)
    obtain ⟨hS, hPush, hPS, hClr, hF, hT, hbP, hCp⟩ := petalProcs_meets (w := w) h33
    exact nodeP_meets h31 (setupCJ_of setup_meets_lsst) hS hPush hPS hClr hF hT hbP hCp h32
      (regPrefix_of lsstP_petals) childP_meets (fun _ _ _ _ _ h => h.nodes_le)
      (fun _ _ _ _ _ _ _ _ _ _ hpre hD _ hk => hpre.reset_lt hD hk)
  have hRec : ∀ w, MeetsRec w bodyA lsstP 29 := fun w =>
    recP_meets (lsstProg_rec _) (hBody w) (copy_at_26 (lsstProg_entry _))
      (by unfold recK bodyA; omega)
  exact lowStretch_of_cl_explicit (lsstProg_entry _) fun w _ _ =>
    rootP_meets (lsstProg_root _) (lsstProg_mx _) (hRec w)

/-- **[AN19] Theorem 1 for the program `lsstP`**, with the setup of `setup_meets_lsst`. -/
theorem lowStretchSpanningTree_lsst : LowStretchSpanningTree :=
  lowStretchSpanningTree_of_setup fun _ => setup_meets_lsst

end MinCostFlow.LowStretch
