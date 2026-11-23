module

public import MinCostFlow.SparseCore.Program.AssemblyTopIface
public import MinCostFlow.SparseCore.Program.AssemblyTourValid
public import MinCostFlow.SparseCore.Program.OutSpec

/-!
# The tour of a branch and its two views (`AssemblyBranchTour`)

The tour of a branch is the data of piece P2 (`TourContract.lean`). Its abstract state
holds the input order `ord`, the rooted forest `rf` of the LSF and a set of marked ends
(`AsmTourAbs`, a copy of P2's `TourAbs`). The first phase of a step cuts and links the
forest of this state, so the branch must hold the whole state, not only the core lists.

Two pieces read the tour through a smaller view:
* P7 (`OutTourAt`) sees the core lists `cord` and the marks (`OutTourAbs`);
* P5 (`BundleTourAt`) sees only the core lists, for fixed marks (`cordRepM`).
Both views are projections of P2's representation for a fixed order and forest
(`asmTourView`): the concrete state, the cells and the potential are those of P2, and the view
holds the core lists `cord` and the marks when P2 holds `⟨ord, rf, marks⟩`. The core lists are
those of the rotation of the core graph (`CoreCordOf`), so the view also asks that `cord` fits
`ord` and `rf` (`TourCordOK`).

The tour conversion proves that P2's operations give P7's and P5's
operations on these views. Here the conversion for P7 is the hypothesis `AsmBrOutProj`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.SparseCore.Program.Restart

/-- The core lists `cord` fit the order `ord` and the forest `rf`: they are the core rotation
lists of some LSF state with the forest `rf` and a rotation of order `ord` (`CoreCordOf`). -/
def TourCordOK (ord : ℕ → List End) (rf : RootedForest) (cord : ℕ → List End) : Prop :=
  ∃ cs : CompLSFState, CoreCordOf cs ord cord ∧ cs.lsf.F = rf

/-- **P7's view of P2's tour** for the order `ord`, the forest `rf` and the core lists `cord`: it
holds `⟨cord, marks⟩` when `cord` fits `ord` and `rf` and P2's tour holds `⟨ord, rf, marks⟩`, with
P2's concrete state, cells and potential. -/
def asmTourView (T : DSRep AsmTourAbs) (ord : ℕ → List End) (rf : RootedForest)
    (cord : ℕ → List End) : DSRep OutTourAbs where
  τ := T.τ
  rep b s x mem := s.cord = cord ∧ TourCordOK ord rf cord ∧ T.rep b ⟨ord, rf, s.marked⟩ x mem
  phi := T.phi
  foot := T.foot

/-- The view is local when P2's tour is. -/
theorem asmTourView_local {T : DSRep AsmTourAbs} (hT : T.Local) (ord : ℕ → List End)
    (rf : RootedForest) (cord : ℕ → List End) : (asmTourView T ord rf cord).Local := by
  intro b s x mem mem' hag
  have h := hT b ⟨ord, rf, s.marked⟩ x mem mem' hag
  exact ⟨fun ⟨hc, hok, hr⟩ => ⟨hc, hok, h.1 hr⟩, h.2⟩

/-- **The tour conversion for P7**: for all caps and every order, forest and core lists, P7's
operations (`OutTourAt` with spec `OS` and procedures `nm`, `sm`, `fm`, `lm` of `p`) run on P7's
view of the tour family `TR` of P2. The view holds only core lists that fit the order and the
forest, so the conversion may use that they fit. -/
def AsmBrOutProj (OS : OutTourSpec) (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (p : Program)
    (nm sm fm lm : ℕ) : Prop :=
  ∀ (vCap eCap : ℕ) (ord : ℕ → List End) (rf : RootedForest) (cord : ℕ → List End),
    ∃ T : OutTourAt OS w vCap eCap p nm sm fm lm, T.rep = asmTourView (TR vCap eCap) ord rf cord

/-- P7's view of the tour of a branch at the abstract state `a`: the order `a.ord`, the forest of
the LSF and the core lists `outCoreOrder a.tr a.ord`. -/
noncomputable def asmBrTourView {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (a : AsmBranchAbs depth) (vCap eCap : ℕ) : DSRep OutTourAbs :=
  asmTourView (TR vCap eCap) a.ord a.tr.cs.lsf.F (outCoreOrder a.tr a.ord)

/-- P7's view of the tour of a branch survives a change of memory outside the cells of the tour,
and its potential does not change. -/
theorem asmBrTourView_keep {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (a : AsmBranchAbs depth) {vCap eCap tourH : ℕ}
    {s : OutTourAbs} {tx : (TR vCap eCap).τ} {mem mem' : ℕ → ℕ}
    (hag : ∀ c, (TR vCap eCap).foot tourH tx c → mem c = mem' c) :
    ((asmBrTourView TR a vCap eCap).rep tourH s tx mem →
      (asmBrTourView TR a vCap eCap).rep tourH s tx mem') ∧
      (TR vCap eCap).phi tourH tx mem = (TR vCap eCap).phi tourH tx mem' :=
  asmTourView_local (hTR vCap eCap) a.ord a.tr.cs.lsf.F (outCoreOrder a.tr a.ord) tourH s tx mem
    mem' hag

end MinCostFlow.SparseCore.Program
