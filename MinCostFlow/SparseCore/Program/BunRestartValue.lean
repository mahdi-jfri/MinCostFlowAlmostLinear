module

public import MinCostFlow.SparseCore.Program.BunRestartRun

/-!
# The restart of the bundles: the value of the interface (`BunRestartValue`)

`bunRestartAtK` is a value of `BunRestartAtK w slotCap eCap p f` on P5's representation of the
table (`bunTableRep slotCap vCap eCap`), the tour of P5's tour queries (`BundleTourAt`) and P5's
invariant (`bunRestartInv`). Procedure `f` of `p` is `bunRestartStmt` (a single fixed program for
every bundle cap `k`, which is read at run time from the table block), and the other procedures it
calls are in `p`.

The cost multiplier is the number `brMul TS = 4000 + 6 TS.mul` (`bunRestartAtK_mul`). The space is
the linear function `x ↦ brSpaceC TS cT · (x + 1)` (`bunRestartAtK_space`), where `cT`
bounds the space of the tour list query: `TS.listSpace len ≤ cT · (len + 1)`. Both constants do
not depend on the input of a run or on `slotCap`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

variable {w slotCap vCap eCap cT : ℕ} {p : Program} {TS : BundleTourSpec}
  {bTourList bTourLen bOwner bWalk bSort bInit bDllPush bExport f : ℕ}

@[expose] public section

/-- **The value of the bundle restart.** The hypotheses are on the word size, the caps, the space
of the tour list query, and the procedures of `p`. The bundle cap `k` is stored in the table block
and read at run time. -/
def bunRestartAtK (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    (hw : 16 ≤ 2 ^ w) (heCap : 2 * eCap < 2 ^ w) (hvCap : vCap ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hpf : p.procs[f]? = some (bunRestartStmt bWalk bOwner bSort bInit bExport))
    (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ prevBase nextBase headAddr key L, MeetsContract w p bDllPush
      (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt]) :
    BunRestartAtK w slotCap eCap p f where
  rep := bunTableRep slotCap vCap eCap
  tour := htour.rep
  inv := bunRestartInv vCap eCap
  mul := brMul TS
  space x := brSpaceC TS cT * (x + 1)
  rep_local k := bunTableRep_local slotCap vCap eCap k
  tour_local := htour.rep_local
  runs := by
    intro k tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω _ htourH _ _ _ hlist hsl hnd
      hact hk1 hcore hinv hrep hrepT hfoot hfootT hdisj hz hfit
    have C : BRCtx htour slotCap tbl tourH slotsPtr h slots S x cord tx cs ord mem :=
      ⟨hw, heCap, hvCap, htourH, hrep.1, hinv, hcore, hrepT, hfoot, hfootT, hdisj, hact, hnd, hlist,
        hsl, hz⟩
    obtain ⟨v, st', c, T', M', tx', hr, htab, hk', _, htr, hinv', hun, hlisted, hlo, hhi, hz', hfr, hft,
        hftr, hdj, hc⟩ :=
      brRun (ω := ω) (k := k) C hpWalk hpSort hpInit hbPush hpExport hk1 hrep.2 hLS hfit pos
    refine ⟨_, hpf, .returned v, st', c, T', M', tx', hr, ⟨htab, hk'⟩, htr, hinv', hun, hlisted,
      hlo, hhi, hz', hfr, hft, hftr, hdj, ?_⟩
    rw [bunTablePhi_eq (k := k) htab, bunTablePhi_eq (k := k) hrep.1]
    exact hc

/-- **The value of the bundle restart on `bunTableHeadroomRep`**: same fixed program, multiplier,
and linear space as `bunRestartAtK`, while establishing and preserving `bunTableHeadroomInv`. -/
def bunRestartAtK_headroom (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    (hw : 16 ≤ 2 ^ w) (heCap : 2 * eCap < 2 ^ w) (hvCap : vCap ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hpf : p.procs[f]? = some (bunRestartStmt bWalk bOwner bSort bInit bExport))
    (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ prevBase nextBase headAddr key L, MeetsContract w p bDllPush
      (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt]) :
    BunRestartAtK w slotCap eCap p f where
  rep := bunTableHeadroomRep slotCap vCap eCap
  tour := htour.rep
  inv := bunRestartInv vCap eCap
  mul := brMul TS
  space x := brSpaceC TS cT * (x + 1)
  rep_local k := bunTableHeadroomRep_local slotCap vCap eCap k
  tour_local := htour.rep_local
  runs := by
    intro k tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω _ htourH _ _ _ hlist hsl hnd
      hact hk1 hcore hinv hrep hrepT hfoot hfootT hdisj hz hfit
    have C : BRCtx htour slotCap tbl tourH slotsPtr h slots S x cord tx cs ord mem :=
      ⟨hw, heCap, hvCap, htourH, hrep.1, hinv, hcore, hrepT, hfoot, hfootT, hdisj, hact, hnd, hlist,
        hsl, hz⟩
    obtain ⟨v, st', c, T', M', tx', hr, htab, hk', hH', htr, hinv', hun, hlisted, hlo, hhi, hz', hfr, hft,
        hftr, hdj, hc⟩ :=
      brRun (ω := ω) (k := k) C hpWalk hpSort hpInit hbPush hpExport hk1 hrep.2.1 hLS hfit pos
    refine ⟨_, hpf, .returned v, st', c, T', M', tx', hr, ⟨htab, hk', hH' hrep.2.2⟩, htr, hinv', hun,
      hlisted, hlo, hhi, hz', hfr, hft, hftr, hdj, ?_⟩
    rw [bunTableHeadroomPhi_eq (k := k) htab, bunTableHeadroomPhi_eq (k := k) hrep.1]
    exact hc

end

public section

variable (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
  (hw : 16 ≤ 2 ^ w) (heCap : 2 * eCap < 2 ^ w) (hvCap : vCap ≤ 2 ^ w)
  (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
  (hpf : p.procs[f]? = some (bunRestartStmt bWalk bOwner bSort bInit bExport))
  (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
  (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
  (hbPush : ∀ prevBase nextBase headAddr key L, MeetsContract w p bDllPush
    (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
  (hpExport : p.HasAt bExport [bundleExportGraphStmt])

/-- **The space of the bundle restart is linear.** It is `brSpaceC TS cT · (x + 1)`, and
`brSpaceC TS cT = 39 + 2 TS.querySpace + 4 cT` does not depend on the input of a run or on
`slotCap`. -/
theorem bunRestartAtK_space (x : ℕ) :
    (bunRestartAtK (slotCap := slotCap) htour hw heCap hvCap hLS hpf hpWalk hpSort hpInit
      hbPush hpExport).space x = brSpaceC TS cT * (x + 1) := rfl

/-- **The cost multiplier of the bundle restart** is `4000 + 6 TS.mul`, which does not depend on
the input of a run. -/
theorem bunRestartAtK_mul :
    (bunRestartAtK (slotCap := slotCap) htour hw heCap hvCap hLS hpf hpWalk hpSort hpInit
      hbPush hpExport).mul = 4000 + 6 * TS.mul := rfl

end

end MinCostFlow.SparseCore.Program.Restart
