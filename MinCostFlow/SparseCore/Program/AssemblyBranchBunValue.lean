module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartIface
public import MinCostFlow.SparseCore.Program.BunRestartValue

/-!
# P5's restart as the interface of the branch (`AssemblyBranchBunValue`)

The restart of a branch takes P5's restart through the interface `AsmBrBunAt`
(`AssemblyBranchRestartIface.lean`): for all bundle caps `k`, caps, orders, forests, core lists and
marks, a run on the bundle table `B5 k slotCap vCap eCap` and on P5's view of P2's tour of the
branch, `asmTourCordView (TR vCap eCap) vo vf vc mk`. P5 proves its restart as `bunRestartAtK`
(`BunRestartValue.lean`), on its table `bunTableRep slotCap vCap eCap k` (which holds `k` in a
word) and on a tour with P5's three tour queries (`BundleTourAt`), for fixed caps and every `k`.

This file shows that `bunRestartAtK` gives `AsmBrBunAt` with `B5 k := bunTableRep · · · k`, once
P5's view
of the tour has P5's tour queries. That step is the tour conversion from P2's contract.
Here it is a hypothesis, `AsmBrTourBridge`: for all caps, orders, forests,
core lists and marks, a `BundleTourAt` whose representation is P5's view
`asmTourCordView (TR vCap eCap) vo vf vc mk`. The space of the tour list
query must be linear, `TS.listSpace len ≤ cT · (len + 1)`; this is a hypothesis too.

The result is `asmBrBunAt_of_bunRestart`. Its multiplier `asmBrBunMul TS cT` pays both the cost of
P5's restart (`brMul TS`) and its space (`brSpaceC TS cT slotCap`, which has the term
`2 · slotCap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- **The tour conversion for P5**, for P2's tour family `TR` of the branch: for all caps `vCap`,
`eCap`, orders `vo`, forests `vf`, core lists `vc` and marks `mk`, procedures `bList`, `bLen`,
`bOwner` of `p` are P5's tour queries (`BundleTourAt` with spec `TS`) on P5's view
`asmTourCordView (TR vCap eCap) vo vf vc mk`. -/
def AsmBrTourBridge (TS : BundleTourSpec) (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (p : Program)
    (bList bLen bOwner : ℕ) : Prop :=
  ∀ (vCap eCap : ℕ) (vo : ℕ → List End) (vf : RootedForest) (vc : ℕ → List End) (mk : Finset End),
    ∃ T : BundleTourAt TS w vCap eCap p bList bLen bOwner,
      T.rep = asmTourCordView (TR vCap eCap) vo vf vc mk

/-- The multiplier of P5's restart in the branch: the cost multiplier `brMul TS` of
`bunRestartAtK`, and enough to cover its space constant `brSpaceC TS cT slotCap` per factor
`slotCap + 1`. -/
def asmBrBunMul (TS : BundleTourSpec) (cT : ℕ) : ℕ :=
  brMul TS + 29 + 2 * TS.querySpace + 4 * cT

/-- The space of P5's restart is at most `asmBrBunMul TS cT · (slotCap + 1) · (n + 1)`. -/
theorem brSpaceC_le (TS : BundleTourSpec) (cT slotCap n : ℕ) :
    brSpaceC TS cT * (n + 1) ≤ asmBrBunMul TS cT * (slotCap + 1) * (n + 1) := by
  apply Nat.mul_le_mul_right
  have h1 : asmBrBunMul TS cT * (slotCap + 1) = asmBrBunMul TS cT * slotCap + asmBrBunMul TS cT :=
    by ring
  rw [h1]
  unfold brSpaceC asmBrBunMul brMul
  omega

variable {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs} {w cT : ℕ} {p : Program}
  {bTourList bTourLen bOwner bWalk bSort bInit bDllPush bExport f : ℕ}

/-- **P5's restart meets the interface of the branch.** Given the tour conversion `hT`, the linear
space of the tour list query, the word size and the procedures of `p` that
`bunRestartAtK` asks, P5's restart is an `AsmBrBunAt` on the table `bunTableRep` with multiplier
`asmBrBunMul TS cT` and space `brSpaceC TS cT · (x + 1)`, for every bundle cap `k`. A run first
replaces the caps of the table by those of the tour (they are equal), then takes the tour queries
of `hT` for these caps, order, forest, core lists and marks of the run, and runs `bunRestartAtK`
on them at the cap `k` of the run. -/
def asmBrBunAt_of_bunRestart (hT : AsmBrTourBridge TS TR w p bTourList bTourLen bOwner)
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hpf : p.procs[f]? = some (bunRestartStmt bWalk bOwner bSort bInit bExport))
    (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ eCap prevBase nextBase headAddr key L, MeetsContract w p bDllPush
      (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt]) :
    AsmBrBunAt TR (fun k slotCap vCap eCap => bunTableRep slotCap vCap eCap k) w p f where
  mul := asmBrBunMul TS cT
  space _ x := brSpaceC TS cT * (x + 1)
  space_le slotCap n := brSpaceC_le TS cT slotCap n
  rep_local k slotCap vCap eCap := bunTableRep_local slotCap vCap eCap k
  runs := by
    intro k slotCap vCap₅ eCap₅ vCap eCap vo vf vc mk hv he heW hvW
    subst hv he
    obtain ⟨⟨rep, hloc, hlist, hlen, howner⟩, hrep⟩ := hT vCap₅ eCap₅ vo vf vc mk
    subst hrep
    intro tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω htbl htourH hn hsp hh hlistS
      hsl hnd hact hk hcore hinv hrepS hrepT hfoot hfootT hdisj hz hfit
    let T : BundleTourAt TS w vCap₅ eCap₅ p bTourList bTourLen bOwner :=
      ⟨asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk, hloc, hlist, hlen, howner⟩
    let I := bunRestartAtK (slotCap := slotCap) (cT := cT) T hw heW hvW hLS hpf hpWalk
      hpSort hpInit (hbPush eCap₅) hpExport
    obtain ⟨body, hb, o, st', c, S', x', tx', hrun, hrS, hrT, hinv', hun, hlisted, hlo, hhi, hz',
        hfr, hft, hftT, hdj, hc⟩ :=
      I.runs k tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω htbl htourH hn hsp hh hlistS
        hsl hnd hact hk hcore hinv hrepS hrepT hfoot hfootT hdisj hz hfit
    have hc' : c + (bunTableRep slotCap vCap₅ eCap₅ k).phi tbl x' st'.mem +
        (asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk).phi tourH tx' st'.mem ≤
        brMul TS * (cs.G.m + slots.length + 1) * ordStoreLog eCap₅ +
          (bunTableRep slotCap vCap₅ eCap₅ k).phi tbl x mem +
          (asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk).phi tourH tx mem := hc
    refine ⟨body, hb, o, st', c, S', x', tx', hrun, hrS, hrT, hinv', hun, hlisted, hlo, hhi, hz',
      hfr, hft, hftT, hdj, le_trans hc' ?_⟩
    have hm : brMul TS ≤ asmBrBunMul TS cT := by unfold asmBrBunMul; omega
    have := Nat.mul_le_mul_right (ordStoreLog eCap₅)
      (Nat.mul_le_mul_right (cs.G.m + slots.length + 1) hm)
    omega

/-- **Exposed `AsmBrBunAt` for P5's headroom restart (`bunTableHeadroomRep`)**: same statement and
proof as `asmBrBunAt_of_bunRestart_headroom`, placed in `@[expose] public section` so callers can
reduce `.mul = asmBrBunMul TS cT` definitionally. -/
def asmBrBunAt_headroom_of_bunRestart (hT : AsmBrTourBridge TS TR w p bTourList bTourLen bOwner)
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hpf : p.procs[f]? = some (bunRestartStmt bWalk bOwner bSort bInit bExport))
    (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ eCap prevBase nextBase headAddr key L, MeetsContract w p bDllPush
      (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt]) :
    AsmBrBunAt TR (fun k slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap k) w p f where
  mul := asmBrBunMul TS cT
  space _ x := brSpaceC TS cT * (x + 1)
  space_le slotCap n := brSpaceC_le TS cT slotCap n
  rep_local k slotCap vCap eCap := bunTableHeadroomRep_local slotCap vCap eCap k
  runs := by
    intro k slotCap vCap₅ eCap₅ vCap eCap vo vf vc mk hv he heW hvW
    subst hv he
    obtain ⟨⟨rep, hloc, hlist, hlen, howner⟩, hrep⟩ := hT vCap₅ eCap₅ vo vf vc mk
    subst hrep
    intro tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω htbl htourH hn hsp hh hlistS
      hsl hnd hact hk hcore hinv hrepS hrepT hfoot hfootT hdisj hz hfit
    let T : BundleTourAt TS w vCap₅ eCap₅ p bTourList bTourLen bOwner :=
      ⟨asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk, hloc, hlist, hlen, howner⟩
    let I := bunRestartAtK_headroom (slotCap := slotCap) (cT := cT) T hw heW hvW hLS hpf hpWalk
      hpSort hpInit (hbPush eCap₅) hpExport
    obtain ⟨body, hb, o, st', c, S', x', tx', hrun, hrS, hrT, hinv', hun, hlisted, hlo, hhi, hz',
        hfr, hft, hftT, hdj, hc⟩ :=
      I.runs k tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω htbl htourH hn hsp hh hlistS
        hsl hnd hact hk hcore hinv hrepS hrepT hfoot hfootT hdisj hz hfit
    have hc' : c + (bunTableHeadroomRep slotCap vCap₅ eCap₅ k).phi tbl x' st'.mem +
        (asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk).phi tourH tx' st'.mem ≤
        brMul TS * (cs.G.m + slots.length + 1) * ordStoreLog eCap₅ +
          (bunTableHeadroomRep slotCap vCap₅ eCap₅ k).phi tbl x mem +
          (asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk).phi tourH tx mem := hc
    refine ⟨body, hb, o, st', c, S', x', tx', hrun, hrS, hrT, hinv', hun, hlisted, hlo, hhi, hz',
      hfr, hft, hftT, hdj, le_trans hc' ?_⟩
    have hm : brMul TS ≤ asmBrBunMul TS cT := by unfold asmBrBunMul; omega
    have := Nat.mul_le_mul_right (ordStoreLog eCap₅)
      (Nat.mul_le_mul_right (cs.G.m + slots.length + 1) hm)
    omega

end MinCostFlow.SparseCore.Program
