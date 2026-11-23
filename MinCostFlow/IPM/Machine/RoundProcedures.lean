module

public import MinCostFlow.IPM.Machine.RoundCycleRepair
public import MinCostFlow.IPM.Machine.RoundRelink
public import MinCostFlow.IPM.Machine.RoundFindRoot
public import MinCostFlow.IPM.Machine.RoundPathSum

/-!
# Procedure addresses for the rounder

The machine rounder links the fixed-point arithmetic, recursive
cleanup and forest-operation adapters by their entry addresses.
Their specifications come from the corresponding verified bodies.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Entry addresses for the rounding procedures. -/
structure RoundProcedures where
  findRoot : ℕ
  pathSum : ℕ
  pathMin : ℕ
  pathAdd : ℕ
  link : ℕ
  cut : ℕ
  pack : ℕ
  packLink : ℕ
  integer : ℕ
  less : ℕ
  availability : ℕ
  pathZero : ℕ
  delta : ℕ
  coordinate : ℕ
  copy : ℕ
  cleanup : ℕ
  push : ℕ
  repair : ℕ
  relink : ℕ

/-- Program placement and numeric contracts used by the rounder.
The forest itself is passed separately through its WordRAM interface. -/
structure RoundProcedures.Linked (B : RoundProcedures) (w h P : ℕ) (p : Program)
    (op : ℕ → ℕ) : Prop where
  root_at : p.procs[B.findRoot]?=some (roundFindRootBody (op 0))
  pathSum_at : p.procs[B.pathSum]?=some (roundPathSumBody (op 5))
  pathMin_at : p.procs[B.pathMin]?=some (roundForestPathMinBody (op 4))
  pathAdd_at : p.procs[B.pathAdd]?=some (roundPathAddBody (op 3))
  link_at : p.procs[B.link]?=some (roundLinkBody (op 1))
  cut_at : p.procs[B.cut]?=some (roundFlushCutBody B.copy (op 2))
  pack_spec : ∀ e, MeetsContract w p B.pack (roundLinkRecordContract w h P e)
  packLink_at : p.procs[B.packLink]?=some (roundPackLinkBody B.pack B.link)
  integer_spec : MeetsContract w p B.integer (Num.isIntegerContract w h)
  less_spec : MeetsContract w p B.less (Num.lessContract w h)
  availability_spec : MeetsContract w p B.availability (roundAvailabilityContract w h)
  pathZero_spec : MeetsContract w p B.pathZero (roundPathZeroContract w h P)
  delta_spec : ∀ q hit, MeetsContract w p B.delta (roundDeltaContract w h P q hit)
  coordinate_spec : ∀ q δ backward,
    MeetsContract w p B.coordinate (roundStoreCoordinateContract w h P q δ backward)
  copy_spec : MeetsContract w p B.copy (copyWordsContract w)
  cleanup_at : p.procs[B.cleanup]?=some (roundCleanupBody B.cleanup B.pathMin B.pathZero B.cut)
  push_at : p.procs[B.push]?=some (roundCyclePushBody B.pathMin B.delta B.coordinate B.pathAdd)
  repair_at : p.procs[B.repair]?=some (roundCycleRepairBody B.push B.cleanup)
  relink_at : p.procs[B.relink]?=some (roundRelinkBody B.integer B.availability B.packLink)

end MinCostFlow.IPM.Machine
