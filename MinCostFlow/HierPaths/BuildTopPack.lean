module

public import MinCostFlow.HierPaths.BuildProgCsr
public import MinCostFlow.HierPaths.InitProg

/-!
# Packing the static hierarchy output

The six section bodies are stored consecutively with a table of lengths.
The compressed-list writer places the directory and copies the bodies.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The six row bodies required by the static output layout. -/
def buildTopSections (S : StaticData) (i : ℕ) : List ℕ := S.sections.getD i []

@[simp] theorem buildTopSections_count (S : StaticData) : S.sections.length = 6 := by
  simp [StaticData.sections]

theorem buildTopSections_encode (S : StaticData) :
    csrList 6 (buildTopSections S) = S.encode := by
  unfold StaticData.encode layoutList buildTopSections
  rw [buildTopSections_count]

/-- Packing the six static sections into the public static output layout. -/
theorem buildTopPack_meetsContract {w f off copy : ℕ} {p : Program}
    (hp : p.procs[f]? = some (csrProc off copy))
    (hoff : p.procs[off]? = some offsetsProc) (hcopy : p.procs[copy]? = some buildCopyProc)
    (S : StaticData) :
    MeetsContract w p f (csrContract w (buildTopSections S)) :=
  csrProc_meetsContract hp hoff hcopy

end MinCostFlow.HierPaths

end
