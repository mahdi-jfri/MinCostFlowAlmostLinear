module

public import MinCostFlow.HierPaths.BuildProgLevelModel
public import MinCostFlow.HierPaths.BuildProgChoiceHistory
import MinCostFlow.HierPaths.BuildChildHost
public import MinCostFlow.HierPaths.BuildProgChoiceGeom

/-!
# Level guarantees from the game trace

A certified loop supplies the finished child states and the occurrence
bound of their archived walks. The final injection completes the child
families. A parent of singleton children only needs its sibling calls.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The level for singleton children has no child edges or embedding walks. -/
theorem levelData_singleton_good {route : RouterFn} {routeCost : RouterCostFn} {G : Graph}
    {start k M r Δ L L' bh : ℕ} {β : ℝ}
    (hRouter : IsMatchingPlayer route routeCost) (hPos : 0 < β)
    (hExp : G.IsExpansionExpanderOn (buildLevelVerts start 1 k) β)
    (hH : HostPre G (buildLevelVerts start 1 k) Δ L) (hBh : max 2 (2/β) ≤ (bh : ℝ)) :
    (levelDataOfFamily route G start 1 k Δ L (fun _ => [])).Good G start 1 k M r Δ L L' bh := by
  apply levelDataOfFamily_good hRouter hPos hExp hH le_rfl hBh
  · intro c hc
    simp [Graph.IsValid,Graph.IsLoopless,Graph.deg,Graph.degIn,Graph.inside]
  · intro e _
    simp [walkFamily,occLoad]

/-- The actual certified run, followed by its final injection, has exactly
the mathematical guarantees of the child construction (`lemma_3`) and the sibling connectors used by the level contract. -/
theorem ChoiceLoopTrace.levelGood {w : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh heap : ℕ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts mem)
    (h : ChoiceGameHyp D β bh) (hk : 1 ≤ D.count) (hs : 1 < D.base.childSize)
    (hVerts : D.base.verts = buildLevelVerts D.first D.base.childSize D.count) :
    let F := finishedChildFamily D.base.route D.base.host D.base.verts D.base.Δ D.base.L
      D.base.childSize D.count D.offset sts
    (levelDataOfFamily D.base.route D.base.host D.first D.base.childSize D.count D.base.Δ D.base.L F).Good
      D.base.host D.first D.base.childSize D.count D.base.M D.base.r D.base.Δ D.base.L D.L' bh := by
  let F := finishedChildFamily D.base.route D.base.host D.base.verts D.base.Δ D.base.L
    D.base.childSize D.count D.offset sts
  obtain ⟨hInv,hLoad⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
    h.denominator h.children h.even (coreLevel_le h.coreSize)
  have hDone := CertifiedGame.all_saved h.children.1 h.sizeLog hInv
  obtain ⟨hHosts,hLoad'⟩ := lemma_3_of_finished_game h.router h.host h.positive h.expansion
    h.denominator h.children hk hInv hLoad hDone
  have hExp : D.base.host.IsExpansionExpanderOn (buildLevelVerts D.first D.base.childSize D.count) β :=
    hVerts ▸ h.expansion
  have hHost : HostPre D.base.host (buildLevelVerts D.first D.base.childSize D.count) D.base.Δ D.base.L :=
    hVerts ▸ h.host
  apply levelDataOfFamily_good h.router h.positive hExp hHost hs.le h.denominator
  · intro c hc
    obtain ⟨hExp,hValid,hLoop,hDeg,hMap,hEntry⟩ := hHosts c hc
    have hF : ∀ en ∈ F c, EntryOK D.base.host D.base.verts (D.first+c*D.base.childSize)
        (routePathLen D.base.Δ bh D.base.L) en := hEntry
    refine ⟨?_,?_,?_,fun he => by omega,?_,?_⟩
    · rwa [hMap]
    · rwa [hMap]
    · rwa [hMap]
    · intro _
      rwa [hMap]
    · rw [← hVerts]
      exact hF
  · exact hLoad'

end MinCostFlow.HierPaths
