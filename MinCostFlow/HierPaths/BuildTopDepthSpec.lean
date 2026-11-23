module

public import MinCostFlow.HierPaths.BuildTopDepthReady

/-!
# The procedure contract for a full depth

Each graph and terminal input lies below the incoming heap and outside
the reply directory. The space check includes the prefix work and the
scratch reservation of each parent.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

namespace BuildTopDepthInput

variable (D : BuildTopDepthInput)

/-- Conditions on each level call in the initial memory of a depth. -/
def parentReady (w K h i : ℕ)
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ v ∈ D.callArgs i h, v < 2 ^ w) ∧
  (D.level w K space i).pre (D.callArgs i h) mem ∧
  (∀ x, D.graphAddr i ≤ x → x < D.graphAddr i + (D.graph i).encode.length →
    x < D.replyDir ∨ D.replyDir + D.count ≤ x) ∧
  (∀ x, D.termBase + D.start i ≤ x →
    x < D.termBase + D.start i + D.childSize * D.branch →
    x < D.replyDir ∨ D.replyDir + D.count ≤ x) ∧
  h + rangeCost (D.spaceStep space) 0 D.count +
    space (D.graph i) D.childSize D.branch D.scale D.rank D.degree D.pathLog D.coreLog
      D.denominator < 2 ^ w

def contract (w K : ℕ)
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Contract where
  pre args mem := ∃ h, args = D.args h ∧ D.childSize * D.branch < 2 ^ w ∧
    D.count < 2 ^ w ∧ h < 2 ^ w ∧ 1 < 2 ^ w ∧ ZeroFrom mem h ∧
    D.replyDir + D.count ≤ h ∧ D.graphDir + D.count ≤ h ∧
    (D.graphDir + D.count ≤ D.replyDir ∨ D.replyDir + D.count ≤ D.graphDir) ∧
    (∀ i < D.count, mem (D.graphDir + i) = D.graphAddr i) ∧
    ∀ i < D.count, D.parentReady w K h i space mem
  post args mem v mem' := ∃ h, args = D.args h ∧ h ≤ v ∧
    v ≤ h + rangeCost (D.spaceStep space) 0 D.count ∧ ZeroFrom mem' v ∧ D.frame h mem mem' ∧
    ∀ i < D.count, D.replyAt i h v mem'
  cost _ _ := rangeCost (fun i => D.work K i + 60) 0 D.count + 9 * D.count + 20

end BuildTopDepthInput

/-- All parents of the depth run against the published level contract. -/
theorem buildTopDepth_meetsContract {w K f call level : ℕ} {p : Program}
    {D : BuildTopDepthInput}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (buildTopDepth call))
    (hc : p.procs[call]? = some (buildTopParentCall level))
    (hl : ProvidesBuildLevel w K space p level) :
    MeetsContract w p f (D.contract w K space) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨h, rfl, hsk, hn, hh, h1, hz, hd, hg, hdisj, hread, hready⟩ := hpre
  have hCall (i : ℕ) (_ : i < D.count) :
      MeetsContract w p call (D.level w K space i) :=
    buildTopParentCall_meetsContract hc hl
  obtain ⟨v, t, c, hrun, hLo, hHi, hZero, hFrame, hReply, hCost⟩ :=
    buildTopDepthInput_runs (D := D) (pos := pos) ω hCall hsk hn hh h1 hz hd hg hdisj hread
      (fun i hi st hinv => by
        obtain ⟨hwords, hinit, hgFrame, hxFrame, hspace⟩ := hready i hi
        exact buildTopDepth_ready hi hd hinv hwords hinit hgFrame hxFrame hspace)
  exact ⟨.returned v, t, c, hrun, ⟨h, rfl, hLo, hHi, hZero, hFrame, hReply⟩, hCost⟩

end MinCostFlow.HierPaths

end
