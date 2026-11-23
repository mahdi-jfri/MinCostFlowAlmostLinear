module

public import MinCostFlow.HierPaths.InitProgFlatLevel
public import MinCostFlow.HierPaths.InitModelCount

/-!
# Scratch space for flattening a connector

Each ancestor pass appends its edge list to scratch with a length word.
The final list can then be read with its length. Scratch is proportional
to the number of edges written across the passes, plus one word per pass.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.ExpanderDecomp

/-- Words needed to retain all the intermediate lists for a rootward traversal. -/
def initFlatScratch (S : StaticData) : ℕ → ℕ → ℕ → List ℕ → ℕ
  | 0, _, _, _ => 0
  | j + 1, g, u, es =>
    let next := initLevelWalk S j g u es
    1 + next.length + initFlatScratch S j (parentGroup S.x S.b j g) u next

/-- The retained lists fit in one word per pass plus the model's edge work. -/
theorem initFlatScratch_le (S : StaticData) :
    ∀ t g u es, initFlatScratch S t g u es ≤ t + flatSteps S.H S.x S.b t g u es
  | 0, _, _, _ => by simp [initFlatScratch, flatSteps]
  | j + 1, g, u, es => by
    have h := initFlatScratch_le S j (parentGroup S.x S.b j g) u (initLevelWalk S j g u es)
    rw [initFlatScratch, flatSteps]
    change _ ≤ _ + (substSteps (S.H.emb j g) es +
      flatSteps S.H S.x S.b j (parentGroup S.x S.b j g) u (initLevelWalk S j g u es))
    have hlen : (initLevelWalk S j g u es).length ≤ substSteps (S.H.emb j g) es := by
      rw [initLevelWalk, length_substWalk, substSteps]
      omega
    omega

/-- Bound the loop and call overhead independently of the length of the lists. -/
def initFlatChainCost (S : StaticData) (t g u : ℕ) (es : List ℕ) : ℕ :=
  320 * (t + 1) + 200 * flatSteps S.H S.x S.b t g u es

theorem initFlatChainCost_step (S : StaticData) (j g u : ℕ) (es : List ℕ) :
    let next := initLevelWalk S j g u es
    30 * next.length + 199 * es.length + 240 +
        initFlatChainCost S j (parentGroup S.x S.b j g) u next ≤
      initFlatChainCost S (j + 1) g u es := by
  intro next
  have hn : next.length = (es.map fun e => (S.H.emb j g e).length).sum := by
    dsimp [next, initLevelWalk]
    exact length_substWalk _ _ _ _
  rw [initFlatChainCost, initFlatChainCost, flatSteps]
  change _ ≤ 320 * (j + 1 + 1) + 200 * (substSteps (S.H.emb j g) es +
      flatSteps S.H S.x S.b j (parentGroup S.x S.b j g) u next)
  rw [substSteps, ← hn]
  omega

/-- A connector whose terminals differ has at least one edge at every level.
Its model work pays for the per-level call overhead. -/
theorem depth_le_flatSteps (S : StaticData) (hH : S.H.IsValid S.x S.b) :
    ∀ {t g u v es}, 1 < groupSize S.x S.b t → g < numGroups S.x S.b t → u ≠ v →
      IsEdgeWalk (S.H.host t g).edges u v es → t ≤ flatSteps S.H S.x S.b t g u es
  | 0, _, _, _, _, _, _, _, _ => Nat.zero_le _
  | j + 1, g, u, v, es, hsize, hg, huv, hw => by
    let next := initLevelWalk S j g u es
    have hn : IsEdgeWalk (S.H.host j (parentGroup S.x S.b j g)).edges u v next :=
      substWalk_isEdgeWalk hw fun e he => hH.emb_walk hsize hg (hw.lt_length e he)
    have hrec := depth_le_flatSteps S hH (hsize.trans_le (groupSize_succ_le j))
      (parentGroup_lt_numGroups hg) huv hn
    have hpos : 0 < es.length := by
      cases es with
      | nil => cases hw; exact (huv rfl).elim
      | cons => simp
    unfold flatSteps
    change _ ≤ substSteps (S.H.emb j g) es + flatSteps S.H S.x S.b j
      (parentGroup S.x S.b j g) u next
    unfold substSteps
    omega

end MinCostFlow.HierPaths

end
