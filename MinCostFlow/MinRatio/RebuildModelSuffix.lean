module

public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.Chain.SparseCoreRestart
import MinCostFlow.MinRatio.RebuildGuard
import MinCostFlow.MinRatio.TreeEditFold

/-!
# Model equations for a rebuilt suffix

The recurrence of Algorithm 1 (page 20) identifies the input and
output of the initializer at every level of a periodic rebuild.
-/

public section
namespace MinCostFlow.MinRatio
open Chain

/-- The state and next graph at any rebuilt level are the output of
initializing its core on the graph, lengths and gradients of that level
(Algorithm 1, page 20). -/
theorem rebuildSuffix_coreAt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (len grad : ℕ → ℝ) (C : TreeChain) (j : ℕ)
    (hj : j < P.d) :
    ∀ (rem first : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd enc dec fwd : ℕ → ℕ),
      first ≤ j → j < first + rem →
      let result := rebuildSuffix T L P lvlM N₀ len grad rem first G sc bran upd enc dec fwd
      (∀ a ≤ j, C.G a = result.1 a) →
      (∀ a < j, C.activeLSF a = T.lsfs (result.2.1 a) (result.2.2.1 a)) →
      result.2.1 j = T.init P.k (lvlM j) N₀ (C.G j) (C.chainLen len j) (C.chainGrad grad j) ∧
      result.1 (j + 1) = T.S (result.2.1 j) 0 := by
  intro rem
  induction rem with
  | zero =>
    intro first G sc bran upd enc dec fwd hfirst hrem
    omega
  | succ rem ih =>
    intro first G sc bran upd enc dec fwd hfirst hrem
    by_cases he : j = first
    · subst first
      dsimp only [rebuildSuffix]
      intro hG hF
      let partialChain : TreeChain :=
        { d := P.d, k := P.k, G := G, lsfs := fun a => T.lsfs (sc a), bran := bran,
          S := fun a => T.S (sc a), emb := fun a => T.emb (sc a),
          lastK := 1, lastLSFs := fun _ => ⟨G j, ⟨G j, ∅⟩, fun _ => 1⟩, lastBran := 0 }
      have hg (a : ℕ) (ha : a ≤ j) : C.G a = partialChain.G a := by
        specialize hG a ha
        rw [treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ha.trans (Nat.le_succ _))] at hG
        simpa [partialChain, show a ≠ j + 1 by omega] using hG
      have hf (a : ℕ) (ha : a < j) : C.activeLSF a = partialChain.activeLSF a := by
        specialize hF a ha
        rw [rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ha.trans (Nat.lt_succ_self _)),
          rebuildSuffix_branch] at hF
        simpa [partialChain, TreeChain.activeLSF, ha.trans hj, Nat.ne_of_lt ha,
          show ¬ j + 1 ≤ a by omega] using hF
      have hs := chainLen_congr_lt len j (fun a ha => hg a ha.le) hf
      have ht := chainGrad_congr_lt grad j (fun a ha => hg a ha.le) hf
      have hstate := rebuildSuffix_state_prefix T L P lvlM N₀ len grad rem (j + 1)
      constructor
      · rw [hstate _ _ _ _ _ _ _ j (Nat.lt_succ_self _), hg j le_rfl, hs, ht]
        simp [partialChain]
      · rw [treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (le_refl (j + 1)),
          hstate _ _ _ _ _ _ _ j (Nat.lt_succ_self _)]
        simp
    · dsimp only [rebuildSuffix]
      exact ih (first + 1) _ _ _ _ _ _ _ (by omega) (by omega)

/-- Algorithm 1 Init (page 20) initializes each sparse core from that
level's graph and inherited values, then uses branch zero for the next graph. -/
theorem algorithm1_initialize_coreAt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ) (j : ℕ) (hj : j < P.d) :
    let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
    next.scState j = T.init P.k (lvlM j) N₀ (next.G j)
      (next.toTreeChain.chainLen len j) (next.toTreeChain.chainGrad grad j) ∧
    next.G (j + 1) = T.S (next.scState j) 0 ∧ next.bran j = 0 := by
  dsimp only
  let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
  have he := rebuildSuffix_coreAt T L P lvlM N₀ len grad next.toTreeChain j hj P.d 0
    (fun _ => G) (fun _ => T.init P.k (lvlM 0) N₀ G len grad) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (Nat.zero_le j) (by simpa using hj)
    (by
      intro a _
      simp only [next, ChainState.toTreeChain, algorithm1_initialize])
    (by
      intro a ha
      simp only [next, ChainState.toTreeChain, TreeChain.activeLSF, algorithm1_initialize,
        ha.trans hj, ite_true])
  refine ⟨he.1, he.2, ?_⟩
  simp only [algorithm1_initialize]
  rw [rebuildSuffix_branch]
  simp

/-- When the inherited vectors vanish off the current edge set, the
core installed by Algorithm 1 Init agrees with the finite input tables. -/
theorem algorithm1_initialize_coreAt_supported
    (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ) (j : ℕ) (hj : j < P.d) :
    let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
    let ℓ := next.toTreeChain.chainLen len j
    let g := next.toTreeChain.chainGrad grad j
    (∀ e ∉ (next.G j).E, ℓ e = 0) →
    (∀ e ∉ (next.G j).E, g e = 0) →
    next.scState j = T.init P.k (lvlM j) N₀ (next.G j)
      (fun e => if e ∈ (next.G j).E then ℓ e else 0)
      (fun e => if e ∈ (next.G j).E then g e else 0) := by
  dsimp only
  intro hlen hgrad
  rw [(algorithm1_initialize_coreAt T L P lvlM N₀ G len grad j hj).1]
  congr 1 <;> funext e <;> split <;> first | rfl | apply hlen; assumption | apply hgrad; assumption

/-- The concrete sparse-core initializer uses lengths for its forest
and bucket choices. The gradient vector is only needed by the caller. -/
theorem sparseCoreRestartTool_init_gradient_independent
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G : MGraph) (len grad grad' : ℕ → ℝ) :
    (sparseCoreRestartTool oracle C_lsst depth sparsify).init k M N G len grad =
      (sparseCoreRestartTool oracle C_lsst depth sparsify).init k M N G len grad' := by
  rw [sparseCoreRestartTool_toSparseCoreTool]
  rfl

/-- For the concrete core in Algorithm 1 Init, only the inherited
length vector needs to agree with its zero extension. -/
theorem algorithm1_initialize_concrete_coreAt_supported
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ)
    (j : ℕ) (hj : j < P.d) :
    let T := sparseCoreRestartTool oracle C_lsst depth sparsify
    let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
    let ℓ := next.toTreeChain.chainLen len j
    let g := next.toTreeChain.chainGrad grad j
    (∀ e ∉ (next.G j).E, ℓ e = 0) →
    next.scState j = T.init P.k (lvlM j) N₀ (next.G j)
      (fun e => if e ∈ (next.G j).E then ℓ e else 0)
      (fun e => if e ∈ (next.G j).E then g e else 0) := by
  dsimp only
  intro hlen
  rw [(algorithm1_initialize_coreAt _ L P lvlM N₀ G len grad j hj).1]
  let next := (algorithm1_initialize (sparseCoreRestartTool oracle C_lsst depth sparsify)
    L P lvlM N₀ G len grad).1
  let paddedGrad := fun e => if e ∈ (next.G j).E then next.toTreeChain.chainGrad grad j e else 0
  refine (sparseCoreRestartTool_init_gradient_independent oracle C_lsst depth sparsify
    P.k (lvlM j) N₀ _ _ _ paddedGrad).trans ?_
  congr 1
  funext e
  split
  · rfl
  · exact hlen e ‹_›

/-- Periodic Rebuild satisfies the initializer and next-graph
equations at every rebuilt core (Algorithm 1, page 20). -/
theorem algorithm1_rebuild_coreAt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (first j : ℕ)
    (hfirst : first ≤ j) (hj : j < P.d) (Gnew : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P st first Gnew enc).1
    next.scState j = T.init P.k (st.lvlM j) st.N₀ (next.G j)
      (next.toTreeChain.chainLen st.ℓ j) (next.toTreeChain.chainGrad st.g j) ∧
    next.G (j + 1) = T.S (next.scState j) 0 := by
  dsimp only
  have hf := hfirst.trans_lt hj
  let next := (algorithm1_rebuild T L P st first Gnew enc).1
  change next.scState j = _ ∧ next.G (j + 1) = _
  have hrem : j < first + (P.d - first) := by omega
  have he := rebuildSuffix_coreAt T L P st.lvlM st.N₀ st.ℓ st.g next.toTreeChain j hj
    (P.d - first) first (fun a => if a = first then Gnew else st.G a)
    st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd hfirst hrem
    (by
      intro a ha
      simp only [next, ChainState.toTreeChain, algorithm1_rebuild, hf, dite_true])
    (by
      intro a ha
      simp only [next, ChainState.toTreeChain, TreeChain.activeLSF, algorithm1_rebuild,
        hf, dite_true, ha.trans hj, ite_true])
  simpa only [next, algorithm1_rebuild, hf, dite_true, ChainState.toTreeChain] using he

/-- A rebuilt nonterminal level starts on branch zero
(Algorithm 1, page 20). -/
theorem algorithm1_rebuild_branch_zero (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (first j : ℕ)
    (hfirst : first ≤ j) (hj : j < P.d) (Gnew : MGraph) (enc : ℕ) :
    (algorithm1_rebuild T L P st first Gnew enc).1.bran j = 0 := by
  have hf := hfirst.trans_lt hj
  simp only [algorithm1_rebuild, hf, dite_true]
  rw [rebuildSuffix_branch, Nat.add_sub_of_le hf.le]
  simp [hfirst, hj]

/-- Each level in an Algorithm 1 Rebuild suffix (page 20) uses
branch zero to pass lengths and gradients to the following level. -/
theorem rebuildSuffix_nextLevelNumbers (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (first j : ℕ)
    (hfirst : first ≤ j) (hj : j < P.d) (Gnew : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P st first Gnew enc).1
    let forest := T.lsfs (next.scState j) 0
    next.toTreeChain.chainLen st.ℓ (j + 1) =
      coreLen forest (next.toTreeChain.chainLen st.ℓ j) ∧
    next.toTreeChain.chainGrad st.g (j + 1) =
      coreGrad (next.G j) forest (next.toTreeChain.chainGrad st.g j) := by
  dsimp only
  let next := (algorithm1_rebuild T L P st first Gnew enc).1
  have hb : next.bran j = 0 := algorithm1_rebuild_branch_zero T L P st first j hfirst hj Gnew enc
  have ha : next.toTreeChain.activeLSF j = T.lsfs (next.scState j) 0 := by
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, hj, ite_true, hb]
  constructor
  · rw [TreeChain.chainLen, ha]
  · rw [TreeChain.chainGrad, ha]
    rfl

/-- Algorithm 1 Init (page 20) propagates lengths and gradients through
the forest of branch zero at each sparse core. -/
theorem algorithm1_initialize_nextLevelNumbers (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ) (j : ℕ) (hj : j < P.d) :
    let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
    let forest := T.lsfs (next.scState j) 0
    next.toTreeChain.chainLen len (j + 1) =
      coreLen forest (next.toTreeChain.chainLen len j) ∧
    next.toTreeChain.chainGrad grad (j + 1) =
      coreGrad (next.G j) forest (next.toTreeChain.chainGrad grad j) := by
  dsimp only
  let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
  have hb : next.bran j = 0 := (algorithm1_initialize_coreAt T L P lvlM N₀ G len grad j hj).2.2
  have ha : next.toTreeChain.activeLSF j = T.lsfs (next.scState j) 0 := by
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, hj, ite_true, hb]
  constructor
  · rw [TreeChain.chainLen, ha]
  · rw [TreeChain.chainGrad, ha]
    rfl

/-- Rebuild starts from the replacement graph and the numbers inherited
from levels that precede the rebuilt suffix (Algorithm 1, page 20). -/
theorem algorithm1_rebuild_entry (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) (first : Fin P.d) (Gnew : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
    next.G first.val = Gnew ∧
      next.toTreeChain.chainLen chain.ℓ first.val = chain.toTreeChain.chainLen chain.ℓ first.val ∧
      next.toTreeChain.chainGrad chain.g first.val = chain.toTreeChain.chainGrad chain.g first.val := by
  dsimp only
  let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
  have hG (j : ℕ) (hj : j ≤ first.val) : next.G j = if j = first.val then Gnew else chain.G j := by
    simp only [next, algorithm1_rebuild, first.isLt, dite_true]
    exact treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj
  have hp (j : ℕ) (hj : j < first.val) : next.toTreeChain.G j = chain.toTreeChain.G j := by
    simpa only [ChainState.toTreeChain, ite_eq_right (Nat.ne_of_lt hj)] using hG j hj.le
  have hf (j : ℕ) (hj : j < first.val) : next.toTreeChain.activeLSF j = chain.toTreeChain.activeLSF j := by
    have hc : next.scState j = chain.scState j := by
      simp only [next, algorithm1_rebuild, first.isLt, dite_true]
      exact rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj
    have hb : next.bran j = chain.bran j := by
      simp only [next, algorithm1_rebuild, first.isLt, dite_true]
      rw [rebuildSuffix_branch]
      simp [not_le_of_gt hj]
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, hj.trans first.isLt, ite_true, hc, hb]
  exact ⟨by simpa using hG first.val le_rfl, chainLen_congr_lt chain.ℓ _ hp hf,
    chainGrad_congr_lt chain.g _ hp hf⟩

/-- The terminal collection is built using the graph and lengths at
the end of the rebuilt suffix (Algorithm 1, page 20). -/
theorem rebuildSuffix_terminal (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (len grad : ℕ → ℝ) (C : TreeChain) :
    ∀ (rem first : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd enc dec fwd : ℕ → ℕ),
      first + rem = P.d →
      let result := rebuildSuffix T L P lvlM N₀ len grad rem first G sc bran upd enc dec fwd
      C.G = result.1 →
      (∀ a < P.d, C.activeLSF a = T.lsfs (result.2.1 a) (result.2.2.1 a)) →
      result.2.2.2.2.2.2.2.1 = L.build (C.G P.d) (C.chainLen len P.d) := by
  intro rem
  induction rem with
  | zero =>
    intro first G sc bran upd enc dec fwd hlast
    simp only [Nat.add_zero] at hlast
    subst first
    dsimp only [rebuildSuffix]
    intro hG hF
    let partialChain : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun a => T.lsfs (sc a), bran := bran,
        S := fun a => T.S (sc a), emb := fun a => T.emb (sc a),
        lastK := 1, lastLSFs := fun _ => ⟨G P.d, ⟨G P.d, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    have hg (a : ℕ) (_ : a < P.d) : C.G a = partialChain.G a := congrFun hG a
    have hf (a : ℕ) (ha : a < P.d) : C.activeLSF a = partialChain.activeLSF a := by
      simpa only [partialChain, TreeChain.activeLSF, ha, ite_true] using hF a ha
    have hl := chainLen_congr_lt len P.d hg hf
    rw [hl, congrFun hG P.d]
  | succ rem ih =>
    intro first G sc bran upd enc dec fwd hlast
    dsimp only [rebuildSuffix]
    exact ih (first + 1) _ _ _ _ _ _ _ (by omega)

/-- Algorithm 1 Init (page 20) builds the terminal collection from the
last graph and its inherited lengths, with branch zero active. -/
theorem algorithm1_initialize_terminal (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ) :
    let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
    (next.lastK, next.lastLSFs) =
      L.build (next.G P.d) (next.toTreeChain.chainLen len P.d) ∧ next.lastBran = 0 := by
  dsimp only
  let next := (algorithm1_initialize T L P lvlM N₀ G len grad).1
  have he := rebuildSuffix_terminal T L P lvlM N₀ len grad next.toTreeChain P.d 0
    (fun _ => G) (fun _ => T.init P.k (lvlM 0) N₀ G len grad) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (Nat.zero_add P.d)
    (by simp only [next, ChainState.toTreeChain, algorithm1_initialize])
    (by
      intro a ha
      simp only [next, ChainState.toTreeChain, TreeChain.activeLSF, algorithm1_initialize,
        ha, ite_true])
  exact ⟨by simpa only [next, algorithm1_initialize, ChainState.toTreeChain] using he,
    by simp only [algorithm1_initialize]⟩

/-- The terminal graph and inherited lengths determine the collection
after periodic Rebuild (Algorithm 1, page 20). -/
theorem algorithm1_rebuild_terminal (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (first : ℕ)
    (hfirst : first < P.d) (Gnew : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P st first Gnew enc).1
    (next.lastK, next.lastLSFs) =
      L.build (next.G P.d) (next.toTreeChain.chainLen st.ℓ P.d) ∧ next.lastBran = 0 := by
  dsimp only
  let next := (algorithm1_rebuild T L P st first Gnew enc).1
  have he := rebuildSuffix_terminal T L P st.lvlM st.N₀ st.ℓ st.g next.toTreeChain
    (P.d - first) first (fun a => if a = first then Gnew else st.G a)
    st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
    (Nat.add_sub_of_le hfirst.le)
    (by simp only [next, ChainState.toTreeChain, algorithm1_rebuild, hfirst, dite_true])
    (by
      intro a ha
      simp only [next, ChainState.toTreeChain, TreeChain.activeLSF, algorithm1_rebuild,
        hfirst, dite_true, ha, ite_true])
  constructor
  · simpa only [next, algorithm1_rebuild, hfirst, dite_true, ChainState.toTreeChain] using he
  · simp only [algorithm1_rebuild, hfirst, dite_true]

/-- A name removed at a rebuilt level can keep a nonzero model length.
The recurrence uses the previous length and stretch even at a removed
name (Algorithm 1, page 20 and Definition 5.6, page 18). -/
theorem rebuildSuffix_removedEdge_not_zeroSupported
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (first j : ℕ)
    (hfirst : first ≤ j) (hj : j < P.d) (Gnew : MGraph) (enc e : ℕ) :
    let next := (algorithm1_rebuild T L P st first Gnew enc).1
    e ∉ (next.G (j + 1)).E →
    (T.lsfs (next.scState j) 0).wstr e ≠ 0 →
    next.toTreeChain.chainLen st.ℓ j e ≠ 0 →
    ¬ ∀ a ∉ (next.G (j + 1)).E, next.toTreeChain.chainLen st.ℓ (j + 1) a = 0 := by
  dsimp only
  intro hremoved hstretch hlen hsupp
  have hz := hsupp e hremoved
  rw [(rebuildSuffix_nextLevelNumbers T L P st first j hfirst hj Gnew enc).1, coreLen] at hz
  exact (mul_ne_zero hstretch hlen) hz

end MinCostFlow.MinRatio
