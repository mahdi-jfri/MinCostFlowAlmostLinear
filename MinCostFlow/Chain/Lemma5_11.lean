module

public import MinCostFlow.Chain.FindCycleProofs
public import MinCostFlow.Chain.CollapseBounds
public import MinCostFlow.Chain.Algorithm1UpdateProofs
public import MinCostFlow.Chain.CycleLemmas
import MinCostFlow.Chain.WalkFlow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dynamic Tree Chain theorem (Lemma 5.11, `jtree.tex` pages 20–24)

This file formalizes **Lemma 5.11** (page 20, proof pages 23–24) for Algorithm 1:

* **`FindCycle` quality, heap keys, and representation (`findCycle_spec`)**: `algorithm1_findCycle`
  maximizes the own-level core-graph key `heapCycleRatio` (with `leastArgmax` tie-breaking).
  Using `lemma_A_2_wlen`, `leastArgmax_spec`, and `heapCycleRatio_le_exactCycleRatio` (via
  repaired `lemma_7_12` and `lemma_7_13`), `algorithm1_findCycle` outputs a circulation `Δ`
  with `⟨g, Δ⟩ ≤ 0` and exact ratio in `G_0` at least `(1 / (σ_tot + 1)) * |⟨g, c⟩| / ∑_{i=0}^d ‖w^{G_i}‖₁`,
  represented by at most `1 + ⌊γ_ℓ(M₀²)⌋` off-tree edges of `G_0` stitched by `T^𝒢 = chainTree`
  forest paths.
* **Level graph size bounds (`level_graph_size_bounds`)**: at every level `i ≤ P.d`,
  `|E(G_i)| ≤ M₀ (γ_ℓ / k)^i`, the non-isolated vertex count is at most `2 M₀ (γ_ℓ / k)^i`,
  and when `(D.G 0)` at level `i - 1` is connected (`0 < i`),
  `|V(G_i)| ≤ c_R * (2 M₀ γ_ℓ^i / k^i + 3)`.
* **Collapsing runtime and `T^𝒢` edge-update bounds (`lemma_5_11`)**: executing any sequence of
  valid `Update` and `Shift` actions starting from `Initialize` maintains `ChainInv`,
  `TreeChain.Holds`, `LastLevelSpans`, `EmbedsSurviving`, exact `T^𝒢` `TreeChange` tracking,
  and explicit non-asymptotic bounds matching `M₀^{1/d} (γ_ℓ γ_r)^{O(d)} polylog (M₀ + N₀)`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section MainLemma5_11

/-- Valid external operations on the Algorithm 1 dynamic tree chain (per Lemma 5.11, page 20,
`Rebuild` is only invoked internally through `Update`). -/
inductive ChainAction where
  | update (U : List Update) (g' ℓ' : ℕ → ℝ)
  | shift (i₀ : ℕ)

/-- Sequential execution of `ChainAction`s starting from `st`, returning the final state and the
list of `TreeChange` batches emitted at each step for updating `T^𝒢`. -/
noncomputable def execChainActions (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) :
    ChainState T P → List ChainAction → ChainState T P × List (List TreeChange)
  | st, [] => (st, [])
  | st, act :: rest =>
    let (st1, ch) := match act with
      | .update U g' ℓ' => algorithm1_update T L TP P N₀ st U g' ℓ'
      | .shift i₀ => algorithm1_shift T L P st i₀
    let (st2, chs) := execChainActions T L TP P N₀ st1 rest
    (st2, ch :: chs)

/-- Validity predicate for a sequence of `ChainAction`s relative to the current top-level graph
and lengths `(G₀, ℓ)`. -/
def ChainActionListValid (P : ChainParams) (N₀ : ℕ) :
    MGraph → (ℕ → ℝ) → List ChainAction → Prop
  | _, _, [] => True
  | G₀, ℓ, .update U _ ℓ' :: rest =>
    G₀.BatchIsValid U ∧
    NoBatchReinsert G₀ U ∧
    (G₀.applyBatch U).IsValid ∧
    (G₀.applyBatch U).m ≤ P.M₀ ∧
    (G₀.applyBatch U).n ≤ N₀ ∧
    U.length ≤ P.M₀ ∧
    (∀ e ∈ (G₀.applyBatch U).E, 0 < ℓ' e) ∧
    (∀ e ∈ (G₀.applyBatch U).E, e ∈ G₀.E → (∀ u ∈ U, ¬ u.Inserts e) → ℓ' e = ℓ e) ∧
    ChainActionListValid P N₀ (G₀.applyBatch U) ℓ' rest
  | G₀, ℓ, .shift i₀ :: rest =>
    i₀ ≤ P.d ∧ ChainActionListValid P N₀ G₀ ℓ rest

private lemma rebuildSuffix_G_le (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      ∀ j ≤ idx,
        (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).1 j = G j
  | 0, _, _, _, _, _, _, _, _, j, _ => rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, j, hj => by
    dsimp only [rebuildSuffix]
    refine (rebuildSuffix_G_le T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ j
      (Nat.le_succ_of_le hj)).trans ?_
    have hne : j ≠ idx + 1 := Nat.ne_of_lt (Nat.lt_succ_of_le hj)
    simp [hne]

private lemma rebuildSuffix_upd_cFwd (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      let res := rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      (∀ j < idx, res.2.2.2.1 j = upd j ∧ res.2.2.2.2.2.2.1 j = cFwd j) ∧
      (∀ j, idx ≤ j → j < idx + rem → res.2.2.2.1 j = 0 ∧ res.2.2.2.2.2.2.1 j = 0)
  | 0, _, _, _, _, upd, _, _, cFwd =>
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ h1 h2 => by omega⟩
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd => by
    dsimp only [rebuildSuffix]
    let Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let sc_i := T.init P.k (lvlM idx) N₀ (G idx) (Cpartial.chainLen ℓ₀ idx) (Cpartial.chainGrad g₀ idx)
    have ih := rebuildSuffix_upd_cFwd T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1)
      (fun j => if j = idx + 1 then T.S sc_i 0 else G j)
      (fun j => if j = idx then sc_i else sc j)
      (fun j => if j = idx then 0 else bran j)
      (fun j => if j = idx then 0 else upd j)
      (fun j => if j = idx then 0 else cEnc j)
      (fun j => if j = idx then 0 else cDec j)
      (fun j => if j = idx then 0 else cFwd j)
    refine ⟨fun j hj => ?_, fun j h1 h2 => ?_⟩
    · have ⟨hu, hcf⟩ := ih.1 j (Nat.lt_succ_of_lt hj)
      have hne : j ≠ idx := Nat.ne_of_lt hj
      simpa [hne] using And.intro hu hcf
    · by_cases hji : j = idx
      · subst hji
        have ⟨hu, hcf⟩ := ih.1 j (Nat.lt_succ_self j)
        simpa using And.intro hu hcf
      · exact ih.2 j (by omega) (by omega)

lemma initialize_chainRecBound (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ)
    {factor : ℝ} (_hf : 0 ≤ factor) :
    ChainRecBound P factor (algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1 := by
  have hUC := (rebuildSuffix_upd_cFwd T L P lvlM N₀ ℓ₀ g₀ P.d 0 (fun _ => G₀)
    (fun _ => T.init P.k (lvlM 0) N₀ G₀ ℓ₀ g₀) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0)).2
  intro i hi
  have ⟨hu, hcf⟩ := hUC i (Nat.zero_le i) (by omega)
  have hu' : (algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.updCount i = 0 := hu
  have hcf' : (algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.curFwd i = 0 := hcf
  have hrec0 : ∀ j, (algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.recUpdates j = 0 := fun _ => rfl
  rw [hu', hcf', hrec0, hrec0]
  simp

lemma shift_preserves_chainRecBound (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) {factor : ℝ} (hf : 0 ≤ factor)
    {st : ChainState T P} (hRec : ChainRecBound P factor st)
    {i₀ : ℕ} (_hi₀ : i₀ ≤ P.d) :
    ChainRecBound P factor (algorithm1_shift T L P st i₀).1 := by
  by_cases hlt : i₀ < P.d
  · dsimp only [algorithm1_shift]
    simp only [hlt, ↓reduceDIte]
    let newBran := (st.bran i₀ + 1) % P.k
    let newSc := T.restart (st.scState i₀) newBran
    have hUC := rebuildSuffix_upd_cFwd T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
      (fun j => if j = i₀ + 1 then T.S newSc newBran else st.G j)
      (fun j => if j = i₀ then newSc else st.scState j)
      (fun j => if j = i₀ then newBran else st.bran j)
      st.updCount (fun j => if j = i₀ + 1 then 0 else st.curEnc j)
      (fun j => if j = i₀ then 0 else st.curDecUpdates j) st.curFwd
    refine chainRecBound_of_rebuildSuffix hf (Nat.succ_le_of_lt hlt) hRec rfl
      (fun j hj => hUC.1 j hj) (fun j h1 h2 => hUC.2 j h1 (by omega))
  · dsimp only [algorithm1_shift]
    simp only [hlt, ↓reduceDIte]
    exact hRec

private lemma algorithm1_rebuild_G0_ℓ (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph) (extraEnc : ℕ) :
    (algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.G 0 = (if 0 = i₀ then Gnew else st.G 0) ∧
    (algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.ℓ = st.ℓ ∧
    (algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.g = st.g ∧
    (algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.recUpdates 0 = st.recUpdates 0 := by
  dsimp only [algorithm1_rebuild]
  by_cases hlt : i₀ < P.d
  · simp only [hlt, ↓reduceDIte]
    have h0 := rebuildSuffix_G_le T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
      (fun j => if j = i₀ then Gnew else st.G j) st.scState st.bran st.updCount
      st.curEnc st.curDecUpdates st.curFwd 0 (Nat.zero_le i₀)
    exact ⟨h0, trivial, trivial, trivial⟩
  · rw [dite_eq_right_iff.mpr (fun h => absurd h hlt)]
    have hne : (0 : ℕ) ≠ i₀ := by have := P.hd; omega
    have hnePd : (0 : ℕ) ≠ P.d := Nat.ne_of_lt P.hd
    simp [hne, hnePd]

private lemma updateLoop_G0_ℓ (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.G 0 =
        (if idx = 0 then curG else st.G 0) ∧
      (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.ℓ = ℓ' ∧
      (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.g = g' ∧
      (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.recUpdates 0 =
        st.recUpdates 0
  | 0, idx, st, curG, curU, _, hsum => by
    have hne0 : idx ≠ 0 := by have := P.hd; omega
    have hnePd : (0 : ℕ) ≠ P.d := Nat.ne_of_lt P.hd
    dsimp only [updateLoop]
    by_cases hU : curU = []
    · simp [hU, hne0, hnePd]
    · simp [hU, hne0, hnePd]
  | rem + 1, idx, st, curG, curU, curEncAcc, hsum => by
    dsimp only [updateLoop]
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · simp only [hOver, ↓reduceIte]
      have hReb := algorithm1_rebuild_G0_ℓ T L P { st with ℓ := ℓ', g := g' } idx curG curEncAcc
      refine ⟨?_, hReb.2.1, hReb.2.2.1, hReb.2.2.2⟩
      rw [hReb.1]
      by_cases h0 : idx = 0
      · subst h0; simp
      · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
        simp [h0, hne0]
    · simp only [hOver, ↓reduceIte]
      set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      set updRes := T.update (st.scState idx) curU (Cpartial.chainLen ℓ' idx) (Cpartial.chainGrad g' idx)
      set nextG := T.S updRes.1 (st.bran idx)
      set nextU := updRes.2 (st.bran idx)
      set stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then updRes.1 else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncAcc
            else if j = idx + 1 then st.curEnc (idx + 1) + (st.G (idx + 1)).batchEnc nextU
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then
              st.curDecUpdates idx +
                (diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
                  (T.lsfs updRes.1 (st.bran idx)).F.F.E).length
            else st.curDecUpdates j }
      have hIH := updateLoop_G0_ℓ T L TP P N₀ ℓ' g' rem (idx + 1) stNext nextG nextU 0 (by omega)
      have hne1 : idx + 1 ≠ 0 := Nat.succ_ne_zero idx
      simp only [hne1, ↓reduceIte] at hIH
      refine ⟨?_, hIH.2.1, hIH.2.2.1, ?_⟩
      · rw [hIH.1]
        by_cases h0 : idx = 0
        · subst h0; simp [stNext]
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          simp [stNext, h0, hne0]
      · rw [hIH.2.2.2]
        simp [stNext]

lemma update_G0_ℓ (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (st : ChainState T P) (U : List Update) (g' ℓ' : ℕ → ℝ) :
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.G 0 = (st.G 0).applyBatch U ∧
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.ℓ = ℓ' ∧
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.g = g' ∧
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.recUpdates 0 = st.recUpdates 0 + U.length := by
  dsimp only [algorithm1_update]
  have h := updateLoop_G0_ℓ T L TP P N₀ ℓ' g' P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U) (Nat.zero_add P.d)
  simpa using h

theorem execChainActions_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) :
    ∀ (acts : List ChainAction) (st : ChainState T P),
      ChainInv T L TP LP P N₀ st →
      ChainBudgetInv TP LP N₀ st →
      ChainActionListValid P N₀ (st.G 0) st.ℓ acts →
      let (stEnd, chs) := execChainActions T L TP P N₀ st acts
      ChainInv T L TP LP P N₀ stEnd ∧
      ChainBudgetInv TP LP N₀ stEnd ∧
      chs.foldl applyTreeChanges st.toTreeChain.chainTree.E = stEnd.toTreeChain.chainTree.E ∧
      (chs.map List.length).sum + st.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  intro acts
  induction acts with
  | nil =>
    intro st hInv hBud _
    exact ⟨hInv, hBud, rfl, by simp⟩
  | cons act rest ih =>
    intro st hInv hBud hAct
    cases act with
    | update U g' ℓ' =>
      rcases hAct with ⟨hB, hNR, hGV, hGm, hGn, hULen, hℓ'p, hℓ's, hRest⟩
      have hU := update_preserves_noHidden T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk hInv hBud U g' ℓ'
        hB hNR hGV hGm hGn hULen hℓ'p hℓ's
      rcases hU with ⟨hInv1, hBud1, _, _, _, hTot1⟩
      have hGℓ := update_G0_ℓ T L TP P N₀ st U g' ℓ'
      set res1 := algorithm1_update T L TP P N₀ st U g' ℓ'
      have hTot1' : res1.2.length + st.totalTreeUpdates ≤ res1.1.totalTreeUpdates := hTot1
      have hApp1 : applyTreeChanges st.toTreeChain.chainTree.E res1.2 =
          res1.1.toTreeChain.chainTree.E := by
        change applyTreeChanges st.toTreeChain.chainTree.E
          (diffTreeChanges st.toTreeChain.chainTree.E res1.1.toTreeChain.chainTree.E) = _
        exact applyTreeChanges_diffTreeChanges _ _
      have ih' := ih res1.1 hInv1 hBud1 (by rwa [hGℓ.1, hGℓ.2.1])
      rcases ih' with ⟨hInv2, hBud2, hApp2, hTot2⟩
      dsimp only [execChainActions]
      refine ⟨hInv2, hBud2, ?_, ?_⟩
      · change List.foldl applyTreeChanges st.toTreeChain.chainTree.E
            (res1.2 :: (execChainActions T L TP P N₀ res1.1 rest).2) =
          (execChainActions T L TP P N₀ res1.1 rest).1.toTreeChain.chainTree.E
        rw [List.foldl_cons, hApp1]
        exact hApp2
      · simp only [List.map_cons, List.sum_cons]
        change res1.2.length + ((execChainActions T L TP P N₀ res1.1 rest).2.map List.length).sum +
            st.totalTreeUpdates ≤
          (execChainActions T L TP P N₀ res1.1 rest).1.totalTreeUpdates
        omega
    | shift i₀ =>
      rcases hAct with ⟨hi₀, hRest⟩
      have hS := shift_preserves_noHidden T L TP LP P hTP hLP hT hL hγM₀ hγk hInv hBud i₀ hi₀
      rcases hS with ⟨hInv1, hBud1, hG1, hℓ1, _, _, _, hApp1, hTot1⟩
      set res1 := algorithm1_shift T L P st i₀
      have hG1' : res1.1.G 0 = st.G 0 := hG1
      have hℓ1' : res1.1.ℓ = st.ℓ := hℓ1
      have hApp1' : applyTreeChanges st.toTreeChain.chainTree.E res1.2 =
          res1.1.toTreeChain.chainTree.E := hApp1
      have hTot1' : res1.1.totalTreeUpdates = st.totalTreeUpdates + res1.2.length := hTot1
      have ih' := ih res1.1 hInv1 hBud1 (by rwa [hG1', hℓ1'])
      rcases ih' with ⟨hInv2, hBud2, hApp2, hTot2⟩
      dsimp only [execChainActions]
      refine ⟨hInv2, hBud2, ?_, ?_⟩
      · change List.foldl applyTreeChanges st.toTreeChain.chainTree.E
            (res1.2 :: (execChainActions T L TP P N₀ res1.1 rest).2) =
          (execChainActions T L TP P N₀ res1.1 rest).1.toTreeChain.chainTree.E
        rw [List.foldl_cons, hApp1']
        exact hApp2
      · simp only [List.map_cons, List.sum_cons]
        change res1.2.length + ((execChainActions T L TP P N₀ res1.1 rest).2.map List.length).sum +
            st.totalTreeUpdates ≤
          (execChainActions T L TP P N₀ res1.1 rest).1.totalTreeUpdates
        omega

theorem execChainActions_preserves (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestart)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) :
    ∀ (acts : List ChainAction) (st : ChainState T P),
      ChainInv T L TP LP P N₀ st →
      ChainBudgetInv TP LP N₀ st →
      ChainActionListValid P N₀ (st.G 0) st.ℓ acts →
      let (stEnd, chs) := execChainActions T L TP P N₀ st acts
      ChainInv T L TP LP P N₀ stEnd ∧
      ChainBudgetInv TP LP N₀ stEnd ∧
      chs.foldl applyTreeChanges st.toTreeChain.chainTree.E = stEnd.toTreeChain.chainTree.E ∧
      (chs.map List.length).sum + st.totalTreeUpdates ≤ stEnd.totalTreeUpdates :=
  execChainActions_preserves_noHidden T L TP LP P hTP hLP (SparseCoreRestartTool.IsSpecRestart.toNoHidden hT)
    hL hNoReinsTool.toNoHidden hγM₀ hγk

/-- **Dynamic Tree Chain Theorem (Lemma 5.11, `jtree.tex` pages 20–21, 23–24)**:
Starting from `algorithm1_initialize T L P G₀ ℓ₀ g₀` and executing any valid sequence of external
`Update` and `Shift` operations `acts` (note that `Rebuild` is only triggered internally from
`Update`, line 325):
1. Algorithm 1 maintains `ChainInv` and the shifted `TreeChain.Holds`, `LastLevelSpans`, and
   `EmbedsSurviving` properties at the resulting state `stEnd`.
2. The emitted `TreeChange` batches `(initChanges :: chs)` explicitly track `T^𝒢 = stEnd.toTreeChain.chainTree.E`,
   with total emitted tree changes bounded by `stEnd.totalTreeUpdates`.
3. Every level graph `stEnd.G i` (`i ≤ P.d`) has at most `M₀ (γ_ℓ / k)^i` edges, at most
   `2 M₀ (γ_ℓ / k)^i` non-isolated vertices, and (for `0 < i`, when level `(i - 1)`'s history
   starts connected) at most `c_R (2 M₀ γ_ℓ^i / k^i + 3)` vertices.
4. For any valid pair `(c, w)` for `(stEnd.G 0, stEnd.ℓ)`, `algorithm1_findCycle stEnd` outputs
   a circulation `Δ` with `⟨g, Δ⟩ ≤ 0`, represented by at most `1 + γ_ℓ(M₀²)` off-tree edges and
   `T^𝒢` tree paths, achieving ratio at least `(1 / (σ_tot + 1)) * |⟨g, c⟩| / ∑_{i=0}^d ‖w^{G_i}‖₁`
   (or `Δ = 0` and `⟨g, c⟩ = 0` when `G_0` has no off-tree edges).
5. With `s_i = stEnd.shiftCount i` and `r_i = stEnd.rebuildCount i`, the total runtime and total
   `T^𝒢` edge updates satisfy the explicit collapsing bounds of Lemma 5.11. -/
theorem lemma_5_11_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hMWU : T.ToolMWURestartNoHidden σ_mwu) (hEmb : T.ToolEmbedsSurvivingRestartNoHidden)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ)
    (hG0Valid : G₀.IsValid) (hG0m : G₀.m ≤ P.M₀) (hG0n : G₀.n ≤ N₀) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (acts : List ChainAction) (hActs : ChainActionListValid P N₀ G₀ ℓ₀ acts) :
    let st₀ := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).1
    let initCh := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).2
    let stEnd := (execChainActions T L TP P N₀ st₀ acts).1
    let chs := (execChainActions T L TP P N₀ st₀ acts).2
    let σ_tot := max (TP.σ P.k (stEnd.G 0).n) (LP.σ_last (stEnd.G 0).n)
    let σ_mwu_tot := max (σ_mwu (stEnd.G 0).n) (LP.σ_mwu (stEnd.G 0).n)
    ChainInv T L TP LP P N₀ stEnd ∧
    stEnd.toTreeChain.Holds (stEnd.G 0) stEnd.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    stEnd.toTreeChain.LastLevelSpans ∧
    stEnd.toTreeChain.EmbedsSurviving ∧
    ((initCh :: chs).foldl applyTreeChanges ∅ = stEnd.toTreeChain.chainTree.E ∧
      initCh.length + (chs.map List.length).sum ≤ stEnd.totalTreeUpdates) ∧
    ((∀ i ≤ P.d, ((stEnd.G i).m : ℝ) ≤ (levelM TP P i : ℝ)) ∧
      (∀ i ≤ P.d, ((nonIsolatedV (stEnd.G i)).card : ℝ) ≤ 2 * (levelM TP P i : ℝ)) ∧
      (∀ i, 0 < i → i ≤ P.d →
        ∀ H : LevelHistory T TP P N₀ stEnd (i - 1),
          (∀ u ∈ (H.D.G 0).V, ∀ v ∈ (H.D.G 0).V, (H.D.G 0).Connected u v) →
          ((stEnd.G i).n : ℝ) ≤ TP.c_R * (2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3))) ∧
    (∀ c w : ℕ → ℝ, IsValidPair (stEnd.G 0) stEnd.ℓ c w →
      let C := stEnd.toTreeChain
      let (Δ, walk, optEdge) := algorithm1_findCycle stEnd
      (stEnd.G 0).IsCirculation Δ ∧
      (stEnd.G 0).inner stEnd.g Δ ≤ 0 ∧
      ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + TP.γ_ℓ (P.M₀ ^ 2) ∧
      (optEdge = none → Δ = 0 ∧ walk = [] ∧ (stEnd.G 0).inner stEnd.g c = 0) ∧
      (∀ e, optEdge = some e →
        e ∈ (stEnd.G 0).E \ C.chainTree.E ∧
        0 < (stEnd.G 0).lnorm stEnd.ℓ Δ ∧
        (1 / (σ_tot + 1)) *
            (|(stEnd.G 0).inner stEnd.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
          |(stEnd.G 0).inner stEnd.g Δ| / (stEnd.G 0).lnorm stEnd.ℓ Δ)) ∧
    ((stEnd.totalRuntime : ℝ) ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm P i)) ∧
    ((stEnd.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm P i)) := by
  have hInit := initialize_preserves_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk
    G₀ ℓ₀ g₀ hG0Valid hG0m hG0n hℓ₀
  rcases hInit with ⟨hInv0, hBud0, hG0eq, hℓ0eq, _, _, _, hApp0, hTot0, _⟩
  let st₀ := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).1
  let initCh := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).2
  have hInv0' : ChainInv T L TP LP P N₀ st₀ := hInv0
  have hBud0' : ChainBudgetInv TP LP N₀ st₀ := hBud0
  have hG0eq' : st₀.G 0 = G₀ := hG0eq
  have hℓ0eq' : st₀.ℓ = ℓ₀ := hℓ0eq
  have hApp0' : applyTreeChanges ∅ initCh = st₀.toTreeChain.chainTree.E := hApp0
  have hTot0' : st₀.totalTreeUpdates = initCh.length := hTot0
  have hActs' : ChainActionListValid P N₀ (st₀.G 0) st₀.ℓ acts := by
    rw [hG0eq', hℓ0eq']
    exact hActs
  have hExec := execChainActions_preserves_noHidden T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk
    acts st₀ hInv0' hBud0' hActs'
  rcases hExec with ⟨hInvEnd, hBudEnd, hAppEnd, hTotEnd⟩
  have hTreeEnd := hInvEnd.toTreeChain_holds_noHidden hσ_mwu_mono hTP hLP hT hMWU hEmb hγM₀ hγk
  refine ⟨hInvEnd, hTreeEnd.1, hTreeEnd.2.1, hTreeEnd.2.2, ⟨?_, ?_⟩,
    level_graph_size_bounds_noHidden T L TP LP P hTP hT hγM₀ hγk hInvEnd,
    fun c w hvp => findCycle_spec_noHidden T L TP LP P hσ_mwu_mono hTP hLP hT hMWU hEmb hγM₀ hγk hInvEnd hvp,
    totalRuntime_collapse_noHidden T L TP LP P hTP hLP hT hγM₀ hγk hInvEnd hBudEnd,
    totalTreeUpdates_collapse_noHidden T L TP LP P hTP hLP hT hγM₀ hγk hInvEnd hBudEnd⟩
  · change List.foldl applyTreeChanges (applyTreeChanges ∅ initCh) _ = _
    rw [hApp0']
    exact hAppEnd
  · calc
      initCh.length + ((execChainActions T L TP P N₀ st₀ acts).2.map List.length).sum
          = ((execChainActions T L TP P N₀ st₀ acts).2.map List.length).sum + st₀.totalTreeUpdates := by
        rw [← hTot0', Nat.add_comm]
      _ ≤ (execChainActions T L TP P N₀ st₀ acts).1.totalTreeUpdates := hTotEnd

theorem lemma_5_11 (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hMWU : T.ToolMWURestart σ_mwu) (hEmb : T.ToolEmbedsSurvivingRestart)
    (hNoReinsTool : T.ToolNoReinsertRestart)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ)
    (hG0Valid : G₀.IsValid) (hG0m : G₀.m ≤ P.M₀) (hG0n : G₀.n ≤ N₀) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (acts : List ChainAction) (hActs : ChainActionListValid P N₀ G₀ ℓ₀ acts) :
    let st₀ := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).1
    let initCh := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).2
    let stEnd := (execChainActions T L TP P N₀ st₀ acts).1
    let chs := (execChainActions T L TP P N₀ st₀ acts).2
    let σ_tot := max (TP.σ P.k (stEnd.G 0).n) (LP.σ_last (stEnd.G 0).n)
    let σ_mwu_tot := max (σ_mwu (stEnd.G 0).n) (LP.σ_mwu (stEnd.G 0).n)
    ChainInv T L TP LP P N₀ stEnd ∧
    stEnd.toTreeChain.Holds (stEnd.G 0) stEnd.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    stEnd.toTreeChain.LastLevelSpans ∧
    stEnd.toTreeChain.EmbedsSurviving ∧
    ((initCh :: chs).foldl applyTreeChanges ∅ = stEnd.toTreeChain.chainTree.E ∧
      initCh.length + (chs.map List.length).sum ≤ stEnd.totalTreeUpdates) ∧
    ((∀ i ≤ P.d, ((stEnd.G i).m : ℝ) ≤ (levelM TP P i : ℝ)) ∧
      (∀ i ≤ P.d, ((nonIsolatedV (stEnd.G i)).card : ℝ) ≤ 2 * (levelM TP P i : ℝ)) ∧
      (∀ i, 0 < i → i ≤ P.d →
        ∀ H : LevelHistory T TP P N₀ stEnd (i - 1),
          (∀ u ∈ (H.D.G 0).V, ∀ v ∈ (H.D.G 0).V, (H.D.G 0).Connected u v) →
          ((stEnd.G i).n : ℝ) ≤ TP.c_R * (2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3))) ∧
    (∀ c w : ℕ → ℝ, IsValidPair (stEnd.G 0) stEnd.ℓ c w →
      let C := stEnd.toTreeChain
      let (Δ, walk, optEdge) := algorithm1_findCycle stEnd
      (stEnd.G 0).IsCirculation Δ ∧
      (stEnd.G 0).inner stEnd.g Δ ≤ 0 ∧
      ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + TP.γ_ℓ (P.M₀ ^ 2) ∧
      (optEdge = none → Δ = 0 ∧ walk = [] ∧ (stEnd.G 0).inner stEnd.g c = 0) ∧
      (∀ e, optEdge = some e →
        e ∈ (stEnd.G 0).E \ C.chainTree.E ∧
        0 < (stEnd.G 0).lnorm stEnd.ℓ Δ ∧
        (1 / (σ_tot + 1)) *
            (|(stEnd.G 0).inner stEnd.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
          |(stEnd.G 0).inner stEnd.g Δ| / (stEnd.G 0).lnorm stEnd.ℓ Δ)) ∧
    ((stEnd.totalRuntime : ℝ) ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm P i)) ∧
    ((stEnd.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm P i)) :=
  lemma_5_11_noHidden T L TP LP P N₀ hσ_mwu_mono hTP hLP (SparseCoreRestartTool.IsSpecRestart.toNoHidden hT)
    hL hMWU.toNoHidden hEmb.toNoHidden hNoReinsTool.toNoHidden hγM₀ hγk G₀ ℓ₀ g₀ hG0Valid hG0m hG0n hℓ₀
    acts hActs

end MainLemma5_11

end MinCostFlow.Chain