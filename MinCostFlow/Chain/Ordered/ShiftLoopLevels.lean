module

public import MinCostFlow.Chain.Ordered.PreLoopChainInv
import MinCostFlow.Chain.LevelConnected
import MinCostFlow.Chain.Ordered.ShiftPreserves
import MinCostFlow.Chain.Ordered.UpdateProofs
import MinCostFlow.Chain.Ordered.RenameFacts

/-!
# The level graphs of the shift loop have at most one more vertex than edges

The init of the sparse-core program charges its work on the vertices of a level graph `G` to the
edges of `G`. So its contract asks `G.n ≤ G.m + 1` of every graph it builds a level from. The
shift loop of `Update` (Algorithm 2, page 29) rebuilds levels from graphs of the chain, so the
solver must know this bound for every chain the loop visits.

The bound comes from connectivity. The input graph of the solver is connected. The graph of
level `i + 1` is a sparsified core graph of the graph of level `i`, so it is connected when the
graph of level `i` is (`isSparsifiedCoreGraph_connected`). A connected graph has
`n ≤ m + 1` (`connected_n_le_m_add_one`).

This file states the facts that the shift loop keeps and proves:
* `ChainInv.levels_connected`: under `ChainInv`, a connected level `0` makes every level
  connected, with `n ≤ m + 1`;
* `ShiftLoopChainInv`: `ChainInv`, a budget invariant, the length range and a connected level `0`;
  `ShiftLoopChainInv.levels_n_le` gives `n ≤ m + 1` at every level, and `ShiftLoopChainInv.shift`
  says that one shift keeps it;
* `alg2_preLoop_shiftLoopChainInv_with`: the chain that the shift loop of stage `t + 1` starts
  from meets it, when the graph of stage `t + 1` is connected. Its proof repeats the steps of
  `alg2_preLoop_chainInv_with` and keeps the budget and the lengths too.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- Under `ChainInv`, if the graph of level `0` is connected, then every level graph `st.G i`
(`i ≤ P.d`) is connected and has `(st.G i).n ≤ (st.G i).m + 1`. The graph of level `i + 1` is a
sparsified core graph of the graph of level `i` (`ChainInv.hGSucc` and the level bounds), so it
is connected by `isSparsifiedCoreGraph_connected`. -/
theorem ChainInv.levels_connected {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    ∀ i ≤ P.d,
      (∀ u ∈ (st.G i).V, ∀ v ∈ (st.G i).V, (st.G i).Connected u v) ∧
      (st.G i).n ≤ (st.G i).m + 1 := by
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  intro i hi
  induction i with
  | zero =>
    exact ⟨hConn0, connected_n_le_m_add_one (hLvl 0 (Nat.zero_le _)).1 hConn0⟩
  | succ i ih =>
    have hi_lt : i < P.d := hi
    obtain ⟨hConni, _⟩ := ih (Nat.le_of_lt hi_lt)
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    have hConnsucc : ∀ u ∈ (st.G (i + 1)).V, ∀ v ∈ (st.G (i + 1)).V,
        (st.G (i + 1)).Connected u v := by
      rw [hInv.hGSucc i hi_lt]
      exact isSparsifiedCoreGraph_connected hBi.1 hBi.2 hConni
    exact ⟨hConnsucc, connected_n_le_m_add_one (hLvl (i + 1) hi).1 hConnsucc⟩

/-- Under `ChainInv`, edge counts are non-increasing along the chain: every level graph `st.G i`
(`i ≤ P.d`) has `(st.G i).m ≤ (st.G 0).m`. -/
theorem ChainInv.levels_m_le {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    ∀ i ≤ P.d, (st.G i).m ≤ (st.G 0).m := by
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    have hi_lt : i < P.d := hi
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    have hsub : (st.G (i + 1)).E ⊆ (st.G i).E := by
      rw [hInv.hGSucc i hi_lt]
      exact hBi.2.1.2.1.trans Finset.sdiff_subset
    exact (Finset.card_le_card hsub).trans (ih (Nat.le_of_lt hi_lt))

/-- The facts about the chain that the shift loop of `Update` keeps: `ChainInv`, the budget
invariant `ChainBudgetInvWith` for some overflow, the lengths of level `0` in the range
`max 0 Ψ`, and a connected graph at level `0`. These are the hypotheses of
`shift_preserves_with_noHidden` and of `ChainInv.levels_connected`. -/
def ShiftLoopChainInv (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) : Prop :=
  ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch ∧
  (∃ overflow : ℝ, ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow) ∧
  LenInRange (max 0 cfg.Ψ) (ch.G 0) ch.ℓ ∧
  ∀ u ∈ (ch.G 0).V, ∀ v ∈ (ch.G 0).V, (ch.G 0).Connected u v

namespace ShiftLoopChainInv

variable {cfg : Alg2Config} {ch : ChainState cfg.T cfg.P}

/-- Every level graph of a chain that meets `ShiftLoopChainInv` has at most one more vertex
than edges (`ChainInv.levels_connected`). -/
theorem levels_n_le (hV : cfg.ValidOrdNoHidden) (h : ShiftLoopChainInv cfg ch) :
    ∀ i ≤ cfg.P.d, (ch.G i).n ≤ (ch.G i).m + 1 := fun i hi =>
  (ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk h.1 h.2.2.2 i hi).2

/-- Every level graph of a chain that meets `ShiftLoopChainInv` has at most `(ch.G 0).m` edges. -/
theorem levels_m_le (hV : cfg.ValidOrdNoHidden) (h : ShiftLoopChainInv cfg ch) :
    ∀ i ≤ cfg.P.d, (ch.G i).m ≤ (ch.G 0).m :=
  ChainInv.levels_m_le hV.hTP hV.hγM₀ hV.hγk h.1

/-- The level sizes `lvlM` of the chain are those of the configuration (`ChainInv.hLvlM`). -/
theorem lvlM_eq (h : ShiftLoopChainInv cfg ch) : ch.lvlM = levelM cfg.TP cfg.P :=
  h.1.hLvlM

/-- The vertex bound `N₀` of the chain is that of the configuration (`ChainInv.hN0`). -/
theorem N₀_eq (h : ShiftLoopChainInv cfg ch) : ch.N₀ = cfg.N₀ :=
  h.1.hN0

/-- One shift keeps `ShiftLoopChainInv`. `shift_preserves_with_noHidden` keeps `ChainInv` and
the budget invariant with the same overflow, and keeps the graph and the lengths of level `0`. -/
theorem shift (hV : cfg.ValidOrdNoHidden) (h : ShiftLoopChainInv cfg ch) (i₀ : ℕ)
    (hi₀ : i₀ ≤ cfg.P.d) :
    ShiftLoopChainInv cfg (algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1 := by
  obtain ⟨hInv, ⟨overflow, hBud⟩, hℓR, hConn⟩ := h
  have hSh := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk hInv hℓR hBud i₀ hi₀
  dsimp only at hSh
  obtain ⟨hInv', hBud', hG0', hℓ', _⟩ := hSh
  refine ⟨hInv', ⟨overflow, hBud'⟩, ?_, ?_⟩
  · rw [hG0', hℓ']; exact hℓR
  · rw [hG0']; exact hConn

end ShiftLoopChainInv

/-- **`ShiftLoopChainInv` before the shift loop.** Take the hypotheses of
`algorithm2_uncond_preserves_with`, a stage `t + 1 ≤ T` whose graph is connected, and let `st` be
the state reached at stage `t`. Then the chain that Algorithm 1's `Update` returns for the
translated batch of stage `t + 1` (the chain the shift loop of stage `t + 1` starts from) meets
`ShiftLoopChainInv`. The proof is that of `alg2_preLoop_chainInv_with`, and it also keeps the
budget invariant, the length range (`update_lenInRange`) and the connected level `0` (the renamed
name maps form a `FreshInv` from the connected graph of stage `t + 1`). -/
theorem alg2_preLoop_shiftLoopChainInv_with {cfg : Alg2Config} (κ : ℝ)
    (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) (t : ℕ) (ht : t + 1 ≤ T)
    (hConn : ∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    ShiftLoopChainInv cfg
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1 := by
  dsimp only
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
  set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
  have ht_le : t ≤ T := Nat.le_of_succ_le ht
  have hI := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdge hLen hmBound
    hnBound).1 t ht_le
  rcases hI with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtLG, hChℓ, _, _, _, _, _, _, _⟩
  have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht
  have hG1Valid := (hHist.2.1 (t + 1) ht).1
  have hℓ1Pos := (hHist.2.1 (t + 1) ht).2
  have hBatch_ext : st.extG.BatchIsValid (D.U (t + 1)) := by rw [hExtG]; exact hD.1
  have hTB := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
  dsimp only at hTB
  change _ ∧ _ at hTB
  rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hEdge_int : ∀ u' ∈ tb.2.2.2.2, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      (hEdge (t + 1) (Nat.succ_pos t) ht)
  have hExtEq : tb.1 = D.G (t + 1) := by
    rw [hExtG', hExtG]; exact hD.2.symm
  have hG0'Valid : ((st.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    (hFresh'.isValid_iff).mpr (hExtEq ▸ hG1Valid)
  have hG0'm : ((st.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
    rw [hFresh'.m_eq, hExtEq]; exact hmBound (t + 1) ht
  have hG0'n : ((st.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
    rw [hFresh'.n_eq, hExtEq]; exact hnBound (t + 1) ht
  have hℓ_intR : LenInRange (max 0 cfg.Ψ) ((st.chain.G 0).applyBatch tb.2.2.2.2)
      (fun e' => D.ℓ (t + 1) (tb.2.2.1 e')) :=
    fun e' he' => hLen.lenInRange ht hℓ1Pos _ (hExtEq ▸ (hFresh'.hRight e' he').2)
  have hℓ_intStable : ∀ e' ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (st.chain.G 0).E →
      (∀ u' ∈ tb.2.2.2.2, ¬ u'.Inserts e') →
        (fun e' => D.ℓ (t + 1) (tb.2.2.1 e')) e' = st.chain.ℓ e' := by
    intro e' he' he'0 _
    have he'_lt : e' < st.nextFresh := hFresh.hLtFresh e' he'0
    have hi2e_eq : tb.2.2.1 e' = st.intToExt e' := hi2e_old e' he'_lt
    obtain ⟨_, he_pre⟩ := hFresh.hRight e' he'0
    obtain ⟨_, he_ext'⟩ := hFresh'.hRight e' he'
    have he_ext1 : st.intToExt e' ∈ (D.G (t + 1)).E := by
      rw [← hExtEq, ← hi2e_eq]; exact he_ext'
    have hNoIns_ext : D.NotInsertedBetween (st.intToExt e') t (t + 1) := by
      intro s hs1 hs2 u hu hIns
      have hseq : s = t + 1 := by omega
      subst hseq
      have hge := hYesInsExt (st.intToExt e') (hExtEq ▸ he_ext1) ⟨u, hu, hIns⟩
      have he2i'_eq : tb.2.1 (st.intToExt e') = e' := by
        rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
      exact absurd (lt_of_lt_of_le he'_lt (le_trans hge (le_of_eq he2i'_eq))) (lt_irrefl _)
    have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht _ he_ext1 hNoIns_ext).2
    dsimp only
    rw [hi2e_eq, hℓ_same, hChℓ]
    dsimp only [Nat.add_sub_cancel]
    exact (hExtLG _ (hExtG ▸ he_pre)).1.symm
  have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud tb.2.2.2.2
    (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
    hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hℓ_intR hℓ_intStable
  dsimp only at hU
  have hRen := update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain
    (D.g (t + 1)) (D.ℓ (t + 1)) hFresh'
  dsimp only at hRen
  refine ⟨hU.1, ⟨_, hU.2.1⟩,
    update_lenInRange cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2 _ _ hℓ_intR,
    hRen.1.connected ?_⟩
  rw [hExtEq]; exact hConn

end MinCostFlow.Chain.Ordered
