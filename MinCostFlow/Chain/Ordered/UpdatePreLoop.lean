module

public import MinCostFlow.Chain.Ordered.UpdatePreLoopNone
public import MinCostFlow.Chain.Ordered.UpdatePreLoopSome

/-!
# Pre-loop hidden-strategy bridge across ordered `algorithm1_update`

Proves `alg2HiddenTrace_update_preLoopAt` and `alg2HiddenTrace_update_preLoop`, advancing
`Alg2HiddenTraceAt` from `t` across `translateBatch` + ordered `algorithm1_update` under
`HistoryEdgeOnly D T` and appending the round-completing step `m₁` plus adversary step `m₂`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- Combined pre-loop trace bridge across ordered `algorithm1_update` inside `algorithm2_update`,
parameterized by last-level vertex cap `nLast`. -/
lemma alg2HiddenTrace_update_preLoopAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (_hisUpd : isUpdate (t + 1) = true)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch' e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' →
      FreshInv (D.G (t + 1)) (ch'.G 0) e2i i2e nf → (ch'.G cfg.P.d).n ≤ nLast)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e')) :
    let (extG', e2i', i2e', nf', U_int) :=
      translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
      (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1
    let (branD1, passes1) :=
      match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    let G₀' := (st.chain.G 0).applyBatch U_int
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext (t + 1)
      { st with
        chain := ch1, branD := branD1, passes := passes1,
        extG := extG', extToInt := level0E2I ren G₀' e2i', intToExt := level0I2E ren G₀' i2e',
        nextFresh := level0NF ren G₀' nf',
        extℓ := D.ℓ (t + 1), extg := D.g (t + 1) }) := by
  have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht1
  have hG1Valid := (hHist.2.1 (t + 1) ht1).1
  have hℓ1Pos := (hHist.2.1 (t + 1) ht1).2
  have hBatch_ext : st.extG.BatchIsValid (D.U (t + 1)) := by rw [hExtG]; exact hD.1
  let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
  let extG' := tb.1
  let e2i' := tb.2.1
  let i2e' := tb.2.2.1
  let nf' := tb.2.2.2.1
  let U_int := tb.2.2.2.2
  have hTB_eq : translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1)) =
      (extG', e2i', i2e', nf', U_int) := rfl
  have hEdge_int : ∀ u' ∈ U_int, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      (hEdge (t + 1) (Nat.succ_pos t) ht1)
  have hTB_all := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
  dsimp only at hTB_all
  change extG' = st.extG.applyBatch (D.U (t + 1)) ∧
    FreshInv extG' ((st.chain.G 0).applyBatch U_int) e2i' i2e' nf' ∧
    (st.chain.G 0).BatchIsValid U_int ∧ NoBatchReinsert (st.chain.G 0) U_int ∧
    U_int.length = (D.U (t + 1)).length ∧ st.nextFresh ≤ nf' ∧
    (∀ u' ∈ U_int, ∀ e', u'.Inserts e' → st.nextFresh ≤ e' ∧ e' < nf') ∧
    (∀ e' < st.nextFresh, i2e' e' = st.intToExt e') ∧
    (∀ e ∈ extG'.E, (∀ u ∈ D.U (t + 1), ¬ u.Inserts e) →
      e ∈ st.extG.E ∧ e2i' e = st.extToInt e ∧ ∀ u' ∈ U_int, ¬ u'.Inserts (st.extToInt e)) ∧
    (∀ e ∈ extG'.E, (∃ u ∈ D.U (t + 1), u.Inserts e) → st.nextFresh ≤ e2i' e) at hTB_all
  rcases hTB_all with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hExtG'_D : extG' = (D.G t).applyBatch (D.U (t + 1)) := by rw [hExtG', hExtG]
  have hG1eq : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)) := hD.2
  have hExtEq : extG' = D.G (t + 1) := by rw [hExtG'_D, hG1eq]
  have hG0'Valid : ((st.chain.G 0).applyBatch U_int).IsValid :=
    (hFresh'.isValid_iff).mpr (hExtEq ▸ hG1Valid)
  have hG0'm : ((st.chain.G 0).applyBatch U_int).m ≤ cfg.P.M₀ := by
    rw [hFresh'.m_eq, hExtEq]; exact hm1
  have hG0'n : ((st.chain.G 0).applyBatch U_int).n ≤ cfg.N₀ := by
    rw [hFresh'.n_eq, hExtEq]; exact hn1
  let g_int : ℕ → ℝ := fun e' => D.g (t + 1) (i2e' e')
  let ℓ_int : ℕ → ℝ := fun e' => D.ℓ (t + 1) (i2e' e')
  have hℓ_intPos : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, 0 < ℓ_int e' :=
    fun e' he' => hℓ1Pos _ (hExtEq ▸ (hFresh'.hRight e' he').2)
  have hℓ_intR : LenInRange (max 0 cfg.Ψ) ((st.chain.G 0).applyBatch U_int) ℓ_int :=
    fun e' he' => lenInRange_of_hiddenStableAt hHS1 _ (hExtEq ▸ (hFresh'.hRight e' he').2)
  have hℓ_intStable : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, e' ∈ (st.chain.G 0).E →
      (∀ u' ∈ U_int, ¬ u'.Inserts e') → ℓ_int e' = st.chain.ℓ e' := by
    intro e' he' he'0 _
    have hi2e_eq : i2e' e' = st.intToExt e' := hi2e_old e' (hFresh.hLtFresh e' he'0)
    have he_ext1 : st.intToExt e' ∈ (D.G (t + 1)).E := by
      rw [← hExtEq, ← hi2e_eq]; exact (hFresh'.hRight e' he').2
    have hNoIns_ext : D.NotInsertedBetween (st.intToExt e') t (t + 1) := by
      intro s hs1 hs2 u hu hIns
      have hseq : s = t + 1 := by omega
      subst hseq
      have hge := hYesInsExt (st.intToExt e') (hExtEq ▸ he_ext1) ⟨u, hu, hIns⟩
      have he2i'_eq : e2i' (st.intToExt e') = e' := by
        rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
      have := hFresh.hLtFresh e' he'0
      omega
    have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht1 _ he_ext1 hNoIns_ext).2
    dsimp only [ℓ_int]
    rw [hi2e_eq, hℓ_same, hℓ, hExtℓ]; rfl
  have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud U_int g_int ℓ_int
    hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hℓ_intR hℓ_intStable
  dsimp only at hU
  rcases hU with ⟨hInv1, _, _, hShEq, _, _⟩
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  have hRen := update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain
    (D.g (t + 1)) (D.ℓ (t + 1)) hFresh'
  dsimp only at hRen
  have hFresh1 := hRen.1
  let st0 : ChainState cfg.T cfg.P :=
    { st.chain with recUpdates := fun j =>
        if j = 0 then st.chain.recUpdates 0 + U_int.length else st.chain.recUpdates j }
  let HPre0 : ∀ k, k < 0 → LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ { st0 with ℓ := ℓ_int, g := g_int } k :=
    fun _ hk => absurd hk (Nat.not_lt_zero _)
  have hLoop := updateLoop_hidden_trace cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk
    hInv tr.H
    (fun k hk => ⟨(tr.hLvlSucc k hk).1, tr.hLvlCore k hk⟩)
    ℓ_int g_int U_int hEdge_int cfg.P.d 0 st0 ((st.chain.G 0).applyBatch U_int) U_int
    ((st.chain.G 0).batchEnc U_int) (Nat.zero_add cfg.P.d)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl rfl rfl rfl
    (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ => rfl) (fun h => absurd h (Nat.lt_irrefl 0)) rfl
    hBatch_int hG0'Valid
    (by
      have hm0r : (((st.chain.G 0).applyBatch U_int).m : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast hG0'm
      have hγ1 := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
      have hmul : (cfg.P.M₀ : ℝ) ≤ (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
        nlinarith [show (0 : ℝ) ≤ cfg.P.M₀ from Nat.cast_nonneg _]
      have hceil : (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
          (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / cfg.P.k) ^ 0 ≤ (levelM cfg.TP cfg.P 0 : ℝ) := Nat.le_ceil _
      simp only [pow_zero, mul_one] at hceil
      linarith)
    (fun _ => ⟨hG0'm, hG0'n, applyBatch_V_subset _ _, hℓ_intPos⟩)
    (fun h => absurd h (Nat.lt_irrefl 0)) (hℓ_intR.toLevel _ _ _) hℓ_intStable
    HPre0 (fun _ hk => absurd hk (Nat.not_lt_zero _))
    (fun h => absurd h (Nat.lt_irrefl 0))
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  obtain ⟨⟨H1, hCore1, hRebSome, hRebNone⟩⟩ := hLoop
  dsimp only [tb]
  have hLast1 : (ch1.G cfg.P.d).n ≤ nLast := hLastBound hInv1 (hExtEq ▸ hFresh1)
  cases hFRL : firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
  | none =>
    have hFRL' : firstRebuiltLevel cfg.P.d st.chain.rebuildCount
        (updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int cfg.P.d 0 st0
          ((st.chain.G 0).applyBatch U_int) U_int ((st.chain.G 0).batchEnc U_int)).1.rebuildCount =
        none := by dsimp only [ch1, algorithm1_update] at hFRL; exact hFRL
    have hRenF : level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount = false :=
      level0Rebuilt_eq_false (by rw [hFRL]; simp)
    have hFresh0 : FreshInv extG' (ch1.G 0) e2i' i2e' nf' := by
      have h := hFresh1
      rw [hRenF] at h
      exact h
    unfold level0E2I level0I2E level0NF
    rw [hRenF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact U3.alg2HiddenTrace_update_preLoop_none nLast hV hHist ht1 hm1 hn1 hHS1 tr hFresh
      hExtG hTB_eq hExtG'_D hG1eq hi2e_old hYesInsExt hInv1 hLast1 hFresh0 hShEq H1 hCore1 hFRL
      (by simpa [algorithm1_update, ch1, g_int, ℓ_int] using hRebNone hFRL')
  | some iStar =>
    have hFRL' : firstRebuiltLevel cfg.P.d st.chain.rebuildCount
        (updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int cfg.P.d 0 st0
          ((st.chain.G 0).applyBatch U_int) U_int ((st.chain.G 0).batchEnc U_int)).1.rebuildCount =
        some iStar := by dsimp only [ch1, algorithm1_update] at hFRL; exact hFRL
    exact U3.alg2HiddenTrace_update_preLoop_some nLast hV hHist ht1 hm1 hn1 hHS1 tr hFresh hExtG
      hTB_eq hExtG'_D hG1eq hi2e_old hYesInsExt hInv1 hLast1 hFresh1 hRen.2.1 hShEq H1 hCore1 hFRL
      (by simpa [algorithm1_update, ch1, g_int, ℓ_int] using hRebSome iStar hFRL')
      (fun hpos => by
        have hRenF : level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount = false :=
          level0Rebuilt_eq_false (by rw [hFRL]; intro h; cases h; omega)
        unfold level0E2I level0I2E level0NF
        rw [hRenF]
        exact ⟨rfl, rfl, rfl⟩)

/-- Combined pre-loop trace bridge across ordered `algorithm1_update` inside `algorithm2_update`. -/
lemma alg2HiddenTrace_update_preLoop {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = true)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg} (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e')) :
    let (extG', e2i', i2e', nf', U_int) :=
      translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
      (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1
    let (branD1, passes1) :=
      match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    let G₀' := (st.chain.G 0).applyBatch U_int
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext (t + 1)
      { st with
        chain := ch1, branD := branD1, passes := passes1,
        extG := extG', extToInt := level0E2I ren G₀' e2i', intToExt := level0I2E ren G₀' i2e',
        nextFresh := level0NF ren G₀' nf',
        extℓ := D.ℓ (t + 1), extg := D.g (t + 1) }) :=
  alg2HiddenTrace_update_preLoopAt cfg.N₀ hV hHist hEdge ht1 hisUpd hm1 hn1
    (fun hIc hFc => chainInv_last_le_N0 hV hn1 hIc hFc)
    hHS1 tr hInv hBud hFresh hExtG hExtℓ hℓ

end MinCostFlow.Chain.Ordered
