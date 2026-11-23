module

public import MinCostFlow.Chain.Algorithm2PsiGame
public import MinCostFlow.Chain.Section6Quality
public import MinCostFlow.Chain.Algorithm2Uncond
public import MinCostFlow.Game.StrategyAnalysis

/-!
# Hidden-stable witness trace invariant for Algorithm 2 (Section 6.2)

This file develops the witness-propagation and Game-synchronization infrastructure needed by
**Lemma 6.5** (`MinCostFlow.Chain.Lemma6_5`):

* `Alg2Config.Valid`: full specification wrapper (adding `IsSpec` item 2, `ToolMWU`,
  `ToolEmbedsSurviving`, `ToolNoReinsert` to `Alg2Config.ValidNoHidden`).
* `weightValid_norm1_of_hiddenStableAt`, `freshInv_pullback_hiddenStable`: `HiddenStableAt`
  implies `Game.WeightValid (alg2PsiGame Ψ M₀)` and transfers cleanly across `FreshInv`.
* `weakHiddenStable_suffix`, `wstr_const_or_one_of_isSpec`, and `chainW` monotonicity/scaling:
  propagating `WeakHiddenStable` down active tree-chain levels via `SparseCoreRestartTool.IsSpecRestart`
  item 5 and tracking `wstr` via item 2.
* `Alg2HiddenTrace`: Game transcript (`ValidPlayPrefix` + `FollowsStrategyPrefix`), round-wise
  snapshots, per-level `LevelHistory` matching `coreInstanceFrom`, and constructor of `RepQualityCtx`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section ConfigAndWeights

/-- Full parameter validity hypotheses for **Theorem 5.1** and **Lemma 6.5**. -/
structure Alg2Config.Valid (cfg : Alg2Config) : Prop where
  hTP : cfg.TP.Valid
  hLP : cfg.LP.Valid
  hT : cfg.T.IsSpecRestart cfg.TP
  hL : cfg.L.IsSpec cfg.LP
  hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → cfg.σ_mwu n₁ ≤ cfg.σ_mwu n₂
  hσ_mwu_nn : 0 ≤ cfg.σ_mwu cfg.N₀
  hMWU : cfg.T.ToolMWURestart cfg.σ_mwu
  hEmb : cfg.T.ToolEmbedsSurvivingRestart
  hNoReins : cfg.T.ToolNoReinsertRestart
  hγM₀ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀
  hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k
  hα : 0 < cfg.α

lemma Alg2Config.Valid.toNoHidden {cfg : Alg2Config} (hV : cfg.Valid) : cfg.ValidNoHidden where
  hTP := hV.hTP
  hLP := hV.hLP
  hT := SparseCoreRestartTool.IsSpecRestart.toNoHidden hV.hT
  hL := hV.hL
  hσ_mwu_mono := hV.hσ_mwu_mono
  hσ_mwu_nn := hV.hσ_mwu_nn
  hMWU := hV.hMWU.toNoHidden
  hEmb := hV.hEmb.toNoHidden
  hNoReins := hV.hNoReins.toNoHidden
  hγM₀ := hV.hγM₀
  hγk := hV.hγk
  hα := hV.hα

lemma alg2KappaAt_pos {cfg : Alg2Config} (hV : cfg.ValidNoHidden) (nLast : ℕ) :
    0 < alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast := by
  refine kappaBound_pos (hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)) ?_ (le_max_left _ _)
  exact le_trans zero_le_one (le_max_of_le_left (hV.hTP.1 cfg.P.k cfg.N₀ cfg.P.hk))

lemma alg2Kappa_pos {cfg : Alg2Config} (hV : cfg.ValidNoHidden) :
    0 < alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
  alg2KappaAt_pos hV cfg.N₀

lemma norm1_pos_of_hiddenStableAt {D : DynamicInstance} {α Ψ : ℝ} {c w : ℕ → ℕ → ℝ} {t : ℕ}
    (hα : 0 < α) (hHS : D.HiddenStableAt α Ψ c w t) : 0 < (D.G t).norm1 (w t) := by
  by_contra hle
  have hnn : 0 ≤ (D.G t).norm1 (w t) := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h0 : (D.G t).norm1 (w t) = 0 := le_antisymm (not_lt.mp hle) hnn
  have h3 := hHS.2.2.1
  change (D.G t).inner (D.g t) (c t) / (D.G t).norm1 (w t) ≤ -α at h3
  rw [h0, div_zero] at h3
  linarith

lemma weightValid_norm1_of_hiddenStableAt {D : DynamicInstance} {α Ψ : ℝ} {c w : ℕ → ℕ → ℝ}
    {t M₀ : ℕ} (hα : 0 < α) (hm : (D.G t).m ≤ M₀) (hHS : D.HiddenStableAt α Ψ c w t) :
    Game.WeightValid (alg2PsiGame Ψ M₀) ((D.G t).norm1 (w t)) := by
  have hWpos : 0 < (D.G t).norm1 (w t) := norm1_pos_of_hiddenStableAt hα hHS
  have hEne : (D.G t).E.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have : (D.G t).norm1 (w t) = 0 := by simp [MGraph.norm1, hemp]
    linarith
  obtain ⟨e₀, he₀⟩ := hEne
  have hw₀ := hHS.2.2.2.2 e₀ he₀
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo_e : Real.exp (-Ψ) ≤ w t e₀ := by
    have := (abs_le.mp hw₀.2.1).1
    rw [← Real.exp_log hw₀.1]
    exact Real.exp_le_exp.mpr this
  have hlo_W : Real.exp (-Ψ) ≤ (D.G t).norm1 (w t) := by
    have hs : |w t e₀| ≤ (D.G t).norm1 (w t) := by
      unfold MGraph.norm1
      exact Finset.single_le_sum (fun x _ => abs_nonneg (w t x)) he₀
    rw [abs_of_pos hw₀.1] at hs
    exact le_trans hlo_e hs
  have hhi_W : (D.G t).norm1 (w t) < ((M₀ : ℝ) + 1) * Real.exp Ψ := by
    have hsum : (D.G t).norm1 (w t) ≤ ((D.G t).E.card : ℝ) * Real.exp Ψ := by
      unfold MGraph.norm1
      calc
        ∑ e ∈ (D.G t).E, |w t e| ≤ ∑ _e ∈ (D.G t).E, Real.exp Ψ := by
          refine Finset.sum_le_sum fun e he => ?_
          have hwe := hHS.2.2.2.2 e he
          rw [abs_of_pos hwe.1, ← Real.exp_log hwe.1]
          exact Real.exp_le_exp.mpr (abs_le.mp hwe.2.1).2
        _ = ((D.G t).E.card : ℝ) * Real.exp Ψ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hm1 : ((D.G t).E.card : ℝ) < (M₀ : ℝ) + 1 := by
      have : ((D.G t).E.card : ℝ) ≤ M₀ := by exact_mod_cast hm
      linarith
    exact lt_of_le_of_lt hsum (mul_lt_mul_of_pos_right hm1 (Real.exp_pos Ψ))
  have hlog_lo : -Ψ ≤ Real.log ((D.G t).norm1 (w t)) := by
    rw [← Real.log_exp (-Ψ)]
    exact Real.log_le_log (Real.exp_pos _) hlo_W
  have hlog_hi : Real.log ((D.G t).norm1 (w t)) < Real.log ((M₀ : ℝ) + 1) + Ψ := by
    have hM1_pos : (0 : ℝ) < (M₀ : ℝ) + 1 := by positivity
    rw [← Real.log_exp Ψ, ← Real.log_mul hM1_pos.ne' (Real.exp_pos _).ne']
    exact Real.log_lt_log hWpos hhi_W
  have hlogb_lo : -(alg2PsiGame Ψ M₀) < Real.logb 2 ((D.G t).norm1 (w t)) := by
    have hdiv : -Ψ / Real.log 2 ≤ Real.log ((D.G t).norm1 (w t)) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog_lo hlog2_pos.le
    have hM1_nn : 0 ≤ Real.log ((M₀ : ℝ) + 1) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ M₀ from Nat.cast_nonneg _])
    have hpsi_lt : Ψ / Real.log 2 < alg2PsiGame Ψ M₀ := by
      refine lt_of_lt_of_le ?_ (alg2PsiGame_real_le Ψ M₀)
      have : Ψ / Real.log 2 ≤ (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2_pos.le
      linarith
    change -(alg2PsiGame Ψ M₀) < Real.log ((D.G t).norm1 (w t)) / Real.log 2
    have : -alg2PsiGame Ψ M₀ < -Ψ / Real.log 2 := by
      rw [neg_div]; exact neg_lt_neg hpsi_lt
    exact lt_of_lt_of_le this hdiv
  have hlogb_hi : Real.logb 2 ((D.G t).norm1 (w t)) < alg2PsiGame Ψ M₀ := by
    change Real.log ((D.G t).norm1 (w t)) / Real.log 2 < alg2PsiGame Ψ M₀
    have hdiv : Real.log ((D.G t).norm1 (w t)) / Real.log 2 <
        (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 :=
      div_lt_div_of_pos_right (by linarith) hlog2_pos
    have hlt1 : (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 <
        (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 + 1 := by linarith
    exact lt_of_lt_of_le (lt_trans hdiv hlt1) (alg2PsiGame_real_le Ψ M₀)
  exact ⟨hWpos, hlogb_lo, hlogb_hi⟩

lemma freshInv_pullback_hiddenAt {D : DynamicInstance} {α Ψ : ℝ} {c w : ℕ → ℕ → ℝ} {t : ℕ}
    {intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv (D.G t) intG e2i i2e nf) (hHS : D.HiddenStableAt α Ψ c w t) :
    let ℓ_int := fun e' => D.ℓ t (i2e e')
    let g_int := fun e' => D.g t (i2e e')
    let c_int := fun e' => c t (i2e e')
    let w_int := fun e' => w t (i2e e')
    intG.IsCirculation c_int ∧
    IsValidPair intG ℓ_int c_int w_int ∧
    intG.inner g_int c_int / intG.norm1 w_int ≤ -α ∧
    ∀ e' ∈ intG.E, 0 < w_int e' ∧ |Real.log (w_int e')| ≤ Ψ ∧
      0 < ℓ_int e' ∧ |Real.log (ℓ_int e')| ≤ Ψ := by
  have hinj : Set.InjOn e2i (D.G t).E := fun e₁ h1 e₂ h2 heq => by
    have := congrArg i2e heq
    rwa [hF.hLeft e₁ h1, hF.hLeft e₂ h2] at this
  have hc_int : intG.IsCirculation (fun e' => c t (i2e e')) := by
    intro v hv
    have hdv := hHS.1 v (hF.hV ▸ hv)
    have hsum_eq : intG.demand (fun e' => c t (i2e e')) v = (D.G t).demand (c t) v := by
      unfold MGraph.demand MGraph.b
      rw [hF.hE, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun e he => ?_
      simp [hF.hTail e he, hF.hHead e he, hF.hLeft e he]
    rwa [hsum_eq]
  have hvp_int : IsValidPair intG (fun e' => D.ℓ t (i2e e'))
      (fun e' => c t (i2e e')) (fun e' => w t (i2e e')) :=
    ⟨hc_int, fun e' he' => hHS.2.1.2 (i2e e') (hF.hRight e' he').2⟩
  have hinner_eq : intG.inner (fun e' => D.g t (i2e e')) (fun e' => c t (i2e e')) =
      (D.G t).inner (D.g t) (c t) := by
    unfold MGraph.inner
    rw [hF.hE, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun e he => by simp [hF.hLeft e he]
  have hratio : intG.inner (fun e' => D.g t (i2e e')) (fun e' => c t (i2e e')) /
      intG.norm1 (fun e' => w t (i2e e')) ≤ -α := by
    rw [hinner_eq, hF.norm1_pullback]
    exact hHS.2.2.1
  exact ⟨hc_int, hvp_int, hratio, fun e' he' => hHS.2.2.2.2 (i2e e') (hF.hRight e' he').2⟩

end ConfigAndWeights

section WeakHiddenAndChainW

lemma chainW_nonneg {C : TreeChain} {w : ℕ → ℝ} {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hw : ∀ e ∈ G.E, 0 ≤ w e) :
    ∀ i ≤ C.d, ∀ e ∈ (C.G i).E, 0 ≤ C.chainW w i e := by
  have hvp0 : IsValidPair G ℓ (fun _ => 0) w :=
    ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using hw e he⟩
  intro i hi e he
  exact le_trans (abs_nonneg _) ((C.chain_isValidPair hH hSub hℓ hvp0 i hi).1.2 e he)

lemma chainW_scale_two (C : TreeChain) (w : ℕ → ℝ) :
    ∀ i e, C.chainW (fun x => 2 * w x) i e = 2 * C.chainW w i e := by
  intro i
  induction i with
  | zero => intro e; rfl
  | succ k ih =>
    intro e
    unfold TreeChain.chainW passSparseCoreW passCoreW
    have hsum :
        ∑ e' ∈ (C.activeCore k).E,
            (C.activeLSF k).wstr e' * C.chainW (fun x => 2 * w x) k e' *
              walkCount (C.activeEmb k e') e =
          2 * ∑ e' ∈ (C.activeCore k).E,
            (C.activeLSF k).wstr e' * C.chainW w k e' * walkCount (C.activeEmb k e') e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [ih e']
      ring
    rw [hsum]

lemma chainW_mono {C₁ C₂ : TreeChain} {w₁ w₂ : ℕ → ℝ} {i : ℕ}
    (hG : ∀ k ≤ i, C₁.G k = C₂.G k)
    (hL : ∀ k < i, C₁.activeLSF k = C₂.activeLSF k)
    (hE : ∀ k < i, C₁.activeEmb k = C₂.activeEmb k)
    (hle : ∀ e ∈ (C₁.G 0).E, w₁ e ≤ w₂ e)
    {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C₁.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C₁.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (_hG0 : C₁.G 0 = G) (hi : i ≤ C₁.d) :
    ∀ e ∈ (C₁.G i).E, C₁.chainW w₁ i e ≤ C₂.chainW w₂ i e := by
  induction i with
  | zero =>
    intro e he
    exact hle e he
  | succ k ih =>
    intro e _
    have hk_lt : k < C₁.d := hi
    have hle_k : ∀ e' ∈ (C₁.G k).E, C₁.chainW w₁ k e' ≤ C₂.chainW w₂ k e' :=
      ih (fun m hm => hG m (Nat.le_succ_of_le hm))
        (fun m hm => hL m (Nat.lt_succ_of_lt hm))
        (fun m hm => hE m (Nat.lt_succ_of_lt hm)) (Nat.le_of_lt hk_lt)
    have hGk : C₁.G k = C₂.G k := hG k (Nat.le_succ _)
    have hLk : C₁.activeLSF k = C₂.activeLSF k := hL k (Nat.lt_succ_self k)
    have hEk : C₁.activeEmb k = C₂.activeEmb k := hE k (Nat.lt_succ_self k)
    have hCk : C₁.activeCore k = C₂.activeCore k := by simp [TreeChain.activeCore, hGk, hLk]
    have hLSFk := C₁.activeLSF_holds hH (Nat.le_of_lt hk_lt)
    have hℓk_nn : ∀ f ∈ (C₁.G k).E, 0 ≤ C₁.chainLen ℓ k f := fun f hf => by
      have hvp0 : IsValidPair G ℓ (fun _ => 0) (fun _ => 0) :=
        ⟨fun _ _ => by simp [MGraph.demand], fun _ _ => by simp⟩
      exact (C₁.chain_isValidPair hH hSub hℓ hvp0 k (Nat.le_of_lt hk_lt)).2 f hf
    unfold TreeChain.chainW
    rw [hCk, hLk, hEk]
    unfold passSparseCoreW passCoreW
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e' he' => ?_) (by norm_num)
    have heGk : e' ∈ (C₁.G k).E := by rw [← hCk] at he'; exact (Finset.mem_sdiff.mp he').1
    have hwstr_nn : 0 ≤ (C₂.activeLSF k).wstr e' := by
      rw [← hLk]
      exact le_trans zero_le_one (le_trans (one_le_stretch hLSFk.2.1.2.2.2.2 hℓk_nn heGk)
        (hLSFk.2.2.2 e' heGk).1)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hle_k e' heGk) hwstr_nn)
      (walkCount_nonneg _ _)

/-- Restrict `WeakHiddenStable D_big L_big Ψ c w` to a suffix `D_small` of length
`L_small ≤ L_big` whose `(G, U, ℓ)` agrees with `D_big` shifted by `off = L_big - L_small`. -/
lemma weakHiddenStable_suffix {D_big D_small : DynamicInstance} {L_big L_small off : ℕ}
    {Ψ : ℝ} {c w : ℕ → ℕ → ℝ}
    (hoff : off + L_small = L_big)
    (hWeak : WeakHiddenStable D_big L_big Ψ c w)
    (hG : ∀ δ ≤ L_small, D_small.G δ = D_big.G (off + δ))
    (hU : ∀ δ, 1 ≤ δ → δ ≤ L_small → D_small.U δ = D_big.U (off + δ))
    (hℓ : ∀ δ ≤ L_small, ∀ e ∈ (D_small.G δ).E, D_small.ℓ δ e = D_big.ℓ (off + δ) e) :
    WeakHiddenStable D_small L_small Ψ (fun δ => c (off + δ)) (fun δ => w (off + δ)) := by
  intro δ hδ
  have hB := hWeak (off + δ) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hG δ hδ]; exact hB.1
  · refine ⟨(hG δ hδ).symm ▸ hB.2.1.1, fun e he => ?_⟩
    rw [hℓ δ hδ e he]
    exact hB.2.1.2 e ((hG δ hδ) ▸ he)
  · intro e he s hs hNoIns
    have hNoInsB : D_big.NotInsertedBetween e (off + s) (off + δ) := by
      intro x hx1 hx2 u hu hIns
      have hx1' : s < x - off := by omega
      have hxeq : x = off + (x - off) := by omega
      rw [hxeq, ← hU (x - off) (by omega) (by omega)] at hu
      exact hNoIns (x - off) hx1' (by omega) u hu hIns
    exact hB.2.2.1 e ((hG δ hδ) ▸ he) (off + s) (by omega) hNoInsB
  · intro e he
    have := hB.2.2.2 e ((hG δ hδ) ▸ he)
    rw [hℓ δ hδ e he]
    exact this

/-- Corollary 6.4 for an explicit per-level MWU average-stretch bound `σ_lvl` at level `i < C.d`
(independent of level `d`'s `LP.σ_mwu`). -/
theorem corollary_6_4_of_lvl {C : TreeChain} {G : MGraph} {ℓ w : ℕ → ℝ}
    {σ σ_mwu σ_lvl γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hw : ∀ e ∈ G.E, 0 ≤ w e) (hσ_nn : 0 ≤ σ_lvl)
    {i : ℕ} (hi : i < C.d)
    (hmwu : ∀ e ∈ (C.G i).E,
      (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr e) / (C.k : ℝ) ≤ σ_lvl) :
    (∑ j ∈ Finset.range C.k, hstrAt C w i j) / (C.k : ℝ) ≤ σ_lvl ∧
    ∃ j < C.k, hstrAt C w i j ≤ σ_lvl := by
  have hk_pos : (0 : ℝ) < C.k := Nat.cast_pos.mpr hH.2.2.1
  have hvp0 : IsValidPair G ℓ (fun _ => 0) w :=
    ⟨fun _ _ => by simp [MGraph.demand], fun e he => by simpa using hw e he⟩
  have hci := C.chain_isValidPair hH hSub hℓ hvp0 i (Nat.le_of_lt hi)
  have hwi_nn : ∀ e ∈ (C.G i).E, 0 ≤ C.chainW w i e := fun e he =>
    le_trans (abs_nonneg _) (hci.1.2 e he)
  have havg : (∑ j ∈ Finset.range C.k, hstrAt C w i j) / (C.k : ℝ) ≤ σ_lvl := by
    unfold hstrAt
    by_cases hden : (C.G i).norm1 (C.chainW w i) = 0
    · simp [hden, hσ_nn]
    · have hden_pos : 0 < (C.G i).norm1 (C.chainW w i) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Ne.symm hden)
      simp only [hden, ↓reduceIte]
      have hsum_eq :
          (∑ j ∈ Finset.range C.k,
            (∑ e ∈ (C.G i).E, (C.lsfs i j).wstr e * C.chainW w i e) /
              (C.G i).norm1 (C.chainW w i)) / (C.k : ℝ) =
          (∑ e ∈ (C.G i).E,
            ((∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr e) / (C.k : ℝ)) *
              C.chainW w i e) / (C.G i).norm1 (C.chainW w i) := by
        simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∑ e ∈ (C.G i).E, ∑ j ∈ Finset.range C.k,
              (C.lsfs i j).wstr e * C.chainW w i e =
            ∑ e ∈ (C.G i).E, (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr e) *
              C.chainW w i e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.sum_mul]
        rw [hinner, Finset.sum_mul, Finset.sum_mul]
        rw [show (∑ x ∈ (C.G i).E, (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr x) * (↑C.k)⁻¹ *
            C.chainW w i x) * ((C.G i).norm1 (C.chainW w i))⁻¹ =
            ∑ x ∈ (C.G i).E, (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr x) * (↑C.k)⁻¹ *
              C.chainW w i x * ((C.G i).norm1 (C.chainW w i))⁻¹ by rw [Finset.sum_mul]]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum_eq, div_le_iff₀ hden_pos]
      have hden_abs : (C.G i).norm1 (C.chainW w i) = ∑ e ∈ (C.G i).E, C.chainW w i e := by
        unfold MGraph.norm1
        exact Finset.sum_congr rfl fun e he => abs_of_nonneg (hwi_nn e he)
      rw [hden_abs, Finset.mul_sum]
      exact Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_right (hmwu e he) (hwi_nn e he)
  refine ⟨havg, ?_⟩
  by_contra hno
  push Not at hno
  have hlt_sum : ∑ _j ∈ Finset.range C.k, σ_lvl < ∑ j ∈ Finset.range C.k, hstrAt C w i j :=
    Finset.sum_lt_sum (fun j hj => (hno j (Finset.mem_range.mp hj)).le)
      ⟨0, Finset.mem_range.mpr hH.2.2.1, hno 0 hH.2.2.1⟩
  have hgt : (C.k : ℝ) * σ_lvl < ∑ j ∈ Finset.range C.k, hstrAt C w i j := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hlt_sum
  have : σ_lvl < (∑ j ∈ Finset.range C.k, hstrAt C w i j) / (C.k : ℝ) :=
    (lt_div_iff₀ hk_pos).mpr (by linarith)
  linarith

/-- Between `τ₁ ≤ τ₂ ≤ τ` on a valid run of `T`, every surviving edge at `τ₂` either received
an insertion in `(τ₁, τ₂]` (and thus has `wstr = 1`) or survived without insertion since `τ₁`
(keeping the same `wstr` as at `τ₁`). -/
lemma wstr_const_or_one_of_isSpec {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (hT : T.IsSpecRestartNoHidden P) {k τ M N : ℕ} {D : DynamicInstance}
    (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG0 : (D.G 0).IsValid) (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hℓPos : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hm₀ : (D.G 0).m ≤ M) (hn₀ : (D.G 0).n ≤ N)
    (hRest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hTh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    {j : ℕ} (hj : j < k) {τ₁ τ₂ : ℕ} (h12 : τ₁ ≤ τ₂) (h2 : τ₂ ≤ τ) :
    ∀ e ∈ (D.G τ₂).E,
      (T.lsfs (T.runAfterRestarts k M N D restarts τ₂) j).wstr e = 1 ∨
      (e ∈ (D.G τ₁).E ∧
        (T.lsfs (T.runAfterRestarts k M N D restarts τ₂) j).wstr e =
          (T.lsfs (T.runAfterRestarts k M N D restarts τ₁) j).wstr e ∧
        D.NotInsertedBetween e τ₁ τ₂) := by
  have hSpec := hT k τ M N D restarts hk hG0 hD hLen hℓPos hm₀ hn₀ hRest hTh
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h12
  clear h12
  induction r with
  | zero =>
    intro e he
    right
    refine ⟨he, rfl, fun s hs1 hs2 => by omega⟩
  | succ r ih =>
    intro e he
    have hr2 : τ₁ + r ≤ τ := by omega
    have hStep := hSpec.2.1 (τ₁ + r + 1) (by omega) h2 j hj
    dsimp only at hStep
    simp only [Nat.add_sub_cancel] at hStep
    by_cases hIns : ∃ u ∈ D.U (τ₁ + r + 1), u.Inserts e
    · left
      exact hStep.2.2.1 e he hIns
    · have hGeq : D.G (τ₁ + r + 1) = (D.G (τ₁ + r)).applyBatch (D.U (τ₁ + r + 1)) := by
        have hV := (hD (τ₁ + r + 1) (by omega) h2).2
        simpa [Nat.add_sub_cancel] using hV
      have he_pre : e ∈ (D.G (τ₁ + r)).E :=
        mem_pre_of_mem_applyBatch (hGeq ▸ he) (fun u hu hIu => hIns ⟨u, hu, hIu⟩)
      have hw_eq := hStep.2.1 e he he_pre (fun u hu hIu => hIns ⟨u, hu, hIu⟩)
      rcases ih hr2 e he_pre with hOne | ⟨he1, hw_pre, hNoPre⟩
      · left; exact hw_eq.trans hOne
      · right
        refine ⟨he1, hw_eq.trans hw_pre, fun s hs1 hs2 u hu => ?_⟩
        rcases eq_or_lt_of_le hs2 with rfl | hslt
        · exact fun hIu => hIns ⟨u, hu, hIu⟩
        · exact hNoPre s hs1 (by omega) u hu

end WeakHiddenAndChainW

section Alg2HiddenTraceSection

/-- Full hidden-stable synchronization invariant linking `Algorithm 2` state `st`,
per-level `LevelHistory`, external witness `(D, c_ext, w_ext)`, and a valid Game
transcript `(moves, initStr, W_game)` ending in `.stage34`, parameterized by total stretch
cap `σ_cap`. -/
structure Alg2HiddenTraceAt (σ_cap : ℝ) (cfg : Alg2Config) (D : DynamicInstance)
    (c_ext w_ext : ℕ → ℕ → ℝ) (t : ℕ) (st : Alg2State cfg) where
  moves : List (Game.Move cfg.P.d cfg.P.k)
  hmne : moves ≠ []
  initStr : Fin (cfg.P.d + 1) → Fin cfg.P.k → ℝ
  W_game : ℕ → ℝ
  hv : Game.ValidPlayPrefix cfg.gameParams W_game initStr moves
  hf : Game.FollowsStrategyPrefix cfg.gameParams W_game initStr moves
  hPhase : (Game.stateAt W_game cfg.P.hk initStr moves moves.length).phase = .stage34
  timeOfRound : ℕ → ℕ
  hTimeMono : ∀ r₁ r₂, r₁ ≤ r₂ →
    r₂ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    timeOfRound r₁ ≤ timeOfRound r₂
  hTimeEnd : timeOfRound (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = t
  hW_eq : ∀ r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round,
    W_game r = (D.G (timeOfRound r)).norm1 (w_ext (timeOfRound r))
  hShiftMatch : ∀ i : Fin (cfg.P.d + 1), Game.shiftCount moves i = st.chain.shiftCount i.val
  hRebMatch : ∀ i : Fin (cfg.P.d + 1), Game.rebuildCount moves i = st.chain.rebuildCount i.val
  hPassMatch : ∀ i : Fin (cfg.P.d + 1),
    Game.passesAt W_game cfg.P.hk initStr moves moves.length i = st.passes i
  hBranMatch : ∀ i : Fin (cfg.P.d + 1),
    ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).bran i).val =
      if i.val < cfg.P.d then st.chain.bran i.val else st.branD
  -- Per-round `TreeChain` snapshots and fresh-ID translations
  snapC : ℕ → TreeChain
  snapE2I : ℕ → ℕ → ℕ
  snapI2E : ℕ → ℕ → ℕ
  snapNF : ℕ → ℕ
  hSnapEndC : snapC (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round =
    st.chain.toTreeChain
  hSnapEndE2I : snapE2I (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = st.extToInt
  hSnapEndI2E : snapI2E (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = st.intToExt
  hSnapEndNF : snapNF (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = st.nextFresh
  hSnapFresh : ∀ r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round,
    FreshInv (D.G (timeOfRound r)) ((snapC r).G 0) (snapE2I r) (snapI2E r) (snapNF r)
  hSnapHolds : ∀ r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round,
    (snapC r).d = cfg.P.d ∧ (snapC r).k = cfg.P.k ∧
    (snapC r).Holds ((snapC r).G 0) (fun e' => D.ℓ (timeOfRound r) (snapI2E r e'))
      σ_cap
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) ∧
    (snapC r).ForestsAreSubgraphs ∧
    ∀ i < cfg.P.d, ∀ e ∈ ((snapC r).G i).E,
      (∑ j ∈ Finset.range cfg.P.k, ((snapC r).lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀
  reinit : Fin (cfg.P.d + 1) → ℕ
  hRebRep : ∀ i : Fin (cfg.P.d + 1),
    reinit i ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i
  hRepRe : ∀ i : Fin cfg.P.d,
    (Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤
    reinit ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  hSnapBran : ∀ i (hi : i ≤ cfg.P.d),
    ∀ r, reinit ⟨i, Nat.lt_succ_of_le hi⟩ ≤ r →
      r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      ∀ b < i, (snapC r).bran b = st.chain.bran b
  hStrMatch : ∀ (i : Fin (cfg.P.d + 1)) (j : Fin cfg.P.k),
    (Game.stateAt W_game cfg.P.hk initStr moves moves.length).str i j =
      if _hi : i.val < cfg.P.d then
        hstrAt (snapC ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i))
          (fun e' => w_ext (timeOfRound ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i))
            (snapI2E ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i) e'))
          i.val j.val
      else 0
  -- Per-level histories synchronized with rounds `reinit i .. currRound`
  H : ∀ i < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ st.chain i
  lvlIdx : ℕ → ℕ → ℕ
  hLvlReinit : ∀ i (hi : i < cfg.P.d),
    lvlIdx (reinit ⟨i, Nat.lt_succ_of_le hi.le⟩) i = 0
  hLvlEnd : ∀ i (hi : i < cfg.P.d),
    lvlIdx (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round i = (H i hi).len
  hLvlMono : ∀ i (hi : i < cfg.P.d), ∀ r₁ r₂,
    reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r₁ →
    r₁ ≤ r₂ → r₂ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    lvlIdx r₁ i ≤ lvlIdx r₂ i
  hLvlSucc : ∀ i (hi : i + 1 < cfg.P.d),
    (H (i + 1) hi).len ≤ (H i (Nat.lt_of_succ_lt hi)).len ∧
    ∀ r, reinit ⟨i + 1, Nat.lt_succ_of_le hi.le⟩ ≤ r →
      r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      lvlIdx r (i + 1) + ((H i (Nat.lt_of_succ_lt hi)).len - (H (i + 1) hi).len) = lvlIdx r i
  hLvlSnap : ∀ i (hi : i < cfg.P.d), ∀ r,
    reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r →
    r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    (snapC r).G i = (H i hi).D.G (lvlIdx r i) ∧
    (∀ j < cfg.P.k, (snapC r).lsfs i j =
      cfg.T.lsfs (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
        (H i hi).D (H i hi).restarts (lvlIdx r i)) j) ∧
    (reinit ⟨i + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ ≤ r →
      ∀ j < cfg.P.k, (snapC r).emb i j =
        cfg.T.emb (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
          (H i hi).D (H i hi).restarts (lvlIdx r i)) j)
  hLvlCore : ∀ k (hk : k + 1 < cfg.P.d),
    let Hk := H k (Nat.lt_of_succ_lt hk)
    let Hk1 := H (k + 1) hk
    let off := Hk.len - Hk1.len
    Hk.s₀ ≤ off ∧
    (∀ δ ≤ Hk1.len,
      Hk1.D.G δ =
        (cfg.T.coreInstanceFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.restarts Hk.s₀ (st.chain.bran k)).G
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ, 1 ≤ δ → δ ≤ Hk1.len →
      Hk1.D.U δ =
        (cfg.T.coreInstanceFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.restarts Hk.s₀ (st.chain.bran k)).U
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ ≤ Hk1.len, ∀ e ∈ (Hk1.D.G δ).E,
      Hk1.D.ℓ δ e =
        (cfg.T.coreInstanceFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.restarts Hk.s₀ (st.chain.bran k)).ℓ
          ((off - Hk.s₀) + δ) e)
  -- Level-0 external step timeline (`0 .. (H 0).len`)
  updRound : ℕ → ℕ
  hUpdBound : ∀ τ ≤ (H 0 cfg.P.hd).len,
    reinit ⟨0, Nat.succ_pos _⟩ ≤ updRound τ ∧
    updRound τ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round
  hUpdMono : ∀ τ₁ τ₂, τ₁ < τ₂ → τ₂ ≤ (H 0 cfg.P.hd).len → updRound τ₁ < updRound τ₂
  hUpdBand : ∀ r,
    reinit ⟨0, Nat.succ_pos _⟩ ≤ r →
    r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    updRound (lvlIdx r 0) ≤ r ∧ (lvlIdx r 0 < (H 0 cfg.P.hd).len → r < updRound (lvlIdx r 0 + 1))
  hLvl0Match : ∀ τ ≤ (H 0 cfg.P.hd).len,
    (H 0 cfg.P.hd).D.G τ = (snapC (updRound τ)).G 0 ∧
    ∀ e' ∈ ((H 0 cfg.P.hd).D.G τ).E,
      (H 0 cfg.P.hd).D.ℓ τ e' = D.ℓ (timeOfRound (updRound τ)) (snapI2E (updRound τ) e')
  hLvl0NoIns : ∀ s τ, s ≤ τ → τ ≤ (H 0 cfg.P.hd).len →
    ∀ r_s r_τ,
      updRound s ≤ r_s → r_s ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      (s < (H 0 cfg.P.hd).len → r_s < updRound (s + 1)) →
      updRound τ ≤ r_τ → r_τ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      (τ < (H 0 cfg.P.hd).len → r_τ < updRound (τ + 1)) →
      r_s ≤ r_τ →
      ∀ e' ∈ ((H 0 cfg.P.hd).D.G τ).E,
        (s = τ →
          snapI2E r_τ e' = snapI2E r_s e' ∧
          D.NotInsertedBetween (snapI2E r_τ e') (timeOfRound r_s) (timeOfRound r_τ) ∧
          D.ℓ (timeOfRound r_τ) (snapI2E r_τ e') = D.ℓ (timeOfRound r_s) (snapI2E r_τ e')) ∧
        ((H 0 cfg.P.hd).D.NotInsertedBetween e' s τ →
          snapI2E r_τ e' = snapI2E r_s e' ∧
          D.NotInsertedBetween (snapI2E r_τ e') (timeOfRound r_s) (timeOfRound r_τ))

/-- `Alg2HiddenTrace` specialized to the global vertex cap `alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀`. -/
abbrev Alg2HiddenTrace (cfg : Alg2Config) (D : DynamicInstance)
    (c_ext w_ext : ℕ → ℕ → ℝ) (t : ℕ) (st : Alg2State cfg) :=
  Alg2HiddenTraceAt (alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀) cfg D c_ext w_ext t st

/-- Construct `RepQualityCtx` from `Alg2HiddenTraceAt` under `D.HiddenStable t α Ψ`, bridging
level-0 to level-`i` weights through `SparseCoreTool.IsSpec` item 2. -/
theorem Alg2HiddenTraceAt.toRepQualityCtx {σ_cap : ℝ} {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain) :
    ∃ ctx : RepQualityCtx,
      ctx.d = cfg.P.d ∧ ctx.k = cfg.P.k ∧
      ctx.γ_ℓ = cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ∧ ctx.γ_c = cfg.TP.γ_c (cfg.P.M₀ ^ 2) ∧
      ctx.σ = σ_cap ∧
      ctx.σ_mwu = max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀) ∧
      ctx.t = (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round ∧
      ctx.C = tr.snapC ∧
      (∀ r ≤ ctx.t, ctx.G0 r = (tr.snapC r).G 0 ∧
        ctx.ℓ0 r = (fun e' => D.ℓ (tr.timeOfRound r) (tr.snapI2E r e')) ∧
        ctx.w r = (fun e' => w_ext (tr.timeOfRound r) (tr.snapI2E r e'))) ∧
      (∀ i : Fin (cfg.P.d + 1),
        ctx.reinit i.val = tr.reinit i ∧
        ctx.repT i.val = (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).repT i) := by
  set gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  set R := gSt.round
  have hRebRep := tr.hRebRep
  have hRepRe := tr.hRepRe
  have hRepB := Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  let mkFin : ℕ → Fin (cfg.P.d + 1) := fun i => ⟨min i cfg.P.d, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hFin_eq : ∀ i ≤ cfg.P.d, (mkFin i).val = i := fun i hi => min_eq_left hi
  let reinitFn : ℕ → ℕ := fun i => tr.reinit (mkFin i)
  let repTFn : ℕ → ℕ := fun i => gSt.repT (mkFin i)
  let ℓ0Fn : ℕ → ℕ → ℝ := fun r e' => D.ℓ (tr.timeOfRound r) (tr.snapI2E r e')
  let wFn : ℕ → ℕ → ℝ := fun r e' => w_ext (tr.timeOfRound r) (tr.snapI2E r e')
  have hRep : IsRepTimestamps cfg.P.d reinitFn R repTFn := by
    refine ⟨fun i _ => ⟨hRebRep (mkFin i), (hRepB (mkFin i)).2⟩, fun i hi1 hi2 => ?_, fun i hi => ?_⟩
    · have h1 : gSt.repT (mkFin (i - 1)) ≤ tr.reinit (mkFin i) := by
        have := hRepRe ⟨i - 1, by omega⟩
        convert this using 2 <;> exact Fin.ext (by simp [mkFin]; omega)
      exact le_trans h1 (hRebRep (mkFin i))
    · have := hRepRe ⟨i, hi⟩
      convert this using 2 <;> exact Fin.ext (by simp [mkFin]; omega)
  have hre_mono : ∀ a b : Fin (cfg.P.d + 1), a ≤ b → tr.reinit a ≤ tr.reinit b := by
    intro a b hab
    obtain ⟨diff, hdiff⟩ := Nat.exists_eq_add_of_le (Fin.le_iff_val_le_val.mp hab)
    have hstep : ∀ d0 (hd0 : a.val + d0 ≤ cfg.P.d),
        tr.reinit a ≤ tr.reinit ⟨a.val + d0, Nat.lt_succ_of_le hd0⟩ := by
      intro d0; induction d0 with
      | zero => intro hd0; simp [Fin.eta]
      | succ d0 ih =>
        intro hd0
        exact le_trans (ih (by omega)) (le_trans (hRebRep ⟨a.val + d0, by omega⟩) (hRepRe ⟨a.val + d0, by omega⟩))
    rw [show b = ⟨a.val + diff, Nat.lt_succ_of_le (by omega)⟩ from Fin.ext (by omega)]
    exact hstep diff (by omega)
  have hNoIns_mem_pre : ∀ (D' : DynamicInstance) {τ τ₁ τ₂ : ℕ}, τ₁ ≤ τ₂ → τ₂ ≤ τ →
      D'.IsValid τ → ∀ e ∈ (D'.G τ₂).E, D'.NotInsertedBetween e τ₁ τ₂ → e ∈ (D'.G τ₁).E := by
    intro D' τ τ₁ τ₂ h12 h2 hD' e he hNoIns
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h12; clear h12
    induction r with
    | zero => exact he
    | succ r ih =>
      have hGeq : D'.G (τ₁ + r + 1) = (D'.G (τ₁ + r)).applyBatch (D'.U (τ₁ + r + 1)) := by
        simpa [Nat.add_sub_cancel] using (hD' (τ₁ + r + 1) (by omega) h2).2
      have he_pre : e ∈ (D'.G (τ₁ + r)).E :=
        mem_pre_of_mem_applyBatch (hGeq ▸ he) fun u hu => hNoIns (τ₁ + r + 1) (by omega) (by omega) u hu
      exact ih (by omega) he_pre fun s hs1 hs2 u hu => hNoIns s hs1 (by omega) u hu
  have hLvl_chainW : ∀ {i} (hi : i < cfg.P.d) {r₁ r₂}
      (hr1_lo : reinitFn i ≤ r₁) (hr1_hi : r₁ ≤ r₂) (hr2_hi : r₂ ≤ R)
      (e : ℕ) (he : e ∈ ((tr.snapC r₂).G i).E),
      (tr.H i hi).D.NotInsertedBetween e (tr.lvlIdx r₁ i) (tr.lvlIdx r₂ i) →
      (tr.snapC r₂).chainW (wFn r₂) i e ≤ 2 * (tr.snapC r₁).chainW (wFn r₁) i e := by
    intro i hi r₁ r₂ hr1_lo hr1_hi hr2_hi e he hNoIns
    have hR1 : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r₁ := by simpa [reinitFn, mkFin, hi.le] using hr1_lo
    have hR2 : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r₂ := le_trans hR1 hr1_hi
    have h12_lvl : tr.lvlIdx r₁ i ≤ tr.lvlIdx r₂ i := tr.hLvlMono i hi r₁ r₂ hR1 hr1_hi hr2_hi
    have h2_end : tr.lvlIdx r₂ i ≤ (tr.H i hi).len := by
      rw [← tr.hLvlEnd i hi]; exact tr.hLvlMono i hi r₂ R hR2 hr2_hi (le_refl R)
    have hre0_1 : tr.reinit ⟨0, Nat.succ_pos _⟩ ≤ r₁ := le_trans (hre_mono _ _ (Fin.zero_le _)) hR1
    have hre0_2 : tr.reinit ⟨0, Nat.succ_pos _⟩ ≤ r₂ := le_trans hre0_1 hr1_hi
    have hrek_r1 : ∀ {k} (hk : k ≤ i), tr.reinit ⟨k, Nat.lt_succ_of_le (by omega)⟩ ≤ r₁ := fun hk =>
      le_trans (hre_mono _ _ (Fin.le_iff_val_le_val.mpr (by simp; omega))) hR1
    by_cases heq_lvl : tr.lvlIdx r₁ i = tr.lvlIdx r₂ i
    · have hDiff_gap : ∀ gap ≤ i, tr.lvlIdx r₁ (i - gap) = tr.lvlIdx r₂ (i - gap) := by
        intro gap; induction gap with
        | zero => intro _; simpa using heq_lvl
        | succ g ihg =>
          intro hgi
          have hm : i - (g + 1) + 1 < cfg.P.d := by omega
          have hm1 : i - (g + 1) + 1 = i - g := by omega
          have hr_m1 := hrek_r1 (show i - (g + 1) + 1 ≤ i by omega)
          have hs1 := (tr.hLvlSucc (i - (g + 1)) hm).2 r₁ hr_m1 (le_trans hr1_hi hr2_hi)
          have hs2 := (tr.hLvlSucc (i - (g + 1)) hm).2 r₂ (le_trans hr_m1 hr1_hi) hr2_hi
          have hsub : tr.lvlIdx r₁ (i - (g + 1) + 1) = tr.lvlIdx r₂ (i - (g + 1) + 1) := by
            simpa [hm1] using ihg (by omega)
          rw [← hs1, ← hs2, hsub]
      have hDiff_eq : ∀ k ≤ i, tr.lvlIdx r₁ k = tr.lvlIdx r₂ k := fun k hk => by
        have := hDiff_gap (i - k) (by omega); rwa [Nat.sub_sub_self hk] at this
      have hG_eq : ∀ k ≤ i, (tr.snapC r₂).G k = (tr.snapC r₁).G k := fun k hk => by
        have hkd := lt_of_le_of_lt hk hi; have hrek := hrek_r1 hk
        rw [(tr.hLvlSnap k hkd r₂ (le_trans hrek hr1_hi) hr2_hi).1,
          (tr.hLvlSnap k hkd r₁ hrek (le_trans hr1_hi hr2_hi)).1, hDiff_eq k hk]
      have hS_r2 := tr.hSnapHolds r₂ hr2_hi
      have hBran_eq : ∀ k < i, (tr.snapC r₂).bran k = (tr.snapC r₁).bran k := fun k hk => by
        rw [tr.hSnapBran i hi.le r₂ hR2 hr2_hi k hk, tr.hSnapBran i hi.le r₁ hR1 (le_trans hr1_hi hr2_hi) k hk]
      have hbk_fn : ∀ k < i, (tr.snapC r₂).bran k < cfg.P.k := fun k hk => by
        rw [tr.hSnapBran i hi.le r₂ hR2 hr2_hi k hk]; exact hInv.hBran k (lt_trans hk hi)
      have hL_eq : ∀ k < i, (tr.snapC r₂).activeLSF k = (tr.snapC r₁).activeLSF k := fun k hk => by
        have hkd := lt_trans hk hi; have hrek := hrek_r1 hk.le; have hS1 := tr.hSnapHolds r₁ (le_trans hr1_hi hr2_hi)
        simp only [TreeChain.activeLSF, hS_r2.1, hS1.1, hkd, ↓reduceIte]
        rw [(tr.hLvlSnap k hkd r₂ (le_trans hrek hr1_hi) hr2_hi).2.1 _ (hbk_fn k hk), hBran_eq k hk,
          ← hDiff_eq k hk.le,
          ← (tr.hLvlSnap k hkd r₁ hrek (le_trans hr1_hi hr2_hi)).2.1 _ (by rw [← hBran_eq k hk]; exact hbk_fn k hk)]
      have hE_eq : ∀ k < i, (tr.snapC r₂).activeEmb k = (tr.snapC r₁).activeEmb k := fun k hk => by
        have hkd := lt_trans hk hi; have hrek := hrek_r1 hk.le; have hS1 := tr.hSnapHolds r₁ (le_trans hr1_hi hr2_hi)
        have hrek1 : tr.reinit ⟨k + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hkd)⟩ ≤ r₁ :=
          le_trans (hre_mono _ _ (Fin.le_iff_val_le_val.mpr (by simp; omega))) hR1
        simp only [TreeChain.activeEmb, hS_r2.1, hS1.1, hkd, ↓reduceIte]
        rw [(tr.hLvlSnap k hkd r₂ (le_trans hrek hr1_hi) hr2_hi).2.2 (le_trans hrek1 hr1_hi) _ (hbk_fn k hk),
          hBran_eq k hk, ← hDiff_eq k hk.le,
          ← (tr.hLvlSnap k hkd r₁ hrek (le_trans hr1_hi hr2_hi)).2.2 hrek1 _ (by rw [← hBran_eq k hk]; exact hbk_fn k hk)]
      have hw0_le : ∀ e' ∈ ((tr.snapC r₂).G 0).E, wFn r₂ e' ≤ 2 * wFn r₁ e' := fun e' he' => by
        set s0 := tr.lvlIdx r₂ 0
        have hs0_len : s0 ≤ (tr.H 0 cfg.P.hd).len := by
          rw [← tr.hLvlEnd 0 cfg.P.hd]; exact tr.hLvlMono 0 cfg.P.hd r₂ R hre0_2 hr2_hi (le_refl R)
        have hb1 := tr.hUpdBand r₁ hre0_1 (le_trans hr1_hi hr2_hi)
        have hb2 := tr.hUpdBand r₂ hre0_2 hr2_hi
        rw [hDiff_eq 0 (Nat.zero_le i)] at hb1
        have he'_H : e' ∈ ((tr.H 0 cfg.P.hd).D.G s0).E := by
          rw [← (tr.hLvlSnap 0 cfg.P.hd r₂ hre0_2 hr2_hi).1]; exact he'
        have hNI := (tr.hLvl0NoIns s0 s0 (le_refl _) hs0_len r₁ r₂ hb1.1 (le_trans hr1_hi hr2_hi)
          hb1.2 hb2.1 hr2_hi hb2.2 hr1_hi e' he'_H).1 rfl
        have ht2_le : tr.timeOfRound r₂ ≤ t :=
          le_trans (tr.hTimeMono r₂ R hr2_hi (le_refl R)) (le_of_eq tr.hTimeEnd)
        have hstab := (hHS (tr.timeOfRound r₂) ht2_le).2.2.2.1 (tr.snapI2E r₂ e')
          ((tr.hSnapFresh r₂ hr2_hi).hRight e' he').2 (tr.timeOfRound r₁)
          (tr.hTimeMono r₁ r₂ hr1_hi hr2_hi) hNI.2.1
        change w_ext (tr.timeOfRound r₂) (tr.snapI2E r₂ e') ≤
          2 * w_ext (tr.timeOfRound r₁) (tr.snapI2E r₁ e')
        rwa [← hNI.1]
      have hℓ2_nn : ∀ e' ∈ ((tr.snapC r₂).G 0).E, 0 ≤ ℓ0Fn r₂ e' := fun e' he' => by
        have ht2_le : tr.timeOfRound r₂ ≤ t :=
          le_trans (tr.hTimeMono r₂ R hr2_hi (le_refl R)) (le_of_eq tr.hTimeEnd)
        exact le_of_lt ((hHS (tr.timeOfRound r₂) ht2_le).2.2.2.2
          (tr.snapI2E r₂ e') ((tr.hSnapFresh r₂ hr2_hi).hRight e' he').2).2.2.1
      have hMono := chainW_mono hG_eq hL_eq hE_eq hw0_le hS_r2.2.2.1 hS_r2.2.2.2.1 hℓ2_nn rfl
        (by rw [hS_r2.1]; exact hi.le) e he
      rwa [chainW_scale_two] at hMono
    · have h12_lt : tr.lvlIdx r₁ i < tr.lvlIdx r₂ i := lt_of_le_of_ne h12_lvl heq_lvl
      have h_lvl0_lt : tr.lvlIdx r₁ 0 < tr.lvlIdx r₂ 0 := by
        have hdown : ∀ m (hm : m < cfg.P.d), m ≤ i → tr.lvlIdx r₁ m < tr.lvlIdx r₂ m →
            tr.lvlIdx r₁ 0 < tr.lvlIdx r₂ 0 := by
          intro m; induction m with
          | zero => intro _ _ h; exact h
          | succ m ihm =>
            intro hm hmi hlt
            have hrem1 := hrek_r1 hmi
            have hs1 := (tr.hLvlSucc m hm).2 r₁ hrem1 (le_trans hr1_hi hr2_hi)
            have hs2 := (tr.hLvlSucc m hm).2 r₂ (le_trans hrem1 hr1_hi) hr2_hi
            exact ihm (Nat.lt_of_succ_lt hm) (Nat.le_of_succ_le hmi) (by omega)
        exact hdown i hi (le_refl i) h12_lt
      set s₁ := tr.lvlIdx r₁ 0; set s₂ := tr.lvlIdx r₂ 0; set H0 := tr.H 0 cfg.P.hd
      have hs2_len : s₂ ≤ H0.len := by
        rw [← tr.hLvlEnd 0 cfg.P.hd]; exact tr.hLvlMono 0 cfg.P.hd r₂ R hre0_2 hr2_hi (le_refl R)
      let tPick : ℕ → ℕ := fun τ => if τ = s₁ then r₁ else if τ = s₂ then r₂ else tr.updRound τ
      have htPick_bd : ∀ τ ≤ H0.len,
          tr.reinit ⟨0, Nat.succ_pos _⟩ ≤ tPick τ ∧ tPick τ ≤ R ∧
          tr.updRound τ ≤ tPick τ ∧ (τ < H0.len → tPick τ < tr.updRound (τ + 1)) := by
        intro τ hτ; dsimp only [tPick]; split_ifs with h1 h2
        · subst h1; have hb := tr.hUpdBand r₁ hre0_1 (le_trans hr1_hi hr2_hi)
          exact ⟨hre0_1, le_trans hr1_hi hr2_hi, hb.1, hb.2⟩
        · subst h2; have hb := tr.hUpdBand r₂ hre0_2 hr2_hi
          exact ⟨hre0_2, hr2_hi, hb.1, hb.2⟩
        · have hub := tr.hUpdBound τ hτ
          exact ⟨hub.1, hub.2, le_rfl, fun hlt => tr.hUpdMono τ (τ + 1) (Nat.lt_succ_self _) hlt⟩
      have hUpdMono_le : ∀ a b, a ≤ b → b ≤ H0.len → tr.updRound a ≤ tr.updRound b := fun a b hab hb => by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab; clear hab
        induction k with
        | zero => exact le_rfl
        | succ k ihk => exact le_trans (ihk (by omega)) (le_of_lt (tr.hUpdMono _ _ (by omega) hb))
      have htPick_mono : ∀ τ₁ τ₂, τ₁ ≤ τ₂ → τ₂ ≤ H0.len → tPick τ₁ ≤ tPick τ₂ := fun τ₁ τ₂ h12 h2 => by
        rcases eq_or_lt_of_le h12 with rfl | hlt
        · exact le_rfl
        · exact le_trans (le_of_lt ((htPick_bd τ₁ (by omega)).2.2.2 (lt_of_lt_of_le hlt h2)))
            (le_trans (hUpdMono_le (τ₁ + 1) τ₂ hlt h2) (htPick_bd τ₂ h2).2.2.1)
      have hG0_match : ∀ τ ≤ H0.len, H0.D.G τ = (tr.snapC (tPick τ)).G 0 ∧
          ∀ e' ∈ (H0.D.G τ).E, H0.D.ℓ τ e' = D.ℓ (tr.timeOfRound (tPick τ)) (tr.snapI2E (tPick τ) e') := by
        intro τ hτ
        have h0m := tr.hLvl0Match τ hτ; have bτ := htPick_bd τ hτ; have hub := tr.hUpdBound τ hτ
        have hNI : ∀ e' ∈ (H0.D.G τ).E, tr.snapI2E (tPick τ) e' = tr.snapI2E (tr.updRound τ) e' ∧
            D.ℓ (tr.timeOfRound (tPick τ)) (tr.snapI2E (tPick τ) e') =
              D.ℓ (tr.timeOfRound (tr.updRound τ)) (tr.snapI2E (tPick τ) e') := fun e' he' => by
          have hS := (tr.hLvl0NoIns τ τ (le_refl τ) hτ (tr.updRound τ) (tPick τ) le_rfl hub.2
            (fun hlt => tr.hUpdMono τ (τ + 1) (Nat.lt_succ_self _) hlt)
            bτ.2.2.1 bτ.2.1 bτ.2.2.2 bτ.2.2.1 e' he').1 rfl
          exact ⟨hS.1, hS.2.2⟩
        have htP1 : tPick s₁ = r₁ := by simp [tPick]
        have htP2 : tPick s₂ = r₂ := by simp [tPick, Nat.ne_of_gt h_lvl0_lt]
        by_cases h1 : τ = s₁
        · subst h1; rw [htP1]
          refine ⟨(tr.hLvlSnap 0 cfg.P.hd r₁ hre0_1 (le_trans hr1_hi hr2_hi)).1.symm, fun e' he' => ?_⟩
          have hNIe := hNI e' he'; rw [htP1] at hNIe
          rw [h0m.2 e' he', hNIe.2, hNIe.1]
        · by_cases h2 : τ = s₂
          · subst h2; rw [htP2]
            refine ⟨(tr.hLvlSnap 0 cfg.P.hd r₂ hre0_2 hr2_hi).1.symm, fun e' he' => ?_⟩
            have hNIe := hNI e' he'; rw [htP2] at hNIe
            rw [h0m.2 e' he', hNIe.2, hNIe.1]
          · have htP0 : tPick τ = tr.updRound τ := by simp [tPick, h1, h2]
            rw [htP0]; exact h0m
      let c0 : ℕ → ℕ → ℝ := fun τ e' => c_ext (tr.timeOfRound (tPick τ)) (tr.snapI2E (tPick τ) e')
      let w0 : ℕ → ℕ → ℝ := fun τ e' => w_ext (tr.timeOfRound (tPick τ)) (tr.snapI2E (tPick τ) e')
      have hWHS0 : WeakHiddenStable H0.D H0.len cfg.Ψ c0 w0 := by
        intro τ hτ
        have bτ := htPick_bd τ hτ
        have ht_le : tr.timeOfRound (tPick τ) ≤ t :=
          le_trans (tr.hTimeMono (tPick τ) R bτ.2.1 (le_refl R)) (le_of_eq tr.hTimeEnd)
        have hHSτ := hHS (tr.timeOfRound (tPick τ)) ht_le
        have hFτ := tr.hSnapFresh (tPick τ) bτ.2.1; have hPb := freshInv_pullback_hiddenAt hFτ hHSτ
        have hGm := hG0_match τ hτ
        refine ⟨hGm.1.symm ▸ hPb.1, ⟨hGm.1 ▸ hPb.2.1.1, fun e' he' => ?_⟩, ?_, ?_⟩
        · rw [hGm.2 e' he']; exact hPb.2.1.2 e' (hGm.1 ▸ he')
        · intro e' he' s hs hNI
          have bs := htPick_bd s (le_trans hs hτ)
          have hNI0 := (tr.hLvl0NoIns s τ hs hτ (tPick s) (tPick τ) bs.2.2.1 bs.2.1 bs.2.2.2
            bτ.2.2.1 bτ.2.1 bτ.2.2.2 (htPick_mono s τ hs hτ) e' he').2 hNI
          have h2 := hHSτ.2.2.2.1 (tr.snapI2E (tPick τ) e') (hFτ.hRight e' (hGm.1 ▸ he')).2
            (tr.timeOfRound (tPick s)) (tr.hTimeMono (tPick s) (tPick τ) (htPick_mono s τ hs hτ) bτ.2.1) hNI0.2
          change w_ext (tr.timeOfRound (tPick τ)) (tr.snapI2E (tPick τ) e') ≤
            2 * w_ext (tr.timeOfRound (tPick s)) (tr.snapI2E (tPick s) e')
          rwa [← hNI0.1]
        · intro e' he'; rw [hGm.2 e' he']; exact hPb.2.2.2 e' (hGm.1 ▸ he')
      have hChainProp : ∀ k ≤ i, ∃ (hk_d : k < cfg.P.d) (Ψk : ℝ) (ck wk : ℕ → ℕ → ℝ),
          WeakHiddenStable (tr.H k hk_d).D (tr.H k hk_d).len Ψk ck wk ∧
          (∀ e' ∈ ((tr.snapC r₁).G k).E, wk (tr.lvlIdx r₁ k) e' = (tr.snapC r₁).chainW (wFn r₁) k e') ∧
          (∀ e' ∈ ((tr.snapC r₂).G k).E, wk (tr.lvlIdx r₂ k) e' = (tr.snapC r₂).chainW (wFn r₂) k e') := by
        intro k; induction k with
        | zero =>
          intro _; refine ⟨cfg.P.hd, cfg.Ψ, c0, w0, hWHS0, ?_, ?_⟩
          · intro e' _
            have ht1 : tPick s₁ = r₁ := by simp [tPick]
            change w_ext (tr.timeOfRound (tPick s₁)) (tr.snapI2E (tPick s₁) e') = wFn r₁ e'
            rw [ht1]
          · intro e' _
            have ht2 : tPick s₂ = r₂ := by simp [tPick, Nat.ne_of_gt h_lvl0_lt]
            change w_ext (tr.timeOfRound (tPick s₂)) (tr.snapI2E (tPick s₂) e') = wFn r₂ e'
            rw [ht2]
        | succ k ihk =>
          intro hk_le
          obtain ⟨hk_d, Ψk, ck, wk, hWHS_k, hw1_k, hw2_k⟩ := ihk (Nat.le_of_succ_le hk_le)
          have hk1_d : k + 1 < cfg.P.d := lt_of_le_of_lt hk_le hi
          let Hk := tr.H k hk_d; let Hk1 := tr.H (k + 1) hk1_d
          have hSpec_k := hV.hT cfg.P.k Hk.len (levelM cfg.TP cfg.P k) cfg.N₀ Hk.D Hk.restarts Ψk ck wk
            cfg.P.hk Hk.hG0 Hk.hD Hk.hLen hWHS_k Hk.hInitMBound Hk.hInitNBound Hk.hRestartsLt
            (by rw [Hk.hUpd]; exact Hk.hThresh)
          have hjb : st.chain.bran k < cfg.P.k := hInv.hBran k hk_d
          obtain ⟨Ψk1, hWHS_core⟩ := hSpec_k.2.2.2.2.1 Hk.s₀ Hk.len Hk.hs₀ (le_refl _) (st.chain.bran k)
            hjb Hk.hS0Fresh (fun r hr1 hr2 => Hk.hNoRestartAfterS0 r hr1 hr2)
          have hSucc := tr.hLvlSucc k hk1_d; have hCore := tr.hLvlCore k hk1_d
          let off := Hk.len - Hk1.len
          let off' := off - Hk.s₀
          have hoff_eq : off' + Hk1.len = Hk.len - Hk.s₀ := by
            have hS := hSucc.1; have hC := hCore.1
            dsimp only [off, off', Hk, Hk1] at hS hC ⊢; omega
          have hWHS_k1 : WeakHiddenStable Hk1.D Hk1.len Ψk1
              (fun δ => cfg.T.coreCFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                Hk.D Hk.restarts ck Hk.s₀ (st.chain.bran k) (off' + δ))
              (fun δ => cfg.T.coreWFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                Hk.D Hk.restarts wk Hk.s₀ (st.chain.bran k) (off' + δ)) :=
            weakHiddenStable_suffix hoff_eq hWHS_core hCore.2.1 hCore.2.2.1 hCore.2.2.2
          have hStepW : ∀ r, gSt.round ≥ r → r₁ ≤ r →
              (∀ e' ∈ ((tr.snapC r).G k).E, wk (tr.lvlIdx r k) e' = (tr.snapC r).chainW (wFn r) k e') →
              ∀ e' ∈ ((tr.snapC r).G (k + 1)).E,
                cfg.T.coreWFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ Hk.D Hk.restarts wk Hk.s₀ (st.chain.bran k)
                    (off' + tr.lvlIdx r (k + 1)) e' =
                  (tr.snapC r).chainW (wFn r) (k + 1) e' := by
            intro r hr_R hr1_r hw_r e' _
            have hrk1 : tr.reinit ⟨k + 1, Nat.lt_succ_of_le hk1_d.le⟩ ≤ r :=
              le_trans (hre_mono _ _ (Fin.le_iff_val_le_val.mpr (by simp; omega))) (le_trans hR1 hr1_r)
            have hrk : tr.reinit ⟨k, Nat.lt_succ_of_le hk_d.le⟩ ≤ r :=
              le_trans (hre_mono _ _ (Fin.le_iff_val_le_val.mpr (by simp))) hrk1
            have hidx : Hk.s₀ + (off' + tr.lvlIdx r (k + 1)) = tr.lvlIdx r k := by
              have := hCore.1; have hS := hSucc.2 r hrk1 hr_R
              dsimp only [off, off', Hk, Hk1] at hS ⊢; omega
            have hSnap_r := tr.hLvlSnap k hk_d r hrk hr_R
            have hBr : (tr.snapC r).bran k = st.chain.bran k :=
              tr.hSnapBran i hi.le r (le_trans hR1 hr1_r) hr_R k hk_le
            have hSr := tr.hSnapHolds r hr_R
            have hactL : (tr.snapC r).activeLSF k =
                cfg.T.lsfs (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                  Hk.D Hk.restarts (tr.lvlIdx r k))
                  (st.chain.bran k) := by
              simp only [TreeChain.activeLSF, hSr.1, hk_d, ↓reduceIte]; rw [hBr, hSnap_r.2.1 _ hjb]
            have hactE : (tr.snapC r).activeEmb k =
                cfg.T.emb (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                  Hk.D Hk.restarts (tr.lvlIdx r k))
                  (st.chain.bran k) := by
              simp only [TreeChain.activeEmb, hSr.1, hk_d, ↓reduceIte]
              rw [hBr, hSnap_r.2.2 (by convert hrk1) _ hjb]
            unfold SparseCoreRestartTool.coreWFrom TreeChain.chainW passSparseCoreW passCoreW
            rw [hidx]
            simp only [TreeChain.activeCore, hSnap_r.1, hactL, hactE]
            refine congrArg (2 * ·) (Finset.sum_congr rfl fun f hf => ?_)
            rw [hw_r f (by rw [hSnap_r.1]; exact (Finset.mem_sdiff.mp hf).1)]
          exact ⟨hk1_d, Ψk1, _, _, hWHS_k1, hStepW r₁ (le_trans hr1_hi hr2_hi) le_rfl hw1_k,
            hStepW r₂ hr2_hi hr1_hi hw2_k⟩
      obtain ⟨hk_d, Ψi, ci, wi, hWHS_i, hw1_i, hw2_i⟩ := hChainProp i (le_refl i)
      have he_H2 : e ∈ ((tr.H i hk_d).D.G (tr.lvlIdx r₂ i)).E := by
        rw [← (tr.hLvlSnap i hk_d r₂ hR2 hr2_hi).1]; exact he
      have he_C1 : e ∈ ((tr.snapC r₁).G i).E := by
        rw [(tr.hLvlSnap i hk_d r₁ hR1 (le_trans hr1_hi hr2_hi)).1]
        exact hNoIns_mem_pre (tr.H i hk_d).D h12_lvl h2_end (tr.H i hk_d).hD e he_H2 hNoIns
      have hWstep := (hWHS_i (tr.lvlIdx r₂ i) h2_end).2.2.1 e he_H2 (tr.lvlIdx r₁ i) h12_lvl hNoIns
      rwa [hw2_i e he, hw1_i e he_C1] at hWstep
  let ctx : RepQualityCtx :=
    { d := cfg.P.d, k := cfg.P.k
      γ_ℓ := cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2), γ_c := cfg.TP.γ_c (cfg.P.M₀ ^ 2)
      σ := σ_cap
      σ_mwu := max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀)
      t := R, C := tr.snapC, G0 := fun r => (tr.snapC r).G 0
      ℓ0 := ℓ0Fn, w := wFn, reinit := reinitFn, repT := repTFn
      hd := cfg.P.hd, hk := cfg.P.hk
      hγℓ := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2), hγc := hV.hTP.2.2.2.2.1 (cfg.P.M₀ ^ 2)
      hRep := hRep
      hWindow := fun i hi_le r hre_le hr => by
        have hSr := tr.hSnapHolds r hr; have hFr := tr.hSnapFresh r hr
        have htr : tr.timeOfRound r ≤ t :=
          le_trans (tr.hTimeMono r R hr (le_refl R)) (le_of_eq tr.hTimeEnd)
        have hHSr := hHS (tr.timeOfRound r) htr
        have hbr : ∀ b < i, (tr.snapC r).bran b = (tr.snapC R).bran b := fun b hb => by
          have hrr : tr.reinit ⟨i, Nat.lt_succ_of_le hi_le⟩ ≤ r := by
            simpa [reinitFn, mkFin, hi_le] using hre_le
          have hRR : tr.reinit ⟨i, Nat.lt_succ_of_le hi_le⟩ ≤ R := le_trans hrr hr
          rw [tr.hSnapBran i hi_le r hrr hr b hb, tr.hSnapBran i hi_le R hRR (le_refl R) b hb]
        refine ⟨hSr.1, hSr.2.1, hSr.2.2.1, hSr.2.2.2.1, fun e he =>
          ⟨le_of_lt (hHSr.2.2.2.2 (tr.snapI2E r e) (hFr.hRight e he).2).2.2.1,
           le_of_lt (hHSr.2.2.2.2 (tr.snapI2E r e) (hFr.hRight e he).2).1⟩, hbr, ?_⟩
        intro hi_lt hrep_le e he
        have hre_R : tr.reinit ⟨i, Nat.lt_succ_of_le hi_lt.le⟩ ≤ repTFn i := by
          simpa [repTFn, mkFin, hi_lt.le] using hRebRep ⟨i, Nat.lt_succ_of_le hi_lt.le⟩
        have hre_r := le_trans hre_R hrep_le
        have hrep_R : repTFn i ≤ R := (hRepB (mkFin i)).2
        set hHi := tr.H i hi_lt
        have hτ12 := tr.hLvlMono i hi_lt (repTFn i) r hre_R hrep_le hr
        have hτ2_end : tr.lvlIdx r i ≤ hHi.len := by
          rw [← tr.hLvlEnd i hi_lt]; exact tr.hLvlMono i hi_lt r R hre_r hr (le_refl R)
        have hBrR_lt : (tr.snapC R).bran i < cfg.P.k := by
          rw [tr.hSnapBran cfg.P.d (le_refl _) R (le_trans (tr.hRebRep _) (hRepB _).2) (le_refl R) i hi_lt]
          exact hInv.hBran i hi_lt
        have he_Hi : e ∈ (hHi.D.G (tr.lvlIdx r i)).E := by rwa [← (tr.hLvlSnap i hi_lt r hre_r hr).1]
        have hWstr := wstr_const_or_one_of_isSpec (SparseCoreRestartTool.IsSpecRestart.toNoHidden hV.hT)
          hHi.restarts cfg.P.hk hHi.hG0 hHi.hD hHi.hLen hHi.hℓPos hHi.hInitMBound hHi.hInitNBound
          hHi.hRestartsLt (by rw [hHi.hUpd]; exact hHi.hThresh)
          hBrR_lt hτ12 hτ2_end e he_Hi
        rcases hWstr with hOne | ⟨he_rep, hEq, hNoIns⟩
        · left; rwa [(tr.hLvlSnap i hi_lt r hre_r hr).2.1 _ hBrR_lt]
        · right
          refine ⟨by rwa [(tr.hLvlSnap i hi_lt (repTFn i) hre_R hrep_R).1], ?_, ?_⟩
          · rw [(tr.hLvlSnap i hi_lt r hre_r hr).2.1 _ hBrR_lt,
              (tr.hLvlSnap i hi_lt (repTFn i) hre_R hrep_R).2.1 _ hBrR_lt]
            exact hEq
          · exact hLvl_chainW hi_lt (by simpa [reinitFn, mkFin, hi_lt.le] using hre_R)
              hrep_le hr e he hNoIns }
  refine ⟨ctx, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r _ => ⟨rfl, rfl, rfl⟩, fun x => ?_⟩
  have hmk : mkFin x.val = x := Fin.ext (min_eq_left (Nat.le_of_lt_succ x.isLt))
  exact ⟨congrArg tr.reinit hmk, congrArg gSt.repT hmk⟩

/-- Specialization of `Alg2HiddenTraceAt.toRepQualityCtx` to `Alg2HiddenTrace`. -/
theorem Alg2HiddenTrace.toRepQualityCtx {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st : Alg2State cfg}
    (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain) :
    ∃ ctx : RepQualityCtx,
      ctx.d = cfg.P.d ∧ ctx.k = cfg.P.k ∧
      ctx.γ_ℓ = cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ∧ ctx.γ_c = cfg.TP.γ_c (cfg.P.M₀ ^ 2) ∧
      ctx.σ = alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀ ∧
      ctx.σ_mwu = max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀) ∧
      ctx.t = (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round ∧
      ctx.C = tr.snapC ∧
      (∀ r ≤ ctx.t, ctx.G0 r = (tr.snapC r).G 0 ∧
        ctx.ℓ0 r = (fun e' => D.ℓ (tr.timeOfRound r) (tr.snapI2E r e')) ∧
        ctx.w r = (fun e' => w_ext (tr.timeOfRound r) (tr.snapI2E r e'))) ∧
      (∀ i : Fin (cfg.P.d + 1),
        ctx.reinit i.val = tr.reinit i ∧
        ctx.repT i.val = (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).repT i) :=
  Alg2HiddenTraceAt.toRepQualityCtx hV tr hHS hInv

end Alg2HiddenTraceSection

end MinCostFlow.Chain
