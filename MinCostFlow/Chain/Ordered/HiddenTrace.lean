module

public import MinCostFlow.Chain.Ordered.Traces
public import MinCostFlow.Chain.Section6Quality

/-!
# Hidden-stable witness trace lemmas for Algorithm 2 with orders (Section 6.2)

This file ports the ordered hidden-trace lemmas of `MinCostFlow.Chain.HiddenTrace` to
`MinCostFlow.Chain.Ordered`:

* `alg2KappaAt_pos`, `alg2Kappa_pos`: positivity of the quality threshold under
  `Alg2Config.ValidOrdNoHidden`.
* `wstr_const_or_one_of_isSpec`: between stages `τ₁ ≤ τ₂` on an ordered run of
  `SparseCoreRestartTool`, every surviving edge either received an insertion (giving `wstr = 1`)
  or survived without insertion with unchanged `wstr`.
* `Alg2HiddenTraceAt.toRepQualityCtx`, `Alg2HiddenTrace.toRepQualityCtx`: construct
  `RepQualityCtx` from `Ordered.Alg2HiddenTraceAt` under `HiddenStableAt` and
  `Alg2Config.ValidOrd`, propagating `WeakHiddenStable` down active levels through
  `SparseCoreRestartTool.IsSpecOrdRestart` item 5.

Generic lemmas that do not mention ordered objects (`weightValid_norm1_of_hiddenStableAt`,
`freshInv_pullback_hiddenAt`, `chainW_mono`, `weakHiddenStable_suffix`, `corollary_6_4_of_lvl`)
are reused directly from `MinCostFlow.Chain`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section KappaAndWstr

lemma alg2KappaAt_pos {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden) (nLast : ℕ) :
    0 < alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast := by
  refine kappaBound_pos (hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)) ?_ (le_max_left _ _)
  exact le_trans zero_le_one (le_max_of_le_left (hV.hTP.1 cfg.P.k cfg.N₀ cfg.P.hk))

lemma alg2Kappa_pos {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden) :
    0 < alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
  alg2KappaAt_pos hV cfg.N₀

/-- Between `τ₁ ≤ τ₂ ≤ τ` on a valid ordered run of `T`, every surviving edge at `τ₂` either
received an insertion in `(τ₁, τ₂]` (and thus has `wstr = 1`) or survived without insertion since
`τ₁` (keeping the same `wstr` as at `τ₁`). -/
lemma wstr_const_or_one_of_isSpec {T : SparseCoreRestartTool} {P : SparseCoreParams}
    {Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop}
    (hT : T.IsSpecOrdRestartNoHiddenOn P Pred) {k τ M N : ℕ} {D : DynamicInstance}
    (hPred : Pred k τ M N D)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG0 : (D.G 0).IsValid) (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hℓPos : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hm₀ : (D.G 0).m ≤ M) (hn₀ : (D.G 0).n ≤ N)
    (hRest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hTh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    {j : ℕ} (hj : j < k) {τ₁ τ₂ : ℕ} (h12 : τ₁ ≤ τ₂) (h2 : τ₂ ≤ τ) :
    ∀ e ∈ (D.G τ₂).E,
      (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts τ₂) j).wstr e = 1 ∨
      (e ∈ (D.G τ₁).E ∧
        (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts τ₂) j).wstr e =
          (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts τ₁) j).wstr e ∧
        D.NotInsertedBetween e τ₁ τ₂) := by
  have hSpec := hT k τ M N D ord restarts hk hG0 hD hLen hℓPos hOrd hm₀ hn₀ hRest hTh hPred
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

end KappaAndWstr

section RepQualityBridge

/-- Construct `RepQualityCtx` from `Ordered.Alg2HiddenTraceAt` under `D.HiddenStableAt`, bridging
level-0 to level-`i` weights through `SparseCoreRestartTool.IsSpecOrdRestart` item 5. -/
theorem Alg2HiddenTraceAt.toRepQualityCtx {σ_cap : ℝ} {cfg : Alg2Config} (hV : cfg.ValidOrd)
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
          have hSpec_k := Hk.hOK cfg.P.k Hk.len (levelM cfg.TP cfg.P k) cfg.N₀ Hk.D Hk.ord Hk.restarts
            Ψk ck wk cfg.P.hk Hk.hG0 Hk.hD Hk.hLen hWHS_k Hk.hOrd Hk.hInitMBound Hk.hInitNBound
            Hk.hRestartsLt (by rw [Hk.hUpd]; exact Hk.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
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
              (fun δ => cfg.T.coreCOrdFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                Hk.D Hk.ord Hk.restarts ck Hk.s₀ (st.chain.bran k) (off' + δ))
              (fun δ => cfg.T.coreWOrdFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                Hk.D Hk.ord Hk.restarts wk Hk.s₀ (st.chain.bran k) (off' + δ)) :=
            weakHiddenStable_suffix hoff_eq hWHS_core hCore.2.1 hCore.2.2.1 hCore.2.2.2.1
          have hStepW : ∀ r, gSt.round ≥ r → r₁ ≤ r →
              (∀ e' ∈ ((tr.snapC r).G k).E, wk (tr.lvlIdx r k) e' = (tr.snapC r).chainW (wFn r) k e') →
              ∀ e' ∈ ((tr.snapC r).G (k + 1)).E,
                cfg.T.coreWOrdFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ Hk.D Hk.ord Hk.restarts wk
                    Hk.s₀ (st.chain.bran k) (off' + tr.lvlIdx r (k + 1)) e' =
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
                cfg.T.lsfs (cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                  Hk.D Hk.ord Hk.restarts (tr.lvlIdx r k))
                  (st.chain.bran k) := by
              simp only [TreeChain.activeLSF, hSr.1, hk_d, ↓reduceIte]; rw [hBr, hSnap_r.2.1 _ hjb]
            have hactE : (tr.snapC r).activeEmb k =
                cfg.T.emb (cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                  Hk.D Hk.ord Hk.restarts (tr.lvlIdx r k))
                  (st.chain.bran k) := by
              simp only [TreeChain.activeEmb, hSr.1, hk_d, ↓reduceIte]
              rw [hBr, hSnap_r.2.2 (by convert hrk1) _ hjb]
            unfold SparseCoreRestartTool.coreWOrdFrom TreeChain.chainW passSparseCoreW passCoreW
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
        have hWstr := wstr_const_or_one_of_isSpec hHi.hOK.noHidden ⟨rfl, rfl, rfl, rfl, rfl⟩
          hHi.ord hHi.restarts cfg.P.hk hHi.hG0 hHi.hD hHi.hLen hHi.hℓPos hHi.hOrd
          hHi.hInitMBound hHi.hInitNBound hHi.hRestartsLt (by rw [hHi.hUpd]; exact hHi.hThresh)
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
theorem Alg2HiddenTrace.toRepQualityCtx {cfg : Alg2Config} (hV : cfg.ValidOrd)
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

end RepQualityBridge

end MinCostFlow.Chain.Ordered
