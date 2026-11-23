module

public import MinCostFlow.Chain.HiddenTrace

/-!
# Trace transition steps for Lemma 6.5 (`Init`, `Detect`, `Shift`)

This file builds the transition lemmas maintaining `Alg2HiddenTrace`
(`MinCostFlow.Chain.HiddenTrace`) across `Init` (`t = 0`), `Detect` (`t → t + 1` with empty
batch), and each `Shift(i)` iteration of `algorithm2_loop`, together with Game prefix / weight
congruence helpers and explicit `LevelHistory` constructors (`zeroLevelHistory`,
`levelHistory_of_shift_le`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section Helpers

private lemma lsfHolds_mono {L : LSF} {G : MGraph} {ℓ : ℕ → ℝ} {σ σ' : ℝ}
    (h : L.Holds G ℓ σ) (hσ : σ ≤ σ') : L.Holds G ℓ σ' :=
  ⟨h.1, h.2.1, h.2.2.1, fun e he => ⟨(h.2.2.2 e he).1, le_trans (h.2.2.2 e he).2 hσ⟩⟩

lemma chainHolds_mono {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ' σ_mwu σ_mwu' γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hσ : σ ≤ σ') (hσm : σ_mwu ≤ σ_mwu') :
    C.Holds G ℓ σ' σ_mwu' γ_ℓ γ_c := by
  refine ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, fun i hi => ?_, hH.2.2.2.2.2.1, fun j hj => ?_, fun e he => ?_⟩
  · have hiH := hH.2.2.2.2.1 i hi
    refine ⟨hiH.1, fun j hj => ⟨lsfHolds_mono (hiH.2.1 j hj).1 hσ, (hiH.2.1 j hj).2⟩,
      fun e he => le_trans (hiH.2.2.1 e he) hσm, hiH.2.2.2⟩
  · exact lsfHolds_mono (hH.2.2.2.2.2.2.1 j hj) hσ
  · exact le_trans (hH.2.2.2.2.2.2.2 e he) hσm

lemma chainInv_last_le_N0 {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {s : ℕ} {ch : ChainState cfg.T cfg.P} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hn : (D.G s).n ≤ cfg.N₀) (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hF : FreshInv (D.G s) (ch.G 0) e2i i2e nf) : (ch.G cfg.P.d).n ≤ cfg.N₀ :=
  calc (ch.G cfg.P.d).n
      ≤ (ch.G 0).n := Finset.card_le_card
        ((level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hT hV.hγM₀ hV.hγk
          hInv cfg.P.d le_rfl).2.1)
    _ = (D.G s).n := hF.n_eq
    _ ≤ cfg.N₀ := hn

lemma chainState_snapHoldsAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {s : ℕ} {ch : ChainState cfg.T cfg.P}
    {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hF : FreshInv (D.G s) (ch.G 0) e2i i2e nf)
    (hℓ : ch.ℓ = fun e' => D.ℓ s (i2e e'))
    (hn : (D.G s).n ≤ cfg.N₀)
    (hnLast : (ch.G cfg.P.d).n ≤ nLast) :
    ch.toTreeChain.d = cfg.P.d ∧ ch.toTreeChain.k = cfg.P.k ∧
    ch.toTreeChain.Holds (ch.G 0) (fun e' => D.ℓ s (i2e e'))
      (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) ∧
    ch.toTreeChain.ForestsAreSubgraphs ∧
    ∀ i < cfg.P.d, ∀ e ∈ (ch.G i).E,
      (∑ j ∈ Finset.range cfg.P.k, (ch.toTreeChain.lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀ := by
  have hB := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hT hV.hγM₀ hV.hγk hInv
  have hTH := hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hT hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk
  have hn0 : (ch.G 0).n ≤ cfg.N₀ := by rw [hF.n_eq]; exact hn
  have hHolds_raw : ch.toTreeChain.Holds (ch.G 0) ch.ℓ
      (max (cfg.TP.σ cfg.P.k (ch.G 0).n) (cfg.LP.σ_last nLast))
      (max (cfg.σ_mwu (ch.G 0).n) (cfg.LP.σ_mwu (ch.G 0).n))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) := by
    refine ⟨hTH.1.1, hTH.1.2.1, hTH.1.2.2.1, hTH.1.2.2.2.1, ?_, hTH.1.2.2.2.2.2.1, ?_,
      hTH.1.2.2.2.2.2.2.2⟩
    · intro i hi
      refine ⟨hInv.hBran i hi, ?_, (hTH.1.2.2.2.2.1 i hi).2.2.1, (hTH.1.2.2.2.2.1 i hi).2.2.2⟩
      intro j hj
      have hij := (hB i (Nat.le_of_lt hi)).2.2.2.2 hi j hj
      exact ⟨LSF.Holds.mono_σ hij.1 (le_max_left _ _), hij.2.toNoSize⟩
    · intro j hj
      exact LSF.Holds.mono_σ (hInv.hLastHolds j hj)
        (le_trans (hV.hLP.2.1 _ _ hnLast) (le_max_right _ _))
  have hσ_le : max (cfg.TP.σ cfg.P.k (ch.G 0).n) (cfg.LP.σ_last nLast) ≤
      alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast :=
    max_le_max (hV.hTP.2.1 _ _ _ _ (le_refl _) hn0) (le_refl _)
  have hσm_le : max (cfg.σ_mwu (ch.G 0).n) (cfg.LP.σ_mwu (ch.G 0).n) ≤
      max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀) :=
    max_le_max (hV.hσ_mwu_mono _ _ hn0) (hV.hLP.2.2.2.1 _ _ hn0)
  have hHolds : ch.toTreeChain.Holds (ch.G 0) (fun e' => D.ℓ s (i2e e'))
      (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) := by
    rw [← hℓ]
    exact chainHolds_mono hHolds_raw hσ_le hσm_le
  have hSub : ch.toTreeChain.ForestsAreSubgraphs :=
    ch.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  refine ⟨rfl, rfl, hHolds, hSub, fun i hi e he => ?_⟩
  obtain ⟨H⟩ := hInv.hHist i hi
  have hm := hV.hMWU cfg.P.k H.len (levelM cfg.TP cfg.P i) cfg.N₀ H.D H.restarts cfg.P.hk
    H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
    (by rw [H.hUpd]; exact H.hThresh) H.len (le_refl _) e (H.hEndG ▸ he)
  have hni : (H.D.G H.len).n ≤ cfg.N₀ := by
    rw [H.hEndG]
    exact le_trans (Finset.card_le_card (hB i hi.le).2.1) hn0
  rw [← H.hRun] at hm
  exact le_trans hm (hV.hσ_mwu_mono _ _ hni)

lemma chainState_snapHolds {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {s : ℕ} {ch : ChainState cfg.T cfg.P}
    {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hF : FreshInv (D.G s) (ch.G 0) e2i i2e nf)
    (hℓ : ch.ℓ = fun e' => D.ℓ s (i2e e'))
    (hn : (D.G s).n ≤ cfg.N₀) :
    ch.toTreeChain.d = cfg.P.d ∧ ch.toTreeChain.k = cfg.P.k ∧
    ch.toTreeChain.Holds (ch.G 0) (fun e' => D.ℓ s (i2e e'))
      (alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀)
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) ∧
    ch.toTreeChain.ForestsAreSubgraphs ∧
    ∀ i < cfg.P.d, ∀ e ∈ (ch.G i).E,
      (∑ j ∈ Finset.range cfg.P.k, (ch.toTreeChain.lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀ :=
  chainState_snapHoldsAt cfg.N₀ hV hInv hF hℓ hn (chainInv_last_le_N0 hV hn hInv hF)

lemma chain_validStretch_hstr {σ_cap : ℝ} {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {C : TreeChain} {ℓ w : ℕ → ℝ}
    (hC_d : C.d = cfg.P.d) (hC_k : C.k = cfg.P.k)
    (hHolds : C.Holds (C.G 0) ℓ σ_cap
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)))
    (hSub : C.ForestsAreSubgraphs)
    (hMWU : ∀ i < cfg.P.d, ∀ e ∈ (C.G i).E,
      (∑ j ∈ Finset.range cfg.P.k, (C.lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀)
    (hℓ_nn : ∀ e ∈ (C.G 0).E, 0 ≤ ℓ e) (hw_nn : ∀ e ∈ (C.G 0).E, 0 ≤ w e) :
    ∀ i : Fin (cfg.P.d + 1),
      let str_i : Fin cfg.P.k → ℝ := fun j =>
        if _hi : i.val < cfg.P.d then hstrAt C w i.val j.val else 0
      (∀ j, 0 ≤ str_i j) ∧ Game.ValidStretch cfg.gameParams.σ str_i := by
  intro i
  dsimp only
  by_cases hi : i.val < cfg.P.d
  · refine ⟨fun j => ?_, ?_⟩
    · simp only [hi, ↓reduceDIte]
      exact hstrAt_nonneg hHolds hSub hℓ_nn hw_nn (by rw [hC_d]; exact hi) (by rw [hC_k]; exact j.isLt)
    · have hcor := corollary_6_4_of_lvl hHolds hSub hℓ_nn hw_nn hV.hσ_mwu_nn (by rw [hC_d]; exact hi)
        (by rw [hC_k]; exact hMWU i.val hi)
      obtain ⟨j, hj, hle⟩ := hcor.2
      refine ⟨⟨j, by rw [← hC_k]; exact hj⟩, ?_⟩
      simp only [hi, ↓reduceDIte]
      exact le_trans hle (le_max_right 0 (cfg.σ_mwu cfg.N₀))
  · refine ⟨fun j => by simp [hi], ⟨⟨0, cfg.P.hk⟩, ?_⟩⟩
    simp [hi, Alg2Config.gameParams, alg2SigmaGame]

lemma chainW_congr {C₁ C₂ : TreeChain} (w : ℕ → ℝ) (k : ℕ)
    (hG : ∀ m ≤ k, C₁.G m = C₂.G m)
    (hL : ∀ m < k, C₁.activeLSF m = C₂.activeLSF m)
    (hE : ∀ m < k, C₁.activeEmb m = C₂.activeEmb m) :
    C₁.chainW w k = C₂.chainW w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext e
    have ihk := ih (fun m hm => hG m (Nat.le_succ_of_le hm))
      (fun m hm => hL m (Nat.lt_succ_of_lt hm))
      (fun m hm => hE m (Nat.lt_succ_of_lt hm))
    unfold TreeChain.chainW passSparseCoreW passCoreW TreeChain.activeCore
    rw [hG k (Nat.le_succ _), hL k (Nat.lt_succ_self _), hE k (Nat.lt_succ_self _), ihk]

lemma hstrAt_congr {C₁ C₂ : TreeChain} (w : ℕ → ℝ) {k l : ℕ}
    (hG : ∀ m ≤ k, C₁.G m = C₂.G m)
    (hL : ∀ m < k, C₁.activeLSF m = C₂.activeLSF m)
    (hE : ∀ m < k, C₁.activeEmb m = C₂.activeEmb m)
    (hLsf : C₁.lsfs k l = C₂.lsfs k l) :
    hstrAt C₁ w k l = hstrAt C₂ w k l := by
  unfold hstrAt
  rw [hG k (le_refl _), hLsf, chainW_congr w k hG hL hE]

end Helpers

section GamePrefixHelpers

open Game

lemma stateAt_append_left {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (ms₁ ms₂ : List (Move d k)) :
    ∀ s ≤ ms₁.length, stateAt W hk initStr (ms₁ ++ ms₂) s = stateAt W hk initStr ms₁ s := by
  intro s hs
  induction s with
  | zero => rfl
  | succ s ih =>
    have hslt : s < ms₁.length := hs
    rw [stateAt_succ W hk initStr (ms₁ ++ ms₂) (by simp; omega),
      stateAt_succ W hk initStr ms₁ hslt, ih (Nat.le_of_succ_le hs), List.getElem_append_left hslt]

lemma passesAt_append_left {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (ms₁ ms₂ : List (Move d k)) :
    ∀ s ≤ ms₁.length, passesAt W hk initStr (ms₁ ++ ms₂) s = passesAt W hk initStr ms₁ s := by
  intro s hs
  induction s with
  | zero => rfl
  | succ s ih =>
    have hslt : s < ms₁.length := hs
    rw [passesAt_succ W hk initStr (ms₁ ++ ms₂) (by simp; omega),
      passesAt_succ W hk initStr ms₁ hslt, ih (Nat.le_of_succ_le hs),
      stateAt_append_left W hk initStr ms₁ ms₂ s (Nat.le_of_succ_le hs),
      List.getElem_append_left hslt]

lemma argminAux_congr_W (W₁ W₂ : ℕ → ℝ) (lo rem : ℕ)
    (hW : ∀ x, lo ≤ x → x ≤ lo + rem → W₁ x = W₂ x) :
    argminAux W₁ lo rem = argminAux W₂ lo rem := by
  induction rem with
  | zero => rfl
  | succ rem ih =>
    simp only [argminAux]
    have hrec := ih fun x h1 h2 => hW x h1 (by omega)
    have hbd := argminRound_bounds W₂ (show lo ≤ lo + rem by omega)
    rw [argminRound] at hbd
    have hEq := hrec
    have hW1 : W₁ (lo + rem + 1) = W₂ (lo + rem + 1) := hW _ (by omega) (by omega)
    have hW2 : W₁ (argminAux W₂ lo rem) = W₂ (argminAux W₂ lo rem) := by
      have : lo ≤ argminAux W₂ lo rem ∧ argminAux W₂ lo rem ≤ lo + rem := by
        simpa [Nat.add_sub_cancel_left] using hbd
      exact hW _ this.1 (by omega)
    rw [hEq, hW1, hW2]

lemma stateAt_W_congr {d k : ℕ} (W₁ W₂ : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (ms : List (Move d k))
    (s : ℕ) (hW : ∀ r ≤ (stateAt W₁ hk initStr ms s).round, W₁ r = W₂ r) :
    stateAt W₁ hk initStr ms s = stateAt W₂ hk initStr ms s ∧
    passesAt W₁ hk initStr ms s = passesAt W₂ hk initStr ms s := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ s ih =>
    have hs_le : (stateAt W₁ hk initStr ms s).round ≤ (stateAt W₁ hk initStr ms (s + 1)).round :=
      round_mono W₁ hk initStr ms (Nat.le_succ s)
    obtain ⟨ihS, ihP⟩ := ih fun r hr => hW r (le_trans hr hs_le)
    by_cases hlt : s < ms.length
    · rw [stateAt_succ W₁ hk initStr ms hlt, stateAt_succ W₂ hk initStr ms hlt,
        passesAt_succ W₁ hk initStr ms hlt, passesAt_succ W₂ hk initStr ms hlt, ← ihS, ← ihP]
      cases hm : ms[s] with
      | advDoNothing => simp [stepState, stepPasses]
      | advRebuild i newStr => simp [stepState, stepPasses]
      | roundStep adv player newStr =>
        have hstep : stepState W₁ hk (stateAt W₁ hk initStr ms s) (.roundStep adv player newStr) =
            stepState W₂ hk (stateAt W₁ hk initStr ms s) (.roundStep adv player newStr) := by
          cases player with
          | doNothing => simp [stepState]
          | shift i =>
            have hrep := (repT_bounds W₁ hk initStr ms s i).2
            have hargmin : argminRound W₁ ((stateAt W₁ hk initStr ms s).repT i)
                  (stateAt W₁ hk initStr ms s).round =
                argminRound W₂ ((stateAt W₁ hk initStr ms s).repT i)
                  (stateAt W₁ hk initStr ms s).round := by
              unfold argminRound
              refine argminAux_congr_W W₁ W₂ _ _ fun x hx1 hx2 =>
                hW x (le_trans (by omega) hs_le)
            simp only [stepState, hargmin]
        exact ⟨hstep, rfl⟩
    · simp only [stateAt, passesAt]
      rw [List.getElem?_eq_none (not_lt.mp hlt)]
      exact ⟨ihS, ihP⟩

lemma validStep_W_congr {params : GameParams} (W₁ W₂ : ℕ → ℝ)
    (st : GameState params.d params.k) (m : Move params.d params.k)
    (hrep : ∀ i, st.repT i ≤ st.round) (hW : ∀ r ≤ st.round, W₁ r = W₂ r) :
    ValidStep params W₁ st m ↔ ValidStep params W₂ st m := by
  have hWr := hW st.round (le_refl _)
  cases hph : st.phase with
  | stage2 => cases m <;> simp [ValidStep, hph, hWr]
  | stage34 =>
    cases m with
    | advDoNothing => simp [ValidStep, hph]
    | advRebuild _ _ => simp [ValidStep, hph]
    | roundStep adv player newStr =>
      have hLoss : LossSumCond W₁ st ↔ LossSumCond W₂ st := by
        unfold LossSumCond
        rw [hWr]
        have hsum : (∑ i : Fin (params.d + 1), W₁ (st.repT i)) =
            ∑ i : Fin (params.d + 1), W₂ (st.repT i) :=
          Finset.sum_congr rfl fun i _ => hW (st.repT i) (hrep i)
        rw [hsum]
      simp [ValidStep, hph, hLoss]

lemma validPlayPrefix_W_congr {params : GameParams} (W₁ W₂ : ℕ → ℝ)
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {ms : List (Move params.d params.k)}
    (hW : ∀ r ≤ (stateAt W₁ params.hk initStr ms ms.length).round, W₁ r = W₂ r)
    (hv : ValidPlayPrefix params W₁ initStr ms) :
    ValidPlayPrefix params W₂ initStr ms := by
  refine ⟨hv.1, fun s hs => ?_⟩
  have hrm := round_mono W₁ params.hk initStr ms (le_of_lt hs)
  have hsc := (stateAt_W_congr W₁ W₂ params.hk initStr ms s fun r hr => hW r (le_trans hr hrm)).1
  rw [← hsc]
  exact (validStep_W_congr W₁ W₂ _ ms[s] (fun i => (repT_bounds W₁ params.hk initStr ms s i).2)
    (fun r hr => hW r (le_trans hr hrm))).mp (hv.2 s hs)

lemma followsStrategyPrefix_W_congr {params : GameParams} (W₁ W₂ : ℕ → ℝ)
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {ms : List (Move params.d params.k)}
    (hW : ∀ r ≤ (stateAt W₁ params.hk initStr ms ms.length).round, W₁ r = W₂ r)
    (hf : FollowsStrategyPrefix params W₁ initStr ms) :
    FollowsStrategyPrefix params W₂ initStr ms := by
  intro s hs
  have hrm := round_mono W₁ params.hk initStr ms (le_of_lt hs)
  have hc := stateAt_W_congr W₁ W₂ params.hk initStr ms s fun r hr => hW r (le_trans hr hrm)
  rw [← hc.1, ← hc.2]
  exact hf s hs

lemma validPlayPrefix_snoc {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {ms : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr ms) (m : Move params.d params.k)
    (hm : ValidStep params W (stateAt W params.hk initStr ms ms.length) m) :
    ValidPlayPrefix params W initStr (ms ++ [m]) := by
  refine ⟨hv.1, fun s hs => ?_⟩
  simp only [List.length_append, List.length_singleton] at hs
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs' | rfl
  · rw [stateAt_append_left W params.hk initStr ms [m] s (le_of_lt hs'), List.getElem_append_left hs']
    exact hv.2 s hs'
  · rw [stateAt_append_left W params.hk initStr ms [m] ms.length (le_refl _),
      List.getElem_append_right (le_refl _)]
    simpa using hm

lemma followsStrategyPrefix_snoc {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {ms : List (Move params.d params.k)}
    (hf : FollowsStrategyPrefix params W initStr ms) (m : Move params.d params.k)
    (hm : StrategyStep params (stateAt W params.hk initStr ms ms.length)
      (passesAt W params.hk initStr ms ms.length) m) :
    FollowsStrategyPrefix params W initStr (ms ++ [m]) := by
  intro s hs
  simp only [List.length_append, List.length_singleton] at hs
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs' | rfl
  · rw [stateAt_append_left W params.hk initStr ms [m] s (le_of_lt hs'),
      passesAt_append_left W params.hk initStr ms [m] s (le_of_lt hs'),
      List.getElem_append_left hs']
    exact hf s hs'
  · rw [stateAt_append_left W params.hk initStr ms [m] ms.length (le_refl _),
      passesAt_append_left W params.hk initStr ms [m] ms.length (le_refl _),
      List.getElem_append_right (le_refl _)]
    simpa using hm

end GamePrefixHelpers

section LevelHistoryHelpers

/-- Explicit `0`-step `LevelHistory` at level `i < P.d` when level `i` was just initialized/rebuilt. -/
noncomputable def zeroLevelHistory (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (N₀ : ℕ) (st : ChainState T P) (i : ℕ) (_hi : i < P.d)
    (_hTP : TP.Valid)
    (hGValid : (st.G i).IsValid)
    (hGm : ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ))
    (hGn : (st.G i).n ≤ N₀)
    (hℓPos : ∀ e ∈ (st.G i).E, 0 < st.toTreeChain.chainLen st.ℓ i e)
    (hInit : st.scState i = T.init P.k (levelM TP P i) N₀ (st.G i)
      (st.toTreeChain.chainLen st.ℓ i) (st.toTreeChain.chainGrad st.g i))
    (hUpd : st.updCount i = 0) (hCurFwd : st.curFwd i = 0)
    (hDec : st.curDecUpdates i = 0) (hRestarts : st.curRestarts i = 0)
    (hEnc0 : i = 0 → st.curEnc 0 = 0)
    (hEncNext : i + 1 < P.d → st.curEnc (i + 1) = 0) :
    LevelHistory T TP P N₀ st i :=
  let D : DynamicInstance :=
    { G := fun _ => st.G i, U := fun _ => [],
      ℓ := fun _ => st.toTreeChain.chainLen st.ℓ i, g := fun _ => st.toTreeChain.chainGrad st.g i }
  { D := D, len := 0, s₀ := 0, hs₀ := le_refl 0,
    restarts := fun _ => [],
    hRestartsLt := fun _ _ _ h => absurd h (List.not_mem_nil),
    hRestartsCount := by simp [hRestarts],
    hS0Fresh := Or.inl rfl,
    hNoRestartAfterS0 := fun _ _ _ h => absurd h (List.not_mem_nil),
    hG0 := hGValid, hD := fun _ ht1 ht2 => by omega, hLen := fun _ ht1 ht2 => by omega,
    hℓPos := fun _ _ e he => hℓPos e he,
    hEndG := rfl, hEndℓ := fun _ _ => rfl, hEndg := rfl,
    hUpd := by simp [hUpd], hThresh := by rw [hUpd]; simp [updateThreshold_nonneg],
    hInitMBound := by exact_mod_cast hGm,
    hInitNBound := hGn,
    hRun := by
      simp only [SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
        List.foldl_nil]
      exact hInit,
    branchSeq := fun _ => 0, hBranch := fun _ => P.hk,
    hBranchTail := fun _ hs1 hs2 => by omega,
    hWinFwdBound := by simp,
    hCurFwdEq := by simp [hCurFwd],
    hDecEq := by
      rw [hInit]
      simp [hDec, SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate, D],
    hEnc0Le := fun h0 => by simp [hEnc0 h0], hEncLe := fun h1 => by simp [hEncNext h1] }

/-- Preserve `H` (keeping exact `.D` and `.len`, resetting `s₀` and appending restart at `i₀`)
across `algorithm1_shift`. -/
noncomputable def levelHistory_of_shift_le {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ} {ch ch' : ChainState T P} {i₀ k : ℕ} (_hk : k < P.d) (hki : k ≤ i₀)
    (H : LevelHistory T TP P N₀ ch k)
    (hG : ∀ j ≤ k, ch'.G j = ch.G j)
    (hSuf_sc : if k = i₀ then ch'.scState k = T.restart (ch.scState k) (ch'.bran k)
      else ch'.scState k = ch.scState k)
    (hAct : ∀ j < k, ch'.toTreeChain.activeLSF j = ch.toTreeChain.activeLSF j)
    (hℓ : ch'.ℓ = ch.ℓ) (hg : ch'.g = ch.g)
    (hUpd : ch'.updCount k = ch.updCount k)
    (hCurFwd : ch'.curFwd k = ch.curFwd k)
    (hCurFwdBd : (ch.curFwd k : ℝ) ≤ TP.γ_r (P.M₀ ^ 2) * (ch.updCount k : ℝ))
    (hBrLtK : ch'.bran k < P.k)
    (hBrLt : k < i₀ → ch'.bran k = ch.bran k)
    (hDec : k = i₀ → ch'.curDecUpdates k = 0)
    (hDecLt : k < i₀ → ch'.curDecUpdates k = ch.curDecUpdates k)
    (hRestarts : ch'.curRestarts k = if k = i₀ then ch.curRestarts k + 1 else ch.curRestarts k)
    (hEnc0 : k = 0 → ch'.curEnc 0 = ch.curEnc 0)
    (hEncNext : k + 1 < P.d → k + 1 ≤ i₀ → ch'.curEnc (k + 1) = ch.curEnc (k + 1))
    (hEncNextGt : k + 1 < P.d → i₀ < k + 1 → ch'.curEnc (k + 1) = 0) :
    LevelHistory T TP P N₀ ch' k :=
  let restarts' : ℕ → List ℕ := fun r =>
    if k = i₀ ∧ r = H.len then H.restarts H.len ++ [ch'.bran k] else H.restarts r
  have hRunPre : ∀ s ≤ H.len,
      T.runAfterUpdate P.k (levelM TP P k) N₀ H.D restarts' s =
        T.runAfterUpdate P.k (levelM TP P k) N₀ H.D H.restarts s := fun s hs =>
    T.runAfterUpdate_congr_lt P.k (levelM TP P k) N₀ s rfl rfl rfl (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
      (fun r hr => by simp [restarts', show ¬ (k = i₀ ∧ r = H.len) by omega])
  { D := H.D, len := H.len
    s₀ := if k = i₀ then H.len else H.s₀
    hs₀ := by split_ifs <;> [exact le_refl _; exact H.hs₀]
    restarts := restarts',
    hRestartsLt := fun r hr b hb => by
      dsimp only [restarts'] at hb
      split_ifs at hb with hcond
      · simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · rw [hcond.2] at hr
          exact H.hRestartsLt _ hr b hb
        · exact hBrLtK
      · exact H.hRestartsLt r hr b hb
    hRestartsCount := by
      by_cases heq : k = i₀
      · subst heq
        rw [Finset.sum_range_succ]
        have hPreSum : (Finset.range H.len).sum (fun r => (restarts' r).length) =
            (Finset.range H.len).sum (fun r => (H.restarts r).length) :=
          Finset.sum_congr rfl fun r hr => by
            simp [restarts', Nat.ne_of_lt (Finset.mem_range.mp hr)]
        have hLast : (restarts' H.len).length = (H.restarts H.len).length + 1 := by
          simp [restarts']
        rw [hPreSum, hLast, ← add_assoc, ← Finset.sum_range_succ, H.hRestartsCount, hRestarts]
        simp
      · have hPreSum : (Finset.range (H.len + 1)).sum (fun r => (restarts' r).length) =
            (Finset.range (H.len + 1)).sum (fun r => (H.restarts r).length) :=
          Finset.sum_congr rfl fun r _ => by simp [restarts', heq]
        rw [hPreSum, H.hRestartsCount, hRestarts]
        simp [heq]
    hS0Fresh := by
      by_cases heq : k = i₀
      · right; simp [restarts', heq]
      · simp only [heq, ↓reduceIte, restarts', false_and]
        rw [hBrLt (lt_of_le_of_ne hki heq)]
        exact H.hS0Fresh
    hNoRestartAfterS0 := fun r hr1 hr2 => by
      by_cases heq : k = i₀
      · subst heq; simp only [↓reduceIte] at hr1; omega
      · simp only [heq, ↓reduceIte] at hr1
        simp only [restarts', heq, false_and, ↓reduceIte]
        rw [hBrLt (lt_of_le_of_ne hki heq)]
        exact H.hNoRestartAfterS0 r hr1 hr2
    hG0 := H.hG0, hD := H.hD, hLen := H.hLen, hℓPos := H.hℓPos,
    hEndG := by rw [hG k (le_refl _)]; exact H.hEndG,
    hEndℓ := fun e he => by
      have he' : e ∈ (ch.G k).E := by rwa [← hG k (le_refl _)]
      have hCL := chainLen_congr_lt (C₁ := ch'.toTreeChain) (C₂ := ch.toTreeChain) ch.ℓ k
        (fun j hj => hG j hj.le) hAct
      change H.D.ℓ H.len e = ch'.toTreeChain.chainLen ch'.ℓ k e
      rw [hℓ, hCL]; exact H.hEndℓ e he',
    hEndg := by
      have hCG := chainGrad_congr_lt (C₁ := ch'.toTreeChain) (C₂ := ch.toTreeChain) ch.g k
        (fun j hj => hG j hj.le) hAct
      change H.D.g H.len = ch'.toTreeChain.chainGrad ch'.g k
      rw [hg, hCG]; exact H.hEndg,
    hUpd := by rw [hUpd]; exact H.hUpd,
    hThresh := by rw [hUpd]; exact H.hThresh,
    hInitMBound := H.hInitMBound,
    hInitNBound := H.hInitNBound,
    hRun := by
      by_cases heq : k = i₀
      · subst heq
        simp only [↓reduceIte] at hSuf_sc
        symm
        unfold SparseCoreRestartTool.runAfterRestarts
        rw [hRunPre H.len (le_refl _)]
        simp only [restarts', ↓reduceIte, and_self, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        change T.restart (T.runAfterRestarts P.k (levelM TP P k) N₀ H.D H.restarts H.len) (ch'.bran k) = ch'.scState k
        rw [← H.hRun, hSuf_sc]
      · simp only [heq, ↓reduceIte] at hSuf_sc
        have hPostEq : T.runAfterRestarts P.k (levelM TP P k) N₀ H.D restarts' H.len =
            T.runAfterRestarts P.k (levelM TP P k) N₀ H.D H.restarts H.len :=
          T.runAfterRestarts_congr_le P.k (levelM TP P k) N₀ H.len rfl rfl rfl (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
            (fun r _ => by simp [restarts', heq])
        rw [hPostEq, hSuf_sc]; exact H.hRun,
    branchSeq := H.branchSeq,
    hBranch := H.hBranch,
    hBranchTail := fun s hs1 hs2 => by
      by_cases heq : k = i₀
      · subst heq; simp only [↓reduceIte] at hs1; omega
      · simp only [heq, ↓reduceIte] at hs1
        rw [hBrLt (lt_of_le_of_ne hki heq)]
        exact H.hBranchTail s hs1 hs2,
    hWinFwdBound := by
      by_cases heq : k = i₀
      · subst heq
        simp only [↓reduceIte]
        have hsub : (Finset.Icc 1 H.len).sum (fun s =>
              ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D restarts' s).2 (H.branchSeq s)).length) =
            (Finset.Icc 1 H.len).sum (fun s =>
              ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D H.restarts s).2 (H.branchSeq s)).length) :=
          Finset.sum_congr rfl fun s hs => by rw [hRunPre s (Finset.mem_Icc.mp hs).2]
        rw [hsub, ← H.hCurFwdEq, H.hUpd]
        exact hCurFwdBd
      · simp only [heq, ↓reduceIte]
        have hsub : (Finset.Icc 1 H.s₀).sum (fun s =>
              ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D restarts' s).2 (H.branchSeq s)).length) =
            (Finset.Icc 1 H.s₀).sum (fun s =>
              ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D H.restarts s).2 (H.branchSeq s)).length) :=
          Finset.sum_congr rfl fun s hs => by
            rw [hRunPre s (le_trans (Finset.mem_Icc.mp hs).2 H.hs₀)]
        rw [hsub]
        exact H.hWinFwdBound,
    hCurFwdEq := by
      rw [hCurFwd, H.hCurFwdEq]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hRunPre s (Finset.mem_Icc.mp hs).2],
    hDecEq := by
      by_cases heq : k = i₀
      · subst heq
        have hPost : T.runAfterRestarts P.k (levelM TP P k) N₀ H.D restarts' (if k = k then H.len else H.s₀) =
            ch'.scState k := by
          simp only [↓reduceIte] at hSuf_sc ⊢
          unfold SparseCoreRestartTool.runAfterRestarts
          rw [hRunPre H.len (le_refl _)]
          simp only [restarts', ↓reduceIte, and_self, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
          change T.restart (T.runAfterRestarts P.k (levelM TP P k) N₀ H.D H.restarts H.len) (ch'.bran k) = ch'.scState k
          rw [← H.hRun, hSuf_sc]
        simp only [↓reduceIte, hDec rfl, zero_add]
        rw [← hPost]
        simp only [↓reduceIte]
      · have hlt : k < i₀ := Nat.lt_of_le_of_ne hki heq
        simp only [heq, ↓reduceIte] at hSuf_sc ⊢
        have hPostEq : T.runAfterRestarts P.k (levelM TP P k) N₀ H.D restarts' H.s₀ =
            T.runAfterRestarts P.k (levelM TP P k) N₀ H.D H.restarts H.s₀ :=
          T.runAfterRestarts_congr_le P.k (levelM TP P k) N₀ H.s₀ rfl rfl rfl (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
            (fun r _ => by simp [restarts', heq])
        change ch'.curDecUpdates k + (T.lsfs (ch'.scState k) (ch'.bran k)).F.F.E.card =
          (T.lsfs (T.runAfterRestarts P.k (levelM TP P k) N₀ H.D restarts' H.s₀) (ch'.bran k)).F.F.E.card
        rw [hDecLt hlt, hSuf_sc, hBrLt hlt, hPostEq]
        exact H.hDecEq,
    hEnc0Le := fun h0 => by rw [hEnc0 h0]; exact H.hEnc0Le h0,
    hEncLe := fun h1 => by
      by_cases hle : k + 1 ≤ i₀
      · have hne : k ≠ i₀ := by omega
        have hlt : k < i₀ := by omega
        change ch'.curEnc (k + 1) ≤ (Finset.Icc ((if k = i₀ then H.len else H.s₀) + 1) H.len).sum fun s =>
          (T.S (T.runAfterRestarts P.k (levelM TP P k) N₀ H.D restarts' (s - 1)) (ch'.bran k)).batchEnc
            ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D restarts' s).2 (ch'.bran k))
        simp only [hne, ↓reduceIte, hEncNext h1 hle, hBrLt hlt]
        have hSumEq : (Finset.Icc (H.s₀ + 1) H.len).sum (fun s =>
              (T.S (T.runAfterRestarts P.k (levelM TP P k) N₀ H.D restarts' (s - 1)) (ch.bran k)).batchEnc
                ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D restarts' s).2 (ch.bran k))) =
            (Finset.Icc (H.s₀ + 1) H.len).sum (fun s =>
              (T.S (T.runAfterRestarts P.k (levelM TP P k) N₀ H.D H.restarts (s - 1)) (ch.bran k)).batchEnc
                ((T.runAfterUpdate P.k (levelM TP P k) N₀ H.D H.restarts s).2 (ch.bran k))) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          rcases Finset.mem_Icc.mp hs with ⟨_, hs2⟩
          have hPostPre := T.runAfterRestarts_congr_le (D₁ := H.D) (D₂ := H.D)
            (restarts₁ := restarts') (restarts₂ := H.restarts) P.k (levelM TP P k) N₀ (s - 1) rfl rfl rfl
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun r _ => by simp [restarts', hne])
          rw [hPostPre, hRunPre s hs2]
        rw [hSumEq]
        exact H.hEncLe h1
      · simp [hEncNextGt h1 (by omega)] }

end LevelHistoryHelpers

section InitDetectShift

/-- **Init step**: construct `Alg2HiddenTraceAt` at `t = 0` after `algorithm2_init`, parameterized by
last-level vertex cap `nLast`. -/
theorem alg2HiddenTrace_initAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hm0 : (D.G 0).m ≤ cfg.P.M₀) (hn0 : (D.G 0).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G 0) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ nLast)
    {c_ext w_ext : ℕ → ℕ → ℝ} (hHS0 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext 0) :
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext 0
      (algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0))) := by
  classical
  set st₀ := algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0)
  have hG0Valid := (hHist.2.1 0 (Nat.zero_le _)).1
  have hℓ0 := (hHist.2.1 0 (Nat.zero_le _)).2
  have hInit := initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk (D.G 0) (D.ℓ 0) (D.g 0) hG0Valid hm0 hn0 hℓ0
  have hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st₀.chain := hInit.1
  have hG0eq : st₀.chain.G 0 = D.G 0 := hInit.2.2.1
  have hFresh : FreshInv (D.G 0) (st₀.chain.G 0) st₀.extToInt st₀.intToExt st₀.nextFresh := by
    change FreshInv (D.G 0) (st₀.chain.G 0) id id ((D.G 0).E.sup id + 1)
    rw [hG0eq]; exact freshInv_init (D.G 0)
  have hSH := chainState_snapHoldsAt nLast hV hInv hFresh rfl hn0 (hLastBound hInv hFresh)
  have hℓ0_nn : ∀ e ∈ (st₀.chain.G 0).E, 0 ≤ D.ℓ 0 (st₀.intToExt e) := fun e he => by
    rw [hG0eq] at he; exact (hℓ0 e he).le
  have hw0_nn : ∀ e ∈ (st₀.chain.G 0).E, 0 ≤ w_ext 0 (st₀.intToExt e) := fun e he => by
    rw [hG0eq] at he; exact (hHS0.2.2.2.2 e he).1.le
  have hInitStr := chain_validStretch_hstr hV hSH.1 hSH.2.1 hSH.2.2.1 hSH.2.2.2.1 hSH.2.2.2.2
    hℓ0_nn hw0_nn
  let initStr : Fin (cfg.P.d + 1) → Fin cfg.P.k → ℝ := fun i j =>
    if _hi : i.val < cfg.P.d then
      hstrAt st₀.chain.toTreeChain (fun e' => w_ext 0 (st₀.intToExt e')) i.val j.val
    else 0
  let W₀ : ℕ → ℝ := fun _ => (D.G 0).norm1 (w_ext 0)
  have hWV : Game.WeightValid cfg.gameParams.Ψ (W₀ 1) :=
    weightValid_norm1_of_hiddenStableAt hV.hα hm0 hHS0
  let moves₀ : List (Game.Move cfg.P.d cfg.P.k) := [.advDoNothing]
  have hv₀ : Game.ValidPlayPrefix cfg.gameParams W₀ initStr moves₀ := by
    refine ⟨⟨fun i j => (hInitStr i).1 j, fun i => (hInitStr i).2⟩, fun s hs => ?_⟩
    have hs0 : s = 0 := Nat.lt_one_iff.mp hs; subst hs0
    simpa [Game.ValidStep, Game.stateAt, Game.initState, moves₀] using ⟨hWV, trivial⟩
  have hf₀ : Game.FollowsStrategyPrefix cfg.gameParams W₀ initStr moves₀ := fun s hs => by
    have hs0 : s = 0 := Nat.lt_one_iff.mp hs; subst hs0
    simp [Game.StrategyStep, Game.stateAt, Game.initState]
  have hRS := rebuildSuffix_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hLP hV.hT hV.hL
    hV.hγM₀ hV.hγk (D.ℓ 0) (D.g 0) cfg.P.d 0 (fun _ => D.G 0)
    (fun _ => cfg.T.init cfg.P.k (levelM cfg.TP cfg.P 0) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (zero_add cfg.P.d) hG0Valid (Finset.Subset.refl _) hn0
    (by
      have hm0r : ((D.G 0).m : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast hm0
      have hγ1 := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
      have hmul : (cfg.P.M₀ : ℝ) ≤ (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
        nlinarith [show (0 : ℝ) ≤ cfg.P.M₀ from Nat.cast_nonneg _]
      have hceil : (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
          (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / cfg.P.k) ^ 0 ≤ (levelM cfg.TP cfg.P 0 : ℝ) := Nat.le_ceil _
      simp only [pow_zero, mul_one] at hceil
      linarith) hℓ0
  let res0 := rebuildSuffix cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.ℓ 0) (D.g 0) cfg.P.d 0
    (fun _ => D.G 0)
    (fun _ => cfg.T.init cfg.P.k (levelM cfg.TP cfg.P 0) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hChCon : ∀ k ≤ cfg.P.d,
      st₀.chain.toTreeChain.chainLen st₀.chain.ℓ k =
        (mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainLen (D.ℓ 0) k ∧
      st₀.chain.toTreeChain.chainGrad st₀.chain.g k =
        (mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainGrad (D.g 0) k :=
    fun k hk => ⟨chainLen_congr_params rfl (D.ℓ 0) hk (fun _ _ => rfl) (fun _ _ => rfl),
      chainGrad_congr_params rfl (D.g 0) hk (fun _ _ => rfl) (fun _ _ => rfl)⟩
  let H₀ : ∀ i < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ st₀.chain i := fun i hi =>
    have hsuf := hRS.2.2.1 i (Nat.zero_le i) hi
    zeroLevelHistory cfg.T cfg.TP cfg.P cfg.N₀ st₀.chain i hi hV.hTP hsuf.2.2.2.2.2.1
      hsuf.2.2.2.2.2.2.2.1
      (le_trans (Finset.card_le_card (hRS.1 0 (Nat.zero_le _) ▸ hsuf.2.2.2.2.2.2.1)) hn0)
      (fun e he => by rw [(hChCon i hi.le).1]; exact hsuf.2.2.2.2.2.2.2.2.1 e he)
      (by rw [(hChCon i hi.le).1, (hChCon i hi.le).2]; exact hsuf.2.2.2.2.2.2.2.2.2.1)
      hsuf.2.1 hsuf.2.2.2.2.1 hsuf.2.2.2.1 rfl
      (fun h0 => by subst h0; exact hsuf.2.2.1)
      (fun h1 => (hRS.2.2.1 (i + 1) (Nat.zero_le _) h1).2.2.1)
  have hEndG : Game.stateAt W₀ cfg.P.hk initStr moves₀ moves₀.length =
      { Game.initState cfg.P.d cfg.P.k cfg.P.hk initStr with phase := .stage34 } := by
    simp [moves₀, Game.stateAt, Game.stepState]
  have hChEq : st₀.chain = (algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0)).1 := rfl
  have hSc0 : ∀ i, st₀.chain.shiftCount i = 0 := by rw [hChEq]; exact hInit.2.2.2.2.2.1
  have hRc0 : ∀ i, st₀.chain.rebuildCount i = 0 := by rw [hChEq]; exact hInit.2.2.2.2.2.2.1
  have hGeq : ∀ j, st₀.chain.G j = res0.1 j := fun _ => rfl
  have hSceq : ∀ j, st₀.chain.scState j = res0.2.1 j := fun _ => rfl
  have hBreq : ∀ j, st₀.chain.bran j = res0.2.2.1 j := fun _ => rfl
  refine ⟨{
    moves := moves₀, hmne := by simp [moves₀], initStr := initStr, W_game := W₀,
    hv := hv₀, hf := hf₀, hPhase := by rw [hEndG],
    timeOfRound := fun _ => 0, hTimeMono := fun _ _ _ _ => le_refl 0, hTimeEnd := rfl,
    hW_eq := fun _ _ => rfl,
    hShiftMatch := fun i => by rw [hSc0]; simp [moves₀, Game.shiftCount],
    hRebMatch := fun i => by rw [hRc0]; simp [moves₀, Game.rebuildCount],
    hPassMatch := fun i => by
      simp [moves₀, Game.passesAt, Game.stepPasses, st₀, algorithm2_init],
    hBranMatch := fun i => by
      rw [hEndG]
      by_cases hi : i.val < cfg.P.d
      · have hsuf := hRS.2.2.1 i.val (Nat.zero_le _) hi
        change 0 = if i.val < cfg.P.d then st₀.chain.bran i.val else st₀.branD
        simp only [hi, ↓reduceIte]; rw [hBreq]; exact hsuf.1.symm
      · change 0 = if i.val < cfg.P.d then st₀.chain.bran i.val else st₀.branD
        simp only [hi, ↓reduceIte]; rfl
    snapC := fun _ => st₀.chain.toTreeChain,
    snapE2I := fun _ => st₀.extToInt, snapI2E := fun _ => st₀.intToExt, snapNF := fun _ => st₀.nextFresh,
    hSnapEndC := rfl, hSnapEndE2I := rfl, hSnapEndI2E := rfl, hSnapEndNF := rfl,
    hSnapFresh := fun _ _ => hFresh,
    hSnapHolds := fun _ _ => hSH,
    reinit := fun _ => 1,
    hRebRep := fun _ => by rw [hEndG]; exact le_refl 1,
    hRepRe := fun _ => by rw [hEndG]; exact le_refl 1,
    hSnapBran := fun _ _ _ _ _ _ _ => rfl,
    hStrMatch := fun i j => by rw [hEndG]; simp [initStr, Game.initState],
    H := H₀, lvlIdx := fun _ _ => 0,
    hLvlReinit := fun _ _ => rfl, hLvlEnd := fun _ _ => rfl,
    hLvlMono := fun _ _ _ _ _ _ _ => le_refl 0,
    hLvlSucc := fun k hk => ⟨le_refl 0, fun _ _ _ => rfl⟩,
    hLvlSnap := fun k hk _ _ _ => by
      have hsuf := hRS.2.2.1 k (Nat.zero_le _) hk
      have hSC_eq : st₀.chain.scState k =
          cfg.T.init cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (st₀.chain.G k)
            (st₀.chain.toTreeChain.chainLen st₀.chain.ℓ k)
            (st₀.chain.toTreeChain.chainGrad st₀.chain.g k) := by
        rw [hSceq k, hGeq k, (hChCon k hk.le).1, (hChCon k hk.le).2]
        dsimp only [res0]; exact hsuf.2.2.2.2.2.2.2.2.2.1
      refine ⟨rfl, fun j _ => ?_, fun _ j _ => ?_⟩
      · simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.runAfterRestarts,
          SparseCoreRestartTool.runAfterUpdate, List.foldl_nil]
        change cfg.T.lsfs (st₀.chain.scState k) j = _
        rw [hSC_eq]
      · simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.runAfterRestarts,
          SparseCoreRestartTool.runAfterUpdate, List.foldl_nil]
        change cfg.T.emb (st₀.chain.scState k) j = _
        rw [hSC_eq]
    hLvlCore := fun k hk => by
      have hsufk := hRS.2.2.1 k (Nat.zero_le _) (Nat.lt_of_succ_lt hk)
      refine ⟨le_refl 0, fun δ hδ => ?_, fun δ h1 h2 => by simp [H₀, zeroLevelHistory] at h2; omega,
        fun δ hδ e he => ?_⟩
      · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
        simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.coreInstanceFrom, Nat.sub_self, Nat.zero_add,
          SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate, List.foldl_nil]
        rw [hGeq (k + 1), hGeq k, hBreq k, (hChCon k (Nat.lt_of_succ_lt hk).le).1,
          (hChCon k (Nat.lt_of_succ_lt hk).le).2]
        dsimp only [res0]
        rw [← hsufk.2.2.2.2.2.2.2.2.2.1, hsufk.1]
        exact hsufk.2.2.2.2.2.2.2.2.2.2
      · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
        simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.coreInstanceFrom, Nat.sub_self, Nat.zero_add,
          SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate, List.foldl_nil]
        rw [hGeq k, hBreq k, (hChCon k (Nat.lt_of_succ_lt hk).le).1,
          (hChCon k (Nat.lt_of_succ_lt hk).le).2, (hChCon (k + 1) hk.le).1]
        have hAct_fold : (mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).activeLSF k =
            cfg.T.lsfs (res0.2.1 k) (res0.2.2.1 k) := by
          simp [TreeChain.activeLSF, mkPartialChain, Nat.lt_of_succ_lt hk]
        rw [TreeChain.chainLen, hAct_fold]
        dsimp only [res0]
        rw [← hsufk.2.2.2.2.2.2.2.2.2.1]
    updRound := fun _ => 1,
    hUpdBound := fun _ _ => by rw [hEndG]; exact ⟨le_refl 1, le_refl 1⟩,
    hUpdMono := fun τ₁ τ₂ h12 h2 => by simp [H₀, zeroLevelHistory] at h2; omega,
    hUpdBand := fun r hre _ => ⟨hre, fun hlt => by simp [H₀, zeroLevelHistory] at hlt⟩,
    hLvl0Match := fun _ _ => ⟨rfl, fun _ _ => rfl⟩,
    hLvl0NoIns := fun s τ _ hτ _ _ _ _ _ _ _ _ _ e _ => by
      simp [H₀, zeroLevelHistory] at hτ
      subst hτ
      exact ⟨fun _ => ⟨rfl, fun x hx1 hx2 => by omega, rfl⟩, fun _ => ⟨rfl, fun x hx1 hx2 => by omega⟩⟩ }⟩

/-- **Init step**: construct `Alg2HiddenTrace` at `t = 0` after `algorithm2_init`. -/
theorem alg2HiddenTrace_init {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hm0 : (D.G 0).m ≤ cfg.P.M₀) (hn0 : (D.G 0).n ≤ cfg.N₀)
    {c_ext w_ext : ℕ → ℕ → ℝ} (hHS0 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext 0) :
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext 0
      (algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0))) :=
  alg2HiddenTrace_initAt cfg.N₀ hV hHist hm0 hn0 (fun hIc hFc => chainInv_last_le_N0 hV hn0 hIc hFc) hHS0

/-- **Detect step**: advance `Alg2HiddenTraceAt` from `t` to `t + 1` across `algorithm2_detect`,
parameterized by last-level vertex cap `nLast`. -/
theorem alg2HiddenTrace_detectAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = false)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G (t + 1)) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ nLast)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t)
    (hℓ : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e')) :
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext
      (t + 1) (algorithm2_detect cfg st).2) := by
  have hDetU := (hHist.2.2.1 (t + 1) (by omega) ht1 hisUpd).1
  have hDetℓ : D.ℓ (t + 1) = D.ℓ t := by
    simpa using (hHist.2.2.1 (t + 1) (by omega) ht1 hisUpd).2.2
  have hDG : D.G (t + 1) = D.G t := by
    have hV1 := (hHist.1 (t + 1) (by omega) ht1).2
    rw [hDetU] at hV1; exact hV1
  have hFresh1 : FreshInv (D.G (t + 1)) (st.chain.G 0) st.extToInt st.intToExt st.nextFresh := by
    rw [hDG, ← hExtG]; exact hFresh
  have hℓ1 : st.chain.ℓ = fun e' => D.ℓ (t + 1) (st.intToExt e') := by
    rw [hℓ]; ext e'; rw [hDetℓ]
  have hSH1 := chainState_snapHoldsAt nLast hV hInv hFresh1 hℓ1 hn1 (hLastBound hInv hFresh1)
  set gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  set R := gSt.round
  let W' : ℕ → ℝ := fun r => if r = R + 1 then (D.G (t + 1)).norm1 (w_ext (t + 1)) else tr.W_game r
  have hW_le : ∀ r ≤ R, tr.W_game r = W' r := fun r hr => by
    simp [W', Nat.ne_of_lt (lt_of_le_of_lt hr (Nat.lt_succ_self R))]
  have hv_congr := validPlayPrefix_W_congr tr.W_game W' hW_le tr.hv
  have hf_congr := followsStrategyPrefix_W_congr tr.W_game W' hW_le tr.hf
  have hsc : Game.stateAt W' cfg.P.hk tr.initStr tr.moves tr.moves.length = gSt :=
    (stateAt_W_congr tr.W_game W' cfg.P.hk tr.initStr tr.moves tr.moves.length hW_le).1.symm
  have hpc : Game.passesAt W' cfg.P.hk tr.initStr tr.moves tr.moves.length =
      Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length :=
    (stateAt_W_congr tr.W_game W' cfg.P.hk tr.initStr tr.moves tr.moves.length hW_le).2.symm
  let m₁ : Game.Move cfg.P.d cfg.P.k := .roundStep .roundCompleting .doNothing (fun _ _ => 0)
  let m₂ : Game.Move cfg.P.d cfg.P.k := .advDoNothing
  have hPh : gSt.phase = .stage34 := tr.hPhase
  have hm1_v : Game.ValidStep cfg.gameParams W' gSt m₁ := by simp [Game.ValidStep, hPh, m₁]
  have hm1_s : Game.StrategyStep cfg.gameParams gSt
      (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m₁ := by
    simp [Game.StrategyStep, hPh, m₁]; rfl
  have hv1 := validPlayPrefix_snoc hv_congr m₁
    ((congrArg (fun s => Game.ValidStep cfg.gameParams W' s m₁) hsc).mpr hm1_v)
  have hf1 := followsStrategyPrefix_snoc hf_congr m₁
    ((congrArg (fun p => Game.StrategyStep cfg.gameParams _ p m₁) hpc).mpr
      ((congrArg (fun s => Game.StrategyStep cfg.gameParams s _ m₁) hsc).mpr hm1_s))
  have hlen1 : (tr.moves ++ [m₁]).length = tr.moves.length + 1 := by simp
  have hget1 : (tr.moves ++ [m₁])[tr.moves.length]'(by simp) = m₁ := by simp
  have hgSt1 : Game.stateAt W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (tr.moves ++ [m₁]).length =
      { gSt with round := R + 1, phase := .stage2 } := by
    rw [hlen1, Game.stateAt_succ W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (by simp),
      stateAt_append_left W' cfg.P.hk tr.initStr tr.moves [m₁] tr.moves.length (le_refl _),
      hget1, hsc]
    simp [m₁, Game.stepState, gSt, R]
  have hm2_v : Game.ValidStep cfg.gameParams W' { gSt with round := R + 1, phase := .stage2 } m₂ := by
    simp only [Game.ValidStep, m₂, W', ↓reduceIte]
    exact ⟨weightValid_norm1_of_hiddenStableAt hV.hα hm1 hHS1, trivial⟩
  let moves' := (tr.moves ++ [m₁]) ++ [m₂]
  have hlen2 : moves'.length = (tr.moves ++ [m₁]).length + 1 := by simp [moves']
  have hget2 : moves'[(tr.moves ++ [m₁]).length]'(by simp [moves']) = m₂ := by simp [moves']
  have hv' := validPlayPrefix_snoc hv1 m₂
    ((congrArg (fun s => Game.ValidStep cfg.gameParams W' s m₂) hgSt1).mpr hm2_v)
  have hf' := followsStrategyPrefix_snoc hf1 m₂
    ((congrArg (fun s => Game.StrategyStep cfg.gameParams s _ m₂) hgSt1).mpr
      (by simp [Game.StrategyStep]))
  have hEnd : Game.stateAt W' cfg.P.hk tr.initStr moves' moves'.length =
      { gSt with round := R + 1, phase := .stage34 } := by
    rw [hlen2, Game.stateAt_succ W' cfg.P.hk tr.initStr moves' (by simp [moves']),
      stateAt_append_left W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) [m₂] _ (le_refl _),
      hget2, hgSt1]
    simp [m₂, Game.stepState]
  have hPassEnd : Game.passesAt W' cfg.P.hk tr.initStr moves' moves'.length =
      Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length := by
    rw [hlen2, Game.passesAt_succ W' cfg.P.hk tr.initStr moves' (by simp [moves']),
      passesAt_append_left W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) [m₂] _ (le_refl _),
      stateAt_append_left W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) [m₂] _ (le_refl _),
      hget2]
    have hp1 : Game.passesAt W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (tr.moves ++ [m₁]).length =
        Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length := by
      rw [hlen1, Game.passesAt_succ W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (by simp),
        passesAt_append_left W' cfg.P.hk tr.initStr tr.moves [m₁] tr.moves.length (le_refl _),
        stateAt_append_left W' cfg.P.hk tr.initStr tr.moves [m₁] tr.moves.length (le_refl _),
        hget1]
      simp [m₁, Game.stepPasses, hpc]
    rw [hp1]; simp [m₂, Game.stepPasses]
  let lvlIdx' : ℕ → ℕ → ℕ := fun r i =>
    if r = R + 1 then (if hi : i < cfg.P.d then (tr.H i hi).len else 0) else tr.lvlIdx r i
  refine ⟨{
    moves := moves', hmne := by simp [moves'], initStr := tr.initStr, W_game := W',
    hv := hv', hf := hf', hPhase := by rw [hEnd],
    timeOfRound := fun r => if r = R + 1 then t + 1 else tr.timeOfRound r,
    hTimeMono := fun r₁ r₂ h12 h2 => by
      rw [hEnd] at h2; simp only at h2
      rcases eq_or_lt_of_le (show r₂ ≤ R + 1 from h2) with rfl | h2lt
      · by_cases h1 : r₁ = R + 1
        · subst h1; simp
        · simp only [↓reduceIte, h1]
          exact le_trans (tr.hTimeMono r₁ R (by omega) (le_refl _)) (by rw [tr.hTimeEnd]; omega)
      · have hr2R : r₂ ≤ R := by omega
        simp only [Nat.ne_of_lt (lt_of_le_of_lt (le_trans h12 hr2R) (Nat.lt_succ_self _)),
          Nat.ne_of_lt (lt_of_le_of_lt hr2R (Nat.lt_succ_self _)), ↓reduceIte]
        exact tr.hTimeMono r₁ r₂ h12 hr2R
    hTimeEnd := by rw [hEnd]; simp,
    hW_eq := fun r hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp [W']
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp [W', hr1, tr.hW_eq r hrR]
    hShiftMatch := fun i => by
      change Game.shiftCount moves' i = st.chain.shiftCount i.val
      simpa [moves', Game.shiftCount, m₁, m₂] using tr.hShiftMatch i,
    hRebMatch := fun i => by
      change Game.rebuildCount moves' i = st.chain.rebuildCount i.val
      simpa [moves', Game.rebuildCount, m₁, m₂] using tr.hRebMatch i,
    hPassMatch := fun i => by rw [hPassEnd]; exact tr.hPassMatch i,
    hBranMatch := fun i => by rw [hEnd]; exact tr.hBranMatch i,
    snapC := fun r => if r = R + 1 then st.chain.toTreeChain else tr.snapC r,
    snapE2I := fun r => if r = R + 1 then st.extToInt else tr.snapE2I r,
    snapI2E := fun r => if r = R + 1 then st.intToExt else tr.snapI2E r,
    snapNF := fun r => if r = R + 1 then st.nextFresh else tr.snapNF r,
    hSnapEndC := by rw [hEnd]; simp [algorithm2_detect],
    hSnapEndE2I := by rw [hEnd]; simp [algorithm2_detect],
    hSnapEndI2E := by rw [hEnd]; simp [algorithm2_detect],
    hSnapEndNF := by rw [hEnd]; simp [algorithm2_detect],
    hSnapFresh := fun r hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp only [↓reduceIte]; exact hFresh1
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp only [hr1, ↓reduceIte]; exact tr.hSnapFresh r hrR
    hSnapHolds := fun r hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp only [↓reduceIte]; exact hSH1
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp only [hr1, ↓reduceIte]; exact tr.hSnapHolds r hrR
    reinit := tr.reinit,
    hRebRep := fun i => by rw [hEnd]; exact tr.hRebRep i,
    hRepRe := fun i => by rw [hEnd]; exact tr.hRepRe i,
    hSnapBran := fun i hi r hre hr b hb => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp [algorithm2_detect, ChainState.toTreeChain]
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp only [hr1, ↓reduceIte]; exact tr.hSnapBran i hi r hre hrR b hb
    hStrMatch := fun i j => by
      rw [hEnd]
      have hne : gSt.repT i ≠ R + 1 :=
        Nat.ne_of_lt (lt_of_le_of_lt (Game.repT_bounds _ _ _ _ _ i).2 (Nat.lt_succ_self _))
      simp only [hne, ↓reduceIte]
      exact tr.hStrMatch i j
    H := tr.H, lvlIdx := lvlIdx',
    hLvlReinit := fun i hi => by
      have hreR : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ R :=
        le_trans (tr.hRebRep _) (Game.repT_bounds _ _ _ _ _ _).2
      simp [lvlIdx', Nat.ne_of_lt (lt_of_le_of_lt hreR (Nat.lt_succ_self _)), tr.hLvlReinit i hi],
    hLvlEnd := fun i hi => by rw [hEnd]; simp [lvlIdx', hi],
    hLvlMono := fun i hi r₁ r₂ hre1 h12 hr2 => by
      rw [hEnd] at hr2; simp only at hr2
      by_cases hr2_1 : r₂ = R + 1
      · subst hr2_1
        by_cases hr1_1 : r₁ = R + 1
        · subst hr1_1; exact le_rfl
        · have hr1R : r₁ ≤ R := by omega
          simp only [lvlIdx', hr1_1, ↓reduceIte, hi, ↓reduceDIte]
          rw [← tr.hLvlEnd i hi]
          exact tr.hLvlMono i hi r₁ R hre1 hr1R (le_refl R)
      · have hr2R : r₂ ≤ R := by omega
        have hr1_1 : r₁ ≠ R + 1 := by omega
        simp only [lvlIdx', hr2_1, hr1_1, ↓reduceIte]
        exact tr.hLvlMono i hi r₁ r₂ hre1 h12 hr2R
    hLvlSucc := fun i hi => by
      refine ⟨(tr.hLvlSucc i hi).1, fun r hre hr => ?_⟩
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1
        simp only [lvlIdx', ↓reduceIte, hi, Nat.lt_of_succ_lt hi, ↓reduceDIte]
        exact Nat.add_sub_of_le (tr.hLvlSucc i hi).1
      · have hrR : r ≤ R := by omega
        simp only [lvlIdx', hr1, ↓reduceIte]; exact (tr.hLvlSucc i hi).2 r hre hrR
    hLvlSnap := fun i hi r hre hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1
        simp only [lvlIdx', ↓reduceIte, hi, ↓reduceDIte]
        have hreR : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ R :=
          le_trans (tr.hRebRep _) (Game.repT_bounds _ _ _ _ _ _).2
        have hSnapR := tr.hLvlSnap i hi R hreR (le_refl R)
        refine ⟨by rw [← tr.hLvlEnd i hi, ← tr.hSnapEndC]; exact hSnapR.1,
          fun j hj => by rw [← tr.hLvlEnd i hi, ← tr.hSnapEndC]; exact hSnapR.2.1 j hj,
          fun _ j _ => by
            dsimp only [algorithm2_detect, ChainState.toTreeChain]
            rw [← (tr.H i hi).hRun]⟩
      · have hrR : r ≤ R := by omega
        simp only [lvlIdx', hr1, ↓reduceIte]; exact tr.hLvlSnap i hi r hre hrR
    hLvlCore := tr.hLvlCore, updRound := tr.updRound,
    hUpdBound := fun τ hτ => ⟨(tr.hUpdBound τ hτ).1, by rw [hEnd]; exact le_trans (tr.hUpdBound τ hτ).2 (Nat.le_succ _)⟩,
    hUpdMono := tr.hUpdMono,
    hUpdBand := fun r hre hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp only [lvlIdx', ↓reduceIte, cfg.P.hd, ↓reduceDIte]
        exact ⟨le_trans (tr.hUpdBound _ (le_refl _)).2 (Nat.le_succ _), fun h => absurd h (lt_irrefl _)⟩
      · have hrR : r ≤ R := by omega
        simp only [lvlIdx', hr1, ↓reduceIte]; exact tr.hUpdBand r hre hrR
    hLvl0Match := fun τ hτ => by
      have hne : tr.updRound τ ≠ R + 1 := Nat.ne_of_lt (lt_of_le_of_lt (tr.hUpdBound τ hτ).2 (Nat.lt_succ_self _))
      have hm := tr.hLvl0Match τ hτ
      simp only [hne, ↓reduceIte]
      exact ⟨hm.1, fun e he => by simpa [hne] using hm.2 e he⟩
    hLvl0NoIns := fun s τ hs hτ r_s r_τ hrs1 hrs2 hrs3 hrt1 hrt2 hrt3 hst_r e he => by
      rw [hEnd] at hrs2 hrt2; simp only at hrs2 hrt2
      by_cases hrt1_eq : r_τ = R + 1
      · subst hrt1_eq
        have hτ_len : τ = (tr.H 0 cfg.P.hd).len := by
          by_contra hne
          have hlt := lt_of_le_of_ne hτ hne
          have hbad := hrt3 hlt; have hb := (tr.hUpdBound (τ + 1) hlt).2
          change tr.updRound (τ + 1) ≤ R at hb; omega
        subst hτ_len
        by_cases hrs_eq : r_s = R + 1
        · subst hrs_eq
          exact ⟨fun _ => ⟨rfl, fun x hx1 hx2 => by omega, rfl⟩,
            fun _ => ⟨rfl, fun x hx1 hx2 => by omega⟩⟩
        · have hrsR : r_s ≤ R := by omega
          have hR_band := tr.hUpdBand R (le_trans (tr.hRebRep _) (Game.repT_bounds _ _ _ _ _ _).2) (le_refl R)
          rw [tr.hLvlEnd 0 cfg.P.hd] at hR_band
          have hbase := tr.hLvl0NoIns s (tr.H 0 cfg.P.hd).len hs (le_refl _) r_s R hrs1 hrsR hrs3
            hR_band.1 (le_refl R) (fun hlt => absurd hlt (lt_irrefl _)) hrsR e he
          have hI2E_eq : st.intToExt e = tr.snapI2E R e := by rw [← tr.hSnapEndI2E]
          have hExtendNI : ∀ a, D.NotInsertedBetween a (tr.timeOfRound r_s) t →
              D.NotInsertedBetween a (tr.timeOfRound r_s) (t + 1) := fun a hNI x hx1 hx2 u hu hIu => by
            rcases eq_or_lt_of_le hx2 with rfl | hxlt
            · rw [hDetU] at hu; cases hu
            · exact hNI x hx1 (by omega) u hu hIu
          simp only [↓reduceIte, hrs_eq, hI2E_eq]
          rw [tr.hTimeEnd] at hbase
          refine ⟨fun heqs => ?_, fun hNI => ?_⟩
          · have hb := hbase.1 heqs; refine ⟨hb.1, hExtendNI _ hb.2.1, ?_⟩; rw [hDetℓ, hb.2.2]
          · have hb := hbase.2 hNI; exact ⟨hb.1, hExtendNI _ hb.2⟩
      · have hrtR : r_τ ≤ R := by omega
        have hrsR : r_s ≤ R := by omega
        have hrs_ne : r_s ≠ R + 1 := by omega
        simp only [hrt1_eq, hrs_ne, ↓reduceIte]
        exact tr.hLvl0NoIns s τ hs hτ r_s r_τ hrs1 hrsR hrs3 hrt1 hrtR hrt3 hst_r e he }⟩

/-- **Detect step**: advance `Alg2HiddenTrace` from `t` to `t + 1` across `algorithm2_detect`. -/
theorem alg2HiddenTrace_detect {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = false)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg} (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t)
    (hℓ : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e')) :
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext (t + 1) (algorithm2_detect cfg st).2) :=
  alg2HiddenTrace_detectAt cfg.N₀ hV hHist ht1 hisUpd hm1 hn1
    (fun hIc hFc => chainInv_last_le_N0 hV hn1 hIc hFc) hHS1 tr hInv hFresh hExtG hℓ

end InitDetectShift

end MinCostFlow.Chain
