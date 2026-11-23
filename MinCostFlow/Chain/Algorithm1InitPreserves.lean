module

public import MinCostFlow.Chain.Algorithm1RebuildSuffix
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Initialize and `rebuildSuffix` Preservation (Algorithm 1 Proofs Helpers)

Split from `MinCostFlow.Chain.Algorithm1Proofs`: `initialize_preserves*`, `rebuildSuffix_preserves*`, and `diffTreeChanges_chainTree_le_cap*`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section OpPreservation

lemma sum_range_inc_coeff (n i₀ : ℕ) (hi₀ : i₀ ≤ n) (c c' : ℕ → ℕ)
    (hc : ∀ i ∈ Finset.range (n + 1), c' i = if i = i₀ then c i₀ + 1 else c i)
    (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), (c' i : ℝ) * f i) =
      (∑ i ∈ Finset.range (n + 1), (c i : ℝ) * f i) + f i₀ := by
  have hmem : i₀ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi₀)
  calc
    ∑ i ∈ Finset.range (n + 1), (c' i : ℝ) * f i
        = ∑ i ∈ Finset.range (n + 1),
            ((c i : ℝ) * f i + if i = i₀ then f i₀ else 0) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hc i hi]
      split_ifs with heq
      · subst heq; push_cast; ring
      · simp
    _ = (∑ i ∈ Finset.range (n + 1), (c i : ℝ) * f i) +
          ∑ i ∈ Finset.range (n + 1), (if i = i₀ then f i₀ else 0) := Finset.sum_add_distrib
    _ = (∑ i ∈ Finset.range (n + 1), (c i : ℝ) * f i) + f i₀ := by
      rw [Finset.sum_ite_eq' _ _ (fun _ => f i₀)]; simp only [hmem, ↓reduceIte]

lemma chainRecBound_of_rebuildSuffix {T : SparseCoreRestartTool} {P : ChainParams}
    {factor : ℝ} (_hf : 0 ≤ factor) {i₀ : ℕ} (_hi₀ : i₀ ≤ P.d)
    {stPre st' : ChainState T P}
    (hRecPre : ChainRecBound P factor stPre)
    (hRec : st'.recUpdates = stPre.recUpdates)
    (hBefore : ∀ j < i₀, st'.updCount j = stPre.updCount j ∧ st'.curFwd j = stPre.curFwd j)
    (hAfter : ∀ j, i₀ ≤ j → j < P.d → st'.updCount j = 0 ∧ st'.curFwd j = 0) :
    ChainRecBound P factor st' := by
  intro j hj
  by_cases hlt : j < i₀
  · have ⟨hu, hcf⟩ := hBefore j hlt
    rw [hu, hcf, hRec]
    exact hRecPre j hj
  · have hge : i₀ ≤ j := Nat.le_of_not_lt hlt
    have ⟨hu, hcf⟩ := hAfter j hge hj
    refine ⟨by simp [hu, hcf], ?_⟩
    rw [hu, hcf, hRec]
    simp only [Nat.cast_zero, sub_zero]
    exact hRecPre.recUpdates_succ_le hj

lemma initialize_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ)
    (hG0Valid : G₀.IsValid) (hG0m : G₀.m ≤ P.M₀) (hG0n : G₀.n ≤ N₀)
    (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) :
    let (st, changes) := algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀
    ChainInv T L TP LP P N₀ st ∧
    ChainBudgetInv TP LP N₀ st ∧
    st.G 0 = G₀ ∧
    st.ℓ = ℓ₀ ∧
    st.g = g₀ ∧
    (∀ i, st.shiftCount i = 0) ∧
    (∀ i, st.rebuildCount i = 0) ∧
    applyTreeChanges ∅ changes = st.toTreeChain.chainTree.E ∧
    st.totalTreeUpdates = changes.length ∧
    (st.totalTreeUpdates : ℝ) ≤ diffTreeCap TP P 0 := by
  dsimp only [algorithm1_initialize]
  set dummySc := T.init P.k (levelM TP P 0) N₀ G₀ ℓ₀ g₀
  have hℓ0' : ∀ e ∈ G₀.E, 0 <
      (mkPartialChain T P (fun _ => G₀) (fun _ => dummySc) (fun _ => 0) G₀).chainLen ℓ₀ 0 e :=
    hℓ₀
  have hm0_real : (G₀.m : ℝ) ≤ (levelM TP P 0 : ℝ) := by
    exact_mod_cast le_trans hG0m (M₀_le_levelM_zero hTP P)
  have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk ℓ₀ g₀ P.d 0
    (fun _ => G₀) (fun _ => dummySc) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (zero_add P.d) hG0Valid (Finset.Subset.refl _) hG0n hm0_real hℓ0'
  rcases hRS with ⟨hG0eq, _, hSuf, _, _, _, hGdℓ, hLk, hLH, hLM, hLS, hLC⟩
  set res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ P.d 0
    (fun _ => G₀) (fun _ => dummySc) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0)
  set st : ChainState T P :=
    { G := res.1, scState := res.2.1, curRestarts := fun _ => 0,
      bran := res.2.2.1, updCount := res.2.2.2.1,
      recUpdates := fun _ => 0, curFwd := res.2.2.2.2.2.2.1,
      lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
      ℓ := ℓ₀, g := g₀, passes := fun _ => 0, shiftCount := fun _ => 0,
      rebuildCount := fun _ => 0, closedRuntime := 0, curLastRebuilds := 0,
      curLastCost := res.2.2.2.2.2.2.2.2, curEnc := res.2.2.2.2.1,
      closedTreeUpdates := 0, curDecUpdates := res.2.2.2.2.2.1, curLastTreeUpdates := 0,
      lvlM := levelM TP P, N₀ := N₀ }
  set changes := diffTreeChanges ∅ st.toTreeChain.chainTree.E
  set st' : ChainState T P := { st with closedTreeUpdates := changes.length }
  have hG0st : st'.G 0 = G₀ := hG0eq 0 (le_refl 0)
  have hChainCon : ∀ idx ≤ P.d,
      st'.toTreeChain.chainLen st'.ℓ idx =
        (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen ℓ₀ idx ∧
      st'.toTreeChain.chainGrad st'.g idx =
        (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad g₀ idx := by
    intro idx hidx
    refine ⟨chainLen_congr_params rfl ℓ₀ hidx (fun _ _ => rfl) ?_,
      chainGrad_congr_params rfl g₀ hidx (fun _ _ => rfl) ?_⟩ <;>
    · intro j hj; rfl
  have hHist : ∀ i < P.d, Nonempty (LevelHistory T TP P N₀ st' i) := by
    intro i hi
    rcases hSuf i (Nat.zero_le _) hi with ⟨hb, hu, henc, hdec, hcfwd, hGV, hSubV, hGm, hℓi, hsc, _⟩
    have hencNext : i + 1 < P.d → st'.curEnc (i + 1) = 0 := fun h1 =>
      (hSuf (i + 1) (Nat.zero_le _) h1).2.2.1
    have hGiN : (st'.G i).n ≤ N₀ := by
      refine le_trans (Finset.card_le_card ?_) hG0n
      simpa [st', st, hG0eq 0 (le_refl 0)] using hSubV
    refine levelHistory_of_init T TP P hTP N₀ st' i hi hGV hGm hGiN ?_ ?_ hu hcfwd hdec rfl
      (fun h0 => by subst h0; exact henc) hencNext
    · rw [(hChainCon i (Nat.le_of_lt hi)).1]; exact hℓi
    · rw [(hChainCon i (Nat.le_of_lt hi)).1, (hChainCon i (Nat.le_of_lt hi)).2]; exact hsc
  have hInv : ChainInv T L TP LP P N₀ st' := by
    refine ⟨?_, ?_, ?_, ?_, hLk, hLk, ?_, hLM, hLS, ?_, ?_, hHist, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · rw [hG0st]; exact hG0Valid
    · rw [hG0st]; exact hG0m
    · rw [hG0st]; exact hG0n
    · rw [hG0st]; exact hℓ₀
    · intro j hj; rw [(hChainCon P.d (le_refl P.d)).1]; exact hLH j hj
    · intro i hi; dsimp only [st', st]; rw [(hSuf i (Nat.zero_le _) hi).1]; exact P.hk
    · intro i hi
      rcases hSuf i (Nat.zero_le _) hi with ⟨hb, _, _, _, _, _, _, _, _, _, hS⟩
      change res.1 (i + 1) = T.S (res.2.1 i) (res.2.2.1 i)
      rw [hb]; exact hS
    · intro i hi
      rcases hSuf i (Nat.zero_le _) hi with ⟨_, hu, _⟩
      dsimp only [st', st]; rw [hu]; simp
    · intro i hi
      rcases hSuf i (Nat.zero_le _) hi with ⟨_, hu, _, _, hcfwd, _⟩
      dsimp only [st', st]; rw [hu, hcfwd]; simp
    · have hc0 : st'.curEnc 0 = 0 := (hSuf 0 (Nat.zero_le _) P.hd).2.2.1
      have hu0 : st'.updCount 0 = 0 := (hSuf 0 (Nat.zero_le _) P.hd).2.1
      rw [hc0, hu0]
      simp only [Nat.cast_zero, add_zero]
      have hlog : 0 ≤ Real.log ((levelM TP P 0 : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ levelM TP P 0 from Nat.cast_nonneg _])
      exact mul_nonneg (by positivity) hlog
    · intro hd
      have hdi : P.d - 1 < P.d := Nat.sub_lt hd zero_lt_one
      obtain ⟨H⟩ := hHist (P.d - 1) hdi
      refine ⟨⟨H, by simp [st', st]⟩, ?_, ?_⟩
      · simpa [st', st, hG0st] using hLC
      · simp [st', st]
  have hCostB := hInv.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P 0 := by
    have hEcard : (changes.length : ℝ) ≤
        ∑ j ∈ Finset.range (P.d + 1), ((st'.toTreeChain.activeLSF j).F.F.E.card : ℝ) := by
      change ((diffTreeChanges ∅ st'.toTreeChain.chainTree.E).length : ℝ) ≤ _
      rw [diffTreeChanges_length, Finset.empty_sdiff, Finset.card_empty, zero_add,
        Finset.sdiff_empty]
      change (st'.toTreeChain.chainTreeEdges.card : ℝ) ≤ _
      unfold TreeChain.chainTreeEdges
      exact_mod_cast (Finset.card_biUnion_le : _ ≤ _)
    unfold diffTreeCap
    have hsum_le : (∑ j ∈ Finset.range (P.d + 1), ((st'.toTreeChain.activeLSF j).F.F.E.card : ℝ)) ≤
        (Finset.Ico 0 (P.d + 1)).sum (fun j => (levelM TP P j : ℝ)) := by
      rw [Nat.Ico_zero_eq_range (P.d + 1)]
      exact Finset.sum_le_sum fun j hj => hCostB.2.2.2.2 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have hnn : 0 ≤ (Finset.Ico 0 (P.d + 1)).sum (fun j => (levelM TP P j : ℝ)) :=
      Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
    linarith
  have hBudget : ChainBudgetInv TP LP N₀ st' := by
    refine ⟨?_, ?_⟩
    · simp only [st', st, activeRestartCap_zero, Nat.cast_zero, add_zero, zero_mul,
        Finset.sum_const_zero, le_refl]
    · simp only [st', st, Nat.cast_zero, add_zero, zero_mul, Finset.sum_const_zero]
      exact hDiffCap
  have hTotEq : st'.totalTreeUpdates = changes.length := by
    have hDec0 : ∀ j ∈ Finset.range P.d, st'.curDecUpdates j = 0 := fun j hj =>
      (hSuf j (Nat.zero_le _) (Finset.mem_range.mp hj)).2.2.2.1
    simp only [ChainState.totalTreeUpdates, st', st, Finset.sum_eq_zero hDec0, add_zero]
  refine ⟨hInv, hBudget, hG0st, rfl, rfl, fun _ => rfl, fun _ => rfl, ?_, hTotEq, hTotEq ▸ hDiffCap⟩
  · change applyTreeChanges ∅ (diffTreeChanges ∅ st'.toTreeChain.chainTree.E) =
      st'.toTreeChain.chainTree.E
    exact applyTreeChanges_diffTreeChanges ∅ st'.toTreeChain.chainTree.E

lemma initialize_preserves (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ)
    (hG0Valid : G₀.IsValid) (hG0m : G₀.m ≤ P.M₀) (hG0n : G₀.n ≤ N₀)
    (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) :
    let (st, changes) := algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀
    ChainInv T L TP LP P N₀ st ∧
    ChainBudgetInv TP LP N₀ st ∧
    st.G 0 = G₀ ∧
    st.ℓ = ℓ₀ ∧
    st.g = g₀ ∧
    (∀ i, st.shiftCount i = 0) ∧
    (∀ i, st.rebuildCount i = 0) ∧
    applyTreeChanges ∅ changes = st.toTreeChain.chainTree.E ∧
    st.totalTreeUpdates = changes.length ∧
    (st.totalTreeUpdates : ℝ) ≤ diffTreeCap TP P 0 :=
  initialize_preserves_noHidden T L TP LP P N₀ hTP hLP hT.toNoHidden hL hγM₀ hγk
    G₀ ℓ₀ g₀ hG0Valid hG0m hG0n hℓ₀

lemma rebuildSuffix_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st st_base : ChainState T P} {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (G0 : ℕ → MGraph) (sc0 : ℕ → T.State) (bran0 upd0 cEnc0 cDec0 cFwd0 : ℕ → ℕ)
    (hG0Valid : (G0 0).IsValid)
    (hGi0Valid : (G0 i₀).IsValid)
    (hGi0V : (G0 i₀).V ⊆ (G0 0).V)
    (hGi0m : ((G0 i₀).m : ℝ) ≤ (levelM TP P i₀ : ℝ))
    (hG0_m_if : (G0 0).m ≤ P.M₀)
    (hG0n : (G0 0).n ≤ N₀)
    (hℓ0_if : ∀ e ∈ (G0 0).E, 0 < st_base.ℓ e)
    (hℓ_i0 : ∀ e ∈ (G0 i₀).E,
      0 < (mkPartialChain T P G0 sc0 bran0 (G0 i₀)).chainLen st_base.ℓ i₀ e)
    (hPreHist : ∀ j < i₀, Nonempty (LevelHistory T TP P N₀
      { st_base with
        G := G0, scState := sc0, bran := bran0, updCount := upd0,
        curEnc := cEnc0, curDecUpdates := cDec0, curFwd := cFwd0 } j))
    (hPreBran : ∀ j < i₀, bran0 j < P.k)
    (hPreGSucc : ∀ j < i₀, G0 (j + 1) = T.S (sc0 j) (bran0 j))
    (hPreRecReb : ∀ j < P.d,
      (st_base.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
        (if j < i₀ then (upd0 j : ℝ) else 0) ≤ (st_base.recUpdates j : ℝ))
    (hPreRecFwd : ChainRecBound P (TP.γ_r (P.M₀ ^ 2))
      { st_base with updCount := upd0, curFwd := cFwd0 })
    (hPreEnc0 : i₀ > 0 → (cEnc0 0 : ℝ) ≤
      20 * ((levelM TP P 0 : ℝ) + (upd0 0 : ℝ)) *
        Real.log ((levelM TP P 0 : ℝ) + (upd0 0 : ℝ) + 2))
    (hLvlM : st_base.lvlM = levelM TP P)
    (hN0 : st_base.N₀ = N₀)
    (hstEq : st =
      let res := rebuildSuffix T L P st_base.lvlM st_base.N₀ st_base.ℓ st_base.g (P.d - i₀) i₀
        G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0
      { st_base with
        G := res.1
        scState := res.2.1
        curRestarts := fun j => if i₀ ≤ j ∧ j < P.d then 0 else st_base.curRestarts j
        bran := res.2.2.1
        updCount := res.2.2.2.1
        curFwd := res.2.2.2.2.2.2.1
        lastK := res.2.2.2.2.2.2.2.1.1
        lastLSFs := res.2.2.2.2.2.2.2.1.2
        lastBran := 0
        curLastRebuilds := 0
        curLastCost := res.2.2.2.2.2.2.2.2
        curEnc := res.2.2.2.2.1
        curDecUpdates := res.2.2.2.2.2.1
        curLastTreeUpdates := 0 }) :
    ChainInv T L TP LP P N₀ st := by
  subst hstEq
  have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk st_base.ℓ st_base.g
    (P.d - i₀) i₀ G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0
    (by omega) hGi0Valid hGi0V hG0n hGi0m hℓ_i0
  have hResEq : rebuildSuffix T L P st_base.lvlM st_base.N₀ st_base.ℓ st_base.g (P.d - i₀) i₀
        G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0 =
      rebuildSuffix T L P (levelM TP P) N₀ st_base.ℓ st_base.g (P.d - i₀) i₀
        G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0 := by
    rw [hLvlM, hN0]
  rw [← hResEq] at hRS
  rcases hRS with ⟨hIG, hIPre, hISuf, _, _, _, _, hLk, hLH, hLM, hLS, hLC⟩
  set res := rebuildSuffix T L P st_base.lvlM st_base.N₀ st_base.ℓ st_base.g (P.d - i₀) i₀
    G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0
  let stMid : ChainState T P :=
    { st_base with
      G := res.1, scState := res.2.1,
      curRestarts := fun j => if i₀ ≤ j ∧ j < P.d then 0 else st_base.curRestarts j,
      bran := res.2.2.1, updCount := res.2.2.2.1,
      curFwd := res.2.2.2.2.2.2.1,
      lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
      curLastRebuilds := 0, curLastCost := res.2.2.2.2.2.2.2.2,
      curEnc := res.2.2.2.2.1, curDecUpdates := res.2.2.2.2.2.1,
      curLastTreeUpdates := 0 }
  let stPre : ChainState T P :=
    { st_base with
      G := G0, scState := sc0, bran := bran0, updCount := upd0,
      curEnc := cEnc0, curDecUpdates := cDec0, curFwd := cFwd0 }
  have hG0eq : stMid.G 0 = G0 0 := hIG 0 (Nat.zero_le _)
  have hChainPre : ∀ idx ≤ i₀,
      stMid.toTreeChain.chainLen stMid.ℓ idx = stPre.toTreeChain.chainLen stPre.ℓ idx ∧
      stMid.toTreeChain.chainGrad stMid.g idx = stPre.toTreeChain.chainGrad stPre.g idx := by
    intro idx hidx
    refine ⟨chainLen_congr_lt st_base.ℓ idx (fun j hj => ?_) (fun j hj => ?_),
      chainGrad_congr_lt st_base.g idx (fun j hj => ?_) (fun j hj => ?_)⟩
    · dsimp only [ChainState.toTreeChain, stMid, stPre]
      rw [hIG j (Nat.le_of_lt (lt_of_lt_of_le hj hidx))]
    · have hjlt : j < P.d := lt_of_lt_of_le hj (le_trans hidx (Nat.le_of_lt hi₀))
      rcases hIPre j (lt_of_lt_of_le hj hidx) with ⟨a1, a2, _⟩
      have h1 : stMid.toTreeChain.activeLSF j = T.lsfs (res.2.1 j) (res.2.2.1 j) := by
        unfold TreeChain.activeLSF; dsimp only [ChainState.toTreeChain, stMid]
        exact ite_eq_left_iff.mpr fun h => absurd hjlt h
      have h2 : stPre.toTreeChain.activeLSF j = T.lsfs (sc0 j) (bran0 j) := by
        unfold TreeChain.activeLSF; dsimp only [ChainState.toTreeChain, stPre]
        exact ite_eq_left_iff.mpr fun h => absurd hjlt h
      rw [h1, h2, a1, a2]
    · dsimp only [ChainState.toTreeChain, stMid, stPre]
      rw [hIG j (Nat.le_of_lt (lt_of_lt_of_le hj hidx))]
    · have hjlt : j < P.d := lt_of_lt_of_le hj (le_trans hidx (Nat.le_of_lt hi₀))
      rcases hIPre j (lt_of_lt_of_le hj hidx) with ⟨a1, a2, _⟩
      have h1 : stMid.toTreeChain.activeLSF j = T.lsfs (res.2.1 j) (res.2.2.1 j) := by
        unfold TreeChain.activeLSF; dsimp only [ChainState.toTreeChain, stMid]
        exact ite_eq_left_iff.mpr fun h => absurd hjlt h
      have h2 : stPre.toTreeChain.activeLSF j = T.lsfs (sc0 j) (bran0 j) := by
        unfold TreeChain.activeLSF; dsimp only [ChainState.toTreeChain, stPre]
        exact ite_eq_left_iff.mpr fun h => absurd hjlt h
      rw [h1, h2, a1, a2]
  have hChainAll : ∀ idx ≤ P.d,
      stMid.toTreeChain.chainLen stMid.ℓ idx =
        (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen st_base.ℓ idx ∧
      stMid.toTreeChain.chainGrad stMid.g idx =
        (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad st_base.g idx := by
    intro idx hidx
    refine ⟨chainLen_congr_params rfl st_base.ℓ hidx (fun _ _ => rfl) (fun _ _ => rfl),
      chainGrad_congr_params rfl st_base.g hidx (fun _ _ => rfl) (fun _ _ => rfl)⟩
  have hHist : ∀ i < P.d, Nonempty (LevelHistory T TP P N₀ stMid i) := by
    intro i hi
    by_cases hlt : i < i₀
    · obtain ⟨H⟩ := hPreHist i hlt
      rcases hIPre i hlt with ⟨a1, a2, a3, a4, a5, a6⟩
      have hC := hChainPre i (Nat.le_of_lt hlt)
      refine ⟨{
        D := H.D, len := H.len, s₀ := H.s₀, hs₀ := H.hs₀,
        restarts := H.restarts, hRestartsLt := H.hRestartsLt,
        hRestartsCount := by
          have hcR : stMid.curRestarts i = stPre.curRestarts i := by
            dsimp only [stMid, stPre]
            simp [show ¬ (i₀ ≤ i ∧ i < P.d) by omega]
          rw [hcR]; exact H.hRestartsCount,
        hS0Fresh := by dsimp only [stMid]; rw [a2]; exact H.hS0Fresh,
        hNoRestartAfterS0 := by dsimp only [stMid]; rw [a2]; exact H.hNoRestartAfterS0,
        hG0 := H.hG0, hD := H.hD, hLen := H.hLen, hℓPos := H.hℓPos,
        hEndG := by dsimp only [stMid]; rw [hIG i (Nat.le_of_lt hlt)]; exact H.hEndG,
        hEndℓ := fun e he => by
          have he' : e ∈ (stPre.G i).E := by
            change e ∈ (stMid.G i).E at he
            rwa [show stMid.G i = stPre.G i from hIG i (Nat.le_of_lt hlt)] at he
          rw [hC.1]; exact H.hEndℓ e he'
        hEndg := by rw [hC.2]; exact H.hEndg
        hUpd := by dsimp only [stMid]; rw [a3]; exact H.hUpd
        hThresh := by dsimp only [stMid]; rw [a3]; exact H.hThresh
        hInitMBound := H.hInitMBound
        hInitNBound := H.hInitNBound
        hRun := by dsimp only [stMid]; rw [a1]; exact H.hRun
        branchSeq := H.branchSeq
        hBranch := H.hBranch
        hBranchTail := by dsimp only [stMid]; rw [a2]; exact H.hBranchTail
        hWinFwdBound := H.hWinFwdBound
        hCurFwdEq := by dsimp only [stMid]; rw [a6]; exact H.hCurFwdEq
        hDecEq := by dsimp only [stMid]; rw [a1, a2, a5]; exact H.hDecEq
        hEnc0Le := fun h0 => by
          subst h0
          dsimp only [stMid] at a4 ⊢
          rw [a4]
          exact H.hEnc0Le rfl
        hEncLe := fun h1 => by
          dsimp only [stMid]
          rw [a2]
          by_cases h1lt : i + 1 < i₀
          · have ha4 := (hIPre (i + 1) h1lt).2.2.2.1
            rw [ha4]
            exact H.hEncLe h1
          · have hieq : i + 1 = i₀ := by omega
            have hzero : res.2.2.2.2.1 (i + 1) = 0 := by
              rw [hieq]; exact (hISuf i₀ (le_refl i₀) hi₀).2.2.1
            change res.2.2.2.2.1 (i + 1) ≤ _
            rw [hzero]
            exact Nat.zero_le _ }⟩
    · have hie : i₀ ≤ i := Nat.le_of_not_lt hlt
      rcases hISuf i hie hi with ⟨hb, hu, henc, hdec, hcfwd, hGV, hSubV, hGm, hℓi, hsc, _⟩
      have hencNext : i + 1 < P.d → stMid.curEnc (i + 1) = 0 := fun h1 =>
        (hISuf (i + 1) (by omega) h1).2.2.1
      have hGiN : (stMid.G i).n ≤ N₀ :=
        le_trans (Finset.card_le_card (hIG 0 (Nat.zero_le _) ▸ hSubV)) hG0n
      refine levelHistory_of_init T TP P hTP N₀ stMid i hi hGV hGm hGiN ?_ ?_ hu hcfwd hdec
        (by dsimp only [stMid]; simp [hie, hi]) (fun h0 => by subst h0; exact henc) hencNext
      · rw [(hChainAll i (Nat.le_of_lt hi)).1]; exact hℓi
      · rw [(hChainAll i (Nat.le_of_lt hi)).1, (hChainAll i (Nat.le_of_lt hi)).2]
        exact hsc
  have hRecFwdMid : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) stMid := by
    have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
    exact chainRecBound_of_rebuildSuffix hγr_nn (Nat.le_of_lt hi₀)
      hPreRecFwd rfl
      (fun j hj => ⟨(hIPre j hj).2.2.1, (hIPre j hj).2.2.2.2.2⟩)
      (fun j hj1 hj2 => ⟨(hISuf j hj1 hj2).2.1, (hISuf j hj1 hj2).2.2.2.2.1⟩)
  refine ⟨?_, ?_, ?_, ?_, hLk, hLk, ?_, hLM, hLS, ?_, ?_, hHist, ?_, hRecFwdMid, ?_, ?_, hLvlM, hN0⟩
  · rw [hG0eq]; exact hG0Valid
  · rw [hG0eq]; exact hG0_m_if
  · rw [hG0eq]; exact hG0n
  · rw [hG0eq]; exact hℓ0_if
  · intro j hj; rw [(hChainAll P.d (le_refl P.d)).1]; exact hLH j hj
  · intro i hi
    dsimp only [stMid]
    by_cases hlt : i < i₀
    · rw [(hIPre i hlt).2.1]; exact hPreBran i hlt
    · rw [(hISuf i (by omega) hi).1]; exact P.hk
  · intro i hi
    by_cases hlt : i < i₀
    · rcases hIPre i hlt with ⟨a1, a2, _⟩
      change res.1 (i + 1) = T.S (res.2.1 i) (res.2.2.1 i)
      rw [a1, a2, hIG (i + 1) hlt]
      exact hPreGSucc i hlt
    · rcases hISuf i (by omega) hi with ⟨hb, _, _, _, _, _, _, _, _, _, hS⟩
      change res.1 (i + 1) = T.S (res.2.1 i) (res.2.2.1 i)
      rw [hb]; exact hS
  · intro j hj
    dsimp only [stMid]
    by_cases hlt : j < i₀
    · have h1 := hPreRecReb j hj
      simp only [hlt, ↓reduceIte] at h1
      rw [(hIPre j hlt).2.2.1]
      exact h1
    · have h1 := hPreRecReb j hj
      simp only [hlt, ↓reduceIte] at h1
      rw [(hISuf j (Nat.le_of_not_lt hlt) hj).2.1]
      simpa using h1
  · by_cases h0 : 0 < i₀
    · rcases hIPre 0 h0 with ⟨_, _, a3, a4, _⟩
      dsimp only [stMid]; rw [a3, a4]; exact hPreEnc0 h0
    · have hi0 : i₀ = 0 := by omega
      subst hi0
      rcases hISuf 0 (le_refl 0) P.hd with ⟨_, hu, henc, _⟩
      dsimp only [stMid]; rw [hu, henc]
      simp only [Nat.cast_zero, add_zero]
      have hlog : 0 ≤ Real.log ((levelM TP P 0 : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ levelM TP P 0 from Nat.cast_nonneg _])
      exact mul_nonneg (by positivity) hlog
  · intro hd
    have hdi : P.d - 1 < P.d := Nat.sub_lt hd zero_lt_one
    obtain ⟨H⟩ := hHist (P.d - 1) hdi
    refine ⟨⟨H, by simp⟩, ?_, ?_⟩
    · simpa [stMid, hG0eq] using hLC
    · simp

lemma rebuildSuffix_preserves (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st st_base : ChainState T P} {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (G0 : ℕ → MGraph) (sc0 : ℕ → T.State) (bran0 upd0 cEnc0 cDec0 cFwd0 : ℕ → ℕ)
    (hG0Valid : (G0 0).IsValid)
    (hGi0Valid : (G0 i₀).IsValid)
    (hGi0V : (G0 i₀).V ⊆ (G0 0).V)
    (hGi0m : ((G0 i₀).m : ℝ) ≤ (levelM TP P i₀ : ℝ))
    (hG0_m_if : (G0 0).m ≤ P.M₀)
    (hG0n : (G0 0).n ≤ N₀)
    (hℓ0_if : ∀ e ∈ (G0 0).E, 0 < st_base.ℓ e)
    (hℓ_i0 : ∀ e ∈ (G0 i₀).E,
      0 < (mkPartialChain T P G0 sc0 bran0 (G0 i₀)).chainLen st_base.ℓ i₀ e)
    (hPreHist : ∀ j < i₀, Nonempty (LevelHistory T TP P N₀
      { st_base with
        G := G0, scState := sc0, bran := bran0, updCount := upd0,
        curEnc := cEnc0, curDecUpdates := cDec0, curFwd := cFwd0 } j))
    (hPreBran : ∀ j < i₀, bran0 j < P.k)
    (hPreGSucc : ∀ j < i₀, G0 (j + 1) = T.S (sc0 j) (bran0 j))
    (hPreRecReb : ∀ j < P.d,
      (st_base.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
        (if j < i₀ then (upd0 j : ℝ) else 0) ≤ (st_base.recUpdates j : ℝ))
    (hPreRecFwd : ChainRecBound P (TP.γ_r (P.M₀ ^ 2))
      { st_base with updCount := upd0, curFwd := cFwd0 })
    (hPreEnc0 : i₀ > 0 → (cEnc0 0 : ℝ) ≤
      20 * ((levelM TP P 0 : ℝ) + (upd0 0 : ℝ)) *
        Real.log ((levelM TP P 0 : ℝ) + (upd0 0 : ℝ) + 2))
    (hLvlM : st_base.lvlM = levelM TP P)
    (hN0 : st_base.N₀ = N₀)
    (hstEq : st =
      let res := rebuildSuffix T L P st_base.lvlM st_base.N₀ st_base.ℓ st_base.g (P.d - i₀) i₀
        G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0
      { st_base with
        G := res.1
        scState := res.2.1
        curRestarts := fun j => if i₀ ≤ j ∧ j < P.d then 0 else st_base.curRestarts j
        bran := res.2.2.1
        updCount := res.2.2.2.1
        curFwd := res.2.2.2.2.2.2.1
        lastK := res.2.2.2.2.2.2.2.1.1
        lastLSFs := res.2.2.2.2.2.2.2.1.2
        lastBran := 0
        curLastRebuilds := 0
        curLastCost := res.2.2.2.2.2.2.2.2
        curEnc := res.2.2.2.2.1
        curDecUpdates := res.2.2.2.2.2.1
        curLastTreeUpdates := 0 }) :
    ChainInv T L TP LP P N₀ st :=
  rebuildSuffix_preserves_noHidden T L TP LP P N₀ hTP hLP hT.toNoHidden hL hγM₀ hγk hi₀
    G0 sc0 bran0 upd0 cEnc0 cDec0 cFwd0 hG0Valid hGi0Valid hGi0V hGi0m hG0_m_if hG0n
    hℓ0_if hℓ_i0 hPreHist hPreBran hPreGSucc hPreRecReb hPreRecFwd hPreEnc0 hLvlM hN0 hstEq

lemma diffTreeChanges_chainTree_le_cap_noHidden {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st₁ st₂ : ChainState T P}
    (hInv₁ : ChainInv T L TP LP P N₀ st₁) (hInv₂ : ChainInv T L TP LP P N₀ st₂)
    {i₀ : ℕ} (hi₀ : i₀ ≤ P.d)
    (hPre : ∀ j < i₀, (st₁.toTreeChain.activeLSF j).F.F.E =
      (st₂.toTreeChain.activeLSF j).F.F.E) :
    ((diffTreeChanges st₁.toTreeChain.chainTree.E st₂.toTreeChain.chainTree.E).length : ℝ) ≤
      diffTreeCap TP P i₀ := by
  have hCost₁ := hInv₁.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hCost₂ := hInv₂.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have htri := diffTreeChanges_chainTree_le_suffix (Nat.le_succ_of_le hi₀) hPre
  unfold diffTreeCap
  calc
    ((diffTreeChanges st₁.toTreeChain.chainTree.E st₂.toTreeChain.chainTree.E).length : ℝ)
        ≤ ∑ j ∈ Finset.Ico i₀ (P.d + 1),
            (((st₁.toTreeChain.activeLSF j).F.F.E.card : ℝ) +
              ((st₂.toTreeChain.activeLSF j).F.F.E.card : ℝ)) := by exact_mod_cast htri
    _ ≤ ∑ j ∈ Finset.Ico i₀ (P.d + 1),
          ((levelM TP P j : ℝ) + (levelM TP P j : ℝ)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjd := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2
      exact add_le_add (hCost₁.2.2.2.2 j hjd) (hCost₂.2.2.2.2 j hjd)
    _ = 2 * ∑ j ∈ Finset.Ico i₀ (P.d + 1), (levelM TP P j : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring

lemma diffTreeChanges_chainTree_le_cap {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st₁ st₂ : ChainState T P}
    (hInv₁ : ChainInv T L TP LP P N₀ st₁) (hInv₂ : ChainInv T L TP LP P N₀ st₂)
    {i₀ : ℕ} (hi₀ : i₀ ≤ P.d)
    (hPre : ∀ j < i₀, (st₁.toTreeChain.activeLSF j).F.F.E =
      (st₂.toTreeChain.activeLSF j).F.F.E) :
    ((diffTreeChanges st₁.toTreeChain.chainTree.E st₂.toTreeChain.chainTree.E).length : ℝ) ≤
      diffTreeCap TP P i₀ :=
  diffTreeChanges_chainTree_le_cap_noHidden hTP hLP hT.toNoHidden hγM₀ hγk hInv₁ hInv₂ hi₀ hPre


end OpPreservation

end MinCostFlow.Chain
