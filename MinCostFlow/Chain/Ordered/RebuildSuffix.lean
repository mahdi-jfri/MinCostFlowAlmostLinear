module

public import MinCostFlow.Chain.Ordered.BudgetHelpersCost
public import MinCostFlow.Chain.Algorithm1RebuildSuffix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `rebuildSuffix` Specification for Algorithm 1 with Orders

This file proves the fresh-level history builder `levelHistory_of_init` and the specification of
the ordered `rebuildSuffix` (`rebuildSuffix_spec_noHidden` and
`rebuildSuffix_levelOrd_rotation`), tracking the rotation witnesses `chainLevelOrd` across every
rebuilt level.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section RebuildSuffixSpec

/-- Construct a length-`0` `LevelHistory` for a freshly initialized level `i < P.d` given a valid
rotation witness for `st.levelOrd i`. -/
lemma levelHistory_of_init (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (_hTP : TP.Valid) (N₀ : ℕ) (st : ChainState T P) (i : ℕ) (_hi : i < P.d)
    (hGiValid : (st.G i).IsValid)
    (hGiM : ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ))
    (hGiN : (st.G i).n ≤ N₀)
    (hℓPos : ∀ e ∈ (st.G i).E, 0 < st.toTreeChain.chainLen st.ℓ i e)
    (hOrd : ∃ ρ : Rotation (st.G i), ρ.order = st.levelOrd i)
    (hInit : st.scState i = T.initOrd P.k (levelM TP P i) N₀ (st.G i)
      (st.toTreeChain.chainLen st.ℓ i) (st.toTreeChain.chainGrad st.g i) (st.levelOrd i))
    (hUpd : st.updCount i = 0)
    (hCurFwd : st.curFwd i = 0)
    (hDec : st.curDecUpdates i = 0)
    (hCurRest : st.curRestarts i = 0)
    (hEnc0 : i = 0 → st.curEnc 0 = 0)
    (hEncNext : i + 1 < P.d → st.curEnc (i + 1) = 0)
    (hOK : T.ToolOKAt TP P.k (levelM TP P i) N₀ (st.G i) (st.toTreeChain.chainLen st.ℓ i)) :
    Nonempty (LevelHistory T TP P N₀ st i) := by
  let D : DynamicInstance :=
    { G := fun _ => st.G i
      U := fun _ => []
      ℓ := fun _ => st.toTreeChain.chainLen st.ℓ i
      g := fun _ => st.toTreeChain.chainGrad st.g i }
  refine ⟨{
    D := D
    len := 0
    s₀ := 0
    hs₀ := le_refl 0
    restarts := fun _ => []
    hRestartsLt := fun _ _ _ h => by cases h
    hRestartsCount := by simp [hCurRest]
    hS0Fresh := Or.inl rfl
    hNoRestartAfterS0 := fun _ hr1 hr2 => by omega
    hG0 := hGiValid
    hD := fun _ ht1 ht2 => by omega
    hLen := fun _ ht1 ht2 => by omega
    hℓPos := fun _ _ e he => hℓPos e he
    hEndG := rfl
    hEndℓ := fun _ _ => rfl
    hEndg := rfl
    hUpd := by simp [hUpd]
    hThresh := by rw [hUpd]; simp [updateThreshold_nonneg]
    hInitMBound := by exact_mod_cast hGiM
    hInitNBound := hGiN
    ord := fun _ => st.levelOrd i
    hOrd := orderedUpTo_zero_of_rotation hOrd
    hEndOrd := rfl
    hRun := by
      simp only [SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
        List.foldl_nil]
      exact hInit
    hOK := hOK
    branchSeq := fun _ => 0
    hBranch := fun _ => P.hk
    hBranchTail := fun _ hs1 hs2 => by omega
    hWinFwdBound := by simp
    hCurFwdEq := by simp [hCurFwd]
    hDecEq := by
      rw [hInit]
      simp [hDec, SparseCoreRestartTool.runOrdAfterRestarts,
        SparseCoreRestartTool.runOrdAfterUpdate, D]
    hEnc0Le := fun h0 => by simp [hEnc0 h0]
    hEncLe := fun h1 => by simp [hEncNext h1] }⟩

/-- Specification of `rebuildSuffix`: given a valid state up to level `idx` whose order
`chainLevelOrd T G sc bran idx` is a rotation of `G idx`, rebuilding levels `idx, …, P.d`
preserves levels `< idx`, initializes each level `j ∈ [idx, P.d)` with `initOrd` using
`chainLevelOrd`, and builds valid last-level LSFs with the quadratic cost bound. -/
theorem rebuildSuffix_spec_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ)
      (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      idx + rem = P.d →
      (G idx).IsValid →
      (G idx).V ⊆ (G 0).V →
      (G 0).n ≤ N₀ →
      ((G idx).m : ℝ) ≤ (levelM TP P idx : ℝ) →
      LevelLenRange TP P N₀ Λ idx (G idx) ((mkPartialChain T P G sc bran (G idx)).chainLen ℓ₀ idx) →
      (∃ ρ : Rotation (G idx), ρ.order = chainLevelOrd T G sc bran idx) →
      let res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      let G' := res.1
      let sc' := res.2.1
      let bran' := res.2.2.1
      let upd' := res.2.2.2.1
      let cEnc' := res.2.2.2.2.1
      let cDec' := res.2.2.2.2.2.1
      let cFwd' := res.2.2.2.2.2.2.1
      let lastRes := res.2.2.2.2.2.2.2.1
      let lastCost := res.2.2.2.2.2.2.2.2
      (∀ j ≤ idx, G' j = G j) ∧
      (∀ j < idx,
        sc' j = sc j ∧ bran' j = bran j ∧ upd' j = upd j ∧
        cEnc' j = cEnc j ∧ cDec' j = cDec j ∧ cFwd' j = cFwd j) ∧
      (∀ j, idx ≤ j → j < P.d →
        bran' j = 0 ∧ upd' j = 0 ∧
        cEnc' j = 0 ∧ cDec' j = 0 ∧ cFwd' j = 0 ∧
        (G' j).IsValid ∧ (G' j).V ⊆ (G' 0).V ∧
        ((G' j).m : ℝ) ≤ (levelM TP P j : ℝ) ∧
        (∀ e ∈ (G' j).E, 0 < (mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j e) ∧
        sc' j = T.initOrd P.k (levelM TP P j) N₀ (G' j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainGrad g₀ j)
          (chainLevelOrd T G' sc' bran' j) ∧
        G' (j + 1) = T.S (sc' j) 0 ∧
        T.ToolOKAt TP P.k (levelM TP P j) N₀ (G' j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j)) ∧
      (G' P.d).IsValid ∧
      (G' P.d).V ⊆ (G' 0).V ∧
      ((G' P.d).m : ℝ) ≤ (levelM TP P P.d : ℝ) ∧
      (∀ e ∈ (G' P.d).E, 0 < (mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ P.d e) ∧
      0 < lastRes.1 ∧
      (∀ j < lastRes.1, (lastRes.2 j).Holds (G' P.d)
        ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ P.d)
        (LP.σ_last (G' P.d).n)) ∧
      (∀ e ∈ (G' P.d).E,
        (∑ j ∈ Finset.range lastRes.1, (lastRes.2 j).wstr e) / (lastRes.1 : ℝ) ≤
          LP.σ_mwu (G' P.d).n) ∧
      (∀ j < lastRes.1, ∀ u ∈ (G' P.d).V, ∀ v ∈ (G' P.d).V,
        (G' P.d).Connected u v → (lastRes.2 j).F.F.Connected u v) ∧
      ((lastCost : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((G' 0).n : ℝ) + 2)) ^
            LP.p_last) := by
  have hcLast := hLP.2.2.2.2
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  intro rem
  induction rem with
  | zero =>
    intro idx G sc bran upd cEnc cDec cFwd hsum hGValid hGV _hG0n hGm hℓ _hOrd
    have hidx : idx = P.d := by omega
    subst hidx
    dsimp only [rebuildSuffix]
    have hLspec := hL (G P.d) _ hGValid hℓ.pos
    have hGdn : (G P.d).n ≤ (G 0).n := Finset.card_le_card hGV
    have hlog_pos0 : 0 ≤ Real.log (((G P.d).m : ℝ) + ((G P.d).n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (G P.d).m from Nat.cast_nonneg _,
        show (0 : ℝ) ≤ (G P.d).n from Nat.cast_nonneg _])
    have hlog_le : Real.log (((G P.d).m : ℝ) + ((G P.d).n : ℝ) + 2) ≤
        Real.log ((levelM TP P P.d : ℝ) + ((G 0).n : ℝ) + 2) := by
      apply Real.log_le_log (by positivity)
      have hn_real : ((G P.d).n : ℝ) ≤ (G 0).n := by exact_mod_cast hGdn
      linarith
    have hpow_log :
        (Real.log (((G P.d).m : ℝ) + ((G P.d).n : ℝ) + 2)) ^ LP.p_last ≤
          (Real.log ((levelM TP P P.d : ℝ) + ((G 0).n : ℝ) + 2)) ^ LP.p_last :=
      pow_le_pow_left₀ hlog_pos0 hlog_le _
    have hCost' : (L.cost (G P.d) : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((G 0).n : ℝ) + 2)) ^ LP.p_last := by
      refine le_trans hLspec.2.2.2.2 ?_
      apply mul_le_mul _ hpow_log (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hcLast
      have : ((G P.d).m : ℝ) + 1 ≤ (levelM TP P P.d : ℝ) + 1 := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun j hj1 hj2 => absurd hj2 (by omega),
      hGValid, hGV, hGm, hℓ.pos, hLspec.1, hLspec.2.1, hLspec.2.2.1, hLspec.2.2.2.1, hCost'⟩
  | succ rem' ih =>
    intro idx G sc bran upd cEnc cDec cFwd hsum hGValid hGV hG0n hGm hℓ hOrdIdx
    dsimp only [rebuildSuffix]
    set Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    set ℓi := Cpartial.chainLen ℓ₀ idx
    set gi := Cpartial.chainGrad g₀ idx
    set Gi := G idx
    set ordi := chainLevelOrd T G sc bran idx
    set sc_i := T.initOrd P.k (levelM TP P idx) N₀ Gi ℓi gi ordi
    set Gi1 := T.S sc_i 0
    set G1 := fun j => if j = idx + 1 then Gi1 else G j
    set sc1 := fun j => if j = idx then sc_i else sc j
    set bran1 := fun j => if j = idx then 0 else bran j
    set upd1 := fun j => if j = idx then 0 else upd j
    set cEnc1 := fun j => if j = idx then 0 else cEnc j
    set cDec1 := fun j => if j = idx then 0 else cDec j
    set cFwd1 := fun j => if j = idx then 0 else cFwd j
    have hidx_lt : idx < P.d := by omega
    have hℓi_eq : ℓi = (mkPartialChain T P G sc bran Gi).chainLen ℓ₀ idx := by
      apply chainLen_congr_params rfl ℓ₀ (Nat.le_of_lt hidx_lt)
      · intro j _; rfl
      · intro j _; rfl
    have hℓi_rng : LevelLenRange TP P N₀ Λ idx Gi ℓi := by rw [hℓi_eq]; exact hℓ
    have hℓi_pos : ∀ e ∈ Gi.E, 0 < ℓi e := hℓi_rng.pos
    let D0 : DynamicInstance :=
      { G := fun _ => Gi, U := fun _ => [], ℓ := fun _ => ℓi, g := fun _ => gi }
    have hD0ℓ : ∀ s ≤ 0, ∀ e ∈ (D0.G s).E, 0 < D0.ℓ s e := fun _ _ e he => hℓi_pos e he
    have hD0Ord : OrderedUpTo D0 0 2 (fun _ => ordi) := orderedUpTo_zero_of_rotation hOrdIdx
    have hGin : Gi.n ≤ N₀ := le_trans (Finset.card_le_card hGV) hG0n
    have hOK0 : T.ToolOKAt TP P.k (levelM TP P idx) N₀ Gi ℓi :=
      hT idx hidx_lt Gi ℓi hGValid hGin hℓi_rng
    have hSpec0 := hOK0.noHidden P.k 0 (levelM TP P idx) N₀ D0 (fun _ => ordi) (fun _ => [])
      P.hk hGValid (fun _ ht1 ht2 => by omega) (fun _ ht1 ht2 => by omega)
      hD0ℓ hD0Ord (by exact_mod_cast hGm) hGin (fun _ _ _ h => by cases h)
      (by simp [updateThreshold_nonneg]) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hAt0 := hSpec0.1 0 (le_refl 0) 0 P.hk
    dsimp only [D0, SparseCoreRestartTool.runOrdAfterRestarts,
      SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil] at hAt0
    have hHolds0 : (T.lsfs sc_i 0).Holds Gi ℓi (TP.σ P.k Gi.n) := hAt0.1
    have hSp0 : IsSparsifiedCoreGraphAt Gi (T.lsfs sc_i 0) ℓi (P.k : ℝ)
        (TP.γ_ℓ (levelM TP P idx)) (TP.γ_c (levelM TP P idx)) (levelM TP P idx)
        Gi1 (T.emb sc_i 0) := hAt0.2.1
    have hOrd1 : ∃ ρ : Rotation (G1 (idx + 1)), ρ.order = chainLevelOrd T G1 sc1 bran1 (idx + 1) := by
      have hOut := hSpec0.2.2.2.2.1 0 0 (le_refl 0) (le_refl 0) 0 P.hk (Or.inl rfl)
        (fun _ h1 h2 => by omega)
      have hRot := rotation_of_orderedUpTo hOut (le_refl 0)
      refine exists_rotation_of_eq ?_ ?_ hRot
      · simp [SparseCoreRestartTool.coreInstanceOrdFrom,
          SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
          G1, Gi1, sc_i, D0]
      · simp [chainLevelOrd, SparseCoreRestartTool.runOrdAfterRestarts,
          SparseCoreRestartTool.runOrdAfterUpdate, sc1, bran1, sc_i, D0]
    have hGi1_Valid : Gi1.IsValid := by
      have hCore := coreGraph_isValid hGValid hHolds0.2.1
      intro e he
      have hEnd := hSp0.1.2.2 e he
      have hc := hCore e (hSp0.1.2.1 he)
      rw [hEnd.1, hEnd.2]
      exact ⟨hSp0.2.1.1 hc.1, hSp0.2.1.1 hc.2⟩
    have hG1_idx1_Valid : (G1 (idx + 1)).IsValid := by
      simp only [G1, ↓reduceIte]; exact hGi1_Valid
    have hG1_0 : G1 0 = G 0 := by simp [G1]
    have hG1_idx1_V : (G1 (idx + 1)).V ⊆ (G1 0).V := by
      rw [hG1_0]; simp only [G1, ↓reduceIte]
      exact Finset.Subset.trans (Finset.Subset.trans hSp0.1.1 hHolds0.2.1.2.2.1) hGV
    have hG1_idx1_m : ((G1 (idx + 1)).m : ℝ) ≤ (levelM TP P (idx + 1) : ℝ) := by
      simp only [G1, ↓reduceIte]
      have hlm_sq : levelM TP P idx ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk idx
      have hγ_le_M0 : TP.γ_ℓ (levelM TP P idx) ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.2.1 _ _ hlm_sq
      have hcard : (Gi1.m : ℝ) ≤ (levelM TP P idx : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := by
        unfold MGraph.m
        exact le_trans hSp0.2.2.2.2.2 (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hγ_le_M0 (Nat.cast_nonneg _)) hk_pos.le)
      exact_mod_cast levelM_step_nat hTP hγk hcard
    have hℓ1 : LevelLenRange TP P N₀ Λ (idx + 1) (G1 (idx + 1))
        ((mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ (idx + 1)) := by
      intro e he
      simp only [G1, ↓reduceIte] at he
      have heGi : e ∈ Gi.E := (Finset.mem_sdiff.mp (hSp0.1.2.1 he)).1
      have hw1 : 1 ≤ (T.lsfs sc_i 0).wstr e := by
        have hnonneg : ∀ f ∈ Gi.E, 0 ≤ ℓi f := fun f hf => (hℓi_pos f hf).le
        exact le_trans (one_le_stretch hHolds0.2.1.2.2.2.2 hnonneg heGi) (hHolds0.2.2.2 e heGi).1
      have hwσ : (T.lsfs sc_i 0).wstr e ≤ max 2 (TP.σ P.k N₀) :=
        le_trans (hHolds0.2.2.2 e heGi).2
          (le_trans (hTP.2.1 _ _ _ _ le_rfl hGin) (le_max_right _ _))
      have hPre : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ idx = ℓi := by
        apply chainLen_congr_lt ℓ₀ idx (fun j hj => by
          change G1 j = G j; simp [G1, show j ≠ idx + 1 by omega])
        · intro j hj
          have hjlt : j < P.d := by omega
          have hL1 : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).activeLSF j =
              T.lsfs (sc1 j) (bran1 j) := by
            unfold TreeChain.activeLSF
            exact ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hjlt) h
          have hL2 : Cpartial.activeLSF j = T.lsfs (sc j) (bran j) := by
            unfold TreeChain.activeLSF
            exact ite_eq_left_iff.mpr fun h => absurd (by simpa [Cpartial] using hjlt) h
          rw [hL1, hL2]
          simp [sc1, bran1, show j ≠ idx by omega]
      have hLidx : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).activeLSF idx = T.lsfs sc_i 0 := by
        unfold TreeChain.activeLSF
        rw [ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hidx_lt) h]
        simp [mkPartialChain, sc1, bran1]
      have hCL1 : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ (idx + 1) e =
          (T.lsfs sc_i 0).wstr e * ℓi e := by
        change coreLen ((mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).activeLSF idx)
          ((mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ idx) e = _
        rw [hLidx, hPre]
        rfl
      rw [hCL1]
      have hR := hℓi_rng e heGi
      have h0 : 0 ≤ ℓi e := (hℓi_pos e heGi).le
      have hσ0 : 0 ≤ max 2 (TP.σ P.k N₀) := le_trans zero_le_two (le_max_left _ _)
      refine ⟨?_, ?_⟩
      · calc Real.exp (-Λ) ≤ ℓi e := hR.1
          _ = 1 * ℓi e := (one_mul _).symm
          _ ≤ (T.lsfs sc_i 0).wstr e * ℓi e := mul_le_mul_of_nonneg_right hw1 h0
      · calc (T.lsfs sc_i 0).wstr e * ℓi e
            ≤ max 2 (TP.σ P.k N₀) * (Real.exp Λ * max 2 (TP.σ P.k N₀) ^ idx) :=
              mul_le_mul hwσ hR.2 h0 hσ0
          _ = Real.exp Λ * max 2 (TP.σ P.k N₀) ^ (idx + 1) := by rw [pow_succ]; ring
    have hIH := ih (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1 (by omega)
      hG1_idx1_Valid hG1_idx1_V (hG1_0 ▸ hG0n) hG1_idx1_m hℓ1 hOrd1
    rcases hIH with ⟨hIG, hIPre, hISuf, hGdV, hGdSub, hGdm, hGdℓ, hLk, hLH, hLM, hLS, hLC⟩
    have hG'eq : ∀ j ≤ idx,
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j =
          G j := by
      intro j hj
      rw [hIG j (Nat.le_succ_of_le hj)]
      simp [G1, show j ≠ idx + 1 by omega]
    have hG'idx :
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 idx =
          Gi := hG'eq idx (le_refl idx)
    have hPreEq : ∀ j < idx,
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 j = sc j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.1 j = bran j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.1 j = upd j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.2.1 j = cEnc j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.2.2.1 j = cDec j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.2.2.2.1 j = cFwd j := by
      intro j hj
      have hj1 : j < idx + 1 := Nat.lt_succ_of_lt hj
      have hne : j ≠ idx := Nat.ne_of_lt hj
      rcases hIPre j hj1 with ⟨a1, a2, a3, a4, a5, a6⟩
      simp only [sc1, bran1, upd1, cEnc1, cDec1, cFwd1, hne, ↓reduceIte]
        at a1 a2 a3 a4 a5 a6
      exact ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨hG'eq, hPreEq, fun j hj1 hj2 => ?_, hGdV, hGdSub, hGdm, hGdℓ, hLk, hLH, hLM, hLS, hLC⟩
    by_cases hjeq : j = idx
    · subst hjeq
      have hlt1 : j < j + 1 := Nat.lt_succ_self j
      rcases hIPre j hlt1 with ⟨a1, a2, a3, a4, a5, a6⟩
      simp only [sc1, bran1, upd1, cEnc1, cDec1, cFwd1, ↓reduceIte] at a1 a2 a3 a4 a5 a6
      set res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1
      have hG_0 : res.1 0 = G1 0 := hIG 0 (Nat.zero_le _)
      have hG_j1 : res.1 (j + 1) = Gi1 := by
        rw [hIG (j + 1) (le_refl _)]; simp [G1]
      have hCL : (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen ℓ₀ j = ℓi := by
        symm
        apply chainLen_congr_params rfl ℓ₀ (Nat.le_of_lt hj2)
        · intro m hm; rw [hG'eq m (Nat.le_of_lt hm)]
        · intro m hm
          rcases hPreEq m hm with ⟨hm1, hm2, _⟩
          rw [hm1, hm2]
      have hCG : (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad g₀ j = gi := by
        symm
        apply chainGrad_congr_params rfl g₀ (Nat.le_of_lt hj2)
        · intro m hm; rw [hG'eq m (Nat.le_of_lt hm)]
        · intro m hm
          rcases hPreEq m hm with ⟨hm1, hm2, _⟩
          rw [hm1, hm2]
      have hOrdEq : chainLevelOrd T res.1 res.2.1 res.2.2.1 j = ordi := by
        dsimp only [ordi]
        unfold chainLevelOrd
        cases j with
        | zero => simp only [↓reduceIte, hG_0, hG1_0]
        | succ m =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          rcases hPreEq m (Nat.lt_succ_self m) with ⟨hm1, hm2, _⟩
          rw [hm1, hm2]
      refine ⟨a2, a3, a4, a5, a6,
        by rw [hG'idx]; exact hGValid,
        by rw [hG'idx, hG_0, hG1_0]; exact hGV,
        by rw [hG'idx]; exact hGm,
        by rw [hCL, hG'idx]; exact hℓi_pos,
        by rw [a1, hG'idx, hCL, hCG, hOrdEq],
        by rw [hG_j1, a1],
        by rw [hG'idx, hCL]; exact hOK0⟩
    · exact hISuf j (by omega) hj2

/-- Every level `j ∈ [idx, P.d)` rebuilt by `rebuildSuffix` carries a valid rotation witness for
`chainLevelOrd`. -/
lemma rebuildSuffix_levelOrd_rotation (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (ℓ₀ g₀ : ℕ → ℝ)
    (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ)
    (hsum : idx + rem = P.d)
    (hGValid : (G idx).IsValid)
    (hGV : (G idx).V ⊆ (G 0).V)
    (hG0n : (G 0).n ≤ N₀)
    (hGm : ((G idx).m : ℝ) ≤ (levelM TP P idx : ℝ))
    (hℓ : LevelLenRange TP P N₀ Λ idx (G idx)
      ((mkPartialChain T P G sc bran (G idx)).chainLen ℓ₀ idx))
    (hOrdIdx : ∃ ρ : Rotation (G idx), ρ.order = chainLevelOrd T G sc bran idx) :
    let res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
    ∀ j, idx ≤ j → j < P.d →
      ∃ ρ : Rotation (res.1 j), ρ.order = chainLevelOrd T res.1 res.2.1 res.2.2.1 j := by
  have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk ℓ₀ g₀ rem idx
    G sc bran upd cEnc cDec cFwd hsum hGValid hGV hG0n hGm hℓ hOrdIdx
  dsimp only at hRS ⊢
  set res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
  rcases hRS with ⟨hIG, hIPre, hISuf, _⟩
  intro j
  induction j with
  | zero =>
    intro h0 _
    have hidx0 : idx = 0 := Nat.le_zero.mp h0
    subst hidx0
    exact ⟨sortedRotation (res.1 0), rfl⟩
  | succ m ih =>
    intro hm1 hm2
    by_cases hmeq : m + 1 = idx
    · subst hmeq
      refine exists_rotation_of_eq (hIG (m + 1) (le_refl _)).symm ?_ hOrdIdx
      unfold chainLevelOrd
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rcases hIPre m (Nat.lt_succ_self m) with ⟨hm1', hm2', _⟩
      rw [hm1', hm2']
    · have hm_ge : idx ≤ m := by omega
      have hm_lt : m < P.d := Nat.lt_of_succ_lt hm2
      have hOrdM := ih hm_ge hm_lt
      rcases hISuf m hm_ge hm_lt with ⟨hb, _, _, _, _, hGVm, hSubVm, hGmm, hℓm, hscm, hSm, hOKm⟩
      let Dm : DynamicInstance :=
        { G := fun _ => res.1 m
          U := fun _ => []
          ℓ := fun _ => (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen ℓ₀ m
          g := fun _ => (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad g₀ m }
      have hGmn : (res.1 m).n ≤ N₀ := by
        refine le_trans (Finset.card_le_card ?_) hG0n
        simpa [hIG 0 (Nat.zero_le _)] using hSubVm
      have hSpecm := hOKm.noHidden P.k 0 (levelM TP P m) N₀ Dm
        (fun _ => chainLevelOrd T res.1 res.2.1 res.2.2.1 m) (fun _ => [])
        P.hk hGVm (fun _ ht1 ht2 => by omega) (fun _ ht1 ht2 => by omega)
        (fun _ _ e he => hℓm e he) (orderedUpTo_zero_of_rotation hOrdM)
        (by exact_mod_cast hGmm) hGmn (fun _ _ _ h => by cases h)
        (by simp [updateThreshold_nonneg]) ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hOut := hSpecm.2.2.2.2.1 0 0 (le_refl 0) (le_refl 0) 0 P.hk (Or.inl rfl)
        (fun _ h1 h2 => by omega)
      have hRot := rotation_of_orderedUpTo hOut (le_refl 0)
      refine exists_rotation_of_eq ?_ ?_ hRot
      · simp only [SparseCoreRestartTool.coreInstanceOrdFrom,
          SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
          List.foldl_nil, Dm]
        rw [← hscm, ← hSm]
      · simp only [SparseCoreRestartTool.runOrdAfterRestarts,
          SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil, Dm]
        rw [← hscm]
        simp only [chainLevelOrd, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, hb]

end RebuildSuffixSpec

end MinCostFlow.Chain.Ordered
