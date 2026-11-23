module

public import MinCostFlow.MinRatio.OrdSolverToolMono
public import MinCostFlow.MinRatio.OrdSolverReached
public import MinCostFlow.MinRatio.ShiftQuotaWriter
public import MinCostFlow.Chain.Ordered.Theorem5_1Helpers
import Mathlib.Tactic

/-!
# Unified rebuild-driven cap, deposit, and forward potential for chain runtime and tree updates

Replaces `shiftCount` in `alg2RuntimeBoundSR` and `alg2TreeUpdatesBoundSR` (Theorem 5.1,
`Chain/Ordered/Theorem5_1Helpers.lean`) by `gameShiftBoundNat` (`ShiftQuotaWriter.lean`), giving
exact natural upper bounds `runtimeCap` and `treeUpdateCap` on every reached state
(`OrdSolverReached.runtime_and_tree_le_cap`).

Because `chainRebuildCap` depends only on `rebuildCount`, it is invariant under `Shift(i)` and
rises by `C_fac * rebuildCapUnitGain cfg i₀` on a rebuild at level `i₀`. The deposit
`chainCapDeposit` and forward potential `capFwdPotential` pay those rebuild gains from updates
(`algorithm1_update_cap_amortized`), while shifts never raise them (`algorithm2_loopWith_cap_le`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain Chain.Ordered SparseCore SparseCore.Program Bundle

/-! ## 3. Unified rebuild-driven cap, deposit, and forward potential -/

/-- The overhead factor of `alg2TreeUpdatesBoundSR` (Lemma 5.11, page 20). -/
@[expose] noncomputable def alg2TreeUpdatesFactor (cfg : Alg2Config) : ℝ :=
  (14 * (cfg.P.d : ℝ) + 36) *
    (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1)

/-- Integer ceiling of `lemma511TimeFactor`. -/
@[expose] noncomputable def runtimeFactorNat (cfg : Alg2Config) : ℕ :=
  ⌈lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀⌉₊

/-- Integer ceiling of `alg2TreeUpdatesFactor`. -/
@[expose] noncomputable def treeUpdateFactorNat (cfg : Alg2Config) : ℕ :=
  ⌈alg2TreeUpdatesFactor cfg⌉₊

/-- Exact `ℕ` rebuild-driven cap replacing `shiftCount` with `gameShiftBoundNat`. -/
@[expose] noncomputable def chainRebuildCap (cfg : Alg2Config) (C_fac : ℕ) (rc : ℕ → ℕ) : ℕ :=
  C_fac * (cfg.P.M₀ + ∑ i ∈ Finset.range (cfg.P.d + 1),
    (gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) rc i + rc i) *
      ⌈powTerm cfg.P i⌉₊)

/-- Exact `ℕ` upper bound on `model.chain.totalRuntime` for reached states. -/
@[expose] noncomputable def runtimeCap (cfg : Alg2Config) (model : Alg2State cfg) : ℕ :=
  chainRebuildCap cfg (runtimeFactorNat cfg) model.chain.rebuildCount + ⌈model.largeBatchEnc⌉₊

/-- Exact `ℕ` upper bound on `model.chain.totalTreeUpdates` for reached states. -/
@[expose] noncomputable def treeUpdateCap (cfg : Alg2Config) (model : Alg2State cfg) : ℕ :=
  chainRebuildCap cfg (treeUpdateFactorNat cfg) model.chain.rebuildCount

private theorem sum_shift_rebuild_le_cap (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P)
    (hSh : ∀ i : Fin (cfg.P.d + 1),
      (ch.shiftCount i.val : ℝ) ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val) :
    (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        ((ch.shiftCount i + ch.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i ≤
      ((cfg.P.M₀ + ∑ i ∈ Finset.range (cfg.P.d + 1),
        (gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) ch.rebuildCount i +
          ch.rebuildCount i) * ⌈powTerm cfg.P i⌉₊ : ℕ) : ℝ) := by
  push_cast
  refine add_le_add le_rfl (Finset.sum_le_sum fun i hi => ?_)
  have hiLt : i < cfg.P.d + 1 := Finset.mem_range.mp hi
  have hsh : (ch.shiftCount i : ℝ) ≤
      (gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) ch.rebuildCount i : ℝ) := by
    rw [← gameShiftBound_eq_natCast]
    exact hSh ⟨i, hiLt⟩
  have hp0 : 0 ≤ powTerm cfg.P i := by unfold powTerm; positivity
  have hp : powTerm cfg.P i ≤ (⌈powTerm cfg.P i⌉₊ : ℝ) := Nat.le_ceil _
  exact mul_le_mul (by linarith) hp hp0 (by positivity)

/-- On every reached state, `totalRuntime ≤ runtimeCap` and `totalTreeUpdates ≤ treeUpdateCap`. -/
theorem OrdSolverReached.runtime_and_tree_le_cap {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀) :
    model.chain.totalRuntime ≤ runtimeCap cfg model ∧
    model.chain.totalTreeUpdates ≤ treeUpdateCap cfg model := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  have hComp := Ordered.theorem_5_1_uncond_complexity_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)
  rw [← hm] at hComp
  obtain ⟨hRt, hTu, hSh, _⟩ := hComp
  have hsum := sum_shift_rebuild_le_cap cfg model.chain hSh
  have hsumNN : 0 ≤ (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
      ((model.chain.shiftCount i + model.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i :=
    add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (by unfold powTerm; positivity))
  refine ⟨?_, ?_⟩
  · have hrtR : (model.chain.totalRuntime : ℝ) ≤ (runtimeCap cfg model : ℝ) := by
      have hC := Nat.le_ceil (lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀)
      have hE := Nat.le_ceil model.largeBatchEnc
      have hmul := mul_le_mul hC hsum hsumNN (Nat.cast_nonneg _)
      unfold Ordered.alg2RuntimeBoundSR at hRt
      unfold runtimeCap chainRebuildCap runtimeFactorNat
      push_cast at hRt hmul ⊢
      linarith
    exact_mod_cast hrtR
  · have htuR : (model.chain.totalTreeUpdates : ℝ) ≤ (treeUpdateCap cfg model : ℝ) := by
      have hC := Nat.le_ceil (alg2TreeUpdatesFactor cfg)
      have hmul := mul_le_mul hC hsum hsumNN (Nat.cast_nonneg _)
      unfold Chain.alg2TreeUpdatesBoundSR at hTu
      unfold alg2TreeUpdatesFactor at hmul
      unfold treeUpdateCap chainRebuildCap treeUpdateFactorNat alg2TreeUpdatesFactor
      push_cast at hTu hmul ⊢
      linarith
    exact_mod_cast htuR

/-- Unit gain added to `chainRebuildCap cfg 1` by one rebuild at level `i₀`. -/
@[expose] noncomputable def rebuildCapUnitGain (cfg : Alg2Config) (i₀ : ℕ) : ℕ :=
  (if i₀ ≤ cfg.P.d then ⌈powTerm cfg.P i₀⌉₊ else 0) +
    ∑ i ∈ Finset.range (cfg.P.d + 1),
      if i₀ ≤ i then
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1 - i₀) * ⌈powTerm cfg.P i⌉₊
      else 0

private theorem gameShiftBoundNat_rebuild_increment (B : ℕ) (rc : ℕ → ℕ) (i₀ i : ℕ) :
    gameShiftBoundNat B (fun j => if j = i₀ then rc i₀ + 1 else rc j) i =
      gameShiftBoundNat B rc i + if i₀ ≤ i then B ^ (i + 1 - i₀) else 0 := by
  unfold gameShiftBoundNat
  have hsum : ∑ j ∈ Finset.range (i + 1),
        (if j = i₀ then rc i₀ + 1 else rc j) * B ^ (i + 1 - j) =
      (∑ j ∈ Finset.range (i + 1), rc j * B ^ (i + 1 - j)) +
        if i₀ ≤ i then B ^ (i + 1 - i₀) else 0 := by
    have hsplit : ∑ j ∈ Finset.range (i + 1),
          (if j = i₀ then rc i₀ + 1 else rc j) * B ^ (i + 1 - j) =
        ∑ j ∈ Finset.range (i + 1),
          (rc j * B ^ (i + 1 - j) + if j = i₀ then B ^ (i + 1 - j) else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = i₀
      · subst hj; simp [Nat.add_mul]
      · simp [hj]
    rw [hsplit, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq']
    by_cases hle : i₀ ≤ i
    · have hm : i₀ ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
      simp [hm, hle]
    · have hm : i₀ ∉ Finset.range (i + 1) := by simp only [Finset.mem_range]; omega
      simp [hm, hle]
  rw [hsum]
  omega

/-- Exact increment of `chainRebuildCap` when `rebuildCount` increments at `i₀`. -/
theorem chainRebuildCap_rebuild_eq (cfg : Alg2Config) (C_fac : ℕ) (rc : ℕ → ℕ) (i₀ : ℕ) :
    chainRebuildCap cfg C_fac (fun j => if j = i₀ then rc i₀ + 1 else rc j) =
      chainRebuildCap cfg C_fac rc + C_fac * rebuildCapUnitGain cfg i₀ := by
  unfold chainRebuildCap rebuildCapUnitGain
  rw [← Nat.mul_add]
  congr 1
  have hsum : ∑ i ∈ Finset.range (cfg.P.d + 1),
        (gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k)
          (fun j => if j = i₀ then rc i₀ + 1 else rc j) i +
          (if i = i₀ then rc i₀ + 1 else rc i)) * ⌈powTerm cfg.P i⌉₊ =
      (∑ i ∈ Finset.range (cfg.P.d + 1),
        (gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) rc i + rc i) *
          ⌈powTerm cfg.P i⌉₊) +
      (if i₀ ≤ cfg.P.d then ⌈powTerm cfg.P i₀⌉₊ else 0) +
      ∑ i ∈ Finset.range (cfg.P.d + 1),
        if i₀ ≤ i then
          shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1 - i₀) * ⌈powTerm cfg.P i⌉₊
        else 0 := by
    have hcongr : ∑ i ∈ Finset.range (cfg.P.d + 1),
          (gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k)
            (fun j => if j = i₀ then rc i₀ + 1 else rc j) i +
            (if i = i₀ then rc i₀ + 1 else rc i)) * ⌈powTerm cfg.P i⌉₊ =
        ∑ i ∈ Finset.range (cfg.P.d + 1),
          ((gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) rc i + rc i) *
              ⌈powTerm cfg.P i⌉₊ +
            (if i = i₀ then ⌈powTerm cfg.P i⌉₊ else 0) +
            (if i₀ ≤ i then
              shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1 - i₀) * ⌈powTerm cfg.P i⌉₊
            else 0)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gameShiftBoundNat_rebuild_increment]
      by_cases h1 : i = i₀
      · subst h1; simp only [↓reduceIte, le_rfl]; ring
      · by_cases h2 : i₀ ≤ i <;> simp only [h1, h2, ↓reduceIte] <;> ring
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 2
    rw [Finset.sum_ite_eq']
    by_cases hle : i₀ ≤ cfg.P.d
    · have hm : i₀ ∈ Finset.range (cfg.P.d + 1) := Finset.mem_range.mpr (by omega)
      simp [hm, hle]
    · have hm : i₀ ∉ Finset.range (cfg.P.d + 1) := by simp only [Finset.mem_range]; omega
      simp [hm, hle]
  rw [hsum]
  omega

/-- Deposit per update counted at level `i` for the rebuild cap unit gain. -/
@[expose] noncomputable def capDeposit (cfg : Alg2Config) (i : ℕ) : ℕ :=
  (rebuildCapUnitGain cfg i + intRebuildThreshold cfg.P cfg.N₀ i) /
    (intRebuildThreshold cfg.P cfg.N₀ i + 1)

theorem rebuildCapUnitGain_le_deposit (cfg : Alg2Config) (i : ℕ) :
    rebuildCapUnitGain cfg i ≤ capDeposit cfg i * (intRebuildThreshold cfg.P cfg.N₀ i + 1) := by
  unfold capDeposit
  have h := Nat.lt_div_mul_add
    (a := rebuildCapUnitGain cfg i + intRebuildThreshold cfg.P cfg.N₀ i)
    (b := intRebuildThreshold cfg.P cfg.N₀ i + 1) (by omega)
  omega

/-- Chain-level deposit held in `updCount` for `chainRebuildCap cfg 1`. -/
@[expose] noncomputable def chainCapDeposit (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) : ℕ :=
  ∑ i ∈ Finset.range cfg.P.d, capDeposit cfg i * ch.updCount i

/-- Cumulative deeper-level deposit for updates forwarded below `idx`. -/
@[expose] noncomputable def capDeeperDeposit (cfg : Alg2Config) (idx : ℕ)
    (ch : ChainState cfg.T cfg.P) : ℕ :=
  ∑ i ∈ (Finset.range cfg.P.d).filter (fun i => idx < i), capDeposit cfg i * ch.recUpdates i

/-- Forward weight `W_i = ∑_{i ≤ j < d} Γ^{j - i} capDeposit j`. -/
@[expose] noncomputable def capFwdWeight (cfg : Alg2Config) (Γ i : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico i cfg.P.d, Γ ^ (j - i) * capDeposit cfg j

theorem capFwdWeight_succ (cfg : Alg2Config) (Γ : ℕ) {i : ℕ} (hi : i < cfg.P.d) :
    capFwdWeight cfg Γ i = capDeposit cfg i + Γ * capFwdWeight cfg Γ (i + 1) := by
  unfold capFwdWeight
  rw [Finset.sum_eq_sum_Ico_succ_bot hi, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := (Finset.mem_Ico.mp hj).1
  rw [show j - i = (j - (i + 1)) + 1 by omega, pow_succ]
  ring

theorem capFwdWeight_of_le (cfg : Alg2Config) (Γ : ℕ) {i : ℕ} (hi : cfg.P.d ≤ i) :
    capFwdWeight cfg Γ i = 0 := by
  unfold capFwdWeight
  rw [Finset.Ico_eq_empty_of_le hi, Finset.sum_empty]

/-- Forward potential paying deeper-level `capDeposit` from recourse. -/
@[expose] noncomputable def capFwdPotential (cfg : Alg2Config) (Γ : ℕ)
    (ch : ChainState cfg.T cfg.P) : ℕ :=
  ∑ j ∈ Finset.range cfg.P.d, capFwdWeight cfg Γ (j + 1) * (Γ * ch.updCount j - ch.curFwd j)

private theorem chainCapDeposit_rebuild (cfg : Alg2Config) (ch ch' : ChainState cfg.T cfg.P)
    {i₀ : ℕ} (hi : i₀ < cfg.P.d)
    (hupd : ∀ j, ch'.updCount j = if i₀ ≤ j ∧ j < cfg.P.d then 0 else ch.updCount j) :
    chainCapDeposit cfg ch' + capDeposit cfg i₀ * ch.updCount i₀ ≤ chainCapDeposit cfg ch := by
  unfold chainCapDeposit
  have hmem : i₀ ∈ Finset.range cfg.P.d := Finset.mem_range.mpr hi
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have hzero : ch'.updCount i₀ = 0 := by rw [hupd i₀, ite_eq_left ⟨le_rfl, hi⟩]
  rw [hzero, mul_zero, zero_add]
  have hrest : ∑ x ∈ (Finset.range cfg.P.d).erase i₀, capDeposit cfg x * ch'.updCount x ≤
      ∑ x ∈ (Finset.range cfg.P.d).erase i₀, capDeposit cfg x * ch.updCount x := by
    refine Finset.sum_le_sum fun x hx => ?_
    rw [hupd x]
    split_ifs
    · exact Nat.zero_le _
    · exact le_rfl
  omega

private theorem capDeeperDeposit_split (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P)
    {idx : ℕ} (hidx : idx + 1 < cfg.P.d) :
    capDeeperDeposit cfg idx ch =
      capDeposit cfg (idx + 1) * ch.recUpdates (idx + 1) + capDeeperDeposit cfg (idx + 1) ch := by
  unfold capDeeperDeposit
  have hmem : idx + 1 ∈ (Finset.range cfg.P.d).filter (fun i => idx < i) := by
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [← Finset.add_sum_erase _ _ hmem]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
  omega

private theorem capDeeperDeposit_eq_of_ge (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P)
    {idx : ℕ} (hidx : cfg.P.d ≤ idx + 1) :
    capDeeperDeposit cfg idx ch = 0 := by
  unfold capDeeperDeposit
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  omega

private theorem updateLoop_cap_deposit (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (enc : ℕ),
      idx + rem = cfg.P.d →
      let st' := (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem idx st curG curU enc).1
      chainRebuildCap cfg 1 st'.rebuildCount + chainCapDeposit cfg st' ≤
        chainRebuildCap cfg 1 st.rebuildCount + chainCapDeposit cfg st +
          (if idx < cfg.P.d then capDeposit cfg idx * curU.length else 0) +
          (capDeeperDeposit cfg idx st' - capDeeperDeposit cfg idx st)
  | 0, idx, st, curG, curU, _, hsum => by
    dsimp only [Ordered.updateLoop]
    have hge : cfg.P.d ≤ idx := by omega
    rw [ite_eq_right (by omega : ¬ idx < cfg.P.d)]
    split_ifs <;>
      (change chainRebuildCap cfg 1 st.rebuildCount + chainCapDeposit cfg st ≤
        chainRebuildCap cfg 1 st.rebuildCount + chainCapDeposit cfg st + 0 +
          (capDeeperDeposit cfg idx st - capDeeperDeposit cfg idx st); omega)
  | rem + 1, idx, st, curG, curU, enc, hsum => by
    have hidx : idx < cfg.P.d := by omega
    dsimp only [Ordered.updateLoop]
    rw [ite_eq_left hidx]
    split_ifs with hTh
    · set stWithLG : ChainState cfg.T cfg.P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      obtain ⟨hrc, _, hrec, hupd⟩ :=
        algorithm1_rebuild_counts cfg.T cfg.L cfg.P stWithLG hidx (rebuildStartGraph idx curG) enc
      set st' := (Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stWithLG idx
        (rebuildStartGraph idx curG) enc).1
      have hcap : chainRebuildCap cfg 1 st'.rebuildCount =
          chainRebuildCap cfg 1 st.rebuildCount + rebuildCapUnitGain cfg idx := by
        rw [hrc]
        simpa [stWithLG] using chainRebuildCap_rebuild_eq cfg 1 st.rebuildCount idx
      have hdep := chainCapDeposit_rebuild cfg st st' hidx hupd
      have hgain : rebuildCapUnitGain cfg idx ≤
          capDeposit cfg idx * st.updCount idx + capDeposit cfg idx * curU.length := by
        have h1 := rebuildCapUnitGain_le_deposit cfg idx
        have h2 : intRebuildThreshold cfg.P cfg.N₀ idx + 1 ≤ st.updCount idx + curU.length := by
          omega
        have h3 := Nat.mul_le_mul_left (capDeposit cfg idx) h2
        rw [Nat.mul_add (capDeposit cfg idx) (st.updCount idx)] at h3
        exact h1.trans h3
      omega
    · let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
        (Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)
      let sc' := updRes.1
      let nextG := cfg.T.S sc' (st.bran idx)
      let nextU := updRes.2 (st.bran idx)
      let fiChanges := diffTreeChanges
        (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E (cfg.T.lsfs sc' (st.bran idx)).F.F.E
      let nextEnc := (st.G (idx + 1)).batchEnc nextU
      set stNext : ChainState cfg.T cfg.P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j => if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + enc
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      set stEnd := (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
        stNext nextG nextU 0).1
      have ih := updateLoop_cap_deposit cfg ℓ' g' rem (idx + 1) stNext nextG nextU 0 (by omega)
      have hdepNext : chainCapDeposit cfg stNext =
          chainCapDeposit cfg st + capDeposit cfg idx * curU.length := by
        unfold chainCapDeposit
        have hmem : idx ∈ Finset.range cfg.P.d := Finset.mem_range.mpr hidx
        rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
        have hrest : ∑ x ∈ (Finset.range cfg.P.d).erase idx, capDeposit cfg x * stNext.updCount x =
            ∑ x ∈ (Finset.range cfg.P.d).erase idx, capDeposit cfg x * st.updCount x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hne : x ≠ idx := (Finset.mem_erase.mp hx).1
          simp only [stNext, ite_eq_right hne]
        rw [hrest]
        simp only [stNext, ↓reduceIte, Nat.mul_add]
        omega
      have hrcNext : stNext.rebuildCount = st.rebuildCount := rfl
      have hrecMono : ∀ j, stNext.recUpdates j ≤ stEnd.recUpdates j :=
        fun j => updateLoop_recUpdates_mono cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
          stNext nextG nextU 0 j
      have hdeepLe : capDeeperDeposit cfg (idx + 1) stNext ≤ capDeeperDeposit cfg (idx + 1) stEnd :=
        Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hrecMono j)
      have hdeepEq : capDeeperDeposit cfg (idx + 1) stNext = capDeeperDeposit cfg (idx + 1) st := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hgt : idx + 1 < j := (Finset.mem_filter.mp hj).2
        simp only [stNext, ite_eq_right (by omega : j ≠ idx + 1)]
      have hrecEq : stEnd.recUpdates (idx + 1) = st.recUpdates (idx + 1) + nextU.length := by
        have hlow := (updateLoop_low cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
          stNext nextG nextU 0 (by omega)).2 (idx + 1) le_rfl
        simpa [stEnd, stNext] using hlow
      change chainRebuildCap cfg 1 stEnd.rebuildCount + chainCapDeposit cfg stEnd ≤
        chainRebuildCap cfg 1 stNext.rebuildCount + chainCapDeposit cfg stNext +
          (if idx + 1 < cfg.P.d then capDeposit cfg (idx + 1) * nextU.length else 0) +
          (capDeeperDeposit cfg (idx + 1) stEnd - capDeeperDeposit cfg (idx + 1) stNext) at ih
      by_cases hidx1 : idx + 1 < cfg.P.d
      · rw [ite_eq_left hidx1] at ih
        rw [capDeeperDeposit_split cfg stEnd hidx1, capDeeperDeposit_split cfg st hidx1, hrecEq,
          Nat.mul_add]
        rw [hdepNext, hrcNext, hdeepEq] at ih
        rw [hdeepEq] at hdeepLe
        omega
      · rw [ite_eq_right hidx1] at ih
        rw [capDeeperDeposit_eq_of_ge cfg stEnd (by omega),
          capDeeperDeposit_eq_of_ge cfg st (by omega)]
        rw [hdepNext, hrcNext, hdeepEq,
          capDeeperDeposit_eq_of_ge cfg stEnd (by omega),
          capDeeperDeposit_eq_of_ge cfg st (by omega)] at ih
        omega

private theorem capFwd_rebuild_le (cfg : Alg2Config) (Γ : ℕ) (ch ch' : ChainState cfg.T cfg.P)
    {i₀ : ℕ} (_hi : i₀ < cfg.P.d)
    (hupd : ∀ j, ch'.updCount j = if i₀ ≤ j ∧ j < cfg.P.d then 0 else ch.updCount j)
    (hfwd : ∀ j, ch'.curFwd j = if i₀ ≤ j ∧ j < cfg.P.d then 0 else ch.curFwd j) :
    capFwdPotential cfg Γ ch' ≤ capFwdPotential cfg Γ ch := by
  unfold capFwdPotential
  refine Finset.sum_le_sum fun j _ => ?_
  rw [hupd j, hfwd j]
  split_ifs
  · simp
  · exact le_rfl

private theorem updateLoop_cap_fwd (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (Γ : ℕ) :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (enc : ℕ),
      idx + rem = cfg.P.d →
      FwdBoundNat cfg.P Γ st →
      let st' := (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem idx st curG curU enc).1
      FwdBoundNat cfg.P Γ st' →
      capFwdPotential cfg Γ st' + (capDeeperDeposit cfg idx st' - capDeeperDeposit cfg idx st) ≤
        capFwdPotential cfg Γ st + Γ * capFwdWeight cfg Γ (idx + 1) * curU.length
  | 0, idx, st, curG, curU, _, hsum, _, _ => by
    dsimp only [Ordered.updateLoop]
    split_ifs <;>
      (change capFwdPotential cfg Γ st + (capDeeperDeposit cfg idx st - capDeeperDeposit cfg idx st) ≤
        capFwdPotential cfg Γ st + Γ * capFwdWeight cfg Γ (idx + 1) * curU.length; omega)
  | rem + 1, idx, st, curG, curU, enc, hsum, hB, hA => by
    have hidx : idx < cfg.P.d := by omega
    dsimp only [Ordered.updateLoop] at hA ⊢
    split_ifs at hA ⊢ with hTh
    · set stWithLG : ChainState cfg.T cfg.P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      obtain ⟨_, _, hrec, hupd⟩ :=
        algorithm1_rebuild_counts cfg.T cfg.L cfg.P stWithLG hidx (rebuildStartGraph idx curG) enc
      have hfwd := algorithm1_rebuild_curFwd cfg.T cfg.L cfg.P stWithLG hidx
        (rebuildStartGraph idx curG) enc
      have hdeep : capDeeperDeposit cfg idx
          (Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stWithLG idx
            (rebuildStartGraph idx curG) enc).1 = capDeeperDeposit cfg idx st := by
        unfold capDeeperDeposit; rw [hrec]
      rw [hdeep, Nat.sub_self, Nat.add_zero]
      exact (capFwd_rebuild_le cfg Γ st _ hidx hupd hfwd).trans (Nat.le_add_right _ _)
    · let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
        (Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)
      let sc' := updRes.1
      let nextG := cfg.T.S sc' (st.bran idx)
      let nextU := updRes.2 (st.bran idx)
      let fiChanges := diffTreeChanges
        (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E (cfg.T.lsfs sc' (st.bran idx)).F.F.E
      let nextEnc := (st.G (idx + 1)).batchEnc nextU
      set stNext : ChainState cfg.T cfg.P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j => if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + enc
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      set stEnd := (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
        stNext nextG nextU 0).1
      have hlow := (updateLoop_low cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
        stNext nextG nextU 0 (by omega)).1 idx (by omega)
      have hBNext : FwdBoundNat cfg.P Γ stNext := by
        intro j hj
        by_cases hji : j = idx
        · subst hji
          have hEnd := hA j hj
          rw [hlow.1, hlow.2] at hEnd
          exact hEnd
        · simpa [stNext, hji] using hB j hj
      have ih := updateLoop_cap_fwd cfg ℓ' g' Γ rem (idx + 1) stNext nextG nextU 0
        (by omega) hBNext hA
      have hfwdStep : capFwdPotential cfg Γ stNext + capFwdWeight cfg Γ (idx + 1) * nextU.length =
          capFwdPotential cfg Γ st + Γ * capFwdWeight cfg Γ (idx + 1) * curU.length := by
        unfold capFwdPotential
        have hmem : idx ∈ Finset.range cfg.P.d := Finset.mem_range.mpr hidx
        rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
        have hrest : ∑ j ∈ (Finset.range cfg.P.d).erase idx,
              capFwdWeight cfg Γ (j + 1) * (Γ * stNext.updCount j - stNext.curFwd j) =
            ∑ j ∈ (Finset.range cfg.P.d).erase idx,
              capFwdWeight cfg Γ (j + 1) * (Γ * st.updCount j - st.curFwd j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : j ≠ idx := (Finset.mem_erase.mp hj).1
          simp only [stNext, ite_eq_right hne]
        rw [hrest]
        have hle1 : st.curFwd idx ≤ Γ * st.updCount idx := hB idx hidx
        have hle2 : st.curFwd idx + nextU.length ≤ Γ * (st.updCount idx + curU.length) := by
          simpa [stNext] using hBNext idx hidx
        have hterm : capFwdWeight cfg Γ (idx + 1) *
              (Γ * (st.updCount idx + curU.length) - (st.curFwd idx + nextU.length)) +
              capFwdWeight cfg Γ (idx + 1) * nextU.length =
            capFwdWeight cfg Γ (idx + 1) * (Γ * st.updCount idx - st.curFwd idx) +
              Γ * capFwdWeight cfg Γ (idx + 1) * curU.length := by
          have hsub : (Γ * (st.updCount idx + curU.length) - (st.curFwd idx + nextU.length)) +
              nextU.length = (Γ * st.updCount idx - st.curFwd idx) + Γ * curU.length := by
            rw [Nat.mul_add] at hle2 ⊢; omega
          calc _ = capFwdWeight cfg Γ (idx + 1) *
                ((Γ * (st.updCount idx + curU.length) - (st.curFwd idx + nextU.length)) +
                  nextU.length) := by rw [← Nat.mul_add]
            _ = capFwdWeight cfg Γ (idx + 1) *
                ((Γ * st.updCount idx - st.curFwd idx) + Γ * curU.length) := by rw [hsub]
            _ = _ := by rw [Nat.mul_add]; ring
        simp only [stNext, ↓reduceIte]
        omega
      have hdeepEq : capDeeperDeposit cfg (idx + 1) stNext = capDeeperDeposit cfg (idx + 1) st := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hgt : idx + 1 < j := (Finset.mem_filter.mp hj).2
        simp only [stNext, ite_eq_right (by omega : j ≠ idx + 1)]
      have hrecMono : ∀ j, stNext.recUpdates j ≤ stEnd.recUpdates j :=
        fun j => updateLoop_recUpdates_mono cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
          stNext nextG nextU 0 j
      have hdeepLe : capDeeperDeposit cfg (idx + 1) stNext ≤ capDeeperDeposit cfg (idx + 1) stEnd :=
        Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hrecMono j)
      have hrecEq : stEnd.recUpdates (idx + 1) = st.recUpdates (idx + 1) + nextU.length := by
        have hlowR := (updateLoop_low cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem (idx + 1)
          stNext nextG nextU 0 (by omega)).2 (idx + 1) le_rfl
        simpa [stEnd, stNext] using hlowR
      change capFwdPotential cfg Γ stEnd +
          (capDeeperDeposit cfg (idx + 1) stEnd - capDeeperDeposit cfg (idx + 1) stNext) ≤
        capFwdPotential cfg Γ stNext + Γ * capFwdWeight cfg Γ (idx + 2) * nextU.length at ih
      by_cases hidx1 : idx + 1 < cfg.P.d
      · have hw := capFwdWeight_succ cfg Γ hidx1
        have hwMul : capFwdWeight cfg Γ (idx + 1) * nextU.length =
            capDeposit cfg (idx + 1) * nextU.length + Γ * capFwdWeight cfg Γ (idx + 2) * nextU.length := by
          rw [hw]; ring
        rw [capDeeperDeposit_split cfg stEnd hidx1, capDeeperDeposit_split cfg st hidx1, hrecEq,
          Nat.mul_add]
        rw [hdeepEq] at ih hdeepLe
        omega
      · rw [capDeeperDeposit_eq_of_ge cfg stEnd (by omega),
          capDeeperDeposit_eq_of_ge cfg st (by omega)]
        rw [capDeeperDeposit_eq_of_ge cfg stEnd (by omega),
          capDeeperDeposit_eq_of_ge cfg stNext (by omega),
          capFwdWeight_of_le cfg Γ (by omega : cfg.P.d ≤ idx + 2)] at ih
        rw [capFwdWeight_of_le cfg Γ (by omega : cfg.P.d ≤ idx + 1)] at hfwdStep ⊢
        omega

/-- Amortized change of `chainRebuildCap + C_fac * (chainCapDeposit + capFwdPotential)` under one
`algorithm1_update`: it increases by at most `C_fac * capFwdWeight cfg Γ 0 * U.length`. -/
theorem algorithm1_update_cap_amortized (cfg : Alg2Config) (C_fac Γ : ℕ)
    (ch : ChainState cfg.T cfg.P) (U : List Update) (g' ℓ' : ℕ → ℝ)
    (hB : FwdBoundNat cfg.P Γ ch)
    (hA : FwdBoundNat cfg.P Γ (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ch U g' ℓ').1) :
    let ch' := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ch U g' ℓ').1
    chainRebuildCap cfg C_fac ch'.rebuildCount +
        C_fac * (chainCapDeposit cfg ch' + capFwdPotential cfg Γ ch') ≤
      chainRebuildCap cfg C_fac ch.rebuildCount +
        C_fac * (chainCapDeposit cfg ch + capFwdPotential cfg Γ ch) +
        C_fac * capFwdWeight cfg Γ 0 * U.length := by
  intro ch'
  have h1 := updateLoop_cap_deposit cfg ℓ' g' cfg.P.d 0
    { ch with recUpdates := fun j => if j = 0 then ch.recUpdates 0 + U.length else ch.recUpdates j }
    ((ch.G 0).applyBatch U) U ((ch.G 0).batchEnc U) (by omega)
  have h2 := updateLoop_cap_fwd cfg ℓ' g' Γ cfg.P.d 0
    { ch with recUpdates := fun j => if j = 0 then ch.recUpdates 0 + U.length else ch.recUpdates j }
    ((ch.G 0).applyBatch U) U ((ch.G 0).batchEnc U) (by omega) hB hA
  have hunit : chainRebuildCap cfg 1 ch'.rebuildCount + chainCapDeposit cfg ch' +
      capFwdPotential cfg Γ ch' ≤
      chainRebuildCap cfg 1 ch.rebuildCount + chainCapDeposit cfg ch +
      capFwdPotential cfg Γ ch + capFwdWeight cfg Γ 0 * U.length := by
    have hW0 : (if 0 < cfg.P.d then capDeposit cfg 0 * U.length else 0) +
        Γ * capFwdWeight cfg Γ 1 * U.length = capFwdWeight cfg Γ 0 * U.length := by
      by_cases hd : 0 < cfg.P.d
      · rw [ite_eq_left hd, capFwdWeight_succ cfg Γ hd]; ring
      · rw [ite_eq_right hd, capFwdWeight_of_le cfg Γ (by omega : cfg.P.d ≤ 1),
          capFwdWeight_of_le cfg Γ (by omega : cfg.P.d ≤ 0)]
        simp
    set st0 : ChainState cfg.T cfg.P :=
      { ch with recUpdates := fun j => if j = 0 then ch.recUpdates 0 + U.length else ch.recUpdates j }
    have hdeep0 : capDeeperDeposit cfg 0 st0 = capDeeperDeposit cfg 0 ch := by
      unfold capDeeperDeposit
      refine Finset.sum_congr rfl fun j hj => ?_
      have hgt : 0 < j := (Finset.mem_filter.mp hj).2
      simp only [st0, ite_eq_right (by omega : j ≠ 0)]
    change chainRebuildCap cfg 1 ch'.rebuildCount + chainCapDeposit cfg ch' ≤
      chainRebuildCap cfg 1 ch.rebuildCount + chainCapDeposit cfg ch +
        (if 0 < cfg.P.d then capDeposit cfg 0 * U.length else 0) +
        (capDeeperDeposit cfg 0 ch' - capDeeperDeposit cfg 0 st0) at h1
    change capFwdPotential cfg Γ ch' +
        (capDeeperDeposit cfg 0 ch' - capDeeperDeposit cfg 0 st0) ≤
      capFwdPotential cfg Γ ch + Γ * capFwdWeight cfg Γ 1 * U.length at h2
    rw [hdeep0] at h1 h2
    omega
  have hscale : ∀ rc, chainRebuildCap cfg C_fac rc = C_fac * chainRebuildCap cfg 1 rc := fun rc => by
    unfold chainRebuildCap; rw [one_mul]
  rw [hscale ch'.rebuildCount, hscale ch.rebuildCount]
  have hmul := Nat.mul_le_mul_left C_fac hunit
  linarith

/-- Shifting a level keeps `chainRebuildCap` equal and does not raise `chainCapDeposit` or
`capFwdPotential`. -/
theorem algorithm1_shift_cap_le (cfg : Alg2Config) (C_fac Γ : ℕ)
    (ch : ChainState cfg.T cfg.P) (i₀ : ℕ) :
    let ch' := (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1
    chainRebuildCap cfg C_fac ch'.rebuildCount = chainRebuildCap cfg C_fac ch.rebuildCount ∧
    chainCapDeposit cfg ch' ≤ chainCapDeposit cfg ch ∧
    capFwdPotential cfg Γ ch' ≤ capFwdPotential cfg Γ ch := by
  intro ch'
  have hrc : ch'.rebuildCount = ch.rebuildCount :=
    funext (ordAlgorithm1_shift_rebuildCount ch i₀)
  refine ⟨by rw [hrc], ?_, ?_⟩
  · unfold chainCapDeposit
    refine Finset.sum_le_sum fun j _ => ?_
    rcases algorithm1_shift_counts_reset cfg.T cfg.L cfg.P ch i₀ j with ⟨hu, _⟩ | ⟨hu, _⟩
    · rw [hu]
    · rw [hu]; exact Nat.zero_le _
  · unfold capFwdPotential
    refine Finset.sum_le_sum fun j _ => ?_
    rcases algorithm1_shift_counts_reset cfg.T cfg.L cfg.P ch i₀ j with ⟨hu, hf⟩ | ⟨hu, hf⟩
    · rw [hu, hf]
    · rw [hu, hf]; simp

/-- `algorithm2_loopWith` keeps `chainRebuildCap` equal and does not raise `chainCapDeposit` or
`capFwdPotential`. -/
theorem algorithm2_loopWith_cap_le (cfg : Alg2Config) (C_fac Γ : ℕ) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P)
    (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    chainRebuildCap cfg C_fac res.1.rebuildCount = chainRebuildCap cfg C_fac ch.rebuildCount ∧
    chainCapDeposit cfg res.1 ≤ chainCapDeposit cfg ch ∧
    capFwdPotential cfg Γ res.1 ≤ capFwdPotential cfg Γ ch := by
  suffices h : ∀ N ch branD passes lctOps,
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ N →
      let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
      chainRebuildCap cfg C_fac res.1.rebuildCount = chainRebuildCap cfg C_fac ch.rebuildCount ∧
      chainCapDeposit cfg res.1 ≤ chainCapDeposit cfg ch ∧
      capFwdPotential cfg Γ res.1 ≤ capFwdPotential cfg Γ ch from
    h _ ch branD passes lctOps le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ch branD passes lctOps hN
    dsimp only
    rw [Ordered.algorithm2_loopWith]
    dsimp only
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤ -(κ * cfg.α)
    · rw [dite_eq_left hGood]; exact ⟨rfl, le_rfl, le_rfl⟩
    · rw [dite_eq_right hGood]
      split
      · exact ⟨rfl, le_rfl, le_rfl⟩
      · rename_i i _
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left hCap]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          obtain ⟨h1, h2, h3⟩ := ih (N - 1) (by omega)
            (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 _ _ _ (by omega)
          obtain ⟨s1, s2, s3⟩ := algorithm1_shift_cap_le cfg C_fac Γ ch i.val
          exact ⟨h1.trans s1, h2.trans s2, h3.trans s3⟩
        · rw [dite_eq_right hCap]; exact ⟨rfl, le_rfl, le_rfl⟩


end MinCostFlow.MinRatio
