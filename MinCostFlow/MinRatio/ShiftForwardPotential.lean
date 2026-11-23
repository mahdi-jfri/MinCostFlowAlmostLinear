module

public import MinCostFlow.MinRatio.ShiftQuotaDeposit
import Mathlib.Tactic

/-!
# Paying the deposit of the deeper levels by recourse

`algorithm1_update_quota_deposit` charges each `Update` `shiftDeposit i` per update forwarded to
a level `0 < i < d` in this call (the growth of `deeperDeposit`). One call may forward many
updates, so this charge has no bound per call. The paper bounds it over the whole run: the
updates that level `i + 1` receives are the recourse of the sparse core of level `i`, at most
`γ_r` times the updates level `i` received since its last rebuild (proof of Theorem 7.1,
page 29; the invariant `curFwd i ≤ γ_r · updCount i` of the chain, `ChainRecBound`).

We pay it by a potential. With `Γ ≥ γ_r` and weights `W_i = Σ_{i ≤ j < d} Γ^{j-i} shiftDeposit j`
(`fwdWeight`), let

  `fwdPotential = Σ_{j < d} W_{j+1} · (Γ · updCount j - curFwd j)`.

An update counted at level `j` raises the term of `j` by `Γ W_{j+1}`. An update forwarded from
level `j` to level `j + 1` lowers it by `W_{j+1} = shiftDeposit (j + 1) + Γ W_{j+2}`
(`fwdWeight_succ`), which pays its deposit at level `j + 1` and the rise of the term of level
`j + 1`. So in one `Update` the potential plus `deeperDeposit` grows by at most `Γ W_1` per update
of the batch (`algorithm1_update_fwd`). A rebuild or a shift sets both counts of the levels it
rebuilds to `0`, which only lowers the potential. The subtraction stays exact as long as
`curFwd j ≤ Γ · updCount j` (`FwdBoundNat`) holds before and after the step.

`update_fwd_amortized` (`OrdSolverShiftPotential.lean`) adds this potential to `update_shift_amortized`: one call then costs the
budget without the loop term, plus one loop step, plus `B · W_0` per update of the batch, where
`W_0 = shiftDeposit 0 + Γ W_1`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-! ## The weights and the potential -/

/-- The weight `W_i = Σ_{i ≤ j < d} Γ^{j-i} shiftDeposit j` of an update counted at level `i`:
its own deposit, and `Γ` times the weight of each update it may cause at level `i + 1`. -/
@[expose] noncomputable def fwdWeight (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (Γ i : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico i P.d, Γ ^ (j - i) * shiftDeposit P N₀ psi j

/-- The recursion of the weights: `W_i = shiftDeposit i + Γ W_{i+1}` for `i < d`. -/
theorem fwdWeight_succ (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (Γ : ℕ) {i : ℕ} (hi : i < P.d) :
    fwdWeight P N₀ psi Γ i = shiftDeposit P N₀ psi i + Γ * fwdWeight P N₀ psi Γ (i + 1) := by
  unfold fwdWeight
  rw [Finset.sum_eq_sum_Ico_succ_bot hi, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := (Finset.mem_Ico.mp hj).1
  rw [show j - i = (j - (i + 1)) + 1 by omega, pow_succ]
  ring

/-- The weights vanish from level `d` on. -/
theorem fwdWeight_of_le (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (Γ : ℕ) {i : ℕ} (hi : P.d ≤ i) :
    fwdWeight P N₀ psi Γ i = 0 := by
  unfold fwdWeight
  rw [Finset.Ico_eq_empty_of_le hi, Finset.sum_empty]

/-- The forward potential `Σ_{j < d} W_{j+1} (Γ · updCount j - curFwd j)`. -/
@[expose] noncomputable def fwdPotential {T : SparseCoreRestartTool} (P : ChainParams) (N₀ : ℕ)
    (psi : ℝ) (Γ : ℕ) (ch : ChainState T P) : ℕ :=
  ∑ j ∈ Finset.range P.d, fwdWeight P N₀ psi Γ (j + 1) * (Γ * ch.updCount j - ch.curFwd j)

/-- The recourse invariant with the integer factor `Γ`: at each level `j < d`, the updates
forwarded since the last rebuild of level `j` are at most `Γ` times the updates counted there. -/
@[expose] def FwdBoundNat {T : SparseCoreRestartTool} (P : ChainParams) (Γ : ℕ)
    (ch : ChainState T P) : Prop :=
  ∀ j < P.d, ch.curFwd j ≤ Γ * ch.updCount j

/-- The invariant of the chain, `curFwd j ≤ γ_r · updCount j` (the first half of
`ChainRecBound`), gives `FwdBoundNat` for `Γ = ⌈γ_r⌉`. -/
theorem fwdBoundNat_of_real {T : SparseCoreRestartTool} {P : ChainParams} {γ : ℝ}
    {ch : ChainState T P} (h : ∀ j < P.d, (ch.curFwd j : ℝ) ≤ γ * (ch.updCount j : ℝ)) :
    FwdBoundNat P ⌈γ⌉₊ ch := by
  intro j hj
  have h1 := h j hj
  have h2 : γ * (ch.updCount j : ℝ) ≤ (⌈γ⌉₊ : ℝ) * (ch.updCount j : ℝ) :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil γ) (Nat.cast_nonneg _)
  exact_mod_cast h1.trans h2

/-! ## Counts after a rebuild, a shift, and the levels below the current one -/

/-- `rebuildSuffix` sets the forward counts of the levels it rebuilds to `0`. -/
theorem rebuildSuffix_curFwd (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.2.2.2.1
          k = if idx ≤ k ∧ k < idx + rem then 0 else cFwd k
  | 0, idx, _, _, _, _, _, _, _, k => by
    have h : ¬ (idx ≤ k ∧ k < idx + 0) := by omega
    simp only [h, ite_false]
    rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k => by
    dsimp only [Ordered.rebuildSuffix]
    rw [rebuildSuffix_curFwd T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k]
    split_ifs <;> first | rfl | omega

/-- A rebuild at level `i₀ < d` sets the forward counts of levels `i₀, …, d - 1` to `0` and
keeps the others. -/
theorem algorithm1_rebuild_curFwd (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) {i₀ : ℕ} (hi : i₀ < P.d) (Gnew : MGraph)
    (extraEnc : ℕ) (j : ℕ) :
    (Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.curFwd j =
      if i₀ ≤ j ∧ j < P.d then 0 else st.curFwd j := by
  dsimp only [Ordered.algorithm1_rebuild]
  rw [dite_eq_left_of_eq_true (eq_true hi)]
  dsimp only
  rw [rebuildSuffix_curFwd]
  congr 2
  apply propext
  omega

/-- A shift at level `i₀` sets both counts of each level it rebuilds to `0`, and keeps both
counts of every other level. -/
theorem algorithm1_shift_counts_reset (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ j : ℕ) :
    let st' := (Ordered.algorithm1_shift T L P st i₀).1
    (st'.updCount j = st.updCount j ∧ st'.curFwd j = st.curFwd j) ∨
      (st'.updCount j = 0 ∧ st'.curFwd j = 0) := by
  dsimp only [Ordered.algorithm1_shift]
  split_ifs with hlt
  · dsimp only
    rw [rebuildSuffix_updCount, rebuildSuffix_curFwd]
    split_ifs
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- `updateLoop` from level `idx` keeps both counts of the levels below `idx`, and the cumulative
counts of the levels up to `idx`. -/
theorem updateLoop_low (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (enc : ℕ),
      idx + rem = P.d →
      let st' := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU enc).1
      (∀ j < idx, st'.updCount j = st.updCount j ∧ st'.curFwd j = st.curFwd j) ∧
        ∀ j ≤ idx, st'.recUpdates j = st.recUpdates j := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU enc _
    dsimp only [Ordered.updateLoop]
    split_ifs <;> exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  | succ rem ih =>
    intro idx st curG curU enc hsum
    have hidx : idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    split_ifs with hTh
    · refine ⟨fun j hj => ⟨?_, ?_⟩, fun j _ => ?_⟩
      · rw [(algorithm1_rebuild_counts T L P _ hidx _ _).2.2.2 j, ite_eq_right (by omega)]
      · rw [algorithm1_rebuild_curFwd T L P _ hidx _ _ j, ite_eq_right (by omega)]
      · rw [algorithm1_rebuild_recUpdates]
    · refine ⟨fun j hj => ⟨((ih (idx + 1) _ _ _ 0 (by omega)).1 j (by omega)).1.trans ?_,
        ((ih (idx + 1) _ _ _ 0 (by omega)).1 j (by omega)).2.trans ?_⟩,
        fun j hj => ((ih (idx + 1) _ _ _ 0 (by omega)).2 j (by omega)).trans ?_⟩
      · dsimp only; rw [ite_eq_right (by omega)]
      · dsimp only; rw [ite_eq_right (by omega)]
      · dsimp only; rw [ite_eq_right (by omega)]

/-! ## One `Update` of Algorithm 1 -/

private theorem fwdPotential_split {T : SparseCoreRestartTool} (P : ChainParams) (N₀ : ℕ)
    (psi : ℝ) (Γ : ℕ) (ch : ChainState T P) {idx : ℕ} (hidx : idx < P.d) :
    fwdPotential P N₀ psi Γ ch =
      fwdWeight P N₀ psi Γ (idx + 1) * (Γ * ch.updCount idx - ch.curFwd idx) +
        ∑ j ∈ (Finset.range P.d).erase idx,
          fwdWeight P N₀ psi Γ (j + 1) * (Γ * ch.updCount j - ch.curFwd j) := by
  unfold fwdPotential
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hidx)]

/-- One level of `updateLoop` without a rebuild. -/
private theorem fwd_step_combine {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ} {ℓ' g' : ℕ → ℝ} {psi : ℝ} {Γ : ℕ}
    {rem idx u : ℕ} {st st₁ : ChainState T P} {G₁ : MGraph} {U₁ : List Update}
    (hidx : idx < P.d) (hsum : idx + 1 + rem = P.d)
    (hu : st₁.updCount = fun j => if j = idx then st.updCount idx + u else st.updCount j)
    (hrec : st₁.recUpdates =
      fun j => if j = idx + 1 then st.recUpdates (idx + 1) + U₁.length else st.recUpdates j)
    (hf : st₁.curFwd = fun j => if j = idx then st.curFwd idx + U₁.length else st.curFwd j)
    (hBefore : st.curFwd idx ≤ Γ * st.updCount idx)
    (hFinal : FwdBoundNat P Γ (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1)
    (hIH : fwdPotential P N₀ psi Γ (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 +
        deeperDeposit P N₀ psi (idx + 1) (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 ≤
      fwdPotential P N₀ psi Γ st₁ + deeperDeposit P N₀ psi (idx + 1) st₁ +
        (if idx + 1 < P.d then Γ * fwdWeight P N₀ psi Γ (idx + 1 + 1) * U₁.length else 0)) :
    fwdPotential P N₀ psi Γ (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 +
        deeperDeposit P N₀ psi idx (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 ≤
      fwdPotential P N₀ psi Γ st + deeperDeposit P N₀ psi idx st +
        Γ * fwdWeight P N₀ psi Γ (idx + 1) * u := by
  set st' := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 with hst'
  obtain ⟨hlow, hlowRec⟩ := updateLoop_low T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0 hsum
  have hu' : st'.updCount idx = st.updCount idx + u := by
    rw [(hlow idx (by omega)).1, hu]; simp
  have hf' : st'.curFwd idx = st.curFwd idx + U₁.length := by
    rw [(hlow idx (by omega)).2, hf]; simp
  have hrec' : st'.recUpdates (idx + 1) = st.recUpdates (idx + 1) + U₁.length := by
    rw [hlowRec (idx + 1) le_rfl, hrec]; simp
  have hAfter : st.curFwd idx + U₁.length ≤ Γ * (st.updCount idx + u) := by
    have := hFinal idx hidx
    rwa [hu', hf'] at this
  -- the term of level `idx`
  set W := fwdWeight P N₀ psi Γ (idx + 1) with hW
  have hT : W * (Γ * (st.updCount idx + u) - (st.curFwd idx + U₁.length)) + W * U₁.length =
      W * (Γ * st.updCount idx - st.curFwd idx) + Γ * W * u := by
    have h0 : Γ * (st.updCount idx + u) - (st.curFwd idx + U₁.length) + U₁.length =
        Γ * st.updCount idx - st.curFwd idx + Γ * u := by
      rw [Nat.mul_add] at hAfter ⊢; omega
    calc W * (Γ * (st.updCount idx + u) - (st.curFwd idx + U₁.length)) + W * U₁.length
        = W * (Γ * (st.updCount idx + u) - (st.curFwd idx + U₁.length) + U₁.length) := by ring
      _ = W * (Γ * st.updCount idx - st.curFwd idx + Γ * u) := by rw [h0]
      _ = _ := by ring
  have hrest : ∑ j ∈ (Finset.range P.d).erase idx,
        fwdWeight P N₀ psi Γ (j + 1) * (Γ * st₁.updCount j - st₁.curFwd j) =
      ∑ j ∈ (Finset.range P.d).erase idx,
        fwdWeight P N₀ psi Γ (j + 1) * (Γ * st.updCount j - st.curFwd j) :=
    Finset.sum_congr rfl fun j hj => by
      have hj : j ≠ idx := Finset.ne_of_mem_erase hj
      rw [hu, hf]; simp [hj]
  have hP1 := fwdPotential_split P N₀ psi Γ st₁ hidx
  have hP0 := fwdPotential_split P N₀ psi Γ st hidx
  have hu1 : st₁.updCount idx = st.updCount idx + u := by rw [hu]; simp
  have hf1 : st₁.curFwd idx = st.curFwd idx + U₁.length := by rw [hf]; simp
  rw [hu1, hf1, hrest] at hP1
  rw [← hW] at hP1 hP0
  -- the deposit of level `idx + 1`
  have hdeep1 : deeperDeposit P N₀ psi (idx + 1) st₁ = deeperDeposit P N₀ psi (idx + 1) st :=
    deeperDeposit_congr (idx + 1) fun i hi => by rw [hrec]; simp [Nat.ne_of_gt hi]
  rw [deeperDeposit_split P N₀ psi idx st', deeperDeposit_split P N₀ psi idx st, hrec']
  rw [hdeep1] at hIH
  split_ifs at hIH ⊢ with hd
  · have hWs := fwdWeight_succ P N₀ psi Γ hd
    rw [← hW] at hWs
    have hWf : W * U₁.length = shiftDeposit P N₀ psi (idx + 1) * U₁.length +
        Γ * fwdWeight P N₀ psi Γ (idx + 1 + 1) * U₁.length := by
      rw [hWs]; ring
    rw [Nat.mul_add]
    omega
  · have hW0 : W = 0 := fwdWeight_of_le P N₀ psi Γ (by omega)
    rw [hW0] at hP1 hP0
    simp only [zero_mul, zero_add] at hP1 hP0
    omega

/-- The rebuild branch of `updateLoop` at level `idx < d`: the potential does not grow, and the
cumulative counts stay. -/
private theorem fwd_rebuild_combine {T : SparseCoreRestartTool} (L : LastLevelTool)
    {P : ChainParams} {N₀ : ℕ} {psi : ℝ} {Γ idx : ℕ} (hidx : idx < P.d)
    (st : ChainState T P) (curG : MGraph) (enc : ℕ) :
    let st' := (Ordered.algorithm1_rebuild T L P st idx curG enc).1
    fwdPotential P N₀ psi Γ st' + deeperDeposit P N₀ psi idx st' ≤
      fwdPotential P N₀ psi Γ st + deeperDeposit P N₀ psi idx st := by
  intro st'
  have hdeep : deeperDeposit P N₀ psi idx st' = deeperDeposit P N₀ psi idx st :=
    deeperDeposit_congr idx fun i _ => by rw [algorithm1_rebuild_recUpdates]
  rw [hdeep]
  refine Nat.add_le_add_right (Finset.sum_le_sum fun j _ => ?_) _
  have hu := (algorithm1_rebuild_counts T L P st hidx curG enc).2.2.2 j
  have hf := algorithm1_rebuild_curFwd T L P st hidx curG enc j
  change fwdWeight P N₀ psi Γ (j + 1) * (Γ * st'.updCount j - st'.curFwd j) ≤ _
  rw [hu, hf]
  split_ifs
  · simp
  · exact le_rfl

/-- **The forward potential pays for the deeper deposit**, over the levels `idx, …, d` of
`updateLoop`: the potential plus `deeperDeposit idx` grows by at most `Γ W_{idx+1}` per update
of the batch entering level `idx < d`. It needs `FwdBoundNat` at the levels `≥ idx` before, and
`FwdBoundNat` after. -/
theorem updateLoop_fwd (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) (psi : ℝ) (Γ : ℕ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (enc : ℕ),
      idx + rem = P.d →
      (∀ j, idx ≤ j → j < P.d → st.curFwd j ≤ Γ * st.updCount j) →
      let st' := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU enc).1
      FwdBoundNat P Γ st' →
      fwdPotential P N₀ psi Γ st' + deeperDeposit P N₀ psi idx st' ≤
        fwdPotential P N₀ psi Γ st + deeperDeposit P N₀ psi idx st +
          (if idx < P.d then Γ * fwdWeight P N₀ psi Γ (idx + 1) * curU.length else 0) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU enc hsum _
    have hidx : ¬ idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    rw [ite_eq_right hidx, Nat.add_zero]
    split_ifs <;> exact fun _ => le_rfl
  | succ rem ih =>
    intro idx st curG curU enc hsum hBefore hFinal
    have hidx : idx < P.d := by omega
    rw [ite_eq_left hidx]
    revert hFinal
    dsimp only [Ordered.updateLoop]
    split_ifs with hTh
    · intro _
      exact le_trans (fwd_rebuild_combine L hidx _ _ _) (Nat.le_add_right _ _)
    · intro hFinal
      refine fwd_step_combine hidx (by omega) rfl rfl rfl (hBefore idx le_rfl hidx) hFinal ?_
      refine ih (idx + 1) _ _ _ 0 (by omega) (fun j hj hjd => ?_) hFinal
      dsimp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hBefore j (by omega) hjd

/-- **The forward potential pays for the deeper deposit**, for one `Update` of Algorithm 1:
if `FwdBoundNat` holds before and after, the forward potential plus `deeperDeposit 0` grows by
at most `Γ W_1` per update of the batch. -/
theorem algorithm1_update_fwd (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) (psi : ℝ) (Γ : ℕ) (hBefore : FwdBoundNat P Γ st)
    (hAfter : FwdBoundNat P Γ (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1) :
    let ch1 := (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1
    fwdPotential P N₀ psi Γ ch1 + deeperDeposit P N₀ psi 0 ch1 ≤
      fwdPotential P N₀ psi Γ st + deeperDeposit P N₀ psi 0 st +
        Γ * fwdWeight P N₀ psi Γ 1 * U.length := by
  dsimp only [Ordered.algorithm1_update] at hAfter ⊢
  have h := updateLoop_fwd T L TP P N₀ ℓ' g' psi Γ P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U) (by omega)
    (fun j _ hj => hBefore j hj) hAfter
  have hd : deeperDeposit P N₀ psi 0
      { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length
                                         else st.recUpdates j } =
      deeperDeposit P N₀ psi 0 st :=
    deeperDeposit_congr 0 fun i hi => by simp [hi.ne']
  rw [hd] at h
  change _ ≤ fwdPotential P N₀ psi Γ st + _ + _ at h
  rw [zero_add] at h
  split_ifs at h <;> omega

/-! ## The shift loop -/

/-- A step relation: each level keeps both counts or has both set to `0`. -/
private def KeepOrReset {T : SparseCoreRestartTool} {P : ChainParams} (ch ch' : ChainState T P) :
    Prop :=
  ∀ j, (ch'.updCount j = ch.updCount j ∧ ch'.curFwd j = ch.curFwd j) ∨
    (ch'.updCount j = 0 ∧ ch'.curFwd j = 0)

private theorem keepOrReset_trans {T : SparseCoreRestartTool} {P : ChainParams}
    {a b c : ChainState T P} (h1 : KeepOrReset a b) (h2 : KeepOrReset b c) : KeepOrReset a c := by
  intro j
  rcases h2 j with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases h1 j with ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact Or.inl ⟨e1.trans f1, e2.trans f2⟩
    · exact Or.inr ⟨e1.trans f1, e2.trans f2⟩
  · exact Or.inr ⟨e1, e2⟩

private theorem algorithm2_loopWith_keepOrReset (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (B : ℕ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
      (lctOps : ℕ),
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ B →
      KeepOrReset ch (Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1 := by
  intro B
  induction B with
  | zero =>
    intro ch branD passes lctOps hB
    rw [Ordered.algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · exact fun j => Or.inl ⟨rfl, rfl⟩
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact fun j => Or.inl ⟨rfl, rfl⟩
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap; omega
        · rw [dite_eq_right_of_eq_false (eq_false hCap)]
          exact fun j => Or.inl ⟨rfl, rfl⟩
  | succ B ihB =>
    intro ch branD passes lctOps hB
    rw [Ordered.algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · exact fun j => Or.inl ⟨rfl, rfl⟩
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact fun j => Or.inl ⟨rfl, rfl⟩
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          exact keepOrReset_trans
            (fun j => algorithm1_shift_counts_reset cfg.T cfg.L cfg.P ch i.val j)
            (ihB (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 _ _ _ (by omega))
        · rw [dite_eq_right_of_eq_false (eq_false hCap)]
          exact fun j => Or.inl ⟨rfl, rfl⟩

/-- The shift loop of Algorithm 2 does not raise the forward potential and keeps
`FwdBoundNat`, since each shift keeps both counts of a level or sets both to `0`. -/
theorem algorithm2_loopWith_fwd (cfg : Alg2Config) (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) (psi : ℝ) (Γ : ℕ) :
    let res := (Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1
    fwdPotential cfg.P cfg.N₀ psi Γ res ≤ fwdPotential cfg.P cfg.N₀ psi Γ ch ∧
      (FwdBoundNat cfg.P Γ ch → FwdBoundNat cfg.P Γ res) := by
  intro res
  have hk := algorithm2_loopWith_keepOrReset cfg κ extG e2i g' ℓ' _ ch branD passes lctOps le_rfl
  refine ⟨Finset.sum_le_sum fun j _ => ?_, fun h j hj => ?_⟩
  · rcases hk j with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · change fwdWeight _ _ _ _ _ * (Γ * res.updCount j - res.curFwd j) ≤ _
      rw [e1, e2]
    · change fwdWeight _ _ _ _ _ * (Γ * res.updCount j - res.curFwd j) ≤ _
      rw [e1, e2]; simp
  · rcases hk j with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact h j hj
    · rw [e1, e2]; exact Nat.zero_le _

end MinCostFlow.MinRatio
