module

public import MinCostFlow.MinRatio.ShiftGuards
public import MinCostFlow.Chain.Ordered.Algorithm2
import Mathlib.Tactic

/-!
# Paying for the shift quota out of the updates

Algorithm 2 (page 29) may shift a level as long as the shift count of that level is below the
quota of Lemma 7.3, `gameShiftBound`. The quota grows with each rebuild. The machine pays for
the shift loop through a potential `B · N`, where `N = shiftRemainingBudget` is the unused quota
and `B` is the cost of one loop step. A shift lowers `N` by at least one, so it pays for itself.
A rebuild raises `N`, and the update that causes it must pay for that.

The paper (page 29, proof of Theorem 7.1) pays for rebuilds by the updates: a rebuild at level
`i` happens only after level `i` has received more than `intRebuildThreshold i` updates since
its last rebuild. We do the same with a second potential, a deposit of `shiftDeposit i` per
update counted at level `i` (`chainShiftDeposit`). The deposit is chosen so that the updates
counted at level `i` before a rebuild there pay for the quota the rebuild adds
(`rebuildQuotaGain_le_deposit`).

The main result is `algorithm1_update_quota_deposit`: in one step of Algorithm 1's `Update`,
the unused quota plus the deposit grows by at most `shiftDeposit 0` per update of the batch,
plus `shiftDeposit i` per update forwarded to each deeper level `i`. It is proved by induction
over the levels of `updateLoop` (`updateLoop_quota_deposit`). We also show that the shift loop
of Algorithm 2 never raises the deposit (`algorithm2_loopWith_updCount_le`), since a shift only
resets update counts.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-! ## The quota a rebuild adds -/

/-- The quota that one rebuild at level `i` adds to the unused shift quota: by Lemma 7.3's
bound, `(10 Ψ k) ^ (j + 1 - i)` at each level `j ≥ i`, here rounded up. -/
@[expose] noncomputable def rebuildQuotaGain (P : ChainParams) (psi : ℝ) (i : ℕ) : ℕ :=
  ∑ j : Fin (P.d + 1), if i ≤ j.val then ⌈(10 * psi * (P.k : ℝ)) ^ (j.val + 1 - i)⌉₊ else 0

/-- The deposit per update counted at level `i`: the quota gain of a rebuild at level `i`,
spread over the `intRebuildThreshold i + 1` updates that cause it, rounded up. -/
@[expose] noncomputable def shiftDeposit (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (i : ℕ) : ℕ :=
  (rebuildQuotaGain P psi i + intRebuildThreshold P N₀ i) / (intRebuildThreshold P N₀ i + 1)

/-- The deposit held by a chain: `shiftDeposit i` per update counted at level `i < d` since the
last rebuild of that level. -/
@[expose] noncomputable def chainShiftDeposit {T : SparseCoreRestartTool} (P : ChainParams) (N₀ : ℕ)
    (psi : ℝ) (ch : ChainState T P) : ℕ :=
  ∑ i ∈ Finset.range P.d, shiftDeposit P N₀ psi i * ch.updCount i

/-- The deposit charged for the updates forwarded to the levels strictly between `idx` and `d`,
measured by the cumulative update counts `recUpdates`. -/
@[expose] noncomputable def deeperDeposit {T : SparseCoreRestartTool} (P : ChainParams) (N₀ : ℕ)
    (psi : ℝ) (idx : ℕ) (ch : ChainState T P) : ℕ :=
  ∑ i ∈ (Finset.range P.d).filter (fun i => idx < i), shiftDeposit P N₀ psi i * ch.recUpdates i

theorem rebuildQuotaGain_le_deposit (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (i : ℕ) :
    rebuildQuotaGain P psi i ≤ shiftDeposit P N₀ psi i * (intRebuildThreshold P N₀ i + 1) := by
  unfold shiftDeposit
  have h := Nat.lt_div_mul_add (a := rebuildQuotaGain P psi i + intRebuildThreshold P N₀ i)
    (b := intRebuildThreshold P N₀ i + 1) (by omega)
  omega

private theorem floor_add_le_floor_add_ceil {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌊a + b⌋₊ ≤ ⌊a⌋₊ + ⌈b⌉₊ := by
  have h : ⌊a + b⌋₊ < ⌊a⌋₊ + ⌈b⌉₊ + 1 := by
    rw [Nat.floor_lt (by linarith)]
    have h1 := Nat.lt_floor_add_one a
    have h2 := Nat.le_ceil b
    push_cast
    linarith
  omega

private theorem gameShiftBound_nonneg' (P : ChainParams) (psi : ℝ) (rebuilds : ℕ → ℕ)
    (i : ℕ) (hpsi : 0 ≤ psi) : 0 ≤ gameShiftBound P psi rebuilds i := by
  unfold gameShiftBound
  apply add_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by positivity) hpsi) (Nat.cast_nonneg _)) _)
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (mul_nonneg (mul_nonneg (by positivity) hpsi) (Nat.cast_nonneg _)) _)

/-- A rebuild at level `i`, which keeps the shift counts, raises the unused shift quota by at
most `rebuildQuotaGain i`. -/
theorem shiftRemainingBudget_rebuild_le {T : SparseCoreRestartTool} (P : ChainParams)
    {psi : ℝ} (hpsi : 0 ≤ psi) {ch ch' : ChainState T P} (i : ℕ)
    (hs : ch'.shiftCount = ch.shiftCount)
    (hr : ch'.rebuildCount = fun j => if j = i then ch.rebuildCount i + 1 else ch.rebuildCount j) :
    shiftRemainingBudget P psi ch' ≤ shiftRemainingBudget P psi ch + rebuildQuotaGain P psi i := by
  unfold shiftRemainingBudget rebuildQuotaGain
  rw [hs, hr, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [gameShiftBound_rebuild_increment]
  have hg := gameShiftBound_nonneg' P psi ch.rebuildCount j.val hpsi
  have hb : (0 : ℝ) ≤ 10 * psi * (P.k : ℝ) := by positivity
  split_ifs with hij
  · have := floor_add_le_floor_add_ceil hg (pow_nonneg hb (j.val + 1 - i))
    omega
  · simp

/-! ## Update counts after a rebuild or a shift -/

private theorem rebuildSuffix_updCount_lt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      k < idx →
      (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.1 k =
        upd k
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k, hk => by
    dsimp only [Ordered.rebuildSuffix]
    rw [rebuildSuffix_updCount_lt T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k
      (Nat.lt_succ_of_lt hk)]
    simp [Nat.ne_of_lt hk]

/-- After `rebuildSuffix` from level `idx`, the update counts of levels `idx, …, idx + rem - 1`
are zero and the others are unchanged. -/
theorem rebuildSuffix_updCount (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.1 k =
        if idx ≤ k ∧ k < idx + rem then 0 else upd k
  | 0, idx, _, _, _, _, _, _, _, k => by
    have h : ¬ (idx ≤ k ∧ k < idx + 0) := by omega
    simp only [h, ite_false]
    rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k => by
    dsimp only [Ordered.rebuildSuffix]
    rw [rebuildSuffix_updCount T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k]
    split_ifs <;> first | rfl | omega

theorem rebuildSuffix_updCount_le (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) (rem idx : ℕ)
    (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ) :
    (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.1 k ≤
      upd k := by
  rw [rebuildSuffix_updCount]
  split_ifs <;> omega

/-- A rebuild at level `i₀ < d` adds one to the rebuild count of level `i₀`, keeps the shift
counts and the cumulative update counts, and zeroes the update counts of levels `i₀, …, d - 1`. -/
theorem algorithm1_rebuild_counts (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) {i₀ : ℕ} (hi : i₀ < P.d) (Gnew : MGraph)
    (extraEnc : ℕ) :
    let st' := (Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1
    st'.rebuildCount = (fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j) ∧
    st'.shiftCount = st.shiftCount ∧ st'.recUpdates = st.recUpdates ∧
    ∀ j, st'.updCount j = if i₀ ≤ j ∧ j < P.d then 0 else st.updCount j := by
  dsimp only [Ordered.algorithm1_rebuild]
  rw [dite_eq_left_of_eq_true (eq_true hi)]
  refine ⟨rfl, rfl, rfl, fun j => ?_⟩
  dsimp only
  rw [rebuildSuffix_updCount]
  congr 2
  apply propext
  omega

/-- A shift keeps the rebuild counts and does not raise any update count. -/
theorem algorithm1_shift_counts (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) :
    let st' := (Ordered.algorithm1_shift T L P st i₀).1
    st'.rebuildCount = st.rebuildCount ∧ ∀ j, st'.updCount j ≤ st.updCount j := by
  dsimp only [Ordered.algorithm1_shift]
  split_ifs with hlt
  · exact ⟨rfl, fun j => rebuildSuffix_updCount_le T L P _ _ _ _ _ _ _ _ _ _ _ _ _ j⟩
  · exact ⟨rfl, fun j => le_rfl⟩

/-- The shift loop of Algorithm 2 keeps the rebuild counts and does not raise any update count,
so it does not raise the deposit. The proof is by induction on an upper bound of the unused
shift quota, which each shift lowers. -/
theorem algorithm2_loopWith_updCount_le (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (B : ℕ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
      (lctOps : ℕ),
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ B →
      let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
      res.1.rebuildCount = ch.rebuildCount ∧ ∀ j, res.1.updCount j ≤ ch.updCount j := by
  intro B
  induction B with
  | zero =>
    intro ch branD passes lctOps hB
    rw [Ordered.algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · exact ⟨rfl, fun j => le_rfl⟩
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact ⟨rfl, fun j => le_rfl⟩
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap; omega
        · simp [hCap]
  | succ B ihB =>
    intro ch branD passes lctOps hB
    rw [Ordered.algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · exact ⟨rfl, fun j => le_rfl⟩
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact ⟨rfl, fun j => le_rfl⟩
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          obtain ⟨hreb, hupd⟩ := algorithm1_shift_counts cfg.T cfg.L cfg.P ch i.val
          obtain ⟨hreb', hupd'⟩ := ihB (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 _ _ _
            (by omega)
          exact ⟨hreb'.trans hreb, fun j => (hupd' j).trans (hupd j)⟩
        · rw [dite_eq_right_of_eq_false (eq_false hCap)]
          exact ⟨rfl, fun j => le_rfl⟩

/-! ## The deposit over one `Update` of Algorithm 1 -/

/-- A rebuild keeps the cumulative update counts. -/
theorem algorithm1_rebuild_recUpdates (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph) (extraEnc : ℕ) :
    (Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.recUpdates = st.recUpdates := by
  dsimp only [Ordered.algorithm1_rebuild]
  split_ifs <;> rfl

/-- `updateLoop` never lowers a cumulative update count. -/
theorem updateLoop_recUpdates_mono (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (enc j : ℕ),
      st.recUpdates j ≤
        (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU enc).1.recUpdates j := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU enc j
    dsimp only [Ordered.updateLoop]
    split_ifs <;> exact le_rfl
  | succ rem ih =>
    intro idx st curG curU enc j
    dsimp only [Ordered.updateLoop]
    split_ifs with hTh
    · rw [algorithm1_rebuild_recUpdates]
    · refine le_trans ?_ (ih (idx + 1) _ _ _ 0 j)
      dsimp only
      split_ifs with h
      · subst h; omega
      · exact le_rfl

private theorem shiftRemainingBudget_congr {T : SparseCoreRestartTool} {P : ChainParams}
    {psi : ℝ} {ch ch' : ChainState T P} (hs : ch'.shiftCount = ch.shiftCount)
    (hr : ch'.rebuildCount = ch.rebuildCount) :
    shiftRemainingBudget P psi ch' = shiftRemainingBudget P psi ch := by
  unfold shiftRemainingBudget
  rw [hs, hr]

private theorem chainShiftDeposit_bump {T : SparseCoreRestartTool} {P : ChainParams} {N₀ : ℕ}
    {psi : ℝ} {ch ch' : ChainState T P} {idx u : ℕ} (hidx : idx < P.d)
    (hu : ch'.updCount = fun j => if j = idx then ch.updCount idx + u else ch.updCount j) :
    chainShiftDeposit P N₀ psi ch' = chainShiftDeposit P N₀ psi ch + shiftDeposit P N₀ psi idx * u := by
  unfold chainShiftDeposit
  rw [hu]
  have h : ∀ i ∈ Finset.range P.d,
      shiftDeposit P N₀ psi i * (if i = idx then ch.updCount idx + u else ch.updCount i) =
        shiftDeposit P N₀ psi i * ch.updCount i + if idx = i then shiftDeposit P N₀ psi i * u else 0 := by
    intro i _
    by_cases hi : i = idx
    · subst hi; simp [Nat.mul_add]
    · simp [hi, Ne.symm hi]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp [hidx]

/-- `deeperDeposit idx` is the term of level `idx + 1` plus `deeperDeposit (idx + 1)`. -/
theorem deeperDeposit_split {T : SparseCoreRestartTool} (P : ChainParams) (N₀ : ℕ)
    (psi : ℝ) (idx : ℕ) (ch : ChainState T P) :
    deeperDeposit P N₀ psi idx ch =
      (if idx + 1 < P.d then shiftDeposit P N₀ psi (idx + 1) * ch.recUpdates (idx + 1) else 0) +
        deeperDeposit P N₀ psi (idx + 1) ch := by
  unfold deeperDeposit
  rw [Finset.sum_filter, Finset.sum_filter]
  have h : ∀ i ∈ Finset.range P.d,
      (if idx < i then shiftDeposit P N₀ psi i * ch.recUpdates i else 0) =
        (if idx + 1 = i then shiftDeposit P N₀ psi i * ch.recUpdates i else 0) +
          if idx + 1 < i then shiftDeposit P N₀ psi i * ch.recUpdates i else 0 := by
    intro i _
    by_cases h1 : idx + 1 = i
    · subst h1; simp
    · by_cases h2 : idx < i
      · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by omega), zero_add]
      · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_range]

/-- `deeperDeposit idx` reads only the cumulative counts of the levels above `idx`. -/
theorem deeperDeposit_congr {T : SparseCoreRestartTool} {P : ChainParams} {N₀ : ℕ}
    {psi : ℝ} {ch ch' : ChainState T P} (idx : ℕ)
    (hrec : ∀ i, idx < i → ch'.recUpdates i = ch.recUpdates i) :
    deeperDeposit P N₀ psi idx ch' = deeperDeposit P N₀ psi idx ch := by
  unfold deeperDeposit
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hrec i (Finset.mem_filter.mp hi).2]

/-- One level of `updateLoop` without a rebuild: the level counts the batch, and forwards a
batch of `n` updates to the next level. -/
private theorem step_combine {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ} {ℓ' g' : ℕ → ℝ} {psi : ℝ}
    {rem idx u : ℕ} {st st₁ : ChainState T P} {G₁ : MGraph} {U₁ : List Update}
    (hidx : idx < P.d)
    (hs : st₁.shiftCount = st.shiftCount) (hr : st₁.rebuildCount = st.rebuildCount)
    (hu : st₁.updCount = fun j => if j = idx then st.updCount idx + u else st.updCount j)
    (hrec : st₁.recUpdates =
      fun j => if j = idx + 1 then st.recUpdates (idx + 1) + U₁.length else st.recUpdates j)
    (hmono : st₁.recUpdates (idx + 1) ≤ (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1.recUpdates (idx + 1))
    (hIH : shiftRemainingBudget P psi (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 + chainShiftDeposit P N₀ psi (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 +
        deeperDeposit P N₀ psi (idx + 1) st₁ ≤
      shiftRemainingBudget P psi st₁ + chainShiftDeposit P N₀ psi st₁ +
        (if idx + 1 < P.d then shiftDeposit P N₀ psi (idx + 1) * U₁.length else 0) +
        deeperDeposit P N₀ psi (idx + 1) (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1) :
    shiftRemainingBudget P psi (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 + chainShiftDeposit P N₀ psi (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 +
        deeperDeposit P N₀ psi idx st ≤
      shiftRemainingBudget P psi st + chainShiftDeposit P N₀ psi st +
        shiftDeposit P N₀ psi idx * u + deeperDeposit P N₀ psi idx (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1 := by
  rw [shiftRemainingBudget_congr hs hr, chainShiftDeposit_bump hidx hu,
    deeperDeposit_congr (ch := st) (idx + 1) (fun i hi => by rw [hrec]; simp [Nat.ne_of_gt hi])]
    at hIH
  rw [deeperDeposit_split P N₀ psi idx st, deeperDeposit_split P N₀ psi idx (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1]
  have hrec1 : st₁.recUpdates (idx + 1) = st.recUpdates (idx + 1) + U₁.length := by rw [hrec]; simp
  split_ifs at hIH ⊢ with hd
  · have : shiftDeposit P N₀ psi (idx + 1) * st.recUpdates (idx + 1) +
        shiftDeposit P N₀ psi (idx + 1) * U₁.length ≤
        shiftDeposit P N₀ psi (idx + 1) * (Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) st₁ G₁ U₁ 0).1.recUpdates (idx + 1) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (hrec1 ▸ hmono)
    omega
  · omega

/-- The rebuild branch of `updateLoop` at level `idx < d`. -/
private theorem rebuild_combine {T : SparseCoreRestartTool} (L : LastLevelTool)
    {P : ChainParams} {N₀ : ℕ} {psi : ℝ} (hpsi : 0 ≤ psi) {idx : ℕ} (hidx : idx < P.d)
    (st : ChainState T P) (curG : MGraph) (u enc : ℕ)
    (hTh : intRebuildThreshold P N₀ idx < st.updCount idx + u) :
    let st' := (Ordered.algorithm1_rebuild T L P st idx curG enc).1
    shiftRemainingBudget P psi st' + chainShiftDeposit P N₀ psi st' +
        deeperDeposit P N₀ psi idx st ≤
      shiftRemainingBudget P psi st + chainShiftDeposit P N₀ psi st +
        shiftDeposit P N₀ psi idx * u + deeperDeposit P N₀ psi idx st' := by
  intro st'
  obtain ⟨hr, hs, hrec, hu⟩ := algorithm1_rebuild_counts T L P st hidx curG enc
  have hN := shiftRemainingBudget_rebuild_le P hpsi (ch := st) (ch' := st') idx hs hr
  have hdeep : deeperDeposit P N₀ psi idx st' = deeperDeposit P N₀ psi idx st :=
    deeperDeposit_congr idx (fun i _ => by rw [hrec])
  have hdep : chainShiftDeposit P N₀ psi st' + shiftDeposit P N₀ psi idx * st.updCount idx ≤
      chainShiftDeposit P N₀ psi st := by
    unfold chainShiftDeposit
    have hmem : idx ∈ Finset.range P.d := Finset.mem_range.mpr hidx
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, hu idx,
      ite_eq_left ⟨le_rfl, hidx⟩, Nat.mul_zero, zero_add, Nat.add_comm]
    refine Nat.add_le_add_left (Finset.sum_le_sum fun i _ => ?_) _
    rw [hu i]
    split_ifs <;> simp
  have hQ := rebuildQuotaGain_le_deposit P N₀ psi idx
  have hmul : shiftDeposit P N₀ psi idx * (intRebuildThreshold P N₀ idx + 1) ≤
      shiftDeposit P N₀ psi idx * st.updCount idx + shiftDeposit P N₀ psi idx * u := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The deposit pays for the quota of the rebuilds.** Over the levels `idx, …, d` of
`updateLoop`, the unused shift quota plus the deposit grows by at most `shiftDeposit idx` per
update of the batch entering level `idx < d`, plus `shiftDeposit i` per update forwarded to each
deeper level `i < d` (the growth of `deeperDeposit`). A rebuild at a level is paid by the
deposit of the updates counted there (`rebuild_combine`). -/
theorem updateLoop_quota_deposit (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) {psi : ℝ}
    (hpsi : 0 ≤ psi) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (enc : ℕ),
      idx + rem = P.d →
      let st' := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU enc).1
      shiftRemainingBudget P psi st' + chainShiftDeposit P N₀ psi st' +
          deeperDeposit P N₀ psi idx st ≤
        shiftRemainingBudget P psi st + chainShiftDeposit P N₀ psi st +
          (if idx < P.d then shiftDeposit P N₀ psi idx * curU.length else 0) +
          deeperDeposit P N₀ psi idx st' := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU enc hsum
    have hidx : ¬ idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    rw [ite_eq_right hidx, Nat.add_zero]
    split_ifs <;> exact le_rfl
  | succ rem ih =>
    intro idx st curG curU enc hsum
    have hidx : idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    try rw [ite_eq_left hidx]
    split_ifs with hTh
    · exact rebuild_combine L hpsi hidx
        { st with ℓ := Ordered.rebuildStartFn idx curG ℓ', g := Ordered.rebuildStartFn idx curG g' }
        (Ordered.rebuildStartGraph idx curG) curU.length enc hTh
    · refine step_combine hidx ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rfl
      · exact updateLoop_recUpdates_mono T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0 (idx + 1)
      · exact ih (idx + 1) _ _ _ 0 (by omega)

/-- **The deposit pays for the quota of the rebuilds**, for one `Update` of Algorithm 1: the
unused shift quota plus the deposit grows by at most `shiftDeposit 0` per update of the batch
(when `d > 0`), plus `shiftDeposit i` per update forwarded to each level `0 < i < d`. -/
theorem algorithm1_update_quota_deposit (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) {psi : ℝ} (hpsi : 0 ≤ psi) :
    let ch1 := (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1
    shiftRemainingBudget P psi ch1 + chainShiftDeposit P N₀ psi ch1 +
        deeperDeposit P N₀ psi 0 st ≤
      shiftRemainingBudget P psi st + chainShiftDeposit P N₀ psi st +
        (if 0 < P.d then shiftDeposit P N₀ psi 0 * U.length else 0) +
        deeperDeposit P N₀ psi 0 ch1 := by
  dsimp only [Ordered.algorithm1_update]
  have h := updateLoop_quota_deposit T L TP P N₀ ℓ' g' hpsi P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U) (by omega)
  rw [deeperDeposit_congr (ch := st) 0 (fun i hi => by simp [Nat.ne_of_gt hi])] at h
  exact h

end MinCostFlow.MinRatio
