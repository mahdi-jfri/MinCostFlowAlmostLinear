module

public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.MinRatio.PassReset
public import MinCostFlow.MinRatio.ShiftBranch
import MinCostFlow.Chain.Algorithm1Proofs
public import MinCostFlow.Chain.ConcreteDefs

/-!
# Testing the periodic rebuild threshold

Algorithm 1 (page 20) tests the number of received updates against
the rebuild threshold before applying the next batch. Since the
counter is integral, the machine can compare it to the stored
floor of the model threshold without rounding the test itself.
-/

public section
namespace MinCostFlow.MinRatio
open Chain WordRAM

/-- Floor of the threshold tested by `algorithm1_update` at level `i`. -/
noncomputable def rebuildThresholdWord (TP : SparseCoreParams) (P : ChainParams)
    (N i : ℕ) : ℕ :=
  ⌊SparseCoreTool.updateThreshold P.k (levelM TP P i) N⌋₊

/-- The integer comparison exactly implements the strict model test. -/
theorem rebuildThresholdWord_lt_iff (TP : SparseCoreParams) (P : ChainParams)
    (N i count : ℕ)
    (hthreshold : 0 ≤ SparseCoreTool.updateThreshold P.k (levelM TP P i) N) :
    rebuildThresholdWord TP P N i < count ↔
      SparseCoreTool.updateThreshold P.k (levelM TP P i) N < (count : ℝ) :=
  Nat.floor_lt hthreshold

/-- Agreement with the current Algorithm 1 guard at every counter requires
the stored threshold to equal the floor of its real budget. -/
theorem rebuildGuard_agrees_iff (TP : SparseCoreParams) (P : ChainParams)
    (N i threshold : ℕ) :
    (∀ count : ℕ, threshold < count ↔
      SparseCoreTool.updateThreshold P.k (levelM TP P i) N < (count : ℝ)) ↔
      threshold = rebuildThresholdWord TP P N i := by
  have hcmp (count : ℕ) := rebuildThresholdWord_lt_iff TP P N i count
    (updateThreshold_nonneg P.k (levelM TP P i) N)
  constructor
  · intro h
    apply Nat.le_antisymm
    · exact Nat.le_of_not_gt (fun hlt => (Nat.lt_irrefl threshold)
        ((h threshold).mpr ((hcmp threshold).mp hlt)))
    · exact Nat.le_of_not_gt (fun hlt => (Nat.lt_irrefl (rebuildThresholdWord TP P N i))
        ((hcmp _).mpr ((h _).mp hlt)))
  · rintro rfl
    exact hcmp

/-- A fixed-point enclosure of the squared logarithm suffices to
identify the exact stored threshold when both endpoints give the same
floor. The two tests use cross multiplication by the shared scale. -/
theorem rebuildThresholdWord_eq_of_scaled_bounds
    (TP : SparseCoreParams) (P : ChainParams) (N i lower upper scale q : ℕ)
    (hscale : 0 < scale)
    (hlo : (lower : ℝ) / scale ≤ (Real.log ((N : ℝ) + 2)) ^ 2)
    (hhi : (Real.log ((N : ℝ) + 2)) ^ 2 ≤ (upper : ℝ) / scale)
    (hleft : q * P.k * upper ≤ levelM TP P i * scale)
    (hright : levelM TP P i * scale < (q + 1) * P.k * lower) :
    rebuildThresholdWord TP P N i = q := by
  have hs : (0 : ℝ) < scale := Nat.cast_pos.mpr hscale
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hlog : 0 < Real.log ((N : ℝ) + 2) := by
    apply Real.log_pos
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith only [hN]
  have hden : 0 < (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2 :=
    mul_pos hk (pow_pos hlog _)
  have hleft' : (q : ℝ) * (P.k : ℝ) * upper ≤ (levelM TP P i : ℝ) * scale := by
    exact_mod_cast hleft
  have hright' : (levelM TP P i : ℝ) * scale < ((q : ℝ) + 1) * (P.k : ℝ) * lower := by
    exact_mod_cast hright
  unfold rebuildThresholdWord
  rw [Nat.floor_eq_iff (updateThreshold_nonneg _ _ _), SparseCoreTool.updateThreshold]
  constructor
  · apply (le_div_iff₀ hden).mpr
    have hmult := mul_le_mul_of_nonneg_left hhi
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hk.le)
    calc
      _ ≤ ((q : ℝ) * P.k) * ((upper : ℝ) / scale) := by simpa only [mul_assoc] using hmult
      _ ≤ _ := by rw [← mul_div_assoc]; exact (div_le_iff₀ hs).mpr hleft'
  · apply (div_lt_iff₀ hden).mpr
    have hmult := mul_le_mul_of_nonneg_left hlo
      (mul_nonneg (by positivity : 0 ≤ (q : ℝ) + 1) hk.le)
    calc
      _ < (((q : ℝ) + 1) * P.k) * ((lower : ℝ) / scale) := by
        rw [← mul_div_assoc]
        exact (lt_div_iff₀ hs).mpr hright'
      _ ≤ _ := by simpa only [mul_assoc] using hmult

/-- The stored threshold is bounded by four times the level size divided
by the branching factor. This uses the model's logarithm bound. -/
theorem rebuildThresholdWord_le (TP : SparseCoreParams) (P : ChainParams) (N i : ℕ) :
    rebuildThresholdWord TP P N i ≤ 4 * levelM TP P i / P.k := by
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hfloor := Nat.floor_le (updateThreshold_nonneg P.k (levelM TP P i) N)
  have hcast : (rebuildThresholdWord TP P N i : ℝ) * (P.k : ℝ) ≤ 4 * (levelM TP P i : ℝ) :=
    (le_div_iff₀ hk).mp (hfloor.trans (updateThreshold_le_four_div P.k (levelM TP P i) N P.hk))
  exact (Nat.le_div_iff_mul_le P.hk).mpr (by exact_mod_cast hcast)

/-- A counter below the threshold stays in range for the next comparison
when a machine word covers the threshold bound plus the batch size. -/
theorem rebuildGuard_count_add_lt {w N i count batch : ℕ}
    (TP : SparseCoreParams) (P : ChainParams)
    (hcount : (count : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P i) N)
    (hword : 4 * levelM TP P i / P.k + batch < 2 ^ w) :
    count + batch < 2 ^ w := by
  have h₁ : count ≤ rebuildThresholdWord TP P N i :=
    (Nat.le_floor_iff (updateThreshold_nonneg P.k (levelM TP P i) N)).mpr hcount
  exact (Nat.add_le_add_right (h₁.trans (rebuildThresholdWord_le TP P N i)) batch).trans_lt hword

/-- Compare the stored threshold in register 0 with the sum of the
received count in register 1 and the batch size in register 2. -/
@[expose] def rebuildGuard : Stmt :=
  .assign 3 (.bin .lt (.reg 0) (.bin .add (.reg 1) (.reg 2)))

/-- Compare a stored integer threshold with the updated counter in six steps. -/
theorem rebuildGuard_integer_runs {w threshold count batch : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hthresholdReg : st.regs 0 = threshold)
    (hcount : st.regs 1 = count) (hbatch : st.regs 2 = batch)
    (hsum : count + batch < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω rebuildGuard st .normal out 6 ∧
      out.regs 3 = (if threshold < count + batch then 1 else 0) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r ≠ 3, out.regs r = st.regs r) := by
  classical
  let flag := if threshold < count + batch then 1 else 0
  let out := { st with regs := Function.update st.regs 3 flag }
  have hflag : flag < 2 ^ w := by
    dsimp [flag]
    split <;> omega
  have heval : (Expr.bin .lt (.reg 0) (.bin .add (.reg 1) (.reg 2))).eval w st =
      some flag := by
    have hbin : BinOp.lt.eval (threshold) (count + batch) = flag := by
      simp only [BinOp.eval, flag]
    simp [Expr.eval, hthresholdReg, hcount, hbatch, hsum, hbin, hflag]
  exact ⟨out, runs_assign_iff.mpr ⟨flag, heval, rfl, rfl, rfl⟩, by simp [out, flag], rfl, rfl,
    fun _ hr => Function.update_of_ne hr _ _⟩

/-- The comparison takes six steps and writes the exact rebuild flag. -/
theorem rebuildGuard_runs {w N i count batch : ℕ} (TP : SparseCoreParams) (P : ChainParams)
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hthreshold : 0 ≤ SparseCoreTool.updateThreshold P.k (levelM TP P i) N)
    (hthresholdReg : st.regs 0 = rebuildThresholdWord TP P N i)
    (hcount : st.regs 1 = count) (hbatch : st.regs 2 = batch)
    (hsum : count + batch < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω rebuildGuard st .normal out 6 ∧
      out.regs 3 = (if SparseCoreTool.updateThreshold P.k (levelM TP P i) N <
        ((count + batch : ℕ) : ℝ) then 1 else 0) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r ≠ 3, out.regs r = st.regs r) := by
  simpa only [rebuildThresholdWord_lt_iff TP P N i (count + batch) hthreshold] using
    rebuildGuard_integer_runs hthresholdReg hcount hbatch hsum hw

/-- The certified integer guard forwards only batches within the sparse-core
update budget and charges a rebuild to at least one forty-eighth of that budget. -/
theorem concreteLevelRebuildCount_guard_bounds
    (TP : SparseCoreParams) (P : ChainParams) (a s i n count : ℕ)
    (hs : 0 < s) (hi : i ≤ P.d) (hγ : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / s)
    (hhi : (a : ℝ) / s ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1)) :
    let threshold := concreteLevelRebuildCount P.M₀ P.k a s i n
    let budget := SparseCoreTool.updateThreshold P.k (levelM TP P i) n
    (count ≤ threshold → (count : ℝ) ≤ budget) ∧
      (threshold < count → budget ≤ 48 * (count : ℝ)) := by
  dsimp only
  obtain ⟨hSafe, hCharge⟩ := concreteLevelRebuildCount_bounds TP P a s i n hs hi hγ hlo hhi
  refine ⟨fun hc => (Nat.cast_le.mpr hc).trans hSafe, fun hc => hCharge.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact_mod_cast (Nat.succ_le_of_lt hc)

/-- The next integer guard can add the batch in one word when the previous
counter was retained by the guard and the model's size bound fits. -/
theorem concreteLevelRebuildCount_count_add_lt
    {w a s i n count batch : ℕ} (TP : SparseCoreParams) (P : ChainParams)
    (hs : 0 < s) (hi : i ≤ P.d) (hγ : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / s)
    (hhi : (a : ℝ) / s ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1))
    (hcount : count ≤ concreteLevelRebuildCount P.M₀ P.k a s i n)
    (hword : 4 * levelM TP P i / P.k + batch < 2 ^ w) :
    count + batch < 2 ^ w :=
  rebuildGuard_count_add_lt TP P
    ((concreteLevelRebuildCount_guard_bounds TP P a s i n count hs hi hγ hlo hhi).1 hcount)
    hword

/-- Increment the level counter at the table base in register 0 and the
index in register 1. Algorithm 1 uses this store for a rebuild or shift. -/
@[expose] def incrementLevelCounter : Stmt :=
  .store (.bin .add (.reg 0) (.reg 1))
    (.bin .add (.load (.bin .add (.reg 0) (.reg 1))) (.const 1))

theorem incrementLevelCounter_noRand : incrementLevelCounter.NoRand := by
  simp [incrementLevelCounter, Stmt.NoRand]

/-- The word-sized counter increment costs ten steps and writes one cell. -/
theorem incrementLevelCounter_runs {w base level count : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = level)
    (hc : st.mem (base + level) = count) (ha : base + level < 2 ^ w)
    (hnext : count + 1 < 2 ^ w) :
    ∃ out, Runs w p ω incrementLevelCounter st .normal out 10 ∧
      out.mem = Function.update st.mem (base + level) (count + 1) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  have hone : 1 < 2 ^ w := by omega
  let out := { st with mem := Function.update st.mem (base + level) (count + 1) }
  refine ⟨out, runs_store_iff.mpr ⟨base + level, count + 1, ?_, ?_, rfl, rfl, rfl⟩,
    rfl, rfl, rfl⟩
  · simp [Expr.eval, BinOp.eval, hb, hi, ha]
  · simp [Expr.eval, BinOp.eval, hb, hi, ha, hc, hone, hnext]

/-- A periodic rebuild increments exactly its level's rebuild counter, as
in Algorithm 1 (page 20) and its scheduling use in Algorithm 2 (page 29). -/
theorem incrementRebuildCounter_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (extraEnc : ℕ)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val)
    (htable : ∀ j : Fin (P.d + 1), st.mem (base + j.val) = chain.rebuildCount j.val)
    (ha : base + i.val < 2 ^ w) (hnext : chain.rebuildCount i.val + 1 < 2 ^ w) :
    ∃ out, Runs w p ω incrementLevelCounter st .normal out 10 ∧
      out.regs = st.regs ∧ out.pos = st.pos ∧
      ∀ j : Fin (P.d + 1), out.mem (base + j.val) =
        (algorithm1_rebuild T L P chain i.val G extraEnc).1.rebuildCount j.val := by
  let index : Fin (P.d + 1) := ⟨i.val, i.isLt.trans (Nat.lt_succ_self _)⟩
  obtain ⟨out, hr, hm, hregs, hp⟩ :=
    incrementLevelCounter_runs (ω := ω) hb hi (htable index) ha hnext
  refine ⟨out, hr, hregs, hp, fun j => ?_⟩
  rw [hm]
  unfold algorithm1_rebuild
  simp only [i.isLt, dite_true]
  change Function.update st.mem (base + i.val) (chain.rebuildCount i.val + 1)
    (base + j.val) = if j.val = i.val then chain.rebuildCount i.val + 1 else chain.rebuildCount j.val
  by_cases hj : j.val = i.val
  · simp [hj]
  · simp [hj, htable j]

private theorem rebuildSuffix_updateCount (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ g : ℕ → ℝ) :
    ∀ (rem first : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd enc dec fwd : ℕ → ℕ) (j : ℕ),
      (rebuildSuffix T L P lvlM N₀ ℓ g rem first G sc bran upd enc dec fwd).2.2.2.1 j =
        if first ≤ j ∧ j < first + rem then 0 else upd j := by
  intro rem
  induction rem with
  | zero =>
    intro first G sc bran upd enc dec fwd j
    simp [rebuildSuffix]
  | succ rem ih =>
    intro first G sc bran upd enc dec fwd j
    dsimp only [rebuildSuffix]
    rw [ih]
    by_cases hj : j = first
    · subst j
      simp
    · have h : first + 1 ≤ j ∧ j < first + (rem + 1) ↔
          first ≤ j ∧ j < first + (rem + 1) := by omega
      simp only [hj, ite_false, Nat.add_right_comm first 1 rem, Nat.add_assoc, h]

/-- Algorithm 1's periodic rebuild (page 20) clears its received-update
counter and those of deeper nonterminal levels. -/
theorem resetRebuildUpdateCounts_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (extraEnc : ℕ)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.updCount j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d - i.val) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_rebuild T L P chain i.val G extraEnc).1.updCount j.val := by
  obtain ⟨out, cost, hr, hc, hp, hm⟩ :=
    resetRebuiltPasses_table_runs (ω := ω) i (fun j => chain.updCount j.val)
      hb hi hend htable hbound hw
  refine ⟨out, cost, hr, hc, hp, fun j => ?_⟩
  rw [hm]
  unfold algorithm1_rebuild
  simp only [i.isLt, dite_true]
  change _ = (rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i.val) i.val
    (fun j => if j = i.val then G else chain.G j) chain.scState chain.bran chain.updCount
    chain.curEnc chain.curDecUpdates chain.curFwd).2.2.2.1 j.val
  rw [rebuildSuffix_updateCount, Nat.add_sub_of_le i.isLt.le]
  change (if i.val ≤ j.val then 0 else _) = _
  simp [j.isLt]

/-- When Algorithm 1 (page 21) forwards a batch without rebuilding, record
its size in the received-update counter. Register 4 holds the counter address. -/
@[expose] def recordForwardedBatch : Stmt :=
  .cond (.reg 3) .nop (.store (.reg 4) (.bin .add (.reg 1) (.reg 2)))

theorem recordForwardedBatch_noRand : recordForwardedBatch.NoRand := by
  simp [recordForwardedBatch, Stmt.NoRand]

/-- The threshold flag determines whether the received-update counter is
advanced. The update writes one cell and costs at most seven steps. -/
theorem recordForwardedBatch_runs {w addr count batch : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (rebuild : Bool)
    (hcount : st.regs 1 = count) (hbatch : st.regs 2 = batch)
    (hflag : st.regs 3 = if rebuild then 1 else 0)
    (haddr : st.regs 4 = addr) (hsum : count + batch < 2 ^ w) :
    ∃ out cost, Runs w p ω recordForwardedBatch st .normal out cost ∧
      cost ≤ 7 ∧ out.regs = st.regs ∧ out.pos = st.pos ∧
      out.mem = if rebuild then st.mem else Function.update st.mem addr (count + batch) := by
  cases rebuild
  · let out := { st with mem := Function.update st.mem addr (count + batch) }
    have hstore : Runs w p ω (.store (.reg 4) (.bin .add (.reg 1) (.reg 2))) st .normal out 5 :=
      runs_store_iff.mpr ⟨addr, count + batch, by simp [Expr.eval, haddr],
        by simp [Expr.eval, BinOp.eval, hcount, hbatch, hsum], rfl, rfl, rfl⟩
    exact ⟨out, 7, runs_cond_iff.mpr ⟨0, 5, by simp [Expr.eval, hflag],
      by simpa using hstore, rfl⟩, le_rfl, rfl, rfl, rfl⟩
  · exact ⟨st, 3, runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, hflag],
      by simp only [one_ne_zero, ite_false]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
      by decide, rfl, rfl, rfl⟩

/-- Test for a periodic rebuild and advance the counter only on the
forwarding path of Algorithm 1 Update (page 21). -/
@[expose] def guardAndRecordForwardedBatch : Stmt :=
  rebuildGuard ;; recordForwardedBatch

theorem guardAndRecordForwardedBatch_noRand : guardAndRecordForwardedBatch.NoRand := by
  simp [guardAndRecordForwardedBatch, rebuildGuard, recordForwardedBatch_noRand, Stmt.NoRand]

/-- Compare the certified integer threshold and record the batch only
when the resulting counter stays within that threshold. -/
theorem guardAndRecordForwardedBatch_integer_runs {w threshold addr count batch : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hthresholdReg : st.regs 0 = threshold)
    (hcount : st.regs 1 = count) (hbatch : st.regs 2 = batch) (haddr : st.regs 4 = addr)
    (hsum : count + batch < 2 ^ w) (hw : 1 < 2 ^ w) :
    let over := threshold < count + batch
    ∃ out cost, Runs w p ω guardAndRecordForwardedBatch st .normal out cost ∧ cost ≤ 14 ∧
      out.regs 3 = (if over then 1 else 0) ∧ out.pos = st.pos ∧
      out.mem = if over then st.mem else Function.update st.mem addr (count + batch) := by
  dsimp only
  obtain ⟨mid, hg, hflag, hm, hp, hframe⟩ :=
    rebuildGuard_integer_runs (ω := ω)
      hthresholdReg hcount hbatch hsum hw
  let over := threshold < count + batch
  obtain ⟨out, cost, hr, hc, hregs, hp', hm'⟩ :=
    recordForwardedBatch_runs (ω := ω) (decide over)
      ((hframe 1 (by decide)).trans hcount) ((hframe 2 (by decide)).trans hbatch)
      (by simpa [over] using hflag) ((hframe 4 (by decide)).trans haddr) hsum
  exact ⟨out, 6 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 6, cost, hg, hr, rfl⟩),
    by omega, (congrFun hregs 3).trans hflag, hp'.trans hp, by simpa [over, hm] using hm'⟩

/-- The combined periodic test and conditional store take at most fourteen
steps. On the rebuild path they leave the counter for the suffix reset. -/
theorem guardAndRecordForwardedBatch_runs {w N i addr count batch : ℕ}
    (TP : SparseCoreParams) (P : ChainParams) {p : Program} {st : State} {ω : ℕ → Bool}
    (hthresholdReg : st.regs 0 = rebuildThresholdWord TP P N i)
    (hcount : st.regs 1 = count) (hbatch : st.regs 2 = batch) (haddr : st.regs 4 = addr)
    (hsum : count + batch < 2 ^ w) (hw : 1 < 2 ^ w) :
    let over := SparseCoreTool.updateThreshold P.k (levelM TP P i) N <
      ((count + batch : ℕ) : ℝ)
    ∃ out cost, Runs w p ω guardAndRecordForwardedBatch st .normal out cost ∧ cost ≤ 14 ∧
      out.regs 3 = (if over then 1 else 0) ∧ out.pos = st.pos ∧
      out.mem = if over then st.mem else Function.update st.mem addr (count + batch) := by
  simpa only [rebuildThresholdWord_lt_iff TP P N i (count + batch)
    (updateThreshold_nonneg P.k (levelM TP P i) N)] using
      guardAndRecordForwardedBatch_integer_runs hthresholdReg hcount hbatch haddr hsum hw

private theorem updateLoop_preserves_earlier_updateCount (T : SparseCoreRestartTool)
    (L : LastLevelTool) (TP : SparseCoreParams) (P : ChainParams)
    (N : ℕ) (ℓ g : ℕ → ℝ) (j : ℕ) :
    ∀ (remaining index : ℕ) (chain : ChainState T P) (G : MGraph)
      (U : List Update) (enc : ℕ), j < index →
      (updateLoop T L TP P N ℓ g remaining index chain G U enc).1.updCount j =
        chain.updCount j := by
  intro remaining
  induction remaining with
  | zero =>
    intro index chain G U enc hj
    simp only [updateLoop]
    split <;> rfl
  | succ remaining ih =>
    intro index chain G U enc hj
    simp only [updateLoop]
    split
    · unfold algorithm1_rebuild
      split
      · change (rebuildSuffix T L P chain.lvlM chain.N₀ ℓ g (P.d - index) index
          (fun k => if k = index then G else chain.G k) chain.scState chain.bran
          chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd).2.2.2.1 j = _
        rw [rebuildSuffix_updateCount]
        simp [Nat.not_le.mpr hj]
      · rfl
    · dsimp only
      rw [ih (index + 1) _ _ _ _ (by omega)]
      simp [Nat.ne_of_lt hj]

/-- The selected level's counter after a forwarding iteration of
Algorithm 1 Update (page 21) includes exactly the received batch.
Processing later levels preserves it, including if they rebuild. -/
theorem updateLoop_forwarded_updateCount (T : SparseCoreRestartTool)
    (L : LastLevelTool) (TP : SparseCoreParams) (P : ChainParams)
    (N : ℕ) (ℓ g : ℕ → ℝ) (remaining index : ℕ) (chain : ChainState T P)
    (G : MGraph) (U : List Update) (enc : ℕ)
    (hforward : ¬ intRebuildThreshold P N index < chain.updCount index + U.length) :
    (updateLoop T L TP P N ℓ g (remaining + 1) index chain G U enc).1.updCount index =
      chain.updCount index + U.length := by
  simp only [updateLoop, hforward, ite_false]
  rw [updateLoop_preserves_earlier_updateCount T L TP P N ℓ g index remaining (index + 1)
    _ _ _ _ (Nat.lt_succ_self _)]
  simp

/-- On the forwarding path, the machine counter equals the counter in the
result of the model's Algorithm 1 Update loop (page 21). -/
theorem guardAndRecordForwardedBatch_updateLoop_runs {T : SparseCoreRestartTool}
    (L : LastLevelTool) (TP : SparseCoreParams) {P : ChainParams}
    (N : ℕ) (ℓ g : ℕ → ℝ) (remaining index : ℕ) (chain : ChainState T P)
    (G : MGraph) (U : List Update) (enc : ℕ) {w addr : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hthreshold : st.regs 0 = intRebuildThreshold P N index)
    (hcount : st.regs 1 = chain.updCount index) (hbatch : st.regs 2 = U.length)
    (haddr : st.regs 4 = addr) (hsum : chain.updCount index + U.length < 2 ^ w)
    (hw : 1 < 2 ^ w)
    (hforward : ¬ intRebuildThreshold P N index < chain.updCount index + U.length) :
    let next := (updateLoop T L TP P N ℓ g (remaining + 1) index chain G U enc).1
    ∃ out cost, Runs w p ω guardAndRecordForwardedBatch st .normal out cost ∧
      cost ≤ 14 ∧ out.regs 3 = 0 ∧ out.pos = st.pos ∧
      out.mem = Function.update st.mem addr (next.updCount index) := by
  obtain ⟨out, cost, hr, hc, hf, hp, hm⟩ :=
    guardAndRecordForwardedBatch_integer_runs (ω := ω) hthreshold hcount hbatch haddr hsum hw
  have hmodel := updateLoop_forwarded_updateCount T L TP P N ℓ g remaining index chain G U enc
    hforward
  exact ⟨out, cost, hr, hc, by simpa only [hforward, ite_false] using hf, hp,
    by simpa only [hforward, hmodel, ite_false] using hm⟩

/-- Once the periodic test selects a rebuild, Algorithm 1 Update (page 21)
stops forwarding and uses the rebuild's received-update table. -/
theorem resetRebuildUpdateCounts_updateLoop_runs {T : SparseCoreRestartTool}
    (L : LastLevelTool) (TP : SparseCoreParams) {P : ChainParams}
    (N : ℕ) (ℓ g : ℕ → ℝ) (remaining : ℕ) (i : Fin P.d) (chain : ChainState T P)
    (G : MGraph) (U : List Update) (enc : ℕ)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.updCount j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hover : intRebuildThreshold P N i.val < chain.updCount i.val + U.length) :
    let next := (updateLoop T L TP P N ℓ g (remaining + 1) i.val chain G U enc).1
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d - i.val) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin P.d, out.mem (base + j.val) = next.updCount j.val := by
  simp only [updateLoop, hover, ite_true]
  exact resetRebuildUpdateCounts_runs (L := L) { chain with ℓ := ℓ, g := g }
    i G enc hb hi hend htable hbound hw

/-- The branch shift in Algorithm 1 (page 20) starts its suffix rebuild
at the following level. Its own received-update counter is preserved. -/
theorem resetShiftUpdateCounts_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val + 1) (hend : st.regs 2 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.updCount j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d - (i.val + 1)) + 7 ∧ out.pos = st.pos ∧
      (∀ r ≠ 19, out.regs r = st.regs r) ∧
      (∀ a, (a < base + (i.val + 1) ∨ base + P.d ≤ a) → out.mem a = st.mem a) ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_shift T L P chain i.val).1.updCount j.val := by
  have hstart : i.val + 1 ≤ P.d := i.isLt
  obtain ⟨out, cost, hr, hc, hm, hregs, hp⟩ :=
    resetPassSuffix_runs (ω := ω) hb hi hend hstart hbound hw
  refine ⟨out, cost, hr, hc, hp, hregs, ?_, fun j => ?_⟩
  · intro a ha
    have hnone : ¬ (base + (i.val + 1) ≤ a ∧ a < base + P.d) := by omega
    simp [hm, hnone]
  · rw [hm, htable j]
    rw [show (algorithm1_shift T L P chain i.val).1.updCount j.val =
        if i.val + 1 ≤ j.val ∧ j.val < P.d then 0 else chain.updCount j.val from by
      unfold algorithm1_shift
      simp only [i.isLt, dite_true]
      rw [rebuildSuffix_updateCount, Nat.add_sub_of_le hstart]]
    have hspan : (base + (i.val + 1) ≤ base + j.val ∧ base + j.val < base + P.d) ↔
        (i.val + 1 ≤ j.val ∧ j.val < P.d) := by omega
    simp only [hspan]

/-- Nonterminal Shift in Algorithm 1 (page 20) restarts the selected
spanner and reinitializes the deeper tools. Increment the selected
restart count and clear the deeper counts using the suffix update. -/
theorem advanceShiftRestartCounts_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (hflag : st.regs 3 = 1)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.curRestarts j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.curRestarts i.val + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω advanceShiftPasses st .normal out cost ∧
      cost ≤ 14 * (P.d - (i.val + 1)) + 25 ∧ out.pos = st.pos ∧
      (∀ a, (a < base + i.val ∨ base + P.d ≤ a) → out.mem a = st.mem a) ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_shift T L P chain i.val).1.curRestarts j.val := by
  obtain ⟨out, cost, hr, hc, hp, hframe, hm⟩ :=
    advanceShiftPasses_table_runs (ω := ω) i (fun j => chain.curRestarts j.val) true
      hb hi hend (by simpa using hflag) htable hbound hw (fun _ => hnext)
  refine ⟨out, cost, hr, hc, hp, hframe, fun j => ?_⟩
  rw [hm]
  unfold algorithm1_shift
  simp only [i.isLt, dite_true]
  change (if i.val < j.val then 0 else if j = i then _ else _) =
    if j.val = i.val then _ else if i.val + 1 ≤ j.val ∧ j.val < P.d then 0 else _
  by_cases hj : j = i
  · subst j
    simp
  · have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp [hj, hne, j.isLt]

/-- A periodic rebuild clears the restart counts of the nonterminal tools
it reinitializes (Algorithm 1, page 20). -/
theorem resetRebuildRestartCounts_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.curRestarts j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d - i.val) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_rebuild T L P chain i.val G enc).1.curRestarts j.val := by
  obtain ⟨out, cost, hr, hc, hp, hm⟩ :=
    resetRebuiltPasses_table_runs (ω := ω) i (fun j => chain.curRestarts j.val)
      hb hi hend htable hbound hw
  refine ⟨out, cost, hr, hc, hp, fun j => ?_⟩
  rw [hm]
  unfold algorithm1_rebuild
  simp only [i.isLt, dite_true]
  change (if i.val ≤ j.val then 0 else _) = _
  simp [j.isLt]

/-- Update the two counters affected by the nonterminal Shift restart in
Algorithm 1 (page 20). Register 4 supplies the restart table base. -/
@[expose] def shiftLevelCounters : Stmt :=
  resetPassSuffix ;;
  .assign 0 (.reg 4) ;;
  .assign 1 (.bin .sub (.reg 1) (.const 1)) ;;
  advanceShiftPasses

theorem shiftLevelCounters_noRand : shiftLevelCounters.NoRand := by
  simp [shiftLevelCounters, resetPassSuffix_noRand, advanceShiftPasses_noRand, Stmt.NoRand]

/-- Switching tables and recording both counters costs at most 28 steps
per deeper level plus 41 steps. -/
theorem shiftLevelCounters_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d)
    {w updates restarts : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = updates) (hi : st.regs 1 = i.val + 1) (hend : st.regs 2 = P.d)
    (hflag : st.regs 3 = 1) (hrbase : st.regs 4 = restarts)
    (hu : ∀ j : Fin P.d, st.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, st.mem (restarts + j.val) = chain.curRestarts j.val)
    (hdisjoint : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.curRestarts i.val + 1 < 2 ^ w) :
    let next := (algorithm1_shift T L P chain i.val).1
    ∃ out cost, Runs w p ω shiftLevelCounters st .normal out cost ∧
      cost ≤ 28 * (P.d - (i.val + 1)) + 41 ∧ out.pos = st.pos ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      ∀ a, (a < updates + (i.val + 1) ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) → out.mem a = st.mem a := by
  obtain ⟨mid, c, huRun, hc, hp, hregs, hmem, hup⟩ :=
    resetShiftUpdateCounts_runs (L := L) (ω := ω) chain i hb hi hend hu hub hw
  let s0 := { mid with regs := Function.update mid.regs 0 restarts }
  let s1 := { s0 with regs := Function.update s0.regs 1 i.val }
  have h0 : Runs w p ω (.assign 0 (.reg 4)) mid .normal s0 2 :=
    runs_assign_iff.mpr ⟨restarts, by simp [Expr.eval, hregs 4 (by decide), hrbase],
      rfl, rfl, rfl⟩
  have hilevel : i.val < 2 ^ w := by have := i.isLt; omega
  have h1 : Runs w p ω (.assign 1 (.bin .sub (.reg 1) (.const 1))) s0 .normal s1 4 :=
    runs_assign_iff.mpr ⟨i.val, by
      simp [Expr.eval, BinOp.eval, s0, Function.update_of_ne, hregs 1 (by decide), hi, hw, hilevel],
      rfl, rfl, rfl⟩
  obtain ⟨out, c', hrRun, hc', hp', hframe, hrout⟩ :=
    advanceShiftRestartCounts_runs (L := L) (ω := ω) (st := s1) chain i
      (by simp [s1, s0, Function.update_of_ne]) (by simp [s1])
      (by simp [s1, s0, Function.update_of_ne, hregs 2 (by decide), hend])
      (by simp [s1, s0, Function.update_of_ne, hregs 3 (by decide), hflag])
      (fun j => by
        change mid.mem (restarts + j.val) = _
        have hj := j.isLt
        rw [hmem _ (by omega), hrr j]) hrb hw hnext
  refine ⟨out, c + (2 + (4 + c' + 1) + 1) + 1, ?_, by omega, hp'.trans hp, ?_, hrout, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, huRun,
      runs_seq_iff.mpr (Or.inr ⟨s0, 2, _, h0,
        runs_seq_iff.mpr (Or.inr ⟨s1, 4, c', h1, hrRun, rfl⟩), rfl⟩), rfl⟩)
  · intro j
    have hj := j.isLt
    exact (hframe _ (by omega)).trans (hup j)
  · intro a huOutside hrOutside
    exact (hframe a hrOutside).trans (hmem a huOutside)

/-- Reset the received-update and restart tables from the periodic rebuild
level onward (Algorithm 1, page 20). Register 4 holds the restart table base. -/
@[expose] def rebuildLevelCounters : Stmt :=
  resetPassSuffix ;; .assign 0 (.reg 4) ;; resetPassSuffix

theorem rebuildLevelCounters_noRand : rebuildLevelCounters.NoRand := by
  simp [rebuildLevelCounters, resetPassSuffix_noRand, Stmt.NoRand]

/-- The two disjoint tables are reset in at most 28 steps per rebuilt
nonterminal level plus 18 steps. -/
theorem rebuildLevelCounters_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {w updates restarts : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = updates) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (hrbase : st.regs 4 = restarts)
    (hu : ∀ j : Fin P.d, st.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, st.mem (restarts + j.val) = chain.curRestarts j.val)
    (hdisjoint : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w) (hw : 1 < 2 ^ w) :
    let next := (algorithm1_rebuild T L P chain i.val G enc).1
    ∃ out cost, Runs w p ω rebuildLevelCounters st .normal out cost ∧
      cost ≤ 28 * (P.d - i.val) + 18 ∧ out.pos = st.pos ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      (∀ a, (a < updates + i.val ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 0 → r ≠ 19 → out.regs r = st.regs r) := by
  obtain ⟨mid, c, huRun, hc, hm, hregs, hp⟩ :=
    resetPassSuffix_runs (ω := ω) hb hi hend i.isLt.le hub hw
  let setup := { mid with regs := Function.update mid.regs 0 restarts }
  have hsetup : Runs w p ω (.assign 0 (.reg 4)) mid .normal setup 2 :=
    runs_assign_iff.mpr ⟨restarts, by simp [Expr.eval, hregs 4 (by decide), hrbase],
      rfl, rfl, rfl⟩
  obtain ⟨out, c', hrRun, hc', hm', hregs', hp'⟩ :=
    resetPassSuffix_runs (ω := ω) (st := setup) (base := restarts) (first := i.val) (stop := P.d)
      (by simp [setup]) (by simp [setup, Function.update_of_ne, hregs 1 (by decide), hi])
      (by simp [setup, Function.update_of_ne, hregs 2 (by decide), hend])
      i.isLt.le hrb hw
  refine ⟨out, c + (2 + c' + 1) + 1, ?_, by omega, hp'.trans hp, ?_, ?_, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, huRun,
      runs_seq_iff.mpr (Or.inr ⟨setup, 2, c', hsetup, hrRun, rfl⟩), rfl⟩)
  · intro j
    have hj := j.isLt
    have hne : ¬ (restarts + i.val ≤ updates + j.val ∧ updates + j.val < restarts + P.d) := by omega
    rw [hm', ite_eq_right hne]
    change mid.mem (updates + j.val) = _
    rw [hm, hu j]
    unfold algorithm1_rebuild
    simp only [i.isLt, dite_true]
    change _ = (rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i.val) i.val
      (fun j => if j = i.val then G else chain.G j) chain.scState chain.bran chain.updCount
      chain.curEnc chain.curDecUpdates chain.curFwd).2.2.2.1 j.val
    rw [rebuildSuffix_updateCount, Nat.add_sub_of_le i.isLt.le]
    simp [hj]
  · intro j
    have hj := j.isLt
    have hne : ¬ (updates + i.val ≤ restarts + j.val ∧ restarts + j.val < updates + P.d) := by omega
    rw [hm']
    change (if _ then 0 else mid.mem (restarts + j.val)) = _
    rw [hm, ite_eq_right hne, hrr j]
    unfold algorithm1_rebuild
    simp [i.isLt, hj]

  · intro a hOutsideUpdates hOutsideRestarts
    have hu' : ¬ (updates + i.val ≤ a ∧ a < updates + P.d) := by omega
    have hr' : ¬ (restarts + i.val ≤ a ∧ a < restarts + P.d) := by omega
    rw [hm', ite_eq_right hr']
    exact (hm a).trans (ite_eq_right hu')
  · intro r hr₀ hr₁₉
    rw [hregs' r hr₁₉]
    change Function.update mid.regs 0 restarts r = _
    rw [Function.update_of_ne hr₀, hregs r hr₁₉]

/-- Record the periodic rebuild after resetting the counters of the
reinitialized tools. Register 5 holds the rebuild counter table base. -/
@[expose] def recordPeriodicRebuild : Stmt :=
  rebuildLevelCounters ;; .assign 0 (.reg 5) ;; incrementLevelCounter

theorem recordPeriodicRebuild_noRand : recordPeriodicRebuild.NoRand := by
  simp [recordPeriodicRebuild, rebuildLevelCounters_noRand, incrementLevelCounter_noRand, Stmt.NoRand]

/-- The three counter tables agree with Algorithm 1 Rebuild (page 20)
after the two suffix resets and the selected-level increment. -/
theorem recordPeriodicRebuild_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {w updates restarts rebuilds : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = updates) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (hrbase : st.regs 4 = restarts) (hcbase : st.regs 5 = rebuilds)
    (hu : ∀ j : Fin P.d, st.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, st.mem (restarts + j.val) = chain.curRestarts j.val)
    (hreb : ∀ j : Fin (P.d + 1), st.mem (rebuilds + j.val) = chain.rebuildCount j.val)
    (hur : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (huc : updates + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ updates)
    (hrc : restarts + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ restarts)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w)
    (hcb : rebuilds + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.rebuildCount i.val + 1 < 2 ^ w) :
    let next := (algorithm1_rebuild T L P chain i.val G enc).1
    ∃ out cost, Runs w p ω recordPeriodicRebuild st .normal out cost ∧
      cost ≤ 28 * (P.d - i.val) + 32 ∧ out.pos = st.pos ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      (∀ j : Fin (P.d + 1), out.mem (rebuilds + j.val) = next.rebuildCount j.val) ∧
      ∀ a, (a < updates + i.val ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) →
        a ≠ rebuilds + i.val → out.mem a = st.mem a := by
  obtain ⟨mid, c, hr, hc, hp, hup, hrest, hmem, hregs⟩ :=
    rebuildLevelCounters_runs (L := L) (ω := ω) chain i G enc hb hi hend hrbase hu hrr hur hub hrb hw
  let setup := { mid with regs := Function.update mid.regs 0 rebuilds }
  have hsetup : Runs w p ω (.assign 0 (.reg 5)) mid .normal setup 2 :=
    runs_assign_iff.mpr ⟨rebuilds, by simp [Expr.eval, hregs 5 (by decide) (by decide), hcbase],
      rfl, rfl, rfl⟩
  have hcells (j : Fin (P.d + 1)) : setup.mem (rebuilds + j.val) = chain.rebuildCount j.val := by
    have hj := j.isLt
    exact (hmem _ (by omega) (by omega)).trans (hreb j)
  let index : Fin (P.d + 1) := ⟨i.val, i.isLt.trans (Nat.lt_succ_self _)⟩
  have hil := i.isLt
  obtain ⟨out, hstore, hm, _, hp'⟩ :=
    incrementLevelCounter_runs (ω := ω) (st := setup) (by simp [setup])
      (by simp [setup, Function.update_of_ne, hregs 1 (by decide) (by decide), hi, index])
      (hcells index) (by omega) hnext
  refine ⟨out, c + 14, ?_, by omega, hp'.trans hp, ?_, ?_, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, 13, hr,
      runs_seq_iff.mpr (Or.inr ⟨setup, 2, 10, hsetup, hstore, rfl⟩), rfl⟩)
  · intro j
    have hj := j.isLt
    rw [hm, Function.update_of_ne (show updates + j.val ≠ rebuilds + i.val by omega)]
    exact hup j
  · intro j
    have hj := j.isLt
    rw [hm, Function.update_of_ne (show restarts + j.val ≠ rebuilds + i.val by omega)]
    exact hrest j
  · intro j
    rw [hm]
    unfold algorithm1_rebuild
    simp only [hil, dite_true]
    change Function.update setup.mem (rebuilds + i.val) (chain.rebuildCount i.val + 1)
      (rebuilds + j.val) = if j.val = i.val then chain.rebuildCount i.val + 1 else chain.rebuildCount j.val
    by_cases hj : j.val = i.val
    · simp [hj]
    · simp [hj, hcells j]
  · intro a huOutside hrOutside hne
    rw [hm, Function.update_of_ne hne]
    exact hmem a huOutside hrOutside

/-- On the periodic rebuild branch of Algorithm 1 Update (page 21), the
three counter tables agree with the final state of the update loop. -/
theorem recordPeriodicRebuild_updateLoop_runs {T : SparseCoreRestartTool}
    (L : LastLevelTool) (TP : SparseCoreParams) {P : ChainParams}
    (N : ℕ) (ℓ g : ℕ → ℝ) (remaining : ℕ) (chain : ChainState T P)
    (i : Fin P.d) (G : MGraph) (U : List Update) (enc : ℕ)
    {w updates restarts rebuilds : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = updates) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (hrbase : st.regs 4 = restarts) (hcbase : st.regs 5 = rebuilds)
    (hu : ∀ j : Fin P.d, st.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, st.mem (restarts + j.val) = chain.curRestarts j.val)
    (hreb : ∀ j : Fin (P.d + 1), st.mem (rebuilds + j.val) = chain.rebuildCount j.val)
    (hur : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (huc : updates + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ updates)
    (hrc : restarts + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ restarts)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w)
    (hcb : rebuilds + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.rebuildCount i.val + 1 < 2 ^ w)
    (hover : intRebuildThreshold P N i.val < chain.updCount i.val + U.length) :
    let next := (updateLoop T L TP P N ℓ g (remaining + 1) i.val chain G U enc).1
    ∃ out cost, Runs w p ω recordPeriodicRebuild st .normal out cost ∧
      cost ≤ 28 * (P.d - i.val) + 32 ∧ out.pos = st.pos ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      (∀ j : Fin (P.d + 1), out.mem (rebuilds + j.val) = next.rebuildCount j.val) ∧
      ∀ a, (a < updates + i.val ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) →
        a ≠ rebuilds + i.val → out.mem a = st.mem a := by
  simp only [updateLoop, hover, ite_true]
  exact recordPeriodicRebuild_runs (L := L) { chain with ℓ := ℓ, g := g }
    i G enc hb hi hend hrbase hcbase hu hrr hreb hur huc hrc hub hrb hcb hw hnext

/-- The suffix selects branch zero at each rebuilt core and preserves earlier choices. -/
theorem rebuildSuffix_branch (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ g : ℕ → ℝ) :
    ∀ (rem first : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd enc dec fwd : ℕ → ℕ) (j : ℕ),
      (rebuildSuffix T L P lvlM N₀ ℓ g rem first G sc bran upd enc dec fwd).2.2.1 j =
        if first ≤ j ∧ j < first + rem then 0 else bran j := by
  intro rem
  induction rem with
  | zero =>
    intro first G sc bran upd enc dec fwd j
    simp [rebuildSuffix]
  | succ rem ih =>
    intro first G sc bran upd enc dec fwd j
    dsimp only [rebuildSuffix]
    rw [ih]
    by_cases hj : j = first
    · subst j
      simp
    · have h : first + 1 ≤ j ∧ j < first + (rem + 1) ↔
          first ≤ j ∧ j < first + (rem + 1) := by omega
      simp only [hj, ite_false, Nat.add_right_comm first 1 rem, Nat.add_assoc, h]

/-- Each nonterminal tool rebuilt by Algorithm 1 (page 20) starts on
branch zero. Earlier branch cells are preserved. -/
theorem resetRebuildBranches_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.bran j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d - i.val) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_rebuild T L P chain i.val G enc).1.bran j.val := by
  obtain ⟨out, cost, hr, hc, hp, hm⟩ :=
    resetRebuiltPasses_table_runs (ω := ω) i (fun j => chain.bran j.val)
      hb hi hend htable hbound hw
  refine ⟨out, cost, hr, hc, hp, fun j => ?_⟩
  rw [hm]
  unfold algorithm1_rebuild
  simp only [i.isLt, dite_true]
  change _ = (rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i.val) i.val
    (fun j => if j = i.val then G else chain.G j) chain.scState chain.bran chain.updCount
    chain.curEnc chain.curDecUpdates chain.curFwd).2.2.1 j.val
  rw [rebuildSuffix_branch, Nat.add_sub_of_le i.isLt.le]
  change (if i.val ≤ j.val then 0 else _) = _
  simp [j.isLt]

/-- Algorithm 1 Shift (page 20) retains the branch choices above the
shifted level and advances the selected branch. -/
theorem algorithm1_shift_branch_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i j : ℕ) (hi : i < P.d) (hj : j ≤ i) :
    (algorithm1_shift T L P st i).1.bran j =
      if j = i then (st.bran i + 1) % P.k else st.bran j := by
  simp only [algorithm1_shift, hi, dite_true]
  rw [rebuildSuffix_branch]
  simp [show ¬ i + 1 ≤ j by omega]

/-- Algorithm 1 Shift selects branch zero in each rebuilt core below
the shifted level (page 20). -/
theorem algorithm1_shift_rebuilt_branch (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i j : ℕ) (hij : i < j) (hj : j < P.d) :
    (algorithm1_shift T L P st i).1.bran j = 0 := by
  have hi : i < P.d := hij.trans hj
  simp only [algorithm1_shift, hi, dite_true]
  rw [rebuildSuffix_branch, Nat.add_sub_of_le (Nat.succ_le_of_lt hi)]
  simp [Nat.succ_le_of_lt hij, hj]

/-- After advancing the selected branch, Algorithm 1 Shift (page 20)
selects branch zero for each deeper nonterminal tool it rebuilds. -/
theorem resetShiftBranches_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val + 1) (hend : st.regs 2 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) =
      if j.val = i.val then (chain.bran i.val + 1) % P.k else chain.bran j.val)
    (hbound : base + P.d < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d - (i.val + 1)) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_shift T L P chain i.val).1.bran j.val := by
  have hstart : i.val + 1 ≤ P.d := i.isLt
  obtain ⟨out, cost, hr, hc, hm, _, hp⟩ :=
    resetPassSuffix_runs (ω := ω) hb hi hend hstart hbound hw
  refine ⟨out, cost, hr, hc, hp, fun j => ?_⟩
  rw [hm, htable j]
  unfold algorithm1_shift
  simp only [i.isLt, dite_true]
  rw [rebuildSuffix_branch, Nat.add_sub_of_le hstart]
  have hspan : (base + (i.val + 1) ≤ base + j.val ∧ base + j.val < base + P.d) ↔
      (i.val + 1 ≤ j.val ∧ j.val < P.d) := by omega
  simp only [hspan]

/-- Advance the selected branch and reset the deeper branch cells
when their tools are reinitialized by Algorithm 1 Shift (page 20). -/
@[expose] def shiftBranchTable : Stmt :=
  shiftBranch ;;
  .assign 0 (.reg 4) ;;
  .assign 1 (.reg 5) ;;
  .assign 2 (.reg 6) ;;
  resetPassSuffix

theorem shiftBranchTable_noRand : shiftBranchTable.NoRand := by
  simp [shiftBranchTable, shiftBranch_noRand, resetPassSuffix_noRand, Stmt.NoRand]

/-- The nonterminal branch table after the advance and reset agrees
with Algorithm 1 Shift. Register 5 holds the first deeper level. -/
theorem shiftBranchTable_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (ha : st.regs 0 = base + i.val) (hk : st.regs 1 = P.k)
    (hb : st.regs 4 = base) (hi : st.regs 5 = i.val + 1) (hd : st.regs 6 = P.d)
    (htable : ∀ j : Fin P.d, st.mem (base + j.val) = chain.bran j.val)
    (hbranch : chain.bran i.val < P.k) (hkword : P.k < 2 ^ w)
    (hbound : base + P.d < 2 ^ w) :
    ∃ out cost, Runs w p ω shiftBranchTable st .normal out cost ∧
      cost ≤ 14 * (P.d - (i.val + 1)) + 31 ∧ out.pos = st.pos ∧
      ∀ j : Fin P.d, out.mem (base + j.val) =
        (algorithm1_shift T L P chain i.val).1.bran j.val := by
  obtain ⟨mid, hr, hm, _, hregs, hp⟩ :=
    shiftBranch_runs (ω := ω) ha hk (htable i) hbranch hkword
  let s0 := { mid with regs := Function.update mid.regs 0 base }
  let s1 := { s0 with regs := Function.update s0.regs 1 (i.val + 1) }
  let s2 := { s1 with regs := Function.update s1.regs 2 P.d }
  have h0 : Runs w p ω (.assign 0 (.reg 4)) mid .normal s0 2 :=
    runs_assign_iff.mpr ⟨base, by simp [Expr.eval, hregs 4 (by decide), hb], rfl, rfl, rfl⟩
  have h1 : Runs w p ω (.assign 1 (.reg 5)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨i.val + 1, by simp [Expr.eval, s0, Function.update_of_ne, hregs 5 (by decide), hi],
      rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 2 (.reg 6)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨P.d, by simp [Expr.eval, s1, s0, Function.update_of_ne, hregs 6 (by decide), hd],
      rfl, rfl, rfl⟩
  obtain ⟨out, cost, hreset, hc, hp', htable'⟩ :=
    resetShiftBranches_runs (L := L) (ω := ω) (st := s2) chain i
      (by simp [s2, s1, s0, Function.update_of_ne])
      (by simp [s2, s1, Function.update_of_ne]) (by simp [s2])
      (fun j => by
        change mid.mem (base + j.val) = _
        rw [hm]
        by_cases hj : j.val = i.val <;> simp [hj, htable j])
      hbound (by omega)
  refine ⟨out, 14 + (2 + (2 + (2 + cost + 1) + 1) + 1) + 1, ?_,
    by omega, hp'.trans hp, htable'⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 14, _, hr,
    runs_seq_iff.mpr (Or.inr ⟨s0, 2, _, h0,
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, h1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 2, cost, h2, hreset, rfl⟩), rfl⟩), rfl⟩), rfl⟩)

end MinCostFlow.MinRatio
