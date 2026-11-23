module

public import MinCostFlow.Chain.Algorithm2
public import WordRAM.Logic
import MinCostFlow.MinRatio.PassReset
public import MinCostFlow.MinRatio.RebuildGuard

/-!
# Failure checks before Shift

Algorithm 2 (page 29) checks the eligible level and its shift budget
before the next shift. The shift quota is the bound from Lemma 7.3,
rounded down so an integer comparison makes the same decision.
-/

public section

namespace MinCostFlow.MinRatio

open Chain WordRAM

/-- The integer quota from the second failure check of Algorithm 2 (page 29). -/
noncomputable def shiftQuotaWord (P : ChainParams) (psi : ℝ) (rebuilds : ℕ → ℕ) (i : ℕ) : ℕ :=
  ⌊gameShiftBound P psi rebuilds i⌋₊

/-- In Lemma 7.3's prefix bound, one rebuild adds a single term to each
quota at or below the rebuilt level. Earlier levels keep their quota. -/
theorem gameShiftBound_rebuild_increment (P : ChainParams) (psi : ℝ)
    (counts : ℕ → ℕ) (rebuilt level : ℕ) :
    gameShiftBound P psi (fun j => if j = rebuilt then counts rebuilt + 1 else counts j) level =
      gameShiftBound P psi counts level +
        if rebuilt ≤ level then (10 * psi * (P.k : ℝ)) ^ (level + 1 - rebuilt) else 0 := by
  let weight := fun j : ℕ => (10 * psi * (P.k : ℝ)) ^ (level + 1 - j)
  unfold gameShiftBound
  have hsum : (∑ j ∈ Finset.range (level + 1),
      (↑(if j = rebuilt then counts rebuilt + 1 else counts j) : ℝ) * weight j) =
      ∑ j ∈ Finset.range (level + 1),
        ((counts j : ℝ) * weight j + if j = rebuilt then weight j else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = rebuilt
    · subst j
      simp [Nat.cast_add, add_mul]
    · simp [hj]
  change _ + (∑ j ∈ Finset.range (level + 1),
    (↑(if j = rebuilt then counts rebuilt + 1 else counts j) : ℝ) * weight j) = _
  rw [hsum, Finset.sum_add_distrib, ← add_assoc]
  simp [weight]

private theorem gameShiftBound_nonneg (P : ChainParams) (psi : ℝ) (rebuilds : ℕ → ℕ)
    (i : ℕ) (hpsi : 0 ≤ psi) : 0 ≤ gameShiftBound P psi rebuilds i := by
  unfold gameShiftBound
  apply add_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by positivity) hpsi) (Nat.cast_nonneg _)) _)
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (mul_nonneg (mul_nonneg (by positivity) hpsi) (Nat.cast_nonneg _)) _)

/-- When the base of Lemma 7.3's powers is integral, the rebuild updates the
stored floor by exactly one integer power at each affected level. -/
theorem shiftQuotaWord_rebuild_increment_of_nat_base (P : ChainParams) (psi : ℝ)
    (counts : ℕ → ℕ) (rebuilt level base : ℕ) (hpsi : 0 ≤ psi)
    (hbase : 10 * psi * (P.k : ℝ) = base) :
    shiftQuotaWord P psi (fun j => if j = rebuilt then counts rebuilt + 1 else counts j) level =
      shiftQuotaWord P psi counts level +
        if rebuilt ≤ level then base ^ (level + 1 - rebuilt) else 0 := by
  unfold shiftQuotaWord
  rw [gameShiftBound_rebuild_increment, hbase]
  by_cases h : rebuilt ≤ level
  · simp only [h, ite_true, ← Nat.cast_pow]
    exact Nat.floor_add_natCast (gameShiftBound_nonneg P psi counts level hpsi) _
  · simp [h]

private theorem floor_add_with_carry (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌊a + b⌋₊ = ⌊a⌋₊ + ⌊b⌋₊ +
      if 1 ≤ (a - (⌊a⌋₊ : ℝ)) + (b - (⌊b⌋₊ : ℝ)) then 1 else 0 := by
  let remainder := (a - (⌊a⌋₊ : ℝ)) + (b - (⌊b⌋₊ : ℝ))
  have hra := Nat.floor_le ha
  have hrb := Nat.floor_le hb
  have hsa := Nat.lt_floor_add_one a
  have hsb := Nat.lt_floor_add_one b
  have hnonneg : 0 ≤ remainder := by dsimp [remainder]; linarith
  have hlt : remainder < 2 := by dsimp [remainder]; linarith
  have heq : a + b = remainder + ((⌊a⌋₊ + ⌊b⌋₊ : ℕ) : ℝ) := by
    simp only [remainder, Nat.cast_add]
    ring
  change ⌊a + b⌋₊ = _ + _ + if 1 ≤ remainder then 1 else 0
  rw [heq, Nat.floor_add_natCast hnonneg, Nat.add_comm ⌊remainder⌋₊]
  congr 1
  rw [Nat.floor_eq_iff hnonneg]
  split <;> push_cast <;> constructor <;> linarith

/-- A rebuild changes a stored quota by the floor of its new power plus
a carry when the old quota and new power have fractional parts summing
to at least one. The fractional parts refer to the real bound of Lemma 7.3. -/
theorem shiftQuotaWord_rebuild_increment (P : ChainParams) (psi : ℝ)
    (counts : ℕ → ℕ) (rebuilt level : ℕ) (hpsi : 0 ≤ psi) :
    let old := gameShiftBound P psi counts level
    let added := if rebuilt ≤ level then (10 * psi * (P.k : ℝ)) ^ (level + 1 - rebuilt) else 0
    shiftQuotaWord P psi (fun j => if j = rebuilt then counts rebuilt + 1 else counts j) level =
      shiftQuotaWord P psi counts level + ⌊added⌋₊ +
        if 1 ≤ (old - (shiftQuotaWord P psi counts level : ℝ)) +
            (added - (⌊added⌋₊ : ℝ)) then 1 else 0 := by
  dsimp only
  unfold shiftQuotaWord
  rw [gameShiftBound_rebuild_increment]
  apply floor_add_with_carry _ _ (gameShiftBound_nonneg P psi counts level hpsi)
  split
  · positivity
  · exact le_rfl

/-- Algorithm 1 Update preserves the real quotas unless its periodic
rebuild fires. The rebuild adds one power at every affected level. -/
theorem gameShiftBound_algorithm1_update {T : SparseCoreRestartTool}
    {L : LastLevelTool} {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ}
    (st : ChainState T P) (U : List Update) (g ℓ : ℕ → ℝ) (psi : ℝ) (level : ℕ) :
    let updated := (algorithm1_update T L TP P N₀ st U g ℓ).1
    gameShiftBound P psi updated.rebuildCount level =
      gameShiftBound P psi st.rebuildCount level +
        (firstRebuiltLevel P.d st.rebuildCount updated.rebuildCount).elim 0
          (fun rebuilt => if rebuilt ≤ level then
            (10 * psi * (P.k : ℝ)) ^ (level + 1 - rebuilt) else 0) := by
  dsimp only
  rcases firstRebuiltLevel_algorithm1_update_cases (L := L) (TP := TP) (N₀ := N₀)
      st U g ℓ with ⟨hsame, hnone⟩ | ⟨i, hincr, hsome⟩
  · rw [hnone, hsame]
    simp
  · rw [hsome, hincr]
    exact gameShiftBound_rebuild_increment P psi st.rebuildCount i.val level

/-- A branch shift, including the terminal shift, preserves the rebuild
counters and hence the stored quotas of Algorithm 2 (page 29). -/
theorem shiftQuotaWord_algorithm1_shift {T : SparseCoreRestartTool}
    {L : LastLevelTool} {P : ChainParams} (st : ChainState T P) (psi : ℝ)
    (shifted level : ℕ) :
    shiftQuotaWord P psi (algorithm1_shift T L P st shifted).1.rebuildCount level =
      shiftQuotaWord P psi st.rebuildCount level := by
  unfold algorithm1_shift
  split <;> rfl

/-- Comparing with the stored quota avoids incrementing a word-sized counter. -/
theorem shiftQuotaWord_lt_iff (P : ChainParams) (psi : ℝ) (rebuilds : ℕ → ℕ)
    (i count : ℕ) (hpsi : 0 ≤ psi) :
    count < shiftQuotaWord P psi rebuilds i ↔
      (count : ℝ) + 1 ≤ gameShiftBound P psi rebuilds i := by
  change count + 1 ≤ ⌊gameShiftBound P psi rebuilds i⌋₊ ↔ _
  rw [Nat.le_floor_iff (gameShiftBound_nonneg P psi rebuilds i hpsi), Nat.cast_add, Nat.cast_one]

/-- Registers 0 and 1 hold the shift counter and the quota for the
eligible level. Register 2 receives the success bit. -/
@[expose] def shiftQuotaGuard : Stmt :=
  .assign 2 (.bin .lt (.reg 0) (.reg 1))

theorem shiftQuotaGuard_noRand : shiftQuotaGuard.NoRand := by
  simp [shiftQuotaGuard, Stmt.NoRand]

/-- The second failure check of Algorithm 2 (page 29) costs four steps. -/
theorem shiftQuotaGuard_runs {w i count : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (P : ChainParams) (psi : ℝ) (rebuilds : ℕ → ℕ) (hpsi : 0 ≤ psi)
    (hcount : st.regs 0 = count) (hquota : st.regs 1 = shiftQuotaWord P psi rebuilds i)
    (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω shiftQuotaGuard st .normal out 4 ∧
      out.regs 2 = (if (count : ℝ) + 1 ≤ gameShiftBound P psi rebuilds i then 1 else 0) ∧
      (∀ r ≠ 2, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  classical
  let flag := if (count : ℝ) + 1 ≤ gameShiftBound P psi rebuilds i then 1 else 0
  let out := { st with regs := Function.update st.regs 2 flag }
  have hflag : flag < 2 ^ w := by dsimp [flag]; split <;> omega
  have hcmp := shiftQuotaWord_lt_iff P psi rebuilds i count hpsi
  have heval : (Expr.bin .lt (.reg 0) (.reg 1)).eval w st = some flag := by
    simp [Expr.eval, hcount, hquota, BinOp.eval, hcmp, flag, hflag]
  exact ⟨out, runs_assign_iff.mpr ⟨flag, heval, rfl, rfl, rfl⟩, by simp [out, flag],
    fun r hr => by simp [out, Function.update_of_ne hr], rfl, rfl⟩

/-- The pass count is strictly below the integer ceiling of the limit. -/
@[expose] def eligibleTest : Expr :=
  .bin .lt (.load (.bin .add (.reg 0) (.reg 19))) (.reg 1)

/-- Inspect one pass count. Save its one-based index if eligible. -/
@[expose] def eligibleLevelStep : Stmt :=
  .cond eligibleTest (.assign 2 (.bin .add (.reg 19) (.const 1))) .nop

/-- Scan the pass table in increasing level order. Register 2 holds zero
for failure or the one-based index of the last eligible level. -/
@[expose] def eligibleLevelScan : Stmt :=
  .assign 2 (.const 0) ;; forRange 19 (.const 0) (.reg 21) eligibleLevelStep

theorem eligibleLevelScan_noRand : eligibleLevelScan.NoRand := by
  simp [eligibleLevelScan, eligibleLevelStep, forRange, forUp, Stmt.NoRand]

private def EligiblePrefix (passes : ℕ → ℕ) (quota n best : ℕ) : Prop :=
  best ≤ n ∧ (best = 0 ∨ ∃ j, best = j + 1 ∧ passes j < quota) ∧
    ∀ j < n, passes j < quota → j + 1 ≤ best

private theorem eligiblePrefix_next {passes : ℕ → ℕ} {quota i best : ℕ}
    (h : EligiblePrefix passes quota i best) :
    EligiblePrefix passes quota (i + 1) (if passes i < quota then i + 1 else best) := by
  by_cases hi : passes i < quota
  · rw [ite_eq_left hi]
    exact ⟨le_rfl, Or.inr ⟨i, rfl, hi⟩, fun j hj _ => by omega⟩
  · rw [ite_eq_right hi]
    exact ⟨h.1.trans (Nat.le_succ _), h.2.1, fun j hj he =>
      h.2.2 j (by have hne : j ≠ i := fun eq => hi (eq ▸ he); omega) he⟩

private theorem eligibleLevelStep_runs
    {w base quota i pass best : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hb : st.regs 0 = base) (hq : st.regs 1 = quota) (hi : st.regs 19 = i)
    (hp : st.mem (base + i) = pass) (hv : st.regs 2 = best)
    (haddr : base + i < 2 ^ w) (hi1 : i + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω eligibleLevelStep st .normal out cost ∧ cost ≤ 11 ∧
      out.regs 2 = (if pass < quota then i + 1 else best) ∧
      (∀ r ≠ 2, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  have he : eligibleTest.eval w st = some (if pass < quota then 1 else 0) := by
    have hm : (if pass < quota then 1 else 0) < 2 ^ w := by split <;> omega
    simp [eligibleTest, Expr.eval, hb, hq, hi, hp, BinOp.eval, haddr, hm]
  by_cases h : pass < quota
  · let out := { st with regs := Function.update st.regs 2 (i + 1) }
    have hassign : Runs w p ω (.assign 2 (.bin .add (.reg 19) (.const 1))) st .normal out 4 :=
      runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, BinOp.eval, hi, hw, hi1], rfl, rfl, rfl⟩
    refine ⟨out, 11, runs_cond_iff.mpr ⟨1, 4, by simpa [h] using he,
      by simpa using hassign, rfl⟩, le_rfl, by simp [out, h],
      fun r hr => by simp [out, Function.update_of_ne hr], rfl, rfl⟩
  · refine ⟨st, 8, runs_cond_iff.mpr ⟨0, 1, by simpa [h] using he,
      by simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
      by decide, by simpa [h] using hv, fun _ _ => rfl, rfl, rfl⟩

private theorem eligiblePrefix_model {d best : ℕ} {psi : ℝ}
    {passes : ℕ → ℕ} {model : Fin (d + 1) → ℕ}
    (hag : ∀ j : Fin (d + 1), passes j.val = model j)
    (h : EligiblePrefix passes ⌈2 * psi⌉₊ (d + 1) best) :
    best = (findEligibleLevel d psi model).elim 0 (fun i => i.val + 1) := by
  cases he : findEligibleLevel d psi model with
  | none =>
    rcases h.2.1 with hz | ⟨j, hj, helig⟩
    · exact hz
    have hjlt : j < d + 1 := by have := h.1; omega
    let j' : Fin (d + 1) := ⟨j, hjlt⟩
    have hlt : (model j' : ℝ) < 2 * psi := by rw [← hag j']; exact Nat.lt_ceil.mp helig
    exact (not_lt_of_ge ((findEligibleLevel_none_iff.mp he) j') hlt).elim
  | some i =>
    obtain ⟨helig, hmax⟩ := findEligibleLevel_spec he
    have hi : i.val + 1 ≤ best := h.2.2 i.val i.isLt (by rw [hag i]; exact Nat.lt_ceil.mpr helig)
    rcases h.2.1 with hz | ⟨j, hj, hpass⟩
    · omega
    have hjlt : j < d + 1 := by have := h.1; omega
    let j' : Fin (d + 1) := ⟨j, hjlt⟩
    have hlt : (model j' : ℝ) < 2 * psi := by rw [← hag j']; exact Nat.lt_ceil.mp hpass
    have hle : j ≤ i.val := hmax j' hlt
    have hn : best = i.val + 1 := by omega
    exact hn

/-- Algorithm 2 (page 29) selects the greatest eligible level in a linear
scan of the level counters. Zero is the failure answer. -/
theorem eligibleLevelScan_runs {w d base : ℕ} {psi : ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (model : Fin (d + 1) → ℕ)
    (hb : st.regs 0 = base) (hq : st.regs 1 = ⌈2 * psi⌉₊) (hn : st.regs 21 = d + 1)
    (hpasses : ∀ j : Fin (d + 1), st.mem (base + j.val) = model j)
    (haddr : base + d < 2 ^ w) (hnword : d + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω eligibleLevelScan st .normal out cost ∧ cost ≤ 20 * (d + 1) + 10 ∧
      out.regs 2 = (findEligibleLevel d psi model).elim 0 (fun i => i.val + 1) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r, r ≠ 2 → r ≠ 19 → out.regs r = st.regs r) := by
  let passes := fun j => st.mem (base + j)
  let start := { st with regs := Function.update st.regs 2 0 }
  let Inv := fun i (s : State) =>
    s.regs 0 = base ∧ s.regs 1 = ⌈2 * psi⌉₊ ∧ s.regs 19 = i ∧ s.regs 21 = d + 1 ∧
    s.mem = st.mem ∧ s.pos = st.pos ∧ EligiblePrefix passes ⌈2 * psi⌉₊ i (s.regs 2) ∧
    (∀ r, r ≠ 2 → r ≠ 19 → s.regs r = st.regs r)
  have hstep : ∀ i, 0 ≤ i → i < d + 1 →
      Triple w p (Inv i) eligibleLevelStep
        (normalPost fun out => Inv (i + 1) { out with regs := Function.update out.regs 19 (i + 1) } ∧
          out.regs 19 = i) (fun _ => 11) := by
    intro i _ hi s bits hs
    obtain ⟨hb', hq', hi', hn', hm, hpos, hbest, hframe⟩ := hs
    obtain ⟨out, cost, hr, hc, hresult, hregs, hmem, hpos'⟩ :=
      eligibleLevelStep_runs (ω := bits) hb' hq' hi' (by rw [hm]) rfl (by omega) (by omega) hw
    refine ⟨.normal, out, cost, hr, ⟨?_, (hregs 19 (by decide)).trans hi'⟩, hc⟩
    have hchange := eligiblePrefix_next hbest
    simp only [Inv, Function.update_self, Function.update_of_ne (by decide : 0 ≠ 19),
      Function.update_of_ne (by decide : 1 ≠ 19), Function.update_of_ne (by decide : 21 ≠ 19),
      Function.update_of_ne (by decide : 2 ≠ 19), true_and]
    rw [hresult]
    exact ⟨(hregs 0 (by decide)).trans hb', (hregs 1 (by decide)).trans hq',
      (hregs 21 (by decide)).trans hn', hmem.trans hm, hpos'.trans hpos, hchange,
      fun r hr1 hr2 => by
        rw [Function.update_of_ne hr2, hregs r hr1]
        exact hframe r hr1 hr2⟩
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = start)
    (r := 19) (lo := .const 0) (hi := .reg 21) (Inv := Inv)
    11 0 (d + 1) (Nat.zero_le _) hw (fun _ => hnword) (by
      intro s hs
      subst s
      refine ⟨by simp [Expr.eval], ?_⟩
      simp [Inv, start, Function.update_of_ne, hb, hq, hn, EligiblePrefix]
      intro r hr1 hr2
      simp [Function.update_of_ne hr1, Function.update_of_ne hr2])
    (fun _ s _ _ hs => hs.2.2.1)
    (fun _ s _ _ hs => by simp [Expr.eval, hs.2.2.2.1])
    hstep
  obtain ⟨o, out, cost, hrun, hout, hcost⟩ := hloop.runs ω rfl
  cases o with
  | returned value => exact False.elim hout
  | normal =>
    have hfirst : Runs w p ω (.assign 2 (.const 0)) st .normal start 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
    refine ⟨out, 2 + cost + 1,
      runs_seq_iff.mpr (Or.inr ⟨start, 2, cost, hfirst, hrun, rfl⟩), ?_,
      eligiblePrefix_model hpasses hout.2.2.2.2.2.2.1, hout.2.2.2.2.1, hout.2.2.2.2.2.1,
      hout.2.2.2.2.2.2.2⟩
    simp only [Expr.size, Nat.sub_zero] at hcost
    omega

/-- Decode the selected level, read its shift count and quota, and check it. -/
@[expose] def checkSelectedShift : Stmt :=
  .assign 5 (.bin .sub (.reg 2) (.const 1)) ;;
  .assign 0 (.load (.bin .add (.reg 3) (.reg 5))) ;;
  .assign 1 (.load (.bin .add (.reg 4) (.reg 5))) ;;
  shiftQuotaGuard

/-- Run both Algorithm 2 failure checks. The success bit is register 2,
and on success register 5 is the level passed to Shift. -/
@[expose] def shiftFailureChecks : Stmt :=
  eligibleLevelScan ;; .cond (.reg 2) checkSelectedShift .nop

theorem shiftFailureChecks_noRand : shiftFailureChecks.NoRand := by
  simp [shiftFailureChecks, checkSelectedShift, eligibleLevelScan_noRand, shiftQuotaGuard_noRand, Stmt.NoRand]

private theorem checkSelectedShift_runs {w i countBase quotaBase : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (P : ChainParams) (psi : ℝ) (rebuilds shifts : ℕ → ℕ)
    (hpsi : 0 ≤ psi) (hw : 1 < 2 ^ w) (hi : i + 1 < 2 ^ w)
    (hcode : st.regs 2 = i + 1) (hcountBase : st.regs 3 = countBase) (hquotaBase : st.regs 4 = quotaBase)
    (hcaddr : countBase + i < 2 ^ w) (hqaddr : quotaBase + i < 2 ^ w)
    (hshift : st.mem (countBase + i) = shifts i)
    (hquota : st.mem (quotaBase + i) = shiftQuotaWord P psi rebuilds i) :
    ∃ out, Runs w p ω checkSelectedShift st .normal out 21 ∧
      out.regs 2 = (if (shifts i : ℝ) + 1 ≤ gameShiftBound P psi rebuilds i then 1 else 0) ∧
      out.regs 5 = i ∧ out.mem = st.mem ∧ out.pos = st.pos ∧ out.regs 3 = countBase := by
  let select := { st with regs := Function.update st.regs 5 i }
  let readCount := { select with regs := Function.update select.regs 0 (shifts i) }
  let readQuota := { readCount with regs := Function.update readCount.regs 1 (shiftQuotaWord P psi rebuilds i) }
  have hs : Runs w p ω (.assign 5 (.bin .sub (.reg 2) (.const 1))) st .normal select 4 := by
    refine runs_assign_iff.mpr ⟨i, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, hcode, hw, show i < 2 ^ w by omega]
  have hc : Runs w p ω (.assign 0 (.load (.bin .add (.reg 3) (.reg 5)))) select .normal readCount 5 := by
    refine runs_assign_iff.mpr ⟨shifts i, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, select, Function.update_of_ne, hcountBase, hcaddr, hshift]
  have hq : Runs w p ω (.assign 1 (.load (.bin .add (.reg 4) (.reg 5)))) readCount .normal readQuota 5 := by
    refine runs_assign_iff.mpr ⟨shiftQuotaWord P psi rebuilds i, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, select, readCount, Function.update_of_ne, hquotaBase, hqaddr, hquota]
  obtain ⟨out, hr, hbit, hframe, hmem, hpos⟩ := shiftQuotaGuard_runs (ω := ω) (st := readQuota) (i := i) (count := shifts i)
    P psi rebuilds hpsi (by simp [readQuota, readCount, Function.update_of_ne]) (by simp [readQuota]) hw
  refine ⟨out, ?_, hbit, ?_, hmem, hpos, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨select, 4, 16, hs,
      runs_seq_iff.mpr (Or.inr ⟨readCount, 5, 10, hc,
        runs_seq_iff.mpr (Or.inr ⟨readQuota, 5, 4, hq, hr, rfl⟩), rfl⟩), rfl⟩)
  · rw [hframe 5 (by decide)]
    simp [readQuota, readCount, select, Function.update_of_ne]
  · rw [hframe 3 (by decide)]
    simp [readQuota, readCount, select, Function.update_of_ne, hcountBase]

/-- The two failure checks of Algorithm 2 (page 29) return the exact
success bit, with an explicit linear cost in the number of levels. -/
theorem shiftFailureChecks_runs {w base countBase quotaBase : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (P : ChainParams) (psi : ℝ) (passes : Fin (P.d + 1) → ℕ)
    (rebuilds shifts : ℕ → ℕ)
    (hpsi : 0 ≤ psi) (hw : 1 < 2 ^ w)
    (hb : st.regs 0 = base) (hq : st.regs 1 = ⌈2 * psi⌉₊) (hn : st.regs 21 = P.d + 1)
    (hcbase : st.regs 3 = countBase) (hqbase : st.regs 4 = quotaBase)
    (hp : ∀ i : Fin (P.d + 1), st.mem (base + i.val) = passes i)
    (hcounts : ∀ i ≤ P.d, st.mem (countBase + i) = shifts i)
    (hquotas : ∀ i ≤ P.d, st.mem (quotaBase + i) = shiftQuotaWord P psi rebuilds i)
    (haddr : base + P.d < 2 ^ w) (hcaddr : countBase + P.d < 2 ^ w)
    (hqaddr : quotaBase + P.d < 2 ^ w) (hnword : P.d + 1 < 2 ^ w) :
    let chosen := findEligibleLevel P.d psi passes
    ∃ out cost, Runs w p ω shiftFailureChecks st .normal out cost ∧ cost ≤ 20 * (P.d + 1) + 34 ∧
      out.regs 2 = chosen.elim 0 (fun i =>
        if (shifts i.val : ℝ) + 1 ≤ gameShiftBound P psi rebuilds i.val then 1 else 0) ∧
      (∀ i, chosen = some i → out.regs 5 = i.val) ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      out.regs 3 = countBase := by
  dsimp only
  obtain ⟨mid, cost, hscan, hs, code, hm, hpos, hframe⟩ :=
    eligibleLevelScan_runs (ω := ω) passes hb hq hn hp haddr hnword hw
  cases he : findEligibleLevel P.d psi passes with
  | none =>
    rw [he] at code
    have hbranch : Runs w p ω (.cond (.reg 2) checkSelectedShift .nop) mid .normal mid 3 :=
      runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, code],
        by simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨mid, cost + 3 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 3, hscan, hbranch, rfl⟩),
      by omega, code, (fun _ h => by cases h), hm, hpos,
      (hframe 3 (by decide) (by decide)).trans hcbase⟩
  | some i =>
    rw [he] at code
    have hi : i.val + 1 < 2 ^ w := (Nat.succ_le_of_lt i.isLt).trans_lt hnword
    have hi' : i.val ≤ P.d := Nat.le_of_lt_succ i.isLt
    obtain ⟨out, hr, hbit, hout, hmem, hpos', hbase⟩ :=
      checkSelectedShift_runs (ω := ω) P psi rebuilds shifts hpsi hw hi code
        ((hframe 3 (by decide) (by decide)).trans hcbase)
        ((hframe 4 (by decide) (by decide)).trans hqbase)
        (by omega) (by omega) (hm ▸ hcounts i.val hi') (hm ▸ hquotas i.val hi')
    have hbranch : Runs w p ω (.cond (.reg 2) checkSelectedShift .nop) mid .normal out 23 :=
      runs_cond_iff.mpr ⟨i.val + 1, 21, by simp [Expr.eval, code], by simpa using hr, rfl⟩
    exact ⟨out, cost + 23 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 23, hscan, hbranch, rfl⟩),
      by omega, hbit, (fun _ h => Option.some.inj h ▸ hout), hmem.trans hm, hpos'.trans hpos, hbase⟩

/-- The pass counts, shift counts, and quota words read by the two
failure checks represent the corresponding fields of Algorithm 2. -/
@[expose] def shiftCheckTablesAt {cfg : Alg2Config} (mem : ℕ → ℕ)
    (passBase countBase quotaBase : ℕ) (s : Alg2State cfg) : Prop :=
  (∀ i : Fin (cfg.P.d + 1), mem (passBase + i.val) = s.passes i) ∧
  (∀ i ≤ cfg.P.d, mem (countBase + i) = s.chain.shiftCount i) ∧
  (∀ i ≤ cfg.P.d, mem (quotaBase + i) =
    shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) s.chain.rebuildCount i)

/-- Run the failure checks on the represented Algorithm 2 counters. -/
theorem shiftFailureChecks_state_runs {w passBase countBase quotaBase : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} {cfg : Alg2Config} (s : Alg2State cfg)
    (hTables : shiftCheckTablesAt st.mem passBase countBase quotaBase s)
    (hb : st.regs 0 = passBase) (hq : st.regs 1 = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊)
    (hn : st.regs 21 = cfg.P.d + 1)
    (hcbase : st.regs 3 = countBase) (hqbase : st.regs 4 = quotaBase)
    (haddr : passBase + cfg.P.d < 2 ^ w) (hcaddr : countBase + cfg.P.d < 2 ^ w)
    (hqaddr : quotaBase + cfg.P.d < 2 ^ w) (hnword : cfg.P.d + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
    let chosen := findEligibleLevel cfg.P.d psi s.passes
    ∃ out cost, Runs w p ω shiftFailureChecks st .normal out cost ∧
      cost ≤ 20 * (cfg.P.d + 1) + 34 ∧
      out.regs 2 = chosen.elim 0 (fun i =>
        if (s.chain.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P psi s.chain.rebuildCount i.val then 1 else 0) ∧
      (∀ i, chosen = some i → out.regs 5 = i.val) ∧
      shiftCheckTablesAt out.mem passBase countBase quotaBase s ∧ out.pos = st.pos := by
  dsimp only
  obtain ⟨out, cost, hr, hcost, hbit, hlevel, hmem, hpos, _⟩ :=
    shiftFailureChecks_runs (ω := ω) cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) s.passes
      s.chain.rebuildCount s.chain.shiftCount ((by norm_num : (0 : ℝ) ≤ 1).trans (alg2PsiGame_ge_one _ _))
      hw hb hq hn hcbase hqbase hTables.1 hTables.2.1 hTables.2.2 haddr hcaddr hqaddr hnword
  exact ⟨out, cost, hr, hcost, hbit, hlevel, hmem.symm ▸ hTables, hpos⟩

/-- Algorithm 2 (page 29) records an accepted shift at the selected level.
Register 0 holds the shift-counter table base and register 1 the level index. -/
@[expose] def recordAcceptedShift : Stmt :=
  incrementLevelCounter

theorem recordAcceptedShift_noRand : recordAcceptedShift.NoRand :=
  incrementLevelCounter_noRand

/-- The quota guard ensures the increment fits in a word. The store preserves
the remaining memory and costs ten steps. -/
theorem recordAcceptedShift_runs {w base level count quota : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = level)
    (hc : st.mem (base + level) = count) (ha : base + level < 2 ^ w)
    (haccepted : count < quota) (hquota : quota < 2 ^ w) :
    ∃ out, Runs w p ω recordAcceptedShift st .normal out 10 ∧
      out.mem = Function.update st.mem (base + level) (count + 1) ∧
      out.regs = st.regs ∧ out.pos = st.pos :=
  incrementLevelCounter_runs hb hi hc ha (by omega)

private theorem algorithm1_shift_count_at {cfg : Alg2Config} (model : Alg2State cfg)
    (i j : Fin (cfg.P.d + 1)) :
    (algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.shiftCount j.val =
      if j.val = i.val then model.chain.shiftCount i.val + 1 else model.chain.shiftCount j.val := by
  unfold algorithm1_shift
  split
  · rfl
  · have heq : i.val = cfg.P.d := by have := i.isLt; omega
    simp [heq]

/-- For any level accepted by Algorithm 2's quota test, the updated table
agrees with Algorithm 1 Shift, including at the terminal level. -/
theorem recordAcceptedShift_state_runs {cfg : Alg2Config} (model : Alg2State cfg)
    (i : Fin (cfg.P.d + 1)) {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val)
    (htable : ∀ j : Fin (cfg.P.d + 1), st.mem (base + j.val) = model.chain.shiftCount j.val)
    (ha : base + i.val < 2 ^ w)
    (hpsi : 0 ≤ alg2PsiGame cfg.Ψ cfg.P.M₀)
    (haccepted : (model.chain.shiftCount i.val : ℝ) + 1 ≤
      gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val)
    (hquota : shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
      model.chain.rebuildCount i.val < 2 ^ w) :
    let next := (algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    ∃ out, Runs w p ω recordAcceptedShift st .normal out 10 ∧
      out.regs = st.regs ∧ out.pos = st.pos ∧
      ∀ j : Fin (cfg.P.d + 1), out.mem (base + j.val) = next.shiftCount j.val := by
  dsimp only
  have hlt := (shiftQuotaWord_lt_iff cfg.P _ model.chain.rebuildCount i.val _ hpsi).mpr haccepted
  obtain ⟨out, hr, hm, hregs, hp⟩ :=
    recordAcceptedShift_runs (ω := ω) hb hi (htable i) ha hlt hquota
  refine ⟨out, hr, hregs, hp, fun j => ?_⟩
  rw [hm, algorithm1_shift_count_at]
  by_cases heq : j.val = i.val
  · simp [heq]
  · simp [heq, htable j]

/-- Consume the Algorithm 2 failure checks' success bit and selected level.
A failed check leaves the shift counters intact. -/
@[expose] def recordCheckedShift : Stmt :=
  .cond (.reg 2) (.assign 0 (.reg 3) ;; .assign 1 (.reg 5) ;; recordAcceptedShift) .nop

theorem recordCheckedShift_noRand : recordCheckedShift.NoRand := by
  simp [recordCheckedShift, recordAcceptedShift_noRand, Stmt.NoRand]

/-- The counter continuation takes at most eighteen steps and preserves the
guard's success flag and selected level for the call to Shift. -/
theorem recordCheckedShift_runs {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (accepted : Option ℕ) (counts quotas : ℕ → ℕ) (hb : st.regs 3 = base)
    (hbit : st.regs 2 = if accepted.isSome then 1 else 0)
    (hlevel : ∀ i ∈ accepted, st.regs 5 = i)
    (hcount : ∀ i ∈ accepted, st.mem (base + i) = counts i)
    (haddr : ∀ i ∈ accepted, base + i < 2 ^ w)
    (hquota : ∀ i ∈ accepted, counts i < quotas i ∧ quotas i < 2 ^ w) :
    ∃ out cost, Runs w p ω recordCheckedShift st .normal out cost ∧ cost ≤ 18 ∧
      out.regs 2 = st.regs 2 ∧ out.regs 5 = st.regs 5 ∧ out.pos = st.pos ∧
      out.mem = accepted.elim st.mem (fun i => Function.update st.mem (base + i) (counts i + 1)) := by
  cases accepted with
  | none =>
    refine ⟨st, 3, ?_, by decide, rfl, rfl, rfl, rfl⟩
    exact runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hbit],
      by simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
  | some i =>
    have hi : i ∈ some i := by simp
    let s0 := { st with regs := Function.update st.regs 0 base }
    let s1 := { s0 with regs := Function.update s0.regs 1 i }
    have h0 : Runs w p ω (.assign 0 (.reg 3)) st .normal s0 2 :=
      runs_assign_iff.mpr ⟨base, by simp [Expr.eval, hb], rfl, rfl, rfl⟩
    have h1 : Runs w p ω (.assign 1 (.reg 5)) s0 .normal s1 2 :=
      runs_assign_iff.mpr ⟨i, by simp [Expr.eval, s0, Function.update_of_ne, hlevel i hi],
        rfl, rfl, rfl⟩
    obtain ⟨out, hr, hm, hregs, hp⟩ := recordAcceptedShift_runs (ω := ω) (st := s1)
      (by simp [s1, s0, Function.update_of_ne]) (by simp [s1]) (hcount i hi)
      (haddr i hi) (hquota i hi).1 (hquota i hi).2
    refine ⟨out, 18, ?_, le_rfl, ?_, ?_, hp, hm⟩
    · exact runs_cond_iff.mpr ⟨1, 16, by simp [Expr.eval, hbit], by
        simp only [one_ne_zero, ite_false]
        exact runs_seq_iff.mpr (Or.inr ⟨s0, 2, 13, h0,
          runs_seq_iff.mpr (Or.inr ⟨s1, 2, 10, h1, hr, rfl⟩), rfl⟩), rfl⟩
    · simp [hregs, s1, s0, Function.update_of_ne]
    · simp [hregs, s1, s0, Function.update_of_ne]

/-- Run the two Algorithm 2 failure checks and record a shift only if both pass. -/
@[expose] def checkAndRecordShift : Stmt :=
  shiftFailureChecks ;; recordCheckedShift

theorem checkAndRecordShift_noRand : checkAndRecordShift.NoRand := by
  simp [checkAndRecordShift, shiftFailureChecks_noRand, recordCheckedShift_noRand, Stmt.NoRand]

/-- The combined guard and counter update returns the accepted level and charges
at most 20 steps per level plus 53 steps. -/
theorem checkAndRecordShift_runs {w passBase countBase quotaBase : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} {cfg : Alg2Config} (s : Alg2State cfg)
    (hTables : shiftCheckTablesAt st.mem passBase countBase quotaBase s)
    (hb : st.regs 0 = passBase) (hq : st.regs 1 = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊)
    (hn : st.regs 21 = cfg.P.d + 1)
    (hcbase : st.regs 3 = countBase) (hqbase : st.regs 4 = quotaBase)
    (haddr : passBase + cfg.P.d < 2 ^ w) (hcaddr : countBase + cfg.P.d < 2 ^ w)
    (hqaddr : quotaBase + cfg.P.d < 2 ^ w) (hnword : cfg.P.d + 1 < 2 ^ w) (hw : 1 < 2 ^ w)
    (hword : ∀ i ≤ cfg.P.d, st.mem (quotaBase + i) < 2 ^ w) :
    let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
    let accepted := (findEligibleLevel cfg.P.d psi s.passes).bind fun i =>
      if (s.chain.shiftCount i.val : ℝ) + 1 ≤
          gameShiftBound cfg.P psi s.chain.rebuildCount i.val then some i.val else none
    ∃ out cost, Runs w p ω checkAndRecordShift st .normal out cost ∧
      cost ≤ 20 * (cfg.P.d + 1) + 53 ∧ out.pos = st.pos ∧
      out.regs 2 = (if accepted.isSome then 1 else 0) ∧
      (∀ i ∈ accepted, out.regs 5 = i) ∧
      out.mem = accepted.elim st.mem
        (fun i => Function.update st.mem (countBase + i) (s.chain.shiftCount i + 1)) := by
  dsimp only
  let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  let chosen := findEligibleLevel cfg.P.d psi s.passes
  let allowed := fun i : Fin (cfg.P.d + 1) =>
    (s.chain.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P psi s.chain.rebuildCount i.val
  let accepted := chosen.bind fun i => if allowed i then some i.val else none
  have hpsi : 0 ≤ psi := (by norm_num : (0 : ℝ) ≤ 1).trans (alg2PsiGame_ge_one _ _)
  obtain ⟨mid, c, hr, hc, hbit, hlevel, hm, hp, hbase⟩ :=
    shiftFailureChecks_runs (ω := ω) cfg.P psi s.passes s.chain.rebuildCount s.chain.shiftCount
      hpsi hw hb hq hn hcbase hqbase hTables.1 hTables.2.1 hTables.2.2
      haddr hcaddr hqaddr hnword
  have hflag : mid.regs 2 = if accepted.isSome then 1 else 0 := by
    change mid.regs 2 = chosen.elim 0 (fun i => if allowed i then 1 else 0) at hbit
    rw [hbit]
    cases he : chosen with
    | none => simp [accepted, he]
    | some i =>
      by_cases h : allowed i <;> simp [accepted, he, h]
  have hselected : ∀ j ∈ accepted, ∃ i : Fin (cfg.P.d + 1),
      chosen = some i ∧ j = i.val ∧ allowed i := by
    intro j hj
    cases he : chosen with
    | none => simp [accepted, he] at hj
    | some i =>
      by_cases ha : allowed i
      · exact ⟨i, rfl, by simpa [accepted, he, ha, eq_comm] using hj, ha⟩
      · simp [accepted, he, ha] at hj
  have hselectedLevel : ∀ j ∈ accepted, mid.regs 5 = j := by
    intro j hj
    obtain ⟨i, he, rfl, _⟩ := hselected j hj
    exact hlevel i he
  have hle : ∀ j ∈ accepted, j ≤ cfg.P.d := by
    intro j hj
    obtain ⟨i, _, rfl, _⟩ := hselected j hj
    exact Nat.le_of_lt_succ i.isLt
  have hquota : ∀ j ∈ accepted, s.chain.shiftCount j < shiftQuotaWord cfg.P psi s.chain.rebuildCount j ∧
      shiftQuotaWord cfg.P psi s.chain.rebuildCount j < 2 ^ w := by
    intro j hj
    obtain ⟨i, _, rfl, ha⟩ := hselected j hj
    refine ⟨(shiftQuotaWord_lt_iff cfg.P psi s.chain.rebuildCount i.val _ hpsi).mpr ha, ?_⟩
    rw [← hTables.2.2 i.val (Nat.le_of_lt_succ i.isLt)]
    exact hword i.val (Nat.le_of_lt_succ i.isLt)
  obtain ⟨out, c', hr', hc', hbit', hlevel', hp', hm'⟩ :=
    recordCheckedShift_runs (ω := ω) accepted s.chain.shiftCount
      (shiftQuotaWord cfg.P psi s.chain.rebuildCount) hbase hflag hselectedLevel
      (fun j hj => by rw [hm]; exact hTables.2.1 j (hle j hj))
      (fun j hj => Nat.lt_of_le_of_lt (Nat.add_le_add_left (hle j hj) _) hcaddr) hquota
  refine ⟨out, c + c' + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, c', hr, hr', rfl⟩),
    by omega, hp'.trans hp, hbit'.trans hflag, fun j hj => hlevel'.trans (hselectedLevel j hj), ?_⟩
  simpa only [hm] using hm'

/-- After both checks, the shift-count table matches the counters of the
chosen Algorithm 1 shift. If either check fails, the counters stay as they were. -/
theorem checkAndRecordShift_state_runs {w passBase countBase quotaBase : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} {cfg : Alg2Config} (s : Alg2State cfg)
    (hTables : shiftCheckTablesAt st.mem passBase countBase quotaBase s)
    (hb : st.regs 0 = passBase) (hq : st.regs 1 = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊)
    (hn : st.regs 21 = cfg.P.d + 1)
    (hcbase : st.regs 3 = countBase) (hqbase : st.regs 4 = quotaBase)
    (haddr : passBase + cfg.P.d < 2 ^ w) (hcaddr : countBase + cfg.P.d < 2 ^ w)
    (hqaddr : quotaBase + cfg.P.d < 2 ^ w) (hnword : cfg.P.d + 1 < 2 ^ w) (hw : 1 < 2 ^ w)
    (hword : ∀ i ≤ cfg.P.d, st.mem (quotaBase + i) < 2 ^ w) :
    let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
    let accepted := (findEligibleLevel cfg.P.d psi s.passes).filter fun i =>
      decide ((s.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P psi s.chain.rebuildCount i.val)
    let next := accepted.elim s.chain (fun i => (algorithm1_shift cfg.T cfg.L cfg.P s.chain i.val).1)
    ∃ out cost, Runs w p ω checkAndRecordShift st .normal out cost ∧
      cost ≤ 20 * (cfg.P.d + 1) + 53 ∧ out.pos = st.pos ∧
      out.regs 2 = (if accepted.isSome then 1 else 0) ∧
      (∀ i ∈ accepted, out.regs 5 = i.val) ∧
      ∀ j : Fin (cfg.P.d + 1), out.mem (countBase + j.val) = next.shiftCount j.val := by
  dsimp only
  obtain ⟨out, cost, hr, hc, hpos, hbit, hlevel, hm⟩ :=
    checkAndRecordShift_runs (ω := ω) s hTables hb hq hn hcbase hqbase
      haddr hcaddr hqaddr hnword hw hword
  let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  cases he : findEligibleLevel cfg.P.d psi s.passes with
  | none =>
    simp [psi, he] at hbit hm ⊢
    exact ⟨out, cost, hr, hc, hpos, hbit, fun j => hm ▸ hTables.2.1 _ (Nat.le_of_lt_succ j.isLt)⟩
  | some i =>
    by_cases hi : (s.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P psi s.chain.rebuildCount i.val
    · simp [psi, he, hi, Option.filter] at hbit hlevel hm ⊢
      refine ⟨out, cost, hr, hc, hpos, hbit, hlevel, fun j => ?_⟩
      rw [hm, algorithm1_shift_count_at]
      by_cases hj : j.val = i.val
      · simp [hj]
      · simp [hj, hTables.2.1 _ (Nat.le_of_lt_succ j.isLt)]
    · simp [psi, he, hi, Option.filter] at hbit hm ⊢
      exact ⟨out, cost, hr, hc, hpos, hbit, fun j => hm ▸ hTables.2.1 _ (Nat.le_of_lt_succ j.isLt)⟩

end MinCostFlow.MinRatio
