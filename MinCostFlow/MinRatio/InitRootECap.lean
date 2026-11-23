module

public import Mathlib.Data.Nat.Log
public import MinCostFlow.ExpanderDecomp.OneShotProgAux
public import MinCostFlow.MinRatio.WireChainSpecs
import Mathlib.Tactic

/-!
# Inline root edge-capacity calculation for concrete Init (`InitRootECap`)

Computes `initRootECap N₀ k m = (N₀ / 4) + ((N₀ / 4) / (Nat.clog 2 (N₀ + 2) ^ 2)) / k + 2 * m`
in-place into register `61` from `reg 56 = N₀`, `reg 76 = k`, and `reg 94 = m`, using only
scratch registers `10, 11, 12`, zero memory writes, and `O(log (N₀ + 2))` deterministic steps.
The ceiling binary logarithm is computed by repeated ceiling-halving `x := (x + 1) / 2`, so every
intermediate value stays at most `N₀ + 3`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Target root-graph edge capacity computed by concrete Init from `(N₀, k, m)`.
When `N₀ = 4 * M₀`, `m ≤ M₀`, `0 < m`, and `G.E = Finset.range m`, this equals
`initTargetCap cfg G = M₀ + intRebuildThreshold cfg.P N₀ 0 + 2 * m`. -/
@[expose] def initRootECap (N₀ k m : ℕ) : ℕ :=
  N₀ / 4 + (N₀ / 4 / (Nat.clog 2 (N₀ + 2) * Nat.clog 2 (N₀ + 2))) / k + 2 * m

theorem initRootECap_ge_two_mul (N₀ k m : ℕ) : 2 * m ≤ initRootECap N₀ k m := by
  unfold initRootECap; exact Nat.le_add_left _ _

theorem initRootECap_ge_m (N₀ k m : ℕ) : m ≤ initRootECap N₀ k m :=
  le_trans (by omega : m ≤ 2 * m) (initRootECap_ge_two_mul N₀ k m)

theorem initRootECap_le_four_mul {M₀ k m : ℕ} (hm : m ≤ M₀) :
    initRootECap (4 * M₀) k m ≤ 4 * M₀ := by
  unfold initRootECap
  have h1 : 4 * M₀ / 4 = M₀ := by omega
  rw [h1]
  have h2 : M₀ / (Nat.clog 2 (4 * M₀ + 2) * Nat.clog 2 (4 * M₀ + 2)) / k ≤ M₀ :=
    (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  omega

/-- Inline deterministic statement computing `initRootECap (reg 56) (reg 76) (reg 94)` into
register `61`, modifying only registers `10, 11, 12, 61` and no memory cells. -/
@[expose] def initComputeRootECap : Stmt :=
  .assign 10 (.bin .add (.reg 56) (.const 2)) ;;
  .assign 12 (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg 10))
    (.assign 10 (.bin .div (.bin .add (.reg 10) (.const 1)) (.const 2)) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1))) ;;
  .assign 10 (.bin .div (.reg 56) (.const 4)) ;;
  .assign 11 (.bin .div (.bin .div (.reg 10) (.bin .mul (.reg 12) (.reg 12))) (.reg 76)) ;;
  .assign 61 (.bin .add (.bin .add (.reg 10) (.reg 11)) (.bin .mul (.const 2) (.reg 94)))

theorem initComputeRootECap_noRand : initComputeRootECap.NoRand := by
  simp [initComputeRootECap, Stmt.NoRand]

private theorem sq_lt_two_pow_of_ge5 {w : ℕ} (hw : 5 ≤ w) : w * w < 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    have hlin : 2 * n + 1 ≤ n * n := by nlinarith
    rw [hpow]
    nlinarith

private theorem clog_sq_lt_two_pow_of_ge5 {w n : ℕ} (hw : 5 ≤ w) (hn : n ≤ 2 ^ w) :
    Nat.clog 2 n * Nat.clog 2 n < 2 ^ w := by
  have hcl : Nat.clog 2 n ≤ w := (Nat.clog_le_iff_le_pow (by decide)).mpr hn
  exact lt_of_le_of_lt (Nat.mul_le_mul hcl hcl) (sq_lt_two_pow_of_ge5 hw)

private theorem clog_half_loop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (hw17 : 17 < 2 ^ w) :
    ∀ (x c : ℕ) (st : State),
      st.regs 10 = x → st.regs 12 = c →
      x + 1 < 2 ^ w → c + Nat.clog 2 x < 2 ^ w →
      ∃ out cost,
        Runs w p ω
          (.loop (.bin .lt (.const 1) (.reg 10))
            (.assign 10 (.bin .div (.bin .add (.reg 10) (.const 1)) (.const 2)) ;;
             .assign 12 (.bin .add (.reg 12) (.const 1))))
          st .normal out cost ∧
        out.regs 12 = c + Nat.clog 2 x ∧
        out.mem = st.mem ∧ out.pos = st.pos ∧
        (∀ r, r ≠ 10 → r ≠ 12 → out.regs r = st.regs r) ∧
        cost ≤ 22 * Nat.clog 2 x + 4 := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro c st h10 h12 hxW hcW
    by_cases hle : x ≤ 1
    · have hcl0 : Nat.clog 2 x = 0 := Nat.clog_of_right_le_one hle 2
      have hcond : (Expr.bin .lt (.const 1) (.reg 10)).eval w st = some 0 := by
        simp [Expr.eval, BinOp.eval, h10, show 1 < 2 ^ w by omega, show ¬ 1 < x by omega]
      exact ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size]⟩),
        by rw [hcl0, Nat.add_zero]; exact h12, rfl, rfl, fun _ _ _ => rfl, by omega⟩
    · have hgt1 : 1 < x := by omega
      have hhalfLt : (x + 1) / 2 < x := by omega
      have hclEq : Nat.clog 2 x = Nat.clog 2 ((x + 1) / 2) + 1 := by
        have h := Nat.clog_of_one_lt (by decide : 1 < 2) hgt1
        have heq : x + 2 - 1 = x + 1 := by omega
        simpa only [heq] using h
      have hcond : (Expr.bin .lt (.const 1) (.reg 10)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h10, show 1 < 2 ^ w by omega, hgt1]
      let s1 := { st with regs := Function.update st.regs 10 ((x + 1) / 2) }
      let s2 := { s1 with regs := Function.update s1.regs 12 (c + 1) }
      have hr1 : Runs w p ω (.assign 10 (.bin .div (.bin .add (.reg 10) (.const 1)) (.const 2)))
          st .normal s1 6 :=
        runs_assign_iff.mpr ⟨(x + 1) / 2, by
          simp [Expr.eval, BinOp.eval, h10, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            hxW, show (x + 1) / 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hr2 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1))) s1 .normal s2 4 :=
        runs_assign_iff.mpr ⟨c + 1, by
          simp [Expr.eval, BinOp.eval, s1, h12, show 1 < 2 ^ w by omega,
            show c + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      obtain ⟨out, cost', hrTail, hout12, hmem, hpos, hregs, hcost'⟩ :=
        ih ((x + 1) / 2) hhalfLt (c + 1) s2 (by simp [s2, s1]) (by simp [s2])
          (by omega) (by omega)
      refine ⟨out, 3 + (6 + 4 + 1) + cost' + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s2, 6 + 4 + 1, cost', hcond, by decide,
          runs_seq_iff.mpr (Or.inr ⟨s1, 6, 4, hr1, hr2, rfl⟩), hrTail, rfl⟩)),
        by rw [hout12, hclEq]; omega, hmem, hpos,
        fun r hr10 hr12 => (hregs r hr10 hr12).trans
          (by simp [s2, s1, Function.update_of_ne hr10, Function.update_of_ne hr12]),
        by omega⟩

/-- Executes `initComputeRootECap` with zero memory writes, storing `initRootECap N₀ k m` in
register `61` in at most `22 * Nat.clog 2 (N₀ + 2) + 45` deterministic steps. -/
theorem initComputeRootECap_runs {w N₀ k m : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h56 : st.regs 56 = N₀) (h76 : st.regs 76 = k) (h94 : st.regs 94 = m)
    (hk : 0 < k) (hw17 : 17 < 2 ^ w) (hN3w : N₀ + 3 < 2 ^ w)
    (heCapW : initRootECap N₀ k m < 2 ^ w) :
    ∃ out cost,
      Runs w p ω initComputeRootECap st .normal out cost ∧
      out.regs 61 = initRootECap N₀ k m ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 61 → out.regs r = st.regs r) ∧
      cost ≤ 22 * Nat.clog 2 (N₀ + 2) + 45 := by
  have hw5 : 5 ≤ w := by
    by_contra h
    have hw4 : w ≤ 4 := by omega
    have hpow : 2 ^ w ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hw4
    omega
  have hclSqW : Nat.clog 2 (N₀ + 2) * Nat.clog 2 (N₀ + 2) < 2 ^ w :=
    clog_sq_lt_two_pow_of_ge5 hw5 (by omega)
  have hclPos : 0 < Nat.clog 2 (N₀ + 2) := by
    have h : 1 < N₀ + 2 := by omega
    have := Nat.clog_of_one_lt (by decide : 1 < 2) h
    omega
  have hclSqPos : 0 < Nat.clog 2 (N₀ + 2) * Nat.clog 2 (N₀ + 2) := Nat.mul_pos hclPos hclPos
  have hclW : Nat.clog 2 (N₀ + 2) < 2 ^ w := by
    have : Nat.clog 2 (N₀ + 2) ≤ Nat.clog 2 (N₀ + 2) * Nat.clog 2 (N₀ + 2) :=
      Nat.le_mul_of_pos_right _ hclPos
    omega
  let s1 := { st with regs := Function.update st.regs 10 (N₀ + 2) }
  let s2 := { s1 with regs := Function.update s1.regs 12 0 }
  have hr1 : Runs w p ω (.assign 10 (.bin .add (.reg 56) (.const 2))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨N₀ + 2, by
      simp [Expr.eval, BinOp.eval, h56, show 2 < 2 ^ w by omega, show N₀ + 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 12 (.const 0)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s3, cLoop, hrLoop, hs3_12, hs3_mem, hs3_pos, hs3_regs, hcLoop⟩ :=
    clog_half_loop_runs (w := w) (p := p) (ω := ω) hw17 (N₀ + 2) 0 s2
      (by simp [s2, s1]) (by simp [s2]) (by omega) (by omega)
  rw [Nat.zero_add] at hs3_12
  have hs3_56 : s3.regs 56 = N₀ :=
    (hs3_regs 56 (by decide) (by decide)).trans (by simp [s2, s1, h56])
  have hs3_76 : s3.regs 76 = k :=
    (hs3_regs 76 (by decide) (by decide)).trans (by simp [s2, s1, h76])
  have hs3_94 : s3.regs 94 = m :=
    (hs3_regs 94 (by decide) (by decide)).trans (by simp [s2, s1, h94])
  let M₀ := N₀ / 4
  let thr₀ := (M₀ / (Nat.clog 2 (N₀ + 2) * Nat.clog 2 (N₀ + 2))) / k
  let eCap := initRootECap N₀ k m
  have heCapDef : eCap = M₀ + thr₀ + 2 * m := rfl
  let s4 := { s3 with regs := Function.update s3.regs 10 M₀ }
  let s5 := { s4 with regs := Function.update s4.regs 11 thr₀ }
  let s6 := { s5 with regs := Function.update s5.regs 61 eCap }
  have hr4 : Runs w p ω (.assign 10 (.bin .div (.reg 56) (.const 4))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨M₀, by
      simp [Expr.eval, BinOp.eval, hs3_56, M₀, show 4 < 2 ^ w by omega,
        show N₀ / 4 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hdiv1W : M₀ / (Nat.clog 2 (N₀ + 2) * Nat.clog 2 (N₀ + 2)) < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hthrW : thr₀ < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hdiv1W
  have hr5 : Runs w p ω
      (.assign 11 (.bin .div (.bin .div (.reg 10) (.bin .mul (.reg 12) (.reg 12))) (.reg 76)))
      s4 .normal s5 8 :=
    runs_assign_iff.mpr ⟨thr₀, by
      simp [Expr.eval, BinOp.eval, s4, hs3_12, hs3_76, thr₀, hclSqW, hdiv1W, hthrW],
      rfl, rfl, rfl⟩
  have hr6 : Runs w p ω
      (.assign 61 (.bin .add (.bin .add (.reg 10) (.reg 11)) (.bin .mul (.const 2) (.reg 94))))
      s5 .normal s6 8 :=
    runs_assign_iff.mpr ⟨eCap, by
      have h3 : M₀ + thr₀ + 2 * m < 2 ^ w := heCapDef ▸ heCapW
      have h1 : M₀ + thr₀ < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) h3
      have h2 : 2 * m < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) h3
      simp [Expr.eval, BinOp.eval, s5, s4, hs3_94, show 2 < 2 ^ w by omega,
        h1, h2, ← heCapDef]; exact heCapW, rfl, rfl, rfl⟩
  refine ⟨s6, 4 + (2 + (cLoop + (4 + (8 + 8 + 1) + 1) + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, hr1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, hr2,
    runs_seq_iff.mpr (Or.inr ⟨s3, cLoop, _, hrLoop,
    runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, hr4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 8, 8, hr5, hr6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [s6, eCap], hs3_mem, hs3_pos,
    fun r hr10 hr11 hr12 hr61 => by
      simp only [s6, s5, s4, Function.update_of_ne hr61, Function.update_of_ne hr11,
        Function.update_of_ne hr10]
      exact (hs3_regs r hr10 hr12).trans
        (by simp [s2, s1, Function.update_of_ne hr12, Function.update_of_ne hr10]),
    by omega⟩

/-- Copy level-0 edge lengths (`m * L` words) into the `eCap * L`-word `len0Buf` (`reg 59`),
advance to `table = len0Buf + eCap * L`, store `N₀` at `solverN0Addr table d`, copy `lvlM[0..d)`
to `solverLvlMAddr table d`, store level-0 metadata `(len0Buf, rootGraph)` at
`solverLevelMetaAddr table d` and `solverLevelMetaAddr table d + d`, leave the two select-pointer
words (`solverSelectHeapAddr`, `solverSelectBlocksAddr`) zeroed, and advance `reg 7` to
`handle = solverHandleAddr table d = table + (4 * d + 4)`. -/
@[expose] def initStage2Meta (copy : ℕ) : Stmt :=
  .assign 59 (.reg 7) ;;
  .assign 10 (.bin .mul (.reg 94) (.reg 67)) ;;
  .call 0 copy [.reg 71, .reg 59, .reg 10] ;;
  .assign 10 (.bin .mul (.reg 61) (.reg 67)) ;;
  .assign 7 (.bin .add (.reg 59) (.reg 10)) ;;
  .assign 10 (.bin .add (.reg 7) (.bin .add (.reg 75) (.const 1))) ;;
  .store (.reg 10) (.reg 56) ;;
  .assign 60 (.bin .add (.reg 10) (.const 1)) ;;
  .call 0 copy [.reg 57, .reg 60, .reg 75] ;;
  .assign 58 (.bin .add (.reg 60) (.reg 75)) ;;
  .store (.reg 58) (.reg 59) ;;
  .store (.bin .add (.reg 58) (.reg 75)) (.reg 96) ;;
  .assign 7 (.bin .add (.reg 58) (.bin .add (.bin .mul (.const 2) (.reg 75)) (.const 2)))

theorem initStage2Meta_noRand (copy : ℕ) : (initStage2Meta copy).NoRand := by
  simp [initStage2Meta, Stmt.NoRand]

/-- Execution of `initStage2Meta`: populates `len0Buf[0..m*L)`, `solverN0Addr`, `solverLvlMAddr`,
and level-0 entries of `solverLevelMetaAddr`, leaves `solverSelectHeapAddr` and
`solverSelectBlocksAddr` zeroed, and advances `reg 7` to `solverHandleAddr table d`. -/
theorem initStage2Meta_runs
    {w copy root rootGraph pBase lengths len0Buf m eCap L d N₀ : ℕ}
    {lvlM : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h7 : st.regs 7 = len0Buf) (h56 : st.regs 56 = N₀) (h57 : st.regs 57 = pBase + 6)
    (h61 : st.regs 61 = eCap) (h67 : st.regs 67 = L) (h71 : st.regs 71 = lengths)
    (h75 : st.regs 75 = d) (h94 : st.regs 94 = m) (h96 : st.regs 96 = rootGraph)
    (hmLeECap : m ≤ eCap)
    (hLenBelow : lengths + m * L ≤ root) (hrootLe : root ≤ pBase)
    (hPBaseLe : pBase + 7 + d ≤ len0Buf)
    (hMTab : ∀ i < d, st.mem (pBase + 6 + i) = lvlM i)
    (_hNw : N₀ < 2 ^ w) (hdPos : 0 < d) (hw17 : 17 < 2 ^ w)
    (hz : ZeroFrom st.mem len0Buf)
    (hroom : len0Buf + eCap * L + (4 * d + 4) < 2 ^ w) :
    let table := len0Buf + eCap * L
    let n0Cell := solverN0Addr table d
    let lvlMTable := solverLvlMAddr table d
    let levelMeta := solverLevelMetaAddr table d
    let handle := solverHandleAddr table d
    ∃ out c,
      Runs w p ω (initStage2Meta copy) st .normal out c ∧
      out.regs 7 = handle ∧ out.regs 58 = levelMeta ∧ out.regs 59 = len0Buf ∧
      out.regs 60 = lvlMTable ∧
      (∀ r, r ≠ 0 → r ≠ 7 → r ≠ 10 → r ≠ 58 → r ≠ 59 → r ≠ 60 → out.regs r = st.regs r) ∧
      (∀ j < m * L, out.mem (len0Buf + j) = st.mem (lengths + j)) ∧
      out.mem n0Cell = N₀ ∧
      (∀ i < d, out.mem (lvlMTable + i) = lvlM i) ∧
      out.mem levelMeta = len0Buf ∧
      out.mem (levelMeta + d) = rootGraph ∧
      out.mem (solverSelectHeapAddr table d) = 0 ∧
      out.mem (solverSelectBlocksAddr table d) = 0 ∧
      (∀ a < len0Buf, out.mem a = st.mem a) ∧
      ZeroFrom out.mem handle ∧
      c ≤ 30 * (m * L) + 30 * d + 140 := by
  intro table n0Cell lvlMTable levelMeta handle
  have hmLLe : m * L ≤ eCap * L := Nat.mul_le_mul_right L hmLeECap
  have hn0Def : n0Cell = table + (d + 1) := rfl
  have hlmDef : lvlMTable = n0Cell + 1 := rfl
  have hmetDef : levelMeta = lvlMTable + d := rfl
  have hshDef : solverSelectHeapAddr table d = levelMeta + 2 * d := rfl
  have hsbDef : solverSelectBlocksAddr table d = levelMeta + 2 * d + 1 := rfl
  have hhDef : handle = table + (4 * d + 4) := by
    unfold handle solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  let m1 := { st with regs := Function.update st.regs 59 len0Buf }
  let m2 := { m1 with regs := Function.update m1.regs 10 (m * L) }
  have rm1 : Runs w p ω (.assign 59 (.reg 7)) st .normal m1 2 :=
    runs_assign_iff.mpr ⟨len0Buf, by simp [Expr.eval, h7], rfl, rfl, rfl⟩
  have rm2 : Runs w p ω (.assign 10 (.bin .mul (.reg 94) (.reg 67))) m1 .normal m2 4 :=
    runs_assign_iff.mpr ⟨m * L, by
      simp [Expr.eval, BinOp.eval, m1, h94, h67, show m * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hargsC1 : evalArgs w m2 [.reg 71, .reg 59, .reg 10] = some [lengths, len0Buf, m * L] := by
    simp [evalArgs, Expr.eval, m2, m1, h71]
  have hwordsC1 : ∀ v ∈ [lengths, len0Buf, m * L], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨m3, cC1, _, rm3, hpostC1, _, hm3_keep, hcC1⟩ :=
    runs_call_of_meetsContract (r := 0) hcopy hargsC1 hwordsC1
      ⟨lengths, len0Buf, m * L, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩ ω
  obtain ⟨_, _, _, hEqC1, _, hCopy1, hFrame1⟩ := hpostC1
  simp only [List.cons.injEq, and_true] at hEqC1
  obtain ⟨rfl, rfl, rfl⟩ := hEqC1
  simp only [copyWordsContract, argsSize, Expr.size] at hcC1
  have hm3_59 : m3.regs 59 = len0Buf := (hm3_keep 59 (by decide)).trans (by simp [m2, m1])
  have hm3_61 : m3.regs 61 = eCap := (hm3_keep 61 (by decide)).trans (by simp [m2, m1, h61])
  have hm3_67 : m3.regs 67 = L := (hm3_keep 67 (by decide)).trans (by simp [m2, m1, h67])
  have hm3_75 : m3.regs 75 = d := (hm3_keep 75 (by decide)).trans (by simp [m2, m1, h75])
  have hm3_56 : m3.regs 56 = N₀ := (hm3_keep 56 (by decide)).trans (by simp [m2, m1, h56])
  have hm3_57 : m3.regs 57 = pBase + 6 := (hm3_keep 57 (by decide)).trans (by simp [m2, m1, h57])
  have hm3_96 : m3.regs 96 = rootGraph := (hm3_keep 96 (by decide)).trans (by simp [m2, m1, h96])
  let m3b := { m3 with regs := Function.update m3.regs 10 (eCap * L) }
  let m4 := { m3b with regs := Function.update m3b.regs 7 table }
  let m5 := { m4 with regs := Function.update m4.regs 10 n0Cell }
  let m6 := { m5 with mem := Function.update m5.mem n0Cell N₀ }
  let m7 := { m6 with regs := Function.update m6.regs 60 lvlMTable }
  have rm3b : Runs w p ω (.assign 10 (.bin .mul (.reg 61) (.reg 67))) m3 .normal m3b 4 :=
    runs_assign_iff.mpr ⟨eCap * L, by
      simp [Expr.eval, BinOp.eval, hm3_61, hm3_67, show eCap * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rm4 : Runs w p ω (.assign 7 (.bin .add (.reg 59) (.reg 10))) m3b .normal m4 4 :=
    runs_assign_iff.mpr ⟨table, by
      simp [Expr.eval, BinOp.eval, m3b, hm3_59, table, show len0Buf + eCap * L < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have rm5 : Runs w p ω (.assign 10 (.bin .add (.reg 7) (.bin .add (.reg 75) (.const 1)))) m4 .normal m5 6 :=
    runs_assign_iff.mpr ⟨n0Cell, by
      simp [Expr.eval, BinOp.eval, m4, m3b, hm3_75, hn0Def, table,
        show 1 < 2 ^ w by omega, show d + 1 < 2 ^ w by omega, show table + (d + 1) < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have rm6 : Runs w p ω (.store (.reg 10) (.reg 56)) m5 .normal m6 3 :=
    runs_store_iff.mpr ⟨n0Cell, N₀, by simp [Expr.eval, m5], by simp [Expr.eval, m5, m4, m3b, hm3_56],
      rfl, rfl, rfl⟩
  have rm7 : Runs w p ω (.assign 60 (.bin .add (.reg 10) (.const 1))) m6 .normal m7 4 :=
    runs_assign_iff.mpr ⟨lvlMTable, by
      simp [Expr.eval, BinOp.eval, m6, m5, hlmDef, hn0Def, table,
        show 1 < 2 ^ w by omega, show table + (d + 1) + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hargsC2 : evalArgs w m7 [.reg 57, .reg 60, .reg 75] = some [pBase + 6, lvlMTable, d] := by
    simp [evalArgs, Expr.eval, m7, m6, m5, m4, m3b, hm3_75, hm3_57]
  have hwordsC2 : ∀ v ∈ [pBase + 6, lvlMTable, d], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  have hMTab7 (i : ℕ) (hi : i < d) : m7.mem (pBase + 6 + i) = lvlM i := by
    change Function.update m3.mem n0Cell N₀ (pBase + 6 + i) = lvlM i
    rw [Function.update_of_ne (by omega)]
    exact (hFrame1 (pBase + 6 + i) (Or.inl (by omega))).trans (hMTab i hi)
  obtain ⟨m8, cC2, _, rm8, hpostC2, _, hm8_keep, hcC2⟩ :=
    runs_call_of_meetsContract (r := 0) hcopy hargsC2 hwordsC2
      ⟨pBase + 6, lvlMTable, d, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩ ω
  obtain ⟨_, _, _, hEqC2, _, hCopy2, hFrame2⟩ := hpostC2
  simp only [List.cons.injEq, and_true] at hEqC2
  obtain ⟨rfl, rfl, rfl⟩ := hEqC2
  simp only [copyWordsContract, argsSize, Expr.size] at hcC2
  have hm8_60 : m8.regs 60 = lvlMTable := (hm8_keep 60 (by decide)).trans (by simp [m7])
  have hm8_75 : m8.regs 75 = d := (hm8_keep 75 (by decide)).trans (by simp [m7, m6, m5, m4, m3b, hm3_75])
  have hm8_59 : m8.regs 59 = len0Buf := (hm8_keep 59 (by decide)).trans (by simp [m7, m6, m5, m4, m3b, hm3_59])
  have hm8_96 : m8.regs 96 = rootGraph := (hm8_keep 96 (by decide)).trans (by simp [m7, m6, m5, m4, m3b, hm3_96])
  let m9 := { m8 with regs := Function.update m8.regs 58 levelMeta }
  let m10 := { m9 with mem := Function.update m9.mem levelMeta len0Buf }
  let m11 := { m10 with mem := Function.update m10.mem (levelMeta + d) rootGraph }
  let out := { m11 with regs := Function.update m11.regs 7 handle }
  have rm9 : Runs w p ω (.assign 58 (.bin .add (.reg 60) (.reg 75))) m8 .normal m9 4 :=
    runs_assign_iff.mpr ⟨levelMeta, by
      simp [Expr.eval, BinOp.eval, hm8_60, hm8_75, hmetDef, hlmDef, hn0Def, table,
        show table + (d + 1) + 1 + d < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rm10 : Runs w p ω (.store (.reg 58) (.reg 59)) m9 .normal m10 3 :=
    runs_store_iff.mpr ⟨levelMeta, len0Buf, by simp [Expr.eval, m9],
      by simp [Expr.eval, m9, hm8_59], rfl, rfl, rfl⟩
  have rm11 : Runs w p ω (.store (.bin .add (.reg 58) (.reg 75)) (.reg 96)) m10 .normal m11 5 :=
    runs_store_iff.mpr ⟨levelMeta + d, rootGraph, by
      simp [Expr.eval, BinOp.eval, m10, m9, hm8_75, show levelMeta + d < 2 ^ w by omega],
      by simp [Expr.eval, m10, m9, hm8_96], rfl, rfl, rfl⟩
  have rm12 : Runs w p ω (.assign 7 (.bin .add (.reg 58) (.bin .add (.bin .mul (.const 2) (.reg 75)) (.const 2))))
      m11 .normal out 8 :=
    runs_assign_iff.mpr ⟨handle, by
      have hEq : levelMeta + (2 * d + 2) = handle := by omega
      simp [Expr.eval, BinOp.eval, m11, m10, m9, hm8_75,
        show 2 < 2 ^ w by omega, show 2 * d < 2 ^ w by omega,
        show 2 * d + 2 < 2 ^ w by omega, hEq, show handle < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have rFull : Runs w p ω (initStage2Meta copy) st .normal out
      (2 + (4 + (cC1 + (4 + (4 + (6 + (3 + (4 + (cC2 + (4 + (3 + (5 + 8 + 1) + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨m1, 2, _, rm1,
    runs_seq_iff.mpr (Or.inr ⟨m2, 4, _, rm2,
    runs_seq_iff.mpr (Or.inr ⟨m3, cC1, _, rm3,
    runs_seq_iff.mpr (Or.inr ⟨m3b, 4, _, rm3b,
    runs_seq_iff.mpr (Or.inr ⟨m4, 4, _, rm4,
    runs_seq_iff.mpr (Or.inr ⟨m5, 6, _, rm5,
    runs_seq_iff.mpr (Or.inr ⟨m6, 3, _, rm6,
    runs_seq_iff.mpr (Or.inr ⟨m7, 4, _, rm7,
    runs_seq_iff.mpr (Or.inr ⟨m8, cC2, _, rm8,
    runs_seq_iff.mpr (Or.inr ⟨m9, 4, _, rm9,
    runs_seq_iff.mpr (Or.inr ⟨m10, 3, _, rm10,
    runs_seq_iff.mpr (Or.inr ⟨m11, 5, 8, rm11, rm12, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hzeroGe (a : ℕ) (ha : levelMeta + 2 * d ≤ a) : out.mem a = 0 := by
    change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph a = 0
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      hFrame2 a (Or.inr (by omega))]
    change Function.update m3.mem n0Cell N₀ a = 0
    rw [Function.update_of_ne (by omega), hFrame1 a (Or.inr (by omega))]
    exact hz a (by omega)
  refine ⟨out, _, rFull, by simp [out], by simp [out, m11, m10, m9],
    by simp [out, m11, m10, m9, hm8_59], by simp [out, m11, m10, m9, hm8_60],
    fun r h0 h7' h10 h58 h59 h60 => by
      simp only [out, m11, m10, m9, Function.update_of_ne h7', Function.update_of_ne h58]
      rw [hm8_keep r h0]
      simp only [m7, m6, m5, m4, m3b, Function.update_of_ne h60, Function.update_of_ne h10, Function.update_of_ne h7']
      rw [hm3_keep r h0]
      simp only [m2, m1, Function.update_of_ne h10, Function.update_of_ne h59],
    fun j hj => by
      change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph (len0Buf + j) = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hFrame2 _ (Or.inl (by omega))]
      change Function.update m3.mem n0Cell N₀ (len0Buf + j) = _
      rw [Function.update_of_ne (by omega)]
      exact hCopy1 j hj,
    by
      change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph n0Cell = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hFrame2 _ (Or.inl (by omega))]
      change Function.update m3.mem n0Cell N₀ n0Cell = _
      simp,
    fun i hi => by
      change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph (lvlMTable + i) = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hCopy2 i hi).trans (hMTab7 i hi),
    by
      change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph levelMeta = _
      rw [Function.update_of_ne (by omega), Function.update_self],
    by
      change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph (levelMeta + d) = _
      rw [Function.update_self],
    hzeroGe _ (by omega),
    hzeroGe _ (by omega),
    fun a ha => by
      change Function.update (Function.update m8.mem levelMeta len0Buf) (levelMeta + d) rootGraph a = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hFrame2 a (Or.inl (by omega))]
      change Function.update m3.mem n0Cell N₀ a = _
      rw [Function.update_of_ne (by omega)]
      exact hFrame1 a (Or.inl ha),
    fun a ha => hzeroGe a (by omega),
    by omega⟩

end MinCostFlow.MinRatio
