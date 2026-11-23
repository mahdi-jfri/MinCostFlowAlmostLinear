module

public import MinCostFlow.MinRatio.InitSparsifierConductanceInputs
public import MinCostFlow.Spanner.PathDSContract
import Mathlib.Tactic

/-!
# Deterministic sparsifier stretch and level-cap subroutine for parameter setup

Given `M₀`, `M₀ ^ 2`, `L`, `d`, `branch`, `heap`, `[quality, epsExp, psi, N₀]`, and scratch cursor
`s2` in registers, `computeGammaAndLevelsStmt` computes `den = maxPhiDenOf decK decThr (M₀ ^ 2)`,
`cap = 36 * M₀ ^ 2 * den + 1`, calls `boundsProc` twice to obtain `g = (max g₁ g₂) ^ 2`, computes
`γ = 3 ^ L * g ^ (L + 1)`, writes `[d, branch, psi, quality, epsExp, N₀]` at `heap .. heap + 5`
and `(M₀ * γ ^ (i + 1) + branch ^ i - 1) / branch ^ i` at `heap + 6 + i` for `i < d`, and returns
the final zero-tail cursor.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-! ## Part 2: Sparsifier stretch `γ = 3^L * g^(L+1)` and level caps `lvlM[0..d)` -/

/-- Loop computing `reg 70 := 3 ^ L * g ^ (L + 1)` from `reg 44 = L`, `reg 69 = g`, `reg 70 = g`,
`reg 71 = 0`. -/
@[expose] def computeGammaLoop : Stmt :=
  .loop (.bin .lt (.reg 71) (.reg 44))
    (.assign 70 (.bin .mul (.bin .mul (.reg 70) (.const 3)) (.reg 69)) ;;
     .assign 71 (.bin .add (.reg 71) (.const 1)))

/-- Loop writing `(M₀ * γ^(i+1) + branch^i - 1) / branch^i` at `heap + 6 + i` for `i < d`,
from `reg 22 = M₀`, `reg 70 = γ`, `reg 75 = d`, `reg 76 = branch`, `reg 82 = heap`,
`reg 71 = 0`, `reg 72 = M₀ * γ`, `reg 73 = 1`. -/
@[expose] def writeLevelMLoop : Stmt :=
  .loop (.bin .lt (.reg 71) (.reg 75))
    (.store (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 71))
       (.bin .div (.bin .sub (.bin .add (.reg 72) (.reg 73)) (.const 1)) (.reg 73)) ;;
     .assign 71 (.bin .add (.reg 71) (.const 1)) ;;
     .cond (.bin .lt (.reg 71) (.reg 75))
       (.assign 72 (.bin .mul (.reg 72) (.reg 70)) ;;
        .assign 73 (.bin .mul (.reg 73) (.reg 76)))
       .nop)

/-- Compute `den`, `cap`, `g₁`, `g₂`, `g = (max g₁ g₂)^2`, `γ = 3^L * g^(L+1)`, store
`[d, branch, psi, quality, epsExp, N₀]` at `heap .. heap + 5`, the sparse-core depth `L` (register
`44`) at `heap + 6 + d` and `lvlM[0..d)` at `heap + 6 .. heap + 6 + d - 1`, and return the final
zero-tail cursor `reg 98`. -/
@[expose] def computeGammaAndLevelsStmt (decK decThr witnessDen boundsProc : ℕ) : Stmt :=
  initSparsifierConductanceDen decK decThr ;;
  .assign 64 (.bin .add (.bin .mul (.bin .mul (.const 36) (.reg 23)) (.reg 63)) (.const 1)) ;;
  .assign 65 (.reg 98) ;;
  .call 98 boundsProc [.reg 63, .reg 23, .reg 98] ;;
  .assign 66 (.load (.bin .add (.reg 65) (.const 1))) ;;
  .assign 65 (.reg 98) ;;
  .call 98 boundsProc [.const witnessDen, .reg 64, .reg 98] ;;
  .assign 67 (.load (.bin .add (.reg 65) (.const 1))) ;;
  .cond (.bin .lt (.reg 66) (.reg 67))
    (.assign 68 (.reg 67))
    (.assign 68 (.reg 66)) ;;
  .assign 69 (.bin .mul (.reg 68) (.reg 68)) ;;
  .assign 70 (.reg 69) ;;
  .assign 71 (.const 0) ;;
  computeGammaLoop ;;
  .store (.reg 82) (.reg 75) ;;
  .store (.bin .add (.reg 82) (.const 1)) (.reg 76) ;;
  .store (.bin .add (.reg 82) (.const 2)) (.reg 85) ;;
  .store (.bin .add (.reg 82) (.const 3)) (.reg 83) ;;
  .store (.bin .add (.reg 82) (.const 4)) (.reg 84) ;;
  .store (.bin .add (.reg 82) (.const 5)) (.reg 86) ;;
  .store (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 75)) (.reg 44) ;;
  .assign 71 (.const 0) ;;
  .assign 72 (.bin .mul (.reg 22) (.reg 70)) ;;
  .assign 73 (.const 1) ;;
  writeLevelMLoop ;;
  .ret (.reg 98)

theorem computeGammaAndLevelsStmt_noRand (decK decThr witnessDen boundsProc : ℕ) :
    (computeGammaAndLevelsStmt decK decThr witnessDen boundsProc).NoRand := by
  simp [computeGammaAndLevelsStmt, initSparsifierConductanceDen, Expander.computePhiDenStmt_noRand,
    computeGammaLoop, writeLevelMLoop, Stmt.NoRand]

private lemma computeGammaLoop_runs {w L g : ℕ} {p : Program} {ω : ℕ → Bool}
    (hg1 : 1 ≤ g) (hγW : 3 ^ L * g ^ (L + 1) < 2 ^ w) :
    ∀ (rem j : ℕ) (st : State),
      j + rem = L →
      st.regs 44 = L → st.regs 69 = g →
      st.regs 70 = 3 ^ j * g ^ (j + 1) → st.regs 71 = j →
      ∃ out c, Runs w p ω computeGammaLoop st .normal out c ∧
        out.regs 70 = 3 ^ L * g ^ (L + 1) ∧
        out.mem = st.mem ∧ out.pos = st.pos ∧
        (∀ r, r ≠ 70 → r ≠ 71 → out.regs r = st.regs r) ∧
        c ≤ 20 * rem + 6
  | 0, j, st, hsum, h44, _, h70, h71 => by
      have hjL : j = L := by omega
      subst hjL
      have hcond : Expr.eval w st (.bin .lt (.reg 71) (.reg 44)) = some 0 := by
        simp [Expr.eval, BinOp.eval, h71, h44, show 0 < 2 ^ w by omega]
      exact ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        h70, rfl, rfl, fun _ _ _ => rfl, by omega⟩
  | rem + 1, j, st, hsum, h44, h69, h70, h71 => by
      have hjlt : j < L := by omega
      have h3j1 : 3 ^ (j + 1) ≤ 3 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
      have hgj1 : g ^ (j + 1) ≤ g ^ (L + 1) := Nat.pow_le_pow_right hg1 (by omega)
      have hgj2 : g ^ (j + 2) ≤ g ^ (L + 1) := Nat.pow_le_pow_right hg1 (by omega)
      have h3W : 3 < 2 ^ w := by
        have h1 : 3 ≤ 3 ^ L := by
          calc 3 = 3 ^ 1 := by ring
            _ ≤ 3 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : 1 ≤ g ^ (L + 1) := Nat.one_le_pow _ _ hg1
        nlinarith
      have hstep1 : 3 ^ j * g ^ (j + 1) * 3 = 3 ^ (j + 1) * g ^ (j + 1) := by rw [pow_succ]; ring
      have hstep2 : 3 ^ (j + 1) * g ^ (j + 1) * g = 3 ^ (j + 1) * g ^ (j + 2) := by rw [pow_succ]; ring
      have hstep1W : 3 ^ j * g ^ (j + 1) * 3 < 2 ^ w := by
        rw [hstep1]; exact lt_of_le_of_lt (Nat.mul_le_mul h3j1 hgj1) hγW
      have hstep2W : 3 ^ j * g ^ (j + 1) * 3 * g < 2 ^ w := by
        rw [hstep1, hstep2]; exact lt_of_le_of_lt (Nat.mul_le_mul h3j1 hgj2) hγW
      have hj1W : j + 1 < 2 ^ w := by
        have hL : L < 3 ^ L := Nat.lt_pow_self (by decide)
        have h1 : 1 ≤ g ^ (L + 1) := Nat.one_le_pow _ _ hg1
        have h2 : 3 ^ L ≤ 3 ^ L * g ^ (L + 1) := Nat.le_mul_of_pos_right _ h1
        omega
      let s1 := { st with regs := Function.update st.regs 70 (3 ^ (j + 1) * g ^ (j + 2)) }
      let s2 := { s1 with regs := Function.update s1.regs 71 (j + 1) }
      have hr1 : Runs w p ω (.assign 70 (.bin .mul (.bin .mul (.reg 70) (.const 3)) (.reg 69)))
          st .normal s1 6 :=
        runs_assign_iff.mpr ⟨3 ^ (j + 1) * g ^ (j + 2), by
          simp only [Expr.eval, BinOp.eval, h70, h69, h3W, hstep1W, hstep2W, ite_true]
          rw [hstep1, hstep2], rfl, rfl, rfl⟩
      have hr2 : Runs w p ω (.assign 71 (.bin .add (.reg 71) (.const 1))) s1 .normal s2 4 :=
        runs_assign_iff.mpr ⟨j + 1, by
          simp [Expr.eval, BinOp.eval, s1, h71, show 1 < 2 ^ w by omega, hj1W], rfl, rfl, rfl⟩
      have hbody : Runs w p ω
          (.assign 70 (.bin .mul (.bin .mul (.reg 70) (.const 3)) (.reg 69)) ;;
           .assign 71 (.bin .add (.reg 71) (.const 1))) st .normal s2 11 :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 6, 4, hr1, hr2, rfl⟩)
      obtain ⟨out, c2, hrTail, hout70, hmem2, hpos2, hkeep2, hc2⟩ :=
        computeGammaLoop_runs hg1 hγW rem (j + 1) s2 (by omega)
          (by simp [s2, s1, h44]) (by simp [s2, s1, h69]) (by simp [s2, s1]) (by simp [s2])
      have hcond : Expr.eval w st (.bin .lt (.reg 71) (.reg 44)) = some 1 := by
        simp [Expr.eval, BinOp.eval, h71, h44, hjlt, show 1 < 2 ^ w by omega]
      refine ⟨out, 3 + 11 + c2 + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s2, 11, c2, hcond, by decide, hbody, hrTail, rfl⟩)),
        hout70, hmem2, hpos2,
        fun r hr70 hr71 => (hkeep2 r hr70 hr71).trans (by simp [s2, s1, hr70, hr71]),
        by omega⟩

private lemma writeLevelMLoop_runs {w M₀ γ d branch heap : ℕ} {p : Program} {ω : ℕ → Bool}
    (hbr1 : 1 ≤ branch) (hM0γ1 : 1 ≤ M₀ * γ)
    (hroom : heap + 6 + d < 2 ^ w)
    (hnumW : ∀ i < d, M₀ * γ ^ (i + 1) + branch ^ i < 2 ^ w) :
    ∀ (rem i : ℕ) (st : State),
      i + rem = d →
      st.regs 22 = M₀ → st.regs 70 = γ → st.regs 75 = d → st.regs 76 = branch →
      st.regs 82 = heap → st.regs 71 = i →
      (i < d → st.regs 72 = M₀ * γ ^ (i + 1) ∧ st.regs 73 = branch ^ i) →
      ∃ out c, Runs w p ω writeLevelMLoop st .normal out c ∧
        (∀ j, i ≤ j → j < d →
          out.mem (heap + 6 + j) = (M₀ * γ ^ (j + 1) + branch ^ j - 1) / branch ^ j) ∧
        (∀ a, a < heap + 6 + i ∨ heap + 6 + d ≤ a → out.mem a = st.mem a) ∧
        out.regs 98 = st.regs 98 ∧ out.pos = st.pos ∧
        c ≤ 45 * rem + 6
  | 0, i, st, hsum, _, _, h75, _, _, h71, _ => by
      have hid : i = d := by omega
      subst hid
      have hcond : Expr.eval w st (.bin .lt (.reg 71) (.reg 75)) = some 0 := by
        simp [Expr.eval, BinOp.eval, h71, h75, show 0 < 2 ^ w by omega]
      exact ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        fun _ h1 h2 => by omega, fun _ _ => rfl, rfl, rfl, by omega⟩
  | rem + 1, i, st, hsum, h22, h70, h75, h76, h82, h71, hpow => by
      have hilt : i < d := by omega
      obtain ⟨h72, h73⟩ := hpow hilt
      have hsumW : M₀ * γ ^ (i + 1) + branch ^ i < 2 ^ w := hnumW i hilt
      have hsubW : M₀ * γ ^ (i + 1) + branch ^ i - 1 < 2 ^ w := by omega
      have hdivW : (M₀ * γ ^ (i + 1) + branch ^ i - 1) / branch ^ i < 2 ^ w :=
        lt_of_le_of_lt (Nat.div_le_self _ _) hsubW
      have h1W : 1 < 2 ^ w := by omega
      have h6W : 6 < 2 ^ w := by omega
      have haddrW : heap + 6 + i < 2 ^ w := by omega
      have hheap6W : heap + 6 < 2 ^ w := by omega
      let val := (M₀ * γ ^ (i + 1) + branch ^ i - 1) / branch ^ i
      let s1 := { st with mem := Function.update st.mem (heap + 6 + i) val }
      let s2 := { s1 with regs := Function.update s1.regs 71 (i + 1) }
      have hr1 : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 71))
            (.bin .div (.bin .sub (.bin .add (.reg 72) (.reg 73)) (.const 1)) (.reg 73)))
          st .normal s1 13 :=
        runs_store_iff.mpr ⟨heap + 6 + i, val,
          by simp [Expr.eval, BinOp.eval, h82, h71, h6W, hheap6W, haddrW],
          by simp [Expr.eval, BinOp.eval, h72, h73, h1W, hsumW, hsubW, hdivW, val],
          rfl, rfl, rfl⟩
      have hi1W : i + 1 < 2 ^ w := by omega
      have hr2 : Runs w p ω (.assign 71 (.bin .add (.reg 71) (.const 1))) s1 .normal s2 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, BinOp.eval, s1, h71, h1W, hi1W],
          rfl, rfl, rfl⟩
      have hs2_next : ∃ s3 c3,
          Runs w p ω
            (.cond (.bin .lt (.reg 71) (.reg 75))
              (.assign 72 (.bin .mul (.reg 72) (.reg 70)) ;;
               .assign 73 (.bin .mul (.reg 73) (.reg 76))) .nop)
            s2 .normal s3 c3 ∧
          s3.mem = s1.mem ∧ s3.pos = st.pos ∧
          s3.regs 22 = M₀ ∧ s3.regs 70 = γ ∧ s3.regs 75 = d ∧ s3.regs 76 = branch ∧
          s3.regs 82 = heap ∧ s3.regs 71 = i + 1 ∧ s3.regs 98 = st.regs 98 ∧
          (i + 1 < d → s3.regs 72 = M₀ * γ ^ (i + 2) ∧ s3.regs 73 = branch ^ (i + 1)) ∧
          c3 ≤ 15 := by
        by_cases hnext : i + 1 < d
        · have hnextW := hnumW (i + 1) hnext
          have hmul1 : M₀ * γ ^ (i + 1) * γ = M₀ * γ ^ (i + 2) := by rw [pow_succ]; ring
          have hmul2 : branch ^ i * branch = branch ^ (i + 1) := by rw [pow_succ]
          let s2a := { s2 with regs := Function.update s2.regs 72 (M₀ * γ ^ (i + 2)) }
          let s3 := { s2a with regs := Function.update s2a.regs 73 (branch ^ (i + 1)) }
          have hra : Runs w p ω (.assign 72 (.bin .mul (.reg 72) (.reg 70))) s2 .normal s2a 4 :=
            runs_assign_iff.mpr ⟨M₀ * γ ^ (i + 2), by
              have hlt1 : M₀ * γ ^ (i + 2) < 2 ^ w := by
                rw [show i + 2 = i + 1 + 1 by omega]; omega
              simp [Expr.eval, BinOp.eval, s2, s1, h72, h70, hmul1, hlt1], rfl, rfl, rfl⟩
          have hrb : Runs w p ω (.assign 73 (.bin .mul (.reg 73) (.reg 76))) s2a .normal s3 4 :=
            runs_assign_iff.mpr ⟨branch ^ (i + 1), by
              simp [Expr.eval, BinOp.eval, s2a, s2, s1, h73, h76, hmul2,
                show branch ^ (i + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
          have hcondN : Expr.eval w s2 (.bin .lt (.reg 71) (.reg 75)) = some 1 := by
            simp [Expr.eval, BinOp.eval, s2, s1, h75, hnext, h1W]
          exact ⟨s3, 13,
            runs_cond_iff.mpr ⟨1, 9, hcondN, runs_seq_iff.mpr (Or.inr ⟨s2a, 4, 4, hra, hrb, rfl⟩), rfl⟩,
            rfl, rfl, by simp [s3, s2a, s2, s1, h22], by simp [s3, s2a, s2, s1, h70],
            by simp [s3, s2a, s2, s1, h75], by simp [s3, s2a, s2, s1, h76],
            by simp [s3, s2a, s2, s1, h82], by simp [s3, s2a, s2], by simp [s3, s2a, s2, s1],
            fun _ => ⟨by simp [s3, s2a], by simp [s3]⟩, by omega⟩
        · have hcondN : Expr.eval w s2 (.bin .lt (.reg 71) (.reg 75)) = some 0 := by
            simp [Expr.eval, BinOp.eval, s2, s1, h75, hnext, show 0 < 2 ^ w by omega]
          exact ⟨s2, 5, runs_cond_iff.mpr ⟨0, 1, hcondN, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
            rfl, rfl, by simp [s2, s1, h22], by simp [s2, s1, h70],
            by simp [s2, s1, h75], by simp [s2, s1, h76],
            by simp [s2, s1, h82], by simp [s2], by simp [s2, s1],
            fun h => (hnext h).elim, by omega⟩
      obtain ⟨s3, c3, hr3, hmem3, hpos3, hs3_22, hs3_70, hs3_75, hs3_76, hs3_82, hs3_71, hs3_98, hs3_pow, hc3⟩ := hs2_next
      have hbody : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 71))
             (.bin .div (.bin .sub (.bin .add (.reg 72) (.reg 73)) (.const 1)) (.reg 73)) ;;
           .assign 71 (.bin .add (.reg 71) (.const 1)) ;;
           .cond (.bin .lt (.reg 71) (.reg 75))
             (.assign 72 (.bin .mul (.reg 72) (.reg 70)) ;;
              .assign 73 (.bin .mul (.reg 73) (.reg 76))) .nop)
          st .normal s3 (13 + (4 + c3 + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 13, 4 + c3 + 1, hr1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 4, c3, hr2, hr3, rfl⟩), rfl⟩)
      obtain ⟨out, cTail, hrTail, hwriteTail, hframeTail, hout98, hposTail, hcTail⟩ :=
        writeLevelMLoop_runs hbr1 hM0γ1 hroom hnumW rem (i + 1) s3 (by omega)
          hs3_22 hs3_70 hs3_75 hs3_76 hs3_82 hs3_71 hs3_pow
      have hcond : Expr.eval w st (.bin .lt (.reg 71) (.reg 75)) = some 1 := by
        simp [Expr.eval, BinOp.eval, h71, h75, hilt, h1W]
      refine ⟨out, 3 + (13 + (4 + c3 + 1) + 1) + cTail + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, 13 + (4 + c3 + 1) + 1, cTail, hcond, by decide, hbody, hrTail, rfl⟩)),
        ?_, ?_, hout98.trans hs3_98, hposTail.trans hpos3, by omega⟩
      · intro j hjlo hjhi
        by_cases hjeq : j = i
        · subst hjeq
          have h1 := hframeTail (heap + 6 + j) (Or.inl (by omega))
          rw [h1, hmem3]; simp [s1, val]
        · exact hwriteTail j (by omega) hjhi
      · intro a ha
        rcases ha with hlt | hge
        · rw [hframeTail a (Or.inl (by omega)), hmem3]
          simp [s1, Function.update_of_ne (show a ≠ heap + 6 + i by omega)]
        · rw [hframeTail a (Or.inr hge), hmem3]
          simp [s1, Function.update_of_ne (show a ≠ heap + 6 + i by omega)]

/-- Step-cost bound for `computeGammaAndLevelsStmt`. -/
@[expose] def gammaAndLevelsCost (decK decThr witnessDen M₀ L d K_bounds : ℕ) : ℕ :=
  let den := Expander.maxPhiDenOf decK decThr (M₀ ^ 2)
  let cap := 36 * M₀ ^ 2 * den + 1
  120 * (Nat.log 2 (4 * M₀ ^ 2 + 2) + decK * (Expander.rOf (4 * M₀ ^ 2)) ^ 2 + 4) +
    K_bounds * (Nat.log 2 (den + M₀ ^ 2 + 2) + 1) +
    K_bounds * (Nat.log 2 (witnessDen + cap + 2) + 1) +
    20 * L + 45 * d + 200

theorem computeGammaAndLevelsStmt_runs
    {w decK decThr witnessDen boundsProc M₀ L d branch heap quality epsExp psi N₀ s2 : ℕ}
    {pds : Spanner.PathDSParams} {p : Program} {ω : ℕ → Bool} {st : State}
    (hdecK : 1 ≤ decK) (hwit1 : 1 ≤ witnessDen)
    (hM01 : 1 ≤ M₀) (hd1 : 1 ≤ d) (hbr1 : 1 ≤ branch)
    (hbounds : MeetsContract w p boundsProc (Spanner.pathDSBoundsContract pds w))
    (h22 : st.regs 22 = M₀) (h23 : st.regs 23 = M₀ ^ 2) (h44 : st.regs 44 = L)
    (h75 : st.regs 75 = d) (h76 : st.regs 76 = branch) (h82 : st.regs 82 = heap)
    (h83 : st.regs 83 = quality) (h84 : st.regs 84 = epsExp) (h85 : st.regs 85 = psi)
    (h86 : st.regs 86 = N₀) (h98 : st.regs 98 = s2)
    (hs2Lo : heap + 6 + d ≤ s2) (hz2 : ZeroFrom st.mem s2)
    (h4M2W : 4 * M₀ ^ 2 + 2 < 2 ^ w)
    (hcubeW : (Nat.log 2 (4 * M₀ ^ 2 + 2) + 2) ^ 3 < 2 ^ w)
    (hdenW : Expander.maxPhiDenOf decK decThr (M₀ ^ 2) < 2 ^ w)
    (hcapW : 36 * M₀ ^ 2 * Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + 1 < 2 ^ w)
    (hwitW : witnessDen < 2 ^ w)
    (hRoomB : s2 + pds.boundsSpace (Expander.maxPhiDenOf decK decThr (M₀ ^ 2)) (M₀ ^ 2) +
        pds.boundsSpace witnessDen (36 * M₀ ^ 2 * Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + 1) < 2 ^ w)
    (hcw1 : pds.cw * (Nat.log 2 (Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + M₀ ^ 2 +
        pds.gExp (Expander.maxPhiDenOf decK decThr (M₀ ^ 2)) (M₀ ^ 2) +
        pds.gDel (Expander.maxPhiDenOf decK decThr (M₀ ^ 2)) (M₀ ^ 2) + 2) + 1) ≤ w)
    (hcw2 : pds.cw * (Nat.log 2 (witnessDen +
        (36 * M₀ ^ 2 * Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + 1) +
        pds.gExp witnessDen (36 * M₀ ^ 2 * Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + 1) +
        pds.gDel witnessDen (36 * M₀ ^ 2 * Expander.maxPhiDenOf decK decThr (M₀ ^ 2) + 1) + 2) + 1) ≤ w)
    (hnumW : ∀ i < d,
      let den := Expander.maxPhiDenOf decK decThr (M₀ ^ 2)
      let cap := 36 * M₀ ^ 2 * den + 1
      let g := (max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap)) ^ 2
      let γ := 3 ^ L * g ^ (L + 1)
      M₀ * γ ^ (i + 1) + branch ^ i < 2 ^ w) :
    let den := Expander.maxPhiDenOf decK decThr (M₀ ^ 2)
    let cap := 36 * M₀ ^ 2 * den + 1
    let g := (max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap)) ^ 2
    let γ := 3 ^ L * g ^ (L + 1)
    ∃ out ret c, Runs w p ω (computeGammaAndLevelsStmt decK decThr witnessDen boundsProc) st
        (.returned ret) out c ∧
      s2 + 6 ≤ ret ∧
      ret ≤ s2 + pds.boundsSpace den (M₀ ^ 2) + pds.boundsSpace witnessDen cap ∧
      ListAt out.mem heap [d, branch, psi, quality, epsExp, N₀] ∧
      (∀ i < d, out.mem (heap + 6 + i) = (M₀ * γ ^ (i + 1) + branch ^ i - 1) / branch ^ i) ∧
      out.mem (heap + 6 + d) = L ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      ZeroFrom out.mem ret ∧
      c ≤ gammaAndLevelsCost decK decThr witnessDen M₀ L d pds.K_bounds := by
  intro den cap g γ
  have hden1 : 1 ≤ den := Expander.maxPhiDenOf_pos decK decThr (M₀ ^ 2)
  have hg1_ge2 : 2 ≤ pds.gExp den (M₀ ^ 2) :=
    le_trans (le_trans (le_max_left 2 _) (pds.hphiOutDen_ge den (M₀ ^ 2) hden1))
      (pds.hgExp_ge den (M₀ ^ 2) hden1)
  have hg_ge1 : 1 ≤ g := by
    have : 2 ≤ max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap) :=
      le_trans hg1_ge2 (le_max_left _ _)
    dsimp only [g]; exact Nat.one_le_pow 2 _ (by omega)
  have hγ_ge1 : 1 ≤ γ := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos hg_ge1)
  have hγW : γ < 2 ^ w := by
    have h0 := hnumW 0 hd1
    dsimp only at h0
    simp only [Nat.zero_add, pow_one, pow_zero] at h0
    change M₀ * γ + 1 < 2 ^ w at h0
    have h1 : γ ≤ M₀ * γ := Nat.le_mul_of_pos_left _ hM01
    omega
  have hgW : g < 2 ^ w := by
    have h1 : g ≤ g ^ (L + 1) := Nat.le_self_pow (Nat.succ_ne_zero L) g
    have h2 : g ^ (L + 1) ≤ 3 ^ L * g ^ (L + 1) := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
    exact lt_of_le_of_lt (h1.trans h2) hγW
  have hgMaxW : max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap) < 2 ^ w := by
    have h1 : max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap) ≤ g :=
      Nat.le_self_pow (by decide : 2 ≠ 0) _
    exact lt_of_le_of_lt h1 hgW
  -- Step 1: den
  obtain ⟨s_d, cd, hrd, hsd_63, hsd_mem, hsd_keep, hcd⟩ :=
    initSparsifierConductanceDen_runs (w := w) (p := p) (ω := ω) hdecK h23 h4M2W hcubeW hdenW
  have hsd_63' : s_d.regs 63 = den := hsd_63
  have hkd (r : ℕ) (h1 : r ≠ 63) (h2 : r ≠ 24) (h3 : r ≠ 31) (h4 : r ≠ 32) (h5 : r ≠ 33) (h6 : r ≠ 36) :
      s_d.regs r = st.regs r := hsd_keep r h1 h2 h3 h4 h5 h6
  -- Step 2: cap
  let s_c := { s_d with regs := Function.update s_d.regs 64 cap }
  let s_p1 := { s_c with regs := Function.update s_c.regs 65 s2 }
  have hcapW' : 36 * M₀ ^ 2 * den + 1 < 2 ^ w := hcapW
  have hRoomB' : s2 + pds.boundsSpace den (M₀ ^ 2) + pds.boundsSpace witnessDen cap < 2 ^ w := hRoomB
  have hrc : Runs w p ω
      (.assign 64 (.bin .add (.bin .mul (.bin .mul (.const 36) (.reg 23)) (.reg 63)) (.const 1)))
      s_d .normal s_c 8 :=
    runs_assign_iff.mpr ⟨cap, by
      have h23' : s_d.regs 23 = M₀ ^ 2 := (hkd 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
      have hM2_1 : 1 ≤ M₀ ^ 2 := Nat.one_le_pow 2 _ hM01
      have h36M2 : 36 * M₀ ^ 2 < 2 ^ w := by
        have : 36 * M₀ ^ 2 ≤ 36 * M₀ ^ 2 * den := Nat.le_mul_of_pos_right _ hden1
        omega
      have h36W : 36 < 2 ^ w := by
        have : 36 ≤ 36 * M₀ ^ 2 := Nat.le_mul_of_pos_right 36 hM2_1
        omega
      have h36M2d : 36 * M₀ ^ 2 * den < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, h23', hsd_63', cap, h36W,
        show 1 < 2 ^ w by omega, h36M2, h36M2d, hcapW'], rfl, rfl, rfl⟩
  have hsd_98 : s_d.regs 98 = s2 :=
    (hkd 98 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h98
  have hrp1 : Runs w p ω (.assign 65 (.reg 98)) s_c .normal s_p1 2 :=
    runs_assign_iff.mpr ⟨s2, by simp [Expr.eval, s_c, hsd_98], rfl, rfl, rfl⟩
  -- Step 3: first boundsProc call on [den, M₀^2, s2]
  have ha_b1 : evalArgs w s_p1 [.reg 63, .reg 23, .reg 98] = some [den, M₀ ^ 2, s2] := by
    have h23' : s_d.regs 23 = M₀ ^ 2 := (hkd 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
    simp [evalArgs, Expr.eval, s_p1, s_c, hsd_63', h23', hsd_98]
  have hw_b1 : ∀ v ∈ [den, M₀ ^ 2, s2], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨s_b1, cb1, s3, hrb1, hpost_b1, hsb1_98, hsb1_keep, hcb1⟩ :=
    runs_call_of_meetsContract (r := 98) hbounds ha_b1 hw_b1
      ⟨⟨den, M₀ ^ 2, s2, rfl, hden1, hcw1⟩, by simpa [heapArg, s_p1, s_c, hsd_mem] using hz2,
        by change s2 + pds.boundsSpace den (M₀ ^ 2) < 2 ^ w; omega⟩ ω
  obtain ⟨⟨hs2_le_s3, hs3_le, hframe_b1, hz3, d1', M1', h1', heq1, hlist1⟩, hs2_3_le⟩ := hpost_b1
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨rfl, rfl, rfl⟩
  change s2 ≤ s3 at hs2_le_s3
  change s3 ≤ s2 + pds.boundsSpace den (M₀ ^ 2) at hs3_le
  change ∀ x < s2, s_b1.mem x = s_p1.mem x at hframe_b1
  change s2 + 3 ≤ s3 at hs2_3_le
  have hg1_mem : s_b1.mem (s2 + 1) = pds.gExp den (M₀ ^ 2) := by
    simpa using hlist1 1 (by simp)
  have hsb1_65 : s_b1.regs 65 = s2 := (hsb1_keep 65 (by decide)).trans (by simp [s_p1])
  let s_g1 := { s_b1 with regs := Function.update s_b1.regs 66 (pds.gExp den (M₀ ^ 2)) }
  have hrg1 : Runs w p ω (.assign 66 (.load (.bin .add (.reg 65) (.const 1)))) s_b1 .normal s_g1 5 :=
    runs_assign_iff.mpr ⟨pds.gExp den (M₀ ^ 2), by
      simp [Expr.eval, BinOp.eval, hsb1_65, show 1 < 2 ^ w by omega,
        show s2 + 1 < 2 ^ w by omega, hg1_mem], rfl, rfl, rfl⟩
  -- Step 4: second boundsProc call on [witnessDen, cap, s3]
  let s_p2 := { s_g1 with regs := Function.update s_g1.regs 65 s3 }
  have hrp2 : Runs w p ω (.assign 65 (.reg 98)) s_g1 .normal s_p2 2 :=
    runs_assign_iff.mpr ⟨s3, by simp [Expr.eval, s_g1, hsb1_98], rfl, rfl, rfl⟩
  have hsb1_64 : s_b1.regs 64 = cap := (hsb1_keep 64 (by decide)).trans (by simp [s_p1, s_c])
  have ha_b2 : evalArgs w s_p2 [.const witnessDen, .reg 64, .reg 98] = some [witnessDen, cap, s3] := by
    simp [evalArgs, Expr.eval, s_p2, s_g1, hwitW, hsb1_64, hsb1_98]
  have hw_b2 : ∀ v ∈ [witnessDen, cap, s3], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨s_b2, cb2, s4, hrb2, hpost_b2, hsb2_98, hsb2_keep, hcb2⟩ :=
    runs_call_of_meetsContract (r := 98) hbounds ha_b2 hw_b2
      ⟨⟨witnessDen, cap, s3, rfl, hwit1, hcw2⟩, by simpa [heapArg, s_p2, s_g1] using hz3,
        by change s3 + pds.boundsSpace witnessDen cap < 2 ^ w; omega⟩ ω
  obtain ⟨⟨hs3_le_s4, hs4_le, hframe_b2, hz4, d2', M2', h2', heq2, hlist2⟩, hs3_3_le⟩ := hpost_b2
  simp only [List.cons.injEq, and_true] at heq2
  rcases heq2 with ⟨rfl, rfl, rfl⟩
  change s3 ≤ s4 at hs3_le_s4
  change s4 ≤ s3 + pds.boundsSpace witnessDen cap at hs4_le
  change ∀ x < s3, s_b2.mem x = s_p2.mem x at hframe_b2
  change s3 + 3 ≤ s4 at hs3_3_le
  have hg2_mem : s_b2.mem (s3 + 1) = pds.gExp witnessDen cap := by
    simpa using hlist2 1 (by simp)
  have hsb2_65 : s_b2.regs 65 = s3 := (hsb2_keep 65 (by decide)).trans (by simp [s_p2])
  let s_g2 := { s_b2 with regs := Function.update s_b2.regs 67 (pds.gExp witnessDen cap) }
  have hrg2 : Runs w p ω (.assign 67 (.load (.bin .add (.reg 65) (.const 1)))) s_b2 .normal s_g2 5 :=
    runs_assign_iff.mpr ⟨pds.gExp witnessDen cap, by
      simp [Expr.eval, BinOp.eval, hsb2_65, show 1 < 2 ^ w by omega,
        show s3 + 1 < 2 ^ w by omega, hg2_mem], rfl, rfl, rfl⟩
  -- Step 5: gMax, g, γ
  have hsg2_66 : s_g2.regs 66 = pds.gExp den (M₀ ^ 2) := by
    simp only [s_g2, Function.update_of_ne (by decide : (66 : ℕ) ≠ 67)]
    exact (hsb2_keep 66 (by decide)).trans (by simp [s_p2, s_g1])
  let gMax := max (pds.gExp den (M₀ ^ 2)) (pds.gExp witnessDen cap)
  let s_gm := { s_g2 with regs := Function.update s_g2.regs 68 gMax }
  let s_gg := { s_gm with regs := Function.update s_gm.regs 69 g }
  let s_a0 := { s_gg with regs := Function.update s_gg.regs 70 g }
  let s_i0 := { s_a0 with regs := Function.update s_a0.regs 71 0 }
  have hsg2_67 : s_g2.regs 67 = pds.gExp witnessDen cap := by simp [s_g2]
  have hrgm : Runs w p ω
      (.cond (.bin .lt (.reg 66) (.reg 67)) (.assign 68 (.reg 67)) (.assign 68 (.reg 66)))
      s_g2 .normal s_gm 6 := by
    by_cases hlt : pds.gExp den (M₀ ^ 2) < pds.gExp witnessDen cap
    · have hgm : gMax = pds.gExp witnessDen cap := max_eq_right hlt.le
      refine runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, hsg2_66, hsg2_67, hlt, show 1 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨pds.gExp witnessDen cap, by simp [Expr.eval, hsg2_67], rfl, by simp [s_gm, hgm], rfl⟩, rfl⟩
    · have hgm : gMax = pds.gExp den (M₀ ^ 2) := max_eq_left (by omega)
      refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, hsg2_66, hsg2_67, hlt, show 0 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨pds.gExp den (M₀ ^ 2), by simp [Expr.eval, hsg2_66], rfl, by simp [s_gm, hgm], rfl⟩, rfl⟩
  have hg_eq : g = gMax * gMax := sq gMax
  have hrgg : Runs w p ω (.assign 69 (.bin .mul (.reg 68) (.reg 68))) s_gm .normal s_gg 4 :=
    runs_assign_iff.mpr ⟨g, by
      have hgW' : gMax * gMax < 2 ^ w := hg_eq ▸ hgW
      simp [Expr.eval, BinOp.eval, s_gm, hg_eq, hgW'], rfl, rfl, rfl⟩
  have hra0 : Runs w p ω (.assign 70 (.reg 69)) s_gg .normal s_a0 2 :=
    runs_assign_iff.mpr ⟨g, by simp [Expr.eval, s_gg], rfl, rfl, rfl⟩
  have hri0 : Runs w p ω (.assign 71 (.const 0)) s_a0 .normal s_i0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hkeepPre (r : ℕ) (h1 : r ≠ 24) (h2 : r ≠ 31) (h3 : r ≠ 32) (h4 : r ≠ 33) (h5 : r ≠ 36)
      (h6 : r ≠ 63) (h7 : r ≠ 64) (h8 : r ≠ 65) (h9 : r ≠ 66) (h10 : r ≠ 67) (h11 : r ≠ 68)
      (h12 : r ≠ 69) (h13 : r ≠ 70) (h14 : r ≠ 71) (h15 : r ≠ 98) :
      s_i0.regs r = st.regs r := by
    simp only [s_i0, s_a0, s_gg, s_gm, s_g2, Function.update_of_ne h14, Function.update_of_ne h13,
      Function.update_of_ne h12, Function.update_of_ne h11, Function.update_of_ne h10]
    rw [hsb2_keep r h15]
    simp only [s_p2, s_g1, Function.update_of_ne h8, Function.update_of_ne h9]
    rw [hsb1_keep r h15]
    simp only [s_p1, s_c, Function.update_of_ne h8, Function.update_of_ne h7]
    exact hkd r h6 h1 h2 h3 h4 h5
  obtain ⟨s_gam, cgam, hrgam, hsgam_70, hsgam_mem, _, hsgam_keep, hcgam⟩ :=
    computeGammaLoop_runs (w := w) (L := L) (g := g) (p := p) (ω := ω) hg_ge1 hγW L 0 s_i0
      (Nat.zero_add L)
      ((hkeepPre 44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans h44)
      (by simp [s_i0, s_a0, s_gg]) (by simp [s_i0, s_a0]) (by simp [s_i0])
  change s_gam.regs 70 = γ at hsgam_70
  have hkeepGam (r : ℕ) (h1 : r ≠ 24) (h2 : r ≠ 31) (h3 : r ≠ 32) (h4 : r ≠ 33) (h5 : r ≠ 36)
      (h6 : r ≠ 63) (h7 : r ≠ 64) (h8 : r ≠ 65) (h9 : r ≠ 66) (h10 : r ≠ 67) (h11 : r ≠ 68)
      (h12 : r ≠ 69) (h13 : r ≠ 70) (h14 : r ≠ 71) (h15 : r ≠ 98) :
      s_gam.regs r = st.regs r :=
    (hsgam_keep r h13 h14).trans (hkeepPre r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15)
  have hsgam_98 : s_gam.regs 98 = s4 := by
    rw [hsgam_keep 98 (by decide) (by decide)]
    simp [s_i0, s_a0, s_gg, s_gm, s_g2, hsb2_98]
  -- Step 6: store the 6 scalar parameters at heap .. heap + 5
  have hsgam_82 : s_gam.regs 82 = heap := (hkeepGam 82 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h82
  have hsgam_75 : s_gam.regs 75 = d := (hkeepGam 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h75
  have hsgam_76 : s_gam.regs 76 = branch := (hkeepGam 76 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h76
  have hsgam_85 : s_gam.regs 85 = psi := (hkeepGam 85 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h85
  have hsgam_83 : s_gam.regs 83 = quality := (hkeepGam 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h83
  have hsgam_84 : s_gam.regs 84 = epsExp := (hkeepGam 84 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h84
  have hsgam_86 : s_gam.regs 86 = N₀ := (hkeepGam 86 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h86
  have hsgam_22 : s_gam.regs 22 = M₀ := (hkeepGam 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
  let m0 := Function.update s_gam.mem heap d
  let m1 := Function.update m0 (heap + 1) branch
  let m2 := Function.update m1 (heap + 2) psi
  let m3 := Function.update m2 (heap + 3) quality
  let m4 := Function.update m3 (heap + 4) epsExp
  let m5 := Function.update m4 (heap + 5) N₀
  let sw0 := { s_gam with mem := m0 }
  let sw1 := { sw0 with mem := m1 }
  let sw2 := { sw1 with mem := m2 }
  let sw3 := { sw2 with mem := m3 }
  let sw4 := { sw3 with mem := m4 }
  let sw5 := { sw4 with mem := m5 }
  have hw0 : Runs w p ω (.store (.reg 82) (.reg 75)) s_gam .normal sw0 3 :=
    runs_store_iff.mpr ⟨heap, d, by simp [Expr.eval, hsgam_82], by simp [Expr.eval, hsgam_75], rfl, rfl, rfl⟩
  have hw1 : Runs w p ω (.store (.bin .add (.reg 82) (.const 1)) (.reg 76)) sw0 .normal sw1 5 :=
    runs_store_iff.mpr ⟨heap + 1, branch, by simp [Expr.eval, BinOp.eval, sw0, hsgam_82, show 1 < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega],
      by simp [Expr.eval, sw0, hsgam_76], rfl, rfl, rfl⟩
  have hw2 : Runs w p ω (.store (.bin .add (.reg 82) (.const 2)) (.reg 85)) sw1 .normal sw2 5 :=
    runs_store_iff.mpr ⟨heap + 2, psi, by simp [Expr.eval, BinOp.eval, sw1, sw0, hsgam_82, show 2 < 2 ^ w by omega, show heap + 2 < 2 ^ w by omega],
      by simp [Expr.eval, sw1, sw0, hsgam_85], rfl, rfl, rfl⟩
  have hw3 : Runs w p ω (.store (.bin .add (.reg 82) (.const 3)) (.reg 83)) sw2 .normal sw3 5 :=
    runs_store_iff.mpr ⟨heap + 3, quality, by simp [Expr.eval, BinOp.eval, sw2, sw1, sw0, hsgam_82, show 3 < 2 ^ w by omega, show heap + 3 < 2 ^ w by omega],
      by simp [Expr.eval, sw2, sw1, sw0, hsgam_83], rfl, rfl, rfl⟩
  have hw4 : Runs w p ω (.store (.bin .add (.reg 82) (.const 4)) (.reg 84)) sw3 .normal sw4 5 :=
    runs_store_iff.mpr ⟨heap + 4, epsExp, by simp [Expr.eval, BinOp.eval, sw3, sw2, sw1, sw0, hsgam_82, show 4 < 2 ^ w by omega, show heap + 4 < 2 ^ w by omega],
      by simp [Expr.eval, sw3, sw2, sw1, sw0, hsgam_84], rfl, rfl, rfl⟩
  have hw5 : Runs w p ω (.store (.bin .add (.reg 82) (.const 5)) (.reg 86)) sw4 .normal sw5 5 :=
    runs_store_iff.mpr ⟨heap + 5, N₀, by simp [Expr.eval, BinOp.eval, sw4, sw3, sw2, sw1, sw0, hsgam_82, show 5 < 2 ^ w by omega, show heap + 5 < 2 ^ w by omega],
      by simp [Expr.eval, sw4, sw3, sw2, sw1, sw0, hsgam_86], rfl, rfl, rfl⟩
  -- Step 6b: store the sparse-core depth `L` at `heap + 6 + d`
  have hsgam_44 : s_gam.regs 44 = L := (hkeepGam 44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h44
  let m6 := Function.update m5 (heap + 6 + d) L
  let sw6 := { sw5 with mem := m6 }
  have hw6 : Runs w p ω (.store (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 75)) (.reg 44))
      sw5 .normal sw6 7 :=
    runs_store_iff.mpr ⟨heap + 6 + d, L, by
      simp [Expr.eval, BinOp.eval, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_82, hsgam_75,
        show 6 < 2 ^ w by omega, show heap + 6 < 2 ^ w by omega,
        show heap + 6 + d < 2 ^ w by omega],
      by simp [Expr.eval, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_44], rfl, rfl, rfl⟩
  -- Step 7: initialize levelM loop registers and run writeLevelMLoop
  let sl0 := { sw6 with regs := Function.update sw6.regs 71 0 }
  let sl1 := { sl0 with regs := Function.update sl0.regs 72 (M₀ * γ) }
  let sl2 := { sl1 with regs := Function.update sl1.regs 73 1 }
  have hrl0 : Runs w p ω (.assign 71 (.const 0)) sw6 .normal sl0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hrl1 : Runs w p ω (.assign 72 (.bin .mul (.reg 22) (.reg 70))) sl0 .normal sl1 4 :=
    runs_assign_iff.mpr ⟨M₀ * γ, by
      have hM0γW : M₀ * γ < 2 ^ w := by
        have h0 := hnumW 0 hd1; dsimp only at h0
        simp only [Nat.zero_add, pow_one, pow_zero] at h0
        change M₀ * γ + 1 < 2 ^ w at h0; omega
      simp [Expr.eval, BinOp.eval, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_22, hsgam_70, hM0γW],
      rfl, rfl, rfl⟩
  have hrl2 : Runs w p ω (.assign 73 (.const 1)) sl1 .normal sl2 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s_fin, cfin, hrfin, hwriteM, hframeM, hsfin_98, _, hcfin⟩ :=
    writeLevelMLoop_runs (w := w) (M₀ := M₀) (γ := γ) (d := d) (branch := branch) (heap := heap)
      (p := p) (ω := ω) hbr1 (Nat.mul_pos hM01 hγ_ge1) (by omega) hnumW d 0 sl2 (Nat.zero_add d)
      (by simp [sl2, sl1, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_22])
      (by simp [sl2, sl1, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_70])
      (by simp [sl2, sl1, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_75])
      (by simp [sl2, sl1, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_76])
      (by simp [sl2, sl1, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_82])
      (by simp [sl2, sl1, sl0])
      (fun _ => ⟨by simp [sl2, sl1], by simp [sl2]⟩)
  have hsfin_98' : s_fin.regs 98 = s4 := by
    rw [hsfin_98]; simp [sl2, sl1, sl0, sw6, sw5, sw4, sw3, sw2, sw1, sw0, hsgam_98]
  have hrRet : Runs w p ω (.ret (.reg 98)) s_fin (.returned s4) s_fin 2 :=
    runs_ret_iff.mpr ⟨s4, by simp [Expr.eval, hsfin_98'], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (computeGammaAndLevelsStmt decK decThr witnessDen boundsProc) st
      (.returned s4) s_fin
      (cd + (8 + (2 + (cb1 + (5 + (2 + (cb2 + (5 + (6 + (4 + (2 + (2 + (cgam +
        (3 + (5 + (5 + (5 + (5 + (5 + (7 + (2 + (4 + (2 + (cfin + 2 + 1) + 1) + 1) + 1) + 1) + 1)
          + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s_d, cd, _, hrd,
    runs_seq_iff.mpr (Or.inr ⟨s_c, 8, _, hrc,
    runs_seq_iff.mpr (Or.inr ⟨s_p1, 2, _, hrp1,
    runs_seq_iff.mpr (Or.inr ⟨s_b1, cb1, _, hrb1,
    runs_seq_iff.mpr (Or.inr ⟨s_g1, 5, _, hrg1,
    runs_seq_iff.mpr (Or.inr ⟨s_p2, 2, _, hrp2,
    runs_seq_iff.mpr (Or.inr ⟨s_b2, cb2, _, hrb2,
    runs_seq_iff.mpr (Or.inr ⟨s_g2, 5, _, hrg2,
    runs_seq_iff.mpr (Or.inr ⟨s_gm, 6, _, hrgm,
    runs_seq_iff.mpr (Or.inr ⟨s_gg, 4, _, hrgg,
    runs_seq_iff.mpr (Or.inr ⟨s_a0, 2, _, hra0,
    runs_seq_iff.mpr (Or.inr ⟨s_i0, 2, _, hri0,
    runs_seq_iff.mpr (Or.inr ⟨s_gam, cgam, _, hrgam,
    runs_seq_iff.mpr (Or.inr ⟨sw0, 3, _, hw0,
    runs_seq_iff.mpr (Or.inr ⟨sw1, 5, _, hw1,
    runs_seq_iff.mpr (Or.inr ⟨sw2, 5, _, hw2,
    runs_seq_iff.mpr (Or.inr ⟨sw3, 5, _, hw3,
    runs_seq_iff.mpr (Or.inr ⟨sw4, 5, _, hw4,
    runs_seq_iff.mpr (Or.inr ⟨sw5, 5, _, hw5,
    runs_seq_iff.mpr (Or.inr ⟨sw6, 7, _, hw6,
    runs_seq_iff.mpr (Or.inr ⟨sl0, 2, _, hrl0,
    runs_seq_iff.mpr (Or.inr ⟨sl1, 4, _, hrl1,
    runs_seq_iff.mpr (Or.inr ⟨sl2, 2, _, hrl2,
    runs_seq_iff.mpr (Or.inr ⟨s_fin, cfin, 2, hrfin, hrRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  simp only [Spanner.pathDSBoundsContract, heapContract, argsSize, Expr.size,
    List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hcb1 hcb2
  refine ⟨s_fin, s4, _, rFull, by omega, by omega, ?_, fun i hi => hwriteM i (Nat.zero_le _) hi,
    ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj6 : j < 6 := by simpa using hj
    have hfm := hframeM (heap + j) (Or.inl (by omega))
    rw [hfm]; change m6 (heap + j) = _
    rw [show m6 (heap + j) = m5 (heap + j) from Function.update_of_ne (by omega) _ _]
    interval_cases j
    · simp [m5, m4, m3, m2, m1, m0]
    · simp [m5, m4, m3, m2, m1]
    · simp [m5, m4, m3, m2]
    · simp [m5, m4, m3]
    · simp [m5, m4]
    · simp [m5]
  · rw [hframeM (heap + 6 + d) (Or.inr le_rfl)]
    change m6 (heap + 6 + d) = L
    simp [m6]
  · intro a ha
    rw [hframeM a (Or.inl (by omega))]
    change m6 a = st.mem a
    simp only [m6, m5, m4, m3, m2, m1, m0,
      Function.update_of_ne (show a ≠ heap + 6 + d by omega),
      Function.update_of_ne (show a ≠ heap + 5 by omega),
      Function.update_of_ne (show a ≠ heap + 4 by omega),
      Function.update_of_ne (show a ≠ heap + 3 by omega),
      Function.update_of_ne (show a ≠ heap + 2 by omega),
      Function.update_of_ne (show a ≠ heap + 1 by omega),
      Function.update_of_ne (show a ≠ heap by omega)]
    rw [hsgam_mem]; change s_b2.mem a = st.mem a
    rw [hframe_b2 a (by omega)]; change s_b1.mem a = st.mem a
    rw [hframe_b1 a (by omega)]; change s_d.mem a = st.mem a
    exact congrFun hsd_mem a
  · intro a ha
    rw [hframeM a (Or.inr (by omega))]
    change m6 a = 0
    simp only [m6, m5, m4, m3, m2, m1, m0,
      Function.update_of_ne (show a ≠ heap + 6 + d by omega),
      Function.update_of_ne (show a ≠ heap + 5 by omega),
      Function.update_of_ne (show a ≠ heap + 4 by omega),
      Function.update_of_ne (show a ≠ heap + 3 by omega),
      Function.update_of_ne (show a ≠ heap + 2 by omega),
      Function.update_of_ne (show a ≠ heap + 1 by omega),
      Function.update_of_ne (show a ≠ heap by omega)]
    rw [hsgam_mem]; change s_b2.mem a = 0
    exact hz4 a ha
  · dsimp only [gammaAndLevelsCost, den, cap] at hcd hcb1 hcb2 hcgam hcfin ⊢
    omega

end MinCostFlow.MinRatio

end
