module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCostGoal
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot
public import MinCostFlow.SparseCore.Program.AssemblyFsCostP123

import MinCostFlow.SparseCore.Program.AssemblyFsCostPot
import MinCostFlow.SparseCore.Program.AssemblyFsCostP4Tasks
import MinCostFlow.SparseCore.Program.AssemblyFsCostP4New
import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCParts
import MinCostFlow.SparseCore.Program.AssemblyFirstSplitLists
import MinCostFlow.SparseCore.Program.OutStepJoinModel
import Mathlib.Tactic

/-!
# Cost of the first step of a branch (`AssemblyFsCostTop`)

Proves `asmFirstStep_hCost : AsmFsCostGoal ...` at walk potential `Ψ := walkPot` and explicit
multiplier `asmFsCostMul TS hRoot.mul K.HE.mul capExp` (quadratic in `capExp`, independent of
`depth`, `w`, `M`, `N`, `L`, `k`, `limbMul`), with no further premises.

* `asmFsCostMulP4`, `asmFsCostMul`: explicit multiplier constants.
* `p4_arith_combine`: pure natural-number arithmetic telescoping combining Phases 1–3 (`asmFsCost_p123`),
  Phase 4's post cost bound, the spanner-bank inequality (`asmFsCost_p4_tasks_bounds.1`) scaled by
  `320 * (capExp + 1) * lg - 1`, `p4TaskPay` (`asmFsCost_p4_tasks_bounds.2`), `p4NewPay + walkPot`
  and `Ld`/`Li`/`Lr` (`asmFsCost_p4_new_bounds`), and the deduplicated rotation bound (`p4RotCost`).
* `asmFirstStep_hCost`: top theorem discharging `AsmFsCostGoal`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

/-! ## 1. Multiplier definitions -/

@[expose] public section

/-- Explicit cost multiplier for Phase 4 (linear in `capExp`, `mulE`, `mulR`). -/
def asmFsCostMulP4 (mulE mulR capExp : ℕ) : ℕ :=
  (5980 + 2 * mulE + 3 * mulR) * capExp + 16874

/-- Total explicit cost multiplier for the first step (`AsmFsCostGoal`), quadratic in `capExp` and
independent of `depth`, `w`, `M`, `N`, `L`, `k`, `limbMul`. -/
noncomputable def asmFsCostMul (TS : BundleTourSpec) (mulR mulE capExp : ℕ) : ℕ :=
  asmFsCostMulP123 TS mulR capExp + asmFsCostMulP4 mulE mulR capExp

end

/-! ## 2. Pure helpers -/

private lemma batchEnc_map_delete : ∀ (L : List ℕ) (G : MGraph),
    G.batchEnc (L.map Update.delete) = L.length
  | [], _ => rfl
  | _ :: L, G => by
    simp only [List.map_cons, MGraph.batchEnc, MGraph.updateEnc, batchEnc_map_delete L,
      List.length_cons]
    omega

private lemma outDelSet_card_le_batchEnc {depth : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End) :
    (outDelSet sp tr U ord ord').card ≤
      tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S := by
  rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_map_delete]
  have hL : (outDelList sp tr U ord ord').length = (outDelSet sp tr U ord ord').card := by
    simp [outDelList, outDelSet]
  rw [hL]
  omega

private lemma log_two_mul_add_one_le_capExp {M N vCap eCap capExp s : ℕ} (hs : s ≤ 2 * eCap)
    (h : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    Nat.log 2 (s + 1) + 1 ≤ (capExp + 1) * (Nat.log 2 (M + N + 2) + 1) := by
  have hlg : 2 ≤ Nat.log 2 (M + N + 2) + 1 := log_two_plus_one_ge_two M N
  have hpos : 0 < capExp := capExp_pos_of_caps h
  have hlt1 : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) (M + N + 2)
  have hlt2 : (M + N + 2) ^ capExp < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1)) := by
    have := Nat.pow_lt_pow_left hlt1 (by omega : capExp ≠ 0)
    rwa [← pow_mul, mul_comm (Nat.log 2 (M + N + 2) + 1) capExp] at this
  have hlt3 : s + 1 < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1) + 1) := by
    rw [pow_succ]; omega
  have hlog : Nat.log 2 (s + 1) < capExp * (Nat.log 2 (M + N + 2) + 1) + 1 :=
    Nat.log_lt_of_lt_pow (by omega) hlt3
  nlinarith

private lemma list_map_add_const_sum {α : Type*} (l : List α) (f : α → ℕ) (k : ℕ) :
    (l.map fun x => f x + k).sum = (l.map f).sum + k * l.length := by
  induction l with
  | nil => simp
  | cons a tl ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## 3. Pure arithmetic telescoping for Phases 1–4 -/

private lemma p4_arith_combine
    {mul123 mulE mulR capExp depth lg₁ lg phiMul C_step C_inp : ℕ}
    {c₁ c₂ c₃ c₄ touchedLen : ℕ}
    {bunPhi₁ bunPhi₃ tourPhi₁ tourPhi₃ tourPhi₄ : ℕ}
    {specPhi₀ specPhiMid specPhiAfter wpBefore wpAfter : ℕ}
    {tasksPay newPay hiLo nU lazyESum nNew fDel nLd nLi nLr nOutIns nOutDel nSp nEd mRot vCap
      ordLog : ℕ}
    {W_tot D_tot R_tot UH_tot encB spanCh lazySum : ℕ}
    (hPhiMul : phiMul = 320 * (capExp + 1) * lg)
    (hlg_eq : lg = lg₁ ^ 2) (hlg₁ : 2 ≤ lg₁) (hcap1 : 1 ≤ capExp) (hdepth : depth ≤ lg)
    (hP123 : c₁ + c₂ + c₃ + 340 + 70 * touchedLen + bunPhi₃ + phiMul * specPhiMid + tourPhi₃ ≤
      mul123 * (C_step + C_inp) + bunPhi₁ + phiMul * specPhi₀ + tourPhi₁)
    (hP4 : c₄ + specPhiAfter + tourPhi₄ ≤
      specPhiMid + (tasksPay + 70 * touchedLen) + newPay + 9 * hiLo + 175 * nU +
      130 * lazyESum + 90 * nNew + 105 * fDel + 115 * (nLd + nLi) + 620 +
      (2 * nOutIns * (mulE * ordLog + 45) + 35 * nLi + outBuildCost nLd + outBuildCost nLi +
        60 * nOutIns + 300) +
      p4RotCost nSp nOutIns nU nEd mRot vCap (mulR * ordLog + 60) +
      p4ReembCost (nLr + nOutDel) + 250 + tourPhi₃)
    (hBank : 400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot + specPhiAfter ≤
      specPhiMid + spanCh)
    (hTaskPay : tasksPay ≤
      spanCh + 9745 * encB + 340 * UH_tot + 170 * D_tot + (811 + 207 * depth) * R_tot + 584 * W_tot)
    (hNewPay : newPay + 9 * hiLo + 300 * wpAfter ≤
      300 * wpBefore + 300 * W_tot + (861 + 142 * depth) * lazySum)
    (hLazyE : lazyESum ≤ lazySum) (hNNew : nNew ≤ 2 * nU)
    (hLd : nLd ≤ UH_tot + D_tot + W_tot + nU)
    (hLi : nLi ≤ UH_tot + D_tot + W_tot + 2 * lazySum + 2 * nU + fDel)
    (hLr : nLr ≤ R_tot + lazySum)
    (hfDel : fDel ≤ nU + nSp)
    (hmRot : mRot ≤ 2 * nSp + 2 * nOutIns + 2 * nU + 2 * nEd)
    (hOrdLog : ordLog ≤ capExp * lg₁)
    (hLogLd : Nat.log 2 (nLd + 1) + 1 ≤ capExp * lg₁)
    (hLogLi : Nat.log 2 (nLi + 1) + 1 ≤ capExp * lg₁)
    (hLogReemb : Nat.log 2 (nLr + nOutDel + 1) + 1 ≤ (capExp + 1) * lg₁)
    (hLogRot : Nat.log 2 (min mRot vCap + 1) + 1 ≤ capExp * lg₁)
    (hU_C : nU * lg ≤ C_step) (hEncB_C : encB * lg ≤ C_step)
    (hSpanCh_C : spanCh * lg ≤ C_step) (hLsp_C : nSp * lg ≤ C_step)
    (hLazy_C : lazySum * lg ≤ C_step) (hOutIns_C : nOutIns * lg ≤ C_step)
    (hOutDel_C : nOutDel * lg ≤ C_step)
    (hEd_C : 2 * nEd * lg ≤ C_inp) (h1_C : lg ≤ C_inp) :
    c₁ + c₂ + c₃ + c₄ + 340 + (bunPhi₃ + phiMul * specPhiAfter + 300 * wpAfter) + tourPhi₄ ≤
      (mul123 + asmFsCostMulP4 mulE mulR capExp) * (C_step + C_inp) +
        (bunPhi₁ + phiMul * specPhi₀ + 300 * wpBefore) + tourPhi₁ := by
  have hlg_ge4 : 4 ≤ lg := by rw [hlg_eq, sq]; exact Nat.mul_le_mul hlg₁ hlg₁
  have hlg₁_le_lg : lg₁ ≤ lg := by rw [hlg_eq, sq]; exact Nat.le_mul_of_pos_right lg₁ (by omega)
  have h2lg₁_le_lg : 2 * lg₁ ≤ lg := by rw [hlg_eq, sq]; exact Nat.mul_le_mul_right lg₁ hlg₁
  have hphi_pos : 1 ≤ phiMul := by
    rw [hPhiMul]; exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  set phiM1 := phiMul - 1
  have hphi_split : 1 + phiM1 = phiMul := by omega
  have hphiM1_lg : 319 * (capExp + 1) * lg ≤ phiM1 := by
    have h8 : 8 ≤ (capExp + 1) * lg :=
      Nat.mul_le_mul (show 2 ≤ capExp + 1 by omega) hlg_ge4
    have hring : 320 * (capExp + 1) * lg = 319 * (capExp + 1) * lg + (capExp + 1) * lg := by ring
    omega
  have hphiM1_lg₁ : 638 * (capExp + 1) * lg₁ ≤ phiM1 := by
    have : 319 * (capExp + 1) * (2 * lg₁) ≤ 319 * (capExp + 1) * lg :=
      Nat.mul_le_mul_left _ h2lg₁_le_lg
    have hring : 319 * (capExp + 1) * (2 * lg₁) = 638 * (capExp + 1) * lg₁ := by ring
    omega
  have hLinLg : ∀ a b : ℕ, a + b * lg₁ ≤ (a + b) * lg := fun a b => by
    have h1 : a ≤ a * lg := Nat.le_mul_of_pos_right a (by omega)
    have h2 : b * lg₁ ≤ b * lg := Nat.mul_le_mul_left b hlg₁_le_lg
    have hring : a * lg + b * lg = (a + b) * lg := by ring
    omega
  -- Scale `hBank` by `phiM1`
  have hBank_scaled :
      phiM1 * (400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot) + phiM1 * specPhiAfter ≤
      phiM1 * specPhiMid + phiM1 * spanCh := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_le_mul_left phiM1 hBank
  -- Bound `outBuildCost nLd` and `outBuildCost nLi`
  have hBuildLd : outBuildCost nLd ≤ 380 * capExp * lg₁ * nLd + 380 * capExp * lg₁ + 250 := by
    unfold outBuildCost
    calc 380 * (nLd + 1) * (Nat.log 2 (nLd + 1) + 1) + 250
        ≤ 380 * (nLd + 1) * (capExp * lg₁) + 250 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hLogLd) 250
      _ = 380 * capExp * lg₁ * nLd + 380 * capExp * lg₁ + 250 := by ring
  have hBuildLi : outBuildCost nLi ≤ 380 * capExp * lg₁ * nLi + 380 * capExp * lg₁ + 250 := by
    unfold outBuildCost
    calc 380 * (nLi + 1) * (Nat.log 2 (nLi + 1) + 1) + 250
        ≤ 380 * (nLi + 1) * (capExp * lg₁) + 250 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hLogLi) 250
      _ = 380 * capExp * lg₁ * nLi + 380 * capExp * lg₁ + 250 := by ring
  -- Bound `p4ReembCost (nLr + nOutDel)`
  have hReemb : p4ReembCost (nLr + nOutDel) ≤
      (20 + 280 * (capExp + 1) * lg₁) * (nLr + nOutDel) + 300 := by
    unfold p4ReembCost
    calc 20 * (nLr + nOutDel) +
          280 * (nLr + nOutDel) * (Nat.log 2 (nLr + nOutDel + 1) + 1) + 300
        ≤ 20 * (nLr + nOutDel) + 280 * (nLr + nOutDel) * ((capExp + 1) * lg₁) + 300 :=
          Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hLogReemb) _) 300
      _ = (20 + 280 * (capExp + 1) * lg₁) * (nLr + nOutDel) + 300 := by ring
  -- Expand `Ld`, `Li`, `Lr` bounds into `W_tot`, `D_tot`, `UH_tot`, `R_tot`, and charge terms
  have hLdLi_coeff :
      115 * (nLd + nLi) + 35 * nLi + (380 * capExp * lg₁ * nLd + 380 * capExp * lg₁ * nLi) ≤
      (265 + 760 * capExp * lg₁) * (UH_tot + D_tot + W_tot) +
      (300 + 760 * capExp * lg₁) * lazySum +
      (565 + 1520 * capExp * lg₁) * nU +
      (150 + 380 * capExp * lg₁) * nSp := by
    have hLi' : nLi ≤ UH_tot + D_tot + W_tot + 2 * lazySum + 3 * nU + nSp := by omega
    have h1 := Nat.mul_le_mul_left (115 + 380 * capExp * lg₁) hLd
    have h2 := Nat.mul_le_mul_left (150 + 380 * capExp * lg₁) hLi'
    have hEqL : 115 * (nLd + nLi) + 35 * nLi +
        (380 * capExp * lg₁ * nLd + 380 * capExp * lg₁ * nLi) =
        (115 + 380 * capExp * lg₁) * nLd + (150 + 380 * capExp * lg₁) * nLi := by ring
    have hEqR : (115 + 380 * capExp * lg₁) * (UH_tot + D_tot + W_tot + nU) +
        (150 + 380 * capExp * lg₁) * (UH_tot + D_tot + W_tot + 2 * lazySum + 3 * nU + nSp) =
        (265 + 760 * capExp * lg₁) * (UH_tot + D_tot + W_tot) +
        (300 + 760 * capExp * lg₁) * lazySum +
        (565 + 1520 * capExp * lg₁) * nU +
        (150 + 380 * capExp * lg₁) * nSp := by ring
    rw [hEqL, ← hEqR]
    exact Nat.add_le_add h1 h2
  have hReemb_split :
      (20 + 280 * (capExp + 1) * lg₁) * (nLr + nOutDel) ≤
      (20 + 280 * (capExp + 1) * lg₁) * R_tot +
      (20 + 280 * (capExp + 1) * lg₁) * lazySum +
      (20 + 280 * (capExp + 1) * lg₁) * nOutDel := by
    have h1 := Nat.mul_le_mul_left (20 + 280 * (capExp + 1) * lg₁) (Nat.add_le_add_right hLr nOutDel)
    have hring : (20 + 280 * (capExp + 1) * lg₁) * (R_tot + lazySum + nOutDel) =
        (20 + 280 * (capExp + 1) * lg₁) * R_tot +
        (20 + 280 * (capExp + 1) * lg₁) * lazySum +
        (20 + 280 * (capExp + 1) * lg₁) * nOutDel := by ring
    rwa [hring] at h1
  -- Show all `(W_tot, D_tot, UH_tot, R_tot)` terms fit inside `phiM1 * (400 W + 90 D + 90 R + 240 UH)`
  have hAbsorb :
      (584 + 300) * W_tot + 170 * D_tot + 340 * UH_tot + (811 + 207 * depth) * R_tot +
      (265 + 760 * capExp * lg₁) * (UH_tot + D_tot + W_tot) +
      (20 + 280 * (capExp + 1) * lg₁) * R_tot ≤
      phiM1 * (400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot) := by
    have hCL1 : 1 ≤ (capExp + 1) * lg₁ := Nat.mul_pos (by omega) (by omega)
    have hCL : 1 ≤ (capExp + 1) * lg := Nat.mul_pos (by omega) (by omega)
    have hcL1 : capExp * lg₁ ≤ (capExp + 1) * lg₁ := Nat.mul_le_mul_right lg₁ (by omega)
    have hcW : 584 + 300 + (265 + 760 * capExp * lg₁) ≤ phiM1 * 400 := by
      have h1 : 1149 ≤ 1149 * ((capExp + 1) * lg₁) := Nat.le_mul_of_pos_right 1149 hCL1
      have h2 : 760 * capExp * lg₁ ≤ 760 * ((capExp + 1) * lg₁) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 760 hcL1
      have h3 : 1909 * ((capExp + 1) * lg₁) ≤ 638 * (capExp + 1) * lg₁ * 400 := by
        have hring : 638 * (capExp + 1) * lg₁ * 400 = 255200 * ((capExp + 1) * lg₁) := by ring
        rw [hring]; exact Nat.mul_le_mul_right _ (by omega)
      have h4 := Nat.mul_le_mul_right 400 hphiM1_lg₁
      have hring : 1149 * ((capExp + 1) * lg₁) + 760 * ((capExp + 1) * lg₁) =
          1909 * ((capExp + 1) * lg₁) := by ring
      omega
    have hcD : 170 + (265 + 760 * capExp * lg₁) ≤ phiM1 * 90 := by
      have h1 : 435 ≤ 435 * ((capExp + 1) * lg₁) := Nat.le_mul_of_pos_right 435 hCL1
      have h2 : 760 * capExp * lg₁ ≤ 760 * ((capExp + 1) * lg₁) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 760 hcL1
      have h3 : 1195 * ((capExp + 1) * lg₁) ≤ 638 * (capExp + 1) * lg₁ * 90 := by
        have hring : 638 * (capExp + 1) * lg₁ * 90 = 57420 * ((capExp + 1) * lg₁) := by ring
        rw [hring]; exact Nat.mul_le_mul_right _ (by omega)
      have h4 := Nat.mul_le_mul_right 90 hphiM1_lg₁
      have hring : 435 * ((capExp + 1) * lg₁) + 760 * ((capExp + 1) * lg₁) =
          1195 * ((capExp + 1) * lg₁) := by ring
      omega
    have hcUH : 340 + (265 + 760 * capExp * lg₁) ≤ phiM1 * 240 := by
      have h1 : 605 ≤ 605 * ((capExp + 1) * lg₁) := Nat.le_mul_of_pos_right 605 hCL1
      have h2 : 760 * capExp * lg₁ ≤ 760 * ((capExp + 1) * lg₁) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 760 hcL1
      have h3 : 1365 * ((capExp + 1) * lg₁) ≤ 638 * (capExp + 1) * lg₁ * 240 := by
        have hring : 638 * (capExp + 1) * lg₁ * 240 = 153120 * ((capExp + 1) * lg₁) := by ring
        rw [hring]; exact Nat.mul_le_mul_right _ (by omega)
      have h4 := Nat.mul_le_mul_right 240 hphiM1_lg₁
      have hring : 605 * ((capExp + 1) * lg₁) + 760 * ((capExp + 1) * lg₁) =
          1365 * ((capExp + 1) * lg₁) := by ring
      omega
    have hcR : (811 + 207 * depth) + (20 + 280 * (capExp + 1) * lg₁) ≤ phiM1 * 90 := by
      have h831 : 831 ≤ 831 * ((capExp + 1) * lg) := Nat.le_mul_of_pos_right 831 hCL
      have h207 : 207 * depth ≤ 207 * ((capExp + 1) * lg) :=
        Nat.mul_le_mul_left 207 (le_trans hdepth (Nat.le_mul_of_pos_left lg (by omega)))
      have h280 : 280 * (capExp + 1) * lg₁ ≤ 280 * ((capExp + 1) * lg) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 280 (Nat.mul_le_mul_left _ hlg₁_le_lg)
      have h3 : 1318 * ((capExp + 1) * lg) ≤ 319 * (capExp + 1) * lg * 90 := by
        have hring : 319 * (capExp + 1) * lg * 90 = 28710 * ((capExp + 1) * lg) := by ring
        rw [hring]; exact Nat.mul_le_mul_right _ (by omega)
      have h4 := Nat.mul_le_mul_right 90 hphiM1_lg
      have hring : 831 * ((capExp + 1) * lg) + 207 * ((capExp + 1) * lg) +
          280 * ((capExp + 1) * lg) = 1318 * ((capExp + 1) * lg) := by ring
      omega
    have hL : (584 + 300) * W_tot + 170 * D_tot + 340 * UH_tot + (811 + 207 * depth) * R_tot +
        (265 + 760 * capExp * lg₁) * (UH_tot + D_tot + W_tot) +
        (20 + 280 * (capExp + 1) * lg₁) * R_tot =
        (584 + 300 + (265 + 760 * capExp * lg₁)) * W_tot +
        (170 + (265 + 760 * capExp * lg₁)) * D_tot +
        ((811 + 207 * depth) + (20 + 280 * (capExp + 1) * lg₁)) * R_tot +
        (340 + (265 + 760 * capExp * lg₁)) * UH_tot := by ring
    have hR : phiM1 * (400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot) =
        (phiM1 * 400) * W_tot + (phiM1 * 90) * D_tot + (phiM1 * 90) * R_tot +
        (phiM1 * 240) * UH_tot := by ring
    rw [hL, hR]
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right W_tot hcW)
        (Nat.mul_le_mul_right D_tot hcD)) (Nat.mul_le_mul_right R_tot hcR))
      (Nat.mul_le_mul_right UH_tot hcUH)
  -- Bound `p4RotCost`
  have hRot : p4RotCost nSp nOutIns nU nEd mRot vCap (mulR * ordLog + 60) ≤
      (216 + 2 * mulR * capExp) * C_step +
      (60 + mulR * capExp) * C_inp +
      (600 + 1680 * capExp) * (C_step + C_inp) + 500 := by
    unfold p4RotCost
    have hqc : mulR * ordLog + 60 ≤ (mulR * capExp + 60) * lg₁ := by
      have h1 := Nat.mul_le_mul_left mulR hOrdLog
      have h2 : 60 ≤ 60 * lg₁ := Nat.le_mul_of_pos_right 60 (by omega)
      have hring : mulR * (capExp * lg₁) + 60 * lg₁ = (mulR * capExp + 60) * lg₁ := by ring
      omega
    have h48 : 48 * (nSp + nOutIns) ≤ 96 * C_step := by
      have h1 : nSp ≤ C_step := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hLsp_C
      have h2 : nOutIns ≤ C_step := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hOutIns_C
      omega
    have h2U : 2 * nU * (mulR * ordLog + 60) ≤ (2 * mulR * capExp + 120) * C_step := by
      calc 2 * nU * (mulR * ordLog + 60)
          ≤ 2 * nU * ((mulR * capExp + 60) * lg₁) := Nat.mul_le_mul_left _ hqc
        _ ≤ 2 * nU * ((mulR * capExp + 60) * lg) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlg₁_le_lg)
        _ = (2 * mulR * capExp + 120) * (nU * lg) := by ring
        _ ≤ (2 * mulR * capExp + 120) * C_step := Nat.mul_le_mul_left _ hU_C
    have h2Ed : 2 * nEd * (mulR * ordLog + 60) ≤ (mulR * capExp + 60) * C_inp := by
      calc 2 * nEd * (mulR * ordLog + 60)
          ≤ 2 * nEd * ((mulR * capExp + 60) * lg₁) := Nat.mul_le_mul_left _ hqc
        _ ≤ 2 * nEd * ((mulR * capExp + 60) * lg) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlg₁_le_lg)
        _ = (mulR * capExp + 60) * (2 * nEd * lg) := by ring
        _ ≤ (mulR * capExp + 60) * C_inp := Nat.mul_le_mul_left _ hEd_C
    have hm_lg : mRot * lg₁ ≤ 6 * (C_step + C_inp) := by
      calc mRot * lg₁ ≤ mRot * lg := Nat.mul_le_mul_left _ hlg₁_le_lg
        _ ≤ (2 * nSp + 2 * nOutIns + 2 * nU + 2 * nEd) * lg := Nat.mul_le_mul_right _ hmRot
        _ = 2 * (nSp * lg) + 2 * (nOutIns * lg) + 2 * (nU * lg) + 2 * nEd * lg := by ring
        _ ≤ 2 * C_step + 2 * C_step + 2 * C_step + C_inp := by omega
        _ ≤ 6 * (C_step + C_inp) := by omega
    have hsort : 100 * mRot + 280 * min mRot vCap * (Nat.log 2 (min mRot vCap + 1) + 1) ≤
        (600 + 1680 * capExp) * (C_step + C_inp) := by
      have hmin : min mRot vCap ≤ mRot := Nat.min_le_left _ _
      have hs1 : 280 * min mRot vCap * (Nat.log 2 (min mRot vCap + 1) + 1) ≤
          280 * capExp * (mRot * lg₁) := by
        calc 280 * min mRot vCap * (Nat.log 2 (min mRot vCap + 1) + 1)
            ≤ 280 * mRot * (capExp * lg₁) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left 280 hmin) hLogRot
          _ = 280 * capExp * (mRot * lg₁) := by ring
      have hs0 : 100 * mRot ≤ 100 * (mRot * lg₁) := by
        have := Nat.le_mul_of_pos_right mRot (by omega : 0 < lg₁)
        exact Nat.mul_le_mul_left 100 this
      calc 100 * mRot + 280 * min mRot vCap * (Nat.log 2 (min mRot vCap + 1) + 1)
          ≤ 100 * (mRot * lg₁) + 280 * capExp * (mRot * lg₁) := Nat.add_le_add hs0 hs1
        _ = (100 + 280 * capExp) * (mRot * lg₁) := by ring
        _ ≤ (100 + 280 * capExp) * (6 * (C_step + C_inp)) := Nat.mul_le_mul_left _ hm_lg
        _ = (600 + 1680 * capExp) * (C_step + C_inp) := by ring
    have hring : 96 * C_step + (2 * mulR * capExp + 120) * C_step =
        (216 + 2 * mulR * capExp) * C_step := by ring
    have hring2 : (mulR * capExp + 60) * C_inp = (60 + mulR * capExp) * C_inp := by ring
    omega
  -- Bound every remaining charge term
  have hT_spanCh : (1 + phiM1) * spanCh ≤ (320 * capExp + 320) * C_step := by
    rw [hphi_split, hPhiMul]
    calc 320 * (capExp + 1) * lg * spanCh
        = (320 * capExp + 320) * (spanCh * lg) := by ring
      _ ≤ (320 * capExp + 320) * C_step := Nat.mul_le_mul_left _ hSpanCh_C
  have hT_encB : 9745 * encB ≤ 9745 * C_step :=
    le_trans (Nat.mul_le_mul_left 9745 (Nat.le_mul_of_pos_right _ (by omega)))
      (Nat.mul_le_mul_left 9745 hEncB_C)
  have hT_lazy : (861 + 142 * depth) * lazySum + 130 * lazyESum +
      (300 + 760 * capExp * lg₁) * lazySum + (20 + 280 * (capExp + 1) * lg₁) * lazySum ≤
      (1733 + 1040 * capExp) * C_step := by
    have h1 : (861 + 142 * depth) * lazySum ≤ 1003 * (lazySum * lg) := by
      have ha : 861 ≤ 861 * lg := Nat.le_mul_of_pos_right 861 (by omega)
      have hb : 142 * depth ≤ 142 * lg := Nat.mul_le_mul_left 142 hdepth
      have : 861 + 142 * depth ≤ 1003 * lg := by omega
      calc (861 + 142 * depth) * lazySum ≤ (1003 * lg) * lazySum := Nat.mul_le_mul_right _ this
        _ = 1003 * (lazySum * lg) := by ring
    have h2 : 130 * lazyESum ≤ 130 * (lazySum * lg) :=
      le_trans (Nat.mul_le_mul_left 130 hLazyE)
        (Nat.mul_le_mul_left 130 (Nat.le_mul_of_pos_right _ (by omega)))
    have h3 : (300 + 760 * capExp * lg₁) * lazySum ≤ (300 + 760 * capExp) * (lazySum * lg) := by
      have : 300 + 760 * capExp * lg₁ ≤ (300 + 760 * capExp) * lg := hLinLg 300 (760 * capExp)
      calc (300 + 760 * capExp * lg₁) * lazySum
          ≤ ((300 + 760 * capExp) * lg) * lazySum := Nat.mul_le_mul_right _ this
        _ = (300 + 760 * capExp) * (lazySum * lg) := by ring
    have h4 : (20 + 280 * (capExp + 1) * lg₁) * lazySum ≤
        (300 + 280 * capExp) * (lazySum * lg) := by
      have : 20 + 280 * (capExp + 1) * lg₁ ≤ (300 + 280 * capExp) * lg := by
        have h := hLinLg 20 (280 * (capExp + 1))
        have hring : (20 + 280 * (capExp + 1)) * lg = (300 + 280 * capExp) * lg := by ring
        rwa [hring] at h
      calc (20 + 280 * (capExp + 1) * lg₁) * lazySum
          ≤ ((300 + 280 * capExp) * lg) * lazySum := Nat.mul_le_mul_right _ this
        _ = (300 + 280 * capExp) * (lazySum * lg) := by ring
    calc _ ≤ 1003 * (lazySum * lg) + 130 * (lazySum * lg) +
            (300 + 760 * capExp) * (lazySum * lg) + (300 + 280 * capExp) * (lazySum * lg) := by
          omega
      _ = (1733 + 1040 * capExp) * (lazySum * lg) := by ring
      _ ≤ (1733 + 1040 * capExp) * C_step := Nat.mul_le_mul_left _ hLazy_C
  have hT_U : 175 * nU + 90 * nNew + 105 * nU + (565 + 1520 * capExp * lg₁) * nU ≤
      (1025 + 1520 * capExp) * C_step := by
    have h1 : 175 * nU + 90 * nNew + 105 * nU + (565 + 1520 * capExp * lg₁) * nU ≤
        (1025 + 1520 * capExp * lg₁) * nU := by
      have : 90 * nNew ≤ 180 * nU := by omega
      have hring : 175 * nU + 180 * nU + 105 * nU + (565 + 1520 * capExp * lg₁) * nU =
          (1025 + 1520 * capExp * lg₁) * nU := by ring
      omega
    have h2 : 1025 + 1520 * capExp * lg₁ ≤ (1025 + 1520 * capExp) * lg :=
      hLinLg 1025 (1520 * capExp)
    calc _ ≤ (1025 + 1520 * capExp * lg₁) * nU := h1
      _ ≤ ((1025 + 1520 * capExp) * lg) * nU := Nat.mul_le_mul_right _ h2
      _ = (1025 + 1520 * capExp) * (nU * lg) := by ring
      _ ≤ (1025 + 1520 * capExp) * C_step := Nat.mul_le_mul_left _ hU_C
  have hT_Lsp : 105 * nSp + (150 + 380 * capExp * lg₁) * nSp ≤ (255 + 380 * capExp) * C_step := by
    have h1 : 105 * nSp + (150 + 380 * capExp * lg₁) * nSp =
        (255 + 380 * capExp * lg₁) * nSp := by ring
    have h2 : 255 + 380 * capExp * lg₁ ≤ (255 + 380 * capExp) * lg :=
      hLinLg 255 (380 * capExp)
    rw [h1]
    calc (255 + 380 * capExp * lg₁) * nSp
        ≤ ((255 + 380 * capExp) * lg) * nSp := Nat.mul_le_mul_right _ h2
      _ = (255 + 380 * capExp) * (nSp * lg) := by ring
      _ ≤ (255 + 380 * capExp) * C_step := Nat.mul_le_mul_left _ hLsp_C
  have hT_outIns : 2 * nOutIns * (mulE * ordLog + 45) + 60 * nOutIns ≤
      (150 + 2 * mulE * capExp) * C_step := by
    have h1 : 2 * nOutIns * (mulE * ordLog + 45) + 60 * nOutIns ≤
        (150 + 2 * mulE * capExp) * (nOutIns * lg) := by
      have hord : mulE * ordLog ≤ mulE * capExp * lg := by
        calc mulE * ordLog ≤ mulE * (capExp * lg₁) := Nat.mul_le_mul_left _ hOrdLog
          _ ≤ mulE * (capExp * lg) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlg₁_le_lg)
          _ = mulE * capExp * lg := by ring
      have h150 : 150 ≤ 150 * lg := Nat.le_mul_of_pos_right 150 (by omega)
      have hc : 2 * (mulE * ordLog + 45) + 60 ≤ (150 + 2 * mulE * capExp) * lg := by
        have hring : (150 + 2 * mulE * capExp) * lg = 150 * lg + 2 * (mulE * capExp * lg) := by
          ring
        omega
      calc 2 * nOutIns * (mulE * ordLog + 45) + 60 * nOutIns
          = nOutIns * (2 * (mulE * ordLog + 45) + 60) := by ring
        _ ≤ nOutIns * ((150 + 2 * mulE * capExp) * lg) := Nat.mul_le_mul_left _ hc
        _ = (150 + 2 * mulE * capExp) * (nOutIns * lg) := by ring
    exact le_trans h1 (Nat.mul_le_mul_left _ hOutIns_C)
  have hT_outDel : (20 + 280 * (capExp + 1) * lg₁) * nOutDel ≤ (300 + 280 * capExp) * C_step := by
    have h1 : 20 + 280 * (capExp + 1) * lg₁ ≤ (300 + 280 * capExp) * lg := by
      have h := hLinLg 20 (280 * (capExp + 1))
      have hring : (20 + 280 * (capExp + 1)) * lg = (300 + 280 * capExp) * lg := by ring
      rwa [hring] at h
    calc (20 + 280 * (capExp + 1) * lg₁) * nOutDel
        ≤ ((300 + 280 * capExp) * lg) * nOutDel := Nat.mul_le_mul_right _ h1
      _ = (300 + 280 * capExp) * (nOutDel * lg) := by ring
      _ ≤ (300 + 280 * capExp) * C_step := Nat.mul_le_mul_left _ hOutDel_C
  have hT_const : 620 + 300 + 250 + 250 + 300 + 250 + 500 +
      (380 * capExp * lg₁ + 380 * capExp * lg₁) ≤ (2470 + 760 * capExp) * C_inp := by
    have h1 : 2470 + 760 * capExp * lg₁ ≤ (2470 + 760 * capExp) * lg :=
      hLinLg 2470 (760 * capExp)
    have hring : 620 + 300 + 250 + 250 + 300 + 250 + 500 +
        (380 * capExp * lg₁ + 380 * capExp * lg₁) = 2470 + 760 * capExp * lg₁ := by ring
    rw [hring]
    exact le_trans h1 (Nat.mul_le_mul_left _ h1_C)
  -- Assemble all Phase 4 charge terms into `asmFsCostMulP4 mulE mulR capExp * (C_step + C_inp)`
  have hP4_charge :
      (320 * capExp + 320) * C_step + 9745 * C_step + (1733 + 1040 * capExp) * C_step +
      (1025 + 1520 * capExp) * C_step + (255 + 380 * capExp) * C_step +
      (150 + 2 * mulE * capExp) * C_step + (300 + 280 * capExp) * C_step +
      (216 + 2 * mulR * capExp) * C_step +
      ((60 + mulR * capExp) * C_inp + (2470 + 760 * capExp) * C_inp) +
      (600 + 1680 * capExp) * (C_step + C_inp) ≤
      asmFsCostMulP4 mulE mulR capExp * (C_step + C_inp) := by
    unfold asmFsCostMulP4
    have hS : (320 * capExp + 320) * C_step + 9745 * C_step + (1733 + 1040 * capExp) * C_step +
        (1025 + 1520 * capExp) * C_step + (255 + 380 * capExp) * C_step +
        (150 + 2 * mulE * capExp) * C_step + (300 + 280 * capExp) * C_step +
        (216 + 2 * mulR * capExp) * C_step =
        ((3540 + 2 * mulE + 2 * mulR) * capExp + 13744) * C_step := by ring
    have hI : (60 + mulR * capExp) * C_inp + (2470 + 760 * capExp) * C_inp =
        ((760 + mulR) * capExp + 2530) * C_inp := by ring
    rw [hS, hI]
    have h1 := Nat.mul_le_mul_left ((3540 + 2 * mulE + 2 * mulR) * capExp + 13744)
      (Nat.le_add_right C_step C_inp)
    have h2 := Nat.mul_le_mul_left ((760 + mulR) * capExp + 2530)
      (Nat.le_add_left C_inp C_step)
    have hring : ((3540 + 2 * mulE + 2 * mulR) * capExp + 13744) * (C_step + C_inp) +
        ((760 + mulR) * capExp + 2530) * (C_step + C_inp) +
        (600 + 1680 * capExp) * (C_step + C_inp) =
        ((5980 + 2 * mulE + 3 * mulR) * capExp + 16874) * (C_step + C_inp) := by ring
    omega
  -- Final telescoping
  have hPhiAfter : specPhiAfter + phiM1 * specPhiAfter = phiMul * specPhiAfter := by
    calc specPhiAfter + phiM1 * specPhiAfter = (1 + phiM1) * specPhiAfter := by ring
      _ = phiMul * specPhiAfter := by rw [hphi_split]
  have hPhiMid : specPhiMid + phiM1 * specPhiMid = phiMul * specPhiMid := by
    calc specPhiMid + phiM1 * specPhiMid = (1 + phiM1) * specPhiMid := by ring
      _ = phiMul * specPhiMid := by rw [hphi_split]
  have hSpanSum : spanCh + phiM1 * spanCh = (1 + phiM1) * spanCh := by ring
  have hMulSplit : (mul123 + asmFsCostMulP4 mulE mulR capExp) * (C_step + C_inp) =
      mul123 * (C_step + C_inp) + asmFsCostMulP4 mulE mulR capExp * (C_step + C_inp) := by ring
  have hfDel_mul : 105 * fDel ≤ 105 * nU + 105 * nSp := by omega
  omega

/-! ## 4. Main theorem (`AsmFsCostGoal`) -/

public section

set_option maxHeartbeats 1600000 in
/-- **The cost goal of the first step (`AsmFsCostGoal`)**, proved at `Ψ := walkPot` and explicit
multiplier `asmFsCostMul TS hRoot.mul K.HE.mul capExp`, with no further premises. -/
theorem asmFirstStep_hCost {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ} :
    AsmFsCostGoal TS impl P L capExp limbMul wordExp w (walkPot (L := depth)) fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K
      (asmFsCostMul TS hRoot.mul K.HE.mul capExp) space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ₄ xTour hTx' yEmb sTour
  obtain ⟨tx₀, hTx₀⟩ : ∃ tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ, HEq tx₀ A.x.xTour := by
    obtain ⟨⟨_, tx₀, hTx₀, _, _⟩, _⟩ := hQ₄
    exact ⟨tx₀, hTx₀⟩
  -- Unpack potentials, Phases 1–3, and Phase 4 bounds
  have hPhi := asmFsCost_phi_eq hA hQ₄ hTx₀ hTx' yEmb sTour
  have hP123 := asmFsCost_p123 hA hQ₄.1 hTx₀
  have hP4T := asmFsCost_p4_tasks_bounds hA hQ₄
  have hP4N := asmFsCost_p4_new_bounds hA hQ₄
  -- Extract parameters and input bounds from `hA` and `hQ₄`
  set sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
  set ord' := applyOrdEdits A.ord A.ed
  set info := stepBundleTree sp A.tr A.U A.ord ord'
  set tr' := info.state
  set P_sp := asmBrSP impl w depth y'
  set tasks := p4TasksOf st₃.mem (outDescPtr + 1) touched.length
  set lg₁ := Nat.log 2 (A.M + A.N + 2) + 1
  set lg := bundleLogFactor A.M A.N
  set C_step := branchStepCharge sp A.tr A.U A.ord ord'
  set C_inp := (A.words + A.editWords + 1) * lg
  have hM0 : A.tr.m₀ = A.M := hA.1
  have hN0 : A.tr.n₀ = A.N := hA.2.1
  have hdepth_le : depth ≤ lg := hA.2.2.2.1
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hv5 : A.x.xRest.vCap5 = A.x.vCap := hR.2.1
  have he5 : A.x.xRest.eCap5 = A.x.eCap := hR.2.2.1
  have hCap : A.x.vCap + A.x.eCap + 2 ≤ (A.M + A.N + 2) ^ capExp := by
    rw [← hM0, ← hN0]; exact hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOutRep : (outGraphRep A.x.vCap A.x.eCap).rep A.x.outH A.tr.S_cur A.x.gOut A.mem :=
    hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSide := hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMod := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨C_lsst, ℓ₀, hI, -, -⟩ := hMod.2.2.2.2.2.2.1
  have hU : A.tr.cs.G.BatchIsValid A.U := hA.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEdAt : OrdEditsAt A.mem A.edits A.ed A.editWords :=
    hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hExact : A.c.Exact A.tr.cs.lsf (compLSFBatch A.tr.cs A.U).lsf :=
    hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- Extract Phase 4 cost and `Ld`/`Li`/`Lr` cap bounds
  have hP4 := hQ₄.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLd_cap, hLi_cap,
    hLr_cap, -, -, -, -, -, -, -, -, -, -, -, -, -, hP4_cost, -⟩ := hP4
  -- Log and cap bounds
  have hlg₁_ge : 2 ≤ lg₁ := log_two_plus_one_ge_two A.M A.N
  have hcap1 : 1 ≤ capExp := capExp_pos_of_caps hCap
  have hOrdLog : ordStoreLog A.x.xRest.eCap5 ≤ capExp * lg₁ := by
    rw [he5]; exact ordStoreLog_le_capExp hCap
  have hLogLd : Nat.log 2 (Ld.length + 1) + 1 ≤ capExp * lg₁ :=
    log_succ_le_capExp (by rw [he5] at hLd_cap; omega) hCap
  have hLogLi : Nat.log 2 (Li.length + 1) + 1 ≤ capExp * lg₁ :=
    log_succ_le_capExp (by rw [he5] at hLi_cap; omega) hCap
  have hScur_card : A.tr.S_cur.E.card ≤ A.x.eCap := by
    have hsub : A.tr.S_cur.E ⊆ Finset.range A.x.eCap := fun e he =>
      Finset.mem_range.mpr (hOutRep.2.2.2.2.1 e he)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hOutDel_le_eCap : (outDelSet sp A.tr A.U A.ord ord').card ≤ A.x.eCap := by
    have hsub : outDelSet sp A.tr A.U A.ord ord' ⊆ A.tr.S_cur.E := fun e he =>
      (mem_outDelSet_iff sp A.tr A.U A.ord ord' e).mp he |>.1
    exact (Finset.card_le_card hsub).trans hScur_card
  have hLogReemb : Nat.log 2 (Lr.length + (outDelSet sp A.tr A.U A.ord ord').card + 1) + 1 ≤
      (capExp + 1) * lg₁ :=
    log_two_mul_add_one_le_capExp (by rw [he5] at hLr_cap; omega) hCap
  have hLogRot : ∀ m, Nat.log 2 (min m A.x.xRest.vCap5 + 1) + 1 ≤ capExp * lg₁ := fun m =>
    log_succ_le_capExp (by rw [hv5]; have := Nat.min_le_right m A.x.vCap; omega) hCap
  -- Charge shortcuts
  have hU_C : A.U.length * lg ≤ C_step := by
    show A.U.length * lg ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    exact Nat.mul_le_mul_right lg (by omega)
  have hBkts : tr'.activeBuckets = A.tr.activeBuckets := rfl
  have hEncB_C : ((activePairs tr').sum fun q => (A.tr.dyn q).G.batchEnc (info.U_B q)) * lg ≤
      C_step := by
    show _ ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    rw [sum_activePairs_eq tr' (fun q => (A.tr.dyn q).G.batchEnc (info.U_B q)), hBkts]
    exact Nat.mul_le_mul_right lg (by dsimp only [tr', info]; omega)
  have hEncS_C : A.tr.S_cur.batchEnc info.U_S * lg ≤ C_step := by
    show _ ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    exact Nat.mul_le_mul_right lg (by dsimp only [info]; omega)
  have hSpanCh_C : ((activePairs tr').sum fun q =>
      spanBatchChargeWith A.tr.spanConst A.tr.spanParams depth
        ((A.tr.initBunG q).n + A.tr.splitBound) (A.tr.initBunG q) (A.tr.dyn q).G (info.U_B q)) *
        lg ≤ C_step := by
    show _ ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    rw [sum_activePairs_eq tr' (fun q =>
      spanBatchChargeWith A.tr.spanConst A.tr.spanParams depth
        ((A.tr.initBunG q).n + A.tr.splitBound) (A.tr.initBunG q) (A.tr.dyn q).G (info.U_B q)),
      hBkts]
    exact Nat.mul_le_mul_right lg (by dsimp only [tr', info]; omega)
  have hLsp_le_enc : (canonSplitList A.tr.cs A.U).length ≤ A.tr.S_cur.batchEnc info.U_S :=
    asmFirstCanonSplitList_length_le_batchEnc sp A.tr A.U A.ord ord'
  have hLsp_C : (canonSplitList A.tr.cs A.U).length * lg ≤ C_step :=
    le_trans (Nat.mul_le_mul_right lg hLsp_le_enc) hEncS_C
  have hLazy_C : (info.newlyActive.sum fun C => A.tr.lazyMachInitCost C) * lg ≤ C_step := by
    show _ ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    exact Nat.mul_le_mul_right lg (by dsimp only [info]; omega)
  have hOutIns_C : (outInsSet sp A.tr A.U A.ord ord').card * lg ≤ C_step :=
    le_trans (Nat.mul_le_mul_right lg (outInsSet_card_le_batchEnc sp A.tr A.U A.ord ord')) hEncS_C
  have hOutDel_C : (outDelSet sp A.tr A.U A.ord ord').card * lg ≤ C_step :=
    le_trans (Nat.mul_le_mul_right lg (outDelSet_card_le_batchEnc sp A.tr A.U A.ord ord')) hEncS_C
  have hEd_C : 2 * A.ed.length * lg ≤ C_inp := by
    have h2ed := ordEditsAt_two_len hEdAt
    exact Nat.mul_le_mul_right lg (by omega)
  have h1_C : lg ≤ C_inp := Nat.le_mul_of_pos_left lg (by omega)
  have hfDel_le : A.c.fDel.length ≤ A.U.length + (canonSplitList A.tr.cs A.U).length :=
    fDel_length_le hI hU hExact
  have hmRot_le : (p4RotRaw (canonSplitList A.tr.cs A.U)
      ((outInsSet sp A.tr A.U A.ord ord').sort (· ≤ ·))
      (fun e => (compLSFBatch A.tr.cs A.U).RF.root ((compLSFBatch A.tr.cs A.U).G.tail e))
      (fun e => (compLSFBatch A.tr.cs A.U).RF.root ((compLSFBatch A.tr.cs A.U).G.head e))
      (compLSFBatch A.tr.cs A.U).RF.root A.U A.ed).length ≤
      2 * (canonSplitList A.tr.cs A.U).length + 2 * (outInsSet sp A.tr A.U A.ord ord').card +
      2 * A.U.length + 2 * A.ed.length := by
    have h := p4RotRaw_length_le (canonSplitList A.tr.cs A.U)
      ((outInsSet sp A.tr A.U A.ord ord').sort (· ≤ ·))
      (fun e => (compLSFBatch A.tr.cs A.U).RF.root ((compLSFBatch A.tr.cs A.U).G.tail e))
      (fun e => (compLSFBatch A.tr.cs A.U).RF.root ((compLSFBatch A.tr.cs A.U).G.head e))
      (compLSFBatch A.tr.cs A.U).RF.root A.U A.ed
    rwa [Finset.length_sort] at h
  have hTasks70 : (tasks.map fun t => p4TaskPay P_sp y'.spanS st₃.mem t + 70).sum =
      (tasks.map fun t => p4TaskPay P_sp y'.spanS st₃.mem t).sum + 70 * touched.length := by
    rw [list_map_add_const_sum, p4TasksOf_length]
  rw [hTasks70] at hP4_cost
  -- Apply pure arithmetic combiner
  have hComb := p4_arith_combine (mul123 := asmFsCostMulP123 TS hRoot.mul capExp)
    (mulE := K.HE.mul) (mulR := hRoot.mul) (capExp := capExp) (depth := depth)
    (lg₁ := lg₁) (lg := lg) (phiMul := 320 * (capExp + 1) * lg)
    (C_step := C_step) (C_inp := C_inp)
    rfl rfl hlg₁_ge hcap1 hdepth_le
    hP123 hP4_cost hP4T.1 hP4T.2 hP4N.1 hP4N.2.1 hP4N.2.2.1
    hP4N.2.2.2.1 hP4N.2.2.2.2.1 hP4N.2.2.2.2.2
    hfDel_le hmRot_le hOrdLog hLogLd hLogLi hLogReemb (hLogRot _)
    hU_C hEncB_C hSpanCh_C hLsp_C hLazy_C hOutIns_C hOutDel_C hEd_C h1_C
  -- Rewrite into `AsmFsCostAt` via `asmFsCost_phi_eq`
  unfold AsmFsCostAt asmFsCostMul
  dsimp only at hPhi ⊢
  rw [hPhi.1, hPhi.2]
  exact (show ∀ cost T t4 B3 M t1 B1 : ℕ,
      cost + B3 + t4 ≤ M + B1 + t1 →
      cost + (T + t4 + B3) ≤ M + (T + t1 + B1) by intro _ _ _ _ _ _ _ h; omega)
    _ _ _ _ _ _ _ hComb

end

end MinCostFlow.SparseCore.Program
