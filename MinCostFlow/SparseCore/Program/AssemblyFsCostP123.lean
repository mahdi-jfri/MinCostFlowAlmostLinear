module

public import MinCostFlow.SparseCore.Program.AssemblyFsCostPot
public import MinCostFlow.SparseCore.Program.AssemblyFsCostLog

import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue3
import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Proof
import MinCostFlow.SparseCore.Program.AssemblyFirstSplitLists
import MinCostFlow.SparseCore.Program.OutStepJoinModel
import Mathlib.Tactic

/-!
# Cost bounds for Phases 1, 2, 3, and the driver (`AssemblyFsCostP123`)

Bounds every term of `c₁`, `c₂`, `c₃`, and the driver overhead `340` against a constant multiple
(depending only on `TS.mul`, `hRoot.mul`, `capExp`, and fixed constants) of
`branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * bundleLogFactor A.M A.N`,
with the intermediate bundle-table and tour potentials at `st₂` cancelled.

* `asmFsCost_p1_driver`, `asmFsCost_p2`, `asmFsCost_p3`, and `asmFsCost_p123`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

/-! ## 1. Multiplier constants -/

@[expose] public section

/-- Multiplier for Phase 1 + driver overhead. -/
def asmFsCostMulP1 : ℕ := 460

/-- Multiplier for Phase 2 (depends only on `TS.mul`, `rMul`, `capExp`). -/
def asmFsCostMulP2 (TS : BundleTourSpec) (rMul capExp : ℕ) : ℕ :=
  2 * capExp * newActCostMul TS rMul + 320 * (capExp + 1)

/-- Multiplier for Phase 3 (quadratic in `capExp`, independent of `depth, w, M, N, L, k, limbMul`). -/
noncomputable def asmFsCostMulP3 (capExp : ℕ) : ℕ :=
  (6 * tourBundleSpec.mul + 710) * capExp + 2490 + bunPhiMul +
    tourBlockStepMul * capExp * (4 * capExp + 6) +
    2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) + 920

/-- Combined multiplier for Phases 1, 2, 3, and the driver. -/
noncomputable def asmFsCostMulP123 (TS : BundleTourSpec) (rMul capExp : ℕ) : ℕ :=
  asmFsCostMulP1 + asmFsCostMulP2 TS rMul capExp + asmFsCostMulP3 capExp

end

/-! ## 2. Phase 1 + driver, Phase 2, and Phase 3 cost bounds -/

public section

/-- **Phase 1 + driver cost bound**. -/
theorem asmFsCost_p1_driver {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    (hQ₃ : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
      splitPtr outDescPtr mk' Mset Ys touched) :
    c₁ + 340 ≤
      asmFsCostMulP1 * ((A.words + A.editWords + 1) * bundleLogFactor A.M A.N) := by
  have hc1 : c₁ ≤ 245 * A.words + 120 := hQ₃.1.2.2.2
  have hlg : 4 ≤ bundleLogFactor A.M A.N := bundleLogFactor_ge_four A.M A.N
  unfold asmFsCostMulP1
  nlinarith

set_option maxHeartbeats 800000 in
/-- **Phase 2 cost bound** (with `bucketPhi` rewritten to `specPhi` and `y'.lgFac = lg`). -/
theorem asmFsCost_p2 {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ₃ : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
      splitPtr outDescPtr mk' Mset Ys touched)
    {tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} (hTx₀ : HEq tx₀ A.x.xTour) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
    let ord' := applyOrdEdits A.ord A.ed
    let P_sp := asmBrSP impl w depth y'
    let lg := bundleLogFactor A.M A.N
    c₂ + (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₂.mem +
        320 * (capExp + 1) * lg * specPhi P_sp y'.spanS +
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx1 st₂.mem ≤
      asmFsCostMulP2 TS hRoot.mul capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      (scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
        A.x.xRest.bunH A.x.xRest.xBun st₁.mem +
      320 * (capExp + 1) * lg * specPhi P_sp A.x.xRest.spanS +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem := by
  intro sp ord' P_sp lg
  obtain ⟨_, tx₀', hTx₀', hP2, _⟩ := hQ₃
  have htx_eq : tx₀' = tx₀ := eq_of_heq (hTx₀'.trans hTx₀.symm)
  subst tx₀'
  have hM0 : A.tr.m₀ = A.M := hA.1
  have hN0 : A.tr.n₀ = A.N := hA.2.1
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hU : A.tr.cs.G.BatchIsValid A.U := hA.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he5 : A.x.xRest.eCap5 = A.x.eCap := hR.2.2.1
  have hCap : A.x.vCap + A.x.eCap + 2 ≤ (A.M + A.N + 2) ^ capExp := by
    rw [← hM0, ← hN0]; exact hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSide := hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSpanRep0 := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMaps := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMod := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLg0 : A.x.xRest.lgFac = lg := by
    change A.x.xRest.lgFac = bundleLogFactor A.M A.N
    rw [← hM0, ← hN0]
    exact hMod.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLSF := hMod.2.2.2.2.2.2.1
  obtain ⟨C_lsst, ℓ₀, hI, _⟩ := hLSF
  have hCross : AsmFirstCrossInactiveInv A.tr :=
    hMod.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCnd : A.x.xRest.comps.Nodup := hMaps.2.2.2.2.1
  have hCiff : ∀ C, C ∈ A.x.xRest.comps ↔ C ∈ components A.tr.cs.G₀ := hMaps.2.2.2.2.2.1
  obtain ⟨-, -, hNewSet, hNewLen, -, -⟩ :=
    asmFirstStep_newComps_ok (cmpMap₀ := fun v => A.mem (A.x.xRest.cmpH + v)) hI hU hCnd hCiff
      (asmSdMaps_cmp_ok hMaps) hCross
  have hsb : y'.splitB = A.x.xRest.splitB := hP2.2.2.2.2.2.2.2.2.2.1
  have hspV : y'.spV = A.x.xRest.spV := hP2.2.2.2.2.2.2.2.2.2.2.1
  have hspE : y'.spE = A.x.xRest.spE := hP2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmMax : y'.mMax = A.x.xRest.mMax := hP2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlg' : y'.lgFac = A.x.xRest.lgFac :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSpanRep2 := hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP2_cost :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hSP0 : asmBrSP impl w depth A.x.xRest = P_sp := by
    simp only [P_sp, asmBrSP, hsb, hspV, hspE, hmMax]
  have hS0 : bucketPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.xSpan =
      specPhi P_sp A.x.xRest.spanS := by
    have h : bucketPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.xSpan =
        specPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.spanS := bucketPhi_eq_specPhi hSpanRep0
    exact h.trans (congrArg (fun Q => specPhi Q A.x.xRest.spanS) hSP0)
  have hS2 : bucketPhi P_sp y'.xSpan = specPhi P_sp y'.spanS := bucketPhi_eq_specPhi hSpanRep2
  have hlg_eq : y'.lgFac = lg := hlg'.trans hLg0
  rw [hS2, hS0, hlg_eq, hLg0] at hP2_cost
  have hNewly : (A.newComps A.x.xRest.cmpH A.x.xRest.comps |>.map
      fun q => A.x.xRest.comps.getD q.1 ∅).toFinset =
      (stepBundleTree sp A.tr A.U A.ord ord').newlyActive := hNewSet
  have hNCLen : (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length ≤ 2 * A.U.length := hNewLen
  have hOrdLog : ordStoreLog A.x.xRest.eCap5 ≤ capExp * lg := by
    rw [he5]
    have h1 := ordStoreLog_le_capExp hCap
    have h2 : Nat.log 2 (A.M + A.N + 2) + 1 ≤ lg := by
      change Nat.log 2 (A.M + A.N + 2) + 1 ≤ (Nat.log 2 (A.M + A.N + 2) + 1) ^ 2
      nlinarith [log_two_plus_one_ge_two A.M A.N]
    exact le_trans h1 (Nat.mul_le_mul_left capExp h2)
  set newlySum := (stepBundleTree sp A.tr A.U A.ord ord').newlyActive.sum A.tr.lazyMachInitCost
  set C_step := branchStepCharge sp A.tr A.U A.ord ord'
  set C_inp := (A.words + A.editWords + 1) * lg
  have hCstep_Unew : (A.U.length + newlySum) * lg ≤ C_step := by
    show (A.U.length + newlySum) * lg ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    exact Nat.mul_le_mul_right lg (by
      change A.U.length + (stepBundleTree sp A.tr A.U A.ord ord').newlyActive.sum
        (fun C => A.tr.lazyMachInitCost C) ≤ _
      omega)
  have hCstep_new : newlySum * lg ≤ C_step :=
    le_trans (Nat.mul_le_mul_right lg (Nat.le_add_left _ _)) hCstep_Unew
  have hCinp_1 : lg ≤ C_inp := Nat.le_mul_of_pos_left lg (by omega)
  have hTerm1 : newActCostMul TS hRoot.mul *
      ((A.newComps A.x.xRest.cmpH A.x.xRest.comps).length + 1 + newlySum) *
        ordStoreLog A.x.xRest.eCap5 ≤
      (2 * capExp * newActCostMul TS hRoot.mul) * (C_step + C_inp) := by
    calc newActCostMul TS hRoot.mul *
          ((A.newComps A.x.xRest.cmpH A.x.xRest.comps).length + 1 + newlySum) *
            ordStoreLog A.x.xRest.eCap5
        ≤ newActCostMul TS hRoot.mul * (2 * (A.U.length + newlySum) + 1) * (capExp * lg) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hOrdLog
      _ = capExp * newActCostMul TS hRoot.mul * (2 * ((A.U.length + newlySum) * lg) + lg) := by
          ring
      _ ≤ capExp * newActCostMul TS hRoot.mul * (2 * (C_step + C_inp)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = (2 * capExp * newActCostMul TS hRoot.mul) * (C_step + C_inp) := by ring
  have hTerm2 : 320 * (capExp + 1) * lg * newlySum ≤
      320 * (capExp + 1) * (C_step + C_inp) := by
    calc 320 * (capExp + 1) * lg * newlySum
        = 320 * (capExp + 1) * (newlySum * lg) := by ring
      _ ≤ 320 * (capExp + 1) * (C_step + C_inp) :=
          Nat.mul_le_mul_left _ (le_trans hCstep_new (Nat.le_add_right _ _))
  rw [hNewly] at hP2_cost
  unfold asmFsCostMulP2
  have hcomb : newActCostMul TS hRoot.mul *
      ((A.newComps A.x.xRest.cmpH A.x.xRest.comps).length + 1 + newlySum) *
        ordStoreLog A.x.xRest.eCap5 +
      320 * (capExp + 1) * lg * newlySum ≤
      (2 * capExp * newActCostMul TS hRoot.mul + 320 * (capExp + 1)) * (C_step + C_inp) := by
    rw [Nat.add_mul]; exact Nat.add_le_add hTerm1 hTerm2
  have hadd := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right hcomb
      ((bunTableHeadroomRep A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5 A.x.xRest.kB).phi
        A.x.xRest.bunH A.x.xRest.xBun st₁.mem))
      (320 * (capExp + 1) * lg * specPhi P_sp A.x.xRest.spanS))
    ((TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem)
  exact le_trans hP2_cost hadd

set_option maxHeartbeats 800000 in
/-- **Phase 3 cost bound**: bounds every non-potential term of `AsmFirstPhase3PostAt` against
`asmFsCostMulP3 capExp * (branchStepCharge + (words + editWords + 1) * bundleLogFactor)`. -/
theorem asmFsCost_p3 {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ₃ : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
      splitPtr outDescPtr mk' Mset Ys touched) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
    let ord' := applyOrdEdits A.ord A.ed
    let lg := bundleLogFactor A.M A.N
    c₃ + 70 * touched.length +
        (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₃.mem +
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx_pot' st₃.mem ≤
      asmFsCostMulP3 capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₂.mem +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx1 st₂.mem := by
  intro sp ord' lg
  obtain ⟨_, _, _, hP2, hP3⟩ := hQ₃
  have hM0 : A.tr.m₀ = A.M := hA.1
  have hN0 : A.tr.n₀ = A.N := hA.2.1
  have hThresh : ((A.n + A.U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold A.k A.M A.N :=
    hA.2.2.2.2.2.2.1
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hModF' : AsmBrModelFacts impl A.x.vCap A.x.eCap
      (stepBundleTree sp A.tr A.U A.ord ord').state ord' :=
    hA.2.2.2.2.2.2.2.2.2.2.1
  have hU : A.tr.cs.G.BatchIsValid A.U := hA.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOB : OrderedBatch A.tr.cs.G A.U A.ord ord' :=
    hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he5 : A.x.xRest.eCap5 = A.x.eCap := hR.2.2.1
  have hCap : A.x.vCap + A.x.eCap + 2 ≤ (A.M + A.N + 2) ^ capExp := by
    rw [← hM0, ← hN0]; exact hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOutRep : (outGraphRep A.x.vCap A.x.eCap).rep A.x.outH A.tr.S_cur A.x.gOut A.mem :=
    hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSide := hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMaps := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMod := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨C_lsst, ℓ₀, hI, _⟩ := hMod.2.2.2.2.2.2.1
  have hkB0 : A.x.xRest.kB = A.tr.k := hMod.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCross : AsmFirstCrossInactiveInv A.tr :=
    hMod.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hkB' : y'.kB = A.tr.k := (hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans hkB0
  have hv5' : y'.vCap5 = A.x.xRest.vCap5 := hP2.2.2.2.2.2.2.1
  have he5' : y'.eCap5 = A.x.xRest.eCap5 := hP2.2.2.2.2.2.2.2.1
  have hYs_le : (Ys.map List.length).sum ≤
      (A.tr.S_cur.applyBatch ((outDelList sp A.tr A.U A.ord ord').map Update.delete)).batchEnc
        (restrictSplits (outKeep sp A.tr A.U A.ord ord')
          (stepBundleTree sp A.tr A.U A.ord ord').U_core) +
      markPot (outKeep sp A.tr A.U A.ord ord') A.tr.S_cur.E (coreGraph A.tr.cs.G A.tr.cs.lsf) :=
    hP3.2.2.2.2.2.2.2.2.2.1
  have hP3_cost := hP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- Key size bounds
  set lg₁ := Nat.log 2 (A.M + A.N + 2) + 1
  have hlg_eq : lg = lg₁ ^ 2 := rfl
  have hlg₁_ge : 2 ≤ lg₁ := log_two_plus_one_ge_two A.M A.N
  have hlg₁_le : lg₁ ≤ lg := by rw [hlg_eq]; nlinarith
  have hlg_ge4 : 4 ≤ lg := bundleLogFactor_ge_four A.M A.N
  have hOrdLog1 : ordStoreLog A.x.xRest.eCap5 ≤ capExp * lg₁ := by
    rw [he5]; exact ordStoreLog_le_capExp hCap
  have hOrdLog : ordStoreLog A.x.xRest.eCap5 ≤ capExp * lg :=
    le_trans hOrdLog1 (Nat.mul_le_mul_left capExp hlg₁_le)
  have h4eLog : Nat.log 2 (4 * A.x.xRest.eCap5) + 2 ≤ (capExp + 2) * lg₁ := by
    rw [he5]; exact log_four_mul_eCap_le hCap
  -- delEdges.length ≤ U.length ≤ 4 * M
  set delEdges := (scanBatchFold A.tr.cs.G
    (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U).delEdges
  have hDel_le_U : delEdges.length ≤ A.U.length :=
    (asmFirstStep_newComps_ok (cmpMap₀ := fun v => A.mem (A.x.xRest.cmpH + v)) hI hU
      hMaps.2.2.2.2.1 hMaps.2.2.2.2.2.1 (asmSdMaps_cmp_ok hMaps) hCross).2.2.2.2.2
  have hLogDel : Nat.log 2 (delEdges.length + 1) + 1 ≤ 2 * lg₁ :=
    log_del_le (le_trans hDel_le_U (updateThreshold_nat_le hThresh))
  -- canonSplitList bounds
  set info := stepBundleTree sp A.tr A.U A.ord ord'
  set L_sp := (canonSplitList A.tr.cs A.U).length
  have hLsp_le_enc : L_sp ≤ A.tr.S_cur.batchEnc info.U_S :=
    asmFirstCanonSplitList_length_le_batchEnc sp A.tr A.U A.ord ord'
  have hR'_lt : ∀ v ∈ (compLSFBatch A.tr.cs A.U).RF.R, v < A.x.vCap := fun v hv =>
    hModF'.2.2.2.2.2.2.2.1 v ((compLSF_RF_isRSF (compLSFBatch_inv hI hU)).2.2.1 hv)
  have hLsp_le_vCap : L_sp ≤ A.x.vCap :=
    asmFirstCanonSplitList_length_le_vCap hI hU hOB hR'_lt
  have hLogLsp : Nat.log 2 (L_sp + 1) + 1 ≤ capExp * lg₁ :=
    log_succ_le_capExp (le_trans hLsp_le_vCap (Nat.le_add_right _ _)) hCap
  -- splitGroupsOf bounds
  set gs := splitGroupsOf ((canonSplitList A.tr.cs A.U).map fun s => (s.kept, s.fresh))
  have hGs_len : gs.length ≤ L_sp := by
    simpa [gs, L_sp] using splitGroupsOf_length_le ((canonSplitList A.tr.cs A.U).map fun s => (s.kept, s.fresh))
  have hGs_tot : groupsTotalLen gs ≤ 2 * L_sp := by
    simpa [gs, L_sp] using groupsTotalLen_splitGroupsOf_le ((canonSplitList A.tr.cs A.U).map fun s => (s.kept, s.fresh))
  -- S_cur.E.card ≤ eCap and Ys sum bound
  have hScur_card : A.tr.S_cur.E.card ≤ A.x.eCap := by
    have hsub : A.tr.S_cur.E ⊆ Finset.range A.x.eCap := fun e he =>
      Finset.mem_range.mpr (hOutRep.2.2.2.2.1 e he)
    simpa using Finset.card_le_card hsub
  have hBE_split : A.tr.S_cur.batchEnc info.U_S =
      (outDelList sp A.tr A.U A.ord ord').length +
        (A.tr.S_cur.applyBatch ((outDelList sp A.tr A.U A.ord ord').map Update.delete)).batchEnc
          (restrictSplits (outKeep sp A.tr A.U A.ord ord') info.U_core) +
        (A.tr.S_cur.applyBatch ((outDelList sp A.tr A.U A.ord ord').map Update.delete ++
          outSplitBatch sp A.tr A.U A.ord ord')).batchEnc
          (outInsBatch sp A.tr A.U A.ord ord') := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]
    rfl
  have hSdiff_eq : (A.tr.S_cur.E \ outKeep sp A.tr A.U A.ord ord').card =
      (outDelList sp A.tr A.U A.ord ord').length := by
    rw [outDelList, Finset.length_sort]
  have hYs_bound : (Ys.map List.length).sum ≤
      (4 * capExp + 5) * A.tr.S_cur.batchEnc info.U_S * lg₁ := by
    have hmp := markPot_le (outKeep sp A.tr A.U A.ord ord') A.tr.S_cur.E
      (coreGraph A.tr.cs.G A.tr.cs.lsf)
    have hlogS : Nat.log 2 (2 * A.tr.S_cur.E.card + 1) ≤ (capExp + 1) * lg₁ :=
      log_two_mul_le_capExp hScur_card hCap
    have hdel_le : (A.tr.S_cur.E \ outKeep sp A.tr A.U A.ord ord').card ≤
        A.tr.S_cur.batchEnc info.U_S := by
      rw [hSdiff_eq, hBE_split]; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    have hmp2 : markPot (outKeep sp A.tr A.U A.ord ord') A.tr.S_cur.E
        (coreGraph A.tr.cs.G A.tr.cs.lsf) ≤
        4 * (capExp + 1) * A.tr.S_cur.batchEnc info.U_S * lg₁ := by
      calc markPot (outKeep sp A.tr A.U A.ord ord') A.tr.S_cur.E
            (coreGraph A.tr.cs.G A.tr.cs.lsf)
          ≤ 2 * (A.tr.S_cur.E \ outKeep sp A.tr A.U A.ord ord').card *
              (2 * Nat.log 2 (2 * A.tr.S_cur.E.card + 1)) := hmp
        _ ≤ 2 * A.tr.S_cur.batchEnc info.U_S * (2 * ((capExp + 1) * lg₁)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdel_le) (Nat.mul_le_mul_left 2 hlogS)
        _ = 4 * (capExp + 1) * A.tr.S_cur.batchEnc info.U_S * lg₁ := by ring
    have hsp_le : (A.tr.S_cur.applyBatch ((outDelList sp A.tr A.U A.ord ord').map Update.delete)).batchEnc
        (restrictSplits (outKeep sp A.tr A.U A.ord ord') info.U_core) ≤
        A.tr.S_cur.batchEnc info.U_S * lg₁ := by
      have h1 : (A.tr.S_cur.applyBatch ((outDelList sp A.tr A.U A.ord ord').map Update.delete)).batchEnc
          (restrictSplits (outKeep sp A.tr A.U A.ord ord') info.U_core) ≤
          A.tr.S_cur.batchEnc info.U_S := by
        rw [hBE_split]; exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
      exact le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))
    have hring : A.tr.S_cur.batchEnc info.U_S * lg₁ +
        4 * (capExp + 1) * A.tr.S_cur.batchEnc info.U_S * lg₁ =
        (4 * capExp + 5) * A.tr.S_cur.batchEnc info.U_S * lg₁ := by ring
    exact le_trans hYs_le (hring ▸ Nat.add_le_add hsp_le hmp2)
  -- Shortcuts into C_step and C_inp
  set C_step := branchStepCharge sp A.tr A.U A.ord ord'
  set C_inp := (A.words + A.editWords + 1) * lg
  set C_tot := C_step + C_inp
  have hU_C : A.U.length * lg ≤ C_step := by
    show A.U.length * lg ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    exact Nat.mul_le_mul_right lg (by omega)
  have hEnc_C : A.tr.S_cur.batchEnc info.U_S * lg ≤ C_step := by
    show A.tr.S_cur.batchEnc info.U_S * lg ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    dsimp only [info]
    exact Nat.mul_le_mul_right lg (by omega)
  have hLsp_C : L_sp * lg ≤ C_step := le_trans (Nat.mul_le_mul_right lg hLsp_le_enc) hEnc_C
  have hULsp_C : (A.U.length + L_sp) * lg ≤ C_step := by
    show (A.U.length + L_sp) * lg ≤ branchStepCharge sp A.tr A.U A.ord ord'
    unfold branchStepCharge; rw [hM0, hN0]
    have h1 : A.U.length + L_sp ≤ A.U.length + A.tr.S_cur.batchEnc info.U_S :=
      Nat.add_le_add_left hLsp_le_enc _
    dsimp only [info] at h1
    exact Nat.mul_le_mul_right lg (by omega)
  have h1_C : 1 ≤ C_inp := le_trans (by omega : 1 ≤ lg) (Nat.le_mul_of_pos_left lg (by omega))
  -- (1) buildDelTriplesCost
  have hT1 : buildDelTriplesCost tourBundleSpec A.x.xRest.eCap5 delEdges.length ≤
      (2 * tourBundleSpec.mul * capExp + 280) * C_step + 60 * C_inp := by
    unfold buildDelTriplesCost
    have h1 : (2 * tourBundleSpec.mul * ordStoreLog A.x.xRest.eCap5 + 280) * delEdges.length ≤
        (2 * tourBundleSpec.mul * capExp + 280) * (A.U.length * lg) := by
      calc (2 * tourBundleSpec.mul * ordStoreLog A.x.xRest.eCap5 + 280) * delEdges.length
          ≤ (2 * tourBundleSpec.mul * (capExp * lg) + 280 * lg) * A.U.length :=
            Nat.mul_le_mul (Nat.add_le_add (Nat.mul_le_mul_left _ hOrdLog)
              (Nat.le_mul_of_pos_right 280 (by omega))) hDel_le_U
        _ = (2 * tourBundleSpec.mul * capExp + 280) * (A.U.length * lg) := by ring
    exact Nat.add_le_add (le_trans h1 (Nat.mul_le_mul_left _ hU_C)) (Nat.le_mul_of_pos_right 60 (by omega))
  -- (2) buildGroupsCost
  have hT2 : buildGroupsCost L_sp ≤ 710 * capExp * C_step + 500 * C_inp := by
    unfold buildGroupsCost
    have h1 : 710 * L_sp * (Nat.log 2 (L_sp + 1) + 1) ≤ 710 * capExp * (L_sp * lg) := by
      calc 710 * L_sp * (Nat.log 2 (L_sp + 1) + 1)
          ≤ 710 * L_sp * (capExp * lg) :=
            Nat.mul_le_mul_left _ (le_trans hLogLsp (Nat.mul_le_mul_left capExp hlg₁_le))
        _ = 710 * capExp * (L_sp * lg) := by ring
    exact Nat.add_le_add (le_trans h1 (Nat.mul_le_mul_left _ hLsp_C)) (Nat.le_mul_of_pos_right 500 (by omega))
  -- (3) tourBlockStepMul term
  have hT3 : tourBlockStepMul *
      ((Ys.map List.length).sum + A.tr.S_cur.batchEnc info.U_S + A.words + A.editWords + 1) *
        ordStoreLog A.x.xRest.eCap5 ≤
      tourBlockStepMul * capExp * (4 * capExp + 6) * C_tot := by
    have hsum : (Ys.map List.length).sum + A.tr.S_cur.batchEnc info.U_S + A.words + A.editWords + 1 ≤
        ((4 * capExp + 6) * A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1)) * lg₁ := by
      have h1 : A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1) ≤
          (A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1)) * lg₁ :=
        Nat.le_mul_of_pos_right _ (by omega)
      have hring : (4 * capExp + 5) * A.tr.S_cur.batchEnc info.U_S * lg₁ +
          (A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1)) * lg₁ =
          ((4 * capExp + 6) * A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1)) * lg₁ := by
        ring
      have hadd := Nat.add_le_add hYs_bound h1
      rw [hring] at hadd
      have hre : (Ys.map List.length).sum + A.tr.S_cur.batchEnc info.U_S + A.words + A.editWords + 1 =
          (Ys.map List.length).sum + (A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1)) := by
        omega
      rw [hre]; exact hadd
    calc tourBlockStepMul *
          ((Ys.map List.length).sum + A.tr.S_cur.batchEnc info.U_S + A.words + A.editWords + 1) *
            ordStoreLog A.x.xRest.eCap5
        ≤ tourBlockStepMul *
            (((4 * capExp + 6) * A.tr.S_cur.batchEnc info.U_S + (A.words + A.editWords + 1)) * lg₁) *
            (capExp * lg₁) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hsum) hOrdLog1
      _ = tourBlockStepMul * capExp *
            ((4 * capExp + 6) * (A.tr.S_cur.batchEnc info.U_S * lg₁ ^ 2) +
              (A.words + A.editWords + 1) * lg₁ ^ 2) := by ring
      _ ≤ tourBlockStepMul * capExp * ((4 * capExp + 6) * C_step + (4 * capExp + 6) * C_inp) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [← hlg_eq]
          exact Nat.add_le_add (Nat.mul_le_mul_left _ hEnc_C) (Nat.le_mul_of_pos_left C_inp (by omega))
      _ = tourBlockStepMul * capExp * (4 * capExp + 6) * C_tot := by ring
  -- (4) bundleStepCost
  have hT4 : bundleStepCost tourBundleSpec A.x.xRest.eCap5 delEdges.length gs ≤
      (4 * tourBundleSpec.mul * capExp + 2210) * C_step + 240 * C_inp := by
    unfold bundleStepCost bundleStepScanCost
    have h4a : 300 * delEdges.length * (Nat.log 2 (delEdges.length + 1) + 1) ≤ 600 * C_step := by
      calc 300 * delEdges.length * (Nat.log 2 (delEdges.length + 1) + 1)
          ≤ 300 * A.U.length * (2 * lg) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 300 hDel_le_U)
              (le_trans hLogDel (Nat.mul_le_mul_left 2 hlg₁_le))
        _ = 600 * (A.U.length * lg) := by ring
        _ ≤ 600 * C_step := Nat.mul_le_mul_left 600 hU_C
    have h4b : 1070 * delEdges.length ≤ 1070 * C_step := by
      calc 1070 * delEdges.length ≤ 1070 * (A.U.length * lg) :=
            Nat.mul_le_mul_left 1070 (le_trans hDel_le_U (Nat.le_mul_of_pos_right _ (by omega)))
        _ ≤ 1070 * C_step := Nat.mul_le_mul_left 1070 hU_C
    have h4c : (2 * tourBundleSpec.mul * ordStoreLog A.x.xRest.eCap5 + 200) * groupsTotalLen gs ≤
        (4 * tourBundleSpec.mul * capExp + 400) * C_step := by
      calc (2 * tourBundleSpec.mul * ordStoreLog A.x.xRest.eCap5 + 200) * groupsTotalLen gs
          ≤ (2 * tourBundleSpec.mul * (capExp * lg) + 200 * lg) * (2 * L_sp) :=
            Nat.mul_le_mul (Nat.add_le_add (Nat.mul_le_mul_left _ hOrdLog)
              (Nat.le_mul_of_pos_right 200 (by omega))) hGs_tot
        _ = (4 * tourBundleSpec.mul * capExp + 400) * (L_sp * lg) := by ring
        _ ≤ (4 * tourBundleSpec.mul * capExp + 400) * C_step := Nat.mul_le_mul_left _ hLsp_C
    have h4d : 70 * gs.length ≤ 140 * C_step := by
      calc 70 * gs.length ≤ 140 * (L_sp * lg) := by
            have h1 : gs.length ≤ L_sp * lg := le_trans hGs_len (Nat.le_mul_of_pos_right _ (by omega))
            exact Nat.mul_le_mul (by omega) h1
        _ ≤ 140 * C_step := Nat.mul_le_mul_left 140 hLsp_C
    have h4e : 80 + 160 ≤ 240 * C_inp := Nat.le_mul_of_pos_right 240 (by omega)
    have hring : 600 * C_step + 1070 * C_step + (4 * tourBundleSpec.mul * capExp + 400) * C_step +
        140 * C_step = (4 * tourBundleSpec.mul * capExp + 2210) * C_step := by ring
    omega
  -- (5) bundleScanPotMul term
  have hT5 : bundleScanPotMul tourBundleSpec A.x.xRest.eCap5 *
      (2 * (A.U.length + L_sp) * (Nat.log 2 (4 * A.x.xRest.eCap5) + 2)) + 120 ≤
      2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) * C_step + 120 * C_inp := by
    have hpm : bundleScanPotMul tourBundleSpec A.x.xRest.eCap5 ≤
        ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * lg₁ := by
      unfold bundleScanPotMul
      have h1 := Nat.mul_le_mul_left (3 * tourBundleSpec.mul + 900) hOrdLog1
      have h2 : 4600 ≤ 4600 * lg₁ := Nat.le_mul_of_pos_right 4600 (by omega)
      have hring : (3 * tourBundleSpec.mul + 900) * (capExp * lg₁) + 4600 * lg₁ =
          ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * lg₁ := by ring
      rw [← hring]
      exact Nat.add_le_add h1 h2
    have hprod : bundleScanPotMul tourBundleSpec A.x.xRest.eCap5 *
        (2 * (A.U.length + L_sp) * (Nat.log 2 (4 * A.x.xRest.eCap5) + 2)) ≤
        2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) * C_step := by
      calc bundleScanPotMul tourBundleSpec A.x.xRest.eCap5 *
            (2 * (A.U.length + L_sp) * (Nat.log 2 (4 * A.x.xRest.eCap5) + 2))
          ≤ (((3 * tourBundleSpec.mul + 900) * capExp + 4600) * lg₁) *
              (2 * (A.U.length + L_sp) * ((capExp + 2) * lg₁)) :=
            Nat.mul_le_mul hpm (Nat.mul_le_mul_left _ h4eLog)
        _ = 2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) *
              ((A.U.length + L_sp) * lg₁ ^ 2) := by ring
        _ ≤ 2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) * C_step := by
            rw [← hlg_eq]; exact Nat.mul_le_mul_left _ hULsp_C
    exact Nat.add_le_add hprod (Nat.le_mul_of_pos_right 120 (by omega))
  -- Combine all terms
  have hRHS : buildDelTriplesCost tourBundleSpec A.x.xRest.eCap5 delEdges.length +
      buildGroupsCost L_sp +
      tourBlockStepMul *
        ((Ys.map List.length).sum + A.tr.S_cur.batchEnc info.U_S + A.words + A.editWords + 1) *
        ordStoreLog A.x.xRest.eCap5 +
      bundleStepCost tourBundleSpec A.x.xRest.eCap5 delEdges.length gs +
      bunPhiMul * C_step +
      bundleScanPotMul tourBundleSpec A.x.xRest.eCap5 *
        (2 * (A.U.length + L_sp) * (Nat.log 2 (4 * A.x.xRest.eCap5) + 2)) + 120 ≤
      asmFsCostMulP3 capExp * C_tot := by
    have hstep_le : C_step ≤ C_tot := Nat.le_add_right _ _
    have hinp_le : C_inp ≤ C_tot := Nat.le_add_left _ _
    unfold asmFsCostMulP3
    have hC1 : ((2 * tourBundleSpec.mul * capExp + 280) + 710 * capExp +
        (4 * tourBundleSpec.mul * capExp + 2210) + bunPhiMul +
        2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2)) * C_step ≤
        ((6 * tourBundleSpec.mul + 710) * capExp + 2490 + bunPhiMul +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2)) * C_tot := by
      have heq : (2 * tourBundleSpec.mul * capExp + 280) + 710 * capExp +
          (4 * tourBundleSpec.mul * capExp + 2210) + bunPhiMul +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) =
          (6 * tourBundleSpec.mul + 710) * capExp + 2490 + bunPhiMul +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) := by ring
      rw [heq]; exact Nat.mul_le_mul_left _ hstep_le
    have hC2 : (60 + 500 + 240 + 120) * C_inp ≤ 920 * C_tot := Nat.mul_le_mul_left 920 hinp_le
    have hsum_eq1 :
        ((2 * tourBundleSpec.mul * capExp + 280) * C_step + 60 * C_inp) +
        (710 * capExp * C_step + 500 * C_inp) +
        tourBlockStepMul * capExp * (4 * capExp + 6) * C_tot +
        ((4 * tourBundleSpec.mul * capExp + 2210) * C_step + 240 * C_inp) +
        bunPhiMul * C_step +
        (2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) * C_step + 120 * C_inp) =
        ((2 * tourBundleSpec.mul * capExp + 280) + 710 * capExp +
          (4 * tourBundleSpec.mul * capExp + 2210) + bunPhiMul +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2)) * C_step +
        tourBlockStepMul * capExp * (4 * capExp + 6) * C_tot +
        (60 + 500 + 240 + 120) * C_inp := by ring
    have hsum_eq2 :
        ((6 * tourBundleSpec.mul + 710) * capExp + 2490 + bunPhiMul +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2)) * C_tot +
        tourBlockStepMul * capExp * (4 * capExp + 6) * C_tot +
        920 * C_tot =
        ((6 * tourBundleSpec.mul + 710) * capExp + 2490 + bunPhiMul +
          tourBlockStepMul * capExp * (4 * capExp + 6) +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) + 920) * C_tot := by
      ring
    have hmid :
        ((2 * tourBundleSpec.mul * capExp + 280) * C_step + 60 * C_inp) +
        (710 * capExp * C_step + 500 * C_inp) +
        tourBlockStepMul * capExp * (4 * capExp + 6) * C_tot +
        ((4 * tourBundleSpec.mul * capExp + 2210) * C_step + 240 * C_inp) +
        bunPhiMul * C_step +
        (2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) * C_step + 120 * C_inp) ≤
        ((6 * tourBundleSpec.mul + 710) * capExp + 2490 + bunPhiMul +
          tourBlockStepMul * capExp * (4 * capExp + 6) +
          2 * ((3 * tourBundleSpec.mul + 900) * capExp + 4600) * (capExp + 2) + 920) * C_tot := by
      rw [hsum_eq1, ← hsum_eq2]
      exact Nat.add_le_add (Nat.add_le_add_right hC1 _) hC2
    have hstep_all := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add hT1 hT2) hT3) hT4) (le_refl (bunPhiMul * C_step))) hT5
    exact le_trans (le_of_eq (Nat.add_assoc _ _ 120)) (le_trans hstep_all hmid)
  change c₃ + 70 * touched.length +
      (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).phi y'.bunH y'.xBun st₃.mem +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx_pot' st₃.mem ≤
    asmFsCostMulP3 capExp * C_tot +
      (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).phi y'.bunH y'.xBun st₂.mem +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx1 st₂.mem
  rw [hkB', hv5', he5']
  exact le_trans hP3_cost (Nat.add_le_add_right (Nat.add_le_add_right hRHS _) _)

/-- **Combined Phases 1, 2, 3, and driver cost bound** (cancelling `bunPhi` and `tourPhi` at
`st₂`). -/
theorem asmFsCost_p123 {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ₃ : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
      splitPtr outDescPtr mk' Mset Ys touched)
    {tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} (hTx₀ : HEq tx₀ A.x.xTour) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
    let ord' := applyOrdEdits A.ord A.ed
    let P_sp := asmBrSP impl w depth y'
    let lg := bundleLogFactor A.M A.N
    c₁ + c₂ + c₃ + 340 + 70 * touched.length +
        (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₃.mem +
        320 * (capExp + 1) * lg * specPhi P_sp y'.spanS +
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx_pot' st₃.mem ≤
      asmFsCostMulP123 TS hRoot.mul capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      (scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
        A.x.xRest.bunH A.x.xRest.xBun st₁.mem +
      320 * (capExp + 1) * lg * specPhi P_sp A.x.xRest.spanS +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem := by
  intro sp ord' P_sp lg
  have h1 := asmFsCost_p1_driver hQ₃
  have h2 : c₂ + (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₂.mem +
        320 * (capExp + 1) * lg * specPhi P_sp y'.spanS +
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx1 st₂.mem ≤
      asmFsCostMulP2 TS hRoot.mul capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      (scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
        A.x.xRest.bunH A.x.xRest.xBun st₁.mem +
      320 * (capExp + 1) * lg * specPhi P_sp A.x.xRest.spanS +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem :=
    asmFsCost_p2 hA hQ₃ hTx₀
  have h3 : c₃ + 70 * touched.length +
        (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₃.mem +
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx_pot' st₃.mem ≤
      asmFsCostMulP3 capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₂.mem +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx1 st₂.mem :=
    asmFsCost_p3 hA hQ₃
  unfold asmFsCostMulP123
  have h1' : c₁ + 340 ≤ asmFsCostMulP1 *
      (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) := by
    calc c₁ + 340 ≤ asmFsCostMulP1 * ((A.words + A.editWords + 1) * lg) := h1
      _ ≤ asmFsCostMulP1 *
            (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) :=
          Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have hring : (asmFsCostMulP1 + asmFsCostMulP2 TS hRoot.mul capExp + asmFsCostMulP3 capExp) *
      (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) =
      asmFsCostMulP1 *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      asmFsCostMulP2 TS hRoot.mul capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) +
      asmFsCostMulP3 capExp *
        (branchStepCharge sp A.tr A.U A.ord ord' + (A.words + A.editWords + 1) * lg) := by
    ring
  omega

end

end MinCostFlow.SparseCore.Program
