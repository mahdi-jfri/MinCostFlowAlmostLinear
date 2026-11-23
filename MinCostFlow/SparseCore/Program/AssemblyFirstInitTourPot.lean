module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBuild
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourPot
public import MinCostFlow.SparseCore.Program.TourAsmBridge

import MinCostFlow.SparseCore.Program.AssemblyFirstInitBoundCost
import Mathlib.Tactic

/-!
# Tour potential at the init of a branch (`AssemblyFirstInitTourPot`)

Wraps a branch-init build `AsmFirstInitBuildAt tourAsmRep …` into
`AsmFirstInitBuildAt (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) …`,
bounding the initial tour potential `bundleScanPotMul tourBundleSpec eCap * tourPot R cord`
against `tr₀.machCost` via `tourPot_le_mul_log` and `SparseCoreCapHyp`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-- Multiplier paying for the initial tour potential
`bundleScanPotMul tourBundleSpec eCap * tourPot R cord` in terms of `tr₀.machCost`. -/
def asmFiTourPotMul (capExp : ℕ) : ℕ :=
  (9 * tourMul + 16500) * capExp

/-- **Initial tour-potential bound against `tr₀.machCost`**: under `SparseCoreCapHyp` and
`AsmBrModelFacts`, `bundleScanPotMul tourBundleSpec eCap * tourPot tr₀.cs.lsf.F.R (outCoreOrder tr₀ ord)`
is at most `asmFiTourPotMul capExp * tr₀.machCost`. -/
theorem asmFi_tourPot_le_machCost {depth capExp limbMul L M N vCap eCap k : ℕ}
    {impl : SparsifyImpl} {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End}
    {j : ℕ} (hM : G.m ≤ M)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hF : AsmBrModelFacts impl vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    bundleScanPotMul tourBundleSpec eCap * tourPot tr.cs.lsf.F.R (outCoreOrder tr ord) ≤
      asmFiTourPotMul capExp * tr.machCost := by
  intro tr
  set L1 := Nat.log 2 (M + N + 2) + 1 with hL1
  have hL1_pos : 1 ≤ L1 := by omega
  have hcap1 : 1 ≤ capExp := by
    by_contra h0
    have hc0 : capExp = 0 := by omega
    have hle := hcap.1
    rw [hc0, pow_zero] at hle
    omega
  have hord : ordStoreLog eCap ≤ capExp * L1 :=
    ordStoreLog_le_of_cap (le_trans (by omega) hcap.1)
  have hmul : tourBundleSpec.mul = tourMul := rfl
  have hcapL1 : 1 ≤ capExp * L1 := Nat.mul_pos hcap1 hL1_pos
  have hscan : bundleScanPotMul tourBundleSpec eCap ≤ (3 * tourMul + 5500) * capExp * L1 := by
    unfold bundleScanPotMul
    rw [hmul]
    have h1 : (3 * tourMul + 900) * ordStoreLog eCap ≤ (3 * tourMul + 900) * (capExp * L1) :=
      Nat.mul_le_mul_left _ hord
    have h2 : 4600 ≤ 4600 * (capExp * L1) := Nat.le_mul_of_pos_right 4600 hcapL1
    have h3 : (3 * tourMul + 900) * (capExp * L1) + 4600 * (capExp * L1) =
        (3 * tourMul + 5500) * capExp * L1 := by ring
    omega
  -- sum of core rotation lengths over `tr.cs.lsf.F.R` is at most `2 * G.m`
  obtain ⟨-, hrot, -⟩ := id hF
  have hC : CoreCordOf tr.cs ord (outCoreOrder tr ord) := coreCordOf_outCoreOrder hrot
  have hsum : (∑ r ∈ tr.cs.lsf.F.R, (outCoreOrder tr ord r).length) ≤ 2 * G.m := by
    have hEq : (∑ r ∈ tr.cs.lsf.F.R, (outCoreOrder tr ord r).length) =
        (tr.cs.lsf.F.R.toList.map fun v => (outCoreOrder tr ord v).length).sum := by
      rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
      simp only [Finset.toList_toFinset]
    rw [hEq]
    exact (coreCord_facts hC).2.2.2 tr.cs.lsf.F.R.toList (Finset.nodup_toList _)
  have hpot : tourPot tr.cs.lsf.F.R (outCoreOrder tr ord) ≤ (Nat.log 2 (2 * G.m + 1) + 2) * (2 * G.m) :=
    tourPot_le_mul_log hsum
  have hlog2m : Nat.log 2 (2 * G.m + 1) + 2 ≤ 3 * L1 := by
    have hle : 2 * G.m + 1 ≤ (M + N + 2) * 2 := by omega
    have hlog1 : Nat.log 2 (2 * G.m + 1) ≤ Nat.log 2 ((M + N + 2) * 2) :=
      Nat.log_mono_right hle
    have hlog2 : Nat.log 2 ((M + N + 2) * 2) = Nat.log 2 (M + N + 2) + 1 :=
      Nat.log_mul_base (by norm_num) (by omega)
    omega
  have hpot' : tourPot tr.cs.lsf.F.R (outCoreOrder tr ord) ≤ 3 * L1 * (3 * G.m + 2) :=
    hpot.trans (Nat.mul_le_mul hlog2m (by omega))
  have hmc : (3 * G.m + 2) * bundleLogFactor M N ≤ tr.machCost :=
    initMachCost_ge lsfInit (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl)
      (dsAmortConst impl) k M N G ℓ₀ ord j
  have hlg : bundleLogFactor M N = L1 * L1 := by
    unfold bundleLogFactor; rw [sq, ← hL1]
  calc bundleScanPotMul tourBundleSpec eCap * tourPot tr.cs.lsf.F.R (outCoreOrder tr ord)
      ≤ ((3 * tourMul + 5500) * capExp * L1) * (3 * L1 * (3 * G.m + 2)) :=
        Nat.mul_le_mul hscan hpot'
    _ = asmFiTourPotMul capExp * ((3 * G.m + 2) * (L1 * L1)) := by
        unfold asmFiTourPotMul; ring
    _ = asmFiTourPotMul capExp * ((3 * G.m + 2) * bundleLogFactor M N) := by rw [hlg]
    _ ≤ asmFiTourPotMul capExp * tr.machCost := Nat.mul_le_mul_left _ hmc

/-- **Lifts a branch-init build from bare `tourAsmRep` to `asmTourRepWithPot tourAsmRep
(bundleScanPotMul tourBundleSpec)`**, adding `asmFiTourPotMul capExp` to the cost multiplier and
keeping the exact same procedure and space polynomial. -/
noncomputable def asmFirstInitBuildAt_withTourPot
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit} {impl : SparsifyImpl}
    {depth P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {f : ℕ}
    (B : AsmFirstInitBuildAt tourAsmRep B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p f) :
    AsmFirstInitBuildAt (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) B5 CFR
      lsfInit impl depth P L capExp limbMul wordExp w Ψ p f where
  mul := B.mul + asmFiTourPotMul capExp
  space := B.space
  runs := by
    intro cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf
      mem pos ω X tr₀ hk hj hGv hGne hGM hGN hnm hPL hcap hword hCF hcfs hlen hdg hgraph hord
      hordh hcw hrot hexp hexph hcfft hargs hz hsp hF
    obtain ⟨body, hf, o, st', cost, x, hrun, w1, w2, w3, w4, w5, w6, w7, w8, hxv, hxe, hxt, hxl,
        hemb, hdom, hembEq, hout, htour, hmarks, hX, hv5, he5, hslot, hin, hdisj, hsize, ho, hz',
        hlow, hcost⟩ :=
      B.runs cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf
        mem pos ω hk hj hGv hGne hGM hGN hnm hPL hcap hword hCF hcfs hlen hdg hgraph hord hordh
        hcw hrot hexp hexph hcfft hargs hz hsp hF
    let pT : ℕ :=
      bundleScanPotMul tourBundleSpec x.eCap *
        tourPotOfAbs ⟨ord, tr₀.cs.lsf.F, x.sTour.marked⟩
    let x' : AsmBrConc (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) X.τ :=
      { vCap := x.vCap
        eCap := x.eCap
        tCap := x.tCap
        L_w := x.L_w
        readH := x.readH
        yRead := x.yRead
        embH := x.embH
        yEmb := x.yEmb
        outH := x.outH
        gOut := x.gOut
        tourH := x.tourH
        sTour := x.sTour
        xTour := (x.xTour, pT)
        restH := x.restH
        xRest := x.xRest }
    have hpotEq : pT = bundleScanPotMul tourBundleSpec eCap *
        tourPot tr₀.cs.lsf.F.R (outCoreOrder tr₀ ord) := by
      dsimp only [pT]
      rw [hxe, tourPotOfAbs_eq_of_tourCordOK x.sTour.marked htour.2.1]
    have hpotLe : pT ≤ asmFiTourPotMul capExp * tr₀.machCost := by
      rw [hpotEq]
      exact asmFi_tourPot_le_machCost hGM hcap hF
    refine ⟨body, hf, o, st', cost, x', hrun, w1, w2, w3, w4, w5, w6, w7, w8, hxv, hxe, hxt, hxl,
      hemb, hdom, hembEq, hout, ⟨htour.1, htour.2.1, htour.2.2, rfl⟩, hmarks, hX, hv5, he5, hslot,
      hin, hdisj, hsize, ho, hz', hlow, ?_⟩
    have hcost' : cost + (tourAsmRep x.vCap x.eCap).phi x.tourH x.xTour st'.mem +
        X.phi x.restH x.xRest st'.mem ≤ B.mul * tr₀.machCost := hcost
    show cost + ((tourAsmRep x.vCap x.eCap).phi x.tourH x.xTour st'.mem + pT) +
        X.phi x.restH x.xRest st'.mem ≤ (B.mul + asmFiTourPotMul capExp) * tr₀.machCost
    rw [Nat.add_mul]
    omega

end MinCostFlow.SparseCore.Program
