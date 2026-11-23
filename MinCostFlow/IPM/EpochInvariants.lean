module

public import MinCostFlow.IPM.EpochProgress
public import MinCostFlow.IPM.EpochHidden
public import MinCostFlow.IPM.EpochResidual
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The full epoch induction

This combines the adapted Lemmas 9.1--9.3 of Chen et al.,
arXiv:2203.00671v2 (Section 9, pages 69--72), for the actual causal
epoch loop. Starting with residual greater than one quarter, a full
`m`-step epoch stays in the analytic domain. Exact Detect semantics
control stale coordinates. Residual drift controls the stored estimate.
These prove hidden stability of each input prefix, which invokes the
data structure's ratio guarantee and proves the next step's progress.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The epoch's initial represented flow equals its base flow, by the
zero-initial-flow part of the data structure contract. -/
theorem epochFlow_zero (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (hI : I.IsValid) (hf : StrictlyInside I base)
    (hA : MinRatioSpec A κ α Ψ ε) : epochFlow I U κ r A base 0 = base := by
  have hv := epoch_history_valid_prefix I U κ r A base 0 hI (by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact hf)
  funext e
  rw [epoch_query I U κ r α Ψ ε A base 0 0 hA hv le_rfl]
  change base e+minRatioFlow A _ _ _ 0 e = base e
  rw [minRatioFlow_zero, add_zero]

private theorem epoch_snapshot (I : Instance) (U κ : ℝ) (R : ℕ → ℝ) (n : ℕ)
    (hm : 0 < I.m) (hn : n ≤ I.m) (hsize : 2 ≤ (I.m : ℝ)*U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hstart : (1/4 : ℝ) < R 0) (hpos : ∀ j ≤ n, 0 < R j)
    (hstep : ∀ j < n, |R (j+1)-R j|/R j ≤ (2*ipmDetectThreshold I U κ)/I.m) :
    ∀ j ≤ n, ScalarApprox (1+8*ipmDetectThreshold I U κ) (R 0) (R j) ∧
      Real.rpow (I.m*U) (-10) < R j := by
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have hg : 0 ≤ 2*ipmDetectThreshold I U κ := mul_nonneg (by norm_num) he.1.le
  have hg' : 2*ipmDetectThreshold I U κ ≤ 1/100 := by linarith only [he.2.1]
  intro j hj
  have hs := epoch_residual_approx_prefix R I.m n (2*ipmDetectThreshold I U κ)
    hm hn hg hg' hpos hstep j hj
  have hfac : 1+4*(2*ipmDetectThreshold I U κ) = 1+8*ipmDetectThreshold I U κ := by ring
  rw [hfac] at hs
  refine ⟨hs, ?_⟩
  have hpay := mul_le_mul_of_nonneg_right he.2.1 (hpos j hj).le
  have hlarge : (1/8 : ℝ) < R j := by linarith only [hstart, hs.2.2.2, hpay, (hpos j hj).le]
  have hpow := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hsize
    (by norm_num : (-10 : ℝ) ≤ 0)
  have hsmall : Real.rpow (I.m*U) (-10) < (1/8 : ℝ) := by
    exact hpow.trans_lt (by norm_num)
  exact hsmall.trans hlarge

/-- The causal epoch loop preserves feasibility and the potential budget
for a full `m` steps. Every residual estimate and hidden prefix needed
by its Update calls is derived in the induction. Each step deposits at
most one Detect threshold and decreases potential by
`(κ α/64)²/500`. -/
theorem epoch_invariants (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hstart : (1/4 : ℝ) < residual I F base)
    (hpot : potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U))
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)) :
    let r := residual I F base
    ∀ n ≤ I.m,
      I.Routes (epochFlow I U κ r A base n) ∧
      StrictlyInside I (epochFlow I U κ r A base n) ∧
      0 < residual I F (epochFlow I U κ r A base n) ∧
      StrictlyInside I (epochState I U κ r A base n).stored ∧
      potential I (alpha I U) F (epochFlow I U κ r A base n) ≤ 200*I.m*Real.log (I.m*U) ∧
      ScalarApprox (1+8*ipmDetectThreshold I U κ) r (residual I F (epochFlow I U κ r A base n)) ∧
      Real.rpow (I.m*U) (-10) < residual I F (epochFlow I U κ r A base n) ∧
      (∀ j < n,
        weightedLength (lengths I (alpha I U) (epochState I U κ r A base j).stored)
          (fun e => epochIncrement I U κ r A base j e) ≤ ipmDetectThreshold I U κ ∧
        potential I (alpha I U) F (epochFlow I U κ r A base (j+1)) ≤
          potential I (alpha I U) F (epochFlow I U κ r A base j)-(κ*alpha I U/64)^2/500) := by
  dsimp only
  let r := residual I F base
  let f := epochFlow I U κ r A base
  let R := fun j => residual I F (f j)
  have hzero : f 0 = base := epochFlow_zero I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
    (ipmDetectThreshold I U κ) A base hI hbase hA
  have hRzero : R 0 = r := by change residual I F (f 0) = _; rw [hzero]
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have hmR : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have hpast : ∀ n ≤ I.m,
      (∀ j ≤ n, I.Routes (f j) ∧ StrictlyInside I (f j) ∧ 0 < R j ∧
        StrictlyInside I (epochState I U κ r A base j).stored ∧
        potential I (alpha I U) F (f j) ≤ 200*I.m*Real.log (I.m*U)) ∧
      (∀ j < n, |R (j+1)-R j|/R j ≤ (2*ipmDetectThreshold I U κ)/I.m ∧
        weightedLength (lengths I (alpha I U) (epochState I U κ r A base j).stored)
          (fun e => epochIncrement I U κ r A base j e) ≤ ipmDetectThreshold I U κ ∧
        potential I (alpha I U) F (f (j+1)) ≤
          potential I (alpha I U) F (f j)-(κ*alpha I U/64)^2/500) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, by intro j hj; omega⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      rw [hzero]
      exact ⟨hroute, hbase, by rw [hRzero]; dsimp only [r]; linarith only [hstart], hbase, hpot⟩
    | succ n ih =>
      intro hn
      have hi := ih (Nat.le_of_succ_le hn)
      have hsnapshot := epoch_snapshot I U κ R n hm (Nat.le_of_succ_le hn) hsize hk hk'
        (by rw [hRzero]; exact hstart) (fun j hj => (hi.1 j hj).2.2.1)
        (fun j hj => (hi.2 j hj).1)
      have hvalid := epoch_history_valid_prefix I U κ r A base (2*n+1) hI
        (by intro j hj; exact (hi.1 j (by omega)).2.2.2.1)
      have hhidden := epoch_hiddenStable_of_numerical I U F κ r A base fstar (2*n+1)
        hm hU hsize hnums hk hk' hs hF hA hvalid
        (fun j hj => (hi.1 j (by omega)).2.2.2.1)
        (fun j hj => (hi.1 j (by omega)).2.1)
        (fun j hj => (hi.1 j (by omega)).1)
        (fun j hj => (hsnapshot j (by omega)).2)
        (fun j hj => (hi.1 j (by omega)).2.2.2.2)
        (by intro j hj; have hh := (hsnapshot j (by omega)).1; rw [hRzero] at hh; exact hh)
        (by intro j hj; exact (hi.2 j (by omega)).2.1)
      have hresn := (hsnapshot n le_rfl).1
      rw [hRzero] at hresn
      have hp := epoch_progress I U F κ r A base n hI hm (le_trans (by norm_num) hU) hsize hnums hk hk' hA
        (fun j hj => (hi.1 j hj).2.2.2.1) (hi.1 n le_rfl).2.1 (hi.1 n le_rfl).1 hresn hhidden
      obtain ⟨hnroute, hninside, hnpos, hnstored, hndec, hndrift, hnmove⟩ := hp
      have hphi : potential I (alpha I U) F (f (n+1)) ≤ 200*I.m*Real.log (I.m*U) := by
        linarith only [hndec, (hi.1 n le_rfl).2.2.2.2, sq_nonneg (κ*alpha I U/64)]
      have hγ : κ*alpha I U/(800*I.m) ≤ (2*ipmDetectThreshold I U κ)/I.m := by
        apply (le_div_iff₀ hmR).mpr
        have hcancel : κ*alpha I U/(800*I.m)*I.m = κ*alpha I U/800 := by field_simp
        rw [hcancel]
        unfold ipmDetectThreshold
        have hka := (mul_pos hk (alpha_pos I U hsize)).le
        linarith only [hka]
      have hmov : κ*alpha I U/6400 ≤ ipmDetectThreshold I U κ := by
        unfold ipmDetectThreshold
        have hka := (mul_pos hk (alpha_pos I U hsize)).le
        linarith only [hka]
      refine ⟨?_, ?_⟩
      · intro j hj
        by_cases heq : j = n+1
        · subst j
          exact ⟨hnroute, hninside, hnpos, hnstored, hphi⟩
        · exact hi.1 j (by omega)
      · intro j hj
        by_cases heq : j = n
        · subst j
          exact ⟨hndrift.trans hγ, hnmove.trans hmov, hndec⟩
        · exact hi.2 j (by omega)
  intro n hn
  have hi := hpast n hn
  have hsn := epoch_snapshot I U κ R n hm hn hsize hk hk'
    (by rw [hRzero]; exact hstart) (fun j hj => (hi.1 j hj).2.2.1) (fun j hj => (hi.2 j hj).1) n le_rfl
  rw [hRzero] at hsn
  obtain ⟨hrn, hfn, hRn, hsnstored, hpn⟩ := hi.1 n le_rfl
  exact ⟨hrn, hfn, hRn, hsnstored, hpn, hsn.1, hsn.2, fun j hj => (hi.2 j hj).2⟩

end MinCostFlow.IPM
