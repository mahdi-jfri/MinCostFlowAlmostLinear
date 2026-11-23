module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpacePhase4

import Mathlib.Tactic.Ring

/-!
# Combined monotone polynomial space bound for the first step (`AssemblyFirstStepSpaceTotal`)

Combines the four phase bounds (`AssemblyFirstStepSpacePhases13`, `AssemblyFirstStepSpacePhase4`)
and an arbitrary driver constant `c₀` into a single `PolyBound` (`asmFirstStepSpacePoly`) and a
monotone function below it (`asmFirstStepSpaceFn`), ready to plug directly into `AsmBrCoreStepAt`
(`AssemblyBranchStepIface.lean:86–174`):

* `asmFirstStepSpacePoly`: combined `PolyBound` parameterized by `c₀, cT, rQ, qE, qR, cw, Cγ, cγ, C_len, c_len, capExp` (free of `limbMul`, `depth`, `M`, `N`, `w`).
* `asmFirstStepSpaceFn`, `asmFirstStepSpaceFn_mono`, `asmFirstStepSpaceFn_le_poly`: monotone space
  function bounded by `asmFirstStepSpacePoly.eval`.
* `asmFirstPhase1Space_le_total`, `asmFirstPhase12Space_le_total`, `asmFirstPhase123Space_le_total`:
  prefix bounds for Phases 1, 1–2, and 1–3.
* `asmFirstStepSpace_le_poly_of_lenBound`: bounds the exact driver sum of Phases 1–4 plus `c₀` by
  `(asmFirstStepSpacePoly ...).eval (M + N + k + vCap + eCap + L + depth + words + editWords)`.
* `asmFirstStepSpacePolySub` and `asmFirstStepSpace_le_poly_of_chosenL`: specialization under
  `depth ≤ Expander.chosenL ((M + N) ^ 2)` and subpolynomial stretch
  `∀ m, impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))` (`0 < C_sp`), with fixed degree
  `(capExp + 7) * (4 * cw + 13)`.
* `asmFirstStepSpacePolyStd`, `asmFirstStepSpaceFnStd`, and `asmFirstStepSpace_le_poly_std`
  (with prefix bounds `asmFirstPhase1Space_le_std`, `asmFirstPhase12Space_le_std`,
  `asmFirstPhase123Space_le_std`): concrete specialization for `TS = tourBundleSpec` (`cT = 3`)
  and `rQ = qE = qR = 1`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **Combined polynomial space bound for the first step of a branch**, summing `c₀` and the
polynomials of Phases 1–4. Free of `limbMul`, `depth`, `M`, `N`, and `w`. -/
def asmFirstStepSpacePoly (c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp : ℕ) : PolyBound where
  coeff := c₀ + asmFirstPhase1SpacePoly.coeff +
    (asmFirstPhase2SpacePoly cT rQ cw Cγ cγ capExp).coeff +
    asmFirstPhase3SpacePoly.coeff +
    (asmFirstPhase4SpacePoly qE qR cw Cγ cγ C_len c_len capExp).coeff
  deg := (capExp + 7) * (cw * (c_len + 3) + cγ + c_len + 11)

/-- Monotone heap-space function for `AsmBrCoreStepAt.space`. -/
def asmFirstStepSpaceFn (c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp : ℕ) : ℕ → ℕ :=
  (asmFirstStepSpacePoly c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp).eval

/-- Subpolynomial-stretch specialization of `asmFirstStepSpacePoly` (degree `(capExp + 7) * (4 * cw + 13)`). -/
noncomputable def asmFirstStepSpacePolySub (c₀ cT rQ qE qR cw capExp : ℕ) (C_sp : ℝ) : PolyBound :=
  asmFirstStepSpacePoly c₀ cT rQ qE qR cw (gammaLinearConst C_sp) 1 (lenBoundLinearConst C_sp) 1 capExp

/-- Concrete specialization for `tourBundleSpec` (`cT = 3`) and `rQ = qE = qR = 1`. -/
noncomputable def asmFirstStepSpacePolyStd (c₀ cw capExp : ℕ) (C_sp : ℝ) : PolyBound :=
  asmFirstStepSpacePolySub c₀ 3 1 1 1 cw capExp C_sp

/-- Monotone heap-space function for the concrete `tourBundleSpec` (`cT = 3`, `rQ = qE = qR = 1`)
specialization. -/
noncomputable def asmFirstStepSpaceFnStd (c₀ cw capExp : ℕ) (C_sp : ℝ) : ℕ → ℕ :=
  (asmFirstStepSpacePolyStd c₀ cw capExp C_sp).eval

end

/-! ## Pure degree/sum helpers -/

private lemma total_deg_ge_three (capExp cw cγ c_len : ℕ) :
    3 ≤ (capExp + 7) * (cw * (c_len + 3) + cγ + c_len + 11) :=
  calc 3 ≤ 7 * 11 := by decide
    _ ≤ (capExp + 7) * (cw * (c_len + 3) + cγ + c_len + 11) :=
      Nat.mul_le_mul (by omega) (by omega)

private lemma total_deg_ge_p2 (capExp cw cγ c_len : ℕ) :
    (capExp + 7) * (cw + cγ + 4) ≤ (capExp + 7) * (cw * (c_len + 3) + cγ + c_len + 11) :=
  Nat.mul_le_mul_left _ (by
    have h1 : cw ≤ cw * (c_len + 3) := Nat.le_mul_of_pos_right cw (by omega)
    omega)

private lemma polyBound_eval_le_of_deg {pb : PolyBound} {D X : ℕ} (hdeg : pb.deg ≤ D) :
    pb.eval X ≤ pb.coeff * (X + 2) ^ D :=
  Nat.mul_le_mul_left pb.coeff (Nat.pow_le_pow_right (by omega) hdeg)

private lemma poly_sum4_le {c₀ c₁ c₂ c₃ c₄ P : ℕ} {a₁ a₂ a₃ a₄ : ℕ}
    (hP : 1 ≤ P) (h₁ : a₁ ≤ c₁ * P) (h₂ : a₂ ≤ c₂ * P) (h₃ : a₃ ≤ c₃ * P) (h₄ : a₄ ≤ c₄ * P) :
    c₀ + a₁ + a₂ + a₃ + a₄ ≤ (c₀ + c₁ + c₂ + c₃ + c₄) * P := by
  have h0 : c₀ ≤ c₀ * P := Nat.le_mul_of_pos_right c₀ hP
  have he : (c₀ + c₁ + c₂ + c₃ + c₄) * P = c₀ * P + c₁ * P + c₂ * P + c₃ * P + c₄ * P := by ring
  omega

public section

/-- Every `PolyBound.eval` is monotone. -/
theorem polyBound_eval_mono (pb : PolyBound) : Monotone pb.eval := fun _ _ hab =>
  Nat.mul_le_mul_left pb.coeff (Nat.pow_le_pow_left (by omega) pb.deg)

/-- `asmFirstStepSpaceFn` is monotone (`AsmBrCoreStepAt.space_mono`). -/
theorem asmFirstStepSpaceFn_mono (c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp : ℕ) :
    Monotone (asmFirstStepSpaceFn c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp) :=
  polyBound_eval_mono _

/-- `asmFirstStepSpaceFn` is bounded by `asmFirstStepSpacePoly.eval` (`AsmBrCoreStepAt.space_le`). -/
theorem asmFirstStepSpaceFn_le_poly (c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp x : ℕ) :
    asmFirstStepSpaceFn c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp x ≤
      (asmFirstStepSpacePoly c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp).eval x :=
  le_rfl

/-- `asmFirstStepSpaceFnStd` is monotone. -/
theorem asmFirstStepSpaceFnStd_mono (c₀ cw capExp : ℕ) (C_sp : ℝ) :
    Monotone (asmFirstStepSpaceFnStd c₀ cw capExp C_sp) :=
  polyBound_eval_mono _

/-- `asmFirstStepSpaceFnStd` is bounded by `asmFirstStepSpacePolyStd.eval`. -/
theorem asmFirstStepSpaceFnStd_le_poly (c₀ cw capExp : ℕ) (C_sp : ℝ) (x : ℕ) :
    asmFirstStepSpaceFnStd c₀ cw capExp C_sp x ≤
      (asmFirstStepSpacePolyStd c₀ cw capExp C_sp).eval x :=
  le_rfl

/-- Phase 1 space alone (`6 + asmFirstScanBatchSpace vCap eCap words`) is at most
`asmFirstStepSpaceFn`. -/
theorem asmFirstPhase1Space_le_total (c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp
    M N k vCap eCap L depth words editWords : ℕ) :
    6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstStepSpaceFn c₀ cT rQ qE qR cw Cγ cγ C_len c_len capExp
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set X := M + N + k + vCap + eCap + L + depth + words + editWords
  set D := (capExp + 7) * (cw * (c_len + 3) + cγ + c_len + 11)
  have h1 : 6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstPhase1SpacePoly.coeff * (X + 2) ^ D :=
    (asmFirstPhase1Space_le_poly M N k vCap eCap L depth words editWords).trans
      (polyBound_eval_le_of_deg (le_trans (by decide) (total_deg_ge_three capExp cw cγ c_len)))
  have hle := poly_sum4_le (c₀ := c₀) (c₁ := asmFirstPhase1SpacePoly.coeff)
    (c₂ := (asmFirstPhase2SpacePoly cT rQ cw Cγ cγ capExp).coeff)
    (c₃ := asmFirstPhase3SpacePoly.coeff)
    (c₄ := (asmFirstPhase4SpacePoly qE qR cw Cγ cγ C_len c_len capExp).coeff)
    (Nat.one_le_pow D (X + 2) (by omega)) h1 (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  exact le_trans (by omega) hle

/-- Phases 1–2 prefix space (`6 + asmFirstScanBatchSpace + newActTotalSpace`) is at most
`asmFirstStepSpaceFn`. -/
theorem asmFirstPhase12Space_le_total
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {Cγ cγ C_len c_len : ℕ}
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ)
    {Ψ : BundleTreeState depth → ℕ}
    {TS : BundleTourSpec} {cT rQ qE qR c₀ : ℕ}
    (hTS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    {b k M N vCap eCap words editWords : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap) :
    6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace TS rQ impl w x.xRest tr ord newComps ≤
      asmFirstStepSpaceFn c₀ cT rQ qE qR impl.cw Cγ cγ C_len c_len capExp
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set X := M + N + k + vCap + eCap + L + depth + words + editWords
  set D := (capExp + 7) * (impl.cw * (c_len + 3) + cγ + c_len + 11)
  have h1 : 6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstPhase1SpacePoly.coeff * (X + 2) ^ D :=
    (asmFirstPhase1Space_le_poly M N k vCap eCap L depth words editWords).trans
      (polyBound_eval_le_of_deg (le_trans (by decide) (total_deg_ge_three capExp impl.cw cγ c_len)))
  have h2 : newActTotalSpace TS rQ impl w x.xRest tr ord newComps ≤
      (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).coeff * (X + 2) ^ D :=
    (asmFirstPhase2Space_le_poly (rQ := rQ) (k := k) (editWords := editWords)
      hγ hTS hrep hM hN hGE hNC_len hSum).trans
      (polyBound_eval_le_of_deg (total_deg_ge_p2 capExp impl.cw cγ c_len))
  have hle := poly_sum4_le (c₀ := c₀) (c₁ := asmFirstPhase1SpacePoly.coeff)
    (c₂ := (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).coeff)
    (c₃ := asmFirstPhase3SpacePoly.coeff)
    (c₄ := (asmFirstPhase4SpacePoly qE qR impl.cw Cγ cγ C_len c_len capExp).coeff)
    (Nat.one_le_pow D (X + 2) (by omega)) h1 h2 (Nat.zero_le _) (Nat.zero_le _)
  exact le_trans (by omega) hle

/-- Phases 1–3 prefix space (`6 + asmFirstScanBatchSpace + newActTotalSpace + asmFirstPhase3Space`)
is at most `asmFirstStepSpaceFn`. -/
theorem asmFirstPhase123Space_le_total
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {Cγ cγ C_len c_len : ℕ}
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ)
    {Ψ : BundleTreeState depth → ℕ}
    {TS : BundleTourSpec} {cT rQ qE qR c₀ : ℕ}
    (hTS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    {b k M N vCap eCap words editWords nDel : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap)
    (hnDel : nDel ≤ words) :
    6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace TS rQ impl w x.xRest tr ord newComps +
      asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel ≤
      asmFirstStepSpaceFn c₀ cT rQ qE qR impl.cw Cγ cγ C_len c_len capExp
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set X := M + N + k + vCap + eCap + L + depth + words + editWords
  set D := (capExp + 7) * (impl.cw * (c_len + 3) + cγ + c_len + 11)
  have hrep0 := hrep
  obtain ⟨-, -, -, hvc, hec, -, hsc, -, -⟩ := hrep0
  dsimp only at hvc hec
  have hslotCap : x.xRest.slotCap ≤ 2 * (vCap + eCap + 2) ^ 2 := by
    rw [← hvc, ← hec]; exact hsc
  have h1 : 6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstPhase1SpacePoly.coeff * (X + 2) ^ D :=
    (asmFirstPhase1Space_le_poly M N k vCap eCap L depth words editWords).trans
      (polyBound_eval_le_of_deg (le_trans (by decide) (total_deg_ge_three capExp impl.cw cγ c_len)))
  have h2 : newActTotalSpace TS rQ impl w x.xRest tr ord newComps ≤
      (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).coeff * (X + 2) ^ D :=
    (asmFirstPhase2Space_le_poly (rQ := rQ) (k := k) (editWords := editWords)
      hγ hTS hrep hM hN hGE hNC_len hSum).trans
      (polyBound_eval_le_of_deg (total_deg_ge_p2 capExp impl.cw cγ c_len))
  have h3 : asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel ≤
      asmFirstPhase3SpacePoly.coeff * (X + 2) ^ D :=
    (asmFirstPhase3Space_le_poly (M := M) (N := N) (k := k) (L := L) (depth := depth)
      (editWords := editWords) hslotCap hnDel).trans
      (polyBound_eval_le_of_deg (total_deg_ge_three capExp impl.cw cγ c_len))
  have hle := poly_sum4_le (c₀ := c₀) (c₁ := asmFirstPhase1SpacePoly.coeff)
    (c₂ := (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).coeff)
    (c₃ := asmFirstPhase3SpacePoly.coeff)
    (c₄ := (asmFirstPhase4SpacePoly qE qR impl.cw Cγ cγ C_len c_len capExp).coeff)
    (Nat.one_le_pow D (X + 2) (by omega)) h1 h2 h3 (Nat.zero_le _)
  exact le_trans (by omega) hle

/-- **Combined space bound for Phases 1–4 plus `c₀`**, given an explicit walk-length bound
`⌈lenBound (impl.γ_ℓ M) depth⌉₊ ≤ C_len * (M + N + 2) ^ c_len` and polynomial stretch. -/
theorem asmFirstStepSpace_le_poly_of_lenBound
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {Cγ cγ C_len c_len : ℕ}
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ)
    {Ψ : BundleTreeState depth → ℕ}
    {TS : BundleTourSpec} {cT rQ qE qR c₀ : ℕ}
    (hTS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    {b k M N vCap eCap words editWords nDel nSp nU nEd lo hi : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem mem₃ : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    {S6 : BucketSpannerState x.xRest.cap} {tasks : List SpanUpdTask}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hdepth1 : 1 ≤ depth)
    (hlen : ⌈lenBound (impl.γ_ℓ M) depth⌉₊ ≤ C_len * (M + N + 2) ^ c_len)
    (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap)
    (hnDel : nDel ≤ words)
    (htasks_len : tasks.length ≤ x.xRest.slotCap)
    (hnew_len : hi - lo ≤ x.xRest.slotCap)
    (hnSp : nSp ≤ vCap) (hnU : nU ≤ words) (hnEd : nEd ≤ editWords)
    (hS6_valid : ∀ (j : Fin x.xRest.cap) (d : DSHist), S6 j = some d →
      P4HistValid (asmBrSP impl w depth x.xRest) d)
    (htasks_valid : ∀ t ∈ tasks,
      P4TaskValid (asmBrSP impl w depth x.xRest) S6 mem₃ t ∧
      t.W ≤ asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel) :
    let SP := asmBrSP impl w depth x.xRest
    c₀ + 6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace TS rQ impl w x.xRest tr ord newComps +
      asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel +
      p4WsSize eCap + (tasks.map (p4TaskSpace SP S6 mem₃)).sum +
      rangeCost (p4NewSpace SP (p4SpanAfter SP S6 mem₃ tasks)) lo hi +
      asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (asmFirstStepSpacePoly c₀ cT rQ qE qR impl.cw Cγ cγ C_len c_len capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  intro SP
  set X := M + N + k + vCap + eCap + L + depth + words + editWords
  set D := (capExp + 7) * (impl.cw * (c_len + 3) + cγ + c_len + 11)
  have hrep0 := hrep
  obtain ⟨hrepA, -, -, hvc, hec, -, hsc, -, -⟩ := hrep0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXr, -, -, -, -⟩ := hrepA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmod⟩ := hXr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hCapS, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hmMax, -, -⟩ := hmod
  dsimp only at hvc hec hCapS hmMax
  have hslotCap : x.xRest.slotCap ≤ 2 * (vCap + eCap + 2) ^ 2 := by
    rw [← hvc, ← hec]; exact hsc
  have hsp : SP.vCap + SP.eCap + 2 ≤ (M + N + 2) ^ (capExp + 7) := by
    have := hCapS.1; rw [hM, hN] at this; exact this
  have hP3 := asmFirstPhase3Space_le_poly (M := M) (N := N) (k := k) (L := L) (depth := depth)
    (editWords := editWords) hslotCap hnDel
  have h1 : 6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstPhase1SpacePoly.coeff * (X + 2) ^ D :=
    (asmFirstPhase1Space_le_poly M N k vCap eCap L depth words editWords).trans
      (polyBound_eval_le_of_deg (le_trans (by decide) (total_deg_ge_three capExp impl.cw cγ c_len)))
  have h2 : newActTotalSpace TS rQ impl w x.xRest tr ord newComps ≤
      (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).coeff * (X + 2) ^ D :=
    (asmFirstPhase2Space_le_poly (rQ := rQ) (k := k) (editWords := editWords)
      hγ hTS hrep hM hN hGE hNC_len hSum).trans
      (polyBound_eval_le_of_deg (total_deg_ge_p2 capExp impl.cw cγ c_len))
  have h3 : asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel ≤
      asmFirstPhase3SpacePoly.coeff * (X + 2) ^ D :=
    hP3.trans (polyBound_eval_le_of_deg (total_deg_ge_three capExp impl.cw cγ c_len))
  have h4 : p4WsSize eCap + (tasks.map (p4TaskSpace SP S6 mem₃)).sum +
      rangeCost (p4NewSpace SP (p4SpanAfter SP S6 mem₃ tasks)) lo hi +
      asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (asmFirstPhase4SpacePoly qE qR impl.cw Cγ cγ C_len c_len capExp).coeff * (X + 2) ^ D :=
    asmFirstPhase4Space_le_poly_of_lenBound SP
      (k := k) (vCap := vCap) (eCap := eCap) (L := L) (words := words) (editWords := editWords)
      (qE := qE) (qR := qR) (capExp := capExp)
      (W_max := asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel)
      hdepth1 rfl (hmMax.trans hM) hsp (hγ M) hlen hP3
      (htasks_len.trans hslotCap) (hnew_len.trans hslotCap) hnSp hnU hnEd hS6_valid htasks_valid
  have hle := poly_sum4_le (c₀ := c₀) (c₁ := asmFirstPhase1SpacePoly.coeff)
    (c₂ := (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).coeff)
    (c₃ := asmFirstPhase3SpacePoly.coeff)
    (c₄ := (asmFirstPhase4SpacePoly qE qR impl.cw Cγ cγ C_len c_len capExp).coeff)
    (Nat.one_le_pow D (X + 2) (by omega)) h1 h2 h3 h4
  exact le_trans (by omega) hle

/-- **Combined space bound under `chosenL` and subpolynomial stretch.** Takes
`depth ≤ Expander.chosenL ((M + N) ^ 2)` and
`∀ m, impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))` (`0 < C_sp`). -/
theorem asmFirstStepSpace_le_poly_of_chosenL
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {C_sp : ℝ} (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {Ψ : BundleTreeState depth → ℕ}
    {TS : BundleTourSpec} {cT rQ qE qR c₀ : ℕ}
    (hTS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    {b k M N vCap eCap words editWords nDel nSp nU nEd lo hi : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem mem₃ : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    {S6 : BucketSpannerState x.xRest.cap} {tasks : List SpanUpdTask}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hdepth1 : 1 ≤ depth)
    (hdepth : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap)
    (hnDel : nDel ≤ words)
    (htasks_len : tasks.length ≤ x.xRest.slotCap)
    (hnew_len : hi - lo ≤ x.xRest.slotCap)
    (hnSp : nSp ≤ vCap) (hnU : nU ≤ words) (hnEd : nEd ≤ editWords)
    (hS6_valid : ∀ (j : Fin x.xRest.cap) (d : DSHist), S6 j = some d →
      P4HistValid (asmBrSP impl w depth x.xRest) d)
    (htasks_valid : ∀ t ∈ tasks,
      P4TaskValid (asmBrSP impl w depth x.xRest) S6 mem₃ t ∧
      t.W ≤ asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel) :
    let SP := asmBrSP impl w depth x.xRest
    c₀ + 6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace TS rQ impl w x.xRest tr ord newComps +
      asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel +
      p4WsSize eCap + (tasks.map (p4TaskSpace SP S6 mem₃)).sum +
      rangeCost (p4NewSpace SP (p4SpanAfter SP S6 mem₃ tasks)) lo hi +
      asmFirstPhase4Room vCap eCap nSp nU nEd qE qR ≤
      (asmFirstStepSpacePolySub c₀ cT rQ qE qR impl.cw capExp C_sp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) :=
  asmFirstStepSpace_le_poly_of_lenBound
    (fun m => by simpa [pow_one] using ceil_gamma_le_linear_of_subpoly hC hγ m)
    hTS hrep hM hN hdepth1
    (by simpa [pow_one] using ceil_lenBound_le_linear_of_chosenL hC hγ hdepth)
    hGE hNC_len hSum hnDel htasks_len hnew_len hnSp hnU hnEd hS6_valid htasks_valid

/-- **Concrete first-step space bound for `tourBundleSpec` and `rQ = qE = qR = 1`.** Directly
matches the driver sum in `AsmBrCoreStepAt`. -/
theorem asmFirstStepSpace_le_poly_std
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {C_sp : ℝ} (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {Ψ : BundleTreeState depth → ℕ} {c₀ : ℕ}
    {b k M N vCap eCap words editWords nDel nSp nU nEd lo hi : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem mem₃ : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    {S6 : BucketSpannerState x.xRest.cap} {tasks : List SpanUpdTask}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hdepth1 : 1 ≤ depth)
    (hdepth : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap)
    (hnDel : nDel ≤ words)
    (htasks_len : tasks.length ≤ x.xRest.slotCap)
    (hnew_len : hi - lo ≤ x.xRest.slotCap)
    (hnSp : nSp ≤ vCap) (hnU : nU ≤ words) (hnEd : nEd ≤ editWords)
    (hS6_valid : ∀ (j : Fin x.xRest.cap) (d : DSHist), S6 j = some d →
      P4HistValid (asmBrSP impl w depth x.xRest) d)
    (htasks_valid : ∀ t ∈ tasks,
      P4TaskValid (asmBrSP impl w depth x.xRest) S6 mem₃ t ∧
      t.W ≤ asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel) :
    let SP := asmBrSP impl w depth x.xRest
    c₀ + 6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace tourBundleSpec 1 impl w x.xRest tr ord newComps +
      asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel +
      p4WsSize eCap + (tasks.map (p4TaskSpace SP S6 mem₃)).sum +
      rangeCost (p4NewSpace SP (p4SpanAfter SP S6 mem₃ tasks)) lo hi +
      asmFirstPhase4Room vCap eCap nSp nU nEd 1 1 ≤
      asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp
        (M + N + k + vCap + eCap + L + depth + words + editWords) :=
  asmFirstStepSpace_le_poly_of_chosenL hC hγ (fun len => by simp [tourBundleSpec]; omega)
    hrep hM hN hdepth1 hdepth hGE hNC_len hSum hnDel htasks_len hnew_len hnSp hnU hnEd
    hS6_valid htasks_valid

/-- Phase 1 space is at most `asmFirstStepSpaceFnStd`. -/
theorem asmFirstPhase1Space_le_std (c₀ cw capExp : ℕ) (C_sp : ℝ)
    (M N k vCap eCap L depth words editWords : ℕ) :
    6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstStepSpaceFnStd c₀ cw capExp C_sp
        (M + N + k + vCap + eCap + L + depth + words + editWords) :=
  asmFirstPhase1Space_le_total c₀ 3 1 1 1 cw (gammaLinearConst C_sp) 1
    (lenBoundLinearConst C_sp) 1 capExp M N k vCap eCap L depth words editWords

/-- Phases 1–2 prefix space for `tourBundleSpec` (`rQ = 1`) is at most `asmFirstStepSpaceFnStd`. -/
theorem asmFirstPhase12Space_le_std
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {C_sp : ℝ} (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {Ψ : BundleTreeState depth → ℕ} {c₀ : ℕ}
    {b k M N vCap eCap words editWords : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap) :
    6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace tourBundleSpec 1 impl w x.xRest tr ord newComps ≤
      asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp
        (M + N + k + vCap + eCap + L + depth + words + editWords) :=
  asmFirstPhase12Space_le_total
    (C_len := lenBoundLinearConst C_sp) (c_len := 1) (qE := 1) (qR := 1) (c₀ := c₀)
    (fun m => by simpa [pow_one] using ceil_gamma_le_linear_of_subpoly hC hγ m)
    (fun len => by simp [tourBundleSpec]; omega) hrep hM hN hGE hNC_len hSum

/-- Phases 1–3 prefix space for `tourBundleSpec` (`rQ = 1`) is at most `asmFirstStepSpaceFnStd`. -/
theorem asmFirstPhase123Space_le_std
    {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {C_sp : ℝ} (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {Ψ : BundleTreeState depth → ℕ} {c₀ : ℕ}
    {b k M N vCap eCap words editWords nDel : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap)
    (hnDel : nDel ≤ words) :
    6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace tourBundleSpec 1 impl w x.xRest tr ord newComps +
      asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel ≤
      asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp
        (M + N + k + vCap + eCap + L + depth + words + editWords) :=
  asmFirstPhase123Space_le_total
    (C_len := lenBoundLinearConst C_sp) (c_len := 1) (qE := 1) (qR := 1) (c₀ := c₀)
    (fun m => by simpa [pow_one] using ceil_gamma_le_linear_of_subpoly hC hγ m)
    (fun len => by simp [tourBundleSpec]; omega) hrep hM hN hGE hNC_len hSum hnDel

end

end MinCostFlow.SparseCore.Program
