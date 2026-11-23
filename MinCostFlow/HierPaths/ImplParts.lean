module

public import MinCostFlow.HierPaths.InitEntry
public import MinCostFlow.HierPaths.InitBlockLen
public import MinCostFlow.HierPaths.InitProgRest
import MinCostFlow.HierPaths.QueryProgSpec
import MinCostFlow.HierPaths.DelProgSpec

/-!
# `HierPathDSExists` from the four parts

The implementation has four parts: the static construction (`StaticProcSpec`), the rest of
`Init` (`RestProcSpec`), `Delete` (`DelProcSpec`) and `GetPath` (`QueryProcSpec`). With the
bounds on the length of the block of `Init`, they give `HierPathDSExists`
(`hierPathDSExists_of_parts`), through `initProc_spec` and `hierPathDSExists_of_procs`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- **`HierPathDSExists` from the four parts.** -/
theorem hierPathDSExists_of_parts
    (h : ∀ a : ℕ, 1 ≤ a → ∃ (PS PR PD PQ : HierProc) (Ks K Kb : ℕ) (KD KQ : ℝ)
      (sS sR sB sD sQ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
      (CS cS CR cR CB cB CD cD CQ cQ cwS cwD cwQ : ℕ),
      StaticProcSpec a PS Ks sS CS cS cwS ∧ RestProcSpec a PR K sR CR cR ∧
      SpaceForm a sB CB cB ∧
      (∀ (S : StaticData) (G : Graph) (phiNum phiDen M : ℕ),
        S.Good a (dOf phiNum phiDen) M G →
        (initBlock S a G phiNum phiDen M).length ≤ Kb * G.m * gammaHP a (dOf phiNum phiDen) M ∧
        (initBlock S a G phiNum phiDen M).length ≤ sB phiNum phiDen G.n G.m M) ∧
      DelProcSpec a PD KD sD CD cD cwD ∧ QueryProcSpec a PQ KQ sQ CQ cQ cwQ) :
    HierPathDSExists := by
  refine hierPathDSExists_of_procs fun a ha => ?_
  obtain ⟨PS, PR, PD, PQ, Ks, K, Kb, KD, KQ, sS, sR, sB, sD, sQ, CS, cS, CR, cR, CB, cB, CD, cD,
    CQ, cQ, cwS, cwD, cwQ, hS, hR, hB, hlen, hD, hQ⟩ := h a ha
  exact ⟨initProc PS PR, PD, PQ, _, KD, KQ, _, sD, sQ, _, _, CD, cD, CQ, cQ, cwS, cwD, cwQ,
    initProc_spec a ha PS PR Ks K Kb sS sR sB CS cS CR cR CB cB cwS hS hR hB
      (fun S G phiNum phiDen M hg => (hlen S G phiNum phiDen M hg).1)
      (fun S G phiNum phiDen M hg => (hlen S G phiNum phiDen M hg).2), hD, hQ⟩

/-- The space bound of the block: `2000 · m · Γ`. -/
noncomputable def blockSpace (a : ℕ) (phiNum phiDen _n m M : ℕ) : ℕ :=
  2000 * m * gammaHP a (dOf phiNum phiDen) M

theorem blockSpace_form (a : ℕ) : SpaceForm a (blockSpace a) 2000 2 := by
  intro phiNum phiDen n m M h1 h2
  unfold blockSpace
  rw [dOf, nat_ceil_div_eq h1 h2]
  set Γ := gammaHP a ((phiDen + phiNum - 1) / phiNum) M
  set B := phiDen + n + m + M + Γ + 2
  have hm : m ≤ B := by omega
  have hΓ : Γ ≤ B := by omega
  calc 2000 * m * Γ = 2000 * (m * Γ) := by ring
    _ ≤ 2000 * (B * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hm hΓ)
    _ = 2000 * B ^ 2 := by ring

/-- **`HierPathDSExists` from the four procedures.** The bounds on the block of `Init` are
`length_initBlock_le` (`Kb = 2000`, space `blockSpace`). -/
theorem hierPathDSExists_of_progs
    (h : ∀ a : ℕ, 1 ≤ a → ∃ (PS PR PD PQ : HierProc) (Ks K : ℕ) (KD KQ : ℝ)
      (sS sR sD sQ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
      (CS cS CR cR CD cD CQ cQ cwS cwD cwQ : ℕ),
      StaticProcSpec a PS Ks sS CS cS cwS ∧ RestProcSpec a PR K sR CR cR ∧
      DelProcSpec a PD KD sD CD cD cwD ∧ QueryProcSpec a PQ KQ sQ CQ cQ cwQ) :
    HierPathDSExists := by
  refine hierPathDSExists_of_parts fun a ha => ?_
  obtain ⟨PS, PR, PD, PQ, Ks, K, KD, KQ, sS, sR, sD, sQ, CS, cS, CR, cR, CD, cD, CQ, cQ, cwS,
    cwD, cwQ, hS, hR, hD, hQ⟩ := h a ha
  refine ⟨PS, PR, PD, PQ, Ks, K, 2000, KD, KQ, sS, sR, blockSpace a, sD, sQ, CS, cS, CR, cR,
    2000, 2, CD, cD, CQ, cQ, cwS, cwD, cwQ, hS, hR, blockSpace_form a,
    fun S G phiNum phiDen M hg => ⟨length_initBlock_le S ha G phiNum phiDen hg,
      length_initBlock_le S ha G phiNum phiDen hg⟩, hD, hQ⟩

/-- **`HierPathDSExists` from the static construction, the builder of the block, `Delete` and
`GetPath`.** The rest of `Init` is `restProc` (the builder, then `moveDown`). -/
theorem hierPathDSExists_of_builder
    (h : ∀ a : ℕ, 1 ≤ a → ∃ (PS PB PD PQ : HierProc) (Ks K : ℕ) (KD KQ : ℝ)
      (sS sR sD sQ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
      (CS cS CR cR CD cD CQ cQ cwS cwD cwQ : ℕ),
      StaticProcSpec a PS Ks sS CS cS cwS ∧ BuildProcSpec a PB K sR CR cR ∧
      DelProcSpec a PD KD sD CD cD cwD ∧ QueryProcSpec a PQ KQ sQ CQ cQ cwQ) :
    HierPathDSExists := by
  refine hierPathDSExists_of_progs fun a ha => ?_
  obtain ⟨PS, PB, PD, PQ, Ks, K, KD, KQ, sS, sR, sD, sQ, CS, cS, CR, cR, CD, cD, CQ, cQ, cwS,
    cwD, cwQ, hS, hB, hD, hQ⟩ := h a ha
  exact ⟨PS, restProc PB, PD, PQ, Ks, K + 80, KD, KQ, sS, sR, sD, sQ, CS, cS, CR, cR, CD, cD,
    CQ, cQ, cwS, cwD, cwQ, hS, restProc_spec a PB K sR CR cR hB, hD, hQ⟩

/-- The verified query procedure supplies the query clause in the hierarchy assembly. -/
theorem hierPathDSExists_of_initBuilder_delete
    (h : ∀ a : ℕ, 1 ≤ a → ∃ (PS PB PD : HierProc) (Ks K : ℕ) (KD : ℝ)
      (sS sR sD : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CS cS CR cR CD cD cwS cwD : ℕ),
      StaticProcSpec a PS Ks sS CS cS cwS ∧ BuildProcSpec a PB K sR CR cR ∧
      DelProcSpec a PD KD sD CD cD cwD) :
    HierPathDSExists := by
  refine hierPathDSExists_of_builder fun a ha => ?_
  obtain ⟨PS, PB, PD, Ks, K, KD, sS, sR, sD, CS, cS, CR, cR, CD, cD, cwS, cwD, hS, hB, hD⟩ :=
    h a ha
  exact ⟨PS, PB, PD, hierQueryProc, Ks, K, KD, 10000, sS, sR, sD, hierQuerySpace a,
    CS, cS, CR, cR, CD, cD, 9, 1, cwS, cwD, 1, hS, hB, hD, hierQueryProc_spec a⟩

/-- The verified Delete and GetPath procedures leave only the two initialization builders
as inputs to the hierarchy assembly. -/
theorem hierPathDSExists_of_initBuilders
    (h : ∀ a : ℕ, 1 ≤ a → ∃ (PS PB : HierProc) (Ks K : ℕ)
      (sS sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CS cS CR cR cwS : ℕ),
      StaticProcSpec a PS Ks sS CS cS cwS ∧ BuildProcSpec a PB K sR CR cR) :
    HierPathDSExists := by
  refine hierPathDSExists_of_initBuilder_delete fun a ha => ?_
  obtain ⟨PS, PB, Ks, K, sS, sR, CS, cS, CR, cR, cwS, hS, hB⟩ := h a ha
  exact ⟨PS, PB, hierDeleteProc, Ks, K, 106496, sS, sR, hierDeleteSpace,
    CS, cS, CR, cR, 11 * 16 ^ 12, 12, cwS, 1, hS, hB, hierDeleteProc_spec a⟩

end MinCostFlow.HierPaths
