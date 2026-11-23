module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFull
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Prog
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActMath
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Defs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial space bounds for Phases 1, 2, and 3 of the first step (`AssemblyFirstStepSpacePhases13`)

Bounds the heap space of Phases 1, 2, and 3 of the first step of a branch (`AsmBrCoreStepAt`) by
explicit `PolyBound`s in `X = M + N + k + vCap + eCap + L + depth + words + editWords`:
* Phase 1 (`asmFirstPhase1Space_le_poly`): `6 + asmFirstScanBatchSpace vCap eCap words ≤ 11 * (X + 2)`.
* Phase 2 (`asmFirstPhase2Space_le_poly`): `newActTotalSpace TS rQ impl w y tr ord newComps` is at
  most `(asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).eval X`, using `asmBrFullRep`,
  `newComps.length ≤ words`, `newCompsBucketSum ≤ y.slotCap`, and `⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ`.
* Phase 3 (`asmFirstPhase3Space_le_poly`): `asmFirstPhase3Space slotCap vCap eCap words editWords nDel`
  is at most `asmFirstPhase3SpacePoly.eval X` (`826 * (X + 2) ^ 3`), using
  `slotCap ≤ 2 * (vCap + eCap + 2) ^ 2` and `nDel ≤ words`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- **Polynomial space bound for Phase 1** (including the 6-word output record header at `h`). -/
def asmFirstPhase1SpacePoly : PolyBound where
  coeff := 11
  deg := 1

/-- **Polynomial space bound for Phase 2** (`newActTotalSpace`), parameterized by the linear list
space constant `cT` (`TS.listSpace len ≤ cT * (len + 1)`), the root-query space `rQ`, the
sparsifier word exponent `cw`, the stretch bound `Cγ · (m + 2) ^ cγ`, and `capExp`. -/
def asmFirstPhase2SpacePoly (cT rQ cw Cγ cγ capExp : ℕ) : PolyBound where
  coeff := 202 + (rQ + 6 * cT + 57) + 2 * (125 + 2 * 72 ^ cw + 30 * (Cγ + 1))
  deg := (capExp + 7) * (cw + cγ + 4)

/-- **Polynomial space bound for Phase 3** (`asmFirstPhase3Space`), independent of `capExp`, `cw`,
and stretch. -/
def asmFirstPhase3SpacePoly : PolyBound where
  coeff := 826
  deg := 3

end

/-! ## Pure helpers -/

private lemma list_sum_map_le_mul_p13 {α : Type*} (l : List α) (f : α → ℕ) (K : ℕ)
    (h : ∀ x ∈ l, f x ≤ K) : (l.map f).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    omega

private lemma list_mem_le_sum_map {α : Type*} (l : List α) (f : α → ℕ) {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).sum := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hrest
    · omega
    · have := ih hrest; omega

private lemma outCoreOrder_length_le_two_eCap {depth eCap : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (hGE : ∀ e ∈ tr.cs.G.E, e < eCap) (v : ℕ) :
    (outCoreOrder tr ord v).length ≤ 2 * eCap := by
  classical
  have hex : ∃ (C' : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C' ℓ tr.cs) (ρ' : Rotation tr.cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  let rot := coreRotation (L := tr.cs.lsf) hex.choose_spec.choose_spec.choose_spec.choose
    hex.choose_spec.choose_spec.choose.hG_val (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)
  have heq : outCoreOrder tr ord v = rot.order v := by
    unfold outCoreOrder
    rw [dite_eq_left hex]
  rw [heq, ← List.toFinset_card_of_nodup (rot.nodup v)]
  have hsub : (rot.order v).toFinset ⊆ Finset.range eCap ×ˢ (Finset.univ : Finset Bool) := by
    intro x hx
    rw [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, Finset.mem_univ _⟩
    have hxE : x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E :=
      ((rot.mem_order v x).mp (List.mem_toFinset.mp hx)).1
    exact hGE x.1 (Finset.sdiff_subset hxE)
  exact (Finset.card_le_card hsub).trans (by simp [Finset.card_product]; omega)

private lemma compCoreEdges_card_le_eCap {depth eCap : ℕ} {tr : BundleTreeState depth}
    (hGE : ∀ e ∈ tr.cs.G.E, e < eCap) (C : Finset ℕ) :
    (compCoreEdges tr C).card ≤ eCap := by
  have hsub : compCoreEdges tr C ⊆ Finset.range eCap := fun e he =>
    Finset.mem_range.mpr (hGE e (Finset.sdiff_subset (Finset.mem_filter.mp he).1))
  exact (Finset.card_le_card hsub).trans (Finset.card_range eCap).le

private lemma asmFiSpanCapSpace_le {B cw Cγ cγ depth spV spE g : ℕ} (hB : 2 ≤ B)
    (hsp : spV + spE + 2 ≤ B) (hdepth : depth + 1 ≤ B) (hg : g ≤ Cγ * B ^ cγ) :
    10 + 13 * spE + spV +
      (100 * ((depth + 1) * (spV + spE + 1)) +
        (2 * (36 * (spV + 2 * spE + 1)) ^ cw + 30 * (spE + 1) * (g + 1) + 3 * spV +
          dynGraphSize spV spE + spE + 10)) ≤
      (125 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 2) := by
  have hBpos : 0 < B := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → B ^ a ≤ B ^ b := fun h => Nat.pow_le_pow_right hBpos h
  have hE : B ≤ B ^ (cw + cγ + 2) := by simpa using hpw (a := 1) (b := cw + cγ + 2) (by omega)
  have p1 : 100 * ((depth + 1) * (spV + spE + 1)) ≤ 100 * B ^ (cw + cγ + 2) := by
    have h1 : (depth + 1) * (spV + spE + 1) ≤ B * B := Nat.mul_le_mul hdepth (by omega)
    have h2 : B * B ≤ B ^ (cw + cγ + 2) := by rw [← pow_two]; exact hpw (by omega)
    omega
  have p2 : 2 * (36 * (spV + 2 * spE + 1)) ^ cw ≤ 2 * 72 ^ cw * B ^ (cw + cγ + 2) := by
    have h1 : 36 * (spV + 2 * spE + 1) ≤ 72 * B := by omega
    have h2 : (36 * (spV + 2 * spE + 1)) ^ cw ≤ 72 ^ cw * B ^ cw := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left h1 cw
    calc 2 * (36 * (spV + 2 * spE + 1)) ^ cw ≤ 2 * (72 ^ cw * B ^ cw) :=
          Nat.mul_le_mul_left 2 h2
      _ ≤ 2 * (72 ^ cw * B ^ (cw + cγ + 2)) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (hpw (by omega)))
      _ = 2 * 72 ^ cw * B ^ (cw + cγ + 2) := by ring
  have p3 : 30 * (spE + 1) * (g + 1) ≤ 30 * (Cγ + 1) * B ^ (cw + cγ + 2) := by
    have hc : 1 ≤ B ^ cγ := Nat.one_le_pow _ _ hBpos
    have h1 : g + 1 ≤ (Cγ + 1) * B ^ cγ := by
      calc g + 1 ≤ Cγ * B ^ cγ + B ^ cγ := by omega
        _ = (Cγ + 1) * B ^ cγ := by ring
    calc 30 * (spE + 1) * (g + 1) ≤ 30 * B * ((Cγ + 1) * B ^ cγ) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 30 (by omega)) h1
      _ = 30 * (Cγ + 1) * B ^ (cγ + 1) := by ring
      _ ≤ 30 * (Cγ + 1) * B ^ (cw + cγ + 2) := Nat.mul_le_mul_left _ (hpw (by omega))
  have p4 : 10 + 13 * spE + spV + (3 * spV + dynGraphSize spV spE + spE + 10) ≤
      25 * B ^ (cw + cγ + 2) := by
    unfold dynGraphSize; omega
  have e : (125 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 2) =
      100 * B ^ (cw + cγ + 2) + 2 * 72 ^ cw * B ^ (cw + cγ + 2) +
        30 * (Cγ + 1) * B ^ (cw + cγ + 2) + 25 * B ^ (cw + cγ + 2) := by ring
  omega

private lemma asmFirstPhase2_arith {B cT rQ cw Cγ cγ newLen loopS sumB depth spV spE g : ℕ}
    (hB : 2 ≤ B) (hnewLen : newLen ≤ B) (hloop : loopS ≤ newLen * ((rQ + 6 * cT + 57) * B ^ 2))
    (hsumB : sumB ≤ 2 * B ^ 2) (hsp : spV + spE + 2 ≤ B) (hdepth : depth + 1 ≤ B)
    (hg : g ≤ Cγ * B ^ cγ) :
    2 * newLen + loopS +
      sumB * (10 + 13 * spE + spV +
        (100 * ((depth + 1) * (spV + spE + 1)) +
          (2 * (36 * (spV + 2 * spE + 1)) ^ cw + 30 * (spE + 1) * (g + 1) + 3 * spV +
            dynGraphSize spV spE + spE + 10))) + 200 ≤
      (202 + (rQ + 6 * cT + 57) + 2 * (125 + 2 * 72 ^ cw + 30 * (Cγ + 1))) *
        B ^ (cw + cγ + 4) := by
  have hBpos : 0 < B := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → B ^ a ≤ B ^ b := fun h => Nat.pow_le_pow_right hBpos h
  have hB_D : B ≤ B ^ (cw + cγ + 4) := by simpa using hpw (a := 1) (b := cw + cγ + 4) (by omega)
  have h1_D : 1 ≤ B ^ (cw + cγ + 4) := Nat.one_le_pow _ _ hBpos
  have hB3_D : B ^ 3 ≤ B ^ (cw + cγ + 4) := hpw (by omega)
  have hT1 : 2 * newLen + 200 ≤ 202 * B ^ (cw + cγ + 4) := by omega
  have hT2 : loopS ≤ (rQ + 6 * cT + 57) * B ^ (cw + cγ + 4) := by
    calc loopS ≤ newLen * ((rQ + 6 * cT + 57) * B ^ 2) := hloop
      _ ≤ B * ((rQ + 6 * cT + 57) * B ^ 2) := Nat.mul_le_mul_right _ hnewLen
      _ = (rQ + 6 * cT + 57) * B ^ 3 := by ring
      _ ≤ (rQ + 6 * cT + 57) * B ^ (cw + cγ + 4) := Nat.mul_le_mul_left _ hB3_D
  have hT3 : sumB * (10 + 13 * spE + spV +
        (100 * ((depth + 1) * (spV + spE + 1)) +
          (2 * (36 * (spV + 2 * spE + 1)) ^ cw + 30 * (spE + 1) * (g + 1) + 3 * spV +
            dynGraphSize spV spE + spE + 10))) ≤
      2 * (125 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 4) := by
    calc sumB * _ ≤ (2 * B ^ 2) * ((125 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 2)) :=
          Nat.mul_le_mul hsumB (asmFiSpanCapSpace_le hB hsp hdepth hg)
      _ = 2 * (125 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 4) := by ring
  have he : (202 + (rQ + 6 * cT + 57) + 2 * (125 + 2 * 72 ^ cw + 30 * (Cγ + 1))) *
        B ^ (cw + cγ + 4) =
      202 * B ^ (cw + cγ + 4) + (rQ + 6 * cT + 57) * B ^ (cw + cγ + 4) +
        2 * (125 + 2 * 72 ^ cw + 30 * (Cγ + 1)) * B ^ (cw + cγ + 4) := by ring
  omega

private lemma newActOneSpace_le_B2 {B cT rQ eCap len m_C r : ℕ} {TS : BundleTourSpec}
    (hB : 2 ≤ B) (hTS : ∀ n, TS.listSpace n ≤ cT * (n + 1))
    (heCap : eCap ≤ B) (hlen : len ≤ 2 * eCap) (hmC : m_C ≤ eCap) (hr : r ≤ 2 * B ^ 2) :
    newActOneSpace TS rQ len m_C r ≤ (rQ + 6 * cT + 57) * B ^ 2 := by
  have hBpos : 0 < B := by omega
  have hB_B2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
  have h1_B2 : 1 ≤ B ^ 2 := Nat.one_le_pow _ _ hBpos
  have hts : TS.listSpace len ≤ cT * (3 * B) :=
    (hTS len).trans (Nat.mul_le_mul_left cT (by omega))
  have hts2 : 2 * TS.listSpace len ≤ 6 * cT * B ^ 2 := by
    calc 2 * TS.listSpace len ≤ 2 * (cT * (3 * B)) := Nat.mul_le_mul_left 2 hts
      _ = 6 * cT * B := by ring
      _ ≤ 6 * cT * B ^ 2 := Nat.mul_le_mul_left _ hB_B2
  have hrQ : rQ ≤ rQ * B ^ 2 := Nat.le_mul_of_pos_right rQ h1_B2
  unfold newActOneSpace
  have he : (rQ + 6 * cT + 57) * B ^ 2 = rQ * B ^ 2 + 6 * cT * B ^ 2 + 57 * B ^ 2 := by ring
  omega

/-! ## Main bounds for Phases 1, 2, and 3 -/

public section

/-- **Phase 1 space bound.** `6 + asmFirstScanBatchSpace vCap eCap words` is at most
`asmFirstPhase1SpacePoly.eval (M + N + k + vCap + eCap + L + depth + words + editWords)`. -/
theorem asmFirstPhase1Space_le_poly (M N k vCap eCap L depth words editWords : ℕ) :
    6 + asmFirstScanBatchSpace vCap eCap words ≤
      asmFirstPhase1SpacePoly.eval (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  unfold asmFirstScanBatchSpace asmFirstPhase1SpacePoly PolyBound.eval
  simp only [pow_one]
  omega

/-- **Phase 2 space bound.** Under `asmBrFullRep`, `newComps.length ≤ words`,
`newCompsBucketSum ≤ y.slotCap`, `∀ e ∈ tr.cs.G.E, e < eCap`, `TS.listSpace len ≤ cT * (len + 1)`,
and `⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ`, `newActTotalSpace` is at most
`(asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).eval X`. -/
theorem asmFirstPhase2Space_le_poly {depth w P L capExp limbMul : ℕ}
    {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {Cγ cγ : ℕ} (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ)
    {Ψ : BundleTreeState depth → ℕ}
    {TS : BundleTourSpec} {cT rQ : ℕ} (hTS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    {b k M N vCap eCap words editWords : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
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
    newActTotalSpace TS rQ impl w x.xRest tr ord newComps ≤
      (asmFirstPhase2SpacePoly cT rQ impl.cw Cγ cγ capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set y := x.xRest
  set X := M + N + k + vCap + eCap + L + depth + words + editWords
  set Z := X + 2
  set B := Z ^ (capExp + 7)
  obtain ⟨hrepA, -, -, hvc, hec, -, hsc, -, -⟩ := hrep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXr, -, -, -, -⟩ := hrepA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmod⟩ := hXr
  obtain ⟨-, -, -, -, -, -, ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, -, -, -, hCapS, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hmMax, -, -⟩ := hmod
  have hZ2 : 2 ≤ Z := by omega
  have hZ_B : Z ≤ B := Nat.le_self_pow (by omega) Z
  have hB2 : 2 ≤ B := hZ2.trans hZ_B
  have hsp : y.spV + y.spE + 2 ≤ B := by
    have h1 : y.spV + y.spE + 2 ≤ (M + N + 2) ^ (capExp + 7) := by
      have := hCapS.1; rw [hM, hN] at this; exact this
    exact h1.trans (Nat.pow_le_pow_left (by omega) _)
  have hslotCap : y.slotCap ≤ 2 * B ^ 2 := by
    dsimp only at hvc hec
    have h1 : x.vCap + x.eCap + 2 ≤ B := by rw [hvc, hec]; omega
    exact hsc.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h1 2))
  have hdepth : depth + 1 ≤ B := by omega
  have hg : ⌈impl.γ_ℓ y.mMax⌉₊ ≤ Cγ * B ^ cγ := by
    rw [hmMax, hM]
    exact (hγ M).trans (Nat.mul_le_mul_left Cγ (Nat.pow_le_pow_left (by omega) cγ))
  have hNC_B : newComps.length ≤ B := hNC_len.trans (le_trans (by omega) hZ_B)
  have hLoop : newActLoopSpace TS rQ tr ord y.comps newComps ≤
      newComps.length * ((rQ + 6 * cT + 57) * B ^ 2) := by
    unfold newActLoopSpace
    exact list_sum_map_le_mul_p13 newComps _ _ fun p hp =>
      newActOneSpace_le_B2 hB2 hTS (by omega)
        (outCoreOrder_length_le_two_eCap hI ρ hρ hGE _)
        (compCoreEdges_card_le_eCap hGE _)
        ((list_mem_le_sum_map newComps (fun q => (tr.activeBuckets (y.comps.getD q.1 ∅)).card) hp).trans
          (hSum.trans hslotCap))
  unfold newActTotalSpace asmFiSpanCapSpace asmBrSP asmFirstPhase2SpacePoly PolyBound.eval
  dsimp only
  rw [pow_mul]
  exact asmFirstPhase2_arith hB2 hNC_B hLoop (hSum.trans hslotCap) hsp hdepth hg

/-- **Phase 3 space bound.** Under `slotCap ≤ 2 * (vCap + eCap + 2) ^ 2` and `nDel ≤ words`,
`asmFirstPhase3Space slotCap vCap eCap words editWords nDel` is at most
`asmFirstPhase3SpacePoly.eval (M + N + k + vCap + eCap + L + depth + words + editWords)`. -/
theorem asmFirstPhase3Space_le_poly {slotCap M N k vCap eCap L depth words editWords nDel : ℕ}
    (hslotCap : slotCap ≤ 2 * (vCap + eCap + 2) ^ 2) (hnDel : nDel ≤ words) :
    asmFirstPhase3Space slotCap vCap eCap words editWords nDel ≤
      asmFirstPhase3SpacePoly.eval (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set Z := M + N + k + vCap + eCap + L + depth + words + editWords + 2
  have hZ2 : 2 ≤ Z := by omega
  have hZ_Z2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by decide) Z
  have hZ2_Z3 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hZ_Z3 : Z ≤ Z ^ 3 := hZ_Z2.trans hZ2_Z3
  have h1_Z3 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hsc : slotCap ≤ 2 * Z ^ 2 :=
    hslotCap.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2))
  have hve : vCap * eCap ≤ Z ^ 2 := by
    calc vCap * eCap ≤ Z * Z := Nat.mul_le_mul (by omega) (by omega)
      _ = Z ^ 2 := (sq Z).symm
  have hsce : slotCap * eCap ≤ 2 * Z ^ 3 := by
    calc slotCap * eCap ≤ (2 * Z ^ 2) * Z := Nat.mul_le_mul hsc (by omega)
      _ = 2 * Z ^ 3 := by ring
  unfold asmFirstPhase3Space buildDelTriplesSpace buildGroupsSpace tourBlockStepSpace
    tourSplitStepSpace outSmallSideSpace phase3BunStepSpaceBound tourBundleSpec tourOutSpec
    asmFirstPhase3SpacePoly PolyBound.eval
  dsimp only
  change 2 + (3 * nDel + 2 * nDel * 1) + (2 + vCap + 10 * vCap) +
      (64 + 160 * (words + editWords) +
        vCap * (2 + ((2 * (2 * eCap) + 2) * 3 + (1 + 2 * eCap) + 2 * eCap + 6))) +
      (1 + 3 * slotCap) +
      22 * (2 * vCap + 12 * vCap * eCap + slotCap * eCap + slotCap + 1) ≤
    826 * Z ^ 3
  have hv_tour : vCap * (2 + ((2 * (2 * eCap) + 2) * 3 + (1 + 2 * eCap) + 2 * eCap + 6)) ≤
      31 * Z ^ 2 := by
    have h1 : 2 + ((2 * (2 * eCap) + 2) * 3 + (1 + 2 * eCap) + 2 * eCap + 6) = 15 + 16 * eCap := by
      ring
    rw [h1]
    calc vCap * (15 + 16 * eCap) = 15 * vCap + 16 * (vCap * eCap) := by ring
      _ ≤ 15 * Z ^ 2 + 16 * Z ^ 2 := by omega
      _ = 31 * Z ^ 2 := by ring
  have h12ve : 12 * vCap * eCap = 12 * (vCap * eCap) := by ring
  omega

end

end MinCostFlow.SparseCore.Program
