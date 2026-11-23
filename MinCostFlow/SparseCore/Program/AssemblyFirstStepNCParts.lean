module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPostTour

import Mathlib.Tactic

/-!
# The parts of the branch at the end of the first step (`AssemblyFirstStepNCParts`)

At the end of the first step only three parts of the branch change: the embedding table, the
tour and the bundle side (`AsmBrConc.afterCore`). The post of the step asks that the six parts
of the new branch are still pairwise apart, and that each new cell is an old cell of the branch or
a cell above the record of the step. This file proves both from facts on the three parts that
change, and two counting facts for the bound on the split lists and on `T₀`.

* `asmBrDisjoint_afterCore`: the parts of the new branch are pairwise apart, if each changed part
  lies in the same old part or at `h` or above, and the three changed parts are pairwise apart.
  The other parts are old, so they lie below `h`.
* `asmBrFoot_afterCore`: each cell of the new branch is a cell of the old one or lies in a given
  range, if this holds for each changed part.
* `asmSdPart_sideAfter`: the bundle side after the step (`asmFsSideAfter`) has the parts `0`,
  `1`, `3` of the side `y'` after Phase 2; its part `2` is the foot of the new spanners.
* `ordEditsAt_two_len`: an edit record takes two words or more, so `2 |ed| + 1 ≤ editWords`.
* `asmFsNC_ys_rot_le`: the bound on `Σ |Y| + |T₀|` of the post, for a multiplier of at least
  `4 capExp + 5`. The split lists are bounded by `asmFirstTourBlockStep_Ys_sum_le`, and `T₀` by
  its raw list: two vertices per split, per entering edge, per update and per edit.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- The parts `0`, `1` and `3` of a branch do not change in `afterCore`. -/
theorem asmBrPart_afterCore {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b : ℕ} {x : AsmBrConc TR X.τ} {yEmb : EmbConc} {sTour : OutTourAbs}
    {xTour : (TR x.vCap x.eCap).τ} {xRest : X.τ} {i a : ℕ} (hi : i = 0 ∨ i = 1 ∨ i = 3) :
    asmBrPart X b (x.afterCore yEmb sTour xTour xRest) i a ↔ asmBrPart X b x i a := by
  rcases hi with rfl | rfl | rfl <;> exact Iff.rfl

/-- **The parts of the new branch are apart.** The old parts lie below `h` and are pairwise apart
(`hOld`, `hlt`). Each changed part lies in the same old part or at `h` or above (`h2`, `h4`,
`h5`), and the three changed parts are pairwise apart (`d24`, `d25`, `d45`). A pair with an
unchanged part has an old cell below `h`, so the other cell is old too, and the old parts are
apart. -/
theorem asmBrDisjoint_afterCore {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b h : ℕ} {x : AsmBrConc TR X.τ} {yEmb : EmbConc} {sTour : OutTourAbs}
    {xTour : (TR x.vCap x.eCap).τ} {xRest : X.τ}
    (hOld : AsmBrDisjoint X b x) (hlt : ∀ i < 6, ∀ a, asmBrPart X b x i a → a < h)
    (h2 : ∀ a, embFoot x.eCap x.embH yEmb a → embFoot x.eCap x.embH x.yEmb a ∨ h ≤ a)
    (h4 : ∀ a, (TR x.vCap x.eCap).foot x.tourH xTour a →
      (TR x.vCap x.eCap).foot x.tourH x.xTour a ∨ h ≤ a)
    (h5 : ∀ a, X.foot x.restH xRest a → X.foot x.restH x.xRest a ∨ h ≤ a)
    (d24 : ∀ a, embFoot x.eCap x.embH yEmb a → ¬ (TR x.vCap x.eCap).foot x.tourH xTour a)
    (d25 : ∀ a, embFoot x.eCap x.embH yEmb a → ¬ X.foot x.restH xRest a)
    (d45 : ∀ a, (TR x.vCap x.eCap).foot x.tourH xTour a → ¬ X.foot x.restH xRest a) :
    AsmBrDisjoint X b (x.afterCore yEmb sTour xTour xRest) := by
  have hloc : ∀ i < 6, ∀ a, asmBrPart X b (x.afterCore yEmb sTour xTour xRest) i a →
      asmBrPart X b x i a ∨ h ≤ a := by
    intro i hi a ha
    interval_cases i
    · exact Or.inl ha
    · exact Or.inl ha
    · exact h2 a ha
    · exact Or.inl ha
    · exact h4 a ha
    · exact h5 a ha
  have key : ∀ i < 6, ∀ j < 6, i ≠ j → (i = 0 ∨ i = 1 ∨ i = 3) → ∀ a,
      asmBrPart X b (x.afterCore yEmb sTour xTour xRest) i a →
      ¬ asmBrPart X b (x.afterCore yEmb sTour xTour xRest) j a := by
    intro i hi j hj hij hi' a hai haj
    have hai' : asmBrPart X b x i a := (asmBrPart_afterCore hi').1 hai
    rcases hloc j hj a haj with hoj | hbj
    · exact hOld i hi j hj hij a hai' hoj
    · have := hlt i hi a hai'
      omega
  intro i hi j hj hij a hai haj
  by_cases hi' : i = 0 ∨ i = 1 ∨ i = 3
  · exact key i hi j hj hij hi' a hai haj
  by_cases hj' : j = 0 ∨ j = 1 ∨ j = 3
  · exact key j hj i hi (Ne.symm hij) hj' a haj hai
  have hi2 : i = 2 ∨ i = 4 ∨ i = 5 := by omega
  have hj2 : j = 2 ∨ j = 4 ∨ j = 5 := by omega
  rcases hi2 with rfl | rfl | rfl <;> rcases hj2 with rfl | rfl | rfl
  · exact hij rfl
  · exact d24 a hai haj
  · exact d25 a hai haj
  · exact d24 a haj hai
  · exact hij rfl
  · exact d45 a hai haj
  · exact d25 a haj hai
  · exact d45 a haj hai
  · exact hij rfl

/-- **The cells of the new branch.** If each changed part lies in the same old part or in the
range `[lo, hi)`, then so does each cell of the new branch. -/
theorem asmBrFoot_afterCore {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b lo hi : ℕ} {x : AsmBrConc TR X.τ} {yEmb : EmbConc} {sTour : OutTourAbs}
    {xTour : (TR x.vCap x.eCap).τ} {xRest : X.τ}
    (h2 : ∀ a, embFoot x.eCap x.embH yEmb a → embFoot x.eCap x.embH x.yEmb a ∨ (lo ≤ a ∧ a < hi))
    (h4 : ∀ a, (TR x.vCap x.eCap).foot x.tourH xTour a →
      (TR x.vCap x.eCap).foot x.tourH x.xTour a ∨ (lo ≤ a ∧ a < hi))
    (h5 : ∀ a, X.foot x.restH xRest a → X.foot x.restH x.xRest a ∨ (lo ≤ a ∧ a < hi)) :
    ∀ a, asmBrFoot X b (x.afterCore yEmb sTour xTour xRest) a →
      asmBrFoot X b x a ∨ (lo ≤ a ∧ a < hi) := by
  rintro a ⟨i, hi6, ha⟩
  interval_cases i
  · exact Or.inl ⟨0, by decide, ha⟩
  · exact Or.inl ⟨1, by decide, ha⟩
  · rcases h2 a ha with h | h
    · exact Or.inl ⟨2, by decide, h⟩
    · exact Or.inr h
  · exact Or.inl ⟨3, by decide, ha⟩
  · rcases h4 a ha with h | h
    · exact Or.inl ⟨4, by decide, h⟩
    · exact Or.inr h
  · rcases h5 a ha with h | h
    · exact Or.inl ⟨5, by decide, h⟩
    · exact Or.inr h

/-- **The parts of the bundle side after the step.** Its parts other than `2` are those of the
side `y'` after Phase 2 (they read only fields that `asmFsSideAfter` keeps), and its part `2` is
the foot of the spanners `x'`. -/
theorem asmSdPart_sideAfter
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {impl : SparsifyImpl} {w : ℕ} {Ψ : BundleTreeState depth → ℕ} {tr : BundleTreeState depth}
    {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit} {y' : AsmBrSide B5 depth}
    {mem₃ : ℕ → ℕ} {outDescPtr nTouched : ℕ} {x' : BucketSpannerMeta depth y'.cap}
    {restH a : ℕ} :
    (∀ i, i ≠ 2 → (asmSdPart restH
      (asmFsSideAfter impl w Ψ tr U ord ed y' mem₃ outDescPtr nTouched x') i a ↔
        asmSdPart restH y' i a)) ∧
    (asmSdPart restH (asmFsSideAfter impl w Ψ tr U ord ed y' mem₃ outDescPtr nTouched x') 2 a ↔
      bucketFoot y'.spanH x' a) := by
  refine ⟨fun i hi => ?_, Iff.rfl⟩
  match i, hi with
  | 0, _ => exact Iff.rfl
  | 1, _ => exact Iff.rfl
  | 3, _ => exact Iff.rfl
  | _ + 4, _ => exact Iff.rfl

/-- A cell of the bundle side after the step lies in a part other than `2` of the side `y'` after
Phase 2, or in the new spanners `x'`. -/
theorem asmSdFoot_sideAfter
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {impl : SparsifyImpl} {w : ℕ} {Ψ : BundleTreeState depth → ℕ} {tr : BundleTreeState depth}
    {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit} {y' : AsmBrSide B5 depth}
    {mem₃ : ℕ → ℕ} {outDescPtr nTouched : ℕ} {x' : BucketSpannerMeta depth y'.cap}
    {restH a : ℕ}
    (ha : asmSdFoot restH (asmFsSideAfter impl w Ψ tr U ord ed y' mem₃ outDescPtr nTouched x') a) :
    (∃ i < 4, i ≠ 2 ∧ asmSdPart restH y' i a) ∨ bucketFoot y'.spanH x' a := by
  obtain ⟨i, hi, hia⟩ := ha
  by_cases h2 : i = 2
  · subst h2
    exact Or.inr ((asmSdPart_sideAfter (x' := x')).2.1 hia)
  · exact Or.inl ⟨i, hi, h2, ((asmSdPart_sideAfter (x' := x')).1 i h2).1 hia⟩

/-- An edit takes two words or more in its record, and the record has one more word for the
count: `2 |ed| + 1 ≤ editWords` (`decodeOrdEdits_sum_ge`). -/
theorem ordEditsAt_two_len {mem : ℕ → ℕ} {a : ℕ} {ed : List OrdEdit} {words : ℕ}
    (h : OrdEditsAt mem a ed words) : 2 * ed.length + 1 ≤ words := by
  obtain ⟨hr, hw, -⟩ := h
  have hl := (decodeOrdEdits_length mem (mem a) (a + 1)).1
  have hs := decodeOrdEdits_sum_ge mem (mem a) (a + 1)
  have hed : ed.length = mem a := by
    rw [← hr]
    exact hl
  omega

/-- The entering output edges of a step are at most the encoding of the output batch, which
ends with one insertion per entering edge (`outStep_batch_eq`). -/
theorem outInsSet_card_le_batchEnc {depth : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End) :
    (outInsSet sp tr U ord ord').card ≤
      tr.S_cur.batchEnc (stepBundleTree sp tr U ord ord').U_S := by
  rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append]
  have hI : ∀ G : MGraph, G.batchEnc (outInsBatch sp tr U ord ord') =
      (outInsList sp tr U ord ord').length := fun G => batchEnc_inserts _ _ _ G
  have hL : (outInsList sp tr U ord ord').length = (outInsSet sp tr U ord ord').card := by
    simp [outInsList, outInsSet]
  rw [hI]
  omega

/-- The raw list of the rotation has two vertices or fewer per split, per entering edge, per
update and per edit. -/
theorem p4RotRaw_length_le (splits : List CompSplitEntry) (insL : List ℕ) (tl hd rt : ℕ → ℕ)
    (U : List Update) (ed : List OrdEdit) :
    (p4RotRaw splits insL tl hd rt U ed).length ≤
      2 * splits.length + 2 * insL.length + 2 * U.length + 2 * ed.length := by
  unfold p4RotRaw
  rw [List.length_append, List.length_append, rotDirectList_length]
  have h1 := rotBatchVertList_length_le rt U
  have h2 := rotEditVertList_length_le rt ed
  omega

/-- An arithmetic step of the bound: `a X Lg + 4 X ≤ (a + 4) X Lg` for `1 ≤ Lg`. -/
private theorem ys_rot_arith {a B X Lg Y T ysMul : ℕ} (hLg : 1 ≤ Lg) (hBX : B ≤ X)
    (hY : Y ≤ a * B * Lg) (hT : T ≤ 4 * X) (hys : a + 4 ≤ ysMul) :
    Y + T ≤ ysMul * X * Lg := by
  have h1 : a * B * Lg ≤ a * X * Lg := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hBX)
  have h2 : 4 * X ≤ 4 * X * Lg := Nat.le_mul_of_pos_right _ hLg
  have h3 : (a + 4) * X * Lg ≤ ysMul * X * Lg :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hys)
  have h4 : (a + 4) * X * Lg = a * X * Lg + 4 * X * Lg := by ring
  omega

/-- **The bound on the split lists and `T₀`** (conjunct of the post of the step): for a
multiplier `ysMul ≥ 4 capExp + 5`. The split lists are bounded by
`asmFirstTourBlockStep_Ys_sum_le`. `T₀` is at most its raw list, which has two vertices or fewer
per split, per entering edge, per update and per edit; the splits and the entering edges are at
most the encoding of the output batch, and the updates and the edits at most half their words. -/
theorem asmFsNC_ys_rot_le {depth capExp vCap eCap M₀ N₀ words editWords ysMul : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    (tl hd rt : ℕ → ℕ)
    (hEcard : tr.S_cur.E.card ≤ eCap) (hcap : vCap + eCap + 2 ≤ (M₀ + N₀ + 2) ^ capExp)
    {Ys : List (List End)} {T₀ : List ℕ}
    (hPot : (Ys.map List.length).sum ≤
      (tr.S_cur.applyBatch ((outDelList sp tr U ord (applyOrdEdits ord ed)).map
        Update.delete)).batchEnc
        (restrictSplits (outKeep sp tr U ord (applyOrdEdits ord ed))
          (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).U_core) +
      markPot (outKeep sp tr U ord (applyOrdEdits ord ed)) tr.S_cur.E
        (coreGraph tr.cs.G tr.cs.lsf))
    (hT : T₀.length ≤ (p4RotRaw (canonSplitList tr.cs U)
      ((outInsSet sp tr U ord (applyOrdEdits ord ed)).sort (· ≤ ·)) tl hd rt U ed).length)
    (hU : 2 * U.length ≤ words) (hed : 2 * ed.length ≤ editWords)
    (hys : 4 * capExp + 5 ≤ ysMul) :
    (Ys.map List.length).sum + T₀.length ≤
      ysMul * (tr.S_cur.batchEnc (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).U_S +
        words + editWords + 1) * (Nat.log 2 (M₀ + N₀ + 2) + 1) := by
  have hY := asmFirstTourBlockStep_Ys_sum_le sp tr U ord (applyOrdEdits ord ed) hEcard hcap hPot
  have hR := p4RotRaw_length_le (canonSplitList tr.cs U)
    ((outInsSet sp tr U ord (applyOrdEdits ord ed)).sort (· ≤ ·)) tl hd rt U ed
  have hS := asmFirstCanonSplitList_length_le_batchEnc sp tr U ord (applyOrdEdits ord ed)
  have hI := outInsSet_card_le_batchEnc sp tr U ord (applyOrdEdits ord ed)
  rw [Finset.length_sort] at hR
  refine ys_rot_arith (a := 1 + 4 * capExp) (Nat.le_add_left _ _) (Nat.le_add_right_of_le
    (Nat.le_add_right_of_le (Nat.le_add_right _ _))) hY (by omega) (by omega)

end

end MinCostFlow.SparseCore.Program
