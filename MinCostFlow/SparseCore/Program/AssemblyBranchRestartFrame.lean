module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartRun
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartBank

/-!
# Frame facts for the restart of a branch (`AssemblyBranchRestartFrame`)

A restart of a branch changes several parts of the branch at once: the restart of P8 changes the
readout data, the tour and the bundle side, and the reset and the refresh change the tour, the
output graph and the embedding table. This file gives the facts that put the parts back together.

* `asmBr_disjoint_of_fresh`: the new parts are disjoint when each new part has only old cells of
  the same part or cells above the heap pointer `h`, and no two new parts share a cell above `h`.
* `asmSd_disjoint_of_fresh`: the same for the four parts of the bundle side, and
  `asmSd_disjoint_of_new12` when only the bundle table and the spanners change.
* `asmBr_apart_of_fresh`: the new cells of a branch stay apart from a footprint that grows only
  into new cells, such as the cells of P4.
* `readViewInv_withS`: the invariant `ReadView.Inv` of the readout data holds again when the graph
  `S` is replaced by a graph stored with the same caps (`DynGraphAt`).

It also defines the cost factor of the restart and the heap space of its first call
(`asmBrRestartConst`, `asmBrP8Space`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The new parts of a branch are disjoint** when every cell of a new part is a cell of the
same old part or lies at `h` or above, all old cells lie below `h`, and no two new parts share a
cell at `h` or above. -/
theorem asmBr_disjoint_of_fresh {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b h : ℕ} {x x' : AsmBrConc TR X.τ} (hdisj : AsmBrDisjoint X b x)
    (hfoot : ∀ c, asmBrFoot X b x c → c < h)
    (hP : ∀ i < 6, ∀ c, asmBrPart X b x' i c → asmBrPart X b x i c ∨ h ≤ c)
    (hfresh : ∀ i < 6, ∀ j < 6, i < j → ∀ c, h ≤ c → asmBrPart X b x' i c →
      ¬ asmBrPart X b x' j c) :
    AsmBrDisjoint X b x' := by
  intro i hi j hj hij c hci hcj
  rcases hP i hi c hci with hci' | hci' <;> rcases hP j hj c hcj with hcj' | hcj'
  · exact hdisj i hi j hj hij c hci' hcj'
  · exact absurd (hfoot c ⟨i, hi, hci'⟩) (by omega)
  · exact absurd (hfoot c ⟨j, hj, hcj'⟩) (by omega)
  · rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact hfresh i hi j hj hlt c hci' hci hcj
    · exact hfresh j hj i hi hlt c hcj' hcj hci

/-- **The new parts of the bundle side are disjoint**, under the same conditions as
`asmBr_disjoint_of_fresh`. -/
theorem asmSd_disjoint_of_fresh
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {s h : ℕ} {y y' : AsmBrSide B5 depth}
    (hdisj : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ c, asmSdPart s y i c → ¬ asmSdPart s y j c)
    (hfoot : ∀ c, asmSdFoot s y c → c < h)
    (hP : ∀ i < 4, ∀ c, asmSdPart s y' i c → asmSdPart s y i c ∨ h ≤ c)
    (hfresh : ∀ i < 4, ∀ j < 4, i < j → ∀ c, h ≤ c → asmSdPart s y' i c →
      ¬ asmSdPart s y' j c) :
    ∀ i < 4, ∀ j < 4, i ≠ j → ∀ c, asmSdPart s y' i c → ¬ asmSdPart s y' j c := by
  intro i hi j hj hij c hci hcj
  rcases hP i hi c hci with hci' | hci' <;> rcases hP j hj c hcj with hcj' | hcj'
  · exact hdisj i hi j hj hij c hci' hcj'
  · exact absurd (hfoot c ⟨i, hi, hci'⟩) (by omega)
  · exact absurd (hfoot c ⟨j, hj, hcj'⟩) (by omega)
  · rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact hfresh i hi j hj hlt c hci' hci hcj
    · exact hfresh j hj i hi hlt c hcj' hcj hci

/-- **The bundle side with a new bundle table and new spanners is disjoint** when the two new
parts have only old cells of the same part or cells at `h` or above, and share no cell. -/
theorem asmSd_disjoint_of_new12
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {s h : ℕ} {y : AsmBrSide B5 depth} {bS : Fin y.slotCap → Option BundleState}
    {xb : (B5 y.kB y.slotCap y.vCap5 y.eCap5).τ} {S6 : BucketSpannerState y.cap}
    {x6 : BucketSpannerMeta depth y.cap} {wp : ℕ}
    (hdisj : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ c, asmSdPart s y i c → ¬ asmSdPart s y j c)
    (hfoot : ∀ c, asmSdFoot s y c → c < h)
    (h1 : ∀ c, (B5 y.kB y.slotCap y.vCap5 y.eCap5).foot y.bunH xb c →
      (B5 y.kB y.slotCap y.vCap5 y.eCap5).foot y.bunH y.xBun c ∨ h ≤ c)
    (h2 : ∀ c, bucketFoot y.spanH x6 c → bucketFoot y.spanH y.xSpan c ∨ h ≤ c)
    (h12 : ∀ c, (B5 y.kB y.slotCap y.vCap5 y.eCap5).foot y.bunH xb c → ¬ bucketFoot y.spanH x6 c) :
    let y' : AsmBrSide B5 depth :=
      { y with bunS := bS, xBun := xb, spanS := S6, xSpan := x6, walkPot := wp }
    ∀ i < 4, ∀ j < 4, i ≠ j → ∀ c, asmSdPart s y' i c → ¬ asmSdPart s y' j c := by
  intro y'
  have h0 : ∀ c, asmSdPart s y 0 c → c < h := fun c hc => hfoot c ⟨0, by decide, hc⟩
  have h3 : ∀ c, asmSdPart s y 3 c → c < h := fun c hc => hfoot c ⟨3, by decide, hc⟩
  apply asmSd_disjoint_of_fresh hdisj hfoot
  · intro i hi c hc
    interval_cases i
    · exact Or.inl hc
    · exact h1 c hc
    · exact h2 c hc
    · exact Or.inl hc
  · intro i hi j hj hij c hc hci hcj
    interval_cases i <;> interval_cases j
    · exact absurd (h0 c hci) (by omega)
    · exact absurd (h0 c hci) (by omega)
    · exact absurd (h0 c hci) (by omega)
    · exact h12 c hci hcj
    · exact absurd (h3 c hcj) (by omega)
    · exact absurd (h3 c hcj) (by omega)

/-- **The new cells of a branch are apart from a footprint `F'`** that grows from a footprint `F`
below `h` into `[h, o)`, when the old cells were apart from `F`, every new cell of a part is an
old cell of the same part or lies at `h` or above, and the new cells in `[h, o)` are apart from
`F'`. -/
theorem asmBr_apart_of_fresh {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b h o : ℕ} {x x' : AsmBrConc TR X.τ} {F F' : ℕ → Prop}
    (hold : ∀ c, asmBrFoot X b x c → ¬ F c)
    (hF : ∀ c, F c → c < h) (hF' : ∀ c, F' c → F c ∨ (h ≤ c ∧ c < o))
    (hP : ∀ i < 6, ∀ c, asmBrPart X b x' i c → asmBrPart X b x i c ∨ h ≤ c)
    (hnew : ∀ i < 6, ∀ c, h ≤ c → c < o → asmBrPart X b x' i c → ¬ F' c) :
    ∀ c, asmBrFoot X b x' c → ¬ F' c := by
  rintro c ⟨i, hi, hc⟩ hc'
  rcases hF' c hc' with hFc | ⟨hl, hu⟩
  · rcases hP i hi c hc with h1 | h1
    · exact hold c ⟨i, hi, h1⟩ hFc
    · have := hF c hFc; omega
  · exact hnew i hi c hl hu hc hc'

/-- **The invariant of the readout data with a new graph `S`.** The parts of `ReadView.Inv` on
`S` say that `S` is valid with names below the caps, which a stored copy of `S` with the same caps
gives (`DynGraphAt`). The other parts do not mention `S`. -/
theorem readViewInv_withS {vCap eCap tCap : ℕ} {v : ReadView} (hv : v.Inv vCap eCap tCap)
    {mem : ℕ → ℕ} {a : ℕ} {S : MGraph} (hS : DynGraphAt mem a vCap eCap S) :
    ReadView.Inv vCap eCap tCap { v with S := S } := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, -, -, -, i16⟩ := hv
  exact ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, hS.1, hS.2.1, hS.2.2.1, i16⟩

/-! ## The cost and the space of the restart -/

/-- The heap space of the restart of P8 in a branch (`restartBranch_model_runs`): the space of
the bundle piece, of the spanner initializations and of the rebuild of the readout data. -/
noncomputable def asmBrP8Space (bunSpace : ℕ → ℕ) (readMul : ℕ) (SP : DSParams)
    {slotCap cap : ℕ} (S : Fin slotCap → Option BundleState) (S6 : BucketSpannerState cap)
    (cs : CompLSFState) (ord : ℕ → List End) (k : ℕ) (slots : List ℕ) (vCap tCap L_w : ℕ) : ℕ :=
  bunSpace (cs.G.m + slots.length) +
    (slots.map fun s => spanActivateSpace SP (restartSlotGraph S cs ord k s)).sum +
    readSpace readMul vCap tCap L_w
      (rebuildSize SP (restartSpanState S6 S cs ord k slots) slots + slots.length)

/-- When `(vCap + eCap + 2) ^ 2` is below `2 ^ w`, so are `2 · eCap` and `vCap`. -/
theorem caps_lt_word {vCap eCap w : ℕ} (h : (vCap + eCap + 2) ^ 2 < 2 ^ w) :
    2 * eCap < 2 ^ w ∧ vCap ≤ 2 ^ w := by
  have h2 : 2 * (vCap + eCap + 2) ≤ (vCap + eCap + 2) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- The cost factor of the restart of a branch: the factor of the restart of P8
(`restartModelConst`), the factor of the reset of P7 (`outResetCost_le_restartMachCost`),
`320 * (capExp + 1)` for the log-weighted banks of the bucket spanners (`bucketPhi_restart_mul_lg_le`),
and `300` for the walk potential after the restart. -/
def asmBrRestartConst (bunMul readMul rootCost tourMul capExp : ℕ) : ℕ :=
  restartModelConst bunMul readMul rootCost (capExp + 7) + 2000 * (tourMul + 1) * (capExp + 1) +
    320 * (capExp + 1) + 300

end MinCostFlow.SparseCore.Program
