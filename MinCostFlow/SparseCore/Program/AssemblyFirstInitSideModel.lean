module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMidFacts
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSideInv
public import MinCostFlow.SparseCore.Program.AssemblyCodeCarry
import MinCostFlow.SparseCore.Program.AssemblyBranchSideGapS8
import Mathlib.Tactic

/-!
# The model clauses of the bundle side at the init (`AssemblyFirstInitSideModel`)

The build leaves a bundle side (`asmFiSide`): P5's table with the bundles of the slots, P6's
spanners of the slots, the slot list `0, …, n - 1`, and the component maps. Its caps are those of
the build: `slotCap = cap = spE = eCap`, `splitB = bundleSplitBudget k M`,
`spV = 2 eCap + splitB + 1` and `mMax = M`. So its spanner parameters `asmBrSP` are `asmFiSP`, the
parameters with which the middle runs P6.

`asmFiSide_model` proves `AsmBrSideModel` for this side at the init state `tr₀`. The clauses come
from four places:
* the middle of the build: the slot map, the match of the table with the model, and P5's
  invariant with the tour;
* the lemmas on the spanners (`asmFirstInit_spanMatch`, `asmFirstInit_spanGraphOK`)
  and on the two step invariants (`asmFirstInit_slotInv`, `initTree_inactiveInv`);
* `AsmBrModelFacts` of `tr₀`, which the interface of the build gives;
* the definition of `tr₀`: the split bound, the lazy init charges and the bundle cap are those of
  the init. The cap clause asks `spV + spE + 2 ≤ (M + N + 2) ^ (capExp + 7)`, and
  `asmFi_capHyp` proves it from the cap hypothesis of the build.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-- **The bundle side that the build leaves**, for P5's tables `scProgB5`: P5's table `S5` at
`bunH`, the spanners of the slots `0, …, n - 1` at `spanH`, the slot list at `slotsPtr`, and the
maps. The caps are those of the build. -/
noncomputable def asmFiSide {depth : ℕ} (k vCap eCap M bunH : ℕ)
    (S5 : Fin eCap → Option BundleState) (m5 : BundleTableMeta eCap) (spanH : ℕ)
    (x6 : BucketSpannerMeta depth eCap) (slotsPtr n slotsCap : ℕ) (slotOf : Finset ℕ × ℤ → ℕ)
    (cmpH bktH ctH : ℕ) (comps : List (Finset ℕ)) (cslPtr : ℕ → ℕ)
    (cslL : ℕ → List (ℤ × ℕ)) (walkPot lgFac : ℕ) : AsmBrSide scProgB5 depth where
  kB := k
  slotCap := eCap
  vCap5 := vCap
  eCap5 := eCap
  cap := eCap
  splitB := bundleSplitBudget k M
  spV := 2 * eCap + bundleSplitBudget k M + 1
  spE := eCap
  mMax := M
  bunH := bunH
  bunS := S5
  xBun := m5
  spanH := spanH
  spanS := spanAfter (fun _ => none) (asmFirstInitSlotGraph S5) (List.range n)
  xSpan := x6
  slotsPtr := slotsPtr
  slots := List.range n
  slotsCap := slotsCap
  slotOf := slotOf
  cmpH := cmpH
  bktH := bktH
  ctH := ctH
  comps := comps
  cslPtr := cslPtr
  cslL := cslL
  walkPot := walkPot
  lgFac := lgFac

/-- **The cap clause of the bundle side.** The split bound is at most `112 M + 2`, so
`spV + spE + 2 ≤ 3 eCap + 112 M + 5`. With `Z = M + N + 2 ≥ 2` and `X = Z ^ capExp ≥ eCap + 2`,
this is at most `64 X Z ≤ X Z ^ 7`, since `Z ^ 6 ≥ 64`. -/
theorem asmFi_capHyp {capExp limbMul L M N vCap eCap k : ℕ} (hk : 1 ≤ k)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    SparseCoreCapHyp (capExp + 7) limbMul L M N (2 * eCap + bundleSplitBudget k M + 1) eCap := by
  obtain ⟨hX, hL⟩ := hcap
  refine ⟨?_, hL⟩
  rw [bundleSplitBudget_eq_div k M hk]
  have hdiv : (56 * M + k - 1) / k ≤ 56 * M + 1 := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_eq_add_one, show 56 * M + (k' + 1) - 1 = 56 * M + k' by omega]
    nlinarith
  set Z := M + N + 2 with hZ
  set X := Z ^ capExp with hXdef
  have hZ2 : 2 ≤ Z := by omega
  have hZ6 : 64 ≤ Z ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ Z ^ 6 := Nat.pow_le_pow_left hZ2 6
  have hpow : Z ^ (capExp + 7) = X * (Z ^ 6 * Z) := by rw [hXdef]; ring
  have hX2 : 2 ≤ X := by omega
  have h1 : 64 * Z ≤ Z ^ 6 * Z := Nat.mul_le_mul_right Z hZ6
  have h2 : X * (64 * Z) ≤ X * (Z ^ 6 * Z) := Nat.mul_le_mul_left X h1
  have h3 : 3 * X + 112 * Z ≤ X * (64 * Z) := by nlinarith
  rw [hpow]
  omega

set_option maxHeartbeats 1000000 in
/-- **The model of the bundle side at the init.** At the init state `tr₀` of the build, the side
`asmFiSide` that the build leaves meets `AsmBrSideModel`, given the facts of the middle (the slot
map, the match of P5's table, P5's invariant, and the empty slots off the list), the model facts
of the interface, `SpanGraphOK` of every start graph, the cap hypothesis, and the facts that the
invariant of the inactive components needs (a valid LSF init, a valid graph, positive lengths). -/
theorem asmFiSide_model {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ}
    {Ψ : BundleTreeState depth → ℕ} {lsfInit : LSFInit} {C_lsst : ℝ} {k M N j vCap eCap : ℕ}
    {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {bunH : ℕ}
    {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap} {spanH : ℕ}
    {x6 : BucketSpannerMeta depth eCap} {slotsPtr n : ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {cmpH bktH ctH : ℕ} {comps : List (Finset ℕ)} {cslPtr : ℕ → ℕ}
    {cslL : ℕ → List (ℤ × ℕ)}
    (hF : AsmBrModelFacts impl vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord)
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap (List.range n) slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hinv : bunRestartInv vCap eCap S5 (outCoreOrder
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord))
    (hnone : ∀ i : Fin eCap, i.1 ∉ List.range n → S5 i = none)
    (hok : ∀ q, SpanGraphOK (asmFiSP impl w M depth k eCap)
      ((initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j).initBunG q))
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) (hGm : G.m ≤ eCap)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hG : G.IsValid)
    (hℓ : ∀ e ∈ G.E, 0 < ℓ₀ e) :
    AsmBrSideModel impl w depth L capExp limbMul Ψ
      ⟨initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j, ord, vCap, eCap⟩
      (asmFiSide k vCap eCap M bunH S5 m5 spanH x6 slotsPtr n G.m slotOf cmpH bktH ctH comps cslPtr
        cslL (Ψ (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j))
        (bundleLogFactor M N)) := by
  set tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j with htr
  set SP := asmFiSP impl w M depth k eCap with hSP
  obtain ⟨hk, hrot, hScur, hBD, -, hPle, hconst, -, -, -⟩ := hF
  have hG' : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph := fun q => rfl
  have hbun : ∀ q ∈ activePairs tr, ∃ E, tr.bun q = initBundleFor tr.cs ord E tr.k :=
    fun q _ => ⟨_, rfl⟩
  have hdyn := initTree_dyn SP lsfInit (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G
    ℓ₀ ord j rfl
  have hspan := asmFirstInit_spanMatch SP (tr := tr) hMap hMatch hG' hdyn
  have hgok := asmFirstInit_spanGraphOK SP hMap hMatch hG' hrot hbun fun q _ => hok q
  refine ⟨hMap, hMatch, hspan, hScur, fun s hs => (hgok s hs).2, hk, hrot, hPle, hconst, rfl,
    asmFi_capHyp hk hcap, hBD, hinv, rfl, fun C _ => le_refl _, by simp [asmFiSide], le_refl _,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, le_refl _, le_refl _⟩
  · exact asmFirstInit_slotInv lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
      (asmFiSide k vCap eCap M bunH S5 m5 spanH x6 slotsPtr n G.m slotOf cmpH bktH ctH comps cslPtr
        cslL (Ψ tr) (bundleLogFactor M N)) (by simp [asmFiSide, hGm])
      (by simp [asmFiSide]) hnone fun i hi => spanAfter_none_of_not_mem _ hi
  · exact initTree_inactiveInv (C_lsst := C_lsst) impl w depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
      (asmFiSide k vCap eCap M bunH S5 m5 spanH x6 slotsPtr n G.m slotOf cmpH bktH ctH comps cslPtr
        cslL (Ψ tr) (bundleLogFactor M N)) hInit hG hℓ hk hok
  · exact asmFirstCrossInactiveInv_init lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
  · exact asmFirstInactiveDynInv_init impl w lsfInit depth (canonicalSparsifyParams impl)
      (dsAmortConst impl) k M N G ℓ₀ ord j
      (asmFiSide k vCap eCap M bunH S5 m5 spanH x6 slotsPtr n G.m slotOf cmpH bktH ctH comps cslPtr
        cslL (Ψ tr) (bundleLogFactor M N)) rfl
  · exact asmFirstActiveBunPartInv_init lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j hk
  · exact asmFirstActiveDynGraphInv_init lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j

end MinCostFlow.SparseCore.Program
