module

public import MinCostFlow.SparseCore.Program.EmbRefreshBound
public import MinCostFlow.SparseCore.Program.AssemblyFirstCharge

import MinCostFlow.SparseCore.Program.AssemblyFirstWalkStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Init walk bounds for newly active bucket pairs (`AssemblyFirstNewPairs`)

When a component `C` becomes newly active in a branch step (`C ∈ info.newlyActive`), the program
lazily initializes the bucket spanner of each pair `(C, b)` (`b ∈ tr.activeBuckets C`) on its
initial bundle graph `Hb = tr.initBunG (C, b)`. Its initial walks are `piTotal (DSHist.state P
⟨Hb, []⟩) e` for `e ∈ Hb.E`, and its initial bank is `dsInitBank P Hb`.

This file bounds those initial walks and initial banks against both `spanInitBound` and the lazy
init charges of the model (`lazyInitCost` and `lazyMachInitCost`, the latter sitting inside
`branchStepCharge`):
* `init_walks_le_spanInitBound`: for any valid graph `Hb` with `Hb.m ≤ P.mMax`,
  `∑ e ∈ Hb.E, (piTotal (DSHist.state P ⟨Hb, []⟩) e).length ≤ spanInitBound Pa P.L P.splitBound Hb`
  (with constant `1`), where `Pa = (canonicalSparsifyParams P.impl P.mMax).absorbTime`.
* `dsInitBank_le_mul_spanInitBound`: the initial bank `dsInitBank P Hb` of a freshly initialized
  slot is at most `dsAmortConst P.impl * spanInitBound Pa P.L P.splitBound Hb`.
* `init_walks_le_init_cost` and `initBundleTreeWithParams_walks_le_lazyInitCost`: the total length
  of the initial walks of `DynSpanner.init Hb L q sparsify` is at most `(DynSpanner.init …).cost`,
  so summed over `b ∈ st₀.activeBuckets C` it fits inside `st₀.lazyInitCost C` (with constant `1`).
* `newlyActive_walks_le_lazyMachInitCost`, `newlyActive_initBank_le_lazyMachInitCost`, and
  `lazyMachInitCost_sum_le_branchStepCharge`: summed over `b ∈ tr.activeBuckets C`, both the init
  walks and the initial banks fit inside `tr.lazyMachInitCost C`, and summed over `info.newlyActive`
  they fit inside `branchStepCharge`.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Bounds by `spanInitBound` -/

/-- `Hb.m * P_b.γ_ℓ` (as a real number) is at most `spanInitBound P_b L splitBound Hb`. -/
private lemma m_mul_gamma_le_spanInitBound_real (P_b : SparsifyParams) (L splitBound : ℕ)
    (Hb : MGraph) :
    (Hb.m : ℝ) * P_b.γ_ℓ ≤ (spanInitBound P_b L splitBound Hb : ℝ) := by
  unfold spanInitBound
  have hKt : 0 ≤ P_b.K_t := P_b.hK_t
  have hKs : 0 ≤ P_b.K_s := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hlog1 : 0 ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph Hb).n, Nat.cast_nonneg (α := ℝ) Hb.m])]
  have hlog2 : 0 ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Hb.n : ℝ) + (Hb.m : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) Hb.n, Nat.cast_nonneg (α := ℝ) Hb.m])]
  have hlog3 : 0 ≤ 1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((Hb.n + splitBound : ℕ) : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) (Hb.n + splitBound)])]
  have ht1 : 0 ≤ P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) := by
    positivity
  have ht2 : 0 ≤ P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
      (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s := by positivity
  have ht3 : 0 ≤ (Hb.n : ℝ) + (Hb.m : ℝ) +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) + 1 := by positivity
  exact le_trans (by linarith) (Nat.le_ceil _)

/-- **The init walks of a newly active pair are at most `spanInitBound`.** For any valid graph `Hb`
with `Hb.m ≤ P.mMax`, the total length of the initial walks `piTotal (DSHist.state P ⟨Hb, []⟩) e`
over `e ∈ Hb.E` is at most `spanInitBound Pa P.L P.splitBound Hb`, where
`Pa = (canonicalSparsifyParams P.impl P.mMax).absorbTime`. -/
theorem init_walks_le_spanInitBound (P : DSParams) {Hb : MGraph} (hVal : Hb.IsValid)
    (hGm : Hb.m ≤ P.mMax) :
    ∑ e ∈ Hb.E, (piTotal (DSHist.state P ⟨Hb, []⟩) e).length ≤
      spanInitBound (canonicalSparsifyParams P.impl P.mMax).absorbTime P.L P.splitBound Hb := by
  set Pa := (canonicalSparsifyParams P.impl P.mMax).absorbTime
  have hreal : ((∑ e ∈ Hb.E, (piTotal (DSHist.state P ⟨Hb, []⟩) e).length : ℕ) : ℝ) ≤
      (spanInitBound Pa P.L P.splitBound Hb : ℝ) := by
    rw [Nat.cast_sum]
    calc ∑ e ∈ Hb.E, ((piTotal (DSHist.state P ⟨Hb, []⟩) e).length : ℝ)
        ≤ ∑ _e ∈ Hb.E, Pa.γ_ℓ :=
          Finset.sum_le_sum fun e he => piTotal_init_length_le P hVal hGm he
      _ = (Hb.m : ℝ) * Pa.γ_ℓ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ (spanInitBound Pa P.L P.splitBound Hb : ℝ) :=
          m_mul_gamma_le_spanInitBound_real Pa P.L P.splitBound Hb
  exact_mod_cast hreal

/-- **The initial bank of a freshly initialized slot is paid by `spanInitBound`.**
`dsInitBank P Hb ≤ dsAmortConst P.impl * spanInitBound Pa P.L P.splitBound Hb`. -/
theorem dsInitBank_le_mul_spanInitBound (P : DSParams) {Hb : MGraph} (hVal : Hb.IsValid)
    (hGm : Hb.m ≤ P.mMax) :
    dsInitBank P Hb ≤
      dsAmortConst P.impl *
        spanInitBound (canonicalSparsifyParams P.impl P.mMax).absorbTime P.L P.splitBound Hb := by
  have hact := spanActivateCost_le_spanInitBound P Hb hVal hGm
  have hle : dsInitBank P Hb ≤ spanActivateCost P Hb := by
    unfold spanActivateCost
    omega
  exact le_trans hle hact

/-- The initial bank of `⟨Hb, []⟩` equals `dsInitBank P Hb`. -/
theorem dsHist_nil_bank_eq_dsInitBank (P : DSParams) (Hb : MGraph) :
    (⟨Hb, []⟩ : DSHist).bank P = dsInitBank P Hb := by
  simp [DSHist.bank, dsBank, dsBankTotal, dsSpent, dsInitBank, DSHist.q]

/-! ## Bounds by the lazy init charges (`lazyInitCost` and `lazyMachInitCost`) -/

/-- For any static sparsifier `sparsify`, the total length of the initial walks of
`DynSpanner.init Hb L q sparsify` is at most its model initialization cost
`(DynSpanner.init Hb L q sparsify).cost`. -/
theorem init_walks_le_init_cost (Hb : MGraph) (L q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    ∑ e ∈ Hb.E, (piTotal (DynSpanner.init Hb L q sparsify).state e).length ≤
      (DynSpanner.init Hb L q sparsify).cost := by
  by_cases hne : Hb.E.Nonempty
  · have hwalk : ∀ e ∈ Hb.E,
        (piTotal (DynSpanner.init Hb L q sparsify).state e).length ≤
          ((sparsify (activeSubgraph Hb) (activeSubgraph Hb) idEmb).emb e).length := by
      intro e he
      rw [piTotal_eq_piLtFrom]
      have h0 : e ∈ (DynSpanner.init Hb L q sparsify).state.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
        simpa [DynSpanner.init, initAt] using he
      have hnone : ∀ k : Fin (L + 1), 0 < k.1 →
          e ∉ (DynSpanner.init Hb L q sparsify).state.inDom k := by
        intro k hk
        have hkne : k.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hk
        show e ∉ if k.1 = 0 then Hb.E else ∅
        simp [hkne]
      rw [piLtFrom_eq_level_zero _ _ h0 hnone]
      change ((initCore Hb sparsify).2.1 e).length ≤ _
      simp only [initCore, dite_eq_left hne]
      exact shortcutWalk_length_le Hb _ (Hb.tail e)
    have hsum := Finset.sum_le_sum hwalk
    have hcost : ∑ e ∈ Hb.E,
        ((sparsify (activeSubgraph Hb) (activeSubgraph Hb) idEmb).emb e).length ≤
        (DynSpanner.init Hb L q sparsify).cost := by
      simp only [DynSpanner.init, initAt, initCore, dite_eq_left hne]
      omega
    exact le_trans hsum hcost
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact Nat.zero_le _

/-- **The init walks of a component fit inside `lazyInitCost`.** For any component `C` of
`st₀ = initBundleTreeWithParams …`, the total length of the initial walks of its bucket pairs
`(C, b)` (`b ∈ st₀.activeBuckets C`) is at most `st₀.lazyInitCost C`. -/
theorem initBundleTreeWithParams_walks_le_lazyInitCost (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    let st₀ := initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j
    ((st₀.activeBuckets C).sum fun b =>
        ∑ e ∈ (st₀.initBunG (C, b)).E, (piTotal (st₀.dyn (C, b)) e).length) ≤
      st₀.lazyInitCost C := by
  intro st₀
  refine Finset.sum_le_sum fun b _ => ?_
  exact init_walks_le_init_cost (st₀.initBunG (C, b)) L
    (phaseBase ((st₀.initBunG (C, b)).n + bundleSplitBudget k M) L) (sparsify M)

/-- Specialization of `initBundleTreeWithParams_walks_le_lazyInitCost` to `initBundleTreeWith`. -/
theorem initBundleTreeWith_walks_le_lazyInitCost (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
    ((st₀.activeBuckets C).sum fun b =>
        ∑ e ∈ (st₀.initBunG (C, b)).E, (piTotal (st₀.dyn (C, b)) e).length) ≤
      st₀.lazyInitCost C :=
  initBundleTreeWithParams_walks_le_lazyInitCost lsfInit L sparsify (fun _ => defaultSparsifyParams)
    1 k M N G₀ ℓ₀ ord j C

/-- **The init walks of a newly active component fit inside `lazyMachInitCost`.** Whenever
`tr.lazyMachInitCost C` dominates the sum of `tr.spanConst * spanInitBound tr.spanParams P.L
tr.splitBound (tr.initBunG (C, b))` over `b ∈ tr.activeBuckets C` (as `AsmBrSideModel` maintains
for every inactive component `C`), the init walks of `(C, b)` sum to at most
`tr.lazyMachInitCost C`. -/
theorem newlyActive_walks_le_lazyMachInitCost (P : DSParams) (tr : BundleTreeState P.L)
    (C : Finset ℕ)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : 1 ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound)
    (hG : ∀ b ∈ tr.activeBuckets C, (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P.mMax)
    (hLazy : ((tr.activeBuckets C).sum fun b =>
      tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) ≤
        tr.lazyMachInitCost C) :
    ((tr.activeBuckets C).sum fun b =>
        ∑ e ∈ (tr.initBunG (C, b)).E, (piTotal (DSHist.state P ⟨tr.initBunG (C, b), []⟩) e).length) ≤
      tr.lazyMachInitCost C := by
  refine le_trans ?_ hLazy
  refine Finset.sum_le_sum fun b hb => ?_
  have h1 := init_walks_le_spanInitBound P (hG b hb).1 (hG b hb).2
  have h2 := spanInitBound_mono (L := P.L) hP hSB (tr.initBunG (C, b))
  have h3 := Nat.le_mul_of_pos_left
    (spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) hC
  exact le_trans h1 (le_trans h2 h3)

/-- **The initial banks of a newly active component fit inside `lazyMachInitCost`.** -/
theorem newlyActive_initBank_le_lazyMachInitCost (P : DSParams) (tr : BundleTreeState P.L)
    (C : Finset ℕ)
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound ≤ tr.splitBound)
    (hG : ∀ b ∈ tr.activeBuckets C, (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P.mMax)
    (hLazy : ((tr.activeBuckets C).sum fun b =>
      tr.spanConst * spanInitBound tr.spanParams P.L tr.splitBound (tr.initBunG (C, b))) ≤
        tr.lazyMachInitCost C) :
    ((tr.activeBuckets C).sum fun b => dsInitBank P (tr.initBunG (C, b))) ≤
      tr.lazyMachInitCost C := by
  refine le_trans ?_ hLazy
  refine Finset.sum_le_sum fun b hb => ?_
  have h1 := dsInitBank_le_mul_spanInitBound P (hG b hb).1 (hG b hb).2
  have h2 := spanInitBound_mono (L := P.L) hP hSB (tr.initBunG (C, b))
  exact le_trans h1 (Nat.mul_le_mul hC h2)

/-- `stepBundleTree` preserves the lazy machine init invariant of `AsmBrSideModel`: any component
inactive after the step was inactive before, and `stepBundleTree` leaves `initBunG`,
`activeBuckets`, `spanConst`, `spanParams`, `splitBound`, and `lazyMachInitCost` unchanged. -/
theorem lazyMachInit_step_preserved {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hLazy : ∀ C ∉ tr.activeComps, ((tr.activeBuckets C).sum fun b =>
      tr.spanConst * spanInitBound tr.spanParams L tr.splitBound (tr.initBunG (C, b))) ≤
        tr.lazyMachInitCost C) :
    let tr' := (stepBundleTree sparsify tr U ord ord').state
    ∀ C ∉ tr'.activeComps, ((tr'.activeBuckets C).sum fun b =>
      tr'.spanConst * spanInitBound tr'.spanParams L tr'.splitBound (tr'.initBunG (C, b))) ≤
        tr'.lazyMachInitCost C := by
  intro tr' C hC
  have hC0 : C ∉ tr.activeComps := fun hm =>
    hC (Finset.mem_union.mpr (Or.inl hm))
  exact hLazy C hC0

/-- The lazy machine init charges of the newly active components of a step sit inside
`branchStepCharge`. -/
theorem lazyMachInitCost_sum_le_branchStepCharge {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    ((stepBundleTree sparsify tr U ord ord').newlyActive.sum fun C => tr.lazyMachInitCost C) ≤
      branchStepCharge sparsify tr U ord ord' := by
  dsimp only [branchStepCharge]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ (one_le_bundleLogFactor _ _))
  omega

end MinCostFlow.SparseCore.Program
