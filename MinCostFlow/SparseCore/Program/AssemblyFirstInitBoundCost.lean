module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitChain
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitCost
public import MinCostFlow.SparseCore.Program.AssemblyFirstInit
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Machine-cost bound for the build of a branch at its init (`AssemblyFirstInitBoundCost`)

`asmFirstInitBody_runs` (`AssemblyFirstInitChain.lean`) bounds the amortized cost of the body of
the build of a branch at its init by the sum of the bounds of its front, middle, and back parts
plus `130`. `AsmFirstInitBuildAt.runs` (`AssemblyFirstInitBuild.lean`) asks that the cost plus the
potentials of the tour and of the bundle side (`asmBrSideRep.phi`, which adds two more copies of
`specPhi` and `walkPot tr₀` beyond `asmFirstInitBody_runs`) be at most `mul * tr₀.machCost`, with
`mul` built from `capExp` and `limbMul` only.

This file proves both bounds:
* `asmFiBodyCostMul capExp limbMul` and `asmFiBodyCost_le`: the cost RHS of
  `asmFirstInitBody_runs` is at most `asmFiBodyCostMul capExp limbMul * tr₀.machCost`.
* `asmFi_specPhi_le_machCost` and `asmFi_walkPot_le_machCost`: each of `specPhi` and `walkPot tr₀`
  is at most `tr₀.machCost` (from `dsInitBank_le_mul_spanInitBound` and
  `init_walks_le_spanInitBound` summed over the active pairs).
* `asmFiBuildCostMul capExp limbMul` (`= asmFiBodyCostMul capExp limbMul + 3`) and
  `asmFiBuildCost_le`: the full cost plus potential bound needed by `AsmFirstInitBuildAt.runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Basic comparisons with `tr₀.machCost` and `spanInitBound` -/

/-- `spanInitBound` dominates `Hb.n + Hb.m + 1`. -/
theorem n_add_m_add_one_le_spanInitBound (P_b : SparsifyParams) (L splitBound : ℕ) (Hb : MGraph) :
    Hb.n + Hb.m + 1 ≤ spanInitBound P_b L splitBound Hb := by
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
  have ht3 : 0 ≤ (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) := by positivity
  have hR : ((Hb.n + Hb.m + 1 : ℕ) : ℝ) ≤
      P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) +
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitBound : ℕ) : ℝ) + 2)) + 1 := by
    push_cast at ht3 ⊢; linarith
  exact_mod_cast le_trans hR (Nat.le_ceil _)

/-- The number of connected components of a graph is at most its number of vertices. -/
theorem card_components_le_n (G : MGraph) : (components G).card ≤ G.n := by
  classical
  exact Finset.card_image_le

/-- The machine cost of `initBundleTreeWithParams` dominates `(3 * G.m + 2 + lazySum) * lg`. -/
theorem initMachCost_ge_m_add_lazy (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    (3 * G.m + 2 + tr.activeComps.sum tr.lazyMachInitCost) * bundleLogFactor M N ≤ tr.machCost := by
  intro tr
  dsimp only [tr, initBundleTreeWithParams]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The active lazy machine init charges of `initBundleTreeWithParams` sit inside `tr.machCost`. -/
theorem initMachCost_ge_activeLazy (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    tr.activeComps.sum tr.lazyMachInitCost ≤ tr.machCost := by
  intro tr
  have h1 := initMachCost_ge_m_add_lazy lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
  have hlg := one_le_bundleLogFactor M N
  have h2 : tr.activeComps.sum tr.lazyMachInitCost ≤
      (3 * G.m + 2 + tr.activeComps.sum tr.lazyMachInitCost) * bundleLogFactor M N :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ hlg)
  exact h2.trans h1

/-- At the init state `tr₀`, the active lazy init charge `tr₀.lazyMachInitCost C` equals the sum of
`tr₀.spanConst * spanInitBound tr₀.spanParams depth tr₀.splitBound (tr₀.initBunG (C, b))` over
`b ∈ tr₀.activeBuckets C`. -/
theorem initTree_lazyMachInitCost_eq {depth : ℕ} (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (C : Finset ℕ) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    tr.lazyMachInitCost C =
      (tr.activeBuckets C).sum fun b =>
        tr.spanConst * spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b)) :=
  rfl

/-- Under `SparseCoreCapHyp`, `tourLog eCap ≤ capExp * bundleLogFactor M N`. -/
theorem tourLog_le_capExp_mul_lg {capExp limbMul L M N vCap eCap : ℕ}
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    tourLog eCap ≤ capExp * bundleLogFactor M N :=
  ordStoreLog_le_capExp_mul_lg hcap

/-! ## Active-slot sums bounded by the lazy init charges of `tr₀` -/

/-- The sum of `bundleExportCost (slotB S5 s)` over `slots` is at most `100` times the active lazy
init charges of `tr₀`. -/
theorem asmFi_bundleExportCost_sum_le {depth M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S5 : Fin eCap → Option BundleState}
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    (slots.map fun s => bundleExportCost (slotB S5 s)).sum ≤
      100 * tr.activeComps.sum tr.lazyMachInitCost := by
  intro tr
  have hc1 : 1 ≤ tr.spanConst := one_le_dsAmortConst impl
  rw [hMap.sum_map_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun C hC => ?_
  rw [initTree_lazyMachInitCost_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨hs, B, hSB, hag⟩ := hMatch (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
  rw [slotB_eq hs hSB]
  have hVn : B.vertices.card = (tr.initBunG (C, b)).n := by
    show B.vertices.card = (normGraph (tr.bun (C, b)).graph).V.card
    rw [normGraph_V]
    exact congrArg Finset.card hag.1
  have hEm : B.edges.card = (tr.initBunG (C, b)).m := by
    show B.edges.card = (normGraph (tr.bun (C, b)).graph).E.card
    rw [normGraph_E]
    exact congrArg Finset.card hag.2.1
  have h1 : bundleExportCost B ≤ 100 * ((tr.initBunG (C, b)).n + (tr.initBunG (C, b)).m + 1) := by
    unfold bundleExportCost; omega
  have h2 := n_add_m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))
  have h3 := Nat.le_mul_of_pos_left
    (spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) hc1
  exact h1.trans (Nat.mul_le_mul_left 100 (h2.trans h3))

/-- The sum of `spanActivateCost` over `slots` is at most the active lazy init charges of `tr₀`. -/
theorem asmFi_spanActivateCost_sum_le {depth w M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S5 : Fin eCap → Option BundleState}
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ slots, SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s))
    (hPle : SparsifyParamsLe (canonicalSparsifyParams impl M).absorbTime
      (canonicalSparsifyParams impl M)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    (slots.map fun s =>
        spanActivateCost (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)).sum ≤
      tr.activeComps.sum tr.lazyMachInitCost := by
  intro tr
  set SP := asmFiSP impl w M depth k eCap with hSP
  rw [hMap.sum_map_eq]
  refine Finset.sum_le_sum fun C hC => ?_
  rw [initTree_lazyMachInitCost_eq]
  refine Finset.sum_le_sum fun b hb => ?_
  have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
  have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) hq
  have hGeq : asmFirstInitSlotGraph S5 (slotOf (C, b)) = tr.initBunG (C, b) :=
    asmFirstInitSlotGraph_slotOf hMatch (fun _ => rfl) hq
  have hokCB : SpanGraphOK SP (tr.initBunG (C, b)) := hGeq ▸ hok _ hmem
  rw [hGeq]
  have h1 := spanActivateCost_le_spanInitBound SP (tr.initBunG (C, b))
    hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1
  have h2 := spanInitBound_mono (L := depth) hPle (le_refl (bundleSplitBudget k M))
    (tr.initBunG (C, b))
  exact h1.trans (Nat.mul_le_mul_left (dsAmortConst impl) h2)

/-- `rebuildSize + slots.length` on `spanAfter` at the init is at most `2` times the active lazy
init charges of `tr₀`. -/
theorem asmFi_rebuildSize_le_lazy {depth w M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S5 : Fin eCap → Option BundleState}
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ slots, SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    let SP := asmFiSP impl w M depth k eCap
    let S6 := spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5) slots
    rebuildSize SP S6 slots + slots.length ≤ 2 * tr.activeComps.sum tr.lazyMachInitCost := by
  intro tr SP S6
  have hc1 : 1 ≤ tr.spanConst := one_le_dsAmortConst impl
  unfold rebuildSize
  rw [hMap.sum_map_eq, hMap.length_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun C hC => ?_
  rw [initTree_lazyMachInitCost_eq, Finset.mul_sum, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b hb => ?_
  have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
  have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) hq
  have hs : slotOf (C, b) < eCap := (hMap.2.2.2.2 _ hmem).2
  have hGeq : asmFirstInitSlotGraph S5 (slotOf (C, b)) = tr.initBunG (C, b) :=
    asmFirstInitSlotGraph_slotOf hMatch (fun _ => rfl) hq
  have hokCB : SpanGraphOK SP (tr.initBunG (C, b)) := hGeq ▸ hok _ hmem
  have hS : S6 ⟨slotOf (C, b), hs⟩ = some ⟨tr.initBunG (C, b), []⟩ := by
    simp [S6, spanAfter, hmem, hGeq]
  have hGE : (slotGE SP S6 (slotOf (C, b))).card = (tr.initBunG (C, b)).m := by
    simp only [slotGE, hs, ↓reduceDIte, hS, dsHist_init_G_eq]; rfl
  have hHE : (slotHE SP S6 (slotOf (C, b))).card ≤ (tr.initBunG (C, b)).m := by
    simp only [slotHE, hs, ↓reduceDIte, hS]
    exact Finset.card_le_card (dsHist_init_H_sub_E SP hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1)
  have hBnd : (tr.initBunG (C, b)).m + 1 ≤
      tr.spanConst * spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b)) :=
    (m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))).trans
      (Nat.le_mul_of_pos_left _ hc1)
  show (slotGE SP S6 (slotOf (C, b))).card + (slotHE SP S6 (slotOf (C, b))).card + 1 ≤
    2 * (tr.spanConst * spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b)))
  omega

/-- `embRefreshSizeAt + slots.length` on `spanAfter` at the init is at most `4` times the active
lazy init charges of `tr₀`. -/
theorem asmFi_embRefreshSizeAt_le_lazy {depth w M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S5 : Fin eCap → Option BundleState}
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ slots, SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s))
    (hPle : SparsifyParamsLe (canonicalSparsifyParams impl M).absorbTime
      (canonicalSparsifyParams impl M)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    let SP := asmFiSP impl w M depth k eCap
    let S6 := spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5) slots
    embRefreshSizeAt SP S6 slots + slots.length ≤ 4 * tr.activeComps.sum tr.lazyMachInitCost := by
  intro tr SP S6
  have hc1 : 1 ≤ tr.spanConst := one_le_dsAmortConst impl
  have hfresh : ∀ s ∈ slots, ∀ (hs : s < eCap) (d : DSHist), S6 ⟨s, hs⟩ = some d → d.Us = [] := by
    intro s hm hs d hd
    have hEq : some d = some ⟨asmFirstInitSlotGraph S5 s, []⟩ := by
      simpa [S6, spanAfter, hm] using hd.symm
    cases Option.some.inj hEq
    rfl
  rw [embRefreshSizeAt_eq_walkSize SP S6 slots hfresh]
  unfold embRefreshWalkSize
  rw [hMap.sum_map_eq, hMap.length_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun C hC => ?_
  rw [initTree_lazyMachInitCost_eq, Finset.mul_sum, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b hb => ?_
  have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
  have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) hq
  have hs : slotOf (C, b) < eCap := (hMap.2.2.2.2 _ hmem).2
  have hGeq : asmFirstInitSlotGraph S5 (slotOf (C, b)) = tr.initBunG (C, b) :=
    asmFirstInitSlotGraph_slotOf hMatch (fun _ => rfl) hq
  have hokCB : SpanGraphOK SP (tr.initBunG (C, b)) := hGeq ▸ hok _ hmem
  have hS : S6 ⟨slotOf (C, b), hs⟩ = some ⟨tr.initBunG (C, b), []⟩ := by
    simp [S6, spanAfter, hmem, hGeq]
  have h1 := slotWalkWords_sum_le_spanInitBound SP hs hS
    hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1
  have h2 := spanInitBound_mono (L := depth) hPle (le_refl (bundleSplitBudget k M))
    (tr.initBunG (C, b))
  have h3 := Nat.le_mul_of_pos_left
    (spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) hc1
  have h4 : 1 ≤ tr.spanConst * spanInitBound tr.spanParams depth tr.splitBound
      (tr.initBunG (C, b)) :=
    (le_trans (by omega) (m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound
      (tr.initBunG (C, b)))).trans h3
  have h5 := h1.trans (Nat.mul_le_mul_left 3 (h2.trans h3))
  show ((slotGE SP S6 (slotOf (C, b))).sum fun e =>
        Read.walkWords (slotWalk SP S6 (slotOf (C, b)) e) + 2) + 1 + 1 ≤
      4 * (tr.spanConst * spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b)))
  omega

/-! ## Potential bounds (`specPhi` and `walkPot`) for `AsmFirstInitBuildAt` -/

/-- **The log-weighted spanner potential `bundleLogFactor M N * specPhi` at the init is at most
`tr₀.machCost`.** -/
theorem asmFi_specPhi_mul_lg_le_machCost {depth w M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S5 : Fin eCap → Option BundleState}
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ slots, SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s))
    (hPle : SparsifyParamsLe (canonicalSparsifyParams impl M).absorbTime
      (canonicalSparsifyParams impl M)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    let SP := asmFiSP impl w M depth k eCap
    let S6 := spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5) slots
    bundleLogFactor M N * specPhi SP S6 ≤ tr.machCost := by
  intro tr SP S6
  have hsum : specPhi SP S6 ≤
      (slots.map fun s => dsInitBank SP (asmFirstInitSlotGraph S5 s)).sum := by
    have hsplit : specPhi SP S6 =
        (Finset.univ.filter fun i : Fin eCap => i.1 ∈ slots).sum
          fun i => dsInitBank SP (asmFirstInitSlotGraph S5 i.1) := by
      unfold specPhi
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin eCap => i.1 ∈ slots)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i : Fin eCap => ¬ i.1 ∈ slots)
        (fun i hi => by
          have hnot : i.1 ∉ slots := (Finset.mem_filter.mp hi).2
          simp [S6, spanAfter, hnot]), add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hm : i.1 ∈ slots := (Finset.mem_filter.mp hi).2
      simp only [S6, spanAfter, hm, ↓reduceIte]
      exact dsHist_nil_bank_eq_dsInitBank SP (asmFirstInitSlotGraph S5 i.1)
    rw [hsplit, ← List.sum_toFinset _ hMap.1]
    have hbij : (Finset.univ.filter fun i : Fin eCap => i.1 ∈ slots).sum
        (fun i => dsInitBank SP (asmFirstInitSlotGraph S5 i.1)) =
        slots.toFinset.sum (fun s => dsInitBank SP (asmFirstInitSlotGraph S5 s)) := by
      refine Finset.sum_nbij (fun i : Fin eCap => i.1) ?_ ?_ ?_ ?_
      · intro i hi; exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
      · intro i₁ _ i₂ _ heq; exact Fin.ext heq
      · intro s hs
        have hms := List.mem_toFinset.mp hs
        have hlt : s < eCap := (hMap.2.2.2.2 s hms).2
        exact ⟨⟨s, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩, rfl⟩
      · intro i _; rfl
    exact le_of_eq hbij
  have hbank : (slots.map fun s => dsInitBank SP (asmFirstInitSlotGraph S5 s)).sum ≤
      tr.activeComps.sum tr.lazyMachInitCost := by
    rw [hMap.sum_map_eq]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [initTree_lazyMachInitCost_eq]
    refine Finset.sum_le_sum fun b hb => ?_
    have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
    have hmem : slotOf (C, b) ∈ slots := hMap.2.1 (C, b) hq
    have hGeq : asmFirstInitSlotGraph S5 (slotOf (C, b)) = tr.initBunG (C, b) :=
      asmFirstInitSlotGraph_slotOf hMatch (fun _ => rfl) hq
    have hokCB : SpanGraphOK SP (tr.initBunG (C, b)) := hGeq ▸ hok _ hmem
    rw [hGeq]
    have h1 := dsInitBank_le_mul_spanInitBound SP hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1
    have h2 := spanInitBound_mono (L := depth) hPle (le_refl (bundleSplitBudget k M))
      (tr.initBunG (C, b))
    exact h1.trans (Nat.mul_le_mul_left (dsAmortConst impl) h2)
  have hmc : tr.activeComps.sum tr.lazyMachInitCost * bundleLogFactor M N ≤ tr.machCost :=
    (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans
      (initMachCost_ge_m_add_lazy lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
  calc bundleLogFactor M N * specPhi SP S6
      = specPhi SP S6 * bundleLogFactor M N := Nat.mul_comm _ _
    _ ≤ tr.activeComps.sum tr.lazyMachInitCost * bundleLogFactor M N :=
        Nat.mul_le_mul_right _ (hsum.trans hbank)
    _ ≤ tr.machCost := hmc

/-- **The spanner potential `specPhi` at the init is at most `tr₀.machCost`.** -/
theorem asmFi_specPhi_le_machCost {depth w M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S5 : Fin eCap → Option BundleState}
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ slots, SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s))
    (hPle : SparsifyParamsLe (canonicalSparsifyParams impl M).absorbTime
      (canonicalSparsifyParams impl M)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    let SP := asmFiSP impl w M depth k eCap
    let S6 := spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5) slots
    specPhi SP S6 ≤ tr.machCost :=
  (Nat.le_mul_of_pos_left _ (one_le_bundleLogFactor M N)).trans
    (asmFi_specPhi_mul_lg_le_machCost hMap hMatch hok hPle)

/-- **The walk potential `walkPot tr₀` at the init is at most `tr₀.machCost`.** -/
theorem asmFi_walkPot_le_machCost {depth w M N k eCap : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} {j : ℕ}
    (hok : ∀ q ∈ activePairs
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j),
      SpanGraphOK (asmFiSP impl w M depth k eCap)
        ((initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j).initBunG q))
    (hPle : SparsifyParamsLe (canonicalSparsifyParams impl M).absorbTime
      (canonicalSparsifyParams impl M)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    walkPot tr ≤ tr.machCost := by
  intro tr
  set SP := asmFiSP impl w M depth k eCap with hSP
  have hc1 : 1 ≤ tr.spanConst := one_le_dsAmortConst impl
  have hlazy : walkPot tr ≤ tr.activeComps.sum tr.lazyMachInitCost := by
    unfold walkPot
    refine Finset.sum_le_sum fun C hC => ?_
    rw [initTree_lazyMachInitCost_eq]
    refine Finset.sum_le_sum fun b hb => ?_
    have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
    have hokCB := hok (C, b) hq
    have hdyn : tr.dyn (C, b) = DSHist.state SP ⟨tr.initBunG (C, b), []⟩ :=
      initTree_dyn SP lsfInit (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
        rfl (C, b)
    have hsub : tr.S_cur.E ∩ (tr.dyn (C, b)).G.E ⊆ (tr.initBunG (C, b)).E := by
      rw [hdyn, dsHist_init_G_eq]
      exact Finset.inter_subset_right
    have h1 : (tr.S_cur.E ∩ (tr.dyn (C, b)).G.E).sum
        (fun e => (piTotal (tr.dyn (C, b)) e).length) ≤
        (tr.initBunG (C, b)).E.sum (fun e => (piTotal (DSHist.state SP ⟨tr.initBunG (C, b), []⟩) e).length) := by
      rw [hdyn]
      exact Finset.sum_le_sum_of_subset hsub
    have h2 := init_walks_le_spanInitBound SP hokCB.2.2.2.2.2.2.1 hokCB.2.2.2.2.2.2.2.1
    have h3 := spanInitBound_mono (L := depth) hPle (le_refl (bundleSplitBudget k M))
      (tr.initBunG (C, b))
    have h4 := Nat.le_mul_of_pos_left
      (spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) hc1
    exact h1.trans (h2.trans (h3.trans h4))
  exact hlazy.trans
    (initMachCost_ge_activeLazy lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)

/-! ## Cost multipliers and total bounds -/

/-- **Cost multiplier of `asmFirstInitBody_runs`**, built from `capExp` and `limbMul` only. -/
def asmFiBodyCostMul (capExp limbMul : ℕ) : ℕ :=
  (3 * tourBranchInitMul * capExp + bktTableMul capExp limbMul + 1360) +
    (tourMul * capExp + bunPhiMul + 999) +
    (tourMarkExportMul * capExp + 4 * embRefreshMul + 3980) + 130

/-- **Cost multiplier of `AsmFirstInitBuildAt`**, built from `capExp` and `limbMul` only: adds
`320 * (capExp + 1) + 300` to `asmFiBodyCostMul` for the log-weighted `specPhi` and `300 * walkPot tr₀`
terms in `asmBrSideRep.phi`. -/
def asmFiBuildCostMul (capExp limbMul : ℕ) : ℕ :=
  asmFiBodyCostMul capExp limbMul + 320 * (capExp + 1) + 300

/-- Helper: `rList.map (fun v => c * (f v + 1))` factors out `c`. -/
private lemma sum_map_mul_add_one (l : List ℕ) (c : ℕ) (f : ℕ → ℕ) :
    (l.map fun v => c * (f v + 1)).sum = c * ((l.map f).sum + l.length) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- **The cost bound of `asmFirstInitBody_runs` is at most
`asmFiBodyCostMul capExp limbMul * tr₀.machCost`.** -/
theorem asmFiBodyCost_le {depth w capExp limbMul M N vCap eCap k L cWords expPtr expEnd : ℕ}
    {impl : SparsifyImpl} {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End}
    {j : ℕ} {mem : ℕ → ℕ} {S D rList : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S5 : Fin eCap → Option BundleState}
    (hGval : G.IsValid) (hM : G.m ≤ M) (hN : G.n ≤ N) (hnm : G.n ≤ G.m + 1) (hcw : cWords ≤ 1 + 6 * G.m)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j).cs)
    (hF : AsmBrModelFacts impl vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord)
    (hSlen : S.length ≤ G.m) (hDlen : D.length ≤ S.length)
    (hrSorted : rList.Pairwise (· < ·))
    (hrIff : ∀ v, v ∈ rList ↔ v ∈
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j).cs.lsf.F.R)
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap (List.range D.length) slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ List.range D.length,
      SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    let SP := asmFiSP impl w M depth k eCap
    let S6 := spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
      (List.range D.length)
    (tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 +
      bucketTableCost (mem (expPtr + 6)) L G.m + compMapCost G.n G.m +
      slotListCost G.m (components G).card (mem (mem (expPtr + 1) + 2)) + 200) +
    (rootsListCost rList.length +
      bundleInitSlotsCost tourBundleSpec eCap D.length S.length (outCoreOrder tr ord) rList +
      bunPhiMul * (2 * S.length) +
      ((List.range D.length).map fun s => bundleExportCost (slotB S5 s)).sum +
      ((List.range D.length).map fun s =>
        spanActivateCost SP (asmFirstInitSlotGraph S5 s)).sum +
      200 * D.length + 600) +
    (rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card +
      (840 * (rebuildSize SP S6 (List.range D.length) + D.length + 1) +
        130 * tr.cs.lsf.F.R.card + 200) +
      (200 * (tr.S_cur.n + tr.S_cur.m + 1) +
        tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20) +
      (30 * G.m + embRefreshMul * (embRefreshSizeAt SP S6 (List.range D.length) + D.length + 1) +
        80) + 100) +
    130 ≤
    asmFiBodyCostMul capExp limbMul * tr.machCost := by
  intro tr SP S6
  set lg := bundleLogFactor M N with hlgDef
  set mc := tr.machCost with hmcDef
  set lazySum := tr.activeComps.sum tr.lazyMachInitCost with hlazyDef
  have hlg : 1 ≤ lg := one_le_bundleLogFactor M N
  have hmc_ge : (3 * G.m + 2) * lg ≤ mc :=
    initMachCost_ge lsfInit (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl)
      (dsAmortConst impl) k M N G ℓ₀ ord j
  have hmc_lsf : lsfInitSize G * lg * lg ≤ mc :=
    initMachCost_ge_lsf lsfInit (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl)
      (dsAmortConst impl) k M N G ℓ₀ ord j
  have hmc_lazy : lazySum ≤ mc :=
    initMachCost_ge_activeLazy lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
  have hmc_m : 3 * G.m + 2 ≤ mc := (Nat.le_mul_of_pos_right _ hlg).trans hmc_ge
  have hmc1 : 1 ≤ mc := by omega
  have hmc_mlazy : 3 * G.m + 2 + lazySum ≤ mc := by
    have h1 := initMachCost_ge_m_add_lazy lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    exact (Nat.le_mul_of_pos_right _ hlg).trans h1
  -- Model facts: rooted spanning forest, `S_cur` sizes, `SparsifyParamsLe`, core order
  obtain ⟨-, hrot, -, -, -, hPle, -, -, -, -⟩ := id hF
  obtain ⟨C_lsst, ℓ₁, hI, ρ, hρ⟩ := hrot
  have hRF : tr.cs.lsf.F.IsRootedSpanningForestOf G := compLSF_RF_isRSF hI
  have hFn : tr.cs.lsf.F.F.n = G.n := by unfold MGraph.n; rw [hRF.2.1]
  have hFm : tr.cs.lsf.F.F.m ≤ G.m := Finset.card_le_card hRF.2.2.2.2.2.1
  have hRcard : tr.cs.lsf.F.R.card ≤ G.n := Finset.card_le_card hRF.2.2.1
  have hScur := scur_size_le_of_facts hF
  have hSn : tr.S_cur.n ≤ G.n := hScur.1
  have hSm : tr.S_cur.m ≤ G.m := hScur.2
  have hlogE : tourLog eCap ≤ capExp * lg := tourLog_le_capExp_mul_lg hcap
  have hordE : ordStoreLog eCap ≤ capExp * lg := ordStoreLog_le_capExp_mul_lg hcap
  have hLw : mem (expPtr + 6) ≤
      L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) :=
    hExp.2.2.2.2.2.2.2.2.1
  have hnF : mem (mem (expPtr + 1) + 2) ≤ G.m := by
    have hfe : mem (mem (expPtr + 1) + 2) = tr.cs.lsf.F.F.m := hExp.2.2.2.2.2.1.2.1
    omega
  have hrNd : rList.Nodup := hrSorted.imp fun h => Nat.ne_of_lt h
  have hrLen : rList.length = tr.cs.lsf.F.R.card := by
    rw [← List.toFinset_card_of_nodup hrNd]
    congr 1; ext v; exact List.mem_toFinset.trans (hrIff v)
  -- Part 1: Front
  have hP1 : tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 +
      bucketTableCost (mem (expPtr + 6)) L G.m + compMapCost G.n G.m +
      slotListCost G.m (components G).card (mem (mem (expPtr + 1) + 2)) + 200 ≤
      (3 * tourBranchInitMul * capExp + bktTableMul capExp limbMul + 1360) * mc := by
    have ht1 : tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap ≤
        3 * tourBranchInitMul * capExp * mc := by
      have hsz : 1 + cWords + G.m + G.n ≤ 3 * (3 * G.m + 2) := by omega
      calc tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap
          ≤ tourBranchInitMul * (3 * (3 * G.m + 2)) * (capExp * lg) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hsz) hlogE
        _ = 3 * tourBranchInitMul * capExp * ((3 * G.m + 2) * lg) := by ring
        _ ≤ 3 * tourBranchInitMul * capExp * mc := Nat.mul_le_mul_left _ hmc_ge
    have ht2 : bucketTableCost (mem (expPtr + 6)) L G.m ≤ bktTableMul capExp limbMul * mc :=
      bucketTableCost_le hcap.2 hLw hGval hmc_lsf hmc1
    have ht3 : compMapCost G.n G.m ≤ 600 * mc := compMapCost_le hnm hlg hmc_ge
    have ht4 : slotListCost G.m (components G).card (mem (mem (expPtr + 1) + 2)) ≤ 500 * mc :=
      slotListCost_le ((card_components_le_n G).trans hnm) (by omega) hM hmc_ge
    have e : (3 * tourBranchInitMul * capExp + bktTableMul capExp limbMul + 1360) * mc =
        3 * tourBranchInitMul * capExp * mc + bktTableMul capExp limbMul * mc +
        600 * mc + 500 * mc + 260 * mc := by ring
    omega
  -- Part 2: Middle
  have hP2 : rootsListCost rList.length +
      bundleInitSlotsCost tourBundleSpec eCap D.length S.length (outCoreOrder tr ord) rList +
      bunPhiMul * (2 * S.length) +
      ((List.range D.length).map fun s => bundleExportCost (slotB S5 s)).sum +
      ((List.range D.length).map fun s =>
        spanActivateCost SP (asmFirstInitSlotGraph S5 s)).sum +
      200 * D.length + 600 ≤
      (tourMul * capExp + bunPhiMul + 999) * mc := by
    have hroots : rootsListCost rList.length ≤ 263 * mc := by
      unfold rootsListCost
      have hlogR : Nat.log 2 (rList.length + 1) + 1 ≤ lg := by
        have h1 : Nat.log 2 (rList.length + 1) ≤ Nat.log 2 (M + N + 2) :=
          Nat.log_mono_right (by omega)
        exact (Nat.add_le_add_right h1 1).trans (logStep_le_bundleLogFactor M N)
      have h1 : 200 * rList.length * (Nat.log 2 (rList.length + 1) + 1) ≤ 200 * mc := by
        calc 200 * rList.length * (Nat.log 2 (rList.length + 1) + 1)
            ≤ 200 * (3 * G.m + 2) * lg :=
              Nat.mul_le_mul (Nat.mul_le_mul_left 200 (by omega)) hlogR
          _ = 200 * ((3 * G.m + 2) * lg) := by ring
          _ ≤ 200 * mc := Nat.mul_le_mul_left 200 hmc_ge
      have h2 : 25 * rList.length + 100 ≤ 63 * mc := by omega
      omega
    have hbunI : bundleInitSlotsCost tourBundleSpec eCap D.length S.length
        (outCoreOrder tr ord) rList ≤ (tourMul * capExp + 335) * mc := by
      unfold bundleInitSlotsCost
      have hC : CoreCordOf tr.cs ord (outCoreOrder tr ord) :=
        coreCordOf_outCoreOrder ⟨C_lsst, ℓ₁, hI, ρ, hρ⟩
      have hsumLen : (rList.map fun v => (outCoreOrder tr ord v).length).sum ≤ 2 * G.m :=
        (coreCord_facts hC).2.2.2 rList hrNd
      rw [sum_map_mul_add_one]
      have hmul : tourBundleSpec.mul = tourMul := rfl
      rw [hmul]
      have hfac : tourMul * ordStoreLog eCap + 220 ≤ (tourMul * capExp + 220) * lg := by
        have h1 : tourMul * ordStoreLog eCap ≤ tourMul * (capExp * lg) :=
          Nat.mul_le_mul_left tourMul hordE
        have h2 : 220 ≤ 220 * lg := Nat.le_mul_of_pos_right 220 hlg
        have e : (tourMul * capExp + 220) * lg = tourMul * (capExp * lg) + 220 * lg := by ring
        omega
      have hloop : (tourMul * ordStoreLog eCap + 220) *
          ((rList.map fun v => (outCoreOrder tr ord v).length).sum + rList.length) ≤
          (tourMul * capExp + 220) * mc := by
        calc _ ≤ ((tourMul * capExp + 220) * lg) * (3 * G.m + 2) :=
              Nat.mul_le_mul hfac (by omega)
          _ = (tourMul * capExp + 220) * ((3 * G.m + 2) * lg) := by ring
          _ ≤ (tourMul * capExp + 220) * mc := Nat.mul_le_mul_left _ hmc_ge
      have hlin : 125 * D.length + 70 * S.length + 50 * rList.length + 180 ≤ 115 * mc := by omega
      have e : (tourMul * capExp + 335) * mc = (tourMul * capExp + 220) * mc + 115 * mc := by ring
      omega
    have hphiB : bunPhiMul * (2 * S.length) ≤ bunPhiMul * mc :=
      Nat.mul_le_mul_left bunPhiMul (by omega)
    have hexpB : ((List.range D.length).map fun s => bundleExportCost (slotB S5 s)).sum ≤
        100 * mc :=
      (asmFi_bundleExportCost_sum_le hMap hMatch).trans (Nat.mul_le_mul_left 100 hmc_lazy)
    have hspA : ((List.range D.length).map fun s =>
        spanActivateCost SP (asmFirstInitSlotGraph S5 s)).sum ≤ mc :=
      (asmFi_spanActivateCost_sum_le hMap hMatch hok hPle).trans hmc_lazy
    have hD200 : 200 * D.length + 600 ≤ 300 * mc := by omega
    have e : (tourMul * capExp + bunPhiMul + 999) * mc =
        263 * mc + (tourMul * capExp + 335) * mc + bunPhiMul * mc + 100 * mc + mc + 300 * mc := by
      ring
    omega
  -- Part 3: Back
  have hP3 : rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card +
      (840 * (rebuildSize SP S6 (List.range D.length) + D.length + 1) +
        130 * tr.cs.lsf.F.R.card + 200) +
      (200 * (tr.S_cur.n + tr.S_cur.m + 1) +
        tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20) +
      (30 * G.m + embRefreshMul * (embRefreshSizeAt SP S6 (List.range D.length) + D.length + 1) +
        80) + 100 ≤
      (tourMarkExportMul * capExp + 4 * embRefreshMul + 3980) * mc := by
    have hrt : rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card ≤ 885 * mc := by
      unfold rootTblCost compMapCost; omega
    have hrb : 840 * (rebuildSize SP S6 (List.range D.length) + D.length + 1) +
        130 * tr.cs.lsf.F.R.card + 200 ≤ 2685 * mc := by
      have h1 : rebuildSize SP S6 (List.range D.length) + D.length ≤ 2 * lazySum := by
        simpa only [List.length_range] using asmFi_rebuildSize_le_lazy hMap hMatch hok
      have h2 : rebuildSize SP S6 (List.range D.length) + D.length + 1 ≤ 3 * mc := by omega
      have h3 : 840 * (rebuildSize SP S6 (List.range D.length) + D.length + 1) ≤ 2520 * mc := by
        calc _ ≤ 840 * (3 * mc) := Nat.mul_le_mul_left 840 h2
          _ = 2520 * mc := by ring
      have h4 : 130 * tr.cs.lsf.F.R.card + 200 ≤ 165 * mc := by omega
      omega
    have hmk : 200 * (tr.S_cur.n + tr.S_cur.m + 1) +
        tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20 ≤
        (tourMarkExportMul * capExp + 210) * mc := by
      have h1 : tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap ≤
          tourMarkExportMul * capExp * mc := by
        calc tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap
            ≤ tourMarkExportMul * (3 * G.m + 2) * (capExp * lg) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hlogE
          _ = tourMarkExportMul * capExp * ((3 * G.m + 2) * lg) := by ring
          _ ≤ tourMarkExportMul * capExp * mc := Nat.mul_le_mul_left _ hmc_ge
      have h2 : 200 * (tr.S_cur.n + tr.S_cur.m + 1) + 20 ≤ 210 * mc := by omega
      have e : (tourMarkExportMul * capExp + 210) * mc =
          tourMarkExportMul * capExp * mc + 210 * mc := by ring
      omega
    have hemb : 30 * G.m +
        embRefreshMul * (embRefreshSizeAt SP S6 (List.range D.length) + D.length + 1) + 80 ≤
        (4 * embRefreshMul + 100) * mc := by
      have h1 : embRefreshSizeAt SP S6 (List.range D.length) + D.length ≤ 4 * lazySum := by
        simpa only [List.length_range] using asmFi_embRefreshSizeAt_le_lazy hMap hMatch hok hPle
      have h2 : embRefreshSizeAt SP S6 (List.range D.length) + D.length + 1 ≤ 4 * mc := by
        have : 1 ≤ 3 * G.m + 2 := by omega
        omega
      have h3 : embRefreshMul * (embRefreshSizeAt SP S6 (List.range D.length) + D.length + 1) ≤
          4 * embRefreshMul * mc := by
        calc _ ≤ embRefreshMul * (4 * mc) := Nat.mul_le_mul_left embRefreshMul h2
          _ = 4 * embRefreshMul * mc := by ring
      have h4 : 30 * G.m + 80 ≤ 100 * mc := by omega
      have e : (4 * embRefreshMul + 100) * mc = 4 * embRefreshMul * mc + 100 * mc := by ring
      omega
    have h100 : 100 ≤ 100 * mc := Nat.le_mul_of_pos_right 100 hmc1
    have e : (tourMarkExportMul * capExp + 4 * embRefreshMul + 3980) * mc =
        885 * mc + 2685 * mc + (tourMarkExportMul * capExp + 210) * mc +
        (4 * embRefreshMul + 100) * mc + 100 * mc := by ring
    exact (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrt hrb) hmk) hemb) h100).trans
      (le_of_eq e.symm)
  -- Combine parts 1, 2, 3 and `+ 130`
  have h130 : 130 ≤ 130 * mc := Nat.le_mul_of_pos_right 130 hmc1
  have e : asmFiBodyCostMul capExp limbMul * mc =
      (3 * tourBranchInitMul * capExp + bktTableMul capExp limbMul + 1360) * mc +
      (tourMul * capExp + bunPhiMul + 999) * mc +
      (tourMarkExportMul * capExp + 4 * embRefreshMul + 3980) * mc + 130 * mc := by
    unfold asmFiBodyCostMul; ring
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hP1 hP2) hP3) h130).trans
    (le_of_eq e.symm)

/-- **The full build cost bound for `AsmFirstInitBuildAt.runs`**: adds `2 * specPhi + walkPot tr₀`
to the bound of `asmFirstInitBody_runs` and bounds the total by
`asmFiBuildCostMul capExp limbMul * tr₀.machCost`. -/
theorem asmFiBuildCost_le {depth w capExp limbMul M N vCap eCap k L cWords expPtr expEnd : ℕ}
    {impl : SparsifyImpl} {lsfInit : LSFInit} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End}
    {j : ℕ} {mem : ℕ → ℕ} {S D rList : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S5 : Fin eCap → Option BundleState}
    (hGval : G.IsValid) (hM : G.m ≤ M) (hN : G.n ≤ N) (hnm : G.n ≤ G.m + 1) (hcw : cWords ≤ 1 + 6 * G.m)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j).cs)
    (hF : AsmBrModelFacts impl vCap eCap
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) ord)
    (hSlen : S.length ≤ G.m) (hDlen : D.length ≤ S.length)
    (hrSorted : rList.Pairwise (· < ·))
    (hrIff : ∀ v, v ∈ rList ↔ v ∈
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j).cs.lsf.F.R)
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j)
      eCap eCap (List.range D.length) slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j) slotOf S5)
    (hok : ∀ s ∈ List.range D.length,
      SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)) :
    let tr := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
    let SP := asmFiSP impl w M depth k eCap
    let S6 := spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
      (List.range D.length)
    (tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 +
      bucketTableCost (mem (expPtr + 6)) L G.m + compMapCost G.n G.m +
      slotListCost G.m (components G).card (mem (mem (expPtr + 1) + 2)) + 200) +
    (rootsListCost rList.length +
      bundleInitSlotsCost tourBundleSpec eCap D.length S.length (outCoreOrder tr ord) rList +
      bunPhiMul * (2 * S.length) +
      ((List.range D.length).map fun s => bundleExportCost (slotB S5 s)).sum +
      ((List.range D.length).map fun s =>
        spanActivateCost SP (asmFirstInitSlotGraph S5 s)).sum +
      200 * D.length + 600) +
    (rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card +
      (840 * (rebuildSize SP S6 (List.range D.length) + D.length + 1) +
        130 * tr.cs.lsf.F.R.card + 200) +
      (200 * (tr.S_cur.n + tr.S_cur.m + 1) +
        tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20) +
      (30 * G.m + embRefreshMul * (embRefreshSizeAt SP S6 (List.range D.length) + D.length + 1) +
        80) + 100) +
    130 + 320 * (capExp + 1) * bundleLogFactor M N * specPhi SP S6 + 300 * walkPot tr ≤
    asmFiBuildCostMul capExp limbMul * tr.machCost := by
  intro tr SP S6
  have hBody := asmFiBodyCost_le hGval hM hN hnm hcw hcap hExp hF hSlen hDlen hrSorted hrIff
    hMap hMatch hok
  have hPle := hF.2.2.2.2.2.1
  have hPhi : bundleLogFactor M N * specPhi SP S6 ≤ tr.machCost :=
    asmFi_specPhi_mul_lg_le_machCost hMap hMatch hok hPle
  have hokPair : ∀ q ∈ activePairs tr, SpanGraphOK SP (tr.initBunG q) := by
    intro q hq
    have hmem : slotOf q ∈ List.range D.length := hMap.2.1 q hq
    have hGeq := asmFirstInitSlotGraph_slotOf hMatch (fun _ => rfl) hq
    exact hGeq ▸ hok _ hmem
  have hWalk : walkPot tr ≤ tr.machCost := asmFi_walkPot_le_machCost hokPair hPle
  have hBigPhi : 320 * (capExp + 1) * bundleLogFactor M N * specPhi SP S6 ≤
      320 * (capExp + 1) * tr.machCost := by
    rw [mul_assoc (320 * (capExp + 1))]
    exact Nat.mul_le_mul_left (320 * (capExp + 1)) hPhi
  have hBigWalk : 300 * walkPot tr ≤ 300 * tr.machCost := Nat.mul_le_mul_left 300 hWalk
  have e : asmFiBuildCostMul capExp limbMul * tr.machCost =
      asmFiBodyCostMul capExp limbMul * tr.machCost + 320 * (capExp + 1) * tr.machCost +
        300 * tr.machCost := by
    unfold asmFiBuildCostMul; ring
  exact (Nat.add_le_add (Nat.add_le_add hBody hBigPhi) hBigWalk).trans (le_of_eq e.symm)

end MinCostFlow.SparseCore.Program
