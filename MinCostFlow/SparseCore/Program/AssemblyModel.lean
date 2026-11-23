module

public import MinCostFlow.SparseCore.Program.ContractInput
public import MinCostFlow.SparseCore.Program.RestartIface
public import MinCostFlow.SparseCore.Program.AssemblySpanCost
public import MinCostFlow.Chain.BundleRestartMach

/-!
# The model side of the sparse-core program

The program of the sparse-core tool keeps one branch record per branch and calls the pieces on
each record. This file proves the facts about the model that the assembly of the program uses,
for `T = sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst`.

* `asm_input_inv`: every state that can accompany the contract's history (`SparseCoreOrdInput`)
  has `k` branches, stores the input order when it is nonempty, and every branch keeps the size
  bounds `M` and `N`, the split budget `bundleSplitBudget k M`, the spanner parameters `params M`,
  and the spanner constant `spanConst`.
* `asm_updateOrd_of_nonempty`, `asm_updateOrd_of_empty`: an update is the step `stepBundleTree`
  of every branch, and nothing on an empty state.
* `asm_update_cost_eq`: the rise of `T.cost` in an update is the sum over the branches `j < k` of
  the step charge `branchStepCharge` (`asm_branchStepCharge_eq` gives its terms).
* `asm_init_cost_eq`: the cost of the initialization is the sum of the initial machine costs of
  the branches.
* `ordWordsOn_activeSubgraph_eq` and `asm_init_pays_k_order_reads`: under `IsRotationOrder G ord`,
  the active-vertex copy of `ord` has `2 * G.m + 2 * (activeSubgraph G).n + 1` words and every
  isolated vertex has `ord v = []`, so `T.cost (T.initOrd k M N G ℓ g ord)` pays
  `k * ((G.m + (activeSubgraph G).n + 1 + ordWordsOn (activeSubgraph G).V ord) * bundleLogFactor M N)`
  with constant `1`.
* `spanActivateCost_le_spanInitBound`, `spanActivateCost_le_spanInitBound_of_unit`, and
  `bucketUpdateCost_le_of_spanBatchChargeWith`: one-line links between P6's spanner costs
  (`spanActivateCost`, `dsBatchCharge`, `bucketUpdateCost`) and the model's `spanInitBound` /
  `spanBatchChargeWith`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program MinCostFlow.LSF MinCostFlow.SparseCore.Program.Restart

/-- The rise of the machine cost of one branch in a step: the input length, the encodings of the
bundle batches and of the output batch, the dynamic-spanner amortized batch charges
`spanBatchChargeWith`, the LSF batches and the lazy initializations `lazyMachInitCost`, all times
the log factor of the branch (`stepBundleTree_machCost`). -/
noncomputable def branchStepCharge {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : ℕ :=
  let info := stepBundleTree sparsify tr U ord ord'
  let active' := info.state.activeComps
  (U.length +
    (active'.sum fun C => (tr.activeBuckets C).sum fun b =>
      (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))) +
    tr.S_cur.batchEnc info.U_S +
    (active'.sum fun C => (tr.activeBuckets C).sum fun b =>
      spanBatchChargeWith tr.spanConst tr.spanParams L
        ((tr.initBunG (C, b)).n + tr.splitBound) (tr.initBunG (C, b))
        (tr.dyn (C, b)).G (info.U_B (C, b))) +
    lsfBatchSize tr.cs U +
    info.newlyActive.sum fun C => tr.lazyMachInitCost C) * bundleLogFactor tr.m₀ tr.n₀

/-- A step adds `branchStepCharge` to the machine cost of a branch. -/
theorem asm_branchStepCharge_eq {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree sparsify tr U ord ord').state.machCost =
      tr.machCost + branchStepCharge sparsify tr U ord ord' :=
  stepBundleTree_machCost sparsify tr U ord ord'

/-! ## One-line P6 cost links (`spanActivateCost`, `dsBatchCharge`, `bucketUpdateCost`) -/

/-- P6's spanner activation cost `spanActivateCost P G` is at most
`dsAmortConst P.impl * spanInitBound (canonicalSparsifyParams P.impl P.mMax).absorbTime P.L P.splitBound G`
with constant `1`. -/
theorem spanActivateCost_le_spanInitBound (P : DSParams) (G : MGraph)
    (hG : G.IsValid) (hGm : G.m ≤ P.mMax) :
    spanActivateCost P G ≤
      dsAmortConst P.impl *
        spanInitBound (canonicalSparsifyParams P.impl P.mMax).absorbTime P.L P.splitBound G :=
  dsInitActivateCost_le_spanInitBound P G hG hGm

/-- Unit-time-factor specialization (`P.impl.γ_t P.mMax = 1`) of
`spanActivateCost_le_spanInitBound`, directly at `canonicalSparsifyParams P.impl P.mMax`. -/
theorem spanActivateCost_le_spanInitBound_of_unit (P : DSParams) (G : MGraph)
    (hG : G.IsValid) (hGm : G.m ≤ P.mMax) (hγt : P.impl.γ_t P.mMax = 1) :
    spanActivateCost P G ≤
      dsAmortConst P.impl *
        spanInitBound (canonicalSparsifyParams P.impl P.mMax) P.L P.splitBound G := by
  rw [← canonicalSparsifyParams_absorbTime_eq_of_unit P.impl P.mMax hγt]
  exact spanActivateCost_le_spanInitBound P G hG hGm

/-- One-line link from the model's `spanBatchChargeWith` to P6's `bucketUpdateCost` when
`P.impl.γ_t P.mMax = 1`. -/
theorem bucketUpdateCost_le_of_spanBatchChargeWith (P : DSParams) (cap : ℕ)
    (S : BucketSpannerState cap) (tbl slot batchPtr W h : ℕ) (hslot : slot < cap) (s : DSHist)
    (hs : S ⟨slot, hslot⟩ = some s) (mem : ℕ → ℕ) (X c_W : ℕ)
    (hγt : P.impl.γ_t P.mMax = 1)
    (hX : spanBatchChargeWith (dsAmortConst P.impl) (canonicalSparsifyParams P.impl P.mMax) P.L
      (s.G₀.n + P.splitBound) s.G₀ (s.G₀.applyBatch s.flat)
      (decodeBatch mem batchPtr (s.state P).G).1 ≤ X)
    (hW : W ≤ c_W * X) (h1 : 1 ≤ X) :
    bucketUpdateCost P cap S [tbl, slot, batchPtr, W, h] mem ≤ (1440 * c_W + 526) * X :=
  bucketUpdateCost_le_of_words P cap S tbl slot batchPtr W h hslot s hs mem X c_W
    (by rwa [dsBatchCharge_eq_spanBatchChargeWith_of_unit _ _ _ _ _ _ _ hγt]) hW h1

/-! ## Active-vertex rotation order size (`ordWordsOn`) -/

/-- In any rotation order `IsRotationOrder G ord`, every vertex outside `(activeSubgraph G).V`
has an empty end list, and the active-vertex representation `ordWordsOn (activeSubgraph G).V ord`
has exactly `2 * G.m + 2 * (activeSubgraph G).n + 1` words. -/
theorem ordWordsOn_activeSubgraph_eq {G : MGraph} {ord : ℕ → List End}
    (hG : G.IsValid) (hrot : IsRotationOrder G ord) :
    (∀ v, v ∉ (activeSubgraph G).V → ord v = []) ∧
      ordWordsOn (activeSubgraph G).V ord = 2 * G.m + 2 * (activeSubgraph G).n + 1 := by
  classical
  rcases hrot with ⟨ρ, rfl⟩
  have hactV := activeSubgraph_isValid hG
  have hmem_act : ∀ x : End, x.1 ∈ G.E → G.src x ∈ (activeSubgraph G).V := by
    intro x hx
    obtain ⟨ht, hh⟩ := hactV x.1 hx
    obtain ⟨ht_eq, hh_eq⟩ := (activeSubgraph_isSubgraph G).2.2 x.1 hx
    cases hb : x.2
    · simpa [MGraph.src, hb, hh_eq] using hh
    · simpa [MGraph.src, hb, ht_eq] using ht
  refine ⟨fun v hv => ?_, ?_⟩
  · cases hlist : ρ.order v with
    | nil => rfl
    | cons x xs =>
      have hx : x ∈ ρ.order v := by rw [hlist]; exact List.mem_cons_self
      have hsrc := (ρ.mem_order v x).mp hx
      exact absurd (hsrc.2 ▸ hmem_act x hsrc.1) hv
  · unfold ordWordsOn
    have hcard_eq : ∀ v, (ρ.order v).length =
        ((G.E ×ˢ ({false, true} : Finset Bool)).filter fun x => G.src x = v).card := by
      intro v
      rw [← List.toFinset_card_of_nodup (ρ.nodup v)]
      congr 1
      ext x
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, ρ.mem_order]
      cases x.2 <;> simp
    have hsum_len : (activeSubgraph G).V.sum (fun v => (ρ.order v).length) = 2 * G.m := by
      trans (activeSubgraph G).V.sum
        (fun v => ((G.E ×ˢ ({false, true} : Finset Bool)).filter fun x => G.src x = v).card)
      · exact Finset.sum_congr rfl fun v _ => hcard_eq v
      · rw [← Finset.card_eq_sum_card_fiberwise
          (f := fun x : End => G.src x)
          (s := G.E ×ˢ ({false, true} : Finset Bool))
          (t := (activeSubgraph G).V)
          (fun x hx => hmem_act x (Finset.mem_product.mp hx).1)]
        rw [Finset.card_product]
        have h2 : ({false, true} : Finset Bool).card = 2 := by decide
        rw [h2, Nat.mul_comm]
        rfl
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hsum_len]
    change 1 + ((activeSubgraph G).n * 2 + 2 * G.m) = 2 * G.m + 2 * (activeSubgraph G).n + 1
    omega

section Tool

variable (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
  (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
  (params : ℕ → SparsifyParams) (spanConst : ℕ)

/-- On a nonempty state, an update of the tool is the step `stepBundleTree` of every branch, with
the stored order as the old order. -/
theorem asm_updateOrd_of_nonempty (st : SparseCoreBundleState L) (hne : st.isNonempty = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).updateOrd
        st U ℓ g ord' =
      ({ st with ord := ord', trees := fun j =>
          (stepBundleTree sparsify (st.trees j) U st.ord ord').state },
        fun j => (stepBundleTree sparsify (st.trees j) U st.ord ord').U_S) :=
  updateBundleCore_of_nonempty hne U ord'

/-- On an empty state, an update of the tool changes nothing and outputs empty batches. -/
theorem asm_updateOrd_of_empty (st : SparseCoreBundleState L) (hne : st.isNonempty = false)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).updateOrd
        st U ℓ g ord' =
      (st, fun _ => []) := by
  change updateBundleCore sparsify st U ord' = _
  simp [updateBundleCore, hne]

/-- On a nonempty state, the rise of the tool's cost in an update is the sum over the branches
`j < st.k` of their step charges. -/
theorem asm_update_cost_eq (st : SparseCoreBundleState L) (hne : st.isNonempty = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    T.cost (T.updateOrd st U ℓ g ord').1 =
      T.cost st + (Finset.range st.k).sum fun j =>
        branchStepCharge sparsify (st.trees j) U st.ord ord' := by
  intro T
  dsimp only [T]
  rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst st hne,
    sparseCoreBundleRestartToolMachWith_cost_eq, sparseCoreBundleRestartToolMachWith_cost_eq]
  simp only [hne, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => asm_branchStepCharge_eq sparsify _ U _ _

/-- The cost of the initialization is the sum of the initial machine costs of the branches when
the graph has a vertex, and `0` otherwise. -/
theorem asm_init_cost_eq (k M N : ℕ) (G : MGraph) (ℓ g : ℕ → ℝ) (ord : ℕ → List End) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    open Classical in
    T.cost (T.initOrd k M N G ℓ g ord) =
      if G.V.Nonempty then (Finset.range k).sum fun j =>
        (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord j).machCost
      else 0 := by
  intro T
  change (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).cost
    (initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G ℓ ord) = _
  rw [sparseCoreBundleRestartToolMachWith_cost_eq]
  by_cases h : G.V.Nonempty <;> simp [h, initBundleCoreWithParams]

/-- Under `G.V.Nonempty` and `IsRotationOrder G ord`, the initialization model cost pays for `k`
reads of the active-vertex rotation order `ordWordsOn (activeSubgraph G).V ord` plus the per-branch
setup `G.m + (activeSubgraph G).n + 1`, all times `bundleLogFactor M N`, with constant `1`. -/
theorem asm_init_pays_k_order_reads (k M N : ℕ) (G : MGraph) (ℓ g : ℕ → ℝ) (ord : ℕ → List End)
    (hG : G.IsValid) (hV : G.V.Nonempty) (hrot : IsRotationOrder G ord) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    k * ((G.m + (activeSubgraph G).n + 1 + ordWordsOn (activeSubgraph G).V ord) *
        bundleLogFactor M N) ≤
      T.cost (T.initOrd k M N G ℓ g ord) := by
  intro T
  rw [asm_init_cost_eq lsfInit C_lsst L sparsify params spanConst k M N G ℓ g ord]
  simp only [hV, ↓reduceIte]
  have hord := (ordWordsOn_activeSubgraph_eq hG hrot).2
  have hle : ∀ j ∈ Finset.range k,
      (G.m + (activeSubgraph G).n + 1 + ordWordsOn (activeSubgraph G).V ord) *
        bundleLogFactor M N ≤
      (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord j).machCost := by
    intro j _
    rw [initBundleTreeWithParams_machCost, hord]
    exact Nat.mul_le_mul_right _ (by omega)
  calc k * ((G.m + (activeSubgraph G).n + 1 + ordWordsOn (activeSubgraph G).V ord) *
          bundleLogFactor M N)
      = (Finset.range k).sum (fun _ =>
          (G.m + (activeSubgraph G).n + 1 + ordWordsOn (activeSubgraph G).V ord) *
            bundleLogFactor M N) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ (Finset.range k).sum (fun j =>
          (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord j).machCost) :=
        Finset.sum_le_sum hle

/-- The invariant of the states of the contract's history: `k` branches, the stored order is the
input order when the state is nonempty, and every branch keeps the size bounds `M` and `N`,
`splitBound = bundleSplitBudget k M`, `spanParams = params M`, and `spanConst = spanConst`. -/
theorem asm_input_inv {k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (h : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n) :
    SparseCoreBundleState.k (L := L) s = k ∧
      (SparseCoreBundleState.isNonempty (L := L) s = true →
        SparseCoreBundleState.ord (L := L) s = ord) ∧
      ∀ j, (SparseCoreBundleState.trees (L := L) s j).m₀ = M ∧
        (SparseCoreBundleState.trees (L := L) s j).n₀ = N ∧
        (SparseCoreBundleState.trees (L := L) s j).splitBound = bundleSplitBudget k M ∧
        (SparseCoreBundleState.trees (L := L) s j).spanParams = params M ∧
        (SparseCoreBundleState.trees (L := L) s j).spanConst = spanConst := by
  induction h with
  | init G ℓ g ord _ _ _ _ _ =>
    exact ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  | @update s₀ _ _ _ _ U ℓ g ord' _ _ _ _ ih =>
    obtain ⟨hk, hord, hmn⟩ := ih
    by_cases hne : s₀.isNonempty = true
    · rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst s₀ hne]
      exact ⟨hk, fun _ => rfl, fun j => hmn j⟩
    · have hf : s₀.isNonempty = false := by simpa using hne
      rw [asm_updateOrd_of_empty lsfInit C_lsst L sparsify params spanConst s₀ hf]
      exact ⟨hk, fun h' => absurd h' hne, hmn⟩
  | @restart s₀ _ ord₀ _ _ j _ ih =>
    obtain ⟨hk, hord, hmn⟩ := ih
    have hR : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).restart s₀ j =
        if s₀.isNonempty = true then
          { isNonempty := s₀.isNonempty, k := s₀.k, ord := s₀.ord,
            trees := Function.update s₀.trees j
              (restartBundleTree L sparsify (s₀.trees j) s₀.ord) }
        else s₀ :=
      sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst L sparsify s₀ j
    have key : ∀ x : SparseCoreBundleState L, x =
        (if s₀.isNonempty = true then
          { isNonempty := s₀.isNonempty, k := s₀.k, ord := s₀.ord,
            trees := Function.update s₀.trees j
              (restartBundleTree L sparsify (s₀.trees j) s₀.ord) }
        else s₀) →
        x.k = k ∧ (x.isNonempty = true → x.ord = ord₀) ∧
          ∀ i, (x.trees i).m₀ = M ∧ (x.trees i).n₀ = N ∧
            (x.trees i).splitBound = bundleSplitBudget k M ∧
            (x.trees i).spanParams = params M ∧ (x.trees i).spanConst = spanConst := by
      intro x hx
      subst hx
      by_cases hne : s₀.isNonempty = true
      · simp only [hne, ↓reduceIte]
        refine ⟨hk, fun _ => hord hne, fun i => ?_⟩
        by_cases hij : i = j
        · subst hij
          simp only [Function.update_self]
          exact hmn i
        · simp only [Function.update_of_ne hij]
          exact hmn i
      · simp only [hne]
        exact ⟨hk, fun h' => absurd h' hne, hmn⟩
    exact key _ hR

/-- On a state of the contract's history, the step charge of every branch has the log factor
`bundleLogFactor M N` and uses `spanConst`, `params M`, and `bundleSplitBudget k M`. -/
theorem asm_branchStepCharge_of_input {k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (h : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n) (j : ℕ) (U : List Update) (ord₁ ord' : ℕ → List End) :
    let tr := SparseCoreBundleState.trees (L := L) s j
    let info := stepBundleTree sparsify tr U ord₁ ord'
    branchStepCharge sparsify tr U ord₁ ord' =
      (U.length +
        (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
          (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))) +
        tr.S_cur.batchEnc info.U_S +
        (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst (params M) L
            ((tr.initBunG (C, b)).n + bundleSplitBudget k M) (tr.initBunG (C, b))
            (tr.dyn (C, b)).G (info.U_B (C, b))) +
        lsfBatchSize tr.cs U +
        info.newlyActive.sum fun C => tr.lazyMachInitCost C) * bundleLogFactor M N := by
  intro tr info
  obtain ⟨-, -, hmn⟩ := asm_input_inv lsfInit C_lsst L sparsify params spanConst h
  unfold branchStepCharge
  rw [(hmn j).1, (hmn j).2.1, (hmn j).2.2.1, (hmn j).2.2.2.1, (hmn j).2.2.2.2]

/-- On every nonempty state of the contract's history, every branch `j` carries branch count
`cs.k = k`. -/
theorem asm_input_cs_k {k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (h : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n) :
    SparseCoreBundleState.isNonempty (L := L) s = true →
      ∀ j, (SparseCoreBundleState.trees (L := L) s j).cs.k = k := by
  induction h with
  | init G ℓ g ord _ _ _ _ _ =>
    intro hne j
    have hV : G.V.Nonempty := by
      by_contra hneV
      simp [sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
        initBundleCoreWithParams, hneV] at hne
    change ((initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G ℓ ord).trees j).cs.k = k
    simp [initBundleCoreWithParams, hV, initBundleTreeWithParams, initCompLSFWith]
  | @update s₀ _ _ _ _ U ℓ g ord' _ _ _ _ ih =>
    intro hne j
    by_cases hne0 : s₀.isNonempty = true
    · rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst s₀ hne0]
      change (compLSFBatch (s₀.trees j).cs U).k = k
      rw [compLSFBatch_k]
      exact ih hne0 j
    · have hf : s₀.isNonempty = false := by simpa using hne0
      rw [asm_updateOrd_of_empty lsfInit C_lsst L sparsify params spanConst s₀ hf] at hne
      exact absurd hne hne0
  | @restart s₀ _ ord₀ _ _ j₀ _ ih =>
    intro hne j
    have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst L sparsify s₀ j₀
    change (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).restart s₀ j₀ = _ at hR
    by_cases hne0 : s₀.isNonempty = true
    · rw [hR]; simp only [hne0, ↓reduceIte]
      by_cases hj : j = j₀
      · subst hj; simp only [Function.update_self]; exact ih hne0 j
      · simp only [Function.update_of_ne hj]; exact ih hne0 j
    · rw [hR] at hne; simp only [hne0] at hne; exact absurd hne hne0

/-- Format preconditions required by P3's canonical LSF initializer (`CanonicalLSFValid`) on
`(L, P_fp, k, m)`: positive limbs, `4 ∣ P_fp`, precision margin `P_fp + 6 ≤ 4 * L`, an exponent `q`
with `q + 11 ≤ P_fp` and `40 * k ≤ 2 ^ q`, and edge-count headroom
`32 * (m + 1) * 2 ^ P_fp < 2 ^ (4 * L - 1)`. -/
def CompInitFormatHyp (L P_fp k m : ℕ) : Prop :=
  1 ≤ L ∧ 4 ∣ P_fp ∧ P_fp + 6 ≤ 4 * L ∧ (∃ q, q + 11 ≤ P_fp ∧ 40 * k ≤ 2 ^ q) ∧
    32 * (m + 1) * 2 ^ P_fp < 2 ^ (4 * L - 1)

end Tool

end MinCostFlow.SparseCore.Program
