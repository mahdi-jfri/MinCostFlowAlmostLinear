module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSide
public import MinCostFlow.SparseCore.Program.BundleInitPost
public import MinCostFlow.SparseCore.Program.RestartLoopDefs
public import MinCostFlow.SparseCore.Program.RestartModelInv
public import MinCostFlow.SparseCore.BundleConstantsLemmas
public import MinCostFlow.SparseCore.BundleSpanCharge
public import MinCostFlow.SparseCore.LSFInit
public import MinCostFlow.DynSpanner.Program.DynSpannerInitCost

/-!
# Two invariants of the bundle side at the init (`AssemblyFirstInitSideInv`)

The first step of a branch needs two facts of the bundle side. Both are clauses of `AsmBrSideModel` (`AssemblyBranchSideInv.lean`).
* **The slots** (`AsmFirstSideSlotInv`). The slot table has room for every pair of a component of
  `G₀` and one of its buckets, the slots in use are `0, 1, …, |slots| - 1`, and the other slots
  are empty in the bundle table and in the spanner table. So a step can put a new pair at the
  next free slot.
* **The inactive components** (`AsmFirstInactiveCompInv`). Each component of `G₀` that is not
  active has one root, its buckets are the buckets of its core edges, its core edges are edges of
  `G₀`, and the bundle of each of its pairs is `initBundleFor` on the edges of the pair, with a
  start graph that meets `SpanGraphOK`. So a step can start such a component without new checks.

Here we prove both at the init (`asmFirstInit_slotInv`, `initTree_inactiveInv`). The reasons:
* There are at most `m` pairs, since the buckets of a component are the buckets of its core edges,
  and distinct components have no common core edge, as their vertex sets are disjoint
  (`initTree_sum_buckets_le`). So caps of at least `m` leave room for all pairs.
* At the init, each inactive component `C` is small: `4 m_C < k`. A valid LSF init then gives one
  root (`initLSF_small_props_with`). The other facts of an inactive component hold by the
  definition of the init.
* `SpanGraphOK` holds for the start graph of every pair (`initTree_spanGraphOK`): the bundles of
  `initBundleFor` are named `0, 1, …` and there are at most `2 |E|` of them, so their names are
  below `2 eCap`; the edges are edges of `G₀`; and the word size clause follows from a bound on
  `w` of the kind that P6's operation 0 asks for its space.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

public section

/-! ## The number of pairs -/

/-- A component that holds a vertex `v` is the component of `v`. -/
theorem components_eq_compOf {G : MGraph} {C : Finset ℕ} {v : ℕ} (hC : C ∈ components G)
    (hv : v ∈ C) : C = compOf G v := by
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hC
  exact compOf_eq_of_connected (mem_compOf_iff.mp hv).2

/-- Sorting the edges of `E` by the component of an end `t e` counts each edge at most once. -/
theorem sum_card_filter_components_le (G : MGraph) (E : Finset ℕ) (t : ℕ → ℕ) :
    ((components G).sum fun C => (E.filter fun e => t e ∈ C).card) ≤ E.card := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun C _ => Finset.filter_subset _ _)
  · intro C₁ h₁ C₂ h₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_filter] at he1 he2
    exact hne ((components_eq_compOf h₁ he1.2).trans (components_eq_compOf h₂ he2.2).symm)

/-- **At the init there are at most `m` pairs**: the buckets of the components of `G₀`, counted
over all components, are at most the edges of `G₀`. -/
theorem initTree_sum_buckets_le (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    let tr := initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j
    (components tr.cs.G₀).sum (fun C => (tr.activeBuckets C).card) ≤ G₀.m := by
  intro tr
  calc (components tr.cs.G₀).sum (fun C => (tr.activeBuckets C).card)
      ≤ (components G₀).sum (fun C => ((coreGraph G₀ tr.cs.lsf).E.filter fun e =>
          (coreGraph G₀ tr.cs.lsf).tail e ∈ C).card) :=
        Finset.sum_le_sum fun C _ => Finset.card_image_le
    _ ≤ (coreGraph G₀ tr.cs.lsf).E.card := sum_card_filter_components_le _ _ _
    _ ≤ G₀.m := Finset.card_le_card Finset.sdiff_subset

/-- The slots of the spanner table after the spanner inits stay empty off the list. -/
theorem spanAfter_none_of_not_mem {cap : ℕ} (g : ℕ → MGraph) {l : List ℕ} {j : Fin cap}
    (hj : j.1 ∉ l) : spanAfter (fun _ => none) g l j = none := by
  simp [spanAfter, hj]

/-- The slots of the bundle table after P5's `initSlots` on the empty table stay empty off the
slots of the specs. -/
theorem tableAfterInitSlots_none_of_not_mem {slotCap : ℕ} (specs assigns : List (ℕ × ℕ))
    (cord : ℕ → List End) (rList : List ℕ) (k : ℕ) {j : Fin slotCap}
    (hj : j.1 ∉ specs.map Prod.fst) :
    tableAfterInitSlots (fun _ => none) specs assigns cord rList k j = none := by
  simp [tableAfterInitSlots, hj]

/-- **The slots of the bundle side at the init.** If the caps are at least the number of edges
of `G₀`, the slots in use are `0, …, |slots| - 1`, and the other slots are empty in the two
tables, then the slot invariant holds. -/
theorem asmFirstInit_slotInv
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (y : AsmBrSide B5 depth) (hcap : G₀.m ≤ min (min y.slotCap y.cap) y.slotsCap)
    (hslots : y.slots = List.range y.slots.length)
    (hbun : ∀ i : Fin y.slotCap, i.1 ∉ y.slots → y.bunS i = none)
    (hspan : ∀ i : Fin y.cap, i.1 ∉ y.slots → y.spanS i = none) :
    AsmFirstSideSlotInv
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord j) y :=
  ⟨(initTree_sum_buckets_le lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord j).trans
    hcap, hslots, hbun, hspan⟩

/-! ## `SpanGraphOK` of the start graphs -/

/-- The bundles of `initBundleFor` are named `0, 1, …, n - 1`. -/
theorem initBundleFor_vertices_range (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ)
    (k : ℕ) :
    (initBundleFor cs ord E k).vertices =
      Finset.range (initBundleFor cs ord E k).vertices.card := by
  classical
  unfold initBundleFor
  split_ifs with h
  · simp [initBundleState]
  · simp

/-- The graph of the bundles of `initBundleFor` is valid, when its edges are core edges. -/
theorem initBundleFor_graph_isValid {cs : CompLSFState} {ord : ℕ → List End} {E : Finset ℕ}
    (hE : E ⊆ (coreGraph cs.G cs.lsf).E) {k : ℕ} (hk : 0 < k) :
    (initBundleFor cs ord E k).graph.IsValid := by
  classical
  unfold initBundleFor
  split_ifs with h
  · let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    have hC : (coreGraph cs.G cs.lsf).IsValid :=
      coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)
    exact BundleState.graph_isValid (initBundleState_inv
      (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) hC hE hk)
  · intro e he
    simp [BundleState.graph] at he

/-- If `(2 X) ^ c < 2 ^ w` for some `X ≥ 1`, then `c (⌊log₂ X⌋ + 1) ≤ w`. -/
theorem mul_log_succ_le_of_pow_lt {c X w : ℕ} (hX : X ≠ 0) (h : (2 * X) ^ c < 2 ^ w) :
    c * (Nat.log 2 X + 1) ≤ w := by
  have h1 : 2 ^ (Nat.log 2 X + 1) ≤ 2 * X := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hX)
  have h2 : 2 ^ (c * (Nat.log 2 X + 1)) < 2 ^ w := by
    rw [mul_comm, pow_mul]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left h1 c) h
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h2).le

/-- **`SpanGraphOK` of the start graphs at the init.** Every pair `q` has a start graph that meets
`SpanGraphOK P`, when the spanner parameters `P` leave room for the names: the vertex cap is at
least `2 eCap + splitBound + 1`, the edge cap is at least `eCap`, the edge cap of the sparsifier is
at least `m`, and the word size is large enough for the caps and for the sparsifier. The edges of
`G₀` must be below `eCap`. -/
theorem initTree_spanGraphOK (P : DSParams) (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) {eCap : ℕ}
    (hk : 1 ≤ k) (hEl : ∀ e ∈ G₀.E, e < eCap) (hm : G₀.m ≤ P.mMax)
    (hV : 2 * eCap + P.splitBound + 1 ≤ P.vCap) (hE : eCap ≤ P.eCap)
    (hL : 1 ≤ P.L) (hp : 1 ≤ max P.impl.p_s P.impl.p_t) (hw16 : 16 ≤ 2 ^ P.w)
    (hw : P.vCap + P.eCap + 2 < 2 ^ P.w)
    (hcw : (36 * (P.vCap + 2 * P.eCap + 1)) ^ P.impl.cw < 2 ^ P.w) (q : Finset ℕ × ℤ) :
    SpanGraphOK P
      ((initBundleTreeWithParams lsfInit P.L sparsify params spanConst k M N G₀ ℓ₀ ord j).initBunG
        q) := by
  classical
  set tr := initBundleTreeWithParams lsfInit P.L sparsify params spanConst k M N G₀ ℓ₀ ord j
  set Eq := bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket q.1 q.2 with hEq
  have hEcore : Eq ⊆ (coreGraph tr.cs.G tr.cs.lsf).E := bucketCoreEdges_sub_coreE _ _ _ _
  have hEG : Eq ⊆ G₀.E := fun e he => (Finset.mem_sdiff.mp (hEcore he)).1
  set B := initBundleFor tr.cs ord Eq tr.k with hB
  have hgr : tr.initBunG q = MinCostFlow.SparseCore.normGraph B.graph := rfl
  have hkpos : 0 < tr.k := hk
  have hval : B.graph.IsValid := initBundleFor_graph_isValid hEcore hkpos
  have hBE : B.edges ⊆ Eq := initBundleFor_edges_subset _ _ _ _
  -- the edges of the pair are at most `eCap`
  have hEcard : Eq.card ≤ eCap := by
    calc Eq.card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hEl e (hEG he))
      _ = eCap := Finset.card_range _
  have hn : B.vertices.card ≤ 2 * Eq.card := initBundleFor_vertices_le_two_card hEcore hkpos
  have hvlt : ∀ v ∈ B.vertices, v < 2 * eCap := by
    intro v hv
    have hr : B.vertices = Finset.range B.vertices.card :=
      initBundleFor_vertices_range tr.cs ord Eq tr.k
    rw [hr] at hv
    have := Finset.mem_range.mp hv
    omega
  have hmB : B.edges.card ≤ Eq.card := Finset.card_le_card hBE
  have hmG : Eq.card ≤ G₀.m := Finset.card_le_card hEG
  have hGn : (MinCostFlow.SparseCore.normGraph B.graph).n = B.vertices.card := rfl
  have hGm : (MinCostFlow.SparseCore.normGraph B.graph).m = B.edges.card := rfl
  rw [hgr]
  refine ⟨hL, hp, hw16, by omega, by omega, fun _ => ?_,
    MinCostFlow.SparseCore.normGraph_isValid hval, by omega,
    fun v hv => lt_of_lt_of_le (hvlt v hv) (by omega),
    fun e he => lt_of_lt_of_le (hEl e (hEG (hBE he))) hE⟩
  -- the word size clause
  refine le_trans (wordSize_canonSparsifyInput_id_le _ _
    (MinCostFlow.SparseCore.normGraph_isValid hval)) (mul_log_succ_le_of_pow_lt (by omega) ?_)
  have hact := activeSubgraph_n_le (MinCostFlow.SparseCore.normGraph B.graph)
  refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ _) hcw
  omega

/-! ## The inactive components -/

/-- **The inactive components at the init.** For a valid LSF init, positive lengths and `k ≥ 1`,
every component of `G₀` that is not active meets the invariant of the inactive components, given
`SpanGraphOK` of the start graphs of its pairs (`initTree_spanGraphOK`). -/
theorem initTree_inactiveInv
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w : ℕ) {lsfInit : LSFInit} {C_lsst : ℝ} (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (y : AsmBrSide B5 depth) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hG : G₀.IsValid)
    (hℓ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hk : 1 ≤ k)
    (hok : ∀ q, SpanGraphOK (asmBrSP impl w depth y)
      ((initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord
        j).initBunG q)) :
    AsmFirstInactiveCompInv impl w depth
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord j) ord y := by
  classical
  intro C hC hnA
  -- an inactive component is small, so a valid init gives it one root
  have hlt : 4 * (compGraph G₀ C).m < k := by
    by_contra hge
    push Not at hge
    have hm1 : 1 ≤ (compGraph G₀ C).m := by
      by_contra h0
      push Not at h0
      omega
    exact hnA (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
    rw [safeLen_eq_of_mem ℓ₀ he]
    exact hℓ e he
  have hGC_val := compGraph_isValid hG hC
  have hGC_ne := compGraph_nonempty hC
  have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < safeLen G₀ ℓ₀ e := fun e he =>
    hℓs e (Finset.filter_subset _ _ he)
  have hG_eq : ((initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord
      j).cs.compSt C).G = compGraph G₀ C :=
    (hInit (compGraph G₀ C) (safeLen G₀ ℓ₀) hGC_val hGC_ne hℓC hk).2.2.1
  refine ⟨(initLSF_small_props_with hInit hG hℓs hk hC hlt).1, rfl,
    fun e he _ => (Finset.mem_sdiff.mp he).1, by rw [hG_eq]; exact hlt,
    fun b _ => ⟨bunAgree_refl _, rfl, hok _⟩⟩

end

end MinCostFlow.SparseCore.Program
