module

public import MinCostFlow.SparseCore.BundleStepDefs
public import MinCostFlow.SparseCore.BundleRunsCore
public import MinCostFlow.SparseCore.CompLSFBridge

/-!
# The canonical bundle step meets the specification

`bundleRunsStep_spec` proves that `bundleRunsStep` meets `BundleStepSpec` and
`BundleStepLocalSpec` on ordered input. The proof takes the pair that exists by
`bundleStepSpec_exists` and applies `bundleRunsStep_core` to it. The partition, the batch and the
deletion count come from that lemma directly. The canonical step has at most as many bundles as
the pair, and both grow by one bundle per split, so it makes at most as many splits. This gives
the global and the local split bounds. If a component has no new roots and loses no bundle edge,
the canonical step makes no splits and no deletions, so it leaves the bundles unchanged.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

private theorem cast_order {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h
  rfl

private theorem bundleState_ext {B₁ B₂ : BundleState} (h1 : B₁.vertices = B₂.vertices)
    (h2 : B₁.edges = B₂.edges) (h3 : B₁.parent = B₂.parent) (h4 : B₁.bundleOf = B₂.bundleOf) :
    B₁ = B₂ := by
  cases B₁
  cases B₂
  cases h1
  cases h2
  cases h3
  cases h4
  rfl

/-- On ordered input the canonical bundle step meets the specification of the bundle step and
its local part. -/
theorem bundleRunsStep_spec {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    BundleStepSpec cs B k ord' U (bundleRunsStep cs B k ord' U).1
        (bundleRunsStep cs B k ord' U).2 ∧
      BundleStepLocalSpec cs B U (bundleRunsStep cs B k ord' U).1
        (bundleRunsStep cs B k ord' U).2 := by
  obtain ⟨⟨UBw, Bw⟩, hS, hL⟩ := bundleStepSpec_exists h
  obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, -, hσ, -, hU, hB⟩ := h
  have hI' := compLSFBatch_inv hI hU
  let σ' : Rotation (compLSFBatch cs U).G := (compLSFBatch_G cs U).symm ▸ σ
  have hσ' : σ'.order = ord' := (cast_order _ σ).trans hσ
  obtain ⟨hwP, hwv, hwg, hwt, hws, -, hwgrowth⟩ := hS
  obtain ⟨hwL1, -, -, hwE, hwL4⟩ := hL
  dsimp only at hwP hwv hwg hwt hws hwgrowth hwL1 hwE hwL4
  have hpar0 : ∀ b ∈ B.vertices, B.parent b ∈ (compLSFBatch cs U).RF.R :=
    fun b hb => (compLSFBatch_decremental hI hU).2 (hB.2.1 b hb)
  have core := fun (σ'' : Rotation (compLSFBatch cs U).G) hG hF (hσ'' : σ''.order = ord') =>
    bundleRunsStep_core (k := k) (fun x hx => (hB.2.2.1 x hx).1) (fun b hb => (hB.2.2.2 b hb).1) hpar0 σ'' hG hF hσ''
      (hwP σ'' hG hF hσ'') hwv hwg hwt hwE
  obtain ⟨-, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    core σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
  -- The canonical step makes at most as many splits as the pair from the existence proof.
  have hle : batchSplitCount (bundleRunsStep cs B k ord' U).1 ≤ batchSplitCount UBw := by
    have h2 := c2
    rw [c10, hwgrowth] at h2
    omega
  refine ⟨⟨fun σ'' hG hF hσ'' => (core σ'' hG hF hσ'').1, c5, c6, c7, hle.trans hws, c9, c10⟩,
    ⟨?_, c8, c11 ▸ Finset.sdiff_subset, c11, ?_⟩⟩
  · intro C hC hpar
    obtain ⟨hcnt, hparw⟩ := hwL1 C hC hpar
    refine ⟨hle.trans hcnt, fun c hc => ?_⟩
    rcases c3 c hc with ⟨x, hx, hpx⟩ | ⟨hcB, hpx⟩
    · rw [hpx]
      apply hparw
      have hxE := ((BundleState.mem_ends _ _ _).mp hx).1
      rw [c11, ← hwE] at hxE
      exact ((hwP σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ').2.2.1 x
        ((mem_edgeEnds _ _).mpr hxE)).1
    · rw [hpx]
      exact (compLSFBatch_compSt hI hU hC).2.2.2.1 (hpar c hcB)
  · intro C hC hpar hRC hdisj
    obtain ⟨hUBw, hBw⟩ := hwL4 C hC hpar hRC hdisj
    have hsplit0 : batchSplitCount (bundleRunsStep cs B k ord' U).1 = 0 := by
      have h0 := hle
      rw [hUBw] at h0
      exact Nat.le_zero.mp h0
    have hnil : (bundleRunsStep cs B k ord' U).1 = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro op hop
      have hds := c7 op hop
      cases op with
      | insert => exact hds
      | delete e =>
        obtain ⟨e', he', heq, hD⟩ := c8 _ hop rfl
        cases heq
        exact Finset.disjoint_left.mp hdisj he' hD
      | split v v' St Sh =>
        rw [batchSplitCount, List.countP_eq_zero] at hsplit0
        exact hsplit0 _ hop rfl
    refine ⟨hnil, ?_⟩
    have hgr : (bundleRunsStep cs B k ord' U).2.graph = B.graph := by
      rw [c6, hnil]
      rfl
    have hbo : (bundleRunsStep cs B k ord' U).2.bundleOf = B.bundleOf := by
      funext x
      obtain ⟨e, side⟩ := x
      cases side
      · exact congrFun (congrArg MGraph.head hgr) e
      · exact congrFun (congrArg MGraph.tail hgr) e
    refine bundleState_ext (congrArg MGraph.V hgr) (congrArg MGraph.E hgr) ?_ hbo
    funext c
    by_cases hc : c ∈ (bundleRunsStep cs B k ord' U).2.vertices
    · rcases c3 c hc with ⟨x, hx, hpx⟩ | ⟨-, hpx⟩
      · rw [hpx, hBw]
        have hxc := ((BundleState.mem_ends _ _ _).mp hx).2
        rw [hbo] at hxc
        rw [hxc]
      · exact hpx
    · exact c4 c hc

end MinCostFlow.SparseCore
