module

public import MinCostFlow.Bundle.SplitCount
public import MinCostFlow.SparseCore.QuotientStepBound
public import MinCostFlow.DynSpanner.Walks
import Mathlib.Tactic.Linarith
import MinCostFlow.Bundle.SplitValid
import MinCostFlow.Bundle.SplitPartition
import MinCostFlow.SparseCore.GraphHelpers

/-!
# Bundle count bounds

Add the counts of ordered core steps, then bound growth from the epoch's
initial population. The quotient step bound supplies the number of core
splits. The boundary estimate is a separate condition on their order.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner

/-- Sum split and deletion estimates for the individual core operations. -/
theorem bundleCounts_of_coreSteps {U : List Update} {Bs : List (List Update)}
    (h : List.Forall₂ (fun u B =>
      batchSplitCount B ≤ 2 * updateSplitTag u ∧ B.countP deleteTag ≤ (if deleteTag u then 1 else 0))
      U Bs) :
    batchSplitCount Bs.flatten ≤ 2 * batchSplitCount U ∧
    Bs.flatten.countP deleteTag ≤ U.countP deleteTag := by
  induction h with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | @cons u B U Bs hstep _ ih =>
    rw [List.flatten_cons, batchSplitCount_append, List.countP_append, List.countP_cons]
    have htag : batchSplitCount [u] = updateSplitTag u := by cases u <;> rfl
    have hcons : batchSplitCount (u :: U) = updateSplitTag u + batchSplitCount U := by
      rw [← htag, ← batchSplitCount_append]
      rfl
    rw [hcons, Nat.mul_add]
    exact ⟨Nat.add_le_add hstep.1 ih.1,
      (Nat.add_le_add hstep.2 ih.2).trans (Nat.le_of_eq (Nat.add_comm _ _))⟩

/-- The split-count side of the bundle analogue of `tildeStepSingle_spec`.
The per-operation hypothesis is the bound that ordered bundle
maintenance gives. The quotient step count is the one proved from
`splitTargets_card_le`. -/
theorem bundleSplitBound_of_tildeStepSingle {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {S₀ S : LSFState} {ts : TildeState} {u : Update}
    (hI₀ : LSFInv C_lsst ℓ₀ S₀)
    (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInv C_lsst ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    (hT : TildeInv S₀ S ts) {Bs : List (List Update)}
    (h : List.Forall₂ (fun op B =>
      batchSplitCount B ≤ 2 * updateSplitTag op ∧ B.countP deleteTag ≤ (if deleteTag op then 1 else 0))
      (tildeStepSingle S ts u).1 Bs) :
    batchSplitCount Bs.flatten ≤ 2 * (updateSplitTag u +
      ((applyLSFUpdate S u).R \ S.R).card + updateForestSplitCard S u) := by
  have hs := tildeStepSingle_spec hI₀ hCov₀ hI hu hD hT
  dsimp only at hs
  have hb := hs.2.2.2.2.2.1
  rw [hs.1] at hb
  exact (bundleCounts_of_coreSteps h).1.trans (Nat.mul_le_mul_left 2 hb)

/-- The vertex envelope for an epoch, including one begun by a restart.
The starting core has at most `r₀ + s₀` vertices and admits at most
`m + q₀` edges. The prefix and epoch use `s₀` and `s₁` core splits
respectively. -/
theorem bundleVertexEnvelope {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k m q₀ r₀ s₀ s₁ n : ℕ} (hk : 0 < k)
    (hCsize : C.V.card ≤ r₀ + s₀) (hEdges : E.card ≤ m + q₀)
    (hGrowth : n ≤ (initBundleState ρ E k).vertices.card + 2 * s₁) :
    k * n ≤ k * (r₀ + s₀ + 2 * s₁) + 2 * (m + q₀) := by
  calc
    k * n ≤ k * ((initBundleState ρ E k).vertices.card + 2 * s₁) :=
      Nat.mul_le_mul_left k hGrowth
    _ ≤ k * C.V.card + 2 * E.card + k * (2 * s₁) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_right (initBundleState_vertex_bound ρ hC hE hk) _
    _ ≤ _ := by
      rw [Nat.mul_add]
      have hc := Nat.mul_le_mul_left k hCsize
      have he := Nat.mul_le_mul_left 2 hEdges
      omega


/-- With the connected-component initial bound `1 + 4m/k` from the Lean
proof of Lemma 5.4 (page 17) and the count from Lemma 5.14 (page 22),
the epoch has at most `234(⌈m/k⌉ + 1)` bundle vertices. The split counts
are for the ordered stream, both before and after the epoch starts. -/
theorem bundleVertexEnvelope_of_lemma_5_14 {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k m q₀ q₁ r₀ s₀ s₁ n : ℕ} (hk : 0 < k)
    {L : ℝ} (hL : 1 ≤ L)
    (hRoot : (r₀ : ℝ) ≤ 1 + 4 * ((m : ℝ) / (k : ℝ)))
    (hCap : ((q₀ : ℝ) + q₁) ≤ (m : ℝ) / ((k : ℝ) * L))
    (hSplits : ((s₀ : ℝ) + s₁) ≤ ((q₀ : ℝ) + q₁) + 112 * (((q₀ : ℝ) + q₁) * L))
    (hCsize : C.V.card ≤ r₀ + s₀) (hEdges : E.card ≤ m + q₀)
    (hGrowth : n ≤ (initBundleState ρ E k).vertices.card + 2 * s₁) :
    n ≤ 234 * (m ⌈/⌉ k + 1) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hqL : ((q₀ : ℝ) + q₁) * L ≤ (m : ℝ) / k := by
    apply (le_div_iff₀ hLpos).mp
    rwa [div_div]
  have hqL' : (q₀ : ℝ) + q₁ ≤ ((q₀ : ℝ) + q₁) * L := by
    have hq : 0 ≤ (q₀ : ℝ) + q₁ := by positivity
    exact le_mul_of_one_le_right hq hL
  have hs : (s₀ : ℝ) + s₁ ≤ 113 * ((m : ℝ) / k) := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq₀ : (q₀ : ℝ) ≤ m :=
    (by linarith [show (0 : ℝ) ≤ q₁ from Nat.cast_nonneg q₁] :
      (q₀ : ℝ) ≤ (m : ℝ) / k).trans (div_le_self (Nat.cast_nonneg _) hk1)
  have h := bundleVertexEnvelope ρ hC hE hk hCsize hEdges hGrowth
  have hR : (k : ℝ) * n ≤ (k : ℝ) * ((r₀ : ℝ) + s₀ + 2 * s₁) + 2 * ((m : ℝ) + q₀) := by
    exact_mod_cast h
  have hterm : (r₀ : ℝ) + s₀ + 2 * s₁ ≤ 1 + 230 * ((m : ℝ) / k) := by
    linarith [show (0 : ℝ) ≤ s₀ from Nat.cast_nonneg s₀]
  have hmul := mul_le_mul_of_nonneg_left hterm hkR.le
  have heq : (k : ℝ) * (1 + 230 * ((m : ℝ) / k)) = k + 230 * (m : ℝ) := by
    rw [mul_add, mul_one, mul_left_comm (k : ℝ) (230 : ℝ), mul_div_cancel₀ _ hkR.ne']
  rw [heq] at hmul
  have hlin : (k : ℝ) * n ≤ k + 234 * m := by linarith
  have hnat : k * n ≤ k + 234 * m := by exact_mod_cast hlin
  have hround : m ≤ k * (m ⌈/⌉ k) := le_smul_ceilDiv (β := ℕ) hk
  apply Nat.le_of_mul_le_mul_left _ hk
  calc
    k * n ≤ k + 234 * m := hnat
    _ ≤ k + 234 * (k * (m ⌈/⌉ k)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 234 hround) _
    _ ≤ k * (234 * (m ⌈/⌉ k + 1)) := by
      rw [Nat.mul_left_comm k 234, Nat.mul_add k, Nat.mul_one, Nat.mul_add 234]
      have hcoeff : k ≤ 234 * k := by
        simpa using Nat.mul_le_mul_right k (show 1 ≤ 234 by decide)
      omega


private theorem bundleSplit_only_splits {C : MGraph} (B : BundleState) (ρ : Rotation C)
    (v v' : ℕ) (St Sh : Finset ℕ) :
    ∀ op ∈ (B.split ρ v v' St Sh).1, isSplit op := by
  unfold BundleState.split
  let p := splitEnds St Sh
  have hb : ∀ (plan : List (ℕ × List (List End))) (s : List Update × BundleState),
      (∀ op ∈ s.1, isSplit op) →
      ∀ op ∈ (plan.foldl (bundleSplitFoldStep v v' p) s).1, isSplit op := by
    intro plan
    induction plan with
    | nil => exact fun _ hs => hs
    | cons x xs ih =>
      intro s hs
      obtain ⟨b, runs⟩ := x
      obtain ⟨ops, st⟩ := s
      rw [List.foldl_cons]
      apply ih
      intro op hop
      simp only [bundleSplitFoldStep, List.mem_append] at hop
      rcases hop with h | h
      · exact hs op h
      · obtain ⟨⟨run, i⟩, _, rfl⟩ := List.mem_map.mp h
        rfl
  exact hb _ ([], B) (by simp)

private theorem count_eq_length_of_all {α : Type*} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x) : xs.countP p = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, p y := fun y hy => h y (List.mem_cons_of_mem x hy)
    simp [hx, ih hxs]

/-- One ordered core operation yields at most two bundle splits or one
deletion. The vertex count increases by exactly the number of splits. -/
theorem bundleStep_counts {C : MGraph} {ρ : Rotation C} {B : BundleState} {k β : ℕ}
    {u : Update} {σ : Rotation (C.applyUpdate u)} (h : B.IsPartition ρ k)
    (hstep : RotationStep β u ρ σ) :
    let out := bundleStep B ρ u
    batchSplitCount out.1 ≤ β * updateSplitTag u ∧
    out.1.countP deleteTag ≤ (if deleteTag u then 1 else 0) ∧
    out.2.vertices.card = B.vertices.card + batchSplitCount out.1 := by
  cases u with
  | insert => simp [bundleStep, batchSplitCount, deleteTag, updateSplitTag]
  | delete e =>
    by_cases he : e ∈ B.edges <;> simp [bundleStep, BundleState.deleteEdge, he,
      batchSplitCount, isSplit, deleteTag, updateSplitTag]
  | split v v' St Sh =>
    let out := B.split ρ v v' St Sh
    have hlen : out.1.length ≤ β := (BundleState.split_length_le h).trans hstep.2.2.1
    have hsv : batchSplitCount out.1 = out.1.length :=
      count_eq_length_of_all isSplit out.1 (bundleSplit_only_splits B ρ v v' St Sh)
    have hd : out.1.countP deleteTag = 0 := by
      apply List.countP_eq_zero.mpr
      intro op hop
      have hs := bundleSplit_only_splits B ρ v v' St Sh op hop
      cases op <;> simp_all [isSplit, deleteTag]
    change batchSplitCount out.1 ≤ β * 1 ∧ out.1.countP deleteTag ≤ 0 ∧
      out.2.vertices.card = B.vertices.card + batchSplitCount out.1
    rw [hsv, hd]
    exact ⟨(Nat.mul_one β).symm ▸ hlen, Nat.le_refl _, BundleState.split_vertex_growth B ρ v v' St Sh⟩


/-- Every emitted primitive applies to the bundle graph in its turn. -/
theorem bundleStep_valid {C : MGraph} {ρ : Rotation C} {B : BundleState} {k : ℕ}
    {u : Update} (h : B.IsPartition ρ k) :
    B.graph.BatchIsValid (bundleStep B ρ u).1 := by
  cases u with
  | insert => trivial
  | delete e =>
    by_cases he : e ∈ B.edges <;> simp [bundleStep, BundleState.deleteEdge, he,
      MGraph.BatchIsValid, MGraph.UpdateIsValid, BundleState.graph]
  | split => exact BundleState.split_valid h

/-- The bundle input uses deletions and splits only. -/
theorem bundleStep_only_delOrSplit {C : MGraph} {ρ : Rotation C} (B : BundleState) (u : Update) :
    ∀ op ∈ (bundleStep B ρ u).1, isDelOrSplit op := by
  cases u with
  | insert => simp [bundleStep]
  | delete e => by_cases he : e ∈ B.edges <;> simp [bundleStep, BundleState.deleteEdge, he, isDelOrSplit]
  | split v v' St Sh =>
    intro op hop
    have hs := bundleSplit_only_splits B ρ v v' St Sh op hop
    cases op <;> simp_all [isSplit, isDelOrSplit]

private theorem bundle_maxDeg_applyBatch_le {G : MGraph} {U : List Update}
    (hG : G.IsValid) (hU : G.BatchIsValid U) (hops : ∀ u ∈ U, isDelOrSplit u) :
    (G.applyBatch U).maxDeg ≤ G.maxDeg := by
  induction U generalizing G with
  | nil => exact Nat.le_refl _
  | cons u U ih =>
    have hu := hops u List.mem_cons_self
    exact (ih (isValid_applyUpdate_of_delOrSplit hG hU.1 hu) hU.2
      (fun v hv => hops v (List.mem_cons_of_mem u hv))).trans (maxDeg_applyUpdate_le hG hU.1 hu)

/-- Applying one emitted bundle batch keeps the maximum degree at most
the bundle cap. -/
theorem bundleStep_degree_le {C : MGraph} {ρ : Rotation C} {B : BundleState} {k : ℕ}
    (h : B.IsPartition ρ k) (u : Update) :
    (bundleStep B ρ u).2.graph.maxDeg ≤ k := by
  rw [bundleStep_graph]
  exact (bundle_maxDeg_applyBatch_le (BundleState.graph_isValid h) (bundleStep_valid h)
    (bundleStep_only_delOrSplit B u)).trans (BundleState.maxDeg_le h)


/-- The bundle update has the new partition, a valid batch, and the exact
vertex count. -/
theorem bundleStep_spec {C : MGraph} {ρ : Rotation C} {B : BundleState} {k β : ℕ}
    {u : Update} {σ : Rotation (C.applyUpdate u)} (h : B.IsPartition ρ k)
    (hu : C.UpdateIsValid u) (hstep : RotationStep β u ρ σ) :
    let out := bundleStep B ρ u
    out.2.IsPartition σ k ∧
    B.graph.BatchIsValid out.1 ∧ out.2.graph = B.graph.applyBatch out.1 ∧
    (∀ op ∈ out.1, isDelOrSplit op) ∧
    batchSplitCount out.1 ≤ β * updateSplitTag u ∧
    out.1.countP deleteTag ≤ (if deleteTag u then 1 else 0) ∧
    out.2.vertices.card = B.vertices.card + batchSplitCount out.1 := by
  have hpost : (bundleStep B ρ u).2.IsPartition σ k := by
    cases u with
    | insert => exact BundleState.insert_preserves h hu hstep
    | delete e => exact (B.deleteEdge_spec h hstep).1
    | split => exact BundleState.split_preserves h hu hstep
  exact ⟨hpost, bundleStep_valid h, bundleStep_graph B ρ u,
    bundleStep_only_delOrSplit B u, bundleStep_counts h hstep⟩

/-- A bundle partition does not depend on where each vertex's cyclic order starts. -/
theorem BundleState.IsPartition.rotate {C : MGraph} {ρ σ : Rotation C} {B : BundleState} {k : ℕ}
    (h : B.IsPartition ρ k) (hr : ∀ v, (σ.order v).IsRotated (ρ.order v)) :
    B.IsPartition σ k :=
  ⟨h.1, h.2.1, h.2.2.1, fun b hb =>
    ⟨(h.2.2.2 b hb).1, (h.2.2.2 b hb).2.of_isRotated (isRotated_filter _ (hr _))⟩⟩

/-- Run the bundle step through an ordered core batch. The resulting
partition agrees with the final core graph, and split and deletion counts
add over the batch. -/
theorem bundleBatch_spec {C : MGraph} {U : List Update} {ρ : Rotation C} {β : ℕ}
    {σ : Rotation (C.applyBatch U)} (hRot : RotationBatch β U ρ σ)
    {k : ℕ} (B : BundleState) (h : B.IsPartition ρ k) (hU : C.BatchIsValid U) :
    ∃ (UB : List Update) (B' : BundleState), B'.IsPartition σ k ∧ B.graph.BatchIsValid UB ∧ B'.graph = B.graph.applyBatch UB ∧
      (∀ op ∈ UB, isDelOrSplit op) ∧
      batchSplitCount UB ≤ β * batchSplitCount U ∧ UB.countP deleteTag ≤ U.countP deleteTag ∧
      B'.vertices.card = B.vertices.card + batchSplitCount UB := by
  induction hRot generalizing B with
  | nil hr => exact ⟨[], B, h.rotate hr, trivial, rfl, by simp, by simp [batchSplitCount],
      Nat.le_refl _, by simp [batchSplitCount]⟩
  | @cons C op rest ρ ρ' σ hs _ ih =>
    obtain ⟨hp, hb, hgraph, hds, hsp, hdel, hv⟩ := bundleStep_spec h hU.1 hs
    let bd := bundleStep B ρ op
    change bd.2.IsPartition ρ' k at hp
    obtain ⟨UB, B', hP', hB', hG', hds', hsp', hdel', hv'⟩ := ih bd.2 hp hU.2
    refine ⟨bd.1 ++ UB, B', hP', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MinCostFlow.SparseCore.batchIsValid_append]
      exact ⟨hb, hgraph ▸ hB'⟩
    · rw [MinCostFlow.SparseCore.applyBatch_append, ← hgraph]
      exact hG'
    · intro u hu
      exact (List.mem_append.mp hu).elim (hds u) (hds' u)
    · have hcount : batchSplitCount (op :: rest) = updateSplitTag op + batchSplitCount rest := by
        cases op <;> simp [batchSplitCount, List.countP_cons, isSplit, updateSplitTag, Nat.add_comm]
      rw [batchSplitCount_append, hcount, Nat.mul_add]
      exact Nat.add_le_add hsp hsp'
    · rw [List.countP_append, List.countP_cons]
      exact (Nat.add_le_add hdel hdel').trans (Nat.le_of_eq (Nat.add_comm _ _))
    · rw [batchSplitCount_append, hv', hv, Nat.add_assoc]


private theorem tildeStepSingle_delete_le (S : LSFState) (ts : TildeState) (u : Update) :
    ((tildeStepSingle S ts u).1.countP deleteTag) ≤ 1 := by
  have ha (C : MGraph) : ((splitStepA ts.m S.G C u ts.nextVid).1.countP deleteTag) = 0 := by
    cases u <;> simp [splitStepA, deleteTag]
  have hb (C : MGraph) (m : ℕ → ℕ) (next : ℕ) :
      ((rootSplitStep S (applyLSFUpdate S u) C m next).1.countP deleteTag) = 0 := by
    simp [rootSplitStep, List.countP_map, Function.comp_def, deleteTag]
  have hd : (delStepC ts.C u).countP deleteTag ≤ 1 := by
    cases u with
    | delete e => by_cases he : e ∈ ts.C.E <;> simp [delStepC, he, deleteTag]
    | insert => simp [delStepC]
    | split => simp [delStepC]
  unfold tildeStepSingle
  simp only [List.countP_append, ha, hb, Nat.add_zero]
  exact hd

/-- Bundle version of the single-step bounds derived from
`splitTargets_card_le` for a quotient stream with ordered rotations.
The rotations are supplied because a quotient batch without them can violate
the split boundary bound. -/
theorem bundleTildeStepSingle_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {S₀ S : LSFState} {ts : TildeState} {u : Update}
    (hI₀ : LSFInv C_lsst ℓ₀ S₀)
    (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInv C_lsst ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    (hT : TildeInv S₀ S ts) {ρ : Rotation ts.C}
    {σ : Rotation (ts.C.applyBatch (tildeStepSingle S ts u).1)}
    (hRot : RotationBatch 2 (tildeStepSingle S ts u).1 ρ σ)
    {B : BundleState} {k : ℕ} (h : B.IsPartition ρ k) :
    ∃ (UB : List Update) (B' : BundleState), B'.IsPartition σ k ∧
      B.graph.BatchIsValid UB ∧ B'.graph = B.graph.applyBatch UB ∧
      (∀ op ∈ UB, isDelOrSplit op) ∧
      batchSplitCount UB ≤ 2 * (updateSplitTag u + ((applyLSFUpdate S u).R \ S.R).card +
        updateForestSplitCard S u) ∧
      UB.countP deleteTag ≤ 1 ∧ B'.vertices.card = B.vertices.card + batchSplitCount UB := by
  have hs := tildeStepSingle_spec hI₀ hCov₀ hI hu hD hT
  have hb := hs.2.2.2.2.2.1
  rw [hs.1] at hb
  obtain ⟨UB, B', hp, hv, he, ho, hsp, hd, hc⟩ := bundleBatch_spec hRot B h hs.2.2.1
  exact ⟨UB, B', hp, hv, he, ho, hsp.trans (Nat.mul_le_mul_left 2 hb),
    hd.trans (tildeStepSingle_delete_le S ts u), hc⟩

/-- An ordered core prefix within the Lemma 5.14 count stays within the
bundle vertex envelope. The prefix may start
at a restart, with the earlier updates counted by `q₀` and `s₀`. -/
theorem bundleBatch_vertexEnvelope {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k m q₀ q₁ r₀ s₀ : ℕ} (hk : 0 < k)
    {L : ℝ} (hL : 1 ≤ L) {U : List Update} {σ : Rotation (C.applyBatch U)}
    (hRot : RotationBatch 2 U ρ σ) (hU : C.BatchIsValid U)
    (hRoot : (r₀ : ℝ) ≤ 1 + 4 * ((m : ℝ) / (k : ℝ)))
    (hCap : ((q₀ : ℝ) + q₁) ≤ (m : ℝ) / ((k : ℝ) * L))
    (hSplits : ((s₀ : ℝ) + batchSplitCount U) ≤
      ((q₀ : ℝ) + q₁) + 112 * (((q₀ : ℝ) + q₁) * L))
    (hCsize : C.V.card ≤ r₀ + s₀) (hEdges : E.card ≤ m + q₀) :
    let B := initBundleState ρ E k
    ∃ (UB : List Update) (B' : BundleState), B'.IsPartition σ k ∧
      B.graph.BatchIsValid UB ∧ B'.graph = B.graph.applyBatch UB ∧
      B'.vertices.card ≤ 234 * (m ⌈/⌉ k + 1) := by
  intro B
  obtain ⟨UB, B', hp, hv, he, _, hs, _, hc⟩ :=
    bundleBatch_spec hRot B (initBundleState_inv ρ hC hE hk) hU
  refine ⟨UB, B', hp, hv, he, ?_⟩
  apply bundleVertexEnvelope_of_lemma_5_14 ρ hC hE hk hL hRoot hCap hSplits hCsize hEdges
  exact hc.le.trans (Nat.add_le_add_left hs _)

/-! ### The local count

A bundle splits only at a core split of its own parent vertex. So if every bundle has its parent
in a set `X` of core vertices, and every core split of a vertex of `X` makes its new vertex in
`X`, then the bundles keep their parents in `X` and split only at core splits whose new vertex is
in `X`. -/

/-- The update is a split whose new vertex lies in `X`. -/
@[expose] def splitNewIn (X : Finset ℕ) : Update → Bool
  | .split _ v' _ _ => decide (v' ∈ X)
  | _ => false

private theorem splitFoldStep_parent_mem (v v' : ℕ) (moved : End → Bool) {X : Finset ℕ}
    (hv : v ∈ X) (hv' : v' ∈ X) (s : List Update × BundleState) (p : ℕ × List (List End))
    (hs : ∀ c ∈ s.2.vertices, s.2.parent c ∈ X) :
    ∀ c ∈ (bundleSplitFoldStep v v' moved s p).2.vertices,
      (bundleSplitFoldStep v v' moved s p).2.parent c ∈ X := by
  obtain ⟨ops, st⟩ := s
  obtain ⟨b, runs⟩ := p
  intro c hc
  change c ∈ (st.graph.applyBatch (bundleRunUpdates b (st.vertices.sup id + 1) runs)).V at hc
  rw [bundleRunUpdates_V_mem] at hc
  simp only [bundleSplitFoldStep]
  split
  · next heq =>
    have hcV : c ∈ st.vertices := by
      rcases hc with hc | ⟨i, hi, rfl⟩
      · exact hc
      · exfalso
        rw [List.length_drop] at hi
        split_ifs at heq with h₁ h₂
        · rw [List.head?_eq_none_iff] at heq
          subst heq
          simp at hi
        · rw [List.getElem?_eq_none_iff] at heq
          omega
        · omega
    exact hs c hcV
  · split_ifs
    · exact hv'
    · exact hv

private theorem splitFold_parent_mem (v v' : ℕ) (moved : End → Bool) {X : Finset ℕ}
    (hv : v ∈ X) (hv' : v' ∈ X) (plan : List (ℕ × List (List End))) :
    ∀ (s : List Update × BundleState), (∀ c ∈ s.2.vertices, s.2.parent c ∈ X) →
      ∀ c ∈ (plan.foldl (bundleSplitFoldStep v v' moved) s).2.vertices,
        (plan.foldl (bundleSplitFoldStep v v' moved) s).2.parent c ∈ X := by
  induction plan with
  | nil => exact fun _ hs => hs
  | cons p rest ih =>
    intro s hs
    exact ih _ (splitFoldStep_parent_mem v v' _ hv hv' s p hs)

private theorem split_parent_mem {C : MGraph} (B : BundleState) (ρ : Rotation C)
    {v v' : ℕ} (St Sh : Finset ℕ) {X : Finset ℕ} (hv : v ∈ X) (hv' : v' ∈ X)
    (hX : ∀ b ∈ B.vertices, B.parent b ∈ X) :
    ∀ b ∈ (B.split ρ v v' St Sh).2.vertices, (B.split ρ v v' St Sh).2.parent b ∈ X :=
  splitFold_parent_mem v v' (splitEnds St Sh) hv hv' (bundleSplitPlan ρ B v (splitEnds St Sh))
    ([], B) hX

private theorem splitFold_edges (v v' : ℕ) (moved : End → Bool)
    (plan : List (ℕ × List (List End))) :
    ∀ (s : List Update × BundleState),
      (plan.foldl (bundleSplitFoldStep v v' moved) s).2.edges = s.2.edges := by
  induction plan with
  | nil => exact fun _ => rfl
  | cons p rest ih =>
    intro s
    rw [List.foldl_cons, ih]
    obtain ⟨ops, st⟩ := s
    obtain ⟨b, runs⟩ := p
    exact bundleRunUpdates_edges st.graph b _ runs

private theorem split_edges {C : MGraph} (B : BundleState) (ρ : Rotation C)
    (v v' : ℕ) (St Sh : Finset ℕ) : (B.split ρ v v' St Sh).2.edges = B.edges :=
  splitFold_edges v v' (splitEnds St Sh) (bundleSplitPlan ρ B v (splitEnds St Sh)) ([], B)

private theorem split_of_no_parent {C : MGraph} (B : BundleState) (ρ : Rotation C)
    {v v' : ℕ} (St Sh : Finset ℕ) (h : ∀ b ∈ B.vertices, B.parent b ≠ v) :
    B.split ρ v v' St Sh = ([], B) := by
  have hplan : bundleSplitPlan ρ B v (splitEnds St Sh) = [] := by
    have hf : B.vertices.filter (fun b => B.parent b = v) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun b hb => h b hb
    simp [bundleSplitPlan, hf]
  simp [BundleState.split, hplan]

/-- One core operation keeps the bundle parents in a closed set `X`, and it yields bundle splits
only if it is a split whose new vertex is in `X`. -/
theorem bundleStep_local {C : MGraph} {ρ : Rotation C} {B : BundleState} {k β : ℕ}
    {u : Update} {σ : Rotation (C.applyUpdate u)} (h : B.IsPartition ρ k)
    (hstep : RotationStep β u ρ σ) {X : Finset ℕ} (hX : ∀ b ∈ B.vertices, B.parent b ∈ X)
    (hu : ∀ v v' St Sh, u = .split v v' St Sh → v ∈ X → v' ∈ X) :
    let out := bundleStep B ρ u
    (∀ b ∈ out.2.vertices, out.2.parent b ∈ X) ∧
    batchSplitCount out.1 ≤ β * (if splitNewIn X u then 1 else 0) := by
  have hc := (bundleStep_counts h hstep).1
  cases u with
  | insert => exact ⟨hX, by simp [bundleStep, batchSplitCount]⟩
  | delete e =>
    refine ⟨hX, ?_⟩
    by_cases he : e ∈ B.edges <;>
      simp [bundleStep, BundleState.deleteEdge, he, batchSplitCount, isSplit]
  | split v v' St Sh =>
    by_cases hp : ∃ b ∈ B.vertices, B.parent b = v
    · obtain ⟨b, hb, rfl⟩ := hp
      have hv := hX b hb
      have hv' := hu _ v' St Sh rfl hv
      refine ⟨split_parent_mem B ρ St Sh hv hv' hX, ?_⟩
      simpa [splitNewIn, hv', updateSplitTag] using hc
    · push Not at hp
      have he := split_of_no_parent B ρ (v' := v') St Sh hp
      have he' : bundleStep B ρ (.split v v' St Sh) = ([], B) := he
      show (∀ b ∈ (bundleStep B ρ (.split v v' St Sh)).2.vertices,
          (bundleStep B ρ (.split v v' St Sh)).2.parent b ∈ X) ∧
        batchSplitCount (bundleStep B ρ (.split v v' St Sh)).1 ≤ _
      rw [he']
      exact ⟨hX, by simp [batchSplitCount]⟩

/-- One core operation keeps the bundle edges among the old ones, and its bundle deletions are
deletions of old bundle edges by the operation itself. -/
theorem bundleStep_edges_deletes {C : MGraph} (ρ : Rotation C) (B : BundleState) (u : Update) :
    (bundleStep B ρ u).2.edges ⊆ B.edges ∧
    ∀ op ∈ (bundleStep B ρ u).1, deleteTag op →
      ∃ e ∈ B.edges, op = .delete e ∧ u = .delete e := by
  cases u with
  | insert => exact ⟨Finset.Subset.rfl, by simp [bundleStep]⟩
  | delete e =>
    refine ⟨Finset.erase_subset _ _, ?_⟩
    intro op hop _
    by_cases he : e ∈ B.edges
    · simp only [bundleStep, BundleState.deleteEdge, he, ↓reduceIte, List.mem_singleton] at hop
      exact ⟨e, he, hop, rfl⟩
    · simp [bundleStep, BundleState.deleteEdge, he] at hop
  | split v v' St Sh =>
    refine ⟨(split_edges B ρ v v' St Sh).le, ?_⟩
    intro op hop hd
    have hs := bundleSplit_only_splits B ρ v v' St Sh op hop
    cases op <;> simp_all [isSplit, deleteTag]

/-- One core operation removes a bundle edge exactly when it deletes that edge. -/
theorem bundleStep_edges_exact {C : MGraph} (ρ : Rotation C) (B : BundleState) (u : Update) :
    (∀ e ∈ B.edges, e ∉ (bundleStep B ρ u).2.edges → u = .delete e) ∧
    ∀ e, u = .delete e → e ∉ (bundleStep B ρ u).2.edges := by
  cases u with
  | insert => exact ⟨fun e he hn => absurd he hn, fun e h => Update.noConfusion h⟩
  | delete f =>
    refine ⟨fun e he hn => ?_, fun e h => ?_⟩
    · have hn' : e ∉ B.edges.erase f := hn
      by_contra hne
      exact hn' (Finset.mem_erase.mpr ⟨fun hef => hne (by rw [hef]), he⟩)
    · obtain rfl := Update.delete.inj h
      exact Finset.notMem_erase _ B.edges
  | split v v' St Sh =>
    refine ⟨fun e he hn => absurd ((split_edges B ρ v v' St Sh).symm ▸ he) hn,
      fun e h => Update.noConfusion h⟩

/-- A core operation that deletes no bundle edge and is no split with new vertex in a closed set
`X` holding the bundle parents leaves the bundle state unchanged. -/
theorem bundleStep_unchanged {C : MGraph} (ρ : Rotation C) (B : BundleState) (u : Update)
    {X : Finset ℕ} (hX : ∀ b ∈ B.vertices, B.parent b ∈ X)
    (hu : ∀ v v' St Sh, u = .split v v' St Sh → v ∈ X → v' ∈ X)
    (hnew : splitNewIn X u = false) (hdel : ∀ e ∈ B.edges, u ≠ .delete e) :
    bundleStep B ρ u = ([], B) := by
  cases u with
  | insert => rfl
  | delete f =>
    have hf : f ∉ B.edges := fun hf => hdel f hf rfl
    change B.deleteEdge f = ([], B)
    simp only [BundleState.deleteEdge, hf, ↓reduceIte, Finset.erase_eq_of_notMem hf]
  | split v v' St Sh =>
    have hv' : v' ∉ X := by simpa [splitNewIn] using hnew
    exact split_of_no_parent B ρ St Sh fun b hb hbv =>
      hv' (hu v v' St Sh rfl (hbv ▸ hX b hb))

/-- Run the bundle step through an ordered core batch (`bundleBatch_spec`). Besides the clauses
of `bundleBatch_spec`, the bundle edges only shrink, every bundle deletion deletes an old bundle
edge that the core batch deletes, and the splits are local: for every set `X` of core vertices
that holds the bundle parents and is closed under the core splits, the bundles split only at core
splits whose new vertex is in `X`. -/
theorem bundleBatch_spec_local {C : MGraph} {U : List Update} {ρ : Rotation C} {β : ℕ}
    {σ : Rotation (C.applyBatch U)} (hRot : RotationBatch β U ρ σ)
    {k : ℕ} (B : BundleState) (h : B.IsPartition ρ k) (hU : C.BatchIsValid U) :
    ∃ (UB : List Update) (B' : BundleState), B'.IsPartition σ k ∧
      B.graph.BatchIsValid UB ∧ B'.graph = B.graph.applyBatch UB ∧
      (∀ op ∈ UB, isDelOrSplit op) ∧
      batchSplitCount UB ≤ β * batchSplitCount U ∧ UB.countP deleteTag ≤ U.countP deleteTag ∧
      B'.vertices.card = B.vertices.card + batchSplitCount UB ∧
      B'.edges ⊆ B.edges ∧
      (∀ op ∈ UB, deleteTag op → ∃ e ∈ B.edges, op = .delete e ∧ Update.delete e ∈ U) ∧
      (∀ e ∈ B.edges, e ∉ B'.edges → Update.delete e ∈ U) ∧
      (∀ e, Update.delete e ∈ U → e ∉ B'.edges) ∧
      ∀ X : Finset ℕ, (∀ b ∈ B.vertices, B.parent b ∈ X) →
        (∀ op ∈ U, ∀ v v' St Sh, op = .split v v' St Sh → v ∈ X → v' ∈ X) →
        (∀ b ∈ B'.vertices, B'.parent b ∈ X) ∧
        batchSplitCount UB ≤ β * U.countP (splitNewIn X) ∧
        ((∀ op ∈ U, splitNewIn X op = false) → (∀ e ∈ B.edges, Update.delete e ∉ U) →
          UB = [] ∧ B' = B) := by
  induction hRot generalizing B with
  | nil hr => exact ⟨[], B, h.rotate hr, trivial, rfl, by simp, by simp [batchSplitCount],
      Nat.le_refl _, by simp [batchSplitCount], Finset.Subset.rfl, by simp,
      fun e he hn => absurd he hn, by simp,
      fun X hX _ => ⟨hX, by simp [batchSplitCount], fun _ _ => ⟨rfl, rfl⟩⟩⟩
  | @cons C op rest ρ ρ' σ hs _ ih =>
    obtain ⟨hp, hb, hgraph, hds, hsp, hdel, hv⟩ := bundleStep_spec h hU.1 hs
    obtain ⟨hE₀, hD₀⟩ := bundleStep_edges_deletes ρ B op
    let bd := bundleStep B ρ op
    change bd.2.IsPartition ρ' k at hp
    obtain ⟨UB, B', hP', hB', hG', hds', hsp', hdel', hv', hE', hD', hR', hK', hL'⟩ :=
      ih bd.2 hp hU.2
    obtain ⟨hR₀, hK₀⟩ := bundleStep_edges_exact ρ B op
    refine ⟨bd.1 ++ UB, B', hP', ?_, ?_, ?_, ?_, ?_, ?_, hE'.trans hE₀, ?_, ?_, ?_, ?_⟩
    · rw [MinCostFlow.SparseCore.batchIsValid_append]
      exact ⟨hb, hgraph ▸ hB'⟩
    · rw [MinCostFlow.SparseCore.applyBatch_append, ← hgraph]
      exact hG'
    · intro u hu
      exact (List.mem_append.mp hu).elim (hds u) (hds' u)
    · have hcount : batchSplitCount (op :: rest) = updateSplitTag op + batchSplitCount rest := by
        cases op <;> simp [batchSplitCount, List.countP_cons, isSplit, updateSplitTag, Nat.add_comm]
      rw [batchSplitCount_append, hcount, Nat.mul_add]
      exact Nat.add_le_add hsp hsp'
    · rw [List.countP_append, List.countP_cons]
      exact (Nat.add_le_add hdel hdel').trans (Nat.le_of_eq (Nat.add_comm _ _))
    · rw [batchSplitCount_append, hv', hv, Nat.add_assoc]
    · intro o ho hd
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨e, he, rfl, rfl⟩ := hD₀ o ho hd
        exact ⟨e, he, rfl, List.mem_cons_self⟩
      · obtain ⟨e, he, rfl, hmem⟩ := hD' o ho hd
        exact ⟨e, hE₀ he, rfl, List.mem_cons_of_mem _ hmem⟩
    · intro e he hn
      by_cases h₀ : e ∈ bd.2.edges
      · exact List.mem_cons_of_mem _ (hR' e h₀ hn)
      · rw [hR₀ e he h₀]
        exact List.mem_cons_self
    · intro e hmem
      rcases List.mem_cons.mp hmem with h₀ | h₀
      · exact fun hB => hK₀ e h₀.symm (hE' hB)
      · exact hK' e h₀
    · intro X hX hcl
      have hcl₀ := fun v v' St Sh he => hcl op List.mem_cons_self v v' St Sh he
      obtain ⟨hX₁, hc₁⟩ := bundleStep_local h hs hX hcl₀
      obtain ⟨hX₂, hc₂, hu₂⟩ := hL' X hX₁ (fun o ho => hcl o (List.mem_cons_of_mem _ ho))
      refine ⟨hX₂, ?_, fun hnew hnd => ?_⟩
      · rw [batchSplitCount_append, List.countP_cons, Nat.mul_add]
        exact (Nat.add_comm _ _).le.trans (Nat.add_le_add hc₂ hc₁)
      · have hb : bd = ([], B) := bundleStep_unchanged ρ B op hX hcl₀
          (hnew op List.mem_cons_self)
          (fun e he hop => hnd e he (hop ▸ List.mem_cons_self))
        have hbd2 : bd.2 = B := by rw [hb]
        have hbd1 : bd.1 = [] := by rw [hb]
        obtain ⟨h1, h2⟩ := hu₂ (fun o ho => hnew o (List.mem_cons_of_mem _ ho))
          (fun e he hmem => hnd e (hbd2 ▸ he) (List.mem_cons_of_mem _ hmem))
        rw [hbd1, h1, h2, hbd2]
        exact ⟨rfl, rfl⟩

private theorem applyBatch_V_subset' (G : MGraph) (U : List Update) :
    G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u U ih =>
    refine Finset.Subset.trans ?_ (ih (G.applyUpdate u))
    cases u with
    | insert => exact Finset.Subset.rfl
    | delete => exact Finset.Subset.rfl
    | split v v' St Sh => exact Finset.subset_insert _ _

/-- In a valid batch the splits with new vertex in `X` are at most the new vertices in `X`. -/
theorem countP_splitNewIn_le {G : MGraph} {U : List Update} (hU : G.BatchIsValid U)
    (X : Finset ℕ) : U.countP (splitNewIn X) ≤ (((G.applyBatch U).V \ G.V) ∩ X).card := by
  induction U generalizing G with
  | nil => simp
  | cons u U ih =>
    have hU' := ih hU.2
    change _ ≤ ((((G.applyUpdate u).applyBatch U).V \ G.V) ∩ X).card
    have hsub : ((((G.applyUpdate u).applyBatch U).V \ (G.applyUpdate u).V) ∩ X) ⊆
        ((((G.applyUpdate u).applyBatch U).V \ G.V) ∩ X) := by
      intro w hw
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hw ⊢
      refine ⟨⟨hw.1.1, fun h => hw.1.2 ?_⟩, hw.2⟩
      cases u with
      | insert => exact h
      | delete => exact h
      | split v v' St Sh => exact Finset.mem_insert_of_mem h
    rw [List.countP_cons]
    cases u with
    | insert => simpa [splitNewIn] using hU'.trans (Finset.card_le_card hsub)
    | delete => simpa [splitNewIn] using hU'.trans (Finset.card_le_card hsub)
    | split v v' St Sh =>
      by_cases hX : v' ∈ X
      · have hnot : v' ∉ (((G.applyUpdate (.split v v' St Sh)).applyBatch U).V \
            (G.applyUpdate (.split v v' St Sh)).V) ∩ X := by
          simp [MGraph.applyUpdate]
        have hins : insert v' ((((G.applyUpdate (.split v v' St Sh)).applyBatch U).V \
            (G.applyUpdate (.split v v' St Sh)).V) ∩ X) ⊆
            ((((G.applyUpdate (.split v v' St Sh)).applyBatch U).V \ G.V) ∩ X) := by
          refine Finset.insert_subset ?_ hsub
          simp only [Finset.mem_inter, Finset.mem_sdiff]
          exact ⟨⟨applyBatch_V_subset' _ U (Finset.mem_insert_self _ _),
            hU.1.2.1⟩, hX⟩
        have := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem hnot] at this
        simp only [splitNewIn, hX, decide_true, ↓reduceIte]
        omega
      · simpa [splitNewIn, hX] using hU'.trans (Finset.card_le_card hsub)

end MinCostFlow.Bundle
