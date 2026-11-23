module

public import MinCostFlow.SparseCore.Program.AssemblyInputRun

import MinCostFlow.Chain.BundleRestartDyn
import MinCostFlow.Chain.BundleRestartMach
import MinCostFlow.SparseCore.Program.RestartModelInv
import MinCostFlow.SparseCore.BundleEpochCost

/-!
# The five branch re-embedding coverage facts on reached states (`ReembFactsStep`)

Proves the five hypotheses of `mem_stepBundleTree_reembList_of_emb_ne` (`BranchReembFacts`) on
every valid ordered step from a nonempty state `s` reached under `SparseCoreOrdInput` for
`sparseCoreBundleRestartToolMachWith`:

1. `stepBundleTree_bun_edges_subset`: every bundle only loses edges in `stepBundleTree`.
2. Surviving-bundle membership: an edge `e` that lies in the new core graph
   `coreGraph info.state.cs.G info.state.cs.lsf` and outside `info.state.S_cur.E` cannot have been
   deleted by the batch `U` (even if `U` deletes `e` and inserts `e` again: after the step `e` is
   in no bundle, so `RestartScurModelInv` places `e` in `S_cur` as a cross edge or an extra edge
   of its component, contradicting `e ∉ info.state.S_cur.E`).
3. Disjointness of active bundles: at most one active bundle holds `e` (`initBundleTreeWith_buckets_sum_le`).
4. Spanner-bundle graph agreement: after the step, each active bucket spanner's graph has the exact
   edge set of its bundle (`runOrdAfterRestarts_bun_inv`).
5. Dynamic-spanner coverage: if an active bucket spanner changes `piTotal` on a surviving edge `e`,
   then `e ∈ DynSpanner.updateReembSet` (`DynSpanner.mem_updateReembList_of_piTotal_ne`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.LSF
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Unconditional shrinking of bundle edge sets -/

/-- In `stepBundleTree`, every bundle only loses edges (whether ready or not). -/
theorem stepBundleTree_bun_edges_subset {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (p : Finset ℕ × ℤ) :
    ((stepBundleTree sparsify tr U ord ord').state.bun p).edges ⊆ (tr.bun p).edges := by
  change (bundleCompStep tr.cs (tr.bun p) tr.k ord ord' U).2.edges ⊆ (tr.bun p).edges
  by_cases hR : BundleStepReady tr.cs (tr.bun p) tr.k ord ord' U
  · rw [bundleCompStep_edges_eq hR]; exact Finset.sdiff_subset
  · rw [bundleCompStep_of_not hR]

/-! ## 2. Private run-extension and `runBatchState` helpers -/

private lemma updateGo_state_eq_runState' {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us : List Update) :
    ∀ (U : List Update) (k₀ : ℕ) (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      (∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      (DynSpanner.updateGo sparsify (DynSpanner.runState (L := L) G₀ q sparsify us k₀) U uhAcc dAcc cAcc).state =
        DynSpanner.runState (L := L) G₀ q sparsify us (k₀ + U.length)
  | [], k₀, _, _, _, _ => by simp [DynSpanner.updateGo]
  | u :: U, k₀, uhAcc, dAcc, cAcc, hget => by
    have h0 : us[k₀]? = some u := by simpa using hget 0 (Nat.succ_pos _)
    have hstep : (DynSpanner.step (DynSpanner.runState (L := L) G₀ q sparsify us k₀) u sparsify).state =
        DynSpanner.runState (L := L) G₀ q sparsify us (k₀ + 1) := by
      simp [DynSpanner.runState, h0]
    simp only [DynSpanner.updateGo, hstep]
    rw [updateGo_state_eq_runState' G₀ q sparsify us U (k₀ + 1) _ _ _ (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hget (i + 1) (Nat.succ_lt_succ hi))]
    simp [Nat.add_assoc, Nat.add_comm 1 U.length]

private lemma runBatchState_eq_runState' {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (Us : List (List Update)) :
    ∀ t ≤ Us.length,
      DynSpanner.runBatchState (L := L) G₀ q sparsify Us t =
        DynSpanner.runState (L := L) G₀ q sparsify Us.flatten (Us.take t).flatten.length
  | 0, _ => by simp [DynSpanner.runBatchState, DynSpanner.runState]
  | t + 1, ht => by
    have hlt : t < Us.length := Nat.lt_of_succ_le ht
    have hsome : Us[t]? = some (Us[t]'hlt) := List.getElem?_eq_getElem hlt
    have htake : Us.take (t + 1) = Us.take t ++ [Us[t]'hlt] :=
      List.take_add_one.trans (by simp [hsome])
    have hflat_split : Us.flatten = (Us.take t).flatten ++ (Us[t]'hlt ++ (Us.drop (t + 1)).flatten) := by
      have h1 : Us.flatten = (Us.take (t + 1) ++ Us.drop (t + 1)).flatten :=
        congrArg List.flatten (List.take_append_drop (t + 1) Us).symm
      rw [h1, htake, List.flatten_append, List.flatten_append, List.flatten_singleton, List.append_assoc]
    simp only [DynSpanner.runBatchState, hsome, runBatchState_eq_runState' G₀ q sparsify Us t (Nat.le_of_lt hlt),
      DynSpanner.update]
    rw [updateGo_state_eq_runState' G₀ q sparsify Us.flatten (Us[t]'hlt) (Us.take t).flatten.length _ _ _
      (fun i hi => by
        rw [hflat_split, List.getElem?_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi])]
    rw [htake, List.flatten_append, List.flatten_singleton, List.length_append]

private lemma rotation_ext' {G : MGraph} {ρ₁ ρ₂ : Rotation G} (h : ρ₁.order = ρ₂.order) :
    ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; simp only [Rotation.mk.injEq]; exact h

private lemma cast_rot_order' {G₁ G₂ : MGraph} (h : G₁ = G₂) (ρ : Rotation G₁) :
    (h ▸ ρ : Rotation G₂).order = ρ.order := by
  cases h; rfl

private lemma cast_rotBatch' {G₁ G₂ G₁' G₂' : MGraph} {U₁ U₂ : List Update} {c : ℕ}
    (h1 : G₁ = G₂) (h2 : G₁' = G₂') (hU : U₁ = U₂) (hG1 : G₁' = G₁.applyBatch U₁)
    (ρ : Rotation G₁) (σ : Rotation G₁')
    (hRB : RotationBatch c U₁ ρ (hG1 ▸ σ)) :
    RotationBatch c U₂ (h1 ▸ ρ)
      ((show G₂' = G₂.applyBatch U₂ by subst h1; subst h2; subst hU; exact hG1) ▸ (h2 ▸ σ)) := by
  subst h1; subst h2; subst hU; exact hRB

private lemma runOrdAfterUpdate_congr' (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List End} {r₁ r₂ : ℕ → List ℕ} :
    ∀ t,
      (∀ s ≤ t, D₁.G s = D₂.G s ∧ D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s ∧
        ord₁ s = ord₂ s) →
      (∀ s < t, r₁ s = r₂ s) →
      T.runOrdAfterUpdate k M N D₁ ord₁ r₁ t = T.runOrdAfterUpdate k M N D₂ ord₂ r₂ t
  | 0, hD, _ => by
    have h0 := hD 0 le_rfl
    simp [SparseCoreRestartTool.runOrdAfterUpdate, h0.1, h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2]
  | t + 1, hD, hr => by
    have ih := runOrdAfterUpdate_congr' T k M N t
      (fun s hs => hD s (Nat.le_succ_of_le hs))
      (fun s hs => hr s (Nat.lt_succ_of_lt hs))
    have ht1 := hD (t + 1) le_rfl
    have hrt := hr t (Nat.lt_succ_self t)
    simp only [SparseCoreRestartTool.runOrdAfterUpdate, ih, hrt, ht1.2.1, ht1.2.2.1,
      ht1.2.2.2.1, ht1.2.2.2.2]

private lemma runOrdAfterRestarts_congr' (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List End} {r₁ r₂ : ℕ → List ℕ} (t : ℕ)
    (hD : ∀ s ≤ t, D₁.G s = D₂.G s ∧ D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s ∧
      ord₁ s = ord₂ s)
    (hr : ∀ s ≤ t, r₁ s = r₂ s) :
    T.runOrdAfterRestarts k M N D₁ ord₁ r₁ t = T.runOrdAfterRestarts k M N D₂ ord₂ r₂ t := by
  simp only [SparseCoreRestartTool.runOrdAfterRestarts, hr t le_rfl,
    runOrdAfterUpdate_congr' T k M N t hD (fun s hs => hr s hs.le)]

/-- Extend a `SparseCoreOrdInput` run by one valid ordered update `(U, ord')` (without requiring
`updateThreshold`). The resulting run matches `s` at step `τ` and applies `(U, ord')` with no
restarts at step `τ + 1`. -/
private lemma sparseCoreOrdInput_exists_run_step (T : SparseCoreRestartTool) {k M N : ℕ}
    {s : T.State} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hinp : SparseCoreOrdInput T k M N s G ord n)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord') :
    ∃ (τ : ℕ) (D' : DynamicInstance) (ordSeq' : ℕ → ℕ → List End) (restarts' : ℕ → List ℕ),
      (D'.G 0).IsValid ∧ (D'.G 0).m ≤ M ∧ (D'.G 0).n ≤ N ∧
      (∀ e ∈ (D'.G 0).E, 0 < D'.ℓ 0 e) ∧
      D'.IsValid (τ + 1) ∧ OrderedUpTo D' (τ + 1) 2 ordSeq' ∧
      D'.G τ = G ∧ D'.U (τ + 1) = U ∧ ordSeq' τ = ord ∧ ordSeq' (τ + 1) = ord' ∧
      restarts' (τ + 1) = [] ∧
      T.runOrdAfterRestarts k M N D' ordSeq' restarts' τ = s := by
  obtain ⟨τ, D, ordSeq, restarts, hG0, hm0, hn0, hℓ0, hD, hOrd, hGτ, hordτ, _, _, hrun⟩ :=
    sparseCoreOrdInput_exists_run T hinp
  let D' : DynamicInstance :=
    { G := fun t => if t ≤ τ then D.G t else G.applyBatch U
      U := fun t => if t ≤ τ then D.U t else U
      g := fun t => if t ≤ τ then D.g t else fun _ => 0
      ℓ := fun t => if t ≤ τ then D.ℓ t else fun _ => 1 }
  let ordSeq' : ℕ → ℕ → List End := fun t => if t ≤ τ then ordSeq t else ord'
  let restarts' : ℕ → List ℕ := fun t => if t ≤ τ then restarts t else []
  have hagree : ∀ t ≤ τ, D'.G t = D.G t ∧ D'.U t = D.U t ∧ D'.ℓ t = D.ℓ t ∧ D'.g t = D.g t ∧
      ordSeq' t = ordSeq t := fun t ht => by simp [D', ordSeq', ht]
  have hD'_val : D'.IsValid (τ + 1) := by
    intro t ht1 ht2
    by_cases ht : t ≤ τ
    · have h1 := hD t ht1 ht
      have htm : t - 1 ≤ τ := by omega
      simp only [D', ht, htm, ↓reduceIte]
      exact h1
    · have hteq : t = τ + 1 := by omega
      subst hteq
      have hnot : ¬ (τ + 1 ≤ τ) := by omega
      simp only [D', hnot, Nat.add_sub_cancel, le_refl, ↓reduceIte, hGτ]
      exact ⟨hBV, trivial⟩
  have hOrd' : OrderedUpTo D' (τ + 1) 2 ordSeq' := by
    obtain ⟨ρ, hρ_ord, hρ_step⟩ := hOrd
    obtain ⟨ρU, σU, hρU, hσU, hRB⟩ := hOrdB
    let ρ' : ∀ t, Rotation (D'.G t) := fun t =>
      if ht : t ≤ τ then
        (show D.G t = D'.G t by simp [D', ht]) ▸ ρ t
      else
        (show G.applyBatch U = D'.G t by simp [D', ht]) ▸ σU
    refine ⟨ρ', fun t ht => ?_, fun t ht => ?_⟩
    · by_cases hle : t ≤ τ
      · have h1 : (ρ' t).order = (ρ t).order := by
          dsimp only [ρ']
          rw [dite_eq_left_of_eq_true (eq_true hle)]
          exact cast_rot_order' _ _
        rw [h1, hρ_ord t hle]; simp [ordSeq', hle]
      · have h1 : (ρ' t).order = σU.order := by
          dsimp only [ρ']
          rw [dite_eq_right_of_eq_false (eq_false hle)]
          exact cast_rot_order' _ _
        rw [h1, hσU]; simp [ordSeq', hle]
    · by_cases hlt : t < τ
      · have ht_le : t ≤ τ := hlt.le
        have ht1_le : t + 1 ≤ τ := hlt
        obtain ⟨hGstep, hstep⟩ := hρ_step t hlt
        have hGeq : D'.G (t + 1) = (D'.G t).applyBatch (D'.U (t + 1)) := by
          simp only [D', ht_le, ht1_le, ↓reduceIte]; exact hGstep
        refine ⟨hGeq, ?_⟩
        have hD't : D.G t = D'.G t := by simp [D', ht_le]
        have hD't1 : D.G (t + 1) = D'.G (t + 1) := by simp [D', ht1_le]
        have hD'U : D.U (t + 1) = D'.U (t + 1) := by simp [D', ht1_le]
        dsimp only [ρ']
        rw [dite_eq_left_of_eq_true (eq_true ht_le), dite_eq_left_of_eq_true (eq_true ht1_le)]
        exact cast_rotBatch' hD't hD't1 hD'U hGstep (ρ t) (ρ (t + 1)) hstep
      · have hteq : t = τ := by omega
        subst t
        have hnot : ¬ (τ + 1 ≤ τ) := by omega
        have hGeq : D'.G (τ + 1) = (D'.G τ).applyBatch (D'.U (τ + 1)) := by
          simp [D', hnot, hGτ]
        refine ⟨hGeq, ?_⟩
        have hD't : D.G τ = D'.G τ := by simp [D']
        have hD't1 : G.applyBatch U = D'.G (τ + 1) := by simp [D', hnot]
        have hD'U : U = D'.U (τ + 1) := by simp [D', hnot]
        dsimp only [ρ']
        rw [dite_eq_left_of_eq_true (eq_true le_rfl), dite_eq_right_of_eq_false (eq_false hnot)]
        have hρ_eq : ρ τ = hGτ.symm ▸ ρU := by
          apply rotation_ext'
          rw [cast_rot_order', hρU, hρ_ord τ le_rfl, hordτ]
        have hRB0 : RotationBatch 2 U ρU ((rfl : G.applyBatch U = G.applyBatch U) ▸ σU) := hRB
        have hRB1 := cast_rotBatch' (hGτ.symm.trans hD't) hD't1 hD'U rfl ρU σU hRB0
        have hcast : (hGτ.symm.trans hD't) ▸ ρU = hD't ▸ ρ τ := by
          rw [hρ_eq]; cases hGτ; rfl
        rwa [hcast] at hRB1
  have hrun_τ : T.runOrdAfterRestarts k M N D' ordSeq' restarts' τ = s := by
    have hprev := runOrdAfterRestarts_congr' T k M N (r₁ := restarts') (r₂ := restarts) τ hagree
      (fun s hs => by dsimp only [restarts']; simp [hs])
    exact hprev.trans hrun
  have hnot : ¬ (τ + 1 ≤ τ) := by omega
  refine ⟨τ, D', ordSeq', restarts', by simpa [D'] using hG0, by simpa [D'] using hm0,
    by simpa [D'] using hn0, by simpa [D'] using hℓ0, hD'_val, hOrd',
    by simp [D', hGτ], by simp [D', hnot], by simp [ordSeq', hordτ], by simp [ordSeq', hnot],
    by simp [restarts', hnot], hrun_τ⟩

private lemma comp_edge_disj_nonCross' {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C₁ C₂ : Finset ℕ}
    (hC₁ : C₁ ∈ components cs.G₀) (hC₂ : C₂ ∈ components cs.G₀) (hne : C₁ ≠ C₂)
    {e : ℕ} (he₁ : e ∈ (cs.compSt C₁).G.E) (he₂ : e ∈ (cs.compSt C₂).G.E)
    (hnc : e ∉ cs.crossEdges) : False := by
  have ht₁ : cs.G.tail e ∈ (cs.compSt C₁).G.V := by
    rw [← (hI.hNonCross_ends C₁ hC₁ e he₁ hnc).1]
    exact ((hI.hCompLSF C₁ hC₁).1.hG_val e he₁).1
  have ht₂ : cs.G.tail e ∈ (cs.compSt C₂).G.V := by
    rw [← (hI.hNonCross_ends C₂ hC₂ e he₂ hnc).1]
    exact ((hI.hCompLSF C₂ hC₂).1.hG_val e he₂).1
  exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C₂ hC₂ hne) ht₁ ht₂

/-! ## 3. Main theorem: all five facts of `BranchReembFacts` -/

/-- **All five branch re-embedding coverage facts** (the five hypotheses of
`mem_stepBundleTree_reembList_of_emb_ne`, bundled as `BranchReembFacts`) on any valid ordered step
`(U, ord')` from a nonempty state `s` reached under `SparseCoreOrdInput`, for every edge `e` that
belongs to the new core graph and lies outside the new sparsified core `S_cur`. -/
theorem sparseCoreOrdInput_reembFacts
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {P_b : SparsifyParams}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k) (hL : 1 ≤ L) (hSp : SparsifySpec M P_b (sparsify M))
    (hinp : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    (hne : SparseCoreBundleState.isNonempty (L := L) s = true)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord')
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) {e : ℕ}
    (heCore' : e ∈ (coreGraph
      (stepBundleTree sparsify (SparseCoreBundleState.trees (L := L) s j) U
        (SparseCoreBundleState.ord (L := L) s) ord').state.cs.G
      (stepBundleTree sparsify (SparseCoreBundleState.trees (L := L) s j) U
        (SparseCoreBundleState.ord (L := L) s) ord').state.cs.lsf).E)
    (heOff' : e ∉ (stepBundleTree sparsify (SparseCoreBundleState.trees (L := L) s j) U
        (SparseCoreBundleState.ord (L := L) s) ord').state.S_cur.E) :
    let tr := SparseCoreBundleState.trees (L := L) s j
    let info := stepBundleTree sparsify tr U (SparseCoreBundleState.ord (L := L) s) ord'
    (∀ p : Finset ℕ × ℤ, (info.state.bun p).edges ⊆ (tr.bun p).edges) ∧
    (∀ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps → p.2 ∈ tr.activeBuckets p.1 →
      e ∈ (tr.bun p).edges → e ∈ (info.state.bun p).edges) ∧
    (∀ p₁ p₂ : Finset ℕ × ℤ,
      p₁.1 ∈ tr.activeComps → p₁.2 ∈ tr.activeBuckets p₁.1 →
      p₂.1 ∈ tr.activeComps → p₂.2 ∈ tr.activeBuckets p₂.1 →
      e ∈ (tr.bun p₁).edges → e ∈ (tr.bun p₂).edges → p₁ = p₂) ∧
    (∀ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps → p.2 ∈ tr.activeBuckets p.1 →
      (info.stepOut p).state.G.E = (info.state.bun p).edges) ∧
    (∀ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps → p.2 ∈ tr.activeBuckets p.1 →
      e ∈ (info.stepOut p).state.G.E →
      DynSpanner.piTotal (info.stepOut p).state e ≠ DynSpanner.piTotal (tr.dyn p) e →
      e ∈ DynSpanner.updateReembSet (tr.dyn p) (info.U_B p) (sparsify tr.m₀)) := by
  classical
  intro tr info
  let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
  let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  obtain ⟨_, hord_s, hmn⟩ := asm_input_inv lsfInit C_lsst L sparsify params spanConst hinp
  have hs_ord : SparseCoreBundleState.ord (L := L) s = ord := hord_s hne
  have htr_m₀ : tr.m₀ = M := (hmn j).1
  obtain ⟨τ, D', ordSeq', restarts', hG₀, hM, hN, hℓ₀, hD', hOrd', _, hU_eq, hord_τ, hord_τ1,
      hrest_τ1, hrun_τ⟩ :=
    sparseCoreOrdInput_exists_run_step Tm hinp U ord' hBV hOrdB
  have hNM_τ := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
    sparsify params spanConst k M N D' ordSeq' restarts' τ).2.2
  rw [hrun_τ] at hNM_τ
  have hV₀ : (D'.G 0).V.Nonempty := by
    have h1 := (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify
      k M N D' ordSeq' restarts' τ).2.1
    rw [← hNM_τ.isNonempty, hne] at h1
    exact of_decide_eq_true h1.symm
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N (τ + 1) hk D' ordSeq' restarts' hG₀ hV₀ hℓ₀ hD' hOrd' j hInit
  have hBun0 := hBun 0 (Nat.zero_le _)
  have hBun_τ := hBun τ (Nat.le_succ τ)
  have hBun_τ1 := hBun (τ + 1) le_rfl
  set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D'.G 0) (D'.ℓ 0) (ordSeq' 0) j
  set pre := (Tb.runOrdAfterUpdate k M N D' ordSeq' restarts' τ).1.trees j
  set post := (Tb.runOrdAfterRestarts k M N D' ordSeq' restarts' τ).trees j
  set pre' := (Tb.runOrdAfterUpdate k M N D' ordSeq' restarts' (τ + 1)).1.trees j
  have hbf : BundleBaseFieldsEq post pre :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (Tb.runOrdAfterUpdate k M N D' ordSeq' restarts' τ).1 (restarts' τ)).2.2.2.2.1 j
  have hEq : BundleNonMachEq tr post := hNM_τ.trees j
  have hne_post : (Tb.runOrdAfterRestarts k M N D' ordSeq' restarts' τ).isNonempty = true :=
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D' ordSeq' restarts' τ).2.1.trans
      (decide_eq_true hV₀)
  have hord_post : (Tb.runOrdAfterRestarts k M N D' ordSeq' restarts' τ).ord = ord := by
    have h1 := ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify
      k M N D' ordSeq' restarts' τ).2.2.2.2 hV₀).2
    exact h1.trans hord_τ
  set infoB := stepBundleTree sparsify post U ord ord'
  have hpre'_eq : pre' = infoB.state := by
    dsimp only [pre', Tb, infoB]
    rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
      sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_post, hord_post, hU_eq, hord_τ1]
  have hStepNM := BundleNonMachEq.step sparsify hEq U ord ord'
  have hinfo_eq : info = stepBundleTree sparsify tr U ord ord' := by
    dsimp only [info]; rw [hs_ord]
  have hEq' : BundleNonMachEq info.state pre' := by
    rw [hinfo_eq, hpre'_eq]; exact hStepNM.1
  have hUB_eq : info.U_B = infoB.U_B := by rw [hinfo_eq]; exact hStepNM.2.1
  have hStepOut_eq : info.stepOut = infoB.stepOut := by rw [hinfo_eq]; exact hStepNM.2.2.2.1
  have hAct_sub : tr.activeComps ⊆ components (D'.G 0) := by
    rw [hEq.activeComps, hbf.activeComps]
    exact hBun_τ.2.2.2.2.2.2.2.2.2.1.2
  -- Prove all 5 conjuncts.
  refine ⟨stepBundleTree_bun_edges_subset sparsify tr U _ ord', ?_, ?_, ?_, ?_⟩
  · -- Fact 2: surviving edge in active bundle stays in that bundle.
    intro p hp1 hp2 he_in
    have hC0 : p.1 ∈ components (D'.G 0) := hAct_sub hp1
    have hRSMI' : RestartScurModelInv pre' :=
      restartScurModelInv_of_runOrdAfterUpdate lsfInit C_lsst L hL P_b sparsify
        k M N (τ + 1) hk D' ordSeq' restarts' hM hN hSp hG₀ hV₀ hℓ₀ hD' hOrd' j hInit (τ + 1) le_rfl
    have he_post : e ∈ (post.bun p).edges := hEq.bun ▸ he_in
    have hpe_edges_τ : (post.bun p).edges =
        (st₀.bun p).edges \ (Finset.Icc 1 τ).biUnion (fun r => batchDeletes (D'.U r)) := by
      have hcb := (hBun_τ.2.2.2.2.2.2.2.2.2.2.2 p.1 hC0).2 p.2
      exact hcb.2.2.2.1.trans hcb.2.2.1
    have hpe_edges_τ1 : ∀ C' ∈ components (D'.G 0), ∀ b' : ℤ,
        (pre'.bun (C', b')).edges =
          (st₀.bun (C', b')).edges \
            (Finset.Icc 1 (τ + 1)).biUnion (fun r => batchDeletes (D'.U r)) := fun C' hC' b' =>
      ((hBun_τ1.2.2.2.2.2.2.2.2.2.2.2 C' hC').2 b').2.2.1
    have hIcc_ins : Finset.Icc 1 (τ + 1) = insert (τ + 1) (Finset.Icc 1 τ) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    -- Show `e ∉ batchDeletes U` by contradiction against `heCore'` and `heOff'`.
    have hnotDel : e ∉ batchDeletes U := by
      intro hdel
      have heCore_pre' : e ∈ (coreGraph pre'.cs.G pre'.cs.lsf).E := by
        rwa [← hEq'.cs]
      have heOff_pre' : e ∉ pre'.S_cur.E := by
        rwa [← hEq'.S_cur]
      have heG' : e ∈ pre'.cs.G.E := (Finset.mem_sdiff.mp heCore_pre').1
      have heNotF' : e ∉ pre'.cs.RF.F.E := (Finset.mem_sdiff.mp heCore_pre').2
      have hI' : CompLSFInv C_lsst (D'.ℓ 0) pre'.cs := hBun_τ1.2.2.2.2.2.2.2.1
      have hG₀_pre' : pre'.cs.G₀ = D'.G 0 := by
        rw [hBun_τ1.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
      have hnotCross : e ∉ pre'.cs.crossEdges := by
        intro hc
        apply heOff_pre'
        rw [hRSMI'.2.2.1]
        exact Finset.mem_union_right _ hc
      obtain ⟨C_e, hC_e_mem, heCe⟩ := hI'.hEdge_cover e heG' hnotCross
      have hC_e0 : C_e ∈ components (D'.G 0) := hG₀_pre' ▸ hC_e_mem
      have hCe_act : C_e ∈ pre'.activeComps := by
        by_contra hna
        have hcomp_eq : pre'.cs.compSt C_e = st₀.cs.compSt C_e :=
          (hBun_τ1.2.2.2.2.2.2.2.2.2.2.1 C_e hC_e0 hna).1
        have he_st0_Ce : e ∈ (st₀.cs.compSt C_e).G.E := hcomp_eq ▸ heCe
        have he_st0_p : e ∈ (st₀.bun p).edges := by
          rw [hpe_edges_τ] at he_post
          exact (Finset.mem_sdiff.mp he_post).1
        have he_st0_C : e ∈ (st₀.cs.compSt p.1).G.E :=
          ((hBun0.2.2.2.2.2.2.2.2.2.2.2 p.1 hC0).2 p.2).1.2.2 he_st0_p
        have hI₀ : CompLSFInv C_lsst (D'.ℓ 0) st₀.cs := hBun0.2.2.2.2.2.2.2.1
        have hnc0 : e ∉ st₀.cs.crossEdges := by
          have hdisj := ((hBun0.2.2.2.2.2.2.2.2.2.2.2 p.1 hC0).2 p.2).2.2.2.2.1
          exact Finset.disjoint_left.mp (Disjoint.mono_right hI₀.hCross_sub hdisj) he_st0_p
        have hp_act' : p.1 ∈ pre'.activeComps := by
          rw [hpre'_eq]
          exact Finset.mem_union_left _ (hEq.activeComps ▸ hp1)
        have hne_C : p.1 ≠ C_e := fun h => hna (h ▸ hp_act')
        exact comp_edge_disj_nonCross' hI₀ hC0 hC_e0 hne_C he_st0_C he_st0_Ce hnc0
      have heNotFCe : e ∉ (pre'.cs.compSt C_e).RF.F.E := by
        intro hf
        apply heNotF'
        exact Finset.mem_biUnion.mpr ⟨C_e, hC_e_mem, hf⟩
      have heNotBun : e ∉ (pre'.activeBuckets C_e).biUnion fun b' => (pre'.bun (C_e, b')).edges := by
        intro hb
        obtain ⟨b', _, heb'⟩ := Finset.mem_biUnion.mp hb
        rw [hpe_edges_τ1 C_e hC_e0 b', hIcc_ins, Finset.biUnion_insert, hU_eq] at heb'
        exact (Finset.mem_sdiff.mp heb').2 (Finset.mem_union_left _ hdel)
      have heExtra : e ∈ pre'.extraEdges C_e := by
        unfold BundleTreeState.extraEdges
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heCe, heNotFCe⟩, heNotBun⟩
      apply heOff_pre'
      rw [hRSMI'.2.2.1]
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨C_e, hCe_act, heExtra⟩))
    -- Since `e ∉ batchDeletes U`, `e` remains in `(pre'.bun p).edges`.
    rw [hEq'.bun, hpe_edges_τ1 p.1 hC0 p.2, hIcc_ins, Finset.biUnion_insert, hU_eq]
    rw [hpe_edges_τ] at he_post
    obtain ⟨he0, hnd_old⟩ := Finset.mem_sdiff.mp he_post
    refine Finset.mem_sdiff.mpr ⟨he0, fun hun => ?_⟩
    rcases Finset.mem_union.mp hun with h1 | h2
    · exact hnotDel h1
    · exact hnd_old h2
  · -- Fact 3: distinct active bundles are disjoint.
    intro p₁ p₂ hp₁1 _ hp₂1 _ he₁ he₂
    have hC₁ : p₁.1 ∈ components (D'.G 0) := hAct_sub hp₁1
    have hC₂ : p₂.1 ∈ components (D'.G 0) := hAct_sub hp₂1
    have hsub₁ : (tr.bun p₁).edges ⊆ (st₀.bun p₁).edges := by
      rw [hEq.bun, ((hBun_τ.2.2.2.2.2.2.2.2.2.2.2 p₁.1 hC₁).2 p₁.2).2.2.2.1,
        ((hBun_τ.2.2.2.2.2.2.2.2.2.2.2 p₁.1 hC₁).2 p₁.2).2.2.1]
      exact Finset.sdiff_subset
    have hsub₂ : (tr.bun p₂).edges ⊆ (st₀.bun p₂).edges := by
      rw [hEq.bun, ((hBun_τ.2.2.2.2.2.2.2.2.2.2.2 p₂.1 hC₂).2 p₂.2).2.2.2.1,
        ((hBun_τ.2.2.2.2.2.2.2.2.2.2.2 p₂.1 hC₂).2 p₂.2).2.2.1]
      exact Finset.sdiff_subset
    have hdisj0 := (initBundleTreeWith_buckets_sum_le lsfInit L sparsify
      (M := M) (N := N) hk (G₀ := D'.G 0) (D'.ℓ 0) (ordSeq' 0) j).2.2.2
    by_contra hne_p
    exact Finset.disjoint_left.mp (hdisj0 p₁.1 hC₁ p₂.1 hC₂ p₁.2 p₂.2 hne_p)
      (hsub₁ he₁) (hsub₂ he₂)
  · -- Fact 4: active bucket spanner graph matches bundle edge set after the step.
    intro p hp1 _
    have hC0 : p.1 ∈ components (D'.G 0) := hAct_sub hp1
    have hGE : GraphEq (pre'.dyn p).G (pre'.bun p).graph :=
      ((hBun_τ1.2.2.2.2.2.2.2.2.2.2.2 p.1 hC0).2 p.2).2.2.2.2.2.1
    have hdyn_eq : (info.stepOut p).state = pre'.dyn p := by
      change (info.state.dyn p) = pre'.dyn p
      rw [hEq'.dyn]
    rw [hdyn_eq, hEq'.bun]
    exact hGE.2.1
  · -- Fact 5: active bucket spanner changes `piTotal` ⇒ `e ∈ updateReembSet`.
    intro p hp1 _ heG' hne_pi
    have hC0 : p.1 ∈ components (D'.G 0) := hAct_sub hp1
    set s₀ := bundleLastRestart restarts' j τ
    obtain ⟨hs₀_le, hs₀_cases, hs₀_none⟩ := bundleLastRestart_spec restarts' j τ
    have hNoRest : ∀ r, s₀ < r → r < τ + 1 → j ∉ restarts' r := fun r h1 h2 =>
      hs₀_none r h1 (Nat.lt_succ_iff.mp h2)
    set ep := epochBundleSeq lsfInit C_lsst L sparsify k M N D' ordSeq' restarts' s₀ (τ + 1) j
    set Hb := ((ep 0).bun p).graph
    set G_init := normGraph Hb
    set q := phaseBase (Hb.n + bundleSplitBudget k M) L
    set Us_ep : List (List Update) := (List.range (τ + 1 - s₀)).map fun r =>
      (stepBundleTree sparsify (ep r) (D'.U (s₀ + r + 1))
        (ordSeq' (s₀ + r)) (ordSeq' (s₀ + r + 1))).U_B p
    have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
      k M N (τ + 1) hk D' ordSeq' restarts' hM hN hSp hG₀ hV₀ hℓ₀ hD' hOrd'
      s₀ (τ + 1) j hInit (by omega) le_rfl hs₀_cases hNoRest p.1 hC0 p.2
    have hlt_ep : τ - s₀ < τ + 1 - s₀ := by omega
    have hep_τ : ep (τ - s₀) = post := by
      have h1 := (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D' ordSeq' restarts'
        s₀ (τ + 1) j (by omega)).1 (τ - s₀) hlt_ep
      have hadd : s₀ + (τ - s₀) = τ := by omega
      rwa [hadd] at h1
    have hlen_Us : Us_ep.length = (τ - s₀) + 1 := by
      simp only [Us_ep, List.length_map, List.length_range]; omega
    have hlast_Us : Us_ep[τ - s₀]? = some (info.U_B p) := by
      have h1 : Us_ep[τ - s₀]? = some ((stepBundleTree sparsify (ep (τ - s₀))
          (D'.U (s₀ + (τ - s₀) + 1)) (ordSeq' (s₀ + (τ - s₀)))
          (ordSeq' (s₀ + (τ - s₀) + 1))).U_B p) := by
        simp [Us_ep, hlt_ep]
      have hadd : s₀ + (τ - s₀) = τ := by omega
      rw [h1, hep_τ, hadd, hU_eq, hord_τ, hord_τ1, hUB_eq]
    have hUs_split : Us_ep = Us_ep.take (τ - s₀) ++ [info.U_B p] := by
      have h1 : Us_ep = Us_ep.take ((τ - s₀) + 1) := by rw [← hlen_Us, List.take_length]
      conv_lhs => rw [h1, List.take_add_one, hlast_Us]
      rfl
    have hflat_eq : Us_ep.flatten = (Us_ep.take (τ - s₀)).flatten ++ info.U_B p := by
      conv_lhs => rw [hUs_split]
      rw [List.flatten_append, List.flatten_singleton]
    set k₀ := (Us_ep.take (τ - s₀)).flatten.length
    have hlen_flat : k₀ + (info.U_B p).length ≤ Us_ep.flatten.length := by
      rw [hflat_eq, List.length_append]
    have hmatch : ∀ (i : ℕ) (hi : i < (info.U_B p).length),
        Us_ep.flatten[k₀ + i]? = some ((info.U_B p)[i]'hi) := fun i hi => by
      rw [hflat_eq, List.getElem?_append_right (Nat.le_add_right k₀ i), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hi]
    have hst₀_eq : tr.dyn p = DynSpanner.runState (L := L) G_init q (sparsify M) Us_ep.flatten k₀ := by
      have h1 := (hDyn.2.2.2.2.2.2.2.2.2.1 (τ - s₀) hlt_ep.le).1
      rw [hEq.dyn, ← hep_τ, h1]
      exact runBatchState_eq_runState' (L := L) G_init q (sparsify M) Us_ep (τ - s₀) (by omega)
    have hG_val : G_init.IsValid := normGraph_isValid hDyn.1
    have hq1 : 1 ≤ q := le_trans (by omega) (two_le_phaseBase _ L)
    have hGm : G_init.m ≤ M := le_trans hDyn.2.1 hM
    have hBV_norm : G_init.BatchIsValid Us_ep.flatten :=
      batchIsValid_of_graphEq (graphEq_symm (normGraph_graphEq Hb)) hDyn.2.2.2.2.2.1
    have hds_norm : ∀ u ∈ Us_ep.flatten, isDelOrSplit u := hDyn.2.2.2.2.2.2.1
    have hstepOut_eq : info.stepOut p =
        DynSpanner.update (tr.dyn p) (info.U_B p) (sparsify M) := by
      rw [← htr_m₀]; rfl
    rw [htr_m₀, ← DynSpanner.mem_updateReembList, hst₀_eq]
    refine DynSpanner.mem_updateReembList_of_piTotal_ne hG_val hL hq1 hGm hSp hBV_norm hds_norm
      hlen_flat hmatch e ?_ ?_
    · rw [← hst₀_eq, ← hstepOut_eq]; exact heG'
    · rw [← hst₀_eq, ← hstepOut_eq]; exact hne_pi

end MinCostFlow.SparseCore
