module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue11

import MinCostFlow.DynSpanner.Correctness
import MinCostFlow.SparseCore.Program.BundleModelBridge
import Mathlib.Tactic

/-!
# Per-task edge/vertex-cap and encoding-size lemmas (`AssemblyFsOpenCaps`)

Provides the pure dynamic-spanner and bundle-step helper lemmas used by `AssemblyFsOpen.lean`
to prove `AsmFsP4Open`:
1. `p4TaskCaps_of_valid`: proves `P4TaskCaps P eCap d U` (every edge in `UH`, `D`,
   `updateReembSet`, and post-update `piTotal` walks lies below `eCap`) from validity of
   `d.flat ++ U` and `∀ e ∈ d.G₀.E, e < eCap`.
2. `batchWithinCaps_bundleCompStep`: proves `BatchWithinCaps P.vCap P.eCap` for the bundle batch
   `bundleCompStep tr.cs B₀ tr.k ord ord' U` from `B₀.vertices = Finset.range nB` (`BundleSlotRepAt`)
   and `bundleRunsStep_vertices_range`.
3. `batchEnc_le_of_delOrSplit`: bounds `G.batchEnc U ≤ U.length * (2 * G.m + 1)` for any valid
   deletion/split batch `U` on a valid graph `G`, so `SmallBatchAt` bounds the encoded word count
   `totalWords ≤ 5 * U.length * (2 * G.m + 1) + 1`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

private lemma deg_le_two_m (G : MGraph) (v : ℕ) : G.deg v ≤ 2 * G.m := by
  unfold MGraph.deg MGraph.m
  have h1 : (G.E.filter fun e => G.tail e = v).card ≤ G.E.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h2 : (G.E.filter fun e => G.head e = v).card ≤ G.E.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

private lemma updateEnc_le_two_m_add_one (G : MGraph) (u : Update) (hds : isDelOrSplit u) :
    G.updateEnc u ≤ 2 * G.m + 1 := by
  cases u with
  | insert _ _ _ => cases hds
  | delete _ => simp [MGraph.updateEnc]
  | split v v' St Sh =>
    simp only [MGraph.updateEnc]
    have h1 : min ((G.applyUpdate (.split v v' St Sh)).deg v)
        ((G.applyUpdate (.split v v' St Sh)).deg v') ≤
        (G.applyUpdate (.split v v' St Sh)).deg v := min_le_left _ _
    have h2 : (G.applyUpdate (.split v v' St Sh)).deg v ≤
        2 * (G.applyUpdate (.split v v' St Sh)).m := deg_le_two_m _ _
    have hm : (G.applyUpdate (.split v v' St Sh)).m = G.m := rfl
    omega

private lemma applyBatch_E_of_inserts {H : MGraph} {L : List ℕ} {tl hd : ℕ → ℕ} :
    ∀ {e : ℕ}, e ∈ L → e ∈ (H.applyBatch (L.map fun e' => Update.insert e' (tl e') (hd e'))).E := by
  induction L generalizing H with
  | nil => intro e he; cases he
  | cons a rest ih =>
    intro e he
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | hrest
    · have hsub : ∀ (G : MGraph) (xs : List ℕ),
          G.E ⊆ (G.applyBatch (xs.map fun e' => Update.insert e' (tl e') (hd e'))).E := by
        intro G xs
        induction xs generalizing G with
        | nil => exact Finset.Subset.rfl
        | cons x xs ihx =>
          have h1 : G.E ⊆ (G.applyUpdate (.insert x (tl x) (hd x))).E :=
            Finset.subset_insert _ _
          exact h1.trans (ihx _)
      exact hsub (H.applyUpdate (.insert e (tl e) (hd e))) rest (Finset.mem_insert_self e H.E)
    · exact ih hrest

private lemma diffBatch_edge_below {eCap : ℕ} {H : MGraph} {uhPref : List Update}
    {H_new_E : Finset ℕ} {tl hd : ℕ → ℕ}
    (hPref : ∀ x ∈ uhPref, UpdEdgeBelow eCap x)
    (hMid_sub : (H.applyBatch uhPref).E ⊆ H.E)
    (hH : ∀ e ∈ H.E, e < eCap)
    (hH' : ∀ e ∈ (H.applyBatch (uhPref ++
      (((H.applyBatch uhPref).E \ H_new_E).sort (· ≤ ·)).map Update.delete ++
      ((H_new_E \ (H.applyBatch uhPref).E).sort (· ≤ ·)).map fun e => Update.insert e (tl e) (hd e))).E,
      e < eCap) :
    ∀ u' ∈ uhPref ++
      (((H.applyBatch uhPref).E \ H_new_E).sort (· ≤ ·)).map Update.delete ++
      ((H_new_E \ (H.applyBatch uhPref).E).sort (· ≤ ·)).map fun e => Update.insert e (tl e) (hd e),
      UpdEdgeBelow eCap u' := by
  intro u' hu'
  simp only [List.mem_append] at hu'
  rcases hu' with (hp | hdel) | hins
  · exact hPref u' hp
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hdel
    exact hH e (hMid_sub (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp he)).1)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hins
    have hmem := applyBatch_E_of_inserts
      (H := H.applyBatch (uhPref ++
        (((H.applyBatch uhPref).E \ H_new_E).sort (· ≤ ·)).map Update.delete))
      (tl := tl) (hd := hd) he
    rw [← applyBatch_append] at hmem
    exact hH' e hmem

private lemma step_uh_edge_below {L eCap : ℕ} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {st : DynSpannerState L} {u : Update} (hds : isDelOrSplit u)
    (hH : ∀ e ∈ st.H.E, e < eCap)
    (hH' : ∀ e ∈ (step st u sparsify).state.H.E, e < eCap) :
    ∀ u' ∈ (step st u sparsify).UH, UpdEdgeBelow eCap u' := by
  have hPref : ∀ x ∈ restrictUpdate u st.H, UpdEdgeBelow eCap x := by
    intro x hx
    cases u with
    | insert _ _ _ => cases hds
    | delete e =>
      unfold restrictUpdate at hx
      dsimp only at hx
      split_ifs at hx with he
      · simp only [List.mem_singleton] at hx
        subst hx
        exact hH e he
      · cases hx
    | split v v' St Sh =>
      simp only [restrictUpdate, List.mem_singleton] at hx
      subst hx
      trivial
  have hMid_sub : (st.H.applyBatch (restrictUpdate u st.H)).E ⊆ st.H.E := by
    cases u with
    | insert _ _ _ => cases hds
    | delete e =>
      unfold restrictUpdate; dsimp only; split_ifs
      · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate]
        exact Finset.erase_subset e st.H.E
      · exact Finset.Subset.rfl
    | split v v' St Sh =>
      simp [restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]
  by_cases hj0 : chooseLevel L st.q (st.t + 1) = 0
  · simp only [step, hj0, ↓reduceDIte] at hH' ⊢
    exact diffBatch_edge_below hPref hMid_sub hH hH'
  · simp only [step, hj0, ↓reduceDIte] at hH' ⊢
    exact diffBatch_edge_below hPref hMid_sub hH hH'

private lemma walk_edges_in_H {H : MGraph} {u v : ℕ} {W : List End}
    (hW : H.IsWalk u v W) : ∀ q ∈ W, q.1 ∈ H.E := by
  induction hW with
  | nil _ => intro _ hq; cases hq
  | cons he _ _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hrest
    · exact he
    · exact ih q hrest

private lemma applyBatch_V_sub_local (H : MGraph) (ls : List Update) :
    H.V ⊆ (H.applyBatch ls).V := by
  induction ls generalizing H with
  | nil => exact Finset.Subset.rfl
  | cons a as ih =>
    have ha : H.V ⊆ (H.applyUpdate a).V := by cases a <;> simp [MGraph.applyUpdate]
    exact ha.trans (ih _)

private lemma batchWithinCaps_of_delOrSplit_V_lt {vCap eCap : ℕ} :
    ∀ (G : MGraph) (U : List Update), G.BatchIsValid U → (∀ u ∈ U, isDelOrSplit u) →
      (∀ v ∈ (G.applyBatch U).V, v < vCap) → BatchWithinCaps vCap eCap U
  | _, [], _, _, _ => fun _ h => by cases h
  | G, u :: rest, ⟨hu, hrest⟩, hds, hV => by
    have hu_ds := hds u List.mem_cons_self
    have hrest_ds : ∀ x ∈ rest, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem u hx)
    have hV_sub : (G.applyUpdate u).V ⊆ ((G.applyUpdate u).applyBatch rest).V :=
      applyBatch_V_sub_local _ _
    have hrest_cap : BatchWithinCaps vCap eCap rest :=
      batchWithinCaps_of_delOrSplit_V_lt (G.applyUpdate u) rest hrest hrest_ds hV
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · cases x with
      | insert _ _ _ => cases hu_ds
      | delete _ => trivial
      | split v v' St Sh =>
        exact hV v' (hV_sub (by simp [MGraph.applyUpdate]))
    · exact hrest_cap x hmem

public section

/-- **Batch encoding bound for deletions and splits.** For any deletion/split batch `U`
on a graph `G`, `G.batchEnc U ≤ U.length * (2 * G.m + 1)`. -/
theorem batchEnc_le_of_delOrSplit :
    ∀ (G : MGraph) (U : List Update), (∀ u ∈ U, isDelOrSplit u) →
      G.batchEnc U ≤ U.length * (2 * G.m + 1)
  | _, [], _ => by simp [MGraph.batchEnc]
  | G, u :: rest, hds => by
    have hu := hds u List.mem_cons_self
    have hrest : ∀ x ∈ rest, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem u hx)
    have h1 := updateEnc_le_two_m_add_one G u hu
    have h2 := batchEnc_le_of_delOrSplit (G.applyUpdate u) rest hrest
    have hm : (G.applyUpdate u).m ≤ G.m := by
      cases u with
      | insert _ _ _ => cases hu
      | delete e => exact Finset.card_le_card (Finset.erase_subset e G.E)
      | split _ _ _ _ => exact le_rfl
    have h3 : rest.length * (2 * (G.applyUpdate u).m + 1) ≤ rest.length * (2 * G.m + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmul : (rest.length + 1) * (2 * G.m + 1) = rest.length * (2 * G.m + 1) + (2 * G.m + 1) :=
      Nat.succ_mul _ _
    simp only [MGraph.batchEnc, List.length_cons]
    omega

/-- **`P4TaskCaps` from history validity and edge-cap bound on `d.G₀`.** Every edge appearing in
`(update (d.state P) U _).UH`, `.D`, `updateReembSet`, and post-update `piTotal` walks lies in
`d.G₀.E` and hence below `eCap`. -/
theorem p4TaskCaps_of_valid {P : DSParams} {eCap : ℕ} {d : DSHist} {U : List Update}
    (hL : 1 ≤ P.L) (hVG₀ : d.G₀.IsValid) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hG₀E : ∀ e ∈ d.G₀.E, e < eCap)
    (hBV : d.G₀.BatchIsValid (d.flat ++ U))
    (hds : ∀ u ∈ d.flat ++ U, isDelOrSplit u) :
    P4TaskCaps P eCap d U := by
  set sp := canonicalSparsify P.impl
  set us := d.flat ++ U
  set k₀ := d.flat.length
  set q := d.q P
  have hq1 : 1 ≤ q := le_trans (by decide) (two_le_phaseBase _ _)
  have hSpec := canonicalSparsify_spec_absorb P.impl P.mMax
  have hInvAll := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds
  have hstate_eq : d.state P = runState (L := P.L) d.G₀ q sp us k₀ := by
    unfold DSHist.state
    exact (runState_append d.G₀ q sp d.flat U k₀ le_rfl).symm
  have hH_below : ∀ k ≤ us.length, ∀ e ∈ (runState (L := P.L) d.G₀ q sp us k).H.E, e < eCap := by
    intro k hk e he
    have hS := (hInvAll k hk).1
    have heG : e ∈ (d.G₀.applyBatch (us.take k)).E := hS.H_sub.2.1 he
    have hsub := applyBatch_E_subset_of_delOrSplit d.G₀ (us.take k)
      fun x hx => hds x (List.mem_of_mem_take hx)
    exact hG₀E e (hsub heG)
  have hG_below : ∀ k ≤ us.length, ∀ e ∈ (runState (L := P.L) d.G₀ q sp us k).G.E, e < eCap := by
    intro k hk e he
    have hS := (hInvAll k hk).1
    rw [hS.G_eq] at he
    have hsub := applyBatch_E_subset_of_delOrSplit d.G₀ (us.take k)
      fun x hx => hds x (List.mem_of_mem_take hx)
    exact hG₀E e (hsub he)
  have hlen : k₀ + U.length ≤ us.length := by simp [us, k₀]
  have hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi) := by
    intro i hi
    simp [us, k₀, List.getElem?_append_right (Nat.le_add_right _ _), List.getElem?_eq_getElem hi]
  have hrun := updateGo_run_eq (L := P.L) (q := q) (sparsify := sp) d.G₀ us U k₀ [] ∅ 0 hlen hmatch
  have hspec := update_batch_spec hVG₀ hL hq1 hGm₀ hSpec hBV hds hlen hmatch
  have hd'_eq : (⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P =
      runState (L := P.L) d.G₀ q sp us (k₀ + U.length) := by
    have hflat : (⟨d.G₀, d.Us ++ [U]⟩ : DSHist).flat = us := dsHist_flat_append d U
    have hlen_eq : us.length = k₀ + U.length := List.length_append
    unfold DSHist.state
    rw [hflat, hlen_eq]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. `UH` edges below `eCap`
    intro u' hu'
    rw [hstate_eq] at hu'
    have hUH_eq : (update (runState (L := P.L) d.G₀ q sp us k₀) U sp).UH =
        (List.range U.length).flatMap fun i =>
          (runStepOut (L := P.L) d.G₀ q sp us (k₀ + i)).UH := by
      unfold update; rw [hrun]; simp
    rw [hUH_eq, List.mem_flatMap] at hu'
    obtain ⟨i, hi, hu'i⟩ := hu'
    have hi' : i < U.length := List.mem_range.mp hi
    have hstep_eq : runStepOut (L := P.L) d.G₀ q sp us (k₀ + i) =
        step (runState (L := P.L) d.G₀ q sp us (k₀ + i)) (U[i]'hi') sp := by
      unfold runStepOut; rw [hmatch i hi']
    rw [hstep_eq] at hu'i
    have hst_next : (step (runState (L := P.L) d.G₀ q sp us (k₀ + i)) (U[i]'hi') sp).state =
        runState (L := P.L) d.G₀ q sp us (k₀ + i + 1) := by
      simp [runState, hmatch i hi']
    exact step_uh_edge_below (hds _ (List.mem_of_getElem? (hmatch i hi')))
      (hH_below (k₀ + i) (by omega))
      (hst_next ▸ hH_below (k₀ + i + 1) (by omega)) u' hu'i
  · -- 2. `D` edges below `eCap`
    intro e he
    rw [hstate_eq] at he
    have heH : e ∈ (update (runState (L := P.L) d.G₀ q sp us k₀) U sp).state.H.E :=
      hspec.2.2.2.1 he
    rw [hspec.1] at heH
    exact hH_below (k₀ + U.length) hlen e heH
  · -- 3. `updateReembSet` edges below `eCap`
    intro e he
    rw [hstate_eq] at he
    have heG := updateReembSet_subset_G (runState (L := P.L) d.G₀ q sp us k₀) U sp he
    rw [hspec.1] at heG
    exact hG_below (k₀ + U.length) hlen e heG
  · -- 4. post-update `piTotal` walk edges below `eCap`
    intro e he q_end hq_end
    rw [hd'_eq] at he hq_end
    have hEmb := (lemma_5_6 hVG₀ hL hq1 hGm₀ hSpec hBV hds hlen).2
    have hGeq := (hInvAll (k₀ + U.length) hlen).1.G_eq
    have he' : e ∈ (d.G₀.applyBatch (us.take (k₀ + U.length))).E := hGeq ▸ he
    have hwalk := hEmb.2 e he'
    exact hH_below (k₀ + U.length) hlen q_end.1 (walk_edges_in_H hwalk q_end hq_end)

/-- **`BatchWithinCaps` for `bundleCompStep` on a slot bundle with contiguous vertex range.**
When `B₀.vertices = Finset.range nB`, `BundleStepReady tr.cs B₀ tr.k ord ord' U`, and
`nB + batchSplitCount (bundleCompStep ...).1 ≤ vCap`, every update in the bundle step batch
respects `(vCap, eCap)`. -/
theorem batchWithinCaps_bundleCompStep {cs : CompLSFState} {B₀ : BundleState} {k nB vCap eCap : ℕ}
    {ord ord' : ℕ → List End} {U : List Update}
    (hReady : BundleStepReady cs B₀ k ord ord' U)
    (hRange : B₀.vertices = Finset.range nB)
    (hCap : nB + batchSplitCount (bundleCompStep cs B₀ k ord ord' U).1 ≤ vCap) :
    BatchWithinCaps vCap eCap (bundleCompStep cs B₀ k ord ord' U).1 := by
  rw [bundleCompStep_eq hReady] at hCap ⊢
  obtain ⟨⟨-, hbv, hwg, hds, -, -, -⟩, -⟩ := bundleRunsStep_spec hReady
  have hVr := bundleRunsStep_vertices_range hReady hRange
  refine batchWithinCaps_of_delOrSplit_V_lt B₀.graph (bundleRunsStep cs B₀ k ord' U).1
    hbv hds ?_
  intro v hv
  rw [← hwg] at hv
  change v ∈ (bundleRunsStep cs B₀ k ord' U).2.vertices at hv
  rw [hVr, Finset.mem_range] at hv
  omega

end

end MinCostFlow.SparseCore.Program
