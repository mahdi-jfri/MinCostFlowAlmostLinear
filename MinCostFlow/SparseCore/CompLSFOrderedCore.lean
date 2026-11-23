module

public import MinCostFlow.Bundle.CoreCongr
public import MinCostFlow.Bundle.CoreInput
public import MinCostFlow.Bundle.CoreReleases
public import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.LSF.Lemma54Split

/-!
# The ordered global core of the component-wise LSFs

The bundle repair of Lemma 5.17 orders the ends at each core vertex by the tour of its forest
component, with the input rotation. The formalization runs one LSF per component of the
initial graph. Its global forest `cs.RF` is the union of the component forests, with the
endpoints of the current graph. The ordered core lemmas hold for any rooted spanning
forest (`orderedCore_input`, `orderedCore_releases`). This file checks their hypotheses for one
update of the component-wise LSF. The result is an ordered batch of the global core graph with
one split per new root and at most one deletion (paper Lemma 5.14, page 22).

The global forest records the endpoints of the current graph. An insertion changes them at the
new edge name, which is no forest edge. So the forest after the step agrees with the factored
forest only on its edges, and `OrderedCoreBatch.congr_lsf` closes the gap.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- A rooted spanning forest stays one when the forest is replaced by one that agrees with it on
its edges. -/
theorem isRootedSpanningForestOf_congr {G : MGraph} {RF RF' : RootedForest}
    (h : RF.IsRootedSpanningForestOf G) (hR : RF.R = RF'.R) (hEq : GraphEq RF.F RF'.F) :
    RF'.IsRootedSpanningForestOf G := by
  have hsub : RF.F.IsSubgraph RF'.F :=
    ⟨hEq.1.symm.le, hEq.2.1.symm.le, fun e he => by
      have := hEq.2.2 e (hEq.2.1 ▸ he)
      exact ⟨this.1.symm, this.2.symm⟩⟩
  refine ⟨isForest_subgraph h.1 hsub (graphEq_isValid hEq h.1.1), hEq.1 ▸ h.2.1, hR ▸ h.2.2.1,
    fun v hv => ?_, ?_⟩
  · obtain ⟨r, ⟨hr, hc⟩, huniq⟩ := h.2.2.2.1 v hv
    refine ⟨r, ⟨hR ▸ hr, (connected_iff_of_graphEq hEq).mp hc⟩, fun r' ⟨hr', hc'⟩ => ?_⟩
    exact huniq r' ⟨hR ▸ hr', (connected_iff_of_graphEq hEq).mpr hc'⟩
  · obtain ⟨hV, hE, hend⟩ := h.2.2.2.2
    refine ⟨hEq.1 ▸ hV, hEq.2.1 ▸ hE, fun e he => ?_⟩
    have he' : e ∈ RF.F.E := hEq.2.1 ▸ he
    obtain ⟨h1, h2⟩ := hEq.2.2 e he'
    obtain ⟨h3, h4⟩ := hend e he'
    exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩

private theorem card_applyBatch_splits {G : MGraph} {U : List Update} (h : G.BatchIsValid U) :
    (G.applyBatch U).V.card = G.V.card + batchSplitCount U := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch, batchSplitCount]
  | cons u U ih =>
    change ((G.applyUpdate u).applyBatch U).V.card = G.V.card + batchSplitCount (u :: U)
    rw [ih h.2]
    cases u with
    | insert => simp [MGraph.applyUpdate, batchSplitCount, isSplit]
    | delete => simp [MGraph.applyUpdate, batchSplitCount, isSplit]
    | split v v' St Sh =>
      have hV : (G.applyUpdate (.split v v' St Sh)).V.card = G.V.card + 1 :=
        Finset.card_insert_of_notMem h.1.2.1
      simp [hV, batchSplitCount, List.countP_cons, isSplit, Nat.add_right_comm G.V.card,
        Nat.add_assoc]

/-- The forest after the input edit of one component-wise LSF update contains the forest after
the update, and it is a forest of the updated graph. -/
private theorem compLSF_forestAfterInput {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    let K := forestAfterInput cs.RF.F u
    let cs' := compLSFStepSingle cs u
    K.IsForest ∧ (cs.G.applyUpdate u).IsSubgraph K ∧ K.IsSubgraph cs'.RF.F ∧
      K.V = cs'.RF.F.V := by
  intro K cs'
  have hF := compLSF_RF_isRSF hI
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF' := compLSF_RF_isRSF hI'
  have hdec := compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩
  have hFE : cs'.RF.F.E ⊆ cs.RF.F.E := hdec.1
  have hFG : cs.RF.F.E ⊆ cs.G.E := hF.2.2.2.2.2.1
  have hFG' : cs'.RF.F.E ⊆ cs'.G.E := hF'.2.2.2.2.2.1
  have hFV : cs.RF.F.V = cs.G.V := hF.2.1
  have hFV' : cs'.RF.F.V = cs'.G.V := hF'.2.1
  -- The forest after the input edit as a subgraph of the updated graph.
  have hKG : (cs.G.applyUpdate u).IsSubgraph K := by
    cases u with
    | insert e a b =>
      refine ⟨hFV.le, hFG.trans (Finset.subset_insert _ _), fun f hf => ?_⟩
      have hfe : f ≠ e := fun h => hu.1 (h ▸ hFG hf)
      change cs.G.tail f = Function.update cs.G.tail e a f ∧
        cs.G.head f = Function.update cs.G.head e b f
      simp [Function.update_of_ne hfe]
    | delete e =>
      exact ⟨hFV.le, Finset.erase_subset_erase e hFG, fun f _ => ⟨rfl, rfl⟩⟩
    | split v v' St Sh =>
      refine ⟨?_, hFG, fun f _ => ⟨rfl, rfl⟩⟩
      change insert v' cs.RF.F.V ⊆ insert v' cs.G.V
      rw [hFV]
  have hKV : K.V = cs'.G.V := by
    cases u with
    | insert => exact hFV
    | delete => exact hFV
    | split v v' St Sh =>
      change insert v' cs.RF.F.V = insert v' cs.G.V
      rw [hFV]
  refine ⟨?_, hKG, ?_, hKV.trans hFV'.symm⟩
  · cases u with
    | insert => exact hF.1
    | delete e => exact isForest_eraseEdge hF.1 e
    | split v v' St Sh =>
      exact applyUpdate_split_isForest hF.1 (hFV ▸ hu.1) (hFV ▸ hu.2.1) St Sh
  · -- The forest after the update lies in the forest after the input edit.
    have hKE : cs'.RF.F.E ⊆ K.E := by
      cases u with
      | insert => exact hFE
      | split => exact hFE
      | delete e =>
        intro f hf
        refine Finset.mem_erase.mpr ⟨?_, hFE hf⟩
        rintro rfl
        have := hFG' hf
        change f ∈ cs.G.E.erase f at this
        simp at this
    refine ⟨hFV'.trans hKV.symm |>.le, hKE, fun f hf => ?_⟩
    have hfK := hKE hf
    obtain ⟨h1, h2⟩ := hKG.2.2 f hfK
    exact ⟨h1.symm, h2.symm⟩

/-- One update of the component-wise LSF gives an ordered batch of the global core graph, for
an input with split bound `β ≥ 2`. It has one split per new root
(paper Lemma 5.14, page 22) and at most one deletion. -/
theorem orderedCore_compLSFStep {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    {β : ℕ} {ρ : Rotation cs.G} {σ : Rotation (cs.G.applyUpdate u)}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) (hr : RotationStep β u ρ σ)
    (hβ : 2 ≤ β) :
    let cs' := compLSFStepSingle cs u
    ∃ hI' : CompLSFInv C_lsst ℓ₀ cs', ∃ UC : List Update,
      OrderedCoreBatch β (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI))
        (coreRotation (L := cs'.lsf) σ hI'.hG_val (compLSF_RF_isRSF hI')) UC ∧
      batchSplitCount UC = (cs'.RF.R \ cs.RF.R).card ∧ UC.countP deleteTag ≤ 1 := by
  intro cs'
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF := compLSF_RF_isRSF hI
  have hF' : cs'.RF.IsRootedSpanningForestOf (cs.G.applyUpdate u) := compLSF_RF_isRSF hI'
  have hH : (cs.G.applyUpdate u).IsValid := hI'.hG_val
  have hR : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  obtain ⟨hK, hKG, hsub, hKV⟩ := compLSF_forestAfterInput hI hu
  let K := forestAfterInput cs.RF.F u
  let cuts := (K.E \ cs'.RF.F.E).toList
  let Fc := cuts.foldl eraseForestEdge K
  have hFcE : Fc.E = cs'.RF.F.E := by
    simp only [Fc, cuts, foldl_eraseForestEdge, Finset.toList_toFinset]
    exact Finset.sdiff_sdiff_eq_self hsub.2.1
  have hFcK : K.IsSubgraph Fc := by
    refine ⟨?_, ?_, fun _ _ => by simp [Fc, foldl_eraseForestEdge]⟩
    · simp only [Fc, foldl_eraseForestEdge]
      exact Finset.Subset.rfl
    · simp only [Fc, foldl_eraseForestEdge]
      exact Finset.sdiff_subset
  have hEqF : GraphEq Fc cs'.RF.F := by
    refine ⟨?_, hFcE, fun f hf => ?_⟩
    · simp only [Fc, foldl_eraseForestEdge]
      exact hKV
    · have hf' : f ∈ cs'.RF.F.E := hFcE ▸ hf
      obtain ⟨h1, h2⟩ := hsub.2.2 f hf'
      simp only [Fc, foldl_eraseForestEdge]
      exact ⟨h1.symm, h2.symm⟩
  let L'' : LSF := ⟨cs'.lsf.T, ⟨Fc, cs'.RF.R⟩, cs'.lsf.wstr⟩
  have hL'' : L''.F.IsRootedSpanningForestOf (cs.G.applyUpdate u) :=
    isRootedSpanningForestOf_congr hF' rfl (graphEq_symm hEqF)
  obtain ⟨mid, hm, hmidF, _, hmR, U₀, h₀, _, hd₀⟩ :=
    orderedCore_input (L := cs.lsf) (last := L'') ρ σ hI.hG_val hH hF hL'' hu hr hβ hR hK hKG
      hFcK
  have hCut : cuts.foldl eraseForestEdge mid.F.F = L''.F.F := by
    rw [hmidF]
    rfl
  have hMem : ∀ e ∈ cuts, e ∈ mid.F.F.E := by
    intro e he
    rw [hmidF]
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp he)).1
  obtain ⟨U₁, h₁, _, hd₁⟩ := orderedCore_releases σ hH cuts hm hL'' hmR hCut hMem
    (Finset.nodup_toList _) hβ
  have hb := h₀.append h₁
  refine ⟨hI', U₀ ++ U₁, hb.congr_lsf σ hH hL'' hF' rfl hEqF, ?_, ?_⟩
  · obtain ⟨hv, hEq, _⟩ := hb
    have hc := card_applyBatch_splits hv
    have hV := congrArg Finset.card hEq.1
    change cs'.RF.R.card = _ at hV
    change _ = cs.RF.R.card + batchSplitCount (U₀ ++ U₁) at hc
    rw [Finset.card_sdiff_of_subset hR, hV.trans hc, Nat.add_sub_cancel_left]
  · simpa only [List.countP_append, hd₁, Nat.add_zero] using hd₀

private theorem card_sdiff_trans' {A B C : Finset ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    (C \ A).card = (C \ B).card + (B \ A).card := by
  rw [Finset.card_sdiff_of_subset h₁, Finset.card_sdiff_of_subset h₂,
    Finset.card_sdiff_of_subset (h₁.trans h₂)]
  have := Finset.card_le_card h₁
  have := Finset.card_le_card h₂
  omega

/-- A batch of the component-wise LSF gives an ordered batch of the global core graph, for an
input with split bound `β ≥ 2`. Its splits are the new roots and it
has at most one deletion per input update. -/
theorem orderedCore_compLSFBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {G : MGraph} {U : List Update}
    {β : ℕ} {ρ : Rotation G} {σ : Rotation (G.applyBatch U)} (hrot : RotationBatch β U ρ σ)
    (hβ : 2 ≤ β) (hU : G.BatchIsValid U) (cs : CompLSFState) (hS : cs.G = G)
    (hI : CompLSFInv C_lsst ℓ₀ cs) :
    let cs' := compLSFBatch cs U
    ∃ he : cs'.G = G.applyBatch U, ∃ hI' : CompLSFInv C_lsst ℓ₀ cs', ∃ UC : List Update,
      OrderedCoreBatch β
        (coreRotation (L := cs.lsf) (hS.symm ▸ ρ) hI.hG_val (compLSF_RF_isRSF hI))
        (coreRotation (L := cs'.lsf) (he.symm ▸ σ) hI'.hG_val (compLSF_RF_isRSF hI')) UC ∧
      batchSplitCount UC = (cs'.RF.R \ cs.RF.R).card ∧ UC.countP deleteTag ≤ U.length := by
  induction hrot generalizing cs with
  | @nil G ρ σ hr =>
    subst G
    exact ⟨rfl, hI, [], OrderedCoreBatch.of_isRotated _ _ hr,
      by simp [batchSplitCount, compLSFBatch], by simp⟩
  | @cons G u rest ρ ρ' σ hs _ ih =>
    subst G
    obtain ⟨hI₀, V₀, h₀, hc₀, hd₀⟩ := orderedCore_compLSFStep hI hU.1 hs hβ
    obtain ⟨he₁, hI₁, V₁, h₁, hc₁, hd₁⟩ := ih hU.2 (compLSFStepSingle cs u) rfl hI₀
    have hR₀ : cs.RF.R ⊆ (compLSFStepSingle cs u).RF.R :=
      (compLSFBatch_decremental (U := [u]) hI ⟨hU.1, trivial⟩).2
    have hR₁ := (compLSFBatch_decremental (U := rest) hI₀ hU.2).2
    refine ⟨he₁, hI₁, V₀ ++ V₁, h₀.append h₁, ?_, ?_⟩
    · change batchSplitCount (V₀ ++ V₁) =
        ((compLSFBatch (compLSFStepSingle cs u) rest).RF.R \ cs.RF.R).card
      rw [batchSplitCount_append, card_sdiff_trans' hR₀ hR₁, hc₀, hc₁, Nat.add_comm]
    · rw [List.countP_append, List.length_cons]
      omega

end MinCostFlow.SparseCore
