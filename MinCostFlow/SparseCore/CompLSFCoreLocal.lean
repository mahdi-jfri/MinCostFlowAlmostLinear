module

public import MinCostFlow.SparseCore.CompLSFOrderedCore
public import MinCostFlow.Bundle.CoreLocal
public import MinCostFlow.SparseCore.SplitSpannerBuckets
import MinCostFlow.LSF.Lemma54Split
import MinCostFlow.SparseCore.CoreModel

/-!
# The ordered global core batch stays inside the components

`orderedCore_compLSFBatch` turns a batch of the component-wise LSF into an ordered batch of the
global core graph. This file builds the same batch and proves two more facts about it. First,
each core split splits a vertex `v` into `v` and a new root `v'` of the same component of the
initial graph: both lie in the vertex set of one component state after the batch. The reason is
that the new root takes a part of the forest tree of `v`, and every forest tree lies inside one
component. Second, every core deletion deletes an edge that the input batch deletes.

These facts make the count of bundle splits local: a component's
bundles split only at core splits inside the component, and there are at most as many such
splits as the component has new roots.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- Every split of the core batch splits a vertex `v` into `v` and `v'` that lie in the vertex
set of one component state of `cs`. -/
@[expose] def CompSplitsLocal (cs : CompLSFState) (UC : List Update) : Prop :=
  ∀ op ∈ UC, ∀ v v' St Sh, op = .split v v' St Sh →
    ∃ C ∈ components cs.G₀, v ∈ (cs.compSt C).G.V ∧ v' ∈ (cs.compSt C).G.V

/-- An update never removes a vertex. -/
theorem applyUpdate_V_subset (G : MGraph) (u : Update) : G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert => exact Finset.Subset.rfl
  | delete => exact Finset.Subset.rfl
  | split v v' St Sh => exact Finset.subset_insert _ _

/-- A batch never removes a vertex. -/
theorem applyBatch_V_subset (G : MGraph) (U : List Update) : G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u U ih => exact (applyUpdate_V_subset G u).trans (ih (G.applyUpdate u))

/-- The split vertex of a split of a valid batch is a vertex after the batch. -/
theorem split_mem_applyBatch_V {G : MGraph} {U : List Update} (hU : G.BatchIsValid U)
    {v v' : ℕ} {St Sh : Finset ℕ} (hop : Update.split v v' St Sh ∈ U) :
    v ∈ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => simp at hop
  | cons u U ih =>
    rcases List.mem_cons.mp hop with h | h
    · subst h
      exact applyBatch_V_subset _ U (applyUpdate_V_subset G _ hU.1.1)
    · exact ih hU.2 h

/-- The graph of a component state after one update is its graph with the projected update. -/
theorem compLSFStepSingle_compSt_G {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) {C : Finset ℕ}
    (hC : C ∈ components cs.G₀) :
    ((compLSFStepSingle cs u).compSt C).G =
      (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) := by
  have h := (compLSFBatch_compSt (U := [u]) hI ⟨hu, trivial⟩ hC).2.1
  simpa [projCompBatchG, compLSFBatch] using h

/-- The vertex set of a component state only grows along a batch. -/
theorem compLSFBatch_compSt_V_subset {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) {C : Finset ℕ}
    (hC : C ∈ components cs.G₀) :
    (cs.compSt C).G.V ⊆ ((compLSFBatch cs U).compSt C).G.V := by
  rw [(compLSFBatch_compSt hI hU hC).2.1]
  exact applyBatch_V_subset _ _

/-- The ends of a global forest edge lie in the vertex set of one component state. -/
private theorem compLSF_RF_edge_comp {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {e : ℕ} (he : e ∈ cs.RF.F.E) :
    ∃ C ∈ components cs.G₀, cs.RF.F.tail e ∈ (cs.compSt C).G.V ∧
      cs.RF.F.head e ∈ (cs.compSt C).G.V := by
  change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) at he
  obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp he
  have hRS := lsfInv_to_RS (hI.hCompLSF C hC).1
  have hsub := compLSF_RF_sub_comp hI hC
  have hends := hRS.1.1 e heC
  rw [hRS.2.1] at hends
  obtain ⟨ht, hh⟩ := hsub.2.2 e heC
  exact ⟨C, hC, ht ▸ hends.1, hh ▸ hends.2⟩

/-- The label of a vertex: the components whose state after the step contains it. -/
private noncomputable def compLabel (cs : CompLSFState) (w : ℕ) : Finset (Finset ℕ) :=
  open Classical in (components cs.G₀).filter fun C => w ∈ (cs.compSt C).G.V

/-- Two vertices of one component state have the same label. -/
private theorem compLabel_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) {a b : ℕ}
    (ha : a ∈ (cs.compSt C).G.V) (hb : b ∈ (cs.compSt C).G.V) :
    compLabel cs a = compLabel cs b := by
  classical
  have key : ∀ {x y : ℕ}, x ∈ (cs.compSt C).G.V → y ∈ (cs.compSt C).G.V →
      ∀ D ∈ components cs.G₀, x ∈ (cs.compSt D).G.V → y ∈ (cs.compSt D).G.V := by
    intro x y hx hy D hD hxD
    by_cases hCD : C = D
    · exact hCD ▸ hy
    · exact absurd hxD (Finset.disjoint_left.mp (hI.hV_disj C hC D hD hCD) hx)
  ext D
  simp only [compLabel, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, key ha hb D h.1 h.2⟩, fun h => ⟨h.1, key hb ha D h.1 h.2⟩⟩

/-- A vertex with the label of a vertex of a component state lies in that state. -/
private theorem mem_of_compLabel_eq {cs : CompLSFState} {C : Finset ℕ}
    (hC : C ∈ components cs.G₀) {a b : ℕ} (ha : a ∈ (cs.compSt C).G.V)
    (h : compLabel cs a = compLabel cs b) : b ∈ (cs.compSt C).G.V := by
  classical
  have hm : C ∈ compLabel cs a := Finset.mem_filter.mpr ⟨hC, ha⟩
  rw [h] at hm
  exact (Finset.mem_filter.mp hm).2

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
  · have hKE : cs'.RF.F.E ⊆ K.E := by
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

/-- The global forest is labeled by the components after the step. -/
private theorem compLSF_forestLabeled {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    ForestLabeled (compLabel (compLSFStepSingle cs u)) cs.RF.F := by
  have hI' := compLSFInv_step hI hu
  intro e he
  obtain ⟨C, hC, ht, hh⟩ := compLSF_RF_edge_comp hI he
  have hsub := compLSFBatch_compSt_V_subset (U := [u]) hI ⟨hu, trivial⟩ hC
  exact compLabel_eq hI' hC (hsub ht) (hsub hh)

/-- An input split splits a vertex into two vertices of one component state after the step. -/
private theorem compLSF_inputSplit_labeled {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    ∀ v v' St Sh, u = .split v v' St Sh →
      compLabel (compLSFStepSingle cs u) v = compLabel (compLSFStepSingle cs u) v' := by
  intro v v' St Sh hsplit
  subst hsplit
  have hI' := compLSFInv_step hI hu
  have hv : v ∈ cs.G.V := hu.1
  rw [← hI.hV_eq] at hv
  obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
  have hG := compLSFStepSingle_compSt_G hI hu hC
  have hmem : v ∈ ((compLSFStepSingle cs (.split v v' St Sh)).compSt C).G.V ∧
      v' ∈ ((compLSFStepSingle cs (.split v v' St Sh)).compSt C).G.V := by
    rw [hG]
    simp only [projCompUpdateG, hvC, ↓reduceIte]
    exact ⟨Finset.mem_insert_of_mem hvC, Finset.mem_insert_self _ _⟩
  exact compLabel_eq hI' hC hmem.1 hmem.2

private theorem card_applyBatch_splits' {G : MGraph} {U : List Update} (h : G.BatchIsValid U) :
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

/-- One update of the component-wise LSF gives an ordered batch of the global core graph
(`orderedCore_compLSFStep`). Its splits stay inside one component state after the step, and its
deletion is the input deletion. -/
theorem orderedCore_compLSFStep_local {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} {β : ℕ} {ρ : Rotation cs.G} {σ : Rotation (cs.G.applyUpdate u)}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) (hr : RotationStep β u ρ σ)
    (hβ : 2 ≤ β) :
    let cs' := compLSFStepSingle cs u
    ∃ hI' : CompLSFInv C_lsst ℓ₀ cs', ∃ UC : List Update,
      OrderedCoreBatch β (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI))
        (coreRotation (L := cs'.lsf) σ hI'.hG_val (compLSF_RF_isRSF hI')) UC ∧
      batchSplitCount UC = (cs'.RF.R \ cs.RF.R).card ∧ UC.countP deleteTag ≤ 1 ∧
      CompSplitsLocal cs' UC ∧ DeletesOf UC u ∧
      ∀ e, u = .delete e → e ∉ cs.RF.F.E → Update.delete e ∈ UC := by
  intro cs'
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF := compLSF_RF_isRSF hI
  have hF' : cs'.RF.IsRootedSpanningForestOf (cs.G.applyUpdate u) := compLSF_RF_isRSF hI'
  have hH : (cs.G.applyUpdate u).IsValid := hI'.hG_val
  have hR : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  obtain ⟨hK, hKG, hsub, hKV⟩ := compLSF_forestAfterInput hI hu
  have hlab := compLSF_forestLabeled hI hu
  have hspl := compLSF_inputSplit_labeled hI hu
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
  obtain ⟨mid, hm, hmidF, _, hmR, U₀, h₀, _, hd₀, hl₀, hdel₀, hin₀⟩ :=
    orderedCore_input_labeled (L := cs.lsf) (last := L'') ρ σ hI.hG_val hH hF hL'' hu hr hβ hR
      hK hKG hFcK hlab hspl
  have hCut : cuts.foldl eraseForestEdge mid.F.F = L''.F.F := by
    rw [hmidF]
    rfl
  have hMem : ∀ e ∈ cuts, e ∈ mid.F.F.E := by
    intro e he
    rw [hmidF]
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp he)).1
  have hlabMid : ForestLabeled (compLabel cs') mid.F.F := by
    rw [hmidF]
    exact hlab.forestAfterInput hspl
  obtain ⟨U₁, h₁, _, hd₁, hl₁⟩ := orderedCore_releases_labeled σ hH cuts hm hL'' hmR hCut hMem
    (Finset.nodup_toList _) hβ hlabMid
  have hb := h₀.append h₁
  have hb' := hb.congr_lsf (L' := cs'.lsf) σ hH hL'' hF' rfl hEqF
  refine ⟨hI', U₀ ++ U₁, hb', ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hv, hEq, _⟩ := hb
    have hc := card_applyBatch_splits' hv
    have hV := congrArg Finset.card hEq.1
    change cs'.RF.R.card = _ at hV
    change _ = cs.RF.R.card + batchSplitCount (U₀ ++ U₁) at hc
    rw [Finset.card_sdiff_of_subset hR, hV.trans hc, Nat.add_sub_cancel_left]
  · simpa only [List.countP_append, hd₁, Nat.add_zero] using hd₀
  · intro op hop v v' St Sh hop'
    have hl : compLabel cs' v = compLabel cs' v' := by
      rcases List.mem_append.mp hop with h | h
      · exact hl₀ op h v v' St Sh hop'
      · exact hl₁ op h v v' St Sh hop'
    obtain ⟨hv, hEq, _⟩ := hb'
    have hvV : v ∈ cs'.G.V := by
      have h1 := split_mem_applyBatch_V hv (hop' ▸ hop)
      rw [← hEq.1] at h1
      exact (compLSF_RF_isRSF hI').2.2.1 h1
    rw [← hI'.hV_eq] at hvV
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hvV
    exact ⟨C, hC, hvC, mem_of_compLabel_eq hC hvC hl⟩
  · intro op hop e hop'
    rcases List.mem_append.mp hop with h | h
    · exact hdel₀ op h e hop'
    · have hz := List.countP_eq_zero.mp hd₁ op h
      rw [hop'] at hz
      exact absurd rfl hz
  · intro e hu he
    exact List.mem_append_left _ (hin₀ e hu he)

private theorem card_sdiff_trans'' {A B C : Finset ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    (C \ A).card = (C \ B).card + (B \ A).card := by
  rw [Finset.card_sdiff_of_subset h₁, Finset.card_sdiff_of_subset h₂,
    Finset.card_sdiff_of_subset (h₁.trans h₂)]
  have := Finset.card_le_card h₁
  have := Finset.card_le_card h₂
  omega

/-- A batch of the component-wise LSF gives an ordered batch of the global core graph
(`orderedCore_compLSFBatch`). Every core split splits a vertex into two vertices of one component
state after the batch, and every core deletion deletes an edge that the batch deletes. -/
theorem orderedCore_compLSFBatch_local {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {G : MGraph}
    {U : List Update} {β : ℕ} {ρ : Rotation G} {σ : Rotation (G.applyBatch U)}
    (hrot : RotationBatch β U ρ σ) (hβ : 2 ≤ β) (hU : G.BatchIsValid U) (cs : CompLSFState)
    (hS : cs.G = G) (hI : CompLSFInv C_lsst ℓ₀ cs) :
    let cs' := compLSFBatch cs U
    ∃ he : cs'.G = G.applyBatch U, ∃ hI' : CompLSFInv C_lsst ℓ₀ cs', ∃ UC : List Update,
      OrderedCoreBatch β
        (coreRotation (L := cs.lsf) (hS.symm ▸ ρ) hI.hG_val (compLSF_RF_isRSF hI))
        (coreRotation (L := cs'.lsf) (he.symm ▸ σ) hI'.hG_val (compLSF_RF_isRSF hI')) UC ∧
      batchSplitCount UC = (cs'.RF.R \ cs.RF.R).card ∧ UC.countP deleteTag ≤ U.length ∧
      CompSplitsLocal cs' UC ∧ (∀ op ∈ UC, ∀ e, op = .delete e → e ∈ batchDeletes U) ∧
      (∀ e ∈ batchDeletes U, e ∈ (coreGraph cs.G cs.lsf).E → Update.delete e ∈ UC) := by
  induction hrot generalizing cs with
  | @nil G ρ σ hr =>
    subst G
    refine ⟨rfl, hI, [], OrderedCoreBatch.of_isRotated _ _ hr,
      by simp [batchSplitCount, compLSFBatch], by simp, ?_, ?_, ?_⟩
    · intro op hop
      simp at hop
    · intro op hop
      simp at hop
    · intro e he
      simp [mem_batchDeletes_iff] at he
  | @cons G u rest ρ ρ' σ hs _ ih =>
    subst G
    obtain ⟨hI₀, V₀, h₀, hc₀, hd₀, hl₀, hdel₀, hin₀⟩ := orderedCore_compLSFStep_local hI hU.1 hs hβ
    obtain ⟨he₁, hI₁, V₁, h₁, hc₁, hd₁, hl₁, hdel₁, hin₁⟩ :=
      ih hU.2 (compLSFStepSingle cs u) rfl hI₀
    have hR₀ : cs.RF.R ⊆ (compLSFStepSingle cs u).RF.R :=
      (compLSFBatch_decremental (U := [u]) hI ⟨hU.1, trivial⟩).2
    have hR₁ := (compLSFBatch_decremental (U := rest) hI₀ hU.2).2
    refine ⟨he₁, hI₁, V₀ ++ V₁, h₀.append h₁, ?_, ?_, ?_, ?_, ?_⟩
    · change batchSplitCount (V₀ ++ V₁) =
        ((compLSFBatch (compLSFStepSingle cs u) rest).RF.R \ cs.RF.R).card
      rw [batchSplitCount_append, card_sdiff_trans'' hR₀ hR₁, hc₀, hc₁, Nat.add_comm]
    · rw [List.countP_append, List.length_cons]
      omega
    · intro op hop v v' St Sh hop'
      rcases List.mem_append.mp hop with h | h
      · obtain ⟨C, hC, hv, hv'⟩ := hl₀ op h v v' St Sh hop'
        have hsub := compLSFBatch_compSt_V_subset (U := rest) hI₀ hU.2 hC
        refine ⟨C, ?_, hsub hv, hsub hv'⟩
        rw [compLSFBatch_G₀]
        exact hC
      · exact hl₁ op h v v' St Sh hop'
    · intro op hop e hop'
      rw [mem_batchDeletes_iff]
      rcases List.mem_append.mp hop with h | h
      · exact ⟨u, List.mem_cons_self, hdel₀ op h e hop'⟩
      · obtain ⟨w, hw, hwe⟩ := (mem_batchDeletes_iff _ _).mp (hdel₁ op h e hop')
        exact ⟨w, List.mem_cons_of_mem _ hw, hwe⟩
    · intro e he heC
      have heC' := Finset.mem_sdiff.mp heC
      by_cases hu : u = .delete e
      · exact List.mem_append_left _ (hin₀ e hu heC'.2)
      · obtain ⟨w, hw, rfl⟩ := (mem_batchDeletes_iff _ _).mp he
        rcases List.mem_cons.mp hw with hw | hw
        · exact absurd hw.symm hu
        · have hrest : e ∈ batchDeletes rest := (mem_batchDeletes_iff _ _).mpr ⟨_, hw, rfl⟩
          have hG1 : e ∈ (compLSFStepSingle cs u).G.E := by
            change e ∈ (cs.G.applyUpdate u).E
            cases u with
            | insert f a b => exact Finset.mem_insert_of_mem heC'.1
            | delete f =>
              refine Finset.mem_erase.mpr ⟨fun hfe => hu ?_, heC'.1⟩
              rw [hfe]
            | split => exact heC'.1
          have hF1 : e ∉ (compLSFStepSingle cs u).RF.F.E := fun h =>
            heC'.2 ((compLSFBatch_decremental (U := [u]) hI ⟨hU.1, trivial⟩).1 h)
          exact List.mem_append_right _ (hin₁ e hrest (Finset.mem_sdiff.mpr ⟨hG1, hF1⟩))

end MinCostFlow.SparseCore
