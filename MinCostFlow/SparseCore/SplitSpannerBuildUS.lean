module

public import MinCostFlow.SparseCore.SplitSpannerBuckets

import Mathlib.Tactic.Linarith

/-!
# Sparsified core-graph batch construction (`buildUSReinsert` and `buildUS`)

Constructs and verifies the update batch `U_S` moving `S_prev` to `targetE` over `cs_new.RF.R`
with independent endpoint splits and re-insertion of `D_reins` edges (`jtree.tex` line 425),
together with surviving-edge insertion propagation (`buildUSReinsert_noReinsertPropagates`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-- Construct the update batch `U_S` moving `S_prev` to `targetE` over vertex set `cs_new.RF.R`,
splitting endpoints `(St, Sh)` independently and deleting + reinserting surviving edges in
`D_reins` (matching `jtree.tex` line 425 when `D_reins = D_total`). -/
noncomputable def buildUSReinsert (cs_old : CompLSFState) (U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) : List Update :=
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  let delEdges := S_prev.E \ keepSet
  let insEdges := targetE \ keepSet
  let newRs := (cs_new.RF.R \ cs_old.RF.R).toList
  let delList := delEdges.toList.map Update.delete
  let splitList := newRs.map fun r' =>
    Update.split (compBatchParentRoot cs_old U r') r'
      (keepSet.filter fun e => cs_new.RF.root (cs_new.G.tail e) = r')
      (keepSet.filter fun e => cs_new.RF.root (cs_new.G.head e) = r')
  let insList := insEdges.toList.map fun e =>
    Update.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e))
  delList ++ splitList ++ insList

/-- Legacy non-reinserting specialization of `buildUSReinsert` with `D_reins = ∅`. -/
@[reducible] noncomputable def buildUS (cs_old : CompLSFState) (U : List Update)
    (cs_new : CompLSFState) (S_prev : MGraph) (targetE : Finset ℕ) : List Update :=
  buildUSReinsert cs_old U cs_new S_prev targetE ∅

lemma mem_split_of_map {par : ℕ → ℕ} {Pt Ph : ℕ → ℕ → Prop}
    [∀ r e, Decidable (Pt r e)] [∀ r e, Decidable (Ph r e)]
    {E_k : Finset ℕ} {rs : List ℕ} {e : ℕ} {a b : ℕ}
    (h : Update.insert e a b ∈
      rs.map (fun r' => Update.split (par r') r' (E_k.filter (Pt r')) (E_k.filter (Ph r')))) :
    False := by
  rw [List.mem_map] at h
  rcases h with ⟨_, _, hEq⟩
  cases hEq

lemma noBatchReinsert_of_ins_fresh {G : MGraph} {delEdges insEdges : Finset ℕ}
    {newRs : List ℕ} {par : ℕ → ℕ} {Pt Ph : ℕ → ℕ → Prop}
    [∀ r e, Decidable (Pt r e)] [∀ r e, Decidable (Ph r e)]
    {ends : ℕ → ℕ × ℕ} {E_k : Finset ℕ}
    (hFresh : ∀ e ∈ insEdges, e ∉ G.E) :
    NoBatchReinsert G
      (delEdges.toList.map Update.delete ++
        newRs.map (fun r' => Update.split (par r') r' (E_k.filter (Pt r')) (E_k.filter (Ph r'))) ++
        insEdges.toList.map (fun e => Update.insert e (ends e).1 (ends e).2)) := by
  intro e heG u hu hIns
  simp only [List.mem_append] at hu
  rcases hu with (hd | hs) | hi
  · rw [List.mem_map] at hd
    rcases hd with ⟨_, _, rfl⟩
    exact hIns
  · rw [List.mem_map] at hs
    rcases hs with ⟨_, _, rfl⟩
    exact hIns
  · rw [List.mem_map] at hi
    rcases hi with ⟨e', he', rfl⟩
    simp only [Update.Inserts] at hIns
    subst hIns
    exact hFresh e' (Finset.mem_toList.mp he') heG

private lemma not_mem_applyBatch_of_not_insert {G : MGraph} {U : List Update} {e : ℕ}
    (hnotin : e ∉ G.E) (hnr : ∀ x ∈ U, ¬ x.Inserts e) :
    e ∉ (G.applyBatch U).E := by
  induction U generalizing G with
  | nil => exact hnotin
  | cons x xs ih =>
    simp only [MGraph.applyBatch, List.foldl_cons]
    refine ih ?_ (fun y hy => hnr y (List.mem_cons_of_mem _ hy))
    cases x with
    | delete e' => simp [MGraph.applyUpdate, hnotin]
    | split _ _ _ _ => exact hnotin
    | insert e' _ _ =>
      have hne : e' ≠ e := fun h => hnr (.insert e' _ _) List.mem_cons_self
        (by simpa [Update.Inserts] using h)
      simp [MGraph.applyUpdate, hne.symm, hnotin]

lemma mem_batchDeletes_of_inserts {G : MGraph} {U : List Update} (hB : G.BatchIsValid U)
    {e : ℕ} (he : e ∈ G.E) (hIns : ∃ u ∈ U, u.Inserts e) :
    e ∈ batchDeletes U := by
  induction U generalizing G with
  | nil => rcases hIns with ⟨_, h, _⟩; cases h
  | cons u rest ih =>
    rw [MGraph.BatchIsValid] at hB
    obtain ⟨hu, hB_rest⟩ := hB
    rcases hIns with ⟨u', hu', hIu'⟩
    rcases List.mem_cons.mp hu' with rfl | hrest
    · cases u' with
      | insert e' a b =>
        simp only [Update.Inserts] at hIu'; subst hIu'
        exact absurd he hu.1
      | delete _ => cases hIu'
      | split _ _ _ _ => cases hIu'
    · by_cases hdel : u = .delete e
      · exact (mem_batchDeletes_iff _ _).mpr ⟨u, List.mem_cons_self, hdel⟩
      · have he' : e ∈ (G.applyUpdate u).E := by
          cases u with
          | delete e₀ =>
            have hne : e ≠ e₀ := fun h => hdel (by rw [h])
            exact Finset.mem_erase.mpr ⟨hne, he⟩
          | insert e₀ _ _ => exact Finset.mem_insert_of_mem he
          | split _ _ _ _ => exact he
        obtain ⟨x, hx, rfl⟩ := (mem_batchDeletes_iff _ _).mp (ih hB_rest he' ⟨u', hrest, hIu'⟩)
        exact (mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_cons_of_mem _ hx, rfl⟩

lemma not_mem_applyBatch_of_delete_not_insert {G : MGraph} {U : List Update} {e : ℕ}
    (hNoIns : ∀ u ∈ U, ¬ u.Inserts e) (hDel : ∃ u ∈ U, u = .delete e) :
    e ∉ (G.applyBatch U).E := by
  induction U generalizing G with
  | nil => rcases hDel with ⟨_, hm, _⟩; simp at hm
  | cons u rest ih =>
    have hNoRest : ∀ x ∈ rest, ¬ x.Inserts e := fun x hx => hNoIns x (List.mem_cons_of_mem _ hx)
    rcases hDel with ⟨u', hu', hEq⟩
    simp only [MGraph.applyBatch, List.foldl_cons]
    rcases List.mem_cons.mp hu' with rfl | hrest
    · subst hEq
      exact not_mem_applyBatch_of_not_insert (by simp [MGraph.applyUpdate]) hNoRest
    · exact ih hNoRest ⟨u', hrest, hEq⟩

lemma buildUSReinsert_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_val : S_prev.IsValid) (hS_V : S_prev.V = cs_old.RF.R)
    (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ}
    (hTgt_sub : targetE ⊆ (compLSFBatch cs_old U).G.E \ (compLSFBatch cs_old U).RF.F.E)
    (D_reins : Finset ℕ) :
    let cs_new := compLSFBatch cs_old U
    let U_S := buildUSReinsert cs_old U cs_new S_prev targetE D_reins
    let S_next := S_prev.applyBatch U_S
    let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
    S_prev.BatchIsValid U_S ∧
    S_next.IsValid ∧
    S_next.V = cs_new.RF.R ∧
    S_next.E = targetE ∧
    (∀ e ∈ S_next.E,
      S_next.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_next.head e = cs_new.RF.root (cs_new.G.head e)) ∧
    (coreGraph cs_new.G cs_new.lsf).IsSubgraph S_next ∧
    U_S.length = (S_prev.E \ keepSet).card + (cs_new.RF.R \ cs_old.RF.R).card + (targetE \ keepSet).card ∧
    (D_reins = ∅ → NoBatchReinsert cs_old.G U → NoBatchReinsert S_prev U_S) := by
  intro cs_new U_S S_next keepSet
  have hI_new := compLSFBatch_inv hI hBU
  have hcs_new_G : cs_new.G = cs_old.G.applyBatch U := compLSFBatch_G cs_old U
  have hR_sub : cs_old.RF.R ⊆ cs_new.RF.R := (compLSFBatch_decremental hI hBU).2
  have hRF_old := compLSF_RF_isRSF hI
  have hRF_new := compLSF_RF_isRSF hI_new
  obtain ⟨hProjV, hProjOld, hProjEdge, hProjConn⟩ := compBatchStepProj_spec hI hBU
  let delEdges := S_prev.E \ keepSet
  let insEdges := targetE \ keepSet
  let newRs := (cs_new.RF.R \ cs_old.RF.R).toList
  let delList := delEdges.toList.map Update.delete
  let splitList := newRs.map fun r' =>
    Update.split (compBatchParentRoot cs_old U r') r'
      (keepSet.filter fun e => cs_new.RF.root (cs_new.G.tail e) = r')
      (keepSet.filter fun e => cs_new.RF.root (cs_new.G.head e) = r')
  let insList := insEdges.toList.map fun e =>
    Update.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e))
  have hDel_spec := applyUpdate_delete_list_spec hS_val (Finset.nodup_toList delEdges)
    (fun e he => Finset.sdiff_subset (Finset.mem_toList.mp he))
  set S_1 := S_prev.applyBatch delList
  have hS1_E : S_1.E = keepSet := by
    rw [hDel_spec.2.2.1]
    ext e
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_toList, delEdges, keepSet,
      Finset.mem_inter]
    tauto
  have hS1_V : S_1.V = cs_old.RF.R := hDel_spec.2.1.trans hS_V
  have hS1_val : S_1.IsValid := hDel_spec.2.2.2.2
  have hS1_ends : ∀ e ∈ keepSet, S_1.tail e = cs_old.RF.root (cs_old.G.tail e) ∧
      S_1.head e = cs_old.RF.root (cs_old.G.head e) := by
    intro e he
    have he1 : e ∈ S_1.E := hS1_E ▸ he
    have hePrev : e ∈ S_prev.E := (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1).1
    have h1 := hDel_spec.2.2.2.1 e he1
    have h2 := hS_sub.2.2 e hePrev
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hParent : ∀ r ∈ newRs, compBatchParentRoot cs_old U r ∈ S_1.V := by
    intro r hr
    rw [hS1_V]
    have hr_in : r ∈ cs_new.RF.R := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hr)).1
    exact (root_mem_R hRF_old (hProjV r (hRF_new.2.2.1 hr_in))).1
  have hDisj : ∀ r ∈ newRs, r ∉ S_1.V := by
    intro r hr
    rw [hS1_V]
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hr)).2
  have hEndTarget : ∀ e ∈ S_1.E, ∀ x ∈ cs_new.G.V,
      (x = cs_new.G.tail e ∨ x = cs_new.G.head e) → e ∈ cs_old.G.E ∧ e ∉ batchDeletes U ∧
      (cs_new.RF.root x ∈ S_1.V ∧ cs_new.RF.root x = cs_old.RF.root (U.foldr stepProj x) ∨
       cs_new.RF.root x ∈ newRs ∧ compBatchParentRoot cs_old U (cs_new.RF.root x) =
         cs_old.RF.root (U.foldr stepProj x)) := by
    intro e he x hx _
    rw [hS1_E] at he
    have he1 := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1
    have hePrev : e ∈ S_prev.E := (Finset.mem_inter.mp he1.1).1
    have heOldG : e ∈ cs_old.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 hePrev)).1
    have hNotDel : e ∉ batchDeletes U := he1.2
    have hrt_mem : cs_new.RF.root x ∈ cs_new.RF.R := (root_mem_R hRF_new hx).1
    have hconn_new : cs_new.RF.F.Connected x (cs_new.RF.root x) := (root_mem_R hRF_new hx).2
    have hconn_old : cs_old.RF.F.Connected (U.foldr stepProj x)
        (U.foldr stepProj (cs_new.RF.root x)) := hProjConn x (cs_new.RF.root x) hconn_new
    have hrt_eq : cs_old.RF.root (U.foldr stepProj x) =
        cs_old.RF.root (U.foldr stepProj (cs_new.RF.root x)) :=
      root_eq_of_connected hRF_old (hProjV x hx) (hProjV _ (hRF_new.2.2.1 hrt_mem)) hconn_old
    refine ⟨heOldG, hNotDel, ?_⟩
    by_cases hrt_old : cs_new.RF.root x ∈ cs_old.RF.R
    · left
      rw [hS1_V]
      refine ⟨hrt_old, ?_⟩
      rw [hrt_eq, hProjOld _ (hRF_old.2.2.1 hrt_old), root_eq_of_mem_R hRF_old hrt_old]
    · right
      exact ⟨Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hrt_mem, hrt_old⟩), hrt_eq.symm⟩
  have hSpecT : ∀ e ∈ S_1.E,
      (cs_new.RF.root (cs_new.G.tail e) ∈ S_1.V ∧ cs_new.RF.root (cs_new.G.tail e) = S_1.tail e) ∨
      (cs_new.RF.root (cs_new.G.tail e) ∈ newRs ∧
        compBatchParentRoot cs_old U (cs_new.RF.root (cs_new.G.tail e)) = S_1.tail e) := by
    intro e he
    have heK : e ∈ keepSet := hS1_E ▸ he
    have heNew : e ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).2)).1
    have hth := hI_new.hG_val e heNew
    obtain ⟨heOldG, hNotDel, hcase⟩ := hEndTarget e he (cs_new.G.tail e) hth.1 (Or.inl rfl)
    have hPE := hProjEdge e heOldG hNotDel
    rw [← hPE.2.1, ← (hS1_ends e heK).1] at hcase
    exact hcase
  have hSpecH : ∀ e ∈ S_1.E,
      (cs_new.RF.root (cs_new.G.head e) ∈ S_1.V ∧ cs_new.RF.root (cs_new.G.head e) = S_1.head e) ∨
      (cs_new.RF.root (cs_new.G.head e) ∈ newRs ∧
        compBatchParentRoot cs_old U (cs_new.RF.root (cs_new.G.head e)) = S_1.head e) := by
    intro e he
    have heK : e ∈ keepSet := hS1_E ▸ he
    have heNew : e ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).2)).1
    have hth := hI_new.hG_val e heNew
    obtain ⟨heOldG, hNotDel, hcase⟩ := hEndTarget e he (cs_new.G.head e) hth.2 (Or.inr rfl)
    have hPE := hProjEdge e heOldG hNotDel
    rw [← hPE.2.2, ← (hS1_ends e heK).2] at hcase
    exact hcase
  have hSplit_spec := applyUpdate_split_list_spec hS1_val (Finset.nodup_toList _)
    hDisj hParent hSpecT hSpecH
  set splitList' := newRs.map fun r => Update.split (compBatchParentRoot cs_old U r) r
    (S_1.E.filter fun e => cs_new.RF.root (cs_new.G.tail e) = r)
    (S_1.E.filter fun e => cs_new.RF.root (cs_new.G.head e) = r)
  have hSplitList_eq : splitList = splitList' := by
    refine List.map_congr_left fun r _ => ?_
    rw [hS1_E]
  rw [← hSplitList_eq] at hSplit_spec
  set S_2 := S_1.applyBatch splitList
  have hS2_V : S_2.V = cs_new.RF.R := by
    rw [hSplit_spec.2.1, hS1_V]
    ext v
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_toList, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun h1 => hR_sub h1) And.left,
      fun h => by by_cases ho : v ∈ cs_old.RF.R <;> simp [ho, h]⟩
  have hS2_E : S_2.E = keepSet := hSplit_spec.2.2.1.trans hS1_E
  let insPairs := insEdges.toList.map fun e =>
    (e, cs_new.RF.root (cs_new.G.tail e), cs_new.RF.root (cs_new.G.head e))
  have hInsList_eq : insList = insPairs.map (fun t => Update.insert t.1 t.2.1 t.2.2) := by
    simp [insList, insPairs, List.map_map]
  have hIns_map_fst : insPairs.map Prod.fst = insEdges.toList := by
    simp [insPairs, List.map_map, Function.comp_def]
  have hIns_nd : (insPairs.map Prod.fst).Nodup := by
    rw [hIns_map_fst]; exact Finset.nodup_toList _
  have hIns_notin : ∀ t ∈ insPairs, t.1 ∉ S_2.E := by
    intro t ht hmem
    rw [List.mem_map] at ht
    rcases ht with ⟨e, he, rfl⟩
    rw [hS2_E] at hmem
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp he)).2 hmem
  have hIns_ends : ∀ t ∈ insPairs, t.2.1 ∈ S_2.V ∧ t.2.2 ∈ S_2.V := by
    intro t ht
    rw [List.mem_map] at ht
    rcases ht with ⟨e, he, rfl⟩
    have heTgt : e ∈ targetE := (Finset.mem_sdiff.mp (Finset.mem_toList.mp he)).1
    have heNew : e ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub heTgt)).1
    have hth := hI_new.hG_val e heNew
    rw [hS2_V]
    exact ⟨(root_mem_R hRF_new hth.1).1, (root_mem_R hRF_new hth.2).1⟩
  have hIns_spec := applyUpdate_insert_list_spec hSplit_spec.2.2.2.2 hIns_nd hIns_notin hIns_ends
  rcases hIns_spec with ⟨hIns_BV, hIns_V, hIns_E, hIns_Old, hIns_New, hIns_Val⟩
  rw [← hInsList_eq] at hIns_BV hIns_V hIns_E hIns_Old hIns_New hIns_Val
  have hUS_eq : U_S = delList ++ splitList ++ insList := rfl
  have hBV_US : S_prev.BatchIsValid U_S := by
    rw [hUS_eq, batchIsValid_append, batchIsValid_append, applyBatch_append]
    exact ⟨⟨hDel_spec.1, hSplit_spec.1⟩, hIns_BV⟩
  have hSnext_eq : S_next = S_2.applyBatch insList := by
    dsimp only [S_next]
    rw [hUS_eq, applyBatch_append, applyBatch_append]
  have hSnext_V : S_next.V = cs_new.RF.R := by rw [hSnext_eq, hIns_V, hS2_V]
  have hSnext_E : S_next.E = targetE := by
    rw [hSnext_eq, hIns_E, hIns_map_fst, hS2_E]
    ext e
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_toList, Finset.mem_sdiff,
      keepSet, insEdges, Finset.mem_inter]
    tauto
  have hSnext_ends : ∀ e ∈ S_next.E,
      S_next.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_next.head e = cs_new.RF.root (cs_new.G.head e) := by
    intro e he
    rw [hSnext_E] at he
    by_cases heK : e ∈ keepSet
    · have heS2 : e ∈ S_2.E := hS2_E ▸ heK
      have heS1 : e ∈ S_1.E := hS1_E ▸ heK
      have h1 := hSnext_eq ▸ hIns_Old e heS2
      have h2 := hSplit_spec.2.2.2.1 e heS1
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
    · have heIns : e ∈ insEdges := Finset.mem_sdiff.mpr ⟨he, heK⟩
      have hePair : (e, cs_new.RF.root (cs_new.G.tail e),
          cs_new.RF.root (cs_new.G.head e)) ∈ insPairs :=
        List.mem_map.mpr ⟨e, Finset.mem_toList.mpr heIns, rfl⟩
      exact hSnext_eq ▸ hIns_New _ hePair
  have hSnext_sub : (coreGraph cs_new.G cs_new.lsf).IsSubgraph S_next := by
    refine ⟨hSnext_V.le, ?_, fun e he => ?_⟩
    · rw [hSnext_E]; exact hTgt_sub
    · exact hSnext_ends e he
  have hUS_len : U_S.length =
      (S_prev.E \ keepSet).card + (cs_new.RF.R \ cs_old.RF.R).card + (targetE \ keepSet).card := by
    rw [hUS_eq, List.length_append, List.length_append]
    simp [delList, splitList, insList, newRs, delEdges, insEdges]
  refine ⟨hBV_US, hSnext_eq ▸ hIns_Val, hSnext_V, hSnext_E, hSnext_ends,
    hSnext_sub, hUS_len, fun hD0 hNoRe => ?_⟩
  intro e hePrev u_op hu hIns
  change u_op ∈ delList ++ splitList ++ insList at hu
  simp only [delList, splitList, insList, List.mem_append, List.mem_map] at hu
  rcases hu with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨e', he', rfl⟩
  · exact hIns
  · exact hIns
  · simp only [Update.Inserts] at hIns
    subst hIns
    have heIns : e' ∈ insEdges := Finset.mem_toList.mp he'
    have heTgt : e' ∈ targetE := (Finset.mem_sdiff.mp heIns).1
    have heNotKeep : e' ∉ keepSet := (Finset.mem_sdiff.mp heIns).2
    have heDel : e' ∈ batchDeletes U := by
      by_contra hnd
      exact heNotKeep (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hePrev, heTgt⟩, hnd⟩, by simp [hD0]⟩)
    have heOldG : e' ∈ cs_old.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 hePrev)).1
    have heNewG : e' ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub heTgt)).1
    exact not_mem_applyBatch_of_delete_not_insert (hNoRe e' heOldG)
      ((mem_batchDeletes_iff U e').mp heDel) (hcs_new_G ▸ heNewG)

lemma buildUS_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_val : S_prev.IsValid) (hS_V : S_prev.V = cs_old.RF.R)
    (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ}
    (hTgt_sub : targetE ⊆ (compLSFBatch cs_old U).G.E \ (compLSFBatch cs_old U).RF.F.E) :
    let cs_new := compLSFBatch cs_old U
    let U_S := buildUS cs_old U cs_new S_prev targetE
    let S_next := S_prev.applyBatch U_S
    let keepSet := (S_prev.E ∩ targetE) \ batchDeletes U
    S_prev.BatchIsValid U_S ∧
    S_next.IsValid ∧
    S_next.V = cs_new.RF.R ∧
    S_next.E = targetE ∧
    (∀ e ∈ S_next.E,
      S_next.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_next.head e = cs_new.RF.root (cs_new.G.head e)) ∧
    (coreGraph cs_new.G cs_new.lsf).IsSubgraph S_next ∧
    U_S.length = (S_prev.E \ keepSet).card + (cs_new.RF.R \ cs_old.RF.R).card + (targetE \ keepSet).card ∧
    (NoBatchReinsert cs_old.G U → NoBatchReinsert S_prev U_S) := by
  have h := buildUSReinsert_spec hI hBU hS_val hS_V hS_sub hTgt_sub ∅
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, by simpa only [Finset.sdiff_empty] using h.2.2.2.2.2.1,
    by simpa only [Finset.sdiff_empty] using h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2 rfl⟩

/-- Surviving-edge insertion and `D_reins`-avoidance propagation for `buildUSReinsert`:
any edge `e ∈ S_prev.E ∩ targetE` that avoids insertion in `U_S` cannot belong to `D_reins`
and cannot be inserted in the input batch `U`. -/
lemma buildUSReinsert_noReinsertPropagates {cs_old : CompLSFState}
    {U : List Update}
    (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE D_reins : Finset ℕ} {e : ℕ}
    (hePrev : e ∈ S_prev.E) (heTgt : e ∈ targetE)
    (hNoIns : ∀ u ∈ buildUSReinsert cs_old U (compLSFBatch cs_old U) S_prev targetE D_reins,
      ¬ u.Inserts e) :
    e ∉ D_reins ∧ ∀ u ∈ U, ¬ u.Inserts e := by
  set cs_new := compLSFBatch cs_old U
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  have hmem_of_notKeep : e ∉ keepSet → False := by
    intro hnk
    have heIns : e ∈ targetE \ keepSet := Finset.mem_sdiff.mpr ⟨heTgt, hnk⟩
    have heMem : Update.insert e (cs_new.RF.root (cs_new.G.tail e))
        (cs_new.RF.root (cs_new.G.head e)) ∈
        buildUSReinsert cs_old U cs_new S_prev targetE D_reins := by
      unfold buildUSReinsert
      simp only [List.mem_append, List.mem_map]
      right
      exact ⟨e, Finset.mem_toList.mpr heIns, rfl⟩
    exact hNoIns _ heMem rfl
  refine ⟨fun hD => hmem_of_notKeep (fun h => (Finset.mem_sdiff.mp h).2 hD), fun u hu hIu => ?_⟩
  have heOldG : e ∈ cs_old.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 hePrev)).1
  have heDel : e ∈ batchDeletes U := mem_batchDeletes_of_inserts hBU heOldG ⟨u, hu, hIu⟩
  exact hmem_of_notKeep (fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 heDel)

/-- Legacy surviving-edge insertion propagation for `buildUS` (`D_reins = ∅`). -/
lemma buildUS_noReinsertPropagates {cs_old : CompLSFState}
    {U : List Update}
    (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ} {e : ℕ}
    (hePrev : e ∈ S_prev.E) (heTgt : e ∈ targetE)
    (hNoIns : ∀ u ∈ buildUS cs_old U (compLSFBatch cs_old U) S_prev targetE, ¬ u.Inserts e) :
    ∀ u ∈ U, ¬ u.Inserts e :=
  (buildUSReinsert_noReinsertPropagates hBU hS_sub hePrev heTgt hNoIns).2


end

end MinCostFlow.SparseCore
