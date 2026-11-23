module

public import MinCostFlow.LSF.Program.Spec
public import MinCostFlow.LSF.Program.BridgeLemmas
import MinCostFlow.LSF.Lemma54Split
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mathematical Lemmas for LSF Batch Updates (`op 0`)

Proves the pure graph, structural-invariant, canonical-batch, and potential-drop lemmas needed by
the Word-RAM LSF batch update procedures:

* `LSFStructInv.to_RF_spanning` and `LSFStructInv.origVert_root_eq`: `S.RF` is a rooted spanning
  forest of `S.G`, and projecting any root `rC ∈ S.R` via `S.origVert` yields the `T₀`-root of
  `z`'s component in `forestGivenRoots S.T₀ S.r₀ S.R_orig S.π`.
* `LSFStructInv.addOrigRoot_inv` and `applyLSFUpdate_structInv`: threshold-free preservation of
  `LSFStructInv` across single root insertions and all three update types.
* `canonUpdate` and `canonBatch`: restrict `.split v v' St Sh` to `St ∩ {e ∈ G.E | G.tail e = v}`
  and `Sh ∩ {e ∈ G.E | G.head e = v}`, preserving `G.applyUpdate`, `UpdateAt`, `BatchAt`,
  `UpdateIsValid`, and `UpdateWithinCaps`.
* `forest_comp_card_eq_edges_succ`, `lsfPhi_eq_semantic`, `phi_drop_addRoot_cut`, and
  `phi_drop_split`: semantic expression of `lsfPhi` and exact potential drops for `T_H`-closure
  root insertions, forest edge cuts, and smaller-to-larger component relabeling.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## `LSFStructInv` rooted-spanning-forest and projection lemmas -/

lemma LSFStructInv.to_RF_spanning {S : LSFState} (I : LSFStructInv S) :
    S.RF.IsRootedSpanningForestOf S.G := by
  let F_orig := forestGivenRoots S.T₀ S.r₀ S.R_orig S.π
  have hRS := forestGivenRoots_isRootedSpanningForest I.hT₀ I.R_orig_bf
    ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
  have hRF_V : S.RF.F.V = S.G.V := I.hT_cur_V
  have hRF_E : S.RF.F.E = F_orig.E := rfl
  have hRF_val : S.RF.F.IsValid := fun e he =>
    I.hT_cur_forest.1 e (I.hT_cur_E ▸ (Finset.sdiff_subset he))
  have hRF_forest : S.RF.F.IsForest :=
    proj_isForest_of_isForest hRS.1 hRF_val fun e he =>
      ⟨he, I.horig_T e (Finset.sdiff_subset he)⟩
  exact RF_isRootedSpanningForestOf hRS hRF_forest hRF_V hRF_E I.hGV_eq I.hdisj_iso
    I.R_orig_sub I.horig_id I.horig_split
    (fun e he => I.horig_T e (Finset.sdiff_subset he))
    (fun x hx hxR f hf => I.hunsplit_F x hx hxR f (Finset.sdiff_subset hf))
    I.hF_sub_G

/-- Projecting the root `rC ∈ S.R` of `z`'s component in `S.RF.F` via `S.origVert` gives the root
of `z` in the `T₀`-forest `rootedForestGivenRoots S.T₀ S.r₀ S.R_orig S.π`. -/
lemma LSFStructInv.origVert_root_eq {S : LSFState} (I : LSFStructInv S)
    {z rC : ℕ} (hzT : z ∈ S.T₀.V) (hrC : rC ∈ S.R) (hconn : S.RF.F.Connected z rC) :
    S.origVert rC = (rootedForestGivenRoots S.T₀ S.r₀ S.R_orig S.π).root z := by
  let F_orig := forestGivenRoots S.T₀ S.r₀ S.R_orig S.π
  let RF_orig := rootedForestGivenRoots S.T₀ S.r₀ S.R_orig S.π
  have hRS := forestGivenRoots_isRootedSpanningForest I.hT₀ I.R_orig_bf
    ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
  obtain ⟨P, hP⟩ := hconn
  have hP_proj : F_orig.IsWalk (S.origVert z) (S.origVert rC) P :=
    proj_isWalk (H := S.RF.F) (K := F_orig) (proj := S.origVert)
      (fun e he => ⟨he, I.horig_T e (Finset.sdiff_subset he)⟩) hP
  rw [I.horig_id z hzT] at hP_proj
  have hrC_orig_R : S.origVert rC ∈ S.R_orig := by
    rw [LSFState.R, Finset.mem_union] at hrC
    rcases hrC with h1 | h2
    · rw [I.horig_id rC (I.R_orig_sub h1)]; exact h1
    · exact I.horig_split rC h2
  have hroot_spec := rootedForest_root_spec hRS hzT
  have hconn_roots : F_orig.Connected (S.origVert rC) (RF_orig.root z) :=
    connected_trans (connected_symm ⟨P, hP_proj⟩) hroot_spec.2
  by_contra hne
  exact forestGivenRoots_not_connected_roots I.hT₀ I.R_orig_bf ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
    hrC_orig_R hroot_spec.1 hne hconn_roots

/-- Adding a single original vertex `z ∈ S.T₀.V` to `S.R₀_base` preserves `LSFStructInv`. -/
lemma LSFStructInv.addOrigRoot_inv {S : LSFState} (I : LSFStructInv S) {z : ℕ}
    (hzT : z ∈ S.T₀.V) :
    let S' : LSFState := { S with R₀_base := insert z S.R₀_base }
    LSFStructInv S' ∧ S.R_orig ⊆ S'.R_orig ∧ S.R ⊆ S'.R ∧ S'.RF.F.E ⊆ S.RF.F.E := by
  let S' : LSFState := { S with R₀_base := insert z S.R₀_base }
  have hR0_sub : S.R₀_base ⊆ S'.R₀_base := Finset.subset_insert z S.R₀_base
  have hR0'_sub : S'.R₀_base ⊆ S.T₀.V := Finset.insert_subset_iff.mpr ⟨hzT, I.hR₀_sub⟩
  have hR_orig_sub : S.R_orig ⊆ S'.R_orig := fun x hx => by
    obtain ⟨u, hu, hanc⟩ := mem_upClosure_iff.mp hx
    exact mem_upClosure_iff.mpr ⟨u, hR0_sub hu, hanc⟩
  have hR_sub : S.R ⊆ S'.R := Finset.union_subset_union_left hR_orig_sub
  have hFE_sub : S'.RF.F.E ⊆ S.RF.F.E := by
    have hdel : deletedEdges S.T₀ S.r₀ S.R_orig S.π ⊆ deletedEdges S.T₀ S.r₀ S'.R_orig S.π :=
      deletedEdges_mono I.hT₀ I.R_orig_bf (upClosure_isBranchFree I.hT₀ hR0'_sub)
        ⟨S.r₀, I.r₀_mem_R_orig⟩ hR_orig_sub S.π I.hord
    exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hdel
  refine ⟨?_, hR_orig_sub, hR_sub, hFE_sub⟩
  exact
    { hG₀_val := I.hG₀_val
      hG_val := I.hG_val
      hV₀ := I.hV₀
      hk := I.hk
      hT₀ := I.hT₀
      hTV := I.hTV
      hr₀_base := hR0_sub I.hr₀_base
      hR₀_sub := hR0'_sub
      hord := I.hord
      hTG₀ := I.hTG₀
      hT_cur_forest := I.hT_cur_forest
      hT_cur_V := I.hT_cur_V
      hT_cur_E := I.hT_cur_E
      hF_sub_G := ⟨I.hF_sub_G.1, hFE_sub.trans I.hF_sub_G.2.1,
        fun e he => I.hF_sub_G.2.2 e (hFE_sub he)⟩
      horig_id := I.horig_id
      horig_split := fun x hx => hR_orig_sub (I.horig_split x hx)
      horig_T := I.horig_T
      hunsplit_F := fun x hx hxR f hf => I.hunsplit_F x hx (fun h => hxR (hR_orig_sub h)) f hf
      hdisj_iso := I.hdisj_iso
      hGV_eq := I.hGV_eq
      hins_sub := I.hins_sub
      hins_wstr := fun e he =>
        ⟨(I.hins_wstr e he).1, hR_sub (I.hins_wstr e he).2.1, hR_sub (I.hins_wstr e he).2.2⟩ }

/-- `applyLSFUpdate` preserves `LSFStructInv` on any valid update of `S.G`. -/
lemma applyLSFUpdate_structInv {S : LSFState} (I : LSFStructInv S) {u : Update}
    (hu : S.G.UpdateIsValid u) :
    LSFStructInv (applyLSFUpdate S u) := by
  classical
  let S' := applyLSFUpdate S u
  have hG₀' : S'.G₀ = S.G₀ := by cases u <;> rfl
  have hT₀' : S'.T₀ = S.T₀ := by cases u <;> rfl
  have hr₀' : S'.r₀ = S.r₀ := by cases u <;> rfl
  have hπ' : S'.π = S.π := by cases u <;> rfl
  have hk' : S'.k = S.k := by cases u <;> rfl
  have hR0_sub : S.R₀_base ⊆ S'.R₀_base := by
    cases u with
    | insert e a b => exact Finset.subset_union_left
    | delete e => exact Finset.subset_union_left
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
  have hR0'_sub : S'.R₀_base ⊆ S.T₀.V := by
    cases u with
    | insert e a b =>
      exact Finset.union_subset I.hR₀_sub (fun x hx => (Finset.mem_filter.mp hx).2)
    | delete e =>
      exact Finset.union_subset I.hR₀_sub (fun x hx => (Finset.mem_filter.mp hx).2)
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate]
      split_ifs with h
      · exact Finset.insert_subset_iff.mpr ⟨h, I.hR₀_sub⟩
      · exact I.hR₀_sub
  have hR_orig_sub : S.R_orig ⊆ S'.R_orig := fun x hx => by
    have hTH' : S'.TH = S.TH := by unfold LSFState.TH; rw [hT₀', hr₀']
    rw [LSFState.R_orig, hTH', hr₀']
    obtain ⟨w, hw, hanc⟩ := mem_upClosure_iff.mp hx
    exact mem_upClosure_iff.mpr ⟨w, hR0_sub hw, hanc⟩
  have hiso_sub : S.isolatedVerts ⊆ S'.isolatedVerts := by
    cases u with
    | insert _ _ _ => exact Finset.Subset.refl _
    | delete _ => exact Finset.Subset.refl _
    | split _ v' _ _ => exact Finset.subset_insert _ _
  have hR_sub : S.R ⊆ S'.R := Finset.union_subset_union hR_orig_sub hiso_sub
  have hFE_sub : S'.RF.F.E ⊆ S.RF.F.E := by
    have hR_orig_eq : S'.R_orig = upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S'.R₀_base := by
      unfold LSFState.R_orig LSFState.TH; rw [hT₀', hr₀']
    have hdel : deletedEdges S.T₀ S.r₀ S.R_orig S.π ⊆ deletedEdges S.T₀ S.r₀ S'.R_orig S.π :=
      deletedEdges_mono I.hT₀ I.R_orig_bf (hR_orig_eq ▸ upClosure_isBranchFree I.hT₀ hR0'_sub)
        ⟨S.r₀, I.r₀_mem_R_orig⟩ hR_orig_sub S.π I.hord
    show (forestGivenRoots S'.T₀ S'.r₀ S'.R_orig S'.π).E ⊆ _
    rw [hT₀', hr₀', hπ']
    exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hdel
  have hG_val' : S'.G.IsValid := by
    have hGeq : S'.G = S.G.applyUpdate u := by cases u <;> rfl
    rw [hGeq]; exact applyUpdate_isValid I.hG_val hu
  have hT_cur_V' : S'.T_cur.V = S'.G.V := by
    cases u with
    | insert _ _ _ => exact I.hT_cur_V
    | delete _ => exact I.hT_cur_V
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      rw [I.hT_cur_V]
  have hT_cur_E' : S'.T_cur.E = S.T₀.E := by
    cases u <;> exact I.hT_cur_E
  have hT_cur_forest' : S'.T_cur.IsForest := by
    cases u with
    | insert _ _ _ => exact I.hT_cur_forest
    | delete _ => exact I.hT_cur_forest
    | split v v' St Sh =>
      exact applyUpdate_split_isForest I.hT_cur_forest (I.hT_cur_V ▸ hu.1) (I.hT_cur_V ▸ hu.2.1) St Sh
  have hdisj' : Disjoint S.T₀.V S'.isolatedVerts := by
    cases u with
    | insert _ _ _ => exact I.hdisj_iso
    | delete _ => exact I.hdisj_iso
    | split v v' St Sh =>
      refine Finset.disjoint_right.mpr fun x hx => ?_
      dsimp only [S', applyLSFUpdate] at hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · intro hxT; exact hu.2.1 (I.hGV_eq ▸ Finset.mem_union_left _ hxT)
      · exact Finset.disjoint_right.mp I.hdisj_iso hx
  have hGV' : S'.G.V = S.T₀.V ∪ S'.isolatedVerts := by
    cases u with
    | insert _ _ _ => exact I.hGV_eq
    | delete _ => exact I.hGV_eq
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      rw [I.hGV_eq, Finset.union_insert]
  have horig_id' : ∀ x ∈ S.T₀.V, S'.origVert x = x := by
    intro x hx
    cases u with
    | insert _ _ _ => exact I.horig_id x hx
    | delete _ => exact I.horig_id x hx
    | split v v' St Sh =>
      have hne : x ≠ v' := fun h => hu.2.1 (h ▸ I.hGV_eq ▸ Finset.mem_union_left _ hx)
      dsimp only [S', applyLSFUpdate]
      rw [Function.update_of_ne hne]; exact I.horig_id x hx
  have horig_split' : ∀ x ∈ S'.isolatedVerts, S'.origVert x ∈ S'.R_orig := by
    intro x hx
    cases u with
    | insert _ _ _ => exact hR_orig_sub (I.horig_split x hx)
    | delete _ => exact hR_orig_sub (I.horig_split x hx)
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate] at hx ⊢
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · rw [Function.update_self]
        have hvT : S.origVert v ∈ S.T₀.V := I.origVert_mem_TV hu.1
        refine subset_upClosure ?_
        dsimp only [S', applyLSFUpdate]
        rw [ite_eq_left hvT]; exact Finset.mem_insert_self _ _
      · have hne : x ≠ v' := fun h => hu.2.1 (h ▸ I.hGV_eq ▸ Finset.mem_union_right _ hx)
        rw [Function.update_of_ne hne]
        exact hR_orig_sub (I.horig_split x hx)
  have horig_T' : ∀ e ∈ S.T₀.E,
      S'.origVert (S'.T_cur.tail e) = S.T₀.tail e ∧ S'.origVert (S'.T_cur.head e) = S.T₀.head e := by
    intro e he
    cases u with
    | insert _ _ _ => exact I.horig_T e he
    | delete _ => exact I.horig_T e he
    | split v v' St Sh =>
      have hec := I.hT_cur_forest.1 e (I.hT_cur_E ▸ he)
      have hold := I.horig_T e he
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      refine ⟨?_, ?_⟩
      · by_cases ht : e ∈ St ∧ S.T_cur.tail e = v
        · rw [ite_eq_left ht, Function.update_self, ← ht.2]; exact hold.1
        · have hne : S.T_cur.tail e ≠ v' := fun h => hu.2.1 (I.hT_cur_V ▸ h ▸ hec.1)
          rw [ite_eq_right ht, Function.update_of_ne hne]; exact hold.1
      · by_cases hh : e ∈ Sh ∧ S.T_cur.head e = v
        · rw [ite_eq_left hh, Function.update_self, ← hh.2]; exact hold.2
        · have hne : S.T_cur.head e ≠ v' := fun h => hu.2.1 (I.hT_cur_V ▸ h ▸ hec.2)
          rw [ite_eq_right hh, Function.update_of_ne hne]; exact hold.2
  have hunsplit_F' : ∀ x ∈ S'.G.V, S'.origVert x ∉ S'.R_orig → ∀ f ∈ S.T₀.E,
      (S.T₀.tail f = S'.origVert x → S'.T_cur.tail f = x) ∧
      (S.T₀.head f = S'.origVert x → S'.T_cur.head f = x) := by
    intro x hx hxR f hf
    cases u with
    | insert _ _ _ => exact I.hunsplit_F x hx (fun h => hxR (hR_orig_sub h)) f hf
    | delete _ => exact I.hunsplit_F x hx (fun h => hxR (hR_orig_sub h)) f hf
    | split v v' St Sh =>
      have hvT : S.origVert v ∈ S.T₀.V := I.origVert_mem_TV hu.1
      have hvR' : S.origVert v ∈ S'.R_orig := by
        refine subset_upClosure ?_
        dsimp only [S', applyLSFUpdate]; rw [ite_eq_left hvT]; exact Finset.mem_insert_self _ _
      have hne_v' : x ≠ v' := fun h => by
        subst h; dsimp only [S', applyLSFUpdate] at hxR; rw [Function.update_self] at hxR
        exact hxR hvR'
      have hx_old : x ∈ S.G.V := by
        dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at hx
        exact (Finset.mem_insert.mp hx).resolve_left hne_v'
      have horig_x : S'.origVert x = S.origVert x := Function.update_of_ne hne_v' _ _
      rw [horig_x] at hxR ⊢
      have hne_v : x ≠ v := fun h => hxR (h ▸ hvR')
      have hold := I.hunsplit_F x hx_old (fun h => hxR (hR_orig_sub h)) f hf
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      exact ⟨fun ht => by rw [ite_eq_right (fun hc => hne_v (hold.1 ht ▸ hc.2))]; exact hold.1 ht,
        fun hh => by rw [ite_eq_right (fun hc => hne_v (hold.2 hh ▸ hc.2))]; exact hold.2 hh⟩
  have hF_sub_G' : S'.G.IsSubgraph S'.RF.F := by
    refine ⟨hT_cur_V'.subset, fun f hf => ?_, fun f hf => ?_⟩
    · have hf_old := hFE_sub hf
      have hfG := I.hF_sub_G.2.1 hf_old
      cases u with
      | insert _ _ _ => exact Finset.mem_insert_of_mem hfG
      | delete e_del =>
        refine Finset.mem_erase.mpr ⟨fun hfe => ?_, hfG⟩
        subst hfe
        have hfT : f ∈ S.T₀.E := Finset.sdiff_subset hf
        have horig_f := I.horig_T f hfT
        have hfg : S.T_cur.tail f = S.G.tail f ∧ S.T_cur.head f = S.G.head f :=
          I.hF_sub_G.2.2 f hf_old
        have hu₀V : S.T₀.tail f ∈ S.T₀.V := (I.hT₀.isForest.1 f hfT).1
        have hv₀V : S.T₀.head f ∈ S.T₀.V := (I.hT₀.isForest.1 f hfT).2
        have hbf' : IsBranchFree S.T₀ S.r₀ S'.R_orig := upClosure_isBranchFree I.hT₀ hR0'_sub
        have hRS' := forestGivenRoots_isRootedSpanningForest I.hT₀ hbf'
          ⟨S.r₀, hR_orig_sub I.r₀_mem_R_orig⟩ S.π
        have hu₀R : S.T₀.tail f ∈ S'.R_orig := by
          rw [← horig_f.1, hfg.1]
          exact subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_insert_self _ _, by rw [← hfg.1, horig_f.1]; exact hu₀V⟩))
        have hv₀R : S.T₀.head f ∈ S'.R_orig := by
          rw [← horig_f.2, hfg.2]
          exact subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
              by rw [← hfg.2, horig_f.2]; exact hv₀V⟩))
        exact rf_edge_not_both_roots_orig hRS' hf ⟨hu₀R, hv₀R⟩
      | split _ _ _ _ => exact hfG
    · have hf_old := hFE_sub hf
      have hfG := I.hF_sub_G.2.1 hf_old
      have hfg : S.T_cur.tail f = S.G.tail f ∧ S.T_cur.head f = S.G.head f :=
        I.hF_sub_G.2.2 f hf_old
      cases u with
      | insert e_new a b =>
        have hne : f ≠ e_new := fun h => hu.1 (h ▸ hfG)
        dsimp only [LSFState.RF, S', applyLSFUpdate, MGraph.applyUpdate]
        rw [Function.update_of_ne hne, Function.update_of_ne hne]; exact hfg
      | delete _ => exact hfg
      | split v v' St Sh =>
        dsimp only [LSFState.RF, S', applyLSFUpdate, MGraph.applyUpdate]
        rw [hfg.1, hfg.2]; exact ⟨rfl, rfl⟩
  have hins_sub' : S'.insertedEdges ⊆ S'.G.E := by
    cases u with
    | insert e _ _ => exact Finset.insert_subset_insert e I.hins_sub
    | delete e => exact Finset.erase_subset_erase e I.hins_sub
    | split _ _ _ _ => exact I.hins_sub
  have hins_wstr' : ∀ e ∈ S'.insertedEdges, S'.wstr e = 1 ∧ S'.G.tail e ∈ S'.R ∧ S'.G.head e ∈ S'.R := by
    intro e he
    cases u with
    | insert e_new a b =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at he ⊢
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · rw [Function.update_self, Function.update_self, Function.update_self]
        refine ⟨rfl, ?_, ?_⟩
        · by_cases ha : a ∈ S.T₀.V
          · exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, ha⟩)))
          · exact Finset.mem_union_right _ ((Finset.mem_union.mp (I.hGV_eq ▸ hu.2.1)).resolve_left ha)
        · by_cases hb : b ∈ S.T₀.V
          · exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hb⟩)))
          · exact Finset.mem_union_right _ ((Finset.mem_union.mp (I.hGV_eq ▸ hu.2.2)).resolve_left hb)
      · have hne : e ≠ e_new := fun h => hu.1 (h ▸ I.hins_sub he)
        rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne]
        exact ⟨(I.hins_wstr e he).1, hR_sub (I.hins_wstr e he).2.1, hR_sub (I.hins_wstr e he).2.2⟩
    | delete e_del =>
      have he' := (Finset.mem_erase.mp he).2
      exact ⟨(I.hins_wstr e he').1, hR_sub (I.hins_wstr e he').2.1, hR_sub (I.hins_wstr e he').2.2⟩
    | split v v' St Sh =>
      have hold := I.hins_wstr e he
      refine ⟨hold.1, ?_, ?_⟩
      · change (if e ∈ St ∧ S.G.tail e = v then v' else S.G.tail e) ∈ S'.R
        by_cases ht : e ∈ St ∧ S.G.tail e = v
        · rw [ite_eq_left ht]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        · rw [ite_eq_right ht]; exact hR_sub hold.2.1
      · change (if e ∈ Sh ∧ S.G.head e = v then v' else S.G.head e) ∈ S'.R
        by_cases hh : e ∈ Sh ∧ S.G.head e = v
        · rw [ite_eq_left hh]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        · rw [ite_eq_right hh]; exact hR_sub hold.2.2
  exact
    { hG₀_val := hG₀'.symm ▸ I.hG₀_val
      hG_val := hG_val'
      hV₀ := hG₀'.symm ▸ I.hV₀
      hk := hk'.symm ▸ I.hk
      hT₀ := hT₀'.symm ▸ hr₀'.symm ▸ I.hT₀
      hTV := hT₀'.symm ▸ hG₀'.symm ▸ I.hTV
      hr₀_base := hr₀'.symm ▸ hR0_sub I.hr₀_base
      hR₀_sub := hT₀'.symm ▸ hR0'_sub
      hord := hT₀'.symm ▸ hπ'.symm ▸ I.hord
      hTG₀ := hT₀'.symm ▸ hG₀'.symm ▸ I.hTG₀
      hT_cur_forest := hT_cur_forest'
      hT_cur_V := hT_cur_V'
      hT_cur_E := hT₀'.symm ▸ hT_cur_E'
      hF_sub_G := hF_sub_G'
      horig_id := hT₀'.symm ▸ horig_id'
      horig_split := horig_split'
      horig_T := hT₀'.symm ▸ horig_T'
      hunsplit_F := hT₀'.symm ▸ hunsplit_F'
      hdisj_iso := hT₀'.symm ▸ hdisj'
      hGV_eq := hT₀'.symm ▸ hGV'
      hins_sub := hins_sub'
      hins_wstr := hins_wstr' }

/-! ## Canonical split updates and batches -/

/-- Canonicalize `.split v v' St Sh` with respect to `G` by intersecting `St` with tail-incident
edges of `v` in `G` and `Sh` with head-incident edges of `v` in `G`. -/
def canonUpdate (G : MGraph) : Update → Update
  | .insert e a b => .insert e a b
  | .delete e => .delete e
  | .split v v' St Sh =>
    .split v v' (St.filter fun e => e ∈ G.E ∧ G.tail e = v)
      (Sh.filter fun e => e ∈ G.E ∧ G.head e = v)

/-- Canonicalize every update in a batch along the evolving graph `G`. -/
def canonBatch (G : MGraph) : List Update → List Update
  | [] => []
  | u :: us => canonUpdate G u :: canonBatch (G.applyUpdate u) us

lemma canonUpdate_apply {G : MGraph} {u : Update} (hu : G.UpdateIsValid u) :
    G.applyUpdate (canonUpdate G u) = G.applyUpdate u := by
  cases u with
  | insert _ _ _ => rfl
  | delete _ => rfl
  | split v v' St Sh =>
    dsimp only [canonUpdate, MGraph.applyUpdate]
    congr 1
    · funext e
      by_cases h1 : e ∈ St ∧ G.tail e = v
      · have hE : e ∈ G.E := hu.2.2.1 (Finset.mem_union_left Sh h1.1)
        simp [h1, hE]
      · simp only [Finset.mem_filter, h1, ↓reduceIte]
        rw [ite_eq_right (fun h => h1 ⟨h.1.1, h.2⟩)]
    · funext e
      by_cases h1 : e ∈ Sh ∧ G.head e = v
      · have hE : e ∈ G.E := hu.2.2.1 (Finset.mem_union_right St h1.1)
        simp [h1, hE]
      · simp only [Finset.mem_filter, h1, ↓reduceIte]
        rw [ite_eq_right (fun h => h1 ⟨h.1.1, h.2⟩)]

lemma canonUpdate_valid {G : MGraph} {u : Update} (hu : G.UpdateIsValid u) :
    G.UpdateIsValid (canonUpdate G u) := by
  cases u with
  | insert _ _ _ => exact hu
  | delete _ => exact hu
  | split v v' St Sh =>
    refine ⟨hu.1, hu.2.1, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_union] at he
      rcases he with h | h <;> exact (Finset.mem_filter.mp h).2.1
    · intro e he
      rw [Finset.mem_union] at he
      rcases he with h | h
      · exact Or.inl (Finset.mem_filter.mp h).2.2
      · exact Or.inr (Finset.mem_filter.mp h).2.2

lemma canonUpdate_withinCaps {vCap eCap : ℕ} {G : MGraph} {u : Update}
    (hc : UpdateWithinCaps vCap eCap u) :
    UpdateWithinCaps vCap eCap (canonUpdate G u) := by
  cases u <;> exact hc

lemma canonUpdate_updateAt {mem : ℕ → ℕ} {a len : ℕ} {G : MGraph} {u : Update} :
    UpdateAt mem a G (canonUpdate G u) len ↔ UpdateAt mem a G u len := by
  cases u with
  | insert _ _ _ => rfl
  | delete _ => rfl
  | split v v' St Sh =>
    simp only [canonUpdate, UpdateAt, Finset.mem_filter]
    constructor <;> (rintro (⟨Lt, Lh, h1, h2, h3, h4, h5, h6⟩ | ⟨Lt, Lh, h1, h2, h3, h4, h5, h6⟩))
    · left; refine ⟨Lt, Lh, h1, h2, fun e => ?_, fun e => ?_, h5, h6⟩
      · rw [h3 e]; tauto
      · rw [h4 e]; tauto
    · right; refine ⟨Lt, Lh, h1, h2, fun e => ?_, fun e => ?_, h5, h6⟩
      · rw [h3 e]; tauto
      · rw [h4 e]; tauto
    · left; refine ⟨Lt, Lh, h1, h2, fun e => ?_, fun e => ?_, h5, h6⟩
      · rw [h3 e]; tauto
      · rw [h4 e]; tauto
    · right; refine ⟨Lt, Lh, h1, h2, fun e => ?_, fun e => ?_, h5, h6⟩
      · rw [h3 e]; tauto
      · rw [h4 e]; tauto

lemma canonBatch_length (G : MGraph) (U : List Update) :
    (canonBatch G U).length = U.length := by
  induction U generalizing G with
  | nil => rfl
  | cons u us ih => simp [canonBatch, ih]

lemma canonBatch_valid {G : MGraph} {U : List Update} (hU : G.BatchIsValid U) :
    G.BatchIsValid (canonBatch G U) := by
  induction U generalizing G with
  | nil => trivial
  | cons u us ih =>
    obtain ⟨hu, hus⟩ := hU
    refine ⟨canonUpdate_valid hu, ?_⟩
    rw [canonUpdate_apply hu]
    exact ih hus

lemma canonBatch_withinCaps {vCap eCap : ℕ} {G : MGraph} {U : List Update}
    (hU : BatchWithinCaps vCap eCap U) :
    BatchWithinCaps vCap eCap (canonBatch G U) := by
  induction U generalizing G with
  | nil => intro x hx; cases hx
  | cons u us ih =>
    intro x hx
    simp only [canonBatch, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact canonUpdate_withinCaps (hU u List.mem_cons_self)
    · exact ih (fun y hy => hU y (List.mem_cons_of_mem u hy)) x hx

lemma canonBatch_bodyAt {mem : ℕ → ℕ} {a totalWords : ℕ} {G : MGraph} {U : List Update}
    (hU : G.BatchIsValid U) :
    BatchBodyAt mem a G (canonBatch G U) totalWords ↔ BatchBodyAt mem a G U totalWords := by
  induction U generalizing G a totalWords with
  | nil => rfl
  | cons u us ih =>
    obtain ⟨hu, hus⟩ := hU
    simp only [canonBatch, BatchBodyAt, canonUpdate_apply hu, canonUpdate_updateAt]
    constructor
    · rintro ⟨len, hle, hup, hrest⟩; exact ⟨len, hle, hup, (ih hus).mp hrest⟩
    · rintro ⟨len, hle, hup, hrest⟩; exact ⟨len, hle, hup, (ih hus).mpr hrest⟩

lemma canonBatch_batchAt {mem : ℕ → ℕ} {a totalWords : ℕ} {G : MGraph} {U : List Update}
    (hU : G.BatchIsValid U) :
    BatchAt mem a G (canonBatch G U) totalWords ↔ BatchAt mem a G U totalWords := by
  simp only [BatchAt, canonBatch_length, canonBatch_bodyAt hU]

/-! ## Forest component edge counts and semantic `lsfPhi` -/

open Classical in
/-- In a forest `F`, the component of `u ∈ F.V` has `|C| = |E_C| + 1`. -/
lemma forest_comp_card_eq_edges_succ {F : MGraph} (hF : F.IsForest) {u : ℕ} (hu : u ∈ F.V) :
    (F.V.filter fun v => F.Connected v u).card =
      (F.E.filter fun e => F.Connected (F.tail e) u).card + 1 := by
  set C := F.V.filter fun v => F.Connected v u
  set EC := F.E.filter fun e => F.Connected (F.tail e) u
  let H : MGraph := { V := C, E := EC, tail := F.tail, head := F.head }
  have hH_val : H.IsValid := by
    intro e he
    obtain ⟨heE, hconnT⟩ := Finset.mem_filter.mp he
    have hte := (hF.1 e heE).1
    have hhe := (hF.1 e heE).2
    have hconnH : F.Connected (F.head e) u :=
      connected_trans ⟨[(e, false)], .cons heE rfl (.nil _)⟩ hconnT
    exact ⟨Finset.mem_filter.mpr ⟨hte, hconnT⟩, Finset.mem_filter.mpr ⟨hhe, hconnH⟩⟩
  have hH_forest : H.IsForest :=
    proj_isForest_of_isForest (proj := id) hF hH_val
      (fun e he => ⟨(Finset.mem_filter.mp he).1, rfl, rfl⟩)
  have hH_conn : ∀ a ∈ C, ∀ b ∈ C, H.Connected a b := by
    intro a ha b hb
    have hab : F.Connected a b :=
      connected_trans (Finset.mem_filter.mp ha).2 (connected_symm (Finset.mem_filter.mp hb).2)
    have hP := forestPath_isPath hF hab
    have hsub : ∀ f ∈ walkEdges (F.forestPath a b), f ∈ H.E := by
      intro f hf
      have hfE := walkEdges_forestPath_sub_edges hF hf
      have hconn_b : F.Connected (F.tail f) b := (isWalk_mem_walkEdges_connected hP.1 hf).1
      exact Finset.mem_filter.mpr ⟨hfE, connected_trans hconn_b (Finset.mem_filter.mp hb).2⟩
    have hlift : ∀ {s t : ℕ} {Q : List (ℕ × Bool)}, F.IsWalk s t Q →
        (∀ f ∈ walkEdges Q, f ∈ H.E) → H.IsWalk s t Q := by
      intro s t Q hQ
      induction hQ with
      | nil s => intro _; exact .nil s
      | cons hxe hsr _ ihQ =>
        intro hsQ
        refine .cons (hsQ _ (by rw [walkEdges_cons]; exact Finset.mem_insert_self _ _)) hsr ?_
        exact ihQ fun f hf => hsQ f (by rw [walkEdges_cons]; exact Finset.mem_insert_of_mem hf)
    exact ⟨F.forestPath a b, hlift hP.1 hsub⟩
  have hST : H.IsSpanningTreeOn C := ⟨hH_forest, rfl, hH_conn⟩
  have hCne : C.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hu, connected_refl F u⟩⟩
  exact (spanningTree_edge_card hST hCne).symm

/-- Doubling drops `Nat.log 2` by at least `1`. -/
lemma log2_add_one_le_of_two_mul_le {a b : ℕ} (ha : 1 ≤ a) (hle : 2 * a ≤ b) :
    Nat.log 2 a + 1 ≤ Nat.log 2 b := by
  refine Nat.le_log_of_pow_le (by decide) ?_
  rw [Nat.pow_succ']
  have hpow : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
  omega

private lemma sum_range_getElem_eq_map_sum (L : List ℕ) (g : ℕ → ℕ) :
    (Finset.range L.length).sum (fun i => if hi : i < L.length then g L[i] else 0) =
      (L.map g).sum := by
  rw [List.sum_eq_foldr]
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.succ_lt_succ_iff, Nat.zero_lt_succ, ↓reduceDIte,
      List.map_cons, List.foldr_cons]
    rw [ih, Nat.add_comm]

/-- Semantic formula for `lsfPhi` on any represented LSF state. -/
theorem lsfPhi_eq_semantic {h b : ℕ} {S : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ}
    (hrep : (LSFRep h).rep b S x mem) :
    lsfPhi b x mem =
      500 * auxLogCap x.n0 * (x.n0 - S.R_orig.card) +
      1400 * S.RF.F.E.card +
      1100 * ∑ e ∈ S.RF.F.E, Nat.log 2 (max 1 (x.compSize (x.compId (S.RF.F.tail e)) - 1)) := by
  classical
  obtain ⟨-, -, -, -, -, -, hInv, hn0, -, -, -, -, -, -, hvT_lt, -, -, -, -, hdgF, hFAnc, -, -,
    hAux⟩ := hrep
  dsimp only [lsfPhi]
  set fAncPtr := lsfFAncPtr b x.vCap x.eCap x.n0 x.tM
  set auxPtr := lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w
  set dgFPtr := lsfDgFPtr b x.vCap x.eCap x.tM
  set eCapF := fECap x.eCap x.n0
  obtain ⟨hFval, hvFcap, heFcap, -, -, -, hmF, -, -, hExtToInt, -, -,
    ⟨eL, heLlen, heLnd, heLmem, heLat, -⟩, hSlots, -⟩ := hdgF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hIsRoot, -, hAct, hCid⟩ := hFAnc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvLen, hvNd, hvMem, -, hvLA, -⟩ := hAux
  have hRorig_eq : (Finset.range x.n0).sum (fun i =>
      let v := mem (auxVListBase auxPtr x.vCap + i)
      if v < x.vCap then (if mem (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0) =
      S.R_orig.card := by
    have h1 : (Finset.range x.n0).sum (fun i =>
        let v := mem (auxVListBase auxPtr x.vCap + i)
        if v < x.vCap then (if mem (fIsRootBase fAncPtr + v) = 1 then 1 else 0) else 0) =
        (Finset.range x.vList.length).sum (fun i =>
          if hi : i < x.vList.length then (if x.vList[i] ∈ S.R_orig then 1 else 0) else 0) := by
      refine Finset.sum_congr (by rw [hvLen]) fun i hi => ?_
      have hi' : i < x.vList.length := Finset.mem_range.mp hi
      have hvi : mem (auxVListBase auxPtr x.vCap + i) = x.vList[i] := hvLA i hi'
      have hvT : x.vList[i] ∈ S.T₀.V := (hvMem _).mp (List.getElem_mem hi')
      have hvlt : x.vList[i] < x.vCap := hvT_lt _ hvT
      have hroot_iff : x.vList[i] ∈ S.RF.R ↔ x.vList[i] ∈ S.R_orig := by
        simp only [LSFState.RF, LSFState.R, Finset.mem_union]
        constructor
        · rintro (h | h)
          · exact h
          · exact False.elim (Finset.disjoint_left.mp hInv.hdisj_iso hvT h)
        · exact Or.inl
      simp only [hvi, hvlt, ↓reduceIte, hi', hIsRoot _ hvlt, hroot_iff]
      split_ifs <;> simp_all
    rw [h1]
    have h2 : (Finset.range x.vList.length).sum (fun i =>
        if hi : i < x.vList.length then (if x.vList[i] ∈ S.R_orig then 1 else 0) else 0) =
        ∑ v ∈ S.T₀.V, if v ∈ S.R_orig then 1 else 0 := by
      rw [sum_range_getElem_eq_map_sum x.vList (fun v => if v ∈ S.R_orig then 1 else 0),
        ← List.sum_toFinset _ hvNd]
      have hto : x.vList.toFinset = S.T₀.V := by
        ext v; simp [hvMem]
      rw [hto]
    rw [h2, Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hInv.R_orig_sub]
  have hmF_le : S.RF.F.E.card ≤ eCapF := by
    have hsub : S.RF.F.E ⊆ Finset.range eCapF := fun e he => Finset.mem_range.mpr (heFcap e he)
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range eCapF)
  have hmin : min (mem (dgFPtr + dgMOff)) eCapF = S.RF.F.E.card := by
    rw [hmF]; exact min_eq_left hmF_le
  have hRelab_eq : (Finset.range (min (mem (dgFPtr + dgMOff)) eCapF)).sum (fun i =>
      let e := mem (dgEListBase dgFPtr x.vCap eCapF + i)
      if e < eCapF then
        let s := mem (dgETailSlotBase dgFPtr x.vCap eCapF + e)
        if s < x.vCap then
          let u := mem (dgIntToExtBase dgFPtr x.vCap + s)
          if u < x.vCap then
            let cid := mem (fCompIdBase fAncPtr x.vCap + u)
            if cid < x.vCap then
              Nat.log 2 (max 1 (mem (fCompSizeBase fAncPtr x.vCap + cid) - 1))
            else 0
          else 0
        else 0
      else 0) =
      ∑ e ∈ S.RF.F.E, Nat.log 2 (max 1 (x.compSize (x.compId (S.RF.F.tail e)) - 1)) := by
    rw [hmin]
    have h1 : (Finset.range S.RF.F.E.card).sum (fun i =>
        let e := mem (dgEListBase dgFPtr x.vCap eCapF + i)
        if e < eCapF then
          let s := mem (dgETailSlotBase dgFPtr x.vCap eCapF + e)
          if s < x.vCap then
            let u := mem (dgIntToExtBase dgFPtr x.vCap + s)
            if u < x.vCap then
              let cid := mem (fCompIdBase fAncPtr x.vCap + u)
              if cid < x.vCap then
                Nat.log 2 (max 1 (mem (fCompSizeBase fAncPtr x.vCap + cid) - 1))
              else 0
            else 0
          else 0
        else 0) =
        (Finset.range eL.length).sum (fun i =>
          if hi : i < eL.length then
            Nat.log 2 (max 1 (x.compSize (x.compId (S.RF.F.tail eL[i])) - 1))
          else 0) := by
      refine Finset.sum_congr (by rw [heLlen]; rfl) fun i hi => ?_
      have hi' : i < eL.length := Finset.mem_range.mp hi
      have he_eq : mem (dgEListBase dgFPtr x.vCap eCapF + i) = eL[i] := heLat i hi'
      have heF : eL[i] ∈ S.RF.F.E := (heLmem _).mp (List.getElem_mem hi')
      have helt : eL[i] < eCapF := heFcap _ heF
      have hs_eq : mem (dgETailSlotBase dgFPtr x.vCap eCapF + eL[i]) =
          mem (dgExtToIntBase dgFPtr x.vCap + S.RF.F.tail eL[i]) := (hSlots _ heF).1
      have huF : S.RF.F.tail eL[i] ∈ S.RF.F.V := (hFval _ heF).1
      have hslt : mem (dgExtToIntBase dgFPtr x.vCap + S.RF.F.tail eL[i]) < x.vCap :=
        hvFcap _ (hExtToInt _ huF).1
      have hu_eq : mem (dgIntToExtBase dgFPtr x.vCap +
          mem (dgExtToIntBase dgFPtr x.vCap + S.RF.F.tail eL[i])) = S.RF.F.tail eL[i] :=
        (hExtToInt _ huF).2
      have hult : S.RF.F.tail eL[i] < x.vCap := hvFcap _ huF
      obtain ⟨hcid_eq, hcid_act, -⟩ := hCid _ huF
      obtain ⟨hcid_lt, -, -, -, hsz_eq, -, -⟩ := hAct _ hcid_act
      rw [hcid_eq] at hcid_lt hsz_eq
      simp only [he_eq, helt, hs_eq, hslt, hu_eq, hult, hcid_eq, hcid_lt, hsz_eq, hi',
        ↓reduceIte, ↓reduceDIte]
    rw [h1, sum_range_getElem_eq_map_sum eL
      (fun e => Nat.log 2 (max 1 (x.compSize (x.compId (S.RF.F.tail e)) - 1))),
      ← List.sum_toFinset _ heLnd]
    have hto : eL.toFinset = S.RF.F.E := by ext e; simp [heLmem]
    rw [hto]
  rw [hRorig_eq, hRelab_eq, hmF]; rfl

/-- Semantic potential drop for one root insertion + edge cut + smaller-to-larger relabeling. -/
lemma phi_drop_addRoot_cut {n0 : ℕ} {R R' E E' E_small : Finset ℕ} {sz sz' : ℕ → ℕ}
    {z cutE : ℕ}
    (hR' : R' = insert z R) (hz_not : z ∉ R) (hR'_le : R'.card ≤ n0)
    (hE' : E' = E.erase cutE) (hcut : cutE ∈ E)
    (hEs_sub : E_small ⊆ E')
    (hmono : ∀ e ∈ E', sz' e ≤ sz e)
    (hdrop : ∀ e ∈ E_small, 2 ≤ sz' e ∧ 2 * (sz' e - 1) ≤ sz e - 1) :
    (500 * auxLogCap n0 * (n0 - R'.card) + 1400 * E'.card +
      1100 * ∑ e ∈ E', Nat.log 2 (max 1 (sz' e - 1))) +
    500 * auxLogCap n0 + 1400 + 1100 * E_small.card ≤
    500 * auxLogCap n0 * (n0 - R.card) + 1400 * E.card +
      1100 * ∑ e ∈ E, Nat.log 2 (max 1 (sz e - 1)) := by
  have hRc : R'.card = R.card + 1 := by rw [hR', Finset.card_insert_of_notMem hz_not]
  have hEc : E.card = E'.card + 1 := by rw [hE']; exact (Finset.card_erase_add_one hcut).symm
  have hphiR : 500 * auxLogCap n0 * (n0 - R'.card) + 500 * auxLogCap n0 =
      500 * auxLogCap n0 * (n0 - R.card) := by
    have : n0 - R.card = (n0 - R'.card) + 1 := by omega
    rw [this, Nat.mul_add, Nat.mul_one]
  have hphiC : 1400 * E'.card + 1400 = 1400 * E.card := by omega
  have hsum_le : (∑ e ∈ E', Nat.log 2 (max 1 (sz' e - 1))) + E_small.card ≤
      ∑ e ∈ E, Nat.log 2 (max 1 (sz e - 1)) := by
    have hE_split : ∑ e ∈ E, Nat.log 2 (max 1 (sz e - 1)) =
        (∑ e ∈ E', Nat.log 2 (max 1 (sz e - 1))) + Nat.log 2 (max 1 (sz cutE - 1)) := by
      rw [hE', ← Finset.sum_erase_add _ _ hcut]
    rw [hE_split]
    have hsplit' : ∀ g : ℕ → ℕ, ∑ e ∈ E', g e = (∑ e ∈ E_small, g e) + ∑ e ∈ E' \ E_small, g e :=
      fun g => (Finset.sum_sdiff hEs_sub).symm.trans (Nat.add_comm _ _)
    rw [hsplit' (fun e => Nat.log 2 (max 1 (sz' e - 1))),
      hsplit' (fun e => Nat.log 2 (max 1 (sz e - 1)))]
    have h1 : (∑ e ∈ E_small, Nat.log 2 (max 1 (sz' e - 1))) + E_small.card ≤
        ∑ e ∈ E_small, Nat.log 2 (max 1 (sz e - 1)) := by
      have : (∑ e ∈ E_small, Nat.log 2 (max 1 (sz' e - 1))) + E_small.card =
          ∑ e ∈ E_small, (Nat.log 2 (max 1 (sz' e - 1)) + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rw [this]
      refine Finset.sum_le_sum fun e he => ?_
      obtain ⟨h2, h2m⟩ := hdrop e he
      have hm1 : max 1 (sz' e - 1) = sz' e - 1 := max_eq_right (by omega)
      have hm2 : max 1 (sz e - 1) = sz e - 1 := max_eq_right (by omega)
      rw [hm1, hm2]
      exact log2_add_one_le_of_two_mul_le (by omega) h2m
    have h2 : ∑ e ∈ E' \ E_small, Nat.log 2 (max 1 (sz' e - 1)) ≤
        ∑ e ∈ E' \ E_small, Nat.log 2 (max 1 (sz e - 1)) :=
      Finset.sum_le_sum fun e he => Nat.log_mono_right (max_le_max_left 1
        (Nat.sub_le_sub_right (hmono e (Finset.mem_sdiff.mp he).1) 1))
    omega
  omega

/-- Semantic potential drop for a vertex split + smaller-to-larger relabeling. -/
lemma phi_drop_split {n0 : ℕ} {R E E_small : Finset ℕ} {sz sz' : ℕ → ℕ}
    (hEs_sub : E_small ⊆ E)
    (hmono : ∀ e ∈ E, sz' e ≤ sz e)
    (hdrop : ∀ e ∈ E_small, 2 ≤ sz' e ∧ 2 * (sz' e - 1) ≤ sz e - 1) :
    (500 * auxLogCap n0 * (n0 - R.card) + 1400 * E.card +
      1100 * ∑ e ∈ E, Nat.log 2 (max 1 (sz' e - 1))) +
    1100 * E_small.card ≤
    500 * auxLogCap n0 * (n0 - R.card) + 1400 * E.card +
      1100 * ∑ e ∈ E, Nat.log 2 (max 1 (sz e - 1)) := by
  have hsum_le : (∑ e ∈ E, Nat.log 2 (max 1 (sz' e - 1))) + E_small.card ≤
      ∑ e ∈ E, Nat.log 2 (max 1 (sz e - 1)) := by
    have hsplit' : ∀ g : ℕ → ℕ, ∑ e ∈ E, g e = (∑ e ∈ E_small, g e) + ∑ e ∈ E \ E_small, g e :=
      fun g => (Finset.sum_sdiff hEs_sub).symm.trans (Nat.add_comm _ _)
    rw [hsplit' (fun e => Nat.log 2 (max 1 (sz' e - 1))),
      hsplit' (fun e => Nat.log 2 (max 1 (sz e - 1)))]
    have h1 : (∑ e ∈ E_small, Nat.log 2 (max 1 (sz' e - 1))) + E_small.card ≤
        ∑ e ∈ E_small, Nat.log 2 (max 1 (sz e - 1)) := by
      have : (∑ e ∈ E_small, Nat.log 2 (max 1 (sz' e - 1))) + E_small.card =
          ∑ e ∈ E_small, (Nat.log 2 (max 1 (sz' e - 1)) + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rw [this]
      refine Finset.sum_le_sum fun e he => ?_
      obtain ⟨h2, h2m⟩ := hdrop e he
      have hm1 : max 1 (sz' e - 1) = sz' e - 1 := max_eq_right (by omega)
      have hm2 : max 1 (sz e - 1) = sz e - 1 := max_eq_right (by omega)
      rw [hm1, hm2]
      exact log2_add_one_le_of_two_mul_le (by omega) h2m
    have h2 : ∑ e ∈ E \ E_small, Nat.log 2 (max 1 (sz' e - 1)) ≤
        ∑ e ∈ E \ E_small, Nat.log 2 (max 1 (sz e - 1)) :=
      Finset.sum_le_sum fun e he => Nat.log_mono_right (max_le_max_left 1
        (Nat.sub_le_sub_right (hmono e (Finset.mem_sdiff.mp he).1) 1))
    omega
  omega

end

end MinCostFlow.LSF.Program
