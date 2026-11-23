module

public import MinCostFlow.LSF.Lemma54Init

/-!
# Walk Projection, Path Lifting, and Stretch Equivalence Under Vertex Splits

This file provides graph-projection and path-lifting helpers used by `MinCostFlow.LSF.Lemma54`
to maintain `S.G.IsSubgraph S.RF.F`, `S.RF.IsRootedSpanningForestOf S.G`, and exact stretch
preservation `S.RF.stretch S.G ℓ e = RF_orig.stretch S.G₀ (safeLen S.G₀ ℓ₀) e` for surviving
edges across `.split` updates.
-/

public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Walk projection and forest preservation -/

lemma proj_isWalk {H K : MGraph} {proj : ℕ → ℕ}
    (hproj : ∀ e ∈ H.E, e ∈ K.E ∧ proj (H.tail e) = K.tail e ∧ proj (H.head e) = K.head e)
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : H.IsWalk u v P) :
    K.IsWalk (proj u) (proj v) P := by
  induction hW with
  | nil s => exact .nil (proj s)
  | @cons u _ x _ he hsrc _ ih =>
    have hm := hproj x.1 he
    have hsrc' : K.src x = proj u := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.src] at hsrc ⊢
      · rw [← hsrc]; exact hm.2.2.symm
      · rw [← hsrc]; exact hm.2.1.symm
    have hdst' : proj (H.dst x) = K.dst x := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.dst]
      · exact hm.2.1
      · exact hm.2.2
    exact .cons hm.1 hsrc' (hdst' ▸ ih)

lemma walkVertices_map_proj {H K : MGraph} {proj : ℕ → ℕ}
    (hproj : ∀ e ∈ H.E, e ∈ K.E ∧ proj (H.tail e) = K.tail e ∧ proj (H.head e) = K.head e)
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : H.IsWalk u v P) :
    (H.walkVertices u P).map proj = K.walkVertices (proj u) P := by
  induction hW with
  | nil s => simp [MGraph.walkVertices]
  | @cons _ _ x _ he _ _ ih =>
    have hm := hproj x.1 he
    have hdst' : proj (H.dst x) = K.dst x := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.dst]
      · exact hm.2.1
      · exact hm.2.2
    rw [walkVertices_cons, List.map_cons, walkVertices_cons, ih, hdst']

lemma proj_isForest_of_isForest {H K : MGraph} {proj : ℕ → ℕ}
    (hK : K.IsForest) (hHv : H.IsValid)
    (hproj : ∀ e ∈ H.E, e ∈ K.E ∧ proj (H.tail e) = K.tail e ∧ proj (H.head e) = K.head e) :
    H.IsForest := by
  refine ⟨hHv, fun P ⟨hne, hnd, u, hW⟩ => ?_⟩
  exact hK.2 P ⟨hne, hnd, proj u, proj_isWalk hproj hW⟩

lemma applyUpdate_split_isForest {T : MGraph} (hT : T.IsForest)
    {v v' : ℕ} (_hv : v ∈ T.V) (hv' : v' ∉ T.V) (St Sh : Finset ℕ) :
    (T.applyUpdate (.split v v' St Sh)).IsForest := by
  let T' := T.applyUpdate (.split v v' St Sh)
  have hT'v : T'.IsValid := by
    intro e he
    have heT := hT.1 e he
    constructor <;> dsimp only [T', MGraph.applyUpdate] <;> split_ifs
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem heT.1
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem heT.2
  let proj : ℕ → ℕ := fun x => if x = v' then v else x
  refine proj_isForest_of_isForest hT hT'v (proj := proj) fun e he => ?_
  have heT := hT.1 e he
  have htn : T.tail e ≠ v' := fun h => hv' (h ▸ heT.1)
  have hhn : T.head e ≠ v' := fun h => hv' (h ▸ heT.2)
  refine ⟨he, ?_, ?_⟩
  · by_cases ht : e ∈ St ∧ T.tail e = v <;> simp [MGraph.applyUpdate, proj, ht, htn]
  · by_cases hh : e ∈ Sh ∧ T.head e = v <;> simp [MGraph.applyUpdate, proj, hh, hhn]

lemma isWalk_mem_walkEdges_connected {G : MGraph} {a b f : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk a b P) (hf : f ∈ walkEdges P) :
    G.Connected (G.tail f) b ∧ G.Connected (G.head f) b := by
  induction hW with
  | nil _ =>
    simp [walkEdges] at hf
  | @cons u w x xs hxE hsrc hrest ih =>
    rw [walkEdges_cons, Finset.mem_insert] at hf
    rcases hf with hfx | hfxs
    · subst hfx
      have hc_src : G.Connected (G.src x) w := ⟨x :: xs, by rw [hsrc]; exact .cons hxE hsrc hrest⟩
      have hc_dst : G.Connected (G.dst x) w := ⟨xs, hrest⟩
      rcases x with ⟨e, _ | _⟩ <;> simp only [MGraph.src, MGraph.dst] at hc_src hc_dst
      · exact ⟨hc_dst, hc_src⟩
      · exact ⟨hc_src, hc_dst⟩
    · exact ih hfxs

/-! ## Membership, root separation, and path lifting for split rooted forests -/

lemma origVert_mem_R_iff {T₀V GV R_orig isolatedVerts : Finset ℕ} {origVert : ℕ → ℕ}
    (hGV : GV = T₀V ∪ isolatedVerts) (hdisj : Disjoint T₀V isolatedVerts)
    (_hR_sub : R_orig ⊆ T₀V)
    (horig_id : ∀ x ∈ T₀V, origVert x = x)
    (horig_split : ∀ x ∈ isolatedVerts, origVert x ∈ R_orig)
    {x : ℕ} (hx : x ∈ GV) :
    x ∈ R_orig ∪ isolatedVerts ↔ origVert x ∈ R_orig := by
  rw [hGV, Finset.mem_union] at hx
  rcases hx with hxT | hxI
  · have hnI : x ∉ isolatedVerts := Finset.disjoint_left.mp hdisj hxT
    simp only [Finset.mem_union, hnI, or_false, horig_id x hxT]
  · exact ⟨fun _ => horig_split x hxI, fun _ => Finset.mem_union_right _ hxI⟩

lemma rf_edge_not_both_roots_orig {T₀ F_orig : MGraph} {R_orig : Finset ℕ}
    (hRS : ({ F := F_orig, R := R_orig } : RootedForest).IsRootedSpanningForestOf T₀)
    {f : ℕ} (hf : f ∈ F_orig.E) :
    ¬ (F_orig.tail f ∈ R_orig ∧ F_orig.head f ∈ R_orig) := by
  rintro ⟨htR, hhR⟩
  have hconn : F_orig.Connected (F_orig.tail f) (F_orig.head f) :=
    ⟨[(f, true)], .cons hf rfl (.nil _)⟩
  have hrt := rootedForest_root_self hRS htR
  have hrh := rootedForest_root_self hRS hhR
  have hreq := (rootedForest_root_eq_iff hRS
    (hRS.2.1 ▸ (hRS.1.1 f hf).1) (hRS.2.1 ▸ (hRS.1.1 f hf).2)).mpr hconn
  rw [hrt, hrh] at hreq
  exact isForest_no_selfLoop hRS.1 hf hreq

lemma rf_not_connected_roots {T₀ F_orig RF_F : MGraph} {R_orig isolatedVerts : Finset ℕ}
    {origVert : ℕ → ℕ}
    (hRS : ({ F := F_orig, R := R_orig } : RootedForest).IsRootedSpanningForestOf T₀)
    (hGV : RF_F.V = T₀.V ∪ isolatedVerts) (hdisj : Disjoint T₀.V isolatedVerts)
    (hR_sub : R_orig ⊆ T₀.V)
    (horig_id : ∀ x ∈ T₀.V, origVert x = x)
    (horig_split : ∀ x ∈ isolatedVerts, origVert x ∈ R_orig)
    (hRF_E : RF_F.E = F_orig.E)
    (horig_RF : ∀ e ∈ F_orig.E, origVert (RF_F.tail e) = F_orig.tail e ∧
      origVert (RF_F.head e) = F_orig.head e)
    (hRF_forest : RF_F.IsForest)
    {r₁ r₂ : ℕ} (hr₁ : r₁ ∈ R_orig ∪ isolatedVerts) (hr₂ : r₂ ∈ R_orig ∪ isolatedVerts)
    (hne : r₁ ≠ r₂) :
    ¬ RF_F.Connected r₁ r₂ := by
  intro hconn
  have hr₁V : r₁ ∈ RF_F.V := hGV ▸ Finset.union_subset_union_left hR_sub hr₁
  have hr₂V : r₂ ∈ RF_F.V := hGV ▸ Finset.union_subset_union_left hR_sub hr₂
  have horig_r₁ : origVert r₁ ∈ R_orig :=
    (origVert_mem_R_iff hGV hdisj hR_sub horig_id horig_split hr₁V).mp hr₁
  have horig_r₂ : origVert r₂ ∈ R_orig :=
    (origVert_mem_R_iff hGV hdisj hR_sub horig_id horig_split hr₂V).mp hr₂
  let P := RF_F.forestPath r₁ r₂
  have hP : RF_F.IsPath r₁ r₂ P := forestPath_isPath hRF_forest hconn
  have hP_ne : P ≠ [] := fun hnil => by
    have hW := hP.1; rw [hnil] at hW; cases hW; exact hne rfl
  have hP_nd : (P.map Prod.fst).Nodup := isPath_nodup_edges hP
  have hW_orig : F_orig.IsWalk (origVert r₁) (origVert r₂) P :=
    proj_isWalk (fun e he => ⟨hRF_E ▸ he, horig_RF e (hRF_E ▸ he)⟩) hP.1
  by_cases heq : origVert r₁ = origVert r₂
  · exact hRS.1.2 P ⟨hP_ne, hP_nd, origVert r₁, heq ▸ hW_orig⟩
  · have hconn_orig : F_orig.Connected (origVert r₁) (origVert r₂) := ⟨P, hW_orig⟩
    have hrt1 := rootedForest_root_self hRS horig_r₁
    have hrt2 := rootedForest_root_self hRS horig_r₂
    have hreq := (rootedForest_root_eq_iff hRS (hRS.2.2.1 horig_r₁) (hRS.2.2.1 horig_r₂)).mpr hconn_orig
    rw [hrt1, hrt2] at hreq
    exact heq hreq

private lemma lift_path_to_root_aux {F_orig RF_F : MGraph} {T₀V GV R_orig isolatedVerts : Finset ℕ}
    {origVert : ℕ → ℕ}
    (hF_val : F_orig.IsValid) (hFV : F_orig.V = T₀V) (hRF_E : RF_F.E = F_orig.E)
    (hRF_val : RF_F.IsValid) (hRF_V : RF_F.V = GV)
    (hGV : GV = T₀V ∪ isolatedVerts) (_hdisj : Disjoint T₀V isolatedVerts)
    (horig_id : ∀ x ∈ T₀V, origVert x = x)
    (horig_split : ∀ x ∈ isolatedVerts, origVert x ∈ R_orig)
    (horig_RF : ∀ e ∈ F_orig.E, origVert (RF_F.tail e) = F_orig.tail e ∧
      origVert (RF_F.head e) = F_orig.head e)
    (hunsplit : ∀ x ∈ GV, origVert x ∉ R_orig → ∀ f ∈ F_orig.E,
      (F_orig.tail f = origVert x → RF_F.tail f = x) ∧
      (F_orig.head f = origVert x → RF_F.head f = x))
    {r₀' : ℕ} (hr₀' : r₀' ∈ R_orig) (P : List (ℕ × Bool)) :
    ∀ x, x ∈ T₀V → x ∉ R_orig → F_orig.IsPath x r₀' P →
      (∀ w ∈ F_orig.walkVertices x P, w ∈ R_orig → w = r₀') →
      ∃ r ∈ R_orig ∪ isolatedVerts, origVert r = r₀' ∧ RF_F.IsWalk x r P := by
  induction P with
  | nil =>
    intro x _ hx_nR hP _
    cases hP.1
    exact absurd hr₀' hx_nR
  | cons e xs ih =>
    intro x hxT hx_nR hP hno
    rcases hP with ⟨hW, hnd⟩
    cases hW with
    | cons he hsrc hrest =>
      have hxG : x ∈ GV := hGV ▸ Finset.mem_union_left _ hxT
      have hsrc_cur : RF_F.src e = x := by
        have hx_un := hunsplit x hxG (by rwa [horig_id x hxT]) e.1 he
        rcases e with ⟨f, _ | _⟩ <;> simp only [MGraph.src] at hsrc ⊢
        · exact hx_un.2 (hsrc.trans (horig_id x hxT).symm)
        · exact hx_un.1 (hsrc.trans (horig_id x hxT).symm)
      let z₀ := F_orig.dst e
      let z_cur := RF_F.dst e
      have horig_z : origVert z_cur = z₀ := by
        have hm := horig_RF e.1 he
        rcases e with ⟨f, _ | _⟩ <;> simp only [MGraph.dst, z₀, z_cur]
        · exact hm.1
        · exact hm.2
      have hz_cur_G : z_cur ∈ GV := by
        rw [← hRF_V]
        have hve := hRF_val e.1 (hRF_E ▸ he)
        rcases e with ⟨f, _ | _⟩ <;> simp only [MGraph.dst, z_cur]
        · exact hve.1
        · exact hve.2
      have hz₀_T : z₀ ∈ T₀V := by
        rw [← hFV]
        have hve := hF_val e.1 he
        rcases e with ⟨f, _ | _⟩ <;> simp only [MGraph.dst, z₀]
        · exact hve.1
        · exact hve.2
      cases xs with
      | nil =>
        cases hrest
        refine ⟨z_cur, ?_, horig_z, .cons (hRF_E ▸ he) hsrc_cur (.nil z_cur)⟩
        rw [hGV, Finset.mem_union] at hz_cur_G
        rcases hz_cur_G with hzT | hzI
        · rw [horig_id z_cur hzT] at horig_z
          exact Finset.mem_union_left _ (horig_z ▸ hr₀')
        · exact Finset.mem_union_right _ hzI
      | cons e2 xs2 =>
        rw [walkVertices_cons] at hnd
        have hnd_rest : (F_orig.walkVertices z₀ (e2 :: xs2)).Nodup := (List.nodup_cons.mp hnd).2
        have hz_ne_r₀ : z₀ ≠ r₀' := fun hz_eq => by
          have hP_loop : F_orig.IsPath r₀' r₀' (e2 :: xs2) := ⟨hz_eq ▸ hrest, hz_eq ▸ hnd_rest⟩
          exact List.cons_ne_nil e2 xs2 (IsPath_nil_of_eq hP_loop)
        have hz_mem : z₀ ∈ F_orig.walkVertices x (e :: e2 :: xs2) := by
          rw [walkVertices_cons]
          exact List.mem_cons_of_mem x (IsWalk_start_mem_walkVertices F_orig z₀ (e2 :: xs2))
        have hz_nR : z₀ ∉ R_orig := fun hzR => hz_ne_r₀ (hno z₀ hz_mem hzR)
        have hz_cur_nI : z_cur ∉ isolatedVerts := fun hI => by
          have hR := horig_split z_cur hI
          rw [horig_z] at hR
          exact hz_nR hR
        have hz_cur_T : z_cur ∈ T₀V := by
          rw [hGV, Finset.mem_union] at hz_cur_G
          exact hz_cur_G.resolve_right hz_cur_nI
        have hz_eq_cur : z_cur = z₀ := by
          rw [← horig_id z_cur hz_cur_T, horig_z]
        have hno_rest : ∀ w ∈ F_orig.walkVertices z₀ (e2 :: xs2), w ∈ R_orig → w = r₀' := by
          intro w hw hwR
          apply hno w _ hwR
          rw [walkVertices_cons]
          exact List.mem_cons_of_mem x hw
        obtain ⟨r, hrR, hr_orig, hW_rest⟩ := ih z₀ hz₀_T hz_nR ⟨hrest, hnd_rest⟩ hno_rest
        have hW_cur : RF_F.IsWalk (RF_F.dst e) r (e2 :: xs2) := by
          change RF_F.IsWalk z_cur r _
          rw [hz_eq_cur]
          exact hW_rest
        exact ⟨r, hrR, hr_orig, .cons (hRF_E ▸ he) hsrc_cur hW_cur⟩

lemma RF_isRootedSpanningForestOf {T₀ F_orig RF_F G : MGraph}
    {R_orig isolatedVerts : Finset ℕ} {origVert : ℕ → ℕ}
    (hRS_orig : ({ F := F_orig, R := R_orig } : RootedForest).IsRootedSpanningForestOf T₀)
    (hRF_forest : RF_F.IsForest)
    (hRF_V : RF_F.V = G.V) (hRF_E : RF_F.E = F_orig.E)
    (hGV : G.V = T₀.V ∪ isolatedVerts) (hdisj : Disjoint T₀.V isolatedVerts)
    (hR_sub : R_orig ⊆ T₀.V)
    (horig_id : ∀ x ∈ T₀.V, origVert x = x)
    (horig_split : ∀ x ∈ isolatedVerts, origVert x ∈ R_orig)
    (horig_RF : ∀ e ∈ F_orig.E, origVert (RF_F.tail e) = F_orig.tail e ∧
      origVert (RF_F.head e) = F_orig.head e)
    (hunsplit : ∀ x ∈ G.V, origVert x ∉ R_orig → ∀ f ∈ F_orig.E,
      (F_orig.tail f = origVert x → RF_F.tail f = x) ∧
      (F_orig.head f = origVert x → RF_F.head f = x))
    (hG_sub_RF : G.IsSubgraph RF_F) :
    ({ F := RF_F, R := R_orig ∪ isolatedVerts } : RootedForest).IsRootedSpanningForestOf G := by
  let R := R_orig ∪ isolatedVerts
  have hR_sub_GV : R ⊆ G.V := hGV ▸ Finset.union_subset_union_left hR_sub
  refine ⟨hRF_forest, hRF_V, hR_sub_GV, fun v hv => ?_, hG_sub_RF⟩
  by_cases hvR : v ∈ R
  · refine ⟨v, ⟨hvR, connected_refl RF_F v⟩, fun r' ⟨hr', hconn⟩ => ?_⟩
    by_contra hne
    exact rf_not_connected_roots hRS_orig (hRF_V.trans hGV) hdisj hR_sub horig_id horig_split
      hRF_E horig_RF hRF_forest hr' hvR hne (connected_symm hconn)
  · have hvT : v ∈ T₀.V := by
      rw [hGV, Finset.mem_union] at hv
      exact hv.resolve_right (fun hI => hvR (Finset.mem_union_right _ hI))
    have hv_nR₀ : v ∉ R_orig := fun h => hvR (Finset.mem_union_left _ h)
    let RF_orig : RootedForest := { F := F_orig, R := R_orig }
    let r₀' := RF_orig.root v
    have hr₀_spec := rootedForest_root_spec hRS_orig hvT
    let P := F_orig.forestPath v r₀'
    have hP : F_orig.IsPath v r₀' P := forestPath_isPath hRS_orig.1 hr₀_spec.2
    have hno : ∀ w ∈ F_orig.walkVertices v P, w ∈ R_orig → w = r₀' := by
      intro w hw hwR
      obtain ⟨P₁, _, _, hW1, _⟩ := walkVertices_mem_split hP.1 hw
      have hwV : w ∈ T₀.V := hRS_orig.2.1 ▸ hRS_orig.2.2.1 hwR
      have hcw : F_orig.Connected w r₀' :=
        connected_trans (connected_symm ⟨P₁, hW1⟩) hr₀_spec.2
      have hrtw := rootedForest_root_self hRS_orig hwR
      have hreq := (rootedForest_root_eq_iff hRS_orig hwV (hRS_orig.2.2.1 hr₀_spec.1)).mpr hcw
      rw [hrtw, rootedForest_root_self hRS_orig hr₀_spec.1] at hreq
      exact hreq
    obtain ⟨r, hrR, _, hW⟩ := lift_path_to_root_aux hRS_orig.1.1 hRS_orig.2.1 hRF_E
      hRF_forest.1 hRF_V hGV hdisj horig_id horig_split horig_RF hunsplit
      hr₀_spec.1 P v hvT hv_nR₀ hP hno
    refine ⟨r, ⟨hrR, ⟨P, hW⟩⟩, fun r' ⟨hr', hconn'⟩ => ?_⟩
    by_contra hne
    exact rf_not_connected_roots hRS_orig (hRF_V.trans hGV) hdisj hR_sub horig_id horig_split
      hRF_E horig_RF hRF_forest hr' hrR hne (connected_trans (connected_symm hconn') ⟨P, hW⟩)

/-! ## Exact stretch preservation on un-inserted edges under splits -/

lemma proj_isPath_of_isPath {T₀ F_orig RF_F : MGraph} {R_orig isolatedVerts : Finset ℕ}
    {origVert : ℕ → ℕ}
    (hRS_orig : ({ F := F_orig, R := R_orig } : RootedForest).IsRootedSpanningForestOf T₀)
    (hGV : RF_F.V = T₀.V ∪ isolatedVerts) (hdisj : Disjoint T₀.V isolatedVerts)
    (hR_sub : R_orig ⊆ T₀.V)
    (horig_id : ∀ x ∈ T₀.V, origVert x = x)
    (horig_split : ∀ x ∈ isolatedVerts, origVert x ∈ R_orig)
    (hRF_E : RF_F.E = F_orig.E)
    (horig_RF : ∀ e ∈ F_orig.E, origVert (RF_F.tail e) = F_orig.tail e ∧
      origVert (RF_F.head e) = F_orig.head e)
    (hRF_forest : RF_F.IsForest)
    {u v : ℕ} (hu : u ∈ RF_F.V) {P : List (ℕ × Bool)} (hP : RF_F.IsPath u v P) :
    F_orig.IsPath (origVert u) (origVert v) P := by
  have hproj : ∀ e ∈ RF_F.E, e ∈ F_orig.E ∧
      origVert (RF_F.tail e) = F_orig.tail e ∧ origVert (RF_F.head e) = F_orig.head e :=
    fun e he => ⟨hRF_E ▸ he, horig_RF e (hRF_E ▸ he)⟩
  refine ⟨proj_isWalk hproj hP.1, ?_⟩
  rw [← walkVertices_map_proj hproj hP.1]
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hP.2
  have hxV : x ∈ RF_F.V := (IsWalk_vertices_mem hRF_forest.1 hu hP.1).2 x hx
  have hyV : y ∈ RF_F.V := (IsWalk_vertices_mem hRF_forest.1 hu hP.1).2 y hy
  obtain ⟨Px, _, _, hWx, _⟩ := walkVertices_mem_split hP.1 hx
  obtain ⟨Py, _, _, hWy, _⟩ := walkVertices_mem_split hP.1 hy
  have hconn_xy : RF_F.Connected x y := connected_trans (connected_symm ⟨Px, hWx⟩) ⟨Py, hWy⟩
  by_cases hxR : x ∈ R_orig ∪ isolatedVerts
  · have horig_x : origVert x ∈ R_orig :=
      (origVert_mem_R_iff hGV hdisj hR_sub horig_id horig_split hxV).mp hxR
    have hyR : y ∈ R_orig ∪ isolatedVerts :=
      (origVert_mem_R_iff hGV hdisj hR_sub horig_id horig_split hyV).mpr (hxy ▸ horig_x)
    by_contra hne
    exact rf_not_connected_roots hRS_orig hGV hdisj hR_sub horig_id horig_split hRF_E horig_RF
      hRF_forest hxR hyR hne hconn_xy
  · have horig_x : origVert x ∉ R_orig := fun h =>
      hxR ((origVert_mem_R_iff hGV hdisj hR_sub horig_id horig_split hxV).mpr h)
    have hyR : y ∉ R_orig ∪ isolatedVerts := fun hyR =>
      horig_x (hxy ▸ (origVert_mem_R_iff hGV hdisj hR_sub horig_id horig_split hyV).mp hyR)
    have hxT : x ∈ T₀.V := by
      rw [hGV, Finset.mem_union] at hxV
      exact hxV.resolve_right (fun hI => hxR (Finset.mem_union_right _ hI))
    have hyT : y ∈ T₀.V := by
      rw [hGV, Finset.mem_union] at hyV
      exact hyV.resolve_right (fun hI => hyR (Finset.mem_union_right _ hI))
    rw [← horig_id x hxT, ← horig_id y hyT, hxy]

lemma RF_stretch_eq_orig {G G₀ T₀ RF_F : MGraph} {R_orig isolatedVerts : Finset ℕ}
    {r₀ : ℕ} {π : ℕ → ℕ} {origVert : ℕ → ℕ} {insertedEdges : Finset ℕ}
    {ℓ₀ ℓ : ℕ → ℝ}
    (hG₀_val : G₀.IsValid) (hG_val : G.IsValid) (hT₀ : IsRootedTree T₀ r₀)
    (hTV : T₀.V = G₀.V) (hord : IsEdgeOrder T₀ π)
    (hTG₀ : ∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f)
    (hTp₀ : ∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E)
    (hpi_br : ∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g)
    (hR_bf : IsBranchFree T₀ r₀ R_orig) (hr₀_R : r₀ ∈ R_orig)
    (hGV : G.V = T₀.V ∪ isolatedVerts) (hdisj : Disjoint T₀.V isolatedVerts)
    (horig_id : ∀ x ∈ T₀.V, origVert x = x)
    (horig_split : ∀ x ∈ isolatedVerts, origVert x ∈ R_orig)
    (hRF_V : RF_F.V = G.V) (hRF_E : RF_F.E = (forestGivenRoots T₀ r₀ R_orig π).E)
    (horig_RF : ∀ e ∈ (forestGivenRoots T₀ r₀ R_orig π).E,
      origVert (RF_F.tail e) = T₀.tail e ∧ origVert (RF_F.head e) = T₀.head e)
    (hunsplit : ∀ x ∈ G.V, origVert x ∉ R_orig → ∀ f ∈ (forestGivenRoots T₀ r₀ R_orig π).E,
      (T₀.tail f = origVert x → RF_F.tail f = x) ∧
      (T₀.head f = origVert x → RF_F.head f = x))
    (hG_sub_RF : G.IsSubgraph RF_F)
    (hRF_forest : RF_F.IsForest)
    (horig_del : ∀ e ∈ G₀.E,
      (e ∈ G.E ∧ e ∉ insertedEdges) ∨ (G₀.tail e ∈ R_orig ∧ G₀.head e ∈ R_orig))
    (hℓ_orig : ∀ e ∈ G₀.E, e ∈ G.E → e ∉ insertedEdges → ℓ e = ℓ₀ e)
    {e : ℕ} (heG : e ∈ G.E) (heG₀ : e ∈ G₀.E) (he_nins : e ∉ insertedEdges)
    (horig_u : origVert (G.tail e) = G₀.tail e) (horig_v : origVert (G.head e) = G₀.head e) :
    ({ F := RF_F, R := R_orig ∪ isolatedVerts } : RootedForest).stretch G ℓ e =
      (rootedForestGivenRoots T₀ r₀ R_orig π).stretch G₀ (safeLen G₀ ℓ₀) e := by
  let F_orig := forestGivenRoots T₀ r₀ R_orig π
  let RF_orig : RootedForest := rootedForestGivenRoots T₀ r₀ R_orig π
  let RF : RootedForest := { F := RF_F, R := R_orig ∪ isolatedVerts }
  have hRS_orig : RF_orig.IsRootedSpanningForestOf T₀ :=
    forestGivenRoots_isRootedSpanningForest hT₀ hR_bf ⟨r₀, hr₀_R⟩ π
  have hRS_full : RF.IsRootedSpanningForestOf G :=
    RF_isRootedSpanningForestOf hRS_orig hRF_forest hRF_V hRF_E hGV hdisj hR_bf.1
      horig_id horig_split horig_RF hunsplit hG_sub_RF
  have hF_sub_T₀ : T₀.IsSubgraph F_orig :=
    ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  let u := G.tail e
  let v := G.head e
  let u₀ := G₀.tail e
  let v₀ := G₀.head e
  have huV : u ∈ RF_F.V := hRF_V ▸ (hG_val e heG).1
  have hvV : v ∈ RF_F.V := hRF_V ▸ (hG_val e heG).2
  have hu₀V : u₀ ∈ T₀.V := hTV ▸ (hG₀_val e heG₀).1
  have hv₀V : v₀ ∈ T₀.V := hTV ▸ (hG₀_val e heG₀).2
  have he_len : ℓ e = safeLen G₀ ℓ₀ e :=
    (hℓ_orig e heG₀ heG he_nins).trans (safeLen_eq_of_mem ℓ₀ heG₀).symm
  have hwalk_eq_len : ∀ {P : List (ℕ × Bool)}, (P.map Prod.fst).Nodup →
      walkEdges P ⊆ RF_F.E → walkEdges P ⊆ G₀.E →
      walkLength ℓ P = walkLength (safeLen G₀ ℓ₀) P := by
    intro P hnd hP_RF hP_G₀
    rw [walkLength_eq_sum_of_nodup ℓ hnd, walkLength_eq_sum_of_nodup (safeLen G₀ ℓ₀) hnd]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hfF : f ∈ F_orig.E := hRF_E ▸ hP_RF hf
    have hfG₀ : f ∈ G₀.E := hP_G₀ hf
    have htf := hTG₀ f (hF_sub_T₀.2.1 hfF) hfG₀
    have hn_both := rf_edge_not_both_roots_orig hRS_orig hfF
    have hn_both₀ : ¬ (G₀.tail f ∈ R_orig ∧ G₀.head f ∈ R_orig) := fun h =>
      hn_both ⟨htf.1 ▸ h.1, htf.2 ▸ h.2⟩
    have hfG_nins := (horig_del f hfG₀).resolve_right hn_both₀
    exact (hℓ_orig f hfG₀ hfG_nins.1 hfG_nins.2).trans (safeLen_eq_of_mem ℓ₀ hfG₀).symm
  have forestPath_to_root_eq : ∀ {x : ℕ}, x ∈ RF_F.V →
      RF_F.forestPath x (RF.root x) = F_orig.forestPath (origVert x) (RF_orig.root (origVert x)) := by
    intro x hx
    have hxG : x ∈ G.V := hRF_V ▸ hx
    have hr_spec := rootedForest_root_spec hRS_full hxG
    have hP_rf : RF_F.IsPath x (RF.root x) (RF_F.forestPath x (RF.root x)) :=
      forestPath_isPath hRF_forest hr_spec.2
    have hP_orig := proj_isPath_of_isPath hRS_orig (hRF_V.trans hGV) hdisj hR_bf.1
      horig_id horig_split hRF_E horig_RF hRF_forest hx hP_rf
    have hrV_rf : RF.root x ∈ RF_F.V := hRF_V ▸ hRS_full.2.2.1 hr_spec.1
    have horig_r : origVert (RF.root x) ∈ R_orig :=
      (origVert_mem_R_iff (hRF_V.trans hGV) hdisj hR_bf.1 horig_id horig_split hrV_rf).mp hr_spec.1
    have horig_xV : origVert x ∈ T₀.V := by
      rw [hGV, Finset.mem_union] at hxG
      rcases hxG with hxT | hxI
      · rw [horig_id x hxT]; exact hxT
      · exact hR_bf.1 (horig_split x hxI)
    have hconn_orig : F_orig.Connected (origVert x) (origVert (RF.root x)) := ⟨_, hP_orig.1⟩
    have hroot_orig : RF_orig.root (origVert x) = origVert (RF.root x) := by
      have h1 := (rootedForest_root_eq_iff hRS_orig horig_xV (hR_bf.1 horig_r)).mpr hconn_orig
      exact h1.trans (rootedForest_root_self hRS_orig horig_r)
    rw [hroot_orig]
    exact (forestPath_eq_of_isPath hRS_orig.1 hP_orig).symm
  unfold RootedForest.stretch
  dsimp only
  change (if RF.root u = RF.root v then _ else _) =
    (if RF_orig.root u₀ = RF_orig.root v₀ then _ else _)
  by_cases hroot : RF.root u = RF.root v
  · have hru_spec := rootedForest_root_spec hRS_full (hRF_V ▸ huV)
    have hrv_spec := rootedForest_root_spec hRS_full (hRF_V ▸ hvV)
    have hconn_uv : RF_F.Connected u v :=
      connected_trans hru_spec.2 (hroot ▸ connected_symm hrv_spec.2)
    have hP_uv : RF_F.IsPath u v (RF_F.forestPath u v) := forestPath_isPath hRF_forest hconn_uv
    have hP_orig := proj_isPath_of_isPath hRS_orig (hRF_V.trans hGV) hdisj hR_bf.1
      horig_id horig_split hRF_E horig_RF hRF_forest huV hP_uv
    rw [horig_u, horig_v] at hP_orig
    have hconn_orig : F_orig.Connected u₀ v₀ := ⟨_, hP_orig.1⟩
    have hroot_orig : RF_orig.root u₀ = RF_orig.root v₀ :=
      (rootedForest_root_eq_iff hRS_orig hu₀V hv₀V).mpr hconn_orig
    simp only [hroot, hroot_orig, ↓reduceIte]
    have hFP_eq : F_orig.forestPath u₀ v₀ = RF_F.forestPath u v :=
      forestPath_eq_of_isPath hRS_orig.1 hP_orig
    have hsub_RF : walkEdges (RF_F.forestPath u v) ⊆ RF_F.E := fun _ hf =>
      walkEdges_forestPath_sub_edges hRF_forest hf
    have hsub_G₀ : walkEdges (F_orig.forestPath u₀ v₀) ⊆ G₀.E := by
      rw [forestPath_subgraph hT₀.isForest hF_sub_T₀ hconn_orig]
      exact hTp₀ e heG₀
    rw [hwalk_eq_len (isPath_nodup_edges hP_uv) hsub_RF (hFP_eq ▸ hsub_G₀), ← hFP_eq, he_len]
    rfl
  · let P_u := RF_F.forestPath u (RF.root u)
    let P_v := RF_F.forestPath v (RF.root v)
    have hPu_eq : P_u = F_orig.forestPath u₀ (RF_orig.root u₀) :=
      (forestPath_to_root_eq huV).trans (by rw [horig_u])
    have hPv_eq : P_v = F_orig.forestPath v₀ (RF_orig.root v₀) :=
      (forestPath_to_root_eq hvV).trans (by rw [horig_v])
    have hru_spec := rootedForest_root_spec hRS_full (hRF_V ▸ huV)
    have hrv_spec := rootedForest_root_spec hRS_full (hRF_V ▸ hvV)
    have hPu_path : RF_F.IsPath u (RF.root u) P_u := forestPath_isPath hRF_forest hru_spec.2
    have hPv_path : RF_F.IsPath v (RF.root v) P_v := forestPath_isPath hRF_forest hrv_spec.2
    have hPu_RF : walkEdges P_u ⊆ RF_F.E := fun _ hf =>
      walkEdges_forestPath_sub_edges hRF_forest hf
    have hPv_RF : walkEdges P_v ⊆ RF_F.E := fun _ hf =>
      walkEdges_forestPath_sub_edges hRF_forest hf
    have hru₀_spec := rootedForest_root_spec hRS_orig hu₀V
    have hrv₀_spec := rootedForest_root_spec hRS_orig hv₀V
    simp only [hroot, ↓reduceIte]
    by_cases hroot₀ : RF_orig.root u₀ = RF_orig.root v₀
    · simp only [hroot₀, ↓reduceIte]
      let r_orig := RF_orig.root u₀
      have hdisj_uv : Disjoint (walkEdges P_u) (walkEdges P_v) := by
        rw [Finset.disjoint_left]
        intro f hf_u hf_v
        have hfF : f ∈ F_orig.E := hRF_E ▸ hPu_RF hf_u
        have hn_both := rf_edge_not_both_roots_orig hRS_orig hfF
        have hconn_f_u := isWalk_mem_walkEdges_connected hPu_path.1 hf_u
        have hconn_f_v := isWalk_mem_walkEdges_connected hPv_path.1 hf_v
        have hconn_rr : RF_F.Connected (RF.root u) (RF.root v) := by
          by_cases htR : T₀.tail f ∈ R_orig
          · have hh_nR : T₀.head f ∉ R_orig := fun hhR => hn_both ⟨htR, hhR⟩
            have hwV : T₀.head f ∈ T₀.V := (hRS_orig.1.1 f hfF).2
            have hwG : T₀.head f ∈ G.V := hGV ▸ Finset.mem_union_left _ hwV
            have hh_eq := (hunsplit (T₀.head f) hwG (by rwa [horig_id _ hwV]) f hfF).2
              (horig_id _ hwV).symm
            rw [hh_eq] at hconn_f_u hconn_f_v
            exact connected_trans (connected_symm hconn_f_u.2) hconn_f_v.2
          · have hwV : T₀.tail f ∈ T₀.V := (hRS_orig.1.1 f hfF).1
            have hwG : T₀.tail f ∈ G.V := hGV ▸ Finset.mem_union_left _ hwV
            have ht_eq := (hunsplit (T₀.tail f) hwG (by rwa [horig_id _ hwV]) f hfF).1
              (horig_id _ hwV).symm
            rw [ht_eq] at hconn_f_u hconn_f_v
            exact connected_trans (connected_symm hconn_f_u.1) hconn_f_v.1
        exact rf_not_connected_roots hRS_orig (hRF_V.trans hGV) hdisj hR_bf.1
          horig_id horig_split hRF_E horig_RF hRF_forest hru_spec.1 hrv_spec.1 hroot hconn_rr
      have hPv_eq' : P_v = F_orig.forestPath v₀ r_orig :=
        hPv_eq.trans (congrArg (F_orig.forestPath v₀) hroot₀.symm)
      have hconn_vr : F_orig.Connected v₀ r_orig := by
        change F_orig.Connected v₀ (RF_orig.root u₀)
        rw [hroot₀]
        exact hrv₀_spec.2
      have hconn_rv : F_orig.Connected r_orig v₀ := connected_symm hconn_vr
      have hrev_rv : F_orig.forestPath r_orig v₀ = walkRev (F_orig.forestPath v₀ r_orig) :=
        forestPath_rev hRS_orig.1 hconn_vr
      have hdisj_orig : Disjoint (walkEdges (F_orig.forestPath u₀ r_orig))
          (walkEdges (F_orig.forestPath r_orig v₀)) := by
        rw [hrev_rv, walkEdges_walkRev, ← hPu_eq, ← hPv_eq']
        exact hdisj_uv
      have hconcat : F_orig.forestPath u₀ v₀ =
          F_orig.forestPath u₀ r_orig ++ F_orig.forestPath r_orig v₀ :=
        forestPath_concat_of_disjoint hRS_orig.1 hru₀_spec.2 hconn_rv hdisj_orig
      have hconn_uv₀ : F_orig.Connected u₀ v₀ := connected_trans hru₀_spec.2 hconn_rv
      have hsub_uv_G₀ : walkEdges (F_orig.forestPath u₀ v₀) ⊆ G₀.E := by
        rw [forestPath_subgraph hT₀.isForest hF_sub_T₀ hconn_uv₀]
        exact hTp₀ e heG₀
      have hPu_G₀ : walkEdges P_u ⊆ G₀.E := fun f hf =>
        hsub_uv_G₀ (by rw [hconcat, walkEdges_append, Finset.mem_union]; exact Or.inl (hPu_eq ▸ hf))
      have hPv_G₀ : walkEdges P_v ⊆ G₀.E := fun f hf =>
        hsub_uv_G₀ (by
          rw [hconcat, hrev_rv, walkEdges_append, walkEdges_walkRev, Finset.mem_union]
          exact Or.inr (hPv_eq' ▸ hf))
      have hlen_u := hwalk_eq_len (isPath_nodup_edges hPu_path) hPu_RF hPu_G₀
      have hlen_v := hwalk_eq_len (isPath_nodup_edges hPv_path) hPv_RF hPv_G₀
      have hP_uv₀ : F_orig.IsPath u₀ v₀ (F_orig.forestPath u₀ v₀) :=
        forestPath_isPath hRS_orig.1 hconn_uv₀
      have hlen_sum : walkLength (safeLen G₀ ℓ₀) (F_orig.forestPath u₀ v₀) =
          walkLength (safeLen G₀ ℓ₀) P_u + walkLength (safeLen G₀ ℓ₀) P_v := by
        rw [walkLength_eq_sum_of_isPath _ hP_uv₀,
          walkLength_eq_sum_of_nodup _ (isPath_nodup_edges hPu_path),
          walkLength_eq_sum_of_nodup _ (isPath_nodup_edges hPv_path),
          hconcat, hrev_rv, walkEdges_append, walkEdges_walkRev, ← hPu_eq, ← hPv_eq']
        exact Finset.sum_union hdisj_uv
      rw [hlen_u, hlen_v, ← hlen_sum, he_len]
      rfl
    · simp only [hroot₀, ↓reduceIte]
      have hPu_G₀ : walkEdges P_u ⊆ G₀.E := by
        rw [hPu_eq, forestPath_subgraph hT₀.isForest hF_sub_T₀ hru₀_spec.2]
        exact no_bridge_in_endpoint_path hT₀ hR_bf hr₀_R hord hpi_br hu₀V hv₀V (hTp₀ e heG₀)
          (Or.inl hroot₀)
      have hPv_G₀ : walkEdges P_v ⊆ G₀.E := by
        have hvu_G₀ : walkEdges (T₀.forestPath v₀ u₀) ⊆ G₀.E := by
          rw [forestPath_rev hT₀.isForest (hT₀.connected hu₀V hv₀V), walkEdges_walkRev]
          exact hTp₀ e heG₀
        rw [hPv_eq, forestPath_subgraph hT₀.isForest hF_sub_T₀ hrv₀_spec.2]
        exact no_bridge_in_endpoint_path hT₀ hR_bf hr₀_R hord hpi_br hv₀V hu₀V hvu_G₀
          (Or.inl (Ne.symm hroot₀))
      rw [hwalk_eq_len (isPath_nodup_edges hPu_path) hPu_RF hPu_G₀,
        hwalk_eq_len (isPath_nodup_edges hPv_path) hPv_RF hPv_G₀, he_len]
      change 1 + (walkLength (safeLen G₀ ℓ₀) P_u + walkLength (safeLen G₀ ℓ₀) P_v) / safeLen G₀ ℓ₀ e =
        1 + (walkLength (safeLen G₀ ℓ₀) (F_orig.forestPath u₀ (RF_orig.root u₀)) +
          walkLength (safeLen G₀ ℓ₀) (F_orig.forestPath v₀ (RF_orig.root v₀))) / safeLen G₀ ℓ₀ e
      rw [hPu_eq, hPv_eq]

end MinCostFlow.LSF
