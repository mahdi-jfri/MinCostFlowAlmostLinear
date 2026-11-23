module

public import MinCostFlow.LinkCut.ForestPhi
import Mathlib.Tactic

/-!
# Invariant and Potential Lemmas for Single-Tree Replacement and `detachRight`

This file proves `LctInvWith` preservation and `sumTreePhi`/`heavyCount` equations for:

1. `replaceSameIds_spec`: replacing `t ∈ trees` by `t'` with equal `evalPairs` and `ppar`
   (covering `splay`, `findLeftmost`, and `applyTagNode`).
2. `detachRight_spec`: detaching the right child `R` of root `x` into a dashed child with `ppar = x`,
   conserving `sumTreePhi` exactly and increasing `heavyCount` by at most `1`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### Shared list/tree replacement helpers -/

theorem treeIds_eq_of_evalPairs {P : LctPayload α σ τ} {s₁ s₂ : SplayState α σ τ}
    {t₁ t₂ : AuxTree}
    (h : SplayState.evalPairs P s₁ t₁ false P.idTag =
      SplayState.evalPairs P s₂ t₂ false P.idTag) :
    treeIds P s₁ t₁ = treeIds P s₂ t₂ := by
  simp [treeIds, h]

theorem treeIds_agree {P : LctPayload α σ τ} {s₁ s₂ : SplayState α σ τ}
    {t : AuxTree} (hag : ∀ u ∈ t.toList, s₁.nodes u = s₂.nodes u) :
    treeIds P s₁ t = treeIds P s₂ t := by
  simp only [treeIds, SplayState.evalPairs_agree P hag]

theorem listHead0_append_of_ne_nil {xs ys : List ℕ} (hxs : xs ≠ []) :
    listHead0 (xs ++ ys) = listHead0 xs := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons a rest => simp [listHead0]

theorem flatMap_perm_of_replace {ts : List AuxTree} {t t' : AuxTree} (ht : t ∈ ts)
    (hp : t'.toList.Perm t.toList) :
    ((t' :: ts.erase t).flatMap AuxTree.toList).Perm (ts.flatMap AuxTree.toList) := by
  have h1 : (ts.flatMap AuxTree.toList).Perm ((t :: ts.erase t).flatMap AuxTree.toList) :=
    (List.perm_cons_erase ht).flatMap (fun _ _ => List.Perm.refl _)
  refine List.Perm.trans ?_ h1.symm
  simp only [List.flatMap_cons]
  exact hp.append_right _

theorem erase_flatMap_disjoint_of_nodup {ts : List AuxTree} {t : AuxTree} (ht : t ∈ ts)
    (hnd : (ts.flatMap AuxTree.toList).Nodup) :
    ∀ u ∈ (ts.erase t).flatMap AuxTree.toList, u ∉ t.toList := by
  have h1 : (ts.flatMap AuxTree.toList).Perm ((t :: ts.erase t).flatMap AuxTree.toList) :=
    (List.perm_cons_erase ht).flatMap (fun _ _ => List.Perm.refl _)
  have hnd2 := h1.nodup_iff.mp hnd
  simp only [List.flatMap_cons, List.nodup_append] at hnd2
  intro u hu hut
  exact hnd2.2.2 u hut u hu rfl

/-- Last node in a nonempty list `xs`, defaulting to `0` on `[]`. -/
def listLast0 : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | _ :: xs => listLast0 xs

theorem listHead0_reverse_eq_listLast0 :
    ∀ xs : List ℕ, listHead0 xs.reverse = listLast0 xs
  | [] => rfl
  | [x] => by simp [listHead0, listLast0]
  | x :: y :: rest => by
      have hne : (y :: rest).reverse ≠ [] := by
        simp only [ne_eq, List.reverse_eq_nil_iff]; exact List.cons_ne_nil _ _
      rw [List.reverse_cons, listHead0_append_of_ne_nil hne]
      dsimp only [listLast0]
      exact listHead0_reverse_eq_listLast0 (y :: rest)

theorem listLast0_reverse_eq_listHead0 (xs : List ℕ) :
    listLast0 xs.reverse = listHead0 xs := by
  simpa using (listHead0_reverse_eq_listLast0 xs.reverse).symm

theorem filter_cons_length {β : Type*} (p : β → Bool) (a : β) (l : List β) :
    ((a :: l).filter p).length = (if p a then 1 else 0) + (l.filter p).length := by
  rw [List.filter_cons]; cases p a <;> simp [Nat.add_comm]

theorem filter_cons_map_sum {β : Type*} (p : β → Bool) (f : β → ℕ) (a : β) (l : List β) :
    (((a :: l).filter p).map f).sum = (if p a then f a else 0) + ((l.filter p).map f).sum := by
  rw [List.filter_cons]; cases p a <;> simp

/-! ### Transition 1: Replacing `t ∈ trees` by `t'` preserving `evalPairs` and `ppar` -/

theorem replaceSameIds_spec {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {s' : SplayState α σ τ} {t t' : AuxTree}
    (ht : t ∈ trees) (ht'_ne : t' ≠ .leaf)
    (ht'_inv : SplayState.TreeInv P s' t')
    (hperm : t'.toList.Perm t.toList)
    (hev : SplayState.evalPairs P s' t' false P.idTag =
      SplayState.evalPairs P st.splay t false P.idTag)
    (hpp : (s'.nodes t'.rootId).ppar = (st.splay.nodes t.rootId).ppar)
    (hout : ∀ u ∉ t.toList, s'.nodes u = st.splay.nodes u) :
    let st' : LctState α σ τ := { st with splay := s' }
    let trees' := t' :: trees.erase t
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    LctInvWith P st' trees' freeList depth ∧
    heavyCount P st' = heavyCount P st ∧
    sumTreePhi P st' + t.treePhi v = sumTreePhi P st + t'.treePhi v ∧
    ∀ z ∈ trees'.flatMap AuxTree.toList,
      inducedSubPar P s' trees' z = inducedSubPar P st.splay trees z := by
  intro st' trees' active par v
  have hact_perm : (trees'.flatMap AuxTree.toList).Perm active :=
    flatMap_perm_of_replace ht hperm
  have hact_nd : (trees'.flatMap AuxTree.toList).Nodup :=
    hact_perm.nodup_iff.mpr W.activeNodup
  have hdisj : ∀ u ∈ (trees.erase t).flatMap AuxTree.toList, u ∉ t.toList :=
    erase_flatMap_disjoint_of_nodup ht W.activeNodup
  have hpar_eq : ∀ x, inducedSubPar P s' trees' x = par x := by
    intro x
    dsimp only [par]
    by_cases hx_act : x ∈ active
    · have hx_act' : x ∈ trees'.flatMap AuxTree.toList := hact_perm.mem_iff.mpr hx_act
      by_cases hx_t : x ∈ t.toList
      · have hx_t' : x ∈ t'.toList := hperm.mem_iff.mpr hx_t
        rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees']) hx_t',
          inducedSubPar_eq_of_mem W.activeNodup ht hx_t,
          treeIds_eq_of_evalPairs hev, hpp]
      · have hx_er : x ∈ (trees.erase t).flatMap AuxTree.toList := by
          rcases List.mem_flatMap.mp hx_act' with ⟨a, ha, hxa⟩
          simp only [trees', List.mem_cons] at ha
          rcases ha with rfl | ha_er
          · exact absurd (hperm.mem_iff.mp hxa) hx_t
          · exact List.mem_flatMap.mpr ⟨a, ha_er, hxa⟩
        obtain ⟨a, ha_er, hxa⟩ := List.mem_flatMap.mp hx_er
        have ha_ts : a ∈ trees := List.mem_of_mem_erase ha_er
        rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees', ha_er]) hxa,
          inducedSubPar_eq_of_mem W.activeNodup ha_ts hxa]
        have hag_a : ∀ u ∈ a.toList, s'.nodes u = st.splay.nodes u := fun u hu =>
          hout u (hdisj u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))
        rw [treeIds_agree hag_a, hag_a a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))]
    · have hx_nact' : x ∉ trees'.flatMap AuxTree.toList := fun hm => hx_act (hact_perm.mem_iff.mp hm)
      rw [inducedSubPar_eq_zero_of_not_mem hx_nact', inducedSubPar_eq_zero_of_not_mem hx_act]
  have hpar_fun : inducedSubPar P s' trees' = par := funext hpar_eq
  have hfl : FreeListInv s' st.freeHead freeList :=
    FreeListInv_agree W.freeListInv (fun e he => by
      have := hout e (fun hmt => W.active_of_freeList_disjoint he
        (List.mem_flatMap.mpr ⟨t, ht, hmt⟩))
      rw [this])
  have hW' : LctInvWith P st' trees' freeList depth :=
    { treesNonEmpty := fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha_er
        · exact ht'_ne
        · exact W.treesNonEmpty a (List.mem_of_mem_erase ha_er)
      treesInv := fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha_er
        · exact ht'_inv
        · have ha_ts := List.mem_of_mem_erase ha_er
          exact SplayState.TreeInv_agree (W.treesInv a ha_ts)
            (fun u hu => (hout u (hdisj u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))).symm)
      activeNodup := hact_nd
      activeValid := fun x hx => W.activeValid x (hact_perm.mem_iff.mp hx)
      verticesActive := fun v hv => hact_perm.symm.mem_iff.mp (W.verticesActive v hv)
      freeNodup := W.freeNodup
      freeValid := W.freeValid
      partitionSlots := fun e he => by
        rw [hact_perm.mem_iff]; exact W.partitionSlots e he
      freeListInv := hfl
      pparActive := fun a ha hp => by
        rw [hact_perm.mem_iff]
        rcases List.mem_cons.mp ha with rfl | ha_er
        · rw [hpp] at hp ⊢; exact W.pparActive t ht hp
        · have ha_ts := List.mem_of_mem_erase ha_er
          have hrt_eq := hout a.rootId (hdisj a.rootId
            (List.mem_flatMap.mpr ⟨a, ha_er, AuxTree.rootId_mem (W.treesNonEmpty a ha_ts)⟩))
          rw [hrt_eq] at hp ⊢
          exact W.pparActive a ha_ts hp
      acyclic := fun x hx hp => by
        rw [hpar_fun] at hp ⊢
        exact W.acyclic x (hact_perm.mem_iff.mp hx) hp
      vertexParEdge := fun x hx hp => by
        rw [hpar_fun] at hp ⊢
        exact W.vertexParEdge x hx hp
      edgeParVertex := fun e he hes => by
        rw [hpar_fun]
        exact W.edgeParVertex e (hact_perm.mem_iff.mp he) hes
      edgeUniqueChild := fun e he hes => by
        rcases W.edgeUniqueChild e (hact_perm.mem_iff.mp he) hes with ⟨w, hw, huniq⟩
        refine ⟨w, ?_, ?_⟩
        · dsimp only [st', active] at *; simp only [hact_perm.mem_iff, hpar_fun]; exact hw
        · intro y hy
          dsimp only [st', active] at hy
          simp only [hact_perm.mem_iff, hpar_fun] at hy
          exact huniq y hy }
  rcases LctInvWith_canon_potentials W with ⟨hH_old, hPhi_old⟩
  rcases LctInvWith_canon_potentials hW' with ⟨hH_new, hPhi_new⟩
  let active' := trees'.flatMap AuxTree.toList
  have hrep_eq : ∀ u, repSize active' (inducedSubPar P s' trees') u = repSize active par u := by
    intro u
    dsimp only [repSize, active']
    rw [hpar_fun, hact_perm.length_eq]
    exact (hact_perm.filter _).length_eq
  have h_er_agree : ∀ a ∈ trees.erase t,
      (s'.nodes a.rootId).ppar = (st.splay.nodes a.rootId).ppar ∧
      treeIds P s' a = treeIds P st.splay a := by
    intro a ha_er
    have ha_ts := List.mem_of_mem_erase ha_er
    have hag : ∀ u ∈ a.toList, s'.nodes u = st.splay.nodes u := fun u hu =>
      hout u (hdisj u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))
    exact ⟨by rw [hag a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))], treeIds_agree hag⟩
  have ht_heavy : isHeavyEdge P s' active' (inducedSubPar P s' trees') t' =
      isHeavyEdge P st.splay active par t := by
    simp only [isHeavyEdge, hpp, hrep_eq, treeIds_eq_of_evalPairs hev]
  have h_er_heavy : ∀ a ∈ trees.erase t,
      isHeavyEdge P s' active' (inducedSubPar P s' trees') a =
      isHeavyEdge P st.splay active par a := by
    intro a ha
    have ha' := h_er_agree a ha
    simp only [isHeavyEdge, ha'.1, ha'.2, hrep_eq]
  have hheavy_eq : heavyCount P st' = heavyCount P st := by
    rw [hH_new, hH_old]
    have hperm_t : trees.Perm (t :: trees.erase t) := List.perm_cons_erase ht
    have hlen_old : heavyCountList P st.splay active par trees =
        (if isHeavyEdge P st.splay active par t then 1 else 0) +
          ((trees.erase t).filter (isHeavyEdge P st.splay active par)).length := by
      dsimp only [heavyCountList]
      rw [(hperm_t.filter _).length_eq, filter_cons_length]
    have hlen_new : heavyCountList P s' active' (inducedSubPar P s' trees') trees' =
        (if isHeavyEdge P s' active' (inducedSubPar P s' trees') t' then 1 else 0) +
          ((trees.erase t).filter (isHeavyEdge P s' active' (inducedSubPar P s' trees'))).length := by
      dsimp only [heavyCountList]
      rw [show trees' = t' :: trees.erase t from rfl, filter_cons_length]
    rw [hlen_new, hlen_old, ht_heavy]
    congr 1
    exact congrArg List.length (List.filter_congr (fun a ha => by
      simp only [h_er_heavy a ha]))
  have hv_eq : vSize P s' active' (inducedSubPar P s' trees') trees' = v := by
    funext u
    dsimp only [v, vSize, active']
    have hperm_t : trees.Perm (t :: trees.erase t) := List.perm_cons_erase ht
    have hsum_old : ((trees.filter (fun a => (st.splay.nodes a.rootId).ppar == u)).map
        (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum =
        (if (st.splay.nodes t.rootId).ppar == u then
          repSize active par (listHead0 (treeIds P st.splay t)) else 0) +
        (((trees.erase t).filter (fun a => (st.splay.nodes a.rootId).ppar == u)).map
          (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum := by
      rw [((hperm_t.filter _).map _).sum_eq, filter_cons_map_sum]
    have hsum_new : ((trees'.filter (fun a => (s'.nodes a.rootId).ppar == u)).map
        (fun a => repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' a)))).sum =
        (if (s'.nodes t'.rootId).ppar == u then
          repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' t')) else 0) +
        (((trees.erase t).filter (fun a => (s'.nodes a.rootId).ppar == u)).map
          (fun a => repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' a)))).sum := by
      rw [show trees' = t' :: trees.erase t from rfl, filter_cons_map_sum]
    rw [hsum_new, hsum_old, hpp, hrep_eq, treeIds_eq_of_evalPairs hev]
    congr 1
    have hfilt : (trees.erase t).filter (fun a => (s'.nodes a.rootId).ppar == u) =
        (trees.erase t).filter (fun a => (st.splay.nodes a.rootId).ppar == u) :=
      List.filter_congr (fun a ha => by rw [(h_er_agree a ha).1])
    rw [hfilt]
    congr 1
    refine List.map_congr_left (fun a ha => ?_)
    have ha' := h_er_agree a (List.mem_filter.mp ha).1
    rw [hrep_eq, ha'.2]
  have hphi_eq : sumTreePhi P st' + t.treePhi v = sumTreePhi P st + t'.treePhi v := by
    rw [hPhi_new, hPhi_old, hv_eq]
    have hperm_t : trees.Perm (t :: trees.erase t) := List.perm_cons_erase ht
    have hsum_old : sumTreePhiList v trees = t.treePhi v + sumTreePhiList v (trees.erase t) := by
      dsimp only [sumTreePhiList]
      rw [(hperm_t.map _).sum_eq, List.map_cons, List.sum_cons]
    have hsum_new : sumTreePhiList v trees' = t'.treePhi v + sumTreePhiList v (trees.erase t) := by
      dsimp only [sumTreePhiList, trees']
      rw [List.map_cons, List.sum_cons]
    rw [hsum_new, hsum_old]
    omega
  exact ⟨hW', hheavy_eq, hphi_eq, fun z _ => hpar_eq z⟩

/-! ### Transition 2: `detachRight` -/

theorem detachRight_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {x : ℕ} {L R : AuxTree}
    (ht : AuxTree.node x L R ∈ trees)
    (hrev : (st.splay.nodes x).rev = false)
    (htag : (st.splay.nodes x).tag = P.idTag) :
    let s' := SplayState.detachRight P st.splay x
    let st' : LctState α σ τ := { st with splay := s' }
    let tL := AuxTree.node x L .leaf
    let trees' := if R = .leaf then trees else tL :: R :: trees.erase (.node x L R)
    let par := inducedSubPar P st.splay trees
    LctInvWith P st' trees' freeList depth ∧
    sumTreePhi P st' = sumTreePhi P st ∧
    (R = .leaf → heavyCount P st' = heavyCount P st) ∧
    (R ≠ .leaf →
      heavyCount P st' = heavyCount P st +
        (if isHeavyEdge P s' (trees'.flatMap AuxTree.toList)
          (inducedSubPar P s' trees') R then 1 else 0)) ∧
    heavyCount P st' ≤ heavyCount P st + 1 ∧
    ∀ z, inducedSubPar P s' trees' z = par z := by
  intro s' st' tL trees' par
  let active := trees.flatMap AuxTree.toList
  have hdet := SplayState.detachRight_preserves hL (W.treesInv _ ht) hrev htag
  rcases hdet with ⟨htL_inv, _, _, hx_pp, _, hev_L, hR_spec, hout⟩
  have hdisj_er := erase_flatMap_disjoint_of_nodup ht W.activeNodup
  cases hRc : R with
  | leaf =>
      subst hRc
      have htrees'_eq : trees' = trees := by simp [trees']
      have hev_eq : SplayState.evalPairs P s' tL false P.idTag =
          SplayState.evalPairs P st.splay (.node x L .leaf) false P.idTag := by
        dsimp only [tL]
        rw [hev_L]
        simp [SplayState.evalPairs, hrev, htag, hL.compTag_id_left, hL.actVal_id]
      have hW_same := replaceSameIds_spec W ht (by simp) htL_inv (List.Perm.refl _)
        hev_eq hx_pp (fun u hu => hout u hu)
      rcases hW_same with ⟨hW', hH, hPhi, hpar_sub⟩
      have ht_perm : trees.Perm (tL :: trees.erase tL) := List.perm_cons_erase ht
      have hfm : (trees.flatMap AuxTree.toList).Perm ((tL :: trees.erase tL).flatMap AuxTree.toList) :=
        ht_perm.flatMap (fun _ _ => List.Perm.refl _)
      have hpar_eq : ∀ z, inducedSubPar P s' trees z = par z := by
        intro z
        have hnd2 : ((tL :: trees.erase tL).flatMap AuxTree.toList).Nodup :=
          hfm.nodup_iff.mp W.activeNodup
        dsimp only [par]
        rw [inducedSubPar_perm ht_perm W.activeNodup z]
        by_cases hz : z ∈ (tL :: trees.erase tL).flatMap AuxTree.toList
        · exact hpar_sub z hz
        · have hz2 : z ∉ trees.flatMap AuxTree.toList := fun hm => hz (hfm.mem_iff.mp hm)
          rw [inducedSubPar_eq_zero_of_not_mem hz, inducedSubPar_eq_zero_of_not_mem hz2]
      have hpar_fun : inducedSubPar P s' trees = par := funext hpar_eq
      have hW_trees : LctInvWith P st' trees freeList depth :=
        { treesNonEmpty := fun a ha => W.treesNonEmpty a ha
          treesInv := fun a ha => hW'.treesInv a (ht_perm.mem_iff.mp ha)
          activeNodup := W.activeNodup
          activeValid := W.activeValid
          verticesActive := W.verticesActive
          freeNodup := W.freeNodup
          freeValid := W.freeValid
          partitionSlots := W.partitionSlots
          freeListInv := hW'.freeListInv
          pparActive := fun a ha hp =>
            hfm.mem_iff.mpr (hW'.pparActive a (ht_perm.mem_iff.mp ha) hp)
          acyclic := fun z hz hp => by
            rw [hpar_fun] at hp ⊢; exact W.acyclic z hz hp
          vertexParEdge := fun z hz hp => by
            rw [hpar_fun] at hp ⊢; exact W.vertexParEdge z hz hp
          edgeParVertex := fun e he hes => by
            rw [hpar_fun]; exact W.edgeParVertex e he hes
          edgeUniqueChild := fun e he hes => by
            rw [hpar_fun]; exact W.edgeUniqueChild e he hes }
      have hH' : heavyCount P st' = heavyCount P st := hH
      have hPhi' : sumTreePhi P st' = sumTreePhi P st := Nat.add_right_cancel hPhi
      have hH_le : heavyCount P st' ≤ heavyCount P st + 1 := Nat.le_succ_of_le (le_of_eq hH')
      rw [htrees'_eq]
      exact ⟨hW_trees, hPhi', fun _ => hH', fun h => absurd rfl h, hH_le, hpar_eq⟩
  | node rid rL rR =>
      subst hRc
      have hR_ne : AuxTree.node rid rL rR ≠ .leaf := by simp
      let trees₂ : List AuxTree :=
        tL :: AuxTree.node rid rL rR :: trees.erase (.node x L (.node rid rL rR))
      have htrees'_eq : trees' = trees₂ := by dsimp only [trees', trees₂]; simp
      rcases hR_spec hR_ne with ⟨hR_inv, hR_pp, hR_ev⟩
      have hx_pp' : (s'.nodes x).ppar = (st.splay.nodes x).ppar := hx_pp
      have hev_L' : SplayState.evalPairs P s' tL false P.idTag =
          SplayState.evalPairs P st.splay L false P.idTag ++ [(x, (st.splay.nodes x).val)] := hev_L
      have hR_pp' : (s'.nodes (AuxTree.node rid rL rR).rootId).ppar = x := hR_pp
      have hR_ev' : SplayState.evalPairs P s' (.node rid rL rR) false P.idTag =
          SplayState.evalPairs P st.splay (.node rid rL rR) false P.idTag := hR_ev
      have hnd_orig := (W.treesInv _ ht).nodup
      rcases AuxTree.nodup_node_unfold hnd_orig with ⟨hL_nd, hx_nL, hR_nd, hx_nR, hdisj_LR⟩
      have hperm_node : (tL.toList ++ (AuxTree.node rid rL rR).toList).Perm
          (AuxTree.node x L (.node rid rL rR)).toList := by
        simp only [tL, AuxTree.toList, List.append_nil, List.append_assoc]
        exact List.Perm.refl _
      have hact_perm : (trees₂.flatMap AuxTree.toList).Perm active := by
        have h1 : active.Perm
            (((.node x L (.node rid rL rR)) :: trees.erase (.node x L (.node rid rL rR))).flatMap
              AuxTree.toList) :=
          (List.perm_cons_erase ht).flatMap (fun _ _ => List.Perm.refl _)
        refine List.Perm.trans ?_ h1.symm
        simp only [trees₂, List.flatMap_cons]
        rw [← List.append_assoc tL.toList]
        exact hperm_node.append_right _
      have hact_nd : (trees₂.flatMap AuxTree.toList).Nodup := hact_perm.nodup_iff.mpr W.activeNodup
      have hev_orig : SplayState.evalPairs P st.splay (.node x L (.node rid rL rR)) false P.idTag =
          SplayState.evalPairs P st.splay L false P.idTag ++ [(x, (st.splay.nodes x).val)] ++
            SplayState.evalPairs P st.splay (.node rid rL rR) false P.idTag := by
        simp [SplayState.evalPairs, hrev, htag, hL.compTag_id_left, hL.actVal_id]
      have hpar_eq : ∀ z, inducedSubPar P s' trees₂ z = par z := by
        intro z
        dsimp only [par]
        by_cases hz_act : z ∈ active
        · have hz_act' : z ∈ trees₂.flatMap AuxTree.toList := hact_perm.mem_iff.mpr hz_act
          by_cases hz_L : z ∈ tL.toList
          · have hz_orig : z ∈ (AuxTree.node x L (.node rid rL rR)).toList :=
              hperm_node.mem_iff.mp (List.mem_append_left _ hz_L)
            rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees₂]) hz_L,
              inducedSubPar_eq_of_mem W.activeNodup ht hz_orig]
            change chainPred (s'.nodes x).ppar (treeIds P s' tL) z = _
            rw [hx_pp']
            have hids_orig : treeIds P st.splay (.node x L (.node rid rL rR)) =
                treeIds P s' tL ++ treeIds P s' (.node rid rL rR) := by
              simp only [treeIds, hev_orig, hev_L', hR_ev', List.map_append]
            rw [hids_orig]
            exact (chainPred_mem_append_left ((mem_treeIds_iff P s' tL z).mpr hz_L)).symm
          · by_cases hz_R : z ∈ (AuxTree.node rid rL rR).toList
            · have hz_orig : z ∈ (AuxTree.node x L (.node rid rL rR)).toList :=
                hperm_node.mem_iff.mp (List.mem_append_right _ hz_R)
              rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees₂]) hz_R,
                inducedSubPar_eq_of_mem W.activeNodup ht hz_orig]
              have hids_orig : treeIds P st.splay (.node x L (.node rid rL rR)) =
                  treeIds P s' tL ++ treeIds P s' (.node rid rL rR) := by
                simp only [treeIds, hev_orig, hev_L', hR_ev', List.map_append]
              have hnd_ids := treeIds_nodup (W.treesInv _ ht)
              rw [hids_orig] at hnd_ids
              have hlast_tL : (treeIds P s' tL).getLast? = some x := by
                simp only [treeIds, hev_L', List.map_append, List.map_cons, List.map_nil]
                rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
                rfl
              rw [hids_orig, chainPred_mem_append_right hnd_ids ((mem_treeIds_iff P s' _ z).mpr hz_R)
                hlast_tL, hR_pp']
            · have hz_er : z ∈ (trees.erase (.node x L (.node rid rL rR))).flatMap AuxTree.toList := by
                rcases List.mem_flatMap.mp hz_act' with ⟨a, ha, hza⟩
                rcases List.mem_cons.mp ha with rfl | ha'
                · exact absurd hza hz_L
                · rcases List.mem_cons.mp ha' with rfl | ha''
                  · exact absurd hza hz_R
                  · exact List.mem_flatMap.mpr ⟨a, ha'', hza⟩
              obtain ⟨a, ha_er, hza⟩ := List.mem_flatMap.mp hz_er
              have ha_ts := List.mem_of_mem_erase ha_er
              rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees₂, ha_er]) hza,
                inducedSubPar_eq_of_mem W.activeNodup ha_ts hza]
              have hag_a : ∀ u ∈ a.toList, s'.nodes u = st.splay.nodes u := fun u hu =>
                hout u (hdisj_er u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))
              rw [treeIds_agree hag_a, hag_a a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))]
        · have hz_act' : z ∉ trees₂.flatMap AuxTree.toList := fun hm => hz_act (hact_perm.mem_iff.mp hm)
          rw [inducedSubPar_eq_zero_of_not_mem hz_act', inducedSubPar_eq_zero_of_not_mem hz_act]
      have hpar_fun : inducedSubPar P s' trees₂ = par := funext hpar_eq
      have hfl : FreeListInv s' st.freeHead freeList :=
        FreeListInv_agree W.freeListInv (fun e he => by
          have := hout e (fun hm => W.active_of_freeList_disjoint he
            (List.mem_flatMap.mpr ⟨.node x L (.node rid rL rR), ht, hm⟩))
          rw [this])
      have hW' : LctInvWith P st' trees₂ freeList depth :=
        { treesNonEmpty := fun a ha => by
            rcases List.mem_cons.mp ha with rfl | ha'
            · simp [tL]
            · rcases List.mem_cons.mp ha' with rfl | ha''
              · exact hR_ne
              · exact W.treesNonEmpty a (List.mem_of_mem_erase ha'')
          treesInv := fun a ha => by
            rcases List.mem_cons.mp ha with rfl | ha'
            · exact htL_inv
            · rcases List.mem_cons.mp ha' with rfl | ha''
              · exact hR_inv
              · have ha_ts := List.mem_of_mem_erase ha''
                exact SplayState.TreeInv_agree (W.treesInv a ha_ts)
                  (fun u hu => (hout u (hdisj_er u (List.mem_flatMap.mpr ⟨a, ha'', hu⟩))).symm)
          activeNodup := hact_nd
          activeValid := fun z hz => W.activeValid z (hact_perm.mem_iff.mp hz)
          verticesActive := fun v hv => hact_perm.symm.mem_iff.mp (W.verticesActive v hv)
          freeNodup := W.freeNodup
          freeValid := W.freeValid
          partitionSlots := fun e he => by
            rw [hact_perm.mem_iff]; exact W.partitionSlots e he
          freeListInv := hfl
          pparActive := fun a ha hp => by
            dsimp only [st'] at hp ⊢
            rw [hact_perm.mem_iff]
            rcases List.mem_cons.mp ha with rfl | ha'
            · change (s'.nodes x).ppar ≠ 0 at hp
              change (s'.nodes x).ppar ∈ active
              rw [hx_pp'] at hp ⊢; exact W.pparActive _ ht hp
            · rcases List.mem_cons.mp ha' with rfl | ha''
              · rw [hR_pp'] at hp ⊢
                exact List.mem_flatMap.mpr ⟨.node x L (.node rid rL rR), ht, by simp [AuxTree.toList]⟩
              · have ha_ts := List.mem_of_mem_erase ha''
                have hrt_eq := hout a.rootId (hdisj_er a.rootId
                  (List.mem_flatMap.mpr ⟨a, ha'', AuxTree.rootId_mem (W.treesNonEmpty a ha_ts)⟩))
                rw [hrt_eq] at hp ⊢
                exact W.pparActive a ha_ts hp
          acyclic := fun z hz hp => by
            rw [hpar_fun] at hp ⊢; exact W.acyclic z (hact_perm.mem_iff.mp hz) hp
          vertexParEdge := fun z hz hp => by
            rw [hpar_fun] at hp ⊢; exact W.vertexParEdge z hz hp
          edgeParVertex := fun e he hes => by
            rw [hpar_fun]; exact W.edgeParVertex e (hact_perm.mem_iff.mp he) hes
          edgeUniqueChild := fun e he hes => by
            rcases W.edgeUniqueChild e (hact_perm.mem_iff.mp he) hes with ⟨w, hw, huniq⟩
            refine ⟨w, ?_, ?_⟩
            · dsimp only [st', active] at *; simp only [hact_perm.mem_iff, hpar_fun]; exact hw
            · intro y hy; dsimp only [st', active] at hy; simp only [hact_perm.mem_iff, hpar_fun] at hy
              exact huniq y hy }
      rcases LctInvWith_canon_potentials W with ⟨hH_old, hPhi_old⟩
      rcases LctInvWith_canon_potentials hW' with ⟨hH_new, hPhi_new⟩
      let active₂ := trees₂.flatMap AuxTree.toList
      let v := vSize P st.splay active par trees
      let v' := vSize P s' active₂ (inducedSubPar P s' trees₂) trees₂
      have hrep_eq : ∀ u, repSize active₂ (inducedSubPar P s' trees₂) u = repSize active par u := by
        intro u
        dsimp only [repSize, active₂]
        rw [hpar_fun, hact_perm.length_eq]
        exact (hact_perm.filter _).length_eq
      have h_er_agree : ∀ a ∈ trees.erase (.node x L (.node rid rL rR)),
          (s'.nodes a.rootId).ppar = (st.splay.nodes a.rootId).ppar ∧
          treeIds P s' a = treeIds P st.splay a := by
        intro a ha_er
        have ha_ts := List.mem_of_mem_erase ha_er
        have hag : ∀ u ∈ a.toList, s'.nodes u = st.splay.nodes u := fun u hu =>
          hout u (hdisj_er u (List.mem_flatMap.mpr ⟨a, ha_er, hu⟩))
        exact ⟨by rw [hag a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))], treeIds_agree hag⟩
      have hx_nin_R : x ∉ (AuxTree.node rid rL rR).toList := hx_nR
      have hids_tL : listHead0 (treeIds P s' tL) =
          listHead0 (treeIds P st.splay (.node x L (.node rid rL rR))) := by
        have hids_L_ne : treeIds P s' tL ≠ [] := by
          simp only [treeIds, hev_L', List.map_append, List.map_cons, List.map_nil, ne_eq,
            List.append_eq_nil_iff, List.cons_ne_nil, and_false, not_false_eq_true]
        have hids_eq : treeIds P st.splay (.node x L (.node rid rL rR)) =
            treeIds P s' tL ++ treeIds P s' (.node rid rL rR) := by
          simp only [treeIds, hev_orig, hev_L', hR_ev', List.map_append]
        rw [hids_eq, listHead0_append_of_ne_nil hids_L_ne]
      have h_v'_gen : ∀ u, v' u = v u +
          (if x == u then repSize active par (listHead0 (treeIds P s' (.node rid rL rR))) else 0) := by
        intro u
        dsimp only [v', v, vSize]
        have hperm_t := List.perm_cons_erase ht
        have hsum_old : ((trees.filter (fun a => (st.splay.nodes a.rootId).ppar == u)).map
            (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum =
            (if (st.splay.nodes (AuxTree.node x L (.node rid rL rR)).rootId).ppar == u then
              repSize active par (listHead0 (treeIds P st.splay (.node x L (.node rid rL rR)))) else 0) +
            (((trees.erase (.node x L (.node rid rL rR))).filter
                (fun a => (st.splay.nodes a.rootId).ppar == u)).map
              (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum := by
          rw [((hperm_t.filter _).map _).sum_eq, filter_cons_map_sum]
        have hsum_new : ((trees₂.filter (fun a => (s'.nodes a.rootId).ppar == u)).map
            (fun a => repSize active₂ (inducedSubPar P s' trees₂) (listHead0 (treeIds P s' a)))).sum =
            (if (s'.nodes tL.rootId).ppar == u then
              repSize active₂ (inducedSubPar P s' trees₂) (listHead0 (treeIds P s' tL)) else 0) +
            ((if (s'.nodes (AuxTree.node rid rL rR).rootId).ppar == u then
              repSize active₂ (inducedSubPar P s' trees₂)
                (listHead0 (treeIds P s' (.node rid rL rR))) else 0) +
            (((trees.erase (.node x L (.node rid rL rR))).filter
                (fun a => (s'.nodes a.rootId).ppar == u)).map
              (fun a => repSize active₂ (inducedSubPar P s' trees₂) (listHead0 (treeIds P s' a)))).sum) := by
          dsimp only [trees₂]
          rw [filter_cons_map_sum, filter_cons_map_sum]
        have hfilt_er : (trees.erase (.node x L (.node rid rL rR))).filter
            (fun a => (s'.nodes a.rootId).ppar == u) =
            (trees.erase (.node x L (.node rid rL rR))).filter
              (fun a => (st.splay.nodes a.rootId).ppar == u) :=
          List.filter_congr (fun a ha => by rw [(h_er_agree a ha).1])
        have hsum_er : (((trees.erase (.node x L (.node rid rL rR))).filter
              (fun a => (s'.nodes a.rootId).ppar == u)).map
            (fun a => repSize active₂ (inducedSubPar P s' trees₂) (listHead0 (treeIds P s' a)))).sum =
            (((trees.erase (.node x L (.node rid rL rR))).filter
                (fun a => (st.splay.nodes a.rootId).ppar == u)).map
              (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum := by
          rw [hfilt_er]
          congr 1
          refine List.map_congr_left (fun a ha => ?_)
          have ha' := h_er_agree a (List.mem_filter.mp ha).1
          rw [hrep_eq, ha'.2]
        have htL_pp : ((s'.nodes tL.rootId).ppar == u) =
            ((st.splay.nodes (AuxTree.node x L (.node rid rL rR)).rootId).ppar == u) := by
          change ((s'.nodes x).ppar == u) = ((st.splay.nodes x).ppar == u)
          rw [hx_pp']
        have hR_pp_eq : ((s'.nodes (AuxTree.node rid rL rR).rootId).ppar == u) = (x == u) := by
          rw [hR_pp']
        rw [hsum_new, hsum_old, hsum_er, htL_pp, hR_pp_eq, hrep_eq, hrep_eq, hids_tL]
        omega
      have hv'_R : ∀ u ∈ (AuxTree.node rid rL rR).toList, v' u = v u := fun u hu => by
        have hux : x ≠ u := fun h => hx_nin_R (h ▸ hu)
        simp [h_v'_gen u, beq_false_of_ne hux]
      have hv'_L : ∀ u ∈ L.toList, v' u = v u := fun u hu => by
        have hux : x ≠ u := fun h => hx_nL (h ▸ hu)
        simp [h_v'_gen u, beq_false_of_ne hux]
      have hR_sz_eq : (AuxTree.node rid rL rR).treeSize v =
          repSize active par (listHead0 (treeIds P s' (.node rid rL rR))) := by
        rw [← SplayState.treeSize_agree hv'_R,
          treeSize_vSize_eq_repSize hW' (by simp [trees₂] : AuxTree.node rid rL rR ∈ trees₂),
          hrep_eq]
      have hv'_x : v' x = v x + (AuxTree.node rid rL rR).treeSize v := by
        rw [hR_sz_eq]; simp [h_v'_gen x]
      have hdet_phi := SplayState.detachRight_treePhi_eq hv'_L hv'_R hv'_x
      have hphi_eq : sumTreePhi P st' = sumTreePhi P st := by
        rw [hPhi_new, hPhi_old]
        have hperm_t := List.perm_cons_erase ht
        have hsum_old : sumTreePhiList v trees =
            (AuxTree.node x L (.node rid rL rR)).treePhi v +
              sumTreePhiList v (trees.erase (.node x L (.node rid rL rR))) := by
          dsimp only [sumTreePhiList]
          rw [(hperm_t.map _).sum_eq, List.map_cons, List.sum_cons]
        have hsum_new : sumTreePhiList v' trees₂ =
            tL.treePhi v' + ((AuxTree.node rid rL rR).treePhi v' +
              sumTreePhiList v' (trees.erase (.node x L (.node rid rL rR)))) := by
          dsimp only [sumTreePhiList, trees₂]
          simp only [List.map_cons, List.sum_cons]
        have hsum_er_eq : sumTreePhiList v' (trees.erase (.node x L (.node rid rL rR))) =
            sumTreePhiList v (trees.erase (.node x L (.node rid rL rR))) := by
          dsimp only [sumTreePhiList]
          congr 1
          refine List.map_congr_left (fun a ha => SplayState.treePhi_agree (fun u hu => ?_))
          have hux : x ≠ u := fun h => hdisj_er u (List.mem_flatMap.mpr ⟨a, ha, hu⟩)
            (h ▸ by simp [AuxTree.toList])
          simp [h_v'_gen u, beq_false_of_ne hux]
        rw [hsum_new, hsum_old, hsum_er_eq]
        have hphi2 : tL.treePhi v' + (AuxTree.node rid rL rR).treePhi v' =
            (AuxTree.node x L (.node rid rL rR)).treePhi v := by
          simpa [tL] using hdet_phi.2
        omega
      have htL_heavy : isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂) tL =
          isHeavyEdge P st.splay active par (.node x L (.node rid rL rR)) := by
        simp only [isHeavyEdge, tL, AuxTree.rootId, hx_pp', hids_tL, hrep_eq]; rfl
      have hheavy_eq : heavyCount P st' = heavyCount P st +
          (if isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂) (.node rid rL rR) then 1 else 0) := by
        have hperm_t := List.perm_cons_erase ht
        have hlen_old : heavyCountList P st.splay active par trees =
            (if isHeavyEdge P st.splay active par (.node x L (.node rid rL rR)) then 1 else 0) +
              ((trees.erase (.node x L (.node rid rL rR))).filter
                (isHeavyEdge P st.splay active par)).length := by
          dsimp only [heavyCountList]
          rw [(hperm_t.filter _).length_eq, filter_cons_length]
        have hfilt_er : (trees.erase (.node x L (.node rid rL rR))).filter
            (isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂)) =
            (trees.erase (.node x L (.node rid rL rR))).filter
              (isHeavyEdge P st.splay active par) := by
          refine List.filter_congr (fun a ha => ?_)
          have ha' := h_er_agree a ha
          simp only [isHeavyEdge, ha'.1, ha'.2, hrep_eq]
        have hH_old' : heavyCount P st =
            (if isHeavyEdge P st.splay active par (.node x L (.node rid rL rR)) then 1 else 0) +
              ((trees.erase (.node x L (.node rid rL rR))).filter
                (isHeavyEdge P st.splay active par)).length := by
          rw [hH_old]; exact hlen_old
        have hH_new' : heavyCount P st' =
            (if isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂) tL then 1 else 0) +
            ((if isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂) (.node rid rL rR) then 1 else 0) +
              ((trees.erase (.node x L (.node rid rL rR))).filter
                (isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂))).length) := by
          rw [hH_new]
          dsimp only [heavyCountList]
          change (((tL :: (.node rid rL rR) :: trees.erase (.node x L (.node rid rL rR))).filter
            (isHeavyEdge P s' active₂ (inducedSubPar P s' trees₂))).length) = _
          rw [filter_cons_length, filter_cons_length]
        rw [hH_new', hH_old', htL_heavy, hfilt_er]
        omega
      have hH_le : heavyCount P st' ≤ heavyCount P st + 1 := by
        rw [hheavy_eq]
        split_ifs <;> omega
      rw [htrees'_eq]
      exact ⟨hW', hphi_eq, fun h => absurd h hR_ne, fun _ => hheavy_eq, hH_le, hpar_eq⟩

end MinCostFlow.LinkCut
