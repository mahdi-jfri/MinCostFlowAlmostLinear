module

public import MinCostFlow.LinkCut.SplayModel
import Mathlib.Tactic

/-!
# Preservation properties for lazy splay operations

This file proves invariant preservation, logical sequence (`evalPairs`) preservation, and
structural/potential invariance for:
- `revNode`, `applyTagNode`, `pull`
- `pushDownRev`, `pushDownTag`, `pushDown`
- `pushPath`

Every theorem holds generically for any `P : LctPayload α σ τ` satisfying `P.Laws`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

namespace SplayState

variable {α σ τ : Type*}

/-! ### `revRoot` structural & potential invariance -/

theorem revRoot_toList_perm (t : AuxTree) : t.revRoot.toList.Perm t.toList := by
  cases t with
  | leaf => rfl
  | node id l r =>
      simp only [AuxTree.revRoot, AuxTree.toList]
      have h1 : (r.toList ++ [id] ++ l.toList).Perm ([id] ++ l.toList ++ r.toList) := by
        rw [List.append_assoc r.toList [id] l.toList, List.append_assoc [id] l.toList r.toList]
        exact List.perm_append_comm
      have h2 : ([id] ++ l.toList ++ r.toList).Perm (l.toList ++ [id] ++ r.toList) :=
        (List.perm_append_comm).append_right r.toList
      exact h1.trans h2

theorem revRoot_nodup {t : AuxTree} (hnd : t.toList.Nodup) : t.revRoot.toList.Nodup :=
  (revRoot_toList_perm t).nodup_iff.mpr hnd

theorem revRoot_rootId (t : AuxTree) : t.revRoot.rootId = t.rootId := by
  cases t <;> rfl

theorem revRoot_ne_leaf_iff {t : AuxTree} : t.revRoot ≠ .leaf ↔ t ≠ .leaf := by
  cases t <;> simp [AuxTree.revRoot]

theorem revRoot_countNodes (t : AuxTree) : t.revRoot.countNodes = t.countNodes := by
  cases t <;> simp [AuxTree.revRoot, AuxTree.countNodes]; omega

theorem revRoot_treeSize (vSize : ℕ → ℕ) (t : AuxTree) :
    t.revRoot.treeSize vSize = t.treeSize vSize := by
  cases t <;> simp [AuxTree.revRoot, AuxTree.treeSize]; omega

theorem revRoot_rank (vSize : ℕ → ℕ) (t : AuxTree) :
    t.revRoot.rank vSize = t.rank vSize := by
  simp only [AuxTree.rank, revRoot_treeSize]

theorem revRoot_treePhi (vSize : ℕ → ℕ) (t : AuxTree) :
    t.revRoot.treePhi vSize = t.treePhi vSize := by
  cases t with
  | leaf => rfl
  | node id l r =>
      have hr : (AuxTree.node id r l).rank vSize = (AuxTree.node id l r).rank vSize := by
        simpa [AuxTree.revRoot] using revRoot_rank vSize (.node id l r)
      simp only [AuxTree.revRoot, AuxTree.treePhi, hr]; omega

theorem revRoot_depthOf {t : AuxTree} (hnd : t.toList.Nodup) (u : ℕ) :
    t.revRoot.depthOf u = t.depthOf u := by
  cases t with
  | leaf => rfl
  | node id l r =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨_, _, _, _, hdisj⟩
      by_cases hid : u = id
      · simp [AuxTree.revRoot, AuxTree.depthOf, hid]
      · simp only [AuxTree.revRoot, AuxTree.depthOf, hid, ↓reduceIte]
        by_cases hul : u ∈ l.toList
        · have hur : u ∉ r.toList := hdisj u hul
          simp [hul, hur]
        · by_cases hur : u ∈ r.toList <;> simp [hul, hur]

theorem revRoot_pathTo {t : AuxTree} (hnd : t.toList.Nodup) (u : ℕ) :
    t.revRoot.pathTo u = t.pathTo u := by
  cases t with
  | leaf => rfl
  | node id l r =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨_, _, _, _, hdisj⟩
      by_cases hid : u = id
      · simp [AuxTree.revRoot, AuxTree.pathTo, hid]
      · simp only [AuxTree.revRoot, AuxTree.pathTo, hid, ↓reduceIte]
        by_cases hul : u ∈ l.toList
        · have hur : u ∉ r.toList := hdisj u hul
          simp [hul, hur]
        · by_cases hur : u ∈ r.toList <;> simp [hul, hur]

private theorem findSubtree_not_mem_leaf {y : ℕ} {t : AuxTree} (hy : y ∉ t.toList) :
    t.findSubtree y = .leaf := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      have h1 : id ≠ y := fun h => hy (by subst h; simp [AuxTree.toList])
      have h2 : y ∉ l.toList := fun h => hy (by simp [AuxTree.toList, h])
      have h3 : y ∉ r.toList := fun h => hy (by simp [AuxTree.toList, h])
      simp [AuxTree.findSubtree, h1, h2, ihr h3]

theorem revRoot_findSubtree_treeSize {t : AuxTree} (hnd : t.toList.Nodup)
    (vSize : ℕ → ℕ) (y : ℕ) :
    (t.revRoot.findSubtree y).treeSize vSize = (t.findSubtree y).treeSize vSize := by
  cases t with
  | leaf => rfl
  | node id l r =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨_, _, _, _, hdisj⟩
      by_cases hid : id = y
      · subst hid
        simpa [AuxTree.revRoot, AuxTree.findSubtree] using revRoot_treeSize vSize (.node id l r)
      · simp only [AuxTree.revRoot, AuxTree.findSubtree, hid, ↓reduceIte]
        by_cases hyl : y ∈ l.toList
        · have hyr : y ∉ r.toList := hdisj y hyl
          simp [hyl, hyr]
        · by_cases hyr : y ∈ r.toList
          · simp [hyl, hyr]
          · simp [hyl, hyr, findSubtree_not_mem_leaf hyl, findSubtree_not_mem_leaf hyr]

/-! ### `revNode`, `applyTagNode`, `pull` preservation -/

theorem revNode_root_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hsub : SubtreeInv P st rp (.node x l r)) :
    let st' := revNode P st x
    SubtreeInv P st' rp (.node x r l) ∧
    (∀ flip acc, evalPairs P st' (.node x r l) flip acc =
      evalPairs P st (.node x l r) (!flip) acc) ∧
    ((st'.nodes x).ppar = (st.nodes x).ppar) ∧
    (∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u) := by
  intro st'
  rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hx_nl, hr_nd, hx_nr, _⟩
  rcases hsub with ⟨hx, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
  have hst'_x : st'.nodes x =
      { st.nodes x with
        left := (st.nodes x).right
        right := (st.nodes x).left
        rev := !(st.nodes x).rev
        val := P.revVal (st.nodes x).val
        sum := P.revSum (st.nodes x).sum
        tag := P.revTag (st.nodes x).tag } := by
    simp [st', revNode, hx]
  have hst'_ne : ∀ u ≠ x, st'.nodes u = st.nodes u := fun u hu => by
    simp [st', revNode, hx, hu]
  have hev : ∀ flip acc, evalPairs P st' (.node x r l) flip acc =
      evalPairs P st (.node x l r) (!flip) acc := by
    intro flip acc
    have hev_l : ∀ b t, evalPairs P st' l b t = evalPairs P st l b t := fun b t =>
      evalPairs_agree P (fun u hu => hst'_ne u (fun h => hx_nl (h ▸ hu))) b t
    have hev_r : ∀ b t, evalPairs P st' r b t = evalPairs P st r b t := fun b t =>
      evalPairs_agree P (fun u hu => hst'_ne u (fun h => hx_nr (h ▸ hu))) b t
    cases flip
    · simp only [evalPairs, hst'_x, Bool.false_xor, Bool.not_false, Bool.true_xor,
        Bool.false_eq_true, ↓reduceIte, hev_l, hev_r]
    · simp only [evalPairs, hst'_x, Bool.true_xor, Bool.not_true, Bool.false_xor, Bool.not_not,
        Bool.false_eq_true, ↓reduceIte, hL.revVal_revVal, hL.revTag_revTag, hev_l, hev_r]
  have hr' : SubtreeInv P st' x r :=
    SubtreeInv_agree hr (fun u hu => (hst'_ne u (fun h => hx_nr (h ▸ hu))).symm)
  have hl' : SubtreeInv P st' x l :=
    SubtreeInv_agree hl (fun u hu => (hst'_ne u (fun h => hx_nl (h ▸ hu))).symm)
  have hsum' : (st'.nodes x).sum = P.listSummary (evalPairs P st' (.node x r l) false P.idTag) := by
    rw [hev false P.idTag]
    simp only [Bool.not_false]
    rw [evalPairs_true_idTag hL, LctPayload.listSummary_reverse_map hL, ← hsum, hst'_x]
  refine ⟨⟨hx, ?_, ?_, ?_, ?_, ?_, hsum', hr', hl'⟩, hev, ?_, ?_⟩
  · simp [hst'_x, hr_eq]
  · simp [hst'_x, hl_eq]
  · simp [hst'_x, hpar]
  · intro hrp; simp [hst'_x, hpp hrp]
  · simp [hst'_x, hsz, AuxTree.countNodes]; omega
  · simp [hst'_x]
  · intro u hu; exact hst'_ne u (fun h => hu (by subst h; simp [AuxTree.toList]))

theorem applyTagNode_root_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {l r : AuxTree} (t₀ : τ)
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hsub : SubtreeInv P st rp (.node x l r)) :
    let st' := applyTagNode P st x t₀
    SubtreeInv P st' rp (.node x l r) ∧
    (∀ flip acc, evalPairs P st' (.node x l r) flip acc =
      evalPairs P st (.node x l r) flip (P.compTag acc (if flip then P.revTag t₀ else t₀))) ∧
    ((st'.nodes x).ppar = (st.nodes x).ppar) ∧
    (∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u) := by
  intro st'
  rcases AuxTree.nodup_node_unfold hnd with ⟨_, hx_nl, _, hx_nr, _⟩
  rcases hsub with ⟨hx, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
  have hst'_x : st'.nodes x =
      { st.nodes x with
        val := P.actVal t₀ (st.nodes x).val
        sum := P.actSum t₀ (st.nodes x).sum
        tag := P.compTag t₀ (st.nodes x).tag } := by
    simp [st', applyTagNode, hx]
  have hst'_ne : ∀ u ≠ x, st'.nodes u = st.nodes u := fun u hu => by
    simp [st', applyTagNode, hx, hu]
  have hev : ∀ flip acc, evalPairs P st' (.node x l r) flip acc =
      evalPairs P st (.node x l r) flip
        (P.compTag acc (if flip then P.revTag t₀ else t₀)) := by
    intro flip acc
    have hev_l : ∀ b t, evalPairs P st' l b t = evalPairs P st l b t := fun b t =>
      evalPairs_agree P (fun u hu => hst'_ne u (fun h => hx_nl (h ▸ hu))) b t
    have hev_r : ∀ b t, evalPairs P st' r b t = evalPairs P st r b t := fun b t =>
      evalPairs_agree P (fun u hu => hst'_ne u (fun h => hx_nr (h ▸ hu))) b t
    cases flip
    · simp only [evalPairs, hst'_x, Bool.false_eq_true, ↓reduceIte,
        hL.actVal_comp, hL.compTag_assoc, hev_l, hev_r]
    · simp only [evalPairs, hst'_x, ↓reduceIte,
        hL.revVal_actVal, hL.revTag_comp, hL.actVal_comp, hL.compTag_assoc, hev_l, hev_r]
  have hl' : SubtreeInv P st' x l :=
    SubtreeInv_agree hl (fun u hu => (hst'_ne u (fun h => hx_nl (h ▸ hu))).symm)
  have hr' : SubtreeInv P st' x r :=
    SubtreeInv_agree hr (fun u hu => (hst'_ne u (fun h => hx_nr (h ▸ hu))).symm)
  have hsum' : (st'.nodes x).sum = P.listSummary (evalPairs P st' (.node x l r) false P.idTag) := by
    rw [hev false P.idTag]
    simp only [Bool.false_eq_true, ↓reduceIte, hL.compTag_id_left]
    rw [← hL.compTag_id_right t₀, evalPairs_compTag hL, LctPayload.listSummary_map_act hL,
      ← hsum, hst'_x]
  refine ⟨⟨hx, ?_, ?_, ?_, ?_, ?_, hsum', hl', hr'⟩, hev, ?_, ?_⟩
  · simp [hst'_x, hl_eq]
  · simp [hst'_x, hr_eq]
  · simp [hst'_x, hpar]
  · intro hrp; simp [hst'_x, hpp hrp]
  · simp [hst'_x, hsz]
  · simp [hst'_x]
  · intro u hu; exact hst'_ne u (fun h => hu (by subst h; simp [AuxTree.toList]))

theorem pull_node_build {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {l r : AuxTree}
    (hx : x ≠ 0) (hx_nl : x ∉ l.toList) (hx_nr : x ∉ r.toList)
    (hleft : (st.nodes x).left = l.rootId) (hright : (st.nodes x).right = r.rootId)
    (hpar : (st.nodes x).par = rp) (hpp : rp ≠ 0 → (st.nodes x).ppar = 0)
    (hrev : (st.nodes x).rev = false) (htag : (st.nodes x).tag = P.idTag)
    (hl : SubtreeInv P st x l) (hr : SubtreeInv P st x r) :
    let st' := pull P st x
    SubtreeInv P st' rp (.node x l r) ∧
    (st'.nodes x).rev = false ∧ (st'.nodes x).tag = P.idTag ∧
    (st'.nodes x).ppar = (st.nodes x).ppar ∧
    (∀ u ≠ x, st'.nodes u = st.nodes u) := by
  intro st'
  have hst'_ne : ∀ u ≠ x, st'.nodes u = st.nodes u := fun u hu => by
    simp [st', pull, hx, hu]
  have hszL : (if (st.nodes x).left = 0 then 0 else (st.nodes (st.nodes x).left).sz) = l.countNodes := by
    cases l with
    | leaf => simp [hleft, AuxTree.rootId, AuxTree.countNodes]
    | node lid ll lr =>
        rcases hl with ⟨hlid, _, _, _, _, hlsz, _, _, _⟩
        simp [hleft, AuxTree.rootId, hlid, hlsz]
  have hszR : (if (st.nodes x).right = 0 then 0 else (st.nodes (st.nodes x).right).sz) = r.countNodes := by
    cases r with
    | leaf => simp [hright, AuxTree.rootId, AuxTree.countNodes]
    | node rid rl rr =>
        rcases hr with ⟨hrid, _, _, _, _, hrsz, _, _, _⟩
        simp [hright, AuxTree.rootId, hrid, hrsz]
  have hsumL : (if (st.nodes x).left = 0 then P.empty else (st.nodes (st.nodes x).left).sum) =
      P.listSummary (evalPairs P st l false P.idTag) := by
    cases l with
    | leaf => simp [hleft, AuxTree.rootId, evalPairs]
    | node lid ll lr =>
        rcases hl with ⟨hlid, _, _, _, _, _, hlsum, _, _⟩
        simp [hleft, AuxTree.rootId, hlid, hlsum]
  have hsumR : (if (st.nodes x).right = 0 then P.empty else (st.nodes (st.nodes x).right).sum) =
      P.listSummary (evalPairs P st r false P.idTag) := by
    cases r with
    | leaf => simp [hright, AuxTree.rootId, evalPairs]
    | node rid rl rr =>
        rcases hr with ⟨hrid, _, _, _, _, _, hrsum, _, _⟩
        simp [hright, AuxTree.rootId, hrid, hrsum]
  have hst'_x : st'.nodes x =
      { st.nodes x with
        sz := (AuxTree.node x l r).countNodes
        sum := P.combine (P.listSummary (evalPairs P st l false P.idTag))
          (P.combine (P.single x (st.nodes x).val)
            (P.listSummary (evalPairs P st r false P.idTag))) } := by
    dsimp only [st', pull]
    rw [ite_eq_right hx]
    simp [hszL, hszR, hsumL, hsumR, AuxTree.countNodes]
  have heval_l : evalPairs P st' l false P.idTag = evalPairs P st l false P.idTag :=
    evalPairs_agree P (fun u hu => hst'_ne u (fun h => hx_nl (h ▸ hu))) false P.idTag
  have heval_r : evalPairs P st' r false P.idTag = evalPairs P st r false P.idTag :=
    evalPairs_agree P (fun u hu => hst'_ne u (fun h => hx_nr (h ▸ hu))) false P.idTag
  have hsum_eq : (st'.nodes x).sum =
      P.listSummary (evalPairs P st' (.node x l r) false P.idTag) := by
    have hev_node : evalPairs P st' (.node x l r) false P.idTag =
        evalPairs P st l false P.idTag ++ [(x, (st.nodes x).val)] ++ evalPairs P st r false P.idTag := by
      simp [evalPairs, hst'_x, hrev, htag, hL.compTag_id_left, hL.actVal_id, heval_l, heval_r]
    rw [hev_node, LctPayload.listSummary_append hL, LctPayload.listSummary_append hL,
      LctPayload.listSummary_single hL]
    simp [hst'_x, hL.combine_assoc]
  have hl' : SubtreeInv P st' x l :=
    SubtreeInv_agree hl (fun u hu => (hst'_ne u (fun h => hx_nl (h ▸ hu))).symm)
  have hr' : SubtreeInv P st' x r :=
    SubtreeInv_agree hr (fun u hu => (hst'_ne u (fun h => hx_nr (h ▸ hu))).symm)
  refine ⟨⟨hx, ?_, ?_, ?_, ?_, ?_, hsum_eq, hl', hr'⟩, ?_, ?_, ?_, hst'_ne⟩
  · simp [hst'_x, hleft]
  · simp [hst'_x, hright]
  · simp [hst'_x, hpar]
  · intro hrp; simp [hst'_x, hpp hrp]
  · simp [hst'_x]
  · simp [hst'_x, hrev]
  · simp [hst'_x, htag]
  · simp [hst'_x]

/-! ### `pushDownRev`, `pushDownTag`, `pushDown` preservation -/

theorem pushDownRev_root_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hsub : SubtreeInv P st rp (.node x l r)) :
    let l' := if (st.nodes x).rev then l.revRoot else l
    let r' := if (st.nodes x).rev then r.revRoot else r
    let st' := pushDownRev P st x
    SubtreeInv P st' rp (.node x l' r') ∧
    (st'.nodes x).rev = false ∧ (st'.nodes x).tag = (st.nodes x).tag ∧
    (st'.nodes x).ppar = (st.nodes x).ppar ∧
    (∀ flip acc, evalPairs P st' (.node x l' r') flip acc =
      evalPairs P st (.node x l r) flip acc) ∧
    (∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u) := by
  intro l' r' st'
  rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hx_nl, hr_nd, hx_nr, hdisj⟩
  rcases hsub with ⟨hx, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
  by_cases hrev : (st.nodes x).rev = true
  · have hl'_eq : l' = l.revRoot := ite_eq_left hrev
    have hr'_eq : r' = r.revRoot := ite_eq_left hrev
    let st₀ := st.updateNode x fun cur => { cur with rev := false }
    let stL := revNode P st₀ l.rootId
    have hst'_eq : st' = revNode P stL r.rootId := by
      simp only [st', pushDownRev, hx, ↓reduceIte, hrev, hl_eq, hr_eq, st₀, stL]
    have hx_node : st'.nodes x = { st.nodes x with rev := false } := by
      have hx0 : st₀.nodes x = { st.nodes x with rev := false } := by simp [st₀]
      have hxL : stL.nodes x = st₀.nodes x := by
        cases l with
        | leaf => simp [stL, revNode, AuxTree.rootId]
        | node lid _ _ =>
            have hne : x ≠ lid := fun h => hx_nl (h ▸ by simp [AuxTree.toList])
            have hlid : lid ≠ 0 := SubtreeInv_nonZero hl (by simp [AuxTree.toList])
            simp [stL, revNode, AuxTree.rootId, hlid, hne]
      have hxR : st'.nodes x = stL.nodes x := by
        cases r with
        | leaf => simp [hst'_eq, revNode, AuxTree.rootId]
        | node rid _ _ =>
            have hne : x ≠ rid := fun h => hx_nr (h ▸ by simp [AuxTree.toList])
            have hrid : rid ≠ 0 := SubtreeInv_nonZero hr (by simp [AuxTree.toList])
            simp [hst'_eq, revNode, AuxTree.rootId, hrid, hne]
      exact hxR.trans (hxL.trans hx0)
    have hx_rev_false : (st'.nodes x).rev = false := by rw [hx_node]
    have hx_fields : (st'.nodes x).tag = (st.nodes x).tag ∧
        (st'.nodes x).ppar = (st.nodes x).ppar ∧
        (st'.nodes x).val = (st.nodes x).val ∧
        (st'.nodes x).par = rp ∧
        (st'.nodes x).left = l'.rootId ∧
        (st'.nodes x).right = r'.rootId ∧
        (st'.nodes x).sz = (AuxTree.node x l' r').countNodes := by
      rw [hx_node]
      refine ⟨rfl, rfl, rfl, hpar, ?_, ?_, ?_⟩
      · simp [hl_eq, hl'_eq, revRoot_rootId]
      · simp [hr_eq, hr'_eq, revRoot_rootId]
      · simp [hsz, hl'_eq, hr'_eq, AuxTree.countNodes, revRoot_countNodes]
    have hst'_out : ∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u := by
      intro u hu
      have hux : u ≠ x := fun h => hu (by subst h; simp [AuxTree.toList])
      have hu0 : st₀.nodes u = st.nodes u := by simp [st₀, hux]
      have huL : stL.nodes u = st₀.nodes u := by
        cases l with
        | leaf => simp [stL, revNode, AuxTree.rootId]
        | node lid _ _ =>
            have hu_l : u ≠ lid := fun h => hu (by subst h; simp [AuxTree.toList])
            have hlid : lid ≠ 0 := SubtreeInv_nonZero hl (by simp [AuxTree.toList])
            simp [stL, revNode, AuxTree.rootId, hlid, hu_l]
      have huR : st'.nodes u = stL.nodes u := by
        cases r with
        | leaf => simp [hst'_eq, revNode, AuxTree.rootId]
        | node rid _ _ =>
            have hu_r : u ≠ rid := fun h => hu (by subst h; simp [AuxTree.toList])
            have hrid : rid ≠ 0 := SubtreeInv_nonZero hr (by simp [AuxTree.toList])
            simp [hst'_eq, revNode, AuxTree.rootId, hrid, hu_r]
      rw [huR, huL, hu0]
    have hl0 : SubtreeInv P st₀ x l :=
      SubtreeInv_agree hl (fun u hu => by
        have hne : u ≠ x := fun h => hx_nl (h ▸ hu)
        exact (nodes_updateNode_ne st hne _).symm)
    have hl'_sub0 : SubtreeInv P stL x l' ∧
        (∀ b acc, evalPairs P stL l' b acc = evalPairs P st₀ l (!b) acc) ∧
        (∀ u ∉ l.toList, stL.nodes u = st₀.nodes u) := by
      cases l with
      | leaf =>
          simp only [hl'_eq, AuxTree.revRoot, AuxTree.rootId, stL, revNode, ↓reduceIte]
          exact ⟨trivial, fun _ _ => rfl, fun _ _ => by simp⟩
      | node lid ll lr =>
          have hrev_l := revNode_root_preserves hL hl_nd hl0
          simp only [hl'_eq, AuxTree.revRoot, AuxTree.rootId, stL]
          exact ⟨hrev_l.1, hrev_l.2.1, hrev_l.2.2.2⟩
    have hr0 : SubtreeInv P stL x r :=
      SubtreeInv_agree hr (fun u hu => by
        have h1 : stL.nodes u = st₀.nodes u := hl'_sub0.2.2 u (fun hm => hdisj u hm hu)
        have hne : u ≠ x := fun h => hx_nr (h ▸ hu)
        have h2 : st₀.nodes u = st.nodes u := nodes_updateNode_ne st hne _
        exact (h1.trans h2).symm)
    have hr'_sub0 : SubtreeInv P st' x r' ∧
        (∀ b acc, evalPairs P st' r' b acc = evalPairs P stL r (!b) acc) ∧
        (∀ u ∉ r.toList, st'.nodes u = stL.nodes u) := by
      cases r with
      | leaf =>
          simp only [hr'_eq, AuxTree.revRoot, AuxTree.rootId, hst'_eq, revNode, ↓reduceIte]
          exact ⟨trivial, fun _ _ => rfl, fun _ _ => by simp⟩
      | node rid rl rr =>
          have hrev_r := revNode_root_preserves hL hr_nd hr0
          simp only [hr'_eq, AuxTree.revRoot, AuxTree.rootId, hst'_eq]
          exact ⟨hrev_r.1, hrev_r.2.1, hrev_r.2.2.2⟩
    have hl'_sub : SubtreeInv P st' x l' := by
      refine SubtreeInv_agree hl'_sub0.1 (fun u hu => ?_)
      have hu_l : u ∈ l.toList := by
        rw [hl'_eq] at hu; exact (revRoot_toList_perm l).mem_iff.mp hu
      exact (hr'_sub0.2.2 u (hdisj u hu_l)).symm
    have hr'_sub := hr'_sub0.1
    have hev : ∀ flip acc, evalPairs P st' (.node x l' r') flip acc =
        evalPairs P st (.node x l r) flip acc := by
      intro flip acc
      have hev_l0 : ∀ b t, evalPairs P st₀ l b t = evalPairs P st l b t := fun b t =>
        evalPairs_agree P (fun u hu => by
          have hne : u ≠ x := fun h => hx_nl (h ▸ hu)
          exact nodes_updateNode_ne st hne _) b t
      have hev_r0 : ∀ b t, evalPairs P stL r b t = evalPairs P st r b t := fun b t =>
        evalPairs_agree P (fun u hu => by
          have h1 := hl'_sub0.2.2 u (fun hm => hdisj u hm hu)
          have hne : u ≠ x := fun h => hx_nr (h ▸ hu)
          have h2 : st₀.nodes u = st.nodes u := nodes_updateNode_ne st hne _
          exact h1.trans h2) b t
      have hev_l1 : ∀ b t, evalPairs P st' l' b t = evalPairs P stL l' b t := fun b t =>
        evalPairs_agree P (fun u hu => by
          rw [hl'_eq] at hu
          exact hr'_sub0.2.2 u (hdisj u ((revRoot_toList_perm l).mem_iff.mp hu))) b t
      cases flip
      · simp only [evalPairs, hx_rev_false, hrev, hx_fields.1, hx_fields.2.2.1,
          Bool.false_xor, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
          hev_l1, hl'_sub0.2.1, hev_l0, hr'_sub0.2.1, hev_r0]
      · simp only [evalPairs, hx_rev_false, hrev, hx_fields.1, hx_fields.2.2.1,
          Bool.true_xor, Bool.not_false, Bool.not_true, ↓reduceIte,
          hev_l1, hl'_sub0.2.1, hev_l0, hr'_sub0.2.1, hev_r0]
    have hsum' : (st'.nodes x).sum = P.listSummary (evalPairs P st' (.node x l' r') false P.idTag) := by
      rw [hev false P.idTag, ← hsum, hx_node]
    refine ⟨⟨hx, hx_fields.2.2.2.2.1, hx_fields.2.2.2.2.2.1, hx_fields.2.2.2.1,
        fun hrp => hx_fields.2.1.trans (hpp hrp), hx_fields.2.2.2.2.2.2, hsum', hl'_sub, hr'_sub⟩,
      hx_rev_false, hx_fields.1, hx_fields.2.1, hev, hst'_out⟩
  · have hrev_f : (st.nodes x).rev = false := Bool.eq_false_iff.mpr hrev
    have hl'_eq : l' = l := ite_eq_right hrev
    have hr'_eq : r' = r := ite_eq_right hrev
    have hst'_eq : st' = st := by simp [st', pushDownRev, hx, hrev_f]
    rw [hl'_eq, hr'_eq, hst'_eq]
    exact ⟨⟨hx, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩, hrev_f, rfl, rfl,
      fun _ _ => rfl, fun _ _ => rfl⟩

theorem pushDownTag_root_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hsub : SubtreeInv P st rp (.node x l r))
    (hrev : (st.nodes x).rev = false) :
    let st' := pushDownTag P st x
    SubtreeInv P st' rp (.node x l r) ∧
    (st'.nodes x).rev = (st.nodes x).rev ∧
    (st'.nodes x).tag = P.idTag ∧
    (st'.nodes x).ppar = (st.nodes x).ppar ∧
    (∀ flip acc, evalPairs P st' (.node x l r) flip acc =
      evalPairs P st (.node x l r) flip acc) ∧
    (∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u) := by
  intro st'
  rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hx_nl, hr_nd, hx_nr, hdisj⟩
  rcases hsub with ⟨hx, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
  by_cases htag_id : P.isIdTag (st.nodes x).tag = true
  · have htag_eq := hL.isIdTag_eq _ htag_id
    have hst'_eq : st' = st := by simp [st', pushDownTag, hx, htag_id]
    rw [hst'_eq]
    exact ⟨⟨hx, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩, rfl, htag_eq, rfl,
      fun _ _ => rfl, fun _ _ => rfl⟩
  · let t₀ := (st.nodes x).tag
    let st₀ := st.updateNode x fun cur => { cur with tag := P.idTag }
    let stL := applyTagNode P st₀ l.rootId t₀
    have hst'_eq : st' = applyTagNode P stL r.rootId t₀ := by
      simp only [st', pushDownTag, hx, ↓reduceIte, htag_id, hl_eq, hr_eq,
        Bool.false_eq_true, t₀, st₀, stL]
    have hx_fields : (st'.nodes x).tag = P.idTag ∧
        (st'.nodes x).rev = (st.nodes x).rev ∧
        (st'.nodes x).ppar = (st.nodes x).ppar ∧
        (st'.nodes x).val = (st.nodes x).val ∧
        (st'.nodes x).par = rp ∧
        (st'.nodes x).left = l.rootId ∧
        (st'.nodes x).right = r.rootId ∧
        (st'.nodes x).sz = (AuxTree.node x l r).countNodes ∧
        (st'.nodes x).sum = (st.nodes x).sum := by
      have hx0 : st₀.nodes x = { st.nodes x with tag := P.idTag } := by simp [st₀]
      have hxL : stL.nodes x = st₀.nodes x := by
        cases l with
        | leaf => simp [stL, applyTagNode, AuxTree.rootId]
        | node lid _ _ =>
            have hne : x ≠ lid := fun h => hx_nl (h ▸ by simp [AuxTree.toList])
            have hlid : lid ≠ 0 := SubtreeInv_nonZero hl (by simp [AuxTree.toList])
            simp [stL, applyTagNode, AuxTree.rootId, hlid, hne]
      have hxR : st'.nodes x = stL.nodes x := by
        cases r with
        | leaf => simp [hst'_eq, applyTagNode, AuxTree.rootId]
        | node rid _ _ =>
            have hne : x ≠ rid := fun h => hx_nr (h ▸ by simp [AuxTree.toList])
            have hrid : rid ≠ 0 := SubtreeInv_nonZero hr (by simp [AuxTree.toList])
            simp [hst'_eq, applyTagNode, AuxTree.rootId, hrid, hne]
      rw [hxR, hxL, hx0]
      exact ⟨rfl, rfl, rfl, rfl, hpar, hl_eq, hr_eq, hsz, rfl⟩
    have hst'_out : ∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u := by
      intro u hu
      have hux : u ≠ x := fun h => hu (by subst h; simp [AuxTree.toList])
      have hu0 : st₀.nodes u = st.nodes u := by simp [st₀, hux]
      have huL : stL.nodes u = st₀.nodes u := by
        cases l with
        | leaf => simp [stL, applyTagNode, AuxTree.rootId]
        | node lid _ _ =>
            have hu_l : u ≠ lid := fun h => hu (by subst h; simp [AuxTree.toList])
            have hlid : lid ≠ 0 := SubtreeInv_nonZero hl (by simp [AuxTree.toList])
            simp [stL, applyTagNode, AuxTree.rootId, hlid, hu_l]
      have huR : st'.nodes u = stL.nodes u := by
        cases r with
        | leaf => simp [hst'_eq, applyTagNode, AuxTree.rootId]
        | node rid _ _ =>
            have hu_r : u ≠ rid := fun h => hu (by subst h; simp [AuxTree.toList])
            have hrid : rid ≠ 0 := SubtreeInv_nonZero hr (by simp [AuxTree.toList])
            simp [hst'_eq, applyTagNode, AuxTree.rootId, hrid, hu_r]
      rw [huR, huL, hu0]
    have hl0 : SubtreeInv P st₀ x l :=
      SubtreeInv_agree hl (fun u hu => by
        have hne : u ≠ x := fun h => hx_nl (h ▸ hu)
        exact (nodes_updateNode_ne st hne _).symm)
    have hl'_sub0 : SubtreeInv P stL x l ∧
        (∀ b acc, evalPairs P stL l b acc =
          evalPairs P st₀ l b (P.compTag acc (if b then P.revTag t₀ else t₀))) ∧
        (∀ u ∉ l.toList, stL.nodes u = st₀.nodes u) := by
      cases l with
      | leaf =>
          simp only [AuxTree.rootId, stL, applyTagNode, ↓reduceIte]
          exact ⟨trivial, fun _ _ => rfl, fun _ _ => by simp⟩
      | node lid ll lr =>
          have h := applyTagNode_root_preserves hL t₀ hl_nd hl0
          simp only [AuxTree.rootId, stL]
          exact ⟨h.1, h.2.1, h.2.2.2⟩
    have hr0 : SubtreeInv P stL x r :=
      SubtreeInv_agree hr (fun u hu => by
        have h1 := hl'_sub0.2.2 u (fun hm => hdisj u hm hu)
        have hne : u ≠ x := fun h => hx_nr (h ▸ hu)
        have h2 : st₀.nodes u = st.nodes u := nodes_updateNode_ne st hne _
        exact (h1.trans h2).symm)
    have hr'_sub0 : SubtreeInv P st' x r ∧
        (∀ b acc, evalPairs P st' r b acc =
          evalPairs P stL r b (P.compTag acc (if b then P.revTag t₀ else t₀))) ∧
        (∀ u ∉ r.toList, st'.nodes u = stL.nodes u) := by
      cases r with
      | leaf =>
          simp only [AuxTree.rootId, hst'_eq, applyTagNode, ↓reduceIte]
          exact ⟨trivial, fun _ _ => rfl, fun _ _ => by simp⟩
      | node rid rl rr =>
          have h := applyTagNode_root_preserves hL t₀ hr_nd hr0
          simp only [AuxTree.rootId, hst'_eq]
          exact ⟨h.1, h.2.1, h.2.2.2⟩
    have hl'_sub : SubtreeInv P st' x l :=
      SubtreeInv_agree hl'_sub0.1 (fun u hu => (hr'_sub0.2.2 u (hdisj u hu)).symm)
    have hev : ∀ flip acc, evalPairs P st' (.node x l r) flip acc =
        evalPairs P st (.node x l r) flip acc := by
      intro flip acc
      have hev_l0 : ∀ b t, evalPairs P st₀ l b t = evalPairs P st l b t := fun b t =>
        evalPairs_agree P (fun u hu => by
          have hne : u ≠ x := fun h => hx_nl (h ▸ hu)
          exact nodes_updateNode_ne st hne _) b t
      have hev_r0 : ∀ b t, evalPairs P stL r b t = evalPairs P st r b t := fun b t =>
        evalPairs_agree P (fun u hu => by
          have h1 := hl'_sub0.2.2 u (fun hm => hdisj u hm hu)
          have hne : u ≠ x := fun h => hx_nr (h ▸ hu)
          have h2 : st₀.nodes u = st.nodes u := nodes_updateNode_ne st hne _
          exact h1.trans h2) b t
      have hev_l1 : ∀ b t, evalPairs P st' l b t = evalPairs P stL l b t := fun b t =>
        evalPairs_agree P (fun u hu => hr'_sub0.2.2 u (hdisj u hu)) b t
      cases flip
      · simp only [evalPairs, hx_fields.1, hx_fields.2.1, hx_fields.2.2.2.1, hrev,
          Bool.false_xor, Bool.false_eq_true, ↓reduceIte, hL.compTag_id_right,
          hev_l1, hl'_sub0.2.1, hev_l0, hr'_sub0.2.1, hev_r0, t₀]
      · simp only [evalPairs, hx_fields.1, hx_fields.2.1, hx_fields.2.2.2.1, hrev,
          Bool.true_xor, Bool.not_false, ↓reduceIte, hL.compTag_id_right, hL.revTag_id,
          hev_l1, hl'_sub0.2.1, hev_l0, hr'_sub0.2.1, hev_r0, t₀]
    refine ⟨⟨hx, hx_fields.2.2.2.2.2.1, hx_fields.2.2.2.2.2.2.1, hx_fields.2.2.2.2.1,
        fun hrp => hx_fields.2.2.1.trans (hpp hrp), hx_fields.2.2.2.2.2.2.2.1,
        by rw [hx_fields.2.2.2.2.2.2.2.2, hsum, hev false P.idTag], hl'_sub, hr'_sub0.1⟩,
      hx_fields.2.1, hx_fields.1, hx_fields.2.2.1, hev, hst'_out⟩

/-- Algebraic tree skeleton after `pushDown P st x` (swapping children's subtrees at `x` when
`x.rev = true`). -/
def pushDownTree (st : SplayState α σ τ) (x : ℕ) (t : AuxTree) : AuxTree :=
  if (st.nodes x).rev then
    match t.findSubtree x with
    | .node _ l r => t.replaceSubtree x (.node x l.revRoot r.revRoot)
    | .leaf => t
  else t

theorem pushDown_root_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hsub : SubtreeInv P st rp (.node x l r)) :
    let l' := if (st.nodes x).rev then l.revRoot else l
    let r' := if (st.nodes x).rev then r.revRoot else r
    let st' := pushDown P st x
    SubtreeInv P st' rp (.node x l' r') ∧
    (st'.nodes x).rev = false ∧ (st'.nodes x).tag = P.idTag ∧
    (st'.nodes x).ppar = (st.nodes x).ppar ∧
    (∀ flip acc, evalPairs P st' (.node x l' r') flip acc =
      evalPairs P st (.node x l r) flip acc) ∧
    (∀ u ∉ (AuxTree.node x l r).toList, st'.nodes u = st.nodes u) := by
  intro l' r' st'
  have h1 := pushDownRev_root_preserves hL hnd hsub
  have hnd1 : (AuxTree.node x l' r').toList.Nodup := by
    have hp : (AuxTree.node x l' r').toList.Perm (AuxTree.node x l r).toList := by
      by_cases hrev : (st.nodes x).rev = true
      · simp only [l', r', hrev, ↓reduceIte, AuxTree.toList]
        exact ((revRoot_toList_perm l).append_right [x]).append (revRoot_toList_perm r)
      · simp [l', r', hrev]
    exact hp.nodup_iff.mpr hnd
  have h2 := pushDownTag_root_preserves hL hnd1 h1.1 h1.2.1
  refine ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    fun flip acc => (h2.2.2.2.2.1 flip acc).trans (h1.2.2.2.2.1 flip acc), fun u hu => ?_⟩
  have hu1 : u ∉ (AuxTree.node x l' r').toList := by
    by_cases hrev : (st.nodes x).rev = true
    · simp only [l', r', hrev, ↓reduceIte, AuxTree.toList, List.mem_append, List.mem_singleton]
        at hu ⊢
      rintro ((h | rfl) | h)
      · exact hu (Or.inl (Or.inl ((revRoot_toList_perm l).mem_iff.mp h)))
      · exact hu (Or.inl (Or.inr rfl))
      · exact hu (Or.inr ((revRoot_toList_perm r).mem_iff.mp h))
    · simpa [l', r', hrev] using hu
  exact (h2.2.2.2.2.2 u hu1).trans (h1.2.2.2.2.2 u hu)

theorem pushDown_preserves_SubtreeInv {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {rp x : ℕ} {t : AuxTree}
    (hnd : t.toList.Nodup) (hsub : SubtreeInv P st rp t) (hx : x ∈ t.toList) :
    let t' := pushDownTree st x t
    let st' := pushDown P st x
    SubtreeInv P st' rp t' ∧
    t'.toList.Perm t.toList ∧
    t'.rootId = t.rootId ∧
    (∀ u, t'.depthOf u = t.depthOf u) ∧
    (∀ u, t'.pathTo u = t.pathTo u) ∧
    (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧ t'.treePhi vSize = t.treePhi vSize ∧
      ∀ y, (t'.findSubtree y).treeSize vSize = (t.findSubtree y).treeSize vSize) ∧
    (st'.nodes x).rev = false ∧ (st'.nodes x).tag = P.idTag ∧
    (∀ u ∉ (t.findSubtree x).toList, st'.nodes u = st.nodes u) ∧
    (∀ flip acc, evalPairs P st' t' flip acc = evalPairs P st t flip acc) := by
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj⟩
      rcases hsub with ⟨hid, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
      by_cases hix : id = x
      · subst hix
        have hpd := pushDown_root_preserves hL hnd ⟨hid, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
        by_cases hrev : (st.nodes id).rev = true
        · have ht' : pushDownTree st id (.node id l r) = .node id l.revRoot r.revRoot := by
            simp [pushDownTree, hrev, AuxTree.findSubtree, AuxTree.replaceSubtree]
          rw [ht']
          have hl'_simp : (if (st.nodes id).rev then l.revRoot else l) = l.revRoot := ite_eq_left hrev
          have hr'_simp : (if (st.nodes id).rev then r.revRoot else r) = r.revRoot := ite_eq_left hrev
          rw [hl'_simp, hr'_simp] at hpd
          refine ⟨hpd.1, ?_, rfl, fun u => ?_, fun u => ?_, fun vSize => ?_,
              hpd.2.1, hpd.2.2.1, by simpa [AuxTree.findSubtree] using hpd.2.2.2.2.2,
              hpd.2.2.2.2.1⟩
          · simp only [AuxTree.toList]
            exact ((revRoot_toList_perm l).append_right [id]).append (revRoot_toList_perm r)
          · by_cases hu : u = id
            · simp [AuxTree.depthOf, hu]
            · simp only [AuxTree.depthOf, hu, ↓reduceIte]
              by_cases hul : u ∈ l.toList
              · have hul' : u ∈ l.revRoot.toList := (revRoot_toList_perm l).mem_iff.mpr hul
                have hur : u ∉ r.toList := hdisj u hul
                simp [hul, hul', revRoot_depthOf hl_nd u]
              · have hul' : u ∉ l.revRoot.toList := fun hm =>
                  hul ((revRoot_toList_perm l).mem_iff.mp hm)
                by_cases hur : u ∈ r.toList
                · have hur' : u ∈ r.revRoot.toList := (revRoot_toList_perm r).mem_iff.mpr hur
                  simp [hul, hul', hur, hur', revRoot_depthOf hr_nd u]
                · have hur' : u ∉ r.revRoot.toList := fun hm =>
                    hur ((revRoot_toList_perm r).mem_iff.mp hm)
                  simp [hul, hul', hur, hur']
          · by_cases hu : u = id
            · simp [AuxTree.pathTo, hu]
            · simp only [AuxTree.pathTo, hu, ↓reduceIte]
              by_cases hul : u ∈ l.toList
              · have hul' : u ∈ l.revRoot.toList := (revRoot_toList_perm l).mem_iff.mpr hul
                simp [hul, hul', revRoot_pathTo hl_nd u]
              · have hul' : u ∉ l.revRoot.toList := fun hm =>
                  hul ((revRoot_toList_perm l).mem_iff.mp hm)
                by_cases hur : u ∈ r.toList
                · have hur' : u ∈ r.revRoot.toList := (revRoot_toList_perm r).mem_iff.mpr hur
                  simp [hul, hul', hur, hur', revRoot_pathTo hr_nd u]
                · have hur' : u ∉ r.revRoot.toList := fun hm =>
                    hur ((revRoot_toList_perm r).mem_iff.mp hm)
                  simp [hul, hul', hur, hur']
          · have hts : (AuxTree.node id l.revRoot r.revRoot).treeSize vSize =
                (AuxTree.node id l r).treeSize vSize := by
              simp [AuxTree.treeSize, revRoot_treeSize]
            have hrk : (AuxTree.node id l.revRoot r.revRoot).rank vSize =
                (AuxTree.node id l r).rank vSize := by simp [AuxTree.rank, hts]
            have htp : (AuxTree.node id l.revRoot r.revRoot).treePhi vSize =
                (AuxTree.node id l r).treePhi vSize := by
              simp [AuxTree.treePhi, hrk, revRoot_treePhi]
            refine ⟨hts, htp, fun y => ?_⟩
            by_cases hy : id = y
            · subst hy; simpa [AuxTree.findSubtree] using hts
            · simp only [AuxTree.findSubtree, hy, ↓reduceIte]
              by_cases hyl : y ∈ l.toList
              · have hyl' : y ∈ l.revRoot.toList := (revRoot_toList_perm l).mem_iff.mpr hyl
                simp [hyl, hyl', revRoot_findSubtree_treeSize hl_nd vSize y]
              · have hyl' : y ∉ l.revRoot.toList := fun hm =>
                  hyl ((revRoot_toList_perm l).mem_iff.mp hm)
                simp [hyl, hyl', revRoot_findSubtree_treeSize hr_nd vSize y]
        · have hrev_f : (st.nodes id).rev = false := Bool.eq_false_iff.mpr hrev
          have ht' : pushDownTree st id (.node id l r) = .node id l r := by
            simp [pushDownTree, hrev_f]
          rw [ht']
          have hl'_simp : (if (st.nodes id).rev then l.revRoot else l) = l := ite_eq_right hrev
          have hr'_simp : (if (st.nodes id).rev then r.revRoot else r) = r := ite_eq_right hrev
          rw [hl'_simp, hr'_simp] at hpd
          exact ⟨hpd.1, List.Perm.refl _, rfl, fun _ => rfl, fun _ => rfl,
            fun _ => ⟨rfl, rfl, fun _ => rfl⟩, hpd.2.1, hpd.2.2.1,
            by simpa [AuxTree.findSubtree] using hpd.2.2.2.2.2, hpd.2.2.2.2.1⟩
      · by_cases hxl : x ∈ l.toList
        · have hxn_r : x ∉ r.toList := hdisj x hxl
          have hfind_eq : (AuxTree.node id l r).findSubtree x = l.findSubtree x := by
            simp [AuxTree.findSubtree, hix, hxl]
          have ht'_eq : pushDownTree st x (.node id l r) =
              AuxTree.node id (pushDownTree st x l) r := by
            by_cases hrev : (st.nodes x).rev = true
            · obtain ⟨A, B, hAB⟩ := AuxTree.findSubtree_root_of_mem hxl
              simp only [pushDownTree, hrev, ↓reduceIte, hfind_eq, hAB, AuxTree.replaceSubtree, hix]
              rw [AuxTree.replaceSubtree_not_mem hxn_r]
            · simp [pushDownTree, hrev]
          rcases ihl hl_nd hl hxl with
            ⟨hl_sub, hl_perm, hl_root, hl_dep, hl_path, hl_sz, hrev_x, htag_x, hout_l, hev_l⟩
          rw [ht'_eq]
          have hst_id : (pushDown P st x).nodes id = st.nodes id :=
            hout_l id (fun hm => hid_nl (AuxTree.findSubtree_subset hm))
          have hr_sub' : SubtreeInv P (pushDown P st x) id r := by
            refine SubtreeInv_agree hr (fun u hu => ?_)
            exact (hout_l u (fun hm => hdisj u (AuxTree.findSubtree_subset hm) hu)).symm
          have hev_r : ∀ b t, evalPairs P (pushDown P st x) r b t = evalPairs P st r b t :=
            fun b t => evalPairs_agree P (fun u hu =>
              (hout_l u (fun hm => hdisj u (AuxTree.findSubtree_subset hm) hu))) b t
          have hev_full : ∀ flip acc, evalPairs P (pushDown P st x)
              (.node id (pushDownTree st x l) r) flip acc =
              evalPairs P st (.node id l r) flip acc := by
            intro flip acc
            cases flip <;> simp only [evalPairs, hst_id, hev_l, hev_r]
          have hcnt : (AuxTree.node id (pushDownTree st x l) r).countNodes =
              (AuxTree.node id l r).countNodes := by
            simp only [AuxTree.countNodes, ← AuxTree.length_toList, hl_perm.length_eq]
          have hsz' : ((pushDown P st x).nodes id).sz =
              (AuxTree.node id (pushDownTree st x l) r).countNodes := by
            rw [hst_id, hsz, hcnt]
          have hsum' : ((pushDown P st x).nodes id).sum =
              P.listSummary (evalPairs P (pushDown P st x)
                (.node id (pushDownTree st x l) r) false P.idTag) := by
            rw [hst_id, hsum, hev_full false P.idTag]
          refine ⟨⟨hid, by rw [hst_id, hl_eq, hl_root], by rw [hst_id, hr_eq],
              by rw [hst_id, hpar], fun hrp => by rw [hst_id]; exact hpp hrp,
              hsz', hsum', hl_sub, hr_sub'⟩,
            (hl_perm.append_right [id]).append_right r.toList, rfl, fun u => ?_, fun u => ?_,
            fun vSize => ?_, hrev_x, htag_x, fun u hu => hout_l u (by simpa [hfind_eq] using hu),
            hev_full⟩
          · by_cases hu : u = id
            · simp [AuxTree.depthOf, hu]
            · simp only [AuxTree.depthOf, hu, ↓reduceIte, hl_perm.mem_iff, hl_dep u]
          · by_cases hu : u = id
            · simp [AuxTree.pathTo, hu]
            · simp only [AuxTree.pathTo, hu, ↓reduceIte, hl_perm.mem_iff, hl_path u]
          · rcases hl_sz vSize with ⟨h1, h2, h3⟩
            have hts : (AuxTree.node id (pushDownTree st x l) r).treeSize vSize =
                (AuxTree.node id l r).treeSize vSize := by
              simp [AuxTree.treeSize, h1]
            have hrk : (AuxTree.node id (pushDownTree st x l) r).rank vSize =
                (AuxTree.node id l r).rank vSize := by
              simp [AuxTree.rank, hts]
            refine ⟨hts, by simp [AuxTree.treePhi, hrk, h2], fun y => ?_⟩
            by_cases hy : id = y
            · subst hy; simpa [AuxTree.findSubtree] using hts
            · simp only [AuxTree.findSubtree, hy, ↓reduceIte, hl_perm.mem_iff]
              split_ifs <;> simp [h3 y]
        · have hxr : x ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h | rfl) | h
            · exact absurd h hxl
            · exact absurd rfl hix
            · exact h
          have hfind_eq : (AuxTree.node id l r).findSubtree x = r.findSubtree x := by
            simp [AuxTree.findSubtree, hix, hxl]
          have ht'_eq : pushDownTree st x (.node id l r) =
              AuxTree.node id l (pushDownTree st x r) := by
            by_cases hrev : (st.nodes x).rev = true
            · obtain ⟨A, B, hAB⟩ := AuxTree.findSubtree_root_of_mem hxr
              simp only [pushDownTree, hrev, ↓reduceIte, hfind_eq, hAB, AuxTree.replaceSubtree, hix]
              rw [AuxTree.replaceSubtree_not_mem hxl]
            · simp [pushDownTree, hrev]
          rcases ihr hr_nd hr hxr with
            ⟨hr_sub, hr_perm, hr_root, hr_dep, hr_path, hr_sz, hrev_x, htag_x, hout_r, hev_r⟩
          rw [ht'_eq]
          have hst_id : (pushDown P st x).nodes id = st.nodes id :=
            hout_r id (fun hm => hid_nr (AuxTree.findSubtree_subset hm))
          have hl_sub' : SubtreeInv P (pushDown P st x) id l := by
            refine SubtreeInv_agree hl (fun u hu => ?_)
            exact (hout_r u (fun hm => hdisj u hu (AuxTree.findSubtree_subset hm))).symm
          have hev_l : ∀ b t, evalPairs P (pushDown P st x) l b t = evalPairs P st l b t :=
            fun b t => evalPairs_agree P (fun u hu =>
              (hout_r u (fun hm => hdisj u hu (AuxTree.findSubtree_subset hm)))) b t
          have hev_full : ∀ flip acc, evalPairs P (pushDown P st x)
              (.node id l (pushDownTree st x r)) flip acc =
              evalPairs P st (.node id l r) flip acc := by
            intro flip acc
            cases flip <;> simp only [evalPairs, hst_id, hev_l, hev_r]
          have hcnt : (AuxTree.node id l (pushDownTree st x r)).countNodes =
              (AuxTree.node id l r).countNodes := by
            simp only [AuxTree.countNodes, ← AuxTree.length_toList, hr_perm.length_eq]
          have hsz' : ((pushDown P st x).nodes id).sz =
              (AuxTree.node id l (pushDownTree st x r)).countNodes := by
            rw [hst_id, hsz, hcnt]
          have hsum' : ((pushDown P st x).nodes id).sum =
              P.listSummary (evalPairs P (pushDown P st x)
                (.node id l (pushDownTree st x r)) false P.idTag) := by
            rw [hst_id, hsum, hev_full false P.idTag]
          refine ⟨⟨hid, by rw [hst_id, hl_eq], by rw [hst_id, hr_eq, hr_root],
              by rw [hst_id, hpar], fun hrp => by rw [hst_id]; exact hpp hrp,
              hsz', hsum', hl_sub', hr_sub⟩,
            hr_perm.append_left (l.toList ++ [id]), rfl, fun u => ?_, fun u => ?_,
            fun vSize => ?_, hrev_x, htag_x, fun u hu => hout_r u (by simpa [hfind_eq] using hu),
            hev_full⟩
          · by_cases hu : u = id
            · simp [AuxTree.depthOf, hu]
            · simp only [AuxTree.depthOf, hu, ↓reduceIte, hr_perm.mem_iff, hr_dep u]
          · by_cases hu : u = id
            · simp [AuxTree.pathTo, hu]
            · simp only [AuxTree.pathTo, hu, ↓reduceIte, hr_perm.mem_iff, hr_path u]
          · rcases hr_sz vSize with ⟨h1, h2, h3⟩
            have hts : (AuxTree.node id l (pushDownTree st x r)).treeSize vSize =
                (AuxTree.node id l r).treeSize vSize := by
              simp [AuxTree.treeSize, h1]
            have hrk : (AuxTree.node id l (pushDownTree st x r)).rank vSize =
                (AuxTree.node id l r).rank vSize := by
              simp [AuxTree.rank, hts]
            refine ⟨hts, by simp [AuxTree.treePhi, hrk, h2], fun y => ?_⟩
            by_cases hy : id = y
            · subst hy; simpa [AuxTree.findSubtree] using hts
            · simp only [AuxTree.findSubtree, hy, ↓reduceIte]
              split_ifs <;> simp [h3 y]

theorem pushDown_preserves_TreeInv {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {x : ℕ} {t : AuxTree}
    (ht : TreeInv P st t) (hx : x ∈ t.toList) :
    let t' := pushDownTree st x t
    let st' := pushDown P st x
    TreeInv P st' t' ∧
    t'.toList.Perm t.toList ∧
    t'.rootId = t.rootId ∧
    (∀ u, t'.depthOf u = t.depthOf u) ∧
    (∀ u, t'.pathTo u = t.pathTo u) ∧
    (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧ t'.treePhi vSize = t.treePhi vSize ∧
      ∀ y, (t'.findSubtree y).treeSize vSize = (t.findSubtree y).treeSize vSize) ∧
    (st'.nodes x).rev = false ∧ (st'.nodes x).tag = P.idTag ∧
    (∀ u ∉ (t.findSubtree x).toList, st'.nodes u = st.nodes u) ∧
    (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar ∧
    (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
    evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag := by
  rcases pushDown_preserves_SubtreeInv hL ht.nodup ht.sub hx with
    ⟨hsub', hperm, hroot, hdep, hpath, hsz, hrev, htag, hout, hev⟩
  have hppar : ((pushDown P st x).nodes (pushDownTree st x t).rootId).ppar =
      (st.nodes t.rootId).ppar := by
    rw [hroot]
    cases t with
    | leaf => simp [AuxTree.toList] at hx
    | node id l r =>
        by_cases hid : id = x
        · subst hid
          have hpd := pushDown_root_preserves hL ht.nodup ht.sub
          exact hpd.2.2.2.1
        · have hnot : id ∉ ((AuxTree.node id l r).findSubtree x).toList := by
            intro hm
            have hd0 : (AuxTree.node id l r).depthOf id = 0 := AuxTree.depthOf_root id l r
            have hdx : (AuxTree.node id l r).depthOf x ≠ 0 := fun h0 =>
              hid ((AuxTree.depthOf_zero_iff_root hx).mp h0).symm
            exact AuxTree.not_mem_findSubtree_of_ancestor ht.nodup (by simp [AuxTree.toList]) hx
              (by omega) (AuxTree.self_mem_pathTo (by simp [AuxTree.toList])) hm
          simp only [AuxTree.rootId]
          rw [hout id hnot]
  refine ⟨⟨hperm.nodup_iff.mpr ht.nodup, hsub'⟩, hperm, hroot, hdep, hpath, hsz, hrev, htag,
    hout, hppar, fun u hu => hout u (fun hm => hu (AuxTree.findSubtree_subset hm)), hev false P.idTag⟩

/-! ### `pushPath` preservation -/

/-- Exact recursive specification theorem for `pushPath P st fuel x` when `t.depthOf x < fuel`. -/
theorem pushPath_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {fuel : ℕ} :
    ∀ {st : SplayState α σ τ} {t : AuxTree} {x : ℕ},
      TreeInv P st t → x ∈ t.toList → t.depthOf x < fuel →
      ∃ t',
        let st' := pushPath P st fuel x
        TreeInv P st' t' ∧
        t'.toList.Perm t.toList ∧
        t'.rootId = t.rootId ∧
        (∀ u, t'.depthOf u = t.depthOf u) ∧
        (∀ u, t'.pathTo u = t.pathTo u) ∧
        (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧ t'.treePhi vSize = t.treePhi vSize ∧
          ∀ y, (t'.findSubtree y).treeSize vSize = (t.findSubtree y).treeSize vSize) ∧
        (∀ u ∈ t'.pathTo x, (st'.nodes u).rev = false ∧ (st'.nodes u).tag = P.idTag) ∧
        (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar ∧
        (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
        evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag := by
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ k ih =>
      intro st t x ht hx hdep
      have hx_nz : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
      have hpar_eq : (st.nodes x).par = t.parentIn x 0 :=
        SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
      by_cases hxr : x = t.rootId
      · have hpar0 : (st.nodes x).par = 0 := by
          rw [hpar_eq]
          cases t with
          | leaf => simp [AuxTree.toList] at hx
          | node id l r => simp only [AuxTree.rootId] at hxr; subst hxr; simp [AuxTree.parentIn]
        have hst'_eq : pushPath P st (k + 1) x = pushDown P st x := by
          simp [pushPath, hx_nz, hpar0]
        rcases pushDown_preserves_TreeInv hL ht hx with
          ⟨ht', hperm, hroot, hdep', hpath, hsz, hrev, htag, _, hpp, hout, hev⟩
        refine ⟨pushDownTree st x t, ?_⟩
        rw [hst'_eq]
        refine ⟨ht', hperm, hroot, hdep', hpath, hsz, fun u hu => ?_, hpp, hout, hev⟩
        rw [hpath x] at hu
        cases t with
        | leaf => simp [AuxTree.toList] at hx
        | node id l r =>
            simp only [AuxTree.rootId] at hxr; subst hxr
            simp only [AuxTree.pathTo, ↓reduceIte, List.mem_singleton] at hu
            subst hu; exact ⟨hrev, htag⟩
      · have hpm := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hxr
        have hp_mem : (st.nodes x).par ∈ t.toList := hpar_eq ▸ hpm.1
        have hp_nz : (st.nodes x).par ≠ 0 := SubtreeInv_nonZero ht.sub hp_mem
        have hp_dep : t.depthOf (st.nodes x).par < k := by rw [hpar_eq]; omega
        rcases ih ht hp_mem hp_dep with
          ⟨t₁, ht₁, hperm₁, hroot₁, hdep₁, hpath₁, hsz₁, hclean₁, hpp₁, hout₁, hev₁⟩
        let st₁ := pushPath P st k (st.nodes x).par
        have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
        rcases pushDown_preserves_TreeInv hL ht₁ hx₁ with
          ⟨ht₂, hperm₂, hroot₂, hdep₂, hpath₂, hsz₂, hrev₂, htag₂, hout₂, hpp₂, hout_full₂, hev₂⟩
        have hst'_eq : pushPath P st (k + 1) x = pushDown P st₁ x := by
          simp [pushPath, hx_nz, hp_nz, st₁]
        refine ⟨pushDownTree st₁ x t₁, ?_⟩
        rw [hst'_eq]
        refine ⟨ht₂, hperm₂.trans hperm₁, hroot₂.trans hroot₁,
          fun u => (hdep₂ u).trans (hdep₁ u), fun u => (hpath₂ u).trans (hpath₁ u),
          fun vSize => ?_, fun u hu => ?_, hpp₂.trans hpp₁, fun u hu => ?_, hev₂.trans hev₁⟩
        · rcases hsz₁ vSize with ⟨a1, a2, a3⟩
          rcases hsz₂ vSize with ⟨b1, b2, b3⟩
          exact ⟨b1.trans a1, b2.trans a2, fun y => (b3 y).trans (a3 y)⟩
        · rw [hpath₂ x, hpath₁ x, hpm.2.2, ← hpar_eq, List.mem_append, List.mem_singleton] at hu
          rcases hu with hu_p | rfl
          · have hu_p₁ : u ∈ t₁.pathTo (st.nodes x).par := by rwa [hpath₁]
            have hlt : t₁.depthOf u < t₁.depthOf x := by
              rw [hdep₁ u, hdep₁ x]
              have hle := (AuxTree.depthOf_le_of_mem_pathTo ht.nodup hp_mem hu_p).1
              have hpm_d : t.depthOf (st.nodes x).par + 1 = t.depthOf x := hpar_eq ▸ hpm.2.1
              omega
            have hu_nin : u ∉ (t₁.findSubtree x).toList :=
              AuxTree.not_mem_findSubtree_of_ancestor ht₁.nodup (AuxTree.mem_pathTo hu_p₁) hx₁
                hlt (AuxTree.self_mem_pathTo (AuxTree.mem_pathTo hu_p₁))
            rw [hout₂ u hu_nin]
            exact hclean₁ u hu_p₁
          · exact ⟨hrev₂, htag₂⟩
        · exact (hout_full₂ u (fun hm => hu (hperm₁.mem_iff.mp hm))).trans (hout₁ u hu)

end SplayState

end MinCostFlow.LinkCut
