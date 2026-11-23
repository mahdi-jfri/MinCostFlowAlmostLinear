module

public import MinCostFlow.LinkCut.ForestExposeSpec
public import MinCostFlow.LinkCut.ForestSplices
public import MinCostFlow.LinkCut.ForestExpose
public import MinCostFlow.LinkCut.ForestReversals
public import MinCostFlow.LinkCut.SplayLazy
public import MinCostFlow.LinkCut.SplayQuery

/-!
# Paths to the root, `findRoot`, and `connected` in the link-cut model

Helpers about `subRoot`, `reaches` and `LctInvWith`, then `leftmostWalk`, `findRoot`,
`connected`, and the first facts about `lctReroot`.
-/

namespace MinCostFlow.LinkCut

@[expose] public section

variable {α σ τ : Type*}

/-! ### `subRoot`, `reaches`, and `LctInvWith` path helpers -/

theorem reaches_weaken {par : ℕ → ℕ} :
    ∀ {k₁ k₂ u x : ℕ}, k₁ ≤ k₂ → reaches par k₁ u x = true → reaches par k₂ u x = true := by
  intro k₁
  induction k₁ with
  | zero =>
      intro k₂ u x _ h
      simp only [reaches, beq_iff_eq] at h
      subst h
      exact reaches_self par k₂ x
  | succ k₁ ih =>
      intro k₂ u x hk h
      cases k₂ with
      | zero => omega
      | succ k₂ =>
          simp only [reaches] at h ⊢
          by_cases hxu : x = u
          · simp [hxu]
          · have hbeq : (x == u) = false := beq_false_of_ne hxu
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hp : par x = 0
            · simp [hp] at h
            · have hp0 : (par x == 0) = false := beq_false_of_ne hp
              simp only [hp0, Bool.false_eq_true, ↓reduceIte] at h ⊢
              exact ih (by omega) h

theorem reaches_subRoot_of_zero {par : ℕ → ℕ} :
    ∀ {k x : ℕ}, par (subRoot par k x) = 0 → reaches par k (subRoot par k x) x = true := by
  intro k
  induction k with
  | zero =>
      intro x _
      simp [subRoot, reaches_self]
  | succ k ih =>
      intro x hzero
      by_cases hpx : par x = 0
      · simp [subRoot, hpx, reaches_self]
      · have hsub : subRoot par (k + 1) x = subRoot par k (par x) := by
          simp [subRoot, hpx]
        rw [hsub] at hzero ⊢
        simp only [reaches]
        by_cases hxr : x = subRoot par k (par x)
        · rw [← hxr]; simp
        · have hbeq : (x == subRoot par k (par x)) = false := beq_false_of_ne hxr
          have hp0 : (par x == 0) = false := beq_false_of_ne hpx
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hp0]
          exact ih hzero

theorem subRoot_eq_of_reaches_zero {par : ℕ → ℕ} :
    ∀ {m k r x : ℕ}, m ≤ k → reaches par m r x = true → par r = 0 → subRoot par k x = r := by
  intro m
  induction m with
  | zero =>
      intro k r x _ h hr0
      simp only [reaches, beq_iff_eq] at h
      subst h
      cases k with
      | zero => simp [subRoot]
      | succ k => simp [subRoot, hr0]
  | succ m ih =>
      intro k r x hk h hr0
      cases k with
      | zero => omega
      | succ k =>
          simp only [reaches] at h
          by_cases hxr : x = r
          · subst hxr
            simp [subRoot, hr0]
          · have hbeq : (x == r) = false := beq_false_of_ne hxr
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hpx : par x = 0
            · simp [hpx] at h
            · have hp0 : (par x == 0) = false := beq_false_of_ne hpx
              simp only [hp0, Bool.false_eq_true, ↓reduceIte] at h
              simp only [subRoot, hpx, ↓reduceIte]
              exact ih (by omega) h hr0

theorem reaches_subRoot {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList) :
    reaches (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length
      (subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length x) x = true :=
  reaches_subRoot_of_zero (W.subRoot_isRoot hx).2.1

theorem subRoot_step_eq {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hpx : inducedSubPar P st.splay trees x ≠ 0) :
    subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length x =
      subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length
        (inducedSubPar P st.splay trees x) := by
  let active := trees.flatMap AuxTree.toList
  let par := inducedSubPar P st.splay trees
  have hpx_mem : par x ∈ active := W.subPar_mem_active hx hpx
  have hr_px := W.subRoot_isRoot hpx_mem
  have hrec_px : reaches par active.length (subRoot par active.length (par x)) (par x) = true :=
    reaches_subRoot W hpx_mem
  have hrec_x : reaches par active.length (subRoot par active.length (par x)) x = true :=
    (reaches_step_iff W.activeNodup (fun _ hz hpz => W.subPar_mem_active hz hpz) W.acyclic hx).mpr
      (Or.inr ⟨hpx, hrec_px⟩)
  exact subRoot_eq_of_reaches_zero le_rfl hrec_x hr_px.2.1

theorem subRoot_eq_self_of_zero {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (_W : LctInvWith P st trees freeList depth) {x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hpx : inducedSubPar P st.splay trees x = 0) :
    subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length x = x := by
  have hne : (trees.flatMap AuxTree.toList).length ≠ 0 :=
    (List.length_pos_of_mem hx).ne'
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [hk]
  simp [subRoot, hpx]

theorem subRoot_eq_iff_reaches_zero {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {r x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hr0 : inducedSubPar P st.splay trees r = 0) :
    subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length x = r ↔
      reaches (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length r x = true := by
  constructor
  · intro h; subst h; exact reaches_subRoot W hx
  · intro h; exact subRoot_eq_of_reaches_zero le_rfl h hr0

theorem subRoot_eq_of_LctInvWith_agree {P Q : LctPayload α σ τ} {st₁ : LctState α σ τ}
    {st₂ : LctState α σ τ} {trees₁ trees₂ : List AuxTree}
    {fl₁ fl₂ : List ℕ} {d₁ d₂ : ℕ → ℕ}
    (_W₁ : LctInvWith P st₁ trees₁ fl₁ d₁) (W₂ : LctInvWith Q st₂ trees₂ fl₂ d₂)
    (hperm : (trees₁.flatMap AuxTree.toList).Perm (trees₂.flatMap AuxTree.toList))
    (hpar : ∀ z, inducedSubPar P st₁.splay trees₁ z = inducedSubPar Q st₂.splay trees₂ z)
    {x : ℕ} (hx : x ∈ trees₁.flatMap AuxTree.toList) :
    subRoot (inducedSubPar Q st₂.splay trees₂) (trees₂.flatMap AuxTree.toList).length x =
      subRoot (inducedSubPar P st₁.splay trees₁) (trees₁.flatMap AuxTree.toList).length x := by
  have hx₂ : x ∈ trees₂.flatMap AuxTree.toList := hperm.mem_iff.mp hx
  have hrec := reaches_subRoot W₂ hx₂
  have hrec' : reaches (inducedSubPar P st₁.splay trees₁) (trees₂.flatMap AuxTree.toList).length
      (subRoot (inducedSubPar Q st₂.splay trees₂) (trees₂.flatMap AuxTree.toList).length x) x = true := by
    rw [reaches_congr hpar]
    exact hrec
  have hr0 : inducedSubPar P st₁.splay trees₁
      (subRoot (inducedSubPar Q st₂.splay trees₂) (trees₂.flatMap AuxTree.toList).length x) = 0 := by
    have hr2 := W₂.subRoot_isRoot hx₂
    dsimp only at hr2
    rw [hpar]
    exact hr2.2.1
  exact (subRoot_eq_of_reaches_zero hperm.length_eq.ge hrec' hr0).symm

theorem listHead0_par_eq_zero_of_ppar {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees)
    (hpp0 : (st.splay.nodes t.rootId).ppar = 0) :
    inducedSubPar P st.splay trees (listHead0 (treeIds P st.splay t)) = 0 := by
  have hne : treeIds P st.splay t ≠ [] := treeIds_ne_nil (W.treesNonEmpty t ht)
  have hmem : listHead0 (treeIds P st.splay t) ∈ t.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty t ht)
  rw [inducedSubPar_eq_of_mem W.activeNodup ht hmem]
  cases hids : treeIds P st.splay t with
  | nil => exact absurd hids hne
  | cons a rest => simp [listHead0, chainPred, hpp0]

theorem eq_listHead0_of_par_zero {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees)
    {u : ℕ} (hu : u ∈ t.toList) (hpu : inducedSubPar P st.splay trees u = 0) :
    u = listHead0 (treeIds P st.splay t) := by
  have hrc : reaches (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length
      (listHead0 (treeIds P st.splay t)) u = true := tree_reaches_head W ht hu
  cases hk : (trees.flatMap AuxTree.toList).length with
  | zero =>
      have := List.length_pos_of_mem (List.mem_flatMap.mpr ⟨t, ht, hu⟩)
      omega
  | succ k =>
      rw [hk] at hrc
      simp only [reaches] at hrc
      by_cases heq : u = listHead0 (treeIds P st.splay t)
      · exact heq
      · have hbeq : (u == listHead0 (treeIds P st.splay t)) = false := beq_false_of_ne heq
        simp [hbeq, hpu] at hrc

/-! ### `leftmostWalk`, `findRoot`, and `connected` -/

private theorem countNodes_eq_toList_length : ∀ t : AuxTree, t.countNodes = t.toList.length
  | .leaf => rfl
  | .node _ l r => by
      simp only [AuxTree.countNodes, AuxTree.toList, List.length_append, List.length_cons,
        List.length_nil]
      rw [countNodes_eq_toList_length l, countNodes_eq_toList_length r]
      omega

theorem ne_of_mem_erase_trees {ts : List AuxTree} {a b : AuxTree}
    (hnd : (ts.flatMap AuxTree.toList).Nodup) (hne : ∀ t ∈ ts, t ≠ AuxTree.leaf)
    (ha : a ∈ ts.erase b) : a ≠ b := by
  intro heq
  subst heq
  have hts_nd : ts.Nodup := by
    clear ha
    induction ts with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
        simp only [List.flatMap_cons, List.nodup_append] at hnd
        refine List.nodup_cons.mpr ⟨fun hmem => ?_,
          ih hnd.2.1 (fun t ht => hne t (List.mem_cons_of_mem x ht))⟩
        have hx_ne : x.toList ≠ [] := fun h => by
          cases x with
          | leaf => exact hne .leaf List.mem_cons_self rfl
          | node _ l r => simp [AuxTree.toList] at h
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil x.toList hx_ne
        exact hnd.2.2 y hy y (List.mem_flatMap.mpr ⟨x, hmem, hy⟩) rfl
  exact (List.Nodup.not_mem_erase hts_nd) ha

theorem lctLeftmostWalk_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {t : AuxTree} (ht : t ∈ trees) :
    let res := SplayState.leftmostWalk P st.splay (2 * st.n + 1) t.rootId
    let s1 := res.1
    let r := res.2
    let st1 : LctState α σ τ := { n := st.n, splay := s1, freeHead := st.freeHead }
    ∃ t₁,
      let trees1 := t₁ :: trees.erase t
      t₁ ∈ trees1 ∧
        r ∈ t₁.toList ∧
        LctInvWith P st1 trees1 freeList depth ∧
        t₁.toList.Perm t.toList ∧
        SplayState.TreeInv P s1 t₁ ∧
        t₁.rootId = t.rootId ∧
        (∀ z, inducedSubPar P s1 trees1 z = inducedSubPar P st.splay trees z) ∧
        (forestPairs P s1 trees1).Perm (forestPairs P st.splay trees) ∧
        r = listHead0 (treeIds P st.splay t) ∧
        (s1.nodes r).left = 0 ∧
        (s1.nodes t₁.rootId).ppar = (st.splay.nodes t.rootId).ppar ∧
        (∀ u ∉ t.toList, s1.nodes u = st.splay.nodes u) ∧
        heavyCount P st1 = heavyCount P st ∧
        sumTreePhi P st1 = sumTreePhi P st ∧
        splayDepth s1 (2 * st.n + 1) r = t₁.depthOf r ∧
        t₁.depthOf r < t.countNodes := by
  intro res s1 r st1
  have hact_le : (trees.flatMap AuxTree.toList).length ≤ 2 * st.n :=
    active_length_le_two_mul W.activeNodup W.activeValid
  have hlen_le : t.toList.length ≤ 2 * st.n := (tree_length_le_active ht).trans hact_le
  have hcnt_eq : t.countNodes = t.toList.length := countNodes_eq_toList_length t
  have hfuel : t.countNodes ≤ 2 * st.n + 1 := by omega
  have ht_inv := W.treesInv t ht
  have ht_ne := W.treesNonEmpty t ht
  rcases SplayState.leftmostWalk_sub_preserves hL ht_inv.nodup ht_inv.sub ht_ne rfl hfuel with
    ⟨t₁, hsub₁, ht1_ne, ht1_rt, ht1_perm, hr_mem, hr_left, hhead, hev_all, hpp1, hout1, hdep1, hsizes⟩
  have hnd₁ : t₁.toList.Nodup := ht1_perm.nodup_iff.mpr ht_inv.nodup
  have ht1_inv : SplayState.TreeInv P s1 t₁ := ⟨hnd₁, hsub₁⟩
  have hev_id : SplayState.evalPairs P s1 t₁ false P.idTag =
      SplayState.evalPairs P st.splay t false P.idTag := hev_all false P.idTag
  have hrep := replaceSameIds_spec W ht ht1_ne ht1_inv ht1_perm hev_id hpp1 hout1
  rcases hrep with ⟨hW1, hH1, hPhi1, hpar_act⟩
  have hpar1 : ∀ z, inducedSubPar P s1 (t₁ :: trees.erase t) z = inducedSubPar P st.splay trees z := by
    intro z
    by_cases hz : z ∈ (t₁ :: trees.erase t).flatMap AuxTree.toList
    · exact hpar_act z hz
    · have hz0 : z ∉ trees.flatMap AuxTree.toList := fun hm =>
        hz ((flatMap_perm_of_replace ht ht1_perm).symm.mem_iff.mp hm)
      rw [inducedSubPar_eq_zero_of_not_mem hz, inducedSubPar_eq_zero_of_not_mem hz0]
  have hpairs1 : (forestPairs P s1 (t₁ :: trees.erase t)).Perm (forestPairs P st.splay trees) :=
    forestPairs_perm_cons_erase ht rfl hev_id hout1 W.activeNodup
  have hr_head : r = listHead0 (treeIds P st.splay t) := by
    dsimp only [treeIds]
    rw [← hev_id]
    cases hev : SplayState.evalPairs P s1 t₁ false P.idTag with
    | nil =>
        have hlen := SplayState.evalPairs_length P s1 t₁ false P.idTag
        rw [hev] at hlen
        simp only [List.length_nil] at hlen
        cases t₁ with
        | leaf => exact absurd rfl ht1_ne
        | node _ _ _ => simp [AuxTree.countNodes] at hlen; omega
    | cons p rest =>
        change (SplayState.evalPairs P s1 t₁ false P.idTag).head? = some (r, (s1.nodes r).val) at hhead
        rw [hev] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        have hp_eq : p.1 = r := congrArg Prod.fst hhead
        simp [listHead0, hp_eq]
  have hsdep : splayDepth s1 (2 * st.n + 1) r = t₁.depthOf r := by
    have hdep1' : t₁.depthOf r < t.countNodes := hdep1
    have hlt_k : t₁.depthOf r < 2 * st.n + 1 := by omega
    exact splayDepth_eq_depthOf ht1_inv hr_mem hlt_k
  have hphi_eq : sumTreePhi P st1 = sumTreePhi P st := by
    have hv_eq := (hsizes (vSize P st.splay (trees.flatMap AuxTree.toList)
      (inducedSubPar P st.splay trees) trees)).2.1
    have hPhi1' : sumTreePhi P st1 +
        t.treePhi (vSize P st.splay (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees) trees) =
        sumTreePhi P st +
        t₁.treePhi (vSize P st.splay (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees) trees) := hPhi1
    rw [hv_eq] at hPhi1'
    omega
  exact ⟨t₁, List.mem_cons_self, hr_mem, hW1, ht1_perm, ht1_inv, ht1_rt, hpar1, hpairs1, hr_head,
    hr_left, hpp1, hout1, hH1, hphi_eq, hsdep, hdep1⟩

/-- Expose `v` and find the leftmost node (represented-tree root) of its auxiliary tree. -/
def lctFindRootCost (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    LctState α σ τ × ℕ × ℕ × ℕ :=
  let r1 := lctExposeCost P st v
  let s1 := r1.1.splay
  let lw := SplayState.leftmostWalk P s1 (2 * st.n + 1) v
  let d2 := splayDepth lw.1 (2 * st.n + 1) lw.2
  let s2 := SplayState.splay P lw.1 (2 * st.n + 1) lw.2
  ({ n := st.n, splay := s2, freeHead := r1.1.freeHead }, lw.2, r1.2.1 + d2 / 2, r1.2.2)

/-- Functional wrapper returning the state and root ID from `lctFindRootCost`. -/
def lctFindRoot (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) : LctState α σ τ × ℕ :=
  let r := lctFindRootCost P st v
  (r.1, r.2.1)

theorem lctFindRoot_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tv : AuxTree} {v : ℕ} (htv : tv ∈ trees) (hv : v ∈ tv.toList) :
    let res := lctFindRootCost P st v
    let st' := res.1
    let r := res.2.1
    let halves := res.2.2.1
    let iters := res.2.2.2
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    ∃ trees',
      LctInvWith P st' trees' freeList depth ∧
        (trees'.flatMap AuxTree.toList).Perm active ∧
        (∀ z, inducedSubPar P st'.splay trees' z = par z) ∧
        (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) ∧
        r = subRoot par active.length v ∧
        r ∈ active ∧
        par r = 0 ∧
        halves + sumTreePhi P st' ≤ sumTreePhi P st + 9 * Nat.log 2 (2 * st.n + 1) ∧
        iters + heavyCount P st' ≤ heavyCount P st + 2 * Nat.log 2 (2 * st.n + 1) + 2 := by
  intro res st' r halves iters active par
  rcases lctExpose_spec hL W htv hv with
    ⟨trees1, Lv, ht1_mem, hW1, hact1_perm, hpar1, hpairs1, hpp_v1, _, _, _, _, _, hpot1, hH1⟩
  let r1 := lctExposeCost P st v
  let lw := SplayState.leftmostWalk P r1.1.splay (2 * st.n + 1) v
  let st2 : LctState α σ τ := LctState.mk st.n lw.1 r1.1.freeHead
  rcases lctLeftmostWalk_spec hL hW1 ht1_mem with
    ⟨t₂, ht2_mem, hr2_mem, hW2, ht2_perm, _, _, hpar2, hpairs2, hr_head, _, _, _, hH2, hPhi2, _, _⟩
  have hst2_n : st2.n = st.n := rfl
  rcases lctSplayTree_spec hL hW2 ht2_mem hr2_mem with
    ⟨t_fin, _, _, ht_fin_perm, _, _, _, hW_fin, hH_fin, hpairs_fin, hpar_fin, _, _, htsz_fin, _, hpot_fin⟩
  let trees2 := t₂ :: trees1.erase (AuxTree.node v Lv AuxTree.leaf)
  let trees' := t_fin :: trees2.erase t₂
  refine ⟨trees', ?_⟩
  have hact2_perm : (trees2.flatMap AuxTree.toList).Perm active :=
    (flatMap_perm_of_replace ht1_mem ht2_perm).trans hact1_perm
  have hact'_perm : (trees'.flatMap AuxTree.toList).Perm active :=
    (flatMap_perm_of_replace ht2_mem ht_fin_perm).trans hact2_perm
  have hpar' : ∀ z, inducedSubPar P st'.splay trees' z = par z := fun z => by
    have h1 : inducedSubPar P st'.splay trees' z = inducedSubPar P st2.splay trees2 z := hpar_fin z
    have h2 : inducedSubPar P st2.splay trees2 z = inducedSubPar P r1.1.splay trees1 z := hpar2 z
    rw [h1, h2, hpar1 z]
  have hpairs' : (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) := by
    have h1 : (forestPairs P st'.splay trees').Perm (forestPairs P st2.splay trees2) := hpairs_fin
    exact h1.trans (hpairs2.trans hpairs1)
  have hhead_par0 : inducedSubPar P r1.1.splay trees1
      (listHead0 (treeIds P r1.1.splay (AuxTree.node v Lv AuxTree.leaf))) = 0 :=
    listHead0_par_eq_zero_of_ppar hW1 ht1_mem hpp_v1
  have hr_head' : r = listHead0 (treeIds P r1.1.splay (AuxTree.node v Lv AuxTree.leaf)) := hr_head
  have hr_par0 : par r = 0 := by
    dsimp only [par]
    rw [hr_head', ← hpar1]
    exact hhead_par0
  have hr_reach_v : reaches par active.length r v = true := by
    have hrc := tree_reaches_head hW1 ht1_mem (by simp [AuxTree.toList] : v ∈ (AuxTree.node v Lv AuxTree.leaf).toList)
    rw [hact1_perm.length_eq, reaches_congr hpar1, ← hr_head'] at hrc
    exact hrc
  have hr_sub : r = subRoot par active.length v :=
    (subRoot_eq_of_reaches_zero le_rfl hr_reach_v hr_par0).symm
  have hr_act : r ∈ active := by
    rw [hr_sub]
    exact (W.subRoot_isRoot (List.mem_flatMap.mpr ⟨tv, htv, hv⟩)).1
  have hact2_le : (trees2.flatMap AuxTree.toList).length ≤ 2 * st.n := by
    rw [hact2_perm.length_eq]
    exact active_length_le_two_mul W.activeNodup W.activeValid
  have htsz_fin' : t_fin.treeSize (vSize P st2.splay (trees2.flatMap AuxTree.toList)
      (inducedSubPar P st2.splay trees2) trees2) =
      t₂.treeSize (vSize P st2.splay (trees2.flatMap AuxTree.toList)
      (inducedSubPar P st2.splay trees2) trees2) := htsz_fin
  have htsz_vsize : t_fin.treeSize (vSize P st2.splay (trees2.flatMap AuxTree.toList)
      (inducedSubPar P st2.splay trees2) trees2) ≤ 2 * st.n := by
    have ht2_rep : t₂.treeSize (vSize P st2.splay (trees2.flatMap AuxTree.toList)
        (inducedSubPar P st2.splay trees2) trees2) =
        repSize (trees2.flatMap AuxTree.toList) (inducedSubPar P st2.splay trees2)
          (listHead0 (treeIds P st2.splay t₂)) :=
      treeSize_vSize_eq_repSize hW2 ht2_mem
    rw [htsz_fin', ht2_rep]
    exact (repSize_le_active _).trans hact2_le
  refine ⟨hW_fin, hact'_perm, hpar', hpairs', hr_sub, hr_act, hr_par0, ?_, ?_⟩
  · have hrank_le : t_fin.rank (vSize P st2.splay (trees2.flatMap AuxTree.toList)
        (inducedSubPar P st2.splay trees2) trees2) ≤ Nat.log 2 (2 * st.n + 1) :=
      Nat.log_mono_right (by omega)
    have hpot1' : r1.2.1 + sumTreePhi P r1.1 ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) := hpot1
    have hPhi2' : sumTreePhi P st2 = sumTreePhi P r1.1 := hPhi2
    have hpot_fin' : splayDepth lw.1 (2 * st.n + 1) r / 2 + sumTreePhi P st' +
        3 * (t₂.findSubtree r).rank (vSize P st2.splay (trees2.flatMap AuxTree.toList)
          (inducedSubPar P st2.splay trees2) trees2) ≤
        sumTreePhi P st2 + 3 * t_fin.rank (vSize P st2.splay (trees2.flatMap AuxTree.toList)
          (inducedSubPar P st2.splay trees2) trees2) := hpot_fin
    change r1.2.1 + splayDepth lw.1 (2 * st.n + 1) r / 2 + sumTreePhi P st' ≤ _
    omega
  · have hH_fin' : heavyCount P st' = heavyCount P st2 := hH_fin
    have hH2' : heavyCount P st2 = heavyCount P r1.1 := hH2
    have hH1' : r1.2.2 + heavyCount P r1.1 ≤ heavyCount P st + 2 * Nat.log 2 (2 * st.n + 1) + 2 := hH1
    change r1.2.2 + heavyCount P st' ≤ _
    omega

/-- Connectivity query: expose and find component roots for `u` and `v`, comparing them. -/
def lctConnectedCost (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    LctState α σ τ × Bool × ℕ × ℕ :=
  let r1 := lctFindRootCost P st u
  let r2 := lctFindRootCost P r1.1 v
  (r2.1, r1.2.1 == r2.2.1, r1.2.2.1 + r2.2.2.1, r1.2.2.2 + r2.2.2.2)

theorem lctConnected_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tu tv : AuxTree} {u v : ℕ} (htu : tu ∈ trees) (hu : u ∈ tu.toList)
    (htv : tv ∈ trees) (hv : v ∈ tv.toList) :
    let res := lctConnectedCost P st u v
    let st' := res.1
    let conn := res.2.1
    let halves := res.2.2.1
    let iters := res.2.2.2
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    ∃ trees',
      LctInvWith P st' trees' freeList depth ∧
        (trees'.flatMap AuxTree.toList).Perm active ∧
        (∀ z, inducedSubPar P st'.splay trees' z = par z) ∧
        (forestPairs P st'.splay trees').Perm (forestPairs P st.splay trees) ∧
        (conn = true ↔ subRoot par active.length u = subRoot par active.length v) ∧
        halves + sumTreePhi P st' ≤ sumTreePhi P st + 18 * Nat.log 2 (2 * st.n + 1) ∧
        iters + heavyCount P st' ≤ heavyCount P st + 4 * Nat.log 2 (2 * st.n + 1) + 4 := by
  intro res st' conn halves iters active par
  rcases lctFindRoot_spec hL W htu hu with
    ⟨trees1, hW1, hact1_perm, hpar1, hpairs1, hr1_eq, _, _, hpot1, hH1⟩
  have hv1 : v ∈ trees1.flatMap AuxTree.toList :=
    hact1_perm.symm.mem_iff.mp (List.mem_flatMap.mpr ⟨tv, htv, hv⟩)
  rcases List.mem_flatMap.mp hv1 with ⟨tv1, htv1, hv1'⟩
  rcases lctFindRoot_spec hL hW1 htv1 hv1' with
    ⟨trees2, hW2, hact2_perm, hpar2, hpairs2, hr2_eq, _, _, hpot2, hH2⟩
  refine ⟨trees2, hW2, hact2_perm.trans hact1_perm, fun z => (hpar2 z).trans (hpar1 z),
    hpairs2.trans hpairs1, ?_, ?_, ?_⟩
  · have hsub_v : subRoot (inducedSubPar P (lctFindRootCost P st u).1.splay trees1)
        (trees1.flatMap AuxTree.toList).length v = subRoot par active.length v :=
      subRoot_eq_of_LctInvWith_agree W hW1 hact1_perm.symm (fun z => (hpar1 z).symm)
        (List.mem_flatMap.mpr ⟨tv, htv, hv⟩)
    have hconn_iff : conn = true ↔ (lctFindRootCost P st u).2.1 =
        (lctFindRootCost P (lctFindRootCost P st u).1 v).2.1 := by
      dsimp only [conn, res, lctConnectedCost]
      exact beq_iff_eq
    rw [hconn_iff, hr1_eq, hr2_eq, hsub_v]
  · have hr1_n : (lctFindRootCost P st u).1.n = st.n := rfl
    rw [hr1_n] at hpot2
    have hst'_eq : st' = (lctFindRootCost P (lctFindRootCost P st u).1 v).1 := rfl
    change (lctFindRootCost P st u).2.2.1 + (lctFindRootCost P (lctFindRootCost P st u).1 v).2.2.1 +
        sumTreePhi P st' ≤ _
    rw [hst'_eq]
    omega
  · have hr1_n : (lctFindRootCost P st u).1.n = st.n := rfl
    rw [hr1_n] at hH2
    have hst'_eq : st' = (lctFindRootCost P (lctFindRootCost P st u).1 v).1 := rfl
    change (lctFindRootCost P st u).2.2.2 + (lctFindRootCost P (lctFindRootCost P st u).1 v).2.2.2 +
        heavyCount P st' ≤ _
    rw [hst'_eq]
    omega

/-! ### `lctReroot` (expose + lazy reversal) -/

/-- Expose `v` and reverse its represented-tree path so `v` becomes the new component root. -/
def lctRerootCost (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    LctState α σ τ × ℕ × ℕ :=
  let r1 := lctExposeCost P st v
  let s' := SplayState.revNode P r1.1.splay v
  ({ n := st.n, splay := s', freeHead := r1.1.freeHead }, r1.2.1, r1.2.2)

/-- Functional wrapper for `lctRerootCost`. -/
def lctReroot (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) : LctState α σ τ :=
  (lctRerootCost P st v).1

end
end MinCostFlow.LinkCut
