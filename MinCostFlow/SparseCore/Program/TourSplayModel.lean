module

public import MinCostFlow.SparseCore.Program.TourPayload
public import MinCostFlow.LinkCut.SplayQuery
public import MinCostFlow.LinkCut.PathTree.Descend
import Mathlib.Tactic

/-!
# Splay-forest sequence model for core rotation tours

Specializes the generic `LinkCut.SplayState` machinery to `tourPayload` with zero virtual weights
(`tourVSize := fun _ => 0`) and clean reversal bits (`rev = false` on every node `u ≤ cap`).

Because `tourPayload` has trivial lazy tags (`Unit`) and all nodes have `rev = false`:
- `pushDown` and `pushPath` are the identity on states;
- `evalPairs tourPayload st t false () = t.toList.map (fun id => (id, (st.nodes id).val))`;
- `splay` preserves `t.toList` identically and satisfies Sleator–Tarjan's amortized bound;
- `tourDetachLeft`, `tourDetachRight`, `tourAttachLeft`, `tourSetVal`, `tourAllocSingleton`,
  `findLeftmost`, and `descend` preserve `TourForestInv` with `O(log (cap + 2))` amortized
  potential change.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree SplayState

/-! ## Potential and clean-state lemmas -/

/-- Zero virtual-weight function used for tour splay sequences (no dashed children). -/
def tourVSize : ℕ → ℕ := fun _ => 0

/-- Total Sleator–Tarjan potential of a forest of tour splay trees. -/
def forestPhi (trees : List AuxTree) : ℕ :=
  (trees.map (AuxTree.treePhi tourVSize)).sum

theorem treeSize_tourVSize (t : AuxTree) : t.treeSize tourVSize = t.countNodes := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr => simp [AuxTree.treeSize, AuxTree.countNodes, tourVSize, ihl, ihr]

theorem rank_tourVSize_le {t : AuxTree} {cap : ℕ} (h : t.countNodes ≤ cap) :
    t.rank tourVSize ≤ Nat.log 2 (cap + 2) := by
  simp only [AuxTree.rank, treeSize_tourVSize]
  exact Nat.log_mono_right (by omega)

theorem treePhi_singleton_tourVSize (x : ℕ) :
    (AuxTree.node x .leaf .leaf).treePhi tourVSize = 0 := by
  simp [AuxTree.treePhi, AuxTree.rank, AuxTree.treeSize, tourVSize]

/-- Every allocated node `0 .. cap` has `rev = false`. -/
def TourNoRev (cap : ℕ) (st : SplayState TourVal TourSum Unit) : Prop :=
  ∀ u ≤ cap, (st.nodes u).rev = false

theorem tourPushDown_eq_self {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    (hnr : TourNoRev cap st) (hx : x ≤ cap) :
    pushDown tourPayload st x = st := by
  apply pushDown_clean tourPayload_laws (hnr x hx)
  rfl

theorem tourPushPath_eq_self {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    (hptr : PtrOk cap st) (hnr : TourNoRev cap st) :
    ∀ fuel x, x ≤ cap → pushPath tourPayload st fuel x = st
  | 0, _, _ => rfl
  | k + 1, x, hx => by
    unfold pushPath
    by_cases hx0 : x = 0
    · simp [hx0]
    · simp only [hx0, ↓reduceIte]
      by_cases hp0 : (st.nodes x).par = 0
      · simp only [hp0, ↓reduceIte]
        exact tourPushDown_eq_self hnr hx
      · simp only [hp0, ↓reduceIte]
        rw [tourPushPath_eq_self hptr hnr k (st.nodes x).par (hptr x hx).2.2.1]
        exact tourPushDown_eq_self hnr hx

theorem tourEvalPairs_eq_map {st : SplayState TourVal TourSum Unit} {t : AuxTree}
    (hnr : ∀ u ∈ t.toList, (st.nodes u).rev = false) :
    evalPairs tourPayload st t false () = t.toList.map fun id => (id, (st.nodes id).val) := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
    have hid : (st.nodes id).rev = false := hnr id (by simp [AuxTree.toList])
    have hl : ∀ u ∈ l.toList, (st.nodes u).rev = false :=
      fun u hu => hnr u (by simp [AuxTree.toList, hu])
    have hr : ∀ u ∈ r.toList, (st.nodes u).rev = false :=
      fun u hu => hnr u (by simp [AuxTree.toList, hu])
    rw [evalPairs]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor, hid,
      AuxTree.toList, List.map_append, List.map_cons, List.map_nil]
    have htag : tourPayload.compTag () (st.nodes id).tag = () := rfl
    have hval : tourPayload.actVal () (st.nodes id).val = (st.nodes id).val := rfl
    rw [htag, hval, ihl hl, ihr hr]

theorem tourEvalPairs_eq_iff_toList {st₁ st₂ : SplayState TourVal TourSum Unit} {t₁ t₂ : AuxTree}
    (h1 : ∀ u ∈ t₁.toList, (st₁.nodes u).rev = false)
    (h2 : ∀ u ∈ t₂.toList, (st₂.nodes u).rev = false)
    (hev : evalPairs tourPayload st₁ t₁ false () = evalPairs tourPayload st₂ t₂ false ()) :
    t₁.toList = t₂.toList := by
  have hm := congrArg (List.map Prod.fst) hev
  rw [tourEvalPairs_eq_map h1, tourEvalPairs_eq_map h2, List.map_map, List.map_map] at hm
  simpa [Function.comp_def] using hm

/-! ## Forest invariant `TourForestInv` -/

/-- Invariant on a forest of disjoint non-empty splay trees over nodes `1 .. cap`. -/
structure TourForestInv (cap : ℕ) (st : SplayState TourVal TourSum Unit)
    (trees : List AuxTree) : Prop where
  nonEmpty : ∀ t ∈ trees, t ≠ .leaf
  treesInv : ∀ t ∈ trees, TreeInv tourPayload st t
  nodupAll : (trees.flatMap AuxTree.toList).Nodup
  inCap : ∀ u ∈ trees.flatMap AuxTree.toList, 1 ≤ u ∧ u ≤ cap
  ptrOk : PtrOk cap st
  noRev : TourNoRev cap st

theorem TourForestInv.mem_inCap {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees)
    {u : ℕ} (hu : u ∈ t.toList) : 1 ≤ u ∧ u ≤ cap :=
  h.inCap u (List.mem_flatMap.mpr ⟨t, ht, hu⟩)

theorem TourForestInv.countNodes_le {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees) :
    t.countNodes ≤ cap := by
  have hsub : ∀ u ∈ t.toList, u ∈ (List.range' 1 cap) := fun u hu => by
    have hb := h.mem_inCap ht hu
    exact List.mem_range'.mpr ⟨u - 1, by omega, by omega⟩
  have hnd : t.toList.Nodup := (h.treesInv t ht).nodup
  have hle : t.toList.length ≤ (List.range' 1 cap).length := by
    have hfin : t.toList.toFinset ⊆ (List.range' 1 cap).toFinset := fun u hu =>
      List.mem_toFinset.mpr (hsub u (List.mem_toFinset.mp hu))
    have hcard := Finset.card_le_card hfin
    rw [List.toFinset_card_of_nodup hnd,
      List.toFinset_card_of_nodup List.nodup_range'] at hcard
    exact hcard
  rw [AuxTree.length_toList, List.length_range'] at hle
  exact hle

theorem TourForestInv.sum_eq {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees) :
    (st.nodes t.rootId).sum =
      tourPayload.listSummary (t.toList.map fun id => (id, (st.nodes id).val)) := by
  have hinv := h.treesInv t ht
  have hne := h.nonEmpty t ht
  have hnr : ∀ u ∈ t.toList, (st.nodes u).rev = false :=
    fun u hu => h.noRev u (h.mem_inCap ht hu).2
  cases t with
  | leaf => exact absurd rfl hne
  | node id l r =>
    have hsum := hinv.sub.2.2.2.2.2.2.1
    simp only [AuxTree.rootId]
    rw [hsum, tourEvalPairs_eq_map hnr]

theorem TourForestInv.sum_sz {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees) :
    (st.nodes t.rootId).sum.sz = t.toList.length := by
  rw [h.sum_eq ht, tourPayload_listSummary_sz, List.length_map]

theorem TourForestInv.sum_openCnt {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees) :
    (st.nodes t.rootId).sum.openCnt = (t.toList.filter fun u => (st.nodes u).val.isOpen).length := by
  rw [h.sum_eq ht, tourPayload_listSummary_openCnt, List.filter_map, List.length_map]
  rfl

theorem TourForestInv.sum_markCnt {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees) :
    (st.nodes t.rootId).sum.markCnt = (t.toList.filter fun u => (st.nodes u).val.isMarked).length := by
  rw [h.sum_eq ht, tourPayload_listSummary_markCnt, List.filter_map, List.length_map]
  rfl

theorem TourForestInv.sum_rootTag {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (h : TourForestInv cap st trees) {t : AuxTree} (ht : t ∈ trees) :
    (st.nodes t.rootId).sum.rootTag = (t.toList.map fun u => (st.nodes u).val.rootTag).foldr max 0 := by
  rw [h.sum_eq ht, tourPayload_listSummary_rootTag, List.map_map]
  rfl

theorem TourForestInv.disjoint_other {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {t : AuxTree} (h : TourForestInv cap st (pre ++ t :: post))
    {t' : AuxTree} (ht' : t' ∈ pre ++ post) {u : ℕ} (hu : u ∈ t'.toList) :
    u ∉ t.toList := by
  have hnd := h.nodupAll
  rw [List.flatMap_append, List.flatMap_cons] at hnd
  have h1 := List.nodup_append.mp hnd
  have h2 := List.nodup_append.mp h1.2.1
  rcases List.mem_append.mp ht' with hpre | hpost
  · intro hut
    exact h1.2.2 u (List.mem_flatMap.mpr ⟨t', hpre, hu⟩) u (List.mem_append.mpr (Or.inl hut)) rfl
  · intro hut
    exact h2.2.2 u hut u (List.mem_flatMap.mpr ⟨t', hpost, hu⟩) rfl

/-! ## `splay` on a tour forest -/

theorem treeInv_agree {st₁ st₂ : SplayState TourVal TourSum Unit} {t : AuxTree}
    (ht : TreeInv tourPayload st₁ t) (hag : ∀ u ∈ t.toList, st₂.nodes u = st₁.nodes u) :
    TreeInv tourPayload st₂ t :=
  ⟨ht.nodup, SubtreeInv_agree ht.sub fun u hu => (hag u hu).symm⟩

theorem tourNoRev_setLeft {cap x l : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : TourNoRev cap st) : TourNoRev cap (st.setLeft x l) := fun u hu => by
  by_cases hux : u = x
  · subst hux; simp [setLeft, updateNode, h u hu]
  · simp [setLeft, updateNode, hux, h u hu]

theorem tourNoRev_setRight {cap x r : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : TourNoRev cap st) : TourNoRev cap (st.setRight x r) := fun u hu => by
  by_cases hux : u = x
  · subst hux; simp [setRight, updateNode, h u hu]
  · simp [setRight, updateNode, hux, h u hu]

theorem tourNoRev_setPar {cap x p : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : TourNoRev cap st) : TourNoRev cap (st.setPar x p) := fun u hu => by
  by_cases hux : u = x
  · subst hux; simp [setPar, updateNode, h u hu]
  · simp [setPar, updateNode, hux, h u hu]

theorem tourNoRev_setPpar {cap x pp : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : TourNoRev cap st) : TourNoRev cap (st.setPpar x pp) := fun u hu => by
  by_cases hux : u = x
  · subst hux; simp [setPpar, updateNode, h u hu]
  · simp [setPpar, updateNode, hux, h u hu]

theorem tourNoRev_pull {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    (h : TourNoRev cap st) : TourNoRev cap (pull tourPayload st x) :=
  fun u hu => by rw [pull_rev_eq]; exact h u hu

theorem tourNoRev_rotate {cap y : ℕ} {s : SplayState TourVal TourSum Unit}
    (hr : TourNoRev cap s) : TourNoRev cap (rotate tourPayload s y) := by
  by_cases hy0 : y = 0
  · simp [rotate, hy0, hr]
  by_cases hp0 : (s.nodes y).par = 0
  · simp [rotate, hy0, hp0, hr]
  unfold rotate; dsimp only
  rw [ite_eq_right_iff.mpr (fun h => absurd h hy0),
    ite_eq_right_iff.mpr (fun h => absurd h hp0)]
  refine tourNoRev_pull (tourNoRev_pull ?_)
  split_ifs <;>
    repeat' (first | exact hr | apply tourNoRev_setLeft | apply tourNoRev_setRight |
      apply tourNoRev_setPar | apply tourNoRev_setPpar)

private theorem tourNoRev_splay {cap fuel x : ℕ} {st : SplayState TourVal TourSum Unit}
    (hptr : PtrOk cap st) (hnr : TourNoRev cap st) (hx : x ≤ cap) :
    TourNoRev cap (splay tourPayload st fuel x) := by
  have hstep : ∀ (s : SplayState TourVal TourSum Unit) (y : ℕ),
      TourNoRev cap s → TourNoRev cap (splayStep tourPayload s y) := by
    intro s y hr
    unfold splayStep; dsimp only
    split_ifs
    · exact hr
    · exact hr
    · exact tourNoRev_rotate hr
    · exact tourNoRev_rotate (tourNoRev_rotate hr)
    · exact tourNoRev_rotate (tourNoRev_rotate hr)
  have hloop : ∀ k (s : SplayState TourVal TourSum Unit),
      TourNoRev cap s → TourNoRev cap (splayLoop tourPayload s k x) := by
    intro k
    induction k with
    | zero => intro s hr; exact hr
    | succ k ih =>
      intro s hr
      unfold splayLoop; split_ifs
      · exact hr
      · exact hr
      · exact ih _ (hstep s x hr)
  unfold splay; split_ifs
  · exact hnr
  · rw [tourPushPath_eq_self hptr hnr fuel x hx]
    exact hloop fuel st hnr

theorem val_setLeft_eq (s : SplayState TourVal TourSum Unit) (x l u : ℕ) :
    ((s.setLeft x l).nodes u).val = (s.nodes u).val := by
  by_cases hux : u = x <;> simp [setLeft, updateNode, hux]

theorem val_setRight_eq (s : SplayState TourVal TourSum Unit) (x r u : ℕ) :
    ((s.setRight x r).nodes u).val = (s.nodes u).val := by
  by_cases hux : u = x <;> simp [setRight, updateNode, hux]

theorem val_setPar_eq (s : SplayState TourVal TourSum Unit) (x p u : ℕ) :
    ((s.setPar x p).nodes u).val = (s.nodes u).val := by
  by_cases hux : u = x <;> simp [setPar, updateNode, hux]

theorem val_setPpar_eq (s : SplayState TourVal TourSum Unit) (x pp u : ℕ) :
    ((s.setPpar x pp).nodes u).val = (s.nodes u).val := by
  by_cases hux : u = x <;> simp [setPpar, updateNode, hux]

theorem val_rotate_eq (s : SplayState TourVal TourSum Unit) (y u : ℕ) :
    ((rotate tourPayload s y).nodes u).val = (s.nodes u).val := by
  by_cases hy0 : y = 0
  · simp [rotate, hy0]
  by_cases hp0 : (s.nodes y).par = 0
  · simp [rotate, hy0, hp0]
  unfold rotate; dsimp only
  rw [ite_eq_right_iff.mpr (fun h => absurd h hy0),
    ite_eq_right_iff.mpr (fun h => absurd h hp0),
    pull_val_eq', pull_val_eq']
  split_ifs <;> simp only [val_setLeft_eq, val_setRight_eq, val_setPar_eq, val_setPpar_eq]

private theorem val_splay_eq {cap fuel x : ℕ} {st : SplayState TourVal TourSum Unit}
    (hptr : PtrOk cap st) (hnr : TourNoRev cap st) (hx : x ≤ cap) :
    ∀ u ≤ cap, ((splay tourPayload st fuel x).nodes u).val = (st.nodes u).val := by
  have hstep : ∀ (s : SplayState TourVal TourSum Unit) (y u : ℕ),
      ((splayStep tourPayload s y).nodes u).val = (s.nodes u).val := by
    intro s y u
    unfold splayStep; dsimp only
    split_ifs
    · rfl
    · rfl
    · exact val_rotate_eq s y u
    · rw [val_rotate_eq, val_rotate_eq]
    · rw [val_rotate_eq, val_rotate_eq]
  have hloop : ∀ k (s : SplayState TourVal TourSum Unit) u,
      ((splayLoop tourPayload s k x).nodes u).val = (s.nodes u).val := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro s u; unfold splayLoop; split_ifs
      · rfl
      · rfl
      · rw [ih, hstep]
  intro u _
  unfold splay; split_ifs
  · rfl
  · rw [tourPushPath_eq_self hptr hnr fuel x hx]
    exact hloop fuel st u

/-- Splaying a node `x ∈ t.toList` in a tour forest brings `x` to the root of `t'`, preserves
`t'.toList = t.toList`, leaves all other trees untouched, preserves all node values, and satisfies
the Sleator–Tarjan amortized potential bound. -/
theorem tourSplay_preserves {cap fuel x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {t : AuxTree}
    (h : TourForestInv cap st (pre ++ t :: post))
    (hx : x ∈ t.toList) (hfuel : t.depthOf x < fuel) :
    ∃ t',
      let st' := splay tourPayload st fuel x
      TourForestInv cap st' (pre ++ t' :: post) ∧
      t' ≠ .leaf ∧
      t'.rootId = x ∧
      t'.toList = t.toList ∧
      (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
      (∀ u ≤ cap, (st'.nodes u).val = (st.nodes u).val) ∧
      forestPhi (pre ++ t' :: post) + t.depthOf x / 2 ≤
        forestPhi (pre ++ t :: post) + 3 * Nat.log 2 (cap + 2) := by
  have ht_mem : t ∈ pre ++ t :: post := by simp
  have hx_cap : x ≤ cap := (h.mem_inCap ht_mem hx).2
  rcases splay_preserves_and_phi tourPayload_laws (h.treesInv t ht_mem) hx hfuel with
    ⟨t', ht', ht'_ne, ht'_root, ht'_perm, ht'_ev, _, _, _, ht'_out, ht'_phi⟩
  set st' := splay tourPayload st fuel x
  have hnr' : TourNoRev cap st' := tourNoRev_splay h.ptrOk h.noRev hx_cap
  have hlist_eq : t'.toList = t.toList := by
    refine tourEvalPairs_eq_iff_toList (fun u hu => hnr' u ?_) (fun u hu => h.noRev u ?_) ht'_ev
    · exact (h.mem_inCap ht_mem (ht'_perm.mem_iff.mp hu)).2
    · exact (h.mem_inCap ht_mem hu).2
  have hflat_eq : (pre ++ t' :: post).flatMap AuxTree.toList =
      (pre ++ t :: post).flatMap AuxTree.toList := by
    simp only [List.flatMap_append, List.flatMap_cons, hlist_eq]
  have hinv' : TourForestInv cap st' (pre ++ t' :: post) :=
    { nonEmpty := fun s hs => by
        simp only [List.mem_append, List.mem_cons] at hs
        rcases hs with h1 | rfl | h2
        · exact h.nonEmpty s (by simp [h1])
        · exact ht'_ne
        · exact h.nonEmpty s (by simp [h2])
      treesInv := fun s hs => by
        simp only [List.mem_append, List.mem_cons] at hs
        rcases hs with h1 | rfl | h2
        · exact treeInv_agree (h.treesInv s (by simp [h1]))
            fun u hu => ht'_out u (h.disjoint_other (by simp [h1]) hu)
        · exact ht'
        · exact treeInv_agree (h.treesInv s (by simp [h2]))
            fun u hu => ht'_out u (h.disjoint_other (by simp [h2]) hu)
      nodupAll := hflat_eq ▸ h.nodupAll
      inCap := fun u hu => h.inCap u (hflat_eq ▸ hu)
      ptrOk := h.ptrOk.splay hx_cap
      noRev := hnr' }
  have hcnt : t'.countNodes ≤ cap := hinv'.countNodes_le (by simp)
  have hrk : t'.rank tourVSize ≤ Nat.log 2 (cap + 2) := rank_tourVSize_le hcnt
  have hphi_t := (ht'_phi tourVSize).2
  refine ⟨t', hinv', ht'_ne, ht'_root, hlist_eq, ht'_out, val_splay_eq h.ptrOk h.noRev hx_cap, ?_⟩
  simp only [forestPhi, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

theorem TourForestInv.perm {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees₁ trees₂ : List AuxTree} (h : TourForestInv cap st trees₁)
    (hp : trees₁.Perm trees₂) :
    TourForestInv cap st trees₂ ∧ forestPhi trees₂ = forestPhi trees₁ := by
  have hflat : (trees₁.flatMap AuxTree.toList).Perm (trees₂.flatMap AuxTree.toList) :=
    hp.flatMap_right AuxTree.toList
  refine ⟨⟨fun t ht => h.nonEmpty t (hp.mem_iff.mpr ht),
    fun t ht => h.treesInv t (hp.mem_iff.mpr ht),
    hflat.nodup_iff.mp h.nodupAll,
    fun u hu => h.inCap u (hflat.mem_iff.mpr hu),
    h.ptrOk, h.noRev⟩, ?_⟩
  exact (hp.symm.map (AuxTree.treePhi tourVSize)).sum_eq

/-- Allocating a fresh (or detached) singleton node `x` with `1 ≤ x ≤ cap'` adds
`.node x .leaf .leaf` to the forest with zero potential change. -/
theorem tourAllocSingleton_preserves {cap cap' x : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} (v : TourVal)
    (h : TourForestInv cap st trees) (hcap : cap ≤ cap')
    (hx1 : 1 ≤ x) (hx_cap : x ≤ cap') (hx_fresh : x ∉ trees.flatMap AuxTree.toList)
    (hptr_ext : ∀ u, cap < u → u ≤ cap' → u ≠ x →
      (st.nodes u).left ≤ cap' ∧ (st.nodes u).right ≤ cap' ∧
      (st.nodes u).par ≤ cap' ∧ (st.nodes u).ppar ≤ cap' ∧ (st.nodes u).rev = false) :
    let st' := makeSingleton tourPayload st x v 0
    TourForestInv cap' st' (AuxTree.node x .leaf .leaf :: trees) ∧
    forestPhi (AuxTree.node x .leaf .leaf :: trees) = forestPhi trees := by
  rcases makeSingleton_treeInv tourPayload_laws st (by omega : x ≠ 0) v 0 with
    ⟨hxt, _, _, _, _, hout⟩
  set st' := makeSingleton tourPayload st x v 0
  have hinv' : TourForestInv cap' st' (AuxTree.node x .leaf .leaf :: trees) :=
    { nonEmpty := fun s hs => by
        rcases List.mem_cons.mp hs with rfl | hs'
        · simp
        · exact h.nonEmpty s hs'
      treesInv := fun s hs => by
        rcases List.mem_cons.mp hs with rfl | hs'
        · exact hxt
        · exact treeInv_agree (h.treesInv s hs')
            fun u hu => hout u fun heq => hx_fresh (List.mem_flatMap.mpr ⟨s, hs', heq ▸ hu⟩)
      nodupAll := by
        rw [List.flatMap_cons]
        simpa [AuxTree.toList] using List.nodup_cons.mpr ⟨hx_fresh, h.nodupAll⟩
      inCap := fun u hu => by
        rw [List.flatMap_cons] at hu
        simp only [AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at hu
        rcases hu with rfl | hu'
        · exact ⟨hx1, hx_cap⟩
        · have hb := h.inCap u hu'; exact ⟨hb.1, le_trans hb.2 hcap⟩
      ptrOk := fun u hu => by
        by_cases hux : u = x
        · subst hux; simp [st', makeSingleton, setNode]
        · rw [hout u hux]
          by_cases huc : u ≤ cap
          · have hp := h.ptrOk u huc
            exact ⟨le_trans hp.1 hcap, le_trans hp.2.1 hcap, le_trans hp.2.2.1 hcap, le_trans hp.2.2.2 hcap⟩
          · have he := hptr_ext u (by omega) hu hux
            exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1⟩
      noRev := fun u hu => by
        by_cases hux : u = x
        · subst hux; simp [st', makeSingleton, setNode]
        · rw [hout u hux]
          by_cases huc : u ≤ cap
          · exact h.noRev u huc
          · exact (hptr_ext u (by omega) hu hux).2.2.2.2 }
  exact ⟨hinv', by simp [forestPhi, treePhi_singleton_tourVSize]⟩

/-! ## `leftmostWalk` and `descend` on clean tour trees -/

/-- On a clean tour forest, `leftmostWalk` leaves `st` unchanged and reaches the head of `t.toList`
in at most `t.depthOf m + 1` steps. -/
theorem tourLeftmostWalk_spec {cap fuel : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} {t : AuxTree}
    (h : TourForestInv cap st trees) (ht : t ∈ trees) (hfuel : t.countNodes ≤ fuel) :
    let res := leftmostWalk tourPayload st fuel t.rootId
    res.1 = st ∧
    res.2 ∈ t.toList ∧
    t.toList.head? = some res.2 ∧
    walkSteps tourPayload st fuel t.rootId = t.depthOf res.2 + 1 := by
  have hsub : ∀ {k rp : ℕ} (c : AuxTree), c ≠ .leaf → c.toList.Nodup →
      SubtreeInv tourPayload st rp c → (∀ u ∈ c.toList, u ≤ cap) → c.countNodes ≤ k →
      (leftmostWalk tourPayload st k c.rootId).1 = st ∧
      (leftmostWalk tourPayload st k c.rootId).2 ∈ c.toList ∧
      c.toList.head? = some (leftmostWalk tourPayload st k c.rootId).2 ∧
      walkSteps tourPayload st k c.rootId = c.depthOf (leftmostWalk tourPayload st k c.rootId).2 + 1 := by
    intro k
    induction k with
    | zero =>
      intro _ c hne _ _ _ hk
      cases c with | leaf => exact absurd rfl hne | node _ _ _ => simp [AuxTree.countNodes] at hk
    | succ k ih =>
      intro rp c hne hnd hc hcap hk
      cases c with
      | leaf => exact absurd rfl hne
      | node id l r =>
        rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hid_nl, _, _, _⟩
        rcases hc with ⟨hid_nz, hl_eq, _, _, _, _, _, hsub_l, _⟩
        have hid_cap : id ≤ cap := hcap id (by simp [AuxTree.toList])
        have hpd : pushDown tourPayload st id = st := tourPushDown_eq_self h.noRev hid_cap
        have hcap_l : ∀ u ∈ l.toList, u ≤ cap := fun u hu => hcap u (by simp [AuxTree.toList, hu])
        have hk_l : l.countNodes ≤ k := by simp only [AuxTree.countNodes] at hk; omega
        cases hl_c : l with
        | leaf =>
          subst hl_c
          have hl0 : (st.nodes id).left = 0 := by simpa [AuxTree.rootId] using hl_eq
          simp [leftmostWalk, walkSteps, AuxTree.rootId, hid_nz, hpd, hl0, AuxTree.toList,
            AuxTree.depthOf]
        | node lid lL lR =>
          subst hl_c
          have hl_nz : lid ≠ 0 := hsub_l.1
          have hl_id : (st.nodes id).left = lid := hl_eq
          have hrec := ih (.node lid lL lR) (by simp) hl_nd hsub_l hcap_l hk_l
          have hwalk_eq : leftmostWalk tourPayload st (k + 1) id =
              leftmostWalk tourPayload st k lid := by
            simp [leftmostWalk, hid_nz, hpd, hl_id, hl_nz]
          have hsteps_eq : walkSteps tourPayload st (k + 1) id =
              1 + walkSteps tourPayload st k lid := by
            simp [walkSteps, hid_nz, hpd, hl_id, hl_nz]
          simp only [AuxTree.rootId] at hrec ⊢
          rw [hwalk_eq, hsteps_eq]
          set m := (leftmostWalk tourPayload st k lid).2
          have hm_l : m ∈ (AuxTree.node lid lL lR).toList := hrec.2.1
          have hmid : m ≠ id := fun heq => hid_nl (heq ▸ hm_l)
          have hl_ne : (AuxTree.node lid lL lR).toList ≠ [] := List.ne_nil_of_mem hm_l
          refine ⟨hrec.1, ?_, ?_, ?_⟩
          · rw [AuxTree.toList]; simp [hm_l]
          · rw [AuxTree.toList, List.append_assoc, List.head?_append_of_ne_nil _ hl_ne]
            exact hrec.2.2.1
          · rw [AuxTree.depthOf]
            simp only [hmid, ↓reduceIte, hm_l]
            exact hrec.2.2.2 ▸ (Nat.add_comm _ 1).symm ▸ rfl
  exact hsub t (h.nonEmpty t ht) (h.treesInv t ht).nodup (h.treesInv t ht).sub
    (fun u hu => (h.mem_inCap ht hu).2) hfuel

/-- On a clean tour forest, `descend` leaves `st` unchanged, returns the **exact first** ready node
in `t.toList` (`t.toList.find? (fun u => rv (st.nodes u).val) = some y`), and visits
`t.depthOf y + 1` nodes. -/
theorem tourDescend_first {cap fuel : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} {t : AuxTree} {rs : TourSum → Bool} {rv : TourVal → Bool}
    (hR : ReadyLaw tourPayload rs rv)
    (h : TourForestInv cap st trees) (ht : t ∈ trees)
    (hrs : rs (st.nodes t.rootId).sum = true) (hfuel : t.countNodes ≤ fuel) :
    let res := descend tourPayload rs rv st fuel t.rootId
    res.1 = st ∧
    res.2 ∈ t.toList ∧
    t.toList.find? (fun u => rv (st.nodes u).val) = some res.2 ∧
    descendSteps tourPayload rs rv st fuel t.rootId = t.depthOf res.2 + 1 := by
  have hsub : ∀ {k rp : ℕ} (c : AuxTree), c ≠ .leaf → c.toList.Nodup →
      SubtreeInv tourPayload st rp c → (∀ u ∈ c.toList, u ≤ cap) →
      rs (st.nodes c.rootId).sum = true → c.countNodes ≤ k →
      (descend tourPayload rs rv st k c.rootId).1 = st ∧
      (descend tourPayload rs rv st k c.rootId).2 ∈ c.toList ∧
      c.toList.find? (fun u => rv (st.nodes u).val) = some (descend tourPayload rs rv st k c.rootId).2 ∧
      descendSteps tourPayload rs rv st k c.rootId =
        c.depthOf (descend tourPayload rs rv st k c.rootId).2 + 1 := by
    intro k
    induction k with
    | zero =>
      intro _ c hne _ _ _ _ hk
      cases c with | leaf => exact absurd rfl hne | node _ _ _ => simp [AuxTree.countNodes] at hk
    | succ k ih =>
      intro rp c hne hnd hc hcap hcrs hk
      cases c with
      | leaf => exact absurd rfl hne
      | node id l r =>
        rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj⟩
        rcases hc with ⟨_, hl_eq, hr_eq, _, _, _, hsum_id, hsub_l, hsub_r⟩
        have hid_cap : id ≤ cap := hcap id (by simp [AuxTree.toList])
        have hpd : pushDown tourPayload st id = st := tourPushDown_eq_self h.noRev hid_cap
        have hdesc_eq : descend tourPayload rs rv st (k + 1) id =
            if (st.nodes id).left ≠ 0 ∧ rs (st.nodes (st.nodes id).left).sum = true then
              descend tourPayload rs rv st k (st.nodes id).left
            else if rv (st.nodes id).val = true then (st, id)
            else descend tourPayload rs rv st k (st.nodes id).right := by
          simp [descend, hpd]
        have hsteps_eq : descendSteps tourPayload rs rv st (k + 1) id =
            if (st.nodes id).left ≠ 0 ∧ rs (st.nodes (st.nodes id).left).sum = true then
              1 + descendSteps tourPayload rs rv st k (st.nodes id).left
            else if rv (st.nodes id).val = true then 1
            else 1 + descendSteps tourPayload rs rv st k (st.nodes id).right := by
          simp [descendSteps, hpd]
        simp only [AuxTree.rootId] at hcrs ⊢
        rw [hdesc_eq, hsteps_eq, hl_eq, hr_eq]
        have hnone_of : ∀ (a : AuxTree), SubtreeInv tourPayload st id a →
            (∀ u ∈ a.toList, u ≤ cap) →
            ¬ (a.rootId ≠ 0 ∧ rs (st.nodes a.rootId).sum = true) →
            a.toList.find? (fun u => rv (st.nodes u).val) = none := by
          intro a ha hacap hna
          cases a with
          | leaf => rfl
          | node aid aL aR =>
            have hsum_a := ha.2.2.2.2.2.2.1
            rw [tourEvalPairs_eq_map (fun u hu => h.noRev u (hacap u hu))] at hsum_a
            have hfalse : rs (st.nodes aid).sum ≠ true := fun ht => hna ⟨ha.1, ht⟩
            rw [List.find?_eq_none]
            intro u hu huv
            apply hfalse
            rw [hsum_a, hR]
            exact ⟨(u, (st.nodes u).val), List.mem_map.mpr ⟨u, hu, rfl⟩, huv⟩
        by_cases hgl : l.rootId ≠ 0 ∧ rs (st.nodes l.rootId).sum = true
        · rw [ite_eq_left_iff.mpr (fun hn => absurd hgl hn),
            ite_eq_left_iff.mpr (fun hn => absurd hgl hn)]
          have hl_ne : l ≠ .leaf := fun h0 => hgl.1 (by simp [h0, AuxTree.rootId])
          have hrec := ih l hl_ne hl_nd hsub_l (fun u hu => hcap u (by simp [AuxTree.toList, hu]))
            hgl.2 (by simp [AuxTree.countNodes] at hk; omega)
          set y := (descend tourPayload rs rv st k l.rootId).2
          have hy_l : y ∈ l.toList := hrec.2.1
          have hy_ne : y ≠ id := fun heq => hid_nl (heq ▸ hy_l)
          refine ⟨hrec.1, by simp [AuxTree.toList, hy_l], ?_, ?_⟩
          · simp only [AuxTree.toList, List.append_assoc, List.find?_append, hrec.2.2.1]
            rfl
          · simp only [AuxTree.depthOf, hy_ne, ↓reduceIte, hy_l]; omega
        · rw [ite_eq_right_iff.mpr (fun ht => absurd ht hgl),
            ite_eq_right_iff.mpr (fun ht => absurd ht hgl)]
          have hl_none : l.toList.find? (fun u => rv (st.nodes u).val) = none :=
            hnone_of l hsub_l (fun u hu => hcap u (by simp [AuxTree.toList, hu])) hgl
          by_cases hgv : rv (st.nodes id).val = true
          · rw [ite_eq_left_iff.mpr (fun hn => absurd hgv hn),
              ite_eq_left_iff.mpr (fun hn => absurd hgv hn)]
            refine ⟨rfl, by simp [AuxTree.toList], ?_, by simp [AuxTree.depthOf]⟩
            simp [AuxTree.toList, List.append_assoc, List.find?_append, hl_none, hgv]
          · rw [ite_eq_right_iff.mpr (fun ht => absurd ht hgv),
              ite_eq_right_iff.mpr (fun ht => absurd ht hgv)]
            have hready : ∃ u ∈ r.toList, rv (st.nodes u).val = true := by
              rw [tourEvalPairs_eq_map (fun u hu => h.noRev u (hcap u hu))] at hsum_id
              obtain ⟨⟨u, vu⟩, hmem, hvu⟩ := (hR _).mp (hsum_id ▸ hcrs)
              obtain ⟨u', hu', heq⟩ := List.mem_map.mp hmem
              cases heq
              simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu'
              rcases hu' with (hl | rfl) | hr
              · exact absurd hvu (by simpa using List.find?_eq_none.mp hl_none u hl)
              · exact absurd hvu hgv
              · exact ⟨u, hr, hvu⟩
            have hr_ne : r ≠ .leaf := fun h0 => by
              obtain ⟨u, hu, _⟩ := hready; simp [h0, AuxTree.toList] at hu
            have hcap_r : ∀ u ∈ r.toList, u ≤ cap := fun u hu => hcap u (by simp [AuxTree.toList, hu])
            have hrs_r : rs (st.nodes r.rootId).sum = true := by
              cases r with
              | leaf => exact absurd rfl hr_ne
              | node rid rL rR =>
                have hsr := hsub_r.2.2.2.2.2.2.1
                rw [tourEvalPairs_eq_map (fun u hu => h.noRev u (hcap_r u hu))] at hsr
                rw [AuxTree.rootId, hsr, hR]
                obtain ⟨u, hu, hvu⟩ := hready
                exact ⟨(u, (st.nodes u).val), List.mem_map.mpr ⟨u, hu, rfl⟩, hvu⟩
            have hrec := ih r hr_ne hr_nd hsub_r hcap_r
              hrs_r (by simp [AuxTree.countNodes] at hk; omega)
            set y := (descend tourPayload rs rv st k r.rootId).2
            have hy_r : y ∈ r.toList := hrec.2.1
            have hy_ne : y ≠ id := fun heq => hid_nr (heq ▸ hy_r)
            have hy_nl : y ∉ l.toList := fun hm => hdisj y hm hy_r
            refine ⟨hrec.1, by simp [AuxTree.toList, hy_r], ?_, ?_⟩
            · simp only [AuxTree.toList, List.append_assoc, List.find?_append, hl_none,
                List.find?_cons, hgv]
              simpa using hrec.2.2.1
            · simp only [AuxTree.depthOf, hy_ne, hy_nl, ↓reduceIte, hy_r]; omega
  exact hsub t (h.nonEmpty t ht) (h.treesInv t ht).nodup (h.treesInv t ht).sub
    (fun u hu => (h.mem_inCap ht hu).2) hrs hfuel


end MinCostFlow.SparseCore.Program
