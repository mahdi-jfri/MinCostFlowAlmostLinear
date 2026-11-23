module

public import MinCostFlow.SparseCore.Program.TourRep
import Mathlib.Tactic

/-!
# Shared `TourRepAt` helpers and Euler-tour query bridge lemmas

Provides reusable representation lemmas over `TourRepAt` and pure-list Euler-tour lemmas shared by
the query (`TourOpsQuery`), forest-update (`TourOpsForest`), edit (`TourOpsEdits`), and
initialization (`TourInit`) modules:
- `tourLog_double_le`, `endKey_endOfKey'`, `endOfKey_endKey'`,
- `TourValid.root_spec`, `TourValid.root_eq_of_mem`,
- `fullTour_filter_marked_eq_tourMarkedList`, `find?_rotate_tail_append_eq_cycNext_filter`,
  `tourAdjacent_iff_nextOpen_eq`,
- `TourRepAt.fixed_le_heap`, `TourRepAt.heapOk`, `TourRepAt.mem_compTree_of_active`,
  `TourRepAt.rootTag_foldr_eq_succ`, `TourRepAt.replace_compTree_same_list`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Pure arithmetic, end-key, and Euler-tour query lemmas -/

theorem tourLog_double_le (eCap : ℕ) :
    Nat.log 2 (2 * eCap + 2) + 1 ≤ 2 * tourLog eCap := by
  unfold tourLog
  have h1 : 2 * eCap + 2 ≤ 2 * (eCap + 2) := by omega
  have h2 : Nat.log 2 (2 * eCap + 2) ≤ Nat.log 2 (2 * (eCap + 2)) := Nat.log_mono_right h1
  have h3 : Nat.log 2 (2 * (eCap + 2)) = Nat.log 2 (eCap + 2) + 1 := by
    rw [Nat.log_eq_iff (by omega)]; constructor
    · rw [pow_succ']; exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
    · rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_succ_log_self (by omega) _) (by omega)
  omega

theorem tourLog_of_le {n eCap : ℕ} (hn : n ≤ 2 * eCap) :
    Nat.log 2 (n + 2) + 1 ≤ 2 * tourLog eCap :=
  le_trans (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) (tourLog_double_le eCap)

theorem endKey_endOfKey' (k : ℕ) : endKey (endOfKey k) = k := by
  simp only [endKey, endOfKey]
  by_cases h : k % 2 = 0 <;> simp [h] <;> omega

theorem endOfKey_endKey' (e : End) : endOfKey (endKey e) = e := by
  obtain ⟨id, dir⟩ := e
  cases dir
  · simp [endKey, endOfKey]; omega
  · simp [endKey, endOfKey]

theorem TourValid.root_spec {vCap eCap v : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hvF : v ∈ s.rf.F.V) :
    s.rf.root v ∈ s.rf.R ∧ s.rf.F.Connected v (s.rf.root v) := by
  unfold RootedForest.root
  obtain ⟨r, hr, _⟩ := hv.unique_root v hvF
  have hex : ∃ r, r ∈ s.rf.R ∧ s.rf.F.Connected v r := ⟨r, hr⟩
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

theorem TourValid.root_eq_of_mem {vCap eCap v r : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hvF : v ∈ s.rf.F.V) (hr : r ∈ s.rf.R)
    (hc : s.rf.F.Connected v r) : s.rf.root v = r := by
  obtain ⟨_, _, huniq⟩ := hv.unique_root v hvF
  have hs := hv.root_spec hvF
  exact (huniq _ hs).trans (huniq r ⟨hr, hc⟩).symm

theorem fullTour_filter_marked_eq_tourMarkedList {vCap eCap r : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hr : r ∈ s.rf.R) :
    open Classical in
    (fullTour s.ord s.rf.F hv.compat.forest r).filter (fun z => decide (z ∈ s.marked)) =
      tourMarkedList s r := by
  classical
  unfold tourMarkedList
  rw [← fullTour_filter_open s.ord hv.compat.forest hr, List.filter_filter]
  refine List.filter_congr fun z _ => ?_
  by_cases hm : z ∈ s.marked
  · have hopen := (hv.marked_open z hm).2
    simp [hm, hopen]
  · simp [hm]

theorem find?_rotate_tail_append_eq_cycNext_filter {L : List End} {e : End} {p : End → Bool}
    (hnd : L.Nodup) (he : e ∈ L) (hpe : p e = true) :
    ((rotateToList e L).tail ++ [e]).find? p = some (cycNext (L.filter p) e) := by
  obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp he
  have he_nP : e ∉ P := fun hm => (List.nodup_append.mp hnd).2.2 e hm e (by simp) rfl
  have hidx : (P ++ e :: Q).idxOf e = P.length := by
    clear he hnd hpe
    induction P with
    | nil => simp
    | cons a as ih =>
      have hae : a ≠ e := fun h => he_nP (by simp [h])
      simp [hae, ih fun hm => he_nP (by simp [hm])]
  have hrot_eq : rotateToList e (P ++ e :: Q) = e :: (Q ++ P) := by
    unfold rotateToList
    have he' : e ∈ P ++ e :: Q := by simp
    simp [he', hidx]
  have hfil_rot : ((P ++ e :: Q).filter p).IsRotated ((e :: (Q ++ P)).filter p) := by
    have h1 : (P ++ e :: Q).filter p = P.filter p ++ (e :: Q).filter p := List.filter_append P (e :: Q)
    have h2 : (e :: (Q ++ P)).filter p = (e :: Q).filter p ++ P.filter p := by
      simp [List.filter_append, hpe]
    rw [h1, h2]
    exact List.isRotated_append
  have hnd_f : ((P ++ e :: Q).filter p).Nodup := hnd.filter p
  have he_f : e ∈ (P ++ e :: Q).filter p := List.mem_filter.mpr ⟨by simp, hpe⟩
  rw [← cycNext_isRotated hnd_f hfil_rot he_f, hrot_eq]
  simp only [List.tail_cons, List.filter_cons, hpe, ↓reduceIte]
  cases hqp : (Q ++ P).filter p with
  | nil =>
    have hnone : (Q ++ P).find? p = none := by
      rw [List.find?_eq_none]
      intro z hz hzp
      have := List.filter_eq_nil_iff.mp hqp z hz
      exact this hzp
    rw [List.find?_append, hnone]
    simp [cycNext, hpe]
  | cons y ys =>
    have hnd_e : (e :: y :: ys).Nodup := by
      have hnd' := hfil_rot.perm.nodup_iff.mp hnd_f
      simpa [List.filter_cons, hpe, hqp] using hnd'
    have hcyc : cycNext (e :: y :: ys) e = y := by
      have := cycNext_eq_getElem hnd_e (i := 0) (by simp)
      simpa using this
    have hsome : (Q ++ P).find? p = some y := by
      generalize hL : Q ++ P = L at hqp ⊢
      clear * - hqp
      induction L with
      | nil => simp at hqp
      | cons a as ih =>
        rw [List.filter_cons] at hqp
        cases ha : p a <;> simp only [ha, ↓reduceIte] at hqp
        · rw [List.find?_cons_of_neg (by simp [ha])]; exact ih hqp
        · rw [List.find?_cons_of_pos ha]; exact congrArg some (List.cons.inj hqp).1
    rw [List.find?_append, hsome, hcyc]; rfl

theorem tourAdjacent_iff_nextOpen_eq {vCap eCap : ℕ} {s : TourAbs} {x y : End}
    (hv : TourValid vCap eCap s)
    (hx : ∃ u, x ∈ s.ord u) (hxo : x.1 ∉ s.rf.F.E)
    (hy : ∃ v, y ∈ s.ord v) :
    tourAdjacent s x y ↔ tourNextOpen s x = y := by
  constructor
  · exact fun h => h.2
  · intro heq
    refine ⟨?_, heq⟩
    obtain ⟨u, hxu⟩ := hx
    obtain ⟨v, hyv⟩ := hy
    have huF : u ∈ s.rf.F.V := hv.compat.vert u (List.ne_nil_of_mem hxu)
    have hvF : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hyv)
    have hr := hv.root_spec huF
    have hrx : s.rf.root (ordSrc s.ord x) = s.rf.root u := by rw [hv.compat.ordSrc_eq hxu]
    have hry : s.rf.root (ordSrc s.ord y) = s.rf.root v := by rw [hv.compat.ordSrc_eq hyv]
    have hx_ct : x ∈ coreTour s.ord s.rf (s.rf.root u) := by
      rw [← fullTour_filter_open s.ord hv.compat.forest hr.1, List.mem_filter]
      exact ⟨((fullTour_spec hv.compat (s.rf.root u)).2 x).mpr ⟨u, hxu, connected_symm hr.2⟩,
        decide_eq_true hxo⟩
    have hy_ct : y ∈ coreTour s.ord s.rf (s.rf.root u) := by
      rw [← heq, tourNextOpen, hrx]
      unfold cycNext
      have hlen : 0 < (coreTour s.ord s.rf (s.rf.root u)).length := List.length_pos_of_mem hx_ct
      rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hlen)]
      exact List.getElem_mem _
    rw [← fullTour_filter_open s.ord hv.compat.forest hr.1, List.mem_filter] at hy_ct
    obtain ⟨w, hyw, hcw⟩ := ((fullTour_spec hv.compat (s.rf.root u)).2 y).mp hy_ct.1
    have hvw : v = w := hv.compat.unique v w y hyv hyw
    subst hvw
    rw [hrx, hry]
    exact (hv.root_eq_of_mem hvF hr.1 (connected_symm hcw)).symm

/-! ## Shared `TourRepAt` structural helpers -/

theorem TourRepAt.fixed_le_heap {R_ord : DSRep (ℕ → List End)} {vCap eCap b heap : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (_h : TourRepAt R_ord vCap eCap b s x mem)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap) :
    ordHandleOf b vCap eCap ≤ heap := by
  have hpos : b < ordHandleOf b vCap eCap := by simp [ordHandleOf, tourFixedSize]
  have := hfoot (ordHandleOf b vCap eCap - 1) (Or.inl ⟨by omega, by omega⟩)
  omega

theorem TourRepAt.heapOk {R_ord : DSRep (ℕ → List End)} {w vCap eCap b heap sp : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + sp < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap sp mem where
  rec_le := by
    have hle := h.fixed_le_heap hfoot
    have hnn := h.numNodes_le
    rw [← nodesBase_end_eq b vCap eCap] at hle
    simp only [nodeAddr, tourLayout_stride]; omega
  room := hroom
  zero := hzero
  wide := hwide

theorem TourRepAt.mem_compTree_of_active {R_ord : DSRep (ℕ → List End)} {vCap eCap b v : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem) {e : End} (he : e ∈ s.ord v) :
    let r := s.rf.root v
    let u := x.nodeOf (endKey e)
    v < vCap ∧ r ∈ s.rf.R ∧ r < vCap ∧ endKey e < 2 * eCap ∧
    1 ≤ u ∧ u ≤ x.numNodes ∧ x.keyOf u = endKey e ∧
    ∃ t rest, x.compTree r = some t ∧ x.trees.Perm (t :: rest) ∧
      t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest r ∧
      u ∈ t.toList := by
  have hv_lt : v < vCap := by
    by_contra hge
    have hnil := h.valid.ordWithin.2.1 v (Nat.le_of_not_lt hge)
    rw [hnil] at he; simp at he
  have hvF : v ∈ s.rf.F.V := h.valid.compat.vert v (List.ne_nil_of_mem he)
  have hr_spec := h.valid.root_spec hvF
  have hr_lt : s.rf.root v < vCap := h.valid.verts_lt _ (h.valid.roots_sub hr_spec.1)
  have he_lt : endKey e < 2 * eCap := by
    have := h.valid.ordWithin.2.2 v e he; simp only [endKey]; cases e.2 <;> simp <;> omega
  have hact := h.active_end v hv_lt e he
  have hu_le : x.nodeOf (endKey e) ≤ x.numNodes := (h.nodeOf_mem (endKey e) he_lt).2
  have hu_key : x.keyOf (x.nodeOf (endKey e)) = endKey e := h.nodeOf_keyOf (endKey e) he_lt hact.1
  have he_ft : e ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) :=
    ((fullTour_spec h.valid.compat (s.rf.root v)).2 e).mpr ⟨v, he, connected_symm hr_spec.2⟩
  have hft_ne : fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) ≠ [] := List.ne_nil_of_mem he_ft
  obtain ⟨t, ht_eq, ht_mem, ht_map⟩ := h.comp_some (s.rf.root v) hr_spec.1 hft_ne
  have hperm : x.trees.Perm (t :: x.trees.erase t) := List.perm_cons_erase ht_mem
  have hu_mem : x.nodeOf (endKey e) ∈ t.toList := by
    rw [← ht_map] at he_ft
    obtain ⟨u', hu', hu'e⟩ := List.mem_map.mp he_ft
    have hu'_in : 1 ≤ u' ∧ u' ≤ x.numNodes :=
      (h.nodes_exact u').mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu'⟩)
    have hkeq : x.keyOf u' = endKey e := by rw [← hu'e, endKey_endOfKey']
    have hu'eq : u' = x.nodeOf (endKey e) := by rw [← hkeq, (h.keyOf_mem u' hu'_in.1 hu'_in.2).2.2]
    exact hu'eq ▸ hu'
  exact ⟨hv_lt, hr_spec.1, hr_lt, he_lt, by omega, hu_le, hu_key, t, x.trees.erase t, ht_eq,
    hperm, ht_map, hu_mem⟩

theorem TourRepAt.rootTag_foldr_eq_succ {R_ord : DSRep (ℕ → List End)} {vCap eCap b r : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem) (hr : r ∈ s.rf.R)
    {t : AuxTree} (ht_mem : t ∈ x.trees)
    (ht_map : t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest r)
    (ht_ne : t.toList ≠ []) :
    (t.toList.map fun u => (x.st.nodes u).val.rootTag).foldr max 0 = r + 1 := by
  have hft_ne : fullTour s.ord s.rf.F h.valid.compat.forest r ≠ [] := by
    rw [← ht_map]; exact mt List.map_eq_nil_iff.mp ht_ne
  have hord_ne : s.ord r ≠ [] := mt (fullTour_eq_nil_iff h.valid.compat r).mpr hft_ne
  obtain ⟨a, ha⟩ : ∃ a, (s.ord r).head? = some a := Option.isSome_iff_exists.mp (by cases ho : s.ord r <;> simp_all)
  have ha_ft : a ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
    List.mem_of_head? (fullTour_head? h.valid.compat r ha)
  rw [← ht_map] at ha_ft
  obtain ⟨ua, hua_mem, hua_eq⟩ := List.mem_map.mp ha_ft
  have hval_u : ∀ u ∈ t.toList, (x.st.nodes u).val.rootTag = tourRootTagVal s (endOfKey (x.keyOf u)) := by
    intro u hu
    have hu_in : 1 ≤ u ∧ u ≤ x.numNodes := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu⟩)
    have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨v, hv_mem, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
    rw [h.val_active u hu_in.1 hu_in.2 ⟨v, hv_mem⟩]
  have hle : ∀ u ∈ t.toList, (x.st.nodes u).val.rootTag ≤ r + 1 := by
    intro u hu
    rw [hval_u u hu]
    by_cases hrt : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf u))
    · obtain ⟨r', hr'R, hr'h⟩ := hrt
      have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
        rw [← ht_map]; exact List.mem_map_of_mem hu
      obtain ⟨v, hv_mem, hcv⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
      have hvr' : v = r' := h.valid.compat.unique v r' _ hv_mem (List.mem_of_head? hr'h)
      rw [hvr'] at hcv
      have hrr' : r' = r := by
        have h1 := h.valid.root_eq_of_mem (h.valid.roots_sub hr'R) hr'R (connected_refl _ r')
        have h2 := h.valid.root_eq_of_mem (h.valid.roots_sub hr'R) hr (connected_symm hcv)
        exact h1.symm.trans h2
      rw [hrr'] at hr'h
      rw [tourRootTagVal_eq_succ h.valid hr hr'h]
    · push Not at hrt
      rw [tourRootTagVal_eq_zero hrt]; omega
  have hua_rt : (x.st.nodes ua).val.rootTag = r + 1 := by
    rw [hval_u ua hua_mem, hua_eq, tourRootTagVal_eq_succ h.valid hr ha]
  have hfold_le : ∀ (ls : List ℕ), (∀ z ∈ ls, z ≤ r + 1) → ls.foldr max 0 ≤ r + 1 := by
    intro ls; induction ls with
    | nil => intro _; simp
    | cons z zs ih =>
      intro hzs; simp only [List.foldr_cons]
      exact max_le (hzs z (by simp)) (ih fun w hw => hzs w (by simp [hw]))
  have hfold_ge : ∀ (ls : List ℕ), r + 1 ∈ ls → r + 1 ≤ ls.foldr max 0 := by
    intro ls; induction ls with
    | nil => intro h; simp at h
    | cons z zs ih =>
      intro hm; simp only [List.foldr_cons, List.mem_cons] at hm ⊢
      rcases hm with rfl | hzs
      · exact le_max_left _ _
      · exact le_trans (ih hzs) (le_max_right _ _)
  exact le_antisymm
    (hfold_le _ fun z hz => by rcases List.mem_map.mp hz with ⟨u, hu, rfl⟩; exact hle u hu)
    (hfold_ge _ (List.mem_map.mpr ⟨ua, hua_mem, hua_rt⟩))

/-- Update `TourRepAt` after a read-only splay operation replaces `t` (for root `r ∈ s.rf.R`) by
`t'` with `t'.toList = t.toList`, keeping all node values and all memory outside `InRecords`
(below `heap`). -/
theorem TourRepAt.replace_compTree_same_list {R_ord : DSRep (ℕ → List End)}
    {vCap eCap b r heap : ℕ} {s : TourAbs} {x : TourConcrete R_ord.τ} {mem mem' : ℕ → ℕ}
    {t t' : AuxTree} {rest : List AuxTree} {s' : SplayState TourVal TourSum Unit}
    (hLoc : R_ord.Local) (h : TourRepAt R_ord vCap eCap b s x mem)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hr : r ∈ s.rf.R) (hperm : x.trees.Perm (t :: rest))
    (hcomp_r : x.compTree r = some t) (hlist : t'.toList = t.toList)
    (hnodes' : tourLayout.NodesAt mem' (nodesBase b vCap eCap) x.numNodes s')
    (hinv' : TourForestInv x.numNodes s' (t' :: rest))
    (hvals' : ∀ u ≤ x.numNodes, (s'.nodes u).val = (x.st.nodes u).val)
    (hagree : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → mem' a = mem a) :
    let x' : TourConcrete R_ord.τ :=
      { x with st := s', trees := t' :: rest, compTree := Function.update x.compTree r (some t') }
    TourRepAt R_ord vCap eCap b s x' mem' ∧
    R_ord.phi (ordHandleOf b vCap eCap) x'.ordX mem' = R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem ∧
    forestPhi x.trees = forestPhi (t :: rest) ∧
    (∀ a, tourFoot R_ord vCap eCap b x' a ↔ tourFoot R_ord vCap eCap b x a) := by
  intro x'
  have hord_lt : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hpre_eq : ∀ a < nodesBase b vCap eCap, mem' a = mem a := fun a ha =>
    hagree a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_lt ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha)
  have hord_eq : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → mem a = mem' a := fun a ha =>
    (hagree a (hfoot a (Or.inr ha)) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (h.ordFootGe a ha))).symm
  have hOrd := hLoc (ordHandleOf b vCap eCap) s.ord x.ordX mem mem' hord_eq
  have hhdr' : TourHeaderAt vCap eCap b x.numNodes mem' := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, mem' (b + k) = mem (b + k) := fun k hk =>
      hpre_eq (b + k) (by simp [nodesBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  have ht_mem : t ∈ x.trees := hperm.mem_iff.mpr (by simp)
  have ht_ne : t ≠ .leaf := h.forestInv.nonEmpty t ht_mem
  have ht_pos : t.toList ≠ [] := by cases t <;> simp [AuxTree.toList] at ht_ne ⊢
  have hft_r_ne : fullTour s.ord s.rf.F h.valid.compat.forest r ≠ [] := by
    intro hnil; have := h.comp_none r hr hnil; rw [hcomp_r] at this; simp at this
  obtain ⟨t_r, hct_r, _, ht_r_map⟩ := h.comp_some r hr hft_r_ne
  have ht_req : t = t_r := Option.some.inj (hcomp_r.symm.trans hct_r)
  rcases ht_req with rfl
  have ht_not_rest : t ∉ rest := by
    intro hm
    have hnd := (h.forestInv.perm hperm).1.nodupAll
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ ht_pos
    exact hnd.2.2 u hu u (List.mem_flatMap.mpr ⟨t, hm, hu⟩) rfl
  have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ r → x.compTree r' ≠ some t := by
    intro r' hr' hne hcr'
    have hft' : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := by
      intro hnil; have := h.comp_none r' hr' hnil; rw [hcr'] at this; simp at this
    obtain ⟨t', hct', _, ht'_map⟩ := h.comp_some r' hr' hft'
    have ht'eq : t' = t := Option.some.inj (hct'.symm.trans hcr')
    subst ht'eq
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ ht_pos
    have he1 : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_r_map]; exact List.mem_map_of_mem hu
    have he2 : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
      rw [← ht'_map]; exact List.mem_map_of_mem hu
    obtain ⟨v1, hv1, hc1⟩ := ((fullTour_spec h.valid.compat r).2 _).mp he1
    obtain ⟨v2, hv2, hc2⟩ := ((fullTour_spec h.valid.compat r').2 _).mp he2
    have hv12 : v1 = v2 := h.valid.compat.unique v1 v2 _ hv1 hv2
    subst hv12
    have hvF := h.valid.compat.vert v1 (List.ne_nil_of_mem hv1)
    have h1 := h.valid.root_eq_of_mem hvF hr (connected_symm hc1)
    have h2 := h.valid.root_eq_of_mem hvF hr' (connected_symm hc2)
    exact hne (h2.symm.trans h1)
  have hrep' : TourRepAt R_ord vCap eCap b s x' mem' :=
    { valid := h.valid
      ordRep := hOrd.1 h.ordRep
      ordFootGe := h.ordFootGe
      header := hhdr'
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hpre_eq _ (by simp [nodeOfEndBase, nodesBase]; omega)]; exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun u h1 h2 => by
        dsimp only [x'] at h2; have hle := h.numNodes_le
        rw [hpre_eq _ (by simp [keyOfNodeBase, nodesBase]; omega)]; exact h.keyOf_mem u h1 h2
      firstEnd_mem := fun v hv => by
        rw [hpre_eq _ (by simp [firstEndBase, nodesBase]; omega)]; exact h.firstEnd_mem v hv
      isRoot_mem := fun v hv => by
        rw [hpre_eq _ (by simp [isRootBase, nodesBase]; omega)]; exact h.isRoot_mem v hv
      slot_bij := h.slot_bij
      slotOf_mem := fun v hv => by
        rw [hpre_eq _ (by simp [slotOfVertBase, nodesBase]; omega)]; exact h.slotOf_mem v hv
      vertOf_mem := fun sl hsl => by
        rw [hpre_eq _ (by simp [vertOfSlotBase, nodesBase]; omega)]; exact h.vertOf_mem sl hsl
      active_end := fun v hv e he => by
        have he_lt : endKey e < 2 * eCap := by
          have := h.valid.ordWithin.2.2 v e he; simp only [endKey]; cases e.2 <;> simp <;> omega
        rw [hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega)]; exact h.active_end v hv e he
      inactive_owner := fun k hk hno => by
        rw [hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega)]; exact h.inactive_owner k hk hno
      markArr_zero := fun k hk => by
        rw [hpre_eq _ (by simp [markArrBase, nodesBase]; omega)]; exact h.markArr_zero k hk
      nodesAt := hnodes'
      forestInv := hinv'
      nodes_exact := fun u => by
        have h1 : u ∈ (t' :: rest).flatMap AuxTree.toList ↔ u ∈ (t :: rest).flatMap AuxTree.toList := by
          simp [List.flatMap_cons, hlist]
        have h2 : u ∈ (t :: rest).flatMap AuxTree.toList ↔ u ∈ x.trees.flatMap AuxTree.toList := by
          simp only [List.mem_flatMap]
          exact ⟨fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mpr ha, hu⟩,
            fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mp ha, hu⟩⟩
        exact h1.trans (h2.trans (h.nodes_exact u))
      comp_none := fun r' hr' hnil => by
        have hne : r' ≠ r := fun heq => hft_r_ne (heq ▸ hnil)
        simp only [x', Function.update_of_ne hne]
        exact h.comp_none r' hr' hnil
      comp_some := fun r' hr' hne_ft => by
        by_cases hrr' : r' = r
        · subst hrr'
          exact ⟨t', by simp [x'], by simp [x'], by rw [hlist]; exact ht_r_map⟩
        · obtain ⟨tr', hctr', htr'_mem, htr'_map⟩ := h.comp_some r' hr' hne_ft
          have htr'_ne : tr' ≠ t := fun heq => hcomp_inj r' hr' hrr' (heq ▸ hctr')
          have htr'_rest : tr' ∈ rest := by
            have := hperm.mem_iff.mp htr'_mem
            simp only [List.mem_cons] at this
            exact this.resolve_left htr'_ne
          exact ⟨tr', by simp [x', Function.update_of_ne hrr', hctr'], by simp [x', htr'_rest], htr'_map⟩
      tree_class := fun tr htr => by
        simp only [x', List.mem_cons] at htr
        rcases htr with rfl | hrest
        · exact Or.inl ⟨r, hr, by simp [x']⟩
        · have htr_mem : tr ∈ x.trees := hperm.mem_iff.mpr (by simp [hrest])
          rcases h.tree_class tr htr_mem with ⟨r', hr', hcr'⟩ | hsing
          · have hne : r' ≠ r := fun heq => by
              subst heq; have : tr = t := Option.some.inj (hcr'.symm.trans hcomp_r)
              exact ht_not_rest (this ▸ hrest)
            exact Or.inl ⟨r', hr', by simp [x', Function.update_of_ne hne, hcr']⟩
          · exact Or.inr hsing
      inactive_single := fun u h1 h2 hno => by
        have hmem := h.inactive_single u h1 h2 hno
        have hne : AuxTree.node u .leaf .leaf ≠ t := by
          intro heq
          have he : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
            rw [← ht_r_map, ← heq]; simp [AuxTree.toList]
          obtain ⟨v, hv, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp he
          exact hno v hv
        have hrest : AuxTree.node u .leaf .leaf ∈ rest :=
          (List.mem_cons.mp (hperm.mem_iff.mp hmem)).resolve_left hne
        simp [x', hrest]
      val_active := fun u h1 h2 hact => by
        dsimp only [x'] at h2 ⊢
        rw [hvals' u (by have := h.numNodes_le; omega)]; exact h.val_active u h1 h2 hact
      val_inactive_rt := fun u h1 h2 hno => by
        dsimp only [x'] at h2 ⊢
        rw [hvals' u (by have := h.numNodes_le; omega)]; exact h.val_inactive_rt u h1 h2 hno
      val_unused_rt := fun u hu hcond => by
        rw [hvals' u hu]; exact h.val_unused_rt u hu hcond }
  exact ⟨hrep', hOrd.2.symm, forestPhi_perm hperm, fun _ => Iff.rfl⟩

/-! ## Compact WordRAM load/store helpers and `rotateNatList` membership -/

theorem mem_of_mem_rotateNatList {x z : ℕ} {L : List ℕ}
    (hx : x ∈ L) (hz : z ∈ rotateNatList x L) : z ∈ L := by
  unfold rotateNatList at hz
  simp only [hx, ↓reduceIte] at hz
  rcases List.mem_append.mp hz with h1 | h2
  · exact List.mem_of_mem_drop h1
  · exact List.mem_of_mem_take h2

theorem runs_load_const_off {w dst rBase off b val : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : st.regs rBase = b) (hoff : off < 2 ^ w) (hsum : b + off < 2 ^ w)
    (hmem : st.mem (b + off) = val) :
    Runs w p ω (.assign dst (.load (.bin .add (.reg rBase) (.const off)))) st .normal
      { st with regs := Function.update st.regs dst val } 5 :=
  runs_assign_iff.mpr ⟨val, by
    simp only [Expr.eval, hr, hoff, ↓reduceIte, BinOp.eval, hsum, Option.map_some, hmem],
    rfl, rfl, rfl⟩

theorem runs_load_reg_off {w dst rBase rIdx base idx val : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h1 : st.regs rBase = base) (h2 : st.regs rIdx = idx) (hsum : base + idx < 2 ^ w)
    (hmem : st.mem (base + idx) = val) :
    Runs w p ω (.assign dst (.load (.bin .add (.reg rBase) (.reg rIdx)))) st .normal
      { st with regs := Function.update st.regs dst val } 5 :=
  runs_assign_iff.mpr ⟨val, by
    simp only [Expr.eval, h1, h2, BinOp.eval, hsum, ↓reduceIte, Option.map_some, hmem],
    rfl, rfl, rfl⟩

theorem runs_ret_reg_add1 {w r v : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : st.regs r = v) (h1 : 1 < 2 ^ w) (hv1 : v + 1 < 2 ^ w) :
    Runs w p ω (.ret (.bin .add (.reg r) (.const 1))) st (.returned (v + 1)) st 4 :=
  runs_ret_iff.mpr ⟨v + 1, by
    simp only [Expr.eval, hr, h1, ↓reduceIte, BinOp.eval, hv1], rfl, rfl, rfl⟩

end MinCostFlow.SparseCore.Program
