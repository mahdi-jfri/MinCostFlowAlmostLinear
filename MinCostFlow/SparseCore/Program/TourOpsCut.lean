module

public import MinCostFlow.SparseCore.Program.TourCutLinkExec
import Mathlib.Tactic

/-!
# Forest cut operation (`cut`, Op 1)

Verifies Op `1` (`cut [b, e, newRoot, heap]`) of `tourContract`: cuts forest edge
`e`, inserts `newRoot` into `rf.R`, splits the Euler-tour splay tree via `tourCutSplitBody`,
updates `isOpen`/`isRoot`/`rootTag`, and rotates both component tours to their roots' first ends
in `O(tourLog eCap)` amortized time with `2` words of heap headroom.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Op 1 (`cut`) verification -/

/-- Op 1 (`cut [b, e, newRoot, heap]`): verified amortized run theorem. -/
theorem tourOp_cut_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b e newRoot heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) {csProc : ℕ}
    (hcs : p.procs[csProc]? = some (tourCutSplitBody C.splay.splay C.detachLeft C.detachRight C.join C.rotateFront))
    (ω : ℕ → Bool) {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (he : e ∈ s.rf.F.E) (hnewLt : newRoot < vCap) (hnewV : newRoot ∈ s.rf.F.V)
    (hnewNotR : newRoot ∉ s.rf.R)
    (huniq' : ∀ v ∈ s.rf.F.V, ∃! r, r ∈ insert newRoot s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 2 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpCutBody csProc C.rootTagOf C.setValNode C.rotateFront)
        (startState [b, e, newRoot, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b (tourCut s e newRoot) x' st'.mem ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_CUTLINK_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le := h.fixed_le_heap hfoot
  have hhdr := h.header
  set u := s.rf.F.tail e
  set v := s.rf.F.head e
  set F' := eraseForestEdge s.rf.F e
  set oldRoot := s.rf.root u
  have ⟨hx_ord, hy_ord⟩ := h.valid.compat.forestEnd e he
  obtain ⟨hrv_eq, holdR, hne_on, hconn_on, hpair_conn⟩ := cut_component_partition h.valid he hnewV hnewNotR huniq'
  have holdLt : oldRoot < vCap := h.valid.verts_lt oldRoot (h.valid.roots_sub holdR)
  have he_lt : e < eCap := h.valid.ordWithin.2.2 u (e, true) hx_ord
  obtain ⟨_, _, _, _, hnx_pos, hnx_le, hnx_key, t, rest, hct, hperm, ht_map, hnx_t⟩ :=
    h.mem_compTree_of_active hx_ord
  obtain ⟨_, _, _, _, hny_pos, hny_le, hny_key, ty, _, hcty, _, _, hny_t⟩ :=
    h.mem_compTree_of_active hy_ord
  rw [hrv_eq] at hcty
  have hty_eq : ty = t := Option.some.inj (hcty.symm.trans hct)
  rw [hty_eq] at hny_t
  have hkx_eq : endKey (e, true) = 2 * e := rfl
  have hky_eq : endKey (e, false) = 2 * e + 1 := rfl
  rw [hkx_eq] at hnx_pos hnx_le hnx_key hnx_t
  rw [hky_eq] at hny_pos hny_le hny_key hny_t
  set nx := x.nodeOf (2 * e)
  set ny := x.nodeOf (2 * e + 1)
  have hnx_ne_ny : nx ≠ ny := fun heq => by
    have := congrArg x.keyOf heq; rw [hnx_key, hny_key] at this; omega
  have hnx_cap : nx ≤ x.numNodes := hnx_le
  have hny_cap : ny ≤ x.numNodes := hny_le
  obtain ⟨eO, heOE, heOS⟩ := exists_edge_of_connected_ne hconn_on hne_on
  obtain ⟨eN, heNE, heNS⟩ := exists_edge_of_connected_ne (connected_symm hconn_on) hne_on.symm
  have hordOld_ne : s.ord oldRoot ≠ [] := List.ne_nil_of_mem (heOS ▸ h.valid.compat.mem_ord_of_forest heOE)
  have hordNew_ne : s.ord newRoot ≠ [] := List.ne_nil_of_mem (heNS ▸ h.valid.compat.mem_ord_of_forest heNE)
  obtain ⟨aO, haO⟩ : ∃ aO, (s.ord oldRoot).head? = some aO :=
    Option.isSome_iff_exists.mp (by cases ho : s.ord oldRoot <;> simp_all)
  obtain ⟨aN, haN⟩ : ∃ aN, (s.ord newRoot).head? = some aN :=
    Option.isSome_iff_exists.mp (by cases ho : s.ord newRoot <;> simp_all)
  have haO_mem : aO ∈ s.ord oldRoot := List.mem_of_head? haO
  have haN_mem : aN ∈ s.ord newRoot := List.mem_of_head? haN
  obtain ⟨_, _, _, _, hfeO_pos, hfeO_le, hfeO_key, _, _, _, _, _, _⟩ := h.mem_compTree_of_active haO_mem
  obtain ⟨_, _, _, _, hfeN_pos, hfeN_le, hfeN_key, _, _, _, _, _, _⟩ := h.mem_compTree_of_active haN_mem
  set feO := x.nodeOf (endKey aO)
  set feN := x.nodeOf (endKey aN)
  have hfeO_cap : feO ≤ x.numNodes := hfeO_le
  have hfeN_cap : feN ≤ x.numNodes := hfeN_le
  have hfeO_first : mem (firstEndBase b + oldRoot) = feO := by rw [h.firstEnd_mem oldRoot holdLt, haO]
  have hfeN_first : mem (firstEndBase b + newRoot) = feN := by rw [h.firstEnd_mem newRoot hnewLt, haN]
  -- Steps 1..4: rootTagOf(nx), setValNode(nx), setValNode(ny), cutSplit(nx, ny)
  have hheap0 := h.heapOk (sp := 2) hfoot hzero hroom hwide
  have hf_perm := (h.forestInv.perm hperm).1
  obtain ⟨t₁, s₁, o₁, st₁, c₁, hrun₁, hv₁, hn₁, hfr₁, hinv₁, hvals₁, _, _, hlist₁, hval₁, _, hcost₁⟩ :=
    tourRootTagOfBody_runs (fuel := 2 * eCap + 2) (pos := pos) C ω h.nodesAt hf_perm (h.valsOk hw)
      hnx_t (by have := h.numNodes_le; omega) (by omega) hheap0
  have ho₁_eq : o₁.value = oldRoot + 1 := by
    rw [hv₁]
    exact h.rootTag_foldr_eq_succ holdR (hperm.mem_iff.mpr (by simp)) ht_map (List.ne_nil_of_mem hnx_t)
  set rtX := (x.st.nodes nx).val.rootTag
  have hrtX_mem : st₁.mem (nodesBase b vCap eCap + 17 * nx + 11) = rtX := by
    rw [nodesAt_rootTag hn₁ hnx_cap, hval₁ nx hnx_cap]
  have hnx_t1 : nx ∈ t₁.toList := by rw [hlist₁]; exact hnx_t
  obtain ⟨t₂, s₂, o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, _, _, hlist₂, hvalX₂, hvalne₂, _, hcost₂⟩ :=
    tourSetValNodeBody_runs (isOpen := 1) (isMarked := 0) (rootTag := rtX)
      (fuel := 2 * eCap + 2) (pos := st₁.pos) C ω hn₁ hinv₁ hvals₁ hnx_t1 ((h.valsOk hw).2 nx hnx_cap)
      (by have := h.numNodes_le; omega) (by omega) ⟨hheap0.rec_le, hroom, hfr₁.1, hwide⟩
  set rtY := (x.st.nodes ny).val.rootTag
  have hrtY_mem : st₂.mem (nodesBase b vCap eCap + 17 * ny + 11) = rtY := by
    rw [nodesAt_rootTag hn₂ hny_cap, hvalne₂ ny hny_cap hnx_ne_ny.symm, hval₁ ny hny_cap]
  have hny_t2 : ny ∈ t₂.toList := by rw [hlist₂, hlist₁]; exact hny_t
  obtain ⟨t₃, s₃, o₃, st₃, c₃, hrun₃, hn₃, hfr₃, hinv₃, hvals₃, _, _, hlist₃, hvalY₃, hvalne₃, _, hcost₃⟩ :=
    tourSetValNodeBody_runs (isOpen := 1) (isMarked := 0) (rootTag := rtY)
      (fuel := 2 * eCap + 2) (pos := st₂.pos) C ω hn₂ hinv₂ hvals₂ hny_t2 ((h.valsOk hw).2 ny hny_cap)
      (by have := h.numNodes_le; omega) (by omega) ⟨hheap0.rec_le, hroom, hfr₂.1, hwide⟩
  have hnx_t3 : nx ∈ t₃.toList := by rw [hlist₃, hlist₂, hlist₁]; exact hnx_t
  have hny_t3 : ny ∈ t₃.toList := by rw [hlist₃]; exact hny_t2
  obtain ⟨tA, tB, A, Q, s₄, o₄, st₄, c₄, hrun₄, hn₄, hfr₄, hinv₄, hvals₄, _, _,
    hrot_split, htA_list, htB_list, hval₄, hcost₄⟩ :=
    tourCutSplitBody_runs (fuel := 2 * eCap + 2) (pos := st₃.pos) C.toTourSplayOpsProcs ω
      hn₃ hinv₃ hvals₃ hnx_t3 hny_t3 hnx_ne_ny (by have := h.numNodes_le; omega) (by omega) ⟨hheap0.rec_le, hroom, hfr₃.1, hwide⟩
  -- Relate `tA, tB` to the two post-cut fullTours via `fullTour_cut`
  have hvalid' : TourValid vCap eCap (tourCut s e newRoot) := tourValid_cut h.valid he hnewV huniq'
  have ht3_eq_t : t₃.toList = t.toList := hlist₃.trans (hlist₂.trans hlist₁)
  have hcut_rot : (([] ++ (e, true) :: A.map (fun id => endOfKey (x.keyOf id)) ++
      (e, false) :: Q.map (fun id => endOfKey (x.keyOf id))).IsRotated
      (fullTour s.ord s.rf.F h.valid.compat.forest oldRoot)) := by
    have h1 : (rotateNatList nx t.toList).map (fun id => endOfKey (x.keyOf id)) =
        (e, true) :: A.map (fun id => endOfKey (x.keyOf id)) ++ (e, false) :: Q.map (fun id => endOfKey (x.keyOf id)) := by
      rw [← ht3_eq_t, hrot_split]
      simp [List.map_append, hnx_key, hny_key, tour_endOfKey_two_mul, endOfKey_two_mul_add1]
    rw [List.nil_append, ← h1, ← ht_map]
    have hrot_nat : (rotateNatList nx t.toList).IsRotated t.toList := by
      unfold rotateNatList; simp only [hnx_t, ↓reduceIte]
      exact List.isRotated_append.symm.trans (by rw [List.take_append_drop])
    exact hrot_nat.map _
  have ⟨hrot_u, hrot_v⟩ := fullTour_cut h.valid.compat he (x := (e, true)) (y := (e, false))
    (Or.inl ⟨rfl, rfl⟩) hcut_rot
  have htA_rot_u : (tA.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated
      (fullTour s.ord F' hvalid'.compat.forest u) := by
    have : tA.toList.map (fun id => endOfKey (x.keyOf id)) = [] ++ (e, true) :: Q.map (fun id => endOfKey (x.keyOf id)) := by
      rw [htA_list]; simp [hnx_key, tour_endOfKey_two_mul]
    rw [this]; exact hrot_u
  have htB_rot_v : (tB.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated
      (fullTour s.ord F' hvalid'.compat.forest v) := by
    have : tB.toList.map (fun id => endOfKey (x.keyOf id)) = A.map (fun id => endOfKey (x.keyOf id)) ++ [(e, false)] := by
      rw [htB_list]; simp [hny_key, endOfKey_two_mul_add1]
    rw [this]; exact hrot_v
  have horient : ∃ tOld tNew : AuxTree,
      (tA :: tB :: rest).Perm (tNew :: tOld :: rest) ∧
      (tOld.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated (fullTour s.ord F' hvalid'.compat.forest oldRoot) ∧
      (tNew.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated (fullTour s.ord F' hvalid'.compat.forest newRoot) ∧
      feO ∈ tOld.toList ∧ feN ∈ tNew.toList := by
    have hmem_of_rot : ∀ (tr : AuxTree) (r0 : ℕ) (a0 : End) (ha0 : a0 ∈ s.ord r0),
        tr ∈ [tA, tB] →
        (tr.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated (fullTour s.ord F' hvalid'.compat.forest r0) →
        x.nodeOf (endKey a0) ∈ tr.toList := by
      intro tr r0 a0 ha0 htr_ab hrot
      have ha_ft : a0 ∈ fullTour s.ord F' hvalid'.compat.forest r0 :=
        ((fullTour_spec hvalid'.compat r0).2 a0).mpr ⟨r0, ha0, connected_refl F' r0⟩
      obtain ⟨id, hid_tr, hid_eq⟩ := List.mem_map.mp (hrot.perm.mem_iff.mpr ha_ft)
      have hid_t : id ∈ t.toList := by
        have hmem_rot : id ∈ rotateNatList nx t.toList := by
          rw [← ht3_eq_t, hrot_split]
          simp only [List.cons_append, List.mem_cons, List.mem_append]
          rcases List.mem_cons.mp htr_ab with rfl | htr_b
          · rw [htA_list] at hid_tr
            rcases List.mem_cons.mp hid_tr with rfl | hq
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inr hq))
          · have htr_b' : tr = tB := by simpa using htr_b
            subst htr_b'; rw [htB_list] at hid_tr
            rcases List.mem_append.mp hid_tr with ha | hy
            · exact Or.inr (Or.inl ha)
            · simp only [List.mem_singleton] at hy; subst hy; exact Or.inr (Or.inr (Or.inl rfl))
        exact mem_of_mem_rotateNatList hnx_t hmem_rot
      have hid_in := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t, hperm.mem_iff.mpr (by simp), hid_t⟩)
      have hkeq : x.keyOf id = endKey a0 := by rw [← hid_eq, endKey_endOfKey']
      have hideq : id = x.nodeOf (endKey a0) := by rw [← hkeq, (h.keyOf_mem id hid_in.1 hid_in.2).2.2]
      exact hideq ▸ hid_tr
    rcases hpair_conn with ⟨huO, hvN⟩ | ⟨huN, hvO⟩
    · have hrO := htA_rot_u.trans (fullTour_isRotated_of_connected hvalid'.compat huO)
      have hrN := htB_rot_v.trans (fullTour_isRotated_of_connected hvalid'.compat hvN)
      exact ⟨tA, tB, List.Perm.swap _ _ rest, hrO, hrN,
        hmem_of_rot tA oldRoot aO haO_mem (by simp) hrO,
        hmem_of_rot tB newRoot aN haN_mem (by simp) hrN⟩
    · have hrO := htB_rot_v.trans (fullTour_isRotated_of_connected hvalid'.compat hvO)
      have hrN := htA_rot_u.trans (fullTour_isRotated_of_connected hvalid'.compat huN)
      exact ⟨tB, tA, List.Perm.refl _, hrO, hrN,
        hmem_of_rot tB oldRoot aO haO_mem (by simp) hrO,
        hmem_of_rot tA newRoot aN haN_mem (by simp) hrN⟩
  obtain ⟨tOld, tNew, hperm_on, htOld_rot, htNew_rot, hfeO_tOld, hfeN_tNew⟩ := horient
  have hinv₄_on := (hinv₄.perm hperm_on).1
  -- Steps 5..7: update isRoot[newRoot] := 1, setValNode(feN), rotateFront(feO), rotateFront(feN)
  set mem5 := Function.update st₄.mem (isRootBase b vCap + newRoot) 1
  have hn₅_pre : tourLayout.NodesAt mem5 (nodesBase b vCap eCap) x.numNodes s₄ :=
    NodesAt.congr tourLayout hn₄ fun a ha =>
      Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega) _ _
  have hfr14 : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem st₄.mem :=
    hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄))
  have hzero5 : ZeroFrom mem5 heap := fun a ha => by
    dsimp only [mem5]
    rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
    exact hfr14.1 a ha
  set opN := if (s₄.nodes feN).val.isOpen then 1 else 0
  set mkN := if (s₄.nodes feN).val.isMarked then 1 else 0
  have hmem5_opN : mem5 (nodesBase b vCap eCap + 17 * feN + 9) = opN := nodesAt_isOpen hn₅_pre hfeN_cap
  have hmem5_mkN : mem5 (nodesBase b vCap eCap + 17 * feN + 10) = mkN := nodesAt_isMarked hn₅_pre hfeN_cap
  obtain ⟨tNew₁, s₅, o₅, st₅, c₅, hrun₅, hn₅, hfr₅, hinv₅, hvals₅, _, _, hlist₅, hvalN₅, hvalne₅, _, hcost₅⟩ :=
    tourSetValNodeBody_runs (isOpen := opN) (isMarked := mkN) (rootTag := newRoot + 1)
      (fuel := 2 * eCap + 2) (pos := st₄.pos) C ω hn₅_pre hinv₄_on hvals₄ hfeN_tNew
      (by omega) (by have := h.numNodes_le; omega) (by omega) ⟨hheap0.rec_le, hroom, hzero5, hwide⟩
  have hinv₅_swap := (hinv₅.perm (List.Perm.swap tOld tNew₁ rest)).1
  obtain ⟨tOld', s₆, o₆, st₆, c₆, hrun₆, _, hn₆, hfr₆, hinv₆, hvals₆, _, hrot₆, hval₆, _, hcost₆⟩ :=
    tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₅.pos) C.toTourSplayOpsProcs ω
      hn₅ hinv₅_swap hvals₅ hfeO_tOld (by have := h.numNodes_le; omega) (by omega) ⟨hheap0.rec_le, hroom, hfr₅.1, hwide⟩
  have hinv₆_swap := (hinv₆.perm (List.Perm.swap tNew₁ tOld' rest)).1
  have hfeN_tNew1 : feN ∈ tNew₁.toList := by rw [hlist₅]; exact hfeN_tNew
  obtain ⟨tNew', s₇, o₇, st₇, c₇, hrun₇, _, hn₇, hfr₇, hinv₇, _, _, hrot₇, hval₇, _, hcost₇⟩ :=
    tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₆.pos) C.toTourSplayOpsProcs ω
      hn₆ hinv₆_swap hvals₆ hfeN_tNew1 (by have := h.numNodes_le; omega) (by omega) ⟨hheap0.rec_le, hroom, hfr₆.1, hwide⟩
  have htOld'_map : tOld'.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord F' hvalid'.compat.forest oldRoot := by
    rw [hrot₆]
    have hnd := htOld_rot.perm.nodup_iff.mpr (fullTour_spec hvalid'.compat oldRoot).1
    rw [rotateNatList_map_of_nodup' hnd hfeO_tOld, hfeO_key, endOfKey_endKey']
    exact rotateToList_fullTour_of_isRotated hvalid'.compat haO htOld_rot
  have htNew'_map : tNew'.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord F' hvalid'.compat.forest newRoot := by
    rw [hrot₇, hlist₅]
    have hnd := htNew_rot.perm.nodup_iff.mpr (fullTour_spec hvalid'.compat newRoot).1
    rw [rotateNatList_map_of_nodup' hnd hfeN_tNew, hfeN_key, endOfKey_endKey']
    exact rotateToList_fullTour_of_isRotated hvalid'.compat haN htNew_rot
  -- Verify `TourRepAt` for `s'Abs := tourCut s e newRoot`
  set s'Abs := tourCut s e newRoot
  let ct' := Function.update (Function.update x.compTree oldRoot (some tOld')) newRoot (some tNew')
  set x' : TourConcrete R_ord.τ := { x with st := s₇, trees := tNew' :: tOld' :: rest, compTree := ct' }
  have hfr57 : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem5 st₇.mem :=
    hfr₅.trans (hfr₆.trans hfr₇)
  have hpre_eq5 : ∀ a < nodesBase b vCap eCap, st₇.mem a = mem5 a := fun a ha =>
    hfr57.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha)
  have hpre_eq_mem : ∀ a < nodesBase b vCap eCap, a ≠ isRootBase b vCap + newRoot → st₇.mem a = mem a := fun a ha hne => by
    rw [hpre_eq5 a ha]; dsimp only [mem5]; rw [Function.update_of_ne hne]
    exact hfr14.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha)
  have hord_eq : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → mem a = st₇.mem a := fun a ha => by
    have ha_ge := h.ordFootGe a ha
    rw [hfr57.2 a (hfoot a (Or.inr ha)) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le ha_ge)]
    dsimp only [mem5]
    rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at ha_ge ⊢; omega),
      hfr14.2 a (hfoot a (Or.inr ha)) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le ha_ge)]
  have hOrd := hLoc (ordHandleOf b vCap eCap) s.ord x.ordX mem st₇.mem hord_eq
  have hhdr' : TourHeaderAt vCap eCap b x.numNodes st₇.mem := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, st₇.mem (b + k) = mem (b + k) := fun k hk =>
      hpre_eq_mem (b + k) (by simp [nodesBase]; omega) (by simp [isRootBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  have ht_not_rest : t ∉ rest := fun hm => by
    have hnd := hf_perm.nodupAll
    rw [List.flatMap_cons, List.nodup_append] at hnd
    exact hnd.2.2 nx hnx_t nx (List.mem_flatMap.mpr ⟨t, hm, hnx_t⟩) rfl
  have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ oldRoot → x.compTree r' ≠ some t := by
    intro r' hr' hne hcr'
    have hft' : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := by
      intro hnil; have := h.comp_none r' hr' hnil; rw [hcr'] at this; simp at this
    obtain ⟨tr', hctr', _, htr'_map⟩ := h.comp_some r' hr' hft'
    have hteq : tr' = t := Option.some.inj (hctr'.symm.trans hcr'); subst hteq
    have he1 : endOfKey (x.keyOf nx) ∈ fullTour s.ord s.rf.F h.valid.compat.forest oldRoot := by
      rw [← ht_map]; exact List.mem_map_of_mem hnx_t
    have he2 : endOfKey (x.keyOf nx) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
      rw [← htr'_map]; exact List.mem_map_of_mem hnx_t
    obtain ⟨v1, hv1, hc1⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he1
    obtain ⟨v2, hv2, hc2⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he2
    have hv12 : v1 = v2 := h.valid.compat.unique v1 v2 _ hv1 hv2; subst hv12
    have hvF := h.valid.compat.vert v1 (List.ne_nil_of_mem hv1)
    exact hne ((h.valid.root_eq_of_mem hvF hr' (connected_symm hc2)).symm.trans
      (h.valid.root_eq_of_mem hvF holdR (connected_symm hc1)))
  have hft_other_eq : ∀ r' ∈ s.rf.R, r' ≠ oldRoot →
      fullTour s.ord F' hvalid'.compat.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr' hne
    have hnd1 := (fullTour_spec hvalid'.compat r').1
    have hnd2 := (fullTour_spec h.valid.compat r').1
    by_cases hnil : s.ord r' = []
    · change fullTour s'Abs.ord s'Abs.rf.F hvalid'.compat.forest r' = _
      rw [(fullTour_eq_nil_iff hvalid'.compat r').mpr hnil, (fullTour_eq_nil_iff h.valid.compat r').mpr hnil]
    · obtain ⟨a', ha'⟩ : ∃ a', (s.ord r').head? = some a' :=
        Option.isSome_iff_exists.mp (by cases ho : s.ord r' <;> simp_all)
      have hsub_ft : ∀ z ∈ fullTour s.ord s.rf.F h.valid.compat.forest r', z.1 ≠ e := by
        intro z hz hez
        obtain ⟨w', hzw', hcw'⟩ := ((fullTour_spec h.valid.compat r').2 z).mp hz
        have hze : z = (e, true) ∨ z = (e, false) := by
          obtain ⟨f, b⟩ := z; change f = e at hez; subst f; cases b <;> simp
        rcases hze with rfl | rfl
        · have hwu := h.valid.compat.unique w' u _ hzw' hx_ord; subst hwu
          exact hne ((h.valid.root_eq_of_mem (h.valid.compat.vert u (List.ne_nil_of_mem hx_ord)) hr' (connected_symm hcw')).symm)
        · have hwv := h.valid.compat.unique w' v _ hzw' hy_ord; subst hwv
          exact hne ((h.valid.root_eq_of_mem (h.valid.compat.vert v (List.ne_nil_of_mem hy_ord)) hr' (connected_symm hcw')).symm.trans hrv_eq)
      have ha'_in1 : a' ∈ fullTour s.ord F' hvalid'.compat.forest r' :=
        ((fullTour_spec hvalid'.compat r').2 a').mpr ⟨r', List.mem_of_head? ha', connected_refl F' r'⟩
      have ha'_in2 : a' ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' :=
        ((fullTour_spec h.valid.compat r').2 a').mpr ⟨r', List.mem_of_head? ha', connected_refl _ r'⟩
      have hrot_eq : (fullTour s.ord F' hvalid'.compat.forest r').IsRotated
          (fullTour s.ord s.rf.F h.valid.compat.forest r') :=
        isRotated_of_cycNext_eq hnd1 hnd2 ha'_in1 ha'_in2
          (fun z hz => by
            have hz2 : z ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
              obtain ⟨w', hzw', hcw'⟩ := ((fullTour_spec hvalid'.compat r').2 z).mp hz
              exact ((fullTour_spec h.valid.compat r').2 z).mpr
                ⟨w', hzw', connected_of_subgraph (eraseForestEdge_subgraph s.rf.F e) hcw'⟩
            have hzne := hsub_ft z hz2
            refine (fullTour_cycNext hvalid'.compat r' z hz).trans ?_
            change eulerSucc s.ord F' z = eulerSucc s.ord s.rf.F z
            simp only [eulerSucc, F', eraseForestEdge, Finset.mem_erase, hzne, ne_eq, not_false_eq_true, true_and]
            rfl)
          (fullTour_cycNext h.valid.compat r')
      have hrot_back := tour_rotateToList_eq_of_isRotated hnd2 hrot_eq (fullTour_head? h.valid.compat r' ha')
      have hrot_self := tour_rotateToList_eq_of_isRotated hnd1 (List.IsRotated.refl _) (fullTour_head? hvalid'.compat r' ha')
      exact hrot_self.symm.trans hrot_back
  have hmem_flat : ∀ id, id ∈ (tNew' :: tOld' :: rest).flatMap AuxTree.toList ↔ id ∈ (t :: rest).flatMap AuxTree.toList := by
    intro id
    have h1 : id ∈ tNew'.toList ↔ id ∈ tNew.toList := by
      rw [hrot₇, hlist₅]; exact (rotateNatList_perm hfeN_tNew).mem_iff
    have h2 : id ∈ tOld'.toList ↔ id ∈ tOld.toList := by
      rw [hrot₆]; exact (rotateNatList_perm hfeO_tOld).mem_iff
    have h3 : id ∈ (tNew :: tOld :: rest).flatMap AuxTree.toList ↔ id ∈ (tA :: tB :: rest).flatMap AuxTree.toList := by
      simp only [List.mem_flatMap]
      exact ⟨fun ⟨a, ha, hi⟩ => ⟨a, hperm_on.mem_iff.mpr ha, hi⟩,
        fun ⟨a, ha, hi⟩ => ⟨a, hperm_on.mem_iff.mp ha, hi⟩⟩
    have h4 : id ∈ tA.toList ∨ id ∈ tB.toList ↔ id ∈ t.toList := by
      rw [← (rotateNatList_perm hnx_t).mem_iff, ← ht3_eq_t, hrot_split, htA_list, htB_list]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((rfl | hq) | (ha | rfl))
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inr hq)
        · exact Or.inl (Or.inr ha)
        · exact Or.inr (Or.inl rfl)
      · rintro ((rfl | ha) | (rfl | hq))
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr hq)
    simp only [List.flatMap_cons, List.mem_append] at h3 ⊢
    rw [h1, h2, h3, ← or_assoc, h4]
  have hrep' : TourRepAt R_ord vCap eCap b s'Abs x' st₇.mem :=
    { valid := hvalid'
      ordRep := hOrd.1 h.ordRep
      ordFootGe := h.ordFootGe
      header := hhdr'
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hpre_eq_mem _ (by simp [nodeOfEndBase, nodesBase]; omega) (by simp [nodeOfEndBase, isRootBase]; omega)]
        exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun id h1 h2 => by
        dsimp only [x'] at h2; have hle := h.numNodes_le
        rw [hpre_eq_mem _ (by simp [keyOfNodeBase, nodesBase]; omega) (by simp [keyOfNodeBase, isRootBase]; omega)]
        exact h.keyOf_mem id h1 h2
      firstEnd_mem := fun w' hw' => by
        rw [hpre_eq_mem _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, isRootBase]; omega)]
        exact h.firstEnd_mem w' hw'
      isRoot_mem := fun w' hw' => by
        rw [hpre_eq5 _ (by simp [isRootBase, nodesBase]; omega)]; dsimp only [mem5]
        by_cases hwn : w' = newRoot
        · subst w'; simp [s'Abs, tourCut]
        · rw [Function.update_of_ne (by omega),
            hfr14.2 _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega)),
            h.isRoot_mem w' hw']
          simp [s'Abs, tourCut, hwn]
      active_end := fun w' hw' z hz => by
        have hz_lt : endKey z < 2 * eCap := by
          have := h.valid.ordWithin.2.2 w' z hz; simp only [endKey]; cases z.2 <;> simp <;> omega
        rw [hpre_eq_mem _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)]
        exact h.active_end w' hw' z hz
      inactive_owner := fun k hk hno => by
        rw [hpre_eq_mem _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)]
        exact h.inactive_owner k hk hno
      slot_bij := h.slot_bij
      slotOf_mem := fun v hv => by
        rw [hpre_eq_mem _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, isRootBase]; omega)]
        exact h.slotOf_mem v hv
      vertOf_mem := fun sl hsl => by
        rw [hpre_eq_mem _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, isRootBase]; omega)]
        exact h.vertOf_mem sl hsl
      markArr_zero := fun k hk => by
        rw [hpre_eq_mem _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, isRootBase]; omega)]
        exact h.markArr_zero k hk
      nodesAt := hn₇
      forestInv := hinv₇
      nodes_exact := fun id => by
        have h2 : id ∈ (t :: rest).flatMap AuxTree.toList ↔ id ∈ x.trees.flatMap AuxTree.toList := by
          simp only [List.mem_flatMap]
          exact ⟨fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mpr ha, hu⟩,
            fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mp ha, hu⟩⟩
        exact (hmem_flat id).trans (h2.trans (h.nodes_exact id))
      comp_none := fun r' hr' hnil => by
        have hrn : r' ≠ newRoot := fun heq => by
          subst r'; exact hordNew_ne ((fullTour_eq_nil_iff hvalid'.compat newRoot).mp hnil)
        have hr'R : r' ∈ s.rf.R := (Finset.mem_insert.mp hr').resolve_left hrn
        have hro : r' ≠ oldRoot := fun heq => by
          subst r'; exact hordOld_ne ((fullTour_eq_nil_iff hvalid'.compat oldRoot).mp hnil)
        simp only [x', ct', Function.update_of_ne hrn, Function.update_of_ne hro]
        change fullTour s.ord F' hvalid'.compat.forest r' = [] at hnil
        rw [hft_other_eq r' hr'R hro] at hnil
        exact h.comp_none r' hr'R hnil
      comp_some := fun r' hr' hne_ft => by
        by_cases hrn : r' = newRoot
        · subst r'
          exact ⟨tNew', by simp [x', ct'], by simp [x'], htNew'_map⟩
        · have hr'R : r' ∈ s.rf.R := (Finset.mem_insert.mp hr').resolve_left hrn
          by_cases hro : r' = oldRoot
          · subst r'
            exact ⟨tOld', by simp [x', ct', Function.update_of_ne hrn], by simp [x'], htOld'_map⟩
          · change fullTour s.ord F' hvalid'.compat.forest r' ≠ [] at hne_ft
            rw [hft_other_eq r' hr'R hro] at hne_ft
            obtain ⟨tr', hctr', htr'_mem, htr'_map⟩ := h.comp_some r' hr'R hne_ft
            have htr'_ne : tr' ≠ t := fun heq => hcomp_inj r' hr'R hro (heq ▸ hctr')
            have htr'_rest : tr' ∈ rest := (List.mem_cons.mp (hperm.mem_iff.mp htr'_mem)).resolve_left htr'_ne
            exact ⟨tr', by simp [x', ct', Function.update_of_ne hrn, Function.update_of_ne hro, hctr'],
              by simp [x', htr'_rest], by change _ = fullTour s.ord F' hvalid'.compat.forest r'; rw [hft_other_eq r' hr'R hro]; exact htr'_map⟩
      tree_class := fun tr htr => by
        simp only [x', List.mem_cons] at htr
        rcases htr with rfl | rfl | hrest
        · exact Or.inl ⟨newRoot, Finset.mem_insert_self _ _, by simp [x', ct']⟩
        · exact Or.inl ⟨oldRoot, Finset.mem_insert_of_mem holdR, by
            simp only [x', ct', Function.update_apply,
              show oldRoot ≠ newRoot from fun heq => hnewNotR (heq ▸ holdR), ↓reduceIte]⟩
        · have htr_mem : tr ∈ x.trees := hperm.mem_iff.mpr (by simp [hrest])
          rcases h.tree_class tr htr_mem with ⟨r', hr', hcr'⟩ | hsing
          · have hro : r' ≠ oldRoot := fun heq => by
              subst heq; exact ht_not_rest ((Option.some.inj (hcr'.symm.trans hct)) ▸ hrest)
            have hrn : r' ≠ newRoot := fun heq => hnewNotR (heq ▸ hr')
            exact Or.inl ⟨r', Finset.mem_insert_of_mem hr',
              by simp [x', ct', Function.update_of_ne hrn, Function.update_of_ne hro, hcr']⟩
          · exact Or.inr hsing
      inactive_single := fun id h1 h2 hno => by
        have hmem := h.inactive_single id h1 h2 hno
        have hne : AuxTree.node id .leaf .leaf ≠ t := fun heq => by
          have he' : endOfKey (x.keyOf id) ∈ fullTour s.ord s.rf.F h.valid.compat.forest oldRoot := by
            rw [← ht_map, ← heq]; simp [AuxTree.toList]
          obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he'
          exact hno w' hw'
        have hrest : AuxTree.node id .leaf .leaf ∈ rest :=
          (List.mem_cons.mp (hperm.mem_iff.mp hmem)).resolve_left hne
        simp [x', hrest]
      val_active := fun id h1 h2 hact => by
        dsimp only [x'] at h2 ⊢
        have hid_cap : id ≤ x.numNodes := h2
        rw [hval₇ id hid_cap, hval₆ id hid_cap]
        have hs4_val : ∀ z ≤ x.numNodes, 1 ≤ z → z ≤ x.numNodes → (∃ w', endOfKey (x.keyOf z) ∈ s.ord w') →
            (s₄.nodes z).val =
              { isOpen := decide ((endOfKey (x.keyOf z)).1 ∉ F'.E)
                isMarked := decide (endOfKey (x.keyOf z) ∈ s.marked)
                rootTag := tourRootTagVal s (endOfKey (x.keyOf z)) } := by
          intro z hz_cap hz1 hz2 hzact
          rw [hval₄ z hz_cap]
          by_cases hzy : z = ny
          · subst z
            rw [hvalY₃, hny_key, endOfKey_two_mul_add1]
            have hny_not_mk : (e, false) ∉ s.marked := fun hm => (h.valid.marked_open _ hm).2 he
            have hrt_ny : rtY = tourRootTagVal s (e, false) := by
              have := h.val_active ny hny_pos hny_le ⟨v, by rw [hny_key, endOfKey_two_mul_add1]; exact hy_ord⟩
              dsimp only [rtY]; rw [this, hny_key, endOfKey_two_mul_add1]
            simp [F', hny_not_mk, hrt_ny]
          · rw [hvalne₃ z hz_cap hzy]
            by_cases hzx : z = nx
            · subst z
              rw [hvalX₂, hnx_key, tour_endOfKey_two_mul]
              have hnx_not_mk : (e, true) ∉ s.marked := fun hm => (h.valid.marked_open _ hm).2 he
              have hrt_nx : rtX = tourRootTagVal s (e, true) := by
                have := h.val_active nx hnx_pos hnx_le ⟨u, by rw [hnx_key, tour_endOfKey_two_mul]; exact hx_ord⟩
                dsimp only [rtX]; rw [this, hnx_key, tour_endOfKey_two_mul]
              simp [F', hnx_not_mk, hrt_nx]
            · rw [hvalne₂ z hz_cap hzx, hval₁ z hz_cap, h.val_active z hz1 hz2 hzact]
              have hzne : (endOfKey (x.keyOf z)).1 ≠ e := by
                intro heq
                have hcases : endOfKey (x.keyOf z) = (e, true) ∨ endOfKey (x.keyOf z) = (e, false) := by
                  cases hb : (endOfKey (x.keyOf z)).2
                  · right; exact Prod.ext heq hb
                  · left; exact Prod.ext heq hb
                rcases hcases with hc | hc
                · have hk : x.keyOf z = 2 * e := by rw [← endKey_endOfKey' (x.keyOf z), hc]; rfl
                  have := (h.keyOf_mem z hz1 hz2).2.2; rw [hk] at this; exact hzx this.symm
                · have hk : x.keyOf z = 2 * e + 1 := by rw [← endKey_endOfKey' (x.keyOf z), hc]; rfl
                  have := (h.keyOf_mem z hz1 hz2).2.2; rw [hk] at this; exact hzy this.symm
              simp [F', hzne]
        by_cases hidN : id = feN
        · subst id
          rw [hvalN₅, hfeN_key, endOfKey_endKey',
            tourRootTagVal_eq_succ hvalid' (Finset.mem_insert_self _ _) haN]
          have hvs4 := hs4_val feN hfeN_cap hfeN_pos hfeN_le ⟨newRoot, by rw [hfeN_key, endOfKey_endKey']; exact haN_mem⟩
          have hop : decide (0 < opN) = (s₄.nodes feN).val.isOpen :=
            (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
          have hmk : decide (0 < mkN) = (s₄.nodes feN).val.isMarked :=
            (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
          rw [hvs4, hfeN_key, endOfKey_endKey'] at hop hmk
          simp [hop, hmk, s'Abs, tourCut, F']
        · rw [hvalne₅ id hid_cap hidN, hs4_val id hid_cap h1 h2 hact]
          have hne_aN : endOfKey (x.keyOf id) ≠ aN := fun heq => by
            have hk : x.keyOf id = endKey aN := by rw [← endKey_endOfKey' (x.keyOf id), heq]
            have := (h.keyOf_mem id h1 h2).2.2; rw [hk] at this; exact hidN this.symm
          have hrt_eq : tourRootTagVal s'Abs (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
            by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
            · obtain ⟨r', hr'R, hr'h⟩ := hex
              rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                tourRootTagVal_eq_succ hvalid' (Finset.mem_insert_of_mem hr'R) hr'h]
            · push Not at hex
              rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
              intro r' hr' hh
              rcases Finset.mem_insert.mp hr' with rfl | hr'R
              · exact hne_aN (Option.some.inj (hh.symm.trans haN))
              · exact hex r' hr'R hh
          rw [hrt_eq]; rfl
      val_inactive_rt := fun id h1 h2 hno => by
        dsimp only [x'] at h2 ⊢
        have hid_cap : id ≤ x.numNodes := h2
        have hidN : id ≠ feN := fun heq => by subst id; rw [hfeN_key, endOfKey_endKey'] at hno; exact hno newRoot haN_mem
        have hidY : id ≠ ny := fun heq => by subst id; rw [hny_key, endOfKey_two_mul_add1] at hno; exact hno v hy_ord
        have hidX : id ≠ nx := fun heq => by subst id; rw [hnx_key, tour_endOfKey_two_mul] at hno; exact hno u hx_ord
        rw [hval₇ id hid_cap, hval₆ id hid_cap, hvalne₅ id hid_cap hidN, hval₄ id hid_cap,
          hvalne₃ id hid_cap hidY, hvalne₂ id hid_cap hidX, hval₁ id hid_cap]
        exact h.val_inactive_rt id h1 h2 hno
      val_unused_rt := fun id hid hcond => by
        dsimp only [x'] at hcond
        have hidN : id ≠ feN := by omega
        have hidY : id ≠ ny := by omega
        have hidX : id ≠ nx := by omega
        rw [hval₇ id hid, hval₆ id hid, hvalne₅ id hid hidN, hval₄ id hid,
          hvalne₃ id hid hidY, hvalne₂ id hid hidX, hval₁ id hid]
        exact h.val_unused_rt id hid hcond }
  -- Invoke the clean WordRAM execution helper
  have hst4_pre : ∀ a < nodesBase b vCap eCap, st₄.mem a = mem a := fun a ha =>
    hfr14.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha)
  have hst5_feO : st₅.mem (firstEndBase b + oldRoot) = feO := by
    rw [hfr₅.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase (by simp [firstEndBase, nodesBase]; omega))]
    dsimp only [mem5]
    rw [Function.update_of_ne (by simp [firstEndBase, isRootBase]; omega),
      hst4_pre _ (by simp [firstEndBase, nodesBase]; omega)]
    exact hfeO_first
  obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody⟩ := tourOpCutBody_exec C hcs ω hord_le hroom hwide
    he_lt hnewLt holdLt
    (by simpa [nodeAddr, tourLayout_stride] using hheap0.addr_lt hnx_cap)
    (by simpa [nodeAddr, tourLayout_stride] using hheap0.addr_lt hny_cap)
    (by simpa [nodeAddr, tourLayout_stride] using hheap0.addr_lt hfeN_cap)
    hhdr.2.2.2.2.2.2.1 (h.nodeOf_mem (2 * e) (by omega)).1 (h.nodeOf_mem (2 * e + 1) (by omega)).1
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1 hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    hrun₁ ho₁_eq hrtX_mem hrun₂ hrtY_mem hrun₃ hrun₄
    (by rw [hst4_pre _ (by simp [HDR_IS_ROOT, nodesBase]; omega)]; exact hhdr.2.2.2.2.2.1)
    (by rw [hst4_pre _ (by simp [HDR_FIRST_END, nodesBase]; omega)]; exact hhdr.2.2.2.2.1)
    (by rw [hst4_pre _ (by simp [firstEndBase, nodesBase]; omega)]; exact hfeN_first)
    hmem5_opN hmem5_mkN hrun₅ hst5_feO hrun₆ hrun₇
  have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem heap b x' st₇.mem :=
    ⟨le_refl heap, Nat.le_add_right heap 2, hfr57.1,
      fun a ha hnf => by
        have hnr : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hrec =>
          hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; simp [nodesBase] at this; omega, (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).2⟩)
        rw [hfr57.2 a ha hnr]; dsimp only [mem5]
        rw [Function.update_of_ne (fun heq => hnf (Or.inl ⟨by simp [isRootBase] at heq ⊢; omega, by simp [isRootBase, ordHandleOf, tourFixedSize] at heq ⊢; omega⟩)), hfr14.2 a ha hnr],
      fun a ha => Or.inl ha⟩
  refine ⟨.returned heap, st_fin, c_fin, hbody, x', hmem_fin ▸ hrep', hmem_fin ▸ hresp, ?_⟩
  have hlog := tourLog_of_le h.numNodes_le
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  rw [forestPhi_perm hperm_on] at hcost₄
  rw [← forestPhi_perm (List.Perm.swap tOld tNew₁ rest)] at hcost₆
  rw [← forestPhi_perm (List.Perm.swap tNew₁ tOld' rest)] at hcost₇
  have hmul_c : (4 * TOUR_FIND_AMORT + TOUR_CUTSPLIT_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
      (4 * TOUR_FIND_AMORT + TOUR_CUTSPLIT_AMORT + 2 * TOUR_SEQ_AMORT) * (2 * tourLog eCap) :=
    Nat.mul_le_mul_left _ hlog
  dsimp only [tourRep, tourPhi, x']
  rw [hmem_fin, ← hOrd.2, forestPhi_perm hperm]
  simp only [TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_SEQ_AMORT,
    TOUR_CUTSPLIT_AMORT, TOUR_CUTLINK_MUL] at hcost₁ hcost₂ hcost₃ hcost₄ hcost₅ hcost₆ hcost₇ hmul_c hcfin ⊢
  omega

end MinCostFlow.SparseCore.Program
