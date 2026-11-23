module

public import MinCostFlow.SparseCore.Program.TourOpsList
import Mathlib.Tactic

/-!
# Point query operations (`adjacent`, `nextOpen`, `nextMarked`, `rootOf`)

Implements and verifies Ops `5` (`adjacent`), `6` (`nextOpen`), `8` (`nextMarked`), and `10`
(`rootOf`) of `tourContract`, each running in `O(tourLog eCap)` amortized time and returning
`heap + 1` (using `3` words of heap headroom).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM bodies for point-query operations -/

/-- Op 6 (`nextOpen`): args `[b, keyX, heap]`. Writes `endKey (tourNextOpen s x)` at `heap`. -/
def tourOpNextOpenBody (nextOpenProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
  .call 8 nextOpenProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
  .store (.reg 2) (.load (.bin .add (.reg 7) (.reg 8))) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- Op 5 (`adjacent`): args `[b, keyX, keyY, heap]`. Writes `1` at `heap` iff `tourAdjacent s x y`. -/
def tourOpAdjacentBody (nextOpenProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 4 (.load (.bin .add (.reg 4) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
  .call 8 nextOpenProc [.reg 5, .reg 4, .reg 6, .reg 3] ;;
  .assign 8 (.load (.bin .add (.reg 7) (.reg 8))) ;;
  .store (.reg 3) (.bin .eq (.reg 8) (.reg 2)) ;;
  .ret (.bin .add (.reg 3) (.const 1))

/-- Op 8 (`nextMarked`): args `[b, keyX, heap]`. Writes `0` or `1 + endKey y` at `heap`. -/
def tourOpNextMarkedBody (nextMarkProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
  .call 8 nextMarkProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
  .cond (.bin .eq (.reg 8) (.const 0))
    (.store (.reg 2) (.const 0))
    (.store (.reg 2) (.bin .add (.const 1) (.load (.bin .add (.reg 7) (.reg 8))))) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- Op 10 (`rootOf`): args `[b, keyX, heap]`. Writes `s.rf.root (ordSrc s.ord x)` at `heap`. -/
def tourOpRootOfBody (rootTagProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .call 7 rootTagProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
  .store (.reg 2) (.bin .sub (.reg 7) (.const 1)) ;;
  .ret (.bin .add (.reg 2) (.const 1))

theorem tourOpsPointQuery_bodies_noRand (nO nM rT : ℕ) :
    (tourOpNextOpenBody nO).NoRand ∧
    (tourOpAdjacentBody nO).NoRand ∧
    (tourOpNextMarkedBody nM).NoRand ∧
    (tourOpRootOfBody rT).NoRand := by
  simp [tourOpNextOpenBody, tourOpAdjacentBody, tourOpNextMarkedBody, tourOpRootOfBody, Stmt.NoRand]

/-! ## Shared setup for `tourNextReadyBody` on an active end -/

private theorem rotateNatList_map_of_nodup {L : List ℕ} {f : ℕ → End} {nx : ℕ}
    (hnd : (L.map f).Nodup) (hnx : nx ∈ L) :
    (rotateNatList nx L).map f = rotateToList (f nx) (L.map f) := by
  have hidx : (L.map f).idxOf (f nx) = L.idxOf nx := by
    induction L with
    | nil => simp at hnx
    | cons a t ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hax : a = nx
      · subst hax; simp
      · have hnt : nx ∈ t := (List.mem_cons.mp hnx).resolve_left (Ne.symm hax)
        have hne : f a ≠ f nx := fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hnt)
        simp [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hne, ih hnd.2 hnt]
  have hfnx : f nx ∈ L.map f := List.mem_map_of_mem hnx
  simp only [rotateNatList, rotateToList, hnx, hfnx, ↓reduceIte,
    List.map_append, List.map_drop, List.map_take, hidx]

private theorem find?_rotateNatList_map {L : List ℕ} {f : ℕ → End} {nx : ℕ}
    {p : ℕ → Bool} {q : End → Bool}
    (hnd : (L.map f).Nodup) (hnx : nx ∈ L)
    (hpq : ∀ u ∈ L, p u = q (f u)) :
    (((rotateNatList nx L).tail ++ [nx]).find? p).map f =
      ((rotateToList (f nx) (L.map f)).tail ++ [f nx]).find? q := by
  have hrot : (rotateNatList nx L).map f = rotateToList (f nx) (L.map f) :=
    rotateNatList_map_of_nodup hnd hnx
  have hmap_eq : (((rotateNatList nx L).tail ++ [nx]).map f) =
      (rotateToList (f nx) (L.map f)).tail ++ [f nx] := by
    rw [List.map_append, List.map_tail, hrot]; rfl
  rw [← hmap_eq, List.find?_map]
  have hsub : ∀ u ∈ (rotateNatList nx L).tail ++ [nx], u ∈ L := by
    intro u hu
    rcases List.mem_append.mp hu with htl | hsg
    · exact mem_of_mem_rotateNatList hnx (List.mem_of_mem_tail htl)
    · simp only [List.mem_singleton] at hsg; exact hsg ▸ hnx
  have hcongr : ((rotateNatList nx L).tail ++ [nx]).find? (q ∘ f) =
      ((rotateNatList nx L).tail ++ [nx]).find? p :=
    list_find?_congr fun u hu => (hpq u (hsub u hu)).symm
  rw [hcongr]

private theorem tourNextReady_on_active {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX heap pos dp fp : ℕ} {p : Program}
    {rs : TourSum → Bool} {rv : TourVal → Bool} {v : ℕ}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p)
    (T : ReadyTests w p tourLayout rs rv) (hTc : T.cost = TOUR_TEST_COST)
    (hR : ReadyLaw tourPayload rs rv)
    (hdp : p.procs[dp]? = some (descendBody dp C.lazy.pushDown T.sumTest T.valTest))
    (hfp : p.procs[fp]? = some (tourFindFirstBody dp T.sumTest C.splay.splay))
    (ω : ℕ → Bool) {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem) (hmemX : endOfKey keyX ∈ s.ord v)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 < 2 ^ w) :
    let r := s.rf.root v
    let nx := x.nodeOf keyX
    keyX < 2 * eCap ∧ 1 ≤ nx ∧ nx ≤ x.numNodes ∧
    ∃ y t' s' o st' c rest,
      Runs w p ω (tourNextReadyBody C.splay.splay C.detachLeft C.detachRight C.join fp T.sumTest T.valTest)
        (startState [nodesBase b vCap eCap, nx, 2 * eCap + 2, heap] mem pos) o st' c ∧
      o.value = y ∧
      (y ≠ 0 → 1 ≤ y ∧ y ≤ x.numNodes ∧ st'.mem (keyOfNodeBase b vCap eCap + y) = x.keyOf y) ∧
      (∀ outVal, outVal < 2 ^ w →
        let M' := Function.update st'.mem heap outVal
        let x' : TourConcrete R_ord.τ :=
          { x with st := s', trees := t' :: rest, compTree := Function.update x.compTree r (some t') }
        (tourRep R_ord vCap eCap).rep b s x' M' ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3 mem (heap + 1) b x' M' ∧
        (tourRep R_ord vCap eCap).phi b x' M' + c ≤
          (TOUR_NEXT_AMORT * 2) * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem) ∧
      (∃ t, x.compTree r = some t ∧ t ∈ x.trees ∧
        t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest r ∧
        (((rotateNatList nx t.toList).tail ++ [nx]).find? (fun u => rv (x.st.nodes u).val)).getD 0 = y ∧
        (∀ u ∈ t.toList, 1 ≤ u ∧ u ≤ x.numNodes ∧ ∃ w', endOfKey (x.keyOf u) ∈ s.ord w')) := by
  obtain ⟨_, hrR, _, hkey_lt', hnx_pos, hnx_le, _, t, rest, hct, hperm, ht_map, hnx_t⟩ :=
    h.mem_compTree_of_active hmemX
  rw [endKey_endOfKey'] at hkey_lt' hnx_pos hnx_le hnx_t
  have hord_le := h.fixed_le_heap hfoot
  have hheap0 := h.heapOk (sp := 2) hfoot hzero (by omega) hwide
  have hf_perm := (h.forestInv.perm hperm).1
  obtain ⟨y, t', s', o, st', c, hrun, hvy, hn', hfr', hinv', _, _, hlist', hval', _, hfind, hcost⟩ :=
    tourNextReadyBody_runs (fuel := 2 * eCap + 2) (pos := pos) C T hTc hR hdp hfp ω h.nodesAt hf_perm
      (h.valsOk hw) hnx_t (by have := h.numNodes_le; omega) (by omega) hheap0
  refine ⟨hkey_lt', hnx_pos, hnx_le, y, t', s', o, st', c, rest, hrun, hvy, ?_, ?_, ?_⟩
  · intro hy0
    have hy_mem : y ∈ t.toList := by
      cases hfp' : ((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find? (fun u => rv (x.st.nodes u).val) with
      | none => rw [hfp'] at hfind; exact absurd hfind.symm hy0
      | some z =>
        rw [hfp'] at hfind; simp only [Option.getD_some] at hfind; subst hfind
        rcases List.mem_append.mp (List.mem_of_find?_eq_some hfp') with htl | hsg
        · exact mem_of_mem_rotateNatList hnx_t (List.mem_of_mem_tail htl)
        · simp only [List.mem_singleton] at hsg; exact hsg ▸ hnx_t
    have hy_in := (h.nodes_exact y).mp (List.mem_flatMap.mpr ⟨t, hperm.mem_iff.mpr (by simp), hy_mem⟩)
    refine ⟨hy_in.1, hy_in.2, ?_⟩
    have hkr := hfr'.2 (keyOfNodeBase b vCap eCap + y)
      (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase (by have := h.numNodes_le; simp [keyOfNodeBase, nodesBase]; omega))
    rw [hkr]; exact (h.keyOf_mem y hy_in.1 hy_in.2).1
  · intro outVal _
    set M' := Function.update st'.mem heap outVal
    have hN' : tourLayout.NodesAt M' (nodesBase b vCap eCap) x.numNodes s' :=
      NodesAt.congr tourLayout hn' fun a ha => by
        dsimp only [M']; exact Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2; omega) _ _
    have hagree : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → M' a = mem a :=
      fun a ha hnr => by
        rw [show M' a = st'.mem a from by dsimp only [M']; exact Function.update_of_ne (by omega) _ _]
        exact hfr'.2 a ha hnr
    obtain ⟨hrep', hphi_ord, hphi_perm, hfoot_eq⟩ :=
      h.replace_compTree_same_list hLoc hfoot hrR hperm hct hlist' hN' hinv' hval' hagree
    refine ⟨hrep', ?_, ?_⟩
    · refine ⟨by omega, by omega, fun a ha => by
        dsimp only [M']; rw [Function.update_of_ne (by omega)]; exact hfr'.1 a (by omega),
        fun a ha hnf => hagree a ha fun hrec => hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; simp [nodesBase] at this; omega, (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).2⟩),
        fun a ha => Or.inl ((hfoot_eq a).mp ha)⟩
    · have hlog := tourLog_of_le h.numNodes_le
      have hlm := Nat.mul_le_mul_left TOUR_NEXT_AMORT hlog
      dsimp only [tourRep, tourPhi]
      rw [hphi_ord, hphi_perm]
      simp only [TOUR_PHI_MULT, TOUR_NEXT_AMORT] at hcost hlm ⊢
      omega
  · refine ⟨t, hct, hperm.mem_iff.mpr (by simp), ht_map, hfind, fun u hu => ?_⟩
    have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, hperm.mem_iff.mpr (by simp), hu⟩)
    have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp hu_ft
    exact ⟨hu_in.1, hu_in.2, w', hw'⟩

/-! ## Op 6 (`nextOpen`), Op 5 (`adjacent`), Op 8 (`nextMarked`), Op 10 (`rootOf`) -/

/-- Op 6 (`nextOpen [b, keyX, heap]`): verified amortized run theorem. -/
theorem tourOp_nextOpen_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX heap pos v : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hmemX : endOfKey keyX ∈ s.ord v) (hopenX : (endOfKey keyX).1 ∉ s.rf.F.E)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpNextOpenBody C.nextOpen)
        (startState [b, keyX, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        st'.mem heap = endKey (tourNextOpen s (endOfKey keyX)) ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  have hord_le := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hhdr := h.header
  obtain ⟨hkey_lt, hnx_pos, _, y, _, _, o_n, st_n, _, _, hrun_n, hvy, hy_info, hupd,
    t, hct, _, ht_map, hfind_y, hu_act⟩ :=
    tourNextReady_on_active (pos := pos) hLoc C C.openTests C.openTests_cost tourOpen_readyLaw
      C.openDesc_body C.findFirstOpen_body ω h hmemX hw hwide hfoot hzero hroom
  have hnx_t : x.nodeOf keyX ∈ t.toList := by
    obtain ⟨_, _, _, _, _, _, _, t0, _, hct0, _, _, hmem0⟩ := h.mem_compTree_of_active hmemX
    have ht0 : t0 = t := Option.some.inj (hct0.symm.trans hct)
    simpa [endKey_endOfKey', ht0] using hmem0
  have hnx_key : x.keyOf (x.nodeOf keyX) = keyX := h.nodeOf_keyOf keyX hkey_lt (by omega)
  have hft_nd : (fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v)).Nodup := (fullTour_spec h.valid.compat _).1
  have hrR : s.rf.root v ∈ s.rf.R := (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hmemX))).1
  have hfind_end : (((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find?
      (fun u => tourOpenRv (x.st.nodes u).val)).map (fun id => endOfKey (x.keyOf id)) =
      some (tourNextOpen s (endOfKey keyX)) := by
    have hmap := find?_rotateNatList_map (f := fun id => endOfKey (x.keyOf id))
      (p := fun u => tourOpenRv (x.st.nodes u).val)
      (q := fun z => decide (z.1 ∉ s.rf.F.E)) (ht_map.symm ▸ hft_nd) hnx_t fun u hu => by
        obtain ⟨h1, h2, w', hw'⟩ := hu_act u hu
        dsimp only [tourOpenRv]; rw [h.val_active u h1 h2 ⟨w', hw'⟩]
    rw [hmap, hnx_key, ht_map]
    have hmem_ft : endOfKey keyX ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) := by
      rw [← ht_map]; exact List.mem_map.mpr ⟨x.nodeOf keyX, hnx_t, by rw [hnx_key]⟩
    rw [find?_rotate_tail_append_eq_cycNext_filter hft_nd hmem_ft (decide_eq_true hopenX),
      fullTour_filter_open s.ord h.valid.compat.forest hrR]
    simp [tourNextOpen, h.valid.compat.ordSrc_eq hmemX]
  have hy_nz : y ≠ 0 := by
    cases hfp : ((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find? (fun u => tourOpenRv (x.st.nodes u).val) with
    | none => rw [hfp] at hfind_end; simp at hfind_end
    | some z =>
      rw [hfp] at hfind_y; simp only [Option.getD_some] at hfind_y; subst hfind_y
      have hz_t : z ∈ t.toList := by
        rcases List.mem_append.mp (List.mem_of_find?_eq_some hfp) with htl | hsg
        · exact mem_of_mem_rotateNatList hnx_t (List.mem_of_mem_tail htl)
        · simp only [List.mem_singleton] at hsg; exact hsg ▸ hnx_t
      exact Nat.ne_of_gt (hu_act z hz_t).1
  obtain ⟨hy1, hy2, hy_mem⟩ := hy_info hy_nz
  have hy_key_eq : x.keyOf y = endKey (tourNextOpen s (endOfKey keyX)) := by
    cases hfp : ((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find? (fun u => tourOpenRv (x.st.nodes u).val) with
    | none => rw [hfp] at hfind_end; simp at hfind_end
    | some z =>
      rw [hfp] at hfind_y hfind_end; simp only [Option.getD_some, Option.map_some, Option.some.injEq] at hfind_y hfind_end
      rw [← hfind_y, ← hfind_end, endKey_endOfKey']
  have hy_key_lt : x.keyOf y < 2 ^ w := by have := (h.keyOf_mem y hy1 hy2).2.1; omega
  unfold tourOpNextOpenBody
  set s0 : State := startState [b, keyX, heap] mem pos
  set r1 := Function.update s0.regs 3 (nodeOfEndBase b vCap)
  set r2 := Function.update r1 4 (x.nodeOf keyX)
  set r3 := Function.update r2 5 (nodesBase b vCap eCap)
  set r4 := Function.update r3 6 (2 * eCap + 2)
  set r5 := Function.update r4 7 (keyOfNodeBase b vCap eCap)
  set s_n : State := { st_n with regs := Function.update r5 8 o_n.value }
  set M' := Function.update st_n.mem heap (x.keyOf y)
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := x.nodeOf keyX) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (h.nodeOf_mem keyX hkey_lt).1
  have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
  have hcall := runs_call_regs4 8 5 4 6 2 (st := ⟨mem, r5, pos⟩) C.nextOpen_body
    (by simp [r5, r4, r3]) (by simp [r5, r4, r3, r2]) (by simp [r5, r4]) (by simp [r5, r4, r3, r2, r1, s0, startState]) hrun_n
  have hst : Runs w p ω (.store (.reg 2) (.load (.bin .add (.reg 7) (.reg 8)))) s_n .normal { s_n with mem := M' } 6 :=
    runs_store_iff.mpr ⟨heap, x.keyOf y, by simp [Expr.eval, s_n, r5, r4, r3, r2, r1, s0, startState],
      by simp [Expr.eval, s_n, r5, hvy, BinOp.eval, hy_mem,
        (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : keyOfNodeBase b vCap eCap + y < 2 ^ w)],
      rfl, rfl, rfl⟩
  have hret := runs_ret_reg_add1 (w := w) (p := p) (ω := ω) (st := { s_n with mem := M' }) (r := 2) (v := heap)
    (by simp [s_n, r5, r4, r3, r2, r1, s0, startState]) (by omega) (by omega)
  obtain ⟨hrep', hresp', hphi'⟩ := hupd (x.keyOf y) hy_key_lt
  refine ⟨.returned (heap + 1), { s_n with mem := M' }, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal ha5 (tour_runs_seq_normal hcall (tour_runs_seq_normal hst hret)))))),
    _, hrep', by simp [M', hy_key_eq], hresp', ?_⟩
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  simp only [TOUR_NEXT_AMORT, TOUR_QUERY_MUL] at hphi' ⊢; nlinarith

/-- Op 5 (`adjacent [b, keyX, keyY, heap]`): verified amortized run theorem. -/
theorem tourOp_adjacent_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX keyY heap pos vx vy : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hmemX : endOfKey keyX ∈ s.ord vx) (hopenX : (endOfKey keyX).1 ∉ s.rf.F.E)
    (hmemY : endOfKey keyY ∈ s.ord vy)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpAdjacentBody C.nextOpen)
        (startState [b, keyX, keyY, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        (open Classical in st'.mem heap = if tourAdjacent s (endOfKey keyX) (endOfKey keyY) then 1 else 0) ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hhdr := h.header
  obtain ⟨hkey_lt, hnx_pos, _, y, _, _, o_n, st_n, _, _, hrun_n, hvy, hy_info, hupd,
    t, hct, _, ht_map, hfind_y, hu_act⟩ :=
    tourNextReady_on_active (pos := pos) hLoc C C.openTests C.openTests_cost tourOpen_readyLaw
      C.openDesc_body C.findFirstOpen_body ω h hmemX hw hwide hfoot hzero hroom
  have hnx_t : x.nodeOf keyX ∈ t.toList := by
    obtain ⟨_, _, _, _, _, _, _, t0, _, hct0, _, _, hmem0⟩ := h.mem_compTree_of_active hmemX
    have ht0 : t0 = t := Option.some.inj (hct0.symm.trans hct)
    simpa [endKey_endOfKey', ht0] using hmem0
  have hnx_key : x.keyOf (x.nodeOf keyX) = keyX := h.nodeOf_keyOf keyX hkey_lt (by omega)
  have hft_nd : (fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root vx)).Nodup := (fullTour_spec h.valid.compat _).1
  have hrR : s.rf.root vx ∈ s.rf.R := (h.valid.root_spec (h.valid.compat.vert vx (List.ne_nil_of_mem hmemX))).1
  have hfind_end : (((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find?
      (fun u => tourOpenRv (x.st.nodes u).val)).map (fun id => endOfKey (x.keyOf id)) =
      some (tourNextOpen s (endOfKey keyX)) := by
    have hmap := find?_rotateNatList_map (f := fun id => endOfKey (x.keyOf id))
      (p := fun u => tourOpenRv (x.st.nodes u).val)
      (q := fun z => decide (z.1 ∉ s.rf.F.E)) (ht_map.symm ▸ hft_nd) hnx_t fun u hu => by
        obtain ⟨h1, h2, w', hw'⟩ := hu_act u hu
        dsimp only [tourOpenRv]; rw [h.val_active u h1 h2 ⟨w', hw'⟩]
    rw [hmap, hnx_key, ht_map]
    have hmem_ft : endOfKey keyX ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root vx) := by
      rw [← ht_map]; exact List.mem_map.mpr ⟨x.nodeOf keyX, hnx_t, by rw [hnx_key]⟩
    rw [find?_rotate_tail_append_eq_cycNext_filter hft_nd hmem_ft (decide_eq_true hopenX),
      fullTour_filter_open s.ord h.valid.compat.forest hrR]
    simp [tourNextOpen, h.valid.compat.ordSrc_eq hmemX]
  have hy_nz : y ≠ 0 := by
    cases hfp : ((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find? (fun u => tourOpenRv (x.st.nodes u).val) with
    | none => rw [hfp] at hfind_end; simp at hfind_end
    | some z =>
      rw [hfp] at hfind_y; simp only [Option.getD_some] at hfind_y; subst hfind_y
      have hz_t : z ∈ t.toList := by
        rcases List.mem_append.mp (List.mem_of_find?_eq_some hfp) with htl | hsg
        · exact mem_of_mem_rotateNatList hnx_t (List.mem_of_mem_tail htl)
        · simp only [List.mem_singleton] at hsg; exact hsg ▸ hnx_t
      exact Nat.ne_of_gt (hu_act z hz_t).1
  obtain ⟨_, hy2, hy_mem⟩ := hy_info hy_nz
  have hy_key_eq : x.keyOf y = endKey (tourNextOpen s (endOfKey keyX)) := by
    cases hfp : ((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find? (fun u => tourOpenRv (x.st.nodes u).val) with
    | none => rw [hfp] at hfind_end; simp at hfind_end
    | some z =>
      rw [hfp] at hfind_y hfind_end; simp only [Option.getD_some, Option.map_some, Option.some.injEq] at hfind_y hfind_end
      rw [← hfind_y, ← hfind_end, endKey_endOfKey']
  have hadj_iff : (x.keyOf y = keyY) ↔ tourAdjacent s (endOfKey keyX) (endOfKey keyY) := by
    rw [hy_key_eq, tourAdjacent_iff_nextOpen_eq h.valid ⟨vx, hmemX⟩ hopenX ⟨vy, hmemY⟩]
    exact ⟨fun he => by rw [← endOfKey_endKey' (tourNextOpen s (endOfKey keyX)), he],
      fun he => by rw [he, endKey_endOfKey']⟩
  set ans := if x.keyOf y = keyY then 1 else 0
  have hans_eq : ans = if tourAdjacent s (endOfKey keyX) (endOfKey keyY) then 1 else 0 := by
    simp [ans, hadj_iff]
  unfold tourOpAdjacentBody
  set s0 : State := startState [b, keyX, keyY, heap] mem pos
  set r1 := Function.update s0.regs 4 (nodeOfEndBase b vCap)
  set r2 := Function.update r1 4 (x.nodeOf keyX)
  set r3 := Function.update r2 5 (nodesBase b vCap eCap)
  set r4 := Function.update r3 6 (2 * eCap + 2)
  set r5 := Function.update r4 7 (keyOfNodeBase b vCap eCap)
  set s_n : State := { st_n with regs := Function.update r5 8 o_n.value }
  set r6 := Function.update s_n.regs 8 (x.keyOf y)
  set M' := Function.update st_n.mem heap ans
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 4) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := x.nodeOf keyX) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (h.nodeOf_mem keyX hkey_lt).1
  have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
  have hcall := runs_call_regs4 8 5 4 6 3 (st := ⟨mem, r5, pos⟩) C.nextOpen_body
    (by simp [r5, r4, r3]) (by simp [r5, r4, r3, r2]) (by simp [r5, r4]) (by simp [r5, r4, r3, r2, r1, s0, startState]) hrun_n
  have ha6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 7) (rIdx := 8)
    (base := keyOfNodeBase b vCap eCap) (idx := y) (val := x.keyOf y) (st := s_n)
    (by simp [s_n, r5]) (by simp [s_n, hvy])
    (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hy_mem
  have hst : Runs w p ω (.store (.reg 3) (.bin .eq (.reg 8) (.reg 2))) ⟨st_n.mem, r6, st_n.pos⟩ .normal ⟨M', r6, st_n.pos⟩ 5 :=
    runs_store_iff.mpr ⟨heap, ans, by simp [Expr.eval, r6, s_n, r5, r4, r3, r2, r1, s0, startState],
      by
        have hr8 : r6 8 = x.keyOf y := by simp [r6]
        have hr2 : r6 2 = keyY := by simp [r6, s_n, r5, r4, r3, r2, r1, s0, startState]
        by_cases hxy : x.keyOf y = keyY <;>
          simp [Expr.eval, hr8, hr2, BinOp.eval, ans, hxy, (by omega : 1 < 2 ^ w), (by omega : 0 < 2 ^ w)],
      rfl, rfl, rfl⟩
  have hret := runs_ret_reg_add1 (w := w) (p := p) (ω := ω) (st := ⟨M', r6, st_n.pos⟩) (r := 3) (v := heap)
    (by simp [r6, s_n, r5, r4, r3, r2, r1, s0, startState]) (by omega) (by omega)
  obtain ⟨hrep', hresp', hphi'⟩ := hupd ans (by simp only [ans]; split_ifs <;> omega)
  refine ⟨.returned (heap + 1), ⟨M', r6, st_n.pos⟩, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal ha5 (tour_runs_seq_normal hcall (tour_runs_seq_normal ha6 (tour_runs_seq_normal hst hret))))))),
    _, hrep', by simp [M', hans_eq], hresp', ?_⟩
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  simp only [TOUR_NEXT_AMORT, TOUR_QUERY_MUL] at hphi' ⊢; nlinarith

/-- Op 8 (`nextMarked [b, keyX, heap]`): verified amortized run theorem. -/
theorem tourOp_nextMarked_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX heap pos v : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hmemX : endOfKey keyX ∈ s.ord v)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpNextMarkedBody C.nextMark)
        (startState [b, keyX, heap] mem pos) o st' c ∧
      o.value = heap + 1 ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        st'.mem heap = (match tourNextMarked s (endOfKey keyX) with | none => 0 | some y => 1 + endKey y) ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hhdr := h.header
  obtain ⟨hkey_lt, hnx_pos, _, y, _, _, o_n, st_n, _, _, hrun_n, hvy, hy_info, hupd,
    t, hct, _, ht_map, hfind_y, hu_act⟩ :=
    tourNextReady_on_active (pos := pos) hLoc C C.markTests C.markTests_cost tourMark_readyLaw
      C.markDesc_body C.findFirstMark_body ω h hmemX hw hwide hfoot hzero hroom
  have hnx_t : x.nodeOf keyX ∈ t.toList := by
    obtain ⟨_, _, _, _, _, _, _, t0, _, hct0, _, _, hmem0⟩ := h.mem_compTree_of_active hmemX
    have ht0 : t0 = t := Option.some.inj (hct0.symm.trans hct)
    simpa [endKey_endOfKey', ht0] using hmem0
  have hnx_key : x.keyOf (x.nodeOf keyX) = keyX := h.nodeOf_keyOf keyX hkey_lt (by omega)
  have hft_nd : (fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v)).Nodup := (fullTour_spec h.valid.compat _).1
  have hfind_end : (((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find?
      (fun u => tourMarkRv (x.st.nodes u).val)).map (fun id => endOfKey (x.keyOf id)) =
      tourNextMarked s (endOfKey keyX) := by
    have hmap := find?_rotateNatList_map (f := fun id => endOfKey (x.keyOf id))
      (p := fun u => tourMarkRv (x.st.nodes u).val)
      (q := fun z => decide (z ∈ s.marked)) (ht_map.symm ▸ hft_nd) hnx_t fun u hu => by
        obtain ⟨h1, h2, w', hw'⟩ := hu_act u hu
        dsimp only [tourMarkRv]; rw [h.val_active u h1 h2 ⟨w', hw'⟩]
    rw [hmap, hnx_key, ht_map]
    simp only [tourNextMarked, h.valid.compat.forest, ↓reduceDIte, h.valid.compat.ordSrc_eq hmemX]
  unfold tourOpNextMarkedBody
  set s0 : State := startState [b, keyX, heap] mem pos
  set r1 := Function.update s0.regs 3 (nodeOfEndBase b vCap)
  set r2 := Function.update r1 4 (x.nodeOf keyX)
  set r3 := Function.update r2 5 (nodesBase b vCap eCap)
  set r4 := Function.update r3 6 (2 * eCap + 2)
  set r5 := Function.update r4 7 (keyOfNodeBase b vCap eCap)
  set s_n : State := { st_n with regs := Function.update r5 8 o_n.value }
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := x.nodeOf keyX) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (h.nodeOf_mem keyX hkey_lt).1
  have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
  have hcall := runs_call_regs4 8 5 4 6 2 (st := ⟨mem, r5, pos⟩) C.nextMark_body
    (by simp [r5, r4, r3]) (by simp [r5, r4, r3, r2]) (by simp [r5, r4]) (by simp [r5, r4, r3, r2, r1, s0, startState]) hrun_n
  cases hfp : ((rotateNatList (x.nodeOf keyX) t.toList).tail ++ [x.nodeOf keyX]).find? (fun u => tourMarkRv (x.st.nodes u).val) with
  | none =>
    rw [hfp] at hfind_y hfind_end; simp only [Option.getD_none, Option.map_none] at hfind_y hfind_end
    set M' := Function.update st_n.mem heap 0
    have hst : Runs w p ω (.store (.reg 2) (.const 0)) s_n .normal { s_n with mem := M' } 3 :=
      runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, s_n, r5, r4, r3, r2, r1, s0, startState],
        by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
    have hcond := tour_runs_cond_true (e := .bin .eq (.reg 8) (.const 0)) (v := 1) (st := s_n)
      (s₂ := .store (.reg 2) (.bin .add (.const 1) (.load (.bin .add (.reg 7) (.reg 8)))))
      (by simp [Expr.eval, s_n, hvy, ← hfind_y, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)])
      (by omega) hst
    have hret := runs_ret_reg_add1 (w := w) (p := p) (ω := ω) (st := { s_n with mem := M' }) (r := 2) (v := heap)
      (by simp [s_n, r5, r4, r3, r2, r1, s0, startState]) (by omega) (by omega)
    obtain ⟨hrep', hresp', hphi'⟩ := hupd 0 (by omega)
    refine ⟨.returned (heap + 1), { s_n with mem := M' }, _,
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
        (tour_runs_seq_normal ha5 (tour_runs_seq_normal hcall (tour_runs_seq_normal hcond hret)))))),
      rfl, _, hrep', by simp [M', ← hfind_end], hresp', ?_⟩
    have htl : 1 ≤ tourLog eCap := by simp [tourLog]
    simp only [Expr.size, TOUR_NEXT_AMORT, TOUR_QUERY_MUL] at hphi' ⊢; nlinarith
  | some z =>
    rw [hfp] at hfind_y hfind_end; simp only [Option.getD_some, Option.map_some] at hfind_y hfind_end
    have hz_t : z ∈ t.toList := by
      rcases List.mem_append.mp (List.mem_of_find?_eq_some hfp) with htl | hsg
      · exact mem_of_mem_rotateNatList hnx_t (List.mem_of_mem_tail htl)
      · simp only [List.mem_singleton] at hsg; exact hsg ▸ hnx_t
    have hy_nz : y ≠ 0 := by rw [← hfind_y]; exact Nat.ne_of_gt (hu_act z hz_t).1
    obtain ⟨hy1, hy2, hy_mem⟩ := hy_info hy_nz
    have h1ky_lt : 1 + x.keyOf y < 2 ^ w := by have := (h.keyOf_mem y hy1 hy2).2.1; omega
    set M' := Function.update st_n.mem heap (1 + x.keyOf y)
    have hst : Runs w p ω (.store (.reg 2) (.bin .add (.const 1) (.load (.bin .add (.reg 7) (.reg 8))))) s_n .normal { s_n with mem := M' } 8 :=
      runs_store_iff.mpr ⟨heap, 1 + x.keyOf y, by simp [Expr.eval, s_n, r5, r4, r3, r2, r1, s0, startState],
        by simp [Expr.eval, s_n, r5, hvy, BinOp.eval, hy_mem, h1ky_lt, (by omega : 1 < 2 ^ w),
          (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : keyOfNodeBase b vCap eCap + y < 2 ^ w)],
        rfl, rfl, rfl⟩
    have hcond := tour_runs_cond_false (e := .bin .eq (.reg 8) (.const 0)) (st := s_n)
      (s₁ := .store (.reg 2) (.const 0))
      (by simp [Expr.eval, s_n, hvy, hy_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]) hst
    have hret := runs_ret_reg_add1 (w := w) (p := p) (ω := ω) (st := { s_n with mem := M' }) (r := 2) (v := heap)
      (by simp [s_n, r5, r4, r3, r2, r1, s0, startState]) (by omega) (by omega)
    obtain ⟨hrep', hresp', hphi'⟩ := hupd (1 + x.keyOf y) h1ky_lt
    refine ⟨.returned (heap + 1), { s_n with mem := M' }, _,
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
        (tour_runs_seq_normal ha5 (tour_runs_seq_normal hcall (tour_runs_seq_normal hcond hret)))))),
      rfl, _, hrep', by simp [M', ← hfind_end, ← hfind_y, endKey_endOfKey'], hresp', ?_⟩
    have htl : 1 ≤ tourLog eCap := by simp [tourLog]
    simp only [Expr.size, TOUR_NEXT_AMORT, TOUR_QUERY_MUL] at hphi' ⊢; nlinarith

/-- Op 10 (`rootOf [b, keyX, heap]`): verified amortized run theorem. -/
theorem tourOp_rootOf_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX heap pos v : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hmemX : endOfKey keyX ∈ s.ord v)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpRootOfBody C.rootTagOf)
        (startState [b, keyX, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        st'.mem heap = s.rf.root (ordSrc s.ord (endOfKey keyX)) ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  have hord_le := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hhdr := h.header
  obtain ⟨_, hrR, hr_lt, hkey_lt, _, _, _, t, rest, hct, hperm, ht_map, hnx_t⟩ :=
    h.mem_compTree_of_active hmemX
  rw [endKey_endOfKey'] at hkey_lt hnx_t
  have hheap0 := h.heapOk (sp := 2) hfoot hzero (by omega) hwide
  have hf_perm := (h.forestInv.perm hperm).1
  obtain ⟨t', s', o_r, st_r, c_r, hrun_r, hvr, hn', hfr', hinv', _, _, _, hlist', hval', _, hcost_r⟩ :=
    tourRootTagOfBody_runs (fuel := 2 * eCap + 2) (pos := pos) C ω h.nodesAt hf_perm (h.valsOk hw)
      hnx_t (by have := h.numNodes_le; omega) (by omega) hheap0
  have hrt_eq : o_r.value = s.rf.root v + 1 := by
    rw [hvr]
    exact h.rootTag_foldr_eq_succ hrR (hperm.mem_iff.mpr (by simp)) ht_map (List.ne_nil_of_mem hnx_t)
  set M' := Function.update st_r.mem heap (s.rf.root v)
  have hN' : tourLayout.NodesAt M' (nodesBase b vCap eCap) x.numNodes s' :=
    NodesAt.congr tourLayout hn' fun a ha => by
      dsimp only [M']; exact Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2; omega) _ _
  have hagree : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → M' a = mem a :=
    fun a ha hnr => by
      rw [show M' a = st_r.mem a from by dsimp only [M']; exact Function.update_of_ne (by omega) _ _]
      exact hfr'.2 a ha hnr
  obtain ⟨hrep', hphi_ord, hphi_perm, hfoot_eq⟩ :=
    h.replace_compTree_same_list hLoc hfoot hrR hperm hct hlist' hN' hinv' hval' hagree
  set x' : TourConcrete R_ord.τ :=
    { x with st := s', trees := t' :: rest, compTree := Function.update x.compTree (s.rf.root v) (some t') }
  unfold tourOpRootOfBody
  set s0 : State := startState [b, keyX, heap] mem pos
  set r1 := Function.update s0.regs 3 (nodeOfEndBase b vCap)
  set r2 := Function.update r1 4 (x.nodeOf keyX)
  set r3 := Function.update r2 5 (nodesBase b vCap eCap)
  set r4 := Function.update r3 6 (2 * eCap + 2)
  set s_r : State := { st_r with regs := Function.update r4 7 o_r.value }
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := x.nodeOf keyX) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (h.nodeOf_mem keyX hkey_lt).1
  have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcall := runs_call_regs4 7 5 4 6 2 (st := ⟨mem, r4, pos⟩) C.rootTagOf_body
    (by simp [r4, r3]) (by simp [r4, r3, r2]) (by simp [r4]) (by simp [r4, r3, r2, r1, s0, startState]) hrun_r
  have hst : Runs w p ω (.store (.reg 2) (.bin .sub (.reg 7) (.const 1))) s_r .normal { s_r with mem := M' } 5 :=
    runs_store_iff.mpr ⟨heap, s.rf.root v, by simp [Expr.eval, s_r, r4, r3, r2, r1, s0, startState],
      by simp [Expr.eval, s_r, hrt_eq, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : s.rf.root v < 2 ^ w)], rfl, rfl, rfl⟩
  have hret := runs_ret_reg_add1 (w := w) (p := p) (ω := ω) (st := { s_r with mem := M' }) (r := 2) (v := heap)
    (by simp [s_r, r4, r3, r2, r1, s0, startState]) (by omega) (by omega)
  have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3 mem (heap + 1) b x' M' :=
    ⟨by omega, by omega, fun a ha => by dsimp only [M']; rw [Function.update_of_ne (by omega)]; exact hfr'.1 a (by omega),
      fun a ha hnf => hagree a ha fun hrec => hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; simp [nodesBase] at this; omega, (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).2⟩),
      fun a ha => Or.inl ((hfoot_eq a).mp ha)⟩
  refine ⟨.returned (heap + 1), { s_r with mem := M' }, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal hcall (tour_runs_seq_normal hst hret))))),
    x', hrep', by simp [M', h.valid.compat.ordSrc_eq hmemX], hresp, ?_⟩
  have hlog := tourLog_of_le h.numNodes_le
  have hlm := Nat.mul_le_mul_left TOUR_FIND_AMORT hlog
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  dsimp only [tourRep, tourPhi, x']
  rw [hphi_ord, hphi_perm]
  simp only [TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_QUERY_MUL] at hcost_r hlm ⊢
  omega

end MinCostFlow.SparseCore.Program
