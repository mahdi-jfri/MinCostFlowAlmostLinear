module

public import MinCostFlow.SparseCore.Program.TourOpsQuery
import Mathlib.Tactic

/-!
# Shared update helpers and mark-toggle operation (`setMark`, Op 7)

Provides shared WordRAM load/store/node-field helpers (`nodesAt_isOpen`, `nodesAt_isMarked`,
`nodesAt_rootTag`, `runs_store_reg_off_const`, `runs_assign_node_addr`, `runs_assign_reg_add1`,
`runs_assign_const`) and implements/verifies Op `7` (`setMark`) of `tourContract`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Amortized multiplier and shared WordRAM/node helpers -/

/-- Unified amortized per-`tourLog` multiplier covering Ops `1`, `2`, `3`, `7`. -/
def TOUR_FOREST_MUL : ℕ := 3000000

theorem nodesAt_isOpen {mem : ℕ → ℕ} {nb cap u : ℕ} {st : SplayState TourVal TourSum Unit}
    (hn : tourLayout.NodesAt mem nb cap st) (hu : u ≤ cap) :
    mem (nb + 17 * u + 9) = if (st.nodes u).val.isOpen then 1 else 0 := by
  simpa [nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using
    (hn u hu).2.2.2.2.2.2.1.2.2.2.1

theorem nodesAt_isMarked {mem : ℕ → ℕ} {nb cap u : ℕ} {st : SplayState TourVal TourSum Unit}
    (hn : tourLayout.NodesAt mem nb cap st) (hu : u ≤ cap) :
    mem (nb + 17 * u + 10) = if (st.nodes u).val.isMarked then 1 else 0 := by
  simpa [nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using
    (hn u hu).2.2.2.2.2.2.1.2.2.2.2.1

theorem nodesAt_rootTag {mem : ℕ → ℕ} {nb cap u : ℕ} {st : SplayState TourVal TourSum Unit}
    (hn : tourLayout.NodesAt mem nb cap st) (hu : u ≤ cap) :
    mem (nb + 17 * u + 11) = (st.nodes u).val.rootTag := by
  simpa [nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using
    (hn u hu).2.2.2.2.2.2.1.2.2.2.2.2

theorem runs_store_reg_off_const {w rBase rIdx base idx val : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (h1 : st.regs rBase = base) (h2 : st.regs rIdx = idx)
    (hsum : base + idx < 2 ^ w) (hval : val < 2 ^ w) :
    Runs w p ω (.store (.bin .add (.reg rBase) (.reg rIdx)) (.const val)) st .normal
      { st with mem := Function.update st.mem (base + idx) val } 5 :=
  runs_store_iff.mpr ⟨base + idx, val,
    by simp only [Expr.eval, h1, h2, BinOp.eval, hsum, ↓reduceIte],
    by simp only [Expr.eval, hval, ↓reduceIte], rfl, rfl, rfl⟩

theorem runs_assign_node_addr {w dst rNb rNode nb node : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (h1 : st.regs rNb = nb) (h2 : st.regs rNode = node)
    (h17 : 17 < 2 ^ w) (hmul : 17 * node < 2 ^ w) (hsum : nb + 17 * node < 2 ^ w) :
    Runs w p ω (.assign dst (.bin .add (.reg rNb) (.bin .mul (.const 17) (.reg rNode)))) st .normal
      { st with regs := Function.update st.regs dst (nb + 17 * node) } 6 :=
  runs_assign_iff.mpr ⟨nb + 17 * node,
    by simp only [Expr.eval, h1, h2, h17, BinOp.eval, hmul, hsum, ↓reduceIte], rfl, rfl, rfl⟩

theorem runs_assign_reg_add1 {w dst rSrc v : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h1 : st.regs rSrc = v) (h1w : 1 < 2 ^ w) (hv1 : v + 1 < 2 ^ w) :
    Runs w p ω (.assign dst (.bin .add (.reg rSrc) (.const 1))) st .normal
      { st with regs := Function.update st.regs dst (v + 1) } 4 :=
  runs_assign_iff.mpr ⟨v + 1,
    by simp only [Expr.eval, h1, h1w, BinOp.eval, hv1, ↓reduceIte], rfl, rfl, rfl⟩

theorem runs_assign_reg_sub1 {w dst rSrc v : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h1 : st.regs rSrc = v) (h1w : 1 < 2 ^ w) (hv : v - 1 < 2 ^ w) :
    Runs w p ω (.assign dst (.bin .sub (.reg rSrc) (.const 1))) st .normal
      { st with regs := Function.update st.regs dst (v - 1) } 4 :=
  runs_assign_iff.mpr ⟨v - 1,
    by simp only [Expr.eval, h1, h1w, BinOp.eval, hv, ↓reduceIte], rfl, rfl, rfl⟩

theorem runs_assign_const {w dst val : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hv : val < 2 ^ w) :
    Runs w p ω (.assign dst (.const val)) st .normal
      { st with regs := Function.update st.regs dst val } 2 :=
  runs_assign_iff.mpr ⟨val, by simp only [Expr.eval, hv, ↓reduceIte], rfl, rfl, rfl⟩

theorem rotateNatList_map_of_nodup' {L : List ℕ} {f : ℕ → End} {nx : ℕ}
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

theorem exists_edge_of_connected_ne {F : MGraph} {u v : ℕ}
    (hconn : F.Connected u v) (hne : u ≠ v) :
    ∃ x : End, x.1 ∈ F.E ∧ F.src x = u := by
  obtain ⟨P, hP⟩ := hconn
  cases hP with
  | nil => exact absurd rfl hne
  | cons he hs _ => exact ⟨_, he, hs⟩

/-! ## WordRAM body and verification for Op 7 (`setMark`) -/

/-- Op 7 (`setMark`): args `[b, keyX, flag, heap]`. Sets `isMarked` of open end `keyX` to `flag`,
returning `heap`. -/
def tourOpSetMarkBody (setValNodeProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 4 (.load (.bin .add (.reg 4) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 7 (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) ;;
  .assign 8 (.load (.bin .add (.reg 7) (.const 11))) ;;
  .assign 9 (.const 1) ;;
  .call 10 setValNodeProc [.reg 5, .reg 4, .reg 9, .reg 2, .reg 8, .reg 6, .reg 3] ;;
  .ret (.reg 3)

theorem tourOpSetMarkBody_noRand (svP : ℕ) : (tourOpSetMarkBody svP).NoRand := by
  simp [tourOpSetMarkBody, Stmt.NoRand]

private theorem tourValid_setMark {vCap eCap flag v : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hmem : x ∈ s.ord v) (hopen : x.1 ∉ s.rf.F.E) :
    TourValid vCap eCap (tourSetMark s x flag) := by
  unfold tourSetMark
  split_ifs
  · refine ⟨hv.ordWithin, hv.compat, hv.roots_sub, hv.verts_lt, hv.unique_root, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact ⟨⟨v, hmem⟩, hopen⟩
    · exact hv.marked_open z hz'
  · refine ⟨hv.ordWithin, hv.compat, hv.roots_sub, hv.verts_lt, hv.unique_root, fun z hz => ?_⟩
    exact hv.marked_open z (Finset.mem_of_mem_erase hz)

/-- Op 7 (`setMark [b, keyX, flag, heap]`): verified amortized run theorem. -/
theorem tourOp_setMark_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX flag heap pos v : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hmemX : endOfKey keyX ∈ s.ord v) (hopenX : (endOfKey keyX).1 ∉ s.rf.F.E) (hflag : flag ≤ 1)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 2 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpSetMarkBody C.setValNode)
        (startState [b, keyX, flag, heap] mem pos) o st' c ∧
      o.value = heap ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b (tourSetMark s (endOfKey keyX) flag) x' st'.mem ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_FOREST_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hhdr := h.header
  obtain ⟨_, hrR, _, hkey_lt, hnx_pos, hnx_le, hnx_key, t, rest, hct, hperm, ht_map, hnx_t⟩ :=
    h.mem_compTree_of_active hmemX
  rw [endKey_endOfKey'] at hkey_lt hnx_pos hnx_le hnx_key hnx_t
  set nx := x.nodeOf keyX
  have hnx_cap : nx ≤ x.numNodes := hnx_le
  have hAx : nodesBase b vCap eCap + 17 * nx + 17 ≤ heap := by
    have := (h.heapOk (sp := 2) hfoot hzero hroom hwide).addr_lt hnx_cap
    simpa [nodeAddr, tourLayout_stride] using this
  have hrt_mem : mem (nodesBase b vCap eCap + 17 * nx + 11) = (x.st.nodes nx).val.rootTag :=
    nodesAt_rootTag h.nodesAt hnx_cap
  have hrt_lt : (x.st.nodes nx).val.rootTag < 2 ^ w := (h.valsOk hw).2 nx hnx_cap
  have hf_perm := (h.forestInv.perm hperm).1
  obtain ⟨t', s', o_sv, st_sv, c_sv, hrun_sv, hn', hfr', hinv', _, _, _, hlist', hvalx', hvalne', _, hcost_sv⟩ :=
    tourSetValNodeBody_runs (isOpen := 1) (isMarked := flag) (rootTag := (x.st.nodes nx).val.rootTag)
      (fuel := 2 * eCap + 2) (pos := pos) C ω h.nodesAt hf_perm (h.valsOk hw)
      hnx_t hrt_lt (by have := h.numNodes_le; omega) (by omega) (h.heapOk (sp := 2) hfoot hzero hroom hwide)
  set s'Abs := tourSetMark s (endOfKey keyX) flag
  set x' : TourConcrete R_ord.τ :=
    { x with st := s', trees := t' :: rest, compTree := Function.update x.compTree (s.rf.root v) (some t') }
  have hval_old := h.val_active nx hnx_pos hnx_le ⟨v, by rw [hnx_key]; exact hmemX⟩
  have hrt_eq_old : (x.st.nodes nx).val.rootTag = tourRootTagVal s (endOfKey keyX) := by
    rw [hval_old, hnx_key]
  have hs'_ord : s'Abs.ord = s.ord := by unfold s'Abs tourSetMark; split_ifs <;> rfl
  have hs'_rf : s'Abs.rf = s.rf := by unfold s'Abs tourSetMark; split_ifs <;> rfl
  have hs'_F : s'Abs.rf.F = s.rf.F := congrArg RootedForest.F hs'_rf
  have hs'_rt : ∀ z, tourRootTagVal s'Abs z = tourRootTagVal s z := fun z => by
    unfold tourRootTagVal; rw [hs'_ord, hs'_rf]
  have hvalid' : TourValid vCap eCap s'Abs := tourValid_setMark h.valid hmemX hopenX
  have hpre_eq : ∀ a < nodesBase b vCap eCap, st_sv.mem a = mem a := fun a ha =>
    hfr'.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha)
  have hord_eq : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → mem a = st_sv.mem a := fun a ha =>
    (hfr'.2 a (hfoot a (Or.inr ha)) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (h.ordFootGe a ha))).symm
  have hOrd := hLoc (ordHandleOf b vCap eCap) s.ord x.ordX mem st_sv.mem hord_eq
  have hhdr' : TourHeaderAt vCap eCap b x.numNodes st_sv.mem := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, st_sv.mem (b + k) = mem (b + k) := fun k hk =>
      hpre_eq (b + k) (by simp [nodesBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  have ht_pos : t.toList ≠ [] := List.ne_nil_of_mem hnx_t
  have ht_not_rest : t ∉ rest := by
    intro hm
    have hnd := hf_perm.nodupAll
    rw [List.flatMap_cons, List.nodup_append] at hnd
    exact hnd.2.2 nx hnx_t nx (List.mem_flatMap.mpr ⟨t, hm, hnx_t⟩) rfl
  have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ s.rf.root v → x.compTree r' ≠ some t := by
    intro r' hr' hne hcr'
    have hft' : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := by
      intro hnil; have := h.comp_none r' hr' hnil; rw [hcr'] at this; simp at this
    obtain ⟨tr', hctr', _, htr'_map⟩ := h.comp_some r' hr' hft'
    have hteq : tr' = t := Option.some.inj (hctr'.symm.trans hcr'); subst hteq
    have he1 : endOfKey (x.keyOf nx) ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) := by
      rw [← ht_map]; exact List.mem_map_of_mem hnx_t
    have he2 : endOfKey (x.keyOf nx) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
      rw [← htr'_map]; exact List.mem_map_of_mem hnx_t
    obtain ⟨v1, hv1, hc1⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he1
    obtain ⟨v2, hv2, hc2⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he2
    have hv12 : v1 = v2 := h.valid.compat.unique v1 v2 _ hv1 hv2; subst hv12
    have hvF := h.valid.compat.vert v1 (List.ne_nil_of_mem hv1)
    exact hne ((h.valid.root_eq_of_mem hvF hr' (connected_symm hc2)).symm.trans
      (h.valid.root_eq_of_mem hvF hrR (connected_symm hc1)))
  have hrep' : TourRepAt R_ord vCap eCap b s'Abs x' st_sv.mem :=
    { valid := hvalid'
      ordRep := by rw [hs'_ord]; exact hOrd.1 h.ordRep
      ordFootGe := h.ordFootGe
      header := hhdr'
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hpre_eq _ (by simp [nodeOfEndBase, nodesBase]; omega)]; exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun u h1 h2 => by
        dsimp only [x'] at h2; have hle := h.numNodes_le
        rw [hpre_eq _ (by simp [keyOfNodeBase, nodesBase]; omega)]; exact h.keyOf_mem u h1 h2
      firstEnd_mem := fun u hu => by
        rw [hs'_ord, hpre_eq _ (by simp [firstEndBase, nodesBase]; omega)]; exact h.firstEnd_mem u hu
      isRoot_mem := fun u hu => by
        rw [hs'_rf, hpre_eq _ (by simp [isRootBase, nodesBase]; omega)]; exact h.isRoot_mem u hu
      active_end := fun u hu e he => by
        rw [hs'_ord] at he
        have he_lt : endKey e < 2 * eCap := by
          have := h.valid.ordWithin.2.2 u e he; simp only [endKey]; cases e.2 <;> simp <;> omega
        rw [hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega)]; exact h.active_end u hu e he
      inactive_owner := fun k hk hno => by
        rw [hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega)]
        exact h.inactive_owner k hk (fun u => hs'_ord ▸ hno u)
      slot_bij := h.slot_bij
      slotOf_mem := fun v hv => by
        rw [hpre_eq _ (by simp [slotOfVertBase, nodesBase]; omega)]; exact h.slotOf_mem v hv
      vertOf_mem := fun sl hsl => by
        rw [hpre_eq _ (by simp [vertOfSlotBase, nodesBase]; omega)]; exact h.vertOf_mem sl hsl
      markArr_zero := fun k hk => by
        rw [hpre_eq _ (by simp [markArrBase, nodesBase]; omega)]; exact h.markArr_zero k hk
      nodesAt := hn'
      forestInv := hinv'
      nodes_exact := fun u => by
        have h1 : u ∈ (t' :: rest).flatMap AuxTree.toList ↔ u ∈ (t :: rest).flatMap AuxTree.toList := by
          simp [List.flatMap_cons, hlist']
        have h2 : u ∈ (t :: rest).flatMap AuxTree.toList ↔ u ∈ x.trees.flatMap AuxTree.toList := by
          simp only [List.mem_flatMap]
          exact ⟨fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mpr ha, hu⟩,
            fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mp ha, hu⟩⟩
        exact h1.trans (h2.trans (h.nodes_exact u))
      comp_none := fun r' hr' hnil => by
        rw [hs'_rf] at hr'
        have hft_eq : fullTour s'Abs.ord s'Abs.rf.F hvalid'.compat.forest r' =
            fullTour s.ord s.rf.F h.valid.compat.forest r' := by
          congr 1
        rw [hft_eq] at hnil
        have hne : r' ≠ s.rf.root v := fun heq => by
          subst heq; have := List.map_eq_nil_iff.mp (ht_map.trans hnil); exact ht_pos this
        simp only [x', Function.update_of_ne hne]
        exact h.comp_none r' hr' hnil
      comp_some := fun r' hr' hne_ft => by
        rw [hs'_rf] at hr'
        have hft_eq : fullTour s'Abs.ord s'Abs.rf.F hvalid'.compat.forest r' =
            fullTour s.ord s.rf.F h.valid.compat.forest r' := by congr 1
        rw [hft_eq] at hne_ft ⊢
        by_cases hrr' : r' = s.rf.root v
        · subst hrr'
          exact ⟨t', by simp [x'], by simp [x'], by rw [hlist']; exact ht_map⟩
        · obtain ⟨tr', hctr', htr'_mem, htr'_map⟩ := h.comp_some r' hr' hne_ft
          have htr'_ne : tr' ≠ t := fun heq => hcomp_inj r' hr' hrr' (heq ▸ hctr')
          have htr'_rest : tr' ∈ rest := (List.mem_cons.mp (hperm.mem_iff.mp htr'_mem)).resolve_left htr'_ne
          exact ⟨tr', by simp [x', Function.update_of_ne hrr', hctr'], by simp [x', htr'_rest], htr'_map⟩
      tree_class := fun tr htr => by
        simp only [x', List.mem_cons] at htr
        rcases htr with rfl | hrest
        · exact Or.inl ⟨s.rf.root v, hs'_rf ▸ hrR, by simp [x']⟩
        · have htr_mem : tr ∈ x.trees := hperm.mem_iff.mpr (by simp [hrest])
          rcases h.tree_class tr htr_mem with ⟨r', hr', hcr'⟩ | ⟨u, rfl, hno⟩
          · have hne : r' ≠ s.rf.root v := fun heq => by
              subst heq; exact ht_not_rest ((Option.some.inj (hcr'.symm.trans hct)) ▸ hrest)
            exact Or.inl ⟨r', hs'_rf ▸ hr', by simp [x', Function.update_of_ne hne, hcr']⟩
          · exact Or.inr ⟨u, rfl, fun w' => hs'_ord ▸ hno w'⟩
      inactive_single := fun u h1 h2 hno => by
        have hno' : ∀ w', endOfKey (x.keyOf u) ∉ s.ord w' := fun w' => hs'_ord ▸ hno w'
        have hmem := h.inactive_single u h1 h2 hno'
        have hne : AuxTree.node u .leaf .leaf ≠ t := fun heq => by
          have he : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) := by
            rw [← ht_map, ← heq]; simp [AuxTree.toList]
          obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he
          exact hno' w' hw'
        have hrest : AuxTree.node u .leaf .leaf ∈ rest :=
          (List.mem_cons.mp (hperm.mem_iff.mp hmem)).resolve_left hne
        simp [x', hrest]
      val_active := fun u h1 h2 hact => by
        dsimp only [x'] at h2 ⊢
        have hact' : ∃ w', endOfKey (x.keyOf u) ∈ s.ord w' := by rwa [hs'_ord] at hact
        by_cases hux : u = nx
        · subst hux
          rw [hvalx', hnx_key, hs'_rt, hs'_rf, hrt_eq_old]
          have hdec_open : decide ((endOfKey keyX).1 ∉ s.rf.F.E) = true := decide_eq_true hopenX
          have hdec_mark : decide (endOfKey keyX ∈ s'Abs.marked) = decide (0 < flag) := by
            unfold s'Abs tourSetMark
            split_ifs with hf1
            · subst hf1; simp
            · have hf0 : flag = 0 := by omega
              subst hf0; simp
          simp [hdec_open, hdec_mark]
        · rw [hvalne' u (by have := h.numNodes_le; omega) hux, h.val_active u h1 h2 hact', hs'_rf, hs'_rt]
          have hkne : endOfKey (x.keyOf u) ≠ endOfKey keyX := by
            intro heq
            have hk : x.keyOf u = keyX := by rw [← endKey_endOfKey' (x.keyOf u), heq, endKey_endOfKey']
            have := (h.keyOf_mem u h1 h2).2.2
            rw [hk] at this; exact hux this.symm
          have hmk : decide (endOfKey (x.keyOf u) ∈ s'Abs.marked) = decide (endOfKey (x.keyOf u) ∈ s.marked) := by
            unfold s'Abs tourSetMark
            split_ifs <;> simp [hkne]
          rw [hmk]
      val_inactive_rt := fun u h1 h2 hno => by
        have hno' : ∀ w', endOfKey (x.keyOf u) ∉ s.ord w' := fun w' => hs'_ord ▸ hno w'
        have hux : u ≠ nx := fun heq => by subst heq; rw [hnx_key] at hno'; exact hno' v hmemX
        dsimp only [x'] at h2 ⊢
        rw [hvalne' u (by have := h.numNodes_le; omega) hux]
        exact h.val_inactive_rt u h1 h2 hno'
      val_unused_rt := fun u hu hcond => by
        have hux : u ≠ nx := by dsimp only [x'] at hcond; omega
        rw [hvalne' u hu hux]; exact h.val_unused_rt u hu hcond }
  unfold tourOpSetMarkBody
  set s0 : State := startState [b, keyX, flag, heap] mem pos
  set r1 := Function.update s0.regs 4 (nodeOfEndBase b vCap)
  set r2 := Function.update r1 4 nx
  set r3 := Function.update r2 5 (nodesBase b vCap eCap)
  set r4 := Function.update r3 6 (2 * eCap + 2)
  set r5 := Function.update r4 7 (nodesBase b vCap eCap + 17 * nx)
  set r6 := Function.update r5 8 (x.st.nodes nx).val.rootTag
  set r7 := Function.update r6 9 1
  set s_sv : State := { st_sv with regs := Function.update r7 10 o_sv.value }
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 4) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := nx) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (h.nodeOf_mem keyX hkey_lt).1
  have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ha5 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 7) (rNb := 5) (rNode := 4)
    (nb := nodesBase b vCap eCap) (node := nx) (st := ⟨mem, r4, pos⟩)
    (by simp [r4, r3]) (by simp [r4, r3, r2]) (by omega) (by omega) (by omega)
  have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 7) (off := 11)
    (b := nodesBase b vCap eCap + 17 * nx) (val := (x.st.nodes nx).val.rootTag) (st := ⟨mem, r5, pos⟩)
    (by simp [r5]) (by omega) (by omega) hrt_mem
  have ha7 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 9) (val := 1) (st := ⟨mem, r6, pos⟩) (by omega)
  have hcall := tour_runs_call_of (r := 10) (args := [.reg 5, .reg 4, .reg 9, .reg 2, .reg 8, .reg 6, .reg 3])
    (st := ⟨mem, r7, pos⟩) C.setValNode_body
    (by simp [evalArgs, Expr.eval, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun_sv
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_sv) (r := 3) (v := heap)
    (by simp [s_sv, r7, r6, r5, r4, r3, r2, r1, s0, startState])
  have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem heap b x' st_sv.mem :=
    ⟨le_refl heap, by omega, hfr'.1,
      fun a ha hnf => hfr'.2 a ha fun hrec => hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; simp [nodesBase] at this; omega, (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).2⟩),
      fun a ha => Or.inl ha⟩
  refine ⟨.returned heap, s_sv, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal hcall hret))))))),
    rfl, x', hrep', hresp, ?_⟩
  have hlog := tourLog_of_le h.numNodes_le
  have hlm := Nat.mul_le_mul_left TOUR_FIND_AMORT hlog
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  dsimp only [tourRep, tourPhi, x']
  rw [← hOrd.2, forestPhi_perm hperm]
  simp only [argsSize, Expr.size, TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_FOREST_MUL] at hcost_sv hlm ⊢
  omega

end MinCostFlow.SparseCore.Program
