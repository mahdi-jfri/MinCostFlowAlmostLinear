module

public import MinCostFlow.SparseCore.Program.TourOpsMark
import Mathlib.Tactic

/-!
# Root-change operation (`changeRoot`, Op 3)

Implements and verifies Op `3` (`changeRoot [b, oldRoot, newRoot, heap]`) of `tourContract`,
moving a component root from `oldRoot` to `newRoot` in `O(tourLog eCap)` amortized time with `2`
words of heap headroom.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Op 3 (`changeRoot`): args `[b, oldRoot, newRoot, heap]`. Moves component root from `oldRoot`
to `newRoot`, updating `isRoot`, `rootTag`, and rotating `firstEnd[newRoot]` to front. -/
def tourOpChangeRootBody (setValNodeProc rotateFrontProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2)) (.ret (.reg 3))
    (.assign 4 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
     .store (.bin .add (.reg 4) (.reg 1)) (.const 0) ;;
     .store (.bin .add (.reg 4) (.reg 2)) (.const 1) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
     .assign 6 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .assign 7 (.load (.bin .add (.reg 5) (.reg 2))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
     .assign 10 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 6))) ;;
     .assign 11 (.load (.bin .add (.reg 10) (.const 9))) ;;
     .assign 12 (.load (.bin .add (.reg 10) (.const 10))) ;;
     .assign 13 (.const 0) ;;
     .call 14 setValNodeProc [.reg 8, .reg 6, .reg 11, .reg 12, .reg 13, .reg 9, .reg 3] ;;
     .assign 10 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 7))) ;;
     .assign 11 (.load (.bin .add (.reg 10) (.const 9))) ;;
     .assign 12 (.load (.bin .add (.reg 10) (.const 10))) ;;
     .assign 13 (.bin .add (.reg 2) (.const 1)) ;;
     .call 14 setValNodeProc [.reg 8, .reg 7, .reg 11, .reg 12, .reg 13, .reg 9, .reg 3] ;;
     .call 14 rotateFrontProc [.reg 8, .reg 7, .reg 9, .reg 3] ;;
     .ret (.reg 3))

theorem tourOpChangeRootBody_noRand (svP rfP : ℕ) : (tourOpChangeRootBody svP rfP).NoRand := by
  simp [tourOpChangeRootBody, Stmt.NoRand]

private theorem tourValid_changeRoot {vCap eCap oldRoot newRoot : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hold : oldRoot ∈ s.rf.R) (hnewV : newRoot ∈ s.rf.F.V)
    (hconn : s.rf.F.Connected oldRoot newRoot) :
    TourValid vCap eCap (tourChangeRoot s oldRoot newRoot) := by
  refine ⟨hv.ordWithin, hv.compat, ?_, hv.verts_lt, ?_, hv.marked_open⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exact hnewV
    · exact hv.roots_sub (Finset.mem_of_mem_erase hr')
  · intro v hvF
    obtain ⟨r, ⟨hrR, hvr⟩, huniq⟩ := hv.unique_root v hvF
    by_cases hro : r = oldRoot
    · subst hro
      refine ⟨newRoot, ⟨Finset.mem_insert_self _ _, connected_trans hvr hconn⟩, fun r' ⟨hr'R, hvr'⟩ => ?_⟩
      rcases Finset.mem_insert.mp hr'R with rfl | hr'e
      · rfl
      · exfalso
        have h1 := huniq r' ⟨Finset.mem_of_mem_erase hr'e, hvr'⟩
        exact (Finset.mem_erase.mp hr'e).1 h1
    · refine ⟨r, ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hro, hrR⟩), hvr⟩, fun r' ⟨hr'R, hvr'⟩ => ?_⟩
      rcases Finset.mem_insert.mp hr'R with rfl | hr'e
      · exfalso
        exact hro (huniq oldRoot ⟨hold, connected_trans hvr' (connected_symm hconn)⟩).symm
      · exact huniq r' ⟨Finset.mem_of_mem_erase hr'e, hvr'⟩

/-- Op 3 (`changeRoot [b, oldRoot, newRoot, heap]`): verified amortized run theorem. -/
theorem tourOp_changeRoot_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b oldRoot newRoot heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hold : oldRoot ∈ s.rf.R) (hnewLt : newRoot < vCap) (hnewV : newRoot ∈ s.rf.F.V)
    (hconn : s.rf.F.Connected oldRoot newRoot)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 2 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpChangeRootBody C.setValNode C.rotateFront)
        (startState [b, oldRoot, newRoot, heap] mem pos) o st' c ∧
      o.value = heap ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b (tourChangeRoot s oldRoot newRoot) x' st'.mem ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_FOREST_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have holdLt : oldRoot < vCap := h.valid.verts_lt oldRoot (h.valid.roots_sub hold)
  set s0 : State := startState [b, oldRoot, newRoot, heap] mem pos
  unfold tourOpChangeRootBody
  by_cases hsame : oldRoot = newRoot
  · subst hsame
    have hs_eq : tourChangeRoot s oldRoot oldRoot = s := by
      cases s with | mk ord rf mk =>
        cases rf with | mk F R =>
          simp [tourChangeRoot, Finset.insert_erase hold]
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s0) (r := 3) (v := heap) (by simp [s0, startState])
    refine ⟨.returned heap, s0, _,
      tour_runs_cond_true (e := .bin .eq (.reg 1) (.reg 2)) (v := 1) (st := s0)
        (by simp [Expr.eval, s0, startState, BinOp.eval, (by omega : 1 < 2 ^ w)]) (by omega) hret,
      rfl, x, hs_eq.symm ▸ h,
      ⟨le_refl heap, Nat.le_add_right heap 2, hzero, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩, ?_⟩
    have htl : 1 ≤ tourLog eCap := by simp [tourLog]
    have hlm := Nat.mul_le_mul_left TOUR_FOREST_MUL htl
    simp only [Expr.size, TOUR_FOREST_MUL, s0, startState] at hlm ⊢; omega
  · have hnewNotR : newRoot ∉ s.rf.R := fun hnr => by
      have h1 := h.valid.root_eq_of_mem hnewV hnr (connected_refl _ newRoot)
      have h2 := h.valid.root_eq_of_mem hnewV hold (connected_symm hconn)
      exact hsame (h2.symm.trans h1)
    obtain ⟨eO, heOE, heOS⟩ := exists_edge_of_connected_ne hconn hsame
    obtain ⟨eN, heNE, heNS⟩ := exists_edge_of_connected_ne (connected_symm hconn) (Ne.symm hsame)
    have hordOld_ne : s.ord oldRoot ≠ [] :=
      List.ne_nil_of_mem (heOS ▸ h.valid.compat.mem_ord_of_forest heOE)
    have hordNew_ne : s.ord newRoot ≠ [] :=
      List.ne_nil_of_mem (heNS ▸ h.valid.compat.mem_ord_of_forest heNE)
    obtain ⟨aO, haO⟩ : ∃ aO, (s.ord oldRoot).head? = some aO :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord oldRoot <;> simp_all)
    obtain ⟨aN, haN⟩ : ∃ aN, (s.ord newRoot).head? = some aN :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord newRoot <;> simp_all)
    have haO_mem : aO ∈ s.ord oldRoot := List.mem_of_head? haO
    have haN_mem : aN ∈ s.ord newRoot := List.mem_of_head? haN
    have hroot_old : s.rf.root oldRoot = oldRoot := h.valid.root_eq_of_mem (h.valid.roots_sub hold) hold (connected_refl _ _)
    have hroot_new : s.rf.root newRoot = oldRoot := h.valid.root_eq_of_mem hnewV hold (connected_symm hconn)
    obtain ⟨_, _, _, _, hfeO_pos, hfeO_le, hfeO_key, t, rest, hct, hperm, ht_map, hfeO_t⟩ :=
      h.mem_compTree_of_active haO_mem
    rw [hroot_old] at hct ht_map
    obtain ⟨_, _, _, _, hfeN_pos, hfeN_le, hfeN_key, tN, _, hctN, _, _, hfeN_t⟩ :=
      h.mem_compTree_of_active haN_mem
    rw [hroot_new] at hctN
    have htN_eq : tN = t := Option.some.inj (hctN.symm.trans hct)
    rw [htN_eq] at hfeN_t
    set feO := x.nodeOf (endKey aO)
    set feN := x.nodeOf (endKey aN)
    have hfeO_ne_feN : feO ≠ feN := fun heq => by
      have haeq : aO = aN := by
        have := congrArg (fun u => endOfKey (x.keyOf u)) heq
        simpa [hfeO_key, hfeN_key, endOfKey_endKey'] using this
      exact hsame (h.valid.compat.unique oldRoot newRoot aO haO_mem (haeq ▸ haN_mem))
    have hfeO_cap : feO ≤ x.numNodes := hfeO_le
    have hfeN_cap : feN ≤ x.numNodes := hfeN_le
    have hfeO_first : mem (firstEndBase b + oldRoot) = feO := by rw [h.firstEnd_mem oldRoot holdLt, haO]
    have hfeN_first : mem (firstEndBase b + newRoot) = feN := by rw [h.firstEnd_mem newRoot hnewLt, haN]
    set mem1 := Function.update mem (isRootBase b vCap + oldRoot) 0
    set mem2 := Function.update mem1 (isRootBase b vCap + newRoot) 1
    have hmem2_eq : ∀ a, a ≠ isRootBase b vCap + oldRoot → a ≠ isRootBase b vCap + newRoot → mem2 a = mem a :=
      fun a h1 h2 => by simp only [mem2, mem1, Function.update_of_ne h2, Function.update_of_ne h1]
    have hmem2_inRec : ∀ a, tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → mem2 a = mem a :=
      fun a ha => hmem2_eq a
        (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega)
        (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega)
    have hnodes2 : tourLayout.NodesAt mem2 (nodesBase b vCap eCap) x.numNodes x.st :=
      NodesAt.congr tourLayout h.nodesAt hmem2_inRec
    have hzero2 : ZeroFrom mem2 heap := fun a ha => by
      rw [hmem2_eq a (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
        (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
      exact hzero a ha
    have hheap2 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 mem2 :=
      ⟨(h.heapOk (sp := 2) hfoot hzero hroom hwide).rec_le, hroom, hzero2, hwide⟩
    have hf_perm := (h.forestInv.perm hperm).1
    set opO := if (x.st.nodes feO).val.isOpen then 1 else 0
    set mkO := if (x.st.nodes feO).val.isMarked then 1 else 0
    have hmem2_opO : mem2 (nodesBase b vCap eCap + 17 * feO + 9) = opO := nodesAt_isOpen hnodes2 hfeO_cap
    have hmem2_mkO : mem2 (nodesBase b vCap eCap + 17 * feO + 10) = mkO := nodesAt_isMarked hnodes2 hfeO_cap
    obtain ⟨t₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, _, _, hlist₁, hvalO₁, hvalne₁, _, hcost₁⟩ :=
      tourSetValNodeBody_runs (isOpen := opO) (isMarked := mkO) (rootTag := 0)
        (fuel := 2 * eCap + 2) (pos := pos) C ω hnodes2 hf_perm (h.valsOk hw)
        hfeO_t (by omega) (by have := h.numNodes_le; omega) (by omega) hheap2
    set opN := if (x.st.nodes feN).val.isOpen then 1 else 0
    set mkN := if (x.st.nodes feN).val.isMarked then 1 else 0
    have hvalN_eq : (s₁.nodes feN).val = (x.st.nodes feN).val := hvalne₁ feN hfeN_cap hfeO_ne_feN.symm
    have hst1_opN : st₁.mem (nodesBase b vCap eCap + 17 * feN + 9) = opN := by
      rw [nodesAt_isOpen hn₁ hfeN_cap, hvalN_eq]
    have hst1_mkN : st₁.mem (nodesBase b vCap eCap + 17 * feN + 10) = mkN := by
      rw [nodesAt_isMarked hn₁ hfeN_cap, hvalN_eq]
    have hfeN_t1 : feN ∈ t₁.toList := by rw [hlist₁]; exact hfeN_t
    have hheap_st1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 st₁.mem :=
      ⟨hheap2.rec_le, hroom, hfr₁.1, hwide⟩
    obtain ⟨t₂, s₂, o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, _, _, hlist₂, hvalN₂, hvalne₂, _, hcost₂⟩ :=
      tourSetValNodeBody_runs (isOpen := opN) (isMarked := mkN) (rootTag := newRoot + 1)
        (fuel := 2 * eCap + 2) (pos := st₁.pos) C ω hn₁ hinv₁ hvals₁
        hfeN_t1 (by omega) (by have := h.numNodes_le; omega) (by omega) hheap_st1
    have hfeN_t2 : feN ∈ t₂.toList := by rw [hlist₂]; exact hfeN_t1
    have hheap_st2 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 st₂.mem :=
      ⟨hheap2.rec_le, hroom, hfr₂.1, hwide⟩
    obtain ⟨t₃, s₃, o₃, st₃, c₃, hrun₃, _, hn₃, hfr₃, hinv₃, _, _, hrot₃, hval₃, _, hcost₃⟩ :=
      tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₂.pos) C.toTourSplayOpsProcs ω
        hn₂ hinv₂ hvals₂ hfeN_t2 (by have := h.numNodes_le; omega) (by omega) hheap_st2
    have hvalid' : TourValid vCap eCap (tourChangeRoot s oldRoot newRoot) :=
      tourValid_changeRoot h.valid hold hnewV hconn
    have ht3_map : t₃.toList.map (fun id => endOfKey (x.keyOf id)) =
        fullTour s.ord s.rf.F h.valid.compat.forest newRoot := by
      have ht2_eq : t₂.toList = t.toList := hlist₂.trans hlist₁
      rw [hrot₃, ht2_eq]
      have hnd_t : (t.toList.map (fun id => endOfKey (x.keyOf id))).Nodup :=
        ht_map.symm ▸ (fullTour_spec h.valid.compat oldRoot).1
      rw [rotateNatList_map_of_nodup' hnd_t hfeN_t, hfeN_key, endOfKey_endKey', ht_map]
      exact rotateToList_fullTour_of_isRotated h.valid.compat haN
        (fullTour_isRotated_of_connected h.valid.compat hconn)
    set s'Abs := tourChangeRoot s oldRoot newRoot
    let ct' := Function.update (Function.update x.compTree oldRoot none) newRoot (some t₃)
    set x' : TourConcrete R_ord.τ := { x with st := s₃, trees := t₃ :: rest, compTree := ct' }
    have hfr_all : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem2 st₃.mem :=
      hfr₁.trans (hfr₂.trans hfr₃)
    have hpre_eq : ∀ a < nodesBase b vCap eCap, st₃.mem a = mem2 a := fun a ha =>
      hfr_all.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
        (not_inRecords_of_lt_nodesBase ha)
    have hord_eq : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → mem a = st₃.mem a := fun a ha => by
      have ha_ge := h.ordFootGe a ha
      rw [hfr_all.2 a (hfoot a (Or.inr ha)) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le ha_ge)]
      exact (hmem2_eq a (by simp [isRootBase, ordHandleOf, tourFixedSize] at ha_ge ⊢; omega)
        (by simp [isRootBase, ordHandleOf, tourFixedSize] at ha_ge ⊢; omega)).symm
    have hOrd := hLoc (ordHandleOf b vCap eCap) s.ord x.ordX mem st₃.mem hord_eq
    have hhdr' : TourHeaderAt vCap eCap b x.numNodes st₃.mem := by
      rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
      have hf : ∀ k < 16, st₃.mem (b + k) = mem (b + k) := fun k hk => by
        rw [hpre_eq (b + k) (by simp [nodesBase]; omega)]
        exact hmem2_eq (b + k) (by simp [isRootBase]; omega) (by simp [isRootBase]; omega)
      exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
        by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
        by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
        by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
        by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
        by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
        by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
        by rw [hf _ (by decide)]; exact h14⟩
    have ht_not_rest : t ∉ rest := by
      intro hm
      have hnd := hf_perm.nodupAll
      rw [List.flatMap_cons, List.nodup_append] at hnd
      exact hnd.2.2 feO hfeO_t feO (List.mem_flatMap.mpr ⟨t, hm, hfeO_t⟩) rfl
    have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ oldRoot → x.compTree r' ≠ some t := by
      intro r' hr' hne hcr'
      have hft' : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := by
        intro hnil; have := h.comp_none r' hr' hnil; rw [hcr'] at this; simp at this
      obtain ⟨tr', hctr', _, htr'_map⟩ := h.comp_some r' hr' hft'
      have hteq : tr' = t := Option.some.inj (hctr'.symm.trans hcr'); subst hteq
      have he1 : endOfKey (x.keyOf feO) ∈ fullTour s.ord s.rf.F h.valid.compat.forest oldRoot := by
        rw [← ht_map]; exact List.mem_map_of_mem hfeO_t
      have he2 : endOfKey (x.keyOf feO) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
        rw [← htr'_map]; exact List.mem_map_of_mem hfeO_t
      obtain ⟨v1, hv1, hc1⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he1
      obtain ⟨v2, hv2, hc2⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he2
      have hv12 : v1 = v2 := h.valid.compat.unique v1 v2 _ hv1 hv2; subst hv12
      have hvF := h.valid.compat.vert v1 (List.ne_nil_of_mem hv1)
      exact hne ((h.valid.root_eq_of_mem hvF hr' (connected_symm hc2)).symm.trans
        (h.valid.root_eq_of_mem hvF hold (connected_symm hc1)))
    have ht3_perm : t₃.toList.Perm t.toList := by
      rw [hrot₃, hlist₂, hlist₁]
      unfold rotateNatList; simp only [hfeN_t, ↓reduceIte]
      exact List.perm_append_comm.trans (by rw [List.take_append_drop])
    have hrep' : TourRepAt R_ord vCap eCap b s'Abs x' st₃.mem :=
      { valid := hvalid'
        ordRep := hOrd.1 h.ordRep
        ordFootGe := h.ordFootGe
        header := hhdr'
        numNodes_le := h.numNodes_le
        nodeOf_mem := fun k hk => by
          rw [hpre_eq _ (by simp [nodeOfEndBase, nodesBase]; omega),
            hmem2_eq _ (by simp [nodeOfEndBase, isRootBase]; omega) (by simp [nodeOfEndBase, isRootBase]; omega)]
          exact h.nodeOf_mem k hk
        nodeOf_keyOf := h.nodeOf_keyOf
        keyOf_mem := fun u h1 h2 => by
          dsimp only [x'] at h2; have hle := h.numNodes_le
          rw [hpre_eq _ (by simp [keyOfNodeBase, nodesBase]; omega),
            hmem2_eq _ (by simp [keyOfNodeBase, isRootBase]; omega) (by simp [keyOfNodeBase, isRootBase]; omega)]
          exact h.keyOf_mem u h1 h2
        firstEnd_mem := fun u hu => by
          rw [hpre_eq _ (by simp [firstEndBase, nodesBase]; omega),
            hmem2_eq _ (by simp [firstEndBase, isRootBase]; omega) (by simp [firstEndBase, isRootBase]; omega)]
          exact h.firstEnd_mem u hu
        isRoot_mem := fun u hu => by
          rw [hpre_eq _ (by simp [isRootBase, nodesBase]; omega)]
          by_cases hun : u = newRoot
          · subst hun; simp [mem2, s'Abs, tourChangeRoot]
          · by_cases huo : u = oldRoot
            · subst u
              simp [mem2, mem1, s'Abs, tourChangeRoot, hsame]
            · rw [hmem2_eq _ (by omega) (by omega), h.isRoot_mem u hu]
              simp [s'Abs, tourChangeRoot, hun, huo]
        active_end := fun u hu e he => by
          have he_lt : endKey e < 2 * eCap := by
            have := h.valid.ordWithin.2.2 u e he; simp only [endKey]; cases e.2 <;> simp <;> omega
          rw [hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega),
            hmem2_eq _ (by simp [endOwnerBase, isRootBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)]
          exact h.active_end u hu e he
        inactive_owner := fun k hk hno => by
          rw [hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega),
            hmem2_eq _ (by simp [endOwnerBase, isRootBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)]
          exact h.inactive_owner k hk hno
        slot_bij := h.slot_bij
        slotOf_mem := fun v hv => by
          rw [hpre_eq _ (by simp [slotOfVertBase, nodesBase]; omega),
            hmem2_eq _ (by simp [slotOfVertBase, isRootBase]; omega) (by simp [slotOfVertBase, isRootBase]; omega)]
          exact h.slotOf_mem v hv
        vertOf_mem := fun sl hsl => by
          rw [hpre_eq _ (by simp [vertOfSlotBase, nodesBase]; omega),
            hmem2_eq _ (by simp [vertOfSlotBase, isRootBase]; omega) (by simp [vertOfSlotBase, isRootBase]; omega)]
          exact h.vertOf_mem sl hsl
        markArr_zero := fun k hk => by
          rw [hpre_eq _ (by simp [markArrBase, nodesBase]; omega),
            hmem2_eq _ (by simp [markArrBase, isRootBase]; omega) (by simp [markArrBase, isRootBase]; omega)]
          exact h.markArr_zero k hk
        nodesAt := hn₃
        forestInv := hinv₃
        nodes_exact := fun u => by
          have h1 : u ∈ (t₃ :: rest).flatMap AuxTree.toList ↔ u ∈ (t :: rest).flatMap AuxTree.toList := by
            simp only [List.flatMap_cons, List.mem_append, ht3_perm.mem_iff]
          have h2 : u ∈ (t :: rest).flatMap AuxTree.toList ↔ u ∈ x.trees.flatMap AuxTree.toList := by
            simp only [List.mem_flatMap]
            exact ⟨fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mpr ha, hu⟩,
              fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mp ha, hu⟩⟩
          exact h1.trans (h2.trans (h.nodes_exact u))
        comp_none := fun r' hr' hnil => by
          have hne_new : r' ≠ newRoot := fun heq => by
            subst r'; exact hordNew_ne ((fullTour_eq_nil_iff hvalid'.compat newRoot).mp hnil)
          have hr'e : r' ∈ s.rf.R.erase oldRoot := (Finset.mem_insert.mp hr').resolve_left hne_new
          have hne_old : r' ≠ oldRoot := (Finset.mem_erase.mp hr'e).1
          simp only [x', ct', Function.update_of_ne hne_new, Function.update_of_ne hne_old]
          exact h.comp_none r' (Finset.mem_of_mem_erase hr'e) hnil
        comp_some := fun r' hr' hne_ft => by
          by_cases hrn : r' = newRoot
          · subst hrn
            exact ⟨t₃, by simp [x', ct'], by simp [x'], ht3_map⟩
          · have hr'e : r' ∈ s.rf.R.erase oldRoot := (Finset.mem_insert.mp hr').resolve_left hrn
            have hro : r' ≠ oldRoot := (Finset.mem_erase.mp hr'e).1
            have hr'R : r' ∈ s.rf.R := Finset.mem_of_mem_erase hr'e
            obtain ⟨tr', hctr', htr'_mem, htr'_map⟩ := h.comp_some r' hr'R hne_ft
            have htr'_ne : tr' ≠ t := fun heq => hcomp_inj r' hr'R hro (heq ▸ hctr')
            have htr'_rest : tr' ∈ rest := (List.mem_cons.mp (hperm.mem_iff.mp htr'_mem)).resolve_left htr'_ne
            exact ⟨tr', by simp [x', ct', Function.update_of_ne hrn, Function.update_of_ne hro, hctr'],
              by simp [x', htr'_rest], htr'_map⟩
        tree_class := fun tr htr => by
          simp only [x', List.mem_cons] at htr
          rcases htr with rfl | hrest
          · exact Or.inl ⟨newRoot, Finset.mem_insert_self _ _, by simp [x', ct']⟩
          · have htr_mem : tr ∈ x.trees := hperm.mem_iff.mpr (by simp [hrest])
            rcases h.tree_class tr htr_mem with ⟨r', hr', hcr'⟩ | hsing
            · have hro : r' ≠ oldRoot := fun heq => by
                subst heq; exact ht_not_rest ((Option.some.inj (hcr'.symm.trans hct)) ▸ hrest)
              have hrn : r' ≠ newRoot := fun heq => hnewNotR (heq ▸ hr')
              exact Or.inl ⟨r', Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hro, hr'⟩),
                by simp [x', ct', Function.update_of_ne hrn, Function.update_of_ne hro, hcr']⟩
            · exact Or.inr hsing
        inactive_single := fun u h1 h2 hno => by
          have hmem := h.inactive_single u h1 h2 hno
          have hne : AuxTree.node u .leaf .leaf ≠ t := fun heq => by
            have he : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest oldRoot := by
              rw [← ht_map, ← heq]; simp [AuxTree.toList]
            obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he
            exact hno w' hw'
          have hrest : AuxTree.node u .leaf .leaf ∈ rest :=
            (List.mem_cons.mp (hperm.mem_iff.mp hmem)).resolve_left hne
          simp [x', hrest]
        val_active := fun u h1 h2 hact => by
          dsimp only [x'] at h2 ⊢
          have hu_cap : u ≤ x.numNodes := h2
          rw [hval₃ u hu_cap]
          by_cases huN : u = feN
          · subst huN
            rw [hvalN₂, hfeN_key, endOfKey_endKey', tourRootTagVal_eq_succ hvalid' (Finset.mem_insert_self _ _) haN]
            have hvo := h.val_active feN hfeN_pos hfeN_le ⟨newRoot, by rw [hfeN_key, endOfKey_endKey']; exact haN_mem⟩
            have hop : decide (0 < opN) = (x.st.nodes feN).val.isOpen :=
              (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
            have hmk : decide (0 < mkN) = (x.st.nodes feN).val.isMarked :=
              (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
            rw [hvo, hfeN_key, endOfKey_endKey'] at hop hmk
            simp [hop, hmk, s'Abs, tourChangeRoot]
          · rw [hvalne₂ u hu_cap huN]
            by_cases huO : u = feO
            · subst huO
              rw [hvalO₁, hfeO_key, endOfKey_endKey']
              have hrt0 : tourRootTagVal s'Abs aO = 0 := tourRootTagVal_eq_zero fun r' hr' hh => by
                have hreq : r' = oldRoot := h.valid.compat.unique r' oldRoot aO (List.mem_of_head? hh) haO_mem
                subst hreq
                rcases Finset.mem_insert.mp hr' with heq | he'
                · exact hsame heq
                · exact (Finset.mem_erase.mp he').1 rfl
              rw [hrt0]
              have hvo := h.val_active feO hfeO_pos hfeO_le ⟨oldRoot, by rw [hfeO_key, endOfKey_endKey']; exact haO_mem⟩
              have hop : decide (0 < opO) = (x.st.nodes feO).val.isOpen :=
                (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
              have hmk : decide (0 < mkO) = (x.st.nodes feO).val.isMarked :=
                (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
              rw [hvo, hfeO_key, endOfKey_endKey'] at hop hmk
              simp [hop, hmk, s'Abs, tourChangeRoot]
            · rw [hvalne₁ u hu_cap huO, h.val_active u h1 h2 hact]
              have hne_aO : endOfKey (x.keyOf u) ≠ aO := fun heq => by
                have hk : x.keyOf u = endKey aO := by rw [← endKey_endOfKey' (x.keyOf u), heq]
                have := (h.keyOf_mem u h1 h2).2.2; rw [hk] at this; exact huO this.symm
              have hne_aN : endOfKey (x.keyOf u) ≠ aN := fun heq => by
                have hk : x.keyOf u = endKey aN := by rw [← endKey_endOfKey' (x.keyOf u), heq]
                have := (h.keyOf_mem u h1 h2).2.2; rw [hk] at this; exact huN this.symm
              have hrt_eq : tourRootTagVal s'Abs (endOfKey (x.keyOf u)) = tourRootTagVal s (endOfKey (x.keyOf u)) := by
                by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf u))
                · obtain ⟨r', hr'R, hr'h⟩ := hex
                  have hro : r' ≠ oldRoot := fun heq => by
                    subst heq; exact hne_aO (Option.some.inj (hr'h.symm.trans haO))
                  rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                    tourRootTagVal_eq_succ hvalid' (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hro, hr'R⟩)) hr'h]
                · push Not at hex
                  rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
                  intro r' hr' hh
                  rcases Finset.mem_insert.mp hr' with rfl | hr'e
                  · exact hne_aN (Option.some.inj (hh.symm.trans haN))
                  · exact hex r' (Finset.mem_of_mem_erase hr'e) hh
              rw [hrt_eq]; rfl
        val_inactive_rt := fun u h1 h2 hno => by
          dsimp only [x'] at h2 ⊢
          have hu_cap : u ≤ x.numNodes := h2
          have huN : u ≠ feN := fun heq => by subst heq; rw [hfeN_key, endOfKey_endKey'] at hno; exact hno newRoot haN_mem
          have huO : u ≠ feO := fun heq => by subst heq; rw [hfeO_key, endOfKey_endKey'] at hno; exact hno oldRoot haO_mem
          rw [hval₃ u hu_cap, hvalne₂ u hu_cap huN, hvalne₁ u hu_cap huO]
          exact h.val_inactive_rt u h1 h2 hno
        val_unused_rt := fun u hu hcond => by
          dsimp only [x'] at hcond
          have huN : u ≠ feN := by omega
          have huO : u ≠ feO := by omega
          rw [hval₃ u hu, hvalne₂ u hu huN, hvalne₁ u hu huO]
          exact h.val_unused_rt u hu hcond }
    have hAxO : nodesBase b vCap eCap + 17 * feO + 17 ≤ heap := by
      simpa [nodeAddr, tourLayout_stride] using hheap2.addr_lt hfeO_cap
    have hAxN : nodesBase b vCap eCap + 17 * feN + 17 ≤ heap := by
      simpa [nodeAddr, tourLayout_stride] using hheap2.addr_lt hfeN_cap
    have hhdr := h.header
    set r1 := Function.update s0.regs 4 (isRootBase b vCap)
    set r2 := Function.update r1 5 (firstEndBase b)
    set r3 := Function.update r2 6 feO
    set r4 := Function.update r3 7 feN
    set r5 := Function.update r4 8 (nodesBase b vCap eCap)
    set r6 := Function.update r5 9 (2 * eCap + 2)
    set r7 := Function.update r6 10 (nodesBase b vCap eCap + 17 * feO)
    set r8 := Function.update r7 11 opO
    set r9 := Function.update r8 12 mkO
    set r10 := Function.update r9 13 0
    set s_1 : State := { st₁ with regs := Function.update r10 14 o₁.value }
    set r11 := Function.update s_1.regs 10 (nodesBase b vCap eCap + 17 * feN)
    set r12 := Function.update r11 11 opN
    set r13 := Function.update r12 12 mkN
    set r14 := Function.update r13 13 (newRoot + 1)
    set s_2 : State := { st₂ with regs := Function.update r14 14 o₂.value }
    set s_3 : State := { st₃ with regs := Function.update s_2.regs 14 o₃.value }
    have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_IS_ROOT)
      (b := b) (val := isRootBase b vCap) (st := s0) (by simp [s0, startState])
      (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hhdr.2.2.2.2.2.1
    have hst1 := runs_store_reg_off_const (w := w) (p := p) (ω := ω) (rBase := 4) (rIdx := 1)
      (base := isRootBase b vCap) (idx := oldRoot) (val := 0) (st := ⟨mem, r1, pos⟩)
      (by simp [r1]) (by simp [r1, s0, startState])
      (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (by omega)
    have hst2 := runs_store_reg_off_const (w := w) (p := p) (ω := ω) (rBase := 4) (rIdx := 2)
      (base := isRootBase b vCap) (idx := newRoot) (val := 1) (st := ⟨mem1, r1, pos⟩)
      (by simp [r1]) (by simp [r1, s0, startState])
      (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (by omega)
    have ha2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_FIRST_END)
      (b := b) (val := firstEndBase b) (st := ⟨mem2, r1, pos⟩) (by simp [r1, s0, startState])
      (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega)
      (by dsimp only; rw [hmem2_eq _ (by simp [HDR_FIRST_END, isRootBase]; omega) (by simp [HDR_FIRST_END, isRootBase]; omega)]; exact hhdr.2.2.2.2.1)
    have ha3 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 5) (rIdx := 1)
      (base := firstEndBase b) (idx := oldRoot) (val := feO) (st := ⟨mem2, r2, pos⟩)
      (by simp [r2]) (by simp [r2, r1, s0, startState])
      (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
      (by dsimp only; rw [hmem2_eq _ (by simp [firstEndBase, isRootBase]; omega) (by simp [firstEndBase, isRootBase]; omega)]; exact hfeO_first)
    have ha4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 5) (rIdx := 2)
      (base := firstEndBase b) (idx := newRoot) (val := feN) (st := ⟨mem2, r3, pos⟩)
      (by simp [r3, r2]) (by simp [r3, r2, r1, s0, startState])
      (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
      (by dsimp only; rw [hmem2_eq _ (by simp [firstEndBase, isRootBase]; omega) (by simp [firstEndBase, isRootBase]; omega)]; exact hfeN_first)
    have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_NODES_BASE)
      (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem2, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
      (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega)
      (by dsimp only; rw [hmem2_eq _ (by simp [HDR_NODES_BASE, isRootBase]; omega) (by simp [HDR_NODES_BASE, isRootBase]; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1)
    have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_FUEL)
      (b := b) (val := 2 * eCap + 2) (st := ⟨mem2, r5, pos⟩) (by simp [r5, r4, r3, r2, r1, s0, startState])
      (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega)
      (by dsimp only; rw [hmem2_eq _ (by simp [HDR_FUEL, isRootBase]; omega) (by simp [HDR_FUEL, isRootBase]; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    have ha7 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 10) (rNb := 8) (rNode := 6)
      (nb := nodesBase b vCap eCap) (node := feO) (st := ⟨mem2, r6, pos⟩)
      (by simp [r6, r5]) (by simp [r6, r5, r4, r3]) (by omega) (by omega) (by omega)
    have ha8 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 10) (off := 9)
      (b := nodesBase b vCap eCap + 17 * feO) (val := opO) (st := ⟨mem2, r7, pos⟩)
      (by simp [r7]) (by omega) (by omega) hmem2_opO
    have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 10) (off := 10)
      (b := nodesBase b vCap eCap + 17 * feO) (val := mkO) (st := ⟨mem2, r8, pos⟩)
      (by simp [r8, r7]) (by omega) (by omega) hmem2_mkO
    have ha10 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 13) (val := 0) (st := ⟨mem2, r9, pos⟩) (by omega)
    have hcall1 := tour_runs_call_of (r := 14) (args := [.reg 8, .reg 6, .reg 11, .reg 12, .reg 13, .reg 9, .reg 3])
      (st := ⟨mem2, r10, pos⟩) C.setValNode_body
      (by simp [evalArgs, Expr.eval, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₁
    have ha11 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 10) (rNb := 8) (rNode := 7)
      (nb := nodesBase b vCap eCap) (node := feN) (st := s_1)
      (by simp [s_1, r10, r9, r8, r7, r6, r5]) (by simp [s_1, r10, r9, r8, r7, r6, r5, r4])
      (by omega) (by omega) (by omega)
    have ha12 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 10) (off := 9)
      (b := nodesBase b vCap eCap + 17 * feN) (val := opN) (st := ⟨st₁.mem, r11, st₁.pos⟩)
      (by simp [r11]) (by omega) (by omega) hst1_opN
    have ha13 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 10) (off := 10)
      (b := nodesBase b vCap eCap + 17 * feN) (val := mkN) (st := ⟨st₁.mem, r12, st₁.pos⟩)
      (by simp [r12, r11]) (by omega) (by omega) hst1_mkN
    have ha14 := runs_assign_reg_add1 (w := w) (p := p) (ω := ω) (dst := 13) (rSrc := 2) (v := newRoot)
      (st := ⟨st₁.mem, r13, st₁.pos⟩) (by simp [r13, r12, r11, s_1, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState])
      (by omega) (by omega)
    have hcall2 := tour_runs_call_of (r := 14) (args := [.reg 8, .reg 7, .reg 11, .reg 12, .reg 13, .reg 9, .reg 3])
      (st := ⟨st₁.mem, r14, st₁.pos⟩) C.setValNode_body
      (by simp [evalArgs, Expr.eval, r14, r13, r12, r11, s_1, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₂
    have hcall3 := runs_call_regs4 14 8 7 9 3 (st := s_2) C.rotateFront_body
      (by simp [s_2, r14, r13, r12, r11, s_1, r10, r9, r8, r7, r6, r5])
      (by simp [s_2, r14, r13, r12, r11, s_1, r10, r9, r8, r7, r6, r5, r4])
      (by simp [s_2, r14, r13, r12, r11, s_1, r10, r9, r8, r7, r6])
      (by simp [s_2, r14, r13, r12, r11, s_1, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₃
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_3) (r := 3) (v := heap)
      (by simp [s_3, s_2, r14, r13, r12, r11, s_1, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState])
    have hbody :=
      tour_runs_seq_normal ha1 (tour_runs_seq_normal hst1 (tour_runs_seq_normal hst2 (tour_runs_seq_normal ha2
        (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6
          (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10
            (tour_runs_seq_normal hcall1 (tour_runs_seq_normal ha11 (tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13
              (tour_runs_seq_normal ha14 (tour_runs_seq_normal hcall2 (tour_runs_seq_normal hcall3 hret))))))))))))))))))
    have hcond := tour_runs_cond_false (e := .bin .eq (.reg 1) (.reg 2)) (st := s0) (s₁ := .ret (.reg 3))
      (by simp [Expr.eval, s0, startState, BinOp.eval, hsame]) hbody
    have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem heap b x' st₃.mem :=
      ⟨le_refl heap, by omega, hfr_all.1,
        fun a ha hnf => by
          have hnr : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hrec =>
            hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; simp [nodesBase] at this; omega, (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).2⟩)
          rw [hfr_all.2 a ha hnr]
          exact hmem2_eq a
            (fun heq => hnf (Or.inl ⟨by simp [isRootBase] at heq ⊢; omega, by simp [isRootBase, ordHandleOf, tourFixedSize] at heq ⊢; omega⟩))
            (fun heq => hnf (Or.inl ⟨by simp [isRootBase] at heq ⊢; omega, by simp [isRootBase, ordHandleOf, tourFixedSize] at heq ⊢; omega⟩)),
        fun a ha => Or.inl ha⟩
    refine ⟨.returned heap, s_3, _, hcond, rfl, x', hrep', hresp, ?_⟩
    have hlog := tourLog_of_le h.numNodes_le
    have hlm1 := Nat.mul_le_mul_left TOUR_FIND_AMORT hlog
    have hlm2 := Nat.mul_le_mul_left TOUR_SEQ_AMORT hlog
    have htl : 1 ≤ tourLog eCap := by simp [tourLog]
    dsimp only [tourRep, tourPhi, x']
    rw [← hOrd.2, forestPhi_perm hperm]
    simp only [argsSize, Expr.size, TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_SEQ_AMORT, TOUR_FOREST_MUL]
      at hcost₁ hcost₂ hcost₃ hlm1 hlm2 ⊢
    omega

end MinCostFlow.SparseCore.Program
