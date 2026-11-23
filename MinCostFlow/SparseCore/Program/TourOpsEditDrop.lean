module

public import MinCostFlow.SparseCore.Program.TourOpsEditDropCase1
import Mathlib.Tactic

/-!
# Single-edit handler for `dropEdge` (Op 0)

Verifies `tourDropOneBody_runs` (dropping one open end while `ordStore` holds `ord0`) and
`tourEditDropBody_runs` (dropping both ends `(e, true)` and `(e, false)` of open edge `e`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Amortized run theorem for `tourDropOneBody` -/

/-- Verified amortized run theorem for `tourDropOneBody [b, keyX, heap]`. -/
theorem tourDropOneBody_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b keyX heap pos ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program}
    {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (C : TourSplayQueryProcs w p)
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2) (ω : ℕ → Bool)
    {ord0 : ℕ → List End} {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hord0U : OrdUniqueWithin vCap eCap ord0)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) ord0 x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < heap)
    (hmiss : (∃ skip : End, skip ≠ endOfKey keyX ∧ ∀ w', s.ord w' = (ord0 w').filter fun z => z != skip) ∨
      s.ord = ord0)
    (hkeyLt : keyX < 2 * eCap) (hxOpen : (endOfKey keyX).1 ∉ s.rf.F.E)
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 6 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) :
    let s' := tourDropOneAbs s (endOfKey keyX)
    ∃ (h' : ℕ) (st' : State) (c : ℕ) (x' : TourConcrete R_ord.τ),
      Runs w p ω (tourDropOneBody C.deleteNode C.setValNode C.rotateFront ordOp2)
        (startState [b, keyX, heap] mem pos) (.returned h') st' c ∧
      heap ≤ h' ∧ h' ≤ heap + 2 ∧ ZeroFrom st'.mem h' ∧
      (∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap ≤ a ∧ a < h')) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) ord0 x'.ordX st'.mem ∧
      TourCoreAt vCap eCap b s' x' st'.mem ∧
      c + TOUR_PHI_MULT * forestPhi x'.trees + R_ord.phi (ordHandleOf b vCap eCap) x'.ordX st'.mem ≤
        (TOUR_EDIT_SIMPLE_MUL + 2 * mul_ord) * tourLog eCap +
          TOUR_PHI_MULT * forestPhi x.trees + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem := by
  intro s'
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (x.numNodes + 2) + 1 ≤ 2 * tourLog eCap := tourLog_of_le h.numNodes_le
  have hhdr := h.header
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have heo_addr : endOwnerBase b vCap eCap + keyX < 2 ^ w := by
    simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  set s0 : State := startState [b, keyX, heap] mem pos
  set r1 := Function.update s0.regs 3 (endOwnerBase b vCap eCap)
  set eo := mem (endOwnerBase b vCap eCap + keyX)
  set r2 := Function.update r1 4 eo
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_END_OWNER)
    (b := b) (val := endOwnerBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_END_OWNER]; omega) (by simp [HDR_END_OWNER]; omega) hhdr.2.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := endOwnerBase b vCap eCap) (idx := keyX) (val := eo) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState]) heo_addr rfl
  -- Check whether `endOfKey keyX` is active in `s.ord`
  by_cases hex : ∃ v, endOfKey keyX ∈ s.ord v
  · obtain ⟨v, hxv⟩ := hex
    have ⟨hvLt, hrR, hrLt, _, hu1, hu_le, hu_key, t, rest, hct_r, hperm_r, ht_map, hu_t⟩ :=
      h.mem_compTree_of_active hxv
    set r := s.rf.root v
    set u := x.nodeOf keyX
    have hu_eq : u = x.nodeOf (endKey (endOfKey keyX)) := by simp [u, endKey_endOfKey']
    have hu1' : 1 ≤ u := by rwa [hu_eq]
    have hu_le' : u ≤ x.numNodes := by rwa [hu_eq]
    have hu_key' : x.keyOf u = keyX := by rw [hu_eq, hu_key, endKey_endOfKey']
    have hu_t' : u ∈ t.toList := by rwa [hu_eq]
    have heo_eq : eo = x.slotOf v + 1 := by simpa [eo, endKey_endOfKey'] using (h.active_end v hvLt (endOfKey keyX) hxv).2
    have hcond_eo : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 0 := by
      simp [Expr.eval, r2, heo_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
    -- Execute active prefix: decodes `v`, clears `endOwner[keyX] := 0`, loads `u, feBase, feOld, nb, fuel`
    set mem1 := Function.update mem (endOwnerBase b vCap eCap + keyX) 0
    obtain ⟨rP, cP, hrP0, hrP1, hrP2, hrP3, hrP5, hrP6, hrP7, hrP8, hrP9, hrP10, hcP, hrunP⟩ :=
      tourDropOne_prefix_exec (p := p) (pos := pos) ω h hkeyLt hvLt hxv hord_le hroom hw hwide
    have hrunP' := hrunP
    rw [← heo_eq] at hrunP'
    have hvalid' : TourValid vCap eCap s' := tourValid_dropOneAbs h.valid hxOpen
    have hord'_upd : s'.ord = Function.update s.ord v ((s.ord v).filter fun z => z != endOfKey keyX) :=
      tourDropOneAbs_ord_eq_update h.valid hxv
    have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ r → x.compTree r' ≠ some t := by
      intro r' hr' hne heq
      have hne_ft : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := fun h0 => by
        rw [h.comp_none r' hr' h0] at heq; cases heq
      obtain ⟨t', ht'eq, _, ht'map⟩ := h.comp_some r' hr' hne_ft
      rw [heq] at ht'eq; cases Option.some.inj ht'eq
      have hx_ft' : endOfKey keyX ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
        rw [← ht'map]; exact List.mem_map.mpr ⟨u, hu_t', by rw [hu_key']⟩
      obtain ⟨w', hw', hcr'⟩ := ((fullTour_spec h.valid.compat r').2 _).mp hx_ft'
      have hw'v : w' = v := h.valid.compat.unique w' v (endOfKey keyX) hw' hxv
      rw [hw'v] at hcr'
      exact hne ((h.valid.unique_root v (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).unique
        ⟨hr', connected_symm hcr'⟩ (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))))
    have hinv_p : TourForestInv x.numNodes x.st (t :: rest) := (h.forestInv.perm hperm_r).1
    have hn1 : tourLayout.NodesAt mem1 (nodesBase b vCap eCap) x.numNodes x.st :=
      NodesAt.congr tourLayout h.nodesAt fun a ha => by
        dsimp only [mem1]; rw [Function.update_of_ne fun heq => by
          have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [endOwnerBase, nodesBase] at heq this; omega]
    have hzero1 : ZeroFrom mem1 heap := fun a ha => by
      dsimp only [mem1]; rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
      exact hzero a ha
    have hordRep1 : R_ord.rep (ordHandleOf b vCap eCap) ord0 x.ordX mem1 :=
      (hOrdImpl.1 (ordHandleOf b vCap eCap) ord0 x.ordX mem mem1 fun a ha => by
        have := hordGe a ha; dsimp only [mem1]
        rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at this ⊢; omega)]).1 hordRep
    have hordPhi1 : R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem1 = R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem :=
      ((hOrdImpl.1 (ordHandleOf b vCap eCap) ord0 x.ordX mem mem1 fun a ha => by
        have := hordGe a ha; dsimp only [mem1]
        rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at this ⊢; omega)]).2).symm
    -- Obtain `aOld` = head of `s.ord v`
    obtain ⟨aOld, haOld⟩ : ∃ aOld, (s.ord v).head? = some aOld :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord v <;> simp_all)
    set feOld := mem (firstEndBase b + v)
    have hfeOld_eq : feOld = x.nodeOf (endKey aOld) := by simp [feOld, h.firstEnd_mem v hvLt, haOld]
    -- Split on `u = feOld` vs `u ≠ feOld`!
    by_cases hufe : u = feOld
    · -- Case 1: `u = feOld` (`endOfKey keyX` is the HEAD of `s.ord v`)!
      have hx_eq_aOld : endOfKey keyX = aOld := by
        have haLt : endKey aOld < 2 * eCap := by
          have := h.valid.ordWithin.2.2 v aOld (List.mem_of_head? haOld); simp only [endKey]; cases aOld.2 <;> simp <;> omega
        have hnz : x.nodeOf (endKey aOld) ≠ 0 := (h.active_end v hvLt aOld (List.mem_of_head? haOld)).1
        have hkeq : keyX = endKey aOld := by rw [← hu_key', hufe, hfeOld_eq, h.nodeOf_keyOf _ haLt hnz]
        rw [hkeq, endOfKey_endKey]
      have hhead_x : (s.ord v).head? = some (endOfKey keyX) := hx_eq_aOld ▸ haOld
      have hcond_eq : (Expr.bin .eq (.reg 6) (.reg 8)).eval w ⟨mem1, rP, pos⟩ = some 1 := by
        simp [Expr.eval, hrP6, hrP8, u, hufe, BinOp.eval, (by omega : 1 < 2 ^ w)]
      -- Step 1a: run the 1-or-2 `ordNext` calls to find `newFe` (`r14`) and `h1 ≤ heap + 2` (`r2`)
      obtain ⟨hN, newFe, ordXN, stN, cN, hhN_ge, hhN_le, hzN, hpreN_eq, hfrN_out, hfootN, hgeN, hrepN,
        hnewFe_eq, hrN0, hrN1, hrN2, hrN5, hrN6, hrN7, hrN9, hrN10, hrN14, hcN, hrunN⟩ :=
        tourDropOne_findNewFe_exec (pos := pos) hOrdImpl hop2 ω h hord0U hordRep hordGe hordFoot hmiss
          hvLt hkeyLt hxv hhead_x hrP0 hrP1 hrP2 hrP3 hrP5 hrP6 hrP7 hrP9 hrP10 hord_le hroom hw hwide hzero
      -- Step 1b: store `firstEnd[v] := newFe`, read `isRoot[v]`
      set memN1 := Function.update stN.mem (firstEndBase b + v) newFe
      have hst_fe : Runs w p ω (.store (.bin .add (.reg 7) (.reg 5)) (.reg 14)) stN .normal
          { stN with mem := memN1 } 5 :=
        runs_store_iff.mpr ⟨firstEndBase b + v, newFe,
          by simp [Expr.eval, hrN7, hrN5, BinOp.eval, (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : firstEndBase b + v < 2 ^ w)],
          by simp [Expr.eval, hrN14], rfl, rfl, rfl⟩
      have hmN1_irb : memN1 (b + HDR_IS_ROOT) = isRootBase b vCap := by
        dsimp only [memN1]; rw [Function.update_of_ne (by simp [HDR_IS_ROOT, firstEndBase]; omega),
          hpreN_eq _ (by simp [HDR_IS_ROOT, ordHandleOf, tourFixedSize]; omega)]
        rw [Function.update_of_ne (by simp [HDR_IS_ROOT, endOwnerBase]; omega)]
        exact hhdr.2.2.2.2.2.1
      set irV := if v ∈ s.rf.R then 1 else 0
      have hmN1_irv : memN1 (isRootBase b vCap + v) = irV := by
        dsimp only [memN1]; rw [Function.update_of_ne (by simp [isRootBase, firstEndBase]; omega),
          hpreN_eq _ (by simp [isRootBase, ordHandleOf, tourFixedSize]; omega)]
        rw [Function.update_of_ne (by simp [isRootBase, endOwnerBase]; omega)]
        exact h.isRoot_mem v hvLt
      set rI1 := Function.update stN.regs 15 (isRootBase b vCap)
      set rI2 := Function.update rI1 15 irV
      have hI1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 0) (off := HDR_IS_ROOT)
        (b := b) (val := isRootBase b vCap) (st := { stN with mem := memN1 }) hrN0
        (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hmN1_irb
      have hI2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 15) (rIdx := 5)
        (base := isRootBase b vCap) (idx := v) (val := irV) (st := { stN with mem := memN1, regs := rI1 })
        (by simp [rI1]) (by simp [rI1, hrN5])
        (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmN1_irv
      have hnN1 : tourLayout.NodesAt memN1 (nodesBase b vCap eCap) x.numNodes x.st :=
        NodesAt.congr tourLayout h.nodesAt fun a ha => by
          have ⟨h1, h2⟩ := inRecords_lt_ordHandle_of_le h.numNodes_le ha
          dsimp only [memN1]; rw [Function.update_of_ne (by simp [firstEndBase, nodesBase] at h1 ⊢; omega),
            hpreN_eq a h2]
          exact Function.update_of_ne (by simp [endOwnerBase, nodesBase] at h1 ⊢; omega) _ _
      have hzN1' : ZeroFrom memN1 hN := fun a ha => by
        dsimp only [memN1]; rw [Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
        exact hzN a ha
      have hheapN1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes hN 2 memN1 :=
        ⟨by have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega, by omega, hzN1', by omega⟩
      -- Pure Euler-tour deletion fact from `fullTour_dropOneOpen`
      have ht_erase_rot : ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)).IsRotated
          (fullTour s'.ord s'.rf.F hvalid'.compat.forest r) := by
        obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hu_t'
        have hu_nP : u ∉ P := fun hm => (List.nodup_append.mp (hPQ ▸ (hinv_p.treesInv t (by simp)).nodup)).2.2 u hm u (by simp) rfl
        have herase_eq : t.toList.erase u = P ++ Q := by
          rw [hPQ]; clear * - hu_nP
          induction P with
          | nil => simp
          | cons a as ih =>
            have hau : a ≠ u := fun h => hu_nP (by simp [h])
            simp [beq_false_of_ne hau, ih (fun hm => hu_nP (by simp [hm]))]
        have hPQ_map : (P.map fun id => endOfKey (x.keyOf id)) ++ endOfKey keyX :: (Q.map fun id => endOfKey (x.keyOf id)) =
            fullTour s.ord s.rf.F h.valid.compat.forest r := by
          rw [← ht_map, hPQ]; simp [List.map_append, hu_key']
        have hrot_v : ((P.map fun id => endOfKey (x.keyOf id)) ++ endOfKey keyX :: (Q.map fun id => endOfKey (x.keyOf id))).IsRotated
            (fullTour s.ord s.rf.F h.valid.compat.forest v) := by
          rw [hPQ_map]; exact fullTour_isRotated_of_connected h.valid.compat (connected_symm (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).2)
        have hdrop := fullTour_dropOneOpen h.valid.compat hxv hxOpen hrot_v
        have hrot_r : (fullTour s'.ord s'.rf.F hvalid'.compat.forest v).IsRotated
            (fullTour s'.ord s'.rf.F hvalid'.compat.forest r) :=
          fullTour_isRotated_of_connected hvalid'.compat (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).2
        rw [herase_eq, List.map_append]
        have hdrop' : ((P.map fun id => endOfKey (x.keyOf id)) ++ Q.map fun id => endOfKey (x.keyOf id)).IsRotated
            (fullTour s'.ord s'.rf.F hvalid'.compat.forest v) := by
          have hfeq : fullTour s'.ord s'.rf.F hvalid'.compat.forest v =
              fullTour (Function.update s.ord v ((s.ord v).filter fun z => z != endOfKey keyX)) s.rf.F hvalid'.compat.forest v := by
            congr 1
          rw [hfeq]; exact hdrop
        exact hdrop'.trans hrot_r
      -- Helper to close Case 1 after the `if irV` block!
      have hClose1 : ∀ (tF? : Option AuxTree) (sF : SplayState TourVal TourSum Unit) (stF : State) (cTail : ℕ),
          Runs w p ω
            (.cond (.reg 15)
              (.assign 16 (.const 1) ;; .assign 17 (.const 0) ;;
               .call 18 C.setValNode [.reg 9, .reg 6, .reg 16, .reg 17, .reg 17, .reg 10, .reg 2] ;;
               .call 18 C.deleteNode [.reg 9, .reg 6, .reg 10, .reg 2] ;;
               .cond (.reg 14)
                 (.assign 15 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 14))) ;;
                  .assign 16 (.load (.bin .add (.reg 15) (.const 9))) ;;
                  .assign 17 (.load (.bin .add (.reg 15) (.const 10))) ;;
                  .assign 18 (.bin .add (.reg 5) (.const 1)) ;;
                  .call 19 C.setValNode [.reg 9, .reg 14, .reg 16, .reg 17, .reg 18, .reg 10, .reg 2] ;;
                  .call 19 C.rotateFront [.reg 9, .reg 14, .reg 10, .reg 2])
                 .nop)
              (.call 18 C.deleteNode [.reg 9, .reg 6, .reg 10, .reg 2]))
            { stN with mem := memN1, regs := rI2 } .normal stF cTail →
          stF.regs 2 = hN →
          tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) x.numNodes sF →
          TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes hN memN1 stF.mem →
          TourForestInv x.numNodes sF (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) →
          (optList tF?).Perm (t.toList.erase u) →
          (optList tF?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r →
          (∀ id, 1 ≤ id → id ≤ x.numNodes → id ≠ u →
            (∃ w', endOfKey (x.keyOf id) ∈ s'.ord w') →
            (sF.nodes id).val =
              { isOpen := decide ((endOfKey (x.keyOf id)).1 ∉ s.rf.F.E)
                isMarked := decide (endOfKey (x.keyOf id) ∈ s'.marked)
                rootTag := tourRootTagVal s' (endOfKey (x.keyOf id)) }) →
          (sF.nodes u).val.rootTag = 0 →
          (∀ id ≤ x.numNodes, (∀ w', endOfKey (x.keyOf id) ∉ s.ord w') ∨ id = 0 ∨ x.numNodes < id →
            (sF.nodes id).val = (x.st.nodes id).val) →
          cTail + TOUR_PHI_MULT * forestPhi (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) ≤
            TOUR_PHI_MULT * forestPhi (t :: rest) +
              (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) + 200 →
          ∃ (h' : ℕ) (st' : State) (c : ℕ) (x' : TourConcrete R_ord.τ),
            Runs w p ω (tourDropOneBody C.deleteNode C.setValNode C.rotateFront ordOp2)
              (startState [b, keyX, heap] mem pos) (.returned h') st' c ∧
            heap ≤ h' ∧ h' ≤ heap + 2 ∧ ZeroFrom st'.mem h' ∧
            (∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
              ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
            (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a →
              R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap ≤ a ∧ a < h')) ∧
            (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a → ordHandleOf b vCap eCap ≤ a) ∧
            R_ord.rep (ordHandleOf b vCap eCap) ord0 x'.ordX st'.mem ∧
            TourCoreAt vCap eCap b s' x' st'.mem ∧
            c + TOUR_PHI_MULT * forestPhi x'.trees + R_ord.phi (ordHandleOf b vCap eCap) x'.ordX st'.mem ≤
              (TOUR_EDIT_SIMPLE_MUL + 2 * mul_ord) * tourLog eCap +
                TOUR_PHI_MULT * forestPhi x.trees + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem := by
        intro tF? sF stF cTail hrunTail hrF2 hnF hfrF hinvF htF_perm htF_map hvalF_act hvalF_u hvalF_oth hcTail
        have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := stF) (r := 2) (v := hN) hrF2
        have hfull : Runs w p ω (tourDropOneBody C.deleteNode C.setValNode C.rotateFront ordOp2)
            (startState [b, keyX, heap] mem pos) (.returned hN) stF _ :=
          tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_false hcond_eo
            (runs_seqAppend hrunP' (tour_runs_cond_true hcond_eq (by omega)
              (runs_seqAppend hrunN (tour_runs_seq_normal hst_fe (tour_runs_seq_normal hI1
                (tour_runs_seq_normal hI2 (tour_runs_seq_normal hrunTail hret)))))))))
        have hagree_ord : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXN a → stN.mem a = stF.mem a := fun a ha => by
          have hge_a := hgeN a ha
          have hlt_a : a < hN := by
            rcases hfootN a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (hordFoot a h0) hhN_ge; exact h2
          have h1 := hfrF.2 a hlt_a (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le hge_a)
          rw [h1]; dsimp only [memN1]
          exact (Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hge_a ⊢; omega) _ _).symm
        have hOrdF := hOrdImpl.1 (ordHandleOf b vCap eCap) ord0 ordXN stN.mem stF.mem hagree_ord
        have hmF_pre : ∀ a < nodesBase b vCap eCap, a ≠ endOwnerBase b vCap eCap + keyX →
            a ≠ firstEndBase b + v → stF.mem a = mem a := fun a hlt h1 h2 => by
          rw [hfrF.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at hlt hord_le ⊢; omega) (not_inRecords_of_lt_nodesBase hlt)]
          dsimp only [memN1]; rw [Function.update_of_ne h2,
            hpreN_eq a (by simp [nodesBase, ordHandleOf, tourFixedSize] at hlt ⊢; omega)]
          exact Function.update_of_ne h1 _ _
        have hmF_eo0 : stF.mem (endOwnerBase b vCap eCap + keyX) = 0 := by
          rw [hfrF.2 _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (not_inRecords_of_lt_nodesBase (by simp [endOwnerBase, nodesBase]; omega))]
          dsimp only [memN1]; rw [Function.update_of_ne (by simp [endOwnerBase, firstEndBase]; omega),
            hpreN_eq _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]
          simp
        have hmF_fev : stF.mem (firstEndBase b + v) = match (s'.ord v).head? with | none => 0 | some e => x.nodeOf (endKey e) := by
          rw [hfrF.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (not_inRecords_of_lt_nodesBase (by simp [firstEndBase, nodesBase]; omega))]
          simp only [memN1, Function.update_self, hnewFe_eq, s']; rfl
        set x' : TourConcrete R_ord.τ :=
          { ordX := ordXN, numNodes := x.numNodes, st := sF,
            trees := AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest,
            nodeOf := x.nodeOf, keyOf := x.keyOf,
            compTree := Function.update x.compTree r tF?,
            slotOf := x.slotOf, vertOf := x.vertOf }
        have hcore' : TourCoreAt vCap eCap b s' x' stF.mem :=
          tourDropOne_core h hkeyLt hvLt hxv hxOpen rfl hu1' hu_le' hu_key' hct_r hperm_r hu_t' hcomp_inj
            hnF hinvF htF_perm htF_map hmF_pre hmF_eo0 hmF_fev hvalF_act hvalF_u hvalF_oth
        refine ⟨hN, stF, _, x', hfull, hhN_ge, hhN_le, hfrF.1,
          fun a ha1 ha2 hnf => by
            rw [hfrF.2 a (by omega) (fun hrec => by have := inRecords_lt_ordHandle_of_le h.numNodes_le hrec; simp [nodesBase] at this; rcases ha2 with h1 | h2 <;> omega)]
            dsimp only [memN1]; rw [Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha2 ⊢; rcases ha2 with h1 | h2 <;> omega)]
            exact hfrN_out a ha1 ha2 hnf,
          hfootN, hgeN, hOrdF.1 hrepN, hcore', ?_⟩
        dsimp only [x']; rw [← hOrdF.2, forestPhi_perm hperm_r]
        have hmul : (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
            (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (2 * tourLog eCap) := Nat.mul_le_mul_left _ hlog
        clear * - hcP hcN hcTail hmul htl
        simp only [Expr.size, TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_SEQ_AMORT, TOUR_EDIT_SIMPLE_MUL] at *
        nlinarith
      -- Split on `v ∈ s.rf.R` vs `v ∉ s.rf.R`!
      obtain ⟨tF?, sF, stF, cTail, hrunTail, hrF2, hnF, hfrF, hinvF, htF_perm, htF_map,
        hvalF_act, hvalF_u, hvalF_oth, hcTail⟩ :=
        tourDropOne_case1_cond (stN := stN) (rI2 := rI2) C ω h hkeyLt hvLt hxv hxOpen hhead_x rfl hu1' hu_le' hu_key' hinv_p hperm_r ht_map hu_t'
          hnN1 hheapN1 hnewFe_eq ht_erase_rot
          (by simp [rI2, rI1, hrN2]) (by simp [rI2, rI1, hrN5]) (by simp [rI2, rI1, hrN6])
          (by simp [rI2, rI1, hrN9]) (by simp [rI2, rI1, hrN10]) (by simp [rI2, rI1, hrN14])
          (by simp [rI2, irV]) (by omega) (by omega) hw hwide
      exact hClose1 tF? sF stF cTail hrunTail hrF2 hnF hfrF hinvF htF_perm htF_map hvalF_act hvalF_u hvalF_oth hcTail
    · -- Case 2: `u ≠ feOld` (`endOfKey keyX` is NOT the head of `s.ord v`): just `deleteNode u`, return `heap`!
      have hx_ne_aOld : endOfKey keyX ≠ aOld := fun heq => hufe (by rw [hfeOld_eq, ← heq, endKey_endOfKey'])
      have hcond_eq : (Expr.bin .eq (.reg 6) (.reg 8)).eval w ⟨mem1, rP, pos⟩ = some 0 := by
        simp [Expr.eval, hrP6, hrP8, u, hufe, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hheap1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 mem1 :=
        ⟨by have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega, by omega, hzero1, by omega⟩
      obtain ⟨t₂?, s₂, o₂, st₂, c₂, hrun₂, _, hn₂, hfr₂, hinv₂, _, hlist₂, hval₂, _, hcost₂⟩ :=
        tourDeleteNodeBody_runs (fuel := 2 * eCap + 2) (pos := pos) C.toTourSplayOpsProcs ω hn1 hinv_p (h.valsOk hw) hu_t'
          (by have := h.numNodes_le; omega) (by omega) hheap1
      have hcall_del := runs_call_regs4 18 9 6 10 2 (st := ⟨mem1, rP, pos⟩) C.deleteNode_body
        hrP9 hrP6 hrP10 hrP2 hrun₂
      set rFin := Function.update rP 18 o₂.value
      have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := { st₂ with regs := rFin }) (r := 2) (v := heap)
        (by simp [rFin, hrP2])
      have hfull : Runs w p ω (tourDropOneBody C.deleteNode C.setValNode C.rotateFront ordOp2)
          (startState [b, keyX, heap] mem pos) (.returned heap) { st₂ with regs := rFin } _ :=
        tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_false hcond_eo
          (runs_seqAppend hrunP' (tour_runs_cond_false hcond_eq (tour_runs_seq_normal hcall_del hret)))))
      -- Head of `s'.ord v` is unchanged (`aOld`)!
      have hhd_v' : (s'.ord v).head? = some aOld := by
        cases hvo : s.ord v with
        | nil => rw [hvo] at haOld; simp at haOld
        | cons a as =>
          rw [hvo] at haOld; cases Option.some.inj haOld
          simp [s', tourDropOneAbs, hvo, bne_iff_ne, hx_ne_aOld.symm]
      -- `t.toList.erase u` still starts at `firstEnd[r]`!
      have ht₂_map : (optList t₂?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
        rw [hlist₂]
        obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hu_t'
        have hu_nP : u ∉ P := fun hm => (List.nodup_append.mp (hPQ ▸ (hinv_p.treesInv t (by simp)).nodup)).2.2 u hm u (by simp) rfl
        have herase_eq : t.toList.erase u = P ++ Q := by
          rw [hPQ]; clear * - hu_nP
          induction P with
          | nil => simp
          | cons a as ih =>
            have hau : a ≠ u := fun h => hu_nP (by simp [h])
            simp [beq_false_of_ne hau, ih (fun hm => hu_nP (by simp [hm]))]
        have hPQ_map : (P.map fun id => endOfKey (x.keyOf id)) ++ endOfKey keyX :: (Q.map fun id => endOfKey (x.keyOf id)) =
            fullTour s.ord s.rf.F h.valid.compat.forest r := by
          rw [← ht_map, hPQ]; simp [List.map_append, hu_key']
        have hrot_v : ((P.map fun id => endOfKey (x.keyOf id)) ++ endOfKey keyX :: (Q.map fun id => endOfKey (x.keyOf id))).IsRotated
            (fullTour s.ord s.rf.F h.valid.compat.forest v) := by
          rw [hPQ_map]; exact fullTour_isRotated_of_connected h.valid.compat (connected_symm (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).2)
        have hdrop := fullTour_dropOneOpen h.valid.compat hxv hxOpen hrot_v
        have hrot_r : (fullTour s'.ord s'.rf.F hvalid'.compat.forest v).IsRotated
            (fullTour s'.ord s'.rf.F hvalid'.compat.forest r) :=
          fullTour_isRotated_of_connected hvalid'.compat (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).2
        have ht_er_rot : ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)).IsRotated
            (fullTour s'.ord s'.rf.F hvalid'.compat.forest r) := by
          rw [herase_eq, List.map_append]
          have hfeq : fullTour s'.ord s'.rf.F hvalid'.compat.forest v =
              fullTour (Function.update s.ord v ((s.ord v).filter fun z => z != endOfKey keyX)) s.rf.F hvalid'.compat.forest v := by
            congr 1
          have hdrop' : ((P.map fun id => endOfKey (x.keyOf id)) ++ Q.map fun id => endOfKey (x.keyOf id)).IsRotated
              (fullTour s'.ord s'.rf.F hvalid'.compat.forest v) := by
            rw [hfeq]; exact hdrop
          exact hdrop'.trans hrot_r
        have hord_r_ne : s.ord r ≠ [] := fun h0 => by
          have := (fullTour_eq_nil_iff h.valid.compat r).mpr h0
          rw [← ht_map] at this; have hne := hinv_p.nonEmpty t (by simp)
          have hnil := List.map_eq_nil_iff.mp this; cases t <;> simp [AuxTree.toList] at hne hnil
        obtain ⟨aR, haR⟩ : ∃ aR, (s.ord r).head? = some aR :=
          Option.isSome_iff_exists.mp (by cases ho : s.ord r <;> simp_all)
        have haR_ne_x : aR ≠ endOfKey keyX := by
          by_cases hrv : r = v
          · rw [hrv, haOld] at haR; exact (Option.some.inj haR ▸ hx_ne_aOld.symm)
          · intro heq; exact hrv (h.valid.compat.unique r v aR (List.mem_of_head? haR) (heq ▸ hxv))
        have hhd_t : (t.toList.map fun id => endOfKey (x.keyOf id)).head? = some aR := by
          rw [ht_map]; exact fullTour_head? h.valid.compat r haR
        cases htc : t.toList with
        | nil => rw [htc] at hu_t'; simp at hu_t'
        | cons t0 ts =>
          have ht0_eq : endOfKey (x.keyOf t0) = aR := by rw [htc] at hhd_t; simpa using hhd_t
          have ht0_ne_u : t0 ≠ u := fun heq => haR_ne_x (by rw [← ht0_eq, heq, hu_key'])
          have hhd_er : ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)).head? = some aR := by
            rw [htc, List.erase_cons]; simp [beq_false_of_ne ht0_ne_u, ht0_eq]
          have hhd_s' : (s'.ord r).head? = some aR := by
            by_cases hrv : r = v
            · rw [hrv] at haR ⊢; rw [haOld] at haR; cases Option.some.inj haR; exact hhd_v'
            · simpa [hord'_upd, Function.update_of_ne hrv] using haR
          have h1 := tour_rotateToList_eq_of_isRotated (ht_er_rot.perm.nodup_iff.mpr (fullTour_spec hvalid'.compat r).1)
            (List.IsRotated.refl _) hhd_er
          have h2 := tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1 ht_er_rot
            (fullTour_head? hvalid'.compat r hhd_s')
          rw [← htc]; exact h1.symm.trans h2
      have hagree_ord : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → mem a = st₂.mem a := fun a ha => by
        have hge_a := hordGe a ha
        rw [hfr₂.2 a (hordFoot a ha) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le hge_a)]
        dsimp only [mem1]; exact (Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hge_a ⊢; omega) _ _).symm
      have hOrdF := hOrdImpl.1 (ordHandleOf b vCap eCap) ord0 x.ordX mem st₂.mem hagree_ord
      set x' : TourConcrete R_ord.τ :=
        { ordX := x.ordX, numNodes := x.numNodes, st := s₂,
          trees := AuxTree.node u .leaf .leaf :: optTrees t₂? ++ rest,
          nodeOf := x.nodeOf, keyOf := x.keyOf,
          compTree := Function.update x.compTree r t₂?,
          slotOf := x.slotOf, vertOf := x.vertOf }
      have hcore' : TourCoreAt vCap eCap b s' x' st₂.mem :=
        tourDropOne_core h hkeyLt hvLt hxv hxOpen rfl hu1' hu_le' hu_key' hct_r hperm_r hu_t' hcomp_inj
          hn₂ hinv₂ (by rw [hlist₂]) ht₂_map
          (fun a hlt h1 _ => by
            rw [hfr₂.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at hlt hord_le ⊢; omega) (not_inRecords_of_lt_nodesBase hlt)]
            dsimp only [mem1]; exact Function.update_of_ne h1 _ _)
          (by rw [hfr₂.2 _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (not_inRecords_of_lt_nodesBase (by simp [endOwnerBase, nodesBase]; omega))]; simp [mem1])
          (by rw [hfr₂.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (not_inRecords_of_lt_nodesBase (by simp [firstEndBase, nodesBase]; omega))]
              dsimp only [mem1]; rw [Function.update_of_ne (by simp [firstEndBase, endOwnerBase]; omega),
                h.firstEnd_mem v hvLt, haOld, hhd_v'])
          (fun id h1 h2 _ hact => by
            have hcap : id ≤ x.numNodes := h2
            obtain ⟨w', hw'⟩ := hact
            have hw'0 : endOfKey (x.keyOf id) ∈ s.ord w' := (List.mem_filter.mp hw').1
            have hne_x : endOfKey (x.keyOf id) ≠ endOfKey keyX := bne_iff_ne.mp (List.mem_filter.mp hw').2
            rw [hval₂ id hcap, h.val_active id h1 h2 ⟨w', hw'0⟩]
            have hmk_eq : decide (endOfKey (x.keyOf id) ∈ s'.marked) = decide (endOfKey (x.keyOf id) ∈ s.marked) := by
              simp [s', tourDropOneAbs, hne_x]
            have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
              have hhd_eq : ∀ r' ∈ s.rf.R, (s'.ord r').head? = (s.ord r').head? := fun r' _ => by
                by_cases hrv : r' = v
                · subst hrv; rw [hhd_v', haOld]
                · simp [hord'_upd, Function.update_of_ne hrv]
              by_cases hex' : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
              · obtain ⟨r', hr'R, hr'h⟩ := hex'
                rw [tourRootTagVal_eq_succ h.valid hr'R hr'h, tourRootTagVal_eq_succ hvalid' hr'R ((hhd_eq r' hr'R).trans hr'h)]
              · push Not at hex'
                rw [tourRootTagVal_eq_zero hex', tourRootTagVal_eq_zero]
                intro r' hr' hh; exact hex' r' hr' ((hhd_eq r' hr').symm.trans hh)
            rw [hmk_eq, hrt_eq])
          (by rw [hval₂ u hu_le', h.val_active u hu1' hu_le' ⟨v, by rwa [hu_key']⟩, hu_key']
              apply tourRootTagVal_eq_zero; intro r' hr' hh
              have hr'v : r' = v := h.valid.compat.unique r' v (endOfKey keyX) (List.mem_of_head? hh) hxv
              subst hr'v; rw [haOld] at hh; exact hx_ne_aOld (Option.some.inj hh).symm)
          (fun id hid _ => hval₂ id hid)
      refine ⟨heap, { st₂ with regs := rFin }, _, x', hfull, le_refl _, by omega, hfr₂.1,
        fun a ha1 ha2 _ => by
          rw [hfr₂.2 a ha1 (fun hrec => by
            have hrec2 := inRecords_lt_ordHandle_of_le h.numNodes_le hrec
            have hnb : b ≤ nodesBase b vCap eCap := by simp [nodesBase]; omega
            rcases ha2 with h1 | h2 <;> omega)]
          dsimp only [mem1]
          exact Function.update_of_ne (by
            have h1 : b ≤ endOwnerBase b vCap eCap := by simp [endOwnerBase]; omega
            have h2 : endOwnerBase b vCap eCap + keyX < ordHandleOf b vCap eCap := by
              simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega
            rcases ha2 with ha2 | ha2 <;> omega) _ _,
        fun _ ha => Or.inl ha, hordGe, hOrdF.1 hordRep, hcore', ?_⟩
      dsimp only [x']; rw [← hOrdF.2, forestPhi_perm hperm_r]
      have hmul : TOUR_SEQ_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤ TOUR_SEQ_AMORT * (2 * tourLog eCap) :=
        Nat.mul_le_mul_left _ hlog
      clear * - hcP hcost₂ hmul htl
      simp only [Expr.size, TOUR_PHI_MULT, TOUR_SEQ_AMORT, TOUR_EDIT_SIMPLE_MUL] at *; nlinarith
  · -- Inactive end (`endOwner[keyX] = 0`): no-op, return `heap`!
    push Not at hex
    have heo0 : eo = 0 := h.inactive_owner keyX hkeyLt hex
    have hcond_eo : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 1 := by
      simp [Expr.eval, r2, heo0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem, r2, pos⟩) (r := 2) (v := heap)
      (by simp [r2, r1, s0, startState])
    have hfull : Runs w p ω (tourDropOneBody C.deleteNode C.setValNode C.rotateFront ordOp2)
        (startState [b, keyX, heap] mem pos) (.returned heap) ⟨mem, r2, pos⟩ _ :=
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_true hcond_eo (by omega) hret))
    have hs'_eq : s' = s := tourDropOneAbs_eq_self_of_not_mem h.valid hex
    refine ⟨heap, ⟨mem, r2, pos⟩, _, x, hfull, le_refl _, by omega, hzero,
      fun _ _ _ _ => rfl, fun _ ha => Or.inl ha, hordGe, hordRep, hs'_eq ▸ h, ?_⟩
    have hmul : 100 ≤ (TOUR_EDIT_SIMPLE_MUL + 2 * mul_ord) * tourLog eCap := by
      have : 100 * 1 ≤ (TOUR_EDIT_SIMPLE_MUL + 2 * mul_ord) * tourLog eCap := Nat.mul_le_mul (by unfold TOUR_EDIT_SIMPLE_MUL; omega) htl
      omega
    clear * - hmul; simp only [Expr.size] at *; omega

/-! ## Amortized run theorem for `tourEditDropBody` -/

/-- Verified amortized run theorem for `tourEditDropBody [b, e, heap]`: drops both ends of open
edge `e`, returning updated `h' ≤ heap + 4`. -/
theorem tourEditDropBody_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b e heap pos dropOneProc ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program}
    {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (C : TourSplayQueryProcs w p)
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2)
    (hdropOne : p.procs[dropOneProc]? = some (tourDropOneBody C.deleteNode C.setValNode C.rotateFront ordOp2))
    (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) s.ord x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < heap)
    (heLt : e < eCap) (heOpen : e ∉ s.rf.F.E)
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 8 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) :
    let s' := tourApplyEdit s (.dropEdge e)
    ∃ (h' : ℕ) (st' : State) (c : ℕ) (x' : TourConcrete R_ord.τ),
      Runs w p ω (tourEditDropBody dropOneProc)
        (startState [b, e, heap] mem pos) (.returned h') st' c ∧
      heap ≤ h' ∧ h' ≤ heap + 4 ∧ ZeroFrom st'.mem h' ∧
      (∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap ≤ a ∧ a < h')) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) s.ord x'.ordX st'.mem ∧
      TourCoreAt vCap eCap b s' x' st'.mem ∧
      c + TOUR_PHI_MULT * forestPhi x'.trees + R_ord.phi (ordHandleOf b vCap eCap) x'.ordX st'.mem ≤
        (2 * TOUR_EDIT_SIMPLE_MUL + 4 * mul_ord + 30) * tourLog eCap +
          TOUR_PHI_MULT * forestPhi x.trees + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem := by
  intro s'
  have hord0U : OrdUniqueWithin vCap eCap s.ord := ⟨h.valid.ordWithin, h.valid.compat.unique⟩
  have hk0 : endOfKey (2 * e) = (e, true) := by simp [endOfKey]
  have hk1 : endOfKey (2 * e + 1) = (e, false) := by simp [endOfKey]; omega
  obtain ⟨h1, st1, c1, x1, hrun1, hh1_ge, hh1_le, hz1, hfr1, hfoot1, hge1, hrep1, hcore1, hcost1⟩ :=
    tourDropOneBody_runs (keyX := 2 * e) (pos := pos) C hOrdImpl hop2 ω h hord0U hordRep hordGe hordFoot
      (Or.inr rfl) (by omega) (by rw [hk0]; exact heOpen) hord_le (by omega) hw hwide hzero
  have hfoot1_lt : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x1.ordX a → a < h1 := fun a ha => by
    rcases hfoot1 a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (hordFoot a h0) hh1_ge; exact h2
  have hmiss2 : (∃ skip : End, skip ≠ endOfKey (2 * e + 1) ∧
      ∀ w', (tourDropOneAbs s (endOfKey (2 * e))).ord w' = (s.ord w').filter fun z => z != skip) ∨
      (tourDropOneAbs s (endOfKey (2 * e))).ord = s.ord :=
    Or.inl ⟨(e, true), by rw [hk1]; simp, fun w' => by simp [tourDropOneAbs, hk0]⟩
  obtain ⟨h2, st2, c2, x2, hrun2, hh2_ge, hh2_le, hz2, hfr2, hfoot2, hge2, hrep2, hcore2, hcost2⟩ :=
    tourDropOneBody_runs (keyX := 2 * e + 1) (pos := st1.pos) C hOrdImpl hop2 ω hcore1 hord0U hrep1 hge1 hfoot1_lt
      hmiss2 (by omega) (by rw [hk1]; exact heOpen) (by omega) (by omega) hw hwide hz1
  set s0 : State := startState [b, e, heap] mem pos
  set r1 := Function.update s0.regs 3 (2 * e)
  have ha1 : Runs w p ω (.assign 3 (.bin .mul (.const 2) (.reg 1))) s0 .normal ⟨mem, r1, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨2 * e, by
      simp [Expr.eval, s0, startState, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w)], rfl, rfl, rfl⟩
  have hc1 := runs_call_regs3 4 0 3 2 (st := ⟨mem, r1, pos⟩) hdropOne
    (by simp [r1, s0, startState]) (by simp [r1]) (by simp [r1, s0, startState]) hrun1
  set r2 := Function.update r1 4 h1
  set r3 := Function.update r2 3 (2 * e + 1)
  have ha2 : Runs w p ω (.assign 3 (.bin .add (.reg 3) (.const 1))) { st1 with regs := r2 } .normal
      { st1 with regs := r3 } 4 :=
    runs_assign_iff.mpr ⟨2 * e + 1, by
      simp [Expr.eval, r2, r1, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : 2 * e + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have hc2 := runs_call_regs3 4 0 3 4 (st := { st1 with regs := r3 }) hdropOne
    (by simp [r3, r2, r1, s0, startState]) (by simp [r3]) (by simp [r3, r2]) hrun2
  set r4 := Function.update r3 4 h2
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := { st2 with regs := r4 }) (r := 4) (v := h2)
    (by simp [r4])
  have hfull : Runs w p ω (tourEditDropBody dropOneProc) (startState [b, e, heap] mem pos)
      (.returned h2) { st2 with regs := r4 } _ :=
    tour_runs_seq_normal ha1 (tour_runs_seq_normal hc1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal hc2 hret)))
  have hs'_eq : tourDropOneAbs (tourDropOneAbs s (endOfKey (2 * e))) (endOfKey (2 * e + 1)) = s' := by
    rw [hk0, hk1]; exact tourDropOneAbs_twice_eq_dropEdge s e
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  refine ⟨h2, { st2 with regs := r4 }, _, x2, hfull, by omega, by omega, hz2,
    fun a ha1 ha2 hnf => by
      have hnf1 : ¬R_ord.foot (ordHandleOf b vCap eCap) x1.ordX a := fun hft => by
        rcases hfoot1 a hft with h0 | ⟨h0a, _⟩; exact hnf h0; omega
      exact (hfr2 a (by omega) ha2 hnf1).trans (hfr1 a ha1 ha2 hnf),
    fun a ha => by
      rcases hfoot2 a ha with h1' | ⟨h1a, h1b⟩
      · rcases hfoot1 a h1' with h0 | ⟨h0a, h0b⟩; exact Or.inl h0; exact Or.inr ⟨h0a, by omega⟩
      · exact Or.inr ⟨by omega, h1b⟩,
    hge2, hrep2, hs'_eq ▸ hcore2, ?_⟩
  dsimp only at hcost1 hcost2 ⊢
  clear * - hcost1 hcost2 htl; nlinarith

end MinCostFlow.SparseCore.Program
