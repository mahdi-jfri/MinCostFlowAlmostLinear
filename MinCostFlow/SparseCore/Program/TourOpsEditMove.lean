module

public import MinCostFlow.SparseCore.Program.TourOpsEditMoveSplitExec
import Mathlib.Tactic

/-!
# `moveEnds` edit handler (`tourEditMoveBody`) for Op 0 (`applyEdits`)

Implements and verifies `tourEditMoveBody [b, recPtr, heap]`, handling both `tag = 1`
(`complement = false`) and `tag = 2` (`complement = true`) in `O((len + 1) * tourLog eCap)`
amortized time and `≤ 4 * len + 2` heap words, updating all tour structures and leaving the
embedded `ordStore` ready for `tourCore_commitOrdStore`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM body for `moveEnds` -/

/-- `moveEnds` handler: args `[b, recPtr, heap]`. Updates the tour representation for the
`moveEnds` record at `recPtr` and returns `hOut ≤ heap + 4 * len + 2`. -/
def tourEditMoveBody
    (splayProc setValProc rotFrontProc collectProc rankSortProc splitLoopProc walkFrontProc : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 7 (.bin .add (.reg 1) (.const 4)) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
  .assign 8 (.load (.bin .add (.reg 8) (.reg 4))) ;;
  .cond (.bin .eq (.reg 8) (.const 0))
    (.assign 9 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
     .store (.bin .add (.reg 9) (.reg 5)) (.const 1) ;;
     .ret (.reg 2))
    (tourMoveSplitPhaseStmt splayProc setValProc rotFrontProc collectProc rankSortProc splitLoopProc ;;
     tourMoveOwnersStmt walkFrontProc ;;
     tourMoveRootsStmt setValProc rotFrontProc ;;
     .ret (.reg 15))

theorem tourEditMoveBody_noRand (sp sV rF cP rS sL wF : ℕ) :
    (tourEditMoveBody sp sV rF cP rS sL wF).NoRand := by
  have hsp := tourMoveSplitPhaseStmt_noRand sp sV rF cP rS sL
  have ⟨h1, h2⟩ := tourMovePost_stmts_noRand wF sV rF
  simp [tourEditMoveBody, Stmt.NoRand, hsp, h1, h2]

/-- Amortized cost multiplier for `tourEditMoveBody` (excluding `mul_ord`). -/
def TOUR_MOVE_MUL : ℕ :=
  TOUR_MOVE_SORT_MUL + 2 * TOUR_MOVE_STEP_AMORT + 2 * TOUR_SPLAY_AMORT +
    4 * TOUR_SEQ_AMORT + 6 * TOUR_FIND_AMORT + 4 * TOUR_JOIN_AMORT + 2000

private theorem move_cost_combine (len m mul_ord tl : ℕ) (hml : m ≤ len) (htl : 1 ≤ tl) :
    (m + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tl +
      ((m + 1) * TOUR_MOVE_STEP_AMORT + TOUR_SPLAY_AMORT + 2 * TOUR_SEQ_AMORT +
        3 * TOUR_FIND_AMORT + 2 * TOUR_JOIN_AMORT) * (2 * tl) +
      160 * len + 1000 ≤
    (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tl := by
  have h1 : m + 1 ≤ len + 1 := by omega
  have h2 : (m + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tl ≤ (len + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tl :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
  have h3 : (m + 1) * TOUR_MOVE_STEP_AMORT * (2 * tl) ≤ (len + 1) * (2 * TOUR_MOVE_STEP_AMORT) * tl := by
    have : (m + 1) * TOUR_MOVE_STEP_AMORT ≤ (len + 1) * TOUR_MOVE_STEP_AMORT := Nat.mul_le_mul_right _ h1
    nlinarith
  have h4 : (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tl =
      (len + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tl +
      (len + 1) * (2 * TOUR_MOVE_STEP_AMORT) * tl +
      (len + 1) * (2 * TOUR_SPLAY_AMORT + 4 * TOUR_SEQ_AMORT + 6 * TOUR_FIND_AMORT + 4 * TOUR_JOIN_AMORT) * tl +
      (len + 1) * 2000 * tl := by
    unfold TOUR_MOVE_MUL; ring
  have h5 : (TOUR_SPLAY_AMORT + 2 * TOUR_SEQ_AMORT + 3 * TOUR_FIND_AMORT + 2 * TOUR_JOIN_AMORT) * (2 * tl) ≤
      (len + 1) * (2 * TOUR_SPLAY_AMORT + 4 * TOUR_SEQ_AMORT + 6 * TOUR_FIND_AMORT + 4 * TOUR_JOIN_AMORT) * tl := by
    have hle : 1 ≤ len + 1 := by omega
    have heq : (TOUR_SPLAY_AMORT + 2 * TOUR_SEQ_AMORT + 3 * TOUR_FIND_AMORT + 2 * TOUR_JOIN_AMORT) * (2 * tl) =
        1 * (2 * TOUR_SPLAY_AMORT + 4 * TOUR_SEQ_AMORT + 6 * TOUR_FIND_AMORT + 4 * TOUR_JOIN_AMORT) * tl := by ring
    rw [heq]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
  have h6 : 160 * len + 1000 ≤ (len + 1) * 2000 * tl := by nlinarith
  nlinarith

private theorem move_nil_cost_le (len mul_ord tl : ℕ) (htl : 1 ≤ tl) :
    100 ≤ (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tl := by
  have h1 : 100 ≤ TOUR_MOVE_MUL + mul_ord := by unfold TOUR_MOVE_MUL; omega
  calc 100 = 1 * 100 * 1 := by ring
    _ ≤ (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tl :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) htl

/-! ## Main verified run theorem for `tourEditMoveBody` -/

/-- Verified amortized run theorem for `tourEditMoveBody [b, recPtr, heap]`. Updates the tour
representation to `s' = tourApplyEdit s (.moveEnds v v' sel.toFinset c)` while keeping `ordStore`
at `s.ord` (ready for `tourCore_commitOrdStore`). -/
theorem tourEditMoveBody_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b recPtr heap pos : ℕ}
    {rankProc sortProc siftProc collectProc rankSortProc splitLoopProc walkFrontProc ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program} {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (C : TourSplayQueryProcs w p)
    (hRank : p.procs[rankProc]? = some (tourSplayRankBody C.splay.splay))
    (hSift : p.procs[siftProc]? = some (ordSiftDownBody siftProc))
    (hSort : p.procs[sortProc]? = some (ordHeapSortBody siftProc))
    (hColl : p.procs[collectProc]? = some tourMoveCollectBody)
    (hRS : p.procs[rankSortProc]? = some (tourMoveRankSortNextBody rankProc sortProc ordOp2))
    (hSplit : p.procs[splitLoopProc]? = some (tourMoveSplitLoopBody C.splay.splay C.detachLeft C.join))
    (hWalk : p.procs[walkFrontProc]? = some (tourWalkFrontBody C.walkProc C.splay.splay))
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    {v v' len : ℕ} {sel : List End} {c : Bool}
    (h : TourCoreAt vCap eCap b s x mem)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) s.ord x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < heap)
    (hrec_tag : mem recPtr = if c then 2 else 1)
    (hrec_v : mem (recPtr + 1) = v) (hrec_v' : mem (recPtr + 2) = v')
    (hrec_len : mem (recPtr + 3) = len) (hsel_len : sel.length = len)
    (hsel_mem : ∀ i (hi : i < len), mem (recPtr + 4 + i) = endKey (sel[i]'(by omega)))
    (hrec_le : recPtr + 4 + len ≤ heap)
    (hrec_out : ∀ a, recPtr ≤ a → a < recPtr + 4 + len → a < b ∨ ordHandleOf b vCap eCap ≤ a)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel.toFinset c))
    (hord_le : ordHandleOf b vCap eCap ≤ heap)
    (hroom : heap + 4 * len + 6 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w)
    (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) :
    let s' := tourApplyEdit s (.moveEnds v v' sel.toFinset c)
    ∃ (hOut : ℕ) (st' : State) (cost : ℕ) (x' : TourConcrete R_ord.τ),
      Runs w p ω (tourEditMoveBody C.splay.splay C.setValNode C.rotateFront
          collectProc rankSortProc splitLoopProc walkFrontProc)
        (startState [b, recPtr, heap] mem pos) (.returned hOut) st' cost ∧
      heap ≤ hOut ∧ hOut ≤ heap + 4 * len + 2 ∧ ZeroFrom st'.mem hOut ∧
      (∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap ≤ a ∧ a < hOut)) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x'.ordX a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) s.ord x'.ordX st'.mem ∧
      TourCoreAt vCap eCap b s' x' st'.mem ∧
      cost + TOUR_PHI_MULT * forestPhi x'.trees + R_ord.phi (ordHandleOf b vCap eCap) x'.ordX st'.mem ≤
        TOUR_PHI_MULT * forestPhi x.trees + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem +
          (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tourLog eCap := by
  classical
  intro s'
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (x.numNodes + 2) + 1 ≤ 2 * tourLog eCap := tourLog_of_le h.numNodes_le
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel_cap⟩
  have he' : TourEditValid vCap eCap s (.moveEnds v v' sel.toFinset c) :=
    ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel_cap⟩
  have hvalid' := tourValid_applyEdit_moveEnds h.valid he'
  have hhdr := h.header
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hrec_w : recPtr + 4 + len < 2 ^ w := by omega
  set s0 : State := startState [b, recPtr, heap] mem pos
  set tag := if c then 2 else 1
  set feV := mem (firstEndBase b + v)
  set r01 := Function.update s0.regs 3 tag
  set r02 := Function.update r01 4 v
  set r03 := Function.update r02 5 v'
  set r04 := Function.update r03 6 len
  set r05 := Function.update r04 7 (recPtr + 4)
  set r06 := Function.update r05 8 (firstEndBase b)
  set r07 := Function.update r06 8 feV
  have ha3 : Runs w p ω (.assign 3 (.load (.reg 1))) s0 .normal ⟨mem, r01, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨tag, by simp [Expr.eval, s0, startState, hrec_tag, tag], rfl, rfl, rfl⟩
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 1) (off := 1)
    (b := recPtr) (val := v) (st := ⟨mem, r01, pos⟩) (by simp [r01, s0, startState])
    (by omega) (by omega) hrec_v
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 1) (off := 2)
    (b := recPtr) (val := v') (st := ⟨mem, r02, pos⟩) (by simp [r02, r01, s0, startState])
    (by omega) (by omega) hrec_v'
  have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 1) (off := 3)
    (b := recPtr) (val := len) (st := ⟨mem, r03, pos⟩) (by simp [r03, r02, r01, s0, startState])
    (by omega) (by omega) hrec_len
  have ha7 : Runs w p ω (.assign 7 (.bin .add (.reg 1) (.const 4))) ⟨mem, r04, pos⟩ .normal ⟨mem, r05, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨recPtr + 4, by simp [Expr.eval, r04, r03, r02, r01, s0, startState, BinOp.eval,
      (by omega : 4 < 2 ^ w), (by omega : recPtr + 4 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha8a := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_FIRST_END)
    (b := b) (val := firstEndBase b) (st := ⟨mem, r05, pos⟩) (by simp [r05, r04, r03, r02, r01, s0, startState])
    (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega) hhdr.2.2.2.2.1
  have ha8b := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 8) (rIdx := 4)
    (base := firstEndBase b) (idx := v) (val := feV) (st := ⟨mem, r06, pos⟩)
    (by simp [r06]) (by simp [r06, r05, r04, r03, r02])
    (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) rfl
  cases hord_v : s.ord v with
  | nil =>
    have hfe0 : feV = 0 := by simp [feV, h.firstEnd_mem v hvLt, hord_v]
    have hcond : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨mem, r07, pos⟩ = some 1 := by
      simp [Expr.eval, r07, hfe0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    set r08 := Function.update r07 9 (isRootBase b vCap)
    set mem1 := Function.update mem (isRootBase b vCap + v') 1
    have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_IS_ROOT)
      (b := b) (val := isRootBase b vCap) (st := ⟨mem, r07, pos⟩)
      (by simp [r07, r06, r05, r04, r03, r02, r01, s0, startState])
      (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hhdr.2.2.2.2.2.1
    have hst : Runs w p ω (.store (.bin .add (.reg 9) (.reg 5)) (.const 1))
        ⟨mem, r08, pos⟩ .normal ⟨mem1, r08, pos⟩ 5 :=
      runs_store_iff.mpr ⟨isRootBase b vCap + v', 1,
        by simp [Expr.eval, r08, r07, r06, r05, r04, r03, BinOp.eval,
          (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : isRootBase b vCap + v' < 2 ^ w)],
        by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem1, r08, pos⟩) (r := 2) (v := heap)
      (by simp [r08, r07, r06, r05, r04, r03, r02, r01, s0, startState])
    obtain ⟨_, _, hcore'⟩ := tourMove_empty_core h he' hord_v
    have hOrd1 := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord x.ordX mem mem1 fun a ha => by
      have hge := hordGe a ha; dsimp only [mem1]
      exact (Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hge ⊢; omega) _ _).symm
    refine ⟨heap, ⟨mem1, r08, pos⟩, _, { x with compTree := Function.update x.compTree v' none },
      tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6
        (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8a (tour_runs_seq_normal ha8b
          (tour_runs_cond_true hcond (by omega) (tour_runs_seq_normal ha9 (tour_runs_seq_normal hst hret))))))))),
      le_refl _, by omega,
      fun a ha => by dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hzero a ha,
      fun a _ ha2 _ => by
        dsimp only [mem1]
        have h1 : b ≤ isRootBase b vCap + v' := by simp [isRootBase]; omega
        have h2 : isRootBase b vCap + v' < ordHandleOf b vCap eCap := by simp [isRootBase, ordHandleOf, tourFixedSize]; omega
        exact Function.update_of_ne (by rcases ha2 with h0 | h0 <;> omega) _ _,
      fun _ ha => Or.inl ha, hordGe, hOrd1.1 hordRep, hcore', ?_⟩
    rw [← hOrd1.2]
    have hnilc := move_nil_cost_le len mul_ord (tourLog eCap) htl
    clear * - hnilc; simp only [Expr.size]; omega
  | cons aHead aTail =>
    have hhead : (s.ord v).head? = some aHead := by simp [hord_v]
    have haHead_mem : aHead ∈ s.ord v := by simp [hord_v]
    have hfeV_eq : feV = x.nodeOf (endKey aHead) := by simp [feV, h.firstEnd_mem v hvLt, hhead]
    obtain ⟨_, _, _, _, hfe1, _, _, t0, rest, hct_r, hperm_r, ht0_map, hfe_t0⟩ :=
      h.mem_compTree_of_active haHead_mem
    have hfeV_nz : feV ≠ 0 := by omega
    have hcond_fe : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨mem, r07, pos⟩ = some 0 := by
      simp [Expr.eval, r07, hfeV_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
    -- Phase 1: split phase (`tourMoveSplitPhase_exec`)
    obtain ⟨m, hOut, tKeep?, tMove?, s5, ordX3, st5, cPhase, A, hrunPh, hm_le, hhOut_ge, hhOut_le, hzero5,
      hr50, hr52, hr53, hr54, hr55, hr59, hr510, hr511, hr512, hr513, hr515, hr516, hr517,
      hA_len, hA_mem, hA_in, hA_sur, hst5_lt_nb, hst5_fr_heap, hn5, hinv5, hvals5,
      hperm_nodes5, hKeep_map5, hMove_map5, hval5_in, hval5_out, hOrd3_foot, hOrd3_ge, hOrd5_rep, hcPhase⟩ :=
      tourMoveSplitPhase_exec (rIn := r07) (pos := pos) C hRank hSift hSort hColl hRS hSplit hOrdImpl hop2 ω
        h hordRep hordGe hordFoot hord_v hperm_r ht0_map hfe_t0 hsel_len hsel_mem hrec_le hrec_out he'
        (by simp [r07, r06, r05, r04, r03, r02, r01, s0, startState])
        (by simp [r07, r06, r05, r04, r03, r02, r01, s0, startState])
        (by simp [r07, r06, r05, r04, r03, r02, r01, tag])
        (by simp [r07, r06, r05, r04, r03, r02]) (by simp [r07, r06, r05, r04, r03])
        (by simp [r07, r06, r05, r04]) (by simp [r07, r06, r05]) (by simp [r07, hfeV_eq])
        hord_le hroom hw hwide hzero
    -- Phase 2: owners + `firstEnd` (`tourMoveOwners_exec`)
    obtain ⟨tKeep6?, tMove6?, s6, st6, cOwn, hrunOwn, hr6_lt, hr6_16, hr6_17, hhdK6, hhdM6,
      hn6, hzero6, hinv6, hvals6, hK6_list, hM6_list, hval6, hfr6, hhdr6, hno6, hko6, hir6, hmk6,
      hfe6, hsov6, hvos6, heo6, hcOwn⟩ :=
      tourMoveOwners_exec (v := v) (v' := v') (c := c) (pairsPtr := heap) (m := m) (hOut := hOut)
        (st0 := st5) C.toTourSplayCoreProcs hWalk ω h hvLt hv'Lt hne hA_len hA_mem
        (fun u hu => let ⟨a1, a2, _, _⟩ := hA_in u hu; ⟨a1, a2⟩)
        hst5_lt_nb hn5 hinv5 hvals5 hr50 hr52 hr53 hr54 hr55 hr59 hr510 hr512 hr513 hr515 hr516 hr517
        hord_le (by omega) (by omega) hw hwide hzero5
    have hfe6_exact : ∀ w' < vCap, st6.mem (firstEndBase b + w') =
        match (s'.ord w').head? with | none => 0 | some e => x.nodeOf (endKey e) := by
      intro w' hw'; rw [hfe6 w' hw']
      by_cases h1 : w' = v'
      · subst h1; simp only [↓reduceIte]; rw [← hhdM6]
        cases ho : s'.ord w' with
        | nil =>
          have hnil : optList tMove6? = [] := List.map_eq_nil_iff.mp (by rw [hM6_list, hMove_map5, (fullTour_eq_nil_iff hvalid'.compat w').mpr ho])
          simp [hnil]
        | cons e es =>
          have hhd_ft := fullTour_head? hvalid'.compat w' (a := e) (by rw [ho]; rfl)
          rw [← hMove_map5, ← hM6_list, List.head?_map] at hhd_ft
          cases hl : optList tMove6? with
          | nil => simp [hl] at hhd_ft
          | cons id ids =>
            simp only [hl, List.head?_cons, Option.map_some, Option.some.injEq] at hhd_ft
            have hid_t0 : id ∈ t0.toList := hperm_nodes5.mem_iff.mp (List.mem_append_right _ (by rw [← hM6_list, hl]; simp))
            have hid_in := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, hperm_r.mem_iff.mpr (by simp), hid_t0⟩)
            have hkeq : x.keyOf id = endKey e := by rw [← hhd_ft, endKey_endOfKey']
            simp only [List.head?_cons, Option.getD_some]
            rw [← hkeq, (h.keyOf_mem id hid_in.1 hid_in.2).2.2]
      · by_cases h2 : w' = v
        · subst h2; simp only [h1, ↓reduceIte]; rw [← hhdK6]
          cases ho : s'.ord w' with
          | nil =>
            have hnil : optList tKeep6? = [] := List.map_eq_nil_iff.mp (by rw [hK6_list, hKeep_map5, (fullTour_eq_nil_iff hvalid'.compat w').mpr ho])
            simp [hnil]
          | cons e es =>
            have hhd_ft := fullTour_head? hvalid'.compat w' (a := e) (by rw [ho]; rfl)
            rw [← hKeep_map5, ← hK6_list, List.head?_map] at hhd_ft
            cases hl : optList tKeep6? with
            | nil => simp [hl] at hhd_ft
            | cons id ids =>
              simp only [hl, List.head?_cons, Option.map_some, Option.some.injEq] at hhd_ft
              have hid_t0 : id ∈ t0.toList := hperm_nodes5.mem_iff.mp (List.mem_append_left _ (by rw [← hK6_list, hl]; simp))
              have hid_in := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, hperm_r.mem_iff.mpr (by simp), hid_t0⟩)
              have hkeq : x.keyOf id = endKey e := by rw [← hhd_ft, endKey_endOfKey']
              simp only [List.head?_cons, Option.getD_some]
              rw [← hkeq, (h.keyOf_mem id hid_in.1 hid_in.2).2.2]
        · simp [h1, h2, h.firstEnd_mem w' hw', s', tourApplyEdit, applyOrdEdit]; rfl
    -- Phase 3: roots update (`tourMoveRoots_exec`)
    obtain ⟨tKeep7?, tMove7?, s7, st7, cRoots, hrunRoots, hr7_15, hn7, hzero7, hfr7, hir7, hinv7,
      hperm7, hKeep_map7, hMove_map7, hval7_act, hval7_oth, hcRoots⟩ :=
      tourMoveRoots_exec (sel := sel.toFinset) (c := c) C ω h he' (hperm_r.mem_iff.mpr (by simp)) ht0_map
        hhdr6 hfe6_exact (fun u hu => (hir6 u hu).trans (h.isRoot_mem u hu)) hn6 hinv6 hvals6 hhdK6 hhdM6
        (by rw [hK6_list, hM6_list]; exact hperm_nodes5) (by rw [hK6_list]; exact hKeep_map5)
        (by rw [hM6_list]; exact hMove_map5)
        (fun hvR u hu => by rw [hval6 u hu]; exact hval5_in hvR u hu)
        (fun hvNR u hu => by rw [hval6 u hu]; exact hval5_out hvNR u hu)
        (by rw [hr6_lt 0 (by omega), hr50]) (by rw [hr6_lt 4 (by omega), hr54])
        (by rw [hr6_lt 5 (by omega), hr55]) (by rw [hr6_lt 9 (by omega), hr59])
        (by rw [hr6_lt 10 (by omega), hr510]) (by rw [hr6_lt 11 (by omega), hr511])
        (by rw [hr6_lt 15 (by omega), hr515]) hr6_16 hr6_17 (by omega) (by omega) hw hwide hzero6
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := st7) (r := 15) (v := hOut) hr7_15
    -- Reconstruct `TourCoreAt` via `tourMove_core`
    have hst7_eq_st6 : ∀ a < nodesBase b vCap eCap, a ≠ isRootBase b vCap + v → a ≠ isRootBase b vCap + v' →
        st7.mem a = st6.mem a := fun a ha h1 h2 =>
      hfr7 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega) (not_inRecords_of_lt_nodesBase ha) h1 h2
    have hhdr7 : TourHeaderAt vCap eCap b x.numNodes st7.mem := by
      rcases hhdr6 with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14⟩
      have hf : ∀ k < 16, st7.mem (b + k) = st6.mem (b + k) := fun k hk =>
        hst7_eq_st6 (b + k) (by simp [nodesBase]; omega) (by simp [isRootBase]; omega) (by simp [isRootBase]; omega)
      exact ⟨(hf _ (by decide)).trans z0, (hf _ (by decide)).trans z1, (hf _ (by decide)).trans z2,
        (hf _ (by decide)).trans z3, (hf _ (by decide)).trans z4, (hf _ (by decide)).trans z5,
        (hf _ (by decide)).trans z6, (hf _ (by decide)).trans z7, (hf _ (by decide)).trans z8,
        (hf _ (by decide)).trans z9, (hf _ (by decide)).trans z10, (hf _ (by decide)).trans z11,
        (hf _ (by decide)).trans z12, (hf _ (by decide)).trans z13, (hf _ (by decide)).trans z14⟩
    set sv := x.slotOf v
    set sv' := x.slotOf v'
    set slotOf' := if c then Function.update (Function.update x.slotOf v sv') v' sv else x.slotOf
    set vertOf' := if c then Function.update (Function.update x.vertOf sv v') sv' v else x.vertOf
    have hbij' : ∀ w' < vCap, slotOf' w' < vCap ∧ vertOf' (slotOf' w') = w' ∧ slotOf' (vertOf' w') = w' := by
      cases c with
      | true => simpa [slotOf', vertOf', sv, sv'] using tourMove_slotSwap_bij h.slot_bij hvLt hv'Lt hne
      | false => simpa [slotOf', vertOf'] using h.slot_bij
    have heo7_act : ∀ w' < vCap, ∀ e ∈ s'.ord w', st7.mem (endOwnerBase b vCap eCap + endKey e) = slotOf' w' + 1 := by
      intro w' hw' e he_ord
      have he_lt : endKey e < 2 * eCap := endKey_lt_two_mul (hvalid'.ordWithin.2.2 w' e he_ord)
      rw [hst7_eq_st6 _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)
        (by simp [endOwnerBase, isRootBase]; omega), heo6 (endKey e) he_lt]
      have hexA_iff : (∃ u ∈ A, x.keyOf u = endKey e) ↔ e ∈ s.ord v ∧ e ∈ sel := by
        constructor
        · rintro ⟨u, huA, hku⟩
          have ⟨_, _, h3, h4⟩ := hA_in u huA
          rw [hku, endOfKey_endKey] at h3 h4; exact ⟨h3, h4⟩
        · rintro ⟨hev, hes⟩
          have ⟨_, _, _, _, _, _, hk_eq, _⟩ := h.mem_compTree_of_active hev
          exact ⟨x.nodeOf (endKey e), hA_sur e hev hes, hk_eq⟩
      by_cases h1 : w' = v
      · subst h1
        have hmem_v : e ∈ s.ord w' ∧ movedBy sel.toFinset c e = false := by
          simpa [s', tourApplyEdit, applyOrdEdit] using he_ord
        cases c with
        | true =>
          have hes : e ∈ sel := by simpa [movedBy] using hmem_v.2
          rw [ite_eq_left_iff.mpr fun h => absurd (hexA_iff.mpr ⟨hmem_v.1, hes⟩) h]; simp [slotOf', hne, sv']
        | false =>
          have hes : e ∉ sel := by simpa [movedBy] using hmem_v.2
          rw [ite_eq_right_iff.mpr fun h => absurd (hexA_iff.mp h).2 hes]
          simpa [slotOf'] using (h.active_end w' hw' e hmem_v.1).2
      · by_cases h2 : w' = v'
        · subst h2
          have hmem_v' : e ∈ s.ord v ∧ movedBy sel.toFinset c e = true := by
            simpa [s', tourApplyEdit, applyOrdEdit, hne.symm, hord_v'] using he_ord
          cases c with
          | true =>
            have hes : e ∉ sel := by simpa [movedBy] using hmem_v'.2
            rw [ite_eq_right_iff.mpr fun h => absurd (hexA_iff.mp h).2 hes]
            simpa [slotOf', sv] using (h.active_end v hvLt e hmem_v'.1).2
          | false =>
            have hes : e ∈ sel := by simpa [movedBy] using hmem_v'.2
            rw [ite_eq_left_iff.mpr fun h => absurd (hexA_iff.mpr ⟨hmem_v'.1, hes⟩) h]; simp [slotOf', sv']
        · have he_old : e ∈ s.ord w' := by simpa [s', tourApplyEdit, applyOrdEdit, h1, h2] using he_ord
          have hnotv : e ∉ s.ord v := fun hv => h1 (h.valid.compat.unique w' v e he_old hv)
          rw [ite_eq_right_iff.mpr fun h => absurd (hexA_iff.mp h).1 hnotv]
          have hslot_eq : slotOf' w' = x.slotOf w' := by cases c <;> simp [slotOf', h1, h2]
          rw [hslot_eq]; exact (h.active_end w' hw' e he_old).2
    have heo7_inact : ∀ k < 2 * eCap, (∀ w', endOfKey k ∉ s'.ord w') → st7.mem (endOwnerBase b vCap eCap + k) = 0 := by
      intro k hk hno
      rw [hst7_eq_st6 _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)
        (by simp [endOwnerBase, isRootBase]; omega), heo6 k hk]
      have hno0 : ∀ w', endOfKey k ∉ s.ord w' := fun w' hw' => by
        by_cases h1 : w' = v
        · subst h1
          by_cases hp : movedBy sel.toFinset c (endOfKey k) = true
          · exact hno v' (by simp [s', tourApplyEdit, applyOrdEdit, hne.symm, hord_v', hw', hp])
          · have hpf : movedBy sel.toFinset c (endOfKey k) = false := by cases hm : movedBy sel.toFinset c (endOfKey k) <;> simp_all
            exact hno w' (by simp [s', tourApplyEdit, applyOrdEdit, hw', hpf])
        · have h2 : w' ≠ v' := fun heq => by rw [heq, hord_v'] at hw'; simp at hw'
          exact hno w' (by simp [s', tourApplyEdit, applyOrdEdit, h1, h2, hw'])
      rw [ite_eq_right_iff.mpr (by rintro ⟨u, huA, hku⟩; exact absurd (hku ▸ (hA_in u huA).2.2.1) (hno0 v))]
      exact h.inactive_owner k hk hno0
    have hcore7 : TourCoreAt vCap eCap b s'
        { ordX := ordX3, numNodes := x.numNodes, st := s7, trees := optTrees tKeep7? ++ optTrees tMove7? ++ rest,
          nodeOf := x.nodeOf, keyOf := x.keyOf,
          compTree := Function.update
            (Function.update x.compTree (if s'.rf.F.Connected v (s.rf.root v) then s.rf.root v else v) tKeep7?)
            (if s'.rf.F.Connected v (s.rf.root v) then v' else s.rf.root v) tMove7?,
          slotOf := slotOf', vertOf := vertOf' } st7.mem := by
      have hx3 : TourCoreAt vCap eCap b s { x with ordX := ordX3 } mem :=
        { valid := h.valid, header := h.header, numNodes_le := h.numNodes_le,
          nodeOf_mem := h.nodeOf_mem, nodeOf_keyOf := h.nodeOf_keyOf, keyOf_mem := h.keyOf_mem,
          firstEnd_mem := h.firstEnd_mem, isRoot_mem := h.isRoot_mem, slot_bij := h.slot_bij,
          slotOf_mem := h.slotOf_mem, vertOf_mem := h.vertOf_mem, active_end := h.active_end,
          inactive_owner := h.inactive_owner, markArr_zero := h.markArr_zero, nodesAt := h.nodesAt,
          forestInv := h.forestInv, nodes_exact := h.nodes_exact, comp_none := h.comp_none,
          comp_some := h.comp_some, tree_class := h.tree_class, inactive_single := h.inactive_single,
          val_active := h.val_active, val_inactive_rt := h.val_inactive_rt, val_unused_rt := h.val_unused_rt }
      exact tourMove_core hx3 he' (by simp [hord_v]) hct_r hperm_r ht0_map hhdr7
        (fun k hk => (hst7_eq_st6 _ (by simp [nodeOfEndBase, nodesBase]; omega) (by simp [nodeOfEndBase, isRootBase]; omega)
          (by simp [nodeOfEndBase, isRootBase]; omega)).trans (hno6 k hk))
        (fun u h1 h2 => (hst7_eq_st6 _ (by dsimp only at h2; have := h.numNodes_le; simp [keyOfNodeBase, nodesBase]; omega)
          (by simp [keyOfNodeBase, isRootBase]; omega) (by simp [keyOfNodeBase, isRootBase]; omega)).trans (hko6 u h1 h2))
        (fun w' hw' => (hst7_eq_st6 _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, isRootBase]; omega)
          (by simp [firstEndBase, isRootBase]; omega)).trans (hfe6_exact w' hw'))
        hir7 hbij'
        (fun w' hw' => by rw [hst7_eq_st6 _ (by simp [slotOfVertBase, nodesBase]; omega)
          (by simp [slotOfVertBase, isRootBase]; omega) (by simp [slotOfVertBase, isRootBase]; omega)]; exact hsov6 w' hw')
        (fun sl hsl => by rw [hst7_eq_st6 _ (by simp [vertOfSlotBase, nodesBase]; omega)
          (by simp [vertOfSlotBase, isRootBase]; omega) (by simp [vertOfSlotBase, isRootBase]; omega)]; exact hvos6 sl hsl)
        heo7_act heo7_inact
        (fun k hk => (hst7_eq_st6 _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, isRootBase]; omega)
          (by simp [markArrBase, isRootBase]; omega)).trans (hmk6 k hk))
        hn7 hinv7 hperm7 hKeep_map7 hMove_map7 hval7_act hval7_oth
    have hOrd7 := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord ordX3 st5.mem st7.mem fun a ha => by
      have ha_ge := hOrd3_ge a ha
      have ha_lt : a < hOut := by
        rcases hOrd3_foot a ha with h1a | ⟨_, h2a⟩
        · exact lt_of_lt_of_le (hordFoot a h1a) (by omega)
        · omega
      have ha_nrec : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hin => by
        have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega
      have ha_ne1 : a ≠ isRootBase b vCap + v := by simp [isRootBase, ordHandleOf, tourFixedSize] at ha_ge ⊢; omega
      have ha_ne2 : a ≠ isRootBase b vCap + v' := by simp [isRootBase, ordHandleOf, tourFixedSize] at ha_ge ⊢; omega
      exact (hfr6 a (Or.inr ⟨ha_ge, ha_lt⟩)).symm.trans (hfr7 a ha_lt ha_nrec ha_ne1 ha_ne2).symm
    have hframe_out : ∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st7.mem a = mem a := by
      intro a ha ha_out ha_noOrd
      have ha_nrec : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hin => by
        have := inRecords_lt_ordHandle_of_le h.numNodes_le hin; rcases ha_out with h1 | h2
        · simp [nodesBase] at this; omega
        · omega
      have ha_ne1 : a ≠ isRootBase b vCap + v := by
        have h1 : b ≤ isRootBase b vCap + v := by simp [isRootBase]; omega
        have h2 : isRootBase b vCap + v < ordHandleOf b vCap eCap := by simp [isRootBase, ordHandleOf, tourFixedSize]; omega
        rcases ha_out with h0 | h0 <;> omega
      have ha_ne2 : a ≠ isRootBase b vCap + v' := by
        have h1 : b ≤ isRootBase b vCap + v' := by simp [isRootBase]; omega
        have h2 : isRootBase b vCap + v' < ordHandleOf b vCap eCap := by simp [isRootBase, ordHandleOf, tourFixedSize]; omega
        rcases ha_out with h0 | h0 <;> omega
      rw [hfr7 a (by omega) ha_nrec ha_ne1 ha_ne2, hfr6 a (ha_out.imp id fun h => ⟨h, by omega⟩),
        hst5_fr_heap a ha ha_nrec ha_noOrd]
    refine ⟨hOut, st7, _, _,
      tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6
        (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8a (tour_runs_seq_normal ha8b
          (tour_runs_cond_false hcond_fe
            (tour_runs_seq_normal hrunPh (tour_runs_seq_normal hrunOwn (tour_runs_seq_normal hrunRoots hret)))))))))),
      by omega, by omega, hzero7, hframe_out,
      fun a ha => (hOrd3_foot a ha).imp id fun ⟨h1a, h2a⟩ => ⟨by omega, by omega⟩,
      hOrd3_ge, hOrd7.1 hOrd5_rep, hcore7, ?_⟩
    have hphi0 : forestPhi x.trees = forestPhi (t0 :: rest) := forestPhi_perm hperm_r
    rw [hphi0, ← hOrd7.2]
    have hlog_mul : ((m + 1) * TOUR_MOVE_STEP_AMORT + TOUR_SPLAY_AMORT + 2 * TOUR_SEQ_AMORT +
        3 * TOUR_FIND_AMORT + 2 * TOUR_JOIN_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
      ((m + 1) * TOUR_MOVE_STEP_AMORT + TOUR_SPLAY_AMORT + 2 * TOUR_SEQ_AMORT +
        3 * TOUR_FIND_AMORT + 2 * TOUR_JOIN_AMORT) * (2 * tourLog eCap) :=
      Nat.mul_le_mul_left _ hlog
    have hcomb := move_cost_combine len m mul_ord (tourLog eCap) hm_le htl
    clear * - hcPhase hcOwn hcRoots hm_le hlog_mul hcomb
    simp only [Expr.size] at *
    linarith

end MinCostFlow.SparseCore.Program
