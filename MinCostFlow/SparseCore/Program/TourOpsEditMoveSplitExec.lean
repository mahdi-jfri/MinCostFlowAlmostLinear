module

public import MinCostFlow.SparseCore.Program.TourOpsEditMoveSort
public import MinCostFlow.SparseCore.Program.TourOpsEditMoveRoots
import Mathlib.Tactic

/-!
# Split-phase execution (`tourMoveSplitPhase_exec`) for `moveEnds` (Op 0)

Implements and verifies `tourMoveSplitPhaseStmt`: starting after loading record fields and `feV`
(when `s.ord v ≠ []`), decodes `sv`, collects unique active selected ends of `v`, clears `rootTag`
if `v ∈ R`, rotates `feV` to the front, runs `rankSortNext`, splays `feV`, runs `splitLoop`,
swaps `(tA?, tB?)` if `tag ≠ 2`, and advances `hOut := h2 + 2`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM statement for the split phase -/

/-- Split-phase statement for `moveEnds` (when `feV ≠ 0`). Expects registers:
`r0 = b, r1 = recPtr, r2 = heap, r3 = tag, r4 = v, r5 = v', r6 = len, r7 = selPtr, r8 = feV`.
Outputs `r9 = nodesBase, r10 = fuel, r11 = irV, r12 = sv, r13 = m, r14 = nxtPtr, r15 = hOut,
r16 = optRoot tKeep?, r17 = optRoot tMove?`. -/
def tourMoveSplitPhaseStmt
    (splayProc setValProc rotFrontProc collectProc rankSortProc splitLoopProc : ℕ) : Stmt :=
  .assign 12 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
  .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 13))) ;;
  .assign 12 (.load (.bin .add (.reg 12) (.reg 4))) ;;
  .cond (.reg 12)
    (.assign 12 (.bin .sub (.reg 12) (.const 1)))
    (.assign 12 (.reg 4)) ;;
  .call 13 collectProc [.reg 0, .reg 12, .reg 7, .reg 6, .reg 2] ;;
  .assign 14 (.bin .add (.reg 2) (.bin .add (.reg 13) (.reg 13))) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 13)) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
  .assign 11 (.load (.bin .add (.reg 11) (.reg 4))) ;;
  .cond (.reg 11)
    (.assign 16 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 8))) ;;
     .assign 17 (.load (.bin .add (.reg 16) (.const 9))) ;;
     .assign 18 (.load (.bin .add (.reg 16) (.const 10))) ;;
     .assign 19 (.const 0) ;;
     .call 20 setValProc [.reg 9, .reg 8, .reg 17, .reg 18, .reg 19, .reg 10, .reg 15])
    .nop ;;
  .call 20 rotFrontProc [.reg 9, .reg 8, .reg 10, .reg 15] ;;
  .call 15 rankSortProc [.reg 0, .reg 4, .reg 8, .reg 2, .reg 14, .reg 13, .reg 15] ;;
  .call 18 splayProc [.reg 9, .reg 8, .reg 10, .reg 15] ;;
  .call 18 splitLoopProc [.reg 9, .reg 8, .reg 2, .reg 14, .reg 13, .reg 10, .reg 15] ;;
  .assign 16 (.load (.reg 15)) ;;
  .assign 17 (.load (.bin .add (.reg 15) (.const 1))) ;;
  .cond (.bin .eq (.reg 3) (.const 2))
    .nop
    (.assign 18 (.reg 16) ;; .assign 16 (.reg 17) ;; .assign 17 (.reg 18)) ;;
  .assign 15 (.bin .add (.reg 15) (.const 2))

theorem tourMoveSplitPhaseStmt_noRand (sp sV rF cP rS sL : ℕ) :
    (tourMoveSplitPhaseStmt sp sV rF cP rS sL).NoRand := by
  simp [tourMoveSplitPhaseStmt, Stmt.NoRand]

/-! ## Local helpers -/

private theorem runs_call_regs7 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ}
    (r0 r1 r2 r3 r4 r5 r6 : ℕ) {st st₁ : State} {v0 v1 v2 v3 v4 v5 v6 : ℕ} {body : Stmt}
    {o₁ : Outcome} {c₁ : ℕ} (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2) (h3 : st.regs r3 = v3)
    (h4 : st.regs r4 = v4) (h5 : st.regs r5 = v5) (h6 : st.regs r6 = v6)
    (hrun : Runs w p ω body (startState [v0, v1, v2, v3, v4, v5, v6] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5, .reg r6]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (8 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5, .reg r6]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5, h6]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

private theorem list_eq_of_map_inj {α β : Type*} {f : α → β} {l₁ l₂ : List α}
    (hmap : l₁.map f = l₂.map f) (hinj : ∀ a ∈ l₁, ∀ b ∈ l₂, f a = f b → a = b) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a as ih =>
    cases l₂ with
    | nil => simp at hmap
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      exact congrArg₂ List.cons (hinj a (by simp) b (by simp) hmap.1)
        (ih hmap.2 fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))

private theorem perm_filter_append_filter_not {α : Type*} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p ++ xs.filter fun z => !p z).Perm xs
  | [] => by simp
  | a :: as => by
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact (List.perm_middle).trans ((perm_filter_append_filter_not p as).cons a)
    · simp only [List.filter_cons, hp, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.cons_append]
      exact (perm_filter_append_filter_not p as).cons a

/-! ## Execution theorem for `tourMoveSplitPhaseStmt` -/

open Classical in
/-- Verified amortized execution of `tourMoveSplitPhaseStmt` when `s.ord v = aHead :: aTail`. -/
theorem tourMoveSplitPhase_exec {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b recPtr heap pos : ℕ}
    {rankProc sortProc siftProc collectProc rankSortProc splitLoopProc ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program} {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (C : TourSplayQueryProcs w p)
    (hRank : p.procs[rankProc]? = some (tourSplayRankBody C.splay.splay))
    (hSift : p.procs[siftProc]? = some (ordSiftDownBody siftProc))
    (hSort : p.procs[sortProc]? = some (ordHeapSortBody siftProc))
    (hColl : p.procs[collectProc]? = some tourMoveCollectBody)
    (hRS : p.procs[rankSortProc]? = some (tourMoveRankSortNextBody rankProc sortProc ordOp2))
    (hSplit : p.procs[splitLoopProc]? = some (tourMoveSplitLoopBody C.splay.splay C.detachLeft C.join))
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ} {rIn : ℕ → ℕ}
    {v v' len : ℕ} {sel : List End} {c : Bool} {aHead : End} {aTail : List End}
    {t0 : AuxTree} {rest : List AuxTree}
    (h : TourCoreAt vCap eCap b s x mem)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) s.ord x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < heap)
    (hord_v : s.ord v = aHead :: aTail)
    (ht0_perm : x.trees.Perm (t0 :: rest))
    (ht0_map : t0.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v))
    (hfe_t0 : x.nodeOf (endKey aHead) ∈ t0.toList)
    (hsel_len : sel.length = len)
    (hsel_mem : ∀ i (hi : i < len), mem (recPtr + 4 + i) = endKey (sel[i]'(by omega)))
    (hrec_le : recPtr + 4 + len ≤ heap)
    (hrec_out : ∀ a, recPtr ≤ a → a < recPtr + 4 + len → a < b ∨ ordHandleOf b vCap eCap ≤ a)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel.toFinset c))
    (hr0 : rIn 0 = b) (hr2 : rIn 2 = heap) (hr3 : rIn 3 = if c then 2 else 1)
    (hr4 : rIn 4 = v) (hr5 : rIn 5 = v') (hr6 : rIn 6 = len) (hr7 : rIn 7 = recPtr + 4)
    (hr8 : rIn 8 = x.nodeOf (endKey aHead))
    (hord_le : ordHandleOf b vCap eCap ≤ heap)
    (hroom : heap + 4 * len + 6 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w)
    (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) :
    let s' := tourApplyEdit s (.moveEnds v v' sel.toFinset c)
    ∃ (m hOut : ℕ) (tKeep? tMove? : Option AuxTree) (s5 : SplayState TourVal TourSum Unit)
      (ordX3 : R_ord.τ) (st5 : State) (cPhase : ℕ) (A : List ℕ),
      Runs w p ω (tourMoveSplitPhaseStmt C.splay.splay C.setValNode C.rotateFront
          collectProc rankSortProc splitLoopProc)
        ⟨mem, rIn, pos⟩ .normal st5 cPhase ∧
      m ≤ len ∧ heap + 3 * m + 2 ≤ hOut ∧ hOut ≤ heap + 4 * m + 2 ∧ ZeroFrom st5.mem hOut ∧
      st5.regs 0 = b ∧ st5.regs 2 = heap ∧ st5.regs 3 = (if c then 2 else 1) ∧
      st5.regs 4 = v ∧ st5.regs 5 = v' ∧ st5.regs 9 = nodesBase b vCap eCap ∧
      st5.regs 10 = 2 * eCap + 2 ∧ st5.regs 11 = (if v ∈ s.rf.R then 1 else 0) ∧
      st5.regs 12 = x.slotOf v ∧ st5.regs 13 = m ∧ st5.regs 15 = hOut ∧
      st5.regs 16 = optRoot tKeep? ∧ st5.regs 17 = optRoot tMove? ∧
      A.length = m ∧
      (∀ i (hi : i < A.length), st5.mem (heap + (2 * i + 1)) = A[i]) ∧
      (∀ u ∈ A, 1 ≤ u ∧ u ≤ x.numNodes ∧ endOfKey (x.keyOf u) ∈ s.ord v ∧ endOfKey (x.keyOf u) ∈ sel) ∧
      (∀ z ∈ s.ord v, z ∈ sel → x.nodeOf (endKey z) ∈ A) ∧
      (∀ a < nodesBase b vCap eCap, st5.mem a = mem a) ∧
      (∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st5.mem a = mem a) ∧
      tourLayout.NodesAt st5.mem (nodesBase b vCap eCap) x.numNodes s5 ∧
      TourForestInv x.numNodes s5 (optTrees tKeep? ++ optTrees tMove? ++ rest) ∧
      TourValsOk w x.numNodes s5 ∧
      (optList tKeep? ++ optList tMove?).Perm t0.toList ∧
      (optList tKeep?).map (fun id => endOfKey (x.keyOf id)) =
        fullTour s'.ord s'.rf.F (tourValid_applyEdit_moveEnds h.valid he).compat.forest v ∧
      (optList tMove?).map (fun id => endOfKey (x.keyOf id)) =
        fullTour s'.ord s'.rf.F (tourValid_applyEdit_moveEnds h.valid he).compat.forest v' ∧
      (v ∈ s.rf.R → ∀ u ≤ x.numNodes,
        (u ∈ t0.toList → (s5.nodes u).val = { (x.st.nodes u).val with rootTag := 0 }) ∧
        (u ∉ t0.toList → (s5.nodes u).val = (x.st.nodes u).val)) ∧
      (v ∉ s.rf.R → ∀ u ≤ x.numNodes, (s5.nodes u).val = (x.st.nodes u).val) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX3 a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap + 3 * m ≤ a ∧ a < hOut - 2)) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX3 a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) s.ord ordX3 st5.mem ∧
      cPhase + TOUR_PHI_MULT * forestPhi (optTrees tKeep? ++ optTrees tMove? ++ rest) +
          R_ord.phi (ordHandleOf b vCap eCap) ordX3 st5.mem ≤
        TOUR_PHI_MULT * forestPhi (t0 :: rest) + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem +
          (m + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tourLog eCap +
          ((m + 1) * TOUR_MOVE_STEP_AMORT + TOUR_SPLAY_AMORT + TOUR_SEQ_AMORT + TOUR_FIND_AMORT) *
            (Nat.log 2 (x.numNodes + 2) + 1) + 130 * len + 350 := by
  intro s'
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel_cap⟩
  have he' : TourEditValid vCap eCap s (.moveEnds v v' sel.toFinset c) :=
    ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel_cap⟩
  have hvalid' := tourValid_applyEdit_moveEnds h.valid he'
  have hhdr := h.header
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hhead : (s.ord v).head? = some aHead := by simp [hord_v]
  have haHead_mem : aHead ∈ s.ord v := by simp [hord_v]
  set feV := x.nodeOf (endKey aHead)
  have ⟨_, _, _, _, hfe1, hfe_le, hfe_key, _⟩ := h.mem_compTree_of_active haHead_mem
  -- Step 1: decode `sv` into `r12` and call `collectProc` on original `mem`
  set rD1 := Function.update rIn 12 (nextArrBase b vCap eCap)
  set rD2 := Function.update rD1 13 eCap
  set rD3 := Function.update rD2 12 (slotOfVertBase b vCap eCap)
  set rawV := mem (slotOfVertBase b vCap eCap + v)
  set rD4 := Function.update rD3 12 rawV
  set rD5 := Function.update rD4 12 (x.slotOf v)
  have hsov_eq : nextArrBase b vCap eCap + 2 * eCap = slotOfVertBase b vCap eCap := by
    simp [nextArrBase, slotOfVertBase]; omega
  have hd1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 0) (off := HDR_NEXT_ARR)
    (b := b) (val := nextArrBase b vCap eCap) (st := ⟨mem, rIn, pos⟩) hr0
    (by simp [HDR_NEXT_ARR]; omega) (by simp [HDR_NEXT_ARR]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hd2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 0) (off := HDR_ECAP)
    (b := b) (val := eCap) (st := ⟨mem, rD1, pos⟩) (by simp [rD1, hr0])
    (by simp only [HDR_ECAP]; omega) (by simp only [HDR_ECAP]; omega) hhdr.2.1
  have hd3 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 13))))
      ⟨mem, rD2, pos⟩ .normal ⟨mem, rD3, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨slotOfVertBase b vCap eCap, by
      simp [Expr.eval, rD2, rD1, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 2 * eCap < 2 ^ w),
        hsov_eq, (by simp [slotOfVertBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : slotOfVertBase b vCap eCap < 2 ^ w)],
      rfl, rfl, rfl⟩
  have hd4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 12) (rIdx := 4)
    (base := slotOfVertBase b vCap eCap) (idx := v) (val := rawV) (st := ⟨mem, rD3, pos⟩)
    (by simp [rD3]) (by simp [rD3, rD2, rD1, hr4])
    (by simp [slotOfVertBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) rfl
  have hd5 : ∃ cD, cD ≤ 6 ∧ Runs w p ω (.cond (.reg 12) (.assign 12 (.bin .sub (.reg 12) (.const 1))) (.assign 12 (.reg 4)))
      ⟨mem, rD4, pos⟩ .normal ⟨mem, rD5, pos⟩ cD := by
    have hdec := h.slotOf_mem v hvLt
    have hsv_lt := (h.slot_bij v hvLt).1
    by_cases hraw0 : rawV = 0
    · have hsv_v : x.slotOf v = v := by simpa [decodeSlot, rawV, hraw0] using hdec.symm
      have hc : (Expr.reg 12).eval w ⟨mem, rD4, pos⟩ = some 0 := by simp [Expr.eval, rD4, hraw0]
      have ha : Runs w p ω (.assign 12 (.reg 4)) ⟨mem, rD4, pos⟩ .normal ⟨mem, rD5, pos⟩ 2 :=
        runs_assign_iff.mpr ⟨v, by simp [Expr.eval, rD4, rD3, rD2, rD1, hr4], rfl,
          by congr 1; funext k; by_cases hk : k = 12 <;> simp [rD5, rD4, hk, hsv_v], rfl⟩
      exact ⟨_, by simp [Expr.size], tour_runs_cond_false hc ha⟩
    · have hsv_sub : rawV - 1 = x.slotOf v := by simpa [decodeSlot, rawV, hraw0] using hdec
      have hc : (Expr.reg 12).eval w ⟨mem, rD4, pos⟩ = some rawV := by simp [Expr.eval, rD4]
      have ha : Runs w p ω (.assign 12 (.bin .sub (.reg 12) (.const 1))) ⟨mem, rD4, pos⟩ .normal ⟨mem, rD5, pos⟩ 4 :=
        runs_assign_iff.mpr ⟨x.slotOf v, by simp [Expr.eval, rD4, BinOp.eval, (by omega : 1 < 2 ^ w), hsv_sub, (by omega : x.slotOf v < 2 ^ w)], rfl, rfl, rfl⟩
      exact ⟨_, by simp [Expr.size], tour_runs_cond_true hc hraw0 ha⟩
  obtain ⟨cD, hcD, hrunD5⟩ := hd5
  obtain ⟨m, stC, cColl, A0, hrunColl, hm_le, hA0_len, hA0_nd, hA0_mem, hA0_in, hA0_sur, hColl_fr, hcColl⟩ :=
    tourMoveCollectBody_runs (pos := pos) ω h hvLt hsel_len hsel_mem
      (fun z hz => hsel_cap z (List.mem_toFinset.mpr hz)) hord_le (Or.inl hrec_le)
      (fun a ha1 ha2 => hrec_out a (by omega) (by omega)) (by omega) (by omega) hw hwide
  have hcallColl := runs_call_regs5 13 0 12 7 6 2 (st := ⟨mem, rD5, pos⟩) hColl
    (by simp [rD5, rD4, rD3, rD2, rD1, hr0]) (by simp [rD5]) (by simp [rD5, rD4, rD3, rD2, rD1, hr7])
    (by simp [rD5, rD4, rD3, rD2, rD1, hr6]) (by simp [rD5, rD4, rD3, rD2, rD1, hr2]) hrunColl
  set rC0 := Function.update rD5 13 m
  set nxtPtr := heap + 2 * m
  set h1 := heap + 3 * m
  set irV := if v ∈ s.rf.R then 1 else 0
  set rC1 := Function.update rC0 14 nxtPtr
  set rC2 := Function.update rC1 15 h1
  set rC3 := Function.update rC2 9 (nodesBase b vCap eCap)
  set rC4 := Function.update rC3 10 (2 * eCap + 2)
  set rC5 := Function.update rC4 11 (isRootBase b vCap)
  set rC6 := Function.update rC5 11 irV
  have hColl_lt : ∀ a < heap, stC.mem a = mem a := fun a ha => hColl_fr a (Or.inl ha)
  have hzeroC : ZeroFrom stC.mem h1 := fun a ha => by
    rw [hColl_fr a (Or.inr (by omega))]; exact hzero a (by omega)
  have hC_nodes : tourLayout.NodesAt stC.mem (nodesBase b vCap eCap) x.numNodes x.st :=
    NodesAt.congr tourLayout h.nodesAt fun a ha => hColl_lt a (lt_of_lt_of_le (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2 hord_le)
  have hOrdC := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord x.ordX mem stC.mem fun a ha =>
    (hColl_lt a (hordFoot a ha)).symm
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 2) (.bin .add (.reg 13) (.reg 13))))
      { stC with regs := rC0 } .normal { stC with regs := rC1 } 6 :=
    runs_assign_iff.mpr ⟨nxtPtr, by
      simp [Expr.eval, rC0, rD5, rD4, rD3, rD2, rD1, hr2, BinOp.eval,
        (by omega : m + m < 2 ^ w), (by omega : heap + (m + m) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 14) (.reg 13)))
      { stC with regs := rC1 } .normal { stC with regs := rC2 } 4 :=
    runs_assign_iff.mpr ⟨h1, by
      simp [Expr.eval, rC1, rC0, BinOp.eval, (by omega : nxtPtr + m < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := { stC with regs := rC2 })
    (by simp [rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr0])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega)
    (by rw [hColl_lt _ (by simp [HDR_NODES_BASE, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have ha10 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := { stC with regs := rC3 })
    (by simp [rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr0])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega)
    (by rw [hColl_lt _ (by simp [HDR_FUEL, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have ha11a := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_IS_ROOT)
    (b := b) (val := isRootBase b vCap) (st := { stC with regs := rC4 })
    (by simp [rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr0])
    (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega)
    (by rw [hColl_lt _ (by simp [HDR_IS_ROOT, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hhdr.2.2.2.2.2.1)
  have ha11b := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 11) (rIdx := 4)
    (base := isRootBase b vCap) (idx := v) (val := irV) (st := { stC with regs := rC5 })
    (by simp [rC5]) (by simp [rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr4])
    (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
    (by rw [hColl_lt _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact h.isRoot_mem v hvLt)
  have hrec_h1 : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ h1 := by
    have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hinv0 : TourForestInv x.numNodes x.st (t0 :: rest) := (h.forestInv.perm ht0_perm).1
  -- Step 2: clear `rootTag := 0` on `feV` if `v ∈ R`
  have hclear : ∃ t1 s1 st1 cClr,
      Runs w p ω (.cond (.reg 11)
        (.assign 16 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 8))) ;;
         .assign 17 (.load (.bin .add (.reg 16) (.const 9))) ;;
         .assign 18 (.load (.bin .add (.reg 16) (.const 10))) ;;
         .assign 19 (.const 0) ;;
         .call 20 C.setValNode [.reg 9, .reg 8, .reg 17, .reg 18, .reg 19, .reg 10, .reg 15])
        .nop) { stC with regs := rC6 } .normal st1 cClr ∧
      (∀ k < 16, st1.regs k = rC6 k) ∧
      tourLayout.NodesAt st1.mem (nodesBase b vCap eCap) x.numNodes s1 ∧
      TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes h1 stC.mem st1.mem ∧
      TourForestInv x.numNodes s1 (t1 :: rest) ∧ TourValsOk w x.numNodes s1 ∧
      t1.toList = t0.toList ∧
      (v ∈ s.rf.R → ∀ u ≤ x.numNodes,
        (u ∈ t0.toList → (s1.nodes u).val = { (x.st.nodes u).val with rootTag := 0 }) ∧
        (u ∉ t0.toList → (s1.nodes u).val = (x.st.nodes u).val)) ∧
      (v ∉ s.rf.R → ∀ u ≤ x.numNodes, (s1.nodes u).val = (x.st.nodes u).val) ∧
      cClr + TOUR_PHI_MULT * forestPhi (t1 :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t0 :: rest) + TOUR_FIND_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) + 50 := by
    by_cases hvR : v ∈ s.rf.R
    · have hcond : (Expr.reg 11).eval w { stC with regs := rC6 } = some 1 := by simp [Expr.eval, rC6, irV, hvR]
      have hfe_cap : feV ≤ x.numNodes := hfe_le
      have hAt : nodesBase b vCap eCap + 17 * feV + 17 ≤ h1 := by
        have := hrec_h1; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
      have hnd := hC_nodes feV hfe_cap
      have hmem9 : stC.mem (nodesBase b vCap eCap + 17 * feV + 9) = if (x.st.nodes feV).val.isOpen then 1 else 0 := by
        simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.1
      have hmem10 : stC.mem (nodesBase b vCap eCap + 17 * feV + 10) = if (x.st.nodes feV).val.isMarked then 1 else 0 := by
        simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.2.1
      set opV := if (x.st.nodes feV).val.isOpen then 1 else 0
      set mkV := if (x.st.nodes feV).val.isMarked then 1 else 0
      set rc1 := Function.update rC6 16 (nodesBase b vCap eCap + 17 * feV)
      set rc2 := Function.update rc1 17 opV
      set rc3 := Function.update rc2 18 mkV
      set rc4 := Function.update rc3 19 0
      have hc16 : Runs w p ω (.assign 16 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 8))))
          { stC with regs := rC6 } .normal { stC with regs := rc1 } 6 :=
        runs_assign_iff.mpr ⟨nodesBase b vCap eCap + 17 * feV, by
          simp [Expr.eval, rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr8, feV,
            BinOp.eval, (by omega : 17 < 2 ^ w), (by omega : 17 * feV < 2 ^ w),
            (by omega : nodesBase b vCap eCap + 17 * feV < 2 ^ w)], rfl, rfl, rfl⟩
      have hc17 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 17) (rBase := 16) (off := 9)
        (b := nodesBase b vCap eCap + 17 * feV) (val := opV) (st := { stC with regs := rc1 })
        (by simp [rc1]) (by omega) (by omega) hmem9
      have hc18 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 18) (rBase := 16) (off := 10)
        (b := nodesBase b vCap eCap + 17 * feV) (val := mkV) (st := { stC with regs := rc2 })
        (by simp [rc2, rc1]) (by omega) (by omega) hmem10
      have hc19 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 19) (val := 0) (st := { stC with regs := rc3 }) (by omega)
      obtain ⟨t1, s1, o1, st1, c1, hrun1, hn1, hfr1, hinv1, hvals1, _, _, hlist1, hval_eq, hval_ne, _, hcost1⟩ :=
        tourSetValNodeBody_runs (isOpen := opV) (isMarked := mkV) (rootTag := 0) (fuel := 2 * eCap + 2) (pos := stC.pos)
          C ω hC_nodes hinv0 (h.valsOk hw) hfe_t0 (by omega) (by have := h.numNodes_le; omega) (by omega)
          ⟨hrec_h1, by omega, hzeroC, by omega⟩
      have hcall := runs_call_regs7 20 9 8 17 18 19 10 15 (st := { stC with regs := rc4 }) C.setValNode_body
        (by simp [rc4, rc3, rc2, rc1, rC6, rC5, rC4, rC3])
        (by simp [rc4, rc3, rc2, rc1, rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr8, feV])
        (by simp [rc4, rc3, rc2]) (by simp [rc4, rc3]) (by simp [rc4])
        (by simp [rc4, rc3, rc2, rc1, rC6, rC5, rC4])
        (by simp [rc4, rc3, rc2, rc1, rC6, rC5, rC4, rC3, rC2]) hrun1
      refine ⟨t1, s1, { st1 with regs := Function.update rc4 20 o1.value }, _,
        tour_runs_cond_true hcond (by omega) (tour_runs_seq_normal hc16 (tour_runs_seq_normal hc17
          (tour_runs_seq_normal hc18 (tour_runs_seq_normal hc19 hcall)))),
        fun k hk => by simp [rc4, rc3, rc2, rc1, Function.update_of_ne (by omega : k ≠ 20),
          Function.update_of_ne (by omega : k ≠ 19), Function.update_of_ne (by omega : k ≠ 18),
          Function.update_of_ne (by omega : k ≠ 17), Function.update_of_ne (by omega : k ≠ 16)],
        hn1, hfr1, hinv1, hvals1, hlist1,
        fun _ u hucap => ⟨fun hut => by
          by_cases hufe : u = feV
          · subst hufe; rw [hval_eq]
            cases hvo : (x.st.nodes feV).val with | mk io im rt => cases io <;> cases im <;> simp [opV, mkV, hvo]
          · rw [hval_ne u hucap hufe]
            have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t0, ht0_perm.mem_iff.mpr (by simp), hut⟩)
            have hfu : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) := by
              rw [← ht0_map]; exact List.mem_map_of_mem hut
            obtain ⟨w1, hw1, hcw1⟩ := ((fullTour_spec h.valid.compat (s.rf.root v)).2 _).mp hfu
            rw [h.val_active u hu_in.1 hu_in.2 ⟨w1, hw1⟩]
            have hrt0 : tourRootTagVal s (endOfKey (x.keyOf u)) = 0 := by
              apply tourRootTagVal_eq_zero; intro r' hr' hh
              have hw1r' := h.valid.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
              rw [hw1r'] at hcw1
              have hr'v : r' = v := by
                have hrv : s.rf.root v = v := h.valid.root_eq_of_mem hvF hvR (connected_refl _ _)
                exact (h.valid.unique_root v hvF).unique ⟨hr', hrv ▸ hcw1⟩ ⟨hvR, connected_refl _ _⟩
              rw [hr'v, hhead] at hh
              have hkeq : x.keyOf u = endKey aHead := by rw [Option.some.inj hh, endKey_endOfKey']
              exact hufe (by dsimp only [feV]; rw [← hkeq, (h.keyOf_mem u hu_in.1 hu_in.2).2.2])
            simp [hrt0],
          fun hunt => hval_ne u hucap (fun heq => hunt (heq ▸ hfe_t0))⟩,
        fun hn => absurd hvR hn, by clear * - hcost1; simp only [Expr.size]; omega⟩
    · have hcond : (Expr.reg 11).eval w { stC with regs := rC6 } = some 0 := by simp [Expr.eval, rC6, irV, hvR]
      refine ⟨t0, x.st, { stC with regs := rC6 }, _, tour_runs_cond_false hcond (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        fun _ _ => rfl, hC_nodes, TreeFrame.refl hzeroC, hinv0, h.valsOk hw, rfl,
        fun hr => absurd hr hvR, fun _ _ _ => rfl, by simp [Expr.size]; omega⟩
  obtain ⟨t1, s1, st1, cClr, hrunClr, hr1_lt, hn1, hfr1, hinv1, hvals1, ht1_list, hval1_in, hval1_out, hcClr⟩ := hclear
  -- Step 3: `rotateFront(nb, feV, fuel, h1)` -> `t2.toList.map ... = fullTour s v`
  have hfe_t1 : feV ∈ t1.toList := by rw [ht1_list]; exact hfe_t0
  obtain ⟨t2, s2, o2, st2, cRot, hrunRot, _, hn2, hfr2, hinv2, hvals2, _, hrot2, hval2, _, hcRot⟩ :=
    tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st1.pos) C.toTourSplayOpsProcs ω
      hn1 hinv1 hvals1 hfe_t1 (by have := h.numNodes_le; omega) (by omega) ⟨hrec_h1, by omega, hfr1.1, by omega⟩
  have hcallRot := runs_call_regs4 20 9 8 10 15 (st := st1) C.rotateFront_body
    (by rw [hr1_lt 9 (by omega)]; simp [rC6, rC5, rC4, rC3])
    (by rw [hr1_lt 8 (by omega)]; simp [rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr8, feV])
    (by rw [hr1_lt 10 (by omega)]; simp [rC6, rC5, rC4])
    (by rw [hr1_lt 15 (by omega)]; simp [rC6, rC5, rC4, rC3, rC2]) hrunRot
  set rRot := Function.update st1.regs 20 o2.value
  have hfr12 := hfr1.trans hfr2
  have ht2_perm : t2.toList.Perm t0.toList := by
    rw [hrot2]; exact (rotateNatList_perm hfe_t1).trans (List.Perm.of_eq ht1_list)
  have ht2_map_v : t2.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord s.rf.F h.valid.compat.forest v := by
    rw [hrot2, ht1_list]
    exact rotateNatList_map_fullTour h.valid h (ht0_perm.mem_iff.mpr (by simp)) ht0_map
      (fun _ hz => hz) (connected_symm (h.valid.root_spec hvF).2) hhead hfe_t0
      (by rw [hfe_key, endOfKey_endKey])
  have hst2_lt_nb : ∀ a < nodesBase b vCap eCap, st2.mem a = mem a := fun a ha => by
    rw [hfr12.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha), hColl_lt a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)]
  have hst2_ge_ord : ∀ a, ordHandleOf b vCap eCap ≤ a → a < h1 → st2.mem a = stC.mem a := fun a ha1 ha2 =>
    hfr12.2 a ha2 (fun hin => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega)
  have hOrd2 := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord x.ordX stC.mem st2.mem fun a ha =>
    (hst2_ge_ord a (hordGe a ha) (lt_of_lt_of_le (hordFoot a ha) (by omega))).symm
  -- Step 4: `rankSortNext [b, v, feV, heap, nxtPtr, m, h1]`
  obtain ⟨h2, t3, s3, ordX3, st3, cRS, A, hrunRS, hh2_ge, hh2_le, hzero3, hA_perm, hA_len, hA_nd,
    hA_pw, hA_mem, hNxt_mem, hn3, hinv3, hvals3, ht3_list, hval3, hRS_fr, hOrd3_foot, hOrd3_ge, hOrd3_rep, hcRS⟩ :=
    tourMoveRankSortNextBody_runs (nxtPtr := nxtPtr) (hCur := h1) (pos := st2.pos) C hRank hSift hSort hOrdImpl hop2 ω
      h hst2_lt_nb (hOrd2.1 (hOrdC.1 hordRep)) hordGe hordFoot hvLt hhead rfl hn2 hinv2 hvals2
      (fun id hid => ((h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, ht0_perm.mem_iff.mpr (by simp), ht2_perm.mem_iff.mp hid⟩)).2)
      ht2_map_v hA0_len hA0_nd
      (fun i hi => by rw [hst2_ge_ord (heap + (2 * i + 1)) (by omega) (by omega)]; exact hA0_mem i hi)
      (fun u hu => let ⟨a1, a2, a3, _⟩ := hA0_in u hu; ⟨a1, a2, a3⟩)
      hord_le (by omega) (by omega) (by omega) hw hwide hfr12.1
  have hcallRS := runs_call_regs7 15 0 4 8 2 14 13 15 (st := { st2 with regs := rRot }) hRS
    (by simp [rRot, hr1_lt 0 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr0])
    (by simp [rRot, hr1_lt 4 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr4])
    (by simp [rRot, hr1_lt 8 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr8, feV])
    (by simp [rRot, hr1_lt 2 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr2])
    (by simp [rRot, hr1_lt 14 (by omega), rC6, rC5, rC4, rC3, rC2, rC1])
    (by simp [rRot, hr1_lt 13 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0])
    (by simp [rRot, hr1_lt 15 (by omega), rC6, rC5, rC4, rC3, rC2]) hrunRS
  set rRS := Function.update rRot 15 h2
  -- Step 5: `splay [nb, feV, fuel, h2]` then `splitLoop [nb, feV, heap, nxtPtr, m, fuel, h2]`
  have hrec_h2 : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ h2 := le_trans hrec_h1 hh2_ge
  have hfe_t3 : feV ∈ t3.toList := by rw [ht3_list]; exact ht2_perm.mem_iff.mpr hfe_t0
  have hfe_dep : t3.depthOf feV < 2 * eCap + 2 :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hfe_t3)
      (le_trans (hinv3.countNodes_le (t := t3) (by simp)) (by have := h.numNodes_le; omega))
  obtain ⟨t4, o4, st4, cSp, hrunSp, hn4, hfr4, hinv4, hvals4, _, ht4_root, ht4_list, _, hcSp⟩ :=
    tourSplay_runs_amort (pre := []) (post := rest) (pos := st3.pos) C.toTourSplayCoreProcs ω
      hn3 hinv3 hvals3 hfe_t3 hfe_dep (by have := h.numNodes_le; omega) ⟨hrec_h2, by omega, hzero3, by omega⟩
  obtain ⟨_, _, _, _, _, _, hval4, _⟩ := tourSplay_preserves (pre := []) (post := rest) hinv3 hfe_t3 hfe_dep
  have hcallSp := runs_call_regs4 18 9 8 10 15 (st := { st3 with regs := rRS }) C.splay.splay_body
    (by simp [rRS, rRot, hr1_lt 9 (by omega), rC6, rC5, rC4, rC3])
    (by simp [rRS, rRot, hr1_lt 8 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr8, feV])
    (by simp [rRS, rRot, hr1_lt 10 (by omega), rC6, rC5, rC4]) (by simp [rRS]) hrunSp
  set rSp := Function.update rRS 18 o4.value
  -- Block decomposition `xs.flatMap f`
  set xs : List ℕ := (s.ord v).map fun z => x.nodeOf (endKey z)
  let fullBlock (z : End) : List End :=
    if z.1 ∉ s.rf.F.E then [z]
    else if _h : z.1 ∈ s.rf.F.E ∧ s.rf.F.src z = v then
      z :: fullTourBlocks s.ord s.rf.F (eraseForestEdge s.rf.F z.1)
        (isForest_eraseEdge h.valid.compat.forest z.1)
        (s.rf.F.dst z) (afterEnd z.flip (s.ord (s.rf.F.dst z))) ++ [z.flip]
    else []
  let f (u : ℕ) : List ℕ := (fullBlock (endOfKey (x.keyOf u))).map fun z => x.nodeOf (endKey z)
  have hblocks := fullTour_moveEnds_blocks (sel := sel.toFinset) (c := c) h.valid.compat hne hvF hv'NotF hord_v'
  have hft_v_eq : fullTour s.ord s.rf.F h.valid.compat.forest v = (s.ord v).flatMap fullBlock := hblocks.1
  have hft'_v_eq : fullTour s'.ord s'.rf.F hvalid'.compat.forest v =
      ((s.ord v).filter fun z => !movedBy sel.toFinset c z).flatMap fullBlock := hblocks.2.1
  have hft'_v'_eq : fullTour s'.ord s'.rf.F hvalid'.compat.forest v' =
      ((s.ord v).filter (movedBy sel.toFinset c)).flatMap fullBlock := hblocks.2.2
  have hact_node : ∀ z, (∃ w', z ∈ s.ord w') →
      1 ≤ x.nodeOf (endKey z) ∧ x.nodeOf (endKey z) ≤ x.numNodes ∧
      endOfKey (x.keyOf (x.nodeOf (endKey z))) = z := by
    rintro z ⟨w', hw'⟩
    have ⟨_, _, _, _, h1, h2, h3, _⟩ := h.mem_compTree_of_active hw'
    exact ⟨h1, h2, by rw [h3, endOfKey_endKey]⟩
  have hfb_map : ∀ z ∈ s.ord v, (f (x.nodeOf (endKey z))).map (fun id => endOfKey (x.keyOf id)) = fullBlock z := by
    intro z hz
    have hzn := hact_node z ⟨v, hz⟩
    simp only [f, hzn.2.2, List.map_map, Function.comp_def]
    conv_rhs => rw [← List.map_id (fullBlock z)]
    refine List.map_congr_left fun e' he' => ?_
    have he'_ft : e' ∈ fullTour s.ord s.rf.F h.valid.compat.forest v := by
      rw [hft_v_eq]; exact List.mem_flatMap.mpr ⟨z, hz, he'⟩
    obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat v).2 e').mp he'_ft
    exact (hact_node e' ⟨w', hw'⟩).2.2
  have hxs_nd : xs.Nodup := (h.valid.compat.nodup v).map_on fun z1 hz1 z2 hz2 heq => by
    have h1 := (hact_node z1 ⟨v, hz1⟩).2.2; have h2 := (hact_node z2 ⟨v, hz2⟩).2.2; rw [← h1, heq, h2]
  have ht4_flat : t4.toList = xs.flatMap f := by
    refine list_eq_of_map_inj (f := fun id => endOfKey (x.keyOf id)) ?_ ?_
    · rw [ht4_list, ht3_list, ht2_map_v, hft_v_eq]
      simp only [xs, List.flatMap_map, List.map_flatMap]
      exact (List.flatMap_congr fun z hz => hfb_map z hz).symm
    · intro a ha b hb hab
      have ha_in := (h.nodes_exact a).mp (List.mem_flatMap.mpr ⟨t0, ht0_perm.mem_iff.mpr (by simp),
        ht2_perm.mem_iff.mp (by rwa [← ht3_list, ← ht4_list])⟩)
      obtain ⟨u, hu, hbu⟩ := List.mem_flatMap.mp hb
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
      dsimp only [f] at hbu; rw [(hact_node z ⟨v, hz⟩).2.2] at hbu
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hbu
      have he'_ft : e' ∈ fullTour s.ord s.rf.F h.valid.compat.forest v := by
        rw [hft_v_eq]; exact List.mem_flatMap.mpr ⟨z, hz, he'⟩
      obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat v).2 e').mp he'_ft
      have hb_in := hact_node e' ⟨w', hw'⟩
      have hka : x.keyOf a = x.keyOf (x.nodeOf (endKey e')) := by
        rw [← endKey_endOfKey' (x.keyOf a), hab, endKey_endOfKey']
      rw [← (h.keyOf_mem a ha_in.1 ha_in.2).2.2, hka, (h.keyOf_mem _ hb_in.1 hb_in.2.1).2.2]
  have hhhd : ∀ u ∈ xs, (f u).head? = some u := by
    intro u hu; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
    have hzn := hact_node z ⟨v, hz⟩
    dsimp only [f]; rw [hzn.2.2, List.head?_map, fullBlock_head? h.valid.compat hz]; rfl
  have hA_sub_xs : ∀ u ∈ A, u ∈ xs := fun u hu => by
    have ⟨h1, h2, h3, _⟩ := hA0_in u (hA_perm.mem_iff.mp hu)
    exact List.mem_map.mpr ⟨endOfKey (x.keyOf u), h3, by rw [endKey_endOfKey', (h.keyOf_mem u h1 h2).2.2]⟩
  have hA_eq : A = xs.filter fun z => decide (z ∈ A) := by
    refine filter_eq_of_perm_sorted_idxOf hxs_nd ?_ hhhd hA_nd hA_sub_xs ?_
    · rw [← ht4_flat]; exact (hinv4.treesInv t4 (by simp)).1
    · rw [← ht4_flat, ht4_list, ht3_list]; exact hA_pw
  have hmem4_A : ∀ i (hi : i < m), st4.mem (heap + (2 * i + 1)) = A[i]'(by omega) := fun i hi => by
    rw [hfr4.2 _ (by omega) (fun hin => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega)]
    exact hA_mem i (by omega)
  have hmem4_W : ∀ i (hi : i < m),
      let idx := xs.idxOf (A[i]'(by omega))
      st4.mem (nxtPtr + i) = if hlt : idx + 1 < xs.length then xs[idx + 1] else 0 := fun i hi => by
    rw [hfr4.2 _ (by omega) (fun hin => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega)]
    exact hNxt_mem i (by omega)
  obtain ⟨tA?, tB?, s5, o5, st5, cSplit, hrunSplit, hm5_0, hm5_1, hn5, hzero5, hfr5, hinv5, hvals5,
    hA_list, hB_list, hval5, hcSplit⟩ :=
    tourMoveSplitLoopBody_runs (fuel := 2 * eCap + 2) (pos := st4.pos) C.toTourSplayOpsProcs ω
      hn4 hinv4 hvals4 hxs_nd ht4_flat hhhd hA_eq hA_len hmem4_A hmem4_W
      (by omega) (by omega)
      (fun a ha1 _ hin => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega)
      (fun a ha1 _ hin => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega)
      (by have := h.numNodes_le; omega) (by omega) ⟨hrec_h2, by omega, hfr4.1, by omega⟩
  have hcallSplit := runs_call_regs7 18 9 8 2 14 13 10 15 (st := { st4 with regs := rSp }) hSplit
    (by simp [rSp, rRS, rRot, hr1_lt 9 (by omega), rC6, rC5, rC4, rC3])
    (by simp [rSp, rRS, rRot, hr1_lt 8 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr8, feV, ht4_root])
    (by simp [rSp, rRS, rRot, hr1_lt 2 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr2])
    (by simp [rSp, rRS, rRot, hr1_lt 14 (by omega), rC6, rC5, rC4, rC3, rC2, rC1])
    (by simp [rSp, rRS, rRot, hr1_lt 13 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0])
    (by simp [rSp, rRS, rRot, hr1_lt 10 (by omega), rC6, rC5, rC4]) (by simp [rSp, rRS]) hrunSplit
  set rSp2 := Function.update rSp 18 o5.value
  -- Step 6: load `(optRoot tA?, optRoot tB?)`, swap if `tag ≠ 2`, advance `hOut := h2 + 2`
  set hOut := h2 + 2
  set tKeep? : Option AuxTree := if c then tA? else tB?
  set tMove? : Option AuxTree := if c then tB? else tA?
  set rL1 := Function.update rSp2 16 (optRoot tA?)
  set rL2 := Function.update rL1 17 (optRoot tB?)
  have ha16 : Runs w p ω (.assign 16 (.load (.reg 15))) { st5 with regs := rSp2 } .normal { st5 with regs := rL1 } 3 :=
    runs_assign_iff.mpr ⟨optRoot tA?, by simp [Expr.eval, rSp2, rSp, rRS, hm5_0], rfl, rfl, rfl⟩
  have ha17 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 17) (rBase := 15) (off := 1)
    (b := h2) (val := optRoot tB?) (st := { st5 with regs := rL1 })
    (by simp [rL1, rSp2, rSp, rRS]) (by omega) (by omega) hm5_1
  have hswap : ∃ rSw cSw, cSw ≤ 14 ∧
      Runs w p ω (.cond (.bin .eq (.reg 3) (.const 2)) .nop
        (.assign 18 (.reg 16) ;; .assign 16 (.reg 17) ;; .assign 17 (.reg 18)))
        { st5 with regs := rL2 } .normal { st5 with regs := rSw } cSw ∧
      (∀ k < 16, rSw k = rL2 k) ∧ rSw 16 = optRoot tKeep? ∧ rSw 17 = optRoot tMove? := by
    cases c with
    | true =>
      have hc : (Expr.bin .eq (.reg 3) (.const 2)).eval w { st5 with regs := rL2 } = some 1 := by
        simp [Expr.eval, rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 3 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0,
          rD5, rD4, rD3, rD2, rD1, hr3, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      exact ⟨rL2, _, by simp [Expr.size], tour_runs_cond_true hc (by omega) (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        fun _ _ => rfl, by simp [rL2, rL1, tKeep?], by simp [rL2, tMove?]⟩
    | false =>
      have hc : (Expr.bin .eq (.reg 3) (.const 2)).eval w { st5 with regs := rL2 } = some 0 := by
        simp [Expr.eval, rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 3 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0,
          rD5, rD4, rD3, rD2, rD1, hr3, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 0 < 2 ^ w)]
      set rs1 := Function.update rL2 18 (optRoot tA?)
      set rs2 := Function.update rs1 16 (optRoot tB?)
      set rs3 := Function.update rs2 17 (optRoot tA?)
      have hs1 : Runs w p ω (.assign 18 (.reg 16)) { st5 with regs := rL2 } .normal { st5 with regs := rs1 } 2 :=
        runs_assign_iff.mpr ⟨optRoot tA?, by simp [Expr.eval, rL2, rL1], rfl, rfl, rfl⟩
      have hs2 : Runs w p ω (.assign 16 (.reg 17)) { st5 with regs := rs1 } .normal { st5 with regs := rs2 } 2 :=
        runs_assign_iff.mpr ⟨optRoot tB?, by simp [Expr.eval, rs1, rL2], rfl, rfl, rfl⟩
      have hs3 : Runs w p ω (.assign 17 (.reg 18)) { st5 with regs := rs2 } .normal { st5 with regs := rs3 } 2 :=
        runs_assign_iff.mpr ⟨optRoot tA?, by simp [Expr.eval, rs2, rs1], rfl, rfl, rfl⟩
      exact ⟨rs3, _, by simp [Expr.size], tour_runs_cond_false hc (tour_runs_seq_normal hs1 (tour_runs_seq_normal hs2 hs3)),
        fun k hk => by simp [rs3, rs2, rs1, Function.update_of_ne (by omega : k ≠ 18),
          Function.update_of_ne (by omega : k ≠ 17), Function.update_of_ne (by omega : k ≠ 16)],
        by simp [rs3, rs2, tKeep?], by simp [rs3, tMove?]⟩
  obtain ⟨rSw, cSw, hcSw, hrunSw, hrSw_lt, hrSw16, hrSw17⟩ := hswap
  set rAdv := Function.update rSw 15 hOut
  have haAdv : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 2))) { st5 with regs := rSw } .normal { st5 with regs := rAdv } 4 :=
    runs_assign_iff.mpr ⟨hOut, by
      simp [Expr.eval, hrSw_lt 15 (by omega), rL2, rL1, rSp2, rSp, rRS, BinOp.eval, (by omega : 2 < 2 ^ w),
        (by omega : h2 + 2 < 2 ^ w), hOut], rfl, rfl, rfl⟩
  -- Forest permutation, `fullTour` maps, and frame
  have hperm_KM : (optTrees tA? ++ optTrees tB? ++ rest).Perm (optTrees tKeep? ++ optTrees tMove? ++ rest) := by
    cases c <;> simp only [tKeep?, tMove?, ↓reduceIte, Bool.false_eq_true]
    · exact List.perm_append_comm.append_right rest
    · exact List.Perm.refl _
  have hperm_nodes5 : (optList tKeep? ++ optList tMove?).Perm t0.toList := by
    have hpAB : (optList tA? ++ optList tB?).Perm t0.toList := by
      rw [hA_list, hB_list, ← List.flatMap_append]
      have hp := (perm_filter_append_filter_not (fun z => decide (z ∈ A)) xs).flatMap_right f
      have heq : (xs.filter fun z => !decide (z ∈ A)) = xs.filter fun z => decide (z ∉ A) :=
        List.filter_congr fun z _ => by simp
      rw [heq] at hp
      exact hp.trans (by rw [← ht4_flat, ht4_list, ht3_list]; exact ht2_perm)
    cases c <;> simp only [tKeep?, tMove?, ↓reduceIte, Bool.false_eq_true]
    · exact List.perm_append_comm.trans hpAB
    · exact hpAB
  have hmem_A_iff : ∀ z ∈ s.ord v, x.nodeOf (endKey z) ∈ A ↔ z ∈ sel := by
    intro z hz; constructor
    · intro hza; have h1 := (hA0_in _ (hA_perm.mem_iff.mp hza)).2.2.2; rwa [(hact_node z ⟨v, hz⟩).2.2] at h1
    · intro hzs; exact hA_perm.mem_iff.mpr (hA0_sur z hz hzs)
  have hA_map : (optList tA?).map (fun id => endOfKey (x.keyOf id)) =
      ((s.ord v).filter fun z => decide (z ∈ sel)).flatMap fullBlock := by
    rw [hA_list]
    have hf1 : xs.filter (fun u => decide (u ∈ A)) = ((s.ord v).filter fun z => decide (z ∈ sel)).map fun z => x.nodeOf (endKey z) := by
      dsimp only [xs]; rw [List.filter_map]; congr 1
      exact List.filter_congr fun z hz => by simp [hmem_A_iff z hz]
    rw [hf1, List.flatMap_map, List.map_flatMap]
    exact List.flatMap_congr fun z hz => hfb_map z (List.mem_filter.mp hz).1
  have hB_map : (optList tB?).map (fun id => endOfKey (x.keyOf id)) =
      ((s.ord v).filter fun z => decide (z ∉ sel)).flatMap fullBlock := by
    rw [hB_list]
    have hf1 : xs.filter (fun u => decide (u ∉ A)) = ((s.ord v).filter fun z => decide (z ∉ sel)).map fun z => x.nodeOf (endKey z) := by
      dsimp only [xs]; rw [List.filter_map]; congr 1
      exact List.filter_congr fun z hz => by simp [hmem_A_iff z hz]
    rw [hf1, List.flatMap_map, List.map_flatMap]
    exact List.flatMap_congr fun z hz => hfb_map z (List.mem_filter.mp hz).1
  have hKeep_map5 : (optList tKeep?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour s'.ord s'.rf.F hvalid'.compat.forest v := by
    rw [hft'_v_eq]; cases c with
    | true => simp only [tKeep?, ↓reduceIte, hA_map]; congr 1; exact List.filter_congr fun z _ => by simp [movedBy]
    | false => simp only [tKeep?, Bool.false_eq_true, ↓reduceIte, hB_map]; congr 1; exact List.filter_congr fun z _ => by simp [movedBy]
  have hMove_map5 : (optList tMove?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour s'.ord s'.rf.F hvalid'.compat.forest v' := by
    rw [hft'_v'_eq]; cases c with
    | true => simp only [tMove?, ↓reduceIte, hB_map]; congr 1; exact List.filter_congr fun z _ => by simp [movedBy]
    | false => simp only [tMove?, Bool.false_eq_true, ↓reduceIte, hA_map]; congr 1; exact List.filter_congr fun z _ => by simp [movedBy]
  have hOrd5 := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord ordX3 st3.mem st5.mem fun a ha => by
    have ha_ge := hOrd3_ge a ha
    have ha_lt : a < h2 := by
      rcases hOrd3_foot a ha with h1a | ⟨_, h2a⟩
      · exact lt_of_lt_of_le (hordFoot a h1a) (by omega)
      · exact h2a
    have ha_nrec : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hin => by
      have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega
    exact (hfr4.2 a ha_lt ha_nrec).symm.trans (hfr5 a ha_lt ha_nrec).symm
  have hval5_all : ∀ u ≤ x.numNodes, (s5.nodes u).val = (s1.nodes u).val := fun u hu => by
    rw [hval5 u hu, hval4 u hu, hval3 u hu, hval2 u hu]
  have hst5_fr_heap : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
      ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st5.mem a = mem a := fun a ha hnrec hnord => by
    rw [hfr5 a (by omega) hnrec, hfr4.2 a (by omega) hnrec, hRS_fr a ha hnrec hnord,
      hfr12.2 a (by omega) hnrec, hColl_lt a ha]
  refine ⟨m, hOut, tKeep?, tMove?, s5, ordX3, { st5 with regs := rAdv }, _, A,
    tour_runs_seq_normal hd1 (tour_runs_seq_normal hd2 (tour_runs_seq_normal hd3 (tour_runs_seq_normal hd4
      (tour_runs_seq_normal hrunD5 (tour_runs_seq_normal hcallColl (tour_runs_seq_normal ha14 (tour_runs_seq_normal ha15
        (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11a (tour_runs_seq_normal ha11b
          (tour_runs_seq_normal hrunClr (tour_runs_seq_normal hcallRot (tour_runs_seq_normal hcallRS
            (tour_runs_seq_normal hcallSp (tour_runs_seq_normal hcallSplit (tour_runs_seq_normal ha16
              (tour_runs_seq_normal ha17 (tour_runs_seq_normal hrunSw haAdv))))))))))))))))))),
    hm_le, by omega, by omega, hzero5,
    by simp [rAdv, hrSw_lt 0 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 0 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr0],
    by simp [rAdv, hrSw_lt 2 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 2 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr2],
    by simp [rAdv, hrSw_lt 3 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 3 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr3],
    by simp [rAdv, hrSw_lt 4 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 4 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr4],
    by simp [rAdv, hrSw_lt 5 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 5 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5, rD4, rD3, rD2, rD1, hr5],
    by simp [rAdv, hrSw_lt 9 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 9 (by omega), rC6, rC5, rC4, rC3],
    by simp [rAdv, hrSw_lt 10 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 10 (by omega), rC6, rC5, rC4],
    by simp [rAdv, hrSw_lt 11 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 11 (by omega), rC6, irV],
    by simp [rAdv, hrSw_lt 12 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 12 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0, rD5],
    by simp [rAdv, hrSw_lt 13 (by omega), rL2, rL1, rSp2, rSp, rRS, rRot, hr1_lt 13 (by omega), rC6, rC5, rC4, rC3, rC2, rC1, rC0],
    by simp [rAdv], by simp [rAdv, hrSw16], by simp [rAdv, hrSw17],
    hA_len,
    fun i hi => by rw [hfr5 _ (by omega) (fun hin => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2; omega)]; exact hmem4_A i (by omega),
    fun u hu => hA0_in u (hA_perm.mem_iff.mp hu),
    fun z hz hzs => hA_perm.mem_iff.mpr (hA0_sur z hz hzs),
    fun a ha => hst5_fr_heap a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha) (fun hft => by have := hordGe a hft; simp [nodesBase, ordHandleOf, tourFixedSize] at ha this; omega),
    hst5_fr_heap, hn5, (hinv5.perm hperm_KM).1, hvals5, hperm_nodes5, hKeep_map5, hMove_map5,
    fun hvR u hu => by rw [hval5_all u hu]; exact hval1_in hvR u hu,
    fun hvNR u hu => by rw [hval5_all u hu]; exact hval1_out hvNR u hu,
    fun a ha => (hOrd3_foot a ha).imp id fun ⟨ha1, ha2⟩ => ⟨by omega, by omega⟩,
    hOrd3_ge, hOrd5.1 hOrd3_rep, ?_⟩
  have hphi5 := forestPhi_perm hperm_KM
  rw [← hphi5, ← hOrd5.2]
  rw [← hOrd2.2, ← hOrdC.2] at hcRS
  simp only [List.nil_append] at hcSp
  clear * - hcD hcColl hcClr hcRot hcRS hcSp hcSplit hcSw
  nlinarith

end MinCostFlow.SparseCore.Program
