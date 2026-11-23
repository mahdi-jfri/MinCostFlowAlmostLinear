module

public import MinCostFlow.SparseCore.Program.TourCutLinkMath
public import MinCostFlow.SparseCore.Program.TourSplayCutLink
import Mathlib.Tactic

/-!
# Forest cut/link procedure bodies and execution helpers

Defines the WordRAM procedure bodies `tourOpCutBody` (Op `1`) and `tourOpLinkBody` (Op `2`),
their `NoRand` proofs, and their standalone WordRAM execution assembly lemmas
`tourOpCutBody_exec` and `tourOpLinkBody_exec`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Amortized per-`tourLog` multiplier covering Ops `1` (`cut`) and `2` (`link`). -/
def TOUR_CUTLINK_MUL : ℕ := 3500000

theorem tour_endOfKey_two_mul (e : ℕ) : endOfKey (2 * e) = (e, true) := by
  simp [endOfKey]

theorem endOfKey_two_mul_add1 (e : ℕ) : endOfKey (2 * e + 1) = (e, false) := by
  simp [endOfKey]; omega

/-- Op 1 (`cut`): args `[b, e, newRoot, heap]`. Cuts forest edge `e` and promotes `newRoot` to root. -/
def tourOpCutBody (cutSplitProc rootTagOfProc setValNodeProc rotateFrontProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 5 (.bin .mul (.const 2) (.reg 1)) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.reg 5))) ;;
  .assign 7 (.load (.bin .add (.reg 4) (.bin .add (.reg 5) (.const 1)))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .call 10 rootTagOfProc [.reg 8, .reg 6, .reg 9, .reg 3] ;;
  .assign 10 (.bin .sub (.reg 10) (.const 1)) ;;
  .assign 11 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 6))) ;;
  .assign 11 (.load (.bin .add (.reg 11) (.const 11))) ;;
  .assign 12 (.const 1) ;;
  .assign 13 (.const 0) ;;
  .call 14 setValNodeProc [.reg 8, .reg 6, .reg 12, .reg 13, .reg 11, .reg 9, .reg 3] ;;
  .assign 11 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 7))) ;;
  .assign 11 (.load (.bin .add (.reg 11) (.const 11))) ;;
  .call 14 setValNodeProc [.reg 8, .reg 7, .reg 12, .reg 13, .reg 11, .reg 9, .reg 3] ;;
  .call 14 cutSplitProc [.reg 8, .reg 6, .reg 7, .reg 9, .reg 3] ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
  .store (.bin .add (.reg 11) (.reg 2)) (.const 1) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
  .assign 12 (.load (.bin .add (.reg 11) (.reg 2))) ;;
  .assign 13 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 12))) ;;
  .assign 14 (.load (.bin .add (.reg 13) (.const 9))) ;;
  .assign 15 (.load (.bin .add (.reg 13) (.const 10))) ;;
  .assign 16 (.bin .add (.reg 2) (.const 1)) ;;
  .call 17 setValNodeProc [.reg 8, .reg 12, .reg 14, .reg 15, .reg 16, .reg 9, .reg 3] ;;
  .assign 13 (.load (.bin .add (.reg 11) (.reg 10))) ;;
  .call 17 rotateFrontProc [.reg 8, .reg 13, .reg 9, .reg 3] ;;
  .call 17 rotateFrontProc [.reg 8, .reg 12, .reg 9, .reg 3] ;;
  .ret (.reg 3)

theorem tourOpCutBody_noRand (csP rtP svP rfP : ℕ) :
    (tourOpCutBody csP rtP svP rfP).NoRand := by
  simp [tourOpCutBody, Stmt.NoRand]

/-- Op 2 (`link`): args `[b, e, dropRoot, heap]`. Links open edge `e` and drops `dropRoot` from `R`. -/
def tourOpLinkBody (linkSpliceProc rootTagOfProc setValNodeProc rotateFrontProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 5 (.bin .mul (.const 2) (.reg 1)) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.reg 5))) ;;
  .assign 7 (.load (.bin .add (.reg 4) (.bin .add (.reg 5) (.const 1)))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
  .store (.bin .add (.reg 10) (.reg 2)) (.const 0) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.reg 2))) ;;
  .assign 12 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 11))) ;;
  .assign 13 (.load (.bin .add (.reg 12) (.const 9))) ;;
  .assign 14 (.load (.bin .add (.reg 12) (.const 10))) ;;
  .assign 15 (.const 0) ;;
  .call 16 setValNodeProc [.reg 8, .reg 11, .reg 13, .reg 14, .reg 15, .reg 9, .reg 3] ;;
  .assign 12 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 6))) ;;
  .assign 13 (.load (.bin .add (.reg 12) (.const 11))) ;;
  .call 16 setValNodeProc [.reg 8, .reg 6, .reg 15, .reg 15, .reg 13, .reg 9, .reg 3] ;;
  .assign 12 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 7))) ;;
  .assign 13 (.load (.bin .add (.reg 12) (.const 11))) ;;
  .call 16 setValNodeProc [.reg 8, .reg 7, .reg 15, .reg 15, .reg 13, .reg 9, .reg 3] ;;
  .call 16 linkSpliceProc [.reg 8, .reg 6, .reg 7, .reg 9, .reg 3] ;;
  .call 11 rootTagOfProc [.reg 8, .reg 6, .reg 9, .reg 3] ;;
  .assign 11 (.bin .sub (.reg 11) (.const 1)) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.reg 11))) ;;
  .call 16 rotateFrontProc [.reg 8, .reg 12, .reg 9, .reg 3] ;;
  .ret (.reg 3)

theorem tourOpLinkBody_noRand (lsP rtP svP rfP : ℕ) :
    (tourOpLinkBody lsP rtP svP rfP).NoRand := by
  simp [tourOpLinkBody, Stmt.NoRand]

/-- Right-associative concatenation of two `Stmt` sequences. -/
def seqAppend : Stmt → Stmt → Stmt
  | .seq a b, c => .seq a (seqAppend b c)
  | a, c => .seq a c

theorem runs_seqAppend {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ {a c : Stmt} {st st1 st2 : State} {o : Outcome} {k1 k2 : ℕ},
    Runs w p ω a st .normal st1 k1 →
    Runs w p ω c st1 o st2 k2 →
    Runs w p ω (seqAppend a c) st o st2 (k1 + k2 + 1) := by
  intro a
  induction a with
  | seq a1 a2 _ ih2 =>
    intro c st st1 st2 o k1 k2 h1 h2
    rcases runs_seq_iff.mp h1 with ⟨_, _, _, hno, _⟩ | ⟨stm, ca, cb, ha, hb, rfl⟩
    · cases hno
    · simp only [seqAppend]
      have := tour_runs_seq_normal ha (ih2 hb h2)
      convert this using 1; omega
  | _ =>
    intro c st st1 st2 o k1 k2 h1 h2
    exact tour_runs_seq_normal h1 h2

/-! ## WordRAM execution assembly for `tourOpCutBody` -/

theorem tourOpCutBody_exec {w vCap eCap b e newRoot heap pos csProc : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p)
    (hcs : p.procs[csProc]? = some (tourCutSplitBody C.splay.splay C.detachLeft C.detachRight C.join C.rotateFront))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {nx ny oldRoot rtX rtY feN feO opN mkN : ℕ}
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : Outcome} {st₁ st₂ st₃ st₄ st₅ st₆ st₇ : State} {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : ℕ}
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (he_lt : e < eCap) (hnewLt : newRoot < vCap) (holdLt : oldRoot < vCap)
    (hAxX : nodesBase b vCap eCap + 17 * nx + 17 ≤ heap)
    (hAxY : nodesBase b vCap eCap + 17 * ny + 17 ≤ heap)
    (hAxN : nodesBase b vCap eCap + 17 * feN + 17 ≤ heap)
    (hm_noe : mem (b + HDR_NODE_OF_END) = nodeOfEndBase b vCap)
    (hm_nx : mem (nodeOfEndBase b vCap + 2 * e) = nx)
    (hm_ny : mem (nodeOfEndBase b vCap + (2 * e + 1)) = ny)
    (hm_nb : mem (b + HDR_NODES_BASE) = nodesBase b vCap eCap)
    (hm_fuel : mem (b + HDR_FUEL) = 2 * eCap + 2)
    (hrun₁ : Runs w p ω (tourRootTagOfBody C.splay.splay)
      (startState [nodesBase b vCap eCap, nx, 2 * eCap + 2, heap] mem pos) o₁ st₁ c₁)
    (ho₁ : o₁.value = oldRoot + 1)
    (hm1_rtX : st₁.mem (nodesBase b vCap eCap + 17 * nx + 11) = rtX)
    (hrun₂ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, nx, 1, 0, rtX, 2 * eCap + 2, heap] st₁.mem st₁.pos) o₂ st₂ c₂)
    (hm2_rtY : st₂.mem (nodesBase b vCap eCap + 17 * ny + 11) = rtY)
    (hrun₃ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, ny, 1, 0, rtY, 2 * eCap + 2, heap] st₂.mem st₂.pos) o₃ st₃ c₃)
    (hrun₄ : Runs w p ω (tourCutSplitBody C.splay.splay C.detachLeft C.detachRight C.join C.rotateFront)
      (startState [nodesBase b vCap eCap, nx, ny, 2 * eCap + 2, heap] st₃.mem st₃.pos) o₄ st₄ c₄)
    (hm4_ir : st₄.mem (b + HDR_IS_ROOT) = isRootBase b vCap)
    (hm4_fe : st₄.mem (b + HDR_FIRST_END) = firstEndBase b)
    (hm4_feN : st₄.mem (firstEndBase b + newRoot) = feN)
    (hm5_opN : Function.update st₄.mem (isRootBase b vCap + newRoot) 1 (nodesBase b vCap eCap + 17 * feN + 9) = opN)
    (hm5_mkN : Function.update st₄.mem (isRootBase b vCap + newRoot) 1 (nodesBase b vCap eCap + 17 * feN + 10) = mkN)
    (hrun₅ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, feN, opN, mkN, newRoot + 1, 2 * eCap + 2, heap]
        (Function.update st₄.mem (isRootBase b vCap + newRoot) 1) st₄.pos) o₅ st₅ c₅)
    (hm5_feO : st₅.mem (firstEndBase b + oldRoot) = feO)
    (hrun₆ : Runs w p ω (tourRotateFrontBody C.splay.splay C.detachLeft C.join)
      (startState [nodesBase b vCap eCap, feO, 2 * eCap + 2, heap] st₅.mem st₅.pos) o₆ st₆ c₆)
    (hrun₇ : Runs w p ω (tourRotateFrontBody C.splay.splay C.detachLeft C.join)
      (startState [nodesBase b vCap eCap, feN, 2 * eCap + 2, heap] st₆.mem st₆.pos) o₇ st₇ c₇) :
    ∃ st_fin c_fin, st_fin.mem = st₇.mem ∧
      c_fin ≤ c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + 300 ∧
      Runs w p ω (tourOpCutBody csProc C.rootTagOf C.setValNode C.rotateFront)
        (startState [b, e, newRoot, heap] mem pos) (.returned heap) st_fin c_fin := by
  have hgeo : b + 16 < 2 ^ w ∧ 2 * e + 1 < 2 ^ w ∧ nodeOfEndBase b vCap + (2 * e + 1) < 2 ^ w ∧
      isRootBase b vCap + newRoot < 2 ^ w ∧ firstEndBase b + newRoot < 2 ^ w ∧
      firstEndBase b + oldRoot < 2 ^ w ∧ newRoot + 1 < 2 ^ w ∧ oldRoot < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize, nodeOfEndBase, isRootBase, firstEndBase] at hord_le ⊢; omega
  unfold tourOpCutBody
  set s0 : State := startState [b, e, newRoot, heap] mem pos
  have hphaseA : ∃ rA cA,
      rA 0 = b ∧ rA 2 = newRoot ∧ rA 3 = heap ∧ rA 8 = nodesBase b vCap eCap ∧ rA 9 = 2 * eCap + 2 ∧ rA 10 = oldRoot ∧
      cA ≤ c₁ + c₂ + c₃ + c₄ + 160 ∧
      Runs w p ω
        (.assign 4 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
         .assign 5 (.bin .mul (.const 2) (.reg 1)) ;;
         .assign 6 (.load (.bin .add (.reg 4) (.reg 5))) ;;
         .assign 7 (.load (.bin .add (.reg 4) (.bin .add (.reg 5) (.const 1)))) ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
         .call 10 C.rootTagOf [.reg 8, .reg 6, .reg 9, .reg 3] ;;
         .assign 10 (.bin .sub (.reg 10) (.const 1)) ;;
         .assign 11 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 6))) ;;
         .assign 11 (.load (.bin .add (.reg 11) (.const 11))) ;;
         .assign 12 (.const 1) ;;
         .assign 13 (.const 0) ;;
         .call 14 C.setValNode [.reg 8, .reg 6, .reg 12, .reg 13, .reg 11, .reg 9, .reg 3] ;;
         .assign 11 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 7))) ;;
         .assign 11 (.load (.bin .add (.reg 11) (.const 11))) ;;
         .call 14 C.setValNode [.reg 8, .reg 7, .reg 12, .reg 13, .reg 11, .reg 9, .reg 3] ;;
         .call 14 csProc [.reg 8, .reg 6, .reg 7, .reg 9, .reg 3])
        s0 .normal ⟨st₄.mem, rA, st₄.pos⟩ cA := by
    set r1 := Function.update s0.regs 4 (nodeOfEndBase b vCap)
    set r2 := Function.update r1 5 (2 * e)
    set r3 := Function.update r2 6 nx
    set r4 := Function.update r3 7 ny
    set r5 := Function.update r4 8 (nodesBase b vCap eCap)
    set r6 := Function.update r5 9 (2 * eCap + 2)
    set s_1 : State := { st₁ with regs := Function.update r6 10 o₁.value }
    set r7 := Function.update s_1.regs 10 oldRoot
    set r8 := Function.update r7 11 (nodesBase b vCap eCap + 17 * nx)
    set r9 := Function.update r8 11 rtX
    set r10 := Function.update r9 12 1
    set r11 := Function.update r10 13 0
    set s_2 : State := { st₂ with regs := Function.update r11 14 o₂.value }
    set r12 := Function.update s_2.regs 11 (nodesBase b vCap eCap + 17 * ny)
    set r13 := Function.update r12 11 rtY
    set s_3 : State := { st₃ with regs := Function.update r13 14 o₃.value }
    set s_4 : State := { st₄ with regs := Function.update s_3.regs 14 o₄.value }
    have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_NODE_OF_END)
      (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
      (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hm_noe
    have ha2 : Runs w p ω (.assign 5 (.bin .mul (.const 2) (.reg 1))) ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨2 * e, by simp [Expr.eval, r1, s0, startState, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w)], rfl, rfl, rfl⟩
    have ha3 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 4) (rIdx := 5)
      (base := nodeOfEndBase b vCap) (idx := 2 * e) (val := nx) (st := ⟨mem, r2, pos⟩)
      (by simp [r2, r1]) (by simp [r2]) (by omega) hm_nx
    have ha4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 4) (.bin .add (.reg 5) (.const 1))))) ⟨mem, r3, pos⟩ .normal ⟨mem, r4, pos⟩ 7 :=
      runs_assign_iff.mpr ⟨ny, by
        have hr4v : r3 4 = nodeOfEndBase b vCap := by simp [r3, r2, r1]
        have hr5v : r3 5 = 2 * e := by simp [r3, r2]
        simp only [Expr.eval, hr4v, hr5v, (by omega : 1 < 2 ^ w), BinOp.eval, (by omega : 2 * e + 1 < 2 ^ w),
          hgeo.2.2.1, ↓reduceIte, Option.map_some, hm_ny], rfl, rfl, rfl⟩
    have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_NODES_BASE)
      (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
      (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hm_nb
    have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_FUEL)
      (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r5, pos⟩) (by simp [r5, r4, r3, r2, r1, s0, startState])
      (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hm_fuel
    have hc1 := runs_call_regs4 10 8 6 9 3 (st := ⟨mem, r6, pos⟩) C.rootTagOf_body
      (by simp [r6, r5]) (by simp [r6, r5, r4, r3]) (by simp [r6]) (by simp [r6, r5, r4, r3, r2, r1, s0, startState]) hrun₁
    have ha7 := runs_assign_reg_sub1 (w := w) (p := p) (ω := ω) (dst := 10) (rSrc := 10) (v := oldRoot + 1)
      (st := s_1) (by simp [s_1, ho₁]) (by omega) (by omega)
    have ha8 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 11) (rNb := 8) (rNode := 6)
      (nb := nodesBase b vCap eCap) (node := nx) (st := ⟨st₁.mem, r7, st₁.pos⟩)
      (by simp [r7, s_1, r6, r5]) (by simp [r7, s_1, r6, r5, r4, r3]) (by omega) (by omega) (by omega)
    have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 11) (off := 11)
      (b := nodesBase b vCap eCap + 17 * nx) (val := rtX) (st := ⟨st₁.mem, r8, st₁.pos⟩)
      (by simp [r8]) (by omega) (by omega) hm1_rtX
    have ha10 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 12) (val := 1) (st := ⟨st₁.mem, r9, st₁.pos⟩) (by omega)
    have ha11 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 13) (val := 0) (st := ⟨st₁.mem, r10, st₁.pos⟩) (by omega)
    have hc2 := tour_runs_call_of (r := 14) (args := [.reg 8, .reg 6, .reg 12, .reg 13, .reg 11, .reg 9, .reg 3])
      (st := ⟨st₁.mem, r11, st₁.pos⟩) C.setValNode_body
      (by simp [evalArgs, Expr.eval, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₂
    have ha12 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 11) (rNb := 8) (rNode := 7)
      (nb := nodesBase b vCap eCap) (node := ny) (st := s_2)
      (by simp [s_2, r11, r10, r9, r8, r7, s_1, r6, r5]) (by simp [s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4])
      (by omega) (by omega) (by omega)
    have ha13 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 11) (off := 11)
      (b := nodesBase b vCap eCap + 17 * ny) (val := rtY) (st := ⟨st₂.mem, r12, st₂.pos⟩)
      (by simp [r12]) (by omega) (by omega) hm2_rtY
    have hc3 := tour_runs_call_of (r := 14) (args := [.reg 8, .reg 7, .reg 12, .reg 13, .reg 11, .reg 9, .reg 3])
      (st := ⟨st₂.mem, r13, st₂.pos⟩) C.setValNode_body
      (by simp [evalArgs, Expr.eval, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₃
    have hc4 := runs_call_regs5 14 8 6 7 9 3 (st := s_3) hcs
      (by simp [s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5])
      (by simp [s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3])
      (by simp [s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4])
      (by simp [s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6])
      (by simp [s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₄
    have hseq :=
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
        (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal hc1 (tour_runs_seq_normal ha7
          (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11
            (tour_runs_seq_normal hc2 (tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13 (tour_runs_seq_normal hc3 hc4)))))))))))))))
    refine ⟨s_4.regs, _,
      by simp [s_4, s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, s0, startState],
      by simp [s_4, s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, s0, startState],
      by simp [s_4, s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, s0, startState],
      by simp [s_4, s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6, r5],
      by simp [s_4, s_3, r13, r12, s_2, r11, r10, r9, r8, r7, s_1, r6],
      by simp [s_4, s_3, r13, r12, s_2, r11, r10, r9, r8, r7],
      ?_, hseq⟩
    clear * -; simp only [argsSize, Expr.size]; omega
  obtain ⟨rA, cA, hrA0, hrA2, hrA3, hrA8, hrA9, hrA10, hcA, hrunA⟩ := hphaseA
  set mem5 := Function.update st₄.mem (isRootBase b vCap + newRoot) 1
  set r14 := Function.update rA 11 (isRootBase b vCap)
  set r15 := Function.update r14 11 (firstEndBase b)
  set r16 := Function.update r15 12 feN
  set r17 := Function.update r16 13 (nodesBase b vCap eCap + 17 * feN)
  set r18 := Function.update r17 14 opN
  set r19 := Function.update r18 15 mkN
  set r20 := Function.update r19 16 (newRoot + 1)
  set s_5 : State := { st₅ with regs := Function.update r20 17 o₅.value }
  set r21 := Function.update s_5.regs 13 feO
  set s_6 : State := { st₆ with regs := Function.update r21 17 o₆.value }
  set s_7 : State := { st₇ with regs := Function.update s_6.regs 17 o₇.value }
  have ha14 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_IS_ROOT)
    (b := b) (val := isRootBase b vCap) (st := ⟨st₄.mem, rA, st₄.pos⟩) hrA0
    (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hm4_ir
  have hst5 := runs_store_reg_off_const (w := w) (p := p) (ω := ω) (rBase := 11) (rIdx := 2)
    (base := isRootBase b vCap) (idx := newRoot) (val := 1) (st := ⟨st₄.mem, r14, st₄.pos⟩)
    (by simp [r14]) (by simp [r14, hrA2]) hgeo.2.2.2.1 (by omega)
  have ha15 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_FIRST_END)
    (b := b) (val := firstEndBase b) (st := ⟨mem5, r14, st₄.pos⟩) (by simp [r14, hrA0])
    (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega)
    (by dsimp only [mem5]; rw [Function.update_of_ne (by simp [HDR_FIRST_END, isRootBase]; omega)]; exact hm4_fe)
  have ha16 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 11) (rIdx := 2)
    (base := firstEndBase b) (idx := newRoot) (val := feN) (st := ⟨mem5, r15, st₄.pos⟩)
    (by simp [r15]) (by simp [r15, r14, hrA2]) hgeo.2.2.2.2.1
    (by dsimp only [mem5]; rw [Function.update_of_ne (by simp [firstEndBase, isRootBase]; omega)]; exact hm4_feN)
  have ha17 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 13) (rNb := 8) (rNode := 12)
    (nb := nodesBase b vCap eCap) (node := feN) (st := ⟨mem5, r16, st₄.pos⟩)
    (by simp [r16, r15, r14, hrA8]) (by simp [r16]) (by omega) (by omega) (by omega)
  have ha18 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 13) (off := 9)
    (b := nodesBase b vCap eCap + 17 * feN) (val := opN) (st := ⟨mem5, r17, st₄.pos⟩)
    (by simp [r17]) (by omega) (by omega) hm5_opN
  have ha19 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 13) (off := 10)
    (b := nodesBase b vCap eCap + 17 * feN) (val := mkN) (st := ⟨mem5, r18, st₄.pos⟩)
    (by simp [r18, r17]) (by omega) (by omega) hm5_mkN
  have ha20 := runs_assign_reg_add1 (w := w) (p := p) (ω := ω) (dst := 16) (rSrc := 2) (v := newRoot)
    (st := ⟨mem5, r19, st₄.pos⟩) (by simp [r19, r18, r17, r16, r15, r14, hrA2]) (by omega) (by omega)
  have hc5 := tour_runs_call_of (r := 17) (args := [.reg 8, .reg 12, .reg 14, .reg 15, .reg 16, .reg 9, .reg 3])
    (st := ⟨mem5, r20, st₄.pos⟩) C.setValNode_body
    (by simp [evalArgs, Expr.eval, r20, r19, r18, r17, r16, r15, r14, hrA8, hrA9, hrA3]) hrun₅
  have ha21 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 11) (rIdx := 10)
    (base := firstEndBase b) (idx := oldRoot) (val := feO) (st := s_5)
    (by simp [s_5, r20, r19, r18, r17, r16, r15]) (by simp [s_5, r20, r19, r18, r17, r16, r15, r14, hrA10])
    hgeo.2.2.2.2.2.1 hm5_feO
  have hc6 := runs_call_regs4 17 8 13 9 3 (st := ⟨st₅.mem, r21, st₅.pos⟩) C.rotateFront_body
    (by simp [r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA8]) (by simp [r21])
    (by simp [r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA9])
    (by simp [r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA3]) hrun₆
  have hc7 := runs_call_regs4 17 8 12 9 3 (st := s_6) C.rotateFront_body
    (by simp [s_6, r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA8])
    (by simp [s_6, r21, s_5, r20, r19, r18, r17, r16])
    (by simp [s_6, r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA9])
    (by simp [s_6, r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA3]) hrun₇
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_7) (r := 3) (v := heap)
    (by simp [s_7, s_6, r21, s_5, r20, r19, r18, r17, r16, r15, r14, hrA3])
  have hrunB :=
    tour_runs_seq_normal ha14 (tour_runs_seq_normal hst5 (tour_runs_seq_normal ha15 (tour_runs_seq_normal ha16
      (tour_runs_seq_normal ha17 (tour_runs_seq_normal ha18 (tour_runs_seq_normal ha19 (tour_runs_seq_normal ha20
        (tour_runs_seq_normal hc5 (tour_runs_seq_normal ha21 (tour_runs_seq_normal hc6 (tour_runs_seq_normal hc7 hret)))))))))))
  have hfull := runs_seqAppend hrunA hrunB
  refine ⟨s_7, _, rfl, ?_, hfull⟩
  clear * - hcA; simp only [argsSize, Expr.size] at hcA ⊢; omega

/-! ## WordRAM execution assembly for `tourOpLinkBody` -/

theorem tourOpLinkBody_exec {w vCap eCap b e dropRoot heap pos lsProc : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p)
    (hls : p.procs[lsProc]? = some (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {nx ny feD feK opD mkD rtX rtY keepRoot : ℕ}
    {o₁ o₂ o₃ o₄ o₅ o₆ : Outcome} {st₁ st₂ st₃ st₄ st₅ st₆ : State} {c₁ c₂ c₃ c₄ c₅ c₆ : ℕ}
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (he_lt : e < eCap) (hdropLt : dropRoot < vCap) (hkeepLt : keepRoot < vCap)
    (hAxD : nodesBase b vCap eCap + 17 * feD + 17 ≤ heap)
    (hAxX : nodesBase b vCap eCap + 17 * nx + 17 ≤ heap)
    (hAxY : nodesBase b vCap eCap + 17 * ny + 17 ≤ heap)
    (hm_noe : mem (b + HDR_NODE_OF_END) = nodeOfEndBase b vCap)
    (hm_nx : mem (nodeOfEndBase b vCap + 2 * e) = nx)
    (hm_ny : mem (nodeOfEndBase b vCap + (2 * e + 1)) = ny)
    (hm_nb : mem (b + HDR_NODES_BASE) = nodesBase b vCap eCap)
    (hm_fuel : mem (b + HDR_FUEL) = 2 * eCap + 2)
    (hm_ir : mem (b + HDR_IS_ROOT) = isRootBase b vCap)
    (hm_fe : mem (b + HDR_FIRST_END) = firstEndBase b)
    (hm_feD : mem (firstEndBase b + dropRoot) = feD)
    (hm1_opD : Function.update mem (isRootBase b vCap + dropRoot) 0 (nodesBase b vCap eCap + 17 * feD + 9) = opD)
    (hm1_mkD : Function.update mem (isRootBase b vCap + dropRoot) 0 (nodesBase b vCap eCap + 17 * feD + 10) = mkD)
    (hrun₁ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, feD, opD, mkD, 0, 2 * eCap + 2, heap]
        (Function.update mem (isRootBase b vCap + dropRoot) 0) pos) o₁ st₁ c₁)
    (hm1_rtX : st₁.mem (nodesBase b vCap eCap + 17 * nx + 11) = rtX)
    (hrun₂ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, nx, 0, 0, rtX, 2 * eCap + 2, heap] st₁.mem st₁.pos) o₂ st₂ c₂)
    (hm2_rtY : st₂.mem (nodesBase b vCap eCap + 17 * ny + 11) = rtY)
    (hrun₃ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, ny, 0, 0, rtY, 2 * eCap + 2, heap] st₂.mem st₂.pos) o₃ st₃ c₃)
    (hrun₄ : Runs w p ω (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join)
      (startState [nodesBase b vCap eCap, nx, ny, 2 * eCap + 2, heap] st₃.mem st₃.pos) o₄ st₄ c₄)
    (hrun₅ : Runs w p ω (tourRootTagOfBody C.splay.splay)
      (startState [nodesBase b vCap eCap, nx, 2 * eCap + 2, heap] st₄.mem st₄.pos) o₅ st₅ c₅)
    (ho₅ : o₅.value = keepRoot + 1)
    (hm5_feK : st₅.mem (firstEndBase b + keepRoot) = feK)
    (hrun₆ : Runs w p ω (tourRotateFrontBody C.splay.splay C.detachLeft C.join)
      (startState [nodesBase b vCap eCap, feK, 2 * eCap + 2, heap] st₅.mem st₅.pos) o₆ st₆ c₆) :
    ∃ st_fin c_fin, st_fin.mem = st₆.mem ∧
      c_fin ≤ c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + 300 ∧
      Runs w p ω (tourOpLinkBody lsProc C.rootTagOf C.setValNode C.rotateFront)
        (startState [b, e, dropRoot, heap] mem pos) (.returned heap) st_fin c_fin := by
  have hgeo : b + 16 < 2 ^ w ∧ 2 * e + 1 < 2 ^ w ∧ nodeOfEndBase b vCap + (2 * e + 1) < 2 ^ w ∧
      isRootBase b vCap + dropRoot < 2 ^ w ∧ firstEndBase b + dropRoot < 2 ^ w ∧
      firstEndBase b + keepRoot < 2 ^ w ∧ keepRoot < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize, nodeOfEndBase, isRootBase, firstEndBase] at hord_le ⊢; omega
  unfold tourOpLinkBody
  set s0 : State := startState [b, e, dropRoot, heap] mem pos
  set mem1 := Function.update mem (isRootBase b vCap + dropRoot) 0
  have hphaseA : ∃ rA cA,
      rA 3 = heap ∧ rA 6 = nx ∧ rA 7 = ny ∧ rA 8 = nodesBase b vCap eCap ∧ rA 9 = 2 * eCap + 2 ∧
      rA 10 = firstEndBase b ∧ rA 15 = 0 ∧ cA ≤ c₁ + 150 ∧
      Runs w p ω
        (.assign 4 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
         .assign 5 (.bin .mul (.const 2) (.reg 1)) ;;
         .assign 6 (.load (.bin .add (.reg 4) (.reg 5))) ;;
         .assign 7 (.load (.bin .add (.reg 4) (.bin .add (.reg 5) (.const 1)))) ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
         .store (.bin .add (.reg 10) (.reg 2)) (.const 0) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
         .assign 11 (.load (.bin .add (.reg 10) (.reg 2))) ;;
         .assign 12 (.bin .add (.reg 8) (.bin .mul (.const 17) (.reg 11))) ;;
         .assign 13 (.load (.bin .add (.reg 12) (.const 9))) ;;
         .assign 14 (.load (.bin .add (.reg 12) (.const 10))) ;;
         .assign 15 (.const 0) ;;
         .call 16 C.setValNode [.reg 8, .reg 11, .reg 13, .reg 14, .reg 15, .reg 9, .reg 3])
        s0 .normal ⟨st₁.mem, rA, st₁.pos⟩ cA := by
    set r1 := Function.update s0.regs 4 (nodeOfEndBase b vCap)
    set r2 := Function.update r1 5 (2 * e)
    set r3 := Function.update r2 6 nx
    set r4 := Function.update r3 7 ny
    set r5 := Function.update r4 8 (nodesBase b vCap eCap)
    set r6 := Function.update r5 9 (2 * eCap + 2)
    set r7 := Function.update r6 10 (isRootBase b vCap)
    set r8 := Function.update r7 10 (firstEndBase b)
    set r9 := Function.update r8 11 feD
    set r10 := Function.update r9 12 (nodesBase b vCap eCap + 17 * feD)
    set r11 := Function.update r10 13 opD
    set r12 := Function.update r11 14 mkD
    set r13 := Function.update r12 15 0
    set s_1 : State := { st₁ with regs := Function.update r13 16 o₁.value }
    have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_NODE_OF_END)
      (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
      (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hm_noe
    have ha2 : Runs w p ω (.assign 5 (.bin .mul (.const 2) (.reg 1))) ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨2 * e, by simp [Expr.eval, r1, s0, startState, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w)], rfl, rfl, rfl⟩
    have ha3 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 4) (rIdx := 5)
      (base := nodeOfEndBase b vCap) (idx := 2 * e) (val := nx) (st := ⟨mem, r2, pos⟩)
      (by simp [r2, r1]) (by simp [r2]) (by omega) hm_nx
    have ha4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 4) (.bin .add (.reg 5) (.const 1))))) ⟨mem, r3, pos⟩ .normal ⟨mem, r4, pos⟩ 7 :=
      runs_assign_iff.mpr ⟨ny, by
        have hr4v : r3 4 = nodeOfEndBase b vCap := by simp [r3, r2, r1]
        have hr5v : r3 5 = 2 * e := by simp [r3, r2]
        simp only [Expr.eval, hr4v, hr5v, (by omega : 1 < 2 ^ w), BinOp.eval, (by omega : 2 * e + 1 < 2 ^ w),
          hgeo.2.2.1, ↓reduceIte, Option.map_some, hm_ny], rfl, rfl, rfl⟩
    have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_NODES_BASE)
      (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
      (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hm_nb
    have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_FUEL)
      (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r5, pos⟩) (by simp [r5, r4, r3, r2, r1, s0, startState])
      (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hm_fuel
    have ha7 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_IS_ROOT)
      (b := b) (val := isRootBase b vCap) (st := ⟨mem, r6, pos⟩) (by simp [r6, r5, r4, r3, r2, r1, s0, startState])
      (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hm_ir
    have hst1 := runs_store_reg_off_const (w := w) (p := p) (ω := ω) (rBase := 10) (rIdx := 2)
      (base := isRootBase b vCap) (idx := dropRoot) (val := 0) (st := ⟨mem, r7, pos⟩)
      (by simp [r7]) (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]) hgeo.2.2.2.1 (by omega)
    have ha8 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_FIRST_END)
      (b := b) (val := firstEndBase b) (st := ⟨mem1, r7, pos⟩) (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState])
      (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega)
      (by dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_FIRST_END, isRootBase]; omega)]; exact hm_fe)
    have ha9 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 10) (rIdx := 2)
      (base := firstEndBase b) (idx := dropRoot) (val := feD) (st := ⟨mem1, r8, pos⟩)
      (by simp [r8]) (by simp [r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hgeo.2.2.2.2.1
      (by dsimp only [mem1]; rw [Function.update_of_ne (by simp [firstEndBase, isRootBase]; omega)]; exact hm_feD)
    have ha10 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 12) (rNb := 8) (rNode := 11)
      (nb := nodesBase b vCap eCap) (node := feD) (st := ⟨mem1, r9, pos⟩)
      (by simp [r9, r8, r7, r6, r5]) (by simp [r9]) (by omega) (by omega) (by omega)
    have ha11 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 12) (off := 9)
      (b := nodesBase b vCap eCap + 17 * feD) (val := opD) (st := ⟨mem1, r10, pos⟩)
      (by simp [r10]) (by omega) (by omega) hm1_opD
    have ha12 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 12) (off := 10)
      (b := nodesBase b vCap eCap + 17 * feD) (val := mkD) (st := ⟨mem1, r11, pos⟩)
      (by simp [r11, r10]) (by omega) (by omega) hm1_mkD
    have ha13 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 15) (val := 0) (st := ⟨mem1, r12, pos⟩) (by omega)
    have hc1 := tour_runs_call_of (r := 16) (args := [.reg 8, .reg 11, .reg 13, .reg 14, .reg 15, .reg 9, .reg 3])
      (st := ⟨mem1, r13, pos⟩) C.setValNode_body
      (by simp [evalArgs, Expr.eval, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₁
    have hseq :=
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
        (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal hst1
          (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11
            (tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13 hc1)))))))))))))
    refine ⟨s_1.regs, _,
      by simp [s_1, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState],
      by simp [s_1, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3],
      by simp [s_1, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4],
      by simp [s_1, r13, r12, r11, r10, r9, r8, r7, r6, r5],
      by simp [s_1, r13, r12, r11, r10, r9, r8, r7, r6],
      by simp [s_1, r13, r12, r11, r10, r9, r8],
      by simp [s_1, r13],
      ?_, hseq⟩
    clear * -; simp only [argsSize, Expr.size]; omega
  obtain ⟨rA, cA, hrA3, hrA6, hrA7, hrA8, hrA9, hrA10, hrA15, hcA, hrunA⟩ := hphaseA
  set r14 := Function.update rA 12 (nodesBase b vCap eCap + 17 * nx)
  set r15 := Function.update r14 13 rtX
  set s_2 : State := { st₂ with regs := Function.update r15 16 o₂.value }
  set r16 := Function.update s_2.regs 12 (nodesBase b vCap eCap + 17 * ny)
  set r17 := Function.update r16 13 rtY
  set s_3 : State := { st₃ with regs := Function.update r17 16 o₃.value }
  set s_4 : State := { st₄ with regs := Function.update s_3.regs 16 o₄.value }
  set s_5 : State := { st₅ with regs := Function.update s_4.regs 11 o₅.value }
  set r18 := Function.update s_5.regs 11 keepRoot
  set r19 := Function.update r18 12 feK
  set s_6 : State := { st₆ with regs := Function.update r19 16 o₆.value }
  have ha14 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 12) (rNb := 8) (rNode := 6)
    (nb := nodesBase b vCap eCap) (node := nx) (st := ⟨st₁.mem, rA, st₁.pos⟩) hrA8 hrA6 (by omega) (by omega) (by omega)
  have ha15 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 12) (off := 11)
    (b := nodesBase b vCap eCap + 17 * nx) (val := rtX) (st := ⟨st₁.mem, r14, st₁.pos⟩)
    (by simp [r14]) (by omega) (by omega) hm1_rtX
  have hc2 := tour_runs_call_of (r := 16) (args := [.reg 8, .reg 6, .reg 15, .reg 15, .reg 13, .reg 9, .reg 3])
    (st := ⟨st₁.mem, r15, st₁.pos⟩) C.setValNode_body
    (by simp [evalArgs, Expr.eval, r15, r14, hrA8, hrA6, hrA15, hrA9, hrA3]) hrun₂
  have ha16 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 12) (rNb := 8) (rNode := 7)
    (nb := nodesBase b vCap eCap) (node := ny) (st := s_2)
    (by simp [s_2, r15, r14, hrA8]) (by simp [s_2, r15, r14, hrA7]) (by omega) (by omega) (by omega)
  have ha17 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 12) (off := 11)
    (b := nodesBase b vCap eCap + 17 * ny) (val := rtY) (st := ⟨st₂.mem, r16, st₂.pos⟩)
    (by simp [r16]) (by omega) (by omega) hm2_rtY
  have hc3 := tour_runs_call_of (r := 16) (args := [.reg 8, .reg 7, .reg 15, .reg 15, .reg 13, .reg 9, .reg 3])
    (st := ⟨st₂.mem, r17, st₂.pos⟩) C.setValNode_body
    (by simp [evalArgs, Expr.eval, r17, r16, s_2, r15, r14, hrA8, hrA7, hrA15, hrA9, hrA3]) hrun₃
  have hc4 := runs_call_regs5 16 8 6 7 9 3 (st := s_3) hls
    (by simp [s_3, r17, r16, s_2, r15, r14, hrA8]) (by simp [s_3, r17, r16, s_2, r15, r14, hrA6])
    (by simp [s_3, r17, r16, s_2, r15, r14, hrA7]) (by simp [s_3, r17, r16, s_2, r15, r14, hrA9])
    (by simp [s_3, r17, r16, s_2, r15, r14, hrA3]) hrun₄
  have hc5 := runs_call_regs4 11 8 6 9 3 (st := s_4) C.rootTagOf_body
    (by simp [s_4, s_3, r17, r16, s_2, r15, r14, hrA8]) (by simp [s_4, s_3, r17, r16, s_2, r15, r14, hrA6])
    (by simp [s_4, s_3, r17, r16, s_2, r15, r14, hrA9]) (by simp [s_4, s_3, r17, r16, s_2, r15, r14, hrA3]) hrun₅
  have ha18 := runs_assign_reg_sub1 (w := w) (p := p) (ω := ω) (dst := 11) (rSrc := 11) (v := keepRoot + 1)
    (st := s_5) (by simp [s_5, ho₅]) (by omega) (by omega)
  have ha19 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 10) (rIdx := 11)
    (base := firstEndBase b) (idx := keepRoot) (val := feK) (st := ⟨st₅.mem, r18, st₅.pos⟩)
    (by simp [r18, s_5, s_4, s_3, r17, r16, s_2, r15, r14, hrA10]) (by simp [r18]) hgeo.2.2.2.2.2.1 hm5_feK
  have hc6 := runs_call_regs4 16 8 12 9 3 (st := ⟨st₅.mem, r19, st₅.pos⟩) C.rotateFront_body
    (by simp [r19, r18, s_5, s_4, s_3, r17, r16, s_2, r15, r14, hrA8]) (by simp [r19])
    (by simp [r19, r18, s_5, s_4, s_3, r17, r16, s_2, r15, r14, hrA9])
    (by simp [r19, r18, s_5, s_4, s_3, r17, r16, s_2, r15, r14, hrA3]) hrun₆
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_6) (r := 3) (v := heap)
    (by simp [s_6, r19, r18, s_5, s_4, s_3, r17, r16, s_2, r15, r14, hrA3])
  have hrunB :=
    tour_runs_seq_normal ha14 (tour_runs_seq_normal ha15 (tour_runs_seq_normal hc2 (tour_runs_seq_normal ha16
      (tour_runs_seq_normal ha17 (tour_runs_seq_normal hc3 (tour_runs_seq_normal hc4 (tour_runs_seq_normal hc5
        (tour_runs_seq_normal ha18 (tour_runs_seq_normal ha19 (tour_runs_seq_normal hc6 hret))))))))))
  have hfull := runs_seqAppend hrunA hrunB
  refine ⟨s_6, _, rfl, ?_, hfull⟩
  clear * - hcA; simp only [argsSize, Expr.size] at hcA ⊢; omega

end MinCostFlow.SparseCore.Program
