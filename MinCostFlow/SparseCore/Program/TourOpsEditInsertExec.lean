module

public import MinCostFlow.SparseCore.Program.TourOpsEditRotate
import Mathlib.Tactic

/-!
# Single-edit handler for `insertBefore` (Op 0)

Implements and verifies `tourEditInsertBody [b, v, keyX, yWord, heap]`, updating the tour concrete
representation (`TourCoreAt`) for `OrdEdit.insertBefore v (endOfKey keyX) yOpt` in `O(tourLog eCap)`
amortized time with `2` words of heap headroom and without touching memory outside
`[b, ordHandleOf b vCap eCap)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM body -/

/-- Prefix of `tourEditInsertBody`: decodes `sv := slotOf v` into `r5`, allocates or reuses node
`u` for `keyX` into `r6`, initializes `u` as a clean singleton (`isOpen = 1, isMarked = 0,
rootTag = 0`), and loads `endOwnerBase` (`r7`), `firstEndBase` (`r8`), `feOld` (`r9`),
`nodesBase` (`r10`), `fuel` (`r11`). -/
def tourEditInsertAllocBlock (initNodeProc : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
  .assign 6 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) ;;
  .assign 5 (.load (.bin .add (.reg 6) (.reg 1))) ;;
  .cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 1)) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 6 (.load (.bin .add (.reg 7) (.reg 2))) ;;
  .cond (.bin .eq (.reg 6) (.const 0))
    (.assign 6 (.load (.bin .add (.reg 0) (.const HDR_NUM_NODES))) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
     .store (.bin .add (.reg 0) (.const HDR_NUM_NODES)) (.reg 6) ;;
     .store (.bin .add (.reg 7) (.reg 2)) (.reg 6) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
     .store (.bin .add (.reg 8) (.reg 6)) (.reg 2))
    .nop ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 12 (.const 1) ;;
  .assign 13 (.const 0) ;;
  .call 14 initNodeProc [.reg 10, .reg 6, .reg 12, .reg 13, .reg 13] ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.reg 1)))

/-- Nonempty-vertex branch of `tourEditInsertBody` (`feOld ≠ 0`). -/
def tourEditInsertNonemptyBlock (insertBeforeProc setValNodeProc rotateFrontProc : ℕ) : Stmt :=
  .assign 12 (.reg 9) ;;
  .assign 13 (.const 0) ;;
  .cond (.reg 3)
    (.assign 14 (.bin .sub (.reg 3) (.const 1)) ;;
     .assign 15 (.load (.bin .add (.reg 7) (.reg 14))) ;;
     .cond (.bin .eq (.reg 15) (.bin .add (.reg 5) (.const 1)))
       (.assign 15 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
        .assign 12 (.load (.bin .add (.reg 15) (.reg 14))) ;;
        .cond (.bin .eq (.reg 12) (.reg 9)) (.assign 13 (.const 1)) .nop)
       .nop)
    .nop ;;
  .call 14 insertBeforeProc [.reg 10, .reg 6, .reg 12, .reg 11, .reg 4] ;;
  .assign 14 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
  .assign 14 (.load (.bin .add (.reg 14) (.reg 1))) ;;
  .cond (.reg 13)
    (.store (.bin .add (.reg 8) (.reg 1)) (.reg 6) ;;
     .cond (.reg 14)
       (.assign 15 (.bin .add (.reg 10) (.bin .mul (.const 17) (.reg 9))) ;;
        .assign 16 (.load (.bin .add (.reg 15) (.const 9))) ;;
        .assign 17 (.load (.bin .add (.reg 15) (.const 10))) ;;
        .assign 18 (.const 0) ;;
        .call 19 setValNodeProc [.reg 10, .reg 9, .reg 16, .reg 17, .reg 18, .reg 11, .reg 4] ;;
        .assign 16 (.const 1) ;;
        .assign 17 (.const 0) ;;
        .assign 18 (.bin .add (.reg 1) (.const 1)) ;;
        .call 19 setValNodeProc [.reg 10, .reg 6, .reg 16, .reg 17, .reg 18, .reg 11, .reg 4] ;;
        .call 19 rotateFrontProc [.reg 10, .reg 6, .reg 11, .reg 4])
       .nop)
    (.cond (.reg 14)
       (.call 19 rotateFrontProc [.reg 10, .reg 9, .reg 11, .reg 4])
       .nop)

/-- Tour update for `insertBefore v (endOfKey keyX) yOpt`: args `[b, v, keyX, yWord, heap]`.
Writes `endOwner[keyX] := sv + 1` at the end so `yWord = keyX + 1` cannot spoof membership in
`s.ord v`. -/
def tourEditInsertBody (initNodeProc insertBeforeProc setValNodeProc rotateFrontProc : ℕ) : Stmt :=
  seqAppend (tourEditInsertAllocBlock initNodeProc)
    (.cond (.bin .eq (.reg 9) (.const 0))
      (.store (.bin .add (.reg 8) (.reg 1)) (.reg 6) ;;
       .assign 14 (.bin .add (.reg 1) (.const 1)) ;;
       .call 15 initNodeProc [.reg 10, .reg 6, .reg 12, .reg 13, .reg 14])
      (tourEditInsertNonemptyBlock insertBeforeProc setValNodeProc rotateFrontProc) ;;
     .store (.bin .add (.reg 7) (.reg 2)) (.bin .add (.reg 5) (.const 1)) ;;
     .ret (.reg 4))

theorem tourEditInsertBody_noRand (iP ibP svP rfP : ℕ) :
    (tourEditInsertBody iP ibP svP rfP).NoRand := by
  have h1 : (tourEditInsertAllocBlock iP).NoRand := by simp [tourEditInsertAllocBlock, Stmt.NoRand]
  have h2 : (tourEditInsertNonemptyBlock ibP svP rfP).NoRand := by
    simp [tourEditInsertNonemptyBlock, Stmt.NoRand]
  have h3 : ∀ a b, a.NoRand → b.NoRand → (seqAppend a b).NoRand := by
    intro a; induction a with
    | seq x y ihx ihy => intro b hxy hb; exact ⟨hxy.1, ihy b hxy.2 hb⟩
    | _ => intro b ha hb; exact ⟨ha, hb⟩
  exact h3 _ _ h1 (by simp [Stmt.NoRand, h2])

/-! ## Execution helpers -/

/-- Execute `tourEditInsertAllocBlock`, producing an intermediate state where `u` is a clean
detached singleton (`val = ⟨true, false, 0⟩`) at the head of `trees1` and `numNodes1`, `nodeOf1`,
`keyOf1` are updated while `endOwner` and `firstEnd` are still untouched. -/
theorem tourEditInsert_alloc_exec {τ_ord : Type}
    {w vCap eCap b v keyX yWord heap pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hvLt : v < vCap) (hkeyLt : keyX < 2 * eCap) (_hyW : yWord < 2 ^ w)
    (hxFresh : ∀ w', endOfKey keyX ∉ s.ord w')
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) :
    ∃ (u nn1 : ℕ) (nodeOf1 keyOf1 : ℕ → ℕ) (s1 : SplayState TourVal TourSum Unit)
      (trees1 : List AuxTree) (mem1 r1 : ℕ → ℕ) (pos1 c1 : ℕ),
      1 ≤ u ∧ u ≤ nn1 ∧ nn1 ≤ 2 * eCap ∧
      nodeOf1 keyX = u ∧ keyOf1 u = keyX ∧
      (∀ k ≠ keyX, nodeOf1 k = x.nodeOf k) ∧
      (∀ id, 1 ≤ id → id ≤ x.numNodes → keyOf1 id = x.keyOf id) ∧
      (∀ k < 2 * eCap, mem1 (nodeOfEndBase b vCap + k) = nodeOf1 k ∧ nodeOf1 k ≤ nn1) ∧
      (∀ k < 2 * eCap, nodeOf1 k ≠ 0 → keyOf1 (nodeOf1 k) = k) ∧
      (∀ id, 1 ≤ id → id ≤ nn1 →
        mem1 (keyOfNodeBase b vCap eCap + id) = keyOf1 id ∧ keyOf1 id < 2 * eCap ∧ nodeOf1 (keyOf1 id) = id) ∧
      TourHeaderAt vCap eCap b nn1 mem1 ∧
      tourLayout.NodesAt mem1 (nodesBase b vCap eCap) nn1 s1 ∧
      TourForestInv nn1 s1 (AuxTree.node u .leaf .leaf :: trees1) ∧
      forestPhi (AuxTree.node u .leaf .leaf :: trees1) = forestPhi x.trees ∧
      (∀ id, id ∈ (AuxTree.node u .leaf .leaf :: trees1).flatMap AuxTree.toList ↔ 1 ≤ id ∧ id ≤ nn1) ∧
      (∀ t ∈ trees1, t ∈ x.trees ∧ u ∉ t.toList) ∧
      (∀ t ∈ x.trees, t ≠ AuxTree.node u .leaf .leaf → t ∈ trees1) ∧
      s1.nodes u = tourSingletonNode u ⟨true, false, 0⟩ ∧
      (∀ id ≠ u, s1.nodes id = x.st.nodes id) ∧
      (∀ a, b ≤ a → a < ordHandleOf b vCap eCap →
        a ≠ b + HDR_NUM_NODES → a ≠ nodeOfEndBase b vCap + keyX →
        a ≠ keyOfNodeBase b vCap eCap + u →
        (∀ i < 17, a ≠ nodesBase b vCap eCap + 17 * u + i) → mem1 a = mem a) ∧
      (∀ a, a < b ∨ ordHandleOf b vCap eCap ≤ a → mem1 a = mem a) ∧
      r1 0 = b ∧ r1 1 = v ∧ r1 2 = keyX ∧ r1 3 = yWord ∧ r1 4 = heap ∧
      r1 5 = x.slotOf v ∧ r1 6 = u ∧ r1 7 = endOwnerBase b vCap eCap ∧
      r1 8 = firstEndBase b ∧ r1 9 = mem (firstEndBase b + v) ∧
      r1 10 = nodesBase b vCap eCap ∧ r1 11 = 2 * eCap + 2 ∧ r1 12 = 1 ∧ r1 13 = 0 ∧
      c1 ≤ TOUR_SPLICE_COST + 160 ∧
      Runs w p ω (tourEditInsertAllocBlock C.initNode)
        (startState [b, v, keyX, yWord, heap] mem pos) .normal ⟨mem1, r1, pos1⟩ c1 := by
  have hgeo : b + 16 < 2 ^ w ∧ 2 * eCap < 2 ^ w ∧
      slotOfVertBase b vCap eCap + v < 2 ^ w ∧ nodeOfEndBase b vCap + keyX < 2 ^ w ∧
      firstEndBase b + v < 2 ^ w ∧ nodesBase b vCap eCap + 17 * (2 * eCap) + 17 < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize, slotOfVertBase, nodeOfEndBase, firstEndBase, nodesBase] at hord_le ⊢
    omega
  have hhdr := h.header
  set s0 : State := startState [b, v, keyX, yWord, heap] mem pos
  -- Step 1: decode slot `sv := x.slotOf v` into r5, load `u0 := x.nodeOf keyX` into r6
  set rawSlot := mem (slotOfVertBase b vCap eCap + v)
  have hraw_eq : decodeSlot rawSlot v = x.slotOf v := h.slotOf_mem v hvLt
  have hrawW : rawSlot < 2 ^ w := by
    by_cases h0 : rawSlot = 0
    · omega
    · have := (h.slot_bij v hvLt).1; simp only [decodeSlot, h0, ↓reduceIte] at hraw_eq; omega
  set rA1 := Function.update s0.regs 6 (nextArrBase b vCap eCap)
  set rA2 := Function.update rA1 7 eCap
  set rA3 := Function.update rA2 6 (slotOfVertBase b vCap eCap)
  set rA4 := Function.update rA3 5 rawSlot
  set rA5 := Function.update rA4 5 (x.slotOf v)
  set rA6 := Function.update rA5 7 (nodeOfEndBase b vCap)
  set rA7 := Function.update rA6 6 (x.nodeOf keyX)
  have hA1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_NEXT_ARR)
    (b := b) (val := nextArrBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NEXT_ARR]; omega) (by simp [HDR_NEXT_ARR]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hA2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_ECAP)
    (b := b) (val := eCap) (st := ⟨mem, rA1, pos⟩) (by simp [rA1, s0, startState])
    (by rw [HDR_ECAP]; omega) (by rw [HDR_ECAP]; omega) hhdr.2.1
  have hA3 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))))
      ⟨mem, rA2, pos⟩ .normal ⟨mem, rA3, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨slotOfVertBase b vCap eCap, by
      simp [Expr.eval, rA2, rA1, BinOp.eval, (by omega : 2 < 2 ^ w), hgeo.2.1,
        (by rw [← slotOfVertBase_eq]; omega : nextArrBase b vCap eCap + 2 * eCap < 2 ^ w),
        slotOfVertBase_eq], rfl, rfl, rfl⟩
  have hA4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 6) (rIdx := 1)
    (base := slotOfVertBase b vCap eCap) (idx := v) (val := rawSlot) (st := ⟨mem, rA3, pos⟩)
    (by simp [rA3]) (by simp [rA3, rA2, rA1, s0, startState]) hgeo.2.2.1 rfl
  have hA5 : Runs w p ω (.cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 1)))
      ⟨mem, rA4, pos⟩ .normal ⟨mem, rA5, pos⟩ (if rawSlot = 0 then 4 else 6) := by
    have hr := runs_decodeSlot_stmt (w := w) (p := p) (ω := ω) (dst := 5) (rRaw := 5) (rIdx := 1)
      (raw := rawSlot) (idx := v) (st := ⟨mem, rA4, pos⟩) (by simp [rA4])
      (by simp [rA4, rA3, rA2, rA1, s0, startState]) (by omega) hrawW
    simpa [rA5, hraw_eq] using hr
  have hA6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := ⟨mem, rA5, pos⟩)
    (by simp [rA5, rA4, rA3, rA2, rA1, s0, startState]) (by simp [HDR_NODE_OF_END]; omega)
    (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have hA7 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 7) (rIdx := 2)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := x.nodeOf keyX) (st := ⟨mem, rA6, pos⟩)
    (by simp [rA6]) (by simp [rA6, rA5, rA4, rA3, rA2, rA1, s0, startState])
    hgeo.2.2.2.1 (h.nodeOf_mem keyX hkeyLt).1
  -- Step 2: allocate if `x.nodeOf keyX = 0`, else reuse existing inactive node
  -- Unify both cases into post-cond state `(u, nn1, nodeOf1, keyOf1, memA, rB, trees1, cB)`
  have hAlloc : ∃ (u nn1 : ℕ) (nodeOf1 keyOf1 memA rB : ℕ → ℕ) (trees1 : List AuxTree) (cB : ℕ),
      1 ≤ u ∧ u ≤ nn1 ∧ nn1 ≤ 2 * eCap ∧
      nodeOf1 keyX = u ∧ keyOf1 u = keyX ∧
      (∀ k ≠ keyX, nodeOf1 k = x.nodeOf k) ∧
      (∀ id, 1 ≤ id → id ≤ x.numNodes → keyOf1 id = x.keyOf id) ∧
      (∀ k < 2 * eCap, memA (nodeOfEndBase b vCap + k) = nodeOf1 k ∧ nodeOf1 k ≤ nn1) ∧
      (∀ k < 2 * eCap, nodeOf1 k ≠ 0 → keyOf1 (nodeOf1 k) = k) ∧
      (∀ id, 1 ≤ id → id ≤ nn1 →
        memA (keyOfNodeBase b vCap eCap + id) = keyOf1 id ∧ keyOf1 id < 2 * eCap ∧ nodeOf1 (keyOf1 id) = id) ∧
      TourHeaderAt vCap eCap b nn1 memA ∧
      tourLayout.NodesAt memA (nodesBase b vCap eCap) x.numNodes x.st ∧
      ((nn1 = x.numNodes + 1 ∧ u = x.numNodes + 1 ∧ u ∉ x.trees.flatMap AuxTree.toList ∧ trees1 = x.trees) ∨
        (nn1 = x.numNodes ∧ x.trees.Perm (AuxTree.node u .leaf .leaf :: trees1))) ∧
      (∀ id, id ∈ (AuxTree.node u .leaf .leaf :: trees1).flatMap AuxTree.toList ↔ 1 ≤ id ∧ id ≤ nn1) ∧
      (∀ t ∈ trees1, t ∈ x.trees ∧ u ∉ t.toList) ∧
      (∀ t ∈ x.trees, t ≠ AuxTree.node u .leaf .leaf → t ∈ trees1) ∧
      (∀ a, a ≠ b + HDR_NUM_NODES → a ≠ nodeOfEndBase b vCap + keyX →
        a ≠ keyOfNodeBase b vCap eCap + u → memA a = mem a) ∧
      rB 0 = b ∧ rB 1 = v ∧ rB 2 = keyX ∧ rB 3 = yWord ∧ rB 4 = heap ∧
      rB 5 = x.slotOf v ∧ rB 6 = u ∧ cB ≤ 40 ∧
      Runs w p ω
        (.cond (.bin .eq (.reg 6) (.const 0))
          (.assign 6 (.load (.bin .add (.reg 0) (.const HDR_NUM_NODES))) ;;
           .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
           .store (.bin .add (.reg 0) (.const HDR_NUM_NODES)) (.reg 6) ;;
           .store (.bin .add (.reg 7) (.reg 2)) (.reg 6) ;;
           .assign 8 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
           .store (.bin .add (.reg 8) (.reg 6)) (.reg 2))
          .nop)
        ⟨mem, rA7, pos⟩ .normal ⟨memA, rB, pos⟩ cB := by
    by_cases h0 : x.nodeOf keyX = 0
    · have hnn_lt : x.numNodes < 2 * eCap := h.numNodes_lt_of_zero hkeyLt h0
      set u := x.numNodes + 1
      have hcond0 : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨mem, rA7, pos⟩ = some 1 := by
        simp [Expr.eval, rA7, h0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      set rB1 := Function.update rA7 6 x.numNodes
      set rB2 := Function.update rB1 6 u
      set memA1 := Function.update mem (b + HDR_NUM_NODES) u
      set memA2 := Function.update memA1 (nodeOfEndBase b vCap + keyX) u
      set rB3 := Function.update rB2 8 (keyOfNodeBase b vCap eCap)
      set memA3 := Function.update memA2 (keyOfNodeBase b vCap eCap + u) keyX
      have hB1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_NUM_NODES)
        (b := b) (val := x.numNodes) (st := ⟨mem, rA7, pos⟩)
        (by simp [rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState])
        (by simp [HDR_NUM_NODES]; omega) (by simp [HDR_NUM_NODES]; omega) hhdr.2.2.2.1
      have hB2 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1)))
          ⟨mem, rB1, pos⟩ .normal ⟨mem, rB2, pos⟩ 4 :=
        runs_assign_iff.mpr ⟨u, by simp [Expr.eval, rB1, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : x.numNodes + 1 < 2 ^ w), u],
          rfl, rfl, rfl⟩
      have hB3 : Runs w p ω (.store (.bin .add (.reg 0) (.const HDR_NUM_NODES)) (.reg 6))
          ⟨mem, rB2, pos⟩ .normal ⟨memA1, rB2, pos⟩ 5 :=
        runs_store_iff.mpr ⟨b + HDR_NUM_NODES, u,
          by simp [Expr.eval, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState,
            BinOp.eval, HDR_NUM_NODES, (by omega : 3 < 2 ^ w), (by omega : b + 3 < 2 ^ w)],
          by simp [Expr.eval, rB2], rfl, rfl, rfl⟩
      have hB4 : Runs w p ω (.store (.bin .add (.reg 7) (.reg 2)) (.reg 6))
          ⟨memA1, rB2, pos⟩ .normal ⟨memA2, rB2, pos⟩ 5 :=
        runs_store_iff.mpr ⟨nodeOfEndBase b vCap + keyX, u,
          by simp [Expr.eval, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState,
            BinOp.eval, hgeo.2.2.2.1],
          by simp [Expr.eval, rB2], rfl, rfl, rfl⟩
      have hmA2_kn : memA2 (b + HDR_KEY_OF_NODE) = keyOfNodeBase b vCap eCap := by
        dsimp only [memA2, memA1]
        rw [Function.update_of_ne (by simp [HDR_KEY_OF_NODE, nodeOfEndBase]; omega),
          Function.update_of_ne (by simp [HDR_KEY_OF_NODE, HDR_NUM_NODES])]
        exact hhdr.2.2.2.2.2.2.2.2.1
      have hB5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_KEY_OF_NODE)
        (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨memA2, rB2, pos⟩)
        (by simp [rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState])
        (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hmA2_kn
      have hkeyU_lt : keyOfNodeBase b vCap eCap + u < 2 ^ w := by
        simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      have hB6 : Runs w p ω (.store (.bin .add (.reg 8) (.reg 6)) (.reg 2))
          ⟨memA2, rB3, pos⟩ .normal ⟨memA3, rB3, pos⟩ 5 :=
        runs_store_iff.mpr ⟨keyOfNodeBase b vCap eCap + u, keyX,
          by simp [Expr.eval, rB3, rB2, BinOp.eval, hkeyU_lt],
          by simp [Expr.eval, rB3, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
          rfl, rfl, rfl⟩
      have hfrA : ∀ a, a ≠ b + HDR_NUM_NODES → a ≠ nodeOfEndBase b vCap + keyX →
          a ≠ keyOfNodeBase b vCap eCap + u → memA3 a = mem a := fun a h1 h2 h3 => by
        dsimp only [memA3, memA2, memA1]
        rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
      have hhdrA : TourHeaderAt vCap eCap b u memA3 := by
        rcases hhdr with ⟨h0', h1', h2', _, h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14'⟩
        have hf : ∀ k < 16, k ≠ HDR_NUM_NODES → memA3 (b + k) = mem (b + k) := fun k hk hne =>
          hfrA (b + k) (by omega) (by simp [nodeOfEndBase]; omega) (by simp [keyOfNodeBase]; omega)
        have h3' : memA3 (b + HDR_NUM_NODES) = u := by
          dsimp only [memA3, memA2, memA1]
          rw [Function.update_of_ne (by simp [HDR_NUM_NODES, keyOfNodeBase]; omega),
            Function.update_of_ne (by simp [HDR_NUM_NODES, nodeOfEndBase]; omega),
            Function.update_self]
        exact ⟨by rw [hf _ (by decide) (by decide)]; exact h0',
          by rw [hf _ (by decide) (by decide)]; exact h1',
          by rw [hf _ (by decide) (by decide)]; exact h2', h3',
          by rw [hf _ (by decide) (by decide)]; exact h4',
          by rw [hf _ (by decide) (by decide)]; exact h5',
          by rw [hf _ (by decide) (by decide)]; exact h6',
          by rw [hf _ (by decide) (by decide)]; exact h7',
          by rw [hf _ (by decide) (by decide)]; exact h8',
          by rw [hf _ (by decide) (by decide)]; exact h9',
          by rw [hf _ (by decide) (by decide)]; exact h10',
          by rw [hf _ (by decide) (by decide)]; exact h11',
          by rw [hf _ (by decide) (by decide)]; exact h12',
          by rw [hf _ (by decide) (by decide)]; exact h13',
          by rw [hf _ (by decide) (by decide)]; exact h14'⟩
      have hu_fresh : u ∉ x.trees.flatMap AuxTree.toList := fun hm => by
        have := (h.nodes_exact u).mp hm; omega
      refine ⟨u, u, Function.update x.nodeOf keyX u, Function.update x.keyOf u keyX,
        memA3, rB3, x.trees, _, by omega, le_refl _, by omega,
        by simp, by simp, fun k hk => Function.update_of_ne hk _ _,
        fun id _ h2 => Function.update_of_ne (by omega) _ _,
        fun k hk => ?_, fun k hk hnz => ?_, fun id h1 h2 => ?_, hhdrA, ?_,
        Or.inl ⟨rfl, rfl, hu_fresh, rfl⟩, ?_,
        fun t ht => ⟨ht, fun hm => hu_fresh (List.mem_flatMap.mpr ⟨t, ht, hm⟩)⟩,
        fun t ht _ => ht, hfrA,
        by simp [rB3, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rB3, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rB3, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rB3, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rB3, rB2, rB1, rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rB3, rB2, rB1, rA7, rA6, rA5],
        by simp [rB3, rB2], by simp [Expr.size],
        tour_runs_cond_true hcond0 (by omega)
          (tour_runs_seq_normal hB1 (tour_runs_seq_normal hB2 (tour_runs_seq_normal hB3
            (tour_runs_seq_normal hB4 (tour_runs_seq_normal hB5 hB6)))))⟩
      · by_cases hkk : k = keyX
        · subst hkk
          exact ⟨by dsimp only [memA3, memA2]; rw [Function.update_of_ne (by simp [nodeOfEndBase, keyOfNodeBase]; omega), Function.update_self]; simp, by simp⟩
        · rw [hfrA _ (by simp [nodeOfEndBase, HDR_NUM_NODES]; omega) (by omega) (by simp [nodeOfEndBase, keyOfNodeBase]; omega),
            Function.update_of_ne hkk]
          have := h.nodeOf_mem k hk; exact ⟨this.1, by omega⟩
      · by_cases hkk : k = keyX
        · subst hkk; simp
        · rw [Function.update_of_ne hkk] at hnz ⊢
          have hle := (h.nodeOf_mem k hk).2
          rw [Function.update_of_ne (by omega)]; exact h.nodeOf_keyOf k hk hnz
      · by_cases hiu : id = u
        · subst hiu; simp [memA3, hkeyLt]
        · have hle : id ≤ x.numNodes := by omega
          have hkm := h.keyOf_mem id h1 hle
          have hkne : x.keyOf id ≠ keyX := fun heq => by rw [heq, h0] at hkm; omega
          rw [hfrA _ (by simp [keyOfNodeBase, HDR_NUM_NODES]; omega)
            (by simp [keyOfNodeBase, nodeOfEndBase]; omega) (by omega),
            Function.update_of_ne hiu, Function.update_of_ne hkne]
          exact hkm
      · exact NodesAt.congr tourLayout h.nodesAt fun a ha =>
          hfrA a (fun heq => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [nodesBase, HDR_NUM_NODES] at heq this; omega)
            (fun heq => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [nodesBase, nodeOfEndBase] at heq this; omega)
            (fun heq => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [nodesBase, keyOfNodeBase] at heq this; omega)
      · intro id
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons, h.nodes_exact]
        omega
    · -- Reuse existing inactive node `u := x.nodeOf keyX ≠ 0`
      set u := x.nodeOf keyX
      have hu_le : u ≤ x.numNodes := (h.nodeOf_mem keyX hkeyLt).2
      have hu_key : x.keyOf u = keyX := h.nodeOf_keyOf keyX hkeyLt h0
      have hu_inact : ∀ w', endOfKey (x.keyOf u) ∉ s.ord w' := by rwa [hu_key]
      have hu_sing : AuxTree.node u .leaf .leaf ∈ x.trees := h.inactive_single u (by omega) hu_le hu_inact
      set trees1 := x.trees.erase (AuxTree.node u .leaf .leaf)
      have hperm : x.trees.Perm (AuxTree.node u .leaf .leaf :: trees1) := List.perm_cons_erase hu_sing
      have hcond0 : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨mem, rA7, pos⟩ = some 0 := by
        simp [Expr.eval, rA7, BinOp.eval, (by omega : 0 < 2 ^ w), show x.nodeOf keyX ≠ 0 from h0]
      have hnd_all := (h.forestInv.perm hperm).1.nodupAll
      simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append] at hnd_all
      have hu_nt1 : u ∉ trees1.flatMap AuxTree.toList := (List.nodup_cons.mp hnd_all).1
      refine ⟨u, x.numNodes, x.nodeOf, x.keyOf, mem, rA7, trees1, _,
        by omega, hu_le, h.numNodes_le, rfl, hu_key, fun _ _ => rfl, fun _ _ _ => rfl,
        h.nodeOf_mem, h.nodeOf_keyOf, h.keyOf_mem, h.header, h.nodesAt, Or.inr ⟨rfl, hperm⟩,
        fun id => by
          have hmem_iff : id ∈ (AuxTree.node u .leaf .leaf :: trees1).flatMap AuxTree.toList ↔ id ∈ x.trees.flatMap AuxTree.toList := by
            simp only [List.mem_flatMap]
            exact ⟨fun ⟨t, ht, hid⟩ => ⟨t, hperm.mem_iff.mpr ht, hid⟩, fun ⟨t, ht, hid⟩ => ⟨t, hperm.mem_iff.mp ht, hid⟩⟩
          exact hmem_iff.trans (h.nodes_exact id),
        fun t ht => ⟨List.mem_of_mem_erase ht, fun hm => hu_nt1 (List.mem_flatMap.mpr ⟨t, ht, hm⟩)⟩,
        fun t ht hne => (List.mem_erase_of_ne hne).mpr ht,
        fun _ _ _ _ => rfl,
        by simp [rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rA7, rA6, rA5, rA4, rA3, rA2, rA1, s0, startState],
        by simp [rA7, rA6, rA5], by simp [rA7, u], by simp [Expr.size],
        tour_runs_cond_false hcond0 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)⟩
  obtain ⟨u, nn1, nodeOf1, keyOf1, memA, rB, trees1, cB, hu1, hunn, hnn_le, hn1k, hk1u, hn1_ne, hk1_old,
    hn1_mem, hn1_ko, hk1_mem, hhdrA, hnA, hcase, hexact1, ht1_sub, ht1_mem, hfrA,
    hrB0, hrB1, hrB2, hrB3, hrB4, hrB5, hrB6, hcB, hrunB⟩ := hAlloc
  -- Step 3: call `initNode [nb, u, 1, 0, 0]`, then load `endOwnerBase`, `firstEndBase`, `feOld`
  set rC1 := Function.update rB 10 (nodesBase b vCap eCap)
  set rC2 := Function.update rC1 11 (2 * eCap + 2)
  set rC3 := Function.update rC2 12 1
  set rC4 := Function.update rC3 13 0
  have hC1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨memA, rB, pos⟩) hrB0
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdrA.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨memA, rC1, pos⟩) (by simp [rC1, hrB0])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdrA.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hC3 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 12) (val := 1) (st := ⟨memA, rC2, pos⟩) (by omega)
  have hC4 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 13) (val := 0) (st := ⟨memA, rC3, pos⟩) (by omega)
  have hAu_lt : nodesBase b vCap eCap + 17 * u + 17 < 2 ^ w := by omega
  obtain ⟨oI, stI, cI, hrunI, ⟨hnuI, hfrI⟩, hcI⟩ :=
    tourInitNodeBody_runs (w := w) (nb := nodesBase b vCap eCap) (x := u) (isOpen := 1)
      (isMarked := 0) (rootTag := 0) (pos := pos) (p := p) ω (mem := memA) hAu_lt hwide
  have hC5 := runs_call_regs5 14 10 6 12 13 13 (st := ⟨memA, rC4, pos⟩) C.initNode_body
    (by simp [rC4, rC3, rC2, rC1]) (by simp [rC4, rC3, rC2, rC1, hrB6])
    (by simp [rC4, rC3]) (by simp [rC4]) (by simp [rC4]) hrunI
  -- Apply fresh/reuse invariant preservation
  set s1 : SplayState TourVal TourSum Unit :=
    { nodes := Function.update x.st.nodes u (tourSingletonNode u ⟨true, false, 0⟩) }
  have hnuI' : tourLayout.NodeAt stI.mem (nodesBase b vCap eCap) u (tourSingletonNode u ⟨true, false, 0⟩) := by
    simpa [tourSingletonNode] using hnuI
  have hNodesInvPhi : tourLayout.NodesAt stI.mem (nodesBase b vCap eCap) nn1 s1 ∧
      TourForestInv nn1 s1 (AuxTree.node u .leaf .leaf :: trees1) ∧
      forestPhi (AuxTree.node u .leaf .leaf :: trees1) = forestPhi x.trees := by
    rcases hcase with ⟨rfl, rfl, _, rfl⟩ | ⟨rfl, hperm⟩
    · exact tourInitNode_fresh_succ_preserves hnA h.forestInv hnuI' hfrI
    · have ⟨hn', hi'⟩ := tourInitNode_reuse_preserves hnA (h.forestInv.perm hperm).1 hnuI' hfrI
      exact ⟨hn', hi', (forestPhi_perm hperm).symm⟩
  -- Non-node memory preserved by `initNode`
  have hpreI : ∀ a < nodesBase b vCap eCap, stI.mem a = memA a := fun a ha =>
    hfrI a fun i _ => by omega
  have hhdrI : TourHeaderAt vCap eCap b nn1 stI.mem := by
    rcases hhdrA with ⟨h0', h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14'⟩
    have hf : ∀ k < 16, stI.mem (b + k) = memA (b + k) := fun k hk =>
      hpreI _ (by simp [nodesBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0', by rw [hf _ (by decide)]; exact h1',
      by rw [hf _ (by decide)]; exact h2', by rw [hf _ (by decide)]; exact h3',
      by rw [hf _ (by decide)]; exact h4', by rw [hf _ (by decide)]; exact h5',
      by rw [hf _ (by decide)]; exact h6', by rw [hf _ (by decide)]; exact h7',
      by rw [hf _ (by decide)]; exact h8', by rw [hf _ (by decide)]; exact h9',
      by rw [hf _ (by decide)]; exact h10', by rw [hf _ (by decide)]; exact h11',
      by rw [hf _ (by decide)]; exact h12', by rw [hf _ (by decide)]; exact h13',
      by rw [hf _ (by decide)]; exact h14'⟩
  have hfe_eqI : stI.mem (firstEndBase b + v) = mem (firstEndBase b + v) := by
    rw [hpreI _ (by simp [firstEndBase, nodesBase]; omega)]
    exact hfrA _ (by simp [firstEndBase, HDR_NUM_NODES]; omega)
      (by simp [firstEndBase, nodeOfEndBase]; omega) (by simp [firstEndBase, keyOfNodeBase]; omega)
  set rC5 := Function.update rC4 14 oI.value
  set rC6 := Function.update rC5 7 (endOwnerBase b vCap eCap)
  set rC7 := Function.update rC6 8 (firstEndBase b)
  set rC8 := Function.update rC7 9 (mem (firstEndBase b + v))
  have hC6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_END_OWNER)
    (b := b) (val := endOwnerBase b vCap eCap) (st := { stI with regs := rC5 })
    (by simp [rC5, rC4, rC3, rC2, rC1, hrB0]) (by simp [HDR_END_OWNER]; omega)
    (by simp [HDR_END_OWNER]; omega) hhdrI.2.2.2.2.2.2.2.1
  have hC7 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_FIRST_END)
    (b := b) (val := firstEndBase b) (st := { stI with regs := rC6 })
    (by simp [rC6, rC5, rC4, rC3, rC2, rC1, hrB0]) (by simp [HDR_FIRST_END]; omega)
    (by simp [HDR_FIRST_END]; omega) hhdrI.2.2.2.2.1
  have hC8 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 8) (rIdx := 1)
    (base := firstEndBase b) (idx := v) (val := mem (firstEndBase b + v)) (st := { stI with regs := rC7 })
    (by simp [rC7]) (by simp [rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB1]) hgeo.2.2.2.2.1 hfe_eqI
  have hfull : Runs w p ω (tourEditInsertAllocBlock C.initNode)
      (startState [b, v, keyX, yWord, heap] mem pos) .normal ⟨stI.mem, rC8, stI.pos⟩ _ :=
    tour_runs_seq_normal hA1 (tour_runs_seq_normal hA2 (tour_runs_seq_normal hA3
      (tour_runs_seq_normal hA4 (tour_runs_seq_normal hA5 (tour_runs_seq_normal hA6 (tour_runs_seq_normal hA7
      (tour_runs_seq_normal hrunB (tour_runs_seq_normal hC1 (tour_runs_seq_normal hC2 (tour_runs_seq_normal hC3
      (tour_runs_seq_normal hC4 (tour_runs_seq_normal hC5 (tour_runs_seq_normal hC6 (tour_runs_seq_normal hC7 hC8))))))))))))))
  refine ⟨u, nn1, nodeOf1, keyOf1, s1, trees1, stI.mem, rC8, stI.pos, _,
    hu1, hunn, hnn_le, hn1k, hk1u, hn1_ne, hk1_old,
    fun k hk => by rw [hpreI _ (by simp [nodeOfEndBase, nodesBase]; omega)]; exact hn1_mem k hk,
    hn1_ko,
    fun id h1 h2 => by rw [hpreI _ (by simp [keyOfNodeBase, nodesBase]; omega)]; exact hk1_mem id h1 h2,
    hhdrI, hNodesInvPhi.1, hNodesInvPhi.2.1, hNodesInvPhi.2.2, hexact1, ht1_sub, ht1_mem,
    by simp [s1], fun id hid => by simp [s1, Function.update_of_ne hid],
    fun a _ _ h1 h2 h3 h4 => (hfrI a h4).trans (hfrA a h1 h2 h3),
    fun a ha => (hfrI a fun i hi => by
      simp [nodesBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega).trans
      (hfrA a
        (by simp [HDR_NUM_NODES, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega)
        (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega)
        (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega)),
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB0],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB1],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB2],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB3],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB4],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB5],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1, hrB6],
    by simp [rC8, rC7, rC6], by simp [rC8, rC7], by simp [rC8],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2, rC1],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3, rC2],
    by simp [rC8, rC7, rC6, rC5, rC4, rC3],
    by simp [rC8, rC7, rC6, rC5, rC4],
    by clear * - hcB hcI; split_ifs at * <;> omega, hfull⟩

/-- Execute the target-selection prefix of `tourEditInsertNonemptyBlock`, computing `yNode` (`r12`)
and `headChanged` (`r13`). -/
theorem tourEditInsert_target_exec {w vCap eCap b v keyX yWord heap sv u feOld pos : ℕ}
    {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ} {rIn : ℕ → ℕ}
    {s : TourAbs} {aOld : End} {nodeOf1 : ℕ → ℕ}
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w)
    (hvLt : v < vCap) (hyWord_le : yWord ≤ 2 * eCap) (hsvLt : sv < vCap)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w)
    (hhead : (s.ord v).head? = some aOld) (haOld_lt : endKey aOld < 2 * eCap)
    (hfeOld : feOld = nodeOf1 (endKey aOld))
    (hm_ne : mem (b + HDR_NODE_OF_END) = nodeOfEndBase b vCap)
    (hn1_mem : ∀ k < 2 * eCap, mem (nodeOfEndBase b vCap + k) = nodeOf1 k)
    (hn1_inj : ∀ k1 k2, k1 < 2 * eCap → k2 < 2 * eCap → nodeOf1 k1 ≠ 0 → nodeOf1 k1 = nodeOf1 k2 → k1 = k2)
    (hfe_nz : feOld ≠ 0)
    (heo_iff : ∀ k < 2 * eCap, mem (endOwnerBase b vCap eCap + k) = sv + 1 ↔ endOfKey k ∈ s.ord v)
    (hr0 : rIn 0 = b) (hr1 : rIn 1 = v) (hr2 : rIn 2 = keyX) (hr3 : rIn 3 = yWord)
    (hr4 : rIn 4 = heap) (hr5 : rIn 5 = sv) (hr6 : rIn 6 = u)
    (hr7 : rIn 7 = endOwnerBase b vCap eCap) (hr8 : rIn 8 = firstEndBase b) (hr9 : rIn 9 = feOld)
    (hr10 : rIn 10 = nodesBase b vCap eCap) (hr11 : rIn 11 = 2 * eCap + 2) :
    let yOpt : Option End := if yWord = 0 then none else some (endOfKey (yWord - 1))
    ∃ yEnd yNode headCh rT cT,
      yEnd ∈ s.ord v ∧ yNode = nodeOf1 (endKey yEnd) ∧
      (yOpt = some yEnd ∨ ((yOpt = none ∨ ∃ y', yOpt = some y' ∧ y' ∉ s.ord v) ∧ (s.ord v).head? = some yEnd)) ∧
      (headCh = 1 ↔ yOpt = some aOld) ∧ (headCh = 0 ∨ headCh = 1) ∧
      rT 0 = b ∧ rT 1 = v ∧ rT 2 = keyX ∧ rT 3 = yWord ∧ rT 4 = heap ∧ rT 5 = sv ∧
      rT 6 = u ∧ rT 7 = endOwnerBase b vCap eCap ∧ rT 8 = firstEndBase b ∧ rT 9 = feOld ∧
      rT 10 = nodesBase b vCap eCap ∧ rT 11 = 2 * eCap + 2 ∧ rT 12 = yNode ∧ rT 13 = headCh ∧
      cT ≤ 50 ∧
      Runs w p ω
        (.assign 12 (.reg 9) ;;
         .assign 13 (.const 0) ;;
         .cond (.reg 3)
           (.assign 14 (.bin .sub (.reg 3) (.const 1)) ;;
            .assign 15 (.load (.bin .add (.reg 7) (.reg 14))) ;;
            .cond (.bin .eq (.reg 15) (.bin .add (.reg 5) (.const 1)))
              (.assign 15 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
               .assign 12 (.load (.bin .add (.reg 15) (.reg 14))) ;;
               .cond (.bin .eq (.reg 12) (.reg 9)) (.assign 13 (.const 1)) .nop)
              .nop)
           .nop)
        ⟨mem, rIn, pos⟩ .normal ⟨mem, rT, pos⟩ cT := by
  intro yOpt
  have haOld_mem : aOld ∈ s.ord v := List.mem_of_head? hhead
  set r1 := Function.update rIn 12 feOld
  set r2 := Function.update r1 13 0
  have h1 : Runs w p ω (.assign 12 (.reg 9)) ⟨mem, rIn, pos⟩ .normal ⟨mem, r1, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨feOld, by simp [Expr.eval, hr9], rfl, rfl, rfl⟩
  have h2 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 13) (val := 0) (st := ⟨mem, r1, pos⟩) (by omega)
  by_cases hy0 : yWord = 0
  · have hcond : (Expr.reg 3).eval w ⟨mem, r2, pos⟩ = some 0 := by simp [Expr.eval, r2, r1, hr3, hy0]
    refine ⟨aOld, feOld, 0, r2, _, haOld_mem, hfeOld, Or.inr ⟨Or.inl (by simp [yOpt, hy0]), hhead⟩,
      by simp [yOpt, hy0], Or.inl rfl,
      by simp [r2, r1, hr0], by simp [r2, r1, hr1], by simp [r2, r1, hr2], by simp [r2, r1, hr3],
      by simp [r2, r1, hr4], by simp [r2, r1, hr5], by simp [r2, r1, hr6], by simp [r2, r1, hr7],
      by simp [r2, r1, hr8], by simp [r2, r1, hr9], by simp [r2, r1, hr10], by simp [r2, r1, hr11],
      by simp [r2, r1], by simp [r2], by simp [Expr.size],
      tour_runs_seq_normal h1 (tour_runs_seq_normal h2 (tour_runs_cond_false hcond (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))⟩
  · have hkyLt : yWord - 1 < 2 * eCap := by omega
    set kY := yWord - 1
    set y' := endOfKey kY
    have hcond : (Expr.reg 3).eval w ⟨mem, r2, pos⟩ = some yWord := by simp [Expr.eval, r2, r1, hr3]
    set r3 := Function.update r2 14 kY
    set eoY := mem (endOwnerBase b vCap eCap + kY)
    set r4 := Function.update r3 15 eoY
    have h3 : Runs w p ω (.assign 14 (.bin .sub (.reg 3) (.const 1))) ⟨mem, r2, pos⟩ .normal ⟨mem, r3, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨kY, by simp [Expr.eval, r2, r1, hr3, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : yWord - 1 < 2 ^ w), kY], rfl, rfl, rfl⟩
    have heo_addr : endOwnerBase b vCap eCap + kY < 2 ^ w := by
      simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
    have h4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 7) (rIdx := 14)
      (base := endOwnerBase b vCap eCap) (idx := kY) (val := eoY) (st := ⟨mem, r3, pos⟩)
      (by simp [r3, r2, r1, hr7]) (by simp [r3]) heo_addr rfl
    by_cases hy_mem : y' ∈ s.ord v
    · have heo1 : eoY = sv + 1 := (heo_iff kY hkyLt).mpr hy_mem
      have hcond_eo : (Expr.bin .eq (.reg 15) (.bin .add (.reg 5) (.const 1))).eval w ⟨mem, r4, pos⟩ = some 1 := by
        simp [Expr.eval, r4, r3, r2, r1, hr5, heo1, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : sv + 1 < 2 ^ w)]
      set r5 := Function.update r4 15 (nodeOfEndBase b vCap)
      set yN := nodeOf1 kY
      set r6 := Function.update r5 12 yN
      have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
      have hne_addr : nodeOfEndBase b vCap + kY < 2 ^ w := by
        simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      have h5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 0) (off := HDR_NODE_OF_END)
        (b := b) (val := nodeOfEndBase b vCap) (st := ⟨mem, r4, pos⟩)
        (by simp [r4, r3, r2, r1, hr0]) (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hm_ne
      have h6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 15) (rIdx := 14)
        (base := nodeOfEndBase b vCap) (idx := kY) (val := yN) (st := ⟨mem, r5, pos⟩)
        (by simp [r5]) (by simp [r5, r4, r3]) hne_addr (hn1_mem kY hkyLt)
      by_cases hyeq : yN = feOld
      · have hky_eq : kY = endKey aOld := by
          have := hn1_inj (endKey aOld) kY haOld_lt hkyLt (hfeOld ▸ hfe_nz) (by rw [← hfeOld]; exact hyeq.symm)
          exact this.symm
        have hy'_eq : y' = aOld := by simp [y', hky_eq, endOfKey_endKey]
        have hcond_eq : (Expr.bin .eq (.reg 12) (.reg 9)).eval w ⟨mem, r6, pos⟩ = some 1 := by
          simp [Expr.eval, r6, r5, r4, r3, r2, r1, hr9, hyeq, BinOp.eval, (by omega : 1 < 2 ^ w)]
        set r7 := Function.update r6 13 1
        have h7 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 13) (val := 1) (st := ⟨mem, r6, pos⟩) (by omega)
        refine ⟨y', yN, 1, r7, _, hy_mem, by simp [yN, y', endKey_endOfKey'],
          Or.inl (by simp [yOpt, hy0, y', kY]), by simp [yOpt, hy0, hy'_eq, y', kY], Or.inr rfl,
          by simp [r7, r6, r5, r4, r3, r2, r1, hr0], by simp [r7, r6, r5, r4, r3, r2, r1, hr1],
          by simp [r7, r6, r5, r4, r3, r2, r1, hr2], by simp [r7, r6, r5, r4, r3, r2, r1, hr3],
          by simp [r7, r6, r5, r4, r3, r2, r1, hr4], by simp [r7, r6, r5, r4, r3, r2, r1, hr5],
          by simp [r7, r6, r5, r4, r3, r2, r1, hr6], by simp [r7, r6, r5, r4, r3, r2, r1, hr7],
          by simp [r7, r6, r5, r4, r3, r2, r1, hr8], by simp [r7, r6, r5, r4, r3, r2, r1, hr9],
          by simp [r7, r6, r5, r4, r3, r2, r1, hr10], by simp [r7, r6, r5, r4, r3, r2, r1, hr11],
          by simp [r7, r6], by simp [r7], by simp [Expr.size],
          tour_runs_seq_normal h1 (tour_runs_seq_normal h2 (tour_runs_cond_true hcond hy0
            (tour_runs_seq_normal h3 (tour_runs_seq_normal h4 (tour_runs_cond_true hcond_eo (by omega)
              (tour_runs_seq_normal h5 (tour_runs_seq_normal h6 (tour_runs_cond_true hcond_eq (by omega) h7))))))))⟩
      · have hy'_ne : y' ≠ aOld := fun heq => hyeq (by rw [hfeOld, ← heq]; simp [yN, y', endKey_endOfKey'])
        have hcond_eq : (Expr.bin .eq (.reg 12) (.reg 9)).eval w ⟨mem, r6, pos⟩ = some 0 := by
          simp [Expr.eval, r6, r5, r4, r3, r2, r1, hr9, hyeq, BinOp.eval, (by omega : 0 < 2 ^ w)]
        refine ⟨y', yN, 0, r6, _, hy_mem, by simp [yN, y', endKey_endOfKey'],
          Or.inl (by simp [yOpt, hy0, y', kY]), by simp [yOpt, hy0, hy'_ne, y', kY], Or.inl rfl,
          by simp [r6, r5, r4, r3, r2, r1, hr0], by simp [r6, r5, r4, r3, r2, r1, hr1],
          by simp [r6, r5, r4, r3, r2, r1, hr2], by simp [r6, r5, r4, r3, r2, r1, hr3],
          by simp [r6, r5, r4, r3, r2, r1, hr4], by simp [r6, r5, r4, r3, r2, r1, hr5],
          by simp [r6, r5, r4, r3, r2, r1, hr6], by simp [r6, r5, r4, r3, r2, r1, hr7],
          by simp [r6, r5, r4, r3, r2, r1, hr8], by simp [r6, r5, r4, r3, r2, r1, hr9],
          by simp [r6, r5, r4, r3, r2, r1, hr10], by simp [r6, r5, r4, r3, r2, r1, hr11],
          by simp [r6], by simp [r6, r5, r4, r3, r2], by simp [Expr.size],
          tour_runs_seq_normal h1 (tour_runs_seq_normal h2 (tour_runs_cond_true hcond hy0
            (tour_runs_seq_normal h3 (tour_runs_seq_normal h4 (tour_runs_cond_true hcond_eo (by omega)
              (tour_runs_seq_normal h5 (tour_runs_seq_normal h6 (tour_runs_cond_false hcond_eq (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))))))⟩
    · have heo0 : eoY ≠ sv + 1 := mt (heo_iff kY hkyLt).mp hy_mem
      have hy'_ne : y' ≠ aOld := fun heq => hy_mem (heq ▸ haOld_mem)
      have hcond_eo : (Expr.bin .eq (.reg 15) (.bin .add (.reg 5) (.const 1))).eval w ⟨mem, r4, pos⟩ = some 0 := by
        simp [Expr.eval, r4, r3, r2, r1, hr5, heo0, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : sv + 1 < 2 ^ w), (by omega : 0 < 2 ^ w)]
      refine ⟨aOld, feOld, 0, r4, _, haOld_mem, hfeOld,
        Or.inr ⟨Or.inr ⟨y', by simp [yOpt, hy0, y', kY], hy_mem⟩, hhead⟩,
        by simp [yOpt, hy0, hy'_ne, y', kY], Or.inl rfl,
        by simp [r4, r3, r2, r1, hr0], by simp [r4, r3, r2, r1, hr1], by simp [r4, r3, r2, r1, hr2],
        by simp [r4, r3, r2, r1, hr3], by simp [r4, r3, r2, r1, hr4], by simp [r4, r3, r2, r1, hr5],
        by simp [r4, r3, r2, r1, hr6], by simp [r4, r3, r2, r1, hr7], by simp [r4, r3, r2, r1, hr8],
        by simp [r4, r3, r2, r1, hr9], by simp [r4, r3, r2, r1, hr10], by simp [r4, r3, r2, r1, hr11],
        by simp [r4, r3, r2, r1], by simp [r4, r3, r2], by simp [Expr.size],
        tour_runs_seq_normal h1 (tour_runs_seq_normal h2 (tour_runs_cond_true hcond hy0
          (tour_runs_seq_normal h3 (tour_runs_seq_normal h4 (tour_runs_cond_false hcond_eo (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩))))))⟩


end MinCostFlow.SparseCore.Program
