module

public import MinCostFlow.SparseCore.Program.TourOpsEditMoveCore
public import MinCostFlow.SparseCore.Program.TourOpsMoveSplit
import Mathlib.Tactic

/-!
# Post-split ownership, `firstEnd`, and root updates for `moveEnds` (Op 0)

Provides two verified WordRAM sub-statements called by `tourEditMoveBody` after
`tourMoveSplitLoopBody` splits `v`'s tour into `(tKeep?, tMove?)`:
- `tourMoveOwnersStmt`: optionally swaps `slotOf`/`vertOf` (`tag == 2`), updates `endOwner` for
  the `m` selected nodes at `pairsPtr`, finds `feKeep` and `feMove` via `tourWalkFrontBody`, and
  stores `firstEnd[v]` and `firstEnd[v']`.
- `tourMoveRootsStmt`: updates `isRoot`, `rootTag`, and rotates the surviving root `r` back to
  the front of its tour in all three root cases (`v ∈ R`, `v ∉ R ∧ F'.Connected v r`, and
  `v ∉ R ∧ ¬F'.Connected v r`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM sub-statements -/

/-- Set `rootTag := rVert + 1` on `rNode` if `rNode ≠ 0`, preserving `isOpen` and `isMarked`.
Expects `r9 = nb`, `r10 = fuel`, `r15 = hOut`; clobbers `r20..r24`. -/
def setRootTagIfNzStmt (rNode rVert setValProc : ℕ) : Stmt :=
  .cond (.reg rNode)
    (.assign 20 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg rNode))) ;;
     .assign 21 (.load (.bin .add (.reg 20) (.const 9))) ;;
     .assign 22 (.load (.bin .add (.reg 20) (.const 10))) ;;
     .assign 23 (.bin .add (.reg rVert) (.const 1)) ;;
     .call 24 setValProc [.reg 9, .reg rNode, .reg 21, .reg 22, .reg 23, .reg 10, .reg 15])
    .nop

/-- Update `slotOf`/`vertOf` (when `tag == 2`), `endOwner` for the `m` ends at `pairsPtr`,
`feKeep`/`feMove` via `walkFrontProc`, and `firstEnd[v]`/`firstEnd[v']`.
Expects `r0 = b`, `r2 = pairsPtr`, `r3 = tag`, `r4 = v`, `r5 = v'`, `r9 = nb`, `r10 = fuel`,
`r12 = sv`, `r13 = m`, `r15 = hOut`, `r16 = optRoot tKeep?`, `r17 = optRoot tMove?`. -/
def tourMoveOwnersStmt (walkFrontProc : ℕ) : Stmt :=
  .assign 18 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
  .assign 19 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
  .assign 20 (.load (.bin .add (.reg 0) (.const HDR_VCAP))) ;;
  .assign 18 (.bin .add (.reg 18) (.bin .mul (.const 2) (.reg 19))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 20)) ;;
  .assign 20 (.load (.bin .add (.reg 18) (.reg 5))) ;;
  .cond (.reg 20)
    (.assign 20 (.bin .sub (.reg 20) (.const 1)))
    (.assign 20 (.reg 5)) ;;
  .cond (.bin .eq (.reg 3) (.const 2))
    (.store (.bin .add (.reg 18) (.reg 4)) (.bin .add (.reg 20) (.const 1)) ;;
     .store (.bin .add (.reg 18) (.reg 5)) (.bin .add (.reg 12) (.const 1)) ;;
     .store (.bin .add (.reg 19) (.reg 12)) (.bin .add (.reg 5) (.const 1)) ;;
     .store (.bin .add (.reg 19) (.reg 20)) (.bin .add (.reg 4) (.const 1)))
    .nop ;;
  .assign 18 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
  .assign 19 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
  .assign 20 (.bin .add (.reg 20) (.const 1)) ;;
  .assign 21 (.const 0) ;;
  .loop (.bin .lt (.reg 21) (.reg 13))
    (.assign 22 (.load (.bin .add (.reg 2) (.bin .add (.bin .add (.reg 21) (.reg 21)) (.const 1)))) ;;
     .assign 22 (.load (.bin .add (.reg 19) (.reg 22))) ;;
     .store (.bin .add (.reg 18) (.reg 22)) (.reg 20) ;;
     .assign 21 (.bin .add (.reg 21) (.const 1))) ;;
  .call 16 walkFrontProc [.reg 9, .reg 16, .reg 10, .reg 15] ;;
  .call 17 walkFrontProc [.reg 9, .reg 17, .reg 10, .reg 15] ;;
  .assign 18 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
  .store (.bin .add (.reg 18) (.reg 4)) (.reg 16) ;;
  .store (.bin .add (.reg 18) (.reg 5)) (.reg 17)

/-- Update `isRoot`, `rootTag`, and rotate the surviving root `r` back to the front of its tour.
Expects `r0 = b`, `r4 = v`, `r5 = v'`, `r9 = nb`, `r10 = fuel`, `r11 = irV`, `r15 = hOut`,
`r16 = feKeep`, `r17 = feMove`. -/
def tourMoveRootsStmt (setValProc rotFrontProc : ℕ) : Stmt :=
  .assign 18 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
  .cond (.reg 11)
    (.store (.bin .add (.reg 18) (.reg 5)) (.const 1) ;;
     setRootTagIfNzStmt 16 4 setValProc ;;
     setRootTagIfNzStmt 17 5 setValProc)
    (.cond (.bin .eq (.reg 16) (.const 0))
       (.assign 19 (.const 0))
       (.assign 19 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 16))) (.const 15)))) ;;
     .cond (.reg 19)
       (.assign 19 (.bin .sub (.reg 19) (.const 1)) ;;
        .assign 20 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
        .assign 20 (.load (.bin .add (.reg 20) (.reg 19))) ;;
        .call 21 rotFrontProc [.reg 9, .reg 20, .reg 10, .reg 15] ;;
        .store (.bin .add (.reg 18) (.reg 5)) (.const 1) ;;
        setRootTagIfNzStmt 17 5 setValProc)
       (.assign 19 (.bin .sub (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 17))) (.const 15))) (.const 1)) ;;
        .assign 20 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
        .assign 20 (.load (.bin .add (.reg 20) (.reg 19))) ;;
        .call 21 rotFrontProc [.reg 9, .reg 20, .reg 10, .reg 15] ;;
        .store (.bin .add (.reg 18) (.reg 4)) (.const 1) ;;
        setRootTagIfNzStmt 16 4 setValProc))

theorem tourMovePost_stmts_noRand (wF sV rF : ℕ) :
    (tourMoveOwnersStmt wF).NoRand ∧ (tourMoveRootsStmt sV rF).NoRand := by
  simp [tourMoveOwnersStmt, tourMoveRootsStmt, setRootTagIfNzStmt, Stmt.NoRand]

/-! ## Helper: `setRootTagIfNzStmt` run theorem -/

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

/-- Execute `setRootTagIfNzStmt rNode rVert C.setValNode` on an optional tree `t?` whose root
(when `some t`) is `rNode`. Sets `rootTag := vert + 1` on `rNode` without changing `isOpen`,
`isMarked`, or `t.toList`. -/
theorem setRootTagIfNz_runs {w nb cap fuel hOut vert rNode rVert : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {st : State} {sT : SplayState TourVal TourSum Unit}
    {t? : Option AuxTree} {rest : List AuxTree}
    (hrn_lt : rNode < 20) (hrv_lt : rVert < 20)
    (hrNode : st.regs rNode = optRoot t?) (hrVert : st.regs rVert = vert)
    (hr9 : st.regs 9 = nb) (hr10 : st.regs 10 = fuel) (hr15 : st.regs 15 = hOut)
    (hnodes : tourLayout.NodesAt st.mem nb cap sT)
    (hinv : TourForestInv cap sT (optTrees t? ++ rest))
    (hvals : TourValsOk w cap sT)
    (hvertW : vert + 1 < 2 ^ w) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap hOut 2 st.mem) :
    ∃ t'? s' st' c,
      Runs w p ω (setRootTagIfNzStmt rNode rVert C.setValNode) st .normal st' c ∧
      (∀ k < 20, st'.regs k = st.regs k) ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap hOut st.mem st'.mem ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t? ∧
      (t? = none → ∀ u ≤ cap, (s'.nodes u).val = (sT.nodes u).val) ∧
      (∀ t, t? = some t →
        (s'.nodes t.rootId).val = { (sT.nodes t.rootId).val with rootTag := vert + 1 } ∧
        ∀ u ≤ cap, u ≠ t.rootId → (s'.nodes u).val = (sT.nodes u).val) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t? ++ rest) +
          TOUR_FIND_AMORT * (Nat.log 2 (cap + 2) + 1) + 50 := by
  have hwide := hheap.wide
  cases t? with
  | none =>
    have hcond : (Expr.reg rNode).eval w st = some 0 := by simp [Expr.eval, hrNode, optRoot]
    refine ⟨none, sT, st, _, tour_runs_cond_false hcond (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
      fun _ _ => rfl, hnodes, TreeFrame.refl hheap.zero, hinv, hvals, rfl, fun _ _ _ => rfl,
      fun _ h => absurd h (by simp), by simp [Expr.size]; omega⟩
  | some t =>
    have ht_mem : t ∈ optTrees (some t) ++ rest := by simp [optTrees]
    have ht_ne : t ≠ .leaf := hinv.nonEmpty t ht_mem
    have hrt_mem : t.rootId ∈ t.toList := AuxTree.rootId_mem ht_ne
    have ⟨hrt_pos, hrt_cap⟩ := hinv.mem_inCap ht_mem hrt_mem
    have hrt_nz : t.rootId ≠ 0 := by omega
    have hcond : (Expr.reg rNode).eval w st = some t.rootId := by simp [Expr.eval, hrNode, optRoot]
    have hAt : nb + 17 * t.rootId + 17 ≤ hOut := by
      simpa [NodeLayout.nodeAddr, tourLayout_stride] using hheap.addr_lt hrt_cap
    have hroom := hheap.room
    have hnd := hnodes t.rootId hrt_cap
    have hmem9 : st.mem (nb + 17 * t.rootId + 9) = if (sT.nodes t.rootId).val.isOpen then 1 else 0 := by
      simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.1
    have hmem10 : st.mem (nb + 17 * t.rootId + 10) = if (sT.nodes t.rootId).val.isMarked then 1 else 0 := by
      simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.2.1
    set opV := if (sT.nodes t.rootId).val.isOpen then 1 else 0
    set mkV := if (sT.nodes t.rootId).val.isMarked then 1 else 0
    set r1 := Function.update st.regs 20 (nb + 17 * t.rootId)
    set r2 := Function.update r1 21 opV
    set r3 := Function.update r2 22 mkV
    set r4 := Function.update r3 23 (vert + 1)
    have ha20 : Runs w p ω (.assign 20 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg rNode))))
        st .normal { st with regs := r1 } 6 :=
      runs_assign_iff.mpr ⟨nb + 17 * t.rootId, by
        simp [Expr.eval, hr9, hrNode, optRoot, BinOp.eval, (by omega : 17 < 2 ^ w),
          (by omega : 17 * t.rootId < 2 ^ w), (by omega : nb + 17 * t.rootId < 2 ^ w)], rfl, rfl, rfl⟩
    have ha21 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 21) (rBase := 20) (off := 9)
      (b := nb + 17 * t.rootId) (val := opV) (st := { st with regs := r1 })
      (by simp [r1]) (by omega) (by omega) hmem9
    have ha22 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 22) (rBase := 20) (off := 10)
      (b := nb + 17 * t.rootId) (val := mkV) (st := { st with regs := r2 })
      (by simp [r2, r1]) (by omega) (by omega) hmem10
    have ha23 : Runs w p ω (.assign 23 (.bin .add (.reg rVert) (.const 1)))
        { st with regs := r3 } .normal { st with regs := r4 } 4 :=
      runs_assign_iff.mpr ⟨vert + 1, by
        simp [Expr.eval, r3, r2, r1, Function.update_of_ne (by omega : rVert ≠ 22),
          Function.update_of_ne (by omega : rVert ≠ 21), Function.update_of_ne (by omega : rVert ≠ 20),
          hrVert, BinOp.eval, (by omega : 1 < 2 ^ w), hvertW], rfl, rfl, rfl⟩
    have hinv_c : TourForestInv cap sT (t :: rest) := by simpa [optTrees] using hinv
    obtain ⟨t', s', o', st', c', hrun', hn', hfr', hinv', hvals', _, _, hlist', hval_eq, hval_ne, _, hcost'⟩ :=
      tourSetValNodeBody_runs (isOpen := opV) (isMarked := mkV) (rootTag := vert + 1) (fuel := fuel) (pos := st.pos)
        C ω hnodes hinv_c hvals hrt_mem hvertW hfuel hfuelW hheap
    have hcall := runs_call_regs7 24 9 rNode 21 22 23 10 15 (st := { st with regs := r4 }) C.setValNode_body
      (by simp [r4, r3, r2, r1, hr9])
      (by simp [r4, r3, r2, r1, Function.update_of_ne (by omega : rNode ≠ 23),
        Function.update_of_ne (by omega : rNode ≠ 22), Function.update_of_ne (by omega : rNode ≠ 21),
        Function.update_of_ne (by omega : rNode ≠ 20), hrNode, optRoot])
      (by simp [r4, r3, r2]) (by simp [r4, r3]) (by simp [r4])
      (by simp [r4, r3, r2, r1, hr10]) (by simp [r4, r3, r2, r1, hr15]) hrun'
    have hval_upd : (s'.nodes t.rootId).val = { (sT.nodes t.rootId).val with rootTag := vert + 1 } := by
      rw [hval_eq]
      cases hvo : (sT.nodes t.rootId).val with
      | mk io im rt =>
        cases io <;> cases im <;> simp [opV, mkV, hvo]
    refine ⟨some t', s', { st' with regs := Function.update r4 24 o'.value }, _,
      tour_runs_cond_true hcond hrt_nz (tour_runs_seq_normal ha20 (tour_runs_seq_normal ha21
        (tour_runs_seq_normal ha22 (tour_runs_seq_normal ha23 hcall)))),
      fun k hk => by
        simp [r4, r3, r2, r1, Function.update_of_ne (by omega : k ≠ 24),
          Function.update_of_ne (by omega : k ≠ 23), Function.update_of_ne (by omega : k ≠ 22),
          Function.update_of_ne (by omega : k ≠ 21), Function.update_of_ne (by omega : k ≠ 20)],
      hn', hfr', by simpa [optTrees] using hinv', hvals', by simpa [optList] using hlist',
      fun h => absurd h (by simp),
      fun t₀ ht₀ => by cases Option.some.inj ht₀; exact ⟨hval_upd, fun u hu hne => hval_ne u hu hne⟩, ?_⟩
    clear * - hcost'
    simp only [optTrees, Option.toList_some, List.singleton_append, Expr.size] at hcost' ⊢
    omega

/-! ## `tourMoveOwnersStmt` execution theorem -/

/-- Execute `tourMoveOwnersStmt`: optionally swaps `slotOf`/`vertOf` (`c = true`), sets `endOwner`
to `sv' + 1` for every node in `A` at `pairsPtr`, walks to the front of `tKeep?` and `tMove?`, and
stores `firstEnd[v]` and `firstEnd[v']`. -/
theorem tourMoveOwners_exec {τ_ord : Type}
    {w vCap eCap b v v' pairsPtr m hOut walkFrontProc : ℕ} {c : Bool} {p : Program}
    (C : TourSplayCoreProcs w p)
    (hWalk : p.procs[walkFrontProc]? = some (tourWalkFrontBody C.walkProc C.splay.splay))
    (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ} {st0 : State}
    {sT : SplayState TourVal TourSum Unit} {tKeep? tMove? : Option AuxTree} {rest : List AuxTree}
    {A : List ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hvLt : v < vCap) (hv'Lt : v' < vCap) (hne : v ≠ v')
    (hA_len : A.length = m)
    (hA_mem : ∀ i (hi : i < A.length), st0.mem (pairsPtr + (2 * i + 1)) = A[i])
    (hA_in : ∀ u ∈ A, 1 ≤ u ∧ u ≤ x.numNodes)
    (hpre_eq : ∀ a < nodesBase b vCap eCap, st0.mem a = mem a)
    (hn0 : tourLayout.NodesAt st0.mem (nodesBase b vCap eCap) x.numNodes sT)
    (hinv0 : TourForestInv x.numNodes sT (optTrees tKeep? ++ optTrees tMove? ++ rest))
    (hvals0 : TourValsOk w x.numNodes sT)
    (hr0 : st0.regs 0 = b) (hr2 : st0.regs 2 = pairsPtr)
    (hr3 : st0.regs 3 = if c then 2 else 1) (hr4 : st0.regs 4 = v) (hr5 : st0.regs 5 = v')
    (hr9 : st0.regs 9 = nodesBase b vCap eCap) (hr10 : st0.regs 10 = 2 * eCap + 2)
    (hr12 : st0.regs 12 = x.slotOf v) (hr13 : st0.regs 13 = m) (hr15 : st0.regs 15 = hOut)
    (hr16 : st0.regs 16 = optRoot tKeep?) (hr17 : st0.regs 17 = optRoot tMove?)
    (hord_le : ordHandleOf b vCap eCap ≤ pairsPtr)
    (hpairs_le : pairsPtr + 2 * m ≤ hOut)
    (hroom : hOut + 2 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w)
    (hzero : ZeroFrom st0.mem hOut) :
    let sv := x.slotOf v
    let sv' := x.slotOf v'
    let slotOf' := if c then Function.update (Function.update x.slotOf v sv') v' sv else x.slotOf
    let vertOf' := if c then Function.update (Function.update x.vertOf sv v') sv' v else x.vertOf
    ∃ tKeep'? tMove'? s' st' cost,
      Runs w p ω (tourMoveOwnersStmt walkFrontProc) st0 .normal st' cost ∧
      (∀ k < 16, st'.regs k = st0.regs k) ∧
      st'.regs 16 = optRoot tKeep'? ∧ st'.regs 17 = optRoot tMove'? ∧
      (optList tKeep'?).head?.getD 0 = optRoot tKeep'? ∧
      (optList tMove'?).head?.getD 0 = optRoot tMove'? ∧
      tourLayout.NodesAt st'.mem (nodesBase b vCap eCap) x.numNodes s' ∧
      ZeroFrom st'.mem hOut ∧
      TourForestInv x.numNodes s' (optTrees tKeep'? ++ optTrees tMove'? ++ rest) ∧
      TourValsOk w x.numNodes s' ∧
      optList tKeep'? = optList tKeep? ∧ optList tMove'? = optList tMove? ∧
      (∀ u ≤ x.numNodes, (s'.nodes u).val = (sT.nodes u).val) ∧
      (∀ a, a < b ∨ (ordHandleOf b vCap eCap ≤ a ∧ a < hOut) → st'.mem a = st0.mem a) ∧
      TourHeaderAt vCap eCap b x.numNodes st'.mem ∧
      (∀ k < 2 * eCap, st'.mem (nodeOfEndBase b vCap + k) = x.nodeOf k) ∧
      (∀ u, 1 ≤ u → u ≤ x.numNodes → st'.mem (keyOfNodeBase b vCap eCap + u) = x.keyOf u) ∧
      (∀ w < vCap, st'.mem (isRootBase b vCap + w) = mem (isRootBase b vCap + w)) ∧
      (∀ k < 2 * eCap, st'.mem (markArrBase b vCap eCap + k) = 0) ∧
      (∀ w < vCap, st'.mem (firstEndBase b + w) =
        if w = v' then optRoot tMove'? else if w = v then optRoot tKeep'? else mem (firstEndBase b + w)) ∧
      (∀ w < vCap, decodeSlot (st'.mem (slotOfVertBase b vCap eCap + w)) w = slotOf' w) ∧
      (∀ sl < vCap, decodeSlot (st'.mem (vertOfSlotBase b vCap eCap + sl)) sl = vertOf' sl) ∧
      (∀ k < 2 * eCap, st'.mem (endOwnerBase b vCap eCap + k) =
        if ∃ u ∈ A, x.keyOf u = k then sv' + 1 else mem (endOwnerBase b vCap eCap + k)) ∧
      cost + TOUR_PHI_MULT * forestPhi (optTrees tKeep'? ++ optTrees tMove'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees tKeep? ++ optTrees tMove? ++ rest) +
          2 * TOUR_JOIN_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) + 30 * m + 160 := by
  intro sv sv' slotOf' vertOf'
  have hhdr := h.header
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hsv_lt : sv < vCap := (h.slot_bij v hvLt).1
  have hsv'_lt : sv' < vCap := (h.slot_bij v' hv'Lt).1
  have hsv_ne : sv ≠ sv' := fun heq => hne (by
    dsimp only [sv, sv'] at heq
    rw [← (h.slot_bij v hvLt).2.1, heq, (h.slot_bij v' hv'Lt).2.1])
  have hm0_hdr : ∀ k < 16, st0.mem (b + k) = mem (b + k) := fun k hk =>
    hpre_eq _ (by simp [nodesBase]; omega)
  -- Step 1: compute `sovBase`, `vosBase`, decode `sv'` into `r20`
  set r01 := Function.update st0.regs 18 (nextArrBase b vCap eCap)
  set r02 := Function.update r01 19 eCap
  set r03 := Function.update r02 20 vCap
  set r04 := Function.update r03 18 (slotOfVertBase b vCap eCap)
  set r05 := Function.update r04 19 (vertOfSlotBase b vCap eCap)
  set rawV' := mem (slotOfVertBase b vCap eCap + v')
  set r06 := Function.update r05 20 rawV'
  set r07 := Function.update r06 20 sv'
  have hsov_eq : nextArrBase b vCap eCap + 2 * eCap = slotOfVertBase b vCap eCap := by
    simp [nextArrBase, slotOfVertBase]; omega
  have hvos_eq : slotOfVertBase b vCap eCap + vCap = vertOfSlotBase b vCap eCap := by
    simp [slotOfVertBase, vertOfSlotBase]; omega
  have h1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 18) (rBase := 0) (off := HDR_NEXT_ARR)
    (b := b) (val := nextArrBase b vCap eCap) (st := st0) hr0
    (by simp [HDR_NEXT_ARR]; omega) (by simp [HDR_NEXT_ARR]; omega)
    (by rw [hm0_hdr _ (by simp [HDR_NEXT_ARR])]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.1)
  have h2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 19) (rBase := 0) (off := HDR_ECAP)
    (b := b) (val := eCap) (st := { st0 with regs := r01 }) (by simp [r01, hr0])
    (by unfold HDR_ECAP; omega) (by unfold HDR_ECAP; omega)
    (by rw [hm0_hdr _ (by simp [HDR_ECAP])]; exact hhdr.2.1)
  have h3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 20) (rBase := 0) (off := HDR_VCAP)
    (b := b) (val := vCap) (st := { st0 with regs := r02 }) (by simp [r02, r01, hr0])
    (by simp [HDR_VCAP]) (by simp [HDR_VCAP]; omega)
    (by rw [hm0_hdr _ (by simp [HDR_VCAP])]; exact hhdr.1)
  have h4 : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.bin .mul (.const 2) (.reg 19))))
      { st0 with regs := r03 } .normal { st0 with regs := r04 } 6 :=
    runs_assign_iff.mpr ⟨slotOfVertBase b vCap eCap, by
      simp [Expr.eval, r03, r02, r01, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 2 * eCap < 2 ^ w),
        hsov_eq, (by simp [slotOfVertBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : slotOfVertBase b vCap eCap < 2 ^ w)],
      rfl, rfl, rfl⟩
  have h5 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 20)))
      { st0 with regs := r04 } .normal { st0 with regs := r05 } 4 :=
    runs_assign_iff.mpr ⟨vertOfSlotBase b vCap eCap, by
      simp [Expr.eval, r04, r03, BinOp.eval, hvos_eq,
        (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : vertOfSlotBase b vCap eCap < 2 ^ w)],
      rfl, rfl, rfl⟩
  have hraw_eq : st0.mem (slotOfVertBase b vCap eCap + v') = rawV' :=
    hpre_eq _ (by simp [slotOfVertBase, nodesBase]; omega)
  have h6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 20) (rBase := 18) (rIdx := 5)
    (base := slotOfVertBase b vCap eCap) (idx := v') (val := rawV') (st := { st0 with regs := r05 })
    (by simp [r05, r04]) (by simp [r05, r04, r03, r02, r01, hr5])
    (by simp [slotOfVertBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hraw_eq
  have h7 : ∃ c7, c7 ≤ 6 ∧ Runs w p ω (.cond (.reg 20) (.assign 20 (.bin .sub (.reg 20) (.const 1))) (.assign 20 (.reg 5)))
      { st0 with regs := r06 } .normal { st0 with regs := r07 } c7 := by
    have hdec := h.slotOf_mem v' hv'Lt
    by_cases hraw0 : rawV' = 0
    · have hsv'v' : sv' = v' := by simpa [decodeSlot, rawV', hraw0] using hdec.symm
      have hc : (Expr.reg 20).eval w { st0 with regs := r06 } = some 0 := by simp [Expr.eval, r06, hraw0]
      have ha : Runs w p ω (.assign 20 (.reg 5)) { st0 with regs := r06 } .normal { st0 with regs := r07 } 2 :=
        runs_assign_iff.mpr ⟨v', by simp [Expr.eval, r06, r05, r04, r03, r02, r01, hr5], rfl,
          by congr 1; funext k; by_cases hk : k = 20 <;> simp [r07, r06, hk, hsv'v'], rfl⟩
      exact ⟨_, by simp [Expr.size], tour_runs_cond_false hc ha⟩
    · have hsv'sub : rawV' - 1 = sv' := by simpa [decodeSlot, rawV', hraw0] using hdec
      have hc : (Expr.reg 20).eval w { st0 with regs := r06 } = some rawV' := by simp [Expr.eval, r06]
      have ha : Runs w p ω (.assign 20 (.bin .sub (.reg 20) (.const 1))) { st0 with regs := r06 } .normal { st0 with regs := r07 } 4 :=
        runs_assign_iff.mpr ⟨sv', by
          simp [Expr.eval, r06, BinOp.eval, (by omega : 1 < 2 ^ w), hsv'sub, (by omega : sv' < 2 ^ w)], rfl, rfl, rfl⟩
      exact ⟨_, by simp [Expr.size], tour_runs_cond_true hc hraw0 ha⟩
  obtain ⟨c7, hc7, hrun7⟩ := h7
  -- Step 2: optional slot swap when `c = true` (`tag == 2`)
  have hswap : ∃ mem1 cSw, cSw ≤ 35 ∧
      Runs w p ω (.cond (.bin .eq (.reg 3) (.const 2))
        (.store (.bin .add (.reg 18) (.reg 4)) (.bin .add (.reg 20) (.const 1)) ;;
         .store (.bin .add (.reg 18) (.reg 5)) (.bin .add (.reg 12) (.const 1)) ;;
         .store (.bin .add (.reg 19) (.reg 12)) (.bin .add (.reg 5) (.const 1)) ;;
         .store (.bin .add (.reg 19) (.reg 20)) (.bin .add (.reg 4) (.const 1)))
        .nop) { st0 with regs := r07 } .normal { st0 with mem := mem1, regs := r07 } cSw ∧
      (∀ a, (a < slotOfVertBase b vCap eCap ∨ nodesBase b vCap eCap ≤ a) → mem1 a = st0.mem a) ∧
      (∀ w < vCap, decodeSlot (mem1 (slotOfVertBase b vCap eCap + w)) w = slotOf' w) ∧
      (∀ sl < vCap, decodeSlot (mem1 (vertOfSlotBase b vCap eCap + sl)) sl = vertOf' sl) := by
    cases c with
    | false =>
      have hc : (Expr.bin .eq (.reg 3) (.const 2)).eval w { st0 with regs := r07 } = some 0 := by
        simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr3, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 0 < 2 ^ w)]
      refine ⟨st0.mem, _, by simp [Expr.size], tour_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        fun _ _ => rfl,
        fun w hw => by rw [hpre_eq _ (by simp [slotOfVertBase, nodesBase]; omega)]; exact h.slotOf_mem w hw,
        fun sl hsl => by rw [hpre_eq _ (by simp [vertOfSlotBase, nodesBase]; omega)]; exact h.vertOf_mem sl hsl⟩
    | true =>
      have hc : (Expr.bin .eq (.reg 3) (.const 2)).eval w { st0 with regs := r07 } = some 1 := by
        simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr3, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      set m1 := Function.update st0.mem (slotOfVertBase b vCap eCap + v) (sv' + 1)
      set m2 := Function.update m1 (slotOfVertBase b vCap eCap + v') (sv + 1)
      set m3 := Function.update m2 (vertOfSlotBase b vCap eCap + sv) (v' + 1)
      set m4 := Function.update m3 (vertOfSlotBase b vCap eCap + sv') (v + 1)
      have hs1 : Runs w p ω (.store (.bin .add (.reg 18) (.reg 4)) (.bin .add (.reg 20) (.const 1)))
          { st0 with regs := r07 } .normal { st0 with mem := m1, regs := r07 } 7 :=
        runs_store_iff.mpr ⟨slotOfVertBase b vCap eCap + v, sv' + 1,
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr4, BinOp.eval,
            (by simp [slotOfVertBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : slotOfVertBase b vCap eCap + v < 2 ^ w)],
          by simp [Expr.eval, r07, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : sv' + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg 18) (.reg 5)) (.bin .add (.reg 12) (.const 1)))
          { st0 with mem := m1, regs := r07 } .normal { st0 with mem := m2, regs := r07 } 7 :=
        runs_store_iff.mpr ⟨slotOfVertBase b vCap eCap + v', sv + 1,
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr5, BinOp.eval,
            (by simp [slotOfVertBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : slotOfVertBase b vCap eCap + v' < 2 ^ w)],
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr12, sv, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : sv + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hs3 : Runs w p ω (.store (.bin .add (.reg 19) (.reg 12)) (.bin .add (.reg 5) (.const 1)))
          { st0 with mem := m2, regs := r07 } .normal { st0 with mem := m3, regs := r07 } 7 :=
        runs_store_iff.mpr ⟨vertOfSlotBase b vCap eCap + sv, v' + 1,
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr12, sv, BinOp.eval,
            (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : vertOfSlotBase b vCap eCap + sv < 2 ^ w)],
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v' + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hs4 : Runs w p ω (.store (.bin .add (.reg 19) (.reg 20)) (.bin .add (.reg 4) (.const 1)))
          { st0 with mem := m3, regs := r07 } .normal { st0 with mem := m4, regs := r07 } 7 :=
        runs_store_iff.mpr ⟨vertOfSlotBase b vCap eCap + sv', v + 1,
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, BinOp.eval,
            (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : vertOfSlotBase b vCap eCap + sv' < 2 ^ w)],
          by simp [Expr.eval, r07, r06, r05, r04, r03, r02, r01, hr4, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      refine ⟨m4, _, by simp [Expr.size],
        tour_runs_cond_true hc (by omega) (tour_runs_seq_normal hs1 (tour_runs_seq_normal hs2 (tour_runs_seq_normal hs3 hs4))),
        fun a ha => by
          dsimp only [m4, m3, m2, m1]
          rw [Function.update_of_ne (by simp [slotOfVertBase, vertOfSlotBase, nodesBase] at ha ⊢; rcases ha with h1 | h2 <;> omega),
            Function.update_of_ne (by simp [slotOfVertBase, vertOfSlotBase, nodesBase] at ha ⊢; rcases ha with h1 | h2 <;> omega),
            Function.update_of_ne (by simp [slotOfVertBase, nodesBase] at ha ⊢; rcases ha with h1 | h2 <;> omega),
            Function.update_of_ne (by simp [slotOfVertBase, nodesBase] at ha ⊢; rcases ha with h1 | h2 <;> omega)],
        fun w hw => by
          dsimp only [m4, m3, m2, m1, slotOf']
          rw [Function.update_of_ne (by simp [slotOfVertBase, vertOfSlotBase]; omega),
            Function.update_of_ne (by simp [slotOfVertBase, vertOfSlotBase]; omega)]
          by_cases hwv' : w = v'
          · subst hwv'; simp [decodeSlot]
          · by_cases hwv : w = v
            · subst hwv; rw [Function.update_of_ne (by omega)]; simp [decodeSlot, hwv']
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                hpre_eq _ (by simp [slotOfVertBase, nodesBase]; omega)]
              simp [hwv', hwv, h.slotOf_mem w hw],
        fun sl hsl => by
          dsimp only [m4, m3, m2, m1, vertOf']
          by_cases hsl' : sl = sv'
          · subst hsl'; simp [decodeSlot]
          · by_cases hslv : sl = sv
            · subst hslv; rw [Function.update_of_ne (by omega)]; simp [decodeSlot, hsl']
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by simp [slotOfVertBase, vertOfSlotBase]; omega),
                Function.update_of_ne (by simp [slotOfVertBase, vertOfSlotBase]; omega),
                hpre_eq _ (by simp [vertOfSlotBase, nodesBase]; omega)]
              simp [hsl', hslv, h.vertOf_mem sl hsl]⟩
  obtain ⟨mem1, cSw, hcSw, hrunSw, hmem1_out, hmem1_sov, hmem1_vos⟩ := hswap
  -- Step 3: loop updating `endOwner[keyOf[A[i]]] := sv' + 1`
  set r08 := Function.update r07 18 (endOwnerBase b vCap eCap)
  set r09 := Function.update r08 19 (keyOfNodeBase b vCap eCap)
  set r10 := Function.update r09 20 (sv' + 1)
  set r11 := Function.update r10 21 0
  have h8 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 18) (rBase := 0) (off := HDR_END_OWNER)
    (b := b) (val := endOwnerBase b vCap eCap) (st := { st0 with mem := mem1, regs := r07 })
    (by simp [r07, r06, r05, r04, r03, r02, r01, hr0])
    (by simp [HDR_END_OWNER]; omega) (by simp [HDR_END_OWNER]; omega)
    (by dsimp only; rw [hmem1_out _ (Or.inl (by simp [HDR_END_OWNER, slotOfVertBase]; omega)),
          hm0_hdr _ (by simp [HDR_END_OWNER])]; exact hhdr.2.2.2.2.2.2.2.1)
  have h9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 19) (rBase := 0) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := { st0 with mem := mem1, regs := r08 })
    (by simp [r08, r07, r06, r05, r04, r03, r02, r01, hr0])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega)
    (by dsimp only; rw [hmem1_out _ (Or.inl (by simp [HDR_KEY_OF_NODE, slotOfVertBase]; omega)),
          hm0_hdr _ (by simp [HDR_KEY_OF_NODE])]; exact hhdr.2.2.2.2.2.2.2.2.1)
  have h10 : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1)))
      { st0 with mem := mem1, regs := r09 } .normal { st0 with mem := mem1, regs := r10 } 4 :=
    runs_assign_iff.mpr ⟨sv' + 1, by simp [Expr.eval, r09, r08, r07, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : sv' + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have h11 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 21) (val := 0)
    (st := { st0 with mem := mem1, regs := r10 }) (by omega)
  have hloop : ∀ (rem i : ℕ) (stC : State), i + rem = m →
      (∀ k < 18, stC.regs k = st0.regs k) →
      stC.regs 18 = endOwnerBase b vCap eCap → stC.regs 19 = keyOfNodeBase b vCap eCap →
      stC.regs 20 = sv' + 1 → stC.regs 21 = i →
      (∀ a, (a < endOwnerBase b vCap eCap ∨ endOwnerBase b vCap eCap + 2 * eCap ≤ a) → stC.mem a = mem1 a) →
      (∀ k < 2 * eCap, stC.mem (endOwnerBase b vCap eCap + k) =
        if ∃ u ∈ A.take i, x.keyOf u = k then sv' + 1 else mem (endOwnerBase b vCap eCap + k)) →
      ∃ stL cL,
        Runs w p ω (.loop (.bin .lt (.reg 21) (.reg 13))
          (.assign 22 (.load (.bin .add (.reg 2) (.bin .add (.bin .add (.reg 21) (.reg 21)) (.const 1)))) ;;
           .assign 22 (.load (.bin .add (.reg 19) (.reg 22))) ;;
           .store (.bin .add (.reg 18) (.reg 22)) (.reg 20) ;;
           .assign 21 (.bin .add (.reg 21) (.const 1)))) stC .normal stL cL ∧
        (∀ k < 18, stL.regs k = st0.regs k) ∧
        (∀ a, (a < endOwnerBase b vCap eCap ∨ endOwnerBase b vCap eCap + 2 * eCap ≤ a) → stL.mem a = mem1 a) ∧
        (∀ k < 2 * eCap, stL.mem (endOwnerBase b vCap eCap + k) =
          if ∃ u ∈ A, x.keyOf u = k then sv' + 1 else mem (endOwnerBase b vCap eCap + k)) ∧
        cL ≤ 30 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i stC hrem hk h18 h19 h20 h21 hfr heo
      have him : i = m := by omega
      have hcond : (Expr.bin .lt (.reg 21) (.reg 13)).eval w stC = some 0 := by
        simp [Expr.eval, h21, hk 13 (by omega), hr13, him, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hk, hfr,
        fun k hkl => by simpa [him, ← hA_len] using heo k hkl, by simp [Expr.size]⟩
    | succ rem ih =>
      intro i stC hrem hk h18 h19 h20 h21 hfr heo
      have hi_lt : i < m := by omega
      set u := A[i]'(by omega)
      have hu_in := hA_in u (List.getElem_mem _)
      set ku := x.keyOf u
      have hku_lt : ku < 2 * eCap := (h.keyOf_mem u hu_in.1 hu_in.2).2.1
      have hcond : (Expr.bin .lt (.reg 21) (.reg 13)).eval w stC = some 1 := by
        simp [Expr.eval, h21, hk 13 (by omega), hr13, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hmC_u : stC.mem (pairsPtr + (i + i + 1)) = u := by
        have h2i : i + i = 2 * i := by omega
        rw [h2i, hfr _ (Or.inr (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)),
          hmem1_out _ (Or.inr (by simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))]
        exact hA_mem i (by omega)
      have hmC_ku : stC.mem (keyOfNodeBase b vCap eCap + u) = ku := by
        have hnn := h.numNodes_le
        rw [hfr _ (Or.inr (by simp [endOwnerBase, keyOfNodeBase]; omega)),
          hmem1_out _ (Or.inl (by simp [keyOfNodeBase, slotOfVertBase]; omega)),
          hpre_eq _ (by simp [keyOfNodeBase, nodesBase]; omega)]
        exact (h.keyOf_mem u hu_in.1 hu_in.2).1
      set ra := Function.update stC.regs 22 u
      set rb := Function.update ra 22 ku
      set memC := Function.update stC.mem (endOwnerBase b vCap eCap + ku) (sv' + 1)
      set rc := Function.update rb 21 (i + 1)
      have ha_u : Runs w p ω (.assign 22 (.load (.bin .add (.reg 2) (.bin .add (.bin .add (.reg 21) (.reg 21)) (.const 1)))))
          stC .normal { stC with regs := ra } 9 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, hk 2 (by omega), hr2, h21, BinOp.eval, (by omega : 1 < 2 ^ w),
            (by omega : i + i < 2 ^ w), (by omega : i + i + 1 < 2 ^ w),
            (by omega : pairsPtr + (i + i + 1) < 2 ^ w), hmC_u], rfl, rfl, rfl⟩
      have ha_ku := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 22) (rBase := 19) (rIdx := 22)
        (base := keyOfNodeBase b vCap eCap) (idx := u) (val := ku) (st := { stC with regs := ra })
        (by simp [ra, h19]) (by simp [ra])
        (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmC_ku
      have hst_eo : Runs w p ω (.store (.bin .add (.reg 18) (.reg 22)) (.reg 20))
          { stC with regs := rb } .normal { stC with mem := memC, regs := rb } 5 :=
        runs_store_iff.mpr ⟨endOwnerBase b vCap eCap + ku, sv' + 1,
          by simp [Expr.eval, rb, ra, h18, BinOp.eval,
            (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : endOwnerBase b vCap eCap + ku < 2 ^ w)],
          by simp [Expr.eval, rb, ra, h20], rfl, rfl, rfl⟩
      have ha_i : Runs w p ω (.assign 21 (.bin .add (.reg 21) (.const 1)))
          { stC with mem := memC, regs := rb } .normal { stC with mem := memC, regs := rc } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, rb, ra, h21, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have htake_s : A.take (i + 1) = A.take i ++ [u] := List.take_succ_eq_append_getElem (by omega)
      obtain ⟨stL, cL, hrunL, hkL, hfrL, heoL, hcL⟩ :=
        ih (i + 1) { stC with mem := memC, regs := rc } (by omega)
          (fun k hkl => by simp [rc, rb, ra, Function.update_of_ne (by omega : k ≠ 21),
            Function.update_of_ne (by omega : k ≠ 22), hk k hkl])
          (by simp [rc, rb, ra, h18]) (by simp [rc, rb, ra, h19]) (by simp [rc, rb, ra, h20]) (by simp [rc])
          (fun a ha => by dsimp only [memC]; rw [Function.update_of_ne (by rcases ha with h1 | h2 <;> omega)]; exact hfr a ha)
          (fun k hkl => by
            dsimp only [memC]
            by_cases hkk : k = ku
            · subst hkk; simp [htake_s, ku]
            · rw [Function.update_of_ne (by omega), heo k hkl]
              have hiff : (∃ u' ∈ A.take (i + 1), x.keyOf u' = k) ↔ (∃ u' ∈ A.take i, x.keyOf u' = k) := by
                simp only [htake_s, List.mem_append, List.mem_singleton]
                exact ⟨fun ⟨u', hu', hk'⟩ => hu'.elim (fun h1 => ⟨u', h1, hk'⟩) (fun heq => absurd (heq ▸ hk').symm hkk),
                  fun ⟨u', hu', hk'⟩ => ⟨u', Or.inl hu', hk'⟩⟩
              simp [hiff])
      refine ⟨stL, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
        tour_runs_seq_normal ha_u (tour_runs_seq_normal ha_ku (tour_runs_seq_normal hst_eo ha_i)), hrunL, rfl⟩)),
        hkL, hfrL, heoL, by clear * - hcL; simp only [Expr.size]; omega⟩
  obtain ⟨stL, cL, hrunL, hkL, hfrL, heoL, hcL⟩ :=
    hloop m 0 { st0 with mem := mem1, regs := r11 } (by omega)
      (fun k hkl => by simp [r11, r10, r09, r08, r07, r06, r05, r04, r03, r02, r01,
        Function.update_of_ne (by omega : k ≠ 21), Function.update_of_ne (by omega : k ≠ 20),
        Function.update_of_ne (by omega : k ≠ 19), Function.update_of_ne (by omega : k ≠ 18)])
      (by simp [r11, r10, r09, r08]) (by simp [r11, r10, r09]) (by simp [r11, r10]) (by simp [r11])
      (fun _ _ => rfl)
      (fun k hkl => by
        simp only [List.take_zero, List.not_mem_nil, false_and, exists_false, ↓reduceIte]
        rw [hmem1_out _ (Or.inl (by simp [endOwnerBase, slotOfVertBase]; omega)),
          hpre_eq _ (by simp [endOwnerBase, nodesBase]; omega)])
  -- Step 4: `walkFront` on `tKeep?` (`r16`) and `tMove?` (`r17`), then store `firstEnd[v]` and `firstEnd[v']`
  have hstL_ge_nb : ∀ a, nodesBase b vCap eCap ≤ a → stL.mem a = st0.mem a := fun a ha => by
    rw [hfrL a (Or.inr (by simp [endOwnerBase, nodesBase] at ha ⊢; omega)),
      hmem1_out a (Or.inr ha)]
  have hnL : tourLayout.NodesAt stL.mem (nodesBase b vCap eCap) x.numNodes sT :=
    NodesAt.congr tourLayout hn0 fun a ha => hstL_ge_nb a (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1
  have hheapL : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes hOut 2 stL.mem :=
    ⟨by have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega,
     by omega, fun a ha => by rw [hstL_ge_nb a (by simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hzero a ha,
     by omega⟩
  have hinvL_K : TourForestInv x.numNodes sT (optTrees tKeep? ++ (optTrees tMove? ++ rest)) := by
    simpa [List.append_assoc] using hinv0
  obtain ⟨tKeep'?, s1, o1, st1, c1, hrun1, hv1, hhd1, hn1, hfr1, hinv1, hvals1, hlist1, hval1, _, hc1⟩ :=
    tourWalkFrontBody_runs (fuel := 2 * eCap + 2) (pos := stL.pos) C ω hnL hinvL_K hvals0 (by have := h.numNodes_le; omega) (by omega) hheapL
  have hcall1 := runs_call_regs4 16 9 16 10 15 (st := stL) hWalk
    (by rw [hkL 9 (by omega), hr9]) (by rw [hkL 16 (by omega), hr16])
    (by rw [hkL 10 (by omega), hr10]) (by rw [hkL 15 (by omega), hr15]) hrun1
  set rW1 := Function.update stL.regs 16 o1.value
  have hperm1 : (optTrees tKeep'? ++ (optTrees tMove? ++ rest)).Perm
      (optTrees tMove? ++ (optTrees tKeep'? ++ rest)) := by
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tKeep'?) (l₂ := optTrees tMove?)).append_right rest
  obtain ⟨tMove'?, s2, o2, st2, c2, hrun2, hv2, hhd2, hn2, hfr2, hinv2, hvals2, hlist2, hval2, _, hc2⟩ :=
    tourWalkFrontBody_runs (fuel := 2 * eCap + 2) (pos := st1.pos) C ω hn1 (hinv1.perm hperm1).1 hvals1 (by have := h.numNodes_le; omega) (by omega)
      ⟨hheapL.rec_le, hheapL.room, hfr1.1, hheapL.wide⟩
  have hcall2 := runs_call_regs4 17 9 17 10 15 (st := { st1 with regs := rW1 }) hWalk
    (by simp [rW1, hkL 9 (by omega), hr9]) (by simp [rW1, hkL 17 (by omega), hr17])
    (by simp [rW1, hkL 10 (by omega), hr10]) (by simp [rW1, hkL 15 (by omega), hr15]) hrun2
  set rW2 := Function.update rW1 17 o2.value
  set rW3 := Function.update rW2 18 (firstEndBase b)
  have hfr12 := hfr1.trans hfr2
  have hst2_lt_nb : ∀ a < nodesBase b vCap eCap, st2.mem a = stL.mem a := fun a ha =>
    hfr12.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega) (not_inRecords_of_lt_nodesBase ha)
  have hfeBase_mem : st2.mem (b + HDR_FIRST_END) = firstEndBase b := by
    rw [hst2_lt_nb _ (by simp [HDR_FIRST_END, nodesBase]; omega),
      hfrL _ (Or.inl (by simp [HDR_FIRST_END, endOwnerBase]; omega)),
      hmem1_out _ (Or.inl (by simp [HDR_FIRST_END, slotOfVertBase]; omega)),
      hm0_hdr _ (by simp [HDR_FIRST_END])]
    exact hhdr.2.2.2.2.1
  have ha18 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 18) (rBase := 0) (off := HDR_FIRST_END)
    (b := b) (val := firstEndBase b) (st := { st2 with regs := rW2 })
    (by simp [rW2, rW1, hkL 0 (by omega), hr0])
    (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega) hfeBase_mem
  set memF1 := Function.update st2.mem (firstEndBase b + v) (optRoot tKeep'?)
  set memF2 := Function.update memF1 (firstEndBase b + v') (optRoot tMove'?)
  have hst_fev : Runs w p ω (.store (.bin .add (.reg 18) (.reg 4)) (.reg 16))
      { st2 with regs := rW3 } .normal { st2 with mem := memF1, regs := rW3 } 5 :=
    runs_store_iff.mpr ⟨firstEndBase b + v, optRoot tKeep'?,
      by simp [Expr.eval, rW3, rW2, rW1, hkL 4 (by omega), hr4, BinOp.eval,
        (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : firstEndBase b + v < 2 ^ w)],
      by simp [Expr.eval, rW3, rW2, rW1, hv1], rfl, rfl, rfl⟩
  have hst_fev' : Runs w p ω (.store (.bin .add (.reg 18) (.reg 5)) (.reg 17))
      { st2 with mem := memF1, regs := rW3 } .normal { st2 with mem := memF2, regs := rW3 } 5 :=
    runs_store_iff.mpr ⟨firstEndBase b + v', optRoot tMove'?,
      by simp [Expr.eval, rW3, rW2, rW1, hkL 5 (by omega), hr5, BinOp.eval,
        (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : firstEndBase b + v' < 2 ^ w)],
      by simp [Expr.eval, rW3, rW2, hv2], rfl, rfl, rfl⟩
  have hperm2 : (optTrees tMove'? ++ (optTrees tKeep'? ++ rest)).Perm
      (optTrees tKeep'? ++ optTrees tMove'? ++ rest) := by
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tMove'?) (l₂ := optTrees tKeep'?)).append_right rest
  have hmemF2_ne_fe : ∀ a, a ≠ firstEndBase b + v → a ≠ firstEndBase b + v' → memF2 a = st2.mem a :=
    fun a h1 h2 => by dsimp only [memF2, memF1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have hmemF2_hdr : ∀ k < 16, memF2 (b + k) = mem (b + k) := fun k hk => by
    rw [hmemF2_ne_fe _ (by simp [firstEndBase]; omega) (by simp [firstEndBase]; omega),
      hst2_lt_nb _ (by simp [nodesBase]; omega),
      hfrL _ (Or.inl (by simp [endOwnerBase]; omega)),
      hmem1_out _ (Or.inl (by simp [slotOfVertBase]; omega)), hm0_hdr k hk]
  have hhdrF : TourHeaderAt vCap eCap b x.numNodes memF2 := by
    rcases hhdr with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    exact ⟨by rw [hmemF2_hdr _ (by decide)]; exact h0, by rw [hmemF2_hdr _ (by decide)]; exact h1,
      by rw [hmemF2_hdr _ (by decide)]; exact h2, by rw [hmemF2_hdr _ (by decide)]; exact h3,
      by rw [hmemF2_hdr _ (by decide)]; exact h4, by rw [hmemF2_hdr _ (by decide)]; exact h5,
      by rw [hmemF2_hdr _ (by decide)]; exact h6, by rw [hmemF2_hdr _ (by decide)]; exact h7,
      by rw [hmemF2_hdr _ (by decide)]; exact h8, by rw [hmemF2_hdr _ (by decide)]; exact h9,
      by rw [hmemF2_hdr _ (by decide)]; exact h10, by rw [hmemF2_hdr _ (by decide)]; exact h11,
      by rw [hmemF2_hdr _ (by decide)]; exact h12, by rw [hmemF2_hdr _ (by decide)]; exact h13,
      by rw [hmemF2_hdr _ (by decide)]; exact h14⟩
  refine ⟨tKeep'?, tMove'?, s2, { st2 with mem := memF2, regs := rW3 }, _,
    tour_runs_seq_normal h1 (tour_runs_seq_normal h2 (tour_runs_seq_normal h3 (tour_runs_seq_normal h4
      (tour_runs_seq_normal h5 (tour_runs_seq_normal h6 (tour_runs_seq_normal hrun7 (tour_runs_seq_normal hrunSw
        (tour_runs_seq_normal h8 (tour_runs_seq_normal h9 (tour_runs_seq_normal h10 (tour_runs_seq_normal h11
          (tour_runs_seq_normal hrunL (tour_runs_seq_normal hcall1 (tour_runs_seq_normal hcall2
            (tour_runs_seq_normal ha18 (tour_runs_seq_normal hst_fev hst_fev')))))))))))))))),
    fun k hk => by simp [rW3, rW2, rW1, Function.update_of_ne (by omega : k ≠ 18),
      Function.update_of_ne (by omega : k ≠ 17), Function.update_of_ne (by omega : k ≠ 16), hkL k (by omega)],
    by simp [rW3, rW2, rW1, hv1], by simp [rW3, rW2, hv2],
    by rw [hlist1, hhd1, hv1], by rw [hlist2, hhd2, hv2],
    NodesAt.congr tourLayout hn2 (fun a ha => hmemF2_ne_fe a
      (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [firstEndBase, nodesBase] at this ⊢; omega)
      (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [firstEndBase, nodesBase] at this ⊢; omega)),
    fun a ha => by
      dsimp only
      rw [hmemF2_ne_fe a (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
        (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
      exact hfr12.1 a ha,
    (hinv2.perm hperm2).1, hvals2, hlist1, hlist2,
    fun u hu => (hval2 u hu).trans (hval1 u hu),
    fun a ha => by
      dsimp only
      have hne1 : a ≠ firstEndBase b + v := by
        simp [firstEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega
      have hne2 : a ≠ firstEndBase b + v' := by
        simp [firstEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega
      rw [hmemF2_ne_fe a hne1 hne2]
      have ha_lt : a < hOut := by
        rcases ha with h1 | ⟨_, h2⟩
        · simp [ordHandleOf, tourFixedSize] at hord_le; omega
        · exact h2
      have ha_nr : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hrec => by
        have := inRecords_lt_ordHandle_of_le h.numNodes_le hrec; simp [nodesBase] at this
        rcases ha with h1 | ⟨h2, _⟩ <;> omega
      rw [hfr12.2 a ha_lt ha_nr,
        hfrL a (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩; exact Or.inl (by omega); exact Or.inr (by omega)),
        hmem1_out a (by simp [slotOfVertBase, nodesBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩; exact Or.inl (by omega); exact Or.inr (by omega))],
    hhdrF,
    fun k hk => by
      dsimp only
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, nodeOfEndBase]; omega) (by simp [firstEndBase, nodeOfEndBase]; omega),
        hst2_lt_nb _ (by simp [nodeOfEndBase, nodesBase]; omega),
        hfrL _ (Or.inl (by simp [nodeOfEndBase, endOwnerBase]; omega)),
        hmem1_out _ (Or.inl (by simp [nodeOfEndBase, slotOfVertBase]; omega)),
        hpre_eq _ (by simp [nodeOfEndBase, nodesBase]; omega)]
      exact (h.nodeOf_mem k hk).1,
    fun u h1 h2 => by
      dsimp only
      have hnn := h.numNodes_le
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, keyOfNodeBase]; omega) (by simp [firstEndBase, keyOfNodeBase]; omega),
        hst2_lt_nb _ (by simp [keyOfNodeBase, nodesBase]; omega),
        hfrL _ (Or.inr (by simp [keyOfNodeBase, endOwnerBase]; omega)),
        hmem1_out _ (Or.inl (by simp [keyOfNodeBase, slotOfVertBase]; omega)),
        hpre_eq _ (by simp [keyOfNodeBase, nodesBase]; omega)]
      exact (h.keyOf_mem u h1 h2).1,
    fun w hw => by
      dsimp only
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, isRootBase]; omega) (by simp [firstEndBase, isRootBase]; omega),
        hst2_lt_nb _ (by simp [isRootBase, nodesBase]; omega),
        hfrL _ (Or.inl (by simp [isRootBase, endOwnerBase]; omega)),
        hmem1_out _ (Or.inl (by simp [isRootBase, slotOfVertBase]; omega)),
        hpre_eq _ (by simp [isRootBase, nodesBase]; omega)],
    fun k hk => by
      dsimp only
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, markArrBase]; omega) (by simp [firstEndBase, markArrBase]; omega),
        hst2_lt_nb _ (by simp [markArrBase, nodesBase]; omega),
        hfrL _ (Or.inr (by simp [markArrBase, endOwnerBase]; omega)),
        hmem1_out _ (Or.inl (by simp [markArrBase, slotOfVertBase]; omega)),
        hpre_eq _ (by simp [markArrBase, nodesBase]; omega)]
      exact h.markArr_zero k hk,
    fun w hw => by
      dsimp only [memF2, memF1]
      by_cases hwv' : w = v'
      · subst hwv'; simp
      · by_cases hwv : w = v
        · subst hwv; rw [Function.update_of_ne (by omega)]; simp [hwv']
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            hst2_lt_nb _ (by simp [firstEndBase, nodesBase]; omega),
            hfrL _ (Or.inl (by simp [firstEndBase, endOwnerBase]; omega)),
            hmem1_out _ (Or.inl (by simp [firstEndBase, slotOfVertBase]; omega)),
            hpre_eq _ (by simp [firstEndBase, nodesBase]; omega)]
          simp [hwv', hwv],
    fun w hw => by
      dsimp only
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, slotOfVertBase]; omega) (by simp [firstEndBase, slotOfVertBase]; omega),
        hst2_lt_nb _ (by simp [slotOfVertBase, nodesBase]; omega),
        hfrL _ (Or.inr (by simp [slotOfVertBase, endOwnerBase]; omega))]
      exact hmem1_sov w hw,
    fun sl hsl => by
      dsimp only
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, vertOfSlotBase]; omega) (by simp [firstEndBase, vertOfSlotBase]; omega),
        hst2_lt_nb _ (by simp [vertOfSlotBase, nodesBase]; omega),
        hfrL _ (Or.inr (by simp [vertOfSlotBase, endOwnerBase]; omega))]
      exact hmem1_vos sl hsl,
    fun k hk => by
      dsimp only
      rw [hmemF2_ne_fe _ (by simp [firstEndBase, endOwnerBase]; omega) (by simp [firstEndBase, endOwnerBase]; omega),
        hst2_lt_nb _ (by simp [endOwnerBase, nodesBase]; omega)]
      exact heoL k hk,
    ?_⟩
  have hpeq0 : forestPhi (optTrees tKeep? ++ (optTrees tMove? ++ rest)) =
      forestPhi (optTrees tKeep? ++ optTrees tMove? ++ rest) := by simp [List.append_assoc]
  have hpeq1 := forestPhi_perm hperm1
  have hpeq2 := forestPhi_perm hperm2
  have h2J : 2 * TOUR_JOIN_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) =
      TOUR_JOIN_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) + TOUR_JOIN_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) := by ring
  rw [← hpeq2]; rw [← hpeq1] at hc2; rw [hpeq0] at hc1
  clear * - hc7 hcSw hcL hc1 hc2 h2J; omega


end MinCostFlow.SparseCore.Program
