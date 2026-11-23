module

public import MinCostFlow.SparseCore.Program.TourOpsEditCommon
public import MinCostFlow.SparseCore.Program.OrdStoreLayout
import Mathlib.Tactic

/-!
# Stage 1 of Tour Initialization (`tourInitStage1Body`)

Builds an initial `TourRepAt` state for the edgeless forest `s₀ = ⟨ord, ⟨V, ∅, tail, head⟩, V, ∅⟩`
where every vertex in `V` is its own singleton component root:
1. Writes the 15-word tour header at `b := heap` and initializes splay node `0` (`[17, 6, 1]`).
2. Calls `ordInitProc [vCap, eCap, ordPtr, ordHandleOf b vCap eCap]` to initialize the embedded
   order store, returning `hOut`.
3. Scans `ordPtr` (`readOrdRecordsAt`), allocating splay nodes `1 .. numNodes`, filling
   `nodeOfEnd`, `keyOfNode`, `endOwner`, `firstEnd`, `isRoot`, and joining each vertex's ends into
   a splay tree via `tourInitNodeBody` + `tourJoinBody`.
4. Scans `rsPtr` (`readNatList`) to mark all listed roots (including isolated roots) in `isRoot`,
   writes `HDR_NUM_NODES`, and returns `hOut`.

Total cost (including the resulting splay-forest potential `TOUR_PHI_MULT * forestPhi x₀.trees`
and embedded order-store potential) is `O((1 + ordWords + |rs|) * tourLog eCap)` with heap space
`tourFixedSize vCap eCap + ordSpace + 2` (independent of `heap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Pure model helpers for Stage 1 -/

/-- Default node-0 record matching `[17, 6, 1]` at offsets `6..8` and zeros elsewhere. -/
def tourZeroNode : SplayNode TourVal TourSum Unit :=
  { left := 0, right := 0, par := 0, ppar := 0, sz := 0,
    val := ⟨false, false, 0⟩, sum := ⟨0, 0, 0, 0⟩, tag := (), rev := false }

/-- Initial splay state containing only node `0`. -/
def tourEmptyState : SplayState TourVal TourSum Unit :=
  ⟨fun _ => tourZeroNode⟩

/-- Edgeless initial `TourAbs` produced by Stage 1 before forest edges are linked. -/
noncomputable def tourInitStage1Abs (recs : List (ℕ × List End)) (rs : List ℕ) : TourAbs :=
  let ord := ordOfRecords recs
  let V := ((recs.filter fun p => !p.2.isEmpty).map Prod.fst).toFinset ∪ rs.toFinset
  { ord := ord
    rf :=
      { F :=
          { V := V
            E := ∅
            tail := fun e => ordSrc ord (e, true)
            head := fun e => ordSrc ord (e, false) }
        R := V }
    marked := ∅ }

theorem tourValid_stage1 {vCap eCap : ℕ} {recs : List (ℕ × List End)} {fe rs : List ℕ}
    (hv : TourValid vCap eCap ⟨ordOfRecords recs, initTourForest recs fe rs, ∅⟩) :
    TourValid vCap eCap (tourInitStage1Abs recs rs) := by
  have hF0 : (tourInitStage1Abs recs rs).rf.F.IsForest := by
    refine ⟨fun _ he => by simp [tourInitStage1Abs] at he, fun P ⟨hne, _, _, hw⟩ => ?_⟩
    cases hw with
    | nil => exact hne rfl
    | cons he _ _ => simp [tourInitStage1Abs] at he
  refine
    { ordWithin := hv.ordWithin
      compat :=
        { nodup := hv.compat.nodup
          unique := hv.compat.unique
          forest := hF0
          vert := hv.compat.vert
          forestEnd := fun {_} he => by simp [tourInitStage1Abs] at he }
      roots_sub := Finset.Subset.refl _
      verts_lt := hv.verts_lt
      unique_root := fun v hvV => by
        refine ⟨v, ⟨hvV, connected_refl _ v⟩, fun r ⟨_, hvr⟩ => ?_⟩
        by_contra hne
        obtain ⟨e, heE, _⟩ := exists_edge_of_connected_ne hvr (Ne.symm hne)
        simp [tourInitStage1Abs] at heE
      marked_open := fun _ hx => (Finset.notMem_empty _ hx).elim }

theorem fullTour_of_empty_E {ord : ℕ → List End} {F : MGraph} (hF : F.IsForest)
    (hE : F.E = ∅) (v : ℕ) :
    fullTour ord F hF v = ord v := by
  rw [fullTour, fullTourBlocks.eq_def]
  simp [hE]

theorem ordOfRecords_mem_iff {recs : List (ℕ × List End)} (hnd : (recs.map Prod.fst).Nodup)
    {v : ℕ} {xs : List End} (hmem : (v, xs) ∈ recs) :
    ordOfRecords recs v = xs := by
  induction recs with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨w, ys⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [ordOfRecords_cons_of_nodup (by simpa using List.nodup_cons.mpr hnd)]
    rcases List.mem_cons.mp hmem with h1 | h2
    · cases h1; simp
    · have hne : v ≠ w := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨(v, xs), h2, rfl⟩)
      rw [Function.update_of_ne hne]; exact ih hnd.2 h2

theorem ordOfRecords_eq_nil_of_not_mem {recs : List (ℕ × List End)} {v : ℕ}
    (hnot : ∀ xs, (v, xs) ∉ recs) : ordOfRecords recs v = [] := by
  induction recs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨w, ys⟩
    have hne : w ≠ v := fun heq => hnot ys (heq ▸ List.mem_cons_self)
    simp only [ordOfRecords, List.find?_cons, beq_false_of_ne hne]
    exact ih fun xs hx => hnot xs (List.mem_cons_of_mem _ hx)

theorem readOrdRecords_eq_of_agree {m₁ m₂ : ℕ → ℕ} :
    ∀ (count a : ℕ),
      (∀ x, a ≤ x → x < a + ordRecordsWords (readOrdRecords m₁ count a) → m₂ x = m₁ x) →
      readOrdRecords m₂ count a = readOrdRecords m₁ count a
  | 0, _, _ => rfl
  | count + 1, a, hag => by
    have hwords : 2 + m₁ (a + 1) + ordRecordsWords (readOrdRecords m₁ count (a + 2 + m₁ (a + 1))) =
        ordRecordsWords (readOrdRecords m₁ (count + 1) a) := by
      simp [readOrdRecords, ordRecordsWords, readList_length]
    have h0 : m₂ a = m₁ a := hag a (le_refl _) (by omega)
    have h1 : m₂ (a + 1) = m₁ (a + 1) := hag (a + 1) (by omega) (by omega)
    have hlist : readList m₂ (a + 2) (m₁ (a + 1)) = readList m₁ (a + 2) (m₁ (a + 1)) := by
      apply List.ext_getElem (by simp [readList_length])
      intro i hi _
      simp only [readList_length] at hi
      simp only [readList_getElem]
      exact hag (a + 2 + i) (by omega) (by omega)
    have htl := readOrdRecords_eq_of_agree count (a + 2 + m₁ (a + 1)) fun x hx1 hx2 =>
      hag x (by omega) (by omega)
    simp only [readOrdRecords, h0, h1, hlist, htl]

/-! ## WordRAM bodies for Stage 1 -/

/-- Header and node-0 initialization prefix on `[vCap, eCap, ordPtr, rsPtr, b]`. -/
def tourInitHeaderStmt : Stmt :=
  .assign 5 (.bin .add (.reg 4) (.const 16)) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 0)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 0)) ;;
  .assign 8 (.bin .add (.reg 7) (.bin .add (.reg 1) (.reg 1))) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .add (.reg 1) (.reg 1))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 9) (.bin .add (.reg 1) (.reg 1))) (.const 1)) ;;
  .assign 14 (.bin .add (.reg 13) (.bin .add (.reg 1) (.reg 1))) ;;
  .assign 15 (.bin .add (.reg 14) (.bin .add (.reg 1) (.reg 1))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 15) (.bin .add (.reg 1) (.reg 1))) (.bin .add (.reg 0) (.reg 0))) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.const 17) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1)))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 2)) ;;
  .store (.bin .add (.reg 4) (.const HDR_VCAP)) (.reg 0) ;;
  .store (.bin .add (.reg 4) (.const HDR_ECAP)) (.reg 1) ;;
  .store (.bin .add (.reg 4) (.const HDR_ORD_H)) (.reg 11) ;;
  .store (.bin .add (.reg 4) (.const HDR_FIRST_END)) (.reg 5) ;;
  .store (.bin .add (.reg 4) (.const HDR_IS_ROOT)) (.reg 6) ;;
  .store (.bin .add (.reg 4) (.const HDR_NODE_OF_END)) (.reg 7) ;;
  .store (.bin .add (.reg 4) (.const HDR_END_OWNER)) (.reg 8) ;;
  .store (.bin .add (.reg 4) (.const HDR_KEY_OF_NODE)) (.reg 9) ;;
  .store (.bin .add (.reg 4) (.const HDR_MARK_ARR)) (.reg 13) ;;
  .store (.bin .add (.reg 4) (.const HDR_PRED_ARR)) (.reg 14) ;;
  .store (.bin .add (.reg 4) (.const HDR_NEXT_ARR)) (.reg 15) ;;
  .store (.bin .add (.reg 4) (.const HDR_NODES_BASE)) (.reg 10) ;;
  .store (.bin .add (.reg 4) (.const HDR_FOOT_END)) (.reg 11) ;;
  .store (.bin .add (.reg 4) (.const HDR_FUEL)) (.reg 12) ;;
  .store (.bin .add (.reg 10) (.const 6)) (.const 17) ;;
  .store (.bin .add (.reg 10) (.const 7)) (.const 6) ;;
  .store (.bin .add (.reg 10) (.const 8)) (.const 1)

/-- Inner loop building the splay tree for one nonempty vertex record `(r18 = v, r19 = len)` whose
keys start at `r15`. -/
def tourInitInnerLoop (initNodeProc joinProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 21) (.reg 19))
    (.assign 22 (.load (.bin .add (.reg 15) (.reg 21))) ;;
     .assign 16 (.bin .add (.reg 16) (.const 1)) ;;
     .store (.bin .add (.reg 7) (.reg 22)) (.reg 16) ;;
     .store (.bin .add (.reg 9) (.reg 16)) (.reg 22) ;;
     .store (.bin .add (.reg 8) (.reg 22)) (.bin .add (.reg 18) (.const 1)) ;;
     .assign 24 (.const 1) ;;
     .assign 25 (.const 0) ;;
     .cond (.bin .eq (.reg 21) (.const 0))
       (.store (.bin .add (.reg 5) (.reg 18)) (.reg 16) ;;
        .assign 23 (.bin .add (.reg 18) (.const 1)) ;;
        .call 26 initNodeProc [.reg 10, .reg 16, .reg 24, .reg 25, .reg 23] ;;
        .assign 20 (.reg 16))
       (.call 26 initNodeProc [.reg 10, .reg 16, .reg 24, .reg 25, .reg 25] ;;
        .call 20 joinProc [.reg 10, .reg 20, .reg 16, .reg 12, .reg 13]) ;;
     .assign 21 (.bin .add (.reg 21) (.const 1)))

/-- Outer loop scanning all `r14` order records starting at `r15`. -/
def tourInitOuterLoop (initNodeProc joinProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 17) (.reg 14))
    (.assign 18 (.load (.reg 15)) ;;
     .assign 19 (.load (.bin .add (.reg 15) (.const 1))) ;;
     .assign 15 (.bin .add (.reg 15) (.const 2)) ;;
     .cond (.reg 19)
       (.store (.bin .add (.reg 6) (.reg 18)) (.const 1) ;;
        .assign 20 (.const 0) ;;
        .assign 21 (.const 0) ;;
        tourInitInnerLoop initNodeProc joinProc)
       .nop ;;
     .assign 15 (.bin .add (.reg 15) (.reg 19)) ;;
     .assign 17 (.bin .add (.reg 17) (.const 1)))

/-- Loop marking every root in `rsPtr` (`r14 = mem rsPtr`, `r15 = rsPtr + 1`) in `isRoot`. -/
def tourInitRootsLoop : Stmt :=
  .loop (.bin .lt (.reg 17) (.reg 14))
    (.assign 18 (.load (.bin .add (.reg 15) (.reg 17))) ;;
     .store (.bin .add (.reg 6) (.reg 18)) (.const 1) ;;
     .assign 17 (.bin .add (.reg 17) (.const 1)))

/-- Full Stage 1 procedure `[vCap, eCap, ordPtr, rsPtr, b] -> hOut`. -/
def tourInitStage1Body (ordInitProc initNodeProc joinProc : ℕ) : Stmt :=
  tourInitHeaderStmt ;;
  .call 13 ordInitProc [.reg 0, .reg 1, .reg 2, .reg 11] ;;
  .assign 14 (.load (.reg 2)) ;;
  .assign 15 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 16 (.const 0) ;;
  .assign 17 (.const 0) ;;
  tourInitOuterLoop initNodeProc joinProc ;;
  .store (.bin .add (.reg 4) (.const HDR_NUM_NODES)) (.reg 16) ;;
  .assign 14 (.load (.reg 3)) ;;
  .assign 15 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 17 (.const 0) ;;
  tourInitRootsLoop ;;
  .ret (.reg 13)

theorem tourInitStage1Body_noRand (oP iP jP : ℕ) :
    (tourInitStage1Body oP iP jP).NoRand := by
  simp [tourInitStage1Body, tourInitHeaderStmt, tourInitOuterLoop, tourInitInnerLoop,
    tourInitRootsLoop, Stmt.NoRand]

/-! ## Step 1: Header + node 0 execution -/

theorem tourInitHeader_runs {w vCap eCap ordPtr rsPtr b pos : ℕ} {p : Program}
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hzero : ZeroFrom mem b)
    (hbound : ordHandleOf b vCap eCap < 2 ^ w) :
    ∃ stH cH,
      Runs w p ω tourInitHeaderStmt (startState [vCap, eCap, ordPtr, rsPtr, b] mem pos) .normal stH cH ∧
      stH.regs 0 = vCap ∧ stH.regs 1 = eCap ∧ stH.regs 2 = ordPtr ∧ stH.regs 3 = rsPtr ∧ stH.regs 4 = b ∧
      stH.regs 5 = firstEndBase b ∧ stH.regs 6 = isRootBase b vCap ∧ stH.regs 7 = nodeOfEndBase b vCap ∧
      stH.regs 8 = endOwnerBase b vCap eCap ∧ stH.regs 9 = keyOfNodeBase b vCap eCap ∧
      stH.regs 10 = nodesBase b vCap eCap ∧ stH.regs 11 = ordHandleOf b vCap eCap ∧
      stH.regs 12 = 2 * eCap + 2 ∧
      TourHeaderAt vCap eCap b 0 stH.mem ∧
      tourLayout.NodesAt stH.mem (nodesBase b vCap eCap) 0 tourEmptyState ∧
      (∀ a, b + 16 ≤ a → a < nodesBase b vCap eCap → stH.mem a = 0) ∧
      ZeroFrom stH.mem (ordHandleOf b vCap eCap) ∧
      (∀ a < b, stH.mem a = mem a) ∧ cH ≤ 250 := by
  have hwide : 18 ≤ 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hbound; omega
  have hbound' : b + 16 + 4 * vCap + 12 * eCap + 1 + 17 * (2 * eCap + 1) < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize] at hbound; omega
  have hgeo : firstEndBase b < 2 ^ w ∧ isRootBase b vCap < 2 ^ w ∧ nodeOfEndBase b vCap < 2 ^ w ∧
      endOwnerBase b vCap eCap < 2 ^ w ∧ keyOfNodeBase b vCap eCap < 2 ^ w ∧
      markArrBase b vCap eCap < 2 ^ w ∧ predArrBase b vCap eCap < 2 ^ w ∧
      nextArrBase b vCap eCap < 2 ^ w ∧ nodesBase b vCap eCap + 17 < 2 ^ w ∧
      2 * eCap + 2 < 2 ^ w ∧ vCap + vCap < 2 ^ w ∧ 17 * (2 * eCap + 1) < 2 ^ w := by
    simp [firstEndBase, isRootBase, nodeOfEndBase, endOwnerBase, keyOfNodeBase,
      markArrBase, predArrBase, nextArrBase, nodesBase]
    omega
  set s0 : State := startState [vCap, eCap, ordPtr, rsPtr, b] mem pos
  set r1 := Function.update s0.regs 5 (firstEndBase b)
  set r2 := Function.update r1 6 (isRootBase b vCap)
  set r3 := Function.update r2 7 (nodeOfEndBase b vCap)
  set r4 := Function.update r3 8 (endOwnerBase b vCap eCap)
  set r5 := Function.update r4 9 (keyOfNodeBase b vCap eCap)
  set r6 := Function.update r5 13 (markArrBase b vCap eCap)
  set r7 := Function.update r6 14 (predArrBase b vCap eCap)
  set r8 := Function.update r7 15 (nextArrBase b vCap eCap)
  set r9 := Function.update r8 10 (nodesBase b vCap eCap)
  set r10 := Function.update r9 11 (ordHandleOf b vCap eCap)
  set r11 := Function.update r10 12 (2 * eCap + 2)
  have ha1 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.const 16))) s0 .normal ⟨mem, r1, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨firstEndBase b, by simp [Expr.eval, s0, startState, BinOp.eval, firstEndBase, (by omega : 16 < 2 ^ w), (by omega : b + 16 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha2 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 0))) ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨isRootBase b vCap, by simp [Expr.eval, r1, s0, startState, BinOp.eval, firstEndBase, isRootBase, (by omega : b + 16 + vCap < 2 ^ w)], rfl, rfl, rfl⟩
  have ha3 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 0))) ⟨mem, r2, pos⟩ .normal ⟨mem, r3, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨nodeOfEndBase b vCap, by simp [Expr.eval, r2, r1, s0, startState, BinOp.eval, isRootBase, nodeOfEndBase, (by omega : b + 16 + vCap + vCap < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha4 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.bin .add (.reg 1) (.reg 1)))) ⟨mem, r3, pos⟩ .normal ⟨mem, r4, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨endOwnerBase b vCap eCap, by simp [Expr.eval, r3, r2, r1, s0, startState, BinOp.eval, nodeOfEndBase, endOwnerBase, (by omega : eCap + eCap < 2 ^ w), (by omega : b + 16 + 2 * vCap + (eCap + eCap) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha5 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.bin .add (.reg 1) (.reg 1)))) ⟨mem, r4, pos⟩ .normal ⟨mem, r5, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨keyOfNodeBase b vCap eCap, by simp [Expr.eval, r4, r3, r2, r1, s0, startState, BinOp.eval, endOwnerBase, keyOfNodeBase, (by omega : eCap + eCap < 2 ^ w), (by omega : b + 16 + 2 * vCap + 2 * eCap + (eCap + eCap) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 13 (.bin .add (.bin .add (.reg 9) (.bin .add (.reg 1) (.reg 1))) (.const 1))) ⟨mem, r5, pos⟩ .normal ⟨mem, r6, pos⟩ 8 :=
    runs_assign_iff.mpr ⟨markArrBase b vCap eCap, by simp [Expr.eval, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, keyOfNodeBase, markArrBase, (by omega : 1 < 2 ^ w), (by omega : eCap + eCap < 2 ^ w), (by omega : b + 16 + 2 * vCap + 4 * eCap + (eCap + eCap) < 2 ^ w), (by omega : b + 16 + 2 * vCap + 4 * eCap + (eCap + eCap) + 1 < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.bin .add (.reg 1) (.reg 1)))) ⟨mem, r6, pos⟩ .normal ⟨mem, r7, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨predArrBase b vCap eCap, by simp [Expr.eval, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, markArrBase, predArrBase, (by omega : eCap + eCap < 2 ^ w), (by omega : b + 16 + 2 * vCap + 6 * eCap + 1 + (eCap + eCap) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 15 (.bin .add (.reg 14) (.bin .add (.reg 1) (.reg 1)))) ⟨mem, r7, pos⟩ .normal ⟨mem, r8, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨nextArrBase b vCap eCap, by simp [Expr.eval, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, predArrBase, nextArrBase, (by omega : eCap + eCap < 2 ^ w), (by omega : b + 16 + 2 * vCap + 8 * eCap + 1 + (eCap + eCap) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha9 : Runs w p ω (.assign 10 (.bin .add (.bin .add (.reg 15) (.bin .add (.reg 1) (.reg 1))) (.bin .add (.reg 0) (.reg 0)))) ⟨mem, r8, pos⟩ .normal ⟨mem, r9, pos⟩ 10 :=
    runs_assign_iff.mpr ⟨nodesBase b vCap eCap, by simp [Expr.eval, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, nextArrBase, nodesBase, (by omega : eCap + eCap < 2 ^ w), (by omega : vCap + vCap < 2 ^ w), (by omega : b + 16 + 2 * vCap + 10 * eCap + 1 + (eCap + eCap) < 2 ^ w), (by omega : b + 16 + 2 * vCap + 10 * eCap + 1 + (eCap + eCap) + (vCap + vCap) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha10 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.bin .mul (.const 17) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1))))) ⟨mem, r9, pos⟩ .normal ⟨mem, r10, pos⟩ 10 :=
    runs_assign_iff.mpr ⟨ordHandleOf b vCap eCap, by
      simp [Expr.eval, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, nodesBase, ordHandleOf, tourFixedSize,
        (by omega : 17 < 2 ^ w), (by omega : 1 < 2 ^ w), (by omega : eCap + eCap < 2 ^ w),
        (by omega : eCap + eCap + 1 < 2 ^ w), (by omega : 17 * (eCap + eCap + 1) < 2 ^ w),
        (by omega : b + 16 + 4 * vCap + 12 * eCap + 1 + 17 * (eCap + eCap + 1) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have ha11 : Runs w p ω (.assign 12 (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 2))) ⟨mem, r10, pos⟩ .normal ⟨mem, r11, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨2 * eCap + 2, by simp [Expr.eval, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : eCap + eCap < 2 ^ w), (by omega : eCap + eCap + 2 < 2 ^ w)]; omega, rfl, rfl, rfl⟩
  have hr11 : r11 0 = vCap ∧ r11 1 = eCap ∧ r11 2 = ordPtr ∧ r11 3 = rsPtr ∧ r11 4 = b ∧
      r11 5 = firstEndBase b ∧ r11 6 = isRootBase b vCap ∧ r11 7 = nodeOfEndBase b vCap ∧
      r11 8 = endOwnerBase b vCap eCap ∧ r11 9 = keyOfNodeBase b vCap eCap ∧
      r11 10 = nodesBase b vCap eCap ∧ r11 11 = ordHandleOf b vCap eCap ∧
      r11 12 = 2 * eCap + 2 ∧ r11 13 = markArrBase b vCap eCap ∧
      r11 14 = predArrBase b vCap eCap ∧ r11 15 = nextArrBase b vCap eCap := by
    simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]
  -- Helper for storing `reg rVal` at `b + off`
  have mkSt : ∀ (m : ℕ → ℕ) (off rVal val : ℕ), off < 16 → r11 rVal = val →
      Runs w p ω (.store (.bin .add (.reg 4) (.const off)) (.reg rVal)) ⟨m, r11, pos⟩ .normal
        ⟨Function.update m (b + off) val, r11, pos⟩ 5 := fun m off rVal val hoff hrv =>
    runs_store_iff.mpr ⟨b + off, val,
      by simp [Expr.eval, hr11.2.2.2.2.1, BinOp.eval, (by omega : off < 2 ^ w), (by simp [ordHandleOf, tourFixedSize] at hbound; omega : b + off < 2 ^ w)],
      by simp [Expr.eval, hrv], rfl, rfl, rfl⟩
  have mkSt0 : ∀ (m : ℕ → ℕ) (off val : ℕ), off < 17 → val < 2 ^ w →
      Runs w p ω (.store (.bin .add (.reg 10) (.const off)) (.const val)) ⟨m, r11, pos⟩ .normal
        ⟨Function.update m (nodesBase b vCap eCap + off) val, r11, pos⟩ 5 := fun m off val hoff hvw =>
    runs_store_iff.mpr ⟨nodesBase b vCap eCap + off, val,
      by simp [Expr.eval, hr11.2.2.2.2.2.2.2.2.2.2.1, BinOp.eval, (by omega : off < 2 ^ w), (by omega : nodesBase b vCap eCap + off < 2 ^ w)],
      by simp [Expr.eval, hvw], rfl, rfl, rfl⟩
  set m1 := Function.update mem (b + HDR_VCAP) vCap
  set m2 := Function.update m1 (b + HDR_ECAP) eCap
  set m3 := Function.update m2 (b + HDR_ORD_H) (ordHandleOf b vCap eCap)
  set m4 := Function.update m3 (b + HDR_FIRST_END) (firstEndBase b)
  set m5 := Function.update m4 (b + HDR_IS_ROOT) (isRootBase b vCap)
  set m6 := Function.update m5 (b + HDR_NODE_OF_END) (nodeOfEndBase b vCap)
  set m7 := Function.update m6 (b + HDR_END_OWNER) (endOwnerBase b vCap eCap)
  set m8 := Function.update m7 (b + HDR_KEY_OF_NODE) (keyOfNodeBase b vCap eCap)
  set m9 := Function.update m8 (b + HDR_MARK_ARR) (markArrBase b vCap eCap)
  set m10 := Function.update m9 (b + HDR_PRED_ARR) (predArrBase b vCap eCap)
  set m11 := Function.update m10 (b + HDR_NEXT_ARR) (nextArrBase b vCap eCap)
  set m12 := Function.update m11 (b + HDR_NODES_BASE) (nodesBase b vCap eCap)
  set m13 := Function.update m12 (b + HDR_FOOT_END) (ordHandleOf b vCap eCap)
  set m14 := Function.update m13 (b + HDR_FUEL) (2 * eCap + 2)
  set m15 := Function.update m14 (nodesBase b vCap eCap + 6) 17
  set m16 := Function.update m15 (nodesBase b vCap eCap + 7) 6
  set m17 := Function.update m16 (nodesBase b vCap eCap + 8) 1
  have hm17_other : ∀ a, (∀ k < 15, a ≠ b + k) → a ≠ nodesBase b vCap eCap + 6 →
      a ≠ nodesBase b vCap eCap + 7 → a ≠ nodesBase b vCap eCap + 8 → m17 a = mem a := fun a hk h6 h7 h8 => by
    simp only [m17, m16, m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1,
      HDR_VCAP, HDR_ECAP, HDR_ORD_H, HDR_FIRST_END, HDR_IS_ROOT, HDR_NODE_OF_END, HDR_END_OWNER,
      HDR_KEY_OF_NODE, HDR_MARK_ARR, HDR_PRED_ARR, HDR_NEXT_ARR, HDR_NODES_BASE, HDR_FOOT_END, HDR_FUEL]
    rw [Function.update_of_ne h8, Function.update_of_ne h7, Function.update_of_ne h6,
      Function.update_of_ne (hk 14 (by omega)), Function.update_of_ne (hk 13 (by omega)),
      Function.update_of_ne (hk 12 (by omega)), Function.update_of_ne (hk 11 (by omega)),
      Function.update_of_ne (hk 10 (by omega)), Function.update_of_ne (hk 9 (by omega)),
      Function.update_of_ne (hk 8 (by omega)), Function.update_of_ne (hk 7 (by omega)),
      Function.update_of_ne (hk 6 (by omega)), Function.update_of_ne (hk 5 (by omega)),
      Function.update_of_ne (hk 4 (by omega)), Function.update_of_ne (hk 2 (by omega)),
      Function.update_of_ne (hk 1 (by omega)), Function.update_of_ne (hk 0 (by omega))]
  have hrun_stores : Runs w p ω
      (.store (.bin .add (.reg 4) (.const HDR_VCAP)) (.reg 0) ;;
       .store (.bin .add (.reg 4) (.const HDR_ECAP)) (.reg 1) ;;
       .store (.bin .add (.reg 4) (.const HDR_ORD_H)) (.reg 11) ;;
       .store (.bin .add (.reg 4) (.const HDR_FIRST_END)) (.reg 5) ;;
       .store (.bin .add (.reg 4) (.const HDR_IS_ROOT)) (.reg 6) ;;
       .store (.bin .add (.reg 4) (.const HDR_NODE_OF_END)) (.reg 7) ;;
       .store (.bin .add (.reg 4) (.const HDR_END_OWNER)) (.reg 8) ;;
       .store (.bin .add (.reg 4) (.const HDR_KEY_OF_NODE)) (.reg 9) ;;
       .store (.bin .add (.reg 4) (.const HDR_MARK_ARR)) (.reg 13) ;;
       .store (.bin .add (.reg 4) (.const HDR_PRED_ARR)) (.reg 14) ;;
       .store (.bin .add (.reg 4) (.const HDR_NEXT_ARR)) (.reg 15) ;;
       .store (.bin .add (.reg 4) (.const HDR_NODES_BASE)) (.reg 10) ;;
       .store (.bin .add (.reg 4) (.const HDR_FOOT_END)) (.reg 11) ;;
       .store (.bin .add (.reg 4) (.const HDR_FUEL)) (.reg 12) ;;
       .store (.bin .add (.reg 10) (.const 6)) (.const 17) ;;
       .store (.bin .add (.reg 10) (.const 7)) (.const 6) ;;
       .store (.bin .add (.reg 10) (.const 8)) (.const 1))
      ⟨mem, r11, pos⟩ .normal ⟨m17, r11, pos⟩ _ :=
    tour_runs_seq_normal (mkSt mem HDR_VCAP 0 vCap (by decide) hr11.1)
      (tour_runs_seq_normal (mkSt m1 HDR_ECAP 1 eCap (by decide) hr11.2.1)
      (tour_runs_seq_normal (mkSt m2 HDR_ORD_H 11 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m3 HDR_FIRST_END 5 _ (by decide) hr11.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m4 HDR_IS_ROOT 6 _ (by decide) hr11.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m5 HDR_NODE_OF_END 7 _ (by decide) hr11.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m6 HDR_END_OWNER 8 _ (by decide) hr11.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m7 HDR_KEY_OF_NODE 9 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m8 HDR_MARK_ARR 13 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m9 HDR_PRED_ARR 14 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m10 HDR_NEXT_ARR 15 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      (tour_runs_seq_normal (mkSt m11 HDR_NODES_BASE 10 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m12 HDR_FOOT_END 11 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt m13 HDR_FUEL 12 _ (by decide) hr11.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (tour_runs_seq_normal (mkSt0 m14 6 17 (by decide) (by omega))
      (tour_runs_seq_normal (mkSt0 m15 7 6 (by decide) (by omega))
        (mkSt0 m16 8 1 (by decide) (by omega)))))))))))))))))
  have hnb_ge : b + 16 < nodesBase b vCap eCap := by simp [nodesBase]; omega
  have hhdr : TourHeaderAt vCap eCap b 0 m17 := by
    have hnd_ne : ∀ k < 15, ∀ j, 6 ≤ j → j ≤ 8 → b + k ≠ nodesBase b vCap eCap + j := fun k hk j hj1 hj2 => by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [m17, m16, m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1,
        HDR_VCAP, HDR_ECAP, HDR_ORD_H, HDR_NUM_NODES, HDR_FIRST_END, HDR_IS_ROOT, HDR_NODE_OF_END,
        HDR_END_OWNER, HDR_KEY_OF_NODE, HDR_MARK_ARR, HDR_PRED_ARR, HDR_NEXT_ARR, HDR_NODES_BASE,
        HDR_FOOT_END, HDR_FUEL]
    all_goals
      (repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)]))
    · exact hzero (b + 3) (by omega)
  have hnd0 : tourLayout.NodesAt m17 (nodesBase b vCap eCap) 0 tourEmptyState := by
    intro u hu
    have hu0 : u = 0 := by omega
    subst hu0
    have hz_off : ∀ j < 17, j ≠ 6 → j ≠ 7 → j ≠ 8 → m17 (nodesBase b vCap eCap + j) = 0 := fun j hj h6 h7 h8 => by
      rw [hm17_other _ (fun k hk => by omega) (by omega) (by omega) (by omega)]
      exact hzero _ (by simp [nodesBase]; omega)
    have h6 : m17 (nodesBase b vCap eCap + 6) = 17 := by
      simp only [m17, m16, m15]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have h7 : m17 (nodesBase b vCap eCap + 7) = 6 := by
      simp only [m17, m16]; rw [Function.update_of_ne (by omega), Function.update_self]
    have h8 : m17 (nodesBase b vCap eCap + 8) = 1 := by simp [m17]
    refine ⟨by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_LEFT, tourEmptyState, tourZeroNode] using hz_off 0 (by omega) (by omega) (by omega) (by omega),
      by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_RIGHT, tourEmptyState, tourZeroNode] using hz_off 1 (by omega) (by omega) (by omega) (by omega),
      by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_PAR, tourEmptyState, tourZeroNode] using hz_off 2 (by omega) (by omega) (by omega) (by omega),
      by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_PPAR, tourEmptyState, tourZeroNode] using hz_off 3 (by omega) (by omega) (by omega) (by omega),
      by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_SZ, tourEmptyState, tourZeroNode] using hz_off 4 (by omega) (by omega) (by omega) (by omega),
      by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_REV, tourEmptyState, tourZeroNode] using hz_off 5 (by omega) (by omega) (by omega) (by omega),
      ⟨by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL] using h6,
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using h7,
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, Nat.add_assoc] using h8,
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 9 (by omega) (by omega) (by omega) (by omega),
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 10 (by omega) (by omega) (by omega) (by omega),
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 11 (by omega) (by omega) (by omega) (by omega)⟩,
      ⟨by simpa [NodeLayout.nodeAddr, tourLayout_stride, tourLayout_offSum, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 12 (by omega) (by omega) (by omega) (by omega),
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, tourLayout_offSum, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 13 (by omega) (by omega) (by omega) (by omega),
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, tourLayout_offSum, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 14 (by omega) (by omega) (by omega) (by omega),
       by simpa [NodeLayout.nodeAddr, tourLayout_stride, tourLayout_offSum, tourEmptyState, tourZeroNode, Nat.add_assoc] using hz_off 15 (by omega) (by omega) (by omega) (by omega)⟩,
      trivial⟩
  refine ⟨⟨m17, r11, pos⟩, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8
        (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11 hrun_stores)))))))))),
    hr11.1, hr11.2.1, hr11.2.2.1, hr11.2.2.2.1, hr11.2.2.2.2.1, hr11.2.2.2.2.2.1,
    hr11.2.2.2.2.2.2.1, hr11.2.2.2.2.2.2.2.1, hr11.2.2.2.2.2.2.2.2.1, hr11.2.2.2.2.2.2.2.2.2.1,
    hr11.2.2.2.2.2.2.2.2.2.2.1, hr11.2.2.2.2.2.2.2.2.2.2.2.1, hr11.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hhdr, hnd0,
    fun a ha1 ha2 => by dsimp only; rw [hm17_other a (fun k hk => by omega) (by omega) (by omega) (by omega)]; exact hzero a (by omega),
    fun a ha => by
      dsimp only
      have hnb_end := nodesBase_end_eq b vCap eCap
      rw [hm17_other a (fun k hk => by omega) (by omega) (by omega) (by omega)]
      exact hzero a (by simp [ordHandleOf, tourFixedSize] at ha ⊢; omega),
    fun a ha => hm17_other a (fun k hk => by omega) (by omega) (by omega) (by omega), by omega⟩

/-! ## Step 2: Inner loop for one nonempty vertex record -/



theorem tourInitRoots_runs {w vCap eCap b rsPtr hOut : ℕ} {p : Program}
    (ω : ℕ → Bool) {st0 : State}
    (hrs_lt : rsPtr + 1 + st0.mem rsPtr ≤ b)
    (hrs_vcap : ∀ r ∈ readNatList st0.mem rsPtr, r < vCap)
    (hord_le : ordHandleOf b vCap eCap ≤ hOut) (hroom : hOut + 2 < 2 ^ w)
    (hr6 : st0.regs 6 = isRootBase b vCap) (hr13 : st0.regs 13 = hOut)
    (hr14 : st0.regs 14 = st0.mem rsPtr) (hr15 : st0.regs 15 = rsPtr + 1) (hr17 : st0.regs 17 = 0) :
    ∃ st1 c1,
      Runs w p ω tourInitRootsLoop st0 .normal st1 c1 ∧
      st1.regs 13 = hOut ∧
      (∀ r ∈ readNatList st0.mem rsPtr, st1.mem (isRootBase b vCap + r) = 1) ∧
      (∀ a, (∀ r ∈ readNatList st0.mem rsPtr, a ≠ isRootBase b vCap + r) → st1.mem a = st0.mem a) ∧
      c1 ≤ 25 * st0.mem rsPtr + 10 := by
  set n := st0.mem rsPtr
  have hloop : ∀ (rem i : ℕ) (stC : State), i + rem = n →
      stC.regs 6 = isRootBase b vCap → stC.regs 13 = hOut →
      stC.regs 14 = n → stC.regs 15 = rsPtr + 1 → stC.regs 17 = i →
      (∀ j < i, stC.mem (isRootBase b vCap + st0.mem (rsPtr + 1 + j)) = 1) →
      (∀ a, (∀ r ∈ readNatList st0.mem rsPtr, a ≠ isRootBase b vCap + r) → stC.mem a = st0.mem a) →
      ∃ st1 c,
        Runs w p ω tourInitRootsLoop stC .normal st1 c ∧
        st1.regs 13 = hOut ∧
        (∀ r ∈ readNatList st0.mem rsPtr, st1.mem (isRootBase b vCap + r) = 1) ∧
        (∀ a, (∀ r ∈ readNatList st0.mem rsPtr, a ≠ isRootBase b vCap + r) → st1.mem a = st0.mem a) ∧
        c ≤ 25 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i stC hi _ hr13C hr14C _ hr17C hset hfr
      have hcond : (Expr.bin .lt (.reg 17) (.reg 14)).eval w stC = some 0 := by
        have hin : i = n := by omega
        simp [Expr.eval, hr17C, hr14C, hin, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hr13C, fun r hr => ?_, hfr, by simp [Expr.size]⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      simp only [readNatList, readList_length] at hj
      simpa [readNatList, readList_getElem] using hset j (by omega)
    | succ rem ih =>
      intro i stC hi hr6C hr13C hr14C hr15C hr17C hset hfr
      have hi_lt : i < n := by omega
      set r := st0.mem (rsPtr + 1 + i)
      have hr_in : r ∈ readNatList st0.mem rsPtr := by
        rw [List.mem_iff_getElem]; exact ⟨i, by simp [readNatList, readList_length, n, hi_lt], by simp [readNatList, readList_getElem, r]⟩
      have hr_lt : r < vCap := hrs_vcap r hr_in
      have hcond : (Expr.bin .lt (.reg 17) (.reg 14)).eval w stC = some 1 := by
        simp [Expr.eval, hr17C, hr14C, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hmem_r : stC.mem (rsPtr + 1 + i) = r :=
        hfr _ (fun r' _ => by simp [isRootBase]; omega)
      set r1 := Function.update stC.regs 18 r
      set m1 := Function.update stC.mem (isRootBase b vCap + r) 1
      set r2 := Function.update r1 17 (i + 1)
      have ha1 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 18) (rBase := 15) (rIdx := 17)
        (base := rsPtr + 1) (idx := i) (val := r) (st := stC) hr15C hr17C
        (by simp [ordHandleOf, tourFixedSize] at hord_le; omega) hmem_r
      have hst : Runs w p ω (.store (.bin .add (.reg 6) (.reg 18)) (.const 1)) ⟨stC.mem, r1, stC.pos⟩ .normal ⟨m1, r1, stC.pos⟩ 5 :=
        runs_store_iff.mpr ⟨isRootBase b vCap + r, 1,
          by simp [Expr.eval, r1, hr6C, BinOp.eval, (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : isRootBase b vCap + r < 2 ^ w)],
          by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have ha2 : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.const 1))) ⟨m1, r1, stC.pos⟩ .normal ⟨m1, r2, stC.pos⟩ 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r1, hr17C, BinOp.eval, (by omega : 1 < 2 ^ w), (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      obtain ⟨st1, cR, hrunR, hr13', hset', hfr', hcR⟩ :=
        ih (i + 1) ⟨m1, r2, stC.pos⟩ (by omega) (by simp [r2, r1, hr6C]) (by simp [r2, r1, hr13C])
          (by simp [r2, r1, hr14C]) (by simp [r2, r1, hr15C]) (by simp [r2])
          (fun j hj => by
            dsimp only [m1]
            by_cases hjeq : st0.mem (rsPtr + 1 + j) = r
            · rw [hjeq, Function.update_self]
            · have hji : j ≠ i := fun heq => hjeq (heq ▸ rfl)
              rw [Function.update_of_ne (by omega)]; exact hset j (by omega))
          (fun a ha => by dsimp only [m1]; rw [Function.update_of_ne (ha r hr_in)]; exact hfr a ha)
      exact ⟨st1, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
        tour_runs_seq_normal ha1 (tour_runs_seq_normal hst ha2), hrunR, rfl⟩)),
        hr13', hset', hfr', by clear * - hcR; simp only [Expr.size]; omega⟩
  exact hloop n 0 st0 (by omega) hr6 hr13 hr14 hr15 hr17 (fun _ h => by omega) (fun _ _ => rfl)


end MinCostFlow.SparseCore.Program
