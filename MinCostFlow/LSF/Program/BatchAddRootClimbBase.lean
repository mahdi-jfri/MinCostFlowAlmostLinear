module

public import MinCostFlow.LSF.Program.BatchAddRootMath
public import MinCostFlow.LSF.Program.BatchMinUp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Definitions, Stack Invariants, and Frame Lemmas for `addOrigRootProc` (`BatchAddRootClimbBase`)

Defines `addOrigRootProc` and its sub-statements, the static concrete-state preservation predicate
`SameStaticConcrete`, the `T_H`-stack invariants `applyThStack`, `ThStackInv`, and `StackMemAt`,
and the memory frame lemmas `addRoot_layout`, `lsfRep_of_thStack_write`, and
`auxAt_of_agree_except_qBuf`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure definitions -/

/-- Loads the handle header fields and `fIsRootBase` in `addOrigRootProc`. -/
def addOrigRootHdrStmt : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const lsfOffVCap))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const lsfOffECap))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const lsfOffN0))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const lsfOffTM))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const lsfOffTPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const lsfOffDgFPtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const lsfOffFAncPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 8) (.const fOffIsRootPtr)))

/-- Loads the `aux` and `fAnc` array pointers and initializes `(curIdx, sp)` in the slow path of
`addOrigRootProc`. -/
def addOrigRootSetupStmt : Stmt :=
  .assign 11 (.load (.bin .add (.reg 9) (.const auxOffVIdxPtr))) ;;
  .assign 12 (.load (.bin .add (.reg 9) (.const auxOffVListPtr))) ;;
  .assign 13 (.load (.bin .add (.reg 9) (.const auxOffThParentPtr))) ;;
  .assign 14 (.load (.bin .add (.reg 9) (.const auxOffThStackPtr))) ;;
  .assign 15 (.load (.bin .add (.reg 9) (.const auxOffOrigVertPtr))) ;;
  .assign 16 (.load (.bin .add (.reg 8) (.const fOffRListPtr))) ;;
  .assign 17 (.load (.bin .add (.reg 8) (.const fOffCompIdPtr))) ;;
  .assign 18 (.load (.bin .add (.reg 8) (.const fOffCompRootPtr))) ;;
  .assign 19 (.load (.bin .add (.reg 8) (.const fOffCompSizePtr))) ;;
  .assign 20 (.bin .add (.bin .mul (.const 3) (.reg 3)) (.reg 4)) ;;
  .assign 21 (.bin .add (.bin .add (.reg 7) (.const 4)) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 36 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 4)) (.bin .mul (.const 7) (.reg 2)))
    (.bin .mul (.const 3) (.reg 20))) ;;
  .assign 37 (.bin .add (.reg 36) (.reg 20)) ;;
  .assign 22 (.bin .sub (.load (.bin .add (.reg 11) (.reg 1))) (.const 1)) ;;
  .assign 23 (.const 0)

/-- Climbs `thParent` from `r22 = curIdx` until hitting a root in `fIsRoot`, pushing each visited
index onto `thStack` (`r14`) and incrementing `sp` (`r23`). -/
def addOrigRootClimbStmt : Stmt :=
  .loop (.bin .eq (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 22))))) (.const 0))
    (.store (.bin .add (.reg 14) (.reg 23)) (.reg 22) ;;
     .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
     .assign 22 (.load (.bin .add (.reg 13) (.reg 22))))

/-- One pop iteration of `addOrigRootProc`: pops `zIdx` from `thStack`, cuts `cutE` in `dgF`, marks
`z` as a root, and relabels the smaller component via `splitCompBFSProc`. -/
def addOrigRootPopStepStmt (idxMinUp idxDgDel idxBFS : ℕ) : Stmt :=
  .assign 23 (.bin .sub (.reg 23) (.const 1)) ;;
  .assign 24 (.load (.bin .add (.reg 14) (.reg 23))) ;;
  .assign 25 (.load (.bin .add (.reg 12) (.reg 24))) ;;
  .assign 26 (.load (.bin .add (.reg 17) (.reg 25))) ;;
  .assign 27 (.load (.bin .add (.reg 18) (.reg 26))) ;;
  .assign 28 (.load (.bin .add (.reg 19) (.reg 26))) ;;
  .assign 29 (.load (.bin .add (.reg 15) (.reg 27))) ;;
  .assign 30 (.bin .sub (.load (.bin .add (.reg 11) (.reg 29))) (.const 1)) ;;
  .call 31 idxMinUp [.reg 9, .reg 6, .reg 2, .reg 4, .reg 5, .reg 24, .reg 30] ;;
  .assign 32 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 36) (.reg 31))))) ;;
  .assign 33 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 37) (.reg 31))))) ;;
  .call 34 idxDgDel [.reg 7, .reg 31] ;;
  .store (.bin .add (.reg 10) (.reg 25)) (.const 1) ;;
  .assign 35 (.load (.bin .add (.reg 8) (.const fOffRCount))) ;;
  .store (.bin .add (.reg 16) (.reg 35)) (.reg 25) ;;
  .store (.bin .add (.reg 8) (.const fOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const lsfOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
  .call 34 idxBFS [.reg 7, .reg 8, .reg 9, .reg 2, .reg 20, .reg 4,
    .reg 32, .reg 33, .reg 26, .reg 27, .reg 25, .reg 28]

/-- Full `addOrigRootProc` procedure (`[b, u]`). -/
def addOrigRootProc (idxMinUp idxDgDel idxBFS : ℕ) : Stmt :=
  addOrigRootHdrStmt ;;
  .cond (.load (.bin .add (.reg 10) (.reg 1)))
    (.ret (.const 0))
    (addOrigRootSetupStmt ;;
     addOrigRootClimbStmt ;;
     .loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) ;;
     .ret (.const 0))

lemma addOrigRootProc_noRand (idxMinUp idxDgDel idxBFS : ℕ) :
    (addOrigRootProc idxMinUp idxDgDel idxBFS).NoRand := by
  simp [addOrigRootProc, addOrigRootHdrStmt, addOrigRootSetupStmt, addOrigRootClimbStmt,
    addOrigRootPopStepStmt, Stmt.NoRand]

/-! ## Static concrete equality and stack invariants -/

/-- Concrete state `x'` agrees with `x` on all static fields (everything except `rList`, `compId`,
`compRoot`, `compSize`, `activeCids`). -/
def SameStaticConcrete (x x' : LSFConcrete) : Prop :=
  x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.n0 = x.n0 ∧ x'.m0 = x.m0 ∧ x'.tM = x.tM ∧
  x'.h = x.h ∧ x'.P_fp = x.P_fp ∧ x'.L_in = x.L_in ∧ x'.L_w = x.L_w ∧ x'.k_nat = x.k_nat ∧
  x'.tOrigList = x.tOrigList ∧ x'.vList = x.vList ∧
  x'.t0Parent = x.t0Parent ∧ x'.t0ParentTreeIdx = x.t0ParentTreeIdx ∧
  x'.t0Depth = x.t0Depth ∧ x'.thParent = x.thParent ∧
  x'.upV = x.upV ∧ x'.upMinIdx = x.upMinIdx

lemma SameStaticConcrete.refl (x : LSFConcrete) : SameStaticConcrete x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma SameStaticConcrete.trans {x y z : LSFConcrete}
    (h1 : SameStaticConcrete x y) (h2 : SameStaticConcrete y z) : SameStaticConcrete x z :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

lemma SameStaticConcrete.endAddr {x x' : LSFConcrete} (h : SameStaticConcrete x x') (b : ℕ) :
    x'.endAddr b = x.endAddr b := by
  dsimp only [LSFConcrete.endAddr]
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1]

/-- Applying a top-first stack of `T_H`-indices to `S` inserts each `vList[zIdx]!` into
`S.R₀_base`. -/
def applyThStack (S : LSFState) (vList : List ℕ) : List ℕ → LSFState
  | [] => S
  | zIdx :: rest => applyThStack { S with R₀_base := insert (vList[zIdx]!) S.R₀_base } vList rest

/-- Invariant for the `T_H` climb stack `stk` (top-first). -/
def ThStackInv (S : LSFState) (vList : List ℕ) (thParent : ℕ → ℕ) (n0 : ℕ) : List ℕ → Prop
  | [] => True
  | zIdx :: rest =>
    zIdx < n0 ∧ vList[zIdx]! ∉ S.R_orig ∧
    vList[thParent zIdx]! ∈ S.R_orig ∧
    (∀ w, IsAncestor S.TH S.r₀ w (vList[zIdx]!) ↔
      w = vList[zIdx]! ∨ IsAncestor S.TH S.r₀ w (vList[thParent zIdx]!)) ∧
    ThStackInv { S with R₀_base := insert (vList[zIdx]!) S.R₀_base } vList thParent n0 rest

/-- `stk` stored bottom-up in `mem[thStackBase + 0 .. thStackBase + stk.length - 1]`, with
`stk.head` at the top (`thStackBase + stk.length - 1`). -/
def StackMemAt (mem : ℕ → ℕ) (thStackBase : ℕ) (stk : List ℕ) : Prop :=
  ∀ i (hi : i < stk.length), mem (thStackBase + (stk.length - 1 - i)) = stk[i]

lemma stackMemAt_tail {mem : ℕ → ℕ} {base a : ℕ} {tl : List ℕ}
    (h : StackMemAt mem base (a :: tl)) :
    mem (base + tl.length) = a ∧ StackMemAt mem base tl := by
  refine ⟨?_, fun i hi => ?_⟩
  · have h0 := h 0 (Nat.zero_lt_succ _)
    simpa only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero] using h0
  · have hi' := h (i + 1) (Nat.succ_lt_succ hi)
    simp only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ] at hi'
    have hsub : tl.length - (i + 1) = tl.length - 1 - i := by omega
    rwa [hsub] at hi'

lemma stackMemAt_push {mem mem' : ℕ → ℕ} {base a : ℕ} {tl : List ℕ}
    (h : StackMemAt mem base tl)
    (hpres : ∀ j < tl.length, mem' (base + j) = mem (base + j))
    (htop : mem' (base + tl.length) = a) :
    StackMemAt mem' base (a :: tl) := by
  intro i hi
  cases i with
  | zero =>
    simpa only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero] using htop
  | succ i' =>
    have hi' : i' < tl.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ]
    have hsub : tl.length - (i' + 1) = tl.length - 1 - i' := by omega
    rw [hsub, hpres _ (by omega)]
    exact h i' hi'

lemma stackMemAt_of_agree {mem mem' : ℕ → ℕ} {base : ℕ} {stk : List ℕ}
    (h : StackMemAt mem base stk)
    (hagree : ∀ j < stk.length, mem' (base + j) = mem (base + j)) :
    StackMemAt mem' base stk := fun i hi => by
  rw [hagree (stk.length - 1 - i) (by omega)]
  exact h i hi

lemma applyThStack_fields (S : LSFState) (vList : List ℕ) (stk : List ℕ) :
    let Sf := applyThStack S vList stk
    Sf.G₀ = S.G₀ ∧ Sf.k = S.k ∧ Sf.T₀ = S.T₀ ∧ Sf.r₀ = S.r₀ ∧ Sf.π = S.π ∧
    Sf.G = S.G ∧ Sf.T_cur = S.T_cur ∧ Sf.R₀_init = S.R₀_init ∧
    Sf.isolatedVerts = S.isolatedVerts ∧ Sf.origVert = S.origVert ∧
    Sf.wstr = S.wstr ∧ Sf.W_init = S.W_init ∧ Sf.numUpdates = S.numUpdates ∧
    Sf.R₀_base = S.R₀_base ∪ (stk.map fun i => vList[i]!).toFinset := by
  induction stk generalizing S with
  | nil => simp [applyThStack]
  | cons a tl ih =>
    dsimp only [applyThStack]
    have h := ih { S with R₀_base := insert (vList[a]!) S.R₀_base }
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
    rw [h.2.2.2.2.2.2.2.2.2.2.2.2.2]
    ext x; simp only [Finset.mem_union, Finset.mem_insert, List.map_cons, List.toFinset_cons]
    tauto

lemma addRoot_layout {w b : ℕ} {x : LSFConcrete}
    (_hend_ltw : x.endAddr b < 2 ^ w) :
    let vCap := x.vCap; let eCap := x.eCap; let n0 := x.n0; let tM := x.tM; let L_w := x.L_w
    let eCapF := fECap eCap n0
    let dgGPtr := lsfDgGPtr b
    let tPtr := lsfTBlockPtr b vCap eCap
    let dgFPtr := lsfDgFPtr b vCap eCap tM
    let fAncPtr := lsfFAncPtr b vCap eCap n0 tM
    let wPtr := lsfWBlockPtr b vCap eCap n0 tM
    let wstrNumPtr := lsfWstrNumPtr b vCap eCap n0 tM
    let wstrDenPtr := lsfWstrDenPtr b vCap eCap n0 tM L_w
    let auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
    b + lsfHdrSize ≤ dgGPtr ∧
    dgGPtr + dynGraphSize vCap eCap ≤ tPtr ∧
    tPtr + tBlockSize vCap eCap tM ≤ dgFPtr ∧
    dgFPtr + dynGraphSize vCap eCapF ≤ fAncPtr ∧
    fAncPtr + fAncSize vCap ≤ wPtr ∧
    wPtr + wBlockSize n0 ≤ auxPtr ∧
    auxPtr + auxSize vCap n0 ≤ wstrNumPtr ∧
    wstrNumPtr + eCap * L_w ≤ wstrDenPtr ∧
    wstrDenPtr + eCap * L_w = x.endAddr b ∧
    auxVisBBase auxPtr vCap n0 + vCap = auxThStackBase auxPtr vCap n0 ∧
    auxThStackBase auxPtr vCap n0 + (hldDepthBound n0 + 2) ≤ auxPtr + auxSize vCap n0 := by
  dsimp only [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfAuxPtr, lsfWstrDenPtr,
    lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr,
    auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
    auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
    auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]
  omega

/-- Memory modifications inside `[auxThStackBase, auxThStackBase + (hldDepthBound n0 + 2))` do not
affect `AuxAt` (nor any earlier block) and therefore preserve `(LSFRep h).rep` and `lsfPhi`. -/
lemma lsfRep_of_thStack_write {h b : ℕ} {S : LSFState} {x : LSFConcrete}
    {mem mem' : ℕ → ℕ}
    (hrep : (LSFRep h).rep b S x mem)
    (hfr : ∀ a, ¬ (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ≤ a ∧
      a < auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 +
        (hldDepthBound x.n0 + 2)) → mem' a = mem a) :
    (LSFRep h).rep b S x mem' ∧ lsfPhi b x mem' = lsfPhi b x mem := by
  set auxPtr := lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w
  set stkBase := auxThStackBase auxPtr x.vCap x.n0
  have hbelow : ∀ a < stkBase, mem' a = mem a :=
    fun a ha => hfr a (fun hc => Nat.not_le.mpr ha hc.1)
  have hhdr_lt : b + lsfHdrSize ≤ stkBase := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
      lsfDgGPtr]; omega
  have hdgG_lt : lsfDgGPtr b + dynGraphSize x.vCap x.eCap ≤ stkBase := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
      lsfDgGPtr]; omega
  have hT_lt : lsfTBlockPtr b x.vCap x.eCap + tBlockSize x.vCap x.eCap x.tM ≤ stkBase := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
      lsfDgGPtr]; omega
  have hdgF_lt : lsfDgFPtr b x.vCap x.eCap x.tM + dynGraphSize x.vCap (fECap x.eCap x.n0) ≤ stkBase := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
      lsfDgGPtr]; omega
  have hFAnc_lt : lsfFAncPtr b x.vCap x.eCap x.n0 x.tM + fAncSize x.vCap ≤ stkBase := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
      lsfDgGPtr]; omega
  have hW_lt : lsfWBlockPtr b x.vCap x.eCap x.n0 x.tM + wBlockSize x.n0 ≤ stkBase := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      lsfAuxPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr,
      lsfDgGPtr]; omega
  have habove : ∀ a, stkBase + (hldDepthBound x.n0 + 2) ≤ a → mem' a = mem a :=
    fun a ha => hfr a (fun hc => Nat.not_lt.mpr ha hc.2)
  have hstk_le_wstrN : stkBase + (hldDepthBound x.n0 + 2) ≤
      lsfWstrNumPtr b x.vCap x.eCap x.n0 x.tM := by
    dsimp [stkBase, auxPtr, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      auxSize, lsfAuxPtr, lsfWstrNumPtr]; omega
  have hstk_le_wstrD : stkBase + (hldDepthBound x.n0 + 2) ≤
      lsfWstrDenPtr b x.vCap x.eCap x.n0 x.tM x.L_w := by
    dsimp [lsfWstrDenPtr]; omega
  have hrep0 := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hk, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvlt, helt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  have hAux' : AuxAt mem' auxPtr x.vCap x.n0 x.tM S x.tOrigList x.vList
      x.t0Parent x.t0ParentTreeIdx x.t0Depth x.thParent x.upV x.upMinIdx := by
    rcases hAux with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      hvlen, hvnd, hvmem, htlen, hvLA, hvIdx, hvIdx0, hr0lt, hr0v, hp, hpe, hd, hup, hth, hthR0,
      hdR0, ht0Edge, hUpProp, hThProp, hIsOrig, hOrig, hVis⟩
    have hhd_aux : ∀ off < auxHdrSize, mem' (auxPtr + off) = mem (auxPtr + off) := fun off hoff =>
      hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
          auxHdrSize] at hoff ⊢; omega)
    dsimp only [AuxAt]
    rw [hhd_aux auxOffR0Idx (by decide)]
    refine ⟨(hhd_aux _ (by decide)).trans h0, (hhd_aux _ (by decide)).trans h1,
      (hhd_aux _ (by decide)).trans h2, (hhd_aux _ (by decide)).trans h3,
      (hhd_aux _ (by decide)).trans h4, (hhd_aux _ (by decide)).trans h5,
      (hhd_aux _ (by decide)).trans h6, (hhd_aux _ (by decide)).trans h7,
      (hhd_aux _ (by decide)).trans h8, (hhd_aux _ (by decide)).trans h9,
      (hhd_aux _ (by decide)).trans h10, (hhd_aux _ (by decide)).trans h11,
      (hhd_aux _ (by decide)).trans h12, (hhd_aux _ (by decide)).trans h13,
      (hhd_aux _ (by decide)).trans h14, (hhd_aux _ (by decide)).trans h15,
      (hhd_aux _ (by decide)).trans h16,
      hvlen, hvnd, hvmem, htlen, ?_, ?_, ?_, hr0lt, hr0v, ?_, ?_, ?_, ?_, ?_, hthR0,
      hdR0, ht0Edge, hUpProp, hThProp, ?_, ?_, ?_⟩
    · intro i hi
      exact (hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hvLA i hi)
    · intro i hi
      have hlt := hvlt _ ((hvmem _).mp (List.getElem_mem hi))
      exact (hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hvIdx i hi)
    · intro v hv hvn
      exact (hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hvIdx0 v hv hvn)
    · intro i hi
      rw [hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)]
      exact hp i hi
    · intro i hi
      rw [hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)]
      exact hpe i hi
    · intro i hi
      exact (hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hd i hi)
    · intro i hi j hj
      have hlt_ij : i * auxLogCap x.n0 + j < x.n0 * auxLogCap x.n0 := by
        calc i * auxLogCap x.n0 + j < i * auxLogCap x.n0 + auxLogCap x.n0 := Nat.add_lt_add_left hj _
          _ = (i + 1) * auxLogCap x.n0 := by ring
          _ ≤ x.n0 * auxLogCap x.n0 := Nat.mul_le_mul_right _ hi
      rw [hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase]; omega),
        hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase]; omega)]
      exact hup i hi j hj
    · intro i hi
      rw [hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase]; omega)]
      exact hth i hi
    · intro v hv
      exact (hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase]; omega)).trans (hIsOrig v hv)
    · intro w hw hwl
      exact (hbelow _ (by
        dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase]; omega)).trans (hOrig w hw hwl)
    · intro v hv
      exact ⟨(hbelow _ (by dsimp [stkBase, auxThStackBase, auxVisBBase, auxVisABase]; omega)).trans (hVis v hv).1,
        (hbelow _ (by dsimp [stkBase, auxThStackBase, auxVisBBase]; omega)).trans (hVis v hv).2⟩
  have hrep' : (LSFRep h).rep b S x mem' :=
    ⟨hxH, hh1, hLin, hLw, hkn, hk, hInv, hn0, hm0, htM, hnv, hme, htn, hn1, hvlt, helt,
      hhdr.of_agree fun a _ ha2 => hbelow a (lt_of_lt_of_le ha2 hhdr_lt),
      hdgG.of_agree fun a _ ha2 => hbelow a (lt_of_lt_of_le ha2 hdgG_lt),
      hT.of_agree fun a _ ha2 => hbelow a (lt_of_lt_of_le ha2 hT_lt),
      hdgF.of_agree fun a _ ha2 => hbelow a (lt_of_lt_of_le ha2 hdgF_lt),
      hFAnc.of_agree fun a _ ha2 => hbelow a (lt_of_lt_of_le ha2 hFAnc_lt),
      hW.of_agree fun a _ ha2 => hbelow a (lt_of_lt_of_le ha2 hW_lt),
      hwstr.of_agree
        (fun a ha1 _ => habove a (le_trans hstk_le_wstrN ha1))
        (fun a ha1 _ => habove a (le_trans hstk_le_wstrD ha1)),
      hAux'⟩
  refine ⟨hrep', ?_⟩
  rw [lsfPhi_eq_semantic hrep', lsfPhi_eq_semantic hrep0]

/-- `AuxAt` is invariant under writes inside `[auxQBufABase, auxQBufBBase + vCap)` and outside
`auxPtr`, provided `S` only changes `R₀_base`. -/
lemma auxAt_of_agree_except_qBuf {mem mem' : ℕ → ℕ} {auxPtr vCap n0 tM : ℕ} {S S' : LSFState}
    {tOrigList vList : List ℕ} {t0Parent t0ParentTreeIdx t0Depth thParent : ℕ → ℕ}
    {upV upMinIdx : ℕ → ℕ → ℕ}
    (hAux : AuxAt mem auxPtr vCap n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx)
    (hvlt : ∀ v ∈ S.T₀.V, v < vCap)
    (hT₀ : S'.T₀ = S.T₀) (hr₀ : S'.r₀ = S.r₀) (hπ : S'.π = S.π)
    (hG : S'.G = S.G) (horig : S'.origVert = S.origVert)
    (hagree : ∀ a, auxPtr ≤ a → a < auxVisBBase auxPtr vCap n0 + vCap →
      ¬ (auxQBufABase auxPtr vCap n0 ≤ a ∧ a < auxQBufBBase auxPtr vCap n0 + vCap) →
      mem' a = mem a) :
    AuxAt mem' auxPtr vCap n0 tM S' tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx := by
  have hTH : S'.TH = S.TH := by simp only [LSFState.TH, hT₀, hr₀]
  have hbelow : ∀ a, auxPtr ≤ a → a < auxQBufABase auxPtr vCap n0 → mem' a = mem a := fun a ha1 ha2 =>
    hagree a ha1 (lt_of_lt_of_le ha2 (by dsimp [auxVisBBase, auxVisABase, auxQBufBBase]; omega))
      (fun hc => Nat.not_le.mpr ha2 hc.1)
  have hvisA : ∀ v < vCap, mem' (auxVisABase auxPtr vCap n0 + v) = mem (auxVisABase auxPtr vCap n0 + v) :=
    fun v hv => hagree _
      (by dsimp [auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase,
        auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase,
        auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxVisBBase, auxVisABase]; omega)
      (fun hc => by dsimp [auxVisABase, auxQBufBBase] at hc; omega)
  have hvisB : ∀ v < vCap, mem' (auxVisBBase auxPtr vCap n0 + v) = mem (auxVisBBase auxPtr vCap n0 + v) :=
    fun v hv => hagree _
      (by dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
        auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by omega)
      (fun hc => by dsimp [auxVisBBase, auxVisABase, auxQBufBBase] at hc; omega)
  have hhd : ∀ off < auxHdrSize, mem' (auxPtr + off) = mem (auxPtr + off) := fun off hoff =>
    hbelow _ (Nat.le_add_right _ _) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase,
        auxVIdxBase, auxHdrSize] at hoff ⊢; omega)
  dsimp only [AuxAt] at hAux ⊢
  rw [hT₀, hr₀, hπ, hTH, hG, horig]
  rcases hAux with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    hvlen, hvnd, hvmem, htlen, hvLA, hvIdx, hvIdx0, hr0lt, hr0v, hp, hpe, hd, hup, hth, hthR0,
    hdR0, ht0Edge, hUpProp, hThProp, hIsOrig, hOrig, hVis⟩
  rw [hhd auxOffR0Idx (by decide)]
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1, (hhd _ (by decide)).trans h2,
    (hhd _ (by decide)).trans h3, (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7, (hhd _ (by decide)).trans h8,
    (hhd _ (by decide)).trans h9, (hhd _ (by decide)).trans h10, (hhd _ (by decide)).trans h11,
    (hhd _ (by decide)).trans h12, (hhd _ (by decide)).trans h13, (hhd _ (by decide)).trans h14,
    (hhd _ (by decide)).trans h15, (hhd _ (by decide)).trans h16,
    hvlen, hvnd, hvmem, htlen, ?_, ?_, ?_, hr0lt, hr0v, ?_, ?_, ?_, ?_, ?_, hthR0,
    hdR0, ht0Edge, hUpProp, hThProp, ?_, ?_, ?_⟩
  · intro i hi
    exact (hbelow _ (by dsimp [auxVListBase, auxVIdxBase]; omega) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase]; omega)).trans (hvLA i hi)
  · intro i hi
    have hlt := hvlt _ ((hvmem _).mp (List.getElem_mem hi))
    exact (hbelow _ (by dsimp [auxVIdxBase]; omega) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hvIdx i hi)
  · intro v hv hvn
    exact (hbelow _ (by dsimp [auxVIdxBase]; omega) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hvIdx0 v hv hvn)
  · intro i hi
    rw [hbelow _ (by dsimp [auxT0ParentBase, auxVListBase, auxVIdxBase]; omega) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase]; omega)]
    exact hp i hi
  · intro i hi
    rw [hbelow _ (by dsimp [auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase]; omega)]
    exact hpe i hi
  · intro i hi
    exact (hbelow _ (by dsimp [auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega) (by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase]; omega)).trans (hd i hi)
  · intro i hi j hj
    have hlt_ij : i * auxLogCap n0 + j < n0 * auxLogCap n0 := by
      calc i * auxLogCap n0 + j < i * auxLogCap n0 + auxLogCap n0 := Nat.add_lt_add_left hj _
        _ = (i + 1) * auxLogCap n0 := by ring
        _ ≤ n0 * auxLogCap n0 := Nat.mul_le_mul_right _ hi
    rw [hbelow _ (by dsimp [auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
        (by dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase]; omega),
      hbelow _ (by dsimp [auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
        (by dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase]; omega)]
    exact hup i hi j hj
  · intro i hi
    rw [hbelow _ (by dsimp [auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase]; omega)]
    exact hth i hi
  · intro v hv
    exact (hbelow _ (by dsimp [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxQBufABase, auxIsOrigVertBase]; omega)).trans (hIsOrig v hv)
  · intro w hw hwl
    exact (hbelow _ (by dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase]; omega)).trans (hOrig w hw hwl)
  · intro v hv
    exact ⟨(hvisA v hv).trans (hVis v hv).1, (hvisB v hv).trans (hVis v hv).2⟩

end

end MinCostFlow.LSF.Program
