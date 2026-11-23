module

public import MinCostFlow.MinRatio.SelectHeapInit
public import MinCostFlow.MinRatio.SelectMetaTableWrite
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.DynSpanner.Program.DynGraphRefillDefs
import WordRAM.Tactic

/-!
# Dynamic-graph copy refill and select-region skeleton allocation (`SelectRegionSkeleton`)

Provides two core Word-RAM procedures shared by Init, `ShiftTerm`, `ShiftDeep`, and `Refresh`:
1. **`dgCopyRefillBody`** (`[dst, src, scratch]`): copies any live `DynGraphAt` block `src`
   (with arbitrary capacities `(srcVCap, srcECap)`) into an existing `DynGraphAt` block `dst`
   (with capacities `(dstVCap, dstECap)`) via `dgRefillFromLists`, using `3 * G.m` scratch words
   and `O(n_old + m_old + G.n + G.m + 1)` steps.
2. **`selectRegionSkeletonBody`** (`[sb, cap, d, vCap, eCap, Lk, slot, lvlMeta, pLast, hbCell]`):
   allocates `SelectRegion sb loc B metaBase` on zeroed memory `[sb, ...)`, writes the runtime
   heap handle `sb` into `hbCell`, calls `selectHeapInit` and `selTableWrite`, and initializes
   `B.fPtr 0 .. B.fPtr d` and `B.lastGPtr` as empty dynamic graphs in strictly increasing address
   order in `O(d)` steps, leaving `ZeroFrom mem' B.endAddr` and
   `SelBlocksDataAt mem' B P emptySelBlocksData pLast`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

/-! ## 1. `dgCopyRefillBody`: copy one `DynGraphAt` block into another via `dgRefillFromLists` -/

/-- Copy the live graph stored at `src` into the existing `DynGraphAt` block at `dst`, using
`3 * m` scratch words at `scratch` and calling `refillProc` (`dgRefillFromLists`).
Arguments: `[dst, src, scratch]` (`reg 0..2`). Returns `scratch + 3 * m`. -/
def dgCopyRefillBody (refillProc : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;; -- srcVCap
  .assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;; -- srcECap
  .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;; -- n
  .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;; -- m
  .assign 7 (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 3)) ;; -- dgVListBase
  .assign 8 (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 4) (.reg 3))) ;; -- dgIntToExtBase
  .assign 9 (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 7) (.reg 3)))
    (.reg 4)) ;; -- dgEListBase
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 4))) ;; -- dgETailSlotBase
  .assign 11 (.bin .add (.reg 10) (.reg 4)) ;; -- dgEHeadSlotBase
  forRange 12 (.const 0) (.reg 6)
    (.assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 8) (.load (.bin .add (.reg 10) (.reg 13))))) ;;
     .assign 15 (.load (.bin .add (.reg 8) (.load (.bin .add (.reg 11) (.reg 13))))) ;;
     .assign 16 (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 12))) ;;
     .store (.reg 16) (.reg 13) ;;
     .store (.bin .add (.reg 16) (.const 1)) (.reg 14) ;;
     .store (.bin .add (.reg 16) (.const 2)) (.reg 15)) ;;
  .call 17 refillProc [.reg 0, .reg 5, .reg 7, .reg 6, .reg 2] ;;
  .ret (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 6)))

theorem dgCopyRefillBody_noRand (refillProc : ℕ) : (dgCopyRefillBody refillProc).NoRand := by
  simp [dgCopyRefillBody, forRange, forUp, Stmt.NoRand]

/-- Step cost bound for `dgCopyRefillBody`. -/
def dgCopyRefillCost (nOld mOld nNew mNew : ℕ) : ℕ :=
  dgRefillFromListsCost nOld mOld nNew mNew + 90 * mNew + 160

/-- Contract for `dgCopyRefillBody` (`[dst, src, scratch]`): copies `G_new` from `src` into
`dst` (replacing `G_old`), preserving all memory `< scratch` outside `dst` and keeping
`ZeroFrom` at `scratch + 3 * G_new.m`. -/
def dgCopyRefillContract (w dstVCap dstECap srcVCap srcECap : ℕ) (G_old G_new : MGraph) :
    Contract where
  pre args mem :=
    ∃ dst src scratch,
      args = [dst, src, scratch] ∧
      16 < 2 ^ w ∧
      dst + dynGraphSize dstVCap dstECap ≤ scratch ∧
      src + dynGraphSize srcVCap srcECap ≤ scratch ∧
      (src + dynGraphSize srcVCap srcECap ≤ dst ∨ dst + dynGraphSize dstVCap dstECap ≤ src) ∧
      DynGraphAt mem dst dstVCap dstECap G_old ∧
      DynGraphAt mem src srcVCap srcECap G_new ∧
      (∀ v ∈ G_new.V, v < dstVCap) ∧ (∀ e ∈ G_new.E, e < dstECap) ∧
      ZeroFrom mem scratch ∧
      scratch + 3 * G_new.m < 2 ^ w
  post args mem ret mem' :=
    let dst := args.getD 0 0
    let scratch := args.getD 2 0
    ret = scratch + 3 * G_new.m ∧
    DynGraphAt mem' dst dstVCap dstECap G_new ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < dst ∨ dst + dynGraphSize dstVCap dstECap ≤ a) → mem' a = mem a)
  cost _ _ := dgCopyRefillCost G_old.n G_old.m G_new.n G_new.m

/-! ## 2. `selectRegionSkeletonBody`: allocate `SelectRegion` on zeroed memory -/

/-- Empty model data for `SelBlocksDataAt` right after initializing the `d + 2` dynamic graph
blocks (`B.fPtr 0 .. B.fPtr d`, `B.lastGPtr`) as `dgEmptyGraph`. -/
def emptySelBlocksData : SelBlocksData where
  V := fun _ => ∅
  E := fun _ => ∅
  F := fun _ => dgEmptyGraph
  φ := fun _ _ => 0
  len := fun _ _ => 0
  coreE := fun _ => ∅
  emb := fun _ _ => []
  Gd := dgEmptyGraph
  E0 := ∅
  g := fun _ => 0

/-- Allocate and initialize the skeleton of `SelectRegion sb loc B metaBase` on zeroed memory:
stores `sb` at `hbCell` (`solverSelectHeapAddr`) and `B.base` at `hbCell + 1`
(`solverSelectBlocksAddr`), calls `selectHeapInit`, calls `selTableWrite`, and initializes
`B.fPtr 0 .. B.fPtr d` and `B.lastGPtr` as empty dynamic graphs in increasing address order.
Arguments: `[sb, cap, d, vCap, eCap, Lk, slot, lvlMeta, pLast, hbCell]` (`reg 0..9`).
Returns `B.endAddr`. -/
def selectRegionSkeletonBody (heapInitProc tableWriteProc dgInitProc : ℕ) : Stmt :=
  .assign 10 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 3)))
    (.bin .mul (.const 9) (.reg 4))) ;; -- dgSz
  .assign 11 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 10) (.bin .mul (.reg 3) (.reg 5)))
    (.bin .mul (.reg 4) (.reg 5))) (.reg 4)) (.bin .mul (.reg 4) (.reg 6))) ;; -- levelSize
  .assign 12 (.bin .add (.reg 2) (.const 1)) ;; -- d + 1
  .assign 13 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 0) (.const shHdrSize)) (.reg 12))
    (.bin .mul (.const 5) (.reg 1))) (.bin .mul (.const 2) (.bin .mul (.reg 1) (.reg 5)))) ;; -- metaBase
  .assign 14 (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 8) (.reg 12))) ;; -- B.base
  .assign 15 (.bin .add (.reg 14) (.bin .mul (.reg 12) (.reg 11))) ;; -- B.lastGPtr
  .assign 16 (.bin .add (.reg 15) (.reg 10)) ;; -- B.g0Ptr
  .assign 17 (.bin .add (.reg 16) (.bin .mul (.reg 4) (.reg 5))) ;; -- B.endAddr
  .store (.reg 9) (.reg 0) ;; -- store loc.hb = sb in runtime heap cell
  .store (.bin .add (.reg 9) (.const 1)) (.reg 14) ;; -- store B.base in runtime blocks cell
  .call 18 heapInitProc [.reg 0, .reg 1, .reg 2, .reg 5, .reg 16, .reg 13] ;;
  .call 18 tableWriteProc [.reg 13, .reg 14, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] ;;
  forRange 19 (.const 0) (.reg 12)
    (.call 18 dgInitProc
      [.bin .add (.reg 14) (.bin .mul (.reg 19) (.reg 11)),
       .reg 3, .reg 4, .const 0, .const 0, .const 0, .const 0]) ;;
  .call 18 dgInitProc [.reg 15, .reg 3, .reg 4, .const 0, .const 0, .const 0, .const 0] ;;
  .ret (.reg 17)

theorem selectRegionSkeletonBody_noRand (heapInitProc tableWriteProc dgInitProc : ℕ) :
    (selectRegionSkeletonBody heapInitProc tableWriteProc dgInitProc).NoRand := by
  simp [selectRegionSkeletonBody, forRange, forUp, Stmt.NoRand]

/-- Step cost bound for `selectRegionSkeletonBody` (`O(d)`). -/
def selectRegionSkeletonCost (d : ℕ) : ℕ :=
  400 * d + 1600

/-- Contract for `selectRegionSkeletonBody` (`[sb, cap, d, vCap, eCap, Lk, slot, lvlMeta, pLast, hbCell]`). -/
def selectRegionSkeletonContract (w P : ℕ) (sb cap d vCap eCap Lk slot lvlMeta pLast hbCell : ℕ) :
    Contract where
  pre args mem :=
    let metaBase := sb + selectHeapSize cap d Lk
    let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize d, d, vCap, eCap, Lk, slot⟩
    args = [sb, cap, d, vCap, eCap, Lk, slot, lvlMeta, pLast, hbCell] ∧
    16 < 2 ^ w ∧
    hbCell + 1 < sb ∧
    (hbCell + 1 < lvlMeta + d ∨ lvlMeta + 2 * d ≤ hbCell) ∧
    lvlMeta + 2 * d + 1 ≤ sb ∧
    pLast < 2 ^ w ∧
    ZeroFrom mem sb ∧
    B.endAddr < 2 ^ w
  post _args mem ret mem' :=
    let metaBase := sb + selectHeapSize cap d Lk
    let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize d, d, vCap, eCap, Lk, slot⟩
    let loc : SelectHeapLoc := ⟨sb, cap, d, Lk, B.g0Ptr, metaBase⟩
    ret = B.endAddr ∧
    SelectRegion sb loc B metaBase ∧
    mem' hbCell = sb ∧
    mem' (hbCell + 1) = B.base ∧
    SelectHeapAt mem' loc 4 0 ∧
    SelectMetaTableAt mem' (selTableOf B metaBase lvlMeta pLast mem) ∧
    SelBlocksDataAt mem' B P emptySelBlocksData pLast ∧
    ZeroFrom mem' B.endAddr ∧
    (∀ a < sb, a ≠ hbCell → a ≠ hbCell + 1 → mem' a = mem a)
  cost _ _ := selectRegionSkeletonCost d

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

/-! ## 3. Verification of `dgCopyRefillBody` -/

set_option maxHeartbeats 600000 in
/-- `dgCopyRefillBody` meets `dgCopyRefillContract`. -/
theorem dgCopyRefill_meetsContract {w proc refillProc dstVCap dstECap srcVCap srcECap : ℕ}
    {G_old G_new : MGraph} {p : Program}
    (hp : p.procs[proc]? = some (dgCopyRefillBody refillProc))
    (hRefill : ∀ vL eEdges,
      MeetsContract w p refillProc (dgRefillFromListsContract w dstVCap dstECap G_old G_new vL eEdges)) :
    MeetsContract w p proc (dgCopyRefillContract w dstVCap dstECap srcVCap srcECap G_old G_new) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _hwords hpre
  obtain ⟨dst, src, scratch, rfl, hw16, hdstSc, hsrcSc, hdisj, hDst, hSrc, hVCap, hECap, hz, hroom⟩ := hpre
  have hSrcSz : dynGraphSize srcVCap srcECap = 4 + 7 * srcVCap + 9 * srcECap := rfl
  have hDstSz : dynGraphSize dstVCap dstECap = 4 + 7 * dstVCap + 9 * dstECap := rfl
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨hValid, hSrcV, hSrcE, hSrcVCapM, hSrcECapM, hSrcNM, hSrcMM, _,
    ⟨vL, hvL_len, _hvL_nd, hvL_mem, hvL_at, _⟩, hE2I, _, _,
    ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩, hEnds, _⟩ := hSrc
  have hGnLe : G_new.n ≤ srcVCap := by
    unfold MGraph.n
    calc G_new.V.card ≤ (Finset.range srcVCap).card :=
          Finset.card_le_card fun v hv => Finset.mem_range.mpr (hSrcV v hv)
      _ = srcVCap := Finset.card_range _
  have hGmLe : G_new.m ≤ srcECap := by
    unfold MGraph.m
    calc G_new.E.card ≤ (Finset.range srcECap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hSrcE e he)
      _ = srcECap := Finset.card_range _
  let eEdges : List (ℕ × ℕ × ℕ) := eL.map fun e => (e, G_new.tail e, G_new.head e)
  have heEdges_len : eEdges.length = G_new.m := by simp [eEdges, heL_len]
  have hloop := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 6)
    (body := .assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
      .assign 14 (.load (.bin .add (.reg 8) (.load (.bin .add (.reg 10) (.reg 13))))) ;;
      .assign 15 (.load (.bin .add (.reg 8) (.load (.bin .add (.reg 11) (.reg 13))))) ;;
      .assign 16 (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 12))) ;;
      .store (.reg 16) (.reg 13) ;;
      .store (.bin .add (.reg 16) (.const 1)) (.reg 14) ;;
      .store (.bin .add (.reg 16) (.const 2)) (.reg 15))
    (P := fun st => st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = scratch ∧
      st.regs 3 = srcVCap ∧ st.regs 4 = srcECap ∧ st.regs 5 = G_new.n ∧ st.regs 6 = G_new.m ∧
      st.regs 7 = dgVListBase src srcVCap ∧ st.regs 8 = dgIntToExtBase src srcVCap ∧
      st.regs 9 = dgEListBase src srcVCap srcECap ∧
      st.regs 10 = dgETailSlotBase src srcVCap srcECap ∧
      st.regs 11 = dgEHeadSlotBase src srcVCap srcECap ∧ st.mem = mem)
    (Inv := fun i st => st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = scratch ∧
      st.regs 3 = srcVCap ∧ st.regs 4 = srcECap ∧ st.regs 5 = G_new.n ∧ st.regs 6 = G_new.m ∧
      st.regs 7 = dgVListBase src srcVCap ∧ st.regs 8 = dgIntToExtBase src srcVCap ∧
      st.regs 9 = dgEListBase src srcVCap srcECap ∧
      st.regs 10 = dgETailSlotBase src srcVCap srcECap ∧
      st.regs 11 = dgEHeadSlotBase src srcVCap srcECap ∧ st.regs 12 = i ∧
      (∀ k < i, ∀ (hk : k < eL.length),
        st.mem (scratch + 3 * k) = eL[k] ∧
        st.mem (scratch + 3 * k + 1) = G_new.tail eL[k] ∧
        st.mem (scratch + 3 * k + 2) = G_new.head eL[k]) ∧
      (∀ a, (a < scratch ∨ scratch + 3 * i ≤ a) → st.mem a = mem a))
    75 0 G_new.m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩ := hst
      exact ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by simp,
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => by simp [hm]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h6 := hi.2.2.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hdone, hout⟩
      have hiE : i < eL.length := by omega
      set e := eL[i]'hiE
      have heG : e ∈ G_new.E := (heL_mem e).mp (List.getElem_mem hiE)
      have heCap : e < srcECap := hSrcE e heG
      have htsEq := (hEnds e heG).1
      have hhsEq := (hEnds e heG).2
      have htSlotLt : mem (dgETailSlotBase src srcVCap srcECap + e) < srcVCap :=
        hSrcV _ (htsEq ▸ (hE2I _ (hValid e heG).1).1)
      have hhSlotLt : mem (dgEHeadSlotBase src srcVCap srcECap + e) < srcVCap :=
        hSrcV _ (hhsEq ▸ (hE2I _ (hValid e heG).2).1)
      have htVal : mem (dgIntToExtBase src srcVCap + mem (dgETailSlotBase src srcVCap srcECap + e)) =
          G_new.tail e := by rw [htsEq]; exact (hE2I _ (hValid e heG).1).2
      have hhVal : mem (dgIntToExtBase src srcVCap + mem (dgEHeadSlotBase src srcVCap srcECap + e)) =
          G_new.head e := by rw [hhsEq]; exact (hE2I _ (hValid e heG).2).2
      have heRead : st.mem (dgEListBase src srcVCap srcECap + i) = e := by
        rw [hout _ (Or.inl (by unfold dgEListBase; omega))]
        exact heL_at i hiE
      have htsRead : st.mem (dgETailSlotBase src srcVCap srcECap + e) =
          mem (dgETailSlotBase src srcVCap srcECap + e) :=
        hout _ (Or.inl (by unfold dgETailSlotBase; omega))
      have hhsRead : st.mem (dgEHeadSlotBase src srcVCap srcECap + e) =
          mem (dgEHeadSlotBase src srcVCap srcECap + e) :=
        hout _ (Or.inl (by unfold dgEHeadSlotBase; omega))
      have huRead : st.mem (dgIntToExtBase src srcVCap + mem (dgETailSlotBase src srcVCap srcECap + e)) =
          G_new.tail e := by
        rw [hout _ (Or.inl (by unfold dgIntToExtBase; omega)), htVal]
      have hvRead : st.mem (dgIntToExtBase src srcVCap + mem (dgEHeadSlotBase src srcVCap srcECap + e)) =
          G_new.head e := by
        rw [hout _ (Or.inl (by unfold dgIntToExtBase; omega)), hhVal]
      have huW : G_new.tail e < 2 ^ w := by have := hSrcV _ (hValid e heG).1; omega
      have hvW : G_new.head e < 2 ^ w := by have := hSrcV _ (hValid e heG).2; omega
      have h16W : scratch + 3 * i + 2 < 2 ^ w := by omega
      apply runs_start_le
      refine runs_seq_assign_le (v := e) (by
        simp [Expr.eval, BinOp.eval, h9, h12, heRead,
          show dgEListBase src srcVCap srcECap + i < 2 ^ w by unfold dgEListBase; omega]) ?_
      refine runs_seq_assign_le (v := G_new.tail e) (by
        simp [Expr.eval, BinOp.eval, Function.update_of_ne, h8, h10, htsRead, huRead,
          show dgETailSlotBase src srcVCap srcECap + e < 2 ^ w by unfold dgETailSlotBase; omega,
          show dgIntToExtBase src srcVCap + mem (dgETailSlotBase src srcVCap srcECap + e) < 2 ^ w by
            unfold dgIntToExtBase; omega]) ?_
      refine runs_seq_assign_le (v := G_new.head e) (by
        simp [Expr.eval, BinOp.eval, Function.update_of_ne, h8, h11, hhsRead, hvRead,
          show dgEHeadSlotBase src srcVCap srcECap + e < 2 ^ w by unfold dgEHeadSlotBase; omega,
          show dgIntToExtBase src srcVCap + mem (dgEHeadSlotBase src srcVCap srcECap + e) < 2 ^ w by
            unfold dgIntToExtBase; omega]) ?_
      refine runs_seq_assign_le (v := scratch + 3 * i) (by eval_expr) ?_
      refine runs_seq_store_le (x := scratch + 3 * i) (v := e) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := scratch + 3 * i + 1) (v := G_new.tail e)
        (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := scratch + 3 * i + 2) (v := G_new.head e)
        (by eval_expr) (by eval_expr) ?_ ?_
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
          by simpa using h8, by simpa using h9, by simpa using h10, by simpa using h11,
          by simp, fun k hk hkL => ?_, fun a ha => ?_⟩, by simp [h12]⟩
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hdone k hlt hkL
          · refine ⟨?_, ?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_self]
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · rw [Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hout a (by omega)
      · simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]; omega)
  apply runs_start_le
  dsimp only [startState]
  unfold dgCopyRefillBody
  refine runs_seq_assign_flat (v := srcVCap)
    (by simp [Expr.eval, show mem src = srcVCap from by simpa [dgVCapOff] using hSrcVCapM]) ?_
  refine runs_seq_assign_flat (v := srcECap)
    (by simp [Expr.eval, BinOp.eval, show mem (src + 1) = srcECap from by simpa [dgECapOff] using hSrcECapM,
      hw1, show src + 1 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := G_new.n)
    (by simp [Expr.eval, BinOp.eval, show mem (src + 2) = G_new.n from by simpa [dgNOff] using hSrcNM,
      show 2 < 2 ^ w by omega, show src + 2 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := G_new.m)
    (by simp [Expr.eval, BinOp.eval, show mem (src + 3) = G_new.m from by simpa [dgMOff] using hSrcMM,
      show 3 < 2 ^ w by omega, show src + 3 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := dgVListBase src srcVCap)
    (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show src + 4 < 2 ^ w by omega,
      show src + 4 + srcVCap = dgVListBase src srcVCap from rfl,
      show dgVListBase src srcVCap < 2 ^ w by unfold dgVListBase; omega]) ?_
  refine runs_seq_assign_flat (v := dgIntToExtBase src srcVCap)
    (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show src + 4 < 2 ^ w by omega,
      show 4 * srcVCap < 2 ^ w by omega,
      show src + 4 + 4 * srcVCap = dgIntToExtBase src srcVCap from rfl,
      show dgIntToExtBase src srcVCap < 2 ^ w by unfold dgIntToExtBase; omega]) ?_
  refine runs_seq_assign_flat (v := dgEListBase src srcVCap srcECap)
    (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
      show src + 4 < 2 ^ w by omega, show 7 * srcVCap < 2 ^ w by omega,
      show src + 4 + 7 * srcVCap < 2 ^ w by omega,
      show src + 4 + 7 * srcVCap + srcECap = dgEListBase src srcVCap srcECap from rfl,
      show dgEListBase src srcVCap srcECap < 2 ^ w by unfold dgEListBase; omega]) ?_
  refine runs_seq_assign_flat (v := dgETailSlotBase src srcVCap srcECap)
    (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * srcECap < 2 ^ w by omega,
      show dgEListBase src srcVCap srcECap + 2 * srcECap = dgETailSlotBase src srcVCap srcECap by
        unfold dgEListBase dgETailSlotBase; omega,
      show dgETailSlotBase src srcVCap srcECap < 2 ^ w by unfold dgETailSlotBase; omega]) ?_
  refine runs_seq_assign_flat (v := dgEHeadSlotBase src srcVCap srcECap)
    (by simp [Expr.eval, BinOp.eval,
      show dgETailSlotBase src srcVCap srcECap + srcECap = dgEHeadSlotBase src srcVCap srcECap by
        unfold dgETailSlotBase dgEHeadSlotBase; omega,
      show dgEHeadSlotBase src srcVCap srcECap < 2 ^ w by unfold dgEHeadSlotBase; omega]) ?_
  refine runs_seq_triple_le hloop ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, rfl⟩ ?_
  intro st1 ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, hdone, hout⟩
  have hDst1 : DynGraphAt st1.mem dst dstVCap dstECap G_old :=
    DynGraphAt.of_agree hDst fun a ha1 ha2 => hout a (Or.inl (by omega))
  have hvL1 : ListAt st1.mem (dgVListBase src srcVCap) vL := fun i hi => by
    rw [hout _ (Or.inl (by unfold dgVListBase; omega))]; exact hvL_at i hi
  have hRefillPre : (dgRefillFromListsContract w dstVCap dstECap G_old G_new vL eEdges).pre
      [dst, G_new.n, dgVListBase src srcVCap, G_new.m, scratch] st1.mem := by
    refine ⟨dst, G_new.n, dgVListBase src srcVCap, G_new.m, scratch, rfl, by omega, by omega,
      hDst1, hValid, hVCap, hECap, hvL_len, hvL1, hvL_mem,
      by unfold dgVListBase; omega,
      fun i hi => by unfold dgVListBase; rcases hdisj with h | h <;> [left; right] <;> omega,
      heEdges_len, by simpa [eEdges, List.map_map, Function.comp_def] using heL_nd,
      fun i hi => by simpa [eEdges] using hdone i (by omega) (by simpa [eEdges] using hi),
      fun t ht => by
        simp only [eEdges, List.mem_map] at ht
        obtain ⟨e, he, rfl⟩ := ht
        exact ⟨(heL_mem e).mp he, rfl, rfl⟩,
      fun e he => ⟨(e, G_new.tail e, G_new.head e), List.mem_map.mpr ⟨e, (heL_mem e).mpr he, rfl⟩, rfl⟩,
      by omega, fun i _ => Or.inr (by omega)⟩
  have hRefCostEq : st1.mem (dst + dgNOff) = G_old.n ∧ st1.mem (dst + dgMOff) = G_old.m :=
    ⟨hDst1.2.2.2.2.2.1, hDst1.2.2.2.2.2.2.1⟩
  refine runs_seq_call_le (hRefill vL eEdges)
    (vs := [dst, G_new.n, dgVListBase src srcVCap, G_new.m, scratch])
    (by eval_expr)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl)
      · omega
      · omega
      · unfold dgVListBase; omega
      · omega
      · omega)
    hRefillPre ?_
  intro v mem2 pos2 hpost2
  obtain ⟨_, _, _, _, _, hargs2, _, hDst2, hFr2⟩ := hpost2
  simp only [List.cons.injEq] at hargs2
  obtain ⟨rfl, -, -, -, -, -⟩ := hargs2
  refine WordRAM.runs_ret_le (v := scratch + 3 * G_new.m) (by eval_expr) ?_ ?_
  · dsimp only [dgCopyRefillContract]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    refine ⟨rfl, hDst2, fun a ha => ?_, fun a ha hnot => ?_⟩
    · change scratch + 3 * G_new.m ≤ a at ha
      rw [hFr2 a (Or.inr (by omega)), hout a (Or.inr ha)]
      exact hz a (by omega)
    · rw [hFr2 a hnot, hout a (Or.inl ha)]
  · simp only [dgCopyRefillContract, dgRefillFromListsContract, dgCopyRefillCost,
      List.getD_cons_zero, List.getD_cons_succ, hRefCostEq.1, hRefCostEq.2,
      Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil,
      Nat.sub_zero]
    omega

/-! ## 4. Verification of `selectRegionSkeletonBody` -/

private lemma dgEmptyGraph_isValid : dgEmptyGraph.IsValid := by
  intro e he; cases he

private lemma dgInitEmpty_pre {w vCap eCap gPtr : ℕ} {mem : ℕ → ℕ}
    (hw : 16 ≤ 2 ^ w) (hEnd : gPtr + dynGraphSize vCap eCap < 2 ^ w) (hz : ZeroFrom mem gPtr) :
    (dgInitFromListsContract w vCap eCap dgEmptyGraph [] []).pre
      [gPtr, vCap, eCap, 0, 0, 0, 0] mem :=
  ⟨gPtr, 0, 0, 0, 0, rfl, hw, hEnd, hz, dgEmptyGraph_isValid,
    fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _),
    rfl, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ => ⟨fun h => absurd h (List.not_mem_nil), fun h => absurd h (Finset.notMem_empty _)⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, List.nodup_nil,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

set_option maxHeartbeats 600000 in
/-- `selectRegionSkeletonBody` meets `selectRegionSkeletonContract`. -/
theorem selectRegionSkeleton_meetsContract
    {w P proc heapInitProc tableWriteProc dgInitProc : ℕ}
    {sb cap d vCap eCap Lk slot lvlMeta pLast hbCell : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selectRegionSkeletonBody heapInitProc tableWriteProc dgInitProc))
    (hHeapInit : MeetsContract w p heapInitProc (selectHeapInitContract w))
    (hTabWrite :
      let metaBase := sb + selectHeapSize cap d Lk
      let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize d, d, vCap, eCap, Lk, slot⟩
      MeetsContract w p tableWriteProc (selTableWriteContract w B metaBase lvlMeta pLast))
    (hDgInit : MeetsContract w p dgInitProc (dgInitFromListsContract w vCap eCap dgEmptyGraph [] [])) :
    MeetsContract w p proc
      (selectRegionSkeletonContract w P sb cap d vCap eCap Lk slot lvlMeta pLast hbCell) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _hwords hpre
  obtain ⟨rfl, hw16, hhbLt, hhbDisj, hlvlLe, hpLastW, hz, hEndW⟩ := hpre
  let metaBase := sb + selectHeapSize cap d Lk
  let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize d, d, vCap, eCap, Lk, slot⟩
  let loc : SelectHeapLoc := ⟨sb, cap, d, Lk, B.g0Ptr, metaBase⟩
  change B.endAddr < 2 ^ w at hEndW
  have hreg : SelectRegion sb loc B metaBase :=
    ⟨rfl, (loc.endAddr_eq).symm, rfl, rfl, rfl, rfl, rfl⟩
  have hRegEnd : B.endAddr = sb + selectRegionSize cap d vCap eCap Lk slot := hreg.endAddr_eq
  have hHeapSz : selectHeapSize cap d Lk = shHdrSize + (d + 1) + 5 * cap + 2 * (cap * Lk) := rfl
  have hMetaSz : selectLevelMetaSize d = 2 + 8 * (d + 1) := rfl
  have hDgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hLvlSz : B.levelSize =
      dynGraphSize vCap eCap + vCap * Lk + eCap * Lk + eCap + eCap * slot := rfl
  have hLastEq : B.lastGPtr = B.base + (d + 1) * B.levelSize := rfl
  have hG0Eq : B.g0Ptr = B.lastGPtr + dynGraphSize vCap eCap := rfl
  have hEndEq : B.endAddr = B.g0Ptr + eCap * Lk := rfl
  have hBaseEq : B.base = metaBase + selectLevelMetaSize d := rfl
  have hMetaDef : metaBase = sb + selectHeapSize cap d Lk := rfl
  have hRegSz : selectRegionSize cap d vCap eCap Lk slot =
      selectHeapSize cap d Lk + selectLevelMetaSize d + selectBlocksSize d vCap eCap Lk slot := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hMetaLt : metaBase < 2 ^ w := by omega
  have hBaseLt : B.base < 2 ^ w := by omega
  have hLastLt : B.lastGPtr < 2 ^ w := by omega
  have hG0Lt : B.g0Ptr < 2 ^ w := by omega
  have hCapLkLt : cap * Lk < 2 ^ w := by omega
  have hBd : B.d = d := rfl
  have hBv : B.vCap = vCap := rfl
  have hBe : B.eCap = eCap := rfl
  have hBLk : B.Lk = Lk := rfl
  have hBslot : B.slot = slot := rfl
  have hBlkLt : ∀ j ≤ d, B.fPtr j + dynGraphSize vCap eCap ≤ B.lastGPtr := fun j hj => by
    have h1 := B.blk_le_last (j := j) (by omega)
    have h2 : B.fPtr j + dynGraphSize vCap eCap ≤ B.fPtr j + B.levelSize := by omega
    omega
  let memAfterTab_loop := fun (memT : ℕ → ℕ) =>
    Triple.forRange_const (p := p) (r := 19) (lo := .const 0) (hi := .reg 12)
      (body := .call 18 dgInitProc
        [.bin .add (.reg 14) (.bin .mul (.reg 19) (.reg 11)),
         .reg 3, .reg 4, .const 0, .const 0, .const 0, .const 0])
      (P := fun st => st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 11 = B.levelSize ∧
        st.regs 12 = d + 1 ∧ st.regs 14 = B.base ∧ st.regs 15 = B.lastGPtr ∧
        st.regs 17 = B.endAddr ∧ st.mem = memT ∧ ZeroFrom memT B.base)
      (Inv := fun i st => st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 11 = B.levelSize ∧
        st.regs 12 = d + 1 ∧ st.regs 14 = B.base ∧ st.regs 15 = B.lastGPtr ∧
        st.regs 17 = B.endAddr ∧ st.regs 19 = i ∧
        (∀ j < i, DynGraphAt st.mem (B.fPtr j) vCap eCap dgEmptyGraph) ∧
        ZeroFrom st.mem (B.base + i * B.levelSize) ∧
        (∀ a < B.base, st.mem a = memT a))
      140 0 (d + 1) (Nat.zero_le _) hw1 (fun _ => by omega)
      (fun st hst => by
        obtain ⟨h3, h4, h11, h12, h14, h15, h17, hm, hzB⟩ := hst
        exact ⟨by eval_expr, h3, h4, h11, h12, h14, h15, h17, by simp,
          fun _ h => absurd h (Nat.not_lt_zero _), by simpa [hm] using hzB, fun _ _ => by simp [hm]⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h12 := hi.2.2.2.1; eval_expr)
      (fun i _ hi => by
        intro st ω' hst
        rcases hst with ⟨h3, h4, h11, h12, h14, h15, h17, h19, hFdone, hzI, hFrB⟩
        have hiD : i ≤ d := by omega
        have hfEnd : B.fPtr i + dynGraphSize vCap eCap ≤ B.fPtr i + B.levelSize := by omega
        have hfNext : B.fPtr i + B.levelSize ≤ B.lastGPtr := B.blk_le_last (j := i) (by omega)
        have hSuccEq : B.base + (i + 1) * B.levelSize = B.fPtr i + B.levelSize := by
          rw [Nat.add_mul, Nat.one_mul]; unfold SelectBlocksLoc.fPtr; omega
        apply runs_start_le
        refine runs_call_le hDgInit (vs := [B.fPtr i, vCap, eCap, 0, 0, 0, 0])
          (by
            have hmulW : i * B.levelSize < 2 ^ w := by
              have : B.base + i * B.levelSize = B.fPtr i := rfl
              omega
            simp [evalArgs, Expr.eval, BinOp.eval, h3, h4, h11, h14, h19, hmulW,
              show B.base + i * B.levelSize = B.fPtr i from rfl,
              show B.fPtr i < 2 ^ w by omega, show 0 < 2 ^ w by omega])
          (by
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
          (dgInitEmpty_pre (by omega) (by omega) hzI) ?_
        intro v mem2 pos2 hpost2
        obtain ⟨_, _, _, _, _, hargs2, _, hG2, hFr2, hz2⟩ := hpost2
        simp only [List.cons.injEq] at hargs2
        obtain ⟨rfl, -, -, -, -, -⟩ := hargs2
        refine ⟨⟨⟨by simpa using h3, by simpa using h4, by simpa using h11, by simpa using h12,
          by simpa using h14, by simpa using h15, by simpa using h17, by simp,
          fun j hj => ?_, ?_, fun a ha => ?_⟩, by simp [h19]⟩, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · have hltEnd : B.fPtr j + dynGraphSize vCap eCap ≤ B.fPtr i := by
              have hbl := B.blk_le_of_lt hlt; omega
            exact DynGraphAt.of_agree (hFdone j hlt) fun a ha1 ha2 => hFr2 a (Or.inl (by omega))
          · exact hG2
        · intro a ha
          rw [hSuccEq] at ha
          exact hz2 a (by omega)
        · exact (hFr2 a (Or.inl (by unfold SelectBlocksLoc.fPtr; omega))).trans (hFrB a ha)
        · simp only [dgInitFromListsContract, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons,
            argsSize_nil]; omega)
  apply runs_start_le
  dsimp only [startState]
  unfold selectRegionSkeletonBody
  have h10W : dynGraphSize vCap eCap < 2 ^ w := by omega
  have h11W : B.levelSize < 2 ^ w := by
    have : B.base + B.levelSize ≤ B.lastGPtr := by
      have := B.blk_le_last (Nat.zero_le d); unfold SelectBlocksLoc.fPtr at this; simpa using this
    omega
  have h12W : d + 1 < 2 ^ w := by omega
  refine runs_seq_assign_flat (v := dynGraphSize vCap eCap)
    (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
      show 9 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show 4 + 7 * vCap < 2 ^ w by omega, show 4 + 7 * vCap + 9 * eCap = dynGraphSize vCap eCap from rfl,
      h10W]) ?_
  refine runs_seq_assign_flat (v := B.levelSize)
    (by simp [Expr.eval, BinOp.eval, show vCap * Lk < 2 ^ w by omega, show eCap * Lk < 2 ^ w by omega,
      show eCap * slot < 2 ^ w by omega, show dynGraphSize vCap eCap + vCap * Lk < 2 ^ w by omega,
      show dynGraphSize vCap eCap + vCap * Lk + eCap * Lk < 2 ^ w by omega,
      show dynGraphSize vCap eCap + vCap * Lk + eCap * Lk + eCap < 2 ^ w by omega,
      show dynGraphSize vCap eCap + vCap * Lk + eCap * Lk + eCap + eCap * slot = B.levelSize from rfl,
      h11W]) ?_
  refine runs_seq_assign_flat (v := d + 1)
    (by simp [Expr.eval, BinOp.eval, hw1, h12W]) ?_
  refine runs_seq_assign_flat (v := metaBase)
    (by
      have hmbEq : sb + shHdrSize + (d + 1) + 5 * cap + 2 * (cap * Lk) = metaBase := by
        dsimp only [metaBase, selectHeapSize]; omega
      simp [Expr.eval, BinOp.eval, show shHdrSize < 2 ^ w by unfold shHdrSize; omega,
        show 5 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
        show sb + shHdrSize < 2 ^ w by omega, show sb + shHdrSize + (d + 1) < 2 ^ w by omega,
        show 5 * cap < 2 ^ w by omega, show sb + shHdrSize + (d + 1) + 5 * cap < 2 ^ w by omega,
        hCapLkLt, show 2 * (cap * Lk) < 2 ^ w by omega, hmbEq, hMetaLt]) ?_
  refine runs_seq_assign_flat (v := B.base)
    (by
      have hbaseEq : metaBase + 2 + 8 * (d + 1) = B.base := by
        dsimp only [B, selectLevelMetaSize]; omega
      simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 8 < 2 ^ w by omega,
        show metaBase + 2 < 2 ^ w by omega, show 8 * (d + 1) < 2 ^ w by omega, hbaseEq, hBaseLt]) ?_
  refine runs_seq_assign_flat (v := B.lastGPtr)
    (by simp [Expr.eval, BinOp.eval, show (d + 1) * B.levelSize < 2 ^ w by omega,
      show B.base + (d + 1) * B.levelSize = B.lastGPtr from rfl, hLastLt]) ?_
  refine runs_seq_assign_flat (v := B.g0Ptr)
    (by simp [Expr.eval, BinOp.eval, show B.lastGPtr + dynGraphSize vCap eCap = B.g0Ptr from rfl,
      hG0Lt]) ?_
  refine runs_seq_assign_flat (v := B.endAddr)
    (by simp [Expr.eval, BinOp.eval, show eCap * Lk < 2 ^ w by omega,
      show B.g0Ptr + eCap * Lk = B.endAddr from rfl, hEndW]) ?_
  refine runs_seq_store_flat (x := hbCell) (v := sb) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hbCell + 1) (v := B.base) (by eval_expr) (by eval_expr) ?_
  set mem1 := Function.update (Function.update mem hbCell sb) (hbCell + 1) B.base
  have hz1 : ZeroFrom mem1 sb := fun a ha => by
    dsimp only [mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz a ha
  refine runs_seq_call_le hHeapInit (vs := [sb, cap, d, Lk, B.g0Ptr, metaBase])
    (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl|rfl)
        · omega
        · omega
        · omega
        · exact _hwords v (by simp)
        · exact hG0Lt
        · exact hMetaLt)
    ⟨sb, cap, d, Lk, B.g0Ptr, metaBase, rfl, hw16, hz1, by omega, hG0Lt, hMetaLt⟩ ?_
  intro vH mem2 pos2 hpostH
  obtain ⟨_, hHeap2, hz2, hFr2⟩ := hpostH
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hHeap2 hz2 hFr2
  have hz2Meta : ZeroFrom mem2 metaBase := fun a ha => hz2 a (by
    dsimp only [SelectHeapLoc.endAddr, SelectHeapLoc.denBase, SelectHeapLoc.numBase,
      SelectHeapLoc.candNext, SelectHeapLoc.candPrev, SelectHeapLoc.candHead,
      SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, metaBase, selectHeapSize]
      at ha ⊢; omega)
  refine runs_seq_call_le hTabWrite (vs := [metaBase, B.base, d, vCap, eCap, Lk, slot, lvlMeta, pLast])
    (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
        · exact hMetaLt
        · exact hBaseLt
        · omega
        · omega
        · omega
        · exact _hwords v (by simp)
        · exact _hwords v (by simp)
        · omega
        · exact hpLastW)
    ⟨rfl, hw16, hEndW, by rw [hBd]; omega, by rw [hBd]; omega, Or.inl (by rw [hBd]; omega)⟩ ?_
  intro vT mem3 pos3 hpostT
  obtain ⟨_, hTab3, hFr3⟩ := hpostT
  have hz3Base : ZeroFrom mem3 B.base := fun a ha => by
    rw [hFr3 a (Or.inr (by omega))]
    exact hz2Meta a (by omega)
  refine runs_seq_triple_le (memAfterTab_loop mem3)
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, rfl, hz3Base⟩ ?_
  intro st4 ⟨h3_4, h4_4, _, _, _, h15_4, h17_4, _, hF4, hz4, hFr4⟩
  refine runs_seq_call_le hDgInit (vs := [B.lastGPtr, vCap, eCap, 0, 0, 0, 0])
    (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega)
    (dgInitEmpty_pre (by omega) (by omega) hz4) ?_
  intro vL mem5 pos5 hpost5
  obtain ⟨_, _, _, _, _, hargs5, _, hLast5, hFr5, hz5⟩ := hpost5
  simp only [List.cons.injEq] at hargs5
  obtain ⟨rfl, -, -, -, -, -⟩ := hargs5
  refine WordRAM.runs_ret_le (v := B.endAddr) (by eval_expr) ?_ ?_
  · dsimp only [selectRegionSkeletonContract]
    have hFrBelowBase : ∀ a < B.base, mem5 a = mem3 a := fun a ha =>
      (hFr5 a (Or.inl (by unfold SelectBlocksLoc.lastGPtr; omega))).trans (hFr4 a ha)
    have hFrBelowMeta : ∀ a < metaBase, mem5 a = mem2 a := fun a ha =>
      (hFrBelowBase a (by omega)).trans (hFr3 a (Or.inl ha))
    have hFrBelowSb : ∀ a < sb, mem5 a = mem1 a := fun a ha =>
      (hFrBelowMeta a (by omega)).trans (hFr2 a ha)
    have hTab5 : SelectMetaTableAt mem5 (selTableOf B metaBase lvlMeta pLast mem) := by
      have hGeq : ∀ j < B.d, mem2 (lvlMeta + B.d + j) = mem (lvlMeta + B.d + j) := fun j hj => by
        have hj' : j < d := hj
        have hne0 : lvlMeta + B.d + j ≠ hbCell := by dsimp only [B]; omega
        have hne1 : lvlMeta + B.d + j ≠ hbCell + 1 := by dsimp only [B]; omega
        rw [hFr2 (lvlMeta + B.d + j) (by dsimp only [B]; omega)]
        dsimp only [mem1]
        rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
      have hTabEq : selTableOf B metaBase lvlMeta pLast mem2 = selTableOf B metaBase lvlMeta pLast mem := by
        have h1 : (fun j => if j < B.d then mem2 (lvlMeta + B.d + j) else B.lastGPtr) =
            (fun j => if j < B.d then mem (lvlMeta + B.d + j) else B.lastGPtr) := by
          funext j; split_ifs with hj
          · exact hGeq j hj
          · rfl
        have h2 : (fun j => if j + 1 < B.d then mem2 (lvlMeta + B.d + (j + 1)) else
              if j < B.d then B.lastGPtr else pLast) =
            (fun j => if j + 1 < B.d then mem (lvlMeta + B.d + (j + 1)) else
              if j < B.d then B.lastGPtr else pLast) := by
          funext j; split_ifs with hj2
          · exact hGeq (j + 1) hj2
          · rfl
          · rfl
        unfold selTableOf selectMlocOf
        exact congrArg₂ (fun gp sp : ℕ → ℕ =>
          ({ metaBase := metaBase, d := B.d, Lk := B.Lk, g0Ptr := B.g0Ptr, GPtr := gp,
             vCap := fun _ => B.vCap, eCap := fun _ => B.eCap, phiPtr := B.phiPtr,
             coreLenPtr := B.lenPtr, embPtr := B.embPtr, fPtr := B.fPtr, sPtr := sp,
             pLast := pLast } : SelectLevelMetaLoc)) h1 h2
      rw [← hTabEq]
      exact hTab3.of_agree fun a ha1 ha2 =>
        hFrBelowBase a (by dsimp only [selTableOf, selectMlocOf] at ha2 ⊢; omega)
    change B.endAddr = B.endAddr ∧ SelectRegion sb loc B metaBase ∧ mem5 hbCell = sb ∧
      mem5 (hbCell + 1) = B.base ∧
      SelectHeapAt mem5 loc 4 0 ∧ SelectMetaTableAt mem5 (selTableOf B metaBase lvlMeta pLast mem) ∧
      SelBlocksDataAt mem5 B P emptySelBlocksData pLast ∧ ZeroFrom mem5 B.endAddr ∧
      (∀ a < sb, a ≠ hbCell → a ≠ hbCell + 1 → mem5 a = mem a)
    refine ⟨rfl, hreg, ?_, ?_, ?_, hTab5, ?_, fun a ha => hz5 a (by omega), fun a ha hne0 hne1 => ?_⟩
    · rw [hFrBelowSb hbCell (by omega)]; dsimp only [mem1]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [hFrBelowSb (hbCell + 1) hhbLt]; dsimp only [mem1]; exact Function.update_self ..
    · exact hHeap2.of_agree fun a _ ha2 => hFrBelowMeta a (by
        change a < loc.endAddr at ha2
        rw [loc.endAddr_eq] at ha2
        exact ha2)
    · refine ⟨fun j hj => ?_,
        fun _ _ => ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _)⟩,
        fun _ _ => ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _)⟩,
        fun _ _ _ h => absurd h (Finset.notMem_empty _), hLast5,
        ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _)⟩⟩
      have hltLast : B.fPtr j + dynGraphSize vCap eCap ≤ B.lastGPtr := hBlkLt j hj
      exact DynGraphAt.of_agree (hF4 j (Nat.lt_succ_of_le hj)) fun a _ ha2 =>
        hFr5 a (Or.inl (by change a < B.fPtr j + dynGraphSize vCap eCap at ha2; omega))
    · rw [hFrBelowSb a ha]; dsimp only [mem1]
      rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
  · simp only [selectRegionSkeletonContract, selectRegionSkeletonCost, selectHeapInitContract,
      selTableWriteContract, dgInitFromListsContract, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Expr.size_reg, Expr.size_const, Expr.size_bin,
      argsSize_cons, argsSize_nil, Nat.sub_zero]
    omega

end MinCostFlow.MinRatio
