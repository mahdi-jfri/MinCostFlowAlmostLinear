module

public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Part 1 of `DynGraphOps`

The first part of `DynGraphOps.lean`, split off to keep files short. See `DynGraphOps.lean` for the
overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices and bodies -/

def dgIdxInitEmpty : ℕ := 0
def dgIdxAddVertex : ℕ := 1
def dgIdxDllCons : ℕ := 2
def dgIdxDllRemove : ℕ := 3
def dgIdxGetTail : ℕ := 4
def dgIdxGetHead : ℕ := 5
def dgIdxGetDeg : ℕ := 6

/-- Initialize an empty `DynGraphAt` at `[gPtr, vCap, eCap]` assuming `ZeroFrom mem gPtr`. -/
def dgInitEmptyStmt : Stmt :=
  .store (.reg 0) (.reg 1) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 2) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.const 0) ;;
  .ret (.reg 0)

/-- Body when `v ∉ G.V` in `dgAddVertex`. Assumes `r0 = gPtr, r1 = v, r2 = vCap, r3 = dgVPresBase + v`. -/
def dgAddVertexBodyStmt : Stmt :=
  .store (.reg 3) (.const 1) ;;
  .assign 4 (.bin .add (.reg 0) (.const 2)) ;;
  .assign 5 (.load (.reg 4)) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 2)) (.reg 5)) (.reg 1) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 2) (.reg 2))) (.reg 1)) (.reg 5) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 2))) (.reg 1)) (.reg 1) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2))) (.reg 1)) (.reg 1) ;;
  .store (.reg 4) (.bin .add (.reg 5) (.const 1))

/-- Insert vertex `v` (`[gPtr, v]`) if `vPres[v] = 0`; idempotent if already present. -/
def dgAddVertexStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 1)) ;;
  .cond (.bin .eq (.load (.reg 3)) (.const 0)) dgAddVertexBodyStmt .nop ;;
  .ret (.const 0)

/-- Doubly-linked list cons (`[hePrevBase, heNextBase, headAddr, slotDegAddr, h]`). -/
def dgDllConsStmt : Stmt :=
  .assign 5 (.load (.reg 2)) ;;
  .store (.bin .add (.reg 0) (.reg 4)) (.const 0) ;;
  .store (.bin .add (.reg 1) (.reg 4)) (.reg 5) ;;
  .store (.reg 2) (.bin .add (.reg 4) (.const 1)) ;;
  .cond (.reg 5)
    (.store (.bin .add (.reg 0) (.bin .sub (.reg 5) (.const 1))) (.bin .add (.reg 4) (.const 1)))
    .nop ;;
  .store (.reg 3) (.bin .add (.load (.reg 3)) (.const 1)) ;;
  .ret (.const 0)

/-- Doubly-linked list removal (`[hePrevBase, heNextBase, headAddr, slotDegAddr, h]`). -/
def dgDllRemoveStmt : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
  .assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
  .cond (.bin .eq (.reg 5) (.const 0))
    (.store (.reg 2) (.reg 6))
    (.store (.bin .add (.reg 1) (.bin .sub (.reg 5) (.const 1))) (.reg 6)) ;;
  .cond (.reg 6)
    (.store (.bin .add (.reg 0) (.bin .sub (.reg 6) (.const 1))) (.reg 5))
    .nop ;;
  .store (.reg 3) (.bin .sub (.load (.reg 3)) (.const 1)) ;;
  .ret (.const 0)

/-- Read `G.tail e` (`[gPtr, e]`). -/
def dgGetTailStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.load (.bin .add (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) (.bin .mul (.const 3) (.reg 3))) (.reg 1))) ;;
  .ret (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2))) (.reg 4)))

/-- Read `G.head e` (`[gPtr, e]`). -/
def dgGetHeadStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.load (.bin .add (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) (.bin .mul (.const 4) (.reg 3))) (.reg 1))) ;;
  .ret (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2))) (.reg 4)))

/-- Read `G.deg v` (`[gPtr, v]`). -/
def dgGetDegStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 2))) (.reg 1))) ;;
  .ret (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 2))) (.reg 3)))

/-- Primitive dynamic-graph procedures (`0..6`). -/
def dgOpsProcs : List Stmt :=
  [ dgInitEmptyStmt
  , dgAddVertexStmt
  , dgDllConsStmt
  , dgDllRemoveStmt
  , dgGetTailStmt
  , dgGetHeadStmt
  , dgGetDegStmt ]

lemma dgOpsProcs_length : dgOpsProcs.length = 7 := rfl

lemma dgOpsProcs_noRand : ∀ s ∈ dgOpsProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts -/

/-- Contract for `dgInitEmptyStmt` (`[gPtr, vCap, eCap]`). -/
def dgInitEmptyContract (w : ℕ) : Contract where
  pre args mem := ∃ gPtr vCap eCap, args = [gPtr, vCap, eCap] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ ZeroFrom mem gPtr
  post args mem ret mem' := ∃ gPtr vCap eCap, args = [gPtr, vCap, eCap] ∧
    ret = gPtr ∧
    DynGraphAt mem' gPtr vCap eCap ⟨∅, ∅, fun _ => 0, fun _ => 0⟩ ∧
    (∀ addr, addr < gPtr ∨ gPtr + 4 ≤ addr → mem' addr = mem addr) ∧
    ZeroFrom mem' (gPtr + 4)
  cost _ _ := 40

/-- Contract for `dgAddVertexStmt` (`[gPtr, v]`) specialized to graph `G` with capacities `(vCap, eCap)`. -/
def dgAddVertexContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr v, args = [gPtr, v] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    v < vCap ∧ DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr v, args = [gPtr, v] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap { G with V := insert v G.V } ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 110

/-- Contract for `dgDllConsStmt` (`[hePrevBase, heNextBase, headAddr, slotDegAddr, h]`) specialized to `(cap, L)`. -/
def dgDllConsContract (w cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ hePrevBase heNextBase headAddr slotDegAddr h,
    args = [hePrevBase, heNextBase, headAddr, slotDegAddr, h] ∧
    16 ≤ 2 ^ w ∧
    hePrevBase + cap < 2 ^ w ∧ heNextBase + cap < 2 ^ w ∧
    headAddr < 2 ^ w ∧ slotDegAddr < 2 ^ w ∧
    IsDoublyLinkedList mem hePrevBase heNextBase headAddr cap L ∧
    h < cap ∧ h ∉ L ∧ mem slotDegAddr + 1 < 2 ^ w ∧
    headAddr ≠ slotDegAddr ∧
    (∀ x < cap, hePrevBase + x ≠ headAddr ∧ hePrevBase + x ≠ slotDegAddr) ∧
    (∀ x < cap, heNextBase + x ≠ headAddr ∧ heNextBase + x ≠ slotDegAddr) ∧
    (∀ x y, hePrevBase + x = heNextBase + y → x < cap → y < cap → False)
  post args mem ret mem' := ∃ hePrevBase heNextBase headAddr slotDegAddr h,
    args = [hePrevBase, heNextBase, headAddr, slotDegAddr, h] ∧ ret = 0 ∧
    IsDoublyLinkedList mem' hePrevBase heNextBase headAddr cap (h :: L) ∧
    mem' slotDegAddr = mem slotDegAddr + 1 ∧
    ∀ addr, (∀ x, addr = hePrevBase + x → x ∉ h :: L) →
      (∀ x, addr = heNextBase + x → x ∉ h :: L) →
      addr ≠ headAddr → addr ≠ slotDegAddr → mem' addr = mem addr
  cost _ _ := 70

/-- Contract for `dgDllRemoveStmt` (`[hePrevBase, heNextBase, headAddr, slotDegAddr, h]`) specialized to `(cap, L)`. -/
def dgDllRemoveContract (w cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ hePrevBase heNextBase headAddr slotDegAddr h,
    args = [hePrevBase, heNextBase, headAddr, slotDegAddr, h] ∧
    16 ≤ 2 ^ w ∧
    hePrevBase + cap < 2 ^ w ∧ heNextBase + cap < 2 ^ w ∧
    headAddr < 2 ^ w ∧ slotDegAddr < 2 ^ w ∧
    IsDoublyLinkedList mem hePrevBase heNextBase headAddr cap L ∧
    h ∈ L ∧ mem slotDegAddr < 2 ^ w ∧
    headAddr ≠ slotDegAddr ∧
    (∀ x < cap, hePrevBase + x ≠ headAddr ∧ hePrevBase + x ≠ slotDegAddr) ∧
    (∀ x < cap, heNextBase + x ≠ headAddr ∧ heNextBase + x ≠ slotDegAddr) ∧
    (∀ x y, hePrevBase + x = heNextBase + y → x < cap → y < cap → False)
  post args mem ret mem' := ∃ hePrevBase heNextBase headAddr slotDegAddr h,
    args = [hePrevBase, heNextBase, headAddr, slotDegAddr, h] ∧ ret = 0 ∧
    IsDoublyLinkedList mem' hePrevBase heNextBase headAddr cap (L.erase h) ∧
    mem' slotDegAddr = mem slotDegAddr - 1 ∧
    ∀ addr, (∀ x, addr = hePrevBase + x → x ∉ L) →
      (∀ x, addr = heNextBase + x → x ∉ L) →
      addr ≠ headAddr → addr ≠ slotDegAddr → mem' addr = mem addr
  cost _ _ := 75

/-- Contract for `dgGetTailStmt` (`[gPtr, e]`) specialized to `(vCap, eCap, G)`. -/
def dgGetTailContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr e, args = [gPtr, e] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    e ∈ G.E ∧ DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr e, args = [gPtr, e] ∧ mem' = mem ∧ ret = G.tail e
  cost _ _ := 45

/-- Contract for `dgGetHeadStmt` (`[gPtr, e]`) specialized to `(vCap, eCap, G)`. -/
def dgGetHeadContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr e, args = [gPtr, e] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    e ∈ G.E ∧ DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr e, args = [gPtr, e] ∧ mem' = mem ∧ ret = G.head e
  cost _ _ := 45

/-- Contract for `dgGetDegStmt` (`[gPtr, v]`) specialized to `(vCap, eCap, G)`. -/
def dgGetDegContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr v, args = [gPtr, v] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    v ∈ G.V ∧ DynGraphAt mem gPtr vCap eCap G
  post args mem ret mem' := ∃ gPtr v, args = [gPtr, v] ∧ mem' = mem ∧ ret = G.deg v
  cost _ _ := 40

end

/-! ## Verification proofs -/

public section

theorem dgInitEmpty_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxInitEmpty) (dgInitEmptyContract w) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxInitEmpty) (by simp [dgOpsProcs, dgIdxInitEmpty]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, vCap, eCap, rfl, hw16, hbound, hzero⟩
  have hlt_gp : gPtr < 2 ^ w := by dsimp [dynGraphSize] at hbound; omega
  have hlt_vc : vCap < 2 ^ w := by dsimp [dynGraphSize] at hbound; omega
  have hlt_ec : eCap < 2 ^ w := by dsimp [dynGraphSize] at hbound; omega
  have hlt_3 : gPtr + 3 < 2 ^ w := by dsimp [dynGraphSize] at hbound; omega
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxInitEmpty, List.getElem_cons_zero, dgInitEmptyStmt]
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (by eval_expr) ⟨gPtr, vCap, eCap, rfl, rfl, ?_, ?_, ?_⟩ ?_
  · dsimp only [startState]
    refine ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [dgVCapOff]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Nat.add_zero, Function.update_self]
    · dsimp only [dgECapOff]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · dsimp only [dgNOff]; rw [Function.update_of_ne (by omega), Function.update_self]; simp [MGraph.n]
    · dsimp only [dgMOff]; rw [Function.update_self]; simp [MGraph.m]
    · intro v hv
      simp only [Finset.notMem_empty, ↓reduceIte, dgVPresBase]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzero _ (by omega)
    · exact ⟨[], by simp [MGraph.n], List.nodup_nil, fun _ => by simp, fun i hi => by simp at hi, fun i hi => by simp at hi⟩
    · intro _ h; cases h
    · intro _ h; cases h
    · intro e he
      simp only [Finset.notMem_empty, ↓reduceIte, dgEPresBase]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzero _ (by omega)
    · exact ⟨[], by simp [MGraph.m], List.nodup_nil, fun _ => by simp, fun i hi => by simp at hi, fun i hi => by simp at hi⟩
    · intro _ h; cases h
    · refine ⟨fun _ => [], fun s hs => ?_⟩
      have hhead0 : (Function.update (Function.update (Function.update (Function.update mem gPtr vCap)
          (gPtr + 1) eCap) (gPtr + 2) 0) (gPtr + 3) 0) (dgIncHeadBase gPtr vCap + s) = 0 := by
        dsimp only [dgIncHeadBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hzero _ (by omega)
      have hdeg0 : (Function.update (Function.update (Function.update (Function.update mem gPtr vCap)
          (gPtr + 1) eCap) (gPtr + 2) 0) (gPtr + 3) 0) (dgSlotDegBase gPtr vCap + s) = 0 := by
        dsimp only [dgSlotDegBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hzero _ (by omega)
      exact ⟨IsDoublyLinkedList.nil hhead0, hdeg0, fun h => by simp⟩
  · intro addr haddr
    dsimp only [startState]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro addr haddr
    dsimp only [startState]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hzero addr (by omega)
  · simp [dgInitEmptyContract]

theorem dgDllCons_meetsContract {w : ℕ} {p : Program} {b cap : ℕ} {L : List ℕ}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxDllCons) (dgDllConsContract w cap L) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxDllCons) (by simp [dgOpsProcs, dgIdxDllCons]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨hePrevBase, heNextBase, headAddr, slotDegAddr, h, rfl,
    hw16, hpb, hnb, hhd_ltw, hdeg_ltw, hdll, hh_lt, hh_not, hdeg_lt, hdisj_hd, hdisj_ph, hdisj_nh, hdisj_pn⟩
  have hprev_lt : mem headAddr < 2 ^ w := by
    cases L with
    | nil =>
      have hh0 : mem headAddr = 0 := by simpa using hdll.2.2.1
      omega
    | cons h₀ xs =>
      have hh0 : mem headAddr = h₀ + 1 := by simpa using hdll.2.2.1
      have := hdll.2.1 h₀ List.mem_cons_self
      omega
  have hlt_cap : ∀ x ∈ L, x < cap := hdll.2.1
  have hheP_lt : hePrevBase + h < 2 ^ w := by omega
  have hheN_lt : heNextBase + h < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxDllCons, List.getElem_cons_succ, List.getElem_cons_zero, dgDllConsStmt]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_cond_le (by eval_expr) ?_ ?_
  · intro hne
    have hLcons : ∃ h₀ xs, L = h₀ :: xs ∧ mem headAddr = h₀ + 1 := by
      cases L with
      | nil => exact absurd (by simpa using hdll.2.2.1) hne
      | cons h₀ xs => exact ⟨h₀, xs, rfl, by simpa using hdll.2.2.1⟩
    rcases hLcons with ⟨h₀, xs, rfl, hhd_eq⟩
    have hh₀_lt : h₀ < cap := hlt_cap h₀ List.mem_cons_self
    have hh₀_ltw : hePrevBase + (mem headAddr - 1) < 2 ^ w := by rw [hhd_eq]; omega
    refine runs_seq_triple_le
      (P := fun st => st.regs 0 = hePrevBase ∧ st.regs 1 = heNextBase ∧
        st.regs 2 = headAddr ∧ st.regs 3 = slotDegAddr ∧ st.regs 4 = h ∧ st.regs 5 = mem headAddr ∧
        st.mem = Function.update (Function.update (Function.update mem (hePrevBase + h) 0)
          (heNextBase + h) (mem headAddr)) headAddr (h + 1))
      (s₁ := .store (.bin .add (.reg 0) (.bin .sub (.reg 5) (.const 1))) (.bin .add (.reg 4) (.const 1)))
      (Q₁ := fun st => st.regs 0 = hePrevBase ∧ st.regs 1 = heNextBase ∧
        st.regs 2 = headAddr ∧ st.regs 3 = slotDegAddr ∧ st.regs 4 = h ∧ st.regs 5 = mem headAddr ∧
        st.mem = Function.update (Function.update (Function.update (Function.update mem (hePrevBase + h) 0)
          (heNextBase + h) (mem headAddr)) headAddr (h + 1)) (hePrevBase + (mem headAddr - 1)) (h + 1))
      (T₁ := fun _ => 12) ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
    · intro st _ ⟨hr0, hr1, hr2, hr3, hr4, hr5, hmem_eq⟩
      refine ⟨.normal, { st with mem := Function.update st.mem (hePrevBase + (mem headAddr - 1)) (h + 1) },
        _, runs_store_iff.mpr ⟨_, _, by eval_expr, by eval_expr, rfl, rfl, rfl⟩,
        ⟨hr0, hr1, hr2, hr3, hr4, hr5, by rw [hmem_eq]⟩, by simp⟩
    · rintro st₁ ⟨hr0, hr1, hr2, hr3, hr4, hr5, hmem_eq⟩
      have hm_deg : st₁.mem slotDegAddr = mem slotDegAddr := by
        rw [hmem_eq, Function.update_of_ne (by rw [hhd_eq]; exact (hdisj_ph h₀ hh₀_lt).2.symm),
            Function.update_of_ne hdisj_hd.symm,
            Function.update_of_ne (hdisj_nh h hh_lt).2.symm,
            Function.update_of_ne (hdisj_ph h hh_lt).2.symm]
      refine runs_seq_store_le (Expr.eval_reg_of_eq hr3)
        (Expr.eval_add (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr3) hm_deg)
          (Expr.eval_const (by omega)) hdeg_lt) ?_
      refine runs_ret_le (by eval_expr)
        ⟨hePrevBase, heNextBase, headAddr, slotDegAddr, h, rfl, rfl, ?_, ?_, ?_⟩
        (by dsimp [dgDllConsContract]; omega)
      · dsimp only
        refine hdll.cons hh_lt hh_not ?_ ?_ ?_ ?_ ?_ ?_
        · rw [Function.update_of_ne hdisj_hd, hmem_eq,
              Function.update_of_ne (by rw [hhd_eq]; exact (hdisj_ph h₀ hh₀_lt).1.symm),
              Function.update_self]
        · have hne_hh0 : h ≠ h₀ := fun hEq => hh_not (hEq ▸ List.mem_cons_self)
          rw [Function.update_of_ne (hdisj_ph h hh_lt).2, hmem_eq,
              Function.update_of_ne (by rw [hhd_eq]; intro e; apply hne_hh0; omega),
              Function.update_of_ne (hdisj_ph h hh_lt).1,
              Function.update_of_ne (fun e => hdisj_pn h h e hh_lt hh_lt),
              Function.update_self]
        · rw [Function.update_of_ne (hdisj_nh h hh_lt).2, hmem_eq,
              Function.update_of_ne (fun e => hdisj_pn (mem headAddr - 1) h e.symm (by rw [hhd_eq]; exact hh₀_lt) hh_lt),
              Function.update_of_ne (hdisj_nh h hh_lt).1,
              Function.update_self]
        · intro h₁ ys hEq
          rcases List.cons.inj hEq with ⟨rfl, rfl⟩
          rw [Function.update_of_ne (hdisj_ph h₀ hh₀_lt).2, hmem_eq,
              show hePrevBase + (mem headAddr - 1) = hePrevBase + h₀ by rw [hhd_eq]; simp,
              Function.update_self]
        · intro y hy hnothead
          have hy_lt := hlt_cap y hy
          have hne_yh0 : y ≠ h₀ := fun hEq => by subst hEq; exact hnothead xs rfl
          have hne_yh : y ≠ h := fun hEq => hh_not (hEq ▸ hy)
          rw [Function.update_of_ne (hdisj_ph y hy_lt).2, hmem_eq,
              Function.update_of_ne (by rw [hhd_eq]; intro e; exact hne_yh0 (by omega)),
              Function.update_of_ne (hdisj_ph y hy_lt).1,
              Function.update_of_ne (fun e => hdisj_pn y h e hy_lt hh_lt),
              Function.update_of_ne (by omega)]
        · intro y hy
          have hy_lt := hlt_cap y hy
          have hne_yh : y ≠ h := fun hEq => hh_not (hEq ▸ hy)
          rw [Function.update_of_ne (hdisj_nh y hy_lt).2, hmem_eq,
              Function.update_of_ne (fun e => hdisj_pn (mem headAddr - 1) y e.symm (by rw [hhd_eq]; exact hh₀_lt) hy_lt),
              Function.update_of_ne (hdisj_nh y hy_lt).1,
              Function.update_of_ne (by omega),
              Function.update_of_ne (fun e => hdisj_pn h y e.symm hh_lt hy_lt)]
      · dsimp only; rw [Function.update_self]
      · intro addr hp_f hn_f ha1 ha2
        dsimp only
        rw [Function.update_of_ne ha2, hmem_eq,
            Function.update_of_ne (fun e => hp_f h₀ (by simpa [hhd_eq] using e) (List.mem_cons_of_mem h List.mem_cons_self)),
            Function.update_of_ne ha1,
            Function.update_of_ne (fun e => hn_f h e List.mem_cons_self),
            Function.update_of_ne (fun e => hp_f h e List.mem_cons_self)]
  · intro heq0
    have hLnil : L = [] := hdll.head_eq_zero_iff.mp heq0
    subst hLnil
    refine runs_seq_nop_le ?_
    dsimp only [startState]
    set mem1 := Function.update (Function.update (Function.update mem (hePrevBase + h) 0)
      (heNextBase + h) (mem headAddr)) headAddr (h + 1)
    have hm_deg : mem1 slotDegAddr = mem slotDegAddr := by
      simp only [mem1]
      rw [Function.update_of_ne hdisj_hd.symm,
          Function.update_of_ne (hdisj_nh h hh_lt).2.symm,
          Function.update_of_ne (hdisj_ph h hh_lt).2.symm]
    refine runs_seq_store_le (by eval_expr)
      (Expr.eval_add (Expr.eval_load_of_eq (by eval_expr) hm_deg) (Expr.eval_const (by omega)) hdeg_lt) ?_
    refine runs_ret_le (by eval_expr)
      ⟨hePrevBase, heNextBase, headAddr, slotDegAddr, h, rfl, rfl, ?_, ?_, ?_⟩
      (by dsimp [dgDllConsContract]; omega)
    · dsimp only
      refine hdll.cons hh_lt hh_not ?_ ?_ ?_ (fun _ _ hEq => by cases hEq)
        (fun _ hy => by cases hy) (fun _ hy => by cases hy)
      · rw [Function.update_of_ne hdisj_hd]; simp [mem1]
      · rw [Function.update_of_ne (hdisj_ph h hh_lt).2]
        simp only [mem1]
        rw [Function.update_of_ne (hdisj_ph h hh_lt).1,
            Function.update_of_ne (fun e => hdisj_pn h h e hh_lt hh_lt),
            Function.update_self]
      · rw [Function.update_of_ne (hdisj_nh h hh_lt).2]
        simp only [mem1]
        rw [Function.update_of_ne (hdisj_nh h hh_lt).1, Function.update_self]
    · dsimp only; rw [Function.update_self]
    · intro addr hp_f hn_f ha1 ha2
      dsimp only
      rw [Function.update_of_ne ha2]
      simp only [mem1]
      rw [Function.update_of_ne ha1,
          Function.update_of_ne (fun e => hn_f h e List.mem_cons_self),
          Function.update_of_ne (fun e => hp_f h e List.mem_cons_self)]

private lemma dgDllRemoveStep1_triple {w : ℕ} {p : Program}
    {hePrevBase heNextBase headAddr slotDegAddr h pVal qVal : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (_hhd_lt : headAddr < 2 ^ w)
    (hp_bound : pVal ≠ 0 → heNextBase + (pVal - 1) < 2 ^ w)
    (hp_lt : pVal < 2 ^ w) (_hq_lt : qVal < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = hePrevBase ∧ st.regs 1 = heNextBase ∧ st.regs 2 = headAddr ∧
        st.regs 3 = slotDegAddr ∧ st.regs 4 = h ∧ st.regs 5 = pVal ∧ st.regs 6 = qVal ∧
        st.mem = mem₀)
      (.cond (.bin .eq (.reg 5) (.const 0))
        (.store (.reg 2) (.reg 6))
        (.store (.bin .add (.reg 1) (.bin .sub (.reg 5) (.const 1))) (.reg 6)))
      (normalPost fun st => st.regs 0 = hePrevBase ∧ st.regs 1 = heNextBase ∧
        st.regs 2 = headAddr ∧ st.regs 3 = slotDegAddr ∧ st.regs 4 = h ∧ st.regs 5 = pVal ∧
        st.regs 6 = qVal ∧
        st.mem = (if pVal = 0 then Function.update mem₀ headAddr qVal
                  else Function.update mem₀ (heNextBase + (pVal - 1)) qVal))
      (fun _ => 20) := by
  intro st _ ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmem⟩
  rcases st with ⟨st_m, st_r, st_p⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hmem
  rw [hmem] at *
  by_cases hp0 : pVal = 0
  · refine ⟨.normal, { mem := Function.update mem₀ headAddr qVal, regs := st_r, pos := st_p },
      _, runs_cond_iff.mpr ⟨1, _, ?_, runs_store_iff.mpr ⟨headAddr, qVal, by eval_expr, by eval_expr, rfl, rfl, rfl⟩, rfl⟩,
      ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp [hp0]⟩, by simp⟩
    have hcond : (Expr.bin .eq (.reg 5) (.const 0)).eval w { mem := mem₀, regs := st_r, pos := st_p } =
        some (if pVal = 0 then 1 else 0) := by eval_expr
    simpa [hp0] using hcond
  · have hp_b := hp_bound hp0
    refine ⟨.normal, { mem := Function.update mem₀ (heNextBase + (pVal - 1)) qVal, regs := st_r, pos := st_p },
      _, runs_cond_iff.mpr ⟨0, _, ?_, runs_store_iff.mpr ⟨_, qVal, by eval_expr, by eval_expr, rfl, rfl, rfl⟩, rfl⟩,
      ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp [hp0]⟩, by simp⟩
    have hcond : (Expr.bin .eq (.reg 5) (.const 0)).eval w { mem := mem₀, regs := st_r, pos := st_p } =
        some (if pVal = 0 then 1 else 0) := by eval_expr
    simpa [hp0] using hcond

private lemma dgDllRemoveStep2_triple {w : ℕ} {p : Program}
    {hePrevBase heNextBase headAddr slotDegAddr h pVal qVal : ℕ} {mem₁ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hq_bound : qVal ≠ 0 → hePrevBase + (qVal - 1) < 2 ^ w)
    (_hp_lt : pVal < 2 ^ w) (hq_lt : qVal < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = hePrevBase ∧ st.regs 1 = heNextBase ∧ st.regs 2 = headAddr ∧
        st.regs 3 = slotDegAddr ∧ st.regs 4 = h ∧ st.regs 5 = pVal ∧ st.regs 6 = qVal ∧
        st.mem = mem₁)
      (.cond (.reg 6)
        (.store (.bin .add (.reg 0) (.bin .sub (.reg 6) (.const 1))) (.reg 5))
        .nop)
      (normalPost fun st => st.regs 0 = hePrevBase ∧ st.regs 1 = heNextBase ∧
        st.regs 2 = headAddr ∧ st.regs 3 = slotDegAddr ∧ st.regs 4 = h ∧ st.regs 5 = pVal ∧
        st.regs 6 = qVal ∧
        st.mem = (if qVal = 0 then mem₁ else Function.update mem₁ (hePrevBase + (qVal - 1)) pVal))
      (fun _ => 15) := by
  intro st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmem⟩
  rcases st with ⟨st_m, st_r, st_p⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hmem
  rw [hmem] at *
  by_cases hq0 : qVal = 0
  · refine ⟨.normal, { mem := mem₁, regs := st_r, pos := st_p }, _,
      runs_cond_iff.mpr ⟨0, _, by eval_expr, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
      ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp [hq0]⟩, by simp⟩
  · have hq_b := hq_bound hq0
    have hstore : Runs w p ω
        (Stmt.store (.bin .add (.reg 0) (.bin .sub (.reg 6) (.const 1))) (.reg 5))
        { mem := mem₁, regs := st_r, pos := st_p } .normal
        { mem := Function.update mem₁ (hePrevBase + (qVal - 1)) pVal, regs := st_r, pos := st_p }
        ((Expr.bin .add (.reg 0) (.bin .sub (.reg 6) (.const 1))).size + (Expr.reg 5).size + 1) :=
      runs_store_iff.mpr
        ⟨hePrevBase + (qVal - 1), pVal, by eval_expr, by eval_expr, rfl, rfl, rfl⟩
    refine ⟨.normal, { mem := Function.update mem₁ (hePrevBase + (qVal - 1)) pVal, regs := st_r, pos := st_p },
      _, runs_cond_iff.mpr ⟨qVal, _, by eval_expr, by simpa [hq0] using hstore, rfl⟩,
      ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp [hq0]⟩, by simp [Expr.size]⟩

theorem dgDllRemove_meetsContract {w : ℕ} {p : Program} {b cap : ℕ} {L : List ℕ}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxDllRemove) (dgDllRemoveContract w cap L) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxDllRemove) (by simp [dgOpsProcs, dgIdxDllRemove]))
    fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨hePrevBase, heNextBase, headAddr, slotDegAddr, h, rfl,
    hw16, hpb, hnb, hhd_ltw, hdeg_ltw, hdll, hh_mem, hdeg_lt, hdisj_hd, hdisj_ph, hdisj_nh, hdisj_pn⟩
  obtain ⟨k, hk, hLk⟩ := List.getElem_of_mem hh_mem
  have hbody_k := hdll.2.2.2 k hk
  rw [hLk] at hbody_k
  set pVal := mem (hePrevBase + h)
  set qVal := mem (heNextBase + h)
  have hh_lt : h < cap := hdll.2.1 h hh_mem
  have hp_ltw : pVal < 2 ^ w := by
    rw [hbody_k.1]
    split_ifs with hk0
    · omega
    · have := hdll.2.1 (L[k - 1]) (List.getElem_mem (by omega)); omega
  have hq_ltw : qVal < 2 ^ w := by
    rw [hbody_k.2]
    split_ifs with hk1
    · omega
    · have : k + 1 < L.length := by omega
      have hmem1 : L.getD (k + 1) 0 ∈ L := by rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this
      have := hdll.2.1 _ hmem1; omega
  have hp_bound : pVal ≠ 0 → heNextBase + (pVal - 1) < 2 ^ w := by
    intro hp0
    rw [hbody_k.1] at hp0 ⊢
    split_ifs at hp0 ⊢ with hk0
    · exact False.elim (hp0 rfl)
    · have := hdll.2.1 (L[k - 1]) (List.getElem_mem (by omega))
      simp only [Nat.add_sub_cancel]; omega
  have hq_bound : qVal ≠ 0 → hePrevBase + (qVal - 1) < 2 ^ w := by
    intro hq0
    rw [hbody_k.2] at hq0 ⊢
    split_ifs at hq0 ⊢ with hk1
    · exact False.elim (hq0 rfl)
    · have : k + 1 < L.length := by omega
      have hmem1 : L.getD (k + 1) 0 ∈ L := by rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this
      have := hdll.2.1 _ hmem1
      simp only [Nat.add_sub_cancel]; omega
  have hheP_lt : hePrevBase + h < 2 ^ w := by omega
  have hheN_lt : heNextBase + h < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dgOpsProcs, dgIdxDllRemove, List.getElem_cons_succ, List.getElem_cons_zero, dgDllRemoveStmt]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  dsimp only [startState]
  set mem1 := if pVal = 0 then Function.update mem headAddr qVal
              else Function.update mem (heNextBase + (pVal - 1)) qVal
  refine runs_seq_triple_le
    (dgDllRemoveStep1_triple (hePrevBase := hePrevBase) (heNextBase := heNextBase)
      (headAddr := headAddr) (slotDegAddr := slotDegAddr) (h := h) (mem₀ := mem)
      hw16 hhd_ltw hp_bound hp_ltw hq_ltw)
    ⟨by simp, by simp, by simp, by simp, by simp, rfl, rfl, rfl⟩ ?_
  rintro st₁ ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmem1⟩
  set mem2 := if qVal = 0 then mem1 else Function.update mem1 (hePrevBase + (qVal - 1)) pVal
  refine runs_seq_triple_le
    (dgDllRemoveStep2_triple (hePrevBase := hePrevBase) (heNextBase := heNextBase)
      (headAddr := headAddr) (slotDegAddr := slotDegAddr) (h := h) (mem₁ := mem1)
      hw16 hq_bound hp_ltw hq_ltw)
    ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmem1⟩ ?_
  rintro st₂ ⟨hr0', hr1', hr2', hr3', hr4', hr5', hr6', hmem2⟩
  change st₂.mem = mem2 at hmem2
  have hdeg_eq2 : st₂.mem slotDegAddr = mem slotDegAddr := by
    have hm1_deg : mem1 slotDegAddr = mem slotDegAddr := by
      dsimp only [mem1]
      split_ifs with hp0
      · rw [Function.update_of_ne hdisj_hd.symm]
      · rw [hbody_k.1] at hp0 ⊢
        have hk0 : k ≠ 0 := fun hc => by simp [hc] at hp0
        have hlt_p := hdll.2.1 (L[k - 1]) (List.getElem_mem (by omega))
        simp only [hk0, ↓reduceIte, Nat.add_sub_cancel]
        rw [Function.update_of_ne (hdisj_nh _ hlt_p).2.symm]
    have hm2_deg : mem2 slotDegAddr = mem1 slotDegAddr := by
      dsimp only [mem2]
      split_ifs with hq0
      · rfl
      · rw [hbody_k.2] at hq0 ⊢
        have hk1 : k + 1 ≠ L.length := fun hc => by simp [hc] at hq0
        have hmem1' : L.getD (k + 1) 0 ∈ L := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
        have hlt_q := hdll.2.1 _ hmem1'
        simp only [hk1, ↓reduceIte, Nat.add_sub_cancel]
        exact Function.update_of_ne (hdisj_ph _ hlt_q).2.symm _ mem1
    rw [hmem2, hm2_deg, hm1_deg]
  have hst2_deg_lt : st₂.mem slotDegAddr < 2 ^ w := by rw [hdeg_eq2]; exact hdeg_lt
  refine runs_seq_store_le (Expr.eval_reg_of_eq hr3')
    (Expr.eval_sub (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr3') hdeg_eq2)
      (Expr.eval_const (by omega)) hdeg_lt) ?_
  refine runs_ret_le (by eval_expr)
    ⟨hePrevBase, heNextBase, headAddr, slotDegAddr, h, rfl, rfl, ?_, ?_, ?_⟩
    (by dsimp [dgDllRemoveContract]; omega)
  · dsimp only
    set mem3 := Function.update st₂.mem slotDegAddr (mem slotDegAddr - 1)
    have hmem3_head : mem3 headAddr = if pVal = 0 then qVal else mem headAddr := by
      have hm2_hd : mem2 headAddr = mem1 headAddr := by
        dsimp only [mem2]; split_ifs with hq0
        · rfl
        · rw [hbody_k.2] at hq0 ⊢
          have hk1 : k + 1 ≠ L.length := fun hc => by simp [hc] at hq0
          have hlt_y : L.getD (k + 1) 0 < cap := by
            rw [List.getD_eq_getElem _ _ (by omega)]; exact hdll.2.1 _ (List.getElem_mem _)
          simp only [hk1, ↓reduceIte, Nat.add_sub_cancel]
          rw [Function.update_of_ne (hdisj_ph _ hlt_y).1.symm]
      rw [show mem3 headAddr = st₂.mem headAddr from Function.update_of_ne hdisj_hd _ st₂.mem,
          hmem2, hm2_hd]
      dsimp only [mem1]; split_ifs with hp0
      · simp [Function.update_self]
      · rw [hbody_k.1] at hp0 ⊢
        have hk0 : k ≠ 0 := fun hc => by simp [hc] at hp0
        have hlt_y : L[k - 1] < cap := hdll.2.1 _ (List.getElem_mem (by omega))
        simp only [hk0, ↓reduceIte, Nat.add_sub_cancel]
        rw [Function.update_of_ne (hdisj_nh _ hlt_y).1.symm]
    have hp_prev : ∀ y < cap, y ≠ (if k + 1 = L.length then cap else L.getD (k + 1) 0) →
        mem3 (hePrevBase + y) = mem (hePrevBase + y) := by
      intro y hy hne_y
      rw [show mem3 (hePrevBase + y) = st₂.mem (hePrevBase + y) from
            Function.update_of_ne (hdisj_ph y hy).2 _ st₂.mem, hmem2]
      have hm2 : mem2 (hePrevBase + y) = mem1 (hePrevBase + y) := by
        dsimp only [mem2]; split_ifs with hq0
        · rfl
        · rw [hbody_k.2] at hq0 ⊢
          have hk1 : k + 1 ≠ L.length := fun hc => by simp [hc] at hq0
          simp only [hk1, ↓reduceIte] at hne_y ⊢
          rw [Function.update_of_ne (by omega)]
      rw [hm2]
      dsimp only [mem1]; split_ifs with hp0
      · rw [Function.update_of_ne (hdisj_ph y hy).1]
      · rw [hbody_k.1] at hp0 ⊢
        have hk0 : k ≠ 0 := fun hc => by simp [hc] at hp0
        have hlt_p : L[k - 1] < cap := hdll.2.1 _ (List.getElem_mem (by omega))
        simp only [hk0, ↓reduceIte, Nat.add_sub_cancel]
        rw [Function.update_of_ne (fun e => hdisj_pn y _ e hy hlt_p)]
    have hp_next : ∀ y < cap, y ≠ (if k = 0 then cap else L[k - 1]'(by omega)) →
        mem3 (heNextBase + y) = mem (heNextBase + y) := by
      intro y hy hne_y
      rw [show mem3 (heNextBase + y) = st₂.mem (heNextBase + y) from
            Function.update_of_ne (hdisj_nh y hy).2 _ st₂.mem, hmem2]
      have hm2 : mem2 (heNextBase + y) = mem1 (heNextBase + y) := by
        dsimp only [mem2]; split_ifs with hq0
        · rfl
        · rw [hbody_k.2] at hq0 ⊢
          have hk1 : k + 1 ≠ L.length := fun hc => by simp [hc] at hq0
          have hlt_q : L.getD (k + 1) 0 < cap := by
            rw [List.getD_eq_getElem _ _ (by omega)]; exact hdll.2.1 _ (List.getElem_mem _)
          simp only [hk1, ↓reduceIte, Nat.add_sub_cancel]
          rw [Function.update_of_ne (fun e => hdisj_pn _ y e.symm hlt_q hy)]
      rw [hm2]
      dsimp only [mem1]; split_ifs with hp0
      · rw [Function.update_of_ne (hdisj_nh y hy).1]
      · rw [hbody_k.1] at hp0 ⊢
        have hk0 : k ≠ 0 := fun hc => by simp [hc] at hp0
        simp only [hk0, ↓reduceIte] at hne_y ⊢
        rw [Function.update_of_ne (by omega)]
    refine hdll.erase hh_mem (fun _ _ => hmem3_head) ?_ ?_ ?_ ?_ ?_
    · intro hEr
      have hlen1 : L.length = 1 := by
        have := List.length_erase_of_mem hh_mem
        rw [hEr, List.length_nil] at this; omega
      have hk0 : k = 0 := by omega
      have hp0' : pVal = 0 := by simp [hbody_k.1, hk0]
      have hq0' : qVal = 0 := by simp [hbody_k.2, hk0, hlen1]
      rw [hmem3_head]; simp [hp0', hq0']
    · intro y hy hne_y
      have hy_lt := hdll.2.1 y (List.mem_of_mem_erase hy)
      have hidx : L.idxOf h = k := by rw [← hLk]; exact hdll.1.idxOf_getElem k hk
      rw [hidx] at hne_y
      dsimp only at hne_y
      refine hp_prev y hy_lt ?_
      by_cases hk1 : k + 1 = L.length
      · simp only [hk1, ↓reduceIte]
        exact Nat.ne_of_lt hy_lt
      · have hk1_lt : k + 1 < L.length := by omega
        simp only [hk1_lt, ↓reduceDIte] at hne_y
        simp only [hk1, ↓reduceIte]
        rw [List.getD_eq_getElem _ _ hk1_lt]
        exact hne_y
    · intro k₀ hk₀ hLk₀
      have hk0_eq : k₀ = k := hdll.1.getElem_inj_iff.mp (hLk₀.trans hLk.symm)
      subst hk0_eq
      have hlt_q : L[k₀ + 1] < cap := hdll.2.1 _ (List.getElem_mem hk₀)
      have hq_ne : qVal ≠ 0 := by simp [hbody_k.2, show k₀ + 1 ≠ L.length by omega]
      rw [show mem3 (hePrevBase + L[k₀ + 1]) = st₂.mem (hePrevBase + L[k₀ + 1]) from
            Function.update_of_ne (hdisj_ph _ hlt_q).2 _ st₂.mem, hmem2]
      dsimp only [mem2]
      simp only [hq_ne, ↓reduceIte]
      rw [show hePrevBase + (qVal - 1) = hePrevBase + L[k₀ + 1] by
            simp only [hbody_k.2, show k₀ + 1 ≠ L.length by omega, ↓reduceIte,
              List.getD_eq_getElem _ _ hk₀, Nat.add_sub_cancel],
          Function.update_self]
    · intro y hy hne_y
      have hy_lt := hdll.2.1 y (List.mem_of_mem_erase hy)
      have hidx : L.idxOf h = k := by rw [← hLk]; exact hdll.1.idxOf_getElem k hk
      rw [hidx] at hne_y
      dsimp only at hne_y
      refine hp_next y hy_lt ?_
      by_cases hk0 : k = 0
      · simp only [hk0, ↓reduceIte]
        exact Nat.ne_of_lt hy_lt
      · simp only [hk0, ↓reduceIte] at hne_y ⊢
        simpa [getElem!_pos L (k - 1) (by omega)] using hne_y
    · intro k₀ hk₀ hk₀_pos hLk₀
      have hk0_eq : k₀ = k := hdll.1.getElem_inj_iff.mp (hLk₀.trans hLk.symm)
      subst hk0_eq
      have hlt_p : L[k₀ - 1] < cap := hdll.2.1 _ (List.getElem_mem (by omega))
      have hp_ne : pVal ≠ 0 := by simp [hbody_k.1, Nat.ne_of_gt hk₀_pos]
      rw [show mem3 (heNextBase + L[k₀ - 1]) = st₂.mem (heNextBase + L[k₀ - 1]) from
            Function.update_of_ne (hdisj_nh _ hlt_p).2 _ st₂.mem, hmem2]
      have hm2 : mem2 (heNextBase + L[k₀ - 1]) = mem1 (heNextBase + L[k₀ - 1]) := by
        dsimp only [mem2]; split_ifs with hq0
        · rfl
        · rw [hbody_k.2] at hq0 ⊢
          have hk1 : k₀ + 1 ≠ L.length := fun hc => by simp [hc] at hq0
          have hlt_q : L.getD (k₀ + 1) 0 < cap := by
            rw [List.getD_eq_getElem _ _ (by omega)]; exact hdll.2.1 _ (List.getElem_mem _)
          simp only [hk1, ↓reduceIte, Nat.add_sub_cancel]
          rw [Function.update_of_ne (fun e => hdisj_pn _ _ e.symm hlt_q hlt_p)]
      rw [hm2]
      dsimp only [mem1]
      simp only [hp_ne, ↓reduceIte]
      rw [show heNextBase + (pVal - 1) = heNextBase + L[k₀ - 1] by
            simp [hbody_k.1, Nat.ne_of_gt hk₀_pos],
          Function.update_self]
  · dsimp only; rw [Function.update_self]
  · intro addr hp_f hn_f ha1 ha2
    dsimp only
    rw [Function.update_of_ne ha2, hmem2]
    have hm2 : mem2 addr = mem1 addr := by
      dsimp only [mem2]; split_ifs with hq0
      · rfl
      · have hk1 : k + 1 ≠ L.length := fun hc => by simp [hbody_k.2, hc] at hq0
        have hmem_q : L.getD (k + 1) 0 ∈ L := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        have hq_eq : qVal - 1 = L.getD (k + 1) 0 := by simp [hbody_k.2, hk1]
        rw [Function.update_of_ne (fun e => hp_f (L.getD (k + 1) 0) (by rw [e, hq_eq]) hmem_q)]
    rw [hm2]
    dsimp only [mem1]; split_ifs with hp0
    · rw [Function.update_of_ne ha1]
    · have hk0 : k ≠ 0 := fun hc => by simp [hbody_k.1, hc] at hp0
      have hmem_p : L[k - 1] ∈ L := List.getElem_mem (by omega)
      have hp_eq : pVal - 1 = L[k - 1] := by simp [hbody_k.1, hk0]
      rw [Function.update_of_ne (fun e => hn_f (L[k - 1]) (by rw [e, hp_eq]) hmem_p)]

end

end MinCostFlow.DynSpanner.Program
