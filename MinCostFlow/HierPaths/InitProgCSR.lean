module

public import MinCostFlow.HierPaths.InitSections

/-!
# Reading the number of records in a connector row

The parent offset table gives the length of a row, but the row itself starts directly with
offsets. The last offset is the first for which its position plus one and its value add up to
the row length. The procedure finds it by a single scan of the offsets.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

private theorem csr_offset_scan_lt {k i : ℕ} (f : ℕ → List ℕ) (hi : i < k) :
    i + 1 + ((List.range i).map fun j => (f j).length).sum < (csrList k f).length := by
  rw [length_csrList, sum_map_range]
  have hsum : ∑ j ∈ Finset.range i, (f j).length ≤ ∑ j ∈ Finset.range k, (f j).length :=
    Finset.sum_le_sum_of_subset ((by intro j hj; exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans hi)))
  omega

private theorem csr_offset_scan_eq (k : ℕ) (f : ℕ → List ℕ) :
    k + 1 + ((List.range k).map fun j => (f j).length).sum = (csrList k f).length := by
  rw [length_csrList, sum_map_range]

/-- The guard compares the current offset plus its position and one to the row length. -/
def initCSRGuard : Expr :=
  .bin .lt (.bin .add (.bin .add (.reg 2) (.const 1))
    (.load (.bin .add (.reg 0) (.reg 2)))) (.reg 1)

/-- Called with the start and length of a row, return its number of records. -/
def initCSRCount : Stmt :=
  .assign 2 (.const 0) ;;
  .loop initCSRGuard (.assign 2 (.bin .add (.reg 2) (.const 1))) ;;
  .ret (.reg 2)

theorem initCSRCount_noRand : initCSRCount.NoRand := by simp [initCSRCount, Stmt.NoRand]

/-- The count leaves memory unchanged and uses at most a constant number of steps per offset. -/
def initCSRCountContract (w k : ℕ) (f : ℕ → List ℕ) : Contract where
  pre args mem := ∃ addr, args = [addr, (csrList k f).length] ∧
    ListAt mem addr (csrList k f) ∧ addr + (csrList k f).length < 2 ^ w ∧ 1 < 2 ^ w
  post _ mem v mem' := v = k ∧ mem' = mem
  cost _ _ := 20 * (k + 1)

/-- The read-only scan stops after exactly the last offset. -/
theorem initCSRCount_meetsContract {w k j : ℕ} {f : ℕ → List ℕ} {p : Program}
    (hp : p.procs[j]? = some initCSRCount) :
    MeetsContract w p j (initCSRCountContract w k f) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨addr, rfl, hmem, hw, h1⟩ := hpre
  set len := (csrList k f).length
  have hk : k + 1 ≤ len := by change k + 1 ≤ (csrList k f).length; rw [length_csrList]; omega
  let Inv : State → Prop := fun s => s.regs 0 = addr ∧ s.regs 1 = len ∧
    s.regs 2 ≤ k ∧ s.mem = mem
  have hloop := Triple.loop_const_normal (p := p) (w := w)
    (e := initCSRGuard) (body := .assign 2 (.bin .add (.reg 2) (.const 1)))
    (Inv := Inv) (Q := fun s => s.regs 2 = k ∧ s.mem = mem)
    (m := fun s => k - s.regs 2) (condVal := fun s => if s.regs 2 < k then 1 else 0)
    (bodyBound := 4)
    (hcond := fun s hs => by
      obtain ⟨h0, hlen, hi, hm⟩ := hs
      set i := s.regs 2
      let off := ((List.range i).map fun j => (f j).length).sum
      have hcell : s.mem (addr + i) = off := by rw [hm, csrList_offset hmem hi]
      have hcase : (if i + 1 + off < len then 1 else 0 : ℕ) = if i < k then 1 else 0 := by
        rcases Nat.lt_or_eq_of_le hi with hlt | heq
        · simp [hlt, csr_offset_scan_lt f hlt, off, len]
        · simp [heq, off, len, csr_offset_scan_eq]
      have hsum : i + 1 + off ≤ len := by
        rcases Nat.lt_or_eq_of_le hi with hlt | heq
        · exact (csr_offset_scan_lt f hlt).le
        · simpa [off, heq, len] using (csr_offset_scan_eq k f).le
      unfold initCSRGuard
      exact Expr.eval_eq_of_eq (Expr.eval_lt_op
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) (by omega))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0)
            (Expr.eval_reg_of_eq rfl) (by omega)) hcell) (by omega))
        (Expr.eval_reg_of_eq hlen) h1) hcase)
    (hexit := fun s hs hzero => by
      obtain ⟨_, _, hi, hm⟩ := hs
      refine ⟨?_, hm⟩
      by_contra hne
      simp [show s.regs 2 < k from lt_of_le_of_ne hi hne] at hzero)
    (hstep := fun s hs hgood => by
      obtain ⟨h0, hlen, hi, hm⟩ := hs
      have hlt : s.regs 2 < k := by by_contra h; simp [h] at hgood
      intro t ω ht
      subst t
      refine runs_start_le ?_
      refine runs_assign_le (v := s.regs 2 + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) (by omega)) ?_ ?_
      · refine ⟨⟨?_, ?_, ?_, hm⟩, ?_⟩
        · simpa using h0
        · simpa using hlen
        · simpa using Nat.succ_le_of_lt hlt
        · simp; omega
      · simp [Expr.size])
  refine runs_start_le ?_
  unfold initCSRCount
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop (by simp [Inv, startState]) ?_
  intro s ⟨hr, hm⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hr) ⟨rfl, hm⟩ ?_
  simp [initCSRCountContract, initCSRGuard, Expr.size, startState]
  omega

/-- The number of data words before row `i` in a compressed table. -/
def initCSRPrefix (f : ℕ → List ℕ) (i : ℕ) : ℕ :=
  ((List.range i).map fun j => (f j).length).sum

theorem initCSRPrefix_succ (f : ℕ → List ℕ) (i : ℕ) :
    initCSRPrefix f (i + 1) = initCSRPrefix f i + (f i).length := by
  simp [initCSRPrefix, List.range_succ]

/-- The address of row `i`, allowing the end sentinel at `i = k`. -/
def initCSRAddr (addr k : ℕ) (f : ℕ → List ℕ) (i : ℕ) : ℕ :=
  addr + (k + 1) + initCSRPrefix f i

theorem initCSRAddr_le_end {addr k i : ℕ} {f : ℕ → List ℕ} (hi : i ≤ k) :
    initCSRAddr addr k f i ≤ addr + (csrList k f).length := by
  unfold initCSRAddr initCSRPrefix
  rw [length_csrList, sum_map_range]
  have hsum : ∑ j ∈ Finset.range i, (f j).length ≤ ∑ j ∈ Finset.range k, (f j).length :=
    Finset.sum_le_sum_of_subset (by
      intro j hj
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hi))
  omega

/-- The address following a row differs from its start by the row's length. -/
theorem initCSRAddr_succ (addr k : ℕ) (f : ℕ → List ℕ) (i : ℕ) :
    initCSRAddr addr k f (i + 1) = initCSRAddr addr k f i + (f i).length := by
  simp [initCSRAddr, initCSRPrefix_succ, Nat.add_assoc]

/-- The row's data begin at the address found from its offset. -/
theorem initCSRAddr_listAt {addr k i : ℕ} {f : ℕ → List ℕ} {mem : ℕ → ℕ}
    (hm : ListAt mem addr (csrList k f)) (hi : i < k) :
    ListAt mem (initCSRAddr addr k f i) (f i) :=
  listAt_csrList_get hm hi

/-- For arguments `[addr, k, i]`, return the address of row `i` in constant time. -/
def initCSRSeek : Stmt :=
  .ret (.bin .add (.bin .add (.reg 0) (.bin .add (.reg 1) (.const 1)))
    (.load (.bin .add (.reg 0) (.reg 2))))

theorem initCSRSeek_noRand : initCSRSeek.NoRand := by simp [initCSRSeek, Stmt.NoRand]

/-- Read an address from a compressed table without modifying memory. -/
def initCSRSeekContract (w k : ℕ) (f : ℕ → List ℕ) : Contract where
  pre args mem := ∃ addr i, args = [addr, k, i] ∧ i ≤ k ∧
    ListAt mem addr (csrList k f) ∧ addr + (csrList k f).length < 2 ^ w
  post args mem v mem' := v = initCSRAddr (args.getD 0 0) k f (args.getD 2 0) ∧ mem' = mem
  cost _ _ := 12

theorem initCSRSeek_meetsContract {w k j : ℕ} {f : ℕ → List ℕ} {p : Program}
    (hp : p.procs[j]? = some initCSRSeek) :
    MeetsContract w p j (initCSRSeekContract w k f) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨addr, i, rfl, hi, hmem, hw⟩ := hpre
  have haddr := (initCSRAddr_le_end (addr := addr) (f := f) hi).trans_lt hw
  have hlen : k + 1 ≤ (csrList k f).length := by rw [length_csrList]; omega
  have hoff : mem (addr + i) = initCSRPrefix f i := csrList_offset hmem hi
  refine runs_start_le ?_
  unfold initCSRSeek
  refine runs_ret_le (v := initCSRAddr addr k f i) ?_ ⟨rfl, rfl⟩ ?_
  · exact Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (v := addr) rfl)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := k) rfl) (Expr.eval_const (by omega)) (by omega))
        (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := addr) rfl)
        (Expr.eval_reg_of_eq (v := i) rfl) (by omega)) hoff) haddr
  · simp [Expr.size, initCSRSeekContract]

end MinCostFlow.HierPaths

end
