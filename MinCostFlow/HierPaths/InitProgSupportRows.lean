module

public import MinCostFlow.HierPaths.InitProgSupportEmit

/-!
# Traversing walk rows for the support index

Two adjacent offsets locate a connector's vertex row. A call emits
three words per position in that row, and the next row appends to it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

def initSupportRowWords (keys : Bool) (f : ℕ → List ℕ) (i : ℕ) : List ℕ :=
  initAppendPrefix (initSupportWords keys true ((f i).getD · 0) i) (f i).length

/-- Arguments are the CSR base, number of rows, and output address. -/
def initSupportRows (emit : ℕ) : Stmt :=
  .assign 7 (.bin .add (.bin .add (.reg 0) (.reg 1)) (.const 1)) ;;
  forRange 3 (.const 0) (.reg 1)
    (.assign 4 (.bin .add (.reg 0) (.reg 3)) ;;
     .assign 5 (.load (.reg 4)) ;;
     .assign 6 (.bin .sub (.load (.bin .add (.reg 4) (.const 1))) (.reg 5)) ;;
     .call 2 emit [.bin .add (.reg 7) (.reg 5), .reg 6, .reg 3, .reg 2]) ;;
  .ret (.reg 2)

theorem initSupportRows_noRand (emit : ℕ) : (initSupportRows emit).NoRand := by
  simp [initSupportRows, forRange, forUp, Stmt.NoRand]

def initSupportRowsContract (w k : ℕ) (keys : Bool) (f : ℕ → List ℕ) : Contract where
  pre args mem := ∃ addr dst, args = [addr, k, dst] ∧ ListAt mem addr (csrList k f) ∧
    addr + (csrList k f).length ≤ dst ∧
    dst + (initAppendPrefix (initSupportRowWords keys f) k).length < 2 ^ w ∧ 3 < 2 ^ w
  post args mem r mem' := ∃ addr dst, args = [addr, k, dst] ∧
    r = dst + (initAppendPrefix (initSupportRowWords keys f) k).length ∧
    ListAt mem' dst (initAppendPrefix (initSupportRowWords keys f) k) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := 50 * (csrData k f).length + 90 * k + 30

theorem initSupportRows_meetsContract {w k j emit : ℕ} {keys : Bool} {f : ℕ → List ℕ}
    {p : Program} (hp : p.procs[j]? = some (initSupportRows emit))
    (hEmit : p.procs[emit]? = some (initSupportEmit keys true)) :
    MeetsContract w p j (initSupportRowsContract w k keys f) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨addr, dst, rfl, hCSR, hsep, hroom, h3⟩ := hpre
  let data := addr + k + 1
  let chunks := initSupportRowWords keys f
  let R := fun (s : State) => s.regs 0 = addr ∧ s.regs 1 = k ∧ s.regs 7 = data
  have hlen : k + 1 ≤ (csrList k f).length := by
    rw [csrList, List.length_append, length_csrOffsets]
    omega
  have h1 : 1 < 2 ^ w := by omega
  have hdata : data < 2 ^ w := by dsimp [data]; omega
  have hloop := initAppendLoop_triple (w := w) (p := p) (dstReg := 2) (idxReg := 3)
    (hi := .reg 1) (body := .assign 4 (.bin .add (.reg 0) (.reg 3)) ;;
      .assign 5 (.load (.reg 4)) ;;
      .assign 6 (.bin .sub (.load (.bin .add (.reg 4) (.const 1))) (.reg 5)) ;;
      .call 2 emit [.bin .add (.reg 7) (.reg 5), .reg 6, .reg 3, .reg 2])
    R chunks (fun i => 50 * (f i).length + 75) k dst mem (by decide) h1 (hw _ (by simp))
    (fun s _ hs => by simpa [R] using hs) (fun _ hs => Expr.eval_reg_of_eq hs.2.1) ?_
  · refine runs_start_le ?_
    unfold initSupportRows
    refine runs_seq_assign_le (v := data) (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) (by dsimp [data] at hdata; omega))
      (Expr.eval_const h1) hdata) ?_
    refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
    intro s ⟨_, hp, hwords, hf⟩
    refine runs_ret_le (v := s.regs 2) (Expr.eval_reg_of_eq rfl)
      ⟨addr, dst, rfl, hp, hwords, fun y hy => hf y (by rwa [hp] at hy)⟩ ?_
    simp only [initSupportRowsContract, rangeCost_add, rangeCost_const, rangeCost_zero_eq_range,
      Nat.sub_zero, Expr.size]
    have he (l : List ℕ) :
        (l.map (fun i => 50 * (f i).length + 75)).sum =
          50 * (l.flatMap f).length + 75 * l.length := by
      induction l with
      | nil => simp
      | cons i l ih => simp [ih, Nat.mul_add]; omega
    rw [he, List.length_range]
    change _ ≤ 50 * ((List.range k).flatMap f).length + 90 * k + 30
    omega
  intro i hi s hR hidx hout hf st ω' hs
  subst st
  obtain ⟨r0, r1, r7⟩ := hR
  let off := initCSRPrefix f i
  let off' := initCSRPrefix f (i + 1)
  let out := dst + (initAppendPrefix chunks i).length
  have hnext : off' = off + (f i).length := initCSRPrefix_succ f i
  have hRowEnd : data + off' ≤ dst := (initCSRAddr_le_end (addr := addr) (f := f) hi).trans hsep
  have hoff : s.mem (addr + i) = off :=
    (hf _ (by omega)).trans (csrList_offset hCSR hi.le)
  have hoff' : s.mem (addr + i + 1) = off' := by
    rw [Nat.add_assoc]
    exact (hf _ (by omega)).trans (csrList_offset hCSR hi)
  have he : dst + (initAppendPrefix chunks (i + 1)).length = out + 3 * (f i).length := by
    rw [initAppendPrefix_succ, List.length_append, Nat.add_assoc]
    exact congrArg (fun n => dst + ((initAppendPrefix chunks i).length + n))
      (initSupportPrefix_length _ _ _ _ _)
  have hLen : out + 3 * (f i).length < 2 ^ w := by
    rw [← he]
    exact (Nat.add_le_add_left (initAppendPrefix_length_mono chunks hi) dst).trans_lt hroom
  have hRow : ListAt s.mem (data + off) (f i) :=
    listAt_congr (fun j hj => (hf _ (by omega)).symm) (initCSRAddr_listAt (addr := addr) (k := k) hCSR hi)
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := addr + i)
    (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq hidx) (by omega)) ?_
  refine runs_seq_assign_le (v := off)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) hoff) ?_
  refine runs_seq_assign_le (v := (f i).length) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := addr + i) rfl)
      (Expr.eval_const h1) (by omega)) hoff') (Expr.eval_reg_of_eq (v := off) rfl) (show off' < 2 ^ w by omega)) (by omega)) ?_
  refine runs_call_le (initSupportEmit_meetsContract (w := w) (row := i) (l := f i) hEmit)
    (vs := [data + off, (f i).length, i, out]) ?_ ?_
    ⟨data + off, out, rfl, hRow, by omega, hLen, h3⟩ ?_
  · simp [evalArgs, Expr.eval, BinOp.eval, r7, hidx, hout, out,
      (show data + off < 2 ^ w by omega)]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro r mem' pos' hp'
    obtain ⟨src', dst', ha, hr, hwords, hfr⟩ := hp'
    simp only [List.cons.injEq, and_true] at ha
    obtain ⟨hs', _, _, hd'⟩ := ha
    subst src' dst' r
    refine ⟨⟨⟨by simpa using r0, by simpa using r1, by simpa using r7⟩, by simpa using hidx,
      he.symm, hwords, ?_⟩, ?_⟩
    · intro y hy
      rw [he] at hy
      exact hfr y hy
    · simp [initSupportEmitContract, Expr.size, argsSize]; omega

end MinCostFlow.HierPaths

end
