module

public import MinCostFlow.HierPaths.InitProgProjectedSec

/-!
# A payload for every edge occurrence

For each projected edge row, the reverse index needs the designated
endpoint once per edge. The adjacent offsets give the length of the
row. A fill appends that many copies of the endpoint word.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- One row contributes its payload repeated once for each stored edge. -/
def initRepeatRowsWords (k : ℕ) (f : ℕ → List ℕ) (vals : ℕ → ℕ) : List ℕ :=
  initAppendPrefix (fun i => List.replicate (f i).length (vals i)) k

/-- Arguments are the CSR base, payload table, row count, and output address. -/
def initRepeatRows (fill : ℕ) : Stmt :=
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.bin .add (.reg 0) (.reg 4)) ;;
      .assign 6 (.bin .sub (.load (.bin .add (.reg 5) (.const 1))) (.load (.reg 5))) ;;
      .call 3 fill [.reg 3, .reg 6, .load (.bin .add (.reg 1) (.reg 4))]) ;;
  .ret (.reg 3)

theorem initRepeatRows_noRand (fill : ℕ) : (initRepeatRows fill).NoRand := by
  simp [initRepeatRows, forRange, forUp, Stmt.NoRand]

def initRepeatRowsContract (w k : ℕ) (f : ℕ → List ℕ) (vals : ℕ → ℕ) : Contract where
  pre args mem := ∃ addr v dst, args = [addr, v, k, dst] ∧
    ListAt mem addr (csrList k f) ∧ addr + (csrList k f).length ≤ dst ∧
    v + k ≤ dst ∧ (∀ i < k, mem (v + i) = vals i ∧ vals i < 2 ^ w) ∧
    dst + (initRepeatRowsWords k f vals).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem r mem' := ∃ addr v dst, args = [addr, v, k, dst] ∧
    r = dst + (initRepeatRowsWords k f vals).length ∧
    ListAt mem' dst (initRepeatRowsWords k f vals) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := rangeCost (fun i => 15 * (f i).length + 45) 0 k + 9 * k + 15

theorem initRepeatRows_meetsContract {w k j fill : ℕ} {f : ℕ → List ℕ} {vals : ℕ → ℕ}
    {p : Program} (hp : p.procs[j]? = some (initRepeatRows fill))
    (hFill : p.procs[fill]? = some initFillWord) :
    MeetsContract w p j (initRepeatRowsContract w k f vals) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨addr, v, dst, rfl, hCSR, hsep, hv, hvals, hroom, h1⟩ := hpre
  let chunks := fun i => List.replicate (f i).length (vals i)
  let R := fun (s : State) => s.regs 0 = addr ∧ s.regs 1 = v ∧ s.regs 2 = k
  have hlen : k + 1 ≤ (csrList k f).length := by
    rw [csrList, List.length_append, length_csrOffsets]
    omega
  have hloop := initAppendLoop_triple (w := w) (p := p) (dstReg := 3) (idxReg := 4)
    (hi := .reg 2) (body := .assign 5 (.bin .add (.reg 0) (.reg 4)) ;;
      .assign 6 (.bin .sub (.load (.bin .add (.reg 5) (.const 1))) (.load (.reg 5))) ;;
      .call 3 fill [.reg 3, .reg 6, .load (.bin .add (.reg 1) (.reg 4))])
    R chunks (fun i => 15 * (f i).length + 45) k dst mem (by decide) h1 (hw _ (by simp))
    (fun s _ hs => by simpa [R] using hs) (fun _ hs => Expr.eval_reg_of_eq hs.2.2) ?_
  · refine runs_start_le ?_
    unfold initRepeatRows
    refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
    intro s ⟨_, hp, hwords, hf⟩
    refine runs_ret_le (v := s.regs 3) (Expr.eval_reg_of_eq rfl)
      ⟨addr, v, dst, rfl, hp, hwords, fun y hy => hf y (by rwa [hp] at hy)⟩ ?_
    simp [initRepeatRowsContract, Expr.size]
    omega
  intro i hi s hR hidx hout hf st ω' hs
  subst st
  obtain ⟨r0, r1, r2⟩ := hR
  let off := initCSRPrefix f i
  let off' := initCSRPrefix f (i + 1)
  let out := dst + (initAppendPrefix chunks i).length
  have hnext : off' = off + (f i).length := initCSRPrefix_succ f i
  have hbound : off' < 2 ^ w := by
    have he := initCSRAddr_le_end (addr := addr) (f := f) hi
    change addr + (k + 1) + off' ≤ _ at he
    omega
  have hoff : s.mem (addr + i) = off :=
    (hf _ (by omega)).trans (csrList_offset hCSR hi.le)
  have hoff' : s.mem (addr + i + 1) = off' := by
    rw [Nat.add_assoc]
    exact (hf _ (by omega)).trans (csrList_offset hCSR hi)
  have hv' : s.mem (v + i) = vals i := (hf _ (by omega)).trans (hvals i hi).1
  have he : dst + (initAppendPrefix chunks (i + 1)).length = out + (f i).length := by
    rw [initAppendPrefix_succ, List.length_append, Nat.add_assoc, List.length_replicate]
  have hLen : out + (f i).length < 2 ^ w := by
    rw [← he]
    exact (Nat.add_le_add_left (initAppendPrefix_length_mono chunks hi) dst).trans_lt hroom
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := addr + i) (Expr.eval_add
    (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq hidx) (by omega)) ?_
  refine runs_seq_assign_le (v := (f i).length) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := addr + i) rfl)
      (Expr.eval_const h1) (by omega)) hoff') (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) hoff)
      hbound) (by omega)) ?_
  refine runs_call_le (initFillWord_meetsContract (w := w) hFill)
    (vs := [out, (f i).length, vals i]) ?_ ?_
    ⟨out, (f i).length, vals i, rfl, hLen, h1⟩ ?_
  · have ev := Expr.eval_load_of_eq
      (Expr.eval_add (w := w) (Expr.eval_reg_of_eq (r := 1)
        (st := {s with regs := Function.update (Function.update s.regs 5 (addr + i)) 6 (f i).length})
        (by simpa using r1)) (Expr.eval_reg_of_eq (r := 4) (by simpa using hidx)) (by omega)) hv'
    simp only [evalArgs, ev]
    simp [Expr.eval, hout, out]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · omega
    · exact (hvals i hi).2
  · intro r mem' pos' hp'
    obtain ⟨dst', len', val', ha, hr, hwords, hfr⟩ := hp'
    simp only [List.cons.injEq, and_true] at ha
    obtain ⟨hd', hl', hv'⟩ := ha
    subst dst' len' val' r
    refine ⟨⟨⟨by simpa using r0, by simpa using r1, by simpa using r2⟩, by simpa using hidx,
      he.symm, hwords, ?_⟩, ?_⟩
    · intro y hy
      rw [he] at hy
      exact hfr y hy
    · simp [initFillWordContract, Expr.size, argsSize]
      omega

end MinCostFlow.HierPaths

end
