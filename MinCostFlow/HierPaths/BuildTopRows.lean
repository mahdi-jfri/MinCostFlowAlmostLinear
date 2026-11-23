module

public import MinCostFlow.HierPaths.BuildProgCopy
public import MinCostFlow.HierPaths.InitProgCSRWrite

/-!
# Gathering rows into the static sections

Level calls leave rows in separate blocks. Each directory entry supplies
the address and length of one row, which can be copied directly into the
static output without scanning earlier rows.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The row directory interleaves source addresses and lengths. -/
def buildTopRowDir (ctx k : ℕ) (row : ℕ → List ℕ) (src : ℕ → ℕ)
    (bound : ℕ) (mem : ℕ → ℕ) : Prop :=
  ctx + 2 * k ≤ bound ∧ ∀ i < k,
    mem (ctx + 2 * i) = src i ∧ mem (ctx + 2 * i + 1) = (row i).length ∧
    ListAt mem (src i) (row i) ∧ src i + (row i).length ≤ bound

/-- Copy a row from the directory to the output suffix and return its end. -/
def buildTopRow (copy : ℕ) : Stmt :=
  .assign 3 (.bin .add (.reg 0) (.bin .add (.reg 1) (.reg 1))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .call 5 copy [.load (.reg 3), .reg 4, .reg 2] ;;
  .ret (.bin .add (.reg 2) (.reg 4))

theorem buildTopRow_noRand (copy : ℕ) : (buildTopRow copy).NoRand := by
  simp [buildTopRow, Stmt.NoRand]

theorem buildTopRowDir_stable {ctx k bound : ℕ} {row : ℕ → List ℕ} {src : ℕ → ℕ}
    {mem mem' : ℕ → ℕ} (hd : buildTopRowDir ctx k row src bound mem)
    (hf : ∀ y < bound, mem' y = mem y) : buildTopRowDir ctx k row src bound mem' := by
  obtain ⟨hc, hd⟩ := hd
  refine ⟨hc, fun i hi => ?_⟩
  obtain ⟨a, b, c, d⟩ := hd i hi
  exact ⟨(hf _ (by omega)).trans a, (hf _ (by omega)).trans b,
    fun j hj => (hf _ (by omega)).trans (c j hj), d⟩

theorem buildTopRow_meetsContract {w f copy ctx k i : ℕ} {rows : ℕ → List ℕ} {src : ℕ → ℕ}
    {p : Program} (hp : p.procs[f]? = some (buildTopRow copy))
    (hc : p.procs[copy]? = some buildCopyProc) (hi : i < k) :
    MeetsContract w p f (initCSRWriteRowContract ctx i (rows i)
      (fun addr mem => ∃ dst,
        buildTopRowDir ctx k rows src dst mem ∧ dst + k + 1 ≤ addr ∧
        addr + (rows i).length < 2 ^ w) (17 * (rows i).length + 70)) := by
  refine meetsContract_of_runs hp fun args mem pos ω words hpre => ?_
  obtain ⟨out, rfl, ⟨dst, hdir, hsep, hr⟩, hz⟩ := hpre
  obtain ⟨hctx, hrows⟩ := hdir
  obtain ⟨ha, hb, hrow, hsrc⟩ := hrows i hi
  have h1 : 1 < 2 ^ w := by omega
  let ptr := ctx + 2 * i
  have hptr : ptr + 1 < 2 ^ w := by dsimp [ptr]; omega
  have hsrc' : src i < 2 ^ w := by omega
  have hlen : (rows i).length < 2 ^ w := by omega
  have he : ctx + (i + i) = ptr := by dsimp [ptr]; omega
  refine runs_start_le ?_
  unfold buildTopRow
  refine runs_seq_assign_le (v := ptr) (Expr.eval_eq_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (v := ctx) rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := i) rfl) (Expr.eval_reg_of_eq (v := i) rfl)
        (by omega)) (by omega)) he) ?_
  refine runs_seq_assign_le (v := (rows i).length) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (v := ptr) rfl) (Expr.eval_const h1) hptr) hb) ?_
  refine runs_seq_call_le (buildCopyProc_meetsContract hc) (vs := [src i, (rows i).length, out])
    ?_ ?_ ⟨src i, _, out, rfl, by omega, hr, h1⟩ ?_
  · simp [evalArgs, Expr.eval, startState, ha, ptr]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  intro _ mem' pos' hpost
  obtain ⟨a, n, d, heq, hcopy, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨e₁,e₂,e₃⟩ := heq
  subst a n d
  refine runs_ret_le (v := out + (rows i).length) (Expr.eval_add
    (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hr)
    ⟨out, rfl, rfl, fun j hj => (hcopy j hj).trans (hrow j hj),
      fun y hy => (hframe y (.inr hy)).trans (hz y (by change out + (rows i).length ≤ y at hy; omega)), fun y hy => hframe y (.inl hy)⟩ ?_
  simp [initCSRWriteRowContract, buildCopyContract, Expr.size, argsSize]; omega

/-- The directory gather writes one complete CSR section in linear time. -/
theorem buildTopGather_meetsContract {w f row copy ctx k : ℕ}
    {rows : ℕ → List ℕ} {src : ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (initCSRWrite row))
    (hrow : p.procs[row]? = some (buildTopRow copy))
    (hc : p.procs[copy]? = some buildCopyProc) :
    MeetsContract w p f (initCSRWriteContract w ctx k rows
      (fun i => 17 * (rows i).length + 70) (buildTopRowDir ctx k rows src) 0) := by
  refine initCSRWrite_meetsContract hp (fun i hi => ?_) (fun _ _ _ hd hf => buildTopRowDir_stable hd hf)
  simpa only [Nat.add_zero] using
    (buildTopRow_meetsContract (rows := rows) (src := src) (ctx := ctx) hrow hc hi)

end MinCostFlow.HierPaths

end
