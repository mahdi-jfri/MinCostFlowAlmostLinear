module

public import MinCostFlow.MinRatio.SelectMetaTableRow
public import MinCostFlow.MinRatio.SelectBlocksParts
import WordRAM.Tactic

/-!
# Writing the select metadata table (`SelectMetaTableWrite`)

The select procedures read the level data through the metadata table (`SelectMetaTableAt`,
`SelectLevelBlocks.lean`): the gradient pointer, the depth, and eight rows of `d + 1` pointers.
Init writes the table once. A rebuild or a shift may move the solver's graph of a level, and the
table points into it, so the table is written again after each of them. The table has
`2 + 8 (d + 1)` words, so this costs `O(d)`.

* `selTableWriteBody row` (`[metaBase, base, d, vCap, eCap, Lk, slot, lvlMeta]`): computes the
  addresses of the level blocks of `B = ⟨base, d, vCap, eCap, Lk, slot⟩`, writes the two header
  words, and writes the eight rows with `selTableRowBody` (procedure `row`). The solver's graph of
  level `j < d` is read at `lvlMeta + d + j` (the word `levelMeta[d + j]` of `SolverLevelMetaAt`).
  The core lengths are owned by the blocks, so their row is affine in `j`.
* `selTableWrite_meetsContract`: after the call, `SelectMetaTableAt` holds for
  `selectMlocOf B metaBase solverG` with the solver pointers read before the call, and only the
  table's words change. Cost `240 d + 800`.
* `selTableWrite_keeps_blocks`: the call keeps the level blocks, when they lie off the table.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-- The entry of row `b` at level `j` of a metadata layout. -/
def SelectLevelMetaLoc.entry (mloc : SelectLevelMetaLoc) : ℕ → ℕ → ℕ
  | 0, j => mloc.GPtr j
  | 1, j => mloc.vCap j
  | 2, j => mloc.eCap j
  | 3, j => mloc.phiPtr j
  | 4, j => mloc.coreLenPtr j
  | 5, j => mloc.embPtr j
  | 6, j => mloc.fPtr j
  | 7, j => mloc.sPtr j
  | _, _ => 0

/-- Write the metadata table of the blocks `B`
(`[metaBase, base, d, vCap, eCap, Lk, slot, lvlMeta, pLast]`), with the row procedure `row`.
The terminal entry of row `7` (`smEntryAddr metaBase d 7 d`) stores `pLast`. -/
def selTableWriteBody (row : ℕ) : Stmt :=
  .assign 9 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 3)))
    (.bin .mul (.const 9) (.reg 4))) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 9) (.bin .mul (.reg 3) (.reg 5)))
    (.bin .mul (.reg 4) (.reg 5))) (.reg 4)) (.bin .mul (.reg 4) (.reg 6))) ;;
  .assign 14 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 11 (.bin .add (.reg 1) (.bin .mul (.reg 14) (.reg 10))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 1) (.reg 9)) (.bin .mul (.reg 3) (.reg 5))) ;;
  .assign 13 (.bin .add (.reg 11) (.reg 9)) ;;
  .store (.reg 0) (.reg 13) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 2) ;;
  .assign 15 (.bin .add (.reg 0) (.const 2)) ;;
  .call 16 row [.reg 15, .reg 14, .bin .add (.reg 7) (.reg 2), .reg 2, .reg 11, .const 0] ;;
  .call 16 row [.bin .add (.reg 15) (.reg 14), .reg 14, .reg 15, .const 0, .reg 3, .const 0] ;;
  .call 16 row [.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 14)), .reg 14, .reg 15,
    .const 0, .reg 4, .const 0] ;;
  .call 16 row [.bin .add (.reg 15) (.bin .mul (.const 3) (.reg 14)), .reg 14, .reg 15,
    .const 0, .bin .add (.reg 1) (.reg 9), .reg 10] ;;
  .call 16 row [.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 14)), .reg 14, .reg 15,
    .const 0, .reg 12, .reg 10] ;;
  .call 16 row [.bin .add (.reg 15) (.bin .mul (.const 5) (.reg 14)), .reg 14, .reg 15,
    .const 0, .bin .add (.reg 12) (.bin .mul (.reg 4) (.reg 5)), .reg 10] ;;
  .call 16 row [.bin .add (.reg 15) (.bin .mul (.const 6) (.reg 14)), .reg 14, .reg 15,
    .const 0, .reg 1, .reg 10] ;;
  .call 16 row [.bin .add (.reg 15) (.bin .mul (.const 7) (.reg 14)), .reg 14,
    .bin .add (.bin .add (.reg 7) (.reg 2)) (.const 1), .bin .sub (.reg 2) (.const 1), .reg 11,
    .const 0] ;;
  .store (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 7) (.reg 14))) (.reg 2)) (.reg 8) ;;
  .ret (.const 0)

theorem selTableWriteBody_noRand (row : ℕ) : (selTableWriteBody row).NoRand := by
  simp [selTableWriteBody, Stmt.NoRand]

/-- The table of the blocks `B` at `metaBase`, with the solver's level graphs at
`lvlMeta + d + j` in `mem` and terminal precision `pLast` at `smEntryAddr metaBase d 7 d`. -/
def selTableOf (B : SelectBlocksLoc) (metaBase lvlMeta pLast : ℕ) (mem : ℕ → ℕ) :
    SelectLevelMetaLoc :=
  selectMlocOf B metaBase (fun j => mem (lvlMeta + B.d + j)) pLast

/-- Contract of `selTableWriteBody`. -/
def selTableWriteContract (w : ℕ) (B : SelectBlocksLoc) (metaBase lvlMeta pLast : ℕ) : Contract where
  pre args _ :=
    args = [metaBase, B.base, B.d, B.vCap, B.eCap, B.Lk, B.slot, lvlMeta, pLast] ∧
    16 < 2 ^ w ∧ B.endAddr < 2 ^ w ∧ metaBase + selectLevelMetaSize B.d < 2 ^ w ∧
    lvlMeta + 2 * B.d + 1 < 2 ^ w ∧
    (lvlMeta + 2 * B.d ≤ metaBase ∨ metaBase + selectLevelMetaSize B.d ≤ lvlMeta)
  post _ mem ret mem' :=
    ret = 0 ∧ SelectMetaTableAt mem' (selTableOf B metaBase lvlMeta pLast mem) ∧
    ∀ a, (a < metaBase ∨ metaBase + selectLevelMetaSize B.d ≤ a) → mem' a = mem a
  cost _ _ := 240 * B.d + 840

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-- The rows `b' < b` of the table at `tb` (rows of `n` words) hold `val`, and the memory
outside the rows is that of `mem0`. -/
private def RowsDone (mem0 mem : ℕ → ℕ) (tb n : ℕ) (val : ℕ → ℕ → ℕ) (b : ℕ) : Prop :=
  (∀ b' < b, ∀ j < n, mem (tb + b' * n + j) = val b' j) ∧
  (∀ a, (a < tb ∨ tb + 8 * n ≤ a) → mem a = mem0 a)

private theorem row_lt {b' b n j : ℕ} (hb : b' < b) (hj : j < n) : b' * n + j < b * n := by
  have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at this
  omega

private theorem row_end {b n : ℕ} (hb : b < 8) : b * n + n ≤ 8 * n := by
  have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at this
  omega

/-- One row call: the rows before stay, and row `b` gets its values. -/
private theorem row_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {row : ℕ}
    (hrow : MeetsContract w p row (selTableRowContract w))
    {args : List Expr} {s : Stmt} {mem R : ℕ → ℕ} {pos k T : ℕ} {Q : Outcome → State → Prop}
    {mem0 : ℕ → ℕ} {tb n b dst src kk c step : ℕ} {val : ℕ → ℕ → ℕ}
    (hargs : evalArgs w ⟨mem, R, pos⟩ args = some [dst, n, src, kk, c, step])
    (hdst : dst = tb + b * n) (hw1 : 1 < 2 ^ w) (hw : tb + 8 * n < 2 ^ w)
    (hsrc : src + kk < 2 ^ w) (hcw : ∀ j < n, c + j * step < 2 ^ w) (hstep : step < 2 ^ w)
    (hcW : c < 2 ^ w)
    (hdisj : src + kk ≤ dst ∨ dst + n ≤ src) (hb : b < 8)
    (hdone : RowsDone mem0 mem tb n val b)
    (hval : ∀ j < n, selTableRowVal mem src kk c step j = val b j)
    (hrest : ∀ mem' pos' R', (∀ r, r ≠ 16 → R' r = R r) → RowsDone mem0 mem' tb n val (b + 1) →
      ∃ o st' c', Runs w p ω s ⟨mem', R', pos'⟩ o st' c' ∧ Q o st' ∧
        (k + argsSize args + (30 * n + 20) + 2) + c' ≤ T) :
    ∃ o st' c', Runs w p ω (.seq (.call 16 row args) s) ⟨mem, R, pos⟩ o st' c' ∧ Q o st' ∧
      k + c' ≤ T := by
  have hbn : b * n + n ≤ 8 * n := row_end hb
  refine runs_seq_call_flat hrow hargs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
    ⟨dst, n, src, kk, c, step, rfl, hw1, by omega, hsrc, by omega, hcw, hdisj⟩ ?_
  intro v mem' pos' hpost
  obtain ⟨_, hrowv, hfr⟩ := hpost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hrowv hfr
  refine hrest mem' pos' _ (fun r hr => Function.update_of_ne hr _ _) ⟨fun b' hb' j hj => ?_,
    fun a ha => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hb' with hlt | rfl
    · have := row_lt hlt hj
      rw [hfr _ (Or.inl (by omega))]
      exact hdone.1 b' hlt j hj
    · have := hrowv j hj
      rw [hdst] at this
      rw [this, hval j hj]
  · rw [hfr _ (by omega)]
    exact hdone.2 a ha

/-- The registers that the rows read. -/
private def RegsOK (B : SelectBlocksLoc) (metaBase lvlMeta pLast : ℕ) (R : ℕ → ℕ) : Prop :=
  R 1 = B.base ∧ R 2 = B.d ∧ R 3 = B.vCap ∧ R 4 = B.eCap ∧ R 5 = B.Lk ∧ R 7 = lvlMeta ∧
  R 8 = pLast ∧
  R 9 = 4 + 7 * B.vCap + 9 * B.eCap ∧
  R 10 = 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot ∧
  R 11 = B.lastGPtr ∧ R 12 = B.base + (4 + 7 * B.vCap + 9 * B.eCap) + B.vCap * B.Lk ∧
  R 14 = B.d + 1 ∧ R 15 = metaBase + 2

private theorem RegsOK.transfer {B : SelectBlocksLoc} {metaBase lvlMeta pLast : ℕ}
    {R R' : ℕ → ℕ}
    (h : RegsOK B metaBase lvlMeta pLast R) (hR : ∀ r, r ≠ 16 → R' r = R r) :
    RegsOK B metaBase lvlMeta pLast R' := by
  obtain ⟨h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h14, h15⟩ := h
  exact ⟨(hR 1 (by decide)).trans h1, (hR 2 (by decide)).trans h2, (hR 3 (by decide)).trans h3,
    (hR 4 (by decide)).trans h4, (hR 5 (by decide)).trans h5, (hR 7 (by decide)).trans h7,
    (hR 8 (by decide)).trans h8, (hR 9 (by decide)).trans h9, (hR 10 (by decide)).trans h10,
    (hR 11 (by decide)).trans h11, (hR 12 (by decide)).trans h12, (hR 14 (by decide)).trans h14,
    (hR 15 (by decide)).trans h15⟩

/-- The last row before the final `pLast` store: agrees with `sPtr` on `j < d`, and writes
`B.lastGPtr` at `j = d`. -/
private theorem sPtr_row_lt (B : SelectBlocksLoc) (metaBase lvlMeta pLast : ℕ) (mem : ℕ → ℕ)
    {j : ℕ} (hj : j < B.d) :
    (selTableOf B metaBase lvlMeta pLast mem).sPtr j =
      selTableRowVal mem (lvlMeta + B.d + 1) (B.d - 1) B.lastGPtr 0 j := by
  simp only [selTableOf, selectMlocOf, selTableRowVal, Nat.mul_zero, Nat.add_zero, hj, ↓reduceIte]
  by_cases h : j + 1 < B.d
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

set_option maxHeartbeats 1000000 in
/-- **The metadata table.** `selTableWriteBody` meets `selTableWriteContract`. -/
theorem selTableWrite_meetsContract {w proc row : ℕ} {p : Program} {B : SelectBlocksLoc}
    {metaBase lvlMeta pLast : ℕ}
    (hp : p.procs[proc]? = some (selTableWriteBody row))
    (hrow : MeetsContract w p row (selTableRowContract w)) :
    MeetsContract w p proc (selTableWriteContract w B metaBase lvlMeta pLast) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hw16, hendW, hmetaW, hlvlW, hdisj⟩ := hpre
  have hpLastW : pLast < 2 ^ w := hwords pLast (by simp)
  -- The sizes, written as the program computes them.
  have hS : B.levelSize =
      4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot := rfl
  have hlast : B.lastGPtr = B.base + (B.d + 1) *
      (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) := rfl
  have hg0 : B.g0Ptr = B.lastGPtr + (4 + 7 * B.vCap + 9 * B.eCap) := rfl
  have hend : B.endAddr = B.g0Ptr + B.eCap * B.Lk := rfl
  have hmeta : selectLevelMetaSize B.d = 2 + 8 * (B.d + 1) := rfl
  have hSle : 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot ≤
      (B.d + 1) * (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hjS : ∀ j < B.d + 1,
      j * (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) +
        (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) ≤
      (B.d + 1) * (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) :=
    fun j hj => by
      have := Nat.mul_le_mul_right
        (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)
        (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at this
      exact this
  have hw1 : 1 < 2 ^ w := by omega
  have hmetaW' : metaBase + 2 + 8 * (B.d + 1) < 2 ^ w := by omega
  have hendW' : B.base + (B.d + 1) *
      (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) +
      (4 + 7 * B.vCap + 9 * B.eCap) + B.eCap * B.Lk < 2 ^ w := by
    rw [hend, hg0, hlast] at hendW; exact hendW
  have hlast' : B.lastGPtr < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold selTableWriteBody
  refine runs_seq_assign_flat (v := 4 + 7 * B.vCap + 9 * B.eCap) (by eval_expr) ?_
  refine runs_seq_assign_flat
    (v := 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)
    (by eval_expr) ?_
  refine runs_seq_assign_flat (v := B.d + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := B.lastGPtr) (by rw [hlast]; eval_expr) ?_
  refine runs_seq_assign_flat (v := B.base + (4 + 7 * B.vCap + 9 * B.eCap) + B.vCap * B.Lk)
    (by eval_expr) ?_
  refine runs_seq_assign_flat (v := B.g0Ptr) (by rw [hg0]; eval_expr) ?_
  refine runs_seq_store_flat (x := metaBase) (v := B.g0Ptr) (by eval_expr)
    (by eval_expr) ?_
  refine runs_seq_store_flat (x := metaBase + 1) (v := B.d) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := metaBase + 2) (by eval_expr) ?_
  -- The registers before the rows, as an opaque function.
  generalize hR : Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun i =>
      [metaBase, B.base, B.d, B.vCap, B.eCap, B.Lk, B.slot, lvlMeta, pLast].getD i 0) 9
      (4 + 7 * B.vCap + 9 * B.eCap)) 10
      (4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)) 14 (B.d + 1))
      11 B.lastGPtr) 12 (B.base + (4 + 7 * B.vCap + 9 * B.eCap) + B.vCap * B.Lk)) 13 B.g0Ptr)
      15 (metaBase + 2) = R0
  have r1 : R0 1 = B.base := by rw [← hR]; rfl
  have r2 : R0 2 = B.d := by rw [← hR]; rfl
  have r3 : R0 3 = B.vCap := by rw [← hR]; rfl
  have r4 : R0 4 = B.eCap := by rw [← hR]; rfl
  have r5 : R0 5 = B.Lk := by rw [← hR]; rfl
  have r7 : R0 7 = lvlMeta := by rw [← hR]; rfl
  have r8 : R0 8 = pLast := by rw [← hR]; rfl
  have r9 : R0 9 = 4 + 7 * B.vCap + 9 * B.eCap := by rw [← hR]; rfl
  have r10 : R0 10 = 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot := by
    rw [← hR]; rfl
  have r11 : R0 11 = B.lastGPtr := by rw [← hR]; rfl
  have r12 : R0 12 = B.base + (4 + 7 * B.vCap + 9 * B.eCap) + B.vCap * B.Lk := by
    rw [← hR]; rfl
  have r14 : R0 14 = B.d + 1 := by rw [← hR]; rfl
  have r15 : R0 15 = metaBase + 2 := by rw [← hR]; rfl
  clear hR
  have hok0 : RegsOK B metaBase lvlMeta pLast R0 :=
    ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩
  -- The memory after the two header words.
  have hlvl : ∀ a, lvlMeta ≤ a → a < lvlMeta + 2 * B.d →
      Function.update (Function.update mem metaBase B.g0Ptr) (metaBase + 1) B.d a = mem a :=
    fun a h1 h2 => by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  let rowVal : ℕ → ℕ → ℕ := fun b j =>
    if b = 7 ∧ j = B.d then B.lastGPtr else (selTableOf B metaBase lvlMeta pLast mem).entry b j
  have hdone0 : RowsDone (Function.update (Function.update mem metaBase B.g0Ptr) (metaBase + 1)
      B.d) (Function.update (Function.update mem metaBase B.g0Ptr) (metaBase + 1) B.d)
      (metaBase + 2) (B.d + 1) rowVal 0 :=
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  -- Row 0: the level graphs.
  refine row_step hrow (dst := metaBase + 2) (src := lvlMeta + B.d) (kk := B.d) (c := B.lastGPtr)
    (step := 0) (by eval_expr) (by omega) hw1 hmetaW' (by omega) (fun j _ => by omega)
    (by omega) hlast' (by omega) (by omega) hdone0 (fun j hj => ?_) ?_
  · simp only [rowVal, show ¬ (0 = 7 ∧ j = B.d) by omega, ↓reduceIte, selTableRowVal, selTableOf,
      selectMlocOf, SelectLevelMetaLoc.entry, Nat.mul_zero, Nat.add_zero]
    split_ifs with h
    · exact hlvl _ (by omega) (by omega)
    · rfl
  intro mem1 pos1 R1 hR1 hdone1
  have hok1 := hok0.transfer hR1
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR1 hok0 hdone0
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok1
  -- Row 1: the vertex caps.
  refine row_step hrow (dst := metaBase + 2 + (B.d + 1)) (src := metaBase + 2) (kk := 0)
    (c := B.vCap) (step := 0) (by eval_expr) (by omega) hw1 hmetaW' (by omega)
    (fun j _ => by omega) (by omega) (by omega) (Or.inl (by omega)) (by omega) hdone1
    (fun j hj => ?_) ?_
  · simp [rowVal, selTableRowVal, selTableOf, selectMlocOf, SelectLevelMetaLoc.entry]
  intro mem2 pos2 R2 hR2 hdone2
  have hok2 := hok1.transfer hR2
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR2 hok1 hdone1
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok2
  -- Row 2: the edge caps.
  refine row_step hrow (dst := metaBase + 2 + 2 * (B.d + 1)) (src := metaBase + 2) (kk := 0)
    (c := B.eCap) (step := 0) (by eval_expr) (by omega) hw1 hmetaW' (by omega)
    (fun j _ => by omega) (by omega) (by omega) (Or.inl (by omega)) (by omega) hdone2
    (fun j hj => ?_) ?_
  · simp [rowVal, selTableRowVal, selTableOf, selectMlocOf, SelectLevelMetaLoc.entry]
  intro mem3 pos3 R3 hR3 hdone3
  have hok3 := hok2.transfer hR3
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR3 hok2 hdone2
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok3
  -- Row 3: the potentials.
  refine row_step hrow (dst := metaBase + 2 + 3 * (B.d + 1)) (src := metaBase + 2) (kk := 0)
    (c := B.base + (4 + 7 * B.vCap + 9 * B.eCap))
    (step := 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)
    (by eval_expr) (by omega) hw1 hmetaW' (by omega) (fun j hj => by have := hjS j hj; omega)
    (by omega) (by omega) (Or.inl (by omega)) (by omega) hdone3 (fun j hj => ?_) ?_
  · simp only [rowVal, show ¬ (3 = 7 ∧ j = B.d) by omega, ↓reduceIte, selTableRowVal,
      Nat.not_lt_zero, ite_false, selTableOf, selectMlocOf, SelectLevelMetaLoc.entry,
      SelectBlocksLoc.phiPtr, SelectBlocksLoc.fPtr, hS, dynGraphSize]
    ring
  intro mem4 pos4 R4 hR4 hdone4
  have hok4 := hok3.transfer hR4
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR4 hok3 hdone3
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok4
  -- Row 4: the core lengths, owned by the blocks.
  refine row_step hrow (dst := metaBase + 2 + 4 * (B.d + 1)) (src := metaBase + 2) (kk := 0)
    (c := B.base + (4 + 7 * B.vCap + 9 * B.eCap) + B.vCap * B.Lk)
    (step := 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)
    (by eval_expr) (by omega) hw1 hmetaW' (by omega) (fun j hj => by have := hjS j hj; omega)
    (by omega) (by omega) (Or.inl (by omega)) (by omega) hdone4 (fun j hj => ?_) ?_
  · simp only [rowVal, show ¬ (4 = 7 ∧ j = B.d) by omega, ↓reduceIte, selTableRowVal,
      Nat.not_lt_zero, ite_false, selTableOf, selectMlocOf, SelectLevelMetaLoc.entry,
      SelectBlocksLoc.lenPtr, SelectBlocksLoc.phiPtr, SelectBlocksLoc.fPtr, hS, dynGraphSize]
    ring
  intro mem5 pos5 R5 hR5 hdone5
  have hok5 := hok4.transfer hR5
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR5 hok4 hdone4
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok5
  -- Row 5: the embedding tables.
  refine row_step hrow (dst := metaBase + 2 + 5 * (B.d + 1)) (src := metaBase + 2) (kk := 0)
    (c := B.base + (4 + 7 * B.vCap + 9 * B.eCap) + B.vCap * B.Lk + B.eCap * B.Lk)
    (step := 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)
    (by eval_expr) (by omega) hw1 hmetaW' (by omega) (fun j hj => by have := hjS j hj; omega)
    (by omega) (by omega) (Or.inl (by omega)) (by omega) hdone5 (fun j hj => ?_) ?_
  · simp only [rowVal, show ¬ (5 = 7 ∧ j = B.d) by omega, ↓reduceIte, selTableRowVal,
      Nat.not_lt_zero, ite_false, selTableOf, selectMlocOf, SelectLevelMetaLoc.entry,
      SelectBlocksLoc.embPtr, SelectBlocksLoc.lenPtr, SelectBlocksLoc.phiPtr,
      SelectBlocksLoc.fPtr, hS, dynGraphSize]
    ring
  intro mem6 pos6 R6 hR6 hdone6
  have hok6 := hok5.transfer hR6
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR6 hok5 hdone5
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok6
  -- Row 6: the forests.
  refine row_step hrow (dst := metaBase + 2 + 6 * (B.d + 1)) (src := metaBase + 2) (kk := 0)
    (c := B.base)
    (step := 4 + 7 * B.vCap + 9 * B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot)
    (by eval_expr) (by omega) hw1 hmetaW' (by omega) (fun j hj => by have := hjS j hj; omega)
    (by omega) (by omega) (Or.inl (by omega)) (by omega) hdone6 (fun j hj => ?_) ?_
  · simp only [rowVal, show ¬ (6 = 7 ∧ j = B.d) by omega, ↓reduceIte, selTableRowVal,
      Nat.not_lt_zero, ite_false, selTableOf, selectMlocOf, SelectLevelMetaLoc.entry,
      SelectBlocksLoc.fPtr, hS]
  intro mem7 pos7 R7 hR7 hdone7
  have hok7 := hok6.transfer hR7
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR7 hok6 hdone6
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok7
  -- Row 7: the active sparsifiers (`j < d`), with `j = d` overwritten below by `pLast`.
  refine row_step hrow (dst := metaBase + 2 + 7 * (B.d + 1)) (src := lvlMeta + B.d + 1)
    (kk := B.d - 1) (c := B.lastGPtr) (step := 0) (by eval_expr) (by omega) hw1 hmetaW'
    (by omega) (fun j _ => by omega) (by omega) hlast' (by omega) (by omega) hdone7
    (fun j hj => ?_) ?_
  · by_cases hjd : j < B.d
    · have hne : j ≠ B.d := by omega
      simp only [rowVal, hne, and_false, ↓reduceIte, SelectLevelMetaLoc.entry,
        sPtr_row_lt B metaBase lvlMeta pLast mem hjd, selTableRowVal]
      by_cases hlt : j + 1 < B.d
      · have hlt' : j < B.d - 1 := by omega
        rw [ite_eq_left hlt', ite_eq_left hlt', hdone7.2 (lvlMeta + B.d + 1 + j) (by omega)]
        exact hlvl _ (by omega) (by omega)
      · have hlt' : ¬ j < B.d - 1 := by omega
        rw [ite_eq_right hlt', ite_eq_right hlt']
    · have hjeq : j = B.d := by omega
      subst hjeq
      simp only [rowVal, true_and, ↓reduceIte, selTableRowVal, show ¬ B.d < B.d - 1 by omega,
        Nat.mul_zero, Nat.add_zero]
  intro mem8 pos8 R8 hR8 hdone8
  have hok8 := hok7.transfer hR8
  clear r1 r2 r3 r4 r5 r7 r8 r9 r10 r11 r12 r14 r15 hR8 hok7 hdone7
  obtain ⟨r1, r2, r3, r4, r5, r7, r8, r9, r10, r11, r12, r14, r15⟩ := id hok8
  -- Overwrite `smEntryAddr metaBase B.d 7 B.d` with `pLast`.
  refine runs_seq_store_flat (x := metaBase + 2 + 7 * (B.d + 1) + B.d) (v := pLast)
    (by eval_expr) (by eval_expr) ?_
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · refine ⟨rfl, ⟨?_, ?_, fun j hj => ?_⟩, fun a ha => ?_⟩
    · show Function.update mem8 (metaBase + 2 + 7 * (B.d + 1) + B.d) pLast (metaBase + smG0Off) = B.g0Ptr
      rw [Function.update_of_ne (by unfold smG0Off; omega)]
      have h0 := hdone8.2 metaBase (Or.inl (by omega))
      rw [show metaBase + smG0Off = metaBase from rfl, h0, Function.update_of_ne (by omega),
        Function.update_self]
    · show Function.update mem8 (metaBase + 2 + 7 * (B.d + 1) + B.d) pLast (metaBase + smDOff) = B.d
      rw [Function.update_of_ne (by unfold smDOff; omega)]
      have h1 := hdone8.2 (metaBase + 1) (Or.inl (by omega))
      rw [show metaBase + smDOff = metaBase + 1 from rfl, h1, Function.update_self]
    · have hj' : j < B.d + 1 := Nat.lt_succ_of_le hj
      have he : ∀ b < 7,
          Function.update mem8 (metaBase + 2 + 7 * (B.d + 1) + B.d) pLast
            (smEntryAddr metaBase B.d b j) =
          (selTableOf B metaBase lvlMeta pLast mem).entry b j := by
        intro b hb
        have hne : smEntryAddr metaBase B.d b j ≠ metaBase + 2 + 7 * (B.d + 1) + B.d := by
          unfold smEntryAddr smTableOff
          have : b * (B.d + 1) + j < 7 * (B.d + 1) := row_lt hb hj'
          omega
        rw [Function.update_of_ne hne]
        have h1 := hdone8.1 b (by omega) j hj'
        simpa [smEntryAddr, smTableOff, rowVal, show ¬ (b = 7 ∧ j = B.d) by omega] using h1
      refine ⟨he 0 (by omega), he 1 (by omega), he 2 (by omega), he 3 (by omega),
        he 4 (by omega), he 5 (by omega), he 6 (by omega), ?_⟩
      by_cases hjd : j = B.d
      · subst hjd
        simp [smEntryAddr, smTableOff, selTableOf, selectMlocOf]
      · have hne : smEntryAddr metaBase B.d 7 j ≠ metaBase + 2 + 7 * (B.d + 1) + B.d := by
          unfold smEntryAddr smTableOff; omega
        show Function.update mem8 (metaBase + 2 + 7 * (B.d + 1) + B.d) pLast
            (smEntryAddr metaBase B.d 7 j) = (selTableOf B metaBase lvlMeta pLast mem).sPtr j
        rw [Function.update_of_ne hne]
        have h1 := hdone8.1 7 (by omega) j hj'
        simpa [smEntryAddr, smTableOff, rowVal, hjd, SelectLevelMetaLoc.entry] using h1
    · show Function.update mem8 (metaBase + 2 + 7 * (B.d + 1) + B.d) pLast a = mem a
      have ha' : a < metaBase ∨ metaBase + 2 + 8 * (B.d + 1) ≤ a := by rw [hmeta] at ha; omega
      rw [Function.update_of_ne (by omega), hdone8.2 a (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · simp only [selTableWriteContract, Expr.size_const, Expr.size_reg, Expr.size_bin,
      argsSize_cons, argsSize_nil]
    omega

/-- **The table write keeps the level blocks**, when they lie off the table. -/
theorem selTableWrite_keeps_blocks {w : ℕ} {B : SelectBlocksLoc} {metaBase lvlMeta P pLast : ℕ}
    {args : List ℕ} {mem mem' : ℕ → ℕ} {ret : ℕ} {D : SelBlocksData}
    (hpost : (selTableWriteContract w B metaBase lvlMeta pLast).post args mem ret mem')
    (hoff : metaBase + selectLevelMetaSize B.d ≤ B.base ∨ B.endAddr ≤ metaBase)
    (hblk : SelBlocksDataAt mem B P D pLast) : SelBlocksDataAt mem' B P D pLast :=
  hblk.of_agree fun a h1 h2 => hpost.2.2 a (by omega)

end MinCostFlow.MinRatio
