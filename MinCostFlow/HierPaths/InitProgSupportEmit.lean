module

public import MinCostFlow.HierPaths.InitProgSupportModel

/-!
# Emitting support columns

Each terminal or walk position writes its three consecutive key or
payload words. The same loop handles a table of owners and a walk row.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Three words in one column, for a terminal or a walk position. -/
def initSupportWords (keys walk : Bool) (read : ℕ → ℕ) (row i : ℕ) : List ℕ :=
  if keys then [read i, read i, read i] else
    if walk then [1, row, i] else [0, i, 0]

/-- Arguments are source address, length, connector number, and output address. -/
def initSupportEmit (keys walk : Bool) : Stmt :=
  forRange 4 (.const 0) (.reg 1)
    (.assign 5 (if keys then .load (.bin .add (.reg 0) (.reg 4))
      else .const (if walk then 1 else 0)) ;;
     .assign 6 (.reg 3) ;;
     storeSeq (if keys then [5, 5, 5] else if walk then [5, 2, 4] else [5, 4, 5]) 0
       (.assign 3 (.bin .add (.reg 6) (.const 3)))) ;;
  .ret (.reg 3)

theorem initSupportEmit_noRand (keys walk : Bool) : (initSupportEmit keys walk).NoRand := by
  cases keys <;> cases walk <;> simp [initSupportEmit, storeSeq, forRange, forUp, Stmt.NoRand]

private theorem initSupportWords_length (keys walk : Bool) (read : ℕ → ℕ) (row i : ℕ) :
    (initSupportWords keys walk read row i).length = 3 := by
  cases keys <;> cases walk <;> rfl

/-- The emitter preserves all cells outside its output and takes linear time. -/
def initSupportEmitContract (w : ℕ) (keys walk : Bool) (l : List ℕ) (row : ℕ) : Contract where
  pre args mem := ∃ src dst, args = [src, l.length, row, dst] ∧ ListAt mem src l ∧
    src + l.length ≤ dst ∧ dst + 3 * l.length < 2 ^ w ∧ 3 < 2 ^ w
  post args mem r mem' := ∃ src dst, args = [src, l.length, row, dst] ∧
    r = dst + 3 * l.length ∧
    ListAt mem' dst (initAppendPrefix (initSupportWords keys walk (l.getD · 0) row) l.length) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := 50 * l.length + 15

theorem initSupportPrefix_length (keys walk : Bool) (read : ℕ → ℕ) (row n : ℕ) :
    (initAppendPrefix (initSupportWords keys walk read row) n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [initAppendPrefix_succ, List.length_append, ih, initSupportWords_length]
    omega

theorem initSupportEmit_meetsContract {w f row : ℕ} {keys walk : Bool} {l : List ℕ}
    {p : Program} (hp : p.procs[f]? = some (initSupportEmit keys walk)) :
    MeetsContract w p f (initSupportEmitContract w keys walk l row) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨src, dst, rfl, hl, hsep, hroom, h3⟩ := hpre
  let n := l.length
  let chunks := initSupportWords keys walk (l.getD · 0) row
  let R := fun (s : State) => s.regs 0 = src ∧ s.regs 1 = n ∧ s.regs 2 = row
  have h1 : 1 < 2 ^ w := by omega
  have hloop := initAppendLoop_triple (w := w) (p := p) (dstReg := 3) (idxReg := 4)
    (hi := .reg 1) (body :=
      .assign 5 (if keys then .load (.bin .add (.reg 0) (.reg 4))
        else .const (if walk then 1 else 0)) ;;
      .assign 6 (.reg 3) ;;
      storeSeq (if keys then [5, 5, 5] else if walk then [5, 2, 4] else [5, 4, 5]) 0
        (.assign 3 (.bin .add (.reg 6) (.const 3))))
    R chunks (fun _ => 39) n dst mem (by decide) h1 (hw _ (by simp [n]))
    (fun s _ hs => by simpa [R] using hs) (fun _ hs => Expr.eval_reg_of_eq hs.2.1) ?_
  · refine runs_start_le ?_
    unfold initSupportEmit
    refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
    intro s ⟨_, hptr, hwords, hf⟩
    rw [initSupportPrefix_length] at hptr
    refine runs_ret_le (v := s.regs 3) (Expr.eval_reg_of_eq rfl)
      ⟨src, dst, rfl, hptr, hwords, fun y hy => hf y (by
        rw [initSupportPrefix_length, ← hptr]; exact hy)⟩ ?_
    simp [initSupportEmitContract, rangeCost_const, Expr.size, n]
    omega
  intro i hi s hR hidx hout hf st ω' hs
  subst st
  obtain ⟨r0, r1, r2⟩ := hR
  let out := dst + 3 * i
  have hout' : s.regs 3 = out := by simpa [chunks, initSupportPrefix_length, out] using hout
  have hb : out + 3 < 2 ^ w := by dsimp [out]; omega
  have hi' : i < l.length := hi
  have hm : s.mem (src + i) = l.getD i 0 := by
    rw [List.getD_eq_getElem _ _ hi']
    exact (hf _ (by omega)).trans (hl i hi')
  have hfinish (rs : List ℕ) (v : ℕ) (hlen : rs.length = 3)
      (hv : Expr.eval w s (if keys then .load (.bin .add (.reg 0) (.reg 4))
        else .const (if walk then 1 else 0)) = v)
      (hwords : rs.map (fun j => (Function.update (Function.update s.regs 5 v) 6 out) j) =
        chunks i) :
      ∃ o st' c', Runs w p ω'
        (.assign 5 (if keys then .load (.bin .add (.reg 0) (.reg 4))
          else .const (if walk then 1 else 0)) ;; .assign 6 (.reg 3) ;;
          storeSeq rs 0 (.assign 3 (.bin .add (.reg 6) (.const 3)))) s o st' c' ∧
        normalPost (fun t => R t ∧ t.regs 4 = i ∧
          t.regs 3 = dst + (initAppendPrefix chunks (i + 1)).length ∧
          ListAt t.mem (dst + (initAppendPrefix chunks i).length) (chunks i) ∧
          ∀ y, y < dst + (initAppendPrefix chunks i).length ∨ dst + (initAppendPrefix chunks (i + 1)).length ≤ y →
            t.mem y = s.mem y) o st' ∧ 0 + c' ≤ 39 := by
    refine runs_seq_assign_le hv ?_
    refine runs_seq_assign_le (Expr.eval_reg_of_eq (v := out) (by simpa using hout')) ?_
    refine runs_storeSeq rs 0 _ _ _ rfl (by simpa [hlen] using hb) ?_
    intro mem' hmem hfr
    refine runs_assign_le (v := out + 3)
      (Expr.eval_add (Expr.eval_reg_of_eq (r := 6) (v := out)
        (st := {s with regs := Function.update (Function.update s.regs 5 v) 6 out, mem := mem'})
        (by exact Function.update_self 6 out (Function.update s.regs 5 v))) (Expr.eval_const h3) hb) ?_ ?_
    refine ⟨⟨by simpa using r0, by simpa using r1, by simpa using r2⟩, by simpa using hidx, ?_, ?_, ?_⟩
    · simp [chunks, initSupportPrefix_length, out]; omega
    · rw [← hwords]
      rw [show dst + (initAppendPrefix chunks i).length = out by
        simp [chunks, initSupportPrefix_length, out]]
      change ListAt mem' out _
      intro j hj
      rw [List.getElem_map]
      simpa using hmem j (by simpa using hj)
    · intro y hy
      apply hfr
      simpa [chunks, initSupportPrefix_length, hlen, hout', out, Nat.mul_add, Nat.add_assoc] using hy
    · cases keys <;> cases walk <;> simp [Expr.size, hlen] <;> omega
  refine runs_start_le ?_
  cases keys <;> cases walk
  · exact hfinish [5, 4, 5] 0 rfl (Expr.eval_const (by change 0 < 2 ^ w; omega)) (by simp [chunks, initSupportWords, hidx])
  · exact hfinish [5, 2, 4] 1 rfl (Expr.eval_const h1) (by simp [chunks, initSupportWords, r2, hidx])
  all_goals
    exact hfinish [5, 5, 5] (l.getD i 0) rfl
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq hidx)
        (by omega)) hm) (by simp [chunks, initSupportWords])

end MinCostFlow.HierPaths

end
