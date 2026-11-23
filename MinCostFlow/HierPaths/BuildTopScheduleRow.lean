module

public import MinCostFlow.HierPaths.BuildTopSchedulePlayers

/-! # Writing all thirteen columns of a schedule row -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The three writers use disjoint columns of the same row. -/
def buildTopScheduleRow (players geometry addresses : ℕ) : Stmt :=
  .call 12 players [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] ;;
  .call 12 geometry [.reg 8, .reg 9, .reg 10, .bin .add (.reg 0) (.const 3)] ;;
  .call 12 addresses [.reg 11, .reg 13, .reg 8, .reg 10, .reg 0] ;;
  .ret (.reg 0)

theorem buildTopScheduleRow_noRand (players geometry addresses : ℕ) :
    (buildTopScheduleRow players geometry addresses).NoRand := by
  simp [buildTopScheduleRow, Stmt.NoRand]

/-- A row uses the actual player parameters and computed addresses and geometry. -/
theorem buildTopScheduleRow_meetsContract
    {w f players geometry addresses x b table n j : ℕ} {p : Program}
    {D : BuildTopDepthInput}
    (hf : p.procs[f]? = some (buildTopScheduleRow players geometry addresses))
    (hplayers : p.procs[players]? = some buildTopSchedulePlayers)
    (hgeometry : p.procs[geometry]? = some buildTopScheduleGeometry)
    (haddresses : p.procs[addresses]? = some buildTopScheduleAddresses)
    (hs : D.childSize = groupSize x b (j + 1))
    (hk : D.branch = branching x b j) (hn : D.count = numGroups x b j)
    (hd : D.replyDir = buildTopScheduleReplies table n x j) :
    let row := table + 13 * j
    MeetsContract w p f {
      pre := fun args _ => args = [row,D.termBase,D.scale,D.rank,D.degree,D.pathLog,
        D.coreLog,D.denominator,x,b,j,table,0,n] ∧ j < n ∧ n ≤ leafDepth x b ∧
        0 < b ∧ b ≤ x ∧ 2 ^ x < 2 ^ w ∧ buildTopScheduleEnd table n x < 2 ^ w
      post := fun _ mem v mem' => v = row ∧
        ListAt mem' row (D.scheduleWords (buildTopSchedulePointer table n j)
          (buildTopSchedulePointer table n (j + 1))) ∧
        ∀ y, y < row ∨ row + 13 ≤ y → mem' y = mem y
      cost := fun _ _ => 300 } := by
  dsimp only
  refine meetsContract_of_runs hf fun args mem pos ω hwords hpre => ?_
  obtain ⟨rfl,hj,hdepth,hb,hbx,hP,hend⟩ := hpre
  let row := table + 13 * j
  obtain ⟨hjw,hm⟩ := (buildTopScheduleWords_fit hb hbx hP).2 j (hj.trans_le hdepth)
  obtain ⟨hr,heq,hrep,hspan⟩ := buildTopSchedule_disjoint
    (table := table) (x := x) (b := b) hj
  have hrow : row + 13 < 2 ^ w := by
    dsimp [row]
    omega
  refine runs_start_le ?_
  unfold buildTopScheduleRow
  refine runs_seq_call_le (buildTopSchedulePlayers_meetsContract hplayers)
    (vs := [row,D.termBase,D.scale,D.rank,D.degree,D.pathLog,D.coreLog,D.denominator])
    rfl ?_ ⟨rfl,by omega⟩ ?_
  · intro v hv
    exact hwords v (List.mem_append_left _ hv)
  intro v₁ mem₁ pos₁ hp₁
  refine runs_seq_call_le (buildTopScheduleGeometry_meetsContract hgeometry)
    (vs := [x,b,j,row + 3]) ?_ ?_ ⟨rfl,hP,hjw,hm,by omega⟩ ?_
  · have h3 : 3 < 2 ^ w := by omega
    have haddr : table + 13 * j + 3 < 2 ^ w := by dsimp [row] at hrow; omega
    simp [evalArgs, Expr.eval, BinOp.eval, startState, row, h3, haddr]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · omega
  intro v₂ mem₂ pos₂ hp₂
  refine runs_seq_call_le (buildTopScheduleAddresses_meetsContract haddresses)
    (vs := [table,n,x,j,row]) rfl ?_ ⟨rfl,hj,hP,hend⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact hwords _ (by simp [row])
  intro v₃ mem₃ pos₃ hp₃
  refine runs_ret_le (v := row) (Expr.eval_reg_of_eq rfl) ⟨rfl,?_,?_⟩ ?_
  · rw [hp₃.2]
    apply buildTopScheduleAddress_completesRow hd
    intro k hlen hlo hhi
    interval_cases k <;> simp [hp₂.2, hp₁.2, BuildTopDepthInput.scheduleWords, row,
      hs, hk, hn, Nat.add_assoc, Function.update_of_ne]
  · intro y hy
    rw [hp₃.2,hp₂.2,hp₁.2]
    dsimp only
    repeat rw [Function.update_of_ne (by dsimp [row] at hy ⊢; omega)]
    rfl
  · simp [argsSize, Expr.size]

end MinCostFlow.HierPaths

end
