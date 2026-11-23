module

public import MinCostFlow.HierPaths.BuildTopScheduledRoot
public import MinCostFlow.HierPaths.BuildTopScheduleAddress

/-! # Composing the padded root and the recursion seed -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- Place the terminal table immediately after the root procedure's heap.
The directory follows the terminals, followed by the schedule. -/
def buildTopRootSeeded (root seed : ℕ) : Stmt :=
  .call 6 root [.reg 0, .reg 1] ;;
  .assign 7 (.bin .add (.reg 6) (.reg 2)) ;;
  .assign 8 (.bin .add (.reg 7) (.const 1)) ;;
  .call 9 seed [.reg 2, .reg 6, .reg 7, .reg 3,
    buildTopPointerExpr (.reg 8) (.reg 4) (.const 0)] ;;
  .ret (.reg 6)

theorem buildTopRootSeeded_noRand (root seed : ℕ) : (buildTopRootSeeded root seed).NoRand := by
  simp [buildTopRootSeeded, Stmt.NoRand]

def buildTopRootSeededContract (w ga h P n : ℕ) (G : Graph) : Contract :=
  let graph := buildTopRootGraphAddr h G.n G.m
  {
      pre := fun args mem => args = [ga,h,P,graph,n] ∧
        (buildTopRootLayoutContract w G).pre [ga,h] mem ∧
        h + buildTopRootSpace G.n G.m + P + 2 + 13 * n < 2 ^ w
      post := fun _ mem r mem' =>
        let dir := r + P
        let table := dir + 1
        (∃ rootMem, (buildTopRootLayoutContract w G).post [ga,h] mem r rootMem ∧
          ∀ y < r, mem' y = rootMem y) ∧
        mem' dir = graph ∧ mem' (buildTopSchedulePointer table n 0) = dir ∧
        ListAt mem' r (List.range P) ∧
        ZeroFrom mem' (buildTopSchedulePointer table n 0 + 1)
      cost := fun args mem => (buildTopRootLayoutContract w G).cost args mem + 30 * (P + 1) + 100 }

/-- The seeded root retains the root representation and supplies the initial driver inputs. -/
theorem buildTopRootSeeded_meetsContract {w f root seed iota store ga h P n : ℕ}
    {p : Program} {G : Graph}
    (hf : p.procs[f]? = some (buildTopRootSeeded root seed))
    (hr : MeetsContract w p root (buildTopRootLayoutContract w G))
    (hs : p.procs[seed]? = some (buildTopSeedDepth iota store))
    (hi : p.HasAt iota [LowStretch.iotaP]) (hp : p.procs[store]? = some buildTopSeedRoot) :
    MeetsContract w p f (buildTopRootSeededContract w ga h P n G) := by
  refine meetsContract_of_runs hf fun args mem pos ω hword hpre => ?_
  obtain ⟨rfl,hroot,hroom⟩ := hpre
  let graph := buildTopRootGraphAddr h G.n G.m
  refine runs_start_le ?_
  unfold buildTopRootSeeded
  refine runs_seq_call_le hr (vs := [ga,h]) rfl
    (fun a ha => hword a (List.mem_append_left _ ha)) hroot ?_
  intro r mem₁ pos₁ hpost
  obtain ⟨ga',h',he,hG,hOwn,hlo,hhi,hzero,hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl,rfl⟩ := he
  let dir := r + P
  let table := dir + 1
  let cell := buildTopSchedulePointer table n 0
  have hdir : dir < 2 ^ w := by dsimp [dir]; omega
  have htable : table < 2 ^ w := by dsimp [table,dir]; omega
  have hcell : cell < 2 ^ w := by dsimp [cell,table,dir,buildTopSchedulePointer]; omega
  have h13 : 13 < 2 ^ w := by
    obtain ⟨_,_,_,_,_,_,_,_,_,h24⟩ := hroot
    omega
  have hsep : dir < cell := by simp [cell,table,buildTopSchedulePointer]; omega
  refine runs_seq_assign_le (v := dir)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hdir) ?_
  refine runs_seq_assign_le (v := table)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) htable) ?_
  refine runs_seq_call_le (buildTopSeedDepth_meetsContract hs hi hp)
    (vs := [P,r,dir,graph,cell]) ?_ ?_ ⟨rfl,htable,hsep.ne,.inr (le_refl _),.inr hsep.le⟩ ?_
  · have h0 : 0 < 2 ^ w := Nat.two_pow_pos _
    have hm : 13 * n < 2 ^ w := by dsimp [cell,table,dir,buildTopSchedulePointer] at hcell; omega
    have ha : table + 13 * n < 2 ^ w := by simpa [cell,buildTopSchedulePointer] using hcell
    simp [evalArgs, Expr.eval, BinOp.eval, startState, buildTopPointerExpr,
      h0,h13,hm,ha,cell,buildTopSchedulePointer,graph]
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact hword _ (by simp)
    · exact (Nat.le_add_right _ _).trans_lt hdir
    · exact hdir
    · exact hword _ (by simp [graph])
    · exact hcell
  intro u mem₂ pos₂ ⟨_,hd,hc,hterms,hfr⟩
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ?_ ?_
  · refine ⟨⟨mem₁,⟨ga,h,rfl,hG,hOwn,hlo,hhi,hzero,hframe⟩,?_⟩,hd,hc,hterms,?_⟩
    · intro y hy
      change y < r at hy
      have hrd : r ≤ dir := Nat.le_add_right _ _
      exact hfr y (.inl hy) (by omega) (by omega)
    · intro y hy
      change cell + 1 ≤ y at hy
      have hrd : r ≤ dir := Nat.le_add_right _ _
      exact (hfr y (.inr (by omega)) (by omega) (by omega)).trans (hzero y (by omega))
  · simp [Expr.size,argsSize,buildTopPointerExpr,buildTopRootLayoutContract,
      buildTopRootContract,buildTopPortContract,buildTopRootSeededContract]
    omega

end MinCostFlow.HierPaths

end
