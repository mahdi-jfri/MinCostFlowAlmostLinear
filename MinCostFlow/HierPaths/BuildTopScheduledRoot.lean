module

public import MinCostFlow.HierPaths.BuildTopScheduledGraphs
public import MinCostFlow.HierPaths.BuildTopRootModule
public import MinCostFlow.LowStretch.ProgChildIota

/-! # Seeding the depth recursion with the padded root -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.LowStretch

/-- Write the initial graph directory and the pointer used by the first schedule row. -/
def buildTopSeedRoot : Stmt :=
  .store (.reg 0) (.reg 1) ;;
  .store (.reg 2) (.reg 0) ;;
  .ret (.reg 0)

theorem buildTopSeedRoot_noRand : buildTopSeedRoot.NoRand := by
  simp [buildTopSeedRoot, Stmt.NoRand]

/-- The two stores preserve the encoded root graph when their cells are outside it. -/
theorem buildTopSeedRoot_meetsContract {w f dir graph cell : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildTopSeedRoot) :
    MeetsContract w p f {
      pre := fun args _ => args = [dir,graph,cell] ∧ dir ≠ cell
      post := fun _ mem v mem' => v = dir ∧ mem' dir = graph ∧ mem' cell = dir ∧
        ∀ a, a ≠ dir → a ≠ cell → mem' a = mem a
      cost := fun _ _ => 12 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hne⟩ := hpre
  refine runs_start_le ?_
  unfold buildTopSeedRoot
  refine runs_seq_store_le (x := dir) (v := graph) (Expr.eval_reg_of_eq rfl)
    (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_store_le (x := cell) (v := dir) (Expr.eval_reg_of_eq rfl)
    (Expr.eval_reg_of_eq rfl) ?_
  refine runs_ret_le (v := dir) (Expr.eval_reg_of_eq rfl)
    ⟨rfl,by simp [Function.update_of_ne hne],by simp,?_⟩ ?_
  · intro a hd hc
    simp [Function.update_of_ne hd,Function.update_of_ne hc,startState]
  · simp [Expr.size]

/-- A single directory entry is the graph layout for depth zero. -/
theorem buildTopScheduledRoot_graphsAt {table count term x b m d dir graph : ℕ}
    {mem : ℕ → ℕ} {G : Cited.Graph} (hd : mem dir = graph)
    (hg : GraphAt mem graph G) :
    (buildTopScheduledDepth table count term x b m d 0 dir
      (fun _ => graph) (fun _ => G)).graphsAt mem := by
  intro j hj
  change j < numGroups x b 0 at hj
  have hj0 : j = 0 := by simpa [numGroups] using hj
  subst j
  exact ⟨show mem (dir + 0) = graph from hd,hg⟩

/-- Write the terminal table, then install the first parent directory. -/
def buildTopSeedDepth (iota seed : ℕ) : Stmt :=
  .call 5 iota [.reg 0, .reg 1, .const 1, .const 0] ;;
  .call 5 seed [.reg 2, .reg 3, .reg 4] ;;
  .ret (.reg 5)

theorem buildTopSeedDepth_noRand (iota seed : ℕ) : (buildTopSeedDepth iota seed).NoRand := by
  simp [buildTopSeedDepth, Stmt.NoRand]

/-- The seed installs both root inputs and frames all other addresses. -/
theorem buildTopSeedDepth_meetsContract {w f iota seed P term dir graph cell : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopSeedDepth iota seed))
    (hi : p.HasAt iota [iotaP]) (hs : p.procs[seed]? = some buildTopSeedRoot) :
    MeetsContract w p f {
      pre := fun args _ => args = [P,term,dir,graph,cell] ∧ term + P + 1 < 2 ^ w ∧
        dir ≠ cell ∧ (dir < term ∨ term + P ≤ dir) ∧ (cell < term ∨ term + P ≤ cell)
      post := fun _ mem v mem' => v = dir ∧ mem' dir = graph ∧ mem' cell = dir ∧
        ListAt mem' term (List.range P) ∧
        ∀ a, (a < term ∨ term + P ≤ a) → a ≠ dir → a ≠ cell → mem' a = mem a
      cost := fun _ _ => 30 * (P + 1) + 40 } := by
  refine meetsContract_of_runs hf fun args mem pos ω hwords hpre => ?_
  obtain ⟨rfl,hroom,hne,hdir,hcell⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := Nat.two_pow_pos _
  refine runs_start_le ?_
  unfold buildTopSeedDepth
  refine runs_seq_call_le (iotaP_spec hi) (vs := [P,term,1,0]) ?_ ?_
    ⟨P,term,1,0,rfl,hroom,by omega⟩ ?_
  · simp [evalArgs, Expr.eval, h1,h0, startState]
  · intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  intro v mem₁ pos₁ hp₁
  obtain ⟨hrow,hframe⟩ := hp₁ P term 1 0 rfl
  refine runs_seq_call_le (buildTopSeedRoot_meetsContract hs) (vs := [dir,graph,cell])
    rfl ?_ ⟨rfl,hne⟩ ?_
  · intro a ha
    exact hwords _ (List.mem_append_right [P,term] ha)
  intro v' mem₂ pos₂ ⟨hv,hd,hc,hf'⟩
  refine runs_ret_le (v := dir) (Expr.eval_reg_of_eq (by simpa only [Function.update_self] using hv))
    ⟨rfl,hd,hc,?_,?_⟩ ?_
  · intro i hi'
    have hlt : i < P := by simpa using hi'
    change mem₂ (term + i) = (List.range P)[i]
    have hdi : term + i ≠ dir := by rcases hdir with h | h <;> omega
    have hci : term + i ≠ cell := by rcases hcell with h | h <;> omega
    rw [hf' _ hdi hci]
    simpa using hrow i hlt
  · intro a ha hd' hc'
    exact (hf' a hd' hc').trans (hframe a ha)
  · simp [argsSize, Expr.size, iotaC]
    omega

end MinCostFlow.HierPaths

end
