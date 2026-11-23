module

public import MinCostFlow.HierPaths.BuildTopReply

/-!
# Locating the next depth's graphs

Each child index determines its parent by quotient and its local graph
row by remainder. The reply directory locates the parent block.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- A child graph pointer is read from the graph section of the parent's reply. -/
def buildTopNextRow (read : ℕ) : Stmt :=
  .assign 4 (.bin .div (.reg 1) (.reg 2)) ;;
  .assign 5 (.bin .mod (.reg 1) (.reg 2)) ;;
  .call 6 read [.load (.bin .add (.reg 0) (.reg 4)), .const 0, .reg 2, .reg 5] ;;
  .store (.bin .add (.reg 3) (.reg 1)) (.reg 6) ;;
  .ret (.reg 6)

theorem buildTopNextRow_noRand (read : ℕ) : (buildTopNextRow read).NoRand := by
  simp [buildTopNextRow, Stmt.NoRand]

/-- The address of a child graph inside its parent's encoded reply. -/
def buildTopChildAddr (a k c : ℕ) (D : BuildLevelData) : ℕ :=
  a + 4 + (k + 1) + initCSRPrefix (fun i => (D.host i).encode) c

/-- The first reply section contains exactly the child graph rows. -/
theorem buildTopChildAddr_graphAt {mem : ℕ → ℕ} {a k c : ℕ} {D : BuildLevelData}
    (h : ListAt mem a (D.encode k)) (hc : c < k) :
    Spanner.GraphAt mem (buildTopChildAddr a k c D) (D.host c) := by
  have h₀ := listAt_csrList_get (i := 0) (k := 3)
    (f := fun i => ([csrList k (fun j => (D.host j).encode),
      csrList k (fun j => csrList (D.host j).m (D.emb j)),
      csrList (k*k) (fun i =>
        let pair := D.conn (i/k) (i%k)
        csrList pair.length (fun j => connWords (pair.getD j (0,0,[]))))] : List (List ℕ)).getD i [])
    h (by decide)
  change ListAt mem (a + 4) (csrList k (fun j => (D.host j).encode)) at h₀
  exact listAt_csrList_get h₀ hc

def buildTopReplySections (D : BuildLevelData) (k : ℕ) : List (List ℕ) :=
  [csrList k (fun j => (D.host j).encode),
   csrList k (fun j => csrList (D.host j).m (D.emb j)),
   csrList (k*k) (fun i =>
      let pair := D.conn (i/k) (i%k)
      csrList pair.length (fun j => connWords (pair.getD j (0,0,[]))))]

def buildTopNextRowContract (w i k a : ℕ) (D : BuildLevelData) : Contract :=
  {
      pre := fun args mem => ∃ dir dst, args = [dir, i, k, dst] ∧ 0 < k ∧
        dir + i / k < 2 ^ w ∧ dst + i < 2 ^ w ∧ mem (dir + i / k) = a ∧
        ListAt mem a (D.encode k) ∧ a + (D.encode k).length < 2 ^ w
      post := fun args mem v mem' => ∃ dir dst, args = [dir, i, k, dst] ∧
        v = buildTopChildAddr a k (i % k) D ∧ mem' = Function.update mem (dst + i) v
      cost := fun _ _ => 80 }

/-- The selected pointer is stored in the next directory. All other cells are preserved. -/
theorem buildTopNextRow_meetsContract {w f read seek i k a : ℕ} {D : BuildLevelData}
    {p : Program} (hp : p.procs[f]? = some (buildTopNextRow read))
    (hr : p.procs[read]? = some (buildTopReplyRead seek)) (hs : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f (buildTopNextRowContract w i k a D) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨dir, dst, rfl, hk, hdir, hdst, ha, hdata, hroom⟩ := hpre
  have hword (v : ℕ) (hv : v ∈ [dir,i,k,dst]) : v < 2 ^ w := hw v hv
  have haf : a < 2 ^ w := by omega
  have him : i % k < k := Nat.mod_lt _ hk
  let F := buildTopReplySections D k
  let rows := fun j => (D.host j).encode
  refine runs_start_le ?_
  unfold buildTopNextRow
  refine runs_seq_assign_le (v := i / k) (Expr.eval_div (Expr.eval_reg_of_eq (v := i) rfl)
    (Expr.eval_reg_of_eq (v := k) rfl) (by omega)) ?_
  refine runs_seq_assign_le (v := i % k) (Expr.eval_mod (Expr.eval_reg_of_eq (v := i) rfl)
    (Expr.eval_reg_of_eq (v := k) rfl) (by have := hword k (by simp); omega)) ?_
  refine runs_seq_call_le (buildTopReplyRead_meetsContract (w := w) (sec := 0) (k := k)
    (i := i % k) (sections := F) (rows := rows) hr hs) (vs := [a,0,k,i % k]) ?_ ?_
    ⟨a, rfl, rfl, by decide, him.le, rfl, hdata, hroom⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, hdir, ha]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact haf
    · exact Nat.two_pow_pos _
    · exact hword _ (by simp)
    · exact him.trans (hword _ (by simp))
  intro v mem₁ pos₁ hp'
  obtain ⟨hv, hm⟩ := hp'
  change mem₁ = mem at hm
  subst mem₁
  have hv' : v = buildTopChildAddr a k (i % k) D := by
    change v = initCSRAddr (initCSRAddr a 3 (F.getD · []) 0) k rows (i % k) at hv
    exact hv
  refine runs_seq_store_le (x := dst + i) (v := v) (Expr.eval_add
    (Expr.eval_reg_of_eq (v := dst) rfl) (Expr.eval_reg_of_eq (v := i) rfl) hdst)
    (Expr.eval_reg_of_eq (v := v) rfl) ?_
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq rfl) ⟨dir, dst, rfl, hv', rfl⟩ ?_
  simp [buildTopNextRowContract, buildTopReplyReadContract, Expr.size, argsSize]

end MinCostFlow.HierPaths

end
