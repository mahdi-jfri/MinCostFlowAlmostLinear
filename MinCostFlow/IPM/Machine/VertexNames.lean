module

public import WordRAM.Layout
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Writing the fixed graph's vertex names

Canonical min-ratio initialization lists the names `0,...,n-1`.
A counted word loop writes this list into fresh heap memory. The
program charges every iteration and preserves all memory outside
its exact output interval, including arbitrary earlier input data.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[n,heap]`. -/
def vertexNamesBody : Stmt :=
  forRange 2 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 1) (.reg 2)) (.reg 2)) ;;
  .ret (.bin .add (.reg 1) (.reg 0))

/-- One counted name-writing entry. -/
def vertexNamesModule : List Stmt := [vertexNamesBody]

/-- Exactly n increasing vertex names, with n allocated words. -/
def vertexNamesContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ n heap,args=[n,heap])
    (fun args _ mem' => ListAt mem' (heapArg args) (List.range (args.getD 0 0)))
    (fun args _ => 30*args.getD 0 0+40) (fun args _ => args.getD 0 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+args.getD 0 0}

/-- Writing vertex names is deterministic. -/
theorem vertexNames_noRand : vertexNamesBody.NoRand := by
  simp [vertexNamesBody,forRange,forUp,Stmt.NoRand]

private theorem names_loop {w n heap : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hw : 1 < 2^w) (hspace : heap+n < 2^w) :
    Triple w p (fun st => st=startState [n,heap] mem pos)
      (forRange 2 (.const 0) (.reg 0) (.store (.bin .add (.reg 1) (.reg 2)) (.reg 2)))
      (normalPost fun st => st.regs 0=n ∧ st.regs 1=heap ∧
        (∀ i < n,st.mem (heap+i)=i) ∧
        (∀ z,z < heap ∨ heap+n ≤ z → st.mem z=mem z))
      (fun _ => 30*n+30) := by
  have hl := Triple.forRange_const (w:=w) (p:=p) (r:=2) (lo:=.const 0) (hi:=.reg 0)
    (body:=.store (.bin .add (.reg 1) (.reg 2)) (.reg 2))
    (P:=fun st => st=startState [n,heap] mem pos)
    (Inv:=fun i st => st.regs 0=n ∧ st.regs 1=heap ∧ st.regs 2=i ∧
      (∀ j < i,st.mem (heap+j)=j) ∧
      (∀ z,z < heap ∨ heap+i ≤ z → st.mem z=mem z))
    5 0 n (Nat.zero_le n) (by omega) (fun _ => by omega)
    (fun st he => by subst st; refine ⟨by eval_expr,?_⟩; simp [startState])
    (fun _ _ _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => by have h0 := hi.1; eval_expr)
    (fun i _ hi => by
      intro st ω hst
      obtain ⟨h0,h1,h2,htable,hframe⟩ := hst
      have haddr : heap+i < 2^w := by omega
      have hiw : i < 2^w := by omega
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨?_,?_,?_,?_,?_⟩,h2⟩
        · simpa using h0
        · simpa using h1
        · simp
        · intro j hj
          dsimp only
          by_cases he : j=i
          · subst j
            simp
          · rw [Function.update_of_ne (by omega)]
            exact htable j (by omega)
        · intro z hz
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe z (by omega)
      · wram_cost)
  refine hl.conseq (fun _ he => he) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.1,ho.2.1,ho.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The machine writes the canonical vertex list in linear time, with
exact heap framing and return pointer. -/
theorem vertexNames_meetsContract {w b : ℕ} {p : Program} (hw : 1 < 2^w)
    (hp : p.HasAt b vertexNamesModule) : MeetsContract w p b (vertexNamesContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨n,heap,rfl⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+n < 2^w at hspace
  apply runs_start_le
  unfold vertexNamesBody
  refine runs_seq_triple_le (names_loop p mem pos hw hspace) rfl ?_
  intro st ⟨h0,h1,htable,hframe⟩
  refine runs_ret_le (v:=heap+n) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+n ∧ heap+n ≤ heap+n ∧ (∀ x < heap,st.mem x=mem x) ∧
      ZeroFrom st.mem (heap+n) ∧ ListAt st.mem heap (List.range n)) ∧ heap+n=heap+n
    refine ⟨⟨by omega,le_rfl,fun x hx => hframe x (Or.inl hx),?_,?_⟩,rfl⟩
    · intro x hx
      exact (hframe x (Or.inr hx)).trans (hzero x (by omega))
    · intro i hi
      rw [List.length_range] at hi
      rw [htable i hi,List.getElem_range (by simpa using hi)]
  · simp only [vertexNamesContract,heapContract,List.getD_cons_zero,
      Expr.size_bin,Expr.size_reg]
    omega

end MinCostFlow.IPM.Machine
