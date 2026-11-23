module

public import MinCostFlow.Scaling.LabelStepProgram
import MinCostFlow.Scaling.LabelBounds
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# The bounded machine traversal for distance labels

The procedure follows `LabelState.run`: stop when fuel is zero or the
pending list is empty, otherwise compute one step and recurse. A uniform
label bound pays for the signed subtraction. Removed adjacency entries pay
for copied nodes, so both machine cost and fresh space are linear in the
counted traversal's work and fuel.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,stateBase,fuel,heap]`. -/
def labelRunBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.cond (.bin .eq (.load (.bin .add (.reg 1) (.const 1))) (.const 0)) (.ret (.reg 3))
      (.call 4 step [.reg 0, .reg 1, .reg 3] ;;
       .assign 5 (.bin .sub (.reg 2) (.const 1)) ;;
       .call 6 self [.reg 0, .reg 1, .reg 5, .reg 4] ;;
       .ret (.reg 6)))

/-- The traversal entry followed by its complete single-step module. -/
def labelRunModule (b : ℕ) : List Stmt := labelRunBody b (b+1) :: labelStepModule (b+1)

/-- The numeric budgets cover all labels and allocations in the run. -/
def labelRunContract (w fuel B C : ℕ) {J : Circulation}
    (s : Circulation.LabelState J) : Contract where
  pre args mem := ∃ a base heap, args = [a, base, fuel, heap] ∧
    ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ base ∧
    LabelStateAt mem base heap s ∧ labelNodes J.n base ≤ heap ∧ J.m < 2^w ∧
    (∀ v, (s.labels v).natAbs ≤ B) ∧ (∀ e, (J.cost e).natAbs ≤ C) ∧
    B+(fuel+1)*C < 2^w ∧ s.remaining+1 < 2^w ∧ ZeroFrom mem heap ∧
    heap+2*J.adjacencyMass s.outgoing+2*fuel+2 < 2^w
  post args mem ret mem' := heapArg args ≤ ret ∧
    ret+2*J.adjacencyMass (Circulation.LabelState.run fuel s).1.outgoing ≤
      heapArg args+2*J.adjacencyMass s.outgoing+2*fuel ∧
    LabelStateAt mem' (args.getD 1 0) ret (Circulation.LabelState.run fuel s).1 ∧
    ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x < args.getD 1 0 ∨ labelNodes J.n (args.getD 1 0) ≤ x → mem' x = mem x
  cost _ _ := 100*(Circulation.LabelState.run fuel s).2+1200*fuel+100

/-- The traversal and all installed callees contain no random instruction. -/
theorem labelRunModule_noRand (b : ℕ) : ∀ body ∈ labelRunModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [labelRunBody, Stmt.NoRand, and_self]
  · exact labelStepModule_noRand _ body hb

/-- The machine traversal computes the counted model run, with explicit
amortized space and cost bounds. -/
theorem labelRun_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (labelRunModule b)) {J : Circulation} (fuel B C : ℕ)
    (s : Circulation.LabelState J) : MeetsContract w p b (labelRunContract w fuel B C s) := by
  induction fuel generalizing s B with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, base, heap, rfl, _, _, hstate, _, _, _, _, _, _, hzero, hspace⟩ := hpre
    have hheap : heap < 2^w := by omega
    apply runs_start_le
    unfold labelRunBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change heap ≤ heap ∧ heap+2*J.adjacencyMass s.outgoing ≤ heap+2*J.adjacencyMass s.outgoing+2*0 ∧
          LabelStateAt mem base heap s ∧ ZeroFrom mem heap ∧
          ∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → mem x = mem x
        exact ⟨le_rfl, by omega, hstate, hzero, fun _ _ _ => rfl⟩
      · simp only [labelRunContract, Circulation.LabelState.run, Nat.mul_zero, Nat.add_zero,
          Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  | succ fuel ih =>
    have hkStep := labelStep_meetsContract (w := w) (hasAt_tail hp) s
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, base, heap, rfl, hat, hend, hstate, hnodes, hm, hlabels, hcosts,
      hbudget, hremaining, hzero, hspace⟩ := hpre
    have haWord := hwords a (List.mem_cons_self)
    have hheap : heap < 2^w := by omega
    have hbaseHeap : base ≤ heap := by have hn : base+3+5*J.n ≤ heap := hnodes; omega
    have hbase : base < 2^w := by have hn : base+3+5*J.n ≤ heap := hnodes; omega
    have hbase1 : base+1 < 2^w := by have hn : base+3+5*J.n ≤ heap := hnodes; omega
    have hone : 1 < 2^w := by omega
    have hfuel : fuel+1 < 2^w := by omega
    have hfuel' : fuel < 2^w := by omega
    have hstate0 := hstate
    obtain ⟨ptr, hheader, _⟩ := hstate
    have hlen : mem (base+1) = s.pending.length := hheader 1 (by change 1<2; decide)
    apply runs_start_le
    unfold labelRunBody
    wram_step
    wram_step
    · have hempty : s.pending = [] := List.length_eq_zero_iff.mp (by simpa [startState, hlen] using hcond)
      refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change heap ≤ heap ∧ heap+2*J.adjacencyMass (Circulation.LabelState.run (fuel+1) s).1.outgoing ≤
          heap+2*J.adjacencyMass s.outgoing+2*(fuel+1) ∧
          LabelStateAt mem base heap (Circulation.LabelState.run (fuel+1) s).1 ∧ ZeroFrom mem heap ∧
          ∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → mem x = mem x
        simp only [Circulation.LabelState.run, hempty, ↓reduceIte]
        exact ⟨le_rfl, by omega, hstate0, hzero, fun _ _ _ => True.intro⟩
      · simp only [labelRunContract, Circulation.LabelState.run, hempty, ↓reduceIte,
          Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]; omega
    · have hnonempty : s.pending ≠ [] := by
        intro hh
        simp [startState, hlen, hh] at hcond
      have hstepBudget : ∀ e ∈ s.pending,
          (s.labels (J.tail e)).natAbs+(J.cost e).natAbs < 2^w := by
        intro e _
        have hl := hlabels (J.tail e)
        have hc := hcosts e
        have hmC : C ≤ (fuel+1+1)*C := Nat.le_mul_of_pos_left C (by omega)
        omega
      have hstepSpace : heap+2+2*J.adjacencyMass s.outgoing < 2^w := by omega
      refine runs_seq_call_le hkStep (vs := [a, base, heap]) (by eval_expr) ?_ ?_ ?_
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact haWord
        · exact hbase
        · exact hheap
      · exact ⟨a, base, heap, rfl, hat, hend, hstate0, hnodes, hm, hremaining,
          hstepBudget, hzero, hstepSpace⟩
      · intro nextHeap memS posS hpostS
        obtain ⟨hle, halloc, hstateS, hzeroS, hframeS⟩ := hpostS
        change heap ≤ nextHeap at hle
        change nextHeap+2*J.adjacencyMass s.step.1.outgoing ≤ heap+2*J.adjacencyMass s.outgoing+2 at halloc
        change LabelStateAt memS base nextHeap s.step.1 at hstateS
        change (∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → memS x = mem x) at hframeS
        have hrecSpace : nextHeap+2*J.adjacencyMass s.step.1.outgoing+2*fuel+2 < 2^w := by omega
        have hnextWord : nextHeap < 2^w := by omega
        have hgraphS : ListAt memS a J.solverWords := by
          intro i hi
          rw [hframeS (a+i) (by omega) (Or.inl (by omega))]
          exact hat i hi
        have hrecBudget : B+C+(fuel+1)*C < 2^w := by
          have heq : B+C+(fuel+1)*C = B+(fuel+1+1)*C := by ring
          rw [heq]
          exact hbudget
        have hrecRemaining : s.step.1.remaining+1 < 2^w := by
          have hh := s.step_remaining hnonempty
          omega
        have hkRec := ih (B+C) s.step.1
        refine runs_seq_assign_le (v := fuel) (by
          conv_rhs => rw [← Nat.add_sub_cancel fuel 1]
          exact Expr.eval_sub (a := .reg 2) (b := .const 1) (x := fuel+1) (y := 1)
            (by eval_expr) (by eval_expr) hfuel) ?_
        refine runs_seq_call_le hkRec (vs := [a, base, fuel, nextHeap]) (by eval_expr) ?_ ?_ ?_
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact haWord
          · exact hbase
          · exact hfuel'
          · exact hnextWord
        · exact ⟨a, base, nextHeap, rfl, hgraphS, hend, hstateS,
            hnodes.trans hle, hm, s.step_labels_bound B C hlabels hcosts, hcosts,
            hrecBudget, hrecRemaining, hzeroS, hrecSpace⟩
        · intro ret memR posR hpostR
          obtain ⟨hretlo, hretalloc, hstateR, hzeroR, hframeR⟩ := hpostR
          change nextHeap ≤ ret at hretlo
          change ret+2*J.adjacencyMass (Circulation.LabelState.run fuel s.step.1).1.outgoing ≤
            nextHeap+2*J.adjacencyMass s.step.1.outgoing+2*fuel at hretalloc
          change LabelStateAt memR base ret (Circulation.LabelState.run fuel s.step.1).1 at hstateR
          change (∀ x < nextHeap, x < base ∨ labelNodes J.n base ≤ x → memR x = memS x) at hframeR
          have hretWord : ret < 2^w := by omega
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change heap ≤ ret ∧ ret+2*J.adjacencyMass (Circulation.LabelState.run (fuel+1) s).1.outgoing ≤
              heap+2*J.adjacencyMass s.outgoing+2*(fuel+1) ∧
              LabelStateAt memR base ret (Circulation.LabelState.run (fuel+1) s).1 ∧ ZeroFrom memR ret ∧
              ∀ x < heap, x < base ∨ labelNodes J.n base ≤ x → memR x = mem x
            simp only [Circulation.LabelState.run, hnonempty, ↓reduceIte]
            refine ⟨hle.trans hretlo, by omega, hstateR, hzeroR, ?_⟩
            intro x hx hout
            exact (hframeR x (by omega) hout).trans (hframeS x hx hout)
          · simp only [labelRunContract, labelStepContract, Circulation.LabelState.run,
              hnonempty, ↓reduceIte, argsSize_cons, argsSize_nil, Expr.size_bin,
              Expr.size_load, Expr.size_reg, Expr.size_const]
            omega
end MinCostFlow.Scaling.Machine
