module

public import MinCostFlow.IPM.Machine.InitialEndpointSums
public import WordRAM.Layout
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Accumulating midpoint capacity at one set of endpoints

Lemma 4.12 (page 31, Appendix B.1 page 92) needs the midpoint routing
deficit at each vertex. Scan the original edges once for tails and once
for heads. This procedure accumulates one of the two capacity tables,
using unsigned exact additions into fresh zero memory. Each table has
one word per vertex. The input total-capacity bound ensures every
intermediate addition fits, including parallel edges and self-loops.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[endpoints,capacities,m,n,heap]`; both input tables have
stride five in the original solver layout. -/
def initialEndpointScanBody : Stmt :=
  forRange 5 (.const 0) (.reg 2)
    (.assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 5)))) ;;
     .assign 7 (.load (.bin .add (.reg 1) (.bin .mul (.const 5) (.reg 5)))) ;;
     .store (.bin .add (.reg 4) (.reg 6))
       (.bin .add (.load (.bin .add (.reg 4) (.reg 6))) (.reg 7))) ;;
  .ret (.bin .add (.reg 4) (.reg 3))

/-- The endpoint accumulator occupies one procedure. -/
def initialEndpointScanModule : List Stmt := [initialEndpointScanBody]

/-- One complete endpoint table costs at most `80m+40` operations and
allocates `n` words. All old memory is preserved. No numeric result is
assumed: the only arithmetic bound is on the total input capacity. -/
def initialEndpointScanContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a c m n heap, args = [a,c,m,n,heap] ∧
      (∀ i < m, a+5*i < heap ∧ c+5*i < heap ∧ mem (a+5*i) < n) ∧
      (∑ i ∈ Finset.range m, mem (c+5*i)) < 2^w)
    (fun args mem mem' => ∀ v < args.getD 3 0,
      mem' (heapArg args+v) = initialEndpointSum
        (fun i => mem (args.getD 0 0+5*i)) (fun i => mem (args.getD 1 0+5*i)) (args.getD 2 0) v)
    (fun args _ => 80*args.getD 2 0+40) (fun args _ => args.getD 3 0)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+args.getD 3 0 }

/-- The accumulator is deterministic. -/
theorem initialEndpointScanBody_noRand : initialEndpointScanBody.NoRand := by
  simp [initialEndpointScanBody,forRange,forUp,Stmt.NoRand]

private theorem endpoint_loop {w a c m n heap : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hw : 5 < 2^w) (hspace : heap+n < 2^w) (hm : m < 2^w)
    (hzero : ZeroFrom mem heap)
    (hsource : ∀ i < m, a+5*i < heap ∧ c+5*i < heap ∧ mem (a+5*i) < n)
    (htotal : (∑ i ∈ Finset.range m, mem (c+5*i)) < 2^w) :
    Triple w p (fun st => st = startState [a,c,m,n,heap] mem pos)
      (forRange 5 (.const 0) (.reg 2)
        (.assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 5)))) ;;
         .assign 7 (.load (.bin .add (.reg 1) (.bin .mul (.const 5) (.reg 5)))) ;;
         .store (.bin .add (.reg 4) (.reg 6))
           (.bin .add (.load (.bin .add (.reg 4) (.reg 6))) (.reg 7))))
      (normalPost fun st => st.regs 3 = n ∧ st.regs 4 = heap ∧
        (∀ v < n, st.mem (heap+v) = initialEndpointSum
          (fun i => mem (a+5*i)) (fun i => mem (c+5*i)) m v) ∧
        (∀ z, z < heap ∨ heap+n ≤ z → st.mem z = mem z))
      (fun _ => 80*m+30) := by
  let endpoint := fun i => mem (a+5*i)
  let weight := fun i => mem (c+5*i)
  have htot : (∑ i ∈ Finset.range m, weight i) < 2^w := htotal
  have hl := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := .assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 5)))) ;;
      .assign 7 (.load (.bin .add (.reg 1) (.bin .mul (.const 5) (.reg 5)))) ;;
      .store (.bin .add (.reg 4) (.reg 6))
        (.bin .add (.load (.bin .add (.reg 4) (.reg 6))) (.reg 7)))
    (P := fun st => st = startState [a,c,m,n,heap] mem pos)
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = c ∧ st.regs 2 = m ∧ st.regs 3 = n ∧
      st.regs 4 = heap ∧ st.regs 5 = i ∧
      (∀ v < n, st.mem (heap+v) = initialEndpointSum endpoint weight i v) ∧
      (∀ z, z < heap ∨ heap+n ≤ z → st.mem z = mem z))
    40 0 m (Nat.zero_le m) (by omega) (fun _ => by omega)
    (fun st he => by
      subst st
      refine ⟨by eval_expr,?_⟩
      simpa [startState,initialEndpointSum] using
        (fun v (_ : v < n) => hzero (heap+v) (Nat.le_add_right _ _)))
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have hm := hi.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st omegaBits hst
      obtain ⟨h0,h1,h2,h3,h4,h5,htable,hframe⟩ := hst
      obtain ⟨ha,hc,hv⟩ := hsource i hi
      have hra : st.mem (a+5*i) = endpoint i := hframe _ (Or.inl ha)
      have hrc : st.mem (c+5*i) = weight i := hframe _ (Or.inl hc)
      have hpoint : endpoint i < n := hv
      have hcword : weight i < 2^w := by
        have hh := initialEndpointSum_le_total endpoint weight (i+1) m (endpoint i) (by omega)
        rw [initialEndpointSum_succ,ite_eq_left rfl] at hh
        omega
      have hnext : initialEndpointSum endpoint weight i (endpoint i)+weight i < 2^w := by
        have hh := initialEndpointSum_le_total endpoint weight (i+1) m (endpoint i) (by omega)
        rw [initialEndpointSum_succ,ite_eq_left rfl] at hh
        exact hh.trans_lt htot
      have hcur := htable (endpoint i) hpoint
      have hcurword : st.mem (heap+endpoint i) < 2^w := by omega
      have hsumword : st.mem (heap+endpoint i)+weight i < 2^w := by omega
      have hmul : 5*i < 2^w := by omega
      apply runs_start_le
      refine runs_seq_assign_le (v := endpoint i) (by eval_expr) ?_
      refine runs_seq_assign_le (v := weight i) (by eval_expr) ?_
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,h5⟩
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simpa using h3
        · simpa using h4
        · simp
        · intro v hv
          dsimp only
          by_cases he : v = endpoint i
          · subst v
            simp only [Function.update_self,initialEndpointSum_succ,↓reduceIte]
            rw [hcur]
          · rw [Function.update_of_ne (by omega),initialEndpointSum_succ,
              ite_eq_right (Ne.symm he),add_zero]
            exact htable v hv
        · intro z hz
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe z hz
      · wram_cost)
  refine hl.conseq (fun _ he => he) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.2.2.1,ho.2.2.2.2.1,ho.2.2.2.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The endpoint scan computes its prefix-sum model on every random tape,
with its own fit and allocation premises made explicit. -/
theorem initialEndpointScan_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b initialEndpointScanModule) :
    MeetsContract w p b (initialEndpointScanContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,c,m,n,heap,rfl,hsource,htotal⟩,hzero,hspace⟩ := hpre
  change heap+n < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hm : m < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold initialEndpointScanBody
  refine runs_seq_triple_le (endpoint_loop p mem pos hw hspace hm hzero hsource htotal) rfl ?_
  intro st ⟨h3,h4,htable,hframe⟩
  refine runs_ret_le (v := heap+n) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+n ∧ heap+n ≤ heap+n ∧ (∀ x < heap, st.mem x = mem x) ∧
      ZeroFrom st.mem (heap+n) ∧ _) ∧ heap+n = heap+n
    exact ⟨⟨by omega,le_rfl,fun x hx => hframe x (Or.inl hx),
      fun x hx => (hframe x (Or.inr hx)).trans (hzero x (by omega)),htable⟩,rfl⟩
  · simp only [initialEndpointScanContract,heapContract,List.getD_cons_zero,
      List.getD_cons_succ,Expr.size_bin,Expr.size_reg]
    omega

end MinCostFlow.IPM.Machine
