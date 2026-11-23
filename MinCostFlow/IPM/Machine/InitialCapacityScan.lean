module

public import WordRAM.Layout
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Reading the doubled original-edge midpoint flow

Lemma 4.12 of Chen et al., arXiv:2203.00671v2 (page 31,
Appendix B.1 page 92), first sets each original edge to its midpoint.
For the bounded circulation solver, lower capacities are zero, so twice
this flow is the upper-capacity word. This procedure copies those words
from the five-word solver records into a fresh dense array. It performs
no division and therefore preserves half units exactly. Auxiliary edges
are added by the subsequent initialization steps.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[capacityAddress,m,heap]`. Capacities are five words apart. -/
def initialCapacityScanBody : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 2) (.reg 3))
      (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 3))))) ;;
  .ret (.bin .add (.reg 2) (.reg 1))

/-- One procedure scans the original capacities. -/
def initialCapacityScanModule : List Stmt := [initialCapacityScanBody]

/-- The scan allocates `m` cells, preserves old memory, and writes the
exact doubled midpoint numerators in at most `40m+40` steps. The space
premise is explicit so this helper can be used independently of the
bounded solver's missing workspace premise. -/
def initialCapacityScanContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a m heap, args = [a,m,heap] ∧
      ∀ i < m, a+5*i < heap ∧ mem (a+5*i) < 2^w)
    (fun args mem mem' => ∀ i < args.getD 1 0,
      mem' (heapArg args+i) = mem (args.getD 0 0+5*i))
    (fun args _ => 40*args.getD 1 0+40) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧ v = heapArg args+args.getD 1 0 }

/-- The capacity scan has no random instruction. -/
theorem initialCapacityScanBody_noRand : initialCapacityScanBody.NoRand := by
  simp [initialCapacityScanBody, forRange, forUp, Stmt.NoRand]

private theorem scan_loop {w a m heap : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hw : 5 < 2^w) (hspace : heap+m < 2^w)
    (hsource : ∀ i < m, a+5*i < heap ∧ mem (a+5*i) < 2^w) :
    Triple w p (fun st => st = startState [a,m,heap] mem pos)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 3))
          (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 3))))))
      (normalPost fun st => st.regs 1 = m ∧ st.regs 2 = heap ∧
        (∀ i < m, st.mem (heap+i) = mem (a+5*i)) ∧
        (∀ z, z < heap ∨ heap+m ≤ z → st.mem z = mem z))
      (fun _ => 40*m+30) := by
  have hl := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.reg 3))
      (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 3)))))
    (P := fun st => st = startState [a,m,heap] mem pos)
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = m ∧ st.regs 2 = heap ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (heap+j) = mem (a+5*j)) ∧
      (∀ z, z < heap ∨ heap+i ≤ z → st.mem z = mem z))
    12 0 m (Nat.zero_le m) (by omega) (fun _ => by omega)
    (fun st he => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      simp [startState])
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
    (fun i _ hi => by
      intro st omegaBits hst
      obtain ⟨h0,h1,h2,h3,hcopy,hframe⟩ := hst
      obtain ⟨hbefore,hword⟩ := hsource i hi
      have hread : st.mem (a+5*i) = mem (a+5*i) := hframe _ (Or.inl hbefore)
      have hreadword : st.mem (a+5*i) < 2^w := hread ▸ hword
      have haddr : a+5*i < 2^w := by omega
      have hmul : 5*i < 2^w := by omega
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,h3⟩
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simp
        · intro j hj
          dsimp only
          by_cases he : j = i
          · subst j
            simp [hread]
          · rw [Function.update_of_ne (by omega)]
            exact hcopy j (by omega)
        · intro z hz
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe z (by omega)
      · wram_cost)
  refine hl.conseq (fun _ he => he) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.1,ho.2.2.1,ho.2.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The midpoint-numerator scan meets its exact memory and cost contract
for every random tape. No unproved arithmetic or allocation oracle is used. -/
theorem initialCapacityScan_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b initialCapacityScanModule) :
    MeetsContract w p b (initialCapacityScanContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,m,heap,rfl,hsource⟩,hzero,hspace⟩ := hpre
  change heap+m < 2^w at hspace
  change ZeroFrom mem heap at hzero
  apply runs_start_le
  unfold initialCapacityScanBody
  refine runs_seq_triple_le (scan_loop p mem pos hw hspace hsource) rfl ?_
  intro st ⟨h1,h2,hcopy,hframe⟩
  refine runs_ret_le (v := heap+m) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+m ∧ heap+m ≤ heap+m ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap+m) ∧
      (∀ i < m, st.mem (heap+i) = mem (a+5*i))) ∧ heap+m = heap+m
    exact ⟨⟨by omega,le_rfl,fun x hx => hframe x (Or.inl hx),
      fun x hx => (hframe x (Or.inr hx)).trans (hzero x (by omega)),hcopy⟩,rfl⟩
  · simp only [initialCapacityScanContract,heapContract,List.getD_cons_zero,
      List.getD_cons_succ,Expr.size_bin,Expr.size_reg]
    omega

end MinCostFlow.IPM.Machine
