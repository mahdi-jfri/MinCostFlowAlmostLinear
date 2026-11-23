module

public import MinCostFlow.Scaling.RoundedInstanceProgram
public import MinCostFlow.Scaling.CostPowersProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Computing all constants and records of a rounded residual graph

The residual graph has `B=2*m` edges. This procedure reads that count,
computes `B^8` and `B^9` once, and constructs the exact rounded instance
from the state power and `C+1`. The graph begins after the two shared power
words. The procedure uses `4+34*m` fresh words including scratch and costs
at most `3600*m+500` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[residual,potentials,power,C+1,heap]`. -/
def buildRoundedInstanceBody (powers graph : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 6 powers [.reg 5, .reg 4] ;;
  .call 7 graph [.reg 0, .reg 1, .load (.reg 4),
    .load (.bin .add (.reg 4) (.const 1)), .reg 2, .reg 3, .reg 6] ;;
  .ret (.reg 7)

/-- Shared power computation and the complete rounded graph constructor. -/
def buildRoundedInstanceModule (b : ℕ) : List Stmt :=
  buildRoundedInstanceBody (b+1) (b+3) ::
    (costPowersModule (b+1) ++ roundedInstanceModule (b+3))

/-- Input graphs and potentials are stored below the heap. Only local
arithmetic budgets are required of the represented cost state. -/
def buildRoundedInstanceContract (w : ℕ) {I : Circulation} (s : CostState I) (C : ℕ) : Contract :=
  let R := I.residual s.flow
  let H := heapContract w
    (fun args mem => ∃ a pot heap, args = [a, pot, s.power, C+1, heap] ∧
      ListAt mem a R.solverWords ∧ SignedTableAt mem pot s.potential ∧
      a+R.solverWords.length ≤ heap ∧ pot+2*I.n ≤ heap ∧
      (∀ x ∈ R.solverWords, x < 2 ^ w) ∧ (I.m+I.m)^9 < 2 ^ w ∧
      (∀ e, (roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem) ∧
      12 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args+2) (s.roundedInstance C).solverWords)
    (fun _ _ => 1800*(I.m+I.m)+500) (fun _ _ => 4+17*(I.m+I.m))
  { H with post := fun args mem out mem' => H.post args mem out mem' ∧
      out = heapArg args+4+17*(I.m+I.m) }

/-- Shared constants and graph construction use no random instructions. -/
theorem buildRoundedInstanceModule_noRand (b : ℕ) :
    ∀ body ∈ buildRoundedInstanceModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [buildRoundedInstanceBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact costPowersModule_noRand _ body hb
    · exact roundedInstanceModule_noRand _ body hb

/-- The machine computes the cost model's rounded graph from the stored
residual graph and potentials, including all shared constants. -/
theorem buildRoundedInstance_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (buildRoundedInstanceModule b)) {I : Circulation}
    (s : CostState I) (C : ℕ) :
    MeetsContract w p b (buildRoundedInstanceContract w s C) := by
  have htail := hasAt_tail hp
  have hpowers := hasAt_append_left htail
  have hgraph : p.HasAt (b+3) (roundedInstanceModule (b+3)) := by
    have h := hasAt_append_right htail
    simpa only [costPowersModule, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  let R := I.residual s.flow
  let B := I.m+I.m
  have hkP := costPowers_meetsContract (w := w) hpowers B
  have hkG := roundedInstance_meetsContract (w := w) hgraph s C
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, pot, heap, rfl, hat, htable, hend, hpotend, hinput, hpower9, hscalar, hw⟩,
    hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(4+17*B) < 2 ^ w at hspace
  change B^9 < 2 ^ w at hpower9
  have hsize : R.solverWords.length = 2+5*B := R.solverWords_length
  change a+R.solverWords.length ≤ heap at hend
  rw [hsize] at hend
  have hM : mem (a+1) = B := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hat 1 (by change 1 < R.solverWords.length; rw [hsize]; omega)
  have hB : B < 2 ^ w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpower : s.power < 2 ^ w := hwords _ (by simp)
  have hd : C+1 < 2 ^ w := hwords _ (by simp)
  have ha : a < 2 ^ w := by omega
  have ha1 : a+1 < 2 ^ w := by omega
  have hp : pot < 2 ^ w := by omega
  have hh : heap < 2 ^ w := by omega
  have hh1 : heap+1 < 2 ^ w := by omega
  have hh2 : heap+2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold buildRoundedInstanceBody
  refine runs_seq_assign_le (v := B) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [B, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hpower9⟩, hzero, hh2⟩
  · intro next memP posP hpostP
    obtain ⟨⟨_, _, hframeP, hzeroP, hpairs⟩, hnext⟩ := hpostP
    change next = heap+2 at hnext
    change (∀ x < heap, memP x = mem x) at hframeP
    change ZeroFrom memP next at hzeroP
    change ListAt memP heap [B^8, B^9] at hpairs
    have hB8mem : memP heap = B^8 := by
      have h := hpairs 0 (by change 0 < 2; decide)
      change memP (heap+0) = B^8 at h
      simpa only [Nat.add_zero] using h
    have hB9mem : memP (heap+1) = B^9 := by
      have h := hpairs 1 (by change 1 < 2; decide)
      change memP (heap+1) = B^9 at h
      exact h
    have hB8 : B^8 < 2 ^ w := by
      by_cases hzeroB : B = 0
      · rw [hzeroB, Nat.zero_pow (by decide : 0 < 8)]
        omega
      · exact (Nat.pow_le_pow_right (by omega : 1 ≤ B) (by decide : 8 ≤ 9)).trans_lt hpower9
    have hnextword : next < 2 ^ w := by omega
    have hatP : ListAt memP a R.solverWords := hat.of_agree_below (by change a+R.solverWords.length ≤ heap; rw [hsize]; exact hend) hframeP
    have htableP : SignedTableAt memP pot s.potential := htable.of_agree_below hpotend hframeP
    refine runs_seq_call_le hkG
      (vs := [a, pot, B^8, B^9, s.power, C+1, next]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨a, pot, next, rfl, hatP, htableP, by change a+R.solverWords.length ≤ next; rw [hsize]; omega, by omega, hinput, ?_, hw⟩,
        hzeroP, ?_⟩
      · intro e
        apply roundedCost_pre_transfer (hscalar e) hzeroP
        have hBpos : 0 < B := by have h := e.isLt; omega
        omega
      · change next+(2+17*B) < 2 ^ w
        omega
    · intro out memG posG hpostG
      obtain ⟨⟨_, _, hframeG, hzeroG, hgraphG⟩, hout⟩ := hpostG
      change out = next+2+17*B at hout
      change (∀ x < next, memG x = memP x) at hframeG
      change ZeroFrom memG out at hzeroG
      change ListAt memG next (s.roundedInstance C).solverWords at hgraphG
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap+(4+17*B) ∧ (∀ x < heap, memG x = mem x) ∧
          ZeroFrom memG out ∧ ListAt memG (heap+2) (s.roundedInstance C).solverWords) ∧
          out = heap+4+17*B
        refine ⟨⟨by omega, by omega, ?_, hzeroG, ?_⟩, by omega⟩
        · intro x hx
          exact (hframeG x (by omega)).trans (hframeP x hx)
        · simpa only [hnext] using hgraphG
      · simp only [buildRoundedInstanceContract, heapContract, costPowersContract,
          roundedInstanceContract, argsSize_cons, argsSize_nil, Expr.size_bin,
          Expr.size_load, Expr.size_reg, Expr.size_const]
        change _ ≤ 1800*B+500
        omega

end MinCostFlow.Scaling.Machine
