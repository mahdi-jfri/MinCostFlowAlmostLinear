module

public import MinCostFlow.Scaling.ShiftedGraphProgram
public import MinCostFlow.Scaling.BuildDemandsProgram
public import MinCostFlow.Scaling.DemandInstanceProgram
public import MinCostFlow.Scaling.ShiftedWordBounds
public import MinCostFlow.Scaling.ReductionAlgorithm
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# The complete feasibility-instance construction

The general-flow reduction of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
first removes lower capacities, builds the shifted demand table by an edge
scan, and converts that table to an auxiliary circulation. This procedure
executes those three proved transformations. The final graph is exactly
`buildFeasibilityInstance`. Intermediate graph and demand storage precede
it in the newly allocated region, with all space and costs counted. The
contract also retains those intermediate arrays for the subsequent objective
threshold and residual construction.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[inputAddress,heap]`. Intermediate output addresses are the
old heap and the first returned heap pointer. -/
def buildFeasibilityBody (graph demands auxiliary : ℕ) : Stmt :=
  .call 2 graph [.reg 0, .reg 1] ;;
  .call 3 demands [.reg 0, .reg 2] ;;
  .call 4 auxiliary [.reg 1, .reg 2, .reg 3] ;;
  .ret (.reg 4)

/-- Entry, shifted graph, shifted demands, and the auxiliary circulation. -/
def buildFeasibilityModule (b : ℕ) : List Stmt :=
  buildFeasibilityBody (b + 1) (b + 6) (b + 15) ::
    (shiftedGraphModule (b + 1) ++
      (buildDemandsModule (b + 6) ++ demandInstanceModule (b + 15)))

/-- The final graph follows the intermediate graph and demand scratch.
The same word budget covers all signed subtraction and table updates. -/
def buildFeasibilityContract (w : ℕ) (I : Instance) (hv : I.IsValid) (U : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ ListAt mem a I.encode ∧
      a + I.encode.length ≤ heap ∧ (∀ e ∈ I.edges, e.lower ≤ e.upper) ∧
      (∀ v : Fin I.n, (I.d v).natAbs ≤ U) ∧
      (∀ e ∈ I.edges, e.lower.natAbs ≤ U) ∧ (∀ e ∈ I.edges, e.upper.natAbs ≤ U) ∧
      (2 * I.m + 2) * U < 2 ^ w ∧ (∀ x ∈ I.encode, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args + 2 + 11 * I.m + 2 * I.n)
      (FlowReduction.buildFeasibilityInstance I hv).solverWords)
    (fun _ _ => 1400 * I.m + 600 * I.n + 1000)
    (fun _ _ => 4 + 16 * I.m + 12 * I.n)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 4 + 16 * I.m + 12 * I.n ∧
      ListAt mem' (heapArg args) (FlowReduction.shiftedGraph I hv).solverWords ∧
      SignedTableAt mem' (heapArg args + 2 + 5 * I.m) (FlowReduction.buildShiftedDemands I hv) }

/-- The complete constructor and every helper have no random instructions. -/
theorem buildFeasibilityModule_noRand (b : ℕ) :
    ∀ body ∈ buildFeasibilityModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [buildFeasibilityBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact shiftedGraphModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact buildDemandsModule_noRand _ body hb
      · exact demandInstanceModule_noRand _ body hb

/-- The executable composition builds exactly the model's feasibility
instance, with linear time, exact space, and unchanged original input. -/
theorem buildFeasibility_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (buildFeasibilityModule b)) (I : Instance) (hv : I.IsValid) (U : ℕ) :
    MeetsContract w p b (buildFeasibilityContract w I hv U) := by
  have hparts := hasAt_tail hp
  have hgraph := hasAt_append_left hparts
  have hrest : p.HasAt (b + 6) (buildDemandsModule (b + 6) ++ demandInstanceModule (b + 15)) := by
    simpa only [shiftedGraphModule_length, Nat.add_assoc] using hasAt_append_right hparts
  have hdemands := hasAt_append_left hrest
  have hinstance : p.HasAt (b + 15) (demandInstanceModule (b + 15)) := by
    simpa only [buildDemandsModule_length, Nat.add_assoc] using hasAt_append_right hrest
  let J := FlowReduction.shiftedGraph I hv
  let d := FlowReduction.buildShiftedDemands I hv
  have hJm : J.m = I.m := rfl
  have hJn : J.n = I.n := rfl
  have hkG := shiftedGraph_meetsContract (w := w) hgraph I hv
  have hkD := buildDemands_meetsContract (w := w) hdemands I hv U U
  have hkP := demandInstance_meetsContract (w := w) hinstance J d
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, horder, hd, hl, hu, hbudget, hinput, hw⟩,
    hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (4 + 16 * I.m + 12 * I.n) < 2 ^ w at hspace
  have hsum := capacity_sum_words I hl hu hbudget
  have hscan := demand_scan_words I hbudget
  have hlFin : ∀ e : Fin I.m, (I.edge e).lower.natAbs ≤ U :=
    fun e => hl (I.edge e) (List.getElem_mem e.isLt)
  have hJwords := shiftedGraph_words I hv hinput hl hu hbudget
  have hdwords := buildShiftedDemands_words I hv hd hlFin hbudget
  have hlength := instance_encode_length I hv
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  apply runs_start_le
  unfold buildFeasibilityBody
  refine runs_seq_call_le hkG (vs := [a, heap]) (by eval_expr) hwords ?_ ?_
  · exact ⟨⟨a, heap, rfl, hat, hend, horder, hsum, hinput, hw⟩, hzero, by change heap + (2 + 5 * I.m) < 2 ^ w; omega⟩
  · intro heapG memG posG hpostG
    obtain ⟨⟨_, _, hframeG, hzeroG, hgraphG⟩, hptrG⟩ := hpostG
    change heapG = heap + 2 + 5 * I.m at hptrG
    change (∀ x < heap, memG x = mem x) at hframeG
    change ZeroFrom memG heapG at hzeroG
    change ListAt memG heap J.solverWords at hgraphG
    have hheapG : heapG < 2 ^ w := by omega
    have hatG := hat.of_agree_below hend hframeG
    refine runs_seq_call_le hkD (vs := [a, heapG]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨a, heapG, rfl, hatG, by omega, hd, hlFin, hscan, hw⟩, hzeroG, by change heapG + (2 * I.n + 6 * I.m) < 2 ^ w; omega⟩
    · intro heapD memD posD hpostD
      obtain ⟨⟨_, _, hframeD, hzeroD, htableD⟩, hptrD⟩ := hpostD
      change heapD = heapG + 2 * I.n + 6 * I.m at hptrD
      change (∀ x < heapG, memD x = memG x) at hframeD
      change ZeroFrom memD heapD at hzeroD
      change SignedTableAt memD heapG d at htableD
      have hgraphD : ListAt memD heap J.solverWords := by
        apply hgraphG.of_agree_below (h₀ := heapG)
        · rw [J.solverWords_length]
          change heap + (2 + 5 * I.m) ≤ heapG
          omega
        · exact hframeD
      have hheapD : heapD < 2 ^ w := by omega
      refine runs_seq_call_le hkP (vs := [heap, heapG, heapD]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨heap, heapG, heapD, rfl, hgraphD, htableD, ?_, ?_, hJwords, hdwords, hw⟩, hzeroD, ?_⟩
        · rw [J.solverWords_length]
          change heap + (2 + 5 * I.m) ≤ heapD
          omega
        · change heapG + 2 * I.n ≤ heapD
          omega
        · change heapD + (2 + 5 * I.m + 10 * I.n) < 2 ^ w
          omega
      · intro out memP posP hpostP
        obtain ⟨⟨_, _, hframeP, hzeroP, hfinalP⟩, hout⟩ := hpostP
        change (∀ x < heapD, memP x = memD x) at hframeP
        change ZeroFrom memP out at hzeroP
        change ListAt memP heapD (J.demandInstance d).solverWords at hfinalP
        change out = heapD + 2 + 5 * I.m + 10 * I.n at hout
        have houtword : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap + (4 + 16 * I.m + 12 * I.n) ∧
            (∀ x < heap, memP x = mem x) ∧ ZeroFrom memP out ∧
            ListAt memP (heap + 2 + 11 * I.m + 2 * I.n)
              (FlowReduction.buildFeasibilityInstance I hv).solverWords) ∧
            out = heap + 4 + 16 * I.m + 12 * I.n ∧
            ListAt memP heap J.solverWords ∧ SignedTableAt memP (heap+2+5*I.m) d
          refine ⟨⟨by omega, by omega, ?_, hzeroP, ?_⟩, by omega,?_,?_⟩
          · intro x hx
            exact (hframeP x (by omega)).trans ((hframeD x (by omega)).trans (hframeG x hx))
          · have haddress : heap + 2 + 11 * I.m + 2 * I.n = heapD := by omega
            rw [haddress]
            exact hfinalP
          · apply hgraphD.of_agree_below (h₀ := heapD) ?_ hframeP
            rw [J.solverWords_length]
            change heap+(2+5*I.m)≤heapD
            omega
          · have he : heap+2+5*I.m=heapG := by omega
            rw [he]
            exact htableD.of_agree_below (by omega) hframeP
        · simp only [buildFeasibilityContract, heapContract, shiftedGraphContract,
            buildDemandsContract, demandInstanceContract, argsSize_cons, argsSize_nil,
            Expr.size_reg, hJm, hJn]
          omega

/-- A valid bounded input with consistent capacities satisfies every
construction premise on its canonical input memory at a sufficiently large width. -/
theorem exists_buildFeasibility_pre (I : Instance) (hv : I.IsValid) (U : ℕ)
    (horder : ∀ e ∈ I.edges, e.lower ≤ e.upper)
    (hd : ∀ v : Fin I.n, (I.d v).natAbs ≤ U)
    (hl : ∀ e ∈ I.edges, e.lower.natAbs ≤ U)
    (hu : ∀ e ∈ I.edges, e.upper.natAbs ≤ U) :
    ∃ w, (∀ x ∈ [0, I.encode.length], x < 2 ^ w) ∧
      (buildFeasibilityContract w I hv U).pre [0, I.encode.length] (initMem I.encode) := by
  let input := I.encode ++ [(2 * I.m + 2) * U + I.encode.length + 4 + 16 * I.m + 12 * I.n + 10]
  let w := wordSize 1 input
  have hlarge : (2 * I.m + 2) * U + I.encode.length + 4 + 16 * I.m + 12 * I.n + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ (List.mem_cons_self))
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · refine ⟨⟨0, I.encode.length, rfl, listAt_initMem _, by omega,
      horder, hd, hl, hu, by omega, ?_, by omega⟩, zeroFrom_initMem _, ?_⟩
    · intro x hx
      exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
    · change I.encode.length + (4 + 16 * I.m + 12 * I.n) < 2 ^ w
      omega

end MinCostFlow.Scaling.Machine
