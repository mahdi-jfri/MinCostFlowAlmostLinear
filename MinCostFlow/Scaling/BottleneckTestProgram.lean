module

public import MinCostFlow.Scaling.BottleneckGraphProgram
public import MinCostFlow.Scaling.BottleneckSolveBounds
public import MinCostFlow.Scaling.IntegerObjectiveProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# One exact bottleneck threshold test

Construct the unit-capacity threshold graph, solve it through the exact
zero-capacity adapter, and compute its signed integer objective. Retain the
actual solved flow for the subsequent cycle extraction. Both outputs refer
to the same canonical solve, including when the optimum is not unique.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,threshold,heap]`. -/
def bottleneckTestBody (graph solve objective : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 graph [.reg 0,.reg 1,.reg 2] ;;
  .call 5 solve [.reg 2,.reg 4] ;;
  .assign 6 (.bin .sub (.reg 5) (.reg 3)) ;;
  .call 7 objective [.reg 2,.reg 6,.reg 5] ;;
  .ret (.reg 7)

/-- The constructor, solver adapter, and objective procedure are consecutive. -/
def bottleneckTestModule (solver : Program) (f b : ℕ) : List Stmt :=
  let s := b+1+(bottleneckGraphModule (b+1)).length
  let o := s+(zeroCapacitySolveModule solver f s).length
  bottleneckTestBody (b+1) s o ::
    (bottleneckGraphModule (b+1) ++ zeroCapacitySolveModule solver f s ++ integerObjectiveModule o)

/-- The final two words hold the signed objective. The solved flow begins
`5*m+2` words before the returned heap. -/
noncomputable def bottleneckTestContract (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (B C : ℕ) : Contract :=
  let K := J.bottleneckGraph B
  let delta := Circulation.solveWithZeroCapacities (canonicalSolver solver f T hproc) K
  let g := wordSize 5 K.positiveInstance.solverWords
  let H := heapContract w
    (fun args mem => ∃ a heap,args=[a,B,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x<2^w) ∧
      J.m*C<2^w ∧ 2^(g+1)+2 ≤ 2^w ∧ 8<2^w)
    (fun _ _ _ => True)
    (fun _ _ => (solver.regBound+6)*T (J.n+1) J.m+
      80*K.positiveInstance.solverWords.length+40*g+solver.regBound+1100*J.m+1600)
    (fun _ _ => 7+15*J.m+2^g)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      ret=heapArg args+7+15*J.m+2^g ∧
      ListAt mem' (ret-(5*J.m+2)) (List.ofFn (fun e => (delta e).toNat)) ∧
      ListAt mem' (ret-2) (encodeInt (K.integerObjective delta)) }

/-- The threshold test is deterministic when its supplied solver is. -/
theorem bottleneckTestModule_noRand (solver : Program) (f b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ bottleneckTestModule solver f b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckTestBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | ho
    · rcases List.mem_append.mp hb with hg | hs
      · exact bottleneckGraphModule_noRand _ body hg
      · exact zeroCapacitySolveModule_noRand solver f _ hdet body hs
    · exact integerObjectiveModule_noRand _ body ho

/-- The composed test writes the exact model objective and retains its
actual test flow, with a counted solver call and linear surrounding work. -/
theorem bottleneckTest_meetsContract {w b : ℕ} {P solver : Program} {f : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (J : Circulation) (B C : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C)
    (hp : P.HasAt b (bottleneckTestModule solver f b)) :
    MeetsContract w P b (bottleneckTestContract w solver f T hproc J B C) := by
  let K := J.bottleneckGraph B
  let delta := Circulation.solveWithZeroCapacities (canonicalSolver solver f T hproc) K
  let g := wordSize 5 K.positiveInstance.solverWords
  have hKm : K.m=J.m := rfl
  have hKn : K.n=J.n := rfl
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hgraph := hasAt_append_left hleft
  have hsolve := hasAt_append_right hleft
  have hobjective : P.HasAt
      (b+1+(bottleneckGraphModule (b+1)).length+
        (zeroCapacitySolveModule solver f (b+1+(bottleneckGraphModule (b+1)).length)).length)
      (integerObjectiveModule (b+1+(bottleneckGraphModule (b+1)).length+
        (zeroCapacitySolveModule solver f (b+1+(bottleneckGraphModule (b+1)).length)).length)) := by
    simpa only [List.length_append,Nat.add_assoc] using hasAt_append_right htail
  have hkG := bottleneckGraph_meetsContract (w := w) hgraph J B
  have hkS := zeroCapacitySolve_meetsContract (w := w) hproc hdet K hc
    (bottleneckGraph_capacity_bound J B) hsolve
  have hkO := integerObjective_meetsContract (w := w) hobjective K (fun e => (delta e).toNat)
  have hunit : ∀ e,(delta e).toNat ≤ 1 := bottleneckSolve_toNat_le_one solver f T hproc J B
  have hopt : K.Optimal (fun e => (delta e : ℝ)) := by
    apply Circulation.solveWithZeroCapacities_of_optimal
    exact canonicalSolver_optimal solver f T hproc K.positiveInstance
  have hn : ∀ e,0≤delta e := fun e => Int.cast_nonneg_iff.mp (hopt.1.2 e).1
  have hmass : objectiveScanMass K (fun e => (delta e).toNat) (List.finRange K.m) ≤ J.m*C :=
    bottleneckSolve_objective_mass_le solver f T hproc J B C hC
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hbudget,hguest,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(7+15*J.m+2^g)<2^w at hs
  have hregion : 0<2^g := Nat.two_pow_pos g
  have hh : heap<2^w := by omega
  have hm : J.m<2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hend; omega
  have hM := (solver_header_at J hat).2
  have hKinput := bottleneckGraph_words_fit J B w hinput (by omega)
  apply runs_start_le
  unfold bottleneckTestBody
  refine runs_seq_assign_le (v := J.m) (by clear! solver T K delta g; eval_expr) ?_
  refine runs_seq_call_le hkG (vs := [a,B,heap]) (by clear! solver T K delta g; eval_expr) ?_ ?_ ?_
  · exact hwords
  · exact ⟨⟨a,heap,rfl,hat,hend,hinput,hw⟩,hz,by change heap+(2+5*J.m)<2^w; omega⟩
  · intro graphEnd memG posG hpostG
    obtain ⟨⟨_,_,hframeG,hzG,hgraphData⟩,hgraphEnd⟩ := hpostG
    change graphEnd=heap+2+5*J.m at hgraphEnd
    change (∀ x<heap,memG x=mem x) at hframeG
    change ZeroFrom memG graphEnd at hzG
    change ListAt memG heap K.solverWords at hgraphData
    have hgw : graphEnd<2^w := by omega
    refine runs_seq_call_le hkS (vs := [heap,graphEnd]) (by clear! solver T K delta g; eval_expr)
      (by wram_words) ?_ ?_
    · refine ⟨⟨heap,graphEnd,rfl,hgraphData,?_,hKinput,hguest⟩,hzG,?_⟩
      · rw [K.solverWords_length,hKm]; omega
      · change graphEnd+(3+6*J.m+2^g)<2^w; omega
    · intro flowEnd memS posS hpostS
      obtain ⟨⟨_,_,hframeS,hzS,hread⟩,hflowEnd⟩ := hpostS
      change flowEnd=graphEnd+3+6*J.m+2^g at hflowEnd
      change (∀ x<graphEnd,memS x=memG x) at hframeS
      change ZeroFrom memS flowEnd at hzS
      change K.readSolverFlow memS (graphEnd+3+5*J.m+2^g)=delta at hread
      have hflowData := solverOutput_listAt K hread
      have hflowPtr : flowEnd-J.m=graphEnd+3+5*J.m+2^g := by omega
      have hfw : flowEnd<2^w := by omega
      have hpw : flowEnd-J.m<2^w := by omega
      have hgraphDataS := hgraphData.of_agree_below (h₀ := graphEnd)
        (by rw [K.solverWords_length,hKm]; omega) hframeS
      refine runs_seq_assign_le (v := flowEnd-J.m) (by clear! solver T K delta g; eval_expr) ?_
      refine runs_seq_call_le hkO (vs := [heap,flowEnd-J.m,flowEnd]) (by clear! solver T K delta g; eval_expr)
        (by wram_words) ?_ ?_
      · refine ⟨⟨heap,flowEnd-J.m,flowEnd,rfl,hgraphDataS,?_,?_,?_,hKinput,?_,hmass.trans_lt hbudget,hw⟩,hzS,?_⟩
        · rw [hflowPtr]; exact hflowData
        · rw [K.solverWords_length,hKm]; omega
        · rw [hKm]; omega
        · intro e; exact (hunit e).trans_lt (by omega)
        · change flowEnd+(4*J.m+2)<2^w; omega
      · intro ret memO posO hpostO
        obtain ⟨⟨_,_,hframeO,hzO,_⟩,hret,hvalue⟩ := hpostO
        change ret=flowEnd+4*J.m+2 at hret
        change (∀ x<flowEnd,memO x=memS x) at hframeO
        change ZeroFrom memO ret at hzO
        change ListAt memO (ret-2) (encodeInt (K.integerObjective (fun e => ((delta e).toNat : ℤ)))) at hvalue
        have hvalue' : ListAt memO (ret-2) (encodeInt (K.integerObjective delta)) := by
          simpa only [Int.toNat_of_nonneg (hn _)] using hvalue
        have hflowDataO := hflowData.of_agree_below (h₀ := flowEnd)
          (by rw [List.length_ofFn,hKm]; omega) hframeO
        have hr : ret<2^w := by omega
        refine runs_ret_le (v := ret) (by clear! solver T K delta g; eval_expr) ?_ ?_
        · change (heap≤ret ∧ ret≤heap+(7+15*J.m+2^g) ∧ (∀ x<heap,memO x=mem x) ∧
            ZeroFrom memO ret ∧ True) ∧ ret=heap+7+15*J.m+2^g ∧
            ListAt memO (ret-(5*J.m+2)) (List.ofFn (fun e => (delta e).toNat)) ∧ _
          refine ⟨⟨by omega,by omega,?_,hzO,True.intro⟩,by omega,?_,hvalue'⟩
          · intro x hx
            exact (hframeO x (by omega)).trans ((hframeS x (by omega)).trans (hframeG x hx))
          · have heq : ret-(5*J.m+2)=graphEnd+3+5*J.m+2^g := by omega
            rw [heq]; exact hflowDataO
        · simp only [bottleneckTestContract,bottleneckGraphContract,zeroCapacitySolveContract,
            integerObjectiveContract,heapContract,hKm,hKn,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_reg,Expr.size_const,Expr.size_load]
          dsimp only [K,g]
          omega

end MinCostFlow.Scaling.Machine
