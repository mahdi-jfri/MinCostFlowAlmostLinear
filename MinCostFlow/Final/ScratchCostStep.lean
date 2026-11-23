module

public import MinCostFlow.Final.ScratchCapacityExtractDual
public import MinCostFlow.Scaling.CostStepContract
import MinCostFlow.Scaling.CapacityScalingCorrectness
import MinCostFlow.Scaling.CostStepNumericFacts
import MinCostFlow.Scaling.CapacityExtractDualProgram
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.CapacityPositiveProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.CostStepInputFacts
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.ResidualWordBounds
import MinCostFlow.Scaling.RoundedCostCalls
import WordRAM.Tactic

/-!
# One cost round with polynomial scratch

The rounded primal solve and measured dual extraction use the widened
capacity procedures. The round then updates the flow and potentials.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The exact positive adapter of the capacity model is optimal whenever
its input has its own polynomial cost bound and the supplied capacity bound. -/
theorem scratchCapacityPositive_optimal (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (U : ℕ) (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    J.Optimal (fun e => ((J.invokePositive
      (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U)).value e : ℝ)) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc K) K
  have hposCap := J.positiveInstance_capacitiesBounded U hU hu
  have hopt := lemma_C_9 solve hsolve J.positiveInstance U (J.positiveInstance_costsBounded _ hc)
    (fun e => (hposCap e).2)
  exact Circulation.solveWithZeroCapacities_of_optimal (fun K => (capacityScalingModel solve K U).value) J hopt

/-- The actual capacity-backed measured cost step preserves all integral
capacity constraints, even without assuming conservation of the current flow. -/
theorem scratchCostStepMeasured_flow_bounds (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    {J : Circulation} (s : CostState J) (C U : ℕ)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    ∀ e,0≤(CostState.stepMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) C s).value.flow e ∧
      (CostState.stepMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) C s).value.flow e≤J.capacity e := by
  let K := s.roundedInstance C
  let delta := (K.invokePositive (fun L => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) L U)).value
  have hopt := scratchCapacityPositive_optimal solver entry T S c d hproc K U (s.roundedInstance_polynomialCosts C)
    (costRounded_capacities_le s C U hf hu) hU
  have hfeas : (J.residual s.flow).Feasible (fun e => (delta e : ℝ)) := hopt.1
  exact residualAugment_integral_bounds J s.flow delta hf hfeas

/-- The complete round and its seven constituent modules, each proved separately. -/
def scratchCostStepModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let rounded := b+1+(residualModule (b+1)).length
  let primal := rounded+(buildRoundedInstanceModule rounded).length
  let dual := primal+(scratchCapacityPositiveModule solver entry primal c d).length
  let augment := dual+(scratchCapacityExtractDualModule solver entry dual c d).length
  let potentials := augment+(residualAugmentModule augment).length
  let header := potentials+(potentialUpdateScanModule potentials).length
  costStepBody (b+1) rounded primal dual augment potentials header ::
    (residualModule (b+1) ++ buildRoundedInstanceModule rounded ++
      scratchCapacityPositiveModule solver entry primal c d ++ scratchCapacityExtractDualModule solver entry dual c d ++
      residualAugmentModule augment ++ potentialUpdateScanModule potentials ++ costHeaderModule)

/-- Fresh residual and rounded graphs, the two exact inner calls, and
new flow, potential, and header storage. -/
noncomputable def scratchCostStepSpace (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    {J : Circulation} (s : CostState J) (C U : ℕ) : ℕ :=
  let K := s.roundedInstance C
  let B := J.m+J.m
  let delta := (K.invokePositive (fun L => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) L U)).value
  2+10*J.m+(4+17*B)+scratchCapacityPositiveSpace c d K (B^10) U+
    scratchCapacityExtractDualSpace c d K delta (B^10) U+J.m+2*J.n+3

/-- Exact measured cost-round output in a three-word state header.
All additional entry conditions are finite data and arithmetic bounds. -/
noncomputable def scratchCostStepContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    {J : Circulation} (s : CostState J) (C U : ℕ) : Contract :=
  let K := s.roundedInstance C
  let B := J.m+J.m
  let delta := (K.invokePositive (fun L => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) L U)).value
  let r := CostState.stepMeasured (fun L => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) L U) C s
  { pre := fun args mem => ∃ a state heap,args=[a,state,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ state+3=heap ∧ CostStateAt mem state heap s ∧
      (∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ J.n+1≤U ∧ (∀ x∈J.solverWords,x<2^w) ∧
      J.n+B+U+B^10+2<2^w ∧ C+1<2^w ∧ 2*s.power<2^w ∧ 2*U<2^w ∧
      (4*J.m+J.n+1)*B^10<2^w ∧
      (∀ v,2*((s.potential v).natAbs+(4*J.m+J.n)*B^10)<2^w) ∧
      (∀ e,(roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem) ∧
      ZeroFrom mem heap ∧ heap+scratchCostStepSpace solver entry T S c d hproc s C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧
      ret≤heapArg args+scratchCostStepSpace solver entry T S c d hproc s C U ∧
      CostStateAt mem' (ret-3) ret r.value ∧ ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (scratchCapacityPositiveContract w solver entry T S c d hproc K (B^10) U).cost [] (fun _ => 0)+
      (scratchCapacityExtractDualContract w solver entry T S c d hproc K delta (B^10) U).cost [] (fun _ => 0)+
      5000*(J.m+J.n+1) }

/-- A cost round and every nested procedure are deterministic. -/
theorem scratchCostStepModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCostStepModule solver entry b c d,body.NoRand := by
  intro body hb
  simp only [scratchCostStepModule,List.mem_cons,List.mem_append,or_assoc] at hb
  rcases hb with rfl | hr | hb | hp | hd | ha | hu | hh
  · simp only [costStepBody,Stmt.NoRand,and_self]
  · exact residualModule_noRand _ body hr
  · exact buildRoundedInstanceModule_noRand _ body hb
  · exact scratchCapacityPositiveModule_noRand solver entry _ c d hdet body hp
  · exact scratchCapacityExtractDualModule_noRand solver entry _ c d hdet body hd
  · exact residualAugmentModule_noRand _ body ha
  · exact potentialUpdateScanModule_noRand _ body hu
  · have heq : body=costHeaderBody := List.mem_singleton.mp hh
    subst body
    exact costHeaderBody_noRand

private theorem step_graph_n {w a n : ℕ} {st : State} (h0 : st.regs 0=a) (hn : st.mem a=n) :
    Expr.eval w st (.load (.reg 0))=some n := by eval_expr

private theorem step_graph_m {w a m : ℕ} {st : State} (h0 : st.regs 0=a) (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem step_flow_ptr {w a ptr : ℕ} {st : State} (h1 : st.regs 1=a) (hm : st.mem a=ptr) :
    Expr.eval w st (.load (.reg 1))=some ptr := by eval_expr

private theorem step_pot_ptr {w a ptr : ℕ} {st : State} (h1 : st.regs 1=a) (ha : a+1<2^w) (hm : st.mem (a+1)=ptr) :
    Expr.eval w st (.load (.bin .add (.reg 1) (.const 1)))=some ptr := by eval_expr

private theorem step_power {w a power : ℕ} {st : State} (h1 : st.regs 1=a) (ha : a+2<2^w) (h2 : 2<2^w)
    (hm : st.mem (a+2)=power) : Expr.eval w st (.load (.bin .add (.reg 1) (.const 2)))=some power := by eval_expr

private theorem step_residual_args {w a f h : ℕ} {st : State}
    (h0 : st.regs 0=a) (h7 : st.regs 7=f) (h4 : st.regs 4=h) :
    evalArgs w st [.reg 0,.reg 7,.reg 4]=some [a,f,h] := by eval_expr

private theorem step_rounded_args {w a p power C heap : ℕ} {st : State}
    (h4 : st.regs 4=a) (h8 : st.regs 8=p) (h9 : st.regs 9=power) (h2 : st.regs 2=C)
    (h10 : st.regs 10=heap) (hC : C+1<2^w) (h1 : 1<2^w) :
    evalArgs w st [.reg 4,.reg 8,.reg 9,.bin .add (.reg 2) (.const 1),.reg 10]=some [a,p,power,C+1,heap] := by eval_expr

private theorem step_rounded_ptr {w a : ℕ} {st : State} (h10 : st.regs 10=a) (ha : a+2<2^w) (h2 : 2<2^w) :
    Expr.eval w st (.bin .add (.reg 10) (.const 2))=some (a+2) := by eval_expr

private theorem step_primal_args {w a U heap : ℕ} {st : State}
    (h12 : st.regs 12=a) (h3 : st.regs 3=U) (h11 : st.regs 11=heap) :
    evalArgs w st [.reg 12,.reg 3,.reg 11]=some [a,U,heap] := by eval_expr

private theorem step_delta_ptr {w a m : ℕ} {st : State}
    (h13 : st.regs 13=a) (h6 : st.regs 6=m) (ha : a<2^w) (hm : m+m<2^w) :
    Expr.eval w st (.bin .sub (.reg 13) (.bin .add (.reg 6) (.reg 6)))=some (a-(m+m)) := by eval_expr

private theorem step_dual_args {w a f U heap : ℕ} {st : State}
    (h12 : st.regs 12=a) (h14 : st.regs 14=f) (h3 : st.regs 3=U) (h13 : st.regs 13=heap) :
    evalArgs w st [.reg 12,.reg 14,.reg 3,.reg 13]=some [a,f,U,heap] := by eval_expr

private theorem step_dual_ptr {w a ptr : ℕ} {st : State} (h13 : st.regs 13=a) (hm : st.mem a=ptr) :
    Expr.eval w st (.load (.reg 13))=some ptr := by eval_expr

private theorem step_augment_args {w f d m heap : ℕ} {st : State}
    (h7 : st.regs 7=f) (h14 : st.regs 14=d) (h6 : st.regs 6=m) (h15 : st.regs 15=heap) :
    evalArgs w st [.reg 7,.reg 14,.reg 6,.reg 15]=some [f,d,m,heap] := by eval_expr

private theorem step_potential_args {w p d n heap : ℕ} {st : State}
    (h8 : st.regs 8=p) (h16 : st.regs 16=d) (h5 : st.regs 5=n) (h17 : st.regs 17=heap) :
    evalArgs w st [.reg 8,.reg 16,.reg 5,.reg 17]=some [p,d,n,heap] := by eval_expr

private theorem step_header_args {w f p n m power : ℕ} {st : State}
    (h17 : st.regs 17=f) (h18 : st.regs 18=p) (h6 : st.regs 6=m) (h5 : st.regs 5=n) (h9 : st.regs 9=power)
    (hf : f<2^w) (hp : p<2^w) (hn : n+n<2^w) (hpow : 2*power<2^w) (h2 : 2<2^w) :
    evalArgs w st [.bin .sub (.reg 17) (.reg 6),.bin .sub (.reg 18) (.bin .add (.reg 5) (.reg 5)),
      .bin .mul (.const 2) (.reg 9),.reg 18]=some [f-m,p-(n+n),2*power,p] := by eval_expr

/-- The assembled cost round computes exactly the measured model state,
with the two actual inner-model costs and linear additional work. -/
theorem scratchCostStep_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCostStepModule solver entry b c d))
    {J : Circulation} (s : CostState J) (C U : ℕ) :
    MeetsContract w p b (scratchCostStepContract w solver entry T S c d hproc s C U) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let inner := fun L => capacityScalingModel solve L U
  let R := J.residual s.flow
  let B := J.m+J.m
  let K := s.roundedInstance C
  let delta := (K.invokePositive inner).value
  let dual := K.extractDualMeasured inner delta
  let next := (CostState.stepMeasured inner C s).value
  let qbase := b+1+(residualModule (b+1)).length
  let pbase := qbase+(buildRoundedInstanceModule qbase).length
  let dbase := pbase+(scratchCapacityPositiveModule solver entry pbase c d).length
  let abase := dbase+(scratchCapacityExtractDualModule solver entry dbase c d).length
  let ubase := abase+(residualAugmentModule abase).length
  let hbase := ubase+(potentialUpdateScanModule ubase).length
  have ht := hasAt_tail hp
  simp only [List.append_assoc] at ht
  have hR : p.HasAt (b+1) (residualModule (b+1)) := hasAt_append_left ht
  have htQ := hasAt_append_right ht
  have hQ : p.HasAt qbase (buildRoundedInstanceModule qbase) := hasAt_append_left htQ
  have htP := hasAt_append_right htQ
  have hP : p.HasAt pbase (scratchCapacityPositiveModule solver entry pbase c d) := hasAt_append_left htP
  have htD := hasAt_append_right htP
  have hD : p.HasAt dbase (scratchCapacityExtractDualModule solver entry dbase c d) := hasAt_append_left htD
  have htA := hasAt_append_right htD
  have hA : p.HasAt abase (residualAugmentModule abase) := hasAt_append_left htA
  have htU := hasAt_append_right htA
  have hU : p.HasAt ubase (potentialUpdateScanModule ubase) := hasAt_append_left htU
  have hH : p.HasAt hbase costHeaderModule := hasAt_append_right htU
  have hkR := residual_meetsContract (w := w) hR J s.flow
  have hkQ := buildRoundedInstance_meetsContract (w := w) hQ s C
  have hcK := s.roundedInstance_polynomialCosts C
  have hkP := scratchCapacityPositive_meetsContract (w := w) hproc hScratch hdet hP K (B^10) U hcK
  have hkD := scratchCapacityExtractDual_meetsContract (w := w) hproc hScratch hdet hD K delta (B^10) U hcK
  have hkA := residualAugment_meetsContract (w := w) hA s.flow delta
  have hkU := potentialUpdate_meetsContract (w := w) hU s.potential dual.value
  have hkH := costHeader_meetsContract (w := w) hH
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hf,hC,hu,hm,hnU,hinput,
    hfields,hCword,hpower,hUdouble,hlabel,hpotBudget,hscalar,hz,hs⟩ := hpre
  obtain ⟨fp,pp,hheader,hfpEnd,hppEnd,hread,hpot⟩ := hstate
  have hflow := solverOutput_listAt J hread
  have hspace : heap+(2+10*J.m+(4+17*B)+scratchCapacityPositiveSpace c d K (B^10) U+
      scratchCapacityExtractDualSpace c d K delta (B^10) U+J.m+2*J.n+3)<2^w := hs
  have h12 : 12<2^w := by change J.n+B+U+B^10+2<2^w at hfields; dsimp only [B] at hspace; omega
  have hh : heap<2^w := by omega
  have hstate1 : state+1<2^w := by omega
  have hstate2 : state+2<2^w := by omega
  have hfpWord : fp<2^w := by omega
  have hppWord : pp<2^w := by omega
  have hnWord : J.n<2^w := by omega
  have hBword : B<2^w := by change J.n+B+U+B^10+2<2^w at hfields; omega
  have hmWord : J.m<2^w := by dsimp only [B] at hBword; omega
  have hUword : U<2^w := by omega
  have hpowerWord : s.power<2^w := by omega
  have hBpos : 0<B := by dsimp only [B]; omega
  have hB9 : B^9<2^w := (Nat.pow_le_pow_right hBpos (by decide : 9≤10)).trans_lt (by change J.n+B+U+B^10+2<2^w at hfields; omega)
  have hnhost : J.n+2<2^w := by change J.n+B+U+B^10+2<2^w at hfields; omega
  have htwon : J.n+J.n<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hfpCell : mem state=fp := by
    have h : mem (state+0)=fp := hheader 0 (by change 0<3; decide)
    simpa only [Nat.add_zero] using h
  have hppCell : mem (state+1)=pp := hheader 1 (by change 1<3; decide)
  have hpowerCell : mem (state+2)=s.power := hheader 2 (by change 2<3; decide)
  have hRwords := residual_words_fit J s.flow w hf hinput hBword (by omega)
  have hKwords := costRounded_words_fit s C U hf hu hfields
  have hKcap := costRounded_capacities_le s C U hf hu
  have hUone : 1≤U := by omega
  have hopt := scratchCapacityPositive_optimal solver entry T S c d hproc K U hcK hKcap hUone
  have hdeltaNonneg : ∀ e,0≤delta e := fun e => Int.cast_nonneg_iff.mp (hopt.1.2 e).1
  have hdeltaBounds := feasible_unsigned_bounds K delta U hopt.1 hKcap
  have hdeltaCap : ∀ e,0≤delta e ∧ delta e≤K.capacity e := by
    intro e
    exact ⟨hdeltaNonneg e,Int.cast_le.mp (by simpa only [Int.cast_natCast] using (hopt.1.2 e).2)⟩
  have hnextBounds := scratchCostStepMeasured_flow_bounds solver entry T S c d hproc s C U hf hu hUone
  have hscan : ∀ e,(s.flow e).toNat+(delta (Fin.castAdd J.m e)).toNat<2^w ∧
      (delta (Fin.natAdd J.m e)).toNat<2^w := by
    intro e
    have hfNat : (s.flow e).toNat≤U := by
      have h := Int.toNat_le_toNat (hf e).2
      simp only [Int.toNat_natCast] at h
      exact h.trans (hu e)
    exact ⟨(Nat.add_le_add hfNat (hdeltaBounds _).2).trans_lt (by simpa only [Nat.two_mul] using hUdouble),
      (hdeltaBounds _).2.trans_lt hUword⟩
  have hlabelK : (K.m+K.m+K.n+1)*B^10<2^w := by
    have hdim : K.m+K.m+K.n+1=4*J.m+J.n+1 := by change B+B+J.n+1=_; dsimp only [B]; omega
    rw [hdim]
    exact hlabel
  have hpotActual := costStep_potential_update_budget inner s C w hpotBudget
  apply runs_start_le
  unfold costStepBody
  refine runs_seq_assign_le (v := J.n) (step_graph_n (by rfl) hN) ?_
  refine runs_seq_assign_le (v := J.m) (step_graph_m (by rfl) ha1 hM) ?_
  refine runs_seq_assign_le (v := fp) (step_flow_ptr (by rfl) hfpCell) ?_
  refine runs_seq_assign_le (v := pp) (step_pot_ptr (by rfl) hstate1 hppCell) ?_
  refine runs_seq_assign_le (v := s.power) (step_power (by rfl) hstate2 (by omega) hpowerCell) ?_
  refine runs_seq_call_le hkR (vs := [a,fp,heap]) (step_residual_args (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨⟨a,fp,heap,rfl,hgraph,hflow,hgraphEnd,hfpEnd,hf,hinput,by omega⟩,hz,by change heap+(2+10*J.m)<2^w; omega⟩ ?_
  intro residualHeap memR posR hpostR
  obtain ⟨⟨_,_,hframeR,hzR,hgraphR⟩,hretR⟩ := hpostR
  change residualHeap=heap+2+10*J.m at hretR
  change (∀ x<heap,memR x=mem x) at hframeR
  change ZeroFrom memR residualHeap at hzR
  change ListAt memR heap R.solverWords at hgraphR
  have hresWord : residualHeap<2^w := by omega
  have hpotR := hpot.of_agree_below hppEnd hframeR
  refine runs_seq_call_le hkQ (vs := [heap,pp,s.power,C+1,residualHeap])
    (step_rounded_args (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hCword (by omega)) (by wram_words)
    ⟨⟨heap,pp,residualHeap,rfl,hgraphR,hpotR,
      by rw [R.solverWords_length]; change heap+(2+5*B)≤residualHeap; dsimp only [B]; omega,
      by omega,hRwords,hB9,
      (fun e => roundedCost_pre_transfer (hscalar e) hzR (by omega)),by omega⟩,hzR,
      by change residualHeap+(4+17*B)<2^w; omega⟩ ?_
  intro roundedHeap memQ posQ hpostQ
  obtain ⟨⟨_,_,hframeQ,hzQ,hgraphQ⟩,hretQ⟩ := hpostQ
  change roundedHeap=residualHeap+4+17*B at hretQ
  change (∀ x<residualHeap,memQ x=memR x) at hframeQ
  change ZeroFrom memQ roundedHeap at hzQ
  change ListAt memQ (residualHeap+2) K.solverWords at hgraphQ
  have hroundWord : roundedHeap<2^w := by omega
  have hgraphQword : residualHeap+2<2^w := by omega
  have hgraphQEnd : residualHeap+2+K.solverWords.length≤roundedHeap := by rw [K.solverWords_length]; change residualHeap+2+(2+5*B)≤roundedHeap; omega
  refine runs_seq_assign_le (v := residualHeap+2) (step_rounded_ptr (by rfl) hgraphQword (by omega)) ?_
  refine runs_seq_call_le hkP (vs := [residualHeap+2,U,roundedHeap])
    (step_primal_args (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨residualHeap+2,roundedHeap,rfl,hgraphQ,hgraphQEnd,hKwords,by change J.n+1<2^w; omega,by omega,
      hcK,hKcap,hUone,hzQ,by omega⟩ ?_
  intro primalHeap memP posP hpostP
  obtain ⟨hloP,hhiP,hprimalP,hzP,hframeP⟩ := hpostP
  change roundedHeap≤primalHeap at hloP
  change primalHeap≤roundedHeap+scratchCapacityPositiveSpace c d K (B^10) U at hhiP
  change ListAt memP (primalHeap-B) (List.ofFn (fun e => (delta e).toNat)) at hprimalP
  change ZeroFrom memP primalHeap at hzP
  change (∀ x<roundedHeap,memP x=memQ x) at hframeP
  have hprimalWord : primalHeap<2^w := by omega
  have hdeltaWord : primalHeap-B<2^w := by omega
  have hdeltaEnd : primalHeap-B+B≤primalHeap := by omega
  have hgraphP := hgraphQ.of_agree_below hgraphQEnd hframeP
  refine runs_seq_assign_le (v := primalHeap-B) (step_delta_ptr (by rfl) (by rfl) hprimalWord hBword) ?_
  refine runs_seq_call_le hkD (vs := [residualHeap+2,primalHeap-B,U,primalHeap])
    (step_dual_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨residualHeap+2,primalHeap-B,primalHeap,rfl,hgraphP,hprimalP,by omega,hdeltaEnd,hdeltaCap,
      hKwords,hcK,hnU,hnhost,hlabelK,
      hzP,by omega⟩ ?_
  intro dualHeap memD posD hpostD
  obtain ⟨hloD,hhiD,hframeD,hzD,dualPtr,hdualLower,hdualWord,hdualEnd,hdualCell,hdualTable⟩ := hpostD
  change primalHeap≤dualHeap at hloD
  change dualHeap≤primalHeap+scratchCapacityExtractDualSpace c d K delta (B^10) U at hhiD
  change (∀ x<primalHeap,memD x=memP x) at hframeD
  change ZeroFrom memD dualHeap at hzD
  change dualPtr+2*J.n≤dualHeap at hdualEnd
  change primalHeap<dualPtr at hdualLower
  change memD primalHeap=dualPtr at hdualCell
  change SignedTableAt memD dualPtr dual.value at hdualTable
  have hdualHeapWord : dualHeap<2^w := by omega
  have hflowD := (((hflow.of_agree_below (by simpa only [List.length_ofFn] using hfpEnd) hframeR).of_agree_below (by simp only [List.length_ofFn]; omega) hframeQ).of_agree_below
    (by simp only [List.length_ofFn]; omega) hframeP).of_agree_below (by simp only [List.length_ofFn]; omega) hframeD
  have hprimalD := hprimalP.of_agree_below (by simpa only [List.length_ofFn] using hdeltaEnd) hframeD
  refine runs_seq_assign_le (v := dualPtr) (step_dual_ptr (by rfl) hdualCell) ?_
  refine runs_seq_call_le hkA (vs := [fp,primalHeap-B,J.m,dualHeap])
    (step_augment_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨⟨fp,primalHeap-B,dualHeap,rfl,hflowD,hprimalD,by omega,by change primalHeap-B+B≤dualHeap; omega,
      (fun e => (hf e).1),hdeltaNonneg,(fun e => (hnextBounds e).1),hscan,by omega⟩,hzD,
      by change dualHeap+J.m<2^w; omega⟩ ?_
  intro flowHeap memA posA hpostA
  obtain ⟨⟨_,_,hframeA,hzA,hflowA⟩,hretA⟩ := hpostA
  change flowHeap=dualHeap+J.m at hretA
  change (∀ x<dualHeap,memA x=memD x) at hframeA
  change ZeroFrom memA flowHeap at hzA
  change ListAt memA dualHeap (List.ofFn (fun e => (next.flow e).toNat)) at hflowA
  have hflowHeapWord : flowHeap<2^w := by omega
  have hpotD := (((hpotR.of_agree_below (by omega : pp+2*J.n≤residualHeap) hframeQ).of_agree_below
    (by omega : pp+2*J.n≤roundedHeap) hframeP).of_agree_below (by omega : pp+2*J.n≤primalHeap) hframeD).of_agree_below
    (by omega : pp+2*J.n≤dualHeap) hframeA
  have hdualA := hdualTable.of_agree_below hdualEnd hframeA
  refine runs_seq_call_le hkU (vs := [pp,dualPtr,J.n,flowHeap])
    (step_potential_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨⟨pp,dualPtr,flowHeap,rfl,hpotD,hdualA,by omega,by omega,hpotActual,by omega⟩,hzA,
      by change flowHeap+2*J.n<2^w; omega⟩ ?_
  intro potHeap memU posU hpostU
  obtain ⟨⟨_,_,hframeU,hzU,hpotU⟩,hretU⟩ := hpostU
  change potHeap=flowHeap+2*J.n at hretU
  change (∀ x<flowHeap,memU x=memA x) at hframeU
  change ZeroFrom memU potHeap at hzU
  change SignedTableAt memU flowHeap next.potential at hpotU
  have hpotHeapWord : potHeap<2^w := by omega
  have hflowPtrWord : flowHeap-J.m<2^w := by omega
  have hpotPtrWord : potHeap-(J.n+J.n)<2^w := by omega
  refine runs_seq_call_le hkH (vs := [flowHeap-J.m,potHeap-(J.n+J.n),2*s.power,potHeap])
    (step_header_args (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hflowHeapWord hpotHeapWord htwon hpower (by omega))
    (by wram_words) ⟨by rfl,hzU,by change potHeap+3<2^w; omega⟩ ?_
  intro ret memH posH hpostH
  obtain ⟨⟨_,_,hframeH,hzH,hheaderH⟩,hretH⟩ := hpostH
  change ret=potHeap+3 at hretH
  change (∀ x<potHeap,memH x=memU x) at hframeH
  change ZeroFrom memH ret at hzH
  change ListAt memH potHeap [flowHeap-J.m,potHeap-(J.n+J.n),2*s.power] at hheaderH
  have hflowPtr : flowHeap-J.m=dualHeap := by omega
  have hpotPtr : potHeap-(J.n+J.n)=flowHeap := by omega
  have hnewBase : ret-3=potHeap := by omega
  have hflowH := (hflowA.of_agree_below (by simpa only [List.length_ofFn] using (show dualHeap+J.m≤flowHeap by omega)) hframeU).of_agree_below
    (by simp only [List.length_ofFn]; omega) hframeH
  have hpotH := hpotU.of_agree_below (by omega : flowHeap+2*J.n≤potHeap) hframeH
  have hstateH : CostStateAt memH (ret-3) ret next := by
    rw [hnewBase]
    rw [hflowPtr,hpotPtr] at hheaderH
    exact costStateAt_of_arrays hheaderH (by omega) (by omega) hflowH (fun e => (hnextBounds e).1) hpotH
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+scratchCostStepSpace solver entry T S c d hproc s C U ∧
      CostStateAt memH (ret-3) ret next ∧ ZeroFrom memH ret ∧ ∀ x<heap,memH x=mem x
    refine ⟨by omega,?_,hstateH,hzH,?_⟩
    · change ret≤heap+(2+10*J.m+(4+17*B)+scratchCapacityPositiveSpace c d K (B^10) U+
        scratchCapacityExtractDualSpace c d K delta (B^10) U+J.m+2*J.n+3)
      omega
    · intro x hx
      exact (hframeH x (by omega)).trans ((hframeU x (by omega)).trans ((hframeA x (by omega)).trans
        ((hframeD x (by omega)).trans ((hframeP x (by omega)).trans ((hframeQ x (by omega)).trans (hframeR x hx))))))
  · simp only [scratchCostStepContract,residualContract,buildRoundedInstanceContract,scratchCapacityPositiveContract,
      scratchCapacityExtractDualContract,residualAugmentContract,potentialUpdateContract,costHeaderContract,
      heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,
      K,B,delta,inner,solve,dual]
    omega

end MinCostFlow.Final
