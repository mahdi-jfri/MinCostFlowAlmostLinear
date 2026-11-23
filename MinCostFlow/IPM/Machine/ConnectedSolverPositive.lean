module

public import MinCostFlow.IPM.Machine.SolverPositive
public import MinCostFlow.IPM.Machine.ConnectedSolverResources
public import MinCostFlow.IPM.Machine.ConnectedSolverAfterInit
public import MinCostFlow.IPM.Machine.ConnectedSolverAfterInitWithV
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Positive-size runs of the connected bounded solver

The original control program calls the connected startup and passes
its output through the search and recovery on the same heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding Scaling

set_option maxHeartbeats 550000 in
/-- All calls of the positive-size branch run on one heap and write
an optimal integral flow in the designated output prefix (`SolverForestResources`). -/
theorem connectedForestSolverPositive_runs_on {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverForestResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverConnectedAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityForestDataStructuresAt w p entries r (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBody search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBody setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (connectedSolverInitializeContract w J r.qualityExponent (charge (solverConnectedAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverConnectedAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverConnectedAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+forestConnectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+forestConnectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤forestConnectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m + 2*charge (solverConnectedAugmented J).m := by
  let I := solverConnectedAugmented J
  let M := I.m
  let V := solverPenalty J.m
  let L := ipmQualityLimbs M V r.qualityExponent
  let h := dest+J.m
  let g := h+2*J.n
  let b := g+2+5*M
  let f := b+7+L
  let s := f+4*(M*L)
  let T := forestConnectedSolverTimeAt r J.n J.m M
  let Q := charge M
  let S := forestConnectedSolverWorkspaceAt r J.n J.m M
  let nextSpace := connectedForestSolverAfterInitSpace r J hw
  let nextCost := connectedForestSolverAfterInitCharge r J hw
  have hid : connectedSolverInitialPointers J r.qualityExponent h=(g,b,f) := rfl
  have hS : S=connectedSolverInitializeSpace J r.qualityExponent+nextSpace := by
    change forestConnectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m=connectedSolverInitializeSpace J r.qualityExponent+(solverSearchSetupSpace I L+5+
      solverQualityForestSearchReserve r I V hw+solverQualityForestRecoveryReserve r I V J.m)
    rw [forestConnectedSolverWorkspaceAt_eq r J hw]
    dsimp only [I,L,M,V]
    omega
  have hT : T+Q=connectedSolverInitializeCost J r.qualityExponent Q+nextCost+250 := by
    change forestConnectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m+Q=_
    rw [forestConnectedSolverTimeAt_eq r J hw]
    dsimp only [nextCost,connectedForestSolverAfterInitCharge,connectedSolverInitializeCost]
    omega
  have hW := ipm_quality_parameter_words_fit M V r.qualityExponent hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hMw : M<2^w := (show M≤20*M by omega).trans_lt hW.2.2.2.2.2.1
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hLw : L<2^w := hW.2.1
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hm₀ := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  have hlen := J.solverWords_length
  have haDest : a<dest := by omega
  have ha : a<2^w := by omega
  have ha1 : a+1<2^w := by omega
  have hht : h<2^w := by change h+S<2^w at hSpace; omega
  have hN : I.n=J.n+1 := rfl
  have hV : 2≤V := by
    have h := (initialPenaltyWord_intermediates J (solverCapacityBound J.m) hm (le_max_left _ _)).2.1
    change 4*J.m≤V at h
    omega
  have hI : I.IsValid := connectedInitialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hGraphLen := zeroLowerWords_length I hI
  have hBound : 2+5*M≤2+5*J.m+15*J.n := by
    have h := connectedInitialInstance_m_le J.toInstance (V:ℤ)
    rw [Circulation.toInstance_m] at h
    change M≤J.m+2*J.n at h
    omega
  have hsBound : s≤h+connectedSolverInitializeSpace J r.qualityExponent := by
    change s≤h+(2+5*J.m+17*J.n+7+L+4*(M*L))
    dsimp only [s,f,b,g]
    omega
  change h+S<2^w at hSpace
  have hhS : h+connectedSolverInitializeSpace J r.qualityExponent<2^w := by omega
  have hsW : s<2^w := hsBound.trans_lt hhS
  have hsSpace : s+nextSpace<2^w := (Nat.add_le_add_right hsBound _).trans_lt (by omega)
  have hbW : b<2^w := by dsimp only [s,f] at hsW; omega
  have hgW : g<2^w := by dsimp only [b] at hbW; omega
  have hfW : f<2^w := by dsimp only [s] at hsW; omega
  have hdW : dest<2^w := by dsimp only [h] at hht; omega
  have hmW : J.m<2^w := hWords _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hnW : J.n<2^w := hWords _ List.mem_cons_self
  have hNIW : I.n<2^w := by rw [hN]; dsimp only [g] at hgW; omega
  have h2n : 2*J.n<2^w := by dsimp only [g] at hgW; omega
  have hg1 : g+1<2^w := by dsimp only [b] at hbW; omega
  have hg2 : g+2<2^w := by dsimp only [b] at hbW; omega
  have h5M : 5*M<2^w := by dsimp only [b] at hbW; omega
  have hb5 : b+5<2^w := by dsimp only [f] at hfW; omega
  have hb7 : b+7<2^w := by dsimp only [f] at hfW; omega
  have hCap : ∀ e,J.capacity e<2^w := fun e =>
    hWords _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  have h5 : 5<2^w := by omega
  have h7 : 7<2^w := by omega
  have hExec :
      ∃ o st c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
        (startState [a,dest] mem pos) o st c ∧
      (J.Optimal (fun e => (J.readSolverFlow st.mem dest e:ℝ)) ∧ h≤o.value ∧
        o.value≤h+S ∧ ZeroFrom st.mem o.value ∧ (∀ x<dest,st.mem x=mem x) ∧ ∃ x,o=.returned x) ∧
      c≤T+2*Q-12 := by
    apply runs_start_le
    unfold solverPositiveRuntimeBody solverPositiveBodyWith
    refine runs_seq_assign_le (v:=J.m) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h1) ha1) hm₀) ?_
    refine runs_seq_assign_le (v:=J.n) (Expr.eval_load_of_eq rfl hn) ?_
    refine runs_seq_assign_le (v:=h) (Expr.eval_add rfl rfl hht) ?_
    refine runs_seq_call_le hPenaltyProc (vs:=[J.m]) rfl (by wram_words)
      ⟨J.m,rfl,hm,hVw⟩ ?_
    intro v₀ mem₀ p₀ o₀
    change mem₀=mem ∧ v₀=V at o₀
    obtain ⟨hm₀',hv₀⟩ := o₀
    subst mem₀ v₀
    refine runs_seq_call_le hInit (vs:=[a,h]) rfl (by wram_words) ?_ ?_
    · exact ⟨⟨a,h,rfl,hat,hend.trans (Nat.le_add_right _ _),hWords,hm,hc,fun e => ⟨hp e,hu e⟩,hVw,hw⟩,
        fun x hx => hZero x ((Nat.le_add_right _ _).trans hx),hhS⟩
    intro v₁ mem₁ p₁ o₁
    obtain ⟨⟨_,_,hFrame₁,hZero₁,hRows,hParams,hPeriod,hAlpha,hFlow⟩,hEnd₁⟩ := o₁
    change v₁=s at hEnd₁
    subst v₁
    change ∀ x<h,mem₁ x=mem x at hFrame₁
    change ZeroLowerAt mem₁ g I at hRows
    change ListAt mem₁ b (qualityPrecisionWords M V r.qualityExponent) at hParams
    have hReadM : mem₁ (g+1)=M := (zeroLower_header_at I hI mem₁ g hRows.2.2).2
    have hReadL : mem₁ (b+5)=L := hParams 5 (by change 5<6; decide)
    have hInitAt : ConnectedSolverInitializedAt J r.qualityExponent g b f s mem₁ :=
      ⟨hRows,by change g+(zeroLowerWords I).length≤s; rw [hGraphLen]; dsimp only [s,f,b]; omega,
        hParams,hPeriod,hAlpha,by change b+7+L≤s; dsimp only [s,f]; omega,hFlow,
        by change f+M*L≤s; dsimp only [s]; omega⟩
    let as := [g,b,f,s,V,r.qualityExponent,I.n,J.m,dest]
    let nextSpec : Contract := {
      pre := fun args mm => args=as ∧ mm=mem₁
      post := fun _ _ out final => J.Optimal (fun e => (J.readSolverFlow final dest e:ℝ)) ∧
        s≤out ∧ out≤s+nextSpace ∧ ZeroFrom final out ∧ ∀ x<dest,final x=mem₁ x
      cost := fun _ _ => nextCost }
    have hNext : MeetsContract w p proceed nextSpec := by
      apply meetsContract_of_runs hAfter
      intro xs mm pos' ω' _ hpre
      obtain ⟨hA,hMem⟩ := hpre
      change xs=as at hA
      change mm=mem₁ at hMem
      subst xs mm
      obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hZ,hF,hC⟩ :=
        connectedForestSolverAfterInit_runs_on r entries C D hD RC RD J hm hp hc hu hw hDS hSearch hRecover hFinish hSetup hWork
          hLimits g b f s dest mem₁ pos' ω' hInitAt hZero₁ hNIW hV hRadius hLimit hBits hKa hCap
          (by change h≤s; dsimp only [s,f,b,g]; omega) hsSpace
      exact ⟨.returned out,final,c,hRun,⟨hOpt,hLo,hHi,hZ,hF⟩,hC⟩
    refine runs_seq_assign_le (v:=g) (Expr.eval_add rfl (Expr.eval_mul (Expr.eval_const h2) rfl h2n) hgW) ?_
    refine runs_seq_assign_le (v:=M) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h1) hg1) hReadM) ?_
    refine runs_seq_assign_le (v:=b) (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const h2) hg2)
      (Expr.eval_mul (Expr.eval_const h5) rfl h5M) hbW) ?_
    refine runs_seq_assign_le (v:=f) (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const h7) hb7)
      (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h5) hb5) hReadL) hfW) ?_
    refine runs_seq_call_le hQuality (vs:=[M]) rfl (by wram_words) ?_ ?_
    · exact ⟨M, rfl, hMatch.symm ▸ hKa⟩
    intro v₂ mem₂ p₂ h₂
    change mem₂=mem₁ ∧ v₂=k M at h₂
    obtain ⟨rfl, hv₂⟩ := h₂
    rw [hMatch] at hv₂
    subst v₂
    refine runs_seq_call_le hNext (vs:=as) (by
      have hNfit : J.n+1<2^w := hN ▸ hNIW
      refine evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl ?_))))
      refine evalArgs_cons rfl ?_
      rw [hN]
      exact evalArgs_cons (Expr.eval_add rfl (Expr.eval_const h1) hNfit) rfl) ?_
      ⟨rfl,rfl⟩ ?_
    · dsimp only [as]
      wram_words
    intro out final pos' hOut
    obtain ⟨hOpt,hOutLo,hOutHi,hZ,hF⟩ := hOut
    change s≤out at hOutLo
    change out≤s+nextSpace at hOutHi
    have hl : h≤s := by dsimp only [s,f,b,g]; omega
    refine runs_ret_le (v:=out) rfl ?_ ?_
    · exact ⟨hOpt,hl.trans hOutLo,show out≤h+S by omega,hZ,
        fun x hx => (hF x hx).trans (hFrame₁ x (hx.trans_le (Nat.le_add_right _ _))),out,rfl⟩
    · simp only [solverQualityContract,solverPenaltyContract,connectedSolverInitializeContract,heapContract,nextSpec,
        argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_bin,Expr.size_const,Expr.size_reg]
      simp only [List.getD_cons_zero]
      rw [show connectedSolverInitializeCost J r.qualityExponent (charge (solverConnectedAugmented J).m) =
        connectedSolverInitializeCost J r.qualityExponent Q from rfl]
      omega
  obtain ⟨o,st,c,hr,hCert,hcst⟩ := hExec
  obtain ⟨hOpt,hLo,hHi,hZ,hF,x,rfl⟩ := hCert
  exact ⟨x,st,c,hr,hOpt,hLo,hHi,hZ,hF,show c+12≤T+2*Q by omega⟩

/-- All calls of the positive-size branch run on one heap and write
an optimal integral flow in the designated output prefix. -/
theorem connectedSolverPositive_runs_on {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverConnectedAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityConnectedDataStructuresAt w p entries r (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBody search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBody setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (connectedSolverInitializeContract w J r.qualityExponent (charge (solverConnectedAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverConnectedAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverConnectedAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤connectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m + 2*charge (solverConnectedAugmented J).m :=
  connectedForestSolverPositive_runs_on r.toForestResources entries C D hD RC RD J k charge hQuality hMatch
    hm hp hc hu hw hDS.toForest hSearch hRecover hFinish hAfter hInit hPenaltyProc hSetup hWork hLimits a dest
    mem pos ω hat hend hWords hZero hRadius hLimit hBits hKa hSpace

/-- Initialize the connected solver on positive capacities with runtime quality
selection, then run search and recovery to obtain an optimal circulation. -/
theorem connectedSolverPositive_runs {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverConnectedAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresAt w p entries r (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBody search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBody setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (connectedSolverInitializeContract w J r.qualityExponent (charge (solverConnectedAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverConnectedAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverConnectedAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤connectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m + 2*charge (solverConnectedAugmented J).m :=
  connectedSolverPositive_runs_on r entries C D hD RC RD J k charge hQuality hMatch hm hp hc hu
    hw hDS.toConnected hSearch hRecover hFinish hAfter hInit hPenaltyProc hSetup hWork hLimits a dest
    mem pos ω hat hend hWords hZero hRadius hLimit hBits hKa hSpace

set_option maxHeartbeats 550000 in
/-- `V`-passing variant of `connectedForestSolverPositive_runs_on`. -/
theorem connectedForestSolverPositiveWithV_runs_on {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverForestResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverConnectedAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityForestDataStructuresWithVAt w p entries r (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (connectedSolverInitializeContract w J r.qualityExponent (charge (solverConnectedAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverConnectedAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverConnectedAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+forestConnectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+forestConnectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤forestConnectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m + 2*charge (solverConnectedAugmented J).m := by
  let I := solverConnectedAugmented J
  let M := I.m
  let V := solverPenalty J.m
  let L := ipmQualityLimbs M V r.qualityExponent
  let h := dest+J.m
  let g := h+2*J.n
  let b := g+2+5*M
  let f := b+7+L
  let s := f+4*(M*L)
  let T := forestConnectedSolverTimeAt r J.n J.m M
  let Q := charge M
  let S := forestConnectedSolverWorkspaceAt r J.n J.m M
  let nextSpace := connectedForestSolverAfterInitSpace r J hw
  let nextCost := connectedForestSolverAfterInitCharge r J hw
  have hid : connectedSolverInitialPointers J r.qualityExponent h=(g,b,f) := rfl
  have hS : S=connectedSolverInitializeSpace J r.qualityExponent+nextSpace := by
    change forestConnectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m=connectedSolverInitializeSpace J r.qualityExponent+(solverSearchSetupSpace I L+5+
      solverQualityForestSearchReserve r I V hw+solverQualityForestRecoveryReserve r I V J.m)
    rw [forestConnectedSolverWorkspaceAt_eq r J hw]
    dsimp only [I,L,M,V]
    omega
  have hT : T+Q=connectedSolverInitializeCost J r.qualityExponent Q+nextCost+250 := by
    change forestConnectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m+Q=_
    rw [forestConnectedSolverTimeAt_eq r J hw]
    dsimp only [nextCost,connectedForestSolverAfterInitCharge,connectedSolverInitializeCost]
    omega
  have hW := ipm_quality_parameter_words_fit M V r.qualityExponent hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hMw : M<2^w := (show M≤20*M by omega).trans_lt hW.2.2.2.2.2.1
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hLw : L<2^w := hW.2.1
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hm₀ := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  have hlen := J.solverWords_length
  have haDest : a<dest := by omega
  have ha : a<2^w := by omega
  have ha1 : a+1<2^w := by omega
  have hht : h<2^w := by change h+S<2^w at hSpace; omega
  have hN : I.n=J.n+1 := rfl
  have hV : 2≤V := by
    have h := (initialPenaltyWord_intermediates J (solverCapacityBound J.m) hm (le_max_left _ _)).2.1
    change 4*J.m≤V at h
    omega
  have hI : I.IsValid := connectedInitialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hGraphLen := zeroLowerWords_length I hI
  have hBound : 2+5*M≤2+5*J.m+15*J.n := by
    have hs := connectedInitialInstance_m_le J.toInstance (V:ℤ)
    rw [Circulation.toInstance_m] at hs
    change M≤J.m+2*J.n at hs
    omega
  have hsBound : s≤h+connectedSolverInitializeSpace J r.qualityExponent := by
    change s≤h+(2+5*J.m+17*J.n+7+L+4*(M*L))
    dsimp only [s,f,b,g]
    omega
  change h+S<2^w at hSpace
  have hhS : h+connectedSolverInitializeSpace J r.qualityExponent<2^w := by omega
  have hsW : s<2^w := hsBound.trans_lt hhS
  have hsSpace : s+nextSpace<2^w := (Nat.add_le_add_right hsBound _).trans_lt (by omega)
  have hbW : b<2^w := by dsimp only [s,f] at hsW; omega
  have hgW : g<2^w := by dsimp only [b] at hbW; omega
  have hfW : f<2^w := by dsimp only [s] at hsW; omega
  have hdW : dest<2^w := by dsimp only [h] at hht; omega
  have hmW : J.m<2^w := hWords _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hnW : J.n<2^w := hWords _ List.mem_cons_self
  have hNIW : I.n<2^w := by rw [hN]; dsimp only [g] at hgW; omega
  have h2n : 2*J.n<2^w := by dsimp only [g] at hgW; omega
  have hg1 : g+1<2^w := by dsimp only [b] at hbW; omega
  have hg2 : g+2<2^w := by dsimp only [b] at hbW; omega
  have h5M : 5*M<2^w := by dsimp only [b] at hbW; omega
  have hb5 : b+5<2^w := by dsimp only [f] at hfW; omega
  have hb7 : b+7<2^w := by dsimp only [f] at hfW; omega
  have hCap : ∀ e,J.capacity e<2^w := fun e =>
    hWords _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  have h5 : 5<2^w := by omega
  have h7 : 7<2^w := by omega
  have hExec :
      ∃ o st c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
        (startState [a,dest] mem pos) o st c ∧
      (J.Optimal (fun e => (J.readSolverFlow st.mem dest e:ℝ)) ∧ h≤o.value ∧
        o.value≤h+S ∧ ZeroFrom st.mem o.value ∧ (∀ x<dest,st.mem x=mem x) ∧ ∃ x,o=.returned x) ∧
      c≤T+2*Q-12 := by
    apply runs_start_le
    unfold solverPositiveRuntimeBody solverPositiveBodyWith
    refine runs_seq_assign_le (v:=J.m) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h1) ha1) hm₀) ?_
    refine runs_seq_assign_le (v:=J.n) (Expr.eval_load_of_eq rfl hn) ?_
    refine runs_seq_assign_le (v:=h) (Expr.eval_add rfl rfl hht) ?_
    refine runs_seq_call_le hPenaltyProc (vs:=[J.m]) rfl (by wram_words)
      ⟨J.m,rfl,hm,hVw⟩ ?_
    intro v₀ mem₀ p₀ o₀
    change mem₀=mem ∧ v₀=V at o₀
    obtain ⟨hm₀',hv₀⟩ := o₀
    subst mem₀ v₀
    refine runs_seq_call_le hInit (vs:=[a,h]) rfl (by wram_words) ?_ ?_
    · exact ⟨⟨a,h,rfl,hat,hend.trans (Nat.le_add_right _ _),hWords,hm,hc,fun e => ⟨hp e,hu e⟩,hVw,hw⟩,
        fun x hx => hZero x ((Nat.le_add_right _ _).trans hx),hhS⟩
    intro v₁ mem₁ p₁ o₁
    obtain ⟨⟨_,_,hFrame₁,hZero₁,hRows,hParams,hPeriod,hAlpha,hFlow⟩,hEnd₁⟩ := o₁
    change v₁=s at hEnd₁
    subst v₁
    change ∀ x<h,mem₁ x=mem x at hFrame₁
    change ZeroLowerAt mem₁ g I at hRows
    change ListAt mem₁ b (qualityPrecisionWords M V r.qualityExponent) at hParams
    have hReadM : mem₁ (g+1)=M := (zeroLower_header_at I hI mem₁ g hRows.2.2).2
    have hReadL : mem₁ (b+5)=L := hParams 5 (by change 5<6; decide)
    have hInitAt : ConnectedSolverInitializedAt J r.qualityExponent g b f s mem₁ :=
      ⟨hRows,by change g+(zeroLowerWords I).length≤s; rw [hGraphLen]; dsimp only [s,f,b]; omega,
        hParams,hPeriod,hAlpha,by change b+7+L≤s; dsimp only [s,f]; omega,hFlow,
        by change f+M*L≤s; dsimp only [s]; omega⟩
    let as := [g,b,f,s,V,r.qualityExponent,I.n,J.m,dest]
    let nextSpec : Contract := {
      pre := fun args mm => args=as ∧ mm=mem₁
      post := fun _ _ out final => J.Optimal (fun e => (J.readSolverFlow final dest e:ℝ)) ∧
        s≤out ∧ out≤s+nextSpace ∧ ZeroFrom final out ∧ ∀ x<dest,final x=mem₁ x
      cost := fun _ _ => nextCost }
    have hNext : MeetsContract w p proceed nextSpec := by
      apply meetsContract_of_runs hAfter
      intro xs mm pos' ω' _ hpre
      obtain ⟨hA,hMem⟩ := hpre
      change xs=as at hA
      change mm=mem₁ at hMem
      subst xs mm
      obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hZ,hF,hC⟩ :=
        connectedForestSolverAfterInitWithV_runs_on r entries C D hD RC RD J hm hp hc hu hw hDS hSearch hRecover hFinish hSetup hWork
          hLimits g b f s dest mem₁ pos' ω' hInitAt hZero₁ hNIW hV hRadius hLimit hBits hKa hCap
          (by change h≤s; dsimp only [s,f,b,g]; omega) hsSpace
      exact ⟨.returned out,final,c,hRun,⟨hOpt,hLo,hHi,hZ,hF⟩,hC⟩
    refine runs_seq_assign_le (v:=g) (Expr.eval_add rfl (Expr.eval_mul (Expr.eval_const h2) rfl h2n) hgW) ?_
    refine runs_seq_assign_le (v:=M) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h1) hg1) hReadM) ?_
    refine runs_seq_assign_le (v:=b) (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const h2) hg2)
      (Expr.eval_mul (Expr.eval_const h5) rfl h5M) hbW) ?_
    refine runs_seq_assign_le (v:=f) (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const h7) hb7)
      (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h5) hb5) hReadL) hfW) ?_
    refine runs_seq_call_le hQuality (vs:=[M]) rfl (by wram_words) ?_ ?_
    · exact ⟨M, rfl, hMatch.symm ▸ hKa⟩
    intro v₂ mem₂ p₂ h₂
    change mem₂=mem₁ ∧ v₂=k M at h₂
    obtain ⟨rfl, hv₂⟩ := h₂
    rw [hMatch] at hv₂
    subst v₂
    refine runs_seq_call_le hNext (vs:=as) (by
      have hNfit : J.n+1<2^w := hN ▸ hNIW
      refine evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl ?_))))
      refine evalArgs_cons rfl ?_
      rw [hN]
      exact evalArgs_cons (Expr.eval_add rfl (Expr.eval_const h1) hNfit) rfl) ?_
      ⟨rfl,rfl⟩ ?_
    · dsimp only [as]
      wram_words
    intro out final pos' hOut
    obtain ⟨hOpt,hOutLo,hOutHi,hZ,hF⟩ := hOut
    change s≤out at hOutLo
    change out≤s+nextSpace at hOutHi
    have hl : h≤s := by dsimp only [s,f,b,g]; omega
    refine runs_ret_le (v:=out) rfl ?_ ?_
    · exact ⟨hOpt,hl.trans hOutLo,show out≤h+S by omega,hZ,
        fun x hx => (hF x hx).trans (hFrame₁ x (hx.trans_le (Nat.le_add_right _ _))),out,rfl⟩
    · simp only [solverQualityContract,solverPenaltyContract,connectedSolverInitializeContract,heapContract,nextSpec,
        argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_bin,Expr.size_const,Expr.size_reg]
      simp only [List.getD_cons_zero]
      rw [show connectedSolverInitializeCost J r.qualityExponent (charge (solverConnectedAugmented J).m) =
        connectedSolverInitializeCost J r.qualityExponent Q from rfl]
      omega
  obtain ⟨o,st,c,hr,hCert,hcst⟩ := hExec
  obtain ⟨hOpt,hLo,hHi,hZ,hF,x,rfl⟩ := hCert
  exact ⟨x,st,c,hr,hOpt,hLo,hHi,hZ,hF,show c+12≤T+2*Q by omega⟩

/-- `V`-passing variant of `connectedSolverPositive_runs_on`. -/
theorem connectedSolverPositiveWithV_runs_on {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverConnectedAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityConnectedDataStructuresWithVAt w p entries r (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (connectedSolverInitializeContract w J r.qualityExponent (charge (solverConnectedAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverConnectedAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverConnectedAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤connectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m + 2*charge (solverConnectedAugmented J).m :=
  connectedForestSolverPositiveWithV_runs_on r.toForestResources entries C D hD RC RD J k charge hQuality hMatch
    hm hp hc hu hw hDS.toForest hSearch hRecover hFinish hAfter hInit hPenaltyProc hSetup hWork hLimits a dest
    mem pos ω hat hend hWords hZero hRadius hLimit hBits hKa hSpace

/-- `V`-passing variant of `connectedSolverPositive_runs`. -/
theorem connectedSolverPositiveWithV_runs {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverConnectedAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresWithVAt w p entries r (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (connectedSolverInitializeContract w J r.qualityExponent (charge (solverConnectedAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverConnectedAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverConnectedAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+connectedSolverWorkspaceAt r J.n J.m (solverConnectedAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤connectedSolverTimeAt r J.n J.m (solverConnectedAugmented J).m + 2*charge (solverConnectedAugmented J).m :=
  connectedSolverPositiveWithV_runs_on r entries C D hD RC RD J k charge hQuality hMatch hm hp hc hu
    hw hDS.toConnected hSearch hRecover hFinish hAfter hInit hPenaltyProc hSetup hWork hLimits a dest
    mem pos ω hat hend hWords hZero hRadius hLimit hBits hKa hSpace

end MinCostFlow.IPM.Machine
