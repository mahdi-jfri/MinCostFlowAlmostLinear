module

public import MinCostFlow.IPM.Machine.SolverPositive
public import MinCostFlow.IPM.Machine.SolverAfterInitWithV
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# `V`-passing positive-size bounded solver calls
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

set_option maxRecDepth 4096 in
set_option maxHeartbeats 550000 in
private theorem solverPositiveBodyWithV_runs {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (useQuality : Bool) (k charge : ℕ → ℕ)
    (hQuality : useQuality = true → MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : useQuality = true → k (solverAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w)
    (hDS : SolverDataStructuresWithVAt w p entries r (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (solverInitializeContract w J))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverSearchSetupContract w (solverAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hk : r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m))
    (hSpace : dest+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveBodyWith
      (if useQuality then .call 24 entries.quality [.reg 8] else .assign 24 (.const r.qualityExponent))
      penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤solverTimeAt r J.n J.m (solverAugmented J).m + (if useQuality then charge (solverAugmented J).m else 0) := by
  let I := solverAugmented J
  let M := I.m
  let V := solverPenalty J.m
  let L := ipmLimbs M V
  let h := dest+J.m
  let g := h+2*J.n
  let b := g+2+5*M
  let f := b+7+L
  let s := f+4*(M*L)
  let T := solverTimeAt r J.n J.m M
  let Q := if useQuality then charge M else 0
  let S := solverWorkspaceAt r J.n J.m M
  let nextSpace := solverAfterInitSpace r J hw
  let nextCost := solverAfterInitCharge r J hw
  have hid : solverInitialPointers J h=(g,b,f) := rfl
  have hS : S=solverInitializeSpace J+nextSpace := by
    change solverWorkspaceAt r J.n J.m (solverAugmented J).m=solverInitializeSpace J+(solverSearchSetupSpace I L+5+
      solverSearchReserve r I V hw+solverRecoveryReserve r I V J.m)
    rw [solverWorkspaceAt_eq r J hw]
    dsimp only [I,L,M,V]
    omega
  have hT : T=solverInitializeCost J+nextCost+250 := by
    change solverTimeAt r J.n J.m (solverAugmented J).m=_
    rw [solverTimeAt_eq r J hw]
    dsimp only [nextCost,solverAfterInitCharge]
    omega
  have hW := ipm_parameter_words_fit M V hw
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
  have hI : I.IsValid := initialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hGraphLen := zeroLowerWords_length I hI
  have hBound : 2+5*M≤2+5*J.m+5*J.n := by
    have hAux : (deficitVertices J.toInstance).card≤J.n := (Finset.card_filter_le _ _).trans (by simp)
    change 2+5*(initialInstance J.toInstance (V:ℤ)).m≤_
    rw [initialInstance_m,freeEdges_circulation J hp,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
    omega
  have hsBound : s≤h+solverInitializeSpace J := by
    change s≤h+(2+5*J.m+7*J.n+7+L+4*(M*L))
    dsimp only [s,f,b,g]
    omega
  change h+S<2^w at hSpace
  have hhS : h+solverInitializeSpace J<2^w := by omega
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
      ∃ o st c,Runs w p ω (solverPositiveBodyWith
      (if useQuality then .call 24 entries.quality [.reg 8] else .assign 24 (.const r.qualityExponent))
      penalty initEntry proceed)
        (startState [a,dest] mem pos) o st c ∧
      (J.Optimal (fun e => (J.readSolverFlow st.mem dest e:ℝ)) ∧ h≤o.value ∧
        o.value≤h+S ∧ ZeroFrom st.mem o.value ∧ (∀ x<dest,st.mem x=mem x) ∧ ∃ x,o=.returned x) ∧
      c≤T+Q-12 := by
    apply runs_start_le
    unfold solverPositiveBodyWith
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
    change ListAt mem₁ b (precisionWords M V) at hParams
    have hReadM : mem₁ (g+1)=M := (zeroLower_header_at I hI mem₁ g hRows.2.2).2
    have hReadL : mem₁ (b+5)=L := hParams 5 (by change 5<6; decide)
    have hInitAt : SolverInitializedAt J g b f s mem₁ :=
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
        solverAfterInitWithV_runs r entries C D hD RC RD J hm hp hc hu hw hDS hSearch hRecover hFinish hSetup hWork
          hLimits g b f s dest mem₁ pos' ω' hInitAt hZero₁ hNIW hV hRadius hLimit hBits hKa hk hCap
          (by change h≤s; dsimp only [s,f,b,g]; omega) hsSpace
      exact ⟨.returned out,final,c,hRun,⟨hOpt,hLo,hHi,hZ,hF⟩,hC⟩
    refine runs_seq_assign_le (v:=g) (Expr.eval_add rfl (Expr.eval_mul (Expr.eval_const h2) rfl h2n) hgW) ?_
    refine runs_seq_assign_le (v:=M) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h1) hg1) hReadM) ?_
    refine runs_seq_assign_le (v:=b) (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const h2) hg2)
      (Expr.eval_mul (Expr.eval_const h5) rfl h5M) hbW) ?_
    refine runs_seq_assign_le (v:=f) (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const h7) hb7)
      (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const h5) hb5) hReadL) hfW) ?_
    by_cases hUse : useQuality = true
    · simp only [hUse, ite_true]
      refine runs_seq_call_le (hQuality hUse) (vs:=[M]) rfl (by wram_words) ?_ ?_
      · exact ⟨M, rfl, (hMatch hUse).symm ▸ hKa⟩
      intro v₂ mem₂ p₂ h₂
      change mem₂=mem₁ ∧ v₂=k M at h₂
      obtain ⟨rfl, hv₂⟩ := h₂
      rw [hMatch hUse] at hv₂
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
      · simp only [solverQualityContract,solverPenaltyContract,solverInitializeContract,heapContract,nextSpec,
          argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_bin,Expr.size_const,Expr.size_reg]
        simp only [Q, hUse, ite_true, List.getD_cons_zero]
        omega
    · rw [ite_eq_right hUse]
      refine runs_seq_assign_le (v:=r.qualityExponent) (Expr.eval_const hKa) ?_
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
      · simp only [solverPenaltyContract,solverInitializeContract,heapContract,nextSpec,
          argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_bin,Expr.size_const,Expr.size_reg]
        simp only [Q, hUse]
        omega
  obtain ⟨o,st,c,hr,hCert,hcst⟩ := hExec
  obtain ⟨hOpt,hLo,hHi,hZ,hF,x,rfl⟩ := hCert
  exact ⟨x,st,c,hr,hOpt,hLo,hHi,hZ,hF,show c+12≤T+Q by omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 550000 in
/-- `V`-passing variant of `solverPositive_runs`. -/
theorem solverPositiveWithV_runs {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w)
    (hDS : SolverDataStructuresWithVAt w p entries r (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (solverInitializeContract w J))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverSearchSetupContract w (solverAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hk : r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m))
    (hSpace : dest+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveBody r.qualityExponent penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤solverTimeAt r J.n J.m (solverAugmented J).m := by
  simpa [solverPositiveBody] using solverPositiveBodyWithV_runs r entries C D hD RC RD J false
    (fun _ => r.qualityExponent) (fun _ => 0) (by simp) (by simp)
    hm hp hc hu hw hDS hSearch hRecover hFinish hAfter hInit hPenaltyProc hSetup hWork hLimits
    a dest mem pos ω hat hend hWords hZero hRadius hLimit hBits hKa hk hSpace

set_option maxRecDepth 4096 in
set_option maxHeartbeats 550000 in
/-- `V`-passing variant of `solverPositiveRuntime_runs`. -/
theorem solverPositiveRuntimeWithV_runs {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w)
    (hDS : SolverDataStructuresWithVAt w p entries r (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (solverInitializeContract w J))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverSearchSetupContract w (solverAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hk : r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m))
    (hSpace : dest+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤solverTimeAt r J.n J.m (solverAugmented J).m + charge (solverAugmented J).m := by
  simpa [solverPositiveRuntimeBody] using solverPositiveBodyWithV_runs r entries C D hD RC RD J true
    k charge (fun _ => hQuality) (fun _ => hMatch)
    hm hp hc hu hw hDS hSearch hRecover hFinish hAfter hInit hPenaltyProc hSetup hWork hLimits
    a dest mem pos ω hat hend hWords hZero hRadius hLimit hBits hKa hk hSpace

set_option maxHeartbeats 550000 in
/-- `V`-passing variant of `solverPositiveQualityRuntime_runs`. -/
theorem solverPositiveQualityRuntimeWithV_runs {w penalty initEntry proceed setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (k charge : ℕ → ℕ)
    (hQuality : MeetsContract w p entries.quality (solverQualityContract w k charge))
    (hMatch : k (solverAugmented J).m = r.qualityExponent)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresWithVAt w p entries r (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hAfter : p.procs[proceed]?=some (solverAfterInitBodyWithV setup workspace limits finish))
    (hInit : MeetsContract w p initEntry (solverQualityInitializeContract w J r.qualityExponent (charge (solverAugmented J).m)))
    (hPenaltyProc : MeetsContract w p penalty (solverPenaltyContract w))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (a dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hat : ListAt mem a J.solverWords) (hend : a+J.solverWords.length≤dest)
    (hWords : ∀ x∈J.solverWords,x<2^w) (hZero : ZeroFrom mem dest)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hSpace : dest+J.m+solverQualityWorkspaceAt r J.n J.m (solverAugmented J).m<2^w) :
    ∃ out final c,Runs w p ω (solverPositiveRuntimeBody entries.quality penalty initEntry proceed)
      (startState [a,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ dest+J.m≤out ∧
      out≤dest+J.m+solverQualityWorkspaceAt r J.n J.m (solverAugmented J).m ∧
      ZeroFrom final.mem out ∧ (∀ x<dest,final.mem x=mem x) ∧
      c+12≤solverQualityTimeAt r J.n J.m (solverAugmented J).m + 2*charge (solverAugmented J).m := by
  let I := solverAugmented J
  let M := I.m
  let V := solverPenalty J.m
  let L := ipmQualityLimbs M V r.qualityExponent
  let h := dest+J.m
  let g := h+2*J.n
  let b := g+2+5*M
  let f := b+7+L
  let s := f+4*(M*L)
  let T := solverQualityTimeAt r J.n J.m M
  let Q := charge M
  let S := solverQualityWorkspaceAt r J.n J.m M
  let nextSpace := solverQualityAfterInitSpace r J hw
  let nextCost := solverQualityAfterInitCharge r J hw
  have hid : solverQualityInitialPointers J r.qualityExponent h=(g,b,f) := rfl
  have hS : S=solverQualityInitializeSpace J r.qualityExponent+nextSpace := by
    change solverQualityWorkspaceAt r J.n J.m (solverAugmented J).m=solverQualityInitializeSpace J r.qualityExponent+(solverSearchSetupSpace I L+5+
      solverQualitySearchReserve r I V hw+solverQualityRecoveryReserve r I V J.m)
    rw [solverQualityWorkspaceAt_eq r J hw]
    dsimp only [I,L,M,V]
    omega
  have hT : T+Q=solverQualityInitializeCost J r.qualityExponent Q+nextCost+250 := by
    change solverQualityTimeAt r J.n J.m (solverAugmented J).m+Q=_
    rw [solverQualityTimeAt_eq r J hw]
    dsimp only [nextCost,solverQualityAfterInitCharge,solverQualityInitializeCost]
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
  have hI : I.IsValid := initialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hGraphLen := zeroLowerWords_length I hI
  have hBound : 2+5*M≤2+5*J.m+5*J.n := by
    have hAux : (deficitVertices J.toInstance).card≤J.n := (Finset.card_filter_le _ _).trans (by simp)
    change 2+5*(initialInstance J.toInstance (V:ℤ)).m≤_
    rw [initialInstance_m,freeEdges_circulation J hp,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
    omega
  have hsBound : s≤h+solverQualityInitializeSpace J r.qualityExponent := by
    change s≤h+(2+5*J.m+7*J.n+7+L+4*(M*L))
    dsimp only [s,f,b,g]
    omega
  change h+S<2^w at hSpace
  have hhS : h+solverQualityInitializeSpace J r.qualityExponent<2^w := by omega
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
    have hInitAt : SolverQualityInitializedAt J r.qualityExponent g b f s mem₁ :=
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
        solverQualityAfterInitWithV_runs r entries C D hD RC RD J hm hp hc hu hw hDS hSearch hRecover hFinish hSetup hWork
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
    · simp only [solverQualityContract,solverPenaltyContract,solverQualityInitializeContract,heapContract,nextSpec,
        argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_bin,Expr.size_const,Expr.size_reg]
      simp only [List.getD_cons_zero]
      rw [show solverQualityInitializeCost J r.qualityExponent (charge (solverAugmented J).m) =
        solverQualityInitializeCost J r.qualityExponent Q from rfl]
      omega
  obtain ⟨o,st,c,hr,hCert,hcst⟩ := hExec
  obtain ⟨hOpt,hLo,hHi,hZ,hF,x,rfl⟩ := hCert
  exact ⟨x,st,c,hr,hOpt,hLo,hHi,hZ,hF,show c+12≤T+2*Q by omega⟩

end MinCostFlow.IPM.Machine