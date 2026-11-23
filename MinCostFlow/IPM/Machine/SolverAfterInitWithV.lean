module

public import MinCostFlow.IPM.Machine.SolverAfterInit
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# `V`-passing solver after-init drivers

Threads `V = solverPenalty J.m` from `.reg 4` through `solverAfterInitBodyWithV`
and `solverSearchRecoverBodyWithV`.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

set_option maxRecDepth 4096 in
set_option maxHeartbeats 580000 in
/-- `V`-passing variant of `solverAfterInit_runs`. -/
theorem solverAfterInitWithV_runs {w setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w)
    (hDS : SolverDataStructuresWithVAt w p entries r (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hSetup : MeetsContract w p setup (solverSearchSetupContract w (solverAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (g b f h dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hi : SolverInitializedAt J g b f h mem) (hZero : ZeroFrom mem h)
    (hN : (solverAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hk : r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m))
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤h)
    (hSpace : h+solverAfterInitSpace r J hw<2^w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    ∃ out final c, Runs w p ω (solverAfterInitBodyWithV setup workspace limits finish)
      (startState [g,b,f,h,V,r.qualityExponent,I.n,J.m,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      h≤out ∧ out≤h+solverAfterInitSpace r J hw ∧ ZeroFrom final.mem out ∧
      (∀ a<dest, final.mem a=mem a) ∧ c≤solverAfterInitCharge r J hw := by
  dsimp only
  let I := solverAugmented J
  let M := I.m
  let V := solverPenalty J.m
  let L := ipmLimbs M V
  let P := ipmPrecision M V
  let E := ipmRangeExponent M V
  let j := Num.IPM.alphaExponent M V
  let k := r.qualityExponent
  let F := ipmMinRatioFormat M V hw
  let B := r.cycleSpace I.n M
  let S := solverSearchReserve r I V hw
  let Q := solverRecoveryReserve r I V J.m
  let la := Num.IPM.lengthArraySpace M L P E
  let ga := Num.IPM.gradientArraySpace M L P E
  let wa := h+solverSearchSetupSpace I L
  let ra := wa+2
  let ht := ra+3
  let radius := M*V^2
  let limit := targetTestLimit M V k
  let old := solverEpochLayout I L E g (b+7) h
  let qp := old.slackMin+2*L
  have hS₀ : h+solverAfterInitSpace r J hw=ht+S+Q := by
    change h+(solverSearchSetupSpace I L+5+S+Q)=ht+S+Q
    dsimp only [ht,ra,wa]
    omega
  rw [hS₀] at hSpace
  have hW := ipm_parameter_words_fit M V hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hL : 0 < L := by unfold L ipmLimbs; omega
  have hLw : L<2^w := hW.2.1
  have hPw : P<2^w := hW.2.2.1
  have hEw : E<2^w := hW.2.2.2.1
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hjw : j<2^w := ((Num.IPM.alphaExponent_le_iff M V _).mpr Nat.lt_two_pow_self.le).trans_lt
    (Nat.lt_of_succ_lt hW.2.2.2.2.2.2.1)
  have hMw : M<2^w := (show M≤20*M by omega).trans_lt hW.2.2.2.2.2.1
  have hM : 0 < M := hm.trans_le (solverAugmented_size J hp).1
  have hSize : 2≤M*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤M from hM))
  have hJw : J.m<2^w := (solverAugmented_size J hp).1.trans_lt hMw
  have hI : I.IsValid := initialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hNums : NumbersBounded I V := (solverAugmented_numbers J hm hc hu).2.1
  have hge : g+(zeroLowerWords I).length≤h := hi.rowsEnd
  have hbe : b+7+L≤h := hi.paramsEnd
  have hfe : f+M*L≤h := hi.flowEnd
  have hge1 : g+1≤h := by rw [zeroLowerWords_length I hI] at hge; omega
  have hGe : g+1<2^w := by dsimp only [ht,ra,wa] at hSpace; omega
  have hgW : g<2^w := by omega
  have hhW : h<2^w := by dsimp only [ht,ra,wa] at hSpace; omega
  have hwaW : wa<2^w := by dsimp only [ht,ra] at hSpace; omega
  have hraW : ra<2^w := by dsimp only [ht] at hSpace; omega
  have hhT : ht<2^w := by omega
  have hB2 : b+2<2^w := by omega
  have hB4 : b+4<2^w := by omega
  have hB5 : b+5<2^w := by omega
  have hB6 : b+6<2^w := by omega
  have hReadM : mem (g+1)=M := (zeroLower_header_at I hI mem g hi.rows.2.2).2
  have hReadE : mem (b+2)=E := hi.params 2 (by change 2<6; decide)
  have hReadP : mem (b+4)=P := hi.params 4 (by change 4<6; decide)
  have hReadL : mem (b+5)=L := hi.params 5 (by change 5<6; decide)
  have hReadJ : mem (b+6)=j := hi.period
  have hNamedWords := zeroLowerWords_fit I hI V w hNums hN hMw hVw (by omega)
  have hWArr : la+ga≤S := by
    have hl₁ : la+ga≤targetStageSpace F M E B := by
      change Num.IPM.lengthArraySpace M F.limbs F.fmt.precision E+
        Num.IPM.gradientArraySpace M F.limbs F.fmt.precision E≤_
      unfold targetStageSpace
      omega
    have h₁ : 1≤limit := by unfold limit targetTestLimit; omega
    have h₂ : targetStageSpace F M E B≤limit*targetStageSpace F M E B := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (targetStageSpace F M E B) h₁
    have h₃ : limit*targetStageSpace F M E B≤targetOffsetSpace F M V k E B := by
      unfold targetOffsetSpace
      dsimp only [limit]
      omega
    have h₄ : targetOffsetSpace F M V k E B≤S := by
      change _≤(targetSearchRounds radius+1)*_
      exact Nat.le_mul_of_pos_left _ (by omega)
    exact hl₁.trans (h₂.trans (h₃.trans h₄))
  have hWorkSpace : wa+2+la+ga<2^w := by dsimp only [ht,ra] at hSpace; omega
  have hLimitSpace : ra+3<2^w := hhT
  have hSSetup : h+solverSearchSetupSpace I L<2^w := hwaW
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hFour : 4<2^w := by omega
  have hFive : 5<2^w := by omega
  have hSix : 6<2^w := by omega
  let args := [g,b,f,h,V,r.qualityExponent,I.n,J.m,dest]
  let certificate : Outcome → State → Prop := fun o st =>
    J.Optimal (fun e => (J.readSolverFlow st.mem dest e:ℝ)) ∧
    h≤o.value ∧ o.value≤ht+S+Q ∧ ZeroFrom st.mem o.value ∧
    (∀ a<dest,st.mem a=mem a) ∧ ∃ x,o=.returned x
  have hRun :
      ∃ o st c,Runs w p ω (solverAfterInitBodyWithV setup workspace limits finish)
        (startState args mem pos) o st c ∧ certificate o st ∧ c≤solverAfterInitCharge r J hw := by
    apply runs_start_le
    unfold solverAfterInitBodyWithV
    refine runs_seq_assign_le (v:=M) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hOne) hGe) hReadM) ?_
    refine runs_seq_assign_le (v:=L) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hFive) hB5) hReadL) ?_
    refine runs_seq_assign_le (v:=P) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hFour) hB4) hReadP) ?_
    refine runs_seq_assign_le (v:=E) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hTwo) hB2) hReadE) ?_
    refine runs_seq_assign_le (v:=j) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hSix) hB6) hReadJ) ?_
    refine runs_seq_call_le hSetup (vs:=[g,E,L,P,k,j,h]) rfl (by wram_words) ?_ ?_
    · exact ⟨⟨g,h,rfl,hI,hM,by omega,hSize,hk,hw,hi.rows,hi.rowsEnd,hNamedWords,hNums⟩,hZero,hSSetup⟩
    intro v₁ mem₁ pos₁ o₁
    obtain ⟨⟨_,_,hFrame₁,hZero₁,hTables⟩,hEnd₁⟩ := o₁
    change v₁=wa at hEnd₁
    subst v₁
    change ∀ x<h,mem₁ x=mem x at hFrame₁
    change SolverSearchTablesAt I V k g (b+7) h mem₁ at hTables
    refine runs_seq_call_le hWork (vs:=[M,L,P,E,wa]) rfl (by wram_words)
      ⟨⟨M,L,P,E,wa,rfl,hM,hL,hWorkSpace⟩,hZero₁,by exact hraW⟩ ?_
    intro v₂ mem₂ pos₂ o₂
    obtain ⟨⟨_,_,hFrame₂,hZero₂,hWorkAt⟩,hEnd₂⟩ := o₂
    change v₂=ra at hEnd₂
    subst v₂
    change ∀ x<wa,mem₂ x=mem₁ x at hFrame₂
    change ListAt mem₂ wa [la,ga] at hWorkAt
    refine runs_seq_call_le hLimits (vs:=[M,V,k,j,ra]) rfl (by wram_words)
      ⟨⟨M,V,k,ra,rfl,hSize,hRadius,hLimit,hBits⟩,hZero₂,hLimitSpace⟩ ?_
    intro v₃ mem₃ pos₃ o₃
    obtain ⟨⟨_,_,hFrame₃,hZero₃,hLimitAt⟩,hEnd₃⟩ := o₃
    change v₃=ht at hEnd₃
    subst v₃
    change ∀ x<ra,mem₃ x=mem₂ x at hFrame₃
    change ListAt mem₃ ra (solverLimitWords M V k) at hLimitAt
    have hWorkAt' : ListAt mem₃ wa [la,ga] := hWorkAt.of_agree_below (show wa+2≤ra from le_rfl) hFrame₃
    have hFrame : ∀ x<h,mem₃ x=mem x := fun x hx =>
      (hFrame₃ x (by dsimp only [ra,wa]; omega)).trans
        ((hFrame₂ x (by dsimp only [wa]; omega)).trans (hFrame₁ x hx))
    have hi' := hi.frozen hFrame (show h≤ht by dsimp only [ht,ra,wa]; omega)
    have hFixed := solverSearchTables_fixed I V k g (b+7) h mem₁ hw hTables hI hN hMw hNamedWords
      hi.rowsEnd hi.paramsEnd (freezeScalar hFrame₁ hi.paramsEnd hi.exponent)
    have hFrame' : ∀ x<wa,mem₃ x=mem₁ x := fun x hx =>
      (hFrame₃ x (by dsimp only [ra]; omega)).trans (hFrame₂ x hx)
    have hFixed' := hFixed.frozen hFrame' (show wa≤ht by dsimp only [ht,ra]; omega)
    obtain ⟨hStage,hHalf⟩ := solverInitialFlow_stage J V f ht mem₃ hm (by omega) hp hw hi'.flowEnd hNums hi'.flow
    have hReady : old.exponent=F.rangeExponent ∧ TargetFixedInputs F I old qp qp ht (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime M V/32)^2/50) (Num.IPM.alphaPrime M V) mem₃ ∧
        TargetStageFlow F I old.exponent f ht mem₃ ∧
        (∀ e,(1/2:ℝ)≤epochVector F I mem₃ f e-(I.edge e).lower ∧
          (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem₃ f e) ∧
        ZeroLowerAt mem₃ old.graph I ∧ ZeroFrom mem₃ ht :=
      ⟨rfl,hFixed',hStage,hHalf,hi'.rows,hZero₃⟩
    let preArgs := targetOffsetPacket old F I 0 qp f ht limit radius++[targetSearchRounds radius,I.n,J.m,dest,V]
    let finishSpec : Contract := {
      pre := fun as mem' => as=preArgs ∧ mem'=mem₃
      post := fun _ _ out final => J.Optimal (fun e => (J.readSolverFlow final dest e:ℝ)) ∧
        ht≤out ∧ out≤ht+S+Q ∧ ZeroFrom final out ∧ ∀ a<dest,final a=mem₃ a
      cost := fun _ _ => solverSearchCharge r I V hw+solverRecoveryCharge r I V J.m+50 }
    have hFinishSpec : MeetsContract w p finish finishSpec := by
      apply meetsContract_of_runs hFinish
      intro xs initial position ω' _ hpre
      obtain ⟨hArgs,hInitial⟩ := hpre
      change xs=preArgs at hArgs
      change initial=mem₃ at hInitial
      subst xs initial
      obtain ⟨out,final,c,hRun,hOpt,hLow,hHigh,hZ,hF,hC⟩ :=
        solverFinishWithV_runs r entries C D hD RC RD J hm hp hc hu hw hDS hSearch hRecover old qp f ht dest
          mem₃ position ω' hReady hN hV hRadius hLimit hk hCap (by dsimp only [ht,ra,wa]; omega) hSpace
      exact ⟨.returned out,final,c,hRun,⟨hOpt,hLow,hHigh,hZ,hF⟩,hC⟩
    let c := solverCoefficientBase I h
    let s := solverGuardBase I L h
    have hcDef : c=h+2+I.n+3*M := rfl
    have hsDef : s=c+9*(M*L)+L := by change c+(9*M+1)*L=_; ring
    have hsa : s+5*L=wa := by
      unfold s wa solverGuardBase solverSearchSetupSpace solverCoefficientBase
      omega
    have hcW : c<2^w := by omega
    have hlM : M*L<2^w := by omega
    have h3M : 3*M<2^w := by omega
    have hH2 : h+2<2^w := by omega
    have hH2N : h+2+I.n<2^w := by omega
    have h9ML : 9*(M*L)<2^w := by omega
    have hc9ML : c+9*(M*L)<2^w := by omega
    have hsW : s<2^w := by omega
    have hCExpr : h+2+I.n+3*M<2^w := hcDef ▸ hcW
    refine runs_seq_assign_le (v:=c) (by
      exact Expr.eval_add (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const hTwo) hH2) rfl hH2N)
        (Expr.eval_mul (Expr.eval_const (show 3<2^w by omega)) rfl h3M) hCExpr) ?_
    refine runs_seq_assign_le (v:=M*L) (Expr.eval_mul rfl rfl hlM) ?_
    refine runs_seq_assign_le (v:=s) (by
      exact (congrArg some hsDef.symm) ▸ Expr.eval_add
        (Expr.eval_add rfl (Expr.eval_mul (Expr.eval_const (show 9<2^w by omega)) rfl h9ML) hc9ML)
        rfl (hsDef ▸ hsW)) ?_
    refine runs_seq_call_le hFinishSpec (vs:=preArgs)
      (solverStartSearchArgsWithV_eval I F L E g b f h ht dest J.m limit radius wa ra V _ (by
        exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩)
        rfl (hWorkAt' 0 (by change 0<2; decide)) (hWorkAt' 1 (by change 1<2; decide))
        (hLimitAt 0 (by change 0<3; decide)) (hLimitAt 1 (by change 1<3; decide)) (hLimitAt 2 (by change 2<3; decide))
        (by dsimp only [ht,ra] at hhT ⊢; exact max_lt (by omega) (by omega)) hhT (by omega)
        (by rw [hsa]; dsimp only [ht,ra]; omega) (by omega)) ?_ ⟨rfl,rfl⟩ ?_
    · have hPacket := solverTargetPacket_words I V k E B F old qp f ht mem₃ _ _ hFixed'
        (by have hh := hi'.flowEnd; change f+M*L≤ht at hh; omega)
        hMw rfl hEw hRadius hLimit (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSpace)
      have hRounds : targetSearchRounds radius<2^w := ((Nat.size_le).mpr hRadius).trans_lt Nat.lt_two_pow_self
      intro x hx
      simp only [preArgs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hIn | rfl | rfl | rfl | rfl | rfl
      · exact hPacket _ hIn
      · exact hRounds
      · exact hN
      · exact hJw
      · omega
      · exact hVw
    intro out final finalPos hOut
    obtain ⟨hOpt,hOutLo,hOutHi,hZ,hF⟩ := hOut
    change ht≤out at hOutLo
    change out≤ht+S+Q at hOutHi
    have hiW : out<2^w := hOutHi.trans_lt hSpace
    have hh : h≤ht := by dsimp only [ht,ra,wa]; omega
    refine runs_ret_le (v:=out) rfl ?_ ?_
    · exact ⟨hOpt,hh.trans hOutLo,hOutHi,hZ,
        fun a ha => (hF a ha).trans (hFrame a (ha.trans_le (by omega))),out,rfl⟩
    · simp only [solverAfterInitCharge,solverSearchSetupContract,workspaceContract,solverLimitsContract,heapContract,
        finishSpec,argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_const,Expr.size_bin,Expr.size_load,
        List.getD_cons_succ,List.getD_cons_zero]
      have hc : argsSize solverStartSearchArgsWithV≤100 := by decide
      dsimp only [V,I,M,E,P,L,radius]
      omega
  obtain ⟨o,st,c,hr,hCert,hcst⟩ := hRun
  obtain ⟨hOpt,hLo,hHi,hZ,hF,x,rfl⟩ := hCert
  exact ⟨x,st,c,hr,hOpt,hLo,hHi.trans_eq hS₀.symm,hZ,hF,hcst⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 580000 in
/-- `V`-passing variant of `solverQualityAfterInit_runs`. -/
theorem solverQualityAfterInitWithV_runs {w setup workspace limits finish search recover : ℕ} {p : Program}
    (r : SolverResources) (entries : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec) (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) r.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresWithVAt w p entries r (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entries.cycleInit entries.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entries.forestInit entries.forestOp))
    (hFinish : p.procs[finish]?=some (solverSearchRecoverBodyWithV search recover))
    (hSetup : MeetsContract w p setup (solverQualitySearchSetupContract w (solverAugmented J) (solverPenalty J.m) r.qualityExponent))
    (hWork : MeetsContract w p workspace (workspaceContract w))
    (hLimits : MeetsContract w p limits (solverLimitsContract w))
    (g b f h dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hi : SolverQualityInitializedAt J r.qualityExponent g b f h mem) (hZero : ZeroFrom mem h)
    (hN : (solverAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) r.qualityExponent<2^w)
    (hBits : (solverAugmented J).m.size+(solverPenalty J.m).size<2^w)
    (hKa : r.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤h)
    (hSpace : h+solverQualityAfterInitSpace r J hw<2^w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    ∃ out final c, Runs w p ω (solverAfterInitBodyWithV setup workspace limits finish)
      (startState [g,b,f,h,V,r.qualityExponent,I.n,J.m,dest] mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      h≤out ∧ out≤h+solverQualityAfterInitSpace r J hw ∧ ZeroFrom final.mem out ∧
      (∀ a<dest, final.mem a=mem a) ∧ c≤solverQualityAfterInitCharge r J hw := by
  dsimp only
  let I := solverAugmented J
  let M := I.m
  let V := solverPenalty J.m
  let L := ipmQualityLimbs M V r.qualityExponent
  let P := ipmQualityPrecision M V r.qualityExponent
  let E := ipmQualityRangeExponent M V r.qualityExponent
  let j := Num.IPM.alphaExponent M V
  let k := r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent hw
  let B := r.cycleSpace I.n M
  let S := solverQualitySearchReserve r I V hw
  let Q := solverQualityRecoveryReserve r I V J.m
  let la := Num.IPM.lengthArraySpace M L P E
  let ga := Num.IPM.gradientArraySpace M L P E
  let wa := h+solverSearchSetupSpace I L
  let ra := wa+2
  let ht := ra+3
  let radius := M*V^2
  let limit := targetTestLimit M V k
  let old := solverEpochLayout I L E g (b+7) h
  let qp := old.slackMin+2*L
  have hS₀ : h+solverQualityAfterInitSpace r J hw=ht+S+Q := by
    change h+(solverSearchSetupSpace I L+5+S+Q)=ht+S+Q
    dsimp only [ht,ra,wa]
    omega
  rw [hS₀] at hSpace
  have hW := ipm_quality_parameter_words_fit M V r.qualityExponent hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hL : 0 < L := by unfold L ipmQualityLimbs; omega
  have hLw : L<2^w := hW.2.1
  have hPw : P<2^w := hW.2.2.1
  have hEw : E<2^w := hW.2.2.2.1
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hjw : j<2^w := ((Num.IPM.alphaExponent_le_iff M V _).mpr Nat.lt_two_pow_self.le).trans_lt
    (Nat.lt_of_succ_lt hW.2.2.2.2.2.2.1)
  have hMw : M<2^w := (show M≤20*M by omega).trans_lt hW.2.2.2.2.2.1
  have hM : 0 < M := hm.trans_le (solverAugmented_size J hp).1
  have hSize : 2≤M*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤M from hM))
  have hJw : J.m<2^w := (solverAugmented_size J hp).1.trans_lt hMw
  have hI : I.IsValid := initialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hNums : NumbersBounded I V := (solverAugmented_numbers J hm hc hu).2.1
  have hge : g+(zeroLowerWords I).length≤h := hi.rowsEnd
  have hbe : b+7+L≤h := hi.paramsEnd
  have hfe : f+M*L≤h := hi.flowEnd
  have hge1 : g+1≤h := by rw [zeroLowerWords_length I hI] at hge; omega
  have hGe : g+1<2^w := by dsimp only [ht,ra,wa] at hSpace; omega
  have hgW : g<2^w := by omega
  have hhW : h<2^w := by dsimp only [ht,ra,wa] at hSpace; omega
  have hwaW : wa<2^w := by dsimp only [ht,ra] at hSpace; omega
  have hraW : ra<2^w := by dsimp only [ht] at hSpace; omega
  have hhT : ht<2^w := by omega
  have hB2 : b+2<2^w := by omega
  have hB4 : b+4<2^w := by omega
  have hB5 : b+5<2^w := by omega
  have hB6 : b+6<2^w := by omega
  have hReadM : mem (g+1)=M := (zeroLower_header_at I hI mem g hi.rows.2.2).2
  have hReadE : mem (b+2)=E := hi.params 2 (by change 2<6; decide)
  have hReadP : mem (b+4)=P := hi.params 4 (by change 4<6; decide)
  have hReadL : mem (b+5)=L := hi.params 5 (by change 5<6; decide)
  have hReadJ : mem (b+6)=j := hi.period
  have hNamedWords := zeroLowerWords_fit I hI V w hNums hN hMw hVw (by omega)
  have hWArr : la+ga≤S := by
    have hl₁ : la+ga≤targetStageSpace F M E B := by
      change Num.IPM.lengthArraySpace M F.limbs F.fmt.precision E+
        Num.IPM.gradientArraySpace M F.limbs F.fmt.precision E≤_
      unfold targetStageSpace
      omega
    have h₁ : 1≤limit := by unfold limit targetTestLimit; omega
    have h₂ : targetStageSpace F M E B≤limit*targetStageSpace F M E B := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (targetStageSpace F M E B) h₁
    have h₃ : limit*targetStageSpace F M E B≤targetOffsetSpace F M V k E B := by
      unfold targetOffsetSpace
      dsimp only [limit]
      omega
    have h₄ : targetOffsetSpace F M V k E B≤S := by
      change _≤(targetSearchRounds radius+1)*_
      exact Nat.le_mul_of_pos_left _ (by omega)
    exact hl₁.trans (h₂.trans (h₃.trans h₄))
  have hWorkSpace : wa+2+la+ga<2^w := by dsimp only [ht,ra] at hSpace; omega
  have hLimitSpace : ra+3<2^w := hhT
  have hSSetup : h+solverSearchSetupSpace I L<2^w := hwaW
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hFour : 4<2^w := by omega
  have hFive : 5<2^w := by omega
  have hSix : 6<2^w := by omega
  let args := [g,b,f,h,V,r.qualityExponent,I.n,J.m,dest]
  let certificate : Outcome → State → Prop := fun o st =>
    J.Optimal (fun e => (J.readSolverFlow st.mem dest e:ℝ)) ∧
    h≤o.value ∧ o.value≤ht+S+Q ∧ ZeroFrom st.mem o.value ∧
    (∀ a<dest,st.mem a=mem a) ∧ ∃ x,o=.returned x
  have hRun :
      ∃ o st c,Runs w p ω (solverAfterInitBodyWithV setup workspace limits finish)
        (startState args mem pos) o st c ∧ certificate o st ∧ c≤solverQualityAfterInitCharge r J hw := by
    apply runs_start_le
    unfold solverAfterInitBodyWithV
    refine runs_seq_assign_le (v:=M) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hOne) hGe) hReadM) ?_
    refine runs_seq_assign_le (v:=L) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hFive) hB5) hReadL) ?_
    refine runs_seq_assign_le (v:=P) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hFour) hB4) hReadP) ?_
    refine runs_seq_assign_le (v:=E) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hTwo) hB2) hReadE) ?_
    refine runs_seq_assign_le (v:=j) (Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hSix) hB6) hReadJ) ?_
    refine runs_seq_call_le hSetup (vs:=[g,E,L,P,k,j,h]) rfl (by wram_words) ?_ ?_
    · exact ⟨⟨g,h,rfl,hI,hM,by omega,hSize,hw,hi.rows,hi.rowsEnd,hNamedWords,hNums⟩,hZero,hSSetup⟩
    intro v₁ mem₁ pos₁ o₁
    obtain ⟨⟨_,_,hFrame₁,hZero₁,hTables⟩,hEnd₁⟩ := o₁
    change v₁=wa at hEnd₁
    subst v₁
    change ∀ x<h,mem₁ x=mem x at hFrame₁
    change SolverQualitySearchTablesAt I V k g (b+7) h mem₁ at hTables
    refine runs_seq_call_le hWork (vs:=[M,L,P,E,wa]) rfl (by wram_words)
      ⟨⟨M,L,P,E,wa,rfl,hM,hL,hWorkSpace⟩,hZero₁,by exact hraW⟩ ?_
    intro v₂ mem₂ pos₂ o₂
    obtain ⟨⟨_,_,hFrame₂,hZero₂,hWorkAt⟩,hEnd₂⟩ := o₂
    change v₂=ra at hEnd₂
    subst v₂
    change ∀ x<wa,mem₂ x=mem₁ x at hFrame₂
    change ListAt mem₂ wa [la,ga] at hWorkAt
    refine runs_seq_call_le hLimits (vs:=[M,V,k,j,ra]) rfl (by wram_words)
      ⟨⟨M,V,k,ra,rfl,hSize,hRadius,hLimit,hBits⟩,hZero₂,hLimitSpace⟩ ?_
    intro v₃ mem₃ pos₃ o₃
    obtain ⟨⟨_,_,hFrame₃,hZero₃,hLimitAt⟩,hEnd₃⟩ := o₃
    change v₃=ht at hEnd₃
    subst v₃
    change ∀ x<ra,mem₃ x=mem₂ x at hFrame₃
    change ListAt mem₃ ra (solverLimitWords M V k) at hLimitAt
    have hWorkAt' : ListAt mem₃ wa [la,ga] := hWorkAt.of_agree_below (show wa+2≤ra from le_rfl) hFrame₃
    have hFrame : ∀ x<h,mem₃ x=mem x := fun x hx =>
      (hFrame₃ x (by dsimp only [ra,wa]; omega)).trans
        ((hFrame₂ x (by dsimp only [wa]; omega)).trans (hFrame₁ x hx))
    have hi' := hi.frozen hFrame (show h≤ht by dsimp only [ht,ra,wa]; omega)
    have hFixed := solverQualitySearchTables_fixed I V k g (b+7) h mem₁ hw hTables hI hN hMw hNamedWords
      hi.rowsEnd hi.paramsEnd (freezeScalar hFrame₁ hi.paramsEnd hi.exponent)
    have hFrame' : ∀ x<wa,mem₃ x=mem₁ x := fun x hx =>
      (hFrame₃ x (by dsimp only [ra]; omega)).trans (hFrame₂ x hx)
    have hFixed' := hFixed.frozen hFrame' (show wa≤ht by dsimp only [ht,ra]; omega)
    obtain ⟨hStage,hHalf⟩ := solverQualityInitialFlow_stage J V k f ht mem₃ hm (by omega) hp hw hi'.flowEnd hNums hi'.flow
    have hReady : old.exponent=F.rangeExponent ∧ TargetFixedInputs F I old qp qp ht (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime M V/32)^2/50) (Num.IPM.alphaPrime M V) mem₃ ∧
        TargetStageFlow F I old.exponent f ht mem₃ ∧
        (∀ e,(1/2:ℝ)≤epochVector F I mem₃ f e-(I.edge e).lower ∧
          (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem₃ f e) ∧
        ZeroLowerAt mem₃ old.graph I ∧ ZeroFrom mem₃ ht :=
      ⟨rfl,hFixed',hStage,hHalf,hi'.rows,hZero₃⟩
    let preArgs := targetOffsetPacket old F I 0 qp f ht limit radius++[targetSearchRounds radius,I.n,J.m,dest,V]
    let finishSpec : Contract := {
      pre := fun as mem' => as=preArgs ∧ mem'=mem₃
      post := fun _ _ out final => J.Optimal (fun e => (J.readSolverFlow final dest e:ℝ)) ∧
        ht≤out ∧ out≤ht+S+Q ∧ ZeroFrom final out ∧ ∀ a<dest,final a=mem₃ a
      cost := fun _ _ => solverQualitySearchCharge r I V hw+solverQualityRecoveryCharge r I V J.m+50 }
    have hFinishSpec : MeetsContract w p finish finishSpec := by
      apply meetsContract_of_runs hFinish
      intro xs initial position ω' _ hpre
      obtain ⟨hArgs,hInitial⟩ := hpre
      change xs=preArgs at hArgs
      change initial=mem₃ at hInitial
      subst xs initial
      obtain ⟨out,final,c,hRun,hOpt,hLow,hHigh,hZ,hF,hC⟩ :=
        solverQualityFinishWithV_runs r entries C D hD RC RD J hm hp hc hu hw hDS hSearch hRecover old qp f ht dest
          mem₃ position ω' hReady hN hV hRadius hLimit hCap (by dsimp only [ht,ra,wa]; omega) hSpace
      exact ⟨.returned out,final,c,hRun,⟨hOpt,hLow,hHigh,hZ,hF⟩,hC⟩
    let c := solverCoefficientBase I h
    let s := solverGuardBase I L h
    have hcDef : c=h+2+I.n+3*M := rfl
    have hsDef : s=c+9*(M*L)+L := by change c+(9*M+1)*L=_; ring
    have hsa : s+5*L=wa := by
      unfold s wa solverGuardBase solverSearchSetupSpace solverCoefficientBase
      omega
    have hcW : c<2^w := by omega
    have hlM : M*L<2^w := by omega
    have h3M : 3*M<2^w := by omega
    have hH2 : h+2<2^w := by omega
    have hH2N : h+2+I.n<2^w := by omega
    have h9ML : 9*(M*L)<2^w := by omega
    have hc9ML : c+9*(M*L)<2^w := by omega
    have hsW : s<2^w := by omega
    have hCExpr : h+2+I.n+3*M<2^w := hcDef ▸ hcW
    refine runs_seq_assign_le (v:=c) (by
      exact Expr.eval_add (Expr.eval_add (Expr.eval_add rfl (Expr.eval_const hTwo) hH2) rfl hH2N)
        (Expr.eval_mul (Expr.eval_const (show 3<2^w by omega)) rfl h3M) hCExpr) ?_
    refine runs_seq_assign_le (v:=M*L) (Expr.eval_mul rfl rfl hlM) ?_
    refine runs_seq_assign_le (v:=s) (by
      exact (congrArg some hsDef.symm) ▸ Expr.eval_add
        (Expr.eval_add rfl (Expr.eval_mul (Expr.eval_const (show 9<2^w by omega)) rfl h9ML) hc9ML)
        rfl (hsDef ▸ hsW)) ?_
    refine runs_seq_call_le hFinishSpec (vs:=preArgs)
      (solverStartSearchArgsWithV_eval I F L E g b f h ht dest J.m limit radius wa ra V _ (by
        exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩)
        rfl (hWorkAt' 0 (by change 0<2; decide)) (hWorkAt' 1 (by change 1<2; decide))
        (hLimitAt 0 (by change 0<3; decide)) (hLimitAt 1 (by change 1<3; decide)) (hLimitAt 2 (by change 2<3; decide))
        (by dsimp only [ht,ra] at hhT ⊢; exact max_lt (by omega) (by omega)) hhT (by omega)
        (by rw [hsa]; dsimp only [ht,ra]; omega) (by omega)) ?_ ⟨rfl,rfl⟩ ?_
    · have hPacket := solverTargetPacket_words I V k E B F old qp f ht mem₃ _ _ hFixed'
        (by have hh := hi'.flowEnd; change f+M*L≤ht at hh; omega)
        hMw rfl hEw hRadius hLimit (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSpace)
      have hRounds : targetSearchRounds radius<2^w := ((Nat.size_le).mpr hRadius).trans_lt Nat.lt_two_pow_self
      intro x hx
      simp only [preArgs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hIn | rfl | rfl | rfl | rfl | rfl
      · exact hPacket _ hIn
      · exact hRounds
      · exact hN
      · exact hJw
      · omega
      · exact hVw
    intro out final finalPos hOut
    obtain ⟨hOpt,hOutLo,hOutHi,hZ,hF⟩ := hOut
    change ht≤out at hOutLo
    change out≤ht+S+Q at hOutHi
    have hiW : out<2^w := hOutHi.trans_lt hSpace
    have hh : h≤ht := by dsimp only [ht,ra,wa]; omega
    refine runs_ret_le (v:=out) rfl ?_ ?_
    · exact ⟨hOpt,hh.trans hOutLo,hOutHi,hZ,
        fun a ha => (hF a ha).trans (hFrame a (ha.trans_le (by omega))),out,rfl⟩
    · simp only [solverQualityAfterInitCharge,solverQualitySearchSetupContract,workspaceContract,solverLimitsContract,heapContract,
        finishSpec,argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_const,Expr.size_bin,Expr.size_load,
        List.getD_cons_succ,List.getD_cons_zero]
      have hc : argsSize solverStartSearchArgsWithV≤100 := by decide
      dsimp only [V,I,M,E,P,L,radius]
      omega
  obtain ⟨o,st,c,hr,hCert,hcst⟩ := hRun
  obtain ⟨hOpt,hLo,hHi,hZ,hF,x,rfl⟩ := hCert
  exact ⟨x,st,c,hr,hOpt,hLo,hHi.trans_eq hS₀.symm,hZ,hF,hcst⟩

end MinCostFlow.IPM.Machine