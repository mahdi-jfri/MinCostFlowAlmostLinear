module

public import MinCostFlow.IPM.Machine.GuardedRefreshInput
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Checking a reported edge before refreshing its coefficients

Run both slack-range guards first. A rejected edge returns immediately,
without evaluating powers or writing the old coefficient tables. An
accepted edge enters the verified scalar computation and table writer.
The output records the actual guard decision and, on acceptance, the
complete coefficient-refresh postcondition at the held residual.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,min,max,L,P,E,lengthDestination,gradientDestination,heap]`. -/
def guardedCoefficientRefreshBody (guard refresh : ℕ) : Stmt :=
  .call 16 guard [.reg 3,.reg 4,.reg 5,.reg 8,.reg 9,.reg 10,.reg 11,.reg 15] ;;
  .assign 17 (.load (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 10)))) ;;
  .cond (.reg 17)
    (.call 18 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
      .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 16] ;;
      .ret (.reg 18))
    (.ret (.reg 16))

/-- The exact slack checks precede the complete scalar coefficient refresh. -/
def guardedCoefficientRefreshModule (b h : ℕ) : List Stmt :=
  let r := b+1+(guardedSlacksModule (b+1) h).length
  [guardedCoefficientRefreshBody (b+1) r] ++
    (guardedSlacksModule (b+1) h ++ edgeCoefficientRefreshModule r h)

/-- The guard's actual intermediate state is retained in the postcondition.
Failure stops there; success supplies the actual coefficient computation
and table-write postcondition. The precondition assumes no slack ranges. -/
def guardedCoefficientRefreshContract (w h q K : ℕ) : Contract where
  pre args mem := (∃ m c r lo f up a one mn mx L P E ld gd heap,
    args=[m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] ∧
    scalarCoefficientSourceConditions w h q K m c r lo f up a one mn mx L P E heap mem ∧
    (guardedSlacksContract w h).pre [lo,f,up,mn,mx,L,P,heap] mem ∧
    ld+L≤heap ∧ gd+L≤heap ∧ (ld+L≤gd ∨ gd+L≤ld)) ∧
    heapArg args+(4*args.getD 10 0+1)+args.getD 10 0+
      Num.IPM.lengthSpace (args.getD 10 0) (args.getD 11 0) (args.getD 12 0)+
      Num.IPM.gradientSpace (args.getD 10 0) (args.getD 11 0) (args.getD 12 0)+1<2^w
  post args mem v mem' := ∃ guardEnd guardMem,
    (guardedSlacksContract w h).post
      [args.getD 3 0,args.getD 4 0,args.getD 5 0,args.getD 8 0,args.getD 9 0,
        args.getD 10 0,args.getD 11 0,heapArg args] mem guardEnd guardMem ∧
    mem' (heapArg args+4*args.getD 10 0)=guardMem (heapArg args+4*args.getD 10 0) ∧
    if guardMem (heapArg args+4*args.getD 10 0)=1 then
      (edgeCoefficientRefreshContract w h q K).post
        [args.getD 0 0,args.getD 1 0,args.getD 2 0,args.getD 3 0,args.getD 4 0,args.getD 5 0,
          args.getD 6 0,args.getD 7 0,args.getD 10 0,args.getD 11 0,args.getD 12 0,
          args.getD 13 0,args.getD 14 0,guardEnd] guardMem v mem'
    else v=guardEnd ∧ mem'=guardMem
  cost args _ := 400*args.getD 10 0+600+
    (Num.IPM.lengthCost (args.getD 10 0) (args.getD 11 0) (args.getD 12 0)+
      Num.IPM.gradientCost (args.getD 10 0) (args.getD 11 0) (args.getD 12 0)+34*args.getD 10 0+500)+100

/-- Both guard branches and all linked numerical calls are deterministic. -/
theorem guardedCoefficientRefreshModule_noRand (b h : ℕ) :
    ∀ body∈guardedCoefficientRefreshModule b h,body.NoRand := by
  intro body hb
  simp only [guardedCoefficientRefreshModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [guardedCoefficientRefreshBody,Stmt.NoRand]
  · exact guardedSlacksModule_noRand _ _ _ hb
  · exact edgeCoefficientRefreshModule_noRand _ _ _ hb

/-- The actual guard runs before either coefficient routine. Acceptance
supplies every missing numerical premise; rejection returns immediately.
All guards, calls, copies and branch instructions are counted. -/
theorem guardedCoefficientRefresh_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w)
    (hp : p.HasAt b (guardedCoefficientRefreshModule b h)) :
    MeetsContract w p b (guardedCoefficientRefreshContract w h q K) := by
  have ht := Num.hasAt_append_right hp
  have hg : p.HasAt (b+1) (guardedSlacksModule (b+1) h) := Num.hasAt_append_left ht
  have hr := Num.hasAt_append_right ht
  have hguard := guardedSlacks_meetsContract (w:=w) hh (by omega) hg
  have hrefresh := edgeCoefficientRefresh_meetsContract (q:=q) (K:=K) hh hw hr
  have hw4 : 4<2^w := lt_of_lt_of_le (by decide : 4<2^3)
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap,rfl,hs,hgp,hld,hgd,hdis⟩,hspace⟩ := hpre
  change heap+(4*L+1)+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1<2^w at hspace
  have hheap : heap<2^w := hwords _ (by simp)
  apply runs_start_le
  unfold guardedCoefficientRefreshBody
  refine runs_seq_call_le hguard (vs:=[lo,f,up,mn,mx,L,P,heap]) (by eval_expr) ?_ hgp ?_
  · intro x hx
    apply hwords x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    tauto
  · intro v0 mem0 pos0 hp0
    have hpostGuard := hp0
    have hv0 := hp0.2
    change v0=heap+(4*L+1) at hv0
    have hbit := hp0.1.2.2.2.2.1
    change mem0 (heap+4*L)≤1 at hbit
    have hv0w : v0<2^w := by omega
    have hslotw : heap+4*L<2^w := by omega
    wram_step
    refine runs_cond_le (v:=mem0 (heap+4*L)) (by eval_expr) ?_ ?_
    · intro hnonzero
      have haccept : mem0 (heap+4*L)=1 := by omega
      have hrpre := edgeCoefficient_pre_of_source_conditions hs hp0 haccept hld hgd hdis
        (by omega : v0+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1<2^w)
      refine runs_seq_call_le hrefresh (vs:=[m,c,r,lo,f,up,a,one,L,P,E,ld,gd,v0])
        (by eval_expr) ?_ hrpre ?_
      · intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | rfl
        all_goals first | exact hx ▸ hwords _ (by simp) | exact hv0w
      · intro v1 mem1 pos1 hp1
        have hframe := hp1.2.2.2.1
        change ∀ z<v0,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem1 z=mem0 z at hframe
        have hslot := hframe (heap+4*L) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        refine runs_ret_le (v:=v1) (by eval_expr) ?_ ?_
        · change ∃ guardEnd guardMem,
            (guardedSlacksContract w h).post [lo,f,up,mn,mx,L,P,heap] mem guardEnd guardMem ∧
            mem1 (heap+4*L)=guardMem (heap+4*L) ∧
            if guardMem (heap+4*L)=1 then
              (edgeCoefficientRefreshContract w h q K).post
                [m,c,r,lo,f,up,a,one,L,P,E,ld,gd,guardEnd] guardMem v1 mem1
            else v1=guardEnd ∧ mem1=guardMem
          refine ⟨v0,mem0,hpostGuard,hslot,?_⟩
          simp only [haccept,ite_true]
          exact hp1
        · simp only [guardedCoefficientRefreshContract,guardedSlacksContract,edgeCoefficientRefreshContract,
            heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
            Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
          omega
    · intro hzero
      refine runs_ret_le (v:=v0) (by eval_expr) ?_ ?_
      · change ∃ guardEnd guardMem,
          (guardedSlacksContract w h).post [lo,f,up,mn,mx,L,P,heap] mem guardEnd guardMem ∧
          mem0 (heap+4*L)=guardMem (heap+4*L) ∧
          if guardMem (heap+4*L)=1 then
            (edgeCoefficientRefreshContract w h q K).post
              [m,c,r,lo,f,up,a,one,L,P,E,ld,gd,guardEnd] guardMem v0 mem0
          else v0=guardEnd ∧ mem0=guardMem
        refine ⟨v0,mem0,hpostGuard,rfl,?_⟩
        simp only [hzero,zero_ne_one,ite_false]
        constructor <;> trivial
      · simp only [guardedCoefficientRefreshContract,guardedSlacksContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
          Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.IPM.Machine
