module

public import MinCostFlow.Num.IPM.Residual
public import MinCostFlow.IPM.Machine.ResidualGuard
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Computing and testing an epoch's exact residual

After explicit flow materialization, compute the exact cost minus the
target, then inspect the stopping and numerical-range guards. Return
zero for a terminal residual, one for a valid continuing epoch, and two
for a rejected target. The residual remains at its known fresh address.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[cost,flow,m,target,L,heap,min,max,quarter]`. The result
code is the existing residual guard code, with no new allocation by the guard. -/
def epochResidualBody (residual guard : ℕ) : Stmt :=
  .call 9 residual [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5] ;;
  .call 10 guard [.bin .sub (.reg 9) (.reg 4),.reg 6,.reg 7,.reg 8,.reg 4] ;;
  .ret (.reg 10)

/-- A closed numerical module for the residual and all three guard codes. -/
def epochResidualModule (b h : ℕ) : List Stmt :=
  let guard := b+1+(Num.IPM.residualModule (b+1) h).length
  [epochResidualBody (b+1) guard] ++
    (Num.IPM.residualModule (b+1) h ++ residualGuardModule guard h)

/-- The complete numerical epoch-residual module is deterministic. -/
theorem epochResidualModule_noRand (b h : ℕ) :
    ∀ body∈epochResidualModule b h,body.NoRand := by
  intro body hb
  simp only [epochResidualModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [epochResidualBody,Stmt.NoRand]
  · exact Num.IPM.residualModule_noRand _ _ _ hb
  · exact residualGuardModule_noRand _ _ _ hb

/-- Numerical residual inputs and three valid, old-prefix guard constants.
The residual allocation includes its final scalar block. -/
def epochResidualContract (w h : ℕ) : Contract where
  pre args mem := ∃ c f m target L heap mn mx quarter,
    args=[c,f,m,target,L,heap,mn,mx,quarter] ∧ 2<2^w ∧
    (Num.IPM.residualContract w h).pre [c,f,m,target,L,heap] mem ∧
    mn+L≤heap ∧ mx+L≤heap ∧ quarter+L≤heap ∧
    Num.Valid mem mn h L ∧ Num.Valid mem mx h L ∧ Num.Valid mem quarter h L
  post args mem code mem' :=
    let c := args.getD 0 0
    let f := args.getD 1 0
    let m := args.getD 2 0
    let target := args.getD 3 0
    let L := args.getD 4 0
    let heap := args.getD 5 0
    let endpoint := heap+(8*m+4)*L
    (Num.IPM.residualContract w h).post [c,f,m,target,L,heap] mem endpoint mem' ∧
    (residualGuardContract w h).post
      [endpoint-L,args.getD 6 0,args.getD 7 0,args.getD 8 0,L] mem' code mem'
  cost args _ := args.getD 2 0*(152*(args.getD 4 0)^2+245*args.getD 4 0+400)+
    244*args.getD 4 0+650

/-- Exact residual computation and all stopping/range branches use no
random instruction in the caller. -/
theorem epochResidualBody_noRand (residual guard : ℕ) : (epochResidualBody residual guard).NoRand := by
  simp [epochResidualBody,Stmt.NoRand]

/-- The actual residual/guard entry meets the exact three-way decision
contract. Its only writes are the numerical residual workspace. -/
theorem epochResidual_meetsContract {w h residual guard entry : ℕ} {p : Program}
    (hp : p.procs[entry]?=some (epochResidualBody residual guard))
    (hresidual : MeetsContract w p residual (Num.IPM.residualContract w h))
    (hguard : MeetsContract w p guard (residualGuardContract w h)) :
    MeetsContract w p entry (epochResidualContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨c,f,m,target,L,heap,mn,mx,quarter,rfl,htwo,hRpre,hmn,hmx,hq,hvmn,hvmx,hvq⟩ := hpre
  have hRpreCopy := hRpre
  have hspace := hRpre.2.2
  change heap+(8*m+4)*L<2^w at hspace
  have hLword : L<2^w := hwords _ (by simp)
  have hmnword : mn<2^w := hwords _ (by simp)
  have hmxword : mx<2^w := hwords _ (by simp)
  have hqword : quarter<2^w := hwords _ (by simp)
  have hRwords : ∀ z∈[c,f,m,target,L,heap],z<2^w :=
    fun z hz => hwords z (List.mem_append_left [mn,mx,quarter] hz)
  apply runs_start_le
  unfold epochResidualBody
  refine runs_seq_call_le hresidual (vs:=[c,f,m,target,L,heap]) (by eval_expr) hRwords hRpreCopy ?_
  intro v mem' pos' hRpost
  have hpostCopy := hRpost
  obtain ⟨hv,_,_,hframe,hzero,hvalid,hvalue⟩ := hRpost
  change v=heap+(8*m+4)*L at hv
  change ∀ z<heap,mem' z=mem z at hframe
  change Num.Valid mem' (heap+(8*m+3)*L) h L at hvalid
  have hex : (8*m+4)*L=(8*m+3)*L+L := by
    simp only [Nat.add_mul]
    omega
  have hptr : v-L=heap+(8*m+3)*L := by rw [hv,hex]; omega
  have hvWord : v<2^w := by omega
  have hptrWord : v-L<2^w := by omega
  have hGuardPre : (residualGuardContract w h).pre [v-L,mn,mx,quarter,L] mem' := by
    refine ⟨v-L,mn,mx,quarter,L,rfl,?_,by omega,by omega,by omega,?_,
      Num.IPM.valid_frozen hframe hmn hvmn,Num.IPM.valid_frozen hframe hmx hvmx,
      Num.IPM.valid_frozen hframe hq hvq⟩
    · rw [hptr]
      omega
    · rw [hptr]
      exact hvalid
  refine runs_seq_call_le hguard (vs:=[v-L,mn,mx,quarter,L]) (by eval_expr) (by wram_words) hGuardPre ?_
  intro code finalMem finalPos hGpost
  have hmemory := hGpost.1
  change finalMem=mem' at hmemory
  have hcodeWord : code<2^w := by
    have hg := hGpost.2
    change code=(if _ then 0 else if _ then 1 else 2) at hg
    rw [hg]
    split_ifs <;> omega
  refine runs_ret_le (v:=code) (by eval_expr) ?_ ?_
  · change (Num.IPM.residualContract w h).post [c,f,m,target,L,heap]
        mem (heap+(8*m+4)*L) finalMem ∧
      (residualGuardContract w h).post [heap+(8*m+4)*L-L,mn,mx,quarter,L] finalMem code finalMem
    rw [hmemory,← hv]
    exact ⟨hpostCopy,by simpa only [hmemory] using hGpost⟩
  · simp only [epochResidualContract,Num.IPM.residualContract,heapContract,residualGuardContract,
      List.getD_cons_zero,List.getD_cons_succ,argsSize_cons,argsSize_nil,
      Expr.size_reg,Expr.size_bin]
    omega

/-- Placing the closed module discharges both numerical call contracts. -/
theorem epochResidualModule_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (htwo : 2<2^w) (hb : Num.base h<2^w)
    (hp : p.HasAt b (epochResidualModule b h)) :
    MeetsContract w p b (epochResidualContract w h) := by
  have ht := Num.hasAt_append_right hp
  exact epochResidual_meetsContract hp.head
    (Num.IPM.residual_meetsContract hh hw (Num.hasAt_append_left ht))
    (residualGuard_meetsContract hh htwo hb (Num.hasAt_append_right ht))

end MinCostFlow.IPM.Machine
