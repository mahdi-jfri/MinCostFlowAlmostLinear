module

public import MinCostFlow.Num.IPM.GradientArray
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# A fixed allocation endpoint for a numerical gradient refresh

The numerical gradient routine returns a pointer bounded by its workspace.
The IPM driver instead reserves that complete workspace. This wrapper
calls the routine and returns the reserved endpoint, preserving the
gradient array and a zero suffix for the following data-structure call.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,L,P,E,allocation,heap]`.
The allocation is the size computed by the workspace program. -/
def gradientRefreshBody (gradient : ℕ) : Stmt :=
  .call 13 gradient [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 12] ;;
  .ret (.bin .add (.reg 12) (.reg 11))

/-- A fixed-endpoint entry followed by the numerical gradient module. -/
def gradientRefreshModule (b h : ℕ) : List Stmt :=
  [gradientRefreshBody (b+1)] ++ Num.IPM.gradientArrayModule (b+1) h

/-- The numerical approximation contract with an exact reserved endpoint.
All numerical input premises are those of the imported gradient procedure. -/
def gradientRefreshContract (w h q K : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ m cp rp lo fp up ap one L P E allocation heap,
      args=[m,cp,rp,lo,fp,up,ap,one,L,P,E,allocation,heap] ∧
      allocation=Num.IPM.gradientArraySpace m L P E ∧
      (Num.IPM.gradientArrayContract w h q K).pre [m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem)
    (fun args mem mem' => ∀ i < args.getD 0 0,
      Num.Valid mem' (heapArg args+i*args.getD 8 0) h (args.getD 8 0) ∧
      |Num.fixVal mem' (heapArg args+i*args.getD 8 0) h (args.getD 8 0) (args.getD 9 0)-
        Num.IPM.arrayGradient mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)
          (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
          h (args.getD 8 0) (args.getD 9 0) i| ≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem (args.getD 3 0) (args.getD 4 0)
          (args.getD 5 0) (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0) i)
    (fun args _ => Num.IPM.gradientArrayCost (args.getD 0 0) (args.getD 8 0)
      (args.getD 9 0) (args.getD 10 0)+120)
    (fun args _ => args.getD 11 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+args.getD 11 0}

/-- Gradient refresh contains no random instruction. -/
theorem gradientRefreshModule_noRand (b h : ℕ) :
    ∀ body ∈ gradientRefreshModule b h,body.NoRand := by
  intro body hb
  simp only [gradientRefreshModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [gradientRefreshBody,Stmt.NoRand]
  · exact Num.IPM.gradientArrayModule_noRand _ _ _ hb

/-- The complete numerical workspace is reserved, with its exact endpoint
and the imported coordinatewise gradient approximation. -/
theorem gradientRefresh_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3*h+2 ≤ w) (hp : p.HasAt b (gradientRefreshModule b h)) :
    MeetsContract w p b (gradientRefreshContract w h q K) := by
  have hplace := Num.hasAt_append_right hp
  change p.HasAt (b+1) (Num.IPM.gradientArrayModule (b+1) h) at hplace
  have hgradient := Num.IPM.gradientArray_meetsContract (q:=q) (K:=K) hh hw hplace
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,cp,rp,lo,fp,up,ap,one,L,P,E,allocation,heap,rfl,rfl,hnpre⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+Num.IPM.gradientArraySpace m L P E < 2^w at hspace
  apply runs_start_le
  unfold gradientRefreshBody
  refine runs_seq_call_le hgradient (vs:=[m,cp,rp,lo,fp,up,ap,one,L,P,E,heap])
    (by eval_expr) ?_ hnpre ?_
  · intro x hx
    have hx' : x ∈ [m,cp,rp,lo,fp,up,ap,one,L,P,E,Num.IPM.gradientArraySpace m L P E,heap] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      tauto
    exact hwords x hx'
  · intro v mem1 pos1 hp1
    obtain ⟨⟨hlo,hhi,hframe,hfresh,_⟩,hvalues⟩ := hp1
    change heap ≤ v at hlo
    change v ≤ heap+Num.IPM.gradientArraySpace m L P E at hhi
    change ∀ x < heap,mem1 x=mem x at hframe
    refine runs_ret_le (v:=heap+Num.IPM.gradientArraySpace m L P E) (by eval_expr) ?_ ?_
    · change (heap ≤ heap+Num.IPM.gradientArraySpace m L P E ∧
        heap+Num.IPM.gradientArraySpace m L P E ≤ heap+Num.IPM.gradientArraySpace m L P E ∧
        (∀ x < heap,mem1 x=mem x) ∧ ZeroFrom mem1 (heap+Num.IPM.gradientArraySpace m L P E) ∧ _) ∧ _
      exact ⟨⟨by omega,le_rfl,hframe,hfresh.mono hhi,hvalues⟩,rfl⟩
    · simp only [gradientRefreshContract,Num.IPM.gradientArrayContract,heapContract,
        List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,argsSize_cons,argsSize_nil]
      omega

end MinCostFlow.IPM.Machine
