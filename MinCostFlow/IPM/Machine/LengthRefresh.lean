module

public import MinCostFlow.Num.IPM.LengthArray
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# A fixed allocation endpoint for a numerical length refresh

The numerical length routine returns a pointer bounded by its workspace.
The IPM driver instead reserves that complete workspace. This wrapper
calls the routine and returns the reserved endpoint, preserving the
length array and a zero suffix for the following gradient call.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[lower,flow,upper,alpha,one,m,L,P,E,allocation,heap]`.
The allocation is the size computed by the workspace program. -/
def lengthRefreshBody (length : ℕ) : Stmt :=
  .call 11 length [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 10] ;;
  .ret (.bin .add (.reg 10) (.reg 9))

/-- A fixed-endpoint entry followed by the numerical length module. -/
def lengthRefreshModule (b h : ℕ) : List Stmt :=
  [lengthRefreshBody (b+1)] ++ Num.IPM.lengthArrayModule (b+1) h

/-- The numerical approximation contract with an exact reserved endpoint.
All numerical input premises are those of the imported length procedure. -/
def lengthRefreshContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ lo fp up ap one m L P E allocation heap,
      args=[lo,fp,up,ap,one,m,L,P,E,allocation,heap] ∧
      allocation=Num.IPM.lengthArraySpace m L P E ∧
      (Num.IPM.lengthArrayContract w h q).pre [lo,fp,up,ap,one,m,L,P,E,heap] mem)
    (fun args mem mem' => ∀ i < args.getD 5 0,
      Num.Valid mem' (heapArg args+i*args.getD 6 0) h (args.getD 6 0) ∧
      ScalarApprox (1+1/(2:ℝ)^q)
        (Num.fixVal mem' (heapArg args+i*args.getD 6 0) h (args.getD 6 0) (args.getD 7 0))
        (Num.IPM.arrayLength mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)
          (args.getD 3 0) h (args.getD 6 0) (args.getD 7 0) i))
    (fun args _ => Num.IPM.lengthArrayCost (args.getD 5 0) (args.getD 6 0)
      (args.getD 7 0) (args.getD 8 0)+100)
    (fun args _ => args.getD 9 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+args.getD 9 0}

/-- Length refresh contains no random instruction. -/
theorem lengthRefreshModule_noRand (b h : ℕ) :
    ∀ body ∈ lengthRefreshModule b h,body.NoRand := by
  intro body hb
  simp only [lengthRefreshModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [lengthRefreshBody,Stmt.NoRand]
  · exact Num.IPM.lengthArrayModule_noRand _ _ _ hb

/-- The complete numerical workspace is reserved, with its exact endpoint
and the imported coordinatewise length approximation. -/
theorem lengthRefresh_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3*h+2 ≤ w) (hp : p.HasAt b (lengthRefreshModule b h)) :
    MeetsContract w p b (lengthRefreshContract w h q) := by
  have hplace := Num.hasAt_append_right hp
  change p.HasAt (b+1) (Num.IPM.lengthArrayModule (b+1) h) at hplace
  have hlength := Num.IPM.lengthArray_meetsContract (q:=q) hh hw hplace
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨lo,fp,up,ap,one,m,L,P,E,allocation,heap,rfl,rfl,hnpre⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+Num.IPM.lengthArraySpace m L P E < 2^w at hspace
  apply runs_start_le
  unfold lengthRefreshBody
  refine runs_seq_call_le hlength (vs:=[lo,fp,up,ap,one,m,L,P,E,heap])
    (by eval_expr) ?_ hnpre ?_
  · intro x hx
    have hx' : x ∈ [lo,fp,up,ap,one,m,L,P,E,Num.IPM.lengthArraySpace m L P E,heap] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      tauto
    exact hwords x hx'
  · intro v mem1 pos1 hp1
    obtain ⟨⟨hlo,hhi,hframe,hfresh,_⟩,hvalues⟩ := hp1
    change heap ≤ v at hlo
    change v ≤ heap+Num.IPM.lengthArraySpace m L P E at hhi
    change ∀ x < heap,mem1 x=mem x at hframe
    refine runs_ret_le (v:=heap+Num.IPM.lengthArraySpace m L P E) (by eval_expr) ?_ ?_
    · change (heap ≤ heap+Num.IPM.lengthArraySpace m L P E ∧
        heap+Num.IPM.lengthArraySpace m L P E ≤ heap+Num.IPM.lengthArraySpace m L P E ∧
        (∀ x < heap,mem1 x=mem x) ∧ ZeroFrom mem1 (heap+Num.IPM.lengthArraySpace m L P E) ∧ _) ∧ _
      exact ⟨⟨by omega,le_rfl,hframe,hfresh.mono hhi,hvalues⟩,rfl⟩
    · simp only [lengthRefreshContract,Num.IPM.lengthArrayContract,heapContract,
        List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,argsSize_cons,argsSize_nil]
      omega

end MinCostFlow.IPM.Machine
