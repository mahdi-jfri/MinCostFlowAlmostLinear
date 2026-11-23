module

public import MinCostFlow.Scaling.CapacityRoutingLabelsContract
public import MinCostFlow.Scaling.ResidualProgram

/-!
# The measured dual-extraction machine interface

Construct the given primal flow's residual graph and compute its source
routing labels with the full capacity model. Those labels are exactly the
measured dual-extraction value used in cost scaling. The original heap
holds one pointer to the output signed table.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,capacityBound,heap]`. -/
def capacityExtractDualBody (residual labels : ℕ) : Stmt :=
  .call 4 residual [.reg 0,.reg 1,.reg 3] ;;
  .call 5 labels [.reg 3,.reg 2,.reg 4] ;;
  .assign 6 (.load (.reg 4)) ;;
  .store (.reg 3) (.reg 6) ;;
  .ret (.reg 5)

/-- Primal residual construction followed by capacity-backed routed labels. -/
def capacityExtractDualModule (solver : Program) (entry b : ℕ) : List Stmt :=
  capacityExtractDualBody (b+1) (b+7) ::
    (residualModule (b+1) ++ capacityRoutingLabelsModule solver entry (b+7))

/-- Residual storage followed by the exact capacity-backed label reserve. -/
def capacityExtractDualSpace (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) : ℕ :=
  2+10*J.m+capacityRoutingLabelsSpace (J.residual flow) C U

/-- Exact measured dual-extraction value through a fitting output pointer,
with the source graph and primal array below the fresh heap. -/
noncomputable def capacityExtractDualContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) : Contract :=
  let R := J.residual flow
  { pre := fun args mem => ∃ a fp heap,args=[a,fp,U,heap] ∧ ListAt mem a J.solverWords ∧
      ListAt mem fp (List.ofFn (fun e => (flow e).toNat)) ∧ a+J.solverWords.length≤heap ∧ fp+J.m≤heap ∧
      (∀ e,0≤flow e ∧ flow e≤J.capacity e) ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ (R.m+R.n+1)*C<2^w ∧ ZeroFrom mem heap ∧
      heap+capacityExtractDualSpace J flow C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+capacityExtractDualSpace J flow C U ∧
      (∀ x<heapArg args,mem' x=mem x) ∧ ZeroFrom mem' ret ∧
      ∃ ptr,heapArg args<ptr ∧ ptr<2^w ∧ ptr+2*J.n≤ret ∧ mem' (heapArg args)=ptr ∧
        SignedTableAt mem' ptr
          (J.extractDualMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) flow).value
    cost := fun _ _ => (capacityRoutingLabelsContract w solver entry T hproc R C U).cost [] (fun _ => 0)+
      600*J.m+400 }

/-- Residual construction and all nested model calls use no random instruction. -/
theorem capacityExtractDualModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityExtractDualModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityExtractDualBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hr | hl
    · exact residualModule_noRand _ body hr
    · exact capacityRoutingLabelsModule_noRand solver entry _ hdet body hl

end MinCostFlow.Scaling.Machine
