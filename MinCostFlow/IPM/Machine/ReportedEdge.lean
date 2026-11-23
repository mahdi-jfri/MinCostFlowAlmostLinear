module

public import MinCostFlow.IPM.Machine.QueryCoefficientInput
public import MinCostFlow.IPM.Machine.CoefficientStatus

/-!
# One reported-edge operation in a target test

Query the accumulated flow and guard the recovered coordinate first.
Reject immediately if it is outside its capacities. Otherwise check the
slacks, evaluate the two coefficients and write their table entries.
Both branches return a status bit in the last allocated word. The source
prefix is separate from the DS footprint and the coefficient entries.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The guarded continuation after Query recovery, with its result in
register 19. A failed capacity check returns status zero immediately. -/
def reportedEdgeTail (coefficient flag : ℕ) : Stmt :=
  .assign 20 (.load (.bin .sub (.reg 19)
    (.bin .add (.const 1) (.bin .mul (.const 4) (.reg 6))))) ;;
  .cond (.reg 20)
    (.call 21 coefficient [.reg 18,.reg 8,.reg 9,.reg 3,.reg 5,.reg 4,.reg 10,.reg 11,
      .reg 12,.reg 13,.reg 6,.reg 14,.reg 15,.reg 16,.reg 17,.reg 19] ;;
      .ret (.reg 21))
    (.call 21 flag [.const 0,.reg 19] ;;
      .ret (.reg 21))

/-- Arguments `[handle,edge,base,lower,upper,flow,L,heap,cost,residual,alpha,one,min,max,P,E,lengthDestination,gradientDestination,m]`. -/
def reportedEdgeBody (query coefficient flag : ℕ) : Stmt :=
  .call 19 query [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7] ;;
  reportedEdgeTail coefficient flag

/-- The reported-edge entry has no random statement. Its three linked
procedures are the verified Query recovery, coefficient guard and flag writer. -/
theorem reportedEdgeBody_noRand (query coefficient flag : ℕ) :
    (reportedEdgeBody query coefficient flag).NoRand := by
  simp [reportedEdgeBody,reportedEdgeTail,Stmt.NoRand]

/-- The exact candidate slacks are strictly inside the selected range. -/
def ReportedCandidateSafe {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (s : A.State) (mem : ℕ → ℕ)
    (e base lo up E : ℕ) : Prop :=
  let value := Num.fixVal mem base F.fmt.limbBits F.limbs F.fmt.precision+A.query s e
  let upper := Num.fixVal mem up F.fmt.limbBits F.limbs F.fmt.precision-value
  let lower := value-Num.fixVal mem lo F.fmt.limbBits F.limbs F.fmt.precision
  (1/(2:ℝ)^E<upper ∧ upper<(2:ℝ)^E) ∧ (1/(2:ℝ)^E<lower ∧ lower<(2:ℝ)^E)

/-- Input arithmetic and separation conditions for a reported edge.
The capacity guard precedes all powers. The source conditions do not
assume a positive minimum slack, and the DS representation is retained
with its exact footprint for subsequent operations. -/
def reportedEdgeContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (q K sourceEnd : ℕ) : Contract :=
  let D := minRatioMachineContract F A G m κ α rate allocation
  { pre := fun args mem => ∃ e base lo up f c r a one mn mx E ld gd heap,
      args=[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] ∧
      (queryCoordinateContract F A G m κ α rate allocation R b s x).pre
        [b,e,base,lo,up,f,F.limbs,heap] mem ∧
      scalarCoefficientSourceConditions w F.fmt.limbBits q K m c r lo f up a one mn mx
        F.limbs F.fmt.precision E sourceEnd mem ∧
      sourceEnd≤heap ∧ mn+F.limbs≤sourceEnd ∧ mx+F.limbs≤sourceEnd ∧ base+F.limbs≤sourceEnd ∧
      (∀ z<sourceEnd,¬ R.foot b x z) ∧
      (∀ p∈[c,r,lo,up,a,one,mn,mx],p+F.limbs≤f ∨ f+F.limbs≤p) ∧
      Num.fixVal mem up F.fmt.limbBits F.limbs F.fmt.precision-
        Num.fixVal mem lo F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E ∧
      ld+F.limbs≤heap ∧ gd+F.limbs≤heap ∧ (ld+F.limbs≤gd ∨ gd+F.limbs≤ld) ∧
      sourceEnd≤ld ∧ sourceEnd≤gd ∧
      (∀ z,R.foot b x z → (z<ld ∨ ld+F.limbs≤z) ∧ (z<gd ∨ gd+F.limbs≤z)) ∧
      heap+D.space 1 s [b,e,heap] mem+16*F.limbs+
        Num.IPM.lengthSpace F.limbs F.fmt.precision E+
        Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w
    post := fun args mem v mem' => ∃ queryEnd queryMem x',
      (queryCoordinateContract F A G m κ α rate allocation R b s x).post
        [b,args.getD 1 0,args.getD 2 0,args.getD 3 0,args.getD 4 0,args.getD 5 0,F.limbs,args.getD 7 0]
        mem queryEnd queryMem ∧ R.rep b s x' queryMem ∧
      (if queryMem (queryEnd-(1+4*F.limbs))=1 then
        (coefficientStatusContract w F.fmt.limbBits q K).post
          [m,args.getD 8 0,args.getD 9 0,args.getD 3 0,args.getD 5 0,args.getD 4 0,
            args.getD 10 0,args.getD 11 0,args.getD 12 0,args.getD 13 0,F.limbs,F.fmt.precision,
            args.getD 15 0,args.getD 16 0,args.getD 17 0,queryEnd] queryMem v mem'
      else (flagRecordContract w).post [0,queryEnd] queryMem v mem') ∧
      R.rep b s x' mem' ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ args.getD 7 0≤z))
    cost := fun args mem => D.cost 1 s [b,args.getD 1 0,args.getD 7 0] mem+R.phi b x mem+
      Num.IPM.lengthCost F.limbs F.fmt.precision (args.getD 15 0)+
      Num.IPM.gradientCost F.limbs F.fmt.precision (args.getD 15 0)+1534*F.limbs+3500 }

end MinCostFlow.IPM.Machine
