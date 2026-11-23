module

public import MinCostFlow.IPM.Machine.DetectNames
public import MinCostFlow.IPM.Machine.ReportedEdgesContract
public import MinCostFlow.IPM.Machine.ReportStatus

/-!
# Detecting and refreshing one reported set

Algorithm 7 of [chen2022maximum], v2, page 69, detects changed edges and
refreshes their cached coordinates and coefficients before the next
Update. This entry calls the stable Detect/name preparation and the
checked list refresh, then returns the report pointer with its status.
A rejected refresh performs only that final metadata write before
returning. The caller prepares the Update batch only after success.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Read Detect's stable pointer and its count. Register 20 holds the
returned Detect/name endpoint. -/
def detectRefreshRead : Stmt :=
  .assign 21 (.load (.bin .sub (.reg 20) (.const 1))) ;;
  .assign 22 (.load (.reg 21))

/-- The actual checked-list arguments use the decoded pointer and count. -/
def detectRefreshArgs : List Expr :=
  [.reg 0,.bin .add (.reg 21) (.const 1),.reg 22,
    .reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 20,.reg 9,.reg 10,.reg 11,
    .reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19]

/-- Return the report pointer and the refresh bit. Register 23 holds the
returned checked-list endpoint; register 21 still holds the report pointer. -/
def detectRefreshRecordTail (record : ℕ) : Stmt :=
  .assign 24 (.load (.bin .sub (.reg 23) (.const 1))) ;;
  .call 25 record [.reg 21,.reg 24,.reg 23] ;;
  .ret (.reg 25)

/-- Decode Detect's report, run the checked refresh, then record its
pointer and status on both guard outcomes. -/
def detectRefreshTail (refresh record : ℕ) : Stmt :=
  detectRefreshRead ;; .call 23 refresh detectRefreshArgs ;; detectRefreshRecordTail record

/-- Arguments are the full-edge cached-table packet of
`reportedEdgesBody`, with `count=m` and `names` an explicit full-edge
list. The last two output words are the report pointer and status. -/
def detectRefreshBody (detect refresh record : ℕ) : Stmt :=
  .call 20 detect [.reg 0,.reg 19,.reg 8] ;;
  detectRefreshTail refresh record

/-- The complete Detect/refresh entry contains no randomness. -/
theorem detectRefreshBody_noRand (detect refresh record : ℕ) :
    (detectRefreshBody detect refresh record).NoRand := by
  simp [detectRefreshBody,detectRefreshTail,detectRefreshRead,detectRefreshRecordTail,Stmt.NoRand]

/-- Complete input and output protocol for one Detect/refresh stage.
Coverage is supplied by the caller's full-edge list. Report inclusion is
proved from Definition 4.5 on the actual history. Neither is an added
requirement on the parameter DS. -/
def detectRefreshContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (q K sourceEnd tableEnd : ℕ) : Contract :=
  let D := minRatioMachineContract F A G m κ α rate allocation
  let S := (A.detect s).1
  { pre := fun args mem => ∃ names base lo up f heap c r a one mn mx E ld gd,
      args=[b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] ∧
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre args mem ∧
      (∀ e∈G.E,∃ i<m,mem (names+i)=e) ∧ S⊆G.E ∧
      heap+D.space 2 s [b,heap] mem+2*(m+1)+m*reportedEdgesScratch F m b E allocation+4<2^w
    post := fun args mem v mem' => ∃ detectHeap detectMem detected refreshHeap refreshMem final,
      let pointer := detectMem (detectHeap-1)
      (detectNamesContract F A G m κ α rate allocation R b s x).post
        [b,m,args.getD 8 0] mem detectHeap detectMem ∧
      R.rep b (A.detect s).2 detected detectMem ∧
      (∀ z,R.foot b detected z → z<detectHeap ∧ (R.foot b x z ∨ args.getD 8 0≤z)) ∧
      (∀ z,R.foot b detected z → z<pointer) ∧
      (reportedEdgesContract F A G m rate allocation R b (A.detect s).2 detected q K sourceEnd tableEnd).post
        [b,pointer+1,S.card,args.getD 3 0,args.getD 4 0,args.getD 5 0,args.getD 6 0,F.limbs,
          detectHeap,args.getD 9 0,args.getD 10 0,args.getD 11 0,args.getD 12 0,args.getD 13 0,
          args.getD 14 0,F.fmt.precision,args.getD 16 0,args.getD 17 0,args.getD 18 0,m]
        detectMem refreshHeap refreshMem ∧
      (reportStatusContract w).post [pointer,refreshMem (refreshHeap-1),refreshHeap] refreshMem v mem' ∧
      R.rep b (A.detect s).2 final mem' ∧
      (∀ z,R.foot b final z → z<v ∧ (R.foot b x z ∨ args.getD 8 0≤z)) ∧
      ZeroFrom mem' v ∧ args.getD 8 0≤v ∧
      v≤args.getD 8 0+D.space 2 s [b,args.getD 8 0] mem+2*(m+1)+
        m*reportedEdgesScratch F m b (args.getD 16 0) allocation+4
    cost := fun args mem => (S.card+1)*(2*rate m+
      Num.IPM.lengthCost F.limbs F.fmt.precision (args.getD 16 0)+
      Num.IPM.gradientCost F.limbs F.fmt.precision (args.getD 16 0)+1534*F.limbs+4200)+R.phi b x mem }

end MinCostFlow.IPM.Machine
