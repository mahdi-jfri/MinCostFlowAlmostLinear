module

public import MinCostFlow.IPM.Machine.ReportedEdgeInputBuilder
public import MinCostFlow.IPM.Machine.ReportedEdges
public import MinCostFlow.IPM.Machine.QueryAllocationBound

/-!
# Contract of the reported-list refresh

The caller owns dense source and coefficient tables and a stable copy
of Detect's name list. The DS footprint avoids those regions. A
successful list refresh recovers every listed flow coordinate and writes
coefficients for the final cached inputs. A failed guard stops the list.
The allocation bound reserves each Query and its numeric scratch work;
the cost bound charges Query once per name and retains amortized credit.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Extra allocation per reported name, including Query's parameter
allocation and the complete guarded numeric continuation. -/
def reportedEdgesScratch {w : ℕ} (F : MinRatioFormat w) (m b E : ℕ)
    (allocation : ℕ → List ℕ → ℕ) : ℕ :=
  queryAllocationBound w m b allocation+16*F.limbs+
    Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+4

/-- Per-name charge including one Query, numerical work and loop control. -/
def reportedEdgesCharge {w : ℕ} (F : MinRatioFormat w) (m E : ℕ) (rate : ℕ → ℕ) : ℕ :=
  rate m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
    Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3630

/-- Numerical output condition for one accepted reported name: exact
cached Query recovery, strict capacity feasibility and valid coefficients
at the final stored inputs.
This predicate is a program postcondition, not part of the DS state. -/
def reportedCachePost {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (s : A.State) (m q base lo up f c r a ld gd e : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  Num.Valid mem (f+e*F.limbs) F.fmt.limbBits F.limbs ∧
  Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
    Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+A.query s e ∧
  Num.Valid mem (ld+e*F.limbs) F.fmt.limbBits F.limbs ∧
  ScalarApprox (1+1/(2:ℝ)^q)
    (Num.fixVal mem (ld+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (Num.IPM.arrayLength mem lo f up a F.fmt.limbBits F.limbs F.fmt.precision e) ∧
  Num.Valid mem (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
  |Num.fixVal mem (gd+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
    Num.IPM.arrayGradient mem m c r lo f up a F.fmt.limbBits F.limbs F.fmt.precision e|≤
    (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a F.fmt.limbBits F.limbs F.fmt.precision e ∧
  (Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
    Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
   Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
    Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)

/-- The reported-list refresh uses the twenty arguments of
`reportedEdgesBody`. The source prefix and coefficient-table extent are
ghost layout bounds. All premises concern the input data, representation,
separation and workspace. Candidate slacks are checked by the program. -/
def reportedEdgesContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (q K sourceEnd tableEnd : ℕ) : Contract where
  pre args mem := ∃ names count base lo up f heap c r a one mn mx E ld gd, ∃ es : List ℕ,
    args=[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] ∧
    es.length=count ∧ es.Nodup ∧ ListAt mem names es ∧
    (∀ e∈es,e∈G.E ∧ e<m) ∧
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s ∧ R.rep b s x mem ∧
    (∀ z,R.foot b x z → z<heap) ∧
    (∀ z<tableEnd,¬ R.foot b x z) ∧
    (∀ i<count,¬ R.foot b x (names+i)) ∧
    sourceEnd≤tableEnd ∧ tableEnd≤names ∧ names+count≤heap ∧
    (∀ p∈[base,c,lo,f,up],p+m*F.limbs≤sourceEnd) ∧
    (∀ p∈[r,a,one,mn,mx],p+F.limbs≤sourceEnd) ∧
    (∀ p∈[base,c,lo,up],p+m*F.limbs≤f ∨ f+m*F.limbs≤p) ∧
    (∀ p∈[r,a,one,mn,mx],p+F.limbs≤f ∨ f+m*F.limbs≤p) ∧
    sourceEnd≤ld ∧ sourceEnd≤gd ∧ ld+m*F.limbs≤tableEnd ∧ gd+m*F.limbs≤tableEnd ∧
    (ld+m*F.limbs≤gd ∨ gd+m*F.limbs≤ld) ∧
    (∀ e∈es,scalarCoefficientSourceConditions w F.fmt.limbBits q K m
      (c+e*F.limbs) r (lo+e*F.limbs) (f+e*F.limbs) (up+e*F.limbs)
      a one mn mx F.limbs F.fmt.precision E sourceEnd mem) ∧
    (∀ e∈es,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs) ∧
    (∀ e∈es,Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E) ∧
    ZeroFrom mem heap ∧ 1<2^w ∧
    heap+count*reportedEdgesScratch F m b E allocation+1<2^w
  post args mem v mem' :=
    let names := args.getD 1 0
    let count := args.getD 2 0
    let base := args.getD 3 0
    let lo := args.getD 4 0
    let up := args.getD 5 0
    let f := args.getD 6 0
    let heap := args.getD 8 0
    let c := args.getD 9 0
    let r := args.getD 10 0
    let a := args.getD 11 0
    let E := args.getD 16 0
    let ld := args.getD 17 0
    let gd := args.getD 18 0
    ∃ x',R.rep b s x' mem' ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      heap≤v ∧ v≤heap+count*reportedEdgesScratch F m b E allocation+1 ∧
      ZeroFrom mem' v ∧ mem' (v-1)≤1 ∧
      (∀ es : List ℕ,ListAt mem names es → es.length=count → ∀ z<heap,¬ R.foot b x z →
        (∀ e∈es,(z<f+e*F.limbs ∨ f+e*F.limbs+F.limbs≤z) ∧
          (z<ld+e*F.limbs ∨ ld+e*F.limbs+F.limbs≤z) ∧
          (z<gd+e*F.limbs ∨ gd+e*F.limbs+F.limbs≤z)) → mem' z=mem z) ∧
      (mem' (v-1)=1 → ∀ es : List ℕ,ListAt mem names es → es.length=count → ∀ e∈es,
        reportedCachePost F A s m q base lo up f c r a ld gd e mem') ∧
      (∀ es : List ℕ,ListAt mem names es → es.length=count →
        (mem' (v-1)=1 ↔
          ∀ e∈es,ReportedCandidateSafe F A s mem e (base+e*F.limbs) (lo+e*F.limbs) (up+e*F.limbs) E))
  cost args mem := args.getD 2 0*reportedEdgesCharge F m (args.getD 16 0) rate+
    R.phi b x mem+100

end MinCostFlow.IPM.Machine
