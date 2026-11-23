module

public import MinCostFlow.IPM.Machine.EpochStartCache
public import MinCostFlow.IPM.Machine.EpochBudgetRecord
public import MinCostFlow.IPM.Machine.VertexNames
import MinCostFlow.IPM.Machine.ReportedCacheCongr
import MinCostFlow.IPM.Machine.VectorFrame
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# The initial cache after names and the report budget are written

The coefficient/Init stage supplies the complete initial cache. Its
source and coefficient blocks all precede the returned initialization
endpoint. The name writer and fresh budget record preserve the cache and
both arrays used to identify the actual initialized state.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The cache facts after the startup and its name and budget records, for any
state whose Query is zero at the edge. -/
theorem epochStartNamesBudget_initial_cache_of_query {w q K : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap initEnd base e end_ : ℕ} {mem initialized named final : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem initEnd initialized)
    (hnames : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ final)
    (he : e<I.m)
    (hsources : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,up+e*F.limbs,ap],p+F.limbs≤heap)
    (hvalid : Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (A' : MinRatioDataStructureWithFailure) (s : A'.State) (hquery : A'.query s e=0) :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    reportedCachePost F A' s I.m q base lo up fp cp rp ap heap (heap+la) e final := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  obtain ⟨_,_,_,_,hlower,_,_⟩ := (epochStart_output F A I κ α rate allocation R hout).2.2
  change heap+(la+ga) ≤ initEnd at hlower
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hlEnd : heap+I.m*F.limbs ≤ initEnd := by omega
  have hgEnd : heap+la+I.m*F.limbs ≤ initEnd := by omega
  have hends : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,
      up+e*F.limbs,ap,heap+e*F.limbs,heap+la+e*F.limbs],p+F.limbs ≤ initEnd := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p
    · exact (hsources (base+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources (cp+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources rp (by simp)).trans (by omega)
    · exact (hsources (lo+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources (fp+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources (up+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources ap (by simp)).trans (by omega)
    · exact (reported_entry_end heap F.limbs e I.m he).trans hlEnd
    · exact (reported_entry_end (heap+la) F.limbs e I.m he).trans hgEnd
  have hnamesFrame := hnames.1.2.2.1
  change ∀ z < initEnd,named z=initialized z at hnamesFrame
  have hbudgetFrame := hrecord.1.2.2.1
  change ∀ z < initEnd+I.m,final z=named z at hbudgetFrame
  have hframe : ∀ z < initEnd,final z=initialized z := fun z hz =>
    (hbudgetFrame z (by omega)).trans (hnamesFrame z hz)
  have hcache := epochStart_initial_cache_of_query F A I κ α rate allocation R hout he hsources
    hvalid hbase hinside A' s hquery
  exact reportedCachePost_congr F A' _ (mem:=initialized) (mem':=final)
    (fun p hp i hi => hframe _ (by have hb := hends p hp; omega)) hcache

/-- The complete epoch-start/name/budget trace under `P` establishes the full cache
invariant at Init of the arrays in the actual final memory. -/
theorem epochStartNamesBudget_initial_cache_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w q K : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap initEnd base e end_ : ℕ} {mem initialized named final : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem initEnd initialized)
    (hnames : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ final)
    (he : e<I.m)
    (hsources : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,up+e*F.limbs,ap],p+F.limbs≤heap)
    (hvalid : Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hP : P (namedInstance I) (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    reportedCachePost F A (A.init (namedInstance I)
      (readVector final (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q base lo up fp cp rp ap heap (heap+la) e final := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  obtain ⟨_,_,_,_,hlower,_,_⟩ := (epochStart_output F A I κ α rate allocation R hout).2.2
  change heap+(la+ga) ≤ initEnd at hlower
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hlEnd : heap+I.m*F.limbs ≤ initEnd := by omega
  have hgEnd : heap+la+I.m*F.limbs ≤ initEnd := by omega
  have hends : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,
      up+e*F.limbs,ap,heap+e*F.limbs,heap+la+e*F.limbs],p+F.limbs ≤ initEnd := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p
    · exact (hsources (base+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources (cp+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources rp (by simp)).trans (by omega)
    · exact (hsources (lo+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources (fp+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources (up+e*F.limbs) (by simp)).trans (by omega)
    · exact (hsources ap (by simp)).trans (by omega)
    · exact (reported_entry_end heap F.limbs e I.m he).trans hlEnd
    · exact (reported_entry_end (heap+la) F.limbs e I.m he).trans hgEnd
  have hnamesFrame := hnames.1.2.2.1
  change ∀ z < initEnd,named z=initialized z at hnamesFrame
  have hbudgetFrame := hrecord.1.2.2.1
  change ∀ z < initEnd+I.m,final z=named z at hbudgetFrame
  have hframe : ∀ z < initEnd,final z=initialized z := fun z hz =>
    (hbudgetFrame z (by omega)).trans (hnamesFrame z hz)
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
  have hcache := epochStart_initial_cache_upTo_on F A I κ α Ψ eps hA hI rate allocation R hout he hsources
    hvalid hbase hinside (hlSame ▸ hP)
  have hfinal := reportedCachePost_congr F A _ (mem:=initialized) (mem':=final)
    (fun p hp i hi => hframe _ (by have hb := hends p hp; omega)) hcache

  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
  dsimp only
  rw [hgSame,hlSame]
  exact hfinal

/-- The complete epoch-start/name/budget trace establishes the full cache
invariant at Init of the arrays in the actual final memory. -/
theorem epochStartNamesBudget_initial_cache_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap initEnd base e end_ : ℕ} {mem initialized named final : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem initEnd initialized)
    (hnames : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ final)
    (he : e<I.m)
    (hsources : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,up+e*F.limbs,ap],p+F.limbs≤heap)
    (hvalid : Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    reportedCachePost F A (A.init (namedInstance I)
      (readVector final (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q base lo up fp cp rp ap heap (heap+la) e final :=
  epochStartNamesBudget_initial_cache_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    hI rate allocation R hout hnames hrecord he hsources hvalid hbase hinside trivial

/-- The complete epoch-start/name/budget trace establishes the full cache
invariant at Init of the arrays in the actual final memory. -/
theorem epochStartNamesBudget_initial_cache {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap initEnd base e end_ : ℕ} {mem initialized named final : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem initEnd initialized)
    (hnames : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ final)
    (he : e<I.m)
    (hsources : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,up+e*F.limbs,ap],p+F.limbs≤heap)
    (hvalid : Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    reportedCachePost F A (A.init (namedInstance I)
      (readVector final (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q base lo up fp cp rp ap heap (heap+la) e final :=
  epochStartNamesBudget_initial_cache_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) hI rate allocation
    R hout hnames hrecord he hsources hvalid hbase hinside

end MinCostFlow.IPM.Machine
