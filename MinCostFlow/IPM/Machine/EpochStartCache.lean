module

public import MinCostFlow.IPM.Machine.EpochStartOutput
public import MinCostFlow.IPM.Machine.ReportedEdgesContract
import MinCostFlow.IPM.Machine.EpochInitialFlow
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# The full cache invariant at epoch initialization

The new coefficient arrays approximate the explicit copied flow. Init
has zero implicit flow on the valid graph, so that copied flow is also
the base plus Query. Initialization preserves the old numerical source
words. Together these facts establish the complete cache condition,
including strict slacks, at the actual initialized state.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The cache facts at epoch start hold for any state whose Query is zero at the
edge. The structure `A'` enters only through its Query, so it may differ from the
one the machine runs. -/
theorem epochStart_initial_cache_of_query {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap v base e : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem v mem')
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
    reportedCachePost F A' s I.m q base lo up fp cp rp ap heap (heap+la) e mem' := by
  have hd := epochStart_output F A I κ α rate allocation R hout
  have hframe := epochStart_frame F A I κ α rate allocation R hout
  have hfix (p : ℕ) (hp : p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,up+e*F.limbs,ap]) :
      Num.fixVal mem' p F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem p F.fmt.limbBits F.limbs F.fmt.precision :=
    Num.IPM.fixVal_frozen hframe (hsources p hp)
  have hlen : Num.IPM.arrayLength mem' lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision e=
      Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision e := by
    simp only [Num.IPM.arrayLength,hfix (lo+e*F.limbs) (by simp),hfix (fp+e*F.limbs) (by simp),
      hfix (up+e*F.limbs) (by simp),hfix ap (by simp)]
  have hcost : Num.intVal mem' (cp+e*F.limbs) F.fmt.limbBits F.limbs=
      Num.intVal mem (cp+e*F.limbs) F.fmt.limbBits F.limbs :=
    Num.intVal_congr (fun i hi => hframe _ (by have hb := hsources (cp+e*F.limbs) (by simp); omega))
  have hgrad : Num.IPM.arrayGradient mem' I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision e=
      Num.IPM.arrayGradient mem I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision e := by
    simp only [Num.IPM.arrayGradient,hcost,hfix rp (by simp),hfix (lo+e*F.limbs) (by simp),
      hfix (fp+e*F.limbs) (by simp),hfix (up+e*F.limbs) (by simp),hfix ap (by simp)]
  refine ⟨Num.IPM.valid_frozen hframe (hsources (fp+e*F.limbs) (by simp)) hvalid,?_,
    (hd.1 e he).1,?_,(hd.2.1 e he).1,?_,?_⟩
  · rw [hquery,add_zero,hfix (fp+e*F.limbs) (by simp),hfix (base+e*F.limbs) (by simp)]
    exact hbase
  · rw [hlen]
    exact (hd.1 e he).2
  · rw [hgrad,hlen]
    exact (hd.2.1 e he).2
  · rw [hfix (lo+e*F.limbs) (by simp),hfix (fp+e*F.limbs) (by simp),hfix (up+e*F.limbs) (by simp)]
    exact hinside

/-- The initialized arrays and explicit copied flow satisfy every part
of the cache invariant at the actual zero-flow Init state under `P`. -/
theorem epochStart_initial_cache_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap v base e : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem v mem')
    (he : e<I.m)
    (hsources : ∀ p∈[base+e*F.limbs,cp+e*F.limbs,rp,lo+e*F.limbs,fp+e*F.limbs,up+e*F.limbs,ap],p+F.limbs≤heap)
    (hvalid : Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hP : P (namedInstance I) (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
    reportedCachePost F A (A.init (namedInstance I)
      (readVector mem' (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q base lo up fp cp rp ap heap (heap+la) e mem' := by
  have hd := epochStart_output F A I κ α rate allocation R hout
  have hlpos : ∀ j∈(namedInstance I).E,0<readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m j := by
    intro j hj
    have hjM : j<I.m := Finset.mem_range.mp hj
    simpa only [readVector,hjM,ite_true] using (hd.1 j hjM).2.1
  have hNamed : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps (namedInstance I).m (namedInstance I).n := by
    rw [namedInstance_m, show (namedInstance I).n = I.n from Finset.card_range I.n]
    exact hA
  exact epochStart_initial_cache_of_query F A I κ α rate allocation R hout he hsources hvalid hbase hinside A _
    (minRatio_init_query_zero_upTo_on A κ α Ψ eps (namedInstance I) hNamed
      (readVector mem' (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E) F.fmt.limbBits F.limbs
        F.fmt.precision I.m)
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m) hP
      (namedInstance_valid I hI) hlpos e (Finset.mem_range.mpr he))

/-- The initialized arrays and explicit copied flow satisfy every part
of the cache invariant at the actual zero-flow Init state. -/
theorem epochStart_initial_cache_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap v base e : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem v mem')
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
      (readVector mem' (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q base lo up fp cp rp ap heap (heap+la) e mem' :=
  epochStart_initial_cache_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) hI
    rate allocation R hout he hsources hvalid hbase hinside trivial


/-- The initialized arrays and explicit copied flow satisfy every part
of the cache invariant at the actual zero-flow Init state. -/
theorem epochStart_initial_cache {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one E graph heap v base e : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (epochStartContract F A I κ α rate allocation R q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem v mem')
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
      (readVector mem' (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q base lo up fp cp rp ap heap (heap+la) e mem' :=
  epochStart_initial_cache_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) hI rate allocation R hout he
    hsources hvalid hbase hinside

end MinCostFlow.IPM.Machine
