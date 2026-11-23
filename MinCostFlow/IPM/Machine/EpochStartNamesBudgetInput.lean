module

public import MinCostFlow.IPM.Machine.EpochStartNamesBudget
public import MinCostFlow.IPM.Machine.ReportedEdgesContract
public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.EpochInitialFlow
import MinCostFlow.IPM.Machine.GuardedRefreshSourceFrame
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Constructing the first complete refresh input of an epoch

The actual startup places full edge names after the initialized DS and
ends with a fresh budget record. Its source frame preserves all numeric
input conditions. The initialized state has positive computed lengths,
so the original specification makes its first Detect empty. Assemble
the complete first refresh precondition from these concrete outputs.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual startup layout and cache under `P` establish the first full
Detect/refresh input. The finite loop supplies its allocation budget. -/
theorem epochStartNamesBudget_refresh_pre_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w q K : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (heps : 0<eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one mn mx E heap b initEnd v base : ℕ}
    {s : A.State} {x : R.τ} {mem named final : ℕ → ℕ}
    (hb : b=heap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E))
    (hinitEnd : b ≤ initEnd)
    (hnames : ListAt final initEnd (List.range I.m))
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named v final)
    (hframe : ∀ z<heap,final z=mem z)
    (hrep : R.rep b s x final)
    (hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s)
    (hstate : s=A.init (namedInstance I)
      (readVector final (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E)
        F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hfoot : ∀ z,R.foot b x z → b≤z ∧ z < initEnd)
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q base lo up fp cp rp ap heap
      (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E) e final)
    (harrays : ∀ p∈[base,cp,lo,up],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,ap,one,mn,mx],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hfamily : ∀ e<I.m,scalarCoefficientSourceConditions w F.fmt.limbBits q K I.m
      (cp+e*F.limbs) rp (lo+e*F.limbs) (fp+e*F.limbs) (up+e*F.limbs)
      ap one mn mx F.limbs F.fmt.precision E heap mem)
    (hbaseValid : ∀ e<I.m,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs)
    (hwidth : ∀ e<I.m,Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w)
    (hP : P (namedInstance I) (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) :
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K heap b).pre
      [b,initEnd,I.m,base,lo,up,fp,F.limbs,v,cp,rp,ap,one,mn,mx,F.fmt.precision,E,heap,
        heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,I.m] final := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hb' : b=heap+(la+ga) := hb
  have hv : v=initEnd+I.m+3 := hrecord.2
  have hzero := hrecord.1.2.2.2.1
  have hOne : 1<2^w := by omega
  have hlength : ∀ e∈(namedInstance I).E,0<readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m e := by
    intro e he
    have heM : e<I.m := Finset.mem_range.mp he
    simpa only [readVector,heM,ite_true] using (hcache e heM).2.2.2.1.1
  have hsubset : (A.detect s).1⊆(namedInstance I).E := by
    have hempty : (A.detect s).1=∅ := by
      rw [hstate]
      have hNamed : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps (namedInstance I).m (namedInstance I).n := by
        rw [namedInstance_m, show (namedInstance I).n = I.n from Finset.card_range I.n]
        exact hA
      exact minRatio_init_detect_empty_upTo_on A κ α Ψ eps heps (namedInstance I) hNamed
        _ _ hP (namedInstance_valid I hI) hlength
    rw [hempty]
    exact Finset.empty_subset _
  have hcover : ∀ e∈(namedInstance I).E,∃ i<I.m,final (initEnd+i)=e := by
    intro e he
    have heM : e<I.m := Finset.mem_range.mp he
    refine ⟨e,heM,?_⟩
    rw [hnames e (by simpa only [List.length_range] using heM),List.getElem_range (by simpa only [List.length_range] using heM)]
  have hentryEnd (p e : ℕ) (hp : p∈[base,cp,lo,up]) (he : e<I.m) : p+e*F.limbs+F.limbs≤heap :=
    (reported_entry_end p F.limbs e I.m he).trans ((harrays p hp).trans (by omega))
  have hfamilyFinal : ∀ e<I.m,scalarCoefficientSourceConditions w F.fmt.limbBits q K I.m
      (cp+e*F.limbs) rp (lo+e*F.limbs) (fp+e*F.limbs) (up+e*F.limbs)
      ap one mn mx F.limbs F.fmt.precision E heap final := by
    intro e he
    exact scalarCoefficientSourceConditions_frozen (hfamily e he) hframe le_rfl
      ((hscalars mn (by simp)).trans (by omega)) ((hscalars mx (by simp)).trans (by omega))
  have hbaseFinal : ∀ e<I.m,Num.Valid final (base+e*F.limbs) F.fmt.limbBits F.limbs := by
    intro e he
    exact Num.IPM.valid_frozen hframe (hentryEnd base e (by simp) he) (hbaseValid e he)
  have hwidthFinal : ∀ e<I.m,Num.fixVal final (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal final (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E := by
    intro e he
    rw [Num.IPM.fixVal_frozen hframe (hentryEnd up e (by simp) he),
      Num.IPM.fixVal_frozen hframe (hentryEnd lo e (by simp) he)]
    exact hwidth e he
  refine ⟨initEnd,base,lo,up,fp,v,cp,rp,ap,one,mn,mx,E,heap,heap+la,rfl,?_,hcover,hsubset,hspace⟩
  refine ⟨initEnd,I.m,base,lo,up,fp,v,cp,rp,ap,one,mn,mx,E,heap,heap+la,List.range I.m,rfl,
    List.length_range,List.nodup_range,hnames,?_,hfit,hrep,?_,?_,?_,?_,hinitEnd,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hzero,hOne,?_⟩
  · intro e he
    have heM := List.mem_range.mp he
    exact ⟨Finset.mem_range.mpr heM,heM⟩
  · intro z hz
    exact (hfoot z hz).2.trans_le (by omega)
  · intro z hz hbad
    have hh := (hfoot z hbad).1
    omega
  · intro i hi hbad
    have hh := (hfoot (initEnd+i) hbad).2
    omega
  · omega
  · omega
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp
    all_goals subst p
    · exact (harrays base (by simp)).trans (by omega)
    · exact (harrays cp (by simp)).trans (by omega)
    · exact (harrays lo (by simp)).trans (by omega)
    · exact hfEnd
    · exact (harrays up (by simp)).trans (by omega)
  · intro p hp
    exact (hscalars p hp).trans (by omega)
  · intro p hp
    exact Or.inl (harrays p hp)
  · intro p hp
    exact Or.inl (hscalars p hp)
  · omega
  · omega
  · omega
  · omega
  · exact Or.inl (by omega)
  · intro e he
    exact hfamilyFinal e (List.mem_range.mp he)
  · intro e he
    exact hbaseFinal e (List.mem_range.mp he)
  · intro e he
    exact hwidthFinal e (List.mem_range.mp he)
  · omega

/-- The actual startup layout and cache establish the first full
Detect/refresh input. The finite loop supplies its allocation budget. -/
theorem epochStartNamesBudget_refresh_pre_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (heps : 0<eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one mn mx E heap b initEnd v base : ℕ}
    {s : A.State} {x : R.τ} {mem named final : ℕ → ℕ}
    (hb : b=heap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E))
    (hinitEnd : b ≤ initEnd)
    (hnames : ListAt final initEnd (List.range I.m))
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named v final)
    (hframe : ∀ z<heap,final z=mem z)
    (hrep : R.rep b s x final)
    (hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s)
    (hstate : s=A.init (namedInstance I)
      (readVector final (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E)
        F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hfoot : ∀ z,R.foot b x z → b≤z ∧ z < initEnd)
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q base lo up fp cp rp ap heap
      (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E) e final)
    (harrays : ∀ p∈[base,cp,lo,up],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,ap,one,mn,mx],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hfamily : ∀ e<I.m,scalarCoefficientSourceConditions w F.fmt.limbBits q K I.m
      (cp+e*F.limbs) rp (lo+e*F.limbs) (fp+e*F.limbs) (up+e*F.limbs)
      ap one mn mx F.limbs F.fmt.precision E heap mem)
    (hbaseValid : ∀ e<I.m,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs)
    (hwidth : ∀ e<I.m,Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w) :
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K heap b).pre
      [b,initEnd,I.m,base,lo,up,fp,F.limbs,v,cp,rp,ap,one,mn,mx,F.fmt.precision,E,heap,
        heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,I.m] final :=
  epochStartNamesBudget_refresh_pre_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    heps hI rate allocation R hb hinitEnd hnames hrecord hframe hrep hfit hstate hfoot
    hcache harrays hscalars hfEnd hfamily hbaseValid hwidth hspace trivial


/-- The actual startup layout and cache establish the first full
Detect/refresh input. The finite loop supplies its allocation budget. -/
theorem epochStartNamesBudget_refresh_pre {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (heps : 0<eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {cp rp lo fp up ap one mn mx E heap b initEnd v base : ℕ}
    {s : A.State} {x : R.τ} {mem named final : ℕ → ℕ}
    (hb : b=heap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E))
    (hinitEnd : b ≤ initEnd)
    (hnames : ListAt final initEnd (List.range I.m))
    (hrecord : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named v final)
    (hframe : ∀ z<heap,final z=mem z)
    (hrep : R.rep b s x final)
    (hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s)
    (hstate : s=A.init (namedInstance I)
      (readVector final (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E)
        F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector final heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hfoot : ∀ z,R.foot b x z → b≤z ∧ z < initEnd)
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q base lo up fp cp rp ap heap
      (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E) e final)
    (harrays : ∀ p∈[base,cp,lo,up],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,ap,one,mn,mx],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hfamily : ∀ e<I.m,scalarCoefficientSourceConditions w F.fmt.limbBits q K I.m
      (cp+e*F.limbs) rp (lo+e*F.limbs) (fp+e*F.limbs) (up+e*F.limbs)
      ap one mn mx F.limbs F.fmt.precision E heap mem)
    (hbaseValid : ∀ e<I.m,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs)
    (hwidth : ∀ e<I.m,Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w) :
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K heap b).pre
      [b,initEnd,I.m,base,lo,up,fp,F.limbs,v,cp,rp,ap,one,mn,mx,F.fmt.precision,E,heap,
        heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,I.m] final :=
  epochStartNamesBudget_refresh_pre_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) heps hI rate
    allocation R hb hinitEnd hnames hrecord hframe hrep hfit hstate hfoot hcache harrays
    hscalars hfEnd hfamily hbaseValid hwidth hspace

end MinCostFlow.IPM.Machine
