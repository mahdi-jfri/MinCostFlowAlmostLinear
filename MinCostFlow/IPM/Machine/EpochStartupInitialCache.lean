module

public import MinCostFlow.IPM.Machine.EpochStartNamesBudgetCache
public import MinCostFlow.IPM.Machine.EpochNextLayout
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Cache established before the startup scan

The two numerical arrays and the initialized DS state already agree
before the scan runs. The cache therefore describes the actual
coefficients even when the scan returns zero.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The cache facts after the full startup, for any state whose Query is zero on
every edge. -/
theorem epochStartup_initial_cache_of_query {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd : ℕ)
    (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (A' : MinRatioDataStructureWithFailure) (s : A'.State) (hquery : ∀ e<I.m,A'.query s e=0) :
    let L := old.next F I base rp fp heap initEnd
    ∀ e<I.m,reportedCachePost F A' s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started := by
  dsimp only
  intro e he
  have hentry (p : ℕ) (hp : p∈[base,old.cost,old.lower,old.upper]) :
      p+e*F.limbs+F.limbs≤heap :=
    (reported_entry_end p F.limbs e I.m he).trans ((harrays p hp).trans (by omega))
  have hrp := hscalars rp (by simp)
  have ha := hscalars old.alpha (by simp)
  have hfp := (reported_entry_end fp F.limbs e I.m he).trans hfEnd
  have hsources : ∀ p∈[base+e*F.limbs,old.cost+e*F.limbs,rp,old.lower+e*F.limbs,fp+e*F.limbs,
      old.upper+e*F.limbs,old.alpha],p+F.limbs≤heap := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | omega | exact hentry _ (by simp)
  exact epochStartNamesBudget_initial_cache_of_query F A I κ α rate allocation R hOut hN hB he
    hsources (hvalid e he) (hbase e he) (hinside e he) A' s (hquery e he)

/-- Recover the cache from the actual startup and its name and budget
records under `P`, regardless of the scan's subsequent verdict. -/
theorem epochStartup_initial_cache_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd : ℕ)
    (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hP : P (namedInstance I) (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) :
    let L := old.next F I base rp fp heap initEnd
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started := by
  dsimp only
  intro e he
  have hentry (p : ℕ) (hp : p∈[base,old.cost,old.lower,old.upper]) :
      p+e*F.limbs+F.limbs≤heap :=
    (reported_entry_end p F.limbs e I.m he).trans ((harrays p hp).trans (by omega))
  have hrp := hscalars rp (by simp)
  have ha := hscalars old.alpha (by simp)
  have hfp := (reported_entry_end fp F.limbs e I.m he).trans hfEnd
  have hsources : ∀ p∈[base+e*F.limbs,old.cost+e*F.limbs,rp,old.lower+e*F.limbs,fp+e*F.limbs,
      old.upper+e*F.limbs,old.alpha],p+F.limbs≤heap := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | omega | exact hentry _ (by simp)
  exact epochStartNamesBudget_initial_cache_upTo_on F A I κ α Ψ eps hA hI rate allocation R hOut hN hB he
    hsources (hvalid e he) (hbase e he) (hinside e he) hP

/-- Recover the cache from the actual startup and its name and budget
records, regardless of the scan's subsequent verdict. -/
theorem epochStartup_initial_cache_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd : ℕ)
    (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) :
    let L := old.next F I base rp fp heap initEnd
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started :=
  epochStartup_initial_cache_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) hI
    rate allocation R old base rp fp heap initEnd mem initialized named started hOut hN hB
    harrays hscalars hfEnd hvalid hbase hinside trivial


/-- Recover the cache from the actual startup and its name and budget
records, regardless of the scan's subsequent verdict. -/
theorem epochStartup_initial_cache {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd : ℕ)
    (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) :
    let L := old.next F I base rp fp heap initEnd
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started :=
  epochStartup_initial_cache_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) hI rate allocation R old
    base rp fp heap initEnd mem initialized named started hOut hN hB harrays hscalars hfEnd
    hvalid hbase hinside

end MinCostFlow.IPM.Machine
