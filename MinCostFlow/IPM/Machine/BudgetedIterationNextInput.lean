module

public import MinCostFlow.IPM.Machine.BudgetedIterationOutput
public import MinCostFlow.IPM.Machine.BudgetedIterationTrace
public import MinCostFlow.IPM.Machine.BudgetedIterationFullNames
import MinCostFlow.IPM.Machine.ScalarSourcesCongr
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Reconstructing the next actual Detect/refresh input

Advance only the incoming heap and represented state. The previous
actual entry preserves the full name list and the static numeric sources.
Its valid flow cache supplies the changed numerical blocks. Fresh DS
footprint growth preserves all table and name separation. Assemble the
next complete input from these facts, leaving its allocation budget and
report inclusion as explicit caller obligations.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Reconstruct the full next refresh precondition from the actual
iteration's state, frames and valid flow blocks. The caller supplies the
next report inclusion and the global remaining allocation bound. -/
theorem budgetedIteration_next_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x y : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1) (hrep : R.rep b s' y final)
    (hmeta : ∀ z,R.foot b y z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (hflow : ∀ e<I.m,Num.Valid final (f+e*F.limbs) F.fmt.limbBits F.limbs)
    (harrays : ∀ p∈[base,c,lo,up],p+I.m*F.limbs≤f)
    (hscalars : ∀ p∈[r,a,one,mn,mx],p+F.limbs≤f)
    (hsubset : (A.detect s').1⊆(namedInstance I).E)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s' [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w) :
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s' y q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] final := by
  have hpreCopy := hpre
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,_,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,es,heq,
    hlen,hnd,hlist,hgraph,_,_,_,havoid,hnameAvoid,hsEnd,htEnd,hnEnd,hends,hshared,
    hdisArrays,hdisScalars,hsld,hsgd,hldEnd,hgdEnd,hdis,hfamily,hbaseValid,hwidth,_,hOne,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hfEnd := hends f (by simp)
  have hfHeap : f≤heap := by omega
  have hbefore : tableEnd≤heap := by omega
  have hsource := budgetedIteration_source_frame F A I κ α rate allocation R hpreCopy hout hfHeap
    (fun z hz => havoid z (by omega))
  have hnames := budgetedIteration_full_names F A I κ α rate allocation R hpreCopy hout
  have hfit := budgetedIteration_success_fits hout haccept
  have hheap := budgetedIteration_end_ge F A I κ α rate allocation R hout
  have hnewAvoid := iteration_footprint_separation R hmeta hbefore hnEnd havoid hnameAvoid
  have hzero := (budgetedIteration_status hout).2.2
  have hentryEnd (p e : ℕ) (hp : p∈[base,c,lo,up]) (he : e<I.m) : p+e*F.limbs+F.limbs≤f :=
    (reported_entry_end p F.limbs e I.m he).trans (harrays p hp)
  have hnewList : ListAt final names es := by
    intro i hi
    have hiM : i<I.m := by omega
    exact (hnames i hiM).trans (hlist i hi)
  have hnewCover : ∀ e∈(namedInstance I).E,∃ i<I.m,final (names+i)=e := by
    intro e he
    obtain ⟨i,hi,hread⟩ := hcover e he
    exact ⟨i,hi,(hnames i hi).trans hread⟩
  have hnewFamily : ∀ e∈es,scalarCoefficientSourceConditions w F.fmt.limbBits q K I.m
      (c+e*F.limbs) r (lo+e*F.limbs) (f+e*F.limbs) (up+e*F.limbs)
      a one mn mx F.limbs F.fmt.precision E sourceEnd final := by
    intro e he
    have heM := (hgraph e he).2
    apply scalarCoefficientSourceConditions_replace_flow (hfamily e he) le_rfl (hflow e heM)
    intro p hp i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p
    · have hend := hentryEnd c e (by simp) heM
      exact hsource _ (by omega)
    · have hend := hscalars r (by simp)
      exact hsource _ (by omega)
    · have hend := hentryEnd lo e (by simp) heM
      exact hsource _ (by omega)
    · have hend := hentryEnd up e (by simp) heM
      exact hsource _ (by omega)
    · have hend := hscalars a (by simp)
      exact hsource _ (by omega)
    · have hend := hscalars one (by simp)
      exact hsource _ (by omega)
    · have hend := hscalars mn (by simp)
      exact hsource _ (by omega)
    · have hend := hscalars mx (by simp)
      exact hsource _ (by omega)
  have hnewBase : ∀ e∈es,Num.Valid final (base+e*F.limbs) F.fmt.limbBits F.limbs := by
    intro e he
    exact Num.IPM.valid_frozen hsource (hentryEnd base e (by simp) (hgraph e he).2) (hbaseValid e he)
  have hnewWidth : ∀ e∈es,Num.fixVal final (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal final (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E := by
    intro e he
    rw [Num.IPM.fixVal_frozen hsource (hentryEnd up e (by simp) (hgraph e he).2),
      Num.IPM.fixVal_frozen hsource (hentryEnd lo e (by simp) (hgraph e he).2)]
    exact hwidth e he
  refine ⟨names,base,lo,up,f,v,c,r,a,one,mn,mx,E,ld,gd,rfl,?_,hnewCover,hsubset,hspace⟩
  refine ⟨names,I.m,base,lo,up,f,v,c,r,a,one,mn,mx,E,ld,gd,es,rfl,hlen,hnd,hnewList,hgraph,
    hfit,hrep,(fun z hz => (hmeta z hz).1),hnewAvoid.1,hnewAvoid.2,hsEnd,htEnd,
    (by omega),hends,hshared,hdisArrays,hdisScalars,hsld,hsgd,hldEnd,hgdEnd,hdis,hnewFamily,
    hnewBase,hnewWidth,hzero,hOne,?_⟩
  omega

end MinCostFlow.IPM.Machine
