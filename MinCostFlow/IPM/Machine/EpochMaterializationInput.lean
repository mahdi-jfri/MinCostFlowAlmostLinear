module

public import MinCostFlow.IPM.Machine.EpochConditions
public import MinCostFlow.IPM.Machine.FlagRecord
import MinCostFlow.IPM.Machine.ScalarSourcesCongr
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Reusing the completed epoch packet to read every flow coordinate

A completed iteration loop writes a fresh success flag. Below the old
heap, the source words, cache and full name list are identical.
The next call can therefore reuse the reported-edge program on the
full name list, at the actual endpoint after that flag.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The successful return of an epoch supplies the complete
materialization input and full name coverage. -/
theorem epoch_materialization_input {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K i v : ℕ) (Q : EpochPoint R.τ)
    (final : ℕ → ℕ) {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hQ : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i Q)
    (hflag : (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v final)
    (hrep : R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)) Q.credit final) :
    (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle
      (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)) Q.credit q K L.sourceEnd L.tableEnd).pre
      ((L.packet F I v).take 20) final ∧
      (∀ e∈(namedInstance I).E,∃ j<I.m,final (L.names+j)=e) := by
  let heap := Q.machine.regs 8
  let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)
  let mem := Q.machine.mem
  have hpre := hQ.2.2.2.2.2.2.2.2.2.1
  obtain ⟨names,base,lo,up,f,old,c,r,a,one,mn,mx,E,ld,gd,heq,hfull,hcover,_,hspace⟩ := hpre
  change [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,
    L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m]=_ at heq
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s Q.credit
    q K L.sourceEnd L.tableEnd).pre
    [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,
      L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem at hfull
  obtain ⟨names,count,base,lo,up,f,old,c,r,a,one,mn,mx,E,ld,gd,es,heq,
    hlen,hnd,hlist,hgraph,hfit,_,hfoot,havoid,hnameAvoid,hsEnd,htEnd,hnEnd,hends,hshared,
    hdisArrays,hdisScalars,hsld,hsgd,hldEnd,hgdEnd,hdis,hfamily,hbase,hwidth,_,hOne,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hframe : ∀ z<heap,final z=mem z := hflag.1.2.2.1
  have hend : v=heap+1 := hflag.2
  have hbudget : v+I.m*reportedEdgesScratch F I.m L.handle L.exponent allocation+1<2^w := by
    change heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2
      s [L.handle,heap] mem+2*(I.m+1)+I.m*reportedEdgesScratch F I.m L.handle L.exponent allocation+4<2^w at hspace
    omega
  have hlist' : ListAt final L.names es :=
    hlist.congr (fun z _ hz => hframe z (by omega))
  have hsource : L.sourceEnd≤heap := by omega
  have heEnd (ptr : ℕ) (hp : ptr∈[L.base,L.cost,L.lower,L.flow,L.upper]) (e : ℕ) (he : e<I.m) :
      ptr+e*F.limbs+F.limbs≤heap :=
    ((reported_entry_end ptr F.limbs e I.m he).trans (hends ptr hp)).trans hsource
  have hfamily' : ∀ e∈es,scalarCoefficientSourceConditions w F.fmt.limbBits q K I.m
      (L.cost+e*F.limbs) L.residual (L.lower+e*F.limbs) (L.flow+e*F.limbs) (L.upper+e*F.limbs)
      L.alpha L.one L.slackMin L.slackMax F.limbs F.fmt.precision L.exponent L.sourceEnd final := by
    intro e he
    have hem := (hgraph e he).2
    apply scalarCoefficientSourceConditions_congr (hfamily e he) le_rfl
    intro ptr hp j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst ptr
    · exact hframe _ (by have hh := heEnd L.cost (by simp) e hem; omega)
    · exact hframe _ (by have hh := (hshared L.residual (by simp)).trans hsource; omega)
    · exact hframe _ (by have hh := heEnd L.lower (by simp) e hem; omega)
    · exact hframe _ (by have hh := heEnd L.flow (by simp) e hem; omega)
    · exact hframe _ (by have hh := heEnd L.upper (by simp) e hem; omega)
    · exact hframe _ (by have hh := (hshared L.alpha (by simp)).trans hsource; omega)
    · exact hframe _ (by have hh := (hshared L.one (by simp)).trans hsource; omega)
    · exact hframe _ (by have hh := (hshared L.slackMin (by simp)).trans hsource; omega)
    · exact hframe _ (by have hh := (hshared L.slackMax (by simp)).trans hsource; omega)
  have hbase' : ∀ e∈es,Num.Valid final (L.base+e*F.limbs) F.fmt.limbBits F.limbs := by
    intro e he
    exact Num.IPM.valid_frozen hframe (heEnd L.base (by simp) e (hgraph e he).2) (hbase e he)
  have hwidth' : ∀ e∈es,Num.fixVal final (L.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal final (L.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^L.exponent := by
    intro e he
    rw [Num.IPM.fixVal_frozen hframe (heEnd L.upper (by simp) e (hgraph e he).2),
      Num.IPM.fixVal_frozen hframe (heEnd L.lower (by simp) e (hgraph e he).2)]
    exact hwidth e he
  refine ⟨⟨L.names,I.m,L.base,L.lower,L.upper,L.flow,v,L.cost,L.residual,L.alpha,L.one,L.slackMin,L.slackMax,
    L.exponent,L.lengths,L.gradient,es,rfl,hlen,hnd,hlist',hgraph,hfit,hrep,?_,havoid,hnameAvoid,hsEnd,htEnd,
    by omega,hends,hshared,hdisArrays,hdisScalars,hsld,hsgd,hldEnd,hgdEnd,hdis,hfamily',hbase',hwidth',
    hflag.1.2.2.2.1,hOne,hbudget⟩,?_⟩
  · exact fun z hz => (hfoot z hz).trans (by omega)
  · intro e he
    obtain ⟨j,hj,hr⟩ := hcover e he
    exact ⟨j,hj,(hframe _ (by omega)).trans hr⟩

end MinCostFlow.IPM.Machine
