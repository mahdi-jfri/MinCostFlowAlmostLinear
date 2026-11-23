module

public import MinCostFlow.IPM.Machine.ReportedEdgeOutput

/-!
# Accepted reported coordinates remain strictly inside capacities

The actual Query recovery checks the true base-plus-implicit-flow sum.
The coefficient stage writes beyond the source prefix, while the
capacity blocks avoid the flow block. Thus the final stored flow
retains the strict capacity inequalities certified by the Query guard.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Success of the complete reported-edge entry certifies strict
feasibility of its final cached coordinate, with the final capacities. -/
theorem reportedEdge_inside {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ} {baseValue : ℝ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (hbase : ScalarAt mem base F.fmt.limbBits F.limbs F.fmt.precision baseValue)
    (haccept : mem' (v-1)=1) :
    Num.fixVal mem' lo F.fmt.limbBits F.limbs F.fmt.precision<
      Num.fixVal mem' f F.fmt.limbBits F.limbs F.fmt.precision ∧
    Num.fixVal mem' f F.fmt.limbBits F.limbs F.fmt.precision<
      Num.fixVal mem' up F.fmt.limbBits F.limbs F.fmt.precision := by
  have hframe := reportedEdge_source_frame F A G m κ α rate allocation R hpre hout
  obtain ⟨queryEnd,queryMem,hQ,hcap,_,hflow⟩ :=
    reportedEdge_accepted F A G m κ α rate allocation R hpre hout hbase haccept
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,_,hs,hend,_,_,hbEnd,
    hsrc,hdis,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,_,_,hloEnd,_,hupEnd,_,_,_,_,hloValid,_,hupValid,_⟩ := hs
  have hguard := queryCoordinate_acceptance F A G m κ α rate allocation R hQ hbase
    ⟨hloValid,rfl⟩ ⟨hupValid,rfl⟩ (hbEnd.trans hend) (hloEnd.trans hend) (hupEnd.trans hend)
    (fun i hi => hsrc _ (by omega)) (fun i hi => hsrc _ (by omega)) (fun i hi => hsrc _ (by omega))
  have hinside : Num.fixVal mem lo F.fmt.limbBits F.limbs F.fmt.precision<baseValue+A.query s e ∧
      baseValue+A.query s e<Num.fixVal mem up F.fmt.limbBits F.limbs F.fmt.precision := by
    split_ifs at hguard with hh
    · exact hh
    · omega
  have same (p : ℕ) (hp : p∈[lo,up]) (hpEnd : p+F.limbs≤sourceEnd) :
      Num.fixVal mem' p F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem p F.fmt.limbBits F.limbs F.fmt.precision := by
    unfold Num.fixVal
    apply congrArg (fun z : ℤ => (z:ℝ)/(2:ℝ)^F.fmt.precision)
    apply Num.intVal_congr
    intro i hi
    apply hframe _ (by omega)
    have hsep := hdis p (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
      tauto)
    rcases hsep with hh | hh <;> omega
  rw [same lo (by simp) hloEnd,same up (by simp) hupEnd,hflow.2]
  exact hinside

end MinCostFlow.IPM.Machine
