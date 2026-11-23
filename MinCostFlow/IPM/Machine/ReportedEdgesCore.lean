module

public import MinCostFlow.IPM.Machine.ReportedEdgesSelectedRun
public import MinCostFlow.IPM.Machine.ReportedEdgesInputWords
public import MinCostFlow.IPM.Machine.ReportedEdgesPostCompose
public import MinCostFlow.IPM.Machine.ReportedEdgesPostBranches
import WordRAM.Tactic

/-!
# Running the complete reported-list counter loop

Track the logical suffix while retaining the original runtime counter
and fixed arguments. A successful iteration gives the full tail input
condition; rejection returns immediately. Compose the proved first-edge
and tail postconditions. The same concrete credit is retained across
the induction, counting nine control operations per successful iteration
and four for the final false guard.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual counter loop satisfies the complete list postcondition,
retains the concrete DS credit and has a linear per-name cost. The
zero-length case needs a current success bit, as supplied by the last
accepted iteration. The outer entry handles an initially empty list. -/
theorem reportedEdgesCore_runs_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag entry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (names count base lo up f heap c r a one mn mx E ld gd idx finish : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w) (hfinish : finish<2^w)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem)
    (hfixed : ∀ z∈[b,base,lo,up,f,F.limbs,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0)
    (hheap : parent.regs 21=heap) (hcounter : parent.regs 20=idx)
    (hend : parent.regs 2=finish) (hremaining : idx+count=finish)
    (haddress : parent.regs 1+idx=names) (hempty : count=0 → parent.mem (heap-1)=1) :
    ∃ o st cost v x',Runs w p ω (forUp 20 (.reg 2) (reportedEdgesLoopBody entry)) parent o st cost ∧
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m]
        parent.mem v st.mem ∧ R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (match o with
        | .normal => st.regs 21=v ∧ st.mem (v-1)=1
        | .returned u => u=v ∧ st.mem (v-1)=0) ∧
      (∀ j<20,st.regs j=parent.regs j) ∧
      v≤heap+count*reportedEdgesScratch F m b E allocation ∧
      cost+R.phi b x' st.mem≤count*reportedEdgesCharge F m E rate+4+R.phi b x parent.mem := by
  induction count generalizing names heap x idx parent with
  | zero =>
    have hbit := hempty rfl
    have hpost := reportedEdges_post_nil F A G m rate allocation R hpre hbit
    have hpreCopy := hpre
    obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
      _,_,_,_,_,hrep,hfoot,_⟩ := hpreCopy
    simp only [List.cons.injEq,and_true,true_and] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    have hidx : idx=finish := by omega
    refine ⟨.normal,parent,4,heap,x,?_,hpost,hrep,
      (fun z hz => ⟨hfoot z hz,Or.inl hz⟩),⟨hheap,hbit⟩,(fun _ _ => rfl),by simp,by simp⟩
    apply runs_loop_iff.mpr
    refine Or.inl ⟨?_,rfl,rfl,rfl⟩
    exact Expr.eval_lt_false (x:=finish) (y:=finish)
      (by simp [Expr.eval,hcounter,hidx]) (by simp [Expr.eval,hend]) le_rfl hw
  | succ k ih =>
    have hlt : idx<finish := by omega
    have hidxWord : idx<2^w := hlt.trans hfinish
    have hnextWord : idx+1<2^w := by omega
    have hcond : (Expr.bin .lt (.reg 20) (.reg 2)).eval w parent=some 1 :=
      Expr.eval_lt_true (x:=idx) (y:=finish)
        (by simp [Expr.eval,hcounter]) (by simp [Expr.eval,hend]) hlt hw
    have hwords := reportedEdges_input_words F A G m rate allocation R hpre hfixed
    let e := parent.mem names
    obtain ⟨o₁,st₁,c₁,v,mid,hr₁,hpost₁,hrep₁,hmeta₁,hbranch₁,hregs₁,hcost₁⟩ :=
      reportedEdges_selected_run_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
        hflag hp s x names (k+1) base lo up f heap c r a one mn mx E ld gd 0 e parent ω hw
        hpre hwords hregs hheap (by omega)
        (by simpa only [hcounter,Nat.add_zero] using haddress) (by simp only [Nat.add_zero,e])
    have hcharge : c₁+R.phi b mid st₁.mem+9≤reportedEdgesCharge F m E rate+R.phi b x parent.mem := by
      simp only [minRatioMachineContract,Nat.mul_one] at hcost₁
      unfold reportedEdgesCharge
      omega
    have hstepBound := reportedEdge_frame F A G m κ α rate allocation R hpost₁
    by_cases haccept : st₁.mem (v-1)=1
    · simp only [haccept,ite_true] at hbranch₁
      obtain ⟨rfl,hheap₁⟩ := hbranch₁
      have htailPre := reportedEdges_tail_pre F A G m κ α rate allocation R hpre rfl hpost₁ hrep₁ hmeta₁ haccept
      let next : State := {st₁ with regs:=Function.update st₁.regs 20 (idx+1)}
      have htailRegs : ∀ j<20,j≠1 → j≠2 → j≠8 → next.regs j=
          [b,names+1,k,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0 := by
        intro j hj h1 h2 h8
        dsimp only [next]
        rw [Function.update_of_ne (by omega : j≠20)]
        exact (hregs₁ j (by omega)).trans ((hregs j hj h1 h2 h8).trans
          (reportedEdges_fixed_getD b names (k+1) base lo up f F.limbs heap c r a one mn mx
            F.fmt.precision E ld gd m (names+1) k v j hj h1 h2 h8))
      have htailHeap : next.regs 21=v := by simpa only [next,Function.update_of_ne (by decide : 21≠20)] using hheap₁
      have htailCounter : next.regs 20=idx+1 := by simp [next]
      have htailEnd : next.regs 2=finish := by
        simpa only [next,Function.update_of_ne (by decide : 2≠20)] using (hregs₁ 2 (by decide)).trans hend
      have htailAddress : next.regs 1+(idx+1)=names+1 := by
        dsimp only [next]
        rw [Function.update_of_ne (by decide : 1≠20),hregs₁ 1 (by decide)]
        omega
      obtain ⟨o₂,st₂,c₂,u,final,hr₂,hpost₂,hrep₂,hmeta₂,hbranch₂,hregs₂,hspace₂,hcost₂⟩ :=
        ih (names:=names+1) (heap:=v) (x:=mid) (idx:=idx+1) (parent:=next)
          htailPre htailRegs htailHeap htailCounter htailEnd (by omega) htailAddress (fun _ => haccept)
      have hcounter₁ : st₁.regs 20=idx := (hregs₁ 20 (by decide)).trans hcounter
      have hinc : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1))) st₁ .normal next 4 := by
        apply runs_assign_iff.mpr
        exact ⟨idx+1,by eval_expr,rfl,rfl,rfl⟩
      have hbody : Runs w p ω
          (reportedEdgesLoopBody entry ;; .assign 20 (.bin .add (.reg 20) (.const 1)))
          parent .normal next (c₁+5) :=
        runs_seq_iff.mpr (Or.inr ⟨st₁,c₁,4,hr₁,hinc,by omega⟩)
      have hfullPost := reportedEdges_post_cons F A G m κ α rate allocation R hpre rfl hpost₁
        hrep₁ hmeta₁ haccept hpost₂
      have hheapWord : heap<2^w := hwords _ (by simp)
      have heM : e<m := by
        obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,es,heq,hlen,_,hlist,hgraph,_⟩ := hpre
        simp only [List.cons.injEq,and_true,true_and] at heq
        obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
        exact (hgraph e (List.mem_iff_getElem.mpr ⟨0,by omega,(hlist 0 (by omega)).symm⟩)).2
      have halloc := query_allocation_le_bound (b:=b) allocation heM hheapWord
      have hspace₁ : v≤heap+reportedEdgesScratch F m b E allocation := by
        have hh := hstepBound.2.1
        change v≤heap+allocation 1 [b,e,heap]+16*F.limbs+
          Num.IPM.lengthSpace F.limbs F.fmt.precision E+
          Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 at hh
        unfold reportedEdgesScratch
        omega
      refine ⟨o₂,st₂,c₁+c₂+9,u,final,?_,hfullPost,hrep₂,?_,hbranch₂,?_,?_,?_⟩
      · apply runs_loop_iff.mpr
        exact Or.inr (Or.inr ⟨1,next,c₁+5,c₂,hcond,by decide,hbody,hr₂,by simp; omega⟩)
      · intro z hz
        refine ⟨(hmeta₂ z hz).1,?_⟩
        rcases (hmeta₂ z hz).2 with hold | hfresh
        · exact (hmeta₁ z hold).2
        · exact Or.inr (hstepBound.1.trans hfresh)
      · intro j hj
        rw [hregs₂ j hj]
        dsimp only [next]
        rw [Function.update_of_ne (by omega : j≠20)]
        exact hregs₁ j (by omega)
      · simp only [Nat.succ_mul]
        omega
      · dsimp only [next] at hcost₂
        simp only [Nat.succ_mul]
        omega
    · simp only [haccept,ite_false] at hbranch₁
      subst o₁
      have hzero : st₁.mem (v-1)=0 := by
        have hb := reportedEdge_status F A G m κ α rate allocation R hpost₁
        omega
      have hpost := reportedEdges_post_reject F A G m κ α rate allocation R hpre rfl hpost₁ hrep₁ hmeta₁ hzero
      have hbody : Runs w p ω
          (reportedEdgesLoopBody entry ;; .assign 20 (.bin .add (.reg 20) (.const 1)))
          parent (.returned v) st₁ (c₁+1) := runs_seq_iff.mpr (Or.inl ⟨v,c₁,hr₁,rfl,rfl⟩)
      have hheapWord : heap<2^w := hwords _ (by simp)
      have heM : e<m := by
        obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,es,heq,hlen,_,hlist,hgraph,_⟩ := hpre
        simp only [List.cons.injEq,and_true,true_and] at heq
        obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
        exact (hgraph e (List.mem_iff_getElem.mpr ⟨0,by omega,(hlist 0 (by omega)).symm⟩)).2
      have halloc := query_allocation_le_bound (b:=b) allocation heM hheapWord
      have hspace₁ : v≤heap+reportedEdgesScratch F m b E allocation := by
        have hh := hstepBound.2.1
        change v≤heap+allocation 1 [b,e,heap]+16*F.limbs+
          Num.IPM.lengthSpace F.limbs F.fmt.precision E+
          Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 at hh
        unfold reportedEdgesScratch
        omega
      have hmul : reportedEdgesCharge F m E rate≤(k+1)*reportedEdgesCharge F m E rate := by
        have hh := Nat.mul_le_mul_right (reportedEdgesCharge F m E rate) (Nat.succ_le_succ (Nat.zero_le k))
        simpa only [Nat.one_mul] using hh
      have hmulSpace : reportedEdgesScratch F m b E allocation≤(k+1)*reportedEdgesScratch F m b E allocation := by
        have hh := Nat.mul_le_mul_right (reportedEdgesScratch F m b E allocation) (Nat.succ_le_succ (Nat.zero_le k))
        simpa only [Nat.one_mul] using hh
      refine ⟨.returned v,st₁,c₁+5,v,mid,?_,hpost,hrep₁,hmeta₁,⟨rfl,hzero⟩,
        (fun j hj => hregs₁ j (by omega)),by omega,by omega⟩
      apply runs_loop_iff.mpr
      exact Or.inr (Or.inl ⟨1,v,c₁+1,hcond,by decide,hbody,rfl,by simp; omega⟩)

theorem reportedEdgesCore_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag entry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (names count base lo up f heap c r a one mn mx E ld gd idx finish : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w) (hfinish : finish<2^w)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem)
    (hfixed : ∀ z∈[b,base,lo,up,f,F.limbs,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0)
    (hheap : parent.regs 21=heap) (hcounter : parent.regs 20=idx)
    (hend : parent.regs 2=finish) (hremaining : idx+count=finish)
    (haddress : parent.regs 1+idx=names) (hempty : count=0 → parent.mem (heap-1)=1) :
    ∃ o st cost v x',Runs w p ω (forUp 20 (.reg 2) (reportedEdgesLoopBody entry)) parent o st cost ∧
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m]
        parent.mem v st.mem ∧ R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (match o with
        | .normal => st.regs 21=v ∧ st.mem (v-1)=1
        | .returned u => u=v ∧ st.mem (v-1)=0) ∧
      (∀ j<20,st.regs j=parent.regs j) ∧
      v≤heap+count*reportedEdgesScratch F m b E allocation ∧
      cost+R.phi b x' st.mem≤count*reportedEdgesCharge F m E rate+4+R.phi b x parent.mem :=
  reportedEdgesCore_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient hflag
    hp s x names count base lo up f heap c r a one mn mx E ld gd idx finish parent ω hw hfinish
    hpre hfixed hregs hheap hcounter hend hremaining haddress hempty

end MinCostFlow.IPM.Machine
