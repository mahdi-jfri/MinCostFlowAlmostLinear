module

public import MinCostFlow.IPM.Machine.RoundRepairRelink
public import MinCostFlow.IPM.Machine.RoundDirection
import WordRAM.Tactic

/-!
# Executing the connected rounding branch

When both endpoints are in one forest component, the path cost
determines the improving direction. The chosen branch passes its
ordered endpoints and residual amount to the same cycle procedure.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Select the correct directional availability and path orientation. -/
def roundOrientedCallArgs (backward : Bool) : List Expr :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,
    .reg (if backward then 12 else 11),.reg 15,
    .reg (if backward then 2 else 3),.reg (if backward then 3 else 2),.reg 14]

/-- The connected edge executes the cost test and the selected cycle. -/
def roundConnectedBody (B : RoundProcedures) (repairRelink : ℕ) : Stmt :=
  roundDirectionBody B ;;
  .cond (.reg 15)
    (.call 16 repairRelink (roundOrientedCallArgs true) ;; .ret (.reg 16))
    (.call 16 repairRelink (roundOrientedCallArgs false) ;; .ret (.reg 16))

/-- The connected branch is deterministic. -/
theorem roundConnected_noRand (B : RoundProcedures) (repairRelink : ℕ) :
    (roundConnectedBody B repairRelink).NoRand := by
  simp [roundConnectedBody,roundDirectionBody,Stmt.NoRand]

set_option maxHeartbeats 580000 in
/-- The connected edge follows the model cost choice and preserves
the earlier caller arrays. Its extra time and space remain linear
in the number of forest cuts actually made. -/
theorem roundConnected_runs {w h L P A repairRelink : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hAlloc : ∀ b u v a heap,allocation 4 [b,u,v,heap]≤A ∧ allocation 3 [b,u,v,a,heap]≤A ∧
      allocation 2 [b,u,v,heap]≤A ∧ allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℚ) (j : Fin I.m) (model : RoundState D I) (M : ℚ)
    (hModel : LoopInv D I f P M j.val model) (hFP : ∀ i,IsFixedPoint P (f i))
    (hFrac : isIntRat (f j)=false)
    (hRoots : D.findRoot model.df (I.edge j).tail=D.findRoot model.df (I.edge j).head)
    (b ac af ab one base heap : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hL : 0<L) (hP : h∣P) (hN : I.n≤2^w)
    (hWords : ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,
      I.m+1,af,ab,heap],z<2^w)
    (hCost : RatAt mem ac h L 0 (I.edge j).cost) (hOne : RatAt mem one h L P 1)
    (hFlow : RoundFlowAt I mem base h L P model.flowArr)
    (hFwd : RatAt mem af h L P (roundAvail (f j) false))
    (hBwd : RatAt mem ab h L P (roundAvail (f j) true))
    (hTable : base+I.m*L≤b) (hAC : ac+L≤base) (hOneEnd : one+L≤base)
    (hAF : af+L≤heap) (hAB : ab+L≤heap) (hAFlo : b≤af) (hABlo : b≤ab) (hb : b≤heap)
    (hRep : R.rep b model.df x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hAvFrame : ∀ z,R.foot b x z → (z<af ∨ af+L≤z) ∧ (z<ab ∨ ab+L≤z)) (hZero : ZeroFrom mem heap)
    (hSum : Num.Fits h L (D.pathSum model.df (I.edge j).tail (I.edge j).head))
    (hNumeric : let back := roundBackward D model.df j
      let clean := roundCycleClean D I (f j) model j back
      let q := roundCycleValue D model.df j (f j) back
      let δ := roundCycleDelta D model.df j (f j) back
      ForestFits D h L P model.df ∧
        ForestFits D h L P (D.pathAdd model.df (roundFrom (I.edge j) back) (roundTo (I.edge j) back) δ) ∧
        ForestFits D h L P clean.1 ∧ Num.Fits h L (I.edge j).cost ∧ RatFits h L P q ∧
        (isIntRat q=false → RatFits h L P (⌊q⌋:ℚ) ∧ RatFits h L P ((⌈q⌉:ℚ)-q) ∧
          RatFits h L P (q-(⌊q⌋:ℚ))))
    (hSpace : heap+A+L+roundRepairRelinkCharge A L (D.toForest model.df).edges.length<2^w) :
    let next := roundEdgeStep D I f model j
    let r := next.counts.cutOps-model.counts.cutOps
    ∃ out final cost y,
      Runs w p ω (roundConnectedBody B repairRelink)
        (startState [b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,
          I.m+1,af,ab,heap] mem pos) (.returned out) final cost ∧
      R.rep b next.df y final.mem ∧ RoundFlowAt I final.mem base h L P next.flowArr ∧
      heap≤out ∧ out≤heap+A+L+roundRepairRelinkCharge A L r ∧
      ZeroFrom final.mem out ∧ (∀ z<base,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤4*rate I.n+509*L+1000+
        roundCleanupCharge (rate I.n+19*L+80) (rate I.n+17*L+115) r+R.phi b x mem := by
  dsimp only
  let back := roundBackward D model.df j
  let e := I.edge j
  let fp := base+j.val*L
  let args := [b,j.val,e.tail,e.head,ac,fp,L,P,one,base,I.m+1,af,ab,heap]
  let ap := if back then ab else af
  let u := roundFrom e back
  let v := roundTo e back
  let next := roundEdgeStep D I f model j
  have hu : e.tail<(D.toForest model.df).n := hModel.2.1.symm ▸ (hI.1 e (List.getElem_mem j.isLt)).1
  have hv : e.head<(D.toForest model.df).n := hModel.2.1.symm ▸ (hI.1 e (List.getElem_mem j.isLt)).2
  have hComp := ((hD.2.2.1 model.df e.head hModel.1 hv).2 e.tail hu).mp hRoots
  have hAlloc₁ := (hAlloc b (I.edge j).tail (I.edge j).head 0 heap).2.2.2.2
  obtain ⟨out₁,mid,c₁,x₁,hRun₁,hOut₁,hBit,hRegs,hRep₁,hLo₁,hHi₁,hZero₁,hMem₁,hFrame₁,hFoot₁,hPriv₁,hC₁⟩ :=
    roundDirection_runs D rate allocation R himpl B hB I j b ac fp one base af ab heap model.df x mem pos ω
      hWords hL hb (hAC.trans (by omega)) hCost hModel.1 hNumeric.1 hComp hSum hRep hFoot hZero (by omega)
  have hAp : ap+L≤heap := by cases hb' : back <;> simp [ap,hb',hAF,hAB]
  have hApLo : b≤ap := by cases hb' : back <;> simp [ap,hb',hAFlo,hABlo]
  have hApOld : ∀ z,R.foot b x z → z<ap ∨ ap+L≤z := by
    intro z hz
    cases hb' : back
    · simpa [ap,hb'] using (hAvFrame z hz).1
    · simpa [ap,hb'] using (hAvFrame z hz).2
  have hApNew : ∀ z,R.foot b x₁ z → z<ap ∨ ap+L≤z := by
    intro z hz
    rcases hPriv₁ z hz with h | ⟨hh,_⟩
    · exact hApOld z h
    · exact Or.inr (hAp.trans hh)
  have hAvail : RatAt mem ap h L P (roundAvail (f j) back) := by
    cases hb' : back
    · simpa [ap,hb'] using hFwd
    · simpa [ap,hb'] using hBwd
  have hAvail₁ := hAvail.agree (mem':=mid.mem) fun i hi => hFrame₁ _ (by omega)
    (fun hf => by rcases hApOld (ap+i) hf with h | h <;> omega)
  have hTable₁ : RoundFlowAt I mid.mem base h L P model.flowArr := by
    intro i
    have hi := Nat.mul_le_mul_right L (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    exact (hFlow i).frozen hMem₁ (by omega)
  have hW (i : Fin 14) : args[i.val]'i.isLt<2^w := hWords _ (List.getElem_mem (l:=args) i.isLt)
  have hu0 : e.tail<2^w := hW 2
  have hv0 : e.head<2^w := hW 3
  have huW : u<2^w := by
    cases hb' : back
    · simpa [u,roundFrom,hb'] using hv0
    · simpa [u,roundFrom,hb'] using hu0
  have hvW : v<2^w := by
    cases hb' : back
    · simpa [v,roundTo,hb'] using hu0
    · simpa [v,roundTo,hb'] using hv0
  have hBW : back.toNat<2^w := by
    have hh : 1<2^w := by unfold roundRepairRelinkCharge roundRepairRelinkSpace at hSpace; omega
    cases hb' : back
    · exact Nat.zero_lt_of_lt hh
    · exact hh
  have hWords₂ : ∀ z∈[b,j.val,e.tail,e.head,ac,fp,L,P,one,base,I.m+1,ap,back.toNat,u,v,out₁],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hW 0
    · exact hW 1
    · exact hW 2
    · exact hW 3
    · exact hW 4
    · exact hW 5
    · exact hW 6
    · exact hW 7
    · exact hW 8
    · exact hW 9
    · exact hW 10
    · have hh : b<2^w := hW 0
      have hheap : heap<2^w := hW 13
      omega
    · exact hBW
    · exact huW
    · exact hvW
    · omega
  obtain ⟨out,raw₂,c₂,y,hRun₂,hRep₂,hFlow₂,hLo₂,hHi₂,hZero₂,hMem₂,hFoot₂,hC₂⟩ :=
    roundRepairRelink_runs D hD rate allocation R himpl B hB
      (fun b u v a heap => ⟨(hAlloc b u v a heap).1,(hAlloc b u v a heap).2.1,
        (hAlloc b u v a heap).2.2.1,(hAlloc b u v a heap).2.2.2.1⟩)
      I hI f j model M hModel hFP hFrac hRoots b ac ap one base out₁ x₁ mid.mem mid.pos ω hL hP hN
      hWords₂ (hCost.frozen hMem₁ (hAC.trans (by omega))) (hOne.frozen hMem₁ (hOneEnd.trans (by omega)))
      hTable₁ hAvail₁ hTable hAC hOneEnd (hAp.trans (by omega)) hApLo (hb.trans (by omega))
      hRep₁ hFoot₁ hApNew hZero₁ hNumeric (by omega)
  have hr (i : ℕ) (hi : i<14) : mid.regs i=(startState args mem pos).regs i := hRegs i hi
  have hArgs₂ : evalArgs w mid (roundOrientedCallArgs back)=
      some [b,j.val,e.tail,e.head,ac,fp,L,P,one,base,I.m+1,ap,back.toNat,u,v,out₁] := by
    have r₀ : mid.regs 0=b := hr 0 (by decide)
    have r₁ : mid.regs 1=j.val := hr 1 (by decide)
    have r₂ : mid.regs 2=e.tail := hr 2 (by decide)
    have r₃ : mid.regs 3=e.head := hr 3 (by decide)
    have r₄ : mid.regs 4=ac := hr 4 (by decide)
    have r₅ : mid.regs 5=fp := hr 5 (by decide)
    have r₆ : mid.regs 6=L := hr 6 (by decide)
    have r₇ : mid.regs 7=P := hr 7 (by decide)
    have r₈ : mid.regs 8=one := hr 8 (by decide)
    have r₉ : mid.regs 9=base := hr 9 (by decide)
    have r₁₀ : mid.regs 10=I.m+1 := hr 10 (by decide)
    have r₁₁ : mid.regs 11=af := hr 11 (by decide)
    have r₁₂ : mid.regs 12=ab := hr 12 (by decide)
    change mid.regs 15=back.toNat at hBit
    cases hb' : back <;> simp [roundOrientedCallArgs,evalArgs,Expr.eval,r₀,r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,
      r₉,r₁₀,r₁₁,r₁₂,hOut₁,hBit,hb',ap,u,v,roundFrom,roundTo]
  let final : State := ⟨raw₂.mem,Function.update mid.regs 16 out,raw₂.pos⟩
  have hCall₂ := round_returning_call (dst:=16) hRL hArgs₂ hRun₂
  have hRet : Runs w p ω (.ret (.reg 16)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  have hCall : Runs w p ω (.call 16 repairRelink (roundOrientedCallArgs back) ;; .ret (.reg 16))
      mid (.returned out) final (16+c₂+1+2+1) :=
    runs_seq_iff.mpr (Or.inr ⟨final,_,_,hCall₂,hRet,rfl⟩)
  have hCond : Runs w p ω (.cond (.reg 15)
      (.call 16 repairRelink (roundOrientedCallArgs true) ;; .ret (.reg 16))
      (.call 16 repairRelink (roundOrientedCallArgs false) ;; .ret (.reg 16)))
      mid (.returned out) final (1+(16+c₂+1+2+1)+1) := by
    apply runs_cond_iff.mpr
    refine ⟨back.toNat,_,congrArg some hBit,?_,rfl⟩
    cases hb' : back <;> simpa [hb'] using hCall
  refine ⟨out,final,c₁+(1+(16+c₂+1+2+1)+1)+1,y,?_,hRep₂,hFlow₂,
    (show heap≤out₁ from by omega).trans hLo₂,?_,hZero₂,?_,hFoot₂,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hRun₁,hCond,rfl⟩)
  · omega
  · intro z hz
    exact (hMem₂ z hz).trans (hMem₁ z (by omega))
  · rw [hModel.2.1] at hC₁
    change _+R.phi b y raw₂.mem≤_
    omega

end MinCostFlow.IPM.Machine
