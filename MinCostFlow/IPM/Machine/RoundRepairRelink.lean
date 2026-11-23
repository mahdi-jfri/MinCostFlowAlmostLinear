module

public import MinCostFlow.IPM.Machine.RoundProcedures
import WordRAM.Tactic

/-!
# Completing the chosen rounding cycle

The chosen direction fixes the forest path and the working edge's
availability. After exact correction and cleanup, relink only when
the working edge is still fractional.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [b,eid,u,v,cost,coordinate,L,P,one,base,fuel,availability,
backward,from,to,heap], execute the selected cycle branch. -/
def roundRepairRelinkBody (B : RoundProcedures) : Stmt :=
  .call 16 B.repair [.reg 0,.reg 13,.reg 14,.reg 11,.reg 5,.reg 6,
    .reg 12,.reg 9,.reg 10,.reg 15] ;;
  .call 16 B.relink [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 16] ;;
  .ret (.reg 16)

/-- Correction, cleanup, and relinking use deterministic calls. -/
theorem roundRepairRelink_noRand (B : RoundProcedures) : (roundRepairRelinkBody B).NoRand := by
  simp [roundRepairRelinkBody,Stmt.NoRand]

/-- Numerical and per-operation bounds for the connected branch,
before adding the charge for the edges cut during cleanup. -/
def roundRepairRelinkSpace (A L : ℕ) : ℕ := 3*A+8+15*L

/-- A geometry bound for the append-only workspace of a connected
edge includes cleanup's cost per cut. -/
def roundRepairRelinkCharge (A L r : ℕ) : ℕ :=
  roundRepairRelinkSpace A L+roundCleanupCharge (A+4+2*L) A r

set_option maxHeartbeats 260000 in
/-- The exact connected branch produces the forest and working
coordinates of `roundEdgeStep`. The bound depends on the count of
actual cuts and composes with the model's global cut count. -/
theorem roundRepairRelink_runs {w h L P A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hAlloc : ∀ b u v a heap,allocation 4 [b,u,v,heap]≤A ∧ allocation 3 [b,u,v,a,heap]≤A ∧
      allocation 2 [b,u,v,heap]≤A ∧ allocation 1 [b,a,heap]≤A)
    (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℚ) (j : Fin I.m) (model : RoundState D I) (M : ℚ)
    (hModel : LoopInv D I f P M j.val model) (hFP : ∀ i,IsFixedPoint P (f i))
    (hFrac : isIntRat (f j)=false)
    (hRoots : D.findRoot model.df (I.edge j).tail=D.findRoot model.df (I.edge j).head)
    (b ac ap one base heap : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hL : 0<L) (hP : h∣P) (hN : I.n≤2^w)
    (hWords : let back := roundBackward D model.df j
      ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,
        I.m+1,ap,back.toNat,roundFrom (I.edge j) back,roundTo (I.edge j) back,heap],z<2^w)
    (hCost : RatAt mem ac h L 0 (I.edge j).cost) (hOne : RatAt mem one h L P 1)
    (hFlow : RoundFlowAt I mem base h L P model.flowArr)
    (hAvail : RatAt mem ap h L P (roundAvail (f j) (roundBackward D model.df j)))
    (hTable : base+I.m*L≤b) (hAC : ac+L≤base) (hOneEnd : one+L≤base)
    (hAP : ap+L≤heap) (hAPlo : b≤ap) (hb : b≤heap)
    (hRep : R.rep b model.df x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hAvailFrame : ∀ z,R.foot b x z → z<ap ∨ ap+L≤z) (hZero : ZeroFrom mem heap)
    (hNumeric : let back := roundBackward D model.df j
      let clean := roundCycleClean D I (f j) model j back
      let q := roundCycleValue D model.df j (f j) back
      let δ := roundCycleDelta D model.df j (f j) back
      ForestFits D h L P model.df ∧
        ForestFits D h L P (D.pathAdd model.df (roundFrom (I.edge j) back) (roundTo (I.edge j) back) δ) ∧
        ForestFits D h L P clean.1 ∧ Num.Fits h L (I.edge j).cost ∧ RatFits h L P q ∧
        (isIntRat q=false → RatFits h L P (⌊q⌋:ℚ) ∧ RatFits h L P ((⌈q⌉:ℚ)-q) ∧
          RatFits h L P (q-(⌊q⌋:ℚ))))
    (hSpace : heap+roundRepairRelinkCharge A L (D.toForest model.df).edges.length<2^w) :
    let back := roundBackward D model.df j
    let next := roundEdgeStep D I f model j
    let r := next.counts.cutOps-model.counts.cutOps
    ∃ out final cost y,
      Runs w p ω (roundRepairRelinkBody B)
        (startState [b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,
          I.m+1,ap,back.toNat,roundFrom (I.edge j) back,roundTo (I.edge j) back,heap] mem pos)
        (.returned out) final cost ∧
      R.rep b next.df y final.mem ∧ RoundFlowAt I final.mem base h L P next.flowArr ∧
      heap≤out ∧ out≤heap+roundRepairRelinkCharge A L r ∧
      ZeroFrom final.mem out ∧ (∀ z<base,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤3*rate I.n+468*L+875+
        roundCleanupCharge (rate I.n+19*L+80) (rate I.n+17*L+115) r+R.phi b x mem := by
  dsimp only at hWords hNumeric ⊢
  let back := roundBackward D model.df j
  let edge := I.edge j
  let fp := base+j.val*L
  let u := roundFrom edge back
  let v := roundTo edge back
  let aval := roundAvail (f j) back
  let q := roundCycleValue D model.df j (f j) back
  let clean := roundCycleClean D I (f j) model j back
  let next := roundEdgeStep D I f model j
  let parent := startState [b,j.val,edge.tail,edge.head,ac,fp,L,P,one,base,
    I.m+1,ap,back.toNat,u,v,heap] mem pos
  have hM := hModel
  obtain ⟨hInv,hModelN,hStrict,_,hFresh,_,_,_,_,hLink,hCut,_,_,_,_,hPts,_,_⟩ := hM
  have hTail : edge.tail<I.n := (hI.1 edge (List.getElem_mem j.isLt)).1
  have hHead : edge.head<I.n := (hI.1 edge (List.getElem_mem j.isLt)).2
  have hTail' : edge.tail<(D.toForest model.df).n := hModelN.symm ▸ hTail
  have hHead' : edge.head<(D.toForest model.df).n := hModelN.symm ▸ hHead
  have hComp := ((hD.2.2.1 model.df edge.head hInv hHead').2 edge.tail hTail').mp hRoots
  obtain ⟨hNn,hPq,hLoq,hHiq,hPushed,hWeak,hInvC,hNC,hValue,hDisc,hCount,hLen⟩ :=
    roundCycleClean_properties hD model j back hModel hFP hFrac hComp
  obtain ⟨hFit₀,hFit₁,hFitC,hFitCost,hFitQ,hFitAvail⟩ := hNumeric
  have hComp' : (D.toForest model.df).SameComp u v := by
    change (D.toForest model.df).SameComp (roundFrom edge back) (roundTo edge back)
    cases hb' : back
    · simpa [roundFrom,roundTo,hb'] using hComp.symm
    · simpa [roundFrom,roundTo,hb'] using hComp
  have hV := hD.2.1 model.df hInv
  obtain ⟨steps,hPath,_,_⟩ := MathForest.findSteps_some_of_sameComp hV hComp'
  have hFuel : (D.toForest model.df).edges.length<I.m+1 := by
    have hj := j.isLt
    omega
  have hArgs₁ : evalArgs w parent [.reg 0,.reg 13,.reg 14,.reg 11,.reg 5,.reg 6,.reg 12,.reg 9,.reg 10,.reg 15]=
      some [b,u,v,ap,fp,L,back.toNat,base,I.m+1,heap] := rfl
  let input := [b,j.val,edge.tail,edge.head,ac,fp,L,P,one,base,I.m+1,ap,back.toNat,u,v,heap]
  have hW (i : Fin 16) : input[i.val]'i.isLt<2^w :=
    hWords _ (List.getElem_mem (l:=input) i.isLt)
  have hWords₁ : ∀ z∈[b,u,v,ap,fp,L,back.toNat,base,I.m+1,heap],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hW 0
    · exact hW 13
    · exact hW 14
    · exact hW 11
    · exact hW 5
    · exact hW 6
    · exact hW 12
    · exact hW 9
    · exact hW 10
    · exact hW 15
  have hSpace₁ : heap+2*A+4+4*L+roundCleanupCharge (A+4+2*L) A (D.toForest model.df).edges.length<2^w := by
    unfold roundRepairRelinkCharge roundRepairRelinkSpace at hSpace
    omega
  have hFj := (hFresh j (Nat.le_refl _)).2
  obtain ⟨out₁,raw₁,c₁,x₁,hRun₁,hRep₁,hFlow₁,hLo₁,hHi₁,hZero₁,hFrame₁,hFoot₁,hC₁⟩ :=
    roundCycleRepair_runs D hD rate allocation R himpl hB.push_at hB.pathMin_at hB.delta_spec hB.coordinate_spec hB.pathAdd_at
      hB.cleanup_at hB.pathMin_at hB.pathZero_spec hB.copy_spec hB.cut_at
      (fun b u v a heap => ⟨(hAlloc b u v a heap).1,(hAlloc b u v a heap).2.1,(hAlloc b u v a heap).2.2.1⟩)
      I f model.flowArr j b u v ap base (I.m+1) heap back aval
      (roundCycleCounts model.counts) (roundCycleRats D model.df j (f j) back model.computedRats)
      steps model.df x mem pos ω hWords₁ hL hAP hAPlo hb hTable hFlow hAvail hInv hFit₀ hPath
      hRep hFoot hAvailFrame hZero (hModelN.symm ▸ hN) hFuel (fun e he => (hStrict e he).1)
      (hPts hFP).1 hNn hSpace₁ (by rw [hFj]; exact ⟨hFitQ,hFit₁⟩)
  let r := (D.toForest model.df).edges.length-(D.toForest clean.1).edges.length
  rw [hFj] at hRep₁ hFlow₁
  have hRead₁ : R.rep b clean.1 x₁ raw₁.mem := hRep₁
  have hTable₁ : RoundFlowAt I raw₁.mem base h L P clean.2.1 := hFlow₁
  change out₁≤heap+2*A+4+4*L+roundCleanupCharge (A+4+2*L) A _ at hHi₁
  simp only [hFj] at hHi₁ hC₁
  change out₁≤heap+2*A+4+4*L+roundCleanupCharge (A+4+2*L) A r at hHi₁
  have hr : r+(D.toForest clean.1).edges.length=(D.toForest model.df).edges.length := by
    dsimp only [r]
    have he : (D.toForest clean.1).edges.length≤(D.toForest model.df).edges.length := hLen
    omega
  have hrLe : r≤(D.toForest model.df).edges.length := Nat.sub_le _ _
  have hBound : roundCleanupCharge (A+4+2*L) A r≤roundCleanupCharge (A+4+2*L) A (D.toForest model.df).edges.length :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ hrLe) _
  have hSpace₂ : out₁+11*L+4+A<2^w := by
    unfold roundRepairRelinkCharge roundRepairRelinkSpace at hSpace
    omega
  have hW₂ : ∀ z∈[b,j.val,edge.tail,edge.head,ac,fp,L,P,one,out₁],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hW 0
    · exact hW 1
    · exact hW 2
    · exact hW 3
    · exact hW 4
    · exact hW 5
    · exact hW 6
    · exact hW 7
    · exact hW 8
    · omega
  have hFp : fp+L≤b := by
    have hj := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hj
    dsimp [fp]
    omega
  have hRel (hQ : isIntRat q=false) :
      let e := roundingEdge I j (f j) q
      e.u<(D.toForest clean.1).n ∧ e.v<(D.toForest clean.1).n ∧ ¬(D.toForest clean.1).SameComp e.u e.v ∧
      (∀ g∈(D.toForest clean.1).edges,g.eid≠j.val) ∧
      Num.Fits h L e.cost ∧ RatFits h L P q ∧ RatFits h L P (⌊q⌋:ℚ) ∧
      RatFits h L P e.availFwd ∧ RatFits h L P e.availBwd ∧
      (⌊q⌋=⌊f j⌋ ∧ ⌈q⌉=⌈f j⌉) := by
    have hEnd := roundRelink_endpoints hFrac hQ hLoq hHiq
    have hfit : RatFits h L P (⌊q⌋:ℚ) ∧ RatFits h L P ((⌈q⌉:ℚ)-q) ∧ RatFits h L P (q-(⌊q⌋:ℚ)) :=
      hFitAvail hQ
    obtain ⟨hf,haf,hab⟩ := hfit
    exact ⟨hNC.symm ▸ hTail,hNC.symm ▸ hHead,hDisc hQ,fun g hg => Nat.ne_of_lt (hWeak g hg).2.2.2.2,
      hFitCost,hFitQ,hf,by simpa only [roundingEdge,hEnd.2] using haf,
      by simpa only [roundingEdge,hEnd.1] using hab,hEnd⟩
  have hAt : RatAt raw₁.mem fp h L P q := by
    have he : clean.2.1 j=q := hValue
    exact he ▸ hTable₁ j
  obtain ⟨out,raw₂,c₂,y,hRun₂,hRep₂,hLo₂,hHi₂,hZero₂,hFrame₂,hFoot₂,hC₂⟩ :=
    roundRelink_runs D hD rate allocation R himpl hB.integer_spec hB.availability_spec hB.packLink_at hB.pack_spec hB.link_at
      (fun b a heap => (hAlloc b 0 0 a heap).2.2.2) I j q (f j) b ac fp one out₁ clean.1 x₁ raw₁.mem raw₁.pos ω
      hW₂ hP (hb.trans hLo₁) (hAC.trans (by omega)) hFp (hOneEnd.trans (by omega))
      (hCost.frozen hFrame₁ hAC) hAt (hOne.frozen hFrame₁ hOneEnd)
      hInvC hFitC hRel hRead₁ hFoot₁ hZero₁ hSpace₂
  let mid : State := ⟨raw₁.mem,Function.update parent.regs 16 out₁,raw₁.pos⟩
  have hCall₁ := round_returning_call (dst:=16) hB.repair_at hArgs₁ hRun₁
  have hArgs₂ : evalArgs w mid [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 16]=
      some [b,j.val,edge.tail,edge.head,ac,fp,L,P,one,out₁] := rfl
  have hCall₂ := round_returning_call (dst:=16) hB.relink_at hArgs₂ hRun₂
  let final : State := ⟨raw₂.mem,Function.update mid.regs 16 out,raw₂.pos⟩
  have hRet : Runs w p ω (.ret (.reg 16)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  obtain ⟨hDf,hArr,hCuts⟩ := roundEdgeStep_connected D I f model j hFrac hRoots
  have hCutEq : next.counts.cutOps-model.counts.cutOps=r := by
    change next.counts.cutOps=clean.2.2.1.cutOps at hCuts
    change clean.2.2.1.cutOps+(D.toForest clean.1).edges.length =
      model.counts.cutOps+(D.toForest model.df).edges.length at hCount
    omega
  have hTable₂ : RoundFlowAt I raw₂.mem base h L P next.flowArr := by
    change next.flowArr=clean.2.1 at hArr
    rw [hArr]
    intro i
    have hi := Nat.mul_le_mul_right L (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    exact (hTable₁ i).frozen hFrame₂ (by omega)
  refine ⟨out,final,10+c₁+1+(10+c₂+1+2+1)+1,y,?_,hDf ▸ hRep₂,hTable₂,
    hLo₁.trans hLo₂,?_,hZero₂,?_,hFoot₂,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall₁,runs_seq_iff.mpr (Or.inr
      ⟨final,_,_,hCall₂,hRet,rfl⟩),rfl⟩)
  · change out≤heap+roundRepairRelinkCharge A L (next.counts.cutOps-model.counts.cutOps)
    rw [hCutEq,roundRepairRelinkCharge,roundRepairRelinkSpace]
    omega
  · intro z hz
    exact (hFrame₂ z (by omega)).trans (hFrame₁ z hz)
  · rw [hModelN] at hC₁
    change c₂+R.phi b y raw₂.mem≤rate (D.toForest clean.1).n+336*L+570+R.phi b x₁ raw₁.mem at hC₂
    rw [hNC] at hC₂
    let C := roundCleanupCharge (rate I.n+19*L+80) (rate I.n+17*L+115) r
    change c₁+R.phi b x₁ raw₁.mem≤2*rate I.n+132*L+275+C+R.phi b x mem at hC₁
    change _+R.phi b y raw₂.mem≤3*rate I.n+468*L+875+
      roundCleanupCharge (rate I.n+19*L+80) (rate I.n+17*L+115) (next.counts.cutOps-model.counts.cutOps)+R.phi b x mem
    rw [hCutEq]
    change _+R.phi b y raw₂.mem≤3*rate I.n+468*L+875+C+R.phi b x mem
    omega

end MinCostFlow.IPM.Machine
