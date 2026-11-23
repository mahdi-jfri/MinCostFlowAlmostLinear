module

public import MinCostFlow.IPM.Machine.RoundFractionalPrep
import WordRAM.Tactic

/-!
# Processing a fractional rounding edge

Different roots identify an edge that can be added to the forest.
Equal roots identify the unique path closing a cycle. In both
cases the exact forest and flow agree with the rounding model.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- The two preserved availability addresses within the scratch area. -/
def roundPreparedFwd : Expr := .bin .sub (.reg 12) (.reg 6)

/-- The backward availability precedes the final two blocks. -/
def roundPreparedBwd : Expr := .bin .sub (.reg 12) (.bin .mul (.const 3) (.reg 6))

/-- Parameters of the connected branch after the root comparison. -/
def roundPreparedCycleArgs : List Expr :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,
    roundPreparedFwd,roundPreparedBwd,.reg 15]

/-- Parameters of the disconnected branch. -/
def roundPreparedLinkArgs : List Expr :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,roundPreparedFwd,roundPreparedBwd,.reg 6,.reg 15]

/-- Process the input fractional edge using the two root names. -/
def roundFractionalBody (B : RoundProcedures) (connected : ℕ) : Stmt :=
  roundFractionalPrepBody B ;;
  .cond (.bin .eq (.reg 14) (.reg 16))
    (.call 17 connected roundPreparedCycleArgs ;; .ret (.reg 17))
    (.call 17 B.packLink roundPreparedLinkArgs ;; .ret (.reg 17))

/-- The two branches use only deterministic calls. -/
theorem roundFractional_noRand (B : RoundProcedures) (connected : ℕ) :
    (roundFractionalBody B connected).NoRand := by
  simp [roundFractionalBody,roundFractionalPrepBody,Stmt.NoRand]

/-- Space for a rounding edge, including one cleanup query and
one additional charge per edge candidate that could get cut. -/
def roundEdgeSpace (A L r : ℕ) : ℕ :=
  7*A+26*L+25+roundCleanupCharge (A+4+2*L) A r

/-- The charge for a rounding edge includes constant many forest
calls and the cleanup charge proportional to its actual cuts. -/
def roundEdgeCost (rate L r : ℕ) : ℕ :=
  6*rate+800*L+1500+roundCleanupCharge (rate+19*L+80) (rate+17*L+115) r

/-- The fixed-point checks supplied by the selected precision for
one edge. The cycle bounds are needed only in the connected branch. -/
def RoundEdgeNumeric (D : DynForest) (I : Instance) (f : Fin I.m → ℚ)
    (j : Fin I.m) (s : RoundState D I) (h L P : ℕ) : Prop :=
  ForestFits D h L P s.df ∧ Num.Fits h L (I.edge j).cost ∧ RatFits h L P (f j) ∧
  RatFits h L P (⌊f j⌋:ℚ) ∧ RatFits h L P (roundAvail (f j) true) ∧ RatFits h L P (roundAvail (f j) false) ∧
  ((D.toForest s.df).SameComp (I.edge j).tail (I.edge j).head →
    let back := roundBackward D s.df j
    let clean := roundCycleClean D I (f j) s j back
    let q := roundCycleValue D s.df j (f j) back
    let δ := roundCycleDelta D s.df j (f j) back
    Num.Fits h L (D.pathSum s.df (I.edge j).tail (I.edge j).head) ∧
    ForestFits D h L P (D.pathAdd s.df (roundFrom (I.edge j) back) (roundTo (I.edge j) back) δ) ∧
    ForestFits D h L P clean.1 ∧ RatFits h L P q ∧
    (isIntRat q=false → RatFits h L P (⌊q⌋:ℚ) ∧
      RatFits h L P ((⌈q⌉:ℚ)-q) ∧ RatFits h L P (q-(⌊q⌋:ℚ))))

set_option maxHeartbeats 600000 in
/-- The full fractional step verifies both branches of the model
and charges space and time to their actual number of cuts. -/
theorem roundFractional_runs {w h L P A connected repairRelink : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hConnect : p.procs[connected]?=some (roundConnectedBody B repairRelink))
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℚ) (j : Fin I.m) (model : RoundState D I) (M : ℚ)
    (hModel : LoopInv D I f P M j.val model) (hFP : ∀ i,IsFixedPoint P (f i))
    (hFrac : isIntRat (f j)=false)
    (b ac one base heap : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hL : 0<L) (hP : h∣P) (hN : I.n≤2^w)
    (hw : ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,I.m+1,heap],z<2^w)
    (hCost : RatAt mem ac h L 0 (I.edge j).cost) (hOne : RatAt mem one h L P 1)
    (hFlow : RoundFlowAt I mem base h L P model.flowArr)
    (hTable : base+I.m*L≤b) (hAC : ac+L≤base) (hOneEnd : one+L≤base) (hb : b≤heap)
    (hRep : R.rep b model.df x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hZero : ZeroFrom mem heap) (hNumeric : RoundEdgeNumeric D I f j model h L P)
    (hSpace : heap+roundEdgeSpace A L (D.toForest model.df).edges.length<2^w) :
    let next := roundEdgeStep D I f model j
    let r := next.counts.cutOps-model.counts.cutOps
    ∃ out final cost y,
      Runs w p ω (roundFractionalBody B connected)
        (startState [b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,I.m+1,heap] mem pos)
        (.returned out) final cost ∧
      R.rep b next.df y final.mem ∧ RoundFlowAt I final.mem base h L P next.flowArr ∧
      heap≤out ∧ out≤heap+roundEdgeSpace A L r ∧ ZeroFrom final.mem out ∧
      (∀ z<base,final.mem z=mem z) ∧ (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤roundEdgeCost (rate I.n) L r+R.phi b x mem := by
  dsimp only
  let e := I.edge j
  let fp := base+j.val*L
  let args := [b,j.val,e.tail,e.head,ac,fp,L,P,one,base,I.m+1,heap]
  let parent := startState args mem pos
  let av := heap+7*L+1
  let af := heap+6*L+1
  let ab := heap+4*L+1
  let next := roundEdgeStep D I f model j
  let r := next.counts.cutOps-model.counts.cutOps
  have hRoom : heap+2*A+7*L+3<2^w := by unfold roundEdgeSpace at hSpace; omega
  have hEnd : fp+L≤b := by
    have hj := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hj
    dsimp only [fp]
    omega
  have heU : e.tail<(D.toForest model.df).n := hModel.2.1.symm ▸ (hI.1 e (List.getElem_mem j.isLt)).1
  have heV : e.head<(D.toForest model.df).n := hModel.2.1.symm ▸ (hI.1 e (List.getElem_mem j.isLt)).2
  have hCoord : model.flowArr j=f j := (hModel.2.2.2.2.1 j le_rfl).2
  obtain ⟨hFit,hCostFits,hQFits,hFloor,hBwd,hFwd,hCycle⟩ := hNumeric
  obtain ⟨midHeap,mid,c₁,x₁,hRun₁,hRegs,hAv,hHeap,hRootU,hRootV,hRep₁,hLo₁,hHi₁,hZero₁,hBelow₁,
    hFoot₁,hFresh₁,hAf,hAb,hC₁⟩ :=
    roundFractionalPrep_runs D hD rate allocation R himpl B hB (fun b v heap => (hAlloc b v 0 0 heap).1)
      I j (f j) b ac fp one base heap model.df x mem pos ω hw hb (hEnd.trans hb) (by omega)
      (hCoord ▸ hFlow j) hOne hFrac hFloor hBwd hFwd hModel.1 hFit heU heV
      (hModel.2.1.symm ▸ hN) hRep hFoot hZero hRoom
  change mid.regs 12=av at hAv
  change mid.regs 14=D.findRoot model.df e.tail at hRootU
  change mid.regs 16=D.findRoot model.df e.head at hRootV
  rw [hModel.2.1] at hC₁
  have hAF : af+L≤midHeap := by
    have he : af+L=av := by dsimp [af,av]; omega
    exact he ▸ hLo₁
  have hAB : ab+L≤midHeap := by
    have hh : ab+L≤av := by dsimp only [ab,av]; omega
    exact hh.trans hLo₁
  have haL : av-L=af := by dsimp [av,af]; omega
  have haB : av-3*L=ab := by dsimp [av,ab]; omega
  have hb₁ : b≤midHeap := by
    have ha : heap≤av := by dsimp [av]; omega
    exact hb.trans (ha.trans hLo₁)
  have hBelow (i : Fin I.m) : base+i.val*L+L≤b := by
    have hi := Nat.mul_le_mul_right L (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hi
    omega
  have hFlow₁ : RoundFlowAt I mid.mem base h L P model.flowArr := fun i =>
    (hFlow i).frozen hBelow₁ (hBelow i)
  have hwAt (i : Fin 12) : args[i.val]'i.isLt<2^w := hw _ (List.getElem_mem (l:=args) i.isLt)
  have hMidFit : midHeap<2^w := hHi₁.trans_lt hRoom
  have hafW : af<2^w := by omega
  have habW : ab<2^w := by omega
  have hAvW : av<2^w := hLo₁.trans_lt hMidFit
  have hMulW : 3*L<2^w := by omega
  have hThree : 3<2^w := by omega
  have huW : D.findRoot model.df e.tail<2^w :=
    ((hD.2.2.1 model.df e.tail hModel.1 heU).1.trans_eq hModel.2.1).trans_le hN
  have hvW : D.findRoot model.df e.head<2^w :=
    ((hD.2.2.1 model.df e.head hModel.1 heV).1.trans_eq hModel.2.1).trans_le hN
  have hR (i : ℕ) (hi : i<12) : mid.regs i=args.getD i 0 := hRegs i hi
  have r₀ : mid.regs 0=b := hR 0 (by decide)
  have r₁ : mid.regs 1=j.val := hR 1 (by decide)
  have r₂ : mid.regs 2=e.tail := hR 2 (by decide)
  have r₃ : mid.regs 3=e.head := hR 3 (by decide)
  have r₄ : mid.regs 4=ac := hR 4 (by decide)
  have r₅ : mid.regs 5=fp := hR 5 (by decide)
  have r₆ : mid.regs 6=L := hR 6 (by decide)
  have r₇ : mid.regs 7=P := hR 7 (by decide)
  have r₈ : mid.regs 8=one := hR 8 (by decide)
  have r₉ : mid.regs 9=base := hR 9 (by decide)
  have r₁₀ : mid.regs 10=I.m+1 := hR 10 (by decide)
  have hEvalF : roundPreparedFwd.eval w mid=some af := by
    rw [← haL]
    unfold roundPreparedFwd
    eval_expr
  have hEvalB : roundPreparedBwd.eval w mid=some ab := by
    rw [← haB]
    unfold roundPreparedBwd
    eval_expr
  let guard : Expr := .bin .eq (.reg 14) (.reg 16)
  have hCost₁ := hCost.frozen hBelow₁ (hAC.trans (by omega))
  have hOne₁ := hOne.frozen hBelow₁ (hOneEnd.trans (by omega))
  by_cases hRoot : D.findRoot model.df e.tail=D.findRoot model.df e.head
  · have hConn := ((hD.2.2.1 model.df e.head hModel.1 heV).2 e.tail heU).mp hRoot
    obtain ⟨hSum,hPushed,hClean,hQ,hAvSafe⟩ := hCycle hConn
    have hSpace₂ : midHeap+A+L+roundRepairRelinkCharge A L (D.toForest model.df).edges.length<2^w := by
      unfold roundEdgeSpace at hSpace
      unfold roundRepairRelinkCharge roundRepairRelinkSpace
      omega
    have hw₂ : ∀ z∈[b,j.val,e.tail,e.head,ac,fp,L,P,one,base,I.m+1,af,ab,midHeap],z<2^w := by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwAt 0
      · exact hwAt 1
      · exact hwAt 2
      · exact hwAt 3
      · exact hwAt 4
      · exact hwAt 5
      · exact hwAt 6
      · exact hwAt 7
      · exact hwAt 8
      · exact hwAt 9
      · exact hwAt 10
      · exact hafW
      · exact habW
      · exact hMidFit
    have hFrame : ∀ z,R.foot b x₁ z → (z<af ∨ af+L≤z) ∧ (z<ab ∨ ab+L≤z) := by
      intro z hz
      rcases hFresh₁ z hz with hz' | hz'
      · exact ⟨Or.inl (by dsimp [af]; omega),Or.inl (by dsimp [ab]; omega)⟩
      · exact ⟨Or.inr (by dsimp [af,av] at *; omega),Or.inr (by dsimp [ab,av] at *; omega)⟩
    obtain ⟨out,raw,c₂,y,hRun₂,hRep₂,hFlow₂,hLo₂,hHi₂,hZero₂,hMem₂,hFoot₂,hC₂⟩ :=
      roundConnected_runs D hD rate allocation R himpl B hB hRL (fun b u v a heap => (hAlloc b u v a heap).2)
        I hI f j model M hModel hFP hFrac hRoot b ac af ab one base midHeap x₁ mid.mem mid.pos ω hL hP hN
        hw₂ hCost₁ hOne₁ hFlow₁ hAf hAb hTable hAC hOneEnd hAF hAB (by dsimp [af]; omega)
        (by dsimp [ab]; omega) hb₁ hRep₁ hFoot₁ hFrame hZero₁ hSum ⟨hFit,hPushed,hClean,hCostFits,hQ,hAvSafe⟩ hSpace₂
    have hArgs₂ : evalArgs w mid roundPreparedCycleArgs=some [b,j.val,e.tail,e.head,ac,fp,L,P,one,base,I.m+1,af,ab,midHeap] := by
      simp [roundPreparedCycleArgs,evalArgs,Expr.eval,r₀,r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉,r₁₀,hEvalF,hEvalB,hHeap]
    have hCall₂ := round_returning_call (dst:=17) hConnect hArgs₂ hRun₂
    let final : State := ⟨raw.mem,Function.update mid.regs 17 out,raw.pos⟩
    have hRet : Runs w p ω (.ret (.reg 17)) final (.returned out) final 2 :=
      runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
    have hGuard : guard.eval w mid=some 1 :=
      Expr.eval_eq_true (congrArg some hRootU) (congrArg some hRootV) hRoot (by omega)
    have hBranch : Runs w p ω (.call 17 connected roundPreparedCycleArgs ;; .ret (.reg 17))
        mid (.returned out) final (24+c₂) :=
      runs_seq_iff.mpr (Or.inr ⟨final,20+c₂+1,2,hCall₂,hRet,by omega⟩)
    have hCond (alt : Stmt) : Runs w p ω (.cond guard
        (.call 17 connected roundPreparedCycleArgs ;; .ret (.reg 17)) alt)
        mid (.returned out) final (28+c₂) :=
      runs_cond_iff.mpr ⟨1,24+c₂,hGuard,hBranch,by change 28+c₂=3+(24+c₂)+1; omega⟩
    refine ⟨out,final,c₁+(28+c₂)+1,y,?_,hRep₂,hFlow₂,by omega,?_,hZero₂,?_,hFoot₂,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hRun₁,hCond _,rfl⟩)
    · change out≤midHeap+A+L+roundRepairRelinkCharge A L r at hHi₂
      change out≤heap+roundEdgeSpace A L r
      unfold roundEdgeSpace roundRepairRelinkCharge roundRepairRelinkSpace at *
      omega
    · intro z hz
      exact (hMem₂ z hz).trans (hBelow₁ z (by omega))
    · change c₂+R.phi b y raw.mem≤4*rate I.n+509*L+1000+
        roundCleanupCharge (rate I.n+19*L+80) (rate I.n+17*L+115) r+R.phi b x₁ mid.mem at hC₂
      change _+R.phi b y raw.mem≤roundEdgeCost (rate I.n) L r+R.phi b x mem
      unfold roundEdgeCost
      omega
  · let fe := roundingEdge I j (f j) (f j)
    have hDis : ¬(D.toForest model.df).SameComp e.tail e.head :=
      fun hc => hRoot (((hD.2.2.1 model.df e.head hModel.1 heV).2 e.tail heU).mpr hc)
    have hFresh : ∀ g∈(D.toForest model.df).edges,g.eid≠fe.eid :=
      fun g hg => Nat.ne_of_lt (hModel.2.2.1 g hg).2
    have hw₂ : ∀ z∈[b,fe.eid,fe.u,fe.v,ac,fp,af,ab,L,midHeap],z<2^w := by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwAt 0
      · exact hwAt 1
      · exact hwAt 2
      · exact hwAt 3
      · exact hwAt 4
      · exact hwAt 5
      · exact hafW
      · exact habW
      · exact hwAt 6
      · exact hMidFit
    have hAlloc₂ := (hAlloc b 0 0 midHeap (midHeap+3+4*L)).2.2.2.2.1
    have hs₂ : midHeap+3+4*L+allocation 1 [b,midHeap,midHeap+3+4*L]<2^w := by
      unfold roundEdgeSpace at hSpace
      omega
    have hf₁ : RatAt mid.mem fp h L P (f j) := by
      rw [← hCoord]
      exact hFlow₁ j
    obtain ⟨out,raw,c₂,y,hRun₂,hRep₂,hLo₂,hHi₂,hZero₂,hMem₂,hFoot₂,hC₂⟩ :=
      roundPackLink_runs D hD rate allocation R himpl hB.pack_spec hB.link_at fe b ac fp af ab midHeap
        model.df x₁ mid.mem mid.pos ω hw₂ ⟨by omega,hEnd.trans hb₁,hAF,hAB⟩ hCost₁ hf₁ hAf hAb
        hModel.1 hFit ⟨hCostFits,hQFits,hFwd,hBwd⟩ heU heV hDis hFresh hRep₁ hFoot₁ hZero₁ hb₁ hs₂
    have hArgs₂ : evalArgs w mid roundPreparedLinkArgs=some [b,fe.eid,fe.u,fe.v,ac,fp,af,ab,L,midHeap] := by
      simp [roundPreparedLinkArgs,evalArgs,Expr.eval,r₀,r₁,r₂,r₃,r₄,r₅,r₆,hEvalF,hEvalB,hHeap,fe,roundingEdge,e]
    have hCall₂ := round_returning_call (dst:=17) hB.packLink_at hArgs₂ hRun₂
    let final : State := ⟨raw.mem,Function.update mid.regs 17 out,raw.pos⟩
    have hRet : Runs w p ω (.ret (.reg 17)) final (.returned out) final 2 :=
      runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
    have hGuard : guard.eval w mid=some 0 :=
      Expr.eval_eq_false (congrArg some hRootU) (congrArg some hRootV) hRoot (by omega)
    have hBranch : Runs w p ω (.call 17 B.packLink roundPreparedLinkArgs ;; .ret (.reg 17))
        mid (.returned out) final (16+c₂+1+2+1) :=
      runs_seq_iff.mpr (Or.inr ⟨final,16+c₂+1,2,hCall₂,hRet,rfl⟩)
    have hCond (alt : Stmt) : Runs w p ω (.cond guard alt
        (.call 17 B.packLink roundPreparedLinkArgs ;; .ret (.reg 17)))
        mid (.returned out) final (24+c₂) :=
      runs_cond_iff.mpr ⟨0,16+c₂+1+2+1,hGuard,hBranch,by change 24+c₂=3+(16+c₂+1+2+1)+1; omega⟩
    obtain ⟨hState,hTableOut,hCounts⟩ := roundEdgeStep_disconnected D I f model j hFrac hRoot
    have hC : r=0 := by dsimp [r,next]; omega
    have hRepFinal : R.rep b next.df y final.mem := hState ▸ hRep₂
    have hFlowFinal : RoundFlowAt I final.mem base h L P next.flowArr := by
      change next.flowArr=model.flowArr at hTableOut
      rw [hTableOut]
      exact fun i => (hFlow₁ i).frozen hMem₂ (hBelow i)
    refine ⟨out,final,c₁+(24+c₂)+1,y,?_,hRepFinal,hFlowFinal,by omega,?_,hZero₂,?_,hFoot₂,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hRun₁,hCond _,rfl⟩)
    · change out≤heap+roundEdgeSpace A L r
      rw [hC,roundEdgeSpace]
      omega
    · intro z hz
      exact (hMem₂ z (by omega)).trans (hBelow₁ z (by omega))
    · rw [hModel.2.1] at hC₂
      change _+R.phi b y raw.mem≤roundEdgeCost (rate I.n) L r+R.phi b x mem
      unfold roundEdgeCost
      omega

end MinCostFlow.IPM.Machine
