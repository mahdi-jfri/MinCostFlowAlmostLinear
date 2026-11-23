module

public import MinCostFlow.IPM.Machine.RoundFractional
public import MinCostFlow.IPM.Machine.RoundRelinkPrecision
import MinCostFlow.IPM.Machine.PrecisionProducts
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# A verified Kang–Payor rounding edge

An exact integer coordinate needs no work. For a fractional one,
the deterministic root and cost tests select the forest update.
The charge is a fixed per-edge term plus an amount per actual cut.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Dispatch the fractional branch only after the exact integer test. -/
def roundEdgeBody (B : RoundProcedures) (fractional : ℕ) : Stmt :=
  .call 12 B.integer [.reg 5,.reg 6,.reg 7] ;;
  .cond (.reg 12) (.ret (.reg 11))
    (.call 13 fractional [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,
      .reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11] ;;
     .ret (.reg 13))

/-- Both branches are deterministic. -/
theorem roundEdge_noRand (B : RoundProcedures) (fractional : ℕ) :
    (roundEdgeBody B fractional).NoRand := by
  simp [roundEdgeBody,Stmt.NoRand]

/-- The IPM precision meets every fixed-point range check made by a
fractional rounding step. -/
theorem roundEdge_numeric {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {M : ℚ} (U : ℕ) (hm : 0<I.m) (hU : 1≤U)
    (hn : NumbersBounded I (U:ℝ)) (hf : ∀ j,|(f j:ℝ)|≤U)
    (model : RoundState D I) (j : Fin I.m)
    (hModel : LoopInv D I f (ipmPrecision I.m U) M j.val model)
    (hFP : ∀ j,IsFixedPoint (ipmPrecision I.m U) (f j))
    (hFrac : isIntRat (f j)=false) :
    RoundEdgeNumeric D I f j model 4 (ipmLimbs I.m U) (ipmPrecision I.m U) := by
  have hi := hModel
  obtain ⟨hInv,_,hStrict,_,_,_,_,_,_,hLink,hCuts,_,_,_,_,hBits,_,_⟩ := hi
  have hFit := roundForest_fits U hm hU hn hf (fun e he => ⟨(hStrict e he).1.1,(hBits hFP).1 e he⟩)
  have hCap := round_capacity_range I.m U hm hU
  have hC := (hn.2 j).2.2
  obtain ⟨hFloor,hBwd,hFwd⟩ := round_availability_fits I.m U (f j) hm hU (hFP j) (hf j) hFrac
  refine ⟨hFit,(fits_integer_at_chosen_precision I.m U (I.edge j).cost (by linarith only [hC,hCap])).1,
    ratFits_chosen_precision I.m U _ (hFP j) (by linarith only [hf j,hCap]),hFloor,hBwd,hFwd,?_⟩
  intro hConn
  obtain ⟨_,hPush,hClean,_,hVal,hAvail⟩ :=
    roundRepairRelink_numeric hD U hm hU hn hf model j (roundBackward D model.df j) hModel hFP hFrac hConn
  have hSize : (D.toForest model.df).edges.length≤I.m := by have hj := j.isLt; omega
  exact ⟨roundPathSum_fits hD U hm hU hn hInv hConn (fun e he => (hStrict e he).1.1) hSize,
    hPush,hClean,hVal,hAvail⟩

set_option maxHeartbeats 500000 in
/-- One pass step agrees with `roundEdgeStep` for integral and
fractional input. Its separate forest credit persists across calls. -/
theorem roundEdge_runs {w h L P A fractional connected repairRelink : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hFracAt : p.procs[fractional]?=some (roundFractionalBody B connected))
    (hConnect : p.procs[connected]?=some (roundConnectedBody B repairRelink))
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℚ) (j : Fin I.m) (model : RoundState D I) (M : ℚ)
    (hModel : LoopInv D I f P M j.val model) (hFP : ∀ i,IsFixedPoint P (f i))
    (b ac one base heap : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hL : 0<L) (hP : h∣P) (hN : I.n≤2^w)
    (hw : ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,I.m+1,heap],z<2^w)
    (hCost : RatAt mem ac h L 0 (I.edge j).cost) (hOne : RatAt mem one h L P 1)
    (hFlow : RoundFlowAt I mem base h L P model.flowArr)
    (hTable : base+I.m*L≤b) (hAC : ac+L≤base) (hOneEnd : one+L≤base) (hb : b≤heap)
    (hRep : R.rep b model.df x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hZero : ZeroFrom mem heap) (hNumeric : isIntRat (f j)=false → RoundEdgeNumeric D I f j model h L P)
    (hSpace : heap+roundEdgeSpace A L (D.toForest model.df).edges.length<2^w) :
    let next := roundEdgeStep D I f model j
    let r := next.counts.cutOps-model.counts.cutOps
    ∃ out final cost y,
      Runs w p ω (roundEdgeBody B fractional)
        (startState [b,j.val,(I.edge j).tail,(I.edge j).head,ac,base+j.val*L,L,P,one,base,I.m+1,heap] mem pos)
        (.returned out) final cost ∧
      R.rep b next.df y final.mem ∧ RoundFlowAt I final.mem base h L P next.flowArr ∧
      heap≤out ∧ out≤heap+roundEdgeSpace A L r ∧ ZeroFrom final.mem out ∧
      (∀ z<base,final.mem z=mem z) ∧ (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤roundEdgeCost (rate I.n) L r+19*L+70+R.phi b x mem := by
  dsimp only
  let fp := base+j.val*L
  let args := [b,j.val,(I.edge j).tail,(I.edge j).head,ac,fp,L,P,one,base,I.m+1,heap]
  let parent := startState args mem pos
  have hw₀ : ∀ z∈[fp,L,P],z<2^w := by
    intro z hz
    have hW (i : Fin 12) : args[i.val]'i.isLt<2^w := hw _ (List.getElem_mem (l:=args) i.isLt)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact hW 5
    · exact hW 6
    · exact hW 7
  have hFp : fp+L≤heap := by
    have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hh
    dsimp [fp]
    omega
  have hHeapW : heap<2^w := hw _ (List.getElem_mem (l:=args) (n:=11) (by change 11<12; decide))
  have hRead : RatAt mem fp h L P (f j) := (hModel.2.2.2.2.1 j le_rfl).2 ▸ hFlow j
  have hPre : (Num.isIntegerContract w h).pre [fp,L,P] mem :=
    ⟨fp,L,P,rfl,hP,by omega,hRead.1⟩
  have hArgs : evalArgs w parent [.reg 5,.reg 6,.reg 7]=some [fp,L,P] := rfl
  obtain ⟨mid,c₁,bit,hCall₁,hOut₁,hBit,hReg,hC₁⟩ :=
    runs_call_of_meetsContract (r:=12) hB.integer_spec hArgs hw₀ hPre ω
  obtain ⟨hMem,hVal⟩ := hOut₁
  have hMid : mid.mem=mem := hMem
  change bit=(if (2:ℤ)^P∣Num.intVal mem fp h L then 1 else 0) at hVal
  simp only [hRead.isInt_iff] at hVal
  change c₁≤3+(19*L+40)+1 at hC₁
  by_cases hInt : isIntRat (f j)=true
  · have hRegInt : mid.regs 12=1 := hBit.trans (by simpa [hInt] using hVal)
    have hRegEnd : mid.regs 11=heap := hReg 11 (by decide)
    have hRet : Runs w p ω (.ret (.reg 11)) mid (.returned heap) mid 2 :=
      runs_ret_iff.mpr ⟨heap,congrArg some hRegEnd,rfl,rfl,rfl⟩
    have hCond (alt : Stmt) : Runs w p ω (.cond (.reg 12) (.ret (.reg 11)) alt)
        mid (.returned heap) mid 4 :=
      runs_cond_iff.mpr ⟨1,2,congrArg some hRegInt,hRet,rfl⟩
    have hRep' : R.rep b (roundEdgeStep D I f model j).df x mid.mem := by
      simpa only [roundEdgeStep,hInt,ite_true,hMid] using hRep
    have hFlow' : RoundFlowAt I mid.mem base h L P (roundEdgeStep D I f model j).flowArr := by
      simpa only [roundEdgeStep,hInt,ite_true,hMid] using hFlow
    refine ⟨heap,mid,c₁+5,x,?_,hRep',hFlow',le_rfl,by omega,hMid ▸ hZero,
      fun z _ => congrFun hMid z,hFoot,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨mid,c₁,4,hCall₁,hCond _,rfl⟩)
    · rw [hMid]
      omega
  · have hFrac := Bool.eq_false_iff.mpr hInt
    have hRegInt : mid.regs 12=0 := hBit.trans (by simpa [hInt] using hVal)
    obtain ⟨out,raw,c₂,y,hRun₂,hRep₂,hFlow₂,hLo₂,hHi₂,hZ₂,hM₂,hF₂,hC₂⟩ :=
      roundFractional_runs D hD rate allocation R himpl B hB hConnect hRL hAlloc I hI f j model M hModel hFP
        hFrac b ac one base heap x mid.mem mid.pos ω hL hP hN hw (hMid ▸ hCost) (hMid ▸ hOne)
        (hMid ▸ hFlow) hTable hAC hOneEnd hb (hMid ▸ hRep) hFoot (hMid ▸ hZero) (hNumeric hFrac) hSpace
    let regs : List Expr := [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11]
    have hArg₂ : evalArgs w mid regs=some args := by
      have hReg' (i : ℕ) (hi : i<12) : mid.regs i=args.getD i 0 := hReg i (by omega)
      have r₀ : mid.regs 0=b := hReg' 0 (by decide)
      have r₁ : mid.regs 1=j.val := hReg' 1 (by decide)
      have r₂ : mid.regs 2=(I.edge j).tail := hReg' 2 (by decide)
      have r₃ : mid.regs 3=(I.edge j).head := hReg' 3 (by decide)
      have r₄ : mid.regs 4=ac := hReg' 4 (by decide)
      have r₅ : mid.regs 5=fp := hReg' 5 (by decide)
      have r₆ : mid.regs 6=L := hReg' 6 (by decide)
      have r₇ : mid.regs 7=P := hReg' 7 (by decide)
      have r₈ : mid.regs 8=one := hReg' 8 (by decide)
      have r₉ : mid.regs 9=base := hReg' 9 (by decide)
      have r₁₀ : mid.regs 10=I.m+1 := hReg' 10 (by decide)
      have r₁₁ : mid.regs 11=heap := hReg' 11 (by decide)
      simp [regs,args,evalArgs,Expr.eval,r₀,r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉,r₁₀,r₁₁]
    let final : State := ⟨raw.mem,Function.update mid.regs 13 out,raw.pos⟩
    have hCall₂ := round_returning_call (dst:=13) hFracAt hArg₂ hRun₂
    have hRet : Runs w p ω (.ret (.reg 13)) final (.returned out) final 2 :=
      runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
    have hB₂ : Runs w p ω (.call 13 fractional regs ;; .ret (.reg 13))
        mid (.returned out) final (12+c₂+1+2+1) :=
      runs_seq_iff.mpr (Or.inr ⟨final,_,_,hCall₂,hRet,rfl⟩)
    have hCond : Runs w p ω (.cond (.reg 12) (.ret (.reg 11)) (.call 13 fractional regs ;; .ret (.reg 13)))
        mid (.returned out) final (1+(12+c₂+1+2+1)+1) :=
      runs_cond_iff.mpr ⟨0,_,congrArg some hRegInt,hB₂,rfl⟩
    refine ⟨out,final,c₁+(1+(12+c₂+1+2+1)+1)+1,y,?_,hRep₂,hFlow₂,hLo₂,hHi₂,hZ₂,
      fun z hz => (hM₂ z hz).trans (congrFun hMid z),hF₂,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall₁,hCond,rfl⟩)
    · change c₂+R.phi b y raw.mem≤_ at hC₂
      rw [hMid] at hC₂
      change _+R.phi b y raw.mem≤_
      omega

/-- The IPM precision meets every fixed-point range check made by a
fractional rounding step. -/
theorem roundEdge_numeric_widened {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {M : ℚ} (U k : ℕ) (hm : 0<I.m) (hU : 1≤U)
    (hn : NumbersBounded I (U:ℝ)) (hf : ∀ j,|(f j:ℝ)|≤U)
    (model : RoundState D I) (j : Fin I.m)
    (hModel : LoopInv D I f (ipmQualityPrecision I.m U k) M j.val model)
    (hFP : ∀ j,IsFixedPoint (ipmQualityPrecision I.m U k) (f j))
    (hFrac : isIntRat (f j)=false) :
    RoundEdgeNumeric D I f j model 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) := by
  have hi := hModel
  obtain ⟨hInv,_,hStrict,_,_,_,_,_,_,hLink,hCuts,_,_,_,_,hBits,_,_⟩ := hi
  have hFit := roundForest_fits_widened U k hm hU hn hf (fun e he => ⟨(hStrict e he).1.1,(hBits hFP).1 e he⟩)
  have hCap := round_capacity_range_widened I.m U k hm hU
  have hC := (hn.2 j).2.2
  obtain ⟨hFloor,hBwd,hFwd⟩ := round_availability_fits_widened I.m U k (f j) hm hU (hFP j) (hf j) hFrac
  refine ⟨hFit,(fits_integer_at_quality_precision I.m U k (I.edge j).cost (by linarith only [hC,hCap])).1,
    ratFits_widened_precision I.m U k _ (hFP j) (by linarith only [hf j,hCap]),hFloor,hBwd,hFwd,?_⟩
  intro hConn
  obtain ⟨_,hPush,hClean,_,hVal,hAvail⟩ :=
    roundRepairRelink_numeric_widened hD U k hm hU hn hf model j (roundBackward D model.df j) hModel hFP hFrac hConn
  have hSize : (D.toForest model.df).edges.length≤I.m := by have hj := j.isLt; omega
  exact ⟨roundPathSum_fits_widened hD U k hm hU hn hInv hConn (fun e he => (hStrict e he).1.1) hSize,
    hPush,hClean,hVal,hAvail⟩


end MinCostFlow.IPM.Machine
