module

public import MinCostFlow.IPM.Machine.RoundLoop
import WordRAM.Tactic

/-!
# Initializing the forest and rounding the fixed-point flow

Lemma 4.1 (page 13) calls the deterministic Kang–Payor rounder.
The machine initializes an empty forest after the working flow,
then rounds the table in place with the proved single-pass scan.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [n,m,graph,cost,flow,L,P,one,heap], initialize and round in place. -/
def roundMachineBody (init loop : ℕ) : Stmt :=
  .call 9 init [.reg 0,.reg 5,.reg 6,.reg 8] ;;
  .call 9 loop [.reg 8,.const 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 9] ;;
  .ret (.reg 9)

/-- The rounding driver uses deterministic calls and no random instruction. -/
theorem roundMachine_noRand (init loop : ℕ) : (roundMachineBody init loop).NoRand := by
  simp [roundMachineBody,Stmt.NoRand]

/-- Rounding storage grows linearly in the number of edges after
the forest's initialization allocation. -/
def roundMachineSpace (A0 A L m : ℕ) : ℕ := A0+m*(11*A+32*L+37)

/-- Total rounding cost includes the forest initialization and
the charges for at most m cuts over the full scan. -/
def roundMachineCost (rate L n m : ℕ) : ℕ := rate*(n+1)+m*(10*rate+893*L+2105)+40

private theorem roundSuffixSpace_initial (A0 A L m : ℕ) :
    A0+roundSuffixSpace A L m 0 0=roundMachineSpace A0 A L m := by
  unfold roundMachineSpace roundSuffixSpace roundEdgeSpace roundCleanupCharge
  simp only [Nat.sub_zero,Nat.mul_zero,Nat.add_zero,← Nat.mul_add]
  congr 2
  omega

private theorem roundSuffixCost_initial (q L m : ℕ) :
    roundSuffixCost q L m 0 0=m*(10*q+893*L+2105)+2 := by
  unfold roundSuffixCost roundEdgeCost roundCleanupCharge
  simp only [Nat.sub_zero,Nat.mul_zero,Nat.add_zero,← Nat.mul_add]
  congr 2
  omega

set_option maxHeartbeats 650000 in
/-- The actual rounding driver constructs the exact table of the
mathematical Lemma 4.1 rounder, with explicit time and space. -/
theorem roundMachine_runs {w h L P A edge fractional connected repairRelink loop : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hLoop : p.procs[loop]?=some (roundLoopBody loop edge))
    (hEdge : p.procs[edge]?=some (roundEdgeBody B fractional))
    (hFrac : p.procs[fractional]?=some (roundFractionalBody B connected))
    (hConnect : p.procs[connected]?=some (roundConnectedBody B repairRelink))
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℚ) (M : ℚ)
    (hRoutes : I.Routes (fun j => (f j:ℝ))) (hFP : ∀ j,IsFixedPoint P (f j))
    (graph cost base one heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hL : 0<L) (hLW : L<2^w) (hP : h∣P) (hPW : P<2^w)
    (hFive : 5<2^w) (hM : I.m+1<2^w) (hN : I.n<2^w)
    (hTable : base+I.m*L≤heap) (hCost : cost+I.m*L≤base)
    (hGraph : graph+(zeroLowerWords I).length≤base) (hOne : one+L≤base)
    (hRows : ZeroLowerAt mem graph I) (hCosts : RoundCostsAt I mem cost h L)
    (hUnit : RatAt mem one h L P 1) (hFlow : RoundFlowAt I mem base h L P f)
    (hZero : ZeroFrom mem heap)
    (hSpace : heap+roundMachineSpace (allocation 6 [I.n,L,P,heap]) A L I.m<2^w)
    (hNumeric : ∀ (j : Fin I.m) (s : RoundState D I),LoopInv D I f P M j.val s →
      isIntRat (f j)=false → RoundEdgeNumeric D I f j s h L P) :
    ∃ out final c,
      Runs w p ω (roundMachineBody init loop)
        (startState [I.n,I.m,graph,cost,base,L,P,one,heap] mem pos) (.returned out) final c ∧
      RoundFlowAt I final.mem base h L P (roundFlow D I f).flowArr ∧ heap≤out ∧
      out≤heap+roundMachineSpace (allocation 6 [I.n,L,P,heap]) A L I.m ∧ ZeroFrom final.mem out ∧
      (∀ z<base,final.mem z=mem z) ∧ c≤roundMachineCost (rate I.n) L I.n I.m := by
  let args := [I.n,I.m,graph,cost,base,L,P,one,heap]
  let parent := startState args mem pos
  have hHeap : heap<2^w := by omega
  have hW : ∀ z∈[I.n,L,P,heap],z<2^w := by wram_words
  have hp : (forestMachineContract D w h L P rate allocation).initPre [I.n,L,P,heap] mem :=
    ⟨I.n,heap,rfl⟩
  have hs : heap+allocation 6 [I.n,L,P,heap]<2^w := by unfold roundMachineSpace at hSpace; omega
  obtain ⟨body,hBody,o,raw,c₁,hRun₁,s,x,hRep,hState,hFrame,hC₁⟩ :=
    himpl.2.1 [I.n,L,P,heap] mem pos ω hW hp hZero hs
  change s=D.init I.n at hState
  subst s
  let mid : State := ⟨raw.mem,Function.update parent.regs 9 o.value,raw.pos⟩
  have hCall₁ : Runs w p ω (.call 9 init [.reg 0,.reg 5,.reg 6,.reg 8]) parent .normal mid (4+c₁+1) :=
    runs_call_iff.mpr ⟨[I.n,L,P,heap],body,o,raw,c₁,rfl,hBody,hRun₁,rfl,by cases raw; rfl,rfl⟩
  have hLo : heap≤o.value := hFrame.1
  have hHi : o.value≤heap+allocation 6 [I.n,L,P,heap] := hFrame.2.1
  have hFrame₁ : ∀ z<heap,raw.mem z=mem z := fun z hz => hFrame.2.2.2.1 z hz id
  have hPriv : ∀ z,R.foot heap x z → heap≤z ∧ z<o.value := by
    intro z hz
    exact (hFrame.2.2.2.2 z hz).resolve_left id
  have hRoom : o.value+roundSuffixSpace A L I.m 0 0<2^w := by
    have he := roundSuffixSpace_initial (allocation 6 [I.n,L,P,heap]) A L I.m
    omega
  have hRows₁ : ZeroLowerAt raw.mem graph I :=
    ⟨hRows.1,hRows.2.1,hRows.2.2.of_agree_below (hGraph.trans (by omega)) hFrame₁⟩
  have hCosts₁ : RoundCostsAt I raw.mem cost h L := by
    intro e
    have he := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
    rw [Nat.succ_mul] at he
    exact (hCosts e).frozen hFrame₁ (by omega)
  have hFlow₁ : RoundFlowAt I raw.mem base h L P f := by
    intro e
    have he := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
    rw [Nat.succ_mul] at he
    exact (hFlow e).frozen hFrame₁ (by omega)
  obtain ⟨out,raw₂,c₂,y,hRuns,hRp,hF,hLo₂,hHi₂,hZero₂,hMem₂,hPriv₂,hC₂⟩ :=
    roundLoop_runs D hD rate allocation R himpl B hB hLoop hEdge hFrac hConnect hRL hAlloc I hI f M hRoutes hFP
      heap graph cost base one ω hL hLW hP hPW hFive hM hN.le hTable hCost hGraph hOne hNumeric
      0 (Nat.zero_le _) o.value x raw.mem raw.pos hRows₁ hCosts₁ (hUnit.frozen hFrame₁ (by omega))
      hLo hFlow₁ hRep hPriv hFrame.2.2.1 hRoom
  let loopArgs : List Expr := [.reg 8,.const 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 9]
  have hArgs : evalArgs w mid loopArgs=some [heap,0,I.m,graph,cost,base,L,P,one,o.value] := by
    dsimp only [mid,parent,args,loopArgs]
    eval_expr
  have hCall₂ := round_returning_call (dst:=9) hLoop hArgs hRuns
  let final : State := ⟨raw₂.mem,Function.update mid.regs 9 out,raw₂.pos⟩
  have hRet : Runs w p ω (.ret (.reg 9)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  refine ⟨out,final,4+c₁+1+(10+c₂+1+2+1)+1,?_,hF,hLo.trans hLo₂,?_,hZero₂,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall₁,runs_seq_iff.mpr (Or.inr
      ⟨final,_,_,hCall₂,hRet,rfl⟩),rfl⟩)
  · change out≤o.value+roundSuffixSpace A L I.m 0 0 at hHi₂
    have he := roundSuffixSpace_initial (allocation 6 [I.n,L,P,heap]) A L I.m
    omega
  · intro z hz
    exact (hMem₂ z hz).trans (hFrame₁ z (by omega))
  · change c₁+R.phi heap x raw.mem≤rate I.n*(I.n+1) at hC₁
    change c₂+R.phi heap y raw₂.mem≤roundSuffixCost (rate I.n) L I.m 0 0+4+R.phi heap x raw.mem at hC₂
    rw [roundSuffixCost_initial] at hC₂
    unfold roundMachineCost
    omega

end MinCostFlow.IPM.Machine
