module

public import MinCostFlow.IPM.Machine.RoundLoopCalls
public import MinCostFlow.Rounding.Lemma4_1
import WordRAM.Tactic

/-!
# Executing the complete rounding scan

The runtime visits every original edge once. The proof follows
the same `roundFlowLoop` state at each index and telescopes the
forest's credit as well as the charges for removed edges.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Indexed cost blocks, stored at precision zero. -/
def RoundCostsAt (I : Instance) (mem : ℕ → ℕ) (base h L : ℕ) : Prop :=
  ∀ e, RatAt mem (base+e.val*L) h L 0 (I.edge e).cost

set_option maxHeartbeats 620000 in
/-- The single-pass scan writes exactly the integral rounding
model's final table. Its remaining budget decreases by one edge
charge and by the charge for that edge's actual cuts. -/
theorem roundLoop_runs {w h L P A entry edge fractional connected repairRelink : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hLoop : p.procs[entry]?=some (roundLoopBody entry edge))
    (hEdge : p.procs[edge]?=some (roundEdgeBody B fractional))
    (hFrac : p.procs[fractional]?=some (roundFractionalBody B connected))
    (hConnect : p.procs[connected]?=some (roundConnectedBody B repairRelink))
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℚ) (M : ℚ)
    (hRoutes : I.Routes (fun j => (f j:ℝ))) (hFP : ∀ j,IsFixedPoint P (f j))
    (b graph cost base one : ℕ) (ω : ℕ → Bool)
    (hL : 0<L) (hLW : L<2^w) (hP : h∣P) (hPW : P<2^w)
    (hFive : 5<2^w) (hM : I.m+1<2^w) (hN : I.n≤2^w)
    (hTable : base+I.m*L≤b) (hCost : cost+I.m*L≤base)
    (hGraph : graph+(zeroLowerWords I).length≤base) (hOne : one+L≤base)
    (hNumeric : ∀ (j : Fin I.m) (s : RoundState D I),LoopInv D I f P M j.val s →
      isIntRat (f j)=false → RoundEdgeNumeric D I f j s h L P) :
    ∀ (k : ℕ) (hk : k≤I.m) (heap : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ),
      let s := roundFlowLoop D I f k hk
      let cuts := s.counts.cutOps
      ZeroLowerAt mem graph I → RoundCostsAt I mem cost h L → RatAt mem one h L P 1 →
      b≤heap → RoundFlowAt I mem base h L P s.flowArr →
      R.rep b s.df x mem → (∀ z,R.foot b x z → b≤z ∧ z<heap) → ZeroFrom mem heap →
      heap+roundSuffixSpace A L I.m k cuts<2^w →
      ∃ out final c y,
        Runs w p ω (roundLoopBody entry edge)
          (startState [b,k,I.m,graph,cost,base,L,P,one,heap] mem pos) (.returned out) final c ∧
        R.rep b (roundFlow D I f).df y final.mem ∧
        RoundFlowAt I final.mem base h L P (roundFlow D I f).flowArr ∧
        heap≤out ∧ out≤heap+roundSuffixSpace A L I.m k cuts ∧ ZeroFrom final.mem out ∧
        (∀ z<base,final.mem z=mem z) ∧ (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
        c+R.phi b y final.mem≤roundSuffixCost (rate I.n) L I.m k cuts+4+R.phi b x mem := by
  intro k hk'
  induction hk' using Nat.decreasingInduction with
  | of_succ k hk ih =>
    intro heap x mem pos
    dsimp only
    intro hRows hCosts hUnit hb hFlow hRep hFoot hZero hSpace
    let hk' : k≤I.m := Nat.le_of_lt hk
    let s := roundFlowLoop D I f k hk'
    let args := [b,k,I.m,graph,cost,base,L,P,one,heap]
    let parent := startState args mem pos
    have hK : k<I.m := hk
    let j : Fin I.m := ⟨k,hK⟩
    let s' := roundFlowLoop D I f (k+1) (Nat.succ_le_of_lt hK)
    have hInv := roundFlowLoop_inv hD hI hRoutes P M k hk'
    have hInv' := roundFlowLoop_inv hD hI hRoutes P M (k+1) (Nat.succ_le_of_lt hK)
    have hCut : s.counts.cutOps≤s'.counts.cutOps := roundEdge_cuts_mono hD hI s j hInv hFP
    have hC (s : RoundState D I) {i : ℕ} (hi : LoopInv D I f P M i s) :
        s.counts.linkOps ≤ i ∧ s.counts.cutOps+(D.toForest s.df).edges.length=s.counts.linkOps := by
      obtain ⟨_,_,_,_,_,_,_,_,_,ha,hb,_,_,_,_,_,_,_⟩ := hi
      exact ⟨ha,hb⟩
    obtain ⟨hLink,hBalance⟩ := hC s hInv
    obtain ⟨hLink',hBalance'⟩ := hC s' hInv'
    have hCut' : s'.counts.cutOps≤I.m := by omega
    have hBudget := roundEdgeSpace_le_remaining A L I.m k s.counts.cutOps
      (D.toForest s.df).edges.length s.counts.linkOps hK hBalance hLink
    have hRoom : heap+roundEdgeSpace A L (D.toForest s.df).edges.length<2^w :=
      (Nat.add_le_add_left hBudget heap).trans_lt hSpace
    have hHeap : heap<2^w := by omega
    have hLim := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hLim
    have hCostEnd : cost+j.val*L+L≤base := by omega
    obtain ⟨hArgs,hWords⟩ :=
      roundLoopEdgeArgs_eval I hI j b graph cost base one heap mem pos hRows hGraph hTable hb hHeap hCost hOne
        hM hN hLW hPW hFive
    obtain ⟨midHeap,raw,c₁,x₁,hRun₁,hRep₁,hFlow₁,hLo,hHi,hZero₁,hMem₁,hFoot₁,hC₁⟩ :=
      roundEdge_runs D hD rate allocation R himpl B hB hFrac hConnect hRL hAlloc I hI f j s M hInv hFP
        b (cost+j.val*L) one base heap x mem pos ω hL hP hN hWords (hCosts j) hUnit hFlow
        hTable hCostEnd hOne hb hRep hFoot hZero (hNumeric j s hInv) hRoom
    have hSplit := roundSuffixSpace_step A L I.m k s.counts.cutOps s'.counts.cutOps hK hCut hCut'
    let r := s'.counts.cutOps-s.counts.cutOps
    have hSplit' : roundSuffixSpace A L I.m k s.counts.cutOps =
        roundEdgeSpace A L r+roundSuffixSpace A L I.m (k+1) s'.counts.cutOps := hSplit
    change midHeap≤heap+roundEdgeSpace A L r at hHi
    have hs : midHeap+roundSuffixSpace A L I.m (k+1) s'.counts.cutOps<2^w := by
      change heap+roundSuffixSpace A L I.m k s.counts.cutOps<2^w at hSpace
      rw [hSplit'] at hSpace
      omega
    have hRows₁ : ZeroLowerAt raw.mem graph I :=
      ⟨hRows.1,hRows.2.1,hRows.2.2.of_agree_below hGraph hMem₁⟩
    have hCosts₁ : RoundCostsAt I raw.mem cost h L := by
      intro e
      have hlim := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
      rw [Nat.succ_mul] at hlim
      exact (hCosts e).frozen hMem₁ (by omega)
    obtain ⟨out,raw₂,c₂,y,hRun₂,hRep₂,hFlow₂,hLo₂,hHi₂,hZero₂,hMem₂,hFoot₂,hC₂⟩ :=
      ih midHeap x₁ raw.mem raw.pos hRows₁ hCosts₁
        (hUnit.frozen hMem₁ hOne) (hb.trans hLo) hFlow₁ hRep₁ hFoot₁ hZero₁ hs
    let mid : State := ⟨raw.mem,Function.update parent.regs 10 midHeap,raw.pos⟩
    have hCall₁ := round_returning_call (dst:=10) hEdge hArgs hRun₁
    let es : List Expr := [.reg 0,.bin .add (.reg 1) (.const 1),.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 10]
    have hK' : k+1<2^w := by omega
    have hOneW : 1<2^w := by omega
    have hArgs₂ : evalArgs w mid es=some [b,k+1,I.m,graph,cost,base,L,P,one,midHeap] := by
      dsimp only [es,mid,parent,args]
      eval_expr
    have hCall₂ := round_returning_call (dst:=10) hLoop hArgs₂ hRun₂
    let final : State := ⟨raw₂.mem,Function.update mid.regs 10 out,raw₂.pos⟩
    have hRet : Runs w p ω (.ret (.reg 10)) final (.returned out) final 2 :=
      runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
    have hRest : Runs w p ω (.call 10 entry es ;; .ret (.reg 10))
        mid (.returned out) final (12+c₂+1+2+1) :=
      runs_seq_iff.mpr (Or.inr ⟨final,_,_,hCall₂,hRet,rfl⟩)
    let fullCost := argsSize roundLoopEdgeArgs+c₁+1+(12+c₂+1+2+1)+1+4
    have hRun : Runs w p ω (roundLoopBody entry edge) parent (.returned out) final fullCost := by
      apply runs_cond_iff.mpr
      refine ⟨1,argsSize roundLoopEdgeArgs+c₁+1+(12+c₂+1+2+1)+1,
        Expr.eval_lt_true (by rfl) (by rfl) hK hOneW,?_,?_⟩
      swap
      · change fullCost=3+(argsSize roundLoopEdgeArgs+c₁+1+(12+c₂+1+2+1)+1)+1
        dsimp only [fullCost]
        omega
      exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall₁,hRest,rfl⟩)
    refine ⟨out,final,fullCost,y,hRun,hRep₂,hFlow₂,hLo.trans hLo₂,?_,hZero₂,?_,hFoot₂,?_⟩
    · change out≤heap+roundSuffixSpace A L I.m k s.counts.cutOps
      change out≤midHeap+roundSuffixSpace A L I.m (k+1) s'.counts.cutOps at hHi₂
      rw [hSplit']
      omega
    · intro z hz
      exact (hMem₂ z hz).trans (hMem₁ z hz)
    · change fullCost+R.phi b y raw₂.mem≤roundSuffixCost (rate I.n) L I.m k s.counts.cutOps+4+R.phi b x mem
      rw [roundSuffixCost_step _ _ _ _ _ _ hK hCut hCut']
      change c₁+R.phi b x₁ raw.mem≤roundEdgeCost (rate I.n) L r+19*L+70+R.phi b x mem at hC₁
      change c₂+R.phi b y raw₂.mem≤roundSuffixCost (rate I.n) L I.m (k+1) s'.counts.cutOps+4+R.phi b x₁ raw.mem at hC₂
      change fullCost+R.phi b y raw₂.mem≤
        roundEdgeCost (rate I.n) L r+19*L+250+roundSuffixCost (rate I.n) L I.m (k+1) s'.counts.cutOps
          +4+R.phi b x mem
      have hs : argsSize roundLoopEdgeArgs≤60 := by decide
      dsimp only [fullCost]
      omega
  | self =>
    intro heap x mem pos
    dsimp only
    intro hRows hCosts hUnit hb hFlow hRep hFoot hZero hSpace
    let parent := startState [b,I.m,I.m,graph,cost,base,L,P,one,heap] mem pos
    have hOneW : 1<2^w := by omega
    have hRet : Runs w p ω (.ret (.reg 9)) parent (.returned heap) parent 2 :=
      runs_ret_iff.mpr ⟨heap,rfl,rfl,rfl,rfl⟩
    refine ⟨heap,parent,6,x,?_,hRep,hFlow,le_rfl,by omega,hZero,fun _ _ => rfl,hFoot,?_⟩
    · exact runs_cond_iff.mpr ⟨0,2,Expr.eval_lt_false (by rfl) (by rfl) le_rfl hOneW,hRet,rfl⟩
    · change 6+R.phi b x mem≤roundSuffixCost (rate I.n) L I.m I.m (roundFlow D I f).counts.cutOps+4+R.phi b x mem
      unfold roundSuffixCost
      omega

end MinCostFlow.IPM.Machine
