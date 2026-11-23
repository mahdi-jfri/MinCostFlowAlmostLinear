module

public import MinCostFlow.IPM.Machine.SolverLimits
public import MinCostFlow.IPM.Machine.RoundExtractFromSearch
import MinCostFlow.IPM.Machine.RoundCleanupProgram
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Connecting a successful bisection to exact solver output

The search returns its actual endpoint. Recovery reads the successful
flow pointer from that endpoint, copies and rounds the table, and
writes the original circulation's coordinates at the reserved address.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The first 26 registers hold the search packet. Registers 26, 27
and 28 hold the augmented vertex count, original edge count and output. -/
def solverSearchRecoverBody (search recover : ℕ) : Stmt :=
  .call 29 search ((List.range 26).map Expr.reg) ;;
  .call 30 recover [.reg 26,.reg 0,.reg 14,.reg 1,
    .load (.bin .sub (.reg 29) (.const 2)),.reg 15,.reg 16,.reg 5,.reg 29,.reg 28,.reg 27] ;;
  .ret (.reg 30)

/-- The dispatch between the two verified procedures is deterministic. -/
theorem solverSearchRecoverBody_noRand (search recover : ℕ) :
    (solverSearchRecoverBody search recover).NoRand := by
  simp [solverSearchRecoverBody,Stmt.NoRand]

/-- The bisection result needed by recovery, including the integer
optimum, actual accepted table and allocation endpoint. -/
def SolverSearchReturned {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (E heap out : ℕ) (before after : ℕ → ℕ) : Prop :=
  ∃ z : ℤ, ∃ fstar,
    I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
    TargetOffsetResult F I E heap out z z before after ∧ after (out-1)=1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 350000 in
/-- Run the actual bisection and recovery calls on consecutive heaps.
The search and rounder bounds are added, with a fixed amount of call
overhead. Both apply to the same memory and random tape. -/
theorem solverSearchRecover_runs {w search recover offsetTest copy roundEntry extract : ℕ} {p : Program}
    (hSearch : p.procs[search]?=some (targetSearchBody offsetTest))
    (hRecover : p.procs[recover]?=some (roundExtractBody copy roundEntry extract))
    (F : MinRatioFormat w) (J : Circulation) (I : Instance) (old : EpochLayout)
    (quarter source heap limit radius dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (searchSpace roundSpace searchCost roundCost : ℕ)
    (hBudget : heap+searchSpace+roundSpace<2^w)
    (hRunSearch : ∃ out final c,
      Runs w p ω (targetSearchBody offsetTest)
        (startState (targetOffsetPacket old F I 0 quarter source heap limit radius++[targetSearchRounds radius]) mem pos)
        (.returned out) final c ∧
      SolverSearchReturned F I old.exponent heap out mem final.mem ∧
      out≤heap+searchSpace ∧ c≤searchCost)
    (hRunRecover : ∀ out mid pos' , out≤heap+searchSpace →
      SolverSearchReturned F I old.exponent heap out mem mid →
      ∃ last final c,
        Runs w p ω (roundExtractBody copy roundEntry extract)
          (startState [I.n,I.m,old.graph,old.cost,mid (out-2),F.limbs,F.fmt.precision,
            old.one,out,dest,J.m] mid pos') (.returned last) final c ∧
        J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
        out≤last ∧ last≤out+roundSpace ∧ ZeroFrom final.mem last ∧
        (∀ a<dest, final.mem a=mid a) ∧ c≤roundCost)
    (hDest : dest≤heap) :
    ∃ out final c,
      Runs w p ω (solverSearchRecoverBody search recover)
        (startState (targetOffsetPacket old F I 0 quarter source heap limit radius++
          [targetSearchRounds radius,I.n,J.m,dest]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+searchSpace+roundSpace ∧ ZeroFrom final.mem out ∧
      (∀ a<dest,final.mem a=mem a) ∧ c≤searchCost+roundCost+50 := by
  obtain ⟨r,mid,c₁,hr,hRet,hrBound,hc₁⟩ := hRunSearch
  obtain ⟨last,final,c₂,hf,hOpt,hLo₂,hHi₂,hZero,hFrame₂,hc₂⟩ :=
    hRunRecover r mid.mem mid.pos hrBound hRet
  obtain ⟨z,fstar,hStar,hValue,hResult,hBit⟩ := hRet
  have hrLo : heap+2≤r := hResult.1
  have hrFit : r<2^w := by omega
  let args := targetOffsetPacket old F I 0 quarter source heap limit radius++[targetSearchRounds radius]
  let st := startState (args++[I.n,J.m,dest]) mem pos
  have hSearchArgs : evalArgs w st ((List.range 26).map Expr.reg)=some args := by
    rfl
  have hCall₁ := round_returning_call (dst:=29) hSearch hSearchArgs hr
  let st₁ : State := ⟨mid.mem,Function.update st.regs 29 r,mid.pos⟩
  have hTwo : 2<2^w := by omega
  have hSub : Expr.eval w st₁ (.bin .sub (.reg 29) (.const 2)) = some (r-2) :=
    Expr.eval_sub rfl (Expr.eval_const hTwo) hrFit
  have hLoad : Expr.eval w st₁ (.load (.bin .sub (.reg 29) (.const 2))) = some (mid.mem (r-2)) :=
    Expr.eval_load hSub
  have hRecoverArgs : evalArgs w st₁ [.reg 26,.reg 0,.reg 14,.reg 1,
      .load (.bin .sub (.reg 29) (.const 2)),.reg 15,.reg 16,.reg 5,.reg 29,.reg 28,.reg 27] =
      some [I.n,I.m,old.graph,old.cost,mid.mem (r-2),F.limbs,F.fmt.precision,old.one,r,dest,J.m] := by
    exact evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons hLoad rfl))))
  have hCall₂ := round_returning_call (dst:=30) hRecover hRecoverArgs hf
  let st₂ : State := ⟨final.mem,Function.update st₁.regs 30 last,final.pos⟩
  have hReturn : Runs w p ω (.ret (.reg 30)) st₂ (.returned last) st₂ 2 :=
    runs_ret_iff.mpr ⟨last,rfl,rfl,rfl,by decide⟩
  have hRun : Runs w p ω (solverSearchRecoverBody search recover) st (.returned last) st₂ (c₁+c₂+46) := by
    unfold solverSearchRecoverBody
    refine runs_seq_iff.mpr (Or.inr ⟨st₁,26+c₁+1,c₂+18,hCall₁,?_,?_⟩)
    · exact runs_seq_iff.mpr (Or.inr ⟨st₂,14+c₂+1,2,hCall₂,hReturn,by omega⟩)
    · omega
  refine ⟨last,st₂,c₁+c₂+46,?_,hOpt,by omega,by omega,hZero,?_,by omega⟩
  · simpa only [st,args,List.append_assoc,List.singleton_append] using hRun
  · intro a ha
    exact (hFrame₂ a ha).trans (hResult.2.2.2.1 a (ha.trans_le hDest))

/-- `V`-passing variant of `solverSearchRecoverBody`: expects `V` at index 29 (`.reg 29`). -/
def solverSearchRecoverBodyWithV (search recover : ℕ) : Stmt :=
  .call 29 search ((List.range 26).map Expr.reg ++ [.reg 29]) ;;
  .call 30 recover [.reg 26,.reg 0,.reg 14,.reg 1,
    .load (.bin .sub (.reg 29) (.const 2)),.reg 15,.reg 16,.reg 5,.reg 29,.reg 28,.reg 27] ;;
  .ret (.reg 30)

/-- The `V`-passing search-recover wrapper is deterministic. -/
theorem solverSearchRecoverBodyWithV_noRand (search recover : ℕ) :
    (solverSearchRecoverBodyWithV search recover).NoRand := by
  simp [solverSearchRecoverBodyWithV,Stmt.NoRand]

/-- `V`-passing variant of `solverSearchRecover_runs`. -/
theorem solverSearchRecoverWithV_runs {w search recover offsetTest copy roundEntry extract : ℕ} {p : Program}
    (hSearch : p.procs[search]?=some (targetSearchBodyWithV offsetTest))
    (hRecover : p.procs[recover]?=some (roundExtractBody copy roundEntry extract))
    (F : MinRatioFormat w) (J : Circulation) (I : Instance) (old : EpochLayout)
    (quarter source heap limit radius dest V : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (searchSpace roundSpace searchCost roundCost : ℕ)
    (hBudget : heap+searchSpace+roundSpace<2^w)
    (_hV : V<2^w)
    (hRunSearch : ∃ out final c,
      Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (targetOffsetPacket old F I 0 quarter source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned out) final c ∧
      SolverSearchReturned F I old.exponent heap out mem final.mem ∧
      out≤heap+searchSpace ∧ c≤searchCost)
    (hRunRecover : ∀ out mid pos' , out≤heap+searchSpace →
      SolverSearchReturned F I old.exponent heap out mem mid →
      ∃ last final c,
        Runs w p ω (roundExtractBody copy roundEntry extract)
          (startState [I.n,I.m,old.graph,old.cost,mid (out-2),F.limbs,F.fmt.precision,
            old.one,out,dest,J.m] mid pos') (.returned last) final c ∧
        J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
        out≤last ∧ last≤out+roundSpace ∧ ZeroFrom final.mem last ∧
        (∀ a<dest, final.mem a=mid a) ∧ c≤roundCost)
    (hDest : dest≤heap) :
    ∃ out final c,
      Runs w p ω (solverSearchRecoverBodyWithV search recover)
        (startState (targetOffsetPacket old F I 0 quarter source heap limit radius++
          [targetSearchRounds radius,I.n,J.m,dest,V]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+searchSpace+roundSpace ∧ ZeroFrom final.mem out ∧
      (∀ a<dest,final.mem a=mem a) ∧ c≤searchCost+roundCost+50 := by
  obtain ⟨r,mid,c₁,hr,hRet,hrBound,hc₁⟩ := hRunSearch
  obtain ⟨last,final,c₂,hf,hOpt,hLo₂,hHi₂,hZero,hFrame₂,hc₂⟩ :=
    hRunRecover r mid.mem mid.pos hrBound hRet
  obtain ⟨z,fstar,hStar,hValue,hResult,hBit⟩ := hRet
  have hrLo : heap+2≤r := hResult.1
  have hrFit : r<2^w := by omega
  let args := targetOffsetPacket old F I 0 quarter source heap limit radius++[targetSearchRounds radius]
  let st := startState (args++[I.n,J.m,dest,V]) mem pos
  have hSearchArgs0 : evalArgs w st ((List.range 26).map Expr.reg)=some args := rfl
  have hst29 : st.regs 29=V := by
    simp [st,args,startState,targetOffsetPacket,targetEpochPacket]
  have hSearchArgs : evalArgs w st ((List.range 26).map Expr.reg ++ [.reg 29])=some (args++[V]) :=
    evalArgs_append hSearchArgs0 (by simp [evalArgs,Expr.eval,hst29])
  have hCall₁ := round_returning_call (dst:=29) hSearch hSearchArgs
    (by
      change Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (args++[V]) mem pos) (.returned r) mid c₁
      dsimp only [args]
      rw [List.append_assoc]
      exact hr)
  let st₁ : State := ⟨mid.mem,Function.update st.regs 29 r,mid.pos⟩
  have hTwo : 2<2^w := by omega
  have hSub : Expr.eval w st₁ (.bin .sub (.reg 29) (.const 2)) = some (r-2) :=
    Expr.eval_sub rfl (Expr.eval_const hTwo) hrFit
  have hLoad : Expr.eval w st₁ (.load (.bin .sub (.reg 29) (.const 2))) = some (mid.mem (r-2)) :=
    Expr.eval_load hSub
  have hRecoverArgs : evalArgs w st₁ [.reg 26,.reg 0,.reg 14,.reg 1,
      .load (.bin .sub (.reg 29) (.const 2)),.reg 15,.reg 16,.reg 5,.reg 29,.reg 28,.reg 27] =
      some [I.n,I.m,old.graph,old.cost,mid.mem (r-2),F.limbs,F.fmt.precision,old.one,r,dest,J.m] := by
    exact evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons rfl (evalArgs_cons hLoad rfl))))
  have hCall₂ := round_returning_call (dst:=30) hRecover hRecoverArgs hf
  let st₂ : State := ⟨final.mem,Function.update st₁.regs 30 last,final.pos⟩
  have hReturn : Runs w p ω (.ret (.reg 30)) st₂ (.returned last) st₂ 2 :=
    runs_ret_iff.mpr ⟨last,rfl,rfl,rfl,by decide⟩
  have hRun : Runs w p ω (solverSearchRecoverBodyWithV search recover) st (.returned last) st₂ (c₁+c₂+47) := by
    unfold solverSearchRecoverBodyWithV
    have hSize : argsSize ((List.range 26).map Expr.reg ++ [.reg 29])=27 := by decide
    refine runs_seq_iff.mpr (Or.inr ⟨st₁,27+c₁+1,c₂+18,by simpa only [hSize] using hCall₁,?_,?_⟩)
    · exact runs_seq_iff.mpr (Or.inr ⟨st₂,14+c₂+1,2,hCall₂,hReturn,by omega⟩)
    · omega
  refine ⟨last,st₂,c₁+c₂+47,?_,hOpt,by omega,by omega,hZero,?_,by omega⟩
  · simpa only [st,args,List.append_assoc,List.singleton_append] using hRun
  · intro a ha
    exact (hFrame₂ a ha).trans (hResult.2.2.2.1 a (ha.trans_le hDest))

end MinCostFlow.IPM.Machine
