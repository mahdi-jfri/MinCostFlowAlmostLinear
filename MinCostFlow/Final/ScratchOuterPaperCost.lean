module

public import MinCostFlow.Final.ScratchOuterCountedCost
import MinCostFlow.Scaling.ArbitraryDemandPaperCost
import MinCostFlow.Scaling.GeneralScalingLogs
import MinCostFlow.Scaling.EmptyOuterCounters
import MinCostFlow.Scaling.OuterEntryPaperCost
import WordRAM.Exec
import WordRAM.Entry
import Mathlib.Tactic.Ring

/-!
# The logarithmic cost bound at the widened scratch policy

The counted work and calls give the same padded logarithms as the
original cost scaling. The guest-width factor enters the constant.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- A solver meeting the actual circulation contract necessarily has a
positive time bound at `(0,0)`. -/
theorem scratchSolverTime_zero_pos (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d) : 1≤T 0 0 := by
  let J : Circulation := ⟨0,0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0⟩
  have hc : J.CostsBounded (J.m^10) := fun e => Fin.elim0 e
  have hu : ∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40 := fun e => Fin.elim0 e
  obtain ⟨hwords,hpre⟩ := polynomialScratch_compressed_pre T S c d J (by decide) (hScratch _ _) hc hu
  obtain ⟨body,_,o,st,steps,hr,_,hcost⟩ := hproc J [0,J.solverWords.length]
    (initMem J.solverWords) 0 (fun _ => false) hwords hpre
  have hd := solverDimensions_of_at J (initMem J.solverWords) 0 J.solverWords.length (listAt_initMem _)
  change steps≤T (solverDimensions [0,J.solverWords.length] (initMem J.solverWords)).1
    (solverDimensions [0,J.solverWords.length] (initMem J.solverWords)).2 at hcost
  rw [hd] at hcost
  exact hr.cost_pos.trans hcost

/-- An explicit constant covering outer machine costs and solver dimensions. -/
def scratchOuterScalingConstant (solver : Program) (c d : ℕ) : ℕ := 1000000000000000000*scratchWorkFactor solver c d

private theorem outer_paper_budget (calls work m n reg A B L time : ℕ)
    (hc : calls≤345600*A*B*L) (hw : work≤210000000000*m*A*B*L+85*n) :
    calls*((reg+6)*time)+2000000*(reg+1)*work≤
      1000000000000000000*(reg+1)*A*B*L*(time+m)+1000000000000000000*(reg+1)*n := by
  have hcoef : 345600*(reg+6)≤1000000000000000000*(reg+1) := by omega
  have hcalls : calls*((reg+6)*time)≤1000000000000000000*(reg+1)*A*B*L*time := by
    calc
      _ ≤ (345600*A*B*L)*((reg+6)*time) := Nat.mul_le_mul_right _ hc
      _ = 345600*(reg+6)*(A*B*L*time) := by ring
      _ ≤ 1000000000000000000*(reg+1)*(A*B*L*time) := Nat.mul_le_mul_right _ hcoef
      _ = _ := by ring
  have hwork : 2000000*(reg+1)*work≤
      1000000000000000000*(reg+1)*A*B*L*m+1000000000000000000*(reg+1)*n := by
    calc
      _ ≤ 2000000*(reg+1)*(210000000000*m*A*B*L+85*n) := Nat.mul_le_mul_left _ hw
      _ = 420000000000000000*((reg+1)*(A*B*L*m))+170000000*((reg+1)*n) := by ring
      _ ≤ 1000000000000000000*((reg+1)*(A*B*L*m))+
          1000000000000000000*((reg+1)*n) := Nat.add_le_add
        (Nat.mul_le_mul_right _ (by decide)) (Nat.mul_le_mul_right _ (by decide))
      _ = _ := by ring
  exact (Nat.add_le_add hcalls hwork).trans_eq (by ring)

/-- The complete outer procedure has the explicit paper-form bound
`K*log(m)*log(mU)*log(C)*(T(K*n,K*m)+m)+K*n`, with padded binary logs
and `K=10^18*(regBound+1)`, on every nonempty valid input. -/
theorem scratchArbitraryDemand_cost_paper_nonempty (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) (hm : 0<I.m) :
    (scratchArbitraryDemandContract w solver entry T S c d hproc I hv C U).cost args mem≤
      scratchOuterScalingConstant solver c d*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)*
          (T (scratchOuterScalingConstant solver c d*min I.n I.m) (scratchOuterScalingConstant solver c d*I.m)+I.m)+
        scratchOuterScalingConstant solver c d*I.n := by
  let r := FlowReduction.arbitraryDemandScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
  have hc := FlowReduction.arbitraryDemandScalingModel_calls ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
  have hw := FlowReduction.arbitraryDemandScalingModel_work ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U hm
  have hb := scratchArbitraryDemand_cost_counted w solver entry T S c d hproc hmono I hv C U args mem
  change (scratchArbitraryDemandContract w solver entry T S c d hproc I hv C U).cost args mem≤
    r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+2000000*scratchWorkFactor solver c d*r.work at hb
  have h8 : 9≤scratchOuterScalingConstant solver c d := by have h := scratchWorkFactor_pos solver c d; unfold scratchOuterScalingConstant; omega
  have h72 : 72≤scratchOuterScalingConstant solver c d := by have h := scratchWorkFactor_pos solver c d; unfold scratchOuterScalingConstant; omega
  have hn : min (8*I.n) (9*I.m) ≤ scratchOuterScalingConstant solver c d * min I.n I.m := by
    rcases le_total I.n I.m with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (Nat.mul_le_mul_right I.n (by omega))
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (Nat.mul_le_mul_right I.m h8)
  have ht := hmono _ _ (72*I.m)
    (scratchOuterScalingConstant solver c d*I.m) hn (Nat.mul_le_mul_right I.m h72)
  let reg := scratchWorkFactor solver c d-1
  have heff : reg+1 = scratchWorkFactor solver c d := scratchWorkFactor_succ solver c d
  have hreg : solver.regBound ≤ reg := by
    have h := Nat.le_mul_of_pos_right (solver.regBound+1) (scratchWidthFactor_pos c d)
    change solver.regBound+1 ≤ scratchWorkFactor solver c d at h
    omega
  have hbudget := outer_paper_budget r.calls.length r.work I.m I.n reg
    (Nat.clog 2 (I.m+1)+1) (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1) (Nat.clog 2 (C+2))
    (T (scratchOuterScalingConstant solver c d*min I.n I.m) (scratchOuterScalingConstant solver c d*I.m)) hc hw
  have hterm := Nat.mul_le_mul_left r.calls.length
    (Nat.mul_le_mul (Nat.add_le_add_right hreg 6) ht)
  exact hb.trans ((Nat.add_le_add_right hterm _).trans (by
    simpa only [heff, scratchOuterScalingConstant] using hbudget))

/-- The explicit logarithmic outer cost bound holds on all valid inputs,
including graphs with no edges or vertices. -/
theorem scratchArbitraryDemand_cost_paper (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (scratchArbitraryDemandContract w solver entry T S c d hproc I hv C U).cost args mem≤
      scratchOuterScalingConstant solver c d*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)*
          (T (scratchOuterScalingConstant solver c d*min I.n I.m) (scratchOuterScalingConstant solver c d*I.m)+I.m)+
        scratchOuterScalingConstant solver c d*I.n := by
  by_cases hm : 0<I.m
  · exact scratchArbitraryDemand_cost_paper_nonempty w solver entry T S c d hproc hmono I hv C U args mem hm
  have hz : I.m=0 := by omega
  obtain ⟨hc,hw⟩ := arbitraryDemandScalingModel_empty_counters
    ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U hz
  have hb := scratchArbitraryDemand_cost_counted w solver entry T S c d hproc hmono I hv C U args mem
  dsimp only at hb
  rw [hc,zero_mul,zero_add] at hb
  have hcost := hb.trans (Nat.mul_le_mul_left (2000000*scratchWorkFactor solver c d) hw)
  have ht : 1≤T (scratchOuterScalingConstant solver c d*min I.n I.m) (scratchOuterScalingConstant solver c d*I.m) :=
    (scratchSolverTime_zero_pos solver entry T S c d hproc hScratch).trans (hmono 0 _ 0 _ (Nat.zero_le _) (Nat.zero_le _))
  have hl : 1≤Nat.clog 2 (C+2) := Nat.clog_pos (by decide) (by omega)
  have hfactor : scratchOuterScalingConstant solver c d≤
      scratchOuterScalingConstant solver c d*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)*
          (T (scratchOuterScalingConstant solver c d*min I.n I.m) (scratchOuterScalingConstant solver c d*I.m)+I.m) := by
    calc
      _ ≤ _*(Nat.clog 2 (I.m+1)+1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _*(Nat.clog 2 (I.m+1)+Nat.clog 2 (U+1)+1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _*Nat.clog 2 (C+2) := Nat.le_mul_of_pos_right _ hl
      _ ≤ _*(T (scratchOuterScalingConstant solver c d*min I.n I.m) (scratchOuterScalingConstant solver c d*I.m)+I.m) :=
        Nat.le_mul_of_pos_right _ (by omega)
  have hsmall : 2000000*scratchWorkFactor solver c d*(83*I.n+2)≤
      scratchOuterScalingConstant solver c d+scratchOuterScalingConstant solver c d*I.n := by
    unfold scratchOuterScalingConstant
    calc
      _ = 166000000*(scratchWorkFactor solver c d*I.n)+4000000*scratchWorkFactor solver c d := by ring
      _ ≤ 1000000000000000000*(scratchWorkFactor solver c d*I.n)+1000000000000000000*scratchWorkFactor solver c d :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by decide)) (Nat.mul_le_mul_right _ (by decide))
      _ = _ := by ring
  exact hcost.trans (hsmall.trans (Nat.add_le_add_right hfactor _))

/-- The whole program uses twice the procedure's explicit constant. -/
def scratchWholeScalingConstant (solver : Program) (c d : ℕ) : ℕ := 2*scratchOuterScalingConstant solver c d

set_option maxRecDepth 4096 in
private theorem entry_paper_budget (cost K A B L time m n : ℕ)
    (hc : cost≤K*A*B*L*(time+m)+K*n) (hK : 2002≤K)
    (hA : 1≤A) (hB : 1≤B) (hL : 1≤L) (ht : 1≤time) :
    cost+2000*(m+n+1)+2≤(2*K)*A*B*L*(time+m)+(2*K)*n := by
  have hkA : K≤K*A := Nat.le_mul_of_pos_right _ hA
  have hkB : K*A≤K*A*B := Nat.le_mul_of_pos_right _ hB
  have hkL : K*A*B≤K*A*B*L := Nat.le_mul_of_pos_right _ hL
  have hcoef : 2002≤K*A*B*L := hK.trans (hkA.trans (hkB.trans hkL))
  have hq : 2002*(m+1)≤K*A*B*L*(time+m) := Nat.mul_le_mul hcoef (by omega)
  have hn : 2002*n≤K*n := Nat.mul_le_mul_right n hK
  have he : (2*K)*A*B*L*(time+m)+(2*K)*n=2*(K*A*B*L*(time+m)+K*n) := by ring
  rw [he]
  omega

/-- The complete original-input program, including its entry call, has
`K*log(m)*log(mU)*log(C)*(T(K*n,K*m)+m)+K*n` cost with padded binary
logs and the explicit constant `K=2*10^18*scratchWorkFactor solver c d`. -/
theorem scratchOuterEntry_cost_paper (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (scratchOuterEntryContract w solver entry T S c d hproc I hv).cost args mem+2≤
      scratchWholeScalingConstant solver c d*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
          (T (scratchWholeScalingConstant solver c d*min I.n I.m) (scratchWholeScalingConstant solver c d*I.m)+I.m)+
        scratchWholeScalingConstant solver c d*I.n := by
  let K := scratchOuterScalingConstant solver c d
  have hb := scratchArbitraryDemand_cost_paper w solver entry T S c d hproc hScratch hmono I hv I.maxCost I.maxCapacity [] (fun _ => 0)
  have hK : 2002≤K := by have h := scratchWorkFactor_pos solver c d; dsimp only [K,scratchOuterScalingConstant]; omega
  have hKK : K≤scratchWholeScalingConstant solver c d := by change K≤2*K; omega
  have ht := hmono (K*min I.n I.m) (scratchWholeScalingConstant solver c d*min I.n I.m)
    (K*I.m) (scratchWholeScalingConstant solver c d*I.m)
    (Nat.mul_le_mul_right (min I.n I.m) hKK) (Nat.mul_le_mul_right I.m hKK)
  have htime : 1≤T (scratchWholeScalingConstant solver c d*min I.n I.m) (scratchWholeScalingConstant solver c d*I.m) :=
    (scratchSolverTime_zero_pos solver entry T S c d hproc hScratch).trans (hmono 0 _ 0 _ (Nat.zero_le _) (Nat.zero_le _))
  have hraise := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left
    (K*(Nat.clog 2 (I.m+1)+1)*(Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2))
    (Nat.add_le_add_right ht I.m)) (K*I.n))
  exact entry_paper_budget _ K _ _ _ _ I.m I.n hraise hK (by omega) (by omega)
    (Nat.clog_pos (by decide) (by omega)) htime

end MinCostFlow.Final
