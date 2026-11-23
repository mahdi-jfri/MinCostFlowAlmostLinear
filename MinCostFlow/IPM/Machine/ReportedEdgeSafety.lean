module

public import MinCostFlow.IPM.Machine.ReportedEdgeOutput
import Mathlib.Tactic.Linarith

/-!
# Sufficient conditions for accepting one reported coordinate

The candidate is the exact base plus Query value. If both slacks lie
strictly within the encoded range, the capacity guard passes, the
candidate is written exactly, and the subsequent slack guard passes.
This proves acceptance from the actual two guard postconditions.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The reported-edge outcome is exactly the strict slack test. -/
theorem reportedEdge_accepts_iff {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v final)
    : final (v-1)=1 ↔ ReportedCandidateSafe F A s mem e base lo up E := by
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,
    hquery,hs,hend,hmn,hmx,hbase,havoid,hsep,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨e',base',lo',up',dst',heap',heq,_,hbaseValid,_⟩ := hquery
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,_,_,hloEnd,_,hupEnd,_,_,_,_,hloValid,_,hupValid,_,_,_,_,_,_,_,hmin,hmax⟩ := hs
  obtain ⟨qEnd,qMem,_,hQ,_,hbranch,_,_⟩ := hout
  change (queryCoordinateContract F A G m κ α rate allocation R b s x).post
    [b,e,base,lo,up,f,F.limbs,heap] mem qEnd qMem at hQ
  let V := fun ptr => Num.fixVal mem ptr F.fmt.limbBits F.limbs F.fmt.precision
  let W := fun ptr => Num.fixVal qMem ptr F.fmt.limbBits F.limbs F.fmt.precision
  have hPos : (0:ℝ)<1/2^E := by positivity
  have hAway (ptr : ℕ) (hp : ptr+F.limbs≤sourceEnd) (j : ℕ) (hj : j<F.limbs) :
      ¬R.foot b x (ptr+j) := havoid _ (by omega)
  have hCap := queryCoordinate_acceptance F A G m κ α rate allocation R hQ
    ⟨hbaseValid,rfl⟩ ⟨hloValid,rfl⟩ ⟨hupValid,rfl⟩
    (hbase.trans hend) (hloEnd.trans hend) (hupEnd.trans hend)
    (hAway base hbase) (hAway lo hloEnd) (hAway up hupEnd)
  change qMem (qEnd-(1+4*F.limbs))=(if V lo<V base+A.query s e ∧ V base+A.query s e<V up then 1 else 0) at hCap
  by_cases hInside : V lo<V base+A.query s e ∧ V base+A.query s e<V up
  · rw [ite_eq_left hInside] at hCap
    have hStored := queryCoordinate_output F A G m κ α rate allocation R hQ
      (baseValue:=V base) ⟨hbaseValid,rfl⟩ (hbase.trans hend) (hAway base hbase) hCap
    have hFrame := (queryCoordinate_frame F A G m κ α rate allocation R hQ).2.2.2
    have hSame (ptr : ℕ) (hp : ptr∈[lo,up,mn,mx]) (hpEnd : ptr+F.limbs≤sourceEnd) : W ptr=V ptr := by
      have hdis := hsep ptr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto)
      unfold W V Num.fixVal
      rw [Num.intVal_congr (fun j hj => hFrame _ (by omega) (hAway ptr hpEnd j hj) (by
        rcases hdis with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)))]
    have hLo := hSame lo (by simp) hloEnd
    have hUp := hSame up (by simp) hupEnd
    have hMn : W mn=1/(2:ℝ)^E := (hSame mn (by simp) hmn).trans hmin.2
    have hMx : W mx=(2:ℝ)^E := (hSame mx (by simp) hmx).trans hmax.2
    have hValue : W f=V base+A.query s e := hStored.2
    simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch
    rw [ite_eq_left hCap] at hbranch
    obtain ⟨guardEnd,guardMem,hguard,hflag⟩ := hbranch
    obtain ⟨slackEnd,slackMem,hslack,hbit,_⟩ := hguard
    have hiff := hslack.1.2.2.2.2.2
    change guardMem (qEnd+4*F.limbs)=slackMem (qEnd+4*F.limbs) at hbit
    change (slackMem (qEnd+4*F.limbs)=1 ↔ (W mn<W up-W f ∧ W up-W f<W mx) ∧
      (W mn<W f-W lo ∧ W f-W lo<W mx)) at hiff
    rw [hLo,hUp,hMn,hMx,hValue] at hiff
    rw [flagRecord_output hflag]
    change guardMem (qEnd+4*F.limbs)=1 ↔ _
    rw [hbit]
    exact hiff
  · rw [ite_eq_right hInside] at hCap
    have hn : qMem (qEnd-(1+4*F.limbs))≠1 := by omega
    simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch
    rw [ite_eq_right hn] at hbranch
    rw [flagRecord_output hbranch]
    constructor
    · omega
    · intro hsafe
      change (1/(2:ℝ)^E<V up-(V base+A.query s e) ∧ _) ∧
        (1/(2:ℝ)^E<V base+A.query s e-V lo ∧ _) at hsafe
      exact False.elim (hInside ⟨by linarith only [hsafe.2.1,hPos],by linarith only [hsafe.1.1,hPos]⟩)

/-- Every actual reported-edge outcome accepts a candidate whose two
slacks lie in the strict guard range. -/
theorem reportedEdge_accepts_safe {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v final)
    (hsafe : ReportedCandidateSafe F A s mem e base lo up E) : final (v-1)=1 :=
  (reportedEdge_accepts_iff F A G m κ α rate allocation R hpre hout).mpr hsafe

end MinCostFlow.IPM.Machine
