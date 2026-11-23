module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract
public import MinCostFlow.IPM.Machine.CachedCoefficientCongr

/-!
# Framing the complete cache postcondition

A tail refresh preserves an earlier name's source and coefficient
blocks. This keeps its exact recovered coordinate relative to the base
flow and both coefficient error bounds. The claim only needs equality
of those blocks, allowing unrelated flow entries in the same prefix to
change during the tail.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Equality on the selected base, flow, coefficient and numeric source
blocks preserves the complete reported-cache program postcondition. -/
theorem reportedCachePost_congr {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (s : A.State)
    {m q base lo up f c r a ld gd e : ℕ} {mem mem' : ℕ → ℕ}
    (hblocks : ∀ p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,f+e*F.limbs,
      up+e*F.limbs,a,ld+e*F.limbs,gd+e*F.limbs],
      ∀ i<F.limbs,mem' (p+i)=mem (p+i))
    (hpost : reportedCachePost F A s m q base lo up f c r a ld gd e mem) :
    reportedCachePost F A s m q base lo up f c r a ld gd e mem' := by
  have hfix (p : ℕ) (hp : p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,f+e*F.limbs,
      up+e*F.limbs,a,ld+e*F.limbs,gd+e*F.limbs]) :
      Num.fixVal mem' p F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem p F.fmt.limbBits F.limbs F.fmt.precision := by
    unfold Num.fixVal
    rw [Num.intVal_congr (hblocks p hp)]
  have haccOld := And.intro hpost.2.2.1 (And.intro hpost.2.2.2.1
    (And.intro hpost.2.2.2.2.1 hpost.2.2.2.2.2.1))
  have hcoef := cached_coefficient_accuracy_congr
    (h:=F.fmt.limbBits) (q:=q) (m:=m) (c:=c+e*F.limbs) (r:=r)
    (lo:=lo+e*F.limbs) (f:=f+e*F.limbs) (up:=up+e*F.limbs) (a:=a)
    (L:=F.limbs) (P:=F.fmt.precision) (ld:=ld+e*F.limbs) (gd:=gd+e*F.limbs)
    (fun p hp => hblocks p (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
      tauto))
    (by simpa only [Num.IPM.arrayLength,Num.IPM.arrayGradient,Nat.zero_mul,Nat.add_zero] using haccOld)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [hblocks (f+e*F.limbs) (by simp) i hi]
    exact hpost.1 i hi
  · rw [hfix (f+e*F.limbs) (by simp),hfix (base+e*F.limbs) (by simp)]
    exact hpost.2.1
  · have hin : Num.fixVal mem' (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem' (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
        Num.fixVal mem' (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem' (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
      rw [hfix (lo+e*F.limbs) (by simp),hfix (f+e*F.limbs) (by simp),hfix (up+e*F.limbs) (by simp)]
      exact hpost.2.2.2.2.2.2
    simpa only [Num.IPM.arrayLength,Num.IPM.arrayGradient,Nat.zero_mul,Nat.add_zero] using
      And.intro hcoef.1 (And.intro hcoef.2.1 (And.intro hcoef.2.2.1 (And.intro hcoef.2.2.2 hin)))

end MinCostFlow.IPM.Machine
