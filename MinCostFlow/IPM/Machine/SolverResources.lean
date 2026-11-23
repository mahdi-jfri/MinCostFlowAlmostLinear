module

public import MinCostFlow.IPM.Machine.SolverFinish
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Total time and space of the bounded circulation solver

Only the augmented edge count is unknown from the input dimensions.
It lies in an interval from (m) through (3m). The advertised
bounds take the maximum of the actual reservations and operation
counts on that interval. The maxima are bounds on the run and
are never computed by the machine.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Cost at particular original and augmented dimensions. -/
def solverTimeAt (r : SolverResources) (n m M : ℕ) : ℕ :=
  let N := n+1
  let V := solverPenalty m
  let L := ipmLimbs M V
  let F := ipmMinRatioFormat M V (w:=ipmParameterWordBits M V) le_rfl
  300*m+400*n+M*(200*L+600)+20028*(M.size+V.size)+23000+
  (30*N+M*(600*L+1900)+36*L+1800)+
  (14*(M.size+V.size+targetSearchRounds (M*V^2))+550)+
  targetSearchCost F M V r.qualityExponent F.rangeExponent r.cycleRate+
  (roundMachineCost (r.forestRate N) L N M+17*(M*L)+m*(100*L+240)+100)+1200

/-- The actual reservations of all fresh blocks. -/
def solverWorkspaceAt (r : SolverResources) (n m M : ℕ) : ℕ :=
  let N := n+1
  let V := solverPenalty m
  let L := ipmLimbs M V
  let F := ipmMinRatioFormat M V (w:=ipmParameterWordBits M V) le_rfl
  (2+5*m+7*n+7+L+4*(M*L))+
  (2+N+3*M+(9*M+1)*L+5*L)+5+
  targetSearchSpace F M V r.qualityExponent F.rangeExponent (r.cycleSpace N M)+
  (M*L+roundMachineSpace (r.forestInitSpace N M) (r.forestOpSpace N M) L M+recoverScanSpace L m)

/-- Numeric word width independent of the caller's address. -/
def solverNumericWidthAt (r : SolverResources) (m M : ℕ) : ℕ :=
  let V := solverPenalty m
  max (ipmParameterWordBits M V)
    (max (2*(M*V^2)).size (max (targetTestLimit M V r.qualityExponent).size
      (max (M.size+V.size).size r.qualityExponent.size)))

/-- Overall time bound for input dimensions (n,m). -/
def solverTime (r : SolverResources) (n m : ℕ) : ℕ :=
  max 30 ((Finset.Icc m (3*m)).sup (solverTimeAt r n m))

/-- Overall scratch at a caller-supplied heap. The numeric guard ensures
this same contract is valid even when a caller supplies a smaller word
width than the usual canonical `wordSize c`. The unused tail stays zero. -/
def solverWorkspace (r : SolverResources) (n m : ℕ) : ℕ :=
  if m=0 then 0 else
    (Finset.Icc m (3*m)).sup
      (fun M => max (solverWorkspaceAt r n m M) (2^solverNumericWidthAt r m M))

/-- Resources for a solver that obtains its quality from the augmented
edge count. The allocation and data-structure rates are shared across sizes. -/
structure SolverRuntimeResources where
  template : SolverResources
  qualityExponent : ℕ → ℕ
  qualityCost : ℕ → ℕ

/-- The inner solver receives the quality for the graph it actually uses. -/
def SolverRuntimeResources.forSize (r : SolverRuntimeResources) (M : ℕ) : SolverResources :=
  {r.template with qualityExponent := r.qualityExponent M}

/-- Time envelope over the augmented sizes, including the quality computation. -/
def solverRuntimeTime (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  max 30 ((Finset.Icc m (3*m)).sup fun M =>
    solverTimeAt (r.forSize M) n m M + r.qualityCost M)

/-- Scratch envelope uses the numeric width for each candidate augmented size. -/
def solverRuntimeWorkspace (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  if m=0 then 0 else
    (Finset.Icc m (3*m)).sup fun M =>
      max (solverWorkspaceAt (r.forSize M) n m M) (2^solverNumericWidthAt (r.forSize M) m M)

/-- Cost at particular original and augmented dimensions. -/
def solverQualityTimeAt (r : SolverResources) (n m M : ℕ) : ℕ :=
  let N := n+1
  let V := solverPenalty m
  let L := ipmQualityLimbs M V r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent (w:=ipmQualityParameterWordBits M V r.qualityExponent) le_rfl
  300*m+400*n+M*(200*L+600)+20028*(M.size+V.size)+23020+
  (30*N+M*(600*L+1900)+36*L+1800)+
  (14*(M.size+V.size+targetSearchRounds (M*V^2))+550)+
  targetSearchCost F M V r.qualityExponent F.rangeExponent r.cycleRate+
  (roundMachineCost (r.forestRate N) L N M+17*(M*L)+m*(100*L+240)+100)+1200

/-- The actual reservations of all fresh blocks. -/
def solverQualityWorkspaceAt (r : SolverResources) (n m M : ℕ) : ℕ :=
  let N := n+1
  let V := solverPenalty m
  let L := ipmQualityLimbs M V r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent (w:=ipmQualityParameterWordBits M V r.qualityExponent) le_rfl
  (2+5*m+7*n+7+L+4*(M*L))+
  (2+N+3*M+(9*M+1)*L+5*L)+5+
  targetSearchSpace F M V r.qualityExponent F.rangeExponent (r.cycleSpace N M)+
  (M*L+roundMachineSpace (r.forestInitSpace N M) (r.forestOpSpace N M) L M+recoverScanSpace L m)

/-- Numeric word width independent of the caller's address. -/
def solverQualityNumericWidthAt (r : SolverResources) (m M : ℕ) : ℕ :=
  let V := solverPenalty m
  max (ipmQualityParameterWordBits M V r.qualityExponent)
    (max (2*(M*V^2)).size (max (targetTestLimit M V r.qualityExponent).size
      (max (M.size+V.size).size r.qualityExponent.size)))

/-- Time envelope over the augmented sizes, including the quality computation. -/
def solverQualityRuntimeTime (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  max 30 ((Finset.Icc m (3*m)).sup fun M =>
    solverQualityTimeAt (r.forSize M) n m M + 2*r.qualityCost M)

/-- Scratch envelope uses the numeric width for each candidate augmented size. -/
def solverQualityRuntimeWorkspace (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  if m=0 then 0 else
    (Finset.Icc m (3*m)).sup fun M =>
      max (solverQualityWorkspaceAt (r.forSize M) n m M) (2^solverQualityNumericWidthAt (r.forSize M) m M)

/-- The runtime envelopes cover the actual augmented dimensions. -/
theorem solverQualityRuntimeWorkspace_covers (r : SolverRuntimeResources) (J : Circulation)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e) :
    let M := (solverAugmented J).m
    solverQualityWorkspaceAt (r.forSize M) J.n J.m M ≤ solverQualityRuntimeWorkspace r J.n J.m ∧
      2^solverQualityNumericWidthAt (r.forSize M) J.m M ≤ solverQualityRuntimeWorkspace r J.n J.m ∧
      solverQualityTimeAt (r.forSize M) J.n J.m M + 2*r.qualityCost M ≤ solverQualityRuntimeTime r J.n J.m := by
  dsimp only
  have hMem := Finset.mem_Icc.mpr (solverAugmented_size J hp)
  unfold solverQualityRuntimeWorkspace solverQualityRuntimeTime
  rw [ite_eq_right hm.ne']
  have hMax := Finset.le_sup (f := fun M => max (solverQualityWorkspaceAt (r.forSize M) J.n J.m M)
    (2^solverQualityNumericWidthAt (r.forSize M) J.m M)) hMem
  exact ⟨(le_max_left _ _).trans hMax, (le_max_right _ _).trans hMax,
    (Finset.le_sup (f := fun M => solverQualityTimeAt (r.forSize M) J.n J.m M + 2*r.qualityCost M)
      hMem).trans (le_max_right _ _)⟩

/-- The runtime envelopes cover the actual augmented dimensions. -/
theorem solverRuntimeWorkspace_covers (r : SolverRuntimeResources) (J : Circulation)
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e) :
    let M := (solverAugmented J).m
    solverWorkspaceAt (r.forSize M) J.n J.m M ≤ solverRuntimeWorkspace r J.n J.m ∧
      2^solverNumericWidthAt (r.forSize M) J.m M ≤ solverRuntimeWorkspace r J.n J.m ∧
      solverTimeAt (r.forSize M) J.n J.m M + r.qualityCost M ≤ solverRuntimeTime r J.n J.m := by
  dsimp only
  have hMem := Finset.mem_Icc.mpr (solverAugmented_size J hp)
  unfold solverRuntimeWorkspace solverRuntimeTime
  rw [ite_eq_right hm.ne']
  have hMax := Finset.le_sup (f := fun M => max (solverWorkspaceAt (r.forSize M) J.n J.m M)
    (2^solverNumericWidthAt (r.forSize M) J.m M)) hMem
  exact ⟨(le_max_left _ _).trans hMax, (le_max_right _ _).trans hMax,
    (Finset.le_sup (f := fun M => solverTimeAt (r.forSize M) J.n J.m M + r.qualityCost M)
      hMem).trans (le_max_right _ _)⟩

/-- Numeric widths and actual allocation fit whenever the advertised
scratch fits. This is derived from the shared solver precondition. -/
theorem solverWorkspace_covers (r : SolverResources) (J : Circulation) (hm : 0 < J.m)
    (hp : ∀ e,1≤J.capacity e) :
    let M := (solverAugmented J).m
    solverWorkspaceAt r J.n J.m M≤solverWorkspace r J.n J.m ∧
      2^solverNumericWidthAt r J.m M≤solverWorkspace r J.n J.m ∧
      solverTimeAt r J.n J.m M≤solverTime r J.n J.m := by
  dsimp only
  have hM := solverAugmented_size J hp
  have hMem : (solverAugmented J).m ∈ Finset.Icc J.m (3*J.m) := Finset.mem_Icc.mpr hM
  unfold solverWorkspace solverTime
  rw [ite_eq_right (Nat.ne_of_gt hm)]
  have hMax := Finset.le_sup (f:=fun M => max (solverWorkspaceAt r J.n J.m M)
    (2^solverNumericWidthAt r J.m M)) hMem
  exact ⟨(le_max_left _ _).trans hMax,(le_max_right _ _).trans hMax,
    (Finset.le_sup (f:=solverTimeAt r J.n J.m) hMem).trans (le_max_right _ _)⟩

/-- The actual geometric call sizes agree with the advertised
dimension-only quantities. The cost and allocation formulas use no
word-width dependent operation beyond the chosen format. -/
theorem solverWorkspaceAt_eq {w : ℕ} (r : SolverResources) (J : Circulation)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let L := ipmLimbs I.m V
    solverWorkspaceAt r J.n J.m I.m = solverInitializeSpace J+
      solverSearchSetupSpace I L+5+solverSearchReserve r I V hw+solverRecoveryReserve r I V J.m := by
  rfl

/-- Likewise for the total time, including only a fixed overhead
beyond the verified procedure charges. -/
theorem solverTimeAt_eq {w : ℕ} (r : SolverResources) (J : Circulation)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let L := ipmLimbs I.m V
    solverTimeAt r J.n J.m I.m = solverInitializeCost J+
      (30*I.n+I.m*(600*L+1900)+36*L+1800)+
      (14*(I.m.size+V.size+targetSearchRounds (I.m*V^2))+550)+
      solverSearchCharge r I V hw+solverRecoveryCharge r I V J.m+1200 := by
  rfl

/-- The actual geometric call sizes agree with the advertised
dimension-only quantities. The cost and allocation formulas use no
word-width dependent operation beyond the chosen format. -/
theorem solverQualityWorkspaceAt_eq {w : ℕ} (r : SolverResources) (J : Circulation)
    (hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) r.qualityExponent≤w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let L := ipmQualityLimbs I.m V r.qualityExponent
    solverQualityWorkspaceAt r J.n J.m I.m = solverQualityInitializeSpace J r.qualityExponent+
      solverSearchSetupSpace I L+5+solverQualitySearchReserve r I V hw+solverQualityRecoveryReserve r I V J.m := by
  rfl

/-- Likewise for the total time, including only a fixed overhead
beyond the verified procedure charges. -/
theorem solverQualityTimeAt_eq {w : ℕ} (r : SolverResources) (J : Circulation)
    (hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) r.qualityExponent≤w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let L := ipmQualityLimbs I.m V r.qualityExponent
    solverQualityTimeAt r J.n J.m I.m = solverQualityInitializeCost J r.qualityExponent 0+
      (30*I.n+I.m*(600*L+1900)+36*L+1800)+
      (14*(I.m.size+V.size+targetSearchRounds (I.m*V^2))+550)+
      solverQualitySearchCharge r I V hw+solverQualityRecoveryCharge r I V J.m+1200 := by
  rfl

end MinCostFlow.IPM.Machine
