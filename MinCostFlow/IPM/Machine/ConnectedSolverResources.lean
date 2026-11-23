module

public import MinCostFlow.IPM.Machine.SolverResources
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize

/-!
# Cost and workspace of the connected solver

The extra hub records enlarge the startup charge and reservation.
The envelopes cover every augmented size up to seven times the
compressed input size.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

/-- Cost of the connected solver at its actual augmented size. -/
def connectedSolverTimeAt (r : SolverResources) (n m M : ℕ) : ℕ :=
  let N := n+1
  let V := solverPenalty m
  let L := ipmQualityLimbs M V r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent (w:=ipmQualityParameterWordBits M V r.qualityExponent) le_rfl
  300*m+900*n+M*(200*L+600)+20028*(M.size+V.size)+23420+
  (30*N+M*(600*L+1900)+36*L+1800)+
  (14*(M.size+V.size+targetSearchRounds (M*V^2))+550)+
  targetSearchCost F M V r.qualityExponent F.rangeExponent r.cycleRate+
  (roundMachineCost (r.forestRate N) L N M+17*(M*L)+m*(100*L+240)+100)+1200

/-- The actual reservations of all fresh blocks. -/
def connectedSolverWorkspaceAt (r : SolverResources) (n m M : ℕ) : ℕ :=
  let N := n+1
  let V := solverPenalty m
  let L := ipmQualityLimbs M V r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent (w:=ipmQualityParameterWordBits M V r.qualityExponent) le_rfl
  (2+5*m+17*n+7+L+4*(M*L))+
  (2+N+3*M+(9*M+1)*L+5*L)+5+
  targetSearchSpace F M V r.qualityExponent F.rangeExponent (r.cycleSpace N M)+
  (M*L+roundMachineSpace (r.forestInitSpace N M) (r.forestOpSpace N M) L M+recoverScanSpace L m)

/-- Time envelope over the augmented sizes, including the quality computation. -/
def connectedSolverRuntimeTime (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  max 30 ((Finset.Icc m (7*m)).sup fun M =>
    connectedSolverTimeAt (r.forSize M) n m M + 2*r.qualityCost M)

/-- Scratch envelope uses the numeric width for each candidate augmented size. -/
def connectedSolverRuntimeWorkspace (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  if m=0 then 0 else
    (Finset.Icc m (7*m)).sup fun M =>
      max (connectedSolverWorkspaceAt (r.forSize M) n m M) (2^solverQualityNumericWidthAt (r.forSize M) m M)

/-- The runtime envelopes cover the actual augmented dimensions. -/
theorem connectedSolverRuntimeWorkspace_covers (r : SolverRuntimeResources) (J : Circulation)
    (hn : J.n ≤ 2*J.m+1) (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e) :
    let M := (solverConnectedAugmented J).m
    connectedSolverWorkspaceAt (r.forSize M) J.n J.m M ≤ connectedSolverRuntimeWorkspace r J.n J.m ∧
      2^solverQualityNumericWidthAt (r.forSize M) J.m M ≤ connectedSolverRuntimeWorkspace r J.n J.m ∧
      connectedSolverTimeAt (r.forSize M) J.n J.m M + 2*r.qualityCost M ≤ connectedSolverRuntimeTime r J.n J.m := by
  dsimp only
  have hMem := Finset.mem_Icc.mpr (solverConnectedAugmented_size J hn hm hp)
  unfold connectedSolverRuntimeWorkspace connectedSolverRuntimeTime
  rw [ite_eq_right hm.ne']
  have hMax := Finset.le_sup (f := fun M => max (connectedSolverWorkspaceAt (r.forSize M) J.n J.m M)
    (2^solverQualityNumericWidthAt (r.forSize M) J.m M)) hMem
  exact ⟨(le_max_left _ _).trans hMax, (le_max_right _ _).trans hMax,
    (Finset.le_sup (f := fun M => connectedSolverTimeAt (r.forSize M) J.n J.m M + 2*r.qualityCost M)
      hMem).trans (le_max_right _ _)⟩

theorem connectedSolverWorkspaceAt_eq {w : ℕ} (r : SolverResources) (J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let L := ipmQualityLimbs I.m V r.qualityExponent
    connectedSolverWorkspaceAt r J.n J.m I.m = connectedSolverInitializeSpace J r.qualityExponent+
      solverSearchSetupSpace I L+5+solverQualitySearchReserve r I V hw+solverQualityRecoveryReserve r I V J.m := by
  rfl

/-- Likewise for the total time, including only a fixed overhead
beyond the verified procedure charges. -/
theorem connectedSolverTimeAt_eq {w : ℕ} (r : SolverResources) (J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent≤w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let L := ipmQualityLimbs I.m V r.qualityExponent
    connectedSolverTimeAt r J.n J.m I.m = connectedSolverInitializeCost J r.qualityExponent 0+
      (30*I.n+I.m*(600*L+1900)+36*L+1800)+
      (14*(I.m.size+V.size+targetSearchRounds (I.m*V^2))+550)+
      solverQualitySearchCharge r I V hw+solverQualityRecoveryCharge r I V J.m+1200 := by
  rfl

/-- Runtime resources whose forest rate/op-space depend on `L` and allocation depends on `(w, L)`. -/
structure SolverForestRuntimeResources where
  template : SolverForestResources
  qualityExponent : ℕ → ℕ
  qualityCost : ℕ → ℕ

/-- Specialize runtime quality to a candidate augmented edge count `M`. -/
def SolverForestRuntimeResources.forSize (r : SolverForestRuntimeResources) (M : ℕ) : SolverForestResources :=
  { r.template with qualityExponent := r.qualityExponent M }

/-- Convert `SolverRuntimeResources` into `SolverForestRuntimeResources`. -/
def SolverRuntimeResources.toForest (r : SolverRuntimeResources) : SolverForestRuntimeResources where
  template := r.template.toForestResources
  qualityExponent := r.qualityExponent
  qualityCost := r.qualityCost

/-- Numeric word width depending only on `qualityExponent`. -/
def solverQualityForestNumericWidthAt (r : SolverForestResources) (m M : ℕ) : ℕ :=
  let V := solverPenalty m
  max (ipmQualityParameterWordBits M V r.qualityExponent)
    (max (2 * (M * V ^ 2)).size (max (targetTestLimit M V r.qualityExponent).size
      (max (M.size + V.size).size r.qualityExponent.size)))

/-- Cost of the connected solver at its actual augmented size with `L`-dependent forest rate. -/
def forestConnectedSolverTimeAt (r : SolverForestResources) (n m M : ℕ) : ℕ :=
  let N := n + 1
  let V := solverPenalty m
  let L := ipmQualityLimbs M V r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent (w := ipmQualityParameterWordBits M V r.qualityExponent) le_rfl
  300 * m + 900 * n + M * (200 * L + 600) + 20028 * (M.size + V.size) + 23420 +
  (30 * N + M * (600 * L + 1900) + 36 * L + 1800) +
  (14 * (M.size + V.size + targetSearchRounds (M * V ^ 2)) + 550) +
  targetSearchCost F M V r.qualityExponent F.rangeExponent r.cycleRate +
  (roundMachineCost (r.forestRate N L) L N M + 17 * (M * L) + m * (100 * L + 240) + 100) + 1200

/-- Reservations of fresh blocks with `L`-dependent forest operation space. -/
def forestConnectedSolverWorkspaceAt (r : SolverForestResources) (n m M : ℕ) : ℕ :=
  let N := n + 1
  let V := solverPenalty m
  let L := ipmQualityLimbs M V r.qualityExponent
  let F := ipmQualityMinRatioFormat M V r.qualityExponent (w := ipmQualityParameterWordBits M V r.qualityExponent) le_rfl
  (2 + 5 * m + 17 * n + 7 + L + 4 * (M * L)) +
  (2 + N + 3 * M + (9 * M + 1) * L + 5 * L) + 5 +
  targetSearchSpace F M V r.qualityExponent F.rangeExponent (r.cycleSpace N M) +
  (M * L + roundMachineSpace (r.forestInitSpace N M) (r.forestOpSpace L N M) L M + recoverScanSpace L m)

/-- Time envelope over augmented sizes for `SolverForestRuntimeResources`. -/
def forestConnectedSolverRuntimeTime (r : SolverForestRuntimeResources) (n m : ℕ) : ℕ :=
  max 30 ((Finset.Icc m (7 * m)).sup fun M =>
    forestConnectedSolverTimeAt (r.forSize M) n m M + 2 * r.qualityCost M)

/-- Scratch envelope over augmented sizes for `SolverForestRuntimeResources`. -/
def forestConnectedSolverRuntimeWorkspace (r : SolverForestRuntimeResources) (n m : ℕ) : ℕ :=
  if m = 0 then 0 else
    (Finset.Icc m (7 * m)).sup fun M =>
      max (forestConnectedSolverWorkspaceAt (r.forSize M) n m M)
        (2 ^ solverQualityForestNumericWidthAt (r.forSize M) m M)

theorem forestConnectedSolverRuntimeWorkspace_covers (r : SolverForestRuntimeResources) (J : Circulation)
    (hn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let M := (solverConnectedAugmented J).m
    forestConnectedSolverWorkspaceAt (r.forSize M) J.n J.m M ≤ forestConnectedSolverRuntimeWorkspace r J.n J.m ∧
      2 ^ solverQualityForestNumericWidthAt (r.forSize M) J.m M ≤ forestConnectedSolverRuntimeWorkspace r J.n J.m ∧
      forestConnectedSolverTimeAt (r.forSize M) J.n J.m M + 2 * r.qualityCost M ≤ forestConnectedSolverRuntimeTime r J.n J.m := by
  dsimp only
  have hMem := Finset.mem_Icc.mpr (solverConnectedAugmented_size J hn hm hp)
  unfold forestConnectedSolverRuntimeWorkspace forestConnectedSolverRuntimeTime
  rw [ite_eq_right hm.ne']
  have hMax := Finset.le_sup (f := fun M => max (forestConnectedSolverWorkspaceAt (r.forSize M) J.n J.m M)
    (2 ^ solverQualityForestNumericWidthAt (r.forSize M) J.m M)) hMem
  exact ⟨(le_max_left _ _).trans hMax, (le_max_right _ _).trans hMax,
    (Finset.le_sup (f := fun M => forestConnectedSolverTimeAt (r.forSize M) J.n J.m M + 2 * r.qualityCost M)
      hMem).trans (le_max_right _ _)⟩

theorem forestConnectedSolverWorkspaceAt_eq {w : ℕ} (r : SolverForestResources) (J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let L := ipmQualityLimbs I.m V r.qualityExponent
    forestConnectedSolverWorkspaceAt r J.n J.m I.m = connectedSolverInitializeSpace J r.qualityExponent +
      solverSearchSetupSpace I L + 5 + solverQualityForestSearchReserve r I V hw +
      solverQualityForestRecoveryReserve r I V J.m := by
  rfl

theorem forestConnectedSolverTimeAt_eq {w : ℕ} (r : SolverForestResources) (J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) r.qualityExponent ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let L := ipmQualityLimbs I.m V r.qualityExponent
    forestConnectedSolverTimeAt r J.n J.m I.m = connectedSolverInitializeCost J r.qualityExponent 0 +
      (30 * I.n + I.m * (600 * L + 1900) + 36 * L + 1800) +
      (14 * (I.m.size + V.size + targetSearchRounds (I.m * V ^ 2)) + 550) +
      solverQualityForestSearchCharge r I V hw + solverQualityForestRecoveryCharge r I V J.m + 1200 := by
  rfl

end MinCostFlow.IPM.Machine
