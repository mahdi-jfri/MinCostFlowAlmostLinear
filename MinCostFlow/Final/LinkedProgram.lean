module

public import MinCostFlow.Final.DataStructurePrograms
public import MinCostFlow.Final.WidenedPrograms
public import MinCostFlow.IPM.Machine.SolverCost
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Running the linked minimum-cost flow program

The bounded IPM is the solver in the polynomial-scratch scaling
program. The scaling proof compares solver calls at larger dimensions,
so use the maximum of the IPM time bounds over smaller dimensions.
This maximum is a proof bound and is never computed by the program.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine IPM.Machine

/-- Monotone envelope of the IPM solver's dimension-dependent bound. -/
def linkedSolverTime (r : SolverResources) (n m : ℕ) : ℕ :=
  ((Finset.range (n+1)) ×ˢ (Finset.range (m+1))).sup
    (fun nm => solverTime r nm.1 nm.2)

theorem solverTime_le_linkedSolverTime (r : SolverResources) (n m : ℕ) :
    solverTime r n m ≤ linkedSolverTime r n m := by
  unfold linkedSolverTime
  apply Finset.le_sup (b := (n,m)) (f := fun nm => solverTime r nm.1 nm.2)
  simp

theorem linkedSolverTime_mono (r : SolverResources) : SolverTimeMonotone (linkedSolverTime r) := by
  intro n n' m m' hn hm
  apply Finset.sup_mono
  exact Finset.product_subset_product (Finset.range_mono (by omega)) (Finset.range_mono (by omega))

/-- Monotone envelope of the IPM solver's dimension-dependent bound. -/
def linkedRuntimeSolverTime (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  ((Finset.range (n+1)) ×ˢ (Finset.range (m+1))).sup
    (fun nm => solverRuntimeTime r nm.1 nm.2)

theorem solverRuntimeTime_le_linkedRuntimeSolverTime (r : SolverRuntimeResources) (n m : ℕ) :
    solverRuntimeTime r n m ≤ linkedRuntimeSolverTime r n m := by
  unfold linkedRuntimeSolverTime
  apply Finset.le_sup (b := (n,m)) (f := fun nm => solverRuntimeTime r nm.1 nm.2)
  simp

theorem linkedRuntimeSolverTime_mono (r : SolverRuntimeResources) : SolverTimeMonotone (linkedRuntimeSolverTime r) := by
  intro n n' m m' hn hm
  apply Finset.sup_mono
  exact Finset.product_subset_product (Finset.range_mono (by omega)) (Finset.range_mono (by omega))

theorem solverContract_raise_time {w entry : ℕ} {p : Program} {T T' S : ℕ → ℕ → ℕ}
    (h : MeetsContract w p entry (compressedSolverContract w T S))
    (hTime : ∀ n m, T n m ≤ T' n m) :
    MeetsContract w p entry (compressedSolverContract w T' S) := by
  intro args mem pos ω hwords hpre
  obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := h args mem pos ω hwords hpre
  exact ⟨body,hbody,o,st,c,hr,hpost,hcost.trans (hTime _ _)⟩

/-- The linked solver followed by the outer scaling procedures. -/
def DataStructurePrograms.program (P : DataStructurePrograms) : Program :=
  scratchOuterScalingProgram P.solver 0 1 P.scratchDegree

/-- Linking the two supplied data structures and applying outer scaling
preserves determinism. -/
theorem DataStructurePrograms.program_deterministic (P : DataStructurePrograms) :
    P.program.IsDeterministic :=
  scratchOuterScalingProgram_deterministic _ _ _ _ P.solver_deterministic

/-- The constant in the original-input solver time bound. -/
def DataStructurePrograms.timeConstant (P : DataStructurePrograms) : ℕ :=
  scratchWholeScalingConstant P.solver 1 P.scratchDegree

/-- The linked program runs on the original input encoding, returns the
correct answer, and obeys the counted scaling bound. -/
theorem DataStructurePrograms.program_runsTo (P : DataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
        (linkedRuntimeSolverTime P.runtimeResources (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)+I.m)+
        P.timeConstant*I.n := by
  apply outerScaling_runsTo_compressedPolynomialScratch P.solver 0 (linkedRuntimeSolverTime P.runtimeResources)
    (solverRuntimeWorkspace P.runtimeResources) 1 P.scratchDegree
  · intro J
    exact solverContract_raise_time (P.solver_meetsContract J)
      (solverRuntimeTime_le_linkedRuntimeSolverTime P.runtimeResources)
  · intro n m
    simpa only [Nat.one_mul] using P.workspace_le n m
  · exact P.solver_deterministic
  · exact linkedRuntimeSolverTime_mono P.runtimeResources
  · exact hv

/-- The logarithmic IPM bound for positive edge count, and the advertised
solver bound when there are no edges. -/
noncomputable def linkedSolverLogCost (r : SolverResources) (n m : ℕ) : ℝ :=
  if m = 0 then (solverTime r n 0 : ℝ) else
    let b := 430*Real.log ((m:ℝ)+2)
    let R := (((Finset.Icc m (3*m)).sup r.cycleRate : ℕ) : ℝ)
    500*n+100000*m*(30000000*b^2+3*b+3)+(r.forestRate (n+1):ℝ)*(n+2+30*m)+
      (2+2*b)*(3276800000000001*b^3*((2:ℝ)^r.qualityExponent)^2*
        ((3*(m:ℝ))*(100000000*(30000000*b^2)^3)+(90*(m:ℝ)+1)*R)+3000000000*b^2+419)+30

theorem solverTime_le_linkedSolverLogCost (r : SolverResources) (n m : ℕ) :
    (solverTime r n m : ℝ) ≤ linkedSolverLogCost r n m := by
  by_cases hm : m=0
  · subst m
    simp [linkedSolverLogCost]
  · simpa only [linkedSolverLogCost, ite_eq_right hm] using
      solverTime_log_bound r n m (Nat.pos_of_ne_zero hm)

/-- The selected augmented size supplies the iteration factor and the
cost of computing it. -/
noncomputable def linkedRuntimeLogCost (r : SolverRuntimeResources) (n m M : ℕ) : ℝ :=
  linkedSolverLogCost (r.forSize M) n m + r.qualityCost M

theorem solverRuntimeTime_le_linkedRuntimeLogCost (r : SolverRuntimeResources) (n m : ℕ) :
    ∃ M ∈ Finset.Icc m (3*m), (solverRuntimeTime r n m:ℝ) ≤ linkedRuntimeLogCost r n m M := by
  have hMem : m ∈ Finset.Icc m (3*m) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  obtain ⟨M,hM,hMax⟩ := Finset.exists_mem_eq_sup (Finset.Icc m (3*m)) ⟨m,hMem⟩
    (fun M => solverTimeAt (r.forSize M) n m M + r.qualityCost M)
  refine ⟨M,hM,?_⟩
  have hT : solverRuntimeTime r n m ≤ solverTime (r.forSize M) n m + r.qualityCost M := by
    unfold solverRuntimeTime
    rw [hMax]
    apply max_le
    · exact (le_max_left _ _).trans (Nat.le_add_right _ _)
    · exact Nat.add_le_add_right
        ((Finset.le_sup (f := solverTimeAt (r.forSize M) n m) hM).trans (le_max_right _ _)) _
  have hCast := (Nat.cast_le (α := ℝ)).mpr hT
  rw [Nat.cast_add] at hCast
  exact hCast.trans (add_le_add (solverTime_le_linkedSolverLogCost (r.forSize M) n m) le_rfl)

/-- The linked program satisfies the scaling bound with the explicit IPM
logarithmic cost at a pair of dimensions inside the comparison rectangle. -/
theorem DataStructurePrograms.program_runsTo_log_bound (P : DataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost n m M₀, M₀ ∈ Finset.Icc m (3*m) ∧ n ≤ P.timeConstant*min I.n I.m ∧ m ≤ P.timeConstant*I.m ∧
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      (cost : ℝ) ≤ (P.timeConstant*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2) : ℕ) *
        (linkedRuntimeLogCost P.runtimeResources n m M₀ + I.m) + (P.timeConstant*I.n : ℕ) := by
  obtain ⟨out,cost,hr,hcorrect,hcost⟩ := P.program_runsTo I hv ω
  let N := P.timeConstant*min I.n I.m
  let M := P.timeConstant*I.m
  let rectangle := (Finset.range (N+1)) ×ˢ (Finset.range (M+1))
  have hne : rectangle.Nonempty := ⟨(N,M), by simp [rectangle]⟩
  obtain ⟨⟨n,m⟩,hmem,hmax⟩ :=
    Finset.exists_mem_eq_sup rectangle hne (fun nm => solverRuntimeTime P.runtimeResources nm.1 nm.2)
  have hnm : n ≤ N ∧ m ≤ M := by simpa [rectangle, Nat.lt_succ_iff] using hmem
  have hmax' : solverRuntimeTime P.runtimeResources n m = linkedRuntimeSolverTime P.runtimeResources N M := hmax.symm
  rw [←hmax'] at hcost
  have hc : (cost : ℝ) ≤ (P.timeConstant*(Nat.clog 2 (I.m+1)+1)*
      (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2) : ℕ) *
      ((solverRuntimeTime P.runtimeResources n m : ℝ)+I.m)+(P.timeConstant*I.n : ℕ) := by
    exact_mod_cast hcost
  obtain ⟨M₀,hM₀,hRuntime⟩ := solverRuntimeTime_le_linkedRuntimeLogCost P.runtimeResources n m
  refine ⟨out,cost,n,m,M₀,hM₀,hnm.1,hnm.2,hr,hcorrect,hc.trans ?_⟩
  exact add_le_add_left
    (mul_le_mul_of_nonneg_left
      (add_le_add_left hRuntime _)
      (Nat.cast_nonneg _)) _

/-- Monotone envelope of the IPM solver's dimension-dependent bound. -/
def linkedWidenedSolverTime (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  ((Finset.range (n+1)) ×ˢ (Finset.range (m+1))).sup
    (fun nm => solverQualityRuntimeTime r nm.1 nm.2)

theorem solverQualityRuntimeTime_le_linkedWidenedSolverTime (r : SolverRuntimeResources) (n m : ℕ) :
    solverQualityRuntimeTime r n m ≤ linkedWidenedSolverTime r n m := by
  unfold linkedWidenedSolverTime
  apply Finset.le_sup (b := (n,m)) (f := fun nm => solverQualityRuntimeTime r nm.1 nm.2)
  simp

theorem linkedWidenedSolverTime_mono (r : SolverRuntimeResources) : SolverTimeMonotone (linkedWidenedSolverTime r) := by
  intro n n' m m' hn hm
  apply Finset.sup_mono
  exact Finset.product_subset_product (Finset.range_mono (by omega)) (Finset.range_mono (by omega))

/-- The linked solver followed by the outer scaling procedures. -/
noncomputable def WidenedDataStructurePrograms.program (P : WidenedDataStructurePrograms) : Program :=
  scratchOuterScalingProgram P.solver 0 1 P.scratchDegree

/-- Linking the two supplied data structures and applying outer scaling
preserves determinism. -/
theorem WidenedDataStructurePrograms.program_deterministic (P : WidenedDataStructurePrograms) :
    P.program.IsDeterministic :=
  scratchOuterScalingProgram_deterministic _ _ _ _ P.solver_deterministic

/-- The constant in the original-input solver time bound. -/
noncomputable def WidenedDataStructurePrograms.timeConstant (P : WidenedDataStructurePrograms) : ℕ :=
  scratchWholeScalingConstant P.solver 1 P.scratchDegree

/-- The linked program runs on the original input encoding, returns the
correct answer, and obeys the counted scaling bound. -/
theorem WidenedDataStructurePrograms.program_runsTo (P : WidenedDataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
        (linkedWidenedSolverTime P.runtimeResources (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)+I.m)+
        P.timeConstant*I.n := by
  apply outerScaling_runsTo_compressedPolynomialScratch P.solver 0 (linkedWidenedSolverTime P.runtimeResources)
    (solverQualityRuntimeWorkspace P.runtimeResources) 1 P.scratchDegree
  · intro J
    exact solverContract_raise_time (P.solver_meetsContract J)
      (solverQualityRuntimeTime_le_linkedWidenedSolverTime P.runtimeResources)
  · intro n m
    simpa only [Nat.one_mul] using P.workspace_le n m
  · exact P.solver_deterministic
  · exact linkedWidenedSolverTime_mono P.runtimeResources
  · exact hv

end MinCostFlow.Final
