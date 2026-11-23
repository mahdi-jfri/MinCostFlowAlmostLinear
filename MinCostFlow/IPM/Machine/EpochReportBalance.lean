module

public import MinCostFlow.IPM.Machine.EpochLoopTrace
public import MinCostFlow.IPM.Machine.EpochIterationCharge
import MinCostFlow.IPM.Machine.BudgetedIterationOutput
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The actual remaining budget pays for the next Detect output

The machine starts with five reports per edge as its allowance. Each
accepted call subtracts exactly the size of the report. The sum of
those charges and all pending movement is bounded by the total
movement of the normalized IPM steps, including the deposit just
before the next Detect.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine

/-- Sum the unspent movement over the currently live graph. -/
def epochPendingTotal {τ : Type} (A : MinRatioDataStructure) (P : EpochPoint τ) (i : ℕ) : ℝ :=
  ∑ e ∈ (P.history.G (2*i)).E,epochPendingMovement A P.history P.eta P.op (2*i) e

/-- The actual machine budget plus its real-valued movement balance
accounts for deposits of at most a quarter of the threshold per step. -/
def EpochReportBalance {τ : Type} (A : MinRatioDataStructure) (m : ℕ)
    (eps : ℝ) (i : ℕ) (P : EpochPoint τ) : Prop :=
  eps*((5*m-P.machine.mem (P.machine.regs 8-3):ℕ):ℝ)+epochPendingTotal A P i≤ (i:ℝ)*(eps/4)

/-- Both cumulative accounts start empty at the actual initial record. -/
theorem epochReportBalance_zero {τ : Type} (A : MinRatioDataStructure) (m : ℕ)
    (eps : ℝ) (P : EpochPoint τ) (h : P.machine.mem (P.machine.regs 8-3)=5*m) :
    EpochReportBalance A m eps 0 P := by
  simp [EpochReportBalance,epochPendingTotal,h,epochPendingMovement_zero]

/-- At most (m) IPM steps can spend only a quarter of the threshold
per step. The current Detect output therefore fits the remaining
machine budget, even before any subsequent Update is attempted. -/
theorem epochReportBalance_detect_fits_on {τ : Type} (A : MinRatioDataStructure)
    (m i : ℕ) (P : EpochPoint τ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecOn A κ α Ψ eps
      (appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i)))
      (Function.update P.eta ((2*i)+1) 0) (Function.update P.op ((2*i)+1) false) ((2*i)+1)) (heps : 0<eps) (hi : i≤m)
    (hv : MinRatioHistoryValid P.history P.op (2*i))
    (hbudget : P.machine.mem (P.machine.regs 8-3)≤5*m)
    (hbal : EpochReportBalance A m eps i P) :
    (A.detect (minRatioState A P.history P.eta P.op (2*i))).1.card≤
      P.machine.mem (P.machine.regs 8-3) := by
  classical
  let S := (A.detect (minRatioState A P.history P.eta P.op (2*i))).1
  let rem := P.machine.mem (P.machine.regs 8-3)
  obtain ⟨hsub,hpaid⟩ := epoch_detect_movement_charge_on A P.history P.eta P.op (2*i) κ α Ψ eps hA hv heps.le
  let D := appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i))
  have hvalidD := appendHistoryStage_valid_detect P.history P.op (2*i) hv
  have hp (e : ℕ) (he : e∈(P.history.G (2*i)).E) :
      (if e∈S then eps else 0)≤epochPendingMovement A P.history P.eta P.op (2*i) e := by
    have heD : e∈(D.G (2*i+1)).E := by
      simpa only [D,appendHistoryStage,Function.update_self] using he
    have hn := epochPendingMovement_nonneg A D (Function.update P.eta (2*i+1) 0) _ _ e hvalidD heD
    exact (le_add_of_nonneg_right hn).trans (hpaid e he).1
  have hcharge := Finset.sum_le_sum (s:=(P.history.G (2*i)).E) (fun e he => hp e he)
  rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr (show S⊆_ from hsub)] at hcharge
  simp only [Finset.sum_const,nsmul_eq_mul,mul_comm (S.card:ℝ)] at hcharge
  change eps*(S.card:ℝ)≤epochPendingTotal A P i at hcharge
  have hcurrent : eps*((5*m-rem:ℕ):ℝ)+epochPendingTotal A P i≤ (i:ℝ)*(eps/4) := hbal
  have hi' : (i:ℝ)≤m := by exact_mod_cast hi
  have hmR : (0:ℝ)≤m := Nat.cast_nonneg m
  have hlimit : (i:ℝ)*(eps/4)≤(5*(m:ℝ))*eps := by
    have h1 := mul_le_mul_of_nonneg_right hi' heps.le
    have h2 := mul_nonneg hmR heps.le
    linarith only [h1,h2]
  have hcount : (S.card:ℝ)+((5*m-rem:ℕ):ℝ)≤(5*m:ℕ) := by
    apply (mul_le_mul_iff_right₀ heps).mp
    push_cast
    nlinarith only [hcharge,hcurrent,hlimit]
  have hn : S.card+(5*m-rem)≤5*m := by exact_mod_cast hcount
  change rem≤5*m at hbudget
  change S.card≤rem
  omega

/-- At most (m) IPM steps can spend only a quarter of the threshold
per step. The current Detect output therefore fits the remaining
machine budget, even before any subsequent Update is attempted. -/
theorem epochReportBalance_detect_fits {τ : Type} (A : MinRatioDataStructure)
    (m i : ℕ) (P : EpochPoint τ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpec A κ α Ψ eps) (heps : 0<eps) (hi : i≤m)
    (hv : MinRatioHistoryValid P.history P.op (2*i))
    (hbudget : P.machine.mem (P.machine.regs 8-3)≤5*m)
    (hbal : EpochReportBalance A m eps i P) :
    (A.detect (minRatioState A P.history P.eta P.op (2*i))).1.card≤
      P.machine.mem (P.machine.regs 8-3) := by
  have hSpec := hA (appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i)))
    (Function.update P.eta ((2*i)+1) 0) (Function.update P.op ((2*i)+1) false) ((2*i)+1)
    (appendHistoryStage_valid_detect P.history P.op (2*i) hv)
  exact epochReportBalance_detect_fits_on A m i P κ α Ψ eps hSpec heps hi hv hbudget hbal

/-- Close the balance after a successful actual step. The deposited
movement is measured in the very coefficients used by that Update. -/
theorem epochReportBalance_step_on {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (q K i : ℕ) (P Q : EpochPoint R.τ)
    (hA : MinRatioSpecOn A.eraseFailure κ α Ψ eps
      (appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i)))
      (Function.update P.eta ((2*i)+1) 0) (Function.update P.op ((2*i)+1) false) ((2*i)+1)) (heps : 0≤eps)
    (hp : MinRatioHistoryValid P.history P.op (2*i))
    (hq : MinRatioHistoryValid Q.history Q.op (2*(i+1)))
    (hbudget : P.machine.mem (P.machine.regs 8-3)≤5*I.m)
    (hbal : EpochReportBalance A.eraseFailure I.m eps i P)
    (hstep : EpochAcceptedStep F A I κ α rate allocation R L q K i P Q)
    (hmove : (Q.history.G (2*(i+1))).lnorm (Q.history.ℓ (2*(i+1)))
      (minRatioIncrement A.eraseFailure Q.history Q.eta Q.op (2*(i+1)))≤eps/4) :
    EpochReportBalance A.eraseFailure I.m eps (i+1) Q := by
  obtain ⟨hbit,hout,es,actual,_,_,_,_,_,_,_,hset,hist,heta,hop,_⟩ := hstep
  have hspent := (budgetedIteration_output hout).2.2 hbit
  rw [L.packet_heap] at hspent
  have hindex : 2*i+1+1=2*(i+1) := by omega
  have hq' := hq
  rw [← hindex,hist,hop] at hq'
  have hcharge := epoch_iteration_movement_charge_on A.eraseFailure P.history P.eta P.op (2*i)
    κ α Ψ eps hA hp heps es _ _ actual hset hq' |>.1
  rw [← hist,← heta,← hop,hindex] at hcharge
  let S := (A.detect (minRatioState A.eraseFailure P.history P.eta P.op (2*i))).1
  let r := P.machine.mem (P.machine.regs 8-3)
  let r' := Q.machine.mem (Q.machine.regs 8-3)
  change r'+S.card=r at hspent
  change r≤5*I.m at hbudget
  have heq : 5*I.m-r'=(5*I.m-r)+S.card := by omega
  have hh : eps*(S.card:ℝ)+epochPendingTotal A.eraseFailure Q (i+1)≤
      epochPendingTotal A.eraseFailure P i+eps/4 :=
    hcharge.trans (add_le_add_right hmove _)
  change eps*((5*I.m-r:ℕ):ℝ)+epochPendingTotal A.eraseFailure P i≤ (i:ℝ)*(eps/4) at hbal
  change eps*((5*I.m-r':ℕ):ℝ)+epochPendingTotal A.eraseFailure Q (i+1)≤((i+1:ℕ):ℝ)*(eps/4)
  rw [heq]
  push_cast
  linarith only [hh,hbal]

/-- Close the balance after a successful actual step. The deposited
movement is measured in the very coefficients used by that Update. -/
theorem epochReportBalance_step {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (q K i : ℕ) (P Q : EpochPoint R.τ)
    (hA : MinRatioSpec A.eraseFailure κ α Ψ eps) (heps : 0≤eps)
    (hp : MinRatioHistoryValid P.history P.op (2*i))
    (hq : MinRatioHistoryValid Q.history Q.op (2*(i+1)))
    (hbudget : P.machine.mem (P.machine.regs 8-3)≤5*I.m)
    (hbal : EpochReportBalance A.eraseFailure I.m eps i P)
    (hstep : EpochAcceptedStep F A I κ α rate allocation R L q K i P Q)
    (hmove : (Q.history.G (2*(i+1))).lnorm (Q.history.ℓ (2*(i+1)))
      (minRatioIncrement A.eraseFailure Q.history Q.eta Q.op (2*(i+1)))≤eps/4) :
    EpochReportBalance A.eraseFailure I.m eps (i+1) Q := by
  have hSpec := hA (appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i)))
    (Function.update P.eta ((2*i)+1) 0) (Function.update P.op ((2*i)+1) false) ((2*i)+1)
    (appendHistoryStage_valid_detect P.history P.op (2*i) hp)
  exact epochReportBalance_step_on F A I κ α Ψ eps rate allocation R L q K i P Q hSpec heps hp
    hq hbudget hbal hstep hmove

end MinCostFlow.IPM.Machine
