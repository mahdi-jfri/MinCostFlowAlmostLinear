module

public import MinCostFlow.IPM.Machine.RoundEdge
import Mathlib.Tactic

/-!
# A remaining-work bound for the rounding edge scan

One scan step uses a fixed allowance. An additional allowance is
consumed only when a forest edge is cut. The model's link count
bounds the total number of cuts by the number of input edges.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- Workspace for unprocessed edges and all possible remaining cuts. -/
def roundSuffixSpace (A L m k cuts : ℕ) : ℕ :=
  (m-k)*roundEdgeSpace A L 0+(m-cuts)*(2*(A+4+2*L)+A)

/-- Time for unprocessed edges and all possible remaining cuts.
The constant includes decoding the row and the scan call overhead. -/
def roundSuffixCost (rate L m k cuts : ℕ) : ℕ :=
  (m-k)*(roundEdgeCost rate L 0+19*L+250)+
    (m-cuts)*(2*(rate+19*L+80)+(rate+17*L+115))+2

/-- One edge consumes only the fixed charge and the charge for the
cuts it actually performs. -/
theorem roundSuffixSpace_step (A L m k cuts cuts' : ℕ)
    (hk : k<m) (hp : cuts≤cuts') (hq : cuts'≤m) :
    roundSuffixSpace A L m k cuts =
      roundEdgeSpace A L (cuts'-cuts)+roundSuffixSpace A L m (k+1) cuts' := by
  have h₁ : m-k=(m-(k+1))+1 := by omega
  have h₂ : m-cuts=(m-cuts')+(cuts'-cuts) := by omega
  unfold roundSuffixSpace
  rw [h₁,h₂,Nat.add_mul,Nat.add_mul,Nat.one_mul]
  have he : roundEdgeSpace A L (cuts'-cuts)=roundEdgeSpace A L 0+(cuts'-cuts)*(2*(A+4+2*L)+A) := by
    simp [roundEdgeSpace,roundCleanupCharge,Nat.mul_comm,Nat.add_assoc]
  omega

/-- Time charges for the current and all subsequent edges telescope. -/
theorem roundSuffixCost_step (rate L m k cuts cuts' : ℕ)
    (hk : k<m) (hp : cuts≤cuts') (hq : cuts'≤m) :
    roundSuffixCost rate L m k cuts =
      roundEdgeCost rate L (cuts'-cuts)+19*L+250+roundSuffixCost rate L m (k+1) cuts' := by
  have h₁ : m-k=(m-(k+1))+1 := by omega
  have h₂ : m-cuts=(m-cuts')+(cuts'-cuts) := by omega
  unfold roundSuffixCost
  rw [h₁,h₂,Nat.add_mul,Nat.add_mul,Nat.one_mul]
  have he : roundEdgeCost rate L (cuts'-cuts)=roundEdgeCost rate L 0+
      (cuts'-cuts)*(2*(rate+19*L+80)+(rate+17*L+115)) := by
    simp [roundEdgeCost,roundCleanupCharge,Nat.mul_comm,Nat.add_assoc]
  omega

/-- Every forest edge present is a possible future cut. Reserve enough
space to enter cleanup before knowing which edges the path will cut. -/
theorem roundEdgeSpace_le_remaining (A L m k cuts edges links : ℕ)
    (hk : k<m) (hC : cuts+edges=links) (hLink : links≤k) :
    roundEdgeSpace A L edges≤roundSuffixSpace A L m k cuts := by
  have h₁ : 1≤m-k := by omega
  have h₂ : edges≤m-cuts := by omega
  have hBase := Nat.mul_le_mul_right (roundEdgeSpace A L 0) h₁
  rw [Nat.one_mul] at hBase
  have hCharge := Nat.mul_le_mul_right (2*(A+4+2*L)+A) h₂
  have he : roundEdgeSpace A L edges=roundEdgeSpace A L 0+edges*(2*(A+4+2*L)+A) := by
    simp [roundEdgeSpace,roundCleanupCharge,Nat.add_assoc,Nat.mul_comm]
  unfold roundSuffixSpace
  omega

/-- The cut count is cumulative across integral, disconnected, and
cycle branches of the model. -/
theorem roundEdge_cuts_mono {D : DynForest} (hD : D.IsSpec) {I : Instance} (hI : I.IsValid)
    {f : Fin I.m → ℚ} {P : ℕ} {M : ℚ} (model : RoundState D I) (j : Fin I.m)
    (hInv : LoopInv D I f P M j.val model) (hFP : ∀ e, IsFixedPoint P (f e)) :
    model.counts.cutOps≤(roundEdgeStep D I f model j).counts.cutOps := by
  by_cases hInt : isIntRat (f j)=true
  · simp [roundEdgeStep,hInt]
  · have hFrac := Bool.eq_false_iff.mpr hInt
    by_cases hRoots : D.findRoot model.df (I.edge j).tail=D.findRoot model.df (I.edge j).head
    · have hu : (I.edge j).tail<(D.toForest model.df).n := by
        rw [hInv.2.1]
        exact (hI.1 _ (List.getElem_mem j.isLt)).1
      have hv : (I.edge j).head<(D.toForest model.df).n := by
        rw [hInv.2.1]
        exact (hI.1 _ (List.getElem_mem j.isLt)).2
      have hConn := ((hD.2.2.1 model.df (I.edge j).head hInv.1 hv).2 (I.edge j).tail hu).mp hRoots
      have hState := (roundEdgeStep_connected D I f model j hFrac hRoots).2.2
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hCount,hLen⟩ :=
        roundCycleClean_properties hD model j (roundBackward D model.df j) hInv hFP hFrac hConn
      rw [hState]
      omega
    · rw [(roundEdgeStep_disconnected D I f model j hFrac hRoots).2.2]

end MinCostFlow.IPM.Machine
