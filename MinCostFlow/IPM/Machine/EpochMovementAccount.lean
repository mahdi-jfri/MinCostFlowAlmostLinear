module

public import MinCostFlow.IPM.Machine.HistoryIteration
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Movement accounts for Detect before Update

Lemma 9.4 of Chen et al., arXiv:2203.00671v2 (pages 71–72), pays for
each report with the movement since its previous report. In the machine
order, Detect spends the old account first. Only then does Update
change the reported lengths and deposit new movement.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine

/-- Uncharged movement at one edge, in units of its currently held
length. The interval starts strictly after the actual last report. -/
def epochPendingMovement (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T e : ℕ) : ℝ :=
  D.ℓ T e * ∑ j ∈ Finset.Ioc (minRatioLast A D eta op T e) T,
    |minRatioIncrement A D eta op j e|

/-- The account has no initial debt or credit. -/
theorem epochPendingMovement_zero (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (e : ℕ) :
    epochPendingMovement A D eta op 0 e=0 := by
  simp only [epochPendingMovement,minRatioLast,Finset.Ioc_self,Finset.sum_empty,mul_zero]

/-- The current length is positive on each edge of a valid history,
and the terms stored in a movement account are absolute increments. -/
theorem epochPendingMovement_nonneg (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T e : ℕ)
    (hv : MinRatioHistoryValid D op T) (he : e∈(D.G T).E) :
    0≤epochPendingMovement A D eta op T e :=
  mul_nonneg ((hv.2.1 T le_rfl).2 e he).le (Finset.sum_nonneg fun _ _ => abs_nonneg _)

private theorem append_increment_past (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) (flag : Bool) (j e : ℕ) (hj : j≤T) :
    minRatioIncrement A (appendHistoryStage D T U g l) (Function.update eta (T+1) actual)
      (Function.update op (T+1) flag) j e=minRatioIncrement A D eta op j e := by
  symm
  apply minRatioIncrement_prefix_congr A D _ eta _ op _ T j e _ hj
  intro i hi
  have hn : i≠T+1 := by omega
  simp only [appendHistoryStage,Function.update_of_ne hn,and_self]

/-- Detect empties the reported accounts and keeps the others. Each
reported account pays one threshold before it is emptied. -/
theorem epoch_detect_movement_charge_on (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecOn A κ α Ψ eps
      (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update eta (T+1) 0) (Function.update op (T+1) false) (T+1)) (_hv : MinRatioHistoryValid D op T) (heps : 0≤eps) :
    let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
    let eta' := Function.update eta (T+1) 0
    let op' := Function.update op (T+1) false
    let S := (A.detect (minRatioState A D eta op T)).1
    S⊆(D.G T).E ∧
    ∀ e∈(D.G T).E,
      (if e∈S then eps else 0)+epochPendingMovement A D' eta' op' (T+1) e ≤
        epochPendingMovement A D eta op T e ∧
      epochPendingMovement A D' eta' op' (T+1) e≤eps := by
  dsimp only
  let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  let eta' := Function.update eta (T+1) 0
  let op' := Function.update op (T+1) false
  have hop : op' (T+1)=false := Function.update_self _ _ _
  have hspec := hA.2.2 T le_rfl hop
  change (A.detect (minRatioState A D' eta' op' T)).1 = minRatioDetectSet A D' eta' op' eps T at hspec
  rw [appendHistoryStage_past_state A D eta op T _ _ _ 0 false T le_rfl] at hspec
  have hgraph : D'.G (T+1)=D.G T := Function.update_self _ _ _
  have hlength : D'.ℓ (T+1)=D.ℓ T := Function.update_self _ _ _
  have hsum (e : ℕ) :
      D'.ℓ (T+1) e * (∑ j ∈ Finset.Ioc (minRatioLast A D' eta' op' T e) (T+1),
        |minRatioIncrement A D' eta' op' j e|)=epochPendingMovement A D eta op T e := by
    rw [hlength,appendHistoryStage_past_last A D eta op T _ _ _ 0 false T e le_rfl,
      Finset.sum_Ioc_succ_top (minRatioLast_le A D eta op T e)]
    have hz : minRatioIncrement A D' eta' op' (T+1) e=0 := by simp [minRatioIncrement,hop]
    rw [hz,abs_zero,add_zero]
    unfold epochPendingMovement
    congr 1
    exact Finset.sum_congr rfl fun j hj =>
      congrArg abs (append_increment_past A D eta op T _ _ _ 0 false j e (Finset.mem_Ioc.mp hj).2)
  have htest (e : ℕ) :
      e∈(A.detect (minRatioState A D eta op T)).1 ↔
        e∈(D.G T).E ∧ eps≤epochPendingMovement A D eta op T e := by
    rw [hspec]
    simp only [minRatioDetectSet,Finset.mem_filter,hgraph,hsum]
  refine ⟨fun e he => ((htest e).mp he).1,?_⟩
  intro e heG
  change ((if e∈(A.detect (minRatioState A D eta op T)).1 then eps else 0)+
      epochPendingMovement A D' eta' op' (T+1) e≤_) ∧ epochPendingMovement A D' eta' op' (T+1) e≤eps
  have hacc : epochPendingMovement A D' eta' op' (T+1) e=
      if e∈(A.detect (minRatioState A D eta op T)).1 then 0 else epochPendingMovement A D eta op T e := by
    unfold epochPendingMovement
    rw [appendHistoryStage_detect_last]
    split_ifs with hmem
    · rw [Finset.Ioc_self,Finset.sum_empty,mul_zero]
    · have hlast : minRatioLast A D' eta' op' T e=minRatioLast A D eta op T e :=
        appendHistoryStage_past_last A D eta op T _ _ _ 0 false T e le_rfl
      simpa only [hlast,epochPendingMovement] using hsum e
  rw [hacc]
  by_cases he : e∈(A.detect (minRatioState A D eta op T)).1
  · simp only [he,↓reduceIte,add_zero]
    exact ⟨((htest e).mp he).2,heps⟩
  · simp only [he,↓reduceIte,zero_add]
    exact ⟨le_rfl,le_of_not_ge fun h => he ((htest e).mpr ⟨heG,h⟩)⟩

/-- Detect empties the reported accounts and keeps the others. Each
reported account pays one threshold before it is emptied. -/
theorem epoch_detect_movement_charge (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpec A κ α Ψ eps) (hv : MinRatioHistoryValid D op T) (heps : 0≤eps) :
    let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
    let eta' := Function.update eta (T+1) 0
    let op' := Function.update op (T+1) false
    let S := (A.detect (minRatioState A D eta op T)).1
    S⊆(D.G T).E ∧
    ∀ e∈(D.G T).E,
      (if e∈S then eps else 0)+epochPendingMovement A D' eta' op' (T+1) e ≤
        epochPendingMovement A D eta op T e ∧
      epochPendingMovement A D' eta' op' (T+1) e≤eps := by
  have hSpec := hA (appendHistoryStage D T [] (D.g T) (D.ℓ T))
    (Function.update eta (T+1) 0) (Function.update op (T+1) false) (T+1)
    (appendHistoryStage_valid_detect D op T hv)
  exact epoch_detect_movement_charge_on A D eta op T κ α Ψ eps hSpec hv heps

/-- For an edge whose length changes, the preceding Detect has just
reset the account. Every other edge keeps its old length. In both
cases Update adds only its own weighted absolute increment. -/
theorem epoch_update_movement_deposit (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) (e : ℕ) (hl : 0≤l e)
    (hchange : l e=D.ℓ T e ∨ minRatioLast A D eta op T e=T) :
    let D' := appendHistoryStage D T U g l
    let eta' := Function.update eta (T+1) actual
    let op' := Function.update op (T+1) true
    epochPendingMovement A D' eta' op' (T+1) e=epochPendingMovement A D eta op T e+
      |l e * minRatioIncrement A D' eta' op' (T+1) e| := by
  dsimp only
  let D' := appendHistoryStage D T U g l
  let eta' := Function.update eta (T+1) actual
  let op' := Function.update op (T+1) true
  change epochPendingMovement A D' eta' op' (T+1) e=_
  unfold epochPendingMovement
  have hlength : D'.ℓ (T+1)=l := Function.update_self _ _ _
  rw [hlength,appendHistoryStage_update_last,Finset.sum_Ioc_succ_top (minRatioLast_le A D eta op T e)]
  have hpast : (∑ j ∈ Finset.Ioc (minRatioLast A D eta op T e) T,
      |minRatioIncrement A D' eta' op' j e|) =
      ∑ j ∈ Finset.Ioc (minRatioLast A D eta op T e) T, |minRatioIncrement A D eta op j e| :=
    Finset.sum_congr rfl fun j hj => congrArg abs
      (append_increment_past A D eta op T U g l actual true j e (Finset.mem_Ioc.mp hj).2)
  rw [hpast,mul_add]
  have hprev : l e * (∑ j ∈ Finset.Ioc (minRatioLast A D eta op T e) T,
      |minRatioIncrement A D eta op j e|) =
      D.ℓ T e * (∑ j ∈ Finset.Ioc (minRatioLast A D eta op T e) T,
        |minRatioIncrement A D eta op j e|) := by
    rcases hchange with hh | hh
    · rw [hh]
    · rw [hh,Finset.Ioc_self,Finset.sum_empty,mul_zero,mul_zero]
  rw [hprev]
  congr 1
  rw [abs_mul,abs_of_nonneg hl]

end MinCostFlow.IPM.Machine
