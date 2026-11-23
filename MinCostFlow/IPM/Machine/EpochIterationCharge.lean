module

public import MinCostFlow.IPM.Machine.EpochMovementAccount
import Mathlib.Tactic.Linarith

/-!
# The movement charge of one complete machine iteration

The copied Detect names are exactly the refreshed names. The
valid-history condition therefore keeps each unreported length, and
only accounts already reset by Detect can change length. Summing the
per-edge charge gives the bound before the next call.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Lemma 9.4 of Chen et al., arXiv:2203.00671v2 (pages 71–72), for one
decoded pair of actual stages. The number of reports times the threshold
plus the new balance is bounded by the old balance and actual deposit. -/
theorem epoch_iteration_movement_charge_on (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecOn A κ α Ψ eps
      (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update eta (T+1) 0) (Function.update op (T+1) false) (T+1)) (hv : MinRatioHistoryValid D op T) (heps : 0≤eps)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    (hset : es.toFinset=(A.detect (minRatioState A D eta op T)).1)
    (hv' : MinRatioHistoryValid (appendHistoryIteration D T es g l)
      (appendHistoryIterationOp op T) (T+1+1)) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    (eps*((A.detect (minRatioState A D eta op T)).1.card:ℝ)+
        (∑ e ∈ (D'.G (T+1+1)).E,epochPendingMovement A D' eta' op' (T+1+1) e) ≤
      (∑ e ∈ (D.G T).E,epochPendingMovement A D eta op T e)+
        (D'.G (T+1+1)).lnorm (D'.ℓ (T+1+1)) (minRatioIncrement A D' eta' op' (T+1+1))) ∧
    ∀ e∈(D'.G (T+1+1)).E,
      epochPendingMovement A D' eta' op' (T+1+1) e ≤
        eps + (D'.G (T+1+1)).lnorm (D'.ℓ (T+1+1)) (minRatioIncrement A D' eta' op' (T+1+1)) := by
  classical
  dsimp only
  let C := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  let nu := Function.update eta (T+1) 0
  let flag := Function.update op (T+1) false
  let D' := appendHistoryIteration D T es g l
  let eta' := appendHistoryIterationEta eta T actual
  let op' := appendHistoryIterationOp op T
  let S := (A.detect (minRatioState A D eta op T)).1
  obtain ⟨hsub,hdetect⟩ := epoch_detect_movement_charge_on A D eta op T κ α Ψ eps hA hv heps
  have hG : D'.G (T+1+1)=D.G T := by simp only [D',appendHistoryIteration,appendHistoryStage,Function.update_self]
  have hl : D'.ℓ (T+1+1)=l := Function.update_self _ _ _
  have hpoint (e : ℕ) (he : e∈(D.G T).E) :
      (if e∈S then eps else 0)+epochPendingMovement A D' eta' op' (T+1+1) e ≤
        epochPendingMovement A D eta op T e+|l e*minRatioIncrement A D' eta' op' (T+1+1) e| ∧
      epochPendingMovement A D' eta' op' (T+1+1) e ≤
        eps+|l e*minRatioIncrement A D' eta' op' (T+1+1) e| := by
    have he' : e∈(D'.G (T+1+1)).E := hG ▸ he
    have hle : 0≤l e := by
      rw [← hl]
      exact ((hv'.2.1 _ le_rfl).2 e he').le
    have hchange : l e=C.ℓ (T+1) e ∨ minRatioLast A C nu flag (T+1) e=T+1 := by
      by_cases hmem : e∈S
      · right
        change minRatioLast A (appendHistoryStage D T [] (D.g T) (D.ℓ T))
          (Function.update eta (T+1) 0) (Function.update op (T+1) false) (T+1) e=T+1
        rw [appendHistoryStage_detect_last,ite_eq_left hmem]
      · left
        have hn : e∉es := by
          intro hm
          apply hmem
          change e∈(A.detect (minRatioState A D eta op T)).1
          rw [← hset]
          exact List.mem_toFinset.mpr hm
        have hnot (j : ℕ) (hlo : T+1<j) (hhi : j≤T+1+1) (u : MinCostFlow.Update)
            (hu : u∈D'.U j) : ¬ u.Inserts e := by
          have hindex : j=T+1+1 := by omega
          subst j
          have hu' : u∈refreshEdges (D.G T) es := by
            simpa only [D',appendHistoryIteration,appendHistoryStage,Function.update_self] using hu
          exact fun hi => hn ((refreshEdges_inserts (D.G T) es e).mp ⟨u,hu',hi⟩)
        have hsame := (hv'.2.2.2 (T+1+1) (by omega) le_rfl e he'
          (by simpa only [DynamicInstance.NotInsertedBetween,Nat.add_sub_cancel] using hnot)).2
        simpa only [hl,D',appendHistoryIteration,appendHistoryStage,Function.update_of_ne
          (by omega : T+1≠T+1+1),Function.update_self,C,Nat.add_sub_cancel] using hsame
    have hupdate := epoch_update_movement_deposit A C nu flag (T+1)
      (refreshEdges (D.G T) es) g l actual e hle hchange
    have hnew : epochPendingMovement A D' eta' op' (T+1+1) e=
        epochPendingMovement A C nu flag (T+1) e+|l e*minRatioIncrement A D' eta' op' (T+1+1) e| :=
      hupdate
    rw [hnew]
    refine ⟨?_,add_le_add_left (hdetect e he).2 _⟩
    rw [← add_assoc]
    exact add_le_add_left (hdetect e he).1 _
  refine ⟨?_,?_⟩
  swap
  · intro e he
    have hlNonneg (j : ℕ) (hj : j∈(D'.G (T+1+1)).E) : 0≤l j := by
      rw [← hl]
      exact ((hv'.2.1 _ le_rfl).2 j hj).le
    have hterm : |l e*minRatioIncrement A D' eta' op' (T+1+1) e| ≤
        (D'.G (T+1+1)).lnorm (D'.ℓ (T+1+1)) (minRatioIncrement A D' eta' op' (T+1+1)) := by
      rw [MGraph.lnorm,hl,abs_mul,abs_of_nonneg (hlNonneg e he)]
      exact Finset.single_le_sum (fun j hj => mul_nonneg (hlNonneg j hj) (abs_nonneg _)) he
    exact ((hpoint e (hG ▸ he)).2).trans (add_le_add_right hterm _)
  have hsum := Finset.sum_le_sum (s:=(D.G T).E) (fun e he => (hpoint e he).1)
  simp only [Finset.sum_add_distrib] at hsum
  have hcount : (∑ e ∈ (D.G T).E,if e∈S then eps else 0)=eps*(S.card:ℝ) := by
    rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr (show S⊆(D.G T).E from hsub)]
    simp [mul_comm]
  rw [hcount] at hsum
  change eps*(S.card:ℝ)+(∑ e ∈ (D'.G (T+1+1)).E,epochPendingMovement A D' eta' op' (T+1+1) e)≤_
  change _ ≤ _ + (D'.G (T+1+1)).lnorm (D'.ℓ (T+1+1)) _
  rw [hG,hl,MGraph.lnorm]
  refine hsum.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have he' : e∈(D'.G (T+1+1)).E := hG ▸ he
  have hle : 0≤l e := by
    rw [← hl]
    exact ((hv'.2.1 _ le_rfl).2 e he').le
  rw [abs_mul,abs_of_nonneg hle]

/-- Lemma 9.4 of Chen et al., arXiv:2203.00671v2 (pages 71–72), for one
decoded pair of actual stages. The number of reports times the threshold
plus the new balance is bounded by the old balance and actual deposit. -/
theorem epoch_iteration_movement_charge (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpec A κ α Ψ eps) (hv : MinRatioHistoryValid D op T) (heps : 0≤eps)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    (hset : es.toFinset=(A.detect (minRatioState A D eta op T)).1)
    (hv' : MinRatioHistoryValid (appendHistoryIteration D T es g l)
      (appendHistoryIterationOp op T) (T+1+1)) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    (eps*((A.detect (minRatioState A D eta op T)).1.card:ℝ)+
        (∑ e ∈ (D'.G (T+1+1)).E,epochPendingMovement A D' eta' op' (T+1+1) e) ≤
      (∑ e ∈ (D.G T).E,epochPendingMovement A D eta op T e)+
        (D'.G (T+1+1)).lnorm (D'.ℓ (T+1+1)) (minRatioIncrement A D' eta' op' (T+1+1))) ∧
    ∀ e∈(D'.G (T+1+1)).E,
      epochPendingMovement A D' eta' op' (T+1+1) e ≤
        eps + (D'.G (T+1+1)).lnorm (D'.ℓ (T+1+1)) (minRatioIncrement A D' eta' op' (T+1+1)) := by
  have hSpec := hA (appendHistoryStage D T [] (D.g T) (D.ℓ T))
    (Function.update eta (T+1) 0) (Function.update op (T+1) false) (T+1)
    (appendHistoryStage_valid_detect D op T hv)
  exact epoch_iteration_movement_charge_on A D eta op T κ α Ψ eps hSpec hv heps es g l actual
    hset hv'

end MinCostFlow.IPM.Machine
