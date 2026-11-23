module

public import MinCostFlow.IPM.Machine.EpochBase
public import MinCostFlow.IPM.Machine.EpochResidualOutput
import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Tactic.Positivity

/-!
# Decoding the guarded residual and fresh base preparation

The old explicit view stays in place, even when the procedure copies
it into a new mutable table. The final return distinguishes
convergence, rejection and continuation. On continuation the two
views agree word for word.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The returned code and all continuing layout facts refer to the
exact original explicit flow and the exact target residual. -/
theorem epochBase_output_instance (I : Instance) (f : Fin I.m → ℝ)
    {w h cp fp tp L P heap mn mx qp v : ℕ} {mem final : ℕ → ℕ}
    {target minimum maximum : ℝ}
    (hout : (epochBaseContract w h).post [cp,fp,I.m,tp,L,heap,mn,mx,qp] mem v final)
    (hL : 0<L) (hfEnd : fp+I.m*L≤heap)
    (hc : ∀ e : Fin I.m,Num.intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hf : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*L) h L P (f e))
    (htarget : Num.fixVal mem tp h L P=target)
    (hmnEnd : mn+L≤heap) (hmxEnd : mx+L≤heap) (hqEnd : qp+L≤heap)
    (hmn : ScalarAt mem mn h L P minimum) (hmx : ScalarAt mem mx h L P maximum)
    (hq : ScalarAt mem qp h L P (1/4)) :
    (∀ z<heap,final z=mem z) ∧
    (if residual I target f≤1/4 then v=0 ∧ ZeroFrom final (epochResidualEnd I.m L heap)
      else if minimum<residual I target f ∧ residual I target f<maximum then
        let next := epochResidualEnd I.m L heap
        v=next+I.m*L ∧ 2<v ∧ ZeroFrom final v ∧
        ScalarAt final (heap+(8*I.m+3)*L) h L P (residual I target f) ∧
        ∀ e : Fin I.m,ScalarAt final (next+e.val*L) h L P (f e)
      else v=2 ∧ ZeroFrom final (epochResidualEnd I.m L heap)) := by
  obtain ⟨code,memR,hres,hbranch⟩ := hout
  obtain ⟨hscalar,hcode,hzero⟩ := epochResidual_output_instance I f hres hc
    (fun e => (hf e).2) htarget hmnEnd hmxEnd hqEnd hmn hmx hq
  have hframeR : ∀ z<heap,memR z=mem z := hres.1.2.2.2.1
  let next := epochResidualEnd I.m L heap
  have hnext : heap≤next := Nat.le_add_right _ _
  by_cases hstop : residual I target f≤1/4
  · rw [ite_eq_left hstop] at hcode ⊢
    subst code
    have hbranch' : v=0 ∧ final=memR := hbranch
    exact ⟨hbranch'.2.symm ▸ hframeR,hbranch'.1,hbranch'.2.symm ▸ hzero⟩
  · rw [ite_eq_right hstop] at hcode ⊢
    by_cases hrange : minimum<residual I target f ∧ residual I target f<maximum
    · rw [ite_eq_left hrange] at hcode ⊢
      subst code
      have hcopy : (epochFlowCopyContract w).post [fp,I.m,L,next] memR v final := hbranch
      have hv : v=next+I.m*L := hcopy.2
      have hF : ∀ z<next,final z=memR z := hcopy.1.2.2.1
      have hz : ZeroFrom final v := hcopy.1.2.2.2.1
      have hrEnd : heap+(8*I.m+3)*L+L=next := by simp [next,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
      have htwo : 2<v := by
        have h := Nat.le_mul_of_pos_right (n:=8*I.m+4) hL
        dsimp only [next,epochResidualEnd] at hv
        omega
      refine ⟨fun z hz' => (hF z (hz'.trans_le hnext)).trans (hframeR z hz'),
        hv,htwo,hz,⟨Num.IPM.valid_frozen hF hrEnd.le hscalar.1,
          (Num.IPM.fixVal_frozen hF hrEnd.le).trans hscalar.2⟩,?_⟩
      intro e
      have hend := (Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt))
      rw [Nat.succ_mul] at hend
      have heEnd : fp+e.val*L+L≤heap := by omega
      have hOld := Num.IPM.valid_frozen hframeR heEnd (hf e).1
      obtain ⟨hvalid,hcopyVal⟩ := epochFlowCopy_coordinate (P:=P) (h:=h) hcopy
        (hfEnd.trans hnext) e.isLt hOld
      exact ⟨hvalid,hcopyVal.trans ((Num.IPM.fixVal_frozen
        (fun z hz' => (hF z (hz'.trans_le hnext)).trans (hframeR z hz')) heEnd).trans (hf e).2)⟩
    · rw [ite_eq_right hrange] at hcode ⊢
      subst code
      have hbranch' : v=2 ∧ final=memR := hbranch
      exact ⟨hbranch'.2.symm ▸ hframeR,hbranch'.1,hbranch'.2.symm ▸ hzero⟩

end MinCostFlow.IPM.Machine
