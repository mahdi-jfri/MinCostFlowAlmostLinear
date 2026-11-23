module

public import MinCostFlow.IPM.Machine.RoundRatFacts
public import WordRAM.CopyWords
public import MinCostFlow.Statement.Problem
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Updating one entry of the rounder's working flow

Flushing a cut edge copies its exact fixed-point block into the
edge's own table entry. The write leaves every other entry and the
dynamic forest's separate footprint intact.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Dense table of the rational flow coordinates. -/
def RoundFlowAt (I : Instance) (mem : ℕ → ℕ) (base h L P : ℕ)
    (flow : Fin I.m → ℚ) : Prop :=
  ∀ e, RatAt mem (base+e.val*L) h L P (flow e)

/-- Decode one exact copy of a fixed-point block. -/
theorem round_copy_rat {w h L P source dest v : ℕ} {mem final : ℕ → ℕ} {q : ℚ}
    (hsrc : RatAt mem source h L P q)
    (hout : (copyWordsContract w).post [source,dest,L] mem v final) :
    RatAt final dest h L P q ∧ (∀ z,z<dest ∨ dest+L≤z → final z=mem z) := by
  obtain ⟨src,dst,len,heq,_,hvals,hframe⟩ := hout
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  refine ⟨⟨?_,?_⟩,hframe⟩
  · intro j hj
    rw [hvals j hj]
    exact hsrc.1 j hj
  · unfold readRat at *
    rw [Num.intVal_congr hvals]
    exact hsrc.2

/-- Distinct indexed coordinate blocks do not overlap. -/
private theorem round_entries_disjoint (base L i j : ℕ) (h : i≠j) :
    base+i*L+L≤base+j*L ∨ base+j*L+L≤base+i*L := by
  rcases lt_or_gt_of_ne h with h' | h'
  · left
    have hl := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h')
    rw [Nat.succ_mul] at hl
    omega
  · right
    have hl := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h')
    rw [Nat.succ_mul] at hl
    omega

/-- One block update changes only the indexed flow coordinate. -/
theorem RoundFlowAt.update {h L P base : ℕ} {I : Instance} {mem final : ℕ → ℕ}
    {flow : Fin I.m → ℚ} (e : Fin I.m) (q : ℚ)
    (hflow : RoundFlowAt I mem base h L P flow)
    (hnew : RatAt final (base+e.val*L) h L P q)
    (hframe : ∀ z<base+I.m*L,z<base+e.val*L ∨ base+e.val*L+L≤z → final z=mem z) :
    RoundFlowAt I final base h L P (fun j => if j=e then q else flow j) := by
  intro j
  change RatAt final (base+j.val*L) h L P (if j=e then q else flow j)
  by_cases he : j=e
  · rw [he,ite_eq_left rfl]
    exact hnew
  · rw [ite_eq_right he]
    have hj : j.val≠e.val := fun hh => he (Fin.ext hh)
    have hEnd := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hEnd
    have hmem (i : ℕ) (hi : i<L) : final (base+j.val*L+i)=mem (base+j.val*L+i) := by
      apply hframe _ (by omega)
      rcases round_entries_disjoint base L j.val e.val hj with h | h
      · left
        omega
      · right
        omega
    refine ⟨?_,?_⟩
    · intro i hi
      rw [hmem i hi]
      exact (hflow j).1 i hi
    · unfold readRat
      rw [Num.intVal_congr hmem]
      exact (hflow j).2

/-- The copy changes exactly the addressed rational coordinate and
preserves the other entries. This is the flush update in the model. -/
theorem round_copy_flow {w h L P source base v : ℕ} {I : Instance} {mem final : ℕ → ℕ}
    {flow : Fin I.m → ℚ} (e : Fin I.m) (q : ℚ)
    (hsrc : RatAt mem source h L P q) (hflow : RoundFlowAt I mem base h L P flow)
    (hout : (copyWordsContract w).post [source,base+e.val*L,L] mem v final) :
    RoundFlowAt I final base h L P (fun j => if j=e then q else flow j) ∧
      (∀ z,z<base+e.val*L ∨ base+e.val*L+L≤z → final z=mem z) := by
  obtain ⟨hnew,hframe⟩ := round_copy_rat hsrc hout
  exact ⟨hflow.update e q hnew (fun z _ => hframe z),hframe⟩

/-- The coordinate copy preserves the concrete forest and its
amortized credit when the table lies outside its footprint. -/
theorem round_copy_preserves_forest {σ : Type} (R : DSRep σ) (hLocal : R.Local)
    {w handle L source dest v : ℕ} {mem final : ℕ → ℕ} {s : σ} {x : R.τ}
    (hrep : R.rep handle s x mem)
    (hsep : ∀ z,R.foot handle x z → z<dest ∨ dest+L≤z)
    (hout : (copyWordsContract w).post [source,dest,L] mem v final) :
    R.rep handle s x final ∧ R.phi handle x mem=R.phi handle x final := by
  obtain ⟨src,dst,len,heq,_,_,hframe⟩ := hout
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  obtain ⟨hr,hφ⟩ := hLocal handle s x mem final (fun z hz => (hframe z (hsep z hz)).symm)
  exact ⟨hr hrep,hφ⟩

end MinCostFlow.IPM.Machine
