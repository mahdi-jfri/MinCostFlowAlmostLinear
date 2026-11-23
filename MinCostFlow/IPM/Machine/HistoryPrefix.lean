module

public import MinCostFlow.IPM.MinRatioSpec

/-!
# Extending a machine history leaves its past unchanged

The model state at a stage reads only inputs up to that stage.
Agreement on that prefix therefore preserves the state, circulation,
actual increments, accumulated flow and last reported stage. These
facts permit a finite machine run to append its decoded calls without
changing the interpretation of any earlier cached coordinate.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Agreement on all decoded inputs through a stage preserves every
abstract state in that prefix. -/
theorem minRatioState_prefix_congr (A : MinRatioDataStructure) (D E : DynamicInstance)
    (eta nu : ℕ → ℝ) (op other : ℕ → Bool) (T : ℕ)
    (h : ∀ j≤T,D.G j=E.G j ∧ D.U j=E.U j ∧ D.g j=E.g j ∧ D.ℓ j=E.ℓ j ∧
      eta j=nu j ∧ op j=other j) :
    ∀ t≤T,minRatioState A D eta op t=minRatioState A E nu other t := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [minRatioState,(h 0 (Nat.zero_le _)).1,(h 0 (Nat.zero_le _)).2.2.1,
      (h 0 (Nat.zero_le _)).2.2.2.1]
  | succ t ih =>
    intro ht
    obtain ⟨_,hU,hg,hl,heta,hop⟩ := h (t+1) ht
    simp only [minRatioState,hU,hg,hl,heta,hop,ih (by omega)]

/-- The circulation returned by a decoded Update depends only on its
input prefix, including the current effective normalization. -/
theorem minRatioDirection_prefix_congr (A : MinRatioDataStructure) (D E : DynamicInstance)
    (eta nu : ℕ → ℝ) (op other : ℕ → Bool) (T t : ℕ)
    (h : ∀ j≤T,D.G j=E.G j ∧ D.U j=E.U j ∧ D.g j=E.g j ∧ D.ℓ j=E.ℓ j ∧
      eta j=nu j ∧ op j=other j) (ht : t+1≤T) :
    minRatioDirection A D eta op t=minRatioDirection A E nu other t := by
  obtain ⟨_,hU,hg,hl,heta,_⟩ := h (t+1) ht
  simp only [minRatioDirection,hU,hg,hl,heta,
    minRatioState_prefix_congr A D E eta nu op other T h t (by omega)]

/-- Actual rounded flow increments are unchanged when only later
history inputs are extended. -/
theorem minRatioIncrement_prefix_congr (A : MinRatioDataStructure) (D E : DynamicInstance)
    (eta nu : ℕ → ℝ) (op other : ℕ → Bool) (T t e : ℕ)
    (h : ∀ j≤T,D.G j=E.G j ∧ D.U j=E.U j ∧ D.g j=E.g j ∧ D.ℓ j=E.ℓ j ∧
      eta j=nu j ∧ op j=other j) (ht : t≤T) :
    minRatioIncrement A D eta op t e=minRatioIncrement A E nu other t e := by
  cases t with
  | zero => rfl
  | succ t =>
    obtain ⟨hG,_,hg,_,heta,hop⟩ := h (t+1) ht
    simp only [minRatioIncrement,hG,hg,heta,hop,
      minRatioDirection_prefix_congr A D E eta nu op other T t h ht]

/-- The accumulated flow of every earlier prefix is unchanged by
appending decoded machine calls. -/
theorem minRatioFlow_prefix_congr (A : MinRatioDataStructure) (D E : DynamicInstance)
    (eta nu : ℕ → ℝ) (op other : ℕ → Bool) (T t e : ℕ)
    (h : ∀ j≤T,D.G j=E.G j ∧ D.U j=E.U j ∧ D.g j=E.g j ∧ D.ℓ j=E.ℓ j ∧
      eta j=nu j ∧ op j=other j) (ht : t≤T) :
    minRatioFlow A D eta op t e=minRatioFlow A E nu other t e := by
  unfold minRatioFlow
  apply Finset.sum_congr rfl
  intro j hj
  exact minRatioIncrement_prefix_congr A D E eta nu op other T j e h
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans ht)

/-- The last report remembered for every cached edge is unchanged
when later decoded calls are appended to its history. -/
theorem minRatioLast_prefix_congr (A : MinRatioDataStructure) (D E : DynamicInstance)
    (eta nu : ℕ → ℝ) (op other : ℕ → Bool) (T e : ℕ)
    (h : ∀ j≤T,D.G j=E.G j ∧ D.U j=E.U j ∧ D.g j=E.g j ∧ D.ℓ j=E.ℓ j ∧
      eta j=nu j ∧ op j=other j) :
    ∀ t≤T,minRatioLast A D eta op t e=minRatioLast A E nu other t e := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    simp only [minRatioLast,(h (t+1) ht).2.2.2.2.2,
      minRatioState_prefix_congr A D E eta nu op other T h t (by omega),ih (by omega)]

/-- The complete input-agreement hypothesis is jointly satisfiable for
any history, normalization sequence, schedule and horizon. -/
theorem historyPrefix_agreement_refl (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) :
    ∀ j≤T,D.G j=D.G j ∧ D.U j=D.U j ∧ D.g j=D.g j ∧ D.ℓ j=D.ℓ j ∧ eta j=eta j ∧ op j=op j := by
  intro j _
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end MinCostFlow.IPM.Machine
