module

public import MinCostFlow.IPM.Machine.HistoryExtension
public import MinCostFlow.IPM.Machine.HistoryPrefix
public import MinCostFlow.IPM.Machine.HistoryValidityPrefix

/-!
# Appending one decoded fixed-graph machine stage

Extend the shared DynamicInstance at the next stage using the actual
batch and coefficient values. Its graph stays fixed. Every earlier
input remains unchanged, so its state and valid-prefix interpretation
are preserved. Detect and refresh Update extensions then follow from
the structural valid-history lemmas.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Append one fixed-graph stage of Definition 4.5 (page 14) to the
shared dynamic input sequence. Only the next stage's data are replaced. -/
def appendHistoryStage (D : DynamicInstance) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) : DynamicInstance where
  G := Function.update D.G (T+1) (D.G T)
  U := Function.update D.U (T+1) U
  g := Function.update D.g (T+1) g
  ℓ := Function.update D.ℓ (T+1) l

/-- The appended stage reuses the previous graph and preserves the
edge and vertex bounds of the prefix. -/
theorem appendHistoryStage_bounded {D : DynamicInstance} {T M N : ℕ}
    (U : List MinCostFlow.Update) (g l : ℕ → ℝ) (hsize : MinRatioHistoryBounded D T M N) :
    MinRatioHistoryBounded (appendHistoryStage D T U g l) (T+1) M N := by
  have hgraph (j : ℕ) (hj : j ≤ T+1) : ∃ i ≤ T, (appendHistoryStage D T U g l).G j = D.G i := by
    by_cases heq : j = T+1
    · subst j
      exact ⟨T, le_rfl, by simp [appendHistoryStage]⟩
    · exact ⟨j, by omega, by simp [appendHistoryStage, heq]⟩
  constructor
  · intro j hj
    obtain ⟨i, hi, h⟩ := hgraph j hj
    rw [h]
    exact hsize.1 i hi
  · intro j hj
    obtain ⟨i, hi, h⟩ := hgraph j hj
    rw [h]
    exact hsize.2 i hi

/-- Appending a fixed-graph stage preserves constant graph identity across the prefix. -/
theorem appendHistoryStage_graph_eq {D : DynamicInstance} {T : ℕ}
    (U : List MinCostFlow.Update) (g l : ℕ → ℝ)
    {G : MGraph} (hG : ∀ j ≤ T, D.G j = G) :
    ∀ j ≤ T+1, (appendHistoryStage D T U g l).G j = G := by
  intro j hj
  by_cases heq : j = T+1
  · subst j; simp [appendHistoryStage, hG T le_rfl]
  · simp [appendHistoryStage, heq, hG j (by omega)]

/-- Appending a stage reuses the previous graph and preserves graph invariants. -/
theorem appendHistoryStage_on {D : DynamicInstance} {T : ℕ}
    (U : List MinCostFlow.Update) (g l : ℕ → ℝ)
    {P : MGraph → Prop} (hP : ∀ j ≤ T, P (D.G j)) :
    ∀ j ≤ T+1, P ((appendHistoryStage D T U g l).G j) := by
  intro j hj
  by_cases heq : j = T+1
  · subst j; simp [appendHistoryStage, hP T le_rfl]
  · simp [appendHistoryStage, heq, hP j (by omega)]

/-- Appending a stage whose lengths satisfy a stage invariant preserves that invariant. -/
theorem appendHistoryStage_stage_on {D : DynamicInstance} {T : ℕ}
    (U : List MinCostFlow.Update) (g l : ℕ → ℝ)
    {P : MGraph → (ℕ → ℝ) → Prop} (hP : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (hl : P (D.G T) l) :
    ∀ j ≤ T+1, P ((appendHistoryStage D T U g l).G j) ((appendHistoryStage D T U g l).ℓ j) := by
  intro j hj
  by_cases heq : j = T+1
  · subst j; simpa [appendHistoryStage] using hl
  · simpa [appendHistoryStage, heq] using hP j (by omega)

/-- Appending a stage with lengths in range keeps the history in range. -/
theorem appendHistoryStage_lengthsWithin {D : DynamicInstance} {T E : ℕ}
    (U : List MinCostFlow.Update) (g l : ℕ → ℝ)
    (hL : HistoryLengthsWithin D T E) (hl : LengthsWithin (D.G T) E l) :
    HistoryLengthsWithin (appendHistoryStage D T U g l) (T+1) E :=
  appendHistoryStage_stage_on (P := fun G l => LengthsWithin G E l) U g l hL hl

/-- Appending a decoded stage and its actual effective normalization
preserves all abstract states in the already executed prefix. -/
theorem appendHistoryStage_past_state (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) (isUpdate : Bool) :
    ∀ t≤T,minRatioState A (appendHistoryStage D T U g l)
      (Function.update eta (T+1) actual) (Function.update op (T+1) isUpdate) t=
      minRatioState A D eta op t := by
  intro t ht
  symm
  apply minRatioState_prefix_congr A D _ eta _ op _ T _ t ht
  intro j hj
  have hn : j≠T+1 := by omega
  simp only [appendHistoryStage,Function.update_of_ne hn,and_self]

/-- Appending a decoded call preserves every earlier accumulated flow. -/
theorem appendHistoryStage_past_flow (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) (isUpdate : Bool) (t e : ℕ) (ht : t≤T) :
    minRatioFlow A (appendHistoryStage D T U g l)
      (Function.update eta (T+1) actual) (Function.update op (T+1) isUpdate) t e=
      minRatioFlow A D eta op t e := by
  symm
  apply minRatioFlow_prefix_congr A D _ eta _ op _ T t e _ ht
  intro j hj
  have hn : j≠T+1 := by omega
  simp only [appendHistoryStage,Function.update_of_ne hn,and_self]

/-- Appending a decoded call preserves every earlier report time. -/
theorem appendHistoryStage_past_last (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) (isUpdate : Bool) (t e : ℕ) (ht : t≤T) :
    minRatioLast A (appendHistoryStage D T U g l)
      (Function.update eta (T+1) actual) (Function.update op (T+1) isUpdate) t e=
      minRatioLast A D eta op t e := by
  symm
  apply minRatioLast_prefix_congr A D _ eta _ op _ T e _ t ht
  intro j hj
  have hn : j≠T+1 := by omega
  simp only [appendHistoryStage,Function.update_of_ne hn,and_self]

/-- The state after an appended Update is exactly the model Update of
the old prefix at the supplied batch, arrays and actual normalization. -/
theorem appendHistoryStage_update_state (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) :
    minRatioState A (appendHistoryStage D T U g l) (Function.update eta (T+1) actual)
      (Function.update op (T+1) true) (T+1)=
      (A.update (minRatioState A D eta op T) U g l actual).1 := by
  rw [minRatioState]
  simp only [Function.update_self,ite_true]
  rw [appendHistoryStage_past_state A D eta op T U g l actual true T le_rfl]
  simp only [appendHistoryStage,Function.update_self]

/-- The state after an appended Detect is exactly the model Detect
state of the old prefix. The normalization is unused by Detect. -/
theorem appendHistoryStage_detect_state (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (actual : ℝ) :
    minRatioState A (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update eta (T+1) actual) (Function.update op (T+1) false) (T+1)=
      (A.detect (minRatioState A D eta op T)).2 := by
  rw [minRatioState]
  simp only [Function.update_self,Bool.false_eq_true,ite_false]
  rw [appendHistoryStage_past_state A D eta op T [] (D.g T) (D.ℓ T) actual false T le_rfl]

/-- Update does not reset `last_e`; only Detect reports do so. -/
theorem appendHistoryStage_update_last (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (U : List MinCostFlow.Update)
    (g l : ℕ → ℝ) (actual : ℝ) (e : ℕ) :
    minRatioLast A (appendHistoryStage D T U g l) (Function.update eta (T+1) actual)
      (Function.update op (T+1) true) (T+1) e=minRatioLast A D eta op T e := by
  rw [minRatioLast]
  simp only [Function.update_self,Bool.true_eq_false,false_and,ite_false]
  exact appendHistoryStage_past_last A D eta op T U g l actual true T e le_rfl

/-- Detect resets exactly its actual reported names to the new stage. -/
theorem appendHistoryStage_detect_last (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (actual : ℝ) (e : ℕ) :
    minRatioLast A (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update eta (T+1) actual) (Function.update op (T+1) false) (T+1) e=
      if e∈(A.detect (minRatioState A D eta op T)).1 then T+1 else minRatioLast A D eta op T e := by
  rw [minRatioLast]
  simp only [Function.update_self,true_and]
  rw [appendHistoryStage_past_state A D eta op T [] (D.g T) (D.ℓ T) actual false T le_rfl,
    appendHistoryStage_past_last A D eta op T [] (D.g T) (D.ℓ T) actual false T e le_rfl]

/-- Detect contributes zero actual increment and preserves the entire
implicit flow while updating its report metadata. -/
theorem appendHistoryStage_detect_flow (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (actual : ℝ) (e : ℕ) :
    minRatioFlow A (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update eta (T+1) actual) (Function.update op (T+1) false) (T+1) e=
      minRatioFlow A D eta op T e := by
  rw [minRatioFlow_succ,appendHistoryStage_past_flow A D eta op T [] (D.g T) (D.ℓ T) actual false T e le_rfl]
  simp only [minRatioIncrement,Function.update_self,Bool.false_eq_true,false_and,ite_false,add_zero]

/-- Appending an unchanged Detect input preserves the full valid
history. The effective normalization at a Detect stage is unused. -/
theorem appendHistoryStage_valid_detect (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) :
    MinRatioHistoryValid (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update op (T+1) false) (T+1) := by
  let E := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  have hp : MinRatioHistoryValid E (Function.update op (T+1) false) T := by
    apply minRatioHistoryValid_prefix_congr D E op _ T _ hvalid
    intro j hj
    have hn : j≠T+1 := by omega
    simp only [E,appendHistoryStage,Function.update_of_ne hn,and_self]
  apply minRatioHistoryValid_succ_detect E _ T hp
  all_goals simp [E,appendHistoryStage]

/-- Appending the actual refresh batch and positive checked lengths
preserves validity, provided unreported coefficients stayed unchanged. -/
theorem appendHistoryStage_valid_refresh (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (es : List ℕ) (g l : ℕ → ℝ)
    (hes : ∀ e∈es,e∈(D.G T).E) (hl : ∀ e∈(D.G T).E,0<l e)
    (hunchanged : ∀ e∈(D.G T).E,e∉es → g e=D.g T e ∧ l e=D.ℓ T e) :
    MinRatioHistoryValid (appendHistoryStage D T (refreshEdges (D.G T) es) g l)
      (Function.update op (T+1) true) (T+1) := by
  let E := appendHistoryStage D T (refreshEdges (D.G T) es) g l
  have hp : MinRatioHistoryValid E (Function.update op (T+1) true) T := by
    apply minRatioHistoryValid_prefix_congr D E op _ T _ hvalid
    intro j hj
    have hn : j≠T+1 := by omega
    simp only [E,appendHistoryStage,Function.update_of_ne hn,and_self]
  have hn : T≠T+1 := by omega
  apply minRatioHistoryValid_succ_refresh E _ T hp (by simp) es
  · simpa [E,appendHistoryStage,hn] using hes
  · simp [E,appendHistoryStage]
  · simp [E,appendHistoryStage]
  · simpa [E,appendHistoryStage] using hl
  · simpa [E,appendHistoryStage,hn] using hunchanged

end MinCostFlow.IPM.Machine
