module

public import MinCostFlow.IPM.Machine.HistoryAppend

/-!
# The two history stages of a complete machine iteration

The machine calls Detect before refreshing coefficients and updating
flow. Append those two decoded stages to the shared history. Detect
uses the previous arrays. Update uses the actual refreshed arrays and
rounded normalization. The resulting state and report times follow
the exact same pair of model operations as the machine program.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Input history after one Detect and one fixed-graph refresh Update,
as performed by the complete machine iteration in Definition 4.5 (page 14). -/
def appendHistoryIteration (D : DynamicInstance) (T : ℕ) (es : List ℕ)
    (g l : ℕ → ℝ) : DynamicInstance :=
  appendHistoryStage (appendHistoryStage D T [] (D.g T) (D.ℓ T)) (T+1)
    (refreshEdges (D.G T) es) g l

/-- Detect ignores its normalization. Update uses the actual decoded scalar. -/
def appendHistoryIterationEta (eta : ℕ → ℝ) (T : ℕ) (actual : ℝ) : ℕ → ℝ :=
  Function.update (Function.update eta (T+1) 0) (T+1+1) actual

/-- The appended stages are Detect followed by Update. -/
def appendHistoryIterationOp (op : ℕ → Bool) (T : ℕ) : ℕ → Bool :=
  Function.update (Function.update op (T+1) false) (T+1+1) true

/-- Actual positive lengths and unreported coefficient preservation
make the complete decoded pair a valid extension of the old history. -/
theorem appendHistoryIteration_valid (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (es : List ℕ) (g l : ℕ → ℝ)
    (hes : ∀ e∈es,e∈(D.G T).E) (hl : ∀ e∈(D.G T).E,0<l e)
    (hunchanged : ∀ e∈(D.G T).E,e∉es → g e=D.g T e ∧ l e=D.ℓ T e) :
    MinRatioHistoryValid (appendHistoryIteration D T es g l) (appendHistoryIterationOp op T) (T+1+1) := by
  have hd := appendHistoryStage_valid_detect D op T hvalid
  have hv := appendHistoryStage_valid_refresh _ _ (T+1) hd es g l
    (by simpa only [appendHistoryStage,Function.update_self] using hes)
    (by simpa only [appendHistoryStage,Function.update_self] using hl)
    (by simpa only [appendHistoryStage,Function.update_self] using hunchanged)
  simpa only [appendHistoryIteration,appendHistoryIterationOp,appendHistoryStage,Function.update_self] using hv

/-- The appended Detect and Update stages keep a stage invariant when the new lengths
satisfy it on the current graph. -/
theorem appendHistoryIteration_stage_on {D : DynamicInstance} {T : ℕ} (es : List ℕ) (g l : ℕ → ℝ)
    {P : MGraph → (ℕ → ℝ) → Prop} (hP : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (hl : P (D.G T) l) :
    ∀ j ≤ T+1+1, P ((appendHistoryIteration D T es g l).G j)
      ((appendHistoryIteration D T es g l).ℓ j) := by
  have h1 := appendHistoryStage_stage_on (D := D) (T := T) [] (D.g T) (D.ℓ T) hP (hP T le_rfl)
  exact appendHistoryStage_stage_on _ g l h1 (by simpa only [appendHistoryStage,Function.update_self] using hl)

/-- The appended pair keeps every length of the history in `[2^{-E}, 2^E]` when the new
lengths are in that range. -/
theorem appendHistoryIteration_lengthsWithin {D : DynamicInstance} {T E : ℕ} (es : List ℕ)
    (g l : ℕ → ℝ) (hL : HistoryLengthsWithin D T E) (hl : LengthsWithin (D.G T) E l) :
    HistoryLengthsWithin (appendHistoryIteration D T es g l) (T+1+1) E :=
  appendHistoryIteration_stage_on (P := fun G l => LengthsWithin G E l) es g l hL hl

/-- The appended pair reaches exactly the state of the actual model
Update applied to the preceding Detect state. -/
theorem appendHistoryIteration_state (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) :
    minRatioState A (appendHistoryIteration D T es g l) (appendHistoryIterationEta eta T actual)
      (appendHistoryIterationOp op T) (T+1+1)=
      (A.update (A.detect (minRatioState A D eta op T)).2 (refreshEdges (D.G T) es) g l actual).1 := by
  unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
  rw [appendHistoryStage_update_state,appendHistoryStage_detect_state]

/-- Only the Detect half of the actual pair resets report times, using
exactly its reported set and its own stage index. -/
theorem appendHistoryIteration_last (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) (e : ℕ) :
    minRatioLast A (appendHistoryIteration D T es g l) (appendHistoryIterationEta eta T actual)
      (appendHistoryIterationOp op T) (T+1+1) e=
      if e∈(A.detect (minRatioState A D eta op T)).1 then T+1 else minRatioLast A D eta op T e := by
  unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
  rw [appendHistoryStage_update_last,appendHistoryStage_detect_last]

/-- Appending the actual pair preserves every previously accumulated
flow, including flows at old cached report times. -/
theorem appendHistoryIteration_past_flow (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (es : List ℕ) (g l : ℕ → ℝ)
    (actual : ℝ) (t e : ℕ) (ht : t≤T) :
    minRatioFlow A (appendHistoryIteration D T es g l) (appendHistoryIterationEta eta T actual)
      (appendHistoryIterationOp op T) t e=minRatioFlow A D eta op t e := by
  unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
  rw [appendHistoryStage_past_flow A _ _ _ (T+1) _ _ _ actual true t e (by omega)]
  exact appendHistoryStage_past_flow A D eta op T [] (D.g T) (D.ℓ T) 0 false t e ht

/-- The new cached report time refers to the pre-Update flow for reported
edges and the unchanged old cached flow for all other edges. -/
theorem appendHistoryIteration_last_flow (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (es : List ℕ) (g l : ℕ → ℝ)
    (actual : ℝ) (e : ℕ) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    minRatioFlow A D' eta' op' (minRatioLast A D' eta' op' (T+1+1) e) e=
      if e∈(A.detect (minRatioState A D eta op T)).1 then minRatioFlow A D eta op T e
      else minRatioFlow A D eta op (minRatioLast A D eta op T e) e := by
  dsimp only
  rw [appendHistoryIteration_last]
  split_ifs with he
  · unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
    rw [appendHistoryStage_past_flow A _ _ _ (T+1) _ _ _ actual true (T+1) e le_rfl]
    exact appendHistoryStage_detect_flow A D eta op T 0 e
  · exact appendHistoryIteration_past_flow A D eta op T es g l actual _ e
      (minRatioLast_le A D eta op T e)

/-- Refreshing exactly the reported cached coordinates preserves the
stored-flow invariant at every edge's actual `last_e` timestamp. -/
theorem appendHistoryIteration_cache_flow (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (es : List ℕ) (g l : ℕ → ℝ)
    (actual : ℝ) (base stored refreshed : ℕ → ℝ)
    (hcache : ∀ e,stored e=base e+minRatioFlow A D eta op (minRatioLast A D eta op T e) e)
    (hreported : ∀ e,e∈(A.detect (minRatioState A D eta op T)).1 →
      refreshed e=base e+minRatioFlow A D eta op T e)
    (hunreported : ∀ e,e∉(A.detect (minRatioState A D eta op T)).1 → refreshed e=stored e) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    ∀ e,refreshed e=base e+minRatioFlow A D' eta' op' (minRatioLast A D' eta' op' (T+1+1) e) e := by
  dsimp only
  intro e
  rw [appendHistoryIteration_last_flow]
  split_ifs with he
  · exact hreported e he
  · exact (hunreported e he).trans (hcache e)

/-- The state at the new cache timestamp is the actual Detect state
for reported edges and the original held state for unreported edges. -/
theorem appendHistoryIteration_last_state (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (es : List ℕ) (g l : ℕ → ℝ)
    (actual : ℝ) (e : ℕ) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    minRatioState A D' eta' op' (minRatioLast A D' eta' op' (T+1+1) e)=
      if e∈(A.detect (minRatioState A D eta op T)).1 then (A.detect (minRatioState A D eta op T)).2
      else minRatioState A D eta op (minRatioLast A D eta op T e) := by
  dsimp only
  rw [appendHistoryIteration_last]
  split_ifs with he
  · unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
    rw [appendHistoryStage_past_state A _ _ _ (T+1) _ _ _ actual true (T+1) le_rfl]
    exact appendHistoryStage_detect_state A D eta op T 0
  · have ht := minRatioLast_le A D eta op T e
    unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
    rw [appendHistoryStage_past_state A _ _ _ (T+1) _ _ _ actual true _ (by omega)]
    exact appendHistoryStage_past_state A D eta op T [] (D.g T) (D.ℓ T) 0 false _ ht

/-- The appended Detect and refresh Update keep the IPM's graph fixed
at every old and newly appended stage. -/
theorem appendHistoryIteration_fixed_graph (D : DynamicInstance) (G : MGraph) (T : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (hG : ∀ j≤T,D.G j=G) :
    ∀ j≤T+1+1,(appendHistoryIteration D T es g l).G j=G := by
  intro j hj
  by_cases hnew : j=T+1+1
  · subst j
    simpa only [appendHistoryIteration,appendHistoryStage,Function.update_self] using hG T le_rfl
  · by_cases hdetect : j=T+1
    · subst j
      simp only [appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : T+1≠T+1+1),
        Function.update_self,hG T le_rfl]
    · have hold : j≤T := by omega
      simpa only [appendHistoryIteration,appendHistoryStage,Function.update_of_ne hnew,
        Function.update_of_ne hdetect] using hG j hold

/-- With no reported names, unchanged old arrays satisfy all extension
conditions together on every valid old prefix. -/
theorem appendHistoryIteration_valid_empty (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) :
    MinRatioHistoryValid (appendHistoryIteration D T [] (D.g T) (D.ℓ T))
      (appendHistoryIterationOp op T) (T+1+1) := by
  apply appendHistoryIteration_valid D op T hvalid [] (D.g T) (D.ℓ T)
  · intro e he
    exact False.elim (List.not_mem_nil he)
  · exact (hvalid.2.1 T le_rfl).2
  · intro e _ _
    exact ⟨rfl,rfl⟩

end MinCostFlow.IPM.Machine
