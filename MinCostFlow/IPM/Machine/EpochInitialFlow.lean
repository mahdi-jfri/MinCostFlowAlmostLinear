module

public import MinCostFlow.IPM.Machine.MinRatioContract
import MinCostFlow.IPM.Machine.HistoryAppend

import MinCostFlow.IPM.Machine.MinRatioBridge

/-!
# Zero implicit flow at the start of an epoch

Definition 4.5 specifies Query on every valid history, including its
initial prefix. A constant graph and constant positive lengths give
such a history. Hence Init contributes zero implicit flow, as required
when the epoch's explicit coordinates become its new base flow.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The failure-aware specification on `P` forces the initialized
structure's Query value to be zero on every edge of `G`. -/
theorem minRatio_init_query_zero_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (G : MGraph) (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps G.m G.n)
    (g l : ℕ → ℝ) (hP : P G l) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : ∀ e∈G.E,A.query (A.init G g l) e=0 := by
  let D : DynamicInstance := ⟨fun _ => G,fun _ => [],fun _ => g,fun _ => l⟩
  have hvalid : MinRatioHistoryValid D (fun _ => false) 0 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht ht'
      omega
    · intro t ht
      exact ⟨hG,hl⟩
    · intro t ht ht' _
      omega
    · intro t ht ht' _ _ _
      omega
  intro e he
  have hh := (hA D (fun _ => 0) (fun _ => false) 0 hvalid ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩
    (fun _ _ => hP)).1.1 0 le_rfl e he
  exact hh.trans (minRatioFlow_zero A.eraseFailure D (fun _ => 0) (fun _ => false) e)

/-- The original failure-aware specification forces the initialized
structure's Query value to be zero on every graph edge. No hidden
stability or representational uniqueness premise is needed. -/
theorem minRatio_init_query_zero_upTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) 
    (G : MGraph) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps G.m G.n) (g l : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : ∀ e∈G.E,A.query (A.init G g l) e=0 :=
  minRatio_init_query_zero_upTo_on A κ α Ψ eps G (hA.upToOn (P := fun _ _ => True)) g l trivial hG hl

/-- The original failure-aware specification forces the initialized
structure's Query value to be zero on every graph edge. No hidden
stability or representational uniqueness premise is needed. -/
theorem minRatio_init_query_zero (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (G : MGraph) (g l : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : ∀ e∈G.E,A.query (A.init G g l) e=0 :=
  minRatio_init_query_zero_upTo A κ α Ψ eps G (hA.upTo G.m G.n) g l hG hl

/-- Once Query is zero, the newly explicit epoch base exactly equals the
sum of the base and implicit flow, on every edge, under `P`. -/
theorem minRatio_init_base_flow_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (G : MGraph) (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps G.m G.n)
    (g l base : ℕ → ℝ) (hP : P G l) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : ∀ e∈G.E,base e+A.query (A.init G g l) e=base e := by
  intro e he
  rw [minRatio_init_query_zero_upTo_on A κ α Ψ eps G hA g l hP hG hl e he,add_zero]

/-- Once Query is zero, the newly explicit epoch base exactly equals the
sum of the base and implicit flow, on every edge. -/
theorem minRatio_init_base_flow_upTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) 
    (G : MGraph) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps G.m G.n) (g l base : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : ∀ e∈G.E,base e+A.query (A.init G g l) e=base e :=
  minRatio_init_base_flow_upTo_on A κ α Ψ eps G (hA.upToOn (P := fun _ _ => True)) g l base trivial hG hl

/-- Once Query is zero, the newly explicit epoch base exactly equals the
sum of the base and implicit flow, on every edge. -/
theorem minRatio_init_base_flow (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (G : MGraph) (g l base : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : ∀ e∈G.E,base e+A.query (A.init G g l) e=base e :=
  minRatio_init_base_flow_upTo A κ α Ψ eps G (hA.upTo G.m G.n) g l base hG hl

/-- With positive detection threshold, the first Detect reports no
edges under `P`. -/
theorem minRatio_init_detect_empty_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ) (heps : 0<eps)
    (G : MGraph) (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps G.m G.n)
    (g l : ℕ → ℝ) (hP : P G l) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : (A.detect (A.init G g l)).1=∅ := by
  let D : DynamicInstance := ⟨fun _ => G,fun _ => [],fun _ => g,fun _ => l⟩
  have hvalid : MinRatioHistoryValid D (fun _ => false) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t _ _
      exact ⟨trivial,rfl⟩
    · intro t _
      exact ⟨hG,hl⟩
    · intro t _ _ _
      exact ⟨rfl,rfl,rfl⟩
    · intro t _ _ _ _ _
      exact ⟨rfl,rfl⟩
  have hh := (hA D (fun _ => 0) (fun _ => false) 1 hvalid ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩
    (fun _ _ => hP)).1.2.2 0 le_rfl rfl
  change (A.detect (A.init G g l)).1=_ at hh
  rw [hh]
  have hinc (j e : ℕ) : minRatioIncrement A.eraseFailure D (fun _ => 0) (fun _ => false) j e=0 := by
    cases j <;> simp [minRatioIncrement]
  simp only [minRatioDetectSet,hinc,abs_zero,Finset.sum_const_zero,mul_zero]
  exact Finset.filter_eq_empty_iff.mpr (fun _ _ => not_le_of_gt heps)

/-- With positive detection threshold, the first Detect reports no
edges. There has been no Update increment since initialization. -/
theorem minRatio_init_detect_empty_upTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ)  (heps : 0<eps)
    (G : MGraph) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps G.m G.n) (g l : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : (A.detect (A.init G g l)).1=∅ :=
  minRatio_init_detect_empty_upTo_on A κ α Ψ eps heps G (hA.upToOn (P := fun _ _ => True)) g l trivial hG hl

/-- With positive detection threshold, the first Detect reports no
edges. There has been no Update increment since initialization. -/
theorem minRatio_init_detect_empty (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) (hA : MinRatioSpecWithFailure A κ α Ψ eps) (heps : 0<eps)
    (G : MGraph) (g l : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) : (A.detect (A.init G g l)).1=∅ :=
  minRatio_init_detect_empty_upTo A κ α Ψ eps heps G (hA.upTo G.m G.n) g l hG hl

/-- The first Detect preserves zero implicit flow under `P`. -/
theorem minRatio_init_detect_query_zero_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (G : MGraph) (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps G.m G.n)
    (g l : ℕ → ℝ) (hP : P G l) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) :
    ∀ e∈G.E,A.query (A.detect (A.init G g l)).2 e=0 := by
  let D : DynamicInstance := ⟨fun _ => G,fun _ => [],fun _ => g,fun _ => l⟩
  have hvalid : MinRatioHistoryValid D (fun _ => false) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t _ _
      exact ⟨trivial,rfl⟩
    · intro t _
      exact ⟨hG,hl⟩
    · intro t _ _ _
      exact ⟨rfl,rfl,rfl⟩
    · intro t _ _ _ _ _
      exact ⟨rfl,rfl⟩
  intro e he
  have hh := (hA D (fun _ => 0) (fun _ => false) 1 hvalid ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩
    (fun _ _ => hP)).1.1 1 le_rfl e he
  change A.query (A.detect (A.init G g l)).2 e=_ at hh
  rw [hh]
  have hinc (j : ℕ) : minRatioIncrement A.eraseFailure D (fun _ => 0) (fun _ => false) j e=0 := by
    cases j <;> simp [minRatioIncrement]
  simp only [minRatioFlow,hinc,Finset.sum_const_zero]

/-- The first Detect preserves zero implicit flow. This gives the
initial post-Detect Query bound directly from the original model spec. -/
theorem minRatio_init_detect_query_zero_upTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) 
    (G : MGraph) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps G.m G.n) (g l : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) :
    ∀ e∈G.E,A.query (A.detect (A.init G g l)).2 e=0 :=
  minRatio_init_detect_query_zero_upTo_on A κ α Ψ eps G (hA.upToOn (P := fun _ _ => True)) g l trivial hG hl

/-- The first Detect preserves zero implicit flow. This gives the
initial post-Detect Query bound directly from the original model spec. -/
theorem minRatio_init_detect_query_zero (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (G : MGraph) (g l : ℕ → ℝ) (hG : G.IsValid)
    (hl : ∀ e∈G.E,0<l e) :
    ∀ e∈G.E,A.query (A.detect (A.init G g l)).2 e=0 :=
  minRatio_init_detect_query_zero_upTo A κ α Ψ eps G (hA.upTo G.m G.n) g l hG hl

/-- Detect on any valid current history satisfying `P` reports only current
graph edges. -/
theorem minRatio_valid_detect_subset_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) :
    (A.detect (minRatioState A.eraseFailure D eta op T)).1⊆(D.G T).E := by
  let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  let eta' := Function.update eta (T+1) 0
  let op' := Function.update op (T+1) false
  have hv : MinRatioHistoryValid D' op' (T+1) := appendHistoryStage_valid_detect D op T hvalid
  have hP' := appendHistoryStage_stage_on (D:=D) (T:=T) [] (D.g T) (D.ℓ T) hP (hP T le_rfl)
  have hs := (hA D' eta' op' (T+1) hv (appendHistoryStage_bounded [] _ _ hsize) hP').1.2.2 T le_rfl (by simp [op'])
  dsimp only [D',eta',op'] at hs
  rw [appendHistoryStage_past_state A.eraseFailure D eta op T [] (D.g T) (D.ℓ T) 0 false T le_rfl] at hs
  intro e he
  have he' : e∈minRatioDetectSet A.eraseFailure (appendHistoryStage D T [] (D.g T) (D.ℓ T))
      (Function.update eta (T+1) 0) (Function.update op (T+1) false) eps T := by
    rw [← hs]
    exact he
  have hh := (Finset.mem_filter.mp he').1
  simpa only [appendHistoryStage,Function.update_self] using hh

/-- Detect on any valid current history reports only current graph
edges. Append its unchanged input to apply the original unconditional
Detect specification, with no hidden stability premise. -/
theorem minRatio_valid_detect_subset_upTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) :
    (A.detect (minRatioState A.eraseFailure D eta op T)).1⊆(D.G T).E :=
  minRatio_valid_detect_subset_upTo_on A κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) D eta op T hvalid hsize (fun _ _ => trivial)

/-- Detect on any valid current history reports only current graph
edges. Append its unchanged input to apply the original unconditional
Detect specification, with no hidden stability premise. -/
theorem minRatio_valid_detect_subset (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) :
    (A.detect (minRatioState A.eraseFailure D eta op T)).1⊆(D.G T).E := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact minRatio_valid_detect_subset_upTo A κ α Ψ eps (hA.upTo M N) D eta op T hvalid hsize

end MinCostFlow.IPM.Machine
