module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullDefs
import MinCostFlow.DynSpanner.Program.DynSpannerAffectedFilter
import MinCostFlow.DynSpanner.Program.DynSpannerBuildProjInv

/-!
# The memory after the affected stage, in the words of the step

`dsAffStage_meetsContract` states its post with the context `AffCtx` of the stage, through the
memories after each of its three calls. The step for `0 < j` needs it as facts on the memory
`memAff` after the stage, in the form of the fields of `StepPosCtx`. `stepPosAff_facts` gives
them. It takes the context `a` with the values of its fields, so that the facts are stated
without `a`.

The facts come from the frame of each call. The candidates go to the heap after the list of
`S_{j-1}`, the affected edges after the candidates, and the projection writes the walk pointers,
the graph `J` in `aux`, the table `MEmbTemp` and its own heap after the affected edges. So
`memAff` agrees with the memory before the stage below its heap, outside the words of the stage,
and above the end of the heap of the projection. The walk pointers point to the walks
`Π_{<j}(e)` of the state, which lie in the footprint `footPi` of `a` and are kept.

`stepPosAff_pre` gives the bound in the precondition of the stage, and `stepPosAff_cost` bounds
its cost with the candidates replaced by all edges of `G'`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

private lemma map_sum_le_map_sum {f g : ℕ → ℕ} (hfg : ∀ e, f e ≤ g e) :
    ∀ l : List ℕ, (l.map f).sum ≤ (l.map g).sum
  | [] => le_rfl
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hfg x) (map_sum_le_map_sum hfg l)

/-- The end of the heap of the projection is below the bound `projHeapNeed`. -/
lemma projHeapAt_length_le (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap : ℕ) : projHeapAt G embLt S es heap es.length ≤ heap + projHeapNeed embLt es := by
  simp only [projHeapAt, projHeapNeed, List.take_length]
  have := map_sum_le_map_sum (f := projOutLen G embLt S)
    (g := fun e => 14 * (embLt e).length + 15)
    (fun e => by have := projOutLen_le G embLt S e; omega) es
  omega

/-- `projHeapNeed` as a sum of lengths. -/
lemma projHeapNeed_eq (embLt : Embedding) (es : List ℕ) :
    projHeapNeed embLt es = 14 * (es.map fun e => (embLt e).length).sum + 15 * es.length := by
  induction es with
  | nil => simp [projHeapNeed]
  | cons x xs ih =>
    simp only [projHeapNeed, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

/-- The candidates are edges of `G'`. -/
lemma AffCtx.candSet_subset (a : AffCtx) : a.candSet ⊆ a.G'.E := by
  intro e he
  simp only [AffCtx.candSet, Finset.mem_filter] at he
  exact he.1

/-- The precondition of `dsAffStage` from a bound with all edges of `G'` in the place of the
candidates. -/
lemma stepPosAff_pre (a : AffCtx)
    (hB : a.heapPtr + 2 + a.vCap + 3 * a.eCap +
      ∑ e ∈ a.G'.E, (14 * (a.piLt_mid e).length + 15) < 2 ^ a.w) :
    (dsAffStageContract a).pre [a.b, a.j, a.heapPtr] a.mem0 := by
  refine ⟨rfl, rfl, lt_of_le_of_lt ?_ hB⟩
  have : a.heapNeed ≤ ∑ e ∈ a.G'.E, (14 * (a.piLt_mid e).length + 15) :=
    Finset.sum_le_sum_of_subset a.candSet_subset
  omega

/-- The cost of `dsAffStage`, with the sets of candidates and of affected edges named. -/
lemma stepPosAff_cost (a : AffCtx) {C : ℕ} {Cs E : Finset ℕ}
    (hC : candRevSum a.L a.j a.revLists a.sPrevList = C) (hCs : a.candSet = Cs)
    (hE : a.affSet = E) (args : List ℕ) (mem : ℕ → ℕ) :
    (dsAffStageContract a).cost args mem =
      100 * C + 100 * (a.j * a.sPrevList.length) + 100 * a.sPrevList.length + 100 * a.j +
        100 * (∑ e ∈ Cs, (a.piLt_mid e).length) + 40 * (Cs.card * a.j) + 160 * Cs.card +
        E.card * (35 * a.j + 60) + (∑ e ∈ E, (800 * (a.piLt_mid e).length + 2000)) + 1200 := by
  simp only [dsAffStageContract, hC, hE, hCs]

end

end MinCostFlow.DynSpanner.Program
