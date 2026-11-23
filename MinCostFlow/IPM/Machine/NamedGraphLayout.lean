module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.IPM.NamedInstance
import WordRAM.Memory

/-!
# The fixed IPM graph in the min-ratio input layout

The shared named graph keeps the original vertex and edge indices.
Canonical sorting turns its vertex names into `0,...,n-1` and its edge
names into `0,...,m-1`. The remaining words are the source endpoints.
This gives a direct serialization target for data-structure initialization.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The exact min-ratio graph encoding for the fixed named instance. -/
theorem graphWords_namedInstance (I : Instance) :
    graphWords (namedInstance I) = [I.n,I.m] ++ List.range I.n ++
      (List.range I.m).flatMap (fun e => [e,(namedInstance I).tail e,(namedInstance I).head e]) := by
  simp only [graphWords,namedInstance,Finset.card_range,Finset.sort_range]

/-- Its encoded size includes every vertex name, including isolated ones. -/
theorem graphWords_namedInstance_length (I : Instance) :
    (graphWords (namedInstance I)).length=2+I.n+3*I.m := by
  rw [graphWords_namedInstance]
  simp [List.length_flatMap]
  omega

/-- Valid endpoints and fitting input dimensions imply that every word
of the named-graph serialization fits, without a bound relating n and m. -/
theorem graphWords_namedInstance_words_fit (I : Instance) (hI : I.IsValid) {w : ℕ}
    (hn : I.n < 2^w) (hm : I.m < 2^w) :
    ∀ x ∈ graphWords (namedInstance I),x < 2^w := by
  intro x hx
  rw [graphWords_namedInstance] at hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range,List.mem_flatMap] at hx
  rcases hx with ((rfl | rfl) | hx) | ⟨e,he,hx⟩
  · exact hn
  · exact hm
  · exact hx.trans hn
  · have hv := namedInstance_valid I hI e (Finset.mem_range.mpr he)
    rcases hx with rfl | rfl | rfl
    · exact he.trans hm
    · exact (Finset.mem_range.mp hv.1).trans hn
    · exact (Finset.mem_range.mp hv.2).trans hn

end MinCostFlow.IPM.Machine
