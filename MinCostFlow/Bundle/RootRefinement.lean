module

public import MinCostFlow.LSF.Components

/-!
# Naming intermediate forest components

When a forest is refined, each intermediate component contains a final
root. Keep any root already assigned to that component. If it has none,
choose a final root from it.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.LSF

/-- An intermediate forest can be rooted using final root names while
retaining the roots already chosen for distinct components. -/
theorem exists_roots_refinement {G F : MGraph} {final : RootedForest} {old : Finset ℕ}
    (hF : F.IsForest) (hV : F.V = G.V) (hFG : G.IsSubgraph F)
    (hfinal : final.IsRootedSpanningForestOf G) (hsub : F.IsSubgraph final.F)
    (hOld : old ⊆ final.R)
    (hSep : ∀ r ∈ old, ∀ s ∈ old, F.Connected r s → r = s) :
    ∃ R : Finset ℕ, old ⊆ R ∧ R ⊆ final.R ∧ (RootedForest.mk F R).IsRootedSpanningForestOf G := by
  classical
  have hAvail : ∀ A ∈ components F, ∃ r, r ∈ A ∧ r ∈ final.R := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
    have hvG : v ∈ G.V := hV ▸ hv
    obtain ⟨r, ⟨hr, hc⟩, _⟩ := hfinal.2.2.2.1 v hvG
    have hrF : r ∈ F.V := hV.symm ▸ hfinal.2.2.1 hr
    exact ⟨r, mem_compOf_iff.mpr ⟨hrF, connected_of_subgraph hsub hc⟩, hr⟩
  let pick (A : Finset ℕ) : ℕ :=
    if h : ∃ r, r ∈ A ∧ r ∈ old then Classical.choose h
    else if h : ∃ r, r ∈ A ∧ r ∈ final.R then Classical.choose h else 0
  have hPick (A : Finset ℕ) (hA : A ∈ components F) :
      pick A ∈ A ∧ pick A ∈ final.R := by
    by_cases h : ∃ r, r ∈ A ∧ r ∈ old
    · have hc := Classical.choose_spec h
      simpa only [pick, h, ↓reduceDIte] using And.intro hc.1 (hOld hc.2)
    · have ha := hAvail A hA
      simpa only [pick, h, ha, ↓reduceDIte] using Classical.choose_spec ha
  let R := (components F).image pick
  have hR : R ⊆ final.R := by
    intro r hr
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hr
    exact (hPick A hA).2
  refine ⟨R, ?_, hR, hF, hV, fun _ hr => hfinal.2.2.1 (hR hr), ?_, hFG⟩
  · intro r hr
    have hrF : r ∈ F.V := hV.symm ▸ hfinal.2.2.1 (hOld hr)
    let A := compOf F r
    have ha : ∃ s, s ∈ A ∧ s ∈ old := ⟨r, self_mem_compOf hrF, hr⟩
    have hc := Classical.choose_spec ha
    have hp : pick A = r := by
      have hconn := (mem_compOf_iff.mp hc.1).2
      simpa only [pick, ha, ↓reduceDIte] using hSep _ hc.2 r hr (connected_symm hconn)
    exact hp ▸ Finset.mem_image_of_mem pick (compOf_mem_components hrF)
  · intro v hv
    have hvF : v ∈ F.V := hV.symm ▸ hv
    let A := compOf F v
    have ha : A ∈ components F := compOf_mem_components hvF
    exact ⟨pick A, ⟨Finset.mem_image_of_mem pick ha, (mem_compOf_iff.mp (hPick A ha).1).2⟩,
      fun w hw => by
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hw.1
        obtain ⟨u, huV, rfl⟩ := Finset.mem_image.mp hT
        have hu := (mem_compOf_iff.mp (hPick (compOf F u) (compOf_mem_components huV)).1).2
        exact congrArg pick (compOf_eq_of_connected (connected_trans hu (connected_symm hw.2)))⟩

end MinCostFlow.Bundle
