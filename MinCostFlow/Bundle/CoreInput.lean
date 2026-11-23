module

public import MinCostFlow.Bundle.CoreReleases
import MinCostFlow.SparseCore.CoreModel

/-!
# From input edits to ordered core batches

First apply the input operation to the graph and forest. Name the
resulting forest components with final roots, then release the other
edges cut by the LSF update.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner

private theorem orderedCore_split_named {G : MGraph} {L L' : LSF}
    {v v' fresh β : ℕ} {At Ah : Finset ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' At Ah)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.split v v' At Ah)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.split v v' At Ah)))
    (hForest : L'.F.F = L.F.F.applyUpdate (.split v v' At Ah))
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hu : G.UpdateIsValid (.split v v' At Ah)) (hs : RotationStep β (.split v v' At Ah) ρ σ) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hF') U ∧
      batchSplitCount U = 1 ∧ U.countP deleteTag = 0 := by
  let H := G.applyUpdate (.split v v' At Ah)
  let P : ℕ → ℕ := fun w => if w = v' then v else w
  let r := L.F.root v
  have hvf : v' ∉ L.F.F.V := fun h => hu.2.1 (hF.2.1 ▸ h)
  have hvG : v ∈ H.V := Finset.mem_insert_of_mem hu.1
  have hvG' : v' ∈ H.V := Finset.mem_insert_self _ _
  have hn : L'.F.root v ≠ L'.F.root v' := by
    intro he
    have hc := connected_of_root_eq hF' hvG hvG' he
    rw [hForest] at hc
    exact applySplit_separates hF.1 (hF.2.1.symm ▸ hu.1) hvf At Ah hc
  have hr (w : ℕ) (hw : w ∈ H.V) (he : P w = v) :
      L'.F.root w = r ∨ L'.F.root w = fresh := by
    obtain ⟨hwR, hc⟩ := root_mem_R hF' hw
    rw [hRoots] at hwR
    rcases Finset.mem_insert.mp hwR with hFresh | hOld
    · exact Or.inr hFresh
    · have htG := hF.2.2.1 hOld
      have hp : P (L'.F.root w) = L'.F.root w := by
        have hne : L'.F.root w ≠ v' := fun h => hu.2.1 (h ▸ htG)
        simp [P, hne]
      rw [hForest] at hc
      have hproj := connected_applySplit_proj hF.1.1 hvf At Ah hc
      change L.F.F.Connected (P w) (P (L'.F.root w)) at hproj
      rw [he, hp] at hproj
      exact Or.inl ((root_eq_of_mem_R hF hOld).symm.trans
        (root_eq_of_connected hF hu.1 htG hproj).symm)
  obtain ⟨side, hk, hm⟩ : ∃ side : Bool,
      L'.F.F.Connected (if side then v else v') r ∧
      L'.F.F.Connected (if side then v' else v) fresh := by
    rcases hr v hvG (by simp [P]) with h₁ | h₁ <;> rcases hr v' hvG' (by simp [P]) with h₂ | h₂
    · exact (hn (h₁.trans h₂.symm)).elim
    · refine ⟨true, ?_, ?_⟩
      · change L'.F.F.Connected v r
        exact h₁ ▸ (root_mem_R hF' hvG).2
      · change L'.F.F.Connected v' fresh
        exact h₂ ▸ (root_mem_R hF' hvG').2
    · refine ⟨false, ?_, ?_⟩
      · change L'.F.F.Connected v' r
        exact h₂ ▸ (root_mem_R hF' hvG').2
      · change L'.F.F.Connected v fresh
        exact h₁ ▸ (root_mem_R hF' hvG).2
    · exact (hn (h₁.trans h₂.symm)).elim
  obtain ⟨hv, he, ho⟩ := coreRotation_vertexSplit side ρ σ hG hH hF hF' hForest
    hRoots hf hk hm hu hs
  exact ⟨_, OrderedCoreBatch.singleton hv he ho, rfl, rfl⟩

private theorem forestAfterInput_root_sep {G : MGraph} {RF : RootedForest} {u : Update}
    (hF : RF.IsRootedSpanningForestOf G) (hu : G.UpdateIsValid u)
    {a b : ℕ} (ha : a ∈ RF.R) (hb : b ∈ RF.R)
    (hc : (forestAfterInput RF.F u).Connected a b) : a = b := by
  have hconn : RF.F.Connected a b := by
    cases u with
    | insert => exact hc
    | delete e => exact connected_of_subgraph (eraseForestEdge_subgraph _ e) hc
    | split v v' St Sh =>
      have hvf : v' ∉ RF.F.V := fun he => hu.2.1 (hF.2.1 ▸ he)
      have ha' : a ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 ha)
      have hb' : b ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 hb)
      exact by simpa [ha', hb'] using connected_applySplit_proj hF.1.1 hvf St Sh hc
  have hEq := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb) hconn
  rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hEq

/-- A deletion of an input forest edge counts as one core split. -/
@[expose] def forestDeleteTag (F : MGraph) : Update → ℕ
  | .delete e => if e ∈ F.E then 1 else 0
  | _ => 0

/-- The input edit has an ordered core batch before the additional
forest releases. Choose intermediate names from the final roots so
later cuts retain the names they inherit. -/
theorem orderedCore_input {G : MGraph} {L last : LSF} {β : ℕ} {u : Update}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate u))
    (hG : G.IsValid) (hH : (G.applyUpdate u).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hlast : last.F.IsRootedSpanningForestOf (G.applyUpdate u))
    (hu : G.UpdateIsValid u) (hs : RotationStep β u ρ σ) (hβ : 2 ≤ β)
    (hR : L.F.R ⊆ last.F.R)
    (hK : (forestAfterInput L.F.F u).IsForest)
    (hKG : (G.applyUpdate u).IsSubgraph (forestAfterInput L.F.F u))
    (hsub : (forestAfterInput L.F.F u).IsSubgraph last.F.F) :
    ∃ mid : LSF, ∃ hm : mid.F.IsRootedSpanningForestOf (G.applyUpdate u),
      mid.F.F = forestAfterInput L.F.F u ∧ L.F.R ⊆ mid.F.R ∧ mid.F.R ⊆ last.F.R ∧
      ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hm) U ∧
        batchSplitCount U = updateSplitTag u + forestDeleteTag L.F.F u ∧ U.countP deleteTag ≤ 1 := by
  have hKV : (forestAfterInput L.F.F u).V = (G.applyUpdate u).V := by
    cases u with
    | insert => exact hF.2.1
    | delete => exact hF.2.1
    | split => simp [forestAfterInput, MGraph.applyUpdate, hF.2.1]
  have hIntermediate := exists_roots_refinement hK hKV hKG hlast hsub hR
    (fun _ ha _ hb hc => forestAfterInput_root_sep hF hu ha hb hc)
  cases u with
  | insert e a b =>
    have hm : L.F.IsRootedSpanningForestOf (G.applyUpdate (.insert e a b)) :=
      ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hKG⟩
    obtain ⟨he, ho⟩ := coreRotation_insert ρ σ hG hH hF hm hu hs
    let op := Update.insert e (L.F.root a) (L.F.root b)
    have hv : (coreGraph G L).UpdateIsValid op :=
      ⟨fun h => hu.1 (Finset.mem_sdiff.mp h).1, (root_mem_R hF hu.2.1).1, (root_mem_R hF hu.2.2).1⟩
    exact ⟨L, hm, rfl, Finset.Subset.rfl, hR, [op], OrderedCoreBatch.singleton hv he ho, rfl, by simp [deleteTag]⟩
  | delete e =>
    by_cases he : e ∈ L.F.F.E
    · obtain ⟨R, hRo, hRf, hm⟩ := hIntermediate
      let mid : LSF := ⟨L.T, ⟨forestAfterInput L.F.F (.delete e), R⟩, L.wstr⟩
      have hcount : R.card = L.F.R.card + 1 := by
        rw [← rootedForest_components_card hm, ← rootedForest_components_card hF]
        exact forest_eraseEdge_components_card hF.1 he
      obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
      obtain ⟨U, ho, hC, hd⟩ := orderedCore_delete_forest (L' := mid) ρ σ hG hH hF hm he rfl hR' hnew hs hβ
      refine ⟨mid, hm, rfl, hRo, hRf, U, ho, ?_, ?_⟩
      · simpa [updateSplitTag, forestDeleteTag, he] using hC
      · simp [hd]
    · have hK_eq : forestAfterInput L.F.F (.delete e) = L.F.F := by
        change { L.F.F with E := L.F.F.E.erase e } = L.F.F
        rw [Finset.erase_eq_of_notMem he]
      have hHG : (G.applyUpdate (.delete e)).IsSubgraph L.F.F := hK_eq ▸ hKG
      have hm : L.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)) :=
        ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hHG⟩
      obtain ⟨hEq, ho⟩ := coreRotation_delete ρ σ hG hH hF hm he hs
      have hv : (coreGraph G L).UpdateIsValid (.delete e) := Finset.mem_sdiff.mpr ⟨hu, he⟩
      refine ⟨L, hm, hK_eq.symm, Finset.Subset.rfl, hR, [.delete e], OrderedCoreBatch.singleton hv hEq ho, ?_, ?_⟩
      · simp [batchSplitCount, updateSplitTag, forestDeleteTag, he, isSplit]
      · simp [deleteTag]
  | split v v' St Sh =>
    obtain ⟨R, hRo, hRf, hm⟩ := hIntermediate
    let mid : LSF := ⟨L.T, ⟨forestAfterInput L.F.F (.split v v' St Sh), R⟩, L.wstr⟩
    have hcount : R.card = L.F.R.card + 1 := by
      have ho := rootedForest_R_add_edges hF
      have hn := rootedForest_R_add_edges hm
      have hv : (G.applyUpdate (.split v v' St Sh)).V.card = G.V.card + 1 :=
        Finset.card_insert_of_notMem hu.2.1
      change R.card + L.F.F.E.card = (G.applyUpdate (.split v v' St Sh)).V.card at hn
      omega
    obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
    obtain ⟨U, ho, hC, hd⟩ := orderedCore_split_named (L' := mid) ρ σ hG hH hF hm rfl hR' hnew hu hs
    exact ⟨mid, hm, rfl, hRo, hRf, U, ho, hC, hd ▸ Nat.zero_le _⟩

end MinCostFlow.Bundle
