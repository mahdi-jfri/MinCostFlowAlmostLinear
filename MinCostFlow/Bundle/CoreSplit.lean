module

public import MinCostFlow.Bundle.CoreOpenStep
public import MinCostFlow.Bundle.TourSplit
import MinCostFlow.SparseCore.CoreModel

/-!
# Core splits induced by vertex splits

Splitting a vertex in both the graph and the forest sends whole tour
blocks to each side. Either side can retain the old core root's name.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-- A simultaneous vertex split of the graph and the forest gives an
ordered core split with the input boundary bound. -/
theorem coreRotation_vertexSplit {G : MGraph} {L L' : LSF}
    {v v' fresh β : ℕ} {At Ah : Finset ℕ} (side : Bool)
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' At Ah)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.split v v' At Ah)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.split v v' At Ah)))
    (hForest : L'.F.F = L.F.F.applyUpdate (.split v v' At Ah))
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hKeep : L'.F.F.Connected (if side then v else v') (L.F.root v))
    (hMove : L'.F.F.Connected (if side then v' else v) fresh)
    (hu : G.UpdateIsValid (.split v v' At Ah)) (hσ : RotationStep β (.split v v' At Ah) ρ σ) :
    let C := coreGraph G L
    let C' := coreGraph (G.applyUpdate (.split v v' At Ah)) L'
    let St := C.E.filter fun e => C'.tail e = fresh
    let Sh := C.E.filter fun e => C'.head e = fresh
    let op := Update.split (L.F.root v) fresh St Sh
    C.UpdateIsValid op ∧ ∃ h : GraphEq C' (C.applyUpdate op),
      RotationStep β op (coreRotation ρ hG hF) ((coreRotation σ hH hF').congrGraph h) := by
  intro C C' St Sh op
  let F := L.F.F
  let H := G.applyUpdate (.split v v' At Ah)
  let P : ℕ → ℕ := fun w => if w = v' then v else w
  let r := L.F.root v
  have hr := (root_mem_R hF hu.1).1
  have hvf : v' ∉ F.V := fun h => hu.2.1 (hF.2.1 ▸ h)
  have hpV (w : ℕ) (hw : w ∈ H.V) : P w ∈ G.V := by
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa [P] using hu.1
    · have hn : w ≠ v' := fun h => hu.2.1 (h ▸ hw)
      simpa [P, hn] using hw
  have hfix (w : ℕ) (hw : w ∈ G.V) : P w = w := by
    have hn : w ≠ v' := fun h => hu.2.1 (h ▸ hw)
    simp [P, hn]
  have hproj (a b : ℕ) (h : L'.F.F.Connected a b) : F.Connected (P a) (P b) :=
    connected_applySplit_proj hF.1.1 hvf At Ah (hForest ▸ h)
  have hFresh : fresh ∈ L'.F.R := hRoots ▸ Finset.mem_insert_self _ _
  have hFreshOld : L.F.root (P fresh) = r := by
    have hcF := hproj _ _ hMove
    have hpv : P (if side then v' else v) = v := by cases side <;> simp [P]
    rw [hpv] at hcF
    exact (root_eq_of_connected hF hu.1 (hpV _ (hF'.2.2.1 hFresh)) hcF).symm
  have hRootProj (y : ℕ) (hy : y ∈ H.V) :
      L.F.root (P y) = L.F.root (P (L'.F.root y)) := by
    have ⟨hyr, hc⟩ := root_mem_R hF' hy
    exact root_eq_of_connected hF (hpV _ hy) (hpV _ (hF'.2.2.1 hyr)) (hproj _ _ hc)
  have hNewRoot (y : ℕ) (hy : y ∈ H.V) :
      L'.F.root y = if L'.F.root y = fresh ∧ L.F.root (P y) = r then fresh else L.F.root (P y) := by
    have ⟨hyR, hc⟩ := root_mem_R hF' hy
    have htarget := hpV _ (hF'.2.2.1 hyR)
    have he := root_eq_of_connected hF (hpV _ hy) htarget (hproj _ _ hc)
    by_cases hEq : L'.F.root y = fresh
    · simp [hEq, he, hFreshOld]
    · have ht : L'.F.root y ∈ L.F.R := by
        rw [hRoots] at hyR
        exact (Finset.mem_insert.mp hyR).resolve_left hEq
      simp [hEq, he, hfix _ (hF.2.2.1 ht), root_eq_of_mem_R hF ht]
  have hFE : L'.F.F.E = L.F.F.E := by rw [hForest]; rfl
  have hE : C'.E = C.E := by
    change G.E \ L'.F.F.E = G.E \ L.F.F.E
    rw [hFE]
  have hTarget (e : ℕ) (he : e ∈ C.E) :
      C'.tail e = (if C'.tail e = fresh ∧ C.tail e = r then fresh else C.tail e) ∧
      C'.head e = (if C'.head e = fresh ∧ C.head e = r then fresh else C.head e) := by
    have he₀ := (Finset.mem_sdiff.mp he).1
    have hends := hH e he₀
    have hstep := stepProj_applyUpdate_eq hG hu he₀ he₀
    change P (H.tail e) = G.tail e ∧ P (H.head e) = G.head e at hstep
    have ht := hNewRoot (H.tail e) hends.1
    have hh := hNewRoot (H.head e) hends.2
    rw [hstep.1] at ht
    rw [hstep.2] at hh
    exact ⟨ht, hh⟩
  have heq : GraphEq C' (C.applyUpdate op) := by
    refine ⟨hRoots, hE, ?_⟩
    intro e he
    have he' : e ∈ C.E := hE ▸ he
    obtain ⟨ht, hh⟩ := hTarget e he'
    change C'.tail e = (if e ∈ St ∧ C.tail e = r then fresh else C.tail e) ∧
      C'.head e = (if e ∈ Sh ∧ C.head e = r then fresh else C.head e)
    simpa [St, Sh, he'] using (And.intro ht hh)
  refine ⟨⟨hr, hf, Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_⟩,
    heq, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with ht | hh
    · obtain ⟨he', hf'⟩ := Finset.mem_filter.mp ht
      have he₀ := (Finset.mem_sdiff.mp he').1
      have hrel := hRootProj (H.tail e) (hH e he₀).1
      have hstep := (stepProj_applyUpdate_eq hG hu he₀ he₀).1
      change P (H.tail e) = G.tail e at hstep
      change L'.F.root (H.tail e) = fresh at hf'
      rw [hstep, hf', hFreshOld] at hrel
      exact Or.inl hrel
    · obtain ⟨he', hf'⟩ := Finset.mem_filter.mp hh
      have he₀ := (Finset.mem_sdiff.mp he').1
      have hrel := hRootProj (H.head e) (hH e he₀).2
      have hstep := (stepProj_applyUpdate_eq hG hu he₀ he₀).2
      change P (H.head e) = G.head e at hstep
      change L'.F.root (H.head e) = fresh at hf'
      rw [hstep, hf', hFreshOld] at hrel
      exact Or.inr hrel
  let old := coreRotation ρ hG hF
  let new := coreRotation σ hH hF'
  let p0 : End → Bool := fun x => (movedTourEnds ρ hF.1 v (splitEnds At Ah)).contains x
  let p : End → Bool := if side then p0 else fun x => !(p0 x)
  have hOld (w : ℕ) (hw : w ∈ L.F.R) : old.order w = tour ρ hF.1 w := by
    simp [old, coreRotation, hw]
  have hNew (w : ℕ) (hw : w ∈ L'.F.R) : new.order w = tour σ hF'.1 w := by
    simp [new, coreRotation, hw]
  have hOldRot := tour_isRotated_of_connected ρ hF.1 hF.2.2.2.2 (root_mem_R hF hu.1).2
  have hF'' : (F.applyUpdate (.split v v' At Ah)).IsForest := hForest ▸ hF'.1
  obtain ⟨hm, hk⟩ := tour_applySplit_restrict ρ σ hG hF.1 hF''
    hF.2.2.2.2 hF.2.1 (applySplit_subgraph hF.2.2.2.2 v v' At Ah) hu.2.1 hσ
  rw [tour_congr_forest σ _ hF'.1 hForest.symm] at hk hm
  change (tour σ hF'.1 v').IsRotated ((tour ρ hF.1 v).filter p0) at hm
  have hCompl : (tour σ hF'.1 v).IsRotated ((tour ρ hF.1 v).filter fun x => !(p0 x)) := by
    rw [List.filter_congr (fun _ hz => movedTourEnds_complement ρ hG hF.1 hF.2.2.2.2 hF.2.1
      (splitEnds At Ah) hz)] at hk
    exact hk
  have hM : (tour σ hF'.1 (if side then v' else v)).IsRotated
      ((tour ρ hF.1 v).filter p) := by
    cases side
    · exact hCompl
    · exact hm
  have hK : (tour σ hF'.1 (if side then v else v')).IsRotated
      ((tour ρ hF.1 v).filter fun x => !(p x)) := by
    cases side
    · simpa [p] using hm
    · exact hCompl
  change RotationStep β op old (new.congrGraph heq)
  apply rotationStep_split_of_parts (ρ := old) (σ := new.congrGraph heq) (fun hh => hf (hh ▸ hr)) p
  · change (new.order r).IsRotated _
    rw [hNew _ (hRoots ▸ Finset.mem_insert_of_mem hr), hOld _ hr]
    exact (tour_isRotated_of_connected σ hF'.1 hF'.2.2.2.2 (connected_symm hKeep)).trans
      (hK.trans (isRotated_filter _ hOldRot))
  · change (new.order fresh).IsRotated _
    rw [hNew _ hFresh, hOld _ hr]
    exact (tour_isRotated_of_connected σ hF'.1 hF'.2.2.2.2 (connected_symm hMove)).trans
      (hM.trans (isRotated_filter _ hOldRot))
  · rw [hOld _ hr, ← cycBdry_isRotated p hOldRot]
    have hb := (tour_split_boundary_le ρ hG hF.1 hF.2.2.2.2 hF.2.1 v (splitEnds At Ah)).trans hσ.2.2.1
    cases side
    · change cycBdry (fun x => !(p0 x)) _ ≤ β
      rw [cycBdry_compl]
      exact hb
    · exact hb
  · intro w hwr hwf
    change (new.order w).IsRotated (old.order w)
    by_cases hw : w ∈ L.F.R
    · rw [hNew _ (hRoots ▸ Finset.mem_insert_of_mem hw), hOld _ hw]
      have hwV := hF.2.2.1 hw
      have hn : ¬ F.Connected w v := fun hc =>
        hwr ((root_eq_of_mem_R hF hw).symm.trans (root_eq_of_connected hF hwV hu.1 hc))
      have hh := tour_applySplit_untouched ρ σ hF.1 hF'' hF.2.2.2.2
        (hF.2.1.symm ▸ hwV) hu.2.1 hσ hn
      rw [tour_congr_forest σ _ hF'.1 hForest.symm] at hh
      exact hh.symm
    · have hw' : w ∉ L'.F.R := by rw [hRoots, Finset.mem_insert]; exact not_or.mpr ⟨hwf, hw⟩
      simp only [old, new, coreRotation, hw, hw', ↓reduceIte]
      exact List.IsRotated.refl []

end MinCostFlow.Bundle
