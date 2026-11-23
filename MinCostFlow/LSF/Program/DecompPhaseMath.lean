module

public import MinCostFlow.LSF.Program.UpClosureMath
public import MinCostFlow.LSF.AuxiliaryTree
public import MinCostFlow.LSF.Model

/-!
# The arrays of `T_H` after the `T_H` stage

`thStageProc` leaves the parent index and the depth of every vertex in `T_H = hldAuxTree T₀ r₀`.
`thArrays_parDep` turns these facts into the form that `rootsStageProc` reads: the parents step
the depth down by one (`ParDep`), every depth is at most `hldDepthBound n`, and the root has depth
`0`.
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

@[expose] public section

lemma depth_self_zero (T : MGraph) (r : ℕ) (hT : IsRootedTree T r) : depth T r r = 0 := by
  unfold depth; rw [forestPath_self hT.isForest r, List.length_nil]

theorem thArrays_parDep {T₀ : MGraph} {vList : List ℕ} {n r : ℕ} {par dep : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hnd : vList.Nodup)
    (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList) (hlen : vList.length = n) (hr : r < n)
    (hpar : ∀ x < n, x ≠ r → par x < n ∧
      vList.getD (par x) 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0))
    (hdep : ∀ x < n, dep x =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0)) :
    ParDep n dep par ∧ (∀ x < n, dep x ≤ hldDepthBound n) ∧ dep r = 0 := by
  have hTH := hldAuxTree_isRootedTree hT
  have hroot : dep r = 0 := by rw [hdep r hr]; exact depth_self_zero _ _ hTH
  have hmem : ∀ x < n, vList.getD x 0 ∈ T₀.V := fun x hx =>
    (hV _).mpr (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hcard : T₀.V.card = n := by
    have : T₀.V = vList.toFinset := by ext v; rw [hV v, List.mem_toFinset]
    rw [this, List.toFinset_card_of_nodup hnd, hlen]
  refine ⟨fun x hx hd => ?_, fun x hx => ?_, hroot⟩
  · have hxr : x ≠ r := by rintro rfl; omega
    have hne : vList.getD x 0 ≠ vList.getD r 0 := by
      intro h
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
      exact hxr ((hnd.getElem_inj_iff).mp h)
    obtain ⟨hp, hpv⟩ := hpar x hx hxr
    refine ⟨hp, ?_⟩
    rw [hdep x hx, hdep _ hp, hpv]
    exact (hldAuxTree_parent hT (hmem x hx) hne).2.2
  · rw [hdep x hx, hldDepthBound, ← hcard]
    exact hldAuxTree_height hT (hmem x hx)

end

end MinCostFlow.LSF.Program
