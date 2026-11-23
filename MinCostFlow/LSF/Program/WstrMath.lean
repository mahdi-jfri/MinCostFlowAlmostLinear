module

public import MinCostFlow.LSF.Program.FRIdx
public import MinCostFlow.LSF.Program.WDepth
public import MinCostFlow.LSF.Program.TreeDist

/-!
# From index arrays to tree distances

The stretch program works with vertex indices and integer lengths. This file links what it
computes to the model.

* `lca_bridge`: the index that `lcaProc` returns (`IsLcaOf`) names the vertex `lca T₀ r₀ u v`.
* `ld_bridge`: the weighted depths `Ld` of `wDepthProc` are `S` times the weighted depths `wDepth`
  of the model, when every tree length is `S` times its real length and no value overflows.
* `treeDist_bridge`: hence the value of `treeDistProc` is `S` times the length of the tree path.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.Num

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

lemma TreeIdx.exists_idx (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {v : ℕ}
    (hv : v ∈ T₀.V) : ∃ c < vList.length, vList.getD c 0 = v := by
  obtain ⟨c, hc, hcv⟩ := List.mem_iff_getElem.mp ((hI.hV v).mp hv)
  exact ⟨c, hc, by rw [List.getD_eq_getElem _ _ hc, hcv]⟩

lemma TreeIdx.anc_iff (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {x z : ℕ}
    (hx : x < vList.length) (hz : z < vList.length) :
    IsAncestor T₀ (vList.getD r 0) (vList.getD z 0) (vList.getD x 0) ↔ AncOf par dep z x :=
  t0Rooted_isAncestor_iff hI.hT.isForest hI.hA hI.hnd hI.hR hI.hr hx hz

/-- The index of the lowest common ancestor names `lca`. -/
theorem lca_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {l x y : ℕ}
    (hl : l < vList.length) (hx : x < vList.length) (hy : y < vList.length)
    (h : IsLcaOf par dep l x y) :
    vList.getD l 0 = lca T₀ (vList.getD r 0) (vList.getD x 0) (vList.getD y 0) := by
  obtain ⟨hzV, hzu, hzv, hmax⟩ := lca_spec hI.hT (hI.getD_mem hx) (hI.getD_mem hy)
  obtain ⟨c, hc, hcz⟩ := hI.exists_idx hzV
  refine isAncestor_antisymm hI.hT (hI.getD_mem hl) hzV
    (hmax _ ((hI.anc_iff hx hl).mpr h.1) ((hI.anc_iff hy hl).mpr h.2.1)) ?_
  rw [← hcz] at hzu hzv ⊢
  exact (hI.anc_iff hl hc).mpr (h.2.2 c ((hI.anc_iff hx hc).mp hzu) ((hI.anc_iff hy hc).mp hzv))

/-- The weighted depths of `wDepthProc` are `S` times the weighted depths of the model. The
hypothesis `hfit` says that no value reaches the capacity. -/
theorem ld_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {h LB S : ℕ}
    {lt Ld : ℕ → ℕ} {ℓ : ℕ → ℝ} (hLd_r : Ld r = 0)
    (hrule : ∀ x < vList.length, x ≠ r → LdRule h LB par pe lt Ld x)
    (hlt : ∀ i < tM, (lt i : ℝ) = S * ℓ (fid i))
    (hfit : ∀ x < vList.length,
      (S : ℝ) * wDepth T₀ (vList.getD r 0) ℓ (vList.getD x 0) < capacity h LB) :
    ∀ x < vList.length, (Ld x : ℝ) = S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD x 0) := by
  suffices H : ∀ d x, x < vList.length → dep x = d →
      (Ld x : ℝ) = S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD x 0) from
    fun x hx => H _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hx hd
    by_cases hxr : x = r
    · subst hxr
      rw [hLd_r, wDepth_root hI.hT]; simp
    obtain ⟨hpx, hpe, hdep, hpar, hpedge⟩ := hI.step hx hxr
    have hgx : vList.getD x 0 ≠ vList.getD r 0 := fun h' => hxr (hI.getD_inj hx hI.hr h')
    have hstep := wDepth_step hI.hT ℓ (hI.getD_mem hx) hgx
    rw [hpar, hpedge] at hstep
    have hih := ih _ (by omega) (par x) hpx rfl
    have hsum : ((Ld (par x) + lt (pe x) : ℕ) : ℝ) =
        S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD x 0) := by
      push_cast
      rw [hih, hlt _ hpe, hstep]; ring
    have hlt' : Ld (par x) + lt (pe x) < capacity h LB := by
      have := hfit x hx
      rw [← hsum] at this
      exact_mod_cast this
    rw [hrule x hx hxr, Nat.mod_eq_of_lt hlt', hsum]

/-- The length of the tree path between `x` and `y` from weighted depths and the lowest common
ancestor index. -/
theorem treeDist_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {S c : ℕ}
    {Ld : ℕ → ℕ} {ℓ : ℕ → ℝ} {l x y : ℕ} (hℓ : ∀ f ∈ T₀.E, 0 ≤ ℓ f)
    (hLd : ∀ z < vList.length, (Ld z : ℝ) = S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD z 0))
    (hl : l < vList.length) (hx : x < vList.length) (hy : y < vList.length)
    (h : IsLcaOf par dep l x y) (hfit : Ld x + Ld y < c) :
    (distMod c (Ld x) (Ld y) (Ld l) : ℝ) =
      S * walkLength ℓ (T₀.forestPath (vList.getD x 0) (vList.getD y 0)) := by
  have hll := lca_bridge hI hl hx hy h
  -- The lowest common ancestor is an ancestor of both, so its depth is at most theirs.
  have hmono : ∀ z < vList.length, AncOf par dep l z → Ld l ≤ Ld z := by
    intro z hz hlz
    have hanc := (hI.anc_iff hz hl).mpr hlz
    have hnn := walkLength_nonneg_of_nonneg ℓ (fun f hf => hℓ f
      (walkEdges_forestPath_subset hI.hT (hI.getD_mem hz) (hI.getD_mem hl) hf))
    rw [walkLength_forestPath_anc hI.hT ℓ (hI.getD_mem hz) hanc] at hnn
    have h1 : (Ld l : ℝ) ≤ Ld z := by
      rw [hLd l hl, hLd z hz]
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    exact_mod_cast h1
  have hlx := hmono x hx h.1
  have hly := hmono y hy h.2.1
  rw [distMod_eq hlx hly hfit, walkLength_forestPath_lca hI.hT ℓ (hI.getD_mem hx)
    (hI.getD_mem hy), ← hll]
  push_cast [Nat.cast_sub (show 2 * Ld l ≤ Ld x + Ld y by omega)]
  rw [hLd x hx, hLd y hy, hLd l hl]; ring

end MinCostFlow.LSF.Program
