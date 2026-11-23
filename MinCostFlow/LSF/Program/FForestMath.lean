module

public import MinCostFlow.LSF.Program.FRIdx

/-!
# The forest `F` on vertex indices

The roots pass (`FRIdx.lean`) gives three arrays for a root set `R`: `mp`, the owner array
`own` and the root array `rt`. This file reads the forest `F = forestGivenRoots T₀ r₀ R π` off
them.

* `own_ne_zero_iff`: the tree edge with index `i` is deleted exactly when `own i ≠ 0`.
* `forest_E_eq`: so the edges of `F` are the edges `fid i` with `own i = 0`.
* `connected_iff_rt`: an index `x` is connected in `F` to a root index `c` exactly when
  `rt x = c`.
* `compCard_eq`: the size of the component of a root `c` is the number of indices `x` with
  `rt x = c`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

/-- The facts of the three passes of the roots pass for the root set `R`. -/
structure RootPassIdx (T₀ : MGraph) (vList : List ℕ) (tM r : ℕ) (fid par pe : ℕ → ℕ)
    (R : Finset ℕ) (π : ℕ → ℕ) (inR piv mp own rt : ℕ → ℕ) : Prop where
  hS : RootSetIdx T₀ vList tM r fid R π inR piv
  hmp : ∀ x < vList.length, x ≠ r → MpRule inR par pe piv mp x
  hown : OwnState r tM inR mp own vList.length
  hrt_r : rt r = r
  hrule : ∀ x < vList.length, x ≠ r → RtRule inR par pe own rt x

variable {R : Finset ℕ} {π inR piv mp own rt : ℕ → ℕ}

/-- The tree edge with index `i` is deleted exactly when it has an owner. -/
theorem own_ne_zero_iff (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt) {i : ℕ} (hi : i < tM) :
    own i ≠ 0 ↔ fid i ∈ deletedEdges T₀ (vList.getD r 0) R π := by
  classical
  have hMP := mp_bridge hI h.hS h.hmp
  unfold deletedEdges
  rw [if_pos ⟨_, h.hS.hrR⟩, topRoot_eq_of_mem hI.hT h.hS.hR h.hS.hrR, Finset.mem_image]
  constructor
  · intro hne
    obtain ⟨a, b, c, d⟩ := (h.hown i hi).1 hne
    refine ⟨vList.getD (own i - 1) 0, Finset.mem_erase.mpr
      ⟨fun he => b (hI.getD_inj a hI.hr he), (h.hS.hinR _ a).mp c⟩, ?_⟩
    rw [deletedEdge_eq_upMin, ← (hMP _ a b).2, d]
  · rintro ⟨y, hy, hyd⟩ hz
    obtain ⟨hyr, hyR⟩ := Finset.mem_erase.mp hy
    have hyl : y ∈ vList := (hI.hV y).mp (h.hS.hR.1 hyR)
    have hyi := List.idxOf_lt_length_of_mem hyl
    have hgy := getD_idxOf hyl
    have hyr' : vList.idxOf y ≠ r := fun he => hyr (by rw [← hgy, he])
    have hyR' : inR (vList.idxOf y) = 1 := (h.hS.hinR _ hyi).mpr (by rw [hgy]; exact hyR)
    obtain ⟨hmpl, hmpf⟩ := hMP _ hyi hyr'
    have hmpi : mp (vList.idxOf y) = i := by
      refine hI.hA.fid_inj _ hmpl _ hi ?_
      rw [hmpf, hgy, ← deletedEdge_eq_upMin, hyd]
    exact (h.hown i hi).2 hz _ hyi hyr' hyR' hmpi

/-- The edges of `F` are the tree edges without an owner. -/
theorem forest_E_eq (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt) :
    (forestGivenRoots T₀ (vList.getD r 0) R π).E =
      ((Finset.range tM).filter (fun i => own i = 0)).image fid := by
  classical
  ext f
  simp only [forestGivenRoots, Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨hf, hnd⟩
    obtain ⟨i, hi, rfl⟩ := hI.hA.fid_cover f hf
    refine ⟨i, ⟨hi, ?_⟩, rfl⟩
    by_contra hne
    exact hnd ((own_ne_zero_iff hI h hi).mp hne)
  · rintro ⟨i, ⟨hi, hz⟩, rfl⟩
    exact ⟨hI.hA.fid_mem i hi, fun hd' => (own_ne_zero_iff hI h hi).mpr hd' hz⟩

/-- An index is connected to a root index in `F` exactly when that root is its `rt`. -/
theorem connected_iff_rt (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt) {x c : ℕ}
    (hx : x < vList.length) (hc : c < vList.length) (hcR : vList.getD c 0 ∈ R) :
    (forestGivenRoots T₀ (vList.getD r 0) R π).Connected (vList.getD x 0) (vList.getD c 0) ↔
      rt x = c := by
  have hB := rt_bridge hI h.hS h.hmp h.hown h.hrt_r h.hrule
  obtain ⟨hrl, hrR, hconn⟩ := hB x hx
  constructor
  · intro hxc
    by_contra hne
    have hne' : vList.getD (rt x) 0 ≠ vList.getD c 0 := fun he => hne (hI.getD_inj hrl hc he)
    exact forestGivenRoots_not_connected_roots hI.hT h.hS.hR ⟨_, h.hS.hrR⟩ π hrR hcR hne'
      (connected_trans (connected_symm hconn) hxc)
  · rintro rfl
    exact hconn

open Classical in
/-- The size of the component of a root index `c` is the number of indices with root `c`. -/
theorem compCard_eq (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt) {c : ℕ}
    (hc : c < vList.length) (hcR : vList.getD c 0 ∈ R) :
    ((forestGivenRoots T₀ (vList.getD r 0) R π).V.filter
        (fun u => (forestGivenRoots T₀ (vList.getD r 0) R π).Connected u (vList.getD c 0))).card =
      ((Finset.range vList.length).filter (fun x => rt x = c)).card := by
  have hV : (forestGivenRoots T₀ (vList.getD r 0) R π).V =
      (Finset.range vList.length).image (fun x => vList.getD x 0) := by
    ext v
    simp only [forestGivenRoots, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hv
      have hl := (hI.hV v).mp hv
      exact ⟨_, List.idxOf_lt_length_of_mem hl, getD_idxOf hl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hI.getD_mem hx
  rw [hV, Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hcx⟩
      exact ⟨hx, (connected_iff_rt hI h hx hc hcR).mp hcx⟩
    · rintro ⟨hx, hrx⟩
      exact ⟨hx, (connected_iff_rt hI h hx hc hcR).mpr hrx⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    exact hI.getD_inj ha.1 hb.1 hab

end MinCostFlow.LSF.Program

end
