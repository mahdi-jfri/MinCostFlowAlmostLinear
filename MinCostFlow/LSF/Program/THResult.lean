module

public import MinCostFlow.LSF.Program.THDepth

/-!
# What the `T_H` passes compute

`THArrays` collects the facts about the arrays after the size, heavy, offset and placing passes.
From them:

* `thDepthIn_of`: the input facts of the last pass hold with `D` the depth in `T_H` and
  `B = thBound n`;
* `th_bridge`: the parent and depth rules of the last pass give the parent and the depth in
  `T_H` (`hldAuxTree`). The proof is by induction along `Q`: the vertices the rules read come
  earlier in `Q`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-- The arrays after the first four passes. -/
structure THArrays (T₀ : MGraph) (vList : List ℕ) (tM r : ℕ) (fid tl hd par pe dep : ℕ → ℕ)
    (Q : List ℕ) (sz top cnt off arr : ℕ → ℕ) : Prop where
  hI : TreeIdx T₀ vList tM r fid tl hd par pe dep
  hQ : TopDownOrder vList.length r par Q
  hH : HeavyState Q par vList.length r sz top cnt vList.length
  hB : TopsSpec T₀ vList r top
  hC : ∀ t < vList.length, top t = t →
    cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card
  hcard : ∀ s < vList.length,
    cnt s = ((Finset.range vList.length).filter (fun x => top x = s)).card
  hoff : ∀ t < vList.length, off t = offSum top cnt t
  harr : ∀ x < vList.length, arr (thSlot (offSum top cnt) top dep x) = x
  hdep : ∀ x < vList.length, dep x < vList.length

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ} {Q : List ℕ}
  {sz top cnt off arr : ℕ → ℕ}

lemma thDepth_root (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) :
    depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD r 0) = 0 := by
  unfold depth
  rw [forestPath_self (hldAuxTree_isRootedTree hI.hT).isForest _, List.length_nil]

lemma THArrays.thR_eq (h : THArrays T₀ vList tM r fid tl hd par pe dep Q sz top cnt off arr)
    {x : ℕ} (hx : x < vList.length) :
    thR top dep cnt off arr x = bstIdx (top x) arr (offSum top cnt (top x) + 1) (cnt (top x) - 1)
      (dep x - dep (top x) - 1) := by
  unfold thR; rw [h.hoff _ (h.hB x hx).1]

/-- The two cases at one vertex other than the root. -/
lemma THArrays.step (h : THArrays T₀ vList tM r fid tl hd par pe dep Q sz top cnt off arr)
    {x : ℕ} (hx : x < vList.length) (hxr : x ≠ r) :
    (dep x - dep (top x) = 0 →
      vList.getD (par x) 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0) ∧
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) =
        depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD (par x) 0) + 1) ∧
    (dep x - dep (top x) ≠ 0 →
      vList.getD (thR top dep cnt off arr x).1 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0) ∧
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) =
        depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD (top x) 0) + 1 +
          (thR top dep cnt off arr x).2) := by
  have hle := (pos_lt h.hI h.hB h.hC hx).1
  refine ⟨fun h0 => th_top_step h.hI h.hB hx hxr hle h0, fun h0 => ?_⟩
  rw [h.thR_eq hx]
  exact th_below_step h.hI h.hB h.hC h.harr hx (by omega)

/-- The input facts of the last pass, with the depths in `T_H`. -/
theorem thDepthIn_of (h : THArrays T₀ vList tM r fid tl hd par pe dep Q sz top cnt off arr) :
    THDepthIn vList.length r Q par top dep cnt off arr (thBound vList.length)
      (fun x => depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0)) := by
  refine ⟨fun x hx => (h.hB x hx).1, h.hdep, fun x hx => (pos_lt h.hI h.hB h.hC hx).2,
    fun x hx => ?_, arr_lt h.hI h.hB h.hC h.hcard h.harr,
    fun x hx _ hne => top_before h.hQ h.hH x hx (fun he => hne (by rw [he]; omega)),
    thDepth_root h.hI, fun x hx => h.hI.thDepth_le hx, fun x hx hxr => ?_⟩
  · have htn := (h.hB x hx).1
    have htt := top_top h.hI h.hB hx
    have h2 := offSum_le h.hcard (fun y hy => top_top h.hI h.hB hy)
      (show top x + 1 ≤ vList.length by omega)
    rw [offSum_succ, if_pos htt] at h2
    rw [h.hoff _ htn]; exact h2
  · unfold DepthRule
    dsimp only
    split_ifs with h0
    · exact ((h.step hx hxr).1 h0).2
    · exact ((h.step hx hxr).2 h0).2

/-- The outputs of the last pass are the parents and depths in `T_H`. -/
theorem th_bridge (h : THArrays T₀ vList tM r fid tl hd par pe dep Q sz top cnt off arr)
    {thPar dTH : ℕ → ℕ} (hdr : dTH r = 0)
    (hrule : ∀ x < vList.length, x ≠ r →
      ParRule par top dep cnt off arr thPar x ∧ DepthRule par top dep cnt off arr dTH x) :
    ∀ x < vList.length,
      dTH x = depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) ∧
      (x ≠ r → vList.getD (thPar x) 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0)) := by
  set n := vList.length with hn
  have hQ := h.hQ
  have hpar_mem : ∀ x < n, x ≠ r → Q.idxOf (par x) < Q.idxOf x ∧ par x < n := by
    intro x hx hxr
    have hxQ := hQ.cover x hx
    have hi := List.idxOf_lt_length_of_mem hxQ
    have hget : Q[Q.idxOf x] = x := List.getElem_idxOf hi
    have hpQ := hQ.after _ hi (by rw [hget]; exact hxr)
    rw [hget] at hpQ
    obtain ⟨i, hi', hiq⟩ := List.mem_take_iff_getElem.mp hpQ
    have : Q.idxOf (par x) = i := by rw [← hiq]; exact hQ.nodup.idxOf_getElem i (by omega)
    exact ⟨by omega, hQ.lt _ (List.mem_of_mem_take hpQ)⟩
  have htop_mem : ∀ x < n, x ≠ r → dep x - dep (top x) ≠ 0 → Q.idxOf (top x) < Q.idxOf x := by
    intro x hx hxr h0
    have htx : top x ≠ x := fun he => h0 (by rw [he]; omega)
    have htQ := top_before hQ h.hH x hx htx
    have hi := List.idxOf_lt_length_of_mem (hQ.cover x hx)
    obtain ⟨i, hi', hiq⟩ := List.mem_take_iff_getElem.mp htQ
    have : Q.idxOf (top x) = i := by rw [← hiq]; exact hQ.nodup.idxOf_getElem i (by omega)
    omega
  have key : ∀ k, ∀ x < n, Q.idxOf x = k →
      dTH x = depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hx hk
      by_cases hxr : x = r
      · rw [hxr, hdr, thDepth_root h.hI]
      · obtain ⟨-, hD⟩ := hrule x hx hxr
        unfold DepthRule at hD
        rw [hD]
        split_ifs with h0
        · obtain ⟨hlt, hpn⟩ := hpar_mem x hx hxr
          rw [ih _ (by omega) _ hpn rfl, ((h.step hx hxr).1 h0).2]
        · have hlt := htop_mem x hx hxr h0
          rw [ih _ (by omega) _ (h.hB x hx).1 rfl, ((h.step hx hxr).2 h0).2]
  refine fun x hx => ⟨key _ x hx rfl, fun hxr => ?_⟩
  obtain ⟨hP, -⟩ := hrule x hx hxr
  unfold ParRule at hP
  rw [hP]
  split_ifs with h0
  · exact ((h.step hx hxr).1 h0).1
  · exact ((h.step hx hxr).2 h0).1

lemma rootedArrays_congr {n tM r : ℕ} {tl hd par pe dep par' dep' : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) (hr : r < n)
    (hpar : ∀ x < n, par' x = par x) (hdep : ∀ x < n, dep' x = dep x) :
    RootedArrays n tM r tl hd par' pe dep' := by
  refine ⟨by rw [hpar r hr]; exact hR.par_r, by rw [hdep r hr]; exact hR.dep_r,
    fun x hx => by rw [hpar x hx]; exact hR.par_lt x hx, fun x hx hxr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hR.step x hx hxr
  rw [hpar x hx, hdep x hx, hdep _ (hR.par_lt x hx)]
  exact ⟨h1, h2, h3⟩

lemma heavyState_congr_input {n : ℕ} (hQ : TopDownOrder n r par Q) {par' sz' : ℕ → ℕ}
    {j : ℕ} (hpar : ∀ x < n, par' x = par x) (hsz : ∀ x < n, sz' x = sz x)
    (h : HeavyState Q par n r sz top cnt j) : HeavyState Q par' n r sz' top cnt j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun x hx hxr => ?_, h4⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [List.length_take] at hk
  have hxr' := hxr
  rw [List.getElem_take] at hxr'
  have hkQ : k < Q.length := by omega
  have hpQ := hQ.after k hkQ hxr'
  have hpn : par Q[k] < n := hQ.lt _ (List.mem_of_mem_take hpQ)
  have hxn : Q[k] < n := hQ.lt _ (List.getElem_mem hkQ)
  rw [h3 _ hx hxr, heavyTop, heavyTop]
  simp only [List.getElem_take]
  rw [hpar _ hxn, hsz _ hxn, hsz _ hpn]

lemma offSum_congr {top cnt top' cnt' : ℕ → ℕ} {n t : ℕ} (ht : t ≤ n)
    (htop : ∀ x < n, top' x = top x) (hcnt : ∀ x < n, cnt' x = cnt x) :
    offSum top' cnt' t = offSum top cnt t := by
  unfold offSum
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [Finset.mem_range] at hs
  rw [htop s (by omega), hcnt s (by omega)]

/-- `THArrays` only reads the arrays below `n`. -/
theorem THArrays.congr (h : THArrays T₀ vList tM r fid tl hd par pe dep Q sz top cnt off arr)
    {par' dep' sz' top' cnt' off' arr' : ℕ → ℕ}
    (hpar : ∀ x < vList.length, par' x = par x) (hdep : ∀ x < vList.length, dep' x = dep x)
    (hsz : ∀ x < vList.length, sz' x = sz x) (htop : ∀ x < vList.length, top' x = top x)
    (hcnt : ∀ x < vList.length, cnt' x = cnt x) (hoff : ∀ x < vList.length, off' x = off x)
    (harr : ∀ x < vList.length, arr' x = arr x) :
    THArrays T₀ vList tM r fid tl hd par' pe dep' Q sz' top' cnt' off' arr' := by
  classical
  have hI := h.hI
  have hR' := rootedArrays_congr hI.hR hI.hr hpar hdep
  have hI' : TreeIdx T₀ vList tM r fid tl hd par' pe dep' :=
    ⟨hI.hT, hI.hA, hI.hnd, hI.hV, hR', hI.hr⟩
  have hQ' := h.hQ.congr (fun x hx => (hpar x hx).symm)
  have hB' : TopsSpec T₀ vList r top' := fun x hx => by rw [htop x hx]; exact h.hB x hx
  have hoS : ∀ t ≤ vList.length, offSum top' cnt' t = offSum top cnt t :=
    fun t ht => offSum_congr ht htop hcnt
  refine ⟨hI', hQ', ?_, hB', fun t ht htt => ?_, fun s hs => ?_, fun t ht => ?_, fun x hx => ?_,
    fun x hx => by rw [hdep x hx]; exact h.hdep x hx⟩
  · have := heavyState_congr_input h.hQ hpar hsz h.hH
    exact heavyState_congr hQ' hI.hr (fun x hx => htop x hx) (fun t ht => hcnt t ht) this
  · rw [hcnt t ht]; exact h.hC t ht (by rw [← htop t ht]; exact htt)
  · rw [hcnt s hs, h.hcard s hs]
    congr 1
    exact Finset.filter_congr (fun x hx => by rw [htop x (Finset.mem_range.mp hx)])
  · rw [hoff t ht, h.hoff t ht, hoS t (by omega)]
  · have htn := (h.hB x hx).1
    have hslot : thSlot (offSum top' cnt') top' dep' x = thSlot (offSum top cnt) top dep x := by
      unfold thSlot
      rw [htop x hx, hoS _ (by omega), hdep x hx, hdep _ htn]
    rw [hslot, harr _ (thSlot_lt hI h.hB h.hC h.hcard hx)]
    exact h.harr x hx

/-- The size, heavy, offset and placing passes give `THArrays`. -/
theorem thArrays_of (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (hQ : TopDownOrder vList.length r par Q) {acc : ℕ → ℕ}
    (hS : SizeState Q par vList.length acc sz 1) (hroot : sz r = acc r + 1)
    (hH : HeavyState Q par vList.length r sz top cnt vList.length)
    (hoff : ∀ t < vList.length, off t = offSum top cnt t)
    (harr : ∀ x < vList.length, arr (thSlot (offSum top cnt) top dep x) = x)
    (hdep : ∀ x < vList.length, dep x < vList.length) :
    THArrays T₀ vList tM r fid tl hd par pe dep Q sz top cnt off arr := by
  have hsz := size_bridge hI.hT hI.hA hI.hnd hI.hV hI.hR hI.hr hQ hS hroot
  have hB : TopsSpec T₀ vList r top :=
    heavy_bridge hI.hT hI.hA hI.hnd hI.hV hI.hR hI.hr hQ hsz hH
  exact ⟨hI, hQ, hH, hB, fun t ht htt => heavy_count hI.hT hI.hnd hI.hV hQ hH hB ht htt,
    cnt_card_of_heavyState hQ hH, hoff, harr, hdep⟩

/-- The sizes are at most `n`. -/
lemma sz_le_of (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (hQ : TopDownOrder vList.length r par Q) {acc : ℕ → ℕ}
    (hS : SizeState Q par vList.length acc sz 1) (hroot : sz r = acc r + 1) :
    ∀ x < vList.length, sz x ≤ vList.length := by
  have hsz := size_bridge hI.hT hI.hA hI.hnd hI.hV hI.hR hI.hr hQ hS hroot
  intro x hx
  rw [hsz x hx, ← hI.card_V]
  exact Finset.card_le_card (fun u hu => (mem_subtree_iff.mp hu).1)

end MinCostFlow.LSF.Program

end
