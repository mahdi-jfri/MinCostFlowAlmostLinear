module

public import MinCostFlow.LSF.Program.THPlaceMath

/-!
# Parent and depth in `T_H`, one vertex at a time

The last pass of the `T_H` program walks the top-down order `Q`. At a vertex `x` with top `t`
and depth `pos = dep x - dep t` below it there are two cases.

* `pos = 0`: `x` is the top of its chain, so its parent in `T_H` is its parent in `T₀`, and its
  depth in `T_H` is one more than the depth of that parent (`th_top_step`).
* `pos > 0`: the parent of `x` in `T_H` comes from the balanced search over the rest of the chain,
  stored in the array from slot `off t + 1` on. The search `bstIdx` gives that parent and the
  depth `d` of `x` in the search tree, and the depth of `x` in `T_H` is `depth t + 1 + d`
  (`th_below_step`).

Both cases read only vertices that come earlier in `Q`: the parent, and in the second case the
top (`top_before`). `bstIdx_step` and `bstIdx_stop` are the two cases of the search loop.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-- The bound on depths in `T_H` (`hldAuxTree_height`). -/
def thBound (n : ℕ) : ℕ := (Nat.log 2 n + 1) * (Nat.log 2 n + 2)

/-- One step of the search, when `x` is not at the middle. -/
lemma bstIdx_step (above : ℕ) (A : ℕ → ℕ) (lo len j : ℕ) (h0 : len ≠ 0) (hj : j ≠ len / 2) :
    bstIdx above A lo len j =
      if j < len / 2 then
        ((bstIdx (A (lo + len / 2)) A lo (len / 2) j).1,
          (bstIdx (A (lo + len / 2)) A lo (len / 2) j).2 + 1)
      else
        ((bstIdx (A (lo + len / 2)) A (lo + len / 2 + 1) (len - len / 2 - 1) (j - len / 2 - 1)).1,
          (bstIdx (A (lo + len / 2)) A (lo + len / 2 + 1) (len - len / 2 - 1)
            (j - len / 2 - 1)).2 + 1) := by
  rw [bstIdx.eq_def above A lo len j]
  simp only [h0, dite_false, hj, if_false]

/-- The search stops at the middle. -/
lemma bstIdx_stop (above : ℕ) (A : ℕ → ℕ) (lo len j : ℕ) (hj : j = len / 2) :
    bstIdx above A lo len j = (above, 0) := by
  rw [bstIdx.eq_def above A lo len j]
  by_cases h0 : len = 0
  · simp [h0]
  · simp [h0, hj]

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

lemma TreeIdx.card_V (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) :
    T₀.V.card = vList.length := by
  classical
  have : T₀.V = vList.toFinset := by ext v; rw [List.mem_toFinset]; exact hI.hV v
  rw [this, List.toFinset_card_of_nodup hI.hnd]

lemma TreeIdx.thDepth_le (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {x : ℕ}
    (hx : x < vList.length) :
    depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) ≤
      thBound vList.length := by
  have := hldAuxTree_height hI.hT (hI.getD_mem hx)
  rwa [hI.card_V] at this

/-- The top of a vertex that is not its own top comes earlier in `Q`. -/
theorem top_before {n : ℕ} {Q : List ℕ} {sz top cnt : ℕ → ℕ} (hQ : TopDownOrder n r par Q)
    (hH : HeavyState Q par n r sz top cnt n) :
    ∀ x < n, top x ≠ x → top x ∈ Q.take (Q.idxOf x) := by
  obtain ⟨h1, -, h3, -⟩ := hH
  have htakeQ : Q.take n = Q := List.take_of_length_le (by rw [hQ.len])
  rw [htakeQ] at h3
  have key : ∀ k, ∀ x < n, Q.idxOf x = k → top x ≠ x → top x ∈ Q.take (Q.idxOf x) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hx hk hne
      have hxQ := hQ.cover x hx
      have hxr : x ≠ r := fun h => hne (by rw [h]; exact h1)
      have hidx : Q.idxOf x < Q.length := List.idxOf_lt_length_of_mem hxQ
      have hget : Q[Q.idxOf x] = x := List.getElem_idxOf hidx
      have hpQ : par x ∈ Q.take (Q.idxOf x) := by
        have := hQ.after (Q.idxOf x) hidx (by rw [hget]; exact hxr)
        rwa [hget] at this
      have hpidx : Q.idxOf (par x) < Q.idxOf x := by
        obtain ⟨i, hi, hiq⟩ := List.mem_take_iff_getElem.mp hpQ
        have hi' : i < Q.length := by omega
        have : Q.idxOf (par x) = i := by
          rw [← hiq]; exact hQ.nodup.idxOf_getElem i hi'
        omega
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      rw [h3 x hxQ hxr, heavyTop] at hne ⊢
      split_ifs at hne ⊢ with hh
      · by_cases hpp : top (par x) = par x
        · rw [hpp]; exact hpQ
        · have := ih _ (by omega) (par x) hpn rfl hpp
          exact (List.take_prefix_take_left (by omega)).subset this
      · exact absurd rfl hne
  exact fun x hx => key _ x hx rfl

section tree

variable {top cnt : ℕ → ℕ}

/-- The values in the chain array are indices. -/
lemma arr_lt (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (hB : TopsSpec T₀ vList r top)
    (hC : ∀ t < vList.length, top t = t →
      cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card)
    (hcard : ∀ s < vList.length,
      cnt s = ((Finset.range vList.length).filter (fun x => top x = s)).card)
    {arr : ℕ → ℕ} (harr : ∀ x < vList.length, arr (thSlot (offSum top cnt) top dep x) = x) :
    ∀ s < vList.length, arr s < vList.length := by
  classical
  set n := vList.length
  set f := thSlot (offSum top cnt) top dep with hf
  have hsub : (Finset.range n).image f ⊆ Finset.range n := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_range.mpr (thSlot_lt hI hB hC hcard (Finset.mem_range.mp hx))
  have hcard_im : ((Finset.range n).image f).card = n := by
    rw [Finset.card_image_of_injOn (fun x hx y hy h =>
      thSlot_inj hI hB hC (Finset.mem_range.mp hx) (Finset.mem_range.mp hy) h), Finset.card_range]
  have heq : (Finset.range n).image f = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard_im, Finset.card_range])
  intro s hs
  have : s ∈ (Finset.range n).image f := by rw [heq]; exact Finset.mem_range.mpr hs
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp this
  rw [harr x (Finset.mem_range.mp hx)]
  exact Finset.mem_range.mp hx

/-- The case `pos = 0`: `x` is the top of its chain. -/
theorem th_top_step (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (hB : TopsSpec T₀ vList r top) {x : ℕ} (hx : x < vList.length) (hxr : x ≠ r)
    (hle : dep (top x) ≤ dep x) (hpos : dep x - dep (top x) = 0) :
    vList.getD (par x) 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0) ∧
    depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD (par x) 0) + 1 := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have hCx := chainOf_mem_heavyChains (r := g r) (hI.getD_mem hx)
  have htn := (hB x hx).1
  have hb : g (top x) = chainTop T₀ (g r) (chainOf T₀ (g r) (g x)) := (hB x hx).2
  have htP : g (top x) ∈ chainOf T₀ (g r) (g x) := by
    rw [hb]; exact (chainTop_spec hI.hT hCx).1
  have hgt : g (top x) = g x := chain_eq_of_depth hI.hT hCx htP
    (mem_chainOf_self (hI.getD_mem hx)) (by rw [hI.depth_eq htn, hI.depth_eq hx]; omega)
  have htop : g x = chainTop T₀ (g r) (chainOf T₀ (g r) (g x)) := hgt.symm.trans hb
  have hpar : parent T₀ (g r) (g x) = g (par x) :=
    ((t0Rooted_spec hI.hT.isForest hI.hA hI.hnd hI.hR hI.hr hx).2 hxr).1
  have hth : thParent T₀ (g r) (g x) = g (par x) := by rw [thParent_top htop, hpar]
  have hgxr : g x ≠ g r := fun h => hxr (getD_inj hI.hnd hx hI.hr h)
  refine ⟨hth.symm, ?_⟩
  have := (hldAuxTree_parent hI.hT (hI.getD_mem hx) hgxr).2.2
  rw [hth] at this
  exact this

/-- The case `pos > 0`: the search over the rest of the chain. -/
theorem th_below_step (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (hB : TopsSpec T₀ vList r top)
    (hC : ∀ t < vList.length, top t = t →
      cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card)
    {arr : ℕ → ℕ} (harr : ∀ x < vList.length, arr (thSlot (offSum top cnt) top dep x) = x)
    {x : ℕ} (hx : x < vList.length) (hpos : dep (top x) < dep x) :
    vList.getD (bstIdx (top x) arr (offSum top cnt (top x) + 1) (cnt (top x) - 1)
        (dep x - dep (top x) - 1)).1 0 = thParent T₀ (vList.getD r 0) (vList.getD x 0) ∧
    depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD (top x) 0) + 1 +
        (bstIdx (top x) arr (offSum top cnt (top x) + 1) (cnt (top x) - 1)
          (dep x - dep (top x) - 1)).2 := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  set P := chainOf T₀ (g r) (g x) with hP
  have hPm : P ∈ heavyChains T₀ (g r) := chainOf_mem_heavyChains (hI.getD_mem hx)
  have htn := (hB x hx).1
  have hb : g (top x) = chainTop T₀ (g r) P := (hB x hx).2
  have htP : g (top x) ∈ P := by rw [hb]; exact (chainTop_spec hI.hT hPm).1
  have hEq : chainOf T₀ (g r) (g (top x)) = P := chainOf_eq_of_mem hPm htP
  have hct : cnt (top x) = P.card := by
    rw [hC _ htn (top_top hI hB hx)]; exact congrArg Finset.card hEq
  have hne : g x ≠ chainTop T₀ (g r) P := by
    intro h
    have := congrArg (depth T₀ (g r)) (h.trans hb.symm)
    rw [hI.depth_eq hx, hI.depth_eq htn] at this
    omega
  have hA := stored_chain hI hB hC harr hx
  obtain ⟨h1, h2⟩ := thParent_of_stored hI.hT (hI.getD_mem hx) (fun s => g (arr s))
    (offSum top cnt (top x)) hA hne
  have hmap := bstIdx_map g arr (P.card - 1) (top x) (offSum top cnt (top x) + 1)
    (depth T₀ (g r) (g x) - depth T₀ (g r) (chainTop T₀ (g r) P) - 1)
  have hcomp : (g ∘ arr) = fun s => g (arr s) := rfl
  rw [hcomp, hb] at hmap
  rw [hmap] at h1 h2
  dsimp only at h1 h2
  rw [← hb, hI.depth_eq hx, hI.depth_eq htn, ← hct] at h1 h2
  refine ⟨h1.symm, ?_⟩
  have hxP : g x ∈ P := mem_chainOf_self (hI.getD_mem hx)
  have htail : g x ∈ (chainList T₀ (g r) P).tail := (chainList_tail_mem_iff hI.hT hPm).mpr ⟨hxP, hne⟩
  have := thDepth_below_top hI.hT hPm _ (g x) htail (by exact h2)
  rw [← hb] at this
  exact this

end tree

end MinCostFlow.LSF.Program

end
