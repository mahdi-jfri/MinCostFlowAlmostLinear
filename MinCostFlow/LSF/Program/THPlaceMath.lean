module

public import MinCostFlow.LSF.Program.THHeavyMath
public import MinCostFlow.LSF.Program.THAuxMath

/-!
# Storing the chains in one array

After the heavy pass every index `x` has its top `top x` and every top `t` has the size `cnt t`
of its chain. The program now stores all chains in one array of `n` words. The chain with top `t`
gets the block that starts at `offSum top cnt t`, the sum of the sizes of the chains whose tops
are below `t`. The index `x` goes to the slot `thSlot … x`, which is the start of the block of its
chain plus its depth below the top.

* `offSum_eq_card`: the start of a block counts the indices whose top is below `t`, so every
  start is at most `n`.
* `thSlot_lt`, `thSlot_inj`: the slots are below `n` and distinct, so writing `x` at its slot for
  every `x` leaves `arr (thSlot x) = x`.
* `stored_chain`: then the block of a chain holds the chain from the top down, which is what
  `thParent_of_stored` (`THAuxMath.lean`) asks for.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-- The arrays of a rooted tree `T₀` on the vertex list `vList`, with root index `r`. -/
structure TreeIdx (T₀ : MGraph) (vList : List ℕ) (tM r : ℕ) (fid tl hd par pe dep : ℕ → ℕ) :
    Prop where
  hT : IsRootedTree T₀ (vList.getD r 0)
  hA : T0IndexArrays T₀ vList tM fid tl hd
  hnd : vList.Nodup
  hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList
  hR : RootedArrays vList.length tM r tl hd par pe dep
  hr : r < vList.length

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

lemma TreeIdx.getD_mem (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {x : ℕ}
    (hx : x < vList.length) : vList.getD x 0 ∈ T₀.V :=
  (hI.hV _).mpr (by rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)

lemma TreeIdx.depth_eq (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {x : ℕ}
    (hx : x < vList.length) : depth T₀ (vList.getD r 0) (vList.getD x 0) = dep x :=
  (t0Rooted_spec hI.hT.isForest hI.hA hI.hnd hI.hR hI.hr hx).1

/-- The start of the block of the chain with top `t`. -/
def offSum (top cnt : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, if top s = s then cnt s else 0

/-- The slot of `x`. -/
def thSlot (off top dep : ℕ → ℕ) (x : ℕ) : ℕ := off (top x) + (dep x - dep (top x))

lemma offSum_succ (top cnt : ℕ → ℕ) (t : ℕ) :
    offSum top cnt (t + 1) = offSum top cnt t + if top t = t then cnt t else 0 := by
  rw [offSum, Finset.sum_range_succ]; rfl

lemma offSum_mono (top cnt : ℕ → ℕ) {t t' : ℕ} (h : t ≤ t') :
    offSum top cnt t ≤ offSum top cnt t' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- The count at an index, as the number of indices with that top. -/
lemma cnt_card_of_heavyState {Q : List ℕ} {n : ℕ} {sz top cnt : ℕ → ℕ}
    (hQ : TopDownOrder n r par Q) (hH : HeavyState Q par n r sz top cnt n) :
    ∀ s < n, cnt s = ((Finset.range n).filter (fun x => top x = s)).card := by
  classical
  intro s hs
  have h4 := hH.2.2.2 s hs
  rw [List.take_of_length_le (by rw [hQ.len])] at h4
  rw [h4, ← List.toFinset_card_of_nodup (hQ.nodup.filter _), List.toFinset_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_range, decide_eq_true_eq]
  exact ⟨fun h => ⟨hQ.lt x h.1, h.2⟩, fun h => ⟨hQ.cover x h.1, h.2⟩⟩

/-- When every top is its own top, the start of a block counts the indices whose top is below
it. -/
lemma offSum_eq_card {n : ℕ} {top cnt : ℕ → ℕ}
    (hcard : ∀ s < n, cnt s = ((Finset.range n).filter (fun x => top x = s)).card)
    (htt : ∀ x < n, top (top x) = top x) :
    ∀ t ≤ n, offSum top cnt t = ((Finset.range n).filter (fun x => top x < t)).card := by
  classical
  intro t
  induction t with
  | zero => intro _; simp [offSum]
  | succ t ih =>
    intro ht
    rw [offSum_succ, ih (by omega)]
    have hsplit : (Finset.range n).filter (fun x => top x < t + 1) =
        (Finset.range n).filter (fun x => top x < t) ∪
          (Finset.range n).filter (fun x => top x = t) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hm, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        exacts [Or.inl ⟨hm, h⟩, Or.inr ⟨hm, h⟩]
      · rintro (⟨hm, h⟩ | ⟨hm, h⟩)
        exacts [⟨hm, by omega⟩, ⟨hm, by omega⟩]
    have hdisj : Disjoint ((Finset.range n).filter (fun x => top x < t))
        ((Finset.range n).filter (fun x => top x = t)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    split_ifs with htt'
    · rw [hcard t (by omega)]
    · have hempty : (Finset.range n).filter (fun x => top x = t) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx hxt
        rw [Finset.mem_range] at hx
        exact htt' (by have := htt x hx; rw [hxt] at this; exact this)
      rw [hempty, Finset.card_empty]

lemma offSum_le {n : ℕ} {top cnt : ℕ → ℕ}
    (hcard : ∀ s < n, cnt s = ((Finset.range n).filter (fun x => top x = s)).card)
    (htt : ∀ x < n, top (top x) = top x) {t : ℕ} (ht : t ≤ n) : offSum top cnt t ≤ n := by
  rw [offSum_eq_card hcard htt t ht]
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The blocks of two tops `t < t'` do not overlap. -/
lemma offSum_add_le {top cnt : ℕ → ℕ} {t t' : ℕ} (htt : top t = t) (h : t < t') :
    offSum top cnt t + cnt t ≤ offSum top cnt t' := by
  have := offSum_mono top cnt (show t + 1 ≤ t' by omega)
  rw [offSum_succ, ite_eq_left htt] at this
  exact this

section tree

variable {top cnt : ℕ → ℕ}

/-- The output of `heavy_bridge`. -/
def TopsSpec (T₀ : MGraph) (vList : List ℕ) (r : ℕ) (top : ℕ → ℕ) : Prop :=
  ∀ x < vList.length, top x < vList.length ∧
    vList.getD (top x) 0 = chainTop T₀ (vList.getD r 0)
      (chainOf T₀ (vList.getD r 0) (vList.getD x 0))

/-- The top of a top is itself. -/
lemma top_top (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (hB : TopsSpec T₀ vList r top)
    {x : ℕ} (hx : x < vList.length) : top (top x) = top x := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have hCx := chainOf_mem_heavyChains (r := g r) (hI.getD_mem hx)
  have hb := (hB x hx).2
  have htP : g (top x) ∈ chainOf T₀ (g r) (g x) := by
    change g (top x) = _ at hb
    rw [hb]; exact (chainTop_spec hI.hT hCx).1
  have hEq : chainOf T₀ (g r) (g (top x)) = chainOf T₀ (g r) (g x) := chainOf_eq_of_mem hCx htP
  have hb2 := (hB (top x) (hB x hx).1).2
  change g (top (top x)) = chainTop T₀ (g r) (chainOf T₀ (g r) (g (top x))) at hb2
  rw [hEq] at hb2
  change g (top x) = _ at hb
  rw [← hb] at hb2
  exact getD_inj hI.hnd (hB _ (hB x hx).1).1 (hB x hx).1 hb2

/-- The depth below the top is less than the size of the chain. -/
lemma pos_lt (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (hB : TopsSpec T₀ vList r top)
    (hC : ∀ t < vList.length, top t = t →
      cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card)
    {x : ℕ} (hx : x < vList.length) :
    dep (top x) ≤ dep x ∧ dep x - dep (top x) < cnt (top x) := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have hCx := chainOf_mem_heavyChains (r := g r) (hI.getD_mem hx)
  have htn := (hB x hx).1
  have hb : g (top x) = chainTop T₀ (g r) (chainOf T₀ (g r) (g x)) := (hB x hx).2
  have htP : g (top x) ∈ chainOf T₀ (g r) (g x) := by
    rw [hb]; exact (chainTop_spec hI.hT hCx).1
  have hEq : chainOf T₀ (g r) (g (top x)) = chainOf T₀ (g r) (g x) := chainOf_eq_of_mem hCx htP
  have hct : cnt (top x) = (chainOf T₀ (g r) (g x)).card := by
    rw [hC _ htn (top_top hI hB hx)]; exact congrArg Finset.card hEq
  obtain ⟨h1, h2⟩ := chain_depth_lt hI.hT hCx (mem_chainOf_self (hI.getD_mem hx))
  rw [← hb, hI.depth_eq hx, hI.depth_eq htn] at h1 h2
  rw [hct]
  exact ⟨h1, h2⟩

lemma thSlot_lt (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (hB : TopsSpec T₀ vList r top)
    (hC : ∀ t < vList.length, top t = t →
      cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card)
    (hcard : ∀ s < vList.length,
      cnt s = ((Finset.range vList.length).filter (fun x => top x = s)).card)
    {x : ℕ} (hx : x < vList.length) :
    thSlot (offSum top cnt) top dep x < vList.length := by
  have htn := (hB x hx).1
  have h1 := (pos_lt hI hB hC hx).2
  have h2 := offSum_le hcard (fun y hy => top_top hI hB hy) (show top x + 1 ≤ vList.length by omega)
  rw [offSum_succ, ite_eq_left (top_top hI hB hx)] at h2
  unfold thSlot
  omega

lemma thSlot_inj (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (hB : TopsSpec T₀ vList r top)
    (hC : ∀ t < vList.length, top t = t →
      cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card)
    {x y : ℕ} (hx : x < vList.length) (hy : y < vList.length)
    (h : thSlot (offSum top cnt) top dep x = thSlot (offSum top cnt) top dep y) : x = y := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  obtain ⟨hx1, hx2⟩ := pos_lt hI hB hC hx
  obtain ⟨hy1, hy2⟩ := pos_lt hI hB hC hy
  unfold thSlot at h
  rcases Nat.lt_trichotomy (top x) (top y) with hlt | heq | hgt
  · have := offSum_add_le (cnt := cnt) (top_top hI hB hx) hlt
    omega
  · have hd : dep x = dep y := by rw [heq] at h hx1 hx2; omega
    -- same top, so same chain, and same depth
    have hCx := chainOf_mem_heavyChains (r := g r) (hI.getD_mem hx)
    have hbx : g (top x) = chainTop T₀ (g r) (chainOf T₀ (g r) (g x)) := (hB x hx).2
    have hby : g (top y) = chainTop T₀ (g r) (chainOf T₀ (g r) (g y)) := (hB y hy).2
    have hyC : g y ∈ chainOf T₀ (g r) (g x) := by
      have hCy := chainOf_mem_heavyChains (r := g r) (hI.getD_mem hy)
      have htP : g (top y) ∈ chainOf T₀ (g r) (g y) := by
        rw [hby]; exact (chainTop_spec hI.hT hCy).1
      have htP' : g (top y) ∈ chainOf T₀ (g r) (g x) := by
        rw [← heq, hbx]; exact (chainTop_spec hI.hT hCx).1
      rw [← chainOf_eq_of_mem hCx htP', chainOf_eq_of_mem hCy htP]
      exact mem_chainOf_self (hI.getD_mem hy)
    refine getD_inj hI.hnd hx hy (chain_eq_of_depth hI.hT hCx
      (mem_chainOf_self (hI.getD_mem hx)) hyC ?_)
    rw [hI.depth_eq hx, hI.depth_eq hy, hd]
  · have := offSum_add_le (cnt := cnt) (top_top hI hB hy) hgt
    omega

/-- The block of a chain holds the chain from the top down. -/
theorem stored_chain (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (hB : TopsSpec T₀ vList r top)
    (hC : ∀ t < vList.length, top t = t →
      cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card)
    {arr : ℕ → ℕ} (harr : ∀ x < vList.length, arr (thSlot (offSum top cnt) top dep x) = x)
    {x : ℕ} (hx : x < vList.length) :
    ∀ k < (chainOf T₀ (vList.getD r 0) (vList.getD x 0)).card,
      vList.getD (arr (offSum top cnt (top x) + k)) 0 ∈
          chainOf T₀ (vList.getD r 0) (vList.getD x 0) ∧
        depth T₀ (vList.getD r 0) (vList.getD (arr (offSum top cnt (top x) + k)) 0) =
          depth T₀ (vList.getD r 0)
            (chainTop T₀ (vList.getD r 0) (chainOf T₀ (vList.getD r 0) (vList.getD x 0))) + k := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  set P := chainOf T₀ (g r) (g x) with hP
  have hPm : P ∈ heavyChains T₀ (g r) := chainOf_mem_heavyChains (hI.getD_mem hx)
  have htn := (hB x hx).1
  have hbx : g (top x) = chainTop T₀ (g r) P := (hB x hx).2
  intro k hk
  have hkL : k < (chainList T₀ (g r) P).length := by rw [chainList_length hI.hT hPm]; exact hk
  set u := (chainList T₀ (g r) P)[k] with hu
  have huP : u ∈ P := (mem_chainList_iff hI.hT hPm).mp (List.getElem_mem hkL)
  have hud : depth T₀ (g r) u = depth T₀ (g r) (chainTop T₀ (g r) P) + k :=
    (depth_chainList_getElem hI.hT hPm).2 k hkL
  have huV := (heavyChain_subset hPm).2 huP
  have hul := (hI.hV u).mp huV
  set y := vList.idxOf u with hy
  have hyn : y < vList.length := List.idxOf_lt_length_of_mem hul
  have hgy : g y = u := getD_idxOf hul
  -- `y` has top `top x`
  have htt := top_top hI hB hx
  have hytop : top y = top x := by
    refine (heavy_top_iff hI.hT hI.hnd hI.hV hB htn htt hyn).mpr ?_
    change g y ∈ chainOf T₀ (g r) (g (top x))
    have htP : g (top x) ∈ P := by rw [hbx]; exact (chainTop_spec hI.hT hPm).1
    rw [chainOf_eq_of_mem hPm htP, hgy]; exact huP
  have hslot : thSlot (offSum top cnt) top dep y = offSum top cnt (top x) + k := by
    unfold thSlot
    rw [hytop, ← hI.depth_eq hyn, ← hI.depth_eq htn]
    change offSum top cnt (top x) + (depth T₀ (g r) (g y) - depth T₀ (g r) (g (top x))) = _
    rw [hgy, hbx, hud]; omega
  rw [← hslot, harr y hyn]
  change g y ∈ P ∧ depth T₀ (g r) (g y) = _
  rw [hgy]
  exact ⟨huP, hud⟩

end tree

end MinCostFlow.LSF.Program

end
