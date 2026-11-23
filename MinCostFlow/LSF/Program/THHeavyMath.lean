module

public import MinCostFlow.LSF.Program.THSizeMath
public import MinCostFlow.LSF.Program.THChainMath

/-!
# Chain tops, top-down

The heavy pass walks the top-down order `Q` from the front. A vertex `x` other than the root is a
heavy child exactly when `sz (par x) < 2 * sz x`, where `sz` holds the subtree sizes. A heavy
child is in the chain of its parent, so it gets the top of its parent; any other vertex is the
top of its own chain. The pass also counts, for each top `t`, the vertices that got `t`.

`HeavyState` is the loop invariant. `heavy_bridge` shows that the stored tops are the chain tops
of `T₀`, and `heavy_count` that the count at a top is the size of its chain.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

variable {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

/-- The rule of the heavy pass at a vertex other than the root. -/
def heavyTop (sz par top : ℕ → ℕ) (x : ℕ) : ℕ :=
  if sz (par x) < 2 * sz x then top (par x) else x

/-- The invariant after the first `j` positions of `Q`. -/
def HeavyState (Q : List ℕ) (par : ℕ → ℕ) (n r : ℕ) (sz top cnt : ℕ → ℕ) (j : ℕ) : Prop :=
  top r = r ∧ (∀ x ∈ Q.take j, top x < n) ∧
  (∀ x ∈ Q.take j, x ≠ r → top x = heavyTop sz par top x) ∧
  ∀ t < n, cnt t = ((Q.take j).filter (fun x => decide (top x = t))).length

lemma TopDownOrder.take_one (hQ : TopDownOrder n r par Q) (hn : 0 < n) : Q.take 1 = [r] := by
  have hlen : 0 < Q.length := by rw [hQ.len]; exact hn
  rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem hlen, hQ.head_eq hn]
  rfl

lemma heavyState_init (hQ : TopDownOrder n r par Q) (hn : 0 < n) (hrn : r < n)
    {sz top cnt : ℕ → ℕ} (htop : top r = r) (hcr : cnt r = 1)
    (hc0 : ∀ t < n, t ≠ r → cnt t = 0) : HeavyState Q par n r sz top cnt 1 := by
  rw [HeavyState, hQ.take_one hn]
  refine ⟨htop, fun x hx => ?_, fun x hx hxr => absurd (List.mem_singleton.mp hx) hxr,
    fun t ht => ?_⟩
  · rw [List.mem_singleton.mp hx, htop]; exact hrn
  · by_cases htr : t = r
    · subst htr; simp [htop, hcr]
    · rw [hc0 t ht htr]
      simp only [List.filter_cons, List.filter_nil, htop]
      simp [Ne.symm htr]

lemma heavyState_congr (hQ : TopDownOrder n r par Q) {sz top cnt top' cnt' : ℕ → ℕ} {j : ℕ}
    (hrn : r < n) (htop : ∀ x < n, top' x = top x) (hcnt : ∀ t < n, cnt' t = cnt t)
    (h : HeavyState Q par n r sz top cnt j) : HeavyState Q par n r sz top' cnt' j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlt : ∀ x ∈ Q.take j, x < n := fun x hx => hQ.lt x (List.mem_of_mem_take hx)
  refine ⟨by rw [htop r hrn, h1], fun x hx => by rw [htop x (hlt x hx)]; exact h2 x hx,
    fun x hx hxr => ?_, fun t ht => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take] at hk
    have h3' := h3 _ hx hxr
    rw [List.getElem_take] at hxr ⊢ h3'
    have hkQ : k < Q.length := by omega
    have hpar := hQ.after k hkQ hxr
    have hpn : par Q[k] < n := hQ.lt _ (List.mem_of_mem_take hpar)
    rw [htop _ (hQ.lt _ (List.getElem_mem hkQ)), h3', heavyTop, heavyTop, htop _ hpn]
  · rw [hcnt t ht, h4 t ht]
    congr 1
    refine List.filter_congr (fun x hx => ?_)
    rw [htop x (hlt x hx)]

theorem heavyState_step (hQ : TopDownOrder n r par Q) {sz top cnt : ℕ → ℕ} {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j < Q.length) (h : HeavyState Q par n r sz top cnt j) :
    HeavyState Q par n r sz (Function.update top Q[j] (heavyTop sz par top Q[j]))
      (Function.update cnt (heavyTop sz par top Q[j])
        (cnt (heavyTop sz par top Q[j]) + 1)) (j + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  set x := Q[j] with hx
  have hn : 0 < n := by rw [← hQ.len]; omega
  have hxr : x ≠ r := by
    intro h
    have h0 := hQ.head_eq hn
    rw [← h0, hx] at h
    have := (hQ.nodup.getElem_inj_iff).mp h
    omega
  have hxt : x ∉ Q.take j := hQ.not_mem_take hj
  have hpx : par x ∈ Q.take j := hQ.after j hj hxr
  have hpx_ne : par x ≠ x := fun h => hxt (h ▸ hpx)
  have htake : Q.take (j + 1) = Q.take j ++ [x] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
  have hxn : x < n := hQ.lt x (List.getElem_mem hj)
  set v := heavyTop sz par top x with hv
  have hvn : v < n := by
    rw [hv, heavyTop]; split_ifs
    · exact h2 _ hpx
    · exact hxn
  -- values on `Q.take j` do not change
  have hsame : ∀ y ∈ Q.take j, Function.update top x v y = top y := fun y hy =>
    Function.update_of_ne (fun h => hxt (by rw [← h]; exact hy)) _ _
  have hrt : r ∈ Q.take j := by
    have : Q.take 1 ⊆ Q.take j := (List.take_prefix_take_left hj1).subset
    exact this (by rw [hQ.take_one hn]; exact List.mem_singleton_self r)
  refine ⟨by rw [hsame r hrt, h1], fun y hy => ?_, fun y hy hyr => ?_, fun t ht => ?_⟩
  · rw [htake, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · rw [hsame y hy]; exact h2 y hy
    · rw [Function.update_self]; exact hvn
  · rw [htake, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · rw [hsame y hy, h3 y hy hyr, heavyTop, heavyTop]
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
      rw [List.length_take] at hk
      rw [List.getElem_take] at hyr ⊢
      rw [hsame _ ((List.take_prefix_take_left (by omega)).subset (hQ.after k (by omega) hyr))]
    · rw [Function.update_self, hv, heavyTop, heavyTop, Function.update_of_ne hpx_ne]
  · rw [htake, List.filter_append, List.length_append, List.filter_cons, List.filter_nil,
      Function.update_self]
    have hfil : (Q.take j).filter (fun y => decide (Function.update top x v y = t)) =
        (Q.take j).filter (fun y => decide (top y = t)) :=
      List.filter_congr (fun y hy => by rw [hsame y hy])
    rw [hfil, ← h4 t ht]
    by_cases hvt : v = t
    · subst hvt; simp
    · rw [Function.update_of_ne (Ne.symm hvt)]; simp [hvt]

/-- The stored tops are the chain tops. -/
theorem heavy_bridge {T₀ : MGraph} {vList : List ℕ} {tM : ℕ}
    {fid tl hd pe dep : ℕ → ℕ} {sz top cnt : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hQ : TopDownOrder vList.length r par Q)
    (hsz : ∀ x < vList.length, sz x = (subtree T₀ (vList.getD r 0) (vList.getD x 0)).card)
    (hH : HeavyState Q par vList.length r sz top cnt vList.length) :
    ∀ x < vList.length, top x < vList.length ∧
      vList.getD (top x) 0 = chainTop T₀ (vList.getD r 0)
        (chainOf T₀ (vList.getD r 0) (vList.getD x 0)) := by
  set n := vList.length with hn_def
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have htakeQ : Q.take n = Q := List.take_of_length_le (by rw [hQ.len])
  obtain ⟨h1, h2, h3, -⟩ := hH
  rw [htakeQ] at h2 h3
  have hgV : ∀ x < n, g x ∈ T₀.V := fun x hx =>
    (hV _).mpr (by simp only [hg]; rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)
  have key : ∀ d, ∀ x < n, dep x = d → top x < n ∧
      g (top x) = chainTop T₀ (g r) (chainOf T₀ (g r) (g x)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx hd
      have hxQ := hQ.cover x hx
      refine ⟨h2 x hxQ, ?_⟩
      by_cases hxr : x = r
      · subst hxr
        rw [h1, chainTop_chainOf_self hT (hgV x hx) (Or.inl rfl)]
      · have hpar : parent T₀ (g r) (g x) = g (par x) :=
          ((t0Rooted_spec hT.isForest hA hnd hR hr hx).2 hxr).1
        have hdp := (hR.step x hx hxr).2.2
        have hpn := hR.par_lt x hx
        have hgxr : g x ≠ g r := fun h => hxr (getD_inj hnd hx hr h)
        have hheavy : IsHeavyChild T₀ (g r) (g x) ↔ sz (par x) < 2 * sz x := by
          rw [IsHeavyChild, hsz _ hpn, hsz x hx]
          rw [hpar]
          exact ⟨fun h => h.2.2, fun h => ⟨hgV x hx, hgxr, h⟩⟩
        rw [h3 x hxQ hxr, heavyTop]
        split_ifs with hh
        · rw [chainOf_heavy hT (hheavy.mpr hh), hpar]
          exact (ih (dep (par x)) (by omega) (par x) hpn rfl).2
        · exact (chainTop_chainOf_self hT (hgV x hx) (Or.inr (fun h => hh (hheavy.mp h)))).symm
  exact fun x hx => key _ x hx rfl

/-- Two vertices with stored tops: the top of `x` is `t` exactly when `x` is in the chain of
`t`, for a vertex `t` that is its own top. -/
theorem heavy_top_iff {T₀ : MGraph} {vList : List ℕ} {top : ℕ → ℕ} {r : ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hB : ∀ x < vList.length, top x < vList.length ∧
      vList.getD (top x) 0 = chainTop T₀ (vList.getD r 0)
        (chainOf T₀ (vList.getD r 0) (vList.getD x 0)))
    {t x : ℕ} (ht : t < vList.length) (htt : top t = t) (hx : x < vList.length) :
    top x = t ↔ vList.getD x 0 ∈ chainOf T₀ (vList.getD r 0) (vList.getD t 0) := by
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have hgV : ∀ x < vList.length, g x ∈ T₀.V := fun x hx =>
    (hV _).mpr (by simp only [hg]; rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)
  have hgt : g t = chainTop T₀ (g r) (chainOf T₀ (g r) (g t)) := by
    have := (hB t ht).2; rw [htt] at this; exact this
  constructor
  · intro hxt
    have hb := (hB x hx).2
    rw [hxt] at hb
    have hCx := chainOf_mem_heavyChains (r := g r) (hgV x hx)
    have hmem : g t ∈ chainOf T₀ (g r) (g x) := by
      change g t = _ at hb
      rw [hb]; exact (chainTop_spec hT hCx).1
    rw [chainOf_eq_of_mem hCx hmem]
    exact mem_chainOf_self (hgV x hx)
  · intro hmem
    have hCt := chainOf_mem_heavyChains (r := g r) (hgV t ht)
    have hEq : chainOf T₀ (g r) (g x) = chainOf T₀ (g r) (g t) := chainOf_eq_of_mem hCt hmem
    have hb := (hB x hx).2
    change g (top x) = _ at hb
    rw [hEq, ← hgt] at hb
    exact getD_inj hnd (hB x hx).1 ht hb

/-- The count at a top is the size of its chain. -/
theorem heavy_count {T₀ : MGraph} {vList : List ℕ} {sz top cnt : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hQ : TopDownOrder vList.length r par Q)
    (hH : HeavyState Q par vList.length r sz top cnt vList.length)
    (hB : ∀ x < vList.length, top x < vList.length ∧
      vList.getD (top x) 0 = chainTop T₀ (vList.getD r 0)
        (chainOf T₀ (vList.getD r 0) (vList.getD x 0)))
    {t : ℕ} (ht : t < vList.length) (htt : top t = t) :
    cnt t = (chainOf T₀ (vList.getD r 0) (vList.getD t 0)).card := by
  classical
  set n := vList.length with hn_def
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have htakeQ : Q.take n = Q := List.take_of_length_le (by rw [hQ.len])
  have h4 := hH.2.2.2 t ht
  rw [htakeQ] at h4
  set l := Q.filter (fun x => decide (top x = t)) with hl
  have hlnd : l.Nodup := hQ.nodup.filter _
  have hlt : ∀ y ∈ l, y < n := fun y hy => hQ.lt y (List.mem_filter.mp hy).1
  have hmap : (l.map g).Nodup :=
    List.Nodup.map_on (fun a ha b hb hab => getD_inj hnd (hlt a ha) (hlt b hb) hab) hlnd
  have hset : chainOf T₀ (g r) (g t) = (l.map g).toFinset := by
    ext v
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · intro hv
      have hgtV : g t ∈ T₀.V :=
        (hV _).mpr (by simp only [hg]; rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _)
      have hvV := (heavyChain_subset (chainOf_mem_heavyChains (r := g r) hgtV)).2 hv
      have hvl := (hV v).mp hvV
      have hin : vList.idxOf v < n := List.idxOf_lt_length_of_mem hvl
      have hgi : g (vList.idxOf v) = v := getD_idxOf hvl
      refine ⟨vList.idxOf v, List.mem_filter.mpr ⟨hQ.cover _ hin, ?_⟩, hgi⟩
      rw [decide_eq_true_iff, heavy_top_iff hT hnd hV hB ht htt hin]
      change g _ ∈ _; rw [hgi]; exact hv
    · rintro ⟨y, hy, rfl⟩
      have hyt := List.mem_filter.mp hy
      rw [decide_eq_true_iff] at hyt
      exact (heavy_top_iff hT hnd hV hB ht htt (hlt y hy)).mp hyt.2
  change cnt t = (chainOf T₀ (g r) (g t)).card
  rw [h4, hset, List.card_toFinset, List.dedup_eq_self.mpr hmap, List.length_map]

end MinCostFlow.LSF.Program

end
