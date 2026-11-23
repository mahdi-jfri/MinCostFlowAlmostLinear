module

public import MinCostFlow.LinkCut.ForestModel
import Mathlib.Tactic

/-!
# Potential and Invariant Lemmas for Link-Cut Tree Splices

This file develops the structural and amortized potential machinery for `LctState` and
`LctInvWith`:

- Reachability (`reaches`), component-size partitioning (`repSize`), and the fundamental
  virtual-size theorem `t.treeSize vSize = repSize (listHead0 (treeIds t))`
- Invariance and exact/logarithmic bounds on `sumTreePhi` and `heavyCount` under:
  1. Single-tree replacement (`splay` and `applyTagNode`)
  2. `detachRight` and `attachRight`, and their combined `expose` step (heavy-light charging)
  3. `reroot` path reversal (`revNode_preserves_LctInvWith`, `heavyCount_revNode_le`)
  4. `cut` splice (`detachRootChildren` + free-list push)
  5. `link` splice (`makeSingleton` + `setPpar`)
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### List partitioning and reachability under an acyclic parent map -/

section Reachability

variable {par : ℕ → ℕ} {active : List ℕ} {depth : ℕ → ℕ}

theorem reaches_self (par : ℕ → ℕ) (k u : ℕ) : reaches par k u u = true := by
  cases k <;> simp [reaches]

theorem reaches_succ_of_ne {k u x : ℕ} (hne : x ≠ u) (hp : par x ≠ 0) :
    reaches par (k + 1) u x = reaches par k u (par x) := by
  simp [reaches, hne, hp]

theorem reaches_of_zero_par {k u x : ℕ} (hne : x ≠ u) (hp : par x = 0) :
    reaches par k u x = false := by
  cases k <;> simp [reaches, hne, hp]

private theorem reaches_depth_le (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k u x, x ∈ active → reaches par k u x = true →
      u ∈ active ∧ (u = x ∨ depth u < depth x) := by
  intro k
  induction k with
  | zero =>
      intro u x hx hr
      simp only [reaches, beq_iff_eq] at hr
      subst hr
      exact ⟨hx, Or.inl rfl⟩
  | succ k ih =>
      intro u x hx hr
      by_cases hxu : x = u
      · subst hxu; exact ⟨hx, Or.inl rfl⟩
      · by_cases hpx : par x = 0
        · simp [reaches, hxu, hpx] at hr
        · simp only [reaches, hxu, hpx, ↓reduceIte, beq_iff_eq] at hr
          rcases ih u (par x) (hmem x hx hpx) hr with ⟨hu, hu_ord⟩
          have hd := hdec x hx hpx
          refine ⟨hu, Or.inr ?_⟩
          rcases hu_ord with rfl | hlt <;> omega

private theorem reaches_nodup_prefix (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k u x, x ∈ active → x ≠ u → par x ≠ 0 → reaches par k u x = true →
      ∃ vis : List ℕ, vis.Nodup ∧ (∀ y ∈ vis, y ∈ active ∧ depth u < depth y ∧ depth y ≤ depth x) ∧
        vis.length ≥ 1 ∧ (k ≤ active.length → True) := by
  -- Helper proving that any successful reach takes fewer than `active.length` steps.
  intro k u x hx _ _ hr
  refine ⟨[x], List.nodup_singleton x, ?_, by simp, fun _ => trivial⟩
  intro y hy
  rw [List.mem_singleton.mp hy]
  rcases reaches_depth_le hmem hdec k u x hx hr with ⟨_, hu_ord⟩
  rcases hu_ord with rfl | hlt
  · contradiction
  · exact ⟨hx, hlt, le_rfl⟩

private theorem nodup_length_le_of_subset' {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a as ih =>
      rcases List.nodup_cons.mp hnd with ⟨ha_n, has_nd⟩
      have ha2 : a ∈ l₂ := hsub a (by simp)
      have hlen_erase : (l₂.erase a).length + 1 = l₂.length :=
        (List.length_erase_of_mem ha2).symm ▸ Nat.sub_add_cancel
          (List.length_pos_of_mem ha2)
      have hsub' : ∀ x ∈ as, x ∈ l₂.erase a := fun x hx =>
        (List.mem_erase_of_ne (by intro h; exact ha_n (h ▸ hx))).mpr (hsub x (by simp [hx]))
      have := ih has_nd hsub'
      simp only [List.length_cons]
      omega

private theorem mem_erase_iff_of_nodup {α : Type*} [DecidableEq α] {l : List α}
    (hnd : l.Nodup) {a x : α} : x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      rcases List.nodup_cons.mp hnd with ⟨hd_n, htl_nd⟩
      by_cases hda : hd = a
      · subst hda
        simp only [List.erase_cons_head, List.mem_cons]
        constructor
        · intro hx; exact ⟨fun h => hd_n (h ▸ hx), Or.inr hx⟩
        · rintro ⟨hxa, rfl | hx⟩ <;> [exact absurd rfl hxa; exact hx]
      · have hne : (hd == a) = false := beq_false_of_ne hda
        simp only [List.erase_cons, hne, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih htl_nd]
        constructor
        · rintro (rfl | ⟨hxa, hx⟩)
          · exact ⟨hda, Or.inl rfl⟩
          · exact ⟨hxa, Or.inr hx⟩
        · rintro ⟨hxa, hhd | hx⟩
          · exact Or.inl hhd
          · exact Or.inr ⟨hxa, hx⟩

private theorem le_sum_map_of_mem {α : Type*} {l : List α} (f : α → ℕ) {a : α} (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons hd tl ih =>
      rcases List.mem_cons.mp ha with rfl | htl
      · simp [List.map_cons, List.sum_cons]
      · simp only [List.map_cons, List.sum_cons]; have := ih htl; omega

private theorem sum_two_mem_le_of_nodup {α : Type*} {l : List α} (hnd : l.Nodup)
    (f : α → ℕ) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    f a + f b ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons hd tl ih =>
      rcases List.nodup_cons.mp hnd with ⟨_, htl_nd⟩
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp ha with rfl | ha' <;>
        rcases List.mem_cons.mp hb with hba | hb'
      · exact absurd hba.symm hne
      · have := le_sum_map_of_mem f hb'; omega
      · rw [hba]; have := le_sum_map_of_mem f ha'; omega
      · have := ih htl_nd ha' hb'; omega

private theorem reaches_chain_nodup (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k u x, x ∈ active → x ≠ u → reaches par k u x = true →
      ∃ vis : List ℕ, vis.Nodup ∧ (∀ y ∈ vis, y ∈ active ∧ depth u < depth y ∧ depth y ≤ depth x) ∧
        1 ≤ vis.length ∧ reaches par (vis.length) u x = true := by
  intro k
  induction k with
  | zero =>
      intro u x _ hxu hr
      simp [reaches, hxu] at hr
  | succ k ih =>
      intro u x hx hxu hr
      by_cases hpx : par x = 0
      · simp [reaches, hxu, hpx] at hr
      · simp only [reaches, hxu, hpx, ↓reduceIte, beq_iff_eq] at hr
        by_cases hpxu : par x = u
        · subst hpxu
          refine ⟨[x], List.nodup_singleton x, ?_, by simp, ?_⟩
          · intro y hy; rw [List.mem_singleton.mp hy]
            exact ⟨hx, hdec x hx hpx, le_rfl⟩
          · simp [reaches, hxu, hpx]
        · rcases ih u (par x) (hmem x hx hpx) hpxu hr with
            ⟨vis, hvis_nd, hvis_sub, hvis_len, hvis_rch⟩
          have hd_px : depth (par x) < depth x := hdec x hx hpx
          have hx_nvis : x ∉ vis := fun hxm => by
            have := (hvis_sub x hxm).2.2
            omega
          refine ⟨x :: vis, List.nodup_cons.mpr ⟨hx_nvis, hvis_nd⟩, ?_, by simp, ?_⟩
          · intro y hy
            rcases List.mem_cons.mp hy with hyx | hy'
            · rw [hyx]
              have hle := reaches_depth_le hmem hdec k u (par x) (hmem x hx hpx) hr
              have hlt : depth u < depth (par x) := by
                rcases hle.2 with h | h
                · exact absurd h.symm hpxu
                · exact h
              exact ⟨hx, by omega, le_rfl⟩
            · have hy_info := hvis_sub y hy'
              exact ⟨hy_info.1, hy_info.2.1, by omega⟩
          · simp only [List.length_cons, reaches, hxu, hpx, ↓reduceIte, beq_iff_eq]
            exact hvis_rch

theorem reaches_mono {par : ℕ → ℕ} :
    ∀ {k₁ k₂ u x}, k₁ ≤ k₂ → reaches par k₁ u x = true → reaches par k₂ u x = true := by
  intro k₁
  induction k₁ with
  | zero =>
      intro k₂ u x _ hr
      simp only [reaches, beq_iff_eq] at hr
      rw [hr]; exact reaches_self par k₂ u
  | succ k₁ ih =>
      intro k₂ u x hk hr
      cases k₂ with
      | zero => omega
      | succ k₂ =>
          by_cases hxu : x = u
          · rw [hxu]; exact reaches_self par _ u
          · by_cases hpx : par x = 0
            · simp [reaches, hxu, hpx] at hr
            · simp only [reaches, hxu, hpx, ↓reduceIte, beq_iff_eq] at hr ⊢
              exact ih (by omega) hr

theorem reaches_stable (_hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x)
    {k u x : ℕ} (hx : x ∈ active) (hk : active.length ≤ k) :
    reaches par k u x = reaches par active.length u x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hr
    by_cases hxu : x = u
    · rw [hxu]; exact reaches_self par _ u
    · rcases reaches_chain_nodup hmem hdec k u x hx hxu hr with
        ⟨vis, hvis_nd, hvis_sub, _, hvis_rch⟩
      have hlen : vis.length ≤ active.length :=
        nodup_length_le_of_subset' hvis_nd (fun y hy => (hvis_sub y hy).1)
      exact reaches_mono hlen hvis_rch
  · intro hr
    exact reaches_mono hk hr

theorem reaches_step_iff (hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x)
    {u x : ℕ} (hx : x ∈ active) :
    reaches par active.length u x = true ↔
      x = u ∨ (par x ≠ 0 ∧ reaches par active.length u (par x) = true) := by
  by_cases hxu : x = u
  · subst hxu; simp [reaches_self]
  · by_cases hpx : par x = 0
    · simp [reaches_of_zero_par hxu hpx, hxu, hpx]
    · have hst := reaches_stable hnd hmem hdec (u := u) hx (Nat.le_succ active.length)
      rw [← hst]
      simp [reaches_succ_of_ne hxu hpx, hxu, hpx]

theorem reaches_trans (hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x)
    {k u y x : ℕ} (hyx : reaches par k y x = true) (huy : reaches par active.length u y = true)
    (hx : x ∈ active) :
    reaches par active.length u x = true := by
  suffices h : ∀ m z, z ∈ active → reaches par m y z = true →
      reaches par active.length u z = true from h k x hx hyx
  intro m
  induction m with
  | zero =>
      intro z hz hr
      simp only [reaches, beq_iff_eq] at hr
      subst hr; exact huy
  | succ m ih =>
      intro z hz hr
      by_cases hzy : z = y
      · subst hzy; exact huy
      · by_cases hpz : par z = 0
        · simp [reaches, hzy, hpz] at hr
        · simp only [reaches, hzy, hpz, ↓reduceIte, beq_iff_eq] at hr
          have hp_rch := ih (par z) (hmem z hz hpz) hr
          exact (reaches_step_iff hnd hmem hdec hz).mpr (Or.inr ⟨hpz, hp_rch⟩)

private theorem reaches_child_exists (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k u x, x ∈ active → x ≠ u → reaches par k u x = true →
      ∃ c ∈ active, par c = u ∧ reaches par k c x = true := by
  intro k
  induction k with
  | zero =>
      intro u x _ hxu hr
      simp [reaches, hxu] at hr
  | succ k ih =>
      intro u x hx hxu hr
      by_cases hpx : par x = 0
      · simp [reaches, hxu, hpx] at hr
      · by_cases hpxu : par x = u
        · refine ⟨x, hx, hpxu, reaches_self par _ x⟩
        · simp only [reaches, hxu, hpx, ↓reduceIte, beq_iff_eq] at hr
          rcases ih u (par x) (hmem x hx hpx) hpxu hr with ⟨c, hc_act, hc_par, hc_rch⟩
          refine ⟨c, hc_act, hc_par, ?_⟩
          have hxc : x ≠ c := by
            rcases reaches_depth_le hmem hdec k c (par x) (hmem x hx hpx) hc_rch with ⟨_, hc_ord⟩
            have hd := hdec x hx hpx
            intro rfl
            rcases hc_ord with h1 | h1
            · rw [← h1] at hd; omega
            · omega
          rw [reaches_succ_of_ne hxc hpx]
          exact hc_rch

private theorem reaches_child_unique (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) {u : ℕ} (hu_nz : u ≠ 0) :
    ∀ k x c₁ c₂, x ∈ active →
      par c₁ = u → par c₂ = u →
      reaches par k c₁ x = true → reaches par k c₂ x = true → c₁ = c₂ := by
  intro k
  induction k with
  | zero =>
      intro x c₁ c₂ _ _ _ h1 h2
      simp only [reaches, beq_iff_eq] at h1 h2
      omega
  | succ k ih =>
      intro x c₁ c₂ hx h1p h2p h1 h2
      by_cases hx1 : x = c₁
      · subst hx1
        by_cases hx2 : x = c₂
        · exact hx2
        · have hnz : par x ≠ 0 := fun h0 => by simp [reaches, hx2, h0] at h2
          simp only [reaches, hx2, hnz, ↓reduceIte, beq_iff_eq] at h2
          rcases reaches_depth_le hmem hdec k c₂ (par x) (hmem x hx hnz) h2 with
            ⟨hc₂_act, hc₂_ord⟩
          have hd1 := hdec x hx hnz
          have hd2 := hdec c₂ hc₂_act (h2p.symm ▸ hu_nz)
          rw [h1p] at hd1 hc₂_ord
          rw [h2p] at hd2
          rcases hc₂_ord with h | h
          · rw [h] at hd2; omega
          · omega
      · by_cases hx2 : x = c₂
        · subst hx2
          have hnz : par x ≠ 0 := fun h0 => by simp [reaches, hx1, h0] at h1
          simp only [reaches, hx1, hnz, ↓reduceIte, beq_iff_eq] at h1
          rcases reaches_depth_le hmem hdec k c₁ (par x) (hmem x hx hnz) h1 with
            ⟨hc₁_act, hc₁_ord⟩
          have hd2 := hdec x hx hnz
          have hd1 := hdec c₁ hc₁_act (h1p.symm ▸ hu_nz)
          rw [h2p] at hd2 hc₁_ord
          rw [h1p] at hd1
          rcases hc₁_ord with h | h
          · rw [h] at hd1; omega
          · omega
        · have hnz : par x ≠ 0 := fun h0 => by simp [reaches, hx1, h0] at h1
          simp only [reaches, hx1, hnz, ↓reduceIte, beq_iff_eq] at h1
          simp only [reaches, hx2, hnz, ↓reduceIte, beq_iff_eq] at h2
          exact ih (par x) c₁ c₂ (hmem x hx hnz) h1p h2p h1 h2

private theorem sum_filter_partition {α β : Type*} [DecidableEq β]
    (l : List α) (B : List β) (f : α → β) (hf : ∀ a ∈ l, f a ∈ B) (hndB : B.Nodup) :
    (B.map (fun b => (l.filter (fun a => decide (f a = b))).length)).sum = l.length := by
  induction B generalizing l with
  | nil =>
      cases l with
      | nil => simp
      | cons a _ => exact absurd (hf a (by simp)) (by simp)
  | cons b bs ih =>
      rcases List.nodup_cons.mp hndB with ⟨hb_nbs, hbs_nd⟩
      simp only [List.map_cons, List.sum_cons]
      have hsub : ∀ a ∈ l.filter (fun a => !(f a == b)), f a ∈ bs := by
        intro a ha
        simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at ha
        rcases List.mem_cons.mp (hf a ha.1) with hfb | hm
        · exact absurd hfb ha.2
        · exact hm
      have ih_res := ih (l.filter (fun a => !(f a == b))) hsub hbs_nd
      have hfilt : ∀ b' ∈ bs,
          ((l.filter (fun a => !(f a == b))).filter (fun a => decide (f a = b'))).length =
            (l.filter (fun a => decide (f a = b'))).length := by
        intro b' hb'
        have hbb' : b' ≠ b := fun h => hb_nbs (h ▸ hb')
        congr 1
        rw [List.filter_filter]
        refine List.filter_congr (fun a _ => ?_)
        by_cases hfa : f a = b' <;> simp [hfa, hbb']
      have hmap : (bs.map (fun b' =>
          ((l.filter (fun a => !(f a == b))).filter (fun a => decide (f a = b'))).length)) =
          bs.map (fun b' => (l.filter (fun a => decide (f a = b'))).length) :=
        List.map_congr_left hfilt
      rw [hmap] at ih_res
      rw [ih_res]
      clear ih ih_res hsub hfilt hmap hbs_nd hb_nbs hf
      induction l with
      | nil => simp
      | cons a as ihl =>
          by_cases hfa : f a = b <;> simp [hfa] <;> omega

theorem repSize_pos_of_mem {u : ℕ} (hu : u ∈ active) : 1 ≤ repSize active par u := by
  dsimp only [repSize]
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hu, reaches_self par _ u⟩)

theorem repSize_le_active (u : ℕ) : repSize active par u ≤ active.length :=
  List.length_filter_le _ _

theorem repSize_eq_one_add_sum_children (hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x)
    {u : ℕ} (hu : u ∈ active) (hu_nz : u ≠ 0) :
    repSize active par u =
      1 + ((active.filter (fun c => par c == u)).map (repSize active par)).sum := by
  classical
  let S := active.filter (fun x => reaches par active.length u x)
  let S' := S.erase u
  have hS_nd : S.Nodup := hnd.filter _
  have huS : u ∈ S := List.mem_filter.mpr ⟨hu, reaches_self par _ u⟩
  have hS_len : S.length = 1 + S'.length := by
    have := List.length_erase_of_mem huS
    have hpos := List.length_pos_of_mem huS
    dsimp only [S']
    omega
  let children := active.filter (fun c => par c == u)
  have hch_nd : children.Nodup := hnd.filter _
  let childOf : ℕ → ℕ := fun x =>
    if hx : x ∈ active ∧ x ≠ u ∧ reaches par active.length u x = true then
      Classical.choose (reaches_child_exists hmem hdec active.length u x hx.1 hx.2.1 hx.2.2)
    else 0
  have hchildOf_spec : ∀ x, x ∈ S' →
      childOf x ∈ children ∧ par (childOf x) = u ∧
      reaches par active.length (childOf x) x = true := by
    intro x hx
    simp only [S', mem_erase_iff_of_nodup hS_nd, S, List.mem_filter] at hx
    rcases hx with ⟨hxu, hx_act, hxu_rch⟩
    have hcond : x ∈ active ∧ x ≠ u ∧ reaches par active.length u x = true :=
      ⟨hx_act, hxu, hxu_rch⟩
    have h_eq : childOf x =
        Classical.choose (reaches_child_exists hmem hdec active.length u x hx_act hxu hxu_rch) := by
      simp [childOf, hcond]
    have hc := Classical.choose_spec
      (reaches_child_exists hmem hdec active.length u x hx_act hxu hxu_rch)
    rw [h_eq]
    exact ⟨List.mem_filter.mpr ⟨hc.1, beq_iff_eq.mpr hc.2.1⟩, hc.2.1, hc.2.2⟩
  have hpart := sum_filter_partition S' children childOf
    (fun x hx => (hchildOf_spec x hx).1) hch_nd
  have hmap_eq : children.map (fun b => (S'.filter (fun a => decide (childOf a = b))).length) =
      children.map (repSize active par) := by
    refine List.map_congr_left (fun c hc => ?_)
    have hc' := List.mem_filter.mp hc
    have hcu : par c = u := beq_iff_eq.mp hc'.2
    have hc_nz : par c ≠ 0 := hcu.symm ▸ hu_nz
    dsimp only [repSize]
    exact List.Perm.length_eq ((List.perm_ext_iff_of_nodup ((hS_nd.erase u).filter _)
      (hnd.filter _)).mpr (fun x => by
        simp only [List.mem_filter, mem_erase_iff_of_nodup hS_nd, S, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hxu, hx_act, hx_rch⟩, hcb⟩
          rw [← hcb]
          refine ⟨hx_act, (hchildOf_spec x ?_).2.2⟩
          simp only [S', mem_erase_iff_of_nodup hS_nd, S, List.mem_filter]
          exact ⟨hxu, hx_act, hx_rch⟩
        · rintro ⟨hx_act, hcx_rch⟩
          have hxu : x ≠ u := by
            intro hxu'
            rw [hxu'] at hx_act hcx_rch
            rcases reaches_depth_le hmem hdec active.length c u hx_act hcx_rch with ⟨_, hord⟩
            have hd := hdec c hc'.1 hc_nz
            rw [hcu] at hd
            rcases hord with rfl | h <;> omega
          have hcu_step : reaches par active.length u c = true :=
            (reaches_step_iff hnd hmem hdec hc'.1).mpr
              (Or.inr ⟨hc_nz, by rw [hcu]; exact reaches_self _ _ _⟩)
          have hux_rch : reaches par active.length u x = true :=
            reaches_trans hnd hmem hdec hcx_rch hcu_step hx_act
          have hx_S' : x ∈ S' := by
            simp only [S', mem_erase_iff_of_nodup hS_nd, S, List.mem_filter]
            exact ⟨hxu, hx_act, hux_rch⟩
          have hcs := hchildOf_spec x hx_S'
          refine ⟨⟨hxu, hx_act, hux_rch⟩, ?_⟩
          exact reaches_child_unique hmem hdec hu_nz active.length x (childOf x) c hx_act
            hcs.2.1 hcu hcs.2.2 hcx_rch))
  rw [hmap_eq] at hpart
  dsimp only [repSize]
  change S.length = _
  rw [hS_len, hpart]

/-- Two distinct children of `u` satisfy `1 + repSize c₁ + repSize c₂ ≤ repSize u`. -/
theorem repSize_ge_one_add_two_children (hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x)
    {u c₁ c₂ : ℕ} (hu : u ∈ active) (hu_nz : u ≠ 0)
    (hc₁ : c₁ ∈ active) (hc₂ : c₂ ∈ active)
    (hp₁ : par c₁ = u) (hp₂ : par c₂ = u) (hne : c₁ ≠ c₂) :
    1 + repSize active par c₁ + repSize active par c₂ ≤ repSize active par u := by
  have heq := repSize_eq_one_add_sum_children hnd hmem hdec hu hu_nz
  have hc₁_mem : c₁ ∈ active.filter (fun c => par c == u) :=
    List.mem_filter.mpr ⟨hc₁, beq_iff_eq.mpr hp₁⟩
  have hc₂_mem : c₂ ∈ active.filter (fun c => par c == u) :=
    List.mem_filter.mpr ⟨hc₂, beq_iff_eq.mpr hp₂⟩
  have hsum := sum_two_mem_le_of_nodup (hnd.filter _) (repSize active par) hc₁_mem hc₂_mem hne
  rw [heq]
  omega

end Reachability

/-! ### `treeSize vSize = repSize (head! treeIds)` under `LctInvWith` -/

section TreeSizeVSize

private theorem active_nonZero {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList) : x ≠ 0 := by
  have hn := W.activeValid x hx
  simp only [isNode] at hn
  omega

private theorem tree_nonZero {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees) :
    0 ∉ treeIds P st.splay t := by
  intro h0
  exact active_nonZero W (List.mem_flatMap.mpr ⟨t, ht, (mem_treeIds_iff P st.splay t 0).mp h0⟩) rfl

private theorem listHead0_mem {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees) :
    listHead0 (treeIds P st.splay t) ∈ t.toList ∧
      listHead0 (treeIds P st.splay t) ∈ treeIds P st.splay t := by
  have hne := treeIds_ne_nil (P := P) (s := st.splay) (W.treesNonEmpty t ht)
  cases hids : treeIds P st.splay t with
  | nil => exact absurd hids hne
  | cons a rest =>
      have hm : a ∈ treeIds P st.splay t := by simp [hids]
      exact ⟨(mem_treeIds_iff P st.splay t a).mp hm, by simp [listHead0]⟩

private theorem depth_head_le_of_chain {par depth : ℕ → ℕ} {active : List ℕ}
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x)
    {xs : List ℕ} {prev : ℕ} (hnd : xs.Nodup) (hz : 0 ∉ xs)
    (hact : ∀ z ∈ xs, z ∈ active)
    (hpar : ∀ z ∈ xs.tail, par z = chainPred prev xs z) :
    ∀ {a z}, xs.head? = some a → z ∈ xs → depth a ≤ depth z := by
  induction xs generalizing prev with
  | nil => intro a z h _; simp at h
  | cons hd tl ih =>
      intro a z hhead hz_mem
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rcases List.mem_cons.mp hz_mem with rfl | hz_tl
      · exact le_rfl
      · cases tl with
        | nil => simp at hz_tl
        | cons b bs =>
            rcases List.nodup_cons.mp hnd with ⟨hd_ntl, htl_nd⟩
            have hbd : b ≠ hd := fun h => hd_ntl (h ▸ by simp)
            have hb_par : par b = hd := by
              have := hpar b (by simp)
              simpa [chainPred, hbd] using this
            have hb_act : b ∈ active := hact b (by simp)
            have hd_nz : hd ≠ 0 := fun h => hz (by simp [h])
            have hlt_ab : depth hd < depth b := by
              rw [← hb_par]
              exact hdec b hb_act (hb_par.symm ▸ hd_nz)
            have htl_par : ∀ w ∈ (b :: bs).tail, par w = chainPred hd (b :: bs) w := by
              intro w hw
              have hw_tl : w ∈ bs := by simpa using hw
              have hw_par := hpar w (by simp [hw_tl])
              have hwd : w ≠ hd := fun h => hd_ntl (by simp [h ▸ hw_tl])
              simpa [chainPred, hwd] using hw_par
            have ih_res := ih (prev := hd) htl_nd (fun h => hz (by simp [h]))
              (fun w hw => hact w (by simp [hw])) htl_par rfl hz_tl
            omega

private theorem depth_listHead0_le_of_mem {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees)
    {z : ℕ} (hz : z ∈ t.toList) :
    depth (listHead0 (treeIds P st.splay t)) ≤ depth z := by
  have hne := treeIds_ne_nil (P := P) (s := st.splay) (W.treesNonEmpty t ht)
  cases hids : treeIds P st.splay t with
  | nil => exact absurd hids hne
  | cons a rest =>
      dsimp only [listHead0]
      have hz_ids : z ∈ a :: rest := by rw [← hids]; exact (mem_treeIds_iff P st.splay t z).mpr hz
      have hnd := treeIds_nodup (W.treesInv t ht)
      rw [hids] at hnd
      have hnz := tree_nonZero W ht
      rw [hids] at hnz
      have hact : ∀ w ∈ a :: rest, w ∈ trees.flatMap AuxTree.toList := fun w hw =>
        List.mem_flatMap.mpr ⟨t, ht, (mem_treeIds_iff P st.splay t w).mp (by simp [hids, hw])⟩
      have hpar : ∀ w ∈ (a :: rest).tail,
          inducedSubPar P st.splay trees w = chainPred (st.splay.nodes t.rootId).ppar (a :: rest) w := by
        intro w hw
        have hw_t : w ∈ t.toList :=
          (mem_treeIds_iff P st.splay t w).mp (by rw [hids]; exact List.mem_cons_of_mem _ hw)
        rw [inducedSubPar_eq_of_mem W.activeNodup ht hw_t, hids]
      exact depth_head_le_of_chain W.acyclic hnd hnz hact hpar rfl hz_ids

private theorem ppar_child_iff_eq_head {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t₀ : AuxTree} (ht₀ : t₀ ∈ trees)
    {y : ℕ} (hy : y ∈ t₀.toList) :
    ∀ c ∈ trees.flatMap AuxTree.toList,
      (inducedSubPar P st.splay trees c = y ∧ c ∉ t₀.toList) ↔
      ∃ t' ∈ trees, (st.splay.nodes t'.rootId).ppar = y ∧
        listHead0 (treeIds P st.splay t') = c := by
  intro c hc
  obtain ⟨tc, htc_in, hct⟩ := List.mem_flatMap.mp hc
  have hsub_c := inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup htc_in hct
  constructor
  · rintro ⟨hpar_y, hc_nt₀⟩
    have hntc : tc ≠ t₀ := fun h => hc_nt₀ (h ▸ hct)
    have hc_head : c = listHead0 (treeIds P st.splay tc) := by
      have hp : chainPred (st.splay.nodes tc.rootId).ppar (treeIds P st.splay tc) c = y :=
        hsub_c ▸ hpar_y
      have hc_ids := (mem_treeIds_iff P st.splay tc c).mpr hct
      cases hids : treeIds P st.splay tc with
      | nil => exact absurd hids (treeIds_ne_nil (W.treesNonEmpty tc htc_in))
      | cons a rest =>
          simp only [hids] at hc_ids hp
          rcases List.mem_cons.mp hc_ids with rfl | hrest
          · rfl
          · exfalso
            have hc_ne_a : c ≠ a := fun hca => by
              have := treeIds_nodup (W.treesInv tc htc_in)
              rw [hids] at this
              exact (List.nodup_cons.mp this).1 (hca ▸ hrest)
            simp only [chainPred, hc_ne_a, ↓reduceIte] at hp
            rcases chainPred_mem_or_prev hrest with h | h <;> rw [hp] at h
            · have hy_tc := (mem_treeIds_iff P st.splay tc y).mp (by simp [hids, h])
              exact hntc (flatMap_mem_unique W.activeNodup htc_in ht₀ hy_tc hy)
            · have hy_tc := (mem_treeIds_iff P st.splay tc y).mp (by simp [hids, h])
              exact hntc (flatMap_mem_unique W.activeNodup htc_in ht₀ hy_tc hy)
    refine ⟨tc, htc_in, ?_, hc_head.symm⟩
    cases hids : treeIds P st.splay tc with
    | nil => exact absurd hids (treeIds_ne_nil (W.treesNonEmpty tc htc_in))
    | cons a rest =>
        rw [hids, listHead0] at hc_head
        rw [← hpar_y, hsub_c, hids, hc_head, chainPred_head]
  · rintro ⟨t', ht'_in, hpp_y, hc_eq⟩
    have hm_t' := (listHead0_mem W ht'_in).1
    rw [hc_eq] at hm_t'
    have hteq : t' = tc := flatMap_mem_unique W.activeNodup ht'_in htc_in hm_t' hct
    subst hteq
    refine ⟨?_, fun hc_t₀ => ?_⟩
    · rw [hsub_c]
      cases hids : treeIds P st.splay t' with
      | nil => exact absurd hids (treeIds_ne_nil (W.treesNonEmpty t' ht'_in))
      | cons a rest =>
          rw [hids, listHead0] at hc_eq
          rw [← hc_eq, chainPred_head]
          exact hpp_y
    · have hsame : t' = t₀ := flatMap_mem_unique W.activeNodup ht'_in ht₀ hm_t' hc_t₀
      subst hsame
      have hy_nz : y ≠ 0 := active_nonZero W (List.mem_flatMap.mpr ⟨t', ht'_in, hy⟩)
      have hc_par : inducedSubPar P st.splay trees c = y := by
        rw [inducedSubPar_eq_of_mem W.activeNodup ht'_in hm_t']
        cases hids : treeIds P st.splay t' with
        | nil => exact absurd hids (treeIds_ne_nil (W.treesNonEmpty t' ht'_in))
        | cons a rest => rw [hids, listHead0] at hc_eq; rw [← hc_eq, chainPred_head, hpp_y]
      have hdec1 := W.acyclic c hc (hc_par.symm ▸ hy_nz)
      rw [hc_par] at hdec1
      have hle1 := depth_listHead0_le_of_mem W ht'_in hy
      rw [hc_eq] at hle1
      omega

private theorem chainPred_eq_head_iff {y a : ℕ} {rest : List ℕ} {c : ℕ}
    (hnd : (y :: a :: rest).Nodup) (hc : c ∈ a :: rest) :
    chainPred y (a :: rest) c = y ↔ c = a := by
  by_cases hca : c = a
  · subst hca; simp [chainPred]
  · simp only [chainPred, hca, ↓reduceIte]
    have hc_rest : c ∈ rest := by simpa [hca] using hc
    rcases List.nodup_cons.mp hnd with ⟨hy_n, _⟩
    constructor
    · intro h
      rcases chainPred_mem_or_prev (prev := a) hc_rest with h1 | h1
      · rw [h1] at h; exact absurd h.symm (fun h' => hy_n (by simp [h'.symm]))
      · rw [h] at h1; exact absurd h1 (fun h' => hy_n (by simp [h']))
    · intro h; exact False.elim h

private theorem tree_ppar_ne_mem {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t₀ : AuxTree} (ht₀ : t₀ ∈ trees)
    {z : ℕ} (hz : z ∈ t₀.toList) : (st.splay.nodes t₀.rootId).ppar ≠ z := by
  intro heq
  have hhd := listHead0_mem W ht₀
  have hnz : z ≠ 0 := active_nonZero W (List.mem_flatMap.mpr ⟨t₀, ht₀, hz⟩)
  have hpar_hd : inducedSubPar P st.splay trees (listHead0 (treeIds P st.splay t₀)) = z := by
    rw [inducedSubPar_eq_of_mem W.activeNodup ht₀ hhd.1]
    cases hids : treeIds P st.splay t₀ with
    | nil => exact absurd hids (treeIds_ne_nil (W.treesNonEmpty t₀ ht₀))
    | cons a rest => simp [listHead0, chainPred_head, heq]
  have hlt := W.acyclic _ (List.mem_flatMap.mpr ⟨t₀, ht₀, hhd.1⟩) (hpar_hd.symm ▸ hnz)
  rw [hpar_hd] at hlt
  have hle := depth_listHead0_le_of_mem W ht₀ hz
  omega

private theorem map_listHead0_nodup {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts : List AuxTree} (hne : ∀ t ∈ ts, t ≠ .leaf) (hnd : (ts.flatMap AuxTree.toList).Nodup) :
    (ts.map (fun t => listHead0 (treeIds P s t))).Nodup := by
  induction ts with
  | nil => simp
  | cons t rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hnd
      rcases hnd with ⟨_, hrest_nd, hdisj⟩
      simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, ih (fun a ha => hne a (by simp [ha])) hrest_nd⟩
      rintro ⟨a, ha, ha_eq⟩
      have hhd_t : listHead0 (treeIds P s t) ∈ t.toList := by
        cases hids : treeIds P s t with
        | nil => exact absurd hids (treeIds_ne_nil (hne t (by simp)))
        | cons x _ =>
            rw [listHead0]
            exact (mem_treeIds_iff P s t x).mp (by simp [hids])
      have hhd_a : listHead0 (treeIds P s a) ∈ a.toList := by
        cases hids : treeIds P s a with
        | nil => exact absurd hids (treeIds_ne_nil (hne a (by simp [ha])))
        | cons x _ =>
            rw [listHead0]
            exact (mem_treeIds_iff P s a x).mp (by simp [hids])
      rw [ha_eq] at hhd_a
      exact hdisj _ hhd_t _ (List.mem_flatMap.mpr ⟨a, ha, hhd_a⟩) rfl

private theorem list_filter_flatMap_nodup {α : Type*} {p : α → Bool} {f : α → List ℕ}
    {l : List α} (hnd : (l.flatMap f).Nodup) :
    ((l.filter p).flatMap f).Nodup := by
  have hsub : List.Sublist ((l.filter p).flatMap f) (l.flatMap f) := by
    clear hnd
    induction l with
    | nil => simp
    | cons a rest ih =>
        by_cases hp : p a = true
        · simp only [List.filter_cons, hp, ↓reduceIte, List.flatMap_cons]
          exact List.Sublist.append (List.Sublist.refl _) ih
        · have hpf : p a = false := Bool.eq_false_iff.mpr hp
          simp only [List.filter_cons, hpf, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons]
          exact List.Sublist.append (List.nil_sublist (f a)) ih
  exact hnd.sublist hsub

private theorem dashedHeads_nodup {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) (y : ℕ) :
    ((trees.filter (fun t => (st.splay.nodes t.rootId).ppar == y)).map
      (fun t => listHead0 (treeIds P st.splay t))).Nodup :=
  map_listHead0_nodup (fun _ ht => W.treesNonEmpty _ (List.mem_filter.mp ht).1)
    (list_filter_flatMap_nodup W.activeNodup)

/-- Sum of `vSize` over a suffix `ys` of `treeIds t₀` equals `repSize (listHead0 ys)` (or `0` on `[]`). -/
private theorem sum_vSize_suffix_eq_repSize {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t₀ : AuxTree} (ht₀ : t₀ ∈ trees) :
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    ∀ (ys : List ℕ), ys <:+ treeIds P st.splay t₀ →
      (ys.map (fun y => 1 + v y)).sum = if ys = [] then 0 else repSize active par (listHead0 ys) := by
  intro active par v ys hsuf
  induction ys with
  | nil => simp
  | cons y rest ih =>
      have hsuf_rest : rest <:+ treeIds P st.splay t₀ := List.IsSuffix.trans ⟨[y], rfl⟩ hsuf
      have ih_rest := ih hsuf_rest
      have hy_ids : y ∈ treeIds P st.splay t₀ := hsuf.subset (by simp)
      have hy_t₀ : y ∈ t₀.toList := (mem_treeIds_iff P st.splay t₀ y).mp hy_ids
      have hy_act : y ∈ active := List.mem_flatMap.mpr ⟨t₀, ht₀, hy_t₀⟩
      have hy_nz : y ≠ 0 := active_nonZero W hy_act
      have hrep_y := repSize_eq_one_add_sum_children W.activeNodup
        (fun z hz hp => W.subPar_mem_active hz hp) W.acyclic hy_act hy_nz
      rcases hsuf with ⟨pre, hpre_eq⟩
      have hnd_ids := treeIds_nodup (W.treesInv t₀ ht₀)
      rw [← hpre_eq] at hnd_ids
      let children := active.filter (fun c => par c == y)
      let dashedTrees := trees.filter (fun t => (st.splay.nodes t.rootId).ppar == y)
      let dashedHeads := dashedTrees.map (fun t => listHead0 (treeIds P st.splay t))
      have hdh_nd : dashedHeads.Nodup := dashedHeads_nodup W y
      have hdh_nt₀ : ∀ c ∈ dashedHeads, c ∉ t₀.toList := by
        intro c hc hc_t₀
        rcases List.mem_map.mp hc with ⟨t', ht'_f, rfl⟩
        rcases List.mem_filter.mp ht'_f with ⟨ht'_in, hpp_y⟩
        have hhd_t' := (listHead0_mem W ht'_in).1
        have hsame : t' = t₀ := flatMap_mem_unique W.activeNodup ht'_in ht₀ hhd_t' hc_t₀
        subst hsame
        exact tree_ppar_ne_mem W ht'_in hy_t₀ (beq_iff_eq.mp hpp_y)
      have hrest_t₀ : ∀ c ∈ rest.head?.toList, c ∈ t₀.toList := by
        intro c hc
        cases rest with
        | nil => simp at hc
        | cons a tl =>
            simp only [List.head?_cons, Option.toList_some, List.mem_singleton] at hc
            subst hc
            exact (mem_treeIds_iff P st.splay t₀ _).mp (by rw [← hpre_eq]; simp)
      have htarget_nd : (rest.head?.toList ++ dashedHeads).Nodup := by
        refine List.nodup_append.mpr ⟨?_, hdh_nd, ?_⟩
        · cases rest <;> simp
        · intro a ha b hb h
          subst h
          exact hdh_nt₀ a hb (hrest_t₀ a ha)
      have hperm_ch : children.Perm (rest.head?.toList ++ dashedHeads) := by
        refine (List.perm_ext_iff_of_nodup (W.activeNodup.filter _) htarget_nd).mpr (fun c => ?_)
        simp only [List.mem_filter, beq_iff_eq, List.mem_append]
        constructor
        · rintro ⟨hc_act, hc_par⟩
          by_cases hc_t₀ : c ∈ t₀.toList
          · left
            have hc_ids : c ∈ treeIds P st.splay t₀ := (mem_treeIds_iff P st.splay t₀ c).mpr hc_t₀
            rw [← hpre_eq] at hc_ids
            have hc_ne_y : c ≠ y := by
              intro hcy
              rw [hcy] at hc_par hc_act
              dsimp only [par] at hc_par
              have := W.acyclic y hc_act (hc_par.symm ▸ hy_nz)
              rw [hc_par] at this; omega
            have hc_npre : c ∉ pre := by
              intro hc_pre
              have hcp := inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht₀ hc_t₀
              rw [← hpre_eq, chainPred_mem_append_left hc_pre] at hcp
              have hpar_eq : chainPred (st.splay.nodes t₀.rootId).ppar pre c = y :=
                hcp.symm.trans hc_par
              rcases chainPred_mem_or_prev hc_pre with hpp | hpre_m
              · rw [hpp] at hpar_eq; exact tree_ppar_ne_mem W ht₀ hy_t₀ hpar_eq
              · rw [hpar_eq] at hpre_m
                have hnd_p := hnd_ids
                rw [List.nodup_append] at hnd_p
                exact hnd_p.2.2 y hpre_m y (by simp) rfl
            have hc_rest : c ∈ rest := by
              rcases List.mem_append.mp hc_ids with h1 | h1
              · exact absurd h1 hc_npre
              · rcases List.mem_cons.mp h1 with h2 | h2
                · exact absurd h2 hc_ne_y
                · exact h2
            cases hrc : rest with
            | nil => rw [hrc] at hc_rest; simp at hc_rest
            | cons a tl =>
                have hc_rest' : c ∈ a :: tl := hrc ▸ hc_rest
                have hpre_rw : pre ++ y :: a :: tl = (pre ++ [y]) ++ (a :: tl) := by simp
                have hcp := inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht₀ hc_t₀
                rw [← hpre_eq, hrc, hpre_rw] at hcp
                have hnd' := hnd_ids
                rw [hrc, hpre_rw] at hnd'
                rw [chainPred_mem_append_right (b := y) hnd' hc_rest' (by simp)] at hcp
                have hy_nd : (y :: a :: tl).Nodup := by
                  have := hnd_ids
                  rw [hrc, List.nodup_append] at this
                  exact this.2.1
                have hca := (chainPred_eq_head_iff hy_nd hc_rest').mp (hcp.symm.trans hc_par)
                simp [hca]
          · right
            rcases (ppar_child_iff_eq_head W ht₀ hy_t₀ c hc_act).mp ⟨hc_par, hc_t₀⟩ with
              ⟨t', ht'_in, hpp_y, rfl⟩
            exact List.mem_map.mpr ⟨t', List.mem_filter.mpr ⟨ht'_in, beq_iff_eq.mpr hpp_y⟩, rfl⟩
        · intro h
          rcases h with hrest_m | hdh_m
          · have hc_t₀ := hrest_t₀ c hrest_m
            have hc_act : c ∈ active := List.mem_flatMap.mpr ⟨t₀, ht₀, hc_t₀⟩
            refine ⟨hc_act, ?_⟩
            cases hrc : rest with
            | nil => rw [hrc] at hrest_m; simp at hrest_m
            | cons a tl =>
                rw [hrc] at hrest_m
                simp only [List.head?_cons, Option.toList_some, List.mem_singleton] at hrest_m
                subst hrest_m
                have hpre_rw : pre ++ y :: c :: tl = (pre ++ [y]) ++ (c :: tl) := by simp
                have hcp := inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht₀ hc_t₀
                rw [← hpre_eq, hrc, hpre_rw] at hcp
                have hnd' := hnd_ids
                rw [hrc, hpre_rw] at hnd'
                rw [chainPred_mem_append_right (b := y) hnd' (by simp) (by simp)] at hcp
                simpa [chainPred] using hcp
          · rcases List.mem_map.mp hdh_m with ⟨t', ht'_f, rfl⟩
            rcases List.mem_filter.mp ht'_f with ⟨ht'_in, hpp_y⟩
            have hhd_t' := (listHead0_mem W ht'_in).1
            have hc_act : listHead0 (treeIds P st.splay t') ∈ active :=
              List.mem_flatMap.mpr ⟨t', ht'_in, hhd_t'⟩
            exact ⟨hc_act, ((ppar_child_iff_eq_head W ht₀ hy_t₀ _ hc_act).mpr
              ⟨t', ht'_in, beq_iff_eq.mp hpp_y, rfl⟩).1⟩
      have hsum_ch : (children.map (repSize active par)).sum =
          (rest.head?.toList.map (repSize active par)).sum +
            (dashedHeads.map (repSize active par)).sum := by
        rw [(hperm_ch.map _).sum_eq, List.map_append, List.sum_append]
      have hv_eq : v y = (dashedHeads.map (repSize active par)).sum := by
        simp only [v, vSize, dashedHeads, dashedTrees, List.map_map]
        rfl
      have hrest_sum : (rest.head?.toList.map (repSize active par)).sum =
          (rest.map (fun y => 1 + v y)).sum := by
        rw [ih_rest]
        cases rest with
        | nil => simp
        | cons a tl => simp [listHead0]
      simp only [List.map_cons, List.sum_cons, List.cons_ne_nil, ↓reduceIte, listHead0]
      dsimp only [active, par, v] at hrep_y hsum_ch hv_eq hrest_sum ⊢
      rw [hrep_y, hsum_ch, hrest_sum, hv_eq]
      omega

theorem treeSize_vSize_eq_repSize {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees) :
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    t.treeSize v = repSize active par (listHead0 (treeIds P st.splay t)) := by
  intro active par v
  have heq := sum_vSize_suffix_eq_repSize W ht (treeIds P st.splay t) (List.suffix_refl _)
  have hne := treeIds_ne_nil (P := P) (s := st.splay) (W.treesNonEmpty t ht)
  simp only [hne, ↓reduceIte] at heq
  have hp : (treeIds P st.splay t).Perm t.toList := by
    simp only [treeIds, SplayState.evalPairs_map_fst]
    exact AuxTree.evalInorder_perm _ _ _
  rw [AuxTree.treeSize_eq_sum, ← (hp.map (fun y => 1 + v y)).sum_eq]
  exact heq

/-- If `prev ∈ trees` has `ppar = x` where `x ∈ t.toList` (`prev ≠ t`), then
`prev.treeSize v ≤ (t.findSubtree x).treeSize v`, hence `prev.rank v ≤ (t.findSubtree x).rank v`. -/
theorem findSubtree_rank_ge_of_ppar {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t prev : AuxTree}
    (_ht : t ∈ trees) (hprev : prev ∈ trees)
    {x : ℕ} (hx : x ∈ t.toList)
    (hpp : (st.splay.nodes prev.rootId).ppar = x) :
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    prev.treeSize v ≤ (t.findSubtree x).treeSize v ∧
    prev.rank v ≤ (t.findSubtree x).rank v := by
  intro active par v
  obtain ⟨l', r', hsub_eq⟩ := AuxTree.findSubtree_root_of_mem hx
  have hsz_le : v x ≤ (t.findSubtree x).treeSize v := by
    rw [hsub_eq, AuxTree.treeSize]
    omega
  have hprev_eq := treeSize_vSize_eq_repSize W hprev
  have hprev_in : prev ∈ trees.filter (fun t' => (st.splay.nodes t'.rootId).ppar == x) :=
    List.mem_filter.mpr ⟨hprev, beq_iff_eq.mpr hpp⟩
  have hv_le : repSize active par (listHead0 (treeIds P st.splay prev)) ≤ v x := by
    have hle := le_sum_map_of_mem
      (fun t' => repSize active par (listHead0 (treeIds P st.splay t'))) hprev_in
    dsimp only [v, vSize]
    omega
  have hle : prev.treeSize v ≤ (t.findSubtree x).treeSize v := by
    rw [hprev_eq]; exact le_trans hv_le hsz_le
  exact ⟨hle, Nat.log_mono_right hle⟩

end TreeSizeVSize

end MinCostFlow.LinkCut

