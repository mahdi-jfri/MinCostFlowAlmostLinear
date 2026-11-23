module

public import MinCostFlow.LinkCut.SplayLazy
import Mathlib.Tactic

/-!
# Rotations in the splay model

Helpers on `AuxTree` depths and reparenting, and the facts that `rotate` keeps the splay
invariants.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

namespace SplayState

variable {α σ τ : Type*}

/-! ### Helper lemmas on `AuxTree` depths and reparenting -/

theorem depthOf_lt_countNodes {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    t.depthOf x < t.countNodes := by
  induction t with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      simp only [AuxTree.depthOf, AuxTree.countNodes]
      by_cases heq : x = id
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        by_cases hxl : x ∈ l.toList
        · simp only [hxl, ↓reduceIte]; have := ihl hxl; omega
        · have hxr : x ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h | rfl) | h
            · exact absurd h hxl
            · exact absurd rfl heq
            · exact h
          simp only [hxl, hxr, ↓reduceIte]; have := ihr hxr; omega

theorem findSubtree_countNodes_le {t : AuxTree} {x : ℕ} :
    (t.findSubtree x).countNodes ≤ t.countNodes := by
  induction t with
  | leaf => exact Nat.le_refl 0
  | node id l r ihl ihr =>
      have hl : (l.findSubtree x).countNodes ≤ l.countNodes := ihl
      have hr : (r.findSubtree x).countNodes ≤ r.countNodes := ihr
      simp only [AuxTree.findSubtree]
      split_ifs
      · exact Nat.le_refl _
      · exact Nat.le_trans hl (by simp [AuxTree.countNodes]; omega)
      · exact Nat.le_trans hr (by simp [AuxTree.countNodes])

theorem parentIn_rootId {t : AuxTree} (p₀ : ℕ) : t.parentIn t.rootId p₀ = p₀ := by
  cases t <;> simp [AuxTree.rootId, AuxTree.parentIn]

/-- Re-establish `SubtreeInv P st' p_new t` from `SubtreeInv P st p_old t` when only the root's
`par` pointer changes (and if `p_new ≠ 0`, its `ppar` becomes `0`), while all other nodes in `t`
keep their state unchanged. -/
theorem SubtreeInv_reparent {P : LctPayload α σ τ}
    {st st' : SplayState α σ τ} {p_old p_new : ℕ} {t : AuxTree}
    (hnd : t.toList.Nodup) (ht : SubtreeInv P st p_old t)
    (hroot : t ≠ .leaf →
      st'.nodes t.rootId = { st.nodes t.rootId with par := p_new } ∧
      (p_new ≠ 0 → (st.nodes t.rootId).ppar = 0))
    (hrest : ∀ u ∈ t.toList, u ≠ t.rootId → st'.nodes u = st.nodes u) :
    SubtreeInv P st' p_new t := by
  cases t with
  | leaf => trivial
  | node rid l r =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨_, hnl, _, hnr, _⟩
      rcases ht with ⟨hrid, hl_eq, hr_eq, _, _, hsz, hsum, hl, hr⟩
      rcases hroot (by simp) with ⟨hnode, hpp0⟩
      simp only [AuxTree.rootId] at hnode hpp0 hrest
      have hl' : SubtreeInv P st' rid l :=
        SubtreeInv_agree hl (fun u hu => (hrest u (by simp [AuxTree.toList, hu])
          (fun h => hnl (h ▸ hu))).symm)
      have hr' : SubtreeInv P st' rid r :=
        SubtreeInv_agree hr (fun u hu => (hrest u (by simp [AuxTree.toList, hu])
          (fun h => hnr (h ▸ hu))).symm)
      have hev_eq : evalPairs P st' (.node rid l r) false P.idTag =
          evalPairs P st (.node rid l r) false P.idTag := by
        refine evalPairs_agree_vrt P (fun u hu => ?_) false P.idTag
        by_cases hur : u = rid
        · subst hur; simp [hnode]
        · rw [hrest u hu hur]; exact ⟨rfl, rfl, rfl⟩
      refine ⟨hrid, ?_, ?_, ?_, ?_, ?_, ?_, hl', hr'⟩
      · simpa [hnode] using hl_eq
      · simpa [hnode] using hr_eq
      · simp [hnode]
      · intro hp; simp [hnode, hpp0 hp]
      · simpa [hnode] using hsz
      · rw [hnode, hev_eq]; exact hsum

private theorem pull_val_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).val = (st.nodes u).val := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

/-! ### `rotate` preservation -/

private theorem rotate_st8_right {st : SplayState α σ τ}
    {x p g : ℕ} (B : AuxTree)
    (hxp : x ≠ p) (hxg : x ≠ g) (hpg : p ≠ g)
    (hb_nx : B.rootId ≠ x) (hb_np : B.rootId ≠ p) (hb_ng : B.rootId ≠ 0 → B.rootId ≠ g) :
    let st1 := st.setRight x p
    let st2 := st1.setLeft p B.rootId
    let st3 := if B.rootId = 0 then st2 else st2.setPar B.rootId p
    let st4 := st3.setPar p x
    let st5 := st4.setPar x g
    let st6 := st5.setPpar x (st.nodes p).ppar
    let st7 := st6.setPpar p 0
    let st8 :=
      if g = 0 then st7
      else if p == (st7.nodes g).left then st7.setLeft g x
      else st7.setRight g x
    st8.nodes x = { st.nodes x with right := p, par := g, ppar := (st.nodes p).ppar } ∧
    st8.nodes p = { st.nodes p with left := B.rootId, par := x, ppar := 0 } ∧
    (B.rootId ≠ 0 → st8.nodes B.rootId = { st.nodes B.rootId with par := p }) ∧
    (g ≠ 0 → st8.nodes g =
      if p = (st.nodes g).left then { st.nodes g with left := x }
      else { st.nodes g with right := x }) ∧
    (∀ u, u ≠ x → u ≠ p → (B.rootId ≠ 0 → u ≠ B.rootId) → (g ≠ 0 → u ≠ g) →
      st8.nodes u = st.nodes u) := by
  intro st1 st2 st3 st4 st5 st6 st7 st8
  have hx1 : st1.nodes x = { st.nodes x with right := p } := by simp [st1, setRight]
  have hp1 : st1.nodes p = st.nodes p := by simp [st1, setRight, hxp.symm]
  have hb1 : ∀ u ≠ x, st1.nodes u = st.nodes u := fun u hu => by simp [st1, setRight, hu]
  have hx2 : st2.nodes x = st1.nodes x := by simp [st2, setLeft, hxp]
  have hp2 : st2.nodes p = { st1.nodes p with left := B.rootId } := by simp [st2, setLeft]
  have hb2 : ∀ u ≠ p, st2.nodes u = st1.nodes u := fun u hu => by simp [st2, setLeft, hu]
  have hx3 : st3.nodes x = st2.nodes x := by
    by_cases h : B.rootId = 0 <;> simp [st3, h, setPar, hb_nx.symm]
  have hp3 : st3.nodes p = st2.nodes p := by
    by_cases h : B.rootId = 0 <;> simp [st3, h, setPar, hb_np.symm]
  have hbb3 : B.rootId ≠ 0 → st3.nodes B.rootId = { st.nodes B.rootId with par := p } := fun h => by
    have h2 : st2.nodes B.rootId = st.nodes B.rootId := by rw [hb2 _ hb_np, hb1 _ hb_nx]
    simp [st3, h, setPar, h2]
  have hu3 : ∀ u, u ≠ x → u ≠ p → (B.rootId ≠ 0 → u ≠ B.rootId) → st3.nodes u = st.nodes u :=
    fun u h1 h2 h3 => by
      by_cases h : B.rootId = 0
      · simp [st3, h, hb2 u h2, hb1 u h1]
      · simp [st3, h, setPar, h3 h, hb2 u h2, hb1 u h1]
  have hx7 : st7.nodes x = { st.nodes x with right := p, par := g, ppar := (st.nodes p).ppar } := by
    simp [st7, st6, st5, st4, setPpar, setPar, hxp, hx3, hx2, hx1]
  have hp7 : st7.nodes p = { st.nodes p with left := B.rootId, par := x, ppar := 0 } := by
    simp [st7, st6, st5, st4, setPpar, setPar, hxp.symm, hp3, hp2, hp1]
  have hb7 : B.rootId ≠ 0 → st7.nodes B.rootId = { st.nodes B.rootId with par := p } := fun h => by
    simp [st7, st6, st5, st4, setPpar, setPar, hb_np, hb_nx, hbb3 h]
  have hu7 : ∀ u, u ≠ x → u ≠ p → (B.rootId ≠ 0 → u ≠ B.rootId) → st7.nodes u = st.nodes u :=
    fun u h1 h2 h3 => by simp [st7, st6, st5, st4, setPpar, setPar, h2, h1, hu3 u h1 h2 h3]
  have hg7 : g ≠ 0 → st7.nodes g = st.nodes g :=
    fun _ => hu7 g hxg.symm hpg.symm (fun hbn => (hb_ng hbn).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases hg0 : g = 0
    · simp [st8, hg0, hx7]
    · dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, hxg, hx7]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, hxg, hx7]
  · by_cases hg0 : g = 0
    · simp [st8, hg0, hp7]
    · dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, hpg, hp7]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, hpg, hp7]
  · intro hbn0
    by_cases hg0 : g = 0
    · simp [st8, hg0, hb7 hbn0]
    · have hbng := hb_ng hbn0
      dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, hbng, hb7 hbn0]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, hbng, hb7 hbn0]
  · intro hg0
    dsimp only [st8]
    simp only [hg0, ↓reduceIte, hg7 hg0]
    by_cases hgl : p = (st.nodes g).left
    · simp [hgl, setLeft, hg7 hg0]
    · simp [hgl, setRight, hg7 hg0]
  · intro u h1 h2 h3 h4
    by_cases hg0 : g = 0
    · simp [st8, hg0, hu7 u h1 h2 h3]
    · have h4' := h4 hg0
      dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, h4', hu7 u h1 h2 h3]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, h4', hu7 u h1 h2 h3]

private theorem rotate_st8_left {st : SplayState α σ τ}
    {x p g : ℕ} (C : AuxTree)
    (hxp : x ≠ p) (hxg : x ≠ g) (hpg : p ≠ g)
    (hc_nx : C.rootId ≠ x) (hc_np : C.rootId ≠ p) (hc_ng : C.rootId ≠ 0 → C.rootId ≠ g) :
    let st1 := st.setLeft x p
    let st2 := st1.setRight p C.rootId
    let st3 := if C.rootId = 0 then st2 else st2.setPar C.rootId p
    let st4 := st3.setPar p x
    let st5 := st4.setPar x g
    let st6 := st5.setPpar x (st.nodes p).ppar
    let st7 := st6.setPpar p 0
    let st8 :=
      if g = 0 then st7
      else if p == (st7.nodes g).left then st7.setLeft g x
      else st7.setRight g x
    st8.nodes x = { st.nodes x with left := p, par := g, ppar := (st.nodes p).ppar } ∧
    st8.nodes p = { st.nodes p with right := C.rootId, par := x, ppar := 0 } ∧
    (C.rootId ≠ 0 → st8.nodes C.rootId = { st.nodes C.rootId with par := p }) ∧
    (g ≠ 0 → st8.nodes g =
      if p = (st.nodes g).left then { st.nodes g with left := x }
      else { st.nodes g with right := x }) ∧
    (∀ u, u ≠ x → u ≠ p → (C.rootId ≠ 0 → u ≠ C.rootId) → (g ≠ 0 → u ≠ g) →
      st8.nodes u = st.nodes u) := by
  intro st1 st2 st3 st4 st5 st6 st7 st8
  have hx1 : st1.nodes x = { st.nodes x with left := p } := by simp [st1, setLeft]
  have hp1 : st1.nodes p = st.nodes p := by simp [st1, setLeft, hxp.symm]
  have hb1 : ∀ u ≠ x, st1.nodes u = st.nodes u := fun u hu => by simp [st1, setLeft, hu]
  have hx2 : st2.nodes x = st1.nodes x := by simp [st2, setRight, hxp]
  have hp2 : st2.nodes p = { st1.nodes p with right := C.rootId } := by simp [st2, setRight]
  have hb2 : ∀ u ≠ p, st2.nodes u = st1.nodes u := fun u hu => by simp [st2, setRight, hu]
  have hx3 : st3.nodes x = st2.nodes x := by
    by_cases h : C.rootId = 0 <;> simp [st3, h, setPar, hc_nx.symm]
  have hp3 : st3.nodes p = st2.nodes p := by
    by_cases h : C.rootId = 0 <;> simp [st3, h, setPar, hc_np.symm]
  have hcc3 : C.rootId ≠ 0 → st3.nodes C.rootId = { st.nodes C.rootId with par := p } := fun h => by
    have h2 : st2.nodes C.rootId = st.nodes C.rootId := by rw [hb2 _ hc_np, hb1 _ hc_nx]
    simp [st3, h, setPar, h2]
  have hu3 : ∀ u, u ≠ x → u ≠ p → (C.rootId ≠ 0 → u ≠ C.rootId) → st3.nodes u = st.nodes u :=
    fun u h1 h2 h3 => by
      by_cases h : C.rootId = 0
      · simp [st3, h, hb2 u h2, hb1 u h1]
      · simp [st3, h, setPar, h3 h, hb2 u h2, hb1 u h1]
  have hx7 : st7.nodes x = { st.nodes x with left := p, par := g, ppar := (st.nodes p).ppar } := by
    simp [st7, st6, st5, st4, setPpar, setPar, hxp, hx3, hx2, hx1]
  have hp7 : st7.nodes p = { st.nodes p with right := C.rootId, par := x, ppar := 0 } := by
    simp [st7, st6, st5, st4, setPpar, setPar, hxp.symm, hp3, hp2, hp1]
  have hc7 : C.rootId ≠ 0 → st7.nodes C.rootId = { st.nodes C.rootId with par := p } := fun h => by
    simp [st7, st6, st5, st4, setPpar, setPar, hc_np, hc_nx, hcc3 h]
  have hu7 : ∀ u, u ≠ x → u ≠ p → (C.rootId ≠ 0 → u ≠ C.rootId) → st7.nodes u = st.nodes u :=
    fun u h1 h2 h3 => by simp [st7, st6, st5, st4, setPpar, setPar, h2, h1, hu3 u h1 h2 h3]
  have hg7 : g ≠ 0 → st7.nodes g = st.nodes g :=
    fun _ => hu7 g hxg.symm hpg.symm (fun hcn => (hc_ng hcn).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases hg0 : g = 0
    · simp [st8, hg0, hx7]
    · dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, hxg, hx7]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, hxg, hx7]
  · by_cases hg0 : g = 0
    · simp [st8, hg0, hp7]
    · dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, hpg, hp7]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, hpg, hp7]
  · intro hcn0
    by_cases hg0 : g = 0
    · simp [st8, hg0, hc7 hcn0]
    · have hcng := hc_ng hcn0
      dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, hcng, hc7 hcn0]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, hcng, hc7 hcn0]
  · intro hg0
    dsimp only [st8]
    simp only [hg0, ↓reduceIte, hg7 hg0]
    by_cases hgl : p = (st.nodes g).left
    · simp [hgl, setLeft, hg7 hg0]
    · simp [hgl, setRight, hg7 hg0]
  · intro u h1 h2 h3 h4
    by_cases hg0 : g = 0
    · simp [st8, hg0, hu7 u h1 h2 h3]
    · have h4' := h4 hg0
      dsimp only [st8]
      by_cases hgl : p = (st7.nodes g).left
      · have hb : (p == (st7.nodes g).left) = true := beq_iff_eq.mpr hgl
        simp [hg0, hb, setLeft, h4', hu7 u h1 h2 h3]
      · have hb : (p == (st7.nodes g).left) = false := beq_false_of_ne hgl
        simp [hg0, hb, setRight, h4', hu7 u h1 h2 h3]

private theorem rootId_ne_zero_of_ne_leaf {P : LctPayload α σ τ}
    {st : SplayState α σ τ} {rp : ℕ} {t : AuxTree}
    (ht : SubtreeInv P st rp t) (hne : t ≠ .leaf) : t.rootId ≠ 0 := by
  cases t with
  | leaf => exact absurd rfl hne
  | node _ _ _ => exact ht.1

/-- Correctness of a single splay rotation `rotate P st x` when `x` and all its ancestors have
`rev = false` and `tag = P.idTag`. -/
theorem rotate_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {t : AuxTree} {x : ℕ}
    (ht : TreeInv P st t) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x, (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag) :
    let t' := t.rotateAt x
    let st' := rotate P st x
    TreeInv P st' t' ∧
    t'.toList.Perm t.toList ∧
    evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag ∧
    (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar ∧
    (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
    (∀ u ∈ t.toList, (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag) := by
  intro t' st'
  have hx_nz : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
  have hpar_x : (st.nodes x).par = t.parentIn x 0 :=
    SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
  set p := t.parentIn x 0
  have hpm_x := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hxr
  have hp_mem : p ∈ t.toList := hpm_x.1
  have hp_nz : p ≠ 0 := SubtreeInv_nonZero ht.sub hp_mem
  have hpar_p : (st.nodes p).par = t.parentIn p 0 :=
    SubtreeInv_par_eq_parentIn ht.nodup ht.sub hp_mem
  set g := t.parentIn p 0
  have hp_in_path : p ∈ t.pathTo x := by
    rw [hpm_x.2.2]; exact List.mem_append.mpr (Or.inl (AuxTree.self_mem_pathTo hp_mem))
  have hx_clean := hclean x (AuxTree.self_mem_pathTo hx)
  have hp_clean := hclean p hp_in_path
  rcases AuxTree.parentIn_child_cases ht.nodup hx hxr rfl with ⟨l, r, hsub_p, hcas⟩
  have hsub_nd : (t.findSubtree p).toList.Nodup := AuxTree.findSubtree_nodup ht.nodup
  have hsub_inv : SubtreeInv P st g (t.findSubtree p) :=
    SubtreeInv_findSubtree ht.nodup ht.sub hp_mem
  have hg_nin_p : g ∉ (t.findSubtree p).toList := by
    by_cases hpr : p = t.rootId
    · have hg0 : g = 0 := by dsimp only [g]; rw [hpr]; exact parentIn_rootId 0
      rw [hg0]; intro hm; exact absurd rfl (SubtreeInv_nonZero ht.sub (AuxTree.findSubtree_subset hm))
    · have hpm_p := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hp_mem hpr
      exact AuxTree.not_mem_findSubtree_of_ancestor ht.nodup hpm_p.1 hp_mem
        (by omega) (AuxTree.self_mem_pathTo hpm_p.1)
  have hg_mem_of_ne : g ≠ 0 → g ∈ t.toList := by
    intro hg0
    have hpr : p ≠ t.rootId := fun h => by
      have hg0' : g = 0 := by dsimp only [g]; rw [h]; exact parentIn_rootId 0
      exact hg0 hg0'
    exact (AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hp_mem hpr).1
  have hdep_px : t.depthOf p + 1 = t.depthOf x := hpm_x.2.1
  have hxp : x ≠ p := fun h => by
    have : t.depthOf x = t.depthOf p := by rw [h]
    omega
  have hxg : x ≠ g := fun h => hg_nin_p (by
    rw [← h, hsub_p]
    rcases hcas with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [AuxTree.toList])
  have hpg : p ≠ g := fun h => by
    have hpm : p ∈ (t.findSubtree p).toList := by
      rw [hsub_p]; simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inr rfl)
    exact hg_nin_p (h ▸ hpm)
  have hanc_p : ∀ u ∈ t.pathTo p, u ≠ p → (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag := by
    intro u hu _
    exact hclean u (by rw [hpm_x.2.2]; exact List.mem_append.mpr (Or.inl hu))
  have hpp_x_root : g ≠ 0 → (st.nodes p).ppar = 0 := by
    intro hg0
    refine SubtreeInv_ppar_zero_of_ne_root ht.nodup ht.sub hp_mem (Or.inr ?_)
    intro hpr
    have hg0' : g = 0 := by dsimp only [g]; rw [hpr]; exact parentIn_rootId 0
    exact hg0 hg0'
  have hperm_t' : t'.toList.Perm t.toList := AuxTree.rotateAt_toList_perm x t
  have ht'_rep : t' = t.replaceSubtree p ((t.findSubtree p).rotateAt x) :=
    (AuxTree.replaceSubtree_rotateAt ht.nodup hx hxr).symm
  have finish : ∀ (s' : AuxTree),
      s' = (t.findSubtree p).rotateAt x →
      s' ≠ .leaf → s'.rootId = x →
      s'.toList.Perm (t.findSubtree p).toList →
      SubtreeInv P st' g s' →
      evalPairs P st' s' false P.idTag = evalPairs P st (t.findSubtree p) false P.idTag →
      (st'.nodes s'.rootId).ppar = (st.nodes p).ppar →
      (∀ u ∈ (t.findSubtree p).toList,
        (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag) →
      (∀ u, u ∉ (t.findSubtree p).toList → (g ≠ 0 → u ≠ g) → st'.nodes u = st.nodes u) →
      (g ≠ 0 → st'.nodes g =
        if p = (st.nodes g).left then { st.nodes g with left := x }
        else { st.nodes g with right := x }) →
      TreeInv P st' t' ∧ t'.toList.Perm t.toList ∧
      evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag ∧
      (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar ∧
      (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
      (∀ u ∈ t.toList, (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag) := by
    intro s' hs'_eq hs'_ne hs'_root hs'_perm hs'_sub hs'_eval hs'_ppar hrt_in hout_ng hnod_g
    have hother : ∀ u ∈ t.toList, u ∉ (t.findSubtree p).toList →
        (st'.nodes u).val = (st.nodes u).val ∧
        (st'.nodes u).rev = (st.nodes u).rev ∧
        (st'.nodes u).tag = (st.nodes u).tag ∧
        (st'.nodes u).par = (st.nodes u).par ∧
        (st'.nodes u).ppar = (st.nodes u).ppar ∧
        (st'.nodes u).sz = (st.nodes u).sz ∧
        (st'.nodes u).sum = (st.nodes u).sum ∧
        (u ≠ g → (st'.nodes u).left = (st.nodes u).left ∧ (st'.nodes u).right = (st.nodes u).right) ∧
        (u = g →
          (st'.nodes u).left = (if (st.nodes u).left = p then s'.rootId else (st.nodes u).left) ∧
          (st'.nodes u).right = (if (st.nodes u).right = p then s'.rootId else (st.nodes u).right)) := by
      intro u hu hu_nin
      by_cases hug : u = g
      · have hg_in : g ∈ t.toList := hug ▸ hu
        have hg_nz : g ≠ 0 := SubtreeInv_nonZero ht.sub hg_in
        have hg_node := hnod_g hg_nz
        have hparent_child : (st.nodes g).left = p ∨ (st.nodes g).right = p := by
          have hsub_u := SubtreeInv_findSubtree ht.nodup ht.sub hg_in
          cases t_u : t.findSubtree g with
          | leaf =>
              exfalso; obtain ⟨lu, ru, hlu⟩ := AuxTree.findSubtree_root_of_mem hg_in
              rw [hlu] at t_u; cases t_u
          | node uid lu ru =>
              rw [t_u] at hsub_u
              have hpr' : p ≠ t.rootId := fun h => by
                have hg0 : g = 0 := by dsimp only [g]; rw [h]; exact parentIn_rootId 0
                exact hg_nz hg0
              rcases AuxTree.parentIn_child_cases ht.nodup hp_mem hpr' rfl with ⟨gl, gr, hg_eq, hcas_g⟩
              rw [hg_eq] at t_u
              cases t_u
              rcases hsub_u with ⟨_, hl_u, hr_u, _, _, _, _, _, _⟩
              rcases hcas_g with ⟨_, _, h1⟩ | ⟨_, _, h2⟩
              · exact Or.inl (by rw [hl_u, h1]; rfl)
              · exact Or.inr (by rw [hr_u, h2]; rfl)
        rw [hug]
        by_cases hgl : p = (st.nodes g).left
        · have hne_r : (st.nodes g).right ≠ p := by
            intro hr_eq
            have hsub_u := SubtreeInv_findSubtree ht.nodup ht.sub hg_in
            obtain ⟨lu, ru, hlu⟩ := AuxTree.findSubtree_root_of_mem hg_in
            rw [hlu] at hsub_u
            rcases hsub_u with ⟨_, hl_u, hr_u, _, _, _, _, _, _⟩
            have hnd_u := hlu ▸ (AuxTree.findSubtree_nodup ht.nodup : (t.findSubtree g).toList.Nodup)
            rcases AuxTree.nodup_node_unfold hnd_u with ⟨_, _, _, _, hdisj_u⟩
            have hpl_mem : p ∈ lu.toList := by
              cases lu with
              | leaf => exact absurd (hgl.trans (by simpa [AuxTree.rootId] using hl_u)) hp_nz
              | node lid _ _ =>
                  have hpid : p = lid := hgl.trans (by simpa [AuxTree.rootId] using hl_u)
                  rw [hpid]; simp [AuxTree.toList]
            have hpr_mem : p ∈ ru.toList := by
              cases ru with
              | leaf => exact absurd (hr_eq.symm.trans (by simpa [AuxTree.rootId] using hr_u)) hp_nz
              | node rid _ _ =>
                  have hpid : p = rid := hr_eq.symm.trans (by simpa [AuxTree.rootId] using hr_u)
                  rw [hpid]; simp [AuxTree.toList]
            exact hdisj_u p hpl_mem hpr_mem
          have h1 : st'.nodes g = { st.nodes g with left := x } := by rw [hg_node, ite_eq_left hgl]
          simp [h1, hs'_root, ite_eq_left hgl.symm, ite_eq_right hne_r]
        · have hgr : (st.nodes g).right = p := hparent_child.resolve_left (Ne.symm hgl)
          have hgl' : (st.nodes g).left ≠ p := Ne.symm hgl
          have h1 : st'.nodes g = { st.nodes g with right := x } := by rw [hg_node, ite_eq_right hgl]
          simp [h1, hs'_root, ite_eq_right hgl', ite_eq_left hgr]
      · have heq := hout_ng u hu_nin (fun _ => hug)
        simp [heq]; exact fun h => absurd h hug
    have hsub_t' : SubtreeInv P st' 0 t' := by
      rw [ht'_rep, ← hs'_eq]
      exact SubtreeInv_replaceSubtree_clean hL ht.nodup ht.sub hp_mem hs'_ne hs'_perm hs'_sub hs'_eval
        hanc_p hother
    have heval_vrt : ∀ u ∈ t.toList, u ∉ (t.findSubtree p).toList →
        (st'.nodes u).val = (st.nodes u).val ∧
        (st'.nodes u).rev = (st.nodes u).rev ∧
        (st'.nodes u).tag = (st.nodes u).tag := fun u hu hnin =>
      let ho := hother u hu hnin; ⟨ho.1, ho.2.1, ho.2.2.1⟩
    have heval_t' : evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag := by
      rw [ht'_rep, ← hs'_eq]
      exact evalPairs_replaceSubtree_clean hL ht.nodup hp_mem hs'_eval hanc_p heval_vrt
    have hppar_t' : (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar := by
      have ht_ne : t ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hx
      rw [ht'_rep, ← hs'_eq, AuxTree.replaceSubtree_rootId ht_ne hs'_ne]
      by_cases htr : t.rootId = p
      · simp only [htr, ↓reduceIte]
        exact hs'_ppar
      · simp only [htr, ↓reduceIte]
        have htr_nin : t.rootId ∉ (t.findSubtree p).toList := fun hm =>
          AuxTree.root_not_mem_findSubtree ht.nodup hp_mem hm htr rfl
        exact (hother t.rootId (AuxTree.rootId_mem ht_ne) htr_nin).2.2.2.2.1
    refine ⟨⟨hperm_t'.nodup_iff.mpr ht.nodup, hsub_t'⟩, hperm_t', heval_t', hppar_t', ?_, ?_⟩
    · intro u hu
      exact hout_ng u (fun hm => hu (AuxTree.findSubtree_subset hm))
        (fun hg0 h => hu (h ▸ hg_mem_of_ne hg0))
    · intro u hu
      by_cases hu_sub : u ∈ (t.findSubtree p).toList
      · exact hrt_in u hu_sub
      · have ho := hother u hu hu_sub; exact ⟨ho.2.1, ho.2.2.1⟩
  rcases hcas with ⟨A, B, rfl⟩ | ⟨C, D, rfl⟩
  · -- Right rotation branch: `t.findSubtree p = .node p (.node x A B) r`
    let s' := AuxTree.node x A (.node p B r)
    have hsub_nd' := hsub_nd
    rw [hsub_p] at hsub_nd'
    rcases AuxTree.nodup_node_unfold hsub_nd' with ⟨hxAB_nd, hp_nxAB, hr_nd, hp_nr, hdisj_xAB_r⟩
    rcases AuxTree.nodup_node_unfold hxAB_nd with ⟨hA_nd, hx_nA, hB_nd, hx_nB, hdisj_AB⟩
    rw [hsub_p] at hsub_inv
    rcases hsub_inv with ⟨_, hl_p, hr_p, _, _, _, _, hsub_xAB, hsub_r⟩
    rcases hsub_xAB with ⟨_, hl_x, hr_x, _, _, _, _, hsub_A, hsub_B⟩
    simp only [AuxTree.rootId] at hl_p hl_x hr_x
    have hx_nr : x ∉ r.toList := hdisj_xAB_r x (by simp [AuxTree.toList])
    have hp_nA : p ∉ A.toList := fun h => hp_nxAB (show p ∈ (AuxTree.node x A B).toList from by simp [AuxTree.toList, h])
    have hp_nB : p ∉ B.toList := fun h => hp_nxAB (show p ∈ (AuxTree.node x A B).toList from by simp [AuxTree.toList, h])
    have hB_nin_p : B.rootId ≠ p := by
      cases B with
      | leaf => exact hp_nz.symm
      | node bid _ _ => exact fun h => hp_nB (h ▸ by simp [AuxTree.rootId, AuxTree.toList])
    have hB_nin_x : B.rootId ≠ x := by
      cases B with
      | leaf => exact hx_nz.symm
      | node bid _ _ => exact fun h => hx_nB (h ▸ by simp [AuxTree.rootId, AuxTree.toList])
    have hB_nin_g : B.rootId ≠ 0 → B.rootId ≠ g := by
      intro hb0 h
      have hb_mem : B.rootId ∈ (t.findSubtree p).toList := by
        rw [hsub_p]
        cases B with
        | leaf => exact absurd rfl hb0
        | node bid _ _ => simp [AuxTree.rootId, AuxTree.toList]
      exact hg_nin_p (h ▸ hb_mem)
    have hB_nin_A : B.rootId ≠ 0 → B.rootId ∉ A.toList := by
      intro hb0 h
      cases B with
      | leaf => exact absurd rfl hb0
      | node bid _ _ => exact hdisj_AB bid h (by simp [AuxTree.toList])
    have hB_nin_r : B.rootId ≠ 0 → B.rootId ∉ r.toList := by
      intro hb0 h
      cases B with
      | leaf => exact absurd rfl hb0
      | node bid _ _ =>
          exact hdisj_xAB_r bid (by simp [AuxTree.toList]) h
    -- Evaluate `rotate P st x`
    have hleft_flag : (x == (st.nodes p).left) = true := beq_iff_eq.mpr hl_p.symm
    let st1 := st.setRight x p
    let st2 := st1.setLeft p B.rootId
    let st3 := if B.rootId = 0 then st2 else st2.setPar B.rootId p
    let st4 := st3.setPar p x
    let st5 := st4.setPar x g
    let st6 := st5.setPpar x (st.nodes p).ppar
    let st7 := st6.setPpar p 0
    let st8 :=
      if g = 0 then st7
      else if p == (st7.nodes g).left then st7.setLeft g x
      else st7.setRight g x
    have hst'_eq : st' = pull P (pull P st8 p) x := by
      dsimp only [st', rotate, st1, st2, st3, st4, st5, st6, st7, st8]
      rw [ite_eq_right hx_nz]
      simp only [hpar_x, hp_nz, ↓reduceIte, hleft_flag, hr_x, hpar_p]; rfl
    rcases rotate_st8_right (st := st) B hxp hxg hpg hB_nin_x hB_nin_p hB_nin_g with
      ⟨hx8, hp8, hb8, hg8, hu8⟩
    have hsub_B8 : SubtreeInv P st8 p B := by
      refine SubtreeInv_reparent hB_nd hsub_B (fun hB => ?_) (fun u hu hur => ?_)
      · have hb0 : B.rootId ≠ 0 := rootId_ne_zero_of_ne_leaf hsub_B hB
        exact ⟨hb8 hb0, fun _ => SubtreeInv_ppar_zero_of_ne_root hB_nd hsub_B
          (AuxTree.rootId_mem hB) (Or.inl hx_nz)⟩
      · refine hu8 u (fun h => hx_nB (h ▸ hu)) (fun h => hp_nB (h ▸ hu))
          (fun _ h => hur h) (fun _ h => hg_nin_p (by rw [← h, hsub_p]; simp [AuxTree.toList, hu]))
    have hsub_r8 : SubtreeInv P st8 p r := by
      refine SubtreeInv_agree hsub_r (fun u hu => ?_)
      refine (hu8 u (fun h => hx_nr (h ▸ hu)) (fun h => hp_nr (show p ∈ r.toList from h ▸ hu))
        (fun hb0 h => hB_nin_r hb0 (h ▸ hu))
        (fun _ h => hg_nin_p (by rw [← h, hsub_p]; simp [AuxTree.toList, hu]))).symm
    let st9 := pull P st8 p
    rcases pull_node_build hL hp_nz hp_nB hp_nr
      (by rw [hp8]) (by rw [hp8]; exact hr_p) (by rw [hp8]) (by intro _; rw [hp8])
      (by rw [hp8]; exact hp_clean.1) (by rw [hp8]; exact hp_clean.2) hsub_B8 hsub_r8 with
      ⟨hsub_p9, hrev_p9, htag_p9, _, hne_p9⟩
    have hsub_A9 : SubtreeInv P st9 x A := by
      refine SubtreeInv_agree hsub_A (fun u hu => ?_)
      have hne_p : u ≠ p := fun h => hp_nA (h ▸ hu)
      have h8 := hu8 u (fun h => hx_nA (h ▸ hu)) hne_p
        (fun hb0 h => hB_nin_A hb0 (h ▸ hu))
        (fun _ h => hg_nin_p (by rw [← h, hsub_p]; simp [AuxTree.toList, hu]))
      exact ((hne_p9 u hne_p).trans h8).symm
    have hx9 : st9.nodes x = st8.nodes x := hne_p9 x hxp
    rcases pull_node_build hL hx_nz hx_nA (by simp [AuxTree.toList, hxp, hx_nB, hx_nr])
      (by rw [hx9, hx8]; exact hl_x) (by rw [hx9, hx8]; rfl)
      (by rw [hx9, hx8]) (by intro hg0; rw [hx9, hx8]; exact hpp_x_root hg0)
      (by rw [hx9, hx8]; exact hx_clean.1) (by rw [hx9, hx8]; exact hx_clean.2) hsub_A9 hsub_p9 with
      ⟨hsub_x', hrev_x', htag_x', hpp_x', hne_x'⟩
    rw [← hst'_eq] at hsub_x' hrev_x' htag_x' hpp_x' hne_x'
    have hst'_rest : ∀ u, u ∉ (t.findSubtree p).toList → (g ≠ 0 → u ≠ g) → st'.nodes u = st.nodes u := by
      intro u hu hug
      rw [hsub_p] at hu
      have hux : u ≠ x := fun h => hu (by subst h; simp [AuxTree.toList])
      have hup : u ≠ p := fun h => hu (by dsimp only [p] at h; rw [h]; simp [AuxTree.toList])
      have hub : B.rootId ≠ 0 → u ≠ B.rootId := fun hb0 h => hu (by
        cases B with
        | leaf => exact absurd rfl hb0
        | node bid _ _ => simp [AuxTree.rootId] at h; subst h; simp [AuxTree.toList])
      exact (hne_x' u hux).trans ((hne_p9 u hup).trans (hu8 u hux hup hub hug))
    have hst'_vrt : ∀ u ∈ (A.toList ++ B.toList ++ r.toList),
        (st'.nodes u).val = (st.nodes u).val ∧
        (st'.nodes u).rev = (st.nodes u).rev ∧
        (st'.nodes u).tag = (st.nodes u).tag := by
      intro u hu
      have hux : u ≠ x := by
        simp only [List.mem_append] at hu
        rcases hu with (h | h) | h
        · exact fun he => hx_nA (he ▸ h)
        · exact fun he => hx_nB (he ▸ h)
        · exact fun he => hx_nr (he ▸ h)
      have hup : u ≠ p := by
        simp only [List.mem_append] at hu
        rcases hu with (h | h) | h
        · exact fun he => hp_nA (he ▸ h)
        · exact fun he => hp_nB (he ▸ h)
        · exact fun he => hp_nr (show p ∈ r.toList from he ▸ h)
      have hug : g ≠ 0 → u ≠ g := fun _ h => hg_nin_p (by
        rw [hsub_p, ← h]
        simp only [List.mem_append] at hu
        rcases hu with (h1 | h1) | h1 <;> simp [AuxTree.toList, h1])
      rw [hne_x' u hux, hne_p9 u hup]
      by_cases hub : B.rootId ≠ 0 ∧ u = B.rootId
      · rw [hub.2, hb8 hub.1]; exact ⟨rfl, rfl, rfl⟩
      · have h8 := hu8 u hux hup (fun hb0 hu' => hub ⟨hb0, hu'⟩) hug
        rw [h8]; exact ⟨rfl, rfl, rfl⟩
    have hs'_eval : evalPairs P st' s' false P.idTag =
        evalPairs P st (t.findSubtree p) false P.idTag := by
      rw [hsub_p]
      have hevA : evalPairs P st' A false P.idTag = evalPairs P st A false P.idTag :=
        evalPairs_agree_vrt P (fun u hu => hst'_vrt u (by simp [hu])) false P.idTag
      have hevB : evalPairs P st' B false P.idTag = evalPairs P st B false P.idTag :=
        evalPairs_agree_vrt P (fun u hu => hst'_vrt u (by simp [hu])) false P.idTag
      have hevr : evalPairs P st' r false P.idTag = evalPairs P st r false P.idTag :=
        evalPairs_agree_vrt P (fun u hu => hst'_vrt u (by simp [hu])) false P.idTag
      have hx_val' : (st'.nodes x).val = (st.nodes x).val := by
        rw [hst'_eq, pull_val_eq, pull_val_eq, hx8]
      have hp_val' : (st'.nodes p).val = (st.nodes p).val := by
        rw [hst'_eq, pull_val_eq, pull_val_eq, hp8]
      have hp_rev' : (st'.nodes p).rev = false := by rw [hne_x' p hxp.symm]; exact hrev_p9
      have hp_tag' : (st'.nodes p).tag = P.idTag := by rw [hne_x' p hxp.symm]; exact htag_p9
      have hp_cl1 : (st.nodes (t.parentIn x 0)).rev = false := hp_clean.1
      have hp_cl2 : (st.nodes (t.parentIn x 0)).tag = P.idTag := hp_clean.2
      simp only [s', evalPairs, hrev_x', htag_x', hp_rev', hp_tag', hx_clean.1, hx_clean.2,
        hp_cl1, hp_cl2, hx_val', hp_val', Bool.false_xor, Bool.false_eq_true, ↓reduceIte,
        hL.compTag_id_left, hL.actVal_id, hevA, hevB, hevr, List.append_assoc]; rfl
    have hs'_rt : ∀ u ∈ (t.findSubtree p).toList,
        (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag := by
      intro u hu
      rw [hsub_p] at hu
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (((huA | rfl) | huB) | hup) | hur
      · have h := hst'_vrt u (by simp [huA]); exact ⟨h.2.1, h.2.2⟩
      · exact ⟨hrev_x'.trans hx_clean.1.symm, htag_x'.trans hx_clean.2.symm⟩
      · have h := hst'_vrt u (by simp [huB]); exact ⟨h.2.1, h.2.2⟩
      · rw [hup, hne_x' p hxp.symm]
        exact ⟨hrev_p9.trans hp_clean.1.symm, htag_p9.trans hp_clean.2.symm⟩
      · have h := hst'_vrt u (by simp [hur]); exact ⟨h.2.1, h.2.2⟩
    have hg'_node : g ≠ 0 → st'.nodes g =
        if p = (st.nodes g).left then { st.nodes g with left := x }
        else { st.nodes g with right := x } := by
      intro hg0
      rw [hne_x' g hxg.symm, hne_p9 g hpg.symm, hg8 hg0]
    refine finish s' ?_ (by simp [s']) rfl ?_ hsub_x' hs'_eval ?_ hs'_rt hst'_rest hg'_node
    · rw [hsub_p]; exact (AuxTree.rotateAt_zigRight A B r hxp.symm).symm
    · rw [hsub_p]; simp only [s', AuxTree.toList, List.append_assoc]; exact List.Perm.refl _
    · simp only [s', AuxTree.rootId]; rw [hpp_x', hx9, hx8]
  · -- Left rotation branch: `t.findSubtree p = .node p l (.node x C D)`
    let s' := AuxTree.node x (.node p l C) D
    have hsub_nd' := hsub_nd
    rw [hsub_p] at hsub_nd'
    rcases AuxTree.nodup_node_unfold hsub_nd' with ⟨hl_nd, hp_nl, hxCD_nd, hp_nxCD, hdisj_l_xCD⟩
    rcases AuxTree.nodup_node_unfold hxCD_nd with ⟨hC_nd, hx_nC, hD_nd, hx_nD, hdisj_CD⟩
    rw [hsub_p] at hsub_inv
    rcases hsub_inv with ⟨_, hl_p, hr_p, _, _, _, _, hsub_l, hsub_xCD⟩
    rcases hsub_xCD with ⟨_, hl_x, hr_x, _, _, _, _, hsub_C, hsub_D⟩
    simp only [AuxTree.rootId] at hr_p hl_x hr_x
    have hx_nl : x ∉ l.toList := fun h => hdisj_l_xCD x h (by simp [AuxTree.toList])
    have hl_has_x : ¬ l.hasRoot x := fun h => by
      obtain ⟨A', B', rfl⟩ := AuxTree.hasRoot_iff.mp h
      exact hx_nl (by simp [AuxTree.toList])
    have hp_nC : p ∉ C.toList := fun h => hp_nxCD (show p ∈ (AuxTree.node x C D).toList from by simp [AuxTree.toList, h])
    have hp_nD : p ∉ D.toList := fun h => hp_nxCD (show p ∈ (AuxTree.node x C D).toList from by simp [AuxTree.toList, h])
    have hC_nin_p : C.rootId ≠ p := by
      cases C with
      | leaf => exact hp_nz.symm
      | node cid _ _ => exact fun h => hp_nC (h ▸ by simp [AuxTree.rootId, AuxTree.toList])
    have hC_nin_x : C.rootId ≠ x := by
      cases C with
      | leaf => exact hx_nz.symm
      | node cid _ _ => exact fun h => hx_nC (h ▸ by simp [AuxTree.rootId, AuxTree.toList])
    have hC_nin_g : C.rootId ≠ 0 → C.rootId ≠ g := by
      intro hc0 h
      have hc_mem : C.rootId ∈ (t.findSubtree p).toList := by
        rw [hsub_p]
        cases C with
        | leaf => exact absurd rfl hc0
        | node cid _ _ => simp [AuxTree.rootId, AuxTree.toList]
      exact hg_nin_p (h ▸ hc_mem)
    have hC_nin_l : C.rootId ≠ 0 → C.rootId ∉ l.toList := by
      intro hc0 h
      cases C with
      | leaf => exact absurd rfl hc0
      | node cid _ _ =>
          exact hdisj_l_xCD cid h (by simp [AuxTree.toList])
    have hC_nin_D : C.rootId ≠ 0 → C.rootId ∉ D.toList := by
      intro hc0 h
      cases C with
      | leaf => exact absurd rfl hc0
      | node cid _ _ => exact hdisj_CD cid (by simp [AuxTree.toList]) h
    have hleft_flag : (x == (st.nodes p).left) = false := by
      have : (st.nodes p).left ≠ x := by
        rw [hl_p]
        cases l with
        | leaf => exact hx_nz.symm
        | node lid _ _ => exact fun h => hx_nl (h ▸ by simp [AuxTree.rootId, AuxTree.toList])
      exact beq_false_of_ne this.symm
    let st1 := st.setLeft x p
    let st2 := st1.setRight p C.rootId
    let st3 := if C.rootId = 0 then st2 else st2.setPar C.rootId p
    let st4 := st3.setPar p x
    let st5 := st4.setPar x g
    let st6 := st5.setPpar x (st.nodes p).ppar
    let st7 := st6.setPpar p 0
    let st8 :=
      if g = 0 then st7
      else if p == (st7.nodes g).left then st7.setLeft g x
      else st7.setRight g x
    have hst'_eq : st' = pull P (pull P st8 p) x := by
      dsimp only [st', rotate, st1, st2, st3, st4, st5, st6, st7, st8]
      rw [ite_eq_right hx_nz]
      simp only [hpar_x, hp_nz, ↓reduceIte, hleft_flag, Bool.false_eq_true, hl_x, hpar_p]; rfl
    rcases rotate_st8_left (st := st) C hxp hxg hpg hC_nin_x hC_nin_p hC_nin_g with
      ⟨hx8, hp8, hc8, hg8, hu8⟩
    have hsub_l8 : SubtreeInv P st8 p l := by
      refine SubtreeInv_agree hsub_l (fun u hu => ?_)
      refine (hu8 u (fun h => hx_nl (h ▸ hu)) (fun h => hp_nl (show p ∈ l.toList from h ▸ hu))
        (fun hc0 h => hC_nin_l hc0 (h ▸ hu))
        (fun _ h => hg_nin_p (by rw [← h, hsub_p]; simp [AuxTree.toList, hu]))).symm
    have hsub_C8 : SubtreeInv P st8 p C := by
      refine SubtreeInv_reparent hC_nd hsub_C (fun hC => ?_) (fun u hu hur => ?_)
      · have hc0 : C.rootId ≠ 0 := rootId_ne_zero_of_ne_leaf hsub_C hC
        exact ⟨hc8 hc0, fun _ => SubtreeInv_ppar_zero_of_ne_root hC_nd hsub_C
          (AuxTree.rootId_mem hC) (Or.inl hx_nz)⟩
      · refine hu8 u (fun h => hx_nC (h ▸ hu)) (fun h => hp_nC (h ▸ hu))
          (fun _ h => hur h) (fun _ h => hg_nin_p (by rw [← h, hsub_p]; simp [AuxTree.toList, hu]))
    let st9 := pull P st8 p
    rcases pull_node_build hL hp_nz hp_nl hp_nC
      (by rw [hp8]; exact hl_p) (by rw [hp8]) (by rw [hp8]) (by intro _; rw [hp8])
      (by rw [hp8]; exact hp_clean.1) (by rw [hp8]; exact hp_clean.2) hsub_l8 hsub_C8 with
      ⟨hsub_p9, hrev_p9, htag_p9, _, hne_p9⟩
    have hsub_D9 : SubtreeInv P st9 x D := by
      refine SubtreeInv_agree hsub_D (fun u hu => ?_)
      have hne_p : u ≠ p := fun h => hp_nD (h ▸ hu)
      have h8 := hu8 u (fun h => hx_nD (h ▸ hu)) hne_p
        (fun hc0 h => hC_nin_D hc0 (h ▸ hu))
        (fun _ h => hg_nin_p (by rw [← h, hsub_p]; simp [AuxTree.toList, hu]))
      exact ((hne_p9 u hne_p).trans h8).symm
    have hx9 : st9.nodes x = st8.nodes x := hne_p9 x hxp
    rcases pull_node_build hL hx_nz (by simp [AuxTree.toList, hxp, hx_nl, hx_nC]) hx_nD
      (by rw [hx9, hx8]; rfl) (by rw [hx9, hx8]; exact hr_x)
      (by rw [hx9, hx8]) (by intro hg0; rw [hx9, hx8]; exact hpp_x_root hg0)
      (by rw [hx9, hx8]; exact hx_clean.1) (by rw [hx9, hx8]; exact hx_clean.2) hsub_p9 hsub_D9 with
      ⟨hsub_x', hrev_x', htag_x', hpp_x', hne_x'⟩
    rw [← hst'_eq] at hsub_x' hrev_x' htag_x' hpp_x' hne_x'
    have hst'_rest : ∀ u, u ∉ (t.findSubtree p).toList → (g ≠ 0 → u ≠ g) → st'.nodes u = st.nodes u := by
      intro u hu hug
      rw [hsub_p] at hu
      have hux : u ≠ x := fun h => hu (by subst h; simp [AuxTree.toList])
      have hup : u ≠ p := fun h => hu (by dsimp only [p] at h; rw [h]; simp [AuxTree.toList])
      have huc : C.rootId ≠ 0 → u ≠ C.rootId := fun hc0 h => hu (by
        cases C with
        | leaf => exact absurd rfl hc0
        | node cid _ _ => simp [AuxTree.rootId] at h; subst h; simp [AuxTree.toList])
      exact (hne_x' u hux).trans ((hne_p9 u hup).trans (hu8 u hux hup huc hug))
    have hst'_vrt : ∀ u ∈ (l.toList ++ C.toList ++ D.toList),
        (st'.nodes u).val = (st.nodes u).val ∧
        (st'.nodes u).rev = (st.nodes u).rev ∧
        (st'.nodes u).tag = (st.nodes u).tag := by
      intro u hu
      have hux : u ≠ x := by
        simp only [List.mem_append] at hu
        rcases hu with (h | h) | h
        · exact fun he => hx_nl (he ▸ h)
        · exact fun he => hx_nC (he ▸ h)
        · exact fun he => hx_nD (he ▸ h)
      have hup : u ≠ p := by
        simp only [List.mem_append] at hu
        rcases hu with (h | h) | h
        · exact fun he => hp_nl (show p ∈ l.toList from he ▸ h)
        · exact fun he => hp_nC (he ▸ h)
        · exact fun he => hp_nD (he ▸ h)
      have hug : g ≠ 0 → u ≠ g := fun _ h => hg_nin_p (by
        rw [hsub_p, ← h]
        simp only [List.mem_append] at hu
        rcases hu with (h1 | h1) | h1 <;> simp [AuxTree.toList, h1])
      rw [hne_x' u hux, hne_p9 u hup]
      by_cases huc : C.rootId ≠ 0 ∧ u = C.rootId
      · rw [huc.2, hc8 huc.1]; exact ⟨rfl, rfl, rfl⟩
      · have h8 := hu8 u hux hup (fun hc0 hu' => huc ⟨hc0, hu'⟩) hug
        rw [h8]; exact ⟨rfl, rfl, rfl⟩
    have hs'_eval : evalPairs P st' s' false P.idTag =
        evalPairs P st (t.findSubtree p) false P.idTag := by
      rw [hsub_p]
      have hevl : evalPairs P st' l false P.idTag = evalPairs P st l false P.idTag :=
        evalPairs_agree_vrt P (fun u hu => hst'_vrt u (by simp [hu])) false P.idTag
      have hevC : evalPairs P st' C false P.idTag = evalPairs P st C false P.idTag :=
        evalPairs_agree_vrt P (fun u hu => hst'_vrt u (by simp [hu])) false P.idTag
      have hevD : evalPairs P st' D false P.idTag = evalPairs P st D false P.idTag :=
        evalPairs_agree_vrt P (fun u hu => hst'_vrt u (by simp [hu])) false P.idTag
      have hx_val' : (st'.nodes x).val = (st.nodes x).val := by
        rw [hst'_eq, pull_val_eq, pull_val_eq, hx8]
      have hp_val' : (st'.nodes p).val = (st.nodes p).val := by
        rw [hst'_eq, pull_val_eq, pull_val_eq, hp8]
      have hp_rev' : (st'.nodes p).rev = false := by rw [hne_x' p hxp.symm]; exact hrev_p9
      have hp_tag' : (st'.nodes p).tag = P.idTag := by rw [hne_x' p hxp.symm]; exact htag_p9
      have hp_cl1 : (st.nodes (t.parentIn x 0)).rev = false := hp_clean.1
      have hp_cl2 : (st.nodes (t.parentIn x 0)).tag = P.idTag := hp_clean.2
      simp only [s', evalPairs, hrev_x', htag_x', hp_rev', hp_tag', hx_clean.1, hx_clean.2,
        hp_cl1, hp_cl2, hx_val', hp_val', Bool.false_xor, Bool.false_eq_true, ↓reduceIte,
        hL.compTag_id_left, hL.actVal_id, hevl, hevC, hevD, List.append_assoc]; rfl
    have hs'_rt : ∀ u ∈ (t.findSubtree p).toList,
        (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag := by
      intro u hu
      rw [hsub_p] at hu
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hul | hup) | ((huC | rfl) | huD)
      · have h := hst'_vrt u (by simp [hul]); exact ⟨h.2.1, h.2.2⟩
      · rw [hup, hne_x' p hxp.symm]
        exact ⟨hrev_p9.trans hp_clean.1.symm, htag_p9.trans hp_clean.2.symm⟩
      · have h := hst'_vrt u (by simp [huC]); exact ⟨h.2.1, h.2.2⟩
      · exact ⟨hrev_x'.trans hx_clean.1.symm, htag_x'.trans hx_clean.2.symm⟩
      · have h := hst'_vrt u (by simp [huD]); exact ⟨h.2.1, h.2.2⟩
    have hg'_node : g ≠ 0 → st'.nodes g =
        if p = (st.nodes g).left then { st.nodes g with left := x }
        else { st.nodes g with right := x } := by
      intro hg0
      rw [hne_x' g hxg.symm, hne_p9 g hpg.symm, hg8 hg0]
    refine finish s' ?_ (by simp [s']) rfl ?_ hsub_x' hs'_eval ?_ hs'_rt hst'_rest hg'_node
    · rw [hsub_p]; exact (AuxTree.rotateAt_zigLeft l C D hxp.symm hl_has_x).symm
    · rw [hsub_p]; simp only [s', AuxTree.toList, List.append_assoc]; exact List.Perm.refl _
    · simp only [s', AuxTree.rootId]; rw [hpp_x', hx9, hx8]

end SplayState
end MinCostFlow.LinkCut
end
