module

public import MinCostFlow.LinkCut.SplayRotate
import Mathlib.Tactic

/-!
# Correctness and amortized bounds for splay rotations and `splay`

This file proves preservation of `TreeInv`, `evalPairs`, path-parent pointers `ppar`,
and Sleator–Tarjan amortized potential inequalities (`treePhi`) for:
- `SubtreeInv_reparent` (helper when a child's `par` pointer changes)
- `rotate` (`rotate_preserves`)
- `splayStep` (`splayStep_preserves`)
- `splayLoop` (`splayLoop_preserves`)
- `splay` (`splay_preserves_and_phi`)

All results hold for any payload `P : LctPayload α σ τ` satisfying `P.Laws` and any
virtual weight function `vSize : ℕ → ℕ`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

namespace SplayState

variable {α σ τ : Type*}

/-! ### `splayStep` preservation and potential -/

private theorem isZigZig_eq_state {P : LctPayload α σ τ}
    {st : SplayState α σ τ} {t : AuxTree} {x p g : ℕ}
    (ht : TreeInv P st t) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hp : p = t.parentIn x 0) (hp_mem : p ∈ t.toList) (hpr : p ≠ t.rootId)
    (hg : g = t.parentIn p 0) :
    ((x == (st.nodes p).left) == (p == (st.nodes g).left)) = t.isZigZig x p g := by
  have hx_nz : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
  have hp_nz : p ≠ 0 := SubtreeInv_nonZero ht.sub hp_mem
  have hg_mem : g ∈ t.toList := hg ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hp_mem hpr).1
  have hsub_g := SubtreeInv_findSubtree ht.nodup ht.sub hg_mem
  have hsub_g_nd : (t.findSubtree g).toList.Nodup := AuxTree.findSubtree_nodup ht.nodup
  rcases AuxTree.grandparent_child_cases ht.nodup hx hxr hp hp_mem hpr hg with
    ⟨A, B, C, D, hg_eq⟩ | ⟨A, B, C, D, hg_eq⟩ | ⟨A, B, C, D, hg_eq⟩ | ⟨A, B, C, D, hg_eq⟩
  · rw [hg_eq] at hsub_g
    rcases hsub_g with ⟨_, hl_g, _, _, _, _, _, hsub_p, _⟩
    rcases hsub_p with ⟨_, hl_p, _, _, _, _, _, _, _⟩
    simp only [AuxTree.rootId] at hl_g hl_p
    simp [hl_g, hl_p, AuxTree.isZigZig, hg_eq]
  · rw [hg_eq] at hsub_g hsub_g_nd
    rcases AuxTree.nodup_node_unfold hsub_g_nd with ⟨hp_nd, hg_nl, _, hg_nr, _⟩
    rcases AuxTree.nodup_node_unfold hp_nd with ⟨_, hp_nA, _, _, hdisj_Ax⟩
    rcases hsub_g with ⟨_, hl_g, _, _, _, _, _, hsub_p, _⟩
    rcases hsub_p with ⟨_, hl_p, _, _, _, _, _, _, _⟩
    simp only [AuxTree.rootId] at hl_g hl_p
    have hx_nA : x ∉ A.toList := fun h => hdisj_Ax x h (by simp [AuxTree.toList])
    have hl_p_ne : (st.nodes p).left ≠ x := by
      rw [hl_p]; cases A with
      | leaf => exact hx_nz.symm
      | node _ _ _ => exact fun h => hx_nA (h ▸ by simp [AuxTree.toList])
    have hp_nr' : p ∉ D.toList := fun h => by
      have := AuxTree.nodup_node_unfold hsub_g_nd
      exact this.2.2.2.2 p (by simp [AuxTree.toList]) h
    have hx_p_eq : (x == (st.nodes p).left) = false := beq_false_of_ne hl_p_ne.symm
    have hp_g_eq : (p == (st.nodes g).left) = true := beq_iff_eq.mpr hl_g.symm
    have hzig : t.isZigZig x p g = false := by
      cases A with
      | leaf =>
          cases D with
          | leaf => simp [AuxTree.isZigZig, hg_eq]
          | node did _ dr =>
              have hneD : did ≠ p := fun h => hp_nr' (h ▸ by simp [AuxTree.toList])
              cases dr <;> simp [AuxTree.isZigZig, hg_eq, beq_false_of_ne hneD]
      | node aid _ _ =>
          have hneA : aid ≠ x := fun h => hx_nA (h ▸ by simp [AuxTree.toList])
          cases D with
          | leaf => simp [AuxTree.isZigZig, hg_eq, beq_false_of_ne hneA]
          | node did _ dr =>
              have hneD : did ≠ p := fun h => hp_nr' (h ▸ by simp [AuxTree.toList])
              cases dr <;> simp [AuxTree.isZigZig, hg_eq, beq_false_of_ne hneA, beq_false_of_ne hneD]
    rw [hx_p_eq, hp_g_eq, hzig]; rfl
  · rw [hg_eq] at hsub_g hsub_g_nd
    rcases AuxTree.nodup_node_unfold hsub_g_nd with ⟨_, hg_nl, hp_nd, _, hdisj_A_p⟩
    rcases AuxTree.nodup_node_unfold hp_nd with ⟨_, _, _, hp_nD, hdisj_xC_D⟩
    rcases hsub_g with ⟨_, hl_g, _, _, _, _, _, _, hsub_p⟩
    rcases hsub_p with ⟨_, hl_p, _, _, _, _, _, _, _⟩
    simp only [AuxTree.rootId] at hl_g hl_p
    have hp_nA : p ∉ A.toList := fun h => hdisj_A_p p h (by simp [AuxTree.toList])
    have hl_g_ne : (st.nodes g).left ≠ p := by
      rw [hl_g]; cases A with
      | leaf => exact hp_nz.symm
      | node _ _ _ => exact fun h => hp_nA (h ▸ by simp [AuxTree.toList])
    have hx_nD : x ∉ D.toList := fun h => hdisj_xC_D x (by simp [AuxTree.toList]) h
    have hx_p_eq : (x == (st.nodes p).left) = true := beq_iff_eq.mpr hl_p.symm
    have hp_g_eq : (p == (st.nodes g).left) = false := beq_false_of_ne hl_g_ne.symm
    have hzig : t.isZigZig x p g = false := by
      cases A with
      | leaf =>
          cases D with
          | leaf => simp [AuxTree.isZigZig, hg_eq]
          | node did _ _ =>
              have hneD : did ≠ x := fun h => hx_nD (h ▸ by simp [AuxTree.toList])
              simp [AuxTree.isZigZig, hg_eq, beq_false_of_ne hneD]
      | node aid al _ =>
          have hneA : aid ≠ p := fun h => hp_nA (h ▸ by simp [AuxTree.toList])
          cases D with
          | leaf => cases al <;> simp [AuxTree.isZigZig, hg_eq, beq_false_of_ne hneA]
          | node did _ _ =>
              have hneD : did ≠ x := fun h => hx_nD (h ▸ by simp [AuxTree.toList])
              cases al <;> simp [AuxTree.isZigZig, hg_eq, beq_false_of_ne hneA, beq_false_of_ne hneD]
    rw [hx_p_eq, hp_g_eq, hzig]; rfl
  · rw [hg_eq] at hsub_g hsub_g_nd
    rcases AuxTree.nodup_node_unfold hsub_g_nd with ⟨_, _, hp_nd, _, hdisj_A_p⟩
    rcases AuxTree.nodup_node_unfold hp_nd with ⟨hB_nd, _, _, _, hdisj_B_xCD⟩
    rcases hsub_g with ⟨_, hl_g, _, _, _, _, _, _, hsub_p⟩
    rcases hsub_p with ⟨_, hl_p, _, _, _, _, _, _, _⟩
    simp only [AuxTree.rootId] at hl_g hl_p
    have hp_nA : p ∉ A.toList := fun h => hdisj_A_p p h (by simp [AuxTree.toList])
    have hl_g_ne : (st.nodes g).left ≠ p := by
      rw [hl_g]; cases A with
      | leaf => exact hp_nz.symm
      | node _ _ _ => exact fun h => hp_nA (h ▸ by simp [AuxTree.toList])
    have hx_nB : x ∉ B.toList := fun h => hdisj_B_xCD x h (by simp [AuxTree.toList])
    have hl_p_ne : (st.nodes p).left ≠ x := by
      rw [hl_p]; cases B with
      | leaf => exact hx_nz.symm
      | node _ _ _ => exact fun h => hx_nB (h ▸ by simp [AuxTree.toList])
    have hx_p_eq : (x == (st.nodes p).left) = false := beq_false_of_ne hl_p_ne.symm
    have hp_g_eq : (p == (st.nodes g).left) = false := beq_false_of_ne hl_g_ne.symm
    have hzig : t.isZigZig x p g = true := by
      simp [AuxTree.isZigZig, hg_eq]
    rw [hx_p_eq, hp_g_eq, hzig]; rfl

/-- Correctness and potential inequality for one `splayStep` moving `x` toward its root. -/
theorem splayStep_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {t : AuxTree} {x : ℕ}
    (ht : TreeInv P st t) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x, (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag) :
    ∃ t',
      let st' := splayStep P st x
      TreeInv P st' t' ∧
      t'.toList.Perm t.toList ∧
      evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag ∧
      (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar ∧
      (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
      (∀ u ∈ t.toList, (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag) ∧
      (∀ u ∈ t'.pathTo x, u ∈ t.pathTo x) ∧
      (t.depthOf x = 1 →
        t'.rootId = x ∧ t'.depthOf x = 0 ∧
        ∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
          t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize ≤
            t.treePhi vSize + 3 * t'.rank vSize) ∧
      (2 ≤ t.depthOf x →
        t'.depthOf x = t.depthOf x - 2 ∧
        ∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
          t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
            t.treePhi vSize + 3 * (t'.findSubtree x).rank vSize) := by
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
  have hdep_px : t.depthOf p + 1 = t.depthOf x := hpm_x.2.1
  have hp_in_path : p ∈ t.pathTo x := by
    rw [hpm_x.2.2]; exact List.mem_append.mpr (Or.inl (AuxTree.self_mem_pathTo hp_mem))
  by_cases hpr : p = t.rootId
  · have hg0 : g = 0 := by dsimp only [g]; rw [hpr]; exact parentIn_rootId 0
    have hstep_eq : splayStep P st x = rotate P st x := by
      simp [splayStep, hx_nz, hpar_x, hp_nz, hpar_p, hg0]
    have hdep1 : t.depthOf x = 1 := by
      have hp0 : t.depthOf p = 0 := (AuxTree.depthOf_zero_iff_root hp_mem).mpr hpr
      omega
    rcases rotate_preserves hL ht hx hxr hclean with ⟨ht', hperm, hev, hpp, hout, hrt⟩
    refine ⟨t.rotateAt x, ?_⟩
    rw [hstep_eq]
    have hz := fun vSize => AuxTree.zigStep_phi_le vSize ht.nodup hx hxr hpr
    exact ⟨ht', hperm, hev, hpp, hout, hrt,
      AuxTree.rotateAt_pathTo_subset ht.nodup hx (AuxTree.self_mem_pathTo hx),
      fun _ => ⟨(hz 0).1, (hz 0).2.1, fun vSize => ⟨(hz vSize).2.2.1, (hz vSize).2.2.2⟩⟩,
      fun h => absurd hdep1 (by omega)⟩
  · have hpm_p := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hp_mem hpr
    have hg_mem : g ∈ t.toList := hpm_p.1
    have hg_nz : g ≠ 0 := SubtreeInv_nonZero ht.sub hg_mem
    have hdep_gp : t.depthOf g + 1 = t.depthOf p := hpm_p.2.1
    have hdep2 : 2 ≤ t.depthOf x := by omega
    have hzig_eq := isZigZig_eq_state ht hx hxr rfl hp_mem hpr rfl
    have hdouble := AuxTree.doubleStep_phi_le ht.nodup hx hxr rfl hp_mem hpr rfl hg_mem
    have hclean_p : ∀ u ∈ t.pathTo p, (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag := by
      intro u hu
      exact hclean u (by rw [hpm_x.2.2]; exact List.mem_append.mpr (Or.inl hu))
    by_cases hzig : t.isZigZig x p g = true
    · have hflag : ((x == (st.nodes p).left) == (p == (st.nodes g).left)) = true :=
        hzig_eq.trans hzig
      have hstep_eq : splayStep P st x = rotate P (rotate P st p) x := by
        dsimp only [splayStep]
        simp only [hx_nz, ↓reduceIte, hpar_x, hp_nz, hpar_p, hg_nz]
        rw [hflag]; rfl
      have ht'_eq : (if t.isZigZig x p g then (t.rotateAt p).rotateAt x else (t.rotateAt x).rotateAt x) =
          (t.rotateAt p).rotateAt x := by simp [hzig]
      rw [ht'_eq] at hdouble
      rcases rotate_preserves hL ht hp_mem hpr hclean_p with ⟨ht₁, hperm₁, hev₁, hpp₁, hout₁, hrt₁⟩
      let st₁ := rotate P st p
      let t₁ := t.rotateAt p
      have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
      have hxr₁ : x ≠ t₁.rootId := by
        have hcases := AuxTree.grandparent_child_cases ht.nodup hx hxr rfl hp_mem hpr rfl
        have hpx : p ≠ x := fun h => by
          have : t.depthOf p = t.depthOf x := by rw [h]
          omega
        have ht_ne : t ≠ .leaf := fun h => by rw [h] at hx; simp [AuxTree.toList] at hx
        by_cases hgr : g = t.rootId
        · rcases hcases with ⟨A, B, C, D, hg_sub⟩ | ⟨A, B, C, D, hg_sub⟩ |
              ⟨A, B, C, D, hg_sub⟩ | ⟨A, B, C, D, hg_sub⟩
          · have htg : t = AuxTree.node g (.node p (.node x A B) C) D := by
              rw [← AuxTree.findSubtree_root ht_ne, ← hgr]
              exact hg_sub
            have hg_ne_p : g ≠ p := fun h => by
              have : t.depthOf g = t.depthOf p := by rw [h]
              omega
            have hrot1 : t₁ = AuxTree.node p (.node x A B) (.node g C D) := by
              dsimp only [t₁]; rw [htg]; exact AuxTree.rotateAt_zigRight (.node x A B) C D hg_ne_p
            rw [hrot1]; simp [AuxTree.rootId, hpx.symm]
          · exfalso
            have hsub_g := SubtreeInv_findSubtree ht.nodup ht.sub hg_mem
            rw [hg_sub] at hsub_g
            have hsub_g_nd : (t.findSubtree g).toList.Nodup := AuxTree.findSubtree_nodup ht.nodup
            rw [hg_sub] at hsub_g_nd
            rcases AuxTree.nodup_node_unfold hsub_g_nd with ⟨hp_nd, _, _, _, _⟩
            rcases AuxTree.nodup_node_unfold hp_nd with ⟨_, _, _, _, hdisj_Ax⟩
            rcases hsub_g with ⟨_, hl_g, _, _, _, _, _, hsub_p, _⟩
            rcases hsub_p with ⟨_, hl_p, _, _, _, _, _, _, _⟩
            simp only [AuxTree.rootId] at hl_g hl_p
            have hx_nA : x ∉ A.toList := fun h => hdisj_Ax x h (by simp [AuxTree.toList])
            have h1 : (st.nodes p).left ≠ x := by
              rw [hl_p]; cases A with
              | leaf => exact hx_nz.symm
              | node _ _ _ => exact fun h => hx_nA (h ▸ by simp [AuxTree.toList])
            have hbx : (x == (st.nodes p).left) = false := beq_false_of_ne h1.symm
            have hbp : (p == (st.nodes g).left) = true := beq_iff_eq.mpr hl_g.symm
            have hzf := hzig_eq.trans hzig
            rw [hbx, hbp] at hzf
            exact Bool.false_ne_true hzf
          · exfalso
            have hsub_g := SubtreeInv_findSubtree ht.nodup ht.sub hg_mem
            rw [hg_sub] at hsub_g
            have hsub_g_nd : (t.findSubtree g).toList.Nodup := AuxTree.findSubtree_nodup ht.nodup
            rw [hg_sub] at hsub_g_nd
            rcases AuxTree.nodup_node_unfold hsub_g_nd with ⟨_, _, _, _, hdisj_Ap⟩
            rcases hsub_g with ⟨_, hl_g, _, _, _, _, _, _, hsub_p⟩
            rcases hsub_p with ⟨_, hl_p, _, _, _, _, _, _, _⟩
            simp only [AuxTree.rootId] at hl_g hl_p
            have hp_nA : p ∉ A.toList := fun h => hdisj_Ap p h (by dsimp only [p]; simp [AuxTree.toList])
            have h1 : (st.nodes g).left ≠ p := by
              rw [hl_g]; cases A with
              | leaf => exact hp_nz.symm
              | node _ _ _ => exact fun h => hp_nA (h ▸ by simp [AuxTree.toList])
            have hbx : (x == (st.nodes p).left) = true := beq_iff_eq.mpr hl_p.symm
            have hbp : (p == (st.nodes g).left) = false := beq_false_of_ne h1.symm
            have hzf := hzig_eq.trans hzig
            rw [hbx, hbp] at hzf
            exact Bool.false_ne_true hzf
          · have htg : t = AuxTree.node g A (.node p B (.node x C D)) := by
              rw [← AuxTree.findSubtree_root ht_ne, ← hgr]
              exact hg_sub
            have hg_ne_p : g ≠ p := fun h => by
              have : t.depthOf g = t.depthOf p := by rw [h]
              omega
            have hp_nA : p ∉ A.toList := by
              have hnd' := ht.nodup; rw [htg] at hnd'
              exact fun h => (AuxTree.nodup_node_unfold hnd').2.2.2.2 p h (by simp [AuxTree.toList])
            have hA_nr : ¬ A.hasRoot p := fun h => by
              obtain ⟨X, Y, rfl⟩ := AuxTree.hasRoot_iff.mp h; exact hp_nA (by simp [AuxTree.toList])
            have hrot1 : t₁ = AuxTree.node p (.node g A B) (.node x C D) := by
              dsimp only [t₁]; rw [htg]; exact AuxTree.rotateAt_zigLeft A B (.node x C D) hg_ne_p hA_nr
            rw [hrot1]; simp [AuxTree.rootId, hpx.symm]
        · have hrep_t₁ : t₁ = t.replaceSubtree g ((t.findSubtree g).rotateAt p) :=
            (AuxTree.replaceSubtree_rotateAt (x := p) (p₀ := 0) ht.nodup hp_mem hpr).symm
          have hne_leaf : (t.findSubtree g).rotateAt p ≠ .leaf := by
            refine AuxTree.rotateAt_ne_leaf ?_
            intro h; obtain ⟨gl, gr, hglr⟩ := AuxTree.findSubtree_root_of_mem hg_mem
            rw [hglr] at h; cases h
          have hrt_t₁ : t₁.rootId = t.rootId := by
            rw [hrep_t₁, AuxTree.replaceSubtree_rootId ht_ne hne_leaf]
            simp only [ite_eq_right_iff]
            exact fun h => absurd h.symm hgr
          rwa [hrt_t₁]
      have hclean₁ : ∀ u ∈ t₁.pathTo x, (st₁.nodes u).rev = false ∧ (st₁.nodes u).tag = P.idTag := by
        intro u hu
        have hu' : u ∈ t.pathTo x := AuxTree.rotateAt_pathTo_subset ht.nodup hx hp_in_path u hu
        rw [(hrt₁ u (AuxTree.mem_pathTo hu')).1, (hrt₁ u (AuxTree.mem_pathTo hu')).2]
        exact hclean u hu'
      rcases rotate_preserves hL ht₁ hx₁ hxr₁ hclean₁ with ⟨ht₂, hperm₂, hev₂, hpp₂, hout₂, hrt₂⟩
      refine ⟨t₁.rotateAt x, ?_⟩
      rw [hstep_eq]
      refine ⟨ht₂, hperm₂.trans hperm₁, hev₂.trans hev₁, hpp₂.trans hpp₁, ?_, ?_, hdouble.2.2.2.1,
        fun h => absurd h (by omega), fun _ => ⟨hdouble.2.1, fun vSize => (hdouble.2.2.2.2.2 vSize)⟩⟩
      · intro u hu
        exact (hout₂ u (fun hm => hu (hperm₁.mem_iff.mp hm))).trans (hout₁ u hu)
      · intro u hu
        have h2 := hrt₂ u (hperm₁.mem_iff.mpr hu)
        have h1 := hrt₁ u hu
        exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    · have hzig_f : t.isZigZig x p g = false := Bool.eq_false_iff.mpr hzig
      have hflag : ((x == (st.nodes p).left) == (p == (st.nodes g).left)) = false :=
        hzig_eq.trans hzig_f
      have hstep_eq : splayStep P st x = rotate P (rotate P st x) x := by
        dsimp only [splayStep]
        simp only [hx_nz, ↓reduceIte, hpar_x, hp_nz, hpar_p, hg_nz]
        rw [hflag]; rfl
      have ht'_eq : (if t.isZigZig x p g then (t.rotateAt p).rotateAt x else (t.rotateAt x).rotateAt x) =
          (t.rotateAt x).rotateAt x := by simp [hzig_f]
      rw [ht'_eq] at hdouble
      rcases rotate_preserves hL ht hx hxr hclean with ⟨ht₁, hperm₁, hev₁, hpp₁, hout₁, hrt₁⟩
      let st₁ := rotate P st x
      let t₁ := t.rotateAt x
      have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
      have hdep₁ : t₁.depthOf x = t.depthOf x - 1 := AuxTree.rotateAt_depthOf_self ht.nodup hx
      have hxr₁ : x ≠ t₁.rootId := by
        intro heq
        have hd0 : t₁.depthOf x = 0 := (AuxTree.depthOf_zero_iff_root hx₁).mpr heq
        omega
      have hclean₁ : ∀ u ∈ t₁.pathTo x, (st₁.nodes u).rev = false ∧ (st₁.nodes u).tag = P.idTag := by
        intro u hu
        have hu' : u ∈ t.pathTo x :=
          AuxTree.rotateAt_pathTo_subset ht.nodup hx (AuxTree.self_mem_pathTo hx) u hu
        rw [(hrt₁ u (AuxTree.mem_pathTo hu')).1, (hrt₁ u (AuxTree.mem_pathTo hu')).2]
        exact hclean u hu'
      rcases rotate_preserves hL ht₁ hx₁ hxr₁ hclean₁ with ⟨ht₂, hperm₂, hev₂, hpp₂, hout₂, hrt₂⟩
      refine ⟨t₁.rotateAt x, ?_⟩
      rw [hstep_eq]
      refine ⟨ht₂, hperm₂.trans hperm₁, hev₂.trans hev₁, hpp₂.trans hpp₁, ?_, ?_, hdouble.2.2.2.1,
        fun h => absurd h (by omega), fun _ => ⟨hdouble.2.1, fun vSize => (hdouble.2.2.2.2.2 vSize)⟩⟩
      · intro u hu
        exact (hout₂ u (fun hm => hu (hperm₁.mem_iff.mp hm))).trans (hout₁ u hu)
      · intro u hu
        have h2 := hrt₂ u (hperm₁.mem_iff.mpr hu)
        have h1 := hrt₁ u hu
        exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-! ### `splayLoop` and `splay` preservation and amortized bounds -/

/-- Correctness and Sleator–Tarjan potential inequality for `splayLoop`. -/
theorem splayLoop_preserves {P : LctPayload α σ τ} (hL : P.Laws) :
    ∀ {fuel : ℕ} {st : SplayState α σ τ} {t : AuxTree} {x : ℕ},
      TreeInv P st t → x ∈ t.toList →
      t.depthOf x / 2 + t.depthOf x % 2 ≤ fuel →
      (∀ u ∈ t.pathTo x, (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag) →
      ∃ t',
        let st' := splayLoop P st fuel x
        TreeInv P st' t' ∧
        t'.rootId = x ∧
        t'.toList.Perm t.toList ∧
        evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag ∧
        (st'.nodes t'.rootId).ppar = (st.nodes t.rootId).ppar ∧
        (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
        (∀ u ∈ t.toList, (st'.nodes u).rev = (st.nodes u).rev ∧ (st'.nodes u).tag = (st.nodes u).tag) ∧
        (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
          t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + t.depthOf x / 2 ≤
            t.treePhi vSize + 3 * t'.rank vSize) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st t x ht hx hfuel _
      have hd0 : t.depthOf x = 0 := by omega
      have hxr : x = t.rootId := (AuxTree.depthOf_zero_iff_root hx).mp hd0
      have ht_ne : t ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hx
      refine ⟨t, ht, hxr.symm, List.Perm.refl _, rfl, rfl, fun _ _ => rfl,
        fun _ _ => ⟨rfl, rfl⟩, fun vSize => ⟨rfl, ?_⟩⟩
      rw [hd0, hxr, AuxTree.findSubtree_root ht_ne]
      simp
  | succ k ih =>
      intro st t x ht hx hfuel hclean
      have hx_nz : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
      have hpar_eq : (st.nodes x).par = t.parentIn x 0 :=
        SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
      by_cases hxr : x = t.rootId
      · have hpar0 : (st.nodes x).par = 0 := by
          rw [hpar_eq]
          cases t with
          | leaf => simp [AuxTree.toList] at hx
          | node rid _ _ => simp only [AuxTree.rootId] at hxr; subst hxr; simp [AuxTree.parentIn]
        have hd0 : t.depthOf x = 0 := (AuxTree.depthOf_zero_iff_root hx).mpr hxr
        have ht_ne : t ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hx
        have hst'_eq : splayLoop P st (k + 1) x = st := by simp [splayLoop, hx_nz, hpar0]
        refine ⟨t, ?_⟩
        rw [hst'_eq]
        refine ⟨ht, hxr.symm, List.Perm.refl _, rfl, rfl, fun _ _ => rfl,
          fun _ _ => ⟨rfl, rfl⟩, fun vSize => ⟨rfl, ?_⟩⟩
        rw [hd0, hxr, AuxTree.findSubtree_root ht_ne]
        simp
      · have hpm := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hxr
        have hp_nz : (st.nodes x).par ≠ 0 := hpar_eq ▸ SubtreeInv_nonZero ht.sub hpm.1
        have hst'_eq : splayLoop P st (k + 1) x = splayLoop P (splayStep P st x) k x := by
          simp [splayLoop, hx_nz, hp_nz]
        rcases splayStep_preserves hL ht hx hxr hclean with
          ⟨t₁, ht₁, hperm₁, hev₁, hpp₁, hout₁, hrt₁, hpath₁, hzig₁, hdbl₁⟩
        let st₁ := splayStep P st x
        have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
        have hclean₁ : ∀ u ∈ t₁.pathTo x, (st₁.nodes u).rev = false ∧ (st₁.nodes u).tag = P.idTag := by
          intro u hu
          have hu' : u ∈ t.pathTo x := hpath₁ u hu
          rw [(hrt₁ u (AuxTree.mem_pathTo hu')).1, (hrt₁ u (AuxTree.mem_pathTo hu')).2]
          exact hclean u hu'
        have hdep_nz : t.depthOf x ≠ 0 := fun h0 =>
          hxr ((AuxTree.depthOf_zero_iff_root hx).mp h0)
        by_cases hdep1 : t.depthOf x = 1
        · rcases hzig₁ hdep1 with ⟨hr₁, hd₁, hphi₁⟩
          have hfuel₁ : t₁.depthOf x / 2 + t₁.depthOf x % 2 ≤ k := by rw [hd₁]; omega
          rcases ih ht₁ hx₁ hfuel₁ hclean₁ with
            ⟨t', ht', hr', hperm', hev', hpp', hout', hrt', hphi'⟩
          refine ⟨t', ?_⟩
          rw [hst'_eq]
          refine ⟨ht', hr', hperm'.trans hperm₁, hev'.trans hev₁, hpp'.trans hpp₁, ?_, ?_, fun vSize => ?_⟩
          · intro u hu
            exact (hout' u (fun hm => hu (hperm₁.mem_iff.mp hm))).trans (hout₁ u hu)
          · intro u hu
            have h2 := hrt' u (hperm₁.mem_iff.mpr hu)
            have h1 := hrt₁ u hu
            exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
          · rcases hphi₁ vSize with ⟨hsz₁, hp₁⟩
            rcases hphi' vSize with ⟨hsz', hp'⟩
            have ht₁_ne : t₁ ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hx₁
            have hfsub : (t₁.findSubtree x).rank vSize = t₁.rank vSize := by
              rw [← hr₁, AuxTree.findSubtree_root ht₁_ne]
            rw [hfsub] at hp'
            refine ⟨hsz'.trans hsz₁, ?_⟩
            rw [hdep1]; omega
        · have hdep2 : 2 ≤ t.depthOf x := by omega
          rcases hdbl₁ hdep2 with ⟨hd₁, hphi₁⟩
          have hfuel₁ : t₁.depthOf x / 2 + t₁.depthOf x % 2 ≤ k := by rw [hd₁]; omega
          rcases ih ht₁ hx₁ hfuel₁ hclean₁ with
            ⟨t', ht', hr', hperm', hev', hpp', hout', hrt', hphi'⟩
          refine ⟨t', ?_⟩
          rw [hst'_eq]
          refine ⟨ht', hr', hperm'.trans hperm₁, hev'.trans hev₁, hpp'.trans hpp₁, ?_, ?_, fun vSize => ?_⟩
          · intro u hu
            exact (hout' u (fun hm => hu (hperm₁.mem_iff.mp hm))).trans (hout₁ u hu)
          · intro u hu
            have h2 := hrt' u (hperm₁.mem_iff.mpr hu)
            have h1 := hrt₁ u hu
            exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
          · rcases hphi₁ vSize with ⟨hsz₁, hp₁⟩
            rcases hphi' vSize with ⟨hsz', hp'⟩
            refine ⟨hsz'.trans hsz₁, ?_⟩
            rw [hd₁] at hp'
            have hhalf : 1 + (t.depthOf x - 2) / 2 = t.depthOf x / 2 := by omega
            omega

/-- Full correctness and Sleator–Tarjan potential inequality for `splay P st fuel x`
when `x ∈ t.toList` and `t.depthOf x < fuel` (for instance `fuel = t.countNodes`). -/
theorem splay_preserves_and_phi {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {t : AuxTree} {fuel x : ℕ}
    (ht : TreeInv P st t) (hx : x ∈ t.toList) (hfuel : t.depthOf x < fuel) :
    ∃ t',
      let st' := splay P st fuel x
      TreeInv P st' t' ∧
      t' ≠ .leaf ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag ∧
      (st'.nodes x).ppar = (st.nodes t.rootId).ppar ∧
      (st'.nodes x).rev = false ∧
      (st'.nodes x).tag = P.idTag ∧
      (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + t.depthOf x / 2 ≤
          t.treePhi vSize + 3 * t'.rank vSize) := by
  have hx_nz : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
  rcases pushPath_preserves hL ht hx hfuel with
    ⟨t₁, ht₁, hperm₁, hroot₁, hdep₁, _, hsz₁, hclean₁, hpp₁, hout₁, hev₁⟩
  let st₁ := pushPath P st fuel x
  have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
  have hfuel₁ : t₁.depthOf x / 2 + t₁.depthOf x % 2 ≤ fuel := by
    rw [hdep₁ x]; omega
  rcases splayLoop_preserves hL ht₁ hx₁ hfuel₁ hclean₁ with
    ⟨t', ht', hr', hperm', hev', hpp', hout', hrt', hphi'⟩
  have hst'_eq : splay P st fuel x = splayLoop P st₁ fuel x := by
    simp [splay, hx_nz, st₁]
  refine ⟨t', ?_⟩
  rw [hst'_eq]
  have ht'_ne : t' ≠ .leaf := fun h => by
    rw [h] at hperm'
    exact absurd (hperm'.symm.mem_iff.mp hx₁) (by simp [AuxTree.toList])
  have hx_path₁ : x ∈ t₁.pathTo x := AuxTree.self_mem_pathTo hx₁
  have hx_rt := hrt' x hx₁
  have hx_cl := hclean₁ x hx_path₁
  have hpp_x' : ((splayLoop P st₁ fuel x).nodes x).ppar = (st.nodes t.rootId).ppar := by
    have hpp_mid : (st₁.nodes t₁.rootId).ppar = (st.nodes t.rootId).ppar := hpp₁
    calc
      ((splayLoop P st₁ fuel x).nodes x).ppar
        = ((splayLoop P st₁ fuel x).nodes t'.rootId).ppar := by rw [hr']
      _ = (st₁.nodes t₁.rootId).ppar := hpp'
      _ = (st.nodes t.rootId).ppar := hpp_mid
  refine ⟨ht', ht'_ne, hr', hperm'.trans hperm₁, hev'.trans hev₁,
    hpp_x', hx_rt.1.trans hx_cl.1, hx_rt.2.trans hx_cl.2, ?_, fun vSize => ?_⟩
  · intro u hu
    exact (hout' u (fun hm => hu (hperm₁.mem_iff.mp hm))).trans (hout₁ u hu)
  · rcases hsz₁ vSize with ⟨a_sz, a_phi, a_sub⟩
    rcases hphi' vSize with ⟨b_sz, b_phi⟩
    have hrank_eq : (t₁.findSubtree x).rank vSize = (t.findSubtree x).rank vSize := by
      simp only [AuxTree.rank, a_sub x]
    rw [hrank_eq, a_phi, hdep₁ x] at b_phi
    exact ⟨b_sz.trans a_sz, b_phi⟩

end SplayState

end MinCostFlow.LinkCut
