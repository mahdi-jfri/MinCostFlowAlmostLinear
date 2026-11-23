module

public import MinCostFlow.LinkCut.SplayOps
import Mathlib.Tactic

/-!
# Leftmost queries and root splice operations on `SplayState`

This file proves preservation and potential bounds for:
- `pull_*_eq` accessors (fields unchanged by `pull`)
- `setPpar_root_preserves` (updating `ppar` at the root of an auxiliary tree)
- `leftmostWalk` (`leftmostWalk_sub_preserves`) and `findLeftmost` (`findLeftmost_preserves_and_phi`)
- Root splice primitives: `makeSingleton`, `detachRight`, `attachRight`, and `detachRootChildren`

All results hold for any payload `P : LctPayload α σ τ` satisfying `P.Laws`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

namespace SplayState

variable {α σ τ : Type*}

/-! ### Fields unchanged by `pull` and `setPpar` on a root -/

theorem pull_val_eq' (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).val = (st.nodes u).val := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

theorem pull_left_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).left = (st.nodes u).left := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

theorem pull_right_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).right = (st.nodes u).right := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

theorem pull_par_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).par = (st.nodes u).par := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

theorem pull_ppar_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).ppar = (st.nodes u).ppar := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

theorem pull_rev_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).rev = (st.nodes u).rev := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

theorem pull_tag_eq (P : LctPayload α σ τ) (st : SplayState α σ τ) (x u : ℕ) :
    ((pull P st x).nodes u).tag = (st.nodes u).tag := by
  by_cases h1 : x = 0 <;> by_cases h2 : u = x <;> simp [pull, h1, h2]

/-- Updating `ppar` at the root `t.rootId` preserves `TreeInv` and `evalPairs`. -/
theorem setPpar_root_preserves (P : LctPayload α σ τ)
    {st : SplayState α σ τ} {t : AuxTree} {pp : ℕ}
    (ht : TreeInv P st t) (hne : t ≠ .leaf) :
    let st' := st.setPpar t.rootId pp
    TreeInv P st' t ∧
    evalPairs P st' t false P.idTag = evalPairs P st t false P.idTag ∧
    (st'.nodes t.rootId).ppar = pp ∧
    (∀ u ≠ t.rootId, st'.nodes u = st.nodes u) := by
  cases t with
  | leaf => exact absurd rfl hne
  | node rid l r =>
      rcases AuxTree.nodup_node_unfold ht.nodup with ⟨_, hnl, _, hnr, _⟩
      rcases ht.sub with ⟨hrid, hl_eq, hr_eq, hpar, _, hsz, hsum, hl, hr⟩
      intro st'
      have hst'_def : st' = st.setPpar rid pp := rfl
      have hrid_eq : st'.nodes rid = { st.nodes rid with ppar := pp } := by
        simp [hst'_def, setPpar]
      have hst'_ne : ∀ u ≠ rid, st'.nodes u = st.nodes u := fun u hu => by
        simp [hst'_def, setPpar, hu]
      have hl' : SubtreeInv P st' rid l :=
        SubtreeInv_agree hl (fun u hu => (hst'_ne u (fun h => hnl (h ▸ hu))).symm)
      have hr' : SubtreeInv P st' rid r :=
        SubtreeInv_agree hr (fun u hu => (hst'_ne u (fun h => hnr (h ▸ hu))).symm)
      have hev : evalPairs P st' (.node rid l r) false P.idTag =
          evalPairs P st (.node rid l r) false P.idTag := by
        refine evalPairs_agree_vrt P (fun u _ => ?_) false P.idTag
        by_cases hur : u = rid
        · subst hur; simp [hrid_eq]
        · rw [hst'_ne u hur]; exact ⟨rfl, rfl, rfl⟩
      refine ⟨⟨ht.nodup, ⟨hrid, ?_, ?_, ?_, fun h => absurd rfl h, ?_, ?_, hl', hr'⟩⟩,
        hev, ?_, hst'_ne⟩
      · simpa [hrid_eq] using hl_eq
      · simpa [hrid_eq] using hr_eq
      · simp [hrid_eq, hpar]
      · simpa [hrid_eq] using hsz
      · rw [hev]; simp [hrid_eq, hsum]
      · simp [AuxTree.rootId, hrid_eq]

/-! ### `leftmostWalk` and `findLeftmost` -/

private theorem nodup_node_intro {x : ℕ} {l r : AuxTree}
    (hl : l.toList.Nodup) (hxl : x ∉ l.toList)
    (hr : r.toList.Nodup) (hxr : x ∉ r.toList)
    (hdisj : ∀ a ∈ l.toList, a ∉ r.toList) :
    (AuxTree.node x l r).toList.Nodup := by
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hl, List.nodup_singleton x, ?_⟩, hr, ?_⟩
  · intro a ha b hb h; simp only [List.mem_singleton] at hb; subst hb; subst h; exact hxl ha
  · intro a ha b hb h
    subst h
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with hal | rfl
    · exact hdisj a hal hb
    · exact hxr hb

private theorem head?_evalPairs_of_left_leaf {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {x : ℕ} {r : AuxTree}
    (hrev : (st.nodes x).rev = false) (htag : (st.nodes x).tag = P.idTag) :
    (evalPairs P st (.node x .leaf r) false P.idTag).head? = some (x, (st.nodes x).val) := by
  simp [evalPairs, hrev, htag, hL.compTag_id_left, hL.actVal_id]

private theorem evalPairs_head_fst_of_left_ne {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {x : ℕ} {l r : AuxTree}
    (hrev : (st.nodes x).rev = false) (htag : (st.nodes x).tag = P.idTag)
    (hl : l ≠ .leaf) :
    (evalPairs P st (.node x l r) false P.idTag).head? =
      (evalPairs P st l false P.idTag).head? := by
  have hlen : (evalPairs P st l false P.idTag).length = l.countNodes := evalPairs_length P st l false P.idTag
  have hpos : 0 < (evalPairs P st l false P.idTag).length := by
    rw [hlen]; cases l with | leaf => exact absurd rfl hl | node _ _ _ => simp [AuxTree.countNodes]
  have hne : evalPairs P st l false P.idTag ≠ [] := List.ne_nil_of_length_pos hpos
  simp [evalPairs, hrev, htag, hL.compTag_id_left, List.head?_append_of_ne_nil _ hne]

private theorem pushDown_leftmost_findSubtree_treeSize
    (st : SplayState α σ τ) (x : ℕ) (l₀ r₀ l₁ r₁ : AuxTree)
    (hrev_flag : l₁ = (if (st.nodes x).rev then l₀.revRoot else l₀) ∧
      r₁ = (if (st.nodes x).rev then r₀.revRoot else r₀))
    (hnd : (AuxTree.node x l₀ r₀).toList.Nodup) (vSize : ℕ → ℕ) (y : ℕ) :
    ((AuxTree.node x l₁ r₁).findSubtree y).treeSize vSize =
      ((AuxTree.node x l₀ r₀).findSubtree y).treeSize vSize := by
  rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, _⟩
  by_cases hxy : x = y
  · subst hxy
    simp only [AuxTree.findSubtree, ↓reduceIte, AuxTree.treeSize]
    by_cases hrev : (st.nodes x).rev = true
    · simp [hrev_flag.1, hrev_flag.2, hrev, revRoot_treeSize]
    · simp [hrev_flag.1, hrev_flag.2, hrev]
  · have hl_perm : l₁.toList.Perm l₀.toList := by
      by_cases hrev : (st.nodes x).rev = true
      · simp [hrev_flag.1, hrev, revRoot_toList_perm]
      · simp [hrev_flag.1, hrev]
    simp only [AuxTree.findSubtree, hxy, ↓reduceIte, hl_perm.mem_iff]
    by_cases hyl : y ∈ l₀.toList
    · simp only [hyl, ↓reduceIte]
      by_cases hrev : (st.nodes x).rev = true
      · simp [hrev_flag.1, hrev, revRoot_findSubtree_treeSize hl_nd]
      · simp [hrev_flag.1, hrev]
    · simp only [hyl, ↓reduceIte]
      by_cases hrev : (st.nodes x).rev = true
      · simp [hrev_flag.2, hrev, revRoot_findSubtree_treeSize hr_nd]
      · simp [hrev_flag.2, hrev]

/-- Specification for `leftmostWalk P st fuel x` starting at root `x` of a nonempty subtree `sub`:
walks down pushed-left pointers, reaching the logical leftmost node `r` with `(st'.nodes r).left = 0`,
preserving `evalPairs` and all virtual `treeSize`/`treePhi`. -/
theorem leftmostWalk_sub_preserves {P : LctPayload α σ τ} (hL : P.Laws) :
    ∀ {fuel rp : ℕ} {st : SplayState α σ τ} {sub : AuxTree} {x : ℕ},
      sub.toList.Nodup → SubtreeInv P st rp sub → sub ≠ .leaf → sub.rootId = x →
      sub.countNodes ≤ fuel →
      ∃ sub',
        let (st', r) := leftmostWalk P st fuel x
        SubtreeInv P st' rp sub' ∧
        sub' ≠ .leaf ∧
        sub'.rootId = x ∧
        sub'.toList.Perm sub.toList ∧
        r ∈ sub'.toList ∧
        (st'.nodes r).left = 0 ∧
        (evalPairs P st' sub' false P.idTag).head? = some (r, (st'.nodes r).val) ∧
        (∀ flip acc, evalPairs P st' sub' flip acc = evalPairs P st sub flip acc) ∧
        (st'.nodes sub'.rootId).ppar = (st.nodes sub.rootId).ppar ∧
        (∀ u ∉ sub.toList, st'.nodes u = st.nodes u) ∧
        sub'.depthOf r < sub.countNodes ∧
        (∀ vSize, sub'.treeSize vSize = sub.treeSize vSize ∧
          sub'.treePhi vSize = sub.treePhi vSize ∧
          ∀ y, (sub'.findSubtree y).treeSize vSize = (sub.findSubtree y).treeSize vSize) := by
  intro fuel
  induction fuel with
  | zero =>
      intro rp st sub x _ _ hne _ hle
      cases sub with
      | leaf => exact absurd rfl hne
      | node _ _ _ => simp [AuxTree.countNodes] at hle
  | succ k ih =>
      intro rp st sub x hnd hsub hne hroot hle
      cases sub with
      | leaf => exact absurd rfl hne
      | node rid l₀ r₀ =>
          simp only [AuxTree.rootId] at hroot; subst hroot
          have hnz : rid ≠ 0 := hsub.1
          let l₁ := if (st.nodes rid).rev then l₀.revRoot else l₀
          let r₁ := if (st.nodes rid).rev then r₀.revRoot else r₀
          let st₁ := pushDown P st rid
          have hpd := pushDown_root_preserves hL hnd hsub
          have hsub₁ : SubtreeInv P st₁ rp (.node rid l₁ r₁) := hpd.1
          have hrev₁ : (st₁.nodes rid).rev = false := hpd.2.1
          have htag₁ : (st₁.nodes rid).tag = P.idTag := hpd.2.2.1
          have hpp₁ : (st₁.nodes rid).ppar = (st.nodes rid).ppar := hpd.2.2.2.1
          have hev₁ : ∀ flip acc, evalPairs P st₁ (.node rid l₁ r₁) flip acc =
              evalPairs P st (.node rid l₀ r₀) flip acc := hpd.2.2.2.2.1
          have hout₁ : ∀ u ∉ (AuxTree.node rid l₀ r₀).toList, st₁.nodes u = st.nodes u := hpd.2.2.2.2.2
          have hl₁_perm : l₁.toList.Perm l₀.toList := by
            by_cases hrev : (st.nodes rid).rev = true <;>
              simp [l₁, hrev, revRoot_toList_perm]
          have hr₁_perm : r₁.toList.Perm r₀.toList := by
            by_cases hrev : (st.nodes rid).rev = true <;>
              simp [r₁, hrev, revRoot_toList_perm]
          have hnd₁ : (AuxTree.node rid l₁ r₁).toList.Nodup := by
            have hp : (AuxTree.node rid l₁ r₁).toList.Perm (AuxTree.node rid l₀ r₀).toList := by
              simp only [AuxTree.toList]
              exact (hl₁_perm.append_right [rid]).append hr₁_perm
            exact hp.nodup_iff.mpr hnd
          rcases AuxTree.nodup_node_unfold hnd₁ with ⟨hl₁_nd, hrid_nl₁, hr₁_nd, hrid_nr₁, hdisj₁⟩
          rcases hsub₁ with ⟨hrid₁_nz, hleft_eq, hright_eq, hpar₁, hpp₁', hsz₁, hsum₁, hsub_l₁, hsub_r₁⟩
          by_cases hl_leaf : l₁ = .leaf
          · have hl0 : (st₁.nodes rid).left = 0 := by
              rw [hleft_eq, hl_leaf, AuxTree.rootId]
            have hwalk_eq : leftmostWalk P st (k + 1) rid = (st₁, rid) := by
              simp [leftmostWalk, hnz, st₁, hl0]
            refine ⟨.node rid .leaf r₁, ?_⟩
            simp only [hwalk_eq]
            have hsub_leaf : SubtreeInv P st₁ rp (.node rid .leaf r₁) := by
              have hleft_leaf : (st₁.nodes rid).left = AuxTree.leaf.rootId := hl0
              have hsz_leaf : (st₁.nodes rid).sz = (AuxTree.node rid .leaf r₁).countNodes := by
                simpa [AuxTree.countNodes, hl_leaf] using hsz₁
              have hsum_leaf : (st₁.nodes rid).sum =
                  P.listSummary (evalPairs P st₁ (.node rid .leaf r₁) false P.idTag) := by
                simpa [hl_leaf] using hsum₁
              exact ⟨hrid₁_nz, hleft_leaf, hright_eq, hpar₁, hpp₁', hsz_leaf, hsum_leaf,
                trivial, hsub_r₁⟩
            have hev_leaf : ∀ flip acc,
                evalPairs P st₁ (.node rid .leaf r₁) flip acc =
                  evalPairs P st (.node rid l₀ r₀) flip acc := fun flip acc => by
              simpa [hl_leaf] using hev₁ flip acc
            have hperm_leaf : (AuxTree.node rid .leaf r₁).toList.Perm
                (AuxTree.node rid l₀ r₀).toList := by
              have hp : (AuxTree.node rid l₁ r₁).toList.Perm (AuxTree.node rid l₀ r₀).toList := by
                simp only [AuxTree.toList]
                exact (hl₁_perm.append_right [rid]).append hr₁_perm
              simpa [hl_leaf] using hp
            have hhead : (evalPairs P st₁ (.node rid .leaf r₁) false P.idTag).head? =
                some (rid, (st₁.nodes rid).val) :=
              head?_evalPairs_of_left_leaf hL hrev₁ htag₁
            refine ⟨hsub_leaf, by simp, rfl, hperm_leaf, by simp [AuxTree.toList], hl0, hhead,
              hev_leaf, hpp₁, hout₁, by simp [AuxTree.depthOf, AuxTree.countNodes], fun vSize => ?_⟩
            · have hl0_eq : l₀ = .leaf := by
                cases l₀ with
                | leaf => rfl
                | node _ _ _ => by_cases hrev : (st.nodes rid).rev = true <;>
                    simp [l₁, hrev, AuxTree.revRoot] at hl_leaf
              refine ⟨?_, ?_, fun y => ?_⟩
              · by_cases hrev : (st.nodes rid).rev = true <;>
                  simp [hl0_eq, r₁, hrev, AuxTree.treeSize, revRoot_treeSize]
              · by_cases hrev : (st.nodes rid).rev = true
                · have hrs : r₁.treeSize vSize = r₀.treeSize vSize := by
                    simp [r₁, hrev, revRoot_treeSize]
                  have hrp : r₁.treePhi vSize = r₀.treePhi vSize := by
                    simp [r₁, hrev, revRoot_treePhi]
                  simp only [hl0_eq, AuxTree.treePhi, AuxTree.rank, AuxTree.treeSize, hrs, hrp]
                · simp [hl0_eq, r₁, hrev]
              · subst hl0_eq
                by_cases hrev : (st.nodes rid).rev = true
                · exact pushDown_leftmost_findSubtree_treeSize st rid .leaf r₀ .leaf r₁
                    ⟨by simp [hrev, AuxTree.revRoot], by simp [r₁, hrev]⟩ hnd vSize y
                · exact pushDown_leftmost_findSubtree_treeSize st rid .leaf r₀ .leaf r₁
                    ⟨by simp [hrev], by simp [r₁, hrev]⟩ hnd vSize y
          · have hleft_nz : l₁.rootId ≠ 0 := by
              cases h : l₁ with
              | leaf => exact absurd h hl_leaf
              | node lid _ _ => rw [h] at hsub_l₁; exact hsub_l₁.1
            have hl₁_len : l₁.countNodes = l₀.countNodes := by
              by_cases hrev : (st.nodes rid).rev = true <;>
                simp [l₁, hrev, revRoot_countNodes]
            have hle_k : l₁.countNodes ≤ k := by
              rw [hl₁_len]
              simp only [AuxTree.countNodes] at hle
              omega
            rcases ih hl₁_nd hsub_l₁ hl_leaf rfl hle_k with ih_res
            rcases ih_res with ⟨l', hl'_sub, hl'_ne, hl'_root, hl'_perm, hr_mem, hr_left, hr_head,
              hl'_hev, _, hl'_out, hr_dep, hl'_sz⟩
            let st' := (leftmostWalk P st₁ k l₁.rootId).1
            let r := (leftmostWalk P st₁ k l₁.rootId).2
            change SubtreeInv P st' rid l' at hl'_sub
            have hwalk_eq : leftmostWalk P st (k + 1) rid = (st', r) := by
              simp [leftmostWalk, hnz, st₁, hleft_eq, hleft_nz, st', r]
            refine ⟨.node rid l' r₁, ?_⟩
            simp only [hwalk_eq]
            have hx_nin : rid ∉ l₁.toList := hrid_nl₁
            have hx_eq : st'.nodes rid = st₁.nodes rid := hl'_out rid hx_nin
            have hr₁_out : ∀ u ∈ r₁.toList, st'.nodes u = st₁.nodes u := fun u hu =>
              hl'_out u (fun hm => hdisj₁ u hm hu)
            have hsub_r₁' : SubtreeInv P st' rid r₁ :=
              SubtreeInv_agree hsub_r₁ (fun u hu => (hr₁_out u hu).symm)
            have hrev' : (st'.nodes rid).rev = false := hx_eq ▸ hrev₁
            have htag' : (st'.nodes rid).tag = P.idTag := hx_eq ▸ htag₁
            have hev_all : ∀ flip acc,
                evalPairs P st' (.node rid l' r₁) flip acc =
                  evalPairs P st (.node rid l₀ r₀) flip acc := fun flip acc => by
              rw [← hev₁ flip acc]
              have hval_r : (st'.nodes rid).val = (st₁.nodes rid).val := by rw [hx_eq]
              cases flip <;>
                simp only [evalPairs, hrev', htag', hrev₁, htag₁, hval_r,
                  Bool.false_xor, Bool.true_xor, Bool.false_eq_true, ↓reduceIte] <;>
                rw [hl'_hev, evalPairs_agree P hr₁_out]
            have hcnt_eq : l'.countNodes = l₁.countNodes := by
              rw [← AuxTree.length_toList, ← AuxTree.length_toList]; exact hl'_perm.length_eq
            have hsub_final : SubtreeInv P st' rp (.node rid l' r₁) := by
              refine ⟨hrid₁_nz, ?_, ?_, ?_, ?_, ?_, ?_, hl'_sub, hsub_r₁'⟩
              · rw [hx_eq, hleft_eq, hl'_root]
              · rw [hx_eq, hright_eq]
              · rw [hx_eq, hpar₁]
              · intro hrp; rw [hx_eq]; exact hpp₁' hrp
              · rw [hx_eq, hsz₁]; simp [AuxTree.countNodes, hcnt_eq]
              · rw [hev_all false P.idTag, ← hev₁ false P.idTag, hx_eq]; exact hsum₁
            have hhead_final : (evalPairs P st' (.node rid l' r₁) false P.idTag).head? =
                some (r, (st'.nodes r).val) := by
              rw [evalPairs_head_fst_of_left_ne hL hrev' htag' hl'_ne]
              exact hr_head
            have hdep_final : (AuxTree.node rid l' r₁).depthOf r <
                (AuxTree.node rid l₀ r₀).countNodes := by
              have hr_ne_rid : r ≠ rid := fun h => hrid_nl₁ (hl'_perm.mem_iff.mp (h ▸ hr_mem))
              have hr_in_l' : r ∈ l'.toList := hr_mem
              have hdep_r : l'.depthOf r < l₀.countNodes := by
                rw [← hl₁_len]; exact hr_dep
              simp only [AuxTree.depthOf, hr_ne_rid, ↓reduceIte, hr_in_l', AuxTree.countNodes]
              omega
            refine ⟨hsub_final, by simp, rfl, ?_, by simp [AuxTree.toList]; exact Or.inl hr_mem, hr_left,
              hhead_final, hev_all, ?_, fun u hu => ?_, hdep_final, fun vSize => ?_⟩
            · simp only [AuxTree.toList]
              exact ((hl'_perm.trans hl₁_perm).append_right [rid]).append hr₁_perm
            · simp only [AuxTree.rootId]; rw [hx_eq, hpp₁]
            · have hu_l₁ : u ∉ l₁.toList := fun hm =>
                hu (by simp [AuxTree.toList, hl₁_perm.mem_iff.mp hm])
              have hu_orig : u ∉ (AuxTree.node rid l₀ r₀).toList := hu
              exact (hl'_out u hu_l₁).trans (hout₁ u hu_orig)
            · rcases hl'_sz vSize with ⟨a_sz, a_phi, a_sub⟩
              have hsz_l₁ : l₁.treeSize vSize = l₀.treeSize vSize := by
                by_cases hrev : (st.nodes rid).rev = true <;> simp [l₁, hrev, revRoot_treeSize]
              have hsz_r₁ : r₁.treeSize vSize = r₀.treeSize vSize := by
                by_cases hrev : (st.nodes rid).rev = true <;> simp [r₁, hrev, revRoot_treeSize]
              have hphi_l₁ : l₁.treePhi vSize = l₀.treePhi vSize := by
                by_cases hrev : (st.nodes rid).rev = true <;> simp [l₁, hrev, revRoot_treePhi]
              have hphi_r₁ : r₁.treePhi vSize = r₀.treePhi vSize := by
                by_cases hrev : (st.nodes rid).rev = true <;> simp [r₁, hrev, revRoot_treePhi]
              refine ⟨?_, ?_, fun y => ?_⟩
              · simp [AuxTree.treeSize, a_sz, hsz_l₁, hsz_r₁]
              · simp only [AuxTree.treePhi, AuxTree.rank, AuxTree.treeSize, a_sz, a_phi,
                  hsz_l₁, hsz_r₁, hphi_l₁, hphi_r₁]
              · have hs1 : ((AuxTree.node rid l' r₁).findSubtree y).treeSize vSize =
                    ((AuxTree.node rid l₁ r₁).findSubtree y).treeSize vSize := by
                  by_cases hry : rid = y
                  · subst hry; simp [AuxTree.findSubtree, AuxTree.treeSize, a_sz]
                  · simp only [AuxTree.findSubtree, hry, ↓reduceIte, hl'_perm.mem_iff]
                    by_cases hyl : y ∈ l₁.toList
                    · simp [hyl, a_sub y]
                    · simp [hyl]
                have hs2 := pushDown_leftmost_findSubtree_treeSize st rid l₀ r₀ l₁ r₁
                  ⟨rfl, rfl⟩ hnd vSize y
                exact hs1.trans hs2

/-- Correctness and Sleator–Tarjan potential inequality for `findLeftmost P st fuel t.rootId`
when `t.countNodes ≤ fuel` and `t ≠ .leaf`. Brings the logical leftmost node `r` to the root
with empty left child and `head? = some (r, (st'.nodes r).val)`. -/
theorem findLeftmost_preserves_and_phi {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {t : AuxTree} {fuel : ℕ}
    (ht : TreeInv P st t) (hne : t ≠ .leaf) (hfuel : t.countNodes ≤ fuel) :
    ∃ (t₁ t' : AuxTree) (r : ℕ),
      (leftmostWalk P st fuel t.rootId).2 = r ∧
      (findLeftmost P st fuel t.rootId).2 = r ∧
      TreeInv P (leftmostWalk P st fuel t.rootId).1 t₁ ∧
      t₁.depthOf r < t.countNodes ∧
      let st' := (findLeftmost P st fuel t.rootId).1
      TreeInv P st' t' ∧
      t' ≠ .leaf ∧
      t'.rootId = r ∧
      (st'.nodes r).left = 0 ∧
      (st'.nodes r).rev = false ∧
      (st'.nodes r).tag = P.idTag ∧
      (st'.nodes r).ppar = (st.nodes t.rootId).ppar ∧
      t'.toList.Perm t.toList ∧
      evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag ∧
      (evalPairs P st' t' false P.idTag).head? = some (r, (st'.nodes r).val) ∧
      (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        t'.treePhi vSize + 3 * (t.findSubtree r).rank vSize + t₁.depthOf r / 2 ≤
          t.treePhi vSize + 3 * t'.rank vSize) := by
  rcases leftmostWalk_sub_preserves hL ht.nodup ht.sub hne rfl hfuel with
    ⟨t₁, ht₁_sub, ht₁_ne, ht₁_root, ht₁_perm, hr_mem, _, hr_head, ht₁_hev, ht₁_pp, ht₁_out,
      hr_dep, ht₁_sz⟩
  let st₁ := (leftmostWalk P st fuel t.rootId).1
  let r := (leftmostWalk P st fuel t.rootId).2
  have ht₁ : TreeInv P st₁ t₁ := ⟨ht₁_perm.nodup_iff.mpr ht.nodup, ht₁_sub⟩
  have hfuel₁ : t₁.depthOf r < fuel := lt_of_lt_of_le hr_dep hfuel
  rcases splay_preserves_and_phi hL ht₁ hr_mem hfuel₁ with
    ⟨t', ht', ht'_ne, ht'_root, ht'_perm, ht'_ev, ht'_pp, ht'_rev, ht'_tag, ht'_out, ht'_phi⟩
  let st' := splay P st₁ fuel r
  have hev_final : evalPairs P st' t' false P.idTag = evalPairs P st t false P.idTag :=
    ht'_ev.trans (ht₁_hev false P.idTag)
  have hhead_eq : (evalPairs P st' t' false P.idTag).head? = some (r, (st₁.nodes r).val) := by
    rw [ht'_ev]; exact hr_head
  have hl'_leaf : ∀ l' r', t' = .node r l' r' → l' = .leaf := by
    intro l' r' ht'_eq
    by_cases hl : l' = .leaf
    · exact hl
    · exfalso
      have hh := evalPairs_head_fst_of_left_ne (r := r') hL ht'_rev ht'_tag hl
      rw [← ht'_eq, hhead_eq] at hh
      have hh_len : (evalPairs P st' l' false P.idTag).length = l'.countNodes :=
        evalPairs_length P st' l' false P.idTag
      have hh_pos : 0 < (evalPairs P st' l' false P.idTag).length := by
        rw [hh_len]; cases l' with | leaf => exact absurd rfl hl | node _ _ _ => simp [AuxTree.countNodes]
      cases h_ev : evalPairs P st' l' false P.idTag with
      | nil => rw [h_ev] at hh_pos; simp at hh_pos
      | cons p_hd _ =>
          rw [h_ev] at hh
          simp only [List.head?_cons, Option.some.injEq] at hh
          have hfst : p_hd.1 ∈ (evalPairs P st' l' false P.idTag).map Prod.fst := by
            rw [h_ev]; simp
          have hl_mem : p_hd.1 ∈ l'.toList := by
            rw [evalPairs_map_fst] at hfst
            exact (AuxTree.evalInorder_perm _ _ _).mem_iff.mp hfst
          have hnd' := ht'.nodup
          rw [ht'_eq] at hnd'
          exact (AuxTree.nodup_node_unfold hnd').2.1
            (by rw [← congrArg Prod.fst hh] at hl_mem; exact hl_mem)
  obtain ⟨l', r', ht'_eq⟩ := AuxTree.findSubtree_root_of_mem (ht'_perm.mem_iff.mpr hr_mem)
  have ht'_node : t' = .node r l' r' := by
    rw [← AuxTree.findSubtree_root ht'_ne, ht'_root]; exact ht'_eq
  have hl'_eq : l' = .leaf := hl'_leaf l' r' ht'_node
  rw [hl'_eq] at ht'_node
  have hr_left' : (st'.nodes r).left = 0 := by
    have hsub' := ht'.sub
    rw [ht'_node] at hsub'
    exact hsub'.2.1
  have hval_eq : (st'.nodes r).val = (st₁.nodes r).val := by
    have h1 := head?_evalPairs_of_left_leaf hL (r := r') ht'_rev ht'_tag
    rw [← ht'_node, hhead_eq] at h1
    exact (Prod.mk.inj (Option.some.inj h1)).2.symm
  refine ⟨t₁, t', r, rfl, rfl, ht₁, hr_dep, ht', ht'_ne, ht'_root, hr_left', ht'_rev, ht'_tag,
    ht'_pp.trans ht₁_pp, ht'_perm.trans ht₁_perm, hev_final,
    by change (evalPairs P st' t' false P.idTag).head? = some (r, (st'.nodes r).val); rw [hval_eq]; exact hhead_eq,
    ?_, fun vSize => ?_⟩
  · intro u hu
    exact (ht'_out u (fun hm => hu (ht₁_perm.mem_iff.mp hm))).trans (ht₁_out u hu)
  · rcases ht₁_sz vSize with ⟨a_sz, a_phi, a_sub⟩
    rcases ht'_phi vSize with ⟨b_sz, b_phi⟩
    have hrank_eq : (t₁.findSubtree r).rank vSize = (t.findSubtree r).rank vSize := by
      simp only [AuxTree.rank, a_sub r]
    rw [hrank_eq, a_phi] at b_phi
    exact ⟨b_sz.trans a_sz, b_phi⟩

/-! ### Root splice primitives: `makeSingleton`, `detachRight`, `attachRight`, `detachRootChildren` -/

/-- Initialize/reset node `x` as a clean singleton auxiliary tree with value `v` and dashed
path-parent `pp`. -/
def makeSingleton (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (x : ℕ) (v : α) (pp : ℕ) : SplayState α σ τ :=
  st.setNode x
    { left := 0
      right := 0
      par := 0
      ppar := pp
      sz := 1
      val := v
      sum := P.single x v
      tag := P.idTag
      rev := false }

theorem makeSingleton_treeInv {P : LctPayload α σ τ} (hL : P.Laws)
    (st : SplayState α σ τ) {x : ℕ} (hx : x ≠ 0) (v : α) (pp : ℕ) :
    let st' := makeSingleton P st x v pp
    TreeInv P st' (.node x .leaf .leaf) ∧
    (st'.nodes x).ppar = pp ∧
    (st'.nodes x).rev = false ∧
    (st'.nodes x).tag = P.idTag ∧
    evalPairs P st' (.node x .leaf .leaf) false P.idTag = [(x, v)] ∧
    (∀ u ≠ x, st'.nodes u = st.nodes u) := by
  intro st'
  have hx_nd : st'.nodes x =
      ({ left := 0, right := 0, par := 0, ppar := pp, sz := 1,
         val := v, sum := P.single x v, tag := P.idTag, rev := false } : SplayNode α σ τ) := by
    simp [st', makeSingleton, setNode]
  have hsum : (st'.nodes x).sum =
      P.listSummary (evalPairs P st' (.node x .leaf .leaf) false P.idTag) := by
    simp [evalPairs, hx_nd, hL.actVal_id, LctPayload.listSummary_single hL]
  refine ⟨⟨by simp [AuxTree.toList], hx, by simp [hx_nd, AuxTree.rootId],
      by simp [hx_nd, AuxTree.rootId], by simp [hx_nd], fun h => absurd rfl h,
      by simp [hx_nd, AuxTree.countNodes], hsum, trivial, trivial⟩,
    by simp [hx_nd], by simp [hx_nd], by simp [hx_nd],
    by simp [evalPairs, hx_nd, hL.actVal_id],
    fun u hu => by simp [st', makeSingleton, setNode, hu]⟩

/-- Detach the right child of auxiliary-tree root `x` into a separate auxiliary tree with `ppar = x`. -/
def detachRight (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) :
    SplayState α σ τ :=
  if x = 0 then st
  else
    let r := (st.nodes x).right
    if r = 0 then st
    else
      let st1 := st.setPar r 0
      let st2 := st1.setPpar r x
      let st3 := st2.setRight x 0
      pull P st3 x

theorem detachRight_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {x : ℕ} {L R : AuxTree}
    (ht : TreeInv P st (.node x L R))
    (hrev : (st.nodes x).rev = false) (htag : (st.nodes x).tag = P.idTag) :
    let st' := detachRight P st x
    TreeInv P st' (.node x L .leaf) ∧
    (st'.nodes x).rev = false ∧ (st'.nodes x).tag = P.idTag ∧
    (st'.nodes x).ppar = (st.nodes x).ppar ∧
    (st'.nodes x).right = 0 ∧
    evalPairs P st' (.node x L .leaf) false P.idTag =
      evalPairs P st L false P.idTag ++ [(x, (st.nodes x).val)] ∧
    (R ≠ .leaf →
      TreeInv P st' R ∧
      (st'.nodes R.rootId).ppar = x ∧
      evalPairs P st' R false P.idTag = evalPairs P st R false P.idTag) ∧
    (∀ u ∉ (AuxTree.node x L R).toList, st'.nodes u = st.nodes u) := by
  intro st'
  rcases AuxTree.nodup_node_unfold ht.nodup with ⟨hL_nd, hx_nL, hR_nd, hx_nR, hdisj⟩
  rcases ht.sub with ⟨hx_nz, hl_eq, hr_eq, hpar, _, _, _, hL_sub, hR_sub⟩
  cases R with
  | leaf =>
      have hr0 : (st.nodes x).right = 0 := by simpa [AuxTree.rootId] using hr_eq
      have hst'_eq : st' = st := by simp [st', detachRight, hx_nz, hr0]
      rw [hst'_eq]
      refine ⟨ht, hrev, htag, rfl, hr0, ?_, fun h => absurd rfl h, fun _ _ => rfl⟩
      simp [evalPairs, hrev, htag, hL.compTag_id_left, hL.actVal_id]
  | node rid rL rR =>
      have hrid_nz : rid ≠ 0 := hR_sub.1
      have hright_rid : (st.nodes x).right = rid := hr_eq
      have hrx : rid ≠ x := fun h => hx_nR (h ▸ by simp [AuxTree.toList])
      let st1 := st.setPar rid 0
      let st2 := st1.setPpar rid x
      let st3 := st2.setRight x 0
      have hst'_eq : st' = pull P st3 x := by
        simp only [st', detachRight, hx_nz, ↓reduceIte, hright_rid, hrid_nz, st1, st2, st3]
      have hx3 : st3.nodes x = { st.nodes x with right := 0 } := by
        simp [st3, st2, st1, setRight, setPpar, setPar, hrx.symm]
      have hrid3 : st3.nodes rid = { st.nodes rid with par := 0, ppar := x } := by
        simp [st3, st2, st1, setRight, setPpar, setPar, hrx]
      have hu3 : ∀ u, u ≠ x → u ≠ rid → st3.nodes u = st.nodes u := fun u h1 h2 => by
        simp [st3, st2, st1, setRight, setPpar, setPar, h1, h2]
      have hL3 : SubtreeInv P st3 x L := by
        refine SubtreeInv_agree hL_sub (fun u hu => ?_)
        exact (hu3 u (fun h => hx_nL (h ▸ hu))
          (fun h => hdisj u hu (h ▸ by simp [AuxTree.toList]))).symm
      have hR3 : SubtreeInv P st3 0 (.node rid rL rR) := by
        rcases AuxTree.nodup_node_unfold hR_nd with ⟨_, hrid_nrL, _, hrid_nrR, _⟩
        rcases hR_sub with ⟨_, hl_r, hr_r, _, _, hsz_r, hsum_r, hrL_sub, hrR_sub⟩
        have hl3 : SubtreeInv P st3 rid rL := SubtreeInv_agree hrL_sub (fun u hu => (hu3 u
          (fun h => hx_nR (h ▸ by simp [AuxTree.toList, hu]))
          (fun h => hrid_nrL (h ▸ hu))).symm)
        have hr3 : SubtreeInv P st3 rid rR := SubtreeInv_agree hrR_sub (fun u hu => (hu3 u
          (fun h => hx_nR (h ▸ by simp [AuxTree.toList, hu]))
          (fun h => hrid_nrR (h ▸ hu))).symm)
        have hevR3 : evalPairs P st3 (.node rid rL rR) false P.idTag =
            evalPairs P st (.node rid rL rR) false P.idTag := by
          refine evalPairs_agree_vrt P (fun u hu => ?_) false P.idTag
          by_cases hur : u = rid
          · subst hur; simp [hrid3]
          · rw [hu3 u (fun h => hx_nR (h ▸ hu)) hur]; exact ⟨rfl, rfl, rfl⟩
        refine ⟨hrid_nz, by simpa [hrid3] using hl_r, by simpa [hrid3] using hr_r,
          by simp [hrid3], fun h => absurd rfl h, by simpa [hrid3] using hsz_r,
          by rw [hevR3]; simp [hrid3, hsum_r], hl3, hr3⟩
      rcases pull_node_build hL (st := st3) (r := .leaf) hx_nz hx_nL (by simp [AuxTree.toList])
        (by rw [hx3]; exact hl_eq) (by simp [hx3, AuxTree.rootId]) (by rw [hx3]; exact hpar)
        (fun h => absurd rfl h) (by rw [hx3]; exact hrev) (by rw [hx3]; exact htag) hL3 trivial with
        ⟨hx_sub', hrev', htag', hpp', hne'⟩
      rw [← hst'_eq] at hx_sub' hrev' htag' hpp' hne'
      have hx_ppar : (st'.nodes x).ppar = (st.nodes x).ppar := by
        rw [hpp', hx3]
      have hx_right : (st'.nodes x).right = 0 := by
        rw [hst'_eq, pull_right_eq, hx3]
      have hnd_L : (AuxTree.node x L .leaf).toList.Nodup :=
        nodup_node_intro hL_nd hx_nL (by simp [AuxTree.toList]) (by simp [AuxTree.toList])
          (fun _ _ h => by simp [AuxTree.toList] at h)
      have hev_L' : evalPairs P st' (.node x L .leaf) false P.idTag =
          evalPairs P st L false P.idTag ++ [(x, (st.nodes x).val)] := by
        have hevL : evalPairs P st' L false P.idTag = evalPairs P st L false P.idTag := by
          refine evalPairs_agree P (fun u hu => ?_) false P.idTag
          have hux : u ≠ x := fun h => hx_nL (h ▸ hu)
          have hur : u ≠ rid := fun h => hdisj u hu (h ▸ by simp [AuxTree.toList])
          exact (hne' u hux).trans (hu3 u hux hur)
        have hval_x : (st'.nodes x).val = (st.nodes x).val := by
          rw [hst'_eq, pull_val_eq', hx3]
        simp [evalPairs, hrev', htag', hval_x, hL.compTag_id_left, hL.actVal_id, hevL]
      have hR_sub' : SubtreeInv P st' 0 (.node rid rL rR) :=
        SubtreeInv_agree hR3 (fun u hu => (hne' u (fun h => hx_nR (h ▸ hu))).symm)
      have hR_pp' : (st'.nodes rid).ppar = x := by
        rw [hne' rid hrx, hrid3]
      have hR_ev' : evalPairs P st' (.node rid rL rR) false P.idTag =
          evalPairs P st (.node rid rL rR) false P.idTag := by
        refine evalPairs_agree_vrt P (fun u hu => ?_) false P.idTag
        have hux : u ≠ x := fun h => hx_nR (h ▸ hu)
        rw [hne' u hux]
        by_cases hur : u = rid
        · subst hur; simp [hrid3]
        · rw [hu3 u hux hur]; exact ⟨rfl, rfl, rfl⟩
      refine ⟨⟨hnd_L, hx_sub'⟩, hrev', htag', hx_ppar, hx_right, hev_L',
        fun _ => ⟨⟨hR_nd, hR_sub'⟩, hR_pp', hR_ev'⟩, fun u hu => ?_⟩
      have hux : u ≠ x := fun h => hu (by subst h; simp [AuxTree.toList])
      have hur : u ≠ rid := fun h => hu (by subst h; simp [AuxTree.toList])
      exact (hne' u hux).trans (hu3 u hux hur)

/-- Attach a separate auxiliary tree rooted at `x` (whose `ppar = u`) as the right child of
auxiliary-tree root `u` (whose current right child is `0`). -/
def attachRight (P : LctPayload α σ τ) (st : SplayState α σ τ) (u x : ℕ) :
    SplayState α σ τ :=
  if u = 0 then st
  else
    let st1 := st.setRight u x
    let st2 := if x = 0 then st1 else (st1.setPar x u).setPpar x 0
    pull P st2 u

theorem attachRight_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {u x : ℕ} {Lu tx : AuxTree}
    (htu : TreeInv P st (.node u Lu .leaf))
    (hrev_u : (st.nodes u).rev = false) (htag_u : (st.nodes u).tag = P.idTag)
    (htx : TreeInv P st tx) (hx_ne : tx ≠ .leaf) (hx_root : tx.rootId = x)
    (hdisj : ∀ a ∈ (AuxTree.node u Lu .leaf).toList, a ∉ tx.toList) :
    let st' := attachRight P st u x
    TreeInv P st' (.node u Lu tx) ∧
    (st'.nodes u).rev = false ∧ (st'.nodes u).tag = P.idTag ∧
    (st'.nodes u).ppar = (st.nodes u).ppar ∧
    evalPairs P st' (.node u Lu tx) false P.idTag =
      evalPairs P st Lu false P.idTag ++ [(u, (st.nodes u).val)] ++
        evalPairs P st tx false P.idTag ∧
    (∀ z ∉ (AuxTree.node u Lu tx).toList, st'.nodes z = st.nodes z) := by
  intro st'
  rcases AuxTree.nodup_node_unfold htu.nodup with ⟨hLu_nd, hu_nLu, _, _, _⟩
  rcases htu.sub with ⟨hu_nz, hl_u, _, hpar_u, _, _, _, hLu_sub, _⟩
  have hx_nz : x ≠ 0 := by
    cases htx_c : tx with
    | leaf => exact absurd htx_c hx_ne
    | node xid xL xR =>
        have hxid : xid = x := by simpa [htx_c, AuxTree.rootId] using hx_root
        have hsubx := htx.sub
        rw [htx_c, hxid] at hsubx
        exact hsubx.1
  have hux : x ≠ u := fun h => hdisj u (by simp [AuxTree.toList])
    (h ▸ hx_root ▸ AuxTree.rootId_mem hx_ne)
  let st1 := st.setRight u x
  let st2 := (st1.setPar x u).setPpar x 0
  have hst'_eq : st' = pull P st2 u := by
    simp only [st', attachRight, hu_nz, ↓reduceIte, hx_nz, st1, st2]
  have hu2 : st2.nodes u = { st.nodes u with right := x } := by
    simp [st2, st1, setPpar, setPar, setRight, hux.symm]
  have hx2 : st2.nodes x = { st.nodes x with par := u, ppar := 0 } := by
    simp [st2, st1, setPpar, setPar, setRight, hux]
  have hz2 : ∀ z, z ≠ u → z ≠ x → st2.nodes z = st.nodes z := fun z h1 h2 => by
    simp [st2, st1, setPpar, setPar, setRight, h1, h2]
  have hLu2 : SubtreeInv P st2 u Lu := by
    refine SubtreeInv_agree hLu_sub (fun z hz => ?_)
    have h1 : z ≠ u := fun h => hu_nLu (h ▸ hz)
    have h2 : z ≠ x := fun h => hdisj z (by simp [AuxTree.toList, hz])
      (h ▸ hx_root ▸ AuxTree.rootId_mem hx_ne)
    exact (hz2 z h1 h2).symm
  have htx2 : SubtreeInv P st2 u tx := by
    cases tx with
    | leaf => exact absurd rfl hx_ne
    | node xid xL xR =>
        have hxid : xid = x := by simpa [AuxTree.rootId] using hx_root
        subst hxid
        rcases AuxTree.nodup_node_unfold htx.nodup with ⟨_, hx_nxL, _, hx_nxR, _⟩
        rcases htx.sub with ⟨_, hl_x, hr_x, _, _, hsz_x, hsum_x, hxL_sub, hxR_sub⟩
        have hxl2 : SubtreeInv P st2 xid xL := SubtreeInv_agree hxL_sub (fun z hz => (hz2 z
          (fun h => hdisj u (by simp [AuxTree.toList]) (by simp [AuxTree.toList, h ▸ hz]))
          (fun h => hx_nxL (h ▸ hz))).symm)
        have hxr2 : SubtreeInv P st2 xid xR := SubtreeInv_agree hxR_sub (fun z hz => (hz2 z
          (fun h => hdisj u (by simp [AuxTree.toList]) (by simp [AuxTree.toList, h ▸ hz]))
          (fun h => hx_nxR (h ▸ hz))).symm)
        have hevx2 : evalPairs P st2 (.node xid xL xR) false P.idTag =
            evalPairs P st (.node xid xL xR) false P.idTag := by
          refine evalPairs_agree_vrt P (fun z hz => ?_) false P.idTag
          by_cases hzx : z = xid
          · subst hzx; simp [hx2]
          · rw [hz2 z (fun h => hdisj u (by simp [AuxTree.toList]) (h ▸ hz)) hzx]
            exact ⟨rfl, rfl, rfl⟩
        refine ⟨hx_nz, by simpa [hx2] using hl_x, by simpa [hx2] using hr_x,
          by simp [hx2], fun _ => by simp [hx2], by simpa [hx2] using hsz_x,
          by rw [hevx2]; simp [hx2, hsum_x], hxl2, hxr2⟩
  have hu_ntx : u ∉ tx.toList := hdisj u (by simp [AuxTree.toList])
  rcases pull_node_build hL hu_nz hu_nLu hu_ntx
    (by simp [hu2, hl_u]) (by simp [hu2, hx_root]) (by simp [hu2, hpar_u])
    (fun h => absurd rfl h) (by simp [hu2, hrev_u]) (by simp [hu2, htag_u]) hLu2 htx2 with
    ⟨hsub', hrev', htag', hpp', hne'⟩
  rw [← hst'_eq] at hsub' hrev' htag' hpp' hne'
  have hnd' : (AuxTree.node u Lu tx).toList.Nodup :=
    nodup_node_intro hLu_nd hu_nLu htx.nodup hu_ntx
      (fun a ha => hdisj a (by simp [AuxTree.toList, ha]))
  have hev' : evalPairs P st' (.node u Lu tx) false P.idTag =
      evalPairs P st Lu false P.idTag ++ [(u, (st.nodes u).val)] ++
        evalPairs P st tx false P.idTag := by
    have hevLu : evalPairs P st' Lu false P.idTag = evalPairs P st Lu false P.idTag := by
      refine evalPairs_agree P (fun z hz => ?_) false P.idTag
      have h1 : z ≠ u := fun h => hu_nLu (h ▸ hz)
      have h2 : z ≠ x := fun h => hdisj z (by simp [AuxTree.toList, hz])
        (h ▸ hx_root ▸ AuxTree.rootId_mem hx_ne)
      exact (hne' z h1).trans (hz2 z h1 h2)
    have hevtx : evalPairs P st' tx false P.idTag = evalPairs P st tx false P.idTag := by
      refine evalPairs_agree_vrt P (fun z hz => ?_) false P.idTag
      have h1 : z ≠ u := fun h => hu_ntx (h ▸ hz)
      rw [hne' z h1]
      by_cases hzx : z = x
      · subst hzx; simp [hx2]
      · rw [hz2 z h1 hzx]; exact ⟨rfl, rfl, rfl⟩
    have hval_u : (st'.nodes u).val = (st.nodes u).val := by
      rw [hst'_eq, pull_val_eq', hu2]
    simp [evalPairs, hrev', htag', hval_u, hL.compTag_id_left, hL.actVal_id, hevLu, hevtx,
      List.append_assoc]
  refine ⟨⟨hnd', hsub'⟩, hrev', htag', by rw [hpp', hu2], hev', fun z hz => ?_⟩
  have h1 : z ≠ u := fun h => hz (by subst h; simp [AuxTree.toList])
  have h2 : z ≠ x := fun h => hz (by
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
    exact Or.inr (h ▸ hx_root ▸ AuxTree.rootId_mem hx_ne))
  exact (hne' z h1).trans (hz2 z h1 h2)

/-- Split a 3-node auxiliary tree `.node x (.node a .leaf .leaf) (.node b .leaf .leaf)` into
three disjoint singleton trees (`x`, `a`, `b`), clearing `left`/`right`/`ppar` on `x` and
`par`/`ppar` on `a` and `b`. Used to remove an edge-node cleanly during `cut`. -/
def detachRootChildren (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) :
    SplayState α σ τ :=
  if x = 0 then st
  else
    let a := (st.nodes x).left
    let b := (st.nodes x).right
    let st1 := if a = 0 then st else (st.setPar a 0).setPpar a 0
    let st2 := if b = 0 then st1 else (st1.setPar b 0).setPpar b 0
    let st3 := (st2.setLeft x 0).setRight x 0
    pull P st3 x

theorem detachRootChildren_preserves {P : LctPayload α σ τ} (hL : P.Laws)
    {st : SplayState α σ τ} {x a b : ℕ}
    (ht : TreeInv P st (.node x (.node a .leaf .leaf) (.node b .leaf .leaf)))
    (hrev : (st.nodes x).rev = false) (htag : (st.nodes x).tag = P.idTag) :
    let st' := detachRootChildren P st x
    TreeInv P st' (.node x .leaf .leaf) ∧
    TreeInv P st' (.node a .leaf .leaf) ∧
    TreeInv P st' (.node b .leaf .leaf) ∧
    (st'.nodes x).ppar = (st.nodes x).ppar ∧
    (st'.nodes a).ppar = 0 ∧ (st'.nodes b).ppar = 0 ∧
    (∀ u ∉ [a, x, b], st'.nodes u = st.nodes u) := by
  intro st'
  have hnd := ht.nodup
  simp only [AuxTree.toList, List.nil_append, List.cons_append,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨hax, hab⟩, ⟨hxb, _⟩⟩
  rcases ht.sub with ⟨hx_nz, hl_x, hr_x, hpar_x, _, _, _, ha_sub, hb_sub⟩
  rcases ha_sub with ⟨ha_nz, hl_a, hr_a, _, _, hsz_a, hsum_a, _, _⟩
  rcases hb_sub with ⟨hb_nz, hl_b, hr_b, _, _, hsz_b, hsum_b, _, _⟩
  simp only [AuxTree.rootId] at hl_x hr_x
  let st1 := (st.setPar a 0).setPpar a 0
  let st2 := (st1.setPar b 0).setPpar b 0
  let st3 := (st2.setLeft x 0).setRight x 0
  have hst'_eq : st' = pull P st3 x := by
    simp only [st', detachRootChildren, hx_nz, ↓reduceIte, hl_x, hr_x, ha_nz, hb_nz, st1, st2, st3]
  have hx3 : st3.nodes x = { st.nodes x with left := 0, right := 0 } := by
    simp [st3, st2, st1, setRight, setLeft, setPpar, setPar, Ne.symm hax, hxb]
  have ha3 : st3.nodes a = { st.nodes a with par := 0, ppar := 0 } := by
    simp [st3, st2, st1, setRight, setLeft, setPpar, setPar, hax, hab]
  have hb3 : st3.nodes b = { st.nodes b with par := 0, ppar := 0 } := by
    simp [st3, st2, st1, setRight, setLeft, setPpar, setPar, Ne.symm hxb, Ne.symm hab]
  have hu3 : ∀ u, u ≠ a → u ≠ x → u ≠ b → st3.nodes u = st.nodes u := fun u h1 h2 h3 => by
    simp [st3, st2, st1, setRight, setLeft, setPpar, setPar, h1, h2, h3]
  rcases pull_node_build hL (st := st3) (l := .leaf) (r := .leaf) hx_nz
    (by simp [AuxTree.toList]) (by simp [AuxTree.toList])
    (by simp [hx3, AuxTree.rootId]) (by simp [hx3, AuxTree.rootId]) (by rw [hx3]; exact hpar_x)
    (fun h => absurd rfl h) (by rw [hx3]; exact hrev) (by rw [hx3]; exact htag) trivial trivial with
    ⟨hx_sub', _, _, hpp_x', hne'⟩
  rw [← hst'_eq] at hx_sub' hpp_x' hne'
  have ha_ev : evalPairs P st' (.node a .leaf .leaf) false P.idTag =
      evalPairs P st (.node a .leaf .leaf) false P.idTag := by
    refine evalPairs_agree_vrt P (fun u hu => ?_) false P.idTag
    have hua : u = a := by simpa [AuxTree.toList] using hu
    rw [hua, hne' a hax, ha3]; exact ⟨rfl, rfl, rfl⟩
  have hb_ev : evalPairs P st' (.node b .leaf .leaf) false P.idTag =
      evalPairs P st (.node b .leaf .leaf) false P.idTag := by
    refine evalPairs_agree_vrt P (fun u hu => ?_) false P.idTag
    have hub : u = b := by simpa [AuxTree.toList] using hu
    rw [hub, hne' b (Ne.symm hxb), hb3]; exact ⟨rfl, rfl, rfl⟩
  have ha_node' : st'.nodes a = { st.nodes a with par := 0, ppar := 0 } := by
    rw [hne' a hax, ha3]
  have hb_node' : st'.nodes b = { st.nodes b with par := 0, ppar := 0 } := by
    rw [hne' b (Ne.symm hxb), hb3]
  have ha_sub' : SubtreeInv P st' 0 (.node a .leaf .leaf) :=
    ⟨ha_nz, by simpa [ha_node'] using hl_a, by simpa [ha_node'] using hr_a,
      by simp [ha_node'], fun h => absurd rfl h, by simpa [ha_node'] using hsz_a,
      by rw [ha_ev]; simp [ha_node', hsum_a], trivial, trivial⟩
  have hb_sub' : SubtreeInv P st' 0 (.node b .leaf .leaf) :=
    ⟨hb_nz, by simpa [hb_node'] using hl_b, by simpa [hb_node'] using hr_b,
      by simp [hb_node'], fun h => absurd rfl h, by simpa [hb_node'] using hsz_b,
      by rw [hb_ev]; simp [hb_node', hsum_b], trivial, trivial⟩
  refine ⟨⟨by simp [AuxTree.toList], hx_sub'⟩, ⟨by simp [AuxTree.toList], ha_sub'⟩,
    ⟨by simp [AuxTree.toList], hb_sub'⟩, by rw [hpp_x', hx3],
    by simp [ha_node'], by simp [hb_node'], fun u hu => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
  exact (hne' u hu.2.1).trans (hu3 u hu.1 hu.2.1 hu.2.2)

/-! ### Virtual-weight conservation under `detachRight` and `attachRight` -/

theorem treeSize_agree {v₁ v₂ : ℕ → ℕ} {t : AuxTree}
    (h : ∀ u ∈ t.toList, v₁ u = v₂ u) :
    t.treeSize v₁ = t.treeSize v₂ := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      simp only [AuxTree.treeSize]
      rw [h id (by simp [AuxTree.toList]),
        ihl (fun u hu => h u (by simp [AuxTree.toList, hu])),
        ihr (fun u hu => h u (by simp [AuxTree.toList, hu]))]

theorem treePhi_agree {v₁ v₂ : ℕ → ℕ} {t : AuxTree}
    (h : ∀ u ∈ t.toList, v₁ u = v₂ u) :
    t.treePhi v₁ = t.treePhi v₂ := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hsz : (AuxTree.node id l r).treeSize v₁ = (AuxTree.node id l r).treeSize v₂ :=
        treeSize_agree h
      simp only [AuxTree.treePhi, AuxTree.rank, hsz,
        ihl (fun u hu => h u (by simp [AuxTree.toList, hu])),
        ihr (fun u hu => h u (by simp [AuxTree.toList, hu]))]

theorem detachRight_treePhi_eq {v v' : ℕ → ℕ} {x : ℕ} {L R : AuxTree}
    (hL : ∀ u ∈ L.toList, v' u = v u)
    (hR : ∀ u ∈ R.toList, v' u = v u)
    (hx : v' x = v x + R.treeSize v) :
    (AuxTree.node x L .leaf).treeSize v' = (AuxTree.node x L R).treeSize v ∧
    (AuxTree.node x L .leaf).treePhi v' + R.treePhi v' = (AuxTree.node x L R).treePhi v := by
  have hL_sz : L.treeSize v' = L.treeSize v := treeSize_agree hL
  have hR_phi : R.treePhi v' = R.treePhi v := treePhi_agree hR
  have hL_phi : L.treePhi v' = L.treePhi v := treePhi_agree hL
  have hsz : (AuxTree.node x L .leaf).treeSize v' = (AuxTree.node x L R).treeSize v := by
    simp only [AuxTree.treeSize, hx, hL_sz]
    omega
  have hrk : (AuxTree.node x L .leaf).rank v' = (AuxTree.node x L R).rank v := by
    simp only [AuxTree.rank, hsz]
  refine ⟨hsz, ?_⟩
  simp only [AuxTree.treePhi, hrk, hL_phi, hR_phi]
  omega

theorem attachRight_treePhi_eq {v v' : ℕ → ℕ} {u : ℕ} {Lu tx : AuxTree}
    (hL : ∀ a ∈ Lu.toList, v' a = v a)
    (hR : ∀ a ∈ tx.toList, v' a = v a)
    (hu : v u = v' u + tx.treeSize v') :
    (AuxTree.node u Lu tx).treeSize v' = (AuxTree.node u Lu .leaf).treeSize v ∧
    (AuxTree.node u Lu tx).treePhi v' = (AuxTree.node u Lu .leaf).treePhi v + tx.treePhi v := by
  have hL_sz : Lu.treeSize v' = Lu.treeSize v := treeSize_agree hL
  have hR_phi : tx.treePhi v' = tx.treePhi v := treePhi_agree hR
  have hL_phi : Lu.treePhi v' = Lu.treePhi v := treePhi_agree hL
  have hsz : (AuxTree.node u Lu tx).treeSize v' = (AuxTree.node u Lu .leaf).treeSize v := by
    simp only [AuxTree.treeSize, hu, hL_sz]
    omega
  have hrk : (AuxTree.node u Lu tx).rank v' = (AuxTree.node u Lu .leaf).rank v := by
    simp only [AuxTree.rank, hsz]
  refine ⟨hsz, ?_⟩
  simp only [AuxTree.treePhi, hrk, hL_phi, hR_phi]
  omega

end SplayState

end MinCostFlow.LinkCut
