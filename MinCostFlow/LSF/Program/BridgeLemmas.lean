module

public import MinCostFlow.LSF.ModelWith
public import MinCostFlow.LSF.Program.Layout
import MinCostFlow.LSF.Lemma54Init
import MinCostFlow.LSF.SafePaths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mathematical Bridge Lemmas for the WordRAM LSF Implementation

This file proves the graph, tree, HLD, and stretch-arithmetic bridge lemmas used across the
WordRAM LSF initialization and update programs:

* `upClosure_insert_of_thParent_mem` and `deletedEdges_insert_branchFree`: incremental forest-cut
  theorem for inserting one vertex `z` into a branch-free root set `R₁` with `thParent z ∈ R₁`
  (or any `z` preserving `IsBranchFree`), showing `(F_T(insert z R₁, π)).E = F₁.E \ {cutE}` for
  the unique minimum-`π` edge on `T[z, F₁.root z]`.
* `refineDecomp_total_bounds`: cardinality bounds on `refineDecomp W_T F₀` showing each piece
  spans a connected subtree of `F₀` with `W.card = (inducedEdges F₀ W).card + 1`, hence
  `W_init.card ≤ F₀.E.card ≤ n₀`, `totalEdges ≤ n₀`, and `totalVerts ≤ 2 * n₀` (`WBlockAt`).
* `isLSST_smul_weights` and `starTree_isLSST_empty`: scaling invariance of `IsLSST` (allowing unit
  `1 / 2^P_fp` weights in `lsstModule`) and explicit star-tree LSST when `G₀.E = ∅`.
* `approxCongOrder_of_floor`: exact `(5 / 4)`-approximate congestion order via integer floor
  scaling `⌊m_e * 2^S_div / ℓ_int(e)⌋`.
* `levelStretchBound_rat_eq`: exact integer numerator identity `levelStretchBound ... = rawNum / ℓ_int`
  using safe integer lengths (`ℓ_int f` on `G₀.E` and `0` on bridge edges).
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-! ## Walk helpers -/

private lemma isWalk_of_edges_mem {T H : MGraph}
    (hend : ∀ e ∈ H.E, H.tail e = T.tail e ∧ H.head e = T.head e) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, T.IsWalk u v P → (∀ f ∈ walkEdges P, f ∈ H.E) →
      H.IsWalk u v P
  | _, _, _, .nil s, _ => .nil s
  | _, _, _, .cons (u := u₀) (x := x) (P := Q) _hx hsrc hw, hsub => by
    have hxH : x.1 ∈ H.E := hsub x.1 (by rw [walkEdges_cons]; exact Finset.mem_insert_self _ _)
    have hrest : ∀ f ∈ walkEdges Q, f ∈ H.E := fun f hf =>
      hsub f (by rw [walkEdges_cons]; exact Finset.mem_insert_of_mem hf)
    have heq := hend x.1 hxH
    have hsrc' : H.src x = u₀ := by
      rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.src, heq.1, heq.2] <;> exact hsrc
    have hdst' : H.dst x = T.dst x := by
      rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.dst, heq.1, heq.2]
    exact .cons hxH hsrc' (hdst'.symm ▸ isWalk_of_edges_mem hend hw hrest)

private lemma isWalk_nil_false_of_ne {G : MGraph} {u v : ℕ} (hne : u ≠ v)
    (hW : G.IsWalk u v []) : False := by
  cases hW
  exact hne rfl

/-! ## Incremental `upClosure` and `deletedEdges` theorem -/

/-- If `thParent T r x` already lies in `upClosure TH r S`, then adding `x` to `upClosure TH r S`
equals `upClosure TH r (insert x S)`, so branch-freeness is preserved step by step along a
top-down pop from `thStack`. -/
lemma upClosure_insert_of_thParent_mem {T : MGraph} {r x : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) (hxV : x ∈ T.V) (hx_ne : x ≠ r)
    (hp : thParent T r x ∈ upClosure (hldAuxTree T r) r S) :
    insert x (upClosure (hldAuxTree T r) r S) = upClosure (hldAuxTree T r) r (insert x S) := by
  have hTH := hldAuxTree_isRootedTree hT
  have hxTH : x ∈ (hldAuxTree T r).V := hxV
  have hpar := (hldAuxTree_parent hT hxV hx_ne).1
  apply Finset.Subset.antisymm
  · intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hyU
    · exact subset_upClosure (Finset.mem_insert_self _ _)
    · rw [mem_upClosure_iff] at hyU ⊢
      rcases hyU with ⟨u, huS, hyu⟩
      exact ⟨u, Finset.mem_insert_of_mem huS, hyu⟩
  · intro y hy
    rw [mem_upClosure_iff] at hy
    rcases hy with ⟨u, huIS, hyu⟩
    rw [Finset.mem_insert] at huIS
    rcases huIS with rfl | huS
    · rcases (isAncestor_iff_eq_or_parent hTH hxTH).mp hyu with rfl | ⟨_, hyp⟩
      · exact Finset.mem_insert_self _ _
      · rw [hpar] at hyp
        exact Finset.mem_insert_of_mem (upClosure_isUpwardClosed hTH hS hp hyp)
    · exact Finset.mem_insert_of_mem (mem_upClosure_iff.mpr ⟨u, huS, hyu⟩)

lemma isBranchFree_insert_of_thParent_mem {T : MGraph} {r x : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) (hxV : x ∈ T.V) (hx_ne : x ≠ r)
    (hp : thParent T r x ∈ upClosure (hldAuxTree T r) r S) :
    IsBranchFree T r (insert x (upClosure (hldAuxTree T r) r S)) := by
  rw [upClosure_insert_of_thParent_mem hT hS hxV hx_ne hp]
  exact upClosure_isBranchFree hT (Finset.insert_subset_iff.mpr ⟨hxV, hS⟩)

private lemma walkEdges_forestPath_comm {T : MGraph} (hT : T.IsForest) {u v : ℕ}
    (hconn : T.Connected u v) :
    walkEdges (T.forestPath u v) = walkEdges (T.forestPath v u) := by
  have hrev := forestPath_rev hT hconn
  rw [← walkEdges_walkRev (T.forestPath u v), ← hrev]

private lemma mem_walkVertices_forestPath_rev {T : MGraph} (hT : T.IsForest) {u v w : ℕ}
    (hconn : T.Connected u v) (hw : w ∈ T.walkVertices u (T.forestPath u v)) :
    w ∈ T.walkVertices v (T.forestPath v u) := by
  have hP := forestPath_isPath hT hconn
  have hrev := forestPath_rev hT hconn
  rw [hrev, walkVertices_walkRev hP.1, List.mem_reverse]
  exact hw

/-- Deleting `z`'s cut edge when inserting one new vertex `z` into a branch-free root set `R₁`
preserving branch-freeness: `(F_T(insert z R₁, π)).E = F₁.E \ {cutE}`. -/
lemma deletedEdges_insert_branchFree {T : MGraph} {r z : ℕ} (hT : IsRootedTree T r)
    {R₁ : Finset ℕ} (hR₁ : IsBranchFree T r R₁) (hR₁ne : R₁.Nonempty)
    (hzV : z ∈ T.V) (hz_not : z ∉ R₁) (hR₂ : IsBranchFree T r (insert z R₁))
    (π : ℕ → ℕ) (hord : IsEdgeOrder T π) :
    let F₁ := forestGivenRoots T r R₁ π
    let RF₁ := rootedForestGivenRoots T r R₁ π
    let rC := RF₁.root z
    let cutE := minEdgeOn π (walkEdges (T.forestPath z rC))
    rC ∈ R₁ ∧ rC ≠ z ∧ cutE ∈ F₁.E ∧
      deletedEdges T r (insert z R₁) π = insert cutE (deletedEdges T r R₁ π) ∧
      (forestGivenRoots T r (insert z R₁) π).E = F₁.E \ {cutE} := by
  classical
  dsimp only
  let F₁ := forestGivenRoots T r R₁ π
  let RF₁ := rootedForestGivenRoots T r R₁ π
  let rC := RF₁.root z
  let cutE := minEdgeOn π (walkEdges (T.forestPath z rC))
  have hRS₁ := forestGivenRoots_isRootedSpanningForest hT hR₁ hR₁ne π
  obtain ⟨hrC_R₁, hrC_conn⟩ := rootedForest_root_spec hRS₁ hzV
  have hF₁_conn_symm : F₁.Connected z rC := hrC_conn
  have hrC_ne_z : rC ≠ z := fun h => hz_not (h ▸ hrC_R₁)
  have hrC_V : rC ∈ T.V := hR₁.1 hrC_R₁
  have hP_F₁_disj : Disjoint (walkEdges (T.forestPath z rC)) (deletedEdges T r R₁ π) := by
    have hconn' : ({ T with E := T.E \ deletedEdges T r R₁ π } : MGraph).Connected z rC := hF₁_conn_symm
    rwa [connected_sdiff_iff_disjoint hT.isForest (hT.connected hzV hrC_V)] at hconn'
  have hP_ne : (walkEdges (T.forestPath z rC)).Nonempty := by
    have hP := forestPath_isPath hT.isForest (hT.connected hzV hrC_V)
    have hP_ne_nil : T.forestPath z rC ≠ [] := by
      intro hnil
      have hw := hP.1
      rw [hnil] at hw
      exact isWalk_nil_false_of_ne hrC_ne_z.symm hw
    rcases List.exists_cons_of_ne_nil hP_ne_nil with ⟨x, xs, hx⟩
    exact ⟨x.1, by rw [hx, walkEdges_cons]; exact Finset.mem_insert_self _ _⟩
  have hcut_in_P : cutE ∈ walkEdges (T.forestPath z rC) := minEdgeOn_mem hP_ne
  have hcut_in_T : cutE ∈ T.E := walkEdges_forestPath_sub_edges hT.isForest hcut_in_P
  have hcut_not_del₁ : cutE ∉ deletedEdges T r R₁ π :=
    Finset.disjoint_left.mp hP_F₁_disj hcut_in_P
  have hcut_in_F₁ : cutE ∈ F₁.E := Finset.mem_sdiff.mpr ⟨hcut_in_T, hcut_not_del₁⟩
  -- `l := lca T r z rC ∈ insert z R₁`; since `T[l, rC] ⊆ T[z, rC] ⊆ F₁`, `l ∈ R₁` forces `l = rC`.
  set l := lca T r z rC
  have hl_R₂ : l ∈ insert z R₁ := hR₂.2 z (Finset.mem_insert_self _ _) rC (Finset.mem_insert_of_mem hrC_R₁)
  have hl_mem_zrC : l ∈ T.walkVertices z (T.forestPath z rC) := lca_mem_forestPath hT hzV hrC_V
  have hT_zrC_sub_F₁ : walkEdges (T.forestPath z rC) ⊆ F₁.E :=
    fun e he => Finset.mem_sdiff.mpr ⟨walkEdges_forestPath_sub_edges hT.isForest he,
      Finset.disjoint_left.mp hP_F₁_disj he⟩
  have hF₁_conn_zrC_vert : ∀ w ∈ T.walkVertices z (T.forestPath z rC), F₁.Connected w rC := by
    intro w hw
    obtain ⟨P₁, P₂, hsplit, _, hW₂⟩ :=
      walkVertices_mem_split (forestPath_isPath hT.isForest (hT.connected hzV hrC_V)).1 hw
    have hP₂_sub : walkEdges P₂ ⊆ walkEdges (T.forestPath z rC) := by
      intro f hf; rw [hsplit, walkEdges_append, Finset.mem_union]; exact Or.inr hf
    have hsubF : ∀ e ∈ F₁.E, F₁.tail e = T.tail e ∧ F₁.head e = T.head e := fun _ _ => ⟨rfl, rfl⟩
    exact ⟨P₂, isWalk_of_edges_mem hsubF hW₂ (fun f hf => hT_zrC_sub_F₁ (hP₂_sub hf))⟩
  have hl_conn_rC : F₁.Connected l rC := hF₁_conn_zrC_vert l hl_mem_zrC
  have hl_cases : l = z ∨ l = rC := by
    rw [Finset.mem_insert] at hl_R₂
    rcases hl_R₂ with hEq | hlR₁
    · exact Or.inl hEq
    · right
      by_contra hne
      exact forestGivenRoots_not_connected_roots hT hR₁ hR₁ne π hlR₁ hrC_R₁ hne hl_conn_rC
  have hcut_in_del₂ : cutE ∈ deletedEdges T r (insert z R₁) π := by
    have hR₂ne : (insert z R₁).Nonempty := ⟨z, Finset.mem_insert_self _ _⟩
    unfold deletedEdges
    rw [ite_eq_left_iff.mpr (fun h => absurd hR₂ne h), Finset.mem_image]
    rcases hl_cases with h_eq_z | h_eq_rC
    · -- `z` is strict ancestor of `rC`, so `rootParent T r (insert z R₁) rC = z`.
      have hz_anc_rC : IsAncestor T r z rC := by
        rw [← h_eq_z]; exact lca_isAncestor_right hT hzV hrC_V
      have hrC_ne_top : rC ≠ topRoot T r (insert z R₁) := by
        intro hEq
        have htop_anc := topRoot_isAncestor hT hR₂ hR₂ne (Finset.mem_insert_self z R₁)
        rw [← hEq] at htop_anc
        exact hrC_ne_z (isAncestor_antisymm hT hrC_V hzV htop_anc hz_anc_rC)
      have hrC_er : rC ∈ (insert z R₁).erase (topRoot T r (insert z R₁)) :=
        Finset.mem_erase.mpr ⟨hrC_ne_top, Finset.mem_insert_of_mem hrC_R₁⟩
      obtain ⟨hpR₂, hp_ne, hp_anc, hp_max⟩ := rootParent_spec hT hR₂ hR₂ne hrC_er
      have hp_eq_z : rootParent T r (insert z R₁) rC = z := by
        have hzp : IsAncestor T r z (rootParent T r (insert z R₁) rC) :=
          hp_max z (Finset.mem_insert_self _ _) hrC_ne_z.symm hz_anc_rC
        by_contra hne_pz
        have hp_in_R₁ : rootParent T r (insert z R₁) rC ∈ R₁ :=
          (Finset.mem_insert.mp hpR₂).resolve_left hne_pz
        have hp_mem_walk : rootParent T r (insert z R₁) rC ∈ T.walkVertices z (T.forestPath z rC) := by
          have hzr := (forestPath_eq_of_isAncestor hT hrC_V hz_anc_rC).1
          have hp_rC : rootParent T r (insert z R₁) rC ∈ T.walkVertices rC (T.forestPath rC r) := hp_anc
          rw [hzr, walkVertices_append] at hp_rC
          rcases List.mem_append.mp hp_rC with h_on_rCz | h_on_zr
          · exact mem_walkVertices_forestPath_rev hT.isForest (hT.connected hrC_V hzV) h_on_rCz
          · have hmem_z_r : rootParent T r (insert z R₁) rC ∈ T.walkVertices z (T.forestPath z r) :=
              List.mem_cons_of_mem _ h_on_zr
            exact absurd (isAncestor_antisymm hT hzV (hR₂.1 hpR₂) hzp hmem_z_r) (Ne.symm hne_pz)
        have hconn_pr : F₁.Connected (rootParent T r (insert z R₁) rC) rC :=
          hF₁_conn_zrC_vert _ hp_mem_walk
        exact forestGivenRoots_not_connected_roots hT hR₁ hR₁ne π hp_in_R₁ hrC_R₁ hp_ne hconn_pr
      refine ⟨rC, hrC_er, ?_⟩
      dsimp only [deletedEdge]
      rw [hp_eq_z, walkEdges_forestPath_comm hT.isForest (hT.connected hrC_V hzV)]
    · -- `rC` is strict ancestor of `z`, so `rootParent T r (insert z R₁) z = rC`.
      have hrC_anc_z : IsAncestor T r rC z := by
        rw [← h_eq_rC]; exact lca_isAncestor_left hT hzV hrC_V
      have hz_ne_top : z ≠ topRoot T r (insert z R₁) := by
        intro hEq
        have htop_anc := topRoot_isAncestor hT hR₂ hR₂ne (Finset.mem_insert_of_mem hrC_R₁)
        rw [← hEq] at htop_anc
        exact hrC_ne_z.symm (isAncestor_antisymm hT hzV hrC_V htop_anc hrC_anc_z)
      have hz_er : z ∈ (insert z R₁).erase (topRoot T r (insert z R₁)) :=
        Finset.mem_erase.mpr ⟨hz_ne_top, Finset.mem_insert_self z R₁⟩
      obtain ⟨hpR₂, hp_ne, hp_anc, hp_max⟩ := rootParent_spec hT hR₂ hR₂ne hz_er
      have hp_eq_rC : rootParent T r (insert z R₁) z = rC := by
        have hrCp : IsAncestor T r rC (rootParent T r (insert z R₁) z) :=
          hp_max rC (Finset.mem_insert_of_mem hrC_R₁) hrC_ne_z hrC_anc_z
        by_contra hne_pr
        have hp_in_R₁ : rootParent T r (insert z R₁) z ∈ R₁ :=
          (Finset.mem_insert.mp hpR₂).resolve_left hp_ne
        have hp_mem_walk : rootParent T r (insert z R₁) z ∈ T.walkVertices z (T.forestPath z rC) := by
          have hzrc := (forestPath_eq_of_isAncestor hT hzV hrC_anc_z).1
          have hp_z : rootParent T r (insert z R₁) z ∈ T.walkVertices z (T.forestPath z r) := hp_anc
          rw [hzrc, walkVertices_append] at hp_z
          rcases List.mem_append.mp hp_z with h_on_zrC | h_on_rCr
          · exact h_on_zrC
          · have hmem_rC_r : rootParent T r (insert z R₁) z ∈ T.walkVertices rC (T.forestPath rC r) :=
              List.mem_cons_of_mem _ h_on_rCr
            exact absurd (isAncestor_antisymm hT hrC_V (hR₂.1 hpR₂) hrCp hmem_rC_r) (Ne.symm hne_pr)
        have hconn_pr : F₁.Connected (rootParent T r (insert z R₁) z) rC :=
          hF₁_conn_zrC_vert _ hp_mem_walk
        exact forestGivenRoots_not_connected_roots hT hR₁ hR₁ne π hp_in_R₁ hrC_R₁ hne_pr hconn_pr
      refine ⟨z, hz_er, ?_⟩
      dsimp only [deletedEdge]
      rw [hp_eq_rC]
  have hsub_del : insert cutE (deletedEdges T r R₁ π) ⊆ deletedEdges T r (insert z R₁) π := by
    intro e he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he₁
    · exact hcut_in_del₂
    · exact deletedEdges_mono hT hR₁ hR₂ hR₁ne (Finset.subset_insert _ _) π hord he₁
  have hcard_ins : (insert cutE (deletedEdges T r R₁ π)).card =
      (deletedEdges T r (insert z R₁) π).card := by
    have h1 := deletedEdges_card hT hR₁ hR₁ne π
    have h2 := deletedEdges_card hT hR₂ ⟨z, Finset.mem_insert_self _ _⟩ π
    rw [Finset.card_insert_of_notMem hcut_not_del₁, Finset.card_insert_of_notMem hz_not] at *
    omega
  have hdel_eq : deletedEdges T r (insert z R₁) π = insert cutE (deletedEdges T r R₁ π) :=
    (Finset.eq_of_subset_of_card_le hsub_del hcard_ins.ge).symm
  refine ⟨hrC_R₁, hrC_ne_z, hcut_in_F₁, hdel_eq, ?_⟩
  change T.E \ deletedEdges T r (insert z R₁) π = (T.E \ deletedEdges T r R₁ π) \ {cutE}
  rw [hdel_eq]
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ## `refineDecomp` piece tree bounds (`WBlockAt`) -/

/-- Every piece `W ∈ refineDecomp W_T F₀` spans a tree inside `F₀`, so
`W.card = (inducedEdges F₀ W).card + 1`, giving `W_init.card ≤ F₀.E.card`,
`∑ inducedEdges = F₀.E.card`, and `∑ W.card ≤ 2 * F₀.E.card ≤ 2 * G₀.n`. -/
lemma refineDecomp_total_bounds {G₀ T₀ : MGraph} {r₀ : ℕ}
    (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V)
    {R : Finset ℕ} (hR : IsBranchFree T₀ r₀ R) (hRne : R.Nonempty) (π : ℕ → ℕ)
    (W_T : Finset (Finset ℕ))
    (hW_pc : ∀ W₀ ∈ W_T, PathConvex T₀ W₀)
    (hW_disj : ∀ W₀₁ ∈ W_T, ∀ W₀₂ ∈ W_T, W₀₁ ≠ W₀₂ →
      Disjoint (inducedEdges T₀ W₀₁) (inducedEdges T₀ W₀₂))
    (hW_cov : W_T.biUnion (inducedEdges T₀) = T₀.E)
    (hBW_sub : boundary W_T ⊆ R) :
    let F₀ := forestGivenRoots T₀ r₀ R π
    let 𝒲 := refineDecomp W_T F₀
    (∀ W ∈ 𝒲, (inducedEdges F₀ W).Nonempty ∧ W.card = (inducedEdges F₀ W).card + 1) ∧
    𝒲.card ≤ F₀.E.card ∧
    (∑ W ∈ 𝒲, (inducedEdges F₀ W).card) = F₀.E.card ∧
    (∑ W ∈ 𝒲, W.card) ≤ 2 * F₀.E.card ∧
    F₀.E.card ≤ G₀.n := by
  classical
  dsimp only
  let F₀ := forestGivenRoots T₀ r₀ R π
  let 𝒲 := refineDecomp W_T F₀
  have hVolB : ∀ W₀ ∈ W_T, (G₀.vol (W₀ \ boundary W_T) : ℝ) ≤ ((2 * G₀.E.card : ℕ) : ℝ) := by
    intro W₀ _
    exact_mod_cast (vol_le_two_mul_filter_card G₀ (W₀ \ boundary W_T)).trans
      (Nat.mul_le_mul_left 2 (Finset.card_filter_le _ _))
  have href := refinement_decomp_spec hT₀ hTV hR hRne π W_T hW_pc hW_disj hW_cov hBW_sub hVolB
  have hRS := forestGivenRoots_isRootedSpanningForest hT₀ hR hRne π
  have hF_sub : T₀.IsSubgraph F₀ := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have hpiece : ∀ W ∈ 𝒲, (inducedEdges F₀ W).Nonempty ∧ W.card = (inducedEdges F₀ W).card + 1 := by
    intro W hW
    have hW_mem_copy := hW
    simp only [𝒲, refineDecomp, Finset.mem_filter, Finset.mem_image, Finset.mem_product] at hW
    obtain ⟨⟨p, hp, hWp⟩, hne_e⟩ := hW
    rw [← hWp] at hW_mem_copy hne_e ⊢
    refine ⟨hne_e, ?_⟩
    have hpcT : PathConvex T₀ (p.1 ∩ p.2) := (href.1 _ hW_mem_copy).1
    let H : MGraph := { V := p.1 ∩ p.2, E := inducedEdges F₀ (p.1 ∩ p.2), tail := F₀.tail, head := F₀.head }
    have hH_val : H.IsValid := fun e he => (Finset.mem_filter.mp he).2
    have hH_sub_F₀ : F₀.IsSubgraph H := ⟨hpcT.2.1, Finset.filter_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩
    have hH_forest : H.IsForest := isForest_subgraph hRS.1 hH_sub_F₀ hH_val
    have hp2_comp := hp.2
    rw [components, Finset.mem_image] at hp2_comp
    obtain ⟨x₀, _, hx₀_eq⟩ := hp2_comp
    have hconnH : ∀ u ∈ p.1 ∩ p.2, ∀ v ∈ p.1 ∩ p.2, H.Connected u v := by
      intro u hu v hv
      have hu2 : u ∈ compOf F₀ x₀ := hx₀_eq ▸ (Finset.mem_inter.mp hu).2
      have hv2 : v ∈ compOf F₀ x₀ := hx₀_eq ▸ (Finset.mem_inter.mp hv).2
      rw [mem_compOf_iff] at hu2 hv2
      have hconnF : F₀.Connected u v := connected_trans (connected_symm hu2.2) hv2.2
      have hP_F := forestPath_isPath hRS.1 hconnF
      have hP_T : T₀.IsPath u v (F₀.forestPath u v) := isPath_of_subgraph hF_sub hP_F
      have hPF_eq_T : T₀.forestPath u v = F₀.forestPath u v := forestPath_eq_of_isPath hT₀.isForest hP_T
      have hverts_eq : F₀.walkVertices u (F₀.forestPath u v) = T₀.walkVertices u (T₀.forestPath u v) := by
        rw [hPF_eq_T]
        exact (isWalk_of_subgraph hF_sub hP_F.1).2.symm
      have h_edges : ∀ f ∈ walkEdges (F₀.forestPath u v), f ∈ H.E := by
        intro f hf
        obtain ⟨y, hyP, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
        have hyF : y.1 ∈ F₀.E := IsWalk_edges_mem hP_F.1 hyP
        have hends := IsWalk_mem_ends hP_F.1 hyP
        have h_in_W : ∀ w ∈ F₀.walkVertices u (F₀.forestPath u v), w ∈ p.1 ∩ p.2 := by
          intro w hw
          rw [hverts_eq] at hw
          exact hpcT.2.2 u hu v hv w hw
        have ht_mem : F₀.tail y.1 ∈ p.1 ∩ p.2 := by
          rcases y with ⟨e, _ | _⟩ <;> simp only [MGraph.src, MGraph.dst] at hends
          · exact h_in_W _ hends.2
          · exact h_in_W _ hends.1
        have hh_mem : F₀.head y.1 ∈ p.1 ∩ p.2 := by
          rcases y with ⟨e, _ | _⟩ <;> simp only [MGraph.src, MGraph.dst] at hends
          · exact h_in_W _ hends.1
          · exact h_in_W _ hends.2
        exact Finset.mem_filter.mpr ⟨hyF, ht_mem, hh_mem⟩
      have hsubH : ∀ e ∈ H.E, H.tail e = F₀.tail e ∧ H.head e = F₀.head e := fun _ _ => ⟨rfl, rfl⟩
      exact ⟨F₀.forestPath u v, isWalk_of_edges_mem hsubH hP_F.1 h_edges⟩
    have hST : H.IsSpanningTreeOn (p.1 ∩ p.2) := ⟨hH_forest, rfl, hconnH⟩
    exact (spanningTree_edge_card hST hpcT.1).symm
  have hsum_eq : (∑ W ∈ 𝒲, (inducedEdges F₀ W).card) = F₀.E.card := by
    rw [← href.2.2.1, Finset.card_biUnion]
    intro W₁ hW₁ W₂ hW₂ hne
    exact href.2.2.2.1 W₁ hW₁ W₂ hW₂ hne
  have hW_card_le : 𝒲.card ≤ F₀.E.card := by
    calc 𝒲.card = ∑ _ ∈ 𝒲, 1 := by simp
      _ ≤ ∑ W ∈ 𝒲, (inducedEdges F₀ W).card :=
          Finset.sum_le_sum (fun W hW => Finset.card_pos.mpr (hpiece W hW).1)
      _ = F₀.E.card := hsum_eq
  have hV_sum_le : (∑ W ∈ 𝒲, W.card) ≤ 2 * F₀.E.card := by
    calc ∑ W ∈ 𝒲, W.card
        = ∑ W ∈ 𝒲, ((inducedEdges F₀ W).card + 1) :=
          Finset.sum_congr rfl (fun W hW => (hpiece W hW).2)
      _ ≤ ∑ W ∈ 𝒲, 2 * (inducedEdges F₀ W).card := by
          refine Finset.sum_le_sum (fun W hW => ?_)
          have h1 : 1 ≤ (inducedEdges F₀ W).card := Finset.card_pos.mpr (hpiece W hW).1
          omega
      _ = 2 * ∑ W ∈ 𝒲, (inducedEdges F₀ W).card := (Finset.mul_sum _ _ _).symm
      _ = 2 * F₀.E.card := by rw [hsum_eq]
  have hF_le : F₀.E.card ≤ G₀.n := by
    have hsub : F₀.E ⊆ T₀.E := Finset.sdiff_subset
    have hTc := spanningTree_edge_card hT₀.1 ⟨r₀, hT₀.2⟩
    have hm1 := Finset.card_le_card hsub
    rw [hTV] at hTc
    change F₀.E.card ≤ G₀.V.card
    omega
  exact ⟨hpiece, hW_card_le, hsum_eq, hV_sum_le, hF_le⟩

/-! ## `IsLSST` scaling and empty-edge star tree -/

/-- Multiplying vertex/edge weights `v` by a positive scalar preserves `IsLSST`. -/
lemma isLSST_smul_weights {G T : MGraph} {ℓ v : ℕ → ℝ} {γ c : ℝ} (hc : 0 < c)
    (h : IsLSST G ℓ (fun e => c * v e) γ T) :
    IsLSST G ℓ v γ T := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hsum := h.2.2.2
  have h1 : ∑ e ∈ G.E, (c * v e) * treeStretch G T ℓ e =
      c * ∑ e ∈ G.E, v e * treeStretch G T ℓ e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => by ring)
  have h2 : G.norm1 (fun e => c * v e) = c * G.norm1 v := by
    unfold MGraph.norm1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => by
      rw [abs_mul, abs_of_pos hc])
  rw [h1, h2] at hsum
  nlinarith

/-- Any star graph over a `Nodup` listing `vList` of `G.V` is a valid `IsLSST` when `G.E = ∅`. -/
lemma starTree_isLSST_empty {G : MGraph} (hV : G.V.Nonempty) (hE : G.E = ∅)
    {γ : ℝ} (_hγ : 0 ≤ γ) {vList : List ℕ}
    (hlen : vList.length = G.n) (_hnd : vList.Nodup) (hmem : ∀ v, v ∈ vList ↔ v ∈ G.V) :
    let T_star : MGraph :=
      { V := G.V
        E := Finset.range (G.n - 1)
        tail := fun _ => vList.getD 0 0
        head := fun i => vList.getD (i + 1) 0 }
    IsLSST G (fun _ => 1) (fun _ => 1) γ T_star := by
  intro T_star
  have hpos : 0 < G.n := Finset.card_pos.mpr hV
  have hval : T_star.IsValid := by
    intro e he
    rw [Finset.mem_range] at he
    change vList.getD 0 0 ∈ G.V ∧ vList.getD (e + 1) 0 ∈ G.V
    rw [← hmem, ← hmem]
    refine ⟨?_, ?_⟩
    · have h0 : 0 < vList.length := by omega
      rw [List.getD_eq_getElem _ _ h0]
      exact List.getElem_mem h0
    · have h1 : e + 1 < vList.length := by omega
      rw [List.getD_eq_getElem _ _ h1]
      exact List.getElem_mem h1
  have hconn : ∀ u ∈ G.V, ∀ w ∈ G.V, T_star.Connected u w := by
    have hconn0 : ∀ i (hi : i < vList.length), T_star.Connected (vList.getD 0 0) (vList[i]'hi) := by
      intro i hi
      cases i with
      | zero =>
        have h0 : vList.getD 0 0 = vList[0]'hi := List.getD_eq_getElem _ _ hi
        rw [h0]
        exact connected_refl _ _
      | succ k =>
        have hk : k ∈ T_star.E := Finset.mem_range.mpr (by omega)
        have hget : T_star.head k = vList[k + 1]'hi := List.getD_eq_getElem _ _ hi
        have htail : T_star.tail k = vList.getD 0 0 := rfl
        rw [← hget, ← htail]
        exact connected_of_edge hk
    intro u hu w hw
    have huL : u ∈ vList := (hmem u).mpr hu
    have hwL : w ∈ vList := (hmem w).mpr hw
    obtain ⟨iu, hiu, rfl⟩ := List.mem_iff_getElem.mp huL
    obtain ⟨iw, hiw, rfl⟩ := List.mem_iff_getElem.mp hwL
    exact connected_trans (connected_symm (hconn0 iu hiu)) (hconn0 iw hiw)
  have hcard : T_star.E.card + 1 = G.V.card := by
    change (Finset.range (G.n - 1)).card + 1 = G.n
    rw [Finset.card_range]
    omega
  refine ⟨isForest_of_connected_card hval rfl hV hconn hcard, ?_, ?_, ?_⟩
  · intro e _ heG; rw [hE] at heG; exact absurd heG (Finset.notMem_empty _)
  · intro e heG; rw [hE] at heG; exact absurd heG (Finset.notMem_empty _)
  · rw [hE, Finset.sum_empty, MGraph.norm1, hE, Finset.sum_empty, mul_zero]

/-! ## Approximate `(5 / 4)` congestion order -/

/-- Integer-floored congestion `congSum f = ∑_{e ∈ G₀.E, f ∈ T₀[e]} ⌊m_e * 2^S_div / ℓ_int e⌋`
with `2^S_div ≥ 16 * ℓ_int e` yields `IsApproxCongOrder G_v T₀ ℓ_v (5 / 4) π` whenever `π`
sorts `T₀.E` non-decreasingly by `congSum`. -/
lemma approxCongOrder_of_floor {G₀ T₀ : MGraph} (hE : G₀.E.Nonempty)
    {v ℓ₀ : ℕ → ℝ} (hv : ∀ e ∈ G₀.E, 0 < v e)
    {ℓ_int : ℕ → ℕ} {P_fp S_div : ℕ}
    (hℓ_pos : ∀ e ∈ G₀.E, 0 < ℓ_int e)
    (hℓ_lt : ∀ e ∈ G₀.E, 16 * ℓ_int e ≤ 2 ^ S_div)
    (hℓ_eq : ∀ e ∈ G₀.E, ℓ₀ e = (ℓ_int e : ℝ) / (2 : ℝ) ^ P_fp)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T₀ π)
    (hsort : ∀ f ∈ T₀.E, ∀ g ∈ T₀.E, π f ≤ π g →
      (∑ e ∈ G₀.E, if f ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e))
          then edgeMult G₀ v e * 2 ^ S_div / ℓ_int e else 0) ≤
      (∑ e ∈ G₀.E, if g ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e))
          then edgeMult G₀ v e * 2 ^ S_div / ℓ_int e else 0)) :
    IsApproxCongOrder (weightedCopyGraph G₀ v) T₀ (weightedCopyLen G₀ ℓ₀) (5 / 4) π := by
  classical
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let q_nat : ℕ → ℕ := fun e => edgeMult G₀ v e * 2 ^ S_div / ℓ_int e
  let scale : ℝ := (2 : ℝ) ^ S_div / (2 : ℝ) ^ P_fp
  have hscale_pos : 0 < scale := by positivity
  let c_exact : ℕ → ℝ := fun f =>
    ∑ e ∈ G₀.E, if f ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e))
      then ((edgeMult G₀ v e : ℝ) * (2 : ℝ) ^ S_div) / (ℓ_int e : ℝ) else 0
  let c_nat : ℕ → ℝ := fun f =>
    ∑ e ∈ G₀.E, if f ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e))
      then (q_nat e : ℝ) else 0
  have hcong_eq : ∀ f, congestion G_v T₀ ℓ_v f * scale = c_exact f := by
    intro f
    unfold congestion G_v ℓ_v
    have hsum := weightedCopyGraph_sum_eq hE v (fun e =>
      if f ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) then 1 / ℓ₀ e else 0)
    have hlhs : ∑ e' ∈ (weightedCopyGraph G₀ v).E,
        (if f ∈ walkEdges (T₀.forestPath ((weightedCopyGraph G₀ v).tail e')
            ((weightedCopyGraph G₀ v).head e'))
         then 1 / weightedCopyLen G₀ ℓ₀ e' else 0) =
        ∑ e' ∈ (weightedCopyGraph G₀ v).E,
          (if f ∈ walkEdges (T₀.forestPath (G₀.tail (origEdge (copyMod G₀) e'))
              (G₀.head (origEdge (copyMod G₀) e')))
           then 1 / ℓ₀ (origEdge (copyMod G₀) e') else 0) := by
      refine Finset.sum_congr rfl (fun e' he' => ?_)
      have hm := weightedCopyGraph_origEdge_mem hE he'
      rw [hm.2.1, hm.2.2]
      rfl
    rw [hlhs, hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e he => ?_)
    split_ifs
    · rw [hℓ_eq e he]
      dsimp only [scale]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hℓ_pos e he)),
        (by positivity : (2 : ℝ) ^ P_fp ≠ 0)]
    · ring
  have hq_sand : ∀ e ∈ G₀.E,
      (15 / 16 : ℝ) * (((edgeMult G₀ v e : ℝ) * (2 : ℝ) ^ S_div) / (ℓ_int e : ℝ)) ≤ (q_nat e : ℝ) ∧
      (q_nat e : ℝ) ≤ ((edgeMult G₀ v e : ℝ) * (2 : ℝ) ^ S_div) / (ℓ_int e : ℝ) := by
    intro e he
    have hm1 : 1 ≤ edgeMult G₀ v e := edgeMult_pos hE hv he
    have hℓp : (0 : ℝ) < (ℓ_int e : ℝ) := Nat.cast_pos.mpr (hℓ_pos e he)
    have hdiv_ge : (16 : ℝ) ≤ ((edgeMult G₀ v e : ℝ) * (2 : ℝ) ^ S_div) / (ℓ_int e : ℝ) := by
      rw [le_div_iff₀ hℓp]
      have h16 : (16 * ℓ_int e : ℝ) ≤ (2 : ℝ) ^ S_div := by exact_mod_cast hℓ_lt e he
      have hm1r : (1 : ℝ) ≤ (edgeMult G₀ v e : ℝ) := by exact_mod_cast hm1
      nlinarith
    have hrem_lt : edgeMult G₀ v e * 2 ^ S_div < (q_nat e + 1) * ℓ_int e :=
      Nat.lt_of_lt_of_eq (Nat.lt_mul_div_succ (edgeMult G₀ v e * 2 ^ S_div) (hℓ_pos e he))
        (Nat.mul_comm _ _)
    have hmul_le : q_nat e * ℓ_int e ≤ edgeMult G₀ v e * 2 ^ S_div :=
      Nat.div_mul_le_self _ _
    have hlo_r : ((edgeMult G₀ v e : ℝ) * (2 : ℝ) ^ S_div) / (ℓ_int e : ℝ) - 1 < (q_nat e : ℝ) := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hℓp]
      have : ((edgeMult G₀ v e * 2 ^ S_div : ℕ) : ℝ) < ((q_nat e + 1) * ℓ_int e : ℕ) :=
        by exact_mod_cast hrem_lt
      push_cast at this
      linarith
    have hhi_r : (q_nat e : ℝ) ≤ ((edgeMult G₀ v e : ℝ) * (2 : ℝ) ^ S_div) / (ℓ_int e : ℝ) := by
      rw [le_div_iff₀ hℓp]
      have : ((q_nat e * ℓ_int e : ℕ) : ℝ) ≤ ((edgeMult G₀ v e * 2 ^ S_div : ℕ) : ℝ) :=
        by exact_mod_cast hmul_le
      push_cast at this
      exact this
    exact ⟨by linarith, hhi_r⟩
  have hlo : ∀ f ∈ T₀.E, congestion G_v T₀ ℓ_v f ≤ (16 / 15 : ℝ) / scale * c_nat f := by
    intro f hf
    have hsum1 : c_exact f ≤ (16 / 15 : ℝ) * c_nat f := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun e he => ?_)
      split_ifs
      · linarith [(hq_sand e he).1]
      · simp
    rw [← hcong_eq f] at hsum1
    rw [← le_div_iff₀ hscale_pos] at hsum1
    linarith [show (16 / 15 : ℝ) * c_nat f / scale = (16 / 15 : ℝ) / scale * c_nat f by ring]
  have hhi : ∀ f ∈ T₀.E, (16 / 15 : ℝ) / scale * c_nat f ≤ (5 / 4 : ℝ) * congestion G_v T₀ ℓ_v f := by
    intro f hf
    have hsum2 : c_nat f ≤ c_exact f := by
      refine Finset.sum_le_sum (fun e he => ?_)
      split_ifs
      · exact (hq_sand e he).2
      · exact le_rfl
    rw [← hcong_eq f] at hsum2
    have hsc_div : c_nat f / scale ≤ congestion G_v T₀ ℓ_v f :=
      (div_le_iff₀ hscale_pos).mpr hsum2
    have hℓ_pos_r : ∀ e ∈ G₀.E, 0 < ℓ₀ e := fun e he => by
      rw [hℓ_eq e he]; exact div_pos (Nat.cast_pos.mpr (hℓ_pos e he)) (by positivity)
    have hmul : (16 / 15 : ℝ) * (c_nat f / scale) ≤ (5 / 4 : ℝ) * congestion G_v T₀ ℓ_v f := by
      have h16_le : (16 / 15 : ℝ) ≤ (5 / 4 : ℝ) := by norm_num
      have hcong0 := congestion_nonneg G_v T₀
        (fun _ he' => weightedCopyLen_pos hE hℓ_pos_r he') f
      calc (16 / 15 : ℝ) * (c_nat f / scale)
          ≤ (16 / 15 : ℝ) * congestion G_v T₀ ℓ_v f := mul_le_mul_of_nonneg_left hsc_div (by positivity)
        _ ≤ (5 / 4 : ℝ) * congestion G_v T₀ ℓ_v f := mul_le_mul_of_nonneg_right h16_le hcong0
    linarith [show (16 / 15 : ℝ) / scale * c_nat f = (16 / 15 : ℝ) * (c_nat f / scale) by ring]
  refine isApproxCongOrder_of_approx (by norm_num) hlo hhi hord (fun f hf g hg hle => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs := hsort f hf g hg hle
  have hsn : (c_nat f : ℝ) ≤ (c_nat g : ℝ) := by
    have : ∀ h, c_nat h = ((∑ e ∈ G₀.E, if h ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e))
        then q_nat e else 0 : ℕ) : ℝ) := fun h => by
      dsimp only [c_nat]; push_cast; refine Finset.sum_congr rfl (fun _ _ => by split_ifs <;> simp)
    rw [this f, this g]
    exact_mod_cast hs
  exact hsn

/-! ## Exact rational representation of `levelStretchBound` -/

/-- Express `levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) e` as an exact natural ratio
`rawNum / ℓ_int e` using `ℓ_safe f = if f ∈ G₀.E then ℓ_int f else 0` (so bridge edges carry
integer weight `0`, matching `safeLen G₀ ℓ₀`). -/
lemma levelStretchBound_rat_eq {G₀ T₀ : MGraph} (r₀ P_fp : ℕ) (π : ℕ → ℕ)
    (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V) (hG₀ : G₀.IsValid)
    {ℓ₀ : ℕ → ℝ} {ℓ_int : ℕ → ℕ}
    (hℓ_pos : ∀ f ∈ G₀.E, 0 < ℓ_int f)
    (hℓ_eq : ∀ f ∈ G₀.E, ℓ₀ f = (ℓ_int f : ℝ) / (2 : ℝ) ^ P_fp)
    {e : ℕ} (he : e ∈ G₀.E) :
    let D := hldDepthBound G₀.n
    let ℓ_safe := fun f => if f ∈ G₀.E then ℓ_int f else 0
    let num_i := fun i =>
      let F_i := rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π
      if F_i.root (G₀.tail e) = F_i.root (G₀.head e) then
        ∑ f ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)), ℓ_safe f
      else
        (∑ f ∈ walkEdges (T₀.forestPath (G₀.tail e) (F_i.root (G₀.tail e))), ℓ_safe f) +
          (∑ f ∈ walkEdges (T₀.forestPath (G₀.head e) (F_i.root (G₀.head e))), ℓ_safe f)
    let rawNum := 2 * ∑ i ∈ Finset.range (D + 1), (ℓ_int e + num_i i)
    levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) e = (rawNum : ℝ) / (ℓ_int e : ℝ) := by
  classical
  dsimp only
  let D := hldDepthBound G₀.n
  let ℓ_safe := fun f => if f ∈ G₀.E then ℓ_int f else 0
  let num_i := fun i =>
    let F_i := rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π
    if F_i.root (G₀.tail e) = F_i.root (G₀.head e) then
      ∑ f ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)), ℓ_safe f
    else
      (∑ f ∈ walkEdges (T₀.forestPath (G₀.tail e) (F_i.root (G₀.tail e))), ℓ_safe f) +
        (∑ f ∈ walkEdges (T₀.forestPath (G₀.head e) (F_i.root (G₀.head e))), ℓ_safe f)
  let rawNum := 2 * ∑ i ∈ Finset.range (D + 1), (ℓ_int e + num_i i)
  have huV : G₀.tail e ∈ T₀.V := hTV ▸ (hG₀ e he).1
  have hvV : G₀.head e ∈ T₀.V := hTV ▸ (hG₀ e he).2
  have hT₀n : T₀.V.card = G₀.n := congrArg Finset.card hTV
  unfold levelStretchBound
  rw [hT₀n]
  change 2 * ∑ i ∈ Finset.range (D + 1),
      (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G₀ (safeLen G₀ ℓ₀) e =
    (rawNum : ℝ) / (ℓ_int e : ℝ)
  have hℓe_safe : safeLen G₀ ℓ₀ e = (ℓ_int e : ℝ) / (2 : ℝ) ^ P_fp := by
    rw [safeLen_eq_of_mem ℓ₀ he, hℓ_eq e he]
  have hℓe_pos : (0 : ℝ) < (ℓ_int e : ℝ) := Nat.cast_pos.mpr (hℓ_pos e he)
  have hterm : ∀ i ∈ Finset.range (D + 1),
      (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G₀ (safeLen G₀ ℓ₀) e =
        ((ℓ_int e + num_i i : ℕ) : ℝ) / (ℓ_int e : ℝ) := by
    intro i _
    let R_i := levelRoots T₀ r₀ i
    let F_i := rootedForestGivenRoots T₀ r₀ R_i π
    have hBi_bf : IsBranchFree T₀ r₀ (levelRoots T₀ r₀ i) :=
      upClosure_levelRoots hT₀ ▸ upClosure_isBranchFree hT₀ levelRoots_subset
    have hBi_ne : (levelRoots T₀ r₀ i).Nonempty := ⟨r₀, root_mem_levelRoots hT₀⟩
    have hRS_i := forestGivenRoots_isRootedSpanningForest hT₀ hBi_bf hBi_ne π
    have hF_sub_T : T₀.IsSubgraph F_i.F :=
      ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsum_safe : ∀ {a b : ℕ} (hconn : F_i.F.Connected a b),
        walkLength (safeLen G₀ ℓ₀) (F_i.F.forestPath a b) / safeLen G₀ ℓ₀ e =
          ((∑ f ∈ walkEdges (T₀.forestPath a b), ℓ_safe f : ℕ) : ℝ) / (ℓ_int e : ℝ) := by
      intro a b hconn
      have hPF := forestPath_isPath hRS_i.1 hconn
      have hPT := isPath_of_subgraph hF_sub_T hPF
      have hP_eq : F_i.F.forestPath a b = T₀.forestPath a b :=
        (forestPath_eq_of_isPath hT₀.isForest hPT).symm
      rw [walkLength_eq_sum_of_isPath _ hPF, hP_eq, hℓe_safe]
      have hsum_num : ∑ f ∈ walkEdges (T₀.forestPath a b), safeLen G₀ ℓ₀ f =
          ((∑ f ∈ walkEdges (T₀.forestPath a b), ℓ_safe f : ℕ) : ℝ) / (2 : ℝ) ^ P_fp := by
        rw [Nat.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        dsimp only [safeLen, ℓ_safe]
        split_ifs with hf
        · exact hℓ_eq f hf
        · simp
      rw [hsum_num]
      field_simp [hℓe_pos.ne', (by positivity : (2 : ℝ) ^ P_fp ≠ 0)]
    unfold RootedForest.stretch
    dsimp only [num_i, F_i, R_i]
    by_cases hrt : (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).root (G₀.tail e) =
        (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).root (G₀.head e)
    · simp only [hrt, ↓reduceIte]
      have h1 := (rootedForest_root_spec hRS_i huV).2
      have h2 := (rootedForest_root_spec hRS_i hvV).2
      have hconn_uv : F_i.F.Connected (G₀.tail e) (G₀.head e) :=
        connected_trans h1 (connected_symm (hrt ▸ h2))
      rw [hsum_safe hconn_uv]
      push_cast; field_simp [hℓe_pos.ne']
    · simp only [hrt, ↓reduceIte]
      have hconn1 : F_i.F.Connected (G₀.tail e) (F_i.root (G₀.tail e)) :=
        (rootedForest_root_spec hRS_i huV).2
      have hconn2 : F_i.F.Connected (G₀.head e) (F_i.root (G₀.head e)) :=
        (rootedForest_root_spec hRS_i hvV).2
      rw [add_div, hsum_safe hconn1, hsum_safe hconn2]
      dsimp only [F_i, R_i]
      push_cast; field_simp [hℓe_pos.ne']
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  dsimp only [rawNum]
  push_cast
  ring

end MinCostFlow.LSF.Program
