module

public import MinCostFlow.MinRatio.WireFindCycleSpec
public import MinCostFlow.MinRatio.PathApplyAccounting
public import MinCostFlow.LinkCut.PathProg.Vals
import MinCostFlow.MinRatio.TreeEdit
import MinCostFlow.MinRatio.TreeEditAccountDirection
import MinCostFlow.LSF.Walks
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic

/-!
# Path-summary accounting and cycle-evaluation algebra

Proves the semantic lemmas behind `evalCycleBody` (`WireEval.lean`):
1. `lctPathSummary_step_account`: one step of `lctPathSummary pathPayload s (vid u) (vid v)`
   preserves `TreeEditNamedSlots`, every tree edge's flow, original gradient, length, detector,
   and parent-child orientation, and the set of slots holding `some _`, and its returned
   `PathSummary` has exact gradient `∑_{e ∈ E0} gInt e * walkFlow (F.forestPath u v) e` and
   length `∑_{e ∈ E0} ℓInt e * |walkFlow (F.forestPath u v) e|`, bounded in absolute value by
   `s.n * B`.
2. `evalCycle_route_algebra`: summing those path summaries over `paths` and the signed gradients
   and lengths of off-tree records over `edges` (with `(edges.map Prod.fst).Nodup`) yields exact
   integer numerators `inner` and `norm` for `model.extG.inner model.extg Δ` and
   `model.extG.lnorm model.extℓ Δ`, with `0 ≤ norm` when edge lengths are nonnegative.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut LinkCut.PathTree LinkCut.PathProg Chain

/-- Gradient coordinate of `pathPayload.listSummary ps` is the sum of edge gradients in `ps`. -/
private theorem listSummary_gradient (ps : List (ℕ × Option PathEdgeValue)) :
    (pathPayload.listSummary ps).gradient =
      (ps.map fun p => match p.2 with | none => (0 : ℤ) | some v => v.gradient).sum := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨id, v⟩
    rw [LctPayload.listSummary_cons, List.map_cons, List.sum_cons]
    cases v with
    | none =>
      change (PathSummary.empty.combine (pathPayload.listSummary rest)).gradient = 0 + _
      rw [PathSummary.empty_combine, zero_add]
      exact ih
    | some val =>
      change val.gradient + (pathPayload.listSummary rest).gradient = val.gradient + _
      rw [ih]

/-- Length coordinate of `pathPayload.listSummary ps` is the sum of edge lengths in `ps`. -/
private theorem listSummary_length (ps : List (ℕ × Option PathEdgeValue)) :
    (pathPayload.listSummary ps).length =
      (ps.map fun p => match p.2 with | none => (0 : ℤ) | some v => v.length).sum := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨id, v⟩
    rw [LctPayload.listSummary_cons, List.map_cons, List.sum_cons]
    cases v with
    | none =>
      change (PathSummary.empty.combine (pathPayload.listSummary rest)).length = 0 + _
      rw [PathSummary.empty_combine, zero_add]
      exact ih
    | some val =>
      change val.length + (pathPayload.listSummary rest).length = val.length + _
      rw [ih]

/-- Cast a list sum of integers to reals. -/
private theorem int_list_sum_cast {α : Type*} (l : List α) (f : α → ℤ) :
    ((l.map f).sum : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A simple path in a graph whose edges have endpoints `< n` uses at most `n` edges. -/
theorem card_walkEdges_isPath_le {F : MGraph} {n u v : ℕ} {P : List (ℕ × Bool)}
    (hV : ∀ e ∈ F.E, F.tail e < n ∧ F.head e < n)
    (hu : u < n) (hp : F.IsPath u v P) :
    (walkEdges P).card ≤ n := by
  have hsub : ∀ {a b : ℕ} {w : List (ℕ × Bool)}, F.IsWalk a b w → a < n →
      ∀ z ∈ F.walkVertices a w, z < n := by
    intro a b w hw ha
    induction hw with
    | nil _ =>
      intro z hz; simp [MGraph.walkVertices] at hz; omega
    | @cons a' b' x rest hxe hsrc hrest ih =>
      intro z hz
      simp only [MGraph.walkVertices, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ha
      · have hdst : F.dst x < n := by
          unfold MGraph.dst; split_ifs
          · exact (hV x.1 hxe).2
          · exact (hV x.1 hxe).1
        exact ih hdst z hz
  have hnodup := hp.2
  have hsubset : (F.walkVertices u P).toFinset ⊆ Finset.range n := by
    intro z hz
    rw [List.mem_toFinset] at hz
    exact Finset.mem_range.mpr (hsub hp.1 hu z hz)
  have hlenV : (F.walkVertices u P).length ≤ n := by
    have h1 := List.toFinset_card_of_nodup hnodup
    have h2 := Finset.card_le_card hsubset
    simp only [Finset.card_range] at h2
    omega
  have hlenP : P.length < (F.walkVertices u P).length := by
    simp [MGraph.walkVertices]
  have hcard : (walkEdges P).card ≤ P.length := by
    unfold walkEdges
    exact (List.toFinset_card_le _).trans (by simp)
  omega

/-- Helper: sum over a nodup list equals sum over a Finset via an injective `slot` map when
entries outside `slot '' S` vanish. -/
private theorem list_sum_eq_finset_sum_bij {β : Type*} [AddCommMonoid β]
    (ps : List (ℕ × Option PathEdgeValue)) (S : Finset ℕ) (slot : ℕ → ℕ)
    (f : ℕ × Option PathEdgeValue → β) (g : ℕ → β)
    (hnd : (ps.map Prod.fst).Nodup)
    (hinj : ∀ e₁ ∈ S, ∀ e₂ ∈ S, slot e₁ = slot e₂ → e₁ = e₂)
    (hmem : ∀ e ∈ S, ∃ v, (slot e, v) ∈ ps ∧ f (slot e, v) = g e)
    (hzero : ∀ p ∈ ps, (∀ e ∈ S, p.1 ≠ slot e) → f p = 0) :
    (ps.map f).sum = ∑ e ∈ S, g e := by
  have hps_nd : ps.Nodup := List.Nodup.of_map Prod.fst hnd
  rw [← List.sum_toFinset _ hps_nd]
  classical
  have hfilt : ∑ p ∈ ps.toFinset, f p = ∑ p ∈ ps.toFinset.filter (fun p => ∃ e ∈ S, p.1 = slot e), f p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    simp only [Finset.mem_filter, not_and, not_exists] at hnot
    exact hzero p (List.mem_toFinset.mp hp) (fun e he => (hnot hp) e he)
  rw [hfilt]
  symm
  have huniq : ∀ {x v₁ v₂}, (x, v₁) ∈ ps → (x, v₂) ∈ ps → v₁ = v₂ := by
    intro x v₁ v₂ h1 h2
    obtain ⟨i₁, hi₁, hq₁⟩ := List.mem_iff_getElem.mp h1
    obtain ⟨i₂, hi₂, hq₂⟩ := List.mem_iff_getElem.mp h2
    have hidx : i₁ = i₂ := by
      have hm1 : (ps.map Prod.fst)[i₁]'(by simpa using hi₁) = x := by simp [hq₁]
      have hm2 : (ps.map Prod.fst)[i₂]'(by simpa using hi₂) = x := by simp [hq₂]
      exact (List.Nodup.getElem_inj hnd).mp (hm1.trans hm2.symm)
    subst hidx
    exact (Prod.mk.inj (hq₁.symm.trans hq₂)).2
  refine Finset.sum_bij (fun e he => (slot e, (hmem e he).choose)) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨(hmem e he).choose_spec.1, e, he, rfl⟩
  · intro e₁ h1 e₂ h2 heq
    exact hinj e₁ h1 e₂ h2 (congrArg Prod.fst heq)
  · intro p hp
    simp only [Finset.mem_filter, List.mem_toFinset] at hp
    obtain ⟨hp_mem, e, he, hp1⟩ := hp
    refine ⟨e, he, ?_⟩
    rcases p with ⟨x, v⟩
    dsimp only at hp1
    subst hp1
    congr 1
    exact huniq (hmem e he).choose_spec.1 hp_mem
  · intro e he
    exact (hmem e he).choose_spec.2.symm

/-- Core step accounting for `lctPathSummary`, abstracted over the intermediate `PathTreeState`s
so the kernel never unfolds `lctRerootCost`/`lctExposeCost`/`lctPathSummaryCost`. -/
private theorem lctPathSummary_step_account_core
    {s st1 s' : PathTreeState}
    {trees trees1 treesS trees' : List AuxTree} {Ls : AuxTree}
    {free : List ℕ} {depth depth1 depthS depth' : ℕ → ℕ}
    {F : MGraph} {E0 : Finset ℕ} {slot name : ℕ → ℕ} {u v : ℕ}
    {gInt ℓInt : ℕ → ℤ} {B : ℤ} {sum : PathSummary}
    (hi : LctInvWith pathPayload s trees free depth)
    (hn : TreeEditNamedSlots s trees F slot name)
    (hF : F.IsForest) (hE0sub : E0 ⊆ F.E)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e)
    (hu : u < s.n) (hv : v < s.n) (hconn : F.Connected u v)
    (hsubEq : subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid u) =
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid v))
    (hB : 0 ≤ B)
    (hsn' : s'.n = s.n)
    (hE' : ValsOnEdges s')
    (hvals : ∀ e ∈ E0, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      val.originalGradient = gInt e ∧ val.length = ℓInt e ∧
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧
      (val.forward = true →
        inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
        inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
      (val.forward = false →
        inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
        inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e)))
    (hhasVal : ∀ e ∈ E0, ∃ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees)
    (hnoVal : ∀ e ∈ F.E, e ∉ E0 → ∀ val : PathEdgeValue,
      (slot e, some val) ∉ forestPairs pathPayload s.splay trees)
    (hi1 : LctInvWith pathPayload st1 trees1 free depth1)
    (hact1 : (trees1.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList))
    (hpar1_u : inducedSubPar pathPayload st1.splay trees1 (vid u) = 0)
    (hconn1 : ∀ x ∈ trees.flatMap AuxTree.toList, ∀ y ∈ trees.flatMap AuxTree.toList,
      subRoot (inducedSubPar pathPayload st1.splay trees1) (trees1.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar pathPayload st1.splay trees1) (trees1.flatMap AuxTree.toList).length y ↔
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length y)
    (hpre_some1 : ∀ sl val, (sl, some val) ∈ forestPairs pathPayload st1.splay trees1 →
      ∃ val0, (sl, some val0) ∈ forestPairs pathPayload s.splay trees)
    (hor1 : ∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val1 : PathEdgeValue,
        (slot e, some val1) ∈ forestPairs pathPayload st1.splay trees1 ∧
        val1.originalFlow = val.originalFlow ∧
        val1.originalGradient = val.originalGradient ∧
        val1.length = val.length ∧
        val1.detector = val.detector ∧
        (val1.forward = true →
          inducedSubPar pathPayload st1.splay trees1 (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload st1.splay trees1 (slot e) = vid (F.tail e)) ∧
        (val1.forward = false →
          inducedSubPar pathPayload st1.splay trees1 (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload st1.splay trees1 (slot e) = vid (F.head e)))
    (hns' : TreeEditNamedSlots s' trees' F slot name)
    (hpar_eq : ∀ x, inducedSubPar pathPayload s'.splay trees' x = inducedSubPar pathPayload st1.splay trees1 x)
    (hfp_eq : (forestPairs pathPayload s'.splay trees').Perm (forestPairs pathPayload st1.splay trees1))
    (htS : AuxTree.node (vid v) Ls AuxTree.leaf ∈ treesS)
    (hiS : LctInvWith pathPayload s' treesS free depthS)
    (hactS : (treesS.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList))
    (hparS_u : inducedSubPar pathPayload s'.splay treesS (vid u) = 0)
    (hsumList : sum = pathPayload.listSummary (SplayState.evalPairs pathPayload s'.splay (AuxTree.node (vid v) Ls AuxTree.leaf) false pathPayload.idTag))
    (hfpS : (forestPairs pathPayload s'.splay treesS).Perm
      (SplayState.evalPairs pathPayload s'.splay (AuxTree.node (vid v) Ls AuxTree.leaf) false pathPayload.idTag ++
       forestPairs pathPayload s'.splay (treesS.erase (AuxTree.node (vid v) Ls AuxTree.leaf))))
    (hreachS : ∀ z, z ∈ (AuxTree.node (vid v) Ls AuxTree.leaf).toList ↔
      reaches (inducedSubPar pathPayload s'.splay treesS) (treesS.flatMap AuxTree.toList).length z (vid v) = true)
    (hoffS : ∀ p ∈ forestPairs pathPayload s'.splay (treesS.erase (AuxTree.node (vid v) Ls AuxTree.leaf)),
      p.1 ∉ (AuxTree.node (vid v) Ls AuxTree.leaf).toList)
    (honS : ∀ p ∈ SplayState.evalPairs pathPayload s'.splay (AuxTree.node (vid v) Ls AuxTree.leaf) false pathPayload.idTag,
      p.1 ∈ (AuxTree.node (vid v) Ls AuxTree.leaf).toList)
    (hi' : LctInvWith pathPayload s' trees' free depth') :
    TreeEditNamedSlots s' trees' F slot name ∧
    (∀ sl val, (sl, some val) ∈ forestPairs pathPayload s'.splay trees' →
      ∃ val0, (sl, some val0) ∈ forestPairs pathPayload s.splay trees) ∧
    (∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ forestPairs pathPayload s'.splay trees' ∧
        val'.originalFlow = val.originalFlow ∧
        val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧
        val'.detector = val.detector ∧
        (val'.forward = true →
          inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.head e))) ∧
    (sum.gradient : ℝ) = ∑ e ∈ E0, (gInt e : ℝ) * walkFlow (F.forestPath u v) e ∧
    (sum.length : ℝ) = ∑ e ∈ E0, (ℓInt e : ℝ) * |walkFlow (F.forestPath u v) e| ∧
    |sum.gradient| ≤ (s.n : ℤ) * B ∧ |sum.length| ≤ (s.n : ℤ) * B := by
  let t_exp := AuxTree.node (vid v) Ls AuxTree.leaf
  let onPath := SplayState.evalPairs pathPayload s'.splay t_exp false pathPayload.idTag
  let offPath := forestPairs pathPayload s'.splay (treesS.erase t_exp)
  have hpre_some' : ∀ sl val, (sl, some val) ∈ forestPairs pathPayload s'.splay trees' →
      ∃ val0, (sl, some val0) ∈ forestPairs pathPayload s.splay trees :=
    fun sl val hp => hpre_some1 sl val (hfp_eq.mem_iff.mp hp)
  have hpar_fun : inducedSubPar pathPayload s'.splay trees' =
      inducedSubPar pathPayload st1.splay trees1 := funext hpar_eq
  have hor' : ∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ forestPairs pathPayload s'.splay trees' ∧
        val'.originalFlow = val.originalFlow ∧ val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧ val'.detector = val.detector ∧
        (val'.forward = true →
          inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.head e)) := by
    intro e he val hp hor
    obtain ⟨val1, hp1, hfl1, hgr1, hlen1, hdet1, hft1, hff1⟩ := hor1 e he val hp hor
    exact ⟨val1, hfp_eq.symm.mem_iff.mp hp1, hfl1, hgr1, hlen1, hdet1,
      fun hf => by rw [hpar_fun]; exact hft1 hf,
      fun hf => by rw [hpar_fun]; exact hff1 hf⟩
  have hVE' : PairsVE s'.n (forestPairs pathPayload s'.splay treesS) := pairsVE_of_vals hE' treesS
  obtain ⟨hactS', hparS'⟩ := treeEdit_witness_agreement hiS hi'
  have hfpS' := treeEdit_account_witness_agreement hiS hi'
  have hnsS : TreeEditNamedSlots s' treesS F slot name := by
    refine ⟨fun e he => ?_, fun k hk hks => hns'.inverse k (hactS'.mem_iff.mp hk) hks, fun e he => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hns'.forward e he
      exact ⟨hactS'.mem_iff.mpr h1, h2, h3⟩
    · have := hns'.endpoints e he; dsimp only at this ⊢; rw [hparS']; exact this
  have hv1 : vid v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (hi.verticesActive v hv)
  have hreachS_uv : reaches (inducedSubPar pathPayload s'.splay treesS)
      (treesS.flatMap AuxTree.toList).length (vid u) (vid v) = true := by
    have h1 := (hconn1 (vid u) (hi.verticesActive u hu) (vid v) (hi.verticesActive v hv)).mpr hsubEq
    have hsu : subRoot (inducedSubPar pathPayload st1.splay trees1)
        (trees1.flatMap AuxTree.toList).length (vid u) = vid u :=
      subRoot_eq_self_of_zero hi1 (hact1.symm.mem_iff.mp (hi.verticesActive u hu)) hpar1_u
    rw [hsu] at h1
    have hr1 := (subRoot_eq_iff_reaches_zero hi1 hv1 hpar1_u).mp h1.symm
    have hparS_eq : inducedSubPar pathPayload s'.splay treesS =
        inducedSubPar pathPayload st1.splay trees1 := by
      funext z; rw [hparS', hpar_fun]
    rw [hparS_eq, (hactS.trans hact1.symm).length_eq]
    exact hr1
  obtain ⟨hwalk_iff, hwalk_dir⟩ := parentWalk_forestPath hiS hnsS hF
    (hsn'.symm ▸ hV) (hsn'.symm ▸ hu) (hsn'.symm ▸ hv) hparS_u hreachS_uv
  have hon_nd : (onPath.map Prod.fst).Nodup := by
    have hnd_all : ((forestPairs pathPayload s'.splay treesS).map Prod.fst).Nodup :=
      (forestPairs_fst_perm s'.splay treesS).nodup_iff.mpr hiS.activeNodup
    have hnd_app : ((onPath ++ offPath).map Prod.fst).Nodup :=
      (hfpS.map Prod.fst).nodup_iff.mp hnd_all
    rw [List.map_append] at hnd_app
    exact (List.nodup_append.mp hnd_app).1
  have hslot_inj : ∀ e₁ ∈ F.E, ∀ e₂ ∈ F.E, slot e₁ = slot e₂ → e₁ = e₂ := fun e₁ h1 e₂ h2 heq => by
    have n1 := (hn.forward e₁ h1).2.2
    have n2 := (hn.forward e₂ h2).2.2
    rw [heq] at n1; exact n1.symm.trans n2
  have hpath_is : F.IsPath u v (F.forestPath u v) := MGraph.isPath_forestPath hconn
  let W0 : Finset ℕ := walkEdges (F.forestPath u v) ∩ E0
  have hW0_subW : W0 ⊆ walkEdges (F.forestPath u v) := Finset.inter_subset_left
  have hW0_subE0 : W0 ⊆ E0 := Finset.inter_subset_right
  have hon_edge : ∀ e ∈ W0,
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ onPath ∧
        (val'.gradient : ℝ) = (gInt e : ℝ) * walkFlow (F.forestPath u v) e ∧
        (val'.length : ℝ) = (ℓInt e : ℝ) * |walkFlow (F.forestPath u v) e| ∧
        |val'.gradient| ≤ B ∧ |val'.length| ≤ B := by
    intro e heW0
    have heW : e ∈ walkEdges (F.forestPath u v) := hW0_subW heW0
    have heE0 : e ∈ E0 := hW0_subE0 heW0
    have heE : e ∈ F.E := hE0sub heE0
    obtain ⟨val, hp⟩ := hhasVal e heE0
    obtain ⟨hg, hl, hgb, hlb, hft, hff⟩ := hvals e heE0 val hp
    obtain ⟨val', hp', _, hgr', hlen', _, hft', hff'⟩ := hor' e heE val hp ⟨hft, hff⟩
    have hpS : (slot e, some val') ∈ forestPairs pathPayload s'.splay treesS :=
      hfpS'.symm.mem_iff.mp hp'
    have hmemExp : slot e ∈ t_exp.toList := (hreachS (slot e)).mpr ((hwalk_iff e heE).mpr heW)
    have hnotOff : (slot e, some val') ∉ offPath := fun h => hoffS _ h hmemExp
    have hon_mem : (slot e, some val') ∈ onPath :=
      (List.mem_append.mp (hfpS.mem_iff.mp hpS)).resolve_right hnotOff
    have hwf_val : walkFlow (F.forestPath u v) e = if val'.forward then 1 else -1 := by
      cases hvf : val'.forward with
      | true =>
        obtain ⟨h1, h2⟩ := hft' hvf
        rw [← hparS'] at h1 h2
        simpa using (hwalk_dir e heE heW).1 ⟨h1, h2⟩
      | false =>
        obtain ⟨h1, h2⟩ := hff' hvf
        rw [← hparS'] at h1 h2
        simpa using (hwalk_dir e heE heW).2 ⟨h1, h2⟩
    have hgrad_abs : |val'.gradient| ≤ B := by
      have h1 : |val'.originalGradient| = |val'.gradient| := by
        unfold PathEdgeValue.originalGradient; split_ifs <;> simp
      have h2 : |val.originalGradient| = |val.gradient| := by
        unfold PathEdgeValue.originalGradient; split_ifs <;> simp
      rw [← h1, hgr', h2]; exact hgb
    refine ⟨val', hon_mem, ?_, ?_, hgrad_abs, hlen' ▸ hlb⟩
    · rw [hwf_val]
      cases hvf : val'.forward with
      | true =>
        have : val'.gradient = gInt e := by
          have := hgr'.trans hg; unfold PathEdgeValue.originalGradient at this; simpa [hvf] using this
        simp [this]
      | false =>
        have : val'.gradient = -gInt e := by
          have := hgr'.trans hg; unfold PathEdgeValue.originalGradient at this; simp [hvf] at this; omega
        simp [this]
    · rw [hwf_val, hlen'.trans hl]
      cases val'.forward <;> simp
  have hon_zero : ∀ p ∈ onPath, (∀ e ∈ W0, p.1 ≠ slot e) → p.2 = none := by
    intro p hp hne
    have hpS : p ∈ forestPairs pathPayload s'.splay treesS :=
      hfpS.symm.mem_iff.mp (List.mem_append_left _ hp)
    have hp_act : p.1 ∈ treesS.flatMap AuxTree.toList :=
      List.mem_flatMap.mpr ⟨t_exp, htS, honS p hp⟩
    have hval := hiS.activeValid p.1 hp_act
    by_cases hvtx : isVertex s'.n p.1
    · exact hVE' p hpS hvtx
    · have hv1 : 1 ≤ p.1 := hval.1
      have hv2 : p.1 < 2 * s'.n := hval.2
      have hedge : isEdgeSlot s'.n p.1 := by
        unfold isVertex at hvtx; unfold isEdgeSlot; omega
      obtain ⟨heE, hslotE⟩ := hnsS.inverse p.1 hp_act hedge
      have hr : reaches (inducedSubPar pathPayload s'.splay treesS)
          (treesS.flatMap AuxTree.toList).length (slot (name p.1)) (vid v) = true := by
        rw [hslotE]; exact (hreachS p.1).mp (honS p hp)
      have heW : name p.1 ∈ walkEdges (F.forestPath u v) := (hwalk_iff _ heE).mp hr
      by_cases heE0 : name p.1 ∈ E0
      · exact absurd hslotE.symm (hne _ (Finset.mem_inter.mpr ⟨heW, heE0⟩))
      · cases hp2 : p.2 with
        | none => rfl
        | some val =>
          have hp' : (slot (name p.1), some val) ∈ forestPairs pathPayload s'.splay trees' := by
            rw [hslotE]; exact hfpS'.mem_iff.mp (hp2 ▸ hpS)
          obtain ⟨val0, hp0⟩ := hpre_some' _ val hp'
          exact absurd hp0 (hnoVal _ heE heE0 val0)
  have hgrad_real : ((pathPayload.listSummary onPath).gradient : ℝ) =
      ∑ e ∈ E0, (gInt e : ℝ) * walkFlow (F.forestPath u v) e := by
    rw [listSummary_gradient, int_list_sum_cast]
    have h1 := list_sum_eq_finset_sum_bij onPath W0 slot
      (fun p => ((match p.2 with | none => (0 : ℤ) | some v => v.gradient : ℤ) : ℝ))
      (fun e => (gInt e : ℝ) * walkFlow (F.forestPath u v) e)
      hon_nd (fun e₁ h1 e₂ h2 => hslot_inj e₁ (hE0sub (hW0_subE0 h1)) e₂ (hE0sub (hW0_subE0 h2)))
      (fun e he => by obtain ⟨val', hm, hgr, _⟩ := hon_edge e he; exact ⟨some val', hm, hgr⟩)
      (fun p hp hne => by rw [hon_zero p hp hne]; simp)
    rw [h1]
    apply Finset.sum_subset hW0_subE0
    intro e heE0 hnot
    have hnotW : e ∉ walkEdges (F.forestPath u v) := fun hw => hnot (Finset.mem_inter.mpr ⟨hw, heE0⟩)
    rw [walkFlow_eq_zero_of_not_mem hnotW, mul_zero]
  have hlen_real : ((pathPayload.listSummary onPath).length : ℝ) =
      ∑ e ∈ E0, (ℓInt e : ℝ) * |walkFlow (F.forestPath u v) e| := by
    rw [listSummary_length, int_list_sum_cast]
    have h1 := list_sum_eq_finset_sum_bij onPath W0 slot
      (fun p => ((match p.2 with | none => (0 : ℤ) | some v => v.length : ℤ) : ℝ))
      (fun e => (ℓInt e : ℝ) * |walkFlow (F.forestPath u v) e|)
      hon_nd (fun e₁ h1 e₂ h2 => hslot_inj e₁ (hE0sub (hW0_subE0 h1)) e₂ (hE0sub (hW0_subE0 h2)))
      (fun e he => by obtain ⟨val', hm, _, hln, _⟩ := hon_edge e he; exact ⟨some val', hm, hln⟩)
      (fun p hp hne => by rw [hon_zero p hp hne]; simp)
    rw [h1]
    apply Finset.sum_subset hW0_subE0
    intro e heE0 hnot
    have hnotW : e ∉ walkEdges (F.forestPath u v) := fun hw => hnot (Finset.mem_inter.mpr ⟨hw, heE0⟩)
    rw [walkFlow_eq_zero_of_not_mem hnotW, abs_zero, mul_zero]
  have hcard : W0.card ≤ s.n :=
    (Finset.card_le_card hW0_subW).trans
      (card_walkEdges_isPath_le (fun e he => ⟨(hV e he).1, (hV e he).2.1⟩) hu hpath_is)
  have hgrad_bd : |(pathPayload.listSummary onPath).gradient| ≤ (s.n : ℤ) * B := by
    rw [listSummary_gradient]
    have h1 := list_sum_eq_finset_sum_bij onPath W0 slot
      (fun p => match p.2 with | none => (0 : ℤ) | some v => v.gradient)
      (fun e => if h : e ∈ W0 then (hon_edge e h).choose.gradient else 0)
      hon_nd (fun e₁ h1 e₂ h2 => hslot_inj e₁ (hE0sub (hW0_subE0 h1)) e₂ (hE0sub (hW0_subE0 h2)))
      (fun e he => ⟨some (hon_edge e he).choose, (hon_edge e he).choose_spec.1, by simp [he]⟩)
      (fun p hp hne => by rw [hon_zero p hp hne])
    rw [h1]
    calc |∑ e ∈ W0, if h : e ∈ W0 then (hon_edge e h).choose.gradient else 0|
      _ ≤ ∑ e ∈ W0, |if h : e ∈ W0 then (hon_edge e h).choose.gradient else 0| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ W0, B := Finset.sum_le_sum fun e he => by
            simp only [he, ↓reduceDIte]; exact (hon_edge e he).choose_spec.2.2.2.1
      _ = (W0.card : ℤ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.n : ℤ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  have hlen_bd : |(pathPayload.listSummary onPath).length| ≤ (s.n : ℤ) * B := by
    rw [listSummary_length]
    have h1 := list_sum_eq_finset_sum_bij onPath W0 slot
      (fun p => match p.2 with | none => (0 : ℤ) | some v => v.length)
      (fun e => if h : e ∈ W0 then (hon_edge e h).choose.length else 0)
      hon_nd (fun e₁ h1 e₂ h2 => hslot_inj e₁ (hE0sub (hW0_subE0 h1)) e₂ (hE0sub (hW0_subE0 h2)))
      (fun e he => ⟨some (hon_edge e he).choose, (hon_edge e he).choose_spec.1, by simp [he]⟩)
      (fun p hp hne => by rw [hon_zero p hp hne])
    rw [h1]
    calc |∑ e ∈ W0, if h : e ∈ W0 then (hon_edge e h).choose.length else 0|
      _ ≤ ∑ e ∈ W0, |if h : e ∈ W0 then (hon_edge e h).choose.length else 0| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ W0, B := Finset.sum_le_sum fun e he => by
            simp only [he, ↓reduceDIte]; exact (hon_edge e he).choose_spec.2.2.2.2
      _ = (W0.card : ℤ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.n : ℤ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  rw [hsumList]
  exact ⟨hns', hpre_some', hor', hgrad_real, hlen_real, hgrad_bd, hlen_bd⟩

private theorem lctPathSummary_fst_eq_cost (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).1 = (lctPathSummaryCost pathPayload s u v).1 := rfl

private theorem lctPathSummary_snd_eq_cost (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).2 = (lctPathSummaryCost pathPayload s u v).2.1 := rfl

private theorem lctPathSummaryCost_fst_eq_expose (s : PathTreeState) (u v : ℕ) :
    (lctPathSummaryCost pathPayload s u v).1 =
      (lctExposeCost pathPayload (lctRerootCost pathPayload s u).1 v).1 := rfl

private theorem lctPathSummary_n_eq (s : PathTreeState) (u v : ℕ) :
    (lctPathSummaryCost pathPayload s u v).1.n = s.n := rfl

/-- One step of `lctPathSummary pathPayload s (vid u) (vid v)` preserves `TreeEditNamedSlots`,
all tree edge accounts and orientations, and the set of slots holding `some _`, and computes
the exact signed gradient sum and unsigned length sum along `F.forestPath u v` (bounded by
`s.n * B`). -/
theorem lctPathSummary_step_account {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth depth' : ℕ → ℕ} {F : MGraph} {E0 : Finset ℕ} {slot name : ℕ → ℕ}
    {u v : ℕ} {gInt ℓInt : ℕ → ℤ} {B : ℤ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hE : ValsOnEdges s)
    (hn : TreeEditNamedSlots s trees F slot name)
    (hF : F.IsForest) (hE0sub : E0 ⊆ F.E)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e)
    (hu : u < s.n) (hv : v < s.n) (hconn : F.Connected u v)
    (hB : 0 ≤ B)
    (hvals : ∀ e ∈ E0, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      val.originalGradient = gInt e ∧ val.length = ℓInt e ∧
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧
      (val.forward = true →
        inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
        inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
      (val.forward = false →
        inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
        inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e)))
    (hhasVal : ∀ e ∈ E0, ∃ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees)
    (hnoVal : ∀ e ∈ F.E, e ∉ E0 → ∀ val : PathEdgeValue,
      (slot e, some val) ∉ forestPairs pathPayload s.splay trees)
    (hi' : LctInvWith pathPayload (lctPathSummary pathPayload s (vid u) (vid v)).1 trees' free depth') :
    let res := lctPathSummary pathPayload s (vid u) (vid v)
    let s' := res.1
    let sum := res.2
    TreeEditNamedSlots s' trees' F slot name ∧
    (∀ sl val, (sl, some val) ∈ forestPairs pathPayload s'.splay trees' →
      ∃ val0, (sl, some val0) ∈ forestPairs pathPayload s.splay trees) ∧
    (∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ forestPairs pathPayload s'.splay trees' ∧
        val'.originalFlow = val.originalFlow ∧
        val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧
        val'.detector = val.detector ∧
        (val'.forward = true →
          inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.head e))) ∧
    (sum.gradient : ℝ) = ∑ e ∈ E0, (gInt e : ℝ) * walkFlow (F.forestPath u v) e ∧
    (sum.length : ℝ) = ∑ e ∈ E0, (ℓInt e : ℝ) * |walkFlow (F.forestPath u v) e| ∧
    |sum.gradient| ≤ (s.n : ℤ) * B ∧ |sum.length| ≤ (s.n : ℤ) * B := by
  dsimp only
  rw [lctPathSummary_fst_eq_cost] at hi' ⊢
  rw [lctPathSummary_snd_eq_cost]
  have hrr : lctReroot pathPayload s (vid u) = (lctRerootCost pathPayload s (vid u)).1 := rfl
  have hex : lctExpose pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v) =
      (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v)).1 := rfl
  have huV : isVertex s.n (vid u) := by unfold isVertex vid; omega
  have hconnT : pathTreeConnected s (vid u) (vid v) :=
    treeEditNamedSlots_connected hi hn (fun e he => ⟨(hV e he).1, (hV e he).2.1⟩) hu hv hconn
  have hsubEq := (pathTreeConnected_iff_induced_roots hi hu hv).mp hconnT
  obtain ⟨tu, htu, huMem⟩ := List.mem_flatMap.mp (hi.verticesActive u hu)
  obtain ⟨tv, htv, hvMem⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
  obtain ⟨trees1, _, depth1, _, hi1, hact1, _, hpar1_u, _, _, _, _, hsplit1, hfp1, _, _, _, hconn1, _, _⟩ :=
    lctReroot_spec pathPayload_laws hi htu huMem huV
  obtain ⟨hns1, hor1⟩ := reroot_preserves_named_orient hi hn hV hu (hrr ▸ hi1)
  rw [hrr] at hns1 hor1
  have hpre_some1 : ∀ sl val, (sl, some val) ∈ forestPairs pathPayload (lctRerootCost pathPayload s (vid u)).1.splay trees1 →
      ∃ val0, (sl, some val0) ∈ forestPairs pathPayload s.splay trees := by
    intro sl val hp
    rcases List.mem_append.mp (hfp1.mem_iff.mp hp) with hm | hm
    · obtain ⟨⟨sl', opt⟩, hq, heq⟩ := List.mem_map.mp (List.mem_reverse.mp hm)
      cases opt with
      | none => simp [pathPayload] at heq
      | some v0 =>
        have hsl : sl' = sl := (Prod.mk.inj heq).1
        subst hsl
        exact ⟨v0, hsplit1.mem_iff.mp (List.mem_append_left _ hq)⟩
    · exact ⟨val, hsplit1.mem_iff.mp (List.mem_append_right _ hm)⟩
  have hv1 : vid v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (hi.verticesActive v hv)
  obtain ⟨tv1, htv1, hv1Mem⟩ := List.mem_flatMap.mp hv1
  obtain ⟨trees2, _, _, hi2, _, hpar2, hfp2, _, _, _, _, _, _, _, _⟩ :=
    lctExpose_spec pathPayload_laws hi1 htv1 hv1Mem
  have hfe := lctPathSummaryCost_fst_eq_expose s (vid u) (vid v)
  have hi2' : LctInvWith pathPayload (lctPathSummaryCost pathPayload s (vid u) (vid v)).1 trees2 free depth1 := by
    rw [hfe]; exact hi2
  obtain ⟨hact2', hpar2'⟩ := treeEdit_witness_agreement hi2' hi'
  have hfp2' := treeEdit_account_witness_agreement hi2' hi'
  have hns2 : TreeEditNamedSlots (lctPathSummaryCost pathPayload s (vid u) (vid v)).1 trees2 F slot name := by
    rw [hfe]
    have h := treeEditNamedSlots_expose_witness hns1 hi1 hv1 (hex ▸ hi2)
    rw [hex] at h; exact h
  have hns' : TreeEditNamedSlots (lctPathSummaryCost pathPayload s (vid u) (vid v)).1 trees' F slot name := by
    refine ⟨fun e he => ?_, fun k hk hks => hns2.inverse k (hact2'.symm.mem_iff.mp hk) hks, fun e he => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hns2.forward e he
      exact ⟨hact2'.mem_iff.mp h1, h2, h3⟩
    · have := hns2.endpoints e he; dsimp only at this ⊢; rw [← hpar2']; exact this
  have hE' : ValsOnEdges (lctPathSummaryCost pathPayload s (vid u) (vid v)).1 := by
    rw [hfe, ← hex]
    exact vals_expose (hrr ▸ hi1) (vals_reroot hi hE huV) hv1
  obtain ⟨_, treesS, Ls, depthS, htS, hiS, hactS, _, _, _, _, hparS_u, _, _,
      hsumList, _, hfpS, hreachS, hoffS, honS, _, _, _⟩ :=
    lctPathSummary_spec pathPayload_laws hi htu huMem huV htv hvMem hsubEq
  exact lctPathSummary_step_account_core hi hn hF hE0sub hV hu hv hconn hsubEq hB
    (lctPathSummary_n_eq s (vid u) (vid v)) hE'
    hvals hhasVal hnoVal hi1 hact1 hpar1_u hconn1 hpre_some1 hor1 hns'
    (fun x => (congrFun hpar2'.symm x).trans (by rw [hfe]; exact hpar2 x))
    (hfp2'.symm.trans (by rw [hfe]; exact hfp2))
    htS hiS hactS hparS_u hsumList hfpS hreachS hoffS honS hi'

/-- Summing a singleton-walk flow over a list with no opposite-orientation pairs: for any `e`,
every occurrence of `e` in `edges` has the same orientation, so `|∑ x ∈ edges, walkFlow [x] e|`
equals the number of occurrences of `e` in `edges`. -/
private theorem abs_edges_walkFlow_eq_sum {edges : List (ℕ × Bool)}
    (hno : NoOppositePairs edges) (e : ℕ) :
    |(edges.map fun x => walkFlow [x] e).sum| =
      (edges.map fun x => if x.1 = e then (1 : ℝ) else 0).sum := by
  have hnn : 0 ≤ (edges.map fun x => if x.1 = e then (1 : ℝ) else 0).sum :=
    List.sum_nonneg fun r hr => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      split_ifs <;> norm_num
  by_cases ht : (e, true) ∈ edges
  · have hf : (e, false) ∉ edges := hno (e, true) ht
    have heq : (edges.map fun x => walkFlow [x] e) =
        (edges.map fun x => if x.1 = e then (1 : ℝ) else 0) := by
      refine List.map_congr_left fun x hx => ?_
      rcases x with ⟨eid, dir⟩
      by_cases he : eid = e
      · subst he
        cases dir
        · exact absurd hx hf
        · simp [walkFlow]
      · simp [walkFlow, he]
    rw [heq, abs_of_nonneg hnn]
  · by_cases hf : (e, false) ∈ edges
    · have heq : (edges.map fun x => walkFlow [x] e) =
          (edges.map fun x => -(if x.1 = e then (1 : ℝ) else 0)) := by
        refine List.map_congr_left fun x hx => ?_
        rcases x with ⟨eid, dir⟩
        by_cases he : eid = e
        · subst he
          cases dir
          · simp [walkFlow]
          · exact absurd hx ht
        · simp [walkFlow, he]
      have hneg : ∀ l : List (ℕ × Bool),
          (l.map fun x => -(if x.1 = e then (1 : ℝ) else 0)).sum =
          -(l.map fun x => if x.1 = e then (1 : ℝ) else 0).sum := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ih => simp [ih]; ring
      rw [heq, hneg edges, abs_neg, abs_of_nonneg hnn]
    · have h0 : ∀ x ∈ edges, x.1 ≠ e := fun ⟨eid, dir⟩ hx he => by
        subst he; cases dir <;> [exact hf hx; exact ht hx]
      have hL : (edges.map fun x => walkFlow [x] e).sum = 0 :=
        List.sum_eq_zero fun r hr => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
          simp [walkFlow, h0 x hx]
      have hR : (edges.map fun x => if x.1 = e then (1 : ℝ) else 0).sum = 0 :=
        List.sum_eq_zero fun r hr => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
          simp [h0 x hx]
      rw [hL, hR, abs_zero]

/-- Exact algebraic identity connecting the accumulated integer gradient and length sums
(from `paths` summaries over `F.E ∩ (G 0).E` and `edges` off-tree records) to
`model.extG.inner model.extg Δ` and `model.extG.lnorm model.extℓ Δ`. -/
theorem evalCycle_route_algebra {cfg : Alg2Config} {P : ℕ} {model : Alg2State cfg}
    {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    {treeGrad treeLen edgeGrad edgeLen : ℤ}
    (hfresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hroute : CycleRouteAt model edges paths)
    (hno : NoOppositePairs edges)
    (hlenNN : ∀ e ∈ model.extG.E, 0 ≤ model.extℓ e)
    (htG : (treeGrad : ℝ) / (2 : ℝ) ^ P =
      (paths.map fun p => ∑ e ∈ model.chain.toTreeChain.chainTree.E ∩ (model.chain.G 0).E,
        model.extg (model.intToExt e) * walkFlow (model.chain.toTreeChain.chainTree.forestPath p.1 p.2) e).sum)
    (htL : (treeLen : ℝ) / (2 : ℝ) ^ P =
      (paths.map fun p => ∑ e ∈ model.chain.toTreeChain.chainTree.E ∩ (model.chain.G 0).E,
        model.extℓ (model.intToExt e) * |walkFlow (model.chain.toTreeChain.chainTree.forestPath p.1 p.2) e|).sum)
    (heG : (edgeGrad : ℝ) / (2 : ℝ) ^ P =
      (edges.map fun x => (if x.2 then (1 : ℝ) else -1) * model.extg (model.intToExt x.1)).sum)
    (heL : (edgeLen : ℝ) / (2 : ℝ) ^ P =
      (edges.map fun x => model.extℓ (model.intToExt x.1)).sum) :
    let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
    model.extG.inner model.extg Δ = ((treeGrad + edgeGrad : ℤ) : ℝ) / (2 : ℝ) ^ P ∧
    model.extG.lnorm model.extℓ Δ = ((treeLen + edgeLen : ℤ) : ℝ) / (2 : ℝ) ^ P ∧
    0 ≤ treeLen + edgeLen := by
  dsimp only
  let F := model.chain.toTreeChain.chainTree
  let E0 := F.E ∩ (model.chain.G 0).E
  let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
  have hswap : ∀ {α : Type} (l : List α) (S : Finset ℕ) (f : α → ℕ → ℝ),
      (l.map fun a => ∑ e ∈ S, f a e).sum = ∑ e ∈ S, (l.map fun a => f a e).sum := by
    intro α l S f
    induction l with
    | nil => simp
    | cons a rest ih => simp [ih, Finset.sum_add_distrib]
  have hmul_sum : ∀ {α : Type} (l : List α) (c : ℝ) (f : α → ℝ),
      c * (l.map f).sum = (l.map fun a => c * f a).sum := by
    intro α l c f
    induction l with
    | nil => simp
    | cons a rest ih => simp [mul_add, ih]
  have hfp_off : ∀ p ∈ paths, ∀ ei, ei ∉ F.E → walkFlow (F.forestPath p.1 p.2) ei = 0 := by
    intro p hp ei hnot
    apply walkFlow_eq_zero_of_not_mem
    intro hmem
    have hpath := MGraph.isPath_forestPath (hroute.2.1 p hp).2.2
    simp only [walkEdges, List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    have hwalk_mem : ∀ {a b : ℕ} {w : List (ℕ × Bool)}, F.IsWalk a b w → ∀ y ∈ w, y.1 ∈ F.E := by
      intro a b w hw
      induction hw with
      | nil _ => intro _ h; cases h
      | cons hxe _ _ ih =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxe
        · exact ih y hy
    exact hnot (hwalk_mem hpath.1 x hx)
  -- Express `edgeGrad` as sum over `(G 0).E`
  have hedge_g_sum :
      (edges.map fun x => (if x.2 then (1 : ℝ) else -1) * model.extg (model.intToExt x.1)).sum =
      ∑ ei ∈ (model.chain.G 0).E, model.extg (model.intToExt ei) * (edges.map fun x => walkFlow [x] ei).sum := by
    have h1 : ∑ ei ∈ (model.chain.G 0).E,
        model.extg (model.intToExt ei) * (edges.map fun x => walkFlow [x] ei).sum =
        ∑ ei ∈ (model.chain.G 0).E,
        (edges.map fun x => model.extg (model.intToExt ei) * walkFlow [x] ei).sum :=
      Finset.sum_congr rfl fun ei _ => hmul_sum edges _ _
    rw [h1, ← hswap]
    congr 1
    apply List.map_congr_left
    intro x hx
    have hxE : x.1 ∈ (model.chain.G 0).E := (Finset.mem_sdiff.mp (hroute.1 x hx)).1
    rw [Finset.sum_eq_single x.1]
    · simp [walkFlow]
    · intro ei _ hne; simp [walkFlow, Ne.symm hne]
    · intro hnot; exact absurd hxE hnot
  -- Express `edgeLen` as sum over `(G 0).E`
  have hedge_l_sum :
      (edges.map fun x => model.extℓ (model.intToExt x.1)).sum =
      ∑ ei ∈ (model.chain.G 0).E, model.extℓ (model.intToExt ei) * |(edges.map fun x => walkFlow [x] ei).sum| := by
    have h1 : ∀ ei ∈ (model.chain.G 0).E,
        model.extℓ (model.intToExt ei) * |(edges.map fun x => walkFlow [x] ei).sum| =
        (edges.map fun x => model.extℓ (model.intToExt ei) * (if x.1 = ei then (1 : ℝ) else 0)).sum := by
      intro ei _
      rw [abs_edges_walkFlow_eq_sum hno ei, hmul_sum]
    rw [Finset.sum_congr rfl h1, ← hswap]
    congr 1
    apply List.map_congr_left
    intro x hx
    have hxE : x.1 ∈ (model.chain.G 0).E := (Finset.mem_sdiff.mp (hroute.1 x hx)).1
    rw [Finset.sum_eq_single x.1]
    · simp
    · intro ei _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd hxE hnot
  -- Extend `treeGrad` and `treeLen` sums from `E0` to `(G 0).E`
  have htree_g_sum :
      (paths.map fun p => ∑ ei ∈ E0, model.extg (model.intToExt ei) * walkFlow (F.forestPath p.1 p.2) ei).sum =
      ∑ ei ∈ (model.chain.G 0).E, model.extg (model.intToExt ei) *
        (paths.map fun p => walkFlow (F.forestPath p.1 p.2) ei).sum := by
    have h1 : (paths.map fun p => ∑ ei ∈ E0, model.extg (model.intToExt ei) * walkFlow (F.forestPath p.1 p.2) ei) =
        (paths.map fun p => ∑ ei ∈ (model.chain.G 0).E,
          model.extg (model.intToExt ei) * walkFlow (F.forestPath p.1 p.2) ei) := by
      apply List.map_congr_left
      intro p hp
      apply Finset.sum_subset Finset.inter_subset_right
      intro ei hei hnot
      have hnotF : ei ∉ F.E := fun hf => hnot (Finset.mem_inter.mpr ⟨hf, hei⟩)
      rw [hfp_off p hp ei hnotF, mul_zero]
    rw [h1, hswap]
    exact Finset.sum_congr rfl fun ei _ => (hmul_sum paths _ _).symm
  have htree_l_sum :
      (paths.map fun p => ∑ ei ∈ E0, model.extℓ (model.intToExt ei) * |walkFlow (F.forestPath p.1 p.2) ei|).sum =
      ∑ ei ∈ (model.chain.G 0).E, model.extℓ (model.intToExt ei) *
        (paths.map fun p => |walkFlow (F.forestPath p.1 p.2) ei|).sum := by
    have h1 : (paths.map fun p => ∑ ei ∈ E0, model.extℓ (model.intToExt ei) * |walkFlow (F.forestPath p.1 p.2) ei|) =
        (paths.map fun p => ∑ ei ∈ (model.chain.G 0).E,
          model.extℓ (model.intToExt ei) * |walkFlow (F.forestPath p.1 p.2) ei|) := by
      apply List.map_congr_left
      intro p hp
      apply Finset.sum_subset Finset.inter_subset_right
      intro ei hei hnot
      have hnotF : ei ∉ F.E := fun hf => hnot (Finset.mem_inter.mpr ⟨hf, hei⟩)
      rw [hfp_off p hp ei hnotF, abs_zero, mul_zero]
    rw [h1, hswap]
    exact Finset.sum_congr rfl fun ei _ => (hmul_sum paths _ _).symm
  have hinner : model.extG.inner model.extg Δ = ((treeGrad + edgeGrad : ℤ) : ℝ) / (2 : ℝ) ^ P := by
    rw [Int.cast_add, add_div, htG, heG, htree_g_sum, hedge_g_sum, ← Finset.sum_add_distrib]
    rw [hfresh.inner_lift model.extg (algorithm1_findCycle model.chain).1]
    unfold MGraph.inner
    refine Finset.sum_congr rfl fun ei hei => ?_
    obtain ⟨heq, he⟩ := hfresh.hRight ei hei
    have hr := (hroute.2.2 (model.intToExt ei) he).1
    rw [heq] at hr
    rw [hr]; ring
  have hlnorm : model.extG.lnorm model.extℓ Δ = ((treeLen + edgeLen : ℤ) : ℝ) / (2 : ℝ) ^ P := by
    rw [Int.cast_add, add_div, htL, heL, htree_l_sum, hedge_l_sum, ← Finset.sum_add_distrib]
    rw [hfresh.lnorm_lift model.extℓ (algorithm1_findCycle model.chain).1]
    unfold MGraph.lnorm
    refine Finset.sum_congr rfl fun ei hei => ?_
    obtain ⟨heq, he⟩ := hfresh.hRight ei hei
    have hr := (hroute.2.2 (model.intToExt ei) he).2 1
    simp only [one_mul, heq] at hr
    rw [hr]; ring
  have hnn : 0 ≤ treeLen + edgeLen := by
    have hnnR : (0 : ℝ) ≤ ((treeLen + edgeLen : ℤ) : ℝ) / (2 : ℝ) ^ P := by
      rw [← hlnorm]
      unfold MGraph.lnorm
      exact Finset.sum_nonneg fun e he => mul_nonneg (hlenNN e he) (abs_nonneg _)
    have hPpos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
    have hmul : (0 : ℝ) ≤ ((treeLen + edgeLen : ℤ) : ℝ) := by
      rwa [le_div_iff₀ hPpos, zero_mul] at hnnR
    exact_mod_cast hmul
  exact ⟨hinner, hlnorm, hnn⟩

end MinCostFlow.MinRatio
