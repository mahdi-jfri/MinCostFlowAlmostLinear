module

public import MinCostFlow.MinRatio.PathTreeNumericBounds
public import MinCostFlow.MinRatio.PathSplayNumericBounds
import MinCostFlow.MinRatio.PathTreeExpose
import MinCostFlow.LinkCut.ForestExposeOps
import MinCostFlow.LinkCut.ForestExposeSpec
import MinCostFlow.LinkCut.ForestReversals

/-!
# Numeric bounds on stored path accounts

Section 6 (pages 29–30) evaluates flow and detector accounts through the
lazy path tree. The stored value differs from the evaluated one by the
tags on its auxiliary route, with reversal preserving magnitudes.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut

/-- The raw edge value differs from the evaluated account by at most
the magnitude of the accumulated tag, after orienting the edge. -/
theorem pathEdgeValue_abs_le_shifted (v : PathEdgeValue) (a : PathTag) (flip : Bool) :
    let value := (if flip then v.reverse else v).shift a
    |v.gradient| = |value.gradient| ∧ v.length = value.length ∧
      |v.flow| ≤ |value.flow| + pathTagMagnitude a ∧
      |v.detector| ≤ |value.detector| + pathTagMagnitude a := by
  dsimp only
  have scalar (x y : ℤ) : |x| ≤ |x + y| + |y| := by
    have h := abs_add_le (x + y) (-y)
    rw [show x + y + -y = x by omega, abs_neg] at h
    exact h
  have hd := scalar v.detector a.detector
  have hf := scalar v.flow a.flow
  have hf' := scalar (-v.flow) a.flow
  rw [abs_neg] at hf'
  have haf := abs_nonneg a.flow
  have had := abs_nonneg a.detector
  cases flip
  · simp only [Bool.false_eq_true, ite_false, PathEdgeValue.shift, true_and]
    unfold pathTagMagnitude
    constructor <;> omega
  · simp only [ite_true, PathEdgeValue.reverse, PathEdgeValue.shift, abs_neg, true_and]
    unfold pathTagMagnitude
    constructor <;> omega

private theorem evalPairs_account_with_charge
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {t : AuxTree} {x : ℕ}
    (hn : t.toList.Nodup) (hx : x ∈ t.toList) {raw : PathEdgeValue}
    (hraw : (s.nodes x).val = some raw) (flip : Bool) (acc : PathTag) :
    ∃ value, (x, some value) ∈ SplayState.evalPairs pathPayload s t flip acc ∧
      |raw.gradient| = |value.gradient| ∧ raw.length = value.length ∧
      |raw.flow| ≤ |value.flow| + (pathTagMagnitude acc + pathTagRouteMagnitude s (t.pathTo x)) ∧
      |raw.detector| ≤ |value.detector| + (pathTagMagnitude acc + pathTagRouteMagnitude s (t.pathTo x)) := by
  induction t generalizing flip acc with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
    let nd := s.nodes id
    let nextFlip := flip ^^ nd.rev
    let tag := if flip then nd.tag.reverse else nd.tag
    let nextTag := acc.compose tag
    have htag : pathTagMagnitude nextTag ≤ pathTagMagnitude acc + pathTagMagnitude nd.tag := by
      have he : pathTagMagnitude tag = pathTagMagnitude nd.tag := by
        cases flip <;> simp [tag, pathTagMagnitude_reverse]
      exact (pathTagMagnitude_compose acc tag).trans (by rw [he])
    have step {c : AuxTree} (he : (AuxTree.node id l r).pathTo x = id :: c.pathTo x) :
        pathTagMagnitude nextTag + pathTagRouteMagnitude s (c.pathTo x) ≤
          pathTagMagnitude acc + pathTagRouteMagnitude s ((AuxTree.node id l r).pathTo x) := by
      rw [he]
      change _ ≤ _ + (pathTagMagnitude nd.tag + pathTagRouteMagnitude s (c.pathTo x))
      omega
    have liftMem {value : PathEdgeValue}
        (hm : (x, some value) ∈ SplayState.evalPairs pathPayload s l nextFlip nextTag ∨
          (x, some value) ∈ SplayState.evalPairs pathPayload s r nextFlip nextTag) :
        (x, some value) ∈ SplayState.evalPairs pathPayload s (.node id l r) flip acc := by
      cases flip <;>
        simp only [SplayState.evalPairs, Bool.false_eq_true, ite_false, ite_true, List.mem_append] <;>
        rcases hm with hm | hm <;> first | exact Or.inl (Or.inl hm) | exact Or.inr hm
    by_cases he : x = id
    · subst x
      let value := (if flip then raw.reverse else raw).shift acc
      have hm : (id, some value) ∈ SplayState.evalPairs pathPayload s (.node id l r) flip acc := by
        cases flip <;> simp [SplayState.evalPairs, pathPayload, hraw, value]
      obtain ⟨hg, hl, hf, hd⟩ := pathEdgeValue_abs_le_shifted raw acc flip
      have hpos : 0 ≤ pathTagRouteMagnitude s ((AuxTree.node id l r).pathTo id) := by
        simp only [AuxTree.pathTo, ite_true, pathTagRouteMagnitude, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero, pathTagMagnitude]
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      change |raw.flow| ≤ |value.flow| + pathTagMagnitude acc at hf
      change |raw.detector| ≤ |value.detector| + pathTagMagnitude acc at hd
      exact ⟨value, hm, hg, hl, by omega, by omega⟩
    obtain ⟨hl, _, hr, _, _⟩ := AuxTree.nodup_node_unfold hn
    by_cases hxl : x ∈ l.toList
    · obtain ⟨value, hm, hg, hv, hf, hd⟩ := ihl hl hxl nextFlip nextTag
      have hstep := step (c := l) (by simp [AuxTree.pathTo, he, hxl])
      exact ⟨value, liftMem (Or.inl hm), hg, hv, by omega, by omega⟩
    · have hxr : x ∈ r.toList := by simpa [AuxTree.toList, he, hxl] using hx
      obtain ⟨value, hm, hg, hv, hf, hd⟩ := ihr hr hxr nextFlip nextTag
      have hstep := step (c := r) (by simp [AuxTree.pathTo, he, hxl, hxr])
      exact ⟨value, liftMem (Or.inr hm), hg, hv, by omega, by omega⟩

/-- A raw value is bounded by its evaluated account plus its route tag budget. -/
theorem pathRawAccount_abs_le
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {t : AuxTree} {x : ℕ}
    (hn : t.toList.Nodup) (hx : x ∈ t.toList) {raw : PathEdgeValue}
    (hraw : (s.nodes x).val = some raw) :
    ∃ value, (x, some value) ∈ SplayState.evalPairs pathPayload s t false pathPayload.idTag ∧
      |raw.gradient| = |value.gradient| ∧ raw.length = value.length ∧
      |raw.flow| ≤ |value.flow| + pathTagRouteMagnitude s (t.pathTo x) ∧
      |raw.detector| ≤ |value.detector| + pathTagRouteMagnitude s (t.pathTo x) := by
  simpa only [show pathTagMagnitude pathPayload.idTag = 0 by
    simp [pathTagMagnitude, pathPayload, PathTag.zero], zero_add] using
      evalPairs_account_with_charge s hn hx hraw false pathPayload.idTag

/-- A segment of bounded evaluated accounts has sum bounds proportional to its
length, and a maximum detector bound independent of its length. -/
theorem pathListSummary_abs_le
    {pairs : List (ℕ × Option PathEdgeValue)} {B : ℤ} (hB : 0 ≤ B)
    (hb : ∀ id v, (id, some v) ∈ pairs →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.detector| ≤ B) :
    let sum := pathPayload.listSummary pairs
    |sum.gradient| ≤ (pairs.length : ℤ) * B ∧
    |sum.length| ≤ (pairs.length : ℤ) * B ∧
    (∀ d, sum.detector = some d → |d| ≤ B) := by
  induction pairs with
  | nil =>
    simp [LctPayload.listSummary_nil, pathPayload, PathSummary.empty]
  | cons pair rest ih =>
    obtain ⟨id, value⟩ := pair
    obtain ⟨hg, hl, hd⟩ := ih (fun i v h => hb i v (List.mem_cons_of_mem _ h))
    simp only [LctPayload.listSummary_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    let sum := pathPayload.listSummary rest
    change |sum.gradient| ≤ (rest.length : ℤ) * B at hg
    change |sum.length| ≤ (rest.length : ℤ) * B at hl
    cases value with
    | none =>
      change |0 + sum.gradient| ≤ _ ∧ |0 + sum.length| ≤ _ ∧
        (∀ d, sum.detector = some d → |d| ≤ B)
      rw [zero_add, zero_add]
      exact ⟨hg.trans (le_add_of_nonneg_right hB), hl.trans (le_add_of_nonneg_right hB), hd⟩
    | some v =>
      obtain ⟨hvg, hvl, hvd⟩ := hb id v List.mem_cons_self
      change |v.gradient + sum.gradient| ≤ _ ∧ |v.length + sum.length| ≤ _ ∧
        (∀ d, detectorMax (some v.detector) sum.detector = some d → |d| ≤ B)
      refine ⟨(abs_add_le _ _).trans (by omega), (abs_add_le _ _).trans (by omega), ?_⟩
      intro d h
      cases hs : sum.detector with
      | none =>
        simp [detectorMax, hs] at h
        rwa [← h]
      | some ds =>
        simp [detectorMax, hs] at h
        rw [← h]
        by_cases hle : v.detector ≤ ds
        · rw [max_eq_right hle]
          exact hd ds hs
        · rw [max_eq_left (le_of_not_ge hle)]
          exact hvd

/-- The stored summary satisfies the segment bounds for the node's own subtree. -/
theorem pathSubtreeSummary_abs_le
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {root parent : ℕ} {l r : AuxTree} {B : ℤ}
    (ht : SplayState.SubtreeInv pathPayload s parent (.node root l r)) (hB : 0 ≤ B)
    (hb : ∀ id v,
      (id, some v) ∈ SplayState.evalPairs pathPayload s (.node root l r) false pathPayload.idTag →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.detector| ≤ B) :
    let sum := (s.nodes root).sum
    let size := (AuxTree.node root l r).countNodes
    |sum.gradient| ≤ (size : ℤ) * B ∧ |sum.length| ≤ (size : ℤ) * B ∧
      (∀ d, sum.detector = some d → |d| ≤ B) := by
  dsimp only
  rw [SplayState.SubtreeInv.eq_2] at ht
  rw [ht.2.2.2.2.2.2.1]
  simpa only [SplayState.evalPairs_length] using pathListSummary_abs_le hB hb

private theorem evalPairs_findSubtree_with_charge
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {t : AuxTree} {x : ℕ}
    (hx : x ∈ t.toList) (flip : Bool) (acc : PathTag) :
    ∃ subFlip subTag, pathTagMagnitude subTag ≤
        pathTagMagnitude acc + pathTagRouteMagnitude s (t.pathTo x) ∧
      ∀ p ∈ SplayState.evalPairs pathPayload s (t.findSubtree x) subFlip subTag,
        p ∈ SplayState.evalPairs pathPayload s t flip acc := by
  induction t generalizing flip acc with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
    let nd := s.nodes id
    let nextFlip := flip ^^ nd.rev
    let localTag := if flip then nd.tag.reverse else nd.tag
    let nextTag := acc.compose localTag
    have htag : pathTagMagnitude nextTag ≤ pathTagMagnitude acc + pathTagMagnitude nd.tag := by
      have hlocal : pathTagMagnitude localTag = pathTagMagnitude nd.tag := by
        cases flip <;> simp [localTag, pathTagMagnitude_reverse]
      exact (pathTagMagnitude_compose acc localTag).trans (by rw [hlocal])
    have leftOrRight {p : ℕ × Option PathEdgeValue}
        (hp : p ∈ SplayState.evalPairs pathPayload s l nextFlip nextTag ∨
          p ∈ SplayState.evalPairs pathPayload s r nextFlip nextTag) :
        p ∈ SplayState.evalPairs pathPayload s (.node id l r) flip acc := by
      cases flip <;>
        simp only [SplayState.evalPairs, Bool.false_eq_true, ite_false, ite_true, List.mem_append] <;>
        rcases hp with hp | hp <;> first | exact Or.inl (Or.inl hp) | exact Or.inr hp
    have extend {c : AuxTree} {subTag : PathTag}
        (he : (AuxTree.node id l r).pathTo x = id :: c.pathTo x)
        (hb : pathTagMagnitude subTag ≤ pathTagMagnitude nextTag +
          pathTagRouteMagnitude s (c.pathTo x)) :
        pathTagMagnitude subTag ≤ pathTagMagnitude acc +
          pathTagRouteMagnitude s ((AuxTree.node id l r).pathTo x) := by
      rw [he]
      change _ ≤ _ + (pathTagMagnitude nd.tag + pathTagRouteMagnitude s (c.pathTo x))
      omega
    by_cases he : x = id
    · subst x
      refine ⟨flip, acc, ?_, ?_⟩
      · simp only [AuxTree.pathTo, ite_true, pathTagRouteMagnitude, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, pathTagMagnitude]
        exact le_add_of_nonneg_right (add_nonneg (abs_nonneg _) (abs_nonneg _))
      · simp only [AuxTree.findSubtree, ite_true]
        exact fun _ h => h
    · by_cases hxl : x ∈ l.toList
      · obtain ⟨f, a, hb, hm⟩ := ihl hxl nextFlip nextTag
        refine ⟨f, a, extend (c := l) (by simp [AuxTree.pathTo, he, hxl]) hb, ?_⟩
        simp only [AuxTree.findSubtree, Ne.symm he, ite_false, hxl, ite_true]
        exact fun p hp => leftOrRight (Or.inl (hm p hp))
      · have hxr : x ∈ r.toList := by simpa [AuxTree.toList, he, hxl] using hx
        obtain ⟨f, a, hb, hm⟩ := ihr hxr nextFlip nextTag
        refine ⟨f, a, extend (c := r) (by simp [AuxTree.pathTo, he, hxl, hxr]) hb, ?_⟩
        simp only [AuxTree.findSubtree, Ne.symm he, ite_false, hxl]
        exact fun p hp => leftOrRight (Or.inr (hm p hp))

/-- The local evaluation of a subtree can be bounded by the whole-tree
accounts and the tags on the route to its root. -/
theorem pathSubtreeAccounts_abs_le
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {t : AuxTree} {x : ℕ} {B R : ℤ} (hx : x ∈ t.toList)
    (hr : pathTagRouteMagnitude s (t.pathTo x) ≤ R)
    (hb : ∀ i v, (i, some v) ∈ SplayState.evalPairs pathPayload s t false pathPayload.idTag →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B) :
    ∀ i v, (i, some v) ∈ SplayState.evalPairs pathPayload s (t.findSubtree x) false pathPayload.idTag →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B + R ∧ |v.detector| ≤ B + R := by
  obtain ⟨f, a, ha, hsub⟩ := evalPairs_findSubtree_with_charge s hx false pathPayload.idTag
  have hz : pathTagMagnitude pathPayload.idTag = 0 := by
    simp [pathTagMagnitude, pathPayload, PathTag.zero]
  have haR : pathTagMagnitude a ≤ R := by rw [hz, zero_add] at ha; exact ha.trans hr
  intro i v h
  let sub := t.findSubtree x
  let v₀ := if f then v.reverse else v
  have hm : (i, some v₀) ∈ SplayState.evalPairs pathPayload s sub f pathPayload.idTag := by
    cases f
    · exact h
    · have hf := SplayState.evalPairs_flip pathPayload_laws s sub false pathPayload.idTag
      change SplayState.evalPairs pathPayload s sub true pathPayload.idTag = _ at hf
      rw [hf]
      exact List.mem_map.mpr ⟨(i, some v), List.mem_reverse.mpr h, rfl⟩
  have hn : (i, some (v₀.shift a)) ∈ SplayState.evalPairs pathPayload s sub f a := by
    have he := SplayState.evalPairs_compTag pathPayload_laws s sub f a pathPayload.idTag
    rw [pathPayload_laws.compTag_id_right] at he
    rw [he]
    exact List.mem_map.mpr ⟨(i, some v₀), hm, rfl⟩
  obtain ⟨hg, hl, hf, hd⟩ := hb i _ (hsub _ hn)
  obtain ⟨eg, el, ef, ed⟩ := pathEdgeValue_abs_le_shifted v a f
  change |v.gradient| = |(v₀.shift a).gradient| at eg
  change v.length = (v₀.shift a).length at el
  change |v.flow| ≤ |(v₀.shift a).flow| + pathTagMagnitude a at ef
  change |v.detector| ≤ |(v₀.shift a).detector| + pathTagMagnitude a at ed
  exact ⟨eg.trans_le hg, by rwa [el], by omega, by omega⟩

/-- The active raw node fits the account bound scaled by its subtree size.
The size term is used for the stored gradient and length sums. -/
theorem pathNodeBound_of_evaluatedAccounts
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {x : ℕ} {B R : ℤ}
    (ht : SplayState.TreeInv pathPayload s t) (hx : x ∈ t.toList)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hr : pathTagRouteMagnitude s (t.pathTo x) ≤ R)
    (hb : ∀ i v, (i, some v) ∈ SplayState.evalPairs pathPayload s t false pathPayload.idTag →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B) :
    PathNodeBound (((t.findSubtree x).countNodes : ℤ) * (B + R) + (B + R)) (s.nodes x) := by
  let amount := B + R
  have ha : 0 ≤ amount := add_nonneg hB hR
  let size := ((t.findSubtree x).countNodes : ℤ)
  have hsize : 0 ≤ size := Int.natCast_nonneg _
  have hprod : 0 ≤ size * amount := mul_nonneg hsize ha
  have hwide : amount ≤ size * amount + amount := le_add_of_nonneg_left hprod
  have hsumwide : size * amount ≤ size * amount + amount := le_add_of_nonneg_right ha
  have hBwide : B ≤ size * amount + amount := (le_add_of_nonneg_right hR).trans hwide
  have hRwide : R ≤ size * amount + amount := (le_add_of_nonneg_left hB).trans hwide
  have htag := pathTagMagnitude_le_of_route_bound hx hr
  have hflow : |(s.nodes x).tag.flow| ≤ R := by
    have h := abs_nonneg (s.nodes x).tag.detector
    unfold pathTagMagnitude at htag
    omega
  have hdetector : |(s.nodes x).tag.detector| ≤ R := by
    have h := abs_nonneg (s.nodes x).tag.flow
    unfold pathTagMagnitude at htag
    omega
  have hsub := SplayState.SubtreeInv_findSubtree ht.nodup ht.sub hx
  have hsubAccounts := pathSubtreeAccounts_abs_le s hx hr hb
  obtain ⟨l, r, he⟩ := AuxTree.findSubtree_root_of_mem hx
  rw [he] at hsub hsubAccounts
  have hsummary := pathSubtreeSummary_abs_le hsub ha (fun i v hm => by
    obtain ⟨hg, hl, _, hd⟩ := hsubAccounts i v hm
    exact ⟨hg.trans (le_add_of_nonneg_right hR), hl.trans (le_add_of_nonneg_right hR), hd⟩)
  change |(s.nodes x).sum.gradient| ≤ ((AuxTree.node x l r).countNodes : ℤ) * amount ∧
    |(s.nodes x).sum.length| ≤ ((AuxTree.node x l r).countNodes : ℤ) * amount ∧
    (∀ d, (s.nodes x).sum.detector = some d → |d| ≤ amount) at hsummary
  rw [← he] at hsummary
  obtain ⟨hg, hl, hd⟩ := hsummary
  refine ⟨?_, hg.trans hsumwide, hl.trans hsumwide, fun z hz => (hd z hz).trans hwide,
    hflow.trans hRwide, hdetector.trans hRwide⟩
  intro v hv
  obtain ⟨value, hm, eg, el, ef, ed⟩ := pathRawAccount_abs_le s ht.nodup hx hv
  obtain ⟨hvg, hvl, hvf, hvd⟩ := hb x value hm
  exact ⟨(eg.trans_le hvg).trans hBwide, (by rw [el]; exact hvl.trans hBwide),
    (ef.trans (add_le_add hvf hr)).trans hwide, (ed.trans (add_le_add hvd hr)).trans hwide⟩

private theorem findSubtree_countNodes_le (t : AuxTree) (x : ℕ) :
    (t.findSubtree x).countNodes ≤ t.countNodes := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
    by_cases hr : id = x
    · simp [AuxTree.findSubtree, hr]
    · by_cases hl : x ∈ l.toList
      · simp only [AuxTree.findSubtree, hr, ite_false, hl, ite_true, AuxTree.countNodes]
        omega
      · simp only [AuxTree.findSubtree, hr, ite_false, hl, AuxTree.countNodes]
        omega

private theorem pathNodeBound_mono {s : SplayNode (Option PathEdgeValue) PathSummary PathTag}
    {B C : ℤ} (h : PathNodeBound B s) (hBC : B ≤ C) : PathNodeBound C s := by
  obtain ⟨hv, hg, hl, hd, hf, ht⟩ := h
  refine ⟨?_, hg.trans hBC, hl.trans hBC, fun z hz => (hd z hz).trans hBC,
    hf.trans hBC, ht.trans hBC⟩
  intro v hval
  obtain ⟨hg, hl, hf, hd⟩ := hv v hval
  exact ⟨hg.trans hBC, hl.trans hBC, hf.trans hBC, hd.trans hBC⟩

/-- Evaluated accounts and route budgets give a signed range for a forest,
provided the same range covers the inactive slots. -/
theorem pathTreeFits_of_evaluatedAccounts
    {s : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    {h L : ℕ} {B R : ℤ}
    (W : LctInvWith pathPayload s trees freeList depth) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hr : ∀ t ∈ trees, ∀ x ∈ t.toList, pathTagRouteMagnitude s.splay (t.pathTo x) ≤ R)
    (hb : ∀ t ∈ trees, ∀ i v,
      (i, some v) ∈ SplayState.evalPairs pathPayload s.splay t false pathPayload.idTag →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B)
    (hfree : ∀ i ≤ 2 * s.n, i ∉ trees.flatMap AuxTree.toList →
      PathNodeBound (((2 * s.n + 1 : ℕ) : ℤ) * (B + R)) (s.splay.nodes i))
    (hroom : 2 * ((2 * s.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity h L : ℤ)) :
    pathTreeFits h L s := by
  apply pathTreeFits_of_nodeBound
  · intro i hi
    by_cases ha : i ∈ trees.flatMap AuxTree.toList
    · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.mp ha
      have hc := findSubtree_countNodes_le t i
      have hlen := tree_length_le_active ht
      rw [AuxTree.length_toList] at hlen
      have hall := active_length_le_two_mul W.activeNodup W.activeValid
      have hs : ((t.findSubtree i).countNodes : ℤ) + 1 ≤ ((2 * s.n + 1 : ℕ) : ℤ) := by omega
      exact pathNodeBound_mono
        (pathNodeBound_of_evaluatedAccounts (W.treesInv t ht) hit hB hR (hr t ht i hit) (hb t ht))
        (by rw [← add_one_mul]; exact mul_le_mul_of_nonneg_right hs (add_nonneg hB hR))
    · exact hfree i hi ha
  · simpa only [mul_assoc] using hroom

/-- Point writes preserve the lazy tag budget. The new account is written
after its slot has been exposed. -/
theorem pathTreeWrite_route_bound
    {st : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {slot : ℕ} {B : ℤ} (ht : t ∈ trees) (hs : slot ∈ t.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B)
    (value : Option PathEdgeValue) :
    ∃ trees', LctInvWith pathPayload (pathTreeWrite st slot value) trees' freeList depth ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList,
        pathTagRouteMagnitude (pathTreeWrite st slot value).splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList,
        (pathTreeWrite st slot value).splay.nodes z = st.splay.nodes z) := by
  obtain ⟨ts, W₁, hb₁, frame⟩ := lctExpose_route_bound_and_frame W ht hs hb
  obtain ⟨us, W₂, _⟩ := pathTreeWrite_forestPairs W ht hs value
  refine ⟨us, W₂, ?_, ?_⟩
  let s := (lctExpose pathPayload st slot).splay
  have hptr x :
      ((pathTreeWrite st slot value).splay.nodes x).left = (s.nodes x).left ∧
      ((pathTreeWrite st slot value).splay.nodes x).right = (s.nodes x).right ∧
      ((pathTreeWrite st slot value).splay.nodes x).par = (s.nodes x).par ∧
      ((pathTreeWrite st slot value).splay.nodes x).tag = (s.nodes x).tag := by
    by_cases h : x = slot
    · subst x
      simp [pathTreeWrite, s, SplayState.pull_left_eq, SplayState.pull_right_eq,
        SplayState.pull_par_eq, SplayState.pull_tag_eq]
    · rw [pathTreeWrite_node_of_ne st h value]
      exact ⟨rfl, rfl, rfl, rfl⟩
  · intro c hc y hy
    have hmem := lct_tree_mem_of_same_pointers W₁ W₂ rfl
      (fun z => (hptr z).1.symm) (fun z => (hptr z).2.1.symm) (fun z => (hptr z).2.2.1.symm) hc
    rw [pathTagRouteMagnitude_congr _ (fun z => (hptr z).2.2.2)]
    exact hb₁ c hmem y hy

  · intro z hz
    have hne : z ≠ slot := fun h => hz (List.mem_flatMap.mpr ⟨t, ht, h ▸ hs⟩)
    exact (pathTreeWrite_node_of_ne st hne value).trans (frame z hz)

/-- Rerooting can reverse accounts along its exposed path, preserving all
four numeric magnitudes. -/
theorem pathForestAccounts_reroot_bound
    {st : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {x : ℕ} {B : ℤ} (ht : t ∈ trees) (hx : x ∈ t.toList)
    (hv : isVertex st.n x)
    (W' : LctInvWith pathPayload (lctReroot pathPayload st x) trees' freeList depth')
    (hb : ∀ i v, (i, some v) ∈ forestPairs pathPayload st.splay trees →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B) :
    ∀ i v, (i, some v) ∈ forestPairs pathPayload (lctReroot pathPayload st x).splay trees' →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B := by
  obtain ⟨us, _, _, _, W₀, _, _, _, _, _, _, _, hp, hq, _⟩ :=
    lctReroot_spec pathPayload_laws W ht hx hv
  intro i v h
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp h
  have hmem := lct_tree_mem_of_same_pointers W₀ W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hc
  have hm₀ : (i, some v) ∈ forestPairs pathPayload (lctRerootCost pathPayload st x).1.splay us :=
    List.mem_flatMap.mpr ⟨c, hmem, hm⟩
  rcases List.mem_append.mp (hq.mem_iff.mp hm₀) with hleft | hright
  · obtain ⟨⟨j, val⟩, hj, he⟩ := List.mem_map.mp (List.mem_reverse.mp hleft)
    cases val with
    | none => simp [pathPayload] at he
    | some a =>
      have hsv : v = a.reverse := by simpa [pathPayload, and_comm, eq_comm] using (Prod.mk.inj he).2
      have hmem := hp.mem_iff.mp (List.mem_append_left _ hj)
      rw [hsv]
      simpa [PathEdgeValue.reverse] using hb j a hmem
  · exact hb i v (hp.mem_iff.mp (List.mem_append_right _ hright))

/-- Link preserves the bound on existing accounts and adds the supplied value. -/
theorem pathForestAccounts_link_bound
    {st : PathTreeState} {trees trees' : List AuxTree} {edge : ℕ} {freeRest : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees (edge :: freeRest) depth)
    {u v : ℕ} {B : ℤ} (hu : isVertex st.n u) (hv : isVertex st.n v)
    (hdisc : subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u ≠
      subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v)
    {value : Option PathEdgeValue}
    (W' : LctInvWith pathPayload (lctLink pathPayload st u v value) trees' freeRest depth')
    (hvalue : ∀ val, value = some val →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B)
    (hb : ∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    ∀ i val, (i, some val) ∈ forestPairs pathPayload (lctLink pathPayload st u v value).splay trees' →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B := by
  obtain ⟨t, ht, htv⟩ := List.mem_flatMap.mp (pathVertex_mem_active W hv)
  obtain ⟨ts, _, d, _, WV, _⟩ := lctReroot_spec pathPayload_laws W ht htv hv
  have hu' : isVertex ((lctRerootCost pathPayload st v).1.n) u := hu
  obtain ⟨a, ha, hau⟩ := List.mem_flatMap.mp (pathVertex_mem_active WV hu')
  obtain ⟨us, du, bs, db, WU, WL, _, _, _, _, _, hp, _⟩ :=
    lctLink_spec pathPayload_laws W rfl hu hv hdisc value
  intro i val h
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp h
  have hmem := lct_tree_mem_of_same_pointers WL W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hc
  have hp' : (i, some val) ∈ forestPairs pathPayload (lctLinkCost pathPayload st u v value).1.splay bs :=
    List.mem_flatMap.mpr ⟨c, hmem, hm⟩
  rcases List.mem_cons.mp (hp.mem_iff.mp hp') with he | hp₂
  · exact hvalue val (Prod.mk.inj he).2.symm
  · exact pathForestAccounts_reroot_bound WV ha hau hu' WU
      (pathForestAccounts_reroot_bound W ht htv hv WV hb) i val hp₂

/-- A point write preserves the account magnitude bound when its new value fits. -/
theorem pathForestAccounts_write_bound
    {st : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {slot : ℕ} {B : ℤ} (ht : t ∈ trees) (hs : slot ∈ t.toList)
    {value : Option PathEdgeValue}
    (W' : LctInvWith pathPayload (pathTreeWrite st slot value) trees' freeList depth')
    (hvalue : ∀ val, value = some val →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B)
    (hb : ∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    ∀ i val, (i, some val) ∈ forestPairs pathPayload (pathTreeWrite st slot value).splay trees' →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B := by
  obtain ⟨us, WW, hwrite⟩ := pathTreeWrite_forestPairs W ht hs value
  intro i val h
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp h
  have hmem := lct_tree_mem_of_same_pointers WW W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hc
  rcases (hwrite i (some val)).mp (List.mem_flatMap.mpr ⟨_, hmem, hm⟩) with hval | hprev
  · exact hvalue val hval.2.symm
  · exact hb i val hprev.2

/-- Path updates increase evaluated account magnitudes by at most the
magnitude of the applied tag. -/
theorem pathForestAccounts_apply_bound
    {st : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {tu tv : AuxTree} {u v : ℕ} {B : ℤ}
    (htu : tu ∈ trees) (hu : u ∈ tu.toList) (huv : isVertex st.n u)
    (htv : tv ∈ trees) (hv : v ∈ tv.toList) (hvv : isVertex st.n v)
    (hconn : subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u =
      subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v)
    {tag : PathTag}
    (W' : LctInvWith pathPayload (lctPathApply pathPayload st u v tag) trees' freeList depth')
    (hb : ∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    let C := B + pathTagMagnitude tag
    ∀ i val, (i, some val) ∈ forestPairs pathPayload (lctPathApply pathPayload st u v tag).splay trees' →
      |val.gradient| ≤ C ∧ |val.length| ≤ C ∧ |val.flow| ≤ C ∧ |val.detector| ≤ C := by
  intro C i val h
  obtain ⟨ts, _, d, _, WR, _⟩ := lctReroot_spec pathPayload_laws W htu hu huv
  have hv₁ : isVertex ((lctRerootCost pathPayload st u).1.n) v := hvv
  obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.mp (pathVertex_mem_active WR hv₁)
  obtain ⟨es, _, _, WE, _, _, hpermE, _⟩ := lctExpose_spec pathPayload_laws WR ht hmem
  obtain ⟨as, l, _, htA, WA, _, _, _, _, _, _, hpermA, _, _⟩ :=
    lctPathApply_spec pathPayload_laws W htu hu huv htv hv hconn tag
  let exp := (lctExposeCost pathPayload (lctRerootCost pathPayload st u).1 v).1
  have hmE {c : AuxTree} (hc : c ∈ as) : c ∈ es :=
    lct_tree_mem_of_same_pointers WE WA rfl
      (fun z => (pathApply_nodePointers exp.splay v tag z).1.symm)
      (fun z => (pathApply_nodePointers exp.splay v tag z).2.1.symm)
      (fun z => (pathApply_nodePointers exp.splay v tag z).2.2.symm) hc
  have bounded {c : AuxTree} (hc : c ∈ as) {j a}
      (ha : (j, some a) ∈ SplayState.evalPairs pathPayload exp.splay c false pathPayload.idTag) :
      |a.gradient| ≤ B ∧ |a.length| ≤ B ∧ |a.flow| ≤ B ∧ |a.detector| ≤ B :=
    pathForestAccounts_reroot_bound W htu hu huv WR hb j a
      (hpermE.mem_iff.mp (List.mem_flatMap.mpr ⟨_, hmE hc, ha⟩))
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp h
  have hmemA := lct_tree_mem_of_same_pointers WA W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hc
  have hmA : (i, some val) ∈ forestPairs pathPayload (lctPathApplyCost pathPayload st u v tag).1.splay as :=
    List.mem_flatMap.mpr ⟨c, hmemA, hm⟩
  have hn : 0 ≤ pathTagMagnitude tag := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmono : B ≤ C := le_add_of_nonneg_right hn
  rcases List.mem_append.mp (hpermA.mem_iff.mp hmA) with on | off
  · obtain ⟨⟨j, a⟩, ha, he⟩ := List.mem_map.mp on
    cases a with
    | none => simp [pathPayload] at he
    | some a =>
      have hvEq : val = a.shift tag := by simpa [pathPayload, eq_comm] using (Prod.mk.inj he).2
      obtain ⟨hg, hl, hf, hd⟩ := bounded htA ha
      rw [hvEq]
      change |a.gradient| ≤ C ∧ |a.length| ≤ C ∧
        |a.flow + tag.flow| ≤ C ∧ |a.detector + tag.detector| ≤ C
      have hnF := abs_nonneg tag.flow
      have hnD := abs_nonneg tag.detector
      refine ⟨hg.trans hmono, hl.trans hmono, (abs_add_le _ _).trans ?_, (abs_add_le _ _).trans ?_⟩
      all_goals dsimp [C, pathTagMagnitude]; omega
  · obtain ⟨t, htt, hval⟩ := List.mem_flatMap.mp off
    obtain ⟨hg, hl, hf, hd⟩ := bounded (List.mem_of_mem_erase htt) hval
    exact ⟨hg.trans hmono, hl.trans hmono, hf.trans hmono, hd.trans hmono⟩

/-- Exposure preserves all evaluated account magnitudes. -/
theorem pathForestAccounts_expose_bound
    {st : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {x : ℕ} {B : ℤ} (ht : t ∈ trees) (hx : x ∈ t.toList)
    (W' : LctInvWith pathPayload (lctExpose pathPayload st x) trees' freeList depth')
    (hb : ∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    ∀ i val, (i, some val) ∈ forestPairs pathPayload (lctExpose pathPayload st x).splay trees' →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B := by
  obtain ⟨us, _, _, WE, _, _, hp, _⟩ := lctExpose_spec pathPayload_laws W ht hx
  intro i val h
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp h
  have hmem := lct_tree_mem_of_same_pointers WE W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hc
  exact hb i val (hp.mem_iff.mp (List.mem_flatMap.mpr ⟨_, hmem, hm⟩))

/-- Computing a path summary preserves all evaluated account magnitudes. -/
theorem pathForestAccounts_summary_bound
    {st : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {u v : ℕ} {B : ℤ} (ht : t ∈ trees) (hu : u ∈ t.toList)
    (huv : isVertex st.n u) (hvv : isVertex st.n v)
    (W' : LctInvWith pathPayload (lctPathSummary pathPayload st u v).1 trees' freeList depth')
    (hb : ∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    ∀ i val, (i, some val) ∈ forestPairs pathPayload (lctPathSummary pathPayload st u v).1.splay trees' →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B := by
  obtain ⟨ts, _, _, _, WR, _⟩ := lctReroot_spec pathPayload_laws W ht hu huv
  have hv₁ : isVertex ((lctRerootCost pathPayload st u).1.n) v := hvv
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp (pathVertex_mem_active WR hv₁)
  exact pathForestAccounts_expose_bound WR hc hm W'
    (pathForestAccounts_reroot_bound W ht hu huv WR hb)

end MinCostFlow.MinRatio
