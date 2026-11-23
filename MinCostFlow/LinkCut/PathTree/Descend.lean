module

public import MinCostFlow.LinkCut.ForestExposeOps
import MinCostFlow.LinkCut.SplayLazy

/-!
# The descent to a ready edge

Find-ready starts at the root of an auxiliary tree whose summary reports a ready value. It walks
down to a node whose own value is ready. At each node it first pushes the lazy flags down, so the
stored summaries of the children are exact. Then it goes left if the left child's summary is
ready, stops if the node's own value is ready, and goes right otherwise. This is `descend`.

The payload is generic here. `rs` tests a summary and `rv` tests a value, and they must agree
with `listSummary`: a summary of a list is ready exactly when some value in it is ready
(`ReadyLaw`).

The main facts:
* `descend_spec`: the descent from the root of a tree stops at a node `y` whose value is ready,
  and `(y, value)` is one of the evaluated pairs of the tree. The state is the start state with
  the nodes from the root down to `y` pushed, in this order, and these nodes are left clean.
* `descend_pushPath`: so the state after the descent is `pushPath s F y`.
* `splay_descend`: splaying `y` after the descent gives the same state as splaying `y` at the
  start. So exposing `y` after the descent gives `lctExpose s y` (`lctExpose_descend`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.LinkCut SplayState

variable {α σ τ : Type*}

/-- Summary and value tests agree: a summary of a list is ready exactly when some value in the
list is ready. -/
def ReadyLaw (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) : Prop :=
  ∀ ps : List (ℕ × α), rs (P.listSummary ps) = true ↔ ∃ p ∈ ps, rv p.2 = true

/-- Walk down from `x`, pushing lazy flags, to a node whose value is ready. -/
def descend (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) (s : SplayState α σ τ) :
    ℕ → ℕ → SplayState α σ τ × ℕ
  | 0, x => (s, x)
  | k + 1, x =>
    let s1 := pushDown P s x
    let l := (s1.nodes x).left
    if l ≠ 0 ∧ rs (s1.nodes l).sum = true then descend P rs rv s1 k l
    else if rv (s1.nodes x).val = true then (s1, x)
    else descend P rs rv s1 k (s1.nodes x).right

end MinCostFlow.LinkCut.PathTree

namespace MinCostFlow.LinkCut.Gen

variable {α σ τ : Type*}

/-- The number of nodes `descend P rs rv st fuel x` visits. -/
def descendSteps (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) :
    SplayState α σ τ → ℕ → ℕ → ℕ
  | _, 0, _ => 0
  | st, k + 1, x =>
    let s1 := SplayState.pushDown P st x
    let l := (s1.nodes x).left
    if l ≠ 0 ∧ rs (s1.nodes l).sum = true then 1 + descendSteps P rs rv s1 k l
    else if rv (s1.nodes x).val = true then 1
    else 1 + descendSteps P rs rv s1 k (s1.nodes x).right

end MinCostFlow.LinkCut.Gen

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.LinkCut SplayState

variable {α σ τ : Type*}

/-- Push the nodes of a list, in order. -/
def pushSeq (P : LctPayload α σ τ) (s : SplayState α σ τ) (L : List ℕ) : SplayState α σ τ :=
  L.foldl (pushDown P) s

/-- The nodes `pushPath s k y` pushes, from the top down to `y`. -/
def chainList (s : SplayState α σ τ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, y =>
    if y = 0 then [] else
      (if (s.nodes y).par = 0 then [] else chainList s k (s.nodes y).par) ++ [y]

/-- Each entry of the list is the parent of the entry before it. -/
def ParChain (par : ℕ → ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => par a = b ∧ ParChain par (b :: rest)

theorem ParChain.append_single {par : ℕ → ℕ} :
    ∀ {L : List ℕ} {x : ℕ}, ParChain par L → (∀ a ∈ L.getLast?, par a = x) →
      ParChain par (L ++ [x])
  | [], _, _, _ => trivial
  | [a], x, _, h => ⟨h a rfl, trivial⟩
  | a :: b :: rest, x, hc, h => ⟨hc.1, ParChain.append_single (L := b :: rest) hc.2
      (fun c hc' => h c (by simpa [List.getLast?_cons_cons] using hc'))⟩

theorem ParChain.congr {par par' : ℕ → ℕ} (h : ∀ z, par' z = par z) :
    ∀ {L : List ℕ}, ParChain par L → ParChain par' L
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: b :: rest, hc => ⟨(h _).trans hc.1, ParChain.congr h (L := b :: rest) hc.2⟩

theorem pushSeq_nil (P : LctPayload α σ τ) (s : SplayState α σ τ) : pushSeq P s [] = s := rfl

theorem pushSeq_cons (P : LctPayload α σ τ) (s : SplayState α σ τ) (x : ℕ) (L : List ℕ) :
    pushSeq P s (x :: L) = pushSeq P (pushDown P s x) L := rfl

theorem pushSeq_append_single (P : LctPayload α σ τ) (s : SplayState α σ τ) (L : List ℕ)
    (y : ℕ) : pushSeq P s (L ++ [y]) = pushDown P (pushSeq P s L) y := by
  simp [pushSeq, List.foldl_append]

theorem pushPath_eq_pushSeq (P : LctPayload α σ τ) (s : SplayState α σ τ) :
    ∀ k y, pushPath P s k y = pushSeq P s (chainList s k y)
  | 0, _ => rfl
  | k + 1, y => by
    unfold pushPath chainList
    by_cases hy : y = 0
    · simp [hy, pushSeq_nil]
    rw [if_neg hy, if_neg hy, pushSeq_append_single]
    by_cases hp : (s.nodes y).par = 0
    · simp [hp, pushSeq_nil]
    · simp only [hp, if_false]
      rw [pushPath_eq_pushSeq P s k]

theorem par_updateNode {s : SplayState α σ τ} {x : ℕ} {f : SplayNode α σ τ → SplayNode α σ τ}
    (hf : ∀ nd, (f nd).par = nd.par) (z : ℕ) :
    ((s.updateNode x f).nodes z).par = (s.nodes z).par := by
  rw [nodes_updateNode]
  split_ifs with h
  · subst h; exact hf _
  · rfl

theorem par_revNode (P : LctPayload α σ τ) (s : SplayState α σ τ) (x z : ℕ) :
    ((revNode P s x).nodes z).par = (s.nodes z).par := by
  unfold revNode; split_ifs
  · rfl
  · apply par_updateNode; intro; rfl

theorem par_applyTagNode (P : LctPayload α σ τ) (s : SplayState α σ τ) (x : ℕ) (t : τ)
    (z : ℕ) : ((applyTagNode P s x t).nodes z).par = (s.nodes z).par := by
  unfold applyTagNode; split_ifs
  · rfl
  · apply par_updateNode; intro; rfl

/-- `pushDown` does not change any parent pointer. -/
theorem par_pushDown (P : LctPayload α σ τ) (s : SplayState α σ τ) (x z : ℕ) :
    ((pushDown P s x).nodes z).par = (s.nodes z).par := by
  unfold pushDown pushDownTag
  have hrev : ((pushDownRev P s x).nodes z).par = (s.nodes z).par := by
    unfold pushDownRev; dsimp only; split_ifs
    · rfl
    · rw [par_revNode, par_revNode]; apply par_updateNode; intro; rfl
    · rfl
  dsimp only
  split_ifs
  · exact hrev
  · exact hrev
  · rw [par_applyTagNode, par_applyTagNode, ← hrev]; apply par_updateNode; intro; rfl

theorem par_pushSeq (P : LctPayload α σ τ) (s : SplayState α σ τ) (L : List ℕ) (z : ℕ) :
    ((pushSeq P s L).nodes z).par = (s.nodes z).par := by
  induction L generalizing s with
  | nil => rfl
  | cons x L ih => rw [pushSeq_cons, ih, par_pushDown]

theorem chainList_congr {s s' : SplayState α σ τ} (h : ∀ z, (s'.nodes z).par = (s.nodes z).par) :
    ∀ k y, chainList s' k y = chainList s k y
  | 0, _ => rfl
  | k + 1, y => by
    unfold chainList
    rw [h y, chainList_congr h k]

/-- A list from `y` up to a node with parent `0`, each entry the parent of the one before, is
read back by `chainList` when the fuel is at least its length. -/
theorem chainList_of_chain (s : SplayState α σ τ) :
    ∀ (rp : List ℕ) (y : ℕ) (k : ℕ), ParChain (fun a => (s.nodes a).par) (y :: rp) →
      (∀ z ∈ y :: rp, z ≠ 0) → ((y :: rp).getLast (List.cons_ne_nil _ _) |> fun r =>
        (s.nodes r).par = 0) → (y :: rp).length ≤ k → chainList s k y = (y :: rp).reverse
  | [], y, k, _, hz, hr, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hy : y ≠ 0 := hz y List.mem_cons_self
    simp only [List.getLast_singleton] at hr
    simp [chainList, hy, hr]
  | p :: rp, y, k, hc, hz, hr, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hy : y ≠ 0 := hz y List.mem_cons_self
    have hp : p ≠ 0 := hz p (List.mem_cons_of_mem _ List.mem_cons_self)
    have ih := chainList_of_chain s rp p k hc.2 (fun z hz' => hz z (List.mem_cons_of_mem _ hz'))
      (by simpa [List.getLast_cons] using hr) (by simp at hk ⊢; omega)
    have h1 : (s.nodes y).par = p := hc.1
    unfold chainList
    rw [if_neg hy, h1, if_neg hp, ih]
    simp

/-- Pushing a node with no reversal and the identity tag changes nothing. -/
theorem pushDown_clean {P : LctPayload α σ τ} (hL : P.Laws) {s : SplayState α σ τ} {x : ℕ}
    (hr : (s.nodes x).rev = false) (ht : (s.nodes x).tag = P.idTag) : pushDown P s x = s := by
  unfold pushDown pushDownTag pushDownRev
  by_cases hx : x = 0
  · simp [hx]
  simp [hx, hr, ht, hL.isIdTag_id]

theorem pushSeq_clean {P : LctPayload α σ τ} (hL : P.Laws) {s : SplayState α σ τ} :
    ∀ L : List ℕ, (∀ z ∈ L, (s.nodes z).rev = false ∧ (s.nodes z).tag = P.idTag) →
      pushSeq P s L = s
  | [], _ => rfl
  | x :: L, h => by
    rw [pushSeq_cons, pushDown_clean hL (h x List.mem_cons_self).1 (h x List.mem_cons_self).2]
    exact pushSeq_clean hL L fun z hz => h z (List.mem_cons_of_mem _ hz)

/-- The result of a descent from the root of the subtree `c`. -/
structure DescendOut (P : LctPayload α σ τ) (rv : α → Bool) (D : SplayState α σ τ)
    (c : AuxTree) (k : ℕ) (D' : SplayState α σ τ) (y : ℕ) (rpath : List ℕ) : Prop where
  head : rpath.head? = some y
  last : rpath.getLast? = some c.rootId
  state : D' = pushSeq P D rpath.reverse
  chain : ParChain (fun a => (D.nodes a).par) rpath
  mem : ∀ z ∈ rpath, z ∈ c.toList
  len : rpath.length ≤ k
  clean : ∀ z ∈ rpath, (D'.nodes z).rev = false ∧ (D'.nodes z).tag = P.idTag
  out : ∀ u ∉ c.toList, D'.nodes u = D.nodes u
  pair : (y, (D'.nodes y).val) ∈ evalPairs P D c false P.idTag
  ready : rv (D'.nodes y).val = true

theorem descend_spec {P : LctPayload α σ τ} (hL : P.Laws) {rs : σ → Bool} {rv : α → Bool}
    (hR : ReadyLaw P rs rv) :
    ∀ (c : AuxTree) (D : SplayState α σ τ) (rp k : ℕ), c ≠ .leaf → c.toList.Nodup →
      SubtreeInv P D rp c → rs (D.nodes c.rootId).sum = true → c.countNodes ≤ k →
      ∃ rpath, DescendOut P rv D c k (descend P rs rv D k c.rootId).1
        (descend P rs rv D k c.rootId).2 rpath ∧
        Gen.descendSteps P rs rv D k c.rootId = rpath.length
  | .leaf, _, _, _, hc, _, _, _, _ => absurd rfl hc
  | .node x l r, D, rp, k, _, hnd, hsub, hrs, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp [AuxTree.countNodes] at hk; omega⟩
    rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hx_nl, hr_nd, hx_nr, hdisj⟩
    have hsum := hsub.2.2.2.2.2.2.1
    rcases pushDown_root_preserves hL hnd hsub with ⟨hsub1, hrev1, htag1, -, hev1, hout1⟩
    set D1 := pushDown P D x with hD1
    set l' := if (D.nodes x).rev then l.revRoot else l with hl'
    set r' := if (D.nodes x).rev then r.revRoot else r with hr'
    have hpl : l'.toList.Perm l.toList := by
      rw [hl']; split_ifs
      · exact revRoot_toList_perm l
      · exact List.Perm.refl _
    have hpr : r'.toList.Perm r.toList := by
      rw [hr']; split_ifs
      · exact revRoot_toList_perm r
      · exact List.Perm.refl _
    have hcnt_l : l'.countNodes = l.countNodes := by
      rw [← AuxTree.length_toList, ← AuxTree.length_toList, hpl.length_eq]
    have hcnt_r : r'.countNodes = r.countNodes := by
      rw [← AuxTree.length_toList, ← AuxTree.length_toList, hpr.length_eq]
    obtain ⟨-, hleft1, hright1, -, -, -, hsum1, hsl, hsr⟩ := hsub1
    -- the evaluated pairs at `x` after the push
    have hev : evalPairs P D (.node x l r) false P.idTag =
        evalPairs P D1 l' false P.idTag ++ [(x, (D1.nodes x).val)] ++
          evalPairs P D1 r' false P.idTag := by
      rw [← hev1]
      simp [evalPairs, hrev1, htag1, hL.compTag_id_left, hL.actVal_id]
    have hsub_l : ∀ z, z ∈ l'.toList → z ∈ (AuxTree.node x l r).toList := fun z hz => by
      simp [AuxTree.toList, hpl.mem_iff.mp hz]
    have hsub_r : ∀ z, z ∈ r'.toList → z ∈ (AuxTree.node x l r).toList := fun z hz => by
      simp [AuxTree.toList, hpr.mem_iff.mp hz]
    -- the sum of a nonempty child is the summary of its pairs
    have hsum_child : ∀ {c : AuxTree}, SubtreeInv P D1 x c → c ≠ .leaf →
        (D1.nodes c.rootId).sum = P.listSummary (evalPairs P D1 c false P.idTag) := by
      intro c hc hne
      cases c with
      | leaf => exact absurd rfl hne
      | node id a b => exact hc.2.2.2.2.2.2.1
    have hroot0 : ∀ {c : AuxTree}, SubtreeInv P D1 x c → (c.rootId = 0 ↔ c = .leaf) := by
      intro c hc
      cases c with
      | leaf => simp [AuxTree.rootId]
      | node id a b => simp [AuxTree.rootId, hc.1]
    have hpar_child : ∀ {c : AuxTree}, SubtreeInv P D1 x c → c ≠ .leaf →
        (D.nodes c.rootId).par = x := by
      intro c hc hne
      rw [← par_pushDown P D x]
      cases c with
      | leaf => exact absurd rfl hne
      | node id a b => exact hc.2.2.2.1
    -- the descent from a child
    have hstep : ∀ {c : AuxTree}, c ≠ .leaf → c.toList.Nodup →
        SubtreeInv P D1 x c → rs (D1.nodes c.rootId).sum = true → c.countNodes ≤ k →
        (∀ z, z ∈ c.toList → z ∈ (AuxTree.node x l r).toList) → x ∉ c.toList →
        evalPairs P D1 c false P.idTag ⊆ evalPairs P D (.node x l r) false P.idTag →
        ∃ rpath, DescendOut P rv D (.node x l r) (k + 1) (descend P rs rv D1 k c.rootId).1
          (descend P rs rv D1 k c.rootId).2 rpath ∧
          1 + Gen.descendSteps P rs rv D1 k c.rootId = rpath.length := by
      intro c hne hcnd hcs hcr hck hcm hxc hcsub
      have ih := descend_spec hL hR c D1 x k hne hcnd hcs hcr hck
      obtain ⟨rp', ⟨hh, hlast, hst, hch, hmem, hlen, hcl, hout, hpair, hrdy⟩, hsteps⟩ := ih
      have hrp_ne : rp' ≠ [] := by rintro rfl; simp at hh
      refine ⟨rp' ++ [x], ⟨?_, by simp [AuxTree.rootId], ?_, ?_, ?_, ?_, ?_, ?_, hcsub hpair, hrdy⟩,
        by rw [hsteps, List.length_append, List.length_singleton]; omega⟩
      · rw [List.head?_append, hh]; rfl
      · rw [hst, List.reverse_append]; rfl
      · refine ParChain.append_single (hch.congr fun a => (par_pushDown P D x a).symm) ?_
        intro a ha
        rw [hlast] at ha; cases ha
        exact hpar_child hcs hne
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hcm z (hmem z hz)
        · simp at hz; simp [hz, AuxTree.toList]
      · simp only [List.length_append, List.length_singleton]; omega
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hcl z hz
        · rw [List.mem_singleton] at hz
          rw [hz, hout _ hxc]; exact ⟨hrev1, htag1⟩
      · intro u hu
        rw [hout u (fun h => hu (hcm u h)), hD1, hout1 u hu]
    -- the case split of `descend`
    have hdesc : descend P rs rv D (k + 1) x =
        if (D1.nodes x).left ≠ 0 ∧ rs (D1.nodes (D1.nodes x).left).sum = true then
          descend P rs rv D1 k (D1.nodes x).left
        else if rv (D1.nodes x).val = true then (D1, x)
        else descend P rs rv D1 k (D1.nodes x).right := rfl
    have hdsteps : Gen.descendSteps P rs rv D (k + 1) x =
        if (D1.nodes x).left ≠ 0 ∧ rs (D1.nodes (D1.nodes x).left).sum = true then
          1 + Gen.descendSteps P rs rv D1 k (D1.nodes x).left
        else if rv (D1.nodes x).val = true then 1
        else 1 + Gen.descendSteps P rs rv D1 k (D1.nodes x).right := rfl
    simp only [AuxTree.rootId]
    rw [hdesc, hdsteps, hleft1, hright1]
    have hk_l : l'.countNodes ≤ k := by simp [AuxTree.countNodes] at hk; omega
    have hk_r : r'.countNodes ≤ k := by simp [AuxTree.countNodes] at hk; omega
    have hnd_l : l'.toList.Nodup := hpl.nodup_iff.mpr hl_nd
    have hnd_r : r'.toList.Nodup := hpr.nodup_iff.mpr hr_nd
    have hx_l : x ∉ l'.toList := fun h => hx_nl (hpl.mem_iff.mp h)
    have hx_r : x ∉ r'.toList := fun h => hx_nr (hpr.mem_iff.mp h)
    split_ifs with hgl hgv
    · have hne : l' ≠ .leaf := fun h => hgl.1 ((hroot0 hsl).mpr h)
      exact hstep hne hnd_l hsl hgl.2 hk_l hsub_l hx_l
        (fun p hp => by rw [hev]; simp [hp])
    · exact ⟨[x], ⟨rfl, rfl, rfl, trivial, by simp [AuxTree.toList], by simp,
        by simp [hrev1, htag1], fun u hu => hout1 u hu, by rw [hev]; simp, hgv⟩, rfl⟩
    · -- the ready pair is in the right part
      have hready : ∃ p ∈ evalPairs P D1 r' false P.idTag, rv p.2 = true := by
        have h0 := (hR _).mp (hsum ▸ hrs)
        rw [hev] at h0
        obtain ⟨p, hp, hpv⟩ := h0
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | rfl) | hp
        · exfalso
          have hne : l' ≠ .leaf := by
            intro h; rw [h] at hp; simp [evalPairs] at hp
          apply hgl
          refine ⟨fun h => hne ((hroot0 hsl).mp h), ?_⟩
          rw [hsum_child hsl hne, hR]
          exact ⟨p, hp, hpv⟩
        · exact absurd hpv hgv
        · exact ⟨p, hp, hpv⟩
      have hne : r' ≠ .leaf := by
        intro h; rw [h] at hready; simp [evalPairs] at hready
      have hrs_r : rs (D1.nodes r'.rootId).sum = true := by
        rw [hsum_child hsr hne, hR]; exact hready
      exact hstep hne hnd_r hsr hrs_r hk_r hsub_r hx_r
        (fun p hp => by rw [hev]; simp [hp])

theorem subtreeInv_ne_zero {P : LctPayload α σ τ} {s : SplayState α σ τ} :
    ∀ {t : AuxTree} {rp z : ℕ}, SubtreeInv P s rp t → z ∈ t.toList → z ≠ 0
  | .leaf, _, _, _, hz => by simp [AuxTree.toList] at hz
  | .node id l r, _, z, h, hz => by
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | rfl) | hz
    · exact subtreeInv_ne_zero h.2.2.2.2.2.2.2.1 hz
    · exact h.1
    · exact subtreeInv_ne_zero h.2.2.2.2.2.2.2.2 hz

/-- The chain of `y` has at most one node more than the depth `splayDepth` counts. -/
theorem chainList_length_le (s : SplayState α σ τ) :
    ∀ (k y : ℕ), (chainList s k y).length ≤ splayDepth s k y + 1
  | 0, _ => by simp [chainList]
  | k + 1, y => by
    have ih := chainList_length_le s k (s.nodes y).par
    simp only [chainList, splayDepth]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hp : (s.nodes y).par = 0
    · simp [hy, hp]
    · simp only [hy, hp, if_false, List.length_append, List.length_singleton, beq_iff_eq]
      omega

/-- The descent from the root of an auxiliary tree, with fuel at least the size of the tree:
it stops at a node `y` of the tree whose value is ready and is paired with `y` in the forest;
the state is `pushPath` of the start state at `y`; and splaying `y` afterwards gives the same
state as splaying `y` at the start. -/
theorem descend_root {P : LctPayload α σ τ} (hL : P.Laws) {rs : σ → Bool} {rv : α → Bool}
    (hR : ReadyLaw P rs rv) {s : SplayState α σ τ} {t : AuxTree} (ht : TreeInv P s t)
    (hne : t ≠ .leaf) (hrs : rs (s.nodes t.rootId).sum = true) {F : ℕ}
    (hF : t.countNodes ≤ F) {D' : SplayState α σ τ} {y : ℕ}
    (hd : descend P rs rv s F t.rootId = (D', y)) :
    y ∈ t.toList ∧ (y, (D'.nodes y).val) ∈ evalPairs P s t false P.idTag ∧
      rv (D'.nodes y).val = true ∧ D' = pushPath P s F y ∧
      splay P D' F y = splay P s F y ∧ pushPath P D' F y = D' ∧
      Gen.descendSteps P rs rv s F t.rootId ≤ splayDepth s F y + 1 := by
  have hsp := descend_spec hL hR t s 0 F hne ht.nodup ht.sub hrs hF
  rw [hd] at hsp
  dsimp only at hsp
  obtain ⟨rpath, ⟨hh, hlast, hst, hch, hmem, hlen, hcl, -, hpair, hrdy⟩, hsteps⟩ := hsp
  obtain ⟨rest, rfl⟩ : ∃ rest, rpath = y :: rest := by
    cases rpath with
    | nil => simp at hh
    | cons a rest => simp at hh; exact ⟨rest, by rw [hh]⟩
  have hy : y ∈ t.toList := hmem y List.mem_cons_self
  have hnz : ∀ z ∈ y :: rest, z ≠ 0 := fun z hz =>
    subtreeInv_ne_zero ht.sub (hmem z hz)
  have hroot : (s.nodes ((y :: rest).getLast (List.cons_ne_nil _ _))).par = 0 := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
    simp only [Option.some.injEq] at hlast
    rw [hlast]
    cases t with
    | leaf => exact absurd rfl hne
    | node id a b => exact ht.sub.2.2.2.1
  have hchain := chainList_of_chain s rest y F hch hnz hroot hlen
  have hpp : pushPath P s F y = D' := by
    rw [pushPath_eq_pushSeq, hchain, hst]
  have hpp' : pushPath P D' F y = D' := by
    rw [pushPath_eq_pushSeq, chainList_congr (s := s), hchain]
    · exact pushSeq_clean hL _ fun z hz => hcl z (List.mem_reverse.mp hz)
    · intro z; rw [hst, par_pushSeq]
  have hy0 : y ≠ 0 := hnz y List.mem_cons_self
  refine ⟨hy, hpair, hrdy, hpp.symm, ?_, hpp', ?_⟩
  · unfold splay
    rw [if_neg hy0, if_neg hy0, hpp', hpp]
  · have := chainList_length_le s F y
    rw [hchain, List.length_reverse] at this
    omega

/-- Exposing `y` after the descent gives the same state as exposing `y` at the start. -/
theorem lctExpose_of_splay_eq {P : LctPayload α σ τ} (st : LctState α σ τ) {D' : SplayState α σ τ}
    {y : ℕ} (h : splay P D' (2 * st.n + 1) y = splay P st.splay (2 * st.n + 1) y) :
    lctExpose P { st with splay := D' } y = lctExpose P st y := by
  unfold lctExpose lctExposeCost
  simp only
  rw [h]

end MinCostFlow.LinkCut.PathTree
