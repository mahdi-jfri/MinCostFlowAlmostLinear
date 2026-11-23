module

public import MinCostFlow.SparseCore.Program.BundleStepEmitProcs

/-!
# Pure single-run split model for Phase 3 (`BundleStepEmitModel`)

Defines `oneRunUpdate`, `applyOneSplitRun`, `runTailEdges`, `runHeadEdges`, and `foldOneSplitRuns`,
and proves their exact correspondence with `MGraph.applyUpdate`, `UpdateAt`, `bundleRunUpdates`,
and `runsFoldStep`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The single `Update.split` emitted for moving run `xs` from bundle `b` to fresh bundle `b'`. -/
def oneRunUpdate (b b' : ℕ) (xs : List End) : Update :=
  .split b b'
    ((xs.filter Prod.snd).map Prod.fst).toFinset
    ((xs.filter fun x => !x.2).map Prod.fst).toFinset

/-- Applies one maximal same-vertex split run `(vCur, xs)` moving `xs` from `b` to fresh `b'`. -/
def applyOneSplitRun (B : BundleState) (b b' vCur : ℕ) (xs : List End) : Update × BundleState :=
  let u := oneRunUpdate b b' xs
  let G' := B.graph.applyUpdate u
  (u, { vertices := G'.V, edges := G'.E, parent := Function.update B.parent b' vCur, bundleOf := G'.src })

/-- List of tail edges in `xs` (matching the order emitted into `Lt`). -/
def runTailEdges (xs : List End) : List ℕ :=
  (xs.filter Prod.snd).map Prod.fst

/-- List of head edges in `xs` (matching the order emitted into `Lh`). -/
def runHeadEdges (xs : List End) : List ℕ :=
  (xs.filter fun x => !x.2).map Prod.fst

/-- Sequential `applyOneSplitRun` fold over `rest : List (ℕ × List End)`. -/
def foldOneSplitRuns (b : ℕ) :
    List (ℕ × List End) → (List Update × BundleState × ℕ) → (List Update × BundleState × ℕ)
  | [], acc => acc
  | (vCur, xs) :: rest, (ops, B, nB) =>
    let res := applyOneSplitRun B b nB vCur xs
    foldOneSplitRuns b rest (ops ++ [res.1], res.2, nB + 1)

/-- Tail edges extracted from a list of end keys `L` (even keys `2 * e`). -/
def keyTailEdges (L : List ℕ) : List ℕ :=
  (L.filter fun k => k % 2 == 0).map (· / 2)

/-- Head edges extracted from a list of end keys `L` (odd keys `2 * e + 1`). -/
def keyHeadEdges (L : List ℕ) : List ℕ :=
  (L.filter fun k => k % 2 != 0).map (· / 2)

/-- Sequential concatenation of compactly encoded updates (`SmallUpdateAt`) starting at `a`. -/
def SmallBatchBodyAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) : List Update → ℕ → Prop
  | [], totalWords => totalWords = 0
  | u :: us, totalWords =>
    ∃ len, len ≤ totalWords ∧ SmallUpdateAt mem a G u len ∧
      SmallBatchBodyAt mem (a + len) (G.applyUpdate u) us (totalWords - len)

end

public section

lemma runTailEdges_add_headEdges_length (xs : List End) :
    (runTailEdges xs).length + (runHeadEdges xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨e, side⟩
    cases side <;> simp only [runTailEdges, runHeadEdges, List.filter_cons, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.length_cons] at ih ⊢ <;> omega

lemma runTailEdges_nodup {xs : List End} (hnd : xs.Nodup) : (runTailEdges xs).Nodup := by
  unfold runTailEdges
  rw [List.nodup_map_iff_inj_on (hnd.filter _)]
  intro ⟨e₁, s₁⟩ h₁ ⟨e₂, s₂⟩ h₂ heq
  have hs₁ : s₁ = true := (List.mem_filter.mp h₁).2
  have hs₂ : s₂ = true := (List.mem_filter.mp h₂).2
  subst hs₁; subst hs₂; exact Prod.ext heq rfl

lemma runHeadEdges_nodup {xs : List End} (hnd : xs.Nodup) : (runHeadEdges xs).Nodup := by
  unfold runHeadEdges
  rw [List.nodup_map_iff_inj_on (hnd.filter _)]
  intro ⟨e₁, s₁⟩ h₁ ⟨e₂, s₂⟩ h₂ heq
  have hs₁ : s₁ = false := by simpa using (List.mem_filter.mp h₁).2
  have hs₂ : s₂ = false := by simpa using (List.mem_filter.mp h₂).2
  subst hs₁; subst hs₂; exact Prod.ext heq rfl

private lemma mgraph_of_src_eq (G : MGraph) :
    ({ V := G.V, E := G.E, tail := fun e => G.src (e, true), head := fun e => G.src (e, false) } : MGraph) = G := by
  cases G; rfl

lemma oneRunUpdate_graph_apply (B : BundleState) {nB b vCur : ℕ} {xs : List End}
    (hV : B.vertices = Finset.range nB) (_hb : b < nB)
    (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b) :
    let res := applyOneSplitRun B b nB vCur xs
    res.2.vertices = Finset.range (nB + 1) ∧
    res.2.edges = B.edges ∧
    (∀ x ∈ edgeEnds B.edges, res.2.bundleOf x = if x ∈ xs then nB else B.bundleOf x) ∧
    res.2.graph = B.graph.applyUpdate (oneRunUpdate b nB xs) := by
  intro res
  have hV' : (B.graph.applyUpdate (oneRunUpdate b nB xs)).V = Finset.range (nB + 1) := by
    simp only [oneRunUpdate, MGraph.applyUpdate, BundleState.graph, hV, Finset.range_add_one]
  have hE' : (B.graph.applyUpdate (oneRunUpdate b nB xs)).E = B.edges := rfl
  have hsrc' : ∀ x ∈ edgeEnds B.edges,
      (B.graph.applyUpdate (oneRunUpdate b nB xs)).src x = if x ∈ xs then nB else B.bundleOf x := by
    intro ⟨e, side⟩ _
    cases side
    · simp only [oneRunUpdate, MGraph.applyUpdate, MGraph.src, BundleState.graph, Bool.false_eq_true,
        ↓reduceIte, List.mem_toFinset, List.mem_map, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true]
      by_cases hmem : (e, false) ∈ xs
      · have hbo := ((BundleState.mem_ends B b (e, false)).mp (hxs_sub _ hmem)).2
        simp [hbo, hmem]
      · simp [hmem]
    · simp only [oneRunUpdate, MGraph.applyUpdate, MGraph.src, BundleState.graph, ↓reduceIte,
        List.mem_toFinset, List.mem_map, List.mem_filter]
      by_cases hmem : (e, true) ∈ xs
      · have hbo := ((BundleState.mem_ends B b (e, true)).mp (hxs_sub _ hmem)).2
        simp [hbo, hmem]
      · simp [hmem]
  exact ⟨hV', hE', hsrc', mgraph_of_src_eq _⟩

lemma applyOneSplitRun_ends {B : BundleState} {nB b vCur : ℕ} {xs : List End}
    (hV : B.vertices = Finset.range nB) (hb : b < nB)
    (hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b) :
    let B' := (applyOneSplitRun B b nB vCur xs).2
    B'.ends b = B.ends b \ xs.toFinset ∧
    B'.ends nB = xs.toFinset ∧
    (∀ c, c ≠ b → c ≠ nB → B'.ends c = B.ends c) := by
  intro B'
  obtain ⟨_, hE', hsrc', _⟩ := oneRunUpdate_graph_apply B hV hb hxs_sub
  refine ⟨?_, ?_, ?_⟩
  · ext x; simp only [BundleState.mem_ends, Finset.mem_sdiff, List.mem_toFinset]
    rw [hE']
    constructor
    · rintro ⟨hxE, hbo⟩
      rw [hsrc' x ((mem_edgeEnds _ _).mpr hxE)] at hbo
      by_cases hx : x ∈ xs
      · simp only [hx, ↓reduceIte] at hbo; omega
      · simp only [hx, ↓reduceIte] at hbo; exact ⟨⟨hxE, hbo⟩, hx⟩
    · rintro ⟨⟨hxE, hbo⟩, hnx⟩
      refine ⟨hxE, ?_⟩
      rw [hsrc' x ((mem_edgeEnds _ _).mpr hxE), ite_eq_right hnx]; exact hbo
  · ext x; simp only [BundleState.mem_ends, List.mem_toFinset]
    rw [hE']
    constructor
    · rintro ⟨hxE, hbo⟩
      rw [hsrc' x ((mem_edgeEnds _ _).mpr hxE)] at hbo
      by_cases hx : x ∈ xs
      · exact hx
      · simp only [hx, ↓reduceIte] at hbo
        have hlt := hbo_lt x ((mem_edgeEnds _ _).mpr hxE); omega
    · intro hx
      have hxB := (BundleState.mem_ends B b x).mp (hxs_sub x hx)
      refine ⟨hxB.1, ?_⟩
      rw [hsrc' x ((mem_edgeEnds _ _).mpr hxB.1), ite_eq_left hx]
  · intro c hcb hcn; ext x; simp only [BundleState.mem_ends]
    rw [hE']
    constructor
    · rintro ⟨hxE, hbo⟩
      rw [hsrc' x ((mem_edgeEnds _ _).mpr hxE)] at hbo
      by_cases hx : x ∈ xs
      · simp only [hx, ↓reduceIte] at hbo; exact absurd hbo.symm hcn
      · simp only [hx, ↓reduceIte] at hbo; exact ⟨hxE, hbo⟩
    · rintro ⟨hxE, hbo⟩
      have hnx : x ∉ xs := fun hx => hcb (hbo.symm.trans ((BundleState.mem_ends B b x).mp (hxs_sub x hx)).2)
      refine ⟨hxE, ?_⟩
      rw [hsrc' x ((mem_edgeEnds _ _).mpr hxE), ite_eq_right hnx]; exact hbo

/-- Tag-`2` encoding of `oneRunUpdate b b' xs` matches `UpdateAt`. -/
lemma oneRunUpdate_updateAt {mem : ℕ → ℕ} {a b b' : ℕ} {B : BundleState} {xs : List End}
    (hnd : xs.Nodup) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hlist : ListAt mem a ([2, b, b', (runTailEdges xs).length, (runHeadEdges xs).length] ++
      runTailEdges xs ++ runHeadEdges xs)) :
    UpdateAt mem a B.graph (oneRunUpdate b b' xs) (5 + xs.length) := by
  refine Or.inl ⟨runTailEdges xs, runHeadEdges xs, runTailEdges_nodup hnd, runHeadEdges_nodup hnd,
    ?_, ?_, by rw [Nat.add_assoc, runTailEdges_add_headEdges_length], hlist⟩
  · intro e; simp only [runTailEdges, List.mem_map, List.mem_filter, BundleState.graph,
      List.mem_toFinset]
    constructor
    · rintro ⟨⟨e', s'⟩, ⟨hmem, hs⟩, rfl⟩
      dsimp only at hs; subst hs
      have hB := (BundleState.mem_ends B b (e', true)).mp (hxs_sub _ hmem)
      exact ⟨hB.1, hB.2, ⟨(e', true), ⟨hmem, rfl⟩, rfl⟩⟩
    · rintro ⟨_, _, h⟩; exact h
  · intro e; simp only [runHeadEdges, List.mem_map, List.mem_filter, BundleState.graph,
      List.mem_toFinset]
    constructor
    · rintro ⟨⟨e', s'⟩, ⟨hmem, hs⟩, rfl⟩
      have hsf : s' = false := by simpa using hs
      subst hsf
      have hB := (BundleState.mem_ends B b (e', false)).mp (hxs_sub _ hmem)
      exact ⟨hB.1, hB.2, ⟨(e', false), ⟨hmem, rfl⟩, rfl⟩⟩
    · rintro ⟨_, _, h⟩; exact h

private lemma zipIdx_map_oneRun (b : ℕ) :
    ∀ (l : List (ℕ × List End)) (k : ℕ),
      (l.zipIdx k).map (fun x => oneRunUpdate b x.2 x.1.2) =
        ((l.map Prod.snd).zipIdx k).map (fun x => oneRunUpdate b x.2 x.1)
  | [], _ => rfl
  | _ :: tl, k => by simp [List.zipIdx_cons, zipIdx_map_oneRun b tl (k + 1)]

/-- Folding `applyOneSplitRun` over `vruns.drop 1` reproduces `runsFoldStep` exactly. -/
lemma runsFoldStep_eq_fold_oneRun {ops : List Update} {B : BundleState} {nB b v0 : ℕ}
    {xs0 : List End} {rest : List (ℕ × List End)}
    (hV : B.vertices = Finset.range nB) (hb : b < nB) :
    let B0 : BundleState := { B with parent := Function.update B.parent b v0 }
    let res := foldOneSplitRuns b rest (ops, B0, nB)
    (res.1, res.2.1) = runsFoldStep (ops, B) (b, (v0, xs0) :: rest) ∧
    res.2.2 = nB + rest.length := by
  intro B0 res
  have hsup : B.vertices.sup id + 1 = nB := by
    rw [hV]
    have hle : (Finset.range nB).sup id ≤ nB - 1 := Finset.sup_le fun x hx => by
      have := Finset.mem_range.mp hx; change x ≤ nB - 1; omega
    have hge : nB - 1 ≤ (Finset.range nB).sup id :=
      Finset.le_sup (f := id) (Finset.mem_range.mpr (by omega))
    omega
  have hfold_gen : ∀ (rs : List (ℕ × List End)) (ops₁ : List Update) (B₁ : BundleState) (k : ℕ),
      let r := foldOneSplitRuns b rs (ops₁, B₁, k)
      let newOps := (rs.zipIdx k).map fun x => oneRunUpdate b x.2 x.1.2
      r.1 = ops₁ ++ newOps ∧
      r.2.1.graph = B₁.graph.applyBatch newOps ∧
      r.2.1.parent = (fun w =>
        if h : k ≤ w ∧ w < k + rs.length then (rs[w - k]'(by omega)).1 else B₁.parent w) ∧
      r.2.2 = k + rs.length := by
    intro rs
    induction rs with
    | nil =>
      intro ops₁ B₁ k
      refine ⟨by simp [foldOneSplitRuns], by simp [foldOneSplitRuns, MGraph.applyBatch], ?_, by simp [foldOneSplitRuns]⟩
      funext w; simp [foldOneSplitRuns]
    | cons hd tl ih =>
      intro ops₁ B₁ k
      rcases hd with ⟨vCur, xs⟩
      let B₂ := (applyOneSplitRun B₁ b k vCur xs).2
      have hB2_graph : B₂.graph = B₁.graph.applyUpdate (oneRunUpdate b k xs) := mgraph_of_src_eq _
      have hsub := ih (ops₁ ++ [oneRunUpdate b k xs]) B₂ (k + 1)
      have hfst : (applyOneSplitRun B₁ b k vCur xs).1 = oneRunUpdate b k xs := rfl
      simp only [foldOneSplitRuns, hfst]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hsub.1]; simp [List.zipIdx_cons, List.append_assoc]
      · rw [hsub.2.1, hB2_graph]; simp [List.zipIdx_cons, MGraph.applyBatch]
      · rw [hsub.2.2.1]
        funext w
        by_cases hwk : w = k
        · subst w
          simp [B₂, applyOneSplitRun]
        · by_cases hrange : k + 1 ≤ w ∧ w < k + 1 + tl.length
          · have h2 : k ≤ w ∧ w < k + ((vCur, xs) :: tl).length := by simp only [List.length_cons]; omega
            have hsub_idx : w - k = (w - (k + 1)) + 1 := by omega
            rw [dite_eq_left hrange, dite_eq_left h2]
            simp only [hsub_idx, List.getElem_cons_succ]
          · have h2 : ¬ (k ≤ w ∧ w < k + ((vCur, xs) :: tl).length) := by simp only [List.length_cons]; omega
            rw [dite_eq_right hrange, dite_eq_right h2]
            simp [B₂, applyOneSplitRun, Function.update_of_ne hwk]
      · rw [hsub.2.2.2]; simp only [List.length_cons]; omega
  have hg := hfold_gen rest ops B0 nB
  have hB0_graph : B0.graph = B.graph := rfl
  refine ⟨?_, hg.2.2.2⟩
  have hops_eq : (rest.zipIdx nB).map (fun x => oneRunUpdate b x.2 x.1.2) =
      bundleRunUpdates b nB (((v0, xs0) :: rest).map Prod.snd) := by
    simp only [bundleRunUpdates, List.map_cons, List.drop_succ_cons, List.drop_zero]
    rw [zipIdx_map_oneRun b rest nB]
    rfl
  refine Prod.ext ?_ ?_
  · dsimp only [runsFoldStep, bundleSplitFoldStep]
    rw [hg.1, hsup, hops_eq]
  · have hG_eq : res.2.1.graph = B.graph.applyBatch (bundleRunUpdates b nB (((v0, xs0) :: rest).map Prod.snd)) := by
      rw [hg.2.1, hB0_graph, hops_eq]
    cases hresB : res.2.1 with
    | mk V E par bo =>
      have hV_eq : V = (B.graph.applyBatch (bundleRunUpdates b nB (((v0, xs0) :: rest).map Prod.snd))).V := by
        have := congrArg MGraph.V hG_eq; simpa [hresB, BundleState.graph] using this
      have hE_eq : E = (B.graph.applyBatch (bundleRunUpdates b nB (((v0, xs0) :: rest).map Prod.snd))).E := by
        have := congrArg MGraph.E hG_eq; simpa [hresB, BundleState.graph] using this
      have hbo_eq : bo = (B.graph.applyBatch (bundleRunUpdates b nB (((v0, xs0) :: rest).map Prod.snd))).src := by
        funext ⟨e, side⟩
        cases side
        · have := congrFun (congrArg MGraph.head hG_eq) e; simpa [hresB, BundleState.graph, MGraph.src] using this
        · have := congrFun (congrArg MGraph.tail hG_eq) e; simpa [hresB, BundleState.graph, MGraph.src] using this
      have hpar_eq : par = runParent b nB ((v0, xs0) :: rest) B.parent := by
        have hp := hg.2.2.1; rw [hresB] at hp; dsimp only at hp; rw [hp]
        funext w; unfold runParent
        by_cases hwb : w = b
        · subst w
          have hnot : ¬ (nB ≤ b ∧ b < nB + rest.length) := by omega
          simp [B0, hnot]
        · simp only [hwb, ↓reduceIte]
          by_cases hge : nB ≤ w
          · simp only [hge, ↓reduceIte]
            by_cases hlt : w < nB + rest.length
            · simp [hlt, List.getElem?_eq_getElem (show w - nB < rest.length by omega)]
            · have hge_r : rest.length ≤ w - nB := by omega
              simp [hlt, List.getElem?_eq_none hge_r, B0, Function.update_of_ne hwb]
          · simp [hge, B0, Function.update_of_ne hwb]
      dsimp only [runsFoldStep, bundleSplitFoldStep]
      rw [hsup, hV_eq, hE_eq, hbo_eq, hpar_eq]

/-! ## Compact split encoding (tag `2` vs tag `3`) and `SmallBatchBodyAt` / `SmallBatchAt` -/

lemma keyTailEdges_add_headEdges_length (L : List ℕ) :
    (keyTailEdges L).length + (keyHeadEdges L).length = L.length := by
  induction L with
  | nil => rfl
  | cons k ks ih =>
    by_cases h : k % 2 = 0
    · simp [keyTailEdges, keyHeadEdges, h] at ih ⊢; omega
    · have h1 : k % 2 = 1 := by omega
      simp [keyTailEdges, keyHeadEdges, h1] at ih ⊢; omega

lemma keyTailEdges_nodup {L : List ℕ} (hnd : L.Nodup) : (keyTailEdges L).Nodup := by
  unfold keyTailEdges
  rw [List.nodup_map_iff_inj_on (hnd.filter _)]
  intro k₁ hk₁ k₂ hk₂ heq
  have h1 : k₁ % 2 = 0 := by simpa using (List.mem_filter.mp hk₁).2
  have h2 : k₂ % 2 = 0 := by simpa using (List.mem_filter.mp hk₂).2
  omega

lemma keyHeadEdges_nodup {L : List ℕ} (hnd : L.Nodup) : (keyHeadEdges L).Nodup := by
  unfold keyHeadEdges
  rw [List.nodup_map_iff_inj_on (hnd.filter _)]
  intro k₁ hk₁ k₂ hk₂ heq
  have h1 : k₁ % 2 = 1 := by have := (List.mem_filter.mp hk₁).2; simp at this; omega
  have h2 : k₂ % 2 = 1 := by have := (List.mem_filter.mp hk₂).2; simp at this; omega
  omega

lemma bundleState_deg_eq_ends_card (B : BundleState) (v : ℕ) :
    B.graph.deg v = (B.ends v).card := by
  unfold MGraph.deg BundleState.graph
  set S_t := (B.edges.filter fun e => B.bundleOf (e, true) = v).image fun e => (e, true)
  set S_h := (B.edges.filter fun e => B.bundleOf (e, false) = v).image fun e => (e, false)
  have hdisj : Disjoint S_t S_h := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨e₁, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨e₂, _, h⟩ := Finset.mem_image.mp hx2
    cases h
  have hunion : S_t ∪ S_h = B.ends v := by
    ext ⟨e, side⟩
    cases side <;> simp [S_t, S_h, BundleState.mem_ends]
  rw [← hunion, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
    Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]

lemma oneRunUpdate_enc_eq {B : BundleState} {nB b : ℕ} {xs : List End}
    (hV : B.vertices = Finset.range nB) (hb : b < nB)
    (hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hxs_nd : xs.Nodup) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b) :
    B.graph.updateEnc (oneRunUpdate b nB xs) =
      min (B.ends b \ xs.toFinset).card xs.length + 1 := by
  unfold MGraph.updateEnc oneRunUpdate
  dsimp only
  obtain ⟨_, _, _, hG'⟩ := oneRunUpdate_graph_apply B hV hb hxs_sub (vCur := 0)
  obtain ⟨hb_ends, hnB_ends, _⟩ := applyOneSplitRun_ends hV hb hbo_lt hxs_sub (vCur := 0)
  have hG'_eq : B.graph.applyUpdate (oneRunUpdate b nB xs) = (applyOneSplitRun B b nB 0 xs).2.graph :=
    hG'.symm
  change min ((B.graph.applyUpdate (oneRunUpdate b nB xs)).deg b)
      ((B.graph.applyUpdate (oneRunUpdate b nB xs)).deg nB) + 1 = _
  rw [hG'_eq, bundleState_deg_eq_ends_card, bundleState_deg_eq_ends_card, hb_ends, hnB_ends,
    List.toFinset_card_of_nodup hxs_nd]

lemma keptKeys_length_eq_sdiff_card {B : BundleState} {b : ℕ} {xs : List End} {L_kept : List ℕ}
    (hL_nd : L_kept.Nodup)
    (hL_mem : ∀ k, k ∈ L_kept ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs) :
    L_kept.length = (B.ends b \ xs.toFinset).card := by
  have himg : (B.ends b \ xs.toFinset).image endKey = L_kept.toFinset := by
    ext k; simp only [Finset.mem_image, List.mem_toFinset, Finset.mem_sdiff, hL_mem]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [bundle_endOfKey_endKey]
    · intro hk; exact ⟨endOfKey k, hk, bundle_endKey_endOfKey k⟩
  rw [← List.toFinset_card_of_nodup hL_nd, ← himg, Finset.card_image_of_injective _ endKey_injective]

/-- Tag-`3` encoding of `oneRunUpdate b b' xs` from the remaining DLL `L_kept` matches `UpdateAt`. -/
lemma oneRunUpdate_updateAt_kept {mem : ℕ → ℕ} {a b b' : ℕ} {B : BundleState} {xs : List End}
    {L_kept : List ℕ} (hL_nd : L_kept.Nodup)
    (hL_mem : ∀ k, k ∈ L_kept ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs)
    (hlist : ListAt mem a ([3, b, b', (keyTailEdges L_kept).length, (keyHeadEdges L_kept).length] ++
      keyTailEdges L_kept ++ keyHeadEdges L_kept)) :
    UpdateAt mem a B.graph (oneRunUpdate b b' xs) (5 + L_kept.length) := by
  refine Or.inr ⟨keyTailEdges L_kept, keyHeadEdges L_kept, keyTailEdges_nodup hL_nd,
    keyHeadEdges_nodup hL_nd, ?_, ?_, by rw [Nat.add_assoc, keyTailEdges_add_headEdges_length], hlist⟩
  · intro e
    simp only [keyTailEdges, List.mem_map, List.mem_filter, beq_iff_eq, BundleState.graph,
      List.mem_toFinset]
    constructor
    · rintro ⟨k, ⟨hkL, hmod⟩, rfl⟩
      have hend : endOfKey k = (k / 2, true) := by simp [endOfKey, hmod]
      have hB := (hL_mem k).mp hkL
      rw [hend, BundleState.mem_ends] at hB
      refine ⟨hB.1.1, hB.1.2, ?_⟩
      rintro ⟨⟨e', s'⟩, ⟨hmem, hs'⟩, heq⟩
      dsimp only at hs' heq; subst hs'; subst heq; exact hB.2 hmem
    · rintro ⟨heE, hbo, hnot⟩
      refine ⟨2 * e, ⟨(hL_mem (2 * e)).mpr ?_, by omega⟩, by omega⟩
      have hend : endOfKey (2 * e) = (e, true) := by unfold endOfKey; simp
      rw [hend, BundleState.mem_ends]
      exact ⟨⟨heE, hbo⟩, fun hmem => hnot ⟨(e, true), ⟨hmem, rfl⟩, rfl⟩⟩
  · intro e
    simp only [keyHeadEdges, List.mem_map, List.mem_filter, bne_iff_ne, BundleState.graph,
      List.mem_toFinset]
    constructor
    · rintro ⟨k, ⟨hkL, hmod⟩, rfl⟩
      have hend : endOfKey k = (k / 2, false) := by simp [endOfKey, hmod]
      have hB := (hL_mem k).mp hkL
      rw [hend, BundleState.mem_ends] at hB
      refine ⟨hB.1.1, hB.1.2, ?_⟩
      rintro ⟨⟨e', s'⟩, ⟨hmem, hs'⟩, heq⟩
      have hsf : s' = false := by simpa using hs'
      subst hsf; dsimp only at heq; subst heq; exact hB.2 hmem
    · rintro ⟨heE, hbo, hnot⟩
      refine ⟨2 * e + 1, ⟨(hL_mem (2 * e + 1)).mpr ?_, by omega⟩, by omega⟩
      have hend : endOfKey (2 * e + 1) = (e, false) := by unfold endOfKey; simp; omega
      rw [hend, BundleState.mem_ends]
      exact ⟨⟨heE, hbo⟩, fun hmem => hnot ⟨(e, false), ⟨hmem, rfl⟩, rfl⟩⟩

lemma oneRunUpdate_smallUpdateAt_moved {mem : ℕ → ℕ} {a b nB : ℕ} {B : BundleState}
    {xs : List End} {L_kept : List ℕ}
    (hV : B.vertices = Finset.range nB) (hb : b < nB)
    (hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hxs_nd : xs.Nodup) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hL_nd : L_kept.Nodup)
    (hL_mem : ∀ k, k ∈ L_kept ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs)
    (hle : xs.length ≤ L_kept.length)
    (hlist : ListAt mem a ([2, b, nB, (runTailEdges xs).length, (runHeadEdges xs).length] ++
      runTailEdges xs ++ runHeadEdges xs)) :
    SmallUpdateAt mem a B.graph (oneRunUpdate b nB xs) (5 + min L_kept.length xs.length) := by
  have hmin : min L_kept.length xs.length = xs.length := Nat.min_eq_right hle
  rw [hmin]
  refine ⟨oneRunUpdate_updateAt hxs_nd hxs_sub hlist, ?_⟩
  rw [oneRunUpdate_enc_eq hV hb hbo_lt hxs_nd hxs_sub, ← keptKeys_length_eq_sdiff_card hL_nd hL_mem, hmin]
  omega

lemma oneRunUpdate_smallUpdateAt_kept {mem : ℕ → ℕ} {a b nB : ℕ} {B : BundleState}
    {xs : List End} {L_kept : List ℕ}
    (hV : B.vertices = Finset.range nB) (hb : b < nB)
    (hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hxs_nd : xs.Nodup) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hL_nd : L_kept.Nodup)
    (hL_mem : ∀ k, k ∈ L_kept ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs)
    (hlt : L_kept.length < xs.length)
    (hlist : ListAt mem a ([3, b, nB, (keyTailEdges L_kept).length, (keyHeadEdges L_kept).length] ++
      keyTailEdges L_kept ++ keyHeadEdges L_kept)) :
    SmallUpdateAt mem a B.graph (oneRunUpdate b nB xs) (5 + min L_kept.length xs.length) := by
  have hmin : min L_kept.length xs.length = L_kept.length := Nat.min_eq_left (le_of_lt hlt)
  rw [hmin]
  refine ⟨oneRunUpdate_updateAt_kept hL_nd hL_mem hlist, ?_⟩
  rw [oneRunUpdate_enc_eq hV hb hbo_lt hxs_nd hxs_sub, ← keptKeys_length_eq_sdiff_card hL_nd hL_mem, hmin]
  omega

lemma updateEnc_pos (G : MGraph) (u : Update) : 1 ≤ G.updateEnc u := by
  cases u <;> simp [MGraph.updateEnc]

lemma SmallBatchBodyAt.to_batchBodyAt {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {w : ℕ}
    (h : SmallBatchBodyAt mem a G U w) : BatchBodyAt mem a G U w := by
  induction U generalizing a G w with
  | nil => exact h
  | cons u us ih =>
    rcases h with ⟨len, hlen, hsu, hrest⟩
    exact ⟨len, hlen, hsu.1, ih hrest⟩

lemma SmallBatchBodyAt.words_le {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {w : ℕ}
    (h : SmallBatchBodyAt mem a G U w) : w ≤ 5 * G.batchEnc U := by
  induction U generalizing a G w with
  | nil => simp only [SmallBatchBodyAt] at h; subst h; simp [MGraph.batchEnc]
  | cons u us ih =>
    rcases h with ⟨len, hlen, hsu, hrest⟩
    have h1 := ih hrest
    have h2 := updateEnc_pos G u
    have h3 := hsu.2
    simp only [MGraph.batchEnc]
    omega

lemma smallBatchBodyAt_append {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U₁ U₂ : List Update} {w₁ w₂ : ℕ}
    (h1 : SmallBatchBodyAt mem a G U₁ w₁)
    (h2 : SmallBatchBodyAt mem (a + w₁) (G.applyBatch U₁) U₂ w₂) :
    SmallBatchBodyAt mem a G (U₁ ++ U₂) (w₁ + w₂) := by
  induction U₁ generalizing a G w₁ with
  | nil =>
    simp only [SmallBatchBodyAt] at h1; subst h1
    simpa [MGraph.applyBatch] using h2
  | cons u us ih =>
    rcases h1 with ⟨len, hlen, hsu, hrest⟩
    refine ⟨len, by omega, hsu, ?_⟩
    have hsub : w₁ + w₂ - len = (w₁ - len) + w₂ := by omega
    rw [hsub]
    refine ih hrest ?_
    have haddr : a + len + (w₁ - len) = a + w₁ := by omega
    rw [haddr]; exact h2

lemma bundle_smallBatchBodyAt_snoc {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {u : Update} {w₁ len : ℕ}
    (h1 : SmallBatchBodyAt mem a G U w₁)
    (hu : SmallUpdateAt mem (a + w₁) (G.applyBatch U) u len) :
    SmallBatchBodyAt mem a G (U ++ [u]) (w₁ + len) :=
  smallBatchBodyAt_append h1 ⟨len, le_refl _, hu, by simp [SmallBatchBodyAt]⟩

lemma smallBatchBodyAt_agree {m1 m2 : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {tot : ℕ}
    (h : SmallBatchBodyAt m1 a G U tot) (hEq : ∀ x, a ≤ x → x < a + tot → m2 x = m1 x) :
    SmallBatchBodyAt m2 a G U tot := by
  induction U generalizing a G tot with
  | nil => exact h
  | cons u us ih =>
    rcases h with ⟨len, hlen, hsu, hrest⟩
    refine ⟨len, hlen, ⟨?_, hsu.2⟩, ih hrest fun x hx1 hx2 => hEq x (by omega) (by omega)⟩
    have hu := hsu.1
    cases u with
    | insert e x y =>
      rcases hu with ⟨rfl, hL⟩
      exact ⟨rfl, fun i hi => (hEq (a + i) (by omega) (by simp at hi; omega)).trans (hL i hi)⟩
    | delete e =>
      rcases hu with ⟨rfl, hL⟩
      exact ⟨rfl, fun i hi => (hEq (a + i) (by omega) (by simp at hi; omega)).trans (hL i hi)⟩
    | split v v' St Sh =>
      rcases hu with ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, hL⟩ | ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, hL⟩
      · refine Or.inl ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        exact (hEq (a + i) (by omega) (by omega)).trans (hL i (by simp; omega))
      · refine Or.inr ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        exact (hEq (a + i) (by omega) (by omega)).trans (hL i (by simp; omega))

lemma batchBodyAt_deletes_small {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {dels : List ℕ} {w : ℕ}
    (h : BatchBodyAt mem a G (dels.map Update.delete) w) :
    SmallBatchBodyAt mem a G (dels.map Update.delete) w := by
  induction dels generalizing a G w with
  | nil => exact h
  | cons e es ih =>
    rcases h with ⟨len, hlen, hu, hrest⟩
    rcases hu with ⟨rfl, hL⟩
    exact ⟨2, hlen, ⟨⟨rfl, hL⟩, by simp [MGraph.updateEnc]⟩, ih hrest⟩

lemma SmallBatchBodyAt.to_smallBatchAt {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {totalWords : ℕ} (h1 : 1 ≤ totalWords) (hlen : mem a = U.length)
    (hbody : SmallBatchBodyAt mem (a + 1) G U (totalWords - 1)) :
    SmallBatchAt mem a G U totalWords := by
  have hw := hbody.words_le
  exact ⟨⟨h1, hlen, hbody.to_batchBodyAt⟩, by omega⟩

/-- For any nonempty batch in `SmallBatchAt` layout, `totalWords ≤ 6 * G.batchEnc U`. -/
lemma smallBatchAt_words_le_of_nonempty {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {totalWords : ℕ} (h : SmallBatchAt mem a G U totalWords) (hne : U ≠ []) :
    totalWords ≤ 6 * G.batchEnc U := by
  cases U with
  | nil => exact absurd rfl hne
  | cons u us =>
    have hpos : 1 ≤ G.batchEnc (u :: us) := by
      simp only [MGraph.batchEnc]
      have := updateEnc_pos G u; omega
    have := h.2
    omega

/-- For any batch in `SmallBatchAt` layout and any charge `X ≥ 1` with `G.batchEnc U ≤ X`,
`totalWords ≤ 6 * X` (so `bucketUpdateCost_le_of_words` applies with `c_W = 6`). -/
lemma smallBatchAt_words_le_charge {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {totalWords X : ℕ} (h : SmallBatchAt mem a G U totalWords)
    (hEnc : G.batchEnc U ≤ X) (hX : 1 ≤ X) :
    totalWords ≤ 6 * X := by
  have := h.2; omega

end

end MinCostFlow.SparseCore.Program
