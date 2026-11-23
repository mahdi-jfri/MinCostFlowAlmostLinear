module

public import MinCostFlow.SparseCore.BundleRunsStep
public import MinCostFlow.Bundle.SplitFibers
public import MinCostFlow.SparseCore.GraphHelpers
public import MinCostFlow.DynSpanner.StepInv

/-!
# The fold of the canonical bundle step

`bundleRunsStep` processes the bundles one at a time with `runsFoldStep`. This file follows the
fold. One step splits a bundle `b` into its runs: `b` keeps the first run, and the fresh names
`next, next + 1, …` take the others, with the run's core vertex as parent (`runsFoldStep_spec`,
from `bundleSplitFoldStep_fibers`). A step changes no other bundle, and the fresh names lie above
every name used so far, so later steps keep what earlier steps made.

So after the whole fold (`runsFold_spec`) the bundle graph is the old one after the emitted
splits, these splits are valid, there is one split for each run after the first of each bundle,
every run is the set of ends of some bundle with the run's vertex as parent, and every bundle is
either a run or an old bundle whose ends are all gone.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

private theorem lt_next {B : BundleState} {c : ℕ} (hc : c ∈ B.vertices) :
    c < B.vertices.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hc)

private theorem card_applyBatch_splits {G : MGraph} {U : List Update} (h : G.BatchIsValid U) :
    (G.applyBatch U).V.card = G.V.card + batchSplitCount U := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch, batchSplitCount]
  | cons u U ih =>
    change ((G.applyUpdate u).applyBatch U).V.card = G.V.card + batchSplitCount (u :: U)
    rw [ih h.2]
    cases u with
    | insert => simp [MGraph.applyUpdate, batchSplitCount, isSplit]
    | delete => simp [MGraph.applyUpdate, batchSplitCount, isSplit]
    | split v v' St Sh =>
      have hV : (G.applyUpdate (.split v v' St Sh)).V.card = G.V.card + 1 :=
        Finset.card_insert_of_notMem h.1.2.1
      simp [hV, batchSplitCount, List.countP_cons, isSplit, Nat.add_right_comm G.V.card,
        Nat.add_assoc]

private theorem bundleRunUpdates_isSplit (b next : ℕ) (runs : List (List End)) :
    ∀ op ∈ bundleRunUpdates b next runs, isSplit op = true := by
  intro op hop
  simp only [bundleRunUpdates, List.mem_map] at hop
  obtain ⟨_, _, rfl⟩ := hop
  rfl

private theorem bundleRunUpdates_splitCount (b next : ℕ) (runs : List (List End)) :
    batchSplitCount (bundleRunUpdates b next runs) = runs.length - 1 := by
  rw [batchSplitCount, List.countP_eq_length.mpr (bundleRunUpdates_isSplit b next runs),
    bundleRunUpdates_length]

/-- One step of the fold: bundle `b` keeps its first run, and the fresh names `next + i` take the
other runs, each with the core vertex of its run as parent. Other bundles keep their ends and
parents. -/
theorem runsFoldStep_spec (ops : List Update) (st : BundleState) (b : ℕ)
    (vruns : List (ℕ × List End)) (hb : b ∈ st.vertices)
    (hlive : ∀ x : End, x.1 ∈ st.edges → st.bundleOf x ∈ st.vertices)
    (hn : (vruns.map Prod.snd).flatten.Nodup)
    (hcover : ∀ x, x ∈ (vruns.map Prod.snd).flatten ↔ x.1 ∈ st.edges ∧ st.bundleOf x = b) :
    let next := st.vertices.sup id + 1
    let newOps := bundleRunUpdates b next (vruns.map Prod.snd)
    let s' := runsFoldStep (ops, st) (b, vruns)
    s'.1 = ops ++ newOps ∧ s'.2.graph = st.graph.applyBatch newOps ∧
    st.graph.BatchIsValid newOps ∧ s'.2.edges = st.edges ∧
    (∀ c, c ∈ s'.2.vertices ↔ c ∈ st.vertices ∨ ∃ i < (vruns.drop 1).length, c = next + i) ∧
    (∀ c ∈ st.vertices, c ≠ b → s'.2.ends c = st.ends c ∧ s'.2.parent c = st.parent c) ∧
    (vruns = [] → s'.2.ends b = ∅ ∧ s'.2.parent b = st.parent b) ∧
    (∀ vr, vruns.head? = some vr → s'.2.ends b = vr.2.toFinset ∧ s'.2.parent b = vr.1) ∧
    ∀ i (hi : i < (vruns.drop 1).length),
      s'.2.ends (next + i) = (vruns.drop 1)[i].2.toFinset ∧
      s'.2.parent (next + i) = (vruns.drop 1)[i].1 := by
  intro next newOps s'
  let runs := vruns.map Prod.snd
  obtain ⟨hE, hV, hOther, hEndsB, -, hFresh⟩ :=
    bundleSplitFoldStep_fibers 0 0 b (fun _ => false) st ops runs hb hlive hn hcover
  have hlen : (runs.drop 1).length = (vruns.drop 1).length := by simp [runs]
  have hget : ∀ i (hi : i < (vruns.drop 1).length),
      (runs.drop 1)[i]'(hlen ▸ hi) = (vruns.drop 1)[i].2 := by
    intro i hi
    simp [runs]
  have hpar : ∀ w, s'.2.parent w = runParent b next vruns st.parent w := fun _ => rfl
  have hends : ∀ c, s'.2.ends c =
      (bundleSplitFoldStep 0 0 (fun _ => false) (ops, st) (b, runs)).2.ends c := fun _ => rfl
  refine ⟨rfl, ?_, ?_, hE, fun c => by rw [← hlen]; exact hV c, ?_, ?_, ?_, ?_⟩
  · exact bundleGraph_of_applied _ _
  · refine bundleRunUpdates_valid st.graph b next runs hb (fun c hc => lt_next hc) hn ?_
    intro x hx
    obtain ⟨h₁, h₂⟩ := (hcover x).mp hx
    exact ⟨h₁, (BundleState.graph_src st x).trans h₂⟩
  · intro c hc hcb
    refine ⟨(hends c).trans (hOther c hc hcb).1, ?_⟩
    rw [hpar]
    have hlt : c < next := lt_next hc
    simp [runParent, hcb, Nat.not_le_of_lt hlt]
  · rintro rfl
    refine ⟨(hends b).trans (by simpa [runs] using hEndsB), ?_⟩
    rw [hpar]
    simp [runParent]
  · intro vr hvr
    refine ⟨(hends b).trans ?_, ?_⟩
    · rw [hEndsB]
      cases vruns with
      | nil => simp at hvr
      | cons v0 rest =>
        simp only [List.head?_cons, Option.some.injEq] at hvr
        subst hvr
        simp [runs]
    · rw [hpar]
      simp [runParent, hvr]
  · intro i hi
    have hbn : b < next := lt_next hb
    refine ⟨(hends _).trans ((hFresh i (hlen ▸ hi)).1.trans (by rw [hget i hi])), ?_⟩
    rw [hpar]
    have hne : next + i ≠ b := by omega
    have hg : vruns[i + 1]? = some (vruns.drop 1)[i] := by
      have hi1 : i + 1 < vruns.length := by simp at hi; omega
      simp [List.getElem?_eq_getElem hi1]
    simp [runParent, hne, hg]

/-- The result of the whole fold. -/
theorem runsFold_spec (G₀ : MGraph) (plan : List (ℕ × List (ℕ × List End)))
    (ops : List Update) (st : BundleState)
    (hnd : (plan.map Prod.fst).Nodup) (hmem : ∀ p ∈ plan, p.1 ∈ st.vertices)
    (hlive : ∀ x : End, x.1 ∈ st.edges → st.bundleOf x ∈ st.vertices)
    (hruns : ∀ p ∈ plan, ((p.2.map Prod.snd).flatten).Nodup ∧
      ∀ x, x ∈ (p.2.map Prod.snd).flatten ↔ x.1 ∈ st.edges ∧ st.bundleOf x = p.1)
    (hg : st.graph = G₀.applyBatch ops) (hv : G₀.BatchIsValid ops) :
    let F := plan.foldl runsFoldStep (ops, st)
    F.2.edges = st.edges ∧ F.2.graph = G₀.applyBatch F.1 ∧ G₀.BatchIsValid F.1 ∧
    (∃ newOps, F.1 = ops ++ newOps ∧ (∀ op ∈ newOps, isSplit op = true) ∧
      batchSplitCount newOps = (plan.map fun p => p.2.length - 1).sum) ∧
    F.2.vertices.card = st.vertices.card + (plan.map fun p => p.2.length - 1).sum ∧
    st.vertices ⊆ F.2.vertices ∧
    (∀ c ∈ st.vertices, c ∉ plan.map Prod.fst →
      F.2.ends c = st.ends c ∧ F.2.parent c = st.parent c) ∧
    (∀ p ∈ plan, ∀ vr ∈ p.2, ∃ c ∈ F.2.vertices, F.2.ends c = vr.2.toFinset ∧
      F.2.parent c = vr.1) ∧
    ∀ c ∈ F.2.vertices, (c ∈ st.vertices ∧ c ∉ plan.map Prod.fst) ∨
      (∃ p ∈ plan, ∃ vr ∈ p.2, F.2.ends c = vr.2.toFinset ∧ F.2.parent c = vr.1) ∨
      (∃ p ∈ plan, p.2 = [] ∧ c = p.1 ∧ F.2.ends c = ∅ ∧ F.2.parent c = st.parent c) := by
  induction plan generalizing ops st with
  | nil =>
    refine ⟨rfl, hg, hv, ⟨[], by simp, by simp, by simp [batchSplitCount]⟩, by simp,
      Finset.Subset.rfl, fun _ _ _ => ⟨rfl, rfl⟩, by simp, fun c hc => Or.inl ⟨hc, by simp⟩⟩
  | cons p rest ih =>
    obtain ⟨b, vruns⟩ := p
    have hb : b ∈ st.vertices := hmem _ List.mem_cons_self
    obtain ⟨hn₀, hcover₀⟩ := hruns _ List.mem_cons_self
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      runsFoldStep_spec ops st b vruns hb hlive hn₀ hcover₀
    set next := st.vertices.sup id + 1 with hnext
    set s' := runsFoldStep (ops, st) (b, vruns) with hs'
    have hndr : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    have hbr : b ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hrest_ne : ∀ q ∈ rest, q.1 ≠ b := fun q hq he =>
      hbr (List.mem_map.mpr ⟨q, hq, he⟩)
    have hrest_mem : ∀ q ∈ rest, q.1 ∈ st.vertices :=
      fun q hq => hmem q (List.mem_cons_of_mem _ hq)
    have hsub : st.vertices ⊆ s'.2.vertices := fun c hc => (h5 c).mpr (Or.inl hc)
    have hfresh_mem : ∀ i < (vruns.drop 1).length, next + i ∈ s'.2.vertices :=
      fun i hi => (h5 _).mpr (Or.inr ⟨i, hi, rfl⟩)
    have hfresh_notin : ∀ i, next + i ∉ rest.map Prod.fst := by
      intro i hm
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
      have := lt_next (hrest_mem q hq)
      omega
    have hends_eq : ∀ c ∈ st.vertices, c ≠ b → ∀ x, (x.1 ∈ s'.2.edges ∧ s'.2.bundleOf x = c ↔
        x.1 ∈ st.edges ∧ st.bundleOf x = c) := by
      intro c hc hcb x
      rw [← BundleState.mem_ends, ← BundleState.mem_ends, (h6 c hc hcb).1]
    have hlive' : ∀ x : End, x.1 ∈ s'.2.edges → s'.2.bundleOf x ∈ s'.2.vertices := by
      intro x hx
      have hx₀ : x.1 ∈ st.edges := h4 ▸ hx
      by_cases hxb : st.bundleOf x = b
      · have hxf := (hcover₀ x).mpr ⟨hx₀, hxb⟩
        obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxf
        obtain ⟨vr, hvr, rfl⟩ := List.mem_map.mp hr
        cases vruns with
        | nil => simp at hvr
        | cons v0 tl =>
          rcases List.mem_cons.mp hvr with rfl | hvr
          · have he := (h8 _ rfl).1
            have : x ∈ s'.2.ends b := by rw [he]; exact List.mem_toFinset.mpr hxr
            rw [((BundleState.mem_ends _ _ _).mp this).2]
            exact hsub hb
          · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvr
            have hi' : i < ((v0 :: tl).drop 1).length := by simpa using hi
            have he := (h9 i hi').1
            have : x ∈ s'.2.ends (next + i) := by
              rw [he]
              simpa using hxr
            rw [((BundleState.mem_ends _ _ _).mp this).2]
            exact hfresh_mem i hi'
      · have hc := hlive x hx₀
        have := (hends_eq _ hc hxb x).mpr ⟨hx₀, rfl⟩
        rw [this.2]
        exact hsub hc
    have hruns' : ∀ q ∈ rest, ((q.2.map Prod.snd).flatten).Nodup ∧
        ∀ x, x ∈ (q.2.map Prod.snd).flatten ↔ x.1 ∈ s'.2.edges ∧ s'.2.bundleOf x = q.1 := by
      intro q hq
      obtain ⟨hn, hc⟩ := hruns q (List.mem_cons_of_mem _ hq)
      exact ⟨hn, fun x => (hc x).trans
        (hends_eq q.1 (hrest_mem q hq) (hrest_ne q hq) x).symm⟩
    have hg' : s'.2.graph = G₀.applyBatch s'.1 := by
      rw [h2, h1, applyBatch_append, hg]
    have hv' : G₀.BatchIsValid s'.1 := by
      rw [h1, batchIsValid_append]
      exact ⟨hv, hg ▸ h3⟩
    obtain ⟨i1, i2, i3, ⟨newOps, i4a, i4b, i4c⟩, i5, i6, i7, i8, i9⟩ :=
      ih s'.1 s'.2 hndr (fun q hq => hsub (hrest_mem q hq)) hlive' hruns' hg' hv'
    have hfold : (((b, vruns) :: rest).foldl runsFoldStep (ops, st)) =
        rest.foldl runsFoldStep (s'.1, s'.2) := rfl
    rw [hfold]
    have hstepCount : batchSplitCount (bundleRunUpdates b next (vruns.map Prod.snd)) =
        vruns.length - 1 := by
      rw [bundleRunUpdates_splitCount, List.length_map]
    have hcard' : s'.2.vertices.card = st.vertices.card + (vruns.length - 1) := by
      have hc := card_applyBatch_splits h3
      rw [← h2] at hc
      change s'.2.vertices.card = st.vertices.card + _ at hc
      rw [hc, hstepCount]
    refine ⟨i1.trans h4, i2, i3, ⟨bundleRunUpdates b next (vruns.map Prod.snd) ++ newOps,
      by rw [i4a, h1, List.append_assoc], ?_, ?_⟩, ?_, hsub.trans i6, ?_, ?_, ?_⟩
    · intro op hop
      rcases List.mem_append.mp hop with hop | hop
      · exact bundleRunUpdates_isSplit _ _ _ op hop
      · exact i4b op hop
    · rw [batchSplitCount_append, i4c, hstepCount]
      simp
    · rw [i5, hcard']
      simp [Nat.add_assoc]
    · intro c hc hcn
      have hcb : c ≠ b := fun h => hcn (h ▸ List.mem_cons_self)
      have hcr : c ∉ rest.map Prod.fst := fun h => hcn (List.mem_cons_of_mem _ h)
      obtain ⟨e1, e2⟩ := i7 c (hsub hc) hcr
      exact ⟨e1.trans (h6 c hc hcb).1, e2.trans (h6 c hc hcb).2⟩
    · intro q hq vr hvr
      rcases List.mem_cons.mp hq with rfl | hq
      · cases vruns with
        | nil => simp at hvr
        | cons v0 tl =>
          rcases List.mem_cons.mp hvr with rfl | hvr
          · obtain ⟨e1, e2⟩ := i7 b (hsub hb) hbr
            obtain ⟨f1, f2⟩ := h8 _ rfl
            exact ⟨b, i6 (hsub hb), e1.trans f1, e2.trans f2⟩
          · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvr
            have hi' : i < ((v0 :: tl).drop 1).length := by simpa using hi
            obtain ⟨e1, e2⟩ := i7 (next + i) (hfresh_mem i hi') (hfresh_notin i)
            obtain ⟨f1, f2⟩ := h9 i hi'
            exact ⟨next + i, i6 (hfresh_mem i hi'), e1.trans (by simpa using f1),
              e2.trans (by simpa using f2)⟩
      · exact i8 q hq vr hvr
    · intro c hc
      rcases i9 c hc with ⟨hcs, hcr⟩ | ⟨q, hq, vr, hvr, e1, e2⟩ | ⟨q, hq, hq2, rfl, e1, e2⟩
      · obtain ⟨e1, e2⟩ := i7 c hcs hcr
        rcases (h5 c).mp hcs with hco | ⟨i, hi, rfl⟩
        · by_cases hcb : c = b
          · subst hcb
            cases hhd : vruns.head? with
            | none =>
              have hnil : vruns = [] := List.head?_eq_none_iff.mp hhd
              obtain ⟨f1, f2⟩ := h7 hnil
              exact Or.inr (Or.inr ⟨(c, vruns), List.mem_cons_self, hnil, rfl, e1.trans f1,
                e2.trans f2⟩)
            | some v0 =>
              obtain ⟨f1, f2⟩ := h8 v0 hhd
              exact Or.inr (Or.inl ⟨(c, vruns), List.mem_cons_self, v0,
                List.mem_of_mem_head? hhd, e1.trans f1, e2.trans f2⟩)
          · exact Or.inl ⟨hco, by simp [hcb, hcr]⟩
        · obtain ⟨f1, f2⟩ := h9 i hi
          refine Or.inr (Or.inl ⟨(b, vruns), List.mem_cons_self, (vruns.drop 1)[i], ?_,
            e1.trans f1, e2.trans f2⟩)
          exact List.mem_of_mem_drop (List.getElem_mem hi)
      · exact Or.inr (Or.inl ⟨q, List.mem_cons_of_mem _ hq, vr, hvr, e1, e2⟩)
      · have hqs := hrest_mem q hq
        exact Or.inr (Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq2, rfl, e1,
          e2.trans (h6 q.1 hqs (hrest_ne q hq)).2⟩)

/-- The bundle vertices after one step: the old ones and the fresh names. -/
theorem runsFoldStep_vertices (s : List Update × BundleState) (b : ℕ)
    (vruns : List (ℕ × List End)) (c : ℕ) :
    c ∈ (runsFoldStep s (b, vruns)).2.vertices ↔
      c ∈ s.2.vertices ∨ ∃ i < (vruns.drop 1).length, c = s.2.vertices.sup id + 1 + i := by
  obtain ⟨ops, st⟩ := s
  have h := bundleRunUpdates_V_mem st.graph b (st.vertices.sup id + 1) (vruns.map Prod.snd) c
  change c ∈ (st.graph.applyBatch
    (bundleRunUpdates b (st.vertices.sup id + 1) (vruns.map Prod.snd))).V ↔ _
  rw [h]
  simp [BundleState.graph]

/-- A name that is not a bundle after one step keeps its parent. -/
theorem runsFoldStep_parent_out (s : List Update × BundleState) (b : ℕ)
    (vruns : List (ℕ × List End)) (hb : b ∈ s.2.vertices) (c : ℕ)
    (hc : c ∉ (runsFoldStep s (b, vruns)).2.vertices) :
    (runsFoldStep s (b, vruns)).2.parent c = s.2.parent c := by
  have hV := runsFoldStep_vertices s b vruns
  have hcb : c ≠ b := fun h => hc ((hV c).mpr (Or.inl (h ▸ hb)))
  change runParent b (s.2.vertices.sup id + 1) vruns s.2.parent c = _
  unfold runParent
  simp only [hcb, ↓reduceIte]
  by_cases hle : s.2.vertices.sup id + 1 ≤ c
  · simp only [hle, ↓reduceIte]
    have hlen : vruns.length ≤ c - (s.2.vertices.sup id + 1) + 1 := by
      by_contra hlt
      refine hc ((hV c).mpr (Or.inr ⟨c - (s.2.vertices.sup id + 1), ?_, by omega⟩))
      simp only [List.length_drop]
      omega
    rw [List.getElem?_eq_none hlen]
  · simp only [hle, ↓reduceIte]

theorem runsFold_vertices_mono (plan : List (ℕ × List (ℕ × List End)))
    (s : List Update × BundleState) :
    s.2.vertices ⊆ (plan.foldl runsFoldStep s).2.vertices := by
  induction plan generalizing s with
  | nil => exact Finset.Subset.rfl
  | cons p rest ih =>
    obtain ⟨b, vruns⟩ := p
    exact Finset.Subset.trans (fun c hc => (runsFoldStep_vertices s b vruns c).mpr (Or.inl hc)) (ih _)

/-- A name that is not a bundle after the fold keeps its parent. -/
theorem runsFold_parent_out (plan : List (ℕ × List (ℕ × List End)))
    (s : List Update × BundleState) (hmem : ∀ p ∈ plan, p.1 ∈ s.2.vertices) (c : ℕ)
    (hc : c ∉ (plan.foldl runsFoldStep s).2.vertices) :
    (plan.foldl runsFoldStep s).2.parent c = s.2.parent c := by
  induction plan generalizing s with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨b, vruns⟩ := p
    have hb : b ∈ s.2.vertices := hmem _ List.mem_cons_self
    have hsub : s.2.vertices ⊆ (runsFoldStep s (b, vruns)).2.vertices :=
      fun c hc => (runsFoldStep_vertices s b vruns c).mpr (Or.inl hc)
    change (rest.foldl runsFoldStep (runsFoldStep s (b, vruns))).2.parent c = _
    rw [ih _ (fun q hq => hsub (hmem q (List.mem_cons_of_mem _ hq))) hc]
    exact runsFoldStep_parent_out s b vruns hb c
      (fun h => hc (runsFold_vertices_mono rest _ h))

end MinCostFlow.SparseCore
