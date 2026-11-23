module

public import MinCostFlow.SparseCore.Program.BundlePotBridge
public import MinCostFlow.Bundle.CoreCongr

/-!
# Root-grouped equivalence for `bundleRunsStep` (`BundleModelBridge`)

Proves that under `BundleStepReady cs B k ord ord' U`, the canonical bundle step
`bundleRunsStep cs B k ord' U` (`M2`, `SparseCore/BundleRunsStep.lean`) reduces bit-for-bit to
partitioning only the genuinely splitting bundles by final core vertex:

1. **At most one run per core vertex (`cycRuns_eq_of_isArc`, `bundleRunsOf_eq_byRootVRuns`)**:
   Every old bundle `b` remains a single cyclic arc inside `(cord' v).filter (·.1 ∈ E)` at every
   final core vertex `v`, so `cycRuns` returns `[]` or a singleton `[r]` whose elements are
   `{x ∈ survivingEnds B E b | src' x = v}`.
2. **Exact root-grouped fold (`bundleRunsStep_eq_byRoot`)**:
   `bundleRunsStep` emits the exact same update batch `U_B`, vertex set, edge set, and `bundleOf`
   as `byRootSplitFold` on `exactSplitCands` (only bundles spanning `≥ 2` final core vertices).
3. **Parents, range vertices, and smaller-side detection (`bundleRunsStep_parent_eq`,
   `bundleRunsStep_vertices_range`, `splitCands_exact_iff`)**:
   Nonempty bundles have parent equal to the final core vertex of any surviving end, empty bundles
   keep their old parent, vertex sets remain `Finset.range n`, and scanning all non-largest roots
   `w ∈ G_v.erase w_max` of each split group identifies `exactSplitCands` with zero false positives.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.Chain
open MinCostFlow.DynSpanner

/-! ## 1. Definitions -/

@[expose] public section

/-- Raw root-grouped runs of bundle `b`: sorted by increasing final core vertex `v`, with the
surviving ends at `v` sorted by `endKey`. -/
noncomputable def rawByRootVRuns (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b : ℕ) :
    List (ℕ × List End) :=
  ((finalRootsOf B E src' b).sort (· ≤ ·)).map fun v =>
    (v, (((survivingEnds B E b).filter fun x => src' x = v).image endKey).sort (· ≤ ·)
      |>.map endOfKey)

/-- Canonical root-grouped runs of bundle `b`: the largest run (tie-broken by smallest core vertex)
first so it keeps bundle name `b`, followed by the remaining runs in increasing core-vertex order. -/
noncomputable def byRootVRuns (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b : ℕ) :
    List (ℕ × List End) :=
  promoteLargestRun (rawByRootVRuns B E src' b)

/-- Root-grouped bundle step processing only a list `cands` of candidate splitting bundles
(in increasing order), starting from deletions `dels` and `{ B with edges := E }`. -/
noncomputable def byRootSplitFold (B : BundleState) (E : Finset ℕ) (src' : End → ℕ)
    (dels : List Update) (cands : List ℕ) : List Update × BundleState :=
  (cands.map fun b => (b, byRootVRuns B E src' b)).foldl runsFoldStep
    (dels, { B with edges := E })

/-- The exact sorted list of splitting bundles of `B` under kept edges `E` and final core-vertex
map `src'`. -/
noncomputable def exactSplitCands (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) : List ℕ :=
  (B.vertices.sort (· ≤ ·)).filter fun b => decide (2 ≤ (finalRootsOf B E src' b).card)

end

/-! ## 2. Arc preservation and single-run theorem -/

public section

private theorem isArc_filter_self {α : Type*} {p : α → Bool} {xs : List α}
    (h : IsArc p xs) (q : α → Bool) : IsArc p (xs.filter q) := by
  obtain ⟨u, v, hrot, hu, hv⟩ := h
  refine ⟨u.filter q, v.filter q, ?_, ?_, ?_⟩
  · have hf := isRotated_filter q hrot
    rwa [List.filter_append] at hf
  · intro x hx
    exact hu x (List.mem_filter.mp hx).1
  · intro x hx
    exact hv x (List.mem_filter.mp hx).1

private theorem isArc_rotationStep {G : MGraph} {β : ℕ} {u : Update}
    {ρ : Rotation G} {σ : Rotation (G.applyUpdate u)}
    (hs : RotationStep β u ρ σ) (hu : G.UpdateIsValid u)
    {E : Finset ℕ} (hEG : E ⊆ G.E) (p : End → Bool)
    (harc : ∀ v, IsArc p ((ρ.order v).filter fun x => decide (x.1 ∈ E))) :
    ∀ v, IsArc p ((σ.order v).filter fun x => decide (x.1 ∈ E)) := by
  let inE : End → Bool := fun x => decide (x.1 ∈ E)
  cases u with
  | insert e a b =>
    intro v
    have heE : e ∉ E := fun h => hu.1 (hEG h)
    have hrot := isRotated_filter inE (hs v)
    have hfe : (((σ.order v).filter fun x => x.1 != e).filter inE) = (σ.order v).filter inE := by
      rw [List.filter_filter]
      congr 1; funext x; apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, bne_iff_ne, inE, decide_eq_true_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun hxe => heE (hxe ▸ h)⟩⟩
    rw [hfe] at hrot
    exact (harc v).of_isRotated hrot
  | delete e =>
    intro v
    have hrot := isRotated_filter inE (hs v)
    have hsw : (((ρ.order v).filter fun x => x.1 != e).filter inE) =
        ((ρ.order v).filter inE).filter fun x => x.1 != e := by
      rw [List.filter_filter, List.filter_filter]
      congr 1; funext x; exact Bool.and_comm _ _
    rw [hsw] at hrot
    exact (isArc_filter_self (harc v) _).of_isRotated hrot
  | split v₀ v' St Sh =>
    intro w
    obtain ⟨hstay, hmove, -, hother⟩ := hs
    by_cases hw0 : w = v₀
    · subst hw0
      have hrot := isRotated_filter inE hstay
      have hsw : (((ρ.order w).filter fun x => !splitEnds St Sh x).filter inE) =
          ((ρ.order w).filter inE).filter fun x => !splitEnds St Sh x := by
        rw [List.filter_filter, List.filter_filter]
        congr 1; funext x; exact Bool.and_comm _ _
      rw [hsw] at hrot
      exact (isArc_filter_self (harc w) _).of_isRotated hrot
    · by_cases hw' : w = v'
      · subst hw'
        have hrot := isRotated_filter inE hmove
        have hsw : (((ρ.order v₀).filter (splitEnds St Sh)).filter inE) =
            ((ρ.order v₀).filter inE).filter (splitEnds St Sh) := by
          rw [List.filter_filter, List.filter_filter]
          congr 1; funext x; exact Bool.and_comm _ _
        rw [hsw] at hrot
        exact (isArc_filter_self (harc v₀) _).of_isRotated hrot
      · have hrot := isRotated_filter inE (hother w hw0 hw')
        exact (harc w).of_isRotated hrot

private theorem isArc_rotationBatch {G : MGraph} {β : ℕ} {U : List Update}
    {ρ : Rotation G} {σ : Rotation (G.applyBatch U)}
    (hrb : RotationBatch β U ρ σ) (hv : G.BatchIsValid U)
    {E : Finset ℕ} (hEG : E ⊆ G.E) (hdisj : Disjoint E (batchDeletes U)) (p : End → Bool)
    (harc : ∀ v, IsArc p ((ρ.order v).filter fun x => decide (x.1 ∈ E))) :
    ∀ v, IsArc p ((σ.order v).filter fun x => decide (x.1 ∈ E)) := by
  induction hrb with
  | nil hrot =>
    intro v
    exact (harc v).of_isRotated (isRotated_filter _ (hrot v))
  | @cons G u U ρ τ σ hs hrest ih =>
    have hdisj_rest : Disjoint E (batchDeletes U) := by
      rw [Finset.disjoint_left] at hdisj ⊢
      intro e he hU
      obtain ⟨w, hw, rfl⟩ := (mem_batchDeletes_iff U e).mp hU
      exact hdisj he ((mem_batchDeletes_iff (u :: U) e).mpr ⟨.delete e, List.mem_cons_of_mem _ hw, rfl⟩)
    have hE_mid : E ⊆ (G.applyUpdate u).E := by
      intro e he
      cases u with
      | insert f a b => exact Finset.mem_insert_of_mem (hEG he)
      | delete f =>
        have hne : e ≠ f := fun hef => by
          subst hef
          exact Finset.disjoint_left.mp hdisj he
            ((mem_batchDeletes_iff (.delete e :: U) e).mpr ⟨.delete e, List.mem_cons_self, rfl⟩)
        exact Finset.mem_erase.mpr ⟨hne, hEG he⟩
      | split => exact hEG he
    exact ih hv.2 hE_mid hdisj_rest (isArc_rotationStep hs hv.1 hEG p harc)

/-- If `p` is already a cyclic arc of a nodup list `xs`, then `cycRuns p xs` has at most one run:
empty when no element satisfies `p`, and a singleton whose elements are `xs.filter p` otherwise. -/
theorem cycRuns_eq_of_isArc {α : Type*} [DecidableEq α] {p : α → Bool} {xs : List α}
    (hn : xs.Nodup) (harc : IsArc p xs) :
    (∀ x ∈ xs, p x = false) ∧ cycRuns p xs = [] ∨
    ∃ r, cycRuns p xs = [r] ∧ r.Nodup ∧ ∀ x, x ∈ r ↔ x ∈ xs ∧ p x = true := by
  by_cases hex : ∃ x ∈ xs, p x = true
  · right
    obtain ⟨r, hr, hall⟩ := cycRuns_block p p harc (fun _ _ h => h) hex
    have hnd := cycRuns_flatten_nodup p hn
    have hspec := cycRuns_spec p xs
    have hsingleton : cycRuns p xs = [r] := by
      cases hc : cycRuns p xs with
      | nil => rw [hc] at hr; cases hr
      | cons a rest =>
        rw [hc] at hr hnd hspec
        have ha_eq : a = r := by
          obtain ⟨hane, hap⟩ := hspec a List.mem_cons_self
          have hx := List.head_mem hane
          obtain ⟨hxs, hpx⟩ := hap _ hx
          exact runs_eq_of_mem hnd List.mem_cons_self hr hx (hall _ hxs hpx)
        subst ha_eq
        cases rest with
        | nil => rfl
        | cons b rest' =>
          exfalso
          obtain ⟨hbne, hbp⟩ := hspec b (List.mem_cons_of_mem _ List.mem_cons_self)
          have hx := List.head_mem hbne
          obtain ⟨hxs, hpx⟩ := hbp _ hx
          have hxr := hall _ hxs hpx
          simp only [List.flatten_cons, List.nodup_append] at hnd
          exact hnd.2.2 _ hxr _ (List.mem_append_left _ hx) rfl
    refine ⟨r, hsingleton, ?_, ?_⟩
    · rw [hsingleton, List.flatten_singleton] at hnd
      exact hnd
    · intro x
      have hm := mem_cycRuns_flatten p xs x
      rw [hsingleton, List.flatten_singleton] at hm
      exact hm
  · left
    have hfalse : ∀ x ∈ xs, p x = false := fun x hx => by
      cases hpx : p x
      · rfl
      · exact False.elim (hex ⟨x, hx, hpx⟩)
    refine ⟨hfalse, ?_⟩
    cases hc : cycRuns p xs with
    | nil => rfl
    | cons a rest =>
      exfalso
      obtain ⟨hane, hap⟩ := cycRuns_spec p xs a (hc ▸ List.mem_cons_self)
      obtain ⟨hxs, hpx⟩ := hap _ (List.head_mem hane)
      rw [hfalse _ hxs] at hpx
      exact Bool.false_ne_true hpx

/-! ## 3. Congruence and filtering of `runsFoldStep` -/

private theorem runsFoldStep_congr_vruns (s : List Update × BundleState) (b : ℕ)
    {vr₁ vr₂ : List (ℕ × List End)}
    (hmap : vr₁.map Prod.fst = vr₂.map Prod.fst)
    (hset : ∀ i (h₁ : i < vr₁.length) (h₂ : i < vr₂.length), vr₁[i].2.toFinset = vr₂[i].2.toFinset) :
    runsFoldStep s (b, vr₁) = runsFoldStep s (b, vr₂) := by
  have hlen : vr₁.length = vr₂.length := by
    have := congrArg List.length hmap
    simpa using this
  have hbu : bundleRunUpdates b (s.2.vertices.sup id + 1) (vr₁.map Prod.snd) =
      bundleRunUpdates b (s.2.vertices.sup id + 1) (vr₂.map Prod.snd) := by
    unfold bundleRunUpdates
    apply List.ext_getElem
    · simp [hlen]
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_drop]
      have hi1 : 1 + i < vr₁.length := by simp at h₁; omega
      have hi2 : 1 + i < vr₂.length := by omega
      have heq := hset (1 + i) hi1 hi2
      congr 1
      · ext e
        simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
        constructor
        · rintro ⟨⟨f, side⟩, ⟨hm, hs⟩, rfl⟩
          have hs' : side = true := hs
          subst hs'
          have hm' : (f, true) ∈ vr₂[1 + i].2 :=
            List.mem_toFinset.mp (heq ▸ List.mem_toFinset.mpr hm)
          exact ⟨(f, true), ⟨hm', rfl⟩, rfl⟩
        · rintro ⟨⟨f, side⟩, ⟨hm, hs⟩, rfl⟩
          have hs' : side = true := hs
          subst hs'
          have hm' : (f, true) ∈ vr₁[1 + i].2 :=
            List.mem_toFinset.mp (heq.symm ▸ List.mem_toFinset.mpr hm)
          exact ⟨(f, true), ⟨hm', rfl⟩, rfl⟩
      · ext e
        simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
        constructor
        · rintro ⟨⟨f, side⟩, ⟨hm, hs⟩, rfl⟩
          have hs' : side = false := by simpa using hs
          subst hs'
          have hm' : (f, false) ∈ vr₂[1 + i].2 :=
            List.mem_toFinset.mp (heq ▸ List.mem_toFinset.mpr hm)
          exact ⟨(f, false), ⟨hm', rfl⟩, rfl⟩
        · rintro ⟨⟨f, side⟩, ⟨hm, hs⟩, rfl⟩
          have hs' : side = false := by simpa using hs
          subst hs'
          have hm' : (f, false) ∈ vr₁[1 + i].2 :=
            List.mem_toFinset.mp (heq.symm ▸ List.mem_toFinset.mpr hm)
          exact ⟨(f, false), ⟨hm', rfl⟩, rfl⟩
  have hpar : runParent b (s.2.vertices.sup id + 1) vr₁ s.2.parent =
      runParent b (s.2.vertices.sup id + 1) vr₂ s.2.parent := by
    funext w
    unfold runParent
    by_cases hwb : w = b
    · simp only [hwb, ↓reduceIte]
      cases vr₁ with
      | nil =>
        cases vr₂ with
        | nil => rfl
        | cons _ _ => simp at hlen
      | cons x xs =>
        cases vr₂ with
        | nil => simp at hlen
        | cons y ys =>
          simp only [List.head?_cons]
          exact by simpa using congrArg List.head? hmap
    · simp only [hwb, ↓reduceIte]
      by_cases hle : s.2.vertices.sup id + 1 ≤ w
      · simp only [hle, ↓reduceIte]
        set idx := w - (s.2.vertices.sup id + 1) + 1
        by_cases hi : idx < vr₁.length
        · have hi2 : idx < vr₂.length := hlen ▸ hi
          rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2]
          dsimp only
          have hget := congrArg (fun l => l[idx]?) hmap
          simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
            List.getElem?_eq_getElem hi2, Option.map_some, Option.some.injEq] at hget
          exact hget
        · have hi1 : vr₁.length ≤ idx := Nat.le_of_not_lt hi
          have hi2 : vr₂.length ≤ idx := hlen ▸ hi1
          rw [List.getElem?_eq_none hi1, List.getElem?_eq_none hi2]
      · simp only [hle, ↓reduceIte]
  unfold runsFoldStep
  dsimp only
  have h1 : bundleSplitFoldStep 0 0 (fun _ => false) s (b, vr₁.map Prod.snd) =
      let after := s.2.graph.applyBatch (bundleRunUpdates b (s.2.vertices.sup id + 1) (vr₁.map Prod.snd))
      (s.1 ++ bundleRunUpdates b (s.2.vertices.sup id + 1) (vr₁.map Prod.snd),
        { vertices := after.V, edges := after.E,
          parent := (bundleSplitFoldStep 0 0 (fun _ => false) s (b, vr₁.map Prod.snd)).2.parent,
          bundleOf := after.src }) := rfl
  have h2 : bundleSplitFoldStep 0 0 (fun _ => false) s (b, vr₂.map Prod.snd) =
      let after := s.2.graph.applyBatch (bundleRunUpdates b (s.2.vertices.sup id + 1) (vr₂.map Prod.snd))
      (s.1 ++ bundleRunUpdates b (s.2.vertices.sup id + 1) (vr₂.map Prod.snd),
        { vertices := after.V, edges := after.E,
          parent := (bundleSplitFoldStep 0 0 (fun _ => false) s (b, vr₂.map Prod.snd)).2.parent,
          bundleOf := after.src }) := rfl
  rw [h1, h2]
  dsimp only
  rw [hbu, hpar]

private theorem runsFoldStep_of_len_le_one (s : List Update × BundleState) (b : ℕ)
    (vruns : List (ℕ × List End)) (hlen : vruns.length ≤ 1) :
    (runsFoldStep s (b, vruns)).1 = s.1 ∧
    (runsFoldStep s (b, vruns)).2.vertices = s.2.vertices ∧
    (runsFoldStep s (b, vruns)).2.edges = s.2.edges ∧
    (runsFoldStep s (b, vruns)).2.bundleOf = s.2.bundleOf ∧
    (runsFoldStep s (b, vruns)).2.parent =
      runParent b (s.2.vertices.sup id + 1) vruns s.2.parent := by
  have hdrop : (vruns.map Prod.snd).drop 1 = [] := by
    rw [List.drop_eq_nil_iff, List.length_map]
    exact hlen
  have hbu : bundleRunUpdates b (s.2.vertices.sup id + 1) (vruns.map Prod.snd) = [] := by
    simp [bundleRunUpdates, hdrop]
  have happ : s.2.graph.applyBatch [] = s.2.graph := rfl
  have hbo : s.2.graph.src = s.2.bundleOf := funext (BundleState.graph_src s.2)
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · change s.1 ++ bundleRunUpdates b (s.2.vertices.sup id + 1) (vruns.map Prod.snd) = s.1
    rw [hbu, List.append_nil]
  · change (s.2.graph.applyBatch (bundleRunUpdates b (s.2.vertices.sup id + 1) (vruns.map Prod.snd))).V = _
    rw [hbu, happ]; rfl
  · change (s.2.graph.applyBatch (bundleRunUpdates b (s.2.vertices.sup id + 1) (vruns.map Prod.snd))).E = _
    rw [hbu, happ]; rfl
  · change (s.2.graph.applyBatch (bundleRunUpdates b (s.2.vertices.sup id + 1) (vruns.map Prod.snd))).src = _
    rw [hbu, happ, hbo]

private theorem runsFoldStep_ignore_parent (ops : List Update) (st₁ st₂ : BundleState)
    (b : ℕ) (vruns : List (ℕ × List End))
    (hV : st₁.vertices = st₂.vertices) (hE : st₁.edges = st₂.edges)
    (hbo : st₁.bundleOf = st₂.bundleOf) :
    (runsFoldStep (ops, st₁) (b, vruns)).1 = (runsFoldStep (ops, st₂) (b, vruns)).1 ∧
    (runsFoldStep (ops, st₁) (b, vruns)).2.vertices = (runsFoldStep (ops, st₂) (b, vruns)).2.vertices ∧
    (runsFoldStep (ops, st₁) (b, vruns)).2.edges = (runsFoldStep (ops, st₂) (b, vruns)).2.edges ∧
    (runsFoldStep (ops, st₁) (b, vruns)).2.bundleOf = (runsFoldStep (ops, st₂) (b, vruns)).2.bundleOf := by
  have hg : st₁.graph = st₂.graph := by
    cases st₁; cases st₂; dsimp only at hV hE hbo; subst hV hE hbo; rfl
  dsimp only [runsFoldStep, bundleSplitFoldStep]
  rw [hV, hg]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem foldl_runsFoldStep_ignore_parent (plan : List (ℕ × List (ℕ × List End)))
    (ops : List Update) (st₁ st₂ : BundleState)
    (hV : st₁.vertices = st₂.vertices) (hE : st₁.edges = st₂.edges)
    (hbo : st₁.bundleOf = st₂.bundleOf) :
    (plan.foldl runsFoldStep (ops, st₁)).1 = (plan.foldl runsFoldStep (ops, st₂)).1 ∧
    (plan.foldl runsFoldStep (ops, st₁)).2.vertices = (plan.foldl runsFoldStep (ops, st₂)).2.vertices ∧
    (plan.foldl runsFoldStep (ops, st₁)).2.edges = (plan.foldl runsFoldStep (ops, st₂)).2.edges ∧
    (plan.foldl runsFoldStep (ops, st₁)).2.bundleOf = (plan.foldl runsFoldStep (ops, st₂)).2.bundleOf := by
  induction plan generalizing ops st₁ st₂ with
  | nil => exact ⟨rfl, hV, hE, hbo⟩
  | cons p rest ih =>
    obtain ⟨b, vruns⟩ := p
    obtain ⟨h1, h2, h3, h4⟩ := runsFoldStep_ignore_parent ops st₁ st₂ b vruns hV hE hbo
    simp only [List.foldl_cons]
    have hs1 : runsFoldStep (ops, st₁) (b, vruns) =
        ((runsFoldStep (ops, st₁) (b, vruns)).1, (runsFoldStep (ops, st₁) (b, vruns)).2) := rfl
    have hs2 : runsFoldStep (ops, st₂) (b, vruns) =
        ((runsFoldStep (ops, st₁) (b, vruns)).1, (runsFoldStep (ops, st₂) (b, vruns)).2) :=
      Prod.ext h1.symm rfl
    rw [hs1, hs2]
    exact ih _ _ _ h2 h3 h4

private theorem foldl_runsFoldStep_filter_splits (plan : List (ℕ × List (ℕ × List End)))
    (s : List Update × BundleState) :
    let filtered := plan.filter fun p => decide (2 ≤ p.2.length)
    (plan.foldl runsFoldStep s).1 = (filtered.foldl runsFoldStep s).1 ∧
    (plan.foldl runsFoldStep s).2.vertices = (filtered.foldl runsFoldStep s).2.vertices ∧
    (plan.foldl runsFoldStep s).2.edges = (filtered.foldl runsFoldStep s).2.edges ∧
    (plan.foldl runsFoldStep s).2.bundleOf = (filtered.foldl runsFoldStep s).2.bundleOf := by
  induction plan generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨b, vruns⟩ := p
    by_cases h2 : 2 ≤ vruns.length
    · simp only [List.filter_cons, decide_eq_true h2, List.foldl_cons]
      exact ih (runsFoldStep s (b, vruns))
    · have hle : vruns.length ≤ 1 := by omega
      simp only [List.filter_cons, decide_eq_false h2, List.foldl_cons]
      obtain ⟨h1, h2', h3, h4, -⟩ := runsFoldStep_of_len_le_one s b vruns hle
      have hign := foldl_runsFoldStep_ignore_parent rest s.1 (runsFoldStep s (b, vruns)).2 s.2 h2' h3 h4
      have hstep : runsFoldStep s (b, vruns) = (s.1, (runsFoldStep s (b, vruns)).2) :=
        Prod.ext h1 rfl
      rw [hstep]
      have hih := ih s
      exact ⟨hign.1.trans hih.1, hign.2.1.trans hih.2.1, hign.2.2.1.trans hih.2.2.1,
        hign.2.2.2.trans hih.2.2.2⟩

private theorem cast_order' {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h; rfl

private theorem finset_sort_filter_eq {S T : Finset ℕ} (hST : S ⊆ T) :
    (T.sort (· ≤ ·)).filter (fun v => decide (v ∈ S)) = S.sort (· ≤ ·) := by
  have hperm : ((T.sort (· ≤ ·)).filter (fun v => decide (v ∈ S))).Perm (S.sort (· ≤ ·)) := by
    refine (List.perm_ext_iff_of_nodup ((Finset.sort_nodup T (· ≤ ·)).filter _)
      (Finset.sort_nodup S (· ≤ ·))).mpr fun x => ?_
    simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hST h, h⟩⟩
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2)
    ((Finset.pairwise_sort T (· ≤ ·)).filter _) (Finset.pairwise_sort S (· ≤ ·))

private theorem flatMap_singleton_or_nil {α β : Type*} (l : List α) (f : α → List β)
    (p : α → Bool) (g : α → β)
    (hf : ∀ a ∈ l, if p a then f a = [g a] else f a = []) :
    l.flatMap f = (l.filter p).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := hf a List.mem_cons_self
    have hl := ih fun x hx => hf x (List.mem_cons_of_mem _ hx)
    cases hpa : p a <;> simp only [hpa, Bool.false_eq_true, ↓reduceIte] at ha
    · simp [List.flatMap_cons, ha, hpa, hl]
    · simp [List.flatMap_cons, ha, hpa, hl]

/-! ## 4. Main root-grouped equivalence theorems -/

/-- Under `BundleStepReady`, for every old bundle `b ∈ B.vertices`, `bundleRunsOf` matches
`byRootVRuns` on both core vertices (`map Prod.fst`) and per-run end sets (`toFinset`). -/
theorem bundleRunsOf_eq_byRootVRuns {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U)
    {b : ℕ} (hb : b ∈ B.vertices) :
    let cs' := compLSFBatch cs U
    let E := B.edges \ batchDeletes U
    let cord := coreOrderOf cs' ord'
    let src' := (coreGraph cs'.G cs'.lsf).src
    let vr₁ := bundleRunsOf cs'.RF.R cord E B b
    let vr₂ := byRootVRuns B E src' b
    vr₁.map Prod.fst = vr₂.map Prod.fst ∧
    ∀ i (h₁ : i < vr₁.length) (h₂ : i < vr₂.length), vr₁[i].2.toFinset = vr₂[i].2.toFinset := by
  classical
  obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, _, hσ, hrot, hU, hB⟩ := h
  obtain ⟨he, hI', UC, ⟨hvC, hgeC, hrbC⟩, -, -, -, hdelC, -⟩ :=
    orderedCore_compLSFBatch_local (C_lsst := C_lsst) (ℓ₀ := ℓ₀) hrot (Nat.le_refl 2) hU cs rfl hI
  set cs' := compLSFBatch cs U
  set E := B.edges \ batchDeletes U
  set cord := coreOrderOf cs' ord'
  set C' := coreGraph cs'.G cs'.lsf
  set src' := C'.src
  have hσ' : (he.symm ▸ σ : Rotation cs'.G).order = ord' := (cast_order' _ σ).trans hσ
  have hRF' := compLSF_RF_isRSF hI'
  set ρ_c := coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)
  set σ_c := coreRotation (L := cs'.lsf) (he.symm ▸ σ) hI'.hG_val hRF'
  have hcord : σ_c.order = cord := coreOrderOf_eq (he.symm ▸ σ) hI'.hG_val hRF' hσ'
  have hEC₀ : E ⊆ (coreGraph cs.G cs.lsf).E := Finset.Subset.trans Finset.sdiff_subset hB.1
  have hdisjUC : Disjoint E (batchDeletes UC) := by
    rw [Finset.disjoint_left]
    intro e heE heUC
    obtain ⟨u, hu, rfl⟩ := (mem_batchDeletes_iff UC e).mp heUC
    exact (Finset.mem_sdiff.mp heE).2 (hdelC _ hu e rfl)
  have harc₀ : ∀ v, IsArc (fun x => decide (B.bundleOf x = b))
      ((ρ_c.order v).filter fun x => decide (x.1 ∈ E)) := by
    intro v
    by_cases hv : v = B.parent b
    · subst hv
      have ha := BundleState.restricted_arc_assigned hB hb
      have hsub : ((ρ_c.order (B.parent b)).filter fun x => decide (x.1 ∈ E)) =
          (restrictedEnds ρ_c B.edges (B.parent b)).filter fun x => decide (x.1 ∈ E) := by
        unfold restrictedEnds
        rw [List.filter_filter]
        congr 1; funext x; apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun hx => ⟨hx, Finset.sdiff_subset hx⟩, fun hx => hx.1⟩
      rw [hsub]
      exact isArc_filter_self ha _
    · refine ⟨[], (ρ_c.order v).filter fun x => decide (x.1 ∈ E), List.IsRotated.refl _,
        by simp, fun x hx => ?_⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hx
      have hxρ := (ρ_c.mem_order v x).mp hx.1
      have hxb := (hB.2.2.1 x ((mem_edgeEnds _ _).mpr (Finset.sdiff_subset hx.2))).2
      apply decide_eq_false
      intro heq
      rw [heq] at hxb
      exact hv (hxρ.2.symm.trans hxb.symm)
  have harc_end := isArc_rotationBatch hrbC hvC hEC₀ hdisjUC (fun x => decide (B.bundleOf x = b)) harc₀
  have hEC' : E ⊆ C'.E := by
    intro e he
    have heC0 : e ∈ (coreGraph cs.G cs.lsf).E := hEC₀ he
    have heC0' : e ∈ ((coreGraph cs.G cs.lsf).applyBatch UC).E := by
      have hgo : ∀ (G : MGraph) (W : List Update), e ∈ G.E → e ∉ batchDeletes W → e ∈ (G.applyBatch W).E := by
        intro G W
        induction W generalizing G with
        | nil => intro h _; exact h
        | cons u W ih =>
          intro hG hnd
          have hnd' : e ∉ batchDeletes W := fun hW => by
            obtain ⟨w, hw, rfl⟩ := (mem_batchDeletes_iff W e).mp hW
            exact hnd ((mem_batchDeletes_iff (u :: W) e).mpr ⟨.delete e, List.mem_cons_of_mem _ hw, rfl⟩)
          apply ih (G.applyUpdate u) _ hnd'
          cases u with
          | insert f a b => exact Finset.mem_insert_of_mem hG
          | delete f =>
            have hne : e ≠ f := fun hef => by
              subst hef
              exact hnd ((mem_batchDeletes_iff (.delete e :: W) e).mpr ⟨.delete e, List.mem_cons_self, rfl⟩)
            exact Finset.mem_erase.mpr ⟨hne, hG⟩
          | split => exact hG
      exact hgo _ UC heC0 (Finset.disjoint_left.mp hdisjUC he)
    exact hgeC.2.1.symm ▸ heC0'
  have hRsub : finalRootsOf B E src' b ⊆ cs'.RF.R := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have hxE : x.1 ∈ E := (Finset.mem_filter.mp hx).2
    have hval := coreGraph_isValid hI'.hG_val hRF' x.1 (hEC' hxE)
    rcases x with ⟨e, side⟩
    cases side
    · exact hval.2
    · exact hval.1
  have hmem_xs : ∀ v x, x ∈ (cord v).filter (fun y => decide (y.1 ∈ E)) ↔ x.1 ∈ E ∧ src' x = v := by
    intro v x
    rw [← hcord, List.mem_filter, σ_c.mem_order, decide_eq_true_eq]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hEC' h.1, h.2⟩, h.1⟩⟩
  have hcyc : ∀ v,
      (v ∉ finalRootsOf B E src' b ∧
        cycRuns (fun x => decide (B.bundleOf x = b)) ((cord v).filter fun x => decide (x.1 ∈ E)) = []) ∨
      (v ∈ finalRootsOf B E src' b ∧
        ∃ r, cycRuns (fun x => decide (B.bundleOf x = b)) ((cord v).filter fun x => decide (x.1 ∈ E)) = [r] ∧
          r.toFinset = (survivingEnds B E b).filter fun x => src' x = v) := by
    intro v
    have hnd : ((cord v).filter fun x => decide (x.1 ∈ E)).Nodup := by
      rw [← hcord]; exact (σ_c.nodup v).filter _
    have ha : IsArc (fun x => decide (B.bundleOf x = b)) ((cord v).filter fun x => decide (x.1 ∈ E)) := by
      rw [← hcord]; exact harc_end v
    rcases cycRuns_eq_of_isArc hnd ha with ⟨hfalse, hnil⟩ | ⟨r, hsing, -, hrmem⟩
    · left
      refine ⟨?_, hnil⟩
      intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hxb, hxE⟩ := Finset.mem_filter.mp hx
      have hxb' := (BundleState.mem_ends B b x).mp hxb
      have hxin := (hmem_xs (src' x) x).mpr ⟨hxE, rfl⟩
      have hf := hfalse x hxin
      simp [hxb'.2] at hf
    · right
      have hrset : r.toFinset = (survivingEnds B E b).filter fun x => src' x = v := by
        ext x
        rw [List.mem_toFinset, hrmem, hmem_xs, Finset.mem_filter, survivingEnds, Finset.mem_filter,
          BundleState.mem_ends, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hxE, hxv⟩, hxb⟩
          exact ⟨⟨⟨Finset.sdiff_subset hxE, hxb⟩, hxE⟩, hxv⟩
        · rintro ⟨⟨⟨-, hxb⟩, hxE⟩, hxv⟩
          exact ⟨⟨hxE, hxv⟩, hxb⟩
      have hv : v ∈ finalRootsOf B E src' b := by
        have hne : r ≠ [] := (cycRuns_spec _ _ r (hsing ▸ List.mem_cons_self)).1
        have hx := List.head_mem hne
        have hxf : r.head hne ∈ (survivingEnds B E b).filter fun x => src' x = v := by
          rw [← hrset]; exact List.mem_toFinset.mpr hx
        exact Finset.mem_image.mpr ⟨_, (Finset.mem_filter.mp hxf).1, (Finset.mem_filter.mp hxf).2⟩
      exact ⟨hv, r, hsing, hrset⟩
  let pickRun : ℕ → List End := fun v =>
    if h : v ∈ finalRootsOf B E src' b then
      ((hcyc v).resolve_left fun h' => h'.1 h).2.choose
    else []
  have hraw_vr1_eq : rawBundleRunsOf cs'.RF.R cord E B b =
      ((finalRootsOf B E src' b).sort (· ≤ ·)).map fun v => (v, pickRun v) := by
    unfold rawBundleRunsOf
    rw [← finset_sort_filter_eq hRsub]
    apply flatMap_singleton_or_nil
    intro v _
    by_cases hv : v ∈ finalRootsOf B E src' b
    · simp only [decide_eq_true hv, ↓reduceIte]
      have hspec := ((hcyc v).resolve_left fun h' => h'.1 hv).2.choose_spec
      change (cycRuns (fun x => decide (B.bundleOf x = b)) ((cord v).filter fun x => decide (x.1 ∈ E))).map
        (fun r => (v, r)) = [(v, pickRun v)]
      rw [hspec.1]
      simp [pickRun, hv]
    · simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte]
      have hnil := ((hcyc v).resolve_right fun h' => hv h'.1).2
      rw [hnil]; rfl
  have hraw_fst : (rawBundleRunsOf cs'.RF.R cord E B b).map Prod.fst =
      (rawByRootVRuns B E src' b).map Prod.fst := by
    rw [hraw_vr1_eq, rawByRootVRuns, List.map_map, List.map_map]; rfl
  have hraw_len : (rawBundleRunsOf cs'.RF.R cord E B b).length =
      (rawByRootVRuns B E src' b).length := by
    have := congrArg List.length hraw_fst; simpa using this
  have hraw_el : ∀ i (h₁ : i < (rawBundleRunsOf cs'.RF.R cord E B b).length)
      (h₂ : i < (rawByRootVRuns B E src' b).length),
      (rawBundleRunsOf cs'.RF.R cord E B b)[i].2.toFinset = (rawByRootVRuns B E src' b)[i].2.toFinset ∧
      (rawBundleRunsOf cs'.RF.R cord E B b)[i].2.length = (rawByRootVRuns B E src' b)[i].2.length := by
    intro i h₁ h₂
    revert h₁
    rw [hraw_vr1_eq]
    intro h₁
    dsimp only [rawByRootVRuns] at h₂ ⊢
    rw [List.getElem_map, List.getElem_map]
    dsimp only
    set v := ((finalRootsOf B E src' b).sort (· ≤ ·))[i]'(by simpa using h₁)
    have hv : v ∈ finalRootsOf B E src' b :=
      (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem (by simpa using h₁))
    have hspec := ((hcyc v).resolve_left fun h' => h'.1 hv).2.choose_spec
    have hpick : pickRun v = ((hcyc v).resolve_left fun h' => h'.1 hv).2.choose :=
      dite_eq_left hv
    have hnd1 : (pickRun v).Nodup := by
      have hnd_all := cycRuns_flatten_nodup (fun x => decide (B.bundleOf x = b))
        ((by rw [← hcord]; exact (σ_c.nodup v).filter _ : ((cord v).filter fun x => decide (x.1 ∈ E)).Nodup))
      rw [hspec.1, List.flatten_singleton] at hnd_all
      rwa [hpick]
    have hnd2 : (((((survivingEnds B E b).filter fun x => src' x = v).image endKey).sort (· ≤ ·)).map endOfKey).Nodup := by
      refine (Finset.sort_nodup _ _).map_on fun a ha b' hb' heq => ?_
      rw [Finset.mem_sort, Finset.mem_image] at ha hb'
      obtain ⟨xa, _, rfl⟩ := ha; obtain ⟨xb, _, rfl⟩ := hb'
      rw [bundle_endOfKey_endKey, bundle_endOfKey_endKey] at heq
      rw [heq]
    have hset : (pickRun v).toFinset =
        (((((survivingEnds B E b).filter fun x => src' x = v).image endKey).sort (· ≤ ·)).map endOfKey).toFinset := by
      rw [hpick, hspec.2]
      ext x
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_sort, Finset.mem_image]
      constructor
      · intro hx
        exact ⟨endKey x, ⟨x, hx, rfl⟩, bundle_endOfKey_endKey x⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
        rw [bundle_endOfKey_endKey] at hxy
        exact hxy ▸ hy
    have hlen_eq : (pickRun v).length =
        (((((survivingEnds B E b).filter fun x => src' x = v).image endKey).sort (· ≤ ·)).map endOfKey).length := by
      rw [← List.toFinset_card_of_nodup hnd1, ← List.toFinset_card_of_nodup hnd2, hset]
    exact ⟨hset, hlen_eq⟩
  exact promoteLargestRun_congr hraw_fst hraw_el

/-- Main equivalence theorem: under `BundleStepReady`, `bundleRunsStep` emits the exact same
update batch `UB`, vertex set, edge set, and `bundleOf` as `byRootSplitFold` on the exact list
`exactSplitCands` of splitting bundles (`2 ≤ (finalRootsOf B E src' b).card`). -/
theorem bundleRunsStep_eq_byRoot {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    let cs' := compLSFBatch cs U
    let E := B.edges \ batchDeletes U
    let src' := (coreGraph cs'.G cs'.lsf).src
    let dels := ((B.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete
    let res := bundleRunsStep cs B k ord' U
    let fast := byRootSplitFold B E src' dels (exactSplitCands B E src')
    res.1 = fast.1 ∧
    res.2.vertices = fast.2.vertices ∧
    res.2.edges = fast.2.edges ∧
    res.2.bundleOf = fast.2.bundleOf := by
  intro cs' E src' dels res fast
  let cord := coreOrderOf cs' ord'
  let plan₁ := (B.vertices.sort (· ≤ ·)).map fun b => (b, bundleRunsOf cs'.RF.R cord E B b)
  let plan₂ := (B.vertices.sort (· ≤ ·)).map fun b => (b, byRootVRuns B E src' b)
  have hfold_eq : ∀ (bs : List ℕ) (s : List Update × BundleState),
      (∀ b ∈ bs, b ∈ B.vertices) →
      (bs.map fun b => (b, bundleRunsOf cs'.RF.R cord E B b)).foldl runsFoldStep s =
      (bs.map fun b => (b, byRootVRuns B E src' b)).foldl runsFoldStep s := by
    intro bs
    induction bs with
    | nil => intro _ _; rfl
    | cons b rest ih =>
      intro s hmem
      simp only [List.map_cons, List.foldl_cons]
      have hbr := bundleRunsOf_eq_byRootVRuns h (hmem b List.mem_cons_self)
      rw [runsFoldStep_congr_vruns s b hbr.1 hbr.2]
      exact ih _ fun c hc => hmem c (List.mem_cons_of_mem _ hc)
  have h1 : res = plan₂.foldl runsFoldStep (dels, { B with edges := E }) :=
    hfold_eq (B.vertices.sort (· ≤ ·)) (dels, { B with edges := E })
      (fun b hb => (Finset.mem_sort (· ≤ ·)).mp hb)
  have h2 := foldl_runsFoldStep_filter_splits plan₂ (dels, { B with edges := E })
  have hfilt : plan₂.filter (fun p => decide (2 ≤ p.2.length)) =
      (exactSplitCands B E src').map fun b => (b, byRootVRuns B E src' b) := by
    dsimp only [plan₂, exactSplitCands]
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro b _
    simp [byRootVRuns, rawByRootVRuns, promoteLargestRun_length, Finset.length_sort]
  rw [hfilt] at h2
  rw [h1]
  exact h2

/-- Exact characterization of `(bundleRunsStep cs B k ord' U).2.parent` for every `c : ℕ`:
nonempty bundles have parent equal to the final core vertex of any of their ends, empty bundles
keep their old parent `B.parent c`, and names outside `B'.vertices` keep `B.parent c`. -/
theorem bundleRunsStep_parent_eq {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    let cs' := compLSFBatch cs U
    let src' := (coreGraph cs'.G cs'.lsf).src
    let B' := (bundleRunsStep cs B k ord' U).2
    (∀ c ∈ B'.vertices, ∀ x ∈ B'.ends c, B'.parent c = src' x) ∧
    (∀ c ∈ B'.vertices, B'.ends c = ∅ → c ∈ B.vertices ∧ B'.parent c = B.parent c) ∧
    (∀ c ∉ B'.vertices, B'.parent c = B.parent c) := by
  obtain ⟨⟨UBw, Bw⟩, hSw, hLw⟩ := bundleStepSpec_exists h
  obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, -, hσ, -, hU, hB⟩ := h
  have hI' := compLSFBatch_inv hI hU
  let σ' : Rotation (compLSFBatch cs U).G := (compLSFBatch_G cs U).symm ▸ σ
  have hσ' : σ'.order = ord' := (cast_order' _ σ).trans hσ
  have hpar0 : ∀ b ∈ B.vertices, B.parent b ∈ (compLSFBatch cs U).RF.R :=
    fun b hb => (compLSFBatch_decremental hI hU).2 (hB.2.1 b hb)
  have core := bundleRunsStep_core (k := k) (fun x hx => (hB.2.2.1 x hx).1)
    (fun b hb => (hB.2.2.2 b hb).1) hpar0 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    (hSw.1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ') hSw.2.1 hSw.2.2.1 hSw.2.2.2.1 hLw.2.2.2.1
  obtain ⟨hpart, -, hpar3, hparOut, -⟩ := core
  refine ⟨?_, ?_, hparOut⟩
  · intro c hc x hx
    obtain ⟨hxE, hxc⟩ := (BundleState.mem_ends _ _ _).mp hx
    have h22 := (hpart.2.2.1 x ((mem_edgeEnds _ _).mpr hxE)).2
    rwa [hxc] at h22
  · intro c hc hempty
    rcases hpar3 c hc with ⟨x, hx, -⟩ | ⟨hcB, hp⟩
    · rw [hempty] at hx; simp at hx
    · exact ⟨hcB, hp⟩

private lemma finset_range_sup_add_one {m : ℕ} (hm : 1 ≤ m) :
    (Finset.range m).sup id + 1 = m := by
  have hle : (Finset.range m).sup id ≤ m - 1 := by
    apply Finset.sup_le
    intro x hx
    have hlt := Finset.mem_range.mp hx
    change x ≤ m - 1
    omega
  have hge : m - 1 ≤ (Finset.range m).sup id :=
    Finset.le_sup (f := id) (Finset.mem_range.mpr (by omega))
  omega

/-- If `B.vertices = Finset.range n`, then after `bundleRunsStep` the vertices remain a contiguous
range `Finset.range (n + batchSplitCount UB)`. -/
theorem bundleRunsStep_vertices_range {cs : CompLSFState} {B : BundleState} {k n : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U)
    (hV : B.vertices = Finset.range n) :
    let res := bundleRunsStep cs B k ord' U
    res.2.vertices = Finset.range (n + batchSplitCount res.1) := by
  intro res
  have hcard : res.2.vertices.card = n + batchSplitCount res.1 := by
    have hspec := (bundleRunsStep_spec h).1.2.2.2.2.2.2
    rw [hV, Finset.card_range] at hspec
    exact hspec
  cases n with
  | zero =>
    have hem : B.vertices = ∅ := by simpa using hV
    have hsort : B.vertices.sort (· ≤ ·) = [] := by rw [hem]; simp
    have hV' : res.2.vertices = ∅ := by
      change ((((B.vertices.sort (· ≤ ·)).map _).foldl runsFoldStep _).2.vertices) = ∅
      rw [hsort]
      simpa using hem
    have h0 : batchSplitCount res.1 = 0 := by
      rw [hV', Finset.card_empty] at hcard; omega
    rw [hV', h0]; simp
  | succ m =>
    have hfold : ∀ (plan : List (ℕ × List (ℕ × List End))) (s : List Update × BundleState) (r : ℕ),
        1 ≤ r → s.2.vertices = Finset.range r →
        ∃ r', (plan.foldl runsFoldStep s).2.vertices = Finset.range r' := by
      intro plan
      induction plan with
      | nil => intro s r _ hr; exact ⟨r, hr⟩
      | cons p rest ih =>
        intro s r hr hsr
        obtain ⟨b, vruns⟩ := p
        have hnext : s.2.vertices.sup id + 1 = r := by
          rw [hsr]; exact finset_range_sup_add_one hr
        have hstepV : (runsFoldStep s (b, vruns)).2.vertices =
            Finset.range (r + (vruns.drop 1).length) := by
          ext c
          rw [runsFoldStep_vertices, hnext, hsr, Finset.mem_range, Finset.mem_range]
          constructor
          · rintro (hc | ⟨i, hi, rfl⟩) <;> omega
          · intro hc
            by_cases hcr : c < r
            · exact Or.inl hcr
            · exact Or.inr ⟨c - r, by omega, by omega⟩
        exact ih (runsFoldStep s (b, vruns)) (r + (vruns.drop 1).length) (by omega) hstepV
    obtain ⟨r', hr'⟩ := hfold _
      ((((B.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete),
        { B with edges := B.edges \ batchDeletes U })
      (m + 1) (Nat.succ_pos m) hV
    have hreq : r' = m + 1 + batchSplitCount res.1 := by
      have hc := congrArg Finset.card hr'
      rw [Finset.card_range] at hc
      exact hc.symm.trans hcard
    exact hr'.trans (congrArg Finset.range hreq)

end

end MinCostFlow.SparseCore.Program
