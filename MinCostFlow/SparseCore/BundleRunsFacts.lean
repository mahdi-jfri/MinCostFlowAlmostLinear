module

public import MinCostFlow.SparseCore.BundleRunsFold

/-!
# Facts used by the proof of the canonical bundle step

Three groups of facts, each used by `bundleRunsStep_core`.

* Runs: two runs of one list that share an element are equal (`runs_eq_of_mem`), and the runs
  that `bundleRunsOf` lists for a bundle cover its kept ends once each.
* Deletions: deleting a list of distinct edges is valid and removes exactly these edges
  (`applyBatch_deletes`).
* Going back: after a valid batch of deletions and splits, each vertex comes from a vertex of the
  old graph (`delSplit_back`). The map is the identity on old vertices and sends the new end of
  every live edge to its old end. So a bundle after such a batch holds ends of one old bundle.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- Two lists of a family with no repeated element in its flattening that share an element are
equal. -/
theorem runs_eq_of_mem {α : Type*} {L : List (List α)} (hn : L.flatten.Nodup) {r r' : List α}
    (hr : r ∈ L) (hr' : r' ∈ L) {x : α} (hx : x ∈ r) (hx' : x ∈ r') : r = r' := by
  induction L with
  | nil => simp at hr
  | cons a L ih =>
    rw [List.flatten_cons] at hn
    have hd := List.nodup_append.mp hn
    rcases List.mem_cons.mp hr with h1 | h1
    · rcases List.mem_cons.mp hr' with h2 | h2
      · exact h1.trans h2.symm
      · subst h1
        exact absurd rfl (hd.2.2 x hx x (List.mem_flatten.mpr ⟨r', h2, hx'⟩))
    · rcases List.mem_cons.mp hr' with h2 | h2
      · subst h2
        exact absurd rfl (hd.2.2 x hx' x (List.mem_flatten.mpr ⟨r, h1, hx⟩))
      · exact ih hd.2.1 h1 h2

private theorem perm_cons_eraseIdx {α : Type*} :
    ∀ {L : List α} {j : ℕ} (hj : j < L.length), (L[j] :: L.eraseIdx j).Perm L
  | [], _, hj => by simp at hj
  | _ :: _, 0, _ => List.Perm.refl _
  | a :: b :: rest, j + 1, hj => by
    have hj' : j < (b :: rest).length := by simp only [List.length_cons] at hj ⊢; omega
    have ih := perm_cons_eraseIdx (L := b :: rest) hj'
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
    exact (List.Perm.swap a _ _).trans (ih.cons a)

theorem maxRunIdx_lt : ∀ {L : List (ℕ × List End)}, L ≠ [] → maxRunIdx L < L.length
  | [], h => absurd rfl h
  | [_], _ => by simp [maxRunIdx]
  | a :: b :: rest, _ => by
    have ih := maxRunIdx_lt (L := b :: rest) (by simp)
    simp only [maxRunIdx]
    split_ifs
    · simp only [List.length_cons] at ih ⊢; omega
    · simp

theorem maxRunIdx_spec : ∀ {L : List (ℕ × List End)} (hne : L ≠ []),
    (∀ i (hi : i < L.length), L[i].2.length ≤ (L[maxRunIdx L]'(maxRunIdx_lt hne)).2.length) ∧
    (∀ i (hi : i < maxRunIdx L), (L[i]'(Nat.lt_trans hi (maxRunIdx_lt hne))).2.length <
      (L[maxRunIdx L]'(maxRunIdx_lt hne)).2.length)
  | [], h => absurd rfl h
  | [a], _ => ⟨fun i hi => by
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0; simp [maxRunIdx],
      fun i hi => by simp [maxRunIdx] at hi⟩
  | a :: b :: rest, _ => by
    have hne' : b :: rest ≠ [] := by simp
    have ih := maxRunIdx_spec hne'
    have hlt' := maxRunIdx_lt hne'
    have hget : (b :: rest).getD (maxRunIdx (b :: rest)) (0, []) = (b :: rest)[maxRunIdx (b :: rest)]'hlt' := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']; rfl
    by_cases hgt : ((b :: rest)[maxRunIdx (b :: rest)]'hlt').2.length > a.2.length
    · have hidx : maxRunIdx (a :: b :: rest) = maxRunIdx (b :: rest) + 1 := by
        rw [maxRunIdx, hget]; exact ite_eq_left hgt
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · simp only [hidx]
        cases i with
        | zero => simp only [List.getElem_cons_zero, List.getElem_cons_succ]; omega
        | succ i' =>
          have hi' : i' < (b :: rest).length := by simp only [List.length_cons] at hi ⊢; omega
          exact ih.1 i' hi'
      · simp only [hidx] at hi ⊢
        cases i with
        | zero => simpa using hgt
        | succ i' => exact ih.2 i' (by omega)
    · have hidx : maxRunIdx (a :: b :: rest) = 0 := by
        rw [maxRunIdx, hget]; exact ite_eq_right hgt
      refine ⟨fun i hi => ?_, fun i hi => by omega⟩
      simp only [hidx]
      cases i with
      | zero => simp
      | succ i' =>
        have hi' : i' < (b :: rest).length := by simp only [List.length_cons] at hi ⊢; omega
        have h1 := ih.1 i' hi'
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        omega

theorem promoteLargestRun_perm (L : List (ℕ × List End)) : (promoteLargestRun L).Perm L := by
  cases L with
  | nil => exact List.Perm.refl []
  | cons a rest =>
    have hlt := maxRunIdx_lt (L := a :: rest) (by simp)
    unfold promoteLargestRun
    dsimp only
    rw [show (a :: rest).getD (maxRunIdx (a :: rest)) (0, []) = (a :: rest)[maxRunIdx (a :: rest)]'hlt by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl]
    exact perm_cons_eraseIdx hlt

theorem promoteLargestRun_length (L : List (ℕ × List End)) :
    (promoteLargestRun L).length = L.length :=
  (promoteLargestRun_perm L).length_eq

theorem promoteLargestRun_eq_nil_iff {L : List (ℕ × List End)} :
    promoteLargestRun L = [] ↔ L = [] :=
  ⟨fun h => List.eq_nil_of_length_eq_zero (by rw [← promoteLargestRun_length L, h]; rfl),
   fun h => by subst h; rfl⟩

theorem maxRunIdx_congr : ∀ {L₁ L₂ : List (ℕ × List End)},
    L₁.length = L₂.length →
    (∀ i (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i].2.length = L₂[i].2.length) →
    maxRunIdx L₁ = maxRunIdx L₂
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | [_], [_], _, _ => rfl
  | [_], _ :: _ :: _, h, _ => by simp at h
  | _ :: _ :: _, [_], h, _ => by simp at h
  | a₁ :: b₁ :: r₁, a₂ :: b₂ :: r₂, hlen, hel => by
    have htl_len : (b₁ :: r₁).length = (b₂ :: r₂).length := by
      simp only [List.length_cons] at hlen ⊢; omega
    have htl_el : ∀ i (h₁ : i < (b₁ :: r₁).length) (h₂ : i < (b₂ :: r₂).length),
        (b₁ :: r₁)[i].2.length = (b₂ :: r₂)[i].2.length := fun i h₁ h₂ =>
      hel (i + 1) (by simp only [List.length_cons] at h₁ ⊢; omega)
        (by simp only [List.length_cons] at h₂ ⊢; omega)
    have hj := maxRunIdx_congr htl_len htl_el
    have hlt1 := maxRunIdx_lt (L := b₁ :: r₁) (by simp)
    have hlt2 : maxRunIdx (b₁ :: r₁) < (b₂ :: r₂).length := htl_len ▸ hlt1
    have ha : a₁.2.length = a₂.2.length := hel 0 (by simp) (by simp)
    have hmid : ((b₁ :: r₁).getD (maxRunIdx (b₁ :: r₁)) (0, [])).2.length =
        ((b₂ :: r₂).getD (maxRunIdx (b₂ :: r₂)) (0, [])).2.length := by
      rw [← hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2]
      exact htl_el _ hlt1 hlt2
    simp only [maxRunIdx, ← hj, hmid, ha]

theorem promoteLargestRun_congr {L₁ L₂ : List (ℕ × List End)}
    (hfst : L₁.map Prod.fst = L₂.map Prod.fst)
    (hel : ∀ i (h₁ : i < L₁.length) (h₂ : i < L₂.length),
      L₁[i].2.toFinset = L₂[i].2.toFinset ∧ L₁[i].2.length = L₂[i].2.length) :
    (promoteLargestRun L₁).map Prod.fst = (promoteLargestRun L₂).map Prod.fst ∧
    ∀ i (h₁ : i < (promoteLargestRun L₁).length) (h₂ : i < (promoteLargestRun L₂).length),
      (promoteLargestRun L₁)[i].2.toFinset = (promoteLargestRun L₂)[i].2.toFinset := by
  have hlen : L₁.length = L₂.length := by
    have := congrArg List.length hfst; simpa using this
  have hidx_eq : maxRunIdx L₁ = maxRunIdx L₂ :=
    maxRunIdx_congr hlen fun i h₁ h₂ => (hel i h₁ h₂).2
  cases L₁ with
  | nil =>
    have hL2 : L₂ = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst hL2; simp [promoteLargestRun]
  | cons a₁ r₁ =>
    cases L₂ with
    | nil => simp at hlen
    | cons a₂ r₂ =>
      have hlt1 := maxRunIdx_lt (L := a₁ :: r₁) (by simp)
      have hlt2 : maxRunIdx (a₁ :: r₁) < (a₂ :: r₂).length := hlen ▸ hlt1
      have hget1 : (a₁ :: r₁).getD (maxRunIdx (a₁ :: r₁)) (0, []) = (a₁ :: r₁)[maxRunIdx (a₁ :: r₁)]'hlt1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt1]; rfl
      have hget2 : (a₂ :: r₂).getD (maxRunIdx (a₁ :: r₁)) (0, []) = (a₂ :: r₂)[maxRunIdx (a₁ :: r₁)]'hlt2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2]; rfl
      have hfst_i : ∀ i (h₁ : i < (a₁ :: r₁).length) (h₂ : i < (a₂ :: r₂).length),
          (a₁ :: r₁)[i].1 = (a₂ :: r₂)[i].1 := fun i h₁ h₂ => by
        have h := congrArg (fun l => l[i]?) hfst
        rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at h
        simpa using h
      refine ⟨?_, ?_⟩
      · simp only [promoteLargestRun, ← hidx_eq, hget1, hget2, List.map_cons]
        congr 1
        · exact hfst_i _ hlt1 hlt2
        · rw [← List.eraseIdx_map, ← List.eraseIdx_map, hfst]
      · intro i h₁ h₂
        have h1' : i < (a₁ :: r₁).length := by rwa [promoteLargestRun_length] at h₁
        have h2' : i < (a₂ :: r₂).length := by rwa [promoteLargestRun_length] at h₂
        simp only [promoteLargestRun, ← hidx_eq, hget1, hget2]
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero]
          exact (hel _ hlt1 hlt2).1
        | succ i' =>
          simp only [List.getElem_cons_succ, List.getElem_eraseIdx]
          split_ifs with hlt
          · exact (hel i' (by omega) (by omega)).1
          · exact (hel (i' + 1) (by omega) (by omega)).1

theorem mem_bundleRunsOf {R : Finset ℕ} {cord : ℕ → List End} {E : Finset ℕ} {B : BundleState}
    {b : ℕ} {vr : ℕ × List End} (h : vr ∈ bundleRunsOf R cord E B b) :
    vr.1 ∈ R ∧ vr.2 ∈ cycRuns (fun x => decide (B.bundleOf x = b))
      ((cord vr.1).filter fun x => decide (x.1 ∈ E)) := by
  have hraw : vr ∈ rawBundleRunsOf R cord E B b :=
    (promoteLargestRun_perm _).subset h
  simp only [rawBundleRunsOf, List.mem_flatMap, List.mem_map] at hraw
  obtain ⟨v, hv, r, hr, rfl⟩ := hraw
  exact ⟨(Finset.mem_sort _).mp hv, hr⟩

private theorem rawBundleRunsOf_snd (R : Finset ℕ) (cord : ℕ → List End) (E : Finset ℕ)
    (B : BundleState) (b : ℕ) :
    ((rawBundleRunsOf R cord E B b).map Prod.snd).flatten =
      (R.sort (· ≤ ·)).flatMap fun v => (cycRuns (fun x => decide (B.bundleOf x = b))
        ((cord v).filter fun x => decide (x.1 ∈ E))).flatten := by
  simp only [rawBundleRunsOf, List.map_flatMap, List.map_map, Function.comp_def, List.map_id']
  induction R.sort (· ≤ ·) with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatten_append, ih]

private theorem bundleRunsOf_snd_perm (R : Finset ℕ) (cord : ℕ → List End) (E : Finset ℕ)
    (B : BundleState) (b : ℕ) :
    ((bundleRunsOf R cord E B b).map Prod.snd).flatten.Perm
      ((rawBundleRunsOf R cord E B b).map Prod.snd).flatten :=
  ((promoteLargestRun_perm _).map Prod.snd).flatten

theorem mem_bundleRunsOf_flatten (R : Finset ℕ) (cord : ℕ → List End) (E : Finset ℕ)
    (B : BundleState) (b : ℕ) (x : End) :
    x ∈ ((bundleRunsOf R cord E B b).map Prod.snd).flatten ↔
      ∃ v ∈ R, x ∈ cord v ∧ x.1 ∈ E ∧ B.bundleOf x = b := by
  rw [(bundleRunsOf_snd_perm R cord E B b).mem_iff, rawBundleRunsOf_snd, List.mem_flatMap]
  simp only [mem_cycRuns_flatten, List.mem_filter, decide_eq_true_eq, Finset.mem_sort]
  constructor
  · rintro ⟨v, hv, ⟨hx, hE⟩, hb⟩
    exact ⟨v, hv, hx, hE, hb⟩
  · rintro ⟨v, hv, hx, hE, hb⟩
    exact ⟨v, hv, ⟨hx, hE⟩, hb⟩

/-- If each end lies in the order of at most one vertex, the runs of a bundle list each end
once. -/
theorem bundleRunsOf_nodup (R : Finset ℕ) (cord : ℕ → List End) (E : Finset ℕ)
    (B : BundleState) (b : ℕ) (hn : ∀ v, (cord v).Nodup)
    (hdis : ∀ v v' x, x ∈ cord v → x ∈ cord v' → v = v') :
    ((bundleRunsOf R cord E B b).map Prod.snd).flatten.Nodup := by
  rw [(bundleRunsOf_snd_perm R cord E B b).nodup_iff, rawBundleRunsOf_snd, List.nodup_flatMap]
  refine ⟨fun v _ => cycRuns_flatten_nodup _ ((hn v).filter _), ?_⟩
  refine (Finset.sort_nodup R (· ≤ ·)).imp fun {v v'} hne => ?_
  intro x hx hx'
  rw [mem_cycRuns_flatten, List.mem_filter] at hx hx'
  exact hne (hdis v v' x hx.1.1 hx'.1.1)

/-- Deleting distinct edges of a graph is valid and removes exactly these edges. -/
theorem applyBatch_deletes (G : MGraph) (L : List ℕ) (hnd : L.Nodup) (hsub : ∀ e ∈ L, e ∈ G.E) :
    G.BatchIsValid (L.map Update.delete) ∧
      G.applyBatch (L.map Update.delete) = { G with E := G.E \ L.toFinset } := by
  induction L generalizing G with
  | nil => exact ⟨trivial, by simp [MGraph.applyBatch]⟩
  | cons e L ih =>
    have he : e ∈ G.E := hsub e List.mem_cons_self
    have heL : e ∉ L := (List.nodup_cons.mp hnd).1
    obtain ⟨hv, hg⟩ := ih { G with E := G.E.erase e } (List.nodup_cons.mp hnd).2
      (fun f hf => Finset.mem_erase.mpr ⟨fun h => heL (h ▸ hf), hsub f (List.mem_cons_of_mem _ hf)⟩)
    refine ⟨⟨he, hv⟩, ?_⟩
    change (G.applyUpdate (.delete e)).applyBatch (L.map Update.delete) = _
    change ({ G with E := G.E.erase e } : MGraph).applyBatch (L.map Update.delete) = _
    rw [hg]
    congr 1
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
    tauto

/-- After a valid batch of deletions and splits, every vertex comes from an old vertex: there is a
map that fixes the old vertices and sends the new ends of every live edge to the old ends. -/
theorem delSplit_back {G : MGraph} {U : List Update} (hv : G.BatchIsValid U)
    (ht : ∀ op ∈ U, isDelOrSplit op) (hends : ∀ e ∈ G.E, G.tail e ∈ G.V ∧ G.head e ∈ G.V) :
    ∃ o : ℕ → ℕ, (∀ v ∈ G.V, o v = v) ∧
      (∀ e ∈ (G.applyBatch U).E,
        o ((G.applyBatch U).tail e) = G.tail e ∧ o ((G.applyBatch U).head e) = G.head e) ∧
      G.V ⊆ (G.applyBatch U).V ∧ (G.applyBatch U).E ⊆ G.E := by
  induction U generalizing G with
  | nil => exact ⟨id, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, Finset.Subset.rfl, Finset.Subset.rfl⟩
  | cons u U ih =>
    obtain ⟨hu, hv'⟩ := hv
    -- One step, and the facts that let the induction go on.
    have step : ∃ o₁ : ℕ → ℕ, (∀ v ∈ G.V, o₁ v = v) ∧
        (∀ e ∈ (G.applyUpdate u).E, o₁ ((G.applyUpdate u).tail e) = G.tail e ∧
          o₁ ((G.applyUpdate u).head e) = G.head e) ∧
        G.V ⊆ (G.applyUpdate u).V ∧ (G.applyUpdate u).E ⊆ G.E ∧
        ∀ e ∈ (G.applyUpdate u).E, (G.applyUpdate u).tail e ∈ (G.applyUpdate u).V ∧
          (G.applyUpdate u).head e ∈ (G.applyUpdate u).V := by
      cases u with
      | insert => exact (ht _ List.mem_cons_self).elim
      | delete d =>
        refine ⟨id, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, Finset.Subset.rfl,
          Finset.erase_subset _ _, fun e he => hends e (Finset.mem_of_mem_erase he)⟩
      | split v v' St Sh =>
        obtain ⟨hvV, hv'V, -, -⟩ := hu
        refine ⟨fun w => if w = v' then v else w, fun w hw => ?_, fun e he => ?_,
          Finset.subset_insert _ _, Finset.Subset.rfl, fun e he => ?_⟩
        · have : w ≠ v' := fun h => hv'V (h ▸ hw)
          simp [this]
        · obtain ⟨htV, hhV⟩ := hends e he
          have ht' : G.tail e ≠ v' := fun h => hv'V (h ▸ htV)
          have hh' : G.head e ≠ v' := fun h => hv'V (h ▸ hhV)
          change (if (if e ∈ St ∧ G.tail e = v then v' else G.tail e) = v' then v else
              (if e ∈ St ∧ G.tail e = v then v' else G.tail e)) = G.tail e ∧
            (if (if e ∈ Sh ∧ G.head e = v then v' else G.head e) = v' then v else
              (if e ∈ Sh ∧ G.head e = v then v' else G.head e)) = G.head e
          constructor
          · by_cases hm : e ∈ St ∧ G.tail e = v
            · simp [hm]
            · simp [hm, ht']
          · by_cases hm : e ∈ Sh ∧ G.head e = v
            · simp [hm]
            · simp [hm, hh']
        · obtain ⟨htV, hhV⟩ := hends e he
          change (if e ∈ St ∧ G.tail e = v then v' else G.tail e) ∈ insert v' G.V ∧
            (if e ∈ Sh ∧ G.head e = v then v' else G.head e) ∈ insert v' G.V
          constructor
          · split_ifs
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem htV
          · split_ifs
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem hhV
    obtain ⟨o₁, h1, h2, h3, h4, h5⟩ := step
    obtain ⟨o', g1, g2, g3, g4⟩ := ih hv' (fun op hop => ht op (List.mem_cons_of_mem _ hop)) h5
    refine ⟨o₁ ∘ o', fun w hw => ?_, fun e he => ?_, h3.trans g3, g4.trans h4⟩
    · change o₁ (o' w) = w
      rw [g1 w (h3 hw), h1 w hw]
    · obtain ⟨t1, t2⟩ := g2 e he
      obtain ⟨s1, s2⟩ := h2 e (g4 he)
      exact ⟨(congrArg o₁ t1).trans s1, (congrArg o₁ t2).trans s2⟩

end MinCostFlow.SparseCore
