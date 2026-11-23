module

public import MinCostFlow.HierPaths.BuildChildLoad
import Mathlib.Data.List.GetD

/-!
# The child construction `lemma_3` at one group

After the `T = 49 L' + 1` rounds of the game every child `c` has saved a set `S_c` with at least
half of the child and expansion at least `1/P` in its game graph (`gameRun_saved`). One more
router call routes the rest of each child into its saved set (`injPairs`). The child host is the
game graph plus these injection edges (`childEdges`). `lemma_3` proves:
- the child host has expansion at least `1/(2P)` (the injection lemma, `childGraph_expansion`);
- every vertex of it has degree at most `T + 1` (`childGraph_deg_le`);
- every edge of it has a walk in `G[X]` between its ends, shifted to terminal numbers, with at
  most `d` edges;
- the walks of all children have load at most `(T + 1) · R`: each of the `T + 1` calls adds
  at most `R`, since its walks are shortcut to walks that repeat no edge.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The ends of a list of edges from `A` to a disjoint set `B`, with distinct first ends and
distinct second ends, are all distinct. -/
theorem flatMap_ends_nodup {A B : Finset ℕ} (hAB : Disjoint A B) :
    ∀ (F : List (ℕ × ℕ)), (F.map Prod.fst).Nodup → (F.map Prod.snd).Nodup →
      (∀ e ∈ F, e.1 ∈ A ∧ e.2 ∈ B) → (F.flatMap fun e => [e.1, e.2]).Nodup := by
  intro F
  induction F with
  | nil => simp
  | cons a F ih =>
    intro h1 h2 h3
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h1 h2
    have ha := h3 a List.mem_cons_self
    have hF := fun e he => h3 e (List.mem_cons_of_mem _ he)
    have hne : ∀ x, x ∈ A → x ∈ B → False := fun x hA hB => Finset.disjoint_left.mp hAB hA hB
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and]
    refine ⟨⟨fun h => hne _ ha.1 (h ▸ ha.2), ?_⟩, ?_, ih h1.2 h2.2 hF⟩
    · intro e he
      refine ⟨fun h => h1.1 ⟨e, he, h.symm⟩, fun h => ?_, by simp⟩
      exact hne _ ha.1 (h ▸ (hF e he).2)
    · intro e he
      refine ⟨fun h => hne _ (h ▸ (hF e he).1) ha.2, fun h => h2.1 ⟨e, he, h.symm⟩, by simp⟩

/-- **A shifted full matching, shifted back.** Let `Mh` go from `o + A` to `o + B`, with distinct
first ends, distinct second ends and `|A|` edges. Shifted back, it goes from `A` to `B`, its first
ends cover `A`, and its ends are distinct. -/
theorem unshift_props {o : ℕ} {A B : Finset ℕ} (hAB : Disjoint A B) {Mh : List (ℕ × ℕ)}
    (hends : ∀ e ∈ Mh, e.1 ∈ shiftSet o A ∧ e.2 ∈ shiftSet o B)
    (hnd1 : (Mh.map Prod.fst).Nodup) (hnd2 : (Mh.map Prod.snd).Nodup)
    (hlen : Mh.length = A.card) :
    (∀ e ∈ unshiftEdges o Mh, e.1 ∈ A ∧ e.2 ∈ B) ∧
      ((unshiftEdges o Mh).map Prod.snd).Nodup ∧
      (∀ a ∈ A, ∃ e ∈ unshiftEdges o Mh, e.1 = a) ∧
      ((unshiftEdges o Mh).flatMap fun e => [e.1, e.2]).Nodup := by
  have hge : ∀ e ∈ Mh, o ≤ e.1 ∧ o ≤ e.2 := fun e he =>
    ⟨(mem_shiftSet_iff.mp (hends e he).1).1, (mem_shiftSet_iff.mp (hends e he).2).1⟩
  have hloc : ∀ e ∈ unshiftEdges o Mh, e.1 ∈ A ∧ e.2 ∈ B := by
    intro e he
    unfold unshiftEdges at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact ⟨(mem_shiftSet_iff.mp (hends f hf).1).2, (mem_shiftSet_iff.mp (hends f hf).2).2⟩
  have hinj : ∀ x y : ℕ, o ≤ x → o ≤ y → x - o = y - o → x = y := by
    intro x y hx hy h
    omega
  have hnd1' : ((unshiftEdges o Mh).map Prod.fst).Nodup := by
    unfold unshiftEdges
    rw [List.map_map]
    have : ((Prod.fst ∘ fun e : ℕ × ℕ => (e.1 - o, e.2 - o))) = (fun x => x - o) ∘ Prod.fst := rfl
    rw [this, ← List.map_map]
    apply List.Nodup.map_on _ hnd1
    intro x hx y hy h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
    exact hinj _ _ (hge e he).1 (hge f hf).1 h
  have hnd2' : ((unshiftEdges o Mh).map Prod.snd).Nodup := by
    unfold unshiftEdges
    rw [List.map_map]
    have : ((Prod.snd ∘ fun e : ℕ × ℕ => (e.1 - o, e.2 - o))) = (fun x => x - o) ∘ Prod.snd := rfl
    rw [this, ← List.map_map]
    apply List.Nodup.map_on _ hnd2
    intro x hx y hy h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
    exact hinj _ _ (hge e he).2 (hge f hf).2 h
  have hfst : ((unshiftEdges o Mh).map Prod.fst).toFinset = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact (hloc e he).1
    · rw [List.toFinset_card_of_nodup hnd1', List.length_map]
      unfold unshiftEdges
      rw [List.length_map, hlen]
  refine ⟨hloc, hnd2', fun a ha => ?_, flatMap_ends_nodup hAB _ hnd1' hnd2' hloc⟩
  rw [← hfst] at ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact ⟨e, he, rfl⟩

@[expose] def finishedInjEntries (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (Δ L s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) (c : ℕ) :
    List ((ℕ × ℕ) × List ℕ) :=
  takeEntries s (off c) (callEntries G.edges (lemma1Route route G X (injPairs s k off sts) Δ L).1)

@[expose] def finishedChildEdges (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (Δ L s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) (c : ℕ) : List (ℕ × ℕ) :=
  witnessEdges (sts c).M (sts c).rounds.length ++
    (finishedInjEntries route G X Δ L s k off sts c).map Prod.fst

@[expose] def finishedChildFamily (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (Δ L s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) (c : ℕ) :
    List ((ℕ × ℕ) × List ℕ) :=
  (sts c).rounds.flatten ++ finishedInjEntries route G X Δ L s k off sts c

/-- The final injection of the child construction applies to any finished game satisfying
the round invariant and accumulated occurrence bound. -/
theorem lemma_3_of_finished_game {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r k s T : ℕ} {off : ℕ → ℕ} {sts : ℕ → ChildState}
    (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s) (hk : 1 ≤ k)
    (hinv : ∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L) (PParam cfg M r) T (sts c))
    (hload : ∀ i < G.m, ∑ c ∈ Finset.range k, occLoad (walkFamily (sts c).rounds.flatten) i ≤
      T * routeCong Δ bh L)
    (hsaved : ∀ c < k, ∃ S, (sts c).saved = some S) :
    (∀ c < k,
      (Graph.mk s (finishedChildEdges route G X Δ L s k off sts c)).IsExpansionExpanderOn
        (Finset.range s) (1 / (2 * PParam cfg M r : ℝ)) ∧
      (Graph.mk s (finishedChildEdges route G X Δ L s k off sts c)).IsValid ∧
      (Graph.mk s (finishedChildEdges route G X Δ L s k off sts c)).IsLoopless ∧
      (∀ v, (Graph.mk s (finishedChildEdges route G X Δ L s k off sts c)).deg v ≤
        T + 1) ∧
      (finishedChildFamily route G X Δ L s k off sts c).map Prod.fst =
        finishedChildEdges route G X Δ L s k off sts c ∧
      ∀ en ∈ finishedChildFamily route G X Δ L s k off sts c,
        EntryOK G X (off c) (routePathLen Δ bh L) en) ∧
    ∀ i < G.m, ∑ c ∈ Finset.range k,
        occLoad (walkFamily (finishedChildFamily route G X Δ L s k off sts c)) i ≤
      (T + 1) * routeCong Δ bh L := by
  -- Read the saved sets from the round invariant.
  have hSprop : ∀ c < k, savedSet s (sts c) ⊆ Finset.range s ∧
      s ≤ 2 * (savedSet s (sts c)).card ∧
      (gameGraph s (sts c)).IsExpansionExpanderOn (savedSet s (sts c))
        (1 / (PParam cfg M r : ℝ)) := by
    intro c hc
    obtain ⟨S, hS⟩ := hsaved c hc
    have h := (hinv c hc).2.2.2.1 S hS
    have hss : savedSet s (sts c) = S := by
      unfold savedSet
      rw [hS]
      rfl
    rw [hss]
    exact h
  -- the injection call
  set p : ℕ → Finset ℕ × Finset ℕ := fun c =>
    (shiftSet (off c) (Finset.range s \ savedSet s (sts c)), shiftSet (off c) (savedSet s (sts c)))
  have hpairs : injPairs s k off sts = (List.range k).map p := rfl
  have hp : ∀ c ∈ List.range k, (p c).1 ⊆ shiftSet (off c) (Finset.range s) ∧
      (p c).2 ⊆ shiftSet (off c) (Finset.range s) ∧ Disjoint (p c).1 (p c).2 ∧
      (p c).1.card ≤ (p c).2.card := by
    intro c hc
    obtain ⟨h1, h2, _⟩ := hSprop c (List.mem_range.mp hc)
    refine ⟨shiftSet_subset Finset.sdiff_subset, shiftSet_subset h1, ?_, ?_⟩
    · simp only [p]
      rw [shiftSet_sdiff]
      exact Finset.sdiff_disjoint
    · simp only [p]
      rw [card_shiftSet, card_shiftSet, Finset.card_sdiff_of_subset h1, Finset.card_range]
      omega
  have hne : List.range k ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  obtain ⟨Ms, emb, hres, hMlen, hMs, hemb, hlen, hcong, hwalk⟩ :=
    group_call hrouter hH hβ hexp hbh hch List.nodup_range (fun c hc => List.mem_range.mp hc)
      hne hp
  have hinjE : ∀ c, finishedInjEntries route G X Δ L s k off sts c =
      takeEntries s (off c) (callEntries G.edges (.matched Ms emb)) := by
    intro c
    show takeEntries s (off c)
      (callEntries G.edges (lemma1Route route G X (injPairs s k off sts) Δ L).1) = _
    rw [hpairs, hres]
  have htake : ∀ c < k,
      (finishedInjEntries route G X Δ L s k off sts c).map Prod.fst =
        unshiftEdges (off c) (Ms.getD c []) ∧
      ∀ en ∈ finishedInjEntries route G X Δ L s k off sts c,
        EntryOK G X (off c) (routePathLen Δ bh L) en := by
    intro c hc
    have hi : c < (List.range k).length := by rw [List.length_range]; exact hc
    rw [hinjE]
    exact take_call (Y := fun c => shiftSet (off c) (Finset.range s)) (p := p)
      List.nodup_range (fun c' hc' => (hch.2.1 c' (List.mem_range.mp hc')).1)
      (fun a ha b hb hab => hch.2.2 a (List.mem_range.mp ha) b (List.mem_range.mp hb) hab)
      (fun c' hc' => ⟨(hp c' hc').1, (hp c' hc').2.1⟩) hMlen (fun i hi => (hMs i hi).1) hemb hlen
      hi (by simp only [List.getElem_range])
  refine ⟨fun c hc => ?_, fun i hi => ?_⟩
  · obtain ⟨hlenT, _, hrounds, _, hent⟩ := hinv c hc
    obtain ⟨hS1, _, hS3⟩ := hSprop c hc
    obtain ⟨hmap, hok⟩ := htake c hc
    have hi : c < (List.range k).length := by rw [List.length_range]; exact hc
    obtain ⟨hends, hnd1, hnd2, hfull⟩ := hMs c hi
    simp only [List.getElem_range, p] at hends hfull
    rw [card_shiftSet] at hfull
    obtain ⟨hloc, hsnd, hcover, hflat⟩ :=
      unshift_props Finset.sdiff_disjoint hends hnd1 hnd2 hfull
    have hedges : finishedChildEdges route G X Δ L s k off sts c =
        witnessEdges (sts c).M (sts c).rounds.length ++ unshiftEdges (off c) (Ms.getD c []) := by
      show witnessEdges (sts c).M (sts c).rounds.length ++
        (finishedInjEntries route G X Δ L s k off sts c).map Prod.fst = _
      rw [hmap]
    have hpm : ∀ j < (sts c).rounds.length, IsPerfectMatchingOn (Finset.range s) ((sts c).M j) :=
      fun j hj => (hrounds j hj).1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hedges]
      refine childGraph_expansion (one_le_PParam cfg M r) hS1 hS3 ?_ hsnd ?_
      · intro e he
        have h := hloc e he
        exact ⟨(Finset.mem_sdiff.mp h.1).1, (Finset.mem_sdiff.mp h.1).2, h.2⟩
      · intro v hv hvS
        exact hcover v (Finset.mem_sdiff.mpr ⟨hv, hvS⟩)
    · rw [hedges]
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact witness_valid hpm e h
      · have h' := hloc e h
        exact ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp h'.1).1, Finset.mem_range.mp (hS1 h'.2)⟩
    · rw [hedges]
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact witness_loopless hpm e h
      · have h' := hloc e h
        intro heq
        exact (Finset.mem_sdiff.mp h'.1).2 (heq ▸ h'.2)
    · intro v
      rw [hedges]
      have hdeg := childGraph_deg_le hpm (Inj := unshiftEdges (off c) (Ms.getD c []))
        (fun e he => ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp (hloc e he).1).1,
          Finset.mem_range.mp (hS1 (hloc e he).2)⟩) hflat v
      have hlenT' : (sts c).rounds.length ≤ T := hlenT
      exact le_trans hdeg (by omega)
    · show ((sts c).rounds.flatten ++ finishedInjEntries route G X Δ L s k off sts c).map
          Prod.fst = _
      rw [List.map_append, hedges, hmap, ← witnessEdges_eq_flatten]
      rfl
    · intro en hen
      rcases List.mem_append.mp hen with h | h
      · exact hent en h
      · exact hok en h
  · have hfam : ∀ c, occLoad (walkFamily (finishedChildFamily route G X Δ L s k off sts c)) i =
        occLoad (walkFamily (sts c).rounds.flatten) i +
          occLoad (walkFamily (takeEntries s (off c) (callEntries G.edges (.matched Ms emb)))) i := by
      intro c
      show occLoad (walkFamily ((sts c).rounds.flatten ++
        finishedInjEntries route G X Δ L s k off sts c)) i = _
      rw [hinjE, walkFamily, List.map_append, occLoad_append]
      rfl
    rw [Finset.sum_congr rfl fun c _ => hfam c, Finset.sum_add_distrib]
    have h1 := hload i hi
    have h2 := sum_occLoad_take_le (fun c hc c' hc' h => hch.2.2 c hc c' hc' h)
      (callEntries G.edges (.matched Ms emb)) i
    have h3 := occLoad_callEntries_le hwalk (hcong i hi)
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add h1 (h2.trans h3)

/-- **The child construction at one group.** Let `G[X]` be a host with expansion `β > 0`, and let the children
`c < k` (`k ≥ 1`) be the disjoint intervals `off c, …, off c + s − 1` of `X`, with `s` even,
`s ≤ N^r` and `s < 2^{L'}`, where `49 L' ≤ deltaParam M`. Let `T = 49 L' + 1`,
`d = routePathLen Δ bh L` and `R = routeCong Δ bh L`. Then each child host
`⟨s, childEdges … T c⟩` has expansion at least `1/(2P)` on `range s` and degree at most `T + 1`,
each of its edges has a good walk in `G[X]`, and all these walks have load at most
`(T + 1) · R`. -/
theorem lemma_3 {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    (hk : 1 ≤ k) {L' : ℕ} (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hΔ : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L') :
    (∀ c < k,
      (Graph.mk s (childEdges route G X Δ L core M r s k off (49 * L' + 1) c)).IsExpansionExpanderOn
        (Finset.range s) (1 / (2 * PParam cfg M r : ℝ)) ∧
      (Graph.mk s (childEdges route G X Δ L core M r s k off (49 * L' + 1) c)).IsValid ∧
      (Graph.mk s (childEdges route G X Δ L core M r s k off (49 * L' + 1) c)).IsLoopless ∧
      (∀ v, (Graph.mk s (childEdges route G X Δ L core M r s k off (49 * L' + 1) c)).deg v ≤
        49 * L' + 2) ∧
      (childFamily route G X Δ L core M r s k off (49 * L' + 1) c).map Prod.fst =
        childEdges route G X Δ L core M r s k off (49 * L' + 1) c ∧
      ∀ en ∈ childFamily route G X Δ L core M r s k off (49 * L' + 1) c,
        EntryOK G X (off c) (routePathLen Δ bh L) en) ∧
    ∀ i < G.m, ∑ c ∈ Finset.range k,
        occLoad (walkFamily (childFamily route G X Δ L core M r s k off (49 * L' + 1) c)) i ≤
      (49 * L' + 2) * routeCong Δ bh L := by
  set T := 49 * L' + 1 with hT
  set sts := gameRun route G X Δ L core M r s k off T with hsts
  obtain ⟨hinv, hload⟩ := gameRun_inv hrouter hH hβ hexp hbh hcore hch heven hsN hΔ T le_rfl
  have hsaved := gameRun_saved hrouter hH hβ hexp hbh hcore hch heven hsN hΔ hsL
  exact lemma_3_of_finished_game hrouter hH hβ hexp hbh hch hk hinv hload hsaved

end MinCostFlow.HierPaths
