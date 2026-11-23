module

public import MinCostFlow.HierPaths.BuildChildCall
public import MinCostFlow.HierPaths.BuildCall
import Mathlib.Data.List.GetD

/-!
# The batched game of `lemma_3`: one round for all children

`gameRound_inv` shows that one round of the game keeps the invariant `ChildInv` of every child.
The steps:
- the core's answer for a child meets its specification, because the invariant makes the game
  graph a union of perfect matchings with few rounds (`coreSpec_of_inv`);
- so each request is a shifted bisection of the child (`request_props`), and the requests of one
  round are valid terminal pairs of the router;
- one full-routing call (`group_call`) then gives each requesting child the matching of its request
  (`take_call`), which is what `childInv_step` needs.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The core's answer for a child meets its specification while the invariant holds. -/
theorem coreSpec_of_inv {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {G : Graph} {X : Finset ℕ} {s o d P t L' : ℕ}
    (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M) (ht : t ≤ 49 * L')
    {st : ChildState} (hinv : ChildInv G X s o d P t st) :
    CoreOutcomeSpec cfg M r (gameGraph s st) (coreAnswer core M r s st) := by
  obtain ⟨hlen, _, hrounds, _, _⟩ := hinv
  have hpm : ∀ j < st.rounds.length, IsPerfectMatchingOn (Finset.range s) (st.M j) :=
    fun j hj => (hrounds j hj).1
  have hdeg : ∀ v < (gameGraph s st).n, (gameGraph s st).deg v ≤ deltaParam M := by
    intro v _
    have := witness_deg_le hpm v
    unfold gameGraph at this ⊢
    omega
  exact hcore.spec_coreLevel (witness_valid hpm) (witness_loopless hpm) hsN hdeg

/-- A request is the shifted bisection of a core cut. -/
theorem request_props {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {G : Graph} {X : Finset ℕ} {s o d P t L' : ℕ} (heven : s % 2 = 0)
    (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M) (ht : t ≤ 49 * L')
    {st : ChildState} (hinv : ChildInv G X s o d P t st) {q : Finset ℕ × Finset ℕ}
    (h : request core M r s o st = some q) :
    q.1 ⊆ shiftSet o (Finset.range s) ∧ q.2 ⊆ shiftSet o (Finset.range s) ∧
      Disjoint q.1 q.2 ∧ q.1.card ≤ q.2.card := by
  have hU : ∃ U, U ⊆ Finset.range s ∧
      q = (shiftSet o (bisectOf s U), shiftSet o (Finset.range s \ bisectOf s U)) := by
    unfold request at h
    cases hsv : st.saved with
    | some S => simp [hsv] at h
    | none =>
      have hspec := coreSpec_of_inv hcore hsN hΔ ht hinv
      cases hca : coreAnswer core M r s st with
      | expander S => simp [hsv, hca] at h
      | cut U =>
        simp only [hsv, hca, Option.some.injEq] at h
        rw [hca] at hspec
        exact ⟨U, hspec.1, h.symm⟩
  obtain ⟨U, hUs, rfl⟩ := hU
  obtain ⟨hC, hcard⟩ := bisectOf_spec hUs
  refine ⟨shiftSet_subset hC, shiftSet_subset Finset.sdiff_subset, ?_, ?_⟩
  · simp only
    rw [shiftSet_sdiff]
    exact Finset.disjoint_sdiff
  · simp only
    rw [card_shiftSet, card_shiftSet, Finset.card_sdiff_of_subset hC, Finset.card_range, hcard]
    omega

/-- **One call for a group of children.** The children `cs` are distinct children of `X`, and
both sides of each request lie in its child. One full-routing call returns one matching per
request, inside the request, covering its first side, with walks of at most
`routePathLen Δ bh L` edges and congestion at most `routeCong Δ bh L`. -/
theorem group_call {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {Y : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X Y k s)
    {cs : List ℕ} (hnd : cs.Nodup) (hcs : ∀ c ∈ cs, c < k) (hne : cs ≠ [])
    {p : ℕ → Finset ℕ × Finset ℕ}
    (hp : ∀ c ∈ cs, (p c).1 ⊆ Y c ∧ (p c).2 ⊆ Y c ∧ Disjoint (p c).1 (p c).2 ∧
      (p c).1.card ≤ (p c).2.card) :
    ∃ Ms emb, (lemma1Route route G X (cs.map p) Δ L).1 = .matched Ms emb ∧
      Ms.length = cs.length ∧
      (∀ i (hi : i < cs.length), (∀ e ∈ Ms.getD i [], e.1 ∈ (p cs[i]).1 ∧ e.2 ∈ (p cs[i]).2) ∧
        ((Ms.getD i []).map Prod.fst).Nodup ∧ ((Ms.getD i []).map Prod.snd).Nodup ∧
        (Ms.getD i []).length = (p cs[i]).1.card) ∧
      IsEmbeddingOn (Graph.mk G.n Ms.flatten) G X emb ∧
      (∀ j < Ms.flatten.length, (emb j).length ≤ routePathLen Δ bh L) ∧
      (∀ i < G.m, congestion (Graph.mk G.n Ms.flatten) emb i ≤ routeCong Δ bh L) ∧
      (∀ j < Ms.flatten.length,
        IsEdgeWalk G.edges (edgeAt Ms.flatten j).1 (edgeAt Ms.flatten j).2 (emb j)) := by
  obtain ⟨C, hC⟩ := hrouter.cost_bound
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  have hY : ∀ c ∈ cs, Y c ⊆ X := fun c hc => (hch.2.1 c (hcs c hc)).1
  have hdisj : ∀ c ∈ cs, ∀ c' ∈ cs, c ≠ c' → Disjoint (Y c) (Y c') :=
    fun c hc c' hc' h => hch.2.2 c (hcs c hc) c' (hcs c' hc') h
  have hv : ValidTerminalPairs X (cs.map p) := validTerminalPairs_of_children hnd hY hdisj hp
  have hpre : RouterPre G X (cs.map p) Δ L := ⟨a1, a2, a3, a4, a5, a6, hv⟩
  have hk : 1 ≤ (cs.map p).length := by
    rw [List.length_map]
    exact List.length_pos_iff.mpr hne
  obtain ⟨Ms, emb, b', hres, hspec, hfull, _, hemb, hlen, hcong, _⟩ :=
    call_facts hrouter (fun b hb => hC G X _ Δ L b 0 a1 a2 a3 a4 a5 a6 hb hv) hpre hk hβ hexp hbh
  obtain ⟨hMlen, hMs, _⟩ := hspec
  rw [List.length_map] at hMlen
  have hblock : ∀ i (hi : i < cs.length), (∀ e ∈ Ms.getD i [], e.1 ∈ (p cs[i]).1 ∧ e.2 ∈ (p cs[i]).2) ∧
      ((Ms.getD i []).map Prod.fst).Nodup ∧ ((Ms.getD i []).map Prod.snd).Nodup ∧
      (Ms.getD i []).length = (p cs[i]).1.card := by
    intro i hi
    have hi' : i < (cs.map p).length := by rw [List.length_map]; exact hi
    obtain ⟨h1, h2, h3⟩ := hMs i hi'
    have hpi : (cs.map p)[i] = p cs[i] := List.getElem_map _
    have h4 := hfull i hi'
    rw [hpi] at h1 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨Ms, emb, by rw [hres], hMlen, hblock, hemb, hlen, hcong, fun j hj => ?_⟩
  have hmem : edgeAt Ms.flatten j ∈ Ms.flatten := by
    unfold edgeAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp hmem
  obtain ⟨i, hiM, rfl⟩ := List.getElem_of_mem hl
  have hi : i < cs.length := hMlen ▸ hiM
  have hends := (hblock i hi).1 _ (by rw [List.getD_eq_getElem _ _ hiM]; exact hel)
  have hcs := List.getElem_mem hi
  obtain ⟨hp1, hp2, _⟩ := hp _ hcs
  have hin : insideB X (edgeAt (Graph.mk G.n Ms.flatten).edges j) = true := by
    simp only [insideB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hY _ hcs (hp1 hends.1), hY _ hcs (hp2 hends.2)⟩
  exact (hemb j hj hin).1

/-- The requesting children are distinct children. -/
theorem requesting_spec (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ)
    (sts : ℕ → ChildState) :
    (requesting core M r s k off sts).Nodup ∧
      ∀ c, c ∈ requesting core M r s k off sts ↔
        c < k ∧ (request core M r s (off c) (sts c)).isSome := by
  refine ⟨List.nodup_range.filter _, fun c => ?_⟩
  unfold requesting
  simp

/-- **One round keeps the invariant of every child.** -/
theorem gameRound_inv {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    {t L' : ℕ} (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M)
    (ht : t ≤ 49 * L') {sts : ℕ → ChildState}
    (hinv : ∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L) (PParam cfg M r) t (sts c)) :
    ∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L) (PParam cfg M r) (t + 1)
      (gameRound route G X Δ L core M r s k off sts c) := by
  intro c hc
  refine childInv_step (take := takeEntries s (off c)
    (callEntries G.edges (lemma1Route route G X (roundPairs core M r s k off sts) Δ L).1))
    hcore heven hsN hΔ ht (hinv c hc) ?_
  intro U hsv hca
  set cs := requesting core M r s k off sts with hcs_def
  obtain ⟨hnd, hmem⟩ := requesting_spec core M r s k off sts
  set p : ℕ → Finset ℕ × Finset ℕ := fun c' => (request core M r s (off c') (sts c')).getD (∅, ∅)
  have hreq : request core M r s (off c) (sts c) =
      some (shiftSet (off c) (bisectOf s U), shiftSet (off c) (Finset.range s \ bisectOf s U)) := by
    unfold request
    simp [hsv, hca]
  have hcmem : c ∈ cs := (hmem c).mpr ⟨hc, by rw [hreq]; rfl⟩
  have hp : ∀ c' ∈ cs, (p c').1 ⊆ shiftSet (off c') (Finset.range s) ∧
      (p c').2 ⊆ shiftSet (off c') (Finset.range s) ∧ Disjoint (p c').1 (p c').2 ∧
      (p c').1.card ≤ (p c').2.card := by
    intro c' hc'
    obtain ⟨hc'k, hsome⟩ := (hmem c').mp hc'
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
    have hpq : p c' = q := by simp only [p, hq, Option.getD_some]
    rw [hpq]
    exact request_props hcore heven hsN hΔ ht (hinv c' hc'k) hq
  have hpairs : roundPairs core M r s k off sts = cs.map p := rfl
  obtain ⟨Ms, emb, hres, hMlen, hMs, hemb, hlen, _, _⟩ :=
    group_call hrouter hH hβ hexp hbh hch hnd (fun c' hc' => ((hmem c').mp hc').1)
      (List.ne_nil_of_mem hcmem) hp
  rw [hpairs, hres]
  have hi : cs.idxOf c < cs.length := List.idxOf_lt_length_of_mem hcmem
  have hci : cs[cs.idxOf c] = c := List.getElem_idxOf hi
  obtain ⟨hmap, hok⟩ := take_call (Y := fun c => shiftSet (off c) (Finset.range s)) (p := p)
    (s := s) (o := off c) hnd (fun c' hc' => (hch.2.1 c' ((hmem c').mp hc').1).1)
    (fun a ha b hb hab => hch.2.2 a ((hmem a).mp ha).1 b ((hmem b).mp hb).1 hab)
    (fun c' hc' => ⟨(hp c' hc').1, (hp c' hc').2.1⟩) hMlen (fun i hi => (hMs i hi).1) hemb hlen hi
    (by show shiftSet (off cs[cs.idxOf c]) _ = _; rw [hci])
  obtain ⟨hends, hnd1, hnd2, hfull⟩ := hMs _ hi
  have hpc : p c = (shiftSet (off c) (bisectOf s U),
      shiftSet (off c) (Finset.range s \ bisectOf s U)) := by
    simp only [p, hreq, Option.getD_some]
  rw [hci, hpc] at hends hfull
  refine ⟨⟨Ms.getD (cs.idxOf c) [], hmap, hends, hnd1, hnd2, ?_⟩, hok⟩
  rw [hfull]
  exact card_shiftSet _ _

end MinCostFlow.HierPaths
