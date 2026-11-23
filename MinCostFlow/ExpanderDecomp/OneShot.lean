module

public import MinCostFlow.ExpanderDecomp.OneShotStepB
public import MinCostFlow.ExpanderDecomp.EdgeColor
public import MinCostFlow.ExpanderDecomp.PortGraph
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `OneShot(q, G, X)`

This file defines `oneShot` and proves its specification `oneShot_spec`, combining:
* Step A (`BlockSplit.lean`): splitting `vs = X.sort (· ≤ ·)` into `k` full blocks of size
  `b = 1` (at `q = 1`) or `b = N ^ (q - 1) / 2` (at `q ≥ 2`) plus leftover set `Z`.
* Step B (`OneShotStepB.lean`): for `q ≥ 2`, running the `k` parallel block cut-matching games
  for `49 * L + 1` rounds and injecting each block complement into its certified expanding subset.
* Step C (`EdgeColor.lean`, `BlocksMacro.lean`, `BlockSplit.lean`): when `2 ≤ k`, deleting loops
  from `cloud k`, greedily 17-colouring its edges, routing one bipartite matching per edge of each
  colour class, and (if `Z ≠ ∅`) injecting `Z` into the full blocks.
* Step D (`OneShotStepD.lean`, `FakeEdges.lean`): composing the embeddings of all at most
  `49 * L + 20 ≤ Δ` routing calls (`isConductanceExpanderOn_of_embedding`) and removing fake edges
  (`removeFake_spec`) to obtain an induced `1 / P_q`-expander on at least `11 / 12` of `X`, or returning any failed-router cut.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Route one colour class `E_c` of the macro expander: each macro edge `(i, j) ∈ E_c` requests a
bipartite perfect matching between `blockSet vs b i` and `blockSet vs b j`. Returns `Sum.inl U`
on a router cut, or `Sum.inr (calls, matchings_completed)` otherwise. -/
def stepCMacroColor (cfg : CoreParams) (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (vs : List ℕ) (b z : ℕ) (Ec : List (ℕ × ℕ)) :
    Finset ℕ ⊕ (List RoutedCall × List (List (ℕ × ℕ))) :=
  if Ec.isEmpty then
    Sum.inr ([], [])
  else
    let pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
    match route G X pairs cfg.Δ cfg.L 100 z with
    | .cut U => Sum.inl U
    | .matched matchings emb =>
        let rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩
        let completed := List.zipWith (fun p m => m ++ completeMatchingFake p.1 p.2 m)
          pairs matchings
        Sum.inr ([rc], completed)

/-- Route colours `0, …, m - 1` of the 17-edge-colouring `colored`. -/
def stepCMacroLoop (cfg : CoreParams) (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (vs : List ℕ) (b z : ℕ) (colored : List ((ℕ × ℕ) × ℕ)) :
    ℕ → Finset ℕ ⊕ (List RoutedCall × List (List (ℕ × ℕ)))
  | 0 => Sum.inr ([], [])
  | m + 1 =>
      match stepCMacroLoop cfg route G X vs b z colored m with
      | Sum.inl U => Sum.inl U
      | Sum.inr (calls, ms) =>
          match stepCMacroColor cfg route G X vs b z (colorClass colored m) with
          | Sum.inl U => Sum.inl U
          | Sum.inr (cs, ms') => Sum.inr (calls ++ cs, ms ++ ms')

/-- Step C macro join: if `2 ≤ k`, 17-colour `removeLoops (cloud k)` and route all 17 colour
classes; if `k < 2`, no macro edges are needed. -/
def stepCMacro (cfg : CoreParams) (route : RouterFn) (cloud : ℕ → Graph) (G : Graph)
    (X : Finset ℕ) (vs : List ℕ) (b k z : ℕ) : Finset ℕ ⊕ List RoutedCall :=
  if 2 ≤ k then
    match stepCMacroLoop cfg route G X vs b z (edgeColor17 (cloud k)) 17 with
    | Sum.inl U => Sum.inl U
    | Sum.inr (calls, _) => Sum.inr calls
  else
    Sum.inr []

/-- Step C leftover injection: if `leftoverVerts vs b` is nonempty, route it into `fullVerts vs b`. -/
def stepCLeftover (cfg : CoreParams) (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (vs : List ℕ) (b z : ℕ) : Finset ℕ ⊕ List RoutedCall :=
  if (leftoverVerts vs b).Nonempty then
    let pairs := [(leftoverVerts vs b, fullVerts vs b)]
    match route G X pairs cfg.Δ cfg.L 100 z with
    | .cut U => Sum.inl U
    | .matched matchings emb =>
        Sum.inr [⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩]
  else
    Sum.inr []

/-- **`OneShot(q, G, X)`**: runs Steps A–D and returns either a failed-router cut
or an induced `1 / P_q`-expander on at least `11 / 12` of `X`. -/
noncomputable def oneShot (cfg : CoreParams) (route : RouterFn) (cloud : ℕ → Graph)
    (q : ℕ) (subCore : Graph → Finset ℕ → CoreResult) (G : Graph) (X : Finset ℕ) :
    CoreResult :=
  let vs := X.sort (· ≤ ·)
  let b := if q = 1 then 1 else cfg.N ^ (q - 1) / 2
  let k := numFullBlocks vs b
  let z := X.card / cfg.D q
  let resB : Finset ℕ ⊕ List RoutedCall :=
    if q = 1 then Sum.inr []
    else stepB cfg route G X vs b k z subCore
  match resB with
  | Sum.inl U => .cut U
  | Sum.inr callsB =>
      match stepCMacro cfg route cloud G X vs b k z with
      | Sum.inl U => .cut U
      | Sum.inr callsC =>
          match stepCLeftover cfg route G X vs b z with
          | Sum.inl U => .cut U
          | Sum.inr callsZ =>
              let callsAll := callsB ++ callsC ++ callsZ
              .expander (removeFake G.n G.edges (callsFakeEdges callsAll) X (12 / (cfg.P q : ℝ)))

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### List permutation helpers for Step C -/

private lemma zipWith_append_flatten_perm {α : Type*} (xs ys : List (List α))
    (h : xs.length = ys.length) :
    (List.zipWith (· ++ ·) xs ys).flatten.Perm (xs.flatten ++ ys.flatten) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons _ _ => simp at h
  | cons x xt ih =>
    cases ys with
    | nil => simp at h
    | cons y yt =>
      have ht : xt.length = yt.length := by simpa using h
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.append_assoc]
      have h1 : (x ++ (y ++ (List.zipWith (· ++ ·) xt yt).flatten)).Perm
          (x ++ (y ++ (xt.flatten ++ yt.flatten))) :=
        List.Perm.append_left x (List.Perm.append_left y (ih yt ht))
      refine h1.trans (List.Perm.append_left x ?_)
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right yt.flatten List.perm_append_comm

private lemma flatten_eq_flatMap_range {α : Type*} (ms : List (List α)) :
    ms.flatten = (List.range ms.length).flatMap (fun j => ms.getD j []) := by
  induction ms with
  | nil => simp
  | cons m rest ih =>
    rw [List.flatten_cons, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.getD_cons_zero, List.flatMap_map, ih]
    congr 1

theorem validTerminalPairs_of_matching_edges {vs : List ℕ} (hnd : vs.Nodup) {b : ℕ}
    (hb : 0 < b) {Ec : List (ℕ × ℕ)}
    (hvalid : ∀ e ∈ Ec, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b)
    (hEc_nd : (Ec.flatMap fun e => [e.1, e.2]).Nodup) :
    ValidTerminalPairs vs.toFinset (Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    have hv := hvalid e he
    refine ⟨blockSet_subset_toFinset vs b e.1, blockSet_subset_toFinset vs b e.2, ?_⟩
    rw [card_blockSet hnd hv.1, card_blockSet hnd hv.2]
  · induction Ec with
    | nil => simp
    | cons e rest ih =>
      have hv := hvalid e List.mem_cons_self
      have hrest_v : ∀ e' ∈ rest, e'.1 < numFullBlocks vs b ∧ e'.2 < numFullBlocks vs b :=
        fun e' he' => hvalid e' (List.mem_cons_of_mem _ he')
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hEc_nd
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append,
        List.pairwise_cons]
      have he12 : e.1 ≠ e.2 := fun h => hEc_nd.1 (h ▸ List.mem_cons_self)
      refine ⟨?_, ?_, ih hrest_v hEc_nd.2.2⟩
      · intro S hS
        rcases List.mem_cons.mp hS with rfl | hfm
        · exact disjoint_blockSet hnd hb hv.1 hv.2 he12
        · obtain ⟨p, hp, hpS⟩ := List.mem_flatMap.mp hfm
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hp
          have hv' := hrest_v e' he'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpS
          rcases hpS with rfl | rfl
          · have hne : e.1 ≠ e'.1 := fun h => hEc_nd.1 (List.mem_cons_of_mem _
              (List.mem_flatMap.mpr ⟨e', he', by simp [h]⟩))
            exact disjoint_blockSet hnd hb hv.1 hv'.1 hne
          · have hne : e.1 ≠ e'.2 := fun h => hEc_nd.1 (List.mem_cons_of_mem _
              (List.mem_flatMap.mpr ⟨e', he', by simp [h]⟩))
            exact disjoint_blockSet hnd hb hv.1 hv'.2 hne
      · intro S hS
        obtain ⟨p, hp, hpS⟩ := List.mem_flatMap.mp hS
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hp
        have hv' := hrest_v e' he'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpS
        rcases hpS with rfl | rfl
        · have hne : e.2 ≠ e'.1 := fun h => hEc_nd.2.1
            (List.mem_flatMap.mpr ⟨e', he', by simp [h]⟩)
          exact disjoint_blockSet hnd hb hv.2 hv'.1 hne
        · have hne : e.2 ≠ e'.2 := fun h => hEc_nd.2.1
            (List.mem_flatMap.mpr ⟨e', he', by simp [h]⟩)
          exact disjoint_blockSet hnd hb hv.2 hv'.2 hne

/-! ### Step C specifications -/

private lemma stepCMacroColor_spec {cfg : CoreParams} {r : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X) (hb : 0 < b)
    {Ec : List (ℕ × ℕ)}
    (hEc_valid : ∀ e ∈ Ec, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b)
    (hEc_nd : (Ec.flatMap fun e => [e.1, e.2]).Nodup) :
    match stepCMacroColor cfg route G X vs b z Ec with
    | Sum.inl U => RouteCutSpec G X 100 z U
    | Sum.inr (cs, ms) =>
        cs.length ≤ 1 ∧
        (∀ c ∈ cs, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
        ms.length = Ec.length ∧
        (callsWitnessEdges cs).Perm ms.flatten ∧
        ∀ j < Ec.length,
          IsBipartiteMatching (blockSet vs b (edgeAt Ec j).1)
            (blockSet vs b (edgeAt Ec j).2) (ms.getD j []) := by
  unfold stepCMacroColor
  by_cases hemp : Ec.isEmpty = true
  · simp only [hemp, ↓reduceIte]
    have hnil : Ec = [] := List.isEmpty_iff.mp hemp
    subst hnil
    exact ⟨by simp, by simp, by simp, by simp [callsWitnessEdges], fun j hj => by simp at hj⟩
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    set pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
    have hpairs : ValidTerminalPairs X pairs :=
      hvs ▸ validTerminalPairs_of_matching_edges hnd hb hEc_valid hEc_nd
    have hrspec := hroute.spec G X pairs cfg.Δ cfg.L 100 z hX hGloop hcfg.hΔ_pos hdegG hcfg.hL
      hXL (by decide) hpairs
    dsimp only [pairs] at hrspec ⊢
    cases hres : route G X (Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2))
        cfg.Δ cfg.L 100 z with
    | cut U =>
      rw [hres] at hrspec
      exact hrspec
    | matched matchings emb =>
      rw [hres] at hrspec
      dsimp only
      have hrc : RoutedCall.Valid G X (routeCong cfg.Δ 100 cfg.L) z
          ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩ :=
        routedCall_valid_of_matched hpairs hrspec
      have hmlen : matchings.length = Ec.length := by simpa [pairs] using hrspec.1
      set fakes := List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings
      have hflen : fakes.length = Ec.length := by
        simp [fakes, pairs, hmlen]
      set completed := List.zipWith (fun p m => m ++ completeMatchingFake p.1 p.2 m) pairs matchings
      have hcomp_eq : completed = List.zipWith (· ++ ·) matchings fakes := by
        apply List.ext_getElem
        · simp [completed, fakes, pairs, hmlen]
        · intro j hj1 hj2
          have hjE : j < Ec.length := by simpa [completed, pairs, hmlen] using hj1
          simp [completed, fakes, List.getElem_zipWith]
      have hperm : (callsWitnessEdges [⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩]).Perm
          completed.flatten := by
        rw [hcomp_eq]
        have hcw : callsWitnessEdges [⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩] =
            matchings.flatten ++ fakes.flatten := by
          simp [callsWitnessEdges, completeBatchFake, fakes]
        rw [hcw]
        exact (zipWith_append_flatten_perm matchings fakes (by omega)).symm
      refine ⟨by simp, fun c hc => by rw [List.mem_singleton.mp hc]; exact hrc,
        by simp [completed, pairs, hmlen], hperm, ?_⟩
      intro j hj
      have hj_p : j < pairs.length := by simp [pairs, hj]
      have hj_m : j < matchings.length := by omega
      have hj_c : j < completed.length := by simp [completed, pairs, hmlen, hj]
      have hmspec := hrspec.2.1 j (by simpa [pairs] using hj_p)
      dsimp only at hmspec
      have he_mem : edgeAt Ec j ∈ Ec := by
        unfold edgeAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      have hve := hEc_valid _ he_mem
      have hne_end : (edgeAt Ec j).1 ≠ (edgeAt Ec j).2 := by
        have hgen : ∀ (L : List (ℕ × ℕ)), (L.flatMap fun e => [e.1, e.2]).Nodup →
            ∀ e ∈ L, e.1 ≠ e.2 := by
          intro L
          induction L with
          | nil => intro _ e he; simp at he
          | cons p rest ihr =>
            rcases p with ⟨a, c⟩
            intro hnd' e he
            simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd'
            rcases List.mem_cons.mp he with rfl | hrest
            · intro heq; dsimp only at heq; apply hnd'.1; rw [heq]; exact List.mem_cons_self
            · exact ihr hnd'.2.2 e hrest
        exact hgen Ec hEc_nd _ he_mem
      have hdisj := disjoint_blockSet hnd hb hve.1 hve.2 hne_end
      have hcard_eq : (blockSet vs b (edgeAt Ec j).1).card =
          (blockSet vs b (edgeAt Ec j).2).card := by
        rw [card_blockSet hnd hve.1, card_blockSet hnd hve.2]
      have hp_j : (Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2))[j]'(by simpa [pairs] using hj_p) =
          (blockSet vs b (edgeAt Ec j).1, blockSet vs b (edgeAt Ec j).2) := by
        unfold edgeAt
        rw [List.getD_eq_getElem _ _ hj]
        simp
      rw [hp_j] at hmspec
      dsimp only at hmspec
      have hget_c : completed.getD j [] =
          matchings.getD j [] ++ completeMatchingFake (blockSet vs b (edgeAt Ec j).1)
            (blockSet vs b (edgeAt Ec j).2) (matchings.getD j []) := by
        unfold edgeAt
        rw [List.getD_eq_getElem _ _ hj_c, List.getD_eq_getElem _ _ hj_m, List.getD_eq_getElem _ _ hj]
        simp [completed, pairs]
      rw [hget_c]
      exact isBipartiteMatching_complete hdisj hcard_eq hmspec.1 hmspec.2.1 hmspec.2.2

/-- **Step C macro-join specification**: given internal edges `callsB` certifying every full block
has expansion `β ∈ [0, 1]`, `stepCMacro` either returns a router cut or returns `callsC` of length
at most `17` such that `callsWitnessEdges (callsB ++ callsC)` has expansion at least `α * β / 10`
on `fullVerts vs b`. -/
theorem stepCMacro_spec {cfg : CoreParams} {r : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud cfg.α)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X) (hb : 0 < b)
    (hk1 : 1 ≤ numFullBlocks vs b)
    {callsB : List RoutedCall} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hint : ∀ i < numFullBlocks vs b,
      (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn (blockSet vs b i) β) :
    match stepCMacro cfg route cloud G X vs b (numFullBlocks vs b) z with
    | Sum.inl U => RouteCutSpec G X 100 z U
    | Sum.inr callsC =>
        callsC.length ≤ 17 ∧
        (∀ c ∈ callsC, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
        (Graph.mk G.n (callsWitnessEdges (callsB ++ callsC))).IsExpansionExpanderOn
          (fullVerts vs b) (cfg.α * β / 10) := by
  set k := numFullBlocks vs b
  unfold stepCMacro
  by_cases hk2 : 2 ≤ k
  · simp only [hk2, ↓reduceIte]
    have hcn : (cloud k).n = k := hcloud.n_eq k hk2
    have hcvalid : (cloud k).IsValid := hcloud.isValid k hk2
    have hcdeg : ∀ v < (cloud k).n, (cloud k).deg v ≤ 9 := fun v hv => hcloud.deg_le k hk2 v (hcn ▸ hv)
    have hcexp : (cloud k).IsExpansionExpanderOn (cloud k).verts cfg.α := hcloud.expansion k hk2
    have hcol_spec := edgeColor17_spec hcvalid hcdeg
    set colored := edgeColor17 (cloud k)
    have hHvalid : (removeLoops (cloud k)).IsValid := removeLoops_isValid hcvalid
    have hEc_valid : ∀ c, ∀ e ∈ colorClass colored c, e.1 < k ∧ e.2 < k := by
      intro c e he
      unfold colorClass at he
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
      have hin : ec.1 ∈ (removeLoops (cloud k)).edges := by
        rw [← hcol_spec.1]
        exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
      have hv := hHvalid ec.1 hin
      rwa [removeLoops_n, hcn] at hv
    -- Induction on `m ≤ 17` for `stepCMacroLoop`.
    have hloop : ∀ m,
        match stepCMacroLoop cfg route G X vs b z colored m with
        | Sum.inl U => RouteCutSpec G X 100 z U
        | Sum.inr (cs, ms) =>
            cs.length ≤ m ∧
            (∀ c ∈ cs, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
            ms.length = ((List.range m).flatMap (colorClass colored)).length ∧
            (callsWitnessEdges cs).Perm ms.flatten ∧
            ∀ j (hj : j < ((List.range m).flatMap (colorClass colored)).length),
              IsBipartiteMatching
                (blockSet vs b (edgeAt ((List.range m).flatMap (colorClass colored)) j).1)
                (blockSet vs b (edgeAt ((List.range m).flatMap (colorClass colored)) j).2)
                (ms.getD j []) := by
      intro m
      induction m with
      | zero =>
        simp [stepCMacroLoop, callsWitnessEdges]
      | succ m ih =>
        unfold stepCMacroLoop
        cases hl : stepCMacroLoop cfg route G X vs b z colored m with
        | inl U =>
          rw [hl] at ih
          exact ih
        | inr res =>
          rcases res with ⟨cs, ms⟩
          rw [hl] at ih
          dsimp only at ih ⊢
          have hstep := stepCMacroColor_spec hcfg hroute (z := z) hX hGloop hdegG hXL hnd hvs hb
            (hEc_valid m) (hcol_spec.2.2.1 m)
          cases hc : stepCMacroColor cfg route G X vs b z (colorClass colored m) with
          | inl U =>
            rw [hc] at hstep
            exact hstep
          | inr res' =>
            rcases res' with ⟨cs', ms'⟩
            rw [hc] at hstep
            dsimp only at hstep ⊢
            set Eprev := (List.range m).flatMap (colorClass colored)
            set Ecur := colorClass colored m
            have hE_eq : (List.range (m + 1)).flatMap (colorClass colored) = Eprev ++ Ecur := by
              rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · rw [List.length_append]; omega
            · intro c hc_mem
              rcases List.mem_append.mp hc_mem with h1 | h2
              · exact ih.2.1 c h1
              · exact hstep.2.1 c h2
            · rw [hE_eq, List.length_append, List.length_append, ih.2.2.1, hstep.2.2.1]
            · rw [show callsWitnessEdges (cs ++ cs') =
                callsWitnessEdges cs ++ callsWitnessEdges cs' by simp [callsWitnessEdges],
                List.flatten_append]
              exact ih.2.2.2.1.append hstep.2.2.2.1
            · intro j hj
              rw [hE_eq] at hj ⊢
              by_cases hj1 : j < Eprev.length
              · have hedge : edgeAt (Eprev ++ Ecur) j = edgeAt Eprev j := by
                  unfold edgeAt; exact List.getD_append _ _ _ _ hj1
                have hget : (ms ++ ms').getD j [] = ms.getD j [] :=
                  List.getD_append _ _ _ _ (ih.2.2.1.symm ▸ hj1)
                rw [hedge, hget]
                exact ih.2.2.2.2 j hj1
              · have hj2 : j - Eprev.length < Ecur.length := by
                  rw [List.length_append] at hj; omega
                have hedge : edgeAt (Eprev ++ Ecur) j = edgeAt Ecur (j - Eprev.length) := by
                  unfold edgeAt
                  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj2,
                    List.getElem_append_right (by omega)]
                have hj_ms : j < (ms ++ ms').length := by
                  rw [List.length_append, ih.2.2.1, hstep.2.2.1]; rw [List.length_append] at hj; exact hj
                have hj2_ms : j - ms.length < ms'.length := by omega
                have hget : (ms ++ ms').getD j [] = ms'.getD (j - Eprev.length) [] := by
                  rw [List.getD_eq_getElem _ _ hj_ms, List.getD_eq_getElem _ _ (ih.2.2.1 ▸ hj2_ms),
                    List.getElem_append_right (by omega)]
                  simp only [ih.2.2.1]
                rw [hedge, hget]
                exact hstep.2.2.2.2 (j - Eprev.length) hj2
    have h17 := hloop 17
    cases hl17 : stepCMacroLoop cfg route G X vs b z colored 17 with
    | inl U =>
      rw [hl17] at h17
      exact h17
    | inr res =>
      rcases res with ⟨callsC, ms⟩
      rw [hl17] at h17
      dsimp only at h17 ⊢
      refine ⟨h17.1, h17.2.1, ?_⟩
      -- Build the permuted macro graph `H'` whose edges are already in colour-class order!
      set H' : Graph := ⟨k, (List.range 17).flatMap (colorClass colored)⟩
      have hHperm : H'.edges.Perm (removeLoops (cloud k)).edges := hcol_spec.2.2.2.2
      have hH'valid : H'.IsValid := by
        intro e he
        have hv := hHvalid e (hHperm.subset he)
        rwa [removeLoops_n, hcn] at hv
      have hH'deg : ∀ i < H'.n, H'.deg i ≤ 9 := by
        intro i hi
        have heq : H'.deg i = (removeLoops (cloud k)).deg i := by
          unfold Graph.deg Graph.verts
          have h1 : H'.n = (removeLoops (cloud k)).n := by rw [removeLoops_n, hcn]
          rw [h1]
          exact degIn_of_perm (removeLoops (cloud k)).n hHperm _ i
        rw [heq]
        exact le_trans (removeLoops_deg_le (cloud k) i) (hcloud.deg_le k hk2 i hi)
      have hH'exp : H'.IsExpansionExpanderOn H'.verts cfg.α := by
        have h1 : (removeLoops (cloud k)).IsExpansionExpanderOn (removeLoops (cloud k)).verts cfg.α :=
          removeLoops_isExpansionExpanderOn hcexp
        have h2 : (removeLoops (cloud k)).n = k := by rw [removeLoops_n, hcn]
        have h3 : (Graph.mk k (removeLoops (cloud k)).edges).IsExpansionExpanderOn
            (Finset.range k) cfg.α := by
          unfold Graph.verts at h1
          rw [h2] at h1
          exact h1
        exact isExpansionExpanderOn_of_perm hHperm.symm h3
      have hcw_eq : callsWitnessEdges (callsB ++ callsC) =
          callsWitnessEdges callsB ++ callsWitnessEdges callsC := by
        simp [callsWitnessEdges]
      rw [hcw_eq]
      have hperm_ext : (callsWitnessEdges callsC).Perm
          ((List.range H'.m).flatMap fun j => ms.getD j []) := by
        have hlen : ms.length = H'.m := h17.2.2.1
        rw [← hlen, ← flatten_eq_flatMap_range ms]
        exact h17.2.2.2.1
      refine isExpansionExpanderOn_of_macro_blocks_nine (b := b) (blockOf vs b)
        hcfg.hα0.le hcfg.hα1 hβ0 hβ1 hH'valid hH'deg hH'exp ?_ ?_ ?_ ?_ hperm_ext
      · intro v hv
        exact blockOf_lt_numFullBlocks hb hv
      · intro i hi
        exact card_filter_blockOf hnd hb hi
      · intro i hi
        rw [filter_blockOf_eq_blockSet hnd hb hi]
        exact hint i hi
      · intro j hj
        have he : edgeAt H'.edges j ∈ H'.edges := by
          unfold edgeAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        have hv := hH'valid _ he
        rw [filter_blockOf_eq_blockSet hnd hb hv.1, filter_blockOf_eq_blockSet hnd hb hv.2]
        exact h17.2.2.2.2 j hj
  · -- Single full block (`k = 1`): `fullVerts vs b = blockSet vs b 0`.
    simp only [hk2, ↓reduceIte]
    have hk_eq : k = 1 := by omega
    have hF_eq : fullVerts vs b = blockSet vs b 0 := by
      rw [← filter_blockOf_eq_blockSet hnd hb (by omega : 0 < k)]
      ext v
      simp only [Finset.mem_filter, iff_self_and]
      intro hv
      have hlt := blockOf_lt_numFullBlocks hb hv
      omega
    have hcw : callsWitnessEdges (callsB ++ []) = callsWitnessEdges callsB := by
      simp [callsWitnessEdges]
    refine ⟨by simp, by simp, ?_⟩
    rw [hcw, hF_eq]
    have hmono : cfg.α * β / 10 ≤ β := by
      have hα1 := hcfg.hα1
      nlinarith
    exact IsExpansionExpanderOn.mono hmono (hint 0 (by omega))

/-- **Step C leftover-injection specification**: given `callsBC` certifying `fullVerts vs b` has
expansion `γ ∈ [0, 1]`, `stepCLeftover` either returns a router cut or returns `callsZ` (length at
most `1`) such that `callsWitnessEdges (callsBC ++ callsZ)` has expansion at least `γ / 2` on `X`. -/
theorem stepCLeftover_spec {cfg : CoreParams} {r : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X) (hb : 0 < b) (hble : b ≤ vs.length)
    {callsBC : List RoutedCall} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hfull : (Graph.mk G.n (callsWitnessEdges callsBC)).IsExpansionExpanderOn (fullVerts vs b) γ) :
    match stepCLeftover cfg route G X vs b z with
    | Sum.inl U => RouteCutSpec G X 100 z U
    | Sum.inr callsZ =>
        callsZ.length ≤ 1 ∧
        (∀ c ∈ callsZ, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
        (Graph.mk G.n (callsWitnessEdges (callsBC ++ callsZ))).IsExpansionExpanderOn X (γ / 2) := by
  unfold stepCLeftover
  by_cases hZne : (leftoverVerts vs b).Nonempty
  · simp only [hZne, ↓reduceIte]
    set pairs := [(leftoverVerts vs b, fullVerts vs b)]
    have hpairs : ValidTerminalPairs X pairs := by
      have hle := card_leftoverVerts_le_card_sdiff hnd hb hble
      rw [sdiff_leftoverVerts_eq_fullVerts hnd] at hle
      refine ⟨?_, ?_⟩
      · intro p hp
        rw [List.mem_singleton.mp hp]
        exact ⟨hvs ▸ leftoverVerts_subset_toFinset vs b, hvs ▸ fullVerts_subset_toFinset vs b, hle⟩
      · simp [pairs, (disjoint_fullVerts_leftoverVerts hnd b).symm]
    have hrspec := hroute.spec G X pairs cfg.Δ cfg.L 100 z hX hGloop hcfg.hΔ_pos hdegG hcfg.hL
      hXL (by decide) hpairs
    dsimp only [pairs] at hrspec ⊢
    cases hres : route G X [(leftoverVerts vs b, fullVerts vs b)] cfg.Δ cfg.L 100 z with
    | cut U =>
      rw [hres] at hrspec
      exact hrspec
    | matched matchings emb =>
      rw [hres] at hrspec
      dsimp only
      have hrc : RoutedCall.Valid G X (routeCong cfg.Δ 100 cfg.L) z
          ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩ :=
        routedCall_valid_of_matched hpairs hrspec
      have hmlen : matchings.length = 1 := by simpa [pairs] using hrspec.1
      cases matchings with
      | nil => simp at hmlen
      | cons m rest =>
        cases rest with
        | cons _ _ => simp at hmlen
        | nil =>
          have hmspec := hrspec.2.1 0 (by simp)
          simp only [List.getD_cons_zero, List.getElem_cons_zero] at hmspec
          have hle := card_leftoverVerts_le_card_sdiff hnd hb hble
          rw [sdiff_leftoverVerts_eq_fullVerts hnd] at hle
          have hcf := completeMatchingFake_spec hle hmspec.1 hmspec.2.1 hmspec.2.2
          set M_Z := m ++ completeMatchingFake (leftoverVerts vs b) (fullVerts vs b) m
          have hcw : callsWitnessEdges (callsBC ++
              [⟨[m].flatten, emb, completeBatchFake pairs [m]⟩]) =
              callsWitnessEdges callsBC ++ M_Z := by
            simp [callsWitnessEdges, completeBatchFake, pairs, M_Z]
          refine ⟨by simp, fun c hc => by rw [List.mem_singleton.mp hc]; exact hrc, ?_⟩
          rw [hcw, ← hvs]
          refine isExpansionExpanderOn_of_blockSplit_injection hnd hγ0 hγ1 hfull ?_
            hcf.2.2.2.2.2.1 hcf.2.2.2.2.2.2.2
          intro e he
          rcases List.mem_append.mp he with h | h
          · exact hmspec.1 e h
          · exact hcf.2.1 e h
  · simp only [hZne, ↓reduceIte]
    have hZempty : leftoverVerts vs b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZne
    have hFX : fullVerts vs b = X := by
      rw [← hvs, ← sdiff_leftoverVerts_eq_fullVerts hnd b, hZempty, Finset.sdiff_empty]
    have hcw : callsWitnessEdges (callsBC ++ []) = callsWitnessEdges callsBC := by
      simp [callsWitnessEdges]
    refine ⟨by simp, by simp, ?_⟩
    rw [hcw, ← hFX]
    exact IsExpansionExpanderOn.mono (by linarith) hfull

/-! ### Full specification of `OneShot` -/

/-- **`OneShot` specification**: for `1 ≤ q ≤ r`, on any valid graph `G` and vertex
set `X ⊆ Finset.range G.n` (loopless inside `X`, max degree `≤ Δ`, size `2 ≤ |X| ≤ N` for `q = 1`
or `N ^ (q - 1) / 2 ≤ |X| ≤ N ^ q` for `q ≥ 2`), `oneShot` returns either a failed-router cut
or an induced `1 / P_q`-expander on at least `11 / 12` of `X`. -/
theorem oneShot_spec {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    (hq1 : 1 ≤ q) (hqr : q ≤ r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud cfg.α)
    {subCore : Graph → Finset ℕ → CoreResult}
    (hsubCore : 2 ≤ q → ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid →
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ cfg.N ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ cfg.Δ) →
      CoreSpec cfg (q - 1) W Y (subCore W Y))
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGvalid : G.IsValid) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ)
    (hsize : (q = 1 → 2 ≤ X.card ∧ X.card ≤ cfg.N) ∧
      (2 ≤ q → cfg.N ^ (q - 1) / 2 ≤ X.card ∧ X.card ≤ cfg.N ^ q)) :
    OneShotSpec cfg q G X (oneShot cfg route cloud q subCore G X) := by
  set vs := X.sort (· ≤ ·)
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hvs : vs.toFinset = X := by
    ext v; simp [vs]
  have hvslen : vs.length = X.card := Finset.length_sort (· ≤ ·)
  set b := if q = 1 then 1 else cfg.N ^ (q - 1) / 2
  set k := numFullBlocks vs b
  set z := X.card / cfg.D q
  -- Establish `0 < b`, `b ≤ vs.length`, `1 ≤ k`, `2 ≤ X.card`, `X.card < 2 ^ cfg.L`.
  have hXleNq : X.card ≤ cfg.N ^ q := by
    by_cases hq : q = 1
    · subst hq; simpa using (hsize.1 rfl).2
    · exact (hsize.2 (by omega)).2
  have hXL : X.card < 2 ^ cfg.L := lt_of_le_of_lt hXleNq (hcfg.hNq_lt_two_pow hqr)
  have hb_params : 0 < b ∧ b ≤ vs.length ∧ 1 ≤ k ∧ 2 ≤ X.card := by
    by_cases hq : q = 1
    · have h1 := hsize.1 hq
      have hb1 : b = 1 := by simp [b, hq]
      have hk_eq : k = vs.length := by simp [k, hb1, numFullBlocks]
      exact ⟨by omega, by omega, by omega, h1.1⟩
    · have hq2 : 2 ≤ q := by omega
      have h2 := hsize.2 hq2
      have hbe : b = cfg.N ^ (q - 1) / 2 := by simp [b, hq]
      have hsp := stepA_block_params hnd hq2 hcfg.hNpos hcfg.hN4
        (by rw [hvslen]; exact h2.1) (by rw [hvslen]; exact h2.2)
      obtain ⟨m, hm⟩ := hcfg.hN4
      have hm1 : 1 ≤ m := by have := hcfg.hNpos; omega
      have hpow4 : 4 ≤ cfg.N ^ (q - 1) := by
        calc 4 ≤ cfg.N := by omega
          _ = cfg.N ^ 1 := (pow_one _).symm
          _ ≤ cfg.N ^ (q - 1) := Nat.pow_le_pow_right hcfg.hNpos (by omega)
      have hb2 : 2 ≤ b := by rw [hbe]; omega
      exact ⟨by rw [hbe]; exact hsp.1, by rw [hbe, hvslen]; exact h2.1,
        by show 1 ≤ numFullBlocks vs b; rw [hbe]; exact hsp.2.2.1, by omega⟩
  obtain ⟨hb_pos, hble, hk1, hX2⟩ := hb_params
  have hPprev_pos : (0 : ℝ) < cfg.P (q - 1) := Nat.cast_pos.mpr (hcfg.hP_pos (by omega))
  have hβ0 : 0 ≤ 1 / (2 * (cfg.P (q - 1) : ℝ)) := by positivity
  have hβ1 : 1 / (2 * (cfg.P (q - 1) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ cfg.P (q - 1) := by exact_mod_cast hcfg.hP_pos (by omega)
    linarith
  -- Step B outcome: either a cut, or `callsB` with `callsB.length ≤ 49 * cfg.L + 2` and every block
  -- expanding by `1 / (2 * P (q - 1))`.
  have hstepB :
      match (if q = 1 then Sum.inr [] else stepB cfg route G X vs b k z subCore) with
      | Sum.inl U => RouteCutSpec G X 100 z U
      | Sum.inr callsB =>
          callsB.length ≤ 49 * cfg.L + 2 ∧
          (∀ c ∈ callsB, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
          ∀ i < k, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
            (blockSet vs b i) (1 / (2 * (cfg.P (q - 1) : ℝ))) := by
    by_cases hq : q = 1
    · simp only [hq, ↓reduceIte]
      have hb1 : b = 1 := by simp [b, hq]
      refine ⟨by simp, by simp, fun i hi => ?_⟩
      have hcard : (blockSet vs b i).card ≤ 1 := by
        rw [card_blockSet hnd hi, hb1]
      exact isExpansionExpanderOn_of_card_le_one _ hcard _
    · simp only [hq, ↓reduceIte]
      have hq2 : 2 ≤ q := by omega
      have h2 := hsize.2 hq2
      have hbe : b = cfg.N ^ (q - 1) / 2 := by simp [b, hq]
      have hsp := stepA_block_params hnd hq2 hcfg.hNpos hcfg.hN4
        (by rw [hvslen]; exact h2.1) (by rw [hvslen]; exact h2.2)
      have hb_even : Even b := hbe ▸ hsp.2.1
      have hb_le : b ≤ cfg.N ^ (q - 1) := by rw [hbe]; exact Nat.div_le_self _ 2
      exact stepB_spec hcfg hq2 hqr hroute hX hGloop hdegG hXL hnd hvs hb_pos hb_even hb_le
        (hsubCore hq2)
  unfold oneShot
  dsimp only
  change OneShotSpec cfg q G X (match (if q = 1 then Sum.inr []
      else stepB cfg route G X vs b k z subCore) with
    | Sum.inl U => .cut U
    | Sum.inr callsB =>
        match stepCMacro cfg route cloud G X vs b k z with
        | Sum.inl U => .cut U
        | Sum.inr callsC =>
            match stepCLeftover cfg route G X vs b z with
            | Sum.inl U => .cut U
            | Sum.inr callsZ =>
                .expander (removeFake G.n G.edges (callsFakeEdges (callsB ++ callsC ++ callsZ))
                  X (12 / (cfg.P q : ℝ))))
  cases hB : (if q = 1 then Sum.inr [] else stepB cfg route G X vs b k z subCore) with
  | inl U =>
    rw [hB] at hstepB
    exact hstepB
  | inr callsB =>
    rw [hB] at hstepB
    dsimp only at hstepB ⊢
    have hstepC := stepCMacro_spec hcfg hroute hcloud (z := z) hX hGloop hdegG hXL hnd hvs hb_pos hk1
      hβ0 hβ1 hstepB.2.2
    cases hC : stepCMacro cfg route cloud G X vs b k z with
    | inl U =>
      rw [hC] at hstepC
      exact hstepC
    | inr callsC =>
      rw [hC] at hstepC
      dsimp only at hstepC ⊢
      have hγ_eq : cfg.α * (1 / (2 * (cfg.P (q - 1) : ℝ))) / 10 =
          cfg.α / (20 * (cfg.P (q - 1) : ℝ)) := by ring
      rw [hγ_eq] at hstepC
      have hγ0 : 0 ≤ cfg.α / (20 * (cfg.P (q - 1) : ℝ)) := by
        have := hcfg.hα0; positivity
      have hγ1 : cfg.α / (20 * (cfg.P (q - 1) : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have h1 : (1 : ℝ) ≤ cfg.P (q - 1) := by exact_mod_cast hcfg.hP_pos (by omega)
        have h2 := hcfg.hα1
        nlinarith
      have hstepZ := stepCLeftover_spec hcfg hroute (z := z) hX hGloop hdegG hXL hnd hvs hb_pos hble
        hγ0 hγ1 hstepC.2.2
      cases hZ : stepCLeftover cfg route G X vs b z with
      | inl U =>
        rw [hZ] at hstepZ
        exact hstepZ
      | inr callsZ =>
        rw [hZ] at hstepZ
        dsimp only at hstepZ ⊢
        set callsAll := callsB ++ callsC ++ callsZ
        have hlen_all : callsAll.length ≤ cfg.Δ := by
          have hΔ := hcfg.hΔ
          simp only [callsAll, List.length_append]
          omega
        have hvalid_all : ∀ c ∈ callsAll, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z := by
          intro c hc
          simp only [callsAll, List.mem_append] at hc
          rcases hc with (h1 | h2) | h3
          · exact hstepB.2.1 c h1
          · exact hstepC.2.1 c h2
          · exact hstepZ.2.1 c h3
        have hwit_exp : (Graph.mk G.n (callsWitnessEdges callsAll)).IsExpansionExpanderOn X
            (cfg.α / (40 * (cfg.P (q - 1) : ℝ))) := by
          have hdiv : cfg.α / (20 * (cfg.P (q - 1) : ℝ)) / 2 =
              cfg.α / (40 * (cfg.P (q - 1) : ℝ)) := by ring
          rw [← hdiv]
          exact hstepZ.2.2
        exact stepD_removeFake hcfg hq1 hqr hX hGvalid hX2 hdegG hlen_all hvalid_all hwit_exp

end MinCostFlow.ExpanderDecomp
