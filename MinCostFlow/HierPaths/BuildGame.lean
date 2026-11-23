module

public import MinCostFlow.ExpanderDecomp.Rounds
public import MinCostFlow.HierPaths.BuildShift
public import MinCostFlow.HierPaths.BuildPad
import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExpanderDecomp.Injection
import Mathlib.Tactic.Linarith

/-!
# The game of one child

The child construction (`lemma_3`) plays a cut-matching game on each child `Y` of a group. The game
graph of `Y` has the local vertices `0, …, s − 1` and gains one perfect matching per round. This
file proves the facts about one child's game that do not depend on the other children.

* `witness_valid`, `witness_loopless`, `witness_deg_le`: after `t` perfect matchings the game
  graph is valid, loopless and has degree at most `t`, as the core player needs.
* `game_rounds_lt`: if in every round the matching crosses a balanced sparse cut of the game graph
  so far (the cut that the core returned), the game lasts fewer than `49 L + 1` rounds when
  `s < 2^L` (`ExpanderDecomp.round_bound_nat`).
* `perfect_of_route`: a full matching that the router returns between the shifted bisection
  `(C', V \ C')` is, shifted back, a perfect matching of `V = range s` with no edge inside `C'`.
* `childGraph_expansion`: adding a matching that injects `V \ S` into `S` to a game graph in which
  `S` has expansion `1/P` gives a child host with expansion at least `1/(2P)` on all of `V`
  (`ExpanderDecomp.isExpansionExpanderOn_of_injection`), and degree at most `t + 1`.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Expander

/-! ### Degrees of a list of edges -/

private theorem filter_len_eq_count (E : List (ℕ × ℕ)) (v : ℕ) :
    (E.filter fun e => e.1 = v).length + (E.filter fun e => e.2 = v).length =
      (E.flatMap fun e => [e.1, e.2]).count v := by
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.filter_cons, List.flatMap_cons, List.count_append, List.count_cons,
      List.count_nil]
    rw [← ih]
    by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v <;> simp [h1, h2] <;> omega

/-- The edges of a witness graph built from perfect matchings on `range s` have both ends below
`s`. -/
theorem witness_valid {s t : ℕ} {M : ℕ → List (ℕ × ℕ)}
    (hM : ∀ j < t, IsPerfectMatchingOn (Finset.range s) (M j)) :
    (Graph.mk s (witnessEdges M t)).IsValid := by
  induction t with
  | zero => intro e he; simp [witnessEdges] at he
  | succ t ih =>
    intro e he
    simp only [witnessEdges, List.mem_append] at he
    rcases he with he | he
    · exact ih (fun j hj => hM j (by omega)) e he
    · have h := (hM t (by omega)).1 e he
      simpa using h

/-- A perfect matching has no loops. -/
private theorem loopless_of_nodup {E : List (ℕ × ℕ)} (h : (E.flatMap fun e => [e.1, e.2]).Nodup) :
    ∀ e ∈ E, e.1 ≠ e.2 := by
  induction E with
  | nil => simp
  | cons a E ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, not_or] at h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1.1
    · exact ih h.2.2 e he

/-- The witness graph of perfect matchings has no loops. -/
theorem witness_loopless {s t : ℕ} {M : ℕ → List (ℕ × ℕ)}
    (hM : ∀ j < t, IsPerfectMatchingOn (Finset.range s) (M j)) :
    (Graph.mk s (witnessEdges M t)).IsLoopless := by
  induction t with
  | zero => intro e he; simp [witnessEdges] at he
  | succ t ih =>
    intro e he
    simp only [witnessEdges, List.mem_append] at he
    rcases he with he | he
    · exact ih (fun j hj => hM j (by omega)) e he
    · exact loopless_of_nodup (hM t (by omega)).2.1 e he

/-- After `t` perfect matchings every vertex has degree at most `t`. -/
theorem witness_deg_le {s t : ℕ} {M : ℕ → List (ℕ × ℕ)}
    (hM : ∀ j < t, IsPerfectMatchingOn (Finset.range s) (M j)) (v : ℕ) :
    (Graph.mk s (witnessEdges M t)).deg v ≤ t := by
  unfold Graph.deg Graph.degIn
  rw [inside_verts_of_isValid (witness_valid hM)]
  simp only
  rw [filter_len_eq_count]
  induction t with
  | zero => simp [witnessEdges]
  | succ t ih =>
    simp only [witnessEdges, List.flatMap_append, List.count_append]
    have h1 := ih (fun j hj => hM j (by omega))
    have h2 := List.nodup_iff_count_le_one.mp (hM t (by omega)).2.1 v
    omega

/-! ### The round bound -/

/-- The condition of one round of the game: the matching `M j` crosses a set `C` with
`|V| ≤ 4|C|`, no edge of `M j` lies inside `C`, and the game graph of the earlier rounds has at
most `|V|/100` edges across `C`. -/
@[expose] def RoundCut (s : ℕ) (M : ℕ → List (ℕ × ℕ)) (j : ℕ) : Prop :=
  ∃ C ⊆ Finset.range s, s ≤ 4 * C.card ∧ (∀ e ∈ M j, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
    100 * (Graph.mk s (witnessEdges M j)).cutIn (Finset.range s) C ≤ s

/-- **The round bound of the cut-matching game.** A game on `range s`,
`1 ≤ s < 2^L`,
whose rounds `j < t` are perfect matchings that meet `RoundCut`, has `t < 49 L + 1`. -/
theorem game_rounds_lt {s L t : ℕ} {M : ℕ → List (ℕ × ℕ)} (hs : 1 ≤ s) (hsL : s < 2 ^ L)
    (hM : ∀ j < t, IsPerfectMatchingOn (Finset.range s) (M j))
    (hcut : ∀ j < t, RoundCut s M j) : t < 49 * L + 1 := by
  apply round_bound_nat (n := s) (V := Finset.range s) ⟨0, by simp; omega⟩ (by simpa using hsL) hM
  intro j hj
  obtain ⟨C, hC, h1, h2, h3⟩ := hcut j hj
  exact ⟨C, hC, by simpa using h1, h2, by simpa using h3⟩

/-- A core cut `U` of the game graph gives the round condition for a matching that crosses the
padded smaller side of `U`. -/
theorem roundCut_of_core {s j : ℕ} {M : ℕ → List (ℕ × ℕ)} {U : Finset ℕ}
    (hU : U ⊆ Finset.range s) (h1 : s ≤ 4 * U.card) (h2 : s ≤ 4 * (Finset.range s \ U).card)
    (h3 : 100 * (Graph.mk s (witnessEdges M j)).cut U ≤ s)
    (hcross : ∀ e ∈ M j, ¬ (e.1 ∈ padHalf s (smallerSide (Finset.range s) U) ∧
      e.2 ∈ padHalf s (smallerSide (Finset.range s) U))) :
    RoundCut s M j := by
  refine ⟨smallerSide (Finset.range s) U, smallerSide_subset hU, ?_, ?_, ?_⟩
  · have := (card_smallerSide hU).2
    rcases le_total U.card (Finset.range s \ U).card with h | h
    · rw [min_eq_left h] at this; omega
    · rw [min_eq_right h] at this; omega
  · intro e he hin
    exact hcross e he ⟨subset_padHalf _ _ hin.1, subset_padHalf _ _ hin.2⟩
  · unfold smallerSide
    have hcut : (Graph.mk s (witnessEdges M j)).cut U =
        (Graph.mk s (witnessEdges M j)).cutIn (Finset.range s) U := rfl
    split_ifs
    · rw [← hcut]; exact h3
    · rw [cutIn_sdiff _ _ _ hU, ← hcut]; exact h3

/-! ### Matchings returned by the router -/

/-- Subtract `o` from both ends of every edge. -/
@[expose] def unshiftEdges (o : ℕ) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  E.map fun e => (e.1 - o, e.2 - o)

/-- Shifting back a list whose ends are at least `o` and shifting again gives the list back. -/
theorem shiftEdges_unshiftEdges {o : ℕ} {E : List (ℕ × ℕ)} (h : ∀ e ∈ E, o ≤ e.1 ∧ o ≤ e.2) :
    shiftEdges o (unshiftEdges o E) = E := by
  unfold shiftEdges unshiftEdges
  rw [List.map_map]
  conv_rhs => rw [← List.map_id E]
  apply List.map_congr_left
  intro e he
  have := h e he
  simp only [Function.comp_apply, id]
  ext <;> simp <;> omega

/-- **A full router matching is a perfect matching.** Let `C' ⊆ range s` have `s/2` vertices,
`s` even, and let `Mh` match `shiftSet o C'` into `shiftSet o (range s \ C')` with distinct first
ends, distinct second ends and `s/2` edges. Then `Mh` shifted back is a perfect matching of
`range s` with no edge inside `C'`, and `Mh` is that matching shifted again. -/
theorem perfect_of_route {s o : ℕ} {C' : Finset ℕ} (hC' : C' ⊆ Finset.range s)
    (hcard : 2 * C'.card = s) {Mh : List (ℕ × ℕ)}
    (hends : ∀ e ∈ Mh, e.1 ∈ shiftSet o C' ∧ e.2 ∈ shiftSet o (Finset.range s \ C'))
    (hnd1 : (Mh.map Prod.fst).Nodup) (hnd2 : (Mh.map Prod.snd).Nodup)
    (hlen : Mh.length = C'.card) :
    IsPerfectMatchingOn (Finset.range s) (unshiftEdges o Mh) ∧
      (∀ e ∈ unshiftEdges o Mh, ¬ (e.1 ∈ C' ∧ e.2 ∈ C')) ∧
      shiftEdges o (unshiftEdges o Mh) = Mh := by
  have hloc : ∀ e ∈ Mh, ∃ a ∈ C', ∃ b ∈ Finset.range s \ C', e = (o + a, o + b) := by
    intro e he
    obtain ⟨h1, h2⟩ := hends e he
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp h1
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp h2
    exact ⟨a, ha, b, hb, Prod.ext hea.symm heb.symm⟩
  have hge : ∀ e ∈ Mh, o ≤ e.1 ∧ o ≤ e.2 := by
    intro e he
    obtain ⟨a, _, b, _, rfl⟩ := hloc e he
    simp
  have hshift := shiftEdges_unshiftEdges hge
  have hlocal : ∀ e ∈ unshiftEdges o Mh, e.1 ∈ C' ∧ e.2 ∈ Finset.range s \ C' := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := hloc f hf
    simp [ha, Finset.mem_sdiff.mp hb]
  have hinj : ∀ x y : ℕ, o ≤ x → o ≤ y → x - o = y - o → x = y := by intro x y hx hy h; omega
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
  set E := unshiftEdges o Mh
  have hElen : E.length = C'.card := by simp [E, unshiftEdges, hlen]
  -- the first ends are exactly `C'` and the second ends exactly `range s \ C'`
  have hfst : (E.map Prod.fst).toFinset = C' := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact (hlocal e he).1
    · rw [List.toFinset_card_of_nodup hnd1', List.length_map, hElen]
  have hsnd : (E.map Prod.snd).toFinset = Finset.range s \ C' := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact (hlocal e he).2
    · rw [List.toFinset_card_of_nodup hnd2', List.length_map, hElen,
        Finset.card_sdiff_of_subset hC', Finset.card_range]
      omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hshift⟩
  · intro e he
    have h := hlocal e he
    exact ⟨hC' h.1, (Finset.mem_sdiff.mp h.2).1⟩
  · -- the ends: first ends distinct, second ends distinct, and the two sets disjoint
    have hgen : ∀ (F : List (ℕ × ℕ)), (F.map Prod.fst).Nodup → (F.map Prod.snd).Nodup →
        (∀ e ∈ F, e.1 ∈ C' ∧ e.2 ∈ Finset.range s \ C') →
        (F.flatMap fun e => [e.1, e.2]).Nodup := by
      intro F
      induction F with
      | nil => simp
      | cons a F ih =>
        intro h1 h2 h3
        simp only [List.map_cons, List.nodup_cons, List.mem_map] at h1 h2
        have ha := h3 a List.mem_cons_self
        have hF := fun e he => h3 e (List.mem_cons_of_mem _ he)
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
          List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and]
        refine ⟨⟨fun h => (Finset.mem_sdiff.mp ha.2).2 (h ▸ ha.1), ?_⟩, ?_, ih h1.2 h2.2 hF⟩
        · intro e he
          refine ⟨fun h => h1.1 ⟨e, he, h.symm⟩, fun h => ?_, by simp⟩
          exact (Finset.mem_sdiff.mp (hF e he).2).2 (by rw [← h]; exact ha.1)
        · intro e he
          refine ⟨fun h => ?_, fun h => h2.1 ⟨e, he, h.symm⟩, by simp⟩
          exact (Finset.mem_sdiff.mp ha.2).2 (by rw [h]; exact (hF e he).1)
    exact hgen E hnd1' hnd2' hlocal
  · intro u hu
    by_cases huC : u ∈ C'
    · rw [← hfst] at huC
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp huC)
      exact ⟨e, he, Or.inl rfl⟩
    · have : u ∈ Finset.range s \ C' := Finset.mem_sdiff.mpr ⟨hu, huC⟩
      rw [← hsnd] at this
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp this)
      exact ⟨e, he, Or.inr rfl⟩
  · intro e he hin
    exact (Finset.mem_sdiff.mp (hlocal e he).2).2 hin.2

/-! ### The child host -/

/-- **The child host.** Let `S ⊆ range s` have expansion at least `1/P` in the game graph
`⟨s, W⟩`, with `P ≥ 1`. Let `Inj` be a list of edges from `range s \ S` into `S` with distinct
second ends whose first ends cover `range s \ S`. Then `⟨s, W ++ Inj⟩` has expansion at least
`1/(2P)` on `range s`. -/
theorem childGraph_expansion {s P : ℕ} (hP : 1 ≤ P) {W Inj : List (ℕ × ℕ)} {S : Finset ℕ}
    (hS : S ⊆ Finset.range s) (hexp : (Graph.mk s W).IsExpansionExpanderOn S (1 / (P : ℝ)))
    (hInj : ∀ e ∈ Inj, e.1 ∈ Finset.range s ∧ e.1 ∉ S ∧ e.2 ∈ S)
    (hsnd : (Inj.map Prod.snd).Nodup)
    (hcover : ∀ v ∈ Finset.range s, v ∉ S → ∃ e ∈ Inj, e.1 = v) :
    (Graph.mk s (W ++ Inj)).IsExpansionExpanderOn (Finset.range s) (1 / (2 * P : ℝ)) := by
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have h0 : (0 : ℝ) ≤ 1 / (P : ℝ) := by positivity
  have h1 : 1 / (P : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hP'
  have h := isExpansionExpanderOn_of_injection h0 h1 hS hexp hInj hsnd hcover
  have heq : 1 / (P : ℝ) / 2 = 1 / (2 * P : ℝ) := by ring
  rw [heq] at h
  exact h

/-- In the child host, every vertex has degree at most `t + 1`: at most `t` from the game graph
and at most one from the injection, whose ends are distinct. -/
theorem childGraph_deg_le {s t : ℕ} {M : ℕ → List (ℕ × ℕ)}
    (hM : ∀ j < t, IsPerfectMatchingOn (Finset.range s) (M j)) {Inj : List (ℕ × ℕ)}
    (hInj : ∀ e ∈ Inj, e.1 < s ∧ e.2 < s)
    (hnd : (Inj.flatMap fun e => [e.1, e.2]).Nodup) (v : ℕ) :
    (Graph.mk s (witnessEdges M t ++ Inj)).deg v ≤ t + 1 := by
  have hval : (Graph.mk s (witnessEdges M t ++ Inj)).IsValid := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact witness_valid hM e h
    · exact hInj e h
  have hW := witness_deg_le hM v
  unfold Graph.deg Graph.degIn at hW ⊢
  rw [inside_verts_of_isValid hval]
  rw [inside_verts_of_isValid (witness_valid hM)] at hW
  simp only at hW ⊢
  rw [filter_len_eq_count] at hW ⊢
  rw [List.flatMap_append, List.count_append]
  have := List.nodup_iff_count_le_one.mp hnd v
  omega

end MinCostFlow.HierPaths
