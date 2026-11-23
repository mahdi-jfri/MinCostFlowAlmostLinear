module

public import MinCostFlow.Expander.GraphHelpers
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Push-relabel expander pruning state, invariants, and level sweep

Defines the configuration, state, invariants, initial state, level-sweep lemma,
and termination/work potential for deterministic push-relabel expander pruning
used in `ExpanderPruning.lean`.
-/

public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited

/-! ### Incident non-loop half-edges -/

/-- Collects non-loop half-edges incident to vertex `u` in edge list `L` starting at index `k`.
Each triple `(idx, dir, w)` records the edge index `idx`, direction (`false` for `u → w` along
`e.1 → e.2`, `true` for `e.2 → e.1`), and the opposite endpoint `w ≠ u`. -/
@[expose] def incEdgesAux (u : ℕ) : ℕ → List (ℕ × ℕ) → List (ℕ × Bool × ℕ)
  | _, [] => []
  | idx, (a, b) :: rest =>
      let tail := incEdgesAux u (idx + 1) rest
      if a = b then tail
      else if a = u then (idx, false, b) :: tail
      else if b = u then (idx, true, a) :: tail
      else tail

/-- Directional flow on edge index `idx`: `+flow idx` in forward direction `false`,
`-flow idx` in reverse direction `true`. -/
@[expose] def flowDir (flow : ℕ → ℤ) (idx : ℕ) (dir : Bool) : ℤ :=
  if dir then -(flow idx) else flow idx

@[simp]
lemma flowDir_not (flow : ℕ → ℤ) (idx : ℕ) (dir : Bool) :
    flowDir flow idx (!dir) = -(flowDir flow idx dir) := by
  cases dir <;> simp [flowDir]

lemma incEdgesAux_idx_ge {u k : ℕ} {L : List (ℕ × ℕ)} {p : ℕ × Bool × ℕ}
    (hp : p ∈ incEdgesAux u k L) : k ≤ p.1 ∧ p.1 < k + L.length := by
  induction L generalizing k with
  | nil => simp [incEdgesAux] at hp
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [incEdgesAux] at hp
    split_ifs at hp with h1 h2 h3
    · have := ih hp; simp only [List.length_cons]; omega
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · have := ih hp; simp only [List.length_cons]; omega
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · have := ih hp; simp only [List.length_cons]; omega
    · have := ih hp; simp only [List.length_cons]; omega

lemma incEdgesAux_ne_self {u k : ℕ} {L : List (ℕ × ℕ)} {p : ℕ × Bool × ℕ}
    (hp : p ∈ incEdgesAux u k L) : p.2.2 ≠ u := by
  induction L generalizing k with
  | nil => simp [incEdgesAux] at hp
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [incEdgesAux] at hp
    split_ifs at hp with h1 h2 h3
    · exact ih hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact fun h => h1 (h2.trans h.symm)
      · exact ih hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact fun h => h1 (h.trans h3.symm)
      · exact ih hp
    · exact ih hp

lemma incEdgesAux_nodup_idx (u k : ℕ) (L : List (ℕ × ℕ)) :
    ((incEdgesAux u k L).map (·.1)).Nodup := by
  induction L generalizing k with
  | nil => simp [incEdgesAux]
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [incEdgesAux]
    split_ifs
    · exact ih (k + 1)
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih (k + 1)⟩
      rcases List.mem_map.mp hmem with ⟨q, hq, hqeq⟩
      have := (incEdgesAux_idx_ge hq).1
      omega
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih (k + 1)⟩
      rcases List.mem_map.mp hmem with ⟨q, hq, hqeq⟩
      have := (incEdgesAux_idx_ge hq).1
      omega
    · exact ih (k + 1)

lemma incEdgesAux_nodup (u k : ℕ) (L : List (ℕ × ℕ)) :
    (incEdgesAux u k L).Nodup :=
  (incEdgesAux_nodup_idx u k L).of_map _

lemma incEdgesAux_mem_endpoints {S : Finset ℕ} {u k : ℕ} {L : List (ℕ × ℕ)}
    (hmem : ∀ e ∈ L, e.1 ∈ S ∧ e.2 ∈ S)
    {p : ℕ × Bool × ℕ} (hp : p ∈ incEdgesAux u k L) :
    u ∈ S ∧ p.2.2 ∈ S := by
  induction L generalizing k with
  | nil => simp [incEdgesAux] at hp
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    have heS := hmem (a, b) (by simp)
    have hrest : ∀ e' ∈ rest, e'.1 ∈ S ∧ e'.2 ∈ S := fun e' he' => hmem e' (by simp [he'])
    simp only [incEdgesAux] at hp
    split_ifs at hp with h1 h2 h3
    · exact ih hrest hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · subst h2; exact heS
      · exact ih hrest hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · subst h3; exact ⟨heS.2, heS.1⟩
      · exact ih hrest hp
    · exact ih hrest hp

lemma sum_incEdgesAux_length (S : Finset ℕ) (k : ℕ) (L : List (ℕ × ℕ)) :
    ∑ u ∈ S, (incEdgesAux u k L).length =
      (L.map fun e =>
        if e.1 = e.2 then 0
        else (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0)).sum := by
  induction L generalizing k with
  | nil => simp [incEdgesAux]
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [List.map_cons, List.sum_cons, ← ih (k + 1)]
    have hpt : ∀ u, (incEdgesAux u k ((a, b) :: rest)).length =
        (if a = b then 0 else if a = u then 1 else if b = u then 1 else 0) +
        (incEdgesAux u (k + 1) rest).length := by
      intro u
      simp only [incEdgesAux]
      split_ifs <;> simp <;> omega
    simp_rw [hpt, Finset.sum_add_distrib]
    congr 1
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, ite_false]
      have h1 : ∀ x ∈ S, (if a = x then (1 : ℕ) else if b = x then 1 else 0) =
          (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
        intro x _
        by_cases ha : a = x <;> by_cases hb : b = x
        · exact False.elim (hab (ha.trans hb.symm))
        · simp [ha, hb, eq_comm]
        · simp [ha, hb, eq_comm]
        · simp [ha, hb, eq_comm]
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']

lemma sum_incEdgesAux_length_le (S : Finset ℕ) (k : ℕ) (L : List (ℕ × ℕ)) :
    ∑ u ∈ S, (incEdgesAux u k L).length ≤ 2 * L.length := by
  rw [sum_incEdgesAux_length]
  calc (L.map fun e =>
        if e.1 = e.2 then 0
        else (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0)).sum
      ≤ (L.map fun _ => 2).sum := by
        apply sum_map_le_sum_map
        intro e _
        split_ifs <;> omega
    _ = 2 * L.length := by rw [sum_map_const]; ring

lemma filter_incEdgesAux_degIn_eq {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X)
    {u : ℕ} (hu : u ∈ R) :
    G.degIn X u - G.degIn R u =
      ((incEdgesAux u 0 (G.inside X)).filter fun p => decide (p.2.2 ∉ R)).length ∧
    G.degIn R u ≤ G.degIn X u := by
  have heq_inside : G.degIn R u =
      ((G.inside X).map fun e =>
        if e.1 ∈ R ∧ e.2 ∈ R then
          (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)
        else 0).sum := by
    rw [degIn_eq_sum_map]
    have hfilt : G.inside R = (G.inside X).filter (fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)) := by
      unfold Graph.inside
      rw [List.filter_filter]
      congr 1
      ext e
      by_cases h1 : e.1 ∈ R
      · by_cases h2 : e.2 ∈ R
        · simp [h1, h2, hRX h1, hRX h2]
        · simp [h1, h2]
      · simp [h1]
    rw [hfilt]
    clear hfilt
    induction (G.inside X) with
    | nil => simp
    | cons e t ih =>
      rw [List.filter_cons]
      by_cases hR : e.1 ∈ R ∧ e.2 ∈ R
      · have hdec : (decide (e.1 ∈ R) && decide (e.2 ∈ R)) = true := by simp [hR]
        rw [hdec]
        simp only [↓reduceIte, List.map_cons, List.sum_cons, ih, hR, and_self]
      · have hdec : (decide (e.1 ∈ R) && decide (e.2 ∈ R)) = false := by
          simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not]
          tauto
        rw [hdec]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, ih, hR, zero_add]
  have hdiff : ∀ k (L : List (ℕ × ℕ)),
      ((L.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum) -
      ((L.map fun e => if e.1 ∈ R ∧ e.2 ∈ R then
          (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0) else 0).sum) =
      ((incEdgesAux u k L).filter fun p => decide (p.2.2 ∉ R)).length ∧
      ((L.map fun e => if e.1 ∈ R ∧ e.2 ∈ R then
          (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0) else 0).sum) ≤
      ((L.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum) := by
    intro k L
    induction L generalizing k with
    | nil => simp [incEdgesAux]
    | cons e rest ih =>
      rcases e with ⟨a, b⟩
      obtain ⟨ih1, ih2⟩ := ih (k + 1)
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      dsimp only
      set S1 := (rest.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum
      set S2 := (rest.map fun e => if e.1 ∈ R ∧ e.2 ∈ R then
          (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0) else 0).sum
      set C1 := (if a = u then 1 else 0) + (if b = u then 1 else 0)
      set C2 := if a ∈ R ∧ b ∈ R then C1 else 0
      by_cases hab : a = b
      · subst hab
        have hinc : incEdgesAux u k ((a, a) :: rest) = incEdgesAux u (k + 1) rest := by
          simp [incEdgesAux]
        rw [hinc]
        by_cases haR : a ∈ R
        · have hC : C2 = C1 := by simp [C2, haR]
          rw [hC]
          omega
        · have hau : a ≠ u := fun h => haR (h ▸ hu)
          have hC1 : C1 = 0 := by simp [C1, hau]
          have hC2 : C2 = 0 := by simp [C2, haR]
          rw [hC1, hC2]
          omega
      · by_cases hau : a = u
        · subst hau
          have hba : b ≠ a := Ne.symm hab
          have hC1 : C1 = 1 := by simp [C1, hba]
          have hinc : incEdgesAux a k ((a, b) :: rest) = (k, false, b) :: incEdgesAux a (k + 1) rest := by
            simp [incEdgesAux, hab]
          rw [hinc, hC1]
          by_cases hbR : b ∈ R
          · have hC2 : C2 = 1 := by simp [C2, C1, hu, hbR, hba]
            have hf : (List.filter (fun p => decide (p.2.2 ∉ R))
                ((k, false, b) :: incEdgesAux a (k + 1) rest)).length =
                (List.filter (fun p => decide (p.2.2 ∉ R)) (incEdgesAux a (k + 1) rest)).length := by
              simp [hbR]
            rw [hC2, hf]
            omega
          · have hC2 : C2 = 0 := by simp [C2, hbR]
            have hf : (List.filter (fun p => decide (p.2.2 ∉ R))
                ((k, false, b) :: incEdgesAux a (k + 1) rest)).length =
                (List.filter (fun p => decide (p.2.2 ∉ R)) (incEdgesAux a (k + 1) rest)).length + 1 := by
              simp [hbR]
            rw [hC2, hf]
            omega
        · by_cases hbu : b = u
          · subst hbu
            have hC1 : C1 = 1 := by simp [C1, hau]
            have hinc : incEdgesAux b k ((a, b) :: rest) = (k, true, a) :: incEdgesAux b (k + 1) rest := by
              simp [incEdgesAux, hab]
            rw [hinc, hC1]
            by_cases haR : a ∈ R
            · have hC2 : C2 = 1 := by simp [C2, C1, haR, hu, hau]
              have hf : (List.filter (fun p => decide (p.2.2 ∉ R))
                  ((k, true, a) :: incEdgesAux b (k + 1) rest)).length =
                  (List.filter (fun p => decide (p.2.2 ∉ R)) (incEdgesAux b (k + 1) rest)).length := by
                simp [haR]
              rw [hC2, hf]
              omega
            · have hC2 : C2 = 0 := by simp [C2, haR]
              have hf : (List.filter (fun p => decide (p.2.2 ∉ R))
                  ((k, true, a) :: incEdgesAux b (k + 1) rest)).length =
                  (List.filter (fun p => decide (p.2.2 ∉ R)) (incEdgesAux b (k + 1) rest)).length + 1 := by
                simp [haR]
              rw [hC2, hf]
              omega
          · have hinc : incEdgesAux u k ((a, b) :: rest) = incEdgesAux u (k + 1) rest := by
              simp [incEdgesAux, hab, hau, hbu]
            have hC1 : C1 = 0 := by simp [C1, hau, hbu]
            have hC2 : C2 = 0 := by simp [C2, hC1]
            rw [hinc, hC1, hC2]
            omega
  have h1 := degIn_eq_sum_map G X u
  rw [h1, heq_inside]
  exact hdiff 0 (G.inside X)

lemma filter_incEdgesAux_mem_degIn {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X)
    {u : ℕ} (hu : u ∈ R) :
    ((incEdgesAux u 0 (G.inside X)).filter fun p => decide (p.2.2 ∈ R)).length ≤ G.degIn R u := by
  have h1 := (filter_incEdgesAux_degIn_eq (G := G) hRX hu).1
  have h2 := (filter_incEdgesAux_degIn_eq (G := G) hRX hu).2
  have htot : (incEdgesAux u 0 (G.inside X)).length =
      ((incEdgesAux u 0 (G.inside X)).filter fun p => decide (p.2.2 ∈ R)).length +
      ((incEdgesAux u 0 (G.inside X)).filter fun p => decide (p.2.2 ∉ R)).length := by
    induction (incEdgesAux u 0 (G.inside X)) with
    | nil => simp
    | cons p t ih =>
      simp only [List.filter_cons]
      by_cases hp : p.2.2 ∈ R <;> simp [hp, ih] <;> omega
  have hle : (incEdgesAux u 0 (G.inside X)).length ≤ G.degIn X u := by
    rw [degIn_eq_sum_map]
    clear h1 h2 htot
    suffices h : ∀ k (L : List (ℕ × ℕ)),
        (incEdgesAux u k L).length ≤
          (L.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum from
      h 0 (G.inside X)
    intro k L
    induction L generalizing k with
    | nil => simp [incEdgesAux]
    | cons e rest ih =>
      rcases e with ⟨a, b⟩
      have iht := ih (k + 1)
      simp only [incEdgesAux, List.map_cons, List.sum_cons]
      split_ifs <;> (try rw [List.length_cons]) <;> omega
  omega

/-! ### Flow-balance summation identity over incident half-edges -/

/-- Edge contribution to the balance identity for vertex `u`:
if the opposite endpoint `w` is still in `R`, `-flowDir flow idx dir`; if `w ∉ R` (so `w ∈ P`),
`+C_cap`. -/
@[expose] def edgeContrib (inR : ℕ → Bool) (flow : ℕ → ℤ) (C_cap : ℕ) (p : ℕ × Bool × ℕ) : ℤ :=
  if inR p.2.2 then -(flowDir flow p.1 p.2.1) else (C_cap : ℤ)

/-- Edge cut count between `S` and `X \ R` in an edge list `L`, where `S ⊆ R ⊆ X`. -/
@[expose] def crossCutList (inR : ℕ → Bool) (S : Finset ℕ) (L : List (ℕ × ℕ)) : ℕ :=
  (L.filter fun e =>
    decide ((e.1 ∈ S ∧ !inR e.2) ∨ (e.2 ∈ S ∧ !inR e.1))).length

/-- Net flow leaving `S` to `R \ S` across edges in `L` starting at index `k`. -/
@[expose] def flowOutAux (inR : ℕ → Bool) (S : Finset ℕ) (flow : ℕ → ℤ) :
    ℕ → List (ℕ × ℕ) → ℤ
  | _, [] => 0
  | idx, (a, b) :: rest =>
      let tail := flowOutAux inR S flow (idx + 1) rest
      if a = b then tail
      else if a ∈ S ∧ inR b ∧ b ∉ S then flow idx + tail
      else if b ∈ S ∧ inR a ∧ a ∉ S then -(flow idx) + tail
      else tail

lemma sum_edgeContrib_eq (inR : ℕ → Bool) (S : Finset ℕ) (hSR : ∀ u ∈ S, inR u = true)
    (flow : ℕ → ℤ) (C_cap k : ℕ) (L : List (ℕ × ℕ)) :
    ∑ u ∈ S, ((incEdgesAux u k L).map (edgeContrib inR flow C_cap)).sum =
      (C_cap : ℤ) * (crossCutList inR S L : ℤ) - flowOutAux inR S flow k L := by
  induction L generalizing k with
  | nil => simp [incEdgesAux, crossCutList, flowOutAux]
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    have ih' := ih (k + 1)
    have hpt : ∀ u ∈ S, ((incEdgesAux u k ((a, b) :: rest)).map (edgeContrib inR flow C_cap)).sum =
        ((incEdgesAux u (k + 1) rest).map (edgeContrib inR flow C_cap)).sum +
        (if a = b then 0
         else if a = u then edgeContrib inR flow C_cap (k, false, b)
         else if b = u then edgeContrib inR flow C_cap (k, true, a)
         else 0) := by
      intro u _
      simp only [incEdgesAux]
      split_ifs <;> simp [add_comm]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ih']
    have hterm : ∑ u ∈ S, (if a = b then (0 : ℤ)
        else if a = u then edgeContrib inR flow C_cap (k, false, b)
        else if b = u then edgeContrib inR flow C_cap (k, true, a)
        else 0) =
        (C_cap : ℤ) * (if (a ∈ S ∧ !inR b) ∨ (b ∈ S ∧ !inR a) then 1 else 0) -
        (if a = b then 0
         else if a ∈ S ∧ inR b ∧ b ∉ S then flow k
         else if b ∈ S ∧ inR a ∧ a ∉ S then -(flow k)
         else 0) := by
      by_cases hab : a = b
      · subst hab
        by_cases haS : a ∈ S
        · have haR : inR a = true := hSR a haS
          simp [haS, haR]
        · simp [haS]
      · have hsplit : ∑ u ∈ S, (if a = b then (0 : ℤ)
            else if a = u then edgeContrib inR flow C_cap (k, false, b)
            else if b = u then edgeContrib inR flow C_cap (k, true, a)
            else 0) =
            (if a ∈ S then edgeContrib inR flow C_cap (k, false, b) else 0) +
            (if b ∈ S then edgeContrib inR flow C_cap (k, true, a) else 0) := by
          have hadd : ∀ u ∈ S,
              (if a = b then (0 : ℤ)
               else if a = u then edgeContrib inR flow C_cap (k, false, b)
               else if b = u then edgeContrib inR flow C_cap (k, true, a)
               else 0) =
              (if a = u then edgeContrib inR flow C_cap (k, false, b) else 0) +
              (if b = u then edgeContrib inR flow C_cap (k, true, a) else 0) := by
            intro u _
            simp only [hab, ite_false]
            by_cases ha : a = u
            · have hb : b ≠ u := fun h => hab (ha.trans h.symm)
              simp [ha, hb]
            · by_cases hb : b = u
              · simp [ha, hb]
              · simp [ha, hb]
          rw [Finset.sum_congr rfl hadd, Finset.sum_add_distrib]
          simp
        rw [hsplit]
        by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S
        · have haR := hSR a haS
          have hbR := hSR b hbS
          simp [hab, haS, hbS, haR, hbR, edgeContrib, flowDir]
        · have haR := hSR a haS
          by_cases hbR : inR b = true
          · simp [hab, haS, hbS, haR, hbR, edgeContrib, flowDir]
          · simp [hab, haS, hbS, haR, hbR, edgeContrib]
        · have hbR := hSR b hbS
          by_cases haR : inR a = true
          · simp [hab, haS, hbS, haR, hbR, edgeContrib, flowDir]
          · simp [hab, haS, hbS, haR, hbR, edgeContrib]
        · simp [hab, haS, hbS]
    have hcut_step : (crossCutList inR S ((a, b) :: rest) : ℤ) =
        (crossCutList inR S rest : ℤ) +
          (if (a ∈ S ∧ !inR b) ∨ (b ∈ S ∧ !inR a) then 1 else 0) := by
      unfold crossCutList
      by_cases hc : (a ∈ S ∧ inR b = false) ∨ (b ∈ S ∧ inR a = false)
      · have hcd : decide ((a ∈ S ∧ !inR b) ∨ (b ∈ S ∧ !inR a)) = true := by simp [hc]
        rw [List.filter_cons, hcd]
        simp [hc]
      · have hcd : decide ((a ∈ S ∧ !inR b) ∨ (b ∈ S ∧ !inR a)) = false := by
          simp only [decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true]
          exact hc
        rw [List.filter_cons, hcd]
        simp [hc]
    have hflow_step : flowOutAux inR S flow k ((a, b) :: rest) =
        flowOutAux inR S flow (k + 1) rest +
          (if a = b then 0
           else if a ∈ S ∧ inR b ∧ b ∉ S then flow k
           else if b ∈ S ∧ inR a ∧ a ∉ S then -(flow k)
           else 0) := by
      simp only [flowOutAux]
      split_ifs <;> ring
    rw [hterm, hcut_step, hflow_step]
    ring

lemma flowOutAux_le_cutIn {G : Graph} {X R S : Finset ℕ} (inR : ℕ → Bool)
    (hinR : ∀ v, inR v = true ↔ v ∈ R) (hRX : R ⊆ X) (hSR : S ⊆ R)
    (flow : ℕ → ℤ) (C_cap : ℕ)
    (hcap : ∀ idx, idx < (G.inside X).length → -(C_cap : ℤ) ≤ flow idx ∧ flow idx ≤ (C_cap : ℤ)) :
    flowOutAux inR S flow 0 (G.inside X) ≤ (C_cap : ℤ) * (G.cutIn R S : ℤ) := by
  have hcutN : G.cutIn R S =
      ((G.inside X).map fun e =>
        if (e.1 ∈ S ∧ inR e.2 ∧ e.2 ∉ S) ∨ (e.2 ∈ S ∧ inR e.1 ∧ e.1 ∉ S) then 1 else 0).sum := by
    rw [cutIn_eq_sum_map]
    have hfilt : G.inside R = (G.inside X).filter (fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)) := by
      unfold Graph.inside
      rw [List.filter_filter]
      congr 1; ext e
      by_cases h1 : e.1 ∈ R
      · by_cases h2 : e.2 ∈ R
        · simp [h1, h2, hRX h1, hRX h2]
        · simp [h1, h2]
      · simp [h1]
    rw [hfilt]
    clear hfilt
    induction (G.inside X) with
    | nil => simp
    | cons e t ih =>
      rcases e with ⟨a, b⟩
      rw [List.filter_cons]
      by_cases hR : a ∈ R ∧ b ∈ R
      · have hdec : (decide (a ∈ R) && decide (b ∈ R)) = true := by simp [hR]
        rw [hdec]
        simp only [↓reduceIte, List.map_cons, List.sum_cons, ih]
        congr 1
        by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
          simp [haS, hbS, (hinR a).mpr hR.1, (hinR b).mpr hR.2]
      · have hf : (decide (a ∈ R) && decide (b ∈ R)) = false := by
          simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not]; tauto
        have hzero : ¬ ((a ∈ S ∧ inR b ∧ b ∉ S) ∨ (b ∈ S ∧ inR a ∧ a ∉ S)) := by
          rintro (⟨haS, hbR, _⟩ | ⟨hbS, haR, _⟩)
          · exact hR ⟨hSR haS, (hinR b).mp hbR⟩
          · exact hR ⟨(hinR a).mp haR, hSR hbS⟩
        rw [hf]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, hzero, zero_add, ih]
  have hcutR : (G.cutIn R S : ℤ) =
      ((G.inside X).map fun e =>
        if (e.1 ∈ S ∧ inR e.2 ∧ e.2 ∉ S) ∨ (e.2 ∈ S ∧ inR e.1 ∧ e.1 ∉ S) then (1 : ℤ) else 0).sum := by
    rw [hcutN]
    induction (G.inside X) with
    | nil => simp
    | cons e t ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      split_ifs <;> simp
  rw [hcutR]
  suffices h : ∀ k (L : List (ℕ × ℕ)),
      (∀ idx, k ≤ idx → idx < k + L.length → -(C_cap : ℤ) ≤ flow idx ∧ flow idx ≤ (C_cap : ℤ)) →
      flowOutAux inR S flow k L ≤
        (C_cap : ℤ) * ((L.map fun e =>
          if (e.1 ∈ S ∧ inR e.2 ∧ e.2 ∉ S) ∨ (e.2 ∈ S ∧ inR e.1 ∧ e.1 ∉ S) then (1 : ℤ) else 0).sum) by
    exact h 0 (G.inside X) (fun idx _ hi => hcap idx (by omega))
  intro k L hcapL
  induction L generalizing k with
  | nil => simp [flowOutAux]
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    have hc := hcapL k (le_refl _) (by simp)
    have hrest := ih (k + 1) (fun idx h1 h2 => hcapL idx (by omega) (by simp at h2 ⊢; omega))
    by_cases h1 : a = b
    · subst h1
      simp only [flowOutAux, List.map_cons, List.sum_cons, mul_add, ite_true]
      split_ifs with hc1 <;> [exact absurd hc1 (by tauto); simpa using hrest]
    · simp only [flowOutAux, List.map_cons, List.sum_cons, mul_add]
      split_ifs <;> first | exact hrest | linarith | tauto

lemma crossCutList_eq_volDiff {G : Graph} {X R S : Finset ℕ} (inR : ℕ → Bool)
    (hinR : ∀ v, inR v = true ↔ v ∈ R) (hRX : R ⊆ X) (hSR : S ⊆ R) :
    G.volIn X S = G.volIn R S + crossCutList inR S (G.inside X) ∧
    G.cutIn X S = G.cutIn R S + crossCutList inR S (G.inside X) := by
  have hSX : S ⊆ X := hSR.trans hRX
  have hsub : G.inside R = (G.inside X).filter (fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)) := by
    unfold Graph.inside
    rw [List.filter_filter]
    congr 1; ext e
    by_cases h1 : e.1 ∈ R
    · by_cases h2 : e.2 ∈ R
      · simp [h1, h2, hRX h1, hRX h2]
      · simp [h1, h2]
    · simp [h1]
  have hcutR : G.cutIn R S =
      ((G.inside X).map fun e =>
        if (e.1 ∈ R ∧ e.2 ∈ R) ∧ (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum := by
    rw [cutIn_eq_sum_map, hsub]
    induction (G.inside X) with
    | nil => simp
    | cons e t ih =>
      rw [List.filter_cons]
      by_cases hR : e.1 ∈ R ∧ e.2 ∈ R
      · have hdec : (decide (e.1 ∈ R) && decide (e.2 ∈ R)) = true := by simp [hR]
        rw [hdec]
        simp only [↓reduceIte, List.map_cons, List.sum_cons, ih, hR, true_and]
      · have hdec : (decide (e.1 ∈ R) && decide (e.2 ∈ R)) = false := by
          simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not]; tauto
        rw [hdec]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, ih, hR, false_and, zero_add]
  have hvolR : G.volIn R S =
      ((G.inside X).map fun e =>
        if e.1 ∈ R ∧ e.2 ∈ R then (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0) else 0).sum := by
    rw [volIn_eq_sum_map, hsub]
    induction (G.inside X) with
    | nil => simp
    | cons e t ih =>
      rw [List.filter_cons]
      by_cases hR : e.1 ∈ R ∧ e.2 ∈ R
      · have hdec : (decide (e.1 ∈ R) && decide (e.2 ∈ R)) = true := by simp [hR]
        rw [hdec]
        simp only [↓reduceIte, List.map_cons, List.sum_cons, ih, hR, and_self]
      · have hdec : (decide (e.1 ∈ R) && decide (e.2 ∈ R)) = false := by
          simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not]; tauto
        rw [hdec]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, ih, hR, zero_add]
  have hcc : crossCutList inR S (G.inside X) =
      ((G.inside X).map fun e =>
        if (e.1 ∈ S ∧ !inR e.2) ∨ (e.2 ∈ S ∧ !inR e.1) then 1 else 0).sum := by
    unfold crossCutList
    rw [length_filter_eq_sum_map]
    congr 1; ext e
    simp
  rw [volIn_eq_sum_map, hvolR, cutIn_eq_sum_map, hcutR, hcc]
  constructor <;> rw [← sum_map_add] <;> congr 1 <;> apply List.map_congr_left <;> intro e _
  · by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
    · have hR1 := hSR h1; have hR2 := hSR h2
      have hB1 := (hinR e.1).mpr hR1; have hB2 := (hinR e.2).mpr hR2
      simp [h1, h2, hR1, hR2, hB1, hB2]
    · have hR1 := hSR h1; have hB1 := (hinR e.1).mpr hR1
      by_cases hR2 : e.2 ∈ R
      · have hB2 := (hinR e.2).mpr hR2; simp [h1, h2, hR1, hR2, hB1, hB2]
      · have hB2 : inR e.2 = false := Bool.eq_false_iff.mpr fun ht => hR2 ((hinR e.2).mp ht)
        simp [h1, h2, hR1, hR2, hB1, hB2]
    · have hR2 := hSR h2; have hB2 := (hinR e.2).mpr hR2
      by_cases hR1 : e.1 ∈ R
      · have hB1 := (hinR e.1).mpr hR1; simp [h1, h2, hR1, hR2, hB1, hB2]
      · have hB1 : inR e.1 = false := Bool.eq_false_iff.mpr fun ht => hR1 ((hinR e.1).mp ht)
        simp [h1, h2, hR1, hR2, hB1, hB2]
    · by_cases hR1 : e.1 ∈ R <;> by_cases hR2 : e.2 ∈ R <;> simp [h1, h2, hR1, hR2]
  · by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
    · have hR1 := hSR h1; have hR2 := hSR h2
      have hB1 := (hinR e.1).mpr hR1; have hB2 := (hinR e.2).mpr hR2
      simp [h1, h2, hR1, hR2, hB1, hB2]
    · have hR1 := hSR h1; have hB1 := (hinR e.1).mpr hR1
      by_cases hR2 : e.2 ∈ R
      · have hB2 := (hinR e.2).mpr hR2; simp [h1, h2, hR1, hR2, hB1, hB2]
      · have hB2 : inR e.2 = false := Bool.eq_false_iff.mpr fun ht => hR2 ((hinR e.2).mp ht)
        simp [h1, h2, hR1, hR2, hB1, hB2]
    · have hR2 := hSR h2; have hB2 := (hinR e.2).mpr hR2
      by_cases hR1 : e.1 ∈ R
      · have hB1 := (hinR e.1).mpr hR1; simp [h1, h2, hR1, hR2, hB1, hB2]
      · have hB1 : inR e.1 = false := Bool.eq_false_iff.mpr fun ht => hR1 ((hinR e.1).mp ht)
        simp [h1, h2, hR1, hR2, hB1, hB2]
    · by_cases hR1 : e.1 ∈ R <;> by_cases hR2 : e.2 ∈ R <;> simp [h1, h2, hR1, hR2]

/-! ### Configuration, state, invariants, and potential -/

/-- Configuration parameters for push-relabel expander pruning on `G[X]` with initial
deleted set `B ⊆ X`. -/
structure PruneCfg where
  G : Graph
  X : Finset ℕ
  B : Finset ℕ
  C_cap : ℕ
  H : ℕ
  θ_out_nat : ℕ

@[expose] def PruneCfg.edges (cfg : PruneCfg) : List (ℕ × ℕ) :=
  cfg.G.inside cfg.X

@[expose] def PruneCfg.incEdges (cfg : PruneCfg) (u : ℕ) : List (ℕ × Bool × ℕ) :=
  incEdgesAux u 0 cfg.edges

@[expose] def PruneCfg.degX (cfg : PruneCfg) (u : ℕ) : ℕ :=
  cfg.G.degIn cfg.X u

/-- Side conditions on `PruneCfg` required by the pruning invariants. -/
@[expose] def PruneCfg.Valid (cfg : PruneCfg) : Prop :=
  cfg.G.IsValid ∧
  cfg.B ⊆ cfg.X ∧
  4 ≤ cfg.C_cap ∧
  4 * cfg.C_cap * (Nat.log 2 (2 * cfg.edges.length + 1) + 1) + 2 ≤ cfg.H ∧
  ∀ v ∈ cfg.X, v ∉ cfg.B → cfg.θ_out_nat ≤ cfg.degX v

lemma PruneCfg.valid_three_le_H {cfg : PruneCfg} (h : cfg.Valid) : 3 ≤ cfg.H := by
  have h1 := h.2.2.1
  have h2 := h.2.2.2.1
  nlinarith

/-- State of push-relabel + low-degree peeling expander pruning. -/
structure PruneState where
  inR : ℕ → Bool
  h : ℕ → ℕ
  cur : ℕ → ℕ
  abs : ℕ → ℕ
  ex : ℕ → ℕ
  degR : ℕ → ℕ
  flow : ℕ → ℤ
  active : List ℕ
  inActive : ℕ → Bool
  peelQ : List ℕ
  steps : ℕ

/-- Active vertex set `R(s)` as a `Finset ℕ`. -/
@[expose] def PruneState.Rset (cfg : PruneCfg) (s : PruneState) : Finset ℕ :=
  cfg.X.filter fun u => s.inR u

lemma PruneState.mem_Rset (cfg : PruneCfg) (s : PruneState) {u : ℕ}
    (hinR : ∀ x, s.inR x = true → x ∈ cfg.X) :
    u ∈ s.Rset cfg ↔ s.inR u = true := by
  simp only [PruneState.Rset, Finset.mem_filter, and_iff_right_iff_imp]
  exact hinR u

/-- Remaining incident non-loop volume in `R`. -/
@[expose] def volR (cfg : PruneCfg) (s : PruneState) : ℕ :=
  ∑ u ∈ cfg.X, if s.inR u then (cfg.incEdges u).length else 0

/-- Remaining pointer + relabel budget over non-isolated vertices in `R`. -/
@[expose] def relabelCurRem (cfg : PruneCfg) (s : PruneState) : ℕ :=
  ∑ u ∈ cfg.X,
    if s.inR u && decide (0 < (cfg.incEdges u).length) then
      (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
      (2 * (cfg.incEdges u).length + 1 - 2 * s.cur u)
    else 0

/-- Remaining sink absorption capacity in `R`. -/
@[expose] def sumAbsRem (cfg : PruneCfg) (s : PruneState) : ℕ :=
  ∑ u ∈ cfg.X, if s.inR u then cfg.degX u - s.abs u else 0

/-- Active-queue height potential for bounding non-saturating pushes. -/
@[expose] def phiActive (s : PruneState) : ℕ :=
  (s.active.map fun u => if s.inR u then s.h u + 2 else 2).sum

/-- Global potential `pot`: decreases strictly on every step of `pruneStep`,
and satisfies `s'.steps + pot cfg s' ≤ s.steps + pot cfg s`. -/
@[expose] def pot (cfg : PruneCfg) (s : PruneState) : ℕ :=
  2 * s.peelQ.length +
  (3 * cfg.H + 8) * volR cfg s +
  (cfg.H + 4) * relabelCurRem cfg s +
  2 * sumAbsRem cfg s +
  2 * phiActive s

/-- Full invariant maintained by push-relabel + low-degree peeling. -/
structure PruningInv (cfg : PruneCfg) (s : PruneState) : Prop where
  inR_sub : ∀ u, s.inR u = true → u ∈ cfg.X
  not_inR_B : ∀ b ∈ cfg.B, s.inR b = false
  h_lt_H : ∀ u, s.inR u = true → s.h u < cfg.H
  cur_le : ∀ u, s.inR u = true → s.cur u ≤ (cfg.incEdges u).length
  abs_le : ∀ u, s.inR u = true → s.abs u ≤ cfg.degX u
  h_pos_abs : ∀ u, s.inR u = true → 0 < s.h u → s.abs u = cfg.degX u
  flow_cap : ∀ idx, idx < cfg.edges.length →
    -(cfg.C_cap : ℤ) ≤ s.flow idx ∧ s.flow idx ≤ (cfg.C_cap : ℤ)
  h_edge : ∀ u, s.inR u = true → ∀ p ∈ cfg.incEdges u, s.inR p.2.2 = true →
    flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ) → s.h u ≤ s.h p.2.2 + 1
  cur_no_adm : ∀ u, s.inR u = true → s.abs u = cfg.degX u →
    ∀ j < s.cur u,
      let p := (cfg.incEdges u).getD j (0, false, 0)
      s.inR p.2.2 = false ∨ flowDir s.flow p.1 p.2.1 = (cfg.C_cap : ℤ) ∨ s.h u ≤ s.h p.2.2
  cur_zero_of_abs_lt : ∀ u, s.inR u = true → s.abs u < cfg.degX u → s.cur u = 0
  flow_balance : ∀ u, s.inR u = true →
    (s.ex u : ℤ) + (s.abs u : ℤ) = ((cfg.incEdges u).map (edgeContrib s.inR s.flow cfg.C_cap)).sum
  degR_eq : ∀ u, s.inR u = true → s.degR u = cfg.G.degIn (s.Rset cfg) u
  degR_peel : ∀ u, s.inR u = true → s.degR u < cfg.θ_out_nat → u ∈ s.peelQ
  active_cov : ∀ u, s.inR u = true → 0 < s.ex u → u ∈ s.active
  active_mem_inActive : ∀ u, s.inActive u = true ↔ u ∈ s.active
  active_nodup : s.active.Nodup
  active_sub : ∀ u ∈ s.active, u ∈ cfg.X
  no_ex_isolated : ∀ u, (cfg.incEdges u).length = 0 →
    s.ex u = 0 ∧ s.h u = 0 ∧ u ∉ s.active ∧ u ∉ s.peelQ

lemma incEdges_mem_sub {cfg : PruneCfg} {u : ℕ} {p : ℕ × Bool × ℕ}
    (hp : p ∈ cfg.incEdges u) : u ∈ cfg.X ∧ p.2.2 ∈ cfg.X :=
  incEdgesAux_mem_endpoints (fun _ he => by
    change _ ∈ cfg.G.inside cfg.X at he
    rw [mem_inside_iff] at he
    exact he.2) hp

lemma incEdges_symm {cfg : PruneCfg} {u : ℕ} {p : ℕ × Bool × ℕ}
    (hp : p ∈ cfg.incEdges u) : (p.1, !p.2.1, u) ∈ cfg.incEdges p.2.2 := by
  unfold PruneCfg.incEdges at hp ⊢
  suffices h : ∀ k (L : List (ℕ × ℕ)),
      p ∈ incEdgesAux u k L → (p.1, !p.2.1, u) ∈ incEdgesAux p.2.2 k L from
    h 0 cfg.edges hp
  intro k L hpL
  induction L generalizing k with
  | nil => simp [incEdgesAux] at hpL
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [incEdgesAux] at hpL ⊢
    split_ifs at hpL with h1 h2 h3
    · have ih' := ih (k + 1) hpL
      split_ifs; simp [ih']
    · rcases List.mem_cons.mp hpL with rfl | hp'
      · subst h2
        simp only [h1, ↓reduceIte, Bool.not_false, List.mem_cons, true_or]
      · have ih' := ih (k + 1) hp'
        split_ifs <;> simp [ih']
    · rcases List.mem_cons.mp hpL with rfl | hp'
      · subst h3
        simp [h1]
      · have ih' := ih (k + 1) hp'
        split_ifs <;> simp [ih']
    · have ih' := ih (k + 1) hpL
      split_ifs <;> simp [ih']

lemma incEdges_unique_idx {cfg : PruneCfg} {u v : ℕ} {p q : ℕ × Bool × ℕ}
    (hp : p ∈ cfg.incEdges u) (hq : q ∈ cfg.incEdges v) (hidx : p.1 = q.1) :
    (u = v ∧ p = q) ∨ (u = q.2.2 ∧ v = p.2.2 ∧ p.2.1 = !q.2.1) := by
  unfold PruneCfg.incEdges at hp hq
  suffices h : ∀ k (L : List (ℕ × ℕ)),
      p ∈ incEdgesAux u k L → q ∈ incEdgesAux v k L → p.1 = q.1 →
      (u = v ∧ p = q) ∨ (u = q.2.2 ∧ v = p.2.2 ∧ p.2.1 = !q.2.1) from
    h 0 cfg.edges hp hq hidx
  intro k L hpL hqL hidx
  induction L generalizing k with
  | nil => simp [incEdgesAux] at hpL
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [incEdgesAux] at hpL hqL
    by_cases hab : a = b
    · simp only [hab, ↓reduceIte] at hpL hqL
      exact ih (k + 1) hpL hqL
    · simp only [hab, ↓reduceIte] at hpL hqL
      by_cases hau : a = u <;> by_cases hbu : b = u
      · exact False.elim (hab (hau.trans hbu.symm))
      · simp only [hau, ↓reduceIte, List.mem_cons] at hpL
        rcases hpL with rfl | hp'
        · by_cases hav : a = v <;> by_cases hbv : b = v
          · exact False.elim (hab (hav.trans hbv.symm))
          · simp only [hav, ↓reduceIte, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · exact Or.inl ⟨hau.symm.trans hav, rfl⟩
            · have := (incEdgesAux_idx_ge hq').1; omega
          · simp only [hav, ↓reduceIte, hbv, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · exact Or.inr ⟨hau.symm, hbv.symm, rfl⟩
            · have := (incEdgesAux_idx_ge hq').1; omega
          · simp only [hav, ↓reduceIte, hbv] at hqL
            have := (incEdgesAux_idx_ge hqL).1; omega
        · have hge := (incEdgesAux_idx_ge hp').1
          by_cases hav : a = v <;> by_cases hbv : b = v
          · exact False.elim (hab (hav.trans hbv.symm))
          · simp only [hav, ↓reduceIte, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · simp at hidx; omega
            · exact ih (k + 1) hp' hq'
          · simp only [hav, ↓reduceIte, hbv, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · simp at hidx; omega
            · exact ih (k + 1) hp' hq'
          · simp only [hav, ↓reduceIte, hbv] at hqL
            exact ih (k + 1) hp' hqL
      · simp only [hau, ↓reduceIte, hbu, List.mem_cons] at hpL
        rcases hpL with rfl | hp'
        · by_cases hav : a = v <;> by_cases hbv : b = v
          · exact False.elim (hab (hav.trans hbv.symm))
          · simp only [hav, ↓reduceIte, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · exact Or.inr ⟨hbu.symm, hav.symm, rfl⟩
            · have := (incEdgesAux_idx_ge hq').1; omega
          · simp only [hav, ↓reduceIte, hbv, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · exact Or.inl ⟨hbu.symm.trans hbv, rfl⟩
            · have := (incEdgesAux_idx_ge hq').1; omega
          · simp only [hav, ↓reduceIte, hbv] at hqL
            have := (incEdgesAux_idx_ge hqL).1; omega
        · have hge := (incEdgesAux_idx_ge hp').1
          by_cases hav : a = v <;> by_cases hbv : b = v
          · exact False.elim (hab (hav.trans hbv.symm))
          · simp only [hav, ↓reduceIte, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · simp at hidx; omega
            · exact ih (k + 1) hp' hq'
          · simp only [hav, ↓reduceIte, hbv, List.mem_cons] at hqL
            rcases hqL with rfl | hq'
            · simp at hidx; omega
            · exact ih (k + 1) hp' hq'
          · simp only [hav, ↓reduceIte, hbv] at hqL
            exact ih (k + 1) hp' hqL
      · simp only [hau, ↓reduceIte, hbu] at hpL
        have hge := (incEdgesAux_idx_ge hpL).1
        by_cases hav : a = v <;> by_cases hbv : b = v
        · exact False.elim (hab (hav.trans hbv.symm))
        · simp only [hav, ↓reduceIte, List.mem_cons] at hqL
          rcases hqL with rfl | hq'
          · simp at hidx; omega
          · exact ih (k + 1) hpL hq'
        · simp only [hav, ↓reduceIte, hbv, List.mem_cons] at hqL
          rcases hqL with rfl | hq'
          · simp at hidx; omega
          · exact ih (k + 1) hpL hq'
        · simp only [hav, ↓reduceIte, hbv] at hqL
          exact ih (k + 1) hpL hqL

/-! ### Initial pruning state -/

/-- Builds initial push-relabel + peeling state for configuration `cfg` starting with `P = B`,
`R = X \ B`. -/
@[expose] noncomputable def initState (cfg : PruneCfg) : PruneState :=
  let inR : ℕ → Bool := fun u => decide (u ∈ cfg.X ∧ u ∉ cfg.B)
  let R₀ := cfg.X.filter fun u => inR u
  let ex : ℕ → ℕ := fun u =>
    if inR u then
      cfg.C_cap * ((cfg.incEdges u).filter fun p => !inR p.2.2).length
    else 0
  let degR : ℕ → ℕ := fun u => if inR u then cfg.G.degIn R₀ u else 0
  let act := cfg.X.toList.filter fun u => inR u && decide (0 < ex u)
  let pQ := cfg.X.toList.filter fun u => inR u && decide (degR u < cfg.θ_out_nat)
  { inR := inR
    h := fun _ => 0
    cur := fun _ => 0
    abs := fun _ => 0
    ex := ex
    degR := degR
    flow := fun _ => 0
    active := act
    inActive := fun u => decide (u ∈ cfg.X) && inR u && decide (0 < ex u)
    peelQ := pQ
    steps := 0 }

lemma initState_inv {cfg : PruneCfg} (hcfg : cfg.Valid) :
    PruningInv cfg (initState cfg) := by
  have hH3 := cfg.valid_three_le_H hcfg
  refine
    { inR_sub := ?_
      not_inR_B := ?_
      h_lt_H := ?_
      cur_le := ?_
      abs_le := ?_
      h_pos_abs := ?_
      flow_cap := ?_
      h_edge := ?_
      cur_no_adm := ?_
      cur_zero_of_abs_lt := ?_
      flow_balance := ?_
      degR_eq := ?_
      degR_peel := ?_
      active_cov := ?_
      active_mem_inActive := ?_
      active_nodup := ?_
      active_sub := ?_
      no_ex_isolated := ?_ }
  · intro u hu; simp [initState] at hu; exact hu.1
  · intro b hb; simp [initState, hb]
  · intro u _; simp [initState]; omega
  · intro u _; simp [initState]
  · intro u _; simp [initState]
  · intro u _ hpos; simp [initState] at hpos
  · intro idx _; simp [initState]
  · intro u _ p _ _ _; simp [initState]
  · intro u _ _ j hj; simp [initState] at hj
  · intro u _ _; simp [initState]
  · intro u hu
    have hu' : u ∈ cfg.X ∧ u ∉ cfg.B := by simpa [initState] using hu
    simp only [initState, hu', Nat.cast_zero, add_zero]
    have hmap : ((cfg.incEdges u).map (edgeContrib (fun u => decide (u ∈ cfg.X ∧ u ∉ cfg.B))
        (fun _ => 0) cfg.C_cap)).sum =
        (cfg.C_cap : ℤ) * (((cfg.incEdges u).filter fun p =>
          !(decide (p.2.2 ∈ cfg.X ∧ p.2.2 ∉ cfg.B))).length : ℤ) := by
      clear hu hu'
      induction (cfg.incEdges u) with
      | nil => simp
      | cons p t ih =>
        rw [List.map_cons, List.sum_cons, List.filter_cons, ih]
        by_cases hp : p.2.2 ∈ cfg.X ∧ p.2.2 ∉ cfg.B
        · have hpt : decide (p.2.2 ∈ cfg.X ∧ p.2.2 ∉ cfg.B) = true := by simp [hp]
          have hec : edgeContrib (fun u => decide (u ∈ cfg.X ∧ u ∉ cfg.B))
              (fun _ => 0) cfg.C_cap p = 0 := by
            simp [edgeContrib, flowDir, hpt]
          rw [hec, hpt]
          simp
        · have hpf : decide (p.2.2 ∈ cfg.X ∧ p.2.2 ∉ cfg.B) = false := by
            exact Bool.eq_false_iff.mpr (by simpa using hp)
          have hec : edgeContrib (fun u => decide (u ∈ cfg.X ∧ u ∉ cfg.B))
              (fun _ => 0) cfg.C_cap p = (cfg.C_cap : ℤ) := by
            simp [edgeContrib, hpf]
          rw [hec, hpf]
          simp only [Bool.not_false, ↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
    push_cast
    exact hmap.symm
  · intro u hu
    have hu' : u ∈ cfg.X ∧ u ∉ cfg.B := by simpa [initState] using hu
    simp [initState, PruneState.Rset, hu']
  · intro u hu hlt
    have hu' : u ∈ cfg.X ∧ u ∉ cfg.B := by simpa [initState] using hu
    have hlt' : (if u ∈ cfg.X ∧ u ∉ cfg.B then cfg.G.degIn ({x ∈ cfg.X | x ∈ cfg.X ∧ x ∉ cfg.B}) u else 0) <
        cfg.θ_out_nat := by
      simpa [initState] using hlt
    simp only [initState, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hu'.1, hu', hlt'⟩
  · intro u hu hpos
    have hu' : u ∈ cfg.X ∧ u ∉ cfg.B := by simpa [initState] using hu
    have hpos' : 0 < (if u ∈ cfg.X ∧ u ∉ cfg.B then
        cfg.C_cap * (List.filter (fun p => !decide (p.2.2 ∈ cfg.X ∧ p.2.2 ∉ cfg.B)) (cfg.incEdges u)).length
        else 0) := by
      simpa [initState] using hpos
    simp only [initState, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hu'.1, hu', hpos'⟩
  · intro u
    simp only [initState, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq,
      Bool.decide_and]
    tauto
  · exact (Finset.nodup_toList cfg.X).filter _
  · intro u hu
    simp only [initState, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq] at hu
    exact hu.1
  · intro u hlen
    have hempty : cfg.incEdges u = [] := List.eq_nil_of_length_eq_zero hlen
    have hex0 : (initState cfg).ex u = 0 := by simp [initState, hempty]
    have hdeg0 : ¬ ((initState cfg).inR u = true ∧ (initState cfg).degR u < cfg.θ_out_nat) := by
      rintro ⟨hu, hlt⟩
      have huXB : u ∈ cfg.X ∧ u ∉ cfg.B := by simpa [initState] using hu
      have hRsub : (initState cfg).Rset cfg ⊆ cfg.X := Finset.filter_subset _ _
      have huR : u ∈ (initState cfg).Rset cfg :=
        (PruneState.mem_Rset cfg (initState cfg) (fun x hx => by simp [initState] at hx; exact hx.1)).mpr hu
      have hdiff := (filter_incEdgesAux_degIn_eq (G := cfg.G) hRsub huR).1
      have hle := (filter_incEdgesAux_degIn_eq (G := cfg.G) hRsub huR).2
      have hdeg_eq : cfg.G.degIn ((initState cfg).Rset cfg) u = cfg.degX u := by
        change cfg.degX u - cfg.G.degIn ((initState cfg).Rset cfg) u =
          ((cfg.incEdges u).filter fun p => decide (p.2.2 ∉ (initState cfg).Rset cfg)).length at hdiff
        change cfg.G.degIn ((initState cfg).Rset cfg) u ≤ cfg.degX u at hle
        rw [hempty] at hdiff
        simp at hdiff
        omega
      have hdegR : (initState cfg).degR u = cfg.degX u := by
        simp only [initState, PruneState.Rset, huXB] at hdeg_eq ⊢
        simpa using hdeg_eq
      have hge := hcfg.2.2.2.2 u huXB.1 huXB.2
      omega
    refine ⟨hex0, rfl, ?_, ?_⟩
    · intro hmem
      simp only [initState, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq] at hmem
      have hpos : 0 < (initState cfg).ex u := by simpa [initState] using hmem.2.2
      omega
    · intro hmem
      simp only [initState, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq] at hmem
      have hin : (initState cfg).inR u = true := by simpa [initState] using hmem.2.1
      have hlt : (initState cfg).degR u < cfg.θ_out_nat := by simpa [initState] using hmem.2.2
      exact hdeg0 ⟨hin, hlt⟩

lemma pot_initState_le {cfg : PruneCfg} (hcfg : cfg.Valid) :
    pot cfg (initState cfg) ≤
      (4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * cfg.edges.length + 1) := by
  have hm : ∑ u ∈ cfg.X, (cfg.incEdges u).length ≤ 2 * cfg.edges.length :=
    sum_incEdgesAux_length_le cfg.X 0 cfg.edges
  have hpeel : (initState cfg).peelQ.length ≤ 2 * cfg.edges.length := by
    have hsub : ∀ u ∈ (initState cfg).peelQ, 1 ≤ (cfg.incEdges u).length := by
      intro u hu
      by_contra h0
      have hlen0 : (cfg.incEdges u).length = 0 := by omega
      exact (initState_inv hcfg).no_ex_isolated u hlen0 |>.2.2.2 hu
    have hnodup : (initState cfg).peelQ.Nodup := (Finset.nodup_toList cfg.X).filter _
    have hmem : ∀ u ∈ (initState cfg).peelQ, u ∈ cfg.X := by
      intro u hu
      simp only [initState, List.mem_filter, Finset.mem_toList] at hu
      exact hu.1
    calc (initState cfg).peelQ.length
        = ∑ _ ∈ (initState cfg).peelQ.toFinset, 1 := by
          rw [← List.toFinset_card_of_nodup hnodup, Finset.card_eq_sum_ones]
      _ ≤ ∑ u ∈ (initState cfg).peelQ.toFinset, (cfg.incEdges u).length :=
          Finset.sum_le_sum fun u hu => hsub u (List.mem_toFinset.mp hu)
      _ ≤ ∑ u ∈ cfg.X, (cfg.incEdges u).length := by
          apply Finset.sum_le_sum_of_subset
          intro u hu
          exact hmem u (List.mem_toFinset.mp hu)
      _ ≤ 2 * cfg.edges.length := hm
  have hvol : volR cfg (initState cfg) ≤ 2 * cfg.edges.length := by
    unfold volR
    calc ∑ u ∈ cfg.X, (if (initState cfg).inR u then (cfg.incEdges u).length else 0)
        ≤ ∑ u ∈ cfg.X, (cfg.incEdges u).length := by
          apply Finset.sum_le_sum; intro u _; split_ifs <;> omega
      _ ≤ 2 * cfg.edges.length := hm
  have hrel : relabelCurRem cfg (initState cfg) ≤ (4 * cfg.H + 3) * (2 * cfg.edges.length) := by
    unfold relabelCurRem
    calc ∑ u ∈ cfg.X,
          (if (initState cfg).inR u && decide (0 < (cfg.incEdges u).length) then
            (cfg.H - (initState cfg).h u) * (2 * (cfg.incEdges u).length + 2) +
            (2 * (cfg.incEdges u).length + 1 - 2 * (initState cfg).cur u)
          else 0)
        ≤ ∑ u ∈ cfg.X, (4 * cfg.H + 3) * (cfg.incEdges u).length := by
          apply Finset.sum_le_sum
          intro u _
          by_cases hgt : 0 < (cfg.incEdges u).length
          · by_cases hin : (initState cfg).inR u = true
            · simp only [hin, hgt, decide_true, Bool.and_self, ↓reduceIte]
              change (cfg.H - 0) * (2 * (cfg.incEdges u).length + 2) +
                (2 * (cfg.incEdges u).length + 1 - 2 * 0) ≤ _
              have hlen1 : 1 ≤ (cfg.incEdges u).length := hgt
              simp only [Nat.sub_zero, Nat.mul_zero]
              have hA : cfg.H * (2 * (cfg.incEdges u).length + 2) ≤
                  4 * cfg.H * (cfg.incEdges u).length := by nlinarith
              have hB : 2 * (cfg.incEdges u).length + 1 ≤
                  3 * (cfg.incEdges u).length := by omega
              linarith [show (4 * cfg.H + 3) * (cfg.incEdges u).length =
                4 * cfg.H * (cfg.incEdges u).length + 3 * (cfg.incEdges u).length by ring]
            · simp [hin]
          · simp [hgt]
      _ = (4 * cfg.H + 3) * ∑ u ∈ cfg.X, (cfg.incEdges u).length := by rw [← Finset.mul_sum]
      _ ≤ (4 * cfg.H + 3) * (2 * cfg.edges.length) := Nat.mul_le_mul_left _ hm
  have habs : sumAbsRem cfg (initState cfg) ≤ 2 * cfg.edges.length := by
    unfold sumAbsRem PruneCfg.degX
    calc ∑ u ∈ cfg.X, (if (initState cfg).inR u then cfg.G.degIn cfg.X u - (initState cfg).abs u else 0)
        ≤ ∑ u ∈ cfg.X, cfg.G.degIn cfg.X u := by
          apply Finset.sum_le_sum; intro u _; split_ifs <;> omega
      _ = cfg.G.volIn cfg.X cfg.X := rfl
      _ = 2 * cfg.edges.length := volIn_self cfg.G cfg.X
  have hact : phiActive (initState cfg) ≤ 4 * cfg.edges.length := by
    unfold phiActive
    have hsub : ∀ u ∈ (initState cfg).active, 1 ≤ (cfg.incEdges u).length := by
      intro u hu
      by_contra h0
      exact (initState_inv hcfg).no_ex_isolated u (by omega) |>.2.2.1 hu
    have hnodup := (initState_inv hcfg).active_nodup
    have hsubX := (initState_inv hcfg).active_sub
    have hmap : ((initState cfg).active.map fun u =>
        if (initState cfg).inR u then (initState cfg).h u + 2 else 2).sum =
        2 * (initState cfg).active.length := by
      have heq : (initState cfg).active.map (fun u =>
          if (initState cfg).inR u then (initState cfg).h u + 2 else 2) =
          (initState cfg).active.map (fun _ => 2) := by
        apply List.map_congr_left
        intro u _
        change (if (initState cfg).inR u then 0 + 2 else 2) = 2
        split_ifs <;> rfl
      rw [heq, sum_map_const]
      ring
    rw [hmap]
    have hcard : (initState cfg).active.length ≤ 2 * cfg.edges.length := by
      calc (initState cfg).active.length
          = ∑ _ ∈ (initState cfg).active.toFinset, 1 := by
            rw [← List.toFinset_card_of_nodup hnodup, Finset.card_eq_sum_ones]
        _ ≤ ∑ u ∈ (initState cfg).active.toFinset, (cfg.incEdges u).length :=
            Finset.sum_le_sum fun u hu => hsub u (List.mem_toFinset.mp hu)
        _ ≤ ∑ u ∈ cfg.X, (cfg.incEdges u).length := by
            apply Finset.sum_le_sum_of_subset
            intro u hu
            exact hsubX u (List.mem_toFinset.mp hu)
        _ ≤ 2 * cfg.edges.length := hm
    omega
  unfold pot
  set E := cfg.edges.length
  nlinarith

/-! ### Level-sweep selection -/

/-- Total `degX`-volume of active vertices in `R` at height `lvl`. -/
@[expose] def volAtLevel (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) (lvl : ℕ) : ℕ :=
  ∑ u ∈ cfg.X, if inR u && decide (h u = lvl) then cfg.degX u else 0

/-- Total `degX`-volume of active vertices in `R` at height at least `lvl`. -/
@[expose] def volGeLevel (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) (lvl : ℕ) : ℕ :=
  ∑ u ∈ cfg.X, if inR u && decide (lvl ≤ h u) then cfg.degX u else 0

lemma volGeLevel_succ_add (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) (lvl : ℕ) :
    volGeLevel cfg inR h lvl =
      volAtLevel cfg inR h lvl + volGeLevel cfg inR h (lvl + 1) := by
  unfold volGeLevel volAtLevel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hr : inR u = true
  · by_cases hlt : lvl ≤ h u
    · rcases eq_or_lt_of_le hlt with hEq | hgt
      · simp [hr, hEq]
      · have hne : h u ≠ lvl := by omega
        have hle1 : lvl + 1 ≤ h u := by omega
        simp [hr, hlt, hne, hle1]
    · have hne : h u ≠ lvl := by omega
      have hnle1 : ¬ (lvl + 1 ≤ h u) := by omega
      simp [hr, hlt, hne, hnle1]
  · simp [hr]

lemma volGeLevel_one_le (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) :
    volGeLevel cfg inR h 1 ≤ 2 * cfg.edges.length := by
  unfold volGeLevel PruneCfg.degX
  calc ∑ u ∈ cfg.X, (if inR u && decide (1 ≤ h u) then cfg.G.degIn cfg.X u else 0)
      ≤ ∑ u ∈ cfg.X, cfg.G.degIn cfg.X u := by
        apply Finset.sum_le_sum; intro u _; split_ifs <;> omega
    _ = cfg.G.volIn cfg.X cfg.X := rfl
    _ = 2 * cfg.edges.length := volIn_self cfg.G cfg.X

/-- Computes the first level `lvl ∈ {1, ..., H - 1}` where `4 * C_cap * volAtLevel lvl ≤ volGeLevel (lvl + 1)`. -/
@[expose] def pickLevelAux (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
      let lvl := cfg.H - 1 - k
      if 4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1) then lvl
      else pickLevelAux cfg inR h k

/-- Good sweep level in `1 .. H - 1`. -/
@[expose] def pickLevel (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) : ℕ :=
  pickLevelAux cfg inR h (cfg.H - 1)

lemma pickLevel_spec {cfg : PruneCfg} (hcfg : cfg.Valid) (inR : ℕ → Bool) (h : ℕ → ℕ)
    (huX : ∃ u ∈ cfg.X, inR u = true ∧ h u = cfg.H ∧ 1 ≤ cfg.degX u) :
    let lvl := pickLevel cfg inR h
    1 ≤ lvl ∧ lvl < cfg.H ∧
      4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1) := by
  have hH3 := cfg.valid_three_le_H hcfg
  have hC4 := hcfg.2.2.1
  have hHbound := hcfg.2.2.2.1
  have hvolH : 1 ≤ volGeLevel cfg inR h cfg.H := by
    rcases huX with ⟨u, huX, hin, hh, hdeg⟩
    unfold volGeLevel
    calc 1 ≤ cfg.degX u := hdeg
      _ = (if inR u && decide (cfg.H ≤ h u) then cfg.degX u else 0) := by
          simp [hin, hh]
      _ ≤ ∑ x ∈ cfg.X, if inR x && decide (cfg.H ≤ h x) then cfg.degX x else 0 :=
          Finset.single_le_sum (f := fun x => if inR x && decide (cfg.H ≤ h x) then cfg.degX x else 0)
            (fun x _ => Nat.zero_le _) huX
  have hexists : ∃ lvl, 1 ≤ lvl ∧ lvl ≤ cfg.H - 1 ∧
      4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1) := by
    by_contra hnone
    push Not at hnone
    have hstep : ∀ lvl, 1 ≤ lvl → lvl ≤ cfg.H - 1 →
        (1 + 1 / (4 * (cfg.C_cap : ℝ))) * (volGeLevel cfg inR h (lvl + 1) : ℝ) ≤
          (volGeLevel cfg inR h lvl : ℝ) := by
      intro lvl h1 h2
      have hgt : volGeLevel cfg inR h (lvl + 1) + 1 ≤ 4 * cfg.C_cap * volAtLevel cfg inR h lvl :=
        hnone lvl h1 h2
      have hreal : (volGeLevel cfg inR h (lvl + 1) : ℝ) ≤
          4 * (cfg.C_cap : ℝ) * (volAtLevel cfg inR h lvl : ℝ) := by
        exact_mod_cast (by omega : volGeLevel cfg inR h (lvl + 1) ≤ 4 * cfg.C_cap * volAtLevel cfg inR h lvl)
      rw [volGeLevel_succ_add (lvl := lvl)]
      push_cast
      have hCpos : (0 : ℝ) < 4 * (cfg.C_cap : ℝ) := by positivity
      have hdiv : (volGeLevel cfg inR h (lvl + 1) : ℝ) / (4 * (cfg.C_cap : ℝ)) ≤
          (volAtLevel cfg inR h lvl : ℝ) := (div_le_iff₀ hCpos).mpr (by linarith)
      linarith [show (1 + 1 / (4 * (cfg.C_cap : ℝ))) * (volGeLevel cfg inR h (lvl + 1) : ℝ) =
        (volGeLevel cfg inR h (lvl + 1) : ℝ) / (4 * (cfg.C_cap : ℝ)) +
        (volGeLevel cfg inR h (lvl + 1) : ℝ) by ring]
    have hpow : ∀ t, t ≤ cfg.H - 1 →
        (1 + 1 / (4 * (cfg.C_cap : ℝ))) ^ t * (volGeLevel cfg inR h cfg.H : ℝ) ≤
          (volGeLevel cfg inR h (cfg.H - t) : ℝ) := by
      intro t ht
      induction t with
      | zero => simp
      | succ t ih =>
        have ih' := ih (by omega)
        have hst := hstep (cfg.H - (t + 1)) (by omega) (by omega)
        have heq1 : cfg.H - (t + 1) + 1 = cfg.H - t := by omega
        rw [heq1] at hst
        have hpos : (0 : ℝ) ≤ 1 + 1 / (4 * (cfg.C_cap : ℝ)) := by positivity
        calc (1 + 1 / (4 * (cfg.C_cap : ℝ))) ^ (t + 1) * (volGeLevel cfg inR h cfg.H : ℝ)
            = (1 + 1 / (4 * (cfg.C_cap : ℝ))) *
                ((1 + 1 / (4 * (cfg.C_cap : ℝ))) ^ t * (volGeLevel cfg inR h cfg.H : ℝ)) := by ring
          _ ≤ (1 + 1 / (4 * (cfg.C_cap : ℝ))) * (volGeLevel cfg inR h (cfg.H - t) : ℝ) :=
              mul_le_mul_of_nonneg_left ih' hpos
          _ ≤ (volGeLevel cfg inR h (cfg.H - (t + 1)) : ℝ) := hst
    have hH1 := hpow (cfg.H - 1) (le_refl _)
    have heqH1 : cfg.H - (cfg.H - 1) = 1 := by omega
    rw [heqH1] at hH1
    set K := 4 * cfg.C_cap
    set L := Nat.log 2 (2 * cfg.edges.length + 1) + 1
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hbern : (2 : ℝ) ≤ (1 + 1 / (K : ℝ)) ^ K := by
      have hb := one_add_mul_le_pow (a := 1 / (K : ℝ))
        (by linarith [show (0 : ℝ) ≤ 1 / (K : ℝ) by positivity]) K
      have hmul : (K : ℝ) * (1 / (K : ℝ)) = 1 := by field_simp
      linarith
    have hKL_le : K * L ≤ cfg.H - 1 := by omega
    have hpow_le : (2 : ℝ) ^ L ≤ (1 + 1 / (K : ℝ)) ^ (cfg.H - 1) := by
      have h1 : (2 : ℝ) ^ L ≤ ((1 + 1 / (K : ℝ)) ^ K) ^ L :=
        pow_le_pow_left₀ (by norm_num) hbern L
      have h2 : ((1 + 1 / (K : ℝ)) ^ K) ^ L = (1 + 1 / (K : ℝ)) ^ (K * L) := by
        rw [← pow_mul]
      have h3 : (1 + 1 / (K : ℝ)) ^ (K * L) ≤ (1 + 1 / (K : ℝ)) ^ (cfg.H - 1) :=
        pow_le_pow_right₀ (by linarith [show (0 : ℝ) ≤ 1 / (K : ℝ) by positivity]) hKL_le
      exact le_trans h1 (h2 ▸ h3)
    have hlt_pow : (2 * (cfg.edges.length : ℝ) + 1) < (2 : ℝ) ^ L := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) (2 * cfg.edges.length + 1)
    have hvol1_le : (volGeLevel cfg inR h 1 : ℝ) ≤ 2 * (cfg.edges.length : ℝ) := by
      exact_mod_cast volGeLevel_one_le cfg inR h
    have hvolH_ge : (1 : ℝ) ≤ (volGeLevel cfg inR h cfg.H : ℝ) := by
      exact_mod_cast hvolH
    have h1lt : (2 * (cfg.edges.length : ℝ) + 1) < (1 + 1 / (K : ℝ)) ^ (cfg.H - 1) *
        (volGeLevel cfg inR h cfg.H : ℝ) := by
      nlinarith
    push_cast [K] at hH1 h1lt
    linarith
  have haux : ∀ k, k ≤ cfg.H - 1 →
      (∃ lvl, cfg.H - k ≤ lvl ∧ lvl ≤ cfg.H - 1 ∧
        4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1)) →
      let lvl := pickLevelAux cfg inR h k
      cfg.H - k ≤ lvl ∧ lvl ≤ cfg.H - 1 ∧
        4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1) := by
    intro k hk hex
    induction k with
    | zero =>
      rcases hex with ⟨lvl, h1, h2, _⟩
      omega
    | succ k ih =>
      simp only [pickLevelAux]
      split_ifs with hgood
      · exact ⟨by omega, by omega, hgood⟩
      · have hexk : ∃ lvl, cfg.H - k ≤ lvl ∧ lvl ≤ cfg.H - 1 ∧
            4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1) := by
          rcases hex with ⟨lvl, h1, h2, h3⟩
          refine ⟨lvl, ?_, h2, h3⟩
          have hne : lvl ≠ cfg.H - 1 - k := fun heq => hgood (heq ▸ h3)
          omega
        rcases ih (by omega) hexk with ⟨a, b, c⟩
        exact ⟨by omega, b, c⟩
  have hex' : ∃ lvl, cfg.H - (cfg.H - 1) ≤ lvl ∧ lvl ≤ cfg.H - 1 ∧
      4 * cfg.C_cap * volAtLevel cfg inR h lvl ≤ volGeLevel cfg inR h (lvl + 1) := by
    rcases hexists with ⟨lvl, h1, h2, h3⟩
    exact ⟨lvl, by omega, h2, h3⟩
  rcases haux (cfg.H - 1) (le_refl _) hex' with ⟨h1, h2, h3⟩
  dsimp only [pickLevel]
  exact ⟨by omega, by omega, h3⟩

/-- Computable initial state scanning a given explicit vertex list `XList` in order.
Used by WordRAM simulation when `XList` enumerates `cfg.X` (`List.range G.n` or reverse). -/
@[expose] def initStateList (cfg : PruneCfg) (XList : List ℕ) : PruneState :=
  let inR : ℕ → Bool := fun u => decide (u ∈ cfg.X ∧ u ∉ cfg.B)
  let R₀ : Finset ℕ := cfg.X.filter fun u => inR u
  let ex : ℕ → ℕ := fun u =>
    if inR u then cfg.C_cap * ((cfg.incEdges u).filter fun p => !inR p.2.2).length else 0
  let degR : ℕ → ℕ := fun u => if inR u then cfg.G.degIn R₀ u else 0
  let act : List ℕ := XList.filter fun u => inR u && decide (0 < ex u)
  let pQ : List ℕ := XList.filter fun u => inR u && decide (degR u < cfg.θ_out_nat)
  { inR := inR
    h := fun _ => 0
    cur := fun _ => 0
    abs := fun _ => 0
    ex := ex
    degR := degR
    flow := fun _ => 0
    active := act
    inActive := fun u => decide (u ∈ cfg.X) && inR u && decide (0 < ex u)
    peelQ := pQ
    steps := 0 }

lemma initStateList_perm_XList {cfg : PruneCfg} {XList : List ℕ}
    (hX : XList.Nodup ∧ ∀ x, x ∈ XList ↔ x ∈ cfg.X) :
    XList.Perm cfg.X.toList :=
  (List.perm_ext_iff_of_nodup hX.1 (Finset.nodup_toList cfg.X)).mpr fun x => by
    rw [hX.2, Finset.mem_toList]

lemma initStateList_inv {cfg : PruneCfg} (hcfg : cfg.Valid) {XList : List ℕ}
    (hX : XList.Nodup ∧ ∀ x, x ∈ XList ↔ x ∈ cfg.X) :
    PruningInv cfg (initStateList cfg XList) := by
  have hinv := initState_inv hcfg
  have hpermX := initStateList_perm_XList hX
  have hactPerm : (initStateList cfg XList).active.Perm (initState cfg).active :=
    hpermX.filter _
  have hpQPerm : (initStateList cfg XList).peelQ.Perm (initState cfg).peelQ :=
    hpermX.filter _
  refine
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_lt_H := hinv.h_lt_H
      cur_le := hinv.cur_le
      abs_le := hinv.abs_le
      h_pos_abs := hinv.h_pos_abs
      flow_cap := hinv.flow_cap
      h_edge := hinv.h_edge
      cur_no_adm := hinv.cur_no_adm
      cur_zero_of_abs_lt := hinv.cur_zero_of_abs_lt
      flow_balance := hinv.flow_balance
      degR_eq := hinv.degR_eq
      degR_peel := fun u hu hlt => hpQPerm.symm.mem_iff.mp (hinv.degR_peel u hu hlt)
      active_cov := fun u hu hex => hactPerm.symm.mem_iff.mp (hinv.active_cov u hu hex)
      active_mem_inActive := fun u => by
        change (initState cfg).inActive u = true ↔ u ∈ (initStateList cfg XList).active
        rw [hinv.active_mem_inActive, hactPerm.mem_iff]
      active_nodup := hactPerm.nodup_iff.mpr hinv.active_nodup
      active_sub := fun u hu => hinv.active_sub u (hactPerm.mem_iff.mp hu)
      no_ex_isolated := fun u hlen => by
        have h0 := hinv.no_ex_isolated u hlen
        refine ⟨h0.1, h0.2.1, ?_, ?_⟩
        · simpa only [hactPerm.mem_iff] using h0.2.2.1
        · simpa only [hpQPerm.mem_iff] using h0.2.2.2 }

lemma pot_initStateList_eq {cfg : PruneCfg} {XList : List ℕ}
    (hX : XList.Nodup ∧ ∀ x, x ∈ XList ↔ x ∈ cfg.X) :
    pot cfg (initStateList cfg XList) = pot cfg (initState cfg) := by
  have hpermX := initStateList_perm_XList hX
  have hactPerm : (initStateList cfg XList).active.Perm (initState cfg).active :=
    hpermX.filter _
  have hpQPerm : (initStateList cfg XList).peelQ.Perm (initState cfg).peelQ :=
    hpermX.filter _
  unfold pot
  have hlen : (initStateList cfg XList).peelQ.length = (initState cfg).peelQ.length :=
    hpQPerm.length_eq
  have hphi : phiActive (initStateList cfg XList) = phiActive (initState cfg) := by
    unfold phiActive
    exact (hactPerm.map _).sum_eq
  rw [hlen, hphi]
  rfl

lemma pot_initStateList_le {cfg : PruneCfg} (hcfg : cfg.Valid) {XList : List ℕ}
    (hX : XList.Nodup ∧ ∀ x, x ∈ XList ↔ x ∈ cfg.X) :
    pot cfg (initStateList cfg XList) ≤
      (4 * cfg.H + 14) * (4 * cfg.H + 4) * (2 * cfg.edges.length + 1) := by
  rw [pot_initStateList_eq hX]
  exact pot_initState_le hcfg

lemma initStateList_peelQ_spec {cfg : PruneCfg} {XList : List ℕ}
    (hX : XList.Nodup ∧ ∀ x, x ∈ XList ↔ x ∈ cfg.X) :
    (initStateList cfg XList).peelQ.Nodup ∧
      (∀ x ∈ (initStateList cfg XList).peelQ, x ∈ cfg.X) ∧
      (∀ x ∈ (initStateList cfg XList).peelQ, (initStateList cfg XList).degR x < cfg.θ_out_nat) := by
  dsimp only [initStateList]
  refine ⟨hX.1.filter _, ?_, ?_⟩
  · intro x hx
    exact (hX.2 x).mp (List.mem_filter.mp hx).1
  · intro x hx
    have hp := (List.mem_filter.mp hx).2
    have hp' := Bool.and_eq_true _ _ |>.mp hp
    exact of_decide_eq_true hp'.2

end MinCostFlow.Expander
