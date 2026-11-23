module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Expander.ExpanderPruning
public import MinCostFlow.Expander.Components

import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.Expander.PruningState
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Twin-Graph Loopless Reduction and Single Level of Algorithm 5

Implements one level of Algorithm 5 (`Decompose`, Appendix B, p. 49) faithfully over loopless
multigraphs using twin-vertex duplication:
- `twinGraph D G`: doubles vertices `0 .. G.n - 1` into `(2u, 2u + 1)`, maps each edge `(a, b)` of `G`
  to `(2a, 2b)`, and adds `D` parallel edges `(2u, 2u + 1)` per vertex `u < G.n` (making the graph
  loopless so `Cited.ExpanderDecomposition` applies).
- `decomposePartFull`: projects each expander part `Y` of `twinGraph` back to `X = {v < G.n | 2v ∈ Y}`.
  If a low-degree vertex `v ∈ X` keeps its twin `2v + 1 ∈ Y`, conductance forces all other twins out
  of `Y` and `≤ G_twin.cut Y` edges inside `X`, so `X` is dropped. Otherwise every low-degree vertex
  `b ∈ B` has `2b + 1 ∉ Y`, giving `volIn X B ≤ φ_B1 * G_twin.cut Y`, and `pruneExpander` extracts
  a `(φ_B1 / 3)`-expander `R` with minimum internal degree `≥ (φ_B1 / 3) * D`.
- `decomposeLevel`: partitions `curG` into `G_i` (disjoint union of kept pruned expanders `R`) and
  `remG` (dropped/inter-part edges), proving Claim B.2 (`remG.m ≤ 2^{i-1} * curG.n` when
  `curG.m ≤ 2^i * curG.n`) and that every nontrivial connected component of `G_i` is one of the `R`.
-/

namespace MinCostFlow.Expander

open Classical

public section

/-- Twin-vertex loopless duplication of `G` with `D` parallel twin edges `(2u, 2u + 1)` per vertex
`u < G.n` replacing self-loops in Algorithm 5 (`G_i^↻`, p. 49). -/
@[expose] def twinGraph (D : ℕ) (G : Cited.Graph) : Cited.Graph :=
  { n := 2 * G.n
    edges :=
      G.edges.map (fun e => (2 * e.1, 2 * e.2)) ++
      (List.range G.n).flatMap (fun u => List.replicate D (2 * u, 2 * u + 1)) }

/-- Projects a vertex set `Y` of `twinGraph D G` to `{v < G.n | 2 * v ∈ Y}`. -/
@[expose] def partX (n : ℕ) (Y : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter fun v => 2 * v ∈ Y

/-- Processes one part `Y` of `twinGraph D curG` at degree scale `D` and conductance `φ_B1`,
returning `(R_Y, pruningSteps_Y)` where either `R_Y = ∅` or `2 ≤ R_Y.card`. -/
@[expose] noncomputable def decomposePartFull (curG : Cited.Graph) (D : ℕ) (φ_B1 : ℝ)
    (Y : Finset ℕ) : Finset ℕ × ℕ :=
  let X := partX curG.n Y
  if X.card ≤ 1 then (∅, 0)
  else
    let B := X.filter fun v => decide ((curG.degIn X v : ℝ) < φ_B1 * (D : ℝ))
    if ∃ v ∈ B, 2 * v + 1 ∈ Y then (∅, 0)
    else
      let cfg := pruneCfgOf curG X B φ_B1 (φ_B1 * (D : ℝ))
      let R := pruneExpander curG X B φ_B1 (φ_B1 * (D : ℝ))
      let st := (pruneFinalState cfg).steps
      if R.card ≤ 1 then (∅, st) else (R, st)

/-- Valid pruned expander components `R` (`|R| ≥ 2`) produced at level `i` of Algorithm 5. -/
@[expose] noncomputable def decomposeLevelComps (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (φ_B1 : ℝ) (curG : Cited.Graph) (i : ℕ) : List (Finset ℕ) :=
  let D := 2 ^ i
  let G_twin := twinGraph D curG
  let label := decomp 1 200 G_twin
  let parts := (Cited.partsOf G_twin label).toList
  let resParts := parts.map fun Y => decomposePartFull curG D φ_B1 Y
  (resParts.map Prod.fst).filter fun R => decide (2 ≤ R.card)

/-- Edge membership predicate for level `i` of Algorithm 5. -/
@[expose] noncomputable def decomposeLevelPred (decomp : ℕ → ℕ → Cited.Graph → List ℕ)
    (φ_B1 : ℝ) (curG : Cited.Graph) (i : ℕ) : ℕ × ℕ → Bool :=
  let validRs := decomposeLevelComps decomp φ_B1 curG i
  fun e => validRs.any fun R => decide (e.1 ∈ R ∧ e.2 ∈ R)

/-- Single level `i` of Algorithm 5: decomposes `twinGraph (2^i) curG`, prunes each part, and splits
`curG` into `(G_i, remG)` with total pruning step cost `levelSteps`. -/
@[expose] noncomputable def decomposeLevel (decomp : ℕ → ℕ → Cited.Graph → List ℕ) (φ_B1 : ℝ)
    (curG : Cited.Graph) (i : ℕ) : Cited.Graph × Cited.Graph × ℕ :=
  let D := 2 ^ i
  let G_twin := twinGraph D curG
  let label := decomp 1 200 G_twin
  let parts := (Cited.partsOf G_twin label).toList
  let resParts := parts.map fun Y => decomposePartFull curG D φ_B1 Y
  let validRs := (resParts.map Prod.fst).filter fun R => decide (2 ≤ R.card)
  let pred : ℕ × ℕ → Bool := fun e => validRs.any fun R => decide (e.1 ∈ R ∧ e.2 ∈ R)
  let Gi : Cited.Graph := { n := curG.n, edges := curG.edges.filter pred }
  let remG : Cited.Graph := { n := curG.n, edges := curG.edges.filter fun e => !pred e }
  (Gi, remG, (resParts.map Prod.snd).sum)

lemma filter_comp_perm {α : Type*} (p : α → Bool) :
    ∀ L : List α, (L.filter p ++ L.filter fun x => !p x).Perm L
  | [] => by simp
  | x :: xs => by
    have ih := filter_comp_perm p xs
    rw [List.filter_cons, List.filter_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact List.Perm.trans List.perm_middle (List.Perm.cons x ih)
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, List.cons_append]
      exact List.Perm.cons x ih

lemma twinGraph_isValid {D : ℕ} {G : Cited.Graph} (hV : G.IsValid) :
    (twinGraph D G).IsValid := by
  intro e he
  simp only [twinGraph, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_replicate] at he
  dsimp only [twinGraph]
  rcases he with ⟨e', he', rfl⟩ | ⟨u, hu, _, rfl⟩
  · rcases hV e' he' with ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩

lemma twinGraph_isLoopless {D : ℕ} {G : Cited.Graph} (hL : G.IsLoopless) :
    (twinGraph D G).IsLoopless := by
  intro e he
  simp only [twinGraph, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_replicate] at he
  rcases he with ⟨e', he', rfl⟩ | ⟨u, _, _, rfl⟩
  · have hne := hL e' he'
    omega
  · omega

private lemma length_flatMap_replicate {α β : Type*} (L : List α) (D : ℕ) (f : α → β) :
    (L.flatMap fun u => List.replicate D (f u)).length = L.length * D := by
  induction L with
  | nil => simp
  | cons u us ih => simp [List.flatMap_cons, List.length_replicate, ih, Nat.succ_mul, Nat.add_comm]

lemma twinGraph_m (D : ℕ) (G : Cited.Graph) :
    (twinGraph D G).m = G.m + D * G.n := by
  unfold Cited.Graph.m twinGraph
  simp only [List.length_append, List.length_map]
  rw [length_flatMap_replicate, List.length_range, Nat.mul_comm]

private lemma inside_verts_eq {G : Cited.Graph} (hV : G.IsValid) :
    G.inside G.verts = G.edges := by
  unfold Cited.Graph.inside Cited.Graph.verts
  rw [List.filter_eq_self]
  intro e he
  rcases hV e he with ⟨h1, h2⟩
  simp [Finset.mem_range, h1, h2]

private lemma inside_twinGraph_eq {D : ℕ} {G : Cited.Graph} (hV : G.IsValid) (Y : Finset ℕ) :
    (twinGraph D G).inside Y =
      (G.inside (partX G.n Y)).map (fun e => (2 * e.1, 2 * e.2)) ++
      ((List.range G.n).flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
        (fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)) := by
  unfold Cited.Graph.inside twinGraph
  rw [List.filter_append]
  congr 1
  dsimp only [partX]
  have h1 : ∀ (L : List (ℕ × ℕ)), (∀ e ∈ L, e.1 < G.n ∧ e.2 < G.n) →
      (L.map fun e => (2 * e.1, 2 * e.2)).filter (fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)) =
      (L.filter fun e => decide (e.1 ∈ (Finset.range G.n).filter fun v => 2 * v ∈ Y) &&
        decide (e.2 ∈ (Finset.range G.n).filter fun v => 2 * v ∈ Y)).map
        (fun e => (2 * e.1, 2 * e.2)) := by
    intro L hL
    induction L with
    | nil => simp
    | cons e rest ih =>
      rcases hL e List.mem_cons_self with ⟨he1, he2⟩
      have ih' := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
      by_cases h2e1 : 2 * e.1 ∈ Y <;> by_cases h2e2 : 2 * e.2 ∈ Y <;>
        simp [Finset.mem_filter, Finset.mem_range, he1, he2, h2e1, h2e2, ih']
  exact h1 G.edges hV

private lemma twin_half_cut_zero (S : Finset ℕ) (Q : Finset ℕ) :
    ∀ (L : List ℕ) (D : ℕ),
      (((L.flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
        fun e => decide (e.1 ∈ Q) && decide (e.2 ∈ Q)).filter
        fun e => decide ((e.1 / 2 ∈ S)) != decide ((e.2 / 2 ∈ S))).length = 0 := by
  intro L D
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.mem_flatMap,
    List.mem_replicate] at he
  rcases he with ⟨⟨u, _, _, rfl⟩, _, _⟩
  have h1 : (2 * u) / 2 = u := by omega
  have h2 : (2 * u + 1) / 2 = u := by omega
  simp [h1, h2]

private lemma twin_half_deg_even (u : ℕ) (Q : Finset ℕ) :
    ∀ (L : List ℕ) (D : ℕ),
      ((((L.flatMap (fun v => List.replicate D (2 * v, 2 * v + 1))).filter
        fun e => decide (e.1 ∈ Q) && decide (e.2 ∈ Q)).filter
        fun e => decide (e.1 = 2 * u)).length +
      (((L.flatMap (fun v => List.replicate D (2 * v, 2 * v + 1))).filter
        fun e => decide (e.1 ∈ Q) && decide (e.2 ∈ Q)).filter
        fun e => decide (e.2 = 2 * u)).length) ≥ 0 := fun _ _ => Nat.zero_le _

private lemma flatMap_replicate_cut_ge (D : ℕ) (Y : Finset ℕ) (B : Finset ℕ) :
    ∀ (L : List ℕ), L.Nodup → (∀ b ∈ B, b ∈ L) →
      (∀ b ∈ B, 2 * b ∈ Y ∧ 2 * b + 1 ∉ Y) →
      D * B.card ≤
        ((L.flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
          fun e => decide (e.1 ∈ Y) != decide (e.2 ∈ Y)).length
  | [], _, hBL, _ => by
    have hB : B = ∅ := Finset.eq_empty_of_forall_notMem fun b hb => by simpa using hBL b hb
    simp [hB]
  | u :: us, hnd, hBL, hYO => by
    simp only [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, List.filter_append, List.length_append]
    have hus : ∀ b ∈ B.erase u, b ∈ us := fun b hb => by
      rcases Finset.mem_erase.mp hb with ⟨hne, hbB⟩
      exact (List.mem_cons.mp (hBL b hbB)).resolve_left hne
    have ih := flatMap_replicate_cut_ge D Y (B.erase u) us hnd.2 hus
      (fun b hb => hYO b (Finset.erase_subset _ _ hb))
    by_cases hu : u ∈ B
    · have ⟨h2u, h2u1⟩ := hYO u hu
      have hcond : (decide ((2 * u, 2 * u + 1).1 ∈ Y) != decide ((2 * u, 2 * u + 1).2 ∈ Y)) =
          true := by simp [h2u, h2u1]
      have hfilt : (List.filter (fun e => decide (e.1 ∈ Y) != decide (e.2 ∈ Y))
          (List.replicate D (2 * u, 2 * u + 1))).length = D := by
        rw [List.filter_replicate, ite_eq_left_iff.mpr fun hn => False.elim (hn hcond),
          List.length_replicate]
      have hcard : B.card = (B.erase u).card + 1 := (Finset.card_erase_add_one hu).symm
      rw [hfilt, hcard, Nat.mul_add, Nat.mul_one]
      omega
    · have heq : B.erase u = B := Finset.erase_eq_of_notMem hu
      rw [heq] at ih
      omega

lemma twin_cut_ge_of_mem_not_twin {D : ℕ} {G : Cited.Graph} (hV : G.IsValid)
    {Y B : Finset ℕ} (hBn : ∀ b ∈ B, b < G.n) (hIn : ∀ b ∈ B, 2 * b ∈ Y)
    (hOut : ∀ b ∈ B, 2 * b + 1 ∉ Y) :
    D * B.card ≤ (twinGraph D G).cut Y := by
  have hTV := twinGraph_isValid (D := D) hV
  unfold Cited.Graph.cut Cited.Graph.cutIn
  rw [inside_verts_eq hTV]
  simp only [twinGraph, List.filter_append, List.length_append]
  have hrep := flatMap_replicate_cut_ge D Y B (List.range G.n) List.nodup_range
    (fun b hb => List.mem_range.mpr (hBn b hb)) (fun b hb => ⟨hIn b hb, hOut b hb⟩)
  omega

private lemma twin_pair_inside_vol {D : ℕ} {G : Cited.Graph} (hV : G.IsValid)
    {Y : Finset ℕ} {v : ℕ} (hv : v < G.n) (h2v : 2 * v ∈ Y) (h2v1 : 2 * v + 1 ∈ Y)
    {S : Finset ℕ} (hS1 : 2 * v ∈ S) (hS2 : 2 * v + 1 ∈ S) :
    2 * D ≤ (twinGraph D G).volIn Y S := by
  have hne : 2 * v ≠ 2 * v + 1 := by omega
  have hsub : {2 * v, 2 * v + 1} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle : (twinGraph D G).volIn Y {2 * v, 2 * v + 1} ≤ (twinGraph D G).volIn Y S :=
    volIn_mono_right (twinGraph D G) Y hsub
  have hvol_pair : (twinGraph D G).volIn Y {2 * v, 2 * v + 1} =
      (twinGraph D G).degIn Y (2 * v) + (twinGraph D G).degIn Y (2 * v + 1) := by
    unfold Cited.Graph.volIn
    rw [Finset.sum_pair hne]
  suffices hd : D ≤ (twinGraph D G).degIn Y (2 * v) ∧ D ≤ (twinGraph D G).degIn Y (2 * v + 1) by
    omega
  unfold Cited.Graph.degIn
  rw [inside_twinGraph_eq hV Y]
  simp only [List.filter_append, List.length_append]
  suffices hrep :
      ∀ (L : List ℕ), v ∈ L →
        D ≤ (((L.flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
          fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)).filter
          fun e => decide (e.1 = 2 * v)).length ∧
        D ≤ (((L.flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
          fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)).filter
          fun e => decide (e.2 = 2 * v + 1)).length by
    have hr := hrep (List.range G.n) (List.mem_range.mpr hv)
    omega
  intro L hvL
  induction L with
  | nil => simp at hvL
  | cons u us ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append]
    rcases List.mem_cons.mp hvL with rfl | hmem
    · have hc1 : (decide ((2 * v, 2 * v + 1).1 ∈ Y) && decide ((2 * v, 2 * v + 1).2 ∈ Y)) =
          true := by simp [h2v, h2v1]
      have hf1 : (List.replicate D (2 * v, 2 * v + 1)).filter
          (fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)) = List.replicate D (2 * v, 2 * v + 1) := by
        rw [List.filter_replicate, ite_eq_left_iff.mpr fun hn => False.elim (hn hc1)]
      have hl1 : ((List.replicate D (2 * v, 2 * v + 1)).filter fun e => decide (e.1 = 2 * v)).length = D := by
        rw [List.filter_replicate, ite_eq_left_iff.mpr (by simp), List.length_replicate]
      have hl2 : ((List.replicate D (2 * v, 2 * v + 1)).filter fun e => decide (e.2 = 2 * v + 1)).length = D := by
        rw [List.filter_replicate, ite_eq_left_iff.mpr (by simp), List.length_replicate]
      rw [hf1]
      omega
    · have ih' := ih hmem
      omega

private lemma twinGraph_cutIn_eq {D : ℕ} {G : Cited.Graph} (hV : G.IsValid)
    (Y : Finset ℕ) (S : Finset ℕ) :
    (twinGraph D G).cutIn Y (Y.filter fun z => z / 2 ∈ S) = G.cutIn (partX G.n Y) S := by
  set S_twin := Y.filter fun z => z / 2 ∈ S
  unfold Cited.Graph.cutIn
  rw [inside_twinGraph_eq hV Y, List.filter_append, List.length_append]
  have hzero : (((((List.range G.n).flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
      fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y))).filter
      fun e => decide (e.1 ∈ S_twin) != decide (e.2 ∈ S_twin)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.mem_flatMap,
      List.mem_replicate] at he
    rcases he with ⟨⟨u, _, _, rfl⟩, h2uY, h2u1Y⟩
    have h1 : (2 * u) / 2 = u := by omega
    have h2 : (2 * u + 1) / 2 = u := by omega
    simp [S_twin, Finset.mem_filter, h2uY, h2u1Y, h1, h2]
  rw [hzero, Nat.add_zero]
  rw [List.filter_map]
  simp only [List.length_map]
  congr 1
  apply List.filter_congr
  intro e he
  rw [mem_inside_iff] at he
  rcases he with ⟨_, he1X, he2X⟩
  have he1Y : 2 * e.1 ∈ Y := (Finset.mem_filter.mp he1X).2
  have he2Y : 2 * e.2 ∈ Y := (Finset.mem_filter.mp he2X).2
  have h1 : (2 * e.1 ∈ S_twin) ↔ e.1 ∈ S := by simp [S_twin, he1Y]
  have h2 : (2 * e.2 ∈ S_twin) ↔ e.2 ∈ S := by simp [S_twin, he2Y]
  by_cases hs1 : e.1 ∈ S <;> by_cases hs2 : e.2 ∈ S <;> simp [h1, h2, hs1, hs2]

private lemma twinGraph_degIn_ge {D : ℕ} {G : Cited.Graph} (hV : G.IsValid)
    (Y : Finset ℕ) {u : ℕ} (_hu : u ∈ partX G.n Y) :
    G.degIn (partX G.n Y) u ≤ (twinGraph D G).degIn Y (2 * u) := by
  unfold Cited.Graph.degIn
  rw [inside_twinGraph_eq hV Y]
  simp only [List.filter_append, List.length_append, List.filter_map, List.length_map,
    Function.comp_def]
  have h1 : ((G.inside (partX G.n Y)).filter (fun e => decide (2 * e.1 = 2 * u))).length =
      ((G.inside (partX G.n Y)).filter (fun e => decide (e.1 = u))).length := by
    congr 1
    apply List.filter_congr
    intro e _
    simp [Nat.mul_right_inj (by omega : 2 ≠ 0)]
  have h2 : ((G.inside (partX G.n Y)).filter (fun e => decide (2 * e.2 = 2 * u))).length =
      ((G.inside (partX G.n Y)).filter (fun e => decide (e.2 = u))).length := by
    congr 1
    apply List.filter_congr
    intro e _
    simp [Nat.mul_right_inj (by omega : 2 ≠ 0)]
  rw [← h1, ← h2]
  omega

lemma twinGraph_volIn_le {D : ℕ} {G : Cited.Graph} (hV : G.IsValid)
    (Y : Finset ℕ) {T : Finset ℕ} (hT : T ⊆ partX G.n Y)
    {Q : Finset ℕ} (hTQ : ∀ u ∈ T, 2 * u ∈ Q) :
    G.volIn (partX G.n Y) T ≤ (twinGraph D G).volIn Y Q := by
  unfold Cited.Graph.volIn
  calc ∑ u ∈ T, G.degIn (partX G.n Y) u
      ≤ ∑ u ∈ T, (twinGraph D G).degIn Y (2 * u) :=
        Finset.sum_le_sum fun u hu => twinGraph_degIn_ge hV Y (hT hu)
    _ = ∑ z ∈ T.image (fun u => 2 * u), (twinGraph D G).degIn Y z := by
        rw [Finset.sum_image (f := fun z => (twinGraph D G).degIn Y z) (g := fun u => 2 * u)
          (fun a _ b _ hab => by dsimp only at hab; omega)]
    _ ≤ ∑ z ∈ Q, (twinGraph D G).degIn Y z := by
        apply Finset.sum_le_sum_of_subset
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
        exact hTQ u hu

/-- Projects `φ_B1`-conductance on `Y` in `twinGraph D G` to `φ_B1`-conductance on `partX G.n Y`
in `G`. -/
lemma conductance_of_twin {D : ℕ} {G : Cited.Graph} (hV : G.IsValid)
    {Y : Finset ℕ} {φ_B1 : ℝ} (hφ₀ : 0 ≤ φ_B1)
    (hexpY : (twinGraph D G).IsConductanceExpanderOn Y φ_B1) :
    G.IsConductanceExpanderOn (partX G.n Y) φ_B1 := by
  intro S hSX hSne hSneX
  set X := partX G.n Y
  set S_twin := Y.filter fun z => z / 2 ∈ S
  have hSubY : S_twin ⊆ Y := Finset.filter_subset _ _
  have hSneY : S_twin.Nonempty := by
    rcases hSne with ⟨u, huS⟩
    have huY : 2 * u ∈ Y := (Finset.mem_filter.mp (hSX huS)).2
    exact ⟨2 * u, Finset.mem_filter.mpr ⟨huY, by simp [huS]⟩⟩
  have hSneYY : S_twin ≠ Y := by
    have hdiff : (X \ S).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
      exact hSneX (Finset.Subset.antisymm hSX h)
    rcases hdiff with ⟨w, hw⟩
    rw [Finset.mem_sdiff] at hw
    have hwY : 2 * w ∈ Y := (Finset.mem_filter.mp hw.1).2
    intro hEq
    have hwS : 2 * w ∈ S_twin := hEq ▸ hwY
    have : w ∈ S := by simpa using (Finset.mem_filter.mp hwS).2
    exact hw.2 this
  have h1 : G.volIn X S ≤ (twinGraph D G).volIn Y S_twin := by
    apply twinGraph_volIn_le hV Y hSX
    intro u hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hSX hu)).2, by simp [hu]⟩
  have h2 : G.volIn X (X \ S) ≤ (twinGraph D G).volIn Y (Y \ S_twin) := by
    apply twinGraph_volIn_le hV Y Finset.sdiff_subset
    intro u hu
    rw [Finset.mem_sdiff] at hu
    have huY : 2 * u ∈ Y := (Finset.mem_filter.mp hu.1).2
    rw [Finset.mem_sdiff]
    exact ⟨huY, fun hm => hu.2 (by simpa using (Finset.mem_filter.mp hm).2)⟩
  have hexp := hexpY S_twin hSubY hSneY hSneYY
  rw [twinGraph_cutIn_eq hV Y S] at hexp
  have hmin : min (↑(G.volIn X S) : ℝ) (↑(G.volIn X (X \ S)) : ℝ) ≤
      min (↑((twinGraph D G).volIn Y S_twin) : ℝ) (↑((twinGraph D G).volIn Y (Y \ S_twin)) : ℝ) :=
    le_min (le_trans (min_le_left _ _) (by exact_mod_cast h1))
      (le_trans (min_le_right _ _) (by exact_mod_cast h2))
  exact le_trans (mul_le_mul_of_nonneg_left hmin hφ₀) hexp

private lemma inside_loopless_length_le_vol {G : Cited.Graph} (_hL : G.IsLoopless)
    {X T : Finset ℕ} (_hTX : T ⊆ X) :
    (G.inside X).length - (G.inside (X \ T)).length ≤ G.volIn X T := by
  have hsub : G.inside (X \ T) =
      (G.inside X).filter fun e => decide (e.1 ∉ T) && decide (e.2 ∉ T) := by
    unfold Cited.Graph.inside
    rw [List.filter_filter]
    congr 1
    ext e
    by_cases h1 : e.1 ∈ X <;> by_cases h2 : e.2 ∈ X <;>
      by_cases t1 : e.1 ∈ T <;> by_cases t2 : e.2 ∈ T <;>
      simp [Finset.mem_sdiff, h1, h2, t1, t2]
  rw [hsub]
  have hle : (G.inside X).length -
      ((G.inside X).filter fun e => decide (e.1 ∉ T) && decide (e.2 ∉ T)).length ≤
      ((G.inside X).filter fun e => decide (e.1 ∈ T) || decide (e.2 ∈ T)).length := by
    suffices h : ∀ (L : List (ℕ × ℕ)),
        L.length ≤ (L.filter fun e => decide (e.1 ∉ T) && decide (e.2 ∉ T)).length +
          (L.filter fun e => decide (e.1 ∈ T) || decide (e.2 ∈ T)).length by
      have := h (G.inside X)
      omega
    intro L
    induction L with
    | nil => simp
    | cons e es ih =>
      simp only [List.length_cons, List.filter_cons]
      by_cases ht1 : e.1 ∈ T <;> by_cases ht2 : e.2 ∈ T
      · simp [ht1, ht2] at *; omega
      · simp [ht1, ht2] at *; omega
      · simp [ht1, ht2] at *; omega
      · simp [ht1, ht2] at *; omega
  refine le_trans hle ?_
  clear hsub hle
  have hvol : G.volIn X T =
      ((G.inside X).map fun e => (if e.1 ∈ T then 1 else 0) + (if e.2 ∈ T then 1 else 0)).sum := by
    unfold Cited.Graph.volIn Cited.Graph.degIn
    rw [Finset.sum_add_distrib]
    have hs1 : ∀ (L : List (ℕ × ℕ)),
        (∑ v ∈ T, (L.filter fun e => decide (e.1 = v)).length) =
          (L.map fun e => if e.1 ∈ T then 1 else 0).sum := by
      intro L
      induction L with
      | nil => simp
      | cons e es ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        have heq : (∑ v ∈ T, (if decide (e.1 = v) then e :: List.filter (fun x => decide (x.1 = v)) es
            else List.filter (fun x => decide (x.1 = v)) es).length) =
            ∑ v ∈ T, ((if e.1 = v then 1 else 0) + (List.filter (fun x => decide (x.1 = v)) es).length) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : e.1 = v <;> simp [h, Nat.add_comm]
        rw [heq, Finset.sum_add_distrib, ih]
        have hpt : (∑ v ∈ T, if e.1 = v then 1 else 0) = if e.1 ∈ T then 1 else 0 := by
          simp only [eq_comm (a := e.1)]
          rw [Finset.sum_ite_eq']
        rw [hpt]
    have hs2 : ∀ (L : List (ℕ × ℕ)),
        (∑ v ∈ T, (L.filter fun e => decide (e.2 = v)).length) =
          (L.map fun e => if e.2 ∈ T then 1 else 0).sum := by
      intro L
      induction L with
      | nil => simp
      | cons e es ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        have heq : (∑ v ∈ T, (if decide (e.2 = v) then e :: List.filter (fun x => decide (x.2 = v)) es
            else List.filter (fun x => decide (x.2 = v)) es).length) =
            ∑ v ∈ T, ((if e.2 = v then 1 else 0) + (List.filter (fun x => decide (x.2 = v)) es).length) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : e.2 = v <;> simp [h, Nat.add_comm]
        rw [heq, Finset.sum_add_distrib, ih]
        have hpt : (∑ v ∈ T, if e.2 = v then 1 else 0) = if e.2 ∈ T then 1 else 0 := by
          simp only [eq_comm (a := e.2)]
          rw [Finset.sum_ite_eq']
        rw [hpt]
    rw [hs1, hs2]
    induction (G.inside X) with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      omega
  rw [hvol]
  induction (G.inside X) with
  | nil => simp
  | cons e es ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases ht1 : e.1 ∈ T <;> by_cases ht2 : e.2 ∈ T
    · simp only [ht1, ht2, ↓reduceIte, decide_true, Bool.or_self, List.length_cons]; omega
    · simp only [ht1, ht2, ↓reduceIte, decide_true, decide_false, Bool.or_false, List.length_cons]; omega
    · simp only [ht1, ht2, ↓reduceIte, decide_false, decide_true, Bool.false_or, List.length_cons]; omega
    · simp only [ht1, ht2, ↓reduceIte, decide_false, Bool.or_self, Bool.false_eq_true]; omega

lemma inside_sub_length_le_vol {G : Cited.Graph} (hL : G.IsLoopless)
    {X R : Finset ℕ} (hRX : R ⊆ X) :
    (G.inside X).length - (G.inside R).length ≤ G.volIn X (X \ R) := by
  have heq : X \ (X \ R) = R := Finset.sdiff_sdiff_eq_self hRX
  have h := inside_loopless_length_le_vol hL Finset.sdiff_subset (X := X) (T := X \ R)
  rwa [heq] at h

lemma inside_card_le_one_eq_nil {G : Cited.Graph} (hL : G.IsLoopless)
    {R : Finset ℕ} (hR : R.card ≤ 1) : G.inside R = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  rw [mem_inside_iff] at he
  have hmem := he.1
  have hne := hL e hmem
  have h1 : e.1 ∈ R := he.2.1
  have h2 : e.2 ∈ R := he.2.2
  rcases Finset.card_le_one.mp hR e.1 h1 e.2 h2 with heq
  exact hne heq

private lemma twin_cut_pair_eq_deg {D : ℕ} {G : Cited.Graph} (hV : G.IsValid) (hL : G.IsLoopless)
    (Y : Finset ℕ) (v : ℕ) :
    (twinGraph D G).cutIn Y {2 * v, 2 * v + 1} = G.degIn (partX G.n Y) v := by
  set P : Finset ℕ := {2 * v, 2 * v + 1}
  unfold Cited.Graph.cutIn Cited.Graph.degIn
  rw [inside_twinGraph_eq hV Y, List.filter_append, List.length_append]
  have hzero : (((((List.range G.n).flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter
      fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y))).filter
      fun e => decide (e.1 ∈ P) != decide (e.2 ∈ P)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.mem_flatMap,
      List.mem_replicate] at he
    rcases he with ⟨⟨u, _, _, rfl⟩, _, _⟩
    have h1 : (2 * u) ∈ P ↔ u = v := by simp [P]; omega
    have h2 : (2 * u + 1) ∈ P ↔ u = v := by simp [P]; omega
    simp [h1, h2]
  rw [hzero, Nat.add_zero, List.filter_map, List.length_map]
  suffices hsum : ∀ (L : List (ℕ × ℕ)), (∀ e ∈ L, e.1 ≠ e.2) →
      (L.filter (fun e => decide ((2 * e.1) ∈ P) != decide ((2 * e.2) ∈ P))).length =
      (L.filter fun e => decide (e.1 = v)).length + (L.filter fun e => decide (e.2 = v)).length by
    exact hsum (G.inside (partX G.n Y)) fun e he => hL e (mem_inside_iff.mp he).1
  intro L hLL
  induction L with
  | nil => simp
  | cons e es ih =>
    have hne := hLL e List.mem_cons_self
    have ih' := ih fun x hx => hLL x (List.mem_cons_of_mem _ hx)
    simp only [List.filter_cons]
    have h1 : (2 * e.1) ∈ P ↔ e.1 = v := by simp [P]; omega
    have h2 : (2 * e.2) ∈ P ↔ e.2 = v := by simp [P]; omega
    by_cases hv1 : e.1 = v <;> by_cases hv2 : e.2 = v
    · exact False.elim (hne (hv1.trans hv2.symm))
    · have hp1 : 2 * e.1 ∈ P := h1.mpr hv1
      have hp2 : 2 * e.2 ∉ P := fun hm => hv2 (h2.mp hm)
      have hne1 : (decide ((2 * e.1) ∈ P) != decide ((2 * e.2) ∈ P)) = true := by simp [hp1, hp2]
      have hd1 : decide (e.1 = v) = true := decide_eq_true hv1
      have hd2 : decide (e.2 = v) = false := decide_eq_false hv2
      rw [hne1, hd1, hd2]
      simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]
      omega
    · have hp1 : 2 * e.1 ∉ P := fun hm => hv1 (h1.mp hm)
      have hp2 : 2 * e.2 ∈ P := h2.mpr hv2
      have hne1 : (decide ((2 * e.1) ∈ P) != decide ((2 * e.2) ∈ P)) = true := by simp [hp1, hp2]
      have hd1 : decide (e.1 = v) = false := decide_eq_false hv1
      have hd2 : decide (e.2 = v) = true := decide_eq_true hv2
      rw [hne1, hd1, hd2]
      simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]
      omega
    · have hp1 : 2 * e.1 ∉ P := fun hm => hv1 (h1.mp hm)
      have hp2 : 2 * e.2 ∉ P := fun hm => hv2 (h2.mp hm)
      have hne1 : (decide ((2 * e.1) ∈ P) != decide ((2 * e.2) ∈ P)) = false := by simp [hp1, hp2]
      have hd1 : decide (e.1 = v) = false := decide_eq_false hv1
      have hd2 : decide (e.2 = v) = false := decide_eq_false hv2
      rw [hne1, hd1, hd2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih'

lemma subcase1_drop {D : ℕ} {curG : Cited.Graph} (hV : curG.IsValid) (hL : curG.IsLoopless)
    (hD : 1 ≤ D) {Y : Finset ℕ} {φ_B1 : ℝ} (hφ₀ : 0 < φ_B1)
    (hexpY : (twinGraph D curG).IsConductanceExpanderOn Y φ_B1)
    (hcard : 2 ≤ (partX curG.n Y).card)
    {v : ℕ} (hvX : v ∈ partX curG.n Y)
    (hvDeg : (curG.degIn (partX curG.n Y) v : ℝ) < φ_B1 * (D : ℝ))
    (h2v1 : 2 * v + 1 ∈ Y) :
    (curG.inside (partX curG.n Y)).length ≤ 15 * (twinGraph D curG).cut Y := by
  set X := partX curG.n Y
  set S_pair : Finset ℕ := {2 * v, 2 * v + 1}
  have hv_lt : v < curG.n := Finset.mem_range.mp (Finset.mem_filter.mp hvX).1
  have h2v : 2 * v ∈ Y := (Finset.mem_filter.mp hvX).2
  have hSub : S_pair ⊆ Y := by
    intro z hz
    simp only [S_pair, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hSne : S_pair.Nonempty := ⟨2 * v, by simp [S_pair]⟩
  have hXdiff : (X \ {v}).Nonempty := by
    rw [← Finset.card_pos]
    have : ({v} : Finset ℕ).card = 1 := Finset.card_singleton v
    have hle : 1 ≤ (X \ {v}).card := by
      have hcard_sdiff := Finset.card_sdiff_add_card_inter X {v}
      have : (X ∩ {v}).card ≤ 1 := by
        calc (X ∩ {v}).card ≤ ({v} : Finset ℕ).card := Finset.card_le_card Finset.inter_subset_right
          _ = 1 := Finset.card_singleton v
      omega
    omega
  rcases hXdiff with ⟨w₀, hw₀⟩
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hw₀
  have hSneY : S_pair ≠ Y := by
    intro hEq
    have hw0Y : 2 * w₀ ∈ Y := (Finset.mem_filter.mp hw₀.1).2
    have hw0P : 2 * w₀ ∈ S_pair := hEq ▸ hw0Y
    simp only [S_pair, Finset.mem_insert, Finset.mem_singleton] at hw0P
    omega
  have hcut := hexpY S_pair hSub hSne hSneY
  rw [twin_cut_pair_eq_deg hV hL Y v] at hcut
  have hvolPair : 2 * D ≤ (twinGraph D curG).volIn Y S_pair :=
    twin_pair_inside_vol hV hv_lt h2v h2v1 (by simp [S_pair]) (by simp [S_pair])
  have hlt_min : min (↑((twinGraph D curG).volIn Y S_pair) : ℝ)
      (↑((twinGraph D curG).volIn Y (Y \ S_pair)) : ℝ) < (D : ℝ) := by
    nlinarith
  have hvolRem : (twinGraph D curG).volIn Y (Y \ S_pair) < D := by
    have hD_le : (D : ℝ) ≤ ↑((twinGraph D curG).volIn Y S_pair) := by
      exact_mod_cast (show D ≤ 2 * D by omega).trans hvolPair
    have hmin_eq : min (↑((twinGraph D curG).volIn Y S_pair) : ℝ)
        (↑((twinGraph D curG).volIn Y (Y \ S_pair)) : ℝ) =
        ↑((twinGraph D curG).volIn Y (Y \ S_pair)) := by
      rw [min_eq_right_iff]
      by_contra hgt
      push Not at hgt
      linarith [min_eq_left hgt.le]
    rw [hmin_eq] at hlt_min
    exact_mod_cast hlt_min
  have hw0_not : 2 * w₀ + 1 ∉ Y := by
    intro hm
    have hw0_lt : w₀ < curG.n := Finset.mem_range.mp (Finset.mem_filter.mp hw₀.1).1
    have h1 : 2 * w₀ ∈ Y \ S_pair := Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hw₀.1).2, by
      simp [S_pair]; omega⟩
    have h2 : 2 * w₀ + 1 ∈ Y \ S_pair := Finset.mem_sdiff.mpr ⟨hm, by
      simp [S_pair]; omega⟩
    have hv2 := twin_pair_inside_vol hV (D := D) hw0_lt (Finset.mem_filter.mp hw₀.1).2 hm h1 h2
    omega
  have hcut_ge_D : D ≤ (twinGraph D curG).cut Y := by
    have h1 := twin_cut_ge_of_mem_not_twin hV (D := D) (Y := Y) (B := {w₀})
      (fun b hb => by simp at hb; subst hb; exact Finset.mem_range.mp (Finset.mem_filter.mp hw₀.1).1)
      (fun b hb => by simp at hb; subst hb; exact (Finset.mem_filter.mp hw₀.1).2)
      (fun b hb => by simp at hb; subst hb; exact hw0_not)
    simpa using h1
  have hinside_le_vol : (curG.inside X).length ≤ curG.volIn X (X \ {v}) := by
    have heq : (curG.inside {v}).length = 0 := by
      rw [inside_card_le_one_eq_nil hL (by simp)]
      rfl
    have h := inside_loopless_length_le_vol hL (X := X) (T := X \ {v}) Finset.sdiff_subset
    have hss : X \ (X \ {v}) = {v} := Finset.sdiff_sdiff_eq_self (Finset.singleton_subset_iff.mpr hvX)
    rw [hss, heq, Nat.sub_zero] at h
    exact h
  have hvol_le : curG.volIn X (X \ {v}) ≤ (twinGraph D curG).volIn Y (Y \ S_pair) := by
    apply twinGraph_volIn_le hV Y Finset.sdiff_subset
    intro u hu
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hu
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hu.1).2, by simp [S_pair]; omega⟩
  omega

/-- Specification of `decomposePartFull`: either `R = ∅` or `2 ≤ R.card`, `R ⊆ partX curG.n Y`,
`curG.IsConductanceExpanderOn R (φ_B1 / 3)`, `∀ v ∈ R, (φ_B1 / 3) * D ≤ curG.degIn R v`,
dropped inside-edges are at most `15 * (twinGraph D curG).cut Y`, and pruning steps are bounded. -/
lemma decomposePartFull_spec {D : ℕ} {curG : Cited.Graph} (hV : curG.IsValid) (hL : curG.IsLoopless)
    (hD : 1 ≤ D) {Y : Finset ℕ} {φ_B1 : ℝ} (hφ₀ : 0 < φ_B1) (hφ_le : φ_B1 ≤ 1)
    (hexpY : (twinGraph D curG).IsConductanceExpanderOn Y φ_B1) :
    let X := partX curG.n Y
    let (R, st) := decomposePartFull curG D φ_B1 Y
    let C_max := max 7 (Nat.ceil (4 / φ_B1) + 2)
    let H_max := 4 * C_max * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
    R ⊆ X ∧
    (R = ∅ ∨
      (2 ≤ R.card ∧ curG.IsConductanceExpanderOn R (φ_B1 / 3) ∧
        ∀ v ∈ R, (φ_B1 / 3) * (D : ℝ) ≤ (curG.degIn R v : ℝ))) ∧
    (curG.inside X).length - (curG.inside R).length ≤ 15 * (twinGraph D curG).cut Y ∧
    (X.card ≤ 1 → st = 0) ∧
    st ≤ (4 * H_max + 14) * (4 * H_max + 4) * (2 * (curG.inside X).length + 1) := by
  dsimp only [decomposePartFull]
  set X := partX curG.n Y
  set C_max := max 7 (Nat.ceil (4 / φ_B1) + 2)
  set H_max := 4 * C_max * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
  by_cases hcard : X.card ≤ 1
  · simp only [hcard, ↓reduceIte]
    have hnil : curG.inside X = [] := inside_card_le_one_eq_nil hL hcard
    refine ⟨Finset.empty_subset X, Or.inl trivial, ?_, fun _ => trivial, Nat.zero_le _⟩
    simp [hnil]
  · simp only [hcard, ↓reduceIte]
    set B := X.filter fun v => decide ((curG.degIn X v : ℝ) < φ_B1 * (D : ℝ))
    by_cases hcase1 : ∃ v ∈ B, 2 * v + 1 ∈ Y
    · simp only [hcase1, ↓reduceIte]
      rcases hcase1 with ⟨v, hvB, h2v1⟩
      have hv := Finset.mem_filter.mp hvB
      have hvDeg : (curG.degIn X v : ℝ) < φ_B1 * (D : ℝ) := decide_eq_true_eq.mp hv.2
      have hdrop := subcase1_drop hV hL hD hφ₀ hexpY (by change 2 ≤ X.card; omega) hv.1 hvDeg h2v1
      have hnil0 : curG.inside ∅ = [] := inside_card_le_one_eq_nil hL (by simp)
      refine ⟨Finset.empty_subset X, Or.inl trivial, ?_, fun hc => False.elim hc, Nat.zero_le _⟩
      rw [hnil0]; simpa using hdrop
    · simp only [hcase1, ↓reduceIte]
      have hBX : B ⊆ X := Finset.filter_subset _ _
      have hexpX : curG.IsConductanceExpanderOn X φ_B1 :=
        conductance_of_twin hV hφ₀.le hexpY
      have hθ : ∀ v ∈ X, v ∉ B → φ_B1 * (D : ℝ) ≤ (curG.degIn X v : ℝ) := by
        intro v hvX hvB
        by_contra hlt
        push Not at hlt
        exact hvB (Finset.mem_filter.mpr ⟨hvX, decide_eq_true hlt⟩)
      have hspec := pruneExpander_spec hV hBX hexpX hφ₀ hθ
      set cfg := pruneCfgOf curG X B φ_B1 (φ_B1 * (D : ℝ))
      set sFin := pruneFinalState cfg
      set R := pruneExpander curG X B φ_B1 (φ_B1 * (D : ℝ))
      rcases hspec with ⟨hRsub, hexpR, hdegR, _, hvolXR, hsteps⟩
      have hRX : R ⊆ X := hRsub.trans Finset.sdiff_subset
      have hB_twin : ∀ b ∈ B, 2 * b ∈ Y ∧ 2 * b + 1 ∉ Y := by
        intro b hbB
        have hbX := hBX hbB
        refine ⟨(Finset.mem_filter.mp hbX).2, fun hm => hcase1 ⟨b, hbB, hm⟩⟩
      have hcut_ge_B : D * B.card ≤ (twinGraph D curG).cut Y :=
        twin_cut_ge_of_mem_not_twin hV
          (fun b hb => Finset.mem_range.mp (Finset.mem_filter.mp (hBX hb)).1)
          (fun b hb => (hB_twin b hb).1) (fun b hb => (hB_twin b hb).2)
      have hvolB_le : (curG.volIn X B : ℝ) ≤ φ_B1 * ((twinGraph D curG).cut Y : ℝ) := by
        have hsum : (curG.volIn X B : ℝ) ≤ ∑ _ ∈ B, (φ_B1 * (D : ℝ)) := by
          unfold Cited.Graph.volIn
          push_cast
          apply Finset.sum_le_sum
          intro b hb
          exact le_of_lt (decide_eq_true_eq.mp (Finset.mem_filter.mp hb).2)
        rw [Finset.sum_const, nsmul_eq_mul] at hsum
        have hcut_R : (D : ℝ) * (B.card : ℝ) ≤ ((twinGraph D curG).cut Y : ℝ) := by
          exact_mod_cast hcut_ge_B
        nlinarith
      have h2C : ((2 * cfg.C_cap + 1 : ℕ) : ℝ) * φ_B1 ≤ 15 := by
        have hCdef : cfg.C_cap = max 7 (Nat.ceil (4 / φ_B1) + 2) := rfl
        have hCbound : (cfg.C_cap : ℝ) ≤ max 7 (4 / φ_B1 + 3) := by
          rw [hCdef]
          by_cases h7 : Nat.ceil (4 / φ_B1) + 2 ≤ 7
          · rw [max_eq_left h7]; exact le_max_left _ _
          · rw [max_eq_right (le_of_not_ge h7)]
            have hceil : (Nat.ceil (4 / φ_B1) : ℝ) < 4 / φ_B1 + 1 :=
              Nat.ceil_lt_add_one (div_nonneg (by norm_num) hφ₀.le)
            refine le_trans ?_ (le_max_right 7 (4 / φ_B1 + 3))
            push_cast
            linarith
        have hprod : (2 * (cfg.C_cap : ℝ) + 1) * φ_B1 ≤
            max (15 * φ_B1) (8 + 7 * φ_B1) := by
          rcases le_max_iff.mp hCbound with h1 | h2
          · have hmul : (2 * (cfg.C_cap : ℝ) + 1) * φ_B1 ≤ 15 * φ_B1 :=
              mul_le_mul_of_nonneg_right (by linarith) hφ₀.le
            exact le_trans hmul (le_max_left _ _)
          · have htmp : (2 * (cfg.C_cap : ℝ) + 1) * φ_B1 ≤ (2 * (4 / φ_B1 + 3) + 1) * φ_B1 :=
              mul_le_mul_of_nonneg_right (by linarith) hφ₀.le
            have heq : (2 * (4 / φ_B1 + 3) + 1) * φ_B1 = 8 + 7 * φ_B1 := by
              field_simp [hφ₀.ne']
              ring
            rw [heq] at htmp
            exact le_trans htmp (le_max_right _ _)
        have hmax15 : max (15 * φ_B1) (8 + 7 * φ_B1) ≤ 15 := max_le (by linarith) (by linarith)
        push_cast
        exact le_trans hprod hmax15
      have hvolXR_le : curG.volIn X (X \ R) ≤ 15 * (twinGraph D curG).cut Y := by
        have hcutB : curG.cutIn X B ≤ curG.volIn X B := cutIn_le_volIn curG X B
        have hvol_nat : curG.volIn X (X \ R) ≤ (2 * cfg.C_cap + 1) * curG.volIn X B := by
          nlinarith
        have hvol_R : (curG.volIn X (X \ R) : ℝ) ≤
            ((2 * cfg.C_cap + 1 : ℕ) : ℝ) * (φ_B1 * ((twinGraph D curG).cut Y : ℝ)) :=
          le_trans (by exact_mod_cast hvol_nat)
            (mul_le_mul_of_nonneg_left hvolB_le (Nat.cast_nonneg _))
        have h15_R : (curG.volIn X (X \ R) : ℝ) ≤ 15 * ((twinGraph D curG).cut Y : ℝ) := by
          have : ((2 * cfg.C_cap + 1 : ℕ) : ℝ) * (φ_B1 * ((twinGraph D curG).cut Y : ℝ)) =
              (((2 * cfg.C_cap + 1 : ℕ) : ℝ) * φ_B1) * ((twinGraph D curG).cut Y : ℝ) := by ring
          rw [this] at hvol_R
          exact le_trans hvol_R (mul_le_mul_of_nonneg_right h2C (Nat.cast_nonneg _))
        exact_mod_cast h15_R
      have hinside_le : (curG.inside X).length - (curG.inside R).length ≤ 15 * (twinGraph D curG).cut Y :=
        le_trans (inside_sub_length_le_vol hL hRX) hvolXR_le
      have hH_le : cfg.H ≤ H_max := by
        have hC_eq : cfg.C_cap = C_max := rfl
        have hins_le : (curG.inside X).length ≤ curG.m := by
          unfold Cited.Graph.inside Cited.Graph.m
          exact List.length_filter_le _ _
        have hlog : Nat.log 2 (2 * (curG.inside X).length + 1) ≤ Nat.log 2 (2 * curG.m + 1) :=
          Nat.log_mono_right (by omega)
        change 4 * cfg.C_cap * (Nat.log 2 (2 * (curG.inside X).length + 1) + 1) + 2 ≤
          4 * C_max * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
        rw [hC_eq]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)) 2
      have hsteps_max : sFin.steps ≤ (4 * H_max + 14) * (4 * H_max + 4) * (2 * (curG.inside X).length + 1) := by
        refine le_trans hsteps ?_
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (by omega) (by omega)
      by_cases hR1 : R.card ≤ 1
      · simp only [hR1, ↓reduceIte]
        have hnilR : curG.inside R = [] := inside_card_le_one_eq_nil hL hR1
        have hnil0 : curG.inside ∅ = [] := inside_card_le_one_eq_nil hL (by simp)
        refine ⟨Finset.empty_subset X, Or.inl trivial, ?_, fun hc => False.elim hc, hsteps_max⟩
        rw [hnilR] at hinside_le
        rw [hnil0]
        simpa using hinside_le
      · simp only [hR1, ↓reduceIte]
        refine ⟨hRX, Or.inr ⟨by omega, hexpR, fun v hv => by linarith [hdegR v hv]⟩,
          hinside_le, fun hc => False.elim hc, hsteps_max⟩

lemma sum_filter_any_le {α β : Type*} (L : List α) (p : β → α → Bool) :
    ∀ (xs : List β), (L.filter fun a => xs.any fun b => p b a).length ≤
      (xs.map fun b => (L.filter fun a => p b a).length).sum
  | [] => by simp
  | b :: bs => by
    have ih := sum_filter_any_le L p bs
    simp only [List.any_cons, List.map_cons, List.sum_cons]
    have hor : (L.filter fun a => p b a || bs.any fun c => p c a).length ≤
        (L.filter fun a => p b a).length + (L.filter fun a => bs.any fun c => p c a).length := by
      clear ih
      induction L with
      | nil => simp
      | cons a as ihl =>
        simp only [List.filter_cons]
        cases p b a <;> cases bs.any (fun c => p c a) <;> simp <;> omega
    omega

private lemma sum_card_pairwiseDisjoint :
    ∀ (Xs : List (Finset ℕ)) (S : Finset ℕ),
      Xs.Pairwise Disjoint → (∀ X ∈ Xs, X ⊆ S) →
      (Xs.map Finset.card).sum ≤ S.card
  | [], _, _, _ => by simp
  | X :: rest, S, hpw, hsub => by
    simp only [List.pairwise_cons] at hpw
    have hXsub : X ⊆ S := hsub X List.mem_cons_self
    have hrest_sub : ∀ R ∈ rest, R ⊆ S \ X := fun R hR x hx =>
      Finset.mem_sdiff.mpr ⟨hsub R (List.mem_cons_of_mem _ hR) hx,
        Finset.disjoint_right.mp (hpw.1 R hR) hx⟩
    have ih := sum_card_pairwiseDisjoint rest (S \ X) hpw.2 hrest_sub
    have hcs : X.card + (S \ X).card = S.card := by
      have := Finset.card_sdiff_add_card_inter S X
      have hint : S ∩ X = X := Finset.inter_eq_right.mpr hXsub
      rw [hint] at this
      omega
    simp only [List.map_cons, List.sum_cons]
    omega

lemma list_filter_disjoint_edges_le :
    ∀ (Xs : List (Finset ℕ)) (L : List (ℕ × ℕ)),
      Xs.Pairwise Disjoint →
      (Xs.map fun X => (L.filter fun e => decide (e.1 ∈ X) && decide (e.2 ∈ X)).length).sum ≤
        L.length
  | [], _, _ => by simp
  | X :: rest, L, hpw => by
    simp only [List.pairwise_cons] at hpw
    have hsub : ∀ R ∈ rest,
        (L.filter fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)) =
        ((L.filter fun e => !(decide (e.1 ∈ X) && decide (e.2 ∈ X))).filter
          fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)) := by
      intro R hR
      rw [List.filter_filter]
      congr 1
      ext e
      by_cases he1R : e.1 ∈ R <;> by_cases he2R : e.2 ∈ R
      · have he1X : e.1 ∉ X := Finset.disjoint_right.mp (hpw.1 R hR) he1R
        simp [he1R, he2R, he1X]
      · simp [he1R, he2R]
      · simp [he1R, he2R]
      · simp [he1R, he2R]
    have hrest : (rest.map fun R => (L.filter fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)).length) =
        (rest.map fun R => ((L.filter fun e => !(decide (e.1 ∈ X) && decide (e.2 ∈ X))).filter
          fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)).length) := by
      apply List.map_congr_left
      intro R hR
      rw [hsub R hR]
    have ih := list_filter_disjoint_edges_le rest
      (L.filter fun e => !(decide (e.1 ∈ X) && decide (e.2 ∈ X))) hpw.2
    have hcomp := (filter_comp_perm (fun e : ℕ × ℕ => decide (e.1 ∈ X) && decide (e.2 ∈ X)) L).length_eq
    rw [List.length_append] at hcomp
    simp only [List.map_cons, List.sum_cons, hrest]
    omega

lemma partsOf_toList_pairwiseDisjoint (G : Cited.Graph) (label : List ℕ) :
    (Cited.partsOf G label).toList.Pairwise Disjoint := by
  have hnodup := Finset.nodup_toList (Cited.partsOf G label)
  have hpd := partsOf_pairwiseDisjoint G label
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact hpd (Finset.mem_toList.mp (List.getElem_mem hi))
    (Finset.mem_toList.mp (List.getElem_mem hj))
    (fun heq => by
      have : i = j := List.Nodup.getElem_inj_iff hnodup |>.mp heq
      omega)

lemma partX_disjoint {n : ℕ} {Y₁ Y₂ : Finset ℕ} (hdisj : Disjoint Y₁ Y₂) :
    Disjoint (partX n Y₁) (partX n Y₂) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hv1).2 (Finset.mem_filter.mp hv2).2

lemma pairwise_partX_disjoint (n : ℕ) {parts : List (Finset ℕ)}
    (hpw : parts.Pairwise Disjoint) :
    (parts.map (partX n)).Pairwise Disjoint := by
  induction parts with
  | nil => simp
  | cons Y Ys ih =>
    simp only [List.map_cons, List.pairwise_cons] at hpw ⊢
    refine ⟨?_, ih hpw.2⟩
    intro Z hZ
    rcases List.mem_map.mp hZ with ⟨Y', hY', rfl⟩
    exact partX_disjoint (hpw.1 Y' hY')

lemma inside_partX_diff_len (curG : Cited.Graph) (X R : Finset ℕ) (hRX : R ⊆ X) :
    ((curG.inside X).filter fun e => !(decide (e.1 ∈ R) && decide (e.2 ∈ R))).length =
      (curG.inside X).length - (curG.inside R).length := by
  have hsub : curG.inside R =
      (curG.inside X).filter fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R) := by
    unfold Cited.Graph.inside
    rw [List.filter_filter]
    congr 1
    ext e
    by_cases h1 : e.1 ∈ R <;> by_cases h2 : e.2 ∈ R
    · simp [h1, h2, hRX h1, hRX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hcomp := (filter_comp_perm (fun e : ℕ × ℕ => decide (e.1 ∈ R) && decide (e.2 ∈ R))
    (curG.inside X)).length_eq
  rw [List.length_append, ← hsub] at hcomp
  omega

lemma pairwise_disjoint_filter_map {α : Type*} (f g : α → Finset ℕ) (p : Finset ℕ → Bool) :
    ∀ (ps : List α), (ps.map g).Pairwise Disjoint → (∀ x ∈ ps, f x ⊆ g x) →
      ((ps.map f).filter p).Pairwise Disjoint
  | [], _, _ => by simp
  | x :: xs, hpw, hsub => by
    simp only [List.map_cons, List.pairwise_cons] at hpw
    have ih := pairwise_disjoint_filter_map f g p xs hpw.2 fun y hy => hsub y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.filter_cons]
    by_cases hx : p (f x) = true
    · simp only [hx, ↓reduceIte, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro R hR
      rw [List.mem_filter] at hR
      rcases List.mem_map.mp hR.1 with ⟨y, hy, rfl⟩
      have hdisj_g : Disjoint (g x) (g y) := hpw.1 (g y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
      exact Finset.disjoint_of_subset_left (hsub x List.mem_cons_self)
        (Finset.disjoint_of_subset_right (hsub y (List.mem_cons_of_mem _ hy)) hdisj_g)
    · have hf : p (f x) = false := Bool.eq_false_iff.mpr hx
      simp [hf, ih]

lemma mem_pairwise_disjoint_eq_of_mem_inter :
    ∀ {L : List (Finset ℕ)} (_ : L.Pairwise Disjoint) {R₁ R₂ : Finset ℕ}
      (_ : R₁ ∈ L) (_ : R₂ ∈ L) (x : ℕ), x ∈ R₁ → x ∈ R₂ → R₁ = R₂
  | [], _, _, _, h1, _, _, _, _ => by simp at h1
  | A :: as, hpw, R₁, R₂, h1, h2, x, hx1, hx2 => by
    simp only [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact False.elim (Finset.disjoint_left.mp (hpw.1 R₂ h2') hx1 hx2)
    · exact False.elim (Finset.disjoint_left.mp (hpw.1 R₁ h1') hx2 hx1)
    · exact mem_pairwise_disjoint_eq_of_mem_inter hpw.2 h1' h2' x hx1 hx2

private lemma list_sum_map_le_const_mul {α : Type*} (f g : α → ℕ) (C : ℕ) :
    ∀ (L : List α), (∀ a ∈ L, f a ≤ C * g a) → (L.map f).sum ≤ C * (L.map g).sum
  | [], _ => by simp
  | a :: as, h => by
    have ha := h a List.mem_cons_self
    have ih := list_sum_map_le_const_mul f g C as fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

private lemma list_sum_map_filter_zero {α : Type*} (f : α → ℕ) (p : α → Bool) :
    ∀ (L : List α), (∀ a ∈ L, p a = false → f a = 0) →
      (L.map f).sum = ((L.filter p).map f).sum
  | [], _ => by simp
  | a :: as, h => by
    have ih := list_sum_map_filter_zero f p as fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases hp : p a = true
    · simp [hp, ih]
    · have hf : p a = false := Bool.eq_false_iff.mpr hp
      have ha0 : f a = 0 := h a List.mem_cons_self hf
      simp [hf, ha0, ih]

lemma reachable_stay_in_set {E : List (ℕ × ℕ)} {R : Finset ℕ}
    (hclosed : ∀ e ∈ E, e.1 ∈ R ↔ e.2 ∈ R) {a b : ℕ} {P : List ℕ}
    (hP : Cited.IsPathAlong E a b P) (ha : a ∈ R) : b ∈ R := by
  induction P generalizing a with
  | nil => simp [Cited.IsPathAlong] at hP
  | cons x xs ih =>
    rcases hP with ⟨hx, hlast, hch⟩
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast; exact ha
    | cons y ys =>
      rw [List.isChain_cons_cons] at hch
      have hy : y ∈ R := by
        rcases hch.1 with hm | hm
        · exact (hclosed (x, y) hm).mp ha
        · exact (hclosed (y, x) hm).mpr ha
      exact ih ⟨rfl, by simpa using hlast, hch.2⟩ hy

/-- Specification of one level `decomposeLevel`: preserves `IsValid` and `IsLoopless`, partitions
`curG.edges`, satisfies Claim B.2 (`remG.m ≤ 2^{i-1} * curG.n` when `curG.m ≤ 2^i * curG.n` and
`1 ≤ i`), guarantees every nontrivial connected component `X` of `G_i` is a `(φ_B1 / 3)`-expander
with min degree `≥ (φ_B1 / 3) * 2^i`, and bounds total pruning steps. -/
theorem decomposeLevel_spec {decomp : ℕ → ℕ → Cited.Graph → List ℕ} {φ_B1 : ℝ}
    {curG : Cited.Graph} {i : ℕ} (hV : curG.IsValid) (hL : curG.IsLoopless) (hi : 1 ≤ i)
    (hφ₀ : 0 < φ_B1) (hφ_le : φ_B1 ≤ 1)
    (hm_in : curG.m ≤ 2 ^ i * curG.n)
    (hdec :
      let G_twin := twinGraph (2 ^ i) curG
      let label := decomp 1 200 G_twin
      Cited.IsExpanderDecomposition G_twin (1 / 200 : ℝ) φ_B1 label ∧
        ((G_twin.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
          (1 / 200 : ℝ) * (G_twin.m : ℝ)) :
    let (Gi, remG, levelSteps) := decomposeLevel decomp φ_B1 curG i
    let C_max := max 7 (Nat.ceil (4 / φ_B1) + 2)
    let H_max := 4 * C_max * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
    Gi.n = curG.n ∧ remG.n = curG.n ∧
    Gi.IsValid ∧ Gi.IsLoopless ∧ remG.IsValid ∧ remG.IsLoopless ∧
    (Gi.edges ++ remG.edges).Perm curG.edges ∧
    Gi.m ≤ 2 ^ i * curG.n ∧
    remG.m ≤ 2 ^ (i - 1) * curG.n ∧
    (∀ X ∈ Cited.partsOf Gi (compLabels Gi), 2 ≤ X.card →
      Gi.IsConductanceExpanderOn X (φ_B1 / 3) ∧
      ∀ x ∈ X, (φ_B1 / 3) * (2 : ℝ) ^ i ≤ (Gi.deg x : ℝ)) ∧
    levelSteps ≤ (4 * H_max + 14) * (4 * H_max + 4) * (2 * curG.m + curG.n) ∧
    (Gi.edges = curG.edges.filter (decomposeLevelPred decomp φ_B1 curG i) ∧
     remG.edges = curG.edges.filter (fun e => !decomposeLevelPred decomp φ_B1 curG i e) ∧
     (decomposeLevelComps decomp φ_B1 curG i).Pairwise Disjoint ∧
     (∀ R ∈ decomposeLevelComps decomp φ_B1 curG i,
       R ⊆ curG.verts ∧ 2 ≤ R.card ∧
       Gi.IsConductanceExpanderOn R (φ_B1 / 3) ∧
       (∀ x ∈ R, (φ_B1 / 3) * (2 : ℝ) ^ i ≤ (Gi.degIn R x : ℝ)) ∧
       (∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
     ∀ e ∈ Gi.edges, ∃ R ∈ decomposeLevelComps decomp φ_B1 curG i, e.1 ∈ R ∧ e.2 ∈ R) := by
  dsimp only [decomposeLevel]
  set D := 2 ^ i
  set G_twin := twinGraph D curG
  set label := decomp 1 200 G_twin
  set parts := (Cited.partsOf G_twin label).toList
  set resParts := parts.map fun Y => decomposePartFull curG D φ_B1 Y
  set validRs := (resParts.map Prod.fst).filter fun R => decide (2 ≤ R.card)
  set pred : ℕ × ℕ → Bool := fun e => validRs.any fun R => decide (e.1 ∈ R ∧ e.2 ∈ R)
  set Gi : Cited.Graph := { n := curG.n, edges := curG.edges.filter pred }
  set remG : Cited.Graph := { n := curG.n, edges := curG.edges.filter fun e => !pred e }
  set C_max := max 7 (Nat.ceil (4 / φ_B1) + 2)
  set H_max := 4 * C_max * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
  have hD : 1 ≤ D := Nat.one_le_pow i 2 (by omega)
  have hTV := twinGraph_isValid (D := D) hV
  have hdecExp := hdec.1
  have hdecCut := hdec.2
  have hGiV : Gi.IsValid := fun e he => hV e (List.mem_filter.mp he).1
  have hGiL : Gi.IsLoopless := fun e he => hL e (List.mem_filter.mp he).1
  have hremV : remG.IsValid := fun e he => hV e (List.mem_filter.mp he).1
  have hremL : remG.IsLoopless := fun e he => hL e (List.mem_filter.mp he).1
  have hperm : (Gi.edges ++ remG.edges).Perm curG.edges := filter_comp_perm pred curG.edges
  have hGi_m : Gi.m ≤ 2 ^ i * curG.n := by
    have : Gi.m ≤ curG.m := List.length_filter_le _ _
    exact le_trans this hm_in
  have hpwParts : parts.Pairwise Disjoint := partsOf_toList_pairwiseDisjoint G_twin label
  have hpartSpec : ∀ Y ∈ parts,
      let X := partX curG.n Y
      let (R, st) := decomposePartFull curG D φ_B1 Y
      R ⊆ X ∧
      (R = ∅ ∨
        (2 ≤ R.card ∧ curG.IsConductanceExpanderOn R (φ_B1 / 3) ∧
          ∀ v ∈ R, (φ_B1 / 3) * (D : ℝ) ≤ (curG.degIn R v : ℝ))) ∧
      (curG.inside X).length - (curG.inside R).length ≤ 15 * G_twin.cut Y ∧
      (X.card ≤ 1 → st = 0) ∧
      st ≤ (4 * H_max + 14) * (4 * H_max + 4) * (2 * (curG.inside X).length + 1) := by
    intro Y hY
    have hYin : Y ∈ Cited.partsOf G_twin label := Finset.mem_toList.mp hY
    exact decomposePartFull_spec hV hL hD hφ₀ hφ_le (hdecExp.2.1 Y hYin)
  have hrem_m : remG.m ≤ 2 ^ (i - 1) * curG.n := by
    set crossE := (curG.edges.filter fun e => decide (label.getD (2 * e.1) 0 ≠ label.getD (2 * e.2) 0)).length
    set crossTwin := (G_twin.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length
    have hcross_le : crossE ≤ crossTwin := by
      have h1 : crossE = ((curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).filter
          fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length := by
        simp [crossE, List.filter_map]
        rfl
      rw [h1]
      change ((curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).filter _).length ≤
        ((curG.edges.map (fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)) ++
          (List.range curG.n).flatMap (fun u => List.replicate D (2 * u, 2 * u + 1))).filter _).length
      rw [List.filter_append, List.length_append]
      exact Nat.le_add_right _ _
    have hrem_split : remG.m ≤ crossE +
        ((curG.edges.filter fun e =>
          decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e)).length := by
      suffices h : ∀ L : List (ℕ × ℕ),
          (L.filter fun e => !pred e).length ≤
          (L.filter fun e => decide (label.getD (2 * e.1) 0 ≠ label.getD (2 * e.2) 0)).length +
          (L.filter fun e => decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e).length by
        exact h curG.edges
      intro L
      induction L with
      | nil => simp
      | cons e es ih =>
        rw [List.filter_cons, List.filter_cons, List.filter_cons]
        cases hpe : pred e <;> cases hlbl : decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) <;>
          simp_all <;> omega
    have hin_parts :
        (curG.edges.filter fun e =>
          decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e).length ≤
        (parts.map fun Y =>
          (curG.inside (partX curG.n Y)).length -
            (curG.inside (decomposePartFull curG D φ_B1 Y).1).length).sum := by
      set Lsame := curG.edges.filter fun e =>
        decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e
      let cond : Finset ℕ → ℕ × ℕ → Bool := fun Y e =>
        let X := partX curG.n Y
        let R := (decomposePartFull curG D φ_B1 Y).1
        decide (e.1 ∈ X) && decide (e.2 ∈ X) && !(decide (e.1 ∈ R) && decide (e.2 ∈ R))
      have hLsame_any : Lsame = Lsame.filter (fun e => parts.any fun Y => cond Y e) := by
        refine (List.filter_eq_self.mpr ?_).symm
        intro e he
        have heLs : e ∈ curG.edges ∧ label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0 ∧ pred e = false := by
          simpa [Lsame] using he
        rcases hV e heLs.1 with ⟨he1, he2⟩
        let Y0 := G_twin.verts.filter fun z => label.getD z 0 = label.getD (2 * e.1) 0
        have h2e1_verts : 2 * e.1 ∈ G_twin.verts := Finset.mem_range.mpr (by change 2 * e.1 < 2 * curG.n; omega)
        have h2e2_verts : 2 * e.2 ∈ G_twin.verts := Finset.mem_range.mpr (by change 2 * e.2 < 2 * curG.n; omega)
        have hY0_mem : Y0 ∈ Cited.partsOf G_twin label := by
          unfold Cited.partsOf
          exact Finset.mem_image.mpr ⟨2 * e.1, h2e1_verts, rfl⟩
        have hY0_parts : Y0 ∈ parts := Finset.mem_toList.mpr hY0_mem
        have he1X : e.1 ∈ partX curG.n Y0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he1, Finset.mem_filter.mpr ⟨h2e1_verts, rfl⟩⟩
        have he2X : e.2 ∈ partX curG.n Y0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he2, Finset.mem_filter.mpr ⟨h2e2_verts, heLs.2.1.symm⟩⟩
        have he_not_R : !(decide (e.1 ∈ (decomposePartFull curG D φ_B1 Y0).1) &&
            decide (e.2 ∈ (decomposePartFull curG D φ_B1 Y0).1)) = true := by
          by_contra hf
          have hboth : e.1 ∈ (decomposePartFull curG D φ_B1 Y0).1 ∧
              e.2 ∈ (decomposePartFull curG D φ_B1 Y0).1 := by
            simpa using hf
          have hne_R : (decomposePartFull curG D φ_B1 Y0).1 ≠ ∅ :=
            Finset.ne_empty_of_mem hboth.1
          have h2le : 2 ≤ (decomposePartFull curG D φ_B1 Y0).1.card := by
            rcases (hpartSpec Y0 hY0_parts).2.1 with hem | ⟨hc, _, _⟩
            · exact False.elim (hne_R hem)
            · exact hc
          have hmem_valid : (decomposePartFull curG D φ_B1 Y0).1 ∈ validRs := by
            rw [List.mem_filter]
            exact ⟨List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨Y0, hY0_parts, rfl⟩, rfl⟩,
              decide_eq_true h2le⟩
          have hpred_true : pred e = true := List.any_eq_true.mpr ⟨_, hmem_valid, by simpa using hboth⟩
          rw [heLs.2.2] at hpred_true
          simp at hpred_true
        exact List.any_eq_true.mpr ⟨Y0, hY0_parts, by
          simp only [cond, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨he1X, he2X⟩, by simpa using he_not_R⟩⟩
      have hsub_len : ∀ Y ∈ parts, (Lsame.filter (cond Y)).length ≤
          (curG.inside (partX curG.n Y)).length -
            (curG.inside (decomposePartFull curG D φ_B1 Y).1).length := by
        intro Y hY
        set R_Y := (decomposePartFull curG D φ_B1 Y).1
        have hRX : R_Y ⊆ partX curG.n Y := (hpartSpec Y hY).1
        rw [← inside_partX_diff_len curG (partX curG.n Y) R_Y hRX]
        rw [show (Lsame.filter (cond Y)) =
            (curG.edges.filter fun e => decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) &&
              !pred e).filter (cond Y) from rfl]
        rw [List.filter_filter]
        unfold Cited.Graph.inside
        rw [List.filter_filter]
        induction curG.edges with
        | nil => simp
        | cons e es ih =>
          simp only [List.filter_cons]
          have hcond_eq : (!(decide (e.1 ∈ R_Y) && decide (e.2 ∈ R_Y)) &&
              (decide (e.1 ∈ partX curG.n Y) && decide (e.2 ∈ partX curG.n Y))) = cond Y e := by
            dsimp only [cond, R_Y]; exact Bool.and_comm _ _
          rw [hcond_eq]
          cases cond Y e
          · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact ih
          · cases decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e <;>
              simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                List.length_cons] <;>
              omega
      calc Lsame.length = (Lsame.filter fun e => parts.any fun Y => cond Y e).length := by
            conv_lhs => rw [hLsame_any]
        _ ≤ (parts.map fun Y => (Lsame.filter (cond Y)).length).sum :=
            sum_filter_any_le Lsame cond parts
        _ ≤ (parts.map fun Y => (curG.inside (partX curG.n Y)).length -
              (curG.inside (decomposePartFull curG D φ_B1 Y).1).length).sum :=
            List.sum_le_sum fun Y hY => hsub_len Y hY
    have hsum_drop : (parts.map fun Y =>
        (curG.inside (partX curG.n Y)).length -
          (curG.inside (decomposePartFull curG D φ_B1 Y).1).length).sum ≤
        15 * ∑ Y ∈ Cited.partsOf G_twin label, G_twin.cut Y := by
      have h1 : (parts.map fun Y =>
          (curG.inside (partX curG.n Y)).length -
            (curG.inside (decomposePartFull curG D φ_B1 Y).1).length).sum ≤
          (parts.map fun Y => 15 * G_twin.cut Y).sum :=
        List.sum_le_sum fun Y hY => (hpartSpec Y hY).2.2.1
      have h2 : (parts.map fun Y => 15 * G_twin.cut Y).sum =
          15 * ∑ Y ∈ Cited.partsOf G_twin label, G_twin.cut Y := by
        have hsum_cut_parts : (parts.map G_twin.cut).sum =
            ∑ Y ∈ Cited.partsOf G_twin label, G_twin.cut Y := by
          rw [Finset.sum_eq_multiset_sum]
          have hcoe : (Cited.partsOf G_twin label).val = ↑parts := (Finset.coe_toList _).symm
          rw [hcoe]
          simp [Multiset.map_coe, Multiset.sum_coe]
        rw [← hsum_cut_parts]
        clear h1 hpartSpec hsum_cut_parts
        induction parts with
        | nil => simp
        | cons Y ys ih => simp [ih]; ring
      omega
    have hsum_cut : ∑ Y ∈ Cited.partsOf G_twin label, G_twin.cut Y = 2 * crossTwin :=
      sum_cut_partsOf hTV label
    have hm_twin : G_twin.m ≤ 2 * D * curG.n := by
      change (twinGraph D curG).m ≤ 2 * D * curG.n
      rw [twinGraph_m, Nat.mul_assoc]
      omega
    have hrem_le_31 : remG.m ≤ 31 * crossTwin := by omega
    have hrem_R : (remG.m : ℝ) ≤ (2 ^ (i - 1) * curG.n : ℕ) := by
      have h1 : (remG.m : ℝ) ≤ 31 * (crossTwin : ℝ) := by exact_mod_cast hrem_le_31
      have h2 : (crossTwin : ℝ) ≤ (1 / 200 : ℝ) * (G_twin.m : ℝ) := hdecCut
      have h3 : (G_twin.m : ℝ) ≤ 2 * (D : ℝ) * (curG.n : ℝ) := by exact_mod_cast hm_twin
      have hD_eq : D = 2 * 2 ^ (i - 1) := by
        have : i = (i - 1) + 1 := by omega
        conv_lhs => rw [show D = 2 ^ i from rfl, this, pow_succ']
      have hD_R : (D : ℝ) = 2 * (2 : ℝ) ^ (i - 1) := by exact_mod_cast hD_eq
      rw [hD_R] at h3
      push_cast
      nlinarith
    exact_mod_cast hrem_R
  have hvalidRs_disj : validRs.Pairwise Disjoint := by
    have hpX : (parts.map (partX curG.n)).Pairwise Disjoint := pairwise_partX_disjoint curG.n hpwParts
    have hmap : resParts.map Prod.fst = parts.map fun Y => (decomposePartFull curG D φ_B1 Y).1 := by
      simp [resParts, List.map_map]
    change ((resParts.map Prod.fst).filter fun R => decide (2 ≤ R.card)).Pairwise Disjoint
    rw [hmap]
    exact pairwise_disjoint_filter_map (fun Y => (decomposePartFull curG D φ_B1 Y).1)
      (partX curG.n) (fun R => decide (2 ≤ R.card)) parts hpX fun Y hY => (hpartSpec Y hY).1
  have hvalidR_spec : ∀ R ∈ validRs,
      R ⊆ curG.verts ∧ 2 ≤ R.card ∧
      curG.IsConductanceExpanderOn R (φ_B1 / 3) ∧
      (∀ v ∈ R, (φ_B1 / 3) * (D : ℝ) ≤ (curG.degIn R v : ℝ)) ∧
      (∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) ∧
      Gi.inside R = curG.inside R ∧
      (∀ v ∈ R, Gi.deg v = curG.degIn R v) := by
    intro R hR
    have hRf := List.mem_filter.mp hR
    rcases List.mem_map.mp hRf.1 with ⟨⟨R', st'⟩, hr, rfl⟩
    rcases List.mem_map.mp hr with ⟨Y, hY, heq⟩
    have hsp := hpartSpec Y hY
    rw [heq] at hsp
    have h2le : 2 ≤ R'.card := decide_eq_true_eq.mp hRf.2
    have hne : R' ≠ ∅ := by intro hem; rw [hem] at h2le; simp at h2le
    rcases hsp.2.1 with hem | ⟨_, hexpR, hdegR⟩
    · exact False.elim (hne hem)
    · have hRverts : R' ⊆ curG.verts := fun v hv =>
        Finset.mem_range.mpr (Finset.mem_range.mp (Finset.mem_filter.mp (hsp.1 hv)).1)
      have hclosed : ∀ e ∈ Gi.edges, e.1 ∈ R' ↔ e.2 ∈ R' := by
        intro e he
        have he_f := (List.mem_filter.mp he).2
        rcases List.any_eq_true.mp he_f with ⟨R₂, hR₂, hmem₂⟩
        have hboth : e.1 ∈ R₂ ∧ e.2 ∈ R₂ := by simpa using hmem₂
        constructor
        · intro he1
          have heqR : R' = R₂ := mem_pairwise_disjoint_eq_of_mem_inter hvalidRs_disj hR hR₂ e.1 he1 hboth.1
          rw [heqR]; exact hboth.2
        · intro he2
          have heqR : R' = R₂ := mem_pairwise_disjoint_eq_of_mem_inter hvalidRs_disj hR hR₂ e.2 he2 hboth.2
          rw [heqR]; exact hboth.1
      have hinside_eq : Gi.inside R' = curG.inside R' := by
        unfold Cited.Graph.inside
        change (curG.edges.filter pred).filter (fun e => decide (e.1 ∈ R') && decide (e.2 ∈ R')) =
          curG.edges.filter fun e => decide (e.1 ∈ R') && decide (e.2 ∈ R')
        rw [List.filter_filter]
        congr 1
        ext e
        by_cases h1 : e.1 ∈ R' <;> by_cases h2 : e.2 ∈ R'
        · have hp : pred e = true := List.any_eq_true.mpr ⟨R', hR, by simp [h1, h2]⟩
          simp [h1, h2, hp]
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      have hdeg_eq : ∀ v ∈ R', Gi.deg v = curG.degIn R' v := by
        intro v hv
        unfold Cited.Graph.deg Cited.Graph.degIn
        rw [inside_verts_eq hGiV]
        have hf1 : (Gi.edges.filter fun e => decide (e.1 = v)) =
            ((Gi.inside R').filter fun e => decide (e.1 = v)) := by
          have hinsR : Gi.inside R' = Gi.edges.filter fun e => decide (e.1 ∈ R') && decide (e.2 ∈ R') := rfl
          rw [hinsR]
          conv_rhs => rw [List.filter_filter]
          suffices h : ∀ (L : List (ℕ × ℕ)), (∀ e ∈ L, e.1 ∈ R' ↔ e.2 ∈ R') →
              L.filter (fun e => decide (e.1 = v)) =
                L.filter (fun e => decide (e.1 = v) && (decide (e.1 ∈ R') && decide (e.2 ∈ R'))) from
            h Gi.edges hclosed
          intro L hL
          induction L with
          | nil => simp
          | cons e es ih =>
            have he := hL e List.mem_cons_self
            have ih' := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
            by_cases hev : e.1 = v
            · have h2 : e.2 ∈ R' := he.mp (hev ▸ hv)
              simp [hev, hv, h2, ih']
            · simp [hev, ih']
        have hf2 : (Gi.edges.filter fun e => decide (e.2 = v)) =
            ((Gi.inside R').filter fun e => decide (e.2 = v)) := by
          have hinsR : Gi.inside R' = Gi.edges.filter fun e => decide (e.1 ∈ R') && decide (e.2 ∈ R') := rfl
          rw [hinsR]
          conv_rhs => rw [List.filter_filter]
          suffices h : ∀ (L : List (ℕ × ℕ)), (∀ e ∈ L, e.1 ∈ R' ↔ e.2 ∈ R') →
              L.filter (fun e => decide (e.2 = v)) =
                L.filter (fun e => decide (e.2 = v) && (decide (e.1 ∈ R') && decide (e.2 ∈ R'))) from
            h Gi.edges hclosed
          intro L hL
          induction L with
          | nil => simp
          | cons e es ih =>
            have he := hL e List.mem_cons_self
            have ih' := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
            by_cases hev : e.2 = v
            · have h1 : e.1 ∈ R' := he.mpr (hev ▸ hv)
              simp [hev, hv, h1, ih']
            · simp [hev, ih']
        rw [hf1, hf2, hinside_eq]
      exact ⟨hRverts, h2le, hexpR, hdegR, hclosed, hinside_eq, hdeg_eq⟩
  have hcomps : ∀ X ∈ Cited.partsOf Gi (compLabels Gi), 2 ≤ X.card →
      Gi.IsConductanceExpanderOn X (φ_B1 / 3) ∧
      ∀ x ∈ X, (φ_B1 / 3) * (D : ℝ) ≤ (Gi.deg x : ℝ) := by
    intro X hX hXcard
    have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    rcases hXne with ⟨u, huX⟩
    have hu_verts : u ∈ Gi.verts := by
      have hb := partsOf_biUnion Gi (compLabels Gi)
      rw [← hb]
      exact Finset.mem_biUnion.mpr ⟨X, hX, huX⟩
    have hXu_ne : {u} ≠ X := by
      intro hEq
      have : ({u} : Finset ℕ).card = X.card := congrArg Finset.card hEq
      simp at this
      omega
    have hcut1 := cutIn_ge_one_of_part_compLabels hGiV hX (Finset.singleton_subset_iff.mpr huX)
      (Finset.singleton_nonempty u) hXu_ne
    have hex_edge : ∃ e ∈ Gi.inside X, e.1 = u ∨ e.2 = u := by
      unfold Cited.Graph.cutIn at hcut1
      have hpos : 0 < (List.filter (fun e => decide (e.1 ∈ ({u} : Finset ℕ)) != decide (e.2 ∈ ({u} : Finset ℕ))) (Gi.inside X)).length := by
        omega
      rcases List.length_pos_iff_exists_mem.mp hpos with ⟨e, he⟩
      rw [List.mem_filter] at he
      refine ⟨e, he.1, ?_⟩
      by_cases h1 : e.1 = u <;> by_cases h2 : e.2 = u <;> simp_all
    rcases hex_edge with ⟨e, heIn, heEnd⟩
    have heGi : e ∈ Gi.edges := (mem_inside_iff.mp heIn).1
    have hePred : pred e = true := (List.mem_filter.mp heGi).2
    rcases List.any_eq_true.mp hePred with ⟨R, hR, heR⟩
    have heR' : e.1 ∈ R ∧ e.2 ∈ R := by simpa using heR
    have huR : u ∈ R := by
      rcases heEnd with rfl | rfl
      · exact heR'.1
      · exact heR'.2
    rcases hvalidR_spec R hR with ⟨hRverts, hRcard, hexpR, hdegR, hclosed, hinside_eq, hdeg_eq⟩
    have hXR_eq : X = R := by
      apply Finset.Subset.antisymm
      · intro y hyX
        have hy_verts : y ∈ Gi.verts := by
          rw [← partsOf_biUnion Gi (compLabels Gi)]
          exact Finset.mem_biUnion.mpr ⟨X, hX, hyX⟩
        have hlbl : (compLabels Gi).getD u 0 = (compLabels Gi).getD y 0 := by
          unfold Cited.partsOf at hX
          rcases Finset.mem_image.mp hX with ⟨w, _, rfl⟩
          have huw := (Finset.mem_filter.mp huX).2
          have hyw := (Finset.mem_filter.mp hyX).2
          exact huw.trans hyw.symm
        rcases (compLabels_eq_iff_reachable hGiV (Finset.mem_range.mp hu_verts)
          (Finset.mem_range.mp hy_verts)).mp hlbl with ⟨P, hP⟩
        exact reachable_stay_in_set hclosed hP huR
      · intro z hzR
        set S := R ∩ X
        have hSR : S ⊆ R := Finset.inter_subset_left
        have hSne : S.Nonempty := ⟨u, Finset.mem_inter.mpr ⟨huR, huX⟩⟩
        have hcut_zero : Gi.cutIn R S = 0 := by
          have hcutX0 := cut_part_compLabels_eq_zero hGiV hX
          by_contra hnz
          have hpos : 0 < Gi.cutIn R S := Nat.pos_of_ne_zero hnz
          unfold Cited.Graph.cutIn at hpos
          rcases List.length_pos_iff_exists_mem.mp hpos with ⟨e', he'⟩
          rw [List.mem_filter] at he'
          have he'R := he'.1
          rw [mem_inside_iff] at he'R
          have he'Gi : e' ∈ Gi.edges := (mem_inside_iff.mp he'.1).1
          have he'V : e' ∈ Gi.inside Gi.verts := by rw [inside_verts_eq hGiV]; exact he'Gi
          have hcross : (decide (e'.1 ∈ X) != decide (e'.2 ∈ X)) = true := by
            have hd : (decide (e'.1 ∈ S) != decide (e'.2 ∈ S)) = true := he'.2
            have he1R := he'R.1
            have he2R := he'R.2
            by_cases h1X : e'.1 ∈ X <;> by_cases h2X : e'.2 ∈ X <;>
              simp_all [S]
          have hcpos : 0 < Gi.cut X := by
            unfold Cited.Graph.cut Cited.Graph.cutIn
            exact List.length_pos_iff_exists_mem.mpr ⟨e', List.mem_filter.mpr ⟨he'V, hcross⟩⟩
          omega
        have hSeq : S = R := by
          by_contra hSneR
          have hexpGi : Gi.IsConductanceExpanderOn R (φ_B1 / 3) := by
            intro T hTR hTne hTneR
            have hT := hexpR T hTR hTne hTneR
            have hv1 : Gi.volIn R T = curG.volIn R T := by
              unfold Cited.Graph.volIn Cited.Graph.degIn
              rw [hinside_eq]
            have hv2 : Gi.volIn R (R \ T) = curG.volIn R (R \ T) := by
              unfold Cited.Graph.volIn Cited.Graph.degIn
              rw [hinside_eq]
            have hc : Gi.cutIn R T = curG.cutIn R T := by
              unfold Cited.Graph.cutIn
              rw [hinside_eq]
            rw [hv1, hv2, hc]
            exact hT
          have he := hexpGi S hSR hSne hSneR
          rw [hcut_zero, Nat.cast_zero] at he
          have hmin0 : min (↑(Gi.volIn R S) : ℝ) (↑(Gi.volIn R (R \ S)) : ℝ) ≤ 0 := by
            by_contra hpos
            push Not at hpos
            have hmul : 0 < (φ_B1 / 3) * min (↑(Gi.volIn R S) : ℝ) (↑(Gi.volIn R (R \ S)) : ℝ) :=
              mul_pos (by linarith) hpos
            linarith
          have hvol0 : Gi.volIn R S = 0 ∨ Gi.volIn R (R \ S) = 0 := by
            rcases min_cases (↑(Gi.volIn R S) : ℝ) (↑(Gi.volIn R (R \ S)) : ℝ) with ⟨h1, _⟩ | ⟨h2, _⟩
            · left; rw [h1] at hmin0; exact Nat.eq_zero_of_le_zero (by exact_mod_cast hmin0)
            · right; rw [h2] at hmin0; exact Nat.eq_zero_of_le_zero (by exact_mod_cast hmin0)
          have exists_zero_deg : ∃ w ∈ R, Gi.degIn R w = 0 := by
            rcases hvol0 with hvs | hvr
            · rcases hSne with ⟨w, hwS⟩
              have hsum0 : ∑ v ∈ S, Gi.degIn R v = 0 := hvs
              rw [Finset.sum_eq_zero_iff] at hsum0
              exact ⟨w, hSR hwS, hsum0 w hwS⟩
            · have hdiff_ne : (R \ S).Nonempty := by
                by_contra hem
                rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hem
                exact hSneR (Finset.Subset.antisymm hSR hem)
              rcases hdiff_ne with ⟨w, hwR⟩
              have hsum0 : ∑ v ∈ R \ S, Gi.degIn R v = 0 := hvr
              rw [Finset.sum_eq_zero_iff] at hsum0
              exact ⟨w, (Finset.mem_sdiff.mp hwR).1, hsum0 w hwR⟩
          rcases exists_zero_deg with ⟨w, hwR, hdw0⟩
          have hwdeg : Gi.degIn R w = curG.degIn R w := by
            unfold Cited.Graph.degIn; rw [hinside_eq]
          have hposD : (0 : ℝ) < (φ_B1 / 3) * (D : ℝ) := mul_pos (by linarith) (by exact_mod_cast hD)
          have hleD := hdegR w hwR
          rw [← hwdeg, hdw0] at hleD
          simp at hleD
          linarith
        exact (Finset.mem_inter.mp (hSeq ▸ hzR)).2
    rw [hXR_eq]
    refine ⟨?_, fun x hx => ?_⟩
    · intro T hTR hTne hTneR
      have hT := hexpR T hTR hTne hTneR
      have hv1 : Gi.volIn R T = curG.volIn R T := by unfold Cited.Graph.volIn Cited.Graph.degIn; rw [hinside_eq]
      have hv2 : Gi.volIn R (R \ T) = curG.volIn R (R \ T) := by unfold Cited.Graph.volIn Cited.Graph.degIn; rw [hinside_eq]
      have hc : Gi.cutIn R T = curG.cutIn R T := by unfold Cited.Graph.cutIn; rw [hinside_eq]
      rw [hv1, hv2, hc]; exact hT
    · rw [hdeg_eq x hx]; exact hdegR x hx
  have hsteps_bound : (resParts.map Prod.snd).sum ≤
      (4 * H_max + 14) * (4 * H_max + 4) * (2 * curG.m + curG.n) := by
    set C := (4 * H_max + 14) * (4 * H_max + 4)
    have hmap_snd : resParts.map Prod.snd = parts.map fun Y => (decomposePartFull curG D φ_B1 Y).2 := by
      simp [resParts, List.map_map]
    rw [hmap_snd]
    set bigParts := parts.filter fun Y => decide (2 ≤ (partX curG.n Y).card)
    have hfzero : (parts.map fun Y => (decomposePartFull curG D φ_B1 Y).2).sum =
        (bigParts.map fun Y => (decomposePartFull curG D φ_B1 Y).2).sum := by
      apply list_sum_map_filter_zero
      intro Y hY hf
      have h1 : (partX curG.n Y).card ≤ 1 := by
        have : ¬ (2 ≤ (partX curG.n Y).card) := by simpa using hf
        omega
      exact (hpartSpec Y hY).2.2.2.1 h1
    rw [hfzero]
    have hmul := list_sum_map_le_const_mul (fun Y => (decomposePartFull curG D φ_B1 Y).2)
      (fun Y => 2 * (curG.inside (partX curG.n Y)).length + 1) C bigParts fun Y hY =>
      (hpartSpec Y (List.mem_filter.mp hY).1).2.2.2.2
    have hsum_big : (bigParts.map fun Y => 2 * (curG.inside (partX curG.n Y)).length + 1).sum =
        2 * (bigParts.map fun Y => (curG.inside (partX curG.n Y)).length).sum + bigParts.length := by
      clear hmul hpartSpec hfzero hmap_snd hcomps hvalidR_spec hvalidRs_disj hrem_m
      induction bigParts with
      | nil => simp
      | cons y ys ih => simp [ih]; ring
    have hbp_pw : bigParts.Pairwise Disjoint := hpwParts.filter _
    have hpX_bp : (bigParts.map (partX curG.n)).Pairwise Disjoint :=
      pairwise_partX_disjoint curG.n hbp_pw
    have hinside_sum : (bigParts.map fun Y => (curG.inside (partX curG.n Y)).length).sum ≤ curG.m := by
      have hm_eq : (bigParts.map fun Y => (curG.inside (partX curG.n Y)).length) =
          ((bigParts.map (partX curG.n)).map fun X =>
            (curG.edges.filter fun e => decide (e.1 ∈ X) && decide (e.2 ∈ X)).length) := by
        simp [Cited.Graph.inside, List.map_map]
      rw [hm_eq]
      exact list_filter_disjoint_edges_le (bigParts.map (partX curG.n)) curG.edges hpX_bp
    have hlen_le_n : bigParts.length ≤ curG.n := by
      have hmem_bp : ∀ Y ∈ bigParts, 1 ≤ (partX curG.n Y).card := fun Y hY =>
        le_trans (by omega) (decide_eq_true_eq.mp (List.mem_filter.mp hY).2)
      have hcard_sum : bigParts.length ≤ (bigParts.map fun Y => (partX curG.n Y).card).sum := by
        suffices h : ∀ (L : List (Finset ℕ)), (∀ Y ∈ L, 1 ≤ (partX curG.n Y).card) →
            L.length ≤ (L.map fun Y => (partX curG.n Y).card).sum from h bigParts hmem_bp
        intro L hL
        induction L with
        | nil => simp
        | cons y ys ih =>
          have hy := hL y List.mem_cons_self
          have ih' := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          omega
      have hcard_n := sum_card_pairwiseDisjoint (bigParts.map (partX curG.n)) (Finset.range curG.n)
        hpX_bp (fun X hX => by
          rcases List.mem_map.mp hX with ⟨Y, _, rfl⟩
          exact Finset.filter_subset _ _)
      simp only [List.map_map, Finset.card_range] at hcard_n
      exact le_trans hcard_sum (by simpa [Function.comp_def] using hcard_n)
    calc (bigParts.map fun Y => (decomposePartFull curG D φ_B1 Y).2).sum
        ≤ C * (bigParts.map fun Y => 2 * (curG.inside (partX curG.n Y)).length + 1).sum := hmul
      _ ≤ C * (2 * curG.m + curG.n) := by
          rw [hsum_big]; exact Nat.mul_le_mul_left C (by omega)
  have hcomps' : ∀ X ∈ Cited.partsOf Gi (compLabels Gi), 2 ≤ X.card →
      Gi.IsConductanceExpanderOn X (φ_B1 / 3) ∧
      ∀ x ∈ X, (φ_B1 / 3) * (2 : ℝ) ^ i ≤ (Gi.deg x : ℝ) := by
    intro X hX hXc
    have h := hcomps X hX hXc
    exact ⟨h.1, fun x hx => by simpa [D] using h.2 x hx⟩
  have hvalidRs_props :
      Gi.edges = curG.edges.filter (decomposeLevelPred decomp φ_B1 curG i) ∧
      remG.edges = curG.edges.filter (fun e => !decomposeLevelPred decomp φ_B1 curG i e) ∧
      (decomposeLevelComps decomp φ_B1 curG i).Pairwise Disjoint ∧
      (∀ R ∈ decomposeLevelComps decomp φ_B1 curG i,
        R ⊆ curG.verts ∧ 2 ≤ R.card ∧
        Gi.IsConductanceExpanderOn R (φ_B1 / 3) ∧
        (∀ x ∈ R, (φ_B1 / 3) * (2 : ℝ) ^ i ≤ (Gi.degIn R x : ℝ)) ∧
        (∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
      ∀ e ∈ Gi.edges, ∃ R ∈ decomposeLevelComps decomp φ_B1 curG i, e.1 ∈ R ∧ e.2 ∈ R := by
    refine ⟨rfl, rfl, hvalidRs_disj, fun R hR => ?_, fun e he => ?_⟩
    · rcases hvalidR_spec R hR with ⟨hRv, hRc, hRexp, hRdeg, hRcl, hRins, _⟩
      refine ⟨hRv, hRc, ?_, fun x hx => ?_, hRcl⟩
      · intro T hTR hTne hTneR
        have hT := hRexp T hTR hTne hTneR
        have hv1 : Gi.volIn R T = curG.volIn R T := by unfold Cited.Graph.volIn Cited.Graph.degIn; rw [hRins]
        have hv2 : Gi.volIn R (R \ T) = curG.volIn R (R \ T) := by unfold Cited.Graph.volIn Cited.Graph.degIn; rw [hRins]
        have hc : Gi.cutIn R T = curG.cutIn R T := by unfold Cited.Graph.cutIn; rw [hRins]
        rw [hv1, hv2, hc]; exact hT
      · have hd : Gi.degIn R x = curG.degIn R x := by unfold Cited.Graph.degIn; rw [hRins]
        rw [hd]
        simpa [D] using hRdeg x hx
    · have hpred : pred e = true := (List.mem_filter.mp he).2
      rcases List.any_eq_true.mp hpred with ⟨R, hR, heR⟩
      exact ⟨R, hR, by simpa using heR⟩
  exact ⟨rfl, rfl, hGiV, hGiL, hremV, hremL, hperm, hGi_m, hrem_m, hcomps', hsteps_bound, hvalidRs_props⟩

end

end MinCostFlow.Expander


