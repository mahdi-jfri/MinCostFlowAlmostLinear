module

public import MinCostFlow.DynSpanner.Tools
public import MinCostFlow.DynSpanner.Walks
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Sort

import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Definitions and algorithm model for the dynamic spanner (Section 8, Theorem 8.2)

This file formalizes the data structures and algorithm from [chen2022maximum] (arXiv:2203.00671v2),
Section 5.1 (lines 24–108), adapted to the deterministic static sparsifier of Theorem 8.1
(`arXiv:2309.16629v1`, page 39):

* **Definition 5.2** (`Touches`, `touchedVertices`, [chen2022maximum] Section 5.1): vertices
  touched by an edge deletion or vertex split.
* **Definition 5.4** (`prefixWalk`, `proj`, `projWalk`, `reembedWalk`, [chen2022maximum]
  Section 5.1): edge-embedding projection onto the touched vertex set `S_{j-1}`, handling both
  deletions and vertex splits via `prefixWalk`.
* **Initialization** (`init`, `initCore`): replaces [chen2022maximum, Theorem 5.3] with
  Theorem 8.1 (`Sparsify(G_act, G_act, idEmb)` on the non-isolated subgraph `G_act` of `G`).
* **Algorithm 6** (`DynSpannerState`, `step`, `update`): maintains levels `0, ..., L` with
  graphs `H_0, ..., H_L`, embeddings `Π_0, ..., Π_L`, domains `inDom`, touched sets `S_0, ..., S_L`,
  union spanner `H`, recourse batches `U_H`, re-embedded sets `D`, and operation counts.

Faithful reading notes:
* To handle non-integer `n^{1 - j/L}`, phase lengths form the integer divisibility chain
  `B_j = q^{L - j}` with `q = phaseBase nCap L = max 2 ⌈nCap^{1/L}⌉`, so `B_L = 1`, `B_{j-1} = q · B_j`,
  and `B_0 = q^L ≥ nCap`. Whenever `t` is divisible by `B_0`, level `0` performs a full restart.
* Storing `q` explicitly in `DynSpannerState` keeps `init`, `step`, and `update` computable.
-/

namespace MinCostFlow.DynSpanner

@[expose] public section

/-- **Definition 5.2** ([chen2022maximum] arXiv:2203.00671v2, Section 5.1):
an update `u` to `G` *touches* vertex `v` if `u` is a deletion of an edge with endpoint `v`, or a
vertex split producing `v` (either the split vertex or the new vertex). -/
def Touches (G : MGraph) (u : Update) (v : ℕ) : Prop :=
  match u with
  | .delete e => v = G.tail e ∨ v = G.head e
  | .split v₁ v₂ _ _ => v = v₁ ∨ v = v₂
  | .insert _ _ _ => False

/-- Finite set of vertices touched by an update `u` on `G` (Definition 5.2). -/
def touchedVertices (G : MGraph) (u : Update) : Finset ℕ :=
  match u with
  | .delete e => {G.tail e, G.head e}
  | .split v₁ v₂ _ _ => {v₁, v₂}
  | .insert _ _ _ => ∅

theorem mem_touchedVertices_iff (G : MGraph) (u : Update) (v : ℕ) :
    v ∈ touchedVertices G u ↔ Touches G u v := by
  cases u <;> simp [touchedVertices, Touches]

theorem card_touchedVertices_le_two (G : MGraph) (u : Update) :
    (touchedVertices G u).card ≤ 2 := by
  cases u with
  | insert _ _ _ => simp [touchedVertices]
  | delete e =>
    simpa [touchedVertices] using Finset.card_insert_le (G.tail e) {G.head e}
  | split v₁ v₂ _ _ =>
    simpa [touchedVertices] using Finset.card_insert_le v₁ {v₂}

/-- Walk along `w` in `H` starting from `a` until reaching the first vertex in `S` (or the end
of `w`), returning `(endpoint, prefix)`. Used for **Definition 5.4** ([chen2022maximum]
arXiv:2203.00671v2, Section 5.1). -/
def prefixWalk (H : MGraph) (a : ℕ) (w : List (ℕ × Bool)) (S : Finset ℕ) :
    ℕ × List (ℕ × Bool) :=
  if a ∈ S then (a, [])
  else match w with
  | [] => (a, [])
  | x :: w' =>
    let res := prefixWalk H (H.dst x) w' S
    (res.1, x :: res.2)

/-- **Definition 5.4** (Edge-embedding projection, [chen2022maximum] arXiv:2203.00671v2,
Section 5.1): endpoints `(â, b̂)` of the projected edge `proj_{j-1}(e)`, defined as the closest
vertices in `S` to `G.tail e` and `G.head e` along the walk `embLt e` in `H`. -/
def proj (G H : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) : ℕ × ℕ :=
  ((prefixWalk H (G.tail e) (embLt e) S).1,
   (prefixWalk H (G.head e) (walkRev (embLt e)) S).1)

/-- The embedding walk `Π_{J → H_{<j} ∪ E_affected}(ê) = Π_{<j}(e)[â, a] ⊕ e ⊕ Π_{<j}(e)[b, b̂]`
constructed in Algorithm 6, line 76 ([chen2022maximum] arXiv:2203.00671v2, Section 5.1). -/
def projWalk (G H : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) : List (ℕ × Bool) :=
  walkRev (prefixWalk H (G.tail e) (embLt e) S).2 ++ [(e, true)] ++
    (prefixWalk H (G.head e) (walkRev (embLt e)) S).2

/-- Re-embedded walk `Π_j(e) = Π_{<j}(e)[a, â] ⊕ mid(ê) ⊕ Π_{<j}(e)[b̂, b]` constructed in
Algorithm 6, line 85 ([chen2022maximum] arXiv:2203.00671v2, Section 5.1). -/
def reembedWalk (G H : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (e : ℕ) :
    List (ℕ × Bool) :=
  (prefixWalk H (G.tail e) (embLt e) S).2 ++ embMid e ++
    walkRev (prefixWalk H (G.head e) (walkRev (embLt e)) S).2

/-- Integer branching factor `q = max 2 ⌈(max nCap 1)^{1/L}⌉` replacing `n^{1/L}` so that
phase periods `q^{L - j}` form an integer divisibility chain. -/
noncomputable def phaseBase (nCap L : ℕ) : ℕ :=
  max 2 (Nat.ceil (((max nCap 1 : ℕ) : ℝ) ^ (1 / (max L 1 : ℝ))))

theorem two_le_phaseBase (nCap L : ℕ) : 2 ≤ phaseBase nCap L :=
  le_max_left _ _

theorem nCap_le_phaseBase_pow (nCap L : ℕ) (hL : 1 ≤ L) :
    max nCap 1 ≤ (phaseBase nCap L) ^ L := by
  have h1 : (1 : ℝ) ≤ ((max nCap 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right nCap 1
  have hL_eq : max (L : ℝ) 1 = (L : ℝ) := max_eq_left (by exact_mod_cast hL)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hceil : (((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) ≤ (phaseBase nCap L : ℝ) := by
    unfold phaseBase
    rw [hL_eq]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_max_right 2 _))
  have hrpow : ((max nCap 1 : ℕ) : ℝ) ≤ (phaseBase nCap L : ℝ) ^ L := by
    have hpow := Real.rpow_le_rpow (by positivity) hceil (Nat.cast_nonneg L)
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hLpos),
      Real.rpow_one, Real.rpow_natCast] at hpow
    exact hpow
  exact_mod_cast hrpow

theorem phaseBase_le (nCap L : ℕ) (hL : 1 ≤ L) :
    (phaseBase nCap L : ℝ) ≤ 2 * ((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by
  have h1 : (1 : ℝ) ≤ ((max nCap 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right nCap 1
  have hL_eq : max (L : ℝ) 1 = (L : ℝ) := max_eq_left (by exact_mod_cast hL)
  have hrpow1 : (1 : ℝ) ≤ ((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) :=
    Real.one_le_rpow h1 (by positivity)
  unfold phaseBase
  rw [hL_eq]
  have hceil : (Nat.ceil (((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) : ℝ) <
      ((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (2 : ℝ) ≤ 2 * ((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by linarith
  have hc : (Nat.ceil (((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) : ℝ) ≤
      2 * ((max nCap 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by linarith
  rw [Nat.cast_max]
  exact max_le (by simpa using h2) (by simpa using hc)

/-- Phase period `B_j = q^{L - j}` at level `j`. -/
def phasePeriod (q L j : ℕ) : ℕ :=
  q ^ (L - j)

/-- Level `j = min { j' ≤ L | q^{L - j'} ∣ t }` selected in Algorithm 6, line 66
([chen2022maximum] arXiv:2203.00671v2, Section 5.1). -/
def chooseLevel (L q t : ℕ) : ℕ :=
  ((List.range (L + 1)).find? fun j' => decide (phasePeriod q L j' ∣ t)).getD L

theorem chooseLevel_le (L q t : ℕ) : chooseLevel L q t ≤ L := by
  unfold chooseLevel
  cases h : (List.range (L + 1)).find? (fun j' => decide (phasePeriod q L j' ∣ t)) with
  | none => simp
  | some j =>
    have hmem : j ∈ List.range (L + 1) := List.mem_of_find?_eq_some h
    rw [List.mem_range] at hmem
    simp [Nat.le_of_lt_succ hmem]

theorem chooseLevel_dvd (L q t : ℕ) : phasePeriod q L (chooseLevel L q t) ∣ t := by
  unfold chooseLevel
  cases h : (List.range (L + 1)).find? (fun j' => decide (phasePeriod q L j' ∣ t)) with
  | none =>
    simp [phasePeriod]
  | some j =>
    have hp := List.find?_some h
    simpa [decide_eq_true_eq] using hp

theorem not_dvd_of_lt_chooseLevel {L q t j' : ℕ} (hj : j' < chooseLevel L q t) :
    ¬ (phasePeriod q L j' ∣ t) := by
  have hjle : j' < L + 1 := Nat.lt_of_lt_of_le hj (Nat.le_succ_of_le (chooseLevel_le L q t))
  have hmem : j' ∈ List.range (L + 1) := List.mem_range.mpr hjle
  unfold chooseLevel at hj
  cases h : (List.range (L + 1)).find? (fun k => decide (phasePeriod q L k ∣ t)) with
  | none =>
    have hnone := List.find?_eq_none.mp h j' hmem
    simpa [decide_eq_true_eq] using hnone
  | some j =>
    simp only [h, Option.getD_some] at hj
    obtain ⟨_, idx, hidx, hget, hprev⟩ := List.find?_eq_some_iff_getElem.mp h
    rw [List.length_range] at hidx
    rw [List.getElem_range] at hget
    subst hget
    have hlt : j' < idx := hj
    have hfalse := hprev j' hlt
    rw [List.getElem_range] at hfalse
    simpa [decide_eq_true_eq] using hfalse

/-- State of the dynamic spanner algorithm (Algorithm 6, [chen2022maximum] arXiv:2203.00671v2,
Section 5.1) with `L + 1` levels `0, ..., L`. -/
structure DynSpannerState (L : ℕ) where
  /-- Phase period base `q ≥ 2`. -/
  q : ℕ
  /-- Number of single updates processed so far. -/
  t : ℕ
  /-- Current dynamic graph `G^{(t)}`. -/
  G : MGraph
  /-- Level spanner subgraphs `H_0, ..., H_L`. -/
  H_level : Fin (L + 1) → MGraph
  /-- Level embeddings `Π_0, ..., Π_L`. -/
  Pi_level : Fin (L + 1) → Embedding
  /-- Pre-images (domains) of `Π_0, ..., Π_L`. -/
  inDom : Fin (L + 1) → Finset ℕ
  /-- Touched vertex sets `S_0, ..., S_L` since each level's last recomputation. -/
  S_level : Fin (L + 1) → Finset ℕ
  /-- Union spanner `H = ⋃_{i=0}^L H_i`. -/
  H : MGraph

/-- Output of initializing `DynSpannerState`. -/
structure InitOut (L : ℕ) where
  state : DynSpannerState L
  cost : ℕ

/-- Output of one step or batch update on `DynSpannerState`. -/
structure StepOut (L : ℕ) where
  state : DynSpannerState L
  UH : List Update
  D : Finset ℕ
  cost : ℕ

/-- Largest index `i < min j (L + 1)` with `e ∈ inDom i` (defaulting to `0`). -/
def findEmbLevel {L : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (j e : ℕ) : ℕ :=
  ((List.range (min j (L + 1))).reverse.find? fun i =>
    if h : i < L + 1 then decide (e ∈ inDom ⟨i, h⟩) else false).getD 0

/-- Combined embedding `Π_{<j}` mapping each edge via the largest `i < j` having it in its
domain ([chen2022maximum] Section 5.1, line 28). -/
def piLtFrom {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) (j : ℕ) : Embedding :=
  fun e =>
    let i := findEmbLevel inDom j e
    if h : i < L + 1 then Pi_level ⟨i, h⟩ e else []

/-- Combined embedding `Π_{<j}` of a state. -/
def piLt {L : ℕ} (st : DynSpannerState L) (j : ℕ) : Embedding :=
  piLtFrom st.Pi_level st.inDom j

/-- Combined embedding `Π_{≤ j}` of a state. -/
def piLe {L : ℕ} (st : DynSpannerState L) (j : ℕ) : Embedding :=
  piLt st (j + 1)

/-- The maintained embedding `Π_{G → H} = Π_{≤ L}`. -/
def piTotal {L : ℕ} (st : DynSpannerState L) : Embedding :=
  piLe st L

/-- Union of edge sets of levels `i < j`. -/
def unionEdgesLt {L : ℕ} (H_level : Fin (L + 1) → MGraph) (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin (L + 1) => i.1 < j).biUnion fun i => (H_level i).E

/-- Union graph `H_{<j} = ⋃_{i < j} H_i` on `G.V`. -/
def unionGraphLt {L : ℕ} (G : MGraph) (H_level : Fin (L + 1) → MGraph) (j : ℕ) : MGraph :=
  { V := G.V
    E := unionEdgesLt H_level j
    tail := G.tail
    head := G.head }

/-- Empty subgraph on `G.V` with `G`'s endpoint maps. -/
def emptyGraphOn (G : MGraph) : MGraph :=
  { V := G.V, E := ∅, tail := G.tail, head := G.head }

/-- Core initialization on a graph `G` using `Sparsify(G_act, G_act, idEmb)` (Theorem 8.1) on the
non-isolated subgraph `G_act`, returning `(H₀, Π₀, cost)`. -/
def initCore (G : MGraph) (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    MGraph × Embedding × ℕ :=
  if _hE : G.E.Nonempty then
    let Gact := activeSubgraph G
    let out := sparsify Gact Gact idEmb
    let H₀ : MGraph := { V := G.V, E := out.Jtilde.E, tail := G.tail, head := G.head }
    let pi₀ : Embedding := fun e => shortcutWalk G (G.tail e) (out.emb e)
    let walkCost := ∑ e ∈ G.E, (out.emb e).length
    (H₀, pi₀, out.cost + G.n + G.m + out.Jtilde.E.card + walkCost)
  else
    (emptyGraphOn G, idEmb, G.n)

/-- Initialize the dynamic spanner state on `G₀` at timestamp `t` (with `t = 0` at start, or
`t > 0` during a restart). -/
def initAt (G₀ : MGraph) (L q t : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : InitOut L :=
  let core := initCore G₀ sparsify
  let H₀ := core.1
  let Pi₀ := core.2.1
  let c := core.2.2
  { state :=
      { q := q
        t := t
        G := G₀
        H_level := fun i => if i.1 = 0 then H₀ else emptyGraphOn G₀
        Pi_level := fun i => if i.1 = 0 then Pi₀ else fun _ => []
        inDom := fun i => if i.1 = 0 then G₀.E else ∅
        S_level := fun _ => ∅
        H := H₀ }
    cost := c + L + 1 }

/-- Initialize the dynamic spanner algorithm on `G₀` with `L` levels and phase base `q`. -/
def init (G₀ : MGraph) (L q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : InitOut L :=
  initAt G₀ L q 0 sparsify

/-- Edges of `G'` affected relative to `H_lt`, `piLt_mid`, and `S_prev`
(Algorithm 6, line 71). -/
def affectedEdges (G' H_lt : MGraph) (piLt_mid : Embedding) (S_prev : Finset ℕ) : Finset ℕ :=
  G'.E.filter fun e => decide (∃ z ∈ H_lt.walkVertices (G'.tail e) (piLt_mid e), z ∈ S_prev)

/-- Auxiliary projected multigraph `J` over `S_{j-1}` built in Algorithm 6, lines 70–77. -/
def buildProjGraph (G' H_lt : MGraph) (piLt_mid : Embedding) (S_prev : Finset ℕ)
    (E_aff : Finset ℕ) : MGraph :=
  { V := E_aff.biUnion fun e =>
      {(proj G' H_lt piLt_mid S_prev e).1, (proj G' H_lt piLt_mid S_prev e).2}
    E := E_aff
    tail := fun e => (proj G' H_lt piLt_mid S_prev e).1
    head := fun e => (proj G' H_lt piLt_mid S_prev e).2 }

/-- Auxiliary host graph `H_{<j} ∪ E_affected` on `G'.V` in Algorithm 6, line 79. -/
def buildAuxHost (G' H_lt : MGraph) (E_aff : Finset ℕ) : MGraph :=
  { V := G'.V, E := H_lt.E ∪ E_aff, tail := G'.tail, head := G'.head }

/-- Single-update step of **Algorithm 6** (`Update(t)`, [chen2022maximum] arXiv:2203.00671v2,
Section 5.1) adapted to Theorem 8.1 (`Sparsify`). When `q^L ∣ (t + 1)` (`j = 0`), a full restart
re-initializes level `0` and resets levels `> 0`. -/
def step {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : StepOut L :=
  let G' := st.G.applyUpdate u
  let touched := touchedVertices st.G u
  let H_mid : Fin (L + 1) → MGraph := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
  let S_mid : Fin (L + 1) → Finset ℕ := fun i => st.S_level i ∪ touched
  let uhPref := restrictUpdate u st.H
  let H_mid_union := st.H.applyBatch uhPref
  let t' := st.t + 1
  let j := chooseLevel L st.q t'
  if hj0 : j = 0 then
    let res := initAt G' L st.q t' sparsify
    let H_new_E := res.state.H.E
    let uhDel := ((H_mid_union.E \ H_new_E).sort (· ≤ ·)).map Update.delete
    let uhIns := ((H_new_E \ H_mid_union.E).sort (· ≤ ·)).map
      fun e => Update.insert e (G'.tail e) (G'.head e)
    let uh := uhPref ++ uhDel ++ uhIns
    let H' := st.H.applyBatch uh
    let D := H'.E
    { state := { res.state with H := H' }
      UH := uh
      D := D
      cost := res.cost + (L + 1) * st.G.updateEnc u + H_mid_union.E.card + H_new_E.card +
        uh.length + D.card }
  else
    let H_lt := unionGraphLt G' H_mid j
    let S_prev := S_mid ⟨j - 1, by
      have hjle : j ≤ L := chooseLevel_le L st.q t'
      omega⟩
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    let E_aff := affectedEdges G' H_lt piLt_mid S_prev
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let H_aux := buildAuxHost G' H_lt E_aff
    let embJH := projWalk G' H_lt piLt_mid S_prev
    let out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
    let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    let embMid := Embedding.comp embJH outEmb
    let H_j : MGraph := { V := G'.V, E := out.Jtilde.E, tail := G'.tail, head := G'.head }
    let Pi_j := reembedWalk G' H_lt piLt_mid embMid S_prev
    let H_level' : Fin (L + 1) → MGraph := fun i =>
      if i.1 < j then H_mid i
      else if i.1 = j then H_j
      else emptyGraphOn G'
    let Pi_level' : Fin (L + 1) → Embedding := fun i =>
      if i.1 < j then st.Pi_level i
      else if i.1 = j then Pi_j
      else fun _ => []
    let inDom' : Fin (L + 1) → Finset ℕ := fun i =>
      if i.1 < j then inDom_mid i
      else if i.1 = j then E_aff
      else ∅
    let S_level' : Fin (L + 1) → Finset ℕ := fun i =>
      if i.1 < j then S_mid i else ∅
    let H_new_E := unionEdgesLt H_level' (L + 1)
    let uhDel := ((H_mid_union.E \ H_new_E).sort (· ≤ ·)).map Update.delete
    let uhIns := ((H_new_E \ H_mid_union.E).sort (· ≤ ·)).map
      fun e => Update.insert e (G'.tail e) (G'.head e)
    let uh := uhPref ++ uhDel ++ uhIns
    let H' := st.H.applyBatch uh
    let D := out.Jtilde.E.biUnion fun e => walkEdges (embJH e)
    let affWork := ∑ e ∈ E_aff, ((piLt_mid e).length + (Pi_j e).length)
    let reembWork := ∑ e ∈ out.Jtilde.E, (embJH e).length
    let stepCost := (L + 1) * st.G.updateEnc u + S_prev.card + E_aff.card + affWork +
      out.cost + out.Jtilde.E.card + reembWork + uh.length + D.card
    { state :=
        { q := st.q
          t := t'
          G := G'
          H_level := H_level'
          Pi_level := Pi_level'
          inDom := inDom'
          S_level := S_level'
          H := H' }
      UH := uh
      D := D
      cost := stepCost }

/-- Helper loop for processing a batch `U` of single updates in order. -/
def updateGo {L : ℕ} (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (cur : DynSpannerState L) (us : List Update) (uhAcc : List Update)
    (dAcc : Finset ℕ) (cAcc : ℕ) : StepOut L :=
  match us with
  | [] =>
    { state := cur
      UH := uhAcc
      D := dAcc ∩ cur.H.E
      cost := cAcc }
  | u :: rest =>
    let res := step cur u sparsify
    updateGo sparsify res.state rest (uhAcc ++ res.UH) (dAcc ∪ res.D) (cAcc + res.cost)

/-- Process a batch `U` of single updates in order, accumulating `U_H`, `D` (intersected with the
final spanner `H.E`), and the total operation count. -/
def update {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : StepOut L :=
  updateGo sparsify st U [] ∅ 0

end

end MinCostFlow.DynSpanner
