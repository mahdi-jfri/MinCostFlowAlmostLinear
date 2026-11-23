module

public import WordRAM.Layout
public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph

import WordRAM.Memory
import Mathlib.Tactic.Ring

/-!
# Memory Layouts for `Sparsify` (Algorithm 4)

This file defines the canonical Word-RAM memory encodings and access/framing lemmas shared by the
tool contracts (`ToolContracts.lean`) and the machine procedures of Algorithm 4 (`Sparsify`):

1. **`GraphAt`**: `ListAt mem a G.encode` (`n :: m :: [u₀, v₀, …, u_{m-1}, v_{m-1}]`), matching
   `Cited.Graph.encode` (`Graphs.lean`) and `Cited.readGraph` (`ChuzhoySaranurak.lean`).
2. **`WalkAt`**: `ListAt mem a (Walk.encode P)` where
   `Walk.encode P = [P.verts.length] ++ P.verts ++ [P.edges.length] ++ P.edges`.
3. **`EmbAt` / `EmbBounded`**: pointer table at `a, …, a + m - 1` pointing to `WalkAt` blocks for
   edges `0, …, m - 1`, with an explicit upper address bound `EmbBounded` for frame preservation.
4. **`Decompose.encode` / `DecomposeOutAt`**: flat component-record layout
   `[ℓ, phiNum, phiDen] ++ level ++ [rawComps.length] ++ flatMap (fun (i, vs) => i :: vs.length :: vs)`,
   together with `mkDecomposeOutput` and order/size bounds showing total size `≤ 4 + 5 · G.m`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM
open MinCostFlow.Cited

/-! ## `GraphAt` — encoding of `Cited.Graph` -/

/-- Graph `G` stored at `a` using `Cited.Graph.encode`:
`mem a = G.n`, `mem (a + 1) = G.m`, and `mem (a + 2 + 2*j) = e_j.1`, `mem (a + 3 + 2*j) = e_j.2`. -/
def GraphAt (mem : ℕ → ℕ) (a : ℕ) (G : Cited.Graph) : Prop :=
  ListAt mem a G.encode

private lemma flatMap_pair_length (es : List (ℕ × ℕ)) :
    (es.flatMap fun e => [e.1, e.2]).length = 2 * es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem graph_encode_length (G : Cited.Graph) : G.encode.length = 2 + 2 * G.m := by
  simp only [Graph.encode, Graph.m, List.length_cons, flatMap_pair_length]
  omega

theorem graphAt_n {mem : ℕ → ℕ} {a : ℕ} {G : Cited.Graph} (h : GraphAt mem a G) :
    mem a = G.n := by
  have := (listAt_cons.mp h).1
  exact this

theorem graphAt_m {mem : ℕ → ℕ} {a : ℕ} {G : Cited.Graph} (h : GraphAt mem a G) :
    mem (a + 1) = G.m := by
  have h1 := (listAt_cons.mp h).2
  exact (listAt_cons.mp h1).1

private lemma flatMap_pair_getElem (es : List (ℕ × ℕ)) (j : ℕ) (hj : j < es.length) :
    (es.flatMap fun e => [e.1, e.2])[2 * j]'(by rw [flatMap_pair_length]; omega) = (es[j]'hj).1 ∧
    (es.flatMap fun e => [e.1, e.2])[2 * j + 1]'(by rw [flatMap_pair_length]; omega) =
      (es[j]'hj).2 := by
  induction es generalizing j with
  | nil => simp at hj
  | cons e es ih =>
    cases j with
    | zero =>
      simp [List.flatMap_cons]
    | succ j =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
      have hsub := ih j hj
      simp only [List.flatMap_cons, List.cons_append, List.nil_append,
        show 2 * (j + 1) = 2 * j + 2 by omega,
        List.getElem_cons_succ]
      exact hsub

theorem graphAt_edge_fst {mem : ℕ → ℕ} {a : ℕ} {G : Cited.Graph}
    (h : GraphAt mem a G) {j : ℕ} (hj : j < G.m) :
    mem (a + 2 + 2 * j) = (G.edges[j]'hj).1 := by
  have hes : ListAt mem (a + 2) (G.edges.flatMap fun e => [e.1, e.2]) := by
    simpa [Nat.add_assoc] using (listAt_cons.mp (listAt_cons.mp h).2).2
  have hget := hes.getElem (by rw [flatMap_pair_length]; exact Nat.mul_lt_mul_of_pos_left hj (by decide))
  rw [Nat.add_assoc] at hget ⊢
  rw [hget]
  exact (flatMap_pair_getElem G.edges j hj).1

theorem graphAt_edge_snd {mem : ℕ → ℕ} {a : ℕ} {G : Cited.Graph}
    (h : GraphAt mem a G) {j : ℕ} (hj : j < G.m) :
    mem (a + 3 + 2 * j) = (G.edges[j]'hj).2 := by
  have hes : ListAt mem (a + 2) (G.edges.flatMap fun e => [e.1, e.2]) := by
    simpa [Nat.add_assoc] using (listAt_cons.mp (listAt_cons.mp h).2).2
  have hlen : 2 * j + 1 < (G.edges.flatMap fun e => [e.1, e.2]).length := by
    rw [flatMap_pair_length]
    simp only [Graph.m] at hj ⊢
    omega
  have hget := hes.getElem hlen
  rw [show a + 3 + 2 * j = a + 2 + (2 * j + 1) by omega, hget]
  exact (flatMap_pair_getElem G.edges j hj).2

theorem graphAt_of_cells {mem : ℕ → ℕ} {a : ℕ} {G : Cited.Graph}
    (hn : mem a = G.n) (hm : mem (a + 1) = G.m)
    (he : ∀ j (hj : j < G.m),
      mem (a + 2 + 2 * j) = (G.edges[j]'hj).1 ∧ mem (a + 3 + 2 * j) = (G.edges[j]'hj).2) :
    GraphAt mem a G := by
  rw [GraphAt, Graph.encode, listAt_cons, listAt_cons]
  refine ⟨hn, hm, ?_⟩
  intro k hk
  rw [flatMap_pair_length] at hk
  have hk_div : k / 2 < G.m := by
    simp only [Graph.m]
    exact Nat.div_lt_of_lt_mul (by omega)
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hj : j < G.m := by omega
    have hmem := (he j hj).1
    have hf := (flatMap_pair_getElem G.edges j hj).1
    rw [show a + 1 + 1 + 2 * j = a + 2 + 2 * j by omega, hmem]
    exact hf.symm
  · have hj : j < G.m := by omega
    have hmem := (he j hj).2
    have hf := (flatMap_pair_getElem G.edges j hj).2
    rw [show a + 1 + 1 + (2 * j + 1) = a + 3 + 2 * j by omega, hmem]
    exact hf.symm

theorem GraphAt.of_agree_below {mem mem' : ℕ → ℕ} {a bound : ℕ} {G : Cited.Graph}
    (h : GraphAt mem a G) (hb : a + G.encode.length ≤ bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    GraphAt mem' a G :=
  ListAt.of_agree_below h hb heq

/-! ## `Walk.encode` and `WalkAt` -/

/-- Canonical flat encoding of `P : Walk`: vertex count, vertices, edge count, edges. -/
def Walk.encode (P : Walk) : List ℕ :=
  P.verts.length :: P.verts ++ P.edges.length :: P.edges

/-- `P : Walk` is stored at address `a` via `Walk.encode P`. -/
def WalkAt (mem : ℕ → ℕ) (a : ℕ) (P : Walk) : Prop :=
  ListAt mem a (Walk.encode P)

theorem walk_encode_length (P : Walk) :
    (Walk.encode P).length = 2 + P.verts.length + P.edges.length := by
  simp only [Walk.encode, List.length_cons, List.length_append]
  omega

theorem walkAt_iff {mem : ℕ → ℕ} {a : ℕ} {P : Walk} :
    WalkAt mem a P ↔
      mem a = P.verts.length ∧
      ListAt mem (a + 1) P.verts ∧
      mem (a + 1 + P.verts.length) = P.edges.length ∧
      ListAt mem (a + 2 + P.verts.length) P.edges := by
  rw [WalkAt, Walk.encode, listAt_append, listAt_cons, listAt_cons]
  simp only [List.length_cons, Nat.add_assoc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, by simpa [Nat.add_assoc, Nat.add_comm 1] using h3,
      by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, by simpa [Nat.add_assoc, Nat.add_comm 1] using h3,
      by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h4⟩

theorem WalkAt.verts_len {mem : ℕ → ℕ} {a : ℕ} {P : Walk} (h : WalkAt mem a P) :
    mem a = P.verts.length :=
  (walkAt_iff.mp h).1

theorem WalkAt.verts_listAt {mem : ℕ → ℕ} {a : ℕ} {P : Walk} (h : WalkAt mem a P) :
    ListAt mem (a + 1) P.verts :=
  (walkAt_iff.mp h).2.1

theorem WalkAt.edges_len {mem : ℕ → ℕ} {a : ℕ} {P : Walk} (h : WalkAt mem a P) :
    mem (a + 1 + P.verts.length) = P.edges.length :=
  (walkAt_iff.mp h).2.2.1

theorem WalkAt.edges_listAt {mem : ℕ → ℕ} {a : ℕ} {P : Walk} (h : WalkAt mem a P) :
    ListAt mem (a + 2 + P.verts.length) P.edges :=
  (walkAt_iff.mp h).2.2.2

theorem WalkAt.of_agree_below {mem mem' : ℕ → ℕ} {a bound : ℕ} {P : Walk}
    (h : WalkAt mem a P) (hb : a + (Walk.encode P).length ≤ bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    WalkAt mem' a P :=
  ListAt.of_agree_below h hb heq

/-! ## `EmbAt` and `EmbBounded` — pointer-table layout for edge embeddings -/

/-- Embedding `emb : ℕ → Walk` on `m` edges stored via a pointer table at `a, …, a + m - 1`,
where `mem (a + j)` holds the address of `WalkAt mem · (emb j)`. -/
def EmbAt (mem : ℕ → ℕ) (a m : ℕ) (emb : ℕ → Walk) : Prop :=
  ∀ j < m, WalkAt mem (mem (a + j)) (emb j)

/-- Memory-region bound showing that all cells used by `EmbAt mem a m emb` lie below `bound`. -/
def EmbBounded (mem : ℕ → ℕ) (a m : ℕ) (emb : ℕ → Walk) (bound : ℕ) : Prop :=
  a + m ≤ bound ∧ ∀ j < m, mem (a + j) + (Walk.encode (emb j)).length ≤ bound

theorem embAt_preserve {mem mem' : ℕ → ℕ} {a m bound : ℕ} {emb : ℕ → Walk}
    (hEmb : EmbAt mem a m emb) (hBnd : EmbBounded mem a m emb bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    EmbAt mem' a m emb ∧ EmbBounded mem' a m emb bound := by
  refine ⟨fun j hj => ?_, hBnd.1, fun j hj => ?_⟩
  · have hptr : mem' (a + j) = mem (a + j) := heq (a + j) (by have := hBnd.1; omega)
    rw [hptr]
    exact (hEmb j hj).of_agree_below (hBnd.2 j hj) heq
  · have hptr : mem' (a + j) = mem (a + j) := heq (a + j) (by have := hBnd.1; omega)
    rw [hptr]
    exact hBnd.2 j hj

theorem embBounded_ptr_lt {mem : ℕ → ℕ} {a m bound : ℕ} {emb : ℕ → Walk}
    (hBnd : EmbBounded mem a m emb bound) {j : ℕ} (hj : j < m) :
    mem (a + j) < bound := by
  have h1 := hBnd.2 j hj
  have hlen : 0 < (Walk.encode (emb j)).length := by
    rw [walk_encode_length]; omega
  omega

/-! ## `DecomposeOutAt` — flat layout for `Decompose` outputs -/

/-- Flat encoding of one component `(level, sortedVerts)`. -/
def compRecord (c : ℕ × List ℕ) : List ℕ :=
  c.1 :: c.2.length :: c.2

/-- Flat encoding of `Decompose` output:
`[ℓ, phiNum, phiDen] ++ level ++ [rawComps.length] ++ rawComps.flatMap compRecord`. -/
def Decompose.encode (ℓ phiNum phiDen : ℕ) (level : List ℕ)
    (rawComps : List (ℕ × List ℕ)) : List ℕ :=
  [ℓ, phiNum, phiDen] ++ level ++ [rawComps.length] ++ rawComps.flatMap compRecord

/-- `Decompose` output stored at address `a` via `Decompose.encode`. -/
def DecomposeOutAt (mem : ℕ → ℕ) (a ℓ phiNum phiDen : ℕ)
    (level : List ℕ) (rawComps : List (ℕ × List ℕ)) : Prop :=
  ListAt mem a (Decompose.encode ℓ phiNum phiDen level rawComps)

private lemma flatMap_compRecord_length (rawComps : List (ℕ × List ℕ)) :
    (rawComps.flatMap compRecord).length = (rawComps.map fun c => 2 + c.2.length).sum := by
  induction rawComps with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, compRecord, List.length_cons,
      List.map_cons, List.sum_cons, ih]
    omega

theorem decompose_encode_length (ℓ phiNum phiDen : ℕ) (level : List ℕ)
    (rawComps : List (ℕ × List ℕ)) :
    (Decompose.encode ℓ phiNum phiDen level rawComps).length =
      4 + level.length + (rawComps.map fun c => 2 + c.2.length).sum := by
  simp only [Decompose.encode, List.length_append, List.length_cons, List.length_nil,
    flatMap_compRecord_length]
  omega

/-- Reconstruct a mathematical `DecomposeOutput` from flat `(ℓ, level, rawComps)`. -/
def mkDecomposeOutput (ℓ : ℕ) (level : List ℕ)
    (rawComps : List (ℕ × List ℕ)) : DecomposeOutput where
  ℓ := ℓ
  level := fun j => level.getD j 0
  comps := fun i => (rawComps.filter fun c => decide (c.1 = i)).map fun c => c.2.toFinset

theorem vertsOf_toFinset_of_pairwise_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) :
    vertsOf l.toFinset = l := by
  have hnodup : l.Nodup := hl.imp fun h => ne_of_lt h
  have hle : l.Pairwise (· ≤ ·) := hl.imp fun h => le_of_lt h
  exact (List.toFinset_sort (· ≤ ·) hnodup).mpr hle

private lemma list_split_eq_of_pairwise {α : Type*} (f : α → ℕ) (lo : ℕ) :
    ∀ (l : List α), l.Pairwise (fun a b => f a ≤ f b) → (∀ x ∈ l, lo ≤ f x) →
      l.filter (fun x => decide (f x = lo)) ++ l.filter (fun x => decide (f x ≠ lo)) = l
  | [], _, _ => rfl
  | x :: xs, hp, hge => by
    rw [List.pairwise_cons] at hp
    have hxs_ge : ∀ y ∈ xs, lo ≤ f y := fun y hy => hge y (List.mem_cons_of_mem _ hy)
    have ih := list_split_eq_of_pairwise f lo xs hp.2 hxs_ge
    by_cases hfx : f x = lo
    · simp only [List.filter_cons, hfx, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        ne_eq, not_true_eq_false, List.cons_append, ih]
    · have hxlo : lo < f x := Nat.lt_of_le_of_ne (hge x List.mem_cons_self) (Ne.symm hfx)
      have hxs_eq : xs.filter (fun y => decide (f y = lo)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have hxy := hp.1 y hy
        simp only [decide_eq_true_eq]
        omega
      have hxs_ne : xs.filter (fun y => decide (f y ≠ lo)) = xs := by
        rw [List.filter_eq_self]
        intro y hy
        have hxy := hp.1 y hy
        exact decide_eq_true (by omega)
      simp only [List.filter_cons, hfx, decide_false, Bool.false_eq_true, ↓reduceIte,
        ne_eq, not_false_eq_true, decide_true, List.nil_append, hxs_eq, hxs_ne]

private lemma list_flatMap_congr {α β : Type*} (l : List α) {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private lemma list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem filter_flatMap_eq_of_pairwise {α : Type*} (f : α → ℕ) (lo len : ℕ) :
    ∀ (l : List α), l.Pairwise (fun a b => f a ≤ f b) → (∀ x ∈ l, lo ≤ f x ∧ f x < lo + len) →
      (List.range len).flatMap (fun k => l.filter fun x => decide (f x = lo + k)) = l := by
  induction len generalizing lo with
  | zero =>
    intro l _ hmem
    cases l with
    | nil => simp
    | cons x _ =>
      have hxm := hmem x List.mem_cons_self
      omega
  | succ len ih =>
    intro l hp hmem
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero]
    set l' := l.filter fun x => decide (f x ≠ lo)
    have hp' : l'.Pairwise (fun a b => f a ≤ f b) := hp.filter _
    have hmem' : ∀ x ∈ l', lo + 1 ≤ f x ∧ f x < (lo + 1) + len := by
      intro x hx
      rcases List.mem_filter.mp hx with ⟨hxl, hne⟩
      have hne' : f x ≠ lo := by simpa using hne
      have hxm := hmem x hxl
      omega
    have hcong : (List.range len).flatMap (fun k => l.filter fun x => decide (f x = lo + (k + 1))) =
        (List.range len).flatMap (fun k => l'.filter fun x => decide (f x = (lo + 1) + k)) := by
      refine list_flatMap_congr (List.range len) fun k _ => ?_
      rw [List.filter_filter]
      refine List.filter_congr fun x _ => ?_
      have : lo + (k + 1) = (lo + 1) + k := by omega
      by_cases hx : f x = lo + (k + 1)
      · have hne2 : lo + 1 + k ≠ lo := by omega
        simp [hx, this, hne2]
      · have hx' : f x ≠ (lo + 1) + k := by omega
        simp [hx, hx']
    rw [hcong, ih (lo + 1) l' hp' hmem']
    exact list_split_eq_of_pairwise f lo l hp fun x hx => (hmem x hx).1

theorem mkDecomposeOutput_rawComps_eq (ℓ : ℕ) (level : List ℕ) (rawComps : List (ℕ × List ℕ))
    (hp : rawComps.Pairwise (fun a b => a.1 ≤ b.1))
    (hbounds : ∀ c ∈ rawComps, 1 ≤ c.1 ∧ c.1 ≤ ℓ) :
    (List.range ℓ).flatMap (fun i' =>
      ((mkDecomposeOutput ℓ level rawComps).comps (i' + 1)).map fun X => (i' + 1, X)) =
      rawComps.map fun c => (c.1, c.2.toFinset) := by
  have h1 : ∀ i' : ℕ,
      (((mkDecomposeOutput ℓ level rawComps).comps (i' + 1)).map fun X => (i' + 1, X)) =
        (rawComps.filter fun c => decide (c.1 = i' + 1)).map fun c => (c.1, c.2.toFinset) := by
    intro i'
    simp only [mkDecomposeOutput, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    have heq : c.1 = i' + 1 := by simpa using (List.mem_filter.mp hc).2
    simp [heq]
  have hf1 : (List.range ℓ).flatMap (fun i' =>
      ((mkDecomposeOutput ℓ level rawComps).comps (i' + 1)).map fun X => (i' + 1, X)) =
      (List.range ℓ).flatMap (fun i' =>
        (rawComps.filter fun c => decide (c.1 = i' + 1)).map fun c => (c.1, c.2.toFinset)) :=
    list_flatMap_congr _ fun i' _ => h1 i'
  have hf2 : (List.range ℓ).flatMap (fun i' =>
      (rawComps.filter fun c => decide (c.1 = i' + 1)).map fun c => (c.1, c.2.toFinset)) =
      ((List.range ℓ).flatMap (fun i' =>
        rawComps.filter fun c => decide (c.1 = 1 + i'))).map fun c => (c.1, c.2.toFinset) := by
    rw [List.map_flatMap]
    refine list_flatMap_congr (List.range ℓ) fun i' _ => ?_
    simp [Nat.add_comm 1 i']
  rw [hf1, hf2, filter_flatMap_eq_of_pairwise (fun c => c.1) 1 ℓ rawComps hp (fun c hc => by
    have hb := hbounds c hc; omega)]

theorem decomposeOutAt_fields {mem : ℕ → ℕ} {a ℓ phiNum phiDen : ℕ}
    {level : List ℕ} {rawComps : List (ℕ × List ℕ)}
    (h : DecomposeOutAt mem a ℓ phiNum phiDen level rawComps) :
    mem a = ℓ ∧ mem (a + 1) = phiNum ∧ mem (a + 2) = phiDen ∧
      ListAt mem (a + 3) level ∧
      mem (a + 3 + level.length) = rawComps.length ∧
      ListAt mem (a + 4 + level.length) (rawComps.flatMap compRecord) := by
  have h1 : Decompose.encode ℓ phiNum phiDen level rawComps =
      ℓ :: phiNum :: phiDen :: (level ++ [rawComps.length] ++ rawComps.flatMap compRecord) := by
    simp [Decompose.encode]
  rw [DecomposeOutAt, h1, listAt_cons, listAt_cons, listAt_cons, listAt_append, listAt_append,
    listAt_singleton] at h
  rcases h with ⟨hℓ, hpn, hpd, ⟨hlvl, hlen⟩, hrest⟩
  refine ⟨hℓ, hpn, hpd, by simpa [Nat.add_assoc] using hlvl,
    by simpa [Nat.add_assoc] using hlen, ?_⟩
  rw [show a + 4 + level.length = a + 1 + 1 + 1 + (level ++ [rawComps.length]).length by
    simp [List.length_append]; omega]
  exact hrest

private lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

private lemma list_sum_map_mul {α : Type*} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma list_sum_two_add_le : ∀ (cs : List (ℕ × List ℕ)),
    (∀ c ∈ cs, 2 ≤ c.2.length) →
    (cs.map fun c => 2 + c.2.length).sum ≤ 2 * (cs.map fun c => c.2.length).sum
  | [], _ => by simp
  | c :: cs, h => by
    have hc := h c List.mem_cons_self
    have htail := list_sum_two_add_le cs fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [List.map_cons, List.sum_cons] at htail ⊢
    omega

private lemma list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, ih]

private lemma pairwise_disjoint_mem (cs : List (Finset ℕ)) :
    cs.Pairwise Disjoint → ∀ A ∈ cs, ∀ B ∈ cs, A ≠ B → Disjoint A B := by
  induction cs with
  | nil => intro _ _ hA; cases hA
  | cons Z zs ih =>
    intro hp A hA B hB hne
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hA with rfl | hAz
    · rcases List.mem_cons.mp hB with rfl | hBz
      · exact (hne rfl).elim
      · exact hp.1 B hBz
    · rcases List.mem_cons.mp hB with rfl | hBz
      · exact (hp.1 A hAz).symm
      · exact ih hp.2 A hAz B hBz hne

private lemma nodup_of_pairwise_disjoint_card2 : ∀ (cs : List (Finset ℕ)),
    cs.Pairwise Disjoint → (∀ X ∈ cs, 2 ≤ X.card) → cs.Nodup
  | [], _, _ => List.nodup_nil
  | X :: xs, hp, hc => by
    rw [List.pairwise_cons] at hp
    rw [List.nodup_cons]
    refine ⟨fun hXmem => ?_, nodup_of_pairwise_disjoint_card2 xs hp.2 fun Y hY =>
      hc Y (List.mem_cons_of_mem _ hY)⟩
    have hdisX : Disjoint X X := hp.1 X hXmem
    have h2X : 2 ≤ X.card := hc X List.mem_cons_self
    rcases Finset.card_pos.mp (by omega : 0 < X.card) with ⟨x, hx⟩
    exact Finset.disjoint_left.mp hdisX hx hx

private lemma list_range_filter_length (m : ℕ) (p : ℕ → Bool) :
    ((List.range m).filter p).length = ((Finset.range m).filter fun j => p j = true).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, Finset.range_add_one,
      Finset.filter_insert, ih]
    cases hpm : p m
    · simp [hpm]
    · have hm : m ∉ (Finset.range m).filter fun j => p j = true := by simp
      simp [hpm, Finset.card_insert_of_notMem hm, Nat.add_comm]

theorem decompose_rawComps_size_le {G : Cited.Graph} {d : DecomposeOutput}
    {rawComps : List (ℕ × List ℕ)}
    (hmatch : rawComps.map (fun c => (c.1, c.2.toFinset)) =
      (List.range d.ℓ).flatMap fun i' => (d.comps (i' + 1)).map fun X => (i' + 1, X))
    (hnodup : ∀ c ∈ rawComps, c.2.Nodup ∧ 2 ≤ c.2.length)
    (hdisj : ∀ i, 1 ≤ i → i ≤ d.ℓ → (d.comps i).Pairwise Disjoint)
    (hc2 : ∀ i, 1 ≤ i → i ≤ d.ℓ → ∀ X ∈ d.comps i, 2 ≤ X.card)
    (hdeg : ∀ i, 1 ≤ i → i ≤ d.ℓ → ∀ X ∈ d.comps i, ∀ x ∈ X, 1 ≤ (d.graphAt G i).degIn X x) :
    (rawComps.map fun c => 2 + c.2.length).sum ≤ 4 * G.m := by
  have hsum_verts : (rawComps.map fun c => c.2.length).sum =
      ((List.range d.ℓ).map fun i' => ((d.comps (i' + 1)).map Finset.card).sum).sum := by
    have hmap := congrArg (List.map fun p => p.2.card) hmatch
    simp only [List.map_map, Function.comp_def, List.map_flatMap] at hmap
    have hL : (rawComps.map fun c => c.2.toFinset.card).sum =
        (rawComps.map fun c => c.2.length).sum := by
      congr 1
      refine List.map_congr_left fun c hc => ?_
      exact List.toFinset_card_of_nodup (hnodup c hc).1
    have hR : ((List.range d.ℓ).flatMap fun i' =>
        ((d.comps (i' + 1)).map fun X => X.card)).sum =
        ((List.range d.ℓ).map fun i' => ((d.comps (i' + 1)).map Finset.card).sum).sum := by
      rw [list_sum_flatMap]
    rw [← hL, hmap, hR]
  have hsum_two : (rawComps.map fun c => 2 + c.2.length).sum ≤
      2 * (rawComps.map fun c => c.2.length).sum :=
    list_sum_two_add_le rawComps fun c hc => (hnodup c hc).2
  suffices hlev : ((List.range d.ℓ).map fun i' => ((d.comps (i' + 1)).map Finset.card).sum).sum ≤
      2 * G.m by
    omega
  have hlev_edge : ∀ i' ∈ List.range d.ℓ,
      ((d.comps (i' + 1)).map Finset.card).sum ≤ 2 * (d.edgesAt G (i' + 1)).length := by
    intro i' hi'
    have hi1 : 1 ≤ i' + 1 := by omega
    have hiℓ : i' + 1 ≤ d.ℓ := by rw [List.mem_range] at hi'; omega
    set Gi := d.graphAt G (i' + 1)
    have hcomp_card : ∀ X ∈ d.comps (i' + 1), X.card ≤ 2 * (Gi.inside X).length := by
      intro X hX
      calc X.card = ∑ _x ∈ X, 1 := by simp
        _ ≤ ∑ x ∈ X, Gi.degIn X x := Finset.sum_le_sum fun x hx => hdeg (i' + 1) hi1 hiℓ X hX x hx
        _ = Gi.volIn X X := rfl
        _ = 2 * (Gi.inside X).length := volIn_self_eq_two_mul_inside Gi X
    have hdisj_all := hdisj (i' + 1) hi1 hiℓ
    have hsum_ins : ∑ X ∈ (d.comps (i' + 1)).toFinset, (Gi.inside X).length ≤ Gi.edges.length := by
      have hdis : Set.PairwiseDisjoint ((d.comps (i' + 1)).toFinset : Set (Finset ℕ)) id :=
        fun X hX Y hY hne => pairwise_disjoint_mem (d.comps (i' + 1)) hdisj_all
          X (List.mem_toFinset.mp hX) Y (List.mem_toFinset.mp hY) hne
      have hinside_card : ∀ X : Finset ℕ,
          (Gi.inside X).length =
            ((Finset.range Gi.m).filter fun j =>
              (Gi.edges.getD j (0, 0)).1 ∈ X ∧ (Gi.edges.getD j (0, 0)).2 ∈ X).card := by
        intro X
        rw [Graph.inside, list_filter_length_eq_range_card _ (0, 0)]
        congr 1
      simp_rw [hinside_card]
      rw [← Finset.card_biUnion]
      · refine le_trans (Finset.card_le_card (t := Finset.range Gi.m) ?_) ?_
        · intro j hj
          rcases Finset.mem_biUnion.mp hj with ⟨X, _, hjf⟩
          exact (Finset.mem_filter.mp hjf).1
        · rw [Finset.card_range]
          rfl
      · intro X hX Y hY hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro j hjX hjY
        have hX1 := (Finset.mem_filter.mp hjX).2.1
        have hY1 := (Finset.mem_filter.mp hjY).2.1
        exact Finset.disjoint_left.mp (hdis hX hY hne) hX1 hY1
    have hnodup_c : (d.comps (i' + 1)).Nodup :=
      nodup_of_pairwise_disjoint_card2 (d.comps (i' + 1)) hdisj_all (hc2 (i' + 1) hi1 hiℓ)
    calc ((d.comps (i' + 1)).map Finset.card).sum
        ≤ ((d.comps (i' + 1)).map fun X => 2 * (Gi.inside X).length).sum :=
          list_sum_map_le _ _ _ hcomp_card
      _ = 2 * ((d.comps (i' + 1)).map fun X => (Gi.inside X).length).sum :=
          list_sum_map_mul _ 2 _
      _ = 2 * ∑ X ∈ (d.comps (i' + 1)).toFinset, (Gi.inside X).length := by
          rw [List.sum_toFinset _ hnodup_c]
      _ ≤ 2 * Gi.edges.length := Nat.mul_le_mul_left 2 hsum_ins
      _ = 2 * (d.edgesAt G (i' + 1)).length := by simp [Gi, DecomposeOutput.graphAt]
  have hsum_edges : ((List.range d.ℓ).map fun i' => (d.edgesAt G (i' + 1)).length).sum ≤ G.m := by
    have hcard_at : ∀ i' : ℕ,
        (d.edgesAt G (i' + 1)).length =
          ((Finset.range G.m).filter fun j => d.level j = i' + 1).card := by
      intro i'
      rw [DecomposeOutput.edgesAt, list_range_filter_length]
      congr 1
    simp_rw [hcard_at]
    rw [list_sum_map_range, ← Finset.card_biUnion]
    · refine le_trans (Finset.card_le_card (t := Finset.range G.m) ?_) ?_
      · intro j hj
        rcases Finset.mem_biUnion.mp hj with ⟨_, _, hjf⟩
        exact (Finset.mem_filter.mp hjf).1
      · rw [Finset.card_range]
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro j hja hjb
      have ha' := (Finset.mem_filter.mp hja).2
      have hb' := (Finset.mem_filter.mp hjb).2
      omega
  calc ((List.range d.ℓ).map fun i' => ((d.comps (i' + 1)).map Finset.card).sum).sum
      ≤ ((List.range d.ℓ).map fun i' => 2 * (d.edgesAt G (i' + 1)).length).sum :=
        list_sum_map_le _ _ _ hlev_edge
    _ = 2 * ((List.range d.ℓ).map fun i' => (d.edgesAt G (i' + 1)).length).sum :=
        list_sum_map_mul _ 2 _
    _ ≤ 2 * G.m := Nat.mul_le_mul_left 2 hsum_edges

end MinCostFlow.Spanner
