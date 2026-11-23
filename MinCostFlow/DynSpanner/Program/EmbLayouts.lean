module

public import MinCostFlow.Basic.Embedding
public import MinCostFlow.Spanner.Layouts
public import WordRAM.Memory

/-!
# Walk and embedding memory layouts for `MGraph`

This file defines Word-RAM memory layouts for `MGraph` walks (`List (ℕ × Bool)`) and embeddings
(`MinCostFlow.Embedding`) and connects them to `MinCostFlow.Spanner.Layouts` (`WalkAt`, `EmbAt`)
on `Cited.Graph`:

* `mWalkEncode P`: `[P.length, e₀, d₀, e₁, d₁, ...]` where `dᵢ = if P[i].2 then 1 else 0`, of length
  `1 + 2 * P.length`.
* `MWalkAt mem a P`: `ListAt mem a (mWalkEncode P)`.
* `mWalkToCitedWalk G u P`: constructs `{ verts := G.walkVertices u P, edges := P.map Prod.fst }`,
  letting us reuse `Spanner.WalkAt` directly when vertex-annotated walks are represented.
* `MEmbAt mem a E eCap emb` and `MEmbBounded mem a E eCap emb lo hi`: edge-ID-indexed array of
  pointers `mem (a + e)` to `MWalkAt mem (mem (a + e)) (emb e)` for every `e ∈ E`.
* `MEmbListAt mem a edges emb`: dense pointer array indexed by `j < edges.length` (matching
  `Spanner.EmbAt`).
-/

namespace MinCostFlow.DynSpanner.Program

@[expose] public section

open WordRAM
open MinCostFlow.Spanner

/-! ## Walk encoding for `MGraph` -/

/-- Encode an `MGraph` walk `P : List (ℕ × Bool)` as `[P.length, e₀, d₀, e₁, d₁, ...]` where
`dᵢ = 1` for forward edges (`true`) and `0` for backward edges (`false`). -/
def mWalkEncode (P : List (ℕ × Bool)) : List ℕ :=
  P.length :: P.flatMap fun p => [p.1, if p.2 then 1 else 0]

/-- `P : List (ℕ × Bool)` is stored in memory starting at `a`. -/
def MWalkAt (mem : ℕ → ℕ) (a : ℕ) (P : List (ℕ × Bool)) : Prop :=
  ListAt mem a (mWalkEncode P)

/-- Translate an `MGraph` walk `(u, P)` into a `Spanner.Walk` with explicit vertex sequence
`G.walkVertices u P` and edge sequence `P.map Prod.fst`. -/
def mWalkToCitedWalk (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) : MinCostFlow.Spanner.Walk :=
  { verts := G.walkVertices u P, edges := P.map Prod.fst }

/-- Reuse `Spanner.WalkAt` to store an explicit vertex-annotated `MGraph` walk `(G, u, P)`. -/
def MGraphCitedWalkAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) (u : ℕ)
    (P : List (ℕ × Bool)) : Prop :=
  WalkAt mem a (mWalkToCitedWalk G u P)

/-! ## Embedding layouts for `MGraph` -/

/-- Edge-ID-indexed embedding layout: for each `e ∈ E` (`e < eCap`), `mem (a + e)` points to an
`MWalkAt` encoding of `emb e`. -/
def MEmbAt (mem : ℕ → ℕ) (a : ℕ) (E : Finset ℕ) (eCap : ℕ)
    (emb : MinCostFlow.Embedding) : Prop :=
  ∀ e ∈ E, e < eCap ∧ MWalkAt mem (mem (a + e)) (emb e)

/-- Bounded edge-ID-indexed embedding layout contained inside `[lo, hi)`. -/
def MEmbBounded (mem : ℕ → ℕ) (a : ℕ) (E : Finset ℕ) (eCap : ℕ)
    (emb : MinCostFlow.Embedding) (lo hi : ℕ) : Prop :=
  lo ≤ a ∧ a + eCap ≤ hi ∧
  ∀ e ∈ E, e < eCap ∧
    lo ≤ mem (a + e) ∧
    mem (a + e) + (mWalkEncode (emb e)).length ≤ hi ∧
    MWalkAt mem (mem (a + e)) (emb e)

/-- Dense embedding pointer array ordered along `edges : List ℕ`, mirroring `Spanner.EmbAt`. -/
def MEmbListAt (mem : ℕ → ℕ) (a : ℕ) (edges : List ℕ)
    (emb : MinCostFlow.Embedding) : Prop :=
  ∀ j (hj : j < edges.length), MWalkAt mem (mem (a + j)) (emb edges[j])

end

/-! ## Encoding and framing lemmas -/

public section

lemma flatMap_pair_length (P : List (ℕ × Bool)) :
    (P.flatMap fun p => [p.1, if p.2 then 1 else 0]).length = 2 * P.length := by
  induction P with
  | nil => simp
  | cons p ps ih =>
    simp [List.flatMap_cons, ih]
    omega

lemma mWalkEncode_length (P : List (ℕ × Bool)) :
    (mWalkEncode P).length = 1 + 2 * P.length := by
  simp [mWalkEncode]
  omega

lemma flatMap_pair_getElem_even {P : List (ℕ × Bool)} {i : ℕ} (hi : i < P.length) :
    (P.flatMap fun p => [p.1, if p.2 then 1 else 0])[2 * i]'(by
      rw [flatMap_pair_length]; omega) = P[i].1 := by
  induction P generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => simp [List.flatMap_cons]
    | succ k =>
      have hk : k < ps.length := Nat.lt_of_succ_lt_succ hi
      simp only [List.flatMap_cons, List.cons_append, List.getElem_cons_succ]
      have hsub := ih hk
      simpa [show 2 * (k + 1) = (2 * k + 1) + 1 by omega] using hsub

lemma flatMap_pair_getElem_odd {P : List (ℕ × Bool)} {i : ℕ} (hi : i < P.length) :
    (P.flatMap fun p => [p.1, if p.2 then 1 else 0])[2 * i + 1]'(by
      rw [flatMap_pair_length]; omega) = if P[i].2 then 1 else 0 := by
  induction P generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => simp [List.flatMap_cons]
    | succ k =>
      have hk : k < ps.length := Nat.lt_of_succ_lt_succ hi
      simp only [List.flatMap_cons, List.cons_append, List.getElem_cons_succ]
      have hsub := ih hk
      simpa [show 2 * (k + 1) = 2 * k + 1 + 1 by omega] using hsub

lemma MWalkAt.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)}
    (hP : MWalkAt mem a P)
    (hagree : ∀ addr, a ≤ addr → addr < a + 1 + 2 * P.length → mem' addr = mem addr) :
    MWalkAt mem' a P := by
  intro i hi
  have hi' : i < 1 + 2 * P.length := by simpa [mWalkEncode_length] using hi
  exact (hagree (a + i) (Nat.le_add_right _ _) (by omega)).trans (hP i hi)

lemma MWalkAt_head {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)} (hP : MWalkAt mem a P) :
    mem a = P.length := by
  have h0 := hP 0 (by simp [mWalkEncode])
  simpa [mWalkEncode] using h0

lemma MWalkAt_step_edge {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)} (hP : MWalkAt mem a P)
    {i : ℕ} (hi : i < P.length) :
    mem (a + 1 + 2 * i) = P[i].1 := by
  have hlt : 1 + 2 * i < (mWalkEncode P).length := by rw [mWalkEncode_length]; omega
  have h := hP (1 + 2 * i) hlt
  rw [Nat.add_assoc, h]
  simpa [mWalkEncode, show 1 + 2 * i = 2 * i + 1 by omega] using flatMap_pair_getElem_even hi

lemma MWalkAt_step_dir {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)} (hP : MWalkAt mem a P)
    {i : ℕ} (hi : i < P.length) :
    mem (a + 1 + 2 * i + 1) = if P[i].2 then 1 else 0 := by
  have hlt : 2 * i + 2 < (mWalkEncode P).length := by rw [mWalkEncode_length]; omega
  have h := hP (2 * i + 2) hlt
  rw [show a + 1 + 2 * i + 1 = a + (2 * i + 2) by omega]
  simpa [mWalkEncode, show 2 * i + 2 = (2 * i + 1) + 1 by omega] using
    h.trans (flatMap_pair_getElem_odd hi)

lemma MEmbAt.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {E : Finset ℕ} {eCap : ℕ}
    {emb : MinCostFlow.Embedding} {lo hi : ℕ}
    (hE : MEmbBounded mem a E eCap emb lo hi)
    (hagree : ∀ addr, lo ≤ addr → addr < hi → mem' addr = mem addr) :
    MEmbBounded mem' a E eCap emb lo hi := by
  rcases hE with ⟨hlo, hhi, hbody⟩
  refine ⟨hlo, hhi, fun e he => ?_⟩
  rcases hbody e he with ⟨he_cap, hp_lo, hp_hi, hwalk⟩
  have hptr : mem' (a + e) = mem (a + e) :=
    hagree (a + e) (by omega) (by omega)
  refine ⟨he_cap, hptr ▸ hp_lo, hptr ▸ hp_hi, ?_⟩
  rw [hptr]
  refine hwalk.of_agree fun addr h1 h2 => hagree addr (by omega) ?_
  rw [mWalkEncode_length] at hp_hi
  omega

lemma MEmbBounded.to_MEmbAt {mem : ℕ → ℕ} {a : ℕ} {E : Finset ℕ} {eCap : ℕ}
    {emb : MinCostFlow.Embedding} {lo hi : ℕ}
    (hE : MEmbBounded mem a E eCap emb lo hi) :
    MEmbAt mem a E eCap emb :=
  fun e he => let h := hE.2.2 e he; ⟨h.1, h.2.2.2⟩

lemma MEmbListAt.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {edges : List ℕ}
    {emb : MinCostFlow.Embedding}
    (hE : MEmbListAt mem a edges emb)
    (hptrs : ∀ j < edges.length, mem' (a + j) = mem (a + j))
    (hwalks : ∀ j (hj : j < edges.length) addr,
      mem (a + j) ≤ addr → addr < mem (a + j) + 1 + 2 * (emb edges[j]).length →
      mem' addr = mem addr) :
    MEmbListAt mem' a edges emb := by
  intro j hj
  rw [hptrs j hj]
  exact (hE j hj).of_agree (hwalks j hj)

end

end MinCostFlow.DynSpanner.Program
