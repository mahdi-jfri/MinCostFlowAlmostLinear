module

public import WordRAM.Layout
public import WordRAM.Memory
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.ExpanderDecomp.RouteOrCut

import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Memory Layouts and Local-Index Transport for the `RouteOrCut` Program

Defines the Word-RAM memory layouts for the deterministic `RouteOrCut` procedure:
1. **Input layouts**:
   - Host graph `G`: `GraphAt mem gAddr G` (`G.encode`).
   - Vertex set `X`: `VertSetAt mem xAddr X` (a nodup length-prefixed list `SeqAt`).
   - Terminal pairs `pairs`: `PairsAt mem pAddr pairs` (`k` followed by `k` pairs of pointers
     to `VertSetAt` lists for `(A_i, B_i)`).
2. **Output layout**:
   - `RouteFullOutAt mem outAddr res`: tag word (`0` for `matched`, `1` for `cut`), followed by
     pointers to `MatchingsAt` (one `MatchListAt` per terminal pair) and `WalksAt` (one
     edge-index `SeqAt` per matching edge in `matchings.flatten` order), or a pointer to
     `VertSetAt` for the cut `U`.
3. **Compact local representation of `G[X]`**:
   - Order-preserving bijection `origOf X` / `locOf X` between `0 .. |X| - 1` and `X` via
     `X.sort (· ≤ ·)`, so strictly increasing local-ID lists map directly to `Finset.sort (· ≤ ·)`.
   - Local CSR predicates `AdjCsrAt` and `NbCsrAt`, plus singly-linked path chains `PathChainAt`
     supporting `O(1)` prepend (within `shortPathBlock`) and `O(1)` tail-append (across batches).
4. **Edge-index invariance lemmas**:
   - `bfsLayers`, `growBall`, and `batchBallLoop` depend only on `(adj u).map Prod.fst`, and
     `adjOf ⟨G.n, G.inside V⟩ X v` matches the `V`-filtered neighbors of `adjOf G X v`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Input and Output Memory Layouts -/

/-- Vertex set `X` stored at `a` as a duplicate-free length-prefixed list (`SeqAt`). -/
def VertSetAt (mem : ℕ → ℕ) (a : ℕ) (X : Finset ℕ) : Prop :=
  ∃ xs : List ℕ, xs.Nodup ∧ xs.toFinset = X ∧ SeqAt mem a xs

/-- Terminal pairs `(A_i, B_i)` stored at `pAddr`: `mem pAddr = pairs.length`, followed by
pointers `(aPtr_i, bPtr_i)` at `pAddr + 1 + 2 * i` and `pAddr + 2 + 2 * i` to `VertSetAt`. -/
def PairsAt (mem : ℕ → ℕ) (pAddr : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  mem pAddr = pairs.length ∧
  ∀ i (hi : i < pairs.length),
    VertSetAt mem (mem (pAddr + 1 + 2 * i)) (pairs[i]'hi).1 ∧
    VertSetAt mem (mem (pAddr + 2 + 2 * i)) (pairs[i]'hi).2

/-- All addresses occupied by `PairsAt mem pAddr pairs` lie strictly below `bound`. -/
def PairsBounded (mem : ℕ → ℕ) (pAddr : ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (bound : ℕ) : Prop :=
  pAddr + 1 + 2 * pairs.length ≤ bound ∧
  ∀ i (hi : i < pairs.length),
    let aPtr := mem (pAddr + 1 + 2 * i)
    let bPtr := mem (pAddr + 2 + 2 * i)
    aPtr + 1 + (pairs[i]'hi).1.card ≤ bound ∧
    bPtr + 1 + (pairs[i]'hi).2.card ≤ bound

/-- A single partial matching `M : List (ℕ × ℕ)` stored at address `a`: `a = 0` represents `[]`,
and otherwise `mem a = M.length` followed by `EdgesAt mem (a + 1) M`. -/
def MatchListAt (mem : ℕ → ℕ) (a : ℕ) (M : List (ℕ × ℕ)) : Prop :=
  if a = 0 then M = [] else mem a = M.length ∧ EdgesAt mem (a + 1) M

/-- List of per-pair matchings stored at `mPtr`: `mem mPtr = matchings.length`, followed by
pointers `mem (mPtr + 1 + i)` satisfying `MatchListAt`. -/
def MatchingsAt (mem : ℕ → ℕ) (mPtr : ℕ) (matchings : List (List (ℕ × ℕ))) : Prop :=
  mem mPtr = matchings.length ∧
  ∀ i (hi : i < matchings.length),
    MatchListAt mem (mem (mPtr + 1 + i)) (matchings[i]'hi)

/-- Embedding walks for the `len` flattened matching edges stored at `wPtr`: `mem wPtr = len`,
followed by pointers `mem (wPtr + 1 + j)` to `SeqAt mem _ (emb j)`. -/
def WalksAt (mem : ℕ → ℕ) (wPtr len : ℕ) (emb : ℕ → List ℕ) : Prop :=
  mem wPtr = len ∧
  ∀ j < len, SeqAt mem (mem (wPtr + 1 + j)) (emb j)

/-- Output layout of `RouteOrCut` at `outAddr`:
* tag `0` (`matched`): `mem (outAddr + 1)` points to `MatchingsAt`, `mem (outAddr + 2)` points
  to `WalksAt` in the order of `matchings.flatten`.
* tag `1` (`cut`): `mem (outAddr + 1)` points to `VertSetAt` for the cut `U`. -/
def RouteFullOutAt (mem : ℕ → ℕ) (outAddr : ℕ) : RouteResult → Prop
  | .matched matchings emb =>
    mem outAddr = 0 ∧
    MatchingsAt mem (mem (outAddr + 1)) matchings ∧
    WalksAt mem (mem (outAddr + 2)) matchings.flatten.length emb
  | .cut U =>
    mem outAddr = 1 ∧
    VertSetAt mem (mem (outAddr + 1)) U

/-! ## 2. Canonical Sorted Local Indexing of `X` -/

/-- Sorted list of vertices of `X` in strictly increasing order. -/
def sortedX (X : Finset ℕ) : List ℕ :=
  X.sort (· ≤ ·)

/-- Original vertex ID of local index `i < X.card`. -/
def origOf (X : Finset ℕ) (i : ℕ) : ℕ :=
  (sortedX X).getD i 0

/-- Local index `0 .. X.card - 1` of original vertex `u ∈ X`. -/
def locOf (X : Finset ℕ) (u : ℕ) : ℕ :=
  (sortedX X).idxOf u

/-- Local CSR prefix-sum offset for an arbitrary adjacency map `adj` on `X`. -/
def adjCsrOff (X : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (adj (origOf X i)).length

/-- Neighbor-only local CSR layout for `adj` on `X` (`off[0..|X|]` and `nb[0..off[|X|]-1]`). -/
def NbCsrAt (mem : ℕ → ℕ) (offAddr nbAddr : ℕ) (X : Finset ℕ)
    (adj : ℕ → List (ℕ × ℕ)) : Prop :=
  (∀ i ≤ X.card, mem (offAddr + i) = adjCsrOff X adj i) ∧
  (∀ i < X.card, ∀ j (hj : j < (adj (origOf X i)).length),
    mem (nbAddr + adjCsrOff X adj i + j) = locOf X ((adj (origOf X i))[j]'hj).1)

/-- Full local CSR layout for `adj` on `X` (`off`, `nb` in local IDs, and `edge` in host IDs). -/
def AdjCsrAt (mem : ℕ → ℕ) (offAddr nbAddr edgeAddr : ℕ) (X : Finset ℕ)
    (adj : ℕ → List (ℕ × ℕ)) : Prop :=
  NbCsrAt mem offAddr nbAddr X adj ∧
  (∀ i < X.card, ∀ j (hj : j < (adj (origOf X i)).length),
    mem (edgeAddr + adjCsrOff X adj i + j) = ((adj (origOf X i))[j]'hj).2)

/-! ## 3. Singly-Linked Path Chains for `O(1)` Prepend and Tail-Append -/

/-- Singly-linked list of routed walks starting at `head`, where each node at `nd ≠ 0` occupies
4 words `[locOf X s, locOf X t, walkPtr, nextNd]` with `SeqAt mem walkPtr es`, and every node
and walk lies in `[lo, hi)`. -/
def PathListAt (mem : ℕ → ℕ) (X : Finset ℕ) (lo hi : ℕ) :
    ℕ → List ((ℕ × ℕ) × List ℕ) → Prop
  | head, [] => head = 0
  | head, ((s, t), es) :: rest =>
    lo ≤ head ∧ head + 4 ≤ hi ∧ head ≠ 0 ∧
    s ∈ X ∧ t ∈ X ∧
    mem head = locOf X s ∧
    mem (head + 1) = locOf X t ∧
    lo ≤ mem (head + 2) ∧ mem (head + 2) + 1 + es.length ≤ hi ∧
    SeqAt mem (mem (head + 2)) es ∧
    PathListAt mem X lo hi (mem (head + 3)) rest

/-- Tail-tracked singly-linked path chain `(head, tail)` representing `ps`:
* if `ps = []`, `head = 0 ∧ tail = 0`;
* if `ps ≠ []`, `PathListAt mem X lo hi head ps`, `lo ≤ tail`, `tail + 4 ≤ hi`, `tail ≠ 0`,
  `mem (tail + 3) = 0`, and updating `mem (tail + 3)` links directly to any appended chain. -/
def PathChainAt (mem : ℕ → ℕ) (X : Finset ℕ) (lo hi : ℕ) :
    ℕ → ℕ → List ((ℕ × ℕ) × List ℕ) → Prop
  | head, tail, [] => head = 0 ∧ tail = 0
  | head, tail, [p] =>
    head = tail ∧ PathListAt mem X lo hi head [p]
  | head, tail, p :: q :: rest =>
    lo ≤ head ∧ head + 4 ≤ hi ∧ head ≠ 0 ∧
    p.1.1 ∈ X ∧ p.1.2 ∈ X ∧
    mem head = locOf X p.1.1 ∧
    mem (head + 1) = locOf X p.1.2 ∧
    lo ≤ mem (head + 2) ∧ mem (head + 2) + 1 + p.2.length ≤ hi ∧
    SeqAt mem (mem (head + 2)) p.2 ∧
    head ≠ tail ∧
    (∀ addr, addr = tail + 3 → head + 3 ≠ addr) ∧
    PathChainAt mem X lo hi (mem (head + 3)) tail (q :: rest)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 4. Layout Framing Lemmas -/

lemma seqAt_congr {mem mem' : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (h : SeqAt mem a xs)
    (heq : ∀ k, a ≤ k → k < a + 1 + xs.length → mem' k = mem k) :
    SeqAt mem' a xs := by
  refine ⟨?_, ?_⟩
  · rw [heq a le_rfl (by omega)]; exact h.1
  · exact ListAt.congr h.2 (fun k hk1 hk2 => heq k (by omega) (by omega))

lemma seqAt_of_agree_below {mem mem' : ℕ → ℕ} {a bound : ℕ} {xs : List ℕ}
    (h : SeqAt mem a xs) (hb : a + 1 + xs.length ≤ bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    SeqAt mem' a xs :=
  seqAt_congr h (fun k _ hk2 => heq k (by omega))

lemma VertSetAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {X : Finset ℕ}
    (h : VertSetAt mem a X)
    (heq : ∀ k, a ≤ k → k < a + 1 + X.card → mem' k = mem k) :
    VertSetAt mem' a X := by
  rcases h with ⟨xs, hnd, hfin, hseq⟩
  have hlen : xs.length = X.card := by rw [← hfin, List.toFinset_card_of_nodup hnd]
  exact ⟨xs, hnd, hfin, seqAt_congr hseq (fun k hk1 hk2 => heq k hk1 (by omega))⟩

lemma VertSetAt.of_agree_below {mem mem' : ℕ → ℕ} {a bound : ℕ} {X : Finset ℕ}
    (h : VertSetAt mem a X) (hb : a + 1 + X.card ≤ bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    VertSetAt mem' a X :=
  h.congr (fun k _ hk2 => heq k (by omega))

lemma PairsAt.of_agree_below {mem mem' : ℕ → ℕ} {pAddr bound : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)}
    (h : PairsAt mem pAddr pairs) (hb : PairsBounded mem pAddr pairs bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    PairsAt mem' pAddr pairs := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [heq pAddr (by have := hb.1; omega)]; exact h.1
  · have hbi := hb.2 i hi
    dsimp only at hbi
    have hp1 : mem' (pAddr + 1 + 2 * i) = mem (pAddr + 1 + 2 * i) :=
      heq _ (by have := hb.1; omega)
    have hp2 : mem' (pAddr + 2 + 2 * i) = mem (pAddr + 2 + 2 * i) :=
      heq _ (by have := hb.1; omega)
    rw [hp1, hp2]
    exact ⟨(h.2 i hi).1.of_agree_below hbi.1 heq, (h.2 i hi).2.of_agree_below hbi.2 heq⟩

lemma PairsBounded.of_agree_below {mem mem' : ℕ → ℕ} {pAddr bound : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)}
    (hb : PairsBounded mem pAddr pairs bound)
    (heq : ∀ k < bound, mem' k = mem k) :
    PairsBounded mem' pAddr pairs bound := by
  refine ⟨hb.1, fun i hi => ?_⟩
  have hbi := hb.2 i hi
  dsimp only at hbi ⊢
  rw [heq (pAddr + 1 + 2 * i) (by have := hb.1; omega),
      heq (pAddr + 2 + 2 * i) (by have := hb.1; omega)]
  exact hbi

lemma MatchListAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {M : List (ℕ × ℕ)}
    (h : MatchListAt mem a M)
    (heq : ∀ k, a ≤ k → k < a + 1 + 2 * M.length → mem' k = mem k) :
    MatchListAt mem' a M := by
  unfold MatchListAt at h ⊢
  by_cases ha : a = 0
  · simp [ha] at h ⊢; exact h
  · simp only [ha, ↓reduceIte] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [heq a le_rfl (by omega)]; exact h.1
    · exact EdgesAt.congr h.2 (fun k hk1 hk2 => heq k (by omega) (by omega))

lemma NbCsrAt.congr {mem mem' : ℕ → ℕ} {offAddr nbAddr : ℕ} {X : Finset ℕ}
    {adj : ℕ → List (ℕ × ℕ)}
    (h : NbCsrAt mem offAddr nbAddr X adj)
    (hoff : ∀ i ≤ X.card, mem' (offAddr + i) = mem (offAddr + i))
    (hnb : ∀ k < adjCsrOff X adj X.card, mem' (nbAddr + k) = mem (nbAddr + k)) :
    NbCsrAt mem' offAddr nbAddr X adj := by
  refine ⟨fun i hi => by rw [hoff i hi]; exact h.1 i hi, fun i hi j hj => ?_⟩
  have hlt : adjCsrOff X adj i + j < adjCsrOff X adj X.card := by
    have hsucc : adjCsrOff X adj (i + 1) = adjCsrOff X adj i + (adj (origOf X i)).length := by
      simp [adjCsrOff, Finset.sum_range_succ]
    have hmono : adjCsrOff X adj (i + 1) ≤ adjCsrOff X adj X.card := by
      unfold adjCsrOff
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hi))
    omega
  rw [show nbAddr + adjCsrOff X adj i + j = nbAddr + (adjCsrOff X adj i + j) by omega,
    hnb _ hlt, ← show nbAddr + adjCsrOff X adj i + j = nbAddr + (adjCsrOff X adj i + j) by omega]
  exact h.2 i hi j hj

lemma AdjCsrAt.congr {mem mem' : ℕ → ℕ} {offAddr nbAddr edgeAddr : ℕ} {X : Finset ℕ}
    {adj : ℕ → List (ℕ × ℕ)}
    (h : AdjCsrAt mem offAddr nbAddr edgeAddr X adj)
    (hoff : ∀ i ≤ X.card, mem' (offAddr + i) = mem (offAddr + i))
    (hnb : ∀ k < adjCsrOff X adj X.card, mem' (nbAddr + k) = mem (nbAddr + k))
    (hedge : ∀ k < adjCsrOff X adj X.card, mem' (edgeAddr + k) = mem (edgeAddr + k)) :
    AdjCsrAt mem' offAddr nbAddr edgeAddr X adj := by
  refine ⟨h.1.congr hoff hnb, fun i hi j hj => ?_⟩
  have hlt : adjCsrOff X adj i + j < adjCsrOff X adj X.card := by
    have hsucc : adjCsrOff X adj (i + 1) = adjCsrOff X adj i + (adj (origOf X i)).length := by
      simp [adjCsrOff, Finset.sum_range_succ]
    have hmono : adjCsrOff X adj (i + 1) ≤ adjCsrOff X adj X.card := by
      unfold adjCsrOff
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hi))
    omega
  rw [show edgeAddr + adjCsrOff X adj i + j = edgeAddr + (adjCsrOff X adj i + j) by omega,
    hedge _ hlt, ← show edgeAddr + adjCsrOff X adj i + j = edgeAddr + (adjCsrOff X adj i + j) by omega]
  exact h.2 i hi j hj

/-! ## 5. Properties of `sortedX`, `origOf`, `locOf`, and `adjCsrOff` -/

lemma sortedX_length (X : Finset ℕ) : (sortedX X).length = X.card :=
  Finset.length_sort (· ≤ ·)

lemma sortedX_nodup (X : Finset ℕ) : (sortedX X).Nodup :=
  Finset.sort_nodup X (· ≤ ·)

lemma mem_sortedX_iff (X : Finset ℕ) (u : ℕ) : u ∈ sortedX X ↔ u ∈ X :=
  Finset.mem_sort (· ≤ ·)

lemma sortedX_toFinset (X : Finset ℕ) : (sortedX X).toFinset = X := by
  ext u
  simp [mem_sortedX_iff]

lemma sortedX_pairwise_le (X : Finset ℕ) : (sortedX X).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort X (· ≤ ·)

lemma sortedX_pairwise_lt (X : Finset ℕ) : (sortedX X).Pairwise (· < ·) := by
  have hle := sortedX_pairwise_le X
  have hnd := sortedX_nodup X
  have hne : (sortedX X).Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mp hnd
  exact (hle.and hne).imp fun h => Nat.lt_of_le_of_ne h.1 h.2

lemma sortedX_eq_of_pairwise_lt {X : Finset ℕ} {xs : List ℕ}
    (hlt : xs.Pairwise (· < ·)) (hfin : xs.toFinset = X) :
    xs = sortedX X := by
  have hnd : xs.Nodup := List.nodup_iff_pairwise_ne.mpr (hlt.imp fun h => Nat.ne_of_lt h)
  have hperm : xs.Perm (sortedX X) := by
    rw [List.perm_ext_iff_of_nodup hnd (sortedX_nodup X)]
    intro u
    rw [mem_sortedX_iff, ← hfin, List.mem_toFinset]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (hlt.imp Nat.le_of_lt) (sortedX_pairwise_le X)

lemma locOf_lt {X : Finset ℕ} {u : ℕ} (hu : u ∈ X) : locOf X u < X.card := by
  rw [← sortedX_length X]
  exact List.idxOf_lt_length_of_mem ((mem_sortedX_iff X u).mpr hu)

lemma origOf_eq_getElem {X : Finset ℕ} {i : ℕ} (hi : i < X.card) :
    origOf X i = (sortedX X)[i]'(by rw [sortedX_length]; exact hi) := by
  unfold origOf
  exact List.getD_eq_getElem _ 0 (by rw [sortedX_length]; exact hi)

lemma origOf_mem {X : Finset ℕ} {i : ℕ} (hi : i < X.card) : origOf X i ∈ X := by
  rw [origOf_eq_getElem hi, ← mem_sortedX_iff]
  exact List.getElem_mem (by rw [sortedX_length]; exact hi)

lemma origOf_locOf {X : Finset ℕ} {u : ℕ} (hu : u ∈ X) : origOf X (locOf X u) = u :=
  nodup_getD_idxOf ((mem_sortedX_iff X u).mpr hu)

lemma locOf_origOf {X : Finset ℕ} {i : ℕ} (hi : i < X.card) : locOf X (origOf X i) = i :=
  nodup_idxOf_getD (sortedX_nodup X) (by rw [sortedX_length]; exact hi)

lemma origOf_inj {X : Finset ℕ} {i j : ℕ} (hi : i < X.card) (hj : j < X.card)
    (heq : origOf X i = origOf X j) : i = j :=
  nodup_getD_inj (sortedX_nodup X) (by rw [sortedX_length]; exact hi)
    (by rw [sortedX_length]; exact hj) heq

lemma origOf_lt_iff {X : Finset ℕ} {i j : ℕ} (hi : i < X.card) (hj : j < X.card) :
    origOf X i < origOf X j ↔ i < j := by
  rw [origOf_eq_getElem hi, origOf_eq_getElem hj]
  have hpw := List.pairwise_iff_getElem.mp (sortedX_pairwise_lt X)
  constructor
  · intro hlt
    by_contra hge
    have hji : j ≤ i := Nat.le_of_not_lt hge
    rcases Nat.eq_or_lt_of_le hji with rfl | hjlt
    · exact Nat.lt_irrefl _ hlt
    · have := hpw j i (by rw [sortedX_length]; exact hj) (by rw [sortedX_length]; exact hi) hjlt
      omega
  · intro hij
    exact hpw i j (by rw [sortedX_length]; exact hi) (by rw [sortedX_length]; exact hj) hij

lemma locOf_lt_iff {X : Finset ℕ} {u v : ℕ} (hu : u ∈ X) (hv : v ∈ X) :
    locOf X u < locOf X v ↔ u < v := by
  have h := origOf_lt_iff (locOf_lt hu) (locOf_lt hv)
  rw [origOf_locOf hu, origOf_locOf hv] at h
  exact h.symm

lemma map_origOf_eq_sort {X : Finset ℕ} {ls : List ℕ}
    (hlt : ls.Pairwise (· < ·)) (hsub : ∀ i ∈ ls, i < X.card) :
    ls.map (origOf X) = (ls.map (origOf X)).toFinset.sort (· ≤ ·) := by
  have hpw : (ls.map (origOf X)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hlt.imp_of_mem fun ha hb hab => (origOf_lt_iff (hsub _ ha) (hsub _ hb)).mpr hab
  exact sortedX_eq_of_pairwise_lt hpw rfl

lemma adjCsrOff_zero (X : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) :
    adjCsrOff X adj 0 = 0 := by
  simp [adjCsrOff]

lemma adjCsrOff_succ (X : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) (k : ℕ) :
    adjCsrOff X adj (k + 1) = adjCsrOff X adj k + (adj (origOf X k)).length := by
  simp [adjCsrOff, Finset.sum_range_succ]

lemma adjCsrOff_mono (X : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) {i j : ℕ} (hij : i ≤ j) :
    adjCsrOff X adj i ≤ adjCsrOff X adj j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hij)

lemma adjCsrOff_card_eq_sum (X : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) :
    adjCsrOff X adj X.card = ∑ v ∈ X, (adj v).length := by
  unfold adjCsrOff
  have himg : (Finset.range X.card).image (origOf X) = X := by
    have := image_range_getD (sortedX X)
    rw [sortedX_length, sortedX_toFinset] at this
    exact this
  have hinj : Set.InjOn (origOf X) (Finset.range X.card : Set ℕ) :=
    fun i hi j hj hij => origOf_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  conv_rhs => rw [← himg, Finset.sum_image hinj]

lemma adjCsrOff_adjOf_card (G : Graph) (X : Finset ℕ) :
    adjCsrOff X (adjOf G X) X.card = 2 * (G.inside X).length := by
  rw [adjCsrOff_card_eq_sum, sum_adjOf_length]

/-! ## 6. Path Chain Lemmas -/

lemma PathListAt.congr {mem mem' : ℕ → ℕ} {X : Finset ℕ} {lo hi head : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (h : PathListAt mem X lo hi head ps)
    (heq : ∀ k, lo ≤ k → k < hi → mem' k = mem k) :
    PathListAt mem' X lo hi head ps := by
  induction ps generalizing head with
  | nil => exact h
  | cons p rest ih =>
    rcases p with ⟨⟨s, t⟩, es⟩
    rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hrest⟩
    have h0 := heq head hlo (by omega)
    have h1 := heq (head + 1) (by omega) (by omega)
    have h2 := heq (head + 2) (by omega) (by omega)
    have h3 := heq (head + 3) (by omega) (by omega)
    refine ⟨hlo, hhi, hne, hsX, htX, by rw [h0]; exact hm0, by rw [h1]; exact hm1,
      by rw [h2]; exact hwlo, by rw [h2]; exact hwhi, ?_, ?_⟩
    · rw [h2]
      exact seqAt_congr hseq (fun k hk1 hk2 => heq k (by omega) (by omega))
    · rw [h3]
      exact ih hrest

lemma PathListAt.mono_hi {mem : ℕ → ℕ} {X : Finset ℕ} {lo hi hi' head : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (h : PathListAt mem X lo hi head ps) (hle : hi ≤ hi') :
    PathListAt mem X lo hi' head ps := by
  induction ps generalizing head with
  | nil => exact h
  | cons p rest ih =>
    rcases p with ⟨⟨s, t⟩, es⟩
    rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hrest⟩
    exact ⟨hlo, by omega, hne, hsX, htX, hm0, hm1, hwlo, by omega, hseq, ih hrest⟩

lemma PathChainAt.to_pathListAt {mem : ℕ → ℕ} {X : Finset ℕ} {lo hi head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (h : PathChainAt mem X lo hi head tail ps) :
    PathListAt mem X lo hi head ps := by
  induction ps generalizing head with
  | nil => exact h.1
  | cons p rest ih =>
    cases rest with
    | nil => exact h.2
    | cons q rest' =>
      rcases p with ⟨⟨s, t⟩, es⟩
      rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, _, _, hrest⟩
      exact ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, ih hrest⟩

lemma PathChainAt.tail_next_zero {mem : ℕ → ℕ} {X : Finset ℕ} {lo hi head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)} (hne : ps ≠ [])
    (h : PathChainAt mem X lo hi head tail ps) :
    lo ≤ tail ∧ tail + 4 ≤ hi ∧ tail ≠ 0 ∧ mem (tail + 3) = 0 := by
  induction ps generalizing head with
  | nil => exact absurd rfl hne
  | cons p rest ih =>
    cases rest with
    | nil =>
      rcases p with ⟨⟨s, t⟩, es⟩
      rcases h with ⟨rfl, hlo, hhi, h0, _, _, _, _, _, _, _, hnext⟩
      exact ⟨hlo, hhi, h0, hnext⟩
    | cons q rest' =>
      exact ih (List.cons_ne_nil _ _) h.2.2.2.2.2.2.2.2.2.2.2.2

lemma PathChainAt.congr {mem mem' : ℕ → ℕ} {X : Finset ℕ} {lo hi head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (h : PathChainAt mem X lo hi head tail ps)
    (heq : ∀ k, lo ≤ k → k < hi → mem' k = mem k) :
    PathChainAt mem' X lo hi head tail ps := by
  induction ps generalizing head with
  | nil => exact h
  | cons p rest ih =>
    cases rest with
    | nil => exact ⟨h.1, h.2.congr heq⟩
    | cons q rest' =>
      rcases p with ⟨⟨s, t⟩, es⟩
      rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hht, hnd, hrest⟩
      have h0 := heq head hlo (by omega)
      have h1 := heq (head + 1) (by omega) (by omega)
      have h2 := heq (head + 2) (by omega) (by omega)
      have h3 := heq (head + 3) (by omega) (by omega)
      refine ⟨hlo, hhi, hne, hsX, htX, by rw [h0]; exact hm0, by rw [h1]; exact hm1,
        by rw [h2]; exact hwlo, by rw [h2]; exact hwhi, ?_, hht, hnd, ?_⟩
      · rw [h2]
        exact seqAt_congr hseq (fun k hk1 hk2 => heq k (by omega) (by omega))
      · rw [h3]
        exact ih hrest

lemma PathChainAt.mono_lo {mem : ℕ → ℕ} {X : Finset ℕ} {lo lo' hi head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (h : PathChainAt mem X lo hi head tail ps) (hle : lo' ≤ lo) :
    PathChainAt mem X lo' hi head tail ps := by
  induction ps generalizing head with
  | nil => exact h
  | cons p rest ih =>
    cases rest with
    | nil =>
      rcases p with ⟨⟨s, t⟩, es⟩
      rcases h with ⟨rfl, hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hnx⟩
      exact ⟨rfl, by omega, hhi, hne, hsX, htX, hm0, hm1, by omega, hwhi, hseq, hnx⟩
    | cons q rest' =>
      rcases p with ⟨⟨s, t⟩, es⟩
      rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hht, hnd, hrest⟩
      exact ⟨by omega, hhi, hne, hsX, htX, hm0, hm1, by omega, hwhi, hseq, hht, hnd, ih hrest⟩

lemma PathChainAt.mono_hi {mem : ℕ → ℕ} {X : Finset ℕ} {lo hi hi' head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (h : PathChainAt mem X lo hi head tail ps) (hle : hi ≤ hi') :
    PathChainAt mem X lo hi' head tail ps := by
  induction ps generalizing head with
  | nil => exact h
  | cons p rest ih =>
    cases rest with
    | nil => exact ⟨h.1, h.2.mono_hi hle⟩
    | cons q rest' =>
      rcases p with ⟨⟨s, t⟩, es⟩
      rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hht, hnd, hrest⟩
      exact ⟨hlo, by omega, hne, hsX, htX, hm0, hm1, hwlo, by omega, hseq, hht, hnd, ih hrest⟩

/-- Prepending a freshly allocated node at `nd ≥ hi` onto a chain `(head, tail)` in `[lo, hi)`. -/
lemma PathChainAt.prepend_fresh {mem : ℕ → ℕ} {X : Finset ℕ}
    {lo hi hi' nd walkPtr head tail s t : ℕ} {es : List ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (hchain : PathChainAt mem X lo hi head tail ps)
    (hlo_hi : lo ≤ hi) (hnd_ge : hi ≤ nd) (hnd_hi : nd + 4 ≤ hi') (hnd_ne : nd ≠ 0)
    (hsX : s ∈ X) (htX : t ∈ X)
    (hm0 : mem nd = locOf X s) (hm1 : mem (nd + 1) = locOf X t)
    (hm2 : mem (nd + 2) = walkPtr) (hm3 : mem (nd + 3) = head)
    (hwlo : lo ≤ walkPtr) (hwhi : walkPtr + 1 + es.length ≤ hi')
    (hseq : SeqAt mem walkPtr es) :
    PathChainAt mem X lo hi' nd (if head = 0 then nd else tail) (((s, t), es) :: ps) := by
  cases ps with
  | nil =>
    rcases hchain with ⟨rfl, rfl⟩
    simp only [↓reduceIte, PathChainAt, PathListAt]
    refine ⟨trivial, by omega, hnd_hi, hnd_ne, hsX, htX, hm0, hm1,
      by rw [hm2]; exact hwlo, by rw [hm2]; exact hwhi, by rw [hm2]; exact hseq, hm3⟩
  | cons q rest =>
    have hhead_ne : head ≠ 0 := by
      have hpl := hchain.to_pathListAt
      rcases q with ⟨⟨_, _⟩, _⟩
      exact hpl.2.2.1
    have htail_bnd := hchain.tail_next_zero (List.cons_ne_nil _ _)
    simp only [hhead_ne, ↓reduceIte, PathChainAt]
    refine ⟨by omega, hnd_hi, hnd_ne, hsX, htX, hm0, hm1,
      by rw [hm2]; exact hwlo, by rw [hm2]; exact hwhi, by rw [hm2]; exact hseq,
      by omega, fun addr haddr => by omega, ?_⟩
    rw [hm3]
    exact hchain.mono_hi (by omega)

/-- Disjointness of a memory address `addr` from all walk buffers and node words `[head, head+3)`
along a path chain `ps`. -/
def PathWalkDisj (mem : ℕ → ℕ) (addr : ℕ) : ℕ → List ((ℕ × ℕ) × List ℕ) → Prop
  | _, [] => True
  | head, p :: rest =>
    (addr < mem (head + 2) ∨ mem (head + 2) + 1 + p.2.length ≤ addr) ∧
    (addr < head ∨ head + 3 ≤ addr) ∧
    PathWalkDisj mem addr (mem (head + 3)) rest

lemma PathChainAt.link_append {mem : ℕ → ℕ} {X : Finset ℕ}
    {lo mid hi head1 tail1 head2 tail2 : ℕ}
    {ps qs : List ((ℕ × ℕ) × List ℕ)}
    (hps_ne : ps ≠ []) (hqs_ne : qs ≠ [])
    (hlo_mid : lo ≤ mid)
    (hc1 : PathChainAt mem X lo mid head1 tail1 ps)
    (hc2 : PathChainAt mem X mid hi head2 tail2 qs)
    (hdisj : PathWalkDisj mem (tail1 + 3) head1 ps) :
    PathChainAt (Function.update mem (tail1 + 3) head2) X lo hi head1 tail2 (ps ++ qs) := by
  have ht1 := hc1.tail_next_zero hps_ne
  have ht2 := hc2.tail_next_zero hqs_ne
  have hc2' : PathChainAt (Function.update mem (tail1 + 3) head2) X lo hi head2 tail2 qs :=
    (hc2.congr (fun k hk1 _ => Function.update_of_ne (by omega) _ _)).mono_lo hlo_mid
  clear hc2
  induction ps generalizing head1 with
  | nil => exact absurd rfl hps_ne
  | cons p rest ih =>
    rcases p with ⟨⟨s, t⟩, es⟩
    rcases hdisj with ⟨hwdisj, hndisj, hrest_disj⟩
    dsimp only at hwdisj
    cases rest with
    | nil =>
      rcases hc1 with ⟨rfl, hlo, hhi, h0, hs, ht, m0, m1, wl, wh, hseq, _⟩
      cases qs with
      | nil => exact absurd rfl hqs_ne
      | cons q rest' =>
        simp only [List.singleton_append, PathChainAt]
        have hne0 : head1 ≠ head1 + 3 := by omega
        have hne1 : head1 + 1 ≠ head1 + 3 := by omega
        have hne2 : head1 + 2 ≠ head1 + 3 := by omega
        have hm2' : Function.update mem (head1 + 3) head2 (head1 + 2) = mem (head1 + 2) :=
          Function.update_of_ne hne2 _ _
        refine ⟨hlo, by omega, h0, hs, ht,
          by rw [Function.update_of_ne hne0]; exact m0,
          by rw [Function.update_of_ne hne1]; exact m1,
          by rw [hm2']; exact wl,
          by rw [hm2']; omega, ?_, by omega, fun addr haddr => by omega, ?_⟩
        · rw [hm2']
          exact seqAt_congr hseq (fun k hk1 hk2 => Function.update_of_ne (by omega) _ _)
        · rw [Function.update_self]
          exact hc2'
    | cons p2 rest' =>
      rcases hc1 with ⟨hlo, hhi, h0, hs, ht, m0, m1, wl, wh, hseq, hht, hnd, hrest⟩
      dsimp only at wl wh hseq
      have hne0 : head1 ≠ tail1 + 3 := by omega
      have hne1 : head1 + 1 ≠ tail1 + 3 := by omega
      have hne2 : head1 + 2 ≠ tail1 + 3 := by omega
      have hne3 : head1 + 3 ≠ tail1 + 3 := hnd (tail1 + 3) rfl
      have hm2' : Function.update mem (tail1 + 3) head2 (head1 + 2) = mem (head1 + 2) :=
        Function.update_of_ne hne2 _ _
      simp only [List.cons_append, PathChainAt]
      refine ⟨hlo, by omega, h0, hs, ht,
        by rw [Function.update_of_ne hne0]; exact m0,
        by rw [Function.update_of_ne hne1]; exact m1,
        by rw [hm2']; exact wl,
        by rw [hm2']; omega, ?_, by omega, fun addr haddr => by omega, ?_⟩
      · rw [hm2']
        exact seqAt_congr hseq (fun k hk1 hk2 => Function.update_of_ne (by omega) _ _)
      · rw [Function.update_of_ne hne3]
        exact ih (List.cons_ne_nil _ _) hrest hrest_disj

end MinCostFlow.ExpanderDecomp
