module

public import MinCostFlow.LowStretch.ClArcs
public import MinCostFlow.LowStretch.KReset
public import MinCostFlow.LowStretch.ProgCSR
public import MinCostFlow.LowStretch.ProgLca
public import MinCostFlow.LowStretch.ProgLog

/-!
# The contract of the child step

After the petals of a cluster `c`, the *child step* builds the records of its children, so that
the cluster procedure can recurse on them. This file states what the child step must do
(`MeetsChild`). It holds no proof about a program.

**What the child step reads** (`ChildPre`). Three blocks of words, at the addresses `GB`, `RB`
and `XB`, and a heap pointer `h`.
* The global block `GlobL`: the input arrays (ends, weights and exponents of the pairs), the
  labels `LAB` and the local indices `LOC`, the arrays of the merge tree (parents, children,
  weights, leaf counts, leaf order, heads) and the pairs grouped by their lowest common node, as
  `csrB` leaves them after `lcaAll`. `GlobL.Ok` says what they hold.
* The record block `RecL` of `c`: what `Rec.Mem` reads, the list of its super-vertices, its center
  and target, and its stored highway (four words per pair). `RecAt` says what they hold.
* The block `PetL` of the petal loop: the number of petals, the nodes of each petal (its settled
  list), the marks of the carved nodes (`OK[u] = os` exactly for the nodes of the stem, as
  `pfin` leaves them), the target and the center of each raw child, the tree of the first run of
  Dijkstra (with the stored highway written over it, as `hwFix` leaves it), the active pairs of
  `c` (as `actP` leaves them) and the radius `Δ`. `PetL.Ok` says what they hold, for a
  decomposition step `D` that meets `DecOk`. The highway of each raw child is the path of the
  tree from its target to its center (`PetL.Ok.walk`).

**What the child step leaves** (`ChildPost`). For each child `k`, a record block at `h + 9k`,
for a cluster `cs k` with `Next G P (c.raw G D k) (cs k)`, that meets `Rec.Ok` and `RecAt`. The
heap grows from `h` to the returned value. Below `h`, only the labels of the vertices of `c` and
the local indices of the labels of its nodes change (`ChildWr`). The cost is `childCost`: a
`log J` factor per active pair and per node of `c`, a term `J` and a logarithm per child, and for
each node of the merge tree that a reset splits, the leaves of its light child and the pairs
grouped at it (`KT.visW`). Each node is split at most once along a run, so these last terms add
up to a global term.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The stored highway -/

namespace Cl

/-- The stored form of a highway `hw` from `t` with threshold `θ` and halved pairs `half`: for
each pair of `hw` that is not light, the pair, its half flag, its end at the side of `t`, and its
other end. -/
def hwE (G : PG) (t : ℕ) (hw : List ℕ) (θ : ℕ) (half : Finset ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  ((List.range hw.length).filter (fun m => θ ≤ G.pω (hw.getD m 0))).map
    (fun m => (hw.getD m 0, if hw.getD m 0 ∈ half then 1 else 0, hv G t hw m, hv G t hw (m + 1)))

/-- The pairs of the stored highway are the pairs of the highway that are not light. -/
theorem hwE_fst (G : PG) (t : ℕ) (hw : List ℕ) (θ : ℕ) (half : Finset ℕ) :
    (hwE G t hw θ half).map Prod.fst = hw.filter (fun p => θ ≤ G.pω p) := by
  have e : (List.range hw.length).map (fun m => hw.getD m 0) = hw := by
    apply List.ext_getElem (by simp)
    intro i _ h2
    simp [List.getElem?_eq_getElem h2]
  unfold hwE
  rw [List.map_map]
  conv_rhs => rw [← e]
  rw [List.filter_map]
  rfl

end Cl

/-! ### The global block -/

/-- The global arrays and numbers, as a block of `21` words. -/
structure GlobL where
  n : ℕ
  m : ℕ
  N : ℕ
  IN : ℕ
  PW : ℕ
  EXP : ℕ
  LAB : ℕ
  LOC : ℕ
  KPAR : ℕ
  KCH1 : ℕ
  KCH2 : ℕ
  KMW : ℕ
  KSZ : ℕ
  KLO : ℕ
  HEAD : ℕ
  ORDL : ℕ
  GOFF : ℕ
  GPR : ℕ
  B : ℕ
  J : ℕ
  INF : ℕ

/-- The global block at address `a`. -/
def GlobL.read (mem : ℕ → ℕ) (a : ℕ) : GlobL :=
  ⟨mem a, mem (a + 1), mem (a + 2), mem (a + 3), mem (a + 4), mem (a + 5), mem (a + 6),
    mem (a + 7), mem (a + 8), mem (a + 9), mem (a + 10), mem (a + 11), mem (a + 12),
    mem (a + 13), mem (a + 14), mem (a + 15), mem (a + 16), mem (a + 17), mem (a + 18),
    mem (a + 19), mem (a + 20)⟩

/-- What the global arrays hold. The merge tree `T` is in memory (parents, children, weights,
leaf counts, starts of the leaf intervals, heads, leaf order), as `krP` and `koP` leave it. The
pairs are grouped by their lowest common node `lf p`, as `csrB` leaves them: the pairs with
lowest common node `u` are at `GPR + GOFF[u]`, …, `GPR + GOFF[u + 1] - 1`. Every pair weighs at
least `8 B n`, the classes of Dijkstra fit below `J` (`128 B n² < 2 ^ J`), and `INF` exceeds
every distance. The labels `LAB` and the local indices `LOC` are not stated here: each record
states the cells it uses (`RecAt`). -/
structure GlobL.Ok (E : GlobL) (T : KT) (G : PG) (P : Par) (mem : ℕ → ℕ) : Prop where
  n : E.n = G.n
  m : E.m = G.m
  N : E.N = T.N
  B : E.B = P.B
  tree : T.Ok G
  hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n
  hGo : G.Ok
  par : ∀ k < T.N, mem (E.KPAR + k) = T.par k
  ch : ∀ k, G.n ≤ k → k < T.N → mem (E.KCH1 + k) = T.ch1 k ∧ mem (E.KCH2 + k) = T.ch2 k
  mw : ∀ k < T.N, mem (E.KMW + k) = T.mw k
  sz : ∀ k < T.N, mem (E.KSZ + k) = T.sz G k
  lo : ∀ k < T.N, mem (E.KLO + k) = T.lo G k
  hd : ∀ k < T.N, mem (E.HEAD + k) = T.hd G k
  ordl : ∀ v < G.n, mem (E.ORDL + T.lo G v) = v
  ends : ∀ p < G.m, mem (E.IN + 3 * p) = G.pu p ∧ mem (E.IN + 3 * p + 1) = G.pv p
  pw : ∀ p < G.m, mem (E.PW + p) = G.pω p
  ex : ∀ p < G.m, G.pω p = 2 ^ mem (E.EXP + p)
  lca : ∃ lf : ℕ → ℕ, (∀ p < G.m, T.IsLca (G.pu p) (G.pv p) (lf p)) ∧
    (∀ u ≤ T.N, mem (E.GOFF + u) = offOf lf G.m u) ∧
    ∀ u < T.N, ∀ j < (grp lf G.m u).length,
      mem (E.GPR + offOf lf G.m u + j) = (grp lf G.m u).getD j 0
  heavy : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p
  hB : 1 ≤ P.B
  hJ : 128 * P.B * G.n ^ 2 < 2 ^ E.J
  hINF : ∀ p < G.m, 2 * G.n * G.pω p < E.INF

/-! ### The record block -/

/-- Where the record of a cluster lies, as a block of `9` words: the number `s` of super-vertices,
the number `nS` of stored pairs and their array `SA` (two words each), the exponent `lθ` of the
threshold, the array `NA` of the super-vertices (Kruskal nodes), the center `x0` and the target `t` (as
vertices; their local indices are read as `LOC[LAB[v]]`), and the stored highway: `nH` entries of four words at `HW`. -/
structure RecL where
  s : ℕ
  nS : ℕ
  SA : ℕ
  lθ : ℕ
  NA : ℕ
  x0 : ℕ
  t : ℕ
  nH : ℕ
  HW : ℕ

/-- The record block at address `a`. -/
def RecL.read (mem : ℕ → ℕ) (a : ℕ) : RecL :=
  ⟨mem a, mem (a + 1), mem (a + 2), mem (a + 3), mem (a + 4), mem (a + 5), mem (a + 6),
    mem (a + 7), mem (a + 8)⟩

/-- The layout that `arcFill` reads (`Rec.Mem`), for the record `L` and the global block `E`.
The scratch fields are `0`; `Rec.Mem` does not read them. -/
def RecL.af (L : RecL) (E : GlobL) : AF :=
  ⟨L.s, L.nS, L.SA, E.IN, E.PW, E.EXP, E.LAB, E.LOC, 0, L.lθ, 0, 0, 0, 0⟩

/-- The memory regions of a record, as pairs (start, length). -/
def RecL.regs (L : RecL) : List (ℕ × ℕ) := [(L.SA, 2 * L.nS), (L.NA, L.s), (L.HW, 4 * L.nH)]

/-- **The record `R` of the cluster `c` is in memory at the layout `L`.** The arrays that
`arcFill` reads hold it (`Rec.Mem`), the super-vertices are at `NA`, the center and target are
given as vertices, the stored highway is `hwE` of the highway of `c`, and the label of
each vertex of `c` is the head of its `θ`-node. -/
structure RecAt (T : KT) (G : PG) (c : Cl) (R : Rec) (E : GlobL) (L : RecL) (mem : ℕ → ℕ) :
    Prop where
  arcs : Rec.Mem T G c R (L.af E) mem
  nodes : ∀ i < R.nodes.length, mem (L.NA + i) = R.nodes.getD i 0
  x0 : L.x0 = c.x0
  t : L.t = c.t
  nH : L.nH = (Cl.hwE G c.t c.hw c.θ c.half).length
  hw : ∀ j < L.nH, mem (L.HW + 4 * j) = ((Cl.hwE G c.t c.hw c.θ c.half).getD j (0, 0, 0, 0)).1 ∧
    mem (L.HW + 4 * j + 1) = ((Cl.hwE G c.t c.hw c.θ c.half).getD j (0, 0, 0, 0)).2.1 ∧
    mem (L.HW + 4 * j + 2) = ((Cl.hwE G c.t c.hw c.θ c.half).getD j (0, 0, 0, 0)).2.2.1 ∧
    mem (L.HW + 4 * j + 3) = ((Cl.hwE G c.t c.hw c.θ c.half).getD j (0, 0, 0, 0)).2.2.2
  lab : ∀ v ∈ c.X, mem (E.LAB + v) = T.hd G (T.top c.θ v)

/-! ### The block of the petal loop -/

/-- What the petal loop leaves, as a block of `16` words: the number `nP` of petals, the flag
`sp` of the special petal, the settled lists of the petals (petal `k` is
`PL[PO[k]], …, PL[PO[k + 1] - 1]`), the marks `OK` with the stamp `os`, the targets `CT` and
centers `CC` of the raw children (vertices), the tree arrays of the first run (`PAR`, and
for each node the pair `PP` of its parent arc, its flag `PF`, its end `PA` in the node and its
other end `PB`), the `nA` active pairs at `ACT` (pair and flag), and the radius `Dc`. -/
structure PetL where
  nP : ℕ
  sp : ℕ
  PL : ℕ
  PO : ℕ
  OK : ℕ
  os : ℕ
  CT : ℕ
  CC : ℕ
  PAR : ℕ
  PP : ℕ
  PF : ℕ
  PA : ℕ
  PB : ℕ
  nA : ℕ
  ACT : ℕ
  Dc : ℕ

/-- The petal block at address `a`. -/
def PetL.read (mem : ℕ → ℕ) (a : ℕ) : PetL :=
  ⟨mem a, mem (a + 1), mem (a + 2), mem (a + 3), mem (a + 4), mem (a + 5), mem (a + 6),
    mem (a + 7), mem (a + 8), mem (a + 9), mem (a + 10), mem (a + 11), mem (a + 12),
    mem (a + 13), mem (a + 14), mem (a + 15)⟩

/-- The first `ℓ` nodes of the path of the parent array `PAR` from `u`. -/
def parWalk (mem : ℕ → ℕ) (PAR : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | u, ℓ + 1 => u :: parWalk mem PAR (mem (PAR + u)) ℓ

/-- The node reached after `ℓ` steps of the parent array `PAR` from `u`. -/
def parEnd (mem : ℕ → ℕ) (PAR : ℕ) (u ℓ : ℕ) : ℕ := (fun v => mem (PAR + v))^[ℓ] u

namespace PetL

variable (X : PetL) (mem : ℕ → ℕ)

/-- The stored form of the parent arc of node `u`: pair, flag, end in `u`, other end. -/
def ent (u : ℕ) : ℕ × ℕ × ℕ × ℕ := (mem (X.PP + u), mem (X.PF + u), mem (X.PA + u), mem (X.PB + u))

/-- The settled list of petal `k`. -/
def nodesOf (k : ℕ) : List ℕ :=
  (List.range (mem (X.PO + (k + 1)) - mem (X.PO + k))).map (fun j => mem (X.PL + mem (X.PO + k) + j))

/-- The active pairs, in order. -/
def actL : List ℕ := (List.range X.nA).map (fun i => mem (X.ACT + 2 * i))

/-- The memory regions of the petal block, as pairs (start, length). -/
def regs (s : ℕ) : List (ℕ × ℕ) :=
  [(X.PL, mem (X.PO + X.nP)), (X.PO, X.nP + 1), (X.OK, s), (X.CT, X.nP + 1), (X.CC, X.nP + 1),
    (X.PAR, s), (X.PP, s), (X.PF, s), (X.PA, s), (X.PB, s), (X.ACT, 2 * X.nA)]

end PetL

/-- **What the petal loop leaves**, for the cluster `c` with record `R` and the decomposition
step `D`.
* `nodes`: the settled list of petal `k` lists the local indices of the petal `W k`, once each.
* `ok`: a node is marked `os` exactly when it lies in the stem.
* `ct`, `cc`: the target and center of each raw child.
* `walk`: the path of the tree from the target of raw child `k` has the stored highway of the
  child as its parent arcs (with the flags of `c`), each node of the path is the node of the end
  of its arc, the path stops at the first visit of the center, and it visits each node once.
* `act`: the active pairs of `c`, once each, with their flags.
* `Dc`: the radius of `c`. -/
structure PetL.Ok (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (D : Cl.Dec) (X : PetL)
    (mem : ℕ → ℕ) : Prop where
  nP : X.nP = D.ps.length
  sp : X.sp = if D.sp then 1 else 0
  po : ∀ k < X.nP, mem (X.PO + k) ≤ mem (X.PO + (k + 1))
  po0 : ∀ k ≤ X.nP, mem (X.PO + k) ≤ mem (X.PO + X.nP)
  nodup : ∀ k < X.nP, (X.nodesOf mem k).Nodup
  nodes : ∀ k < X.nP, ∀ u, u ∈ X.nodesOf mem k ↔ ∃ v ∈ c.W G D k, R.sv T c v = u
  ok : ∀ u < R.nodes.length, mem (X.OK + u) = X.os ↔ ∃ v ∈ c.stem G D, R.sv T c v = u
  ct : ∀ k < D.nch, mem (X.CT + k) = (c.raw G D k).t
  cc : ∀ k < D.nch, mem (X.CC + k) = (c.raw G D k).x0
  walk : ∀ k < D.nch,
    (parWalk mem X.PAR (R.sv T c (mem (X.CT + k)))
      (Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half).length).map (X.ent mem) =
        Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half ∧
    (∀ u ∈ parWalk mem X.PAR (R.sv T c (mem (X.CT + k)))
        (Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half).length,
      u = R.sv T c (mem (X.PA + u))) ∧
    parEnd mem X.PAR (R.sv T c (mem (X.CT + k)))
        (Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half).length =
      R.sv T c (mem (X.CC + k)) ∧
    R.sv T c (mem (X.CC + k)) ∉ parWalk mem X.PAR (R.sv T c (mem (X.CT + k)))
        (Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half).length ∧
    (parWalk mem X.PAR (R.sv T c (mem (X.CT + k)))
        (Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half).length).Nodup
  act_nodup : (X.actL mem).Nodup
  act : ∀ p, p ∈ X.actL mem ↔ p ∈ c.act G P
  act_fl : ∀ i < X.nA, mem (X.ACT + 2 * i + 1) = if mem (X.ACT + 2 * i) ∈ c.half then 1 else 0
  Dc : X.Dc = c.Δ G

/-! ### Regions -/

/-- Two regions (start, length) do not overlap. -/
def RegDisj (a b : ℕ × ℕ) : Prop := a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

/-- The regions that the child step reads: the three blocks and the arrays they name. -/
def readRegs (GB RB XB : ℕ) (E : GlobL) (L : RecL) (X : PetL) (mem : ℕ → ℕ) : List (ℕ × ℕ) :=
  [(GB, 21), (RB, 9), (XB, 16), (E.IN, 3 * E.m), (E.PW, E.m), (E.EXP, E.m), (E.KPAR, E.N),
    (E.KCH1, E.N), (E.KCH2, E.N), (E.KMW, E.N), (E.KSZ, E.N), (E.KLO, E.N), (E.HEAD, E.N),
    (E.ORDL, E.n), (E.GOFF, E.N + 1), (E.GPR, E.m)] ++ L.regs ++ X.regs mem L.s

/-- The cells below the heap that the child step may write: the labels of the vertices of `c`,
and the local indices of the heads of the nodes below the `θ`-nodes of `c`. -/
def ChildWr (T : KT) (G : PG) (c : Cl) (E : GlobL) (a : ℕ) : Prop :=
  (∃ v ∈ c.X, a = E.LAB + v) ∨
    ∃ v ∈ c.X, ∃ k, T.Under v k ∧ T.Under k (T.top c.θ v) ∧ a = E.LOC + T.hd G k

/-! ### The precondition -/

/-- **The precondition of the child step**, with the arguments `[GB, RB, XB, h]`. The cluster `c`
has at least two vertices and its record `R` meets `Rec.Ok`; `D` is a decomposition step of `c`
that meets `DecOk`; the three blocks hold what `GlobL.Ok`, `RecAt` and `PetL.Ok` say; the memory
from `h` on is zero; the regions read lie below `h` and do not meet the labels and the local
indices; the words are large enough; every label is a node, and every local index cell holds a
word (the arc builder `arcP` reads `LOC[LAB[v]]` and asks this of all vertices). -/
structure ChildPre (w : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (D : Cl.Dec)
    (GB RB XB h : ℕ) (mem : ℕ → ℕ) : Prop where
  two : 2 ≤ c.X.card
  ok : R.Ok T G P c
  dec : c.DecOk G P D
  glob : (GlobL.read mem GB).Ok T G P mem
  recAt : RecAt T G c R (GlobL.read mem GB) (RecL.read mem RB) mem
  pet : (PetL.read mem XB).Ok T G P c R D mem
  zero : ZeroFrom mem h
  below : ∀ r ∈ readRegs GB RB XB (GlobL.read mem GB) (RecL.read mem RB) (PetL.read mem XB) mem,
    r.1 + r.2 ≤ h
  lab_below : (GlobL.read mem GB).LAB + G.n ≤ h
  loc_below : (GlobL.read mem GB).LOC + T.N ≤ h
  lab_loc : RegDisj ((GlobL.read mem GB).LAB, G.n) ((GlobL.read mem GB).LOC, T.N)
  lab_disj : ∀ r ∈ readRegs GB RB XB (GlobL.read mem GB) (RecL.read mem RB) (PetL.read mem XB) mem,
    RegDisj r ((GlobL.read mem GB).LAB, G.n)
  loc_disj : ∀ r ∈ readRegs GB RB XB (GlobL.read mem GB) (RecL.read mem RB) (PetL.read mem XB) mem,
    RegDisj r ((GlobL.read mem GB).LOC, T.N)
  room : ∃ Mw, (∀ p < G.m, G.pω p ≤ Mw) ∧ (GlobL.read mem GB).INF ≤ 4 * G.n * Mw + 4 ∧
    h + 2 ^ (2 * (GlobL.read mem GB).J + 20) * (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 < 2 ^ w
  lab_lt : ∀ v < G.n, mem ((GlobL.read mem GB).LAB + v) < T.N
  loc_w : ∀ x < T.N, mem ((GlobL.read mem GB).LOC + x) < 2 ^ w

/-! ### The cost -/

open Classical in
/-- The nodes of the merge tree that the child `r` splits when its threshold becomes `x`: the
nodes made by a merge, of weight at least `x`, below a `θ`-node of `r`. When `x = r.θ` there are
none. -/
noncomputable def KT.splitSet (T : KT) (G : PG) (r : Cl) (x : ℕ) : Finset ℕ :=
  (Finset.range T.N).filter fun u =>
    G.n ≤ u ∧ x ≤ T.mw u ∧ ∃ v ∈ r.X, T.Under v u ∧ T.Under u (T.top r.θ v)

open Classical in
/-- The number of pairs whose lowest common node is `u`. -/
noncomputable def KT.nLca (T : KT) (G : PG) (u : ℕ) : ℕ :=
  ((Finset.range G.m).filter fun p => T.IsLca (G.pu p) (G.pv p) u).card

/-- The work of the splits of a reset: for each split node, the leaves of its light child (whose
labels change), the pairs grouped at it (which become visible), and one. -/
noncomputable def KT.visW (T : KT) (G : PG) (r : Cl) (x : ℕ) : ℕ :=
  ∑ u ∈ T.splitSet G r x, (T.sz G (T.light G u) + T.nLca G u + 1)

/-- The number `S = max(Δ, μ, 4 B |X|)` of the reset rule (`Cl.next_reset`), for a child `r`
whose `θ`-nodes have largest weight `μ`. -/
noncomputable def Cl.resetS (T : KT) (G : PG) (P : Par) (r : Cl) : ℕ :=
  max (max (r.Δ G) (r.X.sup fun a => T.mw (T.top r.θ a))) (4 * P.B * r.X.card)

/-- **The cost of the child step**: `O(log J)` for each active pair and each node of `c`, and for
each child `O(J)`, the logarithm of the reset rule, and the work of its splits. -/
noncomputable def childCost (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (D : Cl.Dec)
    (cs : ℕ → Cl) (J : ℕ) : ℕ :=
  100000 * (Nat.log 2 J + 2) * ((c.act G P).card + R.nodes.length + 1) +
    ∑ k ∈ Finset.range D.nch, (10000 * (J + 1) + log2Cost (Cl.resetS T G P (c.raw G D k) /
      (4 * P.B * (c.raw G D k).X.card)) + 10000 * T.visW G (c.raw G D k) (cs k).θ)

/-! ### The postcondition and the contract -/

/-- **The postcondition of the child step**, started at the memory `mem` with heap pointer `h`,
ending with the value `v` and the memory `mem'`, at cost `cost`. There are children `cs` that
follow `Next` from the raw children of `D`, with records `Rs`. The record block of child `k` is at
`h + 9k`; it meets `Rec.Ok` and `RecAt`, and its arrays lie in `[h + 9 nch, v)`. The memory from
`v` on is zero, and below `h` only the cells of `ChildWr` change. The cost is at most `childCost`
and the heap used at most `J + 1` times as much: the class queues of Dijkstra on a raw child take
`J` cells per pushed entry. The new labels are nodes and the new local indices are below `T.N`,
so that the facts `lab_lt` and `loc_w` of `ChildPre` stay true. The children store at most
the active pairs of `c` and the pairs made visible by their resets (`visW`). -/
def ChildPost (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (D : Cl.Dec) (E : GlobL) (h : ℕ)
    (mem : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) (cost : ℕ) : Prop :=
  ∃ cs : ℕ → Cl, ∃ Rs : ℕ → Rec,
    (∀ k < D.nch, Next G P (c.raw G D k) (cs k) ∧ (Rs k).Ok T G P (cs k) ∧
      RecAt T G (cs k) (Rs k) E (RecL.read mem' (h + 9 * k)) mem' ∧
      ∀ r ∈ (RecL.read mem' (h + 9 * k)).regs, h + 9 * D.nch ≤ r.1 ∧ r.1 + r.2 ≤ v) ∧
    h + 9 * D.nch ≤ v ∧ ZeroFrom mem' v ∧
    (∀ a < h, ¬ ChildWr T G c E a → mem' a = mem a) ∧
    v ≤ h + (E.J + 1) * childCost T G P c R D cs E.J ∧ cost ≤ childCost T G P c R D cs E.J ∧
    (∀ x < G.n, mem (E.LAB + x) < T.N → mem' (E.LAB + x) < T.N) ∧
    (∀ x < T.N, mem' (E.LOC + x) = mem (E.LOC + x) ∨ mem' (E.LOC + x) < T.N) ∧
    ∑ k ∈ Finset.range D.nch, (Rs k).S.length ≤
      (c.act G P).card + ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ

/-- **The contract of the child step.** Procedure `f` of `p`, called with `[GB, RB, XB, h]` on a
memory that meets `ChildPre`, ends as `ChildPost` says, for every sequence of random bits. The
cost may depend on the children it builds, so this is stated with `Runs` rather than with a
`Contract`; a caller uses it through `runs_call_iff`. -/
def MeetsChild (w : ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (D : Cl.Dec) (GB RB XB h : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool), ChildPre w T G P c R D GB RB XB h mem →
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' cost,
      Runs w p ω body (startState [GB, RB, XB, h] mem pos) o st' cost ∧
      ChildPost T G P c R D (GlobL.read mem GB) h mem o.value st'.mem cost

end MinCostFlow.LowStretch
