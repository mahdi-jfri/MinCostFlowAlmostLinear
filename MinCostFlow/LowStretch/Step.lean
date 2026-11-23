module

public import MinCostFlow.LowStretch.Excess
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# One step of the petal decomposition

This file states what a correct step of the decomposition is. It does not say how to find one.
The program makes its own choices, and we only check that they meet the rules below. The
structural claims, the tree, the radius and the stretch bound are then proved for every run that
follows the rules, and the existence of a run is a separate question.

A step takes a cluster `c` with radius `Δ`. If the target is far (`8 d(x0, t) > 5Δ`), it first
carves a *special petal* around the target, using the highway of `c`. Then, while some vertex
`z` that is left has `4 d(x0, z) > 3Δ`, it picks such a vertex as a target, a shortest walk from
it to the center as its highway, and carves a *regular petal* around it. What is left is the
*stem*. Each petal has a radius `r` in a range of width `Δ/8`, chosen by region growing, and a
portal: the pair of its highway where the highway first leaves the petal.

Region growing works with *active* pairs only (`Cl.Active`). The volume of a petal is `κ` plus
the volume weight `cw` of its active pairs, plus a fraction of each active pair that leaves it. The
cost of a petal is the sum of `cw/ω` over the active pairs that leave it. The range is split into
`L` buckets. Bucket `q` has the level `λ_q = 2^(L - q)`, and the petal must satisfy
`cost · s_q ≤ 8 · vol` and `vol ≤ T_q`, where `s_q` is the bucket width divided by
`λ_(q-1) + 3`, and `T_q = 4 V / 2^(λ_q) + κ` for the volume `V` of the cluster.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The fixed numbers of the construction. -/
structure Par where
  /-- The volume weight of each pair. -/
  cw : ℕ → ℕ
  /-- The volume of an empty petal. -/
  κ : ℕ
  /-- The number of buckets of a range. -/
  L : ℕ
  /-- A child keeps the threshold of its parent when its radius is at least `B · |X| · θ`. -/
  B : ℕ
  /-- The constant of `Cl.Active`. -/
  Q : ℕ

/-- A petal: its target, its highway (a shortest walk from the target to the center of the
cluster), its radius, and the index of its portal on the highway. -/
structure PD where
  /-- The target. -/
  tj : ℕ
  /-- The highway. -/
  hw : List ℕ
  /-- The radius. -/
  r : ℕ
  /-- The portal is pair number `i` of the highway. -/
  i : ℕ
  deriving Inhabited

namespace Cl

variable (G : PG) (P : Par) (c : Cl)

open Classical in
/-- The petal of `pd` carved from `Y`, as a finite set. -/
noncomputable def carve (Y : Finset ℕ) (pd : PD) : Finset ℕ :=
  Y.filter (· ∈ c.Petal G pd.tj pd.hw ↑Y pd.r)

/-- The cost of reaching `v` from the target, inside `Y`. -/
noncomputable def ent (Y : Finset ℕ) (pd : PD) (v : ℕ) : ℕ :=
  sInf {k | c.DR G pd.tj pd.hw ↑Y v k}

open Classical in
/-- The active pairs. -/
noncomputable def act : Finset ℕ := (Finset.range G.m).filter (c.Active G P.Q ·)

/-- The volume of the cluster: `κ` plus the volume weight of its active pairs. -/
noncomputable def V : ℝ := P.κ + ∑ p ∈ c.act G P, (P.cw p : ℝ)

/-- The end of pair `p` that lies in `W` (the first end if both or none do). -/
def inEnd (W : Finset ℕ) (p : ℕ) : ℕ := if G.pu p ∈ W then G.pu p else G.pv p

open Classical in
/-- Pair `p` has both ends in `W`. -/
def Inside (W : Finset ℕ) (p : ℕ) : Prop := G.pu p ∈ W ∧ G.pv p ∈ W

/-- Pair `p` leaves `W` inside `Y`: one end in `W`, the other in `Y` but not in `W`. -/
def Leaves (Y W : Finset ℕ) (p : ℕ) : Prop :=
  G.pu p ∈ W ∧ G.pv p ∈ Y \ W ∨ G.pv p ∈ W ∧ G.pu p ∈ Y \ W

open Classical in
/-- The volume of the petal of `pd` carved from `Y`. -/
noncomputable def vol (Y : Finset ℕ) (pd : PD) : ℝ :=
  let W := c.carve G Y pd
  P.κ + ∑ p ∈ (c.act G P).filter (Inside G W ·), (P.cw p : ℝ) +
    ∑ p ∈ (c.act G P).filter (Leaves G Y W ·),
      (P.cw p : ℝ) * ((pd.r - c.ent G Y pd (inEnd G W p) : ℕ) : ℝ) / (8 * G.pω p)

open Classical in
/-- The cost of the petal of `pd` carved from `Y`. -/
noncomputable def cost (Y : Finset ℕ) (pd : PD) : ℝ :=
  let W := c.carve G Y pd
  ∑ p ∈ (c.act G P).filter (Leaves G Y W ·), (P.cw p : ℝ) / G.pω p

/-- The width of a bucket. -/
noncomputable def bw : ℕ := c.Δ G / 8 / P.L

/-- The level of bucket `q`. -/
def lam (q : ℕ) : ℕ := 2 ^ (P.L - q)

/-- The slack of bucket `q`. -/
noncomputable def sq (q : ℕ) : ℕ := c.bw G P / (lam P (q - 1) + 3)

/-- The volume bound of bucket `q`. -/
noncomputable def T (q : ℕ) : ℝ := 4 * c.V G P / 2 ^ lam P q + P.κ

/-- The rules for a petal of `pd` carved from `Y`, with range starting at `lo`. The highway is a
shortest walk in `X`, the portal is where it first leaves the petal, and the radius lies in some
bucket `q` and meets the two tests of region growing. -/
def PetalOk (Y : Finset ℕ) (lo : ℕ) (pd : PD) : Prop :=
  pd.tj ∈ Y ∧ c.IsHighway G pd.tj pd.hw ∧ pd.i < pd.hw.length ∧
    (∀ k ≤ pd.i, hv G pd.tj pd.hw k ∈ c.carve G Y pd) ∧
    hv G pd.tj pd.hw (pd.i + 1) ∉ c.carve G Y pd ∧
    ∃ q, 1 ≤ q ∧ q ≤ P.L ∧ lo + (q - 1) * c.bw G P ≤ pd.r ∧ pd.r ≤ lo + q * c.bw G P ∧
      c.cost G P Y pd * c.sq G P q ≤ 8 * c.vol G P Y pd ∧ c.vol G P Y pd ≤ c.T G P q

/-- A decomposition step: the petals in the order they are carved. When `sp` holds, the first
one is the special petal. -/
structure Dec where
  /-- There is a special petal. -/
  sp : Bool
  /-- The petals. -/
  ps : List PD

/-- The start of the range of the special petal: `d(x0, t) - ⌈Δ/2⌉ - Δ/8`. -/
noncomputable def loS : ℕ := c.d G c.x0 c.t - (c.Δ G + 1) / 2 - c.Δ G / 8

/-- Petal number `k`. -/
def Dec.pd (D : Dec) (k : ℕ) : PD := D.ps.getD k default

/-- What is left before petal number `k` is carved. -/
noncomputable def Z (D : Dec) : ℕ → Finset ℕ
  | 0 => c.X
  | k + 1 => Z D k \ c.carve G (Z D k) (D.pd k)

/-- Petal number `k`, as a set. -/
noncomputable def W (D : Dec) (k : ℕ) : Finset ℕ := c.carve G (c.Z G D k) (D.pd k)

/-- The stem: what is left after all petals. -/
noncomputable def stem (D : Dec) : Finset ℕ := c.Z G D D.ps.length

/-- The rules for a decomposition step. There is a special petal exactly when the target is far.
Its target and highway are those of the cluster, and its range starts at `loS`. Every other petal
has a far target and range `[0, Δ/8]`. Every vertex of the stem is near the center. -/
def DecOk (D : Dec) : Prop :=
  (D.sp = true ↔ 5 * c.Δ G < 8 * c.d G c.x0 c.t) ∧
  (D.sp = true → 0 < D.ps.length ∧ (D.pd 0).tj = c.t ∧ (D.pd 0).hw = c.hw ∧
    c.PetalOk G P c.X (c.loS G) (D.pd 0)) ∧
  (∀ k < D.ps.length, (D.sp = true → k ≠ 0) →
    3 * c.Δ G < 4 * c.d G c.x0 (D.pd k).tj ∧ c.PetalOk G P (c.Z G D k) 0 (D.pd k)) ∧
  ∀ z ∈ c.stem G D, 4 * c.d G c.x0 z ≤ 3 * c.Δ G

/-- The number of children: the stem and the petals. -/
def Dec.nch (D : Dec) : ℕ := D.ps.length + 1

/-- The center of petal `k`: the end of its highway inside the petal. -/
def Dec.xc (G : PG) (D : Dec) (k : ℕ) : ℕ := hv G (D.pd k).tj (D.pd k).hw (D.pd k).i

/-- The outer end of the portal of petal `k`. -/
def Dec.yc (G : PG) (D : Dec) (k : ℕ) : ℕ := hv G (D.pd k).tj (D.pd k).hw ((D.pd k).i + 1)

/-- The portal pair of petal `k`. -/
def Dec.portal (D : Dec) (k : ℕ) : ℕ := (D.pd k).hw.getD (D.pd k).i 0

/-- The children before the choice of their thresholds. Child `0` is the stem, with the center
of the cluster. Its target is the outer end of the special portal if there is a special petal, and
the target of the cluster otherwise. Child `k + 1` is petal `k`, with center `xc k`, target
`t_k` and highway the part of the petal's highway before the portal. For a regular petal this
part is halved. -/
noncomputable def raw (D : Dec) : ℕ → Cl
  | 0 =>
    if D.sp then
      { c with X := c.stem G D, t := D.yc G 0, hw := c.hw.drop ((D.pd 0).i + 1) }
    else { c with X := c.stem G D }
  | k + 1 =>
    { X := c.W G D k, x0 := D.xc G k, t := (D.pd k).tj,
      half := if D.sp ∧ k = 0 then c.half else c.half ∪ ((D.pd k).hw.take (D.pd k).i).toFinset,
      θ := c.θ, hw := (D.pd k).hw.take (D.pd k).i }

/-- The portal pairs: one for each petal. -/
def Dec.portals (D : Dec) : List ℕ := (List.range D.ps.length).map D.portal

end Cl

/-- How a child gets its threshold. Either it keeps the cluster as it is, when it is a single
vertex or its radius is at least `B · |X| · θ`. Or, when its radius is smaller, it is *reset*:
same vertices and center, the center as target, no highway, nothing halved, and a new threshold
`θ'` with `4 θ' ≤ θ` and `B · |X| · θ' ≤ Δ' ≤ 32 · B · |X|² · θ'`. -/
def Next (G : PG) (P : Par) (raw c' : Cl) : Prop :=
  (c' = raw ∧ (raw.X.card ≤ 1 ∨ P.B * raw.X.card * raw.θ ≤ raw.Δ G)) ∨
  (raw.Δ G < P.B * raw.X.card * raw.θ ∧
    c'.X = raw.X ∧ c'.x0 = raw.x0 ∧ c'.t = raw.x0 ∧ c'.half = ∅ ∧ c'.hw = [] ∧
    4 * c'.θ ≤ raw.θ ∧ 1 ≤ c'.θ ∧
    (raw.X.card ≤ 1 ∨ P.B * raw.X.card * c'.θ ≤ c'.Δ G) ∧
    c'.Δ G ≤ 32 * P.B * raw.X.card ^ 2 * c'.θ)

/-- `Run c T`: the decomposition of `c`, followed all the way down, gives the tree `T` (a list of
pair numbers). A single vertex gives the empty tree. Otherwise a correct step splits `c`, each
child gets its threshold by `Next`, and the tree is the union of the trees of the children and
the portals. -/
inductive Run (G : PG) (P : Par) : Cl → List ℕ → Prop
  | leaf {c : Cl} : c.X.card ≤ 1 → Run G P c []
  | node {c : Cl} (D : Cl.Dec) (cs : ℕ → Cl) (Ts : ℕ → List ℕ) :
      2 ≤ c.X.card → c.DecOk G P D → (∀ k < D.nch, Next G P (c.raw G D k) (cs k)) →
      (∀ k < D.nch, Run G P (cs k) (Ts k)) →
      Run G P c ((List.range (D.nch)).flatMap Ts ++ D.portals)

end MinCostFlow.LowStretch
