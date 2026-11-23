module

public import MinCostFlow.LowStretch.ProgChildSpec
public import MinCostFlow.LowStretch.CountVis
public import MinCostFlow.LowStretch.Params

/-!
# The contracts of the cluster procedure and of its body

The cluster procedure runs on one cluster `c` with record `R`. It is made of two parts.
* The **body**: the setup, the petals and the child step. It leaves the records of
  the children and the portals, or finds that `c` is a single vertex.
* The **recursion** (`ProgRec*.lean`): it calls the cluster procedure on each child record, then
  writes the portals after the trees of the children, in the order of `Run`.

This file states three things.
* `ClPre`: what both parts read. The global block (`GlobL.Ok`, with `J = rootJ n`), the record
  block (`RecAt`, `Rec.Ok`), the labels of all vertices below `N`, zero memory from the heap
  pointer `h` on, the
  regions that are read below `h` and apart from the labels and local indices, and room in a
  word for everything the run below `c` allocates, and for the cube of the largest weight (the
  petal searches multiply three numbers of the size of a weight, `SuRoom3`).
* `MeetsRec`: the contract of the cluster procedure, called with `[GB, RB, OUT, h]`. It writes the
  tree of a run of `c` at `OUT` and returns its length, within `recCost`.
* `MeetsBody`: the contract of the body, called with `[GB, RB, h]`. It writes four words at `h`:
  the number of children, the address of their record blocks, the end of the heap it used, and
  the address of the portals. Its cost is `bodyShare` plus `kidCost` per child.

**The cost.** With `a = A · L` (`L = pL n`, the cost of a heap step),
`recCost c R = ⌊a (4 Wk c - 2)⌋ + a (2 hidW c + |S|) + 2 kidCost (2 |X| - 1)`, where `Wk` is the
work of `c` (`Work.lean`), `hidW c` the work of the splits that the run below `c` may still do
(`CountVis.lean`), `|S|` the number of stored pairs, and `kidCost` a cost per child that does not
depend on the cluster: `10⁵ (J + 1)` for the bound `J = rootJ n` of the classes of Dijkstra, and
`500 (log w + 2)`, ten times what bounds `log2Cost` of any word (`log2Cost_le_word`). The body
may spend `a (|act c| + |S| + 1 + nch + Σ_k visW_k) + nch · kidCost`: one unit per active pair,
per stored pair, per child and for itself, the splits of the resets of its children, and
`kidCost` per child. The stored pairs of the children are active pairs of `c` or pairs that the resets make
visible, so the body must also give `Σ_k |S_k| ≤ |act c| + Σ_k visW_k`. The recursion pays for
the children with the rest of `recCost` (`Cl.Wk_step`, `Cl.sum_vis_le`, and `nch ≥ 2` for the
last term, since the sizes of the children add up to `|X|`).

The cost depends on the cluster, which the memory does not fix (its halved pairs are not all
stored). So the two contracts are stated with `Runs`, as `MeetsChild` is, and not as `Contract`s.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The cost -/

/-- The bound of the classes of Dijkstra, the same for all clusters. -/
def rootJ (n : ℕ) : ℕ := pσ n + pa n + 4

/-- The cost per child that does not depend on the cluster, at word size `w`. -/
def kidCost (w n : ℕ) : ℕ := 100000 * (rootJ n + 1) + 500 * (Nat.log 2 w + 2)

/-- `log2P` on a word costs at most `50 (log w + 2)`. -/
theorem log2Cost_le_word {w x : ℕ} (hx : x < 2 ^ w) : log2Cost x ≤ 50 * (Nat.log 2 w + 2) := by
  unfold log2Cost
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have : x = 0 := by simpa using hx
    subst this; simp
  have h1 : Nat.log 2 x < w := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · simpa using hw
    · exact Nat.log_lt_of_lt_pow (by omega) hx
  have := Nat.log_mono_right (b := 2) (show Nat.log 2 x + 1 ≤ w by omega)
  omega

/-- The part of `recCost` that pays `A · L` per unit. -/
noncomputable def recMain (A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) : ℕ :=
  ⌊((A * P.L : ℕ) : ℝ) * (4 * c.Wk G P - 2)⌋₊ + A * P.L * (2 * T.hidW G c + R.S.length)

/-- **The cost of the cluster procedure** on the cluster `c` with record `R`, at word size `w`. -/
noncomputable def recCost (w A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) : ℕ :=
  recMain A T G P c R + 2 * kidCost w G.n * (2 * c.X.card - 1)

/-- **The share of the body**: one unit per active pair, per stored pair, per child and for the
cluster, and the splits of the resets of the children, at `A · L` per unit. -/
noncomputable def bodyShare (A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (D : Cl.Dec)
    (cs : ℕ → Cl) : ℕ :=
  A * P.L * ((c.act G P).card + R.S.length + 1 + D.nch +
    ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ)

/-! ### The precondition -/

/-- The regions that the cluster procedure reads below the heap: the two blocks, the global
arrays and the arrays of the record. -/
def recRegs (GB RB : ℕ) (E : GlobL) (L : RecL) : List (ℕ × ℕ) :=
  [(GB, 21), (RB, 9), (E.IN, 3 * E.m), (E.PW, E.m), (E.EXP, E.m), (E.KPAR, E.N),
    (E.KCH1, E.N), (E.KCH2, E.N), (E.KMW, E.N), (E.KSZ, E.N), (E.KLO, E.N), (E.HEAD, E.N),
    (E.ORDL, E.n), (E.GOFF, E.N + 1), (E.GPR, E.m)] ++ L.regs

/-- **What the cluster procedure and its body read**, with the global block at `GB`, the record
block at `RB` and the heap pointer `h`. The number of buckets is `L = pL n`, as in `par n m`. -/
structure ClPre (w A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB h : ℕ)
    (mem : ℕ → ℕ) : Prop where
  ok : R.Ok T G P c
  glob : (GlobL.read mem GB).Ok T G P mem
  recAt : RecAt T G c R (GlobL.read mem GB) (RecL.read mem RB) mem
  lab_lt : ∀ v < G.n, mem ((GlobL.read mem GB).LAB + v) < T.N
  J_eq : (GlobL.read mem GB).J = rootJ G.n
  zero : ZeroFrom mem h
  below : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h
  lab_below : (GlobL.read mem GB).LAB + G.n ≤ h
  loc_below : (GlobL.read mem GB).LOC + T.N ≤ h
  lab_loc : RegDisj ((GlobL.read mem GB).LAB, G.n) ((GlobL.read mem GB).LOC, T.N)
  lab_disj : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB),
    RegDisj r ((GlobL.read mem GB).LAB, G.n)
  loc_disj : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB),
    RegDisj r ((GlobL.read mem GB).LOC, T.N)
  room : ∃ Mw, (∀ p < G.m, G.pω p ≤ Mw) ∧ (GlobL.read mem GB).INF ≤ 4 * G.n * Mw + 4 ∧
    h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R +
      2 ^ (2 * (GlobL.read mem GB).J + 20) * (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 < 2 ^ w
  L_eq : P.L = pL G.n
  loc_w : ∀ x < T.N, mem ((GlobL.read mem GB).LOC + x) < 2 ^ w

/-- **The precondition of the cluster procedure**: `ClPre`, and room at `OUT` for the tree (at
most `|X|` pairs), below the heap and apart from all that is read. -/
structure RecPre (w A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB OUT h : ℕ)
    (mem : ℕ → ℕ) : Prop extends ClPre w A T G P c R GB RB h mem where
  out_le : OUT + c.X.card ≤ h
  out_disj : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB),
    RegDisj r (OUT, c.X.card)
  out_lab : RegDisj (OUT, c.X.card) ((GlobL.read mem GB).LAB, G.n)
  out_loc : RegDisj (OUT, c.X.card) ((GlobL.read mem GB).LOC, T.N)

/-- The room of `ClPre` with squares in place of cubes: the cubes are at least the squares,
since both bases are at least `1`. -/
theorem ClPre.room_sq {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
    {mem : ℕ → ℕ} (hp : ClPre w A T G P c R GB RB h mem) :
    ∃ Mw, (∀ p < G.m, G.pω p ≤ Mw) ∧ (GlobL.read mem GB).INF ≤ 4 * G.n * Mw + 4 ∧
      h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R +
        2 ^ (2 * (GlobL.read mem GB).J + 20) * (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 < 2 ^ w := by
  obtain ⟨Mw, h1, h2, h3⟩ := hp.room
  refine ⟨Mw, h1, h2, lt_of_le_of_lt (Nat.add_le_add_left ?_ _) h3⟩
  refine Nat.mul_le_mul (Nat.mul_le_mul_left _ ?_) ?_
  · exact Nat.pow_le_pow_right (by omega) (by norm_num)
  · exact Nat.pow_le_pow_right (by omega) (by norm_num)

/-! ### The postconditions -/

/-- **The postcondition of the cluster procedure**, for the global block `E`. It returns the
length of the tree of a run of `c` and leaves the tree at `OUT`. Below `h` it changes only the
tree, the labels of the vertices of `c` and the local indices of the heads below the `θ`-nodes
of `c` (`ChildWr`); the labels stay below `N` and the local indices `LOC[x]`, `x < N`, stay
words. It leaves at `h + 2` the end of the heap it used, from which the memory is zero. -/
def RecPost (w A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (E : GlobL) (OUT h : ℕ)
    (mem : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  (∃ Tr, Run G P c Tr ∧ v = Tr.length ∧ ListAt mem' OUT Tr) ∧
    (∀ a < h, ¬ ChildWr T G c E a → ¬ (OUT ≤ a ∧ a < OUT + c.X.card) → mem' a = mem a) ∧
    (∀ u < G.n, mem' (E.LAB + u) < T.N) ∧ (∀ x < T.N, mem' (E.LOC + x) < 2 ^ w) ∧
    h + 4 ≤ mem' (h + 2) ∧ ZeroFrom mem' (mem' (h + 2)) ∧
    mem' (h + 2) ≤ h + (E.J + 2) * recCost w A T G P c R

/-- What the body leaves for the children `cs` with records `Rs` of a step `D`: the number of
children at `h`, their record blocks at `CB + 9k` (`CB` at `h + 1`), the end `HE` of the heap
at `h + 2` and the portals at `PT` (at `h + 3`). -/
def BodyKids (T : KT) (G : PG) (P : Par) (c : Cl) (D : Cl.Dec) (cs : ℕ → Cl) (Rs : ℕ → Rec)
    (E : GlobL) (h : ℕ) (mem' : ℕ → ℕ) : Prop :=
  mem' h = D.nch ∧
    (∀ k < D.nch, Next G P (c.raw G D k) (cs k) ∧ T.Sat G c.θ (c.raw G D k).X ∧
      (Rs k).Ok T G P (cs k) ∧
      RecAt T G (cs k) (Rs k) E (RecL.read mem' (mem' (h + 1) + 9 * k)) mem' ∧
      h + 4 ≤ mem' (h + 1) + 9 * k ∧ mem' (h + 1) + 9 * k + 9 ≤ mem' (h + 2) ∧
      ∀ r ∈ (RecL.read mem' (mem' (h + 1) + 9 * k)).regs, h + 4 ≤ r.1 ∧ r.1 + r.2 ≤ mem' (h + 2)) ∧
    h + 4 ≤ mem' (h + 3) ∧ mem' (h + 3) + D.ps.length ≤ mem' (h + 2) ∧
    (∀ j < D.ps.length, mem' (mem' (h + 3) + j) = D.portal j)

/-- **The postcondition of the body**, for the global block `E`, at cost `cost`. Below `h` it
changes only the cells of `ChildWr`, the labels stay below `N` and the local indices stay words.
The memory is zero from the end of its heap on. Either `c` is a single vertex and there are no children, or there is a step
`D` that meets `DecOk` with children `cs` and records `Rs` as `BodyKids` says, whose stored pairs
are paid by the active pairs of `c` and the splits. The cost is `bodyShare` plus `kidCost` per
child, and the heap grows by at most `J + 1` cells per step. -/
def BodyPost (w A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (E : GlobL) (h : ℕ)
    (mem mem' : ℕ → ℕ) (cost : ℕ) : Prop :=
  (∀ a < h, ¬ ChildWr T G c E a → mem' a = mem a) ∧ (∀ u < G.n, mem' (E.LAB + u) < T.N) ∧
    (∀ x < T.N, mem' (E.LOC + x) < 2 ^ w) ∧ h + 4 ≤ mem' (h + 2) ∧ ZeroFrom mem' (mem' (h + 2)) ∧
    ((c.X.card ≤ 1 ∧ mem' h = 0 ∧
        mem' (h + 2) ≤ h + 4 + (E.J + 1) * (A * P.L * (R.S.length + 1)) ∧
        cost ≤ A * P.L * (R.S.length + 1)) ∨
      ∃ D cs Rs, 2 ≤ c.X.card ∧ c.DecOk G P D ∧ BodyKids T G P c D cs Rs E h mem' ∧
        ∑ k ∈ Finset.range D.nch, (Rs k).S.length ≤
          (c.act G P).card + ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ ∧
        mem' (h + 2) ≤ h + 4 + (E.J + 1) * (bodyShare A T G P c R D cs + D.nch * kidCost w G.n) ∧
        cost ≤ bodyShare A T G P c R D cs + D.nch * kidCost w G.n)

/-! ### The contracts -/

/-- **The contract of the cluster procedure.** Procedure `f` of `p`, called with
`[GB, RB, OUT, h]` on a memory that meets `RecPre`, ends as `RecPost` says, within `recCost`.
The parameters have `L ≥ 1` and volume weights at least `1`, as `par n m` has. -/
def MeetsRec (w A : ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB OUT h : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool), 1 ≤ P.L → (∀ q, 1 ≤ P.cw q) → P = par G.n G.m → RecPre w A T G P c R GB RB OUT h mem →
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' cost,
      Runs w p ω body (startState [GB, RB, OUT, h] mem pos) o st' cost ∧
      RecPost w A T G P c R (GlobL.read mem GB) OUT h mem o.value st'.mem ∧
      cost ≤ recCost w A T G P c R

/-- **The contract of the body.** Procedure `f` of `p`, called with `[GB, RB, h]` on a memory
that meets `ClPre`, with volume weights at least `1`, ends as `BodyPost` says. -/
def MeetsBody (w A : ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB h : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool), ClPre w A T G P c R GB RB h mem → (∀ q, 1 ≤ P.cw q) → P = par G.n G.m →
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' cost,
      Runs w p ω body (startState [GB, RB, h] mem pos) o st' cost ∧
      BodyPost w A T G P c R (GlobL.read mem GB) h mem st'.mem cost

end MinCostFlow.LowStretch
