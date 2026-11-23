module

public import MinCostFlow.LowStretch.ProgRecFit
public import MinCostFlow.LowStretch.ProgClusterLoop6
public import MinCostFlow.LowStretch.ProgClusterLoop5
public import MinCostFlow.LowStretch.ProgClusterSet14

/-!
# The contract of the setup of a cluster

The body of the cluster procedure first calls the setup, with the arguments `[GB, RB, h]` of the
body and on a memory that meets `ClPre`, for a cluster with at least two vertices. The setup builds
everything that the petal loop reads (`PW.Ok`, `Btw`, `Tree`, `Cone`, `LLay`, `LW`) in the heap
from `h` on. A call cannot hand registers back, so the setup writes the values that the loop keeps
in registers into a block of `51` words at `h`:
- `h + i`, `i < 43`: the registers of the loop, `LReg` (slots `13`, `32`, `41` hold `0`; the
  body sets register `13` to the first stamp `1`);
- `h + 43`, `h + 44`, `h + 45`: the start `loS` of the range of the special petal, the node of
  `c.t` and `c.t` (registers `50`, `51`, `52` of `spPet`);
- `h + 46`: `1` when the target is far (`5 Δ < 8 d(t)`, so there is a special petal), else `0`;
- `h + 47`, `h + 48`, `h + 49`: the addresses `PF`, `PB` of the tree and `ACT` of the active
  entries, which the petal block needs and the loop registers do not hold;
- `h + 50`: the end `hS` of the heap of the setup (fresh memory from there on).

Then the body loads these words into registers, and the first `LInv` holds (a part of
`SetupOut.ex`). The setup also gives what `LInv.spPet_runs` asks of the special petal. Its cost
is `setupCost` (`setupCost_eq` gives it in terms of the ghost): `O(log J + L)` per stored pair
and node, and `O(J)` once (to empty the queues of the two runs of Dijkstra).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The ghost values of the setup. -/
structure SetG where
  T : KT
  G : PG
  P : Par
  c : Cl
  R : Rec

/-- **The room for the products of the petal searches**: room for `Mw³` in a word, for a bound
`Mw` on the weights. The petal searches multiply a weight `2^Es / ω` (up to `Mw`) by a length
(up to `Δ ≤ n Mw`) and by an entry of the table `SQ` (up to `2^2^L + Δ`), so room for `Mw²`
is not enough (`LW.wT1`). The room of `ClPre` gives it. -/
def SuRoom3 (w : ℕ) (T : KT) (G : PG) (h : ℕ) : Prop :=
  ∃ Mw, (∀ p < G.m, G.pω p ≤ Mw) ∧
    h + 2 ^ (2 * rootJ G.n + 20) * (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 < 2 ^ w

/-- The precondition of the setup: `ClPre` at `[GB, RB, h]`, at least two vertices, at least one
bucket, unit volume weights, and room for `Mw³` in a word (`SuRoom3`). The constants are those
of `par n m`: the setup computes the threshold `Q` of the active pairs and the volume `κ` of an
empty petal from `n` and `m`, and the petal searches need `8 L (λ₀ + 3) ≤ Δ` and
`V ≤ 2^λ₀ κ` (`PW.Ok.hΔ`, `PW.Ok.hV`), which hold for these constants (`Par.Fit`). -/
def setupPre (w : ℕ) (g : SetG) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ GB RB h, args = [GB, RB, h] ∧ ClPre w bodyA g.T g.G g.P g.c g.R GB RB h mem ∧
    2 ≤ g.c.X.card ∧ 1 ≤ g.P.L ∧ (∀ q, 1 ≤ g.P.cw q) ∧ g.P = par g.G.n g.G.m ∧
    SuRoom3 w g.T g.G h

/-- The values of the block of the setup at `h`. -/
noncomputable def setupBlock (W : PW) (A : PW.TA) (Q : PW.LA) : List ℕ :=
  W.LReg A Q (W.c.Δ W.G) ++
    [W.c.loS W.G, W.sv W.c.t, W.c.t,
      if 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t then 1 else 0]

/-- **What the setup leaves**, for the ghost `g`, the heap pointer `h` and the memories `mem`
before and `mem'` after: the setting `W` of the petal searches (for the cluster and record of
`g`), the arrays `A` of the tree and the outputs `Q`, with
- the number `J + 5` of classes of the queues of the petal searches, `J = rootJ n` (the arcs of
  the active pairs have classes up to `J + 4`: their reduced lengths are at most twice their
  weights, and these are at most `128 B n² θ`, while `2^J` is only known to exceed `128 B n²`);
- the array `ACT` of the active entries: entry `i < nA` holds the pair `W.pr i` and its half
  flag;
- where the arrays lie: the block of `51` words at `h` comes before all of them, they all
  end by `hS`, and `ACT` ends by the heads `HD` of the graph (the petal searches write there);
- the capacity `A` of the queues of the petal searches is at most `2 |S| + 2 s`;
- the block at `h` (`setupBlock`), the cells below `h` unchanged, and fresh memory from
  `hS ≤ h + 1000 (J + 1) (|S| + s + L + 10)` on (the queues of the two runs
  of Dijkstra take `2 J A` cells, with a capacity `A` linear in `|S| + s`);
- the first invariant of the loop, for every state whose registers are the block and whose
  memory is `mem'`, with no petal, `u = 0`, the stamp `1`, and `M0 = mem'`;
- the layout `LLay` and the word facts `LW`;
- the facts that `LInv.spPet_runs` asks of the special petal, with `lo = loS`: the node of `c.t`
  is allowed, its path of parents has `n` steps, `c.hw` splits along it, and the word facts. -/
structure SetupOut (w : ℕ) (g : SetG) (h : ℕ) (mem mem' : ℕ → ℕ) : Prop where
  ex : ∃ (W : PW) (A : PW.TA) (Q : PW.LA) (hS n ACT : ℕ),
    W.L.J = rootJ g.G.n + 5 ∧ W.T = g.T ∧ W.G = g.G ∧ W.P = g.P ∧ W.c = g.c ∧ W.R = g.R ∧
    (∀ i < W.nA, mem' (ACT + 2 * i) = W.pr i ∧
      mem' (ACT + 2 * i + 1) = if W.pr i ∈ W.c.half then 1 else 0) ∧
    mem' (h + 47) = A.PF ∧ mem' (h + 48) = A.PB ∧ mem' (h + 49) = ACT ∧ mem' (h + 50) = hS ∧
    h + 51 ≤ W.L.HD ∧ h + 51 ≤ A.PP ∧ h + 51 ≤ A.PF ∧ h + 51 ≤ A.PA ∧ h + 51 ≤ A.PB ∧
    h + 51 ≤ A.FD ∧ h + 51 ≤ W.L.OK ∧ h + 51 ≤ W.NXT ∧ h + 51 ≤ ACT ∧
    Q.PT + W.s ≤ hS ∧ W.L.OK + W.s ≤ hS ∧ W.NXT + W.s + 1 ≤ hS ∧ A.PP + W.s ≤ hS ∧
    A.PF + W.s ≤ hS ∧ A.PA + W.s ≤ hS ∧ A.PB + W.s ≤ hS ∧ A.FD + W.s ≤ hS ∧
    ACT + 2 * W.nA ≤ hS ∧ ACT + 2 * W.nA ≤ W.L.HD ∧ W.L.A ≤ 2 * g.R.S.length + 2 * W.s ∧
    (∀ i < 47, mem' (h + i) = (setupBlock W A Q).getD i 0) ∧
    (∀ a < h, mem' a = mem a) ∧ ZeroFrom mem' hS ∧
    hS ≤ h + 1000 * (rootJ g.G.n + 1) * (g.R.S.length + g.R.nodes.length + g.P.L + 10) ∧
    (∀ (sp : Bool) (st : State), st.mem = mem' →
      (∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 → st.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0) →
      st.regs 13 = 1 → st.regs 32 = 0 → st.regs 41 = 0 →
      W.LInv A Q sp 0 mem' w ⟨0, 1, [], W.Φ mem'⟩ st) ∧
    W.LLay A Q w ∧ W.LW A Q w ∧
    W.sv W.c.t < W.s ∧ W.c.t ∈ W.c.X ∧ mem' (W.L.OK + W.sv W.c.t) = W.L.os ∧
    W.Path mem' (W.sv W.c.t) n ∧ W.c.HwDec W.G W.c.t (W.stp A mem' (W.sv W.c.t) n) W.c.hw ∧
    W.c.loS W.G + (W.Lb + 1) * W.bw + 2 < 2 ^ w ∧
    (8 * W.M * (W.κ + W.nA) + (W.c.loS W.G + (W.Lb + 1) * W.bw + 1) * (W.nA * 2 ^ W.Es)) *
      (W.Sm + 1) < 2 ^ w ∧
    W.c.loS W.G + (W.Lb + 1) * W.bw ≤ W.Rm ∧ W.c.loS W.G + (W.Lb + 1) * W.bw < W.L.INF ∧
    (5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t →
      W.c.loS W.G + W.Lb * W.bw < W.c.d W.G W.c.x0 W.c.t) ∧
    W.c.t < 2 ^ w

/-- The postcondition of the setup. -/
def setupPost (w : ℕ) (g : SetG) (args : List ℕ) (mem : ℕ → ℕ) (_ : ℕ) (mem' : ℕ → ℕ) : Prop :=
  ∀ GB RB h, args = [GB, RB, h] → SetupOut w g h mem mem'

/-- **The cost of the setup**, read from the memory: with `J` and `n` from the global block at
`GB` and `s`, `nS` from the record block at `RB`, it is `10⁵ (log J + 2 + L)` for each stored pair
(counted twice, once for the active pairs, which are among them) and each node, and `400 J + 10⁴`
once. Here `L = pL n` (`ClPre.L_eq`). -/
def setupCost (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  100000 * (Nat.log 2 (GlobL.read mem (args.getD 0 0)).J + 2 +
      pL (GlobL.read mem (args.getD 0 0)).n) *
      (2 * (RecL.read mem (args.getD 1 0)).nS + (RecL.read mem (args.getD 1 0)).s + 1) +
    400 * (GlobL.read mem (args.getD 0 0)).J + 10000

/-- **The contract of the setup.** -/
def setupC (w : ℕ) : Contract := ghostC (setupPre w) (setupPost w) setupCost

/-- The cost of the setup in terms of the ghost: `10⁵ (log J + 2 + L)` per stored pair (twice)
and per node, and `400 J + 10⁴` once. -/
noncomputable def setupCostOf (g : SetG) : ℕ :=
  100000 * (Nat.log 2 (rootJ g.G.n) + 2 + g.P.L) * (2 * g.R.S.length + g.R.nodes.length + 1) +
    400 * rootJ g.G.n + 10000

/-- Under the precondition, the cost read from memory is the cost of the ghost. -/
theorem setupCost_eq {w : ℕ} {g : SetG} {GB RB h : ℕ} {mem : ℕ → ℕ}
    (hp : ClPre w bodyA g.T g.G g.P g.c g.R GB RB h mem) :
    setupCost [GB, RB, h] mem = setupCostOf g := by
  have h1 : (RecL.read mem RB).nS = g.R.S.length := hp.recAt.arcs.nS
  have h2 : (RecL.read mem RB).s = g.R.nodes.length := hp.recAt.arcs.s
  have h3 := hp.J_eq
  have h4 : (GlobL.read mem GB).n = g.G.n := hp.glob.n
  unfold setupCost setupCostOf
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [h1, h2, h3, h4, hp.L_eq]

end MinCostFlow.LowStretch
