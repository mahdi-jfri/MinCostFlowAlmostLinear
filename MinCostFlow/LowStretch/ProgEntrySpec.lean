module

public import MinCostFlow.LowStretch.Work
public import MinCostFlow.LowStretch.Transfer
public import MinCostFlow.LowStretch.KReset
public import MinCostFlow.LowStretch.ClRep
public import MinCostFlow.LowStretch.KOrder
public import MinCostFlow.LowStretch.ProgLca
public import MinCostFlow.LowStretch.ProgCSR
public import MinCostFlow.LowStretch.ProgParams
public import MinCostFlow.LowStretch.ProgRecSpec

/-!
# What the entry asks of the cluster procedure

The program first reads the graph and builds the global arrays: the pairs with their rounded
weights, the merge tree with its leaf order and heavy-path heads, the lowest common node of every
pair, and the pairs grouped by this node. Then it writes the record of the first cluster and calls
the cluster procedure on it once. This file states what that call must do (`clC`).

The first cluster holds every vertex, with center and target `0`, nothing halved and no highway.
Its threshold is `rootθ`, the power of two `thr S B n` with `S = max(μ, 4 B n)` for the weight `μ`
of the root of the merge tree (`root_inv`). Its record (`rootRec`) lists its super-vertices, the
`θ`-nodes of the merge tree, in increasing order, and stores every pair whose ends lie in two
different `θ`-nodes, in increasing order, with half flag `0`.

The contract asks the procedure to write the pairs of the tree of a run (`Run`) of the first
cluster at `OUT` and to return their number. Its cost may be `recCost` of the first cluster
(`ProgRecSpec.lean`), plus `30 m + 500` steps to write the blocks of the first cluster. The
precondition also asks that a word holds a bound on the memory that the recursion uses, which
grows with this cost.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- The threshold of the first cluster. -/
def rootθ (T : KT) (G : WGraph) : ℕ :=
  thr (max (T.mw (T.N - 1)) (4 * pB G.n * G.n)) (pB G.n) G.n

/-- The first cluster. -/
def rootCl (T : KT) (G : WGraph) : Cl := root (pgOf G) (rootθ T G)

/-- `k` is an `x`-node: a node of weight below `x` whose parent, if any, weighs at least `x`. -/
def KT.IsNode (T : KT) (x k : ℕ) : Prop :=
  k < T.N ∧ T.mw k < x ∧ (k + 1 < T.N → x ≤ T.mw (T.par k))

instance (T : KT) (x k : ℕ) : Decidable (T.IsNode x k) := by
  unfold KT.IsNode; infer_instance

/-- The record of the first cluster: its `θ`-nodes in increasing order, and every pair between two
different `θ`-nodes in increasing order, not halved. -/
noncomputable def rootRec (T : KT) (G : WGraph) : Rec := by
  classical
  exact
    { nodes := (List.range T.N).filter fun k => T.IsNode (rootθ T G) k
      S := ((List.range G.m).filter fun p =>
          T.top (rootθ T G) ((pgOf G).pu p) ≠ T.top (rootθ T G) ((pgOf G).pv p)).map
        fun p => (p, 0)
      hwc := [] }

/-- The arguments of the cluster procedure: the sizes, the addresses of the global arrays and of
the record, the output address and the heap pointer. -/
structure EA where
  n : ℕ
  m : ℕ
  /-- The two ends of pair `p` at `IN + 3p` and `IN + 3p + 1`. -/
  IN : ℕ
  /-- The rounded weight of each pair. -/
  PW : ℕ
  /-- Its exponent. -/
  EXP : ℕ
  /-- The number of nodes of the merge tree. -/
  NN : ℕ
  KPAR : ℕ
  KCH1 : ℕ
  KCH2 : ℕ
  KMW : ℕ
  KMP : ℕ
  KSZ : ℕ
  KLO : ℕ
  HEAD : ℕ
  ORDL : ℕ
  /-- The lowest common node of the ends of each pair. -/
  LCA : ℕ
  /-- The pairs grouped by their lowest common node: offsets and items. -/
  GOFF : ℕ
  GORD : ℕ
  /-- The label of each vertex: the head of its `θ`-node. -/
  LAB : ℕ
  /-- The local index of each label. -/
  LOC : ℕ
  /-- The six numbers of `parVal`. -/
  PAR : ℕ
  /-- The threshold and its exponent. -/
  TH : ℕ
  lθ : ℕ
  /-- The super-vertices of the record. -/
  s : ℕ
  NODES : ℕ
  /-- The stored pairs of the record, two words each. -/
  nS : ℕ
  SA : ℕ
  /-- Where the tree goes. -/
  OUT : ℕ
  /-- The heap pointer. -/
  H : ℕ

/-- The list of the arguments. -/
def EA.args (E : EA) : List ℕ :=
  [E.n, E.m, E.IN, E.PW, E.EXP, E.NN, E.KPAR, E.KCH1, E.KCH2, E.KMW, E.KMP, E.KSZ, E.KLO,
    E.HEAD, E.ORDL, E.LCA, E.GOFF, E.GORD, E.LAB, E.LOC, E.PAR, E.TH, E.lθ, E.s, E.NODES, E.nS,
    E.SA, E.OUT, E.H]

/-- The arrays lie in this order and do not overlap. -/
structure EA.Lay (E : EA) : Prop where
  l1 : E.IN + 3 * E.m ≤ E.PAR
  l2 : E.PAR + 6 ≤ E.EXP
  l3 : E.EXP + E.m ≤ E.PW
  l4 : E.PW + E.m ≤ E.KPAR
  l5 : E.KPAR + E.NN ≤ E.KCH1
  l6 : E.KCH1 + E.NN ≤ E.KCH2
  l7 : E.KCH2 + E.NN ≤ E.KMW
  l8 : E.KMW + E.NN ≤ E.KMP
  l9 : E.KMP + E.NN ≤ E.KSZ
  l10 : E.KSZ + E.NN ≤ E.KLO
  l11 : E.KLO + E.NN ≤ E.HEAD
  l12 : E.HEAD + E.NN ≤ E.ORDL
  l13 : E.ORDL + E.n ≤ E.LCA
  l14 : E.LCA + E.m ≤ E.GOFF
  l15 : E.GOFF + E.NN + 1 ≤ E.GORD
  l16 : E.GORD + E.m ≤ E.NODES
  l17 : E.NODES + E.s ≤ E.LAB
  l18 : E.LAB + E.n ≤ E.LOC
  l19 : E.LOC + E.NN ≤ E.SA
  l20 : E.SA + 2 * E.nS ≤ E.OUT
  l21 : E.OUT + E.n ≤ E.H

/-- The memory after the preprocessing, for the graph `G` and its merge tree `T`. -/
structure EA.Pre (E : EA) (w : ℕ) (G : WGraph) (T : KT) (mem : ℕ → ℕ) : Prop where
  allowed : Allowed G
  two_le : 2 ≤ G.n
  hn : E.n = G.n
  hm : E.m = G.m
  hN : E.NN = T.N
  N_le : T.N ≤ 2 * G.n
  /-- The record holds the first cluster (this includes `T.Ok` and the invariant). -/
  ok : (rootRec T G).Ok T (pgOf G) (par G.n G.m) (rootCl T G)
  hTH : E.TH = rootθ T G
  th : rootθ T G = 2 ^ E.lθ
  ends : ∀ p < G.m, mem (E.IN + 3 * p) = (pgOf G).pu p ∧ mem (E.IN + 3 * p + 1) = (pgOf G).pv p
  pw : ∀ p < G.m, mem (E.PW + p) = (pgOf G).pω p
  ex : ∀ p < G.m, (pgOf G).pω p = 2 ^ mem (E.EXP + p)
  par : ∀ k < T.N, mem (E.KPAR + k) = T.par k ∧ mem (E.KMW + k) = T.mw k
  ch : ∀ k, G.n ≤ k → k < T.N →
    mem (E.KCH1 + k) = T.ch1 k ∧ mem (E.KCH2 + k) = T.ch2 k ∧ mem (E.KMP + k) = T.mp k
  ko : ∀ k < T.N, mem (E.KSZ + k) = T.sz (pgOf G) k ∧ mem (E.KLO + k) = T.lo (pgOf G) k ∧
    mem (E.HEAD + k) = T.hd (pgOf G) k
  ordl : ∀ v < G.n, mem (E.ORDL + T.lo (pgOf G) v) = v
  lca : ∀ q < G.m, T.IsLca ((pgOf G).pu q) ((pgOf G).pv q) (mem (E.LCA + q))
  goff : ∀ u ≤ T.N, mem (E.GOFF + u) = offOf (fun q => mem (E.LCA + q)) G.m u
  gord : ∀ u < T.N, ∀ j < (grp (fun q => mem (E.LCA + q)) G.m u).length,
    mem (E.GORD + offOf (fun q => mem (E.LCA + q)) G.m u + j) =
      (grp (fun q => mem (E.LCA + q)) G.m u).getD j 0
  lab : ∀ v < G.n, mem (E.LAB + v) = T.hd (pgOf G) (T.top (rootθ T G) v)
  loc : ∀ k ∈ (rootRec T G).nodes, mem (E.LOC + T.hd (pgOf G) k) = (rootRec T G).nodes.idxOf k
  loc_w : ∀ x < T.N, mem (E.LOC + x) < 2 ^ w
  prm : ∀ i < 6, mem (E.PAR + i) = parVal G.n G.m i
  hs : E.s = (rootRec T G).nodes.length
  nodes : ListAt mem E.NODES (rootRec T G).nodes
  hnS : E.nS = (rootRec T G).S.length
  sa : ∀ j < (rootRec T G).S.length, mem (E.SA + 2 * j) = ((rootRec T G).S.getD j (0, 0)).1 ∧
    mem (E.SA + 2 * j + 1) = ((rootRec T G).S.getD j (0, 0)).2
  lay : E.Lay
  zero : ZeroFrom mem E.H
  word : (E.H + (pgOf G).maxω + 2) ^ 16 < 2 ^ w

/-- The cost allowed for the first cluster, with `A · L` per unit: the cost of the cluster
procedure on it, and the steps that write its blocks. -/
noncomputable def clCost (w A : ℕ) (G : WGraph) (T : KT) : ℕ :=
  recCost w A T (pgOf G) (par G.n G.m) (rootCl T G) (rootRec T G) + 30 * G.m + 500

/-- **The contract of the cluster procedure on the first cluster.** From the memory after the
preprocessing, it writes the pairs of the tree of a run of the first cluster at `OUT` and returns
their number, within `clCost w A G T`. A word must hold the bound `E.H + 30 + 2^63 X^14 + 2^21 X^4 ·
clCost w A G T` with `X = H + maxω + 2`, on the memory that the recursion uses. -/
noncomputable def clC (w A : ℕ) (G : WGraph) (T : KT) : Contract where
  pre args mem := ∃ E : EA, args = E.args ∧ E.Pre w G T mem ∧
    E.H + 30 + 2 ^ 63 * (E.H + (pgOf G).maxω + 2) ^ 14 +
      2 ^ 21 * (E.H + (pgOf G).maxω + 2) ^ 4 * clCost w A G T < 2 ^ w
  post args _ v mem' := ∀ E : EA, args = E.args →
    ∃ Tr, Run (pgOf G) (par G.n G.m) (rootCl T G) Tr ∧ v = Tr.length ∧ ListAt mem' E.OUT Tr
  cost _ _ := clCost w A G T

theorem EA.eq_of_args {E E' : EA} (h : E.args = E'.args) : E' = E := by
  cases E; cases E'; simp only [EA.args, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, -⟩ := h
  subst_vars; rfl

end MinCostFlow.LowStretch
