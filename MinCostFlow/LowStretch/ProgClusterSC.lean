module

public import MinCostFlow.LowStretch.ProgClusterLink
public import MinCostFlow.LowStretch.PSearchInv

/-!
# The setting of a petal search inside a cluster

All petal searches of a cluster run on one petal graph, built once (`pgP`). Between two searches
only two kinds of cells change: the marks `OK` of the carved nodes, and the slots. This file
fixes what does not change (`PW`, with the facts `PW.Ok` about a memory), and what a single
search adds (`PW.PS`: the target, the steps of its highway, and the start `lo` of its range).
From both it builds the setting `SC` of the search (`PW.sc`) and proves `SC.Ok` (`PW.sc_ok`, in
`ProgClusterSC2`).

The nodes of the petal graph are the local indices `0, …, s - 1` of the super-vertices and the
dummy node `s`. A node is allowed when its mark is `os`. The vertices of the remaining set `Y`
are those of `X` whose super-vertex is allowed. The highway nodes are the super-vertices of the
entries of the steps (`stEnt`): `H[k] = sv (stEnt t st k)`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The fixed values of the petal searches of one cluster. -/
structure PW where
  T : KT
  G : PG
  P : Par
  c : Cl
  R : Rec
  L : DL
  RR : ℕ
  ORD : ℕ
  AS : ℕ
  EXP : ℕ
  Es : ℕ
  SUM : ℕ
  M : ℕ
  κ : ℕ
  nact : ℕ
  bw : ℕ
  Lb : ℕ
  SQ : ℕ
  P2 : ℕ
  NXT : ℕ
  SL : ℕ
  CTL : ℕ
  nA : ℕ
  pr : ℕ → ℕ
  wtP : ℕ → ℕ
  Sm : ℕ
  Rm : ℕ

namespace PW

variable (W : PW)

/-- The local index of a vertex. -/
noncomputable def sv (v : ℕ) : ℕ := W.R.sv W.T W.c v

/-- The number of super-vertices, which is also the dummy node. -/
def s : ℕ := W.R.nodes.length

/-- The local index of the first end of entry `j`. -/
noncomputable def ea (j : ℕ) : ℕ := W.sv (W.G.pu (W.pr j))

/-- The local index of the second end of entry `j`. -/
noncomputable def eb (j : ℕ) : ℕ := W.sv (W.G.pv (W.pr j))

/-- The allowed nodes in the memory. -/
def Nodes (mem : ℕ → ℕ) : Finset ℕ :=
  (Finset.range W.L.NN).filter (fun v => mem (W.L.OK + v) = W.L.os)

open Classical in
/-- The remaining vertices: those whose super-vertex is allowed. -/
noncomputable def Y (mem : ℕ → ℕ) : Finset ℕ := W.c.X.filter (fun a => mem (W.L.OK + W.sv a) = W.L.os)

/-- The slot of node `u`: its last arc. -/
def slotA (mem : ℕ → ℕ) (u : ℕ) : ℕ := mem (W.L.HI + u) - 1

/-- The highway nodes of the steps `st` from the target `t`. -/
noncomputable def Hl (t : ℕ) (st : List (ℕ × ℕ × ℕ)) : List ℕ := W.sv t :: st.map (fun q => W.sv q.2.2)

/-- The heads with the slots of the nodes of `H` turned on. -/
def hdF (mem : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [] => (W.L.g mem).hd
  | u :: H => fun k => if k = W.slotA mem u then mem (W.NXT + u) else hdF mem H k

/-- The full graph: the graph in memory with the slots of `H` on. -/
def gF (mem : ℕ → ℕ) (H : List ℕ) : AG := { W.L.g mem with hd := W.hdF mem H }

/-- **The setting of one search**, from the memory `mem` at its start, the target `t`, the steps
`st` of its highway, the start `lo` of its range and the stamp `rs` of its run of Dijkstra (each
search takes a new stamp, so the stamps of the earlier searches are below it). -/
noncomputable def sc (mem : ℕ → ℕ) (t : ℕ) (st : List (ℕ × ℕ × ℕ)) (hw : List ℕ) (lo rs : ℕ) : SC where
  X := ⟨⟨{ W.L with rs := rs }, W.Nodes mem, W.sv t, 0, 0, ⟨fun _ => 0, fun _ => False, [], 0⟩, fun _ => [], W.RR⟩,
    W.ORD, W.AS, W.EXP, W.Es, W.SUM, W.M, W.κ, W.nact, lo, W.bw, W.Lb, W.SQ, W.P2, W.NXT, W.SL,
    W.s, W.CTL⟩
  mem0 := mem
  H := W.Hl t st
  hc := Cl.hcL W.G W.c st
  gF := W.gF mem (W.Hl t st)
  nA := W.nA
  ea := W.ea
  eb := W.eb
  pr := W.pr
  wtP := W.wtP
  Sm := W.Sm
  G := W.G
  P := W.P
  c := W.c
  Y := W.Y mem
  pd := ⟨t, hw, 0, 0⟩
  sv := W.sv
  Rm := W.Rm

/-- The facts about the memory at the start of every search of the cluster. They speak only of
cells that the searches do not change, except the marks `OK` and the heads of the slots. -/
structure Ok (w : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- The record and the cluster. -/
  hrec : W.R.Ok W.T W.G W.P W.c
  conn : W.c.Conn W.G
  /-- The nodes. -/
  hNN : W.L.NN = W.s + 1
  sS : mem (W.L.OK + W.s) ≠ W.L.os
  lohi : ∀ u < W.s, mem (W.L.LO + u) < mem (W.L.HI + u)
  chain : ∀ u < W.s, mem (W.L.HI + u) = mem (W.L.LO + (u + 1))
  hiMM : ∀ v < W.L.NN, mem (W.L.HI + v) ≤ W.L.MM
  /-- The layout. -/
  lay : W.L.LO + W.L.NN ≤ W.L.HD ∧ W.L.HI + W.L.NN ≤ W.L.HD ∧ W.L.HD + W.L.MM ≤ W.L.CS ∧
    W.L.CS + W.L.MM ≤ W.L.CL ∧ W.L.CL + W.L.MM ≤ W.L.OK ∧ W.L.OK + W.L.NN ≤ W.NXT ∧
    W.NXT + W.L.NN ≤ W.ORD ∧ W.ORD + W.L.MM ≤ W.AS ∧ W.AS + 2 * W.nA ≤ W.EXP ∧
    W.SQ + W.Lb + 2 ≤ W.P2 ∧ W.P2 + W.Lb + 2 ≤ W.L.TS ∧ W.L.TS + 5 * W.L.NN ≤ W.L.D
  lEXP : ∀ j < W.nA, W.EXP + mem (W.AS + 2 * j) < W.SQ
  lES : W.EXP ≤ W.SQ
  hR : W.L.D + pqSize W.L.J W.L.A ≤ W.RR
  hCTL : W.RR + 2 ≤ W.CTL
  hSUM : W.CTL + 4 ≤ W.SUM
  hSL : W.SUM + 5 ≤ W.SL
  wSL : W.SL + W.L.NN + 1 < 2 ^ w
  /-- The shape of the graph. -/
  heads : ∀ k < W.L.MM, mem (W.L.CL + k) < W.L.J ∧ W.L.INF + mem (W.L.CS + k) < 2 ^ w
  classes : ∀ k < W.L.MM, ∀ k' < W.L.MM, mem (W.L.CL + k) = mem (W.L.CL + k') →
    mem (W.L.CS + k) = mem (W.L.CS + k')
  budget : ∑ u ∈ Finset.range W.s, (mem (W.L.HI + u) - mem (W.L.LO + u) + 1) ≤ W.L.A
  fits : PQFits w W.L.D W.L.J W.L.A W.L.INF
  os_lt : W.L.os + 1 < 2 ^ w
  INF_pos : 0 < W.L.INF
  /-- The arcs of a node before its slot: the two directions of its entries, with their
  rounded costs. -/
  arcsN : ∀ u < W.s, ∀ Q : ℕ → ℕ → Prop,
    (∃ k, mem (W.L.LO + u) ≤ k ∧ k + 1 < mem (W.L.HI + u) ∧ Q (mem (W.L.HD + k)) (mem (W.L.CS + k))) ↔
      ∃ j < W.nA,
        (W.ea j = u ∧ Q (W.eb j) (rc W.c.θ (W.c.wbar W.G (W.pr j) (W.G.pu (W.pr j)) (W.G.pv (W.pr j))))) ∨
        (W.eb j = u ∧ Q (W.ea j) (rc W.c.θ (W.c.wbar W.G (W.pr j) (W.G.pv (W.pr j)) (W.G.pu (W.pr j)))))
  hdNN : ∀ k < W.L.MM, mem (W.L.HD + k) < W.L.NN
  hdN : ∀ u < W.s, ∀ k, mem (W.L.LO + u) ≤ k → k + 1 < mem (W.L.HI + u) → mem (W.L.HD + k) < W.L.NN
  ordA : ∀ u < W.s, ∀ k, mem (W.L.LO + u) ≤ k → k < mem (W.L.HI + u) - 1 → mem (W.ORD + k) / 2 < W.nA
  hsum : ∀ u < W.s, ∀ Fs : ℕ → ℕ → ℕ,
    ∑ k ∈ Finset.Ico (mem (W.L.LO + u)) (mem (W.L.HI + u) - 1),
        Fs (mem (W.L.HD + k)) (mem (W.ORD + k) / 2) =
      ∑ j ∈ (Finset.range W.nA).filter (W.ea · = u), Fs (W.eb j) j +
      ∑ j ∈ (Finset.range W.nA).filter (W.eb · = u), Fs (W.ea j) j
  /-- The entries. -/
  img : (Finset.range W.nA).image W.pr = W.c.act W.G W.P
  inj : Set.InjOn W.pr ↑(Finset.range W.nA)
  hwt : ∀ j < W.nA, 1 <<< (W.Es - mem (W.EXP + mem (W.AS + 2 * j))) = W.wtP (W.pr j)
  wE : ∀ j < W.nA, mem (W.EXP + mem (W.AS + 2 * j)) < 2 ^ w
  hwM : ∀ p ∈ W.c.act W.G W.P, W.wtP p * W.G.pω p = W.M
  /-- Words. -/
  wU : (W.nA + W.L.MM + 1) * (2 ^ W.Es * W.L.INF + 2 ^ W.Es + 1) < 2 ^ w
  wR2 : W.RR + 2 < 2 ^ w
  wL : W.Lb + 2 < 2 ^ w
  wSm : W.Sm < 2 ^ w
  wSQ : W.SQ + W.Lb + 1 < 2 ^ w
  wP2 : W.P2 + W.Lb + 1 < 2 ^ w
  wNXT : W.NXT + W.L.NN < 2 ^ w
  nxt : ∀ v < W.L.NN, mem (W.NXT + v) < W.L.NN
  hSm : ∀ q ≤ W.Lb + 1, mem (W.SQ + q) ≤ W.Sm ∧ mem (W.P2 + q) ≤ W.Sm
  wT2 : 8 * W.M * (4 * (W.κ + W.nact) + W.κ * W.Sm) < 2 ^ w
  /-- The numbers of the tests. -/
  hM : 1 ≤ W.M
  hLb : W.Lb = W.P.L
  hbw : W.bw = W.c.bw W.G W.P
  hκ : W.κ = W.P.κ
  hnact : W.nact = (W.c.act W.G W.P).card
  hsq : ∀ q, 1 ≤ q → q ≤ W.Lb → mem (W.SQ + q) = W.c.sq W.G W.P q
  hP2 : ∀ q, 1 ≤ q → q ≤ W.Lb → mem (W.P2 + q) = 2 ^ Cl.lam W.P q
  hcw : ∀ p, W.P.cw p = 1
  hκ1 : 1 ≤ W.P.κ
  hL1 : 1 ≤ W.P.L
  hΔ : 8 * W.P.L * (Cl.lam W.P 0 + 3) ≤ W.c.Δ W.G
  hV : W.c.V W.G W.P ≤ 2 ^ Cl.lam W.P 0 * W.P.κ
  /-- The largest radius is below `2Δ`, so inactive pairs need no arc. -/
  hRm2 : W.Rm < 2 * W.c.Δ W.G

/-- What one search adds: the target `t`, the steps `st` of its highway, and the start `lo` of its
range. -/
structure PS (w : ℕ) (mem : ℕ → ℕ) (t : ℕ) (st : List (ℕ × ℕ × ℕ)) (hw : List ℕ) (lo : ℕ) : Prop where
  hwd : W.c.HwDec W.G t st hw
  entY : ∀ i ≤ st.length, Cl.stEnt t st i ∈ W.Y mem
  nd : (W.Hl t st).Nodup
  pos : ∀ k < st.length, 0 < W.c.len W.G (st.getD k (0, 0, 0)).1
  nxt : ∀ k < st.length, mem (W.NXT + W.sv (Cl.stEnt t st k)) = W.sv (Cl.stEnt t st (k + 1))
  nxtE : mem (W.NXT + W.sv (Cl.stEnt t st st.length)) = W.s
  scost : ∀ k < st.length, mem (W.L.CS + W.slotA mem (W.sv (Cl.stEnt t st k))) =
    W.c.len W.G (st.getD k (0, 0, 0)).1
  /-- The slots: the one of the target is on, the others go to the dummy node. -/
  sl0 : mem (W.L.HD + W.slotA mem (W.sv t)) = mem (W.NXT + W.sv t)
  slS : ∀ u < W.s, u ≠ W.sv t → mem (W.L.HD + W.slotA mem u) = W.s
  /-- The range. -/
  wb : lo + (W.Lb + 1) * W.bw + 2 < 2 ^ w
  wT1 : (8 * W.M * (W.κ + W.nA) + (lo + (W.Lb + 1) * W.bw + 1) * (W.nA * 2 ^ W.Es)) *
    (W.Sm + 1) < 2 ^ w
  hRm : lo + (W.Lb + 1) * W.bw ≤ W.Rm
  hINF : lo + (W.Lb + 1) * W.bw < W.L.INF

end PW

end MinCostFlow.LowStretch
