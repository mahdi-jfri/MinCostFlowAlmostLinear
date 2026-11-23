module

public import MinCostFlow.LowStretch.ProgChildDraw
public import MinCostFlow.LowStretch.ProgPQClear

/-!
# The radius of a raw child: the program

`drawP` finds the radius of the cluster that a record holds, when the record meets `Rec.OkW`
(a raw child of a cluster need not meet the invariant). From a heap pointer `H` it lays out the
arrays of `arcP`, the stamps of Dijkstra and the class queues, one after the other. It builds the
arc graph with `arcP`, empties the queues with `pqClear`, runs Dijkstra from the node of the
center with `dijRun`, and returns the largest tentative cost with `maxP`. By `Rec.draw_result`
this is the radius (`drawP_spec`). The memory below `H` and from `drawEnd` on is unchanged.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The arguments of `drawP`: what `arcFill` reads, the cutoff `D` of the stored pairs, the
local index `x0` of the center, the number `J` of classes, the value `INF` and the heap
pointer `H`. -/
structure DWE where
  s : ℕ
  nS : ℕ
  SA : ℕ
  IN : ℕ
  PW : ℕ
  EXP : ℕ
  LAB : ℕ
  LOC : ℕ
  D : ℕ
  lθ : ℕ
  x0 : ℕ
  J : ℕ
  INF : ℕ
  H : ℕ

namespace DWE

variable (E : DWE)

def args : List ℕ :=
  [E.s, E.nS, E.SA, E.IN, E.PW, E.EXP, E.LAB, E.LOC, E.D, E.lθ, E.x0, E.J, E.INF, E.H]

theorem eq_of_args {E E' : DWE} (h : E.args = E'.args) : E' = E := by
  cases E; cases E'; simp only [DWE.args, List.cons.injEq] at h
  simp_all

/-- The arrays of `arcP`, from `H` on: `TL, HDt, CSt, CLt` with `2 nS` cells each, `OFF` with
`s + 2`, `CNT` with `s + 1`, `ORD, HD, CS, CL` with `2 nS` each, and `OK` with `s + 1`. The
marks are `os = 0`. -/
def ap : AP :=
  ⟨E.s, E.nS, E.SA, E.IN, E.PW, E.EXP, E.LAB, E.LOC, E.D, E.lθ, E.H, E.H + 2 * E.nS,
    E.H + 4 * E.nS, E.H + 6 * E.nS, E.H + 8 * E.nS, E.H + 8 * E.nS + E.s + 2,
    E.H + 8 * E.nS + 2 * E.s + 3, E.H + 10 * E.nS + 2 * E.s + 3, E.H + 12 * E.nS + 2 * E.s + 3,
    E.H + 14 * E.nS + 2 * E.s + 3, E.H + 16 * E.nS + 2 * E.s + 3, 0⟩

/-- The stamps of Dijkstra, after the arrays of `arcP`. -/
def TS : ℕ := E.H + 16 * E.nS + 3 * E.s + 4

/-- The class queues, after the stamps. -/
def Dq : ℕ := E.H + 16 * E.nS + 8 * E.s + 9

/-- The capacity of the queues. -/
def Aq : ℕ := 2 * E.nS + E.s + 1

/-- The two cells after the queues that the steps of Dijkstra write. -/
def Rr : ℕ := E.Dq + (3 + 4 * E.J + 2 * E.J * E.Aq)

/-- The layout of the run of Dijkstra, with stamp `1`. -/
def L : DL := E.ap.toDL E.Dq E.J E.Aq E.INF E.TS 1

/-- The registers `0` to `13` hold the arguments. -/
def Regs (st : State) : Prop := ∀ r < 14, st.regs r = E.args.getD r 0

end DWE

/-- The end of the cells that `drawP` writes. -/
def drawEnd (E : DWE) : ℕ := E.Rr + 2

/-- The address `H + a nS + b s + k`, from the registers `13`, `1` and `0` of `drawP`. -/
def layE (a b k : ℕ) : Expr :=
  .bin .add (.bin .add (.bin .add (.reg 13) (.bin .mul (.const a) (.reg 1)))
    (.bin .mul (.const b) (.reg 0))) (.const k)

/-- The capacity `Aq` of the queues, from the registers of `drawP`. -/
def aqE : Expr := .bin .add (.bin .add (.bin .mul (.const 2) (.reg 1)) (.reg 0)) (.const 1)

/-- The address `Rr`, from the registers of `drawP`. -/
def rrE : Expr :=
  .bin .add (layE 16 8 9) (.bin .add (.bin .add (.const 3) (.bin .mul (.const 4) (.reg 11)))
    (.bin .mul (.bin .mul (.const 2) (.reg 11)) aqE))

/-- The end of `drawP`, after `pqClear`: Dijkstra, then the largest tentative cost. -/
def drawU (bR bM : ℕ) : Stmt :=
  .seq (.call 29 bR [layE 16 8 9, .reg 11, aqE, .reg 12, layE 8 0 0, layE 8 0 1, layE 10 2 3,
      layE 12 2 3, layE 14 2 3, layE 16 2 3, .const 0, layE 16 3 4,
      .bin .add (.reg 0) (.const 1), .const 1, rrE, .reg 10])
  (.seq (.call 29 bM [layE 16 3 4, .bin .add (.reg 0) (.const 1), .reg 0, .const 1, .reg 12])
  (.ret (.reg 29)))

/-- The part of `drawP` after `arcP`: the header of the queues, `pqClear`, then `drawU`. -/
def drawT (bC bR bM : ℕ) : Stmt :=
  .seq (.store (layE 16 8 9) (.reg 11))
  (.seq (.store (layE 16 8 10) aqE)
  (.seq (.store (layE 16 8 11) (.reg 12))
  (.seq (.call 29 bC [layE 16 8 9, .reg 11, .reg 12]) (drawU bR bM))))

/-- `drawP` with `args = E.args`. Procedures `bA`, `bC`, `bR`, `bM` are `arcP`, `pqClear`,
`dijRun` and `maxP`. The registers `0` to `13` keep the arguments, and each address is computed
from them where it is used. -/
def drawP (bA bC bR bM : ℕ) : Stmt :=
  .seq (.call 29 bA [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
      .reg 9, .reg 13, layE 2 0 0, layE 4 0 0, layE 6 0 0, layE 8 0 0, layE 8 1 2, layE 8 2 3,
      layE 10 2 3, layE 12 2 3, layE 14 2 3, layE 16 2 3, .const 0])
  (drawT bC bR bM)

theorem drawP_noRand (bA bC bR bM : ℕ) : (drawP bA bC bR bM).NoRand := by
  simp [drawP, drawT, drawU, Stmt.NoRand]

/-- The ghost values of `drawP`: the record, its cluster, and the bounds of `arcFill`. -/
structure DWG where
  T : KT
  G : PG
  c : Cl
  R : Rec
  m : ℕ
  n : ℕ
  NL : ℕ

/-- The precondition of `drawP`: the record `R` is in memory below `H` and meets `Rec.OkW`, the
cutoff `D` and `INF` are above the radius, `x0` is the local index of the center, the classes of
the arcs fit below `J`, and the memory from `H` on is fresh. -/
def drawPre (w : ℕ) (g : DWG) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ E : DWE, args = E.args ∧ Rec.Mem g.T g.G g.c g.R E.ap.toAF mem ∧ g.R.OkW g.T g.G g.c ∧
    E.ap.Pre w mem g.m g.n g.NL ∧ g.c.Δ g.G ≤ E.D ∧ g.c.Δ g.G < E.INF ∧
    4 * E.D < 2 ^ (E.J + E.lθ) ∧ 1 ≤ E.J ∧ E.x0 = g.R.sv g.T g.c g.c.x0 ∧ E.x0 < E.s ∧
    ZeroFrom mem E.H ∧ drawEnd E < 2 ^ w ∧ E.INF * E.J + E.J < 2 ^ w ∧ E.INF + E.D < 2 ^ w

/-- The postcondition of `drawP`: the value is the radius, and only the cells from `H` to
`drawEnd` change. -/
def drawPost (_ : ℕ) (g : DWG) (args : List ℕ) (mem : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  v = g.c.Δ g.G ∧ ∀ E : DWE, args = E.args → ∀ a, (a < E.H ∨ drawEnd E ≤ a) → mem' a = mem a

/-- The cost of `drawP`: `O(log J)` per pair and per node, and `O(J)` to empty the queues. -/
def drawCost (args : List ℕ) (_ : ℕ → ℕ) : ℕ :=
  (200 * (Nat.log 2 (args.getD 11 0) + 2) + 3000) * (2 * args.getD 1 0 + 2 * args.getD 0 0 + 2) +
    150 * args.getD 11 0 + 2000

/-- The contract of `drawP`. -/
def drawC (w : ℕ) : Contract := ghostC (drawPre w) (drawPost w) drawCost

end MinCostFlow.LowStretch
