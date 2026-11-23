module

public import MinCostFlow.LowStretch.ProgClusterSetupSpec
public import MinCostFlow.LowStretch.ProgChildProg
public import MinCostFlow.LowStretch.ProgLog
public import MinCostFlow.LowStretch.ProgClusterTab
public import MinCostFlow.LowStretch.ProgClusterMax

/-!
# The setup of a cluster: the program

The setup `setupP` is called with `args = [GB, RB, h]`. It builds, from the heap pointer `h` on,
everything that the petal loop reads, and writes the block of `51` words at `h` that
`ProgClusterSetupSpec.lean` describes.

It first loads the words it needs from the global block at `GB` and the record block at `RB`
into the registers `3` to `22` (`suPro`). Then it computes the number `L` of buckets with two
calls of `log2P`, runs `drawP` (the first run of Dijkstra, which returns `Δ`), and builds the
tree (`treeP`, `hwFix`), the active entries (`actP`), the graph of the petal searches (`pgP`),
the tables `NXT`, `ORD`, `AS`, `EXP`, `P2`, `SQ` (`tabP`), the largest exponent `Es`
(`maxtP`) and the empty queues of the petal searches (`pqClear`). It ends with the stores of
the block.

Every address is computed where it is used, from the registers `13` (`s`), `14` (`nS`), `24`
(the end `Z` of the cells of `drawP`), `28` (`L`) and `33` (the address `RR` after the queues).
From `Z` on, the arrays are (with `NI = 2 nS + s` and `A2 = 2 nS + 2 s`):
- the arrays `PAR, PP, PF, PA, PB, SCc, SCk, PCI` of `treeP` (`s + 1` cells each), then `ACT`
  (`2 nS`);
- the arrays `TL, HDt, CSt, CLt` of `pgP` (`NI` each), `OFF` (`s + 2`), `CNT` (`s + 1`), its
  `ORD`, `HD`, `CS`, `CL` (`NI` each), `OK` (`s + 1`);
- `NXT` (`s + 1`), the copy `ORD` (`NI`), `AS` (`2 nS`), `EXP` (`nS`), `SQ`, `P2` (`L + 2`
  each), the stamps `TS` (`5 (s + 1)`), the queues `D` (`pqSize (J + 5) A2` cells);
- from `RR` on: `RR` (`2`), `CTL` (`4`), `SUM` (`5`), `SL` (`s + 2`), the outputs `PL` (`s`),
  `PO`, `CT`, `CC` (`s + 1` each), `PT` (`s`), and the end `hS`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The procedure indices that the setup calls. -/
structure SuIdx where
  lg : ℕ
  dr : ℕ
  tr : ℕ
  hf : ℕ
  ac : ℕ
  pg : ℕ
  cp : ℕ
  hl : ℕ
  ex : ℕ
  mx : ℕ
  p2 : ℕ
  sq : ℕ
  cl : ℕ

/-- The loads of the setup, into the registers `3` to `22`: from the global block (register `0`)
`n, m, IN, PW, EXP, LAB, LOC, B, J, INF`; from the record block (register `1`) `s, nS, SA, lθ`,
the local index of the center, the target `t`, `nH, HW`; the start `H = h + 51` of the arrays of
`drawP`; and the local index of `t`. -/
def suPro : List (ℕ × Expr) :=
  [(3, ldO 0 0), (4, ldO 0 1), (5, ldO 0 3), (6, ldO 0 4), (7, ldO 0 5), (8, ldO 0 6),
    (9, ldO 0 7), (10, ldO 0 18), (11, ldO 0 19), (12, ldO 0 20), (13, ldO 1 0), (14, ldO 1 1),
    (15, ldO 1 2), (16, ldO 1 3),
    (17, .load (.bin .add (.reg 9) (.load (.bin .add (.reg 8) (ldO 1 5))))),
    (18, ldO 1 6), (19, ldO 1 7), (20, ldO 1 8), (21, .bin .add (.reg 2) (.const 51)),
    (22, locOf' 18)]
where
  /-- `LOC[LAB[v]]` with `LAB`, `LOC` in registers `8`, `9`. -/
  locOf' (v : ℕ) : Expr := .load (.bin .add (.reg 9) (.load (.bin .add (.reg 8) (.reg v))))

/-- `Z + a nS + b s + c L + k`, with `Z`, `nS`, `s`, `L` in registers `24`, `14`, `13`, `28`. -/
def suZ (a b c k : ℕ) : Expr :=
  .bin .add (.bin .add (.bin .add (.bin .add (.reg 24) (mulC a 14)) (mulC b 13)) (mulC c 28))
    (.const k)

/-- `RR + b s + k`, with `RR`, `s` in registers `33`, `13`. -/
def suR (b k : ℕ) : Expr := .bin .add (.bin .add (.reg 33) (mulC b 13)) (.const k)

/-- `H + a nS + b s + k`, with `H`, `nS`, `s` in registers `21`, `14`, `13`. -/
def suH (a b k : ℕ) : Expr :=
  .bin .add (.bin .add (.bin .add (.reg 21) (mulC a 14)) (mulC b 13)) (.const k)

/-- The size `NI = 2 nS + s` of the arrays of `pgP`. -/
def suNI : Expr := .bin .add (mulC 2 14) (.reg 13)

/-- The capacity `A2 = 2 nS + 2 s` of the queues of the petal searches. -/
def suA : Expr := .bin .add (mulC 2 14) (mulC 2 13)

/-- The number `MM = 2 nA + s` of cells of the graph of the petal searches (`nA` in register
`30`). -/
def suMM : Expr := .bin .add (mulC 2 30) (.reg 13)

/-- The tent array `FD = TS + s + 1` of the first run. -/
def suFD : Expr := suH 16 4 5

/-- The queues of the petal searches. -/
def suD : Expr := suZ 23 26 2 16

/-- The end `Z = H + 16 nS + 8 s + 14 + 4 J + 2 J (2 nS + s + 1)` of the cells of `drawP`. -/
def suZE : Expr :=
  .bin .add (.bin .add (suH 16 8 14) (mulC 4 11))
    (.bin .mul (mulC 2 11) (.bin .add (.bin .add (mulC 2 14) (.reg 13)) (.const 1)))

/-- The number `Jq = J + 5` of classes of the queues of the petal searches. -/
def suJq : Expr := .bin .add (.reg 11) (.const 5)

/-- `RR = D + 3 + 4 Jq + 2 Jq A2`. -/
def suRRE : Expr :=
  .bin .add (.bin .add (suD) (.bin .add (.const 3) (.bin .mul (.const 4) suJq)))
    (.bin .mul (.bin .mul (.const 2) suJq) suA)

/-- `(512 B n² Δ) <<< lθ`, the bound `Q · Δ · θ` of the active pairs. -/
def suQD : Expr :=
  .bin .shiftLeft (.bin .mul (.bin .mul (mulC 512 10) (.bin .mul (.reg 3) (.reg 3))) (.reg 23))
    (.reg 16)

/-- The cutoff `32 B n² θ` of the stored pairs of the first run. -/
def suDc : Expr :=
  .bin .shiftLeft (.bin .mul (mulC 32 10) (.bin .mul (.reg 3) (.reg 3))) (.reg 16)

/-- The distance `FD[sv t]` of the target in the first run, `ts` in register `22`. -/
def suDt : Expr := .load (.bin .add suFD (.reg 22))

/-- The words of the block at `h` (register `2`), apart from those that are `0`: offset and
value. The order of the first `43` is that of `PW.LReg`. -/
def suBlk : List (ℕ × Expr) :=
  [(0, suD), (1, suJq), (2, suA), (3, .reg 12), (4, suZ 10 12 0 2), (5, suZ 10 12 0 3),
    (6, suZ 12 15 0 5), (7, suZ 14 16 0 5), (8, suZ 16 17 0 5), (9, suZ 18 18 0 5),
    (11, suZ 23 21 2 11), (12, .bin .add (.reg 13) (.const 1)), (14, .reg 33),
    (15, suZ 18 20 0 7), (16, suZ 20 21 0 7), (17, suZ 22 21 0 7), (18, .reg 31), (19, suR 0 6),
    (20, .bin .shiftLeft (.const 1) (.reg 31)),
    (21, .bin .add (.bin .div (.reg 4) (.bin .mul (.reg 3) (.reg 3))) (.const 1)),
    (22, .reg 30), (24, .reg 32), (25, .reg 28), (26, suZ 23 21 0 7), (27, suZ 23 21 1 9),
    (28, suZ 18 19 0 6), (29, suR 0 11), (30, .reg 13), (31, suR 0 2), (33, suR 1 13),
    (34, suR 2 13), (35, suR 3 14), (36, suR 4 15), (37, suR 5 16), (38, suZ 0 1 0 1),
    (39, suZ 0 3 0 1), (40, suFD), (42, .reg 23),
    (43, .bin .sub (.bin .sub suDt (.bin .div (.bin .add (.reg 23) (.const 1)) (.const 2)))
      (.bin .div (.reg 23) (.const 8))),
    (44, .reg 22), (45, .reg 18),
    (46, .bin .lt (mulC 5 23) (.bin .mul (.const 8) suDt)), (47, suZ 0 2 0 1),
    (48, suZ 0 4 0 1), (49, suZ 0 8 0 2), (50, suR 6 16)]

/-- The stores `mem[h + i] := e` (with `h` in register `2`), then `s`. -/
def suStores : List (ℕ × Expr) → Stmt → Stmt
  | [], s => s
  | (i, e) :: l, s => .seq (.store (.bin .add (.reg 2) (.const i)) e) (suStores l s)

/-- The end of the setup: the header of the queues of the petal searches, `pqClear`, and the
block. -/
def suEnd (I : SuIdx) : Stmt :=
  .seq (.store suD suJq)
  (.seq (.store (.bin .add suD (.const 1)) suA)
  (.seq (.store (.bin .add suD (.const 2)) (.reg 12))
  (.seq (.call 25 I.cl [suD, suJq, .reg 12])
  (suStores suBlk (.ret (.const 0))))))

/-- The tables: `NXT`, the copy of `ORD`, `AS`, `EXP`, then `Es`, `bw`, `P2`, `SQ` and `RR`. -/
def suTab (I : SuIdx) : Stmt :=
  .seq (.call 25 I.cp [.reg 13, suZ 18 19 0 6, suZ 0 0 0 0])
  (.seq (.call 25 I.cp [suMM, suZ 18 20 0 7, suZ 10 14 0 5])
  (.seq (.call 25 I.hl [mulC 2 30, suZ 20 21 0 7])
  (.seq (.call 25 I.ex [.reg 30, suZ 22 21 0 7, .reg 7, suZ 0 8 0 2])
  (.seq (.call 31 I.mx [.reg 30, suZ 22 21 0 7])
  (.seq (.assign 32 (.bin .div (.bin .div (.reg 23) (.const 8)) (.reg 28)))
  (.seq (.call 25 I.p2 [.bin .add (.reg 28) (.const 2), suZ 23 21 1 9, .reg 28, .reg 32])
  (.seq (.call 25 I.sq [.bin .add (.reg 28) (.const 2), suZ 23 21 0 7, .reg 28, .reg 32])
  (.seq (.assign 33 suRRE) (suEnd I)))))))))

/-- The middle of the setup, after `drawP`: the tree, the active entries and the graph. -/
def suMid (I : SuIdx) : Stmt :=
  .seq (.assign 24 suZE)
  (.seq (.call 25 I.tr [.reg 13, .reg 17, suH 16 3 4, .bin .add (.reg 13) (.const 1),
      suH 8 2 3, suH 12 2 3, suH 14 2 3, .reg 15, .reg 5, .reg 8, .reg 9, suZ 0 0 0 0,
      suZ 0 1 0 1, suZ 0 2 0 1, suZ 0 3 0 1, suZ 0 4 0 1, suZ 0 5 0 1, suZ 0 6 0 1,
      suZ 0 7 0 1])
  (.seq (.call 25 I.hf [.reg 19, .reg 20, .reg 8, .reg 9, .reg 6, .reg 7, .reg 16, suZ 0 0 0 0,
      suZ 0 1 0 1, suZ 0 2 0 1, suZ 0 3 0 1, suZ 0 4 0 1, suZ 0 5 0 1, suZ 0 6 0 1, .reg 13])
  (.seq (.assign 29 suQD)
  (.seq (.call 30 I.ac [.reg 14, .reg 15, .reg 6, suZ 0 8 0 2, .reg 29])
  (.seq (.call 25 I.pg [.reg 30, suZ 0 8 0 2, .reg 5, .reg 6, .reg 8, .reg 9, suFD, .reg 16,
      .bin .add (.reg 11) (.const 3), suZ 2 8 0 2, suZ 4 9 0 2, suZ 6 10 0 2, suZ 8 11 0 2,
      suNI, .reg 13, .reg 17,
      suZ 0 7 0 1, suZ 0 5 0 1, suZ 0 6 0 1, suZ 10 12 0 2, suZ 10 13 0 4, suZ 10 14 0 5,
      suZ 12 15 0 5, suZ 14 16 0 5, suZ 16 17 0 5, suZ 18 18 0 5, .const 0])
  (suTab I))))))

/-- The setup after the loads: `L` from two calls of `log2P`
(`L = ⌊log₂ (2 (⌊log₂ (n + 2)⌋ + 1) + 2)⌋ + 1 = pL n`), then `drawP` (which returns `Δ`), then
`suMid`. -/
def suB (I : SuIdx) : Stmt :=
  .seq (.call 26 I.lg [.bin .add (.reg 3) (.const 2)])
  (.seq (.call 27 I.lg [.bin .add (mulC 2 26) (.const 4)])
  (.seq (.assign 28 (.bin .add (.reg 27) (.const 1)))
  (.seq (.call 23 I.dr [.reg 13, .reg 14, .reg 15, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, suDc,
      .reg 16, .reg 17, .reg 11, .reg 12, .reg 21])
  (suMid I))))

/-- **The setup of a cluster**, with `args = [GB, RB, h]`. -/
def setupP (I : SuIdx) : Stmt := assigns suPro (suB I)

theorem suStores_noRand (l : List (ℕ × Expr)) (s : Stmt) (h : s.NoRand) :
    (suStores l s).NoRand := by
  induction l with
  | nil => exact h
  | cons a l ih => obtain ⟨i, e⟩ := a; simp [suStores, Stmt.NoRand, ih]

theorem setupP_noRand (I : SuIdx) : (setupP I).NoRand := by
  refine assigns_noRand _ _ ?_
  simp only [suB, suMid, suTab, suEnd, Stmt.NoRand, true_and, and_true]
  exact suStores_noRand _ _ (by simp [Stmt.NoRand])

end MinCostFlow.LowStretch
