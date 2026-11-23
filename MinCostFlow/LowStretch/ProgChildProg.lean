module

public import WordRAM.Model

/-!
# The child step: the program text

Three procedures make the child step.
* `oneP`, for one child `k`: it writes the stored highway of the child (`hwWalkP`), its stored
  pairs (`pcP`, from the key group `k` of the active pairs), its nodes with their new local
  indices (`ncP`, from the node group `k`), and its record block. Then it sums the leaf counts
  and takes the largest weight of its nodes (`smP`). A child with at least two vertices gets its
  radius by Dijkstra (`drawP`); when the radius is below `B |X| θ` the child is reset (`rsP`).
  It returns the new heap pointer.
* `rsP`, the reset of a child: the new threshold `x = 2 ^ ⌊log₂ (S / 4B|X|)⌋` (`log2P`), the
  split of the nodes of weight at least `x` (`splitP`), the `x`-nodes with their local indices
  (`iotaP`, `ncP`), the stored pairs with flag `0` (`pcP`) followed by the pairs grouped at the
  split nodes (`grpCopyP`), and the new record block.
* `childP`, the top level: the piece of each node (`chxP`), the nodes grouped by piece (`csrB`),
  the key of each active pair (`keyP`) and the pairs grouped by key (`csrB`), then `oneP` for
  each child.

Every argument of a call is a register, and every register is set by one `assign`, so that the
proofs can follow the values register by register.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The procedure indices used by the child step. -/
structure CIdx where
  hw : ℕ
  pc : ℕ
  nc : ℕ
  sm : ℕ
  dr : ℕ
  rs : ℕ
  lg : ℕ
  sp : ℕ
  io : ℕ
  gc : ℕ
  cx : ℕ
  csr : ℕ
  key : ℕ
  one : ℕ

/-- Arguments given by registers. -/
def rgs (l : List ℕ) : List Expr := l.map Expr.reg

/-- The word at offset `i` of the block whose address is in register `r`. -/
def ldO (r i : ℕ) : Expr := .load (.bin .add (.reg r) (.const i))

/-- `a + b`, `a * b` and `a - b` of registers. -/
def addR (a b : ℕ) : Expr := .bin .add (.reg a) (.reg b)
def mulC (k a : ℕ) : Expr := .bin .mul (.const k) (.reg a)

/-- The local index `LOC[LAB[v]]` of the vertex in register `v`, with `LAB`, `LOC` in registers
`14`, `15`. -/
def locOf (v : ℕ) : Expr := .load (.bin .add (.reg 15) (.load (.bin .add (.reg 14) (.reg v))))

/-- The flag of a regular petal: `k ≠ 0` and not (`sp = 1` and `k = 1`). -/
def rgE : Expr :=
  .bin .mul (.bin .lt (.const 0) (.reg 4))
    (.bin .sub (.const 1) (.bin .mul (.bin .eq (ldO 2 1) (.const 1)) (.bin .eq (.reg 4) (.const 1))))

/-- The loads of `oneP`, into the registers `11` to `38`. -/
def onePro : List (ℕ × Expr) :=
  [(11, ldO 0 3), (12, ldO 0 4), (13, ldO 0 5), (14, ldO 0 6), (15, ldO 0 7), (16, ldO 0 14),
    (17, ldO 0 11), (18, ldO 0 12), (19, ldO 0 19), (20, ldO 0 20), (21, ldO 2 8), (22, ldO 2 9),
    (23, ldO 2 10), (24, ldO 2 11), (25, ldO 2 12), (26, ldO 2 14), (27, ldO 2 15), (28, ldO 1 3),
    (29, ldO 1 4), (30, .load (.bin .add (ldO 2 6) (.reg 4))),
    (31, .load (.bin .add (ldO 2 7) (.reg 4))), (32, locOf 30), (33, locOf 31), (34, rgE),
    (35, .bin .add (.reg 9) (.load (addR 8 4))),
    (36, .bin .sub (.load (.bin .add (addR 8 4) (.const 1))) (.load (addR 8 4))),
    (37, .bin .add (.reg 7) (.load (addR 6 4))),
    (38, .bin .sub (.load (.bin .add (addR 6 4) (.const 1))) (.load (addR 6 4))),
    (42, .const 1), (43, .const 0), (44, ldO 0 18)]

/-- A list of assignments followed by `s`. -/
def assigns : List (ℕ × Expr) → Stmt → Stmt
  | [], s => s
  | (r, e) :: l, s => .seq (.assign r e) (assigns l s)

/-- The tail of `oneP` for a child with at least two vertices: Dijkstra, then the reset test.
The heap end of `drawP` is `H' + 16 nS + 8 s + 14 + 4 J + 2 J (2 nS + s + 1)`. -/
def oneD (I : CIdx) : Stmt :=
  .seq (.assign 50 (locOf 31))
  (.seq (.call 51 I.dr (rgs [38, 36, 40, 11, 12, 13, 14, 15, 27, 28, 50, 19, 20, 49]))
  (.seq (.assign 52 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 49) (mulC 16 36))
      (mulC 8 38)) (.bin .add (.const 14) (mulC 4 19)))
      (.bin .mul (mulC 2 19) (.bin .add (.bin .add (mulC 2 36) (.reg 38)) (.const 1)))))
  (.seq (.assign 53 (.bin .shiftLeft (.bin .mul (.reg 44) (.reg 47)) (.reg 28)))
  (.cond (.bin .lt (.reg 51) (.reg 53))
    (.seq (.call 54 I.rs (rgs [0, 3, 52, 51, 47, 48, 35, 36, 45, 38, 31, 10, 2, 44]))
      (.ret (.reg 54)))
    (.ret (.reg 52))))))

/-- The part of `oneP` after the loads. -/
def oneB (I : CIdx) : Stmt :=
  .seq (.call 39 I.hw (rgs [32, 33, 34, 21, 22, 23, 24, 25, 10, 5]))
  (.seq (.assign 40 (.bin .add (.reg 5) (mulC 4 39)))
  (.seq (.call 41 I.pc (rgs [36, 35, 26, 11, 14, 15, 10, 22, 42, 40]))
  (.seq (.assign 45 (.bin .add (.reg 40) (mulC 2 36)))
  (.seq (.call 41 I.nc (rgs [38, 37, 29, 16, 15, 45]))
  (.seq (.store (.reg 3) (.reg 38))
  (.seq (.store (.bin .add (.reg 3) (.const 1)) (.reg 36))
  (.seq (.store (.bin .add (.reg 3) (.const 2)) (.reg 40))
  (.seq (.store (.bin .add (.reg 3) (.const 3)) (.reg 28))
  (.seq (.store (.bin .add (.reg 3) (.const 4)) (.reg 45))
  (.seq (.store (.bin .add (.reg 3) (.const 5)) (.reg 31))
  (.seq (.store (.bin .add (.reg 3) (.const 6)) (.reg 30))
  (.seq (.store (.bin .add (.reg 3) (.const 7)) (.reg 39))
  (.seq (.store (.bin .add (.reg 3) (.const 8)) (.reg 5))
  (.seq (.assign 46 (addR 45 38))
  (.seq (.call 41 I.sm (rgs [38, 45, 18, 17, 46]))
  (.seq (.assign 47 (.load (.reg 46)))
  (.seq (.assign 48 (.load (.bin .add (.reg 46) (.const 1))))
  (.seq (.assign 49 (.bin .add (.reg 46) (.const 2)))
  (.cond (.bin .lt (.reg 47) (.const 2)) (.ret (.reg 49)) (oneD I))))))))))))))))))))

/-- **One child.** `args = [GB, RB, XB, BK, k, H, OFFN, ORDN, OFFK, ORDK, HM]`: the three blocks,
the address `BK` of the record block of child `k`, the heap pointer `H`, the node groups, the key
groups and the highway marks. -/
def oneP (I : CIdx) : Stmt := assigns onePro (oneB I)

/-- The loads of `rsP`, into the registers `14` to `29`. The arguments are
`[GB, BK, A, Δ, sz, μ, SRCK, cnt, NA, sN, cc, HM, XB, B]`. -/
def rsPro : List (ℕ × Expr) :=
  [(14, ldO 0 9), (15, ldO 0 10), (16, ldO 0 11), (17, ldO 0 12), (18, ldO 0 13), (19, ldO 0 15),
    (20, ldO 0 6), (21, ldO 0 0), (22, ldO 0 14), (23, ldO 0 7), (24, ldO 0 16), (25, ldO 0 17),
    (26, ldO 0 3), (27, ldO 12 14), (28, ldO 12 9), (29, .const 0), (30, .const 3),
    (31, .const 1), (32, .bin .add (.reg 2) (.const 2))]

/-- The part of `rsP` after the loads. -/
def rsB (I : CIdx) : Stmt :=
  .seq (.assign 33 (.bin .mul (mulC 4 13) (.reg 4)))
  (.seq (.assign 34 (.bin .add (.reg 3) (.bin .sub (.reg 5) (.reg 3))))
  (.seq (.assign 34 (.bin .add (.reg 34) (.bin .sub (.reg 33) (.reg 34))))
  (.seq (.assign 35 (.bin .div (.reg 34) (.reg 33)))
  (.seq (.call 36 I.lg (rgs [35]))
  (.seq (.assign 37 (.bin .shiftLeft (.const 1) (.reg 36)))
  (.seq (.call 38 I.sp (rgs [14, 15, 16, 17, 18, 19, 20, 21, 2, 8, 9, 37]))
  (.seq (.assign 39 (addR 9 38))
  (.seq (.assign 40 (.bin .add (.reg 2) (mulC 3 39)))
  (.seq (.call 41 I.io (rgs [39, 40, 30, 31]))
  (.seq (.assign 42 (addR 40 39))
  (.seq (.call 41 I.nc (rgs [39, 40, 2, 22, 23, 42]))
  (.seq (.assign 43 (addR 42 39))
  (.seq (.call 41 I.pc (rgs [7, 6, 27, 26, 20, 23, 11, 28, 29, 43]))
  (.seq (.call 44 I.gc (rgs [32, 38, 24, 25, 43, 7]))
  (.seq (.store (.reg 1) (.reg 39))
  (.seq (.store (.bin .add (.reg 1) (.const 1)) (.reg 44))
  (.seq (.store (.bin .add (.reg 1) (.const 2)) (.reg 43))
  (.seq (.store (.bin .add (.reg 1) (.const 3)) (.reg 36))
  (.seq (.store (.bin .add (.reg 1) (.const 4)) (.reg 42))
  (.seq (.store (.bin .add (.reg 1) (.const 6)) (.reg 10))
  (.seq (.store (.bin .add (.reg 1) (.const 7)) (.reg 29))
    (.ret (.bin .add (.reg 43) (mulC 2 44))))))))))))))))))))))))

/-- **The reset of a child.** -/
def rsP (I : CIdx) : Stmt := assigns rsPro (rsB I)

/-- The loads and addresses of `childP`, into the registers `4` to `27`. The arguments are
`[GB, RB, XB, h]`. -/
def topPro : List (ℕ × Expr) :=
  [(4, .bin .add (ldO 2 0) (.const 1)), (5, ldO 1 0), (6, ldO 2 13),
    (7, .bin .add (.reg 3) (mulC 9 4)), (8, addR 7 5),
    (9, .bin .add (.bin .add (.reg 8) (.reg 4)) (.const 1)), (10, addR 9 4), (11, addR 10 5),
    (12, addR 11 6), (13, .bin .add (.bin .add (.reg 12) (.reg 4)) (.const 2)),
    (14, .bin .add (.bin .add (.reg 13) (.reg 4)) (.const 1)), (15, addR 14 6), (16, addR 15 5),
    (17, ldO 2 0), (18, ldO 2 2), (19, ldO 2 3), (20, ldO 2 14), (21, ldO 0 3), (22, ldO 0 6),
    (23, ldO 0 7), (24, .bin .add (.reg 4) (.const 1)), (25, .const 0), (26, .reg 16)]

/-- The loop over the children. -/
def topLoop (I : CIdx) : Stmt :=
  .loop (.bin .lt (.reg 25) (.reg 4))
    (.seq (.assign 27 (.bin .add (.reg 3) (mulC 9 25)))
    (.seq (.call 26 I.one (rgs [0, 1, 2, 27, 25, 26, 8, 10, 12, 14, 15]))
      (.assign 25 (.bin .add (.reg 25) (.const 1)))))

/-- The part of `childP` after the loads. -/
def topB (I : CIdx) : Stmt :=
  .seq (.call 28 I.cx (rgs [17, 18, 19, 7]))
  (.seq (.call 28 I.csr (rgs [7, 5, 4, 8, 9, 10]))
  (.seq (.call 28 I.key (rgs [6, 20, 21, 22, 23, 7, 4, 11]))
  (.seq (.call 28 I.csr (rgs [11, 6, 24, 12, 13, 14]))
  (.seq (topLoop I) (.ret (.reg 26))))))

/-- **The child step**, with `args = [GB, RB, XB, h]`. -/
def childP (I : CIdx) : Stmt := assigns topPro (topB I)

theorem assigns_noRand (l : List (ℕ × Expr)) (s : Stmt) (h : s.NoRand) : (assigns l s).NoRand := by
  induction l with
  | nil => exact h
  | cons e l ih => obtain ⟨r, x⟩ := e; simp [assigns, Stmt.NoRand, ih]

theorem oneP_noRand (I : CIdx) : (oneP I).NoRand :=
  assigns_noRand _ _ (by simp [oneB, oneD, Stmt.NoRand])

theorem rsP_noRand (I : CIdx) : (rsP I).NoRand :=
  assigns_noRand _ _ (by simp [rsB, Stmt.NoRand])

theorem childP_noRand (I : CIdx) : (childP I).NoRand :=
  assigns_noRand _ _ (by simp [topB, topLoop, Stmt.NoRand])

end MinCostFlow.LowStretch
