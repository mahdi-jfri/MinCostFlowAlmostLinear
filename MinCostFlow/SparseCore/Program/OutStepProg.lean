module

public import MinCostFlow.SparseCore.Program.OutStepProcs
public import MinCostFlow.SparseCore.Program.OutResetProg

/-!
# The program of the output step

The output step of a branch (`sig_outStepSmall_runs`) changes the stored output graph by the
output batch `U_S`, and writes `U_S` and the edits of the output order. This file gives the
program (`outStepBody`). It runs in six phases.

1. **Setup** (`osSetup`). It reads the graph address and the caps, and reserves two regions
   after the four words at `h`: the batch from `h + 4` and the edits from `e0 = h + 4 + R`, each
   of `R = 16 (vCap + 1) (eCap + 1)` words. The tour may grow from `e0 + R` on. The batch and
   the edits are written record by record, between tour calls, so they must lie before the cells
   that the tour takes.
2. **Deletions** (`osDelIter`). For each leaving edge `e` with its flag: the batch record
   `[1, e]`, applied to the stored graph, the edit `[0, e]`, and, when the flag is `1`, the two
   ends unmarked.
3. **Splits** (`osSplitIter`), one per split record of the helper. The edges of the ends of its
   list that are still in the graph give a first record of the split (two calls of the filter),
   which is applied to the graph. Then the degrees of the two vertices give the smaller side;
   the walk copies the incidence list of its vertex as the key list of the edit, and the filter
   rewrites the batch record from these keys. So both records list the smaller side.
4. **Insertions** (`osInsIter`). For each entering edge: the batch record `[0, e, a, b]`,
   applied to the graph, and for each end in turn the place from `nextMarked`, the edit
   `[3, v, key, place]`, and the mark.
5. **Rotations** (`osRotIter`). For each vertex `v` of `T₀`: the first marked end from
   `firstMarked`, and the edit `[4, v, key]` when there is one.
6. **The four words** (`osFinal`): the counts of the two regions and the words at `h`.

Registers: `0`–`6` the arguments `[outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h]`, `7` the
heap pointer of the tour, `8` and `9` the results of calls, `10` the graph address, `11` and `12`
the caps, `13` the region size `R`, `14` the next batch cell, `15` the edit region `e0`, `16` the
next edit cell, `17` and `18` the numbers of batch records and of edits, `19`, `23`, `24` and `25`
the bases of the edge presence array, the table of internal names, the incidence heads and the
next words of the graph, `20` the place in the input, `26` its length, and `21`, `22`, `27`–`36`
values of one round.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-! ## Small pieces -/

/-- A tour query `[tourH, arg, heap]` at procedure `f`: its answer goes to register `dst`, and
the heap pointer moves past the cells of the call. -/
def osQuery (f : ℕ) (argE : Expr) (dst : ℕ) : Stmt :=
  .seq (.call 8 f [.reg 1, argE, .reg 7])
    (.seq (.assign dst (.load (.reg 7))) (.assign 7 (.reg 8)))

/-- One more batch record of `lenE` words. -/
def osBumpB (lenE : Expr) : Stmt :=
  .seq (.assign 14 (.bin .add (.reg 14) lenE)) (.assign 17 (.bin .add (.reg 17) (.const 1)))

/-- One more edit record of `lenE` words. -/
def osBumpE (lenE : Expr) : Stmt :=
  .seq (.assign 16 (.bin .add (.reg 16) lenE)) (.assign 18 (.bin .add (.reg 18) (.const 1)))

/-- The key `2 e` of the tail end of the edge in register `21`. -/
def osKey0 : Expr := .bin .add (.reg 21) (.reg 21)

/-- The key `2 e + 1` of the head end of the edge in register `21`. -/
def osKey1 : Expr := .bin .add (.bin .add (.reg 21) (.reg 21)) (.const 1)

/-! ## The phases -/

/-- The setup. -/
def osSetup : Stmt :=
  .seq (.assign 10 (.load (.reg 0)))
  (.seq (.assign 11 (.load (.reg 10)))
  (.seq (.assign 12 (.load (.bin .add (.reg 10) (.const 1))))
  (.seq (.assign 13 (.bin .mul (.bin .mul (.bin .add (.reg 11) (.const 1))
      (.bin .add (.reg 12) (.const 1))) (.const 16)))
  (.seq (.assign 14 (.bin .add (.reg 6) (.const 5)))
  (.seq (.assign 15 (.bin .add (.bin .add (.reg 6) (.const 4)) (.reg 13)))
  (.seq (.assign 16 (.bin .add (.reg 15) (.const 1)))
  (.seq (.assign 7 (.bin .add (.reg 15) (.reg 13)))
  (.seq (.assign 17 (.const 0))
  (.seq (.assign 18 (.const 0))
  (.seq (.assign 19 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 11))))
  (.seq (.assign 23 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 3) (.reg 11))))
  (.seq (.assign 24 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 6) (.reg 11))))
    (.assign 25 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4))
      (.bin .mul (.const 7) (.reg 11))) (.bin .mul (.const 7) (.reg 12))))))))))))))))

/-- One deletion: the edge in register `21`, its flag in register `22`. -/
def osDelIter (sm au : ℕ) : Stmt :=
  .seq (.assign 21 (.load (.bin .add (.bin .add (.reg 2) (.const 1))
      (.bin .add (.reg 20) (.reg 20)))))
  (.seq (.assign 22 (.load (.bin .add (.bin .add (.reg 2) (.const 2))
      (.bin .add (.reg 20) (.reg 20)))))
  (.seq (.store (.reg 14) (.const 1))
  (.seq (.store (.bin .add (.reg 14) (.const 1)) (.reg 21))
  (.seq (.call 9 au [.reg 10, .reg 14, .const 1])
  (.seq (osBumpB (.const 2))
  (.seq (.store (.reg 16) (.const 0))
  (.seq (.store (.bin .add (.reg 16) (.const 1)) (.reg 21))
  (.seq (osBumpE (.const 2))
  (.seq (.cond (.reg 22) (.seq (rsMark sm 0 osKey0) (rsMark sm 0 osKey1)) .nop)
    (.assign 20 (.bin .add (.reg 20) (.const 1))))))))))))

/-- The deletions. -/
def osDelPhase (sm au : ℕ) : Stmt :=
  .seq (.assign 20 (.const 0))
    (.seq (.assign 26 (.load (.reg 2))) (.loop (.bin .lt (.reg 20) (.reg 26)) (osDelIter sm au)))

/-- The two edge lists of a split record of the batch at register `14`, from `nE` keys at
`srcE`: the tails (count in register `29`) and then the heads (count in register `30`). -/
def osFilters (flt : ℕ) (srcE nE : Expr) : Stmt :=
  .seq (.call 29 flt [srcE, nE, .const 0, .bin .add (.reg 14) (.const 5), .reg 19])
    (.call 30 flt [srcE, nE, .const 1, .bin .add (.bin .add (.reg 14) (.const 5)) (.reg 29),
      .reg 19])

/-- The five head words `[tag, v, v', kt, kh]` of a split record of the batch. -/
def osBHdr (tagE : Expr) : Stmt :=
  .seq (.store (.reg 14) tagE)
  (.seq (.store (.bin .add (.reg 14) (.const 1)) (.reg 21))
  (.seq (.store (.bin .add (.reg 14) (.const 2)) (.reg 22))
  (.seq (.store (.bin .add (.reg 14) (.const 3)) (.reg 29))
    (.store (.bin .add (.reg 14) (.const 4)) (.reg 30)))))

/-- The smaller side after the split, from the degrees of `v'` (register `31`) and `v`
(register `32`): its vertex in register `33`, the tag of the batch record in `34` and the tag of
the edit in `35`. The new vertex `v'` is chosen when its degree is at most that of `v`. -/
def osChoose : Stmt :=
  .seq (.assign 33 (.reg 22))
  (.seq (.assign 34 (.const 2))
  (.seq (.assign 35 (.const 1))
    (.cond (.bin .lt (.reg 32) (.reg 31))
      (.seq (.assign 33 (.reg 21)) (.seq (.assign 34 (.const 3)) (.assign 35 (.const 2))))
      .nop)))

/-- The four head words `[tag, v, v', len]` of the edit of a split. -/
def osEHdr : Stmt :=
  .seq (.store (.reg 16) (.reg 35))
  (.seq (.store (.bin .add (.reg 16) (.const 1)) (.reg 21))
  (.seq (.store (.bin .add (.reg 16) (.const 2)) (.reg 22))
    (.store (.bin .add (.reg 16) (.const 3)) (.reg 36))))

/-- One split, from the record at register `20`. -/
def osSplitIter (au gd flt wk : ℕ) : Stmt :=
  .seq (.assign 21 (.load (.reg 20)))
  (.seq (.assign 22 (.load (.bin .add (.reg 20) (.const 1))))
  (.seq (.assign 27 (.load (.bin .add (.reg 20) (.const 2))))
  (.seq (.assign 28 (.load (.bin .add (.reg 20) (.const 3))))
  (.seq (osFilters flt (.bin .add (.reg 28) (.const 1)) (.load (.reg 28)))
  (.seq (osBHdr (.bin .sub (.const 3) (.reg 27)))
  (.seq (.call 9 au [.reg 10, .reg 14, .const 1])
  (.seq (.call 31 gd [.reg 10, .reg 22])
  (.seq (.call 32 gd [.reg 10, .reg 21])
  (.seq osChoose
  (.seq (.call 36 wk [.reg 25, .bin .add (.reg 24) (.load (.bin .add (.reg 23) (.reg 33))),
      .bin .add (.reg 16) (.const 4)])
  (.seq osEHdr
  (.seq (osFilters flt (.bin .add (.reg 16) (.const 4)) (.reg 36))
  (.seq (osBHdr (.reg 34))
  (.seq (osBumpB (.bin .add (.const 5) (.reg 36)))
  (.seq (osBumpE (.bin .add (.const 4) (.reg 36)))
    (.assign 20 (.load (.bin .add (.reg 20) (.const 4)))))))))))))))))))

/-- The splits. -/
def osSplitPhase (au gd flt wk : ℕ) : Stmt :=
  .seq (.assign 20 (.reg 3)) (.loop (.reg 20) (osSplitIter au gd flt wk))

/-- One end of an inserted edge: its key `keyE`, the vertex `vE` of its list. -/
def osInsEnd (nm sm : ℕ) (vE keyE : Expr) : Stmt :=
  .seq (osQuery nm keyE 29)
  (.seq (.store (.reg 16) (.const 3))
  (.seq (.store (.bin .add (.reg 16) (.const 1)) vE)
  (.seq (.store (.bin .add (.reg 16) (.const 2)) keyE)
  (.seq (.store (.bin .add (.reg 16) (.const 3)) (.reg 29))
  (.seq (osBumpE (.const 4))
    (rsMark sm 1 keyE))))))

/-- One insertion: the edge in register `21`, its new tail and head in registers `22` and `27`. -/
def osInsIter (nm sm au : ℕ) : Stmt :=
  .seq (.assign 21 (.load (.bin .add (.bin .add (.reg 4) (.const 1))
      (.bin .mul (.const 3) (.reg 20)))))
  (.seq (.assign 22 (.load (.bin .add (.bin .add (.reg 4) (.const 2))
      (.bin .mul (.const 3) (.reg 20)))))
  (.seq (.assign 27 (.load (.bin .add (.bin .add (.reg 4) (.const 3))
      (.bin .mul (.const 3) (.reg 20)))))
  (.seq (.store (.reg 14) (.const 0))
  (.seq (.store (.bin .add (.reg 14) (.const 1)) (.reg 21))
  (.seq (.store (.bin .add (.reg 14) (.const 2)) (.reg 22))
  (.seq (.store (.bin .add (.reg 14) (.const 3)) (.reg 27))
  (.seq (.call 9 au [.reg 10, .reg 14, .const 1])
  (.seq (osBumpB (.const 4))
  (.seq (osInsEnd nm sm (.reg 22) osKey0)
  (.seq (osInsEnd nm sm (.reg 27) osKey1)
    (.assign 20 (.bin .add (.reg 20) (.const 1)))))))))))))

/-- The insertions. -/
def osInsPhase (nm sm au : ℕ) : Stmt :=
  .seq (.assign 20 (.const 0))
    (.seq (.assign 26 (.load (.reg 4))) (.loop (.bin .lt (.reg 20) (.reg 26)) (osInsIter nm sm au)))

/-- One rotation, of the vertex in register `21`. -/
def osRotIter (fm : ℕ) : Stmt :=
  .seq (.assign 21 (.load (.bin .add (.bin .add (.reg 5) (.const 1)) (.reg 20))))
  (.seq (osQuery fm (.reg 21) 29)
  (.seq (.cond (.reg 29)
      (.seq (.store (.reg 16) (.const 4))
      (.seq (.store (.bin .add (.reg 16) (.const 1)) (.reg 21))
      (.seq (.store (.bin .add (.reg 16) (.const 2)) (.bin .sub (.reg 29) (.const 1)))
        (osBumpE (.const 3)))))
      .nop)
    (.assign 20 (.bin .add (.reg 20) (.const 1)))))

/-- The rotations. -/
def osRotPhase (fm : ℕ) : Stmt :=
  .seq (.assign 20 (.const 0))
    (.seq (.assign 26 (.load (.reg 5))) (.loop (.bin .lt (.reg 20) (.reg 26)) (osRotIter fm)))

/-- The count words of both regions and the four words at `h`; return the heap pointer. -/
def osFinal : Stmt :=
  .seq (.store (.bin .add (.reg 6) (.const 4)) (.reg 17))
  (.seq (.store (.reg 15) (.reg 18))
  (.seq (.store (.reg 6) (.bin .add (.reg 6) (.const 4)))
  (.seq (.store (.bin .add (.reg 6) (.const 1)) (.bin .sub (.reg 14) (.bin .add (.reg 6) (.const 4))))
  (.seq (.store (.bin .add (.reg 6) (.const 2)) (.reg 15))
  (.seq (.store (.bin .add (.reg 6) (.const 3)) (.bin .sub (.reg 16) (.reg 15)))
    (.ret (.reg 7)))))))

/-- **The output step** `[outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h]`, for the tour
procedures `nm` (`nextMarked`), `sm` (`setMark`) and `fm` (`firstMarked`), the graph procedures
`au` (`dgApplyUpdate`) and `gd` (`dgGetDeg`), the filter `flt` and the walk `wk`. -/
def outStepBody (nm sm fm au gd flt wk : ℕ) : Stmt :=
  .seq osSetup
    (.seq (osDelPhase sm au)
      (.seq (osSplitPhase au gd flt wk)
        (.seq (osInsPhase nm sm au)
          (.seq (osRotPhase fm) osFinal))))

end MinCostFlow.SparseCore.Program
