module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitTour
public import MinCostFlow.SparseCore.Program.AssemblyBranchSide

/-!
# The body of the build of a branch at its init (`AssemblyFirstInitBody`)

The build (`AsmFirstInitBuildAt`, `AssemblyFirstInitBuild.lean`) runs its steps one
after the other. Each step is a procedure of its own, proved alone. This file writes the body of
the build: one list of statements that calls the steps in that order, and moves the heap
pointer from each step to the next.

**Arguments.** `[cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]`
in registers `0` to `14`.

**Registers of the body.**
- `15`: the end of the tour, which is also the start `sdH` of the record of the bundle side.
  The bucket table starts at `bktH = sdH + 16`.
- `16`: the end of the bucket table, which is the start `cmpH` of the map to the components.
- `17`: the number of components; `18`: the start `ctH` of the table of the components, after the
  map and its scratch (`5 vCap + 6 eCap + 3` words bound the scratch); `19`: the key base `B`.
- `20`: the end of the slot lists; `21`: their start `sH = ctH + 3 · nComp`; `22`: the number `m`
  of edges of `G` (from the header of `graph`); `23`: the slot list `slotsPtr`; `24`: its length.
- `25`: the end of the sorted roots, which is the start of P5's table.
- `26`: the end of P5's part, which is the start of the spanner table (`eCap` words).
- `27`: `splitB`; `28`: `spV = 2 eCap + splitB + 1`.
- `29`: the end of P6's part, which is the start of the table of roots.
- `30`: the end of the table of roots, which is the heap pointer of `S₀`: its handle is at
  `30 + 5` and its memory form at `30 + 7`.
- `31`: the end of `S₀`, the heap pointer of the marks; `32`: the end of the marks, which is the
  start `embH` of the embedding table; `33`: the end of the embedding table, returned.

**Steps** (the procedures are given by `AsmFirstInitProcs`):
1. the record words and the tour (`asmFirstInitTourStmt`);
2. the bucket table (`bucketTableBody`), the map to the components (`compMapBody`) and the slot
   lists (`slotListBody`);
3. the sorted roots (`rootsListBody`) and P5's table with its slots (`asmFirstInitBunBody`);
4. P6's spanners of the slots (`asmFirstInitSpanBody`);
5. the table of roots (`rootTblBody`), `S₀` (`asmFirstInitS0Body`) and its marks on the tour
   (`asmFirstInitMarkBody`);
6. the embedding table (`asmFirstInitEmbBody`);
7. the words of the record of the branch and of the record of the bundle side.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-- The procedures that the body of the build calls. -/
structure AsmFirstInitProcs where
  /-- P2's init of the tour, `tourBranchInitStmt`. -/
  fTour : ℕ
  /-- The bucket table, `bucketTableBody (fBkt + 1)`. -/
  fBkt : ℕ
  /-- The map to the components, `compMapBody (fComp + 1) (fComp + 2)`. -/
  fComp : ℕ
  /-- The slot lists, `slotListBody (fSlot + 1)`. -/
  fSlot : ℕ
  /-- The sorted roots, `rootsListBody`. -/
  fRoots : ℕ
  /-- P5's table and its slots, `asmFirstInitBunBody`. -/
  fBun : ℕ
  /-- P6's spanners of the slots, `asmFirstInitSpanBody`. -/
  fSpan : ℕ
  /-- The table of roots, `rootTblBody`. -/
  fRootTbl : ℕ
  /-- `S₀`, `asmFirstInitS0Body`. -/
  fS0 : ℕ
  /-- The marks of `S₀` on the tour, `asmFirstInitMarkBody`. -/
  fMark : ℕ
  /-- The embedding table, `asmFirstInitEmbBody`. -/
  fEmb : ℕ

/-- The word `L_w` of P4's export, at `expPtr + 6`. -/
abbrev asmFiLw : Expr := .load (.bin .add (.reg 4) (.const 6))

/-- The handle of the tour, in the record of the branch. -/
abbrev asmFiTourH : Expr := .load (.bin .add (.reg 14) (.const ASM_BR_TOUR))

/-- The key base `B = 2 (P + bucketWordSpace L_w L) + 1`: above the code of every bucket. -/
def asmFirstInitKeyBase (P Lw L : ℕ) : ℕ := 2 * (P + (5 * Lw + 16 * (Lw + L + 1) + 4)) + 1

/-- The key base as an expression. -/
abbrev asmFiKeyBase : Expr :=
  .bin .add (.bin .mul (.const 2) (.bin .add (.reg 9)
    (.bin .add (.bin .add (.bin .mul (.const 5) asmFiLw)
      (.bin .mul (.const 16) (.bin .add (.bin .add asmFiLw (.reg 8)) (.const 1)))) (.const 4))))
    (.const 1)

/-- Steps 1 and 2 of the body: the tour, the bucket table, the map to the components and the
slot lists, with the registers `21` to `24` that the later steps read. -/
def asmFirstInitFrontStmt (F : AsmFirstInitProcs) : Stmt :=
  asmFirstInitTourStmt F.fTour ;;
  .call 16 F.fBkt [.reg 2, .reg 4, .reg 13, .reg 8, .reg 9, .bin .add (.reg 15) (.const 16),
    .bin .add (.bin .add (.reg 15) (.const 16)) (.reg 11)] ;;
  .call 17 F.fComp [.reg 2, .reg 16, .bin .add (.reg 16) (.reg 10)] ;;
  .assign 18 (.bin .add (.bin .add (.reg 16) (.reg 10))
    (.bin .add (.bin .add (.bin .mul (.const 5) (.reg 10)) (.bin .mul (.const 6) (.reg 11)))
      (.const 3))) ;;
  .assign 19 asmFiKeyBase ;;
  .call 20 F.fSlot [.reg 2, .reg 4, .reg 16, .bin .add (.reg 15) (.const 16), .reg 17, .reg 5,
    .reg 19, .reg 18, .bin .add (.reg 18) (.bin .mul (.const 3) (.reg 17))] ;;
  .assign 21 (.bin .add (.reg 18) (.bin .mul (.const 3) (.reg 17))) ;;
  .assign 22 (.load (.bin .add (.reg 2) (.const 3))) ;;
  .assign 23 (.bin .add (.bin .add (.bin .add (.reg 21) (.const 2)) (.reg 11))
    (.bin .mul (.const 5) (.reg 22))) ;;
  .assign 24 (.load (.reg 21))

/-- Steps 3 and 4 of the body: the sorted roots, P5's table with its slots, and P6's spanners. -/
def asmFirstInitMidStmt (F : AsmFirstInitProcs) : Stmt :=
  .call 25 F.fRoots [.load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
    .reg 20] ;;
  .call 26 F.fBun [.reg 11, .reg 10, .reg 11, .reg 5, asmFiTourH, .reg 24,
    .bin .add (.bin .add (.bin .add (.reg 21) (.const 3)) (.reg 11)) (.bin .mul (.const 6) (.reg 22)),
    .load (.bin .add (.reg 21) (.const 1)),
    .bin .add (.bin .add (.bin .add (.reg 21) (.const 3)) (.reg 11)) (.bin .mul (.const 8) (.reg 22)),
    .load (.bin .add (.reg 4) (.const 3)), .reg 20, .reg 25] ;;
  .assign 27 (.bin .mul (.const 2) (.bin .div
    (.bin .sub (.bin .add (.bin .mul (.const 56) (.reg 6)) (.reg 5)) (.const 1)) (.reg 5))) ;;
  .assign 28 (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 11)) (.reg 27)) (.const 1)) ;;
  .call 29 F.fSpan [.reg 25, asmFiTourH, .reg 26, .const 0, .reg 24, .reg 23,
    .bin .add (.reg 26) (.reg 11), .const 0, .const 0, .reg 27, .reg 28, .reg 11, .reg 12]

/-- Steps 5 and 6 of the body: the table of roots, `S₀`, its marks, and the embedding table. -/
def asmFirstInitBackStmt (F : AsmFirstInitProcs) : Stmt :=
  .call 30 F.fRootTbl [.load (.bin .add (.reg 4) (.const 1)), .reg 10, .reg 11,
    .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)), .reg 29] ;;
  .call 31 F.fS0 [.reg 29, .reg 1, .reg 2, .reg 26, .reg 24, .reg 23,
    .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)), .reg 10, .reg 11,
    .reg 30] ;;
  .call 32 F.fMark [asmFiTourH, .bin .add (.reg 30) (.const 7), .reg 31] ;;
  .call 33 F.fEmb [.reg 2, .reg 10, .reg 11, .reg 26, .reg 23, .reg 24, .reg 32]

/-- A store of a register plus a constant offset into the word `r + off`. -/
abbrev asmFiPut (r off : ℕ) (e : Expr) : Stmt := .store (.bin .add (.reg r) (.const off)) e

/-- Step 7 of the body: the three words of the record of the branch, and the record of the bundle
side at `sdH` (register `15`). -/
def asmFirstInitRecStmt : Stmt :=
  asmFiPut 14 ASM_BR_EMB (.reg 32) ;;
  asmFiPut 14 ASM_BR_OUT (.bin .add (.reg 30) (.const 5)) ;;
  asmFiPut 14 ASM_BR_REST (.reg 15) ;;
  asmFiPut 15 ASM_SD_BUN (.reg 25) ;;
  asmFiPut 15 ASM_SD_SPAN (.reg 26) ;;
  asmFiPut 15 ASM_SD_SLOTS (.reg 23) ;;
  asmFiPut 15 ASM_SD_NSLOTS (.reg 24) ;;
  asmFiPut 15 ASM_SD_SLOTCAP (.reg 11) ;;
  asmFiPut 15 ASM_SD_ECAP5 (.reg 11) ;;
  asmFiPut 15 ASM_SD_CAP (.reg 11) ;;
  asmFiPut 15 ASM_SD_SPL (.reg 12) ;;
  asmFiPut 15 ASM_SD_SPLIT (.reg 27) ;;
  asmFiPut 15 ASM_SD_SPV (.reg 28) ;;
  asmFiPut 15 ASM_SD_SPE (.reg 11) ;;
  asmFiPut 15 ASM_SD_MMAX (.reg 6) ;;
  asmFiPut 15 ASM_SD_CMP (.reg 16) ;;
  asmFiPut 15 ASM_SD_BKT (.bin .add (.reg 15) (.const 16)) ;;
  asmFiPut 15 ASM_SD_CT (.reg 18) ;;
  asmFiPut 15 ASM_SD_NCOMP (.reg 17)

/-- **The body of the build.** Steps 1 to 7, then the end of the embedding table is returned. -/
def asmFirstInitBuildBody (F : AsmFirstInitProcs) : Stmt :=
  asmFirstInitFrontStmt F ;; asmFirstInitMidStmt F ;; asmFirstInitBackStmt F ;;
  asmFirstInitRecStmt ;; .ret (.reg 33)

/-- The body never reads random bits. -/
theorem asmFirstInitBuildBody_noRand (F : AsmFirstInitProcs) :
    (asmFirstInitBuildBody F).NoRand := by
  simp [asmFirstInitBuildBody, asmFirstInitFrontStmt, asmFirstInitMidStmt, asmFirstInitBackStmt,
    asmFirstInitRecStmt, asmFiPut, asmFirstInitTourStmt, Stmt.NoRand]

end MinCostFlow.SparseCore.Program
